module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalDefs
import CFSG.Quasithin.Recognition.St84.Gen.ModTwoNatL2Sum
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionBorel
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InExclusive

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

section SecMod

variable {G : Type} [Group G] {F : Type} [Field F] {L : Subgroup G} {α : ↥L →* SL(2, F)}

private structure SecData (L : Subgroup G) (α : ↥L →* SL(2, F)) : Prop where
  surj : Function.Surjective α
  normU : ∀ l ∈ L, ∀ u ∈ blockU L, l * u * l⁻¹ ∈ blockU L
  normZ : ∀ l ∈ L, ∀ z ∈ blockZ L, l * z * l⁻¹ ∈ blockZ L
  le : blockU L ≤ L
  comm : ∀ a ∈ blockU L, ∀ b ∈ blockU L, ⁅a, b⁆ ∈ blockZ L
  sq : ∀ a ∈ blockU L, a ^ 2 ∈ blockZ L
  ker : ∀ l : ↥L, α l = 1 → ∀ u ∈ blockU L, ⁅(l : G), u⁆ ∈ blockZ L

private abbrev zSub (L : Subgroup G) : Subgroup ↥(blockU L) := (blockZ L).subgroupOf (blockU L)

private theorem SecData.normal (h : SecData L α) : (zSub L).Normal where
  conj_mem n hn g := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.normZ g (h.le g.2) n hn

private def SecMod (_h : SecData L α) : Type := Additive (↥(blockU L) ⧸ zSub L)

private noncomputable instance (h : SecData L α) : AddCommGroup (SecMod h) :=
  letI : (zSub L).Normal := h.normal
  letI : CommGroup (↥(blockU L) ⧸ zSub L) :=
    { (inferInstance : Group (↥(blockU L) ⧸ zSub L)) with
      mul_comm := fun a b => by
        induction a using QuotientGroup.induction_on with | H a => ?_
        induction b using QuotientGroup.induction_on with | H b => ?_
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have := h.comm (b⁻¹ : ↥(blockU L)) (b⁻¹).2 (a⁻¹ : ↥(blockU L)) (a⁻¹).2
        convert this using 1
        simp [commutatorElement_def, mul_assoc] }
  inferInstanceAs (AddCommGroup (Additive (↥(blockU L) ⧸ zSub L)))

private instance [Finite ↥L] (h : SecData L α) : Finite (SecMod h) :=
  haveI : Finite ↥(blockU L) := Finite.of_injective _ (Subgroup.inclusion_injective h.le)
  inferInstanceAs (Finite (Additive (↥(blockU L) ⧸ zSub L)))

private def SecMod.mk (h : SecData L α) (u : ↥(blockU L)) : SecMod h :=
  Additive.ofMul (QuotientGroup.mk u : ↥(blockU L) ⧸ zSub L)

private theorem SecMod.mk_mul (h : SecData L α) (a b : ↥(blockU L)) :
    SecMod.mk h (a * b) = SecMod.mk h a + SecMod.mk h b := rfl

private theorem SecMod.mk_one (h : SecData L α) : SecMod.mk h 1 = 0 := rfl

private theorem SecMod.mk_surjective (h : SecData L α) : Function.Surjective (SecMod.mk h) :=
  fun v =>
    let ⟨c, hc⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    ⟨c, by simp only [SecMod.mk, hc]; rfl⟩

private theorem SecMod.mk_eq_mk_iff (h : SecData L α) (a b : ↥(blockU L)) :
    SecMod.mk h a = SecMod.mk h b ↔ (a : G)⁻¹ * b ∈ blockZ L := by
  letI : (zSub L).Normal := h.normal
  have e : SecMod.mk h a = SecMod.mk h b ↔
      (QuotientGroup.mk a : ↥(blockU L) ⧸ zSub L) = QuotientGroup.mk b :=
    ⟨fun hab => Additive.ofMul.injective hab, fun hab => congrArg Additive.ofMul hab⟩
  rw [e, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

private theorem SecMod.mk_eq_zero_iff (h : SecData L α) (u : ↥(blockU L)) :
    SecMod.mk h u = 0 ↔ (u : G) ∈ blockZ L := by
  rw [← SecMod.mk_one h, SecMod.mk_eq_mk_iff]
  simp

private theorem SecMod.mk_inv (h : SecData L α) (u : ↥(blockU L)) :
    SecMod.mk h u⁻¹ = -SecMod.mk h u := by
  have := SecMod.mk_mul h u u⁻¹
  rw [mul_inv_cancel, SecMod.mk_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

private noncomputable instance (h : SecData L α) : Module (ZMod 2) (SecMod h) :=
  AddCommGroup.zmodModule fun v => by
    obtain ⟨u, rfl⟩ := SecMod.mk_surjective h v
    rw [two_nsmul, ← SecMod.mk_mul, SecMod.mk_eq_zero_iff, Subgroup.coe_mul, ← pow_two]
    exact h.sq _ u.2

private def conjU (h : SecData L α) (l : ↥L) : ↥(blockU L) →* ↥(blockU L) where
  toFun u := ⟨(l : G) * u * (l : G)⁻¹, h.normU l l.2 u u.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

private noncomputable def actQ [(zSub L).Normal] (h : SecData L α) (l : ↥L) :
    (↥(blockU L) ⧸ zSub L) →* (↥(blockU L) ⧸ zSub L) :=
  QuotientGroup.map _ _ (conjU h l) (fun n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    simpa [conjU] using h.normZ l l.2 n hn)

private theorem actQ_mk [(zSub L).Normal] (h : SecData L α) (l : ↥L) (u : ↥(blockU L)) :
    actQ h l (QuotientGroup.mk u) = QuotientGroup.mk (conjU h l u) := rfl

private theorem actQ_mul [(zSub L).Normal] (h : SecData L α) (l l' : ↥L)
    (x : ↥(blockU L) ⧸ zSub L) : actQ h (l * l') x = actQ h l (actQ h l' x) := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actQ_mk, actQ_mk, actQ_mk]
  congr 1
  ext
  simp [conjU, mul_assoc]

private theorem actQ_one [(zSub L).Normal] (h : SecData L α) (x : ↥(blockU L) ⧸ zSub L) :
    actQ h 1 x = x := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actQ_mk]
  congr 1
  ext
  simp [conjU]

private theorem actQ_eq [(zSub L).Normal] (h : SecData L α) {l l' : ↥L} (hl : α l = α l')
    (x : ↥(blockU L) ⧸ zSub L) : actQ h l x = actQ h l' x := by
  induction x using QuotientGroup.induction_on with | H c => ?_
  rw [actQ_mk, actQ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hw : α (l⁻¹ * l') = 1 := by rw [map_mul, map_inv, hl, inv_mul_cancel]
  have h1 := h.ker (l⁻¹ * l') hw ((c : G)⁻¹) (inv_mem c.2)
  have h2 := h.normZ l l.2 _ (inv_mem h1)
  convert h2 using 1
  simp only [conjU, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
    commutatorElement_def]
  group

private noncomputable def SecMod.smul' (h : SecData L α) (g : SL(2, F)) (v : SecMod h) :
    SecMod h :=
  letI : (zSub L).Normal := h.normal
  Additive.ofMul (actQ h (Classical.choose (h.surj g)) (Additive.toMul v))

private noncomputable instance (h : SecData L α) : DistribMulAction SL(2, F) (SecMod h) where
  smul := SecMod.smul' h
  one_smul v := by
    letI : (zSub L).Normal := h.normal
    show Additive.ofMul (actQ h (Classical.choose (h.surj 1)) (Additive.toMul v)) = v
    rw [actQ_eq h (l' := 1) (by rw [Classical.choose_spec (h.surj 1), map_one]), actQ_one]
    rfl
  mul_smul g₁ g₂ v := by
    letI : (zSub L).Normal := h.normal
    show Additive.ofMul (actQ h (Classical.choose (h.surj (g₁ * g₂))) (Additive.toMul v)) =
      Additive.ofMul (actQ h (Classical.choose (h.surj g₁))
        (actQ h (Classical.choose (h.surj g₂)) (Additive.toMul v)))
    rw [actQ_eq h (l' := Classical.choose (h.surj g₁) * Classical.choose (h.surj g₂)) (by
      rw [map_mul, Classical.choose_spec (h.surj g₁), Classical.choose_spec (h.surj g₂),
        Classical.choose_spec (h.surj (g₁ * g₂))]), actQ_mul]
  smul_zero g := by
    letI : (zSub L).Normal := h.normal
    show Additive.ofMul (actQ h _ (Additive.toMul (0 : SecMod h))) = 0
    rw [show Additive.toMul (0 : SecMod h) = 1 from rfl, map_one]
    rfl
  smul_add g v w := by
    letI : (zSub L).Normal := h.normal
    show Additive.ofMul (actQ h _ (Additive.toMul (v + w))) = _
    rw [show Additive.toMul (v + w) = Additive.toMul v * Additive.toMul w from rfl, map_mul]
    rfl

private theorem SecMod.smul_mk (h : SecData L α) (l : ↥L) (u : ↥(blockU L)) :
    α l • SecMod.mk h u = SecMod.mk h (conjU h l u) := by
  letI : (zSub L).Normal := h.normal
  show Additive.ofMul (actQ h (Classical.choose (h.surj (α l))) (QuotientGroup.mk u)) = _
  rw [actQ_eq h (Classical.choose_spec (h.surj (α l))), actQ_mk]
  rfl

private theorem SecMod.mk_conjU_eq_iff (h : SecData L α) (l : ↥L) (u : ↥(blockU L)) :
    SecMod.mk h (conjU h l u) = SecMod.mk h u ↔ ⁅(l : G), (u : G)⁆ ∈ blockZ L := by
  have e : ((conjU h l u * u⁻¹ : ↥(blockU L)) : G) = ⁅(l : G), (u : G)⁆ := by
    simp [conjU, commutatorElement_def]
  rw [← e, ← SecMod.mk_eq_zero_iff h, SecMod.mk_mul, SecMod.mk_inv, add_neg_eq_zero]

end SecMod

theorem isTwoNatType_of_quadratic {G : Type} [Group G] {L : Subgroup G} [Finite ↥L] {f : ℕ}
    (hf : 1 ≤ f) (hq : IsL2Quot f (oTwoQuot ↥L))
    (hQU : ∀ x ∈ pCoreOf 2 L, ∀ u ∈ blockU L, ⁅x, u⁆ ∈ blockZ L)
    (hsq : ∀ u ∈ blockU L, u ^ 2 ∈ blockZ L)
    (hcard : Nat.card (blockU L) = 2 ^ (4 * f) * Nat.card (blockZ L))
    (hfree : ∀ u ∈ blockU L, (∀ l ∈ L, ⁅l, u⁆ ∈ blockZ L) → u ∈ blockZ L)
    {T : Subgroup G} (hT : IsSylowTwoOf T L)
    (hquad : ∀ t ∈ T, ∀ t' ∈ T, ∀ u ∈ blockU L, ⁅t, ⁅t', u⁆⁆ ∈ blockZ L) :
    IsTwoNatType L f := by
  classical
  obtain ⟨e0⟩ := hq
  let e : oTwoQuot ↥L ≃* SL(2, GaloisField 2 f) := e0.trans (CFSG.Quasithin.pslTwoGf2EquivSl f)
  let α₀ : ↥L →* SL(2, GaloisField 2 f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hα₀ : Function.Surjective α₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker₀ : α₀.ker = CFSG.pCore 2 ↥L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  obtain ⟨X, hX⟩ := exists_conj_mem_iff hT α₀ hα₀ hker₀
  let α : ↥L →* SL(2, GaloisField 2 f) := (MulAut.conj X).toMonoidHom.comp α₀
  have hαs : Function.Surjective α := (MulAut.conj X).surjective.comp hα₀
  have hαker : α.ker = CFSG.pCore 2 ↥L := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj X).injective, hker₀]
  have hUU : upperUnipotent (GaloisField 2 f) = CFSG.CGT.Timmesfeld75.utri (GaloisField 2 f) :=
    le_antisymm ((Subgroup.closure_le _).2 fun g hg => mem_utri_iff_eq_unitri.2 hg)
      fun g hg => Subgroup.subset_closure (mem_utri_iff_eq_unitri.1 hg)
  have hT' : ∀ l : ↥L, α l ∈ upperUnipotent (GaloisField 2 f) → (l : G) ∈ T := fun l hl =>
    (hX l).2 (by rw [← hUU]; exact hl)
  have hZ : ∀ z, z ∈ blockZ L ↔ z ∈ blockU L ∧ ∀ l ∈ L, l * z = z * l := fun z => by
    rw [blockZ, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    rfl
  have hUQ : blockU L ≤ pCoreOf 2 L := Subgroup.commutator_le.2 fun q hq l hl => by
    have h1 : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L hl) q⁻¹).mp
        (inv_mem hq)
    rw [commutatorElement_def, mul_assoc, mul_assoc]
    exact mul_mem hq (by rw [← mul_assoc]; exact h1)
  haveI : Finite ↥(blockU L) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (hUQ.trans (C1.blockQ_le L)))
  haveI : Finite ↥(blockZ L) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((inf_le_left : blockZ L ≤ blockU L).trans (hUQ.trans (C1.blockQ_le L))))
  have hd : SecData L α :=
    { surj := hαs
      normU := fun l hl u hu =>
        (Subgroup.mem_normalizer_iff.mp (Lin2.le_normalizer_blockU L hl) u).mp hu
      normZ := fun l hl z hz => by
        rwa [((hZ z).1 hz).2 l hl, mul_inv_cancel_right]
      le := hUQ.trans (C1.blockQ_le L)
      comm := fun a ha b hb => hQU a (hUQ ha) b hb
      sq := hsq
      ker := fun l hl u hu => hQU l
        ((CFSG.mem_openPCoreOf_iff l).2 (hαker ▸ MonoidHom.mem_ker.2 hl)) u hu }
  have hfix' : ∀ v : SecMod hd, (∀ x : SL(2, GaloisField 2 f), x • v = v) → v = 0 := by
    intro v hv
    obtain ⟨u, rfl⟩ := SecMod.mk_surjective hd v
    rw [SecMod.mk_eq_zero_iff]
    refine hfree u u.2 fun l hl => ?_
    have h := hv (α ⟨l, hl⟩)
    rwa [SecMod.smul_mk, SecMod.mk_conjU_eq_iff] at h
  have hquad' : ∀ a ∈ upperUnipotent (GaloisField 2 f), ∀ a' ∈ upperUnipotent (GaloisField 2 f),
      ∀ v : SecMod hd, a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    obtain ⟨t, rfl⟩ := hαs a
    obtain ⟨t', rfl⟩ := hαs a'
    obtain ⟨u, rfl⟩ := SecMod.mk_surjective hd v
    have hc : ((conjU hd t u * u⁻¹ : ↥(blockU L)) : G) = ⁅(t : G), (u : G)⁆ := by
      simp [conjU, commutatorElement_def]
    have e : α t • SecMod.mk hd u - SecMod.mk hd u = SecMod.mk hd (conjU hd t u * u⁻¹) := by
      rw [SecMod.smul_mk, SecMod.mk_mul, SecMod.mk_inv, sub_eq_add_neg]
    rw [e, SecMod.smul_mk, SecMod.mk_conjU_eq_iff, hc]
    exact hquad t' (hT' t' ha') t (hT' t ha) u u.2
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcard' : Nat.card (SecMod hd) = Nat.card (GaloisField 2 f) ^ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (zSub L)
    have h2 : Nat.card ↥(zSub L) = Nat.card ↥(blockZ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : blockZ L ≤ blockU L)).toEquiv
    rw [h2, hcard] at h1
    have h3 : Nat.card (SecMod hd) = Nat.card (↥(blockU L) ⧸ zSub L) := rfl
    rw [h3, hK, ← pow_mul, mul_comm f 4]
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  obtain ⟨φ, hφ⟩ := exists_addEquiv_matrix_of_quadratic hfix' hquad' hcard'
  letI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  refine ⟨GaloisField 2 f, inferInstance, inferInstance, ?_, α, hαs, hαker,
    { toFun := fun u => Multiplicative.ofAdd (φ (SecMod.mk hd u))
      map_one' := by rw [SecMod.mk_one, map_zero]; rfl
      map_mul' := fun a b => by rw [SecMod.mk_mul, map_add]; rfl }, ?_, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card, hK]
  · intro y
    obtain ⟨u, hu⟩ := SecMod.mk_surjective hd (φ.symm (Multiplicative.toAdd y))
    refine ⟨u, ?_⟩
    show Multiplicative.ofAdd (φ (SecMod.mk hd u)) = y
    rw [hu, AddEquiv.apply_symm_apply, ofAdd_toAdd]
  · ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← SecMod.mk_eq_zero_iff hd u,
      ← φ.map_eq_zero_iff]
    exact ofAdd_eq_one
  · intro l u v hv
    show φ (SecMod.mk hd v) = (α l : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) *
      φ (SecMod.mk hd u)
    rw [show v = conjU hd l u from Subtype.ext hv, ← SecMod.smul_mk, hφ]

end CFSG.Quasithin.F112R.St84

end
