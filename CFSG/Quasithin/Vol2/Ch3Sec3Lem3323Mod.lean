module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Chief
public import CFSG.Quasithin.Vol2.Ch3Sec3CZL32

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement Pointwise

namespace Mod3323

section Field2

variable {F : Type} [Field F] [Fintype F]

theorem eq_zero_or_one (hF : Fintype.card F = 2) (x : F) : x = 0 ∨ x = 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨hx0, hx1⟩ := h
  have h3 : ({0, 1, x} : Finset F).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hx1.symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨zero_ne_one, hx0.symm⟩
  have := Finset.card_le_univ ({0, 1, x} : Finset F)
  omega

@[expose] noncomputable def toZ2 (hF : Fintype.card F = 2) : F ≃+* ZMod 2 :=
  FiniteField.ringEquivOfCardEq (by rw [hF, ZMod.card])

@[expose] noncomputable def toL3 (hF : Fintype.card F = 2) :
    Matrix.SpecialLinearGroup (Fin 3) F →* L3.Γ :=
  Matrix.SpecialLinearGroup.map (toZ2 hF).toRingHom

theorem toL3_apply (hF : Fintype.card F = 2) (g : Matrix.SpecialLinearGroup (Fin 3) F)
    (i j : Fin 3) :
    ((toL3 hF g : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j =
      toZ2 hF ((g : Matrix (Fin 3) (Fin 3) F) i j) := by
  rw [toL3, Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem toL3_surjective (hF : Fintype.card F = 2) : Function.Surjective (toL3 hF) := by
  intro γ
  refine ⟨Matrix.SpecialLinearGroup.map (toZ2 hF).symm.toRingHom γ, ?_⟩
  apply Subtype.ext
  ext i j
  rw [toL3_apply, Matrix.SpecialLinearGroup.map_apply_coe]
  simp

theorem act_toL3 (hF : Fintype.card F = 2) (g : Matrix.SpecialLinearGroup (Fin 3) F)
    (x : Fin 3 → F) :
    L3.act (toL3 hF g) (toZ2 hF ∘ x) = toZ2 hF ∘ (g : Matrix (Fin 3) (Fin 3) F).mulVec x := by
  funext i
  show ((toL3 hF g : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (toZ2 hF ∘ x) i = _
  rw [toL3, Matrix.SpecialLinearGroup.map_apply_coe]
  exact (RingHom.map_mulVec (toZ2 hF).toRingHom (g : Matrix (Fin 3) (Fin 3) F) x i).symm

theorem toL3_injective (hF : Fintype.card F = 2) : Function.Injective (toL3 hF) := by
  intro g h hgh
  apply Subtype.ext
  ext i j
  have := congrArg (fun k : L3.Γ => (k : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) hgh
  simp only [toL3, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact (toZ2 hF).injective this

theorem card_eq_two {n : ℕ} (hFc : Fintype.card F = 2 ^ n)
    (h : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) = 168) : Fintype.card F = 2 := by
  have h2 := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := F) (n := 3)
    (by norm_num)
  have hF : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hFc]
  rw [h, hF, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at h2
  have hn1 : 1 ≤ n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    have := Fintype.one_lt_card (α := F)
    omega
  have hn : n ≤ 1 := by
    by_contra hcon
    push Not at hcon
    have hdvd : (2 ^ n) ^ (3 * (3 - 1) / 2) ∣ 168 := by
      rw [h2]
      exact Dvd.intro (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) (by ring)
    have h16 : 16 ∣ (2 ^ n) ^ (3 * (3 - 1) / 2) := by
      rw [← pow_mul, show (16 : ℕ) = 2 ^ 4 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have := h16.trans hdvd
    omega
  rw [hFc, show n = 1 by omega]
  norm_num

end Field2

theorem exists_fix {I : Subgroup L3.Γ} (hI : IsPGroup 2 I) (hidx : ¬ 2 ∣ I.index) :
    ∃ e : L3.Vec, ∀ v, (∀ g ∈ I, L3.act g v = v) → v = 0 ∨ v = e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 L3.Γ := hI.toSylow hidx
  let B : Sylow 2 L3.Γ := CZL32.isPGroup_bSub.toSylow CZL32.not_two_dvd_index_bSub
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq L3.Γ B P
  have hmem : ∀ b ∈ CZL32.bSub, x * b * x⁻¹ ∈ I := by
    intro b hb
    have h1 : x * b * x⁻¹ ∈ ((x • B : Sylow 2 L3.Γ) : Subgroup L3.Γ) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have e : (MulAut.conj x)⁻¹ • (x * b * x⁻¹) = b := by
        rw [MulAut.smul_def, MulAut.conj_inv_apply]
        group
      rw [e]
      exact hb
    rw [hx] at h1
    exact h1
  refine ⟨L3.act x CZL32.e1, fun v hv => ?_⟩
  have key : ∀ b ∈ CZL32.bSub, L3.act b (L3.act x⁻¹ v) = L3.act x⁻¹ v := by
    intro b hb
    have h1 := hv _ (hmem b hb)
    rw [L3.act_mul, L3.act_mul] at h1
    have := congrArg (L3.act x⁻¹) h1
    rwa [L3.act_inv_act] at this
  rcases CZL32.fix_B _ (key _ CZL32.b1_mem) (key _ CZL32.b2_mem) with h0 | he
  · left
    have := congrArg (L3.act x) h0
    rwa [L3.act_act_inv, L3.act_zero] at this
  · right
    have := congrArg (L3.act x) he
    rwa [L3.act_act_inv] at this

theorem eq_one_of_central' : ∀ g : L3.Γ, (∀ h : L3.Γ, g * h = h * g) → g = 1 := by
  decide +kernel

theorem eq_one_of_central {g : L3.Γ} (hg : ∀ h : L3.Γ, g * h = h * g) : g = 1 :=
  eq_one_of_central' g hg

variable {G : Type} [Group G]

theorem not_sq_dvd_168 {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : ¬ r ^ 2 ∣ 168 := by
  intro h
  have hle : r ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h
  have hr12 : r ≤ 12 := by nlinarith
  interval_cases r <;> revert hr hr2 h <;> decide

theorem exists_modO2Surj [Finite G] {T M L D : Subgroup G} (h : Hyp331 G T M L D)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hP : IsPSL 3 2 1 ↥(autOn L (vPlus L T))) :
    ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧
      ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ Subgroup.centralizer (vPlus L T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := hP
  let e₁ : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    e₀.trans (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 F
      (by rw [hcard]; norm_num))
  let φ := InternalSec.autOnHom hLV
  have hφs : Function.Surjective φ := InternalSec.autOnHom_surjective hLV
  let α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    ((e₁.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2))).toMonoidHom).comp φ
  have hαφ : ∀ l, α l = 1 ↔ φ l = 1 := fun l => by
    simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  have hαs : Function.Surjective α := by
    intro y
    obtain ⟨z, hz⟩ := (e₁.trans (specialLinearGroupEquivStatedSL 3 (ZMod 2))).surjective y
    obtain ⟨l, rfl⟩ := hφs z
    exact ⟨l, hz⟩
  have hNK : CFSG.pCore 2 ↥L ≤ φ.ker := by
    intro l hl
    rw [InternalSec.mem_ker_autOnHom]
    exact hQC (hOQ ((Lem3328.mem_pCore_iff l).mp hl))
  have hKN : φ.ker ≤ CFSG.pCore 2 ↥L := by
    set N := CFSG.pCore 2 ↥L with hN
    set K := φ.ker with hK
    have hNn : N.Normal := CFSG.pCore_normal
    have hq := h.Lq
    have : Group.IsPerfect (↥L ⧸ N) := hq.1
    have hKn : (K.map (QuotientGroup.mk' N)).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
        (K.map (QuotientGroup.mk' N)) with hc | htop
    · let e : (↥L ⧸ N) ⧸ K.map (QuotientGroup.mk' N) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
        (QuotientGroup.quotientQuotientEquivQuotient N K hNK).trans
          ((QuotientGroup.quotientKerEquivOfSurjective φ hφs).trans e₁)
      have hp := CFSG.Quasithin.isPGroup_two_of_mulEquiv_cyclic_odd_sylow
        (K.map (QuotientGroup.mk' N)) hc e fun r hr hr2 _ Q =>
          CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd
            (by rw [card_L3Γ]; exact not_sq_dvd_168 hr hr2) Q
      have hK2 : IsPGroup 2 ↥K := by
        rintro ⟨k, hk⟩
        obtain ⟨a, ha⟩ := hp ⟨QuotientGroup.mk' N k, ⟨k, hk, rfl⟩⟩
        have ha' : QuotientGroup.mk' N (k ^ 2 ^ a) = 1 := by
          have := congrArg Subtype.val ha
          simpa using this
        have hkN : k ^ 2 ^ a ∈ N := (QuotientGroup.eq_one_iff _).mp ha'
        obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hkN⟩
        refine ⟨a + b, Subtype.ext ?_⟩
        have hb' : (k ^ 2 ^ a) ^ 2 ^ b = 1 := by
          have := congrArg Subtype.val hb
          simpa using this
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, pow_mul, hb']
      exact le_sSup ⟨inferInstance, hK2⟩
    · exfalso
      have htriv : ∀ l : ↥L, φ l = 1 := by
        intro l
        have hl : QuotientGroup.mk' N l ∈ K.map (QuotientGroup.mk' N) := htop ▸ Subgroup.mem_top _
        obtain ⟨k, hk, hkl⟩ := hl
        have h1 : k⁻¹ * l ∈ N := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
          rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hkl
          rw [hkl, inv_mul_cancel]
        have h2 : l ∈ K := by
          have := K.mul_mem hk (hNK h1)
          simpa using this
        exact h2
      have hcard1 : Nat.card ↥(autOn L (vPlus L T)) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun a b => ?_⟩, inferInstance⟩
        obtain ⟨x, rfl⟩ := hφs a
        obtain ⟨y, rfl⟩ := hφs b
        rw [htriv x, htriv y]
      have h168 : Nat.card ↥(autOn L (vPlus L T)) = 168 := by
        rw [Nat.card_congr e₁.toEquiv, card_L3Γ]
      omega
  refine ⟨α, ⟨hαs, ?_⟩, fun l => ?_⟩
  · ext l
    rw [MonoidHom.mem_ker, hαφ, ← MonoidHom.mem_ker]
    exact ⟨fun hl => hKN hl, fun hl => hNK hl⟩
  · rw [hαφ, ← MonoidHom.mem_ker, InternalSec.mem_ker_autOnHom]

section Center

variable {L : Subgroup G}

theorem mem_pCoreOf_of_central {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (hα : IsModO2Surj L α)
    {c : G} (hc : c ∈ L) (hcen : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) :
    c ∈ pCoreOf 2 L := by
  have hker : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ pCoreOf 2 L := fun l => by
    rw [← MonoidHom.mem_ker, hα.2, Lem3328.mem_pCore_iff]
  have hcomm : ∀ x : ↥L, α ⟨c, hc⟩ * α x = α x * α ⟨c, hc⟩ := by
    intro x
    have hmem : c * x * c⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hc x.2) (L.inv_mem hc)) (L.inv_mem x.2)
    have h2 := (hker ⟨_, hmem⟩).mpr (hcen x x.2)
    have e : (⟨_, hmem⟩ : ↥L) = ⟨c, hc⟩ * x * (⟨c, hc⟩)⁻¹ * x⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc α ⟨c, hc⟩ * α x =
          α ⟨c, hc⟩ * α x * (α ⟨c, hc⟩)⁻¹ * (α x)⁻¹ * (α x * α ⟨c, hc⟩) := by group
      _ = α x * α ⟨c, hc⟩ := by rw [h2, one_mul]
  let e := (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  have h1 : e (α ⟨c, hc⟩) = 1 := by
    refine eq_one_of_central fun g => ?_
    obtain ⟨x, hx⟩ := hα.1 (e.symm g)
    rw [← e.apply_symm_apply g, ← hx, ← e.map_mul, ← e.map_mul, hcomm x]
  exact (hker _).mp (e.injective (h1.trans (map_one e).symm))

theorem le_or_sup_eq (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα : IsModO2Surj L α)
    {N : Subgroup G} (hNL : N ≤ L)
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) : N ≤ pCoreOf 2 L ∨ N ⊔ pCoreOf 2 L = L := by
  set P := CFSG.pCore 2 ↥L with hP
  have hNn : (N.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mpr hLN
  have hmn : ((N.subgroupOf L).map (QuotientGroup.mk' P)).Normal :=
    Subgroup.Normal.map hNn _ (QuotientGroup.mk'_surjective P)
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq
      ((N.subgroupOf L).map (QuotientGroup.mk' P)) with hc | htop
  · left
    intro n hn
    refine mem_pCoreOf_of_central hα (hNL hn) fun x hx => ?_
    have h1 : QuotientGroup.mk' P ⟨n, hNL hn⟩ ∈ Subgroup.center (↥L ⧸ P) :=
      hc ⟨⟨n, hNL hn⟩, hn, rfl⟩
    have h2 := Subgroup.mem_center_iff.mp h1 (QuotientGroup.mk' P ⟨x, hx⟩)
    have hmem : n * x * n⁻¹ * x⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem (hNL hn) hx) (L.inv_mem (hNL hn))) (L.inv_mem hx)
    have h4 : QuotientGroup.mk' P (⟨_, hmem⟩ : ↥L) = 1 := by
      have e : (⟨_, hmem⟩ : ↥L) = ⟨n, hNL hn⟩ * ⟨x, hx⟩ * (⟨n, hNL hn⟩)⁻¹ * (⟨x, hx⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← h2]
      group
    exact (Lem3328.mem_pCore_iff _).mp ((QuotientGroup.eq_one_iff _).mp h4)
  · right
    refine le_antisymm (sup_le hNL (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) fun l hl => ?_
    have h1 : QuotientGroup.mk' P ⟨l, hl⟩ ∈ (N.subgroupOf L).map (QuotientGroup.mk' P) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnl⟩ := h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnl
    have h2 : (n : G)⁻¹ * l ∈ pCoreOf 2 L := (Lem3328.mem_pCore_iff _).mp hnl
    have e : l = (n : G) * ((n : G)⁻¹ * l) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hn h2

end Center

section Inner

@[expose] def cenMod (L : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (L : Set G) ∧
    ∀ x ∈ L, g * x * g⁻¹ * x⁻¹ ∈ pCoreOf 2 L}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun x hx => ?_⟩
    have hbx : b * x * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hb x).mp hx
    have h1 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L ha) _).mp (hb' x hx)
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 (ha' x hx)
  one_mem' := ⟨Subgroup.one_mem _, fun x _ => by
    simp only [one_mul, inv_one, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ ha, fun x hx => ?_⟩
    have hy : a⁻¹ * x * a ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) x).mp hx
      simpa using this
    have h1 := Subgroup.inv_mem _ (ha' _ hy)
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by group
    rw [e]
    exact h1

theorem mem_qL_of_cenMod [Finite G] {T L : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT2 : IsPGroup 2 T) {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))}
    (hα : IsModO2Surj L α) {c : G}
    (hc : c ∈ L ⊔ T) (hcen : ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L) : c ∈ qL L T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  set K := cenMod L ⊓ (L ⊔ T) with hK
  have hKLT : K ≤ L ⊔ T := inf_le_right
  have hnorm : L ⊔ T ≤ Subgroup.normalizer (K : Set G) := by
    intro g hg
    refine mem_normalizer_inf ?_ (Subgroup.le_normalizer hg)
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g' ∈ L ⊔ T, ∀ k ∈ cenMod L, g' * k * g'⁻¹ ∈ cenMod L := by
      rintro g' hg' k ⟨hk, hk'⟩
      have hg'N := hLTN hg'
      refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg'N hk) (Subgroup.inv_mem _ hg'N),
        fun x hx => ?_⟩
      have hx' : g'⁻¹ * x * g'⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg'N) x).mp hx
      have h1 := hk' _ hx'
      have h2 : g' * (k * (g'⁻¹ * x * g'⁻¹⁻¹) * k⁻¹ * (g'⁻¹ * x * g'⁻¹⁻¹)⁻¹) * g'⁻¹ ∈
          pCoreOf 2 L :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hg'N) _).mp h1
      have e : g' * k * g'⁻¹ * x * (g' * k * g'⁻¹)⁻¹ * x⁻¹ =
          g' * (k * (g'⁻¹ * x * g'⁻¹⁻¹) * k⁻¹ * (g'⁻¹ * x * g'⁻¹⁻¹)⁻¹) * g'⁻¹ := by group
      rw [e]
      exact h2
    intro k
    constructor
    · exact key g hg k
    · intro hk
      have := key g⁻¹ ((L ⊔ T).inv_mem hg) _ hk
      simpa [mul_assoc] using this
  have hK2 : IsPGroup 2 ↥K := by
    rintro ⟨k, hkC, hkLT⟩
    obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp hkLT
    obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
    have ha' : t ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hstep : ∀ n : ℕ, ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨l', hl', e⟩ := ih
        refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' ?_, ?_⟩
        · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) l).mp hl
        · rw [pow_succ, e]
          group
    obtain ⟨l', hl', e⟩ := hstep (2 ^ a)
    rw [ha', mul_one] at e
    have hkC' : (l * t) ^ 2 ^ a ∈ cenMod L := Subgroup.pow_mem _ hkC _
    have hO : (l * t) ^ 2 ^ a ∈ pCoreOf 2 L := by
      rw [e] at hkC' ⊢
      exact mem_pCoreOf_of_central hα hl' hkC'.2
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hO⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((l * t) ^ 2 ^ a) ^ 2 ^ b = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_add, pow_mul, hb']
  have hKQ : K ≤ qL L T :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKLT hnorm hK2
  exact hKQ ⟨⟨hLTN hc, hcen⟩, hc⟩

theorem exists_eq_mul_of_intertwiner [Finite G] {T L : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α) {t : G} (ht : t ∈ T)
    (θ : (Fin 3 → F) →+ (Fin 3 → F)) (hθ0 : ∃ v, θ v ≠ 0)
    (hθ : ∀ (l l' : ↥L), (l' : G) = t * l * t⁻¹ → ∀ v,
      θ (((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) =
        ((α l' : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (θ v)) :
    ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c := by
  classical
  have hker : ∀ l : ↥L, α l = 1 ↔ (l : G) ∈ pCoreOf 2 L := fun l => by
    rw [← MonoidHom.mem_ker, hα.2, Lem3328.mem_pCore_iff]
  have htN : t ∈ Subgroup.normalizer (L : Set G) := hTL ht
  have hconj : ∀ l : ↥L, t * l * t⁻¹ ∈ L := fun l => (Subgroup.mem_normalizer_iff.mp htN l).mp l.2
  have hinj : ∀ v, θ v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨w, hw⟩ := hθ0
    apply hw
    let W : AddSubgroup (Fin 3 → F) := θ.ker
    have hW : ∀ g : Matrix.SpecialLinearGroup (Fin 3) F, ∀ u ∈ W,
        (g : Matrix (Fin 3) (Fin 3) F).mulVec u ∈ W := by
      intro g u hu
      obtain ⟨l, hl⟩ := hα.1 (specialLinearGroupEquivStatedSL 3 F g)
      have h1 := hθ l ⟨_, hconj l⟩ rfl u
      have hu' : θ u = 0 := hu
      rw [hu', Matrix.mulVec_zero, hl, specialLinearGroupEquivStatedSL_coe] at h1
      exact h1
    exact Chief3323.eq_top_of_invariant W hW hv hv0 w
  let θl : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
    { toFun := θ
      map_add' := θ.map_add
      map_smul' := fun r x => by
        rcases eq_zero_or_one hF r with rfl | rfl
        · simp
        · simp }
  set Mθ := LinearMap.toMatrix' θl with hMθ
  have hMv : ∀ v, Mθ.mulVec v = θ v := fun v => LinearMap.toMatrix'_mulVec θl v
  have hdet : Mθ.det = 1 := by
    have h0 : Mθ.det ≠ 0 := by
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      rw [hMv] at hv
      exact hv0 (hinj v hv)
    rcases eq_zero_or_one hF Mθ.det with h | h
    · exact absurd h h0
    · exact h
  let g₀ : Matrix.SpecialLinearGroup (Fin 3) F := ⟨Mθ, hdet⟩
  obtain ⟨l₀, hl₀⟩ := hα.1 (specialLinearGroupEquivStatedSL 3 F g₀)
  have hl₀m : ((α l₀ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = Mθ := by
    rw [hl₀, specialLinearGroupEquivStatedSL_coe]
  have hcomm : ∀ l : ↥L, α (l₀ * l) = α (⟨_, hconj l⟩ * l₀) := by
    intro l
    apply Subtype.ext
    apply Units.ext
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, map_mul, Subgroup.coe_mul, Units.val_mul,
      ← Matrix.mulVec_mulVec, hl₀m, hMv]
    exact hθ l ⟨_, hconj l⟩ rfl v
  refine ⟨l₀, l₀.2, (l₀ : G)⁻¹ * t, ?_, by group⟩
  refine mem_qL_of_cenMod hTL hT2 hα₂ (Subgroup.mul_mem _ (Subgroup.mem_sup_left
    (L.inv_mem l₀.2)) (Subgroup.mem_sup_right ht)) fun x hx => ?_
  have hmem : (l₀ : G)⁻¹ * (t * x * t⁻¹) * l₀ * x⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem (L.inv_mem l₀.2) (hconj ⟨x, hx⟩)) l₀.2) (L.inv_mem hx)
  have h1 : α ⟨_, hmem⟩ = 1 := by
    have e : (⟨_, hmem⟩ : ↥L) = l₀⁻¹ * (⟨_, hconj ⟨x, hx⟩⟩ * l₀) * (⟨x, hx⟩)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, map_mul, ← hcomm ⟨x, hx⟩, map_mul, map_inv, map_inv]
    group
  have e : (l₀ : G)⁻¹ * t * x * ((l₀ : G)⁻¹ * t)⁻¹ * x⁻¹ =
      (l₀ : G)⁻¹ * (t * x * t⁻¹) * l₀ * x⁻¹ := by group
  rw [e]
  exact (hker _).mp h1

theorem exists_eq_mul_of_natural [Finite G] {T L W : Subgroup G}
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hα : IsModO2Surj L α) {k : ℕ} (hk : 0 < k)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (β : ↥W →* Multiplicative (Fin k → Fin 3 → F)) (hβs : Function.Surjective β)
    (hβi : Function.Injective β)
    (hβe : ∀ (a : ↥L) (u v : ↥W), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    {t : G} (ht : t ∈ T) (htW : t ∈ Subgroup.normalizer (W : Set G)) :
    ∃ l ∈ L, ∃ c ∈ qL L T, t = l * c := by
  classical
  let eβ : ↥W ≃* Multiplicative (Fin k → Fin 3 → F) := MulEquiv.ofBijective β ⟨hβi, hβs⟩
  let ct : MulAut ↥W := W.normalizerMonoidHom ⟨t, htW⟩
  have hct : ∀ u : ↥W, ((ct u : ↥W) : G) = t * u * t⁻¹ := fun _ => rfl
  let Φ : (Fin k → Fin 3 → F) →+ (Fin k → Fin 3 → F) :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (eβ (ct (eβ.symm (Multiplicative.ofAdd x)))))
      (fun a b => by rw [ofAdd_add, map_mul, map_mul, map_mul, toAdd_mul])
  have hΦ : ∀ u : ↥W, Φ (Multiplicative.toAdd (β u)) = Multiplicative.toAdd (β (ct u)) := by
    intro u
    show Multiplicative.toAdd (eβ (ct (eβ.symm (Multiplicative.ofAdd
      (Multiplicative.toAdd (β u)))))) = _
    rw [ofAdd_toAdd]
    have : eβ.symm (β u) = u := eβ.symm_apply_apply u
    rw [this]
    rfl
  have hconj : ∀ l : ↥L, t * l * t⁻¹ ∈ L := fun l =>
    (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp l.2
  have hΦe : ∀ (l : ↥L) (x : Fin k → Fin 3 → F) (i : Fin k),
      Φ (fun j => ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (x j)) i =
        ((α ⟨_, hconj l⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Φ x i) := by
    intro l x i
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β u) := by rw [hu]; rfl
    have hlu : (l : G) * u * (l : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW l.2) u).mp u.2
    let v : ↥W := ⟨_, hlu⟩
    have hv : (fun j => ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (x j)) =
        Multiplicative.toAdd (β v) := by
      funext j
      rw [hβe l u v rfl j, hx]
    have hcv : ((ct v : ↥W) : G) = (t * l * t⁻¹) * (ct u : G) * (t * l * t⁻¹)⁻¹ := by
      rw [hct, hct]
      show t * ((l : G) * u * (l : G)⁻¹) * t⁻¹ = _
      group
    rw [hv, hΦ, hx, hΦ, hβe ⟨_, hconj l⟩ (ct u) (ct v) hcv i]
  have hΦinj : ∀ x, Φ x = 0 → x = 0 := by
    intro x hx
    have h1 : eβ (ct (eβ.symm (Multiplicative.ofAdd x))) = 1 := by
      have := congrArg Multiplicative.ofAdd hx
      simpa [Φ] using this
    have h2 : Multiplicative.ofAdd x = 1 := by
      have h3 := (map_eq_one_iff eβ eβ.injective).mp h1
      have h4 := (map_eq_one_iff ct ct.injective).mp h3
      exact (map_eq_one_iff eβ.symm eβ.symm.injective).mp h4
    simpa using congrArg Multiplicative.toAdd h2
  set j₀ : Fin k := ⟨0, hk⟩ with hj₀
  have hx0 : (Pi.single j₀ (Pi.single 0 1) : Fin k → Fin 3 → F) ≠ 0 := by
    intro h
    have := congrFun (congrFun h j₀) 0
    simp at this
  obtain ⟨i₀, hi₀⟩ : ∃ i, Φ (Pi.single j₀ (Pi.single 0 1)) i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (hΦinj _ (funext hcon))
  let θ : (Fin 3 → F) →+ (Fin 3 → F) :=
    (Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i₀).comp
      (Φ.comp (AddMonoidHom.single (fun _ : Fin k => Fin 3 → F) j₀))
  have hθv : ∀ v, θ v = Φ (Pi.single j₀ v) i₀ := fun _ => rfl
  refine exists_eq_mul_of_intertwiner hTL hT2 hα₂ hF hα ht θ ⟨Pi.single 0 1, by
    rw [hθv]; exact hi₀⟩ fun l l' hl' v => ?_
  have hl'e : l' = ⟨_, hconj l⟩ := Subtype.ext hl'
  subst hl'e
  have harg : (Pi.single j₀ (((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v) :
      Fin k → Fin 3 → F) = fun j => ((α l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        ((Pi.single j₀ v : Fin k → Fin 3 → F) j) := by
    funext j
    by_cases hj : j = j₀
    · rw [hj]
      simp
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, Matrix.mulVec_zero]
  rw [hθv, hθv, harg, hΦe]

end Inner

end Mod3323

end CFSG.Quasithin.H13
