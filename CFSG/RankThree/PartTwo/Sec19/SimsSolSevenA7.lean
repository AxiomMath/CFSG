module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
public import CFSG.Quasithin.SteinbergCBI16A7

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

open CFSG.AGLEmbedding CFSG.Quasithin.JonesParshall CFSG.Quasithin.SteinbergCB.I16

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem eq_bot_of_stab_le_normalizer (θ : Γ ≃* ↥(alternatingGroup (Fin 7)))
    {V : Type*} [Group V] [Finite V] (hcard : Nat.card V = 16) (φ : Γ →* MulAut V)
    {v : V} (hv : v ≠ 1) {T : Subgroup Γ} (hT : IsPGroup 2 T)
    (hN : ∀ γ : Γ, φ γ v = v → γ ∈ Subgroup.normalizer (T : Set Γ)) : T = ⊥ := by
  by_contra hT1
  letI : MulAction Γ V := MulAction.compHom V φ
  set S := MulAction.stabilizer Γ v
  have hS : Nat.card S ∣ 72 :=
    BlockAltSevenPL.card_dvd_seventyTwo_of_mulEquiv θ hT hT1 fun γ hγ => hN γ hγ
  have hΓ : Nat.card Γ = 2520 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hidx : S.index < 16 := by
    rw [MulAction.index_stabilizer, ← hcard]
    refine Set.ncard_lt_card fun h => ?_
    obtain ⟨γ, hγ⟩ : (1 : V) ∈ MulAction.orbit Γ v := h ▸ Set.mem_univ _
    exact hv ((MulEquiv.map_eq_one_iff (φ γ)).mp hγ)
  have h := S.card_mul_index
  rw [hΓ] at h
  have := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hS) (Nat.le_of_lt_succ hidx)
  omega

theorem exists_eq_of_mem_normalizer (θ : Γ ≃* ↥(alternatingGroup (Fin 7)))
    {V : Type*} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a ^ 2 = 1) (hcard : Nat.card V = 16) (φ : Γ →* MulAut V)
    (hφ : Function.Injective φ) {g : MulAut V}
    (hg : ∀ γ : Γ, ∃ γ' : Γ, g * φ γ * g⁻¹ = φ γ') : ∃ γ₀ : Γ, g = φ γ₀ := by
  obtain ⟨hA, hAs⟩ := BlockAltSevenPL.card_mulAut_eq_and_isSimpleGroup hcomm hsq
    (by rw [hcard]; norm_num)
  have : Finite (MulAut V) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  have hH : Nat.card φ.range = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_congr θ.toEquiv,
      nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hgN : g ∈ Subgroup.normalizer (φ.range : Set (MulAut V)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨_, ⟨γ, rfl⟩, rfl⟩
      obtain ⟨γ', hγ'⟩ := hg γ
      exact ⟨γ', hγ'.symm⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨γ₀, hγ₀⟩ := BlockAltSevenPL.mem_of_mem_normalizer_of_index_eight hA hH hgN
  exact ⟨γ₀, hγ₀.symm⟩

theorem eq_one_of_forall_commute (θ : Γ ≃* ↥(alternatingGroup (Fin 7)))
    {V : Type*} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a ^ 2 = 1) (hcard : Nat.card V = 16) (φ : Γ →* MulAut V)
    (hφ : Function.Injective φ) {g : MulAut V} (hg : ∀ γ : Γ, g * φ γ = φ γ * g) : g = 1 := by
  obtain ⟨γ₀, rfl⟩ := exists_eq_of_mem_normalizer θ hcomm hsq hcard φ hφ fun γ =>
    ⟨γ, by rw [hg γ, mul_inv_cancel_right]⟩
  have hc : θ γ₀ ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro a
    obtain ⟨γ, rfl⟩ := θ.surjective a
    rw [← map_mul, ← map_mul]
    exact congrArg θ (hφ (by rw [map_mul, map_mul, hg γ]))
  rw [alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num), Subgroup.mem_bot,
    MulEquiv.map_eq_one_iff] at hc
  rw [hc, map_one]

theorem exists_coboundary (θ : Γ ≃* ↥(alternatingGroup (Fin 7)))
    {V : Type*} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hsq : ∀ a : V, a ^ 2 = 1) (hcard : Nat.card V = 16) (φ : Γ →* MulAut V)
    (hφ : Function.Injective φ) (c : Γ → V) (hc : ∀ x y : Γ, c (x * y) = c x * φ x (c y)) :
    ∃ v : V, ∀ x : Γ, c x = v * (φ x v)⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 4) hcomm
    hsq (by rw [hcard]; norm_num)
  set M : A7 →* GL (Fin 4) (ZMod 2) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (φ.comp θ.symm.toMonoidHom)
  have hM : Function.Injective M :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective.comp (hφ.comp θ.symm.injective)
  have hMe : ∀ (x : Γ) (w : V),
      Multiplicative.toAdd (e (φ x w)) = matAct M (θ x) (Multiplicative.toAdd (e w)) := by
    intro x w
    rw [matAct_apply, ← CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec]
    simp [M]
  have hf : (fun a : A7 => Multiplicative.toAdd (e (c (θ.symm a)))) ∈ Z1A (matAct M) := by
    refine mem_Z1A.mpr fun a b => ?_
    rw [map_mul, hc, map_mul, toAdd_mul, hMe, MulEquiv.apply_symm_apply]
  obtain ⟨m, hm⟩ := Z1A_le_B1A_A7 M hM hf
  refine ⟨e.symm (Multiplicative.ofAdd (-m)), fun x => ?_⟩
  apply e.injective
  apply Multiplicative.toAdd.injective
  have h : matAct M (θ x) m - m = Multiplicative.toAdd (e (c (θ.symm (θ x)))) :=
    congrFun hm (θ x)
  rw [MulEquiv.symm_apply_apply] at h
  have hneg : matAct M (θ x) (-m) = -matAct M (θ x) m := map_neg _ _
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hMe, MulEquiv.apply_symm_apply, toAdd_ofAdd, hneg,
    ← h]
  abel

section Characters

variable {Q : Type*} [Group Q] [Finite Q]

theorem exists_nonempty_mulEquiv (hcomm : ∀ a b : Q, a * b = b * a) (hsq : ∀ a : Q, a ^ 2 = 1) :
    ∃ n : ℕ, Nonempty (Q ≃* Multiplicative (Fin n → ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (show IsPGroup 2 Q from fun g => ⟨1, by rw [pow_one, hsq]⟩)
  exact ⟨n, CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hsq hn⟩

theorem card_monoidHom_eq (hcomm : ∀ a b : Q, a * b = b * a) (hsq : ∀ a : Q, a ^ 2 = 1) :
    Nat.card (Q →* Multiplicative (ZMod 2)) = Nat.card Q := by
  obtain ⟨n, ⟨e⟩⟩ := exists_nonempty_mulEquiv hcomm hsq
  rw [Nat.card_congr (e.monoidHomCongrLeftEquiv (N := Multiplicative (ZMod 2))),
    ← Nat.card_congr (AddMonoidHom.toMultiplicative (α := Fin n → ZMod 2) (β := ZMod 2)),
    Nat.card_congr
      (AddMonoidHom.toZModLinearMapEquiv 2 (M := Fin n → ZMod 2) (M₁ := ZMod 2)).toEquiv,
    ← Nat.card_congr (Module.piEquiv (Fin n) (ZMod 2) (ZMod 2)).toEquiv, Nat.card_congr e.toEquiv]
  rfl

theorem exists_monoidHom_ne_one (hcomm : ∀ a b : Q, a * b = b * a) (hsq : ∀ a : Q, a ^ 2 = 1)
    {q : Q} (hq : q ≠ 1) : ∃ χ : Q →* Multiplicative (ZMod 2), χ q ≠ 1 := by
  obtain ⟨n, ⟨e⟩⟩ := exists_nonempty_mulEquiv hcomm hsq
  have h : Multiplicative.toAdd (e q) ≠ 0 := by
    rwa [Ne, toAdd_eq_zero, MulEquiv.map_eq_one_iff]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  refine ⟨(AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin n => ZMod 2) i)).comp
    e.toMonoidHom, fun h' => hi ?_⟩
  simpa using congrArg Multiplicative.toAdd h'

end Characters

section Dual

variable {U : Type*} [Group U]

def annihilator (Z : Subgroup U) : Subgroup (U →* Multiplicative (ZMod 2)) where
  carrier := {χ | ∀ z ∈ Z, χ z = 1}
  mul_mem' {a b} ha hb z hz := by rw [MonoidHom.mul_apply, ha z hz, hb z hz, one_mul]
  one_mem' _ _ := rfl
  inv_mem' {a} ha z hz := by rw [MonoidHom.inv_apply, ha z hz, inv_one]

theorem mem_annihilator {Z : Subgroup U} {χ : U →* Multiplicative (ZMod 2)} :
    χ ∈ annihilator Z ↔ ∀ z ∈ Z, χ z = 1 :=
  Iff.rfl

def annihilatorEquiv (Z : Subgroup U) [Z.Normal] :
    annihilator Z ≃ (U ⧸ Z →* Multiplicative (ZMod 2)) where
  toFun χ := QuotientGroup.lift Z χ.1 fun z hz =>
    MonoidHom.mem_ker.mpr (mem_annihilator.mp χ.2 z hz)
  invFun ψ := ⟨ψ.comp (QuotientGroup.mk' Z), fun z hz => by
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz,
      map_one]⟩
  left_inv _ := rfl
  right_inv ψ := MonoidHom.ext fun q => QuotientGroup.induction_on q fun _ => rfl

omit [Finite Γ] in
@[expose] def dualAut (φ : Γ →* MulAut U) {Z : Subgroup U} (hZ : ∀ z ∈ Z, ∀ γ : Γ, φ γ z = z)
    (γ : Γ) : MulAut (annihilator Z) where
  toFun χ := ⟨χ.1.comp (φ γ⁻¹).toMonoidHom, mem_annihilator.mpr fun z hz => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hZ z hz, mem_annihilator.mp χ.2 z hz]⟩
  invFun χ := ⟨χ.1.comp (φ γ).toMonoidHom, mem_annihilator.mpr fun z hz => by
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hZ z hz, mem_annihilator.mp χ.2 z hz]⟩
  left_inv χ := Subtype.ext (MonoidHom.ext fun u => by simp)
  right_inv χ := Subtype.ext (MonoidHom.ext fun u => by simp)
  map_mul' _ _ := rfl

omit [Finite Γ] in
theorem dualAut_apply (φ : Γ →* MulAut U) {Z : Subgroup U} (hZ : ∀ z ∈ Z, ∀ γ : Γ, φ γ z = z)
    (γ : Γ) (χ : annihilator Z) (u : U) :
    (dualAut φ hZ γ χ : U →* Multiplicative (ZMod 2)) u =
      (χ : U →* Multiplicative (ZMod 2)) (φ γ⁻¹ u) :=
  rfl

omit [Finite Γ] in
@[expose] def dualAct (φ : Γ →* MulAut U) {Z : Subgroup U} (hZ : ∀ z ∈ Z, ∀ γ : Γ, φ γ z = z) :
    Γ →* MulAut (annihilator Z) :=
  MonoidHom.mk' (dualAut φ hZ) fun x y => MulEquiv.ext fun χ => Subtype.ext <|
    MonoidHom.ext fun u => by
      rw [MulAut.mul_apply, dualAut_apply, dualAut_apply, dualAut_apply, mul_inv_rev, map_mul,
        MulAut.mul_apply]

omit [Finite Γ] in
theorem dualAct_apply (φ : Γ →* MulAut U) {Z : Subgroup U} (hZ : ∀ z ∈ Z, ∀ γ : Γ, φ γ z = z)
    (γ : Γ) (χ : annihilator Z) (u : U) :
    (dualAct φ hZ γ χ : U →* Multiplicative (ZMod 2)) u =
      (χ : U →* Multiplicative (ZMod 2)) (φ γ⁻¹ u) :=
  rfl

end Dual

theorem eq_bot_of_forall_invariant_trivial (θ : Γ ≃* ↥(alternatingGroup (Fin 7)))
    {U : Type*} [Group U] [Finite U] (hcomm : ∀ a b : U, a * b = b * a)
    (hsq : ∀ a : U, a ^ 2 = 1) (φ : Γ →* MulAut U) (Z : Subgroup U)
    (hZ : ∀ z ∈ Z, ∀ γ : Γ, φ γ z = z) (hindex : Nat.card U = 16 * Nat.card Z)
    (hfaith : ∀ γ : Γ, (∀ u : U, φ γ u * u⁻¹ ∈ Z) → γ = 1)
    (hinv : ∀ χ : U →* Multiplicative (ZMod 2), (∀ (γ : Γ) (u : U), χ (φ γ u) = χ u) → χ = 1) :
    Z = ⊥ := by
  have : Z.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hQcomm : ∀ a b : U ⧸ Z, a * b = b * a := fun a b => by
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hQsq : ∀ a : U ⧸ Z, a ^ 2 = 1 := fun a => by
    induction a using QuotientGroup.induction_on
    rw [← QuotientGroup.mk_pow, hsq, QuotientGroup.mk_one]
  have hQcard : Nat.card (U ⧸ Z) = 16 := by
    have h := Z.card_eq_card_quotient_mul_card_subgroup
    rw [hindex] at h
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h).symm
  have : Finite (U →* Multiplicative (ZMod 2)) := .of_injective _ DFunLike.coe_injective
  have hVcomm : ∀ a b : annihilator Z, a * b = b * a := fun a b => Subtype.ext (mul_comm _ _)
  have hVsq : ∀ a : annihilator Z, a ^ 2 = 1 := fun a => Subtype.ext <| MonoidHom.ext fun u => by
    change (a : U →* Multiplicative (ZMod 2)) u ^ 2 = 1
    rw [← map_pow, hsq, map_one]
  have hVcard : Nat.card (annihilator Z) = 16 := by
    rw [Nat.card_congr (annihilatorEquiv Z), card_monoidHom_eq hQcomm hQsq, hQcard]
  have hsep : ∀ w : U, w ∉ Z → ∃ χ ∈ annihilator Z, χ w ≠ 1 := fun w hw => by
    obtain ⟨χ, hχ⟩ := exists_monoidHom_ne_one hQcomm hQsq (q := (w : U ⧸ Z))
      fun h => hw ((QuotientGroup.eq_one_iff w).mp h)
    exact ⟨χ.comp (QuotientGroup.mk' Z), fun z hz => by
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz,
        map_one], hχ⟩
  have hψ : Function.Injective (dualAct φ hZ) := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    refine hfaith γ fun u => ?_
    by_contra hu
    obtain ⟨χ, hχZ, hχ⟩ := hsep _ hu
    apply hχ
    have h1 : dualAct φ hZ γ⁻¹ = 1 := by rw [map_inv, hγ, inv_one]
    have h2 : χ (φ γ u) = χ u := by
      have h := congrArg (fun a : MulAut (annihilator Z) =>
        ((a ⟨χ, hχZ⟩ : annihilator Z) : U →* Multiplicative (ZMod 2)) u) h1
      simpa only [dualAct_apply, inv_inv, MulAut.one_apply] using h
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  by_contra hz1
  obtain ⟨l, hl⟩ := exists_monoidHom_ne_one hcomm hsq hz1
  let c : Γ → annihilator Z := fun γ => ⟨l.comp (φ γ⁻¹).toMonoidHom * l⁻¹, fun z' hz' => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      hZ z' hz', mul_inv_cancel]⟩
  have hcv : ∀ (γ : Γ) (w : U), (c γ : U →* Multiplicative (ZMod 2)) w = l (φ γ⁻¹ w) * (l w)⁻¹ :=
    fun _ _ => rfl
  have hc : ∀ x y : Γ, c (x * y) = c x * dualAct φ hZ x (c y) := by
    intro x y
    refine Subtype.ext (MonoidHom.ext fun u => ?_)
    show (c (x * y) : U →* Multiplicative (ZMod 2)) u = (c x : U →* Multiplicative (ZMod 2)) u *
      (dualAct φ hZ x (c y) : U →* Multiplicative (ZMod 2)) u
    rw [dualAct_apply, hcv, hcv, hcv, mul_inv_rev, map_mul, MulAut.mul_apply]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv]
    abel
  obtain ⟨μ, hμ⟩ := exists_coboundary θ hVcomm hVsq hVcard (dualAct φ hZ) hψ c hc
  have hκ : l * (μ : U →* Multiplicative (ZMod 2)) = 1 := hinv _ fun γ u => by
    have h := congrArg (fun a : annihilator Z => (a : U →* Multiplicative (ZMod 2)) u) (hμ γ⁻¹)
    simp only [hcv, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.mul_apply,
      MonoidHom.inv_apply, dualAct_apply] at h
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply]
    apply Multiplicative.toAdd.injective
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_mul, toAdd_inv] at h' ⊢
    linear_combination h'
  have h := congrArg (fun χ : U →* Multiplicative (ZMod 2) => χ z) hκ
  simp only [MonoidHom.mul_apply, MonoidHom.one_apply, mem_annihilator.mp μ.2 z hz,
    mul_one] at h
  exact hl h

end CFSG.RankThree.PartTwo.Sec19.SolSeven
