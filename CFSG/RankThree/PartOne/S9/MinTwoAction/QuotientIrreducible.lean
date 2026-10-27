module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientDefs
public import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.GroupTheory.SteinbergBM CFSG.RankThree.PartOne.Quotient36
open scoped commutatorElement

namespace Quotient36

section Aux

variable {R A : Type*} [Group R] [Group A] [MulDistribMulAction A R]

theorem quotient_centralized [Finite R] [Finite A] (hR : IsPGroup 2 R) (hA : ¬ 2 ∣ Nat.card A)
    (K : Subgroup R) [K.Normal] (hinv : CFSG.IsInvariant A R K)
    (hmin : ∀ U : Subgroup R, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      actionCommutator A U = U → U ≤ K) :
    letI : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
    ∀ T : Subgroup (R ⧸ K), T ≠ ⊤ → (∀ a : A, ∀ s ∈ T, a • s ∈ T) →
      ∀ a : A, ∀ s ∈ T, a • s = s := by
  let _ : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
  intro T hT hTinv a s hs
  have hsmul : ∀ (a : A) (x : R), a • (x : R ⧸ K) = ((a • x : R) : R ⧸ K) := fun _ _ => rfl
  set U : Subgroup R := T.comap (QuotientGroup.mk' K) with hU
  have hmemU : ∀ x : R, x ∈ U ↔ (x : R ⧸ K) ∈ T := fun _ => Iff.rfl
  have hUtop : U ≠ ⊤ := by
    intro h
    apply hT
    rw [eq_top_iff]
    intro t _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective t
    exact (hmemU x).mp (h ▸ Subgroup.mem_top x)
  have hUinv : ∀ a : A, ∀ x ∈ U, a • x ∈ U := by
    intro a x hx
    rw [hmemU, ← hsmul]
    exact hTinv a _ ((hmemU x).mp hx)
  have hU0le : actionCommutator A U ≤ U := actionCommutator_le_of_invariant hUinv
  have hU0K : actionCommutator A U ≤ K := by
    refine hmin _ (lt_of_le_of_lt hU0le (lt_top_iff_ne_top.mpr hUtop))
      (fun a x hx => smul_mem_actionCommutator_of_invariant hUinv a hx)
      (actionCommutator_actionCommutator_of_isPGroup Nat.prime_two (hR.to_subgroup U) hA hUinv)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  have hx : x ∈ U := (hmemU x).mpr hs
  rw [hsmul, eq_comm, QuotientGroup.eq]
  exact hU0K (gen_mem_actionCommutator hx a)

theorem quotient_nontrivial_action (K : Subgroup R) [K.Normal]
    (hinv : CFSG.IsInvariant A R K) (hKtop : K ≠ ⊤)
    (hRA : actionCommutator A (⊤ : Subgroup R) = ⊤) :
    letI : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
    ∃ (a : A) (s : R ⧸ K), a • s ≠ s := by
  let _ : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
  by_contra h
  push Not at h
  apply hKtop
  rw [eq_top_iff, ← hRA]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, -, a, rfl⟩
  have h1 := h a (x : R ⧸ K)
  change ((a • x : R) : R ⧸ K) = (x : R ⧸ K) at h1
  exact QuotientGroup.eq.mp h1.symm

end Aux

section Rep

variable {R A : Type*} [Group R] [Group A] [MulDistribMulAction A R]
  {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem rep_eq_of_mk_eq (ρR : Representation k R W) (K : Subgroup R) [K.Normal]
    (hK : ∀ r, r ∈ K ↔ ρR r = 1) {x y : R} (h : (x : R ⧸ K) = y) : ρR x = ρR y := by
  have h1 : ρR x⁻¹ * ρR y = 1 := by
    rw [← map_mul]
    exact (hK _).mp (QuotientGroup.eq.mp h)
  have h2 : ρR x * ρR x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  calc ρR x = ρR x * 1 := (mul_one _).symm
    _ = ρR x * (ρR x⁻¹ * ρR y) := by rw [h1]
    _ = (ρR x * ρR x⁻¹) * ρR y := (mul_assoc _ _ _).symm
    _ = ρR y := by rw [h2, one_mul]

theorem rep_central_eq_neg_one [Nontrivial W] (hk : (2 : k) ≠ 0)
    (ρR : Representation k R W) (ρA : Representation k A W)
    (hcompat : ∀ (a : A) (r : R), ρA a * ρR r = ρR (a • r) * ρA a)
    (hirr : ∀ U : Submodule k W, (∀ r : R, ∀ w ∈ U, ρR r w ∈ U) →
      (∀ a : A, ∀ w ∈ U, ρA a w ∈ U) → U = ⊥ ∨ U = ⊤)
    (K : Subgroup R) [K.Normal] (hK : ∀ r, r ∈ K ↔ ρR r = 1)
    (hinv : CFSG.IsInvariant A R K) (z : R)
    (hz : (z : R ⧸ K) ∈ Subgroup.center (R ⧸ K))
    (hzfix : letI : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
      ∀ a : A, a • (z : R ⧸ K) = z)
    (hz2 : (z : R ⧸ K) ^ 2 = 1) (hz1 : (z : R ⧸ K) ≠ 1) :
    ρR z = -1 := by
  let Z : Module.End k W := ρR z
  have hZR : ∀ r : R, Z * ρR r = ρR r * Z := by
    intro r
    have h1 : ((z * r : R) : R ⧸ K) = ((r * z : R) : R ⧸ K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact ((Subgroup.mem_center_iff.mp hz) (r : R ⧸ K)).symm
    have h2 := rep_eq_of_mk_eq ρR K hK h1
    change ρR z * ρR r = ρR r * ρR z
    rw [← map_mul, ← map_mul, h2]
  have hZA : ∀ a : A, Z * ρA a = ρA a * Z := by
    intro a
    have h1 : ((a • z : R) : R ⧸ K) = (z : R ⧸ K) := hzfix a
    have h2 := rep_eq_of_mk_eq ρR K hK h1
    have h3 := hcompat a z
    rw [h2] at h3
    exact h3.symm
  have hZZ : Z * Z = 1 := by
    have h1 : ((z ^ 2 : R) : R ⧸ K) = ((1 : R) : R ⧸ K) := by
      rw [QuotientGroup.mk_pow, hz2, QuotientGroup.mk_one]
    have h2 := rep_eq_of_mk_eq ρR K hK h1
    change ρR z * ρR z = 1
    rw [← map_mul, ← pow_two, h2, map_one]
  have hinvU : ∀ c : k, (∀ w, Z w = c • w → ∀ r : R, Z (ρR r w) = c • ρR r w) := by
    intro c w hw r
    have := congrArg (fun f : Module.End k W => f w) (hZR r)
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_smul]
  have hinvA : ∀ c : k, (∀ w, Z w = c • w → ∀ a : A, Z (ρA a w) = c • ρA a w) := by
    intro c w hw a
    have := congrArg (fun f : Module.End k W => f w) (hZA a)
    simp only [Module.End.mul_apply] at this
    rw [this, hw, map_smul]
  have hdich : ∀ c : k, Module.End.eigenspace Z c = ⊥ ∨ Module.End.eigenspace Z c = ⊤ := by
    intro c
    refine hirr _ (fun r w hw => ?_) (fun a w hw => ?_)
    · rw [Module.End.mem_eigenspace_iff] at hw ⊢
      exact hinvU c w hw r
    · rw [Module.End.mem_eigenspace_iff] at hw ⊢
      exact hinvA c w hw a
  have hnot1 : Module.End.eigenspace Z 1 ≠ ⊤ := by
    intro h
    have hZ1 : ρR z = 1 := by
      refine LinearMap.ext fun w => ?_
      have : w ∈ Module.End.eigenspace Z 1 := by rw [h]; exact Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff, one_smul] at this
      exact this
    exact hz1 (by simpa using (QuotientGroup.eq_one_iff z).mpr ((hK z).mpr hZ1))
  have hbot1 : Module.End.eigenspace Z 1 = ⊥ := (hdich 1).resolve_right hnot1
  have hnotbot : Module.End.eigenspace Z (-1) ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    have h1 : w + Z w ∈ Module.End.eigenspace Z 1 := by
      rw [Module.End.mem_eigenspace_iff, map_add, one_smul]
      have : Z (Z w) = w := by
        have := congrArg (fun f : Module.End k W => f w) hZZ
        simpa using this
      rw [this, add_comm]
    have h2 : w - Z w ∈ Module.End.eigenspace Z (-1) := by
      rw [Module.End.mem_eigenspace_iff, map_sub, neg_one_smul, neg_sub]
      have : Z (Z w) = w := by
        have := congrArg (fun f : Module.End k W => f w) hZZ
        simpa using this
      rw [this]
    rw [hbot1, Submodule.mem_bot] at h1
    rw [hbot, Submodule.mem_bot] at h2
    have h3 : (2 : k) • w = 0 := by
      calc (2 : k) • w = (w + Z w) + (w - Z w) := by rw [two_smul]; abel
        _ = 0 := by rw [h1, h2, add_zero]
    exact (smul_eq_zero.mp h3).resolve_left hk
  have htop : Module.End.eigenspace Z (-1) = ⊤ := (hdich (-1)).resolve_left hnotbot
  refine LinearMap.ext fun w => ?_
  have : w ∈ Module.End.eigenspace Z (-1) := by rw [htop]; exact Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff, neg_one_smul] at this
  simpa using this

end Rep

end Quotient36

theorem irreducibleRelativeMinimalTwoActionQuotient
    {R A : Type*} [Group R] [Group A] [Finite R] [Finite A] [MulDistribMulAction A R]
    {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W] [Nontrivial W]
    (hR : IsPGroup 2 R) (hA : ¬ 2 ∣ Nat.card A) (hk : (2 : k) ≠ 0)
    (ρR : Representation k R W) (ρA : Representation k A W)
    (hcompat : ∀ (a : A) (r : R), ρA a * ρR r = ρR (a • r) * ρA a)
    (hirr : ∀ U : Submodule k W, (∀ r : R, ∀ w ∈ U, ρR r w ∈ U) →
      (∀ a : A, ∀ w ∈ U, ρA a w ∈ U) → U = ⊥ ∨ U = ⊤)
    (K : Subgroup R) [K.Normal] (hK : ∀ r, r ∈ K ↔ ρR r = 1)
    (hinv : CFSG.IsInvariant A R K)
    (hKtop : K ≠ ⊤) (hRA : actionCommutator A (⊤ : Subgroup R) = ⊤)
    (hmin : ∀ U : Subgroup R, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      actionCommutator A U = U → U ≤ K) :
    K ≤ frattini R ∧ NontrivIrredFrattini A R ∧
    letI : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
    (NontrivIrredFrattini A (R ⧸ K) ∧
      (∀ T : Subgroup (R ⧸ K), T ≠ ⊤ → (∀ a : A, ∀ s ∈ T, a • s ∈ T) →
        ∀ a : A, ∀ s ∈ T, a • s = s) ∧
      (IsElementaryAbelian 2 (R ⧸ K) ∨ IsExtraspecialPGroup 2 (R ⧸ K)) ∧
      (∀ a : A, ∀ s ∈ frattini (R ⧸ K), a • s = s) ∧
      (∀ a : A, (∀ r : R, a • r = r) ↔ ∀ s : R ⧸ K, a • s = s) ∧
      (∀ a : A, (∀ s : R ⧸ K, a • s = s) ↔
        letI := frattiniQuotientAction A (R ⧸ K); ∀ v : (R ⧸ K) ⧸ frattini (R ⧸ K), a • v = v)) ∧
    (∀ a : A, (letI := frattiniQuotientAction A R; ∀ v : R ⧸ frattini R, a • v = v) →
      ∀ r : R, a • r = r) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKlt : K < ⊤ := lt_top_iff_ne_top.mpr hKtop
  have hKinv : ∀ a : A, ∀ x ∈ K, a • x ∈ K := fun a x hx => (hinv.invariant a x).mp hx
  have : Nontrivial R := by
    by_contra hsub
    rw [not_nontrivial_iff_subsingleton] at hsub
    exact hKtop (Subsingleton.elim K ⊤)
  obtain ⟨hnt, hirrR, -, hKΦ⟩ := relative_minimal_action_frattini_irreducibility
    Nat.prime_two hR hA K hKlt hKinv hRA hmin
  have hodd : ∀ a : A, ¬ 2 ∣ orderOf a := fun a h2 => hA (h2.trans (orderOf_dvd_natCard a))
  let _ : MulDistribMulAction A (R ⧸ K) := quotientMulDistribMulAction K hinv
  have hsmul : ∀ (a : A) (x : R), a • (x : R ⧸ K) = ((a • x : R) : R ⧸ K) := fun _ _ => rfl
  have hSq : IsPGroup 2 (R ⧸ K) := hR.to_quotient K
  have hcent := quotient_centralized hR hA K hinv hmin
  have hnt' := quotient_nontrivial_action K hinv hKtop hRA
  obtain ⟨-, hFfix, ⟨-, -, hnt2, hirr2⟩, habel, hnab⟩ :=
    minimal_coprime_action_elementary_or_special (l := 2) hSq hA hnt' hcent
  have hshape : IsElementaryAbelian 2 (R ⧸ K) ∨ IsExtraspecialPGroup 2 (R ⧸ K) := by
    by_cases hab : IsMulCommutative (R ⧸ K)
    · exact Or.inl (habel hab).2
    · right
      obtain ⟨hcf, hfc, hcne, hcel, hzfix⟩ := hnab hab
      have hcc : commutator (R ⧸ K) = Subgroup.center (R ⧸ K) := hcf.trans hfc
      refine ⟨hSq, hcc, hfc, ?_⟩
      have h2 : ∀ z ∈ Subgroup.center (R ⧸ K), z ^ 2 = 1 := by
        intro z hz
        have := hcel
        exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := commutator (R ⧸ K)) z
          (hcc ▸ hz)
      have hneg : ∀ z' : R, (z' : R ⧸ K) ∈ Subgroup.center (R ⧸ K) → (z' : R ⧸ K) ≠ 1 →
          ρR z' = -1 := by
        intro z' hz hz1
        exact rep_central_eq_neg_one hk ρR ρA hcompat hirr K hK hinv z' hz
          (fun a => hzfix a _ hz) (h2 _ hz) hz1
      have hcenter_ne : ∃ z ∈ Subgroup.center (R ⧸ K), z ≠ 1 := by
        have : Subgroup.center (R ⧸ K) ≠ ⊥ := hcc ▸ hcne
        obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp this
        exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩
      have huniq : ∀ z₁ ∈ Subgroup.center (R ⧸ K), z₁ ≠ 1 →
          ∀ z₂ ∈ Subgroup.center (R ⧸ K), z₂ ≠ 1 → z₁ = z₂ := by
        intro z₁ h₁ n₁ z₂ h₂ n₂
        obtain ⟨x₁, rfl⟩ := QuotientGroup.mk_surjective z₁
        obtain ⟨x₂, rfl⟩ := QuotientGroup.mk_surjective z₂
        have e1 := hneg x₁ h₁ n₁
        have e2 := hneg x₂ h₂ n₂
        have hprod : ρR (x₁ * x₂) = 1 := by
          rw [map_mul, e1, e2]
          simp
        have hmem : x₁ * x₂ ∈ K := (hK _).mpr hprod
        have h3 : (x₁ : R ⧸ K) * (x₂ : R ⧸ K) = 1 := by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq_one_iff _).mpr hmem
        have h4 : (x₁ : R ⧸ K) * (x₁ : R ⧸ K) = 1 := by rw [← pow_two]; exact h2 _ h₁
        exact (mul_left_cancel (h3.trans h4.symm)).symm
      obtain ⟨z, hz, hz1⟩ := hcenter_ne
      rw [Nat.card_eq_two_iff]
      refine ⟨1, ⟨z, hz⟩, ?_, ?_⟩
      · intro h
        exact hz1 (congrArg Subtype.val h).symm
      · ext w
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        by_cases hw1 : (w : R ⧸ K) = 1
        · exact Or.inl (Subtype.ext hw1)
        · exact Or.inr (Subtype.ext (huniq _ w.2 hw1 z hz hz1))
  refine ⟨hKΦ, ⟨hnt, hirrR⟩, ⟨⟨hnt2, hirr2⟩, hcent, hshape, hFfix, ?_, ?_⟩, ?_⟩
  · intro a
    constructor
    · intro h s
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
      rw [hsmul, h]
    · intro h
      refine smul_eq_of_smul_mk_eq hR a (hodd a) (fun x => ?_)
      have h1 := h (x : R ⧸ K)
      rw [hsmul, QuotientGroup.eq] at h1
      exact QuotientGroup.eq.mpr (hKΦ h1)
  · intro a
    constructor
    · intro h v
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective v
      exact congrArg (fun y : R ⧸ K => (y : (R ⧸ K) ⧸ frattini (R ⧸ K))) (h s)
    · intro h
      exact smul_eq_of_smul_mk_eq hSq a (hodd a) (fun x => h (x : (R ⧸ K) ⧸ frattini (R ⧸ K)))
  · intro a h
    exact smul_eq_of_smul_mk_eq hR a (hodd a) (fun x => h (x : R ⧸ frattini R))

end CFSG.RankThree.PartOne
