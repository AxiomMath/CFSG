module

public import CFSG.RankThree.GF2n.Stroth80.Sec7AddFilt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Quad
public import CFSG.RankThree.GF2n.Stroth80.Sec79OmegaFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec78CardUt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
  CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

theorem eichler_pair_linearIndependent {ι : Type} [Fintype ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} {u w : ι → K} (hu0 : u ≠ 0) (hu : Q u = 0)
    (hne : eichler Q u w ≠ 1) : LinearIndependent K ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    have hs : s • u = 0 := by rwa [zero_smul, add_zero] at hst
    exact ⟨(smul_eq_zero.mp hs).resolve_right hu0, rfl⟩
  · exfalso
    apply hne
    have h5 : t • w = -(s • u) := eq_neg_iff_add_eq_zero.mpr (by rwa [add_comm])
    have hwc : w = (-(t⁻¹ * s)) • u := by
      calc w = t⁻¹ • (t • w) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (-(s • u)) := by rw [h5]
        _ = (-(t⁻¹ * s)) • u := by rw [smul_neg, smul_smul, neg_smul]
    have h0 := eichler_add_smul_self (Q := Q) hu 0 (-(t⁻¹ * s))
    rw [zero_add, eichler_zero_right] at h0
    rw [hwc]
    exact h0

theorem eichler_fix_iff_polar_eq_zero {ι : Type} [Fintype ι] {K : Type} [Field K]
    {Q : QuadraticForm K (ι → K)} {u w : ι → K} (hu : Q u = 0) (hw : polar Q u w = 0)
    (hli : LinearIndependent K ![u, w]) (x : ι → K) :
    eichler Q u w x = x ↔ polar Q x u = 0 ∧ polar Q x w = 0 := by
  rw [eichler_apply hu hw]
  have e : x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u - x
      = (-(polar Q x w + Q w * polar Q x u)) • u + polar Q x u • w := by
    module
  constructor
  · intro h
    have h' : (-(polar Q x w + Q w * polar Q x u)) • u + polar Q x u • w = 0 := by
      rw [← e, h, sub_self]
    obtain ⟨h1, h2⟩ := LinearIndependent.pair_iff.mp hli _ _ h'
    refine ⟨h2, ?_⟩
    have h3 := neg_eq_zero.mp h1
    rwa [h2, mul_zero, add_zero] at h3
  · rintro ⟨h1, h2⟩
    have h' : (-(polar Q x w + Q w * polar Q x u)) • u + polar Q x u • w = 0 := by
      rw [h1, h2]
      simp
    have h'' : x + polar Q x u • w - (polar Q x w + Q w * polar Q x u) • u - x = 0 := by
      rw [e]
      exact h'
    exact sub_eq_zero.mp h''

theorem card_eichler_fixed {ι : Type} [Fintype ι] {K : Type} [Field K] [Finite K]
    {Q : QuadraticForm K (ι → K)} (hQ : (polarBilin Q).Nondegenerate) {u w : ι → K}
    (hu : Q u = 0) (hw : polar Q u w = 0) (hli : LinearIndependent K ![u, w]) :
    Nat.card {x : ι → K // eichler Q u w x = x} = Nat.card K ^ (Fintype.card ι - 2) := by
  have hu_mem : u ∈ Submodule.span K (Set.range ![u, w]) := Submodule.subset_span ⟨0, rfl⟩
  have hw_mem : w ∈ Submodule.span K (Set.range ![u, w]) := Submodule.subset_span ⟨1, rfl⟩
  have horth : ∀ x : ι → K,
      x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K (Set.range ![u, w])) ↔
        polar Q u x = 0 ∧ polar Q w x = 0 := by
    intro x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h
      exact ⟨by simpa [polarBilin_apply_apply] using h u hu_mem,
        by simpa [polarBilin_apply_apply] using h w hw_mem⟩
    · rintro ⟨h1, h2⟩ n hn
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hn
      rw [Fin.sum_univ_two] at hc
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hc
      rw [← hc]
      simp [polarBilin_apply_apply, polar_add_left, polar_smul_left, h1, h2]
  have hmem : ∀ x : ι → K, eichler Q u w x = x ↔
      x ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) (Submodule.span K (Set.range ![u, w])) := by
    intro x
    rw [eichler_fix_iff_polar_eq_zero hu hw hli x, horth x, polar_comm Q x u, polar_comm Q x w]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hmem),
    Module.natCard_eq_pow_finrank (K := K)
      (V := ↥(LinearMap.BilinForm.orthogonal (polarBilin Q)
        (Submodule.span K (Set.range ![u, w])))),
    LinearMap.BilinForm.finrank_orthogonal hQ, Module.finrank_fintype_fun_eq_card,
    finrank_span_eq_card hli, Fintype.card_fin]

theorem card_fixed_rootGroup_minusFour {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {u : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K} (hu : quadMinus 2 K b c u = 0) (hu0 : u ≠ 0)
    {A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K}
    (hA : A ∈ rootGroupGL (quadMinus 2 K b c) u) (hA1 : A ≠ 1) :
    Nat.card {x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K //
      (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x
        = x} = Nat.card K ^ 2 := by
  have hQ : (polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hA' : toLinEquiv (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K A ∈
      rootGroup (quadMinus 2 K b c) u := hA
  obtain ⟨w, hw, hAw⟩ := mem_rootGroup.mp hA'
  have hne : eichler (quadMinus 2 K b c) u w ≠ 1 := by
    intro h
    apply hA1
    apply (toLinEquiv (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K).injective
    rw [map_one, ← hAw]
    exact h
  have hli := eichler_pair_linearIndependent hu0 hu hne
  have hfix : ∀ x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
      (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x
        = x ↔ eichler (quadMinus 2 K b c) u w x = x := by
    intro x
    rw [← toLinEquiv_apply, hAw]
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix),
    card_eichler_fixed hQ hu hw hli]
  simp


variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_Q_conj_of_mem_M (hc : Ctx M Q Z B) {β : G} (hβM : β ∈ M) {x : G} (hx : x ∈ Q) :
    β * x * β⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hβM) x).mp hx

theorem comm_left_mem_Q_of_mem_M (hc : Ctx M Q Z B) {β : G} (hβM : β ∈ M) {x : G}
    (hx : x ∈ Q) : ⁅β, x⁆ ∈ Q := by
  rw [commutatorElement_def]
  exact Q.mul_mem (mem_Q_conj_of_mem_M hc hβM hx) (Q.inv_mem hx)

theorem comm_left_mem_Z_of_mem_M (hc : Ctx M Q Z B) {β : G} (hβM : β ∈ M) {z : G}
    (hz : z ∈ Z) : ⁅β, z⁆ ∈ Z := by
  have h1 : β * z * β⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz
  rw [commutatorElement_def]
  exact Z.mul_mem h1 (Z.inv_mem hz)

omit [Finite G] in
theorem comm_mem_Z_iff_fixes_secVec {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {V : Subgroup G} [(Z.subgroupOf V).Normal] {β : G}
    (hβV : β ∈ Subgroup.normalizer (V : Set G))
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (A : Matrix ι ι K)
    (hA : ∀ v w : ↥V, (w : G) = β * (v : G) * β⁻¹ → secVec ψ w = A *ᵥ secVec ψ v)
    (w : ↥V) : ⁅β, (w : G)⁆ ∈ Z ↔ A *ᵥ secVec ψ w = secVec ψ w := by
  obtain ⟨w', hw'⟩ : ∃ w' : ↥V, (w' : G) = β * (w : G) * β⁻¹ :=
    ⟨⟨β * (w : G) * β⁻¹, (Subgroup.mem_normalizer_iff.mp hβV (w : G)).mp w.2⟩, rfl⟩
  have h1 : secVec ψ w' = A *ᵥ secVec ψ w := hA w w' hw'
  have h2 : secVec ψ w' = secVec ψ w ↔ ⁅β, (w : G)⁆ ∈ Z := by
    rw [secVec_eq_iff, hw', commutatorElement_def]
  rw [← h2, h1]

theorem card_eq_card_Z_mul_fixed {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {V W : Subgroup G} [(Z.subgroupOf V).Normal] {β : G}
    (hβV : β ∈ Subgroup.normalizer (V : Set G))
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (A : Matrix ι ι K)
    (hA : ∀ v w : ↥V, (w : G) = β * (v : G) * β⁻¹ → secVec ψ w = A *ᵥ secVec ψ v)
    (hZW : Z ≤ W) (hWV : W ≤ V) (hW : ∀ w : ↥V, (w : G) ∈ W ↔ ⁅β, (w : G)⁆ ∈ Z) :
    Nat.card ↥W = Nat.card Z * Nat.card {x : ι → K // A *ᵥ x = x} := by
  have hS : ∀ x : ι → K,
      (∃ w : ↥V, (w : G) ∈ W ∧ secVec ψ w = x) ↔ x ∈ {x : ι → K | A *ᵥ x = x} := by
    intro x
    constructor
    · rintro ⟨w, hwW, rfl⟩
      exact (comm_mem_Z_iff_fixes_secVec hβV ψ A hA w).mp ((hW w).mp hwW)
    · intro hx
      obtain ⟨w, rfl⟩ := exists_secVec_eq ψ x
      exact ⟨w, (hW w).mpr ((comm_mem_Z_iff_fixes_secVec hβV ψ A hA w).mpr hx), rfl⟩
  exact card_eq_of_secVec ψ hZW hWV {x : ι → K | A *ᵥ x = x} hS

theorem card_Vt_inf_Q1_of_notMem_CN (hPts : Sec5NatPointsOmegaStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {r : G} (hr : Sec7A hc t r)
    (hom : OmegaMinusNat hc t 2) {β : G} (hβ : β ∈ LB M Q B) (hβN : β ∉ hc.CN t) :
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ Q1 hc β) = Nat.card Z ^ 3 := by
  have hm2 : (2 : ℕ) ≤ 2 := le_refl 2
  have hβM : β ∈ M := hc.LB_le_M hβ
  have hβR : β ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.toSec5.mem hβ
  obtain ⟨K, hKf, hKfin, hchar, b, c, hirr, φ, u, _, hKZ, hu, _, hu0, _, _, hrange,
    hker, hsec, hLu, _⟩ := natPoints_of_omegaMinusNat hPts hc hs hr hm2 hom
  obtain ⟨β', hβ'⟩ : ∃ β' : ↥(Rt M (LB M Q B) t), (β' : G) = β := ⟨⟨β, hβR⟩, rfl⟩
  have hβ'L : β' ∈ (LB M Q B).subgroupOf (Rt M (LB M Q B) t) :=
    Subgroup.mem_subgroupOf.mpr (by rw [hβ']; exact hβ)
  have hA_mem : φ β' ∈ LomGLMinus hm2 hirr u := by
    rw [← hLu]
    exact Subgroup.mem_map_of_mem φ hβ'L
  rw [← ElemMatrixIso.LomGL_minus hm2 hirr u] at hA_mem
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hA_root : φ β' ∈ rootGroupGL (quadMinus 2 K b c) u := by
    obtain ⟨hX, h1, h2, h3⟩ :=
      ((ElemMatrixIso.minus hm2 hirr).mem_LomGL_iff_flag hQnd hu hu0).mp hA_mem
    exact (mem_rootGroupGL_iff hQnd hu hu0).mpr
      ⟨fun v => (ElemMatrixIso.minus hm2 hirr).quad_mulVec hX v, h1, h2, h3⟩
  have hA1 : φ β' ≠ 1 := by
    intro h1
    have hmem : β' ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker, Subgroup.mem_subgroupOf, hβ'] at hmem
    exact hβN hmem
  have hFixA := card_fixed_rootGroup_minusFour hirr hu hu0 hA_root hA1
  obtain ⟨hRn, hn, ψ, hψ⟩ := hsec
  haveI := hn
  have hA : ∀ v w : ↥(Vt M (LB M Q B) B Z t), (w : G) = β * (v : G) * β⁻¹ →
      secVec ψ w = (((φ β' : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
          secVec ψ v := by
    intro v w hvw
    exact hψ β' v w (by rw [hβ']; exact hvw)
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZW : Z ≤ Vt M (LB M Q B) B Z t ⊓ Q1 hc β := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨sec39_Z_le_Vt hz, (hc.mem_Q1_iff hβM).mpr ⟨hc.Z_le_Q hz, ?_⟩⟩
    rw [commutatorElement_def]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz)
      (Z.inv_mem hz)
  have hW : ∀ w : ↥(Vt M (LB M Q B) B Z t),
      (w : G) ∈ Vt M (LB M Q B) B Z t ⊓ Q1 hc β ↔ ⁅β, (w : G)⁆ ∈ Z := by
    intro w
    constructor
    · intro hw
      exact ((hc.mem_Q1_iff hβM).mp (Subgroup.mem_inf.mp hw).2).2
    · intro hw
      exact Subgroup.mem_inf.mpr ⟨w.2, (hc.mem_Q1_iff hβM).mpr ⟨hVQ w.2, hw⟩⟩
  have hcard := card_eq_card_Z_mul_fixed (hRn hβR) ψ _ hA hZW inf_le_left hW
  have hSc : Nat.card {x : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K //
      (((φ β' : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x
          = x} = Nat.card K ^ 2 := hFixA
  rw [hcard, hSc, hKZ]
  ring


open CFSG.ClassicalGroups.F2Fixed in
omit [Finite G] in
theorem exists_subgroup_fixedSub_secSub {R P I : Subgroup G} {Y : Type} [AddCommGroup Y]
    [DistribMulAction ↥R Y] {κ : ↥P →* Multiplicative Y} (hκ : IsSecMod R P I Y κ)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) (hIP : I ≤ P) (b : ↥R) :
    ∃ C : Subgroup G, I ≤ C ∧ C ≤ P ∧ (∀ x ∈ P, x ∈ C ↔ ⁅(b : G), x⁆ ∈ I) ∧
      secSub κ C = fixedSub Y ({b} : Set ↥R) := by
  obtain ⟨C, hIC, hCP, hCF⟩ := exists_secSub_eq hIP hκ (fixedSub Y ({b} : Set ↥R))
  refine ⟨C, hIC, hCP, fun x hx => ?_, hCF⟩
  have hxC : x ∈ C ↔ Multiplicative.toAdd (κ ⟨x, hx⟩) ∈ secSub κ C :=
    (toAdd_mem_secSub_iff hκ hIC ⟨x, hx⟩).symm
  have hmem : (b : G) * x * (b : G)⁻¹ ∈ P := hP _ b.2 x hx
  have hact := hκ.act b ⟨x, hx⟩ ⟨(b : G) * x * (b : G)⁻¹, hmem⟩ rfl
  have heq := hκ.eq_iff ⟨(b : G) * x * (b : G)⁻¹, hmem⟩ ⟨x, hx⟩
  rw [hxC, hCF, mem_fixedSub]
  simp only [Set.mem_singleton_iff, forall_eq]
  rw [commutatorElement_def]
  constructor
  · intro h
    have h' : κ ⟨(b : G) * x * (b : G)⁻¹, hmem⟩ = κ ⟨x, hx⟩ := by
      rw [hact, h, ofAdd_toAdd]
    exact heq.mp h'
  · intro h
    have h' : κ ⟨(b : G) * x * (b : G)⁻¹, hmem⟩ = κ ⟨x, hx⟩ := heq.mpr h
    exact Multiplicative.ofAdd.injective ((hact.symm.trans h').trans (ofAdd_toAdd _).symm)

open CFSG.ClassicalGroups.F2Fixed in
theorem exists_card_sq_comm_Wt (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hom : OmegaMinusNat hc t 2) {β : G} (hβ : β ∈ LB M Q B)
    (hβN : β ∉ hc.CN t) :
    ∃ C : Subgroup G, Vt M (LB M Q B) B Z t ≤ C ∧ C ≤ Wt Q (Vt M (LB M Q B) B Z t) ∧
      (∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), x ∈ C ↔ ⁅β, x⁆ ∈ Vt M (LB M Q B) B Z t) ∧
      Nat.card ↥C * Nat.card ↥C =
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    le_sup_right.trans hr.gen.ge
  have hβR : β ∈ Rt M (LB M Q B) t := hLR hβ
  have hWn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx y hy =>
    conj_mem_Wt (hQM (hRM hx)) (hc.Rt_normalizes_Vt ht hx) hy
  have hVn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hx) y).mp hy
  have hWN : ∀ k ∈ hc.CN t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅k, w⁆ ∈ Vt M (LB M Q B) B Z t := sec7_N_comm_W_le_V h52a hA hc hs
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) :=
    hd.1.trans hd.2.1
  obtain ⟨K, hKf, hKfin, hchar, b, c, hirr, φ, u, u', -, hu, hu', hu0, hu0', huu', hrange,
    hkerφ, -, hLu, hLu'⟩ := natPoints_of_omegaMinusNat hPts hc hs hr (le_refl (2 : ℕ)) hom
  obtain ⟨E, hE⟩ : ∃ E : ElemMatrixIso (quadMinus 2 K b c)
      (StatedOmega (StatedQuadMinus 2 K b c)),
      E = ElemMatrixIso.minus (le_refl (2 : ℕ)) hirr := ⟨_, rfl⟩
  have hL₁ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL u' := by
    rw [hLA, hE, ElemMatrixIso.LomGL_minus (le_refl (2 : ℕ)) hirr]
    exact hLu'
  have hL₂ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u := by
    rw [hE, ElemMatrixIso.LomGL_minus (le_refl (2 : ℕ)) hirr]
    exact hLu
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  have hroot : ∀ (A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
      (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K), quadMinus 2 K b c v = 0 → v ≠ 0 →
        A ∈ E.LomGL v → A ∈ rootGroupGL (quadMinus 2 K b c) v := by
    intro A v hv hv0 hAv
    obtain ⟨hAX, hrest⟩ := (E.mem_LomGL_iff_flag hQnd hv hv0).mp hAv
    exact (mem_rootGroupGL_iff hQnd hv hv0).mpr ⟨fun x => E.quad_mulVec hAX x, hrest⟩
  have hβy : (⟨β, hβR⟩ : ↥(Rt M (LB M Q B) t)) ∈
      (LB M Q B).subgroupOf (Rt M (LB M Q B) t) :=
    Subgroup.mem_subgroupOf.mpr hβ
  have hmem : φ ⟨β, hβR⟩ ∈ E.LomGL u := by
    rw [← hL₂]
    exact Subgroup.mem_map_of_mem φ hβy
  have hne1 : φ ⟨β, hβR⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨β, hβR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hkerφ, Subgroup.mem_subgroupOf] at h2
    exact hβN h2
  have huu'' : polar (quadMinus 2 K b c) u' u ≠ 0 := by
    rw [polar_comm]
    exact huu'
  have hv := sec7_polar_apply_ne_zero_of_mem_rootGroupGL hirr hu' hu hu0' hu0 huu''
    (hroot _ u hu hu0 hmem) hne1
  have h4 : 4 ≤ Fintype.card (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := by
    norm_num [Fintype.card_sum]
  have hsec : SecHyp (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t) := SecHyp.of_isOppDecomp hd hWn hVn
  obtain ⟨Y, iY, iD, κ, hκ, hkerY⟩ := exists_sectionModule_ker hkerφ hsec hWN
  haveI : Finite Y := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hWn hκ hd hLR hL2R
  obtain ⟨hk1, -, hk3⟩ := stroth_2_1_ii_omega_fixed_of_hom E φ hrange hQnd hκ.two hkerY
    hu' hu huu'' hL₁ hL₂ hdec.symm h4 hβy ⟨u', hv⟩
  obtain ⟨C, hVC, hCW, hCiff, hCF⟩ := exists_subgroup_fixedSub_secSub hκ hWn hVW ⟨β, hβR⟩
  have hcardC := natCard_secSub_mul hVW hκ hVC hCW
  have hcardW := natCard_eq_of_isSecMod hVW hκ
  rw [hCF, hk1] at hcardC
  rw [hk3] at hcardW
  refine ⟨C, hVC, hCW, hCiff, ?_⟩
  rw [← hcardC, hcardW]
  ring


theorem Z_le_Wt_of_le_Q (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) :
    Z ≤ Wt Q V := fun z hz => ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hc.hyp.toHyp79.V_central hz (hVQ hv)).symm⟩

theorem conj_mem_Wt_of_mem_Q (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) {x w : G}
    (hx : x ∈ Q) (hw : w ∈ Wt Q V) : x * w * x⁻¹ ∈ Wt Q V := by
  have hxw : ⁅x, w⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx hw.1
  have e : x * w * x⁻¹ = ⁅x, w⁆ * w := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Wt Q V).mul_mem (Z_le_Wt_of_le_Q hc hVQ hxw) hw

theorem comm_comm_congr_mod_Z (hc : Ctx M Q Z B) {t β x : G} (htM : t ∈ M) (hβM : β ∈ M)
    (hβt : ⁅β⁻¹, t⁆ ∈ Q) (hx : x ∈ Q) :
    ⁅⁅β, x⁆, t⁆ * ⁅β, ⁅x, t⁆⁆⁻¹ ∈ Z := by
  have hβx : β * x * β⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hβM) x).mp hx
  have hu : ⁅x, t⁆ ∈ Q := hc.comm_mem_Q htM hx
  have hB : β * ⁅x, t⁆ * β⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hβM) _).mp hu
  have hBM : β * ⁅x, t⁆ * β⁻¹ ∈ M := hc.hyp.Q_normal.1 hB
  have e1 := hc.comm_conj_mem_Z htM hβM hβt hx
  have e2 := hc.comm_mul_mem_Z htM hβx (Q.inv_mem hx)
  have e3 := hc.comm_mul_mem_Z htM (Q.inv_mem hx) hx
  have h1 : ⁅x⁻¹ * x, t⁆ = 1 := by simp [commutatorElement_def]
  rw [h1, one_mul, Subgroup.inv_mem_iff] at e3
  have e4 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hBM) _).mp e3
  have hid : ⁅⁅β, x⁆, t⁆ * ⁅β, ⁅x, t⁆⁆⁻¹ =
      ⁅β * x * β⁻¹ * x⁻¹, t⁆ * (⁅β * x * β⁻¹, t⁆ * ⁅x⁻¹, t⁆)⁻¹ *
        (⁅β * x * β⁻¹, t⁆ * (β * ⁅x, t⁆ * β⁻¹)⁻¹) *
          (β * ⁅x, t⁆ * β⁻¹ * (⁅x⁻¹, t⁆ * ⁅x, t⁆) * (β * ⁅x, t⁆ * β⁻¹)⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact Z.mul_mem (Z.mul_mem e2 e1) e4

theorem mem_iff_of_mul_inv_mem {H : Subgroup G} {a b : G} (h : a * b⁻¹ ∈ H) : a ∈ H ↔ b ∈ H := by
  constructor
  · intro ha
    have e : b = (a * b⁻¹)⁻¹ * a := by group
    rw [e]
    exact H.mul_mem (H.inv_mem h) ha
  · intro hb
    have e : a = a * b⁻¹ * b := by group
    rw [e]
    exact H.mul_mem h hb

theorem exists_subgroup_comm_mem_Wt (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q) (β : G) :
    ∃ C : Subgroup G, ∀ x : G, x ∈ C ↔ x ∈ Q ∧ ⁅β, x⁆ ∈ Wt Q V := by
  refine ⟨{ carrier := {x | x ∈ Q ∧ ⁅β, x⁆ ∈ Wt Q V}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun x => Iff.rfl⟩
  · rintro a b ⟨ha, hab⟩ ⟨hb, hbb⟩
    refine ⟨Q.mul_mem ha hb, ?_⟩
    have e : ⁅β, a * b⁆ = ⁅β, a⁆ * (a * ⁅β, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Wt Q V).mul_mem hab (conj_mem_Wt_of_mem_Q hc hVQ ha hbb)
  · refine ⟨Q.one_mem, ?_⟩
    have e : ⁅β, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
    rw [e]
    exact (Wt Q V).one_mem
  · rintro a ⟨ha, hab⟩
    refine ⟨Q.inv_mem ha, ?_⟩
    have e : ⁅β, a⁻¹⁆ = a⁻¹ * (⁅β, a⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact conj_mem_Wt_of_mem_Q hc hVQ (Q.inv_mem ha) ((Wt Q V).inv_mem hab)

theorem exists_chiTransport_Wt (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {β : G} (hβR : β ∈ Rt M (LB M Q B) t) :
    ∃ C : Subgroup G, Wt Q (Vt M (LB M Q B) B Z t) ≤ C ∧ C ≤ Q ∧
      (∀ x ∈ Q, x ∈ C ↔ ⁅β, x⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
      Nat.card ↥C * Nat.card ↥Z =
        Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) *
          Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ Q1 hc β) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hβM : β ∈ M := hc.Rt_le_M t hβR
  have hβt : ⁅β⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hβR)
  obtain ⟨hV, hW⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  have hchi0 := hc.isChiIso_Q1_Ut ht
  rw [← hW, ← hV] at hchi0
  obtain ⟨c1, c2, c3, c4, c5⟩ := hchi0
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨C, hC⟩ := exists_subgroup_comm_mem_Wt hc hVQ β
  have hCQ : C ≤ Q := fun x hx => ((hC x).mp hx).1
  have hWC : Wt Q (Vt M (LB M Q B) B Z t) ≤ C := by
    intro w hw
    refine (hC w).mpr ⟨hw.1, ?_⟩
    have hβW := conj_mem_Wt (hc.hyp.Q_normal.2 hβM) (hc.Rt_normalizes_Vt ht hβR) hw
    rw [commutatorElement_def]
    exact (Wt Q (Vt M (LB M Q B) B Z t)).mul_mem hβW
      ((Wt Q (Vt M (LB M Q B) B Z t)).inv_mem hw)
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZU : Z ≤ Vt M (LB M Q B) B Z t ⊓ Q1 hc β := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨hZV hz, (hc.mem_Q1_iff hβM).mpr ⟨hc.Z_le_Q hz, ?_⟩⟩
    rw [commutatorElement_def]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz)
      (Z.inv_mem hz)
  have hVQ' : Vt M (LB M Q B) B Z t ⊓ Q1 hc β ≤ Q :=
    fun x hx => hVQ (Subgroup.mem_inf.mp hx).1
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t ⊓ Q1 hc β)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ' hv)))
  have hchiC : IsChiIso C (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Vt M (LB M Q B) B Z t ⊓ Q1 hc β) Z t := by
    refine ⟨fun x hx => ?_, fun u hu => ?_, fun x hx y hy => c3 x (hCQ hx) y (hCQ hy),
      fun x hx => c4 x (hCQ hx), fun r hr x hx => c5 r hr x (hCQ hx)⟩
    · have hxQ : x ∈ Q := hCQ hx
      have hyt : ⁅⁅β, x⁆, t⁆ ∈ Z :=
        (c4 _ (comm_left_mem_Q_of_mem_M hc hβM hxQ)).mpr ((hC x).mp hx).2
      have hb : ⁅β, ⁅x, t⁆⁆ ∈ Z :=
        (mem_iff_of_mul_inv_mem (comm_comm_congr_mod_Z hc htM hβM hβt hxQ)).mp hyt
      exact Subgroup.mem_inf.mpr ⟨c1 x hxQ, (hc.mem_Q1_iff hβM).mpr ⟨hc.comm_mem_Q htM hxQ, hb⟩⟩
    · obtain ⟨huV, huQ1⟩ := Subgroup.mem_inf.mp hu
      obtain ⟨-, hub⟩ := (hc.mem_Q1_iff hβM).mp huQ1
      obtain ⟨x, hxQ, hxu⟩ := c2 u huV
      obtain ⟨z, hz, hzeq⟩ : ∃ z ∈ Z, ⁅x, t⁆ = z * u := ⟨⁅x, t⁆ * u⁻¹, hxu, by simp⟩
      have hb : ⁅β, ⁅x, t⁆⁆ ∈ Z := by
        rw [hzeq]
        have e : ⁅β, z * u⁆ = β * z * β⁻¹ * ⁅β, u⁆ * z⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact Z.mul_mem (Z.mul_mem
          ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hβM) z).mp hz) hub)
          (Z.inv_mem hz)
      have hyt : ⁅⁅β, x⁆, t⁆ ∈ Z :=
        (mem_iff_of_mul_inv_mem (comm_comm_congr_mod_Z hc htM hβM hβt hxQ)).mpr hb
      exact ⟨x, (hC x).mpr ⟨hxQ, (c4 _ (comm_left_mem_Q_of_mem_M hc hβM hxQ)).mp hyt⟩, hxu⟩
  exact ⟨C, hWC, hCQ, fun x hx => ⟨fun h => ((hC x).mp h).2, fun h => (hC x).mpr ⟨hx, h⟩⟩,
    card_mul_card_of_isChiIso hchiC hWC hZU⟩


theorem card_Q1_mul_le_filtration (hc : Ctx M Q Z B) {β : G} (hβM : β ∈ M) {V W C₂ C₃ : Subgroup G}
    (hZV : Z ≤ V) (hVW : V ≤ W) (hWQ : W ≤ Q)
    (hβV : ∀ x ∈ V, β * x * β⁻¹ ∈ V) (hβW : ∀ x ∈ W, β * x * β⁻¹ ∈ W)
    (hC₂V : V ≤ C₂) (hC₂W : C₂ ≤ W) (hC₂ : ∀ x ∈ W, x ∈ C₂ ↔ ⁅β, x⁆ ∈ V)
    (hC₃W : W ≤ C₃) (hC₃Q : C₃ ≤ Q) (hC₃ : ∀ x ∈ Q, x ∈ C₃ ↔ ⁅β, x⁆ ∈ W) :
    Nat.card ↥(Q1 hc β) * Nat.card ↥V * Nat.card ↥W ≤
      Nat.card ↥(V ⊓ Q1 hc β) * Nat.card ↥C₂ * Nat.card ↥C₃ := by
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hVQ : V ≤ Q := hVW.trans hWQ
  have hZW : Z ≤ W := hZV.trans hVW
  have hZC₂ : Z ≤ C₂ := hZV.trans hC₂V
  have hZC₃ : Z ≤ C₃ := hZW.trans hC₃W
  have hC₂Q : C₂ ≤ Q := hC₂W.trans hWQ
  have hβZ : ∀ z ∈ Z, ⁅β, z⁆ ∈ Z := fun z hz => comm_left_mem_Z_of_mem_M hc hβM hz
  have hZQ1 : Z ≤ Q1 hc β := fun z hz => (hc.mem_Q1_iff hβM).mpr ⟨hZQ hz, hβZ z hz⟩
  have hQ1Q : Q1 hc β ≤ Q := fun x hx => ((hc.mem_Q1_iff hβM).mp hx).1
  have hVQ1Q : V ⊓ Q1 hc β ≤ Q := inf_le_left.trans hVQ
  have hZVQ1 : Z ≤ V ⊓ Q1 hc β := le_inf hZV hZQ1
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule (sec7ctr_secHyp hc (le_refl M))
  haveI : Finite Md := hκ.finite
  obtain ⟨ε, hε⟩ : ∃ ε : Md →+ Md, ∀ a, ε a = (⟨β, hβM⟩ : ↥M) • a - a :=
    ⟨AddMonoidHom.mk' (fun a => (⟨β, hβM⟩ : ↥M) • a - a) (fun a b => by rw [smul_add]; abel),
      fun a => rfl⟩
  have hcom : ∀ y : G, ⁅β, y⁆ = β * y * β⁻¹ * y⁻¹ := fun y => by
    rw [commutatorElement_def]
  have hsurjQ : ∀ a : Md, ∃ x : ↥Q, Multiplicative.toAdd (κ x) = a := fun a => by
    obtain ⟨x, hx⟩ := hκ.surj (Multiplicative.ofAdd a)
    exact ⟨x, by rw [hx, toAdd_ofAdd]⟩
  have hκε : ∀ x : ↥Q,
      Multiplicative.toAdd (κ ⟨⁅β, (x : G)⁆, comm_left_mem_Q_of_mem_M hc hβM x.2⟩) =
        ε (Multiplicative.toAdd (κ x)) := by
    intro x
    have h1 := hκ.act (⟨β, hβM⟩ : ↥M) x
      ⟨β * (x : G) * β⁻¹, mem_Q_conj_of_mem_M hc hβM x.2⟩ rfl
    have e : (⟨⁅β, (x : G)⁆, comm_left_mem_Q_of_mem_M hc hβM x.2⟩ : ↥Q) =
        ⟨β * (x : G) * β⁻¹, mem_Q_conj_of_mem_M hc hβM x.2⟩ * x⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, map_mul, map_inv, h1, toAdd_mul, toAdd_inv, toAdd_ofAdd, hε, sub_eq_add_neg]
  have hεS : ∀ s ∈ secSub κ V, ε s ∈ secSub κ V := by
    intro s hs
    obtain ⟨x, hxV, hxs⟩ := mem_secSub.mp hs
    have hxs' : Multiplicative.toAdd (κ x) = s := by rw [hxs, toAdd_ofAdd]
    rw [← hxs', ← hκε x]
    refine (toAdd_mem_secSub_iff hκ hZV _).mpr ?_
    show ⁅β, (x : G)⁆ ∈ V
    rw [hcom]
    exact V.mul_mem (hβV _ hxV) (V.inv_mem hxV)
  have hεA : ∀ a ∈ secSub κ W, ε a ∈ secSub κ W := by
    intro a ha
    obtain ⟨x, hxW, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa, toAdd_ofAdd]
    rw [← hxa', ← hκε x]
    refine (toAdd_mem_secSub_iff hκ hZW _).mpr ?_
    show ⁅β, (x : G)⁆ ∈ W
    rw [hcom]
    exact W.mul_mem (hβW _ hxW) (W.inv_mem hxW)
  have hker : ε.ker = secSub κ (Q1 hc β) := by
    ext a
    obtain ⟨x, rfl⟩ := hsurjQ a
    rw [toAdd_mem_secSub_iff hκ hZQ1 x, hc.mem_Q1_iff hβM, AddMonoidHom.mem_ker, ← hκε x,
      toAdd_eq_zero, hκ.ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have hinf : secSub κ V ⊓ ε.ker = secSub κ (V ⊓ Q1 hc β) := by
    rw [hker]
    exact (secSub_inf hκ hZV).symm
  have hAC₂ : secSub κ W ⊓ (secSub κ V).comap ε = secSub κ C₂ := by
    ext a
    obtain ⟨x, rfl⟩ := hsurjQ a
    have h1 : Multiplicative.toAdd (κ x) ∈ secSub κ W ↔ (x : G) ∈ W :=
      toAdd_mem_secSub_iff hκ hZW x
    have h2 : Multiplicative.toAdd (κ x) ∈ (secSub κ V).comap ε ↔ ⁅β, (x : G)⁆ ∈ V := by
      rw [AddSubgroup.mem_comap, ← hκε x]
      exact toAdd_mem_secSub_iff hκ hZV _
    have h3 : Multiplicative.toAdd (κ x) ∈ secSub κ C₂ ↔ (x : G) ∈ C₂ :=
      toAdd_mem_secSub_iff hκ hZC₂ x
    rw [AddSubgroup.mem_inf, h1, h2, h3]
    constructor
    · rintro ⟨hxW, hb⟩
      exact (hC₂ (x : G) hxW).mpr hb
    · intro hx
      exact ⟨hC₂W hx, (hC₂ (x : G) (hC₂W hx)).mp hx⟩
  have hAC₃ : (secSub κ W).comap ε = secSub κ C₃ := by
    ext a
    obtain ⟨x, rfl⟩ := hsurjQ a
    have h1 : Multiplicative.toAdd (κ x) ∈ (secSub κ W).comap ε ↔ ⁅β, (x : G)⁆ ∈ W := by
      rw [AddSubgroup.mem_comap, ← hκε x]
      exact toAdd_mem_secSub_iff hκ hZW _
    have h2 : Multiplicative.toAdd (κ x) ∈ secSub κ C₃ ↔ (x : G) ∈ C₃ :=
      toAdd_mem_secSub_iff hκ hZC₃ x
    rw [h1, h2]
    exact (hC₃ (x : G) x.2).symm
  have key := card_ker_mul_le_filtration ε (secSub κ V) (secSub κ W) (secSub_mono hVW) hεS hεA
  rw [hinf, hAC₂, hAC₃, hker] at key
  have cQ1 := natCard_secSub_mul hZQ hκ hZQ1 hQ1Q
  have cV := natCard_secSub_mul hZQ hκ hZV hVQ
  have cW := natCard_secSub_mul hZQ hκ hZW hWQ
  have cVQ := natCard_secSub_mul hZQ hκ hZVQ1 hVQ1Q
  have cC₂ := natCard_secSub_mul hZQ hκ hZC₂ hC₂Q
  have cC₃ := natCard_secSub_mul hZQ hκ hZC₃ hC₃Q
  calc Nat.card ↥(Q1 hc β) * Nat.card ↥V * Nat.card ↥W
      = (Nat.card ↥(secSub κ (Q1 hc β)) * Nat.card ↥Z) *
          (Nat.card ↥(secSub κ V) * Nat.card ↥Z) * (Nat.card ↥(secSub κ W) * Nat.card ↥Z) := by
        rw [cQ1, cV, cW]
    _ = (Nat.card ↥(secSub κ (Q1 hc β)) * Nat.card ↥(secSub κ V) *
          Nat.card ↥(secSub κ W)) * Nat.card ↥Z ^ 3 := by ring
    _ ≤ (Nat.card ↥(secSub κ (V ⊓ Q1 hc β)) * Nat.card ↥(secSub κ C₂) *
          Nat.card ↥(secSub κ C₃)) * Nat.card ↥Z ^ 3 := Nat.mul_le_mul_right _ key
    _ = (Nat.card ↥(secSub κ (V ⊓ Q1 hc β)) * Nat.card ↥Z) *
          (Nat.card ↥(secSub κ C₂) * Nat.card ↥Z) * (Nat.card ↥(secSub κ C₃) * Nat.card ↥Z) := by
        ring
    _ = Nat.card ↥(V ⊓ Q1 hc β) * Nat.card ↥C₂ * Nat.card ↥C₃ := by
        rw [cVQ, cC₂, cC₃]


theorem card_arith_beta (q n a c w c₂ c₃ : ℕ) (hq : 1 < q) (hn : 3 ≤ n)
    (hA1 : q ^ (2 * n + 1) * q = c * a) (hA2 : q ^ (2 * n + 1) * q = w * (q * q ^ 4))
    (hc₂ : c₂ * c₂ = (q * q ^ 4) * w) (hc₃ : c₃ * q = w * q ^ 3)
    (hfilt : c * (q * q ^ 4) * w ≤ q ^ 3 * c₂ * c₃) : q ^ (n + 1) ≤ a := by
  have hqpos : 0 < q := by omega
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h
      have : 0 < q ^ (2 * n + 1) * q := by positivity
      omega
    · exact h
  have hc₃' : c₃ = w * q ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hqpos
    rw [hc₃]
    ring
  have hc₂' : c₂ = q ^ (n + 1) := by
    have h1 : c₂ * c₂ = q ^ (n + 1) * q ^ (n + 1) := by
      rw [hc₂, ← pow_add]
      have : q ^ (2 * n + 1) * q = (q * q ^ 4) * w := by rw [hA2]; ring
      calc q * q ^ 4 * w = q ^ (2 * n + 1) * q := this.symm
        _ = q ^ (n + 1 + (n + 1)) := by ring
    exact Nat.mul_self_inj.mp h1
  have hc : c ≤ q ^ (n + 1) := by
    have h1 : c * (q * q ^ 4) * w ≤ q ^ (n + 1 + 5) * w := by
      calc c * (q * q ^ 4) * w ≤ q ^ 3 * c₂ * c₃ := hfilt
        _ = q ^ (n + 1 + 5) * w := by rw [hc₂', hc₃']; ring
    have h2 : c * (q * q ^ 4) ≤ q ^ (n + 1 + 5) := Nat.le_of_mul_le_mul_right h1 hw
    have h3 : c * q ^ 5 ≤ q ^ (n + 1) * q ^ 5 := by
      calc c * q ^ 5 = c * (q * q ^ 4) := by ring
        _ ≤ q ^ (n + 1 + 5) := h2
        _ = q ^ (n + 1) * q ^ 5 := by ring
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)
  have hqn : 0 < q ^ (n + 1) := by positivity
  have h4 : q ^ (n + 1) * q ^ (n + 1) ≤ q ^ (n + 1) * a := by
    calc q ^ (n + 1) * q ^ (n + 1) = q ^ (2 * n + 1) * q := by ring
      _ = c * a := hA1
      _ ≤ q ^ (n + 1) * a := Nat.mul_le_mul_right _ hc
  exact Nat.le_of_mul_le_mul_left h4 hqn


theorem sec73CardBeta_of_inputs (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement) :
    Sec73CardBetaStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom β hβL hβN
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hβR : β ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hβL
  have hβM : β ∈ M := hc.LB_le_M hβL
  obtain ⟨hVU, hWQ1⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hQ1Q : ∀ s : G, Q1 hc s ≤ Q := fun s x hx => hx.1
  have hβV : ∀ x ∈ Vt M (LB M Q B) B Z t, β * x * β⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hβR) x).mp hx
  have hβW : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), β * x * β⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun x hx => conj_mem_Wt (hc.hyp.Q_normal.2 hβM) (hc.Rt_normalizes_Vt ht hβR) hx
  have hF1' := card_Vt_inf_Q1_of_notMem_CN hPts hc hs hr hom hβL hβN
  obtain ⟨C₂, hC₂V, hC₂W, hC₂, hC₂c⟩ := exists_card_sq_comm_Wt hA hPts h52a h52b hc hs hom hβL hβN
  obtain ⟨C₃, hC₃W, hC₃Q, hC₃, hC₃c⟩ := exists_chiTransport_Wt h310chi hc hs hβR
  have hfilt := card_Q1_mul_le_filtration hc hβM hZV hVW hWQ hβV hβW hC₂V hC₂W hC₂ hC₃W hC₃Q hC₃
  have hUt : ∀ {s : G}, s ∈ LB M Q B →
      Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc s) * Nat.card ↥(Ut Q Z s) := by
    intro s hsL
    have hsM : s ∈ M := hc.LB_le_M hsL
    haveI : (Z.subgroupOf (Ut Q Z s)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q hsM hv)))
    exact card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut hsL) (hQ1Q s) (le_sup_right : Z ≤ Ut Q Z s)
  have hA1 := hUt hβL
  have hA2 := hUt ht
  rw [← hWQ1, ← hVU] at hA2
  have hV := card_Vt_orthogonal hc (le_refl 2) (Or.inr hom)
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  have hq : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  norm_num at hV
  rw [hQc] at hA1 hA2
  rw [hV] at hA2 hC₂c hfilt
  rw [hF1'] at hC₃c hfilt
  exact card_arith_beta (Nat.card Z) n _ _ _ _ _ hq hs.toSec5.n_gt hA1.symm.symm
    (by simpa using hA2) hC₂c (by simpa using hC₃c) (by simpa using hfilt)

end CFSG.RankThree.GF2n.Stroth80
