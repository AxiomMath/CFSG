module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKFlagCore
public import CFSG.LieType.Universal.Spin.Generation.Eichler
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.StandardType.RCKFlag

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open
  CFSG.LieType.Universal CFSG.ClassicalGroups.Orthogonal
open CliffordAlgebra QuadraticMap

private lemma rckFlagOm_polar_self {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (x : V) :
    QuadraticMap.polar Q x x = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

private lemma rckFlagOm_neg_eq_self {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (x : V) : -x = x := by
  have hK : (-1 : K) = 1 := CharTwo.neg_eq 1
  calc -x = (-1 : K) • x := (neg_one_smul K x).symm
    _ = 1 • x := by simpa using congrArg (fun a : K => a • x) hK
    _ = x := one_smul _ _

private lemma rckFlagOm_self_adjoint {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (N : V →ₗ[K] V)
    (halt : ∀ m : V, QuadraticMap.polar Q m (N m) = 0) (x y : V) :
    QuadraticMap.polar Q x (N y) = QuadraticMap.polar Q (N x) y := by
  have h := halt (x + y)
  simp only [map_add, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
    halt x, halt y, zero_add, add_zero] at h
  have h' : QuadraticMap.polar Q x (N y) = QuadraticMap.polar Q y (N x) :=
    CharTwo.add_eq_zero.mp (by simpa [add_comm] using h)
  rw [h', QuadraticMap.polar_comm]

private lemma rckFlagOm_N_sq {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (N : V →ₗ[K] V) (W H : Submodule K V) (hWH : W ≤ H) (hW : N.range = W) (hH : N.ker = H) :
    ∀ y : V, N (N y) = 0 := by
  intro y
  have hy : N y ∈ N.ker := by
    rw [hH]
    exact hWH (by rw [← hW]; exact LinearMap.mem_range_self N y)
  simpa using hy

private lemma rckFlagOm_ker_eq_orthogonal {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (N : V →ₗ[K] V) (W : Submodule K V)
    (hsa : ∀ x y : V, QuadraticMap.polar Q x (N y) = QuadraticMap.polar Q (N x) y)
    (hQ : ∀ x : V, (∀ y : V, QuadraticMap.polar Q x y = 0) → x = 0) (hW : N.range = W) :
    ∀ m : V, N m = 0 ↔ ∀ w ∈ W, QuadraticMap.polar Q m w = 0 := by
  intro m
  constructor
  · intro hm w hw
    have hw' : w ∈ N.range := by rw [hW]; exact hw
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hw'
    rw [← hy, hsa m y, hm, QuadraticMap.polar_zero_left]
  · intro hm
    apply hQ
    intro y
    rw [← hsa m y]
    exact hm (N y) (by rw [← hW]; exact LinearMap.mem_range_self N y)

private lemma rckFlagOm_exists_unit_lift {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (N : V →ₗ[K] V)
    (W H : Submodule K V) (hWH : W ≤ H) (hNN : ∀ y : V, N (N y) = 0) (hW : N.range = W)
    (hH : N.ker = H) (hWsing : ∀ w ∈ W, Q w = 0)
    (hker : ∀ m : V, N m = 0 ↔ ∀ w ∈ W, QuadraticMap.polar Q m w = 0)
    (halt : ∀ m : V, QuadraticMap.polar Q m (N m) = 0) {m u : V} (hNm : N m = u) (hu : u ≠ 0) :
    ∃ m' : V, N m' = u ∧ IsUnit (Q m') ∧ QuadraticMap.polar Q u m' = 0 ∧
      QuadraticMap.polar Q m' m' = 0 ∧ ∃ w ∈ W, m' = m + w := by
  have hsa : ∀ x y : V, QuadraticMap.polar Q x (N y) = QuadraticMap.polar Q (N x) y :=
    rckFlagOm_self_adjoint Q N halt
  have hmker : N m ≠ 0 := by rwa [hNm]
  have hnot : ∃ w ∈ W, QuadraticMap.polar Q m w ≠ 0 := by
    by_contra h
    have hzero : ∀ w ∈ W, QuadraticMap.polar Q m w = 0 := by
      intro w hw
      by_contra hwne
      exact h ⟨w, hw, hwne⟩
    exact hmker ((hker m).mpr hzero)
  by_cases hQm : Q m = 0
  · obtain ⟨w, hwW, hmw⟩ := hnot
    let w' : V := (QuadraticMap.polar Q m w)⁻¹ • w
    have hw'W : w' ∈ W := W.smul_mem _ hwW
    have hNw : N w = 0 := by
      have : w ∈ N.ker := by rw [hH]; exact hWH hwW
      simpa using this
    have hNw' : N w' = 0 := by
      dsimp only [w']
      rw [map_smul, hNw, smul_zero]
    have hQw : Q w = 0 := hWsing w hwW
    have hQw' : Q w' = 0 := by
      dsimp only [w']
      rw [map_smul_eq_sq, hQw, mul_zero]
    have hBmw : QuadraticMap.polar Q m w' = 1 := by
      dsimp only [w']
      rw [polar_smul_right, smul_eq_mul]
      exact inv_mul_cancel₀ hmw
    let m' : V := m + w'
    have hNm' : N m' = u := by
      dsimp only [m']
      rw [map_add, hNw', add_zero, hNm]
    have hQm' : Q m' = 1 := by
      dsimp only [m']
      rw [QuadraticMap.map_add Q, hQm, hQw', hBmw, add_zero, zero_add]
    have hum : QuadraticMap.polar Q u m = 0 := by
      rw [← hNm, ← hsa m m]
      exact halt m
    have hu_w' : QuadraticMap.polar Q u w' = 0 := by
      rw [← hNm, ← hsa m w', hNw', QuadraticMap.polar_zero_right]
    refine ⟨m', hNm', ?_, ?_, ?_, w', hw'W, rfl⟩
    · rw [hQm']; exact isUnit_one
    · dsimp only [m']
      rw [QuadraticMap.polar_add_right, hum, hu_w', add_zero]
    · exact rckFlagOm_polar_self Q m'
  · refine ⟨m, hNm, isUnit_iff_ne_zero.mpr hQm, ?_, rckFlagOm_polar_self Q m, 0, W.zero_mem,
      (add_zero m).symm⟩
    rw [← hNm, ← hsa m m]
    exact halt m

private lemma rckFlagOm_eichler_apply_formula {K : Type} [Field K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) {u m x : V} (hu : Q u = 0)
    (hum : QuadraticMap.polar Q u m = 0) (c : K) :
    eichler Q u (c • m) x =
      x + (c * QuadraticMap.polar Q x u) • m +
        (c * QuadraticMap.polar Q x m + c ^ 2 * Q m * QuadraticMap.polar Q x u) • u := by
  have hcw : QuadraticMap.polar Q u (c • m) = 0 := by
    rw [QuadraticMap.polar_smul_right, hum, smul_zero]
  rw [eichler_apply hu hcw, polar_smul_right_eq, map_smul_eq_sq,
    sub_eq_add_neg, rckFlagOm_neg_eq_self (K := K)]
  module

private lemma rckFlagOm_root_exists {K : Type} [Field K] [CharP K 2] {σ : Type} [Fintype σ]
    [DecidableEq σ] (Q : QuadraticForm K (σ → K)) {u m : σ → K} (hu : Q u = 0)
    (hum : QuadraticMap.polar Q u m = 0) (hQm : IsUnit (Q m)) (c : K) :
    ∃ g : spinGroup Q,
      Spin.spinAction Q g = eichler Q u (c • m) := by
  let hmem : ∀ c : K, 1 + c • (ι Q m * ι Q u) ∈ spinGroup Q := fun c =>
    Spin.one_add_smul_ι_mul_ι_mem_spinGroup Q hu hum hum (rckFlagOm_polar_self Q m) hQm c
  refine ⟨Spin.rootHom Q hu hum hmem (Multiplicative.ofAdd c), ?_⟩
  exact Spin.spinAction_rootHom_eq_eichler Q hu hum hmem c

theorem rckFlagIrredW_quadratic {K : Type} [Field K] [Finite K] [CharP K 2] {σ : Type} [Fintype σ]
    [DecidableEq σ] (Q : QuadraticForm K (σ → K))
    (hQ : ∀ x : σ → K, (∀ y : σ → K, QuadraticMap.polar Q x y = 0) → x = 0)
    (hinj : Function.Injective (Spin.spinMatrix Q)) :
    FlagIrredW (Spin.spinMatrix Q) (some (QuadraticMap.polar Q)) := by
  intro R' W H hWH hv hB r hr hr1 P hPW hInv
  let N : (σ → K) →ₗ[K] (σ → K) :=
    Matrix.toLin' (((Spin.spinMatrix Q) r : Matrix σ σ K) - 1)
  have hNrange : N.range = W := (hv r hr hr1).1
  have hNker : N.ker = H := (hv r hr hr1).2
  have hNr : Matrix.toLin' (((Spin.spinMatrix Q) r : Matrix σ σ K)) = N + 1 := by
    have h : Matrix.toLin' (((Spin.spinMatrix Q) r : Matrix σ σ K)) - 1 = N := by
      dsimp only [N]
      rw [map_sub, Matrix.toLin'_one]
      rfl
    exact sub_eq_iff_eq_add.mp h
  by_cases hdim : Module.finrank K W = 1
  · by_cases hPbot : P = ⊥
    · exact Or.inl hPbot
    · right
      obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hPbot
      haveI : FiniteDimensional K W := FiniteDimensional.finiteDimensional_submodule W
      haveI : FiniteDimensional K P := FiniteDimensional.finiteDimensional_submodule P
      have hPle : Module.finrank K P ≤ Module.finrank K W := Submodule.finrank_mono hPW
      haveI : Nontrivial P := (Submodule.nontrivial_iff_ne_bot (p := P)).mpr hPbot
      have hPpos : 0 < Module.finrank K P := Module.finrank_pos_iff.mpr inferInstance
      have hPfin : Module.finrank K P = 1 := by omega
      exact Submodule.eq_of_le_of_finrank_eq hPW (by rw [hPfin, hdim])
  · have hb := hB (QuadraticMap.polar Q) (by simp)
    have hBalt : ∀ m : σ → K, QuadraticMap.polar Q m (N m) = 0 := by
      rcases hb with h | h
      · intro m
        have hm := h r hr m
        dsimp only [N]
        rw [Matrix.toLin'_apply]
        exact hm
      · exact absurd h hdim
    have hNN : ∀ y : σ → K, N (N y) = 0 :=
      rckFlagOm_N_sq N W H hWH hNrange hNker
    have hsa : ∀ x y : σ → K,
        QuadraticMap.polar Q x (N y) = QuadraticMap.polar Q (N x) y :=
      rckFlagOm_self_adjoint Q N hBalt
    have hQN : ∀ x : σ → K, Q (N x) = 0 := by
      intro x
      have hpres : Q (((Spin.spinMatrix Q) r : Matrix σ σ K).mulVec x) = Q x :=
        Spin.spinMatrix_mem Q r x
      have hx : ((Spin.spinMatrix Q) r : Matrix σ σ K).mulVec x = x + N x := by
        have h := congrArg (fun L : (σ → K) →ₗ[K] (σ → K) => L x) hNr
        rw [Matrix.toLin'_apply] at h
        rw [h, LinearMap.add_apply, Module.End.one_apply]
        abel
      rw [hx, QuadraticMap.map_add Q, hBalt x, add_zero] at hpres
      have h2 : Q x + Q (N x) = Q x + 0 := by simpa using hpres
      simpa using add_left_cancel h2
    have hWsing : ∀ w ∈ W, Q w = 0 := by
      intro w hw
      have hwr : w ∈ N.range := by rwa [← hNrange] at hw
      obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hwr
      exact hQN z
    have hWtot : ∀ w ∈ W, ∀ w' ∈ W, QuadraticMap.polar Q w w' = 0 := by
      intro w hw w' hw'
      have hw'r : w' ∈ N.range := by rwa [← hNrange] at hw'
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hw'r
      rw [← hy, hsa w y]
      have hwr : w ∈ N.range := by rwa [← hNrange] at hw
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hwr
      rw [← hz, hNN z, QuadraticMap.polar_zero_left]
    have hker : ∀ m : σ → K, N m = 0 ↔ ∀ w ∈ W, QuadraticMap.polar Q m w = 0 :=
      rckFlagOm_ker_eq_orthogonal Q N W hsa hQ hNrange
    by_cases hPbot : P = ⊥
    · exact Or.inl hPbot
    · right
      obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff P).mp hPbot
      have hxW : x ∈ W := hPW hxP
      have hxpol : ∃ m : σ → K, QuadraticMap.polar Q x m ≠ 0 := by
        by_contra! h
        exact hx0 (hQ x h)
      obtain ⟨m, hBxm⟩ := hxpol
      have hNm0 : N m ≠ 0 := by
        intro hNm
        obtain ⟨z, hz⟩ : x ∈ N.range := by rw [hNrange]; exact hxW
        have : QuadraticMap.polar Q x m = 0 := by
          rw [← hz, ← hsa z m, hNm, QuadraticMap.polar_zero_right]
        exact hBxm this
      have root_mem : ∀ m0 : σ → K, QuadraticMap.polar Q x m0 ≠ 0 → N m0 ∈ P := by
        intro m0 hBxm0
        let u0 : σ → K := N m0
        have hu0W : u0 ∈ W := by
          rw [← hNrange]
          exact LinearMap.mem_range_self N m0
        have hu0ne : u0 ≠ 0 := by
          intro hu0
          obtain ⟨z, hz⟩ : x ∈ N.range := by rw [hNrange]; exact hxW
          have : QuadraticMap.polar Q x m0 = 0 := by
            rw [← hz, ← hsa z m0, show N m0 = 0 from hu0, QuadraticMap.polar_zero_right]
          exact hBxm0 this
        have hu0Q : Q u0 = 0 := hQN m0
        have hu0m0 : QuadraticMap.polar Q u0 m0 = 0 := by
          dsimp only [u0]
          rw [← hsa m0 m0]
          exact hBalt m0
        obtain ⟨m', hNm', hQm', hum', hm'm', w, hwW, hm'eq⟩ :=
          rckFlagOm_exists_unit_lift Q N W H hWH hNN hNrange hNker hWsing hker hBalt
            (m := m0) (u := u0) rfl hu0ne
        have hBxm' : QuadraticMap.polar Q x m' ≠ 0 := by
          intro hzero
          apply hBxm0
          rw [hm'eq, QuadraticMap.polar_add_right] at hzero
          have hxw : QuadraticMap.polar Q x w = 0 := hWtot x hxW w hwW
          rw [hxw, add_zero] at hzero
          exact hzero
        let c : K := (QuadraticMap.polar Q x m')⁻¹
        have hcx : c * QuadraticMap.polar Q x m' = 1 := by
          dsimp only [c]
          exact inv_mul_cancel₀ hBxm'
        obtain ⟨g, hgact⟩ := rckFlagOm_root_exists Q hu0Q hum' hQm' c
        let S : (σ → K) ≃ₗ[K] (σ → K) := Spin.spinAction Q g
        have hS : S = eichler Q u0 (c • m') := by
          dsimp only [S]
          exact hgact
        have hgx : S x = x + u0 := by
          rw [hS, rckFlagOm_eichler_apply_formula Q hu0Q hum' c]
          have hxu : QuadraticMap.polar Q x u0 = 0 := hWtot x hxW u0 hu0W
          simp [hxu, hcx]
        have hcommN : ∀ y : σ → K,
            N (((S : (σ → K) →ₗ[K] (σ → K))) y) =
              ((S : (σ → K) →ₗ[K] (σ → K))) (N y) := by
          intro y
          change N (S y) = S (N y)
          have hNu : N u0 = 0 := by
            dsimp only [u0]
            exact hNN m0
          have hNyu : QuadraticMap.polar Q (N y) u0 = 0 := by
            rw [← hsa y u0, hNu, QuadraticMap.polar_zero_right]
          have hNym : QuadraticMap.polar Q (N y) m' = QuadraticMap.polar Q y u0 := by
            rw [← hsa y m', hNm']
          rw [hS, rckFlagOm_eichler_apply_formula Q hu0Q hum' c,
            rckFlagOm_eichler_apply_formula Q hu0Q hum' c]
          rw [map_add, map_add, map_smul, map_smul, hNm', hNu, hNyu, hNym]
          module
        have hmat : ((Spin.spinMatrix Q) g : Matrix σ σ K) * ((Spin.spinMatrix Q) r : Matrix σ σ K)
            = ((Spin.spinMatrix Q) r : Matrix σ σ K) * ((Spin.spinMatrix Q) g : Matrix σ σ K) := by
          apply Matrix.toLin'.injective
          rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
          have hMg : Matrix.toLin' (((Spin.spinMatrix Q) g) : Matrix σ σ K) =
              (S : (σ → K) →ₗ[K] (σ → K)) := by
            apply LinearMap.ext
            intro x
            rw [Matrix.toLin'_apply, Spin.spinMatrix_mulVec]
            rfl
          rw [hMg, hNr]
          apply LinearMap.ext
          intro y
          rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.add_apply, Module.End.one_apply,
            LinearMap.add_apply, Module.End.one_apply, map_add, hcommN y]
        have hgr : g * r = r * g := by
          apply hinj
          rw [map_mul, map_mul]
          apply Matrix.GeneralLinearGroup.ext
          intro i k
          rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
          exact congrFun (congrFun hmat i) k
        have hgcent : g ∈ Subgroup.centralizer ({r} : Set (spinGroup Q)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact hgr
        have hgxP : S x ∈ P := by
          have h := hInv g hgcent x hxP
          rwa [Spin.spinMatrix_mulVec] at h
        have hdiff : S x - x ∈ P := Submodule.sub_mem P hgxP hxP
        have hEq : (x + u0) - x = u0 := by abel
        rwa [hgx, hEq] at hdiff
      have huP : N m ∈ P := root_mem m hBxm
      have hWleP : W ≤ P := by
        intro y hy
        have hyr : y ∈ N.range := by rwa [← hNrange] at hy
        obtain ⟨my, hmy⟩ := LinearMap.mem_range.mp hyr
        by_cases hBmy : QuadraticMap.polar Q x my = 0
        · have hBsum : QuadraticMap.polar Q x (my + m) ≠ 0 := by
            rw [QuadraticMap.polar_add_right, hBmy, zero_add]
            exact hBxm
          have hmem : N (my + m) ∈ P := root_mem (my + m) hBsum
          have hyu : y + N m ∈ P := by
            rwa [map_add, hmy] at hmem
          have hyP : y ∈ P := by
            have h : (y + N m) - N m ∈ P := Submodule.sub_mem P hyu huP
            simpa using h
          exact hyP
        · have hmem : N my ∈ P := root_mem my hBmy
          rwa [hmy] at hmem
      exact le_antisymm hPW hWleP

end CFSG.StandardType.RCKFlag
