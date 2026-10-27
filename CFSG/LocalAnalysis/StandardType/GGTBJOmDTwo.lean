module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.LocalAnalysis.StandardType.GGTBJOmPlaneIsometries
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthFixed
public import CFSG.LocalAnalysis.StandardType.GGTBJOmQTwo

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

omit [Finite K] [FiniteDimensional K V] in
private theorem tbjOmDTwoAux_inf_pieces_eq_bot (Δ : TBJOmData Q p A r) {i k : Fin r}
    (hik : i ≠ k) : Δ.F.U i ⊓ Δ.F.U k = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨hui, huk⟩ := Submodule.mem_inf.mp hu
  have h0 : u = 0 := Δ.F.nondeg i u hui fun v hv =>
    Δ.F.orth i k hik v hv u huk
  simp [h0]

theorem TBJOmData.finrank_fixedSpace (Δ : TBJOmData Q p A r)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (f₀ : Fin r → Multiplicative (ZMod p)) :
    finrank K (fixedSpace (Δ.τ f₀)) = 2 * Nat.card {j : Fin r // toAdd (f₀ j) = 0} := by
  classical
  let M : Submodule K V := ⨆ j : {j : Fin r // toAdd (f₀ j) = 0}, Δ.F.U j
  have hMle : M ≤ fixedSpace (Δ.τ f₀) := by
    refine iSup_le fun j => ?_
    exact TBJOmData.piece_le_fixedSpace Δ f₀ j.2
  have hdimM : finrank K M = 2 * Nat.card {j : Fin r // toAdd (f₀ j) = 0} := by
    have h := CFSG.StandardType.OrthTorusGen.finrank_iSup_frame_pieces Δ.F
      (fun j => TBJOmData.finrank_piece Δ j) (fun j => toAdd (f₀ j) = 0)
    rw [Nat.card_eq_fintype_card]
    exact h
  let φ : fixedSpace (Δ.τ f₀) →ₗ[K] Module.Dual K M :=
    (polarBilin Q).flip.compl₁₂ (fixedSpace (Δ.τ f₀)).subtype M.subtype
  have hφ_inj : Function.Injective φ := by
    intro v v' h
    have hsub : φ (v - v') = 0 := by rw [map_sub, h, sub_self]
    have hMorth : ∀ m ∈ M, polar Q m (v - v').1 = 0 := by
      intro m hm
      have h := congrArg (fun l : Module.Dual K M => l ⟨m, hm⟩) hsub
      simpa [φ, LinearMap.compl₁₂_apply, LinearMap.BilinForm.flip_apply,
        polarBilin_apply_apply] using h
    have hall : ∀ j : Fin r, ∀ u ∈ Δ.F.U j, polar Q u (v - v').1 = 0 := by
      intro j u hu
      by_cases hj : toAdd (f₀ j) = 0
      · exact hMorth u (Submodule.mem_iSup_of_mem ⟨j, hj⟩ hu)
      · exact (Δ.mem_fixedSpace_iff f₀ (v - v').1).mp (v - v').2 j hj u hu
    have hvA : ∀ a ∈ A, a (v - v').1 = (v - v').1 := by
      intro a ha
      rw [← Δ.τ_range] at ha
      obtain ⟨f, rfl⟩ := MonoidHom.mem_range.mp ha
      exact mem_fixedSpace.mp ((Δ.mem_fixedSpace_iff f (v - v').1).mpr
        fun j _ u hu => hall j u hu)
    have hzero : v - v' = 0 := Subtype.ext (by simpa using hnf (v - v').1 hvA)
    exact sub_eq_zero.mp hzero
  have hWle : finrank K (fixedSpace (Δ.τ f₀)) ≤ finrank K M := by
    rw [← LinearMap.finrank_range_of_inj hφ_inj]
    calc finrank K (LinearMap.range φ) ≤ finrank K (Module.Dual K M) :=
          Submodule.finrank_le _
      _ = finrank K M := Subspace.dual_finrank_eq
  have hEq : M = fixedSpace (Δ.τ f₀) := Submodule.eq_of_le_of_finrank_le hMle hWle
  rw [← hEq, hdimM]

theorem TBJOmData.exists_totallySingular_of_two_zero [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (f₀ : Fin r → Multiplicative (ZMod p)) {i k : Fin r}
    (hik : i ≠ k) (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) :
    ∃ S : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S = 2 ∧
      ∀ x ∈ S, (Q.comp (fixedSpace (Δ.τ f₀)).subtype) x = 0 := by
  classical
  obtain ⟨w, hwΩ, -, hwconj⟩ := Δ.swapMove i k hik
  have hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hwΩ
  have hwQ : ∀ v, Q (w v) = Q v :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hwO
  have hwconj' : w * Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * w⁻¹ =
      Δ.τ (Pi.mulSingle k (ofAdd (1 : ZMod p))) := by
    rw [hwconj, permAut_mulSingle, Equiv.swap_apply_left]
  have hmap : ∀ u ∈ Δ.F.U i, w u ∈ Δ.F.U k :=
    Δ.mapsTo_piece_of_conj_tau_mulSingle hQ hwO hwconj'
  have hWi : Δ.F.U i ≤ fixedSpace (Δ.τ f₀) :=
    TBJOmData.piece_le_fixedSpace Δ f₀ hi
  have hWk : Δ.F.U k ≤ fixedSpace (Δ.τ f₀) :=
    TBJOmData.piece_le_fixedSpace Δ f₀ hk
  let ψ : Δ.F.U i →ₗ[K] V :=
    (Δ.F.U i).subtype + w.toLinearMap.comp (Δ.F.U i).subtype
  have hψ : ∀ u : Δ.F.U i, ψ u ∈ fixedSpace (Δ.τ f₀) := fun u =>
    add_mem (hWi u.2) (hWk (hmap u.1 u.2))
  let φ : Δ.F.U i →ₗ[K] fixedSpace (Δ.τ f₀) := ψ.codRestrict _ hψ
  have hφker : ∀ u : Δ.F.U i, φ u = 0 → u = 0 := by
    intro u hu
    have h0 : (u : V) + w u = 0 := by
      have := congrArg (fun x : fixedSpace (Δ.τ f₀) => (x : V)) hu
      simpa [φ, ψ] using this
    have hneg : -(u : V) = u := by
      have h : (-1 : K) • (u : V) = u := by
        rw [CharTwo.neg_eq (1 : K), one_smul]
      simpa using h
    have hwu : w u = u := by rw [eq_neg_of_add_eq_zero_right h0, hneg]
    have hu_k : (u : V) ∈ Δ.F.U k := by
      have h := hmap u u.2
      rwa [hwu] at h
    have hbot : (u : V) ∈ (⊥ : Submodule K V) := by
      rw [← tbjOmDTwoAux_inf_pieces_eq_bot Δ hik]
      exact Submodule.mem_inf.mpr ⟨u.2, hu_k⟩
    exact Subtype.ext (by simpa using (Submodule.mem_bot K).mp hbot)
  have hφinj : Function.Injective φ := by
    intro u u' h
    have hsub : φ (u - u') = 0 := by rw [map_sub, h, sub_self]
    have h0 := hφker (u - u') hsub
    exact sub_eq_zero.mp h0
  have hrange : finrank K (LinearMap.range φ) = 2 := by
    rw [LinearMap.finrank_range_of_inj hφinj, TBJOmData.finrank_piece]
  refine ⟨LinearMap.range φ, hrange, ?_⟩
  intro x hx
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
  change Q ((u : V) + w u) = 0
  rw [QuadraticMap.map_add Q (u : V) (w u), hwQ,
    Δ.F.orth i k hik u.1 u.2 (w u) (hmap u.1 u.2), add_zero]
  exact CharTwo.add_self_eq_zero (Q (u : V))

private theorem tbjOmDTwoAux_supportedBlock_tau [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (f₀ : Fin r → Multiplicative (ZMod p)) {i k : Fin r} (hik : i ≠ k)
    (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) (f : Fin r → Multiplicative (ZMod p))
    (hf : ∀ j, j ≠ i → j ≠ k → f j = 1) :
    Δ.τ f ∈ supportedBlock Q (Δ.τ f₀) (X - 1) := by
  classical
  set y : V ≃ₗ[K] V := Δ.τ f₀ with hy
  set W : Submodule K V := fixedSpace y with hW
  have hx : OddOrderIsometry Q p y := by rw [hy]; exact Δ.oddOrderIsometry hp2 hQ hA f₀
  have hgΩ : Δ.τ f ∈ orthDerived Q := hA (Δ.τ_range.le ⟨f, rfl⟩)
  have hgO : Δ.τ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup hgΩ
  have hcomm : Δ.τ f * y = y * Δ.τ f := by
    rw [hy, ← map_mul, ← map_mul, mul_comm]
  have hWi : Δ.F.U i ≤ W := by
    rw [hW, hy]; exact TBJOmData.piece_le_fixedSpace Δ f₀ hi
  have hWk : Δ.F.U k ≤ W := by
    rw [hW, hy]; exact TBJOmData.piece_le_fixedSpace Δ f₀ hk
  have hgR : ∀ v, (∀ w ∈ W, polar Q w v = 0) → Δ.τ f v = v := by
    intro v hv
    refine mem_fixedSpace.mp ((Δ.mem_fixedSpace_iff f v).mpr ?_)
    intro j hj u hu
    by_cases hji : j = i
    · subst hji
      exact hv u (hWi hu)
    · by_cases hjk : j = k
      · subst hjk
        exact hv u (hWk hu)
      · rw [hf j hji hjk, toAdd_one] at hj
        exact absurd rfl hj
  have hgB : Δ.τ f ∈ supportedBlock Q y (X - 1) :=
    mem_supportedBlock_of_fixes hx hgO hcomm hgR
  simpa [hy] using hgB

theorem tbjOmDTwo_card_eq_two_or_four_le {k : Type} [Field k] [Finite k] [CharP k 2] :
    Nat.card k = 2 ∨ 4 ≤ Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k 2
  rw [Nat.card_eq_fintype_card, hcard]
  rcases n with ⟨n, hn⟩
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | h2
  · left
    rfl
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2

private theorem tbjOmDTwoAux_isPGroup_quotient_fixed [Fact p.Prime] (hK4 : 4 ≤ Nat.card K)
    (Δ : TBJOmData Q p A r) (f₀ : Fin r → Multiplicative (ZMod p))
    (R : QuadraticForm K (fixedSpace (Δ.τ f₀))) (hRnd : (polarBilin R).Nondegenerate)
    (h4 : finrank K (fixedSpace (Δ.τ f₀)) = 4)
    (hsplit : ∃ S : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) :
    IsPGroup 2 (TauCeti.QuadraticMap.orthogonalGroup R ⧸
      commutator (TauCeti.QuadraticMap.orthogonalGroup R)) := by
  classical
  have hcase : (Odd (Nat.card K) ∧ (finrank K (fixedSpace (Δ.τ f₀)) = 3 ∨
        finrank K (fixedSpace (Δ.τ f₀)) = 4 ∨ finrank K (fixedSpace (Δ.τ f₀)) = 5)) ∨
      (Odd (Nat.card K) ∧ finrank K (fixedSpace (Δ.τ f₀)) = 6 ∧
        ¬ ∃ T : Submodule K (fixedSpace (Δ.τ f₀)), finrank K T = 3 ∧ ∀ x ∈ T, R x = 0) ∨
      (finrank K (fixedSpace (Δ.τ f₀)) = 4 ∧
        ∃ S : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) :=
    Or.inr (Or.inr ⟨h4, hsplit⟩)
  have hnexc : ¬ ((finrank K (fixedSpace (Δ.τ f₀)) = 3 ∧ Nat.card K = 3) ∨
      ((finrank K (fixedSpace (Δ.τ f₀)) = 4 ∧
        ∃ S : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S = 2 ∧ ∀ x ∈ S, R x = 0) ∧
        (Nat.card K = 2 ∨ Nat.card K = 3))) := by
    rintro (⟨h3, -⟩ | ⟨⟨-, -⟩, hK23⟩)
    · omega
    · rcases hK23 with h2 | h3 <;> omega
  have hcov :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_low_dimensional_fixed_derived_component_coverage
      R hRnd hcase
  exact (hcov.2.1 hnexc).2.1

private theorem tbjOmDTwoAux_restrict_mem_orthDerived [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate)
    (f₀ : Fin r → Multiplicative (ZMod p))
    (h4 : finrank K (fixedSpace (Δ.τ f₀)) = 4) {i k : Fin r} (hik : i ≠ k)
    (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) (f : Fin r → Multiplicative (ZMod p))
    (hRnd : (polarBilin (Q.comp (fixedSpace (Δ.τ f₀)).subtype)).Nondegenerate)
    (hgB : Δ.τ f ∈ supportedBlock Q (Δ.τ f₀) (X - 1)) :
    restrictFixed Q (Δ.τ f₀) ⟨Δ.τ f, hgB⟩ ∈
      orthDerived (Q.comp (fixedSpace (Δ.τ f₀)).subtype) := by
  classical
  let R : QuadraticForm K (fixedSpace (Δ.τ f₀)) := Q.comp (fixedSpace (Δ.τ f₀)).subtype
  have hsplit : ∃ S : Submodule K (fixedSpace (Δ.τ f₀)), finrank K S = 2 ∧ ∀ x ∈ S, R x = 0 := by
    obtain ⟨S, hSdim, hSQ⟩ := Δ.exists_totallySingular_of_two_zero hQ f₀ hik hi hk
    exact ⟨S, hSdim, hSQ⟩
  let O := TauCeti.QuadraticMap.orthogonalGroup R
  let gR : O := ⟨restrictFixed Q (Δ.τ f₀) ⟨Δ.τ f, hgB⟩, restrictFixed_mem_orthogonalGroup _⟩
  have hfp : f ^ p = 1 := by
    funext j
    apply toAdd.injective
    rw [toAdd_pow_apply, Pi.one_apply, toAdd_one, ZMod.natCast_self, zero_mul]
  have hτpow : (Δ.τ f) ^ p = 1 := by
    rw [← map_pow, hfp, map_one]
  have hgp : (⟨Δ.τ f, hgB⟩ : ↥(supportedBlock Q (Δ.τ f₀) (X - 1))) ^ p = 1 := by
    apply Subtype.ext
    simpa using hτpow
  have hgRpow : gR ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    change ((restrictFixed Q (Δ.τ f₀) ⟨Δ.τ f, hgB⟩ :
      fixedSpace (Δ.τ f₀) ≃ₗ[K] fixedSpace (Δ.τ f₀)) ^ p) = 1
    rw [← map_pow, hgp, map_one]
  have hgRcomm : gR ∈ commutator O := by
    rcases tbjOmDTwo_card_eq_two_or_four_le (k := K) with hK2 | hK4
    · exact tbjQ2_mem_commutator_of_pow_prime hK2 R hRnd h4 hsplit (Fact.out : p.Prime) hp2
        hgRpow
    · have hP := tbjOmDTwoAux_isPGroup_quotient_fixed hK4 Δ f₀ R hRnd h4 hsplit
      have hquot : QuotientGroup.mk' (commutator O) gR = 1 := by
        apply orderOf_eq_one_iff.mp
        obtain ⟨k, hk2⟩ := hP.exists_orderOf_eq_pow (QuotientGroup.mk' (commutator O) gR)
        have hdvd : orderOf (QuotientGroup.mk' (commutator O) gR) ∣ p :=
          orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hgRpow, map_one])
        have hk2dvd : 2 ^ k ∣ p := hk2 ▸ hdvd
        have hk0 : k = 0 := by
          by_contra hk0
          have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.pos_of_ne_zero hk0).ne'
          exact ((Fact.out : p.Prime).odd_of_ne_two hp2).not_two_dvd_nat (h2dvd.trans hk2dvd)
        rw [hk2, hk0, pow_zero]
      exact (QuotientGroup.eq_one_iff gR).mp hquot
  have hgRorth : restrictFixed Q (Δ.τ f₀) ⟨Δ.τ f, hgB⟩ ∈ orthDerived R := by
    rw [orthDerived_eq_map_commutator]
    exact Subgroup.mem_map.mpr ⟨gR, hgRcomm, rfl⟩
  exact hgRorth

theorem TBJOmData.tau_mem_supportedFixedDerived_of_finrank_eq_four [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate)
    (hA : A ≤ orthDerived Q) (f₀ : Fin r → Multiplicative (ZMod p))
    (h4 : finrank K (fixedSpace (Δ.τ f₀)) = 4) {i k : Fin r} (hik : i ≠ k)
    (hi : toAdd (f₀ i) = 0) (hk : toAdd (f₀ k) = 0) (f : Fin r → Multiplicative (ZMod p))
    (hf : ∀ j, j ≠ i → j ≠ k → f j = 1) :
    Δ.τ f ∈ supportedFixedDerived Q (Δ.τ f₀) := by
  have hgB : Δ.τ f ∈ supportedBlock Q (Δ.τ f₀) (X - 1) :=
    tbjOmDTwoAux_supportedBlock_tau hp2 Δ hQ hA f₀ hik hi hk f hf
  have hRnd : (polarBilin (Q.comp (fixedSpace (Δ.τ f₀)).subtype)).Nondegenerate :=
    (Δ.oddOrderIsometry hp2 hQ hA f₀).polarBilin_fixed_nondegenerate
  exact mem_supportedFixedDerived.mpr ⟨hgB,
    tbjOmDTwoAux_restrict_mem_orthDerived hp2 Δ hQ f₀ h4 hik hi hk f hRnd hgB⟩

end OrthTorus

end CFSG.StandardType

end
