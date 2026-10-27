module

public import CFSG.RankThree.PartOne.S11d.OddAlt

public section

namespace CFSG.RankThree.PartOne.OddIso

open Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}
  {A : Module.End K V} {p : ℕ}

theorem exists_sub_mem_orth [FiniteDimensional K V] {M : Submodule K V}
    (hMn : ∀ m ∈ M, (∀ n ∈ M, B n m = 0) → m = 0) (x : V) :
    ∃ m ∈ M, x - m ∈ M.orthogonalBilin B := by
  classical
  let b := Module.finBasis K M
  let Φ : M →ₗ[K] (Fin (finrank K M) → K) :=
    LinearMap.pi fun i => (B (b i : V)).comp M.subtype
  have hΦ : ∀ m : M, ∀ i, Φ m i = B (b i : V) m := fun m i => rfl
  have hexp : ∀ n : V, ∀ hn : n ∈ M, n = ∑ i, (b.repr ⟨n, hn⟩ i) • (b i : V) := by
    intro n hn
    have h1 := b.sum_repr ⟨n, hn⟩
    have h2 := congrArg (fun z : M => (z : V)) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply Subtype.ext
    refine hMn m.1 m.2 fun n hn => ?_
    rw [hexp n hn, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smulₛₗ, LinearMap.smul_apply]
    have h0 : B (b i : V) (m : V) = 0 := by simpa [hΦ] using congrFun hm i
    rw [h0, smul_zero]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_fin_fun])).mp hinj
  obtain ⟨m, hm⟩ := hsurj (fun i => B (b i : V) x)
  refine ⟨m, m.2, ?_⟩
  rw [Submodule.mem_orthogonalBilin]
  intro n hn
  rw [hexp n hn, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smulₛₗ, LinearMap.smul_apply]
  have h0 : B (b i : V) (m : V) = B (b i : V) x := by simpa [hΦ] using congrFun hm i
  rw [map_sub, ← h0]
  simp

theorem isCompl_orthogonalBilin_of_sep [FiniteDimensional K V] {M : Submodule K V}
    (hMn : ∀ m ∈ M, (∀ n ∈ M, B n m = 0) → m = 0) :
    IsCompl M (M.orthogonalBilin B) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro z hzM hzN
    exact hMn z hzM fun n hn => (Submodule.mem_orthogonalBilin.mp hzN) n hn
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    obtain ⟨m, hm, hx⟩ := exists_sub_mem_orth hMn x
    have : x = m + (x - m) := by abel
    rw [this]
    exact Submodule.add_mem_sup hm hx

theorem orth_invariantH (hAB : ∀ v w, B (A v) (A w) = B v w) (hA : A ^ p = 1) (hp : 1 ≤ p)
    {M : Submodule K V} (hM : ∀ m ∈ M, A m ∈ M) {v : V} (hv : v ∈ M.orthogonalBilin B) :
    A v ∈ M.orthogonalBilin B := by
  rw [Submodule.mem_orthogonalBilin] at hv ⊢
  intro m hm
  have hx : A ((A ^ (p - 1)) m) = m := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp, hA, Module.End.one_apply]
  have hx' : (A ^ (p - 1)) m ∈ M := invariant_pow hM _ m hm
  calc B m (A v) = B (A ((A ^ (p - 1)) m)) (A v) := by rw [hx]
    _ = B ((A ^ (p - 1)) m) v := hAB _ _
    _ = 0 := hv _ hx'

section Odd

variable [CharP K 2]

theorem range_sepH (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) :
    ∀ w ∈ LinearMap.range (A - 1), (∀ w' ∈ LinearMap.range (A - 1), B w w' = 0) → w = 0 := by
  intro w hw h
  apply hBn
  intro v
  obtain ⟨v₁, hv₁, w₂, hw₂, rfl⟩ := exists_fix_add_range hp hA v
  have hv₁' : A v₁ = v₁ := sub_eq_zero.mp (LinearMap.mem_ker.mp hv₁)
  obtain ⟨u, rfl⟩ := hw
  rw [map_add, h w₂ hw₂, add_zero]
  exact B_range_fix B hAB hv₁' u

theorem fix_sepH (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) :
    ∀ v ∈ LinearMap.ker (A - 1), (∀ v' ∈ LinearMap.ker (A - 1), B v v' = 0) → v = 0 := by
  intro v hv h
  apply hBn
  intro w
  obtain ⟨v₁, hv₁, w₂, hw₂, rfl⟩ := exists_fix_add_range hp hA w
  have hv' : A v = v := sub_eq_zero.mp (LinearMap.mem_ker.mp hv)
  obtain ⟨u, rfl⟩ := hw₂
  rw [map_add, h v₁ hv₁, zero_add]
  exact B_fix_range B hAB hv' u

theorem form_eq_zero_of_isotropic (hσ : ∃ c : K, σ c ≠ c) (hH : ∀ x y, B y x = σ (B x y))
    {W : Submodule K V} (hiso : ∀ v ∈ W, B v v = 0) : ∀ u ∈ W, ∀ w ∈ W, B u w = 0 := by
  intro u hu w hw
  by_contra hb
  obtain ⟨c₀, hc₀⟩ := hσ
  have h2 : ∀ x : K, x + x = 0 := fun x => by
    rw [← two_smul K x, show (2 : K) = 0 from CharP.cast_eq_zero K 2, zero_smul]
  have key : ∀ c : K, c * B u w + σ (c * B u w) = 0 := by
    intro c
    have h0 := hiso (u + c • w) (W.add_mem hu (W.smul_mem c hw))
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hiso u hu, hiso w hw] at h0
    have h3 : B w u = σ (B u w) := hH u w
    rw [h3] at h0
    rw [map_mul]
    linear_combination h0
  have h5 := key (c₀ * (B u w)⁻¹)
  rw [mul_assoc, inv_mul_cancel₀ hb, mul_one] at h5
  exact hc₀ (add_left_cancel ((h2 c₀).trans h5.symm)).symm

theorem exists_splitH (hσ : ∃ c : K, σ c ≠ c) (hH : ∀ x y, B y x = σ (B x y))
    (hBn : ∀ v, (∀ w, B v w = 0) → v = 0) (hAB : ∀ v w, B (A v) (A w) = B v w) (hp : Odd p)
    (hA : A ^ p = 1) (hW : LinearMap.range (A - 1) ≠ ⊥)
    (hnc : ¬ IsCyclicOn A (LinearMap.range (A - 1))) :
    ∃ M : Submodule K V, M ≤ LinearMap.range (A - 1) ∧ M ≠ ⊥ ∧ M ≠ LinearMap.range (A - 1) ∧
      (∀ m ∈ M, A m ∈ M) ∧ (∀ m ∈ M, (∀ n ∈ M, B n m = 0) → m = 0) := by
  set W := LinearMap.range (A - 1) with hWdef
  have hWinv : ∀ w ∈ W, A w ∈ W := fun w hw => range_invariant A hw
  obtain ⟨v, hvW, hvv⟩ : ∃ v ∈ W, B v v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall := form_eq_zero_of_isotropic hσ hH (W := W) hcon
    refine hW ((Submodule.eq_bot_iff _).mpr fun w hw => ?_)
    exact range_sepH hBn hAB hp hA w hw fun w' hw' => hall w hw w' hw'
  set U := cyc A v with hU
  have hUW : U ≤ W := cyc_le hWinv hvW
  have hUinv := cyc_invariant A v
  have hvU : v ∈ U := by simpa using pow_mem_cyc A v 0
  have hUne : U ≠ W := by
    intro h
    exact hnc ⟨v, hvW, h ▸ le_rfl⟩
  set R := U ⊓ U.orthogonalBilin B with hR
  have hRinv : ∀ r ∈ R, A r ∈ R := fun r hr =>
    ⟨hUinv r hr.1, orth_invariantH hAB hA hp.pos hUinv hr.2⟩
  obtain ⟨Q, hQinv, hRQ⟩ := exists_invariant_compl hp hA hRinv
  set M := Q ⊓ U with hM
  have hUdec : ∀ u ∈ U, ∃ r ∈ R, ∃ m ∈ M, r + m = u := by
    intro u hu
    have h1 : u ∈ R ⊔ Q := by rw [hRQ.sup_eq_top]; trivial
    obtain ⟨r, hr, q, hq, rfl⟩ := Submodule.mem_sup.mp h1
    refine ⟨r, hr, q, ⟨hq, ?_⟩, rfl⟩
    have : q = (r + q) - r := by abel
    rw [this]
    exact U.sub_mem hu hr.1
  have hRorth : ∀ r ∈ R, ∀ u ∈ U, B u r = 0 := fun r hr u hu =>
    (Submodule.mem_orthogonalBilin.mp hr.2) u hu
  have hMU : M ≤ U := inf_le_right
  have hMbot : M ≠ ⊥ := by
    intro h
    have : ∀ u ∈ U, u ∈ R := by
      intro u hu
      obtain ⟨r, hr, m, hm, rfl⟩ := hUdec u hu
      rw [h] at hm
      rw [(Submodule.mem_bot K).mp hm, add_zero]
      exact hr
    exact hvv ((Submodule.mem_orthogonalBilin.mp (this v hvU).2) v hvU)
  have hMW : M ≠ W := by
    intro h
    exact hUne (le_antisymm hUW (h ▸ hMU))
  have hMinv : ∀ m ∈ M, A m ∈ M := fun m hm => ⟨hQinv m hm.1, hUinv m hm.2⟩
  have hMn : ∀ m ∈ M, (∀ n ∈ M, B n m = 0) → m = 0 := by
    intro m hm h
    have hmR : m ∈ R := by
      refine ⟨hm.2, Submodule.mem_orthogonalBilin.mpr fun u hu => ?_⟩
      obtain ⟨r, hr, n, hn, rfl⟩ := hUdec u hu
      rw [map_add, LinearMap.add_apply, hH m r, hRorth r hr m hm.2, map_zero, h n hn, add_zero]
    exact Submodule.disjoint_def.mp hRQ.disjoint m hmR hm.1
  exact ⟨M, fun m hm => hUW hm.2, hMbot, hMW, hMinv, hMn⟩

theorem exists_independentH (hpp : p.Prime) (hH : ∀ x y, B y x = σ (B x y))
    (hAB : ∀ v w, B (A v) (A w) = B v w)
    (hp : Odd p) (hA : A ^ p = 1) [FiniteDimensional K V] {M : Submodule K V}
    (hMW : M ≤ LinearMap.range (A - 1)) (hM0 : M ≠ ⊥) (hMW' : M ≠ LinearMap.range (A - 1))
    (hMinv : ∀ m ∈ M, A m ∈ M) (hMn : ∀ m ∈ M, (∀ n ∈ M, B n m = 0) → m = 0) :
    ∃ u : Module.End K V, (∀ v w, B (u v) (u w) = B v w) ∧ u * A = A * u ∧ u ^ p = 1 ∧
      ∀ i j : ℕ, u ^ i * A ^ j = 1 → p ∣ i ∧ p ∣ j := by
  set W := LinearMap.range (A - 1) with hWdef
  have hcompl : IsCompl M (M.orthogonalBilin B) := isCompl_orthogonalBilin_of_sep hMn
  set N := M.orthogonalBilin B with hN
  have hNinv : ∀ z ∈ N, A z ∈ N := fun z hz => orth_invariantH hAB hA hp.pos hMinv hz
  let φ : M →ₗ[K] V := M.subtype ∘ₗ A.restrict hMinv
  let ψ : N →ₗ[K] V := N.subtype
  let u : Module.End K V := LinearMap.ofIsCompl hcompl φ ψ
  have hu1 : ∀ m ∈ M, u m = A m := fun m hm => by
    have := LinearMap.ofIsCompl_apply_left hcompl (φ := φ) (ψ := ψ) ⟨m, hm⟩
    simpa [φ, u] using this
  have hu2 : ∀ z ∈ N, u z = z := fun z hz => by
    have := LinearMap.ofIsCompl_apply_right hcompl (φ := φ) (ψ := ψ) ⟨z, hz⟩
    simpa [ψ, u] using this
  have hdec : ∀ v : V, ∃ m ∈ M, ∃ z ∈ N, m + z = v := by
    intro v
    have h1 : v ∈ M ⊔ N := by rw [hcompl.sup_eq_top]; trivial
    obtain ⟨m, hm, z, hz, h⟩ := Submodule.mem_sup.mp h1
    exact ⟨m, hm, z, hz, h⟩
  have hMN : ∀ m ∈ M, ∀ z ∈ N, B m z = 0 := fun m hm z hz =>
    Submodule.mem_orthogonalBilin.mp hz m hm
  have hNM : ∀ m ∈ M, ∀ z ∈ N, B z m = 0 := fun m hm z hz => by
    rw [hH m z, hMN m hm z hz, map_zero]
  have hpow : ∀ (i : ℕ), ∀ m ∈ M, ∀ z ∈ N, (u ^ i) (m + z) = (A ^ i) m + z := by
    intro i
    induction i with
    | zero => intro m hm z hz; simp
    | succ i ih =>
      intro m hm z hz
      rw [pow_succ, Module.End.mul_apply, map_add u m z, hu1 m hm, hu2 z hz,
        ih _ (hMinv m hm) z hz, pow_succ, Module.End.mul_apply]
  have hiso : ∀ v w, B (u v) (u w) = B v w := by
    intro v w
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec v
    obtain ⟨n, hn, y, hy, rfl⟩ := hdec w
    rw [map_add u m z, map_add u n y, hu1 m hm, hu2 z hz, hu1 n hn, hu2 y hy]
    simp only [map_add, LinearMap.add_apply]
    rw [hMN (A m) (hMinv m hm) y hy, hNM (A n) (hMinv n hn) z hz, hMN m hm y hy,
      hNM n hn z hz, hAB]
  have hcomm : u * A = A * u := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec v
    simp only [Module.End.mul_apply, map_add]
    rw [hu1 (A m) (hMinv m hm), hu2 (A z) (hNinv z hz), hu1 m hm, hu2 z hz]
  have hup : u ^ p = 1 := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec v
    rw [hpow p m hm z hz, hA]
    simp
  refine ⟨u, hiso, hcomm, hup, fun i j hij => ?_⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m ∈ M, m ≠ 0 := by
    by_contra h
    push Not at h
    exact hM0 ((Submodule.eq_bot_iff _).mpr h)
  obtain ⟨z, hzN, hzW, hz0⟩ : ∃ z ∈ N, z ∈ W ∧ z ≠ 0 := by
    obtain ⟨w, hwW, hwM⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hMW hMW')
    obtain ⟨m, hm, z, hz, rfl⟩ := hdec w
    refine ⟨z, hz, ?_, fun h => hwM (by rw [h, add_zero]; exact hm)⟩
    have : z = (m + z) - m := by abel
    rw [this]
    exact W.sub_mem hwW (hMW hm)
  have hj : p ∣ j := by
    have h1 := congrArg (fun f : Module.End K V => f z) hij
    simp only [Module.End.mul_apply, Module.End.one_apply] at h1
    have h2 := hpow i 0 M.zero_mem ((A ^ j) z) (invariant_pow hNinv j z hzN)
    rw [zero_add, map_zero, zero_add] at h2
    rw [h2] at h1
    exact dvd_of_pow_fixed hpp hp hA hzW hz0 h1
  have hij' : p ∣ i + j := by
    have h1 := congrArg (fun f : Module.End K V => f m) hij
    simp only [Module.End.mul_apply, Module.End.one_apply] at h1
    have h2 := hpow i ((A ^ j) m) (invariant_pow hMinv j m hm) 0 N.zero_mem
    rw [add_zero, add_zero] at h2
    rw [h2, ← Module.End.mul_apply, ← pow_add] at h1
    exact dvd_of_pow_fixed hpp hp hA (hMW hm) hm0 h1
  exact ⟨(Nat.dvd_add_left hj).mp hij', hj⟩

end Odd

end CFSG.RankThree.PartOne.OddIso
