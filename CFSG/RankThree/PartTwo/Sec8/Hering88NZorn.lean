module

public import CFSG.RankThree.PartTwo.Sec8.Hering88NLinAlg
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Base

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open CFSG.Open CFSG.Quasithin.H13.Orbit

variable {K : Type*} [Field K]

@[expose] def zornPolar (x y : quasithinZorn K) : K :=
  x.1 * y.2.2.2 + y.1 * x.2.2.2 - ∑ i, (x.2.1 i * y.2.2.1 i + y.2.1 i * x.2.2.1 i)

theorem zornPolar_eq (x y : quasithinZorn K) :
    zornPolar x y = zornNorm (x + y) - zornNorm x - zornNorm y := by
  simp only [zornPolar, zornNorm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem zornPolar_comm (x y : quasithinZorn K) : zornPolar x y = zornPolar y x := by
  simp only [zornPolar, Fin.sum_univ_three]
  ring

theorem zornPolar_add_right (x y y' : quasithinZorn K) :
    zornPolar x (y + y') = zornPolar x y + zornPolar x y' := by
  simp only [zornPolar, Prod.fst_add, Prod.snd_add, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem zornPolar_add_left (x x' y : quasithinZorn K) :
    zornPolar (x + x') y = zornPolar x y + zornPolar x' y := by
  rw [zornPolar_comm, zornPolar_add_right, zornPolar_comm y, zornPolar_comm y]

theorem zornPolar_zero_right (x : quasithinZorn K) : zornPolar x 0 = 0 := by
  simp [zornPolar]

theorem zornPolar_nondeg (x : quasithinZorn K) (h : ∀ y, zornPolar x y = 0) : x = 0 := by
  have ha := h (0, 0, 0, 1)
  have hb := h (1, 0, 0, 0)
  simp only [zornPolar, Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add, mul_one,
    Finset.sum_const_zero, sub_zero, one_mul] at ha hb
  apply zorn_ext
  · exact ha
  · intro i
    have h1 := h (0, 0, Pi.single i 1, 0)
    simp only [zornPolar, Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add,
      zero_sub] at h1
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
      (fun hi => absurd (Finset.mem_univ i) hi)] at h1
    simpa using h1
  · intro i
    have h1 := h (0, Pi.single i 1, 0, 0)
    simp only [zornPolar, Pi.zero_apply, mul_zero, zero_mul, add_zero, zero_add,
      zero_sub] at h1
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
      (fun hi => absurd (Finset.mem_univ i) hi)] at h1
    simpa using h1
  · exact hb

@[expose] def zornConj (x : quasithinZorn K) : quasithinZorn K := (x.2.2.2, -x.2.1, -x.2.2.1, x.1)

theorem zornConj_eq (x : quasithinZorn K) : zornConj x = zornTr x • zornOne - x := by
  apply zorn_ext <;> (try intro i) <;> simp [zornConj, zornTr, zornOne]

theorem zornPolar_one (x : quasithinZorn K) : zornPolar x zornOne = zornTr x := by
  simp [zornPolar, zornOne, zornTr]

theorem zornPolar_mul_left (x y w : quasithinZorn K) :
    zornPolar (quasithinZornMul x y) w = zornPolar y (quasithinZornMul (zornConj x) w) := by
  simp [zornPolar, quasithinZornMul, zornConj, quasithinCross, Fin.sum_univ_three]
  ring

theorem zornMul_conj_right (x y : quasithinZorn K) :
    quasithinZornMul (quasithinZornMul x y) (zornConj y) = zornNorm y • x := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [quasithinZornMul, zornConj, zornNorm, quasithinCross, Fin.sum_univ_three] <;> ring

theorem zornMul_add_left (x x' y : quasithinZorn K) :
    quasithinZornMul (x + x') y = quasithinZornMul x y + quasithinZornMul x' y := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [quasithinZornMul, quasithinCross, Fin.sum_univ_three] <;> ring

theorem zornMul_smul_left (c : K) (x y : quasithinZorn K) :
    quasithinZornMul (c • x) y = c • quasithinZornMul x y := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [quasithinZornMul, quasithinCross, Fin.sum_univ_three] <;> ring

@[expose] def zornMulRight (j : quasithinZorn K) : quasithinZorn K →ₗ[K] quasithinZorn K where
  toFun x := quasithinZornMul x j
  map_add' x x' := zornMul_add_left x x' j
  map_smul' c x := zornMul_smul_left c x j

theorem finrank_zorn : Module.finrank K (quasithinZorn K) = 8 := by
  simp [quasithinZorn, Module.finrank_prod, Module.finrank_fin_fun]

section G2

variable {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ quasithinG2 K)
include hg

theorem zornPolar_map (x y : quasithinZorn K) : zornPolar (g x) (g y) = zornPolar x y := by
  rw [zornPolar_eq, zornPolar_eq, ← map_add, quasithinG2_norm hg, quasithinG2_norm hg,
    quasithinG2_norm hg]

theorem zornConj_map (x : quasithinZorn K) : g (zornConj x) = zornConj (g x) := by
  have ht : zornTr (g x) = zornTr x := by
    rw [← zornPolar_one, ← zornPolar_one]
    conv_lhs => rw [← quasithinG2_one hg]
    exact zornPolar_map hg x zornOne
  rw [zornConj_eq, zornConj_eq, map_sub, map_smul, quasithinG2_one hg, ht]

end G2

theorem coe_end_pow {V : Type*} [AddCommGroup V] [Module K V] (g : V ≃ₗ[K] V) (n : ℕ) :
    ((g ^ n : V ≃ₗ[K] V) : Module.End K V) = (g : Module.End K V) ^ n :=
  map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom g n

theorem finrank_ker_sub_one_le_four [CharP K 2] {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ quasithinG2 K) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    Module.finrank K (LinearMap.ker ((g : Module.End K (quasithinZorn K)) - 1)) ≤ 4 := by
  set G : Module.End K (quasithinZorn K) := (g : Module.End K (quasithinZorn K)) with hGdef
  have hG3 : G ^ 3 = 1 := by
    rw [hGdef, ← coe_end_pow, hg3]
    rfl
  have h3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have : (3 : K) = 1 := by
      calc (3 : K) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [this]
    exact one_ne_zero
  have hc := isCompl_ker_sub_one_ker_sq_add_add_one h3 G hG3
  set B := LinearMap.ker (G - 1) with hBdef
  set M := LinearMap.ker (G ^ 2 + G + 1) with hMdef
  have hgB : ∀ x, x ∈ B ↔ g x = x := fun x => by
    rw [hBdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rfl
  have hgM : ∀ x, x ∈ M ↔ g (g x) + g x + x = 0 := fun x => by
    rw [hMdef, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply,
      pow_two, Module.End.mul_apply]
    rfl
  have hmem : ∀ x : quasithinZorn K, ∃ b ∈ B, ∃ m ∈ M, b + m = x := fun x =>
    Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top)
  have hmul := mem_zornAuts_of_mem hg
  have hBM : ∀ b ∈ B, ∀ m ∈ M, zornPolar b m = 0 := by
    intro b hb m hm
    have hb' : g b = b := (hgB b).mp hb
    have h1 : zornPolar b (g m) = zornPolar b m := by
      have := zornPolar_map hg b m
      rwa [hb'] at this
    have h2 : zornPolar b (g (g m)) = zornPolar b m := by
      have := zornPolar_map hg b (g m)
      rwa [hb', h1] at this
    have h4 : zornPolar b (g (g m) + g m + m) = 0 := by
      rw [(hgM m).mp hm, zornPolar_zero_right]
    rw [zornPolar_add_right, zornPolar_add_right, h1, h2] at h4
    have h5 : (3 : K) * zornPolar b m = 0 := by linear_combination h4
    exact (mul_eq_zero.mp h5).resolve_left h3
  have hperp : ∀ x, (∀ b ∈ B, zornPolar x b = 0) → x ∈ M := by
    intro x hx
    obtain ⟨b, hb, m, hm, rfl⟩ := hmem x
    have hb0 : b = 0 := zornPolar_nondeg b fun y => by
      obtain ⟨b', hb', m', hm', rfl⟩ := hmem y
      have e1 : zornPolar b b' = 0 := by
        have h1 := hx b' hb'
        rw [zornPolar_add_left, zornPolar_comm m b', hBM b' hb' m hm, add_zero] at h1
        exact h1
      rw [zornPolar_add_right, e1, hBM b hb m' hm', add_zero]
    rw [hb0, zero_add]
    exact hm
  have hMne : M ≠ ⊥ := by
    intro hM0
    apply hg1
    have hBtop : B = ⊤ := by
      have := hc.sup_eq_top
      rwa [hM0, sup_bot_eq] at this
    exact LinearEquiv.ext fun x => (hgB x).mp (hBtop ▸ Submodule.mem_top)
  obtain ⟨j, hjM, hj⟩ : ∃ j ∈ M, zornNorm j ≠ 0 := by
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
    obtain ⟨m', hm', hmm'⟩ : ∃ m' ∈ M, zornPolar m m' ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hm0
      apply zornPolar_nondeg m
      intro y
      obtain ⟨b', hb', m', hm', rfl⟩ := hmem y
      rw [zornPolar_add_right, zornPolar_comm m b', hBM b' hb' m hm, hcon m' hm', add_zero]
    rw [zornPolar_eq] at hmm'
    by_cases h1 : zornNorm (m + m') = 0
    · by_cases h2 : zornNorm m = 0
      · exact ⟨m', hm', fun h4 => hmm' (by rw [h1, h2, h4]; ring)⟩
      · exact ⟨m, hm, h2⟩
    · exact ⟨m + m', M.add_mem hm hm', h1⟩
  have hBmul : ∀ b ∈ B, ∀ b' ∈ B, quasithinZornMul b b' ∈ B := fun b hb b' hb' =>
    (hgB _).mpr (by rw [hmul, (hgB b).mp hb, (hgB b').mp hb'])
  have hBconj : ∀ b ∈ B, zornConj b ∈ B := fun b hb =>
    (hgB _).mpr (by rw [zornConj_map hg, (hgB b).mp hb])
  have hρM : ∀ b : B, (zornMulRight j ∘ₗ B.subtype) b ∈ M := fun b => by
    refine hperp _ fun b' hb' => ?_
    show zornPolar (quasithinZornMul (b : quasithinZorn K) j) b' = 0
    rw [zornPolar_mul_left, zornPolar_comm]
    exact hBM _ (hBmul _ (hBconj _ b.2) _ hb') j hjM
  let ρ : B →ₗ[K] M := (zornMulRight j ∘ₗ B.subtype).codRestrict M hρM
  have hρ : Function.Injective ρ := by
    intro b b' hbb'
    have h1 : quasithinZornMul (b : quasithinZorn K) j = quasithinZornMul (b' : quasithinZorn K) j :=
      congrArg (fun x : M => (x : quasithinZorn K)) hbb'
    have h2 := congrArg (fun x => quasithinZornMul x (zornConj j)) h1
    simp only [zornMul_conj_right] at h2
    exact Subtype.ext (smul_right_injective _ hj h2)
  have hle := LinearMap.finrank_le_finrank_of_injective hρ
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  rw [finrank_zorn] at hsum
  omega

end CFSG.RankThree.PartTwo.Sec8.Hering88N

end
