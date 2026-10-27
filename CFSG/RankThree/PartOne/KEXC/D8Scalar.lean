module

public import CFSG.RankThree.PartOne.KF.D8Normalizer

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU

section Vectors

variable {p : ℕ} {K : Type} [Field K]

@[expose] def SmallVec (v : D8Mod p K) : Prop :=
  (v.1 = 1 ∧ v.2 ≠ 1) ∨ (v.2 = 1 ∧ v.1 ≠ 1)

@[expose] def BigVec (v : D8Mod p K) : Prop :=
  v.1 ≠ 1 ∧ (v.2 = v.1 ∨ v.2 = v.1⁻¹)

theorem smallVec_of_fixed_even (hp : Odd p) {w : D8Mod p K} (hw : w ≠ 1) {j : ZMod 4}
    (hj : j = 0 ∨ j = 2) (hfix : d8Act (DihedralGroup.sr j) w = w) : SmallVec w := by
  rcases hj with rfl | rfl
  · have h1 := congrArg Prod.fst hfix
    rw [d8Act_sr_zero] at h1
    have h2 : w.1 = 1 := eq_one_of_inv_eq_self hp h1
    exact Or.inl ⟨h2, fun h => hw (Prod.ext h2 h)⟩
  · have h1 := congrArg Prod.snd hfix
    rw [d8Act_sr_two] at h1
    have h2 : w.2 = 1 := eq_one_of_inv_eq_self hp h1
    exact Or.inr ⟨h2, fun h => hw (Prod.ext h h2)⟩

end Vectors

section Finite

theorem exists_dihedral_conj_of_parity (θ : ZMod 4 → ZMod 4) (hinj : Function.Injective θ)
    (h1 : θ 1 = 1 ∨ θ 1 = 3) (h3 : θ 3 = 1 ∨ θ 3 = 3) :
    ∃ δ : DihedralGroup 4, ∀ i, δ * DihedralGroup.sr i * δ⁻¹ = DihedralGroup.sr (θ i) := by
  have key : ∀ a b c d : ZMod 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      (b = 1 ∨ b = 3) → (d = 1 ∨ d = 3) → ∃ δ : DihedralGroup 4,
        δ * DihedralGroup.sr 0 * δ⁻¹ = DihedralGroup.sr a ∧
        δ * DihedralGroup.sr 1 * δ⁻¹ = DihedralGroup.sr b ∧
        δ * DihedralGroup.sr 2 * δ⁻¹ = DihedralGroup.sr c ∧
        δ * DihedralGroup.sr 3 * δ⁻¹ = DihedralGroup.sr d := by
    decide
  have hne : ∀ i j : ZMod 4, i ≠ j → θ i ≠ θ j := fun i j h e => h (hinj e)
  obtain ⟨δ, h0, h1', h2, h3'⟩ := key (θ 0) (θ 1) (θ 2) (θ 3) (hne 0 1 (by decide))
    (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
    (hne 2 3 (by decide)) h1 h3
  refine ⟨δ, fun i => ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
  rcases hi with rfl | rfl | rfl | rfl
  exacts [h0, h1', h2, h3']

end Finite

section Main

variable {p : ℕ} {K : Type} [Field K]

theorem exists_pow_of_commutes_reflections (hp : p.Prime) (hp2 : p ≠ 2)
    (φ : MulAut (D8Mod p K))
    (h2 : φ * d8Act (DihedralGroup.sr 2) = d8Act (DihedralGroup.sr 2) * φ)
    (h3 : φ * d8Act (DihedralGroup.sr 3) = d8Act (DihedralGroup.sr 3) * φ) :
    ∃ k : ℤ, ∀ v, φ v = v ^ k := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have : NeZero p := ⟨hp.ne_zero⟩
  have hA : ∀ a : rootsOfUnity p K, (φ (a, 1)).2 = 1 := by
    intro a
    have := congrArg (fun m : MulAut (D8Mod p K) => m (a, 1)) h2
    simp only [MulAut.mul_apply, d8Act_sr_two, inv_one] at this
    exact eq_one_of_inv_eq_self hpodd (congrArg Prod.snd this).symm
  have hC : ∀ a : rootsOfUnity p K, φ (1, a) = (1, (φ (a, 1)).1) := by
    intro a
    have := congrArg (fun m : MulAut (D8Mod p K) => m (a, 1)) h3
    simp only [MulAut.mul_apply, d8Act_sr_three] at this
    rw [this, hA]
  let g : rootsOfUnity p K →* rootsOfUnity p K :=
    (MonoidHom.fst _ _).comp (φ.toMonoidHom.comp (MonoidHom.inl _ _))
  have hg : ∀ a, φ (a, 1) = (g a, 1) := fun a => Prod.ext rfl (hA a)
  obtain ⟨k, hk⟩ := MonoidHom.map_cyclic g
  refine ⟨k, fun v => ?_⟩
  have hv : v = (v.1, 1) * (1, v.2) := Prod.ext (mul_one _).symm (one_mul _).symm
  rw [hv, map_mul, hg, hC, hg, hk, hk]
  exact Prod.ext (by simp) (by simp)

theorem exists_d8Act_mul_pow (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (φ : MulAut (D8Mod p K))
    (hnorm : ∀ w : DihedralGroup 4, ∃ w' : DihedralGroup 4, φ * d8Act w * φ⁻¹ = d8Act w')
    (hcls : ∀ v : D8Mod p K, BigVec v → ¬ SmallVec (φ v)) :
    ∃ (γ : DihedralGroup 4) (k : ℤ), ∀ v, φ v = d8Act γ (v ^ k) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hinj : Function.Injective (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) :=
    d8Act_injective hp hp2 hζ
  choose θ hθ using exists_sr_conj hp hp2 hζ φ hnorm
  have hθinj : Function.Injective θ := by
    intro i i' h
    have h1 : φ * d8Act (DihedralGroup.sr i) * φ⁻¹ = φ * d8Act (DihedralGroup.sr i') * φ⁻¹ := by
      rw [hθ i, hθ i', h]
    have h2 : (d8Act (DihedralGroup.sr i) : MulAut (D8Mod p K)) = d8Act (DihedralGroup.sr i') :=
      mul_left_cancel (mul_right_cancel h1)
    exact DihedralGroup.sr.inj (hinj h2)
  obtain ⟨a, ha1⟩ : ∃ a : rootsOfUnity p K, a ≠ 1 := by
    obtain ⟨ζ, hζ'⟩ := hζ
    refine ⟨⟨ζ, (mem_rootsOfUnity p _).mpr hζ'.pow_eq_one⟩, fun h => ?_⟩
    have h0 : ζ = 1 := congrArg Subtype.val h
    rw [h0] at hζ'
    have := hζ'.eq_orderOf
    rw [orderOf_one] at this
    exact hp.ne_one this
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  have hodd : ∀ i : ZMod 4, (i = 1 ∨ i = 3) → (θ i = 1 ∨ θ i = 3) := by
    intro i hi
    obtain ⟨v, hvfix, hvbig⟩ : ∃ v : D8Mod p K, d8Act (DihedralGroup.sr i) v = v ∧ BigVec v := by
      rcases hi with rfl | rfl
      · exact ⟨(a, a⁻¹), by rw [d8Act_sr_one]; simp, ha1, Or.inr rfl⟩
      · exact ⟨(a, a), by rw [d8Act_sr_three], ha1, Or.inl rfl⟩
    have hφv1 : φ v ≠ 1 := by
      intro h
      have h1 : v = 1 := φ.injective (by rw [h, map_one])
      exact hvbig.1 (congrArg Prod.fst h1)
    have hfix : d8Act (DihedralGroup.sr (θ i)) (φ v) = φ v := by
      have := congrArg (fun m : MulAut (D8Mod p K) => m (φ v)) (hθ i)
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this
      rw [← this, hvfix]
    rcases hcases (θ i) with h | h | h | h
    · exact absurd (smallVec_of_fixed_even hpodd hφv1 (Or.inl h) hfix)
        (hcls v hvbig)
    · exact Or.inl h
    · exact absurd (smallVec_of_fixed_even hpodd hφv1 (Or.inr h) hfix)
        (hcls v hvbig)
    · exact Or.inr h
  obtain ⟨δ, hδ⟩ := exists_dihedral_conj_of_parity θ hθinj (hodd 1 (Or.inl rfl))
    (hodd 3 (Or.inr rfl))
  set φ' : MulAut (D8Mod p K) := (d8Act (p := p) (K := K) δ)⁻¹ * φ with hφ'
  have hcomm : ∀ i, φ' * d8Act (DihedralGroup.sr i) = d8Act (DihedralGroup.sr i) * φ' := by
    intro i
    have h1 := hθ i
    have h2 : d8Act (p := p) (K := K) δ * d8Act (DihedralGroup.sr i) *
        (d8Act (p := p) (K := K) δ)⁻¹ = d8Act (DihedralGroup.sr (θ i)) := by
      rw [← map_inv, ← map_mul, ← map_mul, hδ i]
    calc φ' * d8Act (DihedralGroup.sr i)
        = (d8Act (p := p) (K := K) δ)⁻¹ * (φ * d8Act (DihedralGroup.sr i) * φ⁻¹) * φ := by
          simp only [hφ']; group
      _ = (d8Act (p := p) (K := K) δ)⁻¹ * (d8Act (p := p) (K := K) δ *
            d8Act (DihedralGroup.sr i) * (d8Act (p := p) (K := K) δ)⁻¹) * φ := by
          rw [h1, h2]
      _ = d8Act (DihedralGroup.sr i) * φ' := by simp only [hφ']; group
  obtain ⟨k, hk⟩ := exists_pow_of_commutes_reflections hp hp2 φ' (hcomm 2) (hcomm 3)
  refine ⟨δ, k, fun v => ?_⟩
  have hφ : φ = d8Act (p := p) (K := K) δ * φ' := by rw [hφ', mul_inv_cancel_left]
  rw [hφ, MulAut.mul_apply, hk v]

end Main

end CFSG.RankThree.PartOne.KEXC
