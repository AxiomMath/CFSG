module

public import CFSG.Quasithin.Background.F918V2G3
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

private theorem szd_div_swap {G : Type*} [CommGroup G] {x y z u : G}
    (h : x * y⁻¹ = z * u⁻¹) : x * z⁻¹ = y * u⁻¹ := by
  calc x * z⁻¹ = (x * y⁻¹) * (y * u⁻¹) * (z * u⁻¹)⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    _ = (z * u⁻¹) * (y * u⁻¹) * (z * u⁻¹)⁻¹ := by rw [h]
    _ = y * u⁻¹ := by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel

private theorem szd_mul_eq {G : Type*} [CommGroup G] {p q a b u : G} :
    p * a * (q * b)⁻¹ = (p * (b * u⁻¹)⁻¹) * (q * (a * u⁻¹)⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem sz_commV_inv {Y L : Subgroup (MulAut W)} (hLY : ∀ l ∈ L, ∀ y ∈ Y, l * y = y * l) :
    ∀ l ∈ L, ∀ u ∈ commV Y, l u ∈ commV Y := by
  intro l hl u hu
  induction hu using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, v, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨x, hx, l v, ?_⟩
    have h1 : l (x v) = x (l v) := by
      have := congrArg (fun φ : MulAut W => φ v) (hLY l hl x hx)
      simpa [MulAut.mul_apply] using this
    rw [map_mul, map_inv, h1]
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

omit [Finite W] in
theorem sz_orbSup_eq_commV {Y T : Subgroup (MulAut W)} {I : Subgroup W}
    (hTY : T ≤ Subgroup.normalizer (Y : Set (MulAut W))) (hI : XMod.IsIrrPlus ↥Y I)
    (hker : ∀ y ∈ Y, ∀ w : W, y w * w⁻¹ ∈ orbSup T I) :
    orbSup T I = commV Y := by
  have hkey : ∀ t ∈ T, I.map t.toMonoidHom ≤ commV Y := by
    intro t ht
    rintro _ ⟨i, hi, rfl⟩
    have hi' : i ∈ XMod.commOf ↥Y I := by rw [hI.2.1]; exact hi
    have hle : XMod.commOf ↥Y I ≤ (commV Y).comap t.toMonoidHom := by
      rw [XMod.commOf, Subgroup.closure_le]
      rintro _ ⟨a, l, hl, rfl⟩
      have hta : t * (a : MulAut W) * t⁻¹ ∈ Y :=
        ((Subgroup.mem_normalizer_iff.mp (hTY ht)) (a : MulAut W)).mp a.2
      have hal : a • l = (a : MulAut W) l := rfl
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure ⟨t * (a : MulAut W) * t⁻¹, hta, t l, ?_⟩
      simp [MulAut.mul_apply, hal]
    exact hle hi'
  refine le_antisymm (orbSup_le hkey) ?_
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, rfl⟩
  exact hker x hx v

omit [Finite W] in
private theorem szd_step_one {L K : Subgroup (MulAut W)} {U : Subgroup W}
    (hKL : ∀ x ∈ K, ∀ y ∈ L, x * y = y * x)
    (hLU : ∀ l ∈ L, ∀ u ∈ U, l u * u⁻¹ ∈ fixV K) :
    ∀ k ∈ K, ∀ u ∈ U, k u * u⁻¹ ∈ fixV L := by
  intro k hk u hu l hl
  have he : k (l u * u⁻¹) = l u * u⁻¹ := hLU l hl u hu k hk
  have hcomm : l (k u) = k (l u) := by
    have := congrArg (fun φ : MulAut W => φ u) (hKL k hk l hl)
    simpa [MulAut.mul_apply] using this.symm
  rw [map_mul, map_inv] at he
  rw [map_mul, map_inv, hcomm]
  exact szd_div_swap he

omit [Finite W] in
private theorem szd_comm_mem {K : Subgroup (MulAut W)} {U C : Subgroup W}
    (hKU : ∀ k ∈ K, ∀ w : W, k w * w⁻¹ ∈ U) (hKC : ∀ k ∈ K, ∀ u ∈ U, k u * u⁻¹ ∈ C)
    {k k' : MulAut W} (hk : k ∈ K) (hk' : k' ∈ K) (x : W) : ⁅k, k'⁆ x * x⁻¹ ∈ C := by
  obtain ⟨u, rfl⟩ : ∃ u : W, x = k' (k u) := ⟨k⁻¹ (k'⁻¹ x), by simp⟩
  have hκ : ⁅k, k'⁆ (k' (k u)) = k (k' u) := by
    simp [commutatorElement_def, MulAut.mul_apply]
  have e₁ : k (k' u) = k (k' u * u⁻¹) * k u := by rw [← map_mul, inv_mul_cancel_right]
  have e₂ : k' (k u) = k' (k u * u⁻¹) * k' u := by rw [← map_mul, inv_mul_cancel_right]
  rw [hκ, e₁, e₂, szd_mul_eq (u := u)]
  exact C.mul_mem (hKC k hk _ (hKU k' hk' u)) (C.inv_mem (hKC k' hk' _ (hKU k hk u)))

theorem sz_final {M Mp T K : Subgroup (MulAut W)} {V : Subgroup W} (hD : D3Std M Mp T Mp V)
    (hKM : K ≤ M) (hKL : ∀ x ∈ K, ∀ y ∈ Mp, x * y = y * x) (hKperf : ⁅K, K⁆ = K) (hK1 : K ≠ ⊥)
    {U : Subgroup W} (hKU : ∀ k ∈ K, ∀ w : W, k w * w⁻¹ ∈ U)
    (hLU : ∀ l ∈ Mp, ∀ u ∈ U, l u * u⁻¹ ∈ fixV K) : False := by
  have h1 := szd_step_one hKL hLU
  have hcomm : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k'⁆ ∈ Z391.centTrivQ M Mp := by
    intro k hk k' hk'
    have hmem : ⁅k, k'⁆ ∈ K := by
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')
    refine ⟨hKM hmem, fun l hl => ?_, fun v => szd_comm_mem hKU h1 hk hk' v⟩
    have hk1 : Commute k l := hKL k hk l hl
    have hk2 : Commute k' l := hKL k' hk' l hl
    rw [commutatorElement_def]
    exact (((hk1.mul_left hk2).mul_left hk1.inv_left).mul_left hk2.inv_left)
  have hle : ⁅K, K⁆ ≤ Z391.centTrivQ M Mp := Subgroup.commutator_le.mpr hcomm
  rw [hKperf] at hle
  apply hK1
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  obtain ⟨hkM, hkL, hkQ⟩ := hle hk
  exact Z391.v2g_faithful_on_Q hD hkM hkL hkQ

end CFSG.Quasithin
