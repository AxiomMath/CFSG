module

public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.Quasithin.H13.NQCatLieCentralG2

public section

namespace CFSG.Quasithin.H13.RootData.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.NQCat
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

theorem rC_isRoot : IsRoot Tag.G2 rC :=
  (isRoot_pos_iff.2 (by simp)).1

theorem torus_conj_gX_rC
    {K : Type} [Field K] {t : ModGL Tag.G2 K} (ht : t ∈ torusGroup Tag.G2 K) :
    ∃ l : Kˣ, ∀ s : K, t * gX rC s * t⁻¹ = gX rC ((l : K) * s) := by
  induction ht using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, u⟩, rfl⟩ := hx
    exact ⟨u ^ (∑ j, Tag.G2.cartan i j * rC j), fun s => root_torus_conjugation i rC_isRoot u s⟩
  | one => exact ⟨1, fun s => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, fun s => ?_⟩
    calc x * y * gX rC s * (x * y)⁻¹ = x * (y * gX rC s * y⁻¹) * x⁻¹ := by group
      _ = gX rC ((a * b : Kˣ) * s) := by rw [hb, ha, Units.val_mul, mul_assoc]
  | inv x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨a⁻¹, fun s => ?_⟩
    have h := ha (((a⁻¹ : Kˣ) : K) * s)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h
    calc x⁻¹ * gX rC s * x⁻¹⁻¹ = x⁻¹ * (x * gX rC (((a⁻¹ : Kˣ) : K) * s) * x⁻¹) * x := by
          rw [h, inv_inv]
      _ = gX rC (((a⁻¹ : Kˣ) : K) * s) := by group

theorem four_le_card {K : Type} {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    4 ≤ Nat.card K := by
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf

theorem parabolicRadical_le_perfectCore
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (i : Fin Tag.G2.rank) :
    parabolicRadical Tag.G2 K {i} ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
  rw [← G2Rad.pCoreOf_perfectCore_parabolic hK hf i]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem posUnipotent_le_perfectCore
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) :
    posUnipotent Tag.G2 K ≤ perfectCore (parabolicSubgroup Tag.G2 K {i0}) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hK4 := four_le_card hK hf
  have hQ := parabolicRadical_le_perfectCore hK hf i0
  obtain ⟨L, hLP, hL, hx, -, -⟩ := leviL_data hK4 i0
  intro x hx'
  obtain ⟨a, r, u, v, b, c, rfl⟩ := LieCentral.G2.exists_eq_prod_of_mem_posUnipotent hx'
  have hA : gX rA a ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}) := by
    rw [← rootOne_gX_i0]
    exact le_perfectCore_of_perfect hLP hL (hx a)
  have hmem : ∀ d, d ∈ ({rR, rU, rV, rB, rC} : Set (Fin Tag.G2.rank → ℤ)) → ∀ s : K,
      gX d s ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}) := fun d hd s =>
    hQ (pinnedX_mem_rootSpan (by rw [radicalRoots_zero]; exact hd) s)
  exact mul_mem hA (mul_mem (hmem rR (by simp) r) (mul_mem (hmem rU (by simp) u)
    (mul_mem (hmem rV (by simp) v) (mul_mem (hmem rB (by simp) b) (hmem rC (by simp) c)))))

theorem weyl_mem_perfectCore_zero
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    weylElt Tag.G2 K i0 1 ∈ perfectCore (parabolicSubgroup Tag.G2 K {i0}) := by
  obtain ⟨L, hLP, hL, hx, hy, -⟩ := leviL_data hK4 i0
  rw [weylElt_eq_xUnit_mul]
  exact le_perfectCore_of_perfect hLP hL (mul_mem (mul_mem (hx _) (hy _)) (hx _))

theorem reflect_i0_rC : reflect Tag.G2 i0 rC = rB := by
  funext k
  fin_cases k <;> decide

theorem map_entrywise_posUnipotent
    {K : Type} [Field K] (σ : K ≃+* K) :
    (posUnipotent Tag.G2 K).map (Units.map (entrywiseHom σ.toRingHom)) = posUnipotent Tag.G2 K := by
  simp only [posUnipotent, rootSpan, Subgroup.map_iSup, map_entrywise_rootSubgroup]

theorem exists_eq_gX_rC_of_centralizer
    {K : Type} [Field K] [Finite K] [CharP K 2] {g : ModGL Tag.G2 K}
    (hgC : g ∈ adjointGroup Tag.G2 K) (hcU : ∀ y ∈ posUnipotent Tag.G2 K, y * g = g * y) :
    ∃ d : K, g = gX rC d := by
  have hgN : g ∈ Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [show g * h * g⁻¹ = h by rw [← hcU h hh]; group]
      exact hh
    · intro hh
      have h1 := hcU _ hh
      have e : h = g * h * g⁻¹ := by
        calc h = g⁻¹ * (g * h * g⁻¹ * g) := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h1]
          _ = g * h * g⁻¹ := by group
      rw [e]
      exact hh
  have hgB : g ∈ borelGroup Tag.G2 K := by
    rw [← (borel_self_normalizers Tag.G2 K).1]
    exact ⟨hgC, hgN⟩
  have hgP : g ∈ parabolicSubgroup Tag.G2 K {i0} := borelGroup_le_parabolicSubgroup _ hgB
  have hgCQ : g ∈ Subgroup.centralizer (parabolicRadical Tag.G2 K {i0} : Set (ModGL Tag.G2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcU y (parabolicRadical_le_posUnipotent _ hy)
  have hJ : ({i0} : Set (Fin Tag.G2.rank)) ≠ Set.univ := by
    intro h
    have : i1 ∈ ({i0} : Set (Fin Tag.G2.rank)) := h ▸ Set.mem_univ i1
    exact absurd (Set.mem_singleton_iff.mp this) (by decide)
  have hgQ := (Chevalley_proper_parabolic_root_radical_self_centralizing Tag.G2 K hJ).2 ⟨hgP, hgCQ⟩
  have hgU : g ∈ posUnipotent Tag.G2 K := parabolicRadical_le_posUnipotent _ hgQ
  have hmemU : ∀ d, (d = rA ∨ d = rR ∨ d = rU ∨ d = rV ∨ d = rB ∨ d = rC) → ∀ s : K,
      gX d s ∈ posUnipotent Tag.G2 K := fun d hd s => LieCentral.G2.gX_mem_posUnipotent hd s
  obtain ⟨a, r, u', v, b, d, hg⟩ := LieCentral.G2.exists_eq_prod_of_mem_posUnipotent hgU
  have ha := LieCentral.G2.a_eq_zero_of_commute (y := (1 : K)) one_ne_zero
    (by rw [← hg]; exact hcU _ (hmemU rB (by simp) 1))
  have hru := LieCentral.G2.r_eq_zero_of_commute (y := (1 : K)) one_ne_zero
    (by rw [← hg]; exact hcU _ (hmemU rV (by simp) 1))
  obtain ⟨hr, hu'⟩ := hru
  subst ha hr hu'
  simp only [gX_zero, one_mul] at hg
  have hv := LieCentral.G2.v_eq_zero_of_commute (a := 0) (u := 0) (y := (1 : K)) one_ne_zero
    (by rw [gX_zero, gX_zero, one_mul, one_mul, ← hg]; exact hcU _ (hmemU rU (by simp) 1))
  subst hv
  simp only [gX_zero, one_mul] at hg
  have hb := LieCentral.G2.b_eq_zero_of_commute (a := 0) (y := (1 : K)) one_ne_zero
    (by rw [gX_zero, one_mul, ← hg]; exact hcU _ (hmemU rA (by simp) 1))
  subst hb
  simp only [gX_zero, one_mul] at hg
  exact ⟨d, hg⟩

theorem eq_one_of_centralizer_of_odd
    {K : Type} [Field K] [Finite K] [CharP K 2] {g : ModGL Tag.G2 K}
    (hgC : g ∈ adjointGroup Tag.G2 K) (hcU : ∀ y ∈ posUnipotent Tag.G2 K, y * g = g * y)
    (hodd : Odd (orderOf g)) : g = 1 := by
  obtain ⟨d, rfl⟩ := exists_eq_gX_rC_of_centralizer hgC hcU
  have h2 : gX rC d ^ 2 = 1 := by rw [sq, gX_self]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  have h1 : orderOf (gX rC d) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp h1

theorem eq_zero_of_commute_weyl
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : K}
    (h : weylElt Tag.G2 K i0 1 * gX rC d = gX rC d * weylElt Tag.G2 K i0 1) : d = 0 := by
  have hw : gX rB d = gX rC d := by
    have h1 := G2Rad.weyl_conj (K := K) i0 rC_isRoot d
    rw [reflect_i0_rC] at h1
    rw [← h1, h, mul_inv_cancel_right]
  have hAB := LieCentral.G2.conj_A_B (K := K) 1 d
  rw [one_mul, hw, MulAut.conj_apply] at hAB
  have hAC := Subgroup.mem_centralizer_iff.mp (LieCentral.G2.gX_rC_mem_centralizer d) (gX rA 1)
    (LieCentral.G2.gX_mem_posUnipotent (by simp) 1)
  rw [hAC, mul_inv_cancel_right] at hAB
  exact gX_eq_one (mul_eq_right.mp hAB.symm)

end CFSG.Quasithin.H13.RootData.G2
