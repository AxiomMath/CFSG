module

public import CFSG.Quasithin.EmptyFaithful.S152N2Lin
public import CFSG.Quasithin.EmptyFaithful.S14117Basic

public section

namespace CFSG.Quasithin

namespace S152N2

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem conjAct_coe' (V : Subgroup G) (g : Subgroup.normalizer (V : Set G)) (x : V) :
    ((conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

theorem commutator_eq_map_commV {U A : Subgroup G} (hU : IsElemAbelian 2 U)
    (hA : A ≤ Subgroup.normalizer (U : Set G)) :
    ⁅U, A⁆ = (@commV ↥U (commGroupOfElemAbelian hU) (autOn A U)).map U.subtype := by
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro u hu a ha
    have haN := hA ha
    have hu' : a * u⁻¹ * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp haN u⁻¹).mp (U.inv_mem hu)
    let g : Subgroup.normalizer (U : Set G) := ⟨a, haN⟩
    have hx : conjAct U g ∈ autOn A U := mem_autOn_iff_exists.mpr ⟨a, haN, ha, rfl⟩
    refine ⟨conjAct U g ⟨u⁻¹, U.inv_mem hu⟩ * (⟨u⁻¹, U.inv_mem hu⟩ : ↥U)⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨conjAct U g, hx, ⟨u⁻¹, U.inv_mem hu⟩, rfl⟩
    · have hcomm : (a * u⁻¹ * a⁻¹) * u = u * (a * u⁻¹ * a⁻¹) := (setLike_mul_comm hu' hu : _)
      have h1 : (((conjAct U g ⟨u⁻¹, U.inv_mem hu⟩ * (⟨u⁻¹, U.inv_mem hu⟩ : ↥U)⁻¹ : ↥U)) : G) =
          a * u⁻¹ * a⁻¹ * u := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [conjAct_coe']
      show (((conjAct U g ⟨u⁻¹, U.inv_mem hu⟩ * (⟨u⁻¹, U.inv_mem hu⟩ : ↥U)⁻¹ : ↥U)) : G) = _
      rw [h1, hcomm]
      simp only [commutatorElement_def]
      group
  · rw [Subgroup.map_le_iff_le_comap, commV, Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨a, haN, haA, rfl⟩ := mem_autOn_iff_exists.mp hx
    have h1 : (((conjAct U ⟨a, haN⟩ v * v⁻¹ : ↥U)) : G) = ⁅(a : G), (v : G)⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [conjAct_coe']
      simp only [commutatorElement_def]
    show (((conjAct U ⟨a, haN⟩ v * v⁻¹ : ↥U)) : G) ∈ ⁅U, A⁆
    rw [h1, Subgroup.commutator_comm U A]
    exact Subgroup.commutator_mem_commutator haA v.2

theorem map_fixV_autOn {U A : Subgroup G} (hU : IsElemAbelian 2 U)
    (hA : A ≤ Subgroup.normalizer (U : Set G)) :
    (@fixV ↥U (commGroupOfElemAbelian hU) (autOn A U)).map U.subtype =
      U ⊓ Subgroup.centralizer (A : Set G) := by
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  ext v
  simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.2, fun a ha => ?_⟩
    have haN := hA ha
    have hx : conjAct U ⟨a, haN⟩ ∈ autOn A U := mem_autOn_iff_exists.mpr ⟨a, haN, ha, rfl⟩
    have h1 := congrArg (fun z : ↥U => (z : G)) (hu _ hx)
    simp only [conjAct_coe'] at h1
    calc a * (u : G) = a * u * a⁻¹ * a := by group
      _ = u * a := by rw [h1]
  · rintro ⟨hvU, hv⟩
    refine ⟨⟨v, hvU⟩, fun x hx => ?_, rfl⟩
    obtain ⟨a, haN, haA, rfl⟩ := mem_autOn_iff_exists.mp hx
    apply Subtype.ext
    rw [conjAct_coe']
    have := hv a haA
    calc a * v * (a : G)⁻¹ = v * a * (a : G)⁻¹ := by rw [this]
      _ = v := by group

theorem star_lemma [Finite G] {M V B Mc : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVcard : Nat.card V = 16) (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hBM : B ≤ M)
    (hB2 : Nat.card (autOn B V) = 2) (hWcard : Nat.card (⁅V, B⁆ : Subgroup G) = 4)
    (hMc : Subgroup.normalizer ((⁅V, B⁆ : Subgroup G) : Set G) ≤ Mc)
    {w₀ : G} (hw₀ : w₀ ∈ (⁅V, B⁆ : Subgroup G)) (hw₀1 : w₀ ≠ 1)
    (hcen : ∀ g ∈ Mc, (∃ a : ℕ, g ^ (3 ^ a) = 1) → g * w₀ = w₀ * g) :
    ∀ y ∈ autOn M V, y ^ 3 = 1 → (∀ b ∈ autOn B V, b * y = y * b) → y = 1 := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hV.2 v v.2)
  have hBN : B ≤ Subgroup.normalizer (V : Set G) := hBM.trans hMV
  have hWeq := commutator_eq_map_commV hV hBN
  obtain ⟨b₀, -, hb₀sq, hgen⟩ := exists_zpowers_eq_of_card_two hB2
  rw [hgen] at hWeq
  have hWc : Nat.card (commV (Subgroup.zpowers b₀)) = 4 := by
    rw [← hWcard, hWeq]
    exact (Subgroup.card_map_of_injective V.subtype_injective).symm
  have hfix : fixV (Subgroup.zpowers b₀) ≤ commV (Subgroup.zpowers b₀) :=
    (fixV_eq_commV_of_card hV2 hb₀sq hVcard hWc).le
  intro y hy hy3 hcomm
  have hb₀mem : b₀ ∈ autOn B V := by rw [hgen]; exact Subgroup.mem_zpowers b₀
  have hcomm₀ : b₀ * y = y * b₀ := hcomm b₀ hb₀mem
  by_contra hy1
  have hnot : ¬ ∀ w ∈ commV (Subgroup.zpowers b₀), y w = w := fun h =>
    hy1 (eq_one_of_centralizes_commV hV2 hy3 hcomm₀ hfix h)
  push Not at hnot
  obtain ⟨w, hwW, hyw⟩ := hnot
  obtain ⟨g₀, hg₀N, hg₀M, hg₀y⟩ := mem_autOn_iff_exists.mp hy
  let φ : ↥M →* MulAut ↥V := (conjAct V).comp (Subgroup.inclusion hMV)
  have hφ : φ ⟨g₀, hg₀M⟩ = y := hg₀y
  obtain ⟨g, a, hga, hgφ⟩ := exists_three_power_lift φ ⟨g₀, hg₀M⟩ (isOfFinOrder_of_finite _)
    (by rw [hφ]; exact hy3) (by rw [hφ]; exact hy1)
  rw [hφ] at hgφ
  have hgM : (g : G) ∈ M := g.2
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := hMV hgM
  have hgy : conjAct V ⟨(g : G), hgN⟩ = y := hgφ
  have hcomm₁ : b₀ * y⁻¹ = y⁻¹ * b₀ := (Commute.inv_right (show Commute b₀ y from hcomm₀)).eq
  have hginv : (g : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) := (Subgroup.normalizer _).inv_mem hgN
  have hgnorm : (g : G) ∈ Subgroup.normalizer ((⁅V, B⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hWeq]
    constructor
    · rintro ⟨w', hw', rfl⟩
      refine ⟨y w', apply_mem_commV_zpowers hcomm₀ hw', ?_⟩
      have h2 := conjAct_coe' V ⟨(g : G), hgN⟩ w'
      rw [hgy] at h2
      exact h2
    · rintro ⟨w', hw', hw'h⟩
      refine ⟨y⁻¹ w', apply_mem_commV_zpowers hcomm₁ hw', ?_⟩
      have h1 : conjAct V ⟨(g : G)⁻¹, hginv⟩ = y⁻¹ := by
        rw [← hgy, ← map_inv]
        rfl
      have h2 := conjAct_coe' V ⟨(g : G)⁻¹, hginv⟩ w'
      rw [h1] at h2
      show ((y⁻¹ w' : ↥V) : G) = h
      rw [h2]
      have h3 : (w' : G) = (g : G) * h * (g : G)⁻¹ := hw'h
      rw [h3]
      group
  have hgMc : (g : G) ∈ Mc := hMc hgnorm
  have hg3 : ∃ a : ℕ, (g : G) ^ (3 ^ a) = 1 :=
    ⟨a, by have := congrArg Subtype.val hga; simpa using this⟩
  have hcomm₂ := hcen (g : G) hgMc hg3
  rw [hWeq] at hw₀
  obtain ⟨w', hw', rfl⟩ := hw₀
  have hcomm₃ : (g : G) * (w' : G) = (w' : G) * (g : G) := hcomm₂
  have hyw' : y w' = w' := by
    apply Subtype.ext
    rw [← hgy, conjAct_coe']
    calc (g : G) * w' * (g : G)⁻¹ = (w' * g) * (g : G)⁻¹ := by rw [hcomm₃]
      _ = w' := by group
  have hw'1 : w' ≠ 1 := fun h => hw₀1 (by rw [h]; rfl)
  have hall := fixed_of_pow_three (fun w hw => hV2 w) hWc hy3
    (fun w hw => apply_mem_commV_zpowers hcomm₀ hw) hw' hw'1 hyw'
  exact hyw (hall w hwW)

end S152N2

end CFSG.Quasithin
