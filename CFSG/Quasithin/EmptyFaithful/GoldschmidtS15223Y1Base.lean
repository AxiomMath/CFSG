module

public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.S152U21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace S15223

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem oPrimeResidual_le {N : Subgroup G} : oPrimeResidualOf 3 N ≤ N :=
  (Subgroup.closure_le N).mpr fun _ hg => hg.1

theorem mem_normalizer_oPrimeResidual {M V N : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hNM : N ≤ M)
    (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ N) {x : G} (hxM : x ∈ M)
    (hxD : ∀ d ∈ autOn (oPrimeResidualOf 3 N) V,
      conjAct V ⟨x, hMV hxM⟩ * d * (conjAct V ⟨x, hMV hxM⟩)⁻¹ ∈ autOn (oPrimeResidualOf 3 N) V) :
    x ∈ Subgroup.normalizer (oPrimeResidualOf 3 N : Set G) := by
  set X := oPrimeResidualOf 3 N with hX
  have hle : ∀ y ∈ X, x * y * x⁻¹ ∈ X := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨hgN, k, hk⟩ := hg
      have hgM : g ∈ M := hNM hgN
      have hg'M : x * g * x⁻¹ ∈ M := M.mul_mem (M.mul_mem hxM hgM) (M.inv_mem hxM)
      have hconj := conjAct_conj (hMV hxM) (hMV hgM) (hMV hg'M)
      have hgD : conjAct V ⟨g, hMV hgM⟩ ∈ autOn X V :=
        mem_autOn_of_mem (hMV hgM) (Subgroup.subset_closure ⟨hgN, k, hk⟩)
      have h1 : x * g * x⁻¹ ∈ N := by
        refine mem_of_conjAct_mem_autOn hMV hNM hC hg'M ?_
        rw [hconj]
        exact A4.autOn_mono oPrimeResidual_le (hxD _ hgD)
      have hord : orderOf (x * g * x⁻¹) = 3 ^ k := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hk
      exact Subgroup.subset_closure ⟨h1, k, hord⟩
    | one => simp
    | mul a b _ _ ha hb => simpa [mul_assoc] using X.mul_mem ha hb
    | inv a _ ha => simpa [mul_assoc] using X.inv_mem ha
  have hsub : conjSub x X ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using hle y hy
  have heq : conjSub x X = X :=
    Subgroup.eq_of_le_of_card_ge hsub (by
      have : Nat.card (conjSub x X) = Nat.card X :=
        Subgroup.card_map_of_injective (MulAut.conj x).injective
      omega)
  exact mem_normalizer_of_conjSub_eq152 heq

theorem mem_normalizer_oPrimeResidual_of_comm {M V N : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hNM : N ≤ M)
    (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ N) {E : Subgroup (MulAut V)}
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hDE : autOn (oPrimeResidualOf 3 N) V ≤ E) {x : G}
    (hxM : x ∈ M) (hxE : conjAct V ⟨x, hMV hxM⟩ ∈ E) :
    x ∈ Subgroup.normalizer (oPrimeResidualOf 3 N : Set G) := by
  refine mem_normalizer_oPrimeResidual hMV hNM hC hxM fun d hd => ?_
  have hc := hEc _ hxE d (hDE hd)
  have : conjAct V ⟨x, hMV hxM⟩ * d * (conjAct V ⟨x, hMV hxM⟩)⁻¹ = d := by
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact hd

omit [Finite G] in
theorem autOn_oPrimeResidual_le {M V N : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hNM : N ≤ M) : autOn (oPrimeResidualOf 3 N) V ≤ oTwoUpper (autOn M V) := by
  intro a ha
  obtain ⟨x, hx, hxX, rfl⟩ := mem_autOn_iff_exists.mp ha
  have hXP : oPrimeResidualOf 3 N ≤ preOn M V (oTwoUpper (autOn M V)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hgN, k, hk⟩
    have hgM : g ∈ M := hNM hgN
    refine mem_preOn.mpr ⟨hgM, hMV hgM, mem_oTwoUpper_of_odd (mem_autOn_of_mem _ hgM) ?_⟩
    have h1 : orderOf (conjAct V ⟨g, hMV hgM⟩) ∣ 3 ^ k := by
      have := orderOf_map_dvd (conjAct V) (⟨g, hMV hgM⟩ : Subgroup.normalizer (V : Set G))
      rw [Subgroup.orderOf_mk, hk] at this
      exact this
    exact Odd.of_dvd_nat (Odd.pow (by decide)) h1
  obtain ⟨-, hx', hxE⟩ := mem_preOn.mp (hXP hxX)
  exact hxE

omit [Finite G] in
theorem autOn_sup {X Y V : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hY : Y ≤ Subgroup.normalizer (V : Set G)) : autOn (X ⊔ Y) V = autOn X V ⊔ autOn Y V :=
  CFSG.Quasithin.AutOn.autOn_sup_eq hX hY

omit [Finite G] in
theorem autOn_conjSub_eq {M V Y : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G)) {t : G}
    (htM : t ∈ M) (hYM : Y ≤ M) :
    autOn (conjSub t Y) V =
      (autOn Y V).map (MulAut.conj (conjAct V ⟨t, hMV htM⟩)).toMonoidHom := by
  ext a
  rw [mem_autOn_iff_exists, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxY, rfl⟩
    have hy : t⁻¹ * x * t ∈ Y := mem_conjSub.mp hxY
    have hyV : t⁻¹ * x * t ∈ Subgroup.normalizer (V : Set G) := hMV (hYM hy)
    have hxeq : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    have hxV : t * (t⁻¹ * x * t) * t⁻¹ ∈ Subgroup.normalizer (V : Set G) := by rw [hxeq]; exact hx
    refine ⟨conjAct V ⟨t⁻¹ * x * t, hyV⟩, mem_autOn_of_mem hyV hy, ?_⟩
    have h := conjAct_conj (hMV htM) hyV hxV
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← h]
    congr 2
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨y, hy, hyY, rfl⟩ := mem_autOn_iff_exists.mp hd
    have hyM : y ∈ M := hYM hyY
    have hxM : t * y * t⁻¹ ∈ M := M.mul_mem (M.mul_mem htM hyM) (M.inv_mem htM)
    have hxV : t * y * t⁻¹ ∈ Subgroup.normalizer (V : Set G) := hMV hxM
    refine ⟨t * y * t⁻¹, hxV, ?_, ?_⟩
    · rw [mem_conjSub]
      have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rw [e]
      exact hyY
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact conjAct_conj (hMV htM) hy hxV

end S15223

end CFSG.Quasithin
