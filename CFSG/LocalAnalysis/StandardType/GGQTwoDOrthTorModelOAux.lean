module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorModelV
public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorOmega

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open TauCeti.QuadraticMap QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

section ModelO

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

@[expose] noncomputable def plhExt (m a : ℕ) (ha : a ≤ m + 1) :
    (Fin a → K) →ₗ[F] (Fin (m + 1) → K) where
  toFun z := fun i => if h : i.val < a then z ⟨i.val, h⟩ else 0
  map_add' z w := by
    funext i
    by_cases h : i.val < a <;> simp [h]
  map_smul' c z := by
    funext i
    by_cases h : i.val < a <;> simp [h]

@[expose] noncomputable def plhRes (m a : ℕ) (ha : a ≤ m + 1) :
    (Fin (m + 1) → K) →ₗ[F] (Fin a → K) where
  toFun v := fun j => v ⟨j.val, lt_of_lt_of_le j.isLt ha⟩
  map_add' v w := by
    funext j
    simp
  map_smul' c v := by
    funext j
    simp

@[simp] theorem plhExt_apply (m a : ℕ) (ha : a ≤ m + 1) (z : Fin a → K)
    (i : Fin (m + 1)) :
    plhExt (F := F) (K := K) m a ha z i = if h : i.val < a then z ⟨i.val, h⟩ else 0 := rfl

@[simp] theorem plhRes_apply (m a : ℕ) (ha : a ≤ m + 1) (v : Fin (m + 1) → K)
    (j : Fin a) :
    plhRes (F := F) (K := K) m a ha v j = v ⟨j.val, lt_of_lt_of_le j.isLt ha⟩ := rfl

@[simp] theorem plhRes_plhExt (m a : ℕ) (ha : a ≤ m + 1) (z : Fin a → K) :
    plhRes (F := F) (K := K) m a ha (plhExt (F := F) (K := K) m a ha z) = z := by
  funext j
  simp

theorem plhExt_smul (m a : ℕ) (ha : a ≤ m + 1) (c : K) (z : Fin a → K) :
    plhExt (F := F) (K := K) m a ha (c • z) = c • plhExt (F := F) (K := K) m a ha z := by
  funext i
  by_cases h : i.val < a <;> simp [h]

theorem plhRes_smul (m a : ℕ) (ha : a ≤ m + 1) (c : K) (v : Fin (m + 1) → K) :
    plhRes (F := F) (K := K) m a ha (c • v) = c • plhRes (F := F) (K := K) m a ha v := by
  funext j
  simp

theorem plhExt_mem_torStdV₀ (m a : ℕ) (ha : a ≤ m + 1) (z : Fin a → K) :
    plhExt (F := F) (K := K) m a ha z ∈ torStdV₀ (F := F) (K := K) m a := by
  intro i hi
  rw [plhExt_apply, dif_neg (not_lt.2 hi)]

theorem plhRes_eq_zero_of_mem_torStdV₁ (m a : ℕ) (ha : a ≤ m + 1)
    {v : Fin (m + 1) → K} (hv : v ∈ torStdV₁ (F := F) (K := K) m a) :
      plhRes (F := F) (K := K) m a ha v = 0 := by
  funext j
  exact hv ⟨j.val, lt_of_lt_of_le j.isLt ha⟩ j.isLt

theorem plhExt_plhRes_of_mem_torStdV₀ (m a : ℕ) (ha : a ≤ m + 1)
    {v : Fin (m + 1) → K} (hv : v ∈ torStdV₀ (F := F) (K := K) m a) :
    plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) = v := by
  funext i
  by_cases h : i.val < a
  · rw [plhExt_apply, dif_pos h]
    exact congrArg v (Fin.ext rfl)
  · rw [plhExt_apply, dif_neg h, (hv i (not_lt.1 h)).symm]

theorem plh_sub_plhExt_plhRes_mem_torStdV₁ (m a : ℕ) (ha : a ≤ m + 1)
    (v : Fin (m + 1) → K) :
    v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) ∈
      torStdV₁ (F := F) (K := K) m a := by
  intro i hi
  rw [Pi.sub_apply, plhExt_apply, dif_pos hi]
  rw [sub_eq_zero]
  exact congrArg v (Fin.ext rfl)

theorem plh_isCompl_torStdV (m a : ℕ) (ha : a ≤ m + 1) :
    IsCompl (torStdV₀ (F := F) (K := K) m a) (torStdV₁ (F := F) (K := K) m a) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro v hv0 hv1
    funext i
    by_cases h : i.val < a
    · exact hv1 i h
    · exact hv0 i (not_lt.1 h)
  · rw [codisjoint_iff, Submodule.eq_top_iff']
    intro v
    have h1 := plhExt_mem_torStdV₀ (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)
    have h2 := plh_sub_plhExt_plhRes_mem_torStdV₁ (F := F) (K := K) m a ha v
    have hv : plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) +
        (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) = v := by abel
    rw [← hv]
    exact Submodule.add_mem_sup h1 h2

theorem plh_Qn_plhExt (E : QuadExt F K (unitaryInvolution K 2 1)) (m a : ℕ)
    (ha : a ≤ m + 1) (z : Fin a → K) :
    Qn E (m + 1) (plhExt (F := F) (K := K) m a ha z) = Qn E a z := by
  rw [Qn_apply, Qn_apply]
  let emb : Fin a → Fin (m + 1) := fun j => ⟨j.val, lt_of_lt_of_le j.isLt ha⟩
  have hemb : Set.InjOn emb (Finset.univ : Finset (Fin a)) :=
    fun j₁ _ j₂ _ h => Fin.ext (congrArg (fun x : Fin (m + 1) => x.val) h)
  have hzero : ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
      i ∉ (Finset.univ : Finset (Fin a)).image emb →
        normQuad E (plhExt (F := F) (K := K) m a ha z i) = 0 := by
    intro i _ hi
    have hge : a ≤ i.val := by
      by_contra hlt
      exact hi (Finset.mem_image.mpr
        ⟨⟨i.val, not_le.1 hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    rw [plhExt_apply, dif_neg (not_lt.2 hge), map_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_image hemb]
  apply Finset.sum_congr rfl
  intro j _
  rw [plhExt_apply, dif_pos j.isLt]

theorem plh_polar_torStdV_orth (E : QuadExt F K (unitaryInvolution K 2 1)) (m a : ℕ)
    {u w : Fin (m + 1) → K} (hu : u ∈ torStdV₀ (F := F) (K := K) m a)
    (hw : w ∈ torStdV₁ (F := F) (K := K) m a) :
    polar (Qn E (m + 1)) u w = 0 := by
  rw [polar_Qn]
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i.val < a
  · rw [hw i h, polar_zero_right]
  · rw [hu i (not_lt.1 h), polar_zero_left]

theorem plh_mem_torStdV₀_of_mem_torE₀ (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    {g : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)}
    (hg : g ∈ torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)) {v : Fin (m + 1) → K}
    (hv : v ∈ torStdV₀ (F := F) (K := K) m a) : g v ∈ torStdV₀ (F := F) (K := K) m a := by
  have hcompl := plh_isCompl_torStdV (F := F) (K := K) m a ha
  have hQ := Qn_polarBilin_nondegenerate E (m + 1)
  have hV₁ : torV₁ (torStdM (F := F) ζ m a) = torStdV₁ (F := F) (K := K) m a := torV₁_torStdM hζ m a
  have hfix : ∀ w ∈ torStdV₁ (F := F) (K := K) m a, g w = w := by
    intro w hw
    exact hg.2 w (by rwa [hV₁])
  have hfix' : ∀ w ∈ torStdV₁ (F := F) (K := K) m a, g.symm w = w := by
    intro w hw
    have hginv : g⁻¹ ∈ torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) :=
      (torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)).inv_mem hg
    simpa using hginv.2 w (by rwa [hV₁])
  have havmem : g v ∈ torStdV₀ (F := F) (K := K) m a ⊔ torStdV₁ (F := F) (K := K) m a := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w₀, hw₀, w₁, hw₁, hsum⟩ := Submodule.mem_sup.mp havmem
  suffices w₁ = 0 by
    have : g v = w₀ := by rw [← hsum, this, add_zero]
    rw [this]
    exact hw₀
  have horth₁ : ∀ w ∈ torStdV₁ (F := F) (K := K) m a, polar (Qn E (m + 1)) w₁ w = 0 := by
    intro w hw
    have hthis : polar (Qn E (m + 1)) (g v) w = 0 := by
      have hgw : g.symm w = w := hfix' w hw
      rw [← g.apply_symm_apply w, polar_apply_of_mem_orthogonalGroup hg.1 v (g.symm w), hgw]
      exact plh_polar_torStdV_orth E m a hv hw
    have hsum' : polar (Qn E (m + 1)) (g v) w =
        polar (Qn E (m + 1)) w₀ w + polar (Qn E (m + 1)) w₁ w := by
      rw [← hsum, polar_add_left]
    rw [hsum', plh_polar_torStdV_orth E m a hw₀ hw, zero_add] at hthis
    exact hthis
  have horth₀ : ∀ w ∈ torStdV₀ (F := F) (K := K) m a, polar (Qn E (m + 1)) w₁ w = 0 := by
    intro w hw
    rw [polar_comm]
    exact plh_polar_torStdV_orth E m a hw hw₁
  have hall : ∀ y : Fin (m + 1) → K, polar (Qn E (m + 1)) w₁ y = 0 := by
    intro y
    have hymem : y ∈ torStdV₀ (F := F) (K := K) m a ⊔ torStdV₁ (F := F) (K := K) m a := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y₀, hy₀, y₁, hy₁, hy⟩ := Submodule.mem_sup.mp hymem
    rw [← hy, polar_add_right, horth₀ y₀ hy₀, horth₁ y₁ hy₁, add_zero]
  exact hQ.1 w₁ fun y => by rw [polarBilin_apply_apply]; exact hall y

@[expose] noncomputable def plhToLinear (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    (Fin a → K) →ₗ[F] (Fin a → K) :=
  (plhRes (F := F) (K := K) m a ha).comp
    ((g.1 : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)).toLinearMap.comp
      (plhExt (F := F) (K := K) m a ha))

theorem plhToLinear_apply (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) (z : Fin a → K) :
    plhToLinear E hζ m a ha g z =
      plhRes (F := F) (K := K) m a ha (g.1 (plhExt (F := F) (K := K) m a ha z)) := rfl

@[expose] noncomputable def plhToLinearInv (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    (Fin a → K) →ₗ[F] (Fin a → K) :=
  (plhRes (F := F) (K := K) m a ha).comp
    ((g.1.symm : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)).toLinearMap.comp
      (plhExt (F := F) (K := K) m a ha))

theorem plhToLinear_comp_inv (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    (plhToLinear E hζ m a ha g).comp (plhToLinearInv E hζ m a ha g) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp only [plhToLinear, plhToLinearInv, LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap]
  have hw : g.1.symm (plhExt (F := F) (K := K) m a ha z) ∈
      torStdV₀ (F := F) (K := K) m a := by
    have h := plh_mem_torStdV₀_of_mem_torE₀ E hζ m a ha (Subgroup.inv_mem _ g.2)
      (plhExt_mem_torStdV₀ (F := F) (K := K) m a ha z)
    simpa using h
  rw [plhExt_plhRes_of_mem_torStdV₀ (F := F) (K := K) m a ha hw]
  rw [g.1.apply_symm_apply]
  exact plhRes_plhExt m a ha z

theorem plhToLinearInv_comp (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    (plhToLinearInv E hζ m a ha g).comp (plhToLinear E hζ m a ha g) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  simp only [plhToLinear, plhToLinearInv, LinearMap.comp_apply, LinearMap.id_apply,
    LinearEquiv.coe_toLinearMap]
  have hw : g.1 (plhExt (F := F) (K := K) m a ha z) ∈
      torStdV₀ (F := F) (K := K) m a :=
    plh_mem_torStdV₀_of_mem_torE₀ E hζ m a ha g.2 (plhExt_mem_torStdV₀ (F := F) (K := K) m a ha z)
  rw [plhExt_plhRes_of_mem_torStdV₀ (F := F) (K := K) m a ha hw]
  rw [g.1.symm_apply_apply]
  exact plhRes_plhExt m a ha z

@[expose] noncomputable def plhToEquiv (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    (Fin a → K) ≃ₗ[F] (Fin a → K) :=
  LinearEquiv.ofLinearMap (plhToLinear E hζ m a ha g) (plhToLinearInv E hζ m a ha g)
    (plhToLinear_comp_inv E hζ m a ha g) (plhToLinearInv_comp E hζ m a ha g)

theorem plhToEquiv_apply (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) (z : Fin a → K) :
    plhToEquiv E hζ m a ha g z =
      plhRes (F := F) (K := K) m a ha (g.1 (plhExt (F := F) (K := K) m a ha z)) := rfl

theorem plhToLinear_mem_orthogonalGroup (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (g : ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a))) :
    plhToEquiv E hζ m a ha g ∈ orthogonalGroup (Qn E a) := by
  rw [mem_orthogonalGroup_iff]
  intro z
  rw [plhToEquiv_apply]
  have hw : g.1 (plhExt (F := F) (K := K) m a ha z) ∈ torStdV₀ (F := F) (K := K) m a :=
    plh_mem_torStdV₀_of_mem_torE₀ E hζ m a ha g.2 (plhExt_mem_torStdV₀ (F := F) (K := K) m a ha z)
  rw [← plh_Qn_plhExt E m a ha
      (plhRes (F := F) (K := K) m a ha (g.1 (plhExt (F := F) (K := K) m a ha z))),
    plhExt_plhRes_of_mem_torStdV₀ (F := F) (K := K) m a ha hw,
    mem_orthogonalGroup_iff.mp g.2.1 (plhExt (F := F) (K := K) m a ha z),
    plh_Qn_plhExt E m a ha z]

@[expose] noncomputable def plhPhi (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1) :
    ↥(torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a)) →*
      ↥(orthogonalGroup (Qn E a)) where
  toFun g := ⟨plhToEquiv E hζ m a ha g, plhToLinear_mem_orthogonalGroup E hζ m a ha g⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rw [plhToEquiv_apply]
    exact plhRes_plhExt m a ha z
  map_mul' g h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    rw [plhToEquiv_apply, Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply]
    have hw : h.1 (plhExt (F := F) (K := K) m a ha z) ∈
        torStdV₀ (F := F) (K := K) m a :=
      plh_mem_torStdV₀_of_mem_torE₀ E hζ m a ha h.2
        (plhExt_mem_torStdV₀ (F := F) (K := K) m a ha z)
    rw [← plhExt_plhRes_of_mem_torStdV₀ (F := F) (K := K) m a ha hw]
    exact (plhToEquiv_apply E hζ m a ha g _).symm

@[expose] noncomputable def plhPsiLinear (E : QuadExt F K (unitaryInvolution K 2 1))
    (m a : ℕ) (ha : a ≤ m + 1)
    (h : ↥(orthogonalGroup (Qn E a))) :
    (Fin (m + 1) → K) →ₗ[F] (Fin (m + 1) → K) :=
  ((plhExt (F := F) (K := K) m a ha).comp ((h.1 : (Fin a → K) ≃ₗ[F] (Fin a → K)).toLinearMap.comp
    (plhRes (F := F) (K := K) m a ha))) + (LinearMap.id -
      (plhExt (F := F) (K := K) m a ha).comp (plhRes (F := F) (K := K) m a ha))

theorem plhPsiLinear_apply (E : QuadExt F K (unitaryInvolution K 2 1))
    (m a : ℕ) (ha : a ≤ m + 1) (h : ↥(orthogonalGroup (Qn E a)))
    (v : Fin (m + 1) → K) :
    plhPsiLinear E m a ha h v =
      plhExt (F := F) (K := K) m a ha (h.1 (plhRes (F := F) (K := K) m a ha v)) +
        (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) :=
  rfl

theorem plhPsiLinear_comp (E : QuadExt F K (unitaryInvolution K 2 1))
    (m a : ℕ) (ha : a ≤ m + 1) (h : ↥(orthogonalGroup (Qn E a))) :
    (plhPsiLinear E m a ha h).comp (plhPsiLinear E m a ha h⁻¹) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.id_apply, plhPsiLinear_apply, plhPsiLinear_apply]
  rw [show plhRes (F := F) (K := K) m a ha (plhExt (F := F) (K := K) m a ha
      ((h⁻¹).1 (plhRes (F := F) (K := K) m a ha v)) +
      (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v))) =
      (h⁻¹).1 (plhRes (F := F) (K := K) m a ha v) from by
    rw [map_add, plhRes_plhExt, plhRes_eq_zero_of_mem_torStdV₁ (F := F) (K := K) m a ha
      (plh_sub_plhExt_plhRes_mem_torStdV₁ (F := F) (K := K) m a ha v), add_zero]]
  rw [show h.1 ((h⁻¹).1 (plhRes (F := F) (K := K) m a ha v)) =
      plhRes (F := F) (K := K) m a ha v from by
    rw [← LinearEquiv.mul_apply, Subgroup.coe_inv, mul_inv_cancel]
    rfl]
  abel

theorem plhPsiLinear_comp' (E : QuadExt F K (unitaryInvolution K 2 1))
    (m a : ℕ) (ha : a ≤ m + 1) (h : ↥(orthogonalGroup (Qn E a))) :
    (plhPsiLinear E m a ha h⁻¹).comp (plhPsiLinear E m a ha h) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.id_apply, plhPsiLinear_apply, plhPsiLinear_apply]
  rw [show plhRes (F := F) (K := K) m a ha (plhExt (F := F) (K := K) m a ha
      (h.1 (plhRes (F := F) (K := K) m a ha v)) +
      (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v))) =
      h.1 (plhRes (F := F) (K := K) m a ha v) from by
    rw [map_add, plhRes_plhExt, plhRes_eq_zero_of_mem_torStdV₁ (F := F) (K := K) m a ha
      (plh_sub_plhExt_plhRes_mem_torStdV₁ (F := F) (K := K) m a ha v), add_zero]]
  rw [show (h⁻¹).1 (h.1 (plhRes (F := F) (K := K) m a ha v)) =
      plhRes (F := F) (K := K) m a ha v from by
    rw [← LinearEquiv.mul_apply, Subgroup.coe_inv, inv_mul_cancel]
    rfl]
  abel

theorem plhPsiEquiv_mem (E : QuadExt F K (unitaryInvolution K 2 1))
    {ζ : normOne (unitaryInvolution K 2 1)} (hζ : ζ ≠ 1) (m a : ℕ) (ha : a ≤ m + 1)
    (h : ↥(orthogonalGroup (Qn E a))) :
    (LinearEquiv.ofLinearMap (plhPsiLinear E m a ha h) (plhPsiLinear E m a ha h⁻¹)
        (plhPsiLinear_comp E m a ha h) (plhPsiLinear_comp' E m a ha h) :
        (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) ∈
      torE₀ (Qn E (m + 1)) (torStdM (F := F) ζ m a) := by
  let ψ : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K) :=
    LinearEquiv.ofLinearMap (plhPsiLinear E m a ha h) (plhPsiLinear E m a ha h⁻¹)
      (plhPsiLinear_comp E m a ha h) (plhPsiLinear_comp' E m a ha h)
  have hψ : ∀ v, ψ v = plhExt (F := F) (K := K) m a ha (h.1 (plhRes (F := F) (K := K) m a ha v)) +
      (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) := fun v => rfl
  rw [torE₀, Subgroup.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [mem_orthogonalGroup_iff]
    intro v
    have ht : v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) ∈
        torStdV₁ (F := F) (K := K) m a :=
      plh_sub_plhExt_plhRes_mem_torStdV₁ (F := F) (K := K) m a ha v
    have hA : plhExt (F := F) (K := K) m a ha (h.1 (plhRes (F := F) (K := K) m a ha v)) ∈
        torStdV₀ (F := F) (K := K) m a :=
      plhExt_mem_torStdV₀ (F := F) (K := K) m a ha _
    have hAB : plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) ∈
        torStdV₀ (F := F) (K := K) m a :=
      plhExt_mem_torStdV₀ (F := F) (K := K) m a ha _
    have hv : v = plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v) +
        (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) := by abel
    calc Qn E (m + 1) (ψ v)
        = Qn E (m + 1) (plhExt (F := F) (K := K) m a ha (h.1 (plhRes (F := F) (K := K) m a ha v)) +
            (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v))) := by
          rw [hψ]
      _ = Qn E (m + 1) (plhExt (F := F) (K := K) m a ha (h.1 (plhRes (F := F) (K := K) m a ha v))) +
            Qn E (m + 1)
              (v - plhExt (F := F) (K := K) m a ha (plhRes (F := F) (K := K) m a ha v)) := by
          rw [QuadraticMap.map_add (Qn E (m + 1)),
            plh_polar_torStdV_orth E m a hA ht, add_zero]
      _ = Qn E (m + 1) v := by
          rw [plh_Qn_plhExt E m a ha (h.1 (plhRes (F := F) (K := K) m a ha v)),
            mem_orthogonalGroup_iff.mp h.2 (plhRes (F := F) (K := K) m a ha v),
            ← plh_Qn_plhExt E m a ha (plhRes (F := F) (K := K) m a ha v)]
          conv_rhs => rw [hv, QuadraticMap.map_add (Qn E (m + 1)),
            plh_polar_torStdV_orth E m a hAB ht, add_zero]
  · rw [torV₁_torStdM hζ m a]
    intro w hw
    rw [hψ]
    have hw0 : plhRes (F := F) (K := K) m a ha w = 0 :=
      plhRes_eq_zero_of_mem_torStdV₁ (F := F) (K := K) m a ha hw
    rw [hw0, map_zero, map_zero, zero_add, sub_zero]

end ModelO

end CFSG.StandardType.QTwo

end
