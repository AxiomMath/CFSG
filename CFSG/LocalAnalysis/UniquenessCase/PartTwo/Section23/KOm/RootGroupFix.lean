module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.RankThree.GF2n.Stroth80.HeringSec63Geom

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open Matrix
open QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
  (eichler eichler_add_smul_self mem_rootGroup rootGroupGL toLinEquiv toLinEquiv_apply
   polar_smul_left_eq)
open CFSG.RankThree.GF2n.Stroth80.HS6

variable {K : Type} [Field K]

private theorem card_le_card_quotient_of_eichler_cover {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {Q : QuadraticForm K (ι → K)} {u : ι → K}
    (hu : Q u = 0) (hu0 : u ≠ 0) {F : Subgroup (GL ι K)}
    {X : Set (ι → K)} {Y : Submodule K (ι → K)}
    (hXsubY : X ⊆ Y) (huY : u ∈ Y)
    (hcover : ∀ g ∈ F, ∃ w ∈ X, eichler Q u w = toLinEquiv ι K g) :
    Nat.card ↥F ≤ Nat.card K ^ (Module.finrank K Y - 1) := by
  classical
  let KuY : Submodule K Y := Submodule.span K {⟨u, huY⟩}
  haveI : Finite (Y ⧸ KuY) :=
    Finite.of_surjective Submodule.Quotient.mk (Submodule.Quotient.mk_surjective KuY)
  let W : ↥F → ι → K := fun g => Classical.choose (hcover g g.2)
  have hWX : ∀ g : ↥F, W g ∈ X := fun g => (Classical.choose_spec (hcover g g.2)).1
  have hWE : ∀ g : ↥F, eichler Q u (W g) = toLinEquiv ι K (g : GL ι K) :=
    fun g => (Classical.choose_spec (hcover g g.2)).2
  let φ : ↥F → Y ⧸ KuY := fun g =>
    Submodule.Quotient.mk (p := KuY) ⟨W g, hXsubY (hWX g)⟩
  have hφinj : Function.Injective φ := by
    intro g₁ g₂ hφ
    have hmem : (⟨W g₁, hXsubY (hWX g₁)⟩ : Y) - ⟨W g₂, hXsubY (hWX g₂)⟩ ∈ KuY :=
      (Submodule.Quotient.eq KuY).mp hφ
    have hmem' : (⟨W g₁, hXsubY (hWX g₁)⟩ : Y) - ⟨W g₂, hXsubY (hWX g₂)⟩ ∈
        Submodule.span K {⟨u, huY⟩} := by simpa [KuY] using hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem'
    have hval : c • u = W g₁ - W g₂ := by
      have := congrArg (Subtype.val) hc
      simpa using this
    have hw : W g₁ = W g₂ + c • u := by
      rw [hval]
      abel
    have hE : eichler Q u (W g₁) = eichler Q u (W g₂) := by
      rw [hw, eichler_add_smul_self hu]
    have hto : toLinEquiv ι K (g₁ : GL ι K) = toLinEquiv ι K (g₂ : GL ι K) := by
      rw [← hWE g₁, ← hWE g₂]
      exact hE
    exact Subtype.ext ((toLinEquiv ι K).injective hto)
  have hcard : Nat.card (Y ⧸ KuY) = Nat.card K ^ (Module.finrank K Y - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Y ⧸ KuY)]
    congr 1
    have h := Submodule.finrank_quotient_add_finrank KuY
    have h1 : Module.finrank K KuY = 1 := by
      have hne : (⟨u, huY⟩ : Y) ≠ 0 := by
        intro h0
        exact hu0 (Subtype.ext_iff.mp h0)
      simpa [KuY] using finrank_span_singleton hne
    omega
  calc
    Nat.card ↥F ≤ Nat.card (Y ⧸ KuY) := Nat.card_le_card_of_injective φ hφinj
    _ = Nat.card K ^ (Module.finrank K Y - 1) := hcard

private theorem fixed_le_orthogonal_of_le_rootGroupGL {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {u : ι → K} (hu : Q u = 0)
    (hu0 : u ≠ 0) {F : Subgroup (GL ι K)} (hF : F ≤ rootGroupGL Q u) (hF1 : F ≠ ⊥)
    {X : Set (ι → K)} {Y : Submodule K (ι → K)}
    (hX : ∀ w ∈ X, polar Q u w = 0)
    (hXF : ∀ w ∈ X, (toLinEquiv ι K).symm (eichler Q u w) ∈ F)
    (hYX : Y = Submodule.span K (X ∪ {u})) :
    {v : ι → K | ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} ⊆
      (LinearMap.BilinForm.orthogonal (polarBilin Q) Y : Set (ι → K)) := by
  classical
  intro v hv
  change v ∈ LinearMap.BilinForm.orthogonal (polarBilin Q) Y
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  obtain ⟨g0, hg0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hF1
  have hg0mem : (g0 : GL ι K) ∈ rootGroupGL Q u := hF g0.2
  rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hg0mem
  obtain ⟨w0, hw0pol, hw0E⟩ := mem_rootGroup.mp hg0mem
  have hne : eichler Q u w0 ≠ 1 := by
    intro hE1
    apply hg0ne
    have h1 : toLinEquiv ι K (g0 : GL ι K) = 1 := by rw [← hw0E, hE1]
    have h2 : (g0 : GL ι K) = 1 := (toLinEquiv ι K).injective (by simpa using h1)
    exact Subtype.ext h2
  have hwu0 : ∀ c : K, w0 ≠ c • u := by
    intro c hc
    exact hne (eichler_eq_one_of_smul hu hc)
  have hv0 : toLinEquiv ι K (g0 : GL ι K) v = v := by
    rw [toLinEquiv_apply]
    exact hv (g0 : GL ι K) g0.2
  have hEfix0 : eichler Q u w0 v = v := by rw [hw0E]; exact hv0
  have hpvu : polar Q v u = 0 :=
    ((eichler_fix_iff hu hw0pol hu0 hwu0 v).mp hEfix0).1
  have hspan : ∀ z ∈ X ∪ {u}, polar Q z v = 0 := by
    intro z hz
    rcases hz with hzX | hzu
    · have hzpol : polar Q u z = 0 := hX z hzX
      have hgF : (toLinEquiv ι K).symm (eichler Q u z) ∈ F := hXF z hzX
      have hvz : toLinEquiv ι K ((toLinEquiv ι K).symm (eichler Q u z)) v = v := by
        rw [toLinEquiv_apply]
        exact hv _ hgF
      have hEfix : eichler Q u z v = v := by
        have hto : toLinEquiv ι K ((toLinEquiv ι K).symm (eichler Q u z)) = eichler Q u z :=
          MulEquiv.apply_symm_apply _ _
        rw [hto] at hvz
        exact hvz
      by_cases hzspan : z ∈ Submodule.span K {u}
      · obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hzspan
        rw [← hc, polar_smul_left_eq, polar_comm, hpvu, mul_zero]
      · have hwu : ∀ c : K, z ≠ c • u := by
          intro c hcz
          exact hzspan (Submodule.mem_span_singleton.mpr ⟨c, hcz.symm⟩)
        have h := ((eichler_fix_iff hu hzpol hu0 hwu v).mp hEfix).2
        rw [polar_comm]
        exact h
    · rw [Set.mem_singleton_iff] at hzu
      rw [hzu, polar_comm]
      exact hpvu
  intro y hy
  have hy' : y ∈ Submodule.span K (X ∪ {u}) := by rwa [hYX] at hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
      rw [polarBilin_apply_apply]
      exact hspan z hz
  | zero => simp
  | add x y hx hy ihx ihy =>
      rw [polarBilin_apply_apply] at ihx ihy
      rw [polarBilin_apply_apply, polar_add_left, ihx, ihy, add_zero]
  | smul a x hx ih =>
      rw [polarBilin_apply_apply] at ih
      rw [polarBilin_apply_apply, polar_smul_left_eq, ih, mul_zero]

theorem card_mul_card_fix_le_of_le_rootGroupGL {ι : Type} [Fintype ι] [DecidableEq ι] [Finite K]
    {Q : QuadraticForm K (ι → K)} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {u : ι → K}
    (hu : Q u = 0) (hu0 : u ≠ 0) {F : Subgroup (GL ι K)} (hF : F ≤ rootGroupGL Q u)
    (hF1 : F ≠ ⊥) :
    Nat.card ↥F * Nat.card {v : ι → K // ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} ≤
      Nat.card K ^ (Fintype.card ι - 1) := by
  classical
  let X : Set (ι → K) :=
    {w | polar Q u w = 0 ∧ (toLinEquiv ι K).symm (eichler Q u w) ∈ F}
  let Y : Submodule K (ι → K) := Submodule.span K (X ∪ {u})
  have hXpol : ∀ w ∈ X, polar Q u w = 0 := fun w hw => hw.1
  have hXF : ∀ w ∈ X, (toLinEquiv ι K).symm (eichler Q u w) ∈ F := fun w hw => hw.2
  have huY : u ∈ Y := Submodule.subset_span (by simp)
  have hXsubY : X ⊆ Y := fun w hw => Submodule.subset_span (by simp [hw])
  have hYX : Y = Submodule.span K (X ∪ {u}) := rfl
  have hcover : ∀ g ∈ F, ∃ w ∈ X, eichler Q u w = toLinEquiv ι K g := by
    intro g hg
    have hg' : (g : GL ι K) ∈ rootGroupGL Q u := hF hg
    rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hg'
    obtain ⟨w, hwpol, hwE⟩ := mem_rootGroup.mp hg'
    exact ⟨w, ⟨hwpol, by rw [hwE, MulEquiv.symm_apply_apply]; exact hg⟩, hwE⟩
  have hFcard : Nat.card ↥F ≤ Nat.card K ^ (Module.finrank K Y - 1) :=
    card_le_card_quotient_of_eichler_cover hu hu0 hXsubY huY hcover
  have hCsub : {v : ι → K | ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} ⊆
      (LinearMap.BilinForm.orthogonal (polarBilin Q) Y : Set (ι → K)) :=
    fixed_le_orthogonal_of_le_rootGroupGL hu hu0 hF hF1 hXpol hXF hYX
  have hcardOrth : Nat.card (LinearMap.BilinForm.orthogonal (polarBilin Q) Y) =
      Nat.card K ^ (Fintype.card ι - Module.finrank K Y) := by
    rw [Module.natCard_eq_pow_finrank (K := K)
        (V := ↥(LinearMap.BilinForm.orthogonal (polarBilin Q) Y)),
      LinearMap.BilinForm.finrank_orthogonal hQ, Module.finrank_fintype_fun_eq_card K]
  have hCcard :
      Nat.card {v : ι → K // ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} ≤
        Nat.card K ^ (Fintype.card ι - Module.finrank K Y) := by
    calc
      Nat.card {v : ι → K // ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} ≤
          Nat.card (LinearMap.BilinForm.orthogonal (polarBilin Q) Y) :=
        Nat.card_le_card_of_injective
          (fun v : {v : ι → K // ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} =>
            (⟨v.1, hCsub v.2⟩ :
              ↥(LinearMap.BilinForm.orthogonal (polarBilin Q) Y)))
          (fun v w h => Subtype.ext
            (congrArg (fun x : ↥(LinearMap.BilinForm.orthogonal (polarBilin Q) Y) =>
              (x : ι → K)) h))
      _ = Nat.card K ^ (Fintype.card ι - Module.finrank K Y) := hcardOrth
  have hd1 : 1 ≤ Module.finrank K Y := by
    refine Submodule.one_le_finrank_iff.mpr ?_
    intro hbot
    apply hu0
    have hu_bot : u ∈ (⊥ : Submodule K (ι → K)) := by rwa [hbot] at huY
    simpa using hu_bot
  have hdn : Module.finrank K Y ≤ Fintype.card ι := by
    have h := Submodule.finrank_le Y
    rwa [Module.finrank_fintype_fun_eq_card K] at h
  calc
    Nat.card ↥F * Nat.card {v : ι → K // ∀ g ∈ F, (g : Matrix ι ι K) *ᵥ v = v} ≤
        Nat.card K ^ (Module.finrank K Y - 1) *
          Nat.card K ^ (Fintype.card ι - Module.finrank K Y) := Nat.mul_le_mul hFcard hCcard
    _ = Nat.card K ^ ((Module.finrank K Y - 1) +
          (Fintype.card ι - Module.finrank K Y)) := by rw [pow_add]
    _ = Nat.card K ^ (Fintype.card ι - 1) := by
        congr 1
        omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
