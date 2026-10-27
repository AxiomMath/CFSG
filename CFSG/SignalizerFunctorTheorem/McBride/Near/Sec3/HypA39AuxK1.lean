module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210jAuxK
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.HypA39AuxRed2

public section

open CFSG.Open
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
open scoped Pointwise commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {Γ : Type u} [Group Γ] {p : ℕ} {H A D D₁ D₂ E L R : Subgroup Γ}

namespace Red

theorem A_cen_DA (c : Red p H A D D₁ D₂ E L R) {e : Γ} (heA : e ∈ A) :
    ∀ t ∈ D ⊔ A, e * t = t * e := by
  intro t ht
  obtain ⟨d, hd, a, ha, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' (S := D) (X := A)
    (le_sup_right.trans c.h15.admits_D)).mp ht
  have h1 : e * d = d * e := Subgroup.mem_centralizer_iff.mp (c.h15.D_le_centralizer hd) e heA
  have h2 : e * a = a * e := (commute_of_mem c.h15.a1_elemAbelian.1 heA ha).eq
  rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem comm_mem_of_cen (c : Red p H A D D₁ D₂ E L R) {K K₁ : Subgroup Γ}
    (hK₁ : Admits (H ⊔ A) K₁) (hK₁D : K₁ ⊔ D₁ = R) {e : Γ} (heA : e ∈ A)
    (hcen : ∀ x ∈ K₁, ⁅e, x⁆ ∈ K) : ∀ g ∈ H ⊔ A, ⁅e, g⁆ ∈ K := by
  intro g hg
  have hG : H ⊔ A = K₁ ⊔ (D ⊔ A) := by
    rw [← c.G_eq, ← hK₁D]
    apply le_antisymm
    · refine sup_le (sup_le (sup_le le_sup_left ?_) ?_) ?_
      · exact c.D₁_le_D.trans (le_sup_left.trans le_sup_right)
      · exact le_sup_left.trans le_sup_right
      · exact le_sup_right.trans le_sup_right
    · refine sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) (sup_le ?_ ?_)
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
  rw [hG] at hg
  have hDAK : D ⊔ A ≤ Subgroup.normalizer (K₁ : Set Γ) := c.DA_le_G.trans hK₁
  obtain ⟨k, hk, t, ht, rfl⟩ := (mem_sup_iff_mul_of_le_normalizer' hDAK).mp hg
  have h1 : Commute t e := (c.A_cen_DA heA t ht).symm
  have h2 : t * e⁻¹ * t⁻¹ = e⁻¹ := by
    rw [h1.inv_right.eq, mul_assoc, mul_inv_cancel, mul_one]
  have : ⁅e, k * t⁆ = ⁅e, k⁆ := by
    calc ⁅e, k * t⁆ = e * k * (t * e⁻¹ * t⁻¹) * k⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅e, k⁆ := by rw [h2]; rfl
  rw [this]
  exact hcen k hk

theorem eq_one_of_cen [Finite Γ] (c : Red p H A D D₁ D₂ E L R) {K K₁ : Subgroup Γ}
    (hK : Admits (H ⊔ A) K) (hKab : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hKR : K ≤ R)
    (hK₁ : Admits (H ⊔ A) K₁) (hK₁R : K₁ ≤ R) (hK₁D : K₁ ⊔ D₁ = R)
    {e : Γ} (he : e ∈ E) (hcen : ∀ x ∈ K₁, ⁅e, x⁆ ∈ K) : e = 1 := by
  by_contra he1
  have heA : e ∈ A := c.hEA he
  have hall := c.comm_mem_of_cen hK₁ hK₁D heA hcen
  have heG : e ∈ H ⊔ A := Subgroup.mem_sup_right heA
  set Z : Subgroup Γ := Subgroup.zpowers e with hZ
  have hZK : Z ≤ Subgroup.normalizer (K : Set Γ) := Subgroup.zpowers_le.mpr (hK heG)
  have hKT : ∀ g ∈ H ⊔ A, g * e * g⁻¹ ∈ K ⊔ Z := by
    intro g hg
    have h1 : ⁅g, e⁆ ∈ K := by
      rw [← commutatorElement_inv]
      exact inv_mem (hall g hg)
    have : g * e * g⁻¹ = ⁅g, e⁆ * e := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
  have hZconj : ∀ g ∈ H ⊔ A, ∀ z ∈ Z, ∃ k ∈ K, ∃ z' ∈ Z, g * z * g⁻¹ = k * z' := by
    intro g hg z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have : g * e ^ n * g⁻¹ ∈ K ⊔ Z := by
      rw [← conj_zpow]
      exact zpow_mem (hKT g hg) n
    obtain ⟨k, hk, z', hz', h⟩ := (mem_sup_iff_mul_of_le_normalizer' hZK).mp this
    exact ⟨k, hk, z', hz', h⟩
  have hid : ∀ k₀ ∈ K, ∀ k ∈ K, ∀ z' ∈ Z, ⁅k₀, k * z'⁆ = ⁅k₀, z'⁆ := by
    intro k₀ hk₀ k hk z' hz'
    have hz'K : z' * k₀⁻¹ * z'⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hZK hz') k₀⁻¹).mp (inv_mem hk₀)
    have h1 : ⁅k₀, z'⁆ ∈ K := by
      have : ⁅k₀, z'⁆ = k₀ * (z' * k₀⁻¹ * z'⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact mul_mem hk₀ hz'K
    have hkk : k₀ * k = k * k₀ := hKab k₀ hk₀ k hk
    calc ⁅k₀, k * z'⁆ = k * ⁅k₀, z'⁆ * k⁻¹ := by
          calc ⁅k₀, k * z'⁆ = (k₀ * k) * z' * k₀⁻¹ * z'⁻¹ * k⁻¹ := by
                simp only [commutatorElement_def]
                group
            _ = (k * k₀) * z' * k₀⁻¹ * z'⁻¹ * k⁻¹ := by rw [hkk]
            _ = k * ⁅k₀, z'⁆ * k⁻¹ := by
                simp only [commutatorElement_def]
                group
      _ = ⁅k₀, z'⁆ := by
          have := hKab k hk _ h1
          rw [this, mul_assoc, mul_inv_cancel, mul_one]
  have hWadm : Admits (H ⊔ A) ⁅K, Z⁆ := by
    rw [Subgroup.commutator_def]
    refine admits_closure fun g hg w hw => ?_
    obtain ⟨k₀, hk₀, z, hz, rfl⟩ := hw
    obtain ⟨k, hk, z', hz', hgz⟩ := hZconj g hg z hz
    refine ⟨g * k₀ * g⁻¹, hK.conj_mem hg hk₀, z', hz', ?_⟩
    have : g * ⁅k₀, z⁆ * g⁻¹ = ⁅g * k₀ * g⁻¹, g * z * g⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this, hgz, hid _ (hK.conj_mem hg hk₀) k hk z' hz']
  have hWK : ⁅K, Z⁆ ≤ K := Thm210.commutator_le_of_normalizes hZK
  have : IsMulCommutative K := ⟨⟨fun a b => Subtype.ext (hKab a a.2 b b.2)⟩⟩
  have hZe : IsElemAbelian p Z := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have := c.h15.a1_elemAbelian.2 e heA
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, this, one_zpow]
  have hZp : IsPGroup p Z := HypAAux.isPGroup_of_isElemAbelian hZe
  have hZA : Z ≤ A := Subgroup.zpowers_le.mpr heA
  have hDZ : D ≤ Subgroup.centralizer (Z : Set Γ) :=
    c.h15.D_le_centralizer.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZA))
  have hKH : K ≤ H := hKR.trans c.R_le_H
  have hK₁H : K₁ ≤ H := hK₁R.trans c.R_le_H
  have hFit := Thm210.commutator_inf_centralizer_eq_bot (R := K) (A := Z) c.h15.prime hZK hZp
    (c.h15.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hKH))
  have hWD : ⁅K, Z⁆ ⊓ D ≤ D₂ :=
    ((inf_le_inf_left _ hDZ).trans hFit.le).trans bot_le
  have hW0 : ⁅K, Z⁆ = ⊥ := c.eq_bot_of_normal (hWK.trans hKH) hWadm hWD
  have hKC : K ≤ Subgroup.centralizer (Z : Set Γ) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hW0
  have hesec : e ∈ McBride.sectionCentralizer K K₁ :=
    McBride.mem_sectionCentralizer_iff.mpr ⟨hK heG, hK₁ heG, hcen⟩
  have hZsec : Z ≤ McBride.sectionCentralizer K K₁ := Subgroup.zpowers_le.mpr hesec
  have hK₁Z : Z ≤ Subgroup.normalizer (K₁ : Set Γ) := fun z hz =>
    (McBride.mem_sectionCentralizer_iff.mp (hZsec hz)).2.1
  have hK₁comm : ⁅K₁, Z⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx z hz => by
    have := (McBride.mem_sectionCentralizer_iff.mp (hZsec hz)).2.2 x hx
    rw [← commutatorElement_inv]
    exact inv_mem this
  have hidem := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent p
    c.h15.prime Z K₁ hZp hK₁Z (c.h15.coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK₁H))
  have hK₁0 : ⁅K₁, Z⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅K₁, Z⁆ = ⁅⁅K₁, Z⁆, Z⁆ := hidem.symm
      _ ≤ ⁅K, Z⁆ := Subgroup.commutator_mono hK₁comm le_rfl
      _ = ⊥ := hW0
  have hK₁C : K₁ ≤ Subgroup.centralizer {e} := by
    rw [← HypAAux.centralizer_zpowers_eq e]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hK₁0
  have hDC : D ≤ Subgroup.centralizer {e} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (c.h15.D_le_centralizer hx) e heA).symm
  have hHC : H ≤ Subgroup.centralizer {e} := by
    rw [c.hHR, ← hK₁D]
    exact sup_le (sup_le hK₁C (c.D₁_le_D.trans hDC)) hDC
  have h6 := c.h6 e he he1
  rw [inf_eq_left.mpr hHC] at h6
  exact c.noB (c.hasB_of_hypA6 h6 c.R_le_H c.L_le_R le_rfl c.admits_R c.hRD)

end Red

end CFSG.SignalizerFunctorTheorem.McBride.Near
