module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Shift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P57Mech

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P58

theorem x3abs (F : FanTree Γ G) (h40 : Fan40 F) {p₀ p v q q₂ q₃ : V} (hp₀p : Γ.Adj p₀ p)
    (hpv : Γ.Adj p v) (hvq : Γ.Adj v q) (hqq₂ : Γ.Adj q q₂) (hq₂q₃ : Γ.Adj q₂ q₃)
    (hp₀v : p₀ ≠ v) (hpq : p ≠ q) (hvq₂ : v ≠ q₂) (hqq₃ : q ≠ q₃) (hv3 : valence Γ v = 3)
    {z z' : G} (hz2 : z * z = 1) (hz'2 : z' * z' = 1)
    (hzp₀ : z • p₀ = p₀) (hzp : z • p = p) (hzv : z • v = v) (hzq : z • q = q)
    (hzq₂ : z • q₂ ≠ q₂) (hzc : ∀ h : G, h • p₀ = p₀ → h • p = p → h * z = z * h)
    (hzF : ∀ x : G, x • p = p → x • p₀ ≠ p₀ → x * z ≠ z * x)
    (hz'v : z' • v = v) (hz'q : z' • q = q) (hz'q₂ : z' • q₂ = q₂) (hz'q₃ : z' • q₃ = q₃)
    (hz'p : z' • p ≠ p) (hz'c : ∀ h : G, h • q₂ = q₂ → h • q₃ = q₃ → h * z' = z' * h) :
    ∃ u : G, u ≠ 1 ∧ u * u = 1 ∧ u • v = v ∧ u • q = q ∧
      (∀ g : G, g • p = p → g • v = v → (g * g ∈ nbrStab Γ G p ∨ valence Γ p = 3) →
        g * u = u * g) ∧
      (∀ g : G, g • q = q → g • q₂ = q₂ → valence Γ q₂ = 3 → g * u = u * g) := by
  have hz0 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz'0 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  have hzKp : z ∈ nbrStab Γ G p := F.fix_two_nbrs hp₀p.symm hpv hp₀v hzp₀ hzv
  have hz'Kq : z' ∈ nbrStab Γ G q := F.fix_two_nbrs hvq.symm hqq₂ hvq₂ hz'v hz'q₂
  have hz'Kq₂ : z' ∈ nbrStab Γ G q₂ := F.fix_two_nbrs hqq₂.symm hq₂q₃ hqq₃ hz'q hz'q₃
  have hzKv : z ∈ nbrStab Γ G v := F.fix_two_nbrs hpv.symm hvq hpq hzp hzq
  obtain ⟨w₁, hw₁⟩ : ∃ w₁ : G, w₁ = z' * z * z' := ⟨_, rfl⟩
  have hw₁2 : w₁ * w₁ = 1 := by
    have := P55.sq_conj z' hz2
    rw [hz'0] at this
    rwa [hw₁]
  have hw₁0 : w₁⁻¹ = w₁ := inv_eq_of_mul_eq_one_right hw₁2
  have hw₁Kv : w₁ ∈ nbrStab Γ G v := by
    have := P58.conj_mem_nbrStab F hz'v hzKv
    rwa [hz'0, ← hw₁] at this
  have hw₁p : w₁ • p = p := mem_nbrStab.1 hw₁Kv p hpv.symm
  have hw₁v : w₁ • v = v := MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer v hw₁Kv)
  have hw₁q : w₁ • q = q := mem_nbrStab.1 hw₁Kv q hvq
  have hα' : Γ.Adj v (z' • p) := by
    have := (F.adj_smul z' v p).2 hpv.symm
    rwa [hz'v] at this
  have hpα' : p ≠ z' • p := fun h => hz'p h.symm
  have hqα' : q ≠ z' • p := fun h => hpq (MulAction.injective z' (h.symm.trans hz'q.symm))
  have hKα' : ∀ k ∈ nbrStab Γ G (z' • p), k * w₁ = w₁ * k := by
    intro k hk
    have hkα : k • z' • p = z' • p :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hk)
    have h1 : (z'⁻¹ * k * z') • p = p := by rw [mul_smul, mul_smul, hkα, inv_smul_smul]
    have h2 : (z'⁻¹ * k * z') • p₀ = p₀ := by
      have hadj : Γ.Adj (z' • p) (z' • p₀) := (F.adj_smul z' p p₀).2 hp₀p.symm
      rw [mul_smul, mul_smul, mem_nbrStab.1 hk _ hadj, inv_smul_smul]
    have hc := hzc _ h2 h1
    rw [hz'0] at hc
    rw [hw₁]
    calc k * (z' * z * z') = (z' * z') * k * (z' * z * z') := by rw [hz'2, one_mul]
      _ = z' * (z' * k * z' * z) * z' := by group
      _ = z' * (z * (z' * k * z')) * z' := by rw [hc]
      _ = z' * z * z' * k * (z' * z') := by group
      _ = z' * z * z' * k := by rw [hz'2, mul_one]
  have hw₁K : w₁ ∉ nbrStab Γ G p := by
    intro hKp
    obtain ⟨y, hyK, hyv, hyp, hyq⟩ :=
      P58.exists_swap F h40 hv3 hpv.symm hvq hα' hpq hpα' hqα'
    have hyc : y * w₁ = w₁ * y := hKα' y hyK
    have hw₁Kq : w₁ ∈ nbrStab Γ G q := by
      have := (F.mem_nbrStab_smul_iff y p (h := w₁)).2 (by
        rw [show y⁻¹ * w₁ * y = w₁ by rw [mul_assoc, ← hyc, ← mul_assoc, inv_mul_cancel, one_mul]]
        exact hKp)
      rwa [hyp] at this
    have hadj : Γ.Adj q (z • q₂) := by
      have := (F.adj_smul z q q₂).2 hqq₂
      rwa [hzq] at this
    have h1 : w₁ • q₂ = z • q₂ := by
      rw [hw₁, mul_smul, mul_smul, hz'q₂]
      exact mem_nbrStab.1 hz'Kq _ hadj
    exact hzq₂ (h1.symm.trans (mem_nbrStab.1 hw₁Kq q₂ hqq₂))
  have hmech₁ := P57.mech F hp₀p.symm hpv hz2 hw₁2 hzKp hzc hw₁p hw₁v hw₁K
  obtain ⟨u, hu⟩ : ∃ u : G, u = z * z' * z * z' * z * z' * z * z' := ⟨_, rfl⟩
  have hu₁ : z * (w₁ * z * w₁⁻¹) = u := by
    rw [hw₁0, hu, hw₁]
    group
  have hu₁2 : u * u = 1 := by
    have := hmech₁.1
    rwa [hu₁] at this
  have hw₁p₀ : w₁ • p₀ ≠ p₀ := fun h => hw₁K (F.fix_two_nbrs hp₀p.symm hpv hp₀v h hw₁v)
  have hnc : w₁ * z ≠ z * w₁ := hzF w₁ hw₁p hw₁p₀
  have hu1 : u ≠ 1 := by
    intro hu'
    apply hnc
    rw [← hu₁, hw₁0] at hu'
    have h2 : z * w₁ * (z * w₁) = 1 := by simpa [mul_assoc] using hu'
    have h3 := inv_eq_of_mul_eq_one_right h2
    rw [mul_inv_rev, hw₁0, hz0] at h3
    exact h3
  obtain ⟨w₂, hw₂⟩ : ∃ w₂ : G, w₂ = z * z' * z := ⟨_, rfl⟩
  have hw₂2 : w₂ * w₂ = 1 := by
    have := P55.sq_conj z hz'2
    rw [hz0] at this
    rwa [hw₂]
  have hw₂0 : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hw₂2
  have hw₂q : w₂ • q = q := by rw [hw₂, mul_smul, mul_smul, hzq, hz'q, hzq]
  have hw₂q₂ : w₂ • q₂ = q₂ := by
    have hadj : Γ.Adj q (z • q₂) := by
      have := (F.adj_smul z q q₂).2 hqq₂
      rwa [hzq] at this
    have h1 : z' • z • q₂ = z • q₂ := mem_nbrStab.1 hz'Kq _ hadj
    rw [hw₂, mul_smul, mul_smul, h1, ← mul_smul, hz2, one_smul]
  have hw₂K : w₂ ∉ nbrStab Γ G q₂ := by
    intro hK
    have hc := hz'c w₂ hw₂q₂ (mem_nbrStab.1 hK q₃ hq₂q₃)
    apply hu1
    have h1 : u = w₂ * z' * (w₂ * z') := by rw [hu, hw₂]; group
    rw [h1]
    calc w₂ * z' * (w₂ * z') = w₂ * (z' * w₂) * z' := by group
      _ = w₂ * (w₂ * z') * z' := by rw [hc]
      _ = (w₂ * w₂) * (z' * z') := by group
      _ = 1 := by rw [hw₂2, hz'2, one_mul]
  have hmech₂ := P57.mech F hq₂q₃ hqq₂.symm hz'2 hw₂2 hz'Kq₂ (fun h h1 h2 => hz'c h h2 h1)
    hw₂q₂ hw₂q hw₂K
  have hu₂ : z' * (w₂ * z' * w₂⁻¹) = u := by
    have h1 : z' * (w₂ * z' * w₂⁻¹) = u⁻¹ := by
      rw [hw₂0, hu, hw₂]
      simp only [mul_inv_rev, hz0, hz'0, mul_assoc]
    rw [h1]
    exact inv_eq_of_mul_eq_one_right hu₁2
  refine ⟨u, hu1, hu₁2, ?_, ?_, ?_, ?_⟩
  · rw [hu]
    simp only [mul_smul, hzv, hz'v]
  · rw [hu]
    simp only [mul_smul, hzq, hz'q]
  · intro g hgp hgv hg
    have := hmech₁.2 g hgp hgv hg
    rwa [hu₁] at this
  · intro g hgq hgq₂ hg3
    have := hmech₂.2 g hgq₂ hgq (Or.inr hg3)
    rwa [hu₂] at this

end P58

end CFSG.Quasithin.Fan86
