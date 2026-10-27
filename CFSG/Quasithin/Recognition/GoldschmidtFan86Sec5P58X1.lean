module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P58Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P58

theorem x1abs (F : FanTree Γ G) (h40 : Fan40 F) {p₀ p v q q₂ : V} (hp₀p : Γ.Adj p₀ p)
    (hpv : Γ.Adj p v) (hvq : Γ.Adj v q) (hqq₂ : Γ.Adj q q₂) (hp₀v : p₀ ≠ v) (hpq : p ≠ q)
    (hvq₂ : v ≠ q₂) (hv3 : valence Γ v = 3) {z z' : G} (hz2 : z * z = 1) (hz'2 : z' * z' = 1)
    (hzp₀ : z • p₀ = p₀) (hzp : z • p = p) (hzv : z • v = v) (hzq : z • q ≠ q)
    (hzc : ∀ h : G, h • p₀ = p₀ → h • p = p → h * z = z * h)
    (hz'p : z' • p = p) (hz'v : z' • v = v) (hz'p₀ : z' • p₀ ≠ p₀)
    (hz'c : ∀ h : G, h • q = q → h • q₂ = q₂ → h * z' = z' * h)
    (hz'F : ∀ x : G, x • q = q → x • q₂ ≠ q₂ → x * z' ≠ z' * x) : False := by
  have hz0 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz'0 : z'⁻¹ = z' := inv_eq_of_mul_eq_one_right hz'2
  have hzKp : z ∈ nbrStab Γ G p := F.fix_two_nbrs hp₀p.symm hpv hp₀v hzp₀ hzv
  have hk1 : z' * z * z'⁻¹ ∈ nbrStab Γ G p := P58.conj_mem_nbrStab F hz'p hzKp
  have hcomm1 : z' * z * z'⁻¹ * z = z * (z' * z * z'⁻¹) :=
    hzc _ (mem_nbrStab.1 hk1 p₀ hp₀p.symm)
      (MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer p hk1))
  have hwc : z * z' * z * z' = z' * (z * z' * z) := by
    rw [hz'0] at hcomm1
    calc z * z' * z * z' = z * (z' * z * z') := by group
      _ = z' * z * z' * z := hcomm1.symm
      _ = z' * (z * z' * z) := by group
  obtain ⟨w, hw⟩ : ∃ w : G, w = z * z' * z := ⟨_, rfl⟩
  rw [← hw] at hwc
  have hwp : w • p = p := by rw [hw, mul_smul, mul_smul, hzp, hz'p, hzp]
  have hwv : w • v = v := by rw [hw, mul_smul, mul_smul, hzv, hz'v, hzv]
  have hwp₀ : w • p₀ ≠ p₀ := by
    have hadj : Γ.Adj p (z' • p₀) := by
      have := (F.adj_smul z' p p₀).2 hp₀p.symm
      rwa [hz'p] at this
    have h1 : z • z' • p₀ = z' • p₀ := mem_nbrStab.1 hzKp _ hadj
    rw [hw, mul_smul, mul_smul, hzp₀, h1]
    exact hz'p₀
  have hω : Γ.Adj v (z • q) := by
    have := (F.adj_smul z v q).2 hvq
    rwa [hzv] at this
  have hωp : p ≠ z • q := fun h => hpq (MulAction.injective z (hzp.trans h))
  obtain ⟨y, hyK, hyv, hyp, hyq⟩ :=
    P58.exists_swap F h40 hv3 hpv.symm hvq hω hpq hωp (fun h => hzq h.symm)
  have hKω : ∀ k ∈ nbrStab Γ G (z • q), k * w = w * k := by
    intro k hk
    have hkω : k • z • q = z • q :=
      MulAction.mem_stabilizer_iff.1 (F.nbrStab_le_stabilizer _ hk)
    have h1 : (z⁻¹ * k * z) • q = q := by rw [mul_smul, mul_smul, hkω, inv_smul_smul]
    have h2 : (z⁻¹ * k * z) • q₂ = q₂ := by
      have hadj : Γ.Adj (z • q) (z • q₂) := (F.adj_smul z q q₂).2 hqq₂
      rw [mul_smul, mul_smul, mem_nbrStab.1 hk _ hadj, inv_smul_smul]
    have hc := hz'c _ h1 h2
    rw [hz0] at hc
    rw [hw]
    calc k * (z * z' * z) = (z * z) * k * (z * z' * z) := by rw [hz2, one_mul]
      _ = z * (z * k * z * z') * z := by group
      _ = z * (z' * (z * k * z)) * z := by rw [hc]
      _ = (z * z') * z * k * (z * z) := by group
      _ = z * z' * z * k := by rw [hz2, mul_one]
  have hwq : w • q = q := by
    calc w • q = w • y • p := by rw [hyp]
      _ = (w * y) • p := by rw [mul_smul]
      _ = (y * w) • p := by rw [← hKω y hyK]
      _ = y • w • p := by rw [mul_smul]
      _ = q := by rw [hwp, hyp]
  have hwq₂ : w • q₂ ≠ q₂ := by
    intro hfix
    have hwKq : w ∈ nbrStab Γ G q := F.fix_two_nbrs hvq.symm hqq₂ hvq₂ hwv hfix
    have hadj : Γ.Adj q (y • p₀) := by
      have := (F.adj_smul y p p₀).2 hp₀p.symm
      rwa [hyp] at this
    have h1 := mem_nbrStab.1 hwKq _ hadj
    have h2 : w • y • p₀ = y • w • p₀ := by
      rw [← mul_smul, ← mul_smul, hKω y hyK]
    exact hwp₀ (MulAction.injective y (h2.symm.trans h1))
  exact hz'F w hwq hwq₂ hwc

end P58

end CFSG.Quasithin.Fan86
