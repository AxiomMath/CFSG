module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartOne.KLC

open MulAction
open scoped commutatorElement

section CommSubgroup

variable {A : Type*} [Group A]

@[expose] def commModSubgroup (N : Subgroup A) [N.Normal] (α : A) : Subgroup A where
  carrier := {γ | ⁅γ, α⁆ ∈ N}
  mul_mem' {a b} ha hb := by
    have e : ⁅a * b, α⁆ = a * ⁅b, α⁆ * a⁻¹ * ⁅a, α⁆ := by
      simp only [commutatorElement_def]
      group
    change ⁅a * b, α⁆ ∈ N
    rw [e]
    exact N.mul_mem (Subgroup.Normal.conj_mem ‹N.Normal› _ hb a) ha
  one_mem' := by
    change ⁅(1 : A), α⁆ ∈ N
    simp
  inv_mem' {a} ha := by
    have e : ⁅a⁻¹, α⁆ = a⁻¹ * ⁅a, α⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    change ⁅a⁻¹, α⁆ ∈ N
    rw [e]
    have := Subgroup.Normal.conj_mem ‹N.Normal› _ (N.inv_mem ha) a⁻¹
    simpa using this

end CommSubgroup

section ThreePoint

variable {A : Type*} [Group A] {X : Type*} [MulAction A X]

theorem smul_orbit_of_normal {N : Subgroup A} [N.Normal] {F : X} (hN : ∀ n ∈ N, n • F = F)
    {n : A} (hn : n ∈ N) (a : A) : n • (a • F) = a • F := by
  have h1 : (a⁻¹ * n * a) • F = F := hN _ (by
    simpa using Subgroup.Normal.conj_mem ‹N.Normal› n hn a⁻¹)
  calc n • (a • F) = a • ((a⁻¹ * n * a) • F) := by
        rw [smul_smul, smul_smul]
        simp [mul_assoc]
    _ = a • F := by rw [h1]

theorem smul_eq_of_pow_fixes {S : Finset X} (hS : S.card ≤ 3) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {α : A} {x : X} (hx : ∀ k : ℕ, α ^ k • x ∈ S)
    (hpx : ∀ k : ℕ, α ^ p • (α ^ k • x) = α ^ k • x) : α • x = x := by
  classical
  obtain ⟨i, hi, j, hj, hij, hxij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range 4) (t := S) (f := fun k : ℕ => α ^ k • x)
    (by simpa using lt_of_le_of_lt hS (by norm_num)) (fun k _ => by simpa using hx k)
  have key : ∀ i j : ℕ, i < j → j < 4 → α ^ i • x = α ^ j • x → α • x = x := by
    intro i j hlt hj4 h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hm : α ^ (m + 1) • (α ^ i • x) = α ^ i • x := by
      rw [smul_smul, ← pow_add]
      have : m + 1 + i = i + m + 1 := by omega
      rw [this]
      exact h.symm
    have hcop : Nat.Coprime (m + 1) p := by
      refine (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_))
      have := Nat.le_of_dvd (by omega) hd
      omega
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ((m + 1 : ℕ) : ℤ) + v * (p : ℤ) = 1 := by
      have hg : Int.gcd ((m + 1 : ℕ) : ℤ) (p : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact hcop
      have h := Int.gcd_eq_gcd_ab ((m + 1 : ℕ) : ℤ) (p : ℤ)
      rw [hg] at h
      exact ⟨Int.gcdA _ _, Int.gcdB _ _, by push_cast at h ⊢; linarith⟩
    have hstab : α ∈ stabilizer A (α ^ i • x) := by
      have h1 : α ^ (m + 1) ∈ stabilizer A (α ^ i • x) := hm
      have h2 : α ^ p ∈ stabilizer A (α ^ i • x) := hpx i
      have : α = (α ^ (m + 1)) ^ u * (α ^ p) ^ v := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
        have : ((m + 1 : ℕ) : ℤ) * u + (p : ℤ) * v = 1 := by linarith
        rw [this, zpow_one]
      have hmem : (α ^ (m + 1)) ^ u * (α ^ p) ^ v ∈ stabilizer A (α ^ i • x) :=
        (stabilizer A (α ^ i • x)).mul_mem ((stabilizer A (α ^ i • x)).zpow_mem h1 u)
          ((stabilizer A (α ^ i • x)).zpow_mem h2 v)
      rwa [← this] at hmem
    have hfix : α • (α ^ i • x) = α ^ i • x := hstab
    have h3 : α ^ i • (α • x) = α ^ i • x :=
      calc α ^ i • (α • x) = (α ^ i * α) • x := smul_smul _ _ _
        _ = (α * α ^ i) • x := by rw [← pow_succ, pow_succ']
        _ = α • (α ^ i • x) := (smul_smul _ _ _).symm
        _ = α ^ i • x := hfix
    exact smul_left_cancel (α ^ i) h3
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (by simpa using hj) hxij
  · exact key j i h (by simpa using hi) hxij.symm

theorem commutator_mem_of_three_point_orbit (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hN : ∀ n ∈ N, n • F = F)
    (hE : ∀ a b : A, a • F = F → b • F = F → ⁅a, b⁆ ∈ N)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {α : A} (hα : α ^ p ∈ N) (γ : A) : ⁅γ, α⁆ ∈ N := by
  classical
  have hfix : ∀ a : A, α • (a • F) = a • F := by
    intro a
    have hcard : ({F, y, z} : Finset X).card ≤ 3 := Finset.card_le_three
    refine smul_eq_of_pow_fixes (S := {F, y, z}) hcard hp hp5 (fun k => ?_) (fun k => ?_)
    · rw [smul_smul]
      have := hO (α ^ k * a)
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    · simpa [mul_smul] using smul_orbit_of_normal hN hα (α ^ k * a)
  have hstab : ∀ a γ : A, γ • (a • F) = a • F → ⁅γ, α⁆ ∈ N := by
    intro a γ hγ
    have h1 : (a⁻¹ * γ * a) • F = F := by
      calc (a⁻¹ * γ * a) • F = a⁻¹ • (γ • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hγ]
        _ = F := inv_smul_smul a F
    have h2 : (a⁻¹ * α * a) • F = F := by
      calc (a⁻¹ * α * a) • F = a⁻¹ • (α • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hfix a]
        _ = F := inv_smul_smul a F
    have h3 := hE _ _ h1 h2
    have e : ⁅a⁻¹ * γ * a, a⁻¹ * α * a⁆ = a⁻¹ * ⁅γ, α⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e] at h3
    have h4 := Subgroup.Normal.conj_mem ‹N.Normal› _ h3 a
    have e2 : a * (a⁻¹ * ⁅γ, α⁆ * a) * a⁻¹ = ⁅γ, α⁆ := by group
    rwa [e2] at h4
  set S := commModSubgroup N α with hS
  have hSstab : ∀ a γ : A, γ • (a • F) = a • F → γ ∈ S := fun a γ h => hstab a γ h
  have hFy : F ≠ y := by
    intro h
    apply hyz
    have h1 : κ • y = y := by rw [← h, hκF]
    rw [← h1, hκy]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    have h1 : κ • z = z := by rw [← h, hκF]
    rw [← hκz, h1]
  have hz : ∀ γ₁ : A, γ₁ • F = y → ∃ s ∈ S, s • F = z := by
    intro γ₁ hγ₁
    have hκ₁ : (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • F := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • (κ • F) := by simp [mul_smul]
        _ = γ₁ • F := by rw [hκF]
    refine ⟨γ₁ * κ * γ₁⁻¹, hSstab γ₁ _ hκ₁, ?_⟩
    have hu : γ₁ • y = F ∨ γ₁ • y = y ∨ γ₁ • y = z := by
      have := hO (γ₁ * γ₁)
      rwa [mul_smul, hγ₁] at this
    have hv : γ₁ • z = F ∨ γ₁ • z = y ∨ γ₁ • z = z := by
      have := hO (γ₁ * (κ * γ₁))
      rwa [mul_smul, mul_smul, hγ₁, hκy] at this
    have hu_y : γ₁ • y ≠ y := fun h =>
      hFy (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have hv_y : γ₁ • z ≠ y := fun h =>
      hFz (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have huv : γ₁ • y ≠ γ₁ • z := fun h => hyz (smul_left_cancel γ₁ h)
    have hκu : (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • z := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • (κ • y) := by simp [mul_smul]
        _ = γ₁ • z := by rw [hκy]
    have hκv : (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • y := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • (κ • z) := by simp [mul_smul]
        _ = γ₁ • y := by rw [hκz]
    rcases hu with hu | hu | hu
    · have hvz : γ₁ • z = z := by
        rcases hv with hv | hv | hv
        · exact absurd (hu.trans hv.symm) huv
        · exact absurd hv hv_y
        · exact hv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) := by rw [hu]
        _ = γ₁ • z := hκu
        _ = z := hvz
    · exact absurd hu hu_y
    · have hvF : γ₁ • z = F := by
        rcases hv with hv | hv | hv
        · exact hv
        · exact absurd hv hv_y
        · exact absurd (hu.trans hv.symm) huv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) := by rw [hvF]
        _ = γ₁ • y := hκv
        _ = z := hu
  have hκS : κ ∈ S := hSstab 1 κ (by simpa using hκF)
  rcases hO γ with h | h | h
  · exact hSstab 1 γ (by simpa using h)
  · obtain ⟨s, hs, hsF⟩ := hz γ h
    have hksF : (κ * s) • F = y := by rw [mul_smul, hsF, hκz]
    have h1 : ((κ * s)⁻¹ * γ) • F = F := by
      calc ((κ * s)⁻¹ * γ) • F = (κ * s)⁻¹ • (γ • F) := mul_smul _ _ _
        _ = (κ * s)⁻¹ • ((κ * s) • F) := by rw [h, hksF]
        _ = F := inv_smul_smul _ _
    have h2 : (κ * s)⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem (S.mul_mem hκS hs) h2
    have e3 : κ * s * ((κ * s)⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3
  · obtain ⟨s, hs, hsF⟩ := hz (κ * γ) (by rw [mul_smul, h, hκz])
    have h1 : (s⁻¹ * γ) • F = F := by
      calc (s⁻¹ * γ) • F = s⁻¹ • (γ • F) := mul_smul _ _ _
        _ = s⁻¹ • (s • F) := by rw [h, hsF]
        _ = F := inv_smul_smul _ _
    have h2 : s⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem hs h2
    have e3 : s * (s⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3

end ThreePoint

section Index

variable {A : Type*} [Group A]

theorem commutator_mem_of_relIndex_le_two [Finite A] (N D : Subgroup A) [N.Normal] (hND : N ≤ D)
    (hidx : N.relIndex D ≤ 2) {e d : A} (hd : d ∈ D) (hed : e * d * e⁻¹ ∈ D) : ⁅e, d⁆ ∈ N := by
  classical
  have hND' : ∀ x : A, x ∈ N → x ∈ D := fun x hx => hND hx
  set N' := N.subgroupOf D with hN'
  have hfinD : Finite D := inferInstance
  have hfin : Finite (D ⧸ N') := inferInstance
  have : Fintype (D ⧸ N') := Fintype.ofFinite _
  have hcard : Fintype.card (D ⧸ N') ≤ 2 := by
    rw [← Nat.card_eq_fintype_card]
    have : N.relIndex D = Nat.card (D ⧸ N') := rfl
    omega
  have hmem : ∀ x : A, ∀ hx : x ∈ D, ((QuotientGroup.mk ⟨x, hx⟩ : D ⧸ N') = 1 ↔ x ∈ N) := by
    intro x hx
    rw [QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf]
  have hconj : ∀ x ∈ N, e * x * e⁻¹ ∈ N := fun x hx => Subgroup.Normal.conj_mem ‹N.Normal› x hx e
  by_cases hx : (QuotientGroup.mk ⟨d, hd⟩ : D ⧸ N') = 1
  · have hdN : d ∈ N := (hmem d hd).1 hx
    have h1 : e * d * e⁻¹ * d⁻¹ ∈ N := N.mul_mem (hconj d hdN) (N.inv_mem hdN)
    exact h1
  · have hx' : (QuotientGroup.mk ⟨e * d * e⁻¹, hed⟩ : D ⧸ N') ≠ 1 := by
      intro h
      apply hx
      rw [hmem _ hed] at h
      rw [hmem d hd]
      have := Subgroup.Normal.conj_mem ‹N.Normal› _ h e⁻¹
      simpa [mul_assoc] using this
    have hxx : (QuotientGroup.mk ⟨e * d * e⁻¹, hed⟩ : D ⧸ N') = QuotientGroup.mk ⟨d, hd⟩ := by
      by_contra hne
      have h3 : ({1, QuotientGroup.mk ⟨d, hd⟩, QuotientGroup.mk ⟨e * d * e⁻¹, hed⟩} :
          Finset (D ⧸ N')).card = 3 := by
        refine Finset.card_eq_three.2 ⟨1, QuotientGroup.mk ⟨d, hd⟩,
          QuotientGroup.mk ⟨e * d * e⁻¹, hed⟩, Ne.symm hx, Ne.symm hx', fun h => hne h.symm, rfl⟩
      have h4 := Finset.card_le_univ ({1, QuotientGroup.mk ⟨d, hd⟩,
        QuotientGroup.mk ⟨e * d * e⁻¹, hed⟩} : Finset (D ⧸ N'))
      omega
    have h5 := (QuotientGroup.eq.1 hxx.symm)
    rw [hN', Subgroup.mem_subgroupOf] at h5
    have h6 : d⁻¹ * (e * d * e⁻¹) ∈ N := by simpa using h5
    have h7 := Subgroup.Normal.conj_mem ‹N.Normal› _ h6 d
    have e1 : d * (d⁻¹ * (e * d * e⁻¹)) * d⁻¹ = e * d * e⁻¹ * d⁻¹ := by group
    rw [e1] at h7
    exact h7

theorem commutator_mem_of_cyclic_quotient (N : Subgroup A) [N.Normal] (E D : Subgroup A)
    (hDE : D ≤ E) {u : A} (hu : u ∈ E) (hcyc : ∀ e ∈ E, ∃ k : ℤ, u ^ k * e ∈ D)
    (hcentral : ∀ e ∈ E, ∀ d ∈ D, ⁅e, d⁆ ∈ N) : ∀ a ∈ E, ∀ b ∈ E, ⁅a, b⁆ ∈ N := by
  intro a ha b hb
  let π : A →* A ⧸ N := QuotientGroup.mk' N
  have hcomm : ∀ e ∈ E, ∀ d ∈ D, π d * π e = π e * π d := by
    intro e he d hd
    have h := hcentral e he d hd
    have h1 : π ⁅e, d⁆ = 1 := (QuotientGroup.eq_one_iff _).2 h
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  obtain ⟨k₁, hk₁⟩ := hcyc a ha
  obtain ⟨k₂, hk₂⟩ := hcyc b hb
  set da := u ^ k₁ * a with hda
  set db := u ^ k₂ * b with hdb
  have haeq : a = u ^ (-k₁) * da := by rw [hda, zpow_neg]; group
  have hbeq : b = u ^ (-k₂) * db := by rw [hdb, zpow_neg]; group
  have hU₁ : u ^ (-k₁) ∈ E := E.zpow_mem hu _
  have hU₂ : u ^ (-k₂) ∈ E := E.zpow_mem hu _
  have hda1 : π da * π (u ^ (-k₂)) = π (u ^ (-k₂)) * π da := hcomm _ hU₂ _ hk₁
  have hdb1 : π db * π (u ^ (-k₁)) = π (u ^ (-k₁)) * π db := hcomm _ hU₁ _ hk₂
  have hdd : π da * π db = π db * π da := hcomm _ (hDE hk₂) _ hk₁
  have huu : π (u ^ (-k₁)) * π (u ^ (-k₂)) = π (u ^ (-k₂)) * π (u ^ (-k₁)) := by
    rw [← map_mul, ← map_mul, ← zpow_add, ← zpow_add, add_comm]
  have hab : π a * π b = π b * π a := by
    rw [haeq, hbeq, map_mul, map_mul, map_mul, map_mul]
    calc π (u ^ (-k₁)) * π da * (π (u ^ (-k₂)) * π db)
        = π (u ^ (-k₁)) * (π da * π (u ^ (-k₂))) * π db := by group
      _ = π (u ^ (-k₁)) * (π (u ^ (-k₂)) * π da) * π db := by rw [hda1]
      _ = (π (u ^ (-k₁)) * π (u ^ (-k₂))) * (π da * π db) := by group
      _ = (π (u ^ (-k₂)) * π (u ^ (-k₁))) * (π db * π da) := by rw [huu, hdd]
      _ = π (u ^ (-k₂)) * (π (u ^ (-k₁)) * π db) * π da := by group
      _ = π (u ^ (-k₂)) * (π db * π (u ^ (-k₁))) * π da := by rw [← hdb1]
      _ = π (u ^ (-k₂)) * π db * (π (u ^ (-k₁)) * π da) := by group
  have h1 : π ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab
  exact (QuotientGroup.eq_one_iff _).1 h1

end Index

end CFSG.RankThree.PartOne.KLC
