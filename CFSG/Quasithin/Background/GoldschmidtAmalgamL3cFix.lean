module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3cRot

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmL3
  CFSG.Quasithin.F6.GoldAmL2T

namespace F6

namespace GoldAmL3c

variable {D : Type*} [Group D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem zz_one (h : GoldHyp3 A B z V) : z * z = 1 := by
  have := h.natural.z_sq
  rwa [pow_two] at this

theorem conj_eq_of_cube (h : GoldHyp3 A B z V) {t : D} (htB : t ∈ B) (ht3 : t * t * t = 1)
    {d : D} (hd : t * d * t⁻¹ * d⁻¹ ∈ Subgroup.zpowers z) : t * d * t⁻¹ = d := by
  obtain ⟨w, hw⟩ : ∃ w : D, w = t * d * t⁻¹ * d⁻¹ := ⟨_, rfl⟩
  rw [← hw] at hd
  have hwd : t * d * t⁻¹ = w * d := by rw [hw]; group
  have hw2 : w * w = 1 := by
    rcases zpowers_cases h hd with e | e
    · rw [e]; simp
    · rw [e]; exact zz_one h
  have htw : t * w * t⁻¹ = w := conj_zpowers_B h htB hd
  have h2 : t * t * d * (t * t)⁻¹ = d := by
    calc t * t * d * (t * t)⁻¹ = t * (t * d * t⁻¹) * t⁻¹ := by group
      _ = t * (w * d) * t⁻¹ := by rw [hwd]
      _ = (t * w * t⁻¹) * (t * d * t⁻¹) := by group
      _ = w * (w * d) := by rw [htw, hwd]
      _ = (w * w) * d := by group
      _ = d := by rw [hw2, one_mul]
  calc t * d * t⁻¹ = t * (t * t * d * (t * t)⁻¹) * t⁻¹ := by rw [h2]
    _ = (t * t * t) * d * (t * t * t)⁻¹ := by group
    _ = d := by rw [ht3]; group

section Fix

variable [Finite D] {x a a₁ a₂ : D} (g : Gen3 A B z V x a a₁ a₂)

include g

theorem Gen3.U_inf_centralizer_x (hU : Nat.card (conjClosure V B) = 8) :
    conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) = Subgroup.zpowers z := by
  have hx3 : x ^ 3 = 1 := by rw [pow_three']; exact g.x_cube
  have hnorm : ∀ u ∈ conjClosure V B, x * u * x⁻¹ ∈ conjClosure V B := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V B g.x_mem) u).mp hu
  have hmod := GoldAmN.card_modEq_card_inf_centralizer (conjClosure V B) hx3 hnorm
  have hzle : Subgroup.zpowers z ≤ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) := by
    refine Subgroup.zpowers_le.mpr ⟨g.z_mem_U, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact g.z_comm g.x_mem
  have hdvd : Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D)) ∣ 8 := by
    rw [← hU]; exact Subgroup.card_dvd_of_le inf_le_left
  have h2dvd : 2 ∣ Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D)) := by
    rw [← card_zpowers_eq_two g.hyp.natural]; exact Subgroup.card_dvd_of_le hzle
  rw [hU] at hmod
  unfold Nat.ModEq at hmod
  have hc : Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D)) = 2 ∨
      Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D)) = 8 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card ↥(conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D)) = m at *
    interval_cases m <;> omega
  rcases hc with hc | hc
  · exact (Subgroup.eq_of_le_of_card_ge hzle
      (by rw [hc, card_zpowers_eq_two g.hyp.natural])).symm
  · exfalso
    have hUC : conjClosure V B ≤ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) :=
      (Subgroup.eq_of_le_of_card_ge (inf_le_left : conjClosure V B ⊓
        Subgroup.centralizer ({x} : Set D) ≤ conjClosure V B) (by rw [hc, hU])).ge
    have ha := (Subgroup.mem_centralizer_iff.mp (hUC g.a_mem_U).2 x rfl)
    apply g.a₁_not_mem_V
    have : a₁ = a := by
      rw [g.a₁_eq, ha]; group
    rw [this]; exact g.a_mem

theorem Gen3.psi_eq_one_of_fixed (hU : Nat.card (conjClosure V B) = 8) (q : ↥(pCoreOf 2 B))
    (hfix : g.xc q = q) : psi g q = 1 := by
  have h1 := g.psi_xc hU q
  rw [hfix] at h1
  rcases hp : psi g q with ⟨e₀, e₁⟩
  rw [hp] at h1
  simp only [Prod.mk.injEq] at h1
  obtain ⟨h1a, h1b⟩ := h1
  have he₁ : e₁ = 1 := mul_left_cancel (a := e₀) (by rw [mul_one]; exact h1a.symm)
  have he₀ : e₀ = 1 := h1b.symm.trans he₁
  rw [he₀, he₁]
  rfl

theorem Gen3.fixed_mem_zpowers (hU : Nat.card (conjClosure V B) = 8)
    (hT : Nat.card ↥(A ⊓ B) = 64) {q : D} (hq : q ∈ pCoreOf 2 B) (hfix : x * q * x⁻¹ = q) :
    q ∈ Subgroup.zpowers z := by
  have h1 : psi g ⟨q, hq⟩ = 1 := g.psi_eq_one_of_fixed hU ⟨q, hq⟩ (Subtype.ext hfix)
  have h2 : q ∈ pCoreOf 2 B ⊓ Subgroup.centralizer (conjClosure V B : Set D) :=
    (g.mem_ker_psi hU ⟨q, hq⟩).mp (MonoidHom.mem_ker.mpr h1)
  have h3 : q ∈ conjClosure V B := (g.U_eq_K hU hT).ge h2
  have h4 : q ∈ conjClosure V B ⊓ Subgroup.centralizer ({x} : Set D) := by
    refine ⟨h3, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * q = (y * q * y⁻¹) * y := by group
      _ = q * y := by rw [hfix]
  rw [g.U_inf_centralizer_x hU] at h4
  exact h4

end Fix

end GoldAmL3c

end F6

end CFSG.Quasithin
