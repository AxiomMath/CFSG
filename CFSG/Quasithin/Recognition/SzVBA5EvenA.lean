module

public import CFSG.Quasithin.Recognition.SzVBA5Geo
public import CFSG.Quasithin.Recognition.SzVBA5Uc

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T V : Subgroup G} {z : G}

omit [Finite G] in
private theorem eq_one_or_eq_of_mem_zpowers_of_mul_self_eq_one {x y : G} (hx : x * x = 1)
    (hy : y ∈ Subgroup.zpowers x) : y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private theorem mem_or_mul_inv_mem_of_relIndex_le_two_of_notMem {Q Y : Subgroup G}
    (h : Q.relIndex Y ≤ 2) {v y : G} (hv : v ∈ Y) (hvQ : v ∉ Q) (hy : y ∈ Y) :
    y ∈ Q ∨ y * v⁻¹ ∈ Q := by
  have hpos : 0 < Q.relIndex Y :=
    Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := Q) (K := Y)) Nat.card_pos
  have hdvd : Q.relIndex Y ∣ 2 := by
    rcases (show Q.relIndex Y = 1 ∨ Q.relIndex Y = 2 by omega) with h1 | h2
    · rw [h1]
      exact one_dvd _
    · rw [h2]
  obtain ⟨a, -, ha⟩ := Subgroup.relIndex_dvd_two_iff.mp hdvd
  have hva : v * a ∈ Q := (ha v hv).resolve_right hvQ
  rcases ha y hy with hya | hyQ
  · right
    have e : y * a * (v * a)⁻¹ = y * v⁻¹ := by group
    simpa only [e] using Q.mul_mem hya (Q.inv_mem hva)
  · exact Or.inl hyQ

theorem Uc_le_pCoreOf_u {u δ x ω p2 : CosetGeom G₀ G₁ G₂}
    (D : CritFacts G₀ G₁ G₂ T V z u δ x ω p2)
    (hLF1 : ∀ {w : G}, w ∈ stab u → w * w = 1 → w ∉ pCoreOf 2 (stab u) →
      ∀ c : G, ∃ a ∈ Vv V u, w * a * w⁻¹ * a⁻¹ ∉ ({1, c, z, c * z} : Set G))
    {β : CosetGeom G₀ G₁ G₂} (hβ : (graph G₀ G₁ G₂).Adj (γ₀ G₀ G₁ G₂) β) :
    Uc V (γ₀ G₀ G₁ G₂) β ≤ pCoreOf 2 (stab u) := by
  intro w hw
  by_contra hwQ
  have hC := D.hC
  have hN : G₁ ≤ Subgroup.normalizer (V : Set G) := hC.hyp.normalizes
  have hstab0 : stab (γ₀ G₀ G₁ G₂) = G₁ := stab_γ₀ hC.hyp.le₁
  have hV0 : Vv V (γ₀ G₀ G₁ G₂) = V := Vv_γ₀ hN
  obtain ⟨⟨-, hwcomm'⟩, hwβ⟩ := mem_Uc.mp hw
  have hwcomm : ∀ q ∈ pCoreOf 2 G₁, q * w * q⁻¹ * w⁻¹ ∈ V := by
    intro q hq
    have h := hwcomm' q (by rw [hstab0]; exact hq)
    rwa [hV0] at h
  have hwδ : w ∈ ballStab 1 δ := by
    rw [ballStab_one_eq_pCoreOf hC δ]
    exact D.Wβ_le_Qδ β hβ hwβ
  have hwu : w ∈ stab u :=
    ballStab_le_stab_of_dist_le (dist_eq_one_iff_adj.mpr D.adj_δu).le hwδ
  have hww : w * w = 1 := by
    rw [← pow_two]
    exact F7.isElemAbelian_pow_eq_one (D.Wβ_abel β hβ) hwβ
  have hwN : w ∈ Subgroup.normalizer (Vv V u : Set G) := stab_le_normalizer_Vv hN u hwu
  have hconjA : ∀ a ∈ Vv V u, w * a * w⁻¹ ∈ Vv V u := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hwN a).mp ha
  obtain ⟨a', ha'ω, ha'Q⟩ : ∃ a' ∈ Vv V ω, a' ∉ pCoreOf 2 G₁ := by
    by_contra hcon
    have hle : Vv V ω ≤ pCoreOf 2 G₁ := fun a ha => by
      by_contra h
      exact hcon ⟨a, ha, h⟩
    apply D.comm_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hle.trans (CosetGeom.pCoreOf_le_centralizer hC.hyp))
  have ha'A : a' ∈ Vv V u := D.Vω_le_A ha'ω
  have hcases : ∀ a ∈ Vv V u, a ∈ pCoreOf 2 G₁ ∨ a * a'⁻¹ ∈ pCoreOf 2 G₁ := fun a ha =>
    mem_or_mul_inv_mem_of_relIndex_le_two_of_notMem D.A_rel ha'A ha'Q ha
  have hzA : z ∈ Vv V u := by
    have h : z ∈ V ⊓ Vv V u := by
      rw [D.A_inf]
      exact Subgroup.mem_zpowers z
    exact (Subgroup.mem_inf.mp h).2
  have hzz : z * z = 1 := hC.klein.z_mul_self
  have hcommQ : ∀ a ∈ Vv V u, a ∈ pCoreOf 2 G₁ →
      w * a * w⁻¹ * a⁻¹ = 1 ∨ w * a * w⁻¹ * a⁻¹ = z := by
    intro a haA haQ
    have h1 : a * w * a⁻¹ * w⁻¹ ∈ V := hwcomm a haQ
    have h2 : w * a * w⁻¹ * a⁻¹ ∈ V := by
      have e : w * a * w⁻¹ * a⁻¹ = (a * w * a⁻¹ * w⁻¹)⁻¹ := by group
      rw [e]
      exact V.inv_mem h1
    have h3 : w * a * w⁻¹ * a⁻¹ ∈ Vv V u :=
      (Vv V u).mul_mem (hconjA a haA) ((Vv V u).inv_mem haA)
    have h4 : w * a * w⁻¹ * a⁻¹ ∈ Subgroup.zpowers z := by
      rw [← D.A_inf]
      exact Subgroup.mem_inf.mpr ⟨h2, h3⟩
    exact eq_one_or_eq_of_mem_zpowers_of_mul_self_eq_one hzz h4
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = w * a' * w⁻¹ * a'⁻¹ := ⟨_, rfl⟩
  have hc₀A : c₀ ∈ Vv V u := by
    rw [hc₀]
    exact (Vv V u).mul_mem (hconjA a' ha'A) ((Vv V u).inv_mem ha'A)
  have hzc : z * c₀ = c₀ * z := F7.isElemAbelian_comm D.A_abel hzA hc₀A
  have hclaim : ∀ a ∈ Vv V u, w * a * w⁻¹ * a⁻¹ = 1 ∨ w * a * w⁻¹ * a⁻¹ = c₀ ∨
      w * a * w⁻¹ * a⁻¹ = z ∨ w * a * w⁻¹ * a⁻¹ = c₀ * z := by
    intro a haA
    rcases hcases a haA with haQ | haQ'
    · rcases hcommQ a haA haQ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · obtain ⟨a₀, ha₀Q, hae⟩ : ∃ a₀ ∈ pCoreOf 2 G₁, a = a₀ * a' :=
        ⟨a * a'⁻¹, haQ', by group⟩
      have ha₀A : a₀ ∈ Vv V u := by
        have h1 : a₀ = a * a'⁻¹ := by rw [hae]; group
        rw [h1]
        exact (Vv V u).mul_mem haA ((Vv V u).inv_mem ha'A)
      have e2 : c₀ * a₀⁻¹ = a₀⁻¹ * c₀ :=
        (Commute.inv_left (show Commute a₀ c₀ from
          F7.isElemAbelian_comm D.A_abel ha₀A hc₀A)).eq.symm
      have e3 : w * a * w⁻¹ * a⁻¹ = (w * a₀ * w⁻¹ * a₀⁻¹) * c₀ := by
        calc w * a * w⁻¹ * a⁻¹ = (w * a₀ * w⁻¹) * c₀ * a₀⁻¹ := by rw [hae, hc₀]; group
          _ = (w * a₀ * w⁻¹) * (c₀ * a₀⁻¹) := mul_assoc _ _ _
          _ = (w * a₀ * w⁻¹) * (a₀⁻¹ * c₀) := by rw [e2]
          _ = (w * a₀ * w⁻¹ * a₀⁻¹) * c₀ := (mul_assoc _ _ _).symm
      rcases hcommQ a₀ ha₀A ha₀Q with h | h
      · rw [e3, h, one_mul]
        exact Or.inr (Or.inl rfl)
      · rw [e3, h, hzc]
        exact Or.inr (Or.inr (Or.inr rfl))
  obtain ⟨a, haA, hnot⟩ := hLF1 hwu hww hwQ c₀
  apply hnot
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact hclaim a haA

end CFSG.Quasithin.SzVB
