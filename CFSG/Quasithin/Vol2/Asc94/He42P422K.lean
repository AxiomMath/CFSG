module

public import CFSG.Quasithin.Vol2.Asc94.He42P422E
public import CFSG.Quasithin.Vol2.Asc94.He42P422Syl
public import CFSG.Quasithin.Recognition.M12AscKlein

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

namespace HeSetup

variable (S : HeSetup G)

theorem cent_iff_422 {g z r β : G} (hg : g ∈ S.L2) (hzZ : z ∈ S.Z)
    (hPz : IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer (S.B : Set G)))
    (hz : g * z * g⁻¹ = r * β) (hβ : β ∈ S.B) {c : G} (hcB : ∀ b ∈ S.B, b * c = c * b) :
    c * r = r * c ↔ g⁻¹ * c * g ∈ S.J := by
  have hB := S.baseFacts
  have hgb : ∀ b ∈ S.B, g * b = b * g := fun b hb =>
    (mem_centralizer_iff.mp (hB.L2_le_centralizer hg) b hb).symm
  have hgb' : ∀ b ∈ S.B, g⁻¹ * b = b * g⁻¹ := by
    intro b hb
    calc g⁻¹ * b = g⁻¹ * (b * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * b) * g⁻¹ := by rw [hgb b hb]
      _ = b * g⁻¹ := by group
  have hcβ : c * β = β * c := (hcB β hβ).symm
  constructor
  · intro hcr
    have hcv : c * (g * z * g⁻¹) = (g * z * g⁻¹) * c := by
      rw [hz]
      calc c * (r * β) = (c * r) * β := by group
        _ = (r * c) * β := by rw [hcr]
        _ = r * (c * β) := by group
        _ = r * (β * c) := by rw [hcβ]
        _ = (r * β) * c := by group
    have hdz : g⁻¹ * c * g * z = z * (g⁻¹ * c * g) := by
      calc g⁻¹ * c * g * z = g⁻¹ * (c * (g * z * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * z * g⁻¹) * c) * g := by rw [hcv]
        _ = z * (g⁻¹ * c * g) := by group
    have hdB : ∀ b ∈ S.B, (g⁻¹ * c * g) * b = b * (g⁻¹ * c * g) := by
      intro b hb
      calc g⁻¹ * c * g * b = g⁻¹ * c * (g * b) := by group
        _ = g⁻¹ * c * (b * g) := by rw [hgb b hb]
        _ = g⁻¹ * (c * b) * g := by group
        _ = g⁻¹ * (b * c) * g := by rw [hcB b hb]
        _ = (g⁻¹ * b) * c * g := by group
        _ = (b * g⁻¹) * c * g := by rw [hgb' b hb]
        _ = b * (g⁻¹ * c * g) := by group
    exact S.le_J_of_isPGroup hB hzZ hPz hdz hdB
  · intro hd
    have hdz : g⁻¹ * c * g * z = z * (g⁻¹ * c * g) := HeJ.TData.Z_central S.hD.hT S.hD.hK.Aab
      S.hD.hK.A'ab hzZ hd
    have hcv : c * (g * z * g⁻¹) = (g * z * g⁻¹) * c := by
      calc c * (g * z * g⁻¹) = g * (g⁻¹ * c * g * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * c * g)) * g⁻¹ := by rw [hdz]
        _ = (g * z * g⁻¹) * c := by group
    rw [hz] at hcv
    have h1 : c * r * β = r * c * β := by
      calc c * r * β = c * (r * β) := by group
        _ = (r * β) * c := hcv
        _ = r * (β * c) := by group
        _ = r * (c * β) := by rw [hcβ]
        _ = r * c * β := by group
    exact mul_right_cancel h1

theorem cent_R_422 {y₁ g z r β : G} (hyN : g⁻¹ * y₁ * g ∈ S.N) (hyord : orderOf (g⁻¹ * y₁ * g) = 3)
    (hg : g ∈ S.L2) (hzZ : z ∈ S.Z)
    (hPz : IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer (S.B : Set G)))
    (hz : g * z * g⁻¹ = r * β) (hβ : β ∈ S.B)
    (hr : r ∈ S.A' ⊓ centralizer ({y₁} : Set G))
    (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4) :
    ∀ c ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G), c * r = r * c →
      c ∈ S.A' ⊓ centralizer ({y₁} : Set G) := by
  have hB := S.baseFacts
  have hBA' : ∀ b ∈ S.B, b ∈ S.A' := fun b hb => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2
  have hRC : S.A' ⊓ centralizer ({y₁} : Set G) ≤
      centralizer ({r} : Set G) ⊓ (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) := by
    intro x hx
    obtain ⟨hxA', hxy⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_inf.mpr ⟨hxy, ?_⟩⟩
    · rw [mem_centralizer_singleton_iff]
      exact hB.A'_comm x hxA' r hr.1
    · rw [mem_centralizer_iff]
      intro b hb
      exact hB.A'_comm b (hBA' b hb) x hxA'
  have hcardCX : Nat.card ↥(centralizer ({r} : Set G) ⊓ (centralizer ({y₁} : Set G) ⊓
      centralizer (S.B : Set G))) ≤ 4 := by
    have hy3 : (g⁻¹ * y₁ * g) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (g⁻¹ * y₁ * g)
      rwa [hyord] at h
    have hcardJ := S.card_centralizer_J_le_four_422 hyN hy3 (S.rhoG_ne_one_422 hyN hyord)
    have hmemJ : ∀ c : ↥(centralizer ({r} : Set G) ⊓ (centralizer ({y₁} : Set G) ⊓
        centralizer (S.B : Set G))), g⁻¹ * (c : G) * g ∈
          centralizer ({g⁻¹ * y₁ * g} : Set G) ⊓ S.J := by
      intro c
      obtain ⟨hcr, hcX⟩ := Subgroup.mem_inf.mp c.2
      obtain ⟨hcy, hcB⟩ := Subgroup.mem_inf.mp hcX
      have hcr' : (c : G) * r = r * c := mem_centralizer_singleton_iff.mp hcr
      have hcB' : ∀ b ∈ S.B, b * (c : G) = (c : G) * b := mem_centralizer_iff.mp hcB
      have hJ := (S.cent_iff_422 hg hzZ hPz hz hβ hcB').mp hcr'
      refine Subgroup.mem_inf.mpr ⟨?_, hJ⟩
      rw [mem_centralizer_singleton_iff]
      have hcy' : (c : G) * y₁ = y₁ * c := mem_centralizer_singleton_iff.mp hcy
      calc g⁻¹ * (c : G) * g * (g⁻¹ * y₁ * g) = g⁻¹ * ((c : G) * y₁) * g := by group
        _ = g⁻¹ * (y₁ * (c : G)) * g := by rw [hcy']
        _ = (g⁻¹ * y₁ * g) * (g⁻¹ * (c : G) * g) := by group
    have hinj : Function.Injective (fun c : ↥(centralizer ({r} : Set G) ⊓ (centralizer ({y₁} : Set G) ⊓
        centralizer (S.B : Set G))) => (⟨g⁻¹ * (c : G) * g, hmemJ c⟩ :
          ↥(centralizer ({g⁻¹ * y₁ * g} : Set G) ⊓ S.J))) := by
      intro c d h
      have h1 : g⁻¹ * (c : G) * g = g⁻¹ * (d : G) * g := congrArg Subtype.val h
      apply Subtype.ext
      calc (c : G) = g * (g⁻¹ * (c : G) * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * (d : G) * g) * g⁻¹ := by rw [h1]
        _ = (d : G) := by group
    exact (Nat.card_le_card_of_injective _ hinj).trans hcardJ
  have hEq : S.A' ⊓ centralizer ({y₁} : Set G) = centralizer ({r} : Set G) ⊓
      (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hRC (hcardCX.trans (le_of_eq hR4.symm))
  intro c hc hcr
  have hcC : c ∈ centralizer ({r} : Set G) ⊓ (centralizer ({y₁} : Set G) ⊓
      centralizer (S.B : Set G)) :=
    Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hcr, hc⟩
  rw [hEq]
  exact hcC

theorem cent_conj_422 {y₁ y₀ r : G} (hy₀N : y₀ ∈ S.N) (hy₀y₁ : y₀ * y₁ = y₁ * y₀)
    (hy₀B : ∀ b ∈ S.B, b * y₀ = y₀ * b)
    (hcr : ∀ c ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G), c * r = r * c →
      c ∈ S.A' ⊓ centralizer ({y₁} : Set G)) :
    ∀ c ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G),
      c * (y₀ * r * y₀⁻¹) = (y₀ * r * y₀⁻¹) * c → c ∈ S.A' ⊓ centralizer ({y₁} : Set G) := by
  intro c hc hcc
  have hcy : c * y₁ = y₁ * c := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).1
  have hcb : ∀ b ∈ S.B, b * c = c * b := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2
  have hy₀inv_y₁ : y₀⁻¹ * y₁ = y₁ * y₀⁻¹ := by
    calc y₀⁻¹ * y₁ = y₀⁻¹ * (y₁ * y₀) * y₀⁻¹ := by group
      _ = y₀⁻¹ * (y₀ * y₁) * y₀⁻¹ := by rw [hy₀y₁]
      _ = y₁ * y₀⁻¹ := by group
  have hbinv : ∀ b ∈ S.B, b * y₀⁻¹ = y₀⁻¹ * b := by
    intro b hb
    calc b * y₀⁻¹ = y₀⁻¹ * (y₀ * b) * y₀⁻¹ := by group
      _ = y₀⁻¹ * (b * y₀) * y₀⁻¹ := by rw [hy₀B b hb]
      _ = y₀⁻¹ * b := by group
  have hc'y : (y₀⁻¹ * c * y₀) * y₁ = y₁ * (y₀⁻¹ * c * y₀) := by
    calc (y₀⁻¹ * c * y₀) * y₁ = y₀⁻¹ * c * (y₀ * y₁) := by group
      _ = y₀⁻¹ * c * (y₁ * y₀) := by rw [hy₀y₁]
      _ = y₀⁻¹ * (c * y₁) * y₀ := by group
      _ = y₀⁻¹ * (y₁ * c) * y₀ := by rw [hcy]
      _ = (y₀⁻¹ * y₁) * c * y₀ := by group
      _ = (y₁ * y₀⁻¹) * c * y₀ := by rw [hy₀inv_y₁]
      _ = y₁ * (y₀⁻¹ * c * y₀) := by group
  have hc'B : ∀ b ∈ S.B, b * (y₀⁻¹ * c * y₀) = (y₀⁻¹ * c * y₀) * b := by
    intro b hb
    calc b * (y₀⁻¹ * c * y₀) = (b * y₀⁻¹) * c * y₀ := by group
      _ = (y₀⁻¹ * b) * c * y₀ := by rw [hbinv b hb]
      _ = y₀⁻¹ * (b * c) * y₀ := by group
      _ = y₀⁻¹ * (c * b) * y₀ := by rw [hcb b hb]
      _ = y₀⁻¹ * c * (b * y₀) := by group
      _ = y₀⁻¹ * c * (y₀ * b) := by rw [hy₀B b hb]
      _ = (y₀⁻¹ * c * y₀) * b := by group
  have hc'r : (y₀⁻¹ * c * y₀) * r = r * (y₀⁻¹ * c * y₀) := by
    calc (y₀⁻¹ * c * y₀) * r = y₀⁻¹ * (c * (y₀ * r * y₀⁻¹)) * y₀ := by group
      _ = y₀⁻¹ * ((y₀ * r * y₀⁻¹) * c) * y₀ := by rw [hcc]
      _ = r * (y₀⁻¹ * c * y₀) := by group
  have hc'X : (y₀⁻¹ * c * y₀) ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) :=
    Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc'y, mem_centralizer_iff.mpr hc'B⟩
  have hc'R := hcr _ hc'X hc'r
  obtain ⟨hc'A, hc'y1⟩ := Subgroup.mem_inf.mp hc'R
  have hy₀A' := S.N_le_normalizer_A'_422 hy₀N
  have hcA : c ∈ S.A' := by
    have e : y₀ * (y₀⁻¹ * c * y₀) * y₀⁻¹ = c := by group
    have h := (Subgroup.mem_normalizer_iff.mp hy₀A' (y₀⁻¹ * c * y₀)).mp hc'A
    rwa [e] at h
  have hcy1 : c * y₁ = y₁ * c := by
    have e : y₀ * (y₀⁻¹ * c * y₀) * y₀⁻¹ = c := by group
    calc c * y₁ = y₀ * (y₀⁻¹ * c * y₀) * y₀⁻¹ * y₁ := by rw [e]
      _ = y₀ * (y₀⁻¹ * c * y₀) * (y₀⁻¹ * y₁) := by group
      _ = y₀ * (y₀⁻¹ * c * y₀) * (y₁ * y₀⁻¹) := by rw [hy₀inv_y₁]
      _ = y₀ * ((y₀⁻¹ * c * y₀) * y₁) * y₀⁻¹ := by group
      _ = y₀ * (y₁ * (y₀⁻¹ * c * y₀)) * y₀⁻¹ := by rw [hc'y]
      _ = (y₀ * y₁) * (y₀⁻¹ * c * y₀) * y₀⁻¹ := by group
      _ = (y₁ * y₀) * (y₀⁻¹ * c * y₀) * y₀⁻¹ := by rw [hy₀y₁]
      _ = y₁ * (y₀ * (y₀⁻¹ * c * y₀) * y₀⁻¹) := by group
      _ = y₁ * c := by rw [e]
  exact Subgroup.mem_inf.mpr ⟨hcA, mem_centralizer_singleton_iff.mpr hcy1⟩

theorem R_elts_422 {y₁ y₀ τ : G} (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4)
    (hτR : τ ∈ S.A' ⊓ centralizer ({y₁} : Set G)) (hτ1 : τ ≠ 1)
    (hyR : ∀ v ∈ S.A' ⊓ centralizer ({y₁} : Set G),
      y₀ * v * y₀⁻¹ ∈ S.A' ⊓ centralizer ({y₁} : Set G))
    (hne : y₀ * τ * y₀⁻¹ ≠ τ) (hy3 : y₀ * y₀ * y₀ = 1) :
    ∀ r ∈ S.A' ⊓ centralizer ({y₁} : Set G),
      r = 1 ∨ r = τ ∨ r = y₀ * τ * y₀⁻¹ ∨ r = y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹ := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have h4 : y₀ * y₀ * y₀ * y₀ = y₀ := by rw [hy3, one_mul]
  have hσR := hyR τ hτR
  have hσ₂R := hyR _ hσR
  have hσ1 : y₀ * τ * y₀⁻¹ ≠ 1 := fun h => hτ1 (by
    calc τ = y₀⁻¹ * (y₀ * τ * y₀⁻¹) * y₀ := by group
      _ = 1 := by rw [h]; group)
  have hσ₂1 : y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹ ≠ 1 := fun h => hσ1 (by
    calc y₀ * τ * y₀⁻¹ = y₀⁻¹ * (y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹) * y₀ := by group
      _ = 1 := by rw [h]; group)
  have hτσ : τ ≠ y₀ * τ * y₀⁻¹ := fun h => hne h.symm
  have hτσ₂ : τ ≠ y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹ := by
    intro h
    have hτeq : y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹ = τ := h.symm
    have key : y₀ * y₀ * τ = τ * (y₀ * y₀) := by
      calc y₀ * y₀ * τ = (y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹) * (y₀ * y₀) := by group
        _ = τ * (y₀ * y₀) := by rw [hτeq]
    have hcomm1 : y₀ * τ = τ * y₀ := by
      calc y₀ * τ = (y₀ * y₀ * y₀ * y₀) * τ := by rw [h4]
        _ = (y₀ * y₀) * ((y₀ * y₀) * τ) := by group
        _ = (y₀ * y₀) * (τ * (y₀ * y₀)) := by rw [key]
        _ = ((y₀ * y₀) * τ) * (y₀ * y₀) := by group
        _ = (τ * (y₀ * y₀)) * (y₀ * y₀) := by rw [key]
        _ = τ * (y₀ * y₀ * y₀ * y₀) := by group
        _ = τ * y₀ := by rw [h4]
    exact hne ((mul_inv_eq_iff_eq_mul).2 hcomm1)
  have hσσ₂ : y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹ ≠ y₀ * τ * y₀⁻¹ := by
    intro h
    have hσy : y₀ * (y₀ * τ * y₀⁻¹) = (y₀ * τ * y₀⁻¹) * y₀ := (mul_inv_eq_iff_eq_mul).1 h
    have hτσ' : y₀⁻¹ * (y₀ * τ * y₀⁻¹) * y₀ = y₀ * τ * y₀⁻¹ := by
      calc y₀⁻¹ * (y₀ * τ * y₀⁻¹) * y₀ = y₀⁻¹ * ((y₀ * τ * y₀⁻¹) * y₀) := by group
        _ = y₀⁻¹ * (y₀ * (y₀ * τ * y₀⁻¹)) := by rw [hσy]
        _ = y₀ * τ * y₀⁻¹ := by group
    exact hτσ (by
      calc τ = y₀⁻¹ * (y₀ * τ * y₀⁻¹) * y₀ := by group
        _ = y₀ * τ * y₀⁻¹ := hτσ')
  let F : Finset G := {1, τ, y₀ * τ * y₀⁻¹, y₀ * (y₀ * τ * y₀⁻¹) * y₀⁻¹}
  have hFcard : F.card = 4 := by
    simp only [F]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hσσ₂.symm]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hτσ, hτσ₂⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hτ1.symm, hσ1.symm, hσ₂1.symm⟩
  let U : Finset G := Finset.univ.filter (fun x : G => x ∈ S.A' ⊓ centralizer ({y₁} : Set G))
  have hUcard : U.card = 4 := by
    have h1 : (Finset.univ.filter (fun x : G => x ∈ S.A' ⊓ centralizer ({y₁} : Set G))).card =
        Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact h1.trans hR4
  have hFU : F ⊆ U := by
    intro x hx
    simp only [F, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact hτR
    · exact hσR
    · exact hσ₂R
  have heq : F = U := Finset.eq_of_subset_of_card_le hFU (le_of_eq (by rw [hUcard, hFcard]))
  intro r hr
  have hrU : r ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
  rw [← heq] at hrU
  simp only [F, Finset.mem_insert, Finset.mem_singleton] at hrU
  exact hrU

theorem syl_X_422 {y₁ : G} (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4)
    (hcentR : ∀ r ∈ S.A' ⊓ centralizer ({y₁} : Set G), r ≠ 1 →
      ∀ c ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G), c * r = r * c →
        c ∈ S.A' ⊓ centralizer ({y₁} : Set G)) :
    ∀ W : Subgroup G, W ≤ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) →
      IsPGroup 2 W → Nat.card ↥W ≤ 4 := by
  intro W hWX hW
  have hB := S.baseFacts
  have hBA' : ∀ b ∈ S.B, b ∈ S.A' := fun b hb => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2
  have hRX : S.A' ⊓ centralizer ({y₁} : Set G) ≤
      centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) := by
    intro x hx
    obtain ⟨hxA', hxy⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxy,
      mem_centralizer_iff.mpr (fun b hb => hB.A'_comm b (hBA' b hb) x hxA')⟩
  have hV : Nat.card ↥((S.A' ⊓ centralizer ({y₁} : Set G)).subgroupOf
      (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G))) = 4 := by
    rw [← hR4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRX).toEquiv
  have hcent : ∀ v ∈ (S.A' ⊓ centralizer ({y₁} : Set G)).subgroupOf
      (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)), v ≠ 1 →
      ∀ c : ↥(centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)), c * v = v * c →
        c ∈ (S.A' ⊓ centralizer ({y₁} : Set G)).subgroupOf
          (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G)) := by
    intro v hv hv1 c hc
    have hv' : (v : G) ∈ S.A' ⊓ centralizer ({y₁} : Set G) := Subgroup.mem_subgroupOf.mp hv
    have hv1' : (v : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hc' : (c : G) * (v : G) = (v : G) * (c : G) := congrArg Subtype.val hc
    exact Subgroup.mem_subgroupOf.mpr (hcentR _ hv' hv1' _ c.2 hc')
  have hW' : IsPGroup 2 (W.subgroupOf (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G))) :=
    hW.of_equiv (Subgroup.subgroupOfEquivOfLe hWX).symm
  have h := card_two_sub_le_four_422 _ hV hcent _ hW'
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv] at h
  exact h

theorem kleinCore_422 {y₁ y₀ τ : G} (hy₀N : y₀ ∈ S.N) (hy₀y₁ : y₀ * y₁ = y₁ * y₀)
    (hy₀B : ∀ b ∈ S.B, b * y₀ = y₀ * b) (hy₀3 : y₀ * y₀ * y₀ = 1) (hy₀ord : orderOf y₀ = 3)
    (hRA : S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) = ⊥)
    (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4)
    (hτR : τ ∈ S.A' ⊓ centralizer ({y₁} : Set G)) (hτ1 : τ ≠ 1)
    (hcentτ : ∀ c ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G), c * τ = τ * c →
      c ∈ S.A' ⊓ centralizer ({y₁} : Set G)) :
    KleinCore (centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G))
      (S.A' ⊓ centralizer ({y₁} : Set G)) τ y₀ := by
  have hB := S.baseFacts
  have hBA' : ∀ b ∈ S.B, b ∈ S.A' := fun b hb => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).2
  have hy₀ρ : S.rhoG y₀ ≠ 1 := S.rhoG_ne_one_422 hy₀N hy₀ord
  have hy₀3' : y₀ ^ 3 = 1 := by rw [pow_three']; exact hy₀3
  have hJB := S.centralizer_J_eq_B_422 hy₀N hy₀3' hy₀ρ hy₀B
  have hτA' : τ ∈ S.A' := (Subgroup.mem_inf.mp hτR).1
  have hτB : τ ∉ S.B := by
    intro hτB
    have hτA : τ ∈ S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) :=
      ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hτB).1).1, hτR⟩
    rw [hRA, Subgroup.mem_bot] at hτA
    exact hτ1 hτA
  have hRX : S.A' ⊓ centralizer ({y₁} : Set G) ≤
      centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G) := by
    intro x hx
    obtain ⟨hxA', hxy⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxy,
      mem_centralizer_iff.mpr (fun b hb => hB.A'_comm b (hBA' b hb) x hxA')⟩
  have hy₀inv_y₁ : y₀⁻¹ * y₁ = y₁ * y₀⁻¹ := by
    calc y₀⁻¹ * y₁ = y₀⁻¹ * (y₁ * y₀) * y₀⁻¹ := by group
      _ = y₀⁻¹ * (y₀ * y₁) * y₀⁻¹ := by rw [← hy₀y₁]
      _ = y₁ * y₀⁻¹ := by group
  have hyR : ∀ v ∈ S.A' ⊓ centralizer ({y₁} : Set G),
      y₀ * v * y₀⁻¹ ∈ S.A' ⊓ centralizer ({y₁} : Set G) := by
    intro v hv
    obtain ⟨hvA, hvy⟩ := Subgroup.mem_inf.mp hv
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (S.N_le_normalizer_A'_422 hy₀N) v).mp hvA
    · have hvy' : v * y₁ = y₁ * v := mem_centralizer_singleton_iff.mp hvy
      rw [mem_centralizer_singleton_iff]
      calc y₀ * v * y₀⁻¹ * y₁ = y₀ * v * (y₀⁻¹ * y₁) := by group
        _ = y₀ * v * (y₁ * y₀⁻¹) := by rw [hy₀inv_y₁]
        _ = y₀ * (v * y₁) * y₀⁻¹ := by group
        _ = y₀ * (y₁ * v) * y₀⁻¹ := by rw [hvy']
        _ = (y₀ * y₁) * v * y₀⁻¹ := by group
        _ = (y₁ * y₀) * v * y₀⁻¹ := by rw [hy₀y₁]
        _ = y₁ * (y₀ * v * y₀⁻¹) := by group
  have hne : y₀ * τ * y₀⁻¹ ≠ τ := by
    intro h
    have hcomm : y₀ * τ = τ * y₀ := (mul_inv_eq_iff_eq_mul).1 h
    have hτX : τ ∈ centralizer ({y₀} : Set G) ⊓ S.J :=
      Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hcomm.symm,
        le_sup_right (a := S.A) (b := S.A') hτA'⟩
    rw [hJB] at hτX
    exact hτB hτX
  have hR_elts := S.R_elts_422 hR4 hτR hτ1 hyR hne hy₀3
  have hσcent := S.cent_conj_422 hy₀N hy₀y₁ hy₀B hcentτ
  have hall : ∀ r ∈ S.A' ⊓ centralizer ({y₁} : Set G), r ≠ 1 →
      ∀ c ∈ centralizer ({y₁} : Set G) ⊓ centralizer (S.B : Set G), c * r = r * c →
        c ∈ S.A' ⊓ centralizer ({y₁} : Set G) := by
    intro r hr hr1 c hc hcr
    rcases hR_elts r hr with h | h | h | h
    · exact absurd h hr1
    · rw [h] at hcr
      exact hcentτ c hc hcr
    · rw [h] at hcr
      exact hσcent c hc hcr
    · rw [h] at hcr
      exact S.cent_conj_422 hy₀N hy₀y₁ hy₀B hσcent c hc hcr
  exact ⟨hB.A'_sq τ hτA', hτ1, hτR, hRX, hR4, fun v hv => hB.A'_sq v (Subgroup.mem_inf.mp hv).1,
    fun k hk hkτ => hall τ hτR hτ1 k hk hkτ,
    Subgroup.mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hy₀y₁, mem_centralizer_iff.mpr hy₀B⟩,
    hy₀3, hyR, hne, S.syl_X_422 hR4 hall⟩
end HeSetup

end CFSG.Quasithin.A94.He42
