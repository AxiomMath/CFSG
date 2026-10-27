module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamSVertexB
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSProd

public section

namespace CFSG.Quasithin.F6.GoldAmS

open Equiv CFSG.Open CFSG.QuasithinUnique

variable {E : Type*} [Group E]

theorem central_trivial {A₁ A₂ : Subgroup E} (h : IsGoldschmidtAmalgam A₁ A₂) {e : E}
    (he : e ∈ A₁ ⊓ A₂) (h1 : ∀ g ∈ A₁, g * e = e * g) (h2 : ∀ g ∈ A₂, g * e = e * g) :
    e = 1 := by
  have hle : A₁ ⊔ A₂ ≤ Subgroup.centralizer ({e} : Set E) :=
    sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h1 x hx))
      (fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (h2 x hx))
  have hcent : ∀ g : E, g * e = e * g := fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle (h.gen ▸ Subgroup.mem_top g))
  have hN : (Subgroup.zpowers e).Normal := ⟨fun n hn g => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * e * g⁻¹ = e := by rw [hcent g]; group
    rw [← conj_zpow, this]
    exact Subgroup.zpow_mem_zpowers e k⟩
  have := h.toIsGoldschmidtTriple.le_pCore_of_normal_le_inf (N := Subgroup.zpowers e)
    (Subgroup.zpowers_le.2 he)
  rw [h.pCore_eq_bot, le_bot_iff] at this
  exact Subgroup.zpowers_eq_bot.1 this

structure Glob (A₁ A₂ N₁ N₂ : Subgroup E) (ε₁ ε₂ : E) : Prop where
  amalgam : IsGoldschmidtAmalgam A₁ A₂
  card : Nat.card ↥(A₁ ⊓ A₂) = 16
  v₁ : VtxB A₁ (pCoreOf 2 A₁) N₁ ε₁
  v₂ : VtxB A₂ (pCoreOf 2 A₂) N₂ ε₂

namespace Glob

variable [Finite E] {A₁ A₂ N₁ N₂ : Subgroup E} {ε₁ ε₂ : E} (G : Glob A₁ A₂ N₁ N₂ ε₁ ε₂)

include G

theorem Q₁_le_inf : pCoreOf 2 A₁ ≤ A₁ ⊓ A₂ := by
  rintro x ⟨q, hq, rfl⟩
  exact ⟨q.2, pCore_le_inf G.amalgam.toIsGoldschmidtTriple q hq⟩

theorem Q₂_le_inf : pCoreOf 2 A₂ ≤ A₁ ⊓ A₂ := by
  rintro x ⟨q, hq, rfl⟩
  exact ⟨pCore_le_inf G.amalgam.toIsGoldschmidtTriple.symm q hq, q.2⟩

theorem ε₁_mem_inf : ε₁ ∈ A₁ ⊓ A₂ := G.Q₁_le_inf G.v₁.ε_mem

theorem ε₂_mem_inf : ε₂ ∈ A₁ ⊓ A₂ := G.Q₂_le_inf G.v₂.ε_mem

theorem ε₁_mem_Q₂ : ε₁ ∈ pCoreOf 2 A₂ :=
  G.v₂.cent ε₁ G.ε₁_mem_inf.2 fun q hq => (G.v₁.ε_central q (G.Q₂_le_inf hq).1).symm

theorem ε₂_mem_Q₁ : ε₂ ∈ pCoreOf 2 A₁ :=
  G.v₁.cent ε₂ G.ε₂_mem_inf.1 fun q hq => (G.v₂.ε_central q (G.Q₁_le_inf hq).2).symm

theorem ε_ne : ε₁ ≠ ε₂ := by
  intro heq
  apply G.v₁.ε_ne
  exact central_trivial G.amalgam G.ε₁_mem_inf (fun g hg => G.v₁.ε_central g hg)
    (fun g hg => by rw [heq]; exact G.v₂.ε_central g hg)

theorem Q_ne : pCoreOf 2 A₁ ≠ pCoreOf 2 A₂ := by
  apply pCoreOf_ne G.amalgam
  have : Nat.card (pCoreOf 2 A₁) = Nat.card (CFSG.Open.pCore 2 ↥A₁) := by
    unfold pCoreOf
    exact Subgroup.card_map_of_injective A₁.subtype_injective
  rw [← this, G.v₁.Q_card]
  norm_num

theorem R_card_le : Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) ≤ 4 := by
  have hdvd : Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) ∣ 8 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ ≤ pCoreOf 2 A₁)
    rwa [G.v₁.Q_card] at this
  have hne : Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) ≠ 8 := by
    intro h8
    have hR : pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ = pCoreOf 2 A₁ :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ ≤ pCoreOf 2 A₁)
        (by rw [G.v₁.Q_card, h8])
    apply G.Q_ne
    have hle : pCoreOf 2 A₁ ≤ pCoreOf 2 A₂ := inf_eq_left.1 hR
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [G.v₁.Q_card, G.v₂.Q_card])
  have hle8 : Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) := Nat.card_pos
  generalize Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) = n at hdvd hne hle8 hpos
  interval_cases n <;> omega

omit [Finite E] in
theorem ε₁_ne_one : ε₁ ≠ 1 := G.v₁.ε_ne

omit [Finite E] in
theorem ε₂_ne_one : ε₂ ≠ 1 := G.v₂.ε_ne

theorem z_ne_one : ε₁ * ε₂ ≠ 1 := by
  intro h1
  apply G.ε_ne
  have h2 : ε₁⁻¹ = ε₂ := inv_eq_of_mul_eq_one_right h1
  have h3 : ε₁⁻¹ = ε₁ := inv_eq_of_mul_eq_one_right (G.v₁.Q_exp ε₁ G.v₁.ε_mem)
  rw [← h3, h2]

theorem ε₁ε₂_mem_R : ε₁ * ε₂ ∈ pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ :=
  ⟨Subgroup.mul_mem _ G.v₁.ε_mem G.ε₂_mem_Q₁, Subgroup.mul_mem _ G.ε₁_mem_Q₂ G.v₂.ε_mem⟩

theorem R_four : ∀ r ∈ pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂, r = 1 ∨ r = ε₁ ∨ r = ε₂ ∨ r = ε₁ * ε₂ := by
  refine mem_of_card_le_four G.R_card_le (u := ε₁) (v := ε₂) (w := ε₁ * ε₂)
    ⟨G.v₁.ε_mem, G.ε₁_mem_Q₂⟩ ⟨G.ε₂_mem_Q₁, G.v₂.ε_mem⟩ G.ε₁ε₂_mem_R
    (Ne.symm G.ε₁_ne_one) (Ne.symm G.ε₂_ne_one) (Ne.symm G.z_ne_one) G.ε_ne ?_ ?_
  · intro h
    apply G.ε₂_ne_one
    calc ε₂ = ε₁⁻¹ * (ε₁ * ε₂) := by group
      _ = 1 := by rw [← h]; group
  · intro h
    apply G.ε₁_ne_one
    calc ε₁ = (ε₁ * ε₂) * ε₂⁻¹ := by group
      _ = 1 := by rw [← h]; group

theorem four_le_R : 4 ≤ Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) := by
  refine four_le_card (u := ε₁) (v := ε₂) (w := ε₁ * ε₂)
    ⟨G.v₁.ε_mem, G.ε₁_mem_Q₂⟩ ⟨G.ε₂_mem_Q₁, G.v₂.ε_mem⟩ G.ε₁ε₂_mem_R
    (Ne.symm G.ε₁_ne_one) (Ne.symm G.ε₂_ne_one) (Ne.symm G.z_ne_one) G.ε_ne ?_ ?_
  · intro h
    apply G.ε₂_ne_one
    calc ε₂ = ε₁⁻¹ * (ε₁ * ε₂) := by group
      _ = 1 := by rw [← h]; group
  · intro h
    apply G.ε₁_ne_one
    calc ε₁ = (ε₁ * ε₂) * ε₂⁻¹ := by group
      _ = 1 := by rw [← h]; group

theorem exists_a : ∃ a ∈ N₁, a ∉ pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ := by
  by_contra hcon
  push Not at hcon
  have hle : N₁ ≤ pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ := fun n hn => hcon n hn
  have heq : N₁ = pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [G.v₁.N_card]; exact G.R_card_le)
  apply G.v₁.ε_not_N
  rw [heq]
  exact ⟨G.v₁.ε_mem, G.ε₁_mem_Q₂⟩

theorem exists_b : ∃ b ∈ N₂, b ∉ pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ := by
  by_contra hcon
  push Not at hcon
  have hle : N₂ ≤ pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ := fun n hn => hcon n hn
  have heq : N₂ = pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [G.v₂.N_card]; exact G.R_card_le)
  apply G.v₂.ε_not_N
  rw [heq]
  exact ⟨G.ε₂_mem_Q₁, G.v₂.ε_mem⟩

theorem exists_z : ∃ a b : E, a ∈ N₁ ∧ a ∉ pCoreOf 2 A₂ ∧ b ∈ N₂ ∧ b ∉ pCoreOf 2 A₁ ∧
    a * b ≠ b * a ∧ a * b * a⁻¹ * b⁻¹ = ε₁ * ε₂ ∧ ε₁ * ε₂ ∈ N₁ ∧ ε₁ * ε₂ ∈ N₂ := by
  obtain ⟨a, haN, haR⟩ := G.exists_a
  obtain ⟨b, hbN, hbR⟩ := G.exists_b
  have ha1 : a ∈ pCoreOf 2 A₁ := G.v₁.N_le haN
  have hb2 : b ∈ pCoreOf 2 A₂ := G.v₂.N_le hbN
  have ha2 : a ∉ pCoreOf 2 A₂ := fun h => haR ⟨ha1, h⟩
  have hb1 : b ∉ pCoreOf 2 A₁ := fun h => hbR ⟨h, hb2⟩
  have haA₂ : a ∈ A₂ := (G.Q₁_le_inf ha1).2
  have hbA₁ : b ∈ A₁ := (G.Q₂_le_inf hb2).1
  have hab : a * b ≠ b * a := by
    intro hab
    let C : Subgroup E := Subgroup.centralizer ({b} : Set E) ⊓ pCoreOf 2 A₁
    have hRC : pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂ ≤ C := by
      intro r hr
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hr.1⟩
      exact comm_of_exp_two G.v₂.Q_exp hr.2 hb2
    have haC : a ∈ C := ⟨Subgroup.mem_centralizer_singleton_iff.2 hab, ha1⟩
    have hCle : C ≤ pCoreOf 2 A₁ := inf_le_right
    have hRC' : ¬ Nat.card C ≤ Nat.card ↥(pCoreOf 2 A₁ ⊓ pCoreOf 2 A₂) := by
      intro hle
      exact haR (Subgroup.eq_of_le_of_card_ge hRC hle ▸ haC)
    have hCdvd : Nat.card C ∣ 8 := by
      have := Subgroup.card_dvd_of_le hCle
      rwa [G.v₁.Q_card] at this
    have hC8 : Nat.card C = 8 := by
      have h4 := G.four_le_R
      have hle8 : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hCdvd
      push Not at hRC'
      generalize Nat.card C = n at hCdvd hRC' hle8
      interval_cases n <;> omega
    have hCQ : C = pCoreOf 2 A₁ :=
      Subgroup.eq_of_le_of_card_ge hCle (by rw [hC8, G.v₁.Q_card])
    have hbQ₁ : b ∈ pCoreOf 2 A₁ := G.v₁.cent b hbA₁ fun q hq => by
      have : q ∈ C := hCQ ▸ hq
      exact (Subgroup.mem_centralizer_singleton_iff.1 this.1).symm
    exact hb1 hbQ₁
  set z : E := a * b * a⁻¹ * b⁻¹ with hz
  have hzQ₁ : z ∈ pCoreOf 2 A₁ := by
    have : z = a * (b * a⁻¹ * b⁻¹) := by rw [hz]; group
    rw [this]
    exact Subgroup.mul_mem _ ha1 (G.v₁.Q_norm b hbA₁ a⁻¹ (Subgroup.inv_mem _ ha1))
  have hzQ₂ : z ∈ pCoreOf 2 A₂ := by
    have : z = (a * b * a⁻¹) * b⁻¹ := rfl
    rw [this]
    exact Subgroup.mul_mem _ (G.v₂.Q_norm a haA₂ b hb2) (Subgroup.inv_mem _ hb2)
  have hzN₁ : z ∈ N₁ := by
    have := G.v₁.comm_N a ha1 b hbA₁
    have e : a * (b * a * b⁻¹)⁻¹ = z := by rw [hz]; group
    rwa [e] at this
  have hzN₂ : z ∈ N₂ := by
    have := G.v₂.comm_N b hb2 a haA₂
    have e : b * (a * b * a⁻¹)⁻¹ = z⁻¹ := by rw [hz]; group
    rw [e] at this
    simpa using Subgroup.inv_mem _ this
  have hz1 : z ≠ 1 := by
    intro h1
    apply hab
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [← hz, h1, one_mul]
  have hzeq : z = ε₁ * ε₂ := by
    rcases G.R_four z ⟨hzQ₁, hzQ₂⟩ with h1 | h1 | h1 | h1
    · exact absurd h1 hz1
    · exact absurd (h1 ▸ hzN₁) G.v₁.ε_not_N
    · exact absurd (h1 ▸ hzN₂) G.v₂.ε_not_N
    · exact h1
  exact ⟨a, b, haN, ha2, hbN, hb1, hab, hzeq, hzeq ▸ hzN₁, hzeq ▸ hzN₂⟩

end Glob

end CFSG.Quasithin.F6.GoldAmS
