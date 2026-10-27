module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35E8Th
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.E8

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {δ : Geo H M}

@[expose] def Goal (δ : Geo H M) (Y Vb : Subgroup G) : Prop :=
  ∃ A B : Subgroup G, A ≤ Vn δ ∧ B ≤ Vn δ ∧ A ⊔ B = Vn δ ∧ ⁅Vb, A⁆ ≤ Zv δ ∧
    ⁅Y, B⁆ ≤ Zv δ ⊔ ⁅Vb, B⁆ ∧ ∀ K : Subgroup G, K ≤ Vb → ¬ K ≤ Qv δ → ⁅B, K⁆ ≠ ⊥

omit [Finite G] in
theorem cm_close (c : Ch.Chart δ) {y v b : G} (hy : y ∈ stab δ) (hv : v ∈ stab δ)
    (hb : b ∈ Vn δ) (h : orth.act (th c y) (pg c b) = orth.act (th c v) (pg c b)) :
    (y * b * y⁻¹ * b⁻¹) * (v * b * v⁻¹ * b⁻¹)⁻¹ ∈ Zv δ := by
  have e : (y * b * y⁻¹ * b⁻¹) * (v * b * v⁻¹ * b⁻¹)⁻¹ = (y * b * y⁻¹) * (v * b * v⁻¹)⁻¹ := by
    group
  rw [e]
  have h1 := Ch.conj_mem_Vn hy hb
  have h2 := Ch.conj_mem_Vn hv hb
  exact (pg_eq_iff c h1 h2).mp (by rw [pg_conj c hy hb, pg_conj c hv hb, h])

omit [Finite G] in
theorem comm_le_of_cases (c : Ch.Chart δ) {Y Vb B : Subgroup G} (hY : Y ≤ stab δ)
    (hV : Vb ≤ stab δ) (hB : B ≤ Vn δ)
    (h : ∀ y ∈ Y, ∀ b ∈ B, orth.act (th c y) (pg c b) = pg c b ∨
      ∃ v ∈ Vb, orth.act (th c y) (pg c b) = orth.act (th c v) (pg c b)) :
    ⁅Y, B⁆ ≤ Zv δ ⊔ ⁅Vb, B⁆ := by
  rw [Subgroup.commutator_le]
  intro y hy b hb
  have e : ⁅y, b⁆ = y * b * y⁻¹ * b⁻¹ := commutatorElement_def y b
  rw [e]
  rcases h _ hy _ hb with h1 | ⟨v, hv, h1⟩
  · exact Subgroup.mem_sup_left ((comm_iff c (hY hy) (hB hb)).mpr h1)
  · have h2 := cm_close c (hY hy) (hV hv) (hB hb) h1
    have h3 : v * b * v⁻¹ * b⁻¹ ∈ ⁅Vb, B⁆ := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hv hb
    have e2 : y * b * y⁻¹ * b⁻¹ =
        ((y * b * y⁻¹ * b⁻¹) * (v * b * v⁻¹ * b⁻¹)⁻¹) * (v * b * v⁻¹ * b⁻¹) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup h2 h3

omit [Finite G] in
theorem act_fixed_of_comm_eq_one (c : Ch.Chart δ) {u b : G} (hu : u ∈ stab δ) (hb : b ∈ Vn δ)
    (h : ⁅b, u⁆ = 1) : orth.act (th c u) (pg c b) = pg c b := by
  refine (comm_iff c hu hb).mp ?_
  have : u * b * u⁻¹ * b⁻¹ = ⁅u, b⁆ := (commutatorElement_def u b).symm
  rw [this, ← commutatorElement_inv, h, inv_one]
  exact (Zv δ).one_mem

theorem goal_of_image (hS : Sit H M S) (hδ : vtype δ = false) (c : Ch.Chart δ)
    {Y Vb : Subgroup G} (hY : Y ≤ stab δ) (hV : Vb ≤ stab δ)
    (h : ∀ y ∈ Y, ∃ v ∈ Vb, th c y = th c v) : Goal δ Y Vb := by
  refine ⟨⊥, Vn δ, bot_le, le_rfl, bot_sup_eq _, ?_, ?_, ?_⟩
  · rw [Subgroup.commutator_bot_right]; exact bot_le
  · refine comm_le_of_cases c hY hV le_rfl fun y hy b hb => Or.inr ?_
    obtain ⟨v, hv, hyv⟩ := h y hy
    exact ⟨v, hv, by rw [hyv]⟩
  · intro K hK hKQ hbot
    have : ∃ u ∈ K, u ∉ Qv δ := by
      by_contra hcon
      push Not at hcon
      exact hKQ hcon
    obtain ⟨u, huK, huQ⟩ := this
    have hus : u ∈ stab δ := hV (hK huK)
    have h1 : th c u ≠ 1 := fun h' => huQ ((th_eq_one_iff c hS hδ hus).mp h')
    refine h1 (S35.Fin.eq_one_of_act_eq_self fun w => ?_)
    obtain ⟨b, hb, rfl⟩ := pg_surj c w
    have h3 : ⁅b, u⁆ ∈ (⊥ : Subgroup G) := hbot ▸ Subgroup.commutator_mem_commutator hb huK
    exact act_fixed_of_comm_eq_one c hus hb (Subgroup.mem_bot.mp h3)

end S35.E8

end F53.Stellmacher

end CFSG.Quasithin
