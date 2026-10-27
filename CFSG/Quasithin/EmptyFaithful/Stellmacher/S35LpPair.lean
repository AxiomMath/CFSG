module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpFin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp

open S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

@[expose] def PlaneAt {δ : Geo H M} (c : Ch.Chart δ) (l : Geo H M) : Prop :=
  ∀ ε : Geo H M, ε ∈ nbrs l → ε ≠ δ →
    c.img (Vn δ ⊓ Vn ε) = commW orth (Subgroup.zpowers (zc (c.Dl l))) ⊤

@[expose] def ZlAt {δ : Geo H M} (c : Ch.Chart δ) (l : Geo H M) : Prop :=
  c.img (Zv l) = Subgroup.zpowers (vp (fixPt (c.Dl l)))

omit [Finite G] in
theorem not_swap_of_neg (hneg : ¬ ClaimLP H M) {δ δ' : Geo H M} (hp : S34.PD δ δ')
    (c : Ch.Chart δ') {v : G} (hv : v ∈ Vn δ) (hvs : v ∈ stab δ') :
    ¬ (c.θ ⟨v, hvs⟩).IsSwap := fun hs =>
  hneg ⟨δ, δ', hp, v, hv, hvs, by
    rw [c.secIdx_eq_idx hvs]
    exact (idx_orth_eq_two_iff _).mpr hs⟩

theorem imageA (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m) {v : G} (hv : v ∈ Vn β)
    (hvs : v ∈ stab α') : c.θ ⟨v, hvs⟩ = 1 ∨ c.θ ⟨v, hvs⟩ = zc (c.Dl m) := by
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hb.1
  have hvi := back_Vn_le_inf hS hp hb hv
  have hmem : c.θ ⟨v, hvs⟩ ∈ c.Dl m := c.mem_bar_of_mem (a := v) hvi hvs
  have hcen : ∀ w ∈ commW orth (Subgroup.zpowers (zc (c.Dl m))) ⊤,
      orth.act (c.θ ⟨v, hvs⟩) w = w := by
    intro w hw
    rw [← hpl γ' hb.2.1 (back_ne hp hb)] at hw
    obtain ⟨x, hx, rfl⟩ := (c.mem_img_iff').mp hw
    refine (c.comm_mem_iff ⟨v, hvs⟩ x).mp ?_
    have hxγ : (x : G) ∈ Vn γ' := (Subgroup.mem_inf.mp hx).2
    have := back_comm_γ hS hp hb v hv x hxγ
    have e : v * (x : G) * v⁻¹ * (x : G)⁻¹ = 1 := by
      rw [this]
      group
    show v * (x : G) * v⁻¹ * (x : G)⁻¹ ∈ Zv α'
    rw [e]
    exact (Zv α').one_mem
  rcases cen_cases hD hmem hcen with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h (not_swap_of_neg hneg hp c hv hvs)

theorem exists_zc (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m) :
    ∃ v ∈ Vn β, ∃ hvs : v ∈ stab α', c.θ ⟨v, hvs⟩ = zc (c.Dl m) := by
  obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp hp.not_le
  have hvs : v ∈ stab α' := (Std.PD_Vn_le_stab hS hp).1 hv
  refine ⟨v, hv, hvs, ?_⟩
  rcases imageA hS hneg hp hb c hpl hv hvs with h | h
  · exact absurd ((c.ker_iff hS hp.vδ' ⟨v, hvs⟩).mp h) hvQ
  · exact h

theorem card_sup_le_of_comm {Y C : Subgroup G} (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y) :
    Nat.card ↥(Y ⊔ C) ≤ Nat.card ↥Y * Nat.card ↥C := by
  have h := EmptyFaithful.Stellmacher.OrdinaryProofs.card_sup_mul_card_inf_of_centralizes hC
  have hpos : 0 < Nat.card ↥(Y ⊓ C) := Nat.card_pos
  nlinarith

theorem central_comm (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {z y : G}
    (hz : z ∈ Zv δ) (hy : y ∈ stab δ) : y * z = z * y := by
  have := (Subgroup.mem_inf.mp (S34.Glob.central hS.glob δ hδ hz)).2
  exact Subgroup.mem_centralizer_iff.mp this y hy

theorem card_Zv_sup_le (hS : Sit H M S) (hp : S34.PD β α') :
    Nat.card ↥(Zv β ⊔ Zv α') ≤ 4 := by
  have hc : ∀ c ∈ Zv α', ∀ y ∈ Zv β, y * c = c * y := fun c hc y hy =>
    central_comm hS hp.vδ' hc (Std.Zv_le_stab_dist_S5 hS hp.vδ (by have := hp.dist_eq; omega) hy)
  have := card_sup_le_of_comm hc
  rwa [hS.cardZ5 β hp.vδ, hS.cardZ5 α' hp.vδ'] at this

theorem not_Vn_le_Qv (hS : Sit H M S) (hneg : ¬ ClaimLP H M) (hp : S34.PD β α')
    (hb : Back H M β α' m γ') (c : Ch.Chart α') (hpl : PlaneAt c m) : ¬ Vn α' ≤ Qv β := by
  intro hle
  obtain ⟨v, hv, hvs, hθ⟩ := exists_zc hS hneg hp hb c hpl
  have hD : Nat.card (c.Dl m) = 8 := c.card_Dl hS hb.1
  have hA : Subgroup.zpowers v ≤ stab α' := Subgroup.zpowers_le.mpr hvs
  have h1 := c.card_commSec hA
  rw [c.bar_zpowers hvs, hθ, card_commW_zc hD] at h1
  set K := commSec (Subgroup.zpowers v) (Zv α') (Vn α') with hK
  have hZK : Zv α' ≤ K := Ch.Chart.Zv_le_commSec _
  have hcard := Subgroup.relIndex_mul_card (H := Zv α') (K := K)
  rw [inf_eq_left.mpr hZK, h1, hS.cardZ5 α' hp.vδ'] at hcard
  have hKJ : K ≤ Zv β ⊔ Zv α' := by
    refine sup_le_sup_right ?_ _
    have h2 : ⁅Vn α', Subgroup.zpowers v⁆ ≤ ⁅Qv β, Vn β⁆ :=
      Subgroup.commutator_mono hle (Subgroup.zpowers_le.mpr hv)
    rw [Subgroup.commutator_comm (Qv β) (Vn β), Std.comm_Vn_Qv hS hp.vδ] at h2
    exact h2
  have := Subgroup.card_le_of_le hKJ
  have := card_Zv_sup_le hS hp
  omega

end S35.Lp

end F53.Stellmacher

end CFSG.Quasithin
