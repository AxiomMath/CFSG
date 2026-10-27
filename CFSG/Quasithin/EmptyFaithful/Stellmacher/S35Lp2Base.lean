module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35LpBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Plane
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Lp2

open S35.Ch2 S35.Fin S35.Lp
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}
  {β α' m γ' : Geo H M}

omit [Finite G] in
theorem fixSecIn_Zv_eq_Cb {δ : Geo H M} (hU : UC δ) (hZC : Zv δ ≤ Cb δ) {A : Subgroup G}
    (hA : A ≤ stab δ) : fixSecIn A (Zv δ) (Vn δ) = fixSecIn A (Cb δ) (Vn δ) := by
  unfold fixSecIn
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun hx => forall₂_congr fun a ha => ⟨fun h => hZC h, fun h => hU ?_⟩
  refine ⟨?_, h⟩
  have h1 : ⁅a, x⁆ ∈ ⁅stab δ, Vn δ⁆ := Subgroup.commutator_mem_commutator (hA ha) hx
  rw [Subgroup.commutator_comm] at h1
  simpa [commutatorElement_def] using h1

omit [Finite G] in
theorem secIdx_Zv_eq_Cb {δ : Geo H M} (hU : UC δ) (hZC : Zv δ ≤ Cb δ) {x : G}
    (hx : x ∈ stab δ) :
    secIdx (Subgroup.zpowers x) (Zv δ) (Vn δ) = secIdx (Subgroup.zpowers x) (Cb δ) (Vn δ) := by
  unfold secIdx
  rw [fixSecIn_Zv_eq_Cb hU hZC (Subgroup.zpowers_le.mpr hx)]

theorem Zv_le_Cb' (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) : Zv δ ≤ Cb δ :=
  S34.Zv_le_Cb hS.glob hδ

theorem hasTransp_iff {δ δ' : Geo H M} (hS : Sit H M S) (hp : S34.PD δ δ') (c : Chart2 δ')
    (hU : UC δ') {v : G} (hvs : v ∈ stab δ') :
    secIdx (Subgroup.zpowers v) (Zv δ') (Vn δ') = 2 ↔ (c.θ ⟨v, hvs⟩).IsSwap := by
  rw [secIdx_Zv_eq_Cb hU (Zv_le_Cb' hS hp.vδ') hvs, c.secIdx_eq_idx hvs,
    idx_orth_eq_two_iff]

theorem not_swap_of_neg (hS : Sit H M S) (hneg : ¬ ClaimLP H M) {δ δ' : Geo H M}
    (hp : S34.PD δ δ') (c : Chart2 δ') (hU : UC δ') {v : G} (hv : v ∈ Vn δ)
    (hvs : v ∈ stab δ') : ¬ (c.θ ⟨v, hvs⟩).IsSwap := fun hs =>
  hneg ⟨δ, δ', hp, v, hv, hvs, (hasTransp_iff hS hp c hU hvs).mpr hs⟩

theorem Vn_comm (hS : Sit H M S) (δ : Geo H M) {a b : G} (ha : a ∈ Vn δ) (hb : b ∈ Vn δ) :
    a * b = b * a :=
  congrArg Subtype.val ((Std.Vn_isElemAbelian hS δ).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem Vn_sq (hS : Sit H M S) (δ : Geo H M) {a : G} (ha : a ∈ Vn δ) : a * a = 1 := by
  rw [← pow_two]
  exact (Std.Vn_isElemAbelian hS δ).2 _ ha

theorem le_zpowers_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) {z : G} (hz : z ∈ Z)
    (hne : z ≠ 1) : Z ≤ Subgroup.zpowers z := by
  have hle : Subgroup.zpowers z ≤ Z := Subgroup.zpowers_le.mpr hz
  have h1 : orderOf z ≠ 1 := fun h => hne (orderOf_eq_one_iff.mp h)
  have h2 : 0 < orderOf z := orderOf_pos z
  have h3 : Nat.card Z ≤ Nat.card (Subgroup.zpowers z) := by
    rw [Nat.card_zpowers, hZ]
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle h3).symm.le

theorem card_sup_le_of_comm {Y C : Subgroup G} (hC : ∀ c ∈ C, ∀ y ∈ Y, y * c = c * y) :
    Nat.card ↥(Y ⊔ C) ≤ Nat.card ↥Y * Nat.card ↥C := by
  have h := EmptyFaithful.Stellmacher.OrdinaryProofs.card_sup_mul_card_inf_of_centralizes hC
  have hpos : 0 < Nat.card ↥(Y ⊓ C) := Nat.card_pos
  nlinarith

theorem central_comm (hS : Sit H M S) {δ : Geo H M} (hδ : vtype δ = false) {z y : G}
    (hz : z ∈ Zv δ) (hy : y ∈ stab δ) : y * z = z * y := by
  have := (Subgroup.mem_inf.mp (S34.Glob.central hS.glob δ hδ hz)).2
  exact Subgroup.mem_centralizer_iff.mp this y hy

omit [Finite G] in
theorem comm_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) {x y : G} (hx : x ∈ A)
    (hy : y ∈ B) : x * y = y * x := by
  have h1 : ⁅x, y⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

theorem exists_PD (hS : Sit H M S) : ∃ β α' : Geo H M, S34.PD β α' := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Geo H M, vtype δ = false := by
    obtain ⟨e, he⟩ := exists_adj (γ₀ (H ⊔ M) H M)
    have hne := vtype_ne_of_adj he
    by_cases hv : vtype (γ₀ (H ⊔ M) H M) = false
    · exact ⟨_, hv⟩
    · refine ⟨e, ?_⟩
      cases h : vtype e
      · rfl
      · exfalso
        apply hne
        rw [h]
        simpa using hv
  obtain ⟨l, hl⟩ := exists_adj δ
  have hl' : l ∈ nbrs δ := hl
  have hlt := Std.vtype_nbr_S5 hδ hl'
  obtain ⟨α', hc⟩ := exists_critData hS.glob.amalg (hS.glob.crit l hlt)
    (Std.mem_nbrs_symm.mpr hl' : δ ∈ nbrs l)
  obtain ⟨-, -, -, -, hp⟩ := Std.Zv_not_le_Qv_crit hS hc hlt
  exact ⟨δ, α', hp⟩

theorem Wb_le_stab_γ (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ') :
    Wb β ≤ stab γ' := by
  refine Std.Wb_le fun ρ hρ => Std.Vn_le_stab_dist hS ?_
  have h1 := dist_triangle rfl ρ β γ'
  have h2 := back_dist_γ hp hb
  omega

end S35.Lp2

end F53.Stellmacher

end CFSG.Quasithin
