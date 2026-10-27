module

public import CFSG.Quasithin.Recognition.RuTypeJ41d
public import CFSG.Quasithin.Recognition.RuTypeJ41a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped MatrixGroups

namespace SL3

@[expose] def IsM2 (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Prop := A 2 0 = 0 ∧ A 2 1 = 0

instance : DecidablePred IsM2 := fun A => inferInstanceAs (Decidable (A 2 0 = 0 ∧ A 2 1 = 0))

theorem IsM2.add {A B : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : IsM2 A) (hB : IsM2 B) :
    IsM2 (A + B) := by
  obtain ⟨h1, h2⟩ := hA
  obtain ⟨h3, h4⟩ := hB
  simp [IsM2, h1, h2, h3, h4]

theorem isM2_zero : IsM2 0 := by decide

theorem isM2_of_isRow0 {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (h : IsRow0 A) : IsM2 A :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1⟩

theorem stAct_Pl_isM2 : ∀ g ∈ Pl, ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsM2 A →
    IsM2 (stAct g A) := by
  decide +kernel

theorem comm_R2m_isM2 : ∀ r ∈ R2m, ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsTraceZero A →
    IsM2 (stAct r A + A) := by
  decide +kernel

theorem comm_R0_gpl_isM2 : ∀ r ∈ R0, ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), IsRow0 A →
    IsM2 (stAct r (stAct gpl A) + stAct gpl A) := by
  decide +kernel

theorem isM2_b0_add : IsM2 (!![1, 0, 0; 0, 1, 1; 0, 1, 0] + !![1, 0, 0; 0, 0, 1; 0, 1, 1]) := by
  decide

theorem card_M2 : Fintype.card {A : Matrix (Fin 3) (Fin 3) (ZMod 2) // IsM2 A ∧ IsTraceZero A} =
    64 := by
  decide +kernel

end SL3

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G)

@[expose] def W : Subgroup G where
  carrier := {x | ∃ hx : x ∈ ruS M.L, SL3.IsM2 (Multiplicative.toAdd (M.χ ⟨x, hx⟩))}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [show (⟨a * b, mul_mem ha hb⟩ : ruS M.L) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, M.toAdd_χ_mul]
    exact ha'.add hb'
  one_mem' := ⟨(ruS M.L).one_mem, by
    rw [show (⟨1, (ruS M.L).one_mem⟩ : ruS M.L) = 1 from rfl, map_one, toAdd_one]
    exact SL3.isM2_zero⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [show (⟨a⁻¹, inv_mem ha⟩ : ruS M.L) = (⟨a, ha⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv]
    exact ha'

theorem W_le_S : M.W ≤ ruS M.L := fun _ ⟨hx, _⟩ => hx

theorem conj_mem_W {g x : G} (hg : g ∈ M.G2) (hx : x ∈ M.W) : g * x * g⁻¹ ∈ M.W := by
  obtain ⟨hgL, hgP⟩ := mem_pullL.mp hg
  obtain ⟨hxS, hxM⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hgL) x).mp hxS, ?_⟩
  have h := M.χ_conj ⟨g, hgL⟩ ⟨x, hxS⟩
  simp only at h
  rw [h]
  exact SL3.stAct_Pl_isM2 _ hgP _ hxM

theorem comm_mem_W {r s : G} (hr : r ∈ M.R2) (hs : s ∈ ruS M.L) : r * s * r⁻¹ * s⁻¹ ∈ M.W := by
  obtain ⟨hrL, hrP⟩ := mem_pullL.mp hr
  have hrs : r * s * r⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hrL) s).mp hs
  refine ⟨mul_mem hrs (inv_mem hs), ?_⟩
  rw [show (⟨r * s * r⁻¹ * s⁻¹, mul_mem hrs (inv_mem hs)⟩ : ruS M.L) =
    ⟨r * s * r⁻¹, hrs⟩ * (⟨s, hs⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv]
  have h := M.χ_conj ⟨r, hrL⟩ ⟨s, hs⟩
  simp only at h
  rw [h]
  exact SL3.comm_R2m_isM2 _ hrP _ (M.χ_trace _)

variable [Finite G]

theorem card_W : Nat.card M.W = 2 ^ 9 := by
  rw [M.card_preimage M.W (fun A => SL3.IsM2 A ∧ IsTraceZero A) M.W_le_S
    (fun x hx => ⟨fun ⟨_, h⟩ => ⟨h, M.χ_trace _⟩, fun h => ⟨hx, h.1⟩⟩) (fun A hA => hA.2),
    Nat.card_eq_fintype_card, SL3.card_M2]
  norm_num

theorem U_le_W : ruU M.L M.T ≤ M.W := fun _ hu =>
  ⟨M.U_le_S hu, SL3.isM2_of_isRow0 ((M.mem_U_iff (M.U_le_S hu)).mp hu)⟩

theorem Ual_le_W : M.Ual ≤ M.W := by
  intro x hx
  have h0 : (M.gel : G)⁻¹ * x * M.gel ∈ ruU M.L M.T := M.mem_conjU.mp hx
  have e : x = (M.gel : G) * ((M.gel : G)⁻¹ * x * M.gel) * (M.gel : G)⁻¹ := by group
  rw [e]
  exact M.conj_mem_W M.gel_mem_G2 (M.U_le_W h0)

theorem comm_Q_Ual_mem_W {q u : G} (hq : q ∈ ruQ M.T) (hu : u ∈ M.Ual) :
    u * (q * u⁻¹ * q⁻¹) ∈ M.W := by
  have hqL : q ∈ M.L := (M.Q_le_LT1.trans M.LT1_le_L) hq
  have hqR0 : M.θ ⟨q, hqL⟩ ∈ SL3.R0 := by
    rw [← M.θQ_eq]
    exact ⟨⟨q, hqL⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  have huS : u ∈ ruS M.L := M.Ual_le_S hu
  have hu' : q * u⁻¹ * q⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L hqL) _).mp (inv_mem huS)
  refine ⟨mul_mem huS hu', ?_⟩
  rw [show (⟨u * (q * u⁻¹ * q⁻¹), mul_mem huS hu'⟩ : ruS M.L) =
    ⟨u, huS⟩ * ⟨q * u⁻¹ * q⁻¹, hu'⟩ from rfl, M.toAdd_χ_mul]
  have h := M.χ_conj ⟨q, hqL⟩ ⟨u⁻¹, inv_mem huS⟩
  simp only at h
  rw [h, show (⟨u⁻¹, inv_mem huS⟩ : ruS M.L) = (⟨u, huS⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_inv]
  have h0 : (M.gel : G)⁻¹ * u * M.gel ∈ ruU M.L M.T := M.mem_conjU.mp hu
  have h0S := M.U_le_S h0
  have hrow := (M.mem_U_iff h0S).mp h0
  have hc := M.χ_conj M.gel ⟨(M.gel : G)⁻¹ * u * M.gel, h0S⟩
  simp only at hc
  have hc' : Multiplicative.toAdd (M.χ ⟨u, huS⟩) =
      stAct SL3.gpl (Multiplicative.toAdd (M.χ ⟨(M.gel : G)⁻¹ * u * M.gel, h0S⟩)) := by
    rw [← M.θ_gel, ← hc]
    congr 3
    group
  rw [hc', add_comm]
  exact SL3.comm_R0_gpl_isM2 _ hqR0 _ hrow

theorem Q0_le_W : M.Q0 ≤ M.W := by
  set t := ((⟨M.t1el, M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)⟩ : ruQ M.T) : M.Qbar)
  set x0 := M.dQ ⟨M.nel, M.nel_mem_H⟩ t
  have htC : t ∈ M.HCbar := M.t1bar_mem_HCbar
  have hx0C : x0 ∈ M.HCbar := by
    show M.actQ _ t * t⁻¹ ∈ M.HCbar
    exact mul_mem (M.actQ_mem_HCbar _ htC) (inv_mem htC)
  have hx0 : x0 ∈ M.Q0bar := by
    refine ⟨hx0C, ?_⟩
    show M.dQ ⟨M.nel, M.nel_mem_H⟩ x0 = 1
    rw [M.dQ_apply, mul_inv_eq_one]
    show M.actQ _ (M.actQ _ t * t⁻¹) = M.actQ _ t * t⁻¹
    rw [map_mul, map_inv, M.actQ_nel_nel htC]
    have hsq : ∀ y : M.Qbar, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (M.Qbar_sq y)
    rw [hsq t, hsq (M.actQ _ t), M.Qbar_comm]
  have hx01 : x0 ≠ 1 := M.dQ_nel_t1bar_ne_one
  have hzp : Subgroup.zpowers x0 = M.Q0bar := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx0) ?_
    rw [M.card_Q0bar, Nat.card_zpowers]
    have h2 : x0 ^ 2 = 1 := by rw [pow_two]; exact M.Qbar_sq x0
    have := orderOf_eq_prime h2 hx01
    rw [this]
  have ht1S := M.t1el_mem_S
  have hnt : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ ∈ ruS M.L :=
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 M.L M.nel.2) _).mp ht1S
  have hcW : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ M.W := by
    refine ⟨mul_mem hnt (inv_mem ht1S), ?_⟩
    rw [show (⟨(M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹, mul_mem hnt (inv_mem ht1S)⟩ :
      ruS M.L) = ⟨_, hnt⟩ * (⟨M.t1el, ht1S⟩ : ruS M.L)⁻¹ from rfl, M.toAdd_χ_mul, M.toAdd_χ_inv]
    have h := M.χ_conj M.nel ⟨M.t1el, ht1S⟩
    simp only at h
    rw [h, M.θ_nel, M.χ_t1el, SL3.n0_b0mat]
    exact SL3.isM2_b0_add
  intro q hq
  obtain ⟨hqQ, hq0⟩ := M.mem_Q0.mp hq
  rw [← hzp] at hq0
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hq0
  have hx2 : x0 ^ 2 = 1 := by rw [pow_two]; exact M.Qbar_sq x0
  have ho : orderOf x0 = 2 := orderOf_eq_prime hx2 hx01
  have hk' : x0 ^ k = 1 ∨ x0 ^ k = x0 := by
    rw [← zpow_mod_orderOf, ho]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  rw [hk] at hk'
  rcases hk' with h1 | h1
  · rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact M.U_le_W h1
  · have hcQ : (M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹ ∈ ruQ M.T :=
      mul_mem (M.conj_mem_Q M.nel_mem_H (M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)))
        (inv_mem (M.HC_le_Q (M.HB_le_HC M.t1el_mem_HB)))
    have e : x0 = ((⟨(M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹, hcQ⟩ : ruQ M.T) :
        M.Qbar) := rfl
    rw [e, M.mk_eq_mk_iff] at h1
    have hq' : q = ((M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹) *
        (((M.nel : G) * M.t1el * (M.nel : G)⁻¹ * M.t1el⁻¹)⁻¹ * q) := by group
    rw [hq']
    exact mul_mem hcW (M.U_le_W (by simpa using (inv_mem h1)))

theorem Q5_le_L {b : G} (hbH : b ∈ ruH M.T) : M.Q5 hbH ≤ M.L :=
  (M.Q5_le_Q hbH).trans (M.Q_le_LT1.trans M.LT1_le_L)

theorem card_Q5_inf_S
    {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5) :
    Nat.card ↥(M.Q5 hbH ⊓ ruS M.L) = 2 ^ 7 := by
  set f : M.Q5 hbH →* SL(3, ZMod 2) := M.θ.comp (Subgroup.inclusion (M.Q5_le_L hbH))
  have h := Subgroup.card_ker_mul_card_range f
  have hS : ∀ (x : G) (hx : x ∈ M.L), M.θ ⟨x, hx⟩ = 1 ↔ x ∈ ruS M.L := by
    intro x hx
    have : M.θ ⟨x, hx⟩ = 1 ↔ (⟨x, hx⟩ : M.L) ∈ M.θ.ker := Iff.rfl
    rw [this, M.θ_ker, Subgroup.mem_subgroupOf]
  have hker : Nat.card f.ker = Nat.card ↥(M.Q5 hbH ⊓ ruS M.L) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (hS _ _).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (hS _ _).mpr y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : f.range = SL3.R0 := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [← M.θQ_eq]
      exact ⟨⟨x.1, M.Q5_le_L hbH x.2⟩, Subgroup.mem_subgroupOf.mpr (M.Q5_le_Q hbH x.2), rfl⟩
    · intro r hr
      rw [← M.θQ_eq] at hr
      obtain ⟨y, hy, rfl⟩ := hr
      obtain ⟨a, ha, c, hc, hac⟩ := exists_Q5_mul_HC hbH hb5 (Subgroup.mem_subgroupOf.mp hy)
      refine ⟨⟨a, ha⟩, ?_⟩
      have hcL : c ∈ M.L := M.toRuData.S_le_L (M.HC_le_S hc)
      have hc1 : M.θ ⟨c, hcL⟩ = 1 := (hS c hcL).mpr (M.HC_le_S hc)
      have e : y = ⟨a, M.Q5_le_L hbH ha⟩ * ⟨c, hcL⟩ := Subtype.ext hac
      show M.θ ⟨a, M.Q5_le_L hbH ha⟩ = M.θ y
      rw [e, map_mul, hc1, mul_one]
  rw [hker, hrange, SL3.card_R0, card_Q5 hbH hb5] at h
  omega

theorem Q5_inf_S_le_W : M.Q5 M.b5el_mem_H ⊓ ruS M.L ≤ M.W := by
  have hb5 := M.orderOf_b5el
  set X : Subgroup G := (((M.dQ ⟨M.vel, M.vel_mem_H⟩).range).comap
    (QuotientGroup.mk' M.UQ)).map (ruQ M.T).subtype
  have hvb : M.vel * M.b5el * M.vel⁻¹ = M.b5el ^ 4 * 1 := by
    rw [M.vel_inv_b5el, mul_one]
    have h5 : M.b5el ^ 5 = 1 := pow_five_of_orderOf hb5
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, h5]
  have hXQ5 : X ≤ M.Q5 M.b5el_mem_H := by
    rintro _ ⟨x, hx, rfl⟩
    refine (M.mem_Q5 M.b5el_mem_H).mpr ⟨x.2, ?_⟩
    have hrange := dQ_range_le_Q5bar M.b5el_mem_H hb5 M.vel_mem_K (one_mem _) hvb
    exact hrange hx
  have hXW : X ≤ M.W := by
    rintro _ ⟨x, ⟨a, ha⟩, rfl⟩
    induction a using QuotientGroup.induction_on with
    | H a =>
    have ha' : M.dQ ⟨M.vel, M.vel_mem_H⟩ (a : M.Qbar) = (x : M.Qbar) := ha
    rw [M.dQ_apply, M.actQ_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      M.mk_eq_mk_iff] at ha'
    have hc := M.comm_Q_Ual_mem_W a.2 M.vel_mem_Ual
    have e : (x : G) = (M.vel * (a * M.vel⁻¹ * (a : G)⁻¹)) *
        ((M.vel * a * M.vel⁻¹ * (a : G)⁻¹)⁻¹ * x) := by group
    show (x : G) ∈ M.W
    rw [e]
    refine mul_mem hc (M.U_le_W ?_)
    have : ((M.conjQ ⟨M.vel, M.vel_mem_H⟩ a * a⁻¹ : ruQ M.T) : G) =
        M.vel * a * M.vel⁻¹ * (a : G)⁻¹ := rfl
    rw [← this]
    exact ha'
  have hcard : 2 ^ 7 ≤ Nat.card X := by
    rw [Subgroup.card_map_of_injective (ruQ M.T).subtype_injective]
    have h := QuotientGroup.card_preimage_mk M.UQ
      ((M.dQ ⟨M.vel, M.vel_mem_H⟩).range : Set M.Qbar)
    have hpre : (QuotientGroup.mk : ruQ M.T → M.Qbar) ⁻¹'
        ((M.dQ ⟨M.vel, M.vel_mem_H⟩).range : Set M.Qbar) =
        ((((M.dQ ⟨M.vel, M.vel_mem_H⟩).range).comap (QuotientGroup.mk' M.UQ)) :
          Set (ruQ M.T)) := rfl
    rw [hpre, card_subgroupOf_of_le M.U_le_Q, M.toRuData.card_U] at h
    have h4 := M.four_le_card_dQ_range M.vel_mem_H M.vel_not_mem_Q
    have h1 : Nat.card (((M.dQ ⟨M.vel, M.vel_mem_H⟩).range : Set M.Qbar)) =
        Nat.card (M.dQ ⟨M.vel, M.vel_mem_H⟩).range := rfl
    have h2 : Nat.card ((((M.dQ ⟨M.vel, M.vel_mem_H⟩).range).comap
        (QuotientGroup.mk' M.UQ)) : Set (ruQ M.T)) =
        Nat.card (((M.dQ ⟨M.vel, M.vel_mem_H⟩).range).comap (QuotientGroup.mk' M.UQ)) := rfl
    rw [h1, h2] at h
    rw [h]
    omega
  have hle : X ≤ M.Q5 M.b5el_mem_H ⊓ ruS M.L := le_inf hXQ5 (hXW.trans M.W_le_S)
  have heq : X = M.Q5 M.b5el_mem_H ⊓ ruS M.L :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [M.card_Q5_inf_S M.b5el_mem_H hb5]; exact hcard)
  rw [← heq]
  exact hXW

end RuDataM

end CFSG.Quasithin.RuType
