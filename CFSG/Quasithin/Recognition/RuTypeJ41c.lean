module

public import CFSG.Quasithin.Recognition.RuTypeJ41b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace RuDataM

variable {G : Type} [Group G] (M : RuDataM G)

noncomputable abbrev Q5 {b : G} (hbH : b ∈ ruH M.T) : Subgroup G :=
  ((M.Q5bar ⟨b, hbH⟩).comap (QuotientGroup.mk' M.UQ)).map (ruQ M.T).subtype

theorem mem_Q5 {b : G} (hbH : b ∈ ruH M.T) {x : G} :
    x ∈ M.Q5 hbH ↔ ∃ hx : x ∈ ruQ M.T, ((⟨x, hx⟩ : ruQ M.T) : M.Qbar) ∈ M.Q5bar ⟨b, hbH⟩ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem Q5_le_Q {b : G} (hbH : b ∈ ruH M.T) : M.Q5 hbH ≤ ruQ M.T := Subgroup.map_subtype_le _

theorem U_le_Q5 {b : G} (hbH : b ∈ ruH M.T) : ruU M.L M.T ≤ M.Q5 hbH := fun u hu => by
  refine (M.mem_Q5 hbH).mpr ⟨M.U_le_Q hu, ?_⟩
  have : ((⟨u, M.U_le_Q hu⟩ : ruQ M.T) : M.Qbar) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hu)
  rw [this]
  exact one_mem _

theorem actQ_of_mem_Q {q : G} (hq : q ∈ ruQ M.T) (a : M.Qbar) :
    M.actQ ⟨q, pCoreOf_le 2 _ hq⟩ a = a := by
  induction a using QuotientGroup.induction_on with
  | H x =>
  rw [M.actQ_mk]
  have h := M.Qbar_comm ((⟨q, hq⟩ : ruQ M.T) : M.Qbar) (x : M.Qbar)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h
  rw [QuotientGroup.eq]
  have e : ((M.conjQ ⟨q, pCoreOf_le 2 _ hq⟩ x : ruQ M.T))⁻¹ * x =
      (⟨q, hq⟩ : ruQ M.T) * ((⟨q, hq⟩ * x)⁻¹ * (x * ⟨q, hq⟩)) * (⟨q, hq⟩ : ruQ M.T)⁻¹ := by
    apply Subtype.ext
    show ((q : G) * x * q⁻¹)⁻¹ * x = (q : G) * (((q : G) * x)⁻¹ * (x * q)) * (q : G)⁻¹
    group
  rw [e]
  exact (M.UQ_normal).conj_mem _ h _

theorem dQ_pow_range_le (h : ruH M.T) (k : ℕ) : (M.dQ (h ^ k)).range ≤ (M.dQ h).range := by
  induction k with
  | zero =>
    rintro _ ⟨a, rfl⟩
    rw [pow_zero, M.dQ_apply, M.actQ_one_apply, mul_inv_cancel]
    exact one_mem _
  | succ k ih =>
    rintro _ ⟨a, rfl⟩
    rw [M.dQ_apply]
    have e : M.actQ (h ^ (k + 1)) a * a⁻¹ =
        M.dQ h (M.actQ (h ^ k) a) * M.dQ (h ^ k) a := by
      rw [M.dQ_apply, M.dQ_apply, pow_succ', M.actQ_mul_apply]
      group
    rw [e]
    exact mul_mem ⟨_, rfl⟩ (ih ⟨a, rfl⟩)

theorem dQ_mul_Q (h : ruH M.T) {q : G} (hq : q ∈ ruQ M.T) :
    M.dQ (h * ⟨q, pCoreOf_le 2 _ hq⟩) = M.dQ h := by
  refine MonoidHom.ext fun a => ?_
  rw [M.dQ_apply, M.dQ_apply, M.actQ_mul_apply, M.actQ_of_mem_Q hq]

theorem actQ_dQ (g h : ruH M.T) (a : M.Qbar) :
    M.actQ g (M.dQ h a) = M.dQ (g * h * g⁻¹) (M.actQ g a) := by
  rw [M.dQ_apply, M.dQ_apply, map_mul, map_inv, M.actQ_mul_apply, M.actQ_mul_apply,
    ← M.actQ_mul_apply g⁻¹ g, inv_mul_cancel, M.actQ_one_apply]

theorem Q5bar_conj {b : G} (hbH : b ∈ ruH M.T) {h : G} (hh : h ∈ ruH M.T) {k : ℕ} {q : G}
    (hq : q ∈ ruQ M.T) (hhb : h * b * h⁻¹ = b ^ k * q) {a : M.Qbar}
    (ha : a ∈ M.Q5bar ⟨b, hbH⟩) : M.actQ ⟨h, hh⟩ a ∈ M.Q5bar ⟨b, hbH⟩ := by
  obtain ⟨c, rfl⟩ := ha
  rw [M.actQ_dQ]
  have e : (⟨h, hh⟩ : ruH M.T) * ⟨b, hbH⟩ * ⟨h, hh⟩⁻¹ =
      ⟨b, hbH⟩ ^ k * ⟨q, pCoreOf_le 2 _ hq⟩ := Subtype.ext (by simpa using hhb)
  rw [e, M.dQ_mul_Q _ hq]
  exact M.dQ_pow_range_le _ k ⟨_, rfl⟩

theorem conj_mem_Q5 {b : G} (hbH : b ∈ ruH M.T) {h : G} (hh : h ∈ ruH M.T) {k : ℕ} {q : G}
    (hq : q ∈ ruQ M.T) (hhb : h * b * h⁻¹ = b ^ k * q) {x : G} (hx : x ∈ M.Q5 hbH) :
    h * x * h⁻¹ ∈ M.Q5 hbH := by
  obtain ⟨hxQ, hxb⟩ := (M.mem_Q5 hbH).mp hx
  have hmem : h * x * h⁻¹ ∈ ruQ M.T := M.conj_mem_Q hh hxQ
  refine (M.mem_Q5 hbH).mpr ⟨hmem, ?_⟩
  have := M.Q5bar_conj hbH hh hq hhb hxb
  rwa [M.actQ_mk] at this

variable [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5

theorem card_Q5 : Nat.card (M.Q5 hbH) = 2 ^ 9 := by
  rw [Subgroup.card_map_of_injective (ruQ M.T).subtype_injective]
  have hpre : (QuotientGroup.mk : ruQ M.T → M.Qbar) ⁻¹' (M.Q5bar ⟨b, hbH⟩ : Set M.Qbar) =
      (((M.Q5bar ⟨b, hbH⟩).comap (QuotientGroup.mk' M.UQ)) : Set (ruQ M.T)) := rfl
  have h := QuotientGroup.card_preimage_mk M.UQ (M.Q5bar ⟨b, hbH⟩ : Set M.Qbar)
  rw [hpre] at h
  have h1 : Nat.card (M.Q5bar ⟨b, hbH⟩ : Set M.Qbar) = 16 := card_Q5bar hbH hb5
  rw [h1, card_subgroupOf_of_le M.U_le_Q, M.toRuData.card_U] at h
  have h2 : Nat.card (((M.Q5bar ⟨b, hbH⟩).comap (QuotientGroup.mk' M.UQ)) : Set (ruQ M.T)) =
      Nat.card ((M.Q5bar ⟨b, hbH⟩).comap (QuotientGroup.mk' M.UQ)) := rfl
  rw [h2] at h
  rw [h]
  norm_num

theorem Q5_inf_HC : M.Q5 hbH ⊓ M.HC = ruU M.L M.T := by
  refine le_antisymm ?_ (le_inf (M.U_le_Q5 hbH) M.U_le_HC)
  rintro x ⟨hx5, hxC⟩
  obtain ⟨hxQ, hxb⟩ := (M.mem_Q5 hbH).mp hx5
  have hxC' : ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) ∈ M.HCbar := (M.mem_HCbar_mk _).mpr hxC
  have h1 : ((⟨x, hxQ⟩ : ruQ M.T) : M.Qbar) ∈ M.Q5bar ⟨b, hbH⟩ ⊓ M.HCbar := ⟨hxb, hxC'⟩
  rw [Q5bar_inf_HCbar hbH hb5, Subgroup.mem_bot, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  exact h1

theorem Q5bar_isComplement :
    Subgroup.IsComplement' (M.Q5bar ⟨b, hbH⟩) M.HCbar :=
  Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [card_Q5bar hbH hb5, M.card_HCbar, M.card_Qbar])
    (disjoint_iff.mpr (Q5bar_inf_HCbar hbH hb5))

theorem exists_Q5_mul_HC {q : G} (hq : q ∈ ruQ M.T) :
    ∃ a ∈ M.Q5 hbH, ∃ c ∈ M.HC, q = a * c := by
  obtain ⟨⟨⟨x, hx⟩, ⟨y, hy⟩⟩, hxy⟩ :=
    ((Q5bar_isComplement hbH hb5).existsUnique ((⟨q, hq⟩ : ruQ M.T) : M.Qbar)).exists
  obtain ⟨c, hc, rfl⟩ := hy
  have hcG : (c : G) ∈ M.HC := Subgroup.mem_subgroupOf.mp hc
  have hxy' : x * (c : M.Qbar) = ((⟨q, hq⟩ : ruQ M.T) : M.Qbar) := hxy
  refine ⟨q * (c : G)⁻¹, ?_, c, hcG, by group⟩
  have hmem : q * (c : G)⁻¹ ∈ ruQ M.T := mul_mem hq (inv_mem c.2)
  refine (M.mem_Q5 hbH).mpr ⟨hmem, ?_⟩
  have e : ((⟨q * (c : G)⁻¹, hmem⟩ : ruQ M.T) : M.Qbar) = x := by
    have : (⟨q * (c : G)⁻¹, hmem⟩ : ruQ M.T) = ⟨q, hq⟩ * c⁻¹ := rfl
    rw [this, QuotientGroup.mk_mul, ← hxy', QuotientGroup.mk_inv, mul_inv_cancel_right]
  rw [e]
  exact hx

end Five

end RuDataM

end CFSG.Quasithin.RuType
