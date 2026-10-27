module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56a3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cMB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColMod
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35S6T
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35StdA3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.S6

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open S35.C56 S35.C56.Six

theorem mem_Zv_of_fixed (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) {u : G} (hu : u ∈ Zv l)
    (hfix : ∀ p ∈ stab β ⊓ stab l, p * u * p⁻¹ * u⁻¹ = 1) : u ∈ Zv β := by
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  obtain ⟨g, hgQ, hgl⟩ := Set.not_subset.mp (Std.Q_not_le hS hβ hl)
  have hgs : g ∈ stab β ⊓ stab l :=
    ⟨pCoreOf_le 2 _ hgQ, Std.Qv_le_stab hS hl hgQ⟩
  have hedge := (S34.aon_edge hS.glob hβ hl (g := g) ⟨hgs.2, hgs.1⟩).2 hgl
  let T : Subgroup G := Zv l ⊓ Subgroup.centralizer ({g} : Set G)
  have hZT : Zv β ≤ T := by
    intro z hz
    refine ⟨Std.Zv_le_Zv_of_nbr hS hβ hl hz, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    exact (Subgroup.mem_centralizer_iff.mp (Std.Zv_central hS hβ hz).2) g hgs.1
  have hTne : T ≠ Zv l := by
    intro hT
    have hle : Zv l ≤ Subgroup.centralizer ({g} : Set G) := hT ▸ inf_le_right
    have hbot : ⁅Zv l, Subgroup.zpowers g⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hc : Commute a g := ((Subgroup.mem_centralizer_iff.mp (hle ha) g
        (Set.mem_singleton g)).symm)
      exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr
        (hc.zpow_right n))
    rw [hedge] at hbot
    have h2 := hS.cardZ5 β hβ
    rw [hbot, Subgroup.card_bot] at h2
    omega
  have hTle : T ≤ Zv l := inf_le_left
  have hdvd : Nat.card T ∣ 4 := by
    have := Subgroup.card_dvd_of_le hTle
    rwa [hS.cardZ3 l hlt] at this
  have h4 : Nat.card T ≠ 4 := fun h4 => hTne
    (Subgroup.eq_of_le_of_card_ge hTle (by rw [hS.cardZ3 l hlt, h4]))
  have hZ2 := hS.cardZ5 β hβ
  have hle2 : Nat.card T ≤ 2 := by
    have h4' : Nat.card T ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card T := Nat.card_pos
    interval_cases h : Nat.card T <;> simp_all
  have hTeq : Zv β = T := Subgroup.eq_of_le_of_card_ge hZT (by rw [hZ2]; exact hle2)
  rw [hTeq]
  refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact commutatorElement_eq_one_iff_mul_comm.mp (hfix g hgs)

theorem false_of_CVQ_index (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false)
    (hC : (CVQ β).relIndex (Vn β) ≤ 2) : False := by
  have hq := quot_five hS hβ
  have horth : IsOrthSec (stab β) (S34.Cb β) (Vn β) := hS.orth β hβ
  have h16 := IsOrthSec.relIndex_eq horth
  have hCn := stab_le_normalizer_CVQ β
  have hCbn : stab β ≤ Subgroup.normalizer (S34.Cb β : Set G) := S34.bl12_stab_le_normalizer_Cb β
  have hCV : CVQ β ≤ Vn β := inf_le_left
  have hCbV : S34.Cb β ≤ Vn β := inf_le_left
  have hVn : stab β ≤ Subgroup.normalizer (Vn β : Set G) := Std.Vn_normal β
  have hsup : CVQ β ⊔ S34.Cb β = Vn β := by
    have hU : oTwoRes (stab β) ≤ Subgroup.normalizer ((CVQ β ⊔ S34.Cb β : Subgroup G) : Set G) :=
      (oTwoRes_le _).trans (F1.le_normalizer_sup hCn hCbn)
    rcases horth.eq_or_eq_of_oTwoRes le_sup_right (sup_le hCV hCbV) hU with h | h
    · exfalso
      have hle : CVQ β ≤ S34.Cb β := h ▸ le_sup_left
      have := Subgroup.relIndex_le_of_le_left (L := Vn β) hle (relIndex_ne_zero' _ _)
      omega
    · exact h
  have horth' : IsOrthSec (stab β) (CVQ β ⊓ S34.Cb β) (CVQ β) :=
    isModelSec_of_sup_eq horth hCV hCn hsup
  have hel := Std.Vn_isElemAbelian hS β
  have hcomm : ∀ x ∈ CVQ β, ∀ y ∈ CVQ β, x * y = y * x := fun x hx y hy =>
    F7.isElemAbelian_comm hel (hCV hx) (hCV hy)
  have hsq : ∀ x ∈ CVQ β, x ^ 2 = 1 := fun x hx => isElemAbelian_pow_eq_one hel (hCV hx)
  have hCbL : ∀ c ∈ S34.Cb β, ∀ a ∈ oTwoRes (stab β), ⁅a, c⁆ = 1 := fun c hc a ha =>
    commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_centralizer_iff.mp hc.2 a ha)
  have hsplit : (CVQ β ⊓ S34.Cb β) ⊓ ⁅CVQ β, oTwoRes (stab β)⁆ ≤ (⊥ : Subgroup G) :=
    Col.inf_comm_le_of_orth (Z := ⊥) hq hCn hsq hcomm bot_le inf_le_left
      (fun c hc a ha => by rw [hCbL c hc.2 a ha]; exact Subgroup.one_mem _)
      (by
        rw [Subgroup.commutator_le]
        intro c hc q hq'
        have := Subgroup.mem_centralizer_iff.mp hc.2 q hq'
        exact Subgroup.mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr this.symm))
      horth'
  have hU'n : stab β ≤ Subgroup.normalizer ((⁅CVQ β, oTwoRes (stab β)⁆ : Subgroup G) : Set G) :=
    Col.le_normalizer_comm hCn (le_normalizer_oTwoRes (stab β))
  have hU'C : ⁅CVQ β, oTwoRes (stab β)⁆ ≤ CVQ β := by
    rw [Subgroup.commutator_le]
    intro c hc a ha
    have h1 := (Subgroup.mem_normalizer_iff.mp (hCn (oTwoRes_le _ ha)) c⁻¹).mp
      ((CVQ β).inv_mem hc)
    have e : ⁅c, a⁆ = c * (a * c⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact (CVQ β).mul_mem hc h1
  have hU'ne : ¬ ⁅CVQ β, oTwoRes (stab β)⁆ ≤ (⊥ : Subgroup G) := by
    intro hbot
    have hle : CVQ β ≤ S34.Cb β := fun c hc =>
      ⟨hCV hc, Subgroup.mem_centralizer_iff.mpr fun a ha => by
        have h1 : ⁅c, a⁆ ∈ ⁅CVQ β, oTwoRes (stab β)⁆ := Subgroup.commutator_mem_commutator hc ha
        have h2 := Subgroup.mem_bot.mp (hbot h1)
        exact (commutatorElement_eq_one_iff_mul_comm.mp h2).symm⟩
    have h3 : Vn β = S34.Cb β := hsup.symm.trans (sup_eq_right.mpr hle)
    rw [← h3, Subgroup.relIndex_self] at h16
    omega
  obtain ⟨l, hl, -⟩ := exists_arc hS hβ
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hl' : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hsyl := sylow_stab_inf_left hS.glob.amalg hl
  have hPp : IsPGroup 2 ↥(stab β ⊓ stab l) := hsyl.2.1
  have hDp : IsPGroup 2 ↥(⁅CVQ β, oTwoRes (stab β)⁆ : Subgroup G) :=
    IsPGroup.to_le (pCoreOf_isPGroup 2 (stab β))
      ((hU'C.trans hCV).trans (Std.Vn_le_Qv_self hS β))
  have hbotn : ∀ x : G, x ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun x => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp [Subgroup.mem_bot]
  obtain ⟨u, huU, huE, hufix⟩ := exists_central_of_pGroup (P := stab β ⊓ stab l) (E := ⊥)
    (D := ⁅CVQ β, oTwoRes (stab β)⁆) (fun x _ => hbotn x)
    (fun p hp => hU'n hp.1) (fun x _ => hbotn x) hPp hDp hU'ne
  have huV : u ∈ Vn β := hCV (hU'C huU)
  have hVQl : Vn β ≤ Qv l := (Std.Vn_le_Wb_self hS hβ).trans (Std.Wb_le_Ql hS hl)
  have huZl : u ∈ Zv l := Std.omegaZ_le hS hlt u (hVQl huV)
    (isElemAbelian_pow_eq_one hel huV) (fun y hy => by
      have hyP : y ∈ stab β ⊓ stab l := ⟨Std.Qv_le_stab hS hl' hy, pCoreOf_le 2 _ hy⟩
      have h1 := Subgroup.mem_bot.mp (hufix y hyP)
      exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm)
  have huZb : u ∈ Zv β :=
    mem_Zv_of_fixed hS hβ hl huZl (fun p hp => Subgroup.mem_bot.mp (hufix p hp))
  have huCb : u ∈ S34.Cb β := S34.Zv_le_Cb hS.glob hβ huZb
  exact huE (hsplit ⟨⟨hU'C huU, huCb⟩, huU⟩)

end S35.S6

end F53.Stellmacher

end CFSG.Quasithin
