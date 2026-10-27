module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddTwelveH
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Seven

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

omit [Finite G] in
theorem relIndex_le_two_of_mul_mem {N K : Subgroup G}
    (h : ∀ a ∈ K, ∀ b ∈ K, a ∉ N → b ∉ N → a * b ∈ N) : N.relIndex K ≤ 2 := by
  by_cases hK : K ≤ N
  · rw [Subgroup.relIndex_eq_one.mpr hK]
    norm_num
  · obtain ⟨a, haK, haN⟩ : ∃ a ∈ K, a ∉ N := by
      by_contra hcon
      push Not at hcon
      exact hK fun x hx => hcon x hx
    let f : Bool → ↥K ⧸ N.subgroupOf K := fun t =>
      if t then ((⟨a⁻¹, K.inv_mem haK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K)
      else ((1 : ↥K) : ↥K ⧸ N.subgroupOf K)
    have hf : Function.Surjective f := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H k =>
        by_cases hk : (k : G) ∈ N
        · refine ⟨false, ?_⟩
          show ((1 : ↥K) : ↥K ⧸ N.subgroupOf K) = (k : ↥K ⧸ N.subgroupOf K)
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using hk
        · refine ⟨true, ?_⟩
          show ((⟨a⁻¹, K.inv_mem haK⟩ : ↥K) : ↥K ⧸ N.subgroupOf K) = (k : ↥K ⧸ N.subgroupOf K)
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using h a haK k k.2 haN hk
    have h2 := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
    exact h2

variable {α' ν β l : Geo H M}

open Twelve

theorem comm_le_inf (hA : F53Amalgam H M S) (hs : Sit43 α) (ho : Odd (bMin H M))
    (d : Data α α' ν β l) : ⁅Vn β, Vn α'⁆ ≤ Vn β ⊓ Vn α' :=
  Core.comm_Vn_le_inf hA hs (Core.isCritPair₃_crit hA hs ho d.crit d.hβ (d.dist_beta hA))

theorem comm_le_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (d : Data α α' ν β l) : ⁅Vn β, Vn α'⁆ ≤ Wn α :=
  (comm_le_inf hA hs ho d).trans (inf_le_left.trans (hs.Vn_le_Wn hA h26 d.hβ))

theorem comm_le_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) : ⁅Vn β, Vn α'⁆ ≤ Zv ν :=
  Core.comm_Vn_le_Zv_nu hA h26 hs ho hb d.crit d.hβ (d.dist_beta hA) d.hν d.dν h6

theorem eight_le_card (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (d : Data α α' ν β l) :
    8 ≤ Nat.card ↥⁅Vn β, Vn α'⁆ :=
  Core.card_comm_Vn_ge hA h26 hs ho hb
    (Core.isCritPair₃_crit hA hs ho d.crit d.hβ (d.dist_beta hA))

theorem commute_of_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) {w r : G}
    (hw : w ∈ Wn α) (hr : r ∈ ⁅Vn β, Vn α'⁆) : w * r = r * w :=
  comm_of_elemAbelian (isElemAbelian_Wn_of_five hA hs hb5) hw (comm_le_Wn hA h26 hs ho d hr)

theorem Wn_le_stab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l) {κ : Geo H M}
    (hκ : κ ∈ nbrs ν) (hdκ : dist α κ + 2 = bMin H M) (h6 : Nat.card (Vn α') = 2 ^ 6) :
    Wn α ≤ stab ν := by
  intro w hw
  by_contra hwν
  have hY := le_Yv_kappa hA h26 hs ho hb5 hκ hdκ hw hwν
    (comm_le_Zv hA h26 hs ho (by omega) d h6) (comm_le_Wn hA h26 hs ho d)
  have hκv : vtype κ = true := Sit43.vtype_true_of_adj (d.vtypes hA hs ho).2.2 hκ
  have h4 := hs.card_Yv hA h26 hκv
  have h8 := eight_le_card hA h26 hs ho (by omega) d
  have hle := Subgroup.card_le_of_le hY
  omega

theorem comm_le_inf_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) {w : G} (hw : w ∈ Wn α) :
    ⁅Vn β, Vn α'⁆ ≤ Zv ν ⊓ Subgroup.centralizer ({w} : Set G) := fun r hr =>
  ⟨comm_le_Zv hA h26 hs ho (by omega) d h6 hr,
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem hA h26 hs ho hb5 d hw hr).symm⟩

theorem relIndex_centralizer_eq_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) (hWν : Wn α ≤ stab ν) {w : G} (hw : w ∈ Wn α)
    (hwQ : w ∉ Qv ν) : (Zv ν ⊓ Subgroup.centralizer ({w} : Set G)).relIndex (Zv ν) = 2 := by
  set C := Zv ν ⊓ Subgroup.centralizer ({w} : Set G) with hC
  have hνv : vtype ν = false := (d.vtypes hA hs ho).2.2
  have h16 : Nat.card (Zv ν) = 16 := hs.card_Zv_false hνv
  have hmul := Subgroup.relIndex_mul_card C (Zv ν)
  rw [inf_of_le_left (inf_le_left : C ≤ Zv ν), h16] at hmul
  have h8 : 8 ≤ Nat.card C :=
    (eight_le_card hA h26 hs ho (by omega) d).trans
      (Subgroup.card_le_of_le (comm_le_inf_centralizer hA h26 hs ho hb5 d h6 hw))
  have hne : C.relIndex (Zv ν) ≠ 1 := by
    intro h1
    apply hwQ
    rw [← hs.centralizer_Zv hA hνv]
    refine ⟨hWν hw, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.relIndex_eq_one.mp h1 hz).2
  have hpos : 0 < C.relIndex (Zv ν) := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : C.relIndex (Zv ν) * 8 ≤ 16 := (Nat.mul_le_mul le_rfl h8).trans hmul.le
  omega

theorem inf_centralizer_eq_comm (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) (hWν : Wn α ≤ stab ν) {w : G} (hw : w ∈ Wn α)
    (hwQ : w ∉ Qv ν) : Zv ν ⊓ Subgroup.centralizer ({w} : Set G) = ⁅Vn β, Vn α'⁆ := by
  set C := Zv ν ⊓ Subgroup.centralizer ({w} : Set G) with hC
  have h2 := relIndex_centralizer_eq_two hA h26 hs ho hb5 d h6 hWν hw hwQ
  have hmul := Subgroup.relIndex_mul_card C (Zv ν)
  rw [inf_of_le_left (inf_le_left : C ≤ Zv ν), hs.card_Zv_false (d.vtypes hA hs ho).2.2,
    h2] at hmul
  have h8 := eight_le_card hA h26 hs ho (by omega) d
  exact (Subgroup.eq_of_le_of_card_ge (comm_le_inf_centralizer hA h26 hs ho hb5 d h6 hw)
    (by omega)).symm

theorem card_comm_le_eight (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) (hWν : Wn α ≤ stab ν) {w : G} (hw : w ∈ Wn α)
    (hwQ : w ∉ Qv ν) : Nat.card ↥⁅Vn β, Vn α'⁆ ≤ 8 := by
  have h2 := relIndex_centralizer_eq_two hA h26 hs ho hb5 d h6 hWν hw hwQ
  have hmul := Subgroup.relIndex_mul_card (Zv ν ⊓ Subgroup.centralizer ({w} : Set G)) (Zv ν)
  rw [inf_of_le_left inf_le_left, hs.card_Zv_false (d.vtypes hA hs ho).2.2, h2,
    inf_centralizer_eq_comm hA h26 hs ho hb5 d h6 hWν hw hwQ] at hmul
  omega

theorem relIndex_Qv_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M)
    (hs : Sit43 α) (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (d : Data α α' ν β l)
    (h6 : Nat.card (Vn α') = 2 ^ 6) (hWν : Wn α ≤ stab ν) : (Qv ν).relIndex (Wn α) ≤ 2 := by
  obtain ⟨D⟩ := (hs.of_vtype_false (d.vtypes hA hs ho).2.2).exists_dict5 hA (nbrs_symm d.hν)
  have hsw : ∀ w (hw : w ∈ Wn α), w ∉ Qv ν → (D.ψ ⟨w, hWν hw⟩).IsSwap := fun w hw hwQ =>
    (D.relIndex_centralizer_eq_two_iff ⟨w, hWν hw⟩).mp
      (relIndex_centralizer_eq_two hA h26 hs ho hb5 d h6 hWν hw hwQ)
  refine relIndex_le_two_of_mul_mem fun a ha b hb haQ hbQ => ?_
  by_contra habQ
  have hab : a * b ∈ Wn α := (Wn α).mul_mem ha hb
  have h1 := (hsw a ha haQ).sign_eq
  have h2 := (hsw b hb hbQ).sign_eq
  have h3 := (hsw (a * b) hab habQ).sign_eq
  have e : D.ψ ⟨a * b, hWν hab⟩ = D.ψ ⟨a, hWν ha⟩ * D.ψ ⟨b, hWν hb⟩ := by
    rw [← map_mul]
    rfl
  rw [e, Equiv.Perm.sign_mul, h1, h2] at h3
  exact absurd h3 (by decide)

theorem card_comm_inf_Yv_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) {δ δ' : Geo H M} (h : IsCritPair₃ δ δ')
    (h8 : Nat.card ↥⁅Vn δ, Vn δ'⁆ ≤ 8) : Nat.card ↥(⁅Vn δ, Vn δ'⁆ ⊓ Yv δ') ≤ 2 := by
  set R := ⁅Vn δ, Vn δ'⁆ with hR
  have h4 := four_le_relIndex_comm_Vn hA h26 hs ho hb h
  have hRn : R ≤ Subgroup.normalizer (Yv δ' : Set G) :=
    (Core.comm_Vn_le_inf hA hs h).trans (inf_le_right.trans
      ((Core.Vn_le_stab_of_dist hA hs h.2.1 (by rw [CosetGeom.dist_self]; omega)).trans
        (hs.stab_le_normalizer_Yv hA h26 h.2.1)))
  rw [Sit43.relIndex_sup_of_le_normalizer hRn] at h4
  have hmul := Subgroup.relIndex_mul_card (Yv δ') R
  rw [inf_comm] at hmul
  have hle : 4 * Nat.card ↥(R ⊓ Yv δ') ≤ 8 := (Nat.mul_le_mul h4 le_rfl).trans (hmul.le.trans h8)
  omega

end Seven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
