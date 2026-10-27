module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Inter
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1a
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2
public import CFSG.Quasithin.Background.B2FactorizationR2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_invol_of_normal {T N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hn : T ≤ Subgroup.normalizer (N : Set G)) (hne : N ≠ ⊥) :
    ∃ z ∈ N, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ t ∈ T, t * z = z * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnorm : (N.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr hn
  have hne' : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [Subgroup.subgroupOf_eq_bot] at h
    exact h.eq_bot_of_le hNT
  have h1 := Group.IsNilpotent.inf_center_ne_bot_of_normal (G := T) (H := N.subgroupOf T) hne'
  set K0 : Subgroup T := N.subgroupOf T ⊓ Subgroup.center T with hK0
  have hK2 : IsPGroup 2 K0 := hT.to_subgroup K0
  have hdvd : 2 ∣ Nat.card K0 := by
    rcases hK2.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) h1
    · exact h
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' (G := K0) 2 hdvd
  have hz0' : (z0 : T) ∈ K0 := z0.2
  refine ⟨((z0 : T) : G), (Subgroup.mem_subgroupOf.mp hz0'.1), ?_, ?_, ?_⟩
  · intro h
    have h' : (z0 : T) = 1 := Subtype.ext h
    have : z0 = 1 := Subtype.ext h'
    rw [this, orderOf_one] at hz0
    omega
  · have := pow_orderOf_eq_one z0
    rw [hz0] at this
    have := congrArg (fun x : K0 => (((x : T) : G))) this
    simpa using this
  · intro t ht
    have hc := Subgroup.mem_center_iff.mp hz0'.2 ⟨t, ht⟩
    exact congrArg (fun x : T => (x : G)) hc

theorem centerOf_eq_bot (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) :
    centerOf (stab l) = ⊥ := by
  obtain ⟨e, he⟩ := exists_adj l
  have he' : e ∈ nbrs l := he
  exact centerOf_eq_bot_of_Zv_central hS.glob.amalg (Std.mem_nbrs_symm.mpr he')
    (hS.glob.central e (Std.vtype_nbr_S3 hl he'))

theorem eq_Zv_of_normal (hS : Sit H M S) {l : Geo H M} (hl : vtype l = true) {N : Subgroup G}
    (hN : N ≤ Zv l) (hn : stab l ≤ Subgroup.normalizer (N : Set G)) (hne : N ≠ ⊥) :
    N = Zv l := by
  have h4 := hS.cardZ3 l hl
  have hd : Nat.card N ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le hN
  have h1 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne
  have hc : Nat.card N = 2 ∨ Nat.card N = 4 := by
    have : Nat.card N ≤ 4 := Nat.le_of_dvd (by norm_num) hd
    interval_cases h : Nat.card N <;> simp_all
  rcases hc with hc | hc
  · exfalso
    obtain ⟨z, hz⟩ : ∃ z : N, z ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card N = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
      omega
    have huniq := (Nat.card_eq_two_iff' (1 : N)).mp hc
    obtain ⟨y0, -, hy0⟩ := huniq
    have hZ : ((z : N) : G) ∈ centerOf (stab l) := by
      refine ⟨pCoreOf_le 2 _ (Zv_le_Qv hS.glob.amalg l (hN z.2)),
        Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      have hgz : g * (z : G) * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hn hg) _).mp z.2
      by_cases h1' : g * (z : G) * g⁻¹ = 1
      · have : (z : G) = 1 := by
          have := congrArg (fun x => g⁻¹ * x * g) h1'
          simpa [mul_assoc] using this
        exact absurd (Subtype.ext this) hz
      · have e1 : (⟨g * (z : G) * g⁻¹, hgz⟩ : N) = y0 :=
          hy0 _ (fun h => h1' (congrArg Subtype.val h))
        have e2 : z = y0 := hy0 _ hz
        have : g * (z : G) * g⁻¹ = (z : G) := by
          have := congrArg Subtype.val (e1.trans e2.symm)
          exact this
        exact mul_inv_eq_iff_eq_mul.mp this
    rw [centerOf_eq_bot hS hl] at hZ
    exact hz (Subtype.ext (Subgroup.mem_bot.mp hZ))
  · exact Subgroup.eq_of_le_of_card_ge hN (by omega)

theorem Vn_le_comm_of_ne (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β)
    (hS2 : ∀ y ∈ Qv l, y ^ 2 = 1 → (∀ q ∈ Qv l, q * y = y * q) → y ∈ Zv l)
    (hne : Vn β ⊓ Vn δ ≠ Zv l) : Vn β ≤ ⁅Vn β, stab β⁆ := by
  have hlt := Std.vtype_nbr_S5 hβ hl
  have hlβ : β ∈ nbrs l := Std.mem_nbrs_symm.mpr hl
  have hRV : Vn β ⊓ Vn δ ≤ Vn β := inf_le_left
  have hRQ : Vn β ⊓ Vn δ ≤ Qv l := hRV.trans (Std.Vn_le_Qv_dist hS (by
    rw [dist_eq_one_iff_adj.mpr hl]
    have := hS.b5
    omega))
  have hRn : stab l ≤ Subgroup.normalizer ((Vn β ⊓ Vn δ : Subgroup G) : Set G) :=
    stab_le_normalizer_inter hS hβ hl hlδ hδβ
  have hZR : Zv l ≤ Vn β ⊓ Vn δ := Zv_le_inter hl hlδ
  have hQn : stab l ≤ Subgroup.normalizer (Qv l : Set G) := le_normalizer_pCoreOf 2 (stab l)
  have hN0 : ⁅Vn β ⊓ Vn δ, Qv l⁆ ≠ ⊥ := by
    intro hN
    apply hne
    refine le_antisymm (fun x hx => hS2 x (hRQ hx)
      ((Std.Vn_isElemAbelian hS β).2 x (hRV hx)) ?_) hZR
    intro q hq
    have h1 : ⁅x, q⁆ ∈ ⁅Vn β ⊓ Vn δ, Qv l⁆ := Subgroup.commutator_mem_commutator hx hq
    rw [hN, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hNR : ⁅Vn β ⊓ Vn δ, Qv l⁆ ≤ Vn β ⊓ Vn δ :=
    commutator_le_left_of_le_normalizer ((pCoreOf_le 2 _).trans hRn)
  have hNn : stab l ≤ Subgroup.normalizer ((⁅Vn β ⊓ Vn δ, Qv l⁆ : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_commutator (hRn hg) (hQn hg)
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf (stab l)
  have hQT : Qv l ≤ T := pCoreOf_le_of_isSylowTwoOf hT
  obtain ⟨z, hzN, hz1, hz2, hzc⟩ := exists_invol_of_normal hT.2.1 ((hNR.trans hRQ).trans hQT)
    (hT.1.trans hNn) hN0
  have hzZ : z ∈ Zv l := by
    have hz : z ∈ quasithinOmegaOneCenter T :=
      mem_quasithinOmegaOneCenter_iff.mpr ⟨(hNR.trans hRQ).trans hQT hzN,
        Subgroup.mem_centralizer_iff.mpr fun t ht => hzc t ht, hz2⟩
    exact (le_iSup₂_of_le (f := fun (T : Subgroup G) (_ : IsSylowTwoOf T (stab l)) =>
      quasithinOmegaOneCenter T) T hT le_rfl) hz
  have hMn : stab l ≤ Subgroup.normalizer ((⁅Vn β ⊓ Vn δ, Qv l⁆ ⊓ Zv l : Subgroup G) : Set G) := by
    intro g hg
    have h1 := hNn hg
    have h2 := stab_le_normalizer_Zv hS.glob.amalg l hg
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]
  have hM0 : ⁅Vn β ⊓ Vn δ, Qv l⁆ ⊓ Zv l ≠ ⊥ := by
    intro h
    have : z ∈ (⁅Vn β ⊓ Vn δ, Qv l⁆ ⊓ Zv l : Subgroup G) := ⟨hzN, hzZ⟩
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  have hZN : Zv l ≤ ⁅Vn β ⊓ Vn δ, Qv l⁆ := by
    have := eq_Zv_of_normal hS hlt (N := ⁅Vn β ⊓ Vn δ, Qv l⁆ ⊓ Zv l) inf_le_right hMn hM0
    exact this ▸ inf_le_left
  have hU : ⁅Vn β ⊓ Vn δ, Qv l⁆ ≤ ⁅Vn β, stab β⁆ :=
    Subgroup.commutator_mono hRV (Std.Qv_le_stab hS hlβ)
  have hUn : stab β ≤ Subgroup.normalizer ((⁅Vn β, stab β⁆ : Subgroup G) : Set G) :=
    fun g hg => mem_normalizer_commutator (Std.Vn_normal β hg) (Subgroup.le_normalizer hg)
  refine iSup₂_le fun μ hμ => ?_
  obtain ⟨g, hg, hgl⟩ := stab_transitive_on_nbrs hl hμ
  have hgn := hUn hg
  rw [Subgroup.mem_normalizer_iff] at hgn
  intro x hx
  rw [← hgl, Zv_smul, mem_conjSub] at hx
  have h1 := (hgn (g⁻¹ * x * g)).mp (hU (hZN hx))
  simpa [mul_assoc] using h1

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin
