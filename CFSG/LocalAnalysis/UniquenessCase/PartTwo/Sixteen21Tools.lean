module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen21

private abbrev conjAction (C : Subgroup G) : MulAction ↥C G where
  smul := fun c g => (c : G) * g * (c : G)⁻¹
  one_smul := fun g => by
    show ((1 : ↥C) : G) * g * ((1 : ↥C) : G)⁻¹ = g
    simp
  mul_smul := fun a b g => by
    show ((a * b : ↥C) : G) * g * ((a * b : ↥C) : G)⁻¹ =
      (a : G) * ((b : G) * g * (b : G)⁻¹) * (a : G)⁻¹
    simp [mul_assoc]

private theorem one_le_pRank_of_dvd_card {Q : Type*} [Group Q] [Finite Q] (J : Subgroup Q)
    {r : ℕ} (hr : r.Prime) (hd : r ∣ Nat.card J) : 1 ≤ CFSG.Open.pRank r J := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' r hd
  have hx' : orderOf (x : Q) = r := (Subgroup.orderOf_coe x).trans hx
  refine CFSG.SectionRank.le_pRank (p := r) (H := J) (E := Subgroup.zpowers (x : Q)) (k := 1)
    hr.one_lt (Subgroup.zpowers_le.2 x.2) ?_ ?_
  · exact CFSG.Open.isElemAbelian_zpowers (by rw [← hx']; exact pow_orderOf_eq_one (x : Q))
  · rw [Nat.card_zpowers, hx', pow_one]

theorem one_le_pRank_of_mem_small {M V₀ : Subgroup G} (hMV₀ : M ≤ normalizer (V₀ : Set G))
    (hV₀ : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p.Prime) (hrk : 2 ≤ CFSG.Open.pRank p M) {v : G}
    (hv : v ∈ V₀) (hv1 : v ≠ 1) :
    1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G)) := by
  classical
  let Cv : Subgroup G := M ⊓ centralizer ({v} : Set G)
  letI : MulAction ↥M G := conjAction M
  have hstab : MulAction.stabilizer ↥M v = Cv.subgroupOf M := by
    ext c
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hc
      exact ⟨c.2, mul_inv_eq_iff_eq_mul.1 hc⟩
    · rintro ⟨-, hc⟩
      show (c : G) * v * (c : G)⁻¹ = v
      rw [mul_inv_eq_iff_eq_mul]
      exact hc
  have hidx : Cv.relIndex M = (MulAction.orbit ↥M v).ncard := by
    rw [Subgroup.relIndex, ← hstab]
    exact MulAction.index_stabilizer ↥M v
  have horb_sub : MulAction.orbit ↥M v ⊆ (V₀ : Set G) \ {1} := by
    rintro w ⟨m, rfl⟩
    refine ⟨?_, ?_⟩
    · show (m : G) * v * (m : G)⁻¹ ∈ V₀
      exact ((Subgroup.mem_normalizer_iff.1 (hMV₀ m.2)) v).1 hv
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      refine hv1 ?_
      have hw' : (m : G) * v * (m : G)⁻¹ = 1 := hw
      have h3 : (m : G)⁻¹ * ((m : G) * v * (m : G)⁻¹) * (m : G) = 1 := by
        rw [hw']; group
      have h4 : (m : G)⁻¹ * ((m : G) * v * (m : G)⁻¹) * (m : G) = v := by group
      rw [h4] at h3
      exact h3
  have horbit_le : (MulAction.orbit ↥M v).ncard ≤ 3 := by
    have h1 : (MulAction.orbit ↥M v).ncard ≤ ((V₀ : Set G) \ {1}).ncard :=
      Set.ncard_le_ncard horb_sub
    have h2 : ((V₀ : Set G) \ {1}).ncard = Nat.card V₀ - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem V₀)]
      congr 1
    rw [h2] at h1
    omega
  have hrelIndex_le : Cv.relIndex M ≤ 3 := by
    rw [hidx]; exact horbit_le
  have hp2M : p ^ 2 ∣ Nat.card M := by
    obtain ⟨E, hEM, _, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
    have h1 : p ^ 2 ∣ Nat.card E := by
      rw [hEcard]; exact pow_dvd_pow p hrk
    exact h1.trans (Subgroup.card_dvd_of_le hEM)
  have hcardM : Nat.card M = Nat.card Cv * Cv.relIndex M := by
    have h := Subgroup.relIndex_mul_card Cv M
    rw [inf_eq_left.2 inf_le_left, mul_comm] at h
    exact h.symm
  have hpdvdCv : p ∣ Nat.card Cv := by
    by_contra hnd
    have hcop : Nat.Coprime (p ^ 2) (Nat.card Cv) :=
      (hp.coprime_pow_of_not_dvd hnd).symm
    have hprod : p ^ 2 ∣ Nat.card Cv * Cv.relIndex M := by
      rw [← hcardM]; exact hp2M
    have hprod' : p ^ 2 ∣ Cv.relIndex M * Nat.card Cv := by
      rw [mul_comm]; exact hprod
    have hrel : p ^ 2 ∣ Cv.relIndex M := hcop.dvd_of_dvd_mul_right hprod'
    have hpos : 0 < Cv.relIndex M := by
      rw [hidx]
      exact (show (MulAction.orbit ↥M v).Nonempty from
        ⟨v, MulAction.mem_orbit_self v⟩).ncard_pos
    have hle : p ^ 2 ≤ Cv.relIndex M := Nat.le_of_dvd hpos hrel
    have hge : 4 ≤ p ^ 2 := by
      have h2 : 2 ≤ p := hp.two_le
      calc 4 = 2 * 2 := by norm_num
        _ ≤ p * p := Nat.mul_le_mul h2 h2
        _ = p ^ 2 := (pow_two p).symm
    omega
  exact one_le_pRank_of_dvd_card Cv hp hpdvdCv

theorem one_le_pRank_of_dvd_cElt {M T V₀ V : Subgroup G} (h : Hyp123 M T V₀ V)
    (hV₀ : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {v : G} (hv : v ∈ V)
    (hv0 : v ∉ V₀) (hdvd : p ∣ Nat.card (F11.CElt M V₀ v)) :
    1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G)) := by
  classical
  let Cv : Subgroup G := M ⊓ centralizer ({v} : Set G)
  have hpf : PairFacts M V₀ V := hyp123_pairFacts h
  have hle : Cv ≤ F11.CElt M V₀ v := by
    rintro m ⟨hmM, hmC⟩
    have hmv : m * v = v * m := Subgroup.mem_centralizer_singleton_iff.1 hmC
    refine ⟨hmM, hpf.le_normalizer₀ hmM, ?_⟩
    have h1 : m * v * m⁻¹ * v⁻¹ = 1 := by
      rw [show m * v * m⁻¹ * v⁻¹ = (m * v) * m⁻¹ * v⁻¹ from by group, hmv]
      group
    rw [h1]
    exact V₀.one_mem
  obtain ⟨n, _, hrel⟩ : ∃ n ≤ 2, Cv.relIndex (F11.CElt M V₀ v) = 2 ^ n := by
    rcases h with ⟨-, h0⟩ | ⟨h0, -⟩
    · subst h0
      exact ⟨0, by norm_num, by
        show (M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt M ⊥ v) = 2 ^ 0
        rw [ElevenThree.relIndex_cElt_bot M v]
        norm_num⟩
    · exact ElevenThree.relIndex_cElt_eq_pow_two h0 hV₀ hv hv0
  have hcard : Nat.card (F11.CElt M V₀ v) = Nat.card Cv * 2 ^ n := by
    have hh := Subgroup.relIndex_mul_card Cv (F11.CElt M V₀ v)
    rw [inf_eq_left.2 hle, mul_comm] at hh
    rw [hrel] at hh
    exact hh.symm
  have hp2n : ¬ p ∣ 2 ^ n := by
    intro hd
    have h2dvd : p ∣ 2 := hp.dvd_of_dvd_pow hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2dvd)
  have hpdvdCv : p ∣ Nat.card Cv :=
    (hp.dvd_mul.mp (hcard ▸ hdvd)).resolve_right hp2n
  exact one_le_pRank_of_dvd_card Cv hp hpdvdCv

theorem dvd_card_cElt_of_mem_mbar {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) {p : ℕ}
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar M V₀ V hV) (hord : orderOf φ = p) {v : G}
    (hv : v ∈ V)
    (hfix : φ (mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)) = mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)) :
    p ∣ Nat.card (F11.CElt M V₀ v) := by
  obtain ⟨g, hgM, hgact⟩ := (mem_barSub V₀ V hV M φ).1 hφ
  have h1 : actTil V₀ V hV g (mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩)) =
      mkTil V₀ V hV (IntMod.mk hV ⟨v, hv⟩) := by
    rw [hgact]; exact hfix
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
  have hmem : (g : G) ∈ F11.CElt M V₀ v :=
    ⟨hgM, stabTil_le_normalizer₀ V₀ V g.2, h1⟩
  have hdvd1 : orderOf φ ∣ orderOf g := by
    rw [← hgact]
    exact orderOf_map_dvd (actTil V₀ V hV) g
  have hdvd2 : orderOf g ∣ Nat.card (F11.CElt M V₀ v) := by
    rw [← Subgroup.orderOf_coe g]
    exact Subgroup.orderOf_dvd_natCard _ hmem
  rw [← hord]
  exact hdvd1.trans hdvd2

theorem one_le_pRank_of_mem_cTilde {M T V₀ V : Subgroup G} (h : Hyp123 M T V₀ V)
    (hV₀ : Nat.card V₀ ≤ 4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 2 ≤ CFSG.Open.pRank p M) {y : G} (hy : y ∈ F11.CTilde M V₀ V)
    (hord : orderOf y = p) :
    ∀ v ∈ V, v ≠ 1 → 1 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({v} : Set G)) := by
  intro v hv hv1
  by_cases hv0 : v ∈ V₀
  · exact one_le_pRank_of_mem_small (hyp123_pairFacts h).le_normalizer₀ hV₀ hp hrk hv0 hv1
  · have hyv : y ∈ F11.CElt M V₀ v :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy v) hv
    have hdvd : p ∣ Nat.card (F11.CElt M V₀ v) := by
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hyv
    exact one_le_pRank_of_dvd_cElt h hV₀ hp hp2 hv hv0 hdvd

theorem exists_mem_cTilde_of_not_dvd {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hMs : M ≤ stabTil V₀ V) {p k : ℕ} (hp : p.Prime) (hrk : k ≤ CFSG.Open.pRank p M)
    (hcard : ¬ p ^ k ∣ Nat.card (Mbar M V₀ V hV)) :
    ∃ y ∈ F11.CTilde M V₀ V, orderOf y = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  by_contra hno
  let φ : ↥E →* ↥(Mbar M V₀ V hV) :=
    ((actTil V₀ V hV).comp (Subgroup.inclusion (hEM.trans hMs))).codRestrict
      (Mbar M V₀ V hV) fun e => actTil_mem_barSub V₀ V hV (hEM e.2) (hMs (hEM e.2))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have hord : orderOf (e : G) = p := by
      refine orderOf_eq_prime (hE.2 e e.2) ?_
      intro h1
      exact hne (Subtype.ext h1)
    refine hno ⟨(e : G), ?_, hord⟩
    have hker : actTil V₀ V hV ⟨(e : G), hMs (hEM e.2)⟩ = 1 := by
      have := congrArg Subtype.val he
      exact this
    have hcomm := (actTil_eq_one_iff V₀ V hV ⟨(e : G), hMs (hEM e.2)⟩).1 hker
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    exact ⟨hEM e.2, stabTil_le_normalizer₀ V₀ V (hMs (hEM e.2)), hcomm v hv⟩
  have h1 : Nat.card E ∣ Nat.card (Mbar M V₀ V hV) := Subgroup.card_dvd_of_injective φ hinj
  rw [hEcard] at h1
  exact hcard ((pow_dvd_pow p hrk).trans h1)

theorem exists_orderOf_fix_of_card_le {U : Type*} [Group U] [Finite U]
    {X : Subgroup (MulAut U)} {p a : ℕ} (hp : p.Prime) (hdvd : p ^ a ∣ Nat.card X)
    (hU : Nat.card U ≤ p ^ a) {u : U} (hu : u ≠ 1) :
    ∃ φ ∈ X, orderOf φ = p ∧ φ u = u := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut U) := inferInstance
  set q : ℕ := (MulAction.stabilizer (↥X) u).index with hq
  have hqcard : q = (MulAction.orbit (↥X) u).ncard := by
    rw [hq]
    exact MulAction.index_stabilizer (↥X) u
  have horb_sub : MulAction.orbit (↥X) u ⊆ {w : U | w ≠ 1} := by
    rintro w ⟨m, rfl⟩
    show (m : MulAut U) u ≠ 1
    intro h1
    exact hu ((m : MulAut U).injective (by simp [h1]))
  have hqle : q ≤ p ^ a - 1 := by
    rw [hqcard]
    have h1 : (MulAction.orbit (↥X) u).ncard ≤ ({w : U | w ≠ 1} : Set U).ncard :=
      Set.ncard_le_ncard horb_sub
    have h2 : ({w : U | w ≠ 1} : Set U).ncard = Nat.card U - 1 := by
      rw [show ({w : U | w ≠ 1} : Set U) = (Set.univ : Set U) \ {1} by ext w; simp,
        Set.ncard_sdiff_singleton_of_mem (Set.mem_univ (1 : U)), Set.ncard_univ]
    rw [h2] at h1
    exact h1.trans (Nat.sub_le_sub_right hU 1)
  have hqpos : 0 < q := by
    rw [hqcard]
    exact (show (MulAction.orbit (↥X) u).Nonempty from
      ⟨u, MulAction.mem_orbit_self u⟩).ncard_pos
  have hcardX : Nat.card X = q * Nat.card (MulAction.stabilizer (↥X) u) := by
    rw [hq]
    exact (Subgroup.index_mul_card (MulAction.stabilizer (↥X) u)).symm
  have hpdvdstab : p ∣ Nat.card (MulAction.stabilizer (↥X) u) := by
    by_contra hnd
    have hcop : Nat.Coprime (p ^ a) (Nat.card (MulAction.stabilizer (↥X) u)) :=
      (hp.coprime_pow_of_not_dvd hnd).symm
    have hprod : p ^ a ∣ q * Nat.card (MulAction.stabilizer (↥X) u) := by
      rw [← hcardX]; exact hdvd
    have hpaq : p ^ a ∣ q := hcop.dvd_of_dvd_mul_right hprod
    have hle : p ^ a ≤ q := Nat.le_of_dvd hqpos hpaq
    have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
    omega
  obtain ⟨ψ, hψ⟩ := exists_prime_orderOf_dvd_card' p hpdvdstab
  refine ⟨(((ψ : ↥(MulAction.stabilizer (↥X) u)) : ↥X) : MulAut U), ?_, ?_, ?_⟩
  · exact (((ψ : ↥(MulAction.stabilizer (↥X) u)) : ↥X)).2
  · exact ((Subgroup.orderOf_coe ((ψ : ↥(MulAction.stabilizer (↥X) u)) : ↥X)).trans
      (Subgroup.orderOf_coe ψ)).trans hψ
  · exact MulAction.mem_stabilizer_iff.1 ψ.2

end Sixteen21

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
