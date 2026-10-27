module

public import CFSG.RankThree.PartOne.S12.Sec158Defs
import CFSG.RankThree.PartOne.S12.Sec158
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S12.Sec12Three
public import CFSG.RankThree.PartOne.S10.ThetaContract

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem layer_ge_of_admissible (hS : SchreierFor InCatalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) {p : ℕ} {A₀ : Subgroup G} {c : G}
    {L E B J : Subgroup G} (h : Sec12Hyp G p A₀ c L E) (hBE : B ≤ E) (hBcard : Nat.card ↥B = p ^ 3)
    (hcard : p * Nat.card ↥(B ⊓ Subgroup.centralizer (J : Set G)) = Nat.card ↥B)
    (hJθ : J ∈ thetaCompCentralizer p (B ⊓ Subgroup.centralizer (J : Set G)))
    (hS2 : ∃ S : Subgroup G, S ≤ J ∧ S ≠ ⊥ ∧ IsPGroup 2 S ∧ B ≤ Subgroup.normalizer (S : Set G) ∧
      S = ⁅S, B⁆)
    {b : G} (hbD : b ∈ B ⊓ Subgroup.centralizer (J : Set G)) (hb1 : b ≠ 1) :
    J ≤ zeroLayer p E b := by
  classical
  have hp := h.prime
  have hp3 := h.three_lt
  have : Fact p.Prime := ⟨hp⟩
  have hBel : IsElementaryAbelian p ↥B :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
        (congrArg (fun z : ↥E => (z : G)) (h.E_elem.is_comm.comm ⟨x, hBE x.2⟩ ⟨y, hBE y.2⟩))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => Subtype.ext
        (by simpa using Sec12Three.pow_eq_one_of_mem_E h (hBE x.2)) }
  set D : Subgroup G := B ⊓ Subgroup.centralizer (J : Set G) with hDdef
  have hDB : D ≤ B := inf_le_left
  have hApow : ∀ x ∈ B, x ^ p = 1 := fun x hx => Sec12Three.pow_eq_one_of_mem_E h (hBE hx)
  have hAcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨x, hBE hx⟩ ⟨y, hBE hy⟩)
  have hDcard : Nat.card ↥D = p ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    rw [hcard, hBcard]
    ring
  have hbA : b ∈ B := hbD.1
  have hbord : orderOf b = p := orderOf_eq_prime (hApow b hbA) hb1
  have hzb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hbord]
  obtain ⟨x, hxD, hxb⟩ : ∃ x ∈ D, x ∉ Subgroup.zpowers b := by
    by_contra hcon
    have hle : D ≤ Subgroup.zpowers b := fun x hx => by_contra fun hxb => hcon ⟨x, hx, hxb⟩
    have := Subgroup.card_le_of_le hle
    rw [hDcard, hzb] at this
    have h2 : p ^ 2 ≤ p := this
    have := hp.two_le
    nlinarith
  have hMD : Subgroup.zpowers b ⊔ Subgroup.zpowers x = D := by
    set M := Subgroup.zpowers b ⊔ Subgroup.zpowers x with hM
    have hMD' : M ≤ D := sup_le (Subgroup.zpowers_le.2 hbD) (Subgroup.zpowers_le.2 hxD)
    have hbM : Subgroup.zpowers b ≤ M := le_sup_left
    have hdvd : Nat.card ↥M ∣ p ^ 2 := hDcard ▸ Subgroup.card_dvd_of_le hMD'
    obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hle1 : p ≤ Nat.card ↥M := hzb ▸ Subgroup.card_le_of_le hbM
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hMk
      have := hp.two_le
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      rw [pow_one] at hMk
      have heq : Subgroup.zpowers b = M :=
        Subgroup.eq_of_le_of_card_ge hbM (by rw [hMk, hzb])
      exact hxb (heq ▸ (le_sup_right : Subgroup.zpowers x ≤ M) (Subgroup.mem_zpowers x))
    have hk2 : k = 2 := by omega
    subst hk2
    exact Subgroup.eq_of_le_of_card_ge hMD' (by rw [hDcard, hMk])
  have hxbc : x * b = b * x := hAcomm x (hDB hxD) b hbA
  have hxH : x ∈ Subgroup.centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hxbc
  set H : Subgroup G := Subgroup.centralizer ({b} : Set G) with hH
  let y : ↥H := ⟨x, hxH⟩
  have hx1 : x ≠ 1 := fun h1 => hxb (h1 ▸ Subgroup.one_mem _)
  have hyord : orderOf y = p := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hApow x (hDB hxD)) hx1
  obtain ⟨hJC, hJθ'⟩ := mem_image_map_subtype_iff_of_le.1 hJθ
  have hDC : (Subgroup.centralizer ({y} : Set ↥H)).map H.subtype =
      Subgroup.centralizer (D : Set G) := by
    ext g
    rw [← hMD]
    constructor
    · rintro ⟨hh, hhc, rfl⟩
      rw [Sec158.mem_centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.1 hh.2, ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hhc
      exact congrArg Subtype.val this
    · intro hg
      rw [Sec158.mem_centralizer_sup, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff] at hg
      have hgH : g ∈ H := Subgroup.mem_centralizer_singleton_iff.2 hg.1
      have hy' : (⟨g, hgH⟩ : ↥H) ∈ Subgroup.centralizer ({y} : Set ↥H) :=
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hg.2)
      exact ⟨_, hy', rfl⟩
  have hJy : J.subgroupOf H ∈ thetaComponentsAt p y :=
    Sec158.mem_thetaComponentsAt_subgroupOf_of_centralizer hp y hDC hJC hJθ'
  have hsimple : IsSimpleGroup G := h.setup.1
  have hHK : CFSG.IsKGroup ↥H :=
    h.setup.2.2.1 _ (EmbeddingFixedResidual.centralizer_ne_top_of_simple h.setup.2.1 hb1)
  have hHE : evenRank ↥H ≤ 3 := (Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  obtain ⟨L', hL', hJL'⟩ := h82 hS ↥H hHK hHE p hp hp3 y hyord _ hJy
  have hIb : L'.map H.subtype ∈ thetaComponentsAt p b := ⟨L', hL', rfl⟩
  obtain ⟨S, hSJ, hS0, hS2', hBS, hSB⟩ := hS2
  have hJIb : J ≤ L'.map H.subtype := by
    intro g hg
    have hgH : g ∈ H :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hbD) (hJC hg)
    exact ⟨⟨g, hgH⟩, hJL' hg, rfl⟩
  have hBadm : B ∈ admissibleTriples p E := ⟨hBE, hBel, hBcard, S, hS0, hS2', hBS⟩
  have hIb0 : L'.map H.subtype ∈ thetaCompZeroE p E :=
    ⟨B, hBadm, mem_thetaComponentFamily_iff.2 ⟨b, hbA, hb1, hIb⟩, S, hSJ.trans hJIb, hS0, hS2',
      hBS, hSB⟩
  exact hJIb.trans (fun g hg => Subgroup.subset_closure ⟨_, hIb0, hIb, hg⟩)

end CFSG.RankThree.PartOne.S15K
