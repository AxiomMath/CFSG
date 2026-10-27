module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Cover
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Coords
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeL81Action
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
public import CFSG.LieType.Multipliers.U62Sylow

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.StandardType
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem mem_O2Z_of_pow {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : L}
    (hz : z ∈ center L) {k : ℕ} (hk : z ^ 2 ^ k = 1) : (z : G) ∈ O2Z L := by
  refine ⟨z.2, fun y hy => ?_, ?_⟩
  · exact congrArg Subtype.val ((mem_center_iff.1 hz ⟨y, hy⟩).symm)
  · obtain ⟨j, hj, hjo⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
    have hdvd : 2 ^ j ∣ Nat.card G := by
      rw [← hjo, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard _
    have hjlt : j ≤ Nat.card G := by
      have h1 := Nat.le_of_dvd Nat.card_pos hdvd
      have h2 : j < 2 ^ j := Nat.lt_two_pow_self
      omega
    rw [← Subgroup.coe_pow, ← Nat.sub_add_cancel hjlt, pow_add, mul_comm, pow_mul, ← hjo,
      pow_orderOf_eq_one, one_pow]
    rfl

theorem mem_centralizer_O2Z_iff {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (b : normalizer (L : Set G)) :
    (b : G) ∈ centralizer (O2Z L : Set G) ↔
      ∀ z ∈ center L, (∃ k : ℕ, z ^ 2 ^ k = 1) → normalizerMonoidHom L b z = z := by
  constructor
  · rintro hb z hz ⟨k, hk⟩
    have h := mem_centralizer_iff.1 hb _ (mem_O2Z_of_pow hz hk)
    apply Subtype.ext
    change (b : G) * z * (b : G)⁻¹ = z
    rw [← h, mul_inv_cancel_right]
  · intro h
    rw [mem_centralizer_iff]
    rintro g ⟨hgL, hgc, hg2⟩
    have hz : (⟨g, hgL⟩ : L) ∈ center L :=
      mem_center_iff.2 fun y => Subtype.ext (hgc y y.2).symm
    have e := congrArg Subtype.val (h _ hz ⟨Nat.card G, Subtype.ext (by simpa using hg2)⟩)
    change (b : G) * g * (b : G)⁻¹ = g at e
    calc g * b = (b : G) * g * (b : G)⁻¹ * b := by rw [e]
      _ = b * g := by group

theorem lemma81Input_holds :
    Lemma81Input := by
  intro G _ _ B Bs x L A κ m hctx
  obtain ⟨hset, hev, -, -, hALA, -, hW5, hW⟩ := hctx
  obtain ⟨hyp, hbstar, hBs_card, hBs_norm, hmodel⟩ := hset
  obtain ⟨-, -, -, hcomp, hcyc, hperf, -, -⟩ := ggThmIHyp_unpack hyp
  haveI : Group.IsPerfect L := Group.isPerfect_def.2 hperf
  have hBab : IsElemAbelian 3 Bs := hbstar.2.1
  set ν := (outerAction L).comp (inclusion hBs_norm) with hν
  have hα3 : ∀ b : Bs, normalizerMonoidHom L (inclusion hBs_norm b) ^ 3 = 1 := fun b => by
    have : b ^ 3 = 1 := Subtype.ext (by simpa using hBab.2 b b.2)
    rw [← map_pow, ← map_pow, this, map_one, map_one]
  have hνα : ∀ b, ν b = 1 ↔ normalizerMonoidHom L (inclusion hBs_norm b) ∈ inner L :=
    fun b => QuotientGroup.eq_one_iff _
  obtain ⟨b₀, hb₀⟩ := exists_outerAction_ne_one hmodel hBab hBs_card hBs_norm hcyc
  have hb₀out : normalizerMonoidHom L (inclusion hBs_norm b₀) ∉ inner L :=
    fun h => hb₀ ((hνα b₀).2 h)
  have hO2le : O2Z L ≤ L := fun g hg => hg.1
  have hcard4 : Nat.card (O2Z L) = 4 := by
    have := card_two_part_eq_four hev hmodel _ (hα3 b₀) hb₀out ((O2Z L).subgroupOf L)
      (fun z hz => mem_center_iff.2 fun y => Subtype.ext (hz.2.1 y y.2).symm)
      (fun z => ⟨Nat.card G, Subtype.ext (Subtype.ext (by simpa using z.2.2.2))⟩)
      (fun z hz ⟨k, hk⟩ => mem_O2Z_of_pow hz hk)
    rw [← this]
    exact (Nat.card_congr (subgroupOfEquivOfLe hO2le).toEquiv).symm
  have hALcard : Nat.card (ggAutomizer L Bs) = 720 := by
    obtain ⟨E, -⟩ := exists_permEquiv_of_ggWeylOfType_A hW5
    rw [← Nat.card_congr E.toEquiv, Nat.card_perm, Nat.card_fin]
    rfl
  refine ⟨hcard4, fun b hb => ?_⟩
  refine (mem_centralizer_O2Z_iff (inclusion hBs_norm ⟨b, hb⟩) :
    b ∈ centralizer (O2Z L : Set G) ↔ _).trans ?_
  rw [fix_two_iff_inner hev hmodel _ (hα3 _), ← hνα]
  exact ker_eq_of_invariant hW hALA
    (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hW.x_mem⟩) hcomp.1 hφ)
    hALcard ν (fun φ hφ b => outerAction_ggAutomizer hBs_norm hφ b) ⟨b₀, hb₀⟩ ⟨b, hb⟩

end CFSG.GGQ2Prime
