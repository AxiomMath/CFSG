module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeU52Models
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Witness46

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models
open scoped commutatorElement Pointwise

theorem lem1025_comm_le_of_split {G : Type} [Group G] {L H Y : Subgroup G} (hY : Y ≤ L)
    (hsplit : ∀ h ∈ H, ∃ c ∈ L ⊓ centralizer (L : Set G), ∃ y ∈ Y, h = c * y) :
    ⁅H, H⁆ ≤ Y := by
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨c, ⟨hcL, hcc⟩, y, hy, rfl⟩ := hsplit a ha
  obtain ⟨d, ⟨hdL, hdc⟩, w, hw, rfl⟩ := hsplit b hb
  have hcc' : ∀ e ∈ centralizer (L : Set G), ∀ l ∈ L, e * l * e⁻¹ = l := fun e he l hl => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (mem_centralizer_iff.1 he l hl).symm
  have hyL : y ∈ L := hY hy
  have hwL : w ∈ L := hY hw
  have hyd : y * d = d * y := mem_centralizer_iff.1 hdc y hyL
  have hmem : y * (d * w) * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL (L.mul_mem hdL hwL)) (L.inv_mem hyL)
  have hmem2 : y * w * y⁻¹ * w⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem hyL hwL) (L.inv_mem hyL)) (L.inv_mem hwL)
  have key : ⁅c * y, d * w⁆ = y * w * y⁻¹ * w⁻¹ := by
    calc ⁅c * y, d * w⁆ = c * (y * (d * w) * y⁻¹) * c⁻¹ * (d * w)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = (y * (d * w) * y⁻¹) * (d * w)⁻¹ := by rw [hcc' c hcc _ hmem]
      _ = (y * d * w * y⁻¹) * (w⁻¹ * d⁻¹) := by group
      _ = d * (y * w * y⁻¹ * w⁻¹) * d⁻¹ := by rw [hyd]; group
      _ = y * w * y⁻¹ * w⁻¹ := hcc' d hdc _ hmem2
  rw [key]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy hw) (Y.inv_mem hy)) (Y.inv_mem hw)

theorem lem1025_mem_normalizer_comm {G : Type} [Group G] {H : Subgroup G} {b : G}
    (hb : b ∈ normalizer (H : Set G)) : b ∈ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  have key : ∀ b ∈ normalizer (H : Set G), ∀ z ∈ ⁅H, H⁆, b * z * b⁻¹ ∈ ⁅H, H⁆ := by
    intro b hb z hz
    have hle : H.map (MulAut.conj b).toMonoidHom ≤ H := by
      rintro _ ⟨h, hh, rfl⟩
      exact (mem_normalizer_iff.1 hb h).1 hh
    have := commutator_mono hle hle
    rw [← map_commutator] at this
    exact this ⟨z, hz, rfl⟩
  rw [mem_normalizer_iff]
  intro z
  refine ⟨key b hb z, fun h => ?_⟩
  have := key b⁻¹ (inv_mem hb) _ h
  simpa [mul_assoc] using this

theorem lem1025_mem_normalizer_cent {G : Type} [Group G] {L : Subgroup G} {z b : G}
    (hb : b ∈ normalizer (L : Set G)) (hbz : b * z = z * b) :
    b ∈ normalizer ((L ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
  have hc : b⁻¹ * z = z * b⁻¹ := (Commute.inv_left hbz).eq
  rw [mem_normalizer_iff]
  intro h
  rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    ← mem_normalizer_iff.1 hb h]
  refine and_congr_right fun _ => ?_
  have e1 : b * h * b⁻¹ * z = b * (h * z) * b⁻¹ := by
    calc b * h * b⁻¹ * z = b * h * (b⁻¹ * z) := by group
      _ = b * h * (z * b⁻¹) := by rw [hc]
      _ = b * (h * z) * b⁻¹ := by group
  have e2 : z * (b * h * b⁻¹) = b * (z * h) * b⁻¹ := by
    calc z * (b * h * b⁻¹) = (z * b) * h * b⁻¹ := by group
      _ = (b * z) * h * b⁻¹ := by rw [hbz]
      _ = b * (z * h) * b⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro h1
    rw [h1]
  · intro h1
    simpa using h1

theorem lem1025_exists_mul_of_mem_sup {G : Type} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {b : G} (hb : b ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, b = h * k := by
  have hle : H ≤ normalizer (K : Set G) := fun h hh => by
    have hconj : ∀ k ∈ K, h * k * h⁻¹ = k := fun k hk => by
      rw [mul_inv_eq_iff_eq_mul]; exact hc h hh k hk
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => by rw [hconj k hk]; exact hk, fun hk => ?_⟩
    have := hc h⁻¹ (H.inv_mem hh) _ hk
    have e : h⁻¹ * (h * k * h⁻¹) * h = k := by group
    rw [← e, this]
    simpa using hk
  have hmul : ((H ⊔ K : Subgroup G) : Set G) = (H : Set G) * (K : Set G) :=
    coe_mul_of_left_le_normalizer_right H K hle
  have hb' : b ∈ (H : Set G) * (K : Set G) := by rw [← hmul]; exact hb
  obtain ⟨h, hh, k, hk, hbk⟩ := Set.mem_mul.1 hb'
  exact ⟨h, hh, k, hk, hbk.symm⟩

theorem lem1025_card_sup {G : Type} [Group G] {H K : Subgroup G}
    (hc : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) (hd : ∀ g ∈ H, g ∈ K → g = 1) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let f : H × K → (H ⊔ K : Subgroup G) := fun p =>
    ⟨p.1 * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => ?_, fun s => ?_⟩
    · have h1 : (p.1 : G) * p.2 = q.1 * q.2 := congrArg Subtype.val hpq
      have h2 : (q.1 : G)⁻¹ * p.1 = q.2 * (p.2 : G)⁻¹ := by
        calc (q.1 : G)⁻¹ * p.1 = (q.1 : G)⁻¹ * (p.1 * p.2) * (p.2 : G)⁻¹ := by group
          _ = q.2 * (p.2 : G)⁻¹ := by rw [h1]; group
      have h3 : (q.1 : G)⁻¹ * p.1 = 1 :=
        hd _ (H.mul_mem (H.inv_mem q.1.2) p.1.2) (h2 ▸ K.mul_mem q.2.2 (K.inv_mem p.2.2))
      have h4 : (p.1 : G) = q.1 := (inv_mul_eq_one.1 h3).symm
      have h5 : (p.2 : G) = q.2 := by rw [h4] at h1; exact mul_left_cancel h1
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    · obtain ⟨h, hh, k, hk, hs⟩ := lem1025_exists_mul_of_mem_sup hc s.2
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hs.symm⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

private theorem le_comm_of_simple {G : Type} [Group G] {X : Subgroup G} [IsSimpleGroup X]
    (hnc : ∃ a b : X, a * b ≠ b * a) : X ≤ ⁅X, X⁆ := by
  have hperf : commutator X = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · obtain ⟨a, b, hab⟩ := hnc
      exfalso
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator X := by
        rw [commutator_def]
        exact commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  exact (Subgroup.isPerfect_iff.1 ⟨hperf⟩).ge

private theorem classicalModel_of_PSU {G : Type} [Group G] {X : Subgroup G} {n : ℕ} (hn : n ≠ 0)
    (h : LieModel X .PSU n 2 1) : StatedClassicalModel X .PSU n 2 1 := by
  rcases h.2 with h | ⟨h, -⟩
  · exact h
  · exact absurd h hn

private theorem lem1025_card_U52 {G : Type} [Group G] {X : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) :
    Nat.card X = 13685760 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_five_two
    (classicalModel_of_PSU (by omega) hX)

private theorem lem1025_le_comm_U52 {G : Type} [Group G] {X : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) : X ≤ ⁅X, X⁆ := by
  have hm := classicalModel_of_PSU (by omega) hX
  have hcard := lem1025_card_U52 hX
  haveI : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact le_comm_of_simple (exists_noncomm_of_simple Nat.prime_two (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num))

theorem lem1025_le_comm_U42 {G : Type} [Group G] {X : Subgroup G} (hX : LieModel X .PSU 4 2 1) :
    X ≤ ⁅X, X⁆ := by
  have hm := classicalModel_of_PSU (by omega) hX
  have hcard := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two hm
  haveI : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
  haveI : Finite X := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact le_comm_of_simple (exists_noncomm_of_simple Nat.prime_two (by rw [hcard]; norm_num)
    (by rw [hcard]; norm_num))

theorem lem1025_eq_comm_of_split {G : Type} [Group G] [Finite G] {L H X X' : Subgroup G}
    (hX : LieModel X .PSU 5 2 1) (hX' : LieModel X' .PSU 5 2 1) (hXH : X ≤ H) (hX'L : X' ≤ L)
    (hsplit : ∀ h ∈ H, ∃ c ∈ L ⊓ centralizer (L : Set G), ∃ y ∈ X', h = c * y) :
    ⁅H, H⁆ = X ∧ X' = X := by
  have hle : X ≤ ⁅H, H⁆ := (lem1025_le_comm_U52 hX).trans (commutator_mono hXH hXH)
  have h1 : X ≤ X' := hle.trans (lem1025_comm_le_of_split hX'L hsplit)
  have hcard : Nat.card X' ≤ Nat.card X := by
    rw [lem1025_card_U52 hX, lem1025_card_U52 hX']
  have h2 : X = X' := eq_of_le_of_card_ge h1 hcard
  exact ⟨le_antisymm (h2 ▸ lem1025_comm_le_of_split hX'L hsplit) hle, h2.symm⟩

end CFSG.GGQ2Prime
