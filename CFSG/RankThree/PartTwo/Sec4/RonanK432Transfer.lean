module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

abbrev imageModCenter {L : Type} [Group L] (P : Subgroup L) : P →* L ⧸ Subgroup.center L :=
  (QuotientGroup.mk' (Subgroup.center L)).comp P.subtype

open scoped IsMulCommutative in
theorem eq_one_of_mem_center_of_abelian_sylow {p : ℕ} [Fact p.Prime] {L : Type} [Group L]
    [Finite L] (hL : Group.IsPerfect L) (P : Sylow p L)
    (hP : ∀ a b : L, a ∈ (P : Subgroup L) → b ∈ (P : Subgroup L) → a * b = b * a)
    {z : L} (hz : z ∈ Subgroup.center L) (hzP : z ∈ (P : Subgroup L)) : z = 1 := by
  haveI : IsMulCommutative (P : Subgroup L) := ⟨⟨fun a b => Subtype.ext (hP a b a.2 b.2)⟩⟩
  have hT1 : ∀ g : L, MonoidHom.transfer (MonoidHom.id (P : Subgroup L)) g = 1 := by
    intro g
    have hg : g ∈ commutator L := by
      rw [hL.commutator_eq_top]
      exact Subgroup.mem_top g
    exact Abelianization.commutator_subset_ker
      (MonoidHom.transfer (MonoidHom.id (P : Subgroup L))) hg
  have hkey : ∀ (k : ℕ) (g₀ : L), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup L) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hzk : z ^ k ∈ Subgroup.center L := pow_mem hz k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hzk g₀, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow (MonoidHom.id (P : Subgroup L)) z hkey
  rw [hT1 z] at h1
  have h2 : z ^ (P : Subgroup L).index = 1 := by
    have := congrArg Subtype.val h1
    simpa using this.symm
  have hcop : Nat.Coprime (orderOf z) (P : Subgroup L).index := by
    obtain ⟨k, hk⟩ := P.isPGroup' (⟨z, hzP⟩ : (P : Subgroup L))
    have hzk : z ^ p ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hzk) ?_
    exact Nat.Coprime.pow_left k
      ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).mpr P.not_dvd_index)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2))

namespace Helpers

theorem isPGroup_imageModCenter {L : Type} [Group L] {p : ℕ} (P : Subgroup L)
    (hP : IsPGroup p P) : IsPGroup p ↥(imageModCenter P).range :=
  hP.of_surjective (imageModCenter P).rangeRestrict (imageModCenter P).rangeRestrict_surjective

theorem two_le_pRank_of_injective {X A : Type} [Group X] [Finite X] [Group A]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 3 ^ 2)
    (f : A →* X) (hf : Function.Injective f) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  unfold CFSG.Open.pRank
  have hcomm' : ∀ a b : f.range, a * b = b * a := by
    intro a b
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  have hel : CFSG.Open.IsElemAbelian 3 f.range := by
    refine ⟨⟨⟨fun a b => hcomm' a b⟩⟩, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]
  have hcard : Nat.card f.range = 3 ^ 2 := by
    rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hbdd : BddAbove {k | ∃ E : Subgroup X, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ k} := by
    refine ⟨Nat.card X, ?_⟩
    rintro k ⟨E, -, -, hk⟩
    have h2 : Nat.card E ≤ Nat.card X := Subgroup.card_le_card_group E
    rw [hk] at h2
    exact (Nat.lt_pow_self (by norm_num : 1 < 3)).le.trans h2
  exact le_csSup hbdd ⟨f.range, le_top, hel, hcard⟩

theorem isCyclic_of_pRank_le_one {X : Type} [Group X] [Finite X]
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) {R : Subgroup X} (hR : IsPGroup 3 R) :
    IsCyclic ↥R := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (IsPGroup 3 ↥R) := ⟨hR⟩
  by_contra hnc
  obtain ⟨E, -, hcard, hel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  haveI := hel.toIsMulCommutative
  have hpow : ∀ a : ↥E, a ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p 3 ↥E)
  have hle := two_le_pRank_of_injective (fun a b => mul_comm' a b) hpow hcard
    (R.subtype.comp E.subtype) (Subtype.val_injective.comp Subtype.val_injective)
  omega

theorem isMulCommutative_of_isCyclic_range {L : Type} [Group L] (P : Subgroup L)
    [IsCyclic ↥(imageModCenter P).range] : IsMulCommutative ↥P := by
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (imageModCenter P).rangeRestrict ?_
  intro x hx
  rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
  have hxZ : (x : L) ∈ Subgroup.center L := (QuotientGroup.eq_one_iff (x : L)).mp hx
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp hxZ g

end Helpers

theorem center_eq_bot_of_pRank_quot_le_one {L : Type} [Group L] [Finite L]
    (hL : Group.IsPerfect L) (hZ : IsPGroup 3 (Subgroup.center L))
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 1) :
    Subgroup.center L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hZP⟩ := IsPGroup.exists_le_sylow hZ
  haveI : IsCyclic ↥(imageModCenter (P : Subgroup L)).range :=
    Helpers.isCyclic_of_pRank_le_one hr
      (Helpers.isPGroup_imageModCenter (P : Subgroup L) P.isPGroup')
  haveI : IsMulCommutative (P : Subgroup L) :=
    Helpers.isMulCommutative_of_isCyclic_range (P : Subgroup L)
  have hPab : ∀ a b : L, a ∈ (P : Subgroup L) → b ∈ (P : Subgroup L) → a * b = b * a :=
    fun a b ha hb => congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : (P : Subgroup L)) ⟨b, hb⟩)
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  exact eq_one_of_mem_center_of_abelian_sylow hL P hPab hz (hZP hz)

theorem three_dvd_card_quot_center {L : Type} [Group L] [Finite L] (hL : Group.IsPerfect L)
    (h3 : 3 ∣ Nat.card L) : 3 ∣ Nat.card (L ⧸ Subgroup.center L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hnd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hzp : IsPGroup 3 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  obtain ⟨P, hgP⟩ := hzp.exists_le_sylow
  have hPZ : ∀ x ∈ (P : Subgroup L), x ∈ Subgroup.center L := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
      (Helpers.isPGroup_imageModCenter (P : Subgroup L) P.isPGroup')
    have hdvd := Subgroup.card_subgroup_dvd_card (imageModCenter (P : Subgroup L)).range
    rw [hn] at hdvd
    have hn0 : n = 0 := by
      by_contra hn0
      exact hnd ((dvd_pow_self 3 hn0).trans hdvd)
    have hR1 : (imageModCenter (P : Subgroup L)).range = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hn, hn0, pow_zero])
    have hmem : imageModCenter (P : Subgroup L) ⟨x, hx⟩ ∈
        (imageModCenter (P : Subgroup L)).range :=
      MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hR1, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  have hPab : ∀ a b : L, a ∈ (P : Subgroup L) → b ∈ (P : Subgroup L) → a * b = b * a :=
    fun a b _ hb => Subgroup.mem_center_iff.mp (hPZ b hb) a
  have hgmem : g ∈ (P : Subgroup L) := hgP (Subgroup.mem_zpowers g)
  have hg1 : g = 1 := eq_one_of_mem_center_of_abelian_sylow hL P hPab (hPZ g hgmem) hgmem
  rw [hg1, orderOf_one] at hg
  norm_num at hg

end CFSG.RankThree.PartTwo.Sec4.RonanK432
