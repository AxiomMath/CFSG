module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Out
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.Literature.GL52Group
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)

variable {G : Type} [Group G] [Finite G]

theorem rhoL_eq_one_of_mem {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : L ≠ K) {x : G} (hxK : x ∈ K) (hxN : x ∈ normalizer (L : Set G)) :
    UC6S846.rhoL L ⟨x, hxN⟩ = 1 := by
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.one_apply]
    refine (UC6S846.rhoL_fix_iff L ⟨x, hxN⟩ y).2 ?_
    exact (PartTwo.calC_commutator_le_of_ne hK hL hne.symm
      (Subgroup.commutator_mem_commutator hxK y.2)).2

theorem rhoL_ne_one_of_mem {L : Subgroup G} (hZ : center (Bar2 L) = ⊥) {a : G} (haL : a ∈ L)
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) : UC6S846.rhoL L ⟨a, le_normalizer haL⟩ ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [UC6S846.rhoL_inner L a haL]
  intro h
  have hc : (QuotientGroup.mk (⟨a, haL⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun φ : MulAut (Bar2 L) => φ z) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hz
    calc z * _ = (_ * z * _⁻¹) * _ := by rw [hz]
      _ = _ * z := by group
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hc
  exact P2251c.not_mem_of_orderOf_eq_three (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    (orderOf_eq_prime ha3 ha1) (mem_map.2 ⟨⟨a, haL⟩, hc, rfl⟩)

theorem le_centralizer_of_pRank_eq_one {L S A : Subgroup G} (hr : CFSG.Open.pRank 3 L = 1)
    (hSp : IsPGroup 3 S) (hSL : S ≤ normalizer (L : Set G)) (hA : A ≤ S ⊓ L)
    (hA3 : Nat.card A = 3) : A ≤ centralizer (S : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro a ha
  by_cases ha1 : a = 1
  · exact ha1 ▸ one_mem _
  have ha3 : a ^ 3 = 1 := by
    rw [← hA3]
    exact (orderOf_dvd_iff_pow_eq_one).mp (Subgroup.orderOf_dvd_natCard A ha)
  exact P2251c.mem_centralizer_of_isCyclic hSp hSL
    (R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one hr inf_le_right hSp.to_inf_left)
    (hA ha).1 (hA ha).2 (orderOf_eq_prime ha3 ha1)

private theorem mem_map_comap_iff {L : Subgroup G} (Q : Subgroup (MulAut (Bar2 L))) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    x ∈ (Q.comap (UC6S846.rhoL L)).map (normalizer (L : Set G)).subtype ↔
      UC6S846.rhoL L ⟨x, hx⟩ ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · exact fun h => ⟨⟨x, hx⟩, h, rfl⟩

private theorem rhoL_commutator_eq_one {L S : Subgroup G} (hr : CFSG.Open.pRank 3 L = 1)
    (hsh : R8107Shape.ThinShape (Bar2 L) ∨ ∃ n : ℕ, IsU3 (Bar2 L) n) (hSp : IsPGroup 3 S)
    (hSL : S ≤ normalizer (L : Set G)) {a s : G} (ha : a ∈ S) (hs : s ∈ S) (ha3 : a ^ 3 = 1)
    (hs3 : s ^ 3 = 1) :
    UC6S846.rhoL L ⟨a * s * a⁻¹ * s⁻¹,
      hSL (S.mul_mem (S.mul_mem (S.mul_mem ha hs) (S.inv_mem ha)) (S.inv_mem hs))⟩ = 1 := by
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) = 1 := by
    rw [pRank_bar2_eq_of_odd Nat.prime_three (by norm_num), hr]
  have hP : IsPGroup 3 ((S.subgroupOf (normalizer (L : Set G))).map (UC6S846.rhoL L)) :=
    hSp.comap_subtype.map _
  have hcube : ∀ y (hy : y ∈ S), y ^ 3 = 1 → UC6S846.rhoL L ⟨y, hSL hy⟩ ^ 3 = 1 :=
    fun y hy hy3 => by
      rw [← map_pow]
      have : (⟨y, hSL hy⟩ : ↥(normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext hy3
      rw [this, map_one]
  have key := commute_of_pow_three_eq_one hsh h1 hP ⟨⟨a, hSL ha⟩, ha, rfl⟩
    ⟨⟨s, hSL hs⟩, hs, rfl⟩ (hcube a ha ha3) (hcube s hs hs3)
  have he : (⟨a * s * a⁻¹ * s⁻¹, hSL (S.mul_mem (S.mul_mem (S.mul_mem ha hs) (S.inv_mem ha))
      (S.inv_mem hs))⟩ : ↥(normalizer (L : Set G))) =
      ⟨a, hSL ha⟩ * ⟨s, hSL hs⟩ * (⟨a, hSL ha⟩)⁻¹ * (⟨s, hSL hs⟩)⁻¹ := rfl
  rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, key]
  group

private theorem exists_orderOf_eq_three_mem_centralizer {S E : Subgroup G} (hS : IsPGroup 3 S)
    (hES : E ≤ S) (hSE : S ≤ normalizer (E : Set G)) (hE : E ≠ ⊥) :
    ∃ z ∈ E, orderOf z = 3 ∧ z ∈ centralizer (S : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent S := hS.isNilpotent
  haveI : (E.subgroupOf S).Normal := (Subgroup.normal_subgroupOf_iff hES).2
    fun a b ha hb => (mem_normalizer_iff.1 (hSE hb) a).1 ha
  have hne : E.subgroupOf S ≠ ⊥ := fun h0 =>
    hE (by rw [← Subgroup.map_subgroupOf_eq_of_le hES, h0, Subgroup.map_bot])
  set D := E.subgroupOf S ⊓ center S with hD
  haveI : Nontrivial D :=
    (Subgroup.nontrivial_iff_ne_bot D).2 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨n, hn, hcard⟩ := ((hS.to_subgroup D).nontrivial_iff_card).1 inferInstance
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3
    (by rw [hcard]; exact dvd_pow_self 3 (by omega))
  refine ⟨((y : S) : G), (Subgroup.mem_inf.1 y.2).1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]
  · rw [mem_centralizer_iff]
    intro z hz
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 y.2).2) ⟨z, hz⟩)

private theorem false_of_card_eighty_one {M E : Subgroup G} (hM3 : CFSG.Open.pRank 3 M ≤ 3)
    (hEM : E ≤ M) (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 4) : False := by
  have := UC6S846.le_pRank' Nat.prime_three hEM hE hcard
  omega

private theorem exists_eq_zpowers_of_card_three {A : Subgroup G} (hA3 : Nat.card A = 3) :
    ∃ a : G, A = zpowers a ∧ a ^ 3 = 1 ∧ a ≠ 1 := by
  have hne : A ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hA3; omega
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  refine ⟨a, CFSG.Literature.GL52.eq_zpowers_of_card_prime Nat.prime_three hA3 ha ha1', ?_, ha1'⟩
  rw [← hA3]
  exact (orderOf_dvd_iff_pow_eq_one).mp (Subgroup.orderOf_dvd_natCard A ha)

private theorem conj_mem_map_comap_bot {L : Subgroup G} {g x : G}
    (hg : g ∈ normalizer (L : Set G))
    (hx : x ∈ ((⊥ : Subgroup (MulAut (Bar2 L))).comap (UC6S846.rhoL L)).map
      (normalizer (L : Set G)).subtype) :
    g * x * g⁻¹ ∈ ((⊥ : Subgroup (MulAut (Bar2 L))).comap (UC6S846.rhoL L)).map
      (normalizer (L : Set G)).subtype := by
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨g, hg⟩ * y * (⟨g, hg⟩)⁻¹, ?_, rfl⟩
  change UC6S846.rhoL L _ ∈ (⊥ : Subgroup (MulAut (Bar2 L)))
  rw [Subgroup.mem_bot, map_mul, map_mul, map_inv, Subgroup.mem_bot.1 hy]
  group

theorem omega_eq_of_outer {M L₁ L₂ S A₁ A₂ : Subgroup G} {a₀ : G}
    (hL₁ : L₁ ∈ calC M) (hL₂ : L₂ ∈ calC M) (hne : L₁ ≠ L₂)
    (hr₁ : CFSG.Open.pRank 3 L₁ = 1) (hr₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hs₁ : R8107Shape.ThinShape (Bar2 L₁) ∨ ∃ n : ℕ, IsU3 (Bar2 L₁) n)
    (hs₂ : R8107Shape.ThinShape (Bar2 L₂) ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n)
    (hZ₁ : center (Bar2 L₁) = ⊥) (hZ₂ : center (Bar2 L₂) = ⊥)
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S M) (hS₁ : S ≤ normalizer (L₁ : Set G))
    (hS₂ : S ≤ normalizer (L₂ : Set G)) (hM3 : CFSG.Open.pRank 3 M ≤ 3)
    (hA₁ : A₁ ≤ S ⊓ L₁) (hA₁3 : Nat.card A₁ = 3) (hA₂ : A₂ ≤ S ⊓ L₂)
    (hA₂3 : Nat.card A₂ = 3) (ha₀ : a₀ ∈ S) (ha₀3 : a₀ ^ 3 = 1)
    (hout : ¬ IsInnerAut (UC6S846.rhoL L₁ ⟨a₀, hS₁ ha₀⟩)) :
    IsElemAbelian 3 (A₁ ⊔ A₂ ⊔ zpowers a₀) ∧ Nat.card ↥(A₁ ⊔ A₂ ⊔ zpowers a₀) = 3 ^ 3 ∧
      ∀ s ∈ S, s ^ 3 = 1 → s ∈ A₁ ⊔ A₂ ⊔ zpowers a₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSp : IsPGroup 3 S := hS.isPGroup
  obtain ⟨a₂, rfl, ha₂3, ha₂1⟩ := exists_eq_zpowers_of_card_three hA₂3
  have hc₁ := le_centralizer_of_pRank_eq_one hr₁ hSp hS₁ hA₁ hA₁3
  have hc₂ := le_centralizer_of_pRank_eq_one hr₂ hSp hS₂ hA₂ hA₂3
  have ha₂S : a₂ ∈ S := (hA₂ (mem_zpowers a₂)).1
  have ha₂L : a₂ ∈ L₂ := (hA₂ (mem_zpowers a₂)).2
  set K₁ := ((⊥ : Subgroup (MulAut (Bar2 L₁))).comap (UC6S846.rhoL L₁)).map
    (normalizer (L₁ : Set G)).subtype with hK₁
  set K₂ := ((⊥ : Subgroup (MulAut (Bar2 L₂))).comap (UC6S846.rhoL L₂)).map
    (normalizer (L₂ : Set G)).subtype with hK₂
  set I₁ := ((MulAut.conj : Bar2 L₁ →* MulAut (Bar2 L₁)).range.comap (UC6S846.rhoL L₁)).map
    (normalizer (L₁ : Set G)).subtype with hI₁
  have hA₁K₂ : A₁ ≤ K₂ := fun a ha => (mem_map_comap_iff ⊥ (hS₂ (hA₁ ha).1)).2
    (Subgroup.mem_bot.2 (rhoL_eq_one_of_mem hL₂ hL₁ hne.symm (hA₁ ha).2 _))
  have hA₂K₁ : zpowers a₂ ≤ K₁ := fun a ha => (mem_map_comap_iff ⊥ (hS₁ (hA₂ ha).1)).2
    (Subgroup.mem_bot.2 (rhoL_eq_one_of_mem hL₁ hL₂ hne (hA₂ ha).2 _))
  have ha₂K₂ : a₂ ∉ K₂ := fun h => rhoL_ne_one_of_mem hZ₂ ha₂L ha₂3 ha₂1
    (Subgroup.mem_bot.1 ((mem_map_comap_iff ⊥ (le_normalizer ha₂L)).1 h))
  have hA₁K₁ : ∀ x ∈ A₁, x ∈ K₁ → x = 1 := fun x hx hxK => by
    by_contra hx1
    have hx3 : x ^ 3 = 1 := by
      rw [← hA₁3]
      exact (orderOf_dvd_iff_pow_eq_one).mp (Subgroup.orderOf_dvd_natCard A₁ hx)
    exact rhoL_ne_one_of_mem hZ₁ (hA₁ hx).2 hx3 hx1
      (Subgroup.mem_bot.1 ((mem_map_comap_iff ⊥ (le_normalizer (hA₁ hx).2)).1 hxK))
  have hA₁I₁ : A₁ ≤ I₁ := fun a ha => (mem_map_comap_iff _ (le_normalizer (hA₁ ha).2)).2
    ⟨_, (UC6S846.rhoL_inner L₁ a (hA₁ ha).2).symm⟩
  have hK₁I₁ : K₁ ≤ I₁ := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, ⟨1, by rw [map_one]; exact (Subgroup.mem_bot.1 hy).symm⟩, rfl⟩
  have ha₀I₁ : a₀ ∉ I₁ := fun h => hout ((mem_map_comap_iff _ (hS₁ ha₀)).1 h)
  have ha₂A₁ : a₂ ∉ A₁ := fun h => ha₂K₂ (hA₁K₂ h)
  obtain ⟨hE9, hE9c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
    (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₁3) ha₂A₁ ha₂3
    (fun x hx => (mem_centralizer_iff.1 (hc₁ hx) a₂ ha₂S).symm)
  have hEC : A₁ ⊔ zpowers a₂ ≤ centralizer (S : Set G) := sup_le hc₁ hc₂
  have hES : A₁ ⊔ zpowers a₂ ≤ S := sup_le (fun x hx => (hA₁ hx).1) (zpowers_le.2 ha₂S)
  have ha₀E : a₀ ∉ A₁ ⊔ zpowers a₂ := fun h => ha₀I₁ (sup_le hA₁I₁ (hA₂K₁.trans hK₁I₁) h)
  obtain ⟨hA27, hA27c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hE9 ha₀E ha₀3
    (fun x hx => (mem_centralizer_iff.1 (hEC hx) a₀ ha₀).symm)
  have hAS : A₁ ⊔ zpowers a₂ ⊔ zpowers a₀ ≤ S := sup_le hES (zpowers_le.2 ha₀)
  have hcard : Nat.card ↥(A₁ ⊔ zpowers a₂ ⊔ zpowers a₀) = 3 ^ 3 := by
    rw [hA27c, hE9c, hA₁3]; norm_num
  have hC : S ⊓ K₁ ⊓ K₂ = ⊥ := by
    by_contra hCne
    have hnorm : S ≤ normalizer ((S ⊓ K₁ ⊓ K₂ : Subgroup G) : Set G) := fun g hg =>
      Subgroup.mem_normalizer_fintype fun x hx =>
        ⟨⟨S.mul_mem (S.mul_mem hg hx.1.1) (S.inv_mem hg), conj_mem_map_comap_bot (hS₁ hg) hx.1.2⟩,
          conj_mem_map_comap_bot (hS₂ hg) hx.2⟩
    obtain ⟨z, ⟨⟨hzS, hzK₁⟩, hzK₂⟩, hz3, hzc⟩ := exists_orderOf_eq_three_mem_centralizer hSp
      (inf_le_left.trans inf_le_left) hnorm hCne
    have hz3' : z ^ 3 = 1 := hz3 ▸ pow_orderOf_eq_one z
    have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz3; omega
    obtain ⟨h1, h1c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers
      (CFSG.GroupTheory.isElemAbelian_of_card_prime hA₁3) (fun h => hz1 (hA₁K₁ z h hzK₁)) hz3'
      (fun x hx => (mem_centralizer_iff.1 (hc₁ hx) z hzS).symm)
    have hB1S : A₁ ⊔ zpowers z ≤ S := sup_le (fun x hx => (hA₁ hx).1) (zpowers_le.2 hzS)
    obtain ⟨h2, h2c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers h1
      (fun h => ha₂K₂ (sup_le hA₁K₂ (zpowers_le.2 hzK₂) h)) ha₂3
      (fun x hx => mem_centralizer_iff.1 (hc₂ (mem_zpowers a₂)) x (hB1S hx))
    have hB2C : A₁ ⊔ zpowers z ⊔ zpowers a₂ ≤ centralizer (S : Set G) :=
      sup_le (sup_le hc₁ (zpowers_le.2 hzc)) hc₂
    obtain ⟨h3, h3c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers h2
      (fun h => ha₀I₁ (sup_le (sup_le hA₁I₁ (zpowers_le.2 (hK₁I₁ hzK₁))) (hA₂K₁.trans hK₁I₁) h))
      ha₀3 (fun x hx => (mem_centralizer_iff.1 (hB2C hx) a₀ ha₀).symm)
    exact false_of_card_eighty_one hM3
      ((sup_le (sup_le hB1S (zpowers_le.2 ha₂S)) (zpowers_le.2 ha₀)).trans hS.le) h3
      (by rw [h3c, h2c, h1c, hA₁3]; norm_num)
  refine ⟨hA27, hcard, fun s hs hs3 => ?_⟩
  have hcS : a₀ * s * a₀⁻¹ * s⁻¹ ∈ S :=
    S.mul_mem (S.mul_mem (S.mul_mem ha₀ hs) (S.inv_mem ha₀)) (S.inv_mem hs)
  have hmem : a₀ * s * a₀⁻¹ * s⁻¹ ∈ S ⊓ K₁ ⊓ K₂ :=
    ⟨⟨hcS, (mem_map_comap_iff ⊥ (hS₁ hcS)).2
      (Subgroup.mem_bot.2 (rhoL_commutator_eq_one hr₁ hs₁ hSp hS₁ ha₀ hs ha₀3 hs3))⟩,
      (mem_map_comap_iff ⊥ (hS₂ hcS)).2
        (Subgroup.mem_bot.2 (rhoL_commutator_eq_one hr₂ hs₂ hSp hS₂ ha₀ hs ha₀3 hs3))⟩
  rw [hC, Subgroup.mem_bot] at hmem
  have hcs : a₀ * s = s * a₀ := by
    calc a₀ * s = (a₀ * s * a₀⁻¹ * s⁻¹) * (s * a₀) := by group
      _ = s * a₀ := by rw [hmem, one_mul]
  have hAc : A₁ ⊔ zpowers a₂ ⊔ zpowers a₀ ≤ centralizer ({s} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hEC hx) s hs).symm)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hcs))
  by_contra hsA
  obtain ⟨h4, h4c⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hA27 hsA hs3
    (fun x hx => mem_centralizer_singleton_iff.1 (hAc hx))
  exact false_of_card_eighty_one hM3 ((sup_le hAS (zpowers_le.2 hs)).trans hS.le) h4
    (by rw [h4c, hcard]; norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out
