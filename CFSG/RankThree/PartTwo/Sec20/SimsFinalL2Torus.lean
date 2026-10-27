module

import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofL2KFact
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer
public import CFSG.RankThree.PartTwo.Sec20.OneTools

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsFinalL2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.BenderSuzuki.MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_odd_of_le_centralizer {Y₀ : Type*} [Group Y₀] {m : ℕ}
    (e : Y₀ ≃* projSL 2 (GaloisField 2 m)) (hns : ¬ Group.IsSolvable Y₀) {x : Y₀} (hx : orderOf x = 3)
    {D : Subgroup Y₀} (hD : D ≤ Subgroup.centralizer ({x} : Set Y₀)) :
    IsCyclic D ∧ Odd (Nat.card D) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F := GaloisField 2 m with hFdef
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  set kk : ℕ := (k : ℕ) with hkk
  have hFk : Nat.card F = 2 ^ kk := by rw [Nat.card_eq_fintype_card]; exact hk
  have hk1 : 1 ≤ kk := k.pos
  set ψ : Y₀ ≃* PSL2MatrixGroup F := e.trans (Sec4.projSLEquivPSL F) with hψ
  have hk2 : 2 ≤ kk := by
    by_contra hlt
    have hk1' : kk = 1 := by omega
    apply hns
    have hP : Nat.card (PSL2MatrixGroup F) = 6 := by
      rw [Nat.card_congr (Res6.pslEquivPgl_of_char_two F hchar).toEquiv,
        CFSG.GorensteinWalter.pgl2_card_formula, hFk, hk1']
      norm_num
    have hY : Nat.card Y₀ < 60 := by
      rw [Nat.card_congr ψ.toEquiv, hP]
      norm_num
    have : Finite Y₀ := Nat.finite_of_card_ne_zero (by rw [Nat.card_congr ψ.toEquiv, hP]; norm_num)
    exact CFSG.GroupTheory.groups_order_below_sixty_solvable hY
  have hx1 : ψ x ≠ 1 := by
    intro h
    have : x = 1 := ψ.injective (by rw [h, map_one])
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hxodd : Odd (orderOf (ψ x)) := by
    rw [MulEquiv.orderOf_eq, hx]
    exact ⟨1, by norm_num⟩
  obtain ⟨hcyc, hcard, -⟩ :=
    CFSG.ShultStronglyClosedTI.TwoCoreGrowth.psl2_even_odd_element_full_centralizer kk hk2 hFk
      (ψ x) hx1 hxodd
  set C := Subgroup.centralizer ({ψ x} : Set (PSL2MatrixGroup F)) with hC
  have hCodd : Odd (Nat.card C) := by
    have h4 : 4 ≤ 2 ^ kk := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ kk := Nat.pow_le_pow_right (by norm_num) hk2
    have h2 : Even (2 ^ kk) := (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨r, hr⟩ := h2
    rw [hFk] at hcard
    generalize 2 ^ kk = q at hr h4 hcard
    rcases hcard with h | h
    · rw [h]
      exact ⟨r - 1, by omega⟩
    · rw [h]
      exact ⟨r, by omega⟩
  set D' := D.map ψ.toMonoidHom with hD'
  have hD'C : D' ≤ C := by
    rintro _ ⟨d, hd, rfl⟩
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hD hd)
    change ψ d * ψ x = ψ x * ψ d
    rw [← map_mul, ← map_mul, h1]
  have hcycD' : IsCyclic D' := by
    have : IsCyclic C := hcyc
    have : IsCyclic (D'.subgroupOf C) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hD'C).toMonoidHom
      (MulEquiv.surjective _)
  have hDD' : D ≃* D' := D.equivMapOfInjective ψ.toMonoidHom ψ.injective
  refine ⟨isCyclic_of_surjective hDD'.symm.toMonoidHom (MulEquiv.surjective _), ?_⟩
  rw [Nat.card_congr hDD'.toEquiv]
  exact Odd.of_dvd_nat hCodd (Subgroup.card_dvd_of_le hD'C)

omit [Finite G] in
theorem commute_of_mem_isCyclic {Q : Type*} [Group Q] {D : Subgroup Q} (hD : IsCyclic D)
    {x y : Q} (hx : x ∈ D) (hy : y ∈ D) : Commute x y := by
  obtain ⟨g, hg⟩ := hD.exists_generator
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have h := (Commute.zpow_zpow_self g i j).eq
  rw [hi, hj] at h
  exact congrArg Subtype.val h

theorem exists_threePrime_part {W 𝒥 : Subgroup G} (h𝒥W : 𝒥 ≤ W)
    (hcyc : IsCyclic ((𝒥.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥W))))
    (hodd : Odd (Nat.card ((𝒥.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥W))))) :
    ∃ J₁ : Subgroup G, J₁ ≤ 𝒥 ∧ 𝒥 ⊓ inSubgroup (CFSG.pPrimeCore 3) W ≤ J₁ ∧
      (∀ y ∈ 𝒥, Nat.Coprime (orderOf y) 3 → y ∈ J₁) ∧
      (∀ t : G, t ∈ Subgroup.normalizer (𝒥 : Set G) →
        t ∈ Subgroup.normalizer (inSubgroup (CFSG.pPrimeCore 3) W : Set G) →
        t ∈ Subgroup.normalizer (J₁ : Set G)) ∧
      ∃ g ∈ J₁, J₁ ≤ (𝒥 ⊓ inSubgroup (CFSG.pPrimeCore 3) W) ⊔ Subgroup.zpowers g ∧
        ∃ k : ℕ, Nat.Coprime k 6 ∧ g ^ k ∈ 𝒥 ⊓ inSubgroup (CFSG.pPrimeCore 3) W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := inSubgroup (CFSG.pPrimeCore 3) W with hO
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥W) with hπ
  set D := (𝒥.subgroupOf W).map π with hD
  set n := Nat.card D with hn
  set a := 3 ^ n.factorization 3 with ha
  set n' := n / a with hn'
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  have han : a * n' = n := Nat.mul_div_cancel' (Nat.ordProj_dvd n 3)
  have hn'3 : Nat.Coprime 3 n' := Nat.coprime_ordCompl Nat.prime_three hn0
  have hn'dvd : n' ∣ n := Nat.div_dvd_of_dvd (Nat.ordProj_dvd n 3)
  have hn'odd : Odd n' := Odd.of_dvd_nat hodd hn'dvd
  have hn'6 : Nat.Coprime n' 6 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hn'odd) hn'3.symm
  have hker : ∀ w : ↥W, π w = 1 ↔ (w : G) ∈ O := by
    intro w
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨w, h, rfl⟩
    · rintro ⟨w', hw', hww'⟩
      rwa [← Subtype.ext hww']
  have hπD : ∀ (g : G) (hg : g ∈ 𝒥), π ⟨g, h𝒥W hg⟩ ∈ D := fun g hg =>
    ⟨⟨g, h𝒥W hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hpowO : ∀ (g : G) (hg : g ∈ W), g ^ n' ∈ O ↔ (π ⟨g, hg⟩) ^ n' = 1 := by
    intro g hg
    rw [← map_pow, hker]
    exact Iff.rfl
  let J₁ : Subgroup G :=
    { carrier := {g | g ∈ 𝒥 ∧ g ^ n' ∈ O}
      mul_mem' := by
        rintro g h ⟨hg, hgO⟩ ⟨hh, hhO⟩
        refine ⟨𝒥.mul_mem hg hh, ?_⟩
        rw [hpowO _ (h𝒥W (𝒥.mul_mem hg hh))]
        rw [hpowO _ (h𝒥W hg)] at hgO
        rw [hpowO _ (h𝒥W hh)] at hhO
        have hsplit : (⟨g * h, h𝒥W (𝒥.mul_mem hg hh)⟩ : ↥W) = ⟨g, h𝒥W hg⟩ * ⟨h, h𝒥W hh⟩ := rfl
        rw [hsplit, map_mul, (commute_of_mem_isCyclic hcyc (hπD g hg) (hπD h hh)).mul_pow, hgO,
          hhO, one_mul]
      one_mem' := ⟨𝒥.one_mem, by rw [one_pow]; exact O.one_mem⟩
      inv_mem' := by
        rintro g ⟨hg, hgO⟩
        exact ⟨𝒥.inv_mem hg, by rw [inv_pow]; exact O.inv_mem hgO⟩ }
  have hmemJ₁ : ∀ g : G, g ∈ J₁ ↔ g ∈ 𝒥 ∧ g ^ n' ∈ O := fun g => Iff.rfl
  have hordD : ∀ (g : G) (hg : g ∈ 𝒥), orderOf (π ⟨g, h𝒥W hg⟩) ∣ n := by
    intro g hg
    have h1 := orderOf_dvd_natCard (⟨π ⟨g, h𝒥W hg⟩, hπD g hg⟩ : D)
    rwa [Subgroup.orderOf_mk] at h1
  obtain ⟨d₀, hd₀⟩ := hcyc.exists_generator
  obtain ⟨⟨g₀, hg₀W⟩, hg₀𝒥, hg₀d⟩ := d₀.2
  have hg₀𝒥' : g₀ ∈ 𝒥 := Subgroup.mem_subgroupOf.mp hg₀𝒥
  have hord₀ : orderOf (d₀ : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) = n := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hd₀]
  have hpowD : ∀ z ∈ D, z ^ n' = 1 → ∃ j : ℤ, z = ((π ⟨g₀, hg₀W⟩) ^ a) ^ j := by
    intro z hz hzn
    have hcop : Nat.Coprime a (orderOf z) :=
      Nat.Coprime.pow_left _ (Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hzn)
        hn'3)
    obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime hcop
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hd₀ ⟨z ^ r, D.pow_mem hz r⟩)
    refine ⟨j, ?_⟩
    have hj' : (d₀ : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) ^ j = z ^ r := congrArg Subtype.val hj
    calc z = (z ^ a) ^ r := hr.symm
      _ = (z ^ r) ^ a := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ = ((d₀ : ↥W ⧸ CFSG.pPrimeCore 3 ↥W) ^ j) ^ a := by rw [hj']
      _ = ((π ⟨g₀, hg₀W⟩) ^ a) ^ j := by rw [hg₀d]; group
  set g := g₀ ^ a with hgdef
  have hg𝒥 : g ∈ 𝒥 := 𝒥.pow_mem hg₀𝒥' a
  have hgn : g ^ n' ∈ O := by
    rw [hpowO _ (h𝒥W hg𝒥)]
    have hsplit : (⟨g, h𝒥W hg𝒥⟩ : ↥W) = ⟨g₀, hg₀W⟩ ^ a := rfl
    rw [hsplit, map_pow, ← pow_mul, han, hg₀d, ← hord₀, pow_orderOf_eq_one]
  refine ⟨J₁, fun g hg => hg.1, ?_, ?_, ?_, g, ⟨hg𝒥, hgn⟩, ?_, n', hn'6, ⟨𝒥.pow_mem hg𝒥 _, hgn⟩⟩
  ·
    rintro o ⟨ho𝒥, hoO⟩
    exact ⟨ho𝒥, O.pow_mem hoO _⟩
  ·
    intro y hy hy3
    refine ⟨hy, ?_⟩
    rw [hpowO _ (h𝒥W hy)]
    have h1 : orderOf (π ⟨y, h𝒥W hy⟩) ∣ orderOf y := by
      have := orderOf_map_dvd π (⟨y, h𝒥W hy⟩ : ↥W)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : Nat.Coprime (orderOf (π ⟨y, h𝒥W hy⟩)) a :=
      Nat.Coprime.pow_right _ (Nat.Coprime.coprime_dvd_left h1 hy3)
    have h3 : orderOf (π ⟨y, h𝒥W hy⟩) ∣ a * n' := by rw [han]; exact hordD y hy
    exact orderOf_dvd_iff_pow_eq_one.mp (h2.dvd_of_dvd_mul_left h3)
  ·
    intro t ht𝒥 htO
    apply Sec20.mem_normalizer_of_map_conj_le
    rintro _ ⟨x, ⟨hx𝒥, hxO⟩, rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp ht𝒥 x).mp hx𝒥, ?_⟩
    change (t * x * t⁻¹) ^ n' ∈ O
    rw [conj_pow]
    exact (Subgroup.mem_normalizer_iff.mp htO _).mp hxO
  ·
    rintro h ⟨hh𝒥, hhO⟩
    rw [hpowO _ (h𝒥W hh𝒥)] at hhO
    obtain ⟨j, hj⟩ := hpowD _ (hπD h hh𝒥) hhO
    have hsplit : π ⟨h, h𝒥W hh𝒥⟩ = π (⟨g, h𝒥W hg𝒥⟩ ^ j) := by
      have e1 : (⟨g, h𝒥W hg𝒥⟩ : ↥W) = ⟨g₀, hg₀W⟩ ^ a := rfl
      rw [hj, map_zpow, e1, map_pow]
    have hmemO : h * (g ^ j)⁻¹ ∈ O := by
      have h1 : π (⟨h, h𝒥W hh𝒥⟩ * (⟨g, h𝒥W hg𝒥⟩ ^ j)⁻¹) = 1 := by
        rw [map_mul, map_inv, hsplit, mul_inv_cancel]
      rw [hker] at h1
      simpa using h1
    have hmem𝒥 : h * (g ^ j)⁻¹ ∈ 𝒥 := 𝒥.mul_mem hh𝒥 (𝒥.inv_mem (𝒥.zpow_mem hg𝒥 j))
    have e : h = (h * (g ^ j)⁻¹) * g ^ j := by group
    rw [e]
    exact Subgroup.mul_mem_sup ⟨hmem𝒥, hmemO⟩ (Subgroup.zpow_mem_zpowers g j)

theorem relIndex_dvd_of_le_sup_zpowers {Γ : Type*} [Group Γ] {J O : Subgroup Γ} (hOJ : O ≤ J)
    (hn : (O.subgroupOf J).Normal) {g : Γ} (hgJ : g ∈ J) (hJ : J ≤ O ⊔ Subgroup.zpowers g)
    {k : ℕ} (hk : g ^ k ∈ O) : O.relIndex J ∣ k := by
  have hJN : J ≤ Subgroup.normalizer (O : Set Γ) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOJ).mp hn
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (O : Set Γ) :=
    Subgroup.zpowers_le.mpr (hJN hgJ)
  set gbar : ↥J ⧸ O.subgroupOf J := ((⟨g, hgJ⟩ : J) : ↥J ⧸ O.subgroupOf J) with hgbar
  have hgen : ∀ q : ↥J ⧸ O.subgroupOf J, q ∈ Subgroup.zpowers gbar := by
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hj : (j : Γ) ∈ ((Subgroup.zpowers g ⊔ O : Subgroup Γ) : Set Γ) := by
      rw [sup_comm]
      exact hJ j.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN] at hj
    obtain ⟨u, hu, o, ho, huo⟩ := hj
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have hoJ : o ∈ J := hOJ ho
    have hsplit : j = (⟨g, hgJ⟩ : J) ^ i * ⟨o, hoJ⟩ := Subtype.ext (by simpa using huo.symm)
    rw [hsplit, QuotientGroup.mk_mul, QuotientGroup.mk_zpow,
      (QuotientGroup.eq_one_iff (⟨o, hoJ⟩ : J)).mpr (Subgroup.mem_subgroupOf.mpr ho), mul_one]
  have hcard : orderOf gbar = O.relIndex J := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen]
    rfl
  rw [← hcard]
  apply orderOf_dvd_of_pow_eq_one
  rw [hgbar, ← QuotientGroup.mk_pow]
  exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))

end CFSG.RankThree.PartTwo.Sec20.SimsFinalL2
