module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofTwelve
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofJ2
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusOrders

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup

theorem perm_three_center : ∀ p : Equiv.Perm (Fin 3), (∀ q : Equiv.Perm (Fin 3), p * q = q * p) →
    p = 1 := by
  decide

set_option maxRecDepth 10000 in
theorem alt_four_center : ∀ p : alternatingGroup (Fin 4),
    (∀ q : alternatingGroup (Fin 4), p * q = q * p) → p = 1 := by
  decide

theorem eq_inv_of_mem_zpowers {X : Type} [Group X] {x y : X} (hx3 : x ^ 3 = 1)
    (hy : y ∈ zpowers x) (hy1 : y ≠ 1) (hyx : y ≠ x) : y = x⁻¹ := by
  rcases mem_zpowers_cube hx3 hy with h | h | h
  · exact absurd h hy1
  · exact absurd h hyx
  · rw [h, sq_eq_inv_of_cube hx3]

theorem j2_exists_inv {X : Type} [Group X] [Finite X] (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {x : X} (hx1 : x ≠ 1)
    (hx3 : x ^ 3 = 1) : ∃ g : X, g * x * g⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hx3g : IsPGroup 3 (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  obtain ⟨P, hxP⟩ := hx3g.exists_le_sylow
  have hxP' : x ∈ (P : Subgroup X) := hxP (mem_zpowers x)
  set Z := (P : Subgroup X) ⊓ centralizer ((P : Subgroup X) : Set X) with hZdef
  obtain ⟨hZ3, -, hext⟩ := Sec14.j2_sylow_facts h415 hX P
  have key : ∀ g ∈ normalizer ((zpowers x : Subgroup X) : Set X), g * x ≠ x * g →
      g * x * g⁻¹ = x⁻¹ := by
    intro g hg hgx
    refine eq_inv_of_mem_zpowers hx3 ((mem_normalizer_iff.mp hg x).mp (mem_zpowers x)) ?_ ?_
    · intro h
      apply hx1
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    · intro h
      apply hgx
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h]
  by_cases hxZ : x ∈ Z
  ·
    have hZx : Z = zpowers x := by
      refine (eq_of_le_of_card_ge (zpowers_le.mpr hxZ) ?_).symm
      rw [hZ3, Nat.card_zpowers, hxo]
    have hN := Sec15.Proof15Res2.j2_card_normalizer_center h415 hX P
    have hC : Nat.card (centralizer (Z : Set X)) = 1080 := by
      rw [Sec6.BThreeCensus.card_of_isExtOf hext, nat_card_alternatingGroup, Nat.card_fin,
        Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      decide
    obtain ⟨g, hgN, hgC⟩ :
        ∃ g ∈ normalizer ((Z : Subgroup X) : Set X), g ∉ centralizer (Z : Set X) := by
      by_contra hcon
      push Not at hcon
      have hle := card_le_of_le (fun g hg => hcon g hg :
        normalizer ((Z : Subgroup X) : Set X) ≤ centralizer (Z : Set X))
      rw [← hZdef] at hN
      rw [hN, hC] at hle
      omega
    refine ⟨g, key g (hZx ▸ hgN) fun hgx => hgC ?_⟩
    rw [mem_centralizer_iff]
    intro z hz
    rw [hZx] at hz
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left hgx.symm k).eq)
  ·
    have hxC : x ∈ centralizer (Z : Set X) :=
      mem_centralizer_iff.mpr fun z hz => (mem_centralizer_iff.mp (mem_inf.mp hz).2 x hxP').symm
    set A := zpowers x ⊔ Z with hAdef
    have hAP : A ≤ P := sup_le hxP inf_le_left
    have hxA : x ∈ A := mem_sup_left (mem_zpowers x)
    have hA9 : Nat.card A = 9 := by
      rw [KFacts.KS14.card_eq_three_mul_card_inf hxC hxZ hx3 le_rfl hxA,
        inf_of_le_right le_sup_right, hZ3]
    obtain ⟨-, ⟨e⟩, -⟩ := (h415 X hX P Z rfl _ rfl).2.2.2.1 A ⟨hAP, hA9⟩ x hxA hxZ
    by_contra hcon
    push Not at hcon
    have hcomm : ∀ g ∈ normalizer ((zpowers x : Subgroup X) : Set X), g * x = x * g := by
      intro g hg
      by_contra hgx
      exact hcon g (key g hg hgx)
    set x' : normalizer ((zpowers x : Subgroup X) : Set X) := ⟨x, le_normalizer (mem_zpowers x)⟩
    have hx'c : ∀ q, e x' * q = q * e x' := by
      intro q
      obtain ⟨q', rfl⟩ := e.surjective q
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm q' q'.2).symm
    have h1 : (e x').1 = 1 := perm_three_center _ fun q => by
      have := congrArg Prod.fst (hx'c (q, 1))
      simpa using this
    have h2 : (e x').2 = 1 := alt_four_center _ fun q => by
      have := congrArg Prod.snd (hx'c (1, q))
      simpa using this
    have h3 : e x' = 1 := Prod.ext h1 h2
    apply hx1
    have := congrArg Subtype.val (e.injective (h3.trans (map_one e).symm))
    simpa [x'] using this

variable {G : Type} [Group G]

theorem exists_inv_of_lBar [Finite G] {L : Subgroup G} {d : G} (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hd3 : d ^ 3 = 1)
    (h : ∃ g : lBar L, g * ((⟨d, hdL⟩ : L) : lBar L) * g⁻¹ = (((⟨d, hdL⟩ : L) : lBar L))⁻¹) :
    ∃ ℓ ∈ L, ℓ * d * ℓ⁻¹ = d⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 L with hNdef
  set d' : L := ⟨d, hdL⟩ with hd'
  have hd'1 : d' ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hd'o : orderOf d' = 3 := orderOf_eq_prime hd'3 hd'1
  have hN3 : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  set π := QuotientGroup.mk' N with hπ
  have hπd1 : π d' ≠ 1 := by
    intro h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply hN3
    rw [← hd'o]
    have := orderOf_dvd_natCard (⟨d', h1⟩ : N)
    rwa [Subgroup.orderOf_mk] at this
  have hπd3 : π d' ^ 3 = 1 := by rw [← map_pow, hd'3, map_one]
  have hπne : π d' ≠ (π d')⁻¹ := by
    intro h1
    apply hπd1
    have h2 : π d' * π d' = 1 := by
      have := mul_inv_cancel (π d')
      rwa [← h1] at this
    have := hπd3
    rwa [pow_succ, sq, h2, one_mul] at this
  obtain ⟨g, hg⟩ := h
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective g
  set y : L := g0 * d' * g0⁻¹ with hy
  have hπy : π y = (π d')⁻¹ := by
    rw [hy, map_mul, map_mul, map_inv]
    exact hg
  set K : Subgroup L := N ⊔ zpowers d' with hK
  have hd'K : d' ∈ K := mem_sup_right (mem_zpowers d')
  have hyK : y ∈ K := by
    have hn : d' * y ∈ N := by
      have : π (d' * y) = 1 := by rw [map_mul, hπy, mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have : y = d'⁻¹ * (d' * y) := by group
    rw [this]
    exact mul_mem (inv_mem hd'K) (mem_sup_left hn)
  have hyo : orderOf y = 3 := by
    have h := orderOf_injective (MulAut.conj g0).toMonoidHom (MulAut.conj g0).injective d'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [hy, h, hd'o]
  have hidx : ¬ 3 ∣ ((zpowers d').subgroupOf K).index := by
    have h1 : ((zpowers d').subgroupOf K).index = (zpowers d').relIndex K := rfl
    rw [h1, hK, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal N (zpowers d')]
    intro h3
    exact hN3 (h3.trans (index_dvd_card _))
  have hcardP2 : Nat.card ((zpowers d').subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hd'K)).toEquiv, Nat.card_zpowers,
      hd'o]
  have hcardP1 : Nat.card ((zpowers y).subgroupOf K) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.mpr hyK)).toEquiv, Nat.card_zpowers,
      hyo]
  have hidx1 : ¬ 3 ∣ ((zpowers y).subgroupOf K).index := by
    have e1 := ((zpowers y).subgroupOf K).card_mul_index
    have e2 := ((zpowers d').subgroupOf K).card_mul_index
    rw [hcardP1] at e1
    rw [hcardP2] at e2
    have : ((zpowers y).subgroupOf K).index = ((zpowers d').subgroupOf K).index := by omega
    rw [this]
    exact hidx
  have hP1 : IsPGroup 3 ((zpowers y).subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by rw [hcardP1, pow_one])
  have hP2 : IsPGroup 3 ((zpowers d').subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by rw [hcardP2, pow_one])
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (hP1.toSylow hidx1) (hP2.toSylow hidx)
  have hmem : (k : L) * y * (k : L)⁻¹ ∈ zpowers d' := by
    have hyP1 : (⟨y, hyK⟩ : K) ∈ ((hP1.toSylow hidx1 : Sylow 3 K) : Subgroup K) :=
      show (⟨y, hyK⟩ : K) ∈ (zpowers y).subgroupOf K from mem_subgroupOf.mpr (mem_zpowers y)
    have h1 : k * ⟨y, hyK⟩ * k⁻¹ ∈ ((k • hP1.toSylow hidx1 : Sylow 3 K) : Subgroup K) := by
      rw [Sec14.coe_sylow_smul_eq_map]
      exact mem_map.mpr ⟨_, hyP1, by simp [MulAut.conj_apply]⟩
    rw [hk] at h1
    have h2 : (k * ⟨y, hyK⟩ * k⁻¹ : K) ∈ (zpowers d').subgroupOf K := h1
    rw [mem_subgroupOf] at h2
    simpa using h2
  have hKle : K ≤ (zpowers (π d')).comap π := by
    refine sup_le ?_ (zpowers_le.mpr (mem_zpowers (π d')))
    intro n hn
    have h1 : π n = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hn
    rw [mem_comap, h1]
    exact one_mem _
  have hπk : Commute (π (k : L)) (π d') := by
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hKle k.2)
    rw [← hj]
    exact Commute.zpow_left (Commute.refl _) j
  set w : L := (k : L) * y * (k : L)⁻¹ with hw
  have hπw : π w = (π d')⁻¹ := by
    rw [hw, map_mul, map_mul, map_inv, hπy, hπk.inv_right.eq, mul_inv_cancel_right]
  have hwd : w = d'⁻¹ := by
    refine eq_inv_of_mem_zpowers hd'3 hmem ?_ ?_
    · intro h1
      apply hπd1
      rw [h1, map_one] at hπw
      exact inv_eq_one.mp hπw.symm
    · intro h1
      apply hπne
      rw [h1] at hπw
      exact hπw
  refine ⟨((k : L) * g0 : L), ((k : L) * g0).2, ?_⟩
  have h1 : ((k : L) * g0) * d' * ((k : L) * g0)⁻¹ = d'⁻¹ := by
    rw [← hwd, hw, hy]
    group
  have h2 := congrArg Subtype.val h1
  simpa using h2

theorem kf2112HJReal_of (h415 : Sec4.Item4_15) : KF2112HJReal := by
  intro G _ _ L hJ d hdL hd1 hd3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine exists_inv_of_lBar hdL hd1 hd3 (j2_exists_inv h415 hJ ?_ ?_)
  · intro h1
    rw [QuotientGroup.eq_one_iff] at h1
    have hN3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
      three_not_dvd_card_aschbacherSolvableCore
    apply hN3
    have hd'1 : (⟨d, hdL⟩ : L) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
    have hd'3 : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    have := orderOf_dvd_natCard (⟨⟨d, hdL⟩, h1⟩ : aschbacherSolvableCore 3 L)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd'3 hd'1] at this
  · rw [← QuotientGroup.mk_pow]
    have hd'3 : (⟨d, hdL⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
    rw [hd'3, QuotientGroup.mk_one]

end CFSG.RankThree.PartTwo.Sec21.Item2113Res2Proof
