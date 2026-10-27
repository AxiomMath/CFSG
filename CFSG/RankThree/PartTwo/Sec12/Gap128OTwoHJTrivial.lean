module

public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJCases
import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJE8

public section

namespace CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Census (CriticalAt)
open CFSG.Assembly.RankThreeEven (localRank)
open scoped IsMulCommutative commutatorElement

@[expose] def omegaOneCenter {G : Type*} [Group G] (Q : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ Q ∧ (∀ y ∈ Q, x * y = y * x) ∧ x ^ 2 = 1}
  mul_mem' := by
    rintro a b ⟨haQ, hac, ha2⟩ ⟨hbQ, hbc, hb2⟩
    refine ⟨mul_mem haQ hbQ, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · rw [(show Commute a b from hac b hbQ).mul_pow 2, ha2, hb2, one_mul]
  one_mem' := ⟨one_mem _, fun y _ => by rw [one_mul, mul_one], one_pow 2⟩
  inv_mem' := by
    rintro a ⟨haQ, hac, ha2⟩
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ha2)
    change a⁻¹ ∈ Q ∧ (∀ y ∈ Q, a⁻¹ * y = y * a⁻¹) ∧ a⁻¹ ^ 2 = 1
    rw [hinv]
    exact ⟨haQ, hac, ha2⟩

theorem mem_omegaOneCenter {G : Type*} [Group G] {Q : Subgroup G} {x : G} :
    x ∈ omegaOneCenter Q ↔ x ∈ Q ∧ (∀ y ∈ Q, x * y = y * x) ∧ x ^ 2 = 1 :=
  Iff.rfl

theorem omegaOneCenter_normal {G : Type*} [Group G] (Q : Subgroup G) [hQ : Q.Normal] :
    (omegaOneCenter Q).Normal := by
  constructor
  rintro x ⟨hxQ, hxc, hx2⟩ g
  refine ⟨hQ.conj_mem x hxQ g, fun y hy => ?_, ?_⟩
  · have hy' : g⁻¹ * y * g ∈ Q := by simpa using hQ.conj_mem y hy g⁻¹
    have h := hxc _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [h]
      _ = y * (g * x * g⁻¹) := by group
  · rw [conj_pow, hx2, mul_one, mul_inv_cancel]

theorem omegaOneCenter_ne_bot {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) : omegaOneCenter Q ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hne
  have : Nontrivial (Subgroup.center Q) := hQ.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center Q) := by
    rcases (hQ.to_subgroup (Subgroup.center Q)).card_eq_or_dvd with hone | hdiv
    · have : Subsingleton (Subgroup.center Q) := (Nat.card_eq_one_iff_unique.mp hone).1
      exact (not_subsingleton (Subgroup.center Q) this).elim
    · exact hdiv
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 hdvd
  have hc' : orderOf ((c : Q) : G) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  intro hbot
  have hmem : ((c : Q) : G) ∈ omegaOneCenter Q := by
    refine ⟨(c : Q).2, fun y hy => ?_, ?_⟩
    · have h := Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩
      exact (congrArg Subtype.val h).symm
    · rw [← hc']
      exact pow_orderOf_eq_one _
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hc'
  exact absurd hc' (by norm_num)

theorem fin_three_sq : ∀ a : Multiplicative (Fin 3 → ZMod 2), a ^ 2 = 1 := by decide

theorem card_fin_three : Nat.card (Multiplicative (Fin 3 → ZMod 2)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  norm_num

theorem ker_eq_bot_of_localRank
    {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (π : Y →* NativeSporadic.J2) (hπ : Function.Surjective π) (hK : Group.IsSolvable π.ker)
    (h3 : ¬ 3 ∣ Nat.card π.ker) (hO2 : CFSG.pCore 2 Y = ⊥)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p Y < 3) : π.ker = ⊥ := by
  have hJ := CFSG.Sporadic.J2.isSimpleGroup_J2
  by_contra hne
  obtain ⟨p, hp, hp3, D, hD, hDK⟩ := exists_critical π hπ hK h3 hO2 hne
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hlocp := hloc p hp hp3
  by_cases hcent : ∃ t : Y, (∀ d ∈ D, t * d = d * t) ∧ t ^ 2 = 1 ∧ t ≠ 1
  · obtain ⟨t, htD, ht2, ht1⟩ := hcent
    have hDr := Sec4.Census.pRank_le_localRank_of_centralizes hp hp2 (orderOf_eq_prime ht2 ht1)
      (H := D) fun h hh => (htD h hh).symm
    exact false_of_pRank_le_two π hπ hp2 hD hDK (by omega)
  have hodd : ∀ t : Y, (∀ d ∈ D, t * d = d * t) → t ^ 2 = 1 → t = 1 :=
    fun t h1 h2 => by_contra fun h => hcent ⟨t, h1, h2, h⟩
  obtain ⟨V, _, _, _, ρ, hρ, -, hfixV⟩ := exists_frattiniModule hp2 hD
  have hker : ∀ g, ρ g = 1 → π g = 1 := fun g hg => hDK (hρ g hg)
  have hfix : ∀ t : Y, t ^ 2 = 1 → t ≠ 1 →
      Module.finrank (ZMod p) ((ρ t).eigenspace 1) ≤ 2 := fun t ht2 ht1 =>
    hfixV t ht2 (by have := pRank_fixedSubgroupOf_le hp2 hD ht2 ht1; omega)
  have he8 : ∀ {A : Type} [CommGroup A] [Finite A], (∀ a : A, a ^ 2 = 1) → Nat.card A = 8 →
      ∀ ι : A →* Y, Function.Injective ι → False :=
    fun hA2 hA8 ι hι => false_of_e8 π hπ hp2 hlocp hD hDK hodd hA2 hA8 ι hι
  obtain ⟨ιJ, hιJ⟩ := exists_injective_e8_j2
  by_cases hodd2 : ¬ 2 ∣ Nat.card π.ker
  · obtain ⟨ι, hι⟩ := exists_injective_lift π hπ hodd2 card_e8 ιJ hιJ
    exact he8 e8_sq card_e8 ι hι
  rw [not_not] at hodd2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 π.ker) := inferInstance
  set T' := (T : Subgroup π.ker).map π.ker.subtype with hT'
  have hT'ne : T' ≠ ⊥ := fun h => T.ne_bot_of_dvd_card hodd2
    ((Subgroup.map_eq_bot_iff_of_injective _ π.ker.subtype_injective).mp h)
  have hT'2 : IsPGroup 2 T' := T.isPGroup'.map _
  set H := Subgroup.normalizer (T' : Set Y) with hH
  have hHπ : H.map π = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hπ y
    have hx : x ∈ H ⊔ π.ker := by
      rw [hH, hT', Sylow.normalizer_sup_eq_top T]
      trivial
    obtain ⟨h, hh, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨h, hh, ?_⟩
    rw [map_mul, (MonoidHom.mem_ker).mp hk, mul_one]
  have : Finite (Subgroup Y) :=
    Finite.of_injective (fun K : Subgroup Y => (K : Set Y)) SetLike.coe_injective
  obtain ⟨L, ⟨hLH, hLπ⟩, hmin⟩ :=
    (Set.toFinite {L : Subgroup Y | L ≤ H ∧ L.map π = ⊤}).exists_minimal ⟨H, le_rfl, hHπ⟩
  have hJp : Group.IsPerfect NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup hJ
      (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)).1
  have hLL : ⁅L, L⁆ = L := by
    have hle : ⁅L, L⁆ ≤ L := Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    refine le_antisymm hle (hmin ⟨hle.trans hLH, ?_⟩ hle)
    rw [Subgroup.map_commutator, hLπ, ← commutator_def, Group.IsPerfect.commutator_eq_top]
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLL
  set πL := π.comp L.subtype with hπLdef
  have hπL : Function.Surjective πL := by
    intro y
    have hy : y ∈ L.map π := by
      rw [hLπ]
      trivial
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let fK : πL.ker →* π.ker :=
    (L.subtype.comp πL.ker.subtype).codRestrict π.ker fun x => x.2
  have hfK : Function.Injective fK := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun w : π.ker => (w : Y)) h))
  have hKL : Group.IsSolvable πL.ker := Group.isSolvable_of_isSolvable_injective hfK
  have h3L : ¬ 3 ∣ Nat.card πL.ker := fun h => h3 (h.trans (Subgroup.card_dvd_of_injective fK hfK))
  have hrankL : ∀ q : ℕ, q.Prime → 3 < q → CFSG.pRank q L ≤ 2 := by
    intro q hq hq3
    have h1 := pRank_le_localRank_of_le_normalizer hq hT'ne hT'2 hLH
    have h2 := hloc q hq hq3
    omega
  have hQ2 : IsPGroup 2 πL.ker := (pCore_isPGroup (p := 2) (G := L)).to_le
    (ker_le_pCore_two_of_pRank_le_two πL hπL hKL h3L hrankL)
  by_cases hQbot : πL.ker = ⊥
  · obtain ⟨ι, hι⟩ := exists_injective_lift πL hπL (by rw [hQbot, Subgroup.card_bot]; norm_num)
      card_e8 ιJ hιJ
    exact he8 e8_sq card_e8 (L.subtype.comp ι) (Subtype.val_injective.comp hι)
  set Z₀ := omegaOneCenter πL.ker with hZ₀
  have : Z₀.Normal := omegaOneCenter_normal πL.ker
  have hZ₀ne : Z₀ ≠ ⊥ := omegaOneCenter_ne_bot hQ2 hQbot
  have hZ₀sq : ∀ x : Z₀, x ^ 2 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, (mem_omegaOneCenter.mp x.2).2.2, Subgroup.coe_one])
  have hZ₀comm : ∀ x y : Z₀, x * y = y * x := fun x y => Subtype.ext
    ((mem_omegaOneCenter.mp x.2).2.1 _ (mem_omegaOneCenter.mp y.2).1)
  have hZ₀p : IsPGroup 2 Z₀ := fun x => ⟨1, by rw [pow_one]; exact hZ₀sq x⟩
  obtain ⟨k, hk⟩ := hZ₀p.exists_card_eq
  by_cases hk3 : 3 ≤ k
  ·
    obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 3)
      (by rw [hk]; exact pow_dvd_pow 2 hk3)
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := E)
      (fun a b => Subtype.ext (hZ₀comm a b)) (fun a => Subtype.ext (hZ₀sq a)) hE
    exact he8 fin_three_sq card_fin_three
      ((L.subtype.comp Z₀.subtype).comp (E.subtype.comp e.symm.toMonoidHom))
      ((Subtype.val_injective.comp Subtype.val_injective).comp
        (Subtype.val_injective.comp e.symm.injective))
  have hk2 : k ≤ 2 := by omega
  have : IsElementaryAbelian 2 Z₀ :=
    { toIsMulCommutative := ⟨⟨hZ₀comm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hZ₀sq }
  have : Finite (Additive Z₀) := inferInstanceAs (Finite Z₀)
  have : FiniteDimensional (ZMod 2) (Additive Z₀) := Module.Finite.of_finite
  let E₀ : MulAut Z₀ →* Module.End (ZMod 2) (Additive Z₀) :=
    { toFun := fun σ => (MonoidHom.toAdditive σ.toMonoidHom).toZModLinearMap 2
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hdim : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Additive Z₀)) ≤ 4 := by
    rw [finrank_top]
    have : Fintype (Additive Z₀) := Fintype.ofFinite _
    have hpow := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive Z₀)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hpow
    have h1 : 2 ^ Module.finrank (ZMod 2) (Additive Z₀) ≤ 2 ^ 2 := by
      rw [← hpow]
      change Nat.card Z₀ ≤ 2 ^ 2
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) hk2
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have htriv := forall_apply_eq_of_finrank_le_four hJ πL hπL hKL
    (E₀.comp (MulAut.conjNormal : L →* MulAut Z₀)) ⊤ (fun _ _ _ => trivial) hdim
  have hcentral : ∀ g : L, ∀ x : Z₀, g * (x : L) * g⁻¹ = x := by
    intro g x
    have h := congrArg Additive.toMul (htriv g (Additive.ofMul x) trivial)
    have h' : MulAut.conjNormal g x = x := h
    rw [← MulAut.conjNormal_apply, h']
  obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ₀ne
  have hz1 : ((z : L) : Y) ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hz2 : ((z : L) : Y) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, hZ₀sq z]
    rfl
  have hzc : ∀ g ∈ L, g * ((z : L) : Y) = ((z : L) : Y) * g := by
    intro g hg
    have h := congrArg Subtype.val (hcentral ⟨g, hg⟩ z)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    calc g * ((z : L) : Y) = g * ((z : L) : Y) * g⁻¹ * g := by group
      _ = ((z : L) : Y) * g := by rw [h]
  by_cases hs : ∃ s : L, s ^ 2 = 1 ∧ s ≠ 1 ∧ s ≠ (z : L)
  · obtain ⟨s, hs2, hs1, hsz⟩ := hs
    exact false_of_central_involution π hp2 ρ hker hfix L hπL hKL s.2 hzc hz2 hz1
      (by rw [← Subgroup.coe_pow, hs2]; rfl) (fun h => hs1 (Subtype.ext h))
      (fun h => hsz (Subtype.ext h))
  · refine false_of_unique_involution πL hπL hQ2 e8_sq card_e8 ιJ hιJ (z := (z : L))
      fun s hs2 hs1 => ?_
    by_contra hsz
    exact hs ⟨s, hs2, hs1, hsz⟩

end CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
