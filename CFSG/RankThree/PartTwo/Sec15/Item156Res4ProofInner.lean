module

public import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofModel
public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.Sec12.Item125Basic
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofA6
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof156Res4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank Subgroup
open CFSG.RankThree.Native.ONTriple

theorem fix_center_of_pow_three {Q : Type*} [Group Q] [Finite Q] (hZ3 : Nat.card (center Q) = 3)
    {σ : MulAut Q} (hσ : σ ^ 3 = 1) : ∀ z ∈ center Q, σ z = z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZexp : ∀ z ∈ center Q, z ^ 3 = 1 := by
    intro z hz
    have h := pow_card_eq_one' (G := center Q) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  have hσZ : ∀ z ∈ center Q, σ z ∈ center Q := by
    intro z hz
    rw [mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := σ.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz g']
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hzZ : zpowers z = center Q := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hz)
    rw [hZ3, Nat.card_zpowers, orderOf_eq_prime (hZexp z hz) hz1]
  have hσz : σ z ∈ zpowers z := hzZ ▸ hσZ z hz
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hσz
  have hz3 : z ^ 3 = 1 := hZexp z hz
  have hord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  rw [← zpow_mod_orderOf, hord, Nat.cast_ofNat] at hk
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k % 3 = m := ⟨(k % 3).toNat, (Int.toNat_of_nonneg h0).symm⟩
  rw [hm, zpow_natCast] at hk
  have hm3 : m < 3 := by omega
  have hσ3z : (σ ^ 3) z = z := by rw [hσ, MulAut.one_apply]
  interval_cases m
  ·
    exfalso
    rw [pow_zero] at hk
    exact hz1 (σ.injective (by rw [← hk, map_one]))
  · rw [pow_one] at hk
    exact hk.symm
  ·
    exfalso
    have h2 : σ (z ^ 2) = z ^ 4 := by
      rw [map_pow, ← hk, ← pow_mul]
    have e3 : (σ ^ 3) z = z ^ 8 := by
      rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, ← hk, h2, map_pow,
        ← hk, ← pow_mul]
    rw [hσ3z] at e3
    have : z ^ 8 = z ^ 2 := by
      rw [show (8 : ℕ) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hz3, one_pow, one_mul]
    rw [this] at e3
    apply hz1
    have : z * z = z * 1 := by
      calc z * z = z ^ 2 := (sq z).symm
        _ = z := e3.symm
        _ = z * 1 := (mul_one z).symm
    exact mul_left_cancel this

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_invariant_sylowOf' [Finite G] {p : ℕ} [Fact p.Prime] {J E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (J : Set G)) (hEp : IsPGroup p E) :
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P J ∧
      E ≤ Subgroup.normalizer (P : Set G) := by
  classical
  set W : Subgroup G := J ⊔ E with hW
  have hJW : J ≤ W := le_sup_left
  have hEW : E ≤ W := le_sup_right
  have hWN : W ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hEN
  have hE' : IsPGroup p (E.subgroupOf W) := hEp.comap_subtype
  obtain ⟨Q, hQ⟩ := hE'.exists_le_sylow
  set S : Subgroup G := (Q : Subgroup W).map W.subtype with hS
  have hSW : CFSG.ABGLocalTools.IsSylowOf p S W := ⟨Q, rfl⟩
  have hES : E ≤ S := by
    intro e he
    exact ⟨⟨e, hEW he⟩, hQ (Subgroup.mem_subgroupOf.mpr he), rfl⟩
  refine ⟨S ⊓ J, hSW.inf_of_le_normalizer hJW hWN, ?_⟩
  intro e he
  have h1 : e ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer (hES he)
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, hEN he⟩

omit [Finite G] in
@[expose] noncomputable def conjQuot (Y : Subgroup G) (a : Subgroup.normalizer (Y : Set G)) :
    MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  mulAutQuotientHom (CFSG.pCore 2 ↥Y) (Y.normalizerMonoidHom a)

omit [Finite G] in
theorem conjQuot_mul (Y : Subgroup G) (a b : Subgroup.normalizer (Y : Set G)) :
    conjQuot Y (a * b) = conjQuot Y a * conjQuot Y b := by
  rw [conjQuot, conjQuot, conjQuot, map_mul, map_mul]

omit [Finite G] in
theorem mem_pCoreOf_iff_mk_eq_one {Y : Subgroup G} (y : ↥Y) :
    (y : G) ∈ CFSG.Open.pCoreOf 2 Y ↔ (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) = 1 := by
  rw [QuotientGroup.eq_one_iff, CFSG.Open.pCoreOf]
  constructor
  · rintro ⟨v, hv, hvu⟩
    rwa [← Subtype.ext hvu]
  · intro hu
    exact ⟨y, hu, rfl⟩

theorem factorization_two_pow_mul_27 (m : ℕ) : (2 ^ m * 27).factorization 3 = 3 := by
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) (by norm_num), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2), smul_zero, zero_add,
    show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
    Finsupp.single_eq_same]

theorem le_of_isTripleCover_on
    {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hO : CFSG.Open.pCoreOf 2 Y ≠ ⊥) (hperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hON : Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON) :
    A ≤ Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ⟩ := ON134.nonempty_equiv_model hperf hON
  have hFE : partTwoF G = partTwoE G :=
    (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.toSec13Data.partTwoS_eq).1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.toSec13Data.isElemAbelian
  set P := CFSG.pCore 2 ↥Y with hP
  set π := QuotientGroup.mk' P with hπ
  set O := CFSG.Open.pCoreOf 2 Y with hOdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y
  have hOY : O ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hYO : Y ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hZ3 := hON.1
  intro a haA
  by_contra haY
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  have ha1 : a ≠ 1 := fun h1 => haY (h1 ▸ one_mem _)
  set aN : Subgroup.normalizer (Y : Set G) := ⟨a, hAY haA⟩ with haN
  set τ := conjQuot Y aN with hτ
  have hτ3 : τ ^ 3 = 1 := by
    rw [hτ, pow_succ, pow_succ, pow_one, ← conjQuot_mul, ← conjQuot_mul]
    have e : aN * aN * aN = 1 := Subtype.ext (by
      show a * a * a = 1
      rw [← pow_three', ha3])
    rw [e, conjQuot, map_one, map_one]
  obtain ⟨k, hk⟩ := ON134.aut_inner ψ τ (fix_center_of_pow_three hZ3 hτ3)
  have hk3 : k ^ 3 = 1 := by
    have hkZ : k ^ 3 ∈ center (↥Y ⧸ P) := by
      rw [mem_center_iff]
      intro q
      have h1 := ON134.pow_apply_of_conj hk 3 q
      rw [hτ3, MulAut.one_apply] at h1
      calc q * k ^ 3 = k ^ 3 * q * (k ^ 3)⁻¹ * k ^ 3 := by rw [← h1]
        _ = k ^ 3 * q := by group
    have h1 := pow_card_eq_one' (G := center (↥Y ⧸ P)) (x := ⟨k ^ 3, hkZ⟩)
    rw [hZ3] at h1
    have h2 : (k ^ 3) ^ 3 = 1 := congrArg Subtype.val h1
    refine ON134.pow_three_eq_one ψ (k := 2) ?_
    rw [show (3 : ℕ) ^ 2 = 3 * 3 by norm_num, pow_mul, h2]
  obtain ⟨F, hFe, hF27, hFk⟩ := exists_E27_le_centralizer ψ hZ3 hk3
  set E : Subgroup G := (F.comap π).map Y.subtype with hE
  have hEY : E ≤ Y := Subgroup.map_subtype_le _
  have hτF : ∀ y : ↥Y, π y ∈ F → τ (π y) = π y := by
    intro y hy
    rw [hk, show k * π y = π y * k from (mem_centralizer_singleton_iff.mp (hFk hy)).symm,
      mul_inv_cancel_right]
  have hconj : ∀ y : ↥Y, π (Y.normalizerMonoidHom aN y) = τ (π y) := fun y => rfl
  have hcomm : ∀ e ∈ E, a * e * a⁻¹ * e⁻¹ ∈ O ∧ a * e * a⁻¹ ∈ E := by
    rintro _ ⟨y, hy, rfl⟩
    have hyF : π y ∈ F := hy
    have h1 : π (Y.normalizerMonoidHom aN y) = π y := by rw [hconj, hτF y hyF]
    have hcoe : ((Y.normalizerMonoidHom aN y : ↥Y) : G) = a * y * a⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe Y aN y
    refine ⟨?_, ⟨Y.normalizerMonoidHom aN y, ?_, hcoe⟩⟩
    · have h2 : ((Y.normalizerMonoidHom aN y * y⁻¹ : ↥Y) : G) ∈ O := by
        rw [mem_pCoreOf_iff_mk_eq_one, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have h1' : ((Y.normalizerMonoidHom aN y : ↥Y) : ↥Y ⧸ P) = (y : ↥Y ⧸ P) := h1
        rw [h1', mul_inv_cancel]
      rwa [Subgroup.coe_mul, hcoe, Subgroup.coe_inv] at h2
    · show π (Y.normalizerMonoidHom aN y) ∈ F
      rw [h1]
      exact hyF
  have haN : a ∈ Subgroup.normalizer (E : Set G) :=
    Proof156Res4.mem_normalizer_of_conj_le ha3 fun e he => (hcomm e he).2
  have hap : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ha3 ha1)
  obtain ⟨F₀, hF₀, hF₀N⟩ :=
    exists_invariant_sylowOf' (zpowers_le.mpr haN) hap
  have hF₀E : F₀ ≤ E := hF₀.le
  have hEcard : Nat.card E = Nat.card P * 27 := by
    rw [hE, Subgroup.card_map_of_injective Y.subtype_injective]
    have h1 := QuotientGroup.card_preimage_mk P (F : Set (↥Y ⧸ P))
    rw [SetLike.coe_sort_coe, hF27] at h1
    exact h1
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 P)
  have hF₀27 : Nat.card F₀ = 27 := by
    rw [hF₀.card_eq, hEcard, hm, factorization_two_pow_mul_27]
    norm_num
  have hF₀3 : IsPGroup 3 F₀ := hF₀.isPGroup
  have hdisj : F₀ ⊓ O = ⊥ := by
    have hd : Disjoint F₀ O := Subgroup.disjoint_of_coprime_natCard (by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
      rw [hF₀27, hn]
      exact Nat.Coprime.pow_right _ (by norm_num))
    exact hd.eq_bot
  have hmemO : ∀ x ∈ F₀, x ∈ O → x = 1 := fun x hx hxO => by
    have : x ∈ F₀ ⊓ O := ⟨hx, hxO⟩
    rwa [hdisj, Subgroup.mem_bot] at this
  have haC : a ∈ centralizer (F₀ : Set G) := by
    rw [mem_centralizer_iff]
    intro f hf
    have h1 : a * f * a⁻¹ ∈ F₀ := (mem_normalizer_iff.mp (hF₀N (mem_zpowers a)) f).mp hf
    have h2 := (hcomm f (hF₀E hf)).1
    have h3 : a * f * a⁻¹ * f⁻¹ = 1 := hmemO _ (mul_mem h1 (inv_mem hf)) h2
    calc f * a = a * f * a⁻¹ * f⁻¹ * (f * a) := by rw [h3, one_mul]
      _ = a * f := by group
  have hπE : ∀ e ∈ E, ∃ y : ↥Y, (y : G) = e ∧ π y ∈ F := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, rfl, hy⟩
  have hF₀c : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl, hx'⟩ := hπE x (hF₀E hx)
    obtain ⟨y', rfl, hy'⟩ := hπE y (hF₀E hy)
    have hO' : ((x' * y' * x'⁻¹ * y'⁻¹ : ↥Y) : G) ∈ O := by
      rw [mem_pCoreOf_iff_mk_eq_one, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv]
      have hc : (x' : ↥Y ⧸ P) * (y' : ↥Y ⧸ P) = (y' : ↥Y ⧸ P) * (x' : ↥Y ⧸ P) :=
        congrArg Subtype.val (hFe.1.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
      rw [hc, mul_inv_cancel_right, mul_inv_cancel]
    have h1 := hmemO _ (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        Subgroup.coe_inv]
      exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)) hO'
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv] at h1
    calc (x' : G) * y' = (x' : G) * y' * (x' : G)⁻¹ * (y' : G)⁻¹ * (y' * x') := by group
      _ = y' * x' := by rw [h1, one_mul]
  have hF₀e : ∀ x ∈ F₀, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x', rfl, hx'⟩ := hπE x (hF₀E hx)
    refine hmemO _ (pow_mem hx 3) ?_
    rw [← Subgroup.coe_pow, mem_pCoreOf_iff_mk_eq_one, QuotientGroup.mk_pow]
    exact hFe.2 _ hx'
  have hF₀ab : CFSG.Assembly.IsElemAbelian 3 F₀ :=
    ⟨⟨⟨fun x y => Subtype.ext (hF₀c x x.2 y y.2)⟩⟩, hF₀e⟩
  have haF₀ : a ∉ F₀ := fun h1 => haY (hEY (hF₀E h1))
  exact CFSG.RankThree.PartTwo.Sec12.false_of_le_E81 hFE hF₀ab hF₀27 hO hO2
    ((hF₀E.trans hEY).trans hYO) haC (orderOf_eq_prime ha3 ha1) haF₀

end CFSG.RankThree.PartTwo.Sec15.Proof156Res4
