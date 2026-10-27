module

public import CFSG.RankThree.PartTwo.Sec21.Item21Statements
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
import CFSG.RankThree.PartTwo.Sec4.LThreePiAct
import CFSG.RankThree.PartTwo.Sec21.Item22L2

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G]

theorem exists_orderOf_eq_mem_centralizer [Finite G] {p : ℕ} [Fact p.Prime] {A K : Subgroup G}
    (hA : IsPGroup p A) (hAK : ∀ a ∈ A, ∀ x ∈ K, a * x * a⁻¹ ∈ K) (hp : p ∣ Nat.card K) :
    ∃ y ∈ K, orderOf y = p ∧ y ∈ Subgroup.centralizer (A : Set G) := by
  let _ : MulAction A K :=
    { smul := fun a x => ⟨(a : G) * x * (a : G)⁻¹, hAK a a.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : A) : G) * x * ((1 : A) : G)⁻¹ = x
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        change ((a * b : A) : G) * x * ((a * b : A) : G)⁻¹ =
          (a : G) * ((b : G) * x * (b : G)⁻¹) * (a : G)⁻¹
        simp [mul_assoc]) }
  set C : Subgroup K := (Subgroup.centralizer (A : Set G)).subgroupOf K
  have hset : MulAction.fixedPoints A K = (C : Set K) := by
    ext x
    rw [MulAction.mem_fixedPoints, SetLike.mem_coe, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro h a ha
      have h' : a * x * a⁻¹ = x := congrArg Subtype.val (h ⟨a, ha⟩)
      calc a * x = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h']
    · intro h a
      apply Subtype.ext
      change (a : G) * x * (a : G)⁻¹ = x
      rw [h a a.2, mul_inv_cancel_right]
  have hmod := hA.card_modEq_card_fixedPoints K
  have hpC : p ∣ Nat.card C := by
    have h := (hmod.dvd_iff dvd_rfl).mp hp
    rw [hset] at h
    exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpC
  refine ⟨((x : K) : G), (x : K).2, ?_, Subgroup.mem_subgroupOf.mp x.2⟩
  rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]

@[expose] def KOfWellDefinedAll : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → KOfWellDefined A

theorem kOf_le_kZero {A : Subgroup G} (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) : kOf A φ ≤ kZero A φ := by
  by_cases hU : StatedClassicalModel (kZero A φ) .PSU 3 2 2
  · obtain ⟨K, hKp, -⟩ := hK φ hφ hU
    exact (kOf_spec hU ⟨K, hKp⟩).1
  · rw [kOf_eq_kZero hU]

theorem kZero_le_centralizer (A : Subgroup G) (φ : MulAut A) :
    kZero A φ ≤ Subgroup.centralizer (fixedInG A φ : Set G) :=
  (Subgroup.map_subtype_le _).trans (Subgroup.map_subtype_le _)

theorem conj_mem_kOf [Finite G] {A : Subgroup G} (hK : KOfWellDefined A)
    (w : Subgroup.normalizer (A : Set G)) {φ : MulAut A} (hφ : φ ∈ dStar A)
    (hw : wConj A w * φ = φ * wConj A w) {x : G} (hx : x ∈ kOf A φ) :
    (w : G) * x * (w : G)⁻¹ ∈ kOf A φ := by
  have h := kOf_conj_of_unique hK w hφ
  rw [hw, mul_inv_cancel_right] at h
  rw [h]
  exact ⟨x, hx, rfl⟩

theorem exists_mulEquiv_projSL_of_case222 {A L K : Subgroup G} (h : Case222 A L K) :
    ∃ n : ℕ, Nonempty (K ≃* projSL 2 (GaloisField 2 n)) := by
  rcases h with ⟨-, n, -, -, -, he, -⟩ | ⟨-, n, -, -, -, he, -⟩ | ⟨-, n, -, -, -, he | he, -⟩ |
    ⟨-, -, he | he, -⟩ | ⟨-, n, -, -, -, he, -⟩
  · exact ⟨n, he⟩
  · exact ⟨n, he⟩
  · exact ⟨n, he⟩
  · exact ⟨2 * n, he⟩
  · exact ⟨2, he⟩
  · exact ⟨4, he⟩
  · exact ⟨n, he⟩

theorem exists_commOf_eq_zpowers_mem_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    (∃ n : ℕ, Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 n))) ∧
      ∃ z : A, commOf φ = Subgroup.zpowers z ∧ (z : G) ∈ kOf A φ ∧ orderOf (z : G) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAF := hpair.mem_S.1
  have hAe : IsElemAbelian 3 A := hAF.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hAp : IsPGroup 3 A := fun a => ⟨1, by simpa using hA3 a⟩
  have hAmax : Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A :=
    ⟨hAe, fun B hB hAB => (hAF.2.1 B hB hAB).le⟩
  obtain ⟨hrefl, X, hX, hφX⟩ := id hφ
  obtain ⟨-, E', hE', U', hU', c', hXpair⟩ := hX
  have hcase := (h222 G A E' U' c' X ⟨hpair.toSec21Std, hE', hU', hXpair⟩).2.2 φ hφX hφ
  obtain ⟨n, ⟨e⟩⟩ := exists_mulEquiv_projSL_of_case222 hcase
  refine ⟨⟨n, ⟨e⟩⟩, ?_⟩
  have hKC : ∀ x ∈ kOf A φ, ∀ b ∈ fixedInG A φ, b * x = x * b := fun x hx b hb =>
    Subgroup.mem_centralizer_iff.mp (kZero_le_centralizer A φ (kOf_le_kZero hK hφ hx)) b hb
  have hAK : ∀ a ∈ A, ∀ x ∈ kOf A φ, a * x * a⁻¹ ∈ kOf A φ := by
    intro a ha x hx
    have hw : wConj A ⟨a, Subgroup.le_normalizer ha⟩ = 1 := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [wConj_apply, MulAut.one_apply]
      have hab : a * (b : G) = b * a := congrArg Subtype.val (hAc ⟨a, ha⟩ b)
      change a * (b : G) * a⁻¹ = b
      rw [hab, mul_inv_cancel_right]
    exact conj_mem_kOf hK ⟨a, Subgroup.le_normalizer ha⟩ hφ (by rw [hw, one_mul, mul_one]) hx
  obtain ⟨y, hyK, hy3, hyC⟩ := exists_orderOf_eq_mem_centralizer hAp hAK
    (three_dvd_card_of_mulEquiv_projSL e)
  have hyA : y ∈ A := Sec4.mem_of_maximal_of_commute hAmax
    (by rw [← hy3]; exact pow_orderOf_eq_one y) fun a ha => Subgroup.mem_centralizer_iff.mp hyC a ha
  obtain ⟨t, -, ht⟩ := hφX
  change wConj A t = φ at ht
  set ya : A := ⟨y, hyA⟩
  set z : A := ya⁻¹ * φ ya with hzdef
  have hzK : (z : G) ∈ kOf A φ := by
    have h1 : (t : G) * y * (t : G)⁻¹ ∈ kOf A φ := conj_mem_kOf hK t hφ (by rw [ht]) hyK
    have h2 : ((φ ya : A) : G) = (t : G) * y * (t : G)⁻¹ := by rw [← ht, wConj_apply]; rfl
    change (ya : G)⁻¹ * ((φ ya : A) : G) ∈ kOf A φ
    rw [h2]
    exact (kOf A φ).mul_mem ((kOf A φ).inv_mem hyK) h1
  have hz1 : z ≠ 1 := by
    intro hz
    have hfix : φ ya = ya := by
      have h := congrArg (ya * ·) hz
      simp only [hzdef, mul_inv_cancel_left, mul_one] at h
      exact h
    have hyF : y ∈ fixedInG A φ := ⟨ya, hfix, rfl⟩
    have hy1 : (⟨y, hyK⟩ : kOf A φ) = 1 := eq_one_of_forall_commute_of_mulEquiv_projSL e
      fun x => Subtype.ext (hKC x x.2 y hyF).symm
    have hy1' : y = 1 := congrArg Subtype.val hy1
    rw [hy1', orderOf_one] at hy3
    norm_num at hy3
  have hz3 : orderOf (z : G) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hA3 z) hz1
  refine ⟨z, ?_, hzK, hz3⟩
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [Subgroup.zpowers_le]
    exact mem_commOf φ ya
  · rw [hrefl.2, Nat.card_zpowers, ← Subgroup.orderOf_coe, hz3]

theorem map_commOf_le_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) : (commOf φ).map A.subtype ≤ kOf A φ := by
  obtain ⟨-, z, hcomm, hzK, -⟩ := exists_commOf_eq_zpowers_mem_kOf h222 hpair hK hφ
  rw [hcomm, MonoidHom.map_zpowers, Subgroup.zpowers_le]
  exact hzK

theorem exists_involution_kOf_wConj_eq [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) :
    ∃ j : Subgroup.normalizer (A : Set G), (j : G) ∈ kOf A φ ∧ orderOf (j : G) = 2 ∧
      wConj A j = φ := by
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  have hA3 : ∀ a : A, a ^ 3 = 1 := fun a => Subtype.ext (by simpa using hAe.2 a a.2)
  have hrefl := hφ.1
  obtain ⟨⟨n, ⟨e⟩⟩, z, hcomm, hzK, hz3⟩ := exists_commOf_eq_zpowers_mem_kOf h222 hpair hK hφ
  have hKC : ∀ x ∈ kOf A φ, ∀ b ∈ fixedInG A φ, b * x = x * b := fun x hx b hb =>
    Subgroup.mem_centralizer_iff.mp (kZero_le_centralizer A φ (kOf_le_kZero hK hφ hx)) b hb
  obtain ⟨jK, hjj, hjz⟩ := exists_inv_conj_of_mulEquiv_projSL e (z := ⟨z, hzK⟩)
    (by rw [Subgroup.orderOf_mk]; exact hz3)
  set jG : G := (jK : G)
  have hjj' : jG * jG = 1 := congrArg Subtype.val hjj
  have hjzG : jG * (z : G) * jG⁻¹ = (z : G)⁻¹ := congrArg Subtype.val hjz
  have hjw : ∀ w ∈ commOf φ, jG * (w : G) * jG⁻¹ = (w : G)⁻¹ := by
    intro w hw
    rw [hcomm] at hw
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h := map_zpow (MulAut.conj jG) (z : G) m
    simp only [MulAut.conj_apply, hjzG, inv_zpow] at h
    rw [Subgroup.coe_zpow]
    exact h
  have hφφ : ∀ a : A, φ (φ a) = a := by
    intro a
    have h2 : φ ^ 2 = 1 := by rw [← hrefl.1]; exact pow_orderOf_eq_one φ
    have h := congrArg (fun ψ : MulAut A => ψ a) h2
    simpa [pow_two, MulAut.mul_apply] using h
  have hconj : ∀ a : A, jG * (a : G) * jG⁻¹ = ((φ a : A) : G) := by
    intro a
    set b : A := a * φ a with hbdef
    set w : A := (φ a)⁻¹ * a with hwdef
    have hb : φ b = b := by
      rw [hbdef, map_mul, hφφ]
      exact hAc _ _
    have hwC : w ∈ commOf φ := by
      have h := (commOf φ).inv_mem (mem_commOf φ a)
      rwa [mul_inv_rev, inv_inv] at h
    have hφw : φ w = w⁻¹ := by
      rw [hwdef, map_mul, map_inv, hφφ, mul_inv_rev, inv_inv]
    have ha : a = (b * w) ^ 2 := by
      have hbw : b * w = a ^ 2 := by rw [hbdef, hwdef, sq, mul_assoc, mul_inv_cancel_left]
      rw [hbw, ← pow_mul]
      calc a = a ^ 3 * a := by rw [hA3, one_mul]
        _ = a ^ (2 * 2) := by rw [← pow_succ]
    have hφa : φ a = (b * w⁻¹) ^ 2 := by
      conv_lhs => rw [ha]
      rw [map_pow, map_mul, hb, hφw]
    have hjb : jG * (b : G) * jG⁻¹ = b := by
      rw [← hKC jG jK.2 b ⟨b, hb, rfl⟩, mul_inv_cancel_right]
    have key := map_pow (MulAut.conj jG) ((b : G) * (w : G)) 2
    simp only [map_mul, MulAut.conj_apply, hjb, hjw w hwC] at key
    calc jG * (a : G) * jG⁻¹ = jG * ((b : G) * (w : G)) ^ 2 * jG⁻¹ := by
          conv_lhs => rw [ha]
          push_cast
          rfl
      _ = ((b : G) * (w : G)⁻¹) ^ 2 := key
      _ = ((φ a : A) : G) := by
          rw [hφa]
          push_cast
          rfl
  have hjinv : jG⁻¹ = jG := inv_eq_of_mul_eq_one_right hjj'
  have hjN : jG ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hconj ⟨x, hx⟩]
      exact (φ ⟨x, hx⟩).2
    · intro hx
      have h := hconj ⟨_, hx⟩
      have hx' : jG * (jG * x * jG⁻¹) * jG⁻¹ = x := by
        rw [hjinv]
        calc jG * (jG * x * jG) * jG = (jG * jG) * x * (jG * jG) := by group
          _ = x := by rw [hjj', one_mul, mul_one]
      change jG * (jG * x * jG⁻¹) * jG⁻¹ = _ at h
      rw [hx'] at h
      rw [h]
      exact (φ _).2
  refine ⟨⟨jG, hjN⟩, jK.2, orderOf_eq_prime (by rw [sq]; exact hjj') fun h1 => ?_,
    MulEquiv.ext fun a => Subtype.ext ?_⟩
  · have h1' : jG = 1 := h1
    have hφ1 : φ = 1 := by
      refine MulEquiv.ext fun a => Subtype.ext ?_
      rw [← hconj a, h1', MulAut.one_apply]
      simp
    have h := hrefl.1
    rw [hφ1, orderOf_one] at h
    norm_num at h
  · rw [wConj_apply]
    exact hconj a

theorem mem_starOf_kOf [Finite G] (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ : MulAut A}
    (hφ : φ ∈ dStar A) : φ ∈ starOf A (kOf A φ) := by
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  exact ⟨j, Subgroup.mem_subgroupOf.mpr hjK, hj⟩

theorem closure_dStar_le_starOf_iGroup [Finite G] (h222 : Item222) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) :
    Subgroup.closure (dStar A) ≤ starOf A (iGroup A) :=
  (Subgroup.closure_le _).mpr fun _ hφ =>
    starOf_mono A (kOf_le_iGroup hφ) (mem_starOf_kOf h222 hpair hK hφ)

theorem le_iGroup [Finite G] (h2130 : Item2130) (h222 : Item222) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) : A ≤ iGroup A := by
  set R : Subgroup A := ⨆ φ ∈ dStar A, commOf φ
  have hle : ∀ ψ ∈ wStar A, R.map ψ.toMonoidHom ≤ R := by
    rintro ψ ⟨w, rfl⟩
    rw [Subgroup.map_iSup]
    refine iSup_le fun φ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hφ => ?_
    rw [← commOf_conj]
    exact le_iSup₂_of_le _ (conj_mem_dStar w hφ) le_rfl
  have hR : ∀ ψ ∈ wStar A, R.map ψ.toMonoidHom = R := fun ψ hψ =>
    Subgroup.eq_of_le_of_card_ge (hle ψ hψ)
      (le_of_eq (Subgroup.card_map_of_injective ψ.injective).symm)
  rcases h2130 G A E U c L hpair R hR with hbot | htop
  · exfalso
    obtain ⟨-, ⟨φ, -, hφ⟩, -⟩ := h222 G A E U c L hpair
    have hφR : commOf φ ≤ R := le_iSup₂_of_le φ hφ le_rfl
    rw [hbot, le_bot_iff] at hφR
    have h3 := hφ.1.2
    rw [hφR, Subgroup.card_bot] at h3
    norm_num at h3
  · have hRle : R ≤ (iGroup A).comap A.subtype := by
      refine iSup₂_le fun φ hφ => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact (map_commOf_le_kOf h222 hpair hK hφ).trans (kOf_le_iGroup hφ)
    intro a ha
    exact hRle (htop ▸ Subgroup.mem_top (⟨a, ha⟩ : A))

end CFSG.RankThree.PartTwo.Sec21
