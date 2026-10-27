module

public import CFSG.RankThree.PartTwo.Sec13.Notation
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Late.Transitivity
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1611Res2

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13

theorem conj_injective_of_center {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro q q' hqq'
  have hc : q⁻¹ * q' ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : q * w * q⁻¹ = q' * w * q'⁻¹ := by
      have := congrArg (fun σ : MulAut X => σ w) hqq'
      simpa only [MulAut.conj_apply] using this
    calc w * (q⁻¹ * q') = q⁻¹ * (q * w * q⁻¹) * q' := by group
      _ = q⁻¹ * (q' * w * q'⁻¹) * q' := by rw [h1]
      _ = q⁻¹ * q' * w := by group
  rw [hZ, Subgroup.mem_bot] at hc
  calc q = q * (q⁻¹ * q') := by rw [hc, mul_one]
    _ = q' := by group

theorem mul_conj_mul_inv {X : Type*} [Group X] (τ : MulAut X) (q : X) :
    τ * MulAut.conj q * τ⁻¹ = MulAut.conj (τ q) := by
  ext w
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]

theorem commute_of_conj_mem_zpowers {H : Type*} [Group H] {x y : H} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hxy : x * y * x⁻¹ ∈ Subgroup.zpowers y) : x * y = y * x := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxy
  have hy3 : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy
  have hk' : y ^ (k % 3) = x * y * x⁻¹ := by
    rw [← hk]
    conv_rhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, hy3, one_zpow, mul_one]
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  have key : x * y * x⁻¹ = y ∨ y = 1 := by
    obtain hm | hm | hm : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    · right
      rw [hm, zpow_zero] at hk'
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = 1 := by rw [← hk']; group
    · left
      rw [hm, zpow_one] at hk'
      exact hk'.symm
    · right
      rw [hm] at hk'
      have e2 : x * y * x⁻¹ = y ^ 2 := by rw [← hk']; norm_cast
      have e4 : x * y ^ 2 * x⁻¹ = y := by
        rw [← conj_pow, e2, ← pow_mul, show 2 * 2 = 1 + 3 from rfl, pow_add, hy, mul_one,
          pow_one]
      have e3 : x * (x * x) * y * (x * (x * x))⁻¹ = y ^ 2 := by
        calc x * (x * x) * y * (x * (x * x))⁻¹ = x * (x * (x * y * x⁻¹) * x⁻¹) * x⁻¹ := by
              group
          _ = y ^ 2 := by rw [e2, e4, e2]
      rw [← pow_three, hx, one_mul, inv_one, mul_one, pow_two] at e3
      calc y = y⁻¹ * (y * y) := by group
        _ = y⁻¹ * y := by rw [← e3]
        _ = 1 := inv_mul_cancel y
  rcases key with h | h
  · calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h]
  · rw [h, mul_one, one_mul]

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem thetaQuotMulAut_of_mem (l : ↥L) :
    Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨(l : G), Subgroup.le_normalizer l.2⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) l) := by
  ext q'
  induction q' using QuotientGroup.induction_on with
  | H x =>
    change ((L.normalizerMonoidHom ⟨(l : G), Subgroup.le_normalizer l.2⟩ x : ↥L) :
        ↥L ⧸ aschbacherSolvableCore 3 ↥L) =
      (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L) * (x : ↥L ⧸ aschbacherSolvableCore 3 ↥L) *
        (l : ↥L ⧸ aschbacherSolvableCore 3 ↥L)⁻¹
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl

theorem le_zpowers_sup_of_inner_aut (hD : Sec13Data G A c L)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hinner : ∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), σ ^ 3 = 1 →
      ∃ q, σ = MulAut.conj q) :
    A ≤ Subgroup.zpowers c ⊔ L := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut (↥L ⧸ θ) := (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom with hρ
  have hAN : A ≤ N := hD.le_normalizer
  have hconj := conj_injective_of_center hZ
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hCA : (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = Subgroup.zpowers c := by
    have hsc := hD.sectionCentralizer_eq
    rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
    exact SetLike.coe_injective hsc
  have hρL : ∀ l : ↥L, ρ ⟨l, Subgroup.le_normalizer l.2⟩ = MulAut.conj (π l) :=
    thetaQuotMulAut_of_mem
  have hmemC : ∀ (x : G) (hx : x ∈ N), ρ ⟨x, hx⟩ = 1 → x ∈ Sec4.thetaQuotCentralizer L :=
    fun x hx h1 => ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr h1, rfl⟩
  intro a ha
  have hρ3 : ρ ⟨a, hAN ha⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨a, hAN ha⟩ : N) ^ 3 = 1 := Subtype.ext (hD.isElemAbelian.2 a ha)
    rw [this, map_one]
  obtain ⟨q, hq⟩ := hinner _ hρ3
  have hq3 : q ^ 3 = 1 := hconj (by rw [map_pow, ← hq, hρ3, map_one])
  by_cases hq1 : q = 1
  · have haC : a ∈ A ⊓ Sec4.thetaQuotCentralizer L :=
      ⟨ha, hmemC a (hAN ha) (by rw [hq, hq1, map_one])⟩
    rw [hCA] at haC
    exact Subgroup.mem_sup_left haC
  have hfix : ∀ (b : G) (hb : b ∈ A), ρ ⟨b, hAN hb⟩ q = q := by
    intro b hb
    apply hconj
    rw [← mul_conj_mul_inv, ← hq, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change b * a * b⁻¹ = a
    rw [hD.commute hb ha, mul_inv_cancel_right]
  set U : Subgroup G := ((Subgroup.zpowers q).comap π).map L.subtype with hU
  have hUL : U ≤ L := Subgroup.map_subtype_le _
  have hmemU : ∀ (u : G) (hu : u ∈ L), u ∈ U ↔ π ⟨u, hu⟩ ∈ Subgroup.zpowers q := by
    intro u hu
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact hl
    · intro h'
      exact ⟨⟨u, hu⟩, h', rfl⟩
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype fun u hu => ?_
    obtain ⟨l, hl, rfl⟩ := hu
    have hbl : b * (l : G) * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hAN hb) l).mp l.2
    refine (hmemU _ hbl).mpr ?_
    have h1 : π ⟨b * (l : G) * b⁻¹, hbl⟩ = ρ ⟨b, hAN hb⟩ (π l) := rfl
    rw [h1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hl
    rw [← hk, map_zpow, hfix b hb]
    exact Subgroup.zpow_mem_zpowers q k
  have hqo : orderOf q = 3 := orderOf_eq_prime hq3 hq1
  have hUcard : Nat.card U = Nat.card θ * 3 := by
    rw [hU, Subgroup.card_map_of_injective L.subtype_injective]
    have h1 : Nat.card ((Subgroup.zpowers q).comap π) =
        Nat.card θ * Nat.card (Subgroup.zpowers q) :=
      QuotientGroup.card_preimage_mk θ (Subgroup.zpowers q : Set (↥L ⧸ θ))
    rw [h1, Nat.card_zpowers, hqo]
  set V := U ⊔ A with hV
  have hVN : V ≤ Subgroup.normalizer (U : Set G) := sup_le Subgroup.le_normalizer hAU
  have hA3 : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by simpa using hD.isElemAbelian.2 x x.2)⟩
  obtain ⟨Qs, hQs⟩ := (hA3.comap_subtype (K := V)).exists_le_sylow
  set T : Subgroup G := (Qs : Subgroup V).map V.subtype with hT
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T V := ⟨Qs, rfl⟩
  have hAT : A ≤ T := fun x hx =>
    ⟨⟨x, (le_sup_right : A ≤ V) hx⟩, hQs (show (⟨x, _⟩ : V) ∈ A.subgroupOf V from hx), rfl⟩
  have hTU := hTsyl.inf_of_le_normalizer (le_sup_left : U ≤ V) hVN
  have hTUcard : Nat.card (T ⊓ U : Subgroup G) = 3 := by
    rw [hTU.card_eq, hUcard]
    have hθ0 : Nat.card θ ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul hθ0 (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hθ3, Nat.Prime.factorization_self Nat.prime_three]
    norm_num
  obtain ⟨y, hyTU, hy1⟩ : ∃ y ∈ T ⊓ U, y ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : T ⊓ U = ⊥ := eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (hall y hy)
    rw [hbot, Subgroup.card_bot] at hTUcard
    omega
  have hy3 : y ^ 3 = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(T ⊓ U)) (x := ⟨y, hyTU⟩)
    rw [hTUcard] at h1
    exact congrArg Subtype.val h1
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hTUz : T ⊓ U = Subgroup.zpowers y := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyTU) ?_
    rw [hTUcard, Nat.card_zpowers, hyo]
  have hATU : A ≤ Subgroup.normalizer ((T ⊓ U : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hAT.trans Subgroup.le_normalizer) hAU
  have hyA : y ∈ A := by
    refine Sec15.mem_of_mem_partTwoF hD.mem_partTwoF hy3 fun b hb => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : b * y * b⁻¹ ∈ T ⊓ U := (Subgroup.mem_normalizer_iff.mp (hATU hb) y).mp hyTU
    rw [hTUz] at h1
    exact commute_of_conj_mem_zpowers (hD.isElemAbelian.2 b hb) hy3 h1
  have hyL : y ∈ L := hUL hyTU.2
  have hπy : π ⟨y, hyL⟩ ∈ Subgroup.zpowers q := (hmemU y hyL).mp hyTU.2
  have hπy1 : π ⟨y, hyL⟩ ≠ 1 := by
    intro h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.orderOf_dvd_natCard θ h1
    rw [Subgroup.orderOf_mk, hyo] at h2
    exact hθ3 h2
  have hπy3 : π ⟨y, hyL⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyL⟩ : ↥L) ^ 3 = 1 := Subtype.ext hy3
    rw [this, map_one]
  have hqy : q ∈ Subgroup.zpowers (π ⟨y, hyL⟩) := by
    have hle : Subgroup.zpowers (π ⟨y, hyL⟩) ≤ Subgroup.zpowers q :=
      Subgroup.zpowers_le.mpr hπy
    have heq : Subgroup.zpowers (π ⟨y, hyL⟩) = Subgroup.zpowers q :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, hqo, orderOf_eq_prime hπy3 hπy1])
    rw [heq]
    exact Subgroup.mem_zpowers q
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hqy
  have hyjL : y ^ j ∈ L := zpow_mem hyL j
  have hρy : ρ ⟨y ^ j, Subgroup.le_normalizer hyjL⟩ = ρ ⟨a, hAN ha⟩ := by
    rw [hq, hρL ⟨y ^ j, hyjL⟩, ← hj, ← map_zpow]
    rfl
  have hrN : (y ^ j)⁻¹ * a ∈ N := mul_mem (inv_mem (Subgroup.le_normalizer hyjL)) (hAN ha)
  have hrC : (y ^ j)⁻¹ * a ∈ Sec4.thetaQuotCentralizer L := by
    refine hmemC _ hrN ?_
    have e : (⟨(y ^ j)⁻¹ * a, hrN⟩ : N) =
        (⟨y ^ j, Subgroup.le_normalizer hyjL⟩ : N)⁻¹ * ⟨a, hAN ha⟩ := rfl
    rw [e, map_mul, map_inv, hρy, inv_mul_cancel]
  have hrA : (y ^ j)⁻¹ * a ∈ A := mul_mem (inv_mem (zpow_mem hyA j)) ha
  have hrc : (y ^ j)⁻¹ * a ∈ Subgroup.zpowers c := by
    rw [← hCA]
    exact ⟨hrA, hrC⟩
  have e : a = y ^ j * ((y ^ j)⁻¹ * a) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_right hyjL) (Subgroup.mem_sup_left hrc)

theorem point_facts_of_inner_aut (hD : Sec13Data G A c L)
    (hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥)
    (hinner : ∀ σ : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), σ ^ 3 = 1 →
      ∃ q, σ = MulAut.conj q) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
  have hcL : c ∉ L := not_mem_of_center_eq_bot hD hZ
  have hAL := le_zpowers_sup_of_inner_aut hD hZ hinner
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hD.mem_A
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) := hcA.trans hD.le_normalizer
  have hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L) := by
    refine le_antisymm (fun a ha => ?_) (sup_le hcA inf_le_left)
    have haL : a ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hAL ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at haL
    obtain ⟨z, hz, l, hl, rfl⟩ := Set.mem_mul.mp haL
    have hlA : l ∈ A := by
      have hl' : l = z⁻¹ * (z * l) := by group
      rw [hl']
      exact mul_mem (inv_mem (hcA hz)) ha
    exact Subgroup.mul_mem_sup hz ⟨hlA, hl⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ A ⊓ L, x * y = y * x := fun x hx y hy =>
    hD.commute (hcA hx) hy.1
  have hdisj : Subgroup.zpowers c ⊓ (A ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hD.orderOf_eq hcL]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  rw [← hAc, hdisj, Subgroup.card_bot, mul_one, hD.card_eq, Nat.card_zpowers,
    hD.orderOf_eq] at hcard
  exact ⟨hcL, by omega, hAc⟩

theorem autThetaQuot_eq_map_conj (hD : Sec13Data G A c L)
    (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L)) :
    Sec4.autThetaQuot A L =
      (((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
        (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _) := by
  set N := Subgroup.normalizer (L : Set G) with hN
  set ρ : N →* MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom with hρ
  have hCA : (A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = Subgroup.zpowers c := by
    have hsc := hD.sectionCentralizer_eq
    rw [sectionCentralizer_eq_inf hD.le_normalizer] at hsc
    exact SetLike.coe_injective hsc
  have hρz : ∀ (z : G) (hz : z ∈ Subgroup.zpowers c) (hzN : z ∈ N), ρ ⟨z, hzN⟩ = 1 := by
    intro z hz hzN
    rw [← hCA] at hz
    obtain ⟨n, hn, hnz⟩ := hz.2
    have hn' : n = ⟨z, hzN⟩ := Subtype.ext hnz
    rw [← hn']
    exact MonoidHom.mem_ker.mp hn
  have hcA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hD.mem_A
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
    Late.le_normalizer_inf (hcA.trans (fun a ha => Subgroup.mem_normalizer_fintype fun b hb => by
      rw [hD.commute ha hb, mul_inv_cancel_right]
      exact hb)) (hcA.trans hD.le_normalizer)
  ext τ
  rw [Sec4.mem_autThetaQuot_iff]
  constructor
  · rintro ⟨a, haN, haA, rfl⟩
    have haA' : a ∈ ((Subgroup.zpowers c ⊔ (A ⊓ L) : Subgroup G) : Set G) := by
      rw [← hAc]
      exact haA
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at haA'
    obtain ⟨z, hz, b, hb, rfl⟩ := Set.mem_mul.mp haA'
    have hzN : z ∈ N := hD.le_normalizer (hcA hz)
    have hbN : b ∈ N := Subgroup.le_normalizer hb.2
    refine ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, hb.2⟩,
      ⟨⟨b, hb.2⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩, ?_⟩
    have e : (⟨z * b, haN⟩ : N) = ⟨z, hzN⟩ * ⟨b, hbN⟩ := rfl
    change MulAut.conj _ = ρ ⟨z * b, haN⟩
    rw [e, map_mul, hρz z hz hzN, one_mul]
    exact (thetaQuotMulAut_of_mem ⟨b, hb.2⟩).symm
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨(b : G), Subgroup.le_normalizer b.2, (Subgroup.mem_subgroupOf.mp hb).1,
      thetaQuotMulAut_of_mem b⟩

theorem range_conj_le_autThetaQuot (hD : Sec13Data G A c L) :
    (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range ≤
      Sec4.autThetaQuot (Subgroup.normalizer (Subgroup.zpowers c : Set G)) L := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Sec4.mem_autThetaQuot_iff]
  refine ⟨(l : G), Subgroup.le_normalizer l.2, ?_, thetaQuotMulAut_of_mem l⟩
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hlc : Commute (l : G) c := Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer l.2)
  rw [(hlc.zpow_right k).eq, mul_inv_cancel_right]
  exact Subgroup.zpow_mem_zpowers c k

theorem false_of_alpha_eq_bot (hD : Sec13Data G A c L) (hAc : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hα : ∀ Y : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
      (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _).range ≤ Y →
        thetaAlpha 3 (((((A ⊓ L).subgroupOf L).map
          (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).map
            (MulAut.conj : (↥L ⧸ aschbacherSolvableCore 3 ↥L) →* MulAut _)).subgroupOf Y) = ⊥) :
    False := by
  have h1 := hα _ (range_conj_le_autThetaQuot hD)
  rw [← autThetaQuot_eq_map_conj hD hAc] at h1
  exact (mem_lA_iff.mp hD.mem_lA).2.2.2 h1

end CFSG.RankThree.PartTwo.Sec16.Proof1611Res2
