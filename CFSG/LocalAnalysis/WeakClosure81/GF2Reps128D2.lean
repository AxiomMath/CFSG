module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128D1
import CFSG.Walter.SimpleCaseStronglyEmbedded
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki
import CFSG.Timmesfeld.RankOne.SL2
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup
open scoped Matrix MatrixGroups

section OrderTwoOrOdd

variable {X : Type} [Group X]

private theorem w4s_sq_eq_one_of_mem_sylow (hord : ∀ x : X, orderOf x ∣ 2 ∨ Odd (orderOf x))
    (T : Sylow 2 X) {x : X} (hx : x ∈ (T : Subgroup X)) : x ^ 2 = 1 := by
  rcases hord x with h | h
  · exact orderOf_dvd_iff_pow_eq_one.mp h
  · obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp T.isPGroup' ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hk
    cases k with
    | zero =>
      rw [pow_zero, orderOf_eq_one_iff] at hk
      rw [hk, one_pow]
    | succ k =>
      rw [hk, pow_succ] at h
      exact absurd h (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr (dvd_mul_left 2 _)))

private theorem w4s_comm_of_sq {H : Subgroup X} (h : ∀ x ∈ H, x ^ 2 = 1) {x y : X} (hx : x ∈ H)
    (hy : y ∈ H) : x * y = y * x := by
  have hinv : ∀ z ∈ H, z⁻¹ = z := fun z hz =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact h z hz)
  calc x * y = (x * y)⁻¹ := (hinv _ (H.mul_mem hx hy)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv y hy, hinv x hx]

private theorem w4s_mem_of_mem_normalizer (T : Sylow 2 X) {m : X}
    (hm : m ∈ Subgroup.normalizer (T : Set X)) (hm2 : m ^ 2 = 1) : m ∈ (T : Subgroup X) := by
  have hP : IsPGroup 2 (Subgroup.zpowers m) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hm2) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have heq := T.is_maximal' (IsPGroup.to_sup_of_normal_right' hP T.isPGroup'
    (Subgroup.zpowers_le.mpr hm)) le_sup_right
  rw [← heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers m)

variable [Finite X]

private theorem w4s_two_dvd_card [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) :
    2 ∣ Nat.card X := by
  by_contra hodd
  have hsolv : Group.IsSolvable X :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv a b)

private theorem w4s_comm_iff_mem (hord : ∀ x : X, orderOf x ∣ 2 ∨ Odd (orderOf x))
    (T : Sylow 2 X) {s : X} (hsT : s ∈ (T : Subgroup X)) (hs1 : s ≠ 1) (y : X) :
    y * s = s * y ↔ y ∈ (T : Subgroup X) := by
  have hos : orderOf s = 2 := orderOf_eq_prime (w4s_sq_eq_one_of_mem_sylow hord T hsT) hs1
  have hC : ∀ c ∈ Subgroup.centralizer {s}, c ^ 2 = 1 := by
    intro c hc
    have hcs : Commute s c := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
    rcases hord c with h | h
    · exact orderOf_dvd_iff_pow_eq_one.mp h
    · have hco : (orderOf s).Coprime (orderOf c) := by
        rw [hos]
        exact Nat.coprime_two_left.mpr h
      have hsc : orderOf (s * c) = 2 * orderOf c := by
        rw [hcs.orderOf_mul_eq_mul_orderOf_of_coprime hco, hos]
      rcases hord (s * c) with h' | h'
      · rw [hsc] at h'
        have h1 : orderOf c = 1 := by
          have hle := Nat.le_of_dvd (by norm_num) h'
          have hpos := orderOf_pos c
          omega
        rw [orderOf_eq_one_iff] at h1
        rw [h1, one_pow]
      · rw [hsc] at h'
        exact absurd h' (Nat.not_odd_iff_even.mpr (even_two_mul _))
  have hP : IsPGroup 2 (Subgroup.centralizer {s} : Subgroup X) := fun c =>
    ⟨1, Subtype.ext (by simpa using hC c c.2)⟩
  have hTC : (T : Subgroup X) ≤ Subgroup.centralizer {s} := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (w4s_comm_of_sq (fun z hz => w4s_sq_eq_one_of_mem_sylow hord T hz) hx hsT)
  rw [← Subgroup.mem_centralizer_singleton_iff, T.is_maximal' hP hTC]

end OrderTwoOrOdd

theorem isStronglyEmbeddedOrder_normalizer {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hord : ∀ x : X, orderOf x ∣ 2 ∨ Odd (orderOf x))
    (T : Sylow 2 X) :
    CFSG.BenderSuzuki.IsStronglyEmbeddedOrder (Subgroup.normalizer (T : Set X)) := by
  have h2X := w4s_two_dvd_card hnonab
  have hT2 : ∀ x ∈ (T : Subgroup X), x ^ 2 = 1 := fun x hx =>
    w4s_sq_eq_one_of_mem_sylow hord T hx
  refine ⟨fun htop => ?_, ?_, fun g hg => ?_⟩
  · rcases (Subgroup.normalizer_eq_top_iff.mp htop).eq_bot_or_eq_top with h | h
    · exact Sylow.ne_bot_of_dvd_card T h2X h
    · obtain ⟨a, b, hab⟩ := hnonab
      exact hab (w4s_comm_of_sq hT2 (by rw [h]; exact Subgroup.mem_top a)
        (by rw [h]; exact Subgroup.mem_top b))
  · exact even_iff_two_dvd.mpr ((Sylow.dvd_card_of_dvd_card T h2X).trans
      (Subgroup.card_dvd_of_le Subgroup.le_normalizer))
  · by_contra hodd
    obtain ⟨⟨s, hsMM⟩, hx⟩ := exists_prime_orderOf_dvd_card' 2
      (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    rw [Subgroup.orderOf_mk] at hx
    have hs2 : s ^ 2 = 1 := by rw [← hx]; exact pow_orderOf_eq_one s
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hx
      exact absurd hx (by norm_num)
    obtain ⟨hsM, hsMg⟩ := Subgroup.mem_inf.mp hsMM
    obtain ⟨m, hmM, hms⟩ := Subgroup.mem_map.mp hsMg
    have hms' : g * m * g⁻¹ = s := hms
    have hm2 : m ^ 2 = 1 := by
      have h := hs2
      rw [← hms', conj_pow] at h
      calc m ^ 2 = g⁻¹ * (g * m ^ 2 * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have hm1 : m ≠ 1 := by
      rintro rfl
      apply hs1
      rw [← hms']
      group
    have hsT := w4s_mem_of_mem_normalizer T hsM hs2
    have hmT := w4s_mem_of_mem_normalizer T hmM hm2
    apply hg
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhm : h * m = m * h := w4s_comm_of_sq hT2 hh hmT
      refine (w4s_comm_iff_mem hord T hsT hs1 (g * h * g⁻¹)).mp ?_
      rw [← hms']
      calc g * h * g⁻¹ * (g * m * g⁻¹) = g * (h * m) * g⁻¹ := by group
        _ = g * (m * h) * g⁻¹ := by rw [hhm]
        _ = g * m * g⁻¹ * (g * h * g⁻¹) := by group
    · intro hh
      have hhs : g * h * g⁻¹ * s = s * (g * h * g⁻¹) := w4s_comm_of_sq hT2 hh hsT
      refine (w4s_comm_iff_mem hord T hmT hm1 h).mp ?_
      rw [← hms'] at hhs
      calc h * m = g⁻¹ * (g * h * g⁻¹ * (g * m * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * m * g⁻¹ * (g * h * g⁻¹)) * g := by rw [hhs]
        _ = m * h := by group

theorem exists_sl2_equiv_of_orderOf {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hord : ∀ x : X, orderOf x ∣ 2 ∨ Odd (orderOf x)) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (X ≃* SL(2, GaloisField 2 n)) := by
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  have hab : CFSG.Walter.HasAbelianSylowTwo X := fun P =>
    isMulCommutative_iff.mpr fun a b => Subtype.ext
      (w4s_comm_of_sq (fun z hz => w4s_sq_eq_one_of_mem_sylow hord P hz) a.2 b.2)
  rcases CFSG.BenderSuzuki.bender_suzuki _ (isStronglyEmbeddedOrder_normalizer hnonab hord T) with
    ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · exact ⟨n, hn, ⟨e.trans (CFSG.Timmesfeld.RankOne.psl2EquivSL2 (GaloisField 2 n))⟩⟩
  · exfalso
    have hmodel : CFSG.Theory.Comparator.SzModel n = CFSG.Open.Sz n := CFSG.Models.benderSzModel_eq_sz n
    let e' : X ≃* CFSG.Open.Sz n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.Sz n) := Finite.of_surjective e' e'.surjective
    have hB := (CFSG.Open.bender_suzuki_borel_full n hn).map_mulEquiv e'.symm
    refine CFSG.Walter.not_hasAbelianSylowTwo_of_fusionBenderBorel hB ?_ le_rfl hab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · exfalso
    have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
      CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : X ≃* CFSG.Open.PSU3 2 n := e.trans (MulEquiv.subgroupCongr hmodel)
    have : Finite (CFSG.Open.PSU3 2 n) := Finite.of_surjective e' e'.surjective
    have hB := (CFSG.Open.bender_psu3_borel_full n hn).map_mulEquiv e'.symm
    refine CFSG.Walter.not_hasAbelianSylowTwo_of_fusionBenderBorel hB ?_ (by norm_num) hab
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

section Swap

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}

theorem exists_sl2_equiv (hW : ∀ w : W, w ^ 2 = 1)
    (hLq : CFSG.Open.IsQuasisimple ↥L) (ht2 : orderOf t = 2)
    (hcomm : ⁅L, L.map (MulAut.conj t).toMonoidHom⁆ = ⊥)
    (hirr : IsIrrOn (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊤ ⊥)
    (hdiag : ∀ x ∈ L, ∀ w ∈ commV (Subgroup.zpowers t), (x * (t * x * t⁻¹)) w = w) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (↥L ≃* SL(2, GaloisField 2 n)) := by
  have hZ : Subgroup.center ↥L = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => Subtype.ext ?_
    rw [Subgroup.coe_one]
    exact eq_one_of_mem_center hW hLq ht2 hcomm hirr hdiag x.2 fun y hy =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hy⟩)).symm
  have : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hLq.2
  have : IsSimpleGroup ↥L :=
    (QuotientGroup.quotientBot.symm.trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).isSimpleGroup
  have hnonab : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    push Not at h
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥L
    have hc : ∀ x : ↥L, x = 1 := fun x => by
      have hx : x ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.mpr fun y => h y x
      rw [hZ, Subgroup.mem_bot] at hx
      exact hx
    exact hab ((hc a).trans (hc b).symm)
  have hord : ∀ x : ↥L, orderOf x ∣ 2 ∨ Odd (orderOf x) := fun x => by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_dvd_two_or_odd hW hLq ht2 hcomm hirr hdiag x.2
  exact exists_sl2_equiv_of_orderOf hnonab hord

end Swap

end CFSG.LocalAnalysis.WeakClosure81
