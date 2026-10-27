module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Ua
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Uc
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL_fix_iff rhoL_inner)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218k_exists_lift {L : Subgroup G} {Eb Qb : Subgroup (Bar2 L)}
    (hEb : IsElemAbelian 3 Eb) (hEc : Nat.card Eb = 3 ^ 2) (hQb : IsPGroup 3 Qb) (hEQ : Eb ≤ Qb) :
    ∃ E Q : Subgroup ↥L, E ≤ Q ∧ IsPGroup 3 Q ∧
      E.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Eb ∧
      Q.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Qb ∧
      IsElemAbelian 3 (E.map L.subtype) ∧ Nat.card (E.map L.subtype) = 3 ^ 2 := by
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  obtain ⟨Q, hQp, hQmap, hQdisj⟩ := UC6S846.exists_lift_pGroup π (QuotientGroup.mk'_surjective _)
    hker Nat.prime_three (by norm_num) Qb hQb
  have hEmap : (Q ⊓ Eb.comap π).map π = Eb := by
    refine le_antisymm (map_le_iff_le_comap.2 inf_le_right) fun x hx => ?_
    have h1 : x ∈ Q.map π := by
      rw [hQmap]
      exact hEQ hx
    obtain ⟨q, hq, rfl⟩ := mem_map.1 h1
    exact mem_map_of_mem π (mem_inf.2 ⟨hq, hx⟩)
  have hdisj : Disjoint (Q ⊓ Eb.comap π) π.ker := hQdisj.mono_left inf_le_left
  refine ⟨Q ⊓ Eb.comap π, Q, inf_le_left, hQp, hEmap, hQmap, ?_, ?_⟩
  · exact (UC6S846.isElemAbelian_of_disjoint_ker π _ hdisj (by rw [hEmap]; exact hEb)).map _
  · rw [card_map_of_injective L.subtype_injective, ← UC6S846.card_map_of_disjoint_ker π _ hdisj,
      hEmap, hEc]

theorem uc22s218k_exists_centralizer_lift {L : Subgroup G} {P : Subgroup ↥L} (hP : IsPGroup 3 P)
    {p : ℕ} {zb : Bar2 L} (hzb : zb ∈ centralizer ((P.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
      Subgroup (Bar2 L)) : Set (Bar2 L))) (hzo : orderOf zb = p) :
    ∃ z ∈ L, orderOf z = p ∧ ∀ x ∈ P, Commute z (x : G) := by
  have hN : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥L) := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  rw [CFSG.GroupTheory.SteinbergBS.centralizer_map_mk'_eq hN hP] at hzb
  obtain ⟨z₀, hz₀C, rfl⟩ := mem_map.1 hzb
  have h1 : p ∣ orderOf z₀ := by
    rw [← hzo]
    exact orderOf_map_dvd _ _
  refine ⟨((z₀ ^ (orderOf z₀ / p) : ↥L) : G), (z₀ ^ (orderOf z₀ / p)).2, ?_, fun x hx => ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (orderOf_pos z₀).ne' h1
  · have h2 : Commute z₀ x := (mem_centralizer_iff.1 hz₀C x hx).symm
    exact (h2.pow_left _).map L.subtype

theorem uc22s218k_conclusion76_hyps {L M E : Subgroup G} {n p : ℕ} (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hX : IsSp4 (Bar2 L) n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsPGroup 3 E) (hEL : E ≤ L) {y : G} (hyM : y ∈ M) (hyo : orderOf y = p)
    (hyL : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L)
    (hz : ∀ e ∈ E, ∃ z ∈ L, Commute z e ∧ orderOf z = p) :
    0 < CFSG.Open.pRank p (M ⊓ centralizer (E : Set G)) ∧
      ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 →
        1 < CFSG.Open.pRank p (M ⊓ normalizer (X : Set G)) := by
  have hO : IsPGroup 2 (pCoreOf 2 L) := UC6S846.isPGroup_pCoreOf L
  have hOL : pCoreOf 2 L ≤ L := map_subtype_le _
  have hLO : L ≤ normalizer (pCoreOf 2 L : Set G) :=
    le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf L)
  have hyp : IsPGroup p (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨w, hwL, hwC⟩ := uc22s218u_exists_conj_commute hp hp2 Nat.prime_three (by norm_num) hO
    hOL hLO hE hEL hyp (hML hyM) hyL
  set y' : G := w⁻¹ * y * w with hy'
  have hy'M : y' ∈ M := mul_mem (mul_mem (inv_mem (hLM hwL)) hyM) (hLM hwL)
  have hy'o : orderOf y' = p := by
    have h1 : orderOf (MulAut.conj w⁻¹ y) = p := by rw [MulEquiv.orderOf_eq, hyo]
    rw [MulAut.conj_apply, inv_inv] at h1
    exact h1
  have hy'p : y' ^ p = 1 := by
    rw [← hy'o]
    exact pow_orderOf_eq_one y'
  have hy'L : ∀ l ∈ L, y' * l * y'⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro l hl
    have h1 := hyL _ (mul_mem (mul_mem hwL hl) (inv_mem hwL))
    have h2 := (mem_normalizer_iff.1 (hLO (inv_mem hwL)) _).1 h1
    have e : y' * l * y'⁻¹ * l⁻¹ =
        w⁻¹ * (y * (w * l * w⁻¹) * y⁻¹ * (w * l * w⁻¹)⁻¹) * w⁻¹⁻¹ := by
      rw [hy']
      group
    rw [e]
    exact h2
  have hy'nL : y' ∉ L := by
    intro hy'L0
    have hzc : (QuotientGroup.mk (⟨y', hy'L0⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
      have h1 := (rhoL_fix_iff L ⟨y', le_normalizer hy'L0⟩ l).2 (hy'L l l.2)
      rw [rhoL_inner L y' hy'L0, MulAut.conj_apply] at h1
      calc (QuotientGroup.mk l : Bar2 L) * QuotientGroup.mk ⟨y', hy'L0⟩
          = QuotientGroup.mk ⟨y', hy'L0⟩ * QuotientGroup.mk l *
            (QuotientGroup.mk ⟨y', hy'L0⟩)⁻¹ * QuotientGroup.mk ⟨y', hy'L0⟩ := by rw [h1]
        _ = QuotientGroup.mk ⟨y', hy'L0⟩ * QuotientGroup.mk l := by group
    rw [uc22p218d_center_eq_bot_sp4 hX, mem_bot, QuotientGroup.eq_one_iff] at hzc
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hzc⟩
    have h2 : y' ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val (congrArg Subtype.val hk)
      simpa using h
    have h3 : p ∣ 2 ^ k := by
      rw [← hy'o]
      exact orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  refine ⟨?_, fun X hXE hXc => ?_⟩
  · have h1 := UC6S846.le_pRank' hp (zpowers_le.2 (mem_inf.2 ⟨hy'M, hwC⟩))
      (isElemAbelian_zpowers hy'p) (k := 1) (by rw [Nat.card_zpowers, hy'o, pow_one])
    omega
  obtain ⟨x, hxX, hx1⟩ := X.bot_or_exists_ne_one.resolve_left fun h => by
    rw [h, card_bot] at hXc
    omega
  have hxo : orderOf x = 3 := by
    have h1 : orderOf x ∣ 3 := hXc ▸ Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hXx : zpowers x = X :=
    eq_of_le_of_card_ge (zpowers_le.2 hxX) (by rw [hXc, Nat.card_zpowers, hxo])
  obtain ⟨z, hzL, hzx, hzo⟩ := hz x (hXE hxX)
  have hzC : z ∈ centralizer (X : Set G) := by
    rw [← hXx, mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hzx.zpow_right k).eq.symm
  have hy'C : y' ∈ centralizer (X : Set G) := centralizer_le (SetLike.coe_subset_coe.2 hXE) hwC
  have hzp : IsPGroup p (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  obtain ⟨w', hw'L, hw'C⟩ := uc22s218u_exists_conj_commute (L := L ⊓ centralizer (X : Set G))
    (O := pCoreOf 2 L ⊓ centralizer (X : Set G)) hp hp2 hp hp2 (hO.to_le inf_le_left)
    (inf_le_inf_right _ hOL)
    (fun l hl => uc22s218u_mem_normalizer_inf (hLO (mem_inf.1 hl).1)
      (le_normalizer (mem_inf.1 hl).2))
    hzp (zpowers_le.2 (mem_inf.2 ⟨hzL, hzC⟩))
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'o, pow_one]))
    (uc22s218u_mem_normalizer_inf (hML hy'M) (le_normalizer hy'C))
    (fun l hl => mem_inf.2 ⟨hy'L l (mem_inf.1 hl).1,
      mul_mem (mul_mem (mul_mem hy'C (mem_inf.1 hl).2) (inv_mem hy'C)) (inv_mem (mem_inf.1 hl).2)⟩)
  set z₁ : G := w' * z * w'⁻¹ with hz₁
  have hz₁LC : z₁ ∈ L ⊓ centralizer (X : Set G) :=
    mul_mem (mul_mem hw'L (mem_inf.2 ⟨hzL, hzC⟩)) (inv_mem hw'L)
  have hz₁o : orderOf z₁ = p := by
    have h1 : orderOf (MulAut.conj w' z) = p := by rw [MulEquiv.orderOf_eq, hzo]
    rw [MulAut.conj_apply] at h1
    exact h1
  have hz₁y' : z₁ * y' = y' * z₁ := by
    have h1 := mem_centralizer_iff.1 hw'C z (mem_zpowers z)
    calc z₁ * y' = w' * (z * (w'⁻¹ * y' * w')) * w'⁻¹ := by rw [hz₁]; group
      _ = w' * ((w'⁻¹ * y' * w') * z) * w'⁻¹ := by rw [h1]
      _ = y' * z₁ := by rw [hz₁]; group
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₁o
    exact hp.one_lt.ne hz₁o
  obtain ⟨hEel, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp
    (by rw [← hz₁o]; exact pow_orderOf_eq_one z₁) hy'p hz₁1
    (fun h => hy'nL (zpowers_le.2 (mem_inf.1 hz₁LC).1 h)) hz₁y'
  have hEN : zpowers z₁ ⊔ zpowers y' ≤ M ⊓ normalizer (X : Set G) :=
    sup_le (zpowers_le.2 (mem_inf.2 ⟨hLM (mem_inf.1 hz₁LC).1,
        centralizer_le_normalizer _ (mem_inf.1 hz₁LC).2⟩))
      (zpowers_le.2 (mem_inf.2 ⟨hy'M, centralizer_le_normalizer _ hy'C⟩))
  have := UC6S846.le_pRank' hp hEN hEel hEc
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
