module

public import CFSG.RankThree.PartTwo.Sec12.Item128BarProofHJL0
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134Sylow
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.KFacts.KS14HJTwentySeven
import CFSG.RankThree.PartTwo.Sec6.Item612
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.Sec12.BCensus

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup)

variable {G : Type} [Group G] [Finite G]

theorem mem_residual_of_pow_three {X : Subgroup G}
    (hXp : Group.IsPerfect (X ⧸ aschbacherSolvableCore 3 X)) {a : G} {k : ℕ}
    (ha3 : a ^ 3 ^ k = 1) (haX : a ∈ Sec4.thetaQuotCentralizer X) {x : G}
    (hx : x ∈ X ⊓ Subgroup.centralizer ({a} : Set G)) {j : ℕ} (hx3 : x ^ 3 ^ j = 1) :
    x ∈ inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({a} : Set G)) := by
  set Y := X ⊓ Subgroup.centralizer ({a} : Set G) with hY
  have hXeq := Proof128.eq_residual_sup_theta hXp ha3 haX
  have hYeq : X = Y ⊔ inSubgroup (aschbacherSolvableCore 3) X :=
    le_antisymm (hXeq.le.trans (sup_le_sup_right (Subgroup.map_subtype_le _) _))
      (sup_le inf_le_left (Subgroup.map_subtype_le _))
  set ψ : Y →* X ⧸ aschbacherSolvableCore 3 X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 X)).comp
      (Subgroup.inclusion (inf_le_left : Y ≤ X)) with hψdef
  have hψ : Function.Surjective ψ :=
    PartOne.EmbeddingFixedResidual.surjective_inclusion_quotient inf_le_left hYeq
  have hres : (perfectResidual Y).map ψ = ψ.range := by
    have h : (perfectResidual Y).map ψ = perfectResidual (X ⧸ aschbacherSolvableCore 3 X) :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
    rw [h, MonoidHom.range_eq_top_of_surjective _ hψ]
    exact top_le_iff.mp ((perfect_residual_transport (MonoidHom.id _)).2.2 ⊤
      (Group.IsPerfect.top_iff.mpr hXp))
  obtain ⟨hθs, -, hθp, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hk : ¬ 3 ∣ Nat.card ψ.ker :=
    (Sec13.ker_facts_of_injective ψ (Subgroup.inclusion (inf_le_left : Y ≤ X))
      (Subgroup.inclusion_injective _) (aschbacherSolvableCore 3 X)
      (fun y hy => (QuotientGroup.eq_one_iff _).mp hy) hθs hθp).2
  have hx' : (⟨x, hx⟩ : Y) ^ 3 ^ j = 1 := Subtype.ext (by simpa using hx3)
  exact ⟨⟨x, hx⟩, Sec13.mem_of_pow_three_of_map_eq ψ (perfectResidual Y) hres hk hx', rfl⟩

theorem false_of_inducesTypeOn {A K D : Subgroup G} {b : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hbA : b ∈ A) (hK : K ∈ thetaComponentsAt 3 b)
    (hAN : A ≤ Subgroup.normalizer (K : Set G)) (hDA : D ≤ A) (hDK : D ≤ K)
    (hAeq : A = Subgroup.zpowers b ⊔ D) {x : G} (hxA : x ∈ A)
    (hx : Sec4.InducesTypeOn K x 3) : False := by
  obtain ⟨hxN, π, p, f, K', _, hK', hq', e, y', hy'H, hy'3, hact⟩ := hx
  have haC : b ∈ Subgroup.centralizer (D : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun d hd =>
      congrArg Subtype.val (hA.1.is_comm.comm ⟨d, hDA hd⟩ ⟨b, hbA⟩)
  obtain ⟨k, y, hy, hxy⟩ := KFacts.KS14.exists_zpow_mul_of_mem_sup haC (by rw [← hAeq]; exact hxA)
  have hyJ : y ∈ K := hDK hy
  have haNJ : b ∈ Subgroup.normalizer (K : Set G) := hAN hbA
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hyJ
  have hρa : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨b, haNJ⟩) = 1 := by
    have hmem := Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hK
    obtain ⟨n, hn, hna⟩ := hmem
    have : n = ⟨b, haNJ⟩ := Subtype.ext hna
    rw [← this]
    exact MonoidHom.mem_ker.mp hn
  have hxe : (⟨x, hxN⟩ : Subgroup.normalizer (K : Set G)) = ⟨b, haNJ⟩ ^ k * ⟨y, hyN⟩ :=
    Subtype.ext (by simp [hxy])
  have hρx : ∀ z : K ⧸ aschbacherSolvableCore 3 K,
      Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) z =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨y, hyJ⟩ : K)) * z *
          (QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨y, hyJ⟩ : K))⁻¹ := by
    intro z
    have h1 : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hxN⟩) =
        Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨y, hyN⟩) := by
      rw [hxe, map_mul, map_mul, map_zpow, map_zpow, hρa, one_zpow, one_mul]
    rw [h1]
    induction z using QuotientGroup.induction_on with
    | H z =>
      rw [Sec4.thetaQuotMulAut_mk]
      change ((QuotientGroup.mk' (aschbacherSolvableCore 3 K))
        (K.normalizerMonoidHom ⟨y, hyN⟩ z)) = _
      have : K.normalizerMonoidHom ⟨y, hyN⟩ z = ⟨y, hyJ⟩ * z * (⟨y, hyJ⟩ : K)⁻¹ :=
        Subtype.ext rfl
      rw [this]
      simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := hK'.prime
    have hf := hK'.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK
    cases π
    · have hsol := Sec13.isSolvable_projImage_slPi_two hK' h2
      have : Group.IsSolvable (K ⧸ aschbacherSolvableCore 3 K) :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hq.1
      have : IsSimpleGroup ((K ⧸ aschbacherSolvableCore 3 K) ⧸
          Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)) := hq.2.1
      have : Nontrivial (K ⧸ aschbacherSolvableCore 3 K) :=
        (QuotientGroup.mk_surjective
          (s := Subgroup.center (K ⧸ aschbacherSolvableCore 3 K))).nontrivial
      exact Group.IsPerfect.not_isSolvable (K ⧸ aschbacherSolvableCore 3 K) inferInstance
    · change p ^ f % 3 = 1 at hq'
      omega
  set yb := QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨y, hyJ⟩ : K) with hyb
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e yb).2
  have hcomm : ∀ m ∈ Sec4.slPi π 3 (p ^ f) K',
      ProjGenLinGroup.mk (s⁻¹ * y') * ProjGenLinGroup.mk m =
        ProjGenLinGroup.mk m * ProjGenLinGroup.mk (s⁻¹ * y') := by
    intro m hm
    set z := e.symm ⟨ProjGenLinGroup.mk m, Subgroup.mem_map_of_mem _ hm⟩ with hz
    have hez : ((e z : projImage (Sec4.slPi π 3 (p ^ f) K')) : ProjGenLinGroup (Fin 3) K') =
        ProjGenLinGroup.mk m := by rw [hz, MulEquiv.apply_symm_apply]
    have h1 := hact z
    rw [hρx z, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      hez, ← hse] at h1
    rw [map_mul, map_inv]
    calc (ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y' * ProjGenLinGroup.mk m =
        (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk y' * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk y')⁻¹) * ProjGenLinGroup.mk y' := by group
      _ = (ProjGenLinGroup.mk s)⁻¹ * (ProjGenLinGroup.mk s * ProjGenLinGroup.mk m *
          (ProjGenLinGroup.mk s)⁻¹) * ProjGenLinGroup.mk y' := by rw [h1]
      _ = ProjGenLinGroup.mk m * ((ProjGenLinGroup.mk s)⁻¹ * ProjGenLinGroup.mk y') := by group
  have hsc := Sec13.mem_statedScalars_of_commute_mk hK' hq' hq2 hcomm
  apply Sec4.not_inner_of_type3 hK' hq' hy'H hy'3
  refine ⟨s, hs, fun m _ => ?_⟩
  have h1 := Sec4.commute_of_mem_statedScalars hsc m
  calc y' * m * y'⁻¹ = s * ((s⁻¹ * y') * m) * (s⁻¹ * y')⁻¹ * s⁻¹ := by group
    _ = s * (m * (s⁻¹ * y')) * (s⁻¹ * y')⁻¹ * s⁻¹ := by rw [← h1]
    _ = s * m * s⁻¹ := by group

theorem exists_sylow_le_centralizer_of_not_dvd {A K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h81 : ¬ 81 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K))
    (h9 : Nat.card (A ⊓ K : Subgroup G) = 9) {c : G} (hcA : c ∈ A) (hcK : c ∈ K) {n : G}
    (hnK : n ∈ K) (hnA : n ∈ Subgroup.normalizer (A : Set G)) {k : ℕ} (hn3 : n ^ 3 ^ k = 1)
    (hnc : n * c = c * n) (hnmove : ∃ x ∈ A, n * x * n⁻¹ ≠ x) :
    ∃ S : Sylow 3 K, (⟨c, hcK⟩ : K) ∈ (S : Subgroup K) ∧
      (S : Subgroup K) ≤ Subgroup.centralizer ({(⟨c, hcK⟩ : K)} : Set K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set c' : K := ⟨c, hcK⟩ with hc'
  set n' : K := ⟨n, hnK⟩ with hn'
  set E := (A ⊓ K).subgroupOf K with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  have hnE : Subgroup.zpowers n' ≤ Subgroup.normalizer (E : Set K) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hx' : (x : G) ∈ A ⊓ K := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hnA _).mp hx'.1,
      K.mul_mem (K.mul_mem hnK hx'.2) (K.inv_mem hnK)⟩
  have hn'3 : n' ^ 3 ^ k = 1 := Subtype.ext (by simpa using hn3)
  have hQ3 : IsPGroup 3 (Subgroup.zpowers n' ⊔ E : Subgroup K) :=
    (Proof128.isPGroup_zpowers_of_pow hn'3).to_sup_of_normal_right' hE3 hnE
  set Q : Subgroup K := Subgroup.zpowers n' ⊔ E with hQ
  have hQC : Q ≤ Subgroup.centralizer ({c'} : Set K) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hnc
    · intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxA : (x : G) ∈ A := (Subgroup.mem_subgroupOf.mp hx).1
      exact Subtype.ext (hcomm _ hxA c hcA)
  have hcQ : c' ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr ⟨hcA, hcK⟩)
  have hnE' : n' ∉ E := by
    intro hnE'
    obtain ⟨x, hxA, hx⟩ := hnmove
    apply hx
    have hnA' : n ∈ A := (Subgroup.mem_subgroupOf.mp hnE').1
    rw [hcomm n hnA' x hxA, mul_inv_cancel_right]
  have hQ27 : 27 ≤ Nat.card Q := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ3
    have hEQ : E ≤ Q := le_sup_right
    have h9dvd : 9 ∣ 3 ^ j := hj ▸ hE9 ▸ Subgroup.card_dvd_of_le hEQ
    have hj2 : 2 ≤ j := by
      by_contra hlt
      push Not at hlt
      interval_cases j <;> norm_num at h9dvd
    have hj3 : j ≠ 2 := by
      rintro rfl
      apply hnE'
      have heq : E = Q := Subgroup.eq_of_le_of_card_ge hEQ (by rw [hj, hE9]; norm_num)
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers n')
    rw [hj]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨S, hQS⟩ := hQ3.exists_le_sylow
  have hS27 : Nat.card (S : Subgroup K) ≤ 27 := by
    have hinj := injOn_mk_of_isPGroup Nat.prime_three S.isPGroup'
    have hcard : Nat.card ((S : Subgroup K).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) = Nat.card (S : Subgroup K) := by
      change Nat.card (↑((S : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K))) :
        Set (K ⧸ aschbacherSolvableCore 3 K)) = Nat.card ((S : Subgroup K) : Set K)
      rw [Subgroup.coe_map, Nat.card_image_of_injOn hinj]
    have hdvd : Nat.card (S : Subgroup K) ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K) := by
      rw [← hcard]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp S.isPGroup'
    rw [hi] at hdvd ⊢
    by_contra hlt
    push Not at hlt
    have hi4 : 4 ≤ i := by
      by_contra h4
      push Not at h4
      interval_cases i <;> norm_num at hlt
    apply h81
    have : 3 ^ 4 ∣ 3 ^ i := Nat.pow_dvd_pow 3 hi4
    exact (show (81 : ℕ) = 3 ^ 4 by norm_num) ▸ this.trans hdvd
  have hSQ : (S : Subgroup K) = Q :=
    (Subgroup.eq_of_le_of_card_ge hQS (by omega)).symm
  exact ⟨S, hSQ ▸ hcQ, hSQ ▸ hQC⟩

theorem exists_threeElement_of_perm3 (h45 : Sec4.Item4_5) (hK2 : KFacts.KS12NormalizerMoves)
    {A L : Subgroup G} {c : G} (h : Sec12StdBar G A c L)
    (hty : Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22)
    {K : Subgroup G} (hS3 : Nonempty (Sec4.autIn K A ≃* Equiv.Perm (Fin 3))) :
    ∃ n ∈ K, n ∈ Subgroup.normalizer (A : Set G) ∧ (∃ k : ℕ, n ^ 3 ^ k = 1) ∧
      n * c = c * n ∧ ∃ x ∈ A, n * x * n⁻¹ ≠ x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA := h.mem_A
  obtain ⟨eS3⟩ := hS3
  obtain ⟨y, hy1, hy3⟩ := Proof128.exists_ne_one_pow_three_of_perm3 eS3
  have hy'3 : (y : MulAut A) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
  have hy'1 : (y : MulAut A) ≠ 1 := fun h' => hy1 (Subtype.ext h')
  have hyT : (y : MulAut A) ∈ transvectionGroup A ⟨c, hcA⟩ :=
    Proof128.mem_transvectionGroup_of_mem_wStar h45 hK2 h hty
      (Sec13.Holds134.autIn_le_wStar K y.2) (k := 1) (by simpa using hy'3)
  obtain ⟨g, hgN, hgK, hgy⟩ := Sec4.mem_autIn_iff.mp y.2
  obtain ⟨k, m, hm, hgm, -⟩ := exists_threePart g
  have hnK : g ^ m ∈ K := K.pow_mem hgK m
  have hnA : g ^ m ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hgN m
  have hσn : A.normalizerMonoidHom ⟨g ^ m, hnA⟩ = (y : MulAut A) ^ m := by
    have e : (⟨g ^ m, hnA⟩ : Subgroup.normalizer (A : Set G)) = ⟨g, hgN⟩ ^ m :=
      Subtype.ext (by simp)
    rw [e, map_pow, hgy]
  have hσn1 : (y : MulAut A) ^ m ≠ 1 := by
    intro h'
    have hord : orderOf (y : MulAut A) = 3 := orderOf_eq_prime hy'3 hy'1
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hord] at this
    exact hm this
  have hσnT : (y : MulAut A) ^ m ∈ transvectionGroup A ⟨c, hcA⟩ := pow_mem hyT m
  have hnc : g ^ m * c = c * g ^ m := by
    have h1 := hσnT.1
    rw [← hσn] at h1
    have h2 : g ^ m * c * (g ^ m)⁻¹ = c := by
      have := congrArg Subtype.val h1
      rwa [Sec4.normalizerMonoidHom_apply_coe] at this
    calc g ^ m * c = g ^ m * c * (g ^ m)⁻¹ * g ^ m := by group
      _ = c * g ^ m := by rw [h2]
  have hnmove : ∃ x ∈ A, g ^ m * x * (g ^ m)⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    apply hσn1
    rw [← hσn]
    ext x
    rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
    exact hcon x x.2
  exact ⟨g ^ m, hnK, hnA, ⟨k, hgm⟩, hnc, hnmove⟩

end CFSG.RankThree.PartTwo.Sec12.BCensus
