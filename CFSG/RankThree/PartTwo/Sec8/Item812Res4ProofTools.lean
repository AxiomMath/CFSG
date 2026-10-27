module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofSylow
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofFrattini
import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSp62
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.Sec10.Item105
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSp)

@[expose] def KF812WreathCent : Prop :=
  ∀ (M : Type) [Group M], (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
    ∀ S : Subgroup M, IsPGroup 3 S → ∀ E : Subgroup M, E ≤ S →
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ y ∈ S, y ∉ E → Nat.card (E ⊓ Subgroup.centralizer {y} : Subgroup M) ≤ 3

@[expose] def KF812E27Fuse : Prop :=
  ∀ (M : Type) [Group M], (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
    ∀ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ y : M, y ^ 3 = 1 → ∃ g : M, g * y * g⁻¹ ∈ E

namespace Item812Res4

theorem card_of_isYGroup {M : Type} [Group M] (hM : Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (M ≃* projSp 3 (GaloisField 2 1))) :
    Nat.card M = 181440 ∨ Nat.card M = 1451520 := by
  rcases hM with h | h
  · obtain ⟨e⟩ := h
    left
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  · obtain ⟨e⟩ := h
    right
    rw [Nat.card_congr e.toEquiv]
    exact Sec21.Item223CensusResProof.card_projSp_three_two

theorem card_le_of_isPGroup {M : Type} [Group M] (hM : Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (M ≃* projSp 3 (GaloisField 2 1))) {S : Subgroup M} (hS : IsPGroup 3 S) :
    Nat.card S ≤ 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := card_of_isYGroup hM
  have : Finite M := Nat.finite_of_card_ne_zero (by rcases hcard with h | h <;> omega)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdvd : 3 ^ k ∣ Nat.card M := hk ▸ Subgroup.card_subgroup_dvd_card S
  have hk4 : k ≤ 4 := by
    by_contra hk4
    have h5 : 3 ^ 5 ∣ Nat.card M := (pow_dvd_pow 3 (by omega)).trans hdvd
    rcases hcard with h | h <;> rw [h] at h5 <;> norm_num at h5
  calc Nat.card S = 3 ^ k := hk
    _ ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    _ = 81 := by norm_num


theorem isElemAbelian_map {M M' : Type*} [Group M] [Group M'] (f : M →* M') {E : Subgroup M}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.map f) :=
  CFSG.SectionRank.isElemAbelian_map hE _

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {E : Subgroup G} (Y : Subgroup G)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) : CFSG.Assembly.IsElemAbelian 3 (E.subgroupOf Y) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE Y

theorem card_map_of_injOn {M M' : Type*} [Group M] [Group M'] (f : M →* M') {S : Subgroup M}
    (h : Set.InjOn f S) : Nat.card (S.map f) = Nat.card S := by
  have := Nat.card_image_of_injOn h
  rw [← Subgroup.coe_map] at this
  exact this

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_core (Y : Subgroup G) : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 Y) :=
  (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.2.1

theorem injOn_mk_of_isPGroup {Y : Subgroup G} {S : Subgroup Y} (hS : IsPGroup 3 S) :
    Set.InjOn (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)) (S : Set Y) := by
  intro u hu v hv huv
  have h1 : u⁻¹ * v ∈ aschbacherSolvableCore 3 Y := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at huv
    exact huv
  obtain ⟨k, hk⟩ := hS ⟨u⁻¹ * v, S.mul_mem (S.inv_mem hu) hv⟩
  have h2 : (u⁻¹ * v) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  exact inv_mul_eq_one.mp (KFacts.eq_one_of_pow_three_pow_eq_one (not_dvd_card_core Y) h1 h2)

abbrev IsYQuot (Y : Subgroup G) : Prop :=
  Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* alternatingGroup (Fin 9)) ∨
    Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSp 3 (GaloisField 2 1))

theorem card_le_of_le {Y : Subgroup G} (hY : IsYQuot Y) {S : Subgroup G} (hSY : S ≤ Y)
    (hS : IsPGroup 3 S) : Nat.card S ≤ 81 := by
  have hS' : IsPGroup 3 (S.subgroupOf Y) := hS.comap_subtype
  have h1 : Nat.card ((S.subgroupOf Y).map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) =
      Nat.card S := by
    rw [card_map_of_injOn _ (injOn_mk_of_isPGroup hS'),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv]
  rw [← h1]
  exact card_le_of_isPGroup hY (hS'.map _)

theorem card_inf_centralizer_le (hW : KF812WreathCent) {Y : Subgroup G} (hY : IsYQuot Y)
    {S E : Subgroup G} (hSY : S ≤ Y) (hS : IsPGroup 3 S) (hES : E ≤ S)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {y : G} (hyS : y ∈ S)
    (hyE : y ∉ E) : Nat.card (E ⊓ Subgroup.centralizer {y} : Subgroup G) ≤ 3 := by
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  have hS' : IsPGroup 3 (S.subgroupOf Y) := hS.comap_subtype
  have hinj := injOn_mk_of_isPGroup hS'
  have hEY : E ≤ Y := hES.trans hSY
  have hESY : E.subgroupOf Y ≤ S.subgroupOf Y := fun u hu =>
    Subgroup.mem_subgroupOf.mpr (hES (Subgroup.mem_subgroupOf.mp hu))
  set y' : Y := ⟨y, hSY hyS⟩ with hy'
  have hy'S : y' ∈ S.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hyS
  have hE'27 : Nat.card ((E.subgroupOf Y).map π) = 27 := by
    rw [card_map_of_injOn _ (hinj.mono hESY),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hE27]
  have hy'E : π y' ∉ (E.subgroupOf Y).map π := by
    rintro ⟨u, hu, hux⟩
    have h1 : u = y' := hinj (hESY hu) hy'S hux
    have h2 : (u : G) = y := congrArg Subtype.val h1
    exact hyE (h2 ▸ Subgroup.mem_subgroupOf.mp hu)
  have h1 := hW _ hY _ (hS'.map π) _ (Subgroup.map_mono hESY)
    (isElemAbelian_map π (isElemAbelian_subgroupOf Y hE)) hE'27 (π y')
    (Subgroup.mem_map_of_mem π hy'S) hy'E
  have hmem : ∀ u : (E ⊓ Subgroup.centralizer {y} : Subgroup G),
      π ⟨u, hEY (Subgroup.mem_inf.mp u.2).1⟩ ∈
        ((E.subgroupOf Y).map π ⊓ Subgroup.centralizer {π y'} : Subgroup _) := by
    intro u
    obtain ⟨huE, huC⟩ := Subgroup.mem_inf.mp u.2
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr huE), ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp huC)
  refine le_trans (Nat.card_le_card_of_injective (fun u => ⟨_, hmem u⟩) ?_) h1
  intro u v huv
  have h2 := congrArg Subtype.val huv
  have h3 : (⟨u, hEY (Subgroup.mem_inf.mp u.2).1⟩ : Y) = ⟨v, hEY (Subgroup.mem_inf.mp v.2).1⟩ :=
    hinj (hESY (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp u.2).1))
      (hESY (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp v.2).1)) h2
  have h4 : (u : G) = v := congrArg (fun w : Y => (w : G)) h3
  exact Subtype.ext h4

omit [Finite G] in
theorem isElemAbelian_of_le {E F : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hFE : F ≤ E) : CFSG.Assembly.IsElemAbelian 3 F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite G] in
theorem isPGroup_of_isElemAbelian {E : Subgroup G} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    IsPGroup 3 E := CFSG.Open.IsElemAbelian.isPGroup hE

theorem mem_of_forall_commute (hW : KF812WreathCent) {Y : Subgroup G} (hY : IsYQuot Y)
    {B : Subgroup G} (hBY : B ≤ Y) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) {y : G} (hyY : y ∈ Y) {k : ℕ} (hyk : y ^ 3 ^ k = 1)
    (hyB : ∀ x ∈ B, y * x = x * y) : y ∈ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hyB'
  have hc : ∀ x ∈ B, ∀ z ∈ Subgroup.zpowers y, x * z = z * x := by
    intro x hx z hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_right (show Commute x y from (hyB x hx).symm) j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B (Subgroup.zpowers y) hc
  have hS : IsPGroup 3 (B ⊔ Subgroup.zpowers y : Subgroup G) := by
    have hdvd : Nat.card (B ⊔ Subgroup.zpowers y : Subgroup G) ∣ 3 ^ (3 + k) := by
      have h1 : Nat.card (B ⊔ Subgroup.zpowers y : Subgroup G) ∣
          Nat.card B * Nat.card (Subgroup.zpowers y) := hcard ▸ dvd_mul_right _ _
      have h2 : Nat.card (Subgroup.zpowers y) ∣ 3 ^ k := by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hyk
      rw [pow_add, show (3 : ℕ) ^ 3 = Nat.card B by rw [hB27]; norm_num]
      exact h1.trans (Nat.mul_dvd_mul_left _ h2)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    exact IsPGroup.of_card hm
  have h := card_inf_centralizer_le hW hY (sup_le hBY ((Subgroup.zpowers_le).mpr hyY)) hS
    le_sup_left hB hB27 (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)) hyB'
  have hBC : B ⊓ Subgroup.centralizer {y} = B := inf_eq_left.mpr fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hyB x hx).symm
  rw [hBC, hB27] at h
  omega

theorem exists_conj_mem_of_fuse (hF : KF812E27Fuse) {Y : Subgroup G} (hY : IsYQuot Y)
    {B : Subgroup G} (hBY : B ≤ Y) (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) {w : G} (hwY : w ∈ Y) (hw3 : w ^ 3 = 1) :
    ∃ g ∈ Y, g * w * g⁻¹ ∈ B := by
  set N := aschbacherSolvableCore 3 Y with hN
  set π := QuotientGroup.mk' N with hπ
  have hB' : IsPGroup 3 (B.subgroupOf Y) := (isPGroup_of_isElemAbelian hB).comap_subtype
  have hE27 : Nat.card ((B.subgroupOf Y).map π) = 27 := by
    rw [card_map_of_injOn _ (injOn_mk_of_isPGroup hB'),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, hB27]
  have hw3' : (⟨w, hwY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
  obtain ⟨m, hm⟩ := hF _ hY _ (isElemAbelian_map π (isElemAbelian_subgroupOf Y hB)) hE27
    (π ⟨w, hwY⟩) (by rw [← map_pow, hw3', map_one])
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective N m
  obtain ⟨u, hu, hux⟩ := hm
  have hmem : u⁻¹ * (g₀ * ⟨w, hwY⟩ * g₀⁻¹) ∈ N := by
    rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← hπ, hux]
    simp only [hπ, map_mul, map_inv]
  have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hB.2 _ (Subgroup.mem_subgroupOf.mp hu))
  have hc3 : (g₀ * ⟨w, hwY⟩ * g₀⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hw3']
    group
  obtain ⟨t, -, ht⟩ := Item812Res3.exists_mem_conj_eq_of_inv_mul_mem (not_dvd_card_core Y)
    hu3 hc3 hmem
  refine ⟨((t * g₀ : Y) : G), (t * g₀).2, ?_⟩
  have h1 : ((t * g₀ : Y) : G) * w * ((t * g₀ : Y) : G)⁻¹ = (u : G) := by
    have h2 := congrArg (fun v : Y => (v : G)) ht
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2 ⊢
    rw [← h2]
    group
  rw [h1]
  exact Subgroup.mem_subgroupOf.mp hu

theorem le_normalizer_of_card_le {S B : Subgroup G} (hS : IsPGroup 3 S) (hBS : B ≤ S)
    (hcard : Nat.card S ≤ 3 * Nat.card B) : S ≤ Subgroup.normalizer (B : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hBS' : B = S
  · rw [hBS']
    exact Subgroup.le_normalizer
  have hlt : B < S := lt_of_le_of_ne hBS hBS'
  obtain ⟨x, hxS, hxB, hxN⟩ := Sec10.exists_mem_normalizer_not_mem_of_lt_of_isPGroup hS hlt
  set N := Subgroup.normalizer (B : Set G) ⊓ S with hNdef
  have hBN : B ≤ N := le_inf Subgroup.le_normalizer hBS
  have hNS : N ≤ S := inf_le_right
  have hBpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBN
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hNS
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hk
    have hNB : N = B := (Subgroup.eq_of_le_of_card_ge hBN (by rw [hk])).symm
    exact hxB (hNB ▸ (⟨hxN, hxS⟩ : x ∈ N))
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    exact (Nat.card_pos (α := N)).ne' hk
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hm
    exact (Nat.card_pos (α := S)).ne' hm
  have hm1 : m = 1 := by
    rw [hm, hk] at hcard
    have h2 : Nat.card B * (k * m) ≤ Nat.card B * 3 := by nlinarith
    have h3 : k * m ≤ 3 := Nat.le_of_mul_le_mul_left h2 hBpos
    rcases Nat.lt_or_ge m 2 with h | h
    · omega
    · exfalso
      have : 2 * 2 ≤ k * m := Nat.mul_le_mul (by omega) h
      omega
  have hNeq : N = S := Subgroup.eq_of_le_of_card_ge hNS (by rw [hm, hm1, mul_one])
  intro y hy
  exact (hNeq ▸ hy : y ∈ N).1

section Config

variable {A : Subgroup G} {a : G} {X Y P Q R V Pa : Subgroup G}

structure Fin812Pre (A : Subgroup G) (a : G) (X Y P Q R Pa : Subgroup G) : Prop where
  pa_max : Item812Res3.IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G))
  le_pa : A ≤ Pa
  pa_eq : Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa
  sec8B_eq : sec8B A X = A ⊓ Y
  q_max : Item812Res3.IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G))
  pa_le_normalizer : Pa ≤ Subgroup.normalizer (Q : Set G)
  q_eq : R ⊔ Subgroup.zpowers a = Q
  r_comm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  card_r : Nat.card R = 3 ^ 6
  r_pow : ∀ x ∈ R, x ^ 9 = 1
  b_le_r : sec8B A X ≤ R
  omega_r : ∀ x ∈ R, x ^ 3 = 1 → x ∈ sec8B A X
  le_q : A ≤ Q
  omega_q : ∀ x ∈ Q, x ^ 3 = 1 → x ∈ A
  a_not_mem_r : a ∉ R
  r_weak : ∀ g : G, R.map (MulAut.conj g).toMonoidHom ≤ Q →
    R.map (MulAut.conj g).toMonoidHom = R
  p_eq : R ⊔ Pa = P

theorem pre_of_config (hc : Fin812Config A a X Y P Q R V Pa) : Fin812Pre A a X Y P Q R Pa :=
  ⟨hc.pa_max, hc.le_pa, hc.pa_eq, hc.sec8B_eq, hc.q_max, hc.pa_le_normalizer, hc.q_eq,
    hc.r_comm, hc.card_r, hc.r_pow, hc.b_le_r, hc.omega_r, hc.le_q, hc.omega_q, hc.a_not_mem_r,
    hc.r_weak, hc.p_eq⟩

theorem r_le_q (hc : Fin812Pre A a X Y P Q R Pa) : R ≤ Q := hc.q_eq ▸ le_sup_left

theorem pa_le_normalizer_r (hc : Fin812Pre A a X Y P Q R Pa) :
    Pa ≤ Subgroup.normalizer (R : Set G) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply hc.r_weak p
  rintro _ ⟨r, hr, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hc.pa_le_normalizer hp) r).mp (r_le_q hc hr)

theorem isPGroup_p (hc : Fin812Pre A a X Y P Q R Pa) : IsPGroup 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hc.pa_max.2.1
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (pa_le_normalizer_r hc)
  rw [hc.p_eq, hc.card_r, hk, ← pow_add] at h1
  have hdvd : Nat.card P ∣ 3 ^ (6 + k) := h1 ▸ dvd_mul_right _ _
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact IsPGroup.of_card hm

theorem pa_le_p (hc : Fin812Pre A a X Y P Q R Pa) : Pa ≤ P := hc.p_eq ▸ le_sup_right

theorem r_le_p (hc : Fin812Pre A a X Y P Q R Pa) : R ≤ P := hc.p_eq ▸ le_sup_left

theorem a_mem_q (hc : Fin812Pre A a X Y P Q R Pa) : a ∈ Q :=
  hc.q_eq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers a)

theorem r_le_v (hc : Fin812Config A a X Y P Q R V Pa) : R ≤ V := hc.v_eq ▸ le_sup_left

theorem p_inf_y_le_v (hc : Fin812Config A a X Y P Q R V Pa) : P ⊓ Y ≤ V :=
  hc.v_eq ▸ le_sup_right

theorem v_le_p (hc : Fin812Config A a X Y P Q R V Pa) : V ≤ P :=
  hc.v_eq ▸ sup_le (r_le_p (pre_of_config hc)) inf_le_left

theorem b_le_a : sec8B A X ≤ A := by
  unfold sec8B
  exact inf_le_left

theorem b_le_y (hc : Fin812Pre A a X Y P Q R Pa) : sec8B A X ≤ Y :=
  hc.sec8B_eq ▸ inf_le_right

theorem commute_of_mem_q (hc : Fin812Pre A a X Y P Q R Pa) {x y : G} (hx : x ∈ Q)
    (hy : y ∈ sec8B A X) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (hc.q_max.1 hx) y hy).symm

theorem mem_pa_of_commute (hc : Fin812Pre A a X Y P Q R Pa) {x : G} (hx : x ∈ P)
    (hxa : x * a = a * x) : x ∈ Pa := by
  have hS : IsPGroup 3 (P ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) :=
    (isPGroup_p hc).to_le inf_le_left
  have heq := hc.pa_max.2.2 _ hS (le_inf (pa_le_p hc) hc.pa_max.1) inf_le_right
  rw [← heq]
  exact ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxa⟩

theorem p_inf_y_le_pa (hc : Fin812Pre A a X Y P Q R Pa)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) : P ⊓ Y ≤ Pa := fun _ hx =>
  mem_pa_of_commute hc hx.1 (Subgroup.mem_centralizer_singleton_iff.mp (hYa hx.2))

theorem exists_eq_zpow_mul_of_mem_pa (hc : Fin812Pre A a X Y P Q R Pa)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {x : G} (hx : x ∈ Pa) :
    ∃ (i : ℤ) (y : G), y ∈ Pa ⊓ Y ∧ x = a ^ i * y := by
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left
      (show Commute a v from (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm) i).eq
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hx' : x ∈ ((Subgroup.zpowers a ⊔ (Pa ⊓ Y) : Subgroup G) : Set G) := by
    rw [hc.pa_eq]
    exact hx
  rw [hset] at hx'
  obtain ⟨u, hu, v, hv, huv⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨i, v, hv, huv.symm⟩

theorem conj_mem_r (hc : Fin812Pre A a X Y P Q R Pa) {q r : G} (hq : q ∈ Q)
    (hr : r ∈ R) : q * r * q⁻¹ ∈ R := by
  have hle : R.map (MulAut.conj q).toMonoidHom ≤ Q := by
    rintro _ ⟨s, hs, rfl⟩
    exact Q.mul_mem (Q.mul_mem hq (r_le_q hc hs)) (Q.inv_mem hq)
  rw [← hc.r_weak q hle]
  exact ⟨r, hr, rfl⟩

theorem zpowers_le_normalizer_r (hc : Fin812Pre A a X Y P Q R Pa) :
    Subgroup.zpowers a ≤ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨conj_mem_r hc (a_mem_q hc), fun h => ?_⟩
  have := conj_mem_r hc (Q.inv_mem (a_mem_q hc)) h
  simpa [mul_assoc] using this

theorem mem_b_of_mem_a_of_mem_r (hc : Fin812Pre A a X Y P Q R Pa)
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) {x : G} (hxA : x ∈ A) (hxR : x ∈ R) :
    x ∈ sec8B A X :=
  hc.omega_r x hxR (hAab.2 x hxA)

theorem exists_eq_zpow_mul_of_mem_a (hc : Fin812Pre A a X Y P Q R Pa)
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A) {x : G} (hx : x ∈ A) :
    ∃ (i : ℤ) (y : G), y ∈ sec8B A X ∧ x = a ^ i * y := by
  have hx' : x ∈ ((R ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [hc.q_eq]
    exact hc.le_q hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R _ (zpowers_le_normalizer_r hc)] at hx'
  obtain ⟨r, hr, u, hu, hru⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have hrA : r ∈ A := by
    have : r = x * (a ^ i)⁻¹ := by rw [← hru]; group
    rw [this]
    exact A.mul_mem hx (A.inv_mem (A.zpow_mem haA i))
  have hrB := mem_b_of_mem_a_of_mem_r hc hAab hrA hr
  refine ⟨i, r, hrB, ?_⟩
  rw [← hru]
  exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨r, hrA⟩ ⟨a ^ i, A.zpow_mem haA i⟩)

theorem a_not_mem_b (hc : Fin812Pre A a X Y P Q R Pa) : a ∉ sec8B A X := fun h =>
  hc.a_not_mem_r (hc.b_le_r h)

theorem card_b (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81) : Nat.card (sec8B A X) = 27 := by
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ sec8B A X, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨a ^ i, A.zpow_mem haA i⟩ ⟨v, b_le_a hv⟩)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  have hsup : Subgroup.zpowers a ⊔ sec8B A X = A := by
    refine le_antisymm (sup_le ((Subgroup.zpowers_le).mpr haA) b_le_a) fun x hx => ?_
    obtain ⟨i, y, hy, rfl⟩ := exists_eq_zpow_mul_of_mem_a hc hAab haA hx
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers a i) hy
  have hinf : Subgroup.zpowers a ⊓ sec8B A X = ⊥ := by
    have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hdvd : Nat.card (Subgroup.zpowers a ⊓ sec8B A X : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ sec8B A X ≤ _)
      rwa [Nat.card_zpowers, hao] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers a ⊓ sec8B A X = Subgroup.zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hao])
      have : a ∈ Subgroup.zpowers a ⊓ sec8B A X := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact a_not_mem_b hc this.2
  rw [hsup, hinf, Subgroup.card_bot, mul_one, hA81, Nat.card_zpowers,
    orderOf_eq_prime ha3 ha1] at hcard
  omega

theorem a_not_mem_v (hc : Fin812Config A a X Y P Q R V Pa) : a ∉ V := by
  intro haV
  have hPV : P ≤ V := by
    rw [← hc.p_eq]
    refine sup_le (r_le_v hc) ?_
    rw [← hc.pa_eq]
    refine sup_le ((Subgroup.zpowers_le).mpr haV) ?_
    intro y hy
    exact p_inf_y_le_v hc ⟨pa_le_p (pre_of_config hc) hy.1, hy.2⟩
  have h1 := Subgroup.card_le_of_le hPV
  have h2 : 0 < Nat.card V := Nat.card_pos
  rw [hc.card_p] at h1
  omega

end Config

omit [Finite G] in
theorem zpow_eq_one_of_mem {V : Subgroup G} {a : G} (ha3 : a ^ 3 = 1) (haV : a ∉ V) {i : ℤ}
    (h : a ^ i ∈ V) : a ^ i = 1 := by
  have hk : a ^ i = a ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
  rw [hk] at h ⊢
  obtain h0 | h1 | h2 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  · rw [h0, zpow_zero]
  · rw [h1, zpow_one] at h
    exact absurd h haV
  · rw [h2] at h
    refine absurd ?_ haV
    have e : a = (a ^ (2 : ℤ)) ^ (2 : ℤ) * (a ^ 3)⁻¹ := by group
    rw [e, ha3, inv_one, mul_one]
    exact V.zpow_mem h 2

section Trans

variable {A : Subgroup G} {a : G} {X Y P Q R V Pa : Subgroup G}

theorem mem_b_of_mem_r_of_commute (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {r : G} (hr : r ∈ R) (hra : r * a = a * r) :
    r ∈ sec8B A X := by
  have hrPa := mem_pa_of_commute hc (r_le_p hc hr) hra
  obtain ⟨i, y, hy, rfl⟩ := exists_eq_zpow_mul_of_mem_pa hc hYa hrPa
  have hyB : ∀ x ∈ sec8B A X, y * x = x * y := by
    intro x hx
    have h1 : a ^ i * y * x = x * (a ^ i * y) := commute_of_mem_q hc (r_le_q hc hr) hx
    have h2 : a ^ i * x = x * a ^ i := congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨a ^ i, A.zpow_mem haA i⟩ ⟨x, b_le_a hx⟩)
    calc y * x = (a ^ i)⁻¹ * (a ^ i * y * x) := by group
      _ = (a ^ i)⁻¹ * (x * (a ^ i * y)) := by rw [h1]
      _ = (a ^ i)⁻¹ * (x * a ^ i) * y := by group
      _ = (a ^ i)⁻¹ * (a ^ i * x) * y := by rw [h2]
      _ = x * y := by group
  obtain ⟨k, hk⟩ := hc.pa_max.2.1 ⟨y, hy.1⟩
  have hyk : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyB' := mem_of_forall_commute hW hY (b_le_y hc) (isElemAbelian_of_le hAab b_le_a)
    (card_b hc hAab haA ha1 hA81) hy.2 hyk hyB
  exact mem_b_of_mem_a_of_mem_r hc hAab (A.mul_mem (A.zpow_mem haA i) (b_le_a hyB')) hr

theorem exists_conj_eq_mul (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {x : G} (hx : x ∈ sec8B A X) :
    ∃ r ∈ R, r * a * r⁻¹ = x * a := by
  classical
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hmemB : ∀ r ∈ R, r * a * r⁻¹ * a⁻¹ ∈ sec8B A X := by
    intro r hr
    have h1 : r * a * r⁻¹ * a⁻¹ ∈ R := by
      have : r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) := by group
      rw [this]
      exact R.mul_mem hr (conj_mem_r hc (a_mem_q hc) (R.inv_mem hr))
    have h2 : r * a * r⁻¹ ∈ A := by
      refine hc.omega_q _ (Q.mul_mem (Q.mul_mem (r_le_q hc hr) (a_mem_q hc))
        (Q.inv_mem (r_le_q hc hr))) ?_
      rw [conj_pow, ha3]
      group
    exact mem_b_of_mem_a_of_mem_r hc hAab (A.mul_mem h2 (A.inv_mem haA)) h1
  have hcB : ∀ u ∈ sec8B A X, ∀ v ∈ sec8B A X, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨u, b_le_a hu⟩ ⟨v, b_le_a hv⟩)
  let f : R →* sec8B A X :=
    { toFun := fun r => ⟨(r : G) * a * (r : G)⁻¹ * a⁻¹, hmemB r r.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro r s
        apply Subtype.ext
        show ((r * s : R) : G) * a * ((r * s : R) : G)⁻¹ * a⁻¹ =
          ((r : G) * a * (r : G)⁻¹ * a⁻¹) * ((s : G) * a * (s : G)⁻¹ * a⁻¹)
        rw [Subgroup.coe_mul]
        have hds := hmemB s s.2
        have hdr := hmemB r r.2
        set u : G := (r : G) with hu
        set v : G := (s : G) with hv
        have h1 : u * (v * a * v⁻¹ * a⁻¹) = (v * a * v⁻¹ * a⁻¹) * u :=
          commute_of_mem_q hc (r_le_q hc r.2) hds
        calc u * v * a * (u * v)⁻¹ * a⁻¹ = u * (v * a * v⁻¹ * a⁻¹) * a * u⁻¹ * a⁻¹ := by group
          _ = (v * a * v⁻¹ * a⁻¹) * u * a * u⁻¹ * a⁻¹ := by rw [h1]
          _ = (v * a * v⁻¹ * a⁻¹) * (u * a * u⁻¹ * a⁻¹) := by group
          _ = (u * a * u⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹) := (hcB _ hdr _ hds).symm }
  have hB27 := card_b hc hAab haA ha1 hA81
  have hker : Nat.card f.ker ≤ Nat.card R / Nat.card (sec8B A X) := by
    rw [hc.card_r, hB27]
    have hmemK : ∀ u : f.ker, ((u : R) : G) ∈ sec8B A X := by
      intro u
      have hu : f u = 1 := u.2
      have hu' : ((u : R) : G) * a * ((u : R) : G)⁻¹ * a⁻¹ = 1 := congrArg Subtype.val hu
      refine mem_b_of_mem_r_of_commute hW hY hc hAab haA ha1 hA81 hYa (u : R).2 ?_
      calc ((u : R) : G) * a = ((u : R) : G) * a * ((u : R) : G)⁻¹ * a⁻¹ * (a * (u : R)) := by
            group
        _ = a * (u : R) := by rw [hu', one_mul]
    have h1 : Nat.card f.ker ≤ Nat.card (sec8B A X) :=
      Nat.card_le_card_of_injective (fun u => (⟨((u : R) : G), hmemK u⟩ : sec8B A X))
        (fun u v huv => by
          have h2 := congrArg Subtype.val huv
          simp only at h2
          exact Subtype.ext (Subtype.ext h2))
    rw [hB27] at h1
    norm_num
    exact h1
  obtain ⟨r, hr⟩ := MonoidHom.surjective_of_card_ker_le_div f hker ⟨x, hx⟩
  refine ⟨r, r.2, ?_⟩
  have h1 : (r : G) * a * (r : G)⁻¹ * a⁻¹ = x := congrArg Subtype.val hr
  calc (r : G) * a * (r : G)⁻¹ = (r * a * (r : G)⁻¹ * a⁻¹) * a := by group
    _ = x * a := by rw [h1]

theorem exists_conj_eq_zpow (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {y : G} (hyA : y ∈ A)
    (hyB : y ∉ sec8B A X) : ∃ r ∈ R, ∃ k : ℤ, y = r * a ^ k * r⁻¹ := by
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  obtain ⟨i, x, hx, rfl⟩ := exists_eq_zpow_mul_of_mem_a hc hAab haA hyA
  have hk : a ^ i = a ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
  have hxa : x * a = a * x := congrArg Subtype.val
    (hAab.1.is_comm.comm ⟨x, b_le_a hx⟩ ⟨a, haA⟩)
  rw [hk]
  rw [hk] at hyB
  obtain h0 | h1 | h2 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  · rw [h0, zpow_zero, one_mul] at hyB
    exact absurd hx hyB
  · obtain ⟨r, hr, hra⟩ := exists_conj_eq_mul hW hY hc hAab haA ha1 hA81 hYa hx
    refine ⟨r, hr, 1, ?_⟩
    rw [h1, zpow_one, hra, hxa]
  · obtain ⟨r, hr, hra⟩ := exists_conj_eq_mul hW hY hc hAab haA ha1 hA81 hYa
      ((sec8B A X).inv_mem hx)
    refine ⟨r, hr, -1, ?_⟩
    have e1 : r * a ^ (-1 : ℤ) * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
    rw [h2, e1, hra]
    have e2 : a ^ (2 : ℤ) = a⁻¹ := by
      have : a ^ (2 : ℤ) = a⁻¹ * a ^ 3 := by group
      rw [this, ha3, mul_one]
    rw [e2]
    group

end Trans

section NormImage

variable {B : Subgroup G} {p : G}

@[expose] noncomputable def conjInvHom (hpN : p ∈ Subgroup.normalizer (B : Set G)) : B →* B where
  toFun u := ⟨p⁻¹ * u * p, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hpN) u).mp u.2
    simpa using this⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

omit [Finite G] in
theorem conjInvHom_apply (hpN : p ∈ Subgroup.normalizer (B : Set G)) (u : B) :
    ((conjInvHom hpN u : B) : G) = p⁻¹ * u * p := rfl

theorem exists_mul_conj_inv_eq_of_norm (hBab : CFSG.Assembly.IsElemAbelian 3 B)
    (hB27 : Nat.card B = 27) (hpN : p ∈ Subgroup.normalizer (B : Set G))
    (hp3 : ∀ u ∈ B, p ^ 3 * u = u * p ^ 3)
    (hcent : Nat.card (B ⊓ Subgroup.centralizer {p} : Subgroup G) ≤ 3) {u : G} (hu : u ∈ B)
    (hN : u * (p⁻¹ * u * p) * (p⁻¹ * (p⁻¹ * u * p) * p) = 1) :
    ∃ v ∈ B, u = v * (p⁻¹ * v * p)⁻¹ := by
  classical
  have hc : ∀ x y : B, x * y = y * x := fun x y => hBab.1.is_comm.comm x y
  let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := hc }
  set T := conjInvHom hpN with hT
  have hT3 : ∀ v : B, T (T (T v)) = v := by
    intro v
    apply Subtype.ext
    simp only [hT, conjInvHom_apply]
    have h : (p * p * p) * (v : G) = v * (p * p * p) := by
      simpa [pow_three, mul_assoc] using hp3 v v.2
    calc p⁻¹ * (p⁻¹ * (p⁻¹ * (v : G) * p) * p) * p =
        (p * p * p)⁻¹ * ((v : G) * (p * p * p)) := by group
      _ = (p * p * p)⁻¹ * ((p * p * p) * v) := by rw [h]
      _ = v := by group
  have hexp : ∀ v : B, v ^ 3 = 1 := fun v => Subtype.ext (by simpa using hBab.2 v v.2)
  have key : ∀ x y z : B, x * y⁻¹ * (y * z⁻¹)⁻¹ = x * y * z * (y ^ 3)⁻¹ := by
    intro x y z
    have h1 : y⁻¹ * z = z * y⁻¹ := hc _ _
    have h2 : y * z = z * y := hc _ _
    calc x * y⁻¹ * (y * z⁻¹)⁻¹ = x * (y⁻¹ * z) * y⁻¹ := by group
      _ = x * (z * y⁻¹) * y⁻¹ := by rw [h1]
      _ = x * (z * y) * (y ^ 3)⁻¹ := by group
      _ = x * (y * z) * (y ^ 3)⁻¹ := by rw [h2]
      _ = x * y * z * (y ^ 3)⁻¹ := by group
  set ψ : B →* B := MonoidHom.id B / T with hψdef
  set Nm : B →* B := MonoidHom.id B * T * T.comp T with hNmdef
  have hψ : ∀ v, ψ v = v * (T v)⁻¹ := fun v => by
    simp [hψdef, div_eq_mul_inv]
  have hNm : ∀ v, Nm v = v * T v * T (T v) := fun v => by
    simp [hNmdef]
  have hker : Nat.card ψ.ker ≤ 3 := by
    have hmem : ∀ v : ψ.ker, ((v : B) : G) ∈ (B ⊓ Subgroup.centralizer {p} : Subgroup G) := by
      intro v
      have hv : ψ (v : B) = 1 := v.2
      rw [hψ, mul_inv_eq_one] at hv
      have hv' : p⁻¹ * ((v : B) : G) * p = (v : B) := congrArg Subtype.val hv.symm
      refine Subgroup.mem_inf.mpr ⟨(v : B).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc ((v : B) : G) * p = p * (p⁻¹ * ((v : B) : G) * p) := by group
        _ = p * (v : B) := by rw [hv']
    refine le_trans (Nat.card_le_card_of_injective (fun v => ⟨_, hmem v⟩) ?_) hcent
    intro v w hvw
    have h2 := congrArg Subtype.val hvw
    simp only at h2
    exact Subtype.ext (Subtype.ext h2)
  have hprod : Nat.card ψ.ker * Nat.card ψ.range = 27 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hB27]
  have hrange : 9 ≤ Nat.card ψ.range := by
    by_contra hlt
    have h1 : Nat.card ψ.ker * Nat.card ψ.range ≤ 3 * 8 := Nat.mul_le_mul hker (by omega)
    omega
  have hle : ψ.range ≤ Nm.ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker, hNm, hψ]
    simp only [map_mul, map_inv]
    rw [hT3]
    group
  have hNne : Nm.ker ≠ ⊤ := by
    intro htop
    have hψψ : ∀ v, ψ (ψ v) = 1 := by
      intro v
      have h1 : v ∈ Nm.ker := by
        rw [htop]
        exact Subgroup.mem_top v
      rw [MonoidHom.mem_ker, hNm] at h1
      rw [hψ, hψ, map_mul, map_inv, key, h1, hexp, inv_one, one_mul]
    have hrk : ψ.range ≤ ψ.ker := by
      rintro _ ⟨v, rfl⟩
      exact hψψ v
    have := Subgroup.card_le_of_le hrk
    omega
  have hNcard : Nat.card Nm.ker ≤ 9 := by
    have hdvd : Nat.card Nm.ker ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hB27]
      exact Subgroup.card_subgroup_dvd_card Nm.ker
    have hne : Nat.card Nm.ker ≠ 27 := by
      intro h27
      exact hNne (Subgroup.eq_top_of_card_eq _ (by rw [h27, hB27]))
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk3 : k ≠ 3 := fun h3 => hne (by rw [hk', h3]; norm_num)
    rw [hk']
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  have heq : ψ.range = Nm.ker := Subgroup.eq_of_le_of_card_ge hle (by omega)
  have huN : (⟨u, hu⟩ : B) ∈ Nm.ker := by
    rw [MonoidHom.mem_ker, hNm]
    apply Subtype.ext
    simpa [hT, conjInvHom_apply] using hN
  rw [← heq] at huN
  obtain ⟨v, hv⟩ := huN
  refine ⟨v, v.2, ?_⟩
  have h2 := congrArg Subtype.val hv
  rw [hψ] at h2
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hT, conjInvHom_apply] at h2
  exact h2.symm

end NormImage

section Cubes

variable {R B : Subgroup G}

theorem exists_pow_three_eq (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x)
    (hR : Nat.card R = 3 ^ 6) (hR9 : ∀ x ∈ R, x ^ 9 = 1)
    (hΩ : ∀ x ∈ R, x ^ 3 = 1 → x ∈ B) (hB27 : Nat.card B = 27) {v : G} (hv : v ∈ B) :
    ∃ r ∈ R, r ^ 3 = v := by
  classical
  have hmem : ∀ r ∈ R, r ^ 3 ∈ B := fun r hr =>
    hΩ _ (R.pow_mem hr 3) (by rw [← pow_mul]; exact hR9 r hr)
  let κ : R →* B :=
    { toFun := fun r => ⟨(r : G) ^ 3, hmem r r.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro r s
        apply Subtype.ext
        show ((r * s : R) : G) ^ 3 = (r : G) ^ 3 * (s : G) ^ 3
        rw [Subgroup.coe_mul]
        exact (Commute.mul_pow (hRc r r.2 s s.2) 3) }
  have hker : Nat.card κ.ker ≤ Nat.card R / Nat.card B := by
    rw [hR, hB27]
    have h1 : Nat.card κ.ker ≤ Nat.card B := by
      refine Nat.card_le_card_of_injective
        (fun r : κ.ker => (⟨((r : R) : G), hΩ _ (r : R).2 ?_⟩ : B)) ?_
      · have := congrArg Subtype.val r.2
        simpa [κ] using this
      · intro r s hrs
        have h2 := congrArg Subtype.val hrs
        simp only at h2
        exact Subtype.ext (Subtype.ext h2)
    rw [hB27] at h1
    norm_num
    exact h1
  obtain ⟨r, hr⟩ := MonoidHom.surjective_of_card_ker_le_div κ hker ⟨v, hv⟩
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

theorem card_le_nine_of_omega {C : Subgroup G} (hCc : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hC9 : ∀ x ∈ C, x ^ 9 = 1) {D : Subgroup G} (hD : Nat.card D ≤ 3)
    (hΩ : ∀ x ∈ C, x ^ 3 = 1 → x ∈ D) : Nat.card C ≤ 9 := by
  classical
  let κ : C →* C :=
    { toFun := fun r => r ^ 3
      map_one' := by simp
      map_mul' := by
        intro r s
        exact (Commute.mul_pow (Subtype.ext (hCc r r.2 s s.2)) 3) }
  have hκ : ∀ r, κ r = r ^ 3 := fun r => rfl
  have hD' : ∀ S : Subgroup C, (∀ x ∈ S, x ^ 3 = 1) → Nat.card S ≤ 3 := by
    intro S hS
    refine le_trans (Nat.card_le_card_of_injective
      (fun x : S => (⟨((x : C) : G), hΩ _ (x : C).2 ?_⟩ : D)) ?_) hD
    · have := congrArg Subtype.val (hS x x.2)
      simpa using this
    · intro x y hxy
      have h2 := congrArg Subtype.val hxy
      simp only at h2
      exact Subtype.ext (Subtype.ext h2)
  have h1 : Nat.card κ.ker ≤ 3 := hD' _ fun x hx => by
    have : κ x = 1 := hx
    rwa [hκ] at this
  have h2 : Nat.card κ.range ≤ 3 := hD' _ fun x hx => by
    obtain ⟨r, rfl⟩ := hx
    rw [hκ, ← pow_mul]
    exact Subtype.ext (by simpa using hC9 r r.2)
  have h3 : Nat.card κ.ker * Nat.card κ.range = Nat.card C := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [← h3]
  calc Nat.card κ.ker * Nat.card κ.range ≤ 3 * 3 := Nat.mul_le_mul h1 h2
    _ = 9 := by norm_num

end Cubes

section PaY

omit [Finite G] in
theorem pow_three_mem_of_card_le {S B : Subgroup G} (hS : IsPGroup 3 S) (hBS : B ≤ S)
    (hN : S ≤ Subgroup.normalizer (B : Set G)) (hcard : Nat.card S ≤ 3 * Nat.card B)
    (hSfin : Nat.card S ≠ 0) {x : G} (hx : x ∈ S) : x ^ 3 ∈ B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite S := Nat.finite_of_card_ne_zero hSfin
  set B' := B.subgroupOf S with hB'
  have hB'n : B'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hN g.2) n).mp hn
    simpa using this⟩
  have hB'card : Nat.card B' = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv
  have hQ := Subgroup.card_eq_card_quotient_mul_card_subgroup B'
  rw [hB'card] at hQ
  have hBpos : 0 < Nat.card B := by
    have : Finite B := Finite.of_injective _ (Subgroup.inclusion_injective hBS)
    exact Nat.card_pos
  have hle : Nat.card (S ⧸ B') ≤ 3 := by
    by_contra hlt
    have h4 : 4 * Nat.card B ≤ Nat.card (S ⧸ B') * Nat.card B :=
      Nat.mul_le_mul_right _ (by omega)
    have h6 : Nat.card (S ⧸ B') * Nat.card B ≤ 3 * Nat.card B := hQ ▸ hcard
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  have hdvd : Nat.card (S ⧸ B') ∣ 3 ^ k := by
    rw [← hk, hQ]
    exact dvd_mul_right _ _
  obtain ⟨j, -, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hj1 : j ≤ 1 := by
    by_contra hj
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hQ3 : Nat.card (S ⧸ B') ∣ 3 := by
    rw [hj']
    interval_cases j <;> norm_num
  have h1 : ((⟨x, hx⟩ : S) : S ⧸ B') ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hQ3)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  simpa using h1

end PaY

section Fusion

variable {A : Subgroup G} {a : G} {X Y P Q R V Pa : Subgroup G}

theorem p_le_normalizer_r (hc : Fin812Pre A a X Y P Q R Pa) :
    P ≤ Subgroup.normalizer (R : Set G) :=
  hc.p_eq ▸ sup_le Subgroup.le_normalizer (pa_le_normalizer_r hc)

theorem exists_eq_mul_of_mem_p (hc : Fin812Pre A a X Y P Q R Pa) {z : G} (hz : z ∈ P) :
    ∃ r ∈ R, ∃ p ∈ Pa, z = r * p := by
  have hz' : z ∈ ((R ⊔ Pa : Subgroup G) : Set G) := by
    rw [hc.p_eq]
    exact hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R Pa (pa_le_normalizer_r hc)] at hz'
  obtain ⟨r, hr, p, hp, hrp⟩ := hz'
  exact ⟨r, hr, p, hp, hrp.symm⟩

theorem b_le_pa_inf_y (hc : Fin812Pre A a X Y P Q R Pa) : sec8B A X ≤ Pa ⊓ Y :=
  le_inf (b_le_a.trans hc.le_pa) (b_le_y hc)

theorem isPGroup_pa_inf_y (hc : Fin812Pre A a X Y P Q R Pa) :
    IsPGroup 3 (Pa ⊓ Y : Subgroup G) :=
  hc.pa_max.2.1.to_le inf_le_left

theorem pa_le_normalizer_b {Y : Subgroup G} (hY : IsYQuot Y) {P Q R Pa : Subgroup G}
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) :
    Pa ≤ Subgroup.normalizer (sec8B A X : Set G) := by
  have hB27 := card_b hc hAab haA ha1 hA81
  have hS81 : Nat.card (Pa ⊓ Y : Subgroup G) ≤ 3 * Nat.card (sec8B A X) := by
    rw [hB27]
    exact (card_le_of_le hY inf_le_right (isPGroup_pa_inf_y hc)).trans (by norm_num)
  have hSN : Pa ⊓ Y ≤ Subgroup.normalizer (sec8B A X : Set G) :=
    le_normalizer_of_card_le (isPGroup_pa_inf_y hc) (b_le_pa_inf_y hc) hS81
  intro p hp
  obtain ⟨i, y, hy, rfl⟩ := exists_eq_zpow_mul_of_mem_pa hc hYa hp
  refine Subgroup.mul_mem _ ?_ (hSN hy)
  refine Item812Res3.mem_normalizer_of_forall_commute fun x hx => ?_
  exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨a ^ i, A.zpow_mem haA i⟩ ⟨x, b_le_a hx⟩)

theorem exists_conj_mem_pa (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {z : G} (hzP : z ∈ P) (hz3 : z ^ 3 = 1) :
    ∃ w ∈ R, w * z * w⁻¹ ∈ Pa := by
  obtain ⟨r, hr, p, hp, rfl⟩ := exists_eq_mul_of_mem_p hc hzP
  obtain ⟨i, y, hy, hpy⟩ := exists_eq_zpow_mul_of_mem_pa hc hYa hp
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hB27 := card_b hc hAab haA ha1 hA81
  have hBab := isElemAbelian_of_le hAab (b_le_a (A := A) (X := X))
  have hRc := hc.r_comm
  by_cases hyB : y ∈ sec8B A X
  · have hpA : p ∈ A := hpy ▸ A.mul_mem (A.zpow_mem haA i) (b_le_a hyB)
    have hzQ : r * p ∈ Q := Q.mul_mem (r_le_q hc hr) (hc.le_q hpA)
    refine ⟨1, R.one_mem, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact hc.le_pa (hc.omega_q _ hzQ hz3)
  have hNB : p ∈ Subgroup.normalizer (sec8B A X : Set G) :=
    pa_le_normalizer_b hY hc hAab haA ha1 hA81 hYa hp
  have hNR : p ∈ Subgroup.normalizer (R : Set G) := pa_le_normalizer_r hc hp
  have hay : Commute a y := (Subgroup.mem_centralizer_singleton_iff.mp (hYa hy.2)).symm
  have hp3 : p ^ 3 = y ^ 3 := by
    rw [hpy, (Commute.zpow_left hay i).mul_pow, ← zpow_natCast (a ^ i), ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, ha3, one_zpow, one_mul]
  have hp3B : p ^ 3 ∈ sec8B A X := by
    rw [hp3]
    refine pow_three_mem_of_card_le (isPGroup_pa_inf_y hc) (b_le_pa_inf_y hc) ?_ ?_
      Nat.card_pos.ne' hy
    · exact fun x hx => pa_le_normalizer_b hY hc hAab haA ha1 hA81 hYa hx.1
    · rw [hB27]
      exact (card_le_of_le hY inf_le_right (isPGroup_pa_inf_y hc)).trans (by norm_num)
  have hcent : Nat.card (sec8B A X ⊓ Subgroup.centralizer {p⁻¹} : Subgroup G) ≤ 3 := by
    refine le_trans (Subgroup.card_le_of_le ?_) (card_inf_centralizer_le hW hY inf_le_right
      (isPGroup_pa_inf_y hc) (b_le_pa_inf_y hc) hBab hB27 hy hyB)
    intro x hx
    obtain ⟨hxB, hxC⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxB, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxC ⊢
    have hxp : x * p = p * x := by
      calc x * p = p * (p⁻¹ * x) * p := by group
        _ = p * (x * p⁻¹) * p := by rw [hxC]
        _ = p * x := by group
    have hxa : x * a ^ i = a ^ i * x := congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨x, b_le_a hxB⟩ ⟨a ^ i, A.zpow_mem haA i⟩)
    rw [hpy] at hxp
    calc x * y = (a ^ i)⁻¹ * (a ^ i * x) * y := by group
      _ = (a ^ i)⁻¹ * (x * a ^ i) * y := by rw [hxa]
      _ = (a ^ i)⁻¹ * (x * (a ^ i * y)) := by group
      _ = (a ^ i)⁻¹ * (a ^ i * y * x) := by rw [hxp]
      _ = y * x := by group
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : G, r₁ = p * r * p⁻¹ := ⟨_, rfl⟩
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ : G, r₂ = p * r₁ * p⁻¹ := ⟨_, rfl⟩
  have hr₁R : r₁ ∈ R := hr₁ ▸ (Subgroup.mem_normalizer_iff.mp hNR r).mp hr
  have hr₂R : r₂ ∈ R := hr₂ ▸ (Subgroup.mem_normalizer_iff.mp hNR r₁).mp hr₁R
  have hz : r * r₁ * r₂ = (p ^ 3)⁻¹ := by
    have e : (r * p) ^ 3 = r * r₁ * r₂ * p ^ 3 := by
      rw [hr₂, hr₁, pow_three, pow_three]
      group
    rw [hz3] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have huB : r ^ 3 ∈ sec8B A X :=
    hc.omega_r _ (R.pow_mem hr 3) (by rw [← pow_mul]; exact hc.r_pow r hr)
  have hNu : r ^ 3 * ((p⁻¹)⁻¹ * r ^ 3 * p⁻¹) *
      ((p⁻¹)⁻¹ * ((p⁻¹)⁻¹ * r ^ 3 * p⁻¹) * p⁻¹) = 1 := by
    simp only [inv_inv]
    have e1 : p * r ^ 3 * p⁻¹ = r₁ ^ 3 := by rw [hr₁, conj_pow]
    have e2 : p * (p * r ^ 3 * p⁻¹) * p⁻¹ = r₂ ^ 3 := by rw [e1, hr₂, conj_pow]
    rw [e2, e1]
    have c1 : Commute r r₁ := hRc r hr r₁ hr₁R
    have c2 : Commute (r * r₁) r₂ := hRc _ (R.mul_mem hr hr₁R) r₂ hr₂R
    rw [← c1.mul_pow, ← c2.mul_pow, hz, inv_pow, hBab.2 _ hp3B, inv_one]
  have hp3c : ∀ x ∈ sec8B A X, p⁻¹ ^ 3 * x = x * p⁻¹ ^ 3 := by
    intro x hx
    have hpB : p⁻¹ ^ 3 ∈ sec8B A X := by
      rw [inv_pow]
      exact (sec8B A X).inv_mem hp3B
    exact congrArg Subtype.val (hBab.1.is_comm.comm ⟨_, hpB⟩ ⟨x, hx⟩)
  obtain ⟨v, hvB, hv⟩ := exists_mul_conj_inv_eq_of_norm hBab hB27
    (Subgroup.inv_mem _ hNB) hp3c hcent huB hNu
  rw [inv_inv] at hv
  obtain ⟨s, hsR, hs⟩ := exists_pow_three_eq hRc hc.card_r hc.r_pow hc.omega_r hB27 hvB
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : G, s₁ = p * s * p⁻¹ := ⟨_, rfl⟩
  have hs₁R : s₁ ∈ R := hs₁ ▸ (Subgroup.mem_normalizer_iff.mp hNR s).mp hsR
  have hr3 : r ^ 3 = (s * s₁⁻¹) ^ 3 := by
    have c : Commute s s₁⁻¹ := hRc s hsR _ (R.inv_mem hs₁R)
    rw [c.mul_pow, inv_pow, hs₁, conj_pow, hs, hv]
  obtain ⟨b, hb⟩ : ∃ b : G, b = r * (s * s₁⁻¹)⁻¹ := ⟨_, rfl⟩
  have hbR : b ∈ R := hb ▸ R.mul_mem hr (R.inv_mem (R.mul_mem hsR (R.inv_mem hs₁R)))
  have hb3 : b ^ 3 = 1 := by
    have c : Commute r (s * s₁⁻¹)⁻¹ :=
      hRc r hr _ (R.inv_mem (R.mul_mem hsR (R.inv_mem hs₁R)))
    rw [hb, c.mul_pow, hr3, inv_pow, mul_inv_cancel]
  have hbB : b ∈ sec8B A X := hc.omega_r b hbR hb3
  have hbs : b * s = s * b := hRc b hbR s hsR
  have hrb : r = b * (s * s₁⁻¹) := by rw [hb]; group
  refine ⟨s⁻¹, R.inv_mem hsR, ?_⟩
  have e : s⁻¹ * (r * p) * s⁻¹⁻¹ = b * p := by
    calc s⁻¹ * (r * p) * s⁻¹⁻¹ = s⁻¹ * (b * s) * p := by rw [hrb, hs₁]; group
      _ = s⁻¹ * (s * b) * p := by rw [hbs]
      _ = b * p := by group
  rw [e]
  exact Pa.mul_mem (hc.le_pa (b_le_a hbB)) hp

theorem r_inf_pa_eq (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) : R ⊓ Pa = sec8B A X := by
  refine le_antisymm (fun r hr => ?_) (le_inf hc.b_le_r (b_le_a.trans hc.le_pa))
  exact mem_b_of_mem_r_of_commute hW hY hc hAab haA ha1 hA81 hYa hr.1
    (Subgroup.mem_centralizer_singleton_iff.mp (hc.pa_max.1 hr.2))

theorem card_pa_le (hc : Fin812Pre A a X Y P Q R Pa) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) :
    Nat.card Pa ≤ 3 * Nat.card (Pa ⊓ Y : Subgroup G) := by
  have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ Pa ⊓ Y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left
      (show Commute a v from (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm)
        j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [hc.pa_eq, Nat.card_zpowers, orderOf_eq_prime ha3 ha1] at hcard
  have hpos : 0 < Nat.card (Subgroup.zpowers a ⊓ (Pa ⊓ Y) : Subgroup G) := Nat.card_pos
  nlinarith

theorem card_p_mul_le (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) : Nat.card P * 27 ≤ Nat.card R * 243 := by
  have hPa := card_pa_le hc (hAab.2 a haA) ha1 hYa
  have hS81 : Nat.card (Pa ⊓ Y : Subgroup G) ≤ 81 :=
    card_le_of_le hY inf_le_right (isPGroup_pa_inf_y hc)
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (pa_le_normalizer_r hc)
  rw [hc.p_eq, r_inf_pa_eq hW hY hc hAab haA ha1 hA81 hYa, card_b hc hAab haA ha1 hA81] at h1
  rw [h1]
  exact Nat.mul_le_mul_left _ (by omega)

theorem card_centralizer_mul_lt (hW : KF812WreathCent) (hY : IsYQuot Y)
    (hc : Fin812Pre A a X Y P Q R Pa) (hAab : CFSG.Assembly.IsElemAbelian 3 A)
    (haA : a ∈ A) (ha1 : a ≠ 1) (hA81 : Nat.card A = 81)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {x : G} (hxPY : x ∈ P ⊓ Y)
    (hxB : x ∉ sec8B A X) :
    Nat.card (P ⊓ Subgroup.centralizer {a * x} : Subgroup G) <
      Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB27 := card_b hc hAab haA ha1 hA81
  have hBab := isElemAbelian_of_le hAab (b_le_a (A := A) (X := X))
  set S := Pa ⊓ Y with hSdef
  have hxS : x ∈ S := ⟨p_inf_y_le_pa hc hYa hxPY, hxPY.2⟩
  have hS81 : Nat.card S ≤ 81 := card_le_of_le hY inf_le_right (isPGroup_pa_inf_y hc)
  have hD := card_inf_centralizer_le hW hY inf_le_right (isPGroup_pa_inf_y hc)
    (b_le_pa_inf_y hc) hBab hB27 hxS hxB
  have hCR : Nat.card (R ⊓ Subgroup.centralizer {a * x} : Subgroup G) ≤ 9 := by
    refine card_le_nine_of_omega (fun u hu v hv => hc.r_comm u hu.1 v hv.1)
      (fun u hu => hc.r_pow u hu.1) hD fun u hu hu3 => ?_
    obtain ⟨huR, huC⟩ := Subgroup.mem_inf.mp hu
    have huB : u ∈ sec8B A X := hc.omega_r u huR hu3
    refine Subgroup.mem_inf.mpr ⟨huB, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at huC ⊢
    have hua : u * a = a * u := congrArg Subtype.val
      (hAab.1.is_comm.comm ⟨u, b_le_a huB⟩ ⟨a, haA⟩)
    calc u * x = a⁻¹ * (a * u) * x := by group
      _ = a⁻¹ * (u * a) * x := by rw [hua]
      _ = a⁻¹ * (u * (a * x)) := by group
      _ = a⁻¹ * (a * x * u) := by rw [huC]
      _ = x * u := by group
  have hP := card_p_mul_le hW hY hc hAab haA ha1 hA81 hYa
  have hC : Nat.card (P ⊓ Subgroup.centralizer {a * x} : Subgroup G) ≤ 81 := by
    set C := P ⊓ Subgroup.centralizer {a * x} with hCdef
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := R) (B := C) (inf_le_left.trans (p_le_normalizer_r hc))
    have h2 : Nat.card (R ⊔ C : Subgroup G) ≤ Nat.card P :=
      Subgroup.card_le_of_le (sup_le (r_le_p hc) inf_le_left)
    have h3 : Nat.card (R ⊓ C : Subgroup G) ≤ 9 :=
      (Subgroup.card_le_of_le (inf_le_inf_left R inf_le_right)).trans hCR
    have hRpos : 0 < Nat.card R := Nat.card_pos
    have h4 : Nat.card R * Nat.card C ≤ Nat.card P * 9 := by
      rw [← h1]
      exact Nat.mul_le_mul h2 h3
    nlinarith
  have hSB : 81 ≤ Nat.card S := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (isPGroup_pa_inf_y hc)
    have hdvd : 3 ^ 3 ∣ 3 ^ m := by
      rw [← hm, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hB27]
      exact Subgroup.card_dvd_of_le (b_le_pa_inf_y hc)
    have hm3 : 3 ≤ m := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    have hm3' : m ≠ 3 := by
      intro h3
      have heq : sec8B A X = S :=
        Subgroup.eq_of_le_of_card_ge (b_le_pa_inf_y hc) (by rw [hm, h3, hB27]; norm_num)
      exact hxB (heq ▸ hxS)
    rw [hm]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have haY : a ∉ Y := fun h => a_not_mem_b hc (hc.sec8B_eq ▸ ⟨haA, h⟩)
  have hPa' : 3 * Nat.card S ≤ Nat.card Pa := by
    have hcomm : ∀ u ∈ Subgroup.zpowers a, ∀ v ∈ S, u * v = v * u := by
      intro u hu v hv
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact (Commute.zpow_left
        (show Commute a v from (Subgroup.mem_centralizer_singleton_iff.mp (hYa hv.2)).symm)
          j).eq
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
    have hinf : Subgroup.zpowers a ⊓ S = ⊥ := by
      have hao : orderOf a = 3 := orderOf_eq_prime (hAab.2 a haA) ha1
      have hdvd : Nat.card (Subgroup.zpowers a ⊓ S : Subgroup G) ∣ 3 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers a ⊓ S ≤ _)
        rwa [Nat.card_zpowers, hao] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have heq : Subgroup.zpowers a ⊓ S = Subgroup.zpowers a :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hao])
        have : a ∈ Subgroup.zpowers a ⊓ S := by
          rw [heq]
          exact Subgroup.mem_zpowers a
        exact haY this.2.2
    rw [hc.pa_eq, hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers,
      orderOf_eq_prime (hAab.2 a haA) ha1] at hcard
    omega
  have hCa : Nat.card Pa ≤ Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf (pa_le_p hc) hc.pa_max.1)
  omega

end Fusion

section Construct

omit [Finite G] in
theorem exists_isMaxPSub_le {C S : Subgroup G} (hS : IsPGroup 3 S) (hSC : S ≤ C) :
    ∃ P : Subgroup G, Item812Res3.IsMaxPSub 3 P C ∧ S ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, hT⟩ := (hS.comap_of_injective C.subtype C.subtype_injective).exists_le_sylow
  refine ⟨(T : Subgroup C).map C.subtype, ⟨Subgroup.map_subtype_le _, T.isPGroup'.map _, ?_⟩, ?_⟩
  · intro U hU hTU hUC
    have h1 : IsPGroup 3 (U.comap C.subtype) := hU.comap_of_injective _ C.subtype_injective
    have h2 : (T : Subgroup C) ≤ U.comap C.subtype := fun x hx =>
      Subgroup.mem_comap.mpr (hTU ⟨x, hx, rfl⟩)
    have h3 := T.is_maximal' h1 h2
    refine le_antisymm (fun u hu => ?_) hTU
    have : (⟨u, hUC hu⟩ : C) ∈ U.comap C.subtype := Subgroup.mem_comap.mpr hu
    rw [h3] at this
    exact ⟨_, this, rfl⟩
  · intro s hs
    exact ⟨⟨s, hSC hs⟩, hT (Subgroup.mem_comap.mpr hs), rfl⟩

theorem isPGroup_sup {S T : Subgroup G} (hS : IsPGroup 3 S) (hT : IsPGroup 3 T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) : IsPGroup 3 (S ⊔ T : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT
  have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hTS
  rw [hk, hm, ← pow_add] at h1
  have hdvd : Nat.card (S ⊔ T : Subgroup G) ∣ 3 ^ (k + m) := h1 ▸ dvd_mul_right _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  exact IsPGroup.of_card hj

omit [Finite G] in
theorem commute_of_mem_normalizer_zpowers {a k : G} (ha3 : a ^ 3 = 1) {m : ℕ}
    (hk : k ^ 3 ^ m = 1) (hN : k ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
    k * a = a * k := by
  have hka : k * a * k⁻¹ ∈ Subgroup.zpowers a :=
    (Subgroup.mem_normalizer_iff.mp hN a).mp (Subgroup.mem_zpowers a)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hka
  have hjmod : a ^ j = a ^ (j % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, ha3, one_zpow, mul_one]
  rw [hjmod] at hj
  obtain h0 | h1 | h2 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  · rw [h0, zpow_zero] at hj
    have : a = 1 := by
      have e : a = k⁻¹ * (k * a * k⁻¹) * k := by group
      rw [e, ← hj]
      group
    rw [this, mul_one, one_mul]
  · rw [h1, zpow_one] at hj
    calc k * a = k * a * k⁻¹ * k := by group
      _ = a * k := by rw [← hj]
  · rw [h2] at hj
    have hinv : k * a * k⁻¹ = a⁻¹ := by
      rw [← hj]
      have : a ^ (2 : ℤ) = a⁻¹ * a ^ 3 := by group
      rw [this, ha3, mul_one]
    have hk2 : k ^ 2 * a = a * k ^ 2 := by
      have e : k ^ 2 * a * (k ^ 2)⁻¹ = k * (k * a * k⁻¹) * k⁻¹ := by
        rw [sq]
        group
      have e2 : k ^ 2 * a * (k ^ 2)⁻¹ = a := by
        rw [e, hinv]
        have : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
        rw [this, hinv, inv_inv]
      calc k ^ 2 * a = k ^ 2 * a * (k ^ 2)⁻¹ * k ^ 2 := by group
        _ = a * k ^ 2 := by rw [e2]
    obtain ⟨t, ht⟩ : ∃ t, 3 ^ m + 1 = 2 * t := by
      obtain ⟨u, hu⟩ : Odd (3 ^ m) := Odd.pow (by decide)
      exact ⟨u + 1, by omega⟩
    have hkt : k = (k ^ 2) ^ t := by
      rw [← pow_mul, ← ht, pow_succ, hk, one_mul]
    rw [hkt]
    exact ((Commute.pow_left (show Commute (k ^ 2) a from hk2) t)).eq

theorem not_mem_of_mem_thetaComponentsAt {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a) (hYq : IsYQuot Y) : a ∉ Y := by
  intro haY
  have hYa := le_centralizer_of_mem_thetaComponentsAt_three hY
  have hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
    rcases hYq with h9 | h6
    · obtain ⟨e⟩ := h9
      exact (Item812Res3.IsYModel.of_mulEquiv e.symm
        Item812Res3.isYModel_alternatingGroup_nine).1
    · obtain ⟨e⟩ := h6
      exact (Item812Res3.IsYModel.of_mulEquiv e.symm Item812Res3.isYModel_projSp_three_two).1
  have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) (⟨a, haY⟩ : Y) ∈
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [Subgroup.mem_center_iff]
    intro w
    induction w using QuotientGroup.induction_on with
    | H w =>
      change QuotientGroup.mk' (aschbacherSolvableCore 3 Y) w *
          QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨a, haY⟩ =
        QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨a, haY⟩ *
          QuotientGroup.mk' (aschbacherSolvableCore 3 Y) w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYa w.2)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
  have h31 : (⟨a, haY⟩ : Y) ^ 3 ^ 1 = 1 := Subtype.ext (by simpa using ha3)
  have h2 := KFacts.eq_one_of_pow_three_pow_eq_one (not_dvd_card_core Y) hcen h31
  exact ha1 (by simpa using congrArg Subtype.val h2)

theorem exists_isMaxPSub_normalized {C P : Subgroup G} (hP : IsPGroup 3 P)
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) :
    ∃ Q : Subgroup G, Item812Res3.IsMaxPSub 3 Q C ∧ P ≤ Subgroup.normalizer (Q : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : P →* MulAut C := C.normalizerMonoidHom.comp (Subgroup.inclusion hPC)
  let _ : MulDistribMulAction P C := MulDistribMulAction.compHom C φ
  have hcard : ¬ 3 ∣ Nat.card (Sylow 3 C) := by
    intro h
    have h1 := card_sylow_modEq_one 3 C
    have h2 := Nat.mod_eq_zero_of_dvd h
    unfold Nat.ModEq at h1
    omega
  obtain ⟨S, hS⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 C) hcard
  have hSinv : ∀ e : P, ∀ s ∈ (S : Subgroup C), e • s ∈ (S : Subgroup C) := by
    intro e s hs
    have hmem : e • s ∈ ((e • S : Sylow 3 C) : Subgroup C) := by
      rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
      exact ⟨s, hs, rfl⟩
    rwa [hS e] at hmem
  have hconj : ∀ e ∈ P, ∀ t ∈ (S : Subgroup C).map C.subtype,
      e * t * e⁻¹ ∈ (S : Subgroup C).map C.subtype := by
    rintro e he _ ⟨s, hs, rfl⟩
    exact ⟨_, hSinv ⟨e, he⟩ s hs, rfl⟩
  refine ⟨(S : Subgroup C).map C.subtype,
    ⟨Subgroup.map_subtype_le _, S.isPGroup'.map _, ?_⟩, fun e he => ?_⟩
  · intro U hU hSU hUC
    have h1 : IsPGroup 3 (U.comap C.subtype) := hU.comap_of_injective _ C.subtype_injective
    have h2 : (S : Subgroup C) ≤ U.comap C.subtype := fun x hx =>
      Subgroup.mem_comap.mpr (hSU ⟨x, hx, rfl⟩)
    have h3 := S.is_maximal' h1 h2
    refine le_antisymm (fun u hu => ?_) hSU
    have : (⟨u, hUC hu⟩ : C) ∈ U.comap C.subtype := Subgroup.mem_comap.mpr hu
    rw [h3] at this
    exact ⟨_, this, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨hconj e he t, fun ht => ?_⟩
    have := hconj e⁻¹ (P.inv_mem he) _ ht
    simpa [mul_assoc] using this

omit [Finite G] in
theorem mem_normalizer_centralizer {B : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (B : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hh x hx
    have hx' : g⁻¹ * x * g ∈ B := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hh _ hx'
    calc x * (g * h * g⁻¹) = g * ((g⁻¹ * x * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * x := by group
  · intro hh x hx
    have hx' : g * x * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h1 := hh _ hx'
    calc x * h = g⁻¹ * ((g * x * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = h * x := by group

end Construct

end Item812Res4

end CFSG.RankThree.PartTwo.Sec8
