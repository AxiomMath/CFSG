module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofInner
public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofCases
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Matrix

section General

variable {X : Type*} [Group X]

theorem commutator_mem_of_sup_closure {L₀ : Subgroup X} [L₀.Normal] {u a : X}
    (htop : L₀ ⊔ Subgroup.closure {u, a} = ⊤) (hua : u * a * u⁻¹ * a⁻¹ ∈ L₀) (x y : X) :
    x * y * x⁻¹ * y⁻¹ ∈ L₀ := by
  set π₀ := QuotientGroup.mk' L₀ with hπ₀
  have huac : Commute (π₀ u) (π₀ a) := by
    have h1 : π₀ (u * a * u⁻¹ * a⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hua
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc π₀ u * π₀ a = (π₀ u * π₀ a * (π₀ u)⁻¹ * (π₀ a)⁻¹) * π₀ a * π₀ u := by group
      _ = π₀ a * π₀ u := by rw [h1, one_mul]
  have hcomm : ({π₀ u, π₀ a} : Set (X ⧸ L₀)).Pairwise Commute :=
    Set.pairwise_pair.mpr fun _ => ⟨huac, huac.symm⟩
  have hmem : ∀ q : X ⧸ L₀, q ∈ Subgroup.closure ({π₀ u, π₀ a} : Set (X ⧸ L₀)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L₀ q
    have hx : π₀ x ∈ (L₀ ⊔ Subgroup.closure {u, a}).map π₀ :=
      Subgroup.mem_map_of_mem _ (htop ▸ Subgroup.mem_top x)
    rwa [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair,
      (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' L₀).ge, bot_sup_eq] at hx
  have hc : π₀ x * π₀ y = π₀ y * π₀ x :=
    Set.centralizer_centralizer_comm_of_comm hcomm _
      (Subgroup.closure_le_centralizer_centralizer _ (hmem _)) _
      (Subgroup.closure_le_centralizer_centralizer _ (hmem _))
  rw [← QuotientGroup.eq_one_iff]
  change π₀ (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
  group

theorem two_mul_card_le_of_le_of_ne [Finite X] {H K : Subgroup X} (hHK : H ≤ K) (hne : H ≠ K) :
    2 * Nat.card H ≤ Nat.card K := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK
  have hK0 : 0 < Nat.card K := Nat.card_pos
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    omega
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hHK (by rw [hm, mul_one]))
  rw [hm, mul_comm]
  exact Nat.mul_le_mul_left _ (by omega)

theorem not_mem_sup_zpowers_of_type3 {L₀ : Subgroup X} (hL : L₀.Normal) {u a : X}
    (huC : u ∈ Subgroup.centralizer (L₀ : Set X)) {π : Bool} {p f : ℕ} {F : Type} [Field F]
    (hF : PiField π p f F) (hq : ModThree π (p ^ f)) (e : L₀ ≃* slPi π 3 (p ^ f) F)
    {y : GL (Fin 3) F} (hyH : y ∈ glPi π 3 (p ^ f) F) (hy3 : Type123 π (p ^ f) F y 3)
    (hact : ∀ z : L₀, ((e ⟨a * z * a⁻¹, hL.conj_mem z z.2 a⟩ : GL (Fin 3) F)) =
      y * (e z : GL (Fin 3) F) * y⁻¹) :
    a ∉ L₀ ⊔ Subgroup.zpowers u := by
  intro ha
  obtain ⟨l, hl, w, hw, hlw⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  have hwC : w ∈ Subgroup.centralizer (L₀ : Set X) := (Subgroup.zpowers_le.mpr huC) hw
  have key : ∀ z : L₀, a * (z : X) * a⁻¹ = l * z * l⁻¹ := by
    intro z
    have hwz : w * (z : X) * w⁻¹ = z := by
      rw [← Subgroup.mem_centralizer_iff.mp hwC z z.2, mul_inv_cancel_right]
    rw [← hlw, show l * w * (z : X) * (l * w)⁻¹ = l * (w * z * w⁻¹) * l⁻¹ by group, hwz]
  apply Sec4.not_inner_of_type3 hF hq hyH hy3
  refine ⟨(e ⟨l, hl⟩ : GL (Fin 3) F), (e ⟨l, hl⟩).2, fun m hm => ?_⟩
  set z := e.symm ⟨m, hm⟩ with hz
  have hez : (e z : GL (Fin 3) F) = m := by rw [hz, MulEquiv.apply_symm_apply]
  have heq : (⟨a * (z : X) * a⁻¹, hL.conj_mem z z.2 a⟩ : L₀) = ⟨l, hl⟩ * z * ⟨l, hl⟩⁻¹ :=
    Subtype.ext (key z)
  have h1 := hact z
  rw [heq, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
    hez] at h1
  exact h1.symm

theorem eq_of_perfect_normal {L₀ K : Subgroup X} [hL₀ : L₀.Normal] {u a : X}
    (htop : L₀ ⊔ Subgroup.closure {u, a} = ⊤) (hua : u * a * u⁻¹ * a⁻¹ ∈ L₀)
    {π : Bool} {p f : ℕ} {F : Type} [Field F] (hF : PiField π p f F) (hq : ModThree π (p ^ f))
    (e : L₀ ≃* slPi π 3 (p ^ f) F) (hKn : K.Normal) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥) :
    K = L₀ := by
  have hKL : K ≤ L₀ := by
    intro k hk
    set φ : K →* X ⧸ L₀ := (QuotientGroup.mk' L₀).comp K.subtype with hφ
    have hle : commutator K ≤ φ.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def]
      change QuotientGroup.mk' L₀ ((x : X) * y * (x : X)⁻¹ * (y : X)⁻¹) = 1
      exact (QuotientGroup.eq_one_iff _).mpr (commutator_mem_of_sup_closure htop hua x y)
    rw [@Group.IsPerfect.commutator_eq_top _ _ hKp] at hle
    have h1 : φ ⟨k, hk⟩ = 1 := hle (Subgroup.mem_top _)
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hKnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK1
  have hp : p.Prime := hF.prime
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by have := hF.one_le; omega) p)
  by_cases h2 : p ^ f = 2
  ·
    exfalso
    cases π
    · have := Sec13.isSolvable_slPi_two hF h2
      have hs : Group.IsSolvable L₀ :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      have hsK : Group.IsSolvable K :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKL)
          (Subgroup.inclusion_injective hKL)
      exact Group.IsPerfect.not_isSolvable K hsK
    · change p ^ f % 3 = 1 at hq
      omega
  · have hQ : IsQuasisimple L₀ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (Sec13.isQuasisimple_slPi hF (by omega))
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ (hKn.subgroupOf L₀) with h | h
    · exact le_antisymm hKL (Subgroup.subgroupOf_eq_top.mp h)
    · exfalso
      have hcomm : ∀ x y : K, x * y = y * x := by
        intro x y
        have hx : (⟨x, hKL x.2⟩ : L₀) ∈ Subgroup.center L₀ := h (Subgroup.mem_subgroupOf.mpr x.2)
        exact Subtype.ext (congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hKL y.2⟩)).symm
      have hbot : commutator K = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hcomm y x
      rw [@Group.IsPerfect.commutator_eq_top _ _ hKp] at hbot
      obtain ⟨x, hx⟩ := exists_ne (1 : K)
      exact hx (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_top x))

theorem center_facts {L₀ : Subgroup X} (hL : L₀.Normal) {u a : X}
    (huC : u ∈ Subgroup.centralizer (L₀ : Set X))
    (htop : L₀ ⊔ Subgroup.closure {u, a} = ⊤) {π : Bool} {p f : ℕ} {F : Type} [Field F]
    (hF : PiField π p f F) (hq : ModThree π (p ^ f)) (e : L₀ ≃* slPi π 3 (p ^ f) F)
    {y : GL (Fin 3) F}
    (hact : ∀ z : L₀, ((e ⟨a * z * a⁻¹, hL.conj_mem z z.2 a⟩ : GL (Fin 3) F)) =
      y * (e z : GL (Fin 3) F) * y⁻¹)
    {z : X} (hz : z ∈ L₀) (hzC : ∀ k ∈ L₀, z * k = k * z) :
    z ^ 3 = 1 ∧ z ∈ Subgroup.center X := by
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F :=
    fun h => by subst h; exact hF.unitary
  have hzc : (⟨z, hz⟩ : L₀) ∈ Subgroup.center L₀ := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hzC k k.2).symm
  have hec : e ⟨z, hz⟩ ∈ Subgroup.center (slPi π 3 (p ^ f) F) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨_, hzc, rfl⟩
  obtain ⟨μ, hμ⟩ := Sec13.mem_statedScalars_of_mem_center hF hq hec
  have hdet : ((e ⟨z, hz⟩ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    ((Sec4.mem_slPi_iff hπ).mp (e ⟨z, hz⟩).2).2
  rw [← hμ, Sec4.det_scalar] at hdet
  have hμ3 : μ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hdet)
  refine ⟨?_, ?_⟩
  · have h1 : (e ⟨z, hz⟩) ^ 3 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ← hμ, ← map_pow, hμ3, map_one]
      rfl
    have h2 : (⟨z, hz⟩ : L₀) ^ 3 = 1 := e.injective (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val h2
  · have hza : a * z * a⁻¹ = z := by
      have h1 := hact ⟨z, hz⟩
      have hc : GeneralLinearGroup.scalar (Fin 3) μ ∈ Subgroup.center (GL (Fin 3) F) := by
        rw [GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨μ, rfl⟩
      have hyc : y * GeneralLinearGroup.scalar (Fin 3) μ * y⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) μ := by
        rw [Subgroup.mem_center_iff.mp hc y, mul_inv_cancel_right]
      rw [← hμ, hyc, hμ] at h1
      have h2 : (⟨a * z * a⁻¹, hL.conj_mem z hz a⟩ : L₀) = ⟨z, hz⟩ :=
        e.injective (Subtype.ext h1)
      exact congrArg Subtype.val h2
    have hle : L₀ ⊔ Subgroup.closure {u, a} ≤ Subgroup.centralizer {z} := by
      refine sup_le (fun k hk => Subgroup.mem_centralizer_singleton_iff.mpr (hzC k hk).symm) ?_
      rw [Subgroup.closure_le]
      intro s hs
      rcases hs with rfl | hs
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp huC z hz).symm
      · rw [Set.mem_singleton_iff] at hs
        subst hs
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc s * z = s * z * s⁻¹ * s := by group
          _ = z * s := by rw [hza]
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (htop ▸ Subgroup.mem_top g))

end General

section Theta

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem eta_thetaQuotMulAut
    {η : L ⧸ aschbacherSolvableCore 3 L ≃* L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))}
    (hη : ∀ l : L, (η (l : L ⧸ aschbacherSolvableCore 3 L) : G ⧸ aschbacherSolvableCore 3 G) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) (l : G))
    {b : G} (hb : b ∈ Subgroup.normalizer (L : Set G)) (x : L ⧸ aschbacherSolvableCore 3 L) :
    (η (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) x) : G ⧸ aschbacherSolvableCore 3 G) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) b * (η x : G ⧸ aschbacherSolvableCore 3 G) *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 G) b)⁻¹ := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [thetaQuotMulAut_mk, hη, hη, Sec4.normalizerMonoidHom_apply_coe, map_mul, map_mul, map_inv]

theorem isSLThreePiTwo_core {Y : Type} [Group Y] [Finite Y] {K H : Subgroup Y} (hKH : K ≤ H)
    (hHn : H ≤ Subgroup.normalizer (K : Set Y)) (hKp : Group.IsPerfect K) (hK1 : K ≠ ⊥)
    (h : IsSLThreePiTwo H) :
    (∃ (π : Bool) (p f : ℕ) (F : Type) (_ : Field F) (_ : PiField π p f F)
      (_ : ModThree π (p ^ f)), Nonempty (K ≃* slPi π 3 (p ^ f) F)) ∧
    4 * Nat.card K ≤ Nat.card H ∧
    (∀ z ∈ K, (∀ k ∈ K, z * k = k * z) → z ^ 3 = 1 ∧ ∀ g ∈ H, g * z = z * g) ∧
    (∃ c ∈ K, c ≠ 1 ∧ ∀ k ∈ K, c * k = k * c) := by
  classical
  obtain ⟨L₀, hL₀, u, a₀, -, huC, huL, -, -, htop, hc1, hcZ, π, p, f, F, _, hF, hq, e, y,
    hyH, hy3, hact⟩ := h
  set K' := K.subgroupOf H with hK'
  have hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHn
  have : Group.IsPerfect K := hKp
  have hK'p : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have hK'1 : K' ≠ ⊥ := by
    intro h0
    apply hK1
    rw [eq_bot_iff]
    intro k hk
    have : (⟨k, hKH hk⟩ : H) ∈ K' := Subgroup.mem_subgroupOf.mpr hk
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hK'L₀ : K' = L₀ := eq_of_perfect_normal htop hcZ.1 hF hq e hK'n hK'p hK'1
  have hmemK : ∀ k : H, k ∈ L₀ ↔ (k : Y) ∈ K := by
    intro k
    rw [← hK'L₀]
    exact Subgroup.mem_subgroupOf
  have eK : K ≃* L₀ :=
    (Subgroup.subgroupOfEquivOfLe hKH).symm.trans (MulEquiv.subgroupCongr hK'L₀)
  have hu : L₀ ≠ L₀ ⊔ Subgroup.zpowers u := by
    intro h0
    apply huL
    rw [h0]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  have ha₀ : L₀ ⊔ Subgroup.zpowers u ≠ ⊤ := by
    intro h0
    exact not_mem_sup_zpowers_of_type3 hL₀ huC hF hq e hyH hy3 hact (h0 ▸ Subgroup.mem_top a₀)
  have h4 : 4 * Nat.card L₀ ≤ Nat.card H := by
    have e1 := two_mul_card_le_of_le_of_ne le_sup_left hu
    have e2 := two_mul_card_le_of_le_of_ne le_top ha₀
    rw [Subgroup.card_top] at e2
    omega
  refine ⟨⟨π, p, f, F, inferInstance, hF, hq, ⟨eK.trans e⟩⟩, ?_, ?_, ?_⟩
  · rw [Nat.card_congr eK.toEquiv]
    exact h4
  ·
    intro z hz hzC
    have hzL₀ : (⟨z, hKH hz⟩ : H) ∈ L₀ := (hmemK _).mpr hz
    have hzC' : ∀ k ∈ L₀, (⟨z, hKH hz⟩ : H) * k = k * ⟨z, hKH hz⟩ := fun k hk =>
      Subtype.ext (hzC k ((hmemK k).mp hk))
    obtain ⟨hz3, hzZ⟩ := center_facts hL₀ huC htop hF hq e hact hzL₀ hzC'
    refine ⟨by simpa using congrArg Subtype.val hz3, fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzZ ⟨g, hg⟩)
  ·
    refine ⟨((u * a₀ * u⁻¹ * a₀⁻¹ : H) : Y), (hmemK _).mp hcZ.1, fun h0 => hc1 (Subtype.ext h0),
      fun k hk => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hcZ.2 ⟨k, hKH hk⟩ ((hmemK _).mpr hk)
    exact (congrArg Subtype.val this).symm

theorem isSLThreePiTwo_structure (hL : L ∈ thetaComponents 3 G) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (h27 : Nat.card A = 27) (h : IsSLThreePiTwo (thetaImage (L ⊔ A))) :
    (∃ (p f : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧
      IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ f)) ∧
    Nat.card (A ⊓ L : Subgroup G) ≤ 3 ∧
    (∀ z ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      (∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), z * k = k * z) →
        z ^ 3 = 1 ∧ ∀ x ∈ A, QuotientGroup.mk' (aschbacherSolvableCore 3 G) x * z =
          z * QuotientGroup.mk' (aschbacherSolvableCore 3 G) x) ∧
    (∃ c ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), c ≠ 1 ∧
      ∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), c * k = k * c) := by
  classical
  obtain ⟨-, hKc, ⟨η, -⟩, -⟩ := theta_component_quotient_structure Nat.prime_three hL
  have hKH : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ thetaImage (L ⊔ A) :=
    Subgroup.map_mono le_sup_left
  have hHn : thetaImage (L ⊔ A) ≤ Subgroup.normalizer
      ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) : Subgroup _) : Set _) :=
    (Subgroup.map_mono (sup_le Subgroup.le_normalizer hAN)).trans (Subgroup.le_normalizer_map _)
  obtain ⟨hKp, -, x₁, x₂, hx₁₂⟩ := hKc.1
  have hK1 : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≠ ⊥ := by
    intro h0
    apply hx₁₂
    have hsub : ∀ k : L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), k = 1 := fun k =>
      Subtype.ext (Subgroup.mem_bot.mp (h0.le k.2))
    obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x₁
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective x₂
    rw [hsub x', hsub y']
  obtain ⟨⟨π, p, f, F, _, hF, hq, ⟨eK⟩⟩, h4, hcen, hc⟩ :=
    isSLThreePiTwo_core hKH hHn hKp hK1 h
  have hpF : Fact p.Prime := ⟨hF.prime⟩
  have hSL : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ f) := by
    have := hF.finite
    cases π
    · exact ⟨F, inferInstance, inferInstance, Or.inr ⟨hF.card, hq, ⟨η.trans eK⟩⟩⟩
    · exact ⟨F, inferInstance, inferInstance, Or.inl ⟨hF.card, hq, ⟨η.trans eK⟩⟩⟩
  have hcardmul := card_thetaImage_mul hL hAN hA3
  have hcardK : Nat.card (L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) =
      Nat.card (L ⧸ aschbacherSolvableCore 3 L) := (Nat.card_congr η.toEquiv).symm
  have hcardAL : Nat.card (A ⊓ L : Subgroup G) ≤ 3 := by
    have hpos : 0 < Nat.card (L ⧸ aschbacherSolvableCore 3 L) := Nat.card_pos
    have h5 : Nat.card (L ⧸ aschbacherSolvableCore 3 L) * (4 * Nat.card (A ⊓ L : Subgroup G)) ≤
        Nat.card (L ⧸ aschbacherSolvableCore 3 L) * 27 := by
      calc Nat.card (L ⧸ aschbacherSolvableCore 3 L) * (4 * Nat.card (A ⊓ L : Subgroup G)) =
            (4 * Nat.card (L ⧸ aschbacherSolvableCore 3 L)) * Nat.card (A ⊓ L : Subgroup G) := by
              ring
        _ ≤ Nat.card (thetaImage (L ⊔ A)) * Nat.card (A ⊓ L : Subgroup G) :=
          Nat.mul_le_mul_right _ (hcardK ▸ h4)
        _ = Nat.card (L ⧸ aschbacherSolvableCore 3 L) * 27 := by rw [hcardmul, h27]
    have h6 := Nat.le_of_mul_le_mul_left h5 hpos
    have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hk] at h6 ⊢
    interval_cases k <;> simp_all
  refine ⟨⟨p, f, hpF, hF.one_le, hSL⟩, hcardAL, fun z hz hzC => ?_, hc⟩
  obtain ⟨hz3, hzH⟩ := hcen z hz hzC
  exact ⟨hz3, fun x hx => hzH _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right hx))⟩

theorem false_of_isSLThreePiTwo (hKL3 : KSLThreeCentralizerQ) {A B D : Subgroup G} {a b : G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) (hBD : B ⊓ D = ⊥)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hβ3 : orderOf (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hAL (hBA hbB)⟩)) = 3)
    (hβ : InnThetaNoncyclic (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hAL (hBA hbB)⟩)))
    (h : IsSLThreePiTwo (thetaImage (L ⊔ A))) : False := by
  classical
  have hAe := hmax.1
  obtain ⟨⟨p, f, hpF, hf, hSL⟩, hcard, hZc, ⟨c, hcK, hc1, hcC⟩⟩ :=
    isSLThreePiTwo_structure hL hAL hAe.2 h27 h
  obtain ⟨-, v, hv3, hβv⟩ := KSLThreeCentralizerQ.inst hKL3 hL hf (Or.inl hSL) hβ3 hβ
  obtain ⟨-, -, ⟨η, hη⟩, -⟩ := theta_component_quotient_structure Nat.prime_three hL
  have haA' : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr haA
  have hZ : ∀ z ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      (∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)), z * k = k * z) →
        z ∈ (Subgroup.zpowers a).map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) := by
    intro z hz hzC
    obtain ⟨hz3, hzA⟩ := hZc z hz hzC
    have hzcen : z ∈ Subgroup.centralizer
        ((A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) : Subgroup _) :
          Set (G ⧸ aschbacherSolvableCore 3 G)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hzA x hx
    obtain ⟨w, hwA, rfl⟩ := Item422Proof.mem_map_of_maximal hmax _
      three_not_dvd_card_aschbacherSolvableCore hz3 hzcen
    have hwC : w ∈ thetaQuotCentralizer L := by
      rw [Item462Proof.mem_thetaQuotCentralizer_iff_mk hL, Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hzC k hk).symm
    exact ⟨w, (hCA w hwA).mp hwC, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hZ c hcK hcC
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hc1 (map_one _)
  have hwL : w ∈ L := mem_of_mk_mem_map hL (hAe.2 w (haA' hw)) hcK
  have haL : a ∈ L := by
    have hwo : orderOf w = 3 := orderOf_eq_prime (hAe.2 w (haA' hw)) hw1
    have heq : Subgroup.zpowers w = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hwo])
    exact (Subgroup.zpowers_le.mpr hwL) (heq ▸ Subgroup.mem_zpowers a)
  have hAL3 : A ⊓ L ≤ Subgroup.zpowers a := by
    have hle : Subgroup.zpowers a ≤ A ⊓ L := Subgroup.zpowers_le.mpr ⟨haA, haL⟩
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, ha3]; exact hcard)).ge
  have hbv : ∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      QuotientGroup.mk' (aschbacherSolvableCore 3 G) b * k *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 G) b)⁻¹ =
      (η v : G ⧸ aschbacherSolvableCore 3 G) * k * (η v : G ⧸ aschbacherSolvableCore 3 G)⁻¹ := by
    intro k hk
    obtain ⟨x, hx⟩ := η.surjective ⟨k, hk⟩
    have hk' : (η x : G ⧸ aschbacherSolvableCore 3 G) = k := congrArg Subtype.val hx
    rw [← hk', ← eta_thetaQuotMulAut hη (hAL (hBA hbB)) x, hβv, MulAut.conj_apply, map_mul,
      map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have hvZ : ¬ ∀ k ∈ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      (η v : G ⧸ aschbacherSolvableCore 3 G) * k = k * (η v : G ⧸ aschbacherSolvableCore 3 G) := by
    intro hcen
    have hv1 : MulAut.conj v = 1 := by
      ext x
      rw [MulAut.conj_apply, MulAut.one_apply]
      apply η.injective
      apply Subtype.ext
      rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
        hcen _ (η x).2, mul_inv_cancel_right]
    rw [hβv, hv1, orderOf_one] at hβ3
    exact absurd hβ3 (by norm_num)
  have hv3' : (η v : G ⧸ aschbacherSolvableCore 3 G) ^ 3 = 1 := by
    rw [← SubgroupClass.coe_pow, ← map_pow, hv3, map_one, OneMemClass.coe_one]
  exact false_of_inner hmax haZ ha3 haB hbB hba hBA hB9 hDA hBDA hBD hND hL hAL hAL3 hZ
    (η v).2 hv3' hvZ hbv

theorem list463_of_isSLThreePiTwo (hKL3 : KSLThreeCentralizerQ) (h41 : Item4_1LargePrime)
    (hS4 : SectionFourHyp G) (hL : L ∈ thetaComponents 3 G) {A : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA3 : ∀ x ∈ A, x ^ 3 = 1)
    (h27 : Nat.card A = 27) {β : MulAut (L ⧸ aschbacherSolvableCore 3 L)} (hβ3 : orderOf β = 3)
    (hβ : InnThetaNoncyclic β) (h : IsSLThreePiTwo (thetaImage (L ⊔ A))) : List463 L := by
  obtain ⟨⟨p, f, hpF, hf, hSL⟩, -⟩ := isSLThreePiTwo_structure hL hAN hA3 h27 h
  exact list463_of_model hKL3 h41 hS4 hL hβ3 hβ hf (Or.inl hSL)

end Theta

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
