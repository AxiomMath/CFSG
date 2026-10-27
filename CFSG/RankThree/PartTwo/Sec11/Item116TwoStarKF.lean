module

public import CFSG.RankThree.PartTwo.Sec11.Item116EiiO
public import CFSG.RankThree.Theta.TwoPlaneComparison

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.Open (fusionIsSylowIn)
open CFSG.Goldschmidt (oddCoreOf)

@[expose] def twoFitting (X : Type*) [Group X] : Subgroup X :=
  (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)).comap (QuotientGroup.mk' (CFSG.pCore 2 X))

instance twoFitting_characteristic (X : Type*) [Group X] : (twoFitting X).Characteristic := by
  refine Subgroup.characteristic_iff_comap_eq.mpr fun φ => ?_
  have hφ : (CFSG.pCore 2 X).map φ.toMonoidHom = CFSG.pCore 2 X :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance φ
  set φ' := QuotientGroup.congr (CFSG.pCore 2 X) (CFSG.pCore 2 X) φ hφ with hφ'
  have hcomp : (QuotientGroup.mk' (CFSG.pCore 2 X)).comp φ.toMonoidHom =
      φ'.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
    ext x
    rfl
  rw [twoFitting, Subgroup.comap_comap, hcomp, ← Subgroup.comap_comap,
    Subgroup.characteristic_iff_comap_eq.mp
      (inferInstance : (CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X)).Characteristic) φ']

section General

variable {G : Type} [Group G] [Finite G]

namespace KFTools

omit [Finite G] in
theorem normalizer_le_normalizer_twoFitting (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((inSubgroup twoFitting H : Subgroup G) : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (twoFitting H)

omit [Finite G] in
theorem inSubgroup_twoFitting_le (H : Subgroup G) : inSubgroup twoFitting H ≤ H :=
  Subgroup.map_subtype_le _

theorem mem_inSubgroup_twoFitting_of_commutator_mem {H : Subgroup G} (hHs : Group.IsSolvable H)
    {x : G} (hx : x ∈ H)
    (h : ∀ v ∈ inSubgroup twoFitting H, x * v * x⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pCore 2) H) :
    x ∈ inSubgroup twoFitting H := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  have hQs : Group.IsSolvable (H ⧸ CFSG.pCore 2 H) := inferInstance
  have hcent : π ⟨x, hx⟩ ∈ Subgroup.centralizer
      (CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H) : Set (H ⧸ CFSG.pCore 2 H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 H) q
    have hv : (v : G) ∈ inSubgroup twoFitting H := ⟨v, hq, rfl⟩
    have h1 := h v hv
    have h2 : (⟨x, hx⟩ * v * ⟨x, hx⟩⁻¹ * v⁻¹ : H) ∈ CFSG.pCore 2 H :=
      (Subgroup.mem_map_iff_mem H.subtype_injective).mp h1
    have h3 : π (⟨x, hx⟩ * v * ⟨x, hx⟩⁻¹ * v⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
    calc π v * π ⟨x, hx⟩ = (π ⟨x, hx⟩ * π v * (π ⟨x, hx⟩)⁻¹ * (π v)⁻¹)⁻¹ *
          (π ⟨x, hx⟩ * π v) := by group
      _ = π ⟨x, hx⟩ * π v := by rw [h3, inv_one, one_mul]
  exact ⟨⟨x, hx⟩, centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hQs hcent, rfl⟩

end KFTools

end General

section Certified


@[expose] def KFAt {G : Type} [Group G] (L : Subgroup G) (a : G) : Prop :=
  ⁅sec11K L a, inSubgroup twoFitting
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))⁆ ≤
    inSubgroup (CFSG.pCore 2)
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G}

theorem commutator_theta_le_pCore_of_kf (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y)
    {d : G} (hdL : A ⊓ L = Subgroup.zpowers d) (hdc : d ∉ Subgroup.zpowers c) {n : G}
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) (hna : n * a * n⁻¹ ∈ Subgroup.zpowers a)
    (hKF : KFAt L a) :
    ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)), A⁆ ≤
      inSubgroup (CFSG.pCore 2)
        (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) := by
  set θa := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) with hθa
  set U := inSubgroup (CFSG.pCore 2) θa with hU
  set V := inSubgroup twoFitting θa with hV
  set K := sec11K L a with hK
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_isPGroup 3 A hAe
  have haA := h.a_mem
  have hCθ : Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) ≤
      Subgroup.normalizer (θa : Set G) := Sec6.normalizer_le_normalizer_theta _
  have hθU : Subgroup.normalizer (θa : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 θa
  have hθV : Subgroup.normalizer (θa : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    KFTools.normalizer_le_normalizer_twoFitting θa
  have hAθ : A ≤ Subgroup.normalizer (θa : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.commutative_plane_le_element_centralizer A hAe.1 a
      haA).trans (Subgroup.le_normalizer.trans hCθ)
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hnC : n ∈ Subgroup.normalizer (Subgroup.centralizer ({a} : Set G) : Set G) := by
    refine GroupTheory.SteinbergBY.mem_normalizer_of_map_conj_eq ?_
    rw [map_centralizer_singleton, MulAut.conj_apply]
    exact TheoremO.centralizer_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna hna1)
  have hnθ : n ∈ Subgroup.normalizer (θa : Set G) := hCθ hnC
  set X := Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (U : Set G) with hX
  set S := sectionCentralizerSubgroup X V U inf_le_left inf_le_right with hS
  have hAX : A ≤ X := le_inf (hAθ.trans hθV) (hAθ.trans hθU)
  have hcomm_mem : ∀ g ∈ X, (∀ v ∈ V, g * v * g⁻¹ * v⁻¹ ∈ U) → g ∈ S := fun g hg hv => ⟨hg, hv⟩
  have hdS : d ∈ S := by
    have hdA : d ∈ A := (show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1
    refine hcomm_mem d (hAX hdA) fun v hv => hKF ?_
    exact Subgroup.commutator_mem_commutator (TheoremO.mem_sec11K_d h45 h hdL hdc) hv
  have hcS : c ∈ S := by
    refine hcomm_mem c (hAX h.mem_A) fun v hv => ?_
    obtain ⟨k, hk, hkc⟩ := TheoremO.mem_map_conj_sec11K_of_conj_mem_zpowers h45 h hdL hdc hnd
    have hkc' : c = n * k * n⁻¹ := by
      rw [← hkc]
      rfl
    have hv' : n⁻¹ * v * n ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hθV hnθ)) v).mp hv
      rwa [inv_inv] at this
    have h1 := hKF (Subgroup.commutator_mem_commutator hk hv')
    have h2 := (Subgroup.mem_normalizer_iff.mp (hθU hnθ) _).mp h1
    rw [hkc']
    rwa [commutatorElement_def, show n * (k * (n⁻¹ * v * n) * k⁻¹ * (n⁻¹ * v * n)⁻¹) * n⁻¹ =
      n * k * n⁻¹ * v * (n * k * n⁻¹)⁻¹ * v⁻¹ by group] at h2
  have haS : a ∈ S := by
    refine hcomm_mem a (hAX haA) fun v hv => ?_
    have hvC : v ∈ Subgroup.centralizer ({a} : Set G) :=
      Sec6.theta_le _ (KFTools.inSubgroup_twoFitting_le θa hv)
    rw [← Subgroup.mem_centralizer_singleton_iff.mp hvC, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem
  have hAS : A ≤ S := by
    rw [← Item116Fusion.closure_cda_eq h hdL hdc, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact hcS
    · exact hdS
    · exact haS
  have hVA : ⁅V, A⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro v hv g hg
    have h1 := U.inv_mem ((hAS hg).2 v hv)
    rwa [show (g * v * g⁻¹ * v⁻¹)⁻¹ = v * g * v⁻¹ * g⁻¹ by group] at h1
  exact Eii.commutator_le_of_selfCentralizing Nat.prime_three hA3
    (not_three_dvd_card_inSubgroup_theta _) hAθ (KFTools.inSubgroup_twoFitting_le θa)
    (GroupTheory.SteinbergBY.le_normalizer_inSubgroup_pCore 2 θa) (hAθ.trans hθU)
    (Subgroup.le_normalizer.trans hθV) hVA
    (fun x hx hxv => KFTools.mem_inSubgroup_twoFitting_of_commutator_mem
      (isSolvable_inSubgroup_theta _) hx hxv)

theorem exists_twoAlpha_ne_bot_of_kf (hP2b : Item116P2b) (hP2c : Item116P2c)
    (h45 : Sec4.Item4_5) (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hRG : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤) (hdc : d ∉ Subgroup.zpowers c)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) (hna : n * a * n⁻¹ = a⁻¹) (hKF : KFAt L a) :
    ∃ D : Subgroup G, D ≤ A ∧ Nat.card D = 9 ∧ twoAlpha D ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θa := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) with hθa
  set U := inSubgroup (CFSG.pCore 2) θa with hU
  set Pa := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set G)) with hPa
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hA3 : IsPGroup 3 A :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_isPGroup 3 A hAe
  have haA := h.a_mem
  have hna' : n * a * n⁻¹ ∈ Subgroup.zpowers a := by
    rw [hna]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)
  have hθA := commutator_theta_le_pCore_of_kf h45 h hdL hdc hnd hna' hKF
  have hAθ : A ≤ Subgroup.normalizer (θa : Set G) :=
    (CFSG.RankThreeEvenClassification.Helpers.commutative_plane_le_element_centralizer A hAe.1 a
      haA).trans (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _))
  have hθ3 : ¬ 3 ∣ Nat.card θa := not_three_dvd_card_inSubgroup_theta _
  obtain ⟨S, hS, -, hAS⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_three
    Nat.prime_two hA3 hθ3 hAθ bot_le IsPGroup.of_bot
    (fun g _ => by rw [Subgroup.mem_normalizer_iff]; intro x; simp)
  have hSA := not_Eii hP2b hP2c h45 h hdL hWB hirr hRG hdc hD8 hnW hnc hnd hna hS
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three A S hA3 (TheoremO.not_three_dvd_card_of_isPGroup_two hS.2.1) hAS
  have hUPa : U ≤ Pa := by
    refine GroupTheory.SteinbergBY.le_inSubgroup_pCore
      (GroupTheory.SteinbergBY.isPGroup_inSubgroup_pCore 2 θa)
      ((GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 θa).trans (Sec6.theta_le _)) ?_
    exact (Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta _)).trans
      (GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 θa)
  have hPaA : ⁅Pa, A⁆ ≠ ⊥ := by
    intro hbot
    apply hSA
    rw [eq_bot_iff, ← hidem, ← hbot]
    exact Subgroup.commutator_mono
      ((Subgroup.commutator_mono hS.1 le_rfl).trans (hθA.trans hUPa)) le_rfl
  have hx : ∃ x ∈ A, ⁅Pa, Subgroup.zpowers x⁆ ≠ ⊥ := by
    by_contra hall
    push Not at hall
    apply hPaA
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hxA
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hall x hxA) hy
    exact Subgroup.mem_centralizer_iff.mp h1 x (Subgroup.mem_zpowers x)
  obtain ⟨x, hxA, hxne⟩ := hx
  have hPaC : Pa ≤ Subgroup.centralizer ({a} : Set G) :=
    GroupTheory.SteinbergBY.inSubgroup_pCore_le 2 _
  have hxa : x ∉ Subgroup.zpowers a := by
    intro hxa
    apply hxne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa
    have hya : y * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp (hPaC hy)
    exact (Commute.zpow_left (Commute.zpow_left (hya.symm : Commute a y) j) k).eq
  have : IsElementaryAbelian 3 A :=
    (SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hAe
  set D := Subgroup.zpowers a ⊔ Subgroup.zpowers x with hD
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hxA)
  have hDcard : Nat.card D = 9 := by
    rw [hD, GroupTheory.SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three
      (show Nat.card A = 3 ^ 3 by rw [h.card_eq]; norm_num) haA h.a_ne_one hxA hxa]
    norm_num
  refine ⟨D, hDA, hDcard, fun hβ => hxne ?_⟩
  rw [eq_bot_iff, ← hβ]
  refine le_trans ?_ (GroupTheory.twoCoreJ_le_twoCoreAlpha D)
  exact (Subgroup.commutator_mono le_rfl le_sup_right).trans
    (GroupTheory.commutator_le_twoCoreJ (le_sup_left (b := Subgroup.zpowers x)
      (Subgroup.mem_zpowers a)) h.a_ne_one)

theorem betaNontrivial_of_kf (hP2b : Item116P2b) (hP2c : Item116P2c) (h45 : Sec4.Item4_5)
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hWB : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hirr : Sec21.IsIrreducibleOn
      (Sec4.autIn (Subgroup.normalizer (A : Set G)) (Subgroup.closure {c, d})))
    (hRG : CFSG.ABGLocalTools.IsSylowOf 3 R ⊤) (hdc : d ∉ Subgroup.zpowers c)
    (hD8 : ∀ w ∈ Subgroup.normalizer (A : Set G),
      (w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d) ∨
      (w * c * w⁻¹ ∈ Subgroup.zpowers d ∧ w * d * w⁻¹ ∈ Subgroup.zpowers c))
    {n : G} (hnW : n ∈ Subgroup.normalizer (A : Set G)) (hnc : n * c * n⁻¹ ∈ Subgroup.zpowers d)
    (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c) (hna : n * a * n⁻¹ = a⁻¹)
    (hstar : ∀ x ∈ A, x ≠ 1 → TwoStarConditionAt A x) (hKF : KFAt L a) :
    twoAlpha (Subgroup.closure ({c, d} : Set G)) ≠ ⊥ := by
  obtain ⟨D, hDA, hD9, hD⟩ := exists_twoAlpha_ne_bot_of_kf hP2b hP2c h45 h hdL hWB hirr hRG hdc
    hD8 hnW hnc hnd hna hKF
  have hBA : Subgroup.closure ({c, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact h.mem_A
    · exact (show y ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers y).1
  have hAe := h.mem_partTwoF.1
  have hB9 : Nat.card (Subgroup.closure ({c, d} : Set G)) = 9 :=
    Item116Fusion.card_closure_pair_eq_nine hAe.2
      (fun u hu v hv => congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)) h.mem_A
      ((show d ∈ A ⊓ L by rw [hdL]; exact Subgroup.mem_zpowers d).1) h.ne_one hdc
  rw [twoAlpha_hyperplane_independence hAe h.card_eq hstar hBA hB9 hDA hD9]
  exact hD

end Certified

end CFSG.RankThree.PartTwo.Sec11
