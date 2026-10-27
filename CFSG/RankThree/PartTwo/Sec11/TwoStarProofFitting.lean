module

public import CFSG.RankThree.PartTwo.Sec11.Item116TwoStarKF
public import CFSG.RankThree.Theta.TwoStarComponents
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.Theta
open CFSG.RankThree.GroupTheory
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_preimage_of_pGroup_prime_complement_kernel)
open scoped commutatorElement

namespace TwoStarProof

variable {G : Type} [Group G] [Finite G]

theorem mem_pCore_of_mem_twoFitting {H : Subgroup G} {w : G}
    (hw : w ∈ inSubgroup twoFitting H) {n : ℕ} (hn : w ^ 2 ^ n = 1) :
    w ∈ inSubgroup (CFSG.pCore 2) H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hh, rfl⟩ := hw
  set q := QuotientGroup.mk' (CFSG.pCore 2 H) with hq
  have hh' : q h ∈ CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H) := hh
  have hhn : h ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
  have hU : IsPGroup 2 (Subgroup.zpowers (q h)) := by
    have hdvd : orderOf (q h) ∣ 2 ^ n :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hhn, map_one])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hle := CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore
    (Subgroup.zpowers (q h)) (CFSG.fittingSubgroup (H ⧸ CFSG.pCore 2 H)) 2 Nat.prime_two hU
    inferInstance inferInstance
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hle
  have h1 : q h = 1 := by
    have := hle ⟨Subgroup.mem_zpowers _, hh'⟩
    rwa [Subgroup.mem_bot] at this
  have h2 : h ∈ CFSG.pCore 2 H := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 H)]
    exact h1
  exact ⟨h, h2, rfl⟩

omit [Finite G] in
theorem pCore_le_twoFitting (H : Subgroup G) :
    inSubgroup (CFSG.pCore 2) H ≤ inSubgroup twoFitting H := by
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨h, ?_, rfl⟩
  change QuotientGroup.mk' (CFSG.pCore 2 H) h ∈ CFSG.fittingSubgroup _
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).mpr hh]
  exact one_mem _

theorem pCore_theta_le_pCore (C : Subgroup G) :
    inSubgroup (CFSG.pCore 2) (inSubgroup (aschbacherSolvableCore 3) C) ≤
      inSubgroup (CFSG.pCore 2) C :=
  SteinbergBY.le_inSubgroup_pCore (SteinbergBY.isPGroup_inSubgroup_pCore 2 _)
    ((SteinbergBY.inSubgroup_pCore_le 2 _).trans (Sec6.theta_le C))
    ((Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta C)).trans
      (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _))

theorem le_normalizer_twoFitting_pCore (C : Subgroup G) :
    C ≤ Subgroup.normalizer
        (inSubgroup twoFitting (inSubgroup (aschbacherSolvableCore 3) C) : Set G) ⊓
      Subgroup.normalizer
        (inSubgroup (CFSG.pCore 2) (inSubgroup (aschbacherSolvableCore 3) C) : Set G) := by
  have h := Subgroup.le_normalizer.trans (Sec6.normalizer_le_normalizer_theta C)
  exact le_inf (h.trans (KFTools.normalizer_le_normalizer_twoFitting _))
    (h.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore 2 _))

omit [Finite G] in
theorem conj_mem_sectionCentralizer {V U : Subgroup G} {g s : G}
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgU : g ∈ Subgroup.normalizer (U : Set G))
    (hs : ∀ v ∈ V, s * v * s⁻¹ * v⁻¹ ∈ U) :
    ∀ v ∈ V, (g * s * g⁻¹) * v * (g * s * g⁻¹)⁻¹ * v⁻¹ ∈ U := by
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgV) v).mp hv
    rwa [inv_inv] at this
  have h1 := (Subgroup.mem_normalizer_iff.mp hgU _).mp (hs _ hv')
  have e : g * (s * (g⁻¹ * v * g) * s⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ =
      (g * s * g⁻¹) * v * (g * s * g⁻¹)⁻¹ * v⁻¹ := by group
  rwa [e] at h1

omit [Finite G] in
theorem commutator_mem_sectionCentralizer {V U : Subgroup G} {x y : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxU : x ∈ Subgroup.normalizer (U : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hyU : y ∈ Subgroup.normalizer (U : Set G))
    (hy : ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ U) :
    ∀ v ∈ V, (x * y * x⁻¹ * y⁻¹) * v * (x * y * x⁻¹ * y⁻¹)⁻¹ * v⁻¹ ∈ U := by
  set S := sectionCentralizerSubgroup (Subgroup.normalizer (V : Set G) ⊓
    Subgroup.normalizer (U : Set G)) V U inf_le_left inf_le_right with hS
  have hyS : y ∈ S := ⟨⟨hyV, hyU⟩, hy⟩
  have hxyS : x * y * x⁻¹ ∈ S :=
    ⟨⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hxV hyV) (Subgroup.inv_mem _ hxV),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxU hyU) (Subgroup.inv_mem _ hxU)⟩,
      conj_mem_sectionCentralizer hxV hxU hy⟩
  exact (S.mul_mem hxyS (S.inv_mem hyS)).2

theorem mem_pCore_of_theta {c : G} {V : Subgroup G} (hV : CFSG.Assembly.IsElemAbelian 3 V)
    (hV9 : 3 ^ 2 ≤ Nat.card V) (hVC : V ≤ Subgroup.centralizer ({c} : Set G)) {u : G}
    (hu : ∀ v ∈ V, v ≠ 1 → u ∈ inSubgroup (CFSG.pCore 2)
      (Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({v} : Set G)))
    (huθ : u ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))) :
    u ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set θc := inSubgroup (aschbacherSolvableCore 3) C with hθc
  set F₂ := inSubgroup twoFitting θc with hF₂
  set O := inSubgroup (CFSG.pCore 2) θc with hO
  have hθC : θc ≤ C := Sec6.theta_le C
  have hθN := le_normalizer_twoFitting_pCore C
  have hθθ : θc ≤ Subgroup.normalizer (F₂ : Set G) ⊓ Subgroup.normalizer (O : Set G) :=
    le_inf (Subgroup.le_normalizer.trans (KFTools.normalizer_le_normalizer_twoFitting θc))
      (SteinbergBY.le_normalizer_inSubgroup_pCore 2 θc)
  have hF₂θ : F₂ ≤ θc := KFTools.inSubgroup_twoFitting_le θc
  let M : Subgroup G :=
    { carrier := {f | f ∈ Subgroup.normalizer (O : Set G) ∧ u * f * u⁻¹ * f⁻¹ ∈ O}
      mul_mem' := by
        rintro f g ⟨hfN, hf⟩ ⟨hgN, hg⟩
        refine ⟨Subgroup.mul_mem _ hfN hgN, ?_⟩
        have e : u * (f * g) * u⁻¹ * (f * g)⁻¹ =
            (u * f * u⁻¹ * f⁻¹) * (f * (u * g * u⁻¹ * g⁻¹) * f⁻¹) := by group
        rw [e]
        exact O.mul_mem hf ((Subgroup.mem_normalizer_iff.mp hfN _).mp hg)
      one_mem' := ⟨Subgroup.one_mem _, by simp⟩
      inv_mem' := by
        rintro f ⟨hfN, hf⟩
        refine ⟨Subgroup.inv_mem _ hfN, ?_⟩
        have e : u * f⁻¹ * u⁻¹ * f⁻¹⁻¹ = f⁻¹ * (u * f * u⁻¹ * f⁻¹)⁻¹ * f⁻¹⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hfN) _).mp (O.inv_mem hf) }
  have hF₂M : F₂ ≤ M := by
    refine Sec5.le_of_forall_inf_centralizer_le Nat.prime_three hV hV9
      (hVC.trans (hθN.trans inf_le_left)) ?_ ?_
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 =>
        not_three_dvd_card_inSubgroup_theta C (h3.trans (Subgroup.card_dvd_of_le hF₂θ))
    · intro v hv hv1 f ⟨hfF, hfv⟩
      refine ⟨(hθθ (hF₂θ hfF)).2, ?_⟩
      set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({v} : Set G))
      have hfP : f ∈ Subgroup.normalizer (P : Set G) :=
        SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ ⟨hθC (hF₂θ hfF), hfv⟩
      have huP := hu v hv hv1
      have h1 : u * f * u⁻¹ * f⁻¹ ∈ P := by
        have := (Subgroup.mem_normalizer_iff.mp hfP u⁻¹).mp (P.inv_mem huP)
        have e : u * f * u⁻¹ * f⁻¹ = u * (f * u⁻¹ * f⁻¹) := by group
        rw [e]
        exact P.mul_mem huP this
      have h2 : u * f * u⁻¹ * f⁻¹ ∈ F₂ :=
        F₂.mul_mem ((Subgroup.mem_normalizer_iff.mp ((hθθ huθ).1) f).mp hfF) (F₂.inv_mem hfF)
      obtain ⟨n, hn⟩ := TwoStarComponents.exists_pow_two_pow_eq_one
        (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) h1
      exact mem_pCore_of_mem_twoFitting h2 hn
  have huF : u ∈ F₂ := KFTools.mem_inSubgroup_twoFitting_of_commutator_mem
    (isSolvable_inSubgroup_theta C) huθ fun v hv => (hF₂M hv).2
  obtain ⟨v₀, hv₀V, hv₀1⟩ : ∃ v ∈ V, v ≠ 1 := by
    by_contra! h
    have hV1 : V = ⊥ := (Subgroup.eq_bot_iff_forall V).mpr h
    rw [hV1, Subgroup.card_bot] at hV9
    norm_num at hV9
  obtain ⟨n, hn⟩ := TwoStarComponents.exists_pow_two_pow_eq_one
    (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) (hu v₀ hv₀V hv₀1)
  exact pCore_theta_le_pCore C (mem_pCore_of_mem_twoFitting huF hn)

theorem zpowers_sup_eq_of_mem {A : Subgroup G} [IsElementaryAbelian 3 A] (hA27 : Nat.card A = 27)
    {c y k : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hyA : y ∈ A) (hyc : y ∉ Subgroup.zpowers c)
    (hkA : k ∈ A) (hkc : k ∉ Subgroup.zpowers c)
    (hkE : k ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers y) :
    Subgroup.zpowers c ⊔ Subgroup.zpowers k = Subgroup.zpowers c ⊔ Subgroup.zpowers y := by
  have h27 : Nat.card A = 3 ^ 3 := by rw [hA27]; norm_num
  refine Subgroup.eq_of_le_of_card_ge
    (sup_le le_sup_left (Subgroup.zpowers_le.mpr hkE)) ?_
  rw [SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hcA hc1 hyA hyc,
    SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hcA hc1 hkA hkc]

theorem zpowers_sup_sup_eq {A : Subgroup G} [IsElementaryAbelian 3 A] (hA27 : Nat.card A = 27)
    {c y k : G} (hcA : c ∈ A) (hc1 : c ≠ 1) (hyA : y ∈ A) (hyc : y ∉ Subgroup.zpowers c)
    (hkA : k ∈ A) (hkE : k ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers y) :
    Subgroup.zpowers c ⊔ Subgroup.zpowers y ⊔ Subgroup.zpowers k = A := by
  have h27 : Nat.card A = 3 ^ 3 := by rw [hA27]; norm_num
  set E := Subgroup.zpowers c ⊔ Subgroup.zpowers y with hE
  set E' := E ⊔ Subgroup.zpowers k with hE'
  have hE9 : Nat.card E = 9 := by
    rw [hE, SteinbergBY.card_zpowers_sup_zpowers Nat.prime_three h27 hcA hc1 hyA hyc]
    norm_num
  have hEA : E ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr hyA)
  have hE'A : E' ≤ A := sup_le hEA (Subgroup.zpowers_le.mpr hkA)
  have hEE' : E ≤ E' := le_sup_left
  have hd1 : Nat.card E' ∣ 27 := hA27 ▸ Subgroup.card_dvd_of_le hE'A
  have hd2 : 9 ∣ Nat.card E' := hE9 ▸ Subgroup.card_dvd_of_le hEE'
  have hne : Nat.card E' ≠ 9 := by
    intro h9
    have : E = E' := Subgroup.eq_of_le_of_card_ge hEE' (by rw [h9, hE9])
    exact hkE (this ▸ (le_sup_right : Subgroup.zpowers k ≤ E') (Subgroup.mem_zpowers k))
  have h27' : Nat.card E' = 27 := by
    obtain ⟨m, hm⟩ := hd2
    rw [hm] at hd1 hne ⊢
    have hm3 : m ∣ 3 :=
      Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 9) (by simpa using hd1)
    rcases (Nat.dvd_prime Nat.prime_three).mp hm3 with h | h
    · rw [h] at hne; norm_num at hne
    · rw [h]
  exact Subgroup.eq_of_le_of_card_ge hE'A (by rw [h27', hA27])

theorem commutator_le_pCore_of_theta {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {y : G} (hyA : y ∈ A)
    (hyc : y ∉ Subgroup.zpowers c) {k : G} (hkA : k ∈ A) (hkc : k ∉ Subgroup.zpowers c)
    (hk : ∀ v ∈ inSubgroup twoFitting (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G))),
      k * v * k⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pCore 2) (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G))))
    (h1 : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)), A⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))) :
    ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)), A⁆ ≤
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G)) := by
  have : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).2 hA
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set θc := inSubgroup (aschbacherSolvableCore 3) C with hθc
  set F₂ := inSubgroup twoFitting θc with hF₂
  set O := inSubgroup (CFSG.pCore 2) θc with hO
  set P := inSubgroup (CFSG.pCore 2) (C ⊓ Subgroup.centralizer ({y} : Set G)) with hP
  set St := Subgroup.normalizer (F₂ : Set G) ⊓ Subgroup.normalizer (O : Set G) with hSt
  set S := sectionCentralizerSubgroup St F₂ O inf_le_left inf_le_right with hS
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAC : A ≤ C := fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hACy : A ≤ C ⊓ Subgroup.centralizer ({y} : Set G) := fun u hu =>
    ⟨hAC hu, Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu y hyA)⟩
  have hPC : P ≤ C := (SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_left
  have hCSt : C ≤ St := le_normalizer_twoFitting_pCore C
  have hAP : A ≤ Subgroup.normalizer (P : Set G) :=
    hACy.trans (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _)
  have hPA : ⁅P, A⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_left.mp hAP
  have hθC : θc ≤ C := Sec6.theta_le C
  have hOθ : O ≤ θc := SteinbergBY.inSubgroup_pCore_le 2 θc
  have hOF : O ≤ F₂ := pCore_le_twoFitting θc
  have hkS : k ∈ S := ⟨hCSt (hAC hkA), hk⟩
  suffices hPAS : ⁅P, A⁆ ≤ S by
    intro w hw
    have hwF : w ∈ F₂ := KFTools.mem_inSubgroup_twoFitting_of_commutator_mem
      (isSolvable_inSubgroup_theta C) (h1 hw) (hPAS hw).2
    obtain ⟨n, hn⟩ := TwoStarComponents.exists_pow_two_pow_eq_one
      (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) (hPA hw)
    exact pCore_theta_le_pCore C (mem_pCore_of_mem_twoFitting hwF hn)
  by_cases hkE : k ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers y
  ·
    have hplane := zpowers_sup_eq_of_mem hA27 hcA hc1 hyA hyc hkA hkc hkE
    have hPS : P ≤ S := by
      intro q hq
      refine ⟨hCSt (hPC hq), fun v hv => ?_⟩
      have hOC : O ≤ C := hOθ.trans hθC
      have hOn : (O.subgroupOf C).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOC).mpr (hCSt.trans inf_le_right)
      set π := QuotientGroup.mk' (O.subgroupOf C) with hπ
      have hker : ¬ 3 ∣ Nat.card π.ker := by
        rw [hπ, QuotientGroup.ker_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOC).toEquiv]
        intro h3
        obtain ⟨m, hm⟩ := (SteinbergBY.isPGroup_inSubgroup_pCore 2 θc).exists_card_eq
        rw [hm] at h3
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
          (Nat.prime_three.dvd_of_dvd_pow h3)
        norm_num at this
      have hk3 : k ^ 3 = 1 := hA.2 k hkA
      have hact : IsPGroup 3 ((Subgroup.zpowers k).subgroupOf C) := by
        have hdvd : orderOf k ∣ 3 ^ 1 := by
          rw [pow_one]
          exact orderOf_dvd_of_pow_eq_one hk3
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
        refine IsPGroup.of_card (n := j) ?_
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (Subgroup.zpowers_le.mpr (hAC hkA))).toEquiv, Nat.card_zpowers, hj]
      have hvC : v ∈ C := hθC (KFTools.inSubgroup_twoFitting_le θc hv)
      have htarget : π ⟨v, hvC⟩ ∈ Subgroup.centralizer
          (((Subgroup.zpowers k).subgroupOf C).map π : Set (C ⧸ O.subgroupOf C)) := by
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp ha)
        have haS : (a : G) ∈ S := by rw [← hj]; exact S.zpow_mem hkS j
        have hcomm : a * ⟨v, hvC⟩ * a⁻¹ * (⟨v, hvC⟩ : C)⁻¹ ∈ O.subgroupOf C :=
          Subgroup.mem_subgroupOf.mpr (by simpa using haS.2 v hv)
        rw [← QuotientGroup.ker_mk' (O.subgroupOf C), ← hπ, MonoidHom.mem_ker] at hcomm
        simp only [map_mul, map_inv] at hcomm
        exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hcomm)
      obtain ⟨e, he, hev⟩ :=
        exists_centralizer_preimage_of_pGroup_prime_complement_kernel
          3 Nat.prime_three π (QuotientGroup.mk'_surjective _) hker _ hact _ htarget
      have ho : (e : G)⁻¹ * v ∈ O := by
        have h' : e⁻¹ * ⟨v, hvC⟩ ∈ O.subgroupOf C := by
          rw [← QuotientGroup.ker_mk' (O.subgroupOf C), ← hπ, MonoidHom.mem_ker, map_mul,
            map_inv, hev, inv_mul_cancel]
        simpa using Subgroup.mem_subgroupOf.mp h'
      have heF : (e : G) ∈ F₂ := by
        have : (e : G) = v * ((e : G)⁻¹ * v)⁻¹ := by group
        rw [this]
        exact F₂.mul_mem hv (F₂.inv_mem (hOF ho))
      have hek : (e : G) * k = k * e := by
        have := Subgroup.mem_centralizer_iff.mp he ⟨k, hAC hkA⟩
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers k))
        exact (congrArg Subtype.val this).symm
      have hey : (e : G) ∈ C ⊓ Subgroup.centralizer ({y} : Set G) := by
        refine ⟨e.2, ?_⟩
        have hsub : Subgroup.zpowers c ⊔ Subgroup.zpowers k ≤
            Subgroup.centralizer ({(e : G)} : Set G) :=
          sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_singleton_iff.mp e.2).symm))
            (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hek.symm))
        have hyc' : y ∈ Subgroup.centralizer ({(e : G)} : Set G) :=
          hsub (hplane ▸ (le_sup_right : Subgroup.zpowers y ≤ _) (Subgroup.mem_zpowers y))
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hyc').symm
      have hqe : q * e * q⁻¹ * (e : G)⁻¹ ∈ O := by
        have hP' : q * e * q⁻¹ * (e : G)⁻¹ ∈ P := by
          have := (Subgroup.mem_normalizer_iff.mp
            (SteinbergBY.le_normalizer_inSubgroup_pCore 2 _ hey) q⁻¹).mp (P.inv_mem hq)
          have e' : q * e * q⁻¹ * (e : G)⁻¹ = q * ((e : G) * q⁻¹ * (e : G)⁻¹) := by group
          rw [e']
          exact P.mul_mem hq this
        have hF' : q * e * q⁻¹ * (e : G)⁻¹ ∈ F₂ :=
          F₂.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCSt (hPC hq)).1 _).mp heF)
            (F₂.inv_mem heF)
        obtain ⟨n, hn⟩ := TwoStarComponents.exists_pow_two_pow_eq_one
          (SteinbergBY.isPGroup_inSubgroup_pCore 2 _) hP'
        exact mem_pCore_of_mem_twoFitting hF' hn
      set o := (e : G)⁻¹ * v with ho_def
      have hvo : v = e * o := by rw [ho_def, mul_inv_cancel_left]
      have hqo : q * o * q⁻¹ * o⁻¹ ∈ O :=
        O.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCSt (hPC hq)).2 o).mp ho) (O.inv_mem ho)
      have heO : (e : G) ∈ Subgroup.normalizer (O : Set G) := (hCSt e.2).2
      have e' : q * v * q⁻¹ * v⁻¹ =
          (q * e * q⁻¹ * (e : G)⁻¹) * ((e : G) * (q * o * q⁻¹ * o⁻¹) * (e : G)⁻¹) := by
        rw [hvo]; group
      rw [e']
      exact O.mul_mem hqe ((Subgroup.mem_normalizer_iff.mp heO _).mp hqo)
    rw [Subgroup.commutator_le]
    intro q hq x hx
    have hxq : x * q⁻¹ * x⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hAP hx) q⁻¹).mp (P.inv_mem hq)
    have e : ⁅q, x⁆ = q * (x * q⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact S.mul_mem (hPS hq) (hPS hxq)
  ·
    have hA' := zpowers_sup_sup_eq hA27 hcA hc1 hyA hyc hkA hkE
    rw [Subgroup.commutator_le]
    intro q hq x hx
    have hqSt : q ∈ St := hCSt (hPC hq)
    let M : Subgroup G :=
      { carrier := {x | x ∈ St ∧ q * x * q⁻¹ * x⁻¹ ∈ S}
        mul_mem' := by
          rintro x₁ x₂ ⟨h₁St, h₁⟩ ⟨h₂St, h₂⟩
          refine ⟨St.mul_mem h₁St h₂St, ?_⟩
          have hconj : x₁ * (q * x₂ * q⁻¹ * x₂⁻¹) * x₁⁻¹ ∈ S :=
            ⟨St.mul_mem (St.mul_mem h₁St h₂.1) (St.inv_mem h₁St),
              conj_mem_sectionCentralizer h₁St.1 h₁St.2 h₂.2⟩
          have e : q * (x₁ * x₂) * q⁻¹ * (x₁ * x₂)⁻¹ =
              (q * x₁ * q⁻¹ * x₁⁻¹) * (x₁ * (q * x₂ * q⁻¹ * x₂⁻¹) * x₁⁻¹) := by group
          rw [e]
          exact S.mul_mem h₁ hconj
        one_mem' := ⟨St.one_mem, by simp⟩
        inv_mem' := by
          rintro x₁ ⟨h₁St, h₁⟩
          refine ⟨St.inv_mem h₁St, ?_⟩
          have hconj : x₁⁻¹ * (q * x₁ * q⁻¹ * x₁⁻¹)⁻¹ * x₁⁻¹⁻¹ ∈ S :=
            ⟨St.mul_mem (St.mul_mem (St.inv_mem h₁St) (S.inv_mem h₁).1)
                (St.inv_mem (St.inv_mem h₁St)),
              conj_mem_sectionCentralizer (Subgroup.inv_mem _ h₁St.1)
                (Subgroup.inv_mem _ h₁St.2) (S.inv_mem h₁).2⟩
          have e : q * x₁⁻¹ * q⁻¹ * x₁⁻¹⁻¹ = x₁⁻¹ * (q * x₁ * q⁻¹ * x₁⁻¹)⁻¹ * x₁⁻¹⁻¹ := by
            group
          rw [e]
          exact hconj }
    have hcM : c ∈ M := by
      refine ⟨hCSt (hAC hcA), ?_⟩
      have hqc : q * c = c * q := Subgroup.mem_centralizer_singleton_iff.mp (hPC hq)
      rw [hqc, mul_inv_cancel_right, mul_inv_cancel]
      exact S.one_mem
    have hyM : y ∈ M := by
      refine ⟨hCSt (hAC hyA), ?_⟩
      have hqy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.mp
        ((SteinbergBY.inSubgroup_pCore_le 2 _).trans inf_le_right hq)
      rw [hqy, mul_inv_cancel_right, mul_inv_cancel]
      exact S.one_mem
    have hkM : k ∈ M := by
      refine ⟨hCSt (hAC hkA), ?_, ?_⟩
      · exact St.mul_mem (St.mul_mem (St.mul_mem hqSt hkS.1) (St.inv_mem hqSt))
          (St.inv_mem hkS.1)
      · exact commutator_mem_sectionCentralizer hqSt.1 hqSt.2 hkS.1.1 hkS.1.2 hkS.2
    have hAM : A ≤ M := by
      rw [← hA']
      exact sup_le (sup_le (Subgroup.zpowers_le.mpr hcM) (Subgroup.zpowers_le.mpr hyM))
        (Subgroup.zpowers_le.mpr hkM)
    rw [commutatorElement_def]
    exact (hAM hx).2

theorem twoStarConditionAt_of_theta {A : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hA27 : Nat.card A = 27) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {V : Subgroup G}
    (hV9 : Nat.card V = 9) (hVA : V ≤ A) (hcV : c ∉ V) {k : G} (hkA : k ∈ A)
    (hkc : k ∉ Subgroup.zpowers c)
    (hk : ∀ v ∈ inSubgroup twoFitting (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G))),
      k * v * k⁻¹ * v⁻¹ ∈ inSubgroup (CFSG.pCore 2) (inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({c} : Set G))))
    (hJθ : ∀ y ∈ A, y ∉ Subgroup.zpowers c →
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G)), A⁆ ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)))
    (hTθ : ∀ u : G, (∀ y ∈ A, y ∉ Subgroup.zpowers c →
      u ∈ inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({c} : Set G) ⊓
          Subgroup.centralizer ({y} : Set G))) →
        u ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G))) :
    TwoStarConditionAt A c := by
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu c hcA)
  have hVe : CFSG.Assembly.IsElemAbelian 3 V :=
    ⟨⟨⟨fun u v => Subtype.ext (hAc u (hVA u.2) v (hVA v.2))⟩⟩, fun u hu => hA.2 u (hVA hu)⟩
  have hVc : ∀ v ∈ V, v ≠ 1 → v ∉ Subgroup.zpowers c := by
    intro v hv hv1 hvc
    apply hcV
    have hz := TheoremO.zpowers_eq_of_mem_of_ne_one hc3 hvc hv1
    exact Subgroup.zpowers_le.mpr hv (hz ▸ Subgroup.mem_zpowers c)
  refine twoStarConditionAt_of_centralizers hAc hcA hc3 hkA hkc
    (fun y hyA hyc => commutator_le_pCore_of_theta hA hA27 hcA hc1 hyA hyc hkA hkc hk
      (hJθ y hyA hyc)) fun u hu => ?_
  refine mem_pCore_of_theta hVe (by rw [hV9]; norm_num) (hVA.trans hAC) (fun v hv hv1 => ?_)
    (hTθ u hu)
  exact hu v (hVA hv) (hVc v hv hv1)

end TwoStarProof

end CFSG.RankThree.PartTwo.Sec11
