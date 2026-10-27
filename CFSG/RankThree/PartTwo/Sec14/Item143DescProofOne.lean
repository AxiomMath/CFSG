module

import CFSG.RankThree.PartTwo.Sec14.Item143DescProofMax
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def Step143HJCompOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∉ omegaA A →
      ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → a ∈ B →
        IsLBConfig A B b d Lb → Subgroup.zpowers a ≠ Subgroup.zpowers d →
        ∀ X ∈ thetaComponentsAt 3 a, lB A B ≤ X →
          X = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) X

namespace Desc143X

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_of_mem_closure_pair {x u v w : G}
    (hu : x ∈ Subgroup.centralizer ({u} : Set G)) (hv : x ∈ Subgroup.centralizer ({v} : Set G))
    (hw : w ∈ Subgroup.closure {u, v}) : x ∈ Subgroup.centralizer ({w} : Set G) := by
  have hle : Subgroup.closure {u, v} ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hu).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hv).symm
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm

theorem zpowers_eq_of_mem {u v : G} (hu : orderOf u = 3) (hv : orderOf v = 3)
    (huv : u ∈ Subgroup.zpowers v) : Subgroup.zpowers u = Subgroup.zpowers v := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huv) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hu, hv]

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {g : G}
    (hH : g ∈ Subgroup.normalizer (H : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem closure_pair_eq_of_not_mem {A B : Subgroup G} (hA : Late.IsE27 A)
    (hB : IsHyperplane A B) {u v : G} (huB : u ∈ B) (hvB : v ∈ B) (hu1 : u ≠ 1)
    (hvu : v ∉ Subgroup.zpowers u) : Subgroup.closure {u, v} = B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB9 : Nat.card B = 9 := by have := hB.2; rw [hA.2] at this; omega
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hv1 : v ≠ 1 := fun h => hvu (h ▸ one_mem _)
  have hou : orderOf u = 3 := orderOf_eq_prime (hA.1.2 u (hB.1 huB)) hu1
  have hov : orderOf v = 3 := orderOf_eq_prime (hA.1.2 v (hB.1 hvB)) hv1
  have hdisj : Subgroup.zpowers u ⊓ Subgroup.zpowers v = ⊥ :=
    Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hov hvu
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (Subgroup.zpowers u)
    (Subgroup.zpowers v) fun x hx y hy =>
      hcomm x ((Subgroup.zpowers_le.mpr (hB.1 huB)) hx) y
        ((Subgroup.zpowers_le.mpr (hB.1 hvB)) hy)
  rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hou, hov] at hcard
  have hle : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ Subgroup.closure {u, v} :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert u _)))
      (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem u rfl)))
  have hclB : Subgroup.closure {u, v} ≤ B := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact huB
    · exact hvB
  refine Subgroup.eq_of_le_of_card_ge hclB ?_
  rw [hB9]
  calc 9 = Nat.card (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup G) := by omega
    _ ≤ Nat.card (Subgroup.closure {u, v}) := Subgroup.card_le_of_le hle

theorem inf_centralizer_eq_of_config {A B Lb : Subgroup G} {a b d : G} (hA : Late.IsE27 A)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) (haB : a ∈ B) (ha1 : a ≠ 1)
    (hab : a ∉ Subgroup.zpowers b) :
    Lb ⊓ Subgroup.centralizer ({a} : Set G) = Lb ⊓ Subgroup.centralizer ({d} : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, -, hLbeq, -, -⟩ := hc
  have hLb : Lb ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt (hLbeq ▸ Set.mem_singleton Lb : Lb ∈ lA A b).1
  have hbB : b ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a (hB.1 haB)) ha1
  by_cases had : a ∈ Subgroup.zpowers d
  · have hod : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d (hB.1 hdB)) hd1
    rw [centralizer_singleton_eq_of_zpowers_eq (zpowers_eq_of_mem hoa hod had)]
  · have hba : b ∉ Subgroup.zpowers a := by
      intro hb
      have hob : orderOf b = 3 := orderOf_eq_prime (hA.1.2 b (hB.1 hbB)) hb1
      exact hab ((zpowers_eq_of_mem hob hoa hb) ▸ Subgroup.mem_zpowers a)
    have hab' : Subgroup.closure {a, b} = B := closure_pair_eq_of_not_mem hA hB haB hbB ha1 hba
    ext x
    constructor
    · rintro ⟨hxL, hxa⟩
      exact ⟨hxL, mem_centralizer_of_mem_closure_pair hxa (hLb hxL) (hab' ▸ hdB)⟩
    · rintro ⟨hxL, hxd⟩
      exact ⟨hxL, mem_centralizer_of_mem_closure_pair (hLb hxL) hxd (hBbd ▸ haB)⟩

theorem commutator_mem_theta_of_ne {A X Y : Subgroup G} {a : G}
    (hX : X ∈ thetaComponentsAt 3 a) (hY : Y ∈ thetaComponentsAt 3 a) (hne : Y ≠ X)
    (hAX : A ≤ Subgroup.zpowers a ⊔ X) {y : G} (hy : y ∈ Y) {α : G} (hα : α ∈ A) :
    ⁅y, α⁆ ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  have hYC : Y ≤ C := le_centralizer_of_mem_thetaComponentsAt hY
  have hXC : X ≤ C := le_centralizer_of_mem_thetaComponentsAt hX
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta C
  have hyC := hYC hy
  have hYX := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hY hX hne
  let S : Subgroup G :=
    { carrier := {g | g ∈ C ∧ ⁅y, g⁆ ∈ T}
      mul_mem' := by
        rintro g₁ g₂ ⟨hg₁, h₁⟩ ⟨hg₂, h₂⟩
        refine ⟨C.mul_mem hg₁ hg₂, ?_⟩
        have e : ⁅y, g₁ * g₂⁆ = ⁅y, g₁⁆ * (g₁ * ⁅y, g₂⁆ * g₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact T.mul_mem h₁ ((Subgroup.mem_normalizer_iff.mp (hCT hg₁) _).mp h₂)
      one_mem' := ⟨C.one_mem, by simp only [commutatorElement_def]; group; exact T.one_mem⟩
      inv_mem' := by
        rintro g ⟨hg, h₁⟩
        refine ⟨C.inv_mem hg, ?_⟩
        have e : ⁅y, g⁻¹⁆ = g⁻¹ * ⁅y, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hCT (C.inv_mem hg)) _).mp (T.inv_mem h₁) }
  have haS : a ∈ S := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
    have : ⁅y, a⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
    rw [this]
    exact T.one_mem
  have hXS : X ≤ S := fun ξ hξ => ⟨hXC hξ, hYX (Subgroup.commutator_mem_commutator hy hξ)⟩
  have hle : Subgroup.zpowers a ⊔ X ≤ S := sup_le (Subgroup.zpowers_le.mpr haS) hXS
  exact (hle (hAX hα)).2

theorem residual_inf_le_theta {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) {N : Subgroup G}
    (hN : inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) ≤
      Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N) :
    inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) ⊓ N ≤
      inSubgroup (aschbacherSolvableCore 3) Lb := by
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  obtain ⟨hdL, -, hq, hZ, -⟩ := Item148HJ.resProj_facts h hB hc
  set M : Subgroup ↥J := (J ⊓ N).subgroupOf J with hM
  have hMn : M.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hM, Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨(g * x * g⁻¹ : ↥J).2, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (hN g.2) x).mp hx.2
    simpa using this
  have hM3 : ¬ 3 ∣ Nat.card M := by
    intro h3
    apply hN3
    have e : Nat.card M = Nat.card (J ⊓ N : Subgroup G) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [e] at h3
    exact h3.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hker := Item148HJ.le_ker_of_normal (Item148HJ.resProj Lb d) hq hZ hMn hM3
  intro x hx
  have hxM : (⟨x, hx.1⟩ : ↥J) ∈ M := by rw [hM, Subgroup.mem_subgroupOf]; exact hx
  exact (Item148HJ.mem_ker_resProj _).mp (hker hxM)

theorem exists_mem_le_residual (h48 : Sec4.Item4_8) {A L B Lb : Subgroup G} {c a b d : G}
    (h : Sec14Std G A c L) (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    (haB : a ∈ B) (ha1 : a ≠ 1) (hab : a ∉ Subgroup.zpowers b) :
    ∃ X ∈ thetaComponentsAt 3 a,
      inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) ≤ X := by
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hA : Late.IsE27 A := h.isE27'
  have hJ := Item148HJ.j2_of_isLBConfig hc
  obtain ⟨hb1, hd1⟩ := hc.ne_one hB hA
  have heq := inf_centralizer_eq_of_config hA hB hc haB ha1 hab
  obtain ⟨-, hbΩ, hLbeq, -, hdL, S, hdS, hSd⟩ := hc
  have hLb : Lb ∈ lA A b := hLbeq ▸ Set.mem_singleton Lb
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({a} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian ha1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ hdL hd1
    ⟨S, hdS, hSd⟩
  rw [← heq] at hJq ⊢
  exact exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hbA (hB.1 haB) hb1 hLb.1 hJq

structure One (A : Subgroup G) (c : G) (L : Subgroup G) (a b d : G) (B Lb : Subgroup G) :
    Prop where
  std : Sec14Std G A c L
  mem : a ∈ A
  ne_one : a ≠ 1
  not_mem_omegaA : Subgroup.zpowers a ∉ omegaA A
  hyp : IsHyperplane A B
  mem_hyp : a ∈ B
  config : IsLBConfig A B b d Lb
  ne_d : Subgroup.zpowers a ≠ Subgroup.zpowers d

namespace One

variable {A L B Lb : Subgroup G} {c a b d : G}

theorem not_mem_zpowers_of_mem_omegaA (h : One A c L a b d B Lb) {e : G}
    (he : Subgroup.zpowers e ∈ omegaA A) : a ∉ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hae
  obtain ⟨heA, he3, -⟩ := zpowers_mem_omegaA_iff.mp he
  have hoe : orderOf e = 3 := by rwa [Nat.card_zpowers] at he3
  have hoa : orderOf a = 3 := orderOf_eq_prime (h.std.isE27'.1.2 a h.mem) h.ne_one
  exact h.not_mem_omegaA (zpowers_eq_of_mem hoa hoe hae ▸ he)

theorem not_mem_zpowers_b (h : One A c L a b d B Lb) : a ∉ Subgroup.zpowers b :=
  h.not_mem_zpowers_of_mem_omegaA h.config.2.1

theorem closure_eq (h : One A c L a b d B Lb) : Subgroup.closure {a, b} = B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.std.isE27'
  have hbB : b ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  obtain ⟨hb1, -⟩ := h.config.ne_one h.hyp hA
  refine closure_pair_eq_of_not_mem hA h.hyp h.mem_hyp hbB h.ne_one fun hb => ?_
  have hob : orderOf b = 3 := orderOf_eq_prime (hA.1.2 b (h.hyp.1 hbB)) hb1
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a h.mem) h.ne_one
  exact h.not_mem_zpowers_b ((zpowers_eq_of_mem hob hoa hb) ▸ Subgroup.mem_zpowers a)

theorem inf_lb_eq (h : One A c L a b d B Lb) : B ⊓ Lb = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA := h.std.isE27'
  have hS := Item148HJ.sec14Std_of_isLBConfig h.std h.config
  obtain ⟨hbL, -, -⟩ := j2_point_facts hS.toSec13Data (Item148HJ.j2_of_isLBConfig h.config)
  obtain ⟨-, hd1⟩ := h.config.ne_one h.hyp hA
  obtain ⟨hBbd, -, -, -, hdL, -⟩ := h.config
  have hbB : b ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert b {d})
  have hdB : d ∈ B := hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hod : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d (h.hyp.1 hdB)) hd1
  have hB9 : Nat.card B = 9 := by have := h.hyp.2; rw [hA.2] at this; omega
  have hBL : Nat.card (B ⊓ Lb : Subgroup G) ≤ 3 := by
    have hdvd : Nat.card (B ⊓ Lb : Subgroup G) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hB9]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases i
    · rw [hik]; norm_num
    · rw [hik]; norm_num
    · exfalso
      apply hbL
      have heqB : B ⊓ Lb = B :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hik, hB9]; norm_num)
      have hb' : b ∈ B ⊓ Lb := by rw [heqB]; exact hbB
      exact hb'.2
  have hdBL : d ∈ B ⊓ Lb := ⟨hdB, hdL⟩
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdBL)
    (by rw [Nat.card_zpowers, hod]; exact hBL)).symm

theorem not_mem_lb (h : One A c L a b d B Lb) : a ∉ Lb := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro haL
  have had : a ∈ B ⊓ Lb := ⟨h.mem_hyp, haL⟩
  rw [h.inf_lb_eq] at had
  have hA := h.std.isE27'
  obtain ⟨-, hd1⟩ := h.config.ne_one h.hyp hA
  have hdB : d ∈ B := h.config.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl)
  have hod : orderOf d = 3 := orderOf_eq_prime (hA.1.2 d (h.hyp.1 hdB)) hd1
  have hoa : orderOf a = 3 := orderOf_eq_prime (hA.1.2 a h.mem) h.ne_one
  exact h.ne_d (zpowers_eq_of_mem hoa hod had)

theorem le_sup (h : One A c L a b d B Lb) : A ≤ Subgroup.zpowers a ⊔ (A ⊓ Lb) := by
  have hA := h.std.isE27'
  have hS := Item148HJ.sec14Std_of_isLBConfig h.std h.config
  obtain ⟨-, h9, -⟩ := j2_point_facts hS.toSec13Data (Item148HJ.j2_of_isLBConfig h.config)
  have hH : IsHyperplane A (A ⊓ Lb) := ⟨inf_le_left, by rw [hA.2, h9]⟩
  rw [sup_comm]
  exact le_sup_zpowers_of_not_mem hA hH h.mem fun ha => h.not_mem_lb ha.2

theorem lB_eq (h : One A c L a b d B Lb) :
    lB A B = inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) :=
  Item148HJ.lB_eq_residual h.std h.hyp h.config

theorem le_sup_of_le (h : One A c L a b d B Lb) {X : Subgroup G} (hJX : lB A B ≤ X) :
    A ≤ Subgroup.zpowers a ⊔ X :=
  h.le_sup.trans (sup_le_sup_left ((Item148HJ.inf_le_residual h.std h.hyp h.config).trans
    (h.lB_eq ▸ hJX)) _)

theorem exists_mem (h : One A c L a b d B Lb) (h48 : Sec4.Item4_8) :
    ∃ X ∈ thetaComponentsAt 3 a, lB A B ≤ X := by
  rw [h.lB_eq]
  exact exists_mem_le_residual h48 h.std h.hyp h.config h.mem_hyp h.ne_one h.not_mem_zpowers_b

theorem conj_eq (h : One A c L a b d B Lb) {X : Subgroup G} (hX : X ∈ thetaComponentsAt 3 a)
    (hJX : lB A B ≤ X) {g : G} (hg : g ∈ Subgroup.centralizer ({a} : Set G)) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  by_contra hne
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set T := inSubgroup (aschbacherSolvableCore 3) C with hT
  set J := inSubgroup perfectResidual (Lb ⊓ Subgroup.centralizer ({d} : Set G)) with hJ
  have hJX' : J ≤ X := by rw [hJ, ← h.lB_eq]; exact hJX
  have hAX : A ≤ Subgroup.zpowers a ⊔ X := h.le_sup_of_le hJX
  have hAmax := h.std.maximal_isElemAbelian
  have hAC : A ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (h.std.isE27'.1.1.is_comm.comm ⟨x, hx⟩ ⟨a, h.mem⟩))
  have hCT : C ≤ Subgroup.normalizer (T : Set G) := Sec6.le_normalizer_theta C
  set Y := X.map (MulAut.conj g).toMonoidHom with hYdef
  have hY : Y ∈ thetaComponentsAt 3 a := Sec6.map_conj_mem_thetaComponentsAt hg hX
  have hYC : Y ≤ C := le_centralizer_of_mem_thetaComponentsAt hY
  obtain ⟨a₀, ha₀, ha₀d, -⟩ := Item148HJ.exists_mem_not_mem_zpowers h.std h.hyp h.config
  obtain ⟨j, hj, hjθ⟩ := Item148HJ.exists_commutator_not_mem h.std h.hyp h.config ha₀ ha₀d
  have ha₀J : a₀ ∈ J := Item148HJ.inf_le_residual h.std h.hyp h.config ha₀
  have hJC : J ≤ C := (Item148HJ.residual_le_centralizer h.config).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr h.mem_hyp))
  set x := g * a₀ * g⁻¹ with hxdef
  have hxY : x ∈ Y := ⟨a₀, hJX' ha₀J, rfl⟩
  have hjY : g * j * g⁻¹ ∈ Y := ⟨j, hJX' hj, rfl⟩
  have hxC : x ∈ C := hYC hxY
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, conj_pow, h.std.isE27'.1.2 a₀ ha₀.1, mul_one, mul_inv_cancel]
  have hfix : ∀ α ∈ A, x⁻¹ * (α * x * α⁻¹) ∈ T := by
    intro α hα
    have := commutator_mem_theta_of_ne hX hY hne hAX (Y.inv_mem hxY) hα
    have e : x⁻¹ * (α * x * α⁻¹) = ⁅x⁻¹, α⁆ := by
      simp only [commutatorElement_def, inv_inv]; group
    rw [e]
    exact this
  obtain ⟨α, hα, hαx⟩ := exists_mem_inv_mul_mem_theta hAmax (hAC.trans Subgroup.le_normalizer)
    hxC hx3 hfix
  set j' := g * j * g⁻¹ with hj'
  have hj'C : j' ∈ C := hYC hjY
  have h1 : ⁅j', α⁆ ∈ T := commutator_mem_theta_of_ne hX hY hne hAX hjY hα
  set t := α⁻¹ * x with ht
  have h2 : ⁅j', t⁆ ∈ T := by
    rw [commutatorElement_def]
    exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp (hCT hj'C) t).mp hαx) (T.inv_mem hαx)
  have hxt : x = α * t := by rw [ht]; group
  have h3 : ⁅j', x⁆ ∈ T := by
    have e : ⁅j', x⁆ = ⁅j', α⁆ * (α * ⁅j', t⁆ * α⁻¹) := by
      rw [hxt]; simp only [commutatorElement_def]; group
    rw [e]
    exact T.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp (hCT (hAC hα)) _).mp h2)
  have h4 : ⁅j, a₀⁆ ∈ T := by
    have e : ⁅j, a₀⁆ = g⁻¹ * ⁅j', x⁆ * g⁻¹⁻¹ := by
      rw [hj', hxdef]; simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hCT (C.inv_mem hg)) _).mp h3
  have h5 : ⁅j, a₀⁆ ∈ J := by
    rw [commutatorElement_def]
    exact J.mul_mem (J.mul_mem (J.mul_mem hj ha₀J) (J.inv_mem hj)) (J.inv_mem ha₀J)
  exact hjθ (residual_inf_le_theta h.std h.hyp h.config (hJC.trans hCT)
    (Sec6.theta_solvable_and_not_dvd C).2 ⟨h5, h4⟩)

theorem le_normalizer (h : One A c L a b d B Lb) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) (hJX : lB A B ≤ X) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) := fun _g hg =>
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (h.conj_eq hX hJX hg)

theorem le_normalizer_sup (h : One A c L a b d B Lb) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) (hJX : lB A B ≤ X) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) :=
  fun _g hg => mem_normalizer_sup (le_normalizer_pPrimeCoreOf 3 _ hg)
    (h.le_normalizer hX hJX hg)

theorem lB_le (h : One A c L a b d B Lb) (h48 : Sec4.Item4_8) {X : Subgroup G}
    (hX : X ∈ thetaComponentsAt 3 a) (hJX : lB A B ≤ X) {D : Subgroup G}
    (hD : IsHyperplane A D) (haD : a ∈ D) : lB A D ≤ X := by
  refine iSup_le fun b' => iSup_le fun d' => iSup_le fun L' => iSup_le fun hc' => ?_
  set J' := inSubgroup perfectResidual (L' ⊓ Subgroup.centralizer ({d'} : Set G)) with hJ'
  set C := Subgroup.centralizer ({a} : Set G) with hC
  have hab' : a ∉ Subgroup.zpowers b' := h.not_mem_zpowers_of_mem_omegaA hc'.2.1
  obtain ⟨X', hX', hJX'⟩ := exists_mem_le_residual h48 h.std hD hc' haD h.ne_one hab'
  by_cases hXX : X' = X
  · exact hXX ▸ hJX'
  exfalso
  obtain ⟨e, he, hed, -⟩ := Item148HJ.exists_mem_not_mem_zpowers h.std hD hc'
  obtain ⟨j, hj, hjθ⟩ := Item148HJ.exists_commutator_not_mem h.std hD hc' he hed
  have heJ : e ∈ J' := Item148HJ.inf_le_residual h.std hD hc' he
  have h1 := commutator_mem_theta_of_ne hX hX' hXX (h.le_sup_of_le hJX) (hJX' hj) he.1
  have hJC : J' ≤ C := (Item148HJ.residual_le_centralizer hc').trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haD))
  have h5 : ⁅j, e⁆ ∈ J' := by
    rw [commutatorElement_def]
    exact J'.mul_mem (J'.mul_mem (J'.mul_mem hj heJ) (J'.inv_mem hj)) (J'.inv_mem heJ)
  exact hjθ (residual_inf_le_theta h.std hD hc' (hJC.trans (Sec6.le_normalizer_theta C))
    (Sec6.theta_solvable_and_not_dvd C).2 ⟨h5, h1⟩)

theorem pPrimeCoreOf_le_delta (h : One A c L a b d B Lb) :
    pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ≤
      delta A (lB A) (Subgroup.centralizer ({a} : Set G)) := by
  have hmem := sup_pPrimeCoreOf_mem_scriptQ (LB := lB A) h.std.isE27'
    h.std.maximal_isElemAbelian h.mem
  exact le_sup_left.trans (le_delta hmem.1 hmem.2)

theorem descX (h : One A c L a b d B Lb) (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne)
    (hgen : lB A B ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G))) :
    ∃ X : Subgroup G,
      X ≤ delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ∧
      (∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
        lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) ∧
      Subgroup.centralizer ({a} : Set G) ≤
        Subgroup.normalizer
          ((pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X : Subgroup G) : Set G) ∧
      (X ∈ thetaComponentsAt 3 a ∧
        X = lB A (Subgroup.closure {a, b}) ⊔ inSubgroup (aschbacherSolvableCore 3) X ∧
        Subgroup.zpowers a ≠ Subgroup.zpowers d) := by
  obtain ⟨X, hX, hJX⟩ := h.exists_mem h48
  have hXeq := hcomp G A c L h.std a h.mem h.ne_one h.not_mem_omegaA B b d Lb h.hyp h.mem_hyp
    h.config h.ne_d X hX hJX
  have hθ : inSubgroup (aschbacherSolvableCore 3) X ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) := by
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hX]
    exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf _)
  refine ⟨X, ?_, fun D hD haD => (h.lB_le h48 hX hJX hD haD).trans le_sup_right,
    h.le_normalizer_sup hX hJX, hX, by rw [h.closure_eq]; exact hXeq, h.ne_d⟩
  rw [hXeq]
  exact sup_le hgen (hθ.trans h.pPrimeCoreOf_le_delta)

end One

end Desc143X

end CFSG.RankThree.PartTwo.Sec14
