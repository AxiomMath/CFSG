module

public import CFSG.RankThree.PartOne.S13K.Pair134Basic
public import CFSG.GroupTheory.LocalCores.Components
import CFSG.RankThree.PartOne.S9.Vanishing.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne

theorem IsKt.le_kZero {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {t : MulAut E}
    {K : Subgroup G} (h : IsKt p E t K) : K ≤ kZero p E t := by
  by_cases hex : ∃ f, kExceptional p (kZero p E t) f
  · obtain ⟨f, hf⟩ := hex
    exact (h.1 f hf).1
  · exact (h.2 hex).le

theorem kZero_le_centralizer_fixed {G : Type} [Group G] (p : ℕ) (E : Subgroup G) (t : MulAut E) :
    kZero p E t ≤ Subgroup.centralizer (autFixedInG E t : Set G) := by
  unfold kZero pElementSubgroup
  rw [Subgroup.closure_le]
  intro x hx
  exact Subgroup.map_subtype_le _ hx.1

theorem isPGroup_of_le_elementaryAbelian {G : Type} [Group G] {p : ℕ} {E P : Subgroup G}
    (hE : IsElementaryAbelian p ↥E) (hPE : P ≤ E) : IsPGroup p ↥P := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have := hE
  simpa using elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) (x : G) (hPE x.2)

theorem exists_fixed_mem_coset {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P U V : Subgroup G} (hP : IsPGroup p P) (hPU : P ≤ Subgroup.normalizer (U : Set G))
    (hPV : P ≤ Subgroup.normalizer (V : Set G)) (hV : ¬ p ∣ Nat.card V) {k : G}
    (hk : ∀ x ∈ P, x * k * x⁻¹ = k) (hex : ∃ u ∈ U, u⁻¹ * k ∈ V) :
    ∃ u ∈ U, u⁻¹ * k ∈ V ∧ ∀ x ∈ P, x * u * x⁻¹ = u := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u₀, hu₀U, hu₀V⟩ := hex
  have hconj : ∀ (x : P) (u : G), (u ∈ U ∧ u⁻¹ * k ∈ V) →
      ((x : G) * u * (x : G)⁻¹ ∈ U ∧ ((x : G) * u * (x : G)⁻¹)⁻¹ * k ∈ V) := by
    intro x u ⟨huU, huV⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hPU x.2) u).mp huU, ?_⟩
    have h1 : ((x : G) * u * (x : G)⁻¹)⁻¹ * k = (x : G) * (u⁻¹ * k) * (x : G)⁻¹ := by
      have hxk := hk x x.2
      calc ((x : G) * u * (x : G)⁻¹)⁻¹ * k = (x : G) * u⁻¹ * (x : G)⁻¹ * k := by group
        _ = (x : G) * u⁻¹ * (x : G)⁻¹ * ((x : G) * k * (x : G)⁻¹) := by rw [hxk]
        _ = (x : G) * (u⁻¹ * k) * (x : G)⁻¹ := by group
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.mp (hPV x.2) _).mp huV
  let S : Type := {u : G // u ∈ U ∧ u⁻¹ * k ∈ V}
  let _inst : MulAction P S :=
    { smul := fun x s => ⟨(x : G) * s.1 * (x : G)⁻¹, hconj x s.1 s.2⟩
      one_smul := fun s => by
        apply Subtype.ext
        change ((1 : P) : G) * s.1 * ((1 : P) : G)⁻¹ = s.1
        simp
      mul_smul := fun x y s => by
        apply Subtype.ext
        change ((x * y : P) : G) * s.1 * ((x * y : P) : G)⁻¹ =
          (x : G) * ((y : G) * s.1 * (y : G)⁻¹) * (x : G)⁻¹
        simp [mul_assoc] }
  have hsmul : ∀ (x : P) (s : S), ((x • s : S) : G) = (x : G) * s.1 * (x : G)⁻¹ := fun _ _ => rfl
  have hmod := hP.card_modEq_card_fixedPoints S
  have hcard : Nat.card S = Nat.card ↥(U ⊓ V) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨u₀⁻¹ * s.1, ?_, ?_⟩
        invFun := fun w => ⟨u₀ * w.1, ?_⟩
        left_inv := fun s => by
          apply Subtype.ext
          change u₀ * (u₀⁻¹ * s.1) = s.1
          group
        right_inv := fun w => by
          apply Subtype.ext
          change u₀⁻¹ * (u₀ * w.1) = w.1
          group }
    · exact U.mul_mem (U.inv_mem hu₀U) s.2.1
    · have h1 : u₀⁻¹ * s.1 = (u₀⁻¹ * k) * (s.1⁻¹ * k)⁻¹ := by group
      rw [h1]
      exact V.mul_mem hu₀V (V.inv_mem s.2.2)
    · refine ⟨U.mul_mem hu₀U w.2.1, ?_⟩
      have h1 : (u₀ * w.1)⁻¹ * k = w.1⁻¹ * (u₀⁻¹ * k) := by group
      rw [h1]
      exact V.mul_mem (V.inv_mem w.2.2) hu₀V
  have hnd : ¬ p ∣ Nat.card S := by
    rw [hcard]
    intro hdvd
    exact hV (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hne : (MulAction.fixedPoints P S).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : Nat.card (MulAction.fixedPoints P S) = 0 := by
      rw [hemp]
      simp
    rw [h0] at hmod
    exact hnd (Nat.modEq_zero_iff_dvd.mp hmod)
  obtain ⟨⟨u, hu⟩, hfix⟩ := hne
  refine ⟨u, hu.1, hu.2, fun x hx => ?_⟩
  have := congrArg Subtype.val (hfix ⟨x, hx⟩)
  rw [hsmul] at this
  exact this

theorem le_of_sectionTenRel_fixed {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {K I J P : Subgroup G} (hK : Group.IsPerfect ↥K) (hKI : K ≤ I) (hIJ : sectionTenRel p I J)
    (hP : IsPGroup p P) (hPI : P ≤ Subgroup.normalizer (I : Set G))
    (hPJ : P ≤ Subgroup.normalizer (J : Set G)) (hKP : K ≤ Subgroup.centralizer (P : Set G))
    (hKθ : K ≤ Subgroup.centralizer ((inSubgroup (aschbacherSolvableCore p) I ⊓
      Subgroup.centralizer (P : Set G) : Subgroup G) : Set G)) : K ≤ J := by
  classical
  set N := inSubgroup (aschbacherSolvableCore p) I with hN
  set C := Subgroup.centralizer (P : Set G) with hC
  obtain ⟨hNI, hNn⟩ := theta_le_and_normal p I
  obtain ⟨hNs, hNp⟩ := theta_solvable_and_not_dvd hp I
  have hIJ' : I = I ⊓ J ⊔ N := hIJ
  set H : Subgroup G := I ⊓ C with hH
  have hKH : K ≤ H := le_inf hKI hKP
  have hPU : P ≤ Subgroup.normalizer ((I ⊓ J : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hPI hx) h).mp h1,
        (Subgroup.mem_normalizer_iff.mp (hPJ hx) h).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hPI hx) h).mpr h1,
        (Subgroup.mem_normalizer_iff.mp (hPJ hx) h).mpr h2⟩
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p I (hPI hx)
  have hdecomp : ∀ k ∈ K, ∃ u ∈ (I ⊓ J) ⊓ C, ∃ v ∈ N ⊓ C, u * v = k := by
    intro k hk
    obtain ⟨m, hm, n, hn, hmn⟩ :=
      exists_mul_of_eq_sup_core (p := p) (M := I ⊓ J) inf_le_left hIJ' (hKI hk)
    have hex : ∃ u ∈ I ⊓ J, u⁻¹ * k ∈ N := ⟨m, hm, by rw [← hmn]; simpa using hn⟩
    have hkP : ∀ x ∈ P, x * k * x⁻¹ = k := fun x hx => by
      have := Subgroup.mem_centralizer_iff.mp (hKP hk) x hx
      rw [this]
      group
    obtain ⟨u, huU, huV, hufix⟩ := exists_fixed_mem_coset hp hP hPU hPN hNp hkP hex
    have huC : u ∈ C := by
      rw [hC, Subgroup.mem_centralizer_iff]
      intro x hx
      have := hufix x hx
      calc x * u = (x * u * x⁻¹) * x := by group
        _ = u * x := by rw [this]
    refine ⟨u, ⟨huU, huC⟩, u⁻¹ * k, ⟨huV, C.mul_mem (C.inv_mem huC) (hKP hk)⟩, by group⟩
  let Ng : Subgroup ↥H := (N ⊓ C).subgroupOf H
  let Pg : Subgroup ↥H := ((I ⊓ J) ⊓ C).subgroupOf H
  let Kg : Subgroup ↥H := K.subgroupOf H
  have hNgn : Ng.Normal := by
    refine ⟨fun n hn h => ?_⟩
    have hn' : (n : G) ∈ N ⊓ C := hn
    have hhI : (h : G) ∈ I := h.2.1
    have hhC : (h : G) ∈ C := h.2.2
    show ((h * n * h⁻¹ : ↥H) : G) ∈ N ⊓ C
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨?_, C.mul_mem (C.mul_mem hhC hn'.2) (C.inv_mem hhC)⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore p I hhI) _).mp hn'.1
  have hNle : N ⊓ C ≤ H := inf_le_inf_right C hNI
  have hNgs : Group.IsSolvable ↥Ng := by
    have h1 : Group.IsSolvable ↥(N ⊓ C) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion (inf_le_left : N ⊓ C ≤ N)))
        (Subgroup.inclusion_injective _)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNle).toMonoidHom) (MulEquiv.injective _)
  have hKgperf : Group.IsPerfect ↥Kg :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hKgP : Kg ≤ Pg ⊔ Ng := by
    intro k hk
    have hk' : (k : G) ∈ K := hk
    obtain ⟨u, hu, v, hv, huv⟩ := hdecomp k hk'
    have huH : u ∈ H := ⟨(hu.1).1, hu.2⟩
    have hvH : v ∈ H := hNle hv
    have hkuv : k = (⟨u, huH⟩ : ↥H) * ⟨v, hvH⟩ := Subtype.ext huv.symm
    rw [hkuv]
    exact Subgroup.mul_mem_sup (show (⟨u, huH⟩ : ↥H) ∈ Pg from hu)
      (show (⟨v, hvH⟩ : ↥H) ∈ Ng from hv)
  have hKgc : Kg ≤ Subgroup.centralizer (Ng : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have := Subgroup.mem_centralizer_iff.mp (hKθ (show (x : G) ∈ K from hx)) (y : G)
      (show (y : G) ∈ N ⊓ C from hy)
    simpa using this
  have hmain := le_of_perfect_of_centralizes hKgperf hNgn hNgs hKgP hKgc
  intro k hk
  have := hmain (show (⟨k, hKH hk⟩ : ↥H) ∈ Kg from hk)
  exact ((Subgroup.mem_inf.mp (Subgroup.mem_inf.mp this).1).2)

theorem isKt_centralizes_fixed_theta {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} {t : MulAut E} {K : Subgroup G} (hK : IsKt p E t K) {e : G}
    (he : e ∈ autFixedInG E t) :
    K ≤ Subgroup.centralizer
      ((inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) ⊓
        Subgroup.centralizer (autFixedInG E t : Set G) : Subgroup G) : Set G) := by
  classical
  set C₀ := Subgroup.centralizer (autFixedInG E t : Set G) with hC₀
  set M := Subgroup.centralizer ({e} : Set G) with hM
  set N := inSubgroup (aschbacherSolvableCore p) M with hN
  obtain ⟨hNM, hNn⟩ := theta_le_and_normal p M
  obtain ⟨hNs, -⟩ := theta_solvable_and_not_dvd hp M
  have hC₀M : C₀ ≤ M := by
    intro x hx
    rw [hM, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hx e he).symm
  let R : Subgroup ↥C₀ := (N ⊓ C₀).subgroupOf C₀
  have hRn : R.Normal := by
    refine ⟨fun r hr y => ?_⟩
    have hr' : (r : G) ∈ N ⊓ C₀ := hr
    show ((y * r * y⁻¹ : ↥C₀) : G) ∈ N ⊓ C₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine ⟨?_, C₀.mul_mem (C₀.mul_mem y.2 hr'.2) (C₀.inv_mem y.2)⟩
    exact (Subgroup.mem_normalizer_iff.mp
      (Vanish.le_normalizer_inSubgroup_aschbacherSolvableCore p M (hC₀M y.2)) _).mp hr'.1
  have hNC : N ⊓ C₀ ≤ C₀ := inf_le_right
  have hRs : Group.IsSolvable ↥R := by
    have h1 : Group.IsSolvable ↥(N ⊓ C₀) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.inclusion (inf_le_left : N ⊓ C₀ ≤ N)))
        (Subgroup.inclusion_injective _)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNC).toMonoidHom) (MulEquiv.injective _)
  have hlayer : layer ↥C₀ ≤ Subgroup.centralizer (R : Set ↥C₀) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalCores.component_solvable_centralizer hRs hRn.isSubnormal).2
  have hKl : K ≤ inSubgroup (fun K _ => layer K) C₀ := by
    refine (IsKt.le_kZero hK).trans ?_
    unfold kZero pElementSubgroup
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp (hKl hz)
  have hr' : (⟨r, hr.2⟩ : ↥C₀) ∈ R := hr
  have := Subgroup.mem_centralizer_iff.mp (hlayer hz') _ hr'
  exact congrArg Subtype.val this

theorem isKt_le_centralizer_fixed {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {t : MulAut E}
    {K : Subgroup G} (h : IsKt p E t K) : K ≤ Subgroup.centralizer (autFixedInG E t : Set G) :=
  (IsKt.le_kZero h).trans (kZero_le_centralizer_fixed p E t)

theorem kZero_conj_mem {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {t : MulAut E} {g : G}
    (hg : g ∈ Subgroup.centralizer (autFixedInG E t : Set G)) {x : G} (hx : x ∈ kZero p E t) :
    g * x * g⁻¹ ∈ kZero p E t := by
  set C₀ := Subgroup.centralizer (autFixedInG E t : Set G) with hC₀
  set Λ : Subgroup G := inSubgroup (fun K _ => layer K) C₀ with hΛ
  have hKdef : kZero p E t = pElementSubgroup p Λ := rfl
  have hΛconj : ∀ y ∈ Λ, g * y * g⁻¹ ∈ Λ := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hn : (layer ↥C₀).Normal := by
      have := LocalCores.layer_characteristic (G := ↥C₀)
      infer_instance
    have h1 := hn.conj_mem y' hy' ⟨g, hg⟩
    exact Subgroup.mem_map.mpr ⟨_, h1, by simp⟩
  have h1 : kZero p E t ≤ (kZero p E t).comap (MulAut.conj g).toMonoidHom := by
    rw [hKdef]
    unfold pElementSubgroup
    rw [Subgroup.closure_le]
    intro y hy
    refine Subgroup.subset_closure ⟨hΛconj y hy.1, ?_⟩
    obtain ⟨k, hk⟩ := hy.2
    refine ⟨k, ?_⟩
    have := MulEquiv.orderOf_eq (MulAut.conj g) y
    simpa [MulAut.conj_apply, hk] using this
  exact h1 hx

theorem kZero_mem_normalizer {G : Type} [Group G] {p : ℕ} {E : Subgroup G} {t : MulAut E} {g : G}
    (hg : g ∈ Subgroup.centralizer (autFixedInG E t : Set G)) :
    g ∈ Subgroup.normalizer (kZero p E t : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => kZero_conj_mem hg hy, fun hy => ?_⟩
  have := kZero_conj_mem (p := p) (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem E_le_normalizer_kZero {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E) (t : MulAut E) :
    E ≤ Subgroup.normalizer (kZero p E t : Set G) := by
  intro g hg
  refine kZero_mem_normalizer fun x hx => ?_
  have hxE : x ∈ E := Subgroup.map_subtype_le _ hx
  exact congrArg Subtype.val (hE.is_comm.comm (⟨x, hxE⟩ : ↥E) ⟨g, hg⟩)

theorem isKt_le_of_sectionTenRel {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElementaryAbelian p ↥E) {t : MulAut E} {K I J : Subgroup G} {e : G}
    (hK : IsKt p E t K) (hKperf : Group.IsPerfect ↥K) (he : e ∈ autFixedInG E t)
    (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) (hIJ : sectionTenRel p I J)
    (hEI : E ≤ Subgroup.normalizer (I : Set G)) (hEJ : E ≤ Subgroup.normalizer (J : Set G)) :
    K ≤ J := by
  have hθI : inSubgroup (aschbacherSolvableCore p) I ≤
      inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) := by
    rw [theta_eq_inf_of_mem_thetaComponentsAt hp hI]
    exact inf_le_right
  have hCE : autFixedInG E t ≤ E := Subgroup.map_subtype_le _
  exact le_of_sectionTenRel_fixed hp hKperf hKI hIJ (isPGroup_of_le_elementaryAbelian hE hCE)
    (hCE.trans hEI) (hCE.trans hEJ) (isKt_le_centralizer_fixed hK)
    ((isKt_centralizes_fixed_theta hp hK he).trans
      (Subgroup.centralizer_le (inf_le_inf_right _ hθI)))

end CFSG.RankThree.PartOne.S13K
