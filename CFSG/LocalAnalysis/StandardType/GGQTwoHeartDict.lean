module

public import CFSG.LocalAnalysis.StandardType.GGQTwoHeartDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2hD_root_xV {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (i : M.Λ) : M.root i M.xV = 0 := by
  have hxmem : M.xV ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
    rw [M.fixed_x]
    exact Submodule.subset_span (Set.mem_singleton M.xV)
  have hfix := (mem_ggFixedSubmodule_iff (p := 3) (ι := M.model) (N := ggAutomizer L Bs)
    (v := M.xV)).mp hxmem
  have hsi : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  have h1 := hfix (M.simple i) hsi
  rw [M.simple_apply i M.xV] at h1
  have h2 : M.root i M.xV • M.coroot i = 0 := sub_eq_self.mp h1
  have hc : M.coroot i ≠ 0 := by
    intro h
    have hp := M.pairing i i
    rw [M.isCartan.1, h, map_zero] at hp
    exact (by decide : (2 : ZMod 3) ≠ 0) hp.symm
  exact (smul_eq_zero.mp h2).resolve_right hc

private theorem ggQ2hD_mem_fixed_of_root_eq_zero {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (h : M.V) (hh : ∀ i, M.root i h = 0) :
    h ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
  rw [mem_ggFixedSubmodule_iff]
  intro φ hφ
  rw [M.automizer_L] at hφ
  induction hφ using Subgroup.closure_induction with
  | mem ψ hψ =>
      obtain ⟨i, rfl⟩ := hψ
      rw [M.simple_apply i h, hh i, zero_smul, sub_zero]
  | one => simp
  | mul a b ha hb iha ihb =>
      rw [map_mul]
      show ggLin (p := 3) M.model a (ggLin (p := 3) M.model b h) = h
      rw [ihb, iha]
  | inv a ha iha =>
      rw [map_inv]
      have h2 := congrArg (fun w => (ggLin (p := 3) M.model a).symm w) iha
      rw [LinearEquiv.symm_apply_apply] at h2
      exact h2.symm

private theorem ggQ2hD_ker_rootMap {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) :
    LinearMap.ker M.rootMap = Submodule.span (ZMod 3) {M.xV} := by
  apply le_antisymm
  · intro v hv
    rw [LinearMap.mem_ker] at hv
    have hv' : ∀ i, M.root i v = 0 := fun i => by
      have := congrFun hv i
      change M.root i v = 0 at this
      exact this
    have hvtop : v ∈ M.coSpan ⊔ Submodule.span (ZMod 3) {M.xV} := by
      rw [hB.2.2.2]; exact Submodule.mem_top
    obtain ⟨h, hh, b, hb, hvb⟩ := Submodule.mem_sup.mp hvtop
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    have hhroot : ∀ i, M.root i h = 0 := by
      intro i
      have := hv' i
      rw [← hvb, map_add, ← hc, map_smul, ggQ2hD_root_xV M hB i, smul_zero, add_zero] at this
      exact this
    have hfix := ggQ2hD_mem_fixed_of_root_eq_zero M h hhroot
    rw [M.fixed_x] at hfix
    obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp hfix
    rw [← hvb, ← hc', ← hc]
    change c' • M.xV + c • M.xV ∈ Submodule.span (ZMod 3) {M.xV}
    rw [← add_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton M.xV))
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    ext i
    change M.root i M.xV = 0
    exact ggQ2hD_root_xV M hB i

private theorem ggQ2hD_cartan_of_labels {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) {Γ : Type} [Fintype Γ] [DecidableEq Γ] (e : Γ ≃ M.Λ)
    {Mx : CoxeterMatrix Γ} (hM : M.coxeter = Mx.reindex e)
    (hM23 : ∀ i j, i ≠ j → Mx i j = 2 ∨ Mx i j = 3) (C : Matrix Γ Γ ℤ)
    (hC0 : ∀ i j, i ≠ j → Mx i j = 2 → C i j = 0)
    (hC3 : ∀ i j, i ≠ j → Mx i j = 3 → C i j = -1) (hCii : ∀ i, C i i = 2) (i j : Γ) :
    M.cartan (e i) (e j) = C i j := by
  by_cases hij : i = j
  · subst hij
    rw [M.isCartan.1, hCii]
  · have hne : e i ≠ e j := fun h => hij (e.injective h)
    have hcox : M.coxeter (e i) (e j) = Mx i j := by
      rw [hM, CoxeterMatrix.reindex_apply]
      simp
    rcases hM23 i j hij with h2 | h3
    · rw [hC0 i j hij h2]
      rcases M.isCartan.2 (e i) (e j) hne with ⟨hm, h1, -⟩ | ⟨hm, -, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega
    · rw [hC3 i j hij h3]
      rcases M.isCartan.2 (e i) (e j) hne with ⟨hm, -, -⟩ | ⟨hm, h1, -⟩ |
        ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
      · rw [hcox] at hm; omega
      · exact h1
      · rw [hcox] at hm; omega
      · rw [hcox] at hm; omega

private theorem ggQ2hD_cartan_E6 {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (e : Fin 6 ≃ M.Λ)
    (he : M.coxeter = CoxeterMatrix.E₆.reindex e) (i j : Fin 6) :
    M.cartan (e i) (e j) = E6Heart.C i j :=
  ggQ2hD_cartan_of_labels M e he
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [CoxeterMatrix.E₆])
    E6Heart.C
    (by intro i j hij h; fin_cases i <;> fin_cases j <;>
      simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by intro i j hij h; fin_cases i <;> fin_cases j <;>
      simp_all [CoxeterMatrix.E₆, CartanMatrix.E])
    (by intro i; fin_cases i <;> decide) i j

private def ggQ2hD_C3 : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  E6Heart.C.map (fun z => (z : ZMod 3))

private def ggQ2hD_T : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  Matrix.mulVecLin ggQ2hD_C3

private theorem ggQ2hD_T_rad : ggQ2hD_T E6Heart.rad = 0 := by
  ext i; fin_cases i <;> decide

private theorem ggQ2hD_T_ker :
    LinearMap.ker ggQ2hD_T = Submodule.span (ZMod 3) {E6Heart.rad} := by
  apply le_antisymm
  · intro y hy
    rw [LinearMap.mem_ker] at hy
    have hdec : ∀ y : Fin 6 → ZMod 3, ggQ2hD_T y = 0 →
        ∃ c : ZMod 3, y = c • E6Heart.rad := by
      decide +kernel
    obtain ⟨c, rfl⟩ := hdec y hy
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton E6Heart.rad))
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact ggQ2hD_T_rad

private def ggQ2hD_Tbar : E6Heart.H →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  Submodule.liftQ (Submodule.span (ZMod 3) {E6Heart.rad}) ggQ2hD_T
    (le_of_eq ggQ2hD_T_ker.symm)

private theorem ggQ2hD_Tbar_apply (y : Fin 6 → ZMod 3) :
    ggQ2hD_Tbar (Submodule.Quotient.mk y) = ggQ2hD_T y := by
  rw [ggQ2hD_Tbar]
  exact Submodule.liftQ_apply _ _ y

private theorem ggQ2hD_Tbar_range : ggQ2hD_Tbar.range = ggQ2hD_T.range := by
  apply le_antisymm
  · rintro w ⟨h, hh⟩
    rw [← hh]
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ h
    exact ⟨y, (ggQ2hD_Tbar_apply y).symm⟩
  · rintro w ⟨y, hh⟩
    rw [← hh]
    exact ⟨Submodule.Quotient.mk y, ggQ2hD_Tbar_apply y⟩

private theorem ggQ2hD_Tbar_injective : Function.Injective ggQ2hD_Tbar := by
  rw [← LinearMap.ker_eq_bot, ggQ2hD_Tbar]
  exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq ggQ2hD_T_ker)

private def ggQ2hD_rho {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (e : Fin 6 ≃ M.Λ) :
    M.V →ₗ[ZMod 3] (Fin 6 → ZMod 3) where
  toFun v := fun i => M.root (e i) v
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

private theorem ggQ2hD_rho_xV {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ) :
    ggQ2hD_rho M e M.xV = 0 := by
  funext i
  exact ggQ2hD_root_xV M hB (e i)

private theorem ggQ2hD_rho_coroot {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) (j : Fin 6) :
    ggQ2hD_rho M e (M.coroot (e j)) = ggQ2hD_T (Pi.single j 1) := by
  funext i
  change M.root (e i) (M.coroot (e j)) = ggQ2hD_T (Pi.single j 1) i
  rw [M.pairing (e i) (e j), hc i j]
  simp only [ggQ2hD_T, ggQ2hD_C3, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, Matrix.map_apply]

private theorem ggQ2hD_eq_sum_single (y : Fin 6 → ZMod 3) :
    y = ∑ j : Fin 6, y j • Pi.single j (1 : ZMod 3) := by
  funext k
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    rw [Pi.smul_apply, Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

private theorem ggQ2hD_range_rho_le {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) :
    (ggQ2hD_rho M e).range ≤ ggQ2hD_T.range := by
  intro w hw
  obtain ⟨v, rfl⟩ := hw
  have hvtop : v ∈ M.coSpan ⊔ Submodule.span (ZMod 3) {M.xV} := by
    rw [hB.2.2.2]; exact Submodule.mem_top
  obtain ⟨h, hh, b, hb, hvb⟩ := Submodule.mem_sup.mp hvtop
  obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp hb
  have hrho : ggQ2hD_rho M e v = ggQ2hD_rho M e h := by
    rw [← hvb, map_add, ← hc', map_smul, ggQ2hD_rho_xV M hB e, smul_zero, add_zero]
  rw [hrho]
  rw [GGQ2LDatum.coSpan, Submodule.mem_span_range_iff_exists_fun] at hh
  obtain ⟨coeff, hcoeff⟩ := hh
  rw [← hcoeff]
  simp only [map_sum, map_smul]
  refine ⟨∑ j : Fin 6, coeff (e j) • Pi.single j 1, ?_⟩
  rw [map_sum]
  simp only [map_smul]
  rw [show (∑ j : Fin 6, coeff (e j) • ggQ2hD_T (Pi.single j 1)) =
      ∑ j : Fin 6, coeff (e j) • ggQ2hD_rho M e (M.coroot (e j)) from
    Finset.sum_congr rfl (fun j _ => by rw [ggQ2hD_rho_coroot M e hc j])]
  exact Equiv.sum_comp e (fun i => coeff i • ggQ2hD_rho M e (M.coroot i))

private theorem ggQ2hD_range_T_le_rho {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) :
    ggQ2hD_T.range ≤ (ggQ2hD_rho M e).range := by
  intro w hw
  obtain ⟨y, rfl⟩ := hw
  rw [ggQ2hD_eq_sum_single y]
  simp only [map_sum, map_smul]
  refine ⟨∑ j : Fin 6, y j • M.coroot (e j), ?_⟩
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [ggQ2hD_rho_coroot M e hc j]

private noncomputable def ggQ2hD_Psi {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) :
    M.V →ₗ[ZMod 3] E6Heart.H :=
  ((LinearEquiv.ofInjective ggQ2hD_Tbar ggQ2hD_Tbar_injective).symm :
      ggQ2hD_Tbar.range ≃ₗ[ZMod 3] E6Heart.H).toLinearMap.comp
    ((ggQ2hD_rho M e).codRestrict ggQ2hD_Tbar.range
      (fun v => by
        rw [ggQ2hD_Tbar_range]
        exact ggQ2hD_range_rho_le M hB e hc ⟨v, rfl⟩))

private theorem ggQ2hD_Psi_spec {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) (v : M.V) :
    ggQ2hD_Tbar (ggQ2hD_Psi M hB e hc v) = ggQ2hD_rho M e v := by
  rw [ggQ2hD_Psi]
  simp only [LinearEquiv.coe_toLinearMap, LinearMap.comp_apply, LinearMap.codRestrict_apply]
  exact congrArg Subtype.val (LinearEquiv.apply_symm_apply
    (LinearEquiv.ofInjective ggQ2hD_Tbar ggQ2hD_Tbar_injective)
    ((ggQ2hD_rho M e).codRestrict ggQ2hD_Tbar.range _ v))

private theorem ggQ2hD_Psi_surj {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) :
    Function.Surjective (ggQ2hD_Psi M hB e hc) := by
  intro h
  have hmem : ggQ2hD_Tbar h ∈ ggQ2hD_T.range := by
    rw [← ggQ2hD_Tbar_range]
    exact LinearMap.mem_range_self _ h
  obtain ⟨v, hv⟩ := ggQ2hD_range_T_le_rho M hB e hc hmem
  exact ⟨v, by
    apply ggQ2hD_Tbar_injective
    rw [ggQ2hD_Psi_spec, hv]⟩

private theorem ggQ2hD_rho_eq_zero {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (e : Fin 6 ≃ M.Λ) (v : M.V) :
    ggQ2hD_rho M e v = 0 ↔ v ∈ LinearMap.ker M.rootMap := by
  constructor
  · intro h
    rw [LinearMap.mem_ker]
    ext k
    obtain ⟨i, rfl⟩ := e.surjective k
    have hh := congrFun h i
    change M.root (e i) v = 0 at hh
    exact hh
  · intro h
    funext i
    have hh := congrFun h (e i)
    change M.root (e i) v = 0 at hh
    exact hh

private theorem ggQ2hD_Psi_ker {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) :
    LinearMap.ker (ggQ2hD_Psi M hB e hc) = Submodule.span (ZMod 3) {M.xV} := by
  ext v
  rw [LinearMap.mem_ker]
  have hiff : ggQ2hD_Psi M hB e hc v = 0 ↔ ggQ2hD_rho M e v = 0 := by
    constructor
    · intro h
      rw [← ggQ2hD_Psi_spec M hB e hc v, h, map_zero]
    · intro h
      apply ggQ2hD_Tbar_injective
      rw [ggQ2hD_Psi_spec, h, map_zero]
  rw [hiff, ggQ2hD_rho_eq_zero M e v, ggQ2hD_ker_rootMap M hB]

private theorem ggQ2hD_pair_eq (a' : Fin 6 → ℤ) (y : Fin 6 → ZMod 3) :
    E6Heart.pair a' y = ∑ i, (a' i : ZMod 3) * ggQ2hD_T y i := by
  simp only [E6Heart.pair, ggQ2hD_T, ggQ2hD_C3, Matrix.mulVecLin_apply, Matrix.mulVec,
    Matrix.map_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem ggQ2hD_alpha_Psi {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) (a' : Fin 6 → ℤ) (v : M.V) :
    E6Heart.alpha a' (ggQ2hD_Psi M hB e hc v) =
      ∑ i, (a' i : ZMod 3) * ggQ2hD_rho M e v i := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    (Submodule.span (ZMod 3) {E6Heart.rad}) (ggQ2hD_Psi M hB e hc v)
  have hyT : ggQ2hD_T y = ggQ2hD_rho M e v := by
    have h := ggQ2hD_Psi_spec M hB e hc v
    rw [← hy] at h
    rwa [ggQ2hD_Tbar, Submodule.liftQ_apply] at h
  rw [← hy]
  simp only [E6Heart.alpha, E6Heart.pairLin, Submodule.liftQ_apply]
  change E6Heart.pair a' y = ∑ i, (a' i : ZMod 3) * ggQ2hD_rho M e v i
  rw [ggQ2hD_pair_eq, hyT]

private theorem ggQ2hD_form_eq {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) (hB : M.ShapeB) (e : Fin 6 ≃ M.Λ)
    (hc : ∀ i j, M.cartan (e i) (e j) = E6Heart.C i j) (a : M.Λ → ℤ) (v : M.V) :
    M.rootForm a v = E6Heart.alpha (fun i => a (e i)) (ggQ2hD_Psi M hB e hc v) := by
  rw [ggQ2hD_alpha_Psi]
  simp only [GGQ2LDatum.rootForm, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact (Equiv.sum_comp e (fun k => (a k : ZMod 3) * M.root k v)).symm

theorem ggQ2_heartDict {G : Type} [Group G] {Bs L : Subgroup G} {x : G} {labL : LargeEvenLabel}
    (hlab : labL.tag = .twE6) (M : GGQ2LDatum 3 Bs L x) (hW : GGQ2LabelWeyl labL M.coxeter)
    (hB : M.ShapeB) : Nonempty (GGHeartDict M) := by
  obtain ⟨e, he⟩ : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₆.reindex e := by
    simpa only [GGQ2LabelWeyl, hlab] using hW
  have hc := ggQ2hD_cartan_E6 M e he
  exact ⟨e, ggQ2hD_Psi M hB e hc, hc, ggQ2hD_Psi_surj M hB e hc,
    ggQ2hD_Psi_ker M hB e hc, ggQ2hD_form_eq M hB e hc⟩

end CFSG.StandardType

end

