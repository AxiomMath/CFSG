module

public import CFSG.RankThree.PartOne.KFR4.Defs
public import CFSG.ClassicalGroups.Orthogonal.RootCenters

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG.RankThree.PartOne.KCOrthogonal CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.OrthogonalInvolutions Module
open scoped commutatorElement

namespace SGen

section Regular

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {S : Submodule K V}

abbrev perpS (Q : QuadraticForm K V) (S : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) S

theorem mem_perpS {z : V} : z ∈ perpS Q S ↔ ∀ x ∈ S, polar Q z x = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h x hx
    have := h x hx
    rw [polarBilin_apply_apply] at this
    rw [polar_comm]
    exact this
  · intro h x hx
    show polarBilin Q x z = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact h x hx

theorem isCompl_perpS [FiniteDimensional K V] (hS : (polarBilin (Q.restrict S)).Nondegenerate) :
    IsCompl S (perpS Q S) := by
  have h : polarBilin (Q.comp S.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) S := by
    refine LinearMap.ext₂ fun x y => ?_
    simp [polarBilin_apply_apply, polar]
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    (isSymm_polarBilin Q).isRefl (by rw [← h]; exact hS)

@[expose] def resAut (g : V ≃ₗ[K] V) (hg : ∀ x, x ∈ S ↔ g x ∈ S) : S ≃ₗ[K] S where
  toFun r := ⟨g r, (hg r).mp r.2⟩
  map_add' x y := Subtype.ext (map_add g (x : V) (y : V))
  map_smul' c x := Subtype.ext (map_smul g c (x : V))
  invFun r := ⟨g⁻¹ r, (hg (g⁻¹ r)).mpr (by rw [LinearEquiv.apply_inv_apply']; exact r.2)⟩
  left_inv r := Subtype.ext (LinearEquiv.inv_apply_apply' g (r : V))
  right_inv r := Subtype.ext (LinearEquiv.apply_inv_apply' g (r : V))

theorem coe_resAut (g : V ≃ₗ[K] V) (hg : ∀ x, x ∈ S ↔ g x ∈ S) (r : S) :
    ((resAut g hg r : S) : V) = g r := rfl

theorem resAut_mem_orth {g : V ≃ₗ[K] V} (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ x, x ∈ S ↔ g x ∈ S) :
    resAut g hg ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict S) :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hgO (x : V)

theorem finrank_commSpace_resAut [FiniteDimensional K V]
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : ∀ x, x ∈ S ↔ g x ∈ S) (hfix : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z) :
    finrank K (commSpace (resAut g hg)) = finrank K (commSpace g) := by
  have h : commSpace g = (commSpace (resAut g hg)).map S.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
      have hv : v ∈ S ⊔ perpS Q S := by
        rw [(isCompl_perpS hS).sup_eq_top]
        trivial
      obtain ⟨s, hs, z, hz, rfl⟩ := Submodule.mem_sup.mp hv
      refine ⟨resAut g hg ⟨s, hs⟩ - ⟨s, hs⟩, sub_mem_commSpace _ _, ?_⟩
      simp only [Submodule.subtype_apply, Submodule.coe_sub, coe_resAut]
      rw [map_add, hfix z (mem_perpS.mp hz)]
      abel
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨v, rfl⟩ := mem_commSpace.mp hy
      exact mem_commSpace.mpr ⟨(v : V), by simp [coe_resAut]⟩
  rw [h, Submodule.finrank_map_subtype_eq]

theorem resAut_mem_omega [CharP K 2] [FiniteDimensional K V] {hQ : (polarBilin Q).Nondegenerate}
    (hS : (polarBilin (Q.restrict S)).Nondegenerate) {g : V ≃ₗ[K] V}
    (hgΩ : g ∈ omegaGroup Q hQ) (hg : ∀ x, x ∈ S ↔ g x ∈ S)
    (hfix : ∀ z, (∀ x ∈ S, polar Q z x = 0) → g z = z) :
    resAut g hg ∈ omegaGroup (Q.restrict S) hS :=
  ⟨resAut_mem_orth hgΩ.1 hg, by rw [finrank_commSpace_resAut hS hg hfix]; exact hgΩ.2⟩

theorem coe_eichler_restrict {u w : V} (hu : Q u = 0) (hw : polar Q u w = 0) (huS : u ∈ S)
    (hwS : w ∈ S) (x : S) :
    ((eichler (Q.restrict S) ⟨u, huS⟩ ⟨w, hwS⟩ x : S) : V) = eichler Q u w x := by
  have hu' : (Q.restrict S) ⟨u, huS⟩ = 0 := hu
  have hw' : polar (Q.restrict S) ⟨u, huS⟩ ⟨w, hwS⟩ = 0 := by rw [polar_restrict]; exact hw
  rw [eichler_apply (Q := Q.restrict S) hu' hw', eichler_apply hu hw]
  simp [polar_restrict]

end Regular

theorem commutator_mem {G : Type*} [Group G] {H : Subgroup G} {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

section Coord

variable {K E : Type} [Field K] [Field E] [Algebra K E]

theorem exists_decomp (F : Finset (Fin 3)) (v : Vs K E) :
    ∃ v₁ v₂ : Vs K E, v₁ ∈ Ufix K E F ∧ (∀ l ∈ F, v₂.1 l = 0) ∧ v₂.2 = 0 ∧ v = v₁ + v₂ := by
  refine ⟨(fun l => if l ∈ F then v.1 l else 0, v.2), (fun l => if l ∈ F then 0 else v.1 l, 0),
    fun l hl => by simp [hl], fun l hl => by simp [hl], rfl, ?_⟩
  refine Prod.ext (funext fun l => ?_) (add_zero v.2).symm
  by_cases hl : l ∈ F <;> simp [hl]

end Coord

section Supp

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]
  {D : EvenNormPlane K E}

theorem supp_apply_fst {F : Finset (Fin 3)} {g : Vs K E ≃ₗ[K] Vs K E} (hg : g ∈ Supp D F)
    (v : Vs K E) {l : Fin 3} (hl : l ∉ F) : (g v).1 l = v.1 l := by
  obtain ⟨-, hgU, hgW⟩ := hg
  obtain ⟨v₁, v₂, hv₁, hv₂, hv₂', rfl⟩ := exists_decomp F v
  have h1 := (hgU v₁).1 hv₁ l hl
  rw [map_add, hgW v₂ hv₂ hv₂']
  simp only [Prod.fst_add, Pi.add_apply, h1, hv₁ l hl]

theorem supp_mono {F F' : Finset (Fin 3)} (h : F ⊆ F') : Supp D F ≤ Supp D F' := by
  intro g hg
  refine ⟨hg.1, fun v => ?_, fun v hv hv2 => hg.2.2 v (fun l hl => hv l (h hl)) hv2⟩
  have key : ∀ l, l ∉ F' → (g v).1 l = v.1 l := fun l hl =>
    supp_apply_fst hg v fun hlF => hl (h hlF)
  constructor
  · intro hv l hl
    rw [key l hl]
    exact hv l hl
  · intro hv l hl
    rw [← key l hl]
    exact hv l hl

theorem supp_ext {F : Finset (Fin 3)} {g h : Vs K E ≃ₗ[K] Vs K E} (hg : g ∈ Supp D F)
    (hh : h ∈ Supp D F) (hgh : ∀ x ∈ Ufix K E F, g x = h x) : g = h := by
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨v₁, v₂, hv₁, hv₂, hv₂', rfl⟩ := exists_decomp F v
  rw [map_add, map_add, hgh v₁ hv₁, hg.2.2 v₂ hv₂ hv₂', hh.2.2 v₂ hv₂ hv₂']

theorem perp_Ufix {F : Finset (Fin 3)} {z : Vs K E}
    (hz : ∀ x ∈ Ufix K E F, polar (Qs D) z x = 0) : (∀ l ∈ F, z.1 l = 0) ∧ z.2 = 0 := by
  refine ⟨fun l hl => ?_, ?_⟩
  · by_contra h0
    obtain ⟨u, hu⟩ := polar_N_ne_zero D h0
    apply hu
    have hmem : ((Pi.single l u : Fin 3 → E), (0 : K × K)) ∈ Ufix K E F := by
      intro j hj
      have hjl : j ≠ l := fun h => hj (h ▸ hl)
      simp [hjl]
    have h := hz _ hmem
    rw [polar_Qs, Finset.sum_eq_single l (fun j _ hj => by simp [hj]) (by simp)] at h
    simpa using h
  · have h1 := hz ((0 : Fin 3 → E), ((1 : K), (0 : K))) (fun j _ => rfl)
    have h2 := hz ((0 : Fin 3 → E), ((0 : K), (1 : K))) (fun j _ => rfl)
    rw [polar_Qs] at h1 h2
    simp at h1 h2
    exact Prod.ext h2 h1

variable (D) in
theorem polarNondegOn_Ufix (F : Finset (Fin 3)) : PolarNondegOn (Qs D) (Ufix K E F) := by
  intro x hx hperp
  obtain ⟨h1, h2⟩ := perp_Ufix (D := D) hperp
  refine Prod.ext (funext fun l => ?_) h2
  by_cases hl : l ∈ F
  · exact h1 l hl
  · exact hx l hl

theorem polar_eq_zero_of_Ufix {F : Finset (Fin 3)} {v u : Vs K E} (hv : ∀ l ∈ F, v.1 l = 0)
    (hv2 : v.2 = 0) (hu : u ∈ Ufix K E F) : polar (Qs D) v u = 0 := by
  have hsum : ∑ l, polar D.N (v.1 l) (u.1 l) = 0 := Finset.sum_eq_zero fun l _ => by
    by_cases hl : l ∈ F
    · rw [hv l hl, polar_zero_left]
    · rw [hu l hl, polar_zero_right]
  rw [polar_Qs, hsum, hv2]
  simp

theorem eichler_mem_supp {F : Finset (Fin 3)} {u w : Vs K E} (hu : u ∈ Ufix K E F)
    (hw : w ∈ Ufix K E F) : eichler (Qs D) u w ∈ Supp D F := by
  refine ⟨eichler_mem_orthogonalGroup _ u w, fun v => ?_, fun v hv hv2 => ?_⟩
  · obtain ⟨a, b, hab⟩ := eichler_apply_eq_add (Q := Qs D) u w v
    rw [hab]
    have hd : a • w + b • u ∈ Ufix K E F :=
      add_mem (Submodule.smul_mem _ a hw) (Submodule.smul_mem _ b hu)
    constructor
    · intro hv
      rw [add_assoc]
      exact add_mem hv hd
    · intro hv
      have := sub_mem hv hd
      rwa [add_assoc, add_sub_cancel_right] at this
  · exact eichler_apply_of_polar_eq_zero (polar_eq_zero_of_Ufix hv hv2 hu)
      (polar_eq_zero_of_Ufix hv hv2 hw)

variable (D) in
theorem elementaryGroup_le_Om [Module.Finite K E] : elementaryGroup (Qs D) ≤ Om D :=
  (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure (Qs_nondegenerate D)
    (exists_three_totSing_Qs D)).1.ge

theorem eichler_mem_supp_inf_Om [Module.Finite K E] {F : Finset (Fin 3)} {u w : Vs K E}
    (hu : u ∈ Ufix K E F) (hw : w ∈ Ufix K E F) : eichler (Qs D) u w ∈ Supp D F ⊓ Om D :=
  ⟨eichler_mem_supp hu hw, elementaryGroup_le_Om D (eichler_mem_elementaryGroup _ u w)⟩

end Supp

section Pair

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E]

@[expose] def resGroup (F : Finset (Fin 3)) (G : Subgroup (Vs K E ≃ₗ[K] Vs K E)) :
    Subgroup (Ufix K E F ≃ₗ[K] Ufix K E F) where
  carrier := {g' | ∃ g ∈ G, ∀ x : Ufix K E F, g (x : Vs K E) = ((g' x : Ufix K E F) : Vs K E)}
  mul_mem' := by
    rintro a b ⟨g, hg, hga⟩ ⟨h, hh, hhb⟩
    refine ⟨g * h, mul_mem hg hh, fun x => ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hhb, hga]
  one_mem' := ⟨1, one_mem G, fun x => rfl⟩
  inv_mem' := by
    rintro a ⟨g, hg, hga⟩
    refine ⟨g⁻¹, inv_mem hg, fun x => ?_⟩
    apply g.injective
    rw [LinearEquiv.apply_inv_apply', hga]
    exact (congrArg Subtype.val (LinearEquiv.apply_inv_apply' a x)).symm

theorem resGroup_le_orth {D : EvenNormPlane K E} {F : Finset (Fin 3)}
    {G : Subgroup (Vs K E ≃ₗ[K] Vs K E)}
    (hG : G ≤ TauCeti.QuadraticMap.orthogonalGroup (Qs D)) :
    resGroup F G ≤ TauCeti.QuadraticMap.orthogonalGroup ((Qs D).restrict (Ufix K E F)) := by
  rintro g' ⟨g, hg, hgx⟩
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun x => ?_
  show Qs D (g' x : Vs K E) = Qs D x
  rw [← hgx x]
  exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hG hg) x

theorem Qs_pair (D : EvenNormPlane K E) {i j : Fin 3} (hij : i ≠ j) (u : E) (x : K) :
    Qs D (fun l => if l = i ∨ l = j then u else 0, (x, 0)) = 0 := by
  rw [Qs_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three] at hij ⊢ <;>
    exact CharTwo.add_self_eq_zero _

theorem exists_three_totSing_restrict [Module.Finite K E] (D : EvenNormPlane K E) {i j : Fin 3}
    (hij : i ≠ j) :
    ∃ T : Submodule K (Ufix K E {i, j}), finrank K T = 3 ∧
      ∀ x ∈ T, (Qs D).restrict (Ufix K E {i, j}) x = 0 := by
  let f₀ : (E × K) →ₗ[K] Vs K E :=
    { toFun := fun u => (fun l => if l = i ∨ l = j then u.1 else 0, (u.2, 0))
      map_add' := fun u w => by
        refine Prod.ext (funext fun l => ?_) (Prod.ext rfl (add_zero 0).symm)
        by_cases hl : l = i ∨ l = j <;> simp [hl]
      map_smul' := fun c u => by
        refine Prod.ext (funext fun l => ?_) (Prod.ext rfl (smul_zero c).symm)
        by_cases hl : l = i ∨ l = j <;> simp [hl] }
  have hmem : ∀ u, f₀ u ∈ Ufix K E {i, j} := by
    intro u l hl
    have hl' : ¬(l = i ∨ l = j) := by simpa using hl
    simp [f₀, hl']
  let f := LinearMap.codRestrict (Ufix K E {i, j}) f₀ hmem
  have hinj : Function.Injective f := by
    intro u w h
    have h' : f₀ u = f₀ w := congrArg Subtype.val h
    have h1 := congrArg (fun v : Vs K E => v.1 i) h'
    have h2 := congrArg (fun v : Vs K E => v.2.1) h'
    simp [f₀] at h1 h2
    exact Prod.ext h1 h2
  refine ⟨LinearMap.range f, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, D.finrank_eq,
      Module.finrank_self]
  · rintro _ ⟨u, rfl⟩
    exact Qs_pair D hij u.1 u.2

theorem nondeg_Ufix (D : EvenNormPlane K E) (F : Finset (Fin 3)) :
    (polarBilin ((Qs D).restrict (Ufix K E F))).Nondegenerate :=
  nondegenerate_polarBilin_restrict (polarNondegOn_Ufix D F)

variable [Module.Finite K E] {D : EvenNormPlane K E}

variable (D) in
theorem omega_restrict_le {i j : Fin 3} (hij : i ≠ j) :
    omegaGroup ((Qs D).restrict (Ufix K E {i, j})) (nondeg_Ufix D {i, j}) ≤
      elementaryGroup ((Qs D).restrict (Ufix K E {i, j})) :=
  (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived (nondeg_Ufix D {i, j})
    (exists_three_totSing_restrict D hij)).trans
    (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure (nondeg_Ufix D {i, j})
      (exists_three_totSing_restrict D hij)).1.le

theorem isRootCenter_H {i j : Fin 3} (hij : i ≠ j) {h : Vs K E} (hh1 : h.1 = 0)
    (hhQ : Qs D h = 0) (hh0 : h ≠ 0) (hhW : h ∈ Ufix K E {i, j}) :
    IsRootCenter ((Qs D).restrict (Ufix K E {i, j}))
      (resGroup {i, j} ((Supp D {i} ⊓ Om D) ⊔ (Supp D {j} ⊓ Om D))) ⟨h, hhW⟩ := by
  have hhi : h ∈ Ufix K E {i} := fun l _ => by rw [hh1]; rfl
  have hhj : h ∈ Ufix K E {j} := fun l _ => by rw [hh1]; rfl
  have hhe : h ∈ Ufix K E ∅ := fun l _ => by rw [hh1]; rfl
  refine IsRootCenter.of_span (fun h0 => hh0 (congrArg Subtype.val h0)) hhQ
    {w : Ufix K E {i, j} | polar ((Qs D).restrict (Ufix K E {i, j})) ⟨h, hhW⟩ w = 0 ∧
      ((w : Vs K E) ∈ Ufix K E {i} ∨ (w : Vs K E) ∈ Ufix K E {j})} ?_ ?_
  · rintro w ⟨hw, hwij⟩
    refine ⟨hw, eichler (Qs D) h w, ?_, fun x => ?_⟩
    · rcases hwij with hwi | hwj
      · exact Subgroup.mem_sup_left (eichler_mem_supp_inf_Om hhi hwi)
      · exact Subgroup.mem_sup_right (eichler_mem_supp_inf_Om hhj hwj)
    · exact (coe_eichler_restrict hhQ (by rwa [polar_restrict] at hw) hhW w.2 x).symm
  · rintro ⟨w, hwW⟩ hw
    have hwk : ∀ l, l ≠ i → l ≠ j → w.1 l = 0 := fun l hli hlj => hwW l (by simp [hli, hlj])
    have haW : ((Pi.single i (w.1 i) : Fin 3 → E), w.2) ∈ Ufix K E {i, j} := by
      intro l hl
      have hli : l ≠ i := fun h => hl (by simp [h])
      simp [hli]
    have hbW : ((Pi.single j (w.1 j) : Fin 3 → E), (0 : K × K)) ∈ Ufix K E {i, j} := by
      intro l hl
      have hlj : l ≠ j := fun h => hl (by simp [h])
      simp [hlj]
    have hai : ((Pi.single i (w.1 i) : Fin 3 → E), w.2) ∈ Ufix K E {i} := by
      intro l hl
      have hli : l ≠ i := fun h => hl (by simp [h])
      simp [hli]
    have hbj : ((Pi.single j (w.1 j) : Fin 3 → E), (0 : K × K)) ∈ Ufix K E {j} := by
      intro l hl
      have hlj : l ≠ j := fun h => hl (by simp [h])
      simp [hlj]
    have hab : (⟨w, hwW⟩ : Ufix K E {i, j}) = ⟨_, haW⟩ + ⟨_, hbW⟩ := by
      refine Subtype.ext (Prod.ext (funext fun l => ?_) (add_zero w.2).symm)
      show w.1 l = (Pi.single i (w.1 i) : Fin 3 → E) l + (Pi.single j (w.1 j) : Fin 3 → E) l
      rcases eq_or_ne l i with rfl | hli
      · simp [hij]
      · rcases eq_or_ne l j with rfl | hlj
        · simp [hli]
        · simp [hli, hlj, hwk l hli hlj]
    have hbpol : polar ((Qs D).restrict (Ufix K E {i, j})) ⟨h, hhW⟩ ⟨_, hbW⟩ = 0 := by
      rw [polar_restrict, polar_comm]
      exact polar_eq_zero_of_Ufix (F := ∅) (fun l hl => absurd hl (Finset.notMem_empty l)) rfl hhe
    have hapol : polar ((Qs D).restrict (Ufix K E {i, j})) ⟨h, hhW⟩ ⟨_, haW⟩ = 0 := by
      rw [hab, polar_add_right, hbpol, add_zero] at hw
      exact hw
    rw [hab]
    exact add_mem (AddSubgroup.subset_closure (Or.inl ⟨hapol, Or.inl hai⟩))
      (AddSubgroup.subset_closure (Or.inl ⟨hbpol, Or.inr hbj⟩))

variable (D) in
theorem supp_pair_le {i j : Fin 3} (hij : i ≠ j) :
    Supp D {i, j} ⊓ Om D ≤ (Supp D {i} ⊓ Om D) ⊔ (Supp D {j} ⊓ Om D) := by
  intro f hf
  have hW := nondeg_Ufix D {i, j}
  have hGsupp : (Supp D {i} ⊓ Om D) ⊔ (Supp D {j} ⊓ Om D) ≤ Supp D {i, j} :=
    sup_le (inf_le_left.trans (supp_mono (Finset.singleton_subset_iff.2
      (Finset.mem_insert_self i {j})))) (inf_le_left.trans (supp_mono (Finset.subset_insert i {j})))
  have hGO : (Supp D {i} ⊓ Om D) ⊔ (Supp D {j} ⊓ Om D) ≤
      TauCeti.QuadraticMap.orthogonalGroup (Qs D) := fun g hg => (hGsupp hg).1
  have hfW : ∀ x, x ∈ Ufix K E {i, j} ↔ f x ∈ Ufix K E {i, j} := hf.1.2.1
  have hfix : ∀ z, (∀ x ∈ Ufix K E {i, j}, polar (Qs D) z x = 0) → f z = z := fun z hz =>
    hf.1.2.2 z (perp_Ufix hz).1 (perp_Ufix hz).2
  have hfΩ : f ∈ omegaGroup (Qs D) (Qs_nondegenerate D) := by
    rw [← Om_eq_omegaGroup]
    exact hf.2
  have hE : resAut f hfW ∈ elementaryGroup ((Qs D).restrict (Ufix K E {i, j})) :=
    omega_restrict_le D hij (resAut_mem_omega hW hfΩ hfW hfix)
  let P : HypPair ((Qs D).restrict (Ufix K E {i, j})) :=
    { e := ⟨((0 : Fin 3 → E), ((1 : K), (0 : K))), fun l _ => rfl⟩
      f := ⟨((0 : Fin 3 → E), ((0 : K), (1 : K))), fun l _ => rfl⟩
      Q_e := by
        show Qs D _ = 0
        simp [Qs_apply]
      Q_f := by
        show Qs D _ = 0
        simp [Qs_apply]
      polar_ef := by
        rw [polar_restrict, polar_Qs]
        simp }
  have he : IsRootCenter ((Qs D).restrict (Ufix K E {i, j}))
      (resGroup {i, j} ((Supp D {i} ⊓ Om D) ⊔ (Supp D {j} ⊓ Om D))) P.e :=
    isRootCenter_H hij rfl (by simp [Qs_apply])
      (fun h0 => by simpa using congrArg (fun v : Vs K E => v.2.1) h0) _
  have hf' : IsRootCenter ((Qs D).restrict (Ufix K E {i, j}))
      (resGroup {i, j} ((Supp D {i} ⊓ Om D) ⊔ (Supp D {j} ⊓ Om D))) P.f :=
    isRootCenter_H hij rfl (by simp [Qs_apply])
      (fun h0 => by simpa using congrArg (fun v : Vs K E => v.2.2) h0) _
  obtain ⟨g, hg, hgf⟩ := elementaryGroup_le_of_hypPair hW (resGroup_le_orth hGO) P he hf' hE
  have hfg : f = g := supp_ext hf.1 (hGsupp hg) fun x hx => (hgf ⟨x, hx⟩).symm
  rw [hfg]
  exact hg

end Pair

section Empty

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {D : EvenNormPlane K E}

theorem exists_diag {f : Vs K E ≃ₗ[K] Vs K E} (hf : f ∈ Supp D ∅ ⊓ Om D) :
    ∃ a d : K, ∀ v : Vs K E, f v = (v.1, (a * v.2.1, d * v.2.2)) := by
  obtain ⟨hS, hΩ⟩ := hf
  have hO := hS.1
  have hfst : ∀ v : Vs K E, (f v).1 = v.1 := fun v =>
    funext fun l => supp_apply_fst hS v (Finset.notMem_empty l)
  obtain ⟨a, b, hfe₁⟩ : ∃ a b : K, f ((0 : Fin 3 → E), ((1 : K), (0 : K))) =
      ((0 : Fin 3 → E), (a, b)) :=
    ⟨(f ((0 : Fin 3 → E), ((1 : K), (0 : K)))).2.1, (f ((0 : Fin 3 → E), ((1 : K), (0 : K)))).2.2,
      Prod.ext (hfst ((0 : Fin 3 → E), ((1 : K), (0 : K)))) rfl⟩
  obtain ⟨c, d, hfe₂⟩ : ∃ c d : K, f ((0 : Fin 3 → E), ((0 : K), (1 : K))) =
      ((0 : Fin 3 → E), (c, d)) :=
    ⟨(f ((0 : Fin 3 → E), ((0 : K), (1 : K)))).2.1, (f ((0 : Fin 3 → E), ((0 : K), (1 : K)))).2.2,
      Prod.ext (hfst ((0 : Fin 3 → E), ((0 : K), (1 : K)))) rfl⟩
  have hv : ∀ v : Vs K E, f v = (v.1, (v.2.1 * a + v.2.2 * c, v.2.1 * b + v.2.2 * d)) := by
    intro v
    have e : v = (v.1, 0) + v.2.1 • ((0 : Fin 3 → E), ((1 : K), (0 : K))) +
        v.2.2 • ((0 : Fin 3 → E), ((0 : K), (1 : K))) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
    have hfix : f (v.1, 0) = (v.1, 0) :=
      hS.2.2 _ (fun l hl => absurd hl (Finset.notMem_empty l)) rfl
    have h := congrArg f e
    rw [map_add, map_add, map_smul, map_smul, hfix, hfe₁, hfe₂] at h
    rw [h]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  have hab : a * b = 0 := by
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hO
      ((0 : Fin 3 → E), ((1 : K), (0 : K)))
    rw [hfe₁, Qs_apply, Qs_apply] at h
    simpa using h
  have hcd : c * d = 0 := by
    have h := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hO
      ((0 : Fin 3 → E), ((0 : K), (1 : K)))
    rw [hfe₂, Qs_apply, Qs_apply] at h
    simpa using h
  have hpol : a * d + c * b = 1 := by
    have h := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hO
      ((0 : Fin 3 → E), ((1 : K), (0 : K))) ((0 : Fin 3 → E), ((0 : K), (1 : K)))
    rw [hfe₁, hfe₂, polar_Qs, polar_Qs] at h
    simpa using h
  rcases mul_eq_zero.1 hab with ha0 | hb0 <;> rcases mul_eq_zero.1 hcd with hc0 | hd0
  · rw [ha0, hc0] at hpol
    simp at hpol
  · exfalso
    subst ha0 hd0
    have hcb : c * b = 1 := by simpa using hpol
    have hΩ' : f ∈ omegaGroup (Qs D) (Qs_nondegenerate D) := by
      rw [← Om_eq_omegaGroup]
      exact hΩ
    have hu0 : ((0 : Fin 3 → E), ((1 : K), -b)) ≠ 0 := fun h => by
      simpa using congrArg (fun v : Vs K E => v.2.1) h
    have hle : commSpace f ≤ K ∙ ((0 : Fin 3 → E), ((1 : K), -b)) := by
      intro x hx
      obtain ⟨v, rfl⟩ := mem_commSpace.1 hx
      rw [Submodule.mem_span_singleton]
      refine ⟨v.2.2 * c - v.2.1, ?_⟩
      rw [hv v]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp
      · simp only [Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        linear_combination (-v.2.2) * hcb
    have hne : f ≠ 1 := by
      intro h1
      have h2 := hfe₁
      rw [h1] at h2
      simpa using congrArg (fun v : Vs K E => v.2.1) h2
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0] at h1
    have h3 : finrank K (commSpace f) = 1 := le_antisymm h1 (one_le_finrank_commSpace hne)
    have h4 := hΩ'.2
    rw [h3] at h4
    exact Nat.not_even_one h4
  · refine ⟨a, d, fun v => ?_⟩
    rw [hv v, hb0, hc0]
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring
  · rw [hb0, hd0] at hpol
    simp at hpol

theorem commutator_eq_one_of_empty {f₁ f₂ : Vs K E ≃ₗ[K] Vs K E} (h₁ : f₁ ∈ Supp D ∅ ⊓ Om D)
    (h₂ : f₂ ∈ Supp D ∅ ⊓ Om D) : ⁅f₁, f₂⁆ = 1 := by
  obtain ⟨a₁, d₁, hf₁⟩ := exists_diag h₁
  obtain ⟨a₂, d₂, hf₂⟩ := exists_diag h₂
  rw [commutatorElement_eq_one_iff_mul_comm]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hf₂ v, hf₁ v, hf₁, hf₂]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

end Empty

section Short

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] {p : ℕ}

theorem exists_not_mem_fixedSet {A : AddSubgroup (Fin 3 → ZMod p)} (hA : A ≠ ⊥) :
    ∃ l, l ∉ fixedSet A := by
  by_contra h
  push Not at h
  apply hA
  refine eq_bot_iff.2 fun a ha => ?_
  rw [AddSubgroup.mem_bot]
  funext l
  exact mem_fixedSet.1 (h l) a ha

theorem short_le_iSup (D : EvenNormPlane K E) (A : AddSubgroup (Fin 3 → ZMod p)) {i : Fin 3}
    (hi : i ∈ fixedSet A) :
    Supp D {i} ⊓ Om D ≤ ⨆ ρ : {ρ : Root // vanishes A ρ}, Block D ρ.1 := by
  have key : ∀ ρ : Root, Block D ρ = Supp D {i} ⊓ Om D →
      (∀ a : Fin 3 → ZMod p, ρ.vecp p ⬝ᵥ a = a i) →
      Supp D {i} ⊓ Om D ≤ ⨆ ρ : {ρ : Root // vanishes A ρ}, Block D ρ.1 := by
    intro ρ hρ hdot
    rw [← hρ]
    exact le_iSup (fun ρ : {ρ : Root // vanishes A ρ} => Block D ρ.1)
      ⟨ρ, fun a ha => by rw [hdot]; exact mem_fixedSet.1 hi a ha⟩
  fin_cases i
  · exact key .s1 rfl fun a => by simp [Root.vecp, Root.vec, dotProduct, Fin.sum_univ_three]
  · exact key .s2 rfl fun a => by simp [Root.vecp, Root.vec, dotProduct, Fin.sum_univ_three]
  · exact key .s3 rfl fun a => by simp [Root.vecp, Root.vec, dotProduct, Fin.sum_univ_three]

end Short

end SGen

section Std

variable {K E : Type} [Field K] [Finite K] [CharP K 2] [Field E] [Algebra K E] [Module.Finite K E]
  {p : ℕ} (S : StdData K E p)

open SGen in
theorem supp_commutator_mem (A : AddSubgroup (Fin 3 → ZMod p)) (hA : A ≠ ⊥)
    (f₁ f₂ : Vs K E ≃ₗ[K] Vs K E) (h₁ : f₁ ∈ Supp S.D (fixedSet A) ⊓ Om S.D)
    (h₂ : f₂ ∈ Supp S.D (fixedSet A) ⊓ Om S.D) :
    ⁅f₁, f₂⁆ ∈ ⨆ ρ : {ρ : Root // vanishes A ρ}, Block S.D ρ.1 := by
  classical
  have hcard : (fixedSet A).card < 3 := by
    obtain ⟨l, hl⟩ := exists_not_mem_fixedSet hA
    simpa using Finset.card_lt_univ_of_notMem hl
  have hcases : (fixedSet A).card = 0 ∨ (fixedSet A).card = 1 ∨ (fixedSet A).card = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    rw [h0] at h₁ h₂
    rw [commutator_eq_one_of_empty h₁ h₂]
    exact one_mem _
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.1 h1
    have hiF : i ∈ fixedSet A := by
      rw [hi]
      exact Finset.mem_singleton_self i
    rw [hi] at h₁ h₂
    exact short_le_iSup S.D A hiF (commutator_mem h₁ h₂)
  · obtain ⟨i, j, hij, hF⟩ := Finset.card_eq_two.1 h2
    have hiF : i ∈ fixedSet A := by
      rw [hF]
      simp
    have hjF : j ∈ fixedSet A := by
      rw [hF]
      simp
    rw [hF] at h₁ h₂
    exact sup_le (short_le_iSup S.D A hiF) (short_le_iSup S.D A hjF)
      (commutator_mem (supp_pair_le S.D hij h₁) (supp_pair_le S.D hij h₂))

end Std

end CFSG.RankThree.PartOne.KFR4
