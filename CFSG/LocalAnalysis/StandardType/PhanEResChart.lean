module

public import CFSG.LocalAnalysis.StandardType.PhanEClassify
public import CFSG.Monster.B.Geometry.InitialIsometryProduct
import CFSG.LocalAnalysis.StandardType.PhanEDMBuilding
import CFSG.Monster.B.Geometry.Census

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Res

open CFSG.Monster.B.Geometry CFSG.LieType.Chevalley.CosetBuilding
  CFSG.ClassicalInvolution.Phan.PhanE

variable {ι : Type} {M : CoxeterMatrix ι} {W : Type} [Group W] {cs : CoxeterSystem M W}
  {C : Type} {δ : C → C → W}

theorem buildingOver_adj_iff (hB : IsWeylDistanceBuilding cs δ) {J : Set ι} (j : ↥J)
    (x y : C) :
    (buildingOver cs δ J).adj j x y ↔ δ x y = 1 ∨ δ x y = cs.simple j :=
  buildingSystem_adj_iff hB

section ChartOfMap

variable (hB : IsWeylDistanceBuilding cs δ) {J : Set ι} {a : C} {ι' Ω : Type}
  (Y : ChamberSystem ι' Ω) (e : ↥J ≃ ι') (Ψ : Ω → C) (hinj : Function.Injective Ψ)
  (hadj : ∀ (j : ↥J) (ω ω' : Ω),
    Y.adj (e j) ω ω' ↔ δ (Ψ ω) (Ψ ω') = 1 ∨ δ (Ψ ω) (Ψ ω') = cs.simple j)
  (hmem : ∀ ω, Ψ ω ∈ residue cs δ J a) (hbase : a ∈ Set.range Ψ)
  (hpanel : ∀ (ω : Ω) (j : ↥J) (c : C), δ (Ψ ω) c = cs.simple j → c ∈ Set.range Ψ)

include hB hadj hmem hbase hpanel in
theorem range_eq_residue : Set.range Ψ = residue cs δ J a := by
  refine Set.Subset.antisymm (fun x hx => ?_) (fun y hy => ?_)
  · obtain ⟨ω, rfl⟩ := hx
    exact hmem ω
  · induction hy with
    | refl => exact hbase
    | @tail b c _ hbc ih =>
      obtain ⟨i, hi, hδ⟩ := hbc
      obtain ⟨ω, rfl⟩ := ih
      exact hpanel ω ⟨i, hi⟩ c hδ

noncomputable def chartOfMap (hB : IsWeylDistanceBuilding cs δ) {J : Set ι} {a : C}
    {ι' Ω : Type} (Y : ChamberSystem ι' Ω) (e : ↥J ≃ ι') (Ψ : Ω → C)
    (hinj : Function.Injective Ψ)
    (hadj : ∀ (j : ↥J) (ω ω' : Ω),
      Y.adj (e j) ω ω' ↔ δ (Ψ ω) (Ψ ω') = 1 ∨ δ (Ψ ω) (Ψ ω') = cs.simple j)
    (hmem : ∀ ω, Ψ ω ∈ residue cs δ J a) (hbase : a ∈ Set.range Ψ)
    (hpanel : ∀ (ω : Ω) (j : ↥J) (c : C), δ (Ψ ω) c = cs.simple j → c ∈ Set.range Ψ) :
    ChamberIso ((buildingOver cs δ J).restrict (residue cs δ J a)) Y := by
  let G : Ω → ↥(residue cs δ J a) := fun ω => ⟨Ψ ω, hmem ω⟩
  have hsurj : Function.Surjective G := by
    intro x
    have hx : (x : C) ∈ Set.range Ψ := by
      rw [range_eq_residue hB Y e Ψ hadj hmem hbase hpanel]
      exact x.2
    obtain ⟨ω, hω⟩ := hx
    exact ⟨ω, Subtype.ext hω⟩
  have hG : Function.Bijective G := ⟨fun u v h => hinj (Subtype.ext_iff.mp h), hsurj⟩
  let Φ₀ : Ω ≃ ↥(residue cs δ J a) := Equiv.ofBijective G hG
  refine
    { e := e
      Φ := Φ₀.symm
      adj_iff := ?_ }
  intro j x y
  have hx : Ψ (Φ₀.symm x) = (x : C) := congrArg Subtype.val (Equiv.apply_symm_apply Φ₀ x)
  have hy : Ψ (Φ₀.symm y) = (y : C) := congrArg Subtype.val (Equiv.apply_symm_apply Φ₀ y)
  change (buildingOver cs δ J).adj j (x : C) (y : C) ↔
    Y.adj (e j) (Φ₀.symm x) (Φ₀.symm y)
  rw [buildingOver_adj_iff hB j (x : C) (y : C), hadj j (Φ₀.symm x) (Φ₀.symm y), ← hx, ← hy]

theorem chartOfMap_symm_apply (ω : Ω) :
    (((chartOfMap hB Y e Ψ hinj hadj hmem hbase hpanel).Φ.symm ω :
      ↥(residue cs δ J a)) : C) = Ψ ω := by
  simp only [chartOfMap, Equiv.symm_symm]
  rfl

theorem chartOfMap_apply (ω : Ω) :
    (chartOfMap hB Y e Ψ hinj hadj hmem hbase hpanel).Φ ⟨Ψ ω, hmem ω⟩ = ω := by
  simp only [chartOfMap]
  exact (Equiv.symm_apply_eq _).mpr rfl

theorem chartOfMap_e : (chartOfMap hB Y e Ψ hinj hadj hmem hbase hpanel).e = e := by
  rfl

end ChartOfMap

section ChamberIsoResidue

variable {I I' D : Type} {X : ChamberSystem I C} {Y : ChamberSystem I' D}

private theorem hmbRC_chamberIso_mapsTo_residue (Θ : ChamberIso X Y) (S : Set I) (x : C) :
    Set.MapsTo Θ.Φ (X.residue S x) (Y.residue (Θ.e '' S) (Θ.Φ x)) := by
  intro c hc
  refine mem_residue_induction (J := S) (c := x)
    (fun d => Θ.Φ d ∈ Y.residue (Θ.e '' S) (Θ.Φ x)) (Y.self_mem_residue _ _) ?_ c hc
  intro d e j hj hd hde
  have hje : Θ.e j ∈ Θ.e '' S := ⟨j, hj, rfl⟩
  have h1 : Θ.Φ e ∈ Y.residue {Θ.e j} (Θ.Φ d) :=
    Y.mem_residue_singleton.mpr ((Θ.adj_iff j d e).mp hde)
  exact Y.mem_residue_trans hd
    (Y.residue_mono (Set.singleton_subset_iff.mpr hje) (Θ.Φ d) h1)

private theorem hmbRC_chamberIso_mapsTo_residue_symm (Θ : ChamberIso X Y) (S : Set I') (y : D) :
    Set.MapsTo Θ.Φ.symm (Y.residue S y) (X.residue (Θ.e.symm '' S) (Θ.Φ.symm y)) := by
  intro c hc
  refine mem_residue_induction (J := S) (c := y)
    (fun d => Θ.Φ.symm d ∈ X.residue (Θ.e.symm '' S) (Θ.Φ.symm y))
    (X.self_mem_residue _ _) ?_ c hc
  intro d e j hj hd hde
  have hje : Θ.e.symm j ∈ Θ.e.symm '' S := ⟨j, hj, rfl⟩
  have hadj : X.adj (Θ.e.symm j) (Θ.Φ.symm d) (Θ.Φ.symm e) :=
    (Θ.adj_iff (Θ.e.symm j) (Θ.Φ.symm d) (Θ.Φ.symm e)).mpr (by simpa using hde)
  have h1 : Θ.Φ.symm e ∈ X.residue {Θ.e.symm j} (Θ.Φ.symm d) :=
    X.mem_residue_singleton.mpr hadj
  exact X.mem_residue_trans hd
    (X.residue_mono (Set.singleton_subset_iff.mpr hje) (Θ.Φ.symm d) h1)

private theorem hmbRC_chamberIso_residue_iff (Θ : ChamberIso X Y) (S : Set I) (x c : C) :
    c ∈ X.residue S x ↔ Θ.Φ c ∈ Y.residue (Θ.e '' S) (Θ.Φ x) := by
  refine ⟨fun h => hmbRC_chamberIso_mapsTo_residue Θ S x h, fun h => ?_⟩
  have h' := hmbRC_chamberIso_mapsTo_residue_symm Θ (Θ.e '' S) (Θ.Φ x) h
  have himg : Θ.e.symm '' (Θ.e '' S) = S := by
    rw [Set.image_image,
      show (fun a => Θ.e.symm (Θ.e a)) = id from funext fun a => Θ.e.symm_apply_apply a,
      Set.image_id]
  rwa [himg, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h'

end ChamberIsoResidue

section ResidueSubtype

private theorem hmbRC_mem_restrict_residue_of_mem (hB : IsWeylDistanceBuilding cs δ)
    {I J : Set ι} (hIJ : I ⊆ J) {a : C} {b : C} (hb : b ∈ residue cs δ J a)
    {c : C} (hc : c ∈ residue cs δ J a) (h : c ∈ residue cs δ I b) :
    (⟨c, hc⟩ : ↥(residue cs δ J a)) ∈
      ((buildingOver cs δ J).restrict (residue cs δ J a)).residue
        {j : ↥J | (j : ι) ∈ I} ⟨b, hb⟩ := by
  revert hc
  induction h with
  | refl => intro hc; exact ((buildingOver cs δ J).restrict _).self_mem_residue _ ⟨b, hc⟩
  | @tail b' c' hb₁ hbc ih =>
    intro hc'
    obtain ⟨i, hi, hδ⟩ := hbc
    have hb'R : b' ∈ residue cs δ J a := by
      have hm : b' ∈ residue cs δ I c' :=
        Relation.ReflTransGen.head ⟨i, hi, hB.symm_of_eq_simple hδ⟩ Relation.ReflTransGen.refl
      have hmJ : b' ∈ residue cs δ J c' := residue_mono hIJ c' hm
      rwa [residue_eq_of_mem hB hc'] at hmJ
    have hjS : (⟨i, hIJ hi⟩ : ↥J) ∈ {j : ↥J | (j : ι) ∈ I} := hi
    have hadj : ((buildingOver cs δ J).restrict (residue cs δ J a)).adj ⟨i, hIJ hi⟩
        ⟨b', hb'R⟩ ⟨c', hc'⟩ :=
      (buildingOver_adj_iff hB ⟨i, hIJ hi⟩ b' c').mpr (Or.inr hδ)
    have hstep : (⟨c', hc'⟩ : ↥(residue cs δ J a)) ∈
        ((buildingOver cs δ J).restrict (residue cs δ J a)).residue
          {j : ↥J | (j : ι) ∈ I} ⟨b', hb'R⟩ :=
      ((buildingOver cs δ J).restrict _).residue_mono (Set.singleton_subset_iff.mpr hjS)
        ⟨b', hb'R⟩ (((buildingOver cs δ J).restrict _).mem_residue_singleton.mpr hadj)
    exact ((buildingOver cs δ J).restrict _).mem_residue_trans (ih hb'R) hstep

private theorem hmbRC_mem_residue_of_mem_restrict (hB : IsWeylDistanceBuilding cs δ)
    {I J : Set ι} (hIJ : I ⊆ J) {a : C} {b : C} (hb : b ∈ residue cs δ J a)
    {c : C} (hc : c ∈ residue cs δ J a)
    (h : (⟨c, hc⟩ : ↥(residue cs δ J a)) ∈
      ((buildingOver cs δ J).restrict (residue cs δ J a)).residue
        {j : ↥J | (j : ι) ∈ I} ⟨b, hb⟩) :
    c ∈ residue cs δ I b := by
  obtain ⟨γ, hγ, hS, hend⟩ := h
  have key : ∀ (bb : ↥(residue cs δ J a)) (γ : List (↥J × ↥(residue cs δ J a))),
      ((buildingOver cs δ J).restrict (residue cs δ J a)).IsGallery bb γ →
      (∀ j ∈ galleryType γ, (j : ι) ∈ I) →
      ((galleryEnd bb γ : ↥(residue cs δ J a)) : C) ∈ residue cs δ I (bb : C) := by
    intro bb γ
    induction γ generalizing bb with
    | nil => intro _ _; exact Relation.ReflTransGen.refl
    | cons p γ ih =>
      intro hγ hSj
      obtain ⟨h1, h2⟩ := hγ
      have hp : (p.1 : ι) ∈ I := hSj p.1 (by simp)
      have hmem1 : (p.2 : C) ∈ residue cs δ I (bb : C) := by
        rcases (buildingOver_adj_iff hB p.1 (bb : C) (p.2 : C)).mp h1 with h | h
        · rw [(hB.eq_one_iff _ _).mp h]; exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.head ⟨p.1, hp, h⟩ Relation.ReflTransGen.refl
      exact mem_residue_trans hmem1 (ih p.2 h2 fun j hj => hSj j (by simp [hj]))
  have hmain := key ⟨b, hb⟩ γ hγ hS
  rwa [hend] at hmain

end ResidueSubtype

theorem mem_residue_iff_of_chamberIso (hB : IsWeylDistanceBuilding cs δ) {J I : Set ι} {a : C}
    {ι' Ω : Type} {Y : ChamberSystem ι' Ω}
    (Θ : ChamberIso ((buildingOver cs δ J).restrict (residue cs δ J a)) Y) (hIJ : I ⊆ J)
    (x c : ↥(residue cs δ J a)) :
    (c : C) ∈ residue cs δ I x ↔ Θ.Φ c ∈ Y.residue (Θ.e '' {j | (j : ι) ∈ I}) (Θ.Φ x) := by
  have h1 : (c : C) ∈ residue cs δ I (x : C) ↔
      c ∈ ((buildingOver cs δ J).restrict (residue cs δ J a)).residue
        {j : ↥J | (j : ι) ∈ I} x :=
    ⟨fun h => hmbRC_mem_restrict_residue_of_mem hB hIJ x.2 c.2 h,
      fun h => hmbRC_mem_residue_of_mem_restrict hB hIJ x.2 c.2 h⟩
  have h2 := hmbRC_chamberIso_residue_iff Θ {j : ↥J | (j : ι) ∈ I} x c
  exact h1.trans h2

section Product

private theorem hmbRC_adj_I_iff (hB : IsWeylDistanceBuilding cs δ) {I : Set ι} {z : ι}
    (hz : z ∉ I) (hcomm : ∀ i ∈ I, M i z = 2) {c y y' : C}
    (hy : y ∈ residue cs δ (insert z I) c) (hy' : y' ∈ residue cs δ (insert z I) c)
    {i : ι} (hi : i ∈ I) :
    (δ y y' = 1 ∨ δ y y' = cs.simple i) ↔
      ((δ (resProj cs δ I c y) (resProj cs δ I c y') = 1 ∨
        δ (resProj cs δ I c y) (resProj cs δ I c y') = cs.simple i) ∧
        resProj cs δ {z} c y = resProj cs δ {z} c y') := by
  constructor
  · rintro (h | h)
    · have hyy : y = y' := (hB.eq_one_iff y y').mp h
      subst hyy
      exact ⟨Or.inl (hB.eq_one_self _), rfl⟩
    · obtain ⟨hq, hp⟩ := (dist_eq_simple_iff_of_mem hB hz hcomm hy hy' hi).mp h
      exact ⟨Or.inr hp, hq⟩
  · rintro ⟨hp | hp, hq⟩
    · have hpp : resProj cs δ I c y = resProj cs δ I c y' := (hB.eq_one_iff _ _).mp hp
      have hyy : y = y' := eq_of_resProj_eq hB hz hcomm hy hy' hpp hq
      rw [hyy]
      exact Or.inl (hB.eq_one_self _)
    · exact Or.inr ((dist_eq_simple_iff_of_mem hB hz hcomm hy hy' hi).mpr ⟨hq, hp⟩)

private theorem hmbRC_adj_z_iff (hB : IsWeylDistanceBuilding cs δ) {I : Set ι} {z : ι}
    (hz : z ∉ I) (hcomm : ∀ i ∈ I, M i z = 2) {c y y' : C}
    (hy : y ∈ residue cs δ (insert z I) c) (hy' : y' ∈ residue cs δ (insert z I) c) :
    (δ y y' = 1 ∨ δ y y' = cs.simple z) ↔
      (resProj cs δ I c y = resProj cs δ I c y' ∧
        (δ (resProj cs δ {z} c y) (resProj cs δ {z} c y') = 1 ∨
         δ (resProj cs δ {z} c y) (resProj cs δ {z} c y') = cs.simple z)) := by
  constructor
  · rintro (h | h)
    · have hyy : y = y' := (hB.eq_one_iff y y').mp h
      subst hyy
      exact ⟨rfl, Or.inl (hB.eq_one_self _)⟩
    · have h' := (dist_eq_simple_z_iff hB hz hcomm hy hy').mp h
      refine ⟨h'.1, Or.inr ?_⟩
      refine dist_eq_simple_of_mem_panel hB ?_ (fun h => h'.2 h.symm)
      change resProj cs δ {z} c y' ∈ residue cs δ {z} (resProj cs δ {z} c y)
      rw [residue_eq_of_mem hB (resProj_mem hB {z} c y)]
      exact resProj_mem hB {z} c y'
  · rintro ⟨hp, hq | hq⟩
    · have hyy : y = y' := eq_of_resProj_eq hB hz hcomm hy hy' hp ((hB.eq_one_iff _ _).mp hq)
      rw [hyy]
      exact Or.inl (hB.eq_one_self _)
    · exact Or.inr ((dist_eq_simple_z_iff hB hz hcomm hy hy').mpr ⟨hp, hB.ne_of_eq_simple hq⟩)

variable (hB : IsWeylDistanceBuilding cs δ) {I : Set ι} {z : ι} (hz : z ∉ I)
  (hcomm : ∀ i ∈ I, M i z = 2) (c : C)

noncomputable def prodChart (hB : IsWeylDistanceBuilding cs δ) {I : Set ι} {z : ι} (hz : z ∉ I)
    (hcomm : ∀ i ∈ I, M i z = 2) (c : C) :
    ChamberIso ((buildingOver cs δ (insert z I)).restrict (residue cs δ (insert z I) c))
      (((buildingOver cs δ I).restrict (residue cs δ I c)).prod
        ((buildingOver cs δ {z}).restrict (residue cs δ {z} c))) := by
  classical
  let e : ↥(insert z I) ≃ (↥I ⊕ ↥({z} : Set ι)) :=
    (Equiv.Set.insert hz).trans (Equiv.sumCongr (Equiv.refl _) (Equiv.Set.singleton z).symm)
  let F : ↥(residue cs δ (insert z I) c) →
      (↥(residue cs δ I c) × ↥(residue cs δ {z} c)) := fun y =>
    (⟨resProj cs δ I c y, resProj_mem hB I c y⟩,
     ⟨resProj cs δ {z} c y, resProj_mem hB {z} c y⟩)
  have hF : Function.Bijective F := by
    constructor
    · intro y y' h
      apply Subtype.ext
      exact eq_of_resProj_eq hB hz hcomm y.2 y'.2
        (congrArg (fun t => ((t.1 : ↥(residue cs δ I c)) : C)) h)
        (congrArg (fun t => ((t.2 : ↥(residue cs δ {z} c)) : C)) h)
    · intro t
      obtain ⟨y, hy, hpy, hqy⟩ := exists_resProj_eq hB hz hcomm t.1.2 t.2.2
      exact ⟨⟨y, hy⟩, Prod.ext (Subtype.ext hpy) (Subtype.ext hqy)⟩
  refine
    { e := e
      Φ := Equiv.ofBijective F hF
      adj_iff := ?_ }
  intro j y y'
  have hjC : (j : ι) = z ∨ (j : ι) ∈ I := Set.mem_insert_iff.mp j.2
  rcases hjC with hjz | hjI
  · have hj : j = (⟨z, Or.inl rfl⟩ : ↥(insert z I)) := Subtype.ext hjz
    have hez : e (⟨z, Or.inl rfl⟩ : ↥(insert z I)) =
        (Sum.inr (⟨z, rfl⟩ : ↥({z} : Set ι))) := by
      rw [show e = (Equiv.Set.insert hz).trans
          (Equiv.sumCongr (Equiv.refl _) (Equiv.Set.singleton z).symm) from rfl,
        Equiv.trans_apply,
        show (Equiv.Set.insert hz) ⟨z, Or.inl rfl⟩ = Sum.inr PUnit.unit from
          Equiv.Set.insert_apply_left hz]
      rfl
    rw [hj, hez]
    change ((buildingOver cs δ (insert z I)).adj ⟨z, Or.inl rfl⟩ (y : C) (y' : C)) ↔
      ((⟨resProj cs δ I c (y : C), resProj_mem hB I c (y : C)⟩ : ↥(residue cs δ I c)) =
        ⟨resProj cs δ I c (y' : C), resProj_mem hB I c (y' : C)⟩ ∧
       (buildingOver cs δ {z}).adj (⟨z, rfl⟩ : ↥({z} : Set ι))
        (resProj cs δ {z} c (y : C)) (resProj cs δ {z} c (y' : C)))
    rw [Subtype.ext_iff, buildingOver_adj_iff hB ⟨z, Or.inl rfl⟩ (y : C) (y' : C),
      buildingOver_adj_iff hB (⟨z, rfl⟩ : ↥({z} : Set ι))
        (resProj cs δ {z} c (y : C)) (resProj cs δ {z} c (y' : C))]
    exact hmbRC_adj_z_iff hB hz hcomm y.2 y'.2
  · have hj : j = (⟨(j : ι), Or.inr hjI⟩ : ↥(insert z I)) := Subtype.ext rfl
    have hei : e (⟨(j : ι), Or.inr hjI⟩ : ↥(insert z I)) =
        (Sum.inl (⟨(j : ι), hjI⟩ : ↥I)) := by
      rw [show e = (Equiv.Set.insert hz).trans
          (Equiv.sumCongr (Equiv.refl _) (Equiv.Set.singleton z).symm) from rfl,
        Equiv.trans_apply,
        show (Equiv.Set.insert hz) ⟨(j : ι), Or.inr hjI⟩ = Sum.inl ⟨(j : ι), hjI⟩ from
          Equiv.Set.insert_apply_right hz ⟨(j : ι), hjI⟩]
      rfl
    rw [hj, hei]
    change ((buildingOver cs δ (insert z I)).adj ⟨(j : ι), Or.inr hjI⟩ (y : C) (y' : C)) ↔
      (((buildingOver cs δ I).adj (⟨(j : ι), hjI⟩ : ↥I)
          (resProj cs δ I c (y : C)) (resProj cs δ I c (y' : C))) ∧
        (⟨resProj cs δ {z} c (y : C), resProj_mem hB {z} c (y : C)⟩ :
            ↥(residue cs δ {z} c)) =
          ⟨resProj cs δ {z} c (y' : C), resProj_mem hB {z} c (y' : C)⟩)
    rw [Subtype.ext_iff, buildingOver_adj_iff hB ⟨(j : ι), Or.inr hjI⟩ (y : C) (y' : C),
      buildingOver_adj_iff hB (⟨(j : ι), hjI⟩ : ↥I)
        (resProj cs δ I c (y : C)) (resProj cs δ I c (y' : C))]
    exact hmbRC_adj_I_iff hB hz hcomm y.2 y'.2 hjI

theorem prodChart_e_of_mem {i : ι} (hi : i ∈ I) :
    (prodChart hB hz hcomm c).e ⟨i, Set.mem_insert_of_mem z hi⟩ = Sum.inl ⟨i, hi⟩ := by
  classical
  simp only [prodChart, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [show (⟨i, Set.mem_insert_of_mem z hi⟩ : ↥(insert z I)) =
    ⟨((⟨i, hi⟩ : ↥I) : ι), Or.inr hi⟩ from rfl, Equiv.Set.insert_apply_right]
  rfl

theorem prodChart_e_self :
    (prodChart hB hz hcomm c).e ⟨z, Set.mem_insert z I⟩ = Sum.inr ⟨z, rfl⟩ := by
  classical
  simp only [prodChart, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [show (⟨z, Set.mem_insert z I⟩ : ↥(insert z I)) = ⟨z, Or.inl rfl⟩ from rfl,
    Equiv.Set.insert_apply_left]
  rfl

theorem prodChart_apply (y : ↥(residue cs δ (insert z I) c)) :
    ((((prodChart hB hz hcomm c).Φ y).1 : ↥(residue cs δ I c)) : C) =
        resProj cs δ I c y ∧
      ((((prodChart hB hz hcomm c).Φ y).2 : ↥(residue cs δ {z} c)) : C) =
        resProj cs δ {z} c y :=
  ⟨rfl, rfl⟩

theorem prodChart_symm_apply_of_mem {p q y : C} (hp : p ∈ residue cs δ I c)
    (hq : q ∈ residue cs δ {z} c) (hyp : y ∈ residue cs δ {z} p) (hyq : y ∈ residue cs δ I q) :
    (((prodChart hB hz hcomm c).Φ.symm (⟨p, hp⟩, ⟨q, hq⟩) :
      ↥(residue cs δ (insert z I) c)) : C) = y := by
  have hwzI : ({z} : Set ι) ⊆ insert z I :=
    Set.singleton_subset_iff.mpr (Set.mem_insert z I)
  have hqJ : q ∈ residue cs δ (insert z I) c := residue_mono hwzI c hq
  have hyJ : y ∈ residue cs δ (insert z I) c := by
    rw [← residue_eq_of_mem hB hqJ]
    exact residue_mono (Set.subset_insert z I) q hyq
  have hresI : resProj cs δ I c y = p :=
    resProj_eq hB (isProjection_of_panel hB hz hcomm hp ((mem_panel_iff hB).mp hyp))
  have hresZ : resProj cs δ {z} c y = q :=
    resProj_eq hB (isProjection_of_res hB hz hq ((mem_residue_iff_mem_parabolic hB).mp hyq))
  have hΦ : (prodChart hB hz hcomm c).Φ ⟨y, hyJ⟩ = (⟨p, hp⟩, ⟨q, hq⟩) := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [(prodChart_apply hB hz hcomm c ⟨y, hyJ⟩).1, hresI]
    · rw [(prodChart_apply hB hz hcomm c ⟨y, hyJ⟩).2, hresZ]
  have hsymm : (prodChart hB hz hcomm c).Φ.symm (⟨p, hp⟩, ⟨q, hq⟩) = ⟨y, hyJ⟩ :=
    (Equiv.symm_apply_eq (prodChart hB hz hcomm c).Φ).mpr hΦ.symm
  simpa using congrArg Subtype.val hsymm

end Product

end CFSG.ClassicalInvolution.Phan.PhanE.Res

end
