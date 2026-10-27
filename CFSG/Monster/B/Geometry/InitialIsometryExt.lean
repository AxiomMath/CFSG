module

public import CFSG.Monster.B.Geometry.InitialIsometryResidue
public import CFSG.Monster.B.Geometry.ClassicalExtension

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.E6.StdF4

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

variable (cs δ δ') in
@[expose] def Ext₃At (J : Set ι) : Prop :=
  ∀ (a b : C) (a' b' : C'),
    b ∈ residue cs δ J a → b' ∈ residue cs δ' J a' →
      δ a b = longest cs J → δ' a' b' = longest cs J →
        ∀ f : C → C', IsWeylIsometry δ δ' (residueFoundation cs δ J a ∪ {b})
            (residueFoundation cs δ' J a' ∪ {b'}) f → f a = a' → f b = b' →
          (∃ F : C → C', IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') F ∧
              IsWeylIsometry δ δ' (residue cs δ J a) (residue cs δ' J a') F ∧
              Set.EqOn F f (residueFoundation cs δ J a ∪ {b})) ∧
            ∀ F₁ F₂ : C → C',
              IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') F₁ →
              IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') F₂ →
              Set.EqOn F₁ f (residueFoundation cs δ J a ∪ {b}) →
              Set.EqOn F₂ f (residueFoundation cs δ J a ∪ {b}) →
              Set.EqOn F₁ F₂ (residue cs δ J a)

theorem ext₃_of_ext₃At (h : ∀ J : Set ι, J.ncard = 3 → Ext₃At cs δ δ' J) : Ext₃ cs δ δ' := h

variable (cs δ) in
@[expose] def Rig₂At (i j : ι) : Prop :=
  ∀ (a b : C), b ∈ residue cs δ {i, j} a → δ a b = longest cs {i, j} →
    ∀ g : C → C, IsTypeIso cs δ δ (residue cs δ {i, j} a) (residue cs δ {i, j} a) g →
      g b = b → (∀ x ∈ panel cs δ i a ∪ panel cs δ j a, g x = x) →
        ∀ x ∈ residue cs δ {i, j} a, g x = x

theorem rig₂_of_rig₂At (h : ∀ i j : ι, i ≠ j → Rig₂At cs δ i j) : Rig₂ cs δ := h

theorem rig₂At_of_commute (hδ : IsWeylDistanceBuilding cs δ) {i j : ι} (hij : i ≠ j)
    (hM : M i j = 2) : Rig₂At cs δ i j := fun _ _ _ _ _ hg _ hfix =>
  fix_residue_of_commute hδ hij hM hg hfix

theorem residue_subset_residueFoundation {K J : Set ι} (hK : K ⊆ J) (hK2 : K.encard ≤ 2)
    (x : C) : residue cs δ K x ⊆ residueFoundation cs δ J x := fun _ hy =>
  mem_residueFoundation_iff.mpr ⟨K, ⟨hK, hK2⟩, hy⟩

theorem self_mem_residueFoundation (J : Set ι) (x : C) : x ∈ residueFoundation cs δ J x :=
  residue_subset_residueFoundation (Set.empty_subset J) (by simp) x (self_mem_residue _ x)

section Commute

variable (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
include hδ hδ'

theorem ext₃At_of_commute {I : Set ι} {z : ι} (hz : z ∉ I) (hcomm : ∀ i ∈ I, M i z = 2)
    (hI : I.encard ≤ 2) : Ext₃At cs δ δ' (insert z I) := by
  intro a b a' b' hb hb' _ _ f hf hfa hfb
  set J := insert z I
  have hIJ : I ⊆ J := Set.subset_insert z I
  have hzJ : ({z} : Set ι) ⊆ J := Set.singleton_subset_iff.mpr (Set.mem_insert z I)
  have hsubF : ∀ {K : Set ι}, K ⊆ J → K.encard ≤ 2 → ∀ x : C,
      residue cs δ K x ⊆ residueFoundation cs δ J x := fun hK hK2 x =>
    residue_subset_residueFoundation hK hK2 x
  have hsubF' : ∀ {K : Set ι}, K ⊆ J → K.encard ≤ 2 → ∀ x : C',
      residue cs δ' K x ⊆ residueFoundation cs δ' J x := fun hK hK2 x =>
    residue_subset_residueFoundation hK hK2 x
  have hz2 : ({z} : Set ι).encard ≤ 2 := by rw [Set.encard_singleton]; norm_num
  have ha : a ∈ residueFoundation cs δ J a ∪ {b} := Or.inl (self_mem_residueFoundation J a)
  have hbI := hf.bijOn_residue hδ hδ' ha hfa ((hsubF hIJ hI a).trans Set.subset_union_left)
    ((hsubF' hIJ hI a').trans Set.subset_union_left)
  have hbz := hf.bijOn_residue hδ hδ' ha hfa ((hsubF hzJ hz2 a).trans Set.subset_union_left)
    ((hsubF' hzJ hz2 a').trans Set.subset_union_left)
  have hdI : ∀ x ∈ residue cs δ I a, ∀ y ∈ residue cs δ I a, δ' (f x) (f y) = δ x y :=
    fun x hx y hy => hf.2 x (Or.inl (hsubF hIJ hI a hx)) y (Or.inl (hsubF hIJ hI a hy))
  have hF := isTypeIso_prodMap hδ hδ' hz hcomm hbI hbz hdI
  set F := prodMap cs δ δ' I z a a' f f
  have hdomR : residueFoundation cs δ J a ∪ {b} ⊆ residue cs δ J a :=
    Set.union_subset (residueFoundation_subset_residue J a) (Set.singleton_subset_iff.mpr hb)
  have hdomR' : residueFoundation cs δ' J a' ∪ {b'} ⊆ residue cs δ' J a' :=
    Set.union_subset (residueFoundation_subset_residue J a') (Set.singleton_subset_iff.mpr hb')
  have hagree : Set.EqOn F f (residueFoundation cs δ J a ∪ {b}) := by
    intro y hy
    have h₁ := resProj_map hδ hδ' (y := y) hbI fun q hq => hf.2 y hy q
      (Or.inl (hsubF hIJ hI a hq))
    have h₂ := resProj_map hδ hδ' (y := y) hbz fun q hq => hf.2 y hy q
      (Or.inl (hsubF hzJ hz2 a hq))
    exact (eq_prodMap hδ hδ' hz hcomm hbI hbz (hdomR' (hf.1.mapsTo hy)) h₁ h₂).symm
  refine ⟨⟨F, hF, hF.isWeylIsometry hδ hδ', hagree⟩, fun F₁ F₂ hF₁ hF₂ hF₁f hF₂f => ?_⟩
  have key : ∀ G : C → C', IsTypeIso cs δ δ' (residue cs δ J a) (residue cs δ' J a') G →
      Set.EqOn G f (residueFoundation cs δ J a ∪ {b}) → Set.EqOn G F (residue cs δ J a) := by
    intro G hG hGf y hy
    have hGI : Set.BijOn G (residue cs δ I a) (residue cs δ' I a') :=
      hbI.congr fun x hx => (hGf (Or.inl (hsubF hIJ hI a hx))).symm
    have hGz : Set.BijOn G (panel cs δ z a) (panel cs δ' z a') :=
      hbz.congr fun x hx => (hGf (Or.inl (hsubF hzJ hz2 a hx))).symm
    have h₁ := resProj_map hδ hδ' (y := y) hGI fun q hq =>
      hG.dist_eq hδ hδ' hy (residue_mono hIJ a hq)
    have h₂ := resProj_map hδ hδ' (y := y) hGz fun q hq =>
      hG.dist_eq hδ hδ' hy (residue_mono hzJ a hq)
    rw [hGf (Or.inl (hsubF hIJ hI a (resProj_mem hδ I a y)))] at h₁
    rw [hGf (Or.inl (hsubF hzJ hz2 a (resProj_mem hδ {z} a y)))] at h₂
    exact eq_prodMap hδ hδ' hz hcomm hbI hbz (hG.1.mapsTo hy) h₁ h₂
  intro y hy
  rw [key F₁ hF₁ hF₁f hy, key F₂ hF₂ hF₂f hy]

end Commute

section Transfer

variable (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
include hδ hδ'

theorem ext₃At_of_foundationExtension [Finite W] (J : Set ι)
    (hFE : ∀ (a : C) (a' : C'), FoundationExtension (parCS M J)
      (fun x y : residue cs δ J a => parDist cs δ J x y)
      (fun x y : residue cs δ' J a' => parDist cs δ' J x y)) :
    Ext₃At cs δ δ' J := by
  classical
  intro a b a' b' hb hb' hab hab' f hf hfa hfb
  set R := residue cs δ J a
  set R' := residue cs δ' J a'
  have hdom : residueFoundation cs δ J a ∪ {b} ⊆ R :=
    Set.union_subset (residueFoundation_subset_residue J a) (Set.singleton_subset_iff.mpr hb)
  have hdom' : residueFoundation cs δ' J a' ∪ {b'} ⊆ R' :=
    Set.union_subset (residueFoundation_subset_residue J a') (Set.singleton_subset_iff.mpr hb')
  set a₃ : R := ⟨a, self_mem_residue J a⟩
  set b₃ : R := ⟨b, hb⟩
  set a₃' : R' := ⟨a', self_mem_residue J a'⟩
  set b₃' : R' := ⟨b', hb'⟩
  have hpre : Subtype.val ⁻¹' (residueFoundation cs δ J a ∪ {b}) =
      foundation (parCS M J) (fun x y : R => parDist cs δ J x y) 2 a₃ ∪ {b₃} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff]
    rw [mem_foundation_parDist_iff hδ a₃ x, Subtype.ext_iff]
  have hpre' : Subtype.val ⁻¹' (residueFoundation cs δ' J a' ∪ {b'}) =
      foundation (parCS M J) (fun x y : R' => parDist cs δ' J x y) 2 a₃' ∪ {b₃'} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_singleton_iff]
    rw [mem_foundation_parDist_iff hδ' a₃' x, Subtype.ext_iff]
  have hf₃ := (isWeylIsometry_resMap_iff hδ hδ' hdom hdom' hf.1.mapsTo a₃').mp hf
  rw [hpre, hpre'] at hf₃
  have hcoe : ∀ x : R, (x : C) ∈ residueFoundation cs δ J a ∪ {b} →
      (resMap f a₃' x : C') = f x := fun x hx => coe_resMap (hdom' (hf.1.mapsTo hx))
  have hf₃a : resMap f a₃' a₃ = a₃' :=
    Subtype.ext ((hcoe a₃ (Or.inl (self_mem_residueFoundation J a))).trans hfa)
  have hf₃b : resMap f a₃' b₃ = b₃' := Subtype.ext ((hcoe b₃ (Or.inr rfl)).trans hfb)
  have hab₃ : parDist cs δ J a b = longest (parCS M J) Set.univ :=
    (parDist_eq_longest_univ_iff hδ (self_mem_residue J a) hb).mpr hab
  have hab₃' : parDist cs δ' J a' b' = longest (parCS M J) Set.univ :=
    (parDist_eq_longest_univ_iff hδ' (self_mem_residue J a') hb').mpr hab'
  obtain ⟨-, -, hext⟩ := hFE a a'
  obtain ⟨F₃, hF₃, hF₃e, hF₃u⟩ := hext a₃ b₃ a₃' b₃' hab₃ hab₃' _ hf₃ hf₃a hf₃b
  set F : C → C' := fun x => if h : x ∈ R then (F₃ ⟨x, h⟩ : C') else f x with hFdef
  have hFR : ∀ x : R, F x = F₃ x := fun x => by
    rw [hFdef]
    exact (dite_eq_left x.2).trans rfl
  have hFmaps : Set.MapsTo F R R' := fun x hx => by
    rw [hFR ⟨x, hx⟩]
    exact (F₃ ⟨x, hx⟩).2
  have hFres : resMap (R := R) F a₃' = F₃ := funext fun x =>
    Subtype.ext ((coe_resMap (hFmaps x.2)).trans (hFR x))
  have hFiso : IsTypeIso cs δ δ' R R' F := by
    rw [isTypeIso_resMap_iff hδ hδ' subset_rfl subset_rfl hFmaps a₃', hFres,
      Subtype.coe_preimage_self, Subtype.coe_preimage_self]
    exact hF₃
  have hFf : Set.EqOn F f (residueFoundation cs δ J a ∪ {b}) := by
    intro x hx
    have h1 := hF₃e (show (⟨x, hdom hx⟩ : R) ∈ foundation (parCS M J)
      (fun x y : R => parDist cs δ J x y) 2 a₃ ∪ {b₃} by rw [← hpre]; exact hx)
    rw [hFR ⟨x, hdom hx⟩, h1]
    exact hcoe ⟨x, hdom hx⟩ hx
  refine ⟨⟨F, hFiso, hFiso.isWeylIsometry hδ hδ', hFf⟩, fun F₁ F₂ hF₁ hF₂ hF₁f hF₂f => ?_⟩
  have key : ∀ G : C → C', IsTypeIso cs δ δ' R R' G →
      Set.EqOn G f (residueFoundation cs δ J a ∪ {b}) → resMap (R := R) G a₃' = F₃ := by
    intro G hG hGf
    have hGiso := (isTypeIso_resMap_iff hδ hδ' subset_rfl subset_rfl hG.1.mapsTo a₃').mp hG
    rw [Subtype.coe_preimage_self, Subtype.coe_preimage_self] at hGiso
    refine hF₃u _ hGiso fun x hx => ?_
    have hx' : (x : C) ∈ residueFoundation cs δ J a ∪ {b} := by
      rw [← Set.mem_preimage, hpre]
      exact hx
    exact Subtype.ext ((coe_resMap (hG.1.mapsTo x.2)).trans
      ((hGf hx').trans (hcoe x hx').symm))
  intro x hx
  have h1 := congrArg (fun G : R → R' => (G ⟨x, hx⟩ : C')) (key F₁ hF₁ hF₁f)
  have h2 := congrArg (fun G : R → R' => (G ⟨x, hx⟩ : C')) (key F₂ hF₂ hF₂f)
  rw [coe_resMap (hF₁.1.mapsTo hx)] at h1
  rw [coe_resMap (hF₂.1.mapsTo hx)] at h2
  rw [h1, h2]

end Transfer

theorem rig₂At_of_rig₂_parDist [Finite W] (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι}
    {i j : ι} (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j)
    (hR : ∀ a : C, Rig₂ (parCS M J) (fun x y : residue cs δ J a => parDist cs δ J x y)) :
    Rig₂At cs δ i j := by
  intro a b hb hab g hg hgb hfix
  set B := residue cs δ J a
  set a₃ : B := ⟨a, self_mem_residue J a⟩
  set i' : J := ⟨i, hi⟩
  set j' : J := ⟨j, hj⟩
  have himg : Subtype.val '' ({i', j'} : Set J) = {i, j} := by rw [Set.image_pair]
  have hX : residue cs δ {i, j} a ⊆ B := residue_mono (Set.pair_subset hi hj) a
  have hpre : Subtype.val ⁻¹' residue cs δ {i, j} a =
      residue (parCS M J) (fun x y : B => parDist cs δ J x y) {i', j'} a₃ := by
    ext x
    rw [Set.mem_preimage, mem_residue_parDist_iff hδ, himg]
  have hg₃ := (isTypeIso_resMap_iff hδ hδ hX hX hg.1.mapsTo a₃).mp hg
  rw [hpre] at hg₃
  have hbB : b ∈ B := hX hb
  have hb₃ : (⟨b, hbB⟩ : B) ∈ residue (parCS M J) (fun x y : B => parDist cs δ J x y)
      {i', j'} a₃ := by rw [← hpre]; exact hb
  have hab₃ : parDist cs δ J a b = longest (parCS M J) {i', j'} := by
    rw [parDist_eq_longest_iff hδ (self_mem_residue J a) hbB, himg]
    exact hab
  have hi'j' : i' ≠ j' := fun e => hij (congrArg Subtype.val e)
  have hfix₃ : ∀ x ∈ panel (parCS M J) (fun x y : B => parDist cs δ J x y) i' a₃ ∪
      panel (parCS M J) (fun x y : B => parDist cs δ J x y) j' a₃, resMap g a₃ x = x := by
    rintro x (hx | hx)
    · rw [panel, mem_residue_parDist_iff hδ, Set.image_singleton] at hx
      have hx' : (x : C) ∈ residue cs δ {i, j} a :=
        residue_mono (show ({i} : Set ι) ⊆ {i, j} from Set.singleton_subset_iff.mpr (Or.inl rfl))
          a hx
      exact Subtype.ext ((coe_resMap (hX (hg.1.mapsTo hx'))).trans (hfix x (Or.inl hx)))
    · rw [panel, mem_residue_parDist_iff hδ, Set.image_singleton] at hx
      have hx' : (x : C) ∈ residue cs δ {i, j} a :=
        residue_mono (show ({j} : Set ι) ⊆ {i, j} from Set.singleton_subset_iff.mpr (Or.inr rfl))
          a hx
      exact Subtype.ext ((coe_resMap (hX (hg.1.mapsTo hx'))).trans (hfix x (Or.inr hx)))
  have hkey := hR a i' j' hi'j' a₃ ⟨b, hbB⟩ hb₃ hab₃ (resMap g a₃) hg₃
    (Subtype.ext ((coe_resMap (hX (hg.1.mapsTo hb))).trans hgb)) hfix₃
  intro x hx
  have := congrArg Subtype.val (hkey ⟨x, hX hx⟩ (by rw [← hpre]; exact hx))
  rwa [coe_resMap (hX (hg.1.mapsTo hx))] at this

theorem isChamberModel_parDist (hδ : IsWeylDistanceBuilding cs δ) {J : Set ι} {a : C}
    {F : Type*} {Y : ChamberSystem ι F} {Y₃ : ChamberSystem J F}
    (hY : ∀ j : J, Y₃.adj j = Y.adj j) {f : residue cs δ J a → F}
    (hf : IsChamberModel cs (resDist cs δ J a) Y f) :
    IsChamberModel (parCS M J) (fun x y : residue cs δ J a => parDist cs δ J x y) Y₃ f :=
  ⟨hf.1, fun x y j => by rw [parDist_eq_simple_iff hδ x.2 y.2, hY]; exact hf.2 x y j⟩

theorem ofThree_subtype_adj {F : Type*} {L : Set ι} {i₁ i₂ i₃ : L} {r₁ r₂ r₃ : F → F → Prop}
    {h₁ : Equivalence r₁} {h₂ : Equivalence r₂} {h₃ : Equivalence r₃} (j : L) :
    (ChamberSystem.ofThree i₁ i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).adj j =
      (ChamberSystem.ofThree (i₁ : ι) i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).adj j := by
  unfold ChamberSystem.ofThree
  dsimp only
  by_cases e₁ : j = i₁
  · rw [ite_eq_left e₁, ite_eq_left (congrArg Subtype.val e₁)]
  · rw [ite_eq_right e₁, ite_eq_right fun e => e₁ (Subtype.ext e)]
    by_cases e₂ : j = i₂
    · rw [ite_eq_left e₂, ite_eq_left (congrArg Subtype.val e₂)]
    · rw [ite_eq_right e₂, ite_eq_right fun e => e₂ (Subtype.ext e)]
      by_cases e₃ : j = i₃
      · rw [ite_eq_left e₃, ite_eq_left (congrArg Subtype.val e₃)]
      · rw [ite_eq_right e₃, ite_eq_right fun e => e₃ (Subtype.ext e)]

theorem polarChamber_subtype_adj {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {P : PolarSpace K V} {L : Set ι} {p l π : L} (j : L) :
    (polarChamber P p l π).adj j = (polarChamber P (p : ι) l π).adj j :=
  ofThree_subtype_adj j

end CFSG.Monster.B.Geometry
