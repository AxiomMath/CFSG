module

public import CFSG.Monster.B.Geometry.InitialIsometryExt

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.E6.StdF4

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
variable {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

@[expose] def liftResMap {R : Set C} {R' : Set C'} (G : R → R') (dflt : C → C') (x : C) : C' :=
  open _root_.Classical in if h : x ∈ R then (G ⟨x, h⟩ : C') else dflt x

theorem liftResMap_of_mem {R : Set C} {R' : Set C'} (G : R → R') (dflt : C → C') {x : C}
    (hx : x ∈ R) : liftResMap G dflt x = G ⟨x, hx⟩ := by
  rw [liftResMap, dite_eq_left hx]

theorem resMap_liftResMap {R : Set C} {R' : Set C'} (G : R → R') (dflt : C → C') (y : R') :
    resMap (R := R) (liftResMap G dflt) y = G := funext fun x => Subtype.ext (by
  rw [coe_resMap (by rw [liftResMap_of_mem G dflt x.2]; exact (G _).2),
    liftResMap_of_mem G dflt x.2])

theorem isTypeIso_liftResMap (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {J : Set ι} {c : C} {c' : C'}
    {G : residue cs δ J c → residue cs δ' J c'}
    (hG : IsTypeIso (parCS M J) (fun x y : residue cs δ J c => parDist cs δ J x y)
      (fun x y : residue cs δ' J c' => parDist cs δ' J x y) Set.univ Set.univ G)
    (dflt : C → C') :
    IsTypeIso cs δ δ' (residue cs δ J c) (residue cs δ' J c') (liftResMap G dflt) := by
  have hmaps : Set.MapsTo (liftResMap G dflt) (residue cs δ J c) (residue cs δ' J c') :=
    fun x hx => by rw [liftResMap_of_mem G dflt hx]; exact (G _).2
  rw [isTypeIso_resMap_iff hδ hδ' subset_rfl subset_rfl hmaps ⟨c', self_mem_residue J c'⟩,
    resMap_liftResMap, Subtype.coe_preimage_self, Subtype.coe_preimage_self]
  exact hG

theorem IsTypeIso.trans {C'' : Type*} {δ'' : C'' → C'' → W} {X : Set C} {X' : Set C'}
    {X'' : Set C''} {f : C → C'} {g : C' → C''} (hf : IsTypeIso cs δ δ' X X' f)
    (hg : IsTypeIso cs δ' δ'' X' X'' g) : IsTypeIso cs δ δ'' X X'' (g ∘ f) :=
  ⟨hg.1.comp hf.1, fun x hx y hy i =>
    (hg.2 _ (hf.1.mapsTo hx) _ (hf.1.mapsTo hy) i).trans (hf.2 x hx y hy i)⟩

section Models

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hδ' : IsWeylDistanceBuilding cs δ')
  {J : Set ι} {u t s : J} (hut : u ≠ t) (hts : t ≠ s) (hus : u ≠ s)
  (hJ : ∀ i : J, i = u ∨ i = t ∨ i = s) (hMut : M u t = 3) (hMts : M t s = 4) (hMus : M u s = 2)
include hδ hδ' hut hts hus hJ hMut hMts hMus

theorem foundationExtension_unitary {c : C} {c' : C'} {f : residue cs δ J c → PFlag UData}
    {f' : residue cs δ' J c' → PFlag UData}
    (hf : IsChamberModel cs (resDist cs δ J c) (polarChamber UData (u : ι) t s) f)
    (hf' : IsChamberModel cs (resDist cs δ' J c') (polarChamber UData (u : ι) t s) f') :
    FoundationExtension (parCS M J) (fun x y : residue cs δ J c => parDist cs δ J x y)
      (fun x y : residue cs δ' J c' => parDist cs δ' J x y) := by
  have := finite_parGroup cs J
  exact (classical_rank_three_opposite_foundation_extension (parCS M J)
    (fun x y : residue cs δ J c => parDist cs δ J x y)
    (fun x y : residue cs δ' J c' => parDist cs δ' J x y)
    (isWeylDistanceBuilding_parDist hδ J c) (isWeylDistanceBuilding_parDist hδ' J c')).1
    u t s hut hts hus hJ hMut hMts hMus f f'
    (isChamberModel_parDist hδ (fun j => polarChamber_subtype_adj j) hf)
    (isChamberModel_parDist hδ' (fun j => polarChamber_subtype_adj j) hf')

theorem foundationExtension_orth {c : C} {c' : C'} {f : residue cs δ J c → PFlag OData}
    {f' : residue cs δ' J c' → PFlag OData}
    (hf : IsChamberModel cs (resDist cs δ J c) (polarChamber OData (u : ι) t s) f)
    (hf' : IsChamberModel cs (resDist cs δ' J c') (polarChamber OData (u : ι) t s) f') :
    FoundationExtension (parCS M J) (fun x y : residue cs δ J c => parDist cs δ J x y)
      (fun x y : residue cs δ' J c' => parDist cs δ' J x y) := by
  have := finite_parGroup cs J
  exact (classical_rank_three_opposite_foundation_extension (parCS M J)
    (fun x y : residue cs δ J c => parDist cs δ J x y)
    (fun x y : residue cs δ' J c' => parDist cs δ' J x y)
    (isWeylDistanceBuilding_parDist hδ J c) (isWeylDistanceBuilding_parDist hδ' J c')).2.1
    u t s hut hts hus hJ hMut hMts hMus f f'
    (isChamberModel_parDist hδ (fun j => polarChamber_subtype_adj j) hf)
    (isChamberModel_parDist hδ' (fun j => polarChamber_subtype_adj j) hf')

theorem exists_typeIso_unitary {c y : C} {c' y' : C'} {f : residue cs δ J c → PFlag UData}
    {f' : residue cs δ' J c' → PFlag UData}
    (hf : IsChamberModel cs (resDist cs δ J c) (polarChamber UData (u : ι) t s) f)
    (hf' : IsChamberModel cs (resDist cs δ' J c') (polarChamber UData (u : ι) t s) f')
    (hy : y ∈ residue cs δ J c) (hy' : y' ∈ residue cs δ' J c') (hcy : δ c y = longest cs J)
    (hcy' : δ' c' y' = longest cs J) :
    ∃ A : C → C', IsTypeIso cs δ δ' (residue cs δ J c) (residue cs δ' J c') A ∧ A c = c' ∧
      A y = y' := by
  have := finite_parGroup cs J
  have hB := isWeylDistanceBuilding_parDist hδ J c
  have hB' := isWeylDistanceBuilding_parDist hδ' J c'
  have hf₃ := isChamberModel_parDist hδ (fun j => polarChamber_subtype_adj (p := u) (l := t)
    (π := s) j) hf
  have hf₃' := isChamberModel_parDist hδ' (fun j => polarChamber_subtype_adj (p := u) (l := t)
    (π := s) j) hf'
  obtain ⟨c₀, hc₀⟩ := hf₃'.1.2 uC0
  obtain ⟨d₀, hd₀⟩ := hf₃'.1.2 uD0
  have htrans := transitive_of_standard
    (unitary_transitive hB' hut hts hus hJ hMut hMts hMus hf₃' hc₀ hd₀)
  have hψ := hf₃.isTypeIso hf₃'
  set c₃ : residue cs δ J c := ⟨c, self_mem_residue J c⟩
  set y₃ : residue cs δ J c := ⟨y, hy⟩
  have hopp : parDist cs δ J c y = longest (parCS M J) Set.univ :=
    (parDist_eq_longest_univ_iff hδ (self_mem_residue J c) hy).mpr hcy
  have hopp' : parDist cs δ' J c' y' = longest (parCS M J) Set.univ :=
    (parDist_eq_longest_univ_iff hδ' (self_mem_residue J c') hy').mpr hcy'
  have hψopp := (IsTypeIso.dist_eq_univ hB hB' hψ c₃ y₃).trans hopp
  obtain ⟨g, hg, hgc, hgy⟩ := htrans _ _ ⟨c', self_mem_residue J c'⟩ ⟨y', hy'⟩ hψopp hopp'
  have hG := IsTypeIso.comp hψ (isTypeIso_of_mem_typeAut hg)
  refine ⟨liftResMap _ (fun _ => c'), isTypeIso_liftResMap hδ hδ' hG _, ?_, ?_⟩
  · rw [liftResMap_of_mem _ _ (self_mem_residue J c)]
    exact congrArg Subtype.val hgc
  · rw [liftResMap_of_mem _ _ hy]
    exact congrArg Subtype.val hgy

theorem exists_typeIso_orth {c y : C} {c' y' : C'} {f : residue cs δ J c → PFlag OData}
    {f' : residue cs δ' J c' → PFlag OData}
    (hf : IsChamberModel cs (resDist cs δ J c) (polarChamber OData (u : ι) t s) f)
    (hf' : IsChamberModel cs (resDist cs δ' J c') (polarChamber OData (u : ι) t s) f')
    (hy : y ∈ residue cs δ J c) (hy' : y' ∈ residue cs δ' J c') (hcy : δ c y = longest cs J)
    (hcy' : δ' c' y' = longest cs J) :
    ∃ A : C → C', IsTypeIso cs δ δ' (residue cs δ J c) (residue cs δ' J c') A ∧ A c = c' ∧
      A y = y' := by
  have := finite_parGroup cs J
  have hB := isWeylDistanceBuilding_parDist hδ J c
  have hB' := isWeylDistanceBuilding_parDist hδ' J c'
  have hf₃ := isChamberModel_parDist hδ (fun j => polarChamber_subtype_adj (p := u) (l := t)
    (π := s) j) hf
  have hf₃' := isChamberModel_parDist hδ' (fun j => polarChamber_subtype_adj (p := u) (l := t)
    (π := s) j) hf'
  obtain ⟨c₀, hc₀⟩ := hf₃'.1.2 oC0
  obtain ⟨d₀, hd₀⟩ := hf₃'.1.2 oD0
  have htrans := transitive_of_standard
    (orth_transitive hB' hut hts hus hJ hMut hMts hMus hf₃' hc₀ hd₀)
  have hψ := hf₃.isTypeIso hf₃'
  set c₃ : residue cs δ J c := ⟨c, self_mem_residue J c⟩
  set y₃ : residue cs δ J c := ⟨y, hy⟩
  have hopp : parDist cs δ J c y = longest (parCS M J) Set.univ :=
    (parDist_eq_longest_univ_iff hδ (self_mem_residue J c) hy).mpr hcy
  have hopp' : parDist cs δ' J c' y' = longest (parCS M J) Set.univ :=
    (parDist_eq_longest_univ_iff hδ' (self_mem_residue J c') hy').mpr hcy'
  have hψopp := (IsTypeIso.dist_eq_univ hB hB' hψ c₃ y₃).trans hopp
  obtain ⟨g, hg, hgc, hgy⟩ := htrans _ _ ⟨c', self_mem_residue J c'⟩ ⟨y', hy'⟩ hψopp hopp'
  have hG := IsTypeIso.comp hψ (isTypeIso_of_mem_typeAut hg)
  refine ⟨liftResMap _ (fun _ => c'), isTypeIso_liftResMap hδ hδ' hG _, ?_, ?_⟩
  · rw [liftResMap_of_mem _ _ (self_mem_residue J c)]
    exact congrArg Subtype.val hgc
  · rw [liftResMap_of_mem _ _ hy]
    exact congrArg Subtype.val hgy

end Models

end CFSG.Monster.B.Geometry
