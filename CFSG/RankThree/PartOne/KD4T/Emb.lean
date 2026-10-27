module

public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.RankThree.PartOne.KD4T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

class E6Sub (τ : Tag) : Prop where
  rank_ge : Tag.E6.rank ≤ τ.rank
  cartan_eq : ∀ k l : Fin Tag.E6.rank,
    τ.cartan (Fin.castLE rank_ge k) (Fin.castLE rank_ge l) = Tag.E6.cartan k l
  roots_up : ∀ l ∈ Tag.E6.artifactRoots, l ++ List.replicate (τ.rank - Tag.E6.rank) 0 ∈
    τ.artifactRoots
  roots_down : ∀ l ∈ τ.artifactRoots, l.drop Tag.E6.rank = List.replicate (τ.rank - Tag.E6.rank) 0 →
    l.take Tag.E6.rank ∈ Tag.E6.artifactRoots
  cartan_zero : ∀ j i : Fin τ.rank, 1 ≤ j.val → j.val ≤ 4 → Tag.E6.rank ≤ i.val →
    τ.cartan j i = 0

instance : E6Sub .E7 :=
  have h : Tag.E6.rank ≤ Tag.E7.rank := by decide
  ⟨h, fun k l => sub_eq_zero.1 ((by decide +revert : ∀ (h : Tag.E6.rank ≤ Tag.E7.rank)
    (k l : Fin Tag.E6.rank), Tag.E7.cartan (Fin.castLE h k) (Fin.castLE h l) -
      Tag.E6.cartan k l = 0) h k l), by decide +kernel, by decide +kernel,
    fun j i h1 h2 h3 => sub_zero (Tag.E7.cartan j i) ▸ (by decide :
      ∀ j i : Fin Tag.E7.rank, 1 ≤ j.val → j.val ≤ 4 → Tag.E6.rank ≤ i.val →
        Tag.E7.cartan j i - 0 = 0) j i h1 h2 h3⟩

instance : E6Sub .E8 :=
  have h : Tag.E6.rank ≤ Tag.E8.rank := by decide
  ⟨h, fun k l => sub_eq_zero.1 ((by decide +revert : ∀ (h : Tag.E6.rank ≤ Tag.E8.rank)
    (k l : Fin Tag.E6.rank), Tag.E8.cartan (Fin.castLE h k) (Fin.castLE h l) -
      Tag.E6.cartan k l = 0) h k l), by decide +kernel, by decide +kernel,
    fun j i h1 h2 h3 => sub_zero (Tag.E8.cartan j i) ▸ (by decide :
      ∀ j i : Fin Tag.E8.rank, 1 ≤ j.val → j.val ≤ 4 → Tag.E6.rank ≤ i.val →
        Tag.E8.cartan j i - 0 = 0) j i h1 h2 h3⟩

@[expose] def e6Lat (τ : Tag) (β : Fin Tag.E6.rank → ℤ) : Fin τ.rank → ℤ :=
  fun i => if h : i.val < Tag.E6.rank then β ⟨i.val, h⟩ else 0

section Lattice

variable {τ : Tag}

theorem e6Lat_apply_of_le {β : Fin Tag.E6.rank → ℤ} {i : Fin τ.rank} (h : Tag.E6.rank ≤ i.val) :
    e6Lat τ β i = 0 := by
  simp [e6Lat, not_lt.2 h]

theorem e6Lat_add (β γ : Fin Tag.E6.rank → ℤ) : e6Lat τ (β + γ) = e6Lat τ β + e6Lat τ γ := by
  funext i
  by_cases h : i.val < Tag.E6.rank <;> simp [e6Lat, h]

theorem e6Lat_neg (β : Fin Tag.E6.rank → ℤ) : e6Lat τ (-β) = -e6Lat τ β := by
  funext i
  by_cases h : i.val < Tag.E6.rank <;> simp [e6Lat, h]

theorem e6Lat_sub (β γ : Fin Tag.E6.rank → ℤ) : e6Lat τ (β - γ) = e6Lat τ β - e6Lat τ γ := by
  funext i
  by_cases h : i.val < Tag.E6.rank <;> simp [e6Lat, h]

theorem e6Lat_smul (n : ℤ) (β : Fin Tag.E6.rank → ℤ) : e6Lat τ (n • β) = n • e6Lat τ β := by
  funext i
  by_cases h : i.val < Tag.E6.rank <;> simp [e6Lat, h]

end Lattice

section Index

variable {τ : Tag} [hτ : E6Sub τ]

@[expose] def e6Idx (k : Fin Tag.E6.rank) : Fin τ.rank := Fin.castLE hτ.rank_ge k

theorem e6Idx_injective : Function.Injective (e6Idx (τ := τ)) :=
  Fin.castLE_injective hτ.rank_ge

theorem e6Idx_val (k : Fin Tag.E6.rank) : (e6Idx (τ := τ) k).val = k.val := rfl

theorem e6Lat_apply_e6Idx (β : Fin Tag.E6.rank → ℤ) (k : Fin Tag.E6.rank) :
    e6Lat τ β (e6Idx k) = β k := by
  simp [e6Lat, e6Idx]

theorem exists_e6Idx_eq {i : Fin τ.rank} (h : i.val < Tag.E6.rank) : ∃ k, e6Idx (τ := τ) k = i :=
  ⟨⟨i.val, h⟩, Fin.ext rfl⟩

theorem e6Lat_single (k : Fin Tag.E6.rank) :
    e6Lat τ (Pi.single k 1) = Pi.single (e6Idx k) 1 := by
  funext i
  by_cases h : i.val < Tag.E6.rank
  · obtain ⟨l, rfl⟩ := exists_e6Idx_eq (τ := τ) h
    simp only [e6Lat_apply_e6Idx, Pi.single_apply, e6Idx_injective.eq_iff]
  · rw [e6Lat_apply_of_le (not_lt.1 h), Pi.single_apply, eq_comm, ite_eq_right_iff]
    intro hi
    exact absurd (by rw [hi]; exact k.2) h

theorem e6Lat_injective : Function.Injective (e6Lat τ) := by
  intro β γ h
  funext k
  rw [← e6Lat_apply_e6Idx (τ := τ) β k, ← e6Lat_apply_e6Idx (τ := τ) γ k, h]

theorem e6Lat_comp_e6Idx {γ : Fin τ.rank → ℤ}
    (h : ∀ i : Fin τ.rank, Tag.E6.rank ≤ i.val → γ i = 0) :
    e6Lat τ (fun k => γ (e6Idx k)) = γ := by
  funext i
  by_cases hi : i.val < Tag.E6.rank
  · obtain ⟨l, rfl⟩ := exists_e6Idx_eq (τ := τ) hi
    rw [e6Lat_apply_e6Idx]
  · rw [e6Lat_apply_of_le (not_lt.1 hi), h i (not_lt.1 hi)]

theorem cartan_e6Idx (k l : Fin Tag.E6.rank) :
    τ.cartan (e6Idx k) (e6Idx l) = Tag.E6.cartan k l :=
  hτ.cartan_eq k l

theorem sum_eq_sum_e6Idx (f : Fin τ.rank → ℤ)
    (hf : ∀ i : Fin τ.rank, Tag.E6.rank ≤ i.val → f i = 0) :
    ∑ j, f j = ∑ k : Fin Tag.E6.rank, f (e6Idx k) := by
  rw [← Finset.sum_image (f := f) (g := e6Idx (τ := τ)) (fun a _ b _ h => e6Idx_injective h)]
  refine (Finset.sum_subset (Finset.subset_univ _) fun j _ hj => hf j ?_).symm
  by_contra hlt
  exact hj (Finset.mem_image.2 ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem sum_cartan_e6Lat (k : Fin Tag.E6.rank) (β : Fin Tag.E6.rank → ℤ) :
    ∑ j, τ.cartan (e6Idx k) j * e6Lat τ β j = ∑ j, Tag.E6.cartan k j * β j := by
  rw [sum_eq_sum_e6Idx _ (fun i hi => by rw [e6Lat_apply_of_le hi, mul_zero])]
  exact Finset.sum_congr rfl fun l _ => by rw [cartan_e6Idx, e6Lat_apply_e6Idx]

theorem e6Lat_reflect (k : Fin Tag.E6.rank) (β : Fin Tag.E6.rank → ℤ) :
    e6Lat τ (reflect Tag.E6 k β) = reflect τ (e6Idx k) (e6Lat τ β) := by
  rw [reflect, reflect, e6Lat_sub, e6Lat_smul, e6Lat_single, sum_cartan_e6Lat]

theorem ofFn_e6Lat (β : Fin Tag.E6.rank → ℤ) :
    List.ofFn (e6Lat τ β) = List.ofFn β ++ List.replicate (τ.rank - Tag.E6.rank) 0 := by
  have hge := hτ.rank_ge
  refine List.ext_getElem (by simp; omega) fun n h1 h2 => ?_
  simp only [List.length_ofFn] at h1
  simp only [List.getElem_ofFn, List.getElem_append, List.length_ofFn, List.getElem_replicate]
  by_cases hn : n < Tag.E6.rank
  · simp [e6Lat, hn]
  · simp [e6Lat, hn]

theorem e6Lat_add_smul_single (β : Fin Tag.E6.rank → ℤ) (k : Fin Tag.E6.rank) (n : ℤ) :
    e6Lat τ (β + n • Pi.single k 1) = e6Lat τ β + n • Pi.single (e6Idx k) 1 := by
  rw [e6Lat_add, e6Lat_smul, e6Lat_single]

theorem e6Lat_sub_smul_single (β : Fin Tag.E6.rank → ℤ) (k : Fin Tag.E6.rank) (n : ℤ) :
    e6Lat τ (β - n • Pi.single k 1) = e6Lat τ β - n • Pi.single (e6Idx k) 1 := by
  rw [sub_eq_add_neg, ← neg_smul, e6Lat_add_smul_single, neg_smul, ← sub_eq_add_neg]

theorem e6Lat_eq_single_iff {α : Fin Tag.E6.rank → ℤ} {k : Fin Tag.E6.rank} :
    e6Lat τ α = Pi.single (e6Idx k) 1 ↔ α = Pi.single k 1 := by
  rw [← e6Lat_single]
  exact e6Lat_injective.eq_iff

theorem e6Lat_eq_neg_single_iff {α : Fin Tag.E6.rank → ℤ} {k : Fin Tag.E6.rank} :
    e6Lat τ α = -Pi.single (e6Idx k) 1 ↔ α = -Pi.single k 1 := by
  rw [← e6Lat_single, ← e6Lat_neg]
  exact e6Lat_injective.eq_iff

end Index

section Roots

variable {τ : Tag} [hτ : E6Sub τ]

theorem isRoot_e6Lat_iff {β : Fin Tag.E6.rank → ℤ} : IsRoot τ (e6Lat τ β) ↔ IsRoot Tag.E6 β := by
  rw [isRoot_iff_mem_artifactRoots, isRoot_iff_mem_artifactRoots, ofFn_e6Lat]
  refine ⟨fun h => ?_, hτ.roots_up _⟩
  have h' := hτ.roots_down _ h (by rw [List.drop_left' (by simp)])
  rwa [List.take_left' (by simp)] at h'

theorem stringUp_e6Lat (k : Fin Tag.E6.rank) (β : Fin Tag.E6.rank → ℤ) :
    stringUp τ (e6Idx k) (e6Lat τ β) = stringUp Tag.E6 k β := by
  simp only [stringUp, ← e6Lat_add_smul_single, isRoot_e6Lat_iff]

theorem stringDown_e6Lat (k : Fin Tag.E6.rank) (β : Fin Tag.E6.rank → ℤ) :
    stringDown τ (e6Idx k) (e6Lat τ β) = stringDown Tag.E6 k β := by
  simp only [stringDown, ← e6Lat_sub_smul_single, isRoot_e6Lat_iff]

@[expose] def e6Label : Label Tag.E6 → Label τ
  | .inl k => .inl (e6Idx k)
  | .inr β => .inr ⟨e6Lat τ β.1, isRoot_e6Lat_iff.2 β.2⟩

theorem e6Label_injective : Function.Injective (e6Label (τ := τ)) := by
  rintro (k | β) (l | γ) h
  · exact congrArg Sum.inl (e6Idx_injective (Sum.inl_injective h))
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg Sum.inr
      (Subtype.ext (e6Lat_injective (congrArg Subtype.val (Sum.inr_injective h))))

variable (τ) (K : Type) [Field K]

@[expose] def e6Emb : RootModule Tag.E6 K →ₗ[K] RootModule τ K :=
  Finsupp.lmapDomain K K (e6Label (τ := τ))

variable {τ} {K}

theorem e6Emb_single (b : Label Tag.E6) (c : K) :
    e6Emb τ K (Finsupp.single b c) = Finsupp.single (e6Label b) c :=
  Finsupp.mapDomain_single

theorem e6Emb_injective : Function.Injective (e6Emb τ K) :=
  Finsupp.mapDomain_injective e6Label_injective

theorem e6Emb_hVec (k : Fin Tag.E6.rank) :
    e6Emb τ K (hVec Tag.E6 K k) = hVec τ K (e6Idx k) :=
  e6Emb_single _ 1

theorem e6Emb_rootVec (β : Fin Tag.E6.rank → ℤ) :
    e6Emb τ K (rootVec Tag.E6 K β) = rootVec τ K (e6Lat τ β) := by
  by_cases hβ : IsRoot Tag.E6 β
  · rw [rootVec_eq_single_of_isRoot hβ, rootVec_eq_single_of_isRoot (isRoot_e6Lat_iff.2 hβ),
      e6Emb_single]
    rfl
  · rw [rootVec, dite_eq_right hβ, rootVec, dite_eq_right (mt isRoot_e6Lat_iff.1 hβ), map_zero]

theorem xOp_comp_e6Emb (k : Fin Tag.E6.rank) (c : K) :
    xOp τ K (e6Idx k) c ∘ₗ e6Emb τ K = e6Emb τ K ∘ₗ xOp Tag.E6 K k c := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, e6Emb_single, xOp,
    Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [e6Label]
    rw [map_add, map_smul, e6Emb_hVec, e6Emb_rootVec, e6Lat_single, cartan_e6Idx]
  · simp only [e6Label, e6Lat_eq_single_iff, e6Lat_eq_neg_single_iff]
    split_ifs with h1 h2
    · rw [e6Emb_single]
      rfl
    · rw [map_add, map_add, map_smul, map_smul, e6Emb_single, e6Emb_hVec, e6Emb_rootVec,
        e6Lat_single]
      rfl
    · rw [map_sum, stringUp_e6Lat, stringDown_e6Lat]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, e6Emb_rootVec, e6Lat_add_smul_single]

theorem yOp_comp_e6Emb (k : Fin Tag.E6.rank) (c : K) :
    yOp τ K (e6Idx k) c ∘ₗ e6Emb τ K = e6Emb τ K ∘ₗ yOp Tag.E6 K k c := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, e6Emb_single, yOp,
    Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [e6Label]
    rw [map_add, map_smul, e6Emb_hVec, e6Emb_rootVec, e6Lat_neg, e6Lat_single, cartan_e6Idx]
  · simp only [e6Label, e6Lat_eq_single_iff, e6Lat_eq_neg_single_iff]
    split_ifs with h1 h2
    · rw [e6Emb_single]
      rfl
    · rw [map_add, map_add, map_smul, map_smul, e6Emb_single, e6Emb_hVec, e6Emb_rootVec,
        e6Lat_neg, e6Lat_single]
      rfl
    · rw [map_sum, stringUp_e6Lat, stringDown_e6Lat]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, e6Emb_rootVec, e6Lat_sub_smul_single]

theorem e6Emb_comp_injective {f f' : Module.End K (RootModule Tag.E6 K)}
    (h : e6Emb τ K ∘ₗ f = e6Emb τ K ∘ₗ f') : f = f' :=
  LinearMap.ext fun v => e6Emb_injective (LinearMap.congr_fun h v)

theorem one_comp_e6Emb : ((1 : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
    e6Emb τ K ∘ₗ ((1 : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) := by
  rw [Units.val_one, Units.val_one, Module.End.one_eq_id, Module.End.one_eq_id,
    LinearMap.id_comp, LinearMap.comp_id]

theorem mul_comp_e6Emb {g h : ModGL τ K} {g' h' : ModGL Tag.E6 K}
    (hg : (g : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E6 K)))
    (hh : (h : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (h' : Module.End K (RootModule Tag.E6 K))) :
    ((g * h : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ ((g' * h' : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) := by
  rw [Units.val_mul, Units.val_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, hh, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]

theorem inv_comp_e6Emb {g : ModGL τ K} {g' : ModGL Tag.E6 K}
    (hg : (g : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E6 K))) :
    ((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ ((g'⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) := by
  have e : ∀ v, (g : Module.End K (RootModule τ K))
      (((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (e6Emb τ K v)) =
      (g : Module.End K (RootModule τ K)) (e6Emb τ K
        (((g'⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) v)) := by
    intro v
    have h1 := LinearMap.congr_fun hg (((g'⁻¹ : ModGL Tag.E6 K) : Module.End K _) v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [h1, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply]
  refine LinearMap.ext fun v => ?_
  have hinj : Function.Injective (g : Module.End K (RootModule τ K)) := fun x y hxy => by
    have := congrArg ((g⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) hxy
    rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply] at this
  exact hinj (e v)

variable (τ K) in
@[expose] def e6Preserving : Subgroup (ModGL τ K) where
  carrier := {g | ∃ g' : ModGL Tag.E6 K,
    (g : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E6 K))}
  mul_mem' := by
    rintro g h ⟨g', hg⟩ ⟨h', hh⟩
    exact ⟨g' * h', mul_comp_e6Emb hg hh⟩
  one_mem' := ⟨1, one_comp_e6Emb⟩
  inv_mem' := by
    rintro g ⟨g', hg⟩
    exact ⟨g'⁻¹, inv_comp_e6Emb hg⟩

theorem e6Preserving_partner_unique {g : ModGL τ K} {g' g'' : ModGL Tag.E6 K}
    (h' : (g : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E6 K)))
    (h'' : (g : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (g'' : Module.End K (RootModule Tag.E6 K))) : g' = g'' :=
  Units.ext (e6Emb_comp_injective (h'.symm.trans h''))

variable (τ K) in
@[expose] def e6PreservingRes : e6Preserving τ K →* ModGL Tag.E6 K where
  toFun g := g.2.choose
  map_one' := e6Preserving_partner_unique (1 : e6Preserving τ K).2.choose_spec one_comp_e6Emb
  map_mul' g h := e6Preserving_partner_unique (g * h).2.choose_spec
    (mul_comp_e6Emb g.2.choose_spec h.2.choose_spec)

theorem e6PreservingRes_spec (g : e6Preserving τ K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (e6PreservingRes τ K g : Module.End K (RootModule Tag.E6 K)) :=
  g.2.choose_spec

theorem e6PreservingRes_eq {g : e6Preserving τ K} {g' : ModGL Tag.E6 K}
    (h : ((g : ModGL τ K) : Module.End K (RootModule τ K)) ∘ₗ e6Emb τ K =
      e6Emb τ K ∘ₗ (g' : Module.End K (RootModule Tag.E6 K))) : e6PreservingRes τ K g = g' :=
  e6Preserving_partner_unique (e6PreservingRes_spec g) h

end Roots

section Units

variable {τ : Tag} [hτ : E6Sub τ]
  {K : Type} [Field K]

theorem xUnit_mem_e6Preserving (k : Fin Tag.E6.rank) (c : K) :
    xUnit τ K (e6Idx k) c ∈ e6Preserving τ K :=
  ⟨xUnit Tag.E6 K k c, xOp_comp_e6Emb k c⟩

theorem yUnit_mem_e6Preserving (k : Fin Tag.E6.rank) (c : K) :
    yUnit τ K (e6Idx k) c ∈ e6Preserving τ K :=
  ⟨yUnit Tag.E6 K k c, yOp_comp_e6Emb k c⟩

theorem subsystemGroup_le_e6Preserving {A : Set (Fin τ.rank)}
    (hA : ∀ i ∈ A, i.val < Tag.E6.rank) : subsystemGroup τ K A ≤ e6Preserving τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (hA i hi)
    exact xUnit_mem_e6Preserving k c
  · obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := τ) (hA i hi)
    exact yUnit_mem_e6Preserving k c

variable (K) in
@[expose] def e6Res {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank) :
    subsystemGroup τ K A →* ModGL Tag.E6 K :=
  (e6PreservingRes τ K).comp (Subgroup.inclusion (subsystemGroup_le_e6Preserving hA))

theorem e6Res_apply {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    (g : subsystemGroup τ K A) (v : RootModule Tag.E6 K) :
    ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e6Emb τ K v) =
      e6Emb τ K ((e6Res K hA g : Module.End K (RootModule Tag.E6 K)) v) :=
  LinearMap.congr_fun (e6PreservingRes_spec (Subgroup.inclusion
    (subsystemGroup_le_e6Preserving hA) g)) v

theorem e6Res_eq {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    {g : subsystemGroup τ K A} {g' : ModGL Tag.E6 K}
    (h : ∀ v, ((g : ModGL τ K) : Module.End K (RootModule τ K)) (e6Emb τ K v) =
      e6Emb τ K ((g' : Module.End K (RootModule Tag.E6 K)) v)) : e6Res K hA g = g' :=
  e6PreservingRes_eq (LinearMap.ext h)

theorem e6Res_xUnit {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    (k : Fin Tag.E6.rank) (hk : e6Idx (τ := τ) k ∈ A) (c : K) :
    e6Res K hA ⟨xUnit τ K (e6Idx k) c, xUnit_mem_subsystemGroup hk c⟩ = xUnit Tag.E6 K k c :=
  e6Res_eq hA fun v => LinearMap.congr_fun (xOp_comp_e6Emb k c) v

theorem e6Res_yUnit {A : Set (Fin τ.rank)} (hA : ∀ i ∈ A, i.val < Tag.E6.rank)
    (k : Fin Tag.E6.rank) (hk : e6Idx (τ := τ) k ∈ A) (c : K) :
    e6Res K hA ⟨yUnit τ K (e6Idx k) c, yUnit_mem_subsystemGroup hk c⟩ = yUnit Tag.E6 K k c :=
  e6Res_eq hA fun v => LinearMap.congr_fun (yOp_comp_e6Emb k c) v

end Units

end CFSG.RankThree.PartOne.KD4T
