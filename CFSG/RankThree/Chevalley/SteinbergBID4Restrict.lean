module

public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LieType.Chevalley.AllRootWeylConjugation
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange
public import CFSG.RankThree.Lattice.SteinbergBIListMatrix
public import CFSG.Blueprint.ChevalleyRootArtifact

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

@[expose] def d4Idx (k : Fin Tag.D4.rank) : Fin Tag.E6.rank :=
  ⟨k.val + 1, by have h := k.2; change k.val < 4 at h; change k.val + 1 < 6; omega⟩

@[expose] def d4Lat (β : Fin Tag.D4.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  (![0, β 0, β 1, β 2, β 3, 0] : Fin 6 → ℤ)

@[expose] def d4Support : Set (Fin Tag.E6.rank) := {i | i ≠ 0 ∧ i ≠ 5}

theorem d4Idx_injective : Function.Injective d4Idx := by
  intro k l h
  exact Fin.ext (by simpa [d4Idx] using congrArg Fin.val h)

theorem mem_d4Support {i : Fin Tag.E6.rank} : i ∈ d4Support ↔ i ≠ 0 ∧ i ≠ 5 := Iff.rfl

theorem d4Idx_mem (k : Fin Tag.D4.rank) : d4Idx k ∈ d4Support := by
  rw [mem_d4Support]
  revert k
  decide

theorem exists_d4Idx_eq {i : Fin Tag.E6.rank} (hi : i ∈ d4Support) : ∃ k, d4Idx k = i := by
  rw [mem_d4Support] at hi
  revert i
  decide

theorem d4Lat_apply_zero (β : Fin Tag.D4.rank → ℤ) : d4Lat β 0 = 0 := rfl

theorem d4Lat_apply_five (β : Fin Tag.D4.rank → ℤ) : d4Lat β 5 = 0 := rfl

theorem d4Lat_apply_d4Idx (β : Fin Tag.D4.rank → ℤ) (k : Fin Tag.D4.rank) :
    d4Lat β (d4Idx k) = β k := by
  fin_cases k <;> rfl

theorem d4Lat_add (β γ : Fin Tag.D4.rank → ℤ) : d4Lat (β + γ) = d4Lat β + d4Lat γ := by
  funext i
  fin_cases i <;> rfl

theorem d4Lat_neg (β : Fin Tag.D4.rank → ℤ) : d4Lat (-β) = -d4Lat β := by
  funext i
  fin_cases i <;> rfl

theorem d4Lat_smul (n : ℤ) (β : Fin Tag.D4.rank → ℤ) : d4Lat (n • β) = n • d4Lat β := by
  funext i
  fin_cases i <;> first | rfl | exact (mul_zero n).symm

theorem d4Lat_single (k : Fin Tag.D4.rank) :
    d4Lat (Pi.single k 1) = Pi.single (d4Idx k) 1 := by
  funext i
  fin_cases k <;> fin_cases i <;> rfl

theorem d4Lat_injective : Function.Injective d4Lat := by
  intro β γ h
  funext k
  rw [← d4Lat_apply_d4Idx β k, ← d4Lat_apply_d4Idx γ k, h]

theorem d4Lat_comp_d4Idx {γ : Fin Tag.E6.rank → ℤ} (h0 : γ 0 = 0) (h5 : γ 5 = 0) :
    d4Lat (fun k => γ (d4Idx k)) = γ := by
  funext i
  fin_cases i
  · exact h0.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · exact h5.symm

theorem cartan_d4Idx_sub : ∀ k l : Fin Tag.D4.rank,
    Tag.E6.cartan (d4Idx k) (d4Idx l) - Tag.D4.cartan k l = 0 := by
  decide

theorem cartan_d4Idx (k l : Fin Tag.D4.rank) :
    Tag.E6.cartan (d4Idx k) (d4Idx l) = Tag.D4.cartan k l :=
  sub_eq_zero.1 (cartan_d4Idx_sub k l)

theorem sum_cartan_d4Lat (k : Fin Tag.D4.rank) (β : Fin Tag.D4.rank → ℤ) :
    ∑ j, Tag.E6.cartan (d4Idx k) j * d4Lat β j = ∑ j, Tag.D4.cartan k j * β j := by
  have h6 : ∀ f : Fin Tag.E6.rank → ℤ, ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := fun f =>
    Fin.sum_univ_six f
  have h4 : ∀ f : Fin Tag.D4.rank → ℤ, ∑ j, f j = f 0 + f 1 + f 2 + f 3 := fun f =>
    Fin.sum_univ_four f
  rw [h6, h4]
  have e : ∀ (j : Fin Tag.E6.rank) (l : Fin Tag.D4.rank), j = d4Idx l →
      Tag.E6.cartan (d4Idx k) j * d4Lat β j = Tag.D4.cartan k l * β l := by
    rintro j l rfl
    rw [cartan_d4Idx, d4Lat_apply_d4Idx]
  rw [e 1 0 rfl, e 2 1 rfl, e 3 2 rfl, e 4 3 rfl, d4Lat_apply_zero, d4Lat_apply_five]
  ring

theorem d4Lat_sub (β γ : Fin Tag.D4.rank → ℤ) : d4Lat (β - γ) = d4Lat β - d4Lat γ := by
  rw [sub_eq_add_neg, d4Lat_add, d4Lat_neg, ← sub_eq_add_neg]

theorem d4Lat_reflect (k : Fin Tag.D4.rank) (β : Fin Tag.D4.rank → ℤ) :
    d4Lat (reflect Tag.D4 k β) = reflect Tag.E6 (d4Idx k) (d4Lat β) := by
  rw [reflect, reflect, d4Lat_sub, d4Lat_smul, d4Lat_single, sum_cartan_d4Lat]

theorem d4_roots_check : ∀ l ∈ Tag.D4.artifactRoots, (0 :: l ++ [0]) ∈ Tag.E6.artifactRoots := by
  decide +kernel

theorem e6_roots_d4_check : ∀ l ∈ Tag.E6.artifactRoots, l.head? = some 0 → l.getLast? = some 0 →
    (l.drop 1).take 4 ∈ Tag.D4.artifactRoots := by
  decide +kernel

theorem ofFn_d4Lat (β : Fin Tag.D4.rank → ℤ) :
    List.ofFn (d4Lat β) = 0 :: List.ofFn β ++ [0] := by
  rfl

theorem isRoot_d4Lat_iff {β : Fin Tag.D4.rank → ℤ} : IsRoot Tag.E6 (d4Lat β) ↔ IsRoot Tag.D4 β := by
  rw [isRoot_iff_mem_artifactRoots, isRoot_iff_mem_artifactRoots, ofFn_d4Lat]
  refine ⟨fun h => ?_, d4_roots_check _⟩
  have hl : (0 :: List.ofFn β ++ [0]).getLast? = some 0 := by
    rw [List.cons_append, ← List.cons_append, List.getLast?_concat]
  have h' := e6_roots_d4_check _ h rfl hl
  rwa [List.cons_append, List.drop_one, List.tail_cons,
    List.take_left' (by rw [List.length_ofFn]; rfl)] at h'

theorem mem_parabolicRoots_d4Support_iff {γ : Fin Tag.E6.rank → ℤ} :
    γ ∈ parabolicRoots Tag.E6 d4Support ↔ ∃ β, IsRoot Tag.D4 β ∧ d4Lat β = γ := by
  constructor
  · rintro ⟨hγ, hz⟩
    have h0 : γ 0 = 0 := hz 0 (by simp [d4Support])
    have h5 : γ 5 = 0 := hz 5 (by simp [d4Support])
    refine ⟨fun k => γ (d4Idx k), ?_, d4Lat_comp_d4Idx h0 h5⟩
    rw [← isRoot_d4Lat_iff, d4Lat_comp_d4Idx h0 h5]
    exact hγ
  · rintro ⟨β, hβ, rfl⟩
    refine ⟨isRoot_d4Lat_iff.2 hβ, fun i hi => ?_⟩
    rw [mem_d4Support, not_and_or, not_not, not_not] at hi
    rcases hi with rfl | rfl
    · rfl
    · rfl

theorem d4Lat_mem_parabolicRoots {β : Fin Tag.D4.rank → ℤ} (hβ : IsRoot Tag.D4 β) :
    d4Lat β ∈ parabolicRoots Tag.E6 d4Support :=
  mem_parabolicRoots_d4Support_iff.2 ⟨β, hβ, rfl⟩

theorem d4Lat_add_smul_single (β : Fin Tag.D4.rank → ℤ) (k : Fin Tag.D4.rank) (n : ℤ) :
    d4Lat (β + n • Pi.single k 1) = d4Lat β + n • Pi.single (d4Idx k) 1 := by
  rw [d4Lat_add, d4Lat_smul, d4Lat_single]

theorem d4Lat_sub_smul_single (β : Fin Tag.D4.rank → ℤ) (k : Fin Tag.D4.rank) (n : ℤ) :
    d4Lat (β - n • Pi.single k 1) = d4Lat β - n • Pi.single (d4Idx k) 1 := by
  rw [sub_eq_add_neg, ← neg_smul, d4Lat_add_smul_single, neg_smul, ← sub_eq_add_neg]

theorem stringUp_d4Lat (k : Fin Tag.D4.rank) (β : Fin Tag.D4.rank → ℤ) :
    stringUp Tag.E6 (d4Idx k) (d4Lat β) = stringUp Tag.D4 k β := by
  simp only [stringUp, ← d4Lat_add_smul_single, isRoot_d4Lat_iff]

theorem stringDown_d4Lat (k : Fin Tag.D4.rank) (β : Fin Tag.D4.rank → ℤ) :
    stringDown Tag.E6 (d4Idx k) (d4Lat β) = stringDown Tag.D4 k β := by
  simp only [stringDown, ← d4Lat_sub_smul_single, isRoot_d4Lat_iff]

theorem d4Lat_eq_single_iff {α : Fin Tag.D4.rank → ℤ} {k : Fin Tag.D4.rank} :
    d4Lat α = Pi.single (d4Idx k) 1 ↔ α = Pi.single k 1 := by
  rw [← d4Lat_single]
  exact d4Lat_injective.eq_iff

theorem d4Lat_eq_neg_single_iff {α : Fin Tag.D4.rank → ℤ} {k : Fin Tag.D4.rank} :
    d4Lat α = -Pi.single (d4Idx k) 1 ↔ α = -Pi.single k 1 := by
  rw [← d4Lat_single, ← d4Lat_neg]
  exact d4Lat_injective.eq_iff

@[expose] def d4Label : Label Tag.D4 → Label Tag.E6
  | .inl k => .inl (d4Idx k)
  | .inr β => .inr ⟨d4Lat β.1, isRoot_d4Lat_iff.2 β.2⟩

theorem d4Label_injective : Function.Injective d4Label := by
  rintro (k | β) (l | γ) h
  · exact congrArg Sum.inl (d4Idx_injective (Sum.inl_injective h))
  · exact absurd h Sum.inl_ne_inr
  · exact absurd h Sum.inr_ne_inl
  · exact congrArg Sum.inr
      (Subtype.ext (d4Lat_injective (congrArg Subtype.val (Sum.inr_injective h))))

variable (K : Type) [Field K]

@[expose] def d4Emb : RootModule Tag.D4 K →ₗ[K] RootModule Tag.E6 K :=
  Finsupp.lmapDomain K K d4Label

variable {K}

theorem d4Emb_single (b : Label Tag.D4) (c : K) :
    d4Emb K (Finsupp.single b c) = Finsupp.single (d4Label b) c :=
  Finsupp.mapDomain_single

theorem d4Emb_injective : Function.Injective (d4Emb K) :=
  Finsupp.mapDomain_injective d4Label_injective

theorem d4Emb_hVec (k : Fin Tag.D4.rank) :
    d4Emb K (hVec Tag.D4 K k) = hVec Tag.E6 K (d4Idx k) :=
  d4Emb_single _ 1

theorem d4Emb_rootVec (β : Fin Tag.D4.rank → ℤ) :
    d4Emb K (rootVec Tag.D4 K β) = rootVec Tag.E6 K (d4Lat β) := by
  by_cases hβ : IsRoot Tag.D4 β
  · rw [rootVec_eq_single_of_isRoot hβ, rootVec_eq_single_of_isRoot (isRoot_d4Lat_iff.2 hβ),
      d4Emb_single]
    rfl
  · rw [rootVec, dite_eq_right hβ, rootVec, dite_eq_right (mt isRoot_d4Lat_iff.1 hβ), map_zero]

theorem xOp_comp_d4Emb (k : Fin Tag.D4.rank) (c : K) :
    xOp Tag.E6 K (d4Idx k) c ∘ₗ d4Emb K = d4Emb K ∘ₗ xOp Tag.D4 K k c := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, d4Emb_single, xOp,
    Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [d4Label]
    rw [map_add, map_smul, d4Emb_hVec, d4Emb_rootVec, d4Lat_single, cartan_d4Idx]
  · simp only [d4Label, d4Lat_eq_single_iff, d4Lat_eq_neg_single_iff]
    split_ifs with h1 h2
    · rw [d4Emb_single]
      rfl
    · rw [map_add, map_add, map_smul, map_smul, d4Emb_single, d4Emb_hVec, d4Emb_rootVec,
        d4Lat_single]
      rfl
    · rw [map_sum, stringUp_d4Lat, stringDown_d4Lat]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, d4Emb_rootVec, d4Lat_add_smul_single]

theorem yOp_comp_d4Emb (k : Fin Tag.D4.rank) (c : K) :
    yOp Tag.E6 K (d4Idx k) c ∘ₗ d4Emb K = d4Emb K ∘ₗ yOp Tag.D4 K k c := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, d4Emb_single, yOp,
    Finsupp.linearCombination_single, one_smul]
  rcases b with j | ⟨α, hα⟩
  · simp only [d4Label]
    rw [map_add, map_smul, d4Emb_hVec, d4Emb_rootVec, d4Lat_neg, d4Lat_single, cartan_d4Idx]
  · simp only [d4Label, d4Lat_eq_single_iff, d4Lat_eq_neg_single_iff]
    split_ifs with h1 h2
    · rw [d4Emb_single]
      rfl
    · rw [map_add, map_add, map_smul, map_smul, d4Emb_single, d4Emb_hVec, d4Emb_rootVec,
        d4Lat_neg, d4Lat_single]
      rfl
    · rw [map_sum, stringUp_d4Lat, stringDown_d4Lat]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_smul, d4Emb_rootVec, d4Lat_sub_smul_single]

theorem d4Emb_comp_injective {f f' : Module.End K (RootModule Tag.D4 K)}
    (h : d4Emb K ∘ₗ f = d4Emb K ∘ₗ f') : f = f' :=
  LinearMap.ext fun v => d4Emb_injective (LinearMap.congr_fun h v)

theorem one_comp_d4Emb : ((1 : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) ∘ₗ
    d4Emb K = d4Emb K ∘ₗ ((1 : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) := by
  rw [Units.val_one, Units.val_one, Module.End.one_eq_id, Module.End.one_eq_id,
    LinearMap.id_comp, LinearMap.comp_id]

theorem mul_comp_d4Emb {g h : ModGL Tag.E6 K} {g' h' : ModGL Tag.D4 K}
    (hg : (g : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (g' : Module.End K (RootModule Tag.D4 K)))
    (hh : (h : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (h' : Module.End K (RootModule Tag.D4 K))) :
    ((g * h : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ ((g' * h' : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) := by
  rw [Units.val_mul, Units.val_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    LinearMap.comp_assoc, hh, ← LinearMap.comp_assoc, hg, LinearMap.comp_assoc]

theorem inv_comp_d4Emb {g : ModGL Tag.E6 K} {g' : ModGL Tag.D4 K}
    (hg : (g : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (g' : Module.End K (RootModule Tag.D4 K))) :
    ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ ((g'⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) := by
  have e : ∀ v, (g : Module.End K (RootModule Tag.E6 K))
      (((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Emb K v)) =
      (g : Module.End K (RootModule Tag.E6 K)) (d4Emb K
        (((g'⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) v)) := by
    intro v
    have h1 := LinearMap.congr_fun hg (((g'⁻¹ : ModGL Tag.D4 K) : Module.End K _) v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
    rw [h1, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Module.End.one_apply]
  refine LinearMap.ext fun v => ?_
  have hinj : Function.Injective (g : Module.End K (RootModule Tag.E6 K)) := fun x y hxy => by
    have := congrArg ((g⁻¹ : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) hxy
    rwa [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Module.End.one_apply] at this
  exact hinj (e v)

variable (K) in
@[expose] def d4Preserving : Subgroup (ModGL Tag.E6 K) where
  carrier := {g | ∃ g' : ModGL Tag.D4 K,
    (g : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (g' : Module.End K (RootModule Tag.D4 K))}
  mul_mem' := by
    rintro g h ⟨g', hg⟩ ⟨h', hh⟩
    exact ⟨g' * h', mul_comp_d4Emb hg hh⟩
  one_mem' := ⟨1, one_comp_d4Emb⟩
  inv_mem' := by
    rintro g ⟨g', hg⟩
    exact ⟨g'⁻¹, inv_comp_d4Emb hg⟩

theorem d4Preserving_partner_unique {g : ModGL Tag.E6 K} {g' g'' : ModGL Tag.D4 K}
    (h' : (g : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (g' : Module.End K (RootModule Tag.D4 K)))
    (h'' : (g : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (g'' : Module.End K (RootModule Tag.D4 K))) : g' = g'' :=
  Units.ext (d4Emb_comp_injective (h'.symm.trans h''))

variable (K) in
@[expose] def d4PreservingRes : d4Preserving K →* ModGL Tag.D4 K where
  toFun g := g.2.choose
  map_one' := d4Preserving_partner_unique (1 : d4Preserving K).2.choose_spec one_comp_d4Emb
  map_mul' g h := d4Preserving_partner_unique (g * h).2.choose_spec
    (mul_comp_d4Emb g.2.choose_spec h.2.choose_spec)

theorem d4PreservingRes_spec (g : d4Preserving K) :
    ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (d4PreservingRes K g : Module.End K (RootModule Tag.D4 K)) :=
  g.2.choose_spec

theorem d4PreservingRes_eq {g : d4Preserving K} {g' : ModGL Tag.D4 K}
    (h : ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (g' : Module.End K (RootModule Tag.D4 K))) : d4PreservingRes K g = g' :=
  d4Preserving_partner_unique (d4PreservingRes_spec g) h

theorem xUnit_mem_d4Preserving (k : Fin Tag.D4.rank) (c : K) :
    xUnit Tag.E6 K (d4Idx k) c ∈ d4Preserving K :=
  ⟨xUnit Tag.D4 K k c, xOp_comp_d4Emb k c⟩

theorem yUnit_mem_d4Preserving (k : Fin Tag.D4.rank) (c : K) :
    yUnit Tag.E6 K (d4Idx k) c ∈ d4Preserving K :=
  ⟨yUnit Tag.D4 K k c, yOp_comp_d4Emb k c⟩

theorem subsystemGroup_le_d4Preserving : subsystemGroup Tag.E6 K d4Support ≤ d4Preserving K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
    exact xUnit_mem_d4Preserving k c
  · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
    exact yUnit_mem_d4Preserving k c

variable (K) in
@[expose] def d4Res : subsystemGroup Tag.E6 K d4Support →* ModGL Tag.D4 K :=
  (d4PreservingRes K).comp (Subgroup.inclusion subsystemGroup_le_d4Preserving)

theorem d4Res_apply (g : subsystemGroup Tag.E6 K d4Support) (v : RootModule Tag.D4 K) :
    ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Emb K v) =
      d4Emb K ((d4Res K g : Module.End K (RootModule Tag.D4 K)) v) :=
  LinearMap.congr_fun (d4PreservingRes_spec (Subgroup.inclusion subsystemGroup_le_d4Preserving g))
    v

theorem d4Res_eq {g : subsystemGroup Tag.E6 K d4Support} {g' : ModGL Tag.D4 K}
    (h : ∀ v, ((g : ModGL Tag.E6 K) : Module.End K (RootModule Tag.E6 K)) (d4Emb K v) =
      d4Emb K ((g' : Module.End K (RootModule Tag.D4 K)) v)) : d4Res K g = g' :=
  d4PreservingRes_eq (LinearMap.ext h)

theorem d4Res_xUnit (k : Fin Tag.D4.rank) (c : K) :
    d4Res K ⟨xUnit Tag.E6 K (d4Idx k) c, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      xUnit Tag.D4 K k c :=
  d4Res_eq fun v => LinearMap.congr_fun (xOp_comp_d4Emb k c) v

theorem d4Res_yUnit (k : Fin Tag.D4.rank) (c : K) :
    d4Res K ⟨yUnit Tag.E6 K (d4Idx k) c, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ =
      yUnit Tag.D4 K k c :=
  d4Res_eq fun v => LinearMap.congr_fun (yOp_comp_d4Emb k c) v

theorem weylElt_comp_d4Emb (k : Fin Tag.D4.rank) (t : Kˣ) :
    (weylElt Tag.E6 K (d4Idx k) t : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (weylElt Tag.D4 K k t : Module.End K (RootModule Tag.D4 K)) := by
  rw [LieType.Chevalley.weylElt_eq_xUnit_mul, LieType.Chevalley.weylElt_eq_xUnit_mul]
  exact mul_comp_d4Emb (mul_comp_d4Emb (xOp_comp_d4Emb k _) (yOp_comp_d4Emb k _))
    (xOp_comp_d4Emb k _)

theorem torusElt_comp_d4Emb (k : Fin Tag.D4.rank) (t : Kˣ) :
    (torusElt Tag.E6 K (d4Idx k) t : Module.End K (RootModule Tag.E6 K)) ∘ₗ d4Emb K =
      d4Emb K ∘ₗ (torusElt Tag.D4 K k t : Module.End K (RootModule Tag.D4 K)) :=
  mul_comp_d4Emb (weylElt_comp_d4Emb k t) (weylElt_comp_d4Emb k (-1))

theorem d4Res_weylElt (k : Fin Tag.D4.rank) (t : Kˣ) :
    d4Res K ⟨weylElt Tag.E6 K (d4Idx k) t, weylElt_mem_subsystemGroup (d4Idx_mem k) t⟩ =
      weylElt Tag.D4 K k t :=
  d4Res_eq fun v => LinearMap.congr_fun (weylElt_comp_d4Emb k t) v

theorem torusElt_mem_d4Q (k : Fin Tag.D4.rank) (t : Kˣ) :
    torusElt Tag.E6 K (d4Idx k) t ∈ subsystemGroup Tag.E6 K d4Support :=
  subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus (d4Idx_mem k) t)

theorem d4Res_torusElt (k : Fin Tag.D4.rank) (t : Kˣ) :
    d4Res K ⟨torusElt Tag.E6 K (d4Idx k) t, torusElt_mem_d4Q k t⟩ = torusElt Tag.D4 K k t :=
  d4Res_eq fun v => LinearMap.congr_fun (torusElt_comp_d4Emb k t) v

theorem closure_d4Q_generators : Subgroup.closure
    (((↑) : subsystemGroup Tag.E6 K d4Support → ModGL Tag.E6 K) ⁻¹'
      {g | ∃ i ∈ d4Support, ∃ c : K, g = xUnit Tag.E6 K i c ∨ g = yUnit Tag.E6 K i c}) = ⊤ :=
  Subgroup.closure_closure_coe_preimage

theorem range_d4Res : (d4Res K).range = adjointGroup Tag.D4 K := by
  rw [MonoidHom.range_eq_map, ← closure_d4Q_generators, MonoidHom.map_closure, adjointGroup]
  congr 1
  ext g
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨i, hi, c, h | h⟩, rfl⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      subst h
      exact ⟨k, c, Or.inl (by rw [d4Res_xUnit]; rfl)⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      subst h
      exact ⟨k, c, Or.inr (by rw [d4Res_yUnit]; rfl)⟩
  · rintro ⟨k, c, h | h⟩
    · refine ⟨⟨xUnit Tag.E6 K (d4Idx k) c, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩,
        ⟨d4Idx k, d4Idx_mem k, c, Or.inl rfl⟩, ?_⟩
      rw [d4Res_xUnit]
      exact Units.ext h.symm
    · refine ⟨⟨yUnit Tag.E6 K (d4Idx k) c, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩,
        ⟨d4Idx k, d4Idx_mem k, c, Or.inr rfl⟩, ?_⟩
      rw [d4Res_yUnit]
      exact Units.ext h.symm

theorem d4Res_mem_adjointGroup (g : subsystemGroup Tag.E6 K d4Support) :
    d4Res K g ∈ adjointGroup Tag.D4 K := by
  rw [← range_d4Res]
  exact ⟨g, rfl⟩

theorem exists_sign_pinnedX_comp_d4Emb {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      (pinnedX Tag.E6 L (d4Lat α) c : Module.End L (RootModule Tag.E6 L)) ∘ₗ d4Emb L =
        d4Emb L ∘ₗ (pinnedX Tag.D4 L α ((ε : L) * c) : Module.End L (RootModule Tag.D4 L)) := by
  induction hα with
  | basis j =>
    refine ⟨1, Or.inl rfl, fun L _ c => ?_⟩
    rw [d4Lat_single, pinnedX_single, pinnedX_single, Int.cast_one, one_mul]
    exact xOp_comp_d4Emb j c
  | @reflect i v hv ih =>
    obtain ⟨ε, hε, h⟩ := ih
    have hv6 : IsRoot Tag.E6 (d4Lat v) := isRoot_d4Lat_iff.2 hv
    have h6 := (all_root_weyl_infinitesimal.{0} Tag.E6).2.2.2.1 (d4Idx i) _ hv6
    have h4 := (all_root_weyl_infinitesimal.{0} Tag.D4).2.2.2.1 i _ hv
    refine ⟨allRootWeylSign Tag.D4 i v * ε * allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v), ?_,
      fun L _ c => ?_⟩
    · rcases h4 with h4 | h4 <;> rcases hε with hε | hε <;> rcases h6 with h6 | h6 <;>
        simp [h4, hε, h6]
    have hσ6 : ((allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v) : L) *
        allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v)) = 1 := by
      rcases h6 with h6 | h6 <;> simp [h6]
    have e6 := weylElt_one_mul_pinnedX_mul_inv L (d4Idx i) hv6
      ((allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v) : L) * c)
    rw [← mul_assoc, hσ6, one_mul, ← d4Lat_reflect] at e6
    have e4 := weylElt_one_mul_pinnedX_mul_inv L i hv
      ((ε : L) * ((allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v) : L) * c))
    have hc : ((allRootWeylSign Tag.D4 i v * ε * allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v) :
        ℤ) : L) * c = (allRootWeylSign Tag.D4 i v : L) *
          ((ε : L) * ((allRootWeylSign Tag.E6 (d4Idx i) (d4Lat v) : L) * c)) := by
      push_cast
      ring
    rw [← e6, hc, ← e4]
    exact mul_comp_d4Emb (mul_comp_d4Emb (weylElt_comp_d4Emb i 1) (h L _))
      (inv_comp_d4Emb (weylElt_comp_d4Emb i 1))

theorem pinnedX_mem_d4Q {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) (c : K) :
    pinnedX Tag.E6 K (d4Lat α) c ∈ subsystemGroup Tag.E6 K d4Support :=
  rootSubgroup_le_subsystemGroup (d4Lat_mem_parabolicRoots hα) (Subgroup.subset_closure ⟨c, rfl⟩)

theorem exists_sign_d4Res_pinnedX {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (L : Type) [Field L] (c : L),
      d4Res L ⟨pinnedX Tag.E6 L (d4Lat α) c, pinnedX_mem_d4Q hα c⟩ =
        pinnedX Tag.D4 L α ((ε : L) * c) := by
  obtain ⟨ε, hε, h⟩ := exists_sign_pinnedX_comp_d4Emb hα
  exact ⟨ε, hε, fun L _ c => d4Res_eq fun v => LinearMap.congr_fun (h L c) v⟩

theorem map_d4Res_rootSubgroup {α : Fin Tag.D4.rank → ℤ} (hα : IsRoot Tag.D4 α) :
    ((rootSubgroup Tag.E6 K (d4Lat α)).subgroupOf (subsystemGroup Tag.E6 K d4Support)).map
      (d4Res K) = rootSubgroup Tag.D4 K α := by
  obtain ⟨ε, hε, h⟩ := exists_sign_d4Res_pinnedX hα
  have hεε : (ε : K) * ε = 1 := by rcases hε with hε | hε <;> simp [hε]
  ext g
  rw [Subgroup.mem_map, mem_rootSubgroup]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf, mem_rootSubgroup] at hx
    obtain ⟨c, hc⟩ := hx
    have e : x = ⟨pinnedX Tag.E6 K (d4Lat α) c, pinnedX_mem_d4Q hα c⟩ := Subtype.ext hc.symm
    exact ⟨(ε : K) * c, by rw [e, h K c]⟩
  · rintro ⟨c, rfl⟩
    refine ⟨⟨pinnedX Tag.E6 K (d4Lat α) ((ε : K) * c), pinnedX_mem_d4Q hα _⟩,
      (Subgroup.mem_subgroupOf).2 (mem_rootSubgroup.2 ⟨_, rfl⟩), ?_⟩
    rw [h K, ← mul_assoc, hεε, one_mul]

theorem baseChangeGL_mem_d4Q {L : Type} [Field L] (σ : K →+* L) {g : ModGL Tag.E6 K}
    (hg : g ∈ subsystemGroup Tag.E6 K d4Support) :
    baseChangeGL σ g ∈ subsystemGroup Tag.E6 L d4Support := by
  refine (Subgroup.closure_le (K := (subsystemGroup Tag.E6 L d4Support).comap (baseChangeGL σ))
    |>.2 ?_) hg
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_xUnit]
    exact xUnit_mem_subsystemGroup hi _
  · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_yUnit]
    exact yUnit_mem_subsystemGroup hi _

variable (K) in
@[expose] def d4QBaseChange {L : Type} [Field L] (σ : K →+* L) :
    subsystemGroup Tag.E6 K d4Support →* subsystemGroup Tag.E6 L d4Support :=
  ((baseChangeGL σ).comp (subsystemGroup Tag.E6 K d4Support).subtype).codRestrict _
    fun g => baseChangeGL_mem_d4Q σ g.2

theorem d4Res_baseChangeGL {L : Type} [Field L] (σ : K →+* L)
    (g : subsystemGroup Tag.E6 K d4Support) :
    d4Res L (d4QBaseChange K σ g) = baseChangeGL σ (d4Res K g) := by
  have h : (d4Res L).comp (d4QBaseChange K σ) = (baseChangeGL σ).comp (d4Res K) := by
    refine MonoidHom.eq_of_eqOn_dense closure_d4Q_generators ?_
    rintro ⟨x, hx⟩ ⟨i, hi, c, h | h⟩
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      have e : (⟨x, hx⟩ : subsystemGroup Tag.E6 K d4Support) =
          ⟨xUnit Tag.E6 K (d4Idx k) c, xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ := Subtype.ext h
      have e' : d4QBaseChange K σ ⟨xUnit Tag.E6 K (d4Idx k) c,
          xUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ = ⟨xUnit Tag.E6 L (d4Idx k) (σ c),
            xUnit_mem_subsystemGroup (d4Idx_mem k) (σ c)⟩ := Subtype.ext (baseChangeGL_xUnit σ _ _)
      rw [e, MonoidHom.comp_apply, MonoidHom.comp_apply, e', d4Res_xUnit, d4Res_xUnit,
        baseChangeGL_xUnit]
    · obtain ⟨k, rfl⟩ := exists_d4Idx_eq hi
      have e : (⟨x, hx⟩ : subsystemGroup Tag.E6 K d4Support) =
          ⟨yUnit Tag.E6 K (d4Idx k) c, yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ := Subtype.ext h
      have e' : d4QBaseChange K σ ⟨yUnit Tag.E6 K (d4Idx k) c,
          yUnit_mem_subsystemGroup (d4Idx_mem k) c⟩ = ⟨yUnit Tag.E6 L (d4Idx k) (σ c),
            yUnit_mem_subsystemGroup (d4Idx_mem k) (σ c)⟩ := Subtype.ext (baseChangeGL_yUnit σ _ _)
      rw [e, MonoidHom.comp_apply, MonoidHom.comp_apply, e', d4Res_yUnit, d4Res_yUnit,
        baseChangeGL_yUnit]
  exact DFunLike.congr_fun h g

end CFSG.RankThree.Chevalley
