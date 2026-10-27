module

public import CFSG.Timmesfeld.RankTwo.ModelG2Comm
public import CFSG.Timmesfeld.RankTwo.Positive
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.Timmesfeld.GradedPresentation CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWalk

section Generic

variable {ι : Type*} {F : ι → Type*} {n : Type*} {K' : Type*} [Group K']
  {X : (n → ℤ) → Subgroup K'}

theorem injective_prod_of_prodInjectiveFor (r : ι → n → ℤ) (hr : Function.Injective r)
    (x : ∀ i, F i → K') (hx : ∀ i c, x i c ∈ X (r i)) (hxinj : ∀ i, Function.Injective (x i))
    (L : List ι) (hL : ∀ i, i ∈ L) (hP : ProdInjectiveFor X (L.map r)) :
    Function.Injective fun c : (∀ i, F i) => (L.map fun i => x i (c i)).prod := by
  classical
  intro c c' hcc'
  let f : (∀ i, F i) → (n → ℤ) → K' := fun c γ =>
    if h : ∃ i, r i = γ then x h.choose (c h.choose) else 1
  have hf : ∀ c i, f c (r i) = x i (c i) := fun c i => by
    have h : ∃ j, r j = r i := ⟨i, rfl⟩
    simp only [f, dite_eq_left h]
    exact congrArg (fun j => x j (c j)) (hr h.choose_spec)
  have hmap : ∀ c, ((L.map r).map (f c)).prod = (L.map fun i => x i (c i)).prod := fun c => by
    rw [List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => hf c i)
  have hmem : ∀ c, ∀ γ ∈ L.map r, f c γ ∈ X γ := fun c γ hγ => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hγ
    rw [hf]
    exact hx i (c i)
  have key := hP (f c) (f c') (hmem c) (hmem c') (by rw [hmap, hmap]; exact hcc')
  funext i
  have := key (r i) (List.mem_map.2 ⟨i, hL i, rfl⟩)
  rw [hf, hf] at this
  exact hxinj i this

variable [Fintype ι] [DecidableEq ι] [∀ i, AddGroup (F i)] [∀ i, Fintype (F i)]
  {cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)} {ht : ι → ℕ}

theorem extendsToHom_of_rels (hgr : ∀ α s β t, cm α s β t ∈ above ht (max (ht α) (ht β)))
    (r : ι → n → ℤ) (x : ∀ i, F i → K') (hx : ∀ i c, x i c ∈ X (r i))
    (hrel : ∀ w ∈ rels cm, FreeGroup.lift (fun g : Σ γ, F γ => x g.1 g.2) w = 1)
    (L : List ι) (hinj : Function.Injective fun c : (∀ i, F i) => (L.map fun i => x i (c i)).prod)
    {Ψ : Set (n → ℤ)} (hΨ : ∀ γ ∈ Ψ, ∃ i, r i = γ) (hsurj : ∀ i, ∀ y ∈ X (r i), ∃ c, x i c = y)
    {G : Type*} [Group G] {φ : ∀ γ, X γ → G} (ψ : (Σ i, F i) → G)
    (hψ : ∀ w ∈ rels cm, FreeGroup.lift ψ w = 1)
    (hφ : ∀ i c, φ (r i) ⟨x i c, hx i c⟩ = ψ ⟨i, c⟩) :
    ExtendsToHom X Ψ φ := by
  obtain ⟨θ, hθ⟩ := exists_hom hgr (fun g : Σ γ, F γ => x g.1 g.2) ψ hrel hψ L hinj
  refine ⟨Subgroup.closure (Set.range fun g : Σ γ, F γ => x g.1 g.2), θ, fun γ hγ y => ?_⟩
  obtain ⟨i, rfl⟩ := hΨ γ hγ
  obtain ⟨y, hy⟩ := y
  obtain ⟨c, rfl⟩ := hsurj i y hy
  exact ⟨Subgroup.subset_closure ⟨⟨i, c⟩, rfl⟩, (hθ ⟨i, c⟩).trans (hφ i c).symm⟩

end Generic

section G2

variable {K : Type} [Field K]

set_option quotPrecheck false in
local notation "Φ" => RootSystem.ofCartan (g2Datum K).isFiniteType (g2Datum K).divisible

set_option quotPrecheck false in
local notation "𝕏" => (g2Datum K).rootGroup

set_option quotPrecheck false in
local notation "𝕩" => xPar (rootOperatorFamily Tag.G2)

theorem isRoot_hexRoot (i : Fin 6) : IsRoot .G2 (hexRoot i) := by
  rw [hexRoot_eq_g2]
  exact isRoot_rootCertificate_root (by fin_cases i <;> decide)

theorem hexRoot_injective : Function.Injective hexRoot := by
  decide

theorem mem_g2_roots {γ : Fin (Tag.rank .G2) → ℤ} : γ ∈ (Φ).roots ↔ IsRoot .G2 γ := by
  change γ ∈ CFSG.LieType.RootSystem.roots _ _ ↔ _
  rw [roots_eq_setOf_isRoot]
  rfl

theorem exists_hexRoot_eq {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (hpos : 0 < ht γ) :
    ∃ i, hexRoot i = γ := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
  have hk' : k < 12 := hk
  interval_cases k
  · exact ⟨5, hexRoot_eq_g2 5⟩
  · exact ⟨0, hexRoot_eq_g2 0⟩
  · exact absurd hpos (by decide)
  · exact ⟨1, hexRoot_eq_g2 1⟩
  · exact ⟨4, hexRoot_eq_g2 4⟩
  · exact absurd hpos (by decide)
  · exact absurd hpos (by decide)
  · exact ⟨3, hexRoot_eq_g2 3⟩
  · exact ⟨2, hexRoot_eq_g2 2⟩
  · exact absurd hpos (by decide)
  · exact absurd hpos (by decide)
  · exact absurd hpos (by decide)

theorem g2X_prod_injective :
    Function.Injective fun c : Fin 6 → K =>
      ([0, 5, 4, 2, 1, 3].map fun i => g2X i (c i)).prod := by
  refine injective_prod_of_prodInjectiveFor (F := fun _ => K) (X := 𝕏) hexRoot hexRoot_injective
    (fun i c => g2X i c) (fun i c => xPar_mem (isRoot_hexRoot i) c)
    (fun i => xPar_injective (isRoot_hexRoot i)) _ (by decide) ?_
  refine prodInjective (F := rootOperatorFamily Tag.G2) (K := K) htHom
    (([0, 5, 4, 2, 1, 3] : List (Fin 6)).map hexRoot) (by decide) (fun γ hγ => ?_) (by decide)
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hγ
  exact ⟨isRoot_hexRoot i, by fin_cases i <;> decide⟩

open Classical in
@[expose] noncomputable def g2PhiOf {G : Type*} [Group G]
    (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G) : ∀ γ, 𝕏 γ → G :=
  fun γ y => if h : IsRoot .G2 γ then ψ γ ((mem_rootGroup_iff h y).1 y.2).choose else 1

theorem g2PhiOf_xPar {G : Type*} [Group G] (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G)
    {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ) (c : K) :
    g2PhiOf ψ γ ⟨𝕩 γ c, xPar_mem hγ c⟩ = ψ γ c := by
  classical
  rw [g2PhiOf, dite_eq_left hγ]
  exact congrArg (ψ γ) (xPar_injective hγ ((mem_rootGroup_iff hγ _).1 (xPar_mem hγ c)).choose_spec)

variable [CharP K 2] [Finite K]

theorem g2_extendsToHom_pos {G : Type*} [Group G] {φ : ∀ γ, 𝕏 γ → G}
    (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G)
    (hψ : ∀ w ∈ rels (g2Cm (K := K)),
      FreeGroup.lift (fun g : Σ _ : Fin 6, K => ψ (hexRoot g.1) g.2) w = 1)
    (hφ : ∀ γ (hγ : IsRoot .G2 γ) c, φ γ ⟨𝕩 γ c, xPar_mem hγ c⟩ = ψ γ c) :
    ExtendsToHom 𝕏 (Φ).pos φ := by
  have := Fintype.ofFinite K
  exact extendsToHom_of_rels (F := fun _ => K) (fun i s j t => g2Cm_mem_above i s j t) hexRoot
    (fun i c => g2X i c) (fun i c => xPar_mem (isRoot_hexRoot i) c) g2X_rels _ g2X_prod_injective
    (fun γ hγ => exists_hexRoot_eq (mem_g2_roots.1 hγ.1) hγ.2)
    (fun i y hy => (mem_rootGroup_iff (isRoot_hexRoot i) y).1 hy) _ hψ
    (fun i c => hφ _ (isRoot_hexRoot i) c)

omit [Finite K] in
theorem g2_weylElement_conj_xPar (i : Fin (Tag.rank .G2)) {γ : Fin (Tag.rank .G2) → ℤ}
    (hγ : IsRoot .G2 γ) (c : K) :
    CFSG.LieType.Chevalley.weylElement .G2 K i * 𝕩 γ c *
        (CFSG.LieType.Chevalley.weylElement .G2 K i)⁻¹ = 𝕩 ((Φ).refl i γ) c := by
  obtain ⟨ε, hε, h⟩ := weylElement_xPar_conj (F := rootOperatorFamily .G2) (K := K) i hγ
  have h1 := h 1 c
  rw [weylElement_xPar, torusElement_one_eq, one_mul] at h1
  rw [h1, RootSystem.ofCartan_refl_apply]
  congr 1
  have hε1 : (ε : K) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  simp [hε1]

omit [Finite K] in
theorem g2_conj_mem_refl :
    ∀ i, ∀ γ ∈ (Φ).roots, ∀ x ∈ 𝕏 γ, CFSG.LieType.Chevalley.weylElement .G2 K i * x *
      (CFSG.LieType.Chevalley.weylElement .G2 K i)⁻¹ ∈ 𝕏 ((Φ).refl i γ) := by
  intro i γ hγ x hx
  have hγ' := mem_g2_roots.1 hγ
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
  rw [g2_weylElement_conj_xPar i hγ' c]
  exact xPar_mem (mem_g2_roots.1 ((Φ).refl_mem i γ hγ)) c

omit [Finite K] in
theorem g2_conj_map_refl {G : Type*} [Group G] (ñ : Fin (Tag.rank .G2) → G) {φ : ∀ γ, 𝕏 γ → G}
    (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G)
    (hφ : ∀ γ (hγ : IsRoot .G2 γ) c, φ γ ⟨𝕩 γ c, xPar_mem hγ c⟩ = ψ γ c)
    (hW : ∀ i γ, IsRoot .G2 γ → ∀ c, ñ i * ψ γ c * (ñ i)⁻¹ = ψ ((Φ).refl i γ) c) :
    ∀ i, ∀ γ ∈ (Φ).roots, ∀ (x : 𝕏 γ) (y : 𝕏 ((Φ).refl i γ)),
      (y : adjointGroup .G2 K) = CFSG.LieType.Chevalley.weylElement .G2 K i * x *
        (CFSG.LieType.Chevalley.weylElement .G2 K i)⁻¹ →
      ñ i * φ γ x * (ñ i)⁻¹ = φ ((Φ).refl i γ) y := by
  intro i γ hγ x y hy
  have hγ' := mem_g2_roots.1 hγ
  have hs := mem_g2_roots.1 ((Φ).refl_mem i γ hγ)
  obtain ⟨x, hx⟩ := x
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
  obtain ⟨y, hy'⟩ := y
  simp only at hy
  rw [g2_weylElement_conj_xPar i hγ' c] at hy
  subst hy
  rw [hφ γ hγ' c, hφ _ hs c, hW i γ hγ' c]

theorem g2_coneCompatible_of {G : Type*} [Group G] (ψ : (Fin (Tag.rank .G2) → ℤ) → K → G)
    (hψ : ∀ w ∈ rels (g2Cm (K := K)),
      FreeGroup.lift (fun g : Σ _ : Fin 6, K => ψ (hexRoot g.1) g.2) w = 1)
    (ñ : Fin (Tag.rank .G2) → G)
    (hW : ∀ i γ, IsRoot .G2 γ → ∀ c, ñ i * ψ γ c * (ñ i)⁻¹ = ψ ((Φ).refl i γ) c)
    (hrank : ∀ i, ExtendsToHom 𝕏 {Pi.single i 1, -Pi.single i 1} (g2PhiOf ψ)) :
    ConeCompatible Φ 𝕏 (g2PhiOf ψ) :=
  coneCompatible_of_pos (CFSG.LieType.Chevalley.weylElement .G2 K) g2_conj_mem_refl ñ
    (g2_conj_map_refl ñ ψ (fun _ hγ c => g2PhiOf_xPar ψ hγ c) hW)
    (g2_extendsToHom_pos ψ hψ (fun _ hγ c => g2PhiOf_xPar ψ hγ c)) hrank

end G2

end CFSG.Timmesfeld.RankTwo
