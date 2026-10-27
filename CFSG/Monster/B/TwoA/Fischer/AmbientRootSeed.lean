module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootOrbit
public import Certificates.Certificate16003
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3017
public import Certificates.Certificate3029
public import Certificates.Certificate3030
public import Certificates.Certificate3031
public import Certificates.Certificate3033
public import Certificates.Certificate3034
public import Certificates.Certificate3035
public import Certificates.Certificate3036
public import Certificates.Certificate3068
public import Certificates.Certificate16010
public import Certificates.Certificate16023
public import Certificates.Certificate3065
public import Certificates.Certificate3066
public import Certificates.Certificate3067
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

@[expose] noncomputable def fourGens :
    Fin 4 → Equiv.Perm CFSG.Monster.B.Fischer.Y :=
  ![MulAction.toPerm (kF CFSG.Sporadic.Mathieu.m22a),
    MulAction.toPerm (kF CFSG.Sporadic.Mathieu.m22b), MulAction.toPerm (wF (bW 0)), tPerm]

theorem fourGens_eq
    (k : Fin 4) : fourGens k = jGen (Cert.fourGen k) := by
  fin_cases k
  · change MulAction.toPerm (kF CFSG.Sporadic.Mathieu.m22a) = jGen 0
    rw [jGen_zero]
  · change MulAction.toPerm (kF CFSG.Sporadic.Mathieu.m22b) = jGen 1
    rw [jGen_one]
  · change MulAction.toPerm (wF (bW 0)) = jGen ((0 : Fin 10) + 2)
    rw [jGen_trans]
  · change tPerm = jGen 12
    rw [jGen_twelve]

@[expose] def seedRootVec
    (ρ : sliceGroup lab Y →* stdGroup) (s : Fin 4 → sliceGroup lab Y)
    (q : stdGroup) (u : fixedL) : fixedL :=
  actStar (SemidirectProduct.inl q) (actStar (SemidirectProduct.inl
    (ρ (s 3 * s 2 * s 0 * s 2 * s 3 * s 1 * s 2 * s 0 * s 2 * s 3))) u)

theorem seedLabels_nodup : Cert.seedLabels.Nodup :=
  Certificates.certificate16003.1

theorem seedLabels_lt : ∀ n ∈ Cert.seedLabels, n < 3510 :=
  Certificates.certificate16003.2

theorem ncard_seedLabels
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) :
    {y : Y | (ι (Φ y) : ℕ) ∈ Cert.seedLabels}.ncard = 126 := by
  have e : {y : Y | (ι (Φ y) : ℕ) ∈ Cert.seedLabels} =
      (fun n : ℕ => Φ.symm (decY n)) '' {n | n ∈ Cert.seedLabels} := by
    ext y
    constructor
    · intro hy
      refine ⟨_, hy, ?_⟩
      change Φ.symm (decY (ι (Φ y))) = y
      rw [decY_ι, Equiv.symm_apply_apply]
    · rintro ⟨n, hn, rfl⟩
      change (ι (Φ (Φ.symm (decY n))) : ℕ) ∈ Cert.seedLabels
      rw [Equiv.apply_symm_apply, ι_decY (seedLabels_lt n hn)]
      exact hn
  have hinj : Set.InjOn (fun n : ℕ => Φ.symm (decY n)) {n | n ∈ Cert.seedLabels} := by
    intro n hn n' hn' h
    have h' := congrArg (fun y => (ι (Φ y) : ℕ)) h
    simp only [Equiv.apply_symm_apply] at h'
    rwa [ι_decY (seedLabels_lt n hn), ι_decY (seedLabels_lt n' hn')] at h'
  rw [e, hinj.ncard_image, show {n | n ∈ Cert.seedLabels} = (Cert.seedLabels.toFinset : Set ℕ) by
    ext n; simp, Set.ncard_coe_finset, List.toFinset_card_of_nodup seedLabels_nodup,
    Cert.seedLabels_length]

theorem ncard_commute_lab (hS : IsFischerSlice act lab Y) (y' : Y) :
    {y : Y | Commute (lab y') (lab y)}.ncard = 694 := by
  have e : Subtype.val '' {y : Y | Commute (lab y') (lab y)} =
      insert (y' : V) ((sliceGraph lab Y).neighborSet y') := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases h : (y : V) = y'
      · exact Or.inl h
      · exact Or.inr ⟨y'.2, y.2, fun e => h e.symm, hy⟩
    · rintro (rfl | ⟨-, hv, -, hc⟩)
      · exact ⟨y', Commute.refl _, rfl⟩
      · exact ⟨⟨v, hv⟩, hc, rfl⟩
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective, e,
    Set.ncard_insert_of_notMem (fun h => h.2.2.1 rfl) (hS.finite.subset fun _ h => h.2.1),
    hS.valency y' y'.2]

namespace FullIntertwinerHyp

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))] {x : V}
  {η : C ≃ X₀}
  {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
    CFSG.Blueprint.NativeSporadic.M22}
  {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀} {α : setStab act lab Y C →* F₀}
  (H : FullIntertwinerHyp act lab Y C x η θ φ α)
  {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
  {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
  (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
  {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y)
include H hΦ

theorem existsUnique_fourGens :
    ∃! s : Fin 4 → sliceGroup lab Y, ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v →
      Φ w = fourGens k (Φ v) := by
  have hex : ∀ k : Fin 4, ∃ g : sliceGroup lab Y, H.conjHom Φ g = fourGens k := fun k => by
    rw [fourGens_eq]
    exact H.exists_conjHom_eq hΦ (by fin_cases k <;> decide)
  have hiff : ∀ (g : sliceGroup lab Y) (π : Equiv.Perm CFSG.Monster.B.Fischer.Y),
      (∀ (v w : Y), (w : V) = act (g : S) v → Φ w = π (Φ v)) ↔ H.conjHom Φ g = π := by
    intro g π
    constructor
    · intro h
      refine Equiv.ext fun u => ?_
      obtain ⟨v, rfl⟩ := Φ.surjective u
      rw [← H.phi_act g v (H.slice.mapsTo _ g.2 _ v.2)]
      exact h v _ rfl
    · rintro rfl v w hw
      rw [← H.phi_act g v (H.slice.mapsTo _ g.2 _ v.2)]
      congr 1
      exact Subtype.ext hw
  choose s hs using hex
  refine ⟨s, fun k => (hiff (s k) _).2 (hs k), fun s' hs' => funext fun k => ?_⟩
  exact H.conjHom_injective Φ (((hiff (s' k) _).1 (hs' k)).trans (hs k).symm)

include hroot hΨ in
theorem gL_word_coordEquiv
    {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v)) :
    gL (ρ (s 3 * s 2 * s 0 * s 2 * s 3 * s 1 * s 2 * s 0 * s 2 * s 3))
        (H.coordEquiv hΦ Ψ (toVecD 78 949)) =
      H.coordEquiv hΦ Ψ (toVecD 78 16058837531770935235962) := by
  have hc : ∀ k : Fin 4, H.conjHom Φ (s k) = jGen (Cert.fourGen k) := fun k => by
    rw [← fourGens_eq]
    refine Equiv.ext fun u => ?_
    obtain ⟨v, rfl⟩ := Φ.surjective u
    rw [← H.phi_act (s k) v (H.slice.mapsTo _ (s k).2 _ v.2)]
    exact hs k v _ rfl
  have hk : ∀ (k : Fin 4) (c : Fin 78 → ZMod 2),
      gL (ρ (s k)) (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ (Cert.fourMat k *ᵥ c) :=
    fun k c => H.gL_coordEquiv_fourMat hΦ hroot hΨ k.2 (hc k) c
  have hw := (Cert.fischer_seed_certificate).2.2.2.1
  simp only [Cert.seedWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, ← Matrix.mulVec_mulVec] at hw
  simp only [map_mul, gL_mul_apply]
  rw [hk 3, hk 2, hk 0, hk 2, hk 1, hk 3, hk 2, hk 0, hk 2, hk 3]
  exact congrArg (H.coordEquiv hΦ Ψ) hw

include hρ hroot hΨ in
theorem gL_root_coordEquiv
    {q : stdGroup} (hq : IsConj rootInv q) {c₀ : Fin 78 → ZMod 2}
    (hqz : rootVecOf q = H.coordEquiv hΦ Ψ c₀) (c : Fin 78 → ZMod 2) :
    gL q (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ (Cert.rootOp c₀ c) := by
  rw [← actStar_inl_eq_gL, actStar_inl_of_mem_rootClass hq, hqz,
    H.bracketL_coordEquiv hΦ hρ hroot hΨ, H.formL_coordEquiv hΦ hρ hroot hΨ, Cert.rootOp,
    map_add, map_add, map_smul]

include hρ hroot hΨ in
theorem seedRootVec_eq
    {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    {q : stdGroup} (hq : IsConj rootInv q) (hqz : rootVecOf q = cliqueFixedVec Φ Ψ) :
    seedRootVec ρ s q (cliqueFixedVec Φ Ψ) =
      H.coordEquiv hΦ Ψ (toVecD 78 16058837527637121392057) := by
  rw [H.cliqueFixedVec_eq hΦ hΨ] at hqz ⊢
  rw [seedRootVec, actStar_inl_eq_gL, actStar_inl_eq_gL, H.gL_word_coordEquiv hΦ hroot hΨ hs,
    H.gL_root_coordEquiv hΦ hρ hroot hΨ hq hqz, (Cert.fischer_seed_certificate).2.2.2.2.1]

include hρ hroot hΨ in
theorem seedRootVec_mem
    (s : Fin 4 → sliceGroup lab Y) (q : stdGroup) :
    seedRootVec ρ s q (cliqueFixedVec Φ Ψ) ∈ rootVecSet := by
  rw [seedRootVec, actStar_inl_eq_gL, actStar_inl_eq_gL]
  exact gL_mem_rootVecSet (gL_mem_rootVecSet (H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ) _)
    q

include hρ hroot hΨ in
theorem commute_seed_iff
    {s : Fin 4 → sliceGroup lab Y}
    (hs : ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v → Φ w = fourGens k (Φ v))
    {q : stdGroup} (hq : IsConj rootInv q) (hqz : rootVecOf q = cliqueFixedVec Φ Ψ)
    {q' : stdGroup} (hq' : IsConj rootInv q')
    (hq'a : rootVecOf q' = seedRootVec ρ s q (cliqueFixedVec Φ Ψ)) (y : Y) :
    Commute q' (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) ↔ (ι (Φ y) : ℕ) ∈ Cert.seedLabels := by
  rw [← bracketL_eq_zero_iff_commute hq' (hroot y), hq'a, H.seedRootVec_eq hΦ hρ hroot hΨ hs hq hqz,
    show rootVecOf (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩) = Ψ (ncommVec lab Y y) from (hΨ y).symm,
    H.psi_ncommVec_eq hΦ hΨ, H.bracketL_coordEquiv hΦ hρ hroot hΨ,
    LinearEquiv.map_eq_zero_iff]
  exact (Cert.fischer_seed_certificate).2.2.2.2.2.1 (Φ y)

include hρ hroot hΨ in
theorem ncard_commute_hOrbit_cliqueFixedVec
    {u : fixedL} (hu : u ∈ hOrbit ρ (cliqueFixedVec Φ Ψ))
    {q : stdGroup} (hq : IsConj rootInv q) (hqu : rootVecOf q = u) :
    {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 22 := by
  obtain ⟨q₀, hq₀, hq₀z⟩ := H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
  rw [H.ncard_commute_of_mem_hOrbit hu hq₀ hq hq₀z hqu]
  have e : {y : Y | Commute q₀ (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | (y : V) ∈ C} := by
    ext y
    exact H.commute_cliqueFixedVec_iff hΦ hρ hroot hΨ hq₀ hq₀z y
  rw [e, H.ncard_clique]

include hρ hroot hΨ in
theorem ncard_commute_hOrbit_cliqueFixedVec_add
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) {u : fixedL}
    (hu : u ∈ hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) {q : stdGroup}
    (hq : IsConj rootInv q) (hqu : rootVecOf q = u) :
    {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 22 := by
  obtain ⟨q₁, hq₁, hq₁z⟩ := H.cliqueFixedVec_add_mem_rootVecSet hΦ hρ hroot hΨ hy₀
  rw [H.ncard_commute_of_mem_hOrbit hu hq₁ hq hq₁z hqu]
  have e : {y : Y | Commute q₁ (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | (y : V) ∈ C} := by
    ext y
    exact H.commute_cliqueFixedVec_add_iff hΦ hρ hroot hΨ hy₀ hq₁ hq₁z y
  rw [e, H.ncard_clique]

omit hΦ in
include hρ hroot hΨ in
theorem ncard_commute_label
    {q : stdGroup} (hq : IsConj rootInv q) (y' : Y)
    (hqy : rootVecOf q = Ψ (ncommVec lab Y y')) :
    {y : Y | Commute q (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 694 := by
  have e : q = ρ ⟨lab y', lab_mem_sliceGroup y'.2⟩ :=
    bijOn_rootVecOf.injOn hq (hroot y') (hqy.trans (hΨ y'))
  subst e
  have e2 : {y : Y | Commute (ρ ⟨lab y', lab_mem_sliceGroup y'.2⟩)
      (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} = {y : Y | Commute (lab y') (lab y)} := by
    ext y
    exact IsFischerSlice.commute_rho_iff hρ y' y
  rw [e2, ncard_commute_lab H.slice y']

end FullIntertwinerHyp

namespace IsFischerSlice

theorem explicit_126_neighbor_ambient_root
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x : V} (hx : x ∈ hexadFiber lab Y C ∅) {η : C ≃ X₀}
    {θ : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    {φ : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    {α : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    {Φ : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    {ρ : sliceGroup lab Y →* stdGroup} (hρ : Function.Injective ρ)
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y) :
    (∃! s : Fin 4 → sliceGroup lab Y, ∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v →
      Φ w = fourGens k (Φ v)) ∧
    (∃! q : stdGroup, IsConj rootInv q ∧ rootVecOf q = cliqueFixedVec Φ Ψ) ∧
    ∀ s : Fin 4 → sliceGroup lab Y, (∀ (k : Fin 4) (v w : Y), (w : V) = act (s k : S) v →
      Φ w = fourGens k (Φ v)) →
    ∀ q : stdGroup, IsConj rootInv q → rootVecOf q = cliqueFixedVec Φ Ψ →
      seedRootVec ρ s q (cliqueFixedVec Φ Ψ) ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} ∧
      seedRootVec ρ s q (cliqueFixedVec Φ Ψ) = gramVec Φ Ψ 16058837527637121392057 ∧
      (∀ q' : stdGroup, IsConj rootInv q' →
        rootVecOf q' = seedRootVec ρ s q (cliqueFixedVec Φ Ψ) →
        {y : Y | Commute q' (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} =
          {y : Y | (ι (Φ y) : ℕ) ∈ Cert.seedLabels} ∧
        {y : Y | Commute q' (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 126) ∧
      ∀ y₀ : Y, (y₀ : V) ∈ C →
        seedRootVec ρ s q (cliqueFixedVec Φ Ψ) ∈ rootVecOf '' {q : stdGroup | IsConj rootInv q} \
          (Set.range (fun y : Y => Ψ (ncommVec lab Y y)) ∪ hOrbit ρ (cliqueFixedVec Φ Ψ) ∪
            hOrbit ρ (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀))) := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  refine ⟨H.existsUnique_fourGens hΦ, ?_, fun s hs q hq hqz => ?_⟩
  · obtain ⟨q, hq, hqz⟩ := H.cliqueFixedVec_mem_rootVecSet hΦ hρ hroot hΨ
    exact ⟨q, ⟨hq, hqz⟩, fun q' hq' => bijOn_rootVecOf.injOn hq'.1 hq (hq'.2.trans hqz.symm)⟩
  have hmem := H.seedRootVec_mem hΦ hρ hroot hΨ s q
  have hcount : ∀ q' : stdGroup, IsConj rootInv q' →
      rootVecOf q' = seedRootVec ρ s q (cliqueFixedVec Φ Ψ) →
      {y : Y | Commute q' (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} =
          {y : Y | (ι (Φ y) : ℕ) ∈ Cert.seedLabels} ∧
        {y : Y | Commute q' (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)}.ncard = 126 := by
    intro q' hq' hq'a
    have e : {y : Y | Commute q' (ρ ⟨lab y, lab_mem_sliceGroup y.2⟩)} =
        {y : Y | (ι (Φ y) : ℕ) ∈ Cert.seedLabels} := by
      ext y
      exact H.commute_seed_iff hΦ hρ hroot hΨ hs hq hqz hq' hq'a y
    exact ⟨e, by rw [e, ncard_seedLabels]⟩
  refine ⟨hmem, by rw [H.seedRootVec_eq hΦ hρ hroot hΨ hs hq hqz, H.gramVec_eq hΦ], hcount,
    fun y₀ hy₀ => ⟨hmem, ?_⟩⟩
  obtain ⟨q', hq', hq'a⟩ := hmem
  have h126 := (hcount q' hq' hq'a).2
  rintro ((⟨y', hy'⟩ | hu) | hu)
  · have := H.ncard_commute_label hρ hroot hΨ hq' y' (hq'a.trans hy'.symm)
    omega
  · have := H.ncard_commute_hOrbit_cliqueFixedVec hΦ hρ hroot hΨ hu hq' hq'a
    omega
  · have := H.ncard_commute_hOrbit_cliqueFixedVec_add hΦ hρ hroot hΨ hy₀ hu hq' hq'a
    omega

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
