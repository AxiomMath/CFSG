module

public import CFSG.Monster.B.TwoA.Fischer.AmbientRootCoord

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.Classical.Mog22
  CFSG.Sporadic.SmallF2
open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open scoped Matrix IsMulCommutative

def mapsToSubgroup {G X : Type*} [Group G] (π : G →* Equiv.Perm X) {O : Set X}
    (hO : O.Finite) : Subgroup G where
  carrier := {g | Set.MapsTo (π g) O O}
  mul_mem' {a b} ha hb := by
    change Set.MapsTo (π (a * b)) O O
    rw [map_mul, Equiv.Perm.coe_mul]
    exact Set.MapsTo.comp ha hb
  one_mem' := by
    change Set.MapsTo (π 1) O O
    rw [map_one, Equiv.Perm.coe_one]
    exact Set.mapsTo_id O
  inv_mem' {a} ha := by
    have hb := (hO.injOn_iff_bijOn_of_mapsTo ha).1 (π a).injective.injOn
    intro w hw
    obtain ⟨w', hw', rfl⟩ := hb.surjOn hw
    rw [map_inv, Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    exact hw'

theorem mem_mapsToSubgroup {G X : Type*} [Group G] {π : G →* Equiv.Perm X} {O : Set X}
    {hO : O.Finite} {g : G} : g ∈ mapsToSubgroup π hO ↔ Set.MapsTo (π g) O O :=
  Iff.rfl

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

@[expose] def cliqueFixedVec
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y)
    (Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL) : fixedL :=
  ([0, 2, 4, 6, 8, 10, 12].map fun p => Ψ (ncommVec lab Y (Φ.symm (decY p)))).sum

@[expose] def gramVec
    (Φ : Y ≃ CFSG.Monster.B.Fischer.Y) (Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL)
    (m : ℕ) : fixedL :=
  ∑ i : Fin 78, toVecD 78 m i • Ψ (ncommVec lab Y (Φ.symm (decY (Cert.basisPt i))))

@[expose] def cliqueVecs (Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL) (C : Set V) : Set fixedL :=
  (fun y => Ψ (ncommVec lab Y y)) '' {y : Y | (y : V) ∈ C}

variable (act) in
@[expose] def fOrbit
    (C : Set V) (ρ : sliceGroup lab Y →* stdGroup) (u : fixedL) : Set fixedL :=
  {u' | ∃ f : setStab act lab Y C, u' = actStar (SemidirectProduct.inl (ρ ⟨f, f.2.1⟩)) u}

theorem orbRep_eq (t : Fin 8) :
    (![0, 1, 3, 7, 39, 117, 437, 949] : Fin 8 → ℕ) t = Cert.orbRep t := by
  fin_cases t <;> rfl

theorem orbLen_eq (t : Fin 8) :
    (![1, 22, 231, 770, 770, 231, 22, 1] : Fin 8 → ℕ) t = Cert.orbLen t := by
  fin_cases t <;> rfl

theorem orbRank_eq (t : Fin 8) :
    (![0, 22, 32, 38, 38, 32, 22, 22] : Fin 8 → ℕ) t = Cert.orbRank t := by
  fin_cases t <;> rfl

theorem orbRank_eq_22 {t : ℕ} (ht : t < 8) (h : Cert.orbRank t = 22) : t = 1 ∨ t = 6 ∨ t = 7 := by
  interval_cases t <;> first | (left; rfl) | (right; left; rfl) | (right; right; rfl) |
    exact absurd h (by decide)

theorem rank22_iff
    (c : Fin 78 → ZMod 2) :
    c ∈ Cert.cliqueSpan ∧ (Cert.adMat c).rank = 22 ↔
      c ∈ Cert.orbSet 1 ∨ c ∈ Cert.orbSet 6 ∨ c ∈ Cert.orbSet 7 := by
  constructor
  · rintro ⟨hc, hr⟩
    obtain ⟨t, ht, hct⟩ := (Cert.mem_cliqueSpan_iff_orbSet c).1 hc
    rw [Cert.rank_orbSet hct] at hr
    rcases orbRank_eq_22 ht hr with rfl | rfl | rfl
    · exact Or.inl hct
    · exact Or.inr (Or.inl hct)
    · exact Or.inr (Or.inr hct)
  · rintro (h | h | h)
    · exact ⟨(Cert.mem_cliqueSpan_iff_orbSet c).2 ⟨1, by norm_num, h⟩, Cert.rank_orbSet h⟩
    · exact ⟨(Cert.mem_cliqueSpan_iff_orbSet c).2 ⟨6, by norm_num, h⟩, Cert.rank_orbSet h⟩
    · exact ⟨(Cert.mem_cliqueSpan_iff_orbSet c).2 ⟨7, by norm_num, h⟩, Cert.rank_orbSet h⟩

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

theorem gramVec_eq
    (m : ℕ) : gramVec Φ Ψ m = H.coordEquiv hΦ Ψ (toVecD 78 m) := by
  rw [gramVec, coordEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gramPt_eq_symm_decY Φ i.2]

include hΨ in
theorem psi_ncommVec_eq
    (y : Y) :
    Ψ (ncommVec lab Y y) = H.coordEquiv hΦ Ψ (toVecD 78 (Cert.labelCoord (ι (Φ y)))) := by
  rw [hΨ, H.adjVec_eq_coordEquiv hΦ hΨ]

include hΨ in
theorem psi_decY
    {p : ℕ} (hp : p < 3510) :
    Ψ (ncommVec lab Y (Φ.symm (decY p))) = H.coordEquiv hΦ Ψ (toVecD 78 (Cert.labelCoord p)) := by
  rw [H.psi_ncommVec_eq hΦ hΨ, Equiv.apply_symm_apply, ι_decY hp]

include hΨ in
theorem cliqueFixedVec_eq :
    cliqueFixedVec Φ Ψ = H.coordEquiv hΦ Ψ (toVecD 78 949) := by
  rw [← Cert.maskSum_vec, map_list_sum, List.map_map, cliqueFixedVec]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp' : p < 3510 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    omega
  rw [Function.comp_apply, H.psi_decY hΦ hΨ hp']

theorem mem_iff_ι_lt
    (y : Y) : (y : V) ∈ C ↔ (ι (Φ y) : ℕ) < 22 := by
  constructor
  · intro hy
    rw [hΦ.clique ⟨y, hy⟩ y rfl, ι_inl]
    exact (pos _).2
  · intro hlt
    rcases hy : Φ y with x₀ | w | z
    · obtain ⟨z, hz⟩ := η.surjective x₀
      have e : Φ ⟨z, H.clique.1.1 z.2⟩ = Φ y := by rw [H.phi_clique hΦ, hz, hy]
      rw [← Φ.injective e]
      exact z.2
    · rw [hy] at hlt
      change 22 + _ < 22 at hlt
      omega
    · rw [hy] at hlt
      change 1046 + _ + _ < 22 at hlt
      omega

include hΨ in
theorem cliqueVecs_eq :
    cliqueVecs Ψ C =
    H.coordEquiv hΦ Ψ '' Set.range fun c : Fin 22 => toVecD 78 (Cert.labelCoord c) := by
  ext u
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, ⟨⟨ι (Φ y), (H.mem_iff_ι_lt hΦ y).1 hy⟩, rfl⟩, (H.psi_ncommVec_eq hΦ hΨ y).symm⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    have hc : (c : ℕ) < 3510 := by omega
    refine ⟨Φ.symm (decY c), ?_, H.psi_decY hΦ hΨ hc⟩
    change _ ∈ C
    rw [H.mem_iff_ι_lt hΦ, Equiv.apply_symm_apply, ι_decY hc]
    exact c.2

include hΨ in
theorem span_cliqueVecs :
    Submodule.span (ZMod 2) (cliqueVecs Ψ C) =
      Cert.cliqueSpan.map (H.coordEquiv hΦ Ψ).toLinearMap := by
  rw [H.cliqueVecs_eq hΦ hΨ, Cert.cliqueSpan, ← Submodule.span_image]
  rfl

include hΨ in
theorem finrank_span_cliqueVecs :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (cliqueVecs Ψ C)) = 11 := by
  rw [H.span_cliqueVecs hΦ hΨ, LinearEquiv.finrank_map_eq]
  exact Cert.finrank_span_clique

include hΨ in
theorem mem_span_cliqueVecs
    (c : Fin 78 → ZMod 2) :
    H.coordEquiv hΦ Ψ c ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C) ↔ c ∈ Cert.cliqueSpan := by
  rw [H.span_cliqueVecs hΦ hΨ, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

include hroot hΨ in
theorem fixed_setStab_eq :
    {u : fixedL | ∀ f : setStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨f, f.2.1⟩)) u = u} = {0, cliqueFixedVec Φ Ψ} := by
  ext u
  obtain ⟨c, rfl⟩ := (H.coordEquiv hΦ Ψ).surjective u
  change (∀ f : setStab act lab Y C,
      actH ρ ⟨f, f.2.1⟩ (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ c) ↔ _
  rw [H.fixed_setStab_iff hΦ hroot hΨ, Cert.fixed_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
    H.cliqueFixedVec_eq hΦ hΨ, ← map_zero (H.coordEquiv hΦ Ψ),
    (H.coordEquiv hΦ Ψ).injective.eq_iff, (H.coordEquiv hΦ Ψ).injective.eq_iff]

include hΨ in
theorem cliqueFixedVec_ne_zero :
    cliqueFixedVec Φ Ψ ≠ 0 := by
  rw [H.cliqueFixedVec_eq hΦ hΨ, ← map_zero (H.coordEquiv hΦ Ψ),
    (H.coordEquiv hΦ Ψ).injective.ne_iff]
  exact Cert.fischer_clique_fixed_certificate.2.2.2.2.1

include hΨ in
theorem cliqueFixedVec_ne
    (y : Y) : cliqueFixedVec Φ Ψ ≠ Ψ (ncommVec lab Y y) := by
  rw [H.cliqueFixedVec_eq hΦ hΨ, H.psi_ncommVec_eq hΦ hΨ, (H.coordEquiv hΦ Ψ).injective.ne_iff]
  exact (Cert.ne_labelCoord (Φ y)).symm

include hroot hΨ in
theorem eq_cliqueFixedVec_iff
    (u : fixedL) :
    (u ≠ 0 ∧ ∀ f : setStab act lab Y C, actStar (SemidirectProduct.inl (ρ ⟨f, f.2.1⟩)) u = u) ↔
      u = cliqueFixedVec Φ Ψ := by
  have h := Set.ext_iff.1 (H.fixed_setStab_eq hΦ hroot hΨ) u
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  change (∀ f : setStab act lab Y C, _) ↔ _ at h
  constructor
  · rintro ⟨h0, hf⟩
    exact (h.1 hf).resolve_left h0
  · rintro rfl
    exact ⟨H.cliqueFixedVec_ne_zero hΦ hΨ, h.2 (Or.inr rfl)⟩

theorem bijective_gramComb :
    Function.Bijective fun c : Fin 78 → ZMod 2 =>
      ∑ i : Fin 78, c i • Ψ (ncommVec lab Y (Φ.symm (decY (Cert.basisPt i)))) := by
  convert (H.coordEquiv hΦ Ψ).bijective using 1
  funext c
  rw [coordEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gramPt_eq_symm_decY Φ i.2]

include hroot hΨ in
theorem fOrbit_coordEquiv
    (v₀ : Fin 78 → ZMod 2) :
    fOrbit act C ρ (H.coordEquiv hΦ Ψ v₀) =
      H.coordEquiv hΦ Ψ '' {v | Cert.FReach v₀ v} := by
  have := finite_fixedL
  apply Set.Subset.antisymm
  · rintro _ ⟨f, rfl⟩
    set O := H.coordEquiv hΦ Ψ '' {v | Cert.FReach v₀ v} with hO
    have hK : ∀ k < 12, ∀ g, H.conjHom Φ g = jGen k →
        g ∈ mapsToSubgroup (actH ρ) (Set.toFinite O) := by
      intro k hk g hg
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨Cert.fMat k *ᵥ v, Cert.FReach.step k hk hv,
        by rw [actH_eq_gL, H.gL_coordEquiv_fMat hΦ hroot hΨ hk hg]⟩
    exact H.setStab_mem_of_gen hΦ _ hK f ⟨v₀, Cert.FReach.refl, rfl⟩
  · rintro _ ⟨v, hv, rfl⟩
    induction hv with
    | refl =>
      refine ⟨1, ?_⟩
      change _ = actH ρ 1 _
      rw [map_one, Equiv.Perm.one_apply]
    | step k hk _ ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨g, hg⟩ := H.exists_conjHom_eq hΦ (show k < 13 by omega)
      refine ⟨⟨g, H.mem_setStab_of_conjHom_eq hΦ hk hg⟩ * f, ?_⟩
      change _ = actH ρ (g * ⟨f, f.2.1⟩) _
      rw [← H.gL_coordEquiv_fMat hΦ hroot hΨ hk hg, hf, map_mul, Equiv.Perm.mul_apply,
        actH_eq_gL ρ g]
      rfl

include hroot hΨ in
theorem fixed_ptStab_eq :
    {u : fixedL | ∀ r : ptStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨r, r.2.1⟩)) u = u} =
      Submodule.span (ZMod 2) (cliqueVecs Ψ C) := by
  ext u
  obtain ⟨c, rfl⟩ := (H.coordEquiv hΦ Ψ).surjective u
  change (∀ r : ptStab act lab Y C,
      actH ρ ⟨r, r.2.1⟩ (H.coordEquiv hΦ Ψ c) = H.coordEquiv hΦ Ψ c) ↔ _
  rw [H.fixed_ptStab_iff hΦ hroot hΨ, Cert.radical_fixed_iff, SetLike.mem_coe,
    H.mem_span_cliqueVecs hΦ hΨ]

include hΨ in
theorem ncard_span_cliqueVecs :
    ((Submodule.span (ZMod 2) (cliqueVecs Ψ C) : Set fixedL)).ncard = 2048 := by
  rw [H.span_cliqueVecs hΦ hΨ, Submodule.map_coe, LinearEquiv.coe_coe,
    Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective, Cert.ncard_cliqueSpan]

include hroot hΨ in
theorem fOrbit_gramVec_orbRep
    {t : ℕ} (ht : t < 8) :
    fOrbit act C ρ (gramVec Φ Ψ (Cert.orbRep t)) = H.coordEquiv hΦ Ψ '' Cert.orbSet t := by
  rw [H.gramVec_eq hΦ, H.fOrbit_coordEquiv hΦ hroot hΨ]
  congr 1
  ext v
  exact Cert.freach_iff ht v

include hroot hΨ in
theorem existsUnique_fOrbit
    (u : fixedL) (hu : u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C)) :
    ∃! t : Fin 8, u ∈ fOrbit act C ρ (gramVec Φ Ψ ((![0, 1, 3, 7, 39, 117, 437, 949] :
      Fin 8 → ℕ) t)) := by
  obtain ⟨c, rfl⟩ := (H.coordEquiv hΦ Ψ).surjective u
  have hc : c ∈ Cert.cliqueSpan := (H.mem_span_cliqueVecs hΦ hΨ c).1 hu
  obtain ⟨t, ht, hct⟩ := (Cert.mem_cliqueSpan_iff_orbSet c).1 hc
  refine ⟨⟨t, ht⟩, ?_, fun t' ht' => ?_⟩
  · dsimp only
    rw [orbRep_eq, H.fOrbit_gramVec_orbRep hΦ hroot hΨ ht]
    exact ⟨c, hct, rfl⟩
  · dsimp only at ht'
    rw [orbRep_eq, H.fOrbit_gramVec_orbRep hΦ hroot hΨ t'.2] at ht'
    obtain ⟨c', hc', e⟩ := ht'
    obtain rfl := (H.coordEquiv hΦ Ψ).injective e
    by_contra hne
    exact Set.disjoint_left.1 (Cert.orbSet_disjoint fun h => hne (Fin.ext h)) hc' hct

include hρ hroot hΨ in
theorem ncard_rank_fOrbit
    (t : Fin 8) :
    (fOrbit act C ρ (gramVec Φ Ψ ((![0, 1, 3, 7, 39, 117, 437, 949] : Fin 8 → ℕ) t))).ncard =
        (![1, 22, 231, 770, 770, 231, 22, 1] : Fin 8 → ℕ) t ∧
      ∀ u ∈ fOrbit act C ρ (gramVec Φ Ψ ((![0, 1, 3, 7, 39, 117, 437, 949] : Fin 8 → ℕ) t)),
        Module.finrank (ZMod 2) (LinearMap.range (adL u)) =
          (![0, 22, 32, 38, 38, 32, 22, 22] : Fin 8 → ℕ) t := by
  rw [orbRep_eq, H.fOrbit_gramVec_orbRep hΦ hroot hΨ t.2, orbLen_eq, orbRank_eq]
  refine ⟨?_, ?_⟩
  · rw [Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective, Cert.ncard_orbSet t.2]
  · rintro _ ⟨v, hv, rfl⟩
    rw [H.finrank_range_adL_coordEquiv hΦ hρ hroot hΨ, Cert.rank_orbSet hv]

include hroot hΨ in
theorem fOrbit_one :
    fOrbit act C ρ (gramVec Φ Ψ 1) = cliqueVecs Ψ C := by
  rw [show (1 : ℕ) = Cert.orbRep 1 from rfl, H.fOrbit_gramVec_orbRep hΦ hroot hΨ (by norm_num),
    Cert.orbSet_one, H.cliqueVecs_eq hΦ hΨ]

include hroot hΨ in
theorem fOrbit_six :
    fOrbit act C ρ (gramVec Φ Ψ 437) = (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C := by
  rw [show (437 : ℕ) = Cert.orbRep 6 from rfl, H.fOrbit_gramVec_orbRep hΦ hroot hΨ (by norm_num),
    Cert.orbSet_six, H.cliqueVecs_eq hΦ hΨ, H.cliqueFixedVec_eq hΦ hΨ, Set.image_image,
    ← Set.range_comp, ← Set.range_comp]
  congr 1
  funext c
  rw [Function.comp_apply, Function.comp_apply, map_add]

include hroot hΨ in
theorem fOrbit_seven :
    fOrbit act C ρ (gramVec Φ Ψ 949) = {cliqueFixedVec Φ Ψ} := by
  rw [show (949 : ℕ) = Cert.orbRep 7 from rfl, H.fOrbit_gramVec_orbRep hΦ hroot hΨ (by norm_num),
    Cert.orbSet_seven, Set.image_singleton, H.cliqueFixedVec_eq hΦ hΨ]

include hroot hΨ in
theorem cliqueVecs_eq_orbSet :
    cliqueVecs Ψ C = H.coordEquiv hΦ Ψ '' Cert.orbSet 1 := by
  have h := H.fOrbit_gramVec_orbRep hΦ hroot hΨ (t := 1) (by norm_num)
  rwa [show Cert.orbRep 1 = 1 from rfl, H.fOrbit_one hΦ hroot hΨ] at h

include hroot hΨ in
theorem cliqueShift_eq_orbSet :
    (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C = H.coordEquiv hΦ Ψ '' Cert.orbSet 6 := by
  have h := H.fOrbit_gramVec_orbRep hΦ hroot hΨ (t := 6) (by norm_num)
  rwa [show Cert.orbRep 6 = 437 from rfl, H.fOrbit_six hΦ hroot hΨ] at h

include hroot hΨ in
theorem singleton_eq_orbSet :

    {cliqueFixedVec Φ Ψ} = H.coordEquiv hΦ Ψ '' Cert.orbSet 7 := by
  have h := H.fOrbit_gramVec_orbRep hΦ hroot hΨ (t := 7) (by norm_num)
  rwa [show Cert.orbRep 7 = 949 from rfl, H.fOrbit_seven hΦ hroot hΨ] at h

include hρ hroot hΨ in
theorem rank22_eq :
    {u | u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C) ∧
        Module.finrank (ZMod 2) (LinearMap.range (adL u)) = 22} =
      cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∪ {cliqueFixedVec Φ Ψ} := by
  ext u
  obtain ⟨c, rfl⟩ := (H.coordEquiv hΦ Ψ).surjective u
  rw [Set.mem_ofPred_eq, H.mem_span_cliqueVecs hΦ hΨ, H.finrank_range_adL_coordEquiv hΦ hρ hroot hΨ,
    rank22_iff, Set.mem_union, Set.mem_union, H.cliqueShift_eq_orbSet hΦ hroot hΨ,
    H.cliqueVecs_eq_orbSet hΦ hroot hΨ, H.singleton_eq_orbSet hΦ hroot hΨ,
    (H.coordEquiv hΦ Ψ).injective.mem_set_image, (H.coordEquiv hΦ Ψ).injective.mem_set_image,
    (H.coordEquiv hΦ Ψ).injective.mem_set_image, or_assoc]

include hroot hΨ in
theorem disjoint_cliqueShift :
    Disjoint (cliqueVecs Ψ C) ((cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C) := by
  rw [H.cliqueShift_eq_orbSet hΦ hroot hΨ, H.cliqueVecs_eq_orbSet hΦ hroot hΨ,
    Set.disjoint_image_iff (H.coordEquiv hΦ Ψ).injective]
  exact Cert.orbSet_disjoint (by norm_num)

include hroot hΨ in
theorem cliqueFixedVec_not_mem :
    cliqueFixedVec Φ Ψ ∉ cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C := by
  rw [H.cliqueShift_eq_orbSet hΦ hroot hΨ, H.cliqueVecs_eq_orbSet hΦ hroot hΨ,
    H.cliqueFixedVec_eq hΦ hΨ, Set.mem_union, (H.coordEquiv hΦ Ψ).injective.mem_set_image,
    (H.coordEquiv hΦ Ψ).injective.mem_set_image]
  have h7 : toVecD 78 949 ∈ Cert.orbSet 7 := by
    rw [Cert.orbSet_seven]
    rfl
  rintro (h | h)
  · exact Set.disjoint_left.1 (Cert.orbSet_disjoint (by norm_num : (1 : ℕ) ≠ 7)) h h7
  · exact Set.disjoint_left.1 (Cert.orbSet_disjoint (by norm_num : (6 : ℕ) ≠ 7)) h h7

include hroot hΨ in
theorem ncard_rank22 :
    (cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∪
      {cliqueFixedVec Φ Ψ}).ncard = 45 := by
  have := finite_fixedL
  rw [Set.ncard_union_eq (Set.disjoint_singleton_right.2 (H.cliqueFixedVec_not_mem hΦ hroot hΨ)),
    Set.ncard_union_eq (H.disjoint_cliqueShift hΦ hroot hΨ), Set.ncard_singleton,
    H.cliqueShift_eq_orbSet hΦ hroot hΨ, H.cliqueVecs_eq_orbSet hΦ hroot hΨ,
    Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective,
    Set.ncard_image_of_injective _ (H.coordEquiv hΦ Ψ).injective,
    Cert.ncard_orbSet (by norm_num), Cert.ncard_orbSet (by norm_num)]
  rfl

include hρ hroot hΨ in
theorem bracketL_cliqueFixedVec_eq_zero_iff
    (y : Y) :
    bracketL (cliqueFixedVec Φ Ψ) (Ψ (ncommVec lab Y y)) = 0 ↔ (y : V) ∈ C := by
  rw [H.cliqueFixedVec_eq hΦ hΨ, H.psi_ncommVec_eq hΦ hΨ, H.bracketL_coordEquiv hΦ hρ hroot hΨ,
    ← map_zero (H.coordEquiv hΦ Ψ), (H.coordEquiv hΦ Ψ).injective.eq_iff, Cert.zeroSet_clique,
    H.mem_iff_ι_lt hΦ]

include hρ hroot hΨ in
theorem bracketL_cliqueFixedVec_add_eq_zero_iff
    {y₀ : Y} (hy₀ : (y₀ : V) ∈ C) (y : Y) :
    bracketL (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) (Ψ (ncommVec lab Y y)) = 0 ↔
      (y : V) ∈ C := by
  rw [H.cliqueFixedVec_eq hΦ hΨ, H.psi_ncommVec_eq hΦ hΨ y₀, ← map_add,
    H.psi_ncommVec_eq hΦ hΨ y, H.bracketL_coordEquiv hΦ hρ hroot hΨ,
    ← map_zero (H.coordEquiv hΦ Ψ), (H.coordEquiv hΦ Ψ).injective.eq_iff,
    Cert.zeroSet_clique_add ((H.mem_iff_ι_lt hΦ y₀).1 hy₀), H.mem_iff_ι_lt hΦ]

end FullIntertwinerHyp

namespace IsFischerSlice

theorem clique_unique_fixed_adjoint_vector
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
    {ρ : sliceGroup lab Y →* stdGroup}
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (cliqueVecs Ψ C)) = 11 ∧
    {u : fixedL | ∀ f : setStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨f, f.2.1⟩)) u = u} = {0, cliqueFixedVec Φ Ψ} ∧
    cliqueFixedVec Φ Ψ ≠ 0 ∧
    Function.Bijective (fun c : Fin 78 → ZMod 2 =>
      ∑ i : Fin 78, c i • Ψ (ncommVec lab Y (Φ.symm (decY (Cert.basisPt i))))) ∧
    cliqueFixedVec Φ Ψ = gramVec Φ Ψ 949 ∧
    (∀ y : Y, cliqueFixedVec Φ Ψ ≠ Ψ (ncommVec lab Y y)) ∧
    ∀ u : fixedL, (u ≠ 0 ∧ ∀ f : setStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨f, f.2.1⟩)) u = u) ↔ u = cliqueFixedVec Φ Ψ := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  exact ⟨H.finrank_span_cliqueVecs hΦ hΨ, H.fixed_setStab_eq hΦ hroot hΨ,
    H.cliqueFixedVec_ne_zero hΦ hΨ, H.bijective_gramComb hΦ,
    by rw [H.cliqueFixedVec_eq hΦ hΨ, H.gramVec_eq hΦ], H.cliqueFixedVec_ne hΦ hΨ,
    H.eq_cliqueFixedVec_iff hΦ hroot hΨ⟩

theorem cliqueFixedVec_eq_of
    (hS : IsFischerSlice act lab Y) {C : Set V}
    (hC : IsSliceMaxClique lab Y C) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]
    {x x' : V} (hx : x ∈ hexadFiber lab Y C ∅) (hx' : x' ∈ hexadFiber lab Y C ∅)
    {η η' : C ≃ X₀}
    {θ θ' : setStab act lab Y C ⧸ (ptStab act lab Y C).subgroupOf (setStab act lab Y C) ≃*
      CFSG.Blueprint.NativeSporadic.M22}
    (hη : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η z : Fin 24)) ∈ ℬ₀)
    (hη' : ∀ T : Finset C, Subtype.val '' (T : Set C) ∈ cliqueBlocks lab C ↔
      T.image (fun z => (η' z : Fin 24)) ∈ ℬ₀)
    (hθ : ∀ (f : setStab act lab Y C) (z : C),
      (η (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ f) (η z))
    (hθ' : ∀ (f : setStab act lab Y C) (z : C),
      (η' (setStabPerm act lab Y C f z) : Fin 24) = psiHom (θ' f) (η' z))
    {φ φ' : Additive (Subgroup.closure (lab '' C)) ≃ₗ[ZMod 2] W₀}
    (hφ : ∀ z : C, φ (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η z)))
    (hφ' : ∀ z : C, φ' (Additive.ofMul (cliqueGen z)) = K₀.mkQ (e (η' z)))
    {α α' : setStab act lab Y C →* F₀}
    (hα : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x = x → α f = wF (φ (Additive.ofMul r)) * kF (θ k))
    (hα' : ∀ (r : Subgroup.closure (lab '' C)) (f k : setStab act lab Y C),
      (f : S) = r * k → act (k : S) x' = x' → α' f = wF (φ' (Additive.ofMul r)) * kF (θ' k))
    {Φ Φ' : Y ≃ CFSG.Monster.B.Fischer.Y} (hΦ : IsCliqueIntertwiner act lab Y C x η φ α Φ)
    (hΦ' : IsCliqueIntertwiner act lab Y C x' η' φ' α' Φ')
    {ρ : sliceGroup lab Y →* stdGroup}
    (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
    {Ψ : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL} (hΨ : ∀ y : Y, Ψ (ncommVec lab Y y) = adjVec ρ y) :
    cliqueFixedVec Φ' Ψ = cliqueFixedVec Φ Ψ := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  have H' := FullIntertwinerHyp.mk hS hC hx' hη' hθ' hφ' hα'
  exact (H.eq_cliqueFixedVec_iff hΦ hroot hΨ _).1
    ((H'.eq_cliqueFixedVec_iff hΦ' hroot hΨ _).2 rfl)

theorem clique_radical_fixed_space_rank_sieve
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
    {u : fixedL | ∀ r : ptStab act lab Y C,
        actStar (SemidirectProduct.inl (ρ ⟨r, r.2.1⟩)) u = u} =
      Submodule.span (ZMod 2) (cliqueVecs Ψ C) ∧
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (cliqueVecs Ψ C)) = 11 ∧
    ((Submodule.span (ZMod 2) (cliqueVecs Ψ C) : Set fixedL)).ncard = 2048 ∧
    (∀ u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C),
      ∃! t : Fin 8, u ∈ fOrbit act C ρ
        (gramVec Φ Ψ ((![0, 1, 3, 7, 39, 117, 437, 949] : Fin 8 → ℕ) t))) ∧
    (∀ t : Fin 8,
      (fOrbit act C ρ (gramVec Φ Ψ ((![0, 1, 3, 7, 39, 117, 437, 949] : Fin 8 → ℕ) t))).ncard =
          (![1, 22, 231, 770, 770, 231, 22, 1] : Fin 8 → ℕ) t ∧
        ∀ u ∈ fOrbit act C ρ (gramVec Φ Ψ ((![0, 1, 3, 7, 39, 117, 437, 949] : Fin 8 → ℕ) t)),
          Module.finrank (ZMod 2) (LinearMap.range (adL u)) =
            (![0, 22, 32, 38, 38, 32, 22, 22] : Fin 8 → ℕ) t) ∧
    fOrbit act C ρ (gramVec Φ Ψ 1) = cliqueVecs Ψ C ∧
    fOrbit act C ρ (gramVec Φ Ψ 437) = (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∧
    fOrbit act C ρ (gramVec Φ Ψ 949) = {cliqueFixedVec Φ Ψ} ∧
    {u | u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C) ∧
        Module.finrank (ZMod 2) (LinearMap.range (adL u)) = 22} =
      cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∪ {cliqueFixedVec Φ Ψ} ∧
    Disjoint (cliqueVecs Ψ C) ((cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C) ∧
    cliqueFixedVec Φ Ψ ∉ cliqueVecs Ψ C ∪ (cliqueFixedVec Φ Ψ + ·) '' cliqueVecs Ψ C ∧
    {u | u ∈ Submodule.span (ZMod 2) (cliqueVecs Ψ C) ∧
        Module.finrank (ZMod 2) (LinearMap.range (adL u)) = 22}.ncard = 45 ∧
    {y : Y | bracketL (cliqueFixedVec Φ Ψ) (Ψ (ncommVec lab Y y)) = 0} = {y : Y | (y : V) ∈ C} ∧
    ∀ y₀ : Y, (y₀ : V) ∈ C →
      {y : Y | bracketL (cliqueFixedVec Φ Ψ + Ψ (ncommVec lab Y y₀)) (Ψ (ncommVec lab Y y)) = 0} =
        {y : Y | (y : V) ∈ C} := by
  have H := FullIntertwinerHyp.mk hS hC hx hη hθ hφ hα
  refine ⟨H.fixed_ptStab_eq hΦ hroot hΨ, H.finrank_span_cliqueVecs hΦ hΨ,
    H.ncard_span_cliqueVecs hΦ hΨ, H.existsUnique_fOrbit hΦ hroot hΨ,
    H.ncard_rank_fOrbit hΦ hρ hroot hΨ, H.fOrbit_one hΦ hroot hΨ, H.fOrbit_six hΦ hroot hΨ,
    H.fOrbit_seven hΦ hroot hΨ, H.rank22_eq hΦ hρ hroot hΨ, H.disjoint_cliqueShift hΦ hroot hΨ,
    H.cliqueFixedVec_not_mem hΦ hroot hΨ, ?_, ?_, fun y₀ hy₀ => ?_⟩
  · rw [H.rank22_eq hΦ hρ hroot hΨ]
    exact H.ncard_rank22 hΦ hroot hΨ
  · ext y
    exact H.bracketL_cliqueFixedVec_eq_zero_iff hΦ hρ hroot hΨ y
  · ext y
    exact H.bracketL_cliqueFixedVec_add_eq_zero_iff hΦ hρ hroot hΨ hy₀ y

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
