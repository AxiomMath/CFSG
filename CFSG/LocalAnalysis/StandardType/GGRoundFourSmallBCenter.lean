module

public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeNbr
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGLayerCenterCyclic (p : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    (∀ S : Subgroup L', S ≤ Subgroup.center L' → IsPGroup p S → IsCyclic S) →
    ∀ a : MulAut L', a ≠ 1 → a ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
      ∀ S : Subgroup L', S ≤ LargeEvenLayer (ggFix a) →
        S ≤ Subgroup.centralizer (LargeEvenLayer (ggFix a) : Set L') → IsPGroup p S → IsCyclic S

@[expose] def GGLayerCenterCyclicInput : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab →
    LargeEvenSplit p lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGLayerCenterCyclic p R I)

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_of_le_center_of_sstar {p : ℕ} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L) (S : Subgroup L) (hSZ : S ≤ Subgroup.center L)
    (hSp : IsPGroup p S) : IsCyclic S := by
  have hmap : S.map L.subtype ≤ Subgroup.centralizer (L : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp (hSZ hs)) ⟨l, hl⟩)
  have hcyc : IsCyclic (S.map L.subtype) := hS.2.2.2.2 _ hmap (hSp.map L.subtype)
  set e := S.equivMapOfInjective L.subtype L.subtype_injective
  exact isCyclic_of_surjective e.symm e.symm.surjective

theorem ggStdSubCenterCyclicInput_of_labels (h : GGLayerCenterCyclicInput) :
    GGStdSubCenterCyclicInput := by
  intro G _ _ p B x L D J hI hDJ S hSJ hSC hSp
  have hI0 := hI
  obtain ⟨-, -, -, -, -, hβ, hS, hst⟩ := hI
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have := Fact.mk hp
  have hM := largeEvenMarking_and_labelAll (S := fun lab => LargeEvenSplit p lab)
    (fun lab hlab hs => h p lab hp hp2 hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hst.1
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, hsimple, hnab, θ, ⟨-, hBN, h3⟩, hcen⟩ := largeEvenRawDatum_exists hraw
  have hLC : GGLayerCenterCyclic p R I := hcen hsimple hnab
  have hxB : x ∈ B := hS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  obtain ⟨y, hyD, hyx⟩ : ∃ y ∈ D, y ∉ Subgroup.zpowers x := by
    by_contra hcon
    have hle := Subgroup.card_le_of_le (show D ≤ Subgroup.zpowers x from fun y hy => by
      by_contra hy'
      exact hcon ⟨y, hy, hy'⟩)
    rw [hDJ.1.2.2.1, Nat.card_zpowers, orderOf_eq_prime (hS.1.1.2 x hxB) hS.2.2.1] at hle
    have hlt : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact absurd hle (not_le.mpr hlt)
  have hyB : y ∈ B := hDJ.1.1 hyD
  set a := ggGamma L hBN ⟨y, hyB⟩ with ha
  have ha1 : a ≠ 1 := by
    intro ha1
    apply hyx
    rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
    exact ⟨hyB, (ggGamma_eq_one_iff L hBN _).mp ha1⟩
  have hap : a ^ p = 1 := by
    have hyp : (⟨y, hyB⟩ : B) ^ p = 1 := Subtype.ext (by simpa using hS.1.1.2 y hyB)
    rw [ha, ← map_pow, hyp, map_one]
  have hind : ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) :=
    ⟨ggBeta L θ hBN ⟨y, hyB⟩, ggBeta_mem L θ hBN h3 _, fun l => ggBeta_ggQuotHom L hBN θ _ l⟩
  have hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    rw [eq_closure_pair_of_mem hI0 hDJ hyD hyx, Set.insert_eq, Subgroup.closure_union,
      Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  have hfix : (ggFix a).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hD, inf_centralizer_sup_zpowers hLx]
    exact map_ggFix_ggGamma L hBN ⟨y, hyB⟩
  have hJ : J = (LargeEvenLayer (ggFix a)).map L.subtype := by
    rw [hDJ.1.2.2.2.2.1, ← hfix, largeEvenLayer_map_of_injective _ L.subtype_injective]
  have hcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) := by
    have h1 := hDJ.1.2.2.2.2.2.1
    rw [hJ, ← hfix] at h1
    have h2 := (isComponentOf_comap_of_injective _ L.subtype_injective h1).1
    rwa [Subgroup.comap_map_eq_self_of_injective L.subtype_injective] at h2
  have hJL : J ≤ L := by
    rw [hJ]
    exact Subgroup.map_subtype_le _
  set S' : Subgroup L := S.comap L.subtype with hS'
  have hS'map : S'.map L.subtype = S :=
    Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hSJ.trans hJL)
  have hS'J : S' ≤ LargeEvenLayer (ggFix a) := by
    intro s hs
    have hsJ : (s : G) ∈ J := hSJ hs
    rw [hJ] at hsJ
    obtain ⟨t, ht, hts⟩ := hsJ
    rwa [← L.subtype_injective hts]
  have hS'C : S' ≤ Subgroup.centralizer (LargeEvenLayer (ggFix a) : Set L) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    have htJ : (t : G) ∈ J := by
      rw [hJ]
      exact ⟨t, ht, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hSC hs) _ htJ
  have hS'p : IsPGroup p S' := hSp.comap_of_injective L.subtype L.subtype_injective
  have hcyc : IsCyclic S' := hLC L (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hL (isCyclic_of_le_center_of_sstar hS) a ha1 hap hind hcomp S'
    hS'J hS'C hS'p
  rw [← hS'map]
  set e := S'.equivMapOfInjective L.subtype L.subtype_injective
  exact isCyclic_of_surjective e e.surjective

end Reduction

end CFSG.StandardType

end
