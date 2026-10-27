module

public import CFSG.LocalAnalysis.StandardType.GGSixJNotA6KnownDefs
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpRank
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.Quasithin.Background.SimsD1TransGrp
import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType.A6InsideSp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

open CFSG.Quasithin.SimsD1.TransGrp (map_inf_centralizer_eq isElemAbelian_map_iff
  isPGroup_map_iff le_normalizer_map_iff)
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_map_iff)

theorem largeEvenLayer_map {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) (H : Subgroup G) :
    LargeEvenLayer (H.map f) = (LargeEvenLayer H).map f := by
  have hset : {K : Subgroup G' | IsComponentOf K (H.map f)} =
      Subgroup.map f '' {K : Subgroup G | IsComponentOf K H} := by
    ext K
    constructor
    · intro hK
      have hmap : (K.comap f).map f = K :=
        Subgroup.map_comap_eq_self (hK.1.trans (Subgroup.map_le_range f H))
      exact ⟨K.comap f, (isComponentOf_map_iff hf (Q := K.comap f) (K := H)).mp (by
        rwa [hmap]), hmap⟩
    · rintro ⟨Q, hQ, rfl⟩
      exact (isComponentOf_map_iff hf).mpr hQ
  unfold LargeEvenLayer
  rw [hset]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro K ⟨Q, hQ, rfl⟩
    exact Subgroup.map_mono (le_sSup hQ)
  · rw [sSup_eq_iSup]
    simp_rw [Subgroup.map_iSup]
    refine iSup_le fun Q => iSup_le fun hQ => ?_
    exact le_sSup ⟨Q, hQ, rfl⟩

theorem largeEvenStdSubPre_map_iff {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) (p : ℕ) (B L D K : Subgroup G) (x : G) :
    LargeEvenStdSubPre p (B.map f) (f x) (L.map f) (D.map f) (K.map f) ↔
      LargeEvenStdSubPre p B x L D K := by
  unfold LargeEvenStdSubPre
  rw [← map_inf_centralizer_eq f hf L D,
    largeEvenLayer_map hf (L ⊓ Subgroup.centralizer (D : Set G)),
    ← map_inf_centralizer_eq f hf B K,
    Subgroup.map_le_map_iff_of_injective hf,
    isElemAbelian_map_iff f hf p D,
    Subgroup.card_map_of_injective hf,
    Subgroup.mem_map_iff_mem hf,
    (Subgroup.map_injective hf).eq_iff,
    isComponentOf_map_iff hf,
    (Subgroup.map_injective hf).eq_iff]

theorem largeEvenSmall_map_iff {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Injective f) (K : Subgroup G) : LargeEvenSmall (K.map f) ↔ LargeEvenSmall K := by
  unfold LargeEvenSmall LargeEvenIsU42
  constructor
  · intro hsmall
    rcases hsmall with ⟨F, hF, hFin, hcard, ⟨e'⟩⟩ | hne
    · exact Or.inl ⟨F, hF, hFin, hcard, ⟨(K.equivMapOfInjective f hf).trans e'⟩⟩
    · obtain ⟨e'⟩ := hne
      exact Or.inr ⟨(K.equivMapOfInjective f hf).trans e'⟩
  · intro hsmall
    rcases hsmall with ⟨F, hF, hFin, hcard, ⟨e'⟩⟩ | hne
    · exact Or.inl ⟨F, hF, hFin, hcard, ⟨(K.equivMapOfInjective f hf).symm.trans e'⟩⟩
    · obtain ⟨e'⟩ := hne
      exact Or.inr ⟨(K.equivMapOfInjective f hf).symm.trans e'⟩

@[expose] def Core : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ), Nat.card K = 2 → 5 ≤ n →
    ∀ (B L D J : Subgroup (StatedSp n K)) (x : StatedSp n K),
      IsElemAbelian 3 B → 3 ^ 4 ≤ Nat.card B →
      IsComponentOf L (Subgroup.centralizer {x}) → x ≠ 1 →
      (∀ S : Subgroup (StatedSp n K), S ≤ Subgroup.centralizer (L : Set (StatedSp n K)) →
        IsPGroup 3 S → IsCyclic S) →
      LargeEvenStdSubPre 3 B x L D J → Nonempty (↥J ≃* alternatingGroup (Fin 6)) →
        (∃ D₁ K₁ : Subgroup (StatedSp n K), LargeEvenStdSubPre 3 B x L D₁ K₁ ∧
            ¬ LargeEvenSmall K₁) ∨
          ∀ U : Subgroup (StatedSp n K), U ≤ L → IsPGroup 2 U →
            B ≤ Subgroup.normalizer (U : Set (StatedSp n K)) → U = ⊥

theorem ggSixA6InsideSpKnown_of_core (h : Core) : GGSixA6InsideSpKnown := by
  intro X _ _ n G₀ B L D J x hn hX hZ hBG hBe hB4 hLG hLc hx1 hcyc hpre hA6
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hX.statedClassicalModel (by decide)
  have hK2 : Nat.card K = 2 := by simpa using hK
  haveI : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two le_rfl hK
  haveI : NeZero n := ⟨by omega⟩
  let eR : ↥G₀ ≃* LargeEvenProj (LargeEvenSpGroup K n) :=
    ((QuotientGroup.quotientBot.symm).trans
      (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans e
  let e₀ : ↥G₀ ≃* CFSG.Open.StatedSp n K := eR.trans TableBSymp.spProjEquivSp
  let ι : CFSG.Open.StatedSp n K →* X := G₀.subtype.comp e₀.symm.toMonoidHom
  have hι_inj : Function.Injective ι := G₀.subtype_injective.comp e₀.symm.injective
  have hι_range : ι.range = G₀ := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (e₀.symm z).2
    · intro hy
      exact ⟨e₀ ⟨y, hy⟩, by simp [ι]⟩
  rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with hn4 | hn5
  · right
    intro U hUL hU2 hBN
    by_contra hU
    have hUG : U ≤ G₀ := hUL.trans hLG
    let B' : Subgroup ↥G₀ := B.subgroupOf G₀
    let U' : Subgroup ↥G₀ := U.subgroupOf G₀
    let A : Subgroup (LargeEvenProj (LargeEvenSpGroup K n)) := B'.map eR.toMonoidHom
    let V : Subgroup (LargeEvenProj (LargeEvenSpGroup K n)) := U'.map eR.toMonoidHom
    have hBmap : B'.map G₀.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBG
    have hUmap : U'.map G₀.subtype = U := Subgroup.map_subgroupOf_eq_of_le hUG
    have hB'el : IsElemAbelian 3 B' :=
      (isElemAbelian_map_iff G₀.subtype G₀.subtype_injective 3 B').mp (by rwa [hBmap])
    have hAel : IsElemAbelian 3 A :=
      (isElemAbelian_map_iff eR.toMonoidHom eR.injective 3 B').mpr hB'el
    have hU'ne : U' ≠ ⊥ := fun hbot => hU (by rw [← hUmap, hbot, Subgroup.map_bot])
    have hVne : V ≠ ⊥ := fun hbot =>
      hU'ne ((Subgroup.map_eq_bot_iff_of_injective U' eR.injective).mp hbot)
    have hU'2 : IsPGroup 2 U' :=
      (isPGroup_map_iff G₀.subtype G₀.subtype_injective 2 U').mp (by rwa [hUmap])
    have hV2 : IsPGroup 2 V :=
      (isPGroup_map_iff eR.toMonoidHom eR.injective 2 U').mpr hU'2
    have hB'N : B' ≤ Subgroup.normalizer (U' : Set ↥G₀) := by
      rw [← le_normalizer_map_iff G₀.subtype G₀.subtype_injective B' U', hBmap, hUmap]
      exact hBN
    have hAV : A ≤ Subgroup.normalizer (V : Set (LargeEvenProj (LargeEvenSpGroup K n))) := by
      dsimp only [A, V]
      rw [le_normalizer_map_iff eR.toMonoidHom eR.injective B' U']
      exact hB'N
    have hcardA : Nat.card A = Nat.card B := by
      rw [Subgroup.card_map_of_injective eR.injective,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv]
    have hle := SmallRule.card_le_sp_normalizes_two hK2 hAel hVne hV2
      (fun a ha v hv => (Subgroup.mem_normalizer_iff.mp (hAV ha) v).mp hv)
    rw [hcardA] at hle
    have h3 : 3 ^ (n - 1) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h27 : Nat.card B ≤ 27 := hle.trans (by simpa using h3)
    have h81 : 81 ≤ Nat.card B := by simpa using hB4
    omega
  · have hxG : x ∈ G₀ := hBG (hpre.1 hpre.2.2.2.1)
    have hJG : J ≤ G₀ := (hpre.2.2.2.2.2.1.1.trans inf_le_left).trans hLG
    let x' : CFSG.Open.StatedSp n K := e₀ ⟨x, hxG⟩
    let B' : Subgroup (CFSG.Open.StatedSp n K) := B.comap ι
    let L' : Subgroup (CFSG.Open.StatedSp n K) := L.comap ι
    let D' : Subgroup (CFSG.Open.StatedSp n K) := D.comap ι
    let J' : Subgroup (CFSG.Open.StatedSp n K) := J.comap ι
    have hxι : ι x' = x := by simp [x', ι]
    have hBmap : B'.map ι = B := Subgroup.map_comap_eq_self (by rw [hι_range]; exact hBG)
    have hLmap : L'.map ι = L := Subgroup.map_comap_eq_self (by rw [hι_range]; exact hLG)
    have hDmap : D'.map ι = D :=
      Subgroup.map_comap_eq_self (by rw [hι_range]; exact hpre.1.trans hBG)
    have hJmap : J'.map ι = J := Subgroup.map_comap_eq_self (by rw [hι_range]; exact hJG)
    have hB'el : IsElemAbelian 3 B' :=
      (isElemAbelian_map_iff ι hι_inj 3 B').mp (by rwa [hBmap])
    have hB'4 : 3 ^ 4 ≤ Nat.card B' := by
      rw [← Subgroup.card_map_of_injective hι_inj (K := B'), hBmap]
      exact hB4
    have hczx : Subgroup.centralizer (Subgroup.zpowers x : Set X) =
        Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hczx' : Subgroup.centralizer (Subgroup.zpowers x' : Set (CFSG.Open.StatedSp n K)) =
        Subgroup.centralizer ({x'} : Set (CFSG.Open.StatedSp n K)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hCmap : G₀ ⊓ Subgroup.centralizer ({x} : Set X) =
        (Subgroup.centralizer ({x'} : Set (CFSG.Open.StatedSp n K))).map ι := by
      have h := map_inf_centralizer_eq ι hι_inj (⊤ : Subgroup (CFSG.Open.StatedSp n K))
        (Subgroup.zpowers x')
      rw [Subgroup.map_top, top_inf_eq, MonoidHom.map_zpowers, hxι, hczx', hczx] at h
      rw [← hι_range, h]
    have hLc' : IsComponentOf L' (Subgroup.centralizer ({x'} : Set (CFSG.Open.StatedSp n K))) := by
      rw [← isComponentOf_map_iff hι_inj (Q := L')
        (K := Subgroup.centralizer ({x'} : Set (CFSG.Open.StatedSp n K)))]
      rw [hLmap, ← hCmap]
      exact hLc
    have hx'1 : x' ≠ 1 := by
      intro hx'
      exact hx1 (by rw [← hxι, hx', map_one])
    have hcyc' : ∀ S' : Subgroup (CFSG.Open.StatedSp n K),
        S' ≤ Subgroup.centralizer (L' : Set (CFSG.Open.StatedSp n K)) →
          IsPGroup 3 S' → IsCyclic S' := by
      intro S' hS' hS'3
      have hCL : (Subgroup.centralizer (L' : Set (CFSG.Open.StatedSp n K))).map ι =
          G₀ ⊓ Subgroup.centralizer (L : Set X) := by
        have h := map_inf_centralizer_eq ι hι_inj (⊤ : Subgroup (CFSG.Open.StatedSp n K)) L'
        rw [Subgroup.map_top, top_inf_eq, hLmap, hι_range] at h
        exact h
      have hSmap : S'.map ι ≤ G₀ ⊓ Subgroup.centralizer (L : Set X) := by
        rw [← hCL]
        exact Subgroup.map_mono hS'
      have hSp : IsPGroup 3 (S'.map ι) :=
        (isPGroup_map_iff ι hι_inj 3 S').mpr hS'3
      exact (S'.equivMapOfInjective ι hι_inj).isCyclic.mpr (hcyc (S'.map ι) hSmap hSp)
    have hpre' : LargeEvenStdSubPre 3 B' x' L' D' J' := by
      rw [← largeEvenStdSubPre_map_iff hι_inj (p := 3) (B := B') (x := x') (L := L')
        (D := D') (K := J')]
      rw [hBmap, hxι, hLmap, hDmap, hJmap]
      exact hpre
    have hA6' : Nonempty (↥J' ≃* alternatingGroup (Fin 6)) := by
      obtain ⟨e6⟩ := hA6
      refine ⟨(J'.equivMapOfInjective ι hι_inj).trans ?_⟩
      rwa [hJmap]
    have hmain := h K n hK2 hn5 B' L' D' J' x' hB'el hB'4 hLc' hx'1 hcyc' hpre' hA6'
    rcases hmain with ⟨D₁', K₁', hpre₁, hsmall₁⟩ | hU'
    · left
      refine ⟨D₁'.map ι, K₁'.map ι, ?_, ?_⟩
      · have h := (largeEvenStdSubPre_map_iff hι_inj (p := 3) (B := B') (x := x') (L := L')
          (D := D₁') (K := K₁')).mpr hpre₁
        rwa [hBmap, hxι, hLmap] at h
      · rwa [largeEvenSmall_map_iff hι_inj K₁']
    · right
      intro U hUL hU2 hBN
      let U' : Subgroup (CFSG.Open.StatedSp n K) := U.comap ι
      have hUmap : U'.map ι = U :=
        Subgroup.map_comap_eq_self (by rw [hι_range]; exact hUL.trans hLG)
      have hU'L' : U' ≤ L' := fun y hy => hUL hy
      have hU'2 : IsPGroup 2 U' :=
        (isPGroup_map_iff ι hι_inj 2 U').mp (by rwa [hUmap])
      have hB'N : B' ≤ Subgroup.normalizer (U' : Set (CFSG.Open.StatedSp n K)) := by
        rw [← le_normalizer_map_iff ι hι_inj B' U', hBmap, hUmap]
        exact hBN
      have hbot : U' = ⊥ := hU' U' hU'L' hU'2 hB'N
      rw [← hUmap, hbot, Subgroup.map_bot]

end CFSG.StandardType.A6InsideSp
