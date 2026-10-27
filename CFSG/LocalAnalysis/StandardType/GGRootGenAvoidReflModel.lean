module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenAvoidKG
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidInduced
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenCover
public import CFSG.RankThree.CentralCover.SteinbergBNReflectionNormalizers
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.Tools
public import CFSG.Walter.PSL2Facts
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

theorem exists_mulAut_conj_of_mem {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {I : Set (MulAut R)}
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∀ a ∈ A, ∃ l : L', a = MulAut.conj l := by
  intro a ha
  obtain ⟨φ, hφI, hφa⟩ := hAI a ha
  have hap : a ^ p = 1 := hA.2 a ha
  have hφp : φ ^ p = 1 := by
    ext g
    obtain ⟨l, rfl⟩ := hψ g
    have h1 := TypeA.induced_pow ψ hφa p l
    rw [hap] at h1
    simpa using h1
  obtain ⟨g, hg⟩ := hI φ hφI hφp
  obtain ⟨l, rfl⟩ := hψ g
  refine ⟨l, ?_⟩
  refine TypeA.mulAut_eq_of_forall ψ hker hperf (fun x => ?_)
  rw [← hφa x, ← hg]
  calc MulAut.conj (ψ l) (ψ x) = ψ l * ψ x * (ψ l)⁻¹ := by rw [MulAut.conj_apply]
    _ = ψ (l * x * l⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = ψ ((MulAut.conj l) x) := by rw [MulAut.conj_apply]

theorem inducedSub_eq_map_mulAut_conj {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} (hψ : Function.Surjective ψ) {A : Subgroup (MulAut L')}
    (hinn : ∀ a ∈ A, ∃ l : L', a = MulAut.conj l) :
    TypeA.inducedSub ψ A =
      ((A.comap (MulAut.conj : L' →* MulAut L')).map ψ).map
        (MulAut.conj : R →* MulAut R) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
    obtain ⟨l, rfl⟩ := hinn a ha
    have hφeq : φ = MulAut.conj (ψ l) := by
      ext r
      obtain ⟨l', rfl⟩ := hψ r
      rw [hφa l', MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
    rw [hφeq]
    exact Subgroup.mem_map_of_mem (MulAut.conj : R →* MulAut R)
      (Subgroup.mem_map_of_mem ψ (Subgroup.mem_comap.mpr ha))
  · intro hφ
    rw [Subgroup.mem_map] at hφ
    obtain ⟨g, hg, rfl⟩ := hφ
    rw [Subgroup.mem_map] at hg
    obtain ⟨l, hl, rfl⟩ := hg
    rw [Subgroup.mem_comap] at hl
    exact TypeA.mem_inducedSub.mpr ⟨MulAut.conj l, hl, fun l' => by
      rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]⟩

private theorem centralizer_map_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (X : Set G) :
    (Subgroup.centralizer X).map e.toMonoidHom = Subgroup.centralizer (e '' X) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ Subgroup.centralizer X at hx
    rw [Subgroup.mem_centralizer_iff] at hx
    change e x ∈ Subgroup.centralizer (e '' X)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [← map_mul, ← map_mul, hx w hw]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change e.symm y ∈ Subgroup.centralizer X
    rw [Subgroup.mem_centralizer_iff]
    change y ∈ Subgroup.centralizer (e '' X) at hy
    rw [Subgroup.mem_centralizer_iff] at hy
    intro w hw
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hy (e w) ⟨w, hw, rfl⟩

theorem ggTorusRootGenAvoidKG_of_reflTorusModel {p k r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {I : Set (MulAut G)}
    (hZ : Subgroup.center G = ⊥)
    (hI : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : G →* MulAut G))
    (hrefl : GGTorusReflElt p r G)
    (T : Multiplicative (Fin k → ZMod p) →* G) (hT : Function.Injective T)
    (hconj : ∀ E : Subgroup G, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
      ∃ α : G ≃* G, E = T.range.map α.toMonoidHom)
    {ι : Type} [Nonempty ι] (w : ι → G) (f : ι → (Fin k → ZMod p) → Fin k → ZMod p)
    (S : ι → Subgroup G)
    (hw : ∀ i t, w i * T (ofAdd t) * (w i)⁻¹ = T (ofAdd (f i t)))
    (hinv : ∀ i t, f i (f i t) = t)
    (hfix : ∀ i, Nat.card {t // f i t = t} * p = p ^ k)
    (hwS : ∀ i, w i ∈ S i)
    (hcomp : ∀ i, IsComponentOf (S i)
      (Subgroup.centralizer (SuSplitRootGen.torusFix T (f i))))
    (hdvd : ∀ i, p ∣ Nat.card (S i))
    (hgen : ∀ j, (⨆ (i : ι) (_ : f i ≠ f j), S i) = ⊤) :
    GGTorusRootGenAvoidKG p r G I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 _hsc
  have hinn : ∀ a ∈ A, ∃ l : L', a = MulAut.conj l :=
    exists_mulAut_conj_of_mem hψ hker hperf hI hA hAI
  let E : Subgroup G := (A.comap (MulAut.conj : L' →* MulAut L')).map ψ
  have hconjmap : TypeA.inducedSub ψ A = E.map (MulAut.conj : G →* MulAut G) :=
    inducedSub_eq_map_mulAut_conj hψ hinn
  have hZconj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    intro x y hxy
    have h1 : MulAut.conj (x⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one h1
    rw [hZ, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  have hEea : IsElemAbelian p E := by
    have hR : IsElemAbelian p (E.map (MulAut.conj : G →* MulAut G)) := by
      rw [← hconjmap]
      exact TypeA.isElemAbelian_inducedSub hψ hA
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hZconj
      have hx' : MulAut.conj (x : G) ∈ E.map (MulAut.conj : G →* MulAut G) :=
        Subgroup.mem_map_of_mem _ x.2
      have hy' : MulAut.conj (y : G) ∈ E.map (MulAut.conj : G →* MulAut G) :=
        Subgroup.mem_map_of_mem _ y.2
      have hcomm : MulAut.conj (x : G) * MulAut.conj (y : G) =
          MulAut.conj (y : G) * MulAut.conj (x : G) := by
        haveI : IsMulCommutative ↥(E.map (MulAut.conj : G →* MulAut G)) := hR.1
        exact congrArg Subtype.val (mul_comm' (⟨MulAut.conj (x : G), hx'⟩ :
          E.map (MulAut.conj : G →* MulAut G)) ⟨MulAut.conj (y : G), hy'⟩)
      calc MulAut.conj ((x : G) * (y : G))
          = MulAut.conj (x : G) * MulAut.conj (y : G) := map_mul _ _ _
        _ = MulAut.conj (y : G) * MulAut.conj (x : G) := hcomm
        _ = MulAut.conj ((y : G) * (x : G)) := (map_mul _ _ _).symm
    · have hx' : MulAut.conj (x : G) ∈ E.map (MulAut.conj : G →* MulAut G) :=
        Subgroup.mem_map_of_mem _ hx
      have hxp : (MulAut.conj (x : G)) ^ p = 1 := hR.2 (MulAut.conj x) hx'
      have hconjxp : MulAut.conj ((x : G) ^ p) = 1 := by
        rw [map_pow]
        exact hxp
      have hcenter := CFSG.InnerNormalizedAutomorphisms.mem_center_of_conj_eq_one hconjxp
      have hpow : (x : G) ^ p = 1 := by
        rw [hZ] at hcenter
        simpa using hcenter
      exact hpow
  have hEcard : Nat.card E = Nat.card A := by
    calc Nat.card E = Nat.card (E.map (MulAut.conj : G →* MulAut G)) :=
          (Subgroup.card_map_of_injective hZconj).symm
      _ = Nat.card (TypeA.inducedSub ψ A) := by rw [← hconjmap]
      _ = Nat.card A := TypeA.card_inducedSub hψ hker hperf (A := A) (fun a ha => by
            obtain ⟨φ, -, hφa⟩ := hAI a ha
            exact ⟨φ, hφa⟩)
  have hrE : p ^ r ≤ Nat.card E := by rw [hEcard]; exact hr
  have h3E : p ^ 3 ≤ Nat.card E := by rw [hEcard]; exact h3
  have hcomm : ∀ x y : L', MulAut.conj x ∈ A → MulAut.conj y ∈ A → x * y = y * x := by
    intro x y hx hy
    obtain ⟨d, e, c, n, heE, hc, hn, -⟩ := hrefl E hEea hrE h3E
    have hxE : ψ x ∈ E := Subgroup.mem_map_of_mem ψ (Subgroup.mem_comap.mpr hx)
    have hyE : ψ y ∈ E := Subgroup.mem_map_of_mem ψ (Subgroup.mem_comap.mpr hy)
    have hx' : x ∈ e.range.comap ψ := Subgroup.mem_comap.mpr (heE.symm ▸ hxE)
    have hy' : y ∈ e.range.comap ψ := Subgroup.mem_comap.mpr (heE.symm ▸ hyE)
    exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker hp hp2 e c hc n hn
      x hx' y hy'
  let A_R : Subgroup (MulAut G) := TypeA.inducedSub ψ A
  have hconjmap' : A_R = E.map (MulAut.conj : G →* MulAut G) := hconjmap
  have hAR : GGTorusRootGenAvoid p A_R := by
    obtain ⟨α, hEα⟩ := hconj E hEea hrE h3E
    let τ : Multiplicative (Fin k → ZMod p) →* G := α.toMonoidHom.comp T
    have hτrange : τ.range = E := by
      change (α.toMonoidHom.comp T).range = E
      rw [MonoidHom.range_comp]
      exact hEα.symm
    have hM : SuSplitRootGen.IsCoverTorusModel (MonoidHom.id G) τ A_R := by
      intro a
      rw [hconjmap']
      constructor
      · intro ha
        rw [Subgroup.mem_map] at ha
        obtain ⟨g, hg, hga⟩ := ha
        have hg' : g ∈ τ.range := hτrange.symm ▸ hg
        obtain ⟨t, hgt⟩ := MonoidHom.mem_range.mp hg'
        refine ⟨t, ?_⟩
        rw [← hga, ← hgt]
        rfl
      · rintro ⟨t, rfl⟩
        rw [Subgroup.mem_map]
        refine ⟨τ t, ?_, rfl⟩
        rw [← hτrange]
        exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
    have hτc : ∀ t, (MonoidHom.id G) (τ t) ∈ Subgroup.center G → t = 1 := by
      intro t ht
      have h1 : τ t = 1 := by simpa [hZ] using ht
      have h2 : T t = 1 := by
        apply α.injective
        simpa [τ] using h1
      exact hT (h2.trans (map_one T).symm)
    have hw' : ∀ i t, α (w i) * τ (ofAdd t) * (α (w i))⁻¹ = τ (ofAdd (f i t)) := by
      intro i t
      have h := congrArg (fun x => α x) (hw i t)
      simpa [τ, map_mul, map_inv] using h
    have htorus : ∀ i, SuSplitRootGen.torusFix τ (f i) =
        α '' SuSplitRootGen.torusFix T (f i) := by
      intro i
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨T t, ⟨t, ht, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨t, ht, rfl⟩
    have hcomp' : ∀ i, IsComponentOf ((S i).map α.toMonoidHom)
        (Subgroup.centralizer (SuSplitRootGen.torusFix τ (f i))) := by
      intro i
      have hcompO : CFSG.Open.IsComponentOf (S i)
          (Subgroup.centralizer (SuSplitRootGen.torusFix T (f i))) :=
        CFSG.Assembly.isComponentOf_iff_open.mp (hcomp i)
      rw [htorus i, ← centralizer_map_mulEquiv α (SuSplitRootGen.torusFix T (f i))]
      exact CFSG.Assembly.isComponentOf_iff_open.mpr (isComponentOf_map_mulEquiv α hcompO)
    have hdvd' : ∀ i, p ∣ Nat.card ((S i).map α.toMonoidHom) := by
      intro i
      rw [Subgroup.card_map_of_injective α.injective]
      exact hdvd i
    have hgen' : ∀ j, (⨆ (i : ι) (_ : f i ≠ f j), (S i).map α.toMonoidHom) = ⊤ := by
      intro j
      rw [← Subgroup.map_top_of_surjective α.toMonoidHom α.surjective, ← hgen j]
      simp only [Subgroup.map_iSup]
    exact SuSplitRootGen.ggTorusRootGenAvoid_of_cover (H := G) (L' := G) hp
      (φ := MonoidHom.id G) (τ := τ) (A := A_R)
      (fun x => ⟨x, rfl⟩)
      (fun z hz => by
        have hz1 : z = 1 := by simpa using hz
        rw [hz1]
        exact Subgroup.one_mem _)
      (fun z hz _ => by simpa using hz) hM hτc
      (fun i => α (w i)) f (fun i => (S i).map α.toMonoidHom)
      hw' hinv hfix (fun i => Subgroup.mem_map_of_mem _ (hwS i)) hcomp' hdvd' hgen'
  exact ggTorusRootGenAvoid_of_inducedSub hψ hker hperf hA hinn hcomm hAR

end CFSG.StandardType
