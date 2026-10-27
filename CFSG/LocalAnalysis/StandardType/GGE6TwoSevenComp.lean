module

public import CFSG.LocalAnalysis.StandardType.GGExcTwoCompList
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenLayers
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenLabelA2
public import CFSG.LocalAnalysis.StandardType.GGE6TwoSevenLabelTriD4
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.LocalAnalysis.StandardType.GGTCJCoverGen
public import CFSG.LocalAnalysis.EvenBN.Common.CommutatorFixed
public import CFSG.LocalAnalysis.GLTheoremA.S12.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S12.Prop123

public section

namespace CFSG.StandardType.E6TwoSeven

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private lemma ltqL5_e6_recipe_data {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum (⟨.E6, 0, 1⟩ : LargeEvenLabel) Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      Q (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false))
        (LargeEvenChevIDImage (LargeEvenCartanE 6) K
          (LargeEvenChevH (LargeEvenCartanE 6) K false))
        (LargeEvenChevFieldImage (LargeEvenCartanE 6) K
          (LargeEvenChevH (LargeEvenCartanE 6) K false)) := by
  simpa only [LargeEvenRawDatum, LargeEvenRecipeChevalley, pow_one] using h

private lemma ltqL5_aut_eq_one_of_fix {L' R : Type} [Group L'] [Group R]
    (ψ : L' →* R) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hcomm : commutator L' = ⊤) (e : MulAut L') (he : ∀ l : L', ψ (e l) = ψ l) :
    e = 1 := by
  have hmem : ∀ l : L', l⁻¹ * e l ∈ Subgroup.center L' := by
    intro l
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, he l, inv_mul_cancel]
  let δ : L' →* Subgroup.center L' :=
    { toFun := fun l => ⟨l⁻¹ * e l, hmem l⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show (a * b)⁻¹ * e (a * b) = (a⁻¹ * e a) * (b⁻¹ * e b)
        rw [map_mul, mul_inv_rev]
        calc (b⁻¹ * a⁻¹) * (e a * e b)
            = b⁻¹ * ((a⁻¹ * e a) * e b) := by group
          _ = b⁻¹ * (e b * (a⁻¹ * e a)) := by
                rw [Subgroup.mem_center_iff.1 (hmem a) (e b)]
          _ = (b⁻¹ * e b) * (a⁻¹ * e a) := by group
          _ = (a⁻¹ * e a) * (b⁻¹ * e b) :=
                Subgroup.mem_center_iff.1 (hmem a) (b⁻¹ * e b) }
  have hle : commutator L' ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.1 (δ a).2 (δ b).val).symm
  rw [hcomm] at hle
  have hδtriv : ∀ l : L', δ l = 1 := by
    intro l
    have hl : l ∈ δ.ker := hle (Subgroup.mem_top l)
    rwa [MonoidHom.mem_ker] at hl
  ext l
  have hl : l⁻¹ * e l = 1 := by
    change (δ l).val = 1
    rw [hδtriv l]
    rfl
  exact (inv_mul_eq_one.mp hl).symm

private lemma ltqL5_fixSub_conj_eq_centralizer {R : Type} [Group R] (r : R) :
    ggFixSub (MulAut.conj r) = Subgroup.centralizer ({r} : Set R) := by
  ext l
  rw [mem_ggFixSub, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have h' : r * l = l * r := by
      calc r * l = r * l * r⁻¹ * r := by group
        _ = l * r := by rw [h]
    exact h'.symm
  · intro h
    calc r * l * r⁻¹ = (l * r) * r⁻¹ := by rw [← h]
      _ = l := by group

private lemma ltqL5_centralizer_map {R G : Type} [Group R] [Group G] (e : R ≃* G) (r : R) :
    (Subgroup.centralizer ({r} : Set R)).map e.toMonoidHom =
      Subgroup.centralizer ({e r} : Set G) := by
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    change e.toMonoidHom y * e.toMonoidHom r = e.toMonoidHom r * e.toMonoidHom y
    rw [← map_mul, ← map_mul, hy]
  · intro hz
    rw [Subgroup.mem_map]
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    refine ⟨e.symm z, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hz

private lemma ltqL5_isComponentOf_map {G H : Type} [Group G] [Group H] (e : G ≃* H)
    {K X : Subgroup G} (h : IsComponentOf K X) :
    IsComponentOf (K.map e.toMonoidHom) (X.map e.toMonoidHom) := by
  obtain ⟨hKX, hsub, hperf, hsimple⟩ := h
  refine ⟨Subgroup.map_mono hKX, hsub.map e.toMonoidHom, ?_, ?_⟩
  · exact TCJ.tcjDescent_commutator_map_eq_top hperf e.toMonoidHom
  · let iso : ↥K ≃* ↥(K.map e.toMonoidHom) :=
      Subgroup.equivMapOfInjective K e.toMonoidHom e.injective
    let qiso : (↥K ⧸ Subgroup.center ↥K) ≃*
        (↥(K.map e.toMonoidHom) ⧸ Subgroup.center ↥(K.map e.toMonoidHom)) :=
      QuotientGroup.congr (Subgroup.center ↥K) (Subgroup.center ↥(K.map e.toMonoidHom))
        iso (by
          ext b
          constructor
          · rintro ⟨a, ha, rfl⟩
            exact (mem_center_iff_of_mulEquiv iso a).2 ha
          · intro hb
            exact ⟨iso.symm b,
              (mem_center_iff_of_mulEquiv iso (iso.symm b)).1
                (by rw [iso.apply_symm_apply]; exact hb),
              iso.apply_symm_apply b⟩)
    exact MulEquiv.isSimpleGroup qiso.symm

theorem ggE6TwoSevenComp_holds :
    GGE6TwoSevenComp := by
  classical
  unfold GGE6TwoSevenComp GGCompList LargeEvenLabelAll
  intro Q hQ
  obtain ⟨K, hKfield, hKfin, hKcard, hQK⟩ := ltqL5_e6_recipe_data hQ
  refine ⟨K, hKfield, hKfin, by simpa using hKcard, ?_⟩
  refine ⟨hQK, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e he7 he1 hφex J hJ
  obtain ⟨φ, hφI, hφe⟩ := hφex
  let Qprop : ∀ (X : Type) [Group X], Prop := fun X _ =>
    ∃ labJ : LargeEvenLabel, labJ ∈ [⟨.A, 2, 1⟩, ⟨.triD4, 0, 1⟩] ∧ GGHasLabel labJ X
  have hQinv : ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → Qprop X → Qprop Y := by
    intro X Y _ _ eXY hX
    obtain ⟨labJ, hmem, hlab⟩ := hX
    exact ⟨labJ, hmem, ggHasLabel_of_mulEquiv eXY hlab⟩
  refine TCJ.ggTCJ_cover_prop ψ hψ hker e he7 φ hφe Qprop hQinv ?_ J hJ
  intro hφ7 K' hK'
  have hKsub : Subsingleton Kˣ := by
    have h1 : Nat.card Kˣ = 1 := by rw [Nat.card_units, hKcard]
    exact (Nat.card_eq_one_iff_unique.mp h1).1
  obtain ⟨r, hr⟩ := (chevIDImage_subset_inn_of_subsingleton
    (A := LargeEvenCartanE 6) (H := LargeEvenChevH (LargeEvenCartanE 6) K false)) hφI
  let eR : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃*
      ↥(adjointGroup .E6 K) := TableBExc.recipeEquiv .E6 K
  let x : ↥(adjointGroup .E6 K) := eR r
  have hφ1 : φ ≠ 1 := by
    intro hφ1
    exact he1 (ltqL5_aut_eq_one_of_fix ψ hψ hker hcomm e (fun l => by
      simpa [hφ1] using (hφe l).symm))
  have hr7 : r ^ 7 = 1 := by
    have hr7conj : MulAut.conj (r ^ 7) = 1 := by
      have h : (MulAut.conj r) ^ 7 = 1 := by rw [hr]; exact hφ7
      rwa [← map_pow] at h
    have hr7center : r ^ 7 ∈ Subgroup.center
        (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := congrArg (fun f : MulAut _ => f g) hr7conj
      rw [MulAut.conj_apply, MulAut.one_apply] at hg
      calc g * r ^ 7 = (r ^ 7 * g * (r ^ 7)⁻¹) * r ^ 7 := by rw [hg]
        _ = r ^ 7 * g := by group
    have hr7center' : r ^ 7 ∈ Subgroup.center (TableBExc.RecipeGroup .E6 K) := hr7center
    rw [TableBExc.center_recipeGroup_eq_bot] at hr7center'
    exact Subgroup.mem_bot.mp hr7center'
  have hx7 : x ^ 7 = 1 := by
    show (eR r) ^ 7 = 1
    rw [← map_pow, hr7, map_one]
  have hx1 : x ≠ 1 := by
    intro hx1
    apply hφ1
    rw [← hr]
    have hr1 : r = 1 := by
      have h : eR r = eR 1 := by
        rw [show eR r = 1 from hx1, map_one]
      exact eR.injective h
    rw [hr1, map_one]
  have hx : orderOf x = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx7 hx1
  have hK'' : IsComponentOf K' (Subgroup.centralizer ({r} : Set
      (LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false)))) := by
    rw [← hr, ltqL5_fixSub_conj_eq_centralizer] at hK'
    exact hK'
  have hX : IsComponentOf (K'.map eR.toMonoidHom)
      (Subgroup.centralizer ({x} : Set (↥(adjointGroup .E6 K)))) := by
    have h := ltqL5_isComponentOf_map eR hK''
    rwa [ltqL5_centralizer_map eR r] at h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by simpa using hKcard)
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hlabel : ∃ labJ : LargeEvenLabel, labJ ∈ [⟨.A, 2, 1⟩, ⟨.triD4, 0, 1⟩] ∧
      GGHasLabel labJ (↥(K'.map eR.toMonoidHom) ⧸
        Subgroup.center ↥(K'.map eR.toMonoidHom)) := by
    rcases e6Phi3_component_type (K := K) (ℓ := 2) (f := 1) (hf := le_rfl)
      (hK := by simpa using hKcard) (p := 7) (hp := by norm_num) (hp3 := by norm_num)
      (hpq := by rw [hKcard]; norm_num) (L := AlgebraicClosure K)
      x hx (K'.map eR.toMonoidHom) hX with hcomp | ⟨e₀, he₀, ⟨eD4⟩⟩
    · rcases hcomp with ⟨eSL⟩
      exact ⟨⟨.A, 2, 1⟩, by simp, ggHasLabel_A21_of_mulEquiv_SL3 hKcard eSL⟩
    · exact ⟨⟨.triD4, 0, 1⟩, by simp,
        ggHasLabel_triD4_of_mulEquiv_d4ThetaFixed hKcard he₀ eD4⟩
  obtain ⟨labJ, hmem, hlab⟩ := hlabel
  exact ⟨labJ, hmem, ggHasLabel_quotCenter_of_mulEquiv
    (Subgroup.equivMapOfInjective K' eR.toMonoidHom eR.injective).symm hlab⟩

end CFSG.StandardType.E6TwoSeven

end
