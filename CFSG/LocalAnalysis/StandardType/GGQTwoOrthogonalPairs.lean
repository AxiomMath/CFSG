module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixAux
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDSupported
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBNbrCompare
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoMoves
import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeEvenAux
public import CFSG.LocalAnalysis.StandardType.GGQTwoNormPlaneCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoOrthogonalBlocks
public import CFSG.Permutation.Embedding
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniOmFrames
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockGeneration
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmBlkCore

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {p n : ℕ}

noncomputable abbrev ggZ (Bs : Subgroup G)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) (P : Finset (Fin n)) : Subgroup G :=
  ggBlockComm Bs eta (P : Set (Fin n)) ⊓
    ggConjPreimage Bs ((TypeDDatum.evenSignedSupportedAut n 3 P).comap
      (MulAut.congr eta).toMonoidHom)

theorem mem_ggZ {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    {P : Finset (Fin n)} {g : G} :
    g ∈ ggZ Bs eta P ↔
      g ∈ ggBlockComm Bs eta (P : Set (Fin n)) ∧
        g ∈ ggConjPreimage Bs ((TypeDDatum.evenSignedSupportedAut n 3 P).comap
          (MulAut.congr eta).toMonoidHom) :=
  Iff.rfl

theorem ggZ_map_conj {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    {P : Finset (Fin n)} {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ) :
    (ggZ Bs eta P).map (MulAut.conj g).toMonoidHom = ggZ Bs eta (P.image τ) := by
  rw [ggZ, ggZ, Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective]
  congr 1
  · simpa using ggBlockComm_map_conj (Bs := Bs) (eta := eta) hg hτ (P : Set (Fin n))
  · rw [ggConjPreimage_map_conj hg]
    congr 1
    rw [← TypeDDatum.tbD_map_conj_evenSignedSupportedAut, ← hτ]
    rw [Subgroup.map_equiv_eq_comap_symm' (f := MulAut.conj (ggConjAut Bs hg))]
    rw [Subgroup.comap_comap]
    rw [Subgroup.map_equiv_eq_comap_symm'
      (f := MulAut.conj (MulAut.congr eta (ggConjAut Bs hg)))]
    rw [Subgroup.comap_comap]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]

private theorem moveExp_symm_apply {r : ℕ} (σ : Equiv.Perm (Fin r)) (ε : Fin r → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (f : Fin r → ZMod 3) (i : Fin r) :
    ChoiceTwo.moveExp σ.symm (fun j => decide (ε (σ.symm j) = -1)) f (σ i) = ε i * f i := by
  simp only [ChoiceTwo.moveExp_apply, Equiv.symm_apply_apply]
  rcases hε i with h | h
  · have hdec : decide (ε i = -1) = false := by rw [h]; decide
    rw [hdec, h]
    simp [ChoiceTwo.sgnZ]
  · have hdec : decide (ε i = -1) = true := by rw [h]; decide
    rw [hdec, h]
    simp [ChoiceTwo.sgnZ]

theorem exists_ggG0_transporter_of_perm {B Bs L D J : Subgroup G} {x : G}
    {𝒦 : Finset (Subgroup G)} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom =
      bSignedFull n 3)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (τ : Equiv.Perm (Fin n)) :
    ∃ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
      g ∈ ggG0 3 B x L D J ∧
        MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ := by
  have hperm : SpCoord.permAut (p := 3) τ ∈ bSignedFull n 3 :=
    aPermutationFull_le_bSignedFull (permAut_mem_aPermutationFull (p := 3) τ)
  have hmem : SpCoord.permAut (p := 3) τ ∈
      (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom := by
    rw [h𝒦]
    exact hperm
  have hmem' : SpCoord.permAut (p := 3) τ ∈
      (ggAutomizer (L ⊔ ⨆ K ∈ 𝒦, K) Bs).map (MulAut.congr eta).toMonoidHom :=
    (Subgroup.map_mono (ggAutomizerJoin_le_ggAutomizer L Bs 𝒦)) hmem
  obtain ⟨g, hgN, hgW, hτ⟩ :=
    exists_mem_of_mem_map_congr (Bs := Bs) (W := L ⊔ ⨆ K ∈ 𝒦, K) eta hmem'
  refine ⟨g, hgN, ?_, hτ⟩
  rw [hG0]
  exact hgW


section Native

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LieType.BorelTits
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.RankThree.PartOne.KCOrthogonal QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  {f : ℕ} {E : QuadExt F K (unitaryInvolution K 2 f)} {r : ℕ}

theorem normBlock_fixes_coordSupport_of_disjoint {S T : Finset (Fin r)} (hdisj : Disjoint S T)
    {a : normOmega E r} (ha : a ∈ normBlock E r S)
    (hfix : ∀ w : F × F, a.1 (w, (0 : Fin r → K)) = (w, 0)) :
    ∀ x ∈ coordSupport (LinearEquiv.refl F ((F × F) × (Fin r → K))) T, a.1 x = x := by
  classical
  let V := (F × F) × (Fin r → K)
  let ψ : V ≃ₗ[F] ((F × F) × (Fin r → K)) := LinearEquiv.refl F V
  have haSD : (a : V ≃ₗ[F] V) ∈ supportedDerived (normHypForm E r)
      (coordSupport ψ S) := ha
  let P : Submodule F V → Prop := fun U => ∀ x ∈ U, (a : V ≃ₗ[F] V) x = x
  have hPbot : P ⊥ := by
    intro x hx
    rw [Submodule.mem_bot] at hx
    rw [hx]
    exact map_zero _
  have hPsup : ∀ U W : Submodule F V, P U → P W → P (U ⊔ W) := by
    intro U W hU hW x hx
    rw [Submodule.mem_sup] at hx
    obtain ⟨u, hu, w, hw, rfl⟩ := hx
    rw [map_add, hU u hu, hW w hw]
  have hPanchor : P (coordAnchor ψ) := by
    intro x hx
    obtain ⟨w, rfl⟩ := (mem_coordAnchor (ψ := ψ)).mp hx
    change (a : V ≃ₗ[F] V) (w, (0 : Fin r → K)) = (w, 0)
    exact hfix w
  have hPplane : ∀ j ∈ T, P (coordPlane ψ j) := by
    intro j hj x hx
    obtain ⟨e, rfl⟩ := (mem_coordPlane (ψ := ψ)).mp hx
    have hperp : ψ.symm (0, Pi.single j e) ∈
        suppPerp (normHypForm E r) (coordSupport ψ S) := by
      rw [mem_suppPerp_coordSupport_refl_iff (E := E) S]
      refine ⟨rfl, fun k hk => ?_⟩
      have hkj : k ≠ j := by
        rintro rfl
        exact (Finset.disjoint_left.mp hdisj hk) hj
      change (Pi.single j e : Fin r → K) k = 0
      simp [Pi.single_eq_of_ne hkj]
    simpa [ψ] using supportedDerived_apply_perp haSD hperp
  have hPT : P (T.sup (coordPlane ψ)) :=
    Finset.sup_induction hPbot (fun U hU W hW => hPsup U W hU hW) hPplane
  change P (coordSupport ψ T)
  rw [coordSupport]
  exact hPsup _ _ hPanchor hPT

theorem normBlock_commute_of_disjoint_of_fix_anchor {S T : Finset (Fin r)} (hdisj : Disjoint S T)
    {a b : normOmega E r} (ha : a ∈ normBlock E r S) (hb : b ∈ normBlock E r T)
    (hfix : ∀ w : F × F, a.1 (w, (0 : Fin r → K)) = (w, 0)) : Commute a b := by
  classical
  let V := (F × F) × (Fin r → K)
  let X : Submodule F V :=
    coordSupport (LinearEquiv.refl F V) T
  haveI : FiniteDimensional F K := finiteDimensional_of_quadExt E
  have hXpolar : PolarNondegOn (normHypForm E r) X :=
    polarNondegOn_of_nondegenerate
      (coordSupport_nondegenerate (ψ := LinearEquiv.refl F V)
        (hψ := normHypForm_apply_coord E r)
        (hQ := normHypForm_polarBilin_nondegenerate E r)
        (hQE := normQuad_polarBilin_nondegenerate E) T)
  have hX : SUTB.NondegOn (polarBilin (normHypForm E r)) X := by
    intro m hm h
    refine hXpolar m hm fun n hn => ?_
    have hn0 := h n hn
    rw [polarBilin_apply_apply] at hn0
    simpa [polar_comm] using hn0
  have hbSD : (b : V ≃ₗ[F] V) ∈ supportedDerived (normHypForm E r)
      (coordSupport (LinearEquiv.refl F V) T) := hb
  have haSD : (a : V ≃ₗ[F] V) ∈ supportedDerived (normHypForm E r)
      (coordSupport (LinearEquiv.refl F V) S) := ha
  have hbFix : ∀ y ∈ X.orthogonalBilin (polarBilin (normHypForm E r)), (b : V ≃ₗ[F] V) y = y :=
    fun y hy => supportedDerived_apply_perp hbSD hy
  have hbPres : ∀ x ∈ X, (b : V ≃ₗ[F] V) x ∈ X :=
    fun x hx => supportedDerived_apply_mem hbSD hx
  have haFix : ∀ x ∈ X, (a : V ≃ₗ[F] V) x = x :=
    normBlock_fixes_coordSupport_of_disjoint hdisj ha hfix
  have haO : (a : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E r) :=
    supportedDerived_le_orthogonalGroup
      (polarNondegOn_of_nondegenerate
        (coordSupport_nondegenerate (ψ := LinearEquiv.refl F V)
          (hψ := normHypForm_apply_coord E r)
          (hQ := normHypForm_polarBilin_nondegenerate E r)
          (hQE := normQuad_polarBilin_nondegenerate E) S)) haSD
  have haPerp : ∀ y ∈ X.orthogonalBilin (polarBilin (normHypForm E r)),
      (a : V ≃ₗ[F] V) y ∈ X.orthogonalBilin (polarBilin (normHypForm E r)) :=
    fun y hy => WitOmBlk.map_mem_orth_of_fix haO haFix hy
  have hcomm : (b : V ≃ₗ[F] V) * (a : V ≃ₗ[F] V) =
      (a : V ≃ₗ[F] V) * (b : V ≃ₗ[F] V) :=
    WitOmBlk.commute_of_fix hX hbFix hbPres haFix haPerp
  apply Subtype.ext
  exact hcomm.symm

end Native

section Forward

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  {E : QuadExt F K (unitaryInvolution K 2 1)} {G : Type} [Group G] [Finite G]
  {B Bs L D J : Subgroup G} {x : G} {n r : ℕ}

theorem normOmega_mem_normBlock_and_fixes_anchor_of_mem_ggZ
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {S : Finset (Fin r)} (hS : S.card = 2) {a : normOmega E r}
    (hz : κ a ∈ ggZ Bs eta (S.image (fun i : Fin r => π i.castSucc))) :
    a ∈ normBlock E r S ∧
      ∀ w : F × F, a.1 (w, (0 : Fin r → K)) = (w, 0) := by
  classical
  letI : CharP F 2 := (Algebra.charP_iff F K 2).mpr inferInstance
  let ι : Fin r → Fin n := fun i => π i.castSucc
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hcfg.2.1.2.2.2
  rw [mem_ggZ] at hz
  obtain ⟨hzY, hzPre⟩ := hz
  have haN : κ a ∈ Subgroup.normalizer (Bs : Set G) :=
    ggConjPreimage_le_normalizer Bs _ hzPre
  have hNH : Bs.normalizerMonoidHom (⟨κ a, haN⟩ : Subgroup.normalizer (Bs : Set G)) =
      ggConjAut Bs haN := by
    ext b
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ggConjAut_apply]
  have hEven : MulAut.congr eta (ggConjAut Bs haN) ∈
      TypeDDatum.evenSignedSupportedAut n 3 (S.image ι) := by
    have h := (mem_ggConjPreimage_iff (⟨κ a, haN⟩ : Subgroup.normalizer (Bs : Set G))).mp hzPre
    simpa [Subgroup.mem_comap, hNH] using h
  obtain ⟨σ, ε, hε, hprod, hact, hlast⟩ :=
    TypeDDatum.exists_signed_on_castSucc_of_mem_evenSignedSupportedAut
      (p := 3) (by decide : (3 : ℕ) ≠ 2) π S hEven
  let η : Fin r → Bool := fun j => decide (ε (σ.symm j) = -1)
  have hEvenη : Even (Finset.univ.filter fun j => η j = true).card := by
    have hprod' : (∏ i, ε (σ.symm i)) = 1 := by
      rw [Equiv.prod_comp]
      exact hprod
    have h := ggWTEven_even_card_of_prod (p := 3) (by decide : (3 : ℕ).Prime)
      (by decide : (3 : ℕ) ≠ 2) (fun j => ε (σ.symm j))
      (fun j => hε (σ.symm j)) hprod'
    simpa [η, decide_eq_true_eq] using h
  have hblock := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (S := S) (hS := Or.inr hS)
  have hzMap : κ a ∈ (normBlock E r S).map κ := by
    simpa [hblock] using hzY
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hzMap
  have hba' : b = a := hframe.1 hba
  have haBlock : a ∈ normBlock E r S := by
    simpa [hba'] using hb
  refine ⟨haBlock, ?_⟩
  have hconj : ∀ f : Fin r → ZMod 3,
      a * normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => Multiplicative.ofAdd (f i)) * a⁻¹ =
        normPlaneTorus E (by omega : 2 ≤ r) (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => Multiplicative.ofAdd (ChoiceTwo.moveExp σ.symm η f i)) := by
    intro f
    let u : Fin r → Multiplicative (ZMod 3) := fun i => Multiplicative.ofAdd (f i)
    let u' : Fin r → Multiplicative (ZMod 3) :=
      fun i => Multiplicative.ofAdd (ChoiceTwo.moveExp σ.symm η f i)
    let bf : ↥Bs := ⟨κ (normPlaneTorus E (by omega : 2 ≤ r)
        (by decide : 3 ∣ 2 ^ 1 + 1) χ u),
      hframe.normPlaneTorus_mem_Bs (hr := by omega) (hSC := hSC) u⟩
    let bf' : ↥Bs := ⟨κ (normPlaneTorus E (by omega : 2 ≤ r)
        (by decide : 3 ∣ 2 ^ 1 + 1) χ u'),
      hframe.normPlaneTorus_mem_Bs (hr := by omega) (hSC := hSC) u'⟩
    have hcongr (y : ↥Bs) :
        (MulAut.congr eta (ggConjAut Bs haN)) (eta y) =
          eta (ggConjAut Bs haN y) := by
      funext j
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have heta : eta (ggConjAut Bs haN bf) = eta bf' := by
      funext j
      obtain ⟨k, rfl⟩ := π.surjective j
      rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
      · obtain ⟨j, rfl⟩ := σ.surjective i
        apply Multiplicative.toAdd.injective
        have hleft := hact (eta bf) j
        rw [hcongr bf] at hleft
        have hbi : Multiplicative.toAdd (eta bf (π j.castSucc)) = f j := by
          rw [hframe.coords_normPlaneTorus (hr := by omega) (hSC := hSC) (u := u) j]
          simp [u]
        have hbi' : Multiplicative.toAdd (eta bf' (π (σ j).castSucc)) = ε j * f j := by
          rw [hframe.coords_normPlaneTorus (hr := by omega) (hSC := hSC) (u := u') (σ j)]
          simpa [u'] using moveExp_symm_apply σ ε hε f j
        calc
          Multiplicative.toAdd (eta (ggConjAut Bs haN bf) (π (σ j).castSucc)) =
              ε j * Multiplicative.toAdd (eta bf (π j.castSucc)) := hleft
          _ = ε j * f j := by rw [hbi]
          _ = Multiplicative.toAdd (eta bf' (π (σ j).castSucc)) := hbi'.symm
      · have hleft := hlast (eta bf)
        rw [hcongr bf] at hleft
        have hbf_last : eta bf (π (Fin.last r)) = 1 := by
          rw [hpi]
          exact hframe.normPlaneTorus_coord_last (hr := hr) hcfg hZ hN hLeta u
        have hbf'_last : eta bf' (π (Fin.last r)) = 1 := by
          rw [hpi]
          exact hframe.normPlaneTorus_coord_last (hr := hr) hcfg hZ hN hLeta u'
        rw [hleft, hbf_last, hbf'_last]
    have hsub : ggConjAut Bs haN bf = bf' := eta.injective heta
    have hG : κ a * κ (normPlaneTorus E (by omega : 2 ≤ r)
        (by decide : 3 ∣ 2 ^ 1 + 1) χ u) * (κ a)⁻¹ =
        κ (normPlaneTorus E (by omega : 2 ≤ r)
          (by decide : 3 ∣ 2 ^ 1 + 1) χ u') := by
      have := congrArg (fun y : ↥Bs => (y : G)) hsub
      simpa [bf, bf', ggConjAut_apply] using this
    have hκ : κ (a * normPlaneTorus E (by omega : 2 ≤ r)
        (by decide : 3 ∣ 2 ^ 1 + 1) χ u * a⁻¹) =
        κ (normPlaneTorus E (by omega : 2 ≤ r)
          (by decide : 3 ∣ 2 ^ 1 + 1) χ u') := by
      simpa [map_mul, map_inv] using hG
    exact hframe.1 hκ
  exact (OrthAnchor.normPlaneTorus_even_moveExp_iff_fixes_anchor E (by omega : 2 ≤ r)
    hF χ hframe.2.2.1 (g := a) σ.symm η hconj).mp hEvenη

theorem ggZ_commute_ggBlockComm_of_disjoint
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {S T : Finset (Fin r)} (hS : S.card = 2) (hT : T.card = 1 ∨ T.card = 2)
    (hdisj : Disjoint S T) {z y : G}
    (hz : z ∈ ggZ Bs eta (S.image (fun i : Fin r => π i.castSucc)))
    (hy : y ∈ ggBlockComm Bs eta (T.image (fun i : Fin r => π i.castSucc))) :
    Commute z y := by
  classical
  let ι : Fin r → Fin n := fun i => π i.castSucc
  obtain ⟨hzY, -⟩ := (mem_ggZ (Bs := Bs) (eta := eta)
    (P := S.image ι) (g := z)).mp hz
  have hblockS := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (S := S) (hS := Or.inr hS)
  have hzMap : z ∈ (normBlock E r S).map κ := by
    simpa [ι, hblockS] using hzY
  obtain ⟨a, haBlock, rfl⟩ := Subgroup.mem_map.mp hzMap
  have hforward := normOmega_mem_normBlock_and_fixes_anchor_of_mem_ggZ
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (hS := hS) hz
  obtain ⟨-, haFix⟩ := hforward
  have hblockT := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (S := T) (hS := hT)
  have hyMap : y ∈ (normBlock E r T).map κ := by
    simpa [ι, hblockT] using hy
  obtain ⟨b, hbBlock, rfl⟩ := Subgroup.mem_map.mp hyMap
  have hcomm : Commute a b :=
    normBlock_commute_of_disjoint_of_fix_anchor hdisj haBlock hbBlock haFix
  simpa using hcomm.map κ

private theorem ggZ_commute_ggBlockComm_ambient_transport
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    {P Q : Finset (Fin n)} (hP : P.card = 2) (hQ : Q.card = 1 ∨ Q.card = 2)
    (hcard : (P ∪ Q).card < n) (hPQ : Disjoint P Q) {z y : G}
    (hz : z ∈ ggZ Bs eta P)
    (hy : y ∈ ggBlockComm Bs eta (Q : Set (Fin n))) :
    Commute z y := by
  classical
  let ι : Fin r → Fin n := fun i => π i.castSucc
  have hιinj : Function.Injective ι := by
    intro i j hij
    exact Fin.castSucc_injective r (π.injective hij)
  have hlt : (P ∪ Q).card < (Finset.univ : Finset (Fin n)).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using hcard
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let τ : Equiv.Perm (Fin n) := Equiv.swap i0 e
  obtain ⟨g, hgN, -, hτ⟩ :=
    exists_ggG0_transporter_of_perm (h𝒦 := h𝒦) (hG0 := hG0) τ
  have hz' : (MulAut.conj g) z ∈ ggZ Bs eta (P.image τ) := by
    change g * z * g⁻¹ ∈ ggZ Bs eta (P.image τ)
    rw [← ggZ_map_conj (Bs := Bs) (eta := eta) (g := g) hgN (P := P) (τ := τ) hτ]
    exact Subgroup.mem_map_of_mem _ hz
  have hy' : (MulAut.conj g) y ∈ ggBlockComm Bs eta (τ '' (Q : Set (Fin n))) := by
    change g * y * g⁻¹ ∈ ggBlockComm Bs eta (τ '' (Q : Set (Fin n)))
    rw [← ggBlockComm_map_conj (Bs := Bs) (eta := eta) (g := g) hgN (τ := τ) hτ
      (Q : Set (Fin n))]
    exact Subgroup.mem_map_of_mem _ hy
  have hi0P : i0 ∉ P.image τ := by
    intro hi
    obtain ⟨p, hp, hpi⟩ := Finset.mem_image.mp hi
    have hpe : p = e := by
      have h := (Equiv.swap_apply_eq_iff (x := i0) (y := e) (z := p) (w := i0)).mp
        (by simpa [τ] using hpi)
      simpa using h
    exact he (by simpa [hpe] using Finset.mem_union_left Q hp)
  have hi0Q : i0 ∉ Q.image τ := by
    intro hi
    obtain ⟨q, hq, hqi⟩ := Finset.mem_image.mp hi
    have hqe : q = e := by
      have h := (Equiv.swap_apply_eq_iff (x := i0) (y := e) (z := q) (w := i0)).mp
        (by simpa [τ] using hqi)
      simpa using h
    exact he (by simpa [hqe] using Finset.mem_union_right P hq)
  have hrange : ∀ x : Fin n, x ≠ i0 → x ∈ Set.range ι := by
    intro x hx
    obtain ⟨k, rfl⟩ := π.surjective x
    have hk : k ≠ Fin.last r := by
      intro h
      exact hx (by rw [h, hpi])
    obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hk
    exact ⟨i, by simp [ι, hi]⟩
  let S : Finset (Fin r) := (P.image τ).preimage ι hιinj.injOn
  let T : Finset (Fin r) := (Q.image τ).preimage ι hιinj.injOn
  have hSimg : S.image ι = P.image τ := by
    rw [Finset.image_preimage]
    exact Finset.filter_true_of_mem fun x hx => hrange x (fun h => hi0P (h ▸ hx))
  have hTimg : T.image ι = Q.image τ := by
    rw [Finset.image_preimage]
    exact Finset.filter_true_of_mem fun x hx => hrange x (fun h => hi0Q (h ▸ hx))
  have hScard : S.card = 2 := by
    have := congrArg Finset.card hSimg
    rw [Finset.card_image_of_injOn hιinj.injOn,
      Finset.card_image_of_injOn τ.injective.injOn, hP] at this
    exact this
  have hTcardQ : T.card = Q.card := by
    have := congrArg Finset.card hTimg
    rw [Finset.card_image_of_injOn hιinj.injOn,
      Finset.card_image_of_injOn τ.injective.injOn] at this
    exact this
  have hTcard : T.card = 1 ∨ T.card = 2 := by
    rw [hTcardQ]
    exact hQ
  have hST : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    have hP' : ι i ∈ P.image τ := Finset.mem_preimage.mp hiS
    have hQ' : ι i ∈ Q.image τ := Finset.mem_preimage.mp hiT
    exact (Finset.disjoint_left.mp ((Finset.disjoint_image τ.injective).mpr hPQ) hP') hQ'
  have hz'' : (MulAut.conj g) z ∈ ggZ Bs eta (S.image ι) := by
    simpa [hSimg] using hz'
  have hy'' : (MulAut.conj g) y ∈ ggBlockComm Bs eta (T.image ι : Set (Fin n)) := by
    simpa [hTimg, Finset.coe_image] using hy'
  have hcomm := ggZ_commute_ggBlockComm_of_disjoint
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe)
    (S := S) (T := T) hScard hTcard hST hz'' hy''
  exact Commute.of_map (f := MulAut.conj g) (MulAut.conj g).injective hcomm

private theorem ggBlockComm_pair_eq_sup
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hn : 4 ≤ n) (i j : Fin n) :
    ggBlockComm Bs eta ({i, j} : Set (Fin n)) =
      ggBlockComm Bs eta ({i} : Set (Fin n)) ⊔
        ggBlockComm Bs eta ({j} : Set (Fin n)) := by
  classical
  by_cases hij : i = j
  · subst j
    simp
  have hcard3 : ({i, j, i0} : Finset (Fin n)).card ≤ 3 :=
    Finset.card_le_three
  have hlt : ({i, j, i0} : Finset (Fin n)).card <
      (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨e, -, he⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have he_i : e ≠ i := by rintro rfl; exact he (by simp)
  have he_j : e ≠ j := by rintro rfl; exact he (by simp)
  have he_i0 : e ≠ i0 := by rintro rfl; exact he (by simp)
  let τ : Equiv.Perm (Fin n) := Equiv.swap i0 e
  obtain ⟨g, hgN, -, hτ⟩ :=
    exists_ggG0_transporter_of_perm (h𝒦 := h𝒦) (hG0 := hG0) τ
  let ι : Fin r → Fin n := fun i => π i.castSucc
  have hιinj : Function.Injective ι := by
    intro a b hab
    exact Fin.castSucc_injective r (π.injective hab)
  have hrange : ∀ x : Fin n, x ≠ i0 → x ∈ Set.range ι := by
    intro x hx
    obtain ⟨k, rfl⟩ := π.surjective x
    have hk : k ≠ Fin.last r := by intro h; exact hx (by rw [h, hpi])
    obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last hk
    exact ⟨a, by simp [ι, ha]⟩
  have hi0τi : τ i ≠ i0 := by
    intro h
    have hie : i = e := by
      have := (Equiv.swap_apply_eq_iff (x := i0) (y := e) (z := i) (w := i0)).mp
        (by simpa [τ] using h)
      simpa using this
    exact he_i hie.symm
  have hi0τj : τ j ≠ i0 := by
    intro h
    have hje : j = e := by
      have := (Equiv.swap_apply_eq_iff (x := i0) (y := e) (z := j) (w := i0)).mp
        (by simpa [τ] using h)
      simpa using this
    exact he_j hje.symm
  let a : Fin r := Classical.choose (hrange (τ i) hi0τi)
  have ha : ι a = τ i := Classical.choose_spec (hrange (τ i) hi0τi)
  let b : Fin r := Classical.choose (hrange (τ j) hi0τj)
  have hb : ι b = τ j := Classical.choose_spec (hrange (τ j) hi0τj)
  have hS : ({a, b} : Finset (Fin r)).card = 1 ∨
      ({a, b} : Finset (Fin r)).card = 2 := by
    by_cases hab : a = b
    · left; simp [hab]
    · right; simp [hab]
  have hblockS := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe)
    (S := ({a, b} : Finset (Fin r))) (hS := hS)
  have hSimg : ({a, b} : Finset (Fin r)).image ι = ({τ i, τ j} : Finset (Fin n)) := by
    ext x
    simp [ι, ha, hb]
  have hpairY : ggBlockComm Bs eta ({τ i, τ j} : Set (Fin n)) =
      (normBlock E r ({a, b} : Finset (Fin r))).map κ := by
    simpa [hSimg, Set.image_pair, ι, ha, hb] using hblockS
  have hblocka := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe)
    (S := ({a} : Finset (Fin r))) (hS := Or.inl (by simp))
  have hblockb := GGSecFiveBPermOmKFrame.blockComm
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe)
    (S := ({b} : Finset (Fin r))) (hS := Or.inl (by simp))
  have hsinglea : ggBlockComm Bs eta ({τ i} : Set (Fin n)) =
      (normBlock E r ({a} : Finset (Fin r))).map κ := by
    simpa [ι, ha] using hblocka
  have hsingleb : ggBlockComm Bs eta ({τ j} : Set (Fin n)) =
      (normBlock E r ({b} : Finset (Fin r))).map κ := by
    simpa [ι, hb] using hblockb
  have hnative : (normBlock E r ({a, b} : Finset (Fin r))).map κ =
      (normBlock E r ({a} : Finset (Fin r))).map κ ⊔
        (normBlock E r ({b} : Finset (Fin r))).map κ := by
    rw [← normBlock_singleton_sup_singleton (E := E) a b, Subgroup.map_sup]
  have hYpair : ggBlockComm Bs eta ({τ i, τ j} : Set (Fin n)) =
      ggBlockComm Bs eta ({τ i} : Set (Fin n)) ⊔
        ggBlockComm Bs eta ({τ j} : Set (Fin n)) := by
    rw [hpairY, hnative, ← hsinglea, ← hsingleb]
  apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective
  rw [ggBlockComm_map_conj (Bs := Bs) (eta := eta) (g := g) hgN (τ := τ) hτ
      ({i, j} : Set (Fin n)),
    Subgroup.map_sup,
    ggBlockComm_map_conj (Bs := Bs) (eta := eta) (g := g) hgN (τ := τ) hτ
      ({i} : Set (Fin n)),
    ggBlockComm_map_conj (Bs := Bs) (eta := eta) (g := g) hgN (τ := τ) hτ
      ({j} : Set (Fin n))]
  simpa [Set.image_pair] using hYpair

theorem ggZ_commute_ggBlockComm_ambient_far
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hn : 4 ≤ n) {P Q : Finset (Fin n)} (hP : P.card = 2) (hQ : Q.card = 2)
    (hPQ : Disjoint P Q) {z y : G}
    (hz : z ∈ ggZ Bs eta P)
    (hy : y ∈ ggBlockComm Bs eta (Q : Set (Fin n))) :
    Commute z y := by
  classical
  obtain ⟨c, d, hcd, rfl⟩ := Finset.card_eq_two.mp hQ
  have hcP : c ∉ P := by
    intro hc
    exact (Finset.disjoint_left.mp hPQ hc) (by simp)
  have hdP : d ∉ P := by
    intro hd
    exact (Finset.disjoint_left.mp hPQ hd) (by simp)
  have hcardPc : (P ∪ {c}).card < n := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hcP), hP]
    simp
    omega
  have hcardPd : (P ∪ {d}).card < n := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hdP), hP]
    simp
    omega
  have hcomm_c : ∀ y ∈ ggBlockComm Bs eta ({c} : Set (Fin n)), Commute z y := by
    intro y hy
    exact ggZ_commute_ggBlockComm_ambient_transport
      (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
      (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (h𝒦 := h𝒦) (hG0 := hG0)
      (P := P) (Q := {c}) (hP := hP) (hQ := Or.inl rfl)
      (hcard := hcardPc) (hPQ := Finset.disjoint_singleton_right.mpr hcP) hz
      (by simpa [Finset.coe_singleton] using hy)
  have hcomm_d : ∀ y ∈ ggBlockComm Bs eta ({d} : Set (Fin n)), Commute z y := by
    intro y hy
    exact ggZ_commute_ggBlockComm_ambient_transport
      (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
      (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (h𝒦 := h𝒦) (hG0 := hG0)
      (P := P) (Q := {d}) (hP := hP) (hQ := Or.inl rfl)
      (hcard := hcardPd) (hPQ := Finset.disjoint_singleton_right.mpr hdP) hz
      (by simpa [Finset.coe_singleton] using hy)
  have hjoin := ggBlockComm_pair_eq_sup
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe)
    (h𝒦 := h𝒦) (hG0 := hG0) hn c d
  rw [Finset.coe_pair] at hy
  rw [hjoin] at hy
  have hle_c : ggBlockComm Bs eta ({c} : Set (Fin n)) ≤
      Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvz : v = z := by simpa using hv
    rw [hvz]
    exact (hcomm_c u hu).eq
  have hle_d : ggBlockComm Bs eta ({d} : Set (Fin n)) ≤
      Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvz : v = z := by simpa using hv
    rw [hvz]
    exact (hcomm_d u hu).eq
  have hle : ggBlockComm Bs eta ({c} : Set (Fin n)) ⊔
      ggBlockComm Bs eta ({d} : Set (Fin n)) ≤
        Subgroup.centralizer ({z} : Set G) := sup_le hle_c hle_d
  have hyz := hle hy
  rw [Subgroup.mem_centralizer_iff] at hyz
  exact hyz z (by simp)

theorem ggBlockComm_commute_of_supported_swap
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hn : 4 ≤ n) {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (hdisj : Disjoint ({a, b} : Finset (Fin n)) {c, d})
    {z : G} (hzY : z ∈ ggBlockComm Bs eta ({c, d} : Set (Fin n)))
    (hzN : z ∈ Subgroup.normalizer (Bs : Set G))
    (hzact : MulAut.congr eta (ggConjAut Bs hzN) =
      SpCoord.permAut (Equiv.swap c d)) :
    ∀ y ∈ ggBlockComm Bs eta ({a, b} : Set (Fin n)), Commute z y := by
  classical
  have hswap : SpCoord.permAut (Equiv.swap c d) ∈
      TypeDDatum.evenSignedSupportedAut n 3 ({c, d} : Finset (Fin n)) :=
    Subgroup.subset_closure
      (Or.inl ⟨c, by simp, d, by simp, hcd, rfl⟩)
  have hEven : MulAut.congr eta (ggConjAut Bs hzN) ∈
      TypeDDatum.evenSignedSupportedAut n 3 ({c, d} : Finset (Fin n)) := by
    simpa [hzact] using hswap
  have hNH : Bs.normalizerMonoidHom (⟨z, hzN⟩ : Subgroup.normalizer (Bs : Set G)) =
      ggConjAut Bs hzN := by
    ext b
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, ggConjAut_apply]
  have hzPre : z ∈ ggConjPreimage Bs
      ((TypeDDatum.evenSignedSupportedAut n 3 ({c, d} : Finset (Fin n))).comap
        (MulAut.congr eta).toMonoidHom) := by
    rw [mem_ggConjPreimage_iff (⟨z, hzN⟩ : Subgroup.normalizer (Bs : Set G))]
    simpa [Subgroup.mem_comap, hNH] using hEven
  have hzZ : z ∈ ggZ Bs eta ({c, d} : Finset (Fin n)) := by
    exact (mem_ggZ (Bs := Bs) (eta := eta) (P := ({c, d} : Finset (Fin n)))
      (g := z)).mpr ⟨by simpa using hzY, hzPre⟩
  have hP : ({c, d} : Finset (Fin n)).card = 2 := by simp [hcd]
  have hQ : ({a, b} : Finset (Fin n)).card = 2 := by simp [hab]
  intro y hy
  exact ggZ_commute_ggBlockComm_ambient_far
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (h𝒦 := h𝒦) (hG0 := hG0)
    (hn := hn) (P := {c, d}) (Q := {a, b}) hP hQ hdisj.symm hzZ
    (by simpa using hy)

theorem GGSecFiveBPermOmKFrame.normPerm_swap_commute_of_componentFrame
    (hF : Nat.card F = 2) (hr : 3 ≤ r)
    (hcfg : GGConfig 3 B Bs x L D J)
    (hZ : Subgroup.center L = ⊥)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hLeta : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom =
      bCoordinateBlock n 3 i0)
    {π : Fin (r + 1) ≃ Fin n} (hpi : π (Fin.last r) = i0)
    {κ : normOmega E r →* G} {χ : Multiplicative (ZMod 3) →* Kˣ}
    (hframe : GGSecFiveBPermOmKFrame E Bs L eta π κ χ)
    {𝒦 : Finset (Subgroup G)}
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n 3)
    (hG0 : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (hn : 4 ≤ n)
    {F' K' : Type} [Field F'] [Field K'] [Algebra F' K'] [Finite K'] [CharP K' 2]
    {f' : ℕ} {E' : QuadExt F' K' (unitaryInvolution K' 2 f')}
    {X : Subgroup G} {s : ℕ} (hs : 3 ≤ s)
    {y : G} (hyB : y ∈ Bs)
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({y} : Set G)))
    {π' : Fin (s + 1) ≃ Fin n} {κ' : normOmega E' s →* G}
    {χ' : Multiplicative (ZMod 3) →* K'ˣ}
    (hframe' : GGSecFiveBPermOmKFrame E' Bs X eta π' κ' χ')
    {i j : Fin r} (hij : i ≠ j) {u v : Fin s} (huv : u ≠ v)
    (hdisj : Disjoint
      ({π i.castSucc, π j.castSucc} : Finset (Fin n))
      ({π' u.castSucc, π' v.castSucc} : Finset (Fin n))) :
    Commute (κ (normPerm E hr (Equiv.swap i j)))
      (κ' (normPerm E' hs (Equiv.swap u v))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let z : G := κ (normPerm E hr (Equiv.swap i j))
  have hzY : z ∈ ggBlockComm Bs eta
      ({π i.castSucc, π j.castSucc} : Set (Fin n)) :=
    hframe.normPerm_swap_mem_ggBlockComm (hF := hF) (hr := hr)
      (hcfg := hcfg) (hZ := hZ) (hN := hN) (hLeta := hLeta) (hpi := hpi) i j
  have hzN : z ∈ Subgroup.normalizer (Bs : Set G) :=
    hframe.normPerm_mem_normalizer (hr := hr) (hSC := hcfg.2.1.2.2.2)
      (Equiv.swap i j)
  have hzact : MulAut.congr eta (ggConjAut Bs hzN) =
      SpCoord.permAut (Equiv.swap (π i.castSucc) (π j.castSucc)) := by
    have h := GGSecFiveBPermOmKFrame.congr_normPerm (hframe := hframe)
      (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN) (hLeta := hLeta)
      (hpi := hpi) (σ := Equiv.swap i j)
    dsimp only at h
    rw [CFSG.Permutation.viaEmbeddingHom_swap] at h
    simpa [Fin.castSuccEmb_apply] using h
  have hYpair : ({u, v} : Finset (Fin s)).card = 2 := by simp [huv]
  have hYlt : ({u, v} : Finset (Fin s)).card < s := by
    rw [hYpair]
    omega
  have hblk' := GGSecFiveBPermOmKFrame.blockComm_eq_map_normBlock
    (p := 3) (hBs := hcfg.2.1.2.2.2) (hyB := hyB) (hX := hX)
    (hκ := hframe') (S := ({u, v} : Finset (Fin s))) (by omega) hYlt
  have hyY : κ' (normPerm E' hs (Equiv.swap u v)) ∈
      ggBlockComm Bs eta ({π' u.castSucc, π' v.castSucc} : Set (Fin n)) := by
    have hmem : κ' (normPerm E' hs (Equiv.swap u v)) ∈
        (normBlock E' s ({u, v} : Finset (Fin s))).map κ' :=
      Subgroup.mem_map_of_mem _ (normPerm_swap_mem_normBlock (E := E') hs u v)
    rw [← hblk'] at hmem
    simpa [Set.image_pair] using hmem
  have hcd : π i.castSucc ≠ π j.castSucc := fun h =>
    hij (Fin.castSucc_injective r (π.injective h))
  have hab : π' u.castSucc ≠ π' v.castSucc := fun h =>
    huv (Fin.castSucc_injective s (π'.injective h))
  exact (ggBlockComm_commute_of_supported_swap
    (hF := hF) (hr := hr) (hcfg := hcfg) (hZ := hZ) (hN := hN)
    (hLeta := hLeta) (hpi := hpi) (hframe := hframe) (h𝒦 := h𝒦) (hG0 := hG0)
    (hn := hn) (a := π' u.castSucc) (b := π' v.castSucc)
    (c := π i.castSucc) (d := π j.castSucc) hab hcd hdisj.symm hzY hzN hzact)
    (κ' (normPerm E' hs (Equiv.swap u v))) hyY

end Forward

end CFSG.StandardType

end
