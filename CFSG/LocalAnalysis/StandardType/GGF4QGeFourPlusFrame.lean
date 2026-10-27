module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankBound
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveOrthMinusLayer
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndElt
public import CFSG.RankThree.PartOne.S11d.OrthCaseH
public import CFSG.RankThree.PartOne.S11d.OrthCyclic
public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Weak
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicProof
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import Certificates.Certificate9124
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.StandardType

namespace OmPlusFrame

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.WeirSylow CFSG.Assembly

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_plusBlocks (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hminus : ¬ IsPlusType Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ orthDerived Q)
    (hpow : ∀ a ∈ E, a ^ p = 1) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hcard : p ^ 3 ≤ Nat.card E) :
    ∃ (τ : (Fin 3 → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V)) (F : SevOm.Frame Q p E 3)
      (D : Type) (_ : AddCommGroup D) (_ : Module K D) (_ : FiniteDimensional K D)
      (c : D ≃ₗ[K] D) (θ : Fin 3 → D →ₗ[K] V),
      (∀ f, τ f = F.ι (OrthTorus.piMul 3 p f)) ∧ Function.Injective τ ∧ τ.range = E ∧
      finrank K D = 2 ∧ c ^ p = 1 ∧ (∀ u, c u = u → u = 0) ∧
      (∃ T : D ≃ₗ[K] D, T * c * T⁻¹ = c⁻¹) ∧
      (∀ j, Function.Injective (θ j)) ∧ (∀ j, LinearMap.range (θ j) = F.U j) ∧
      (∀ (s : Multiplicative (Fin 3 → ZMod p)) (j : Fin 3) (d : D),
        F.ι s (θ j d) = θ j ((c ^ (toAdd s j).val) d)) ∧
      (∀ j, finrank K (F.U j) = 2) ∧
      (∀ (j : Fin 3) (a : ZMod p), a ≠ 0 →
        CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle j (ofAdd a))) = F.U j) ∧
      ∀ g : V ≃ₗ[K] V, (∀ a ∈ E, g * a * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hbound : ∀ E' : Subgroup ↥(orthDerived Q), CFSG.Open.IsElemAbelian p E' →
      Nat.card E' ≤ p ^ 3 := fun E' hE' =>
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.card_le_pow_pred_of_isElemAbelian_orthDerived hQ
      (n := 4) (by omega) hminus (by norm_num) (by decide) hp hp2 hpq E' hE'
  set EΩ : Subgroup ↥(orthDerived Q) := E.subgroupOf (orthDerived Q) with hEΩdef
  have hcardEΩ : Nat.card EΩ = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩ).toEquiv
  have hEΩel : CFSG.Open.IsElemAbelian p EΩ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
    · simpa using hpow _ (Subgroup.mem_subgroupOf.mp ha)
  have hcard3 : Nat.card E = p ^ 3 := le_antisymm (hcardEΩ ▸ hbound EΩ hEΩel) hcard
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ E, g * c = c * g) → g ∈ E := by
    intro g hg hgp hgc
    set gΩ : ↥(orthDerived Q) := ⟨g, hg⟩
    have hz : CFSG.Open.IsElemAbelian p (Subgroup.zpowers gΩ) :=
      CFSG.Open.isElemAbelian_zpowers (Subtype.ext (by simpa [gΩ] using hgp))
    have hsup : CFSG.Open.IsElemAbelian p (EΩ ⊔ Subgroup.zpowers gΩ) := by
      refine CFSG.Open.IsElemAbelian.sup_of_commute hEΩel hz fun a ha b hb => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      have hag : Commute a gΩ := Subtype.ext (hgc _ (Subgroup.mem_subgroupOf.mp ha)).symm
      exact (hag.zpow_right k).eq
    have hle : EΩ ≤ EΩ ⊔ Subgroup.zpowers gΩ := le_sup_left
    have heq : EΩ = EΩ ⊔ Subgroup.zpowers gΩ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardEΩ, hcard3]; exact hbound _ hsup)
    have hgmem : gΩ ∈ EΩ := by
      rw [heq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers gΩ)
    exact Subgroup.mem_subgroupOf.mp hgmem
  have hne : ∃ b ∈ E, b ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr h
    rw [hbot, Subgroup.card_bot] at hcard3
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0 :=
    OrthRestOdd.exists_totallySingular_three Q hQ (by omega)
  obtain ⟨r, τ, F, D, _, _, _, c, θ, hτ, hτinj, hτrange, hD2, hcp, hcfix, hctw, -, hθinj,
    hθrange, hθact, hnorm, -, -, -, -, -⟩ := OrthTorus.exists_torus_blocks hp2 (Or.inr hpq) hQ hT
      hEΩ hpow hcomm hmax hne
  have hr : r = 3 := by
    have h1 : Nat.card E = p ^ r := by
      rw [← hτrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hτinj,
        Subgroup.card_top, Nat.card_fun, Nat.card_fin]
      show Nat.card (ZMod p) ^ r = p ^ r
      rw [Nat.card_zmod]
    rw [h1] at hcard3
    exact Nat.pow_right_injective hp.two_le hcard3
  subst hr
  have hU2 : ∀ j, finrank K (F.U j) = 2 := fun j => by
    rw [← hθrange j, LinearMap.finrank_range_of_inj (hθinj j), hD2]
  refine ⟨τ, F, D, inferInstance, inferInstance, inferInstance, c, θ, hτ, hτinj, hτrange, hD2,
    hcp, hcfix, hctw, hθinj, hθrange, hθact, hU2, fun j a ha => ?_, hnorm⟩
  set s : Fin 3 → Multiplicative (ZMod p) := Pi.mulSingle j (ofAdd a) with hs
  have hsE : τ s ∈ E := hτrange ▸ ⟨s, rfl⟩
  have hsp : τ s ^ p = 1 := hpow _ hsE
  have hpK : (p : K) ≠ 0 := OrthRestOdd.natCast_ne_zero_of_odd hp hp2
  have hfix : CFSG.RankThree.PartOne.LIT.fixedSpace (τ s) =
      LinearMap.BilinForm.orthogonal (polarBilin Q) (F.U j) := by
    ext v
    rw [CFSG.RankThree.PartOne.LIT.mem_fixedSpace, hτ, F.fix, LinearMap.BilinForm.mem_orthogonal_iff]
    have hcoord : ∀ j', toAdd (OrthTorus.piMul 3 p s) j' ≠ 0 ↔ j' = j := by
      intro j'
      rw [OrthTorus.piMul_apply, toAdd_ofAdd]
      by_cases hj : j' = j
      · subst hj
        simp [s, ha]
      · simp [s, Pi.mulSingle_eq_of_ne hj, hj]
    constructor
    · intro h u hu
      rw [polarBilin_apply_apply]
      exact h j ((hcoord j).mpr rfl) u hu
    · intro h j' hj' u hu
      rw [(hcoord j').mp hj'] at hu
      have := h u hu
      rwa [polarBilin_apply_apply] at this
  have hfix6 : finrank K (CFSG.RankThree.PartOne.LIT.fixedSpace (τ s)) = 6 := by
    rw [hfix, LinearMap.BilinForm.finrank_orthogonal hQ, hdim, hU2 j]
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hsp)
  have hc2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (τ s)) = 2 := by omega
  have hcoordj : toAdd (OrthTorus.piMul 3 p s) j ≠ 0 := by
    rw [OrthTorus.piMul_apply, toAdd_ofAdd]
    simp [s, ha]
  set N : V →ₗ[K] V := ((τ s : V ≃ₗ[K] V) : V →ₗ[K] V) - LinearMap.id with hN
  have hmaps : ∀ v ∈ F.U j, N v ∈ F.U j := by
    intro v hv
    simp only [hN, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
    exact (F.U j).sub_mem (by rw [hτ]; exact F.mapsTo _ j v hv) hv
  have hinj : Function.Injective (N.restrict hmaps) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    have h0 : (τ s) (v : V) - v = 0 := congrArg Subtype.val hv
    have h1 : F.ι (OrthTorus.piMul 3 p s) v = v := by
      rw [← hτ]
      exact sub_eq_zero.mp h0
    exact (Submodule.mem_bot K).mpr (Subtype.ext (F.fpf _ j hcoordj v v.2 h1))
  have hUle : F.U j ≤ CFSG.RankThree.PartOne.LIT.commSpace (τ s) := by
    intro u hu
    obtain ⟨u', hu'⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨u, hu⟩
    exact CFSG.RankThree.PartOne.LIT.mem_commSpace.mpr ⟨u', congrArg Subtype.val hu'⟩
  exact (Submodule.eq_of_le_of_finrank_eq hUle (by rw [hU2 j, hc2])).symm

theorem exists_plusFrame (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hminus : ¬ IsPlusType Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ orthDerived Q)
    (hpow : ∀ a ∈ E, a ^ p = 1) (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hcard : p ^ 3 ≤ Nat.card E) :
    ∃ τ : (Fin 3 → Multiplicative (ZMod p)) →* (V ≃ₗ[K] V),
      Function.Injective τ ∧ τ.range = E ∧
      (∀ (j : Fin 3) (a : ZMod p), a ≠ 0 →
        finrank K (CFSG.RankThree.PartOne.LIT.commSpace (τ (Pi.mulSingle j (ofAdd a)))) = 2) ∧
      ∀ g : V ≃ₗ[K] V, (∀ a ∈ E, g * a * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i) := by
  obtain ⟨τ, F, _, _, _, _, _, _, -, hτinj, hτrange, -, -, -, -, -, -, -, hU2, hcU, hnorm⟩ :=
    exists_plusBlocks hQ hdim hminus hp hp2 hpq hEΩ hpow hcomm hcard
  exact ⟨τ, hτinj, hτrange, fun j a ha => by rw [hcU j a ha, hU2 j], hnorm⟩

end Frame

section Signed

variable {p : ℕ}

@[expose] def spAct (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p) (v : Fin 3 → ZMod p) :
    Fin 3 → ZMod p :=
  fun k => ε (π.symm k) * v (π.symm k)

theorem spAct_apply_perm (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p) (v : Fin 3 → ZMod p)
    (i : Fin 3) : spAct π ε v (π i) = ε i * v i := by
  simp [spAct]

theorem spAct_apply_of_eq {π : Equiv.Perm (Fin 3)} {i m : Fin 3} (h : π i = m)
    (ε : Fin 3 → ZMod p) (v : Fin 3 → ZMod p) : spAct π ε v m = ε i * v i := by
  subst h
  exact spAct_apply_perm π ε v i

theorem spAct_one_apply (ε : Fin 3 → ZMod p) (v : Fin 3 → ZMod p) (l : Fin 3) :
    spAct 1 ε v l = ε l * v l :=
  rfl

theorem spAct_spAct (π π' : Equiv.Perm (Fin 3)) (ε ε' : Fin 3 → ZMod p) (v : Fin 3 → ZMod p) :
    spAct π ε (spAct π' ε' v) = spAct (π * π') (fun i => ε (π' i) * ε' i) v := by
  funext k
  simp only [spAct, Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.apply_symm_apply]
  ring

theorem perm_eq_one_of_spAct [Fact p.Prime] {ρ : Equiv.Perm (Fin 3)}
    (h : ∃ η : Fin 3 → ZMod p, ∀ v, spAct ρ η v = v) : ρ = 1 := by
  classical
  obtain ⟨η, h⟩ := h
  ext i
  by_contra hne
  have hne' : ρ.symm i ≠ i := fun h' => hne (by
    have := congrArg ρ h'
    rw [Equiv.apply_symm_apply] at this
    exact congrArg Fin.val this.symm)
  have h1 := congrFun (h (Pi.single i 1)) i
  simp only [spAct, Pi.single_eq_of_ne hne', Pi.single_eq_same, mul_zero] at h1
  exact zero_ne_one h1

theorem sign_ne_zero [Fact p.Prime] {e : ZMod p} (he : e = 1 ∨ e = -1) : e ≠ 0 := by
  rcases he with rfl | rfl
  · exact one_ne_zero
  · exact neg_ne_zero.mpr one_ne_zero

theorem two_ne_zero_zmod [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem perm_three_cases : ∀ π π' : Equiv.Perm (Fin 3), π * π = 1 → π' * π' = 1 →
    (π * π') ^ 4 = 1 → π = π' ∨ π = 1 ∨ π' = 1 := by
  decide

theorem perm_three_swap : ∀ π : Equiv.Perm (Fin 3), π * π = 1 → π ≠ 1 →
    ∃ i j k : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ π i = i ∧ π j = k ∧ π k = j := by
  decide

theorem fin_three_cases {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (l : Fin 3) :
    l = i ∨ l = j ∨ l = k := by
  revert i j k l
  decide

theorem spAct_comm_of_eq {π π' : Equiv.Perm (Fin 3)} {ε ε' : Fin 3 → ZMod p}
    (hπ : π * π' = π' * π) (hη : ∀ i, ε (π' i) * ε' i = ε' (π i) * ε i) (v : Fin 3 → ZMod p) :
    spAct π ε (spAct π' ε' v) = spAct π' ε' (spAct π ε v) := by
  rw [spAct_spAct, spAct_spAct, hπ]
  congr 1
  funext i
  exact hη i

theorem eq_single_of_spAct_diag_swap [Fact p.Prime] (hp2 : p ≠ 2) {π' : Equiv.Perm (Fin 3)}
    {ε ε' : Fin 3 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : π' i = i) (hj : π' j = k)
    (hk : π' k = j)
    (hnc : ∃ w, spAct 1 ε (spAct π' ε' w) ≠ spAct π' ε' (spAct 1 ε w))
    {v : Fin 3 → ZMod p} (hv : spAct 1 ε v = v) (hv' : spAct π' ε' v = v) :
    ∀ l, l ≠ i → v l = 0 := by
  have hvl : ∀ l, v l = ε l * v l := fun l => by
    have := congrFun hv l
    rw [spAct_one_apply] at this
    exact this.symm
  have hvj : v k = ε' j * v j := by
    have := spAct_apply_of_eq hj ε' v
    rwa [hv'] at this
  have hvk : v j = ε' k * v k := by
    have := spAct_apply_of_eq hk ε' v
    rwa [hv'] at this
  have hsign : ε j = -1 ∨ ε k = -1 := by
    by_contra hcon
    push Not at hcon
    have hεj : ε j = 1 := (hε j).resolve_right hcon.1
    have hεk : ε k = 1 := (hε k).resolve_right hcon.2
    obtain ⟨w, hw⟩ := hnc
    apply hw
    refine spAct_comm_of_eq (by rw [one_mul, mul_one]) (fun l => ?_) w
    simp only [Equiv.Perm.one_apply]
    rcases fin_three_cases hij hik hjk l with h | h | h
    · rw [h, hi]
      ring
    · rw [h, hj, hεj, hεk]
      ring
    · rw [h, hk, hεj, hεk]
      ring
  have hzero : ∀ {m : Fin 3}, ε m = -1 → v m = 0 := by
    intro m hm
    have h1 := hvl m
    rw [hm] at h1
    have h2 : (2 : ZMod p) * v m = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero_zmod hp2)
  have hj0 : v j = 0 ∧ v k = 0 := by
    rcases hsign with h | h
    · have h0 := hzero h
      exact ⟨h0, by rw [hvj, h0, mul_zero]⟩
    · have h0 := hzero h
      exact ⟨by rw [hvk, h0, mul_zero], h0⟩
  intro l hl
  rcases fin_three_cases hij hik hjk l with h | h | h <;> subst h
  · exact absurd rfl hl
  · exact hj0.1
  · exact hj0.2

theorem eq_single_of_spAct_pair [Fact p.Prime] (hp2 : p ≠ 2) {π π' : Equiv.Perm (Fin 3)}
    {ε ε' : Fin 3 → ZMod p} (hε : ∀ i, ε i = 1 ∨ ε i = -1) (hε' : ∀ i, ε' i = 1 ∨ ε' i = -1)
    (h2 : ∀ v, spAct π ε (spAct π ε v) = v) (h2' : ∀ v, spAct π' ε' (spAct π' ε' v) = v)
    (h4 : ∀ v, spAct π ε (spAct π' ε' (spAct π ε (spAct π' ε' (spAct π ε (spAct π' ε'
      (spAct π ε (spAct π' ε' v))))))) = v)
    (hnc : ∃ w, spAct π ε (spAct π' ε' w) ≠ spAct π' ε' (spAct π ε w))
    {v : Fin 3 → ZMod p} (hv : spAct π ε v = v) (hv' : spAct π' ε' v = v) :
    ∃ j, ∀ i, i ≠ j → v i = 0 := by
  have hπ2 : π * π = 1 :=
    perm_eq_one_of_spAct ⟨_, fun v => (spAct_spAct π π ε ε v).symm.trans (h2 v)⟩
  have hπ'2 : π' * π' = 1 :=
    perm_eq_one_of_spAct ⟨_, fun v => (spAct_spAct π' π' ε' ε' v).symm.trans (h2' v)⟩
  have hdiag : ∀ {η η' : Fin 3 → ZMod p}, ∀ w, spAct 1 η (spAct 1 η' w) =
      spAct 1 η' (spAct 1 η w) := fun w =>
    spAct_comm_of_eq rfl (fun i => by simp only [Equiv.Perm.one_apply]; ring) w
  have h4π : (π * π') ^ 4 = 1 := by
    have key : π * (π' * (π * (π' * (π * (π' * (π * π')))))) = 1 :=
      perm_eq_one_of_spAct ⟨_, fun w => by simpa only [spAct_spAct] using h4 w⟩
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using key
  rcases perm_three_cases π π' hπ2 hπ'2 h4π with heq | h1 | h1'
  ·
    subst heq
    by_cases hπ1 : π = 1
    · subst hπ1
      obtain ⟨w, hw⟩ := hnc
      exact absurd (hdiag w) hw
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := perm_three_swap π hπ2 hπ1
    have hjk1 : ∀ {η : Fin 3 → ZMod p}, (∀ v, spAct π η (spAct π η v) = v) → η k * η j = 1 := by
      intro η hη2
      have h1 := congrFun (hη2 (Pi.single j 1)) j
      rw [spAct_apply_of_eq hk, spAct_apply_of_eq hj, Pi.single_eq_same, mul_one] at h1
      exact h1
    have hk1 := hjk1 h2
    have hk1' := hjk1 h2'
    by_cases hs : ε j = ε' j
    · have hsk : ε k = ε' k := by
        have hεj : ε j ≠ 0 := sign_ne_zero (hε j)
        have : ε k * ε j = ε' k * ε j := by rw [hk1, hs, hk1']
        exact mul_right_cancel₀ hεj this
      obtain ⟨w, hw⟩ := hnc
      exfalso
      apply hw
      refine spAct_comm_of_eq rfl (fun l => ?_) w
      rcases fin_three_cases hij hik hjk l with h | h | h
      · rw [h, hi]
        ring
      · rw [h, hj, hs, hsk]
      · rw [h, hk, hs, hsk]
    · have hs' : ε' j = -ε j := by
        rcases hε j with h | h <;> rcases hε' j with h' | h'
        · exact absurd (h.trans h'.symm) hs
        · rw [h, h']
        · rw [h, h', neg_neg]
        · exact absurd (h.trans h'.symm) hs
      have hvk : v k = ε j * v j := by
        have := spAct_apply_of_eq hj ε v
        rwa [hv] at this
      have hvk' : v k = ε' j * v j := by
        have := spAct_apply_of_eq hj ε' v
        rwa [hv'] at this
      have h2v : (2 : ZMod p) * (ε j * v j) = 0 := by
        rw [hs'] at hvk'
        linear_combination hvk' - hvk
      have hvj : v j = 0 := by
        have h3 := (mul_eq_zero.mp h2v).resolve_left (two_ne_zero_zmod hp2)
        exact (mul_eq_zero.mp h3).resolve_left (sign_ne_zero (hε j))
      refine ⟨i, fun l hl => ?_⟩
      rcases fin_three_cases hij hik hjk l with h | h | h <;> subst h
      · exact absurd rfl hl
      · exact hvj
      · rw [hvk, hvj, mul_zero]
  ·
    subst h1
    by_cases hπ'1 : π' = 1
    · subst hπ'1
      obtain ⟨w, hw⟩ := hnc
      exact absurd (hdiag w) hw
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := perm_three_swap π' hπ'2 hπ'1
    exact ⟨i, eq_single_of_spAct_diag_swap hp2 hε hij hik hjk hi hj hk hnc hv hv'⟩
  ·
    subst h1'
    by_cases hπ1 : π = 1
    · subst hπ1
      obtain ⟨w, hw⟩ := hnc
      exact absurd (hdiag w) hw
    obtain ⟨i, j, k, hij, hik, hjk, hi, hj, hk⟩ := perm_three_swap π hπ2 hπ1
    obtain ⟨w, hw⟩ := hnc
    exact ⟨i, eq_single_of_spAct_diag_swap hp2 hε' hij hik hjk hi hj hk ⟨w, fun h => hw h.symm⟩
      hv' hv⟩

end Signed

section Layer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem eq_one_of_pow_eq_one_of_dvd_add_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) : ∀ c : K, c ^ p = 1 → c = 1 := by
  classical
  intro c hc
  haveI := Fintype.ofFinite K
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact zero_ne_one hc
  have hq : c ^ (Nat.card K - 1) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one c hc0
  have hndvd : ¬ p ∣ Nat.card K - 1 := by
    intro h
    have h1 : 1 ≤ Nat.card K := Nat.card_pos
    have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h
    have h3 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h3] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hcop : Nat.Coprime p (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
  have h := (pow_gcd_eq_one (a := c) (m := p) (n := Nat.card K - 1)).mpr ⟨hc, hq⟩
  rwa [hcop.gcd_eq_one, pow_one] at h

theorem oddOrderIsometry_of_orthDerived (hQ : (polarBilin Q).Nondegenerate) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {t : orthDerived Q} (htp : t ^ p = 1) :
    OddOrderIsometry Q p (t : V ≃ₗ[K] V) :=
  ⟨orthDerived_le_orthogonalGroup t.2, by rw [← Subgroup.coe_pow, htp]; rfl,
    OrthRestOdd.natCast_ne_zero_of_odd hp hp2,
    fun v hv => hQ.1 v fun w => by rw [polarBilin_apply_apply]; exact hv w⟩

theorem isPlusType_fixedSpace_of_commSpace_two (hdim : finrank K V = 8) (hminus : ¬ IsPlusType Q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x)
    (h2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace x) = 2) :
    finrank K (fixedSpace x) = 6 ∧ IsPlusType (Q.comp (fixedSpace x).subtype) := by
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero
    hx.pow_eq_one
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have h6 : finrank K (fixedSpace x) = 6 := by
    rw [OrthRestOdd.fixedSpace_eq_lit]
    omega
  refine ⟨h6, ?_⟩
  obtain ⟨s, k, hs, hk, hsk, htype⟩ :=
    CFSG.HardMathSupport.Dickson.Bal207.OrthFix.fixed_type' hx hp hp2 hpq (n := 4) hdim
  have hk1 : k = 1 := by omega
  exact (htype (by omega)).mpr (iff_of_false hminus (by rw [hk1]; decide))

theorem exists_three_of_isPlusType {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {R : QuadraticForm K W} (hW : finrank K W = 6) (h : IsPlusType R) :
    ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0 := by
  obtain ⟨U, hU, hUs⟩ := h
  exact ⟨U, by omega, hUs⟩

theorem mem_layer_of_two_pow (hQ : (polarBilin Q).Nondegenerate) (hV : 8 ≤ finrank K V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {t : orthDerived Q}
    (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2)
    (hT : ∃ U : Submodule K (fixedSpace (t : V ≃ₗ[K] V)), finrank K U = 3 ∧
      ∀ u ∈ U, Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype u = 0)
    {g : orthDerived Q} (hg : g ∈ Subgroup.centralizer ({t} : Set (orthDerived Q))) {k : ℕ}
    (hgk : g ^ (2 ^ k) = 1) :
    g ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) := by
  classical
  rw [IOneOrthEnd.layer_eq_of_commSpace_two hQ hV hp hp2 hK1 htp ht2, Subgroup.mem_subgroupOf]
  have hx := oddOrderIsometry_of_orthDerived hQ hp hp2 htp
  set x : V ≃ₗ[K] V := (t : V ≃ₗ[K] V) with hxdef
  have hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1 := fun h hh hne =>
    (OrthRestOdd.primaryMultiplicity_eq_one hx hK1 ht2 hh hne).le
  have hgC : (g : V ≃ₗ[K] V) ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp hg
    exact congrArg Subtype.val this
  have hgk' : (g : V ≃ₗ[K] V) ^ (2 ^ k) = 1 := by
    rw [← Subgroup.coe_pow, hgk]
    rfl
  have hgR := hx.apply_eq_of_two_pow hmult hgC hgk'
  have hgM : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q x :=
    Subgroup.mem_inf.mpr ⟨orthDerived_le_orthogonalGroup g.2, hgC⟩
  have hblock : (g : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) := mem_supportedBlock.mpr ⟨hgM, hgR⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hx.cast_ne_zero
    hx.pow_eq_one
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hr : (X - 1 : K[X]) ∈ primaryFactors x.toLinearMap := by
    by_contra hnot
    have hbot := fixedSpace_eq_bot_of_not_mem hnot
    have h0 : finrank K (fixedSpace x) = 0 := by rw [hbot, finrank_bot]
    rw [OrthRestOdd.fixedSpace_eq_lit] at h0
    omega
  have hdick := dicksonHom_apply_orthDerived_eq_one hQ g.2
  rw [hx.dicksonHom_eq_restrict_of_mem_supportedBlock (hp.odd_of_ne_two hp2) hQ hr hblock]
    at hdick
  have hD := CFSG.RankThree.PartOne.dicksonDerived_of_threeSingular
    (Q.comp (fixedSpace x).subtype) hx.polarBilin_fixed_nondegenerate hT
  exact mem_supportedFixedDerived.mpr ⟨hblock, hD _ hdick⟩

theorem dvd_card_orthDerived_of_dvd {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] {R : QuadraticForm K W} (hR : (polarBilin R).Nondegenerate)
    (hW : 6 ≤ finrank K W) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hdvd : ℓ ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R)) :
    ℓ ∣ Nat.card (orthDerived R) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hgℓ : (g : W ≃ₗ[K] W) ^ ℓ = 1 := by
    have h1 := pow_orderOf_eq_one g
    rw [hg] at h1
    exact congrArg Subtype.val h1
  obtain ⟨-, -, hodd⟩ := OrthRestOdd.orthDerived_facts R hR hW
  have hgΩ : (g : W ≃ₗ[K] W) ∈ orthDerived R :=
    hodd g g.2 ℓ (hℓ.odd_of_ne_two hℓ2) hgℓ
  have hord : orderOf (⟨(g : W ≃ₗ[K] W), hgΩ⟩ : orthDerived R) = ℓ := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem layer_facts (hQ : (polarBilin Q).Nondegenerate) (hdim : finrank K V = 8)
    (hminus : ¬ IsPlusType Q) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) {t : orthDerived Q}
    (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    Nonempty (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) ≃*
        Matrix.SpecialLinearGroup (Fin 4) K) ∧
      Subgroup.center (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q)))) = ⊥ ∧
      7 ∣ Nat.card (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q)))) ∧
      p ∣ Nat.card (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q)))) := by
  classical
  have hK1 := eq_one_of_pow_eq_one_of_dvd_add_one hp hp2 hpq
  have hx := oddOrderIsometry_of_orthDerived hQ hp hp2 htp
  obtain ⟨h6, hplus⟩ := isPlusType_fixedSpace_of_commSpace_two hdim hminus hp hp2 hpq hx ht2
  have hT := exists_three_of_isPlusType h6 hplus
  have hR := hx.polarBilin_fixed_nondegenerate
  obtain ⟨e⟩ := IOneOrthEnd.layer_equiv_of_commSpace_two hQ (by omega) hp hp2 hK1 htp ht2
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype) hR h6 hT hK4
  have eSL : LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) ≃*
      Matrix.SpecialLinearGroup (Fin 4) K :=
    ((e.trans (CFSG.RankThree.PartOne.orthDerivedEquivCommutator _).symm).trans κ).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 K).symm
  obtain ⟨-, hcen, -⟩ := OrthRestOdd.orthDerived_facts _ hR (by omega)
  have hcardO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (2 * (2 + 1)) * ((Nat.card K : ℤ) ^ (2 + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 2, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    natCard_orthogonalGroup_of_type hR (m := 2) (by rw [h6]) (Or.inl ⟨rfl, hplus⟩)
  refine ⟨⟨eSL⟩, ?_, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply e.symm.injective
      rw [map_mul, map_mul, e.symm_apply_apply]
      exact hz (e.symm g)
    rw [hcen, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← e.symm_apply_apply z, hz', map_one]
  · rw [Nat.card_congr e.toEquiv]
    refine dvd_card_orthDerived_of_dvd hR (by omega) (by norm_num) (by norm_num) ?_
    have h7 : (7 : ℤ) ∣ (Nat.card K : ℤ) ^ (2 + 1) - 1 := by
      have h1 : (Nat.card K : ℤ) ^ (2 + 1) = (8 : ℤ) ^ f := by
        rw [hK]
        push_cast
        rw [show (8 : ℤ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_mul]
        ring_nf
      have h2 : (8 : ℤ) - 1 ∣ (8 : ℤ) ^ f - 1 ^ f := sub_dvd_pow_sub_pow _ _ _
      rw [h1]
      rw [one_pow] at h2
      exact (show (7 : ℤ) ∣ 8 - 1 by norm_num).trans h2
    have h7O : (7 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype)) : ℤ) := by
      rw [hcardO]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h7 _) _
    exact_mod_cast h7O
  · rw [Nat.card_congr e.toEquiv]
    refine dvd_card_orthDerived_of_dvd hR (by omega) hp hp2 ?_
    have hp1 : (p : ℤ) ∣ ((Nat.card K : ℤ) ^ 2) ^ 1 - 1 := by
      have h1 : ((Nat.card K : ℤ) ^ 2) ^ 1 - 1 =
          ((Nat.card K : ℤ) + 1) * ((Nat.card K : ℤ) - 1) := by ring
      rw [h1]
      exact Dvd.dvd.mul_right (by exact_mod_cast hpq) _
    have hprod : (p : ℤ) ∣ ∏ i ∈ Finset.Icc 1 2, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
      hp1.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, by norm_num⟩))
    have hpO : (p : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup
        (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype)) : ℤ) := by
      rw [hcardO]
      exact Dvd.dvd.mul_left hprod _
    exact_mod_cast hpO

end Layer

end OmPlusFrame

end CFSG.StandardType

end
