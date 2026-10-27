module

public import CFSG.Quasithin.H13.NQBlockRadicalControl
public import CFSG.Quasithin.H13.NQBlockTwoPrimeOnePrime
public import CFSG.Quasithin.H13.NQCatTitsLocal
public import CFSG.Quasithin.H13.NQCatJ4Frattini
public import CFSG.Quasithin.H13.NQTermUnipotentPlane
public import CFSG.RankThree.GroupTheory.SteinbergBMFrattiniNormalizerTwoCore

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.Open hiding StatedClassicalModel StatedCyclePerm StatedLieAdmissible StatedLieTag
  StatedM11 StatedOmega StatedProj StatedQuadMinus StatedQuadOdd StatedQuadPlus StatedSL StatedSU
  StatedScalars StatedSp

section Alternatives

variable {K : Type} [Group K] [Finite K]

theorem ambient_witness_alternatives (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hK : CFSG.SectionRank.IsSQTKCat K) (hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    {T A : Subgroup K} (hT : quasithinIsSylowTwo T) (hA : A ∈ cComp (A ⊔ T))
    (hAq : ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup K} (hXA : X ≤ A) (hXn : (X.subgroupOf A).Normal)
    (hTX : T ≤ normalizer (X : Set K))
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hXr : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) :
    (∃ ℓ : ℕ, ℓ.Prime ∧ 5 ≤ ℓ ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) .PSL 3 ℓ 1) ∨
      (Nonempty (((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* NativeSporadic.J4) ∧
        p = 11) := by
  obtain ⟨⟨hsimple, hnab⟩, hcat, hsqt, -, hTb, hAb, hAbq, -⟩ :=
    NQTerm.quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses hK hQ hT
      hA hAq
  have := hsimple
  let Ts : Sylow 2 ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) := hTb.1.toSylow hTb.2
  have hBS : A.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))) ∈ cComp (A.map ((QuotientGroup.mk'
        (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))) ⊔
          (Ts : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)))) := hAb
  obtain ⟨hXpB, -, -, -, -, Up, hUpX, hUp, hUpnc, hUpT⟩ :=
    ambient_witness_data hK hQ hT hA hAq hp hp5 hXA hXn hTX hX2 hXp hXr
  rcases hCat _ hnab hcat hsqt p hp hp5 Ts Up hUp hUpnc hUpT with
    ⟨ℓ, hℓ, hℓ5, hPSL | hPSU⟩ | ⟨f, hf3, hPSL2⟩ | ⟨f, hf2, hSp⟩ | hexc | hree | hJ4
  · exact Or.inl ⟨ℓ, hℓ, hℓ5, hPSL⟩
  · exact (not_statedPSU_three hnab Ts hBS hAbq hPSU).elim
  · exact (not_statedPSL_three_two hnab Ts hBS hAbq (by omega) hPSL2).elim
  · exact (not_statedPSp_four_two hnab Ts hBS hAbq (by omega) hSp).elim
  · exfalso
    rcases hexc with hG2 | hD4
    · exact hUpnc (isCyclic_of_even_exceptional_model hnab hTb hAb hAbq (Or.inl hG2) hp
        (by omega) (hUpX.trans hXpB) hUp)
    · exact hUpnc (isCyclic_of_even_exceptional_model hnab hTb hAb hAbq (Or.inr (Or.inl hD4)) hp
        (by omega) (hUpX.trans hXpB) hUp)
  · exfalso
    rcases hree with hF4 | hTits
    · exact hUpnc (isCyclic_of_even_exceptional_model hnab hTb hAb hAbq (Or.inr (Or.inr hF4)) hp
        (by omega) (hUpX.trans hXpB) hUp)
    · obtain ⟨eT⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv (h := hTits)
      have hlt := sup_lt_top_of_not_quasisimple hnab hBS hAbq
      have htopS : IsSimpleGroup ↥(⊤ : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸
          center (K ⧸ CFSG.pCore 2 K))) := MulEquiv.isSimpleGroup Subgroup.topEquiv
      have htopnab : ∃ a b : ↥(⊤ : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸
          center (K ⧸ CFSG.pCore 2 K))), a * b ≠ b * a := by
        obtain ⟨a, b, hab⟩ := hnab
        exact ⟨⟨a, mem_top a⟩, ⟨b, mem_top b⟩, fun h => hab (congrArg Subtype.val h)⟩
      obtain ⟨hBtop, -⟩ := NQCat.Tits_actual_Sylow_local_component_equality Ts htopS htopnab
        Subgroup.IsSubnormal.top (Subgroup.topEquiv.trans eT) le_top hBS
      apply hlt.ne
      rw [hBtop]
      exact top_sup_eq _
  · exact Or.inr hJ4

end Alternatives

@[expose] def PrimeLinearThreeAmbientPlane : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (K : Type) [Group K] [Finite K] (q : ℕ) [Fact q.Prime],
    Nat.card F = q → 5 ≤ q →
    ∀ (D : Subgroup (CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F)) [D.Normal],
      D ≤ CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F →
      ∀ (α : K ⧸ CFSG.pCore 2 K ≃* CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F ⧸ D)
        (S : Sylow 2 K) (A : Subgroup K), A ∈ cComp (A ⊔ (S : Subgroup K)) →
        ¬ CFSG.IsQuasisimple (↥A ⧸ CFSG.pCore 2 ↥A) →
        ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup K, X ≤ A → (X.subgroupOf A).Normal →
          (∀ (Y : Subgroup ↥X) [Y.Normal], IsPGroup 2 (↥X ⧸ Y) → Y = ⊤) →
          IsPGroup p (↥X ⧸ CFSG.pCore 2 ↥X) → CFSG.pRank p (↥X ⧸ CFSG.pCore 2 ↥X) = 2 →
          p = q ∧ ∃ V : Submodule F (Fin 3 → F),
            (Module.finrank F V = 1 ∨ Module.finrank F V = 2) ∧
            X.map (α.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 K))) =
              (CFSG.LieType.SteinbergBR.BlockPar.radU F V).map (QuotientGroup.mk' D)

section LinearThree

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj elationSubgroup
  elationGenerators projElationSubgroup scalars_eq_center)

theorem radU_eq_elationSubgroup {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hF : Nat.card F = p) (V : Submodule F (Fin 3 → F))
    (hV : Module.finrank F V = 1 ∨ Module.finrank F V = 2) :
    CFSG.LieType.SteinbergBR.BlockPar.radU F V = elationSubgroup V := by
  obtain ⟨⟨hset, -⟩, -⟩ :=
    NQTerm.prime_linear_three_unipotent_plane_normalizes_no_two_subgroup hp hp5 hF V hV
  ext g
  have h1 : g ∈ elationSubgroup V ↔ g ∈ elationGenerators V := by
    rw [← SetLike.mem_coe, hset]
  rw [h1]
  constructor
  · rintro ⟨h2, h3⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact h2 v
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec, h3 v hv, sub_self]
  · rintro ⟨h2, h3⟩
    refine ⟨fun v => ?_, fun w hw => ?_⟩
    · have h4 := h2 v
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h4
    · have h4 := h3 w hw
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h4

@[expose] def mulAutConjHom {S P : Type*} [Group S] [Group P] (β : S ≃* P) :
    MulAut S →* MulAut P where
  toFun σ := (β.symm.trans σ).trans β
  map_one' := by
    ext w
    simp
  map_mul' σ τ := by
    ext w
    simp [MulAut.mul_apply]

theorem mulAutConjHom_apply {S P : Type*} [Group S] [Group P] (β : S ≃* P) (σ : MulAut S)
    (y : S) : mulAutConjHom β σ (β y) = β (σ y) := by
  simp [mulAutConjHom]

theorem mulAutConjHom_injective {S P : Type*} [Group S] [Group P] (β : S ≃* P) :
    Function.Injective (mulAutConjHom β) := by
  intro σ τ h
  ext y
  have h1 := congrArg (fun φ : MulAut P => φ (β y)) h
  simp only [mulAutConjHom_apply] at h1
  exact β.injective h1

variable {G : Type} [Group G] [Finite G]

theorem normal_of_linear_three_escape (hPLU : PrimeLinearThreeAmbientPlane)
    {T X KC : Subgroup G} (hSQTK : CFSG.SectionRank.IsSQTKCat KC)
    (hKq : CFSG.IsQuasisimple (↥KC ⧸ CFSG.pCore 2 ↥KC)) {AK : Subgroup KC}
    (hTKs : quasithinIsSylowTwo (T.subgroupOf KC))
    (hAKc : AK ∈ cComp (AK ⊔ T.subgroupOf KC))
    (hAqK : ¬ CFSG.IsQuasisimple (↥AK ⧸ CFSG.pCore 2 ↥AK))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hXK : X ≤ KC) (hXpA : X.subgroupOf KC ≤ AK)
    (hXpn : ((X.subgroupOf KC).subgroupOf AK).Normal)
    (hTXp : T.subgroupOf KC ≤ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC))
    (hXp2 : ∀ (N : Subgroup (X.subgroupOf KC)) [N.Normal],
      IsPGroup 2 ((X.subgroupOf KC) ⧸ N) → N = ⊤)
    (hXpp : IsPGroup p (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)))
    (hXpr : CFSG.pRank p (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) = 2) {ℓ : ℕ}
    (hℓ5 : 5 ≤ ℓ) (hPSL : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC)) .PSL 3 ℓ 1)
    (hTKC : T ≤ normalizer (KC : Set G)) (hO2KT : pCoreOf 2 KC ≤ T)
    (hRX : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (X : Set G)) :
    (X.subgroupOf KC).Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hQperf : Group.IsPerfect (↥KC ⧸ CFSG.pCore 2 ↥KC) := hKq.1
  obtain ⟨⟨hsimple, hnab⟩, -, -, -, hTb, hAb, hAbq, hwit⟩ :=
    NQTerm.quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses hSQTK hKq
      hTKs hAKc hAqK
  have := hsimple
  let Ts : Sylow 2 ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC)) :=
    hTb.1.toSylow hTb.2
  obtain ⟨hXbn, -, hXb2, ⟨e, -⟩, -⟩ := hwit p hp hp5 _ hXpA hXpn hTXp hXp2 hXpp hXpr
  have hXbp := IsPGroup.of_equiv hXpp e
  have hXbr := (CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv e p).symm.trans hXpr
  obtain ⟨⟨hℓ, -⟩, F, _, _, hF, ⟨eM⟩⟩ := hPSL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hF' : Nat.card F = ℓ := by rw [hF, pow_one]
  have hO2 := pCore_two_eq_bot_of_simple hnab
  let α : ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC)) ⧸
      CFSG.pCore 2 ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC)) ≃*
        CFSG.Wreathed.OddLinearThreeCentralizerCore.SL3 F ⧸
          CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 F :=
    ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).trans
      ((eM.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
        (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 3 F).symm))
  obtain ⟨hpℓ, V, hV, hmap⟩ := hPLU F _ ℓ hF' hℓ5 _ le_rfl α Ts _ hAb hAbq p (by omega) _
    (Subgroup.map_mono hXpA) hXbn hXb2 hXbp hXbr
  subst hpℓ
  have hβinj : Function.Injective (α.toMonoidHom.comp (QuotientGroup.mk'
      (CFSG.pCore 2 ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC))))) := by
    intro a b h
    have h1 := α.injective h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hO2,
      Subgroup.mem_bot] at h1
    exact inv_mul_eq_one.mp h1
  have hβsurj : Function.Surjective (α.toMonoidHom.comp (QuotientGroup.mk'
      (CFSG.pCore 2 ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC))))) := by
    intro y
    obtain ⟨z, rfl⟩ := α.surjective y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ z
    exact ⟨a, rfl⟩
  let β : ((↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC)) ≃* projectiveSL 3 F :=
    MulEquiv.ofBijective _ ⟨hβinj, hβsurj⟩
  have hβ : β.toMonoidHom = α.toMonoidHom.comp (QuotientGroup.mk' _) := MonoidHom.ext fun _ => rfl
  have hβX : ((X.subgroupOf KC).map ((QuotientGroup.mk' (center (↥KC ⧸ CFSG.pCore 2 ↥KC))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥KC)))).map β.toMonoidHom = projElationSubgroup V := by
    rw [hβ, hmap, radU_eq_elationSubgroup hp hp5 hF' V hV]
    try rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, hQ2⟩ :=
    NQTerm.prime_linear_three_unipotent_plane_normalizes_no_two_subgroup hp hp5 hF' V hV
  let ψ₀ : ↥(normalizer (KC : Set G)) →* MulAut (projectiveSL 3 F) :=
    (mulAutConjHom β).comp
      ((CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom
        (↥KC ⧸ CFSG.pCore 2 ↥KC)).comp
        ((CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 ↥KC)).comp KC.normalizerMonoidHom))
  have hψ₀ : ∀ (n : ↥(normalizer (KC : Set G))) (k : ↥KC), ψ₀ n (β
      ((QuotientGroup.mk' (center (↥KC ⧸ CFSG.pCore 2 ↥KC)))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥KC) k))) =
      β ((QuotientGroup.mk' (center (↥KC ⧸ CFSG.pCore 2 ↥KC)))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥KC) (KC.normalizerMonoidHom n k))) := by
    intro n k
    simp only [ψ₀, MonoidHom.coe_comp, Function.comp_apply, mulAutConjHom_apply]
    congr 1
  have hXN : X ≤ normalizer (KC : Set G) := hXK.trans Subgroup.le_normalizer
  have hconjX : ∀ (x : G) (hx : x ∈ X), ψ₀ ⟨x, hXN hx⟩ = MulAut.conj (β
      ((QuotientGroup.mk' (center (↥KC ⧸ CFSG.pCore 2 ↥KC)))
        (QuotientGroup.mk' (CFSG.pCore 2 ↥KC) ⟨x, hXK hx⟩))) := by
    intro x hx
    refine MulEquiv.ext fun w => ?_
    obtain ⟨σv, rfl⟩ := β.surjective w
    obtain ⟨qv, rfl⟩ := QuotientGroup.mk'_surjective (center (↥KC ⧸ CFSG.pCore 2 ↥KC)) σv
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥KC) qv
    rw [hψ₀, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
    congr 1
  have hR2 : IsPGroup 2 (pCoreOf 2 (X ⊔ T)) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXTR : X ⊔ T ≤ normalizer (pCoreOf 2 (X ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (X ⊔ T)
  have hRN : pCoreOf 2 (X ⊔ T) ≤ normalizer (KC : Set G) :=
    (Subgroup.map_subtype_le _).trans (sup_le hXN hTKC)
  have hKE : normalizer (KC : Set G) ≤ normalizer (pCoreOf 2 KC : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) KC
  have hER : pCoreOf 2 KC ≤ pCoreOf 2 (X ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hO2KT.trans le_sup_right)
      (sup_le (hXN.trans hKE) (hTKC.trans hKE)) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 KC)
  have hQ'2 : IsPGroup 2 (((pCoreOf 2 (X ⊔ T)).subgroupOf (normalizer (KC : Set G))).map ψ₀) :=
    (hR2.of_equiv (subgroupOfEquivOfLe hRN).symm).map ψ₀
  have hQ'N : (projElationSubgroup V).map MulAut.conj ≤ normalizer
      ((((pCoreOf 2 (X ⊔ T)).subgroupOf (normalizer (KC : Set G))).map ψ₀ :
        Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [← hβX] at hu
    obtain ⟨_, ⟨x', hx', rfl⟩, rfl⟩ := hu
    have hx'G : (x' : G) ∈ X := hx'
    have h1 := hconjX (x' : G) hx'G
    have h2 : MulAut.conj (β.toMonoidHom (((QuotientGroup.mk'
        (center (↥KC ⧸ CFSG.pCore 2 ↥KC))).comp (QuotientGroup.mk' (CFSG.pCore 2 ↥KC))) x')) =
          ψ₀ ⟨(x' : G), hXN hx'G⟩ := h1.symm
    rw [h2]
    exact Subgroup.le_normalizer_map ψ₀ (Subgroup.mem_map_of_mem _
      (mem_normalizer_subgroupOf_of_mem (hXTR (Subgroup.mem_sup_left hx'G))))
  have hQ'1 := hQ2 _ hQ'2 hQ'N
  have hRtriv : ∀ r ∈ pCoreOf 2 (X ⊔ T), ∀ k ∈ KC, (r * k * r⁻¹)⁻¹ * k ∈ pCoreOf 2 KC := by
    intro r hr k hk
    have h1 : ψ₀ ⟨r, hRN hr⟩ = 1 := by
      have h2 : ψ₀ ⟨r, hRN hr⟩ ∈ (((pCoreOf 2 (X ⊔ T)).subgroupOf
          (normalizer (KC : Set G))).map ψ₀) := Subgroup.mem_map_of_mem _ hr
      rw [hQ'1, Subgroup.mem_bot] at h2
      exact h2
    have h3 : (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 ↥KC))
        (KC.normalizerMonoidHom ⟨r, hRN hr⟩) = 1 := by
      apply CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
        (↥KC ⧸ CFSG.pCore 2 ↥KC)
      rw [map_one]
      apply mulAutConjHom_injective β
      rw [map_one]
      exact h1
    have h4 := congrArg (fun φ : MulAut (↥KC ⧸ CFSG.pCore 2 ↥KC) =>
      φ (QuotientGroup.mk' (CFSG.pCore 2 ↥KC) ⟨k, hk⟩)) h3
    simp only [MulAut.one_apply] at h4
    change ((QuotientGroup.mk' (CFSG.pCore 2 ↥KC)) (KC.normalizerMonoidHom ⟨r, hRN hr⟩ ⟨k, hk⟩) :
      ↥KC ⧸ CFSG.pCore 2 ↥KC) = QuotientGroup.mk' (CFSG.pCore 2 ↥KC) ⟨k, hk⟩ at h4
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h4
    have h5 : ((KC.normalizerMonoidHom ⟨r, hRN hr⟩ ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥KC) ∈
        CFSG.Open.pCore 2 ↥KC := by
      exact h4
    exact ⟨_, h5, rfl⟩
  have hconjR : ∀ k ∈ KC, ∀ r ∈ pCoreOf 2 (X ⊔ T), k * r * k⁻¹ ∈ pCoreOf 2 (X ⊔ T) := by
    intro k hk r hr
    have h1 := hER (hRtriv r hr k⁻¹ (KC.inv_mem hk))
    have h2 : ((r * k⁻¹ * r⁻¹)⁻¹ * k⁻¹)⁻¹ * r = k * r * k⁻¹ := by group
    rw [← h2]
    exact (pCoreOf 2 (X ⊔ T)).mul_mem ((pCoreOf 2 (X ⊔ T)).inv_mem h1) hr
  have hKR : KC ≤ normalizer (pCoreOf 2 (X ⊔ T) : Set G) := by
    intro k hk
    rw [mem_normalizer_iff]
    intro r
    constructor
    · exact hconjR k hk r
    · intro hr
      have h1 := hconjR k⁻¹ (KC.inv_mem hk) _ hr
      rwa [show k⁻¹ * (k * r * k⁻¹) * k⁻¹⁻¹ = r by group] at h1
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr (hKR.trans hRX)

end LinearThree

section JFour

open CFSG.Quasithin.H13.NQCat (normalizerFrattiniAction normalizerFrattiniAction_mk normalizerConj
  normalizerConj_apply)

variable {S : Type} [Group S] [Finite S]

omit [Finite S] in
theorem normalizerFrattiniConj_eq_one_of_mem {X : Subgroup S} {p : ℕ} [Fact p.Prime]
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2) {x : S}
    (hx : x ∈ X) : normalizerFrattiniConj X ⟨x, Subgroup.le_normalizer hx⟩ = 1 := by
  have hcomm := (IsPGroup.isMulCommutative_of_card_eq_prime_sq hW).is_comm.comm
  refine MulEquiv.ext fun w => ?_
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective v
  have h1 : (X.normalizerMonoidHom ⟨x, Subgroup.le_normalizer hx⟩ z : X) =
      ⟨x, hx⟩ * z * (⟨x, hx⟩ : X)⁻¹ := Subtype.ext rfl
  change ((((X.normalizerMonoidHom ⟨x, Subgroup.le_normalizer hx⟩ z : X) :
      X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
    (((z : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))
  have key : ∀ a b : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X), a * b * a⁻¹ = b :=
    fun a b => by rw [hcomm a b, mul_inv_cancel_right]
  rw [h1]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact key _ _

theorem exists_sylow_frattini_equiv {X P : Subgroup S} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hPX : CFSG.ABGLocalTools.IsSylowOf p P X) :
    Nonempty (P ≃* X ⧸ CFSG.pCore 2 X) ∧
    ∃ Ξ : (P ⧸ frattini P) ≃* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X),
      ∀ (n : S) (hnP : n ∈ normalizer (P : Set S)) (hnX : n ∈ normalizer (X : Set S)) w,
        Ξ (normalizerFrattiniAction P ⟨n, hnP⟩ w) = normalizerFrattiniConj X ⟨n, hnX⟩ (Ξ w) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPXle : P ≤ X := hPX.le
  let ι₀ : P →* X ⧸ CFSG.pCore 2 X :=
    (QuotientGroup.mk' (CFSG.pCore 2 X)).comp (Subgroup.inclusion hPXle)
  have hinj : Function.Injective ι₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    have h1 : (Subgroup.inclusion hPXle a : X) ∈ CFSG.pCore 2 X := by
      rw [MonoidHom.mem_ker] at ha
      exact (QuotientGroup.eq_one_iff _).mp ha
    have h2 : (Subgroup.inclusion hPXle a : X) ∈ P.subgroupOf X := a.2
    have hd := IsPGroup.disjoint_of_ne p 2 hp2 (P.subgroupOf X) (CFSG.pCore 2 X)
      (hPX.isPGroup.of_equiv (subgroupOfEquivOfLe hPXle).symm) CFSG.pCore_isPGroup
    have h3 := Subgroup.disjoint_def.mp hd h2 h1
    have h4 : ((a : P) : S) = 1 := congrArg (fun z : X => (z : S)) h3
    rw [Subgroup.mem_bot]
    exact Subtype.ext h4
  have hcard : Nat.card P = Nat.card (X ⧸ CFSG.pCore 2 X) := by
    have hp : p.Prime := Fact.out
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hXp
    obtain ⟨j, hj⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := X))
    have hX : Nat.card X = p ^ k * 2 ^ j := by
      rw [← hk, ← hj]
      exact card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X)
    rw [hPX.card_eq, hk, hX, Nat.factorization_mul (pow_ne_zero _ hp.ne_zero)
      (pow_ne_zero _ two_ne_zero), Nat.Prime.factorization_pow hp,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [hp2]
  have hbij : Function.Bijective ι₀ :=
    (Nat.bijective_iff_injective_and_card ι₀).mpr ⟨hinj, hcard⟩
  let ι : P ≃* X ⧸ CFSG.pCore 2 X := MulEquiv.ofBijective ι₀ hbij
  let Ξ := QuotientGroup.congr _ _ ι (map_frattini_mulEquiv ι)
  refine ⟨⟨ι⟩, Ξ, fun n hnP hnX w => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective w
  rw [normalizerFrattiniAction_mk]
  have h1 : ι (normalizerConj P ⟨n, hnP⟩ a) =
      ((X.normalizerMonoidHom ⟨n, hnX⟩ (Subgroup.inclusion hPXle a) : X) :
        X ⧸ CFSG.pCore 2 X) := by
    change QuotientGroup.mk' _ (Subgroup.inclusion hPXle (normalizerConj P ⟨n, hnP⟩ a)) = _
    congr 1
  change ((ι (normalizerConj P ⟨n, hnP⟩ a) : X ⧸ CFSG.pCore 2 X) :
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = _
  rw [h1]
  rfl

omit [Finite S] in
theorem isSolvable_range_normalizerFrattiniAction {S' : Type*} [Group S'] (ε : S ≃* S')
    (P : Subgroup S)
    (h : Group.IsSolvable (normalizerFrattiniAction (P.map ε.toMonoidHom)).range) :
    Group.IsSolvable (normalizerFrattiniAction P).range := by
  let e₁ : P ≃* P.map ε.toMonoidHom := P.equivMapOfInjective ε.toMonoidHom ε.injective
  let Θ : P ⧸ frattini P ≃* P.map ε.toMonoidHom ⧸ frattini (P.map ε.toMonoidHom) :=
    QuotientGroup.congr _ _ e₁ (map_frattini_mulEquiv e₁)
  have hεN : ∀ n : normalizer (P : Set S),
      ε n ∈ normalizer ((P.map ε.toMonoidHom : Subgroup S') : Set S') := fun n => by
    have h1 := Subgroup.le_normalizer_map ε.toMonoidHom (Subgroup.mem_map_of_mem _ n.2)
    exact h1
  have hΘ : ∀ (n : normalizer (P : Set S)) w, mulAutConjHom Θ (normalizerFrattiniAction P n) w =
      normalizerFrattiniAction (P.map ε.toMonoidHom) ⟨ε n, hεN n⟩ w := by
    intro n w
    obtain ⟨v, rfl⟩ := Θ.surjective w
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective v
    rw [mulAutConjHom_apply, normalizerFrattiniAction_mk]
    change ((e₁ (normalizerConj P n a) : P.map ε.toMonoidHom) : _ ⧸ frattini _) =
      normalizerFrattiniAction (P.map ε.toMonoidHom) ⟨ε n, hεN n⟩ ((e₁ a : _) : _ ⧸ frattini _)
    rw [normalizerFrattiniAction_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply]
    change ε ((normalizerConj P n a : P) : S) = _
    rw [normalizerConj_apply, map_mul, map_mul, map_inv]
    rfl
  let φ : (normalizerFrattiniAction P).range →*
      (normalizerFrattiniAction (P.map ε.toMonoidHom)).range :=
    { toFun := fun σ => ⟨mulAutConjHom Θ σ, by
        obtain ⟨n, hn⟩ := σ.2
        refine ⟨⟨ε n, hεN n⟩, ?_⟩
        rw [← hn]
        exact (MulEquiv.ext (hΘ n)).symm⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun σ τ => Subtype.ext (map_mul _ _ _) }
  have hφ : Function.Injective φ := fun σ τ hστ =>
    Subtype.ext (mulAutConjHom_injective Θ (congrArg Subtype.val hστ))
  exact Group.isSolvable_of_isSolvable_injective hφ

omit [Finite S] in
theorem isSolvable_range_of_mulEquiv {S' : Type*} [Group S'] {p : ℕ}
    (hS' : ∀ Q : Subgroup S', IsPGroup p Q → ¬ IsCyclic Q →
      Group.IsSolvable (normalizerFrattiniAction Q).range)
    (ε : S ≃* S') (P : Subgroup S) (hP : IsPGroup p P) (hPnc : ¬ IsCyclic P) :
    Group.IsSolvable (normalizerFrattiniAction P).range :=
  isSolvable_range_normalizerFrattiniAction ε P (hS' _ (hP.map ε.toMonoidHom) fun hc => hPnc (by
    have := hc
    exact isCyclic_of_surjective
      (P.equivMapOfInjective ε.toMonoidHom ε.injective).symm.toMonoidHom
      (P.equivMapOfInjective ε.toMonoidHom ε.injective).symm.surjective))

theorem false_of_J4_frattini_action
    (e : S ≃* NativeSporadic.J4) {X : Subgroup S} (hXp : IsPGroup 11 (X ⧸ CFSG.pCore 2 X))
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = 11)
    (hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = 11 ^ 2)
    {Y : Subgroup S} (hYp : Group.IsPerfect Y) (hYX : Y ≤ normalizer (X : Set S))
    (hnt : ∃ (y : S) (hy : y ∈ Y), normalizerFrattiniConj X ⟨y, hYX hy⟩ ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨P, hPX⟩ := CFSG.ABGLocalTools.exists_isSylowOf 11 X
  obtain ⟨⟨ι⟩, Ξ, hΞ⟩ := exists_sylow_frattini_equiv (by norm_num) hXp hPX
  have hPnc : ¬ IsCyclic P := by
    intro hc
    have : IsCyclic (X ⧸ CFSG.pCore 2 X) := isCyclic_of_surjective ι.toMonoidHom ι.surjective
    have h1 := IsCyclic.exponent_eq_card (α := X ⧸ CFSG.pCore 2 X)
    rw [hexp] at h1
    have h2 : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ∣ 11 := by
      rw [h1]
      exact Subgroup.card_quotient_dvd_card _
    rw [hW] at h2
    norm_num at h2
  have eJ : NativeSporadic.J4 ≃* CFSG.Sporadic.J4.J :=
    CFSG.Sporadic.J4.seedEquiv CFSG.Sporadic.J4.j4Facts.mat
  have hsolv : Group.IsSolvable (normalizerFrattiniAction P).range :=
    @isSolvable_range_of_mulEquiv S _ CFSG.Sporadic.J4.J inferInstance 11
      (fun Q hQ hQc =>
        (NQCat.J4_noncyclic_eleven_subgroup_frattini_normalizer_image_is_solvable Q hQ hQc).2.2.1)
      (e.trans eJ) P hPX.isPGroup hPnc
  have : Group.IsPerfect (Y.subgroupOf (normalizer (X : Set S))) :=
    @Group.IsPerfect.ofSurjective _ _ _ _ (subgroupOfEquivOfLe hYX).symm.toMonoidHom hYp
      (subgroupOfEquivOfLe hYX).symm.surjective
  let I := ((Y.subgroupOf (normalizer (X : Set S))).map (normalizerFrattiniConj X)).map
    (mulAutConjHom Ξ.symm)
  have hY'm : Group.IsPerfect ((Y.subgroupOf (normalizer (X : Set S))).map
      (normalizerFrattiniConj X)) := Group.IsPerfect.map _
  have hIp : Group.IsPerfect I := Group.IsPerfect.map _
  have hI : I ≤ (normalizerFrattiniAction P).range := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨S₀, hS₀⟩ := hPX
    obtain ⟨x, hx, hxy⟩ :=
      CFSG.RankThree.GroupTheory.SteinbergBM.exists_mul_mem_normalizer_sylow S₀ y.2
    rw [hS₀] at hxy
    have hxyX : x * y ∈ normalizer (X : Set S) := mul_mem (Subgroup.le_normalizer hx) y.2
    have h1 : normalizerFrattiniConj X ⟨x * y, hxyX⟩ = normalizerFrattiniConj X y := by
      have h2 : (⟨x * y, hxyX⟩ : normalizer (X : Set S)) = ⟨x, Subgroup.le_normalizer hx⟩ * y :=
        Subtype.ext rfl
      rw [h2, map_mul, normalizerFrattiniConj_eq_one_of_mem hW hx, one_mul]
    refine ⟨⟨x * y, hxy⟩, ?_⟩
    refine MulEquiv.ext fun w => ?_
    obtain ⟨v, rfl⟩ := Ξ.symm.surjective w
    rw [mulAutConjHom_apply]
    apply Ξ.injective
    rw [MulEquiv.apply_symm_apply, hΞ (x * y) hxy hxyX, MulEquiv.apply_symm_apply, h1]
  have hIs : Group.IsSolvable I := by
    have := hsolv
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hI)
  obtain ⟨y, hy, hy1⟩ := hnt
  have hy' : (⟨y, hYX hy⟩ : normalizer (X : Set S)) ∈ Y.subgroupOf (normalizer (X : Set S)) := hy
  have hInt : Nontrivial I := by
    refine ⟨⟨1, ⟨_, Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hy')⟩, fun h => hy1 ?_⟩⟩
    have h2 := congrArg Subtype.val h
    exact mulAutConjHom_injective Ξ.symm (by rw [map_one]; exact h2.symm)
  exact Group.IsPerfect.not_isSolvable I hIs

end JFour

section Confined

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

variable {G : Type} [Group G] [Finite G]

theorem exists_frattini_map_equiv {K M' : Type*} [Group K] [Group M'] (η : K →* M')
    {X : Subgroup K} (e : (X ⧸ CFSG.pCore 2 X) ≃* ((X.map η) ⧸ CFSG.pCore 2 (X.map η)))
    (he : ∀ x : X, e x = ((⟨η x, Subgroup.mem_map_of_mem η x.2⟩ : X.map η) :
      (X.map η) ⧸ CFSG.pCore 2 (X.map η))) :
    ∃ Θ : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) ≃*
        ((X.map η) ⧸ CFSG.pCore 2 (X.map η)) ⧸ frattini ((X.map η) ⧸ CFSG.pCore 2 (X.map η)),
      ∀ (k : normalizer (X : Set K)) (w : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
        Θ (normalizerFrattiniConj X k w) = normalizerFrattiniConj (X.map η)
          ⟨η k, Subgroup.le_normalizer_map η (Subgroup.mem_map_of_mem η k.2)⟩ (Θ w) := by
  refine ⟨QuotientGroup.congr _ _ e (map_frattini_mulEquiv e), fun k w => ?_⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  have hk : η k ∈ normalizer ((X.map η : Subgroup M') : Set M') :=
    Subgroup.le_normalizer_map η (Subgroup.mem_map_of_mem η k.2)
  have hx : (⟨η (X.normalizerMonoidHom k x),
      Subgroup.mem_map_of_mem η (X.normalizerMonoidHom k x).2⟩ : X.map η) =
      (X.map η).normalizerMonoidHom ⟨η k, hk⟩ ⟨η x, Subgroup.mem_map_of_mem η x.2⟩ := by
    apply Subtype.ext
    change η ((k : K) * (x : K) * (k : K)⁻¹) = η k * η x * (η k)⁻¹
    rw [map_mul, map_mul, map_inv]
  have h1 := congrArg (fun y : X.map η => (((y : (X.map η) ⧸ CFSG.pCore 2 (X.map η))) :
      ((X.map η) ⧸ CFSG.pCore 2 (X.map η)) ⧸
        frattini ((X.map η) ⧸ CFSG.pCore 2 (X.map η)))) hx
  rw [← he (X.normalizerMonoidHom k x)] at h1
  refine h1.trans ?_
  have h2 := he x
  change _ = normalizerFrattiniConj (X.map η) ⟨η k, hk⟩
    (((e (x : X ⧸ CFSG.pCore 2 X)) : (X.map η) ⧸ CFSG.pCore 2 (X.map η)) :
      ((X.map η) ⧸ CFSG.pCore 2 (X.map η)) ⧸ frattini ((X.map η) ⧸ CFSG.pCore 2 (X.map η)))
  rw [h2]
  rfl

theorem escaping_characteristic_normalizers_confined_of
    (h39 : SQTKCLayerPerfectResidual)
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPLU : PrimeLinearThreeAmbientPlane)
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G)
    {T H L : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) (hLH : L ≤ H)
    (hLn : (L.subgroupOf H).Normal) (hHLT : H = L ⊔ T) (hLC : L ∈ cComp L) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {X : Subgroup G} (hXL : X ≤ L)
    (hXn : (X.subgroupOf H).Normal) (hX2 : NoPQuotient 2 X)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤)
    (hRX : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (X : Set G)) :
    ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
      (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
      normalizer (C : Set G) ≤ normalizer (X : Set G) := by
  intro C hC1 hCR hCc
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  by_contra hNX
  obtain ⟨hTN, -, hCO, hTs, -, hAloc, -, KC, ⟨hKC, hAK⟩, -, hKn, -, hXleY, hYA, -, hOKO, hO2T,
      -, -, hesc⟩ :=
    escaping_characteristic_normalizer_has_proper_original_local_of h39 hnab hK hT hTH hLH hLn hHLT
      hLC hp hp5 hXL hXn hX2 hXp hexp hrank hW hLW hirr C hC1 hCR hCc
  obtain ⟨-, hAq, -, -, -, hψ⟩ := char_normalizer_residual_in_G hT hTH hLH hLn hHLT hLC hp hp5
    hXL hXn hX2 hXp hW hLW hirr C hC1 hCR hCc
  obtain ⟨hKq, hXnK, -⟩ := hesc hNX
  set AG := (CFSG.perfectResidual ↥(L ⊓ normalizer (C : Set G))).map
    (L ⊓ normalizer (C : Set G)).subtype with hAGdef
  set Y := (CFSG.perfectResidual ↥(L ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G))).map
    (L ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)).subtype with hYdef
  have hXH : X ≤ H := hXL.trans hLH
  have hHX : H ≤ normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXn
  have hAL : AG ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hYK : Y ≤ KC := hYA.trans hAK
  have hXK : X ≤ KC := hXleY.trans hYK
  have hO2 : pCoreOf 2 (normalizer (C : Set G)) ≠ ⊥ := fun hb =>
    hC1 (le_bot_iff.mp (hb ▸ hCO))
  have hloc : LocalSQTK G := (qtkeCore_of_cat hnab hK).1
  have hKNC : KC ≤ normalizer (C : Set G) := le_of_mem_cComp hKC
  have hSQTK : CFSG.SectionRank.IsSQTKCat KC :=
    CFSG.QuasithinUnique.Setup.Family.isSQTKCat_of_le hKNC (hloc _ hO2)
  have hTK := CFSG.QuasithinUnique.L246C127.isSylowTwoOf_inf_of_isSubnormal'
    (subnormal_of_mem_cComp hKC) hTs
  have hTKs : quasithinIsSylowTwo (T.subgroupOf KC) := by
    rw [← Subgroup.inf_subgroupOf_right T KC]
    exact ⟨hTK.2.1.of_equiv (subgroupOfEquivOfLe inf_le_right).symm, hTK.2.2⟩
  have hAKc : AG.subgroupOf KC ∈ cComp (AG.subgroupOf KC ⊔ T.subgroupOf KC) := by
    have h1 : AG ∈ cComp (AG ⊔ (T ⊓ KC)) :=
      cComp_mem_of_le hAloc.2.1 le_sup_left (sup_le_sup_left inf_le_left AG)
    have h3 := subgroupOf_mem_cComp_of_le (sup_le hAK inf_le_right) h1
    rwa [Subgroup.subgroupOf_sup hAK inf_le_right, Subgroup.inf_subgroupOf_right] at h3
  have hAqK : ¬ CFSG.IsQuasisimple (↥(AG.subgroupOf KC) ⧸ CFSG.pCore 2 ↥(AG.subgroupOf KC)) := by
    intro hq'
    apply hAq
    let eA : AG.subgroupOf KC ≃* AG := subgroupOfEquivOfLe hAK
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.congr _ _ eA (CFSG.pCore_map_iso 2 eA))).1 hq'
  have hXpA : X.subgroupOf KC ≤ AG.subgroupOf KC := fun x hx => hXleY.trans hYA hx
  have hnorm : ∀ U : Subgroup KC, (∀ u ∈ U, (u : G) ∈ H) →
      U ≤ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC) :=
    fun _ hU u hu => mem_normalizer_subgroupOf_of_mem (hHX (hU u hu))
  have hXpn : ((X.subgroupOf KC).subgroupOf (AG.subgroupOf KC)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXpA).mpr
      (hnorm _ fun u hu => hLH (hAL hu))
  have hTXp : T.subgroupOf KC ≤ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC) :=
    hnorm _ fun u hu => hTH hu
  obtain ⟨hXp2', hXpp', hXpr'⟩ := odd_residual_witness_subgroupOf hXK hX2 hXp hrank
  have hTKC : T ≤ normalizer (KC : Set G) :=
    hTN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKNC).mp hKn)
  have hO2KT : pCoreOf 2 KC ≤ T := hOKO.trans hO2T
  rcases ambient_witness_alternatives hCat hSQTK hKq hTKs hAKc hAqK hp hp5 hXpA hXpn hTXp hXp2'
      hXpp' hXpr' with ⟨ℓ, -, hℓ5, hPSL⟩ | ⟨⟨eJ⟩, hp11⟩
  · exact hXnK (normal_of_linear_three_escape hPLU hSQTK hKq hTKs hAKc hAqK hp hp5 hXK hXpA hXpn
      hTXp hXp2' hXpp' hXpr' hℓ5 hPSL hTKC hO2KT hRX)
  ·
    subst hp11
    obtain ⟨-, -, -, -, -, -, -, hwit⟩ :=
      NQTerm.quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses hSQTK
        hKq hTKs hAKc hAqK
    obtain ⟨-, -, -, ⟨e, he⟩, -⟩ := hwit 11 hp hp5 _ hXpA hXpn hTXp hXp2' hXpp' hXpr'
    let η : ↥KC →* (↥KC ⧸ CFSG.pCore 2 ↥KC) ⧸ center (↥KC ⧸ CFSG.pCore 2 ↥KC) :=
      (QuotientGroup.mk' (center (↥KC ⧸ CFSG.pCore 2 ↥KC))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ↥KC))
    let e₁ : X.subgroupOf KC ≃* X := subgroupOfEquivOfLe hXK
    let e₂ : X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC) ≃* X ⧸ CFSG.pCore 2 X :=
      QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
    have hexpK : Monoid.exponent (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) = 11 :=
      (Monoid.exponent_eq_of_mulEquiv e₂).trans hexp
    obtain ⟨Θ₁, hΘ₁⟩ := exists_residual_subgroupOf_equiv hXK
    obtain ⟨Θ₂, hΘ₂⟩ := exists_frattini_map_equiv η e he
    have hWK : Nat.card ((X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC)) ⧸
        frattini (X.subgroupOf KC ⧸ CFSG.pCore 2 (X.subgroupOf KC))) = 11 ^ 2 :=
      (Nat.card_congr Θ₁.toEquiv).trans hW
    have hWb := (Nat.card_congr Θ₂.toEquiv).symm.trans hWK
    have hXbp := IsPGroup.of_equiv hXpp' e
    have hexpb := (Monoid.exponent_eq_of_mulEquiv e.symm).trans hexpK
    have hYperf : Group.IsPerfect Y := by
      have := (CFSG.perfect_residual_characterization
        (G := ↥(L ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)))).2.2.1
      exact Group.IsPerfect.map _
    have hYKp : Group.IsPerfect (Y.subgroupOf KC) :=
      @Group.IsPerfect.ofSurjective _ _ _ _ (subgroupOfEquivOfLe hYK).symm.toMonoidHom hYperf
        (subgroupOfEquivOfLe hYK).symm.surjective
    have hYbp : Group.IsPerfect ((Y.subgroupOf KC).map η) := Group.IsPerfect.map _
    have hYX : Y ≤ normalizer (X : Set G) := (hYA.trans hAL).trans (hLH.trans hHX)
    have hYKX : Y.subgroupOf KC ≤ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC) :=
      fun y hy => mem_normalizer_subgroupOf_of_mem (hYX hy)
    have hYbX : (Y.subgroupOf KC).map η ≤
        normalizer (((X.subgroupOf KC).map η : Subgroup _) : Set _) :=
      (Subgroup.map_mono hYKX).trans (Subgroup.le_normalizer_map η)
    obtain ⟨l, hlL, hl1⟩ := hLW
    obtain ⟨y, hyY, hyl⟩ := hψ l hlL
    have hy1 : normalizerFrattiniConj X y ≠ 1 := by
      rw [hyl]
      exact hl1
    let yK : ↥KC := ⟨y, hYK hyY⟩
    have hyKY : yK ∈ Y.subgroupOf KC := hyY
    have hyKN : yK ∈ normalizer ((X.subgroupOf KC : Subgroup KC) : Set KC) := hYKX hyKY
    have hyK1 : normalizerFrattiniConj (X.subgroupOf KC) ⟨yK, hyKN⟩ ≠ 1 := by
      intro h1
      apply hy1
      refine MulEquiv.ext fun w => ?_
      obtain ⟨v, rfl⟩ := Θ₁.surjective w
      have h2 := hΘ₁ ⟨yK, hyKN⟩ v
      change Θ₁ (normalizerFrattiniConj (X.subgroupOf KC) ⟨yK, hyKN⟩ v) = _ at h2
      rw [h1, MulAut.one_apply] at h2
      exact h2.symm
    refine false_of_J4_frattini_action eJ hXbp hexpb hWb hYbp hYbX
      ⟨η yK, Subgroup.mem_map_of_mem η hyKY, fun h1 => hyK1 ?_⟩
    refine MulEquiv.ext fun w => ?_
    apply Θ₂.injective
    rw [hΘ₂, h1]
    rfl

end Confined

section Statements

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

@[expose] def StmtCharNormalizersConfined : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G → ∀ T H L : Subgroup G, quasithinIsSylowTwo T → T ≤ H → L ≤ H →
    (L.subgroupOf H).Normal → H = L ⊔ T → L ∈ cComp L → ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ X : Subgroup G, X ≤ L → (X.subgroupOf H).Normal → NoPQuotient 2 X →
    IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
    CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 → Nat.card (WPlane X) = p ^ 2 →
    (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
    (∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) →
    normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (X : Set G) →
    ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
      (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
      normalizer (C : Set G) ≤ normalizer (X : Set G)

theorem stmtCharNormalizersConfined_of
    (h39 : SQTKCLayerPerfectResidual)
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPLU : PrimeLinearThreeAmbientPlane)
    : StmtCharNormalizersConfined :=
  fun _ _ _ _ hnab hK _ _ _ hT hTH hLH hLn hHLT hLC _ hp hp5 _ hXL hXn hX2 hXp hexp hrank hW hLW
    hirr hRX => escaping_characteristic_normalizers_confined_of h39 hCat hPLU hnab hK hT hTH hLH
      hLn hHLT hLC hp hp5 hXL hXn hX2 hXp hexp hrank hW hLW hirr hRX

variable {G : Type} [Group G] [Finite G]

theorem every_original_radical_characteristic_normalizer_is_confined_of
    (h39 : SQTKCLayerPerfectResidual) (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPLU : PrimeLinearThreeAmbientPlane)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hO2X : CFSG.pCore 2 X ≠ ⊥) (hX2 : NoPQuotient 2 X)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) :
    normalizer (X : Set G) = M ∧ ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
      (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → normalizer (C : Set G) ≤ M := by
  obtain ⟨hNX, hNR, -, -, -, -⟩ :=
    original_radical_normalizer_and_core_control_before_same_witness_singleton_of h39 h2 h hp hp5
      hXR hXc hO2X hX2 hXp hexp hrank hW hLW hirr
  refine ⟨hNX, fun C hC1 hCR hCc => ?_⟩
  have := h.simple
  have hXL : X ≤ L := hXR.trans (Subgroup.map_subtype_le _)
  have hTL : T ≤ normalizer (L : Set G) := h.t_le.trans h.eq_normalizer.le
  have hLn : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hTL)
  have hLC : L ∈ cComp L := cComp_mem_of_le h.maximal_local.1.2.1 le_rfl le_sup_left
  have hXn : (X.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hXL.trans le_sup_left)).mpr
      (h.join_le.trans hNX.ge)
  exact (escaping_characteristic_normalizers_confined_of h39 hCat hPLU h.nonabelian h.qtke h.sylow
    le_sup_right le_sup_left hLn rfl hLC hp hp5 hXL hXn hX2 hXp hexp hrank hW hLW hirr
    (hNR.trans hNX.ge) C hC1 hCR hCc).trans hNX.le

@[expose] def StmtEveryOriginalRadicalCharNormalizerConfined : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ (CFSG.solvableRadical L).map L.subtype →
      (X.subgroupOf L).Characteristic → CFSG.pCore 2 X ≠ ⊥ → NoPQuotient 2 X →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 → Nat.card (WPlane X) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      (∀ V : Subgroup (WPlane X),
        (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
          V = ⊥ ∨ V = ⊤) →
      normalizer (X : Set G) = M ∧ ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
        (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → normalizer (C : Set G) ≤ M

theorem stmtEveryOriginalRadicalCharNormalizerConfined_of
    (h39 : SQTKCLayerPerfectResidual)
    (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    (hCat : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct) (hPLU : PrimeLinearThreeAmbientPlane)
    : StmtEveryOriginalRadicalCharNormalizerConfined :=
  fun _ _ _ _ _ _ h _ hp hp5 _ hXR hXc hO2X hX2 hXp hexp hrank hW hLW hirr =>
    every_original_radical_characteristic_normalizer_is_confined_of h39 h2 hCat hPLU h hp hp5 hXR
      hXc hO2X hX2 hXp hexp hrank hW hLW hirr

end Statements

end CFSG.Quasithin.H13.NQBlock
