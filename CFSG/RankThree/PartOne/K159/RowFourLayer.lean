module

public import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.RankThree.PartOne.K159.FamilyRowFour
public import CFSG.RankThree.PartOne.K159.BorelRow1
public import CFSG.RankThree.PartOne.S15K.FamilyExclusion

public section

namespace CFSG.RankThree.PartOne.K159

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.GroupTheory.WeirSylow QuadraticMap CFSG.RankThree.PartOne.S15K
open scoped commutatorElement

section Transport

variable {G : Type} [Group G] {T : Type*} [Group T]

theorem exists_two_subgroup_of_transport {I Y E : Subgroup G} (φ : ↥I ≃* T)
    (hEI : E ≤ Subgroup.normalizer (I : Set G)) (a : ↥E →* T)
    (hcompat : ∀ (g' : ↥E) (y : ↥I),
      φ (I.normalizerMonoidHom ⟨(g' : G), hEI g'.2⟩ y) = a g' * φ y * (a g')⁻¹) {F : Subgroup T}
    (hmem : ∀ y : G, y ∈ Y ↔ ∃ hy : y ∈ I, φ ⟨y, hy⟩ ∈ F) {S : Subgroup G} (hSY : S ≤ Y)
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S) (hSN : E ≤ Subgroup.normalizer (S : Set G))
    (hSc : S = ⁅S, E⁆) :
    ∃ S' : Subgroup T, S' ≤ F ∧ S' ≠ ⊥ ∧ IsPGroup 2 ↥S' ∧
      (∀ e : ↥E, a e ∈ Subgroup.normalizer (S' : Set T)) ∧ S' ≤ ⁅S', a.range⁆ := by
  classical
  have hSI : S ≤ I := fun s hs => ((hmem s).1 (hSY hs)).1
  set SI : Subgroup ↥I := S.subgroupOf I with hSIdef
  set S' : Subgroup T := SI.map φ.toMonoidHom with hS'
  have hSIS2 : IsPGroup 2 ↥SI := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSI).symm
  have hmemS : ∀ y : ↥I, y ∈ SI ↔ (y : G) ∈ S := fun y => Iff.rfl
  have hnorm : ∀ (e : ↥E) (y : ↥I), y ∈ SI → I.normalizerMonoidHom ⟨(e : G), hEI e.2⟩ y ∈ SI := by
    intro e y hy
    rw [hmemS] at hy ⊢
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact (Subgroup.mem_normalizer_iff.1 (hSN e.2) _).1 hy
  have hconj : ∀ e : ↥E, ∀ t ∈ S', a e * t * (a e)⁻¹ ∈ S' := by
    intro e t ht
    obtain ⟨y, hy, rfl⟩ := ht
    exact ⟨_, hnorm e y hy, hcompat e y⟩
  refine ⟨S', ?_, ?_, hSIS2.map φ.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hy', hF⟩ := (hmem (y : G)).1 (hSY hy)
    have : (⟨(y : G), hy'⟩ : ↥I) = y := Subtype.ext rfl
    rw [this] at hF
    exact hF
  · obtain ⟨s, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS1
    intro h
    have hsI : (s : G) ∈ I := hSI s.2
    have hmem' : φ ⟨(s : G), hsI⟩ ∈ S' := ⟨⟨(s : G), hsI⟩, s.2, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem'
    apply hs1
    have h3 := φ.injective (hmem'.trans φ.map_one.symm)
    have h4 : (s : G) = 1 := congrArg (fun z : ↥I => (z : G)) h3
    exact Subtype.ext h4
  · intro e
    refine Subgroup.mem_normalizer_iff.2 fun t => ⟨fun ht => hconj e t ht, fun ht => ?_⟩
    have h1 := hconj e⁻¹ _ ht
    rw [map_inv] at h1
    simpa [mul_assoc] using h1
  · set H : Subgroup T := ⁅S', a.range⁆ with hH
    have hle : ⁅S, E⁆ ≤ (H.comap φ.toMonoidHom).map I.subtype := by
      rw [Subgroup.commutator_le]
      intro s hs e he
      have hsI : s ∈ I := hSI hs
      have he' : (e : G) ∈ Subgroup.normalizer (I : Set G) := hEI he
      set y : ↥I := ⟨s, hsI⟩ with hy
      have hyS : y ∈ SI := hs
      refine ⟨y * I.normalizerMonoidHom ⟨e, he'⟩ y⁻¹, ?_, ?_⟩
      · have : φ (y * I.normalizerMonoidHom ⟨e, he'⟩ y⁻¹) = ⁅φ y, a ⟨e, he⟩⁆ := by
          rw [map_mul, hcompat ⟨e, he⟩ y⁻¹, map_inv, commutatorElement_def]
          group
        show φ (y * I.normalizerMonoidHom ⟨e, he'⟩ y⁻¹) ∈ H
        rw [this]
        exact Subgroup.commutator_mem_commutator ⟨y, hyS, rfl⟩ ⟨⟨e, he⟩, rfl⟩
      · show ((y * I.normalizerMonoidHom ⟨e, he'⟩ y⁻¹ : ↥I) : G) = ⁅s, e⁆
        rw [Subgroup.coe_mul, Subgroup.normalizerMonoidHom_apply_apply_coe, commutatorElement_def]
        simp [hy]
        group
    rintro _ ⟨y, hy, rfl⟩
    have h1 : (y : G) ∈ ⁅S, E⁆ := by
      rw [← hSc]
      exact hy
    obtain ⟨z, hz, hzy⟩ := hle h1
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz

end Transport

section Family

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}

theorem exists_layerFamily_models_four (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 8)
    (hV : ¬ IsPlusType Q) {f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hK : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (hpq : p ∣ 2 ^ f + 1) (hq : 3 < Nat.card K) (A : Subgroup (ProjOrthDerived Q))
    (hA : Assembly.IsElemAbelian p A) (hAcard : Nat.card A = p ^ 2) (a : ProjOrthDerived Q)
    (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ (x : orthDerived Q) (Rep : Finset K[X]) (n : ℕ) (C : Fin n → Subgroup (ProjOrthDerived Q)),
      (QuotientGroup.mk x : ProjOrthDerived Q) = a ∧ orderOf x = p ∧
      IsOrbitRepresentatives (x : V ≃ₗ[K] V) Rep ∧
      (⨆ i, C i) = fixedLayerImage Q (x : V ≃ₗ[K] V) ∧
      LayerFamily p a (orthFamily Q (x : V ≃ₗ[K] V) Rep C) ∧ ∀ j, BlockModelFour p ↥(C j) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (ProjOrthDerived Q) := inferInstance
  obtain ⟨x, Rep, n, C, hxa, hxp, hRep, hCsup, hFam⟩ :=
    exists_layerFamily hQ hT hdim hp hp5 hq A hA hAcard a haA ha1
  refine ⟨x, Rep, n, C, hxa, hxp, hRep, hCsup, hFam, ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  have hpl : p ≠ ringChar K := by rw [ringChar.eq K 2]; omega
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hx := oddOrderIsometry_of_orthDerived hp hpl hQ x hxp
  have hx1 : (x : V ≃ₗ[K] V) ≠ 1 := by
    intro h1
    have : x = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  obtain ⟨-, hmain⟩ := orthogonal_primary_local_components_and_fixed_residue hQ hT hp hp3 hpl
    (MulAut.conj : ProjOrthDerived Q →* MulAut (ProjOrthDerived Q)).range le_rfl a
    (orderOf_eq_prime (hA.2 a haA) ha1) x hxa hxp
  obtain ⟨hNeq, -, -, -, -, hspec, -, -⟩ := hmain Rep hRep
  have hNeq' : centralizerImage Q (x : V ≃ₗ[K] V) =
      Subgroup.centralizer ({a} : Set (ProjOrthDerived Q)) := hNeq.symm
  have hC' : ∀ j : Fin n, CFSG.IsQuasisimple ↥(C j) ∧ C j ≤ centralizerImage Q (x : V ≃ₗ[K] V) ∧
      ((C j).subgroupOf (centralizerImage Q (x : V ≃ₗ[K] V))).IsSubnormal := by
    intro j
    have hle := hFam.le (Sum.inr j)
    have hcomp := hFam.comp (Sum.inr j)
    rw [orthFamily_inr] at hle hcomp
    rw [← hNeq'] at hle hcomp
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hcomp.1, hle,
      hcomp.2⟩
  intro j
  exact blockModelFour_fixedLayer_component hQ hx hp hp2 hK hf hpq hdim hV hx1 hCsup hC' j

end Family

section Rows

variable {G : Type} [Group G] [Finite G]

theorem layerModelDataFour_of_lifts_orth {p f : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {E I : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) (hdim : finrank K V = 8)
    (hV : ¬ IsPlusType Q) (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hq : 3 < Nat.card K)
    (hpq : p ∣ 2 ^ f + 1) (hEcard : Nat.card E = p ^ 3) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (φ : ↥I ≃* ProjOrthDerived Q) (a : ↥E → ProjOrthDerived Q) (hap : ∀ e, a e ^ p = 1)
    (hac : ∀ e : ↥E, MulAut.conj (a e) = actP φ ⟨(e : G), hEI e.2⟩)
    (hacomm : ∀ e e' : ↥E, a e * a e' = a e' * a e) (hao : ∀ e : ↥E, e ≠ 1 → orderOf (a e) = p)
    (hmul : ∀ e e' : ↥E, a (e * e') = a e * a e') : LayerModelDataFour p E I := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (ProjOrthDerived Q) := inferInstance
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  intro b hb hb1
  set bE : ↥E := ⟨b, hb⟩ with hbE
  have hbne : bE ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  obtain ⟨A, hA, hAcard, haA, habne⟩ := exists_plane_of_lifts hp hEcard a hap hacomm hmul hao bE hbne
  obtain ⟨x, Rep, n, C, hxa, hxp, hRep, hCsup, hFam, hBM⟩ :=
    exists_layerFamily_models_four hQ hT hdim hV hp hp5 hK hf hpq hq A hA hAcard (a bE) haA habne
  have hcompat := compat_of_lifts φ hEI a hac
  obtain ⟨Qf, h1, h2, h3, h4, hmem⟩ := layerData_clauses_of_family hp φ hEI a hap hcompat hacomm bE _
    hFam
  refine ⟨_, Qf, h1, h2, h3, fun i => ?_⟩
  have hQ' : ∀ y : G, y ∈ Qf i ↔ ∃ hy : y ∈ I,
      φ.toMonoidHom ⟨y, hy⟩ ∈ (orthFamily Q (x : V ≃ₗ[K] V) Rep C i).map (MonoidHom.id _) := by
    intro y
    rw [hmem i y, Subgroup.map_id]
    rfl
  obtain ⟨e⟩ := nonempty_mulEquiv_of_transport φ.toMonoidHom φ.injective (MonoidHom.id _) hQ'
    (by rw [Subgroup.map_id]; exact fun y _ => ⟨φ.symm y, by simp⟩) (fun u _ h => h)
  rcases i with ⟨h, hmem', hne1, hm⟩ | j
  ·
    right
    intro hY0
    obtain ⟨B, hBadm, hYB⟩ := hY0
    have hBE : B = E := by
      have hcard : Nat.card B = Nat.card E := by rw [hBadm.2.2.1, hEcard]
      exact Subgroup.eq_of_le_of_card_ge hBadm.1 hcard.ge
    subst hBE
    obtain ⟨-, S, hSY, hS1, hS2, hSN, hSc⟩ := hYB
    obtain ⟨S', hS'F, hS'1, hS'2, hS'N, hS'c⟩ :=
      exists_two_subgroup_of_transport φ hEI (MonoidHom.mk' a hmul) hcompat (F := orthFamily Q
        (x : V ≃ₗ[K] V) Rep C (Sum.inl ⟨h, hmem', hne1, hm⟩)) (fun y => hmem (Sum.inl ⟨h, hmem', hne1, hm⟩) y)
        hSY hS1 hS2 hSN hSc
    exact hS'1 (special_selfDual_no_two_subgroup hQ hdim hV hp hp5 hpq' hEcard a hap hacomm hao hmul
      bE x hxa hxp (hRep.1 hmem') hne1 hm hS'F hS'2 hS'N hS'c)
  · left
    exact BlockModelFour.of_mulEquiv e (hBM j)

section Orth

open CFSG.Assembly.RankThreeEven (projOmegaMinus)
open CFSG.LieType.Universal.Spin (quadMinus)

theorem layerModelDataFour_of_orthMinus {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E) (hEA : E = A) {f : ℕ} (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) {b c' : GaloisField 2 f}
    (hbc : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c' ≠ 0)
    (φ₀ : ↥(lieGenerated p E) ≃* projOmegaMinus 3 (GaloisField 2 f) b c') :
    LayerModelDataFour p E (lieGenerated p E) := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq : 3 < Nat.card (GaloisField 2 f) := by
    rw [hK]
    have := Nat.le_of_dvd (by positivity) hpq
    omega
  have hf2 : 2 ≤ f := by
    by_contra hlt
    obtain rfl : f = 1 := by omega
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  let φ : ↥(lieGenerated p E) ≃* ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c') :=
    φ₀.trans (projOmegaMinusEquivOrth (GaloisField 2 f) b c')
  have hOut := outPNice_of_projOmegaMinus
    (X := ProjOrthDerived (quadMinus 4 (GaloisField 2 f) b c')) hp (by omega) hf hbc
    (projOmegaMinusEquivOrth (GaloisField 2 f) b c').symm
  have hpI : p ∣ Nat.card (lieGenerated p E) := dvd_card_of_projOmegaMinus hf hbc φ₀ (Or.inr hpq)
  have hQ := polar_nondegenerate_quadMinus hbc
  have hT := exists_three_totSing_quadMinus (GaloisField 2 f) b c'
  have hdim : finrank (GaloisField 2 f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hV : ¬ IsPlusType (quadMinus 4 (GaloisField 2 f) b c') :=
    not_isPlusType_quadMinus (by omega) hbc
  obtain ⟨a, hap, hac, hacomm, hao, hmul⟩ := orth_lifts h h13 hEA hQ hT hOut hpI φ
  exact layerModelDataFour_of_lifts_orth hp h5 hQ hT hdim hV hK hf2 hq hpq hEcard
    (E_le_normalizer_lieGenerated hp) φ a hap hac hacomm hao hmul

end Orth

end Rows

theorem layerRowFourModel : LayerRowFourModel := by
  intro G _ _ p A c L E h15 hF h13 hout
  obtain ⟨f, hf, hpq, ⟨b, c', hbc, ⟨φ₀⟩⟩, -, hEA, -⟩ := hout
  exact layerModelDataFour_of_orthMinus h15.h12 h13 hEA hf hpq hbc φ₀

theorem kf158BlocksFourModel_of_sec13 (hS13 : Sec13Avail) : KF158BlocksFourModel :=
  kf158BlocksFourModel_of_layer hS13 layerRowFourModel

theorem kf158L0c_of_sec13 (hS13 : Sec13Avail) (h5 : KF158L0cRowFive) : KF158L0c :=
  kf158L0c_of_borel_four (kf158BlocksBorel_of_sec13 hS13) (kf158BlocksFourModel_of_sec13 hS13) h5

end CFSG.RankThree.PartOne.K159
