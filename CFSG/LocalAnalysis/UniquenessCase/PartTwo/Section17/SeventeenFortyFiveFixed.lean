module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveConfig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveAssembly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySevenTorus
public import CFSG.Quasithin.EmptyFaithful.S152TOpp
public import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzPairOuterRankHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzFieldFixedFreeHolds
import CFSG.GroupTheory.NormalizerSubgroupOfConj
import CFSG.GroupTheory.InnerAutomorphismProd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Sz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KRankOneBorel.ProductBar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Monster.B.Generic
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem borel_order_data_of_case34 {D : Data G}
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ : Subgroup G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) :
    ¬ p ∣ Nat.card ↥
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ∧
      (D.T ⊓ X).relIndex
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2 ∧
      (Nat.card ↥
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G))).factorization r = 2 ∧
      (Nat.card ↥X).factorization r = 2 := by
  classical
  obtain ⟨hLcal, hLne, hshapeN, hr, hrdvd, hpSig, -, -, hXprod, hMNX⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshapeN 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hKdef
  have hXprod' : (X : Set G) = (L : Set G) * (K : Set G) := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hXprod
  have hLcal0 : L ∈ calC D.M := by simpa using hLcal 0
  have hLM : L ≤ D.M := s13_le_of_mem_calC hLcal0
  have hXeq : X = L ⊔ K := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : z ∈ (L : Set G) * (K : Set G) := by rwa [← hXprod']
      obtain ⟨a, ha, b, hb, rfl⟩ := hz'
      exact Subgroup.mul_mem_sup ha hb
    · refine sup_le ?_ ?_
      · intro a ha
        have h : a ∈ (L : Set G) * (K : Set G) := ⟨a, ha, 1, K.one_mem, by simp⟩
        change a ∈ (X : Set G)
        rw [hXprod']
        exact h
      · intro b hb
        have h : b ∈ (L : Set G) * (K : Set G) := ⟨1, L.one_mem, b, hb, by simp⟩
        change b ∈ (X : Set G)
        rw [hXprod']
        exact h
  have hLKne : L ≠ K := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hLne
  have hKconj : K ∈ conjSetOf D.M L := by
    rcases hc with h3 | h4
    · have h1' : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
        simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h3.1
      have hmem : K ∈ ({L, K} : Set (Subgroup G)) := by simp
      rwa [h1'] at hmem
    · have h1' : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
        simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h4.1
      have hmem : K ∈ ({L, K} : Set (Subgroup G)) := by simp
      rwa [h1'] at hmem
  have hKcalM : K ∈ calC D.M := uc22p2214_calC_of_mem_conjSetOf hLcal0 hKconj
  obtain ⟨m, hmM, hmK⟩ := hKconj
  have hmK' : K = CFSG.Quasithin.conjSubgroup L m⁻¹ := by
    rw [hmK, CFSG.Quasithin.conjSubgroup]
    simp
  have hKM : K ≤ D.M := s13_le_of_mem_calC hKcalM
  have hXM : X ≤ D.M := by rw [hXeq]; exact sup_le hLM hKM
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := hMNX
  have hXne : X ≠ L := by
    intro hXL
    have hKleL : K ≤ L := by
      have : K ≤ X := by rw [hXeq]; exact le_sup_right
      rwa [hXL] at this
    have hKcard : Nat.card ↥K = Nat.card ↥L := by
      rw [hmK', CFSG.Quasithin.conjSubgroup]
      exact Subgroup.card_map_of_injective (MulAut.conj (m⁻¹)⁻¹).injective
    have hKL : K = L := Subgroup.eq_of_le_of_card_ge hKleL (by rw [hKcard])
    exact hLKne hKL.symm
  have hXsup : conjClosure D.M L = L ⊔ K := by rw [← ctx.X_eq, hXeq]
  have hneCl : conjClosure D.M L ≠ L := by rw [← ctx.X_eq]; exact hXne
  rcases hc with h3 | h4
  · obtain ⟨-, hL2raw, hp3, -, φ, hφ, hker⟩ := h3
    have hL2 : IsL2 (Bar2 L) 3 := hL2raw
    subst p
    have hn3 : n = 3 := by
      rcases hshape0 with hN | hN
      · exact isL2_field_unique hN hL2
      · exact (P2214S.false_of_isSz_of_isL2 hN hL2).elim
    have hr7 : r = 7 := by
      have hdvd7 : r ∣ 7 := by simpa [hn3] using hrdvd
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact absurd h hr.ne_one
      · exact h
    have hr2 : r ≠ 2 := by rw [hr7]; norm_num
    have hSq : IsL2Square (Bar2 X) 3 := by
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isL2Square_bar2_conjClosure
        hLcal0 (D.M.inv_mem hmM) (by rw [hXsup, ← hmK']) hneCl hL2
      rwa [← ctx.X_eq] at h
    obtain ⟨A, B, _, _, ⟨e⟩, hAL2, hBL2⟩ := hSq
    have : Finite A := finite_of_isL2 hAL2
    have : Finite B := finite_of_isL2 hBL2
    have hSyl := (sylow_inf_T D hXM hMX).1
    have hQ := (sylow_inf_T D hXM hMX).2
    have hSbar : CFSG.QuasithinUnique.IsSylowTwoOf (barImage X (D.T ⊓ X)) ⊤ :=
      isSylowTwoOf_sylowBar2_of hSyl
    let S : Subgroup (A × B) := (barImage X (D.T ⊓ X)).map e.toMonoidHom
    have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
      have h := CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_mulEquiv e hSbar
      rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
    obtain ⟨hNp, hrel, hfacN, hfacX⟩ :=
      product_borel_data_isL2_square (A := A) (B := B) hAL2 hBL2 (S := S) hS
    have hcardN : Nat.card ↥(Subgroup.normalizer
        (barImage X (D.T ⊓ X) : Set (Bar2 X))) =
        Nat.card ↥(Subgroup.normalizer (S : Set (A × B))) := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
        Subgroup.map_equiv_normalizer_eq]
    have hrel' : (barImage X (D.T ⊓ X)).relIndex
        (Subgroup.normalizer (barImage X (D.T ⊓ X) : Set (Bar2 X))) =
        S.relIndex (Subgroup.normalizer (S : Set (A × B))) := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective,
        Subgroup.map_equiv_normalizer_eq]
    refine borel_order_data_of_bar D hXM hMX (by norm_num) (by norm_num)
      (by rw [hr7]; norm_num) hr2 hSyl hQ ?_ ?_ ?_ ?_
    · rw [hcardN]; exact hNp
    · rw [hrel', hr7]; exact hrel
    · rw [hcardN, hr7]; exact hfacN
    · rw [Nat.card_congr e.toEquiv, hr7]; exact hfacX
  · obtain ⟨-, hSzraw, hp5, -, φ, hφ, hker⟩ := h4
    have hSz : IsSz (Bar2 L) 5 := hSzraw
    subst p
    have hn5 : n = 5 := by
      rcases hshape0 with hN | hN
      · exact (P2214S.false_of_isSz_of_isL2 hSz hN).elim
      · exact eq_five_of_isSz_five hN hSz
    have hr31 : r = 31 := by
      have hdvd31 : r ∣ 31 := by simpa [hn5] using hrdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
      · exact absurd h hr.ne_one
      · exact h
    have hr2 : r ≠ 2 := by rw [hr31]; norm_num
    have hSq : IsSzSquare (Bar2 X) 5 := by
      have h := CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.isSzSquare_bar2_conjClosure
        hLcal0 (D.M.inv_mem hmM) (by rw [hXsup, ← hmK']) hneCl hSz
      rwa [← ctx.X_eq] at h
    obtain ⟨A, B, _, _, ⟨e⟩, hASz, hBSz⟩ := hSq
    have : Finite A := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hASz
    have : Finite B := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_twistedB2 hBSz
    have hSyl := (sylow_inf_T D hXM hMX).1
    have hQ := (sylow_inf_T D hXM hMX).2
    have hSbar : CFSG.QuasithinUnique.IsSylowTwoOf (barImage X (D.T ⊓ X)) ⊤ :=
      isSylowTwoOf_sylowBar2_of hSyl
    let S : Subgroup (A × B) := (barImage X (D.T ⊓ X)).map e.toMonoidHom
    have hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
      have h := CFSG.GroupTheory.PermSylowTwo.isSylowTwoOf_map_mulEquiv e hSbar
      rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
    obtain ⟨hNp, hrel, hfacN, hfacX⟩ :=
      product_borel_data_isSz_square (A := A) (B := B) hASz hBSz (S := S) hS
    have hcardN : Nat.card ↥(Subgroup.normalizer
        (barImage X (D.T ⊓ X) : Set (Bar2 X))) =
        Nat.card ↥(Subgroup.normalizer (S : Set (A × B))) := by
      rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective,
        Subgroup.map_equiv_normalizer_eq]
    have hrel' : (barImage X (D.T ⊓ X)).relIndex
        (Subgroup.normalizer (barImage X (D.T ⊓ X) : Set (Bar2 X))) =
        S.relIndex (Subgroup.normalizer (S : Set (A × B))) := by
      rw [← Subgroup.relIndex_map_map_of_injective (f := e.toMonoidHom) _ _ e.injective,
        Subgroup.map_equiv_normalizer_eq]
    refine borel_order_data_of_bar D hXM hMX (by norm_num) (by norm_num)
      (by rw [hr31]; norm_num) hr2 hSyl hQ ?_ ?_ ?_ ?_
    · rw [hcardN]; exact hNp
    · rw [hrel', hr31]; exact hrel
    · rw [hcardN, hr31]; exact hfacN
    · rw [Nat.card_congr e.toEquiv, hr31]; exact hfacX

theorem gapWitness_mem_normalizer_components {D : Data G} {X L K : Subgroup G} {p : ℕ} {y : G}
    (hLKne : L ≠ K) (hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L)
    (hpodd : Odd p) (hy : GapWitness D X p y) :
    y ∈ Subgroup.normalizer (L : Set G) ∧ y ∈ Subgroup.normalizer (K : Set G) := by
  classical
  have hyM : y ∈ D.M := hy.1
  have hS2 : (conjSetOf D.M L).ncard = 2 := by
    rw [← hset]
    rw [Set.ncard_pair]
    exact hLKne
  have hSφ : ∀ A ∈ conjSetOf D.M L, A.map (MulAut.conj y).toMonoidHom ∈ conjSetOf D.M L := by
    intro A hA
    obtain ⟨m, hm, rfl⟩ := hA
    refine ⟨y * m, D.M.mul_mem hyM hm, ?_⟩
    rw [uc22p22d_map_conj_map_conj]
  have hLmem : L ∈ conjSetOf D.M L := by
    refine ⟨1, D.M.one_mem, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  have hKmem : K ∈ conjSetOf D.M L := by
    rw [← hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hodd : Odd (orderOf y) := by rw [hy.2.2.1]; exact hpodd
  have hLmap : L.map (MulAut.conj y).toMonoidHom = L :=
    c23_map_conj_eq_of_odd_order hS2 hodd (pow_orderOf_eq_one y) hSφ hLmem
  have hKmap : K.map (MulAut.conj y).toMonoidHom = K :=
    c23_map_conj_eq_of_odd_order hS2 hodd (pow_orderOf_eq_one y) hSφ hKmem
  exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hLmap,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hKmap⟩

theorem barImage_equiv_rhoL_apply {I L : Subgroup G} (hLI : L ≤ I)
    {e : Bar2 L ≃* ↥(barImage I L)}
    (he : ∀ k : ↥L, ((e (QuotientGroup.mk k) : ↥(barImage I L)) : Bar2 I) =
      (QuotientGroup.mk (Subgroup.inclusion hLI k) : Bar2 I))
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyI : y ∈ Subgroup.normalizer (I : Set G)) (z : Bar2 L) :
    ((e (UC6S846.rhoL L ⟨y, hyL⟩ z) : ↥(barImage I L)) : Bar2 I) =
      UC6S846.rhoL I ⟨y, hyI⟩ ((e z : ↥(barImage I L)) : Bar2 I) := by
  induction z using QuotientGroup.induction_on with
  | H k =>
    rw [UC6S846.rhoL_mk L ⟨y, hyL⟩ k, he (L.normalizerMonoidHom ⟨y, hyL⟩ k), he k,
      UC6S846.rhoL_mk I ⟨y, hyI⟩ (Subgroup.inclusion hLI k)]
    congr 1

theorem rhoL_maps_barImage {I L : Subgroup G} (hLI : L ≤ I) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyI : y ∈ Subgroup.normalizer (I : Set G)) :
    (barImage I L).map (UC6S846.rhoL I ⟨y, hyI⟩).toMonoidHom = barImage I L := by
  classical
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro u ⟨v, hv, rfl⟩
    obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp
      (show v ∈ (L.subgroupOf I).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) from hv)
    have hwL : (w : G) ∈ L := Subgroup.mem_subgroupOf.mp hw
    have hyw : y * (w : G) * y⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hyL (w : G)).mp hwL
    refine Subgroup.mem_map.mpr ⟨Subgroup.normalizerMonoidHom I ⟨y, hyI⟩ w, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf, UC6S846.rhoL_mk_coe]
      exact hyw
    · rw [← hwv]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
          ((I.normalizerMonoidHom ⟨y, hyI⟩) w) = ((UC6S846.rhoL I) ⟨y, hyI⟩) ↑w
      rw [UC6S846.rhoL_mk]
      rfl
  · rw [Subgroup.card_map_of_injective (f := (UC6S846.rhoL I ⟨y, hyI⟩).toMonoidHom)
      (UC6S846.rhoL I ⟨y, hyI⟩).injective]

theorem mulAutRestrict_rhoL_eq_congr {I L : Subgroup G} (hLI : L ≤ I)
    {e : Bar2 L ≃* ↥(barImage I L)}
    (he : ∀ k : ↥L, ((e (QuotientGroup.mk k) : ↥(barImage I L)) : Bar2 I) =
      (QuotientGroup.mk (Subgroup.inclusion hLI k) : Bar2 I))
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyI : y ∈ Subgroup.normalizer (I : Set G)) :
    mulAutRestrict (UC6S846.rhoL I ⟨y, hyI⟩) (barImage I L)
        (rhoL_maps_barImage hLI hyL hyI) =
      MulAut.congr e (UC6S846.rhoL L ⟨y, hyL⟩) := by
  ext x
  rw [mulAutRestrict_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    barImage_equiv_rhoL_apply hLI he hyL hyI (e.symm x), e.apply_symm_apply]

theorem fixed_point_clause_of_components
    (hFixFree : Inputs1719.K_L2SzFieldFixedFree)
    {D : Data G} {X L K : Subgroup G} {p r : ℕ}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L)
    (hLcal : L ∈ calC X) (hKcal : K ∈ calC X)
    (hshapeL : (p = 3 ∧ r = 7 ∧ IsL2 (Bar2 L) 3) ∨
      (p = 5 ∧ r = 31 ∧ IsSz (Bar2 L) 5))
    (hshapeK : (p = 3 ∧ r = 7 ∧ IsL2 (Bar2 K) 3) ∨
      (p = 5 ∧ r = 31 ∧ IsSz (Bar2 K) 5))
    (hrel : (D.T ⊓ X).relIndex
      (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2)
    (hout : ∀ y : G, GapWitness D X p y →
      (∀ (hyL : y ∈ Subgroup.normalizer (L : Set G)),
        UC6S846.rhoL L ⟨y, hyL⟩ ∉
          CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) ∧
      (∀ (hyK : y ∈ Subgroup.normalizer (K : Set G)),
        UC6S846.rhoL K ⟨y, hyK⟩ ∉
          CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K))) :
    ∀ y : G, GapWitness D X p y →
      Subgroup.centralizer (Subgroup.zpowers y : Set G) ⊓
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤ D.T ⊓ X := by
  classical
  intro y hy
  have hyM : y ∈ D.M := hy.1
  have hyord : orderOf y = p := hy.2.2.1
  have hp : p.Prime := by
    rcases hshapeL with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · norm_num
    · norm_num
  have hr : r.Prime := by
    rcases hshapeL with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
    · norm_num
    · norm_num
  have hpodd : Odd p := by
    rcases hshapeL with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · norm_num
    · norm_num
  obtain ⟨hyL, hyK⟩ := gapWitness_mem_normalizer_components hLKne hset hpodd hy
  obtain ⟨hαL, hαK⟩ := hout y hy
  have hαL' := hαL hyL
  have hαK' := hαK hyK
  intro z hz
  have hzC : z ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := hz.1
  have hzK : z ∈ X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G) := hz.2
  by_contra hzT
  let P : Subgroup G := D.T ⊓ X
  let K0 : Subgroup G := X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)
  have hPK0 : P ≤ K0 := le_inf inf_le_right (Subgroup.le_normalizer)
  have hK0X : K0 ≤ X := inf_le_left
  have hPK0norm : K0 ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hzK0 : z ∈ K0 := hzK
  have hznotP : z ∉ P := hzT
  have hSylP : CFSG.QuasithinUnique.IsSylowTwoOf P X := (sylow_inf_T D hXM hMX).1
  have hQ : CFSG.Open.pCoreOf 2 X ≤ P := (sylow_inf_T D hXM hMX).2
  have hSylPK0 : CFSG.QuasithinUnique.IsSylowTwoOf P K0 := by
    rw [CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf] at hSylP ⊢
    exact hSylP.of_le hPK0 hK0X
  have : (P.subgroupOf K0).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK0).mpr hPK0norm
  have hindex : (P.subgroupOf K0).index = r ^ 2 := by
    rw [← Subgroup.relIndex_top_right (P.subgroupOf K0), ← Subgroup.subgroupOf_self K0,
      Subgroup.relIndex_subgroupOf (H := P) (K := K0) (L := K0) le_rfl]
    exact hrel
  let t : G := TauCeti.pPart 2 z
  let w : G := TauCeti.pFreePart 2 z
  have htz : t * w = z := TauCeti.pPart_mul_pFreePart 2 z
  have ht_mem : t ∈ Subgroup.zpowers z := TauCeti.pPart_mem_zpowers 2 z
  have hw_mem : w ∈ Subgroup.zpowers z := TauCeti.pFreePart_mem_zpowers 2 z
  have htK0 : t ∈ K0 := Subgroup.zpowers_le.mpr hzK0 ht_mem
  have hwK0 : w ∈ K0 := Subgroup.zpowers_le.mpr hzK0 hw_mem
  have hwodd : ¬ 2 ∣ orderOf w :=
    TauCeti.not_dvd_orderOf_pFreePart Nat.prime_two (orderOf_pos z).ne'
  have htord : orderOf t = 2 ^ (orderOf z).factorization 2 :=
    TauCeti.orderOf_pPart Nat.prime_two (orderOf_pos z).ne'
  have htP : t ∈ P := by
    have hV : CFSG.QuasithinUnique.IsSylowTwoOf (P.subgroupOf K0) ⊤ :=
      CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSylPK0
    have htV : (⟨t, htK0⟩ : K0) ∈ (P.subgroupOf K0) := by
      refine CFSG.Quasithin.S152T.mem_of_isPGroup_of_mem_normalizer hV ?_ ?_
      · refine IsPGroup.of_card (n := (orderOf z).factorization 2) ?_
        rw [Nat.card_zpowers, Subgroup.orderOf_mk, htord]
      · rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp htV
  have hwne : w ≠ 1 := by
    intro hw1
    have hzP : z ∈ P := by
      rw [← htz, hw1, mul_one]
      exact htP
    exact hznotP hzP
  have hwpowP : w ^ (r ^ 2) ∈ P := by
    have h := Subgroup.pow_index_mem (P.subgroupOf K0) (⟨w, hwK0⟩ : K0)
    rw [hindex] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hwdvd : orderOf w ∣ r ^ 2 := by
    refine orderOf_dvd_iff_pow_eq_one.mpr ?_
    have hP2 : IsPGroup 2 ↥P := hSylP.2.1
    obtain ⟨k, hk⟩ := hP2.exists_orderOf_eq_pow ⟨w ^ (r ^ 2), hwpowP⟩
    have hkG : orderOf (w ^ (r ^ 2)) = 2 ^ k := by
      rw [← Subgroup.orderOf_mk (w ^ (r ^ 2)) hwpowP]
      exact hk
    have hoddpow : ¬ 2 ∣ orderOf (w ^ (r ^ 2)) := by
      intro h2
      exact hwodd (h2.trans (orderOf_pow_dvd (r ^ 2)))
    rw [hkG] at hoddpow
    cases k with
    | zero => exact orderOf_eq_one_iff.mp (by simpa using hkG)
    | succ k =>
      exfalso
      exact hoddpow (dvd_pow_self 2 (Nat.succ_ne_zero k))
  have hrdvd : r ∣ orderOf w := by
    obtain ⟨i, hi2, hi⟩ := (Nat.dvd_prime_pow hr).mp hwdvd
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hi
      exact hwne (orderOf_eq_one_iff.mp hi)
    rw [hi]
    exact dvd_pow_self r hi0
  let w' : G := w ^ (orderOf w / r)
  have hw'ord : orderOf w' = r :=
    orderOf_pow_orderOf_div (orderOf_pos w).ne' hrdvd
  have hw'K0 : w' ∈ K0 := Subgroup.pow_mem _ hwK0 _
  have hrodd : Odd r := by
    rcases hshapeL with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> norm_num
  have hw'notP : w' ∉ P := by
    intro hw'P
    obtain ⟨k, hk⟩ := (hSylP.2.1).exists_orderOf_eq_pow ⟨w', hw'P⟩
    have hkG : orderOf w' = 2 ^ k := by
      rwa [Subgroup.orderOf_mk] at hk
    rw [hw'ord] at hkG
    cases k with
    | zero => rw [pow_zero] at hkG; exact hr.ne_one hkG
    | succ k =>
      have h2dvd : 2 ∣ r := by
        rw [hkG]
        exact dvd_pow_self 2 (Nat.succ_ne_zero k)
      exact (Nat.not_even_iff_odd.mpr hrodd) (even_iff_two_dvd.mpr h2dvd)
  have hw'C : w' ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    have hwC : w ∈ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
      Subgroup.zpowers_le.mpr hzC hw_mem
    exact Subgroup.pow_mem _ hwC _
  have hw'X : w' ∈ X := hK0X hw'K0
  let u : Bar2 X := QuotientGroup.mk (⟨w', hw'X⟩ : ↥X)
  have huord : orderOf u = r := by
    have hdvd : orderOf u ∣ r := by
      have h1 : orderOf u ∣ orderOf (⟨w', hw'X⟩ : ↥X) :=
        orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥X)) _
      rwa [Subgroup.orderOf_mk, hw'ord] at h1
    have hne : orderOf u ≠ 1 := by
      intro h1
      have hu1 : u = 1 := orderOf_eq_one_iff.mp h1
      have hmem : (⟨w', hw'X⟩ : ↥X) ∈ CFSG.pCore 2 ↥X :=
        (QuotientGroup.eq_one_iff _).mp hu1
      have hmemP : w' ∈ CFSG.Open.pCoreOf 2 X := by
        have h2 : (⟨w', hw'X⟩ : ↥X) ∈ (CFSG.Open.pCoreOf 2 X).subgroupOf X := by
          rwa [CFSG.openPCoreOf_subgroupOf]
        exact Subgroup.mem_subgroupOf.mp h2
      exact hw'notP (hQ hmemP)
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd h hne
    · exact h
  have hLX : L ≤ X := by rw [hXeq]; exact le_sup_left
  have hKX : K ≤ X := by rw [hXeq]; exact le_sup_right
  obtain ⟨eL, heL⟩ := uc22p22l_barImage_equiv (L := X) (K := L) hLcal
  obtain ⟨eK, heK⟩ := uc22p22l_barImage_equiv (L := X) (K := K) hKcal
  have hρX : y ∈ Subgroup.normalizer (X : Set G) := hMX hyM
  let ρ : MulAut (Bar2 X) := UC6S846.rhoL X ⟨y, hρX⟩
  let αL : MulAut ↥(barImage X L) :=
    mulAutRestrict ρ (barImage X L) (rhoL_maps_barImage hLX hyL hρX)
  let αK : MulAut ↥(barImage X K) :=
    mulAutRestrict ρ (barImage X K) (rhoL_maps_barImage hKX hyK hρX)
  have hαLeq : αL = MulAut.congr eL (UC6S846.rhoL L ⟨y, hyL⟩) :=
    mulAutRestrict_rhoL_eq_congr hLX heL hyL hρX
  have hαKeq : αK = MulAut.congr eK (UC6S846.rhoL K ⟨y, hyK⟩) :=
    mulAutRestrict_rhoL_eq_congr hKX heK hyK hρX
  have hαLnon : αL ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(barImage X L) := by
    intro hin
    exact hαL' (uc22p2214_out_mem_of_congr eL (by rwa [hαLeq] at hin))
  have hαKnon : αK ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(barImage X K) := by
    intro hin
    exact hαK' (uc22p2214_out_mem_of_congr eK (by rwa [hαKeq] at hin))
  have hpow : ∀ (n : ℕ) (z : ↥(barImage X L)),
      (((αL ^ n) z : ↥(barImage X L)) : Bar2 X) = (ρ ^ n) z := by
    intro n z
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, mulAutRestrict_apply, ih]
  have hρdvd : orderOf ρ ∣ p := by
    have h1 : orderOf ρ ∣ orderOf (⟨y, hρX⟩ : ↥(Subgroup.normalizer (X : Set G))) :=
      orderOf_map_dvd (UC6S846.rhoL X) _
    rwa [Subgroup.orderOf_mk, hyord] at h1
  have hαLdvd : orderOf αL ∣ p := by
    have hρpow : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
    have hαLpow : αL ^ orderOf ρ = 1 := by
      ext z
      have h := hpow (orderOf ρ) z
      rw [hρpow, MulAut.one_apply] at h
      simpa using h
    exact (orderOf_dvd_of_pow_eq_one hαLpow).trans hρdvd
  have hαKdvd : orderOf αK ∣ p := by
    have hpowK : ∀ (n : ℕ) (z : ↥(barImage X K)),
        (((αK ^ n) z : ↥(barImage X K)) : Bar2 X) = (ρ ^ n) z := by
      intro n z
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', pow_succ', MulAut.mul_apply, MulAut.mul_apply, mulAutRestrict_apply, ih]
    have hρpow : ρ ^ orderOf ρ = 1 := pow_orderOf_eq_one ρ
    have hαKpow : αK ^ orderOf ρ = 1 := by
      ext z
      have h := hpowK (orderOf ρ) z
      rw [hρpow, MulAut.one_apply] at h
      simpa using h
    exact (orderOf_dvd_of_pow_eq_one hαKpow).trans hρdvd
  have hαLne1 : orderOf αL ≠ 1 := by
    intro h1
    refine hαLnon ?_
    rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  have hαKne1 : orderOf αK ≠ 1 := by
    intro h1
    refine hαKnon ?_
    rw [orderOf_eq_one_iff.mp h1]
    exact Subgroup.one_mem _
  have hαLord : orderOf αL = p := by
    rcases (Nat.dvd_prime hp).mp hαLdvd with h | h
    · exact absurd h hαLne1
    · exact h
  have hαKord : orderOf αK = p := by
    rcases (Nat.dvd_prime hp).mp hαKdvd with h | h
    · exact absurd h hαKne1
    · exact h
  have hshapeLbar : (p = 3 ∧ r = 7 ∧ IsL2 ↥(barImage X L) 3) ∨
      (p = 5 ∧ r = 31 ∧ IsSz ↥(barImage X L) 5) := by
    rcases hshapeL with ⟨hp3, hr7, hL2⟩ | ⟨hp5, hr31, hSz⟩
    · exact Or.inl ⟨hp3, hr7, CFSG.Blueprint.LieModel.of_mulEquiv eL hL2⟩
    · exact Or.inr ⟨hp5, hr31, CFSG.Blueprint.LieModel.of_mulEquiv eL hSz⟩
  have hshapeKbar : (p = 3 ∧ r = 7 ∧ IsL2 ↥(barImage X K) 3) ∨
      (p = 5 ∧ r = 31 ∧ IsSz ↥(barImage X K) 5) := by
    rcases hshapeK with ⟨hp3, hr7, hK2⟩ | ⟨hp5, hr31, hSz⟩
    · exact Or.inl ⟨hp3, hr7, CFSG.Blueprint.LieModel.of_mulEquiv eK hK2⟩
    · exact Or.inr ⟨hp5, hr31, CFSG.Blueprint.LieModel.of_mulEquiv eK hSz⟩
  have hsup : barImage X L ⊔ barImage X K = ⊤ := RankOneBorel.barImage_sup_eq_top hXeq
  have hcomm : ∀ a ∈ barImage X L, ∀ b ∈ barImage X K, a * b = b * a :=
    uc22p22l_barImage_commute hLcal hKcal hLKne
  have hZL : Subgroup.center ↥(barImage X L) = ⊥ := by
    rcases hshapeL with ⟨-, -, hL2⟩ | ⟨-, -, hSz⟩
    · exact center_eq_bot_of_lieModel_psl2
        (CFSG.Blueprint.LieModel.of_mulEquiv eL hL2)
    · exact center_eq_bot_of_isSz_five
        (CFSG.Blueprint.LieModel.of_mulEquiv eL hSz)
  have hdisj : barImage X L ⊓ barImage X K = ⊥ :=
    barImage_inf_eq_bot_of_center_eq_bot hLcal hKcal hLKne hZL
  let e : Bar2 X ≃* ↥(barImage X L) × ↥(barImage X K) :=
    bar2SquareEquiv hsup hcomm hdisj
  have hρu : ρ u = u := by
    change (UC6S846.rhoL X ⟨y, hρX⟩)
        (QuotientGroup.mk (⟨w', hw'X⟩ : ↥X)) = QuotientGroup.mk (⟨w', hw'X⟩ : ↥X)
    rw [UC6S846.rhoL_mk]
    congr 1
    apply Subtype.ext
    rw [UC6S846.rhoL_mk_coe]
    have hcommw : y * w' = w' * y :=
      Subgroup.mem_centralizer_iff.mp hw'C y (Subgroup.mem_zpowers y)
    calc y * w' * y⁻¹ = w' * y * y⁻¹ := by rw [hcommw]
      _ = w' := by group
  have he_decomp : u = ((e u).1 : Bar2 X) * ((e u).2 : Bar2 X) := by
    let A := (e u).1
    let B := (e u).2
    have h1 : e.symm (A, 1) = (A : Bar2 X) := by
      rw [MulEquiv.symm_apply_eq]
      exact (bar2SquareEquiv_apply_fst hsup hcomm hdisj A).symm
    have h2 : e.symm (1, B) = (B : Bar2 X) := by
      rw [MulEquiv.symm_apply_eq]
      exact (bar2SquareEquiv_apply_snd hsup hcomm hdisj B).symm
    calc u = e.symm (e u) := (e.symm_apply_apply u).symm
      _ = e.symm ((A, 1) * (1, B)) := by
            rw [Prod.mk_mul_mk, mul_one, one_mul]
      _ = e.symm (A, 1) * e.symm (1, B) := map_mul _ _ _
      _ = (A : Bar2 X) * (B : Bar2 X) := by rw [h1, h2]
  have heρ : e (ρ u) =
      (((αL (e u).1) : ↥(barImage X L)), ((αK (e u).2) : ↥(barImage X K))) := by
    have hA : e (ρ ((e u).1 : Bar2 X)) = ((αL (e u).1 : ↥(barImage X L)), 1) := by
      have hcoe : ρ ((e u).1 : Bar2 X) = ((αL (e u).1 : ↥(barImage X L)) : Bar2 X) := by
        rw [mulAutRestrict_apply]
      rw [hcoe, bar2SquareEquiv_apply_fst hsup hcomm hdisj]
    have hB : e (ρ ((e u).2 : Bar2 X)) = (1, ((αK (e u).2 : ↥(barImage X K)))) := by
      have hcoe : ρ ((e u).2 : Bar2 X) = ((αK (e u).2 : ↥(barImage X K)) : Bar2 X) := by
        rw [mulAutRestrict_apply]
      rw [hcoe, bar2SquareEquiv_apply_snd hsup hcomm hdisj]
    calc e (ρ u)
        = e (ρ ((e u).1 : Bar2 X) * ρ ((e u).2 : Bar2 X)) := by
            conv_lhs => rw [he_decomp]
            rw [map_mul]
      _ = e (ρ ((e u).1 : Bar2 X)) * e (ρ ((e u).2 : Bar2 X)) := map_mul _ _ _
      _ = ((αL (e u).1 : ↥(barImage X L)), 1) *
            (1, ((αK (e u).2 : ↥(barImage X K)))) := by rw [hA, hB]
      _ = _ := by simp [Prod.mk_mul_mk]
  have hfixA : αL (e u).1 = (e u).1 := by
    have h := congrArg Prod.fst (heρ.symm.trans (congrArg e hρu))
    simpa using h
  have hfixB : αK (e u).2 = (e u).2 := by
    have h := congrArg Prod.snd (heρ.symm.trans (congrArg e hρu))
    simpa using h
  have horderpair : orderOf (e u) = r := by
    rw [MulEquiv.orderOf_eq, huord]
  have hlcm : (orderOf (e u).1).lcm (orderOf (e u).2) = r := by
    rw [← Prod.orderOf, horderpair]
  have hdvdA : orderOf (e u).1 ∣ r := by
    rw [← hlcm]; exact Nat.dvd_lcm_left _ _
  have hdvdB : orderOf (e u).2 ∣ r := by
    rw [← hlcm]; exact Nat.dvd_lcm_right _ _
  have hord : orderOf (e u).1 = r ∨ orderOf (e u).2 = r := by
    rcases (Nat.dvd_prime hr).mp hdvdA with hA1 | hAr
    · rcases (Nat.dvd_prime hr).mp hdvdB with hB1 | hBr
      · exfalso
        rw [hA1, hB1, Nat.lcm_one_left] at hlcm
        exact hr.ne_one hlcm.symm
      · exact Or.inr hBr
    · exact Or.inl hAr
  rcases hord with hAr | hBr
  · exact (hFixFree ↥(barImage X L) p r αL hshapeLbar hαLord hαLnon
      ((e u).1) hAr) hfixA
  · exact (hFixFree ↥(barImage X K) p r αK hshapeKbar hαKord hαKnon
      ((e u).2) hBr) hfixB

theorem barImage_map_conj_of_mem_normalizer {I L : Subgroup G} (hLI : L ≤ I)
    {c : G} (hcI : c ∈ Subgroup.normalizer (I : Set G)) :
    barImage I (L.map (MulAut.conj c).toMonoidHom) =
      (barImage I L).map (UC6S846.rhoL I ⟨c, hcI⟩).toMonoidHom := by
  unfold barImage
  rw [CFSG.GroupTheory.subgroupOf_map_conj_eq_map_normalizerMonoidHom hcI, Subgroup.map_map,
    Subgroup.map_map]
  congr 1

theorem centOverO2_le_normalizer_of_component {D : Data G} {X L K : Subgroup G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L)
    (hLcal : L ∈ calC X) (hKcal : K ∈ calC X)
    (hZ : Subgroup.center ↥(barImage X L) = ⊥) :
    F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G) := by
  classical
  intro c hc
  have hcM : c ∈ D.M := (mem_centOverO2_iff.mp hc).1
  have hcX : c ∈ Subgroup.normalizer (X : Set G) := hMX hcM
  have hρc : UC6S846.rhoL X ⟨c, hcX⟩ = 1 := by
    ext u
    induction u using QuotientGroup.induction_on with
    | H x =>
      rw [MulAut.one_apply]
      exact (UC6S846.rhoL_fix_iff X ⟨c, hcX⟩ x).2
        ((mem_centOverO2_iff.mp hc).2 x x.2)
  have hLX : L ≤ X := by rw [hXeq]; exact le_sup_left
  have hmem : L.map (MulAut.conj c).toMonoidHom ∈ conjSetOf D.M L :=
    ⟨c, hcM, rfl⟩
  have hmem' : L.map (MulAut.conj c).toMonoidHom ∈ ({L, K} : Set (Subgroup G)) := by
    rw [hset]; exact hmem
  have hcase : L.map (MulAut.conj c).toMonoidHom = L ∨
      L.map (MulAut.conj c).toMonoidHom = K := by simpa using hmem'
  rcases hcase with h | h
  · exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · exfalso
    have himg : barImage X (L.map (MulAut.conj c).toMonoidHom) = barImage X L := by
      have hone : (1 : MulAut (Bar2 X)).toMonoidHom = MonoidHom.id (Bar2 X) := by
        ext x
        simp
      rw [barImage_map_conj_of_mem_normalizer hLX hcX, hρc, hone, Subgroup.map_id]
    have hKimg : barImage X K = barImage X L := by rw [← h, himg]
    have hLne : barImage X L ≠ ⊥ := by
      intro hbot
      obtain ⟨-, -, a, b, hab⟩ := (uc22p22l_barImage_isComponent (L := X) (K := L) hLcal).1
      have : Subsingleton ↥(barImage X L) := by rw [hbot]; infer_instance
      exact hab (Subsingleton.elim (a * b) (b * a))
    have hdisj : barImage X L ⊓ barImage X K = ⊥ :=
      barImage_inf_eq_bot_of_center_eq_bot hLcal hKcal hLKne hZ
    rw [hKimg, inf_idem] at hdisj
    exact hLne hdisj

theorem sup_centOverO2_le_normalizer_of_component {D : Data G} {X L K : Subgroup G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L)
    (hLcal : L ∈ calC X) (hKcal : K ∈ calC X)
    (hZ : Subgroup.center ↥(barImage X L) = ⊥) :
    X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G) := by
  refine sup_le ?_ (centOverO2_le_normalizer_of_component hXM hMX hXeq hLKne hset hLcal hKcal hZ)
  rw [hXeq]
  exact sup_le (Subgroup.le_normalizer (H := L))
    (uc22p22u_calC_normalizes hLcal hKcal hLKne)

theorem rhoL_eq_one_of_mem_centOverO2 {D : Data G} {X K : Subgroup G}
    (hKcal : K ∈ calC X) {c : G} (hc : c ∈ F08.CentOverO2 D.M X)
    (hcK : c ∈ Subgroup.normalizer (K : Set G)) :
    UC6S846.rhoL K ⟨c, hcK⟩ = 1 := by
  ext u
  induction u using QuotientGroup.induction_on with
  | H x =>
    rw [MulAut.one_apply]
    refine (UC6S846.rhoL_fix_iff K ⟨c, hcK⟩ x).2 ?_
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hKcal.1]
    refine ⟨?_, ?_⟩
    · simpa using K.mul_mem
        ((Subgroup.mem_normalizer_iff.mp hcK (x : G)).mp x.2) (K.inv_mem x.2)
    · exact (mem_centOverO2_iff.mp hc).2 (x : G)
        (CFSG.Quasithin.A3.subnormal_le hKcal.1 x.2)

theorem rhoL_eq_one_of_mem_component {M X L K : Subgroup G}
    (hXM : X ≤ M) (hLcalM : L ∈ calC M) (hKcalM : K ∈ calC M)
    (hLcalX : L ∈ calC X) (hKcalX : K ∈ calC X) (hLKne : L ≠ K)
    {l : G} (hl : l ∈ L) (hlK : l ∈ Subgroup.normalizer (K : Set G)) :
    UC6S846.rhoL K ⟨l, hlK⟩ = 1 := by
  ext u
  induction u using QuotientGroup.induction_on with
  | H x =>
    rw [MulAut.one_apply]
    refine (UC6S846.rhoL_fix_iff K ⟨l, hlK⟩ x).2 ?_
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hKcalX.1]
    have hlM : l ∈ M := hLcalM.1.le hl
    have hxM : (x : G) ∈ M := hKcalM.1.le x.2
    have hcomm : uc22p21cPi M ⟨l, hlM⟩ * uc22p21cPi M ⟨(x : G), hxM⟩ =
        uc22p21cPi M ⟨(x : G), hxM⟩ * uc22p21cPi M ⟨l, hlM⟩ :=
      uc22p22l_barImage_commute hLcalM hKcalM hLKne _ (uc22p21c_mem_barImage.mpr ⟨_, hl, rfl⟩) _
        (uc22p21c_mem_barImage.mpr ⟨_, x.2, rfl⟩)
    have hcommM : ⁅l, (x : G)⁆ ∈ pCoreOf 2 M :=
      uc22p22u_commutator_mem_pCoreOf hlM hxM hcomm
    have hxX : (x : G) ∈ X := CFSG.Quasithin.A3.subnormal_le hKcalX.1 x.2
    have hlX : l ∈ X := CFSG.Quasithin.A3.subnormal_le hLcalX.1 hl
    have hcommMemX : ⁅l, (x : G)⁆ ∈ X := by
      rw [commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem hlX hxX) (X.inv_mem hlX)) (X.inv_mem hxX)
    have hcommX : ⁅l, (x : G)⁆ ∈ pCoreOf 2 X :=
      uc22p2214_pCoreOf_inf_le hXM ⟨hcommM, hcommMemX⟩
    refine ⟨?_, by simpa [commutatorElement_def] using hcommX⟩
    simpa using K.mul_mem
      ((Subgroup.mem_normalizer_iff.mp hlK (x : G)).mp x.2) (K.inv_mem x.2)

theorem rhoL_mem_inner_of_mem_sup_centOverO2 {D : Data G} {X L K : Subgroup G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hLcalM : L ∈ calC D.M) (hKcalM : K ∈ calC D.M)
    (hLcalX : L ∈ calC X) (hKcalX : K ∈ calC X)
    (hNleK : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (K : Set G))
    {n : G} (hn : n ∈ X ⊔ F08.CentOverO2 D.M X) :
    UC6S846.rhoL K ⟨n, hNleK hn⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) := by
  classical
  have hC_le_NX : F08.CentOverO2 D.M X ≤ Subgroup.normalizer (X : Set G) :=
    fun c hc => hMX (mem_centOverO2_iff.mp hc).1
  obtain ⟨x, hxX, c, hcC, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (H := X) (K := F08.CentOverO2 D.M X) hC_le_NX).mp hn
  have hxX' : x ∈ L ⊔ K := by rwa [← hXeq]
  have hK_le_NL : K ≤ Subgroup.normalizer (L : Set G) :=
    uc22p22u_calC_normalizes hLcalX hKcalX hLKne
  obtain ⟨l, hl, k, hk, rfl⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (H := L) (K := K) hK_le_NL).mp hxX'
  have hL_le_NK : L ≤ Subgroup.normalizer (K : Set G) :=
    uc22p22u_calC_normalizes hKcalX hLcalX hLKne.symm
  have hlnK : l ∈ Subgroup.normalizer (K : Set G) := hL_le_NK hl
  have hknK : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  have hcnK : c ∈ Subgroup.normalizer (K : Set G) :=
    hNleK (Subgroup.mem_sup_right hcC)
  let lN : ↥(Subgroup.normalizer (K : Set G)) := ⟨l, hlnK⟩
  let kN : ↥(Subgroup.normalizer (K : Set G)) := ⟨k, hknK⟩
  let cN : ↥(Subgroup.normalizer (K : Set G)) := ⟨c, hcnK⟩
  have hl1 : UC6S846.rhoL K lN = 1 :=
    rhoL_eq_one_of_mem_component hXM hLcalM hKcalM hLcalX hKcalX hLKne hl hlnK
  have hc1 : UC6S846.rhoL K cN = 1 :=
    rhoL_eq_one_of_mem_centOverO2 hKcalX hcC hcnK
  have hk1 : UC6S846.rhoL K kN = MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K)) :=
    UC6S846.rhoL_inner K k hk
  change UC6S846.rhoL K (lN * kN * cN) ∈
    CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K)
  rw [map_mul, map_mul, hl1, hk1, hc1, one_mul, mul_one]
  exact ⟨QuotientGroup.mk (⟨k, hk⟩ : ↥K), rfl⟩

theorem tau_map_conj_eq_swapped {D : Data G} {X L K : Subgroup G} {p : ℕ}
    (hNM : X ⊔ F08.CentOverO2 D.M X ≤ D.M)
    (hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L) (hLKne : L ≠ K)
    (hNleL : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G))
    (hMLrel : (D.M ⊓ Subgroup.normalizer (L : Set G)).relIndex D.M = 2)
    (hp : p.Prime) (hp2 : p ≠ 2)
    {φ : ↥D.M →* DihedralGroup p}
    (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    {τ : G} (hτM : τ ∈ D.M) (hτφ : φ ⟨τ, hτM⟩ = DihedralGroup.sr 0) :
    L.map (MulAut.conj τ).toMonoidHom = K := by
  classical
  let N : Subgroup G := X ⊔ F08.CentOverO2 D.M X
  let H : Subgroup G := D.M ⊓ Subgroup.normalizer (L : Set G)
  have hHM : H ≤ D.M := inf_le_left
  have hNleH : N ≤ H := fun x hx => ⟨hNM hx, hNleL hx⟩
  have hNindex : N.index = (N.subgroupOf D.M).index * D.M.index := by
    have hmap := Subgroup.index_map_subtype (H := D.M) (K := N.subgroupOf D.M)
    rwa [Subgroup.map_subgroupOf_eq_of_le hNM] at hmap
  have hkeridx : (N.subgroupOf D.M).index = 2 * p := by
    rw [← hker, Subgroup.index_ker φ, MonoidHom.range_eq_top.mpr hφ]
    simp [DihedralGroup.nat_card]
  have hNrelM : N.relIndex D.M = 2 * p := by
    have hrel := Subgroup.relIndex_mul_index hNM
    rw [hNindex, hkeridx] at hrel
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hrel
  have hNrelH : N.relIndex H = p := by
    have hrel := Subgroup.relIndex_mul_relIndex N H D.M hNleH hHM
    rw [hMLrel, hNrelM] at hrel
    have h2 : N.relIndex H * 2 = p * 2 := by rw [hrel, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hkercomp : (φ.comp (Subgroup.inclusion hHM)).ker = N.subgroupOf H := by
    ext x
    change (φ.comp (Subgroup.inclusion hHM)) x = 1 ↔ x ∈ N.subgroupOf H
    rw [MonoidHom.comp_apply]
    constructor
    · intro h
      have h1 : (Subgroup.inclusion hHM x : ↥D.M) ∈ φ.ker := MonoidHom.mem_ker.mpr h
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact Subgroup.mem_subgroupOf.mpr h1
    · intro h
      have h1 : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp h
      have h2 : (Subgroup.inclusion hHM x : ↥D.M) ∈ N.subgroupOf D.M :=
        Subgroup.mem_subgroupOf.mpr h1
      rw [← hker] at h2
      exact MonoidHom.mem_ker.mp h2
  have hindexH : (N.subgroupOf H).index = N.relIndex H := by
    rw [← Subgroup.relIndex_top_right (N.subgroupOf H), ← Subgroup.subgroupOf_self H,
      Subgroup.relIndex_subgroupOf (H := N) (K := H) (L := H) le_rfl]
  have himgcard : Nat.card ↥(φ.comp (Subgroup.inclusion hHM)).range = p := by
    have h := Subgroup.index_ker (φ.comp (Subgroup.inclusion hHM))
    rw [hkercomp, hindexH, hNrelH] at h
    exact h.symm
  have hτnotH : τ ∉ H := by
    intro hτH
    have hτH' : (⟨τ, hτM⟩ : ↥D.M) ∈ H.subgroupOf D.M :=
      Subgroup.mem_subgroupOf.mpr hτH
    have hφτ_mem : φ ⟨τ, hτM⟩ ∈ (φ.comp (Subgroup.inclusion hHM)).range :=
      ⟨⟨τ, hτH⟩, rfl⟩
    have h2dvd : 2 ∣ Nat.card ↥(φ.comp (Subgroup.inclusion hHM)).range := by
      have hord : orderOf (φ ⟨τ, hτM⟩) = 2 := by
        rw [hτφ, DihedralGroup.orderOf_sr]
      rw [← hord]
      exact Subgroup.orderOf_dvd_natCard _ hφτ_mem
    rw [himgcard] at h2dvd
    have h2p : (2 : ℕ) = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2dvd
    exact hp2 h2p.symm
  have hneL : L.map (MulAut.conj τ).toMonoidHom ≠ L := by
    intro hL
    exact hτnotH ⟨hτM, Subgroup.mem_normalizer_iff_map_conj_eq.mpr hL⟩
  have hmem : L.map (MulAut.conj τ).toMonoidHom ∈ ({L, K} : Set (Subgroup G)) := by
    rw [hset]
    exact ⟨τ, hτM, rfl⟩
  have hcase : L.map (MulAut.conj τ).toMonoidHom = L ∨
      L.map (MulAut.conj τ).toMonoidHom = K := by simpa using hmem
  exact hcase.resolve_left hneL

theorem exists_bar2_conj_intertwines_rhoL {L K : Subgroup G} {τ : G}
    (hτ : L.map (MulAut.conj τ).toMonoidHom = K) :
    ∃ e : Bar2 L ≃* Bar2 K, ∀ (y : G)
      (hyL : y ∈ Subgroup.normalizer (L : Set G))
      (hyK : τ * y * τ⁻¹ ∈ Subgroup.normalizer (K : Set G)),
      MulAut.congr e (UC6S846.rhoL L ⟨y, hyL⟩) =
        UC6S846.rhoL K ⟨τ * y * τ⁻¹, hyK⟩ := by
  classical
  have hτinv : K.map (MulAut.conj τ⁻¹).toMonoidHom = L := by
    rw [← hτ, Subgroup.map_map]
    have hcomp : (MulAut.conj τ⁻¹).toMonoidHom.comp (MulAut.conj τ).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  let eLK : ↥L ≃* ↥K := {
    toFun k := (⟨τ * (k : G) * τ⁻¹, by
      have hk : τ * (k : G) * τ⁻¹ ∈ L.map (MulAut.conj τ).toMonoidHom :=
        ⟨(k : G), k.2, rfl⟩
      rwa [hτ] at hk⟩ : ↥K)
    invFun k := (⟨τ⁻¹ * (k : G) * τ, by
      have hk : τ⁻¹ * (k : G) * τ ∈ K.map (MulAut.conj τ⁻¹).toMonoidHom :=
        ⟨(k : G), k.2, by
          simpa [MulAut.conj_apply] using
            (show τ⁻¹ * (k : G) * (τ⁻¹)⁻¹ = τ⁻¹ * (k : G) * τ from rfl)⟩
      rwa [hτinv] at hk⟩ : ↥L)
    left_inv k := Subtype.ext (by group)
    right_inv k := Subtype.ext (by group)
    map_mul' a b := Subtype.ext (by
      change τ * ↑(a * b) * τ⁻¹ = (τ * ↑a * τ⁻¹) * (τ * ↑b * τ⁻¹)
      rw [Subgroup.coe_mul]
      group) }
  let e : Bar2 L ≃* Bar2 K :=
    QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥K) eLK
      (CFSG.pCore_map_iso 2 eLK)
  have he_apply : ∀ k : ↥L, e (QuotientGroup.mk k) =
      QuotientGroup.mk (eLK k) := fun k => QuotientGroup.congr_mk _ _ _ _ k
  have he_coe : ∀ k : ↥L, ((eLK k : ↥K) : G) = τ * (k : G) * τ⁻¹ := fun k => rfl
  refine ⟨e, ?_⟩
  intro y hyL hyK
  ext z
  obtain ⟨zL, rfl⟩ := e.surjective z
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  induction zL using QuotientGroup.induction_on with
  | H k =>
    rw [UC6S846.rhoL_mk L ⟨y, hyL⟩ k]
    rw [he_apply]
    rw [he_apply]
    rw [UC6S846.rhoL_mk K ⟨τ * y * τ⁻¹, hyK⟩ (eLK k)]
    congr 1
    apply Subtype.ext
    rw [he_coe (L.normalizerMonoidHom ⟨y, hyL⟩ k), UC6S846.rhoL_mk_coe,
      UC6S846.rhoL_mk_coe, he_coe k]
    group

theorem rhoL_mem_inner_of_component_actions {D : Data G} {X L K : Subgroup G}
    (hLcal : L ∈ calC X) (hKcal : K ∈ calC X)
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hsup : barImage X L ⊔ barImage X K = ⊤)
    (hcomm : ∀ a ∈ barImage X L, ∀ b ∈ barImage X K, a * b = b * a)
    (hdisj : barImage X L ⊓ barImage X K = ⊥)
    {y : G} (hyM : y ∈ D.M) (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hinL : UC6S846.rhoL L ⟨y, hyL⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L))
    (hinK : UC6S846.rhoL K ⟨y, hyK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K)) :
    UC6S846.rhoL X ⟨y, by
      rw [hXeq]
      exact (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
        rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp hyL,
          Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK]))⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
  classical
  have hLX : L ≤ X := by rw [hXeq]; exact le_sup_left
  have hKX : K ≤ X := by rw [hXeq]; exact le_sup_right
  have hρX : y ∈ Subgroup.normalizer (X : Set G) := by
    rw [hXeq]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
      rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp hyL,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK])
  let ρ : MulAut (Bar2 X) := UC6S846.rhoL X ⟨y, hρX⟩
  obtain ⟨eL, heL⟩ := uc22p22l_barImage_equiv (L := X) (K := L) hLcal
  obtain ⟨eK, heK⟩ := uc22p22l_barImage_equiv (L := X) (K := K) hKcal
  let αL : MulAut ↥(barImage X L) :=
    mulAutRestrict ρ (barImage X L) (rhoL_maps_barImage hLX hyL hρX)
  let αK : MulAut ↥(barImage X K) :=
    mulAutRestrict ρ (barImage X K) (rhoL_maps_barImage hKX hyK hρX)
  have hαLeq : αL = MulAut.congr eL (UC6S846.rhoL L ⟨y, hyL⟩) :=
    mulAutRestrict_rhoL_eq_congr hLX heL hyL hρX
  have hαKeq : αK = MulAut.congr eK (UC6S846.rhoL K ⟨y, hyK⟩) :=
    mulAutRestrict_rhoL_eq_congr hKX heK hyK hρX
  have hαLin : αL ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(barImage X L) := by
    rw [hαLeq]
    obtain ⟨a, ha⟩ := hinL
    refine ⟨eL a, ?_⟩
    rw [← ha]
    ext x
    simp [MulAut.conj_apply, map_mul]
  have hαKin : αK ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥(barImage X K) := by
    rw [hαKeq]
    obtain ⟨a, ha⟩ := hinK
    refine ⟨eK a, ?_⟩
    rw [← ha]
    ext x
    simp [MulAut.conj_apply, map_mul]
  let e : Bar2 X ≃* ↥(barImage X L) × ↥(barImage X K) :=
    bar2SquareEquiv hsup hcomm hdisj
  have he_decomp : ∀ u : Bar2 X, u = ((e u).1 : Bar2 X) * ((e u).2 : Bar2 X) := by
    intro u
    let A := (e u).1
    let B := (e u).2
    have h1 : e.symm (A, 1) = (A : Bar2 X) := by
      rw [MulEquiv.symm_apply_eq]
      exact (bar2SquareEquiv_apply_fst hsup hcomm hdisj A).symm
    have h2 : e.symm (1, B) = (B : Bar2 X) := by
      rw [MulEquiv.symm_apply_eq]
      exact (bar2SquareEquiv_apply_snd hsup hcomm hdisj B).symm
    calc u = e.symm (e u) := (e.symm_apply_apply u).symm
      _ = e.symm ((A, 1) * (1, B)) := by
            rw [Prod.mk_mul_mk, mul_one, one_mul]
      _ = e.symm (A, 1) * e.symm (1, B) := map_mul _ _ _
      _ = (A : Bar2 X) * (B : Bar2 X) := by rw [h1, h2]
  have heρ : ∀ u : Bar2 X, e (ρ u) =
      (((αL (e u).1) : ↥(barImage X L)), ((αK (e u).2) : ↥(barImage X K))) := by
    intro u
    have hA : e (ρ ((e u).1 : Bar2 X)) = ((αL (e u).1 : ↥(barImage X L)), 1) := by
      have hcoe : ρ ((e u).1 : Bar2 X) = ((αL (e u).1 : ↥(barImage X L)) : Bar2 X) := by
        rw [mulAutRestrict_apply]
      rw [hcoe, bar2SquareEquiv_apply_fst hsup hcomm hdisj]
    have hB : e (ρ ((e u).2 : Bar2 X)) = (1, ((αK (e u).2 : ↥(barImage X K)))) := by
      have hcoe : ρ ((e u).2 : Bar2 X) = ((αK (e u).2 : ↥(barImage X K)) : Bar2 X) := by
        rw [mulAutRestrict_apply]
      rw [hcoe, bar2SquareEquiv_apply_snd hsup hcomm hdisj]
    calc e (ρ u)
        = e (ρ ((e u).1 : Bar2 X) * ρ ((e u).2 : Bar2 X)) := by
            conv_lhs => rw [he_decomp u]
            rw [map_mul]
      _ = e (ρ ((e u).1 : Bar2 X)) * e (ρ ((e u).2 : Bar2 X)) := map_mul _ _ _
      _ = ((αL (e u).1 : ↥(barImage X L)), 1) *
            (1, ((αK (e u).2 : ↥(barImage X K)))) := by rw [hA, hB]
      _ = _ := by simp [Prod.mk_mul_mk]
  have hρin : ρ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) :=
    CFSG.GroupTheory.mem_inner_of_mulEquiv_prod e ρ αL αK heρ hαLin hαKin
  have hproof : (⟨y, hρX⟩ : ↥(Subgroup.normalizer (X : Set G))) =
      ⟨y, by
        rw [hXeq]
        exact (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by
          rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp hyL,
            Subgroup.mem_normalizer_iff_map_conj_eq.mp hyK]))⟩ := Subtype.ext rfl
  rw [hproof]
  exact hρin

theorem mem_sup_centOverO2_of_rhoL_mem_inner {D : Data G} {X : Subgroup G}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    {y : G} (hyM : y ∈ D.M)
    (hin : UC6S846.rhoL X ⟨y, hMX hyM⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X)) :
    y ∈ X ⊔ F08.CentOverO2 D.M X := by
  classical
  obtain ⟨xbar, hxbar⟩ := hin
  obtain ⟨⟨x, hxX⟩, rfl⟩ := QuotientGroup.mk_surjective xbar
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := hMX (hXM hxX)
  have hxconj : UC6S846.rhoL X ⟨x, hxN⟩ =
      MulAut.conj (QuotientGroup.mk (⟨x, hxX⟩ : ↥X)) := UC6S846.rhoL_inner X x hxX
  have hsame : UC6S846.rhoL X ⟨y, hMX hyM⟩ = UC6S846.rhoL X ⟨x, hxN⟩ := by
    rw [← hxbar, hxconj]
  have hyxM : y * x⁻¹ ∈ D.M := D.M.mul_mem hyM (D.M.inv_mem (hXM hxX))
  have hker : UC6S846.rhoL X ⟨y * x⁻¹, hMX hyxM⟩ = 1 := by
    rw [show (⟨y * x⁻¹, hMX hyxM⟩ : ↥(Subgroup.normalizer (X : Set G))) =
        ⟨y, hMX hyM⟩ * ⟨x, hxN⟩⁻¹ from Subtype.ext (by simp)]
    rw [map_mul, map_inv, hsame, mul_inv_cancel]
  have hmemcomp : (⟨y * x⁻¹, hyxM⟩ : ↥D.M) ∈
      ((UC6S846.rhoL X).comp (Subgroup.inclusion hMX)).ker := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change UC6S846.rhoL X ⟨y * x⁻¹, hMX hyxM⟩ = 1
    exact hker
  have hmap : y * x⁻¹ ∈ F08.CentOverO2 D.M X := by
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.centOverO2_eq_ker_map hMX]
    exact ⟨⟨y * x⁻¹, hyxM⟩, hmemcomp, rfl⟩
  have hcomm : F08.CentOverO2 D.M X ≤ Subgroup.normalizer (X : Set G) :=
    fun c hc => hMX (mem_centOverO2_iff.mp hc).1
  have hconjX : (y * x⁻¹) * x * (y * x⁻¹)⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp (hcomm hmap) x).mp hxX
  refine (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
    (H := X) (K := F08.CentOverO2 D.M X) hcomm).mpr ?_
  refine ⟨(y * x⁻¹) * x * (y * x⁻¹)⁻¹, hconjX, y * x⁻¹, hmap, ?_⟩
  group

theorem rhoL_mem_inner_of_conj_transport {L K N : Subgroup G} {y τ n : G}
    (hτmap : L.map (MulAut.conj τ).toMonoidHom = K)
    (hNleK : N ≤ Subgroup.normalizer (K : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hτyK : τ * y * τ⁻¹ ∈ Subgroup.normalizer (K : Set G))
    (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hn_eq : n = y * (τ * y * τ⁻¹))
    (hnN : n ∈ N)
    (hinN : UC6S846.rhoL K ⟨n, hNleK hnN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K))
    (hinL : UC6S846.rhoL L ⟨y, hyL⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) :
    UC6S846.rhoL K ⟨y, hyK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) := by
  obtain ⟨e, he⟩ := exists_bar2_conj_intertwines_rhoL hτmap
  have hconj : UC6S846.rhoL K ⟨τ * y * τ⁻¹, hτyK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) := by
    rw [← he y hyL hτyK]
    obtain ⟨a, ha⟩ := hinL
    refine ⟨e a, ?_⟩
    rw [← ha]
    ext z
    simp [MulAut.conj_apply, map_mul]
  have hsplit : (⟨τ * y * τ⁻¹, hτyK⟩ : ↥(Subgroup.normalizer (K : Set G))) =
      ⟨y⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hyK⟩ *
        ⟨n, hNleK hnN⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [hn_eq]
    group
  have hinv : UC6S846.rhoL K
      ⟨y⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hyK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) := by
    rw [hsplit, map_mul] at hconj
    have h := Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ hinN)
    simpa [mul_assoc] using h
  have hfinv : UC6S846.rhoL K ⟨y, hyK⟩ =
      (UC6S846.rhoL K
        ⟨y⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hyK⟩)⁻¹ := by
    rw [show (⟨y⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem hyK⟩ :
        ↥(Subgroup.normalizer (K : Set G))) = ⟨y, hyK⟩⁻¹ from Subtype.ext (by simp)]
    rw [map_inv, inv_inv]
  rw [hfinv]
  exact Subgroup.inv_mem _ hinv

theorem outer_of_dihedral_quotient {D : Data G} {X L K : Subgroup G} {p : ℕ}
    (hXM : X ≤ D.M) (hMX : D.M ≤ Subgroup.normalizer (X : Set G))
    (hXeq : X = L ⊔ K) (hLKne : L ≠ K)
    (hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L)
    (hLcalM : L ∈ calC D.M) (hKcalM : K ∈ calC D.M)
    (hLcalX : L ∈ calC X) (hKcalX : K ∈ calC X)
    (hsup : barImage X L ⊔ barImage X K = ⊤)
    (hcomm : ∀ a ∈ barImage X L, ∀ b ∈ barImage X K, a * b = b * a)
    (hdisj : barImage X L ⊓ barImage X K = ⊥)
    (hNleL : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G))
    (hNleK : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (K : Set G))
    (hMLrel : (D.M ⊓ Subgroup.normalizer (L : Set G)).relIndex D.M = 2)
    {φ : ↥D.M →* DihedralGroup p} (hφ : Function.Surjective φ)
    (hker : φ.ker = (X ⊔ F08.CentOverO2 D.M X).subgroupOf D.M)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpodd : Odd p) :
    ∀ y : G, GapWitness D X p y →
      (∀ hyL : y ∈ Subgroup.normalizer (L : Set G),
        UC6S846.rhoL L ⟨y, hyL⟩ ∉
          CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) ∧
      (∀ hyK : y ∈ Subgroup.normalizer (K : Set G),
        UC6S846.rhoL K ⟨y, hyK⟩ ∉
          CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K)) := by
  classical
  intro y hy
  have hyM : y ∈ D.M := hy.1
  have hyord : orderOf y = p := hy.2.2.1
  have hφy_ne : φ ⟨y, hyM⟩ ≠ 1 := by
    intro h1
    have hmem : ⟨y, hyM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr h1
    rw [hker] at hmem
    exact hy.2.1 (Subgroup.mem_subgroupOf.mp hmem)
  have hφy_dvd : orderOf (φ ⟨y, hyM⟩) ∣ p := by
    have h := orderOf_map_dvd φ ⟨y, hyM⟩
    rwa [Subgroup.orderOf_mk, hyord] at h
  have hφy_ord : orderOf (φ ⟨y, hyM⟩) = p := by
    rcases (Nat.dvd_prime hp).mp hφy_dvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hφy_ne
    · exact h1
  have hφy_rot : φ ⟨y, hyM⟩ ∈ TauCeti.dihedralRotations p := by
    rw [TauCeti.mem_dihedralRotations_iff]
    by_contra h
    push Not at h
    rcases hd : φ ⟨y, hyM⟩ with i | i
    · exact h i hd
    · rw [hd] at hφy_ord
      rw [DihedralGroup.orderOf_sr] at hφy_ord
      exact hp2 hφy_ord.symm
  obtain ⟨τ, hτφ⟩ := hφ (DihedralGroup.sr 0)
  have hτM : (τ : G) ∈ D.M := τ.2
  have hτφ' : φ ⟨(τ : G), hτM⟩ = DihedralGroup.sr 0 := hτφ
  have hτ_not_rot : DihedralGroup.sr 0 ∉ TauCeti.dihedralRotations p :=
    TauCeti.sr_notMem_dihedralRotations 0
  have hτ_conj : φ ⟨(τ : G), hτM⟩ * φ ⟨y, hyM⟩ * (φ ⟨(τ : G), hτM⟩)⁻¹ =
      (φ ⟨y, hyM⟩)⁻¹ := by
    rw [hτφ']
    exact TauCeti.conj_eq_inv_of_notMem_dihedralRotations hτ_not_rot hφy_rot
  have hτy : φ ⟨(τ : G) * y * (τ : G)⁻¹,
      D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM)⟩ =
      (φ ⟨y, hyM⟩)⁻¹ := by
    have harg : (⟨(τ : G) * y * (τ : G)⁻¹,
        D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM)⟩ : ↥D.M) =
        ⟨(τ : G), hτM⟩ * ⟨y, hyM⟩ * ⟨(τ : G), hτM⟩⁻¹ := Subtype.ext rfl
    rw [harg, map_mul, map_mul, map_inv, hτ_conj]
  have hCM : F08.CentOverO2 D.M X ≤ D.M :=
    fun c hc => (mem_centOverO2_iff.mp hc).1
  have hNM : X ⊔ F08.CentOverO2 D.M X ≤ D.M := sup_le hXM hCM
  have hτswap : L.map (MulAut.conj (τ : G)).toMonoidHom = K :=
    tau_map_conj_eq_swapped hNM hset hLKne hNleL hMLrel hp hp2 hφ hker hτM hτφ'
  have hτinv_swap : K.map (MulAut.conj (τ : G)⁻¹).toMonoidHom = L := by
    rw [← hτswap, Subgroup.map_map]
    have hcomp : (MulAut.conj (τ : G)⁻¹).toMonoidHom.comp
        (MulAut.conj (τ : G)).toMonoidHom = MonoidHom.id G := by
      ext z
      simp [MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id]
  have hτinvφ : φ ⟨(τ : G)⁻¹, D.M.inv_mem hτM⟩ = DihedralGroup.sr 0 := by
    have harg : (⟨(τ : G)⁻¹, D.M.inv_mem hτM⟩ : ↥D.M) = ⟨(τ : G), hτM⟩⁻¹ :=
      Subtype.ext rfl
    rw [harg]
    rw [map_inv, hτφ']
    exact inv_eq_of_mul_eq_one_left (by
      rw [DihedralGroup.sr_mul_sr]; simp)
  have hτinv_conj : φ ⟨(τ : G)⁻¹, D.M.inv_mem hτM⟩ * φ ⟨y, hyM⟩ *
      (φ ⟨(τ : G)⁻¹, D.M.inv_mem hτM⟩)⁻¹ = (φ ⟨y, hyM⟩)⁻¹ := by
    rw [hτinvφ]
    exact TauCeti.conj_eq_inv_of_notMem_dihedralRotations hτ_not_rot hφy_rot
  have hτinv_y : φ ⟨(τ : G)⁻¹ * y * (τ : G),
      D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hτM) hyM) hτM⟩ =
      (φ ⟨y, hyM⟩)⁻¹ := by
    have harg : (⟨(τ : G)⁻¹ * y * (τ : G),
        D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hτM) hyM) hτM⟩ : ↥D.M) =
        ⟨(τ : G)⁻¹, D.M.inv_mem hτM⟩ * ⟨y, hyM⟩ *
          ⟨(τ : G)⁻¹, D.M.inv_mem hτM⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [harg, map_mul, map_mul, map_inv, hτinv_conj]
  obtain ⟨hyL, hyK⟩ := gapWitness_mem_normalizer_components hLKne hset hpodd hy
  let n : G := y * ((τ : G) * y * (τ : G)⁻¹)
  have hnM : n ∈ D.M :=
    D.M.mul_mem hyM (D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM))
  have hφn : φ ⟨n, hnM⟩ = 1 := by
    have harg : (⟨n, hnM⟩ : ↥D.M) = ⟨y, hyM⟩ *
        ⟨(τ : G) * y * (τ : G)⁻¹,
          D.M.mul_mem (D.M.mul_mem hτM hyM) (D.M.inv_mem hτM)⟩ := Subtype.ext rfl
    rw [harg, map_mul, hτy, mul_inv_cancel]
  have hnN : n ∈ X ⊔ F08.CentOverO2 D.M X := by
    have hmem : ⟨n, hnM⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr hφn
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hinN : UC6S846.rhoL K ⟨n, hNleK hnN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) :=
    rhoL_mem_inner_of_mem_sup_centOverO2 hXM hMX hXeq hLKne hLcalM hKcalM
      hLcalX hKcalX hNleK hnN
  let n' : G := y * ((τ : G)⁻¹ * y * (τ : G))
  have hn'M : n' ∈ D.M :=
    D.M.mul_mem hyM (D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hτM) hyM) hτM)
  have hφn' : φ ⟨n', hn'M⟩ = 1 := by
    have harg : (⟨n', hn'M⟩ : ↥D.M) = ⟨y, hyM⟩ *
        ⟨(τ : G)⁻¹ * y * (τ : G),
          D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hτM) hyM) hτM⟩ := Subtype.ext rfl
    rw [harg, map_mul, hτinv_y, mul_inv_cancel]
  have hn'N : n' ∈ X ⊔ F08.CentOverO2 D.M X := by
    have hmem : ⟨n', hn'M⟩ ∈ φ.ker := MonoidHom.mem_ker.mpr hφn'
    rw [hker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hinN' : UC6S846.rhoL L ⟨n', hNleL hn'N⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) :=
    rhoL_mem_inner_of_mem_sup_centOverO2 (L := K) (K := L) hXM hMX
      (by rw [hXeq, sup_comm]) hLKne.symm hKcalM hLcalM hKcalX hLcalX hNleL hn'N
  have transportLK : UC6S846.rhoL L ⟨y, hyL⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) →
      UC6S846.rhoL K ⟨y, hyK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) := by
    intro hinL
    have hτyK : (τ : G) * y * (τ : G)⁻¹ ∈
        Subgroup.normalizer (K : Set G) := by
      have heq : (τ : G) * y * (τ : G)⁻¹ = y⁻¹ * n := by
        rw [show n = y * ((τ : G) * y * (τ : G)⁻¹) from rfl]
        group
      rw [heq]
      exact (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).inv_mem hyK) (hNleK hnN)
    exact rhoL_mem_inner_of_conj_transport hτswap hNleK hyL hτyK hyK rfl hnN hinN hinL
  have transportKL : UC6S846.rhoL K ⟨y, hyK⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K) →
      UC6S846.rhoL L ⟨y, hyL⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) := by
    intro hinK
    have hτinv_yK : (τ : G)⁻¹ * y * ((τ : G)⁻¹)⁻¹ ∈
        Subgroup.normalizer (L : Set G) := by
      have heq : (τ : G)⁻¹ * y * ((τ : G)⁻¹)⁻¹ = y⁻¹ * n' := by
        rw [show n' = y * ((τ : G)⁻¹ * y * (τ : G)) from rfl]
        group
      rw [heq]
      exact (Subgroup.normalizer (L : Set G)).mul_mem
        ((Subgroup.normalizer (L : Set G)).inv_mem hyL) (hNleL hn'N)
    have hn'_eq : n' = y * ((τ : G)⁻¹ * y * ((τ : G)⁻¹)⁻¹) := by
      rw [show n' = y * ((τ : G)⁻¹ * y * (τ : G)) from rfl]
      simp
    exact rhoL_mem_inner_of_conj_transport hτinv_swap hNleL hyK hτinv_yK hyL
      hn'_eq hn'N hinN' hinK
  have hnotboth : ¬ (UC6S846.rhoL L ⟨y, hyL⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L) ∧
      UC6S846.rhoL K ⟨y, hyK⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 K)) := by
    rintro ⟨hinL, hinK⟩
    have hinX : UC6S846.rhoL X ⟨y, hMX hyM⟩ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 X) := by
      have h := rhoL_mem_inner_of_component_actions hLcalX hKcalX hXeq hLKne
        hsup hcomm hdisj hyM hyL hyK hinL hinK
      convert h using 1
    exact hy.2.1 (mem_sup_centOverO2_of_rhoL_mem_inner hXM hMX hyM hinX)
  refine ⟨?_, ?_⟩
  · intro hyL' hinL'
    have hsame : (⟨y, hyL'⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨y, hyL⟩ := Subtype.ext rfl
    rw [hsame] at hinL'
    exact hnotboth ⟨hinL', transportLK hinL'⟩
  · intro hyK' hinK'
    have hsame : (⟨y, hyK'⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨y, hyK⟩ := Subtype.ext rfl
    rw [hsame] at hinK'
    exact hnotboth ⟨transportKL hinK', hinK'⟩

theorem gap17_45_outerAction_holds {D : Data G} :
    ∀ (V₀ V L X : Subgroup G) (p n l r : ℕ) (C Dc : Subgroup G) (Gamma : Set G) (x : G)
      (A₀ : Subgroup G),
      Ctx17_42 D V₀ V L X p n l C Dc Gamma →
      F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X →
      (F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
        F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) →
      ∀ y : G, GapWitness D X p y →
        (∀ (hyL : y ∈ Subgroup.normalizer (L : Set G)),
          UC6S846.rhoL L ⟨y, hyL⟩ ∉
            CFSG.ComponentClassification.OuterAutomorphisms.inner (Bar2 L)) ∧
        (∀ (hyK : y ∈ Subgroup.normalizer
            (CFSG.Quasithin.conjSubgroup L x : Set G)),
          UC6S846.rhoL (CFSG.Quasithin.conjSubgroup L x) ⟨y, hyK⟩ ∉
            CFSG.ComponentClassification.OuterAutomorphisms.inner
              (Bar2 (CFSG.Quasithin.conjSubgroup L x))) := by
  intro V₀ V L X p n l r C Dc Gamma x A₀ ctx h8100 hc y hy
  classical
  have h8100' := h8100
  obtain ⟨hLcal, hLne, hshapeN, hr, hrdvd, hpSig, -, -, hXprod, hMNX⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshapeN 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hKdef
  have hXprod' : (X : Set G) = (L : Set G) * (K : Set G) := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hXprod
  have hLcal0 : L ∈ calC D.M := by simpa using hLcal 0
  have hXeq : X = L ⊔ K := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : z ∈ (L : Set G) * (K : Set G) := by rwa [← hXprod']
      obtain ⟨a, ha, b, hb, rfl⟩ := hz'
      exact Subgroup.mul_mem_sup ha hb
    · refine sup_le ?_ ?_
      · intro a ha
        have h : a ∈ (L : Set G) * (K : Set G) := ⟨a, ha, 1, K.one_mem, by simp⟩
        change a ∈ (X : Set G)
        rw [hXprod']
        exact h
      · intro b hb
        have h : b ∈ (L : Set G) * (K : Set G) := ⟨1, L.one_mem, b, hb, by simp⟩
        change b ∈ (X : Set G)
        rw [hXprod']
        exact h
  have hLKne : L ≠ K := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hLne
  have hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
    rcases hc with h3 | h4
    · simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h3.1
    · simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h4.1
  have hKconj : K ∈ conjSetOf D.M L := by
    rw [← hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hKM : K ≤ D.M :=
    s13_le_of_mem_calC (uc22p2214_calC_of_mem_conjSetOf hLcal0 hKconj)
  have hLM : L ≤ D.M := s13_le_of_mem_calC hLcal0
  have hXM : X ≤ D.M := by rw [hXeq]; exact sup_le hLM hKM
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := hMNX
  obtain ⟨-, -, hsubset⟩ := conjSetOf_subset_calC_conjClosure (M := D.M) hLcal0
  have hLcalX : L ∈ calC X := by
    rw [ctx.X_eq]
    exact hsubset L (by
      refine ⟨1, D.M.one_mem, ?_⟩
      ext z; simp [MulAut.conj_apply])
  have hKcalX : K ∈ calC X := by
    rw [ctx.X_eq]
    exact hsubset K hKconj
  have hsup : barImage X L ⊔ barImage X K = ⊤ := RankOneBorel.barImage_sup_eq_top hXeq
  have hcomm : ∀ a ∈ barImage X L, ∀ b ∈ barImage X K, a * b = b * a :=
    uc22p22l_barImage_commute hLcalX hKcalX hLKne
  have hMLrel : (D.M ⊓ Subgroup.normalizer (L : Set G)).relIndex D.M = 2 :=
    s17_45_relIndex_inf_normalizer_eq_two (by rw [← hset]; simp [hLKne])
  have hsetK : ({K, L} : Set (Subgroup G)) = conjSetOf D.M K := by
    have hEqK := uc22p2214_conjSetOf_eq hKconj
    rw [hEqK]
    rw [show ({K, L} : Set (Subgroup G)) = ({L, K} : Set (Subgroup G)) from by
      ext z; simp [or_comm]]
    exact hset
  have hKconj' := hKconj
  obtain ⟨m, hmM, hmK⟩ := hKconj
  have hmK' : K = L.map (MulAut.conj m).toMonoidHom := hmK
  rcases hc with h3 | h4
  · obtain ⟨-, hL2raw, hp3, -, φ, hφ, hker⟩ := h3
    subst p
    have hL2 : IsL2 (Bar2 L) 3 := hL2raw
    have hK2 : IsL2 (Bar2 K) 3 := by
      obtain ⟨eKL⟩ := uc22p20d_bar2_conj m L
      have hKuc : K = uc22p20bCj m L := by rw [hmK', uc22p20bCj]
      rw [← hKuc] at eKL
      exact CFSG.Blueprint.LieModel.of_mulEquiv eKL hL2
    obtain ⟨eL, heL⟩ := uc22p22l_barImage_equiv (L := X) (K := L) hLcalX
    obtain ⟨eK, heK⟩ := uc22p22l_barImage_equiv (L := X) (K := K) hKcalX
    have hZL : Subgroup.center ↥(barImage X L) = ⊥ :=
      center_eq_bot_of_lieModel_psl2 (CFSG.Blueprint.LieModel.of_mulEquiv eL hL2)
    have hZK : Subgroup.center ↥(barImage X K) = ⊥ :=
      center_eq_bot_of_lieModel_psl2 (CFSG.Blueprint.LieModel.of_mulEquiv eK hK2)
    have hdisj : barImage X L ⊓ barImage X K = ⊥ :=
      barImage_inf_eq_bot_of_center_eq_bot hLcalX hKcalX hLKne hZL
    have hNleL : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G) :=
      sup_centOverO2_le_normalizer_of_component hXM hMX hXeq hLKne hset hLcalX hKcalX hZL
    have hNleK : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (K : Set G) :=
      sup_centOverO2_le_normalizer_of_component hXM hMX (by rw [hXeq, sup_comm])
        hLKne.symm hsetK hKcalX hLcalX hZK
    have hp : Nat.Prime 3 := by norm_num
    have hp2 : (3 : ℕ) ≠ 2 := by norm_num
    have hpodd : Odd 3 := by norm_num
    exact outer_of_dihedral_quotient hXM hMX hXeq hLKne hset hLcal0
      (uc22p2214_calC_of_mem_conjSetOf hLcal0 hKconj') hLcalX hKcalX hsup hcomm hdisj
      hNleL hNleK hMLrel hφ hker hp hp2 hpodd y hy
  · obtain ⟨-, hSzraw, hp5, -, φ, hφ, hker⟩ := h4
    subst p
    have hSz : IsSz (Bar2 L) 5 := hSzraw
    have hK2 : IsSz (Bar2 K) 5 := by
      obtain ⟨eKL⟩ := uc22p20d_bar2_conj m L
      have hKuc : K = uc22p20bCj m L := by rw [hmK', uc22p20bCj]
      rw [← hKuc] at eKL
      exact CFSG.Blueprint.LieModel.of_mulEquiv eKL hSz
    obtain ⟨eL, heL⟩ := uc22p22l_barImage_equiv (L := X) (K := L) hLcalX
    obtain ⟨eK, heK⟩ := uc22p22l_barImage_equiv (L := X) (K := K) hKcalX
    have hZL : Subgroup.center ↥(barImage X L) = ⊥ :=
      center_eq_bot_of_isSz_five (CFSG.Blueprint.LieModel.of_mulEquiv eL hSz)
    have hZK : Subgroup.center ↥(barImage X K) = ⊥ :=
      center_eq_bot_of_isSz_five (CFSG.Blueprint.LieModel.of_mulEquiv eK hK2)
    have hdisj : barImage X L ⊓ barImage X K = ⊥ :=
      barImage_inf_eq_bot_of_center_eq_bot hLcalX hKcalX hLKne hZL
    have hNleL : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (L : Set G) :=
      sup_centOverO2_le_normalizer_of_component hXM hMX hXeq hLKne hset hLcalX hKcalX hZL
    have hNleK : X ⊔ F08.CentOverO2 D.M X ≤ Subgroup.normalizer (K : Set G) :=
      sup_centOverO2_le_normalizer_of_component hXM hMX (by rw [hXeq, sup_comm])
        hLKne.symm hsetK hKcalX hLcalX hZK
    have hp : Nat.Prime 5 := by norm_num
    have hp2 : (5 : ℕ) ≠ 2 := by norm_num
    have hpodd : Odd 5 := by norm_num
    exact outer_of_dihedral_quotient hXM hMX hXeq hLKne hset hLcal0
      (uc22p2214_calC_of_mem_conjSetOf hLcal0 hKconj') hLcalX hKcalX hsup hcomm hdisj
      hNleL hNleK hMLrel hφ hker hp hp2 hpodd y hy

theorem fixed_point_clause_of_case34 {D : Data G}
    (hFixFree : Inputs1719.K_L2SzFieldFixedFree)
    {V₀ V L X : Subgroup G} {p n l r : ℕ} {C Dc : Subgroup G} {Gamma : Set G} {x : G}
    {A₀ : Subgroup G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (h8100 : F08.Hyp8100 D ![L, CFSG.Quasithin.conjSubgroup L x] ![n, n] r p A₀ X)
    (hc : F08.Case8100ThreeR D ![L, CFSG.Quasithin.conjSubgroup L x] p X ∨
      F08.Case8100FourR D ![L, CFSG.Quasithin.conjSubgroup L x] p X) :
    ∀ y : G, GapWitness D X p y →
      Subgroup.centralizer (Subgroup.zpowers y : Set G) ⊓
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) ≤ D.T ⊓ X := by
  classical
  have h8100' := h8100
  obtain ⟨hLcal, hLne, hshapeN, hr, hrdvd, hpSig, -, -, hXprod, hMNX⟩ := h8100
  have hshape0 : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hshapeN 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Nat.gcd_self] at hrdvd
  set K : Subgroup G := CFSG.Quasithin.conjSubgroup L x with hKdef
  have hXprod' : (X : Set G) = (L : Set G) * (K : Set G) := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hXprod
  have hLcal0 : L ∈ calC D.M := by simpa using hLcal 0
  have hXeq : X = L ⊔ K := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : z ∈ (L : Set G) * (K : Set G) := by rwa [← hXprod']
      obtain ⟨a, ha, b, hb, rfl⟩ := hz'
      exact Subgroup.mul_mem_sup ha hb
    · refine sup_le ?_ ?_
      · intro a ha
        have h : a ∈ (L : Set G) * (K : Set G) := ⟨a, ha, 1, K.one_mem, by simp⟩
        change a ∈ (X : Set G)
        rw [hXprod']
        exact h
      · intro b hb
        have h : b ∈ (L : Set G) * (K : Set G) := ⟨1, L.one_mem, b, hb, by simp⟩
        change b ∈ (X : Set G)
        rw [hXprod']
        exact h
  have hLKne : L ≠ K := by
    simpa [hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using hLne
  have hset : ({L, K} : Set (Subgroup G)) = conjSetOf D.M L := by
    rcases hc with h3 | h4
    · simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h3.1
    · simpa [conjSetOf, hKdef, Matrix.cons_val_zero, Matrix.cons_val_one] using h4.1
  have hKconj : K ∈ conjSetOf D.M L := by
    rw [← hset]; exact Set.mem_insert_iff.mpr (Or.inr rfl)
  have hKM : K ≤ D.M :=
    s13_le_of_mem_calC (uc22p2214_calC_of_mem_conjSetOf hLcal0 hKconj)
  have hLM : L ≤ D.M := s13_le_of_mem_calC hLcal0
  have hXM : X ≤ D.M := by rw [hXeq]; exact sup_le hLM hKM
  have hMX : D.M ≤ Subgroup.normalizer (X : Set G) := hMNX
  have hXne : X ≠ L := by
    intro hXL
    have hKleL : K ≤ L := by
      have : K ≤ X := by rw [hXeq]; exact le_sup_right
      rwa [hXL] at this
    have hKcard : Nat.card ↥K = Nat.card ↥L := by
      rw [hKdef, CFSG.Quasithin.conjSubgroup]
      exact Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective
    have hKL : K = L := Subgroup.eq_of_le_of_card_ge hKleL (by rw [hKcard])
    exact hLKne hKL.symm
  have hXsup : conjClosure D.M L = L ⊔ K := by rw [← ctx.X_eq, hXeq]
  obtain ⟨-, -, hsubset⟩ := conjSetOf_subset_calC_conjClosure (M := D.M) hLcal0
  have hLself : L ∈ conjSetOf D.M L := by
    refine ⟨1, D.M.one_mem, ?_⟩
    ext z
    simp [MulAut.conj_apply]
  have hLcalX : L ∈ calC X := by
    rw [ctx.X_eq]
    exact hsubset L hLself
  have hKcalX : K ∈ calC X := by
    rw [ctx.X_eq]
    exact hsubset K hKconj
  obtain ⟨m, hmM, hmK⟩ := hKconj
  have hmK' : K = L.map (MulAut.conj m).toMonoidHom := hmK
  rcases hc with h3 | h4
  · have h3' := h3
    obtain ⟨-, hL2raw, hp3, -, φ, hφ, hker⟩ := h3
    have hL2 : IsL2 (Bar2 L) 3 := hL2raw
    have hn3 : n = 3 := by
      rcases hshape0 with hN | hN
      · exact isL2_field_unique hN hL2
      · exact (P2214S.false_of_isSz_of_isL2 hN hL2).elim
    have hr7 : r = 7 := by
      have hdvd7 : r ∣ 7 := by simpa [hn3] using hrdvd
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd7 with h | h
      · exact absurd h hr.ne_one
      · exact h
    have hK2 : IsL2 (Bar2 K) 3 := by
      obtain ⟨eKL⟩ := uc22p20d_bar2_conj m L
      have hKuc : K = uc22p20bCj m L := by
        rw [hmK', uc22p20bCj]
      rw [← hKuc] at eKL
      exact CFSG.Blueprint.LieModel.of_mulEquiv eKL hL2
    have hshapeL : (p = 3 ∧ r = 7 ∧ IsL2 (Bar2 L) 3) ∨
        (p = 5 ∧ r = 31 ∧ IsSz (Bar2 L) 5) :=
      Or.inl ⟨hp3, hr7, hL2⟩
    have hshapeK : (p = 3 ∧ r = 7 ∧ IsL2 (Bar2 K) 3) ∨
        (p = 5 ∧ r = 31 ∧ IsSz (Bar2 K) 5) :=
      Or.inl ⟨hp3, hr7, hK2⟩
    have hrel : (D.T ⊓ X).relIndex
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2 :=
      (borel_order_data_of_case34 ctx h8100' (Or.inl h3')).2.1
    refine fixed_point_clause_of_components hFixFree hXM hMX hXeq hLKne hset hLcalX hKcalX
      hshapeL hshapeK hrel ?_
    intro y hy
    have h := gap17_45_outerAction_holds V₀ V L X p n l r C Dc Gamma x A₀ ctx h8100'
      (Or.inl h3') y hy
    refine ⟨h.1, ?_⟩
    intro hyK
    exact h.2 hyK
  · have h4' := h4
    obtain ⟨-, hSzraw, hp5, -, φ, hφ, hker⟩ := h4
    have hSz : IsSz (Bar2 L) 5 := hSzraw
    have hn5 : n = 5 := by
      rcases hshape0 with hN | hN
      · exact (P2214S.false_of_isSz_of_isL2 hSz hN).elim
      · exact eq_five_of_isSz_five hN hSzraw
    have hr31 : r = 31 := by
      have hdvd31 : r ∣ 31 := by simpa [hn5] using hrdvd
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 31)).mp hdvd31 with h | h
      · exact absurd h hr.ne_one
      · exact h
    have hK2 : IsSz (Bar2 K) 5 := by
      obtain ⟨eKL⟩ := uc22p20d_bar2_conj m L
      have hKuc : K = uc22p20bCj m L := by
        rw [hmK', uc22p20bCj]
      rw [← hKuc] at eKL
      exact CFSG.Blueprint.LieModel.of_mulEquiv eKL hSz
    have hshapeL : (p = 3 ∧ r = 7 ∧ IsL2 (Bar2 L) 3) ∨
        (p = 5 ∧ r = 31 ∧ IsSz (Bar2 L) 5) :=
      Or.inr ⟨hp5, hr31, hSz⟩
    have hshapeK : (p = 3 ∧ r = 7 ∧ IsL2 (Bar2 K) 3) ∨
        (p = 5 ∧ r = 31 ∧ IsSz (Bar2 K) 5) :=
      Or.inr ⟨hp5, hr31, hK2⟩
    have hrel : (D.T ⊓ X).relIndex
        (X ⊓ Subgroup.normalizer ((D.T ⊓ X : Subgroup G) : Set G)) = r ^ 2 :=
      (borel_order_data_of_case34 ctx h8100' (Or.inr h4')).2.1
    refine fixed_point_clause_of_components hFixFree hXM hMX hXeq hLKne hset hLcalX hKcalX
      hshapeL hshapeK hrel ?_
    intro y hy
    have h := gap17_45_outerAction_holds V₀ V L X p n l r C Dc Gamma x A₀ ctx h8100'
      (Or.inr h4') y hy
    refine ⟨h.1, ?_⟩
    intro hyK
    exact h.2 hyK

theorem gap17_45_borelDataCtx_of {D : Data G}
    (hFixFree : Inputs1719.K_L2SzFieldFixedFree) :
    Gap17_45_BorelDataCtx D := by
  intro V₀ V L X p n l r C Dc Gamma x A₀ ctx h8100 hc
  exact ⟨borel_order_data_of_case34 ctx h8100 hc,
    fixed_point_clause_of_case34 hFixFree ctx h8100 hc⟩

section CertifiedAssembly


theorem seventeen_fortyfive_of_borel (D : Data G) (V₀ V : Subgroup G)
    (h1 : ∀ hV : Hyp125 D V₀ V, R17_1At D V₀ V hV)
    (h44_1 : R17_44_1AtB D V₀ V) (h44_2 : R17_44_2AtB D V₀ V)
    (h44_3 : R17_44_3AtB D V₀ V) (h899 : F08.R899 D)
    (h8100R : CFSG.Open.evenRank G ≠ 3 → F08.R8100R D)
    (hE3 : CFSG.Open.evenRank G = 3 → F07.R77E2 D ∧ R847E3ThinNN D)
    (h13 : SigmaRankThree13 D) (hSg : UC6S846.SigmaStd D)
    (hK3 : Inputs1719.K_BorelTorusAbelianRankTwoNotL34)
    (hK4 : Inputs1719.K_CartanRankLeThree)
    (hN : uc22p20rNativeGriess)
    (h33_2 : R17_33_2 D) (h33_3 : ∀ _hV : Hyp125 D V₀ V, R17_33_3At D V₀ V)
    (h846 : F08.R846 D)
    (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (h1219 : D.sig = D.sig1)
    (hKG : CFSG.Open.IsKGroup ↥D.M)
    (hKF : CFSG.LocalAnalysis.RankThreeTheoremC.KFactInnerAction)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (h147 : Inputs1719.UC2_14_7Three D)
    (hg5 : Gap17_45_UniqueMaxFive D V₀ V)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h126 : R126 D) (h86 : W3Lem86_1 G)
    (h111 : W3Thm111 G) (h61 : UC6.R6_1 D)
    (hx : DataExt D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h1214 : F12.R1214 D) (h869 : F08.R869 D) (h640 : UC6.R6_40_2 D)
    (hFF : W4Thm12McClurg) (hW4a : Inputs1719.W4Lem14_6aSmall) : R17_45At D V₀ V :=
  seventeen_fortyfive D V₀ V h1 h44_1 h44_2 h44_3 h899 h8100R h614 hE3 h13 hSg hK3 hK4 hN
    Inputs1719.k_L2SzPairOuterRank_holds h33_2 h33_3 h846
    (gap17_45_borelDataCtx_of Inputs1719.k_L2SzFieldFixedFree_holds)
    (gap17_45_pRanCtxAt_of D h76 h614 hSg h1219 h1 hK3 hK4)
    hKG hKF h93 h147 hg5 h1669 hTim hcat h66 h88 h126 h86 h111 h61 hx h127 h1114 h162 hTor h1482
    h183 h1214 h869 h640 hFF hW4a

end CertifiedAssembly

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
