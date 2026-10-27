module

public import CFSG.LocalAnalysis.StandardType.GGRowKFrame
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviAssemble
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkTransport
public import CFSG.LocalAnalysis.StandardType.GGRowKSide
public import CFSG.LocalAnalysis.StandardType.GGDepAOddLarge
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Defs
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGPZWeylType
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputHolds
public import CFSG.LocalAnalysis.StandardType.ZS.Adapter
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepAtLK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepAtThree
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepMove
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepPos
public import CFSG.LocalAnalysis.StandardType.GGResThreeSettledDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Monster.B.Geometry CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem three_le_card_survivor_of_automizer_order
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs X J : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {S : Finset Λ}
    {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ} (hWM : GGIsWeylMatrix M)
    (hC : GGIntCartan M C) (hdel : GGDeletedConnectedS M S)
    {ψ : Λ → MulAut ↥Bs} {f : M.Group ≃* ↥(ggAutomizer X Bs)}
    (hf : ∀ i, (f (M.simple i) : MulAut ↥Bs) = ψ i)
    (hclosJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => ψ j))
    {r : ℕ} (hAJ : Nat.card (ggAutomizer J Bs) = (r - 2).factorial) (hr : 6 ≤ r) :
    3 ≤ Fintype.card {j : Λ // j ∉ S} := by
  classical
  by_contra hlt
  have hle : Fintype.card {j : Λ // j ∉ S} ≤ 2 := by omega
  have hne : Nonempty {j : Λ // j ∉ S} := by
    by_contra hne
    haveI : IsEmpty {j : Λ // j ∉ S} := not_nonempty_iff.mp hne
    have hbot : ggAutomizer J Bs = ⊥ := by
      rw [hclosJ]
      simp
    have hcard : Nat.card (ggAutomizer J Bs) = 1 := by
      rw [hbot]
      simp
    rw [hAJ] at hcard
    have h4 : 4 ≤ r - 2 := by omega
    have hfac : 8 ≤ (r - 2).factorial :=
      (show (8 : ℕ) ≤ Nat.factorial 4 by norm_num).trans (Nat.factorial_le h4)
    omega
  have hWMJ : GGIsWeylMatrix (parMatrix M {j : Λ | j ∉ S}) :=
    l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S M C hWM hC hdel hne
  have hdata := ggWeylTypeData_of_isWeylMatrix hWMJ
  have hle12 : Nat.card (parMatrix M {j : Λ | j ∉ S}).Group ≤ 12 :=
    ggWeylTypeData_card_le_twelve_of_rank_le_two hdata hle
  let jEquiv : (parMatrix M {j : Λ | j ∉ S}).Group ≃* ↥(ggAutomizer J Bs) :=
    ggParabolic_equiv_of_generator_equiv M {j : Λ | j ∉ S} ψ f hf hclosJ
  have hcardEq : Nat.card (parMatrix M {j : Λ | j ∉ S}).Group =
      Nat.card (ggAutomizer J Bs) := Nat.card_congr jEquiv.toEquiv
  rw [hcardEq, hAJ] at hle12
  have h4 : 4 ≤ r - 2 := by omega
  have hfac : 12 < (r - 2).factorial :=
    (show (12 : ℕ) < Nat.factorial 4 by norm_num).trans_le (Nat.factorial_le h4)
  omega

theorem ggSideDatum_of_exact3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs K J L : Subgroup G} {r : ℕ}
    (h3 : GGResLeviDatumExact3 p Bs K J L (fun _ _ => True) (fun _ _ => True))
    (hAJ : Nat.card (ggAutomizer J Bs) = (r - 2).factorial) (hr : 6 ≤ r) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  obtain ⟨k, hk1, hk3, hrev⟩ :=
    ggResLeviDatumCard_reverse (k := 3) (by norm_num) (by norm_num) h3
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hScard, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin, hrefl, hpairL, hpairK,
    hsel, hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := hrev
  obtain ⟨fL, hfL⟩ := hfLx
  let ψ : Λ → MulAut ↥Bs := fun i => φ (Sum.inl i)
  let hψ : Λ → V := fun i => h (Sum.inl i)
  let αψ : Λ → Module.Dual (ZMod p) V := fun i => α (Sum.inl i)
  have hlinψ : ∀ i w, ggLin (p := p) ι (ψ i) w = w - αψ i w • hψ i :=
    fun i => hlin (Sum.inl i)
  have hreflψ : ∀ i, GGIsReflection p (ψ i) := fun i => hrefl (Sum.inl i)
  have hpairψ : ∀ i j, αψ i (hψ j) = (CL i j : ZMod p) := fun i j => hpairL i j
  have hclosJψ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ∉ S} => ψ j) := by
    simpa [ψ] using hclosJ
  have h3J : 3 ≤ Fintype.card {j : Λ // j ∉ S} :=
    three_le_card_survivor_of_automizer_order (p := p) hWML hCLL hdel
      (ψ := ψ) (f := fL) (hf := fun i => hfL i) hclosJψ hAJ hr
  have hne : Nonempty {j : Λ // j ∉ S} :=
    Fintype.card_pos_iff.mp (by omega)
  have hWMJ : GGIsWeylMatrix (parMatrix ML {j : Λ | j ∉ S}) :=
    l05nBL_ggIsWeylMatrix_parMatrix_of_deletedConnected S ML CL hWML hCLL hdel hne
  rcases (by omega : k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl
  · left
    have hScard1 : S.card = 1 := hScard
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hScard1
    have hrange : Set.range (fun j : {j : Λ // j ≠ b} => ψ j) =
        Set.range (fun j : {j : Λ // j ∉ S} => ψ j) := by
      subst hb
      let e : {j : Λ // j ≠ b} ≃ {j : Λ // j ∉ ({b} : Finset Λ)} :=
        Equiv.subtypeEquivRight (fun j => by simp)
      have hcomp : (fun j : {j : Λ // j ≠ b} => ψ j) =
          (fun j : {j : Λ // j ∉ ({b} : Finset Λ)} => ψ j) ∘ e := rfl
      rw [hcomp, Set.range_comp, e.surjective.range_eq, Set.image_univ]
    have hJb : ggAutomizer J Bs = Subgroup.closure
        (Set.range fun j : {j : Λ // j ≠ b} => ψ j) := by
      rw [hclosJψ, hrange]
    have hset : {j : Λ | j ≠ b} = {j : Λ | j ∉ S} := by
      subst hb
      ext j
      simp
    have hcardT : Fintype.card {j : Λ // j ∉ S} = Fintype.card Λ - S.card := by
      rw [Fintype.card_subtype_compl]
      congr 1
      simpa using Fintype.card_coe S
    have hcardTb : Fintype.card {j : Λ // j ≠ b} = Fintype.card Λ - 1 := by
      rw [Fintype.card_subtype_compl]
      congr 1
    have h3b : 3 ≤ Fintype.card {j : Λ // j ≠ b} := by
      rw [hcardTb]
      have h := h3J
      rw [hcardT, hScard1] at h
      exact h
    have hWMJb : GGIsWeylMatrix (parMatrix ML {j : Λ | j ≠ b}) := by
      rw [hset]
      exact hWMJ
    exact ggResSideDatum_of_weylMatrix hp2 hWML hCLL hlinψ hreflψ hpairψ
      hfL hclosL b hJb hWMJb h3b
  · right
    exact ggResLeviSideDatumLE3_of_weylMatrix hp2 hWML hCLL hlinψ hreflψ hpairψ
      hfL hclosL S (by omega) (by omega) hclosJψ hWMJ h3J
  · right
    exact ggResLeviSideDatumLE3_of_weylMatrix hp2 hWML hCLL hlinψ hreflψ hpairψ
      hfL hclosL S (by omega) (by omega) hclosJψ hWMJ h3J


theorem ggExactThreeAtK_false_of_dep
    (hKG : GGReflClassLargeInput') (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) {N : ℕ}
    (hN : 11 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hcardBs : Nat.card Bs = p ^ (N - 1)) (hdep : ¬ LinearIndependent (ZMod p) h)
    (h3 : GGResLeviDatumExact3 p Bs K J L (fun _ _ => True) (fun _ _ => True))
    {r : ℕ} (hAJ : Nat.card (ggAutomizer J Bs) = (r - 2).factorial) (hr : 10 ≤ r) : False := by
  classical
  have hN5 : 5 ≤ N := by omega
  haveI : Fintype ↥Bs := Fintype.ofFinite ↥Bs
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hfixK : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y :=
    ggXDatumA_fix_K_of_card hp2 hH hy hN5 hpN hcardBs e hMK hCK hφ hpair hAK
  let F : GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i))
      (ι (Additive.ofMul ⟨y, hy⟩)) :=
    ggXDatumA_frame_K hp2 hH hy hfixK hN5 hpN e hMK hCK hφ hpair hAK hdep
  have hJK : ggAutomizer J Bs ≤ ggAutomizer K Bs := by
    obtain ⟨Λ', i1, i2, S, Λa, i3, i4, ML, CL, MK', CK', V', i5, i6, ι', φ', h', α',
      hS3, hA1, hA3, hWML, hCLL, hWMK, hCKK, htyp, hlin', hrefl', hpairL, hpairK, hsel,
      hfLx, hfKx, hclosL, hclosK, hdel, hclosJ⟩ := h3
    rw [hclosJ, hclosL]
    refine Subgroup.closure_mono ?_
    rintro z ⟨j, rfl⟩
    exact ⟨j.1, rfl⟩
  have hLside : GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J :=
    ggSideDatum_of_exact3 hp2 h3 hAJ (by omega)
  obtain ⟨t, ha, αa, htK, htlin, hαaha, hαay, hjoin, hnt, hcard⟩ :=
    hLside.elim
      (fun hL => ggTwoNodeL_lside hFix hOrbK hp2 hH hy hN5 e hφ hAK hJK F hL)
      (fun hL => ggTwoNodeL_lside_LE3 hFix hOrbK hp2 hH hy hN5 e hφ hAK hJK F hL)
  let r : Fin (N - 1) → (V ≃ₗ[ZMod p] V) := fun i => ggLin (p := p) ι (φ (e i))
  let ra : V ≃ₗ[ZMod p] V := ggLin (p := p) ι t
  have hr' : ∀ i v, r i v = v - α (e i) v • h (e i) := fun i v => hφ (e i) v
  have hra : ∀ v, ra v = v - αa v • ha := fun v => htlin v
  have hnt' : ∀ g ∈ Subgroup.closure (Set.range r ∪ {ra}),
      ¬ (Module.finrank (ZMod p) (ggLinMove g) = 1 ∧ ∀ w, g (g w - w) = g w - w) := by
    simpa only [r, ra] using hnt
  have hcard' : Nat.card ↥(Subgroup.closure (Set.range r ∪ {ra})) ≤
      p ^ N * (6 * (p - 1) * Nat.factorial N) := by
    simpa only [r, ra] using hcard
  by_cases hHa : ha ∈ Submodule.span (ZMod p) (Set.range (fun i : Fin (N - 1) => h (e i)))
  · exact ggDepAOdd_caseII_false hKG hp2 hN F r hr' ra ha αa hra hαaha hαay hnt' hcard' hHa
  · refine ggDepAOdd_caseI_false hKG hp2 hN F r hr' ra ha αa hra hαaha ?_ hαay hnt' hcard' hHa
    obtain ⟨c, hc⟩ := hjoin
    exact ⟨c, hc⟩

theorem ggExactThreeAtK_false_of_yNotMem
    (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) (hyK : y ∉ K) {N : ℕ}
    (hN : 11 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hcardBs : Nat.card Bs = p ^ (N - 1))
    (h3 : GGResLeviDatumExact3 p Bs K J L (fun _ _ => True) (fun _ _ => True))
    {r : ℕ} (hAJ : Nat.card (ggAutomizer J Bs) = (r - 2).factorial) (hr : 10 ≤ r) : False := by
  have hfixK : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) →
      (b : G) ∈ Subgroup.zpowers y :=
    ggXDatumA_fix_K_of_card hp2 hH hy (by omega) hpN hcardBs e hMK hCK hφ hpair hAK
  exact ggExactThreeAtK_false_of_dep hKG hOrbK hFix hp2 hH hy hN hpN e hMK hCK hφ hpair hAK
    hcardBs (ggXDatumA_dep_K hp2 hH hy hyK hfixK (by omega) hpN e hMK hCK hφ hpair hAK) h3 hAJ hr

theorem ggResExactThree_K_highDegree_of_yNotMem
    (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hModel : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 11 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (hKG : GGReflClassLargeInput')
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hy : y ∈ Bs) (hyK : y ∉ K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (_hF : ¬ GGCoxeterForkDatum p Bs L K) (_hS : ¬ GGCoxeterStdDatum p Bs L K)
    (_hE : ¬ GGE6DepPerpCfg p Bs L K) : False := by
  classical
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨r, hd_eq, hpd, hXD, hcard, hcent, hBlt, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hModel hpq (by omega) hdiag h3
  obtain ⟨Λ, i1, i2, M, C, V, i3, i4, ι, φ, h, α, e, hMeq, hWM, hC, hlin, hrefl, hpair,
    hf, hclos⟩ := hXD
  let := i1
  let := i2
  let := i3
  let := i4
  refine ggExactThreeAtK_false_of_yNotMem hLB hKG hOrbK hFix hp2 hH hy hyK (N := r + 1)
    (by omega) (by simpa [hd_eq] using hpd) (e := ?_) (MK := M) (CK := C) ?_ hC hlin hpair
    hclos (by simpa using hcard) h3 hAJ (by omega)
  · simpa using e
  · simpa using hMeq

theorem ggResExactThree_K_highDegree_join_of_yNotMem
    (hLB : GGLBalanceInput) {G : Type} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F] {n d p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hModel : UnitTB.Model ψ)
    (hpq : p ∣ 2 ^ n + 1) (hd : 11 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, LineU.ActsDiagU ψ a t)
    (hKG : GGReflClassLargeInput')
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    (hy : y ∈ Bs) (hyK : y ∉ K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (hF : ¬ GGCoxeterForkDatum p Bs L K) (hS : ¬ GGCoxeterStdDatum p Bs L K)
    (hE : ¬ GGE6DepPerpCfg p Bs L K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) :=
  (ggResExactThree_K_highDegree_of_yNotMem hLB hH hModel hpq hd hdiag hKG hOrbK hFix hy hyK h3 hF hS hE).elim

theorem ggResExactThree_K_highDegree_externalAxis
    (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput')
    (hOrbK : GGResCentBoundNbrInput) (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1)
      p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny)
    (hF : ¬ GGCoxeterForkDatum p Bs L K) (hS : ¬ GGCoxeterStdDatum p Bs L K)
    (hE : ¬ GGE6DepPerpCfg p Bs L K)
    (_hreserved : ¬ ggReservedRows p J L K)
    (_htwo : ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K))
    (_hC2 : ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K))
    (_hSU2 : ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K))
    (hyK : y ∉ K) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) :=
    (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  dsimp only at hP₀
  obtain ⟨⟨htag, hr10, hn2, hpq⟩, hN₀, hact₀⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 10 ≤ rank at hr10
  change 2 ≤ n at hn2
  change p ∣ 2 ^ n + 1 at hpq
  subst tag
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨hSimple, hNonAb, θ, hP⟩ := hQ
  obtain ⟨hlabel, hN', hact⟩ := hP
  have h63 : ¬ (rank + 1 = 6 ∧ p = 3) := by omega
  obtain ⟨ψ, hModel, hdiag⟩ :=
    GGResHyp.exists_unitaryModel_K_of_marking_data hH hFK (by omega : 1 ≤ n)
      (by omega : 5 ≤ rank + 1) hpq h63 θ hN hact
  exact (ggResExactThree_K_highDegree_of_yNotMem hLB hH hModel (by omega) (by omega)
    hdiag hKG hOrbK hFix hy hyK h3 hF hS hE).elim

section HighDegreeBothAxes

open CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU TableB

private theorem l05nUHD_datum
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ∃ N : ℕ, 11 ≤ N ∧ p ∣ N ∧ GGResXDatumA p Bs K (N - 1) ∧ Nat.card ↥Bs = p ^ (N - 1) ∧
      Nat.card ↥(ggAutomizer J Bs) = (N - 1 - 2).factorial := by
  classical
  obtain ⟨-, lab, hΛ, hraw⟩ := hU
  obtain ⟨R₀, iR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨⟨htag, hrank, hpq⟩, -, -⟩ := hP₀
  obtain ⟨tag, rank, n⟩ := lab
  change tag = .twA at htag
  change 10 ≤ rank at hrank
  change p ∣ 2 ^ n + 1 at hpq
  subst htag
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨F, hField, hFinite, hFK, hQ⟩ := hraw
  let _ : Field F := hField
  let _ : Finite F := hFinite
  obtain ⟨-, -, θ, -, hNK, hact⟩ := hQ
  have h63 : ¬ (rank + 1 = 6 ∧ p = 3) := by omega
  obtain ⟨ψ, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_marking_data hFK hΛ.1 (by omega) hpq h63 θ hNK hact
  obtain ⟨r, hdr, hpd, hXA, hcardBs, -, -, hcardJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq (by omega) hdiag h3
  have hr : rank = r := by omega
  subst hr
  exact ⟨rank + 1, by omega, hpd, by simpa using hXA, by simpa using hcardBs,
    by simpa using hcardJ⟩

theorem ggFinrank_eq_of_card_Bs {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {N : ℕ} (hcardBs : Nat.card ↥Bs = p ^ (N - 1)) :
    Module.finrank (ZMod p) V = N - 1 := by
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rwa [Nat.card_zmod] at hc
  have hcardV : Nat.card V = Nat.card ↥Bs := by
    rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
    exact (Nat.card_congr ι.toEquiv).symm
  have heq : p ^ Module.finrank (ZMod p) V = p ^ (N - 1) := by
    rw [← hVcard, hcardV, hcardBs]
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le heq

theorem ggResLeviDatumExact3_reflGenerated_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L J K : Subgroup G} (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGReflGenerated p (ggAutomizer L Bs) := by
  obtain ⟨Λ₃, _, _, S, Λa, _, _, -, -, -, -, _, _, _, -, φ₃, -, -,
    -, -, -, -, -, -, -, -, -, hrefl₃, -, -, -, -, -, -, hcl₃, -, -⟩ := h3
  let φL : {i : Λ₃ // i ∉ S} ⊕ Λa → MulAut ↥Bs := fun o => φ₃ (o.map Subtype.val id)
  have hrange : Set.range φL =
      Set.range (fun j : {j : Λ₃ // j ∉ S} => φ₃ (Sum.inl (j : Λ₃))) ∪
        Set.range (fun a : Λa => φ₃ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range φL) := by
    rw [hcl₃, ← hrange]
  exact ggIndep_reflGenerated_of_closure (φ := φL) (fun o => hrefl₃ (o.map Subtype.val id)) hclosL

private theorem l05nUHD_indep (hKG : GGReflClassLargeInput') (hFix : GGTBFixInput)
    (hOrbK : GGResCentBoundNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) {N : ℕ} (hN : 11 ≤ N) (hpN : p ∣ N)
    (hcardBs : Nat.card ↥Bs = p ^ (N - 1))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i))
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hind : LinearIndependent (ZMod p) h)
    (hLrefl : GGReflGenerated p (ggAutomizer L Bs)) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hstrong :=
    ggXDatumA_fix_K_of_card hp2 hH hy (by omega) hpN hcardBs e hMK hCK hφ hpair hAK
  have hmove := ggIndep_moving_L hFix hH hy hLrefl
  rw [sup_comm]
  by_cases hp3 : p = 3
  · exact ggTwoNodeIndepAtK_three hKG hOrbK hp3 hH hy hstrong hLrefl (by omega) hpN hmove
      e hMK hCK hφ hrefl hpair hAK hind
  · have hp5 : 5 ≤ p := by
      have hp := (Fact.out : p.Prime)
      have h2 := hp.two_le
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
      · exact absurd h' hp2
      · exact absurd h' hp3
      · subst h'
        exact absurd hp (by norm_num)
      · exact h'
    refine ggTwoNodeIndepAtK_weyl hKG hOrbK hp5 hH hy hstrong hLrefl (by omega) hpN hmove
      e hMK hCK hφ hrefl hpair hAK hind ?_
    intro _ _ f _
    have hf := Module.finrank_eq_card_basis f
    rw [ggFinrank_eq_of_card_Bs ι hcardBs, Fintype.card_fin] at hf
    omega

theorem GGResHyp.weyl_of_unitary_highDegree_exactThree_K
    (hKG : GGReflClassLargeInput') (hFix : GGTBFixInput) (hOrbK : GGResCentBoundNbrInput)
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) p Bs K)
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hy : y ∈ Bs := hH.1.2.1.1 hH.2.2.2.2.1.1.2.1
  obtain ⟨N, hN, hpN, hXA, hcardBs, hAJ⟩ := l05nUHD_datum hLB hH hU h3
  obtain ⟨Λ, _, _, MK, CK, V, _, _, ι, φ, h, α, e, hMK, -, hCK, hφ, hrefl, hpair, -, hAK⟩ :=
    hXA
  by_cases hind : LinearIndependent (ZMod p) h
  · exact l05nUHD_indep hKG hFix hOrbK hp2 hH hy hN hpN hcardBs e hMK hCK hφ hrefl hpair hAK
      hind (ggResLeviDatumExact3_reflGenerated_L h3)
  · exact (ggExactThreeAtK_false_of_dep hKG hOrbK hFix hp2 hH hy hN hpN e hMK hCK hφ hpair hAK
      hcardBs hind h3 hAJ (by omega)).elim

theorem ggXDatumA_dep_K_of_exactThree_card_three
    (hFix : GGTBFixInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp3 : p = 3)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs) {N : ℕ}
    (hN : 5 ≤ N) (hpN : p ∣ N)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ}
    (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hcardBs : Nat.card ↥Bs = p ^ (N - 1))
    (h3 : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) :
    ¬ LinearIndependent (ZMod p) h := by
  intro hind
  have hstrong := ggXDatumA_fix_K_of_card (by omega : p ≠ 2) hH hy hN hpN
    hcardBs e hMK hCK hφ hpair hAK
  have hmove := ggIndep_moving_L hFix hH hy (ggResLeviDatumExact3_reflGenerated_L h3)
  exact ggTwoNodeIndepAtK_three_false_of_card hp3 hH hy hstrong hN hpN hmove
    e hMK hCK hφ hpair hAK hind hcardBs

section Cert


theorem ggResLeaf_unitary_highDegree_exactThree_K (hKG : GGReflClassLargeInput') :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨hU, h3, -⟩ := hP
  exact hH.weyl_of_unitary_highDegree_exactThree_K hKG ggTBFixInput_holds
    ggResCentBoundNbrInput_holds ggGammaSuppliers_proved.1
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, h.2.1, h.2.2.2⟩) hU) h3

theorem ggResLeaf_unitary_highDegree_exactThree_K_yInK (hKG : GGReflClassLargeInput') :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J y K =>
      y ∈ K ∧
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hl hP
  exact ggResLeaf_unitary_highDegree_exactThree_K hKG G p B Bs x L D J y K hH hF hS hl hP.2

theorem ggResLeaf_threeResidualK_highDegree (hKG : GGReflClassLargeInput') :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ∃ lab : LargeEvenLabel, ggThreeResidualLabelK p lab ∧ 10 ≤ lab.rank ∧
        GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs K := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ _ hP
  obtain ⟨h3, lab, ⟨htag, -, -, hpq⟩, hrank, hU⟩ := hP
  refine hH.weyl_of_unitary_highDegree_exactThree_K hKG ggTBFixInput_holds
    ggResCentBoundNbrInput_holds ggGammaSuppliers_proved.1
    (GGInnerDiagOnLabel.mono_label (fun lab' hlab => ?_) hU) h3
  rw [hlab]
  exact ⟨htag, hrank, hpq⟩

end Cert

end HighDegreeBothAxes

section OriginalLeaf


theorem ggResLeaf_unitary_highDegree_exactThree_K_yNotMem :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J y K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) ∧
      y ∉ K := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hP
  obtain ⟨hU, h3, hreserved, htwo, hC2, hSU2, hyK⟩ := hP
  have hKG : GGReflClassLargeInput' :=
    ggReflClassLargeInput_of_omega
      (ZS.ggReflClassOmegaLarge_of_useInput ZS.useInput_holds)
  exact ggResExactThree_K_highDegree_externalAxis ggGammaSuppliers_proved.1 hKG
    ggResCentBoundNbrInput_holds ggTBFixInput_holds hH hU h3 hF hS hE
    hreserved htwo hC2 hSU2 hyK

theorem ggResLeaf_unitary_highDegree_exactThree_K_holds :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      GGInnerDiagOnLabel
        (fun p lab => lab.tag = .twA ∧ 10 ≤ lab.rank ∧ 2 ≤ lab.n ∧
          p ∣ 2 ^ lab.n + 1) p Bs K ∧
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  exact ggResLeaf_unitary_highDegree_exactThree_K
    (ggReflClassLargeInput_of_omega
      (ZS.ggReflClassOmegaLarge_of_useInput ZS.useInput_holds))

end OriginalLeaf

end CFSG.StandardType

end
