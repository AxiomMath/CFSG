module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.LieType.SeitzGeneration.ExcTorusCount
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.Open.LocalVocabulary
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLFaithful
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfToralDescent
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Three
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.ExcFiveToralAux.SylowFrame
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.StandardType.ExcMaxToral

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus Polynomial
open scoped Matrix

@[expose] def excDegrees : Tag → List ℕ
  | .F4 => [2, 6, 8, 12]
  | .E7 => [2, 6, 8, 10, 12, 14, 18]
  | .E8 => [2, 8, 12, 14, 18, 20, 24, 30]
  | _ => []

@[expose] def excDegCount (τ : Tag) (d : ℕ) : ℕ := (excDegrees τ).countP fun x => d ∣ x

@[expose] def ExcLangShape (τ : Tag) (d : ℕ) (w : WeylGroup τ) : Prop :=
  (d = 1 → w = 1) ∧ (d = 2 → ∀ u : Fin τ.rank → ℤ, w • u = -u) ∧
    ((τ = .E8 ∧ (d = 3 ∨ d = 4 ∨ d = 6)) → orderOf w = d ∧
      ∃ M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ, (∀ u, w • u = M *ᵥ u) ∧
        M.charpoly = (cyclotomic d ℤ) ^ 4)

@[expose] def AdjointMaxElemToral
    (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  Finite K → CharP K 2 → p.Prime → p ≠ 2 →
    4 ≤ excDegCount τ (orderOf (Nat.card K : ZMod p)) →
    ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E →
      p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ Nat.card E →
      ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ D : LangDatum τ (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) ∧
          D.q = Nat.card K ∧
          (∃ w : WeylGroup τ, D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
            ExcLangShape τ (orderOf (Nat.card K : ZMod p)) w) ∧
          (∀ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
            D.g0 ∈ D.torus) ∧
          ∀ y : ModGL τ (AlgebraicClosure K), (y ∈ D.torus ∧ y ^ p = 1) ↔
            ∃ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
              D.g0 = y

@[expose] def ExcFiveFourToral
    (K : Type) [Field K] : Prop :=
  Finite K → CharP K 2 → orderOf (Nat.card K : ZMod 5) = 4 →
    ∀ E : Subgroup (adjointGroup .E8 K), IsElemAbelian 5 E → 5 ^ 4 ≤ Nat.card E →
      ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ D : LangDatum .E8 (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) ∧
          D.q = Nat.card K ∧
          (∃ w : WeylGroup .E8, D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w ∧
            ExcLangShape .E8 4 w) ∧
          ∀ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
            D.g0 ∈ D.torus

section WeylSign

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix



private theorem ggA5a7_modMat_eq_smul_one {τ : Tag} {p : ℕ} (hp : p.Prime)
    (w : WeylGroup τ) {ε : ℤ}
    (h : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z}) :
    modMat p (weylMatrix w) = (ε : ZMod p) • 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z} = p ^ τ.rank := by
    refine le_antisymm ?_ h
    calc Nat.card {z : Fin τ.rank → ZMod p //
          (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z}
        ≤ Nat.card (Fin τ.rank → ZMod p) := Finite.card_subtype_le _
      _ = p ^ τ.rank := by rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hsub : Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z} =
      (Finset.univ.filter fun z : Fin τ.rank → ZMod p =>
        (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z).card :=
    Nat.subtype_card _ (by intro x; simp)
  have hS : (Finset.univ.filter fun z : Fin τ.rank → ZMod p =>
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z).card =
      Fintype.card (Fin τ.rank → ZMod p) := by
    rw [← hsub, hcard, ← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hall : ∀ z : Fin τ.rank → ZMod p,
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z := by
    intro z
    have hz : z ∈ Finset.univ.filter (fun z : Fin τ.rank → ZMod p =>
        (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z) := by
      rw [Finset.eq_univ_of_card _ hS]
      exact Finset.mem_univ z
    exact (Finset.mem_filter.mp hz).2
  ext i j
  have h1 := congrFun (hall (Pi.single i (1 : ZMod p))) j
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.transpose_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply] at h1
  rw [h1, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

private theorem ggA5a7_dvd_of_modMat_eq {τ : Tag} {p : ℕ} {w : WeylGroup τ} {ε : ℤ}
    (hε2 : ε * ε = 1)
    (hN : modMat p (weylMatrix w) = (ε : ZMod p) • 1) :
    ∀ i j, (p : ℤ) ∣ (((ε : ℤ) • weylMatrix w) - 1) i j := by
  intro i j
  have h1 : (((weylMatrix w) i j : ℤ) : ZMod p) =
      (ε : ZMod p) * (if i = j then 1 else 0) := by
    have h2 := congrFun (congrFun hN i) j
    simpa [modMat, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul] using h2
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hcast : ((ε * (weylMatrix w) i j - if i = j then (1 : ℤ) else 0 : ℤ) : ZMod p) =
      (ε : ZMod p) * (((weylMatrix w) i j : ℤ) : ZMod p) -
        (if i = j then (1 : ZMod p) else 0) := by
    split_ifs <;> simp
  rw [hcast, h1]
  have hε2' : (ε : ZMod p) * (ε : ZMod p) = 1 := by
    rw [← Int.cast_mul, hε2, Int.cast_one]
  rw [← mul_assoc, hε2', one_mul, sub_self]

private theorem ggA5a7_smul_weylMatrix_pow {τ : Tag} (w : WeylGroup τ) {ε : ℤ}
    (hε2 : ε * ε = 1) :
    (((ε : ℤ) • weylMatrix w) ^ (2 * orderOf w)) = 1 := by
  have hNk : (weylMatrix w) ^ orderOf w = 1 := by
    rw [← weylMatrix_pow, pow_orderOf_eq_one, weylMatrix_one]
  have hX2 : ((ε : ℤ) • weylMatrix w) ^ 2 = (weylMatrix w) ^ 2 := by
    rw [_root_.smul_pow, pow_two, hε2, one_smul]
  rw [pow_mul, hX2, ← pow_mul, mul_comm 2 (orderOf w), pow_mul, hNk, one_pow]



theorem weyl_eq_sign_of_eigenspace_top {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (w : WeylGroup τ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p (weylMatrix w))ᵀ *ᵥ z = (ε : ZMod p) • z}) :
    ∀ u : Fin τ.rank → ℤ, w • u = ε • u := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  haveI : Fact p.Prime := ⟨hp⟩
  have hN := ggA5a7_modMat_eq_smul_one hp w h
  have hX := ggA5a7_smul_weylMatrix_pow w hε2
  have hmod := ggA5a7_dvd_of_modMat_eq hε2 hN
  have hk : 2 * orderOf w ≠ 0 := by
    have := orderOf_pos w
    omega
  have hX1 := CFSG.StandardType.int_matrix_eq_one_of_pow_eq_one (p := p) hp2 hk hX hmod
  have hN_eq : weylMatrix w = (ε : ℤ) • 1 := by
    have hh := congrArg (fun M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ => (ε : ℤ) • M) hX1
    rw [smul_smul, hε2, one_smul] at hh
    simpa using hh
  intro u
  rw [← weylMatrix_mulVec w u, hN_eq, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem ggA5a7_excDegrees_pos {τ : Tag} : ∀ x ∈ excDegrees τ, 0 < x := by
  cases τ <;> decide

private theorem ggA5a7_excDegrees_le_thirty {τ : Tag} : ∀ x ∈ excDegrees τ, x ≤ 30 := by
  cases τ <;> decide

private theorem ggA5a7_countP_eq_zero_of_thirty_lt {d : ℕ} (hd : 30 < d) {τ : Tag} :
    (excDegrees τ).countP (fun x => d ∣ x) = 0 := by
  rw [List.countP_eq_zero]
  intro x hx hdvd
  have hdvd' : d ∣ x := of_decide_eq_true hdvd
  have hpos := ggA5a7_excDegrees_pos (τ := τ) x hx
  have hle := ggA5a7_excDegrees_le_thirty (τ := τ) x hx
  have := Nat.le_of_dvd hpos hdvd'
  omega

private theorem ggA5a7_countP_eq_zero_of_eq_zero {τ : Tag} :
    (excDegrees τ).countP (fun x => (0 : ℕ) ∣ x) = 0 := by
  rw [List.countP_eq_zero]
  intro x hx hdvd
  have hdvd' : (0 : ℕ) ∣ x := of_decide_eq_true hdvd
  rw [Nat.zero_dvd] at hdvd'
  have hpos := ggA5a7_excDegrees_pos (τ := τ) x hx
  omega



theorem excDegCount_ge_four {τ : Tag} {d : ℕ} (h : 4 ≤ excDegCount τ d) :
    ((τ = .E7 ∨ τ = .E8 ∨ τ = .F4) ∧ (d = 1 ∨ d = 2) ∧ excDegCount τ d = τ.rank) ∨
      (τ = .E8 ∧ (d = 3 ∨ d = 4 ∨ d = 6) ∧ excDegCount τ d = 4) := by
  have hd_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · subst hd0
      have hz : excDegCount τ 0 = 0 := ggA5a7_countP_eq_zero_of_eq_zero
      rw [hz] at h
      omega
    · exact hdpos
  have hd_le : d ≤ 30 := by
    by_contra hd
    have hd' : 30 < d := by omega
    have hz : excDegCount τ d = 0 := ggA5a7_countP_eq_zero_of_thirty_lt hd'
    rw [hz] at h
    omega
  interval_cases d <;> (cases τ <;> first | decide | exact absurd h (by decide))

end WeylSign

section ToralClosure

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar Polynomial
open scoped Matrix



private theorem ggA5a1_conj_of_map_eq
    {K : Type} [Field K] {τ : Tag}
    {A : Subgroup (ModGL τ K)} (hA : A ≤ adjointGroup τ K)
    {V : Subgroup (adjointGroup τ K)}
    (hV : ∀ {g : adjointGroup τ K}, g ∈ V → (g : ModGL τ K) ∈ torusGroup τ K)
    {g : adjointGroup τ K}
    (hg : (A.subgroupOf (adjointGroup τ K)).map (MulAut.conj g).toMonoidHom = V) :
    ∃ g' ∈ adjointGroup τ K, ∀ x ∈ A, g'⁻¹ * x * g' ∈ torusGroup τ K := by
  refine ⟨g⁻¹, inv_mem g.2, fun x hx => ?_⟩
  have hmem : (MulAut.conj g).toMonoidHom ⟨x, hA hx⟩ ∈
      (A.subgroupOf (adjointGroup τ K)).map (MulAut.conj g).toMonoidHom :=
    ⟨⟨x, hA hx⟩, hx, rfl⟩
  rw [hg] at hmem
  have h1 := hV hmem
  rw [inv_inv]
  simpa [MulAut.conj_apply] using h1

private theorem ggA5a1_finite
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (A : Subgroup (ModGL τ K)) (hA : A ≤ adjointGroup τ K)
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hpow : ∀ x ∈ A, x ^ p = 1)
    (hcard : p ^ τ.rank ≤ Nat.card A) :
    ∃ g ∈ adjointGroup τ K, ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ K := by
  have hE : CFSG.Open.IsElemAbelian p (A.subgroupOf (adjointGroup τ K)) :=
    ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext (hcomm _ a.2 _ b.2))⟩⟩,
      fun x hx => Subtype.ext ((Subgroup.coe_pow _ x p).trans (hpow _ hx))⟩
  have hEcard : Nat.card (A.subgroupOf (adjointGroup τ K)) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hcardE : p ^ τ.rank ≤ Nat.card (A.subgroupOf (adjointGroup τ K)) := by
    rw [hEcard]
    exact hcard
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨g, hg⟩ := (CFSG.StandardType.IOneRest.ggExcToralRankInput_E7E8 (Or.inl rfl) hp hp2
      hpq) (A.subgroupOf (adjointGroup .E7 K)) hE hcardE
    exact ggA5a1_conj_of_map_eq hA (fun h => (CFSG.StandardType.TableBExc.mem_torusPow.mp h).1) hg
  · obtain ⟨g, hg⟩ := (CFSG.StandardType.IOneRest.ggExcToralRankInput_E7E8 (Or.inr rfl) hp hp2
      hpq) (A.subgroupOf (adjointGroup .E8 K)) hE hcardE
    exact ggA5a1_conj_of_map_eq hA (fun h => (CFSG.StandardType.TableBExc.mem_torusPow.mp h).1) hg
  · by_cases hp3 : p = 3
    · subst hp3
      obtain ⟨g, hg⟩ := (CFSG.StandardType.TableBF4.ggF4ToralRankInput_three hpq)
        (A.subgroupOf (adjointGroup .F4 K)) hE hcardE
      exact ggA5a1_conj_of_map_eq hA (fun h => (CFSG.StandardType.TableBF4.mem_torusPow.mp h).1) hg
    · have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      obtain ⟨g, hg⟩ := (CFSG.StandardType.TableBF4.ggF4ToralRankInput_of_five_le hp hp5 hpq)
        (A.subgroupOf (adjointGroup .F4 K)) hE hcardE
      exact ggA5a1_conj_of_map_eq hA (fun h => (CFSG.StandardType.TableBF4.mem_torusPow.mp h).1) hg



theorem toral_over_closure_of_rank_le_card
    {τ : Tag}
    (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (A : Subgroup (ModGL τ (AlgebraicClosure K))) (hA : A ≤ adjointGroup τ (AlgebraicClosure K))
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hpow : ∀ x ∈ A, x ^ p = 1)
    (hcard : p ^ τ.rank ≤ Nat.card A) :
    ∃ g ∈ adjointGroup τ (AlgebraicClosure K),
      ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup τ (AlgebraicClosure K) := by
  haveI : Fact p.Prime := Fact.mk hp
  have hAfin : (A : Set (ModGL τ (AlgebraicClosure K))).Finite := by
    have : Finite A := Nat.finite_of_card_ne_zero
      (lt_of_lt_of_le (pow_pos hp.pos _) hcard).ne'
    exact Set.toFinite _
  obtain ⟨K₁, hK₁, -, hq, hdesc⟩ := exists_descent_subgroup (ℓ := 2) (r := p) hp2.symm
    (isAlgebraic_zmod_algebraicClosure_of_finite K 2) hA hAfin ∅ (le_refl 1)
  haveI : Finite K₁ := hK₁
  set ι := K₁.subtype
  have hA₁C : A.comap (baseChangeGL ι) ≤ adjointGroup τ K₁ := comap_le_adjointGroup ι hdesc
  have hcomm₁ : ∀ x ∈ A.comap (baseChangeGL ι), ∀ y ∈ A.comap (baseChangeGL ι),
      x * y = y * x := fun x hx y hy => baseChangeGL_injective ι (by
    rw [map_mul, map_mul]
    exact hcomm _ (Subgroup.mem_comap.mp hx) _ (Subgroup.mem_comap.mp hy))
  have hpow₁ : ∀ x ∈ A.comap (baseChangeGL ι), x ^ p = 1 := fun x hx =>
    baseChangeGL_injective ι (by rw [map_pow, map_one]; exact hpow _ (Subgroup.mem_comap.mp hx))
  have hcard₁ : Nat.card (A.comap (baseChangeGL ι)) = Nat.card A := by
    have hrange : A ≤ (baseChangeGL (τ := τ) ι).range := fun x hx => by
      obtain ⟨y, -, hy⟩ := hdesc x hx
      exact ⟨y, hy⟩
    conv_rhs => rw [← Subgroup.map_comap_eq_self hrange]
    exact (Subgroup.card_map_of_injective (baseChangeGL_injective ι)).symm
  have hq' : p ∣ Nat.card K₁ - 1 := by
    have h := (Nat.modEq_iff_dvd' Nat.card_pos).mp hq.symm
    simpa using h
  obtain ⟨g, hgC, hg⟩ := ggA5a1_finite (τ := τ) hτ hp hp2 K₁ hq'
    (A.comap (baseChangeGL ι)) hA₁C hcomm₁ hpow₁ (by rw [hcard₁]; exact hcard)
  have hH : torusGroup τ K₁ ≤ (torusGroup τ (AlgebraicClosure K)).comap (baseChangeGL ι) := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
    exact torusElt_mem_torusGroup i _
  refine ⟨baseChangeGL ι g, baseChangeGL_mem_adjointGroup ι hgC, fun x hx => ?_⟩
  obtain ⟨x₁, -, rfl⟩ := hdesc x hx
  rw [← map_inv, ← map_mul, ← map_mul]
  exact hH (hg x₁ hx)

end ToralClosure

section LangDatumOf

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups





theorem exists_langDatum_of_toral_conj
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (E : Subgroup (adjointGroup τ K)) (hE : ∀ x ∈ E, x ^ p = 1)
    {g : ModGL τ (AlgebraicClosure K)} (hg : g ∈ adjointGroup τ (AlgebraicClosure K))
    (hT : ∀ x ∈ E, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * g ∈
      torusGroup τ (AlgebraicClosure K)) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ D : LangDatum τ (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) ∧
        D.q = Nat.card K ∧
        (∃ w : WeylGroup τ, D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) ∧
        ∀ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          D.g0 ∈ D.torus := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have he : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hq : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have hp2cop : Nat.Coprime p 2 := by
    rw [hp.coprime_iff_not_dvd]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  have hpq : Nat.Coprime p (2 ^ (f : ℕ)) := hp2cop.pow_right f
  set ι : K →+* L := algebraMap K L with hι
  have htor : ∀ x : E, g⁻¹ * baseChangeGL ι (x : ModGL τ K) * g ∈ torusGroup τ L :=
    fun x => hT (x : adjointGroup τ K) x.2
  choose a ha using fun x : E => exists_rootDiagUnit_eq_of_mem_torusGroup (htor x)
  have hexp : ∀ (x : E) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ 1 := by
      have hmap : rootDiagUnit τ (a x ^ p) = rootDiagUnit τ (a x) ^ p :=
        (rootDiagUnitHom τ L).map_pow (a x) p
      rw [hmap, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * baseChangeGL ι (x : ModGL τ K) * g) ^ p
          = g⁻¹ * (baseChangeGL ι (x : ModGL τ K)) ^ p * g := by
            have hconj := conj_pow (a := g⁻¹) (b := baseChangeGL ι (x : ModGL τ K)) (i := p)
            rwa [inv_inv] at hconj
        _ = 1 := by
            rw [← map_pow]
            have hxp : (x : ModGL τ K) ^ p = 1 :=
              congrArg Subtype.val (hE (x : adjointGroup τ K) x.2)
            rw [hxp, map_one]
            group
    have h2 : a x ^ p = 1 := rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hFix : ∀ y : ModGL τ K,
      entrywiseFrobGL τ L 2 (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L 2 (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L 2 f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hn : ∀ x : E,
      (g⁻¹ * entrywiseFrobGL τ L 2 (f : ℕ) g) *
        entrywiseFrobGL τ L 2 (f : ℕ) (rootDiagUnit τ (a x)) *
        (g⁻¹ * entrywiseFrobGL τ L 2 (f : ℕ) g)⁻¹ = rootDiagUnit τ (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix (x : ModGL τ K)]
    group
  obtain ⟨w', z, hz, hlang⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.exists_lang_datum_of_plane 2 (f : ℕ) he hpq
      a hexp hg hn
  have hzC := CFSG.HardMathSupport.Timmesfeld.Torality.familyGroup_le_familyCentralizer
    (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ :=
    CFSG.HardMathSupport.Timmesfeld.Torality.mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL τ L 2 (f : ℕ) (g * z) =
      (g * z) * canonicalRep (coxeterSystem τ) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  let Fr : L →+* L := iterateFrobenius L 2 (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    change iterateFrobenius L 2 (f : ℕ) c = c ^ Nat.card K
    rw [iterateFrobenius_def, hq]
  have hmem : ∀ x ∈ E, (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z) ∈
      CFSG.RankThree.PartOne.KE.twistedTorusOf (canonicalRep (coxeterSystem τ) L w')
        (Units.map (entrywiseHom Fr)) := by
    intro x hx
    set xE : E := ⟨x, hx⟩ with hxE
    set d := rootDiagUnit τ (a xE) with hd
    have hzd : z⁻¹ * d * z = d := by
      have hcomm := hzcomm xE
      rw [← hd, mul_inv_eq_iff_eq_mul] at hcomm
      calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
        _ = z⁻¹ * (z * d) := by rw [hcomm]
        _ = d := by group
    have ht : (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z) = d := by
      calc (g * z)⁻¹ * baseChangeGL ι (x : ModGL τ K) * (g * z)
          = z⁻¹ * (g⁻¹ * baseChangeGL ι (x : ModGL τ K) * g) * z := by group
        _ = d := by rw [ha xE, hzd]
    rw [ht, CFSG.RankThree.PartOne.KE.mem_twistedTorusOf]
    refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    have hfx : entrywiseFrobGL τ L 2 (f : ℕ) (baseChangeGL ι (x : ModGL τ K)) =
        baseChangeGL ι (x : ModGL τ K) := hFix _
    have hFd : entrywiseFrobGL τ L 2 (f : ℕ) d =
        (canonicalRep (coxeterSystem τ) L w')⁻¹ * d * canonicalRep (coxeterSystem τ) L w' := by
      rw [← ht, map_mul, map_mul, map_inv, hfx, hu]
      group
    change canonicalRep (coxeterSystem τ) L w' * entrywiseFrobGL τ L 2 (f : ℕ) d *
      (canonicalRep (coxeterSystem τ) L w')⁻¹ = d
    rw [hFd]
    group
  let D : LangDatum τ L :=
    { Φ := Units.map (entrywiseHom Fr), q := Nat.card K,
      n := canonicalRep (coxeterSystem τ) L w', g0 := g * z,
      steinberg := ⟨Fr, hFr, 1, Or.inl rfl, fun g => by simp⟩,
      n_weyl := ⟨w', rfl⟩, g0_mem := mul_mem hg hzG, lang := hu }
  refine ⟨Fr, hFr, D, rfl, rfl, ⟨w', rfl⟩, ?_⟩
  exact hmem

end LangDatumOf

section TorsionCount

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial CFSG.RankThree.PartOne.KE
open scoped Matrix



private theorem ggA5a6_natCard_torsion_map {τ : Tag} {L : Type} [Field L]
    (T : Subgroup (Fin τ.rank → Lˣ)) (S : Subgroup (ModGL τ L))
    (hS : S = T.map (rootDiagUnitHom τ L)) (p : ℕ) :
    Nat.card {y : S // y ^ p = 1} =
      Nat.card {a : T // ∀ i, (a : Fin τ.rank → Lˣ) i ^ p = 1} := by
  subst hS
  have hinj : Function.Injective (rootDiagUnitHom τ L) := rootDiagUnit_injective
  have hpow : ∀ a : Fin τ.rank → Lˣ,
      (rootDiagUnitHom τ L a) ^ p = 1 ↔ ∀ i, a i ^ p = 1 := by
    intro a
    rw [← map_pow, ← map_one (rootDiagUnitHom τ L), hinj.eq_iff]
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun a : {a : T // ∀ i, (a : Fin τ.rank → Lˣ) i ^ p = 1} =>
      (⟨(⟨rootDiagUnitHom τ L a.1.1, ⟨a.1.1, a.1.2, rfl⟩⟩ :
            T.map (rootDiagUnitHom τ L)),
          Subtype.ext ((hpow a.1.1).2 a.2)⟩ :
        {y : T.map (rootDiagUnitHom τ L) // y ^ p = 1})) ⟨?_, ?_⟩)
  · intro a b h
    have h1 : (rootDiagUnitHom τ L a.1.1 : ModGL τ L) = rootDiagUnitHom τ L b.1.1 :=
      congrArg (fun z : {y : T.map (rootDiagUnitHom τ L) // y ^ p = 1} =>
        (z.1.1 : ModGL τ L)) h
    exact Subtype.ext (Subtype.ext (hinj h1))
  · rintro ⟨y, hy⟩
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.1 y.2
    refine ⟨⟨⟨a, ha⟩, (hpow a).1 ?_⟩, Subtype.ext (Subtype.ext hay)⟩
    rw [hay]
    simpa using congrArg Subtype.val hy



theorem card_torsion_langDatum_torus
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (D : LangDatum τ (AlgebraicClosure K)) (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hΦ : D.Φ = Units.map (entrywiseHom Fr))
    (w : WeylGroup τ) (hw : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    Nat.card {y : D.torus // y ^ p = 1} =
      Nat.card {z : Fin τ.rank → ZMod p //
        (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} := by
  let M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ := weylMatrix w
  have hM : ∀ u, w • u = M *ᵥ u := fun u => (weylMatrix_mulVec w u).symm
  have hT0 : twistedTorus (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) Fr =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ (AlgebraicClosure K)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hM Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hM Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a,
        mem_twistedFixedTuples_iff_conj.1 ha⟩
  have hD : D.torus =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ (AlgebraicClosure K)) := by
    show twistedTorusOf D.n D.Φ = _
    rw [hΦ, hw]
    exact hT0
  exact (ggA5a6_natCard_torsion_map (fixedCharTuples M Fr) D.torus hD p).trans
    (natCard_fixedTorsion M Fr Nat.prime_two hFr hp hp2)

end TorsionCount

section CharpolyCyclotomic

open Polynomial Matrix



private lemma ggA5q_d_pos {d : ℕ} (hdeg : (cyclotomic d ℚ).natDegree = 2) : 0 < d := by
  rw [natDegree_cyclotomic] at hdeg
  exact Nat.pos_of_ne_zero fun hd => by subst hd; simp at hdeg

private lemma ggA5q_aeval_mapMatrix {R S : Type*} [CommRing R] [CommRing S]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : R →+* S)
    (M : Matrix ι ι R) (p : R[X]) :
    aeval (M.map f) (p.map f) = (aeval M p).map f := by
  have key := Polynomial.map_aeval_eq_aeval_map
    (R := R) (S := Matrix ι ι R) (T := S) (U := Matrix ι ι S)
    (φ := f) (ψ := RingHom.mapMatrix f) ?_ p M
  · simpa [RingHom.mapMatrix_apply] using key.symm
  · ext r a b
    by_cases hab : a = b
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, hab]
    · simp [RingHom.mapMatrix_apply, Matrix.algebraMap_matrix_apply, hab]

private lemma ggA5q_minpoly_rat {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {d : ℕ}
    (hd : 0 < d) (M : Matrix ι ι ℤ) (h : aeval M (cyclotomic d ℤ) = 0) :
    minpoly ℚ (M.map (Int.castRingHom ℚ)) = cyclotomic d ℚ := by
  have hq : aeval (M.map (Int.castRingHom ℚ)) (cyclotomic d ℚ) = 0 := by
    have key := ggA5q_aeval_mapMatrix (Int.castRingHom ℚ) M (cyclotomic d ℤ)
    rw [Polynomial.map_cyclotomic] at key
    rw [key, h]
    simp
  exact (minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hd) hq
    (Polynomial.cyclotomic.monic d ℚ)).symm

private lemma ggA5q_charpoly_dvd_pow_rat {ι : Type*} [Fintype ι] [DecidableEq ι] {d m : ℕ}
    (hd : 0 < d) (hcard : Fintype.card ι = 2 * m)
    (Mq : Matrix ι ι ℚ) (hmin : minpoly ℚ Mq = cyclotomic d ℚ) :
    Mq.charpoly ∣ (cyclotomic d ℚ) ^ (2 * m) := by
  let Mc : Matrix ι ι ℂ := Mq.map (algebraMap ℚ ℂ)
  let gc : ℂ[X] := cyclotomic d ℂ
  have hgc : gc = (cyclotomic d ℚ).map (algebraMap ℚ ℂ) :=
    (Polynomial.map_cyclotomic d (algebraMap ℚ ℂ)).symm
  have hq0 : aeval Mq (cyclotomic d ℚ) = 0 := by
    rw [← hmin]
    exact minpoly.aeval ℚ Mq
  have hc0 : aeval Mc gc = 0 := by
    have key := ggA5q_aeval_mapMatrix (algebraMap ℚ ℂ) Mq (cyclotomic d ℚ)
    rw [hgc]
    rw [key, hq0]
    simp
  have hminc : minpoly ℂ Mc ∣ gc := minpoly.dvd ℂ Mc hc0
  have hroot : ∀ a, Mc.charpoly.IsRoot a → gc.IsRoot a := by
    intro a ha
    have hev : Module.End.HasEigenvalue (Matrix.toLin' Mc) a := by
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
      rwa [Matrix.charpoly_toLin']
    have hminroot : (minpoly ℂ (Matrix.toLin' Mc)).IsRoot a :=
      (Module.End.hasEigenvalue_iff_isRoot).mp hev
    rw [Matrix.minpoly_toLin'] at hminroot
    exact hminroot.dvd hminc
  have hf0 : Mc.charpoly ≠ 0 := (Matrix.charpoly_monic Mc).ne_zero
  have hg0 : gc ≠ 0 := (Polynomial.cyclotomic.monic d ℂ).ne_zero
  have hgp0 : gc ^ (2 * m) ≠ 0 := pow_ne_zero _ hg0
  have hle : Mc.charpoly.roots ≤ (gc ^ (2 * m)).roots := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Polynomial.roots_pow, Multiset.count_nsmul]
    by_cases ha : a ∈ gc.roots
    · have hpos : 0 < Multiset.count a gc.roots := Multiset.count_pos.mpr ha
      have hcard_le : Multiset.count a Mc.charpoly.roots ≤ 2 * m := by
        calc Multiset.count a Mc.charpoly.roots ≤ (Mc.charpoly.roots).card :=
              Multiset.count_le_card a _
          _ ≤ Mc.charpoly.natDegree := Polynomial.card_roots' _
          _ = Fintype.card ι := Matrix.charpoly_natDegree_eq_dim Mc
          _ = 2 * m := hcard
      calc Multiset.count a Mc.charpoly.roots ≤ 2 * m := hcard_le
        _ ≤ 2 * m * Multiset.count a gc.roots := Nat.le_mul_of_pos_right (2 * m) hpos
    · have hnotmem : a ∉ Mc.charpoly.roots := by
        intro hmem
        exact ha ((mem_roots hg0).mpr (hroot a ((mem_roots hf0).mp hmem)))
      rw [Multiset.count_eq_zero.mpr hnotmem, Multiset.count_eq_zero.mpr ha, Nat.mul_zero]
  have hdvdc : Mc.charpoly ∣ gc ^ (2 * m) :=
    (IsAlgClosed.dvd_iff_roots_le_roots hf0 hgp0).mpr hle
  have hmapf : Mc.charpoly = Mq.charpoly.map (algebraMap ℚ ℂ) :=
    Matrix.charpoly_map Mq (algebraMap ℚ ℂ)
  have hmapg : gc ^ (2 * m) = ((cyclotomic d ℚ) ^ (2 * m)).map (algebraMap ℚ ℂ) := by
    rw [hgc, Polynomial.map_pow]
  rw [hmapf, hmapg] at hdvdc
  exact (Polynomial.map_dvd_map' (algebraMap ℚ ℂ)).mp hdvdc

private lemma ggA5q_charpoly_eq_rat {ι : Type*} [Fintype ι] [DecidableEq ι] {d m : ℕ}
    (hdeg : (cyclotomic d ℚ).natDegree = 2) (hcard : Fintype.card ι = 2 * m)
    (Mq : Matrix ι ι ℚ) (hmin : minpoly ℚ Mq = cyclotomic d ℚ) :
    Mq.charpoly = (cyclotomic d ℚ) ^ m := by
  have hd := ggA5q_d_pos hdeg
  have hdiv := ggA5q_charpoly_dvd_pow_rat hd hcard Mq hmin
  have hprime : Prime (cyclotomic d ℚ) :=
    (Polynomial.cyclotomic.irreducible_rat hd).prime
  obtain ⟨i, _hi, hassoc⟩ := (dvd_prime_pow hprime (2 * m)).mp hdiv
  have heq : Mq.charpoly = (cyclotomic d ℚ) ^ i :=
    Polynomial.eq_of_monic_of_associated (Matrix.charpoly_monic Mq)
      ((Polynomial.cyclotomic.monic d ℚ).pow i) hassoc
  have hdegf : Mq.charpoly.natDegree = 2 * m := by
    rw [Matrix.charpoly_natDegree_eq_dim, hcard]
  have hdegi : ((cyclotomic d ℚ) ^ i).natDegree = 2 * i := by
    rw [Polynomial.natDegree_pow, hdeg, mul_comm]
  have him : i = m := by
    have h2 : 2 * m = 2 * i := by rw [← hdegf, heq, hdegi]
    omega
  rw [heq, him]

private theorem ggA5r1_charpoly_eq_cyclotomic_pow {ι : Type} [Fintype ι] [DecidableEq ι] {d m : ℕ}
    (hdeg : (cyclotomic d ℚ).natDegree = 2) (hcard : Fintype.card ι = 2 * m)
    (M : Matrix ι ι ℤ) (h : aeval M (cyclotomic d ℤ) = 0) :
    M.charpoly = (cyclotomic d ℤ) ^ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by simpa using hcard)
    simp [Matrix.charpoly_isEmpty]
  · haveI : Nonempty ι := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
    have hd := ggA5q_d_pos hdeg
    have hmin := ggA5q_minpoly_rat hd M h
    have hrat := ggA5q_charpoly_eq_rat hdeg hcard (M.map (Int.castRingHom ℚ)) hmin
    refine Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective ?_
    rw [← Matrix.charpoly_map M (Int.castRingHom ℚ), hrat, Polynomial.map_pow,
      Polynomial.map_cyclotomic]

end CharpolyCyclotomic

section RegularWeylE8

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix



private def ggA5r_S0 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![-1, 0, 1, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, -1, 0, 1, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     1, 0, -1, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 1, 1, -1, 1, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 1, -1, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S5 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 1, -1, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 1, -1, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_S7 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 1, -1]

private def ggA5r_S : Fin Tag.E8.rank → Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  ![ggA5r_S0, ggA5r_S1, ggA5r_S2, ggA5r_S3, ggA5r_S4, ggA5r_S5, ggA5r_S6, ggA5r_S7]

private lemma ggA5r_weylMatrix_simple (i : Fin Tag.E8.rank) :
    weylMatrix (simple .E8 i) = ggA5r_S i := by
  ext k j
  rw [weylMatrix_apply, simple_smul]
  fin_cases i <;> fin_cases k <;> fin_cases j <;> decide

private lemma ggA5r_weylMatrix_foldr (W : List (Fin Tag.E8.rank)) :
    weylMatrix ((coxeterSystem .E8).wordProd W) =
      W.foldr (fun i M => ggA5r_S i * M) 1 := by
  induction W with
  | nil => rw [CoxeterSystem.wordProd_nil, weylMatrix_one]; rfl
  | cons i W ih =>
    rw [CoxeterSystem.wordProd_cons, weylMatrix_mul, ggA5r_weylMatrix_simple, ih]
    rfl

private def ggA5r_c : WeylGroup .E8 :=
  (coxeterSystem .E8).wordProd [0, 1, 2, 3, 4, 5, 6, 7]

private def ggA5r_V1 : List (Fin Tag.E8.rank) :=
  [0, 3, 1, 2, 3, 4, 3, 1, 2, 3]

private def ggA5r_V2 : List (Fin Tag.E8.rank) :=
  [5, 4, 3, 1, 2, 0, 3, 2, 4, 6]

private def ggA5r_V3 : List (Fin Tag.E8.rank) :=
  [5, 4, 3, 1, 2, 0, 3, 2, 4, 3]

private def ggA5r_V4 : List (Fin Tag.E8.rank) :=
  [1, 5, 4, 3, 2, 0, 6, 5, 4, 7]

private def ggA5r_V5 : List (Fin Tag.E8.rank) :=
  [6, 5, 4, 3, 1, 2, 0, 3, 2, 4]

private def ggA5r_V6 : List (Fin Tag.E8.rank) :=
  [3, 1, 5, 4, 3, 2, 6, 5, 4, 7]

private def ggA5r_w4 : WeylGroup .E8 :=
  (coxeterSystem .E8).wordProd
    (ggA5r_V1 ++ ggA5r_V2 ++ ggA5r_V3 ++ ggA5r_V4 ++ ggA5r_V5 ++ ggA5r_V6)

private def ggA5r_w3 : WeylGroup .E8 := ggA5r_c ^ 10

private def ggA5r_w6 : WeylGroup .E8 := ggA5r_c ^ 5

private def ggA5r_Mc : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, 0, 0, 0, 0, 0, -1;
     0, 0, 1, 0, 0, 0, 0, -1;
     1, 1, 0, 0, 0, 0, 0, -1;
     0, 1, 1, 0, 0, 0, 0, -1;
     0, 0, 0, 1, 0, 0, 0, -1;
     0, 0, 0, 0, 1, 0, 0, -1;
     0, 0, 0, 0, 0, 1, 0, -1;
     0, 0, 0, 0, 0, 0, 1, -1]

private def ggA5r_D1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, 1, -1, 0, 1, 0, 0;
     1, 1, 0, -1, 0, 1, 0, 0;
     1, 0, 1, -1, 0, 1, 0, 0;
     2, 0, 0, -1, 0, 2, 0, 0;
     1, 0, 0, -1, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_D2 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, -1, 1, 0, 0, 0, 0;
     1, 0, -1, 1, -1, 1, 0, 0;
     0, 1, -1, 1, -1, 1, 0, 0;
     0, 0, -1, 2, -2, 2, 0, 0;
     0, 0, -1, 1, -1, 2, 0, 0;
     0, 0, -1, 1, -1, 2, -1, 1;
     0, 0, 0, 0, 0, 1, -1, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_D3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, 0, -1, 1, 0, 0, 0;
     1, 1, 0, -1, 0, 1, 0, 0;
     0, 2, 0, -1, 0, 1, 0, 0;
     0, 2, 1, -2, 0, 2, 0, 0;
     0, 1, 0, -1, 0, 2, 0, 0;
     0, 1, 0, -1, 0, 1, 1, 0;
     0, 0, 0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_D4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![-1, 0, 1, 0, 0, 0, 0, 0;
     -1, 0, 0, 1, -1, 1, 0, 0;
     -1, 0, 0, 1, 0, 0, 0, 0;
     -1, 1, 0, 1, -1, 1, 0, 0;
     -1, 1, 0, 1, -1, 0, 1, 0;
     -1, 1, 0, 1, -1, 0, 1, -1;
     0, 0, 0, 1, -1, 0, 1, -1;
     0, 0, 0, 0, 0, 0, 1, -1]

private def ggA5r_D5 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 0, -1, 1, 0, 0, 0, 0;
     1, 0, -1, 1, -1, 1, 0, 0;
     0, 1, -1, 1, -1, 1, 0, 0;
     0, 0, -1, 2, -2, 2, 0, 0;
     0, 0, -1, 1, -1, 2, 0, 0;
     0, 0, -1, 1, -1, 1, 1, 0;
     0, 0, -1, 1, -1, 1, 0, 1;
     0, 0, 0, 0, 0, 0, 0, 1]

private def ggA5r_D6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     1, 0, -1, 1, -1, 1, 0, 0;
     1, 0, -1, 1, 0, 0, 0, 0;
     2, 0, -2, 2, -1, 0, 1, 0;
     1, 1, -1, 1, -1, 0, 1, 0;
     1, 1, -1, 1, -1, 0, 1, -1;
     0, 0, 0, 1, -1, 0, 1, -1;
     0, 0, 0, 0, 0, 0, 1, -1]

private def ggA5r_M6 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![1, 1, 1, -1, 0, 0, -1, 0;
     1, 2, 1, -1, 0, -1, 0, -1;
     1, 2, 2, -1, -1, 0, -1, -1;
     2, 3, 2, -1, -1, -1, -1, -1;
     1, 2, 2, -1, 0, -1, -1, -1;
     1, 2, 1, -1, 0, 0, -1, -1;
     1, 1, 1, -1, 0, 0, 0, -1;
     0, 1, 1, -1, 0, 0, 0, 0]

private def ggA5r_M3 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![0, 1, 1, -1, 0, 0, -1, 0;
     1, 1, 1, -1, 0, -1, 0, -1;
     1, 2, 1, -1, -1, 0, -1, -1;
     2, 3, 2, -2, -1, -1, -1, -1;
     1, 2, 2, -1, -1, -1, -1, -1;
     1, 2, 1, -1, 0, -1, -1, -1;
     1, 1, 1, -1, 0, 0, -1, -1;
     0, 1, 1, -1, 0, 0, 0, -1]

private def ggA5r_M4 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ :=
  !![2, 0, -2, 1, -1, 1, 0, -1;
     3, 0, -3, 1, 0, 0, 1, -2;
     4, 0, -4, 2, -1, 1, 0, -2;
     6, 0, -6, 3, -1, 0, 1, -3;
     5, -1, -5, 3, -1, 0, 1, -2;
     3, -1, -4, 3, -1, 0, 1, -2;
     2, -1, -2, 2, -1, 0, 1, -2;
     1, 0, -1, 1, -1, 0, 1, -1]

private lemma ggA5r_c_matrix : weylMatrix ggA5r_c = ggA5r_Mc := by
  unfold ggA5r_c
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_w6_matrix : weylMatrix ggA5r_w6 = ggA5r_M6 := by
  unfold ggA5r_w6
  rw [weylMatrix_pow, ggA5r_c_matrix]
  decide

private lemma ggA5r_w3_matrix : weylMatrix ggA5r_w3 = ggA5r_M3 := by
  unfold ggA5r_w3
  rw [weylMatrix_pow, ggA5r_c_matrix]
  decide

private lemma ggA5r_V1_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggA5r_V1) = ggA5r_D1 := by
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_V2_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggA5r_V2) = ggA5r_D2 := by
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_V3_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggA5r_V3) = ggA5r_D3 := by
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_V4_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggA5r_V4) = ggA5r_D4 := by
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_V5_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggA5r_V5) = ggA5r_D5 := by
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_V6_matrix :
    weylMatrix ((coxeterSystem .E8).wordProd ggA5r_V6) = ggA5r_D6 := by
  rw [ggA5r_weylMatrix_foldr]
  decide

private lemma ggA5r_w4_matrix : weylMatrix ggA5r_w4 = ggA5r_M4 := by
  unfold ggA5r_w4
  simp only [CoxeterSystem.wordProd_append, weylMatrix_mul, ggA5r_V1_matrix, ggA5r_V2_matrix,
    ggA5r_V3_matrix, ggA5r_V4_matrix, ggA5r_V5_matrix, ggA5r_V6_matrix]
  decide

private lemma ggA5r_M6_quad : ggA5r_M6 ^ 2 - ggA5r_M6 + 1 = 0 := by
  decide

private lemma ggA5r_M3_quad : ggA5r_M3 ^ 2 + ggA5r_M3 + 1 = 0 := by
  decide

private lemma ggA5r_M4_quad : ggA5r_M4 ^ 2 + 1 = 0 := by
  decide

private lemma ggA5r_aeval_six : aeval (weylMatrix ggA5r_w6) (cyclotomic 6 ℤ) = 0 := by
  rw [ggA5r_w6_matrix, Polynomial.cyclotomic_six]
  simpa using ggA5r_M6_quad

private lemma ggA5r_aeval_three : aeval (weylMatrix ggA5r_w3) (cyclotomic 3 ℤ) = 0 := by
  rw [ggA5r_w3_matrix, Polynomial.cyclotomic_three]
  simpa using ggA5r_M3_quad

private lemma ggA5r_aeval_four : aeval (weylMatrix ggA5r_w4) (cyclotomic 4 ℤ) = 0 := by
  have hcyc : cyclotomic 4 ℤ = (X : ℤ[X]) ^ 2 + 1 := by
    rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num,
      Polynomial.cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two]
    simp only [Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one]
    ring
  rw [ggA5r_w4_matrix, hcyc]
  simpa [add_comm] using ggA5r_M4_quad

private lemma ggA5r_charpoly_six :
    (weylMatrix ggA5r_w6).charpoly = (cyclotomic 6 ℤ) ^ 4 := by
  refine ggA5r1_charpoly_eq_cyclotomic_pow (d := 6) (m := 4) (hdeg := ?_) (hcard := ?_)
    (M := weylMatrix ggA5r_w6) (h := ?_)
  · rw [Polynomial.natDegree_cyclotomic]; decide
  · decide
  · exact ggA5r_aeval_six

private lemma ggA5r_charpoly_three :
    (weylMatrix ggA5r_w3).charpoly = (cyclotomic 3 ℤ) ^ 4 := by
  refine ggA5r1_charpoly_eq_cyclotomic_pow (d := 3) (m := 4) (hdeg := ?_) (hcard := ?_)
    (M := weylMatrix ggA5r_w3) (h := ?_)
  · rw [Polynomial.natDegree_cyclotomic]; decide
  · decide
  · exact ggA5r_aeval_three

private lemma ggA5r_charpoly_four :
    (weylMatrix ggA5r_w4).charpoly = (cyclotomic 4 ℤ) ^ 4 := by
  refine ggA5r1_charpoly_eq_cyclotomic_pow (d := 4) (m := 4) (hdeg := ?_) (hcard := ?_)
    (M := weylMatrix ggA5r_w4) (h := ?_)
  · rw [Polynomial.natDegree_cyclotomic]; decide
  · decide
  · exact ggA5r_aeval_four

private lemma ggA5r_orderOf_eq_of_matrix {w : WeylGroup .E8} {d : ℕ} (hd : 0 < d)
    {M : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ} (hM : weylMatrix w = M)
    (hdec : M ^ d = 1) (hne : ∀ m, 0 < m → m < d → M ^ m ≠ 1) :
    orderOf w = d := by
  rw [orderOf_eq_iff hd]
  refine ⟨?_, ?_⟩
  · apply weylMatrix_injective
    rw [weylMatrix_pow, hM, hdec, weylMatrix_one]
  · intro m hm hpos hwm
    exact hne m hpos hm (by rw [← hM, ← weylMatrix_pow, hwm, weylMatrix_one])

private lemma ggA5r_order_six : orderOf ggA5r_w6 = 6 := by
  refine ggA5r_orderOf_eq_of_matrix (d := 6) (by norm_num) ggA5r_w6_matrix (by decide) ?_
  intro m h1 h2
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide

private lemma ggA5r_order_three : orderOf ggA5r_w3 = 3 := by
  refine ggA5r_orderOf_eq_of_matrix (d := 3) (by norm_num) ggA5r_w3_matrix (by decide) ?_
  intro m h1 h2
  have hm : m = 1 ∨ m = 2 := by omega
  rcases hm with rfl | rfl <;> decide

private lemma ggA5r_order_four : orderOf ggA5r_w4 = 4 := by
  refine ggA5r_orderOf_eq_of_matrix (d := 4) (by norm_num) ggA5r_w4_matrix (by decide) ?_
  intro m h1 h2
  have hm : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm with rfl | rfl | rfl <;> decide

private lemma ggA5r_shape_six : ExcLangShape .E8 6 ggA5r_w6 := by
  refine ⟨fun h => by omega, fun h => by omega, ?_⟩
  intro _
  exact ⟨ggA5r_order_six, weylMatrix ggA5r_w6, fun u => (weylMatrix_mulVec ggA5r_w6 u).symm,
    ggA5r_charpoly_six⟩

private lemma ggA5r_shape_three : ExcLangShape .E8 3 ggA5r_w3 := by
  refine ⟨fun h => by omega, fun h => by omega, ?_⟩
  intro _
  exact ⟨ggA5r_order_three, weylMatrix ggA5r_w3, fun u => (weylMatrix_mulVec ggA5r_w3 u).symm,
    ggA5r_charpoly_three⟩

private lemma ggA5r_shape_four : ExcLangShape .E8 4 ggA5r_w4 := by
  refine ⟨fun h => by omega, fun h => by omega, ?_⟩
  intro _
  exact ⟨ggA5r_order_four, weylMatrix ggA5r_w4, fun u => (weylMatrix_mulVec ggA5r_w4 u).symm,
    ggA5r_charpoly_four⟩



theorem exists_regular_weyl_E8 {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 6) :
    ∃ w : WeylGroup .E8, ExcLangShape .E8 d w := by
  rcases hd with rfl | rfl | rfl
  · exact ⟨ggA5r_w3, ggA5r_shape_three⟩
  · exact ⟨ggA5r_w4, ggA5r_shape_four⟩
  · exact ⟨ggA5r_w6, ggA5r_shape_six⟩

end RegularWeylE8

section EigenspaceBound

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix



private theorem ggA5a8_rootMultiplicity_pow {R : Type*} [CommRing R] [IsDomain R]
    (P : R[X]) (hP : P ≠ 0) (a : R) (m : ℕ) :
    (P ^ m).rootMultiplicity a = m * P.rootMultiplicity a := by
  induction m with
  | zero => simpa using Polynomial.rootMultiplicity_C (1 : R) a
  | succ n ih =>
      rw [pow_succ, Polynomial.rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hP) hP), ih,
        Nat.succ_mul]

private theorem ggA5a8_charpoly_modMat_transpose {τ : Tag} (p : ℕ)
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    ((modMat p M)ᵀ).charpoly = (M.charpoly).map (Int.castRingHom (ZMod p)) := by
  rw [Matrix.charpoly_transpose]
  simpa only [modMat] using Matrix.charpoly_map M (Int.castRingHom (ZMod p))

private theorem ggA5a8_cyclotomic_rootMultiplicity_le_one {p d q : ℕ} (hp : p.Prime)
    (hq : orderOf (q : ZMod p) = d) :
    (cyclotomic d (ZMod p)).rootMultiplicity (q : ZMod p) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne d 0 with rfl | hd
  · rw [Polynomial.cyclotomic_zero, ← Polynomial.C_1, Polynomial.rootMultiplicity_C]
    exact Nat.zero_le 1
  · have hd0 : 0 < d := Nat.pos_of_ne_zero hd
    have hpr : IsPrimitiveRoot (q : ZMod p) d := IsPrimitiveRoot.iff_orderOf.mpr hq
    have hq0 : (q : ZMod p) ≠ 0 := hpr.ne_zero hd
    have hdvd : d ∣ p - 1 := by
      rw [← hq]
      exact ZMod.orderOf_dvd_card_sub_one hq0
    have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
    have hpd : ¬ p ∣ d := by
      intro h
      have := Nat.le_of_dvd hd0 h
      have := Nat.le_of_dvd hp1 hdvd
      omega
    have hNe : NeZero (d : ZMod p) := ⟨fun h => hpd ((ZMod.natCast_eq_zero_iff d p).1 h)⟩
    haveI : NeZero (d : ZMod p) := hNe
    have hsep := Polynomial.separable_cyclotomic d (ZMod p)
    have hroot : IsRoot (cyclotomic d (ZMod p)) (q : ZMod p) :=
      Polynomial.isRoot_cyclotomic_iff.mpr hpr
    exact Polynomial.rootMultiplicity_le_one_of_separable hsep (q : ZMod p)

private theorem ggA5a8_finrank_eigenspace_le {K : Type*} [Field K] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) K} {d m : ℕ} {q : K}
    (hM : A.charpoly = (cyclotomic d K) ^ m)
    (hroot : (cyclotomic d K).rootMultiplicity q ≤ 1) :
    Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) q) ≤ m := by
  have hle : Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) q) ≤
      A.charpoly.rootMultiplicity q := by
    have h := LinearMap.finrank_eigenspace_le (Matrix.toLin' A) q
    rwa [Matrix.charpoly_toLin'] at h
  calc Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) q)
      ≤ A.charpoly.rootMultiplicity q := hle
    _ = ((cyclotomic d K) ^ m).rootMultiplicity q := by rw [hM]
    _ = m * (cyclotomic d K).rootMultiplicity q :=
        ggA5a8_rootMultiplicity_pow (cyclotomic d K) (Polynomial.cyclotomic.monic d K).ne_zero q m
    _ ≤ m * 1 := Nat.mul_le_mul_left m hroot
    _ = m := mul_one m

private theorem ggA5a8_natCard_eigenspace_le {K : Type*} [Field K] [Fintype K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (q : K) {m : ℕ}
    (h : Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) q) ≤ m) :
    Nat.card {z : Fin n → K // A *ᵥ z = q • z} ≤ Nat.card K ^ m := by
  haveI : FiniteDimensional K (Module.End.eigenspace (Matrix.toLin' A) q) :=
    FiniteDimensional.finiteDimensional_submodule _
  have hcard : Nat.card {z : Fin n → K // A *ᵥ z = q • z} =
      Nat.card (Module.End.eigenspace (Matrix.toLin' A) q) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun z => by
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply])
  have hcardpow : Nat.card (Module.End.eigenspace (Matrix.toLin' A) q) =
      Nat.card K ^ Module.finrank K (Module.End.eigenspace (Matrix.toLin' A) q) :=
    Module.natCard_eq_pow_finrank
  rw [hcard, hcardpow]
  exact Nat.pow_le_pow_right Nat.card_pos h



theorem card_eigenspace_le_of_charpoly {τ : Tag} {p : ℕ} (hp : p.Prime) {d m : ℕ}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : M.charpoly = (cyclotomic d ℤ) ^ m) {q : ℕ}
    (hq : orderOf (q : ZMod p) = d) :
    Nat.card {z : Fin τ.rank → ZMod p // (modMat p M)ᵀ *ᵥ z = (q : ZMod p) • z} ≤ p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hchar : ((modMat p M)ᵀ).charpoly = (cyclotomic d (ZMod p)) ^ m := by
    rw [ggA5a8_charpoly_modMat_transpose p M, hM, Polynomial.map_pow,
      Polynomial.map_cyclotomic_int]
  have hfin := ggA5a8_finrank_eigenspace_le (K := ZMod p) (A := (modMat p M)ᵀ)
    (q := (q : ZMod p)) hchar (ggA5a8_cyclotomic_rootMultiplicity_le_one hp hq)
  have hnat := ggA5a8_natCard_eigenspace_le (K := ZMod p) ((modMat p M)ᵀ) (q : ZMod p) hfin
  rwa [Nat.card_zmod] at hnat

end EigenspaceBound

section OrderE8

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix



private def ggA5a9_E8list : List ℕ := [30, 24, 20, 18, 14, 12, 8, 2]

private lemma ggA5a9_mem_E8list {x : ℕ} (hx : x ∈ ggA5a9_E8list) : x ≠ 0 := by
  simp only [ggA5a9_E8list, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

private lemma ggA5a9_ordE8_eq_prod (q : ℕ) :
    ordE8 q = q ^ 120 * (ggA5a9_E8list.map fun e => q ^ e - 1).prod := by
  simp only [ggA5a9_E8list, ordE8, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

private lemma ggA5a9_ordProj_list_prod (p : ℕ) (L : List ℕ) (hL : ∀ x ∈ L, x ≠ 0) :
    p ^ (L.prod).factorization p = (L.map fun x => p ^ x.factorization p).prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
      have ha : a ≠ 0 := hL a (by simp)
      have ht : ∀ x ∈ t, x ≠ 0 := fun x hx => hL x (by simp [hx])
      have htprod : t.prod ≠ 0 := List.prod_ne_zero fun h0 => ht 0 h0 rfl
      rw [List.prod_cons, List.map_cons, List.prod_cons,
        Nat.ordProj_mul p ha htprod, ih ht]

private lemma ggA5a9_not_dvd_ratio {p d m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : d = 3 ∨ d = 4 ∨ d = 6) (hpd : d ∣ p - 1)
    (hne : ¬ (d = 4 ∧ p = 5)) (hm : m ∣ 120) : ¬ p ∣ m := by
  intro hpm
  have hp120 : p ∣ 120 := dvd_trans hpm hm
  have hfac : (120 : ℕ) = 2 ^ 3 * 3 * 5 := by norm_num
  rw [hfac] at hp120
  rcases hp.dvd_mul.mp hp120 with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h2)
    · have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
      rw [h3] at hpd
      have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) hpd
      rcases hd with rfl | rfl | rfl <;> omega
  · have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h
    rw [h5] at hpd
    rcases hd with rfl | rfl | rfl
    · norm_num at hpd
    · exact hne ⟨rfl, h5⟩
    · norm_num at hpd

private lemma ggA5a9_div_dvd_120 {d x : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 6)
    (hx : x ∈ ggA5a9_E8list) (hdx : d ∣ x) : x / d ∣ 120 := by
  simp only [ggA5a9_E8list, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hd with rfl | rfl | rfl <;>
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (norm_num at hdx) <;> norm_num

private lemma ggA5a9_factorization_eq {p q d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : ¬ p ∣ q) (hq2 : 2 ≤ q) (he : orderOf (q : ZMod p) = d)
    (hd : d = 3 ∨ d = 4 ∨ d = 6) (hpd : d ∣ p - 1) (hne : ¬ (d = 4 ∧ p = 5)) :
    (ordE8 q).factorization p = 4 * (q ^ d - 1).factorization p := by
  have hD : ∀ x ∈ ggA5a9_E8list, d ∣ x → x ≠ 0 ∧ ¬ p ∣ x / d := by
    intro x hx hdx
    exact ⟨ggA5a9_mem_E8list hx,
      ggA5a9_not_dvd_ratio hp hp2 hd hpd hne (ggA5a9_div_dvd_120 hd hx hdx)⟩
  have hlen : (ggA5a9_E8list.filter fun x => decide (d ∣ x)).length = 4 := by
    rcases hd with rfl | rfl | rfl <;> decide
  have hnonzero : (ggA5a9_E8list.map fun e => q ^ e - 1).prod ≠ 0 :=
    List.prod_ne_zero fun h0 => by
      obtain ⟨e, he, hq0⟩ := List.mem_map.1 h0
      have he0 : e ≠ 0 := ggA5a9_mem_E8list he
      have hlt : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
      omega
  have hLpow : p ^ ((ordE8 q).factorization p) = p ^ (4 * (q ^ d - 1).factorization p) := by
    rw [ggA5a9_ordE8_eq_prod q]
    rw [Nat.ordProj_mul p (pow_ne_zero 120 (by omega)) hnonzero]
    rw [ordProj_eq_one_of_not_dvd' (fun h => hpq (hp.dvd_of_dvd_pow h)), one_mul]
    rw [ggA5a9_ordProj_list_prod p _ (fun x hx => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
      have he0 : e ≠ 0 := ggA5a9_mem_E8list he
      have hlt : 1 < q ^ e := Nat.one_lt_pow he0 (by omega)
      omega)]
    change (ggA5a9_E8list.map fun e => p ^ (q ^ e - 1).factorization p).prod =
      p ^ (4 * (q ^ d - 1).factorization p)
    rw [prod_ordProj_pow_sub_one hp hp2 hpq hq2 he ggA5a9_E8list hD, hlen]
    rw [← pow_mul, Nat.mul_comm]
  exact Nat.pow_right_injective hp.two_le hLpow



theorem factorization_card_adjointGroup_E8_le
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 6)
    (hq : orderOf (Nat.card K : ZMod p) = d) (hne : ¬ (d = 4 ∧ p = 5)) :
    (Nat.card (adjointGroup .E8 K)).factorization p ≤
      ((((cyclotomic d ℤ) ^ 4).eval (Nat.card K : ℤ)).natAbs).factorization p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype K := Fintype.ofFinite K
  set q : ℕ := Nat.card K with hqdef
  have hq' : orderOf (q : ZMod p) = d := by rw [hqdef]; exact hq
  have hq2 : 2 ≤ q := by
    rw [hqdef, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hq0 : q ≠ 0 := by omega
  have hd0 : d ≠ 0 := by rcases hd with rfl | rfl | rfl <;> norm_num
  have hpow : (q : ZMod p) ^ d = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hq']
  have hqne : (q : ZMod p) ≠ 0 := by
    intro h0
    have h1 : (1 : ZMod p) = 0 := by rw [← hpow, h0, zero_pow hd0]
    exact zero_ne_one h1.symm
  have hqp : ¬ p ∣ q := fun h => hqne ((ZMod.natCast_eq_zero_iff q p).2 h)
  have hpd : d ∣ p - 1 := hq' ▸ ZMod.orderOf_dvd_card_sub_one hqne
  have hcard : Nat.card (adjointGroup .E8 K) = ordE8 q := by
    rw [hqdef]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8
  have hR1 : ¬ (p : ℤ) ∣ (1 : ℤ[X]).eval (q : ℤ) := by
    intro h
    exact hp.not_dvd_one (Int.natCast_dvd.1 (by simpa using h))
  have hRpow : p ^ ((((cyclotomic d ℤ) ^ 4).eval (q : ℤ)).natAbs.factorization p)
      = p ^ (4 * (q ^ d - 1).factorization p) := by
    have hR := ordProj_cyclotomic_pow_mul_eval hp hq2 hq' hd0 (m := 4) (R := (1 : ℤ[X])) hR1
    rw [mul_one] at hR
    rw [hR, ← pow_mul, Nat.mul_comm]
  have hReq : ((((cyclotomic d ℤ) ^ 4).eval (q : ℤ)).natAbs).factorization p
      = 4 * (q ^ d - 1).factorization p := Nat.pow_right_injective hp.two_le hRpow
  rw [hcard, ggA5a9_factorization_eq hp hp2 hqp hq2 hq' hd hpd hne, hReq]

end OrderE8

section SylowFrameE8

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix



private theorem ggA5b1_weylMatrix_eq_of_mulVec {τ : Tag} {w : WeylGroup τ}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hM : ∀ u, w • u = M *ᵥ u) :
    M = weylMatrix w := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [← hM (Pi.single j 1), weylMatrix_mulVec]

private theorem ggA5b1_cyclotomic_eval_ne_zero {d q : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 6)
    (hq : q ≠ 1) : ((cyclotomic d ℤ) ^ 4).eval (q : ℤ) ≠ 0 := by
  rw [eval_pow]
  refine pow_ne_zero 4 fun h => ?_
  have hd1 : 1 < d := by rcases hd with rfl | rfl | rfl <;> norm_num
  have hlt := Polynomial.sub_one_lt_natAbs_cyclotomic_eval (n := d) (q := q) hd1 hq
  rw [h, Int.natAbs_zero] at hlt
  omega

private theorem ggA5b1_three_lt_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] [CharP K 2] {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 6)
    (hq : orderOf (Nat.card K : ZMod p) = d) : 3 < p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx0 : (Nat.card K : ZMod p) ≠ 0 := by
    intro hx
    have h0 : orderOf (Nat.card K : ZMod p) = 0 := by
      rw [hx, orderOf_eq_zero_iff']
      intro n hn h
      rw [zero_pow hn.ne'] at h
      exact zero_ne_one h
    rcases hd with rfl | rfl | rfl <;> omega
  have hdvd : d ∣ p - 1 := hq ▸ ZMod.orderOf_dvd_card_sub_one hx0
  have hp1 : 0 < p - 1 := by
    have := hp.two_le
    omega
  have hle : d ≤ p - 1 := Nat.le_of_dvd hp1 hdvd
  rcases hd with rfl | rfl | rfl <;> omega

private theorem ggA5b1_entrywiseHom_baseChangeGL_fixed
    {K L : Type} [Field K] [Finite K]
    [Field L] (ι : K →+* L) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) {τ : Tag}
    (y : ModGL τ K) :
    Units.map (entrywiseHom Fr) (baseChangeGL ι y) = baseChangeGL ι y := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hpow : ∀ c : K, c ^ Nat.card K = c := fun c => by
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hcomp : Fr.comp ι = ι := by
    ext c
    rw [RingHom.comp_apply, hFr, ← map_pow, hpow]
  rw [units_map_entrywiseHom_eq_baseChangeGL Fr (baseChangeGL ι y),
    baseChangeGL_baseChangeGL ι Fr y, hcomp]



theorem exists_langDatum_E8_regular_of_ne_five
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} (hd : d = 3 ∨ d = 4 ∨ d = 6)
    (hq : orderOf (Nat.card K : ZMod p) = d) (hne : ¬ (d = 4 ∧ p = 5))
    (E : Subgroup (adjointGroup .E8 K)) (hE : ∀ x ∈ E, x ^ p = 1) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ D : LangDatum .E8 (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) ∧
        D.q = Nat.card K ∧
        (∃ w : WeylGroup .E8, D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w ∧
          ExcLangShape .E8 d w) ∧
        ∀ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
          D.g0 ∈ D.torus := by
  classical
  obtain ⟨w, hshape⟩ := exists_regular_weyl_E8 hd
  obtain ⟨-, M, hM, hchar⟩ := hshape.2.2 ⟨rfl, hd⟩
  have hMweyl : M = weylMatrix w := ggA5b1_weylMatrix_eq_of_mulVec hM
  have hn0 : orderOf w ≠ 0 := (isOfFinOrder_of_finite w).orderOf_pos.ne'
  have hpow : M ^ orderOf w = 1 := by
    rw [hMweyl, ← weylMatrix_pow, pow_orderOf_eq_one, weylMatrix_one]
  have hqK : Nat.card K ≠ 1 := (Finite.one_lt_card (α := K)).ne'
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hchar]
    exact ggA5b1_cyclotomic_eval_ne_zero hd hqK
  have hord : (Nat.card (adjointGroup .E8 K)).factorization p ≤
      ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p := by
    rw [hchar]
    exact factorization_card_adjointGroup_E8_le hp hp2 hd hq hne
  have hp3 : 3 < p := ggA5b1_three_lt_p hp hp2 hd hq
  obtain ⟨Fr, hFr, g0, hg0C, hg0lang, hconj⟩ :=
    CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.exists_langFrame_untwisted_sylow
      (τ := .E8) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) K hp hp3
      (M := M) w hM hn0 hpow hev hord
  obtain ⟨c, hc⟩ := hconj E hE
  let Φ : ModGL .E8 (AlgebraicClosure K) →* ModGL .E8 (AlgebraicClosure K) :=
    Units.map (entrywiseHom Fr)
  let bc : ModGL .E8 (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL .E8 K)
  have hbcC : bc ∈ adjointGroup .E8 (AlgebraicClosure K) :=
    baseChangeGL_mem_adjointGroup (f := algebraMap K (AlgebraicClosure K)) c.2
  have hfix : Φ bc = bc :=
    ggA5b1_entrywiseHom_baseChangeGL_fixed (τ := .E8) (algebraMap K (AlgebraicClosure K)) Fr hFr
      (c : ModGL .E8 K)
  refine ⟨Fr, hFr,
    { Φ := Φ
      q := Nat.card K
      n := canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w
      g0 := bc⁻¹ * g0
      steinberg := ?_
      n_weyl := ⟨w, rfl⟩
      g0_mem := ?_
      lang := ?_ },
    rfl, rfl, ⟨w, rfl, hshape⟩, ?_⟩
  · refine ⟨Fr, hFr, 1, Or.inl rfl, fun g => ?_⟩
    simp [Φ]
  · exact mul_mem (inv_mem hbcC) hg0C
  · rw [map_mul, map_inv, hfix, hg0lang]
    group
  · intro x hx
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 (hc x hx)
    have hyeq' : g0 * y * g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((c * x * c⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) := by
      rw [← MulAut.conj_apply]
      exact hyeq
    have hbcx : bc * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * bc⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((c * x * c⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) := by
      show baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL .E8 K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL .E8 K))⁻¹ = _
      rw [← map_mul, ← map_inv, ← map_mul]
      congr 1
    have hgoal : (bc⁻¹ * g0)⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * (bc⁻¹ * g0) =
        y := by
      calc (bc⁻¹ * g0)⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) * (bc⁻¹ * g0)
          = g0⁻¹ * (bc * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
              bc⁻¹) * g0 := by group
        _ = g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) * g0 := by rw [hbcx]
        _ = y := by rw [← hyeq']; group
    rw [hgoal]
    exact hy

end SylowFrameE8

section Assembly

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6 CFSG.HardMathSupport.Timmesfeld.LangTorus
  Polynomial
open scoped Matrix



private theorem ggA5z0_torsion_finite
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (hp : p.Prime) (D : LangDatum τ (AlgebraicClosure K)) (w : WeylGroup τ)
    (hL6 : Nat.card {y : D.torus // y ^ p = 1} =
      Nat.card {z : Fin τ.rank → ZMod p //
        (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z}) :
    Finite {y : D.torus // y ^ p = 1} := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  apply Nat.finite_of_card_ne_zero
  rw [hL6]
  exact Nat.card_ne_zero.mpr ⟨⟨0, by simp⟩, inferInstance⟩

private theorem ggA5z0_range_torsion_eq
    {τ : Tag} {K : Type} [Field K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hpow : ∀ x ∈ E, x ^ p = 1)
    (D : LangDatum τ (AlgebraicClosure K))
    (hmem : ∀ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL τ K) * D.g0 ∈ D.torus)
    (hupper : Nat.card {y : D.torus // y ^ p = 1} ≤
      p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)))
    (hcard : p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ Nat.card E)
    (hfin : Finite {y : D.torus // y ^ p = 1}) :
    Nat.card {y : D.torus // y ^ p = 1} =
        p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) ∧
      (∀ y : ModGL τ (AlgebraicClosure K), (y ∈ D.torus ∧ y ^ p = 1) ↔
        ∃ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL τ K) * D.g0 = y) := by
  haveI : Finite {y : D.torus // y ^ p = 1} := hfin
  let f : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype)
  have hf : ∀ x : adjointGroup τ K, f x = D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 := by
    intro x
    simp [f, MulAut.conj_apply]
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) :=
      (MulAut.conj D.g0⁻¹).injective (by simpa [f] using hxy)
    exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h1)
  let T : Set (ModGL τ (AlgebraicClosure K)) := ↑(E.map f)
  let S : Set (ModGL τ (AlgebraicClosure K)) := {y | y ∈ D.torus ∧ y ^ p = 1}
  have hTS : T ⊆ S := by
    intro y hy
    change y ∈ E.map f at hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change f x ∈ D.torus ∧ (f x) ^ p = 1
    exact ⟨by rw [hf x]; exact hmem x hx, by rw [← map_pow, hpow x hx, map_one]⟩
  have hcardT : Nat.card T = Nat.card E := by
    change Nat.card (E.map f) = Nat.card E
    exact Subgroup.card_map_of_injective hf_inj
  let e : ↥S ≃ {y : D.torus // y ^ p = 1} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩, Subtype.ext (by simpa using y.2.2)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, by simpa using congrArg Subtype.val y.2⟩
      left_inv := fun y => by ext <;> rfl
      right_inv := fun y => by ext <;> rfl }
  have hScard : Nat.card S = Nat.card {y : D.torus // y ^ p = 1} := Nat.card_congr e
  haveI : Finite ↥S := Finite.of_equiv _ e.symm
  have hcardS_le : Nat.card S ≤ p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) := by
    rw [hScard]; exact hupper
  have hcardT_le : Nat.card T ≤ Nat.card S :=
    Nat.card_le_card_of_injective (fun y : ↥T => (⟨y.1, hTS y.2⟩ : ↥S))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥S => (z : ModGL τ (AlgebraicClosure K))) h))
  have hcardT_ge : p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) ≤ Nat.card T := by
    rw [hcardT]; exact hcard
  have hcardS_eq : Nat.card S = p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) :=
    le_antisymm hcardS_le (le_trans hcardT_ge hcardT_le)
  have hTS_eq : T = S :=
    Set.eq_of_subset_of_ncard_le hTS (by
      rw [← Nat.card_coe_set_eq S, ← Nat.card_coe_set_eq T]
      exact le_trans (le_of_eq hcardS_eq) hcardT_ge)
  refine ⟨hScard.symm.trans hcardS_eq, ?_⟩
  intro y
  change y ∈ S ↔ ∃ x ∈ E, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
    (x : ModGL τ K) * D.g0 = y
  rw [← hTS_eq]
  change y ∈ E.map f ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rw [hf x] at h; exact h⟩
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, by rw [hf x]; exact h⟩



private theorem adjointMaxElemToral_aux
    (τ : Tag) (K : Type) [Field K] (p : ℕ)
    (hB2 : p = 5 ∧ orderOf (Nat.card K : ZMod p) = 4 → ExcFiveFourToral K) :
    AdjointMaxElemToral τ K p := by
  intro hfin hchar hp hp2 hdeg E hE hcard
  haveI : Finite K := hfin
  haveI : CharP K 2 := hchar
  haveI : Fact p.Prime := ⟨hp⟩
  rcases excDegCount_ge_four (τ := τ) (d := orderOf (Nat.card K : ZMod p)) hdeg with
    ⟨hτ, hd, ha⟩ | ⟨hτE8, hd, ha⟩
  ·
    let fA : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
      (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup τ K).subtype
    let A : Subgroup (ModGL τ (AlgebraicClosure K)) := E.map fA
    have hfA_inj : Function.Injective fA := by
      intro x y h
      exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
        (by simpa [fA] using h))
    have hA_le : A ≤ adjointGroup τ (AlgebraicClosure K) := by
      intro x hx
      change x ∈ E.map fA at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, -, rfl⟩ := hx
      exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup
        (algebraMap K (AlgebraicClosure K)) a.2
    have hA_pow : ∀ x ∈ A, x ^ p = 1 := by
      intro x hx
      change x ∈ E.map fA at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      rw [← map_pow, hE.2 a ha, map_one]
    have hA_card : p ^ τ.rank ≤ Nat.card A := by
      have hc : Nat.card A = Nat.card E := by
        change Nat.card (E.map fA) = Nat.card E
        exact Subgroup.card_map_of_injective hfA_inj
      rw [hc, ← ha]; exact hcard
    have hA_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
      haveI hEcomm : IsMulCommutative ↥E := hE.1
      letI : CommMagma ↥E := IsMulCommutative.instCommMagma
      intro x hx y hy
      change x ∈ E.map fA at hx
      change y ∈ E.map fA at hy
      rw [Subgroup.mem_map] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have hab : a * b = b * a :=
        congrArg (fun z : ↥E => (z : adjointGroup τ K))
          (mul_comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)
      rw [← map_mul, ← map_mul, hab]
    obtain ⟨g, hg, hgA⟩ :=
      toral_over_closure_of_rank_le_card (K := K) hτ hp hp2 A hA_le hA_comm hA_pow hA_card
    have hT : ∀ x ∈ E, g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL τ K) * g ∈ torusGroup τ (AlgebraicClosure K) := by
      intro x hx
      have hxA : fA x ∈ A := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have := hgA (fA x) hxA
      simpa [fA] using this
    obtain ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw⟩, hmem⟩ :=
      exists_langDatum_of_toral_conj (τ := τ) hp hp2 E hE.2 hg hT
    have hL6 : Nat.card {y : D.torus // y ^ p = 1} =
        Nat.card {z : Fin τ.rank → ZMod p //
          (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} :=
      card_torsion_langDatum_torus (K := K) hp hp2 D Fr hFr hΦ w hw
    have hfinβ : Finite {y : D.torus // y ^ p = 1} := ggA5z0_torsion_finite hp D w hL6
    have hbound : Nat.card {y : D.torus // y ^ p = 1} ≤
        p ^ excDegCount τ (orderOf (Nat.card K : ZMod p)) := by
      rw [hL6, ha]
      exact le_trans (Finite.card_subtype_le _)
        (le_of_eq (by
          rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]))
    obtain ⟨hcardβ, hiff⟩ :=
      ggA5z0_range_torsion_eq (E := E) hE.2 D hmem hbound hcard hfinβ
    rcases hd with hd1 | hd2
    ·
      have hq1 : (Nat.card K : ZMod p) = 1 := orderOf_eq_one_iff.mp hd1
      have hL7hyp : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
          (modMat p (weylMatrix w))ᵀ *ᵥ z = ((1 : ℤ) : ZMod p) • z} := by
        have hγ : Nat.card {z : Fin τ.rank → ZMod p //
            (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} = p ^ τ.rank := by
          rw [← hL6, hcardβ, ha]
        have hqterm : (Nat.card K : ZMod p) = (((1 : ℤ) : ZMod p)) := by
          rw [hq1]; ring
        have hset : Nat.card {z : Fin τ.rank → ZMod p //
            (modMat p (weylMatrix w))ᵀ *ᵥ z = ((1 : ℤ) : ZMod p) • z} =
            Nat.card {z : Fin τ.rank → ZMod p //
              (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun z => by rw [hqterm]))
        rw [hset, ← hγ]
      have hL7 := weyl_eq_sign_of_eigenspace_top (τ := τ) hp hp2 w (ε := 1)
        (Or.inl rfl) hL7hyp
      have hw1 : w = 1 := by
        refine FaithfulSMul.eq_of_smul_eq_smul (M := WeylGroup τ) (α := Fin τ.rank → ℤ)
          fun u => ?_
        calc w • u = (1 : ℤ) • u := hL7 u
          _ = u := one_smul ℤ u
          _ = (1 : WeylGroup τ) • u := (one_smul (WeylGroup τ) u).symm
      have hshape : ExcLangShape τ (orderOf (Nat.card K : ZMod p)) w := by
        rw [hd1]
        exact ⟨fun _ => hw1, fun h => absurd h (by omega), fun h => absurd h.2 (by omega)⟩
      exact ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, hshape⟩, hmem, hiff⟩
    ·
      have hq2 : (Nat.card K : ZMod p) = -1 := by
        have h2 : (Nat.card K : ZMod p) ^ 2 = 1 := by
          have := pow_orderOf_eq_one (Nat.card K : ZMod p)
          rwa [hd2] at this
        have hne : (Nat.card K : ZMod p) ≠ 1 := by
          intro h
          rw [h] at hd2
          simp at hd2
        rcases sq_eq_one_iff.mp h2 with h | h
        · exact absurd h hne
        · exact h
      have hL7hyp : p ^ τ.rank ≤ Nat.card {z : Fin τ.rank → ZMod p //
          (modMat p (weylMatrix w))ᵀ *ᵥ z = ((-1 : ℤ) : ZMod p) • z} := by
        have hγ : Nat.card {z : Fin τ.rank → ZMod p //
            (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} = p ^ τ.rank := by
          rw [← hL6, hcardβ, ha]
        have hqterm : (Nat.card K : ZMod p) = (((-1 : ℤ) : ZMod p)) := by
          rw [hq2]
          simp only [Int.cast_neg, Int.cast_one, neg_inj]
          rfl
        have hset : Nat.card {z : Fin τ.rank → ZMod p //
            (modMat p (weylMatrix w))ᵀ *ᵥ z = ((-1 : ℤ) : ZMod p) • z} =
            Nat.card {z : Fin τ.rank → ZMod p //
              (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} :=
          Nat.card_congr (Equiv.subtypeEquivRight (fun z => by rw [hqterm]))
        rw [hset, ← hγ]
      have hL7 := weyl_eq_sign_of_eigenspace_top (τ := τ) hp hp2 w (ε := -1)
        (Or.inr rfl) hL7hyp
      have hneg : ∀ u : Fin τ.rank → ℤ, w • u = -u := fun u => by simpa using hL7 u
      have hshape : ExcLangShape τ (orderOf (Nat.card K : ZMod p)) w := by
        rw [hd2]
        exact ⟨fun h => absurd h (by omega), fun _ => hneg, fun h => absurd h.2 (by omega)⟩
      exact ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, hshape⟩, hmem, hiff⟩
  ·
    subst hτE8
    by_cases h45 : p = 5 ∧ orderOf (Nat.card K : ZMod p) = 4
    ·
      have hB2' := hB2 h45
      obtain ⟨hp5, hd4⟩ := h45
      subst hp5
      have hq5 : orderOf (Nat.card K : ZMod 5) = 4 := hd4
      have hE5 : IsElemAbelian 5 E := hE
      have ha5 : excDegCount .E8 (orderOf (Nat.card K : ZMod 5)) = 4 := ha
      have hcard5 : 5 ^ 4 ≤ Nat.card E := by
        have h := hcard
        rw [ha5] at h
        exact h
      obtain ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, hshape⟩, hmem⟩ :=
        hB2' hfin hchar hq5 E hE5 hcard5
      have hL6 : Nat.card {y : D.torus // y ^ 5 = 1} =
          Nat.card {z : Fin (Tag.E8).rank → ZMod 5 //
            (modMat 5 (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod 5) • z} :=
        card_torsion_langDatum_torus (K := K) hp hp2 D Fr hFr hΦ w hw
      have hfinβ : Finite {y : D.torus // y ^ 5 = 1} := ggA5z0_torsion_finite hp D w hL6
      obtain ⟨-, M, hMsmul, hMchar⟩ := hshape.2.2 ⟨rfl, Or.inr (Or.inl rfl)⟩
      have hMw : weylMatrix w = M := by
        apply Matrix.ext
        intro i j
        have h := hMsmul (Pi.single j 1)
        rw [← weylMatrix_mulVec] at h
        rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
        exact congrFun h i
      have hMchar' : (weylMatrix w).charpoly =
          (cyclotomic (orderOf (Nat.card K : ZMod 5)) ℤ) ^ 4 := by
        rw [hMw, hd4]; exact hMchar
      have hbound : Nat.card {y : D.torus // y ^ 5 = 1} ≤
          5 ^ excDegCount .E8 (orderOf (Nat.card K : ZMod 5)) := by
        rw [hL6, ha]
        exact card_eigenspace_le_of_charpoly (τ := .E8) (q := Nat.card K) hp hMchar' rfl
      obtain ⟨-, hiff⟩ :=
        ggA5z0_range_torsion_eq (E := E) hE.2 D hmem hbound hcard hfinβ
      refine ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, ?_⟩, hmem, hiff⟩
      rw [hd4]; exact hshape
    ·
      have hne' : ¬ (orderOf (Nat.card K : ZMod p) = 4 ∧ p = 5) := by
        rintro ⟨hd4, hp5⟩
        exact h45 ⟨hp5, hd4⟩
      obtain ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, hshape⟩, hmem⟩ :=
        exists_langDatum_E8_regular_of_ne_five (K := K) hp hp2 hd rfl hne' E hE.2
      have hL6 : Nat.card {y : D.torus // y ^ p = 1} =
          Nat.card {z : Fin (Tag.E8).rank → ZMod p //
            (modMat p (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod p) • z} :=
        card_torsion_langDatum_torus (K := K) hp hp2 D Fr hFr hΦ w hw
      have hfinβ : Finite {y : D.torus // y ^ p = 1} := ggA5z0_torsion_finite hp D w hL6
      obtain ⟨-, M, hMsmul, hMchar⟩ := hshape.2.2 ⟨rfl, hd⟩
      have hMw : weylMatrix w = M := by
        apply Matrix.ext
        intro i j
        have h := hMsmul (Pi.single j 1)
        rw [← weylMatrix_mulVec] at h
        rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
        exact congrFun h i
      have hMchar' : (weylMatrix w).charpoly =
          (cyclotomic (orderOf (Nat.card K : ZMod p)) ℤ) ^ 4 := by
        rw [hMw]; exact hMchar
      have hbound : Nat.card {y : D.torus // y ^ p = 1} ≤
          p ^ excDegCount .E8 (orderOf (Nat.card K : ZMod p)) := by
        rw [hL6, ha]
        exact card_eigenspace_le_of_charpoly (τ := .E8) (q := Nat.card K) hp hMchar' rfl
      obtain ⟨-, hiff⟩ :=
        ggA5z0_range_torsion_eq (E := E) hE.2 D hmem hbound hcard hfinβ
      exact ⟨Fr, hFr, D, hΦ, hqK, ⟨w, hw, hshape⟩, hmem, hiff⟩

end Assembly

theorem adjointMaxElemToral_of_fiveFourToral
    (τ : Tag) (K : Type) [Field K] (p : ℕ)
    (h : ExcFiveFourToral K) : AdjointMaxElemToral τ K p :=
  adjointMaxElemToral_aux τ K p fun _ => h

theorem adjointMaxElemToral_of_not_five_four
    (τ : Tag) (K : Type) [Field K] (p : ℕ)
    (hne : ¬ (p = 5 ∧ orderOf (Nat.card K : ZMod p) = 4)) : AdjointMaxElemToral τ K p :=
  adjointMaxElemToral_aux τ K p fun h => absurd h hne

section E8Three

open CFSG.LieType.SeitzGeneration CFSG.RankThree.E6

private theorem ggA5e8_three_eigenspace_card
    {q : ℕ} (w : WeylGroup .E8)
    (hord : orderOf (q : ZMod 3) = 1 ∨ orderOf (q : ZMod 3) = 2)
    (hshape : ExcLangShape .E8 (orderOf (q : ZMod 3)) w) :
    Nat.card {z : Fin Tag.E8.rank → ZMod 3 //
      (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (q : ZMod 3) • z} = 3 ^ 8 := by
  rcases hord with h1 | h2
  · have hq1 : (q : ZMod 3) = 1 := orderOf_eq_one_iff.mp h1
    have hw1 : w = 1 := hshape.1 h1
    have hmat : modMat 3 (weylMatrix w) = 1 := by
      rw [hw1, weylMatrix_one]
      simp [modMat]
    have hfull : ∀ z : Fin Tag.E8.rank → ZMod 3,
        (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (q : ZMod 3) • z := by
      intro z
      rw [hmat, hq1]
      simp
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hfull), Nat.card_fun, Nat.card_fin,
      Nat.card_zmod]
    norm_num [Tag.rank]
  · have hqneg : (q : ZMod 3) = -1 := by
      have hq2 : (q : ZMod 3) ^ 2 = 1 := by
        simpa [h2] using pow_orderOf_eq_one (q : ZMod 3)
      have hne : (q : ZMod 3) ≠ 1 := by
        intro hq1
        rw [orderOf_eq_one_iff.mpr hq1] at h2
        omega
      rcases sq_eq_one_iff.mp hq2 with h | h
      · exact absurd h hne
      · exact h
    have hwneg : ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u := hshape.2.1 h2
    have hmat : modMat 3 (weylMatrix w) = -1 := by
      have hweyl : weylMatrix w = -1 := by
        ext i j
        have h := congrFun (hwneg (Pi.single j 1)) i
        rw [← weylMatrix_mulVec, Matrix.mulVec_single_one] at h
        simpa [Matrix.neg_apply, Matrix.one_apply, Pi.neg_apply, Pi.single_apply] using h
      rw [hweyl, modMat]
      ext i j
      simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
      split_ifs <;> rfl
    have hfull : ∀ z : Fin Tag.E8.rank → ZMod 3,
        (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (q : ZMod 3) • z := by
      intro z
      rw [hmat, hqneg, Matrix.transpose_neg, Matrix.transpose_one]
      calc
        (-(1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) (ZMod 3))) *ᵥ z
            = -(1 *ᵥ z) := Matrix.neg_mulVec z 1
        _ = -z := by rw [Matrix.one_mulVec]
        _ = (-1 : ZMod 3) • z := by
          ext i
          simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
          exact (neg_one_mul (z i)).symm
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hfull), Nat.card_fun, Nat.card_fin,
      Nat.card_zmod]
    norm_num [Tag.rank]

theorem adjointMaxElemToral_E8_three
    (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (hK : Nat.card K = 2 ^ n)
    (A : Subgroup (adjointGroup .E8 K))
    (hA : IsElemAbelian 3 A) (hcard : 3 ^ 8 ≤ Nat.card A) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ D : LangDatum .E8 (AlgebraicClosure K), D.Φ = Units.map (entrywiseHom Fr) ∧
        D.q = Nat.card K ∧
        (∃ w : WeylGroup .E8, D.n = canonicalRep (coxeterSystem .E8) (AlgebraicClosure K) w ∧
          ExcLangShape .E8 (orderOf (Nat.card K : ZMod 3)) w ∧
          (3 ∣ 2 ^ n - 1 → w = 1) ∧
          (3 ∣ 2 ^ n + 1 → ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u)) ∧
        (∀ x ∈ A, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
          D.g0 ∈ D.torus) ∧
        (∀ y : ModGL .E8 (AlgebraicClosure K), (y ∈ D.torus ∧ y ^ 3 = 1) ↔
          ∃ x ∈ A, D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
            D.g0 = y) ∧
        Nat.card A = 3 ^ 8 := by
  classical
  have hq0 : (Nat.card K : ZMod 3) ≠ 0 := by
    intro h0
    have h3 : 3 ∣ Nat.card K := (ZMod.natCast_eq_zero_iff (Nat.card K) 3).mp h0
    rw [hK] at h3
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hdvd : orderOf (Nat.card K : ZMod 3) ∣ 2 := by
    have h := ZMod.orderOf_dvd_card_sub_one hq0
    norm_num at h
    exact h
  have hd : orderOf (Nat.card K : ZMod 3) = 1 ∨
      orderOf (Nat.card K : ZMod 3) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hcount : excDegCount .E8 (orderOf (Nat.card K : ZMod 3)) = 8 := by
    rcases hd with h | h <;> rw [h] <;> decide
  have hne : ¬ (3 = 5 ∧ orderOf (Nat.card K : ZMod 3) = 4) := by
    rintro ⟨h5, -⟩
    norm_num at h5
  have hdeg : 4 ≤ excDegCount .E8 (orderOf (Nat.card K : ZMod 3)) := by
    rw [hcount]
    norm_num
  have hcardE : 3 ^ excDegCount .E8 (orderOf (Nat.card K : ZMod 3)) ≤ Nat.card A := by
    rw [hcount]
    exact hcard
  obtain ⟨Fr, hFr, D, hΦ, hqD, ⟨w, hw, hshape⟩, hmem, hiff⟩ :=
    (adjointMaxElemToral_of_not_five_four (τ := .E8) (K := K) (p := 3) hne)
      inferInstance inferInstance (by norm_num) (by norm_num) hdeg A hA hcardE
  have hL6 := card_torsion_langDatum_torus (K := K) (p := 3) (by norm_num) (by norm_num)
    D Fr hFr hΦ w hw
  have hcardβ : Nat.card {z : Fin Tag.E8.rank → ZMod 3 //
      (modMat 3 (weylMatrix w))ᵀ *ᵥ z = (Nat.card K : ZMod 3) • z} = 3 ^ 8 :=
    ggA5e8_three_eigenspace_card (q := Nat.card K) w hd hshape
  have hcard_torsion : Nat.card {y : D.torus // y ^ 3 = 1} = 3 ^ 8 := by
    rw [hL6, hcardβ]
  have hsign1 : 3 ∣ 2 ^ n - 1 → w = 1 := by
    intro hdiv
    have hq1 : (Nat.card K : ZMod 3) = 1 := by
      have hmod : (1 : ℕ) ≡ Nat.card K [MOD 3] := by
        rw [Nat.modEq_iff_dvd' (by rw [hK]; exact Nat.one_le_two_pow)]
        rw [hK]
        exact hdiv
      exact ((ZMod.natCast_eq_natCast_iff 1 (Nat.card K) 3).mpr hmod).symm
    have hd1 : orderOf (Nat.card K : ZMod 3) = 1 := orderOf_eq_one_iff.mpr hq1
    exact hshape.1 hd1
  have hsign2 : 3 ∣ 2 ^ n + 1 → ∀ u : Fin Tag.E8.rank → ℤ, w • u = -u := by
    intro hdiv
    have hqneg : (Nat.card K : ZMod 3) = -1 := by
      have hzero : ((Nat.card K + 1 : ℕ) : ZMod 3) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        rw [hK]
        exact hdiv
      have h' : (Nat.card K : ZMod 3) + 1 = 0 := by simpa using hzero
      exact eq_neg_of_add_eq_zero_left h'
    have hd2 : orderOf (Nat.card K : ZMod 3) = 2 := by
      rw [hqneg]
      exact orderOf_eq_prime (p := 2) (by decide) (by decide)
    exact hshape.2.1 hd2
  let f : adjointGroup .E8 K →* ModGL .E8 (AlgebraicClosure K) :=
    (MulAut.conj D.g0⁻¹).toMonoidHom.comp
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp (adjointGroup .E8 K).subtype)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E8 K) :=
      (MulAut.conj D.g0⁻¹).injective (by simpa [f] using hxy)
    exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h1)
  have hf_apply : ∀ x : adjointGroup .E8 K,
      f x = D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E8 K) *
        D.g0 := by
    intro x
    simp [f, MulAut.conj_apply]
  have hset : (A.map f : Set (ModGL .E8 (AlgebraicClosure K))) =
      {y : ModGL .E8 (AlgebraicClosure K) | y ∈ D.torus ∧ y ^ 3 = 1} := by
    ext y
    change y ∈ A.map f ↔ y ∈ {y : ModGL .E8 (AlgebraicClosure K) | y ∈ D.torus ∧ y ^ 3 = 1}
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hiff (f x)).mpr ⟨x, hx, (hf_apply x).symm⟩
    · intro hy
      obtain ⟨x, hx, hxy⟩ := (hiff y).mp hy
      exact ⟨x, hx, by rw [hf_apply x]; exact hxy⟩
  let e : {y : ModGL .E8 (AlgebraicClosure K) // y ∈ D.torus ∧ y ^ 3 = 1} ≃
      {y : D.torus // y ^ 3 = 1} :=
    { toFun := fun y => ⟨⟨y.1, y.2.1⟩,
        Subtype.ext (by
          change (y.1 : ModGL .E8 (AlgebraicClosure K)) ^ 3 =
            (1 : ModGL .E8 (AlgebraicClosure K))
          simpa using y.2.2)⟩
      invFun := fun y => ⟨y.1.1, y.1.2, by
        simpa using congrArg Subtype.val y.2⟩
      left_inv := by intro y; ext <;> rfl
      right_inv := by intro y; ext <;> rfl }
  have hcardA : Nat.card A = 3 ^ 8 := by
    calc
      Nat.card A = Nat.card (A.map f) :=
        (Subgroup.card_map_of_injective hf_inj).symm
      _ = (A.map f : Set (ModGL .E8 (AlgebraicClosure K))).ncard :=
        Nat.card_coe_set_eq _
      _ = ({y : ModGL .E8 (AlgebraicClosure K) | y ∈ D.torus ∧ y ^ 3 = 1} :
            Set (ModGL .E8 (AlgebraicClosure K))).ncard := by rw [hset]
      _ = Nat.card {y : ModGL .E8 (AlgebraicClosure K) // y ∈ D.torus ∧ y ^ 3 = 1} :=
        (Nat.card_coe_set_eq _).symm
      _ = Nat.card {y : D.torus // y ^ 3 = 1} := Nat.card_congr e
      _ = 3 ^ 8 := hcard_torsion
  exact ⟨Fr, hFr, D, hΦ, hqD, ⟨w, hw, hshape, hsign1, hsign2⟩, hmem, hiff, hcardA⟩

end E8Three

end CFSG.StandardType.ExcMaxToral
