module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpCompPair
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockRank
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpDecomp
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagBlocks
public import CFSG.LocalAnalysis.StandardType.GGClassicalBlockSpIsoOneLinear
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
public import CFSG.LocalAnalysis.StandardType.GGCentInnerDiagLinear
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommSpRes
public import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpGen
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockSympHas

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp StatedSL)
open CFSG.Assembly
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped commutatorElement

private lemma orderOf_diagSp_dvd {K : Type} [Field K] [Finite K] {m : ℕ} (t : Fin m → Kˣ) :
    orderOf (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K)) ∣ Nat.card K - 1 := by
  classical
  have hmat : (((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = Matrix.diagonal (diagSpEntry t) := by
    simpa [mat] using mat_diagSp t
  rw [orderOf_dvd_iff_pow_eq_one]; apply Units.ext
  ext a b; rw [Units.val_pow_eq_pow_val, Units.val_one, hmat, Matrix.diagonal_pow,
    Matrix.diagonal_apply, Matrix.one_apply]
  let F : Fintype K := Fintype.ofFinite K
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_pos rfl, @Nat.card_eq_fintype_card K F]
    exact @FiniteField.pow_card_sub_one_eq_one K _ F (diagSpEntry t a) (by
      rcases a with i | i <;> simp)
  · simp [hab]

private lemma odd_orderOf_diagSp {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (t : Fin m → Kˣ) : Odd (orderOf (((diagSp K m t : StatedSp m K) :
      GL (Fin m ⊕ Fin m) K))) := by
  let F : Fintype K := Fintype.ofFinite K
  have hcard : Even (Nat.card K) := by
    obtain ⟨n, -, hn⟩ := @FiniteField.card K _ F 2 (inferInstance : CharP K 2)
    rw [@Nat.card_eq_fintype_card K F, hn]
    refine Nat.even_pow.mpr ⟨by norm_num, ?_⟩; intro h0
    have h1 : 1 < @Fintype.card K F := @Fintype.one_lt_card K F _
    rw [h0] at hn; simp at hn; omega
  have h1 : 1 ≤ Nat.card K := Nat.succ_le_of_lt (Nat.card_pos (α := K))
  exact Odd.of_dvd_nat (Nat.Even.sub_odd h1 hcard odd_one)
    (orderOf_diagSp_dvd t)

lemma finrank_diagonal_eq_card {K : Type} [Field K] [DecidableEq K] {m : ℕ}
    (v : Fin m ⊕ Fin m → K) (hv : ∀ a, v a = 0 ∨ v a = 1) :
    Module.finrank K (LinearMap.range (Matrix.toLin' (Matrix.diagonal v))) =
      Fintype.card {a // v a = 1} := by
  have hlin : (Matrix.toLin (Pi.basisFun K (Fin m ⊕ Fin m))
      (Pi.basisFun K (Fin m ⊕ Fin m))) (Matrix.diagonal v) = Matrix.toLin' (Matrix.diagonal v) := by
    rw [Matrix.toLin_eq_toLin']
  rw [← hlin]; rw [← Matrix.rank_eq_finrank_range_toLin (Matrix.diagonal v)
      (Pi.basisFun K (Fin m ⊕ Fin m)) (Pi.basisFun K (Fin m ⊕ Fin m)), Matrix.rank_diagonal]
  refine Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl _) ?_); intro a
  simp only [Equiv.refl_apply]; constructor
  · intro h; rcases hv a with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h
    rw [h]; exact one_ne_zero

private theorem exists_ne_inl_eq_one_of_four_le_card {K : Type} [Field K] [DecidableEq K] {m : ℕ}
    (v : Fin m ⊕ Fin m → K)
    (hsym : ∀ a, v a = v (Equiv.sumComm (Fin m) (Fin m) a))
    (h4 : 4 ≤ Fintype.card {a // v a = 1}) :
    ∃ i k : Fin m, i ≠ k ∧ v (Sum.inl i) = 1 ∧ v (Sum.inl k) = 1 := by
  classical
  let I := {i : Fin m // v (Sum.inl i) = 1}
  have hmemr : ∀ i : I, v (Sum.inr i.1) = 1 := by
    intro i
    have h := hsym (Sum.inl i.1)
    rw [show Equiv.sumComm (Fin m) (Fin m) (Sum.inl i.1) = Sum.inr i.1 from rfl] at h
    rw [← h]
    exact i.2
  let f : I ⊕ I → {a : Fin m ⊕ Fin m // v a = 1}
    | Sum.inl i => ⟨Sum.inl i.1, i.2⟩
    | Sum.inr i => ⟨Sum.inr i.1, hmemr i⟩
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rcases a with i | i
    · exact ⟨Sum.inl ⟨i, ha⟩, rfl⟩
    · refine ⟨Sum.inr ⟨i, ?_⟩, rfl⟩
      have h := hsym (Sum.inl i)
      rw [show Equiv.sumComm (Fin m) (Fin m) (Sum.inl i) = Sum.inr i from rfl] at h
      rw [h]
      exact ha
  have hle := Fintype.card_le_of_surjective f hf
  rw [Fintype.card_sum] at hle
  have h2 : 2 ≤ Fintype.card I := by omega
  obtain ⟨i, k, hik⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card I)
  exact ⟨i.1, k.1, fun h => hik (Subtype.ext h), i.2, k.2⟩

private theorem exists_diagSp_mem_aux {K : Type} [Field K] {m : ℕ}
    [Finite K] [CharP K 2] (p : ℕ) (t : Fin m → Kˣ) {J : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K)))) :
    ∃ (x : Fin m → Kˣ) (j : Fin m), (∃ k : ℕ, x ^ p ^ k = 1) ∧
      (∀ u : Kˣ, (∃ k : ℕ, u ^ p ^ k = 1) → u ∈ Subgroup.zpowers (x j)) ∧
      diagSp K m x ∈ J := by
  classical
  let F : Fintype K := Fintype.ofFinite K
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · exfalso
      subst hm
      have hsub : Subsingleton (StatedSp 0 K) := subsingleton_statedSp_zero
      have hbot : J = ⊥ := by
        refine le_antisymm (fun x hx => ?_) bot_le; rw [Subgroup.mem_bot]
        exact @Subsingleton.elim _ hsub x 1
      exact CFSG.StandardType.GGHalf.ne_bot_of_isComponentOf hJ hbot
    · exact hm
  let Pp : Subgroup Kˣ :=
    { carrier := {u | ∃ k, u ^ p ^ k = 1}
      mul_mem' := by
        rintro u v ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨a + b, ?_⟩
        rw [pow_add, pow_mul, mul_pow, ha, one_mul, ← pow_mul, mul_comm (p ^ a) (p ^ b),
          pow_mul, hb, one_pow]
      one_mem' := ⟨0, by simp⟩
      inv_mem' := by
        rintro u ⟨a, ha⟩
        refine ⟨a, ?_⟩; rw [inv_pow, ha, inv_one] }
  have hcyc : IsCyclic ↥Pp := Subgroup.isCyclic Pp
  obtain ⟨z, hzgen⟩ := @IsCyclic.exists_generator ↥Pp _ hcyc; let ζ : Kˣ := (z : Kˣ)
  have hζP : ∃ k, ζ ^ p ^ k = 1 := z.2
  have hgen : ∀ u : Kˣ, (∃ k, u ^ p ^ k = 1) → u ∈ Subgroup.zpowers ζ := by
    intro u hu; obtain ⟨a, ha⟩ := hzgen ⟨u, hu⟩
    refine ⟨a, ?_⟩; have h := congrArg (fun x : Pp => (x : Kˣ)) ha; simpa [ζ] using h
  by_cases hζ1 : ζ = 1
  · refine ⟨fun _ => 1, ⟨0, by omega⟩, ⟨0, by ext i; simp⟩, ?_, ?_⟩
    · intro u hu
      simpa [hζ1] using hgen u hu
    · change diagSp K m (1 : Fin m → Kˣ) ∈ J
      rw [map_one]; exact J.one_mem
  have hcard : Nat.card K ≠ 2 := by
    intro h2
    have hcardu : Nat.card Kˣ = 1 := by rw [Nat.card_units, h2]
    have hsub : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.mp hcardu).1
    exact hζ1 (@Subsingleton.elim Kˣ hsub ζ 1)
  let b : GL (Fin m ⊕ Fin m) K := ((diagSp K m t : StatedSp m K) : GL _ K)
  have hb : b ∈ StatedSp m K := (diagSp K m t).2
  have hodd : Odd (orderOf b) := odd_orderOf_diagSp t
  obtain ⟨Pset, hPprim, -, -, hPcomm, hPsup, -⟩ := @centralizer_block_decomp_Sp K _ F _ m b hb hodd
  let Gb : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K → Subgroup (StatedSp m K) :=
    fun ε => glBlockCentralizer (StatedSp m K).subtype {b} ε
  have hcent : Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K)) =
      (Subgroup.centralizer ({b} : Set (GL (Fin m ⊕ Fin m) K))).comap (StatedSp m K).subtype := by
    ext g; simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype, Subtype.ext_iff, Subgroup.coe_mul]; rfl
  have hC : IsComponentOf J (⨆ ε ∈ Pset, Gb ε) := by
    change IsComponentOf J (⨆ ε ∈ Pset, glBlockCentralizer (StatedSp m K).subtype {b} ε)
    rw [hPsup, ← hcent]; exact hJ
  obtain ⟨ε, hεP, hJε⟩ := exists_isComponentOf_block Pset Gb hPcomm hC
  have hε : IsPrimAdjIdemIn (RingHom.id K)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (Algebra.adjoin K (Units.val ''
        ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
          Set (GL (Fin m ⊕ Fin m) K)))) ε := hPprim ε hεP
  obtain ⟨v, hεv, hv, hconst, hsym, lam0, hlam0ne, hsupp0⟩ :=
    exists_eq_diagonal_of_isPrimAdjIdemIn_diagSp t hε
  let A : Subalgebra K (Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) :=
    Algebra.adjoin K (Units.val ''
      ({(((diagSp K m t : StatedSp m K) : GL (Fin m ⊕ Fin m) K))} :
        Set (GL (Fin m ⊕ Fin m) K)))
  let Gr : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.fromBlocks 0 1 (-1) 0
  have hneg : (-1 : K) = 1 := CharTwo.neg_eq 1
  have hnegm : (-1 : Matrix (Fin m) (Fin m) K) = 1 := by
    ext i j; rw [Matrix.neg_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h, hneg]
  have hGG : Gr * Gr = 1 := by
    rw [show Gr = Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) K) 1 (-1) 0 from rfl,
      Matrix.fromBlocks_multiply, hnegm]
    simp [Matrix.fromBlocks_one]
  have hG : IsUnit Gr.det := by
    rw [isUnit_iff_ne_zero]; intro h0
    have h := congrArg Matrix.det hGG; rw [Matrix.det_mul, h0, zero_mul] at h; simp at h
  have hGh : Matrix.transpose (Gr.map (RingHom.id K)) = Gr := by
    rw [show (RingHom.id K : K → K) = id from rfl, Matrix.map_id]; ext a b
    rcases a with i | i <;> rcases b with j | j <;>
      simp [Gr, hnegm, Matrix.one_apply, eq_comm]
  have hS : ∀ s ∈ ({b} : Set (GL (Fin m ⊕ Fin m) K)),
      ∀ s' ∈ ({b} : Set (GL (Fin m ⊕ Fin m) K)), Commute s s' := by
    intro s hs s' hs'; rw [Set.mem_singleton_iff] at hs hs'; rw [hs, hs']
  have hSU : ∀ s ∈ ({b} : Set (GL (Fin m ⊕ Fin m) K)),
      Matrix.transpose ((s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map
        (RingHom.id K)) * Gr * (s : Matrix _ _ K) = Gr := by
    intro s hs; rw [Set.mem_singleton_iff] at hs
    subst hs; simpa [Gr, Matrix.map_id] using CFSG.Open.StatedAPI.mem_statedSp_iff.mp hb
  obtain ⟨e1, he1, he1ε, hcases⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn
    (RingHom.id K) (fun x => rfl) hG hGh hS hSU hε
  have hGt : Matrix.transpose Gr = Gr := by simpa [Matrix.map_id] using hGh
  have hstar : IsPrimIdemIn A (formAdj (RingHom.id K) Gr e1) :=
    TableC.isPrimIdemIn_formAdj_gram K Gr hGt hG hSU hS he1
  rcases hcases with heq | ⟨hne, hfixne, hεsum⟩
  · have hprim : IsPrimIdemIn A ε := heq ▸ he1
    have hbε : ((b : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * ε = ε :=
      diagSp_mul_eq_of_isPrimAdjIdemIn t hε hprim
    obtain ⟨n1, hrank, ⟨eiso⟩⟩ := @blockGroup_iso_Sp_one K _ F _ m b hb hodd ε hε hbε
    have hne0 : ∃ a, v a = 1 := by
      by_contra h; apply hε.2.2.1; rw [hεv]
      ext a b; have h0 : v a = 0 := by
        rcases hv a with h0 | h1
        · exact h0
        · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
      simp [Matrix.diagonal_apply, h0]
    obtain ⟨a0, ha0⟩ := hne0; have hbasis : Matrix.toLin' ε (Pi.single a0 1) = Pi.single a0 1 := by
      rw [hεv, Matrix.toLin'_apply, Matrix.diagonal_mulVec_single, ha0, one_mul]
    have hrange : LinearMap.range (Matrix.toLin' ε) ≠ ⊥ := by
      intro hbot; have h1 : Matrix.toLin' ε (Pi.single a0 1) = 0 := by
        have hzero : Matrix.toLin' ε = 0 := (LinearMap.range_eq_bot).mp hbot; rw [hzero]; simp
      rw [hbasis] at h1; have h2 := congrFun h1 a0; simp at h2
    have hfin : Module.finrank K ↥(LinearMap.range (Matrix.toLin' ε)) ≠ 0 :=
      fun h0 => hrange ((Submodule.finrank_eq_zero).mp h0)
    have hn1 : 1 ≤ n1 := by
      have h0 : n1 ≠ 0 := by intro h; apply hfin; rw [← hrank, h, mul_zero]
      omega
    let Gε : Subgroup (StatedSp m K) :=
      glBlockCentralizer (StatedSp m K).subtype {b} ε
    have hq : CFSG.Open.IsQuasisimple (StatedSp n1 K) :=
      isQuasisimple_statedSp_of_not_small hn1 (fun h => hcard h.2) (fun h => hcard h.2)
    have hqA : CFSG.Assembly.IsQuasisimple ↥(StatedSp n1 K) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hq
    have hqG : CFSG.Assembly.IsQuasisimple ↥Gε := CFSG.Assembly.IsQuasisimple.of_mulEquiv eiso hqA
    have hJG : J = Gε := CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hqG hJε
    obtain ⟨i, hi⟩ : ∃ i, v (Sum.inl i) = 1 := by
      rcases a0 with i | i
      · exact ⟨i, ha0⟩
      · refine ⟨i, ?_⟩
        have h := hsym (Sum.inl i); simpa [Equiv.sumComm] using h ▸ ha0
    let x : Fin m → Kˣ := Pi.mulSingle i ζ; refine ⟨x, i, ?_, ?_, ?_⟩
    · have h := congrArg (fun u : Kˣ => (Pi.mulSingle i u : Fin m → Kˣ)) hζP.choose_spec
      exact ⟨hζP.choose, by simpa [x, Pi.mulSingle_pow] using h⟩
    · intro u hu
      simpa [x, Pi.mulSingle_eq_same] using hgen u hu
    · rw [hJG]
      rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} (Matrix.diagonal v) from by
        rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} ε from rfl, hεv]]
      refine (diagSp_mem_glBlockCentralizer_iff t x v hv).mpr ?_; intro a ha
      rcases a with j | j
      · by_cases hji : j = i
        · subst hji
          exfalso; rw [hi] at ha; exact one_ne_zero ha
        · simp [x, Pi.mulSingle_eq_of_ne (by simpa using hji)]
      · by_cases hji : j = i
        · subst hji
          have hii : v (Sum.inr j) = 1 := by
            have h := hsym (Sum.inl j); simpa [Equiv.sumComm] using h ▸ hi
          exfalso; rw [hii] at ha; exact one_ne_zero ha
        · simp [x, Pi.mulSingle_eq_of_ne (by simpa using hji)]
  · obtain ⟨d, mm, E, hEfield, hEfin, hd, -, hrank, -, ⟨eiso⟩⟩ :=
      @blockGroup_iso_Sp_linear K _ F _ m b hb hodd ε e1 (formAdj (RingHom.id K) Gr e1)
        hε he1 hstar (fun h => hfixne h.symm) hεsum
    let S : Subgroup (GL (Fin mm) E) := StatedSL mm E
    let Gε : Subgroup (StatedSp m K) :=
      glBlockCentralizer (StatedSp m K).subtype {b} ε
    have hcompJ : IsComponentOf (J.subgroupOf Gε) ⊤ := by
      have hC₀ : (J.subgroupOf Gε).map Gε.subtype = J := by
        rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJε.1]
      have hH : (⊤ : Subgroup ↥Gε).map Gε.subtype = Gε := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [← CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff Gε.subtype_injective,
        hC₀, hH]
      exact hJε
    have himg : IsComponentOf ((J.subgroupOf Gε).map eiso.toMonoidHom) ⊤ := by
      have h := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_iff
        (f := eiso.toMonoidHom) eiso.injective).2 hcompJ
      rwa [Subgroup.map_top_of_surjective _ eiso.surjective] at h
    have hSL : (J.subgroupOf Gε).map eiso.toMonoidHom = S :=
      eq_statedSL_of_isComponentOf_top himg
    have hmm : 2 ≤ mm := by
      by_contra h
      have hle : mm ≤ 1 := by omega
      have hsub : Subsingleton ↥S :=
        CFSG.LieType.SemisimpleCentralizers.Held.hct_subsingleton_statedSL_of_le_one hle
      have hSLbot : S = ⊥ := Subgroup.eq_bot_of_subsingleton S
      have hmapbot : (J.subgroupOf Gε).map eiso.toMonoidHom = ⊥ := by rw [hSL, hSLbot]
      have hJsub : J.subgroupOf Gε = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ eiso.injective).1 hmapbot
      apply CFSG.StandardType.GGHalf.ne_bot_of_isComponentOf hJ
      apply (Subgroup.eq_bot_iff_forall J).mpr; intro x hx
      have hx' : (⟨x, hJε.1 hx⟩ : Gε) ∈ J.subgroupOf Gε := hx; rw [hJsub] at hx'; simpa using hx'
    have hrank4 : 4 ≤ Module.finrank K (LinearMap.range (Matrix.toLin' ε)) := by
      rw [← hrank]; nlinarith
    have hcardS : 4 ≤ Fintype.card {a // v a = 1} := by
      rw [← finrank_diagonal_eq_card v hv]; rw [hεv] at hrank4; exact hrank4
    obtain ⟨i, k, hikne, hi, hk⟩ := exists_ne_inl_eq_one_of_four_le_card v hsym hcardS
    have hrel : t k = t i ∨ t k = (t i)⁻¹ := by
      have hkS := hsupp0 (Sum.inl k) hk; have hiS := hsupp0 (Sum.inl i) hi
      rcases hkS with hk' | hk' <;> rcases hiS with hi' | hi'
      · left; apply Units.ext; simpa using hk'.trans hi'.symm
      · right
        apply Units.ext; rw [Units.val_inv_eq_inv_val]
        have hkK : (t k : K) = lam0 := by simpa using hk'
        have hiK : (t i : K) = lam0⁻¹ := by simpa using hi'
        rw [hkK, hiK]; simp
      · right
        apply Units.ext; rw [Units.val_inv_eq_inv_val]
        have hkK : (t k : K) = lam0⁻¹ := by simpa using hk'
        have hiK : (t i : K) = lam0 := by simpa using hi'
        rw [hkK, hiK]
      · left; apply Units.ext; simpa using hk'.trans hi'.symm
    have hbase : diagSp K m (Pi.mulSingle i ζ) ∈ Gε := by
      rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} (Matrix.diagonal v) from by
        rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} ε from rfl, hεv]]
      refine (diagSp_mem_glBlockCentralizer_iff t (Pi.mulSingle i ζ) v hv).mpr ?_; intro a ha
      rcases a with j | j
      · by_cases hji : j = i
        · subst hji
          exfalso; rw [hi] at ha; exact one_ne_zero ha
        · simp [Pi.mulSingle_eq_of_ne (by simpa using hji)]
      · by_cases hji : j = i
        · subst hji
          have hii : v (Sum.inr j) = 1 := by
            have h := hsym (Sum.inl j); simpa [Equiv.sumComm] using h ▸ hi
          exfalso; rw [hii] at ha; exact one_ne_zero ha
        · simp [Pi.mulSingle_eq_of_ne (by simpa using hji)]
    rcases hrel with hrel | hrel
    · let x : Fin m → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle k ζ⁻¹
      have hw : permSp K (Equiv.swap i k) ∈ Gε := by
        rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} (Matrix.diagonal v) from by
          rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} ε from rfl, hεv]]
        exact permSp_swap_mem_glBlockCentralizer_diagSp t v hv hsym hrel hi hk
      refine ⟨x, i, ?_, ?_, ?_⟩
      · have h := congrArg (fun u : Kˣ => (Pi.mulSingle i u : Fin m → Kˣ)) hζP.choose_spec
        have : x ^ p ^ hζP.choose = 1 := by
          rw [show x = Pi.mulSingle i ζ * Pi.mulSingle k ζ⁻¹ from rfl, mul_pow,
            ← Pi.mulSingle_pow, ← Pi.mulSingle_pow]
          simp [hζP.choose_spec]
        exact ⟨hζP.choose, this⟩
      · intro u hu
        have hxi : x i = ζ := by simp [x, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hikne]
        rw [hxi]; exact hgen u hu
      · have hcomm := commutator_diagSp_mulSingle_permSp_swap i k ζ
        have hxG : diagSp K m x ∈ Gε := by
          rw [← hcomm]; exact (Subgroup.commutator_le_self Gε)
            (Subgroup.commutator_mem_commutator hbase hw)
        have hSLmem : eiso ⟨diagSp K m x, hxG⟩ ∈ StatedSL mm E := by
          have hxeq : (⟨diagSp K m x, hxG⟩ : Gε) =
              ⟨⁅diagSp K m (Pi.mulSingle i ζ), permSp K (Equiv.swap i k)⁆,
                (Subgroup.commutator_le_self Gε)
                  (Subgroup.commutator_mem_commutator hbase hw)⟩ := Subtype.ext hcomm.symm
          rw [hxeq]; have hmap := map_commutatorElement eiso.toMonoidHom
            (⟨diagSp K m (Pi.mulSingle i ζ), hbase⟩ : Gε)
            (⟨permSp K (Equiv.swap i k), hw⟩ : Gε)
          have hcomm_e : (⟨⁅diagSp K m (Pi.mulSingle i ζ), permSp K (Equiv.swap i k)⁆,
              (Subgroup.commutator_le_self Gε)
                (Subgroup.commutator_mem_commutator hbase hw)⟩ : Gε) =
              ⁅(⟨diagSp K m (Pi.mulSingle i ζ), hbase⟩ : Gε),
                (⟨permSp K (Equiv.swap i k), hw⟩ : Gε)⁆ := Subtype.ext rfl
          rw [hcomm_e]; simpa [map_commutatorElement] using
            CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL
              (eiso (⟨diagSp K m (Pi.mulSingle i ζ), hbase⟩ : Gε))
              (eiso (⟨permSp K (Equiv.swap i k), hw⟩ : Gε))
        change eiso ⟨(diagSp K m x), hxG⟩ ∈ S at hSLmem
        rw [← hSL] at hSLmem; obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hSLmem
        have hje' : j = ⟨diagSp K m x, hxG⟩ := eiso.injective hje
        have hxJ : (j : StatedSp m K) ∈ J := hj
        rwa [hje'] at hxJ
    · let x : Fin m → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle k ζ
      have hw : TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈
          Gε := by
        rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} (Matrix.diagonal v) from by
          rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} ε from rfl, hεv]]
        exact spSwapSp_mul_permSp_swap_mem_glBlockCentralizer_diagSp t v hv hsym hrel hi hk
      refine ⟨x, i, ?_, ?_, ?_⟩
      · have h := congrArg (fun u : Kˣ => (Pi.mulSingle i u : Fin m → Kˣ)) hζP.choose_spec
        have : x ^ p ^ hζP.choose = 1 := by
          rw [show x = Pi.mulSingle i ζ * Pi.mulSingle k ζ from rfl, mul_pow,
            ← Pi.mulSingle_pow, ← Pi.mulSingle_pow]
          simp [hζP.choose_spec]
        exact ⟨hζP.choose, this⟩
      · intro u hu
        have hxi : x i = ζ := by simp [x, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hikne]
        rw [hxi]; exact hgen u hu
      · have hcomm := commutator_diagSp_mulSingle_spSwapSp_permSp_swap i k hikne ζ
        have hxG : diagSp K m x ∈ Gε := by
          rw [← hcomm]; exact (Subgroup.commutator_le_self Gε)
            (Subgroup.commutator_mem_commutator hbase hw)
        have hSLmem : eiso ⟨diagSp K m x, hxG⟩ ∈ StatedSL mm E := by
          have hxeq : (⟨diagSp K m x, hxG⟩ : Gε) =
              ⟨⁅diagSp K m (Pi.mulSingle i ζ),
                TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)⁆,
                (Subgroup.commutator_le_self Gε)
                  (Subgroup.commutator_mem_commutator hbase hw)⟩ := Subtype.ext hcomm.symm
          rw [hxeq]; have hmap := map_commutatorElement eiso.toMonoidHom
            (⟨diagSp K m (Pi.mulSingle i ζ), hbase⟩ : Gε)
            (⟨TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k),
              hw⟩ : Gε)
          have hcomm_e : (⟨⁅diagSp K m (Pi.mulSingle i ζ),
              TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k)⁆,
              (Subgroup.commutator_le_self Gε)
                (Subgroup.commutator_mem_commutator hbase hw)⟩ : Gε) =
              ⁅(⟨diagSp K m (Pi.mulSingle i ζ), hbase⟩ : Gε),
                (⟨TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k),
                  hw⟩ : Gε)⁆ := Subtype.ext rfl
          rw [hcomm_e]; simpa [map_commutatorElement] using
            CFSG.LieType.SemisimpleCentralizers.Held.commutatorElement_mem_statedSL
              (eiso (⟨diagSp K m (Pi.mulSingle i ζ), hbase⟩ : Gε))
              (eiso (⟨TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k),
                hw⟩ : Gε))
        change eiso ⟨(diagSp K m x), hxG⟩ ∈ S at hSLmem
        rw [← hSL] at hSLmem; obtain ⟨j, hj, hje⟩ := Subgroup.mem_map.mp hSLmem
        have hje' : j = ⟨diagSp K m x, hxG⟩ := eiso.injective hje
        have hxJ : (j : StatedSp m K) ∈ J := hj
        rwa [hje'] at hxJ

theorem exists_diagSp_mem_of_isComponentOf_centralizer_Sp {K : Type} [Field K] {m : ℕ}
    [Finite K] [CharP K 2] (p : ℕ) (t : Fin m → Kˣ) {J : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K)))) :
    ∃ (x : Fin m → Kˣ) (j : Fin m), (∃ k : ℕ, x ^ p ^ k = 1) ∧
      (∀ u : Kˣ, (∃ k : ℕ, u ^ p ^ k = 1) → u ∈ Subgroup.zpowers (x j)) ∧
      diagSp K m x ∈ J :=
  exists_diagSp_mem_aux p t hJ

end CFSG.StandardType
