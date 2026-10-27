module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpComp
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSpCompPair
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGTBJSpBlockAux

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp StatedSL)
open CFSG.Assembly
open CFSG.StandardType.ClassicalPosition
open CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Sp
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

theorem ggTBJ_sp_blockData {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K)
    {m : ℕ} (t : Fin m → Kˣ) {J : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K)))) :
    ∃ lam : Kˣ,
      (∀ i k : Fin m, i ≠ k → t i = t k → (t i = lam ∨ t i = lam⁻¹) →
        permSp K (Equiv.swap i k) ∈ J) ∧
      (∀ i k : Fin m, t i = lam → t k = lam⁻¹ → lam ≠ 1 →
        TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈ J) ∧
      (lam = 1 → ∀ i : Fin m, t i = 1 → TableBSymp.spSwapSp i ∈ J) ∧
      (∀ x : Fin m → Kˣ,
        ((lam = 1 ∧ ∀ i, t i = 1 → x i = 1) ∨
          (lam ≠ 1 ∧ ∃ c : Kˣ, ∀ i, (t i = lam → x i = c) ∧ (t i = lam⁻¹ → x i = c⁻¹))) →
        ∀ j ∈ J, diagSp K m x * j = j * diagSp K m x) := by
  classical
  have hcard : Nat.card K ≠ 2 := by omega
  let F : Fintype K := Fintype.ofFinite K
  let b : GL (Fin m ⊕ Fin m) K := ((diagSp K m t : StatedSp m K) : GL _ K)
  have hb : b ∈ StatedSp m K := (diagSp K m t).2
  have hodd : Odd (orderOf b) := ggTBJSpB_odd_orderOf_diagSp t
  obtain ⟨Pset, hPprim, -, -, hPcomm, hPsup, -⟩ :=
    @centralizer_block_decomp_Sp K _ F _ m b hb hodd
  let Gb : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K → Subgroup (StatedSp m K) :=
    fun ε => glBlockCentralizer (StatedSp m K).subtype {b} ε
  have hcent : Subgroup.centralizer ({diagSp K m t} : Set (StatedSp m K)) =
      (Subgroup.centralizer ({b} : Set (GL (Fin m ⊕ Fin m) K))).comap
        (StatedSp m K).subtype := by
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
  let Gε : Subgroup (StatedSp m K) :=
    glBlockCentralizer (StatedSp m K).subtype {b} ε
  have hGεv : Gε = glBlockCentralizer (StatedSp m K).subtype {b} (Matrix.diagonal v) := by
    rw [show Gε = glBlockCentralizer (StatedSp m K).subtype {b} ε from rfl, hεv]
  have hvne : ∃ a, v a = 1 := by
    by_contra h
    apply hε.2.2.1
    rw [hεv]
    ext a b
    have h0 : v a = 0 := by
      rcases hv a with h0 | h1
      · exact h0
      · exact absurd h1 (fun h1 => h ⟨a, h1⟩)
    simp [Matrix.diagonal_apply, h0]
  let lam : Kˣ := Units.mk0 lam0 hlam0ne
  have hlam_val : (lam : K) = lam0 := rfl
  have hlam_inv_val : ((lam⁻¹ : Kˣ) : K) = lam0⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hlam_val]
  have hlam_iff : ∀ u : Kˣ, u = lam ↔ (u : K) = lam0 := by
    intro u; constructor
    · intro h; rw [h, hlam_val]
    · intro h; exact Units.ext h
  have hlam_inv_iff : ∀ u : Kˣ, u = lam⁻¹ ↔ (u : K) = lam0⁻¹ := by
    intro u; constructor
    · intro h; rw [h, hlam_inv_val]
    · intro h; exact Units.ext (by rw [h, hlam_inv_val])
  have hsupp1 : ∀ a, (diagSpEntry t a = lam0 ∨ diagSpEntry t a = lam0⁻¹) → v a = 1 := by
    obtain ⟨a0, ha0⟩ := hvne
    have hb0 : ∃ b0, v b0 = 1 ∧ diagSpEntry t b0 = lam0 := by
      rcases hsupp0 a0 ha0 with h | h
      · exact ⟨a0, ha0, h⟩
      · refine ⟨Equiv.sumComm (Fin m) (Fin m) a0, ?_, ?_⟩
        · rw [← hsym a0]; exact ha0
        · have hsum : diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a0) =
              (diagSpEntry t a0)⁻¹ := by
            rcases a0 with i | i <;> simp [Equiv.sumComm]
          rw [hsum, h, inv_inv]
    obtain ⟨b0, hb0v, hb0e⟩ := hb0
    intro a ha
    rcases ha with h | h
    · rw [hconst a b0 (h.trans hb0e.symm)]
      exact hb0v
    · have h1 : diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) = lam0 := by
        have hsum : diagSpEntry t (Equiv.sumComm (Fin m) (Fin m) a) =
            (diagSpEntry t a)⁻¹ := by
          rcases a with i | i <;> simp [Equiv.sumComm]
        rw [hsum, h, inv_inv]
      rw [hsym a, hconst _ _ (h1.trans hb0e.symm)]
      exact hb0v
  have hJinv : ∀ g ∈ Gε, g * g = 1 → g ∈ J := by
    rcases hcases with heq | ⟨hne, hfixne, hεsum⟩
    · have hprim : IsPrimIdemIn A ε := heq ▸ he1
      have hbε : (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * ε = ε :=
        diagSp_mul_eq_of_isPrimAdjIdemIn t hε hprim
      obtain ⟨n1, hrank, ⟨eiso⟩⟩ :=
        @blockGroup_iso_Sp_one K _ F _ m b hb hodd ε hε hbε
      obtain ⟨a0, ha0⟩ := hvne
      have hbasis : Matrix.toLin' ε (Pi.single a0 1) = Pi.single a0 1 := by
        rw [hεv, Matrix.toLin'_apply, Matrix.diagonal_mulVec_single, ha0, one_mul]
      have hrange : LinearMap.range (Matrix.toLin' ε) ≠ ⊥ := by
        intro hbot
        have h1 : Matrix.toLin' ε (Pi.single a0 1) = 0 := by
          have hzero : Matrix.toLin' ε = 0 := (LinearMap.range_eq_bot).mp hbot
          rw [hzero]; simp
        rw [hbasis] at h1
        have h2 := congrFun h1 a0; simp at h2
      have hfin : Module.finrank K ↥(LinearMap.range (Matrix.toLin' ε)) ≠ 0 :=
        fun h0 => hrange ((Submodule.finrank_eq_zero).mp h0)
      have hn1 : 1 ≤ n1 := by
        have h0 : n1 ≠ 0 := by intro h; apply hfin; rw [← hrank, h, mul_zero]
        omega
      have hq : CFSG.Open.IsQuasisimple (StatedSp n1 K) :=
        isQuasisimple_statedSp_of_not_small hn1 (fun h => hcard h.2) (fun h => hcard h.2)
      have hqA : CFSG.Assembly.IsQuasisimple ↥(StatedSp n1 K) :=
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mpr hq
      have hqG : CFSG.Assembly.IsQuasisimple ↥Gε :=
        CFSG.Assembly.IsQuasisimple.of_mulEquiv eiso hqA
      have hJG : J = Gε := CFSG.StandardType.GGHalf.eq_of_isComponentOf_isQuasisimple hqG hJε
      intro g hg _
      rwa [hJG]
    · obtain ⟨d, mm, E, hEfield, hEfin, hd, hEcard, hrank, hdeg, ⟨eiso⟩⟩ :=
        @blockGroup_iso_Sp_linear K _ F _ m b hb hodd ε e1 (formAdj (RingHom.id K) Gr e1)
          hε he1 hstar (fun h => hfixne h.symm) hεsum
      letI : Field E := hEfield
      letI : Fintype E := hEfin
      obtain ⟨nE, -, hnE⟩ := @FiniteField.card K _ F 2 (inferInstance : CharP K 2)
      have hEpow : Nat.card E = 2 ^ ((nE : ℕ) * d) := by
        rw [@Nat.card_eq_fintype_card E _, hEcard, hnE, ← pow_mul]
      letI : CharP E 2 := charP_two_of_card hEpow
      let S : Subgroup (GL (Fin mm) E) := StatedSL mm E
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
      intro g hg hgsq
      have hsq : eiso ⟨g, hg⟩ * eiso ⟨g, hg⟩ = 1 := by
        have h1 : (⟨g, hg⟩ : Gε) * ⟨g, hg⟩ = 1 := by
          apply Subtype.ext
          show g * g = 1
          exact hgsq
        rw [← map_mul, h1, map_one]
      have hmem : eiso ⟨g, hg⟩ ∈ StatedSL mm E := ggTBJSpB_mem_statedSL_of_mul_self hsq
      change eiso ⟨g, hg⟩ ∈ S at hmem
      rw [← hSL] at hmem
      obtain ⟨k, hk, hke⟩ := Subgroup.mem_map.mp hmem
      have hke' : k = ⟨g, hg⟩ := eiso.injective hke
      have hkJ : (k : StatedSp m K) ∈ J := hk
      rwa [hke'] at hkJ
  refine ⟨lam, ?_, ?_, ?_, ?_⟩
  · intro i k hikne htik h
    have hti' : (t i : K) = lam0 ∨ (t i : K) = lam0⁻¹ := by
      rcases h with h | h
      · exact Or.inl ((hlam_iff (t i)).mp h)
      · exact Or.inr ((hlam_inv_iff (t i)).mp h)
    have htk' : (t k : K) = lam0 ∨ (t k : K) = lam0⁻¹ := by rw [← htik]; exact hti'
    have hi : v (Sum.inl i) = 1 := by apply hsupp1; simpa using hti'
    have hk : v (Sum.inl k) = 1 := by apply hsupp1; simpa using htk'
    have hg : permSp K (Equiv.swap i k) ∈ Gε := by
      rw [hGεv]
      exact permSp_swap_mem_glBlockCentralizer_diagSp t v hv hsym htik.symm hi hk
    exact hJinv _ hg (ggTBJSpB_permSp_swap_mul_self i k)
  · intro i k hti htk hne1
    have hikne : i ≠ k := by
      intro hik
      apply hne1
      have h1 : lam = lam⁻¹ := hti.symm.trans ((congrArg t hik).trans htk)
      exact ggTBJSpB_eq_one_of_mul_self (by
        have hh := congrArg (fun z : Kˣ => lam * z) h1
        rwa [mul_inv_cancel] at hh)
    have hti' : (t i : K) = lam0 := (hlam_iff (t i)).mp hti
    have htk' : (t k : K) = lam0⁻¹ := (hlam_inv_iff (t k)).mp htk
    have hi : v (Sum.inl i) = 1 := by apply hsupp1; exact Or.inl (by simpa using hti')
    have hk : v (Sum.inl k) = 1 := by apply hsupp1; exact Or.inr (by simpa using htk')
    have hik : t k = (t i)⁻¹ := by rw [htk, hti]
    have hg : TableBSymp.spSwapSp i * TableBSymp.spSwapSp k * permSp K (Equiv.swap i k) ∈
        Gε := by
      rw [hGεv]
      exact spSwapSp_mul_permSp_swap_mem_glBlockCentralizer_diagSp t v hv hsym hik hi hk
    exact hJinv _ hg (ggTBJSpB_spSwapSp_mul_permSp_swap_mul_self hikne)
  · intro hlam1 i hti
    have hlam0_1 : lam0 = 1 := by
      have h := congrArg (fun z : Kˣ => (z : K)) hlam1
      simpa [hlam_val] using h
    have hvi : v (Sum.inl i) = 1 := by
      apply hsupp1; left
      simpa [hlam0_1] using congrArg (fun z : Kˣ => (z : K)) hti
    have hg : TableBSymp.spSwapSp i ∈ Gε := by
      rw [hGεv]
      exact ggTBJSpB_spSwapSp_mem_glBlockCentralizer_diagSp t v hv hsym hti hvi
    exact hJinv _ hg (ggTBJSpB_spSwapSp_mul_self i)
  · intro x hxcond j hj
    have hjGε : j ∈ Gε := hJε.1 hj
    have hjmem : (((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) ∈
        Subgroup.centralizer ({b} : Set (GL (Fin m ⊕ Fin m) K)) ⊓
          glFixing (1 - Matrix.diagonal v) := by
      have h := hjGε
      simp only [Gε, glBlockCentralizer, Subgroup.mem_comap, hεv] at h
      exact h
    have hjcomm : (((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) * b =
        b * (((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hjmem).1
    have hjfix : (((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) *
        (1 - Matrix.diagonal v) = 1 - Matrix.diagonal v :=
      (Subgroup.mem_inf.mp hjmem).2
    have hx : ∀ a b, v a = 1 → v b = 1 → diagSpEntry t a = diagSpEntry t b →
        diagSpEntry x a = diagSpEntry x b := by
      rcases hxcond with ⟨hlam1, hx1⟩ | ⟨hlamne, hc⟩
      · have hlam0_1 : lam0 = 1 := by
          have h := congrArg (fun z : Kˣ => (z : K)) hlam1
          simpa [hlam_val] using h
        have hA : ∀ a, v a = 1 → diagSpEntry x a = 1 := by
          intro a ha
          have hta : diagSpEntry t a = 1 := by
            rcases hsupp0 a ha with h | h
            · rw [h, hlam0_1]
            · rw [h, hlam0_1, inv_one]
          rcases a with i | i
          · have hti : t i = 1 := Units.ext (by simpa using hta)
            have hxi : x i = 1 := hx1 i hti
            simpa [hxi]
          · have hti : t i = 1 := by
              apply Units.ext
              have h' : ((t i)⁻¹ : K) = 1 := by simpa using hta
              rwa [inv_eq_one] at h'
            have hxi : x i = 1 := hx1 i hti
            simpa [hxi]
        intro a b ha hb _
        rw [hA a ha, hA b hb]
      · obtain ⟨c, hc⟩ := hc
        have hlam0_ne_inv : lam0 ≠ lam0⁻¹ := by
          intro h
          apply hlamne
          have h2 : lam0 * lam0 = 1 := by
            have hh := congrArg (fun z : K => lam0 * z) h
            rwa [mul_inv_cancel₀ hlam0ne] at hh
          have hsq : lam0 ^ 2 = 1 := by rw [pow_two]; exact h2
          exact Units.ext (ggTBJSpB_eq_one_of_sq_eq_one hsq)
        have hdv_lam : ∀ a, v a = 1 → diagSpEntry t a = lam0 → diagSpEntry x a = c := by
          intro a ha h
          rcases a with i | i
          · have hti : t i = lam := (hlam_iff (t i)).mpr (by simpa using h)
            have hxi : x i = c := (hc i).1 hti
            simpa [hxi]
          · have hti : t i = lam⁻¹ := by
              apply (hlam_inv_iff (t i)).mpr
              have h' : ((t i : K))⁻¹ = lam0 := by simpa using h
              have h2 := congrArg (fun z : K => z⁻¹) h'
              simpa using h2
            have hxi : x i = c⁻¹ := (hc i).2 hti
            simp [hxi]
        have hdv_lam_inv : ∀ a, v a = 1 → diagSpEntry t a = lam0⁻¹ →
            diagSpEntry x a = c⁻¹ := by
          intro a ha h
          rcases a with i | i
          · have hti : t i = lam⁻¹ := (hlam_inv_iff (t i)).mpr (by simpa using h)
            have hxi : x i = c⁻¹ := (hc i).2 hti
            simpa [hxi]
          · have hti : t i = lam := by
              apply (hlam_iff (t i)).mpr
              have h' : ((t i : K))⁻¹ = lam0⁻¹ := by simpa using h
              have h2 := congrArg (fun z : K => z⁻¹) h'
              simpa using h2
            have hxi : x i = c := (hc i).1 hti
            simp [hxi]
        have hdv' : ∀ a, v a = 1 → diagSpEntry x a =
            (if diagSpEntry t a = lam0 then c else c⁻¹) := by
          intro a ha
          rcases hsupp0 a ha with h | h
          · rw [if_pos h]; exact hdv_lam a ha h
          · rw [if_neg (fun hh => hlam0_ne_inv (hh.symm.trans h))]
            exact hdv_lam_inv a ha h
        intro a b ha hb hab
        rw [hdv' a ha, hdv' b hb, hab]
    have hbm : (b : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        Matrix.diagonal (diagSpEntry t) := by
      simpa [b, mat_apply] using mat_diagSp t
    have hjm : ((((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * Matrix.diagonal (diagSpEntry t) =
        Matrix.diagonal (diagSpEntry t) *
          ((((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
      have h := congrArg (fun g : GL (Fin m ⊕ Fin m) K =>
        (g.val : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hjcomm
      simpa [hbm, Units.val_mul] using h
    have hkey := ggTBJSpB_diagonal_mul_eq_mul_of_block v (diagSpEntry t) (diagSpEntry x)
      ((((j : StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) hv hjfix hjm hconst hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, ← mat_apply (diagSp K m x), ← mat_apply j, mat_diagSp]
    exact hkey

end CFSG.StandardType

end

