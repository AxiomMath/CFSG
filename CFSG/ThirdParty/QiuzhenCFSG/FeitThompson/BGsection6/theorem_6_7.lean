module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_6_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.Defs

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct commutatorElement

/-! # Theorem 6.7 from BG Section 6 -/

private theorem CFSG.theorem_6_7_reduced
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hpl : HasPLengthOne (p := p) G)
    (hKbot : pPrimeCore p G = ⊥)
    {E : Subgroup G} (hEmax : E ∈ maximalElementaryAbelianSubgroups p G)
    {L : Subgroup G} (hLp' : Nat.Coprime p (Nat.card L)) (hnorm : E ≤ Subgroup.normalizer L) :
    L ≤ pPrimeCore p G := by
  classical
  let K : Subgroup G := pPrimeCore p G
  obtain ⟨hEelem, hEmaximal⟩ := hEmax
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  obtain ⟨S, hES⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hEp
  have hOp_eq_pCore : Op_p'p p G = pCore p G := by
    simpa [K] using Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G) (p := p) hKbot
  have hS_eq_Op : (S : Subgroup G) = Op_p'p p G := by
    have hS_eq : K ⊔ S = Op_p'p p G := by
      simpa [K] using (lemma_6_6_a (G := G) (p := p) hpl (S := S)).2.1
    simpa [K, hKbot] using hS_eq
  have hS_eq_pCore : (S : Subgroup G) = pCore p G := by
    rw [hS_eq_Op, hOp_eq_pCore]
  have hL_normS : L ≤ Subgroup.normalizer (S : Subgroup G) := by
    have hS_normal : (S : Subgroup G).Normal := by
      rw [hS_eq_pCore]
      exact pCore_normal (G := G) (p := p)
    let : (S : Subgroup G).Normal := hS_normal
    exact Subgroup.le_normalizer_of_normal
  have hL_centE : L ≤ Subgroup.centralizer (E : Set G) := by
    intro x hxL
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro e heE
    have hcomm_mem : ⁅e, x⁆ ∈ (S : Subgroup G) ⊓ L := by
      have hx_normS : x ∈ Subgroup.normalizer (S : Subgroup G) := hL_normS hxL
      have he_normL : e ∈ Subgroup.normalizer L := hnorm heE
      have hcomm_memS : ⁅e, x⁆ ∈ (S : Subgroup G) := by
        have hx_conj_einv : x * e⁻¹ * x⁻¹ ∈ (S : Subgroup G) :=
          ((Subgroup.mem_normalizer_iff).1 hx_normS e⁻¹).1 ((S : Subgroup G).inv_mem (hES heE))
        simpa [commutatorElement_def, mul_assoc] using
          (S : Subgroup G).mul_mem (hES heE) hx_conj_einv
      have hcomm_memL : ⁅e, x⁆ ∈ L := by
        have he_conj_x : e * x * e⁻¹ ∈ L :=
          ((Subgroup.mem_normalizer_iff).1 he_normL x).1 hxL
        simpa [commutatorElement_def, mul_assoc] using L.mul_mem he_conj_x (L.inv_mem hxL)
      exact ⟨hcomm_memS, hcomm_memL⟩
    have hSL_cop : Nat.Coprime (Nat.card S) (Nat.card L) := by
      rcases S.isPGroup'.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact Nat.Coprime.pow_left n hLp'
    have hSL_bot : (S : Subgroup G) ⊓ L = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hSL_cop).eq_bot
    have hcomm_bot : ⁅e, x⁆ ∈ (⊥ : Subgroup G) := by
      simpa [hSL_bot] using hcomm_mem
    simpa using hcomm_bot
  have hL_centS : L ≤ Subgroup.centralizer (S : Set G) := by
    let : Fact (IsPGroup p ↥(S : Subgroup G)) := ⟨S.isPGroup'⟩
    let : MulDistribMulAction ↥L ↥(S : Subgroup G) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) L (S : Subgroup G) hL_normS
    let Esub : Subgroup ↥(S : Subgroup G) := E.subgroupOf (S : Subgroup G)
    have hEsub_elem : IsElementaryAbelian p ↥Esub := by
      let : IsMulCommutative ↥E := hEelem.toIsMulCommutative
      refine
        { toIsMulCommutative := by infer_instance
          exponent_dvd_p := ?_ }
      have hmap : Esub.map (S : Subgroup G).subtype = E := by
        change (E.subgroupOf (S : Subgroup G)).map (S : Subgroup G).subtype = E
        exact Subgroup.map_subgroupOf_eq_of_le hES
      have hExpEq : Monoid.exponent Esub = Monoid.exponent E := by
        calc
          Monoid.exponent Esub = Monoid.exponent (Esub.map (S : Subgroup G).subtype) := by
            exact Monoid.exponent_eq_of_mulEquiv
              (Subgroup.equivMapOfInjective Esub (S : Subgroup G).subtype Subtype.coe_injective)
          _ = Monoid.exponent E := by rw [hmap]
      rw [hExpEq]
      exact IsElementaryAbelian.exponent_dvd_p p E
    have hEsub : ∃ _ : Fact (IsPGroup p ↥Esub), IsElementaryAbelian p ↥Esub := by
      refine ⟨⟨S.isPGroup'.to_subgroup Esub⟩, hEsub_elem⟩
    have hSL_cop : Nat.Coprime (Nat.card ↥L) (Nat.card ↥(S : Subgroup G)) := by
      rcases S.isPGroup'.exists_card_eq with ⟨n, hn⟩
      rw [hn]
      exact Nat.Coprime.symm (Nat.Coprime.pow_left n hLp')
    have htrivS : ActsTrivially (A := ↥L) (G := ↥(S : Subgroup G)) := by
      refine corollary_1_12 (G := ↥(S : Subgroup G)) (A := ↥L) (p := p) hodd Esub hEsub hSL_cop ?_
      intro g hgcent hgord a
      have hg_centE : (g : G) ∈ Subgroup.centralizer (E : Set G) := by
        rw [Subgroup.mem_centralizer_iff] at hgcent ⊢
        intro e heE
        let eS : ↥(S : Subgroup G) := ⟨e, hES heE⟩
        have heEsub : eS ∈ Esub := by
          exact heE
        exact congrArg Subtype.val (hgcent eS heEsub)
      have hgE : (g : G) ∈ E := by
        let B : Subgroup G := Subgroup.closure ((E : Set G) ∪ ({(g : G)} : Set G))
        have hE_le_B : E ≤ B := by
          intro x hxE
          exact Subgroup.subset_closure (Or.inl hxE)
        have hg_mem_B : (g : G) ∈ B := by
          exact Subgroup.subset_closure (Or.inr (by simp))
        have hB_comm :
            ∀ x ∈ ((E : Set G) ∪ ({(g : G)} : Set G)),
              ∀ y ∈ ((E : Set G) ∪ ({(g : G)} : Set G)), x * y = y * x := by
          let : IsMulCommutative ↥E := hEelem.toIsMulCommutative
          intro x hx y hy
          rcases hx with hxE | hxg
          · rcases hy with hyE | hyg
            · let : IsMulCommutative ↥E := hEelem.toIsMulCommutative
              simpa using congrArg Subtype.val
                ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
            · rcases Set.mem_singleton_iff.mp hyg with rfl
              exact Subgroup.mem_centralizer_iff.mp hg_centE x hxE
          · rcases Set.mem_singleton_iff.mp hxg with rfl
            rcases hy with hyE | hyg
            · exact (Subgroup.mem_centralizer_iff.mp hg_centE y hyE).symm
            · rcases Set.mem_singleton_iff.mp hyg with rfl
              simp
        let : IsMulCommutative B := Subgroup.isMulCommutative_closure (fun x hx y hy _ => hB_comm x hx y hy)
        let : CommGroup B := IsMulCommutative.instCommGroup
        have hB_elem : IsElementaryAbelian p ↥B := by
          refine
            { toIsMulCommutative := by
                refine ⟨⟨?_⟩⟩
                intro a b
                exact mul_comm a b
              exponent_dvd_p := ?_ }
          refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
          intro x
          apply Subtype.ext
          change (x : G) ^ p = 1
          have hgen_pow : ∀ z ∈ ((E : Set G) ∪ ({(g : G)} : Set G)), z ^ p = 1 := by
            intro z hz
            rcases hz with hzE | hzg
            · have htmp : (⟨z, hzE⟩ : E) ^ p = 1 := by
                exact
                  (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                    (IsElementaryAbelian.exponent_dvd_p p E)) ⟨z, hzE⟩
              simpa using congrArg Subtype.val htmp
            · rcases Set.mem_singleton_iff.mp hzg with rfl
              simpa [hgord] using pow_orderOf_eq_one (g : G)
          exact
            Subgroup.closure_induction'' (s := ((E : Set G) ∪ ({(g : G)} : Set G)))
              (fun z hz => hgen_pow z hz)
              (fun z hz => by
                simpa [inv_pow] using congrArg Inv.inv (hgen_pow z hz))
              (by simp)
              (fun x y hx hy hxpow hypow => by
                have hxy : x * y = y * x := by
                  simpa using congrArg Subtype.val (mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
                have hxyC : Commute x y := by
                  simpa [Commute, SemiconjBy] using hxy
                simpa [hxpow, hypow] using hxyC.mul_pow p)
              x.2
        have hBE : E = B := hEmaximal B hE_le_B hB_elem
        simpa [hBE] using hg_mem_B
      have ha_centE : (a : G) ∈ Subgroup.centralizer (E : Set G) := hL_centE a.2
      apply Subtype.ext
      have hcomm : (a : G) * (g : G) = (g : G) * (a : G) := by
        symm
        exact Subgroup.mem_centralizer_iff.mp ha_centE _ hgE
      calc
        ((a • g : ↥(S : Subgroup G)) : G) = (a : G) * (g : G) * (a : G)⁻¹ := by
          rfl
        _ = (g : G) * ((a : G) * (a : G)⁻¹) := by
          rw [hcomm]
          simp [mul_assoc]
        _ = (g : G) := by simp
    intro x hxL
    rw [Subgroup.mem_centralizer_iff]
    intro s hsS
    let sS : ↥(S : Subgroup G) := ⟨s, hsS⟩
    have hsfix : (⟨x, hxL⟩ : L) • sS = sS := htrivS ⟨x, hxL⟩ sS
    have hconj : x * s * x⁻¹ = s := by
      have : ((⟨x, hxL⟩ : L) • (⟨s, hsS⟩ : S)).val = (⟨s, hsS⟩ : S).val := by rw [hsfix]
      simpa
    have hcomm : x * s = s * x := by
      have htmp := congrArg (fun t : G => t * x) hconj
      simpa [mul_assoc] using htmp
    exact hcomm.symm
  have hL_le_S : L ≤ S := by
    intro y hy
    have hy_centS : y ∈ Subgroup.centralizer (S : Set G) := hL_centS hy
    have hy_centP : y ∈ Subgroup.centralizer (pCore p G : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hy_centS ⊢
      intro z hzP
      have hzS : z ∈ (S : Subgroup G) := by
        simpa [hS_eq_pCore] using hzP
      exact hy_centS z hzS
    have hy_pCore : y ∈ pCore p G :=
      (centralizer_pCore_le_pCore_of_pPrimeCore_eq_bot
        (G := G) (hsolv := inferInstance) (p := p) hKbot) hy_centP
    simpa [hS_eq_pCore] using hy_pCore
  have hL_bot : L = ⊥ := by
    have hLpGroup : IsPGroup p L :=
      IsPGroup.to_le (H := L) (K := (S : Subgroup G)) S.isPGroup' hL_le_S
    have hL_card_one : Nat.card L = 1 := by
      rcases hLpGroup.card_eq_or_dvd with h1 | hpdvd
      · exact h1
      · exfalso
        exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hLp') hpdvd
    exact (Subgroup.card_eq_one (H := L)).1 hL_card_one
  simpa [K, hKbot] using hL_bot.le

public theorem CFSG.theorem_6_7
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {p : ℕ} [Fact p.Prime] (hodd : p ≠ 2) (hpl : HasPLengthOne (p := p) G)
    {E : Subgroup G} (hEmax : E ∈ maximalElementaryAbelianSubgroups p G)
    {L : Subgroup G} (hLp' : Nat.Coprime p (Nat.card L)) (hnorm : E ≤ Subgroup.normalizer L) :
    L ≤ pPrimeCore p G := by
  classical
  let K : Subgroup G := pPrimeCore p G
  let : K.Normal := by
    simpa [K] using (pPrimeCore_normal (G := G) (p := p))
  have hEelem : IsElementaryAbelian p E := hEmax.1
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  obtain ⟨S, hES⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hEp
  have hreduce : L ≤ K := by
    by_cases hKbot : K = ⊥
    · simpa [K] using
        theorem_6_7_reduced (G := G) (p := p) hodd hpl hKbot
          (E := E) hEmax (L := L) hLp' hnorm
    · -- Quotient-reduction step: pass to `G / O_{p'}(G)` and apply the reduced case there.
      -- The key bookkeeping facts are:
      -- * `HasPLengthOne p (G ⧸ K)`;
      -- * the images of `E` and `L` in the quotient satisfy the same hypotheses;
      -- * `pPrimeCore p (G ⧸ K) = ⊥`.
      let q : G →* G ⧸ K := QuotientGroup.mk' K
      have hpl_bar : HasPLengthOne (p := p) (G ⧸ K) := by
        have hKbar_bot : pPrimeCore p (G ⧸ K) = ⊥ := by
          simpa [K] using
            (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
        have hK_le_Op : K ≤ Op_p'p p G := by
          simpa [K, Op_p'p, q] using
            (QuotientGroup.le_comap_mk' K (pCore p (G ⧸ K)))
        have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ K) := by
          simpa [Op_p'p, q] using
            (Subgroup.map_comap_eq_self_of_surjective
              (f := QuotientGroup.mk' K) (h := QuotientGroup.mk'_surjective K)
              (H := pCore p (G ⧸ K)))
        let e1 : (G ⧸ K) ⧸ (Op_p'p p G).map q ≃* G ⧸ Op_p'p p G :=
          QuotientGroup.quotientQuotientEquivQuotient (N := K) (M := Op_p'p p G) hK_le_Op
        let e2 : (G ⧸ K) ⧸ pCore p (G ⧸ K) ≃* (G ⧸ K) ⧸ (Op_p'p p G).map q :=
          QuotientGroup.quotientMulEquivOfEq hmap_op.symm
        let e : (G ⧸ K) ⧸ pCore p (G ⧸ K) ≃* G ⧸ Op_p'p p G := e2.trans e1
        have hpl_top : Op_p'pp' p G = ⊤ := by
          simpa [HasPLengthOne] using hpl
        have hcoreTopG : pPrimeCore p (G ⧸ Op_p'p p G) = ⊤ := by
          have htmp :
              (pPrimeCore p (G ⧸ Op_p'p p G)).comap
                (QuotientGroup.mk' (Op_p'p p G)) = ⊤ := by
            simpa [Op_p'pp'] using hpl_top
          apply (Subgroup.comap_injective
            (QuotientGroup.mk'_surjective (Op_p'p p G)))
          simpa using htmp
        have hcopQuot : Nat.Coprime p (Nat.card (G ⧸ Op_p'p p G)) := by
          simpa [hcoreTopG] using
            (pPrimeCore_coprime_card (G := G ⧸ Op_p'p p G) (p := p))
        have hcopDouble : Nat.Coprime p (Nat.card ((G ⧸ K) ⧸ pCore p (G ⧸ K))) := by
          rw [Nat.card_congr e.toEquiv]
          exact hcopQuot
        have htopDouble_cop :
            Nat.Coprime p (Nat.card (⊤ : Subgroup ((G ⧸ K) ⧸ pCore p (G ⧸ K)))) := by
          simpa using hcopDouble
        have hcoreTopDouble : pPrimeCore p ((G ⧸ K) ⧸ pCore p (G ⧸ K)) = ⊤ := by
          apply top_le_iff.mp
          exact le_sSup
            ⟨(inferInstance : (⊤ : Subgroup ((G ⧸ K) ⧸ pCore p (G ⧸ K))).Normal), htopDouble_cop⟩
        have hOpQ_eq : Op_p'p p (G ⧸ K) = pCore p (G ⧸ K) :=
          Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ K) (p := p) hKbar_bot
        let eOp : (G ⧸ K) ⧸ Op_p'p p (G ⧸ K) ≃* (G ⧸ K) ⧸ pCore p (G ⧸ K) :=
          QuotientGroup.quotientMulEquivOfEq hOpQ_eq
        have hcoreTopOpQ : pPrimeCore p ((G ⧸ K) ⧸ Op_p'p p (G ⧸ K)) = ⊤ := by
          have hmap_op :
              (pPrimeCore p ((G ⧸ K) ⧸ pCore p (G ⧸ K))).map eOp.symm.toMonoidHom =
                pPrimeCore p ((G ⧸ K) ⧸ Op_p'p p (G ⧸ K)) := by
            simpa [eOp] using
              (pPrimeCore_map_iso (G := ((G ⧸ K) ⧸ pCore p (G ⧸ K)))
                (G' := ((G ⧸ K) ⧸ Op_p'p p (G ⧸ K))) (p := p) eOp.symm)
          simpa [hcoreTopDouble] using hmap_op.symm
        simp [HasPLengthOne, Op_p'pp', hcoreTopOpQ]
      have hKbar_bot : pPrimeCore p (G ⧸ K) = ⊥ := by
        simpa [K] using
          (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
      have hEbar_max : E.map q ∈ maximalElementaryAbelianSubgroups p (G ⧸ K) := by
        have hEbar_elem : IsElementaryAbelian p (E.map q) := by
          refine
            { toIsMulCommutative := by infer_instance
              exponent_dvd_p := ?_ }
          exact dvd_trans
            (MonoidHom.exponent_dvd (MonoidHom.subgroupMap_surjective q E))
            (IsElementaryAbelian.exponent_dvd_p p E)
        have hSK_cop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card K) := by
          rcases S.isPGroup'.exists_card_eq with ⟨n, hn⟩
          rw [hn]
          simpa [K] using Nat.Coprime.pow_left n (pPrimeCore_coprime_card (G := G) (p := p))
        have hKS_bot : K ⊓ (S : Subgroup G) = ⊥ := by
          exact (Subgroup.disjoint_of_coprime_natCard hSK_cop.symm).eq_bot
        let Sbar : Sylow p (G ⧸ K) :=
          S.mapSurjective (f := q) (hf := QuotientGroup.mk'_surjective K)
        have hSbar_norm_top :
            Subgroup.normalizer ((Sbar : Subgroup (G ⧸ K)) : Set (G ⧸ K)) = ⊤ := by
          have htmp := (lemma_6_6_a (G := G ⧸ K) (p := p) hpl_bar (S := Sbar)).2.2
          simpa [hKbar_bot] using htmp
        have hSbar_normal : ((Sbar : Subgroup (G ⧸ K))).Normal := by
          exact (Subgroup.normalizer_eq_top_iff.mp hSbar_norm_top)
        let : Unique (Sylow p (G ⧸ K)) := Sylow.unique_of_normal Sbar hSbar_normal
        have hBbar_le_Sbar {Bbar : Subgroup (G ⧸ K)} (hBbar_p : IsPGroup p Bbar) :
            Bbar ≤ (Sbar : Subgroup (G ⧸ K)) := by
          obtain ⟨T, hle⟩ := IsPGroup.exists_le_sylow (G := G ⧸ K) (p := p) hBbar_p
          have hTS : T = Sbar := Subsingleton.elim _ _
          simpa [hTS] using hle
        have hqS_inj : Function.Injective (q.comp (S : Subgroup G).subtype) := by
          intro a b hab
          apply Subtype.ext
          have hdivK : ((a : G) / b : G) ∈ K := by
            exact (QuotientGroup.eq_iff_div_mem).1 hab
          have hdivS : ((a : G) / b : G) ∈ (S : Subgroup G) := by
            exact (S : Subgroup G).div_mem a.2 b.2
          have hdiv : ((a : G) / b : G) ∈ K ⊓ (S : Subgroup G) := ⟨hdivK, hdivS⟩
          have hdiv1 : ((a : G) / b : G) = 1 := by
            simpa [hKS_bot] using hdiv
          exact div_eq_one.mp hdiv1
        refine ⟨hEbar_elem, ?_⟩
        intro Bbar hEBbar hBbar_elem
        have hBbar_p : IsPGroup p Bbar := IsElementaryAbelian.isPGroup p Bbar
        have hBbar_le : Bbar ≤ (Sbar : Subgroup (G ⧸ K)) := hBbar_le_Sbar hBbar_p
        let Bsub : Subgroup S := Bbar.comap (q.comp (S : Subgroup G).subtype)
        have hEsub_le_Bsub : E.subgroupOf (S : Subgroup G) ≤ Bsub := by
          intro x hx
          change q ((x : S) : G) ∈ Bbar
          exact hEBbar (Subgroup.mem_map_of_mem q hx)
        have hBsub_elem : IsElementaryAbelian p Bsub := by
          refine
            { toIsMulCommutative := by
                exact Subgroup.comap_injective_isMulCommutative
                  (H := Bbar) (f := q.comp (S : Subgroup G).subtype) hqS_inj
              exponent_dvd_p := ?_ }
          refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
          intro x
          apply Subtype.ext
          let f : S →* G ⧸ K := q.comp (S : Subgroup G).subtype
          have hxmap : f x ∈ Bbar := x.2
          have hxpow_bar : (⟨f x, hxmap⟩ : Bbar) ^ p = 1 := by
            exact
              (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                (IsElementaryAbelian.exponent_dvd_p p Bbar))
                ⟨f x, hxmap⟩
          have hxpow_f : f ((x : S) ^ p) = 1 := by
            simpa [f, MonoidHom.map_pow] using congrArg Subtype.val hxpow_bar
          have hxpow_eq : ((x : S) ^ p) = 1 := by
            exact hqS_inj hxpow_f
          simpa using hxpow_eq
        let B : Subgroup G := Bsub.map (S : Subgroup G).subtype
        have hE_le_B : E ≤ B := by
          calc
            E = (E.subgroupOf (S : Subgroup G)).map (S : Subgroup G).subtype := by
              symm
              simpa using
                (Subgroup.map_subgroupOf_eq_of_le
                  (G := G) (H := E) (K := (S : Subgroup G)) hES)
            _ ≤ B := by
              exact Subgroup.map_mono hEsub_le_Bsub
        have hB_elem : IsElementaryAbelian p B := by
          refine
            { toIsMulCommutative := by infer_instance
              exponent_dvd_p := ?_ }
          exact dvd_trans
            (MonoidHom.exponent_dvd
              (MonoidHom.subgroupMap_surjective (S : Subgroup G).subtype Bsub))
            (IsElementaryAbelian.exponent_dvd_p p Bsub)
        have hBE : B = E := (hEmax.2 B hE_le_B hB_elem).symm
        have hmap :
            Bsub.map (q.comp (S : Subgroup G).subtype) = Bbar := by
          apply Subgroup.map_comap_eq_self
          intro x hx
          rcases hBbar_le hx with ⟨y, hyS, rfl⟩
          exact ⟨⟨y, hyS⟩, rfl⟩
        have hB_map : B.map q = Bbar := by
          change (Bsub.map ((S : Subgroup G).subtype)).map q = Bbar
          rw [Subgroup.map_map]
          exact hmap
        calc
          E.map q = B.map q := by simp [hBE]
          _ = Bbar := hB_map
      have hLbar_coprime : Nat.Coprime p (Nat.card (L.map q)) := by
        exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := L) q) hLp'
      have hLbar_norm : E.map q ≤ Subgroup.normalizer (L.map q) := by
        exact (Subgroup.map_mono hnorm).trans (Subgroup.le_normalizer_map (H := L) q)
      have hLbar_le : L.map q ≤ pPrimeCore p (G ⧸ K) := by
        exact
          theorem_6_7_reduced (G := G ⧸ K) (p := p) hodd hpl_bar hKbar_bot
            (E := E.map q) hEbar_max (L := L.map q) hLbar_coprime hLbar_norm
      have hL_le_comap : L ≤ (pPrimeCore p (G ⧸ K)).comap q := by
        intro x hx
        exact hLbar_le (Subgroup.mem_map_of_mem q hx)
      simpa [K, q, hKbar_bot] using hL_le_comap
  simpa [K] using hreduce
