module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveLocal
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveModel
import CFSG.OddTranspositions.PartThree.CommSetConjCentralizer

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 Matrix

variable {k : ℕ} {ε π : Bool}

theorem commute_mk_eq_iff_conj_eq {n : ℕ} (hn : 4 ≤ n) (ε π : Bool)
    {s : fiveReflectionGroup n ε π}
    (hs : (s : GL (Fin (n + 1)) (ZMod 5)) ∈ fiveReflections n ε π)
    (r : fiveReflectionGroup n ε π) :
    Commute (QuotientGroup.mk r : fiveProjective n ε π) (QuotientGroup.mk s) ↔
      r * s * r⁻¹ = s := by
  constructor
  · intro hc
    have hmem : r * s * r⁻¹ * s⁻¹ ∈ Subgroup.center (fiveReflectionGroup n ε π) := by
      rw [← QuotientGroup.eq_one_iff]
      have h := hc.eq
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv, h]
      group
    rcases (mem_center_fiveReflectionGroup_iff hn ε π _).mp hmem with h1 | hneg
    · have h1' : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
          (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ * (s : GL (Fin (n + 1)) (ZMod 5))⁻¹ = 1 := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] using h1
      exact Subtype.ext (mul_inv_eq_one.mp h1')
    · exfalso
      have h' : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
          (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ = -(s : GL (Fin (n + 1)) (ZMod 5)) := by
        have hcongr := congrArg (fun x => x * (s : GL (Fin (n + 1)) (ZMod 5))) hneg
        simpa [mul_assoc] using hcongr
      have hmem' : (r : GL (Fin (n + 1)) (ZMod 5)) * (s : GL (Fin (n + 1)) (ZMod 5)) *
          (r : GL (Fin (n + 1)) (ZMod 5))⁻¹ ∈ fiveReflections n ε π :=
        conj_mem_fiveReflections (fiveForm_mulVec_of_mem r.2) hs
      rw [h'] at hmem'
      exact neg_notMem_fiveReflections (by omega : 2 ≤ n) ε π hs hmem'
  · intro h
    rw [commute_iff_eq]
    have h' : r * s = s * r := by
      calc r * s = r * s * r⁻¹ * r := by group
        _ = s * r := by rw [h]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h']

theorem adjoinLinearEquiv_symm_adjoin (A : FiveAdjoin k ε π)
    (v : Fin (k + 1) → ZMod 5) (c : ZMod 5) :
    (adjoinLinearEquiv A).symm (A.j v + c • A.a) = (v, c) := by
  rw [← adjoinLinearEquiv_apply A v c, LinearEquiv.symm_apply_apply]

theorem centralizer_eq_hypLineGroup_proj_at_adjoinRa {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    (A : FiveAdjoin k ε π)
    {s : fiveProjective (k + 1) (ε == π) π}
    (hs : s ∈ fiveProjClass (k + 1) (ε == π) π)
    (hsu : ¬ Commute s (QuotientGroup.mk (adjoinRa A) : fiveProjective (k + 1) (ε == π) π)) :
    Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
        (QuotientGroup.mk (adjoinRa A))) ⊓ Subgroup.centralizer {s} =
      Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
          (QuotientGroup.mk (adjoinRa A)) ∩
        commSet (fiveProjClass (k + 1) (ε == π) π) s) := by
  have hn : 4 ≤ k + 1 := by omega
  obtain ⟨rb, hrb, rfl⟩ := hs
  obtain ⟨b, hbQ, hbπ, hb_val⟩ := exists_eq_fiveReflOf hrb
  let r_b : fiveReflectionGroup (k + 1) (ε == π) π :=
    ⟨fiveReflOf (k + 1) (ε == π) b, Subgroup.subset_closure (fiveReflOf_mem hbQ hbπ)⟩
  have hrb_eq : rb = r_b := Subtype.ext hb_val
  rw [hrb_eq] at hsu ⊢
  have hrb_rb : ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
      GL (Fin (k + 2)) (ZMod 5)) ∈ fiveReflections (k + 1) (ε == π) π :=
    hrb_eq ▸ hrb
  have hcomm_gl : ¬ Commute r_b (adjoinRa A) := by
    intro hc
    exact hsu ((commute_mk_iff_commute hn (ε := ε == π) (π := π)
      (by rw [coe_adjoinRa]; exact fiveReflOf_mem A.sign_a.1 A.sign_a.2)).mpr hc)
  have hcc : ¬ Commute (fiveReflOf (k + 1) (ε == π) b)
      (fiveReflOf (k + 1) (ε == π) A.a) := by
    intro h
    apply hcomm_gl
    rw [commute_iff_eq]
    have h' : ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
          GL (Fin (k + 2)) (ZMod 5)) *
        ((adjoinRa A : fiveReflectionGroup (k + 1) (ε == π) π) :
          GL (Fin (k + 2)) (ZMod 5)) =
        ((adjoinRa A : fiveReflectionGroup (k + 1) (ε == π) π) :
          GL (Fin (k + 2)) (ZMod 5)) *
        ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
          GL (Fin (k + 2)) (ZMod 5)) := by
      rw [show ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
            GL (Fin (k + 2)) (ZMod 5)) = fiveReflOf (k + 1) (ε == π) b from rfl,
        coe_adjoinRa A]
      exact h.eq
    exact Subtype.ext h'
  have hform_ne : fiveForm (k + 1) (ε == π) b A.a ≠ 0 := by
    intro h0
    exact hcc ((commute_fiveReflOf_iff (k + 1) (ε == π) hbQ A.sign_a.1).mpr (Or.inl h0))
  let e := adjoinLinearEquiv A
  let p := e.symm b
  let b'' : Fin (k + 1) → ZMod 5 := p.1
  let lam : ZMod 5 := p.2
  have hb_decomp : b = A.j b'' + lam • A.a := by
    have h : adjoinLinearEquiv A (b'', lam) = b := e.apply_symm_apply b
    rw [adjoinLinearEquiv_apply] at h
    exact h.symm
  have hform_b : fiveForm (k + 1) (ε == π) b A.a =
      lam * fiveForm (k + 1) (ε == π) A.a A.a := by
    rw [hb_decomp, fiveForm_add_left, fiveForm_smul_left, A.perp b'', zero_add]
  have hlam : lam ≠ 0 := by
    intro h0
    apply hform_ne
    rw [hform_b, h0, zero_mul]
  have hb''_ne : b'' ≠ 0 := by
    intro h0
    have hb : b = lam • A.a := by rw [hb_decomp, h0, map_zero, zero_add]
    refine hcc ((commute_fiveReflOf_iff (k + 1) (ε == π) hbQ A.sign_a.1).mpr
      (Or.inr ⟨lam⁻¹, ?_⟩))
    rw [hb, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  have hfix_iff (g : fiveReflectionGroup k ε π) :
      Commute (adjoinPhi A g) (QuotientGroup.mk r_b) ↔
        ((g : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'' = b'' := by
    rw [adjoinPhi_apply A g]
    rw [commute_mk_eq_iff_conj_eq hn (ε == π) π hrb_rb
      (adjoinIotaSub A g)]
    constructor
    · intro hconj
      have hgl : ((adjoinIotaSub A g * r_b * (adjoinIotaSub A g)⁻¹ :
            fiveReflectionGroup (k + 1) (ε == π) π) : GL (Fin (k + 2)) (ZMod 5)) =
          ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
            GL (Fin (k + 2)) (ZMod 5)) :=
        congrArg (fun z : fiveReflectionGroup (k + 1) (ε == π) π =>
          (z : GL (Fin (k + 2)) (ZMod 5))) hconj
      have hfix_gl : (adjoinIota A g) * fiveReflOf (k + 1) (ε == π) b *
          (adjoinIota A g)⁻¹ = fiveReflOf (k + 1) (ε == π) b := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_adjoinIotaSub] using hgl
      have hrfl : fiveReflOf (k + 1) (ε == π) ((adjoinIota A g) *ᵥ b) =
          fiveReflOf (k + 1) (ε == π) b := by
        rw [← conj_fiveReflOf (fiveForm_mulVec_of_mem
          (adjoinIota_mem_fiveReflectionGroup A g.2)) b]
        exact hfix_gl
      obtain ⟨μ, hμ⟩ := exists_smul_eq_of_fiveReflOf_eq hbQ hrfl.symm
      have hιb : (adjoinIota A g : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ b =
          A.j (((g : GL (Fin (k + 1)) (ZMod 5)) :
                Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'') + lam • A.a := by
        rw [hb_decomp, adjoinIota_apply_adjoin]
      have hμ' : A.j (((g : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'') +
            lam • A.a = A.j (μ • b'') + (μ * lam) • A.a := by
        calc A.j (((g : GL (Fin (k + 1)) (ZMod 5)) :
              Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'') +
              lam • A.a
            = (adjoinIota A g : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ b :=
              hιb.symm
          _ = μ • b := hμ
          _ = A.j (μ • b'') + (μ * lam) • A.a := by
              rw [hb_decomp]
              simp only [map_smul, smul_add, smul_smul]
      have hpair : ((((g : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'', lam) :
            (Fin (k + 1) → ZMod 5) × ZMod 5) = (μ • b'', μ * lam) := by
        have hh := congrArg (adjoinLinearEquiv A).symm hμ'
        rwa [adjoinLinearEquiv_symm_adjoin, adjoinLinearEquiv_symm_adjoin] at hh
      have hgsmul : ((g : GL (Fin (k + 1)) (ZMod 5)) :
            Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'' =
          μ • b'' := congrArg Prod.fst hpair
      have hlamμ : lam = μ * lam := congrArg Prod.snd hpair
      have hμ1 : μ = 1 := by
        have h0 : (μ - 1) * lam = 0 := by
          rw [sub_mul, one_mul, ← hlamμ, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hlam)
      rw [hμ1, one_smul] at hgsmul
      exact hgsmul
    · intro hfix
      apply Subtype.ext
      show ((adjoinIotaSub A g * r_b * (adjoinIotaSub A g)⁻¹ :
            fiveReflectionGroup (k + 1) (ε == π) π) : GL (Fin (k + 2)) (ZMod 5)) =
          ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
            GL (Fin (k + 2)) (ZMod 5))
      have hrb_coe : ((r_b : fiveReflectionGroup (k + 1) (ε == π) π) :
          GL (Fin (k + 2)) (ZMod 5)) = fiveReflOf (k + 1) (ε == π) b := rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_adjoinIotaSub, hrb_coe]
      rw [conj_fiveReflOf (fiveForm_mulVec_of_mem
        (adjoinIota_mem_fiveReflectionGroup A g.2)) b]
      have hιb : (adjoinIota A g : Matrix (Fin (k + 2)) (Fin (k + 2)) (ZMod 5)) *ᵥ b =
          A.j (((g : GL (Fin (k + 1)) (ZMod 5)) :
                Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'') + lam • A.a := by
        rw [hb_decomp, adjoinIota_apply_adjoin]
      rw [hιb, hfix, ← hb_decomp]
  have hRange : Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
        (QuotientGroup.mk (adjoinRa A))) = (adjoinPhi A).range := by
    have hs' : Subgroup.closure ((fiveReflectionGroup k ε π).subtype ⁻¹'
        fiveReflections k ε π) = ⊤ :=
      Subgroup.closure_closure_coe_preimage (k := fiveReflections k ε π)
    have h := MonoidHom.map_closure (adjoinPhi A)
      ((fiveReflectionGroup k ε π).subtype ⁻¹' fiveReflections k ε π)
    rw [hs'] at h
    rw [MonoidHom.range_eq_map, h, commSet_fiveProjClass_eq_image A hk]
    rfl
  let S_R : Set (fiveReflectionGroup k ε π) :=
    {g | (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflectionsFixing k ε π b''}
  let K : Subgroup (fiveReflectionGroup k ε π) := Subgroup.closure S_R
  have hinter : commSet (fiveProjClass (k + 1) (ε == π) π)
        (QuotientGroup.mk (adjoinRa A)) ∩
        commSet (fiveProjClass (k + 1) (ε == π) π) (QuotientGroup.mk r_b) =
      adjoinPhi A '' S_R := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_inter_iff, commSet_fiveProjClass_eq_image A hk, Set.mem_image] at hx
      obtain ⟨⟨g, hg, rfl⟩, hx2⟩ := hx
      refine ⟨g, ⟨hg, ?_⟩, rfl⟩
      rw [commSet] at hx2
      exact (hfix_iff g).mp hx2.2.1
    · rintro hx
      rw [Set.mem_image] at hx
      obtain ⟨g, hg, rfl⟩ := hx
      rw [Set.mem_inter_iff]
      constructor
      · rw [commSet_fiveProjClass_eq_image A hk, Set.mem_image]
        exact ⟨g, hg.1, rfl⟩
      · rw [commSet]
        refine ⟨(by
          have hmemu : adjoinPhi A g ∈ commSet (fiveProjClass (k + 1) (ε == π) π)
              (QuotientGroup.mk (adjoinRa A)) := by
            rw [commSet_fiveProjClass_eq_image A hk, Set.mem_image]
            exact ⟨g, hg.1, rfl⟩
          exact hmemu.1), (hfix_iff g).mpr hg.2, ?_⟩
        intro hEq
        have hmemu : adjoinPhi A g ∈ commSet (fiveProjClass (k + 1) (ε == π) π)
            (QuotientGroup.mk (adjoinRa A)) := by
          rw [commSet_fiveProjClass_eq_image A hk, Set.mem_image]
          exact ⟨g, hg.1, rfl⟩
        exact hsu (hEq ▸ hmemu.2.1)
  have hLR : Subgroup.closure (fiveReflectionsFixing k ε π b'') ≤
      fiveReflectionGroup k ε π :=
    (Subgroup.closure_le (fiveReflectionGroup k ε π)).mpr
      (fun x hx => Subgroup.subset_closure hx.1)
  have hset : (fiveReflectionGroup k ε π).subtype '' S_R =
      fiveReflectionsFixing k ε π b'' := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hx
      exact ⟨⟨x, Subgroup.subset_closure hx.1⟩, hx, rfl⟩
  have hKmap : K.map (fiveReflectionGroup k ε π).subtype =
      Subgroup.closure (fiveReflectionsFixing k ε π b'') := by
    change (Subgroup.closure S_R).map (fiveReflectionGroup k ε π).subtype =
      Subgroup.closure (fiveReflectionsFixing k ε π b'')
    rw [MonoidHom.map_closure, hset]
  have hK_eq : K = (Subgroup.closure (fiveReflectionsFixing k ε π b'')).comap
      (fiveReflectionGroup k ε π).subtype := by
    apply Subgroup.map_subtype_inj.mp
    rw [hKmap, Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLR]
  have hK_mem : ∀ g : fiveReflectionGroup k ε π, g ∈ K ↔
      ((g : GL (Fin (k + 1)) (ZMod 5)) :
          Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ b'' = b'' := by
    intro g
    rw [hK_eq, Subgroup.mem_comap]
    constructor
    · intro h
      exact ((mem_closure_fiveReflectionsFixing_iff hk ε π hb''_ne
        (g : GL (Fin (k + 1)) (ZMod 5))).mp h).2
    · intro h
      exact (mem_closure_fiveReflectionsFixing_iff hk ε π hb''_ne
        (g : GL (Fin (k + 1)) (ZMod 5))).mpr ⟨g.2, h⟩
  have hLHS : (adjoinPhi A).range ⊓ Subgroup.centralizer {QuotientGroup.mk r_b} =
      K.map (adjoinPhi A) := by
    ext x
    rw [Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨⟨g, rfl⟩, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      exact ⟨g, (hK_mem g).mpr ((hfix_iff g).mp hx), rfl⟩
    · rintro ⟨g, hgK, rfl⟩
      refine ⟨⟨g, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hfix_iff g).mpr ((hK_mem g).mp hgK)
  have hRHS : Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π)
        (QuotientGroup.mk (adjoinRa A)) ∩
        commSet (fiveProjClass (k + 1) (ε == π) π) (QuotientGroup.mk r_b)) =
      K.map (adjoinPhi A) := by
    rw [hinter, MonoidHom.map_closure]
  rw [hRange, hLHS, hRHS]

theorem centralizer_eq_hypLineGroup_proj {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {u s : fiveProjective (k + 1) (ε == π) π} (hu : u ∈ fiveProjClass (k + 1) (ε == π) π)
    (hs : s ∈ fiveProjClass (k + 1) (ε == π) π) (hsu : ¬ Commute s u) :
    Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π) u) ⊓ Subgroup.centralizer {s} =
      Subgroup.closure (commSet (fiveProjClass (k + 1) (ε == π) π) u ∩
        commSet (fiveProjClass (k + 1) (ε == π) π) s) := by
  obtain ⟨A⟩ := nonempty_fiveAdjoin k ε π
  have hS := setup_fiveProjClass (n := k + 1) (by omega) (ε == π) π
  have husta : (QuotientGroup.mk (adjoinRa A) : fiveProjective (k + 1) (ε == π) π) ∈
      fiveProjClass (k + 1) (ε == π) π :=
    ⟨adjoinRa A, by rw [coe_adjoinRa]; exact fiveReflOf_mem A.sign_a.1 A.sign_a.2, rfl⟩
  obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj husta hu)
  have h := closure_commSet_inf_centralizer_conj hS.normal g
    (fun t ht htu => centralizer_eq_hypLineGroup_proj_at_adjoinRa hk ε π A ht htu)
    hs (by rw [hg]; exact hsu)
  rwa [hg] at h

end CFSG.OddTranspositions.PartThree

end
