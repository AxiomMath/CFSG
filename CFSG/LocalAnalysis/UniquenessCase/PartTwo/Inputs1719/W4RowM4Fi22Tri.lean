module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4Z3Inner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFi22Pack
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCover
public import CFSG.Sporadic.FischerOddCore.Fi22Unitary
public import CFSG.Sporadic.Bridge.Fi22Surj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Fi22ExactCover
import all CFSG.Sporadic.Presentation.Fi22ExactCover
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.Fi22
open CFSG.Sporadic.Bridge.TwoGen (img2)
open CFSG.Sporadic.Presentation.Fi22Exact
open CFSG.Sporadic.Fi22 (a b J closure_ab)

private theorem m4_lift_W0 :
    ∀ r ∈ {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk},
      FreeGroup.lift (fun i : Fin gc => img2 a b i.val) r = 1 := by
  intro r hr
  change r ∈ W0.map FreeGroup.mk at hr
  rw [List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [lift_mk TauCeti.SporadicName.Fi22.presentation (img2 a b) w]
  exact relators_eval _ (by
    rw [TauCeti.GroupPresentation.relatorLetters_def, List.mem_map]
    exact ⟨w, hw, rfl⟩)

private noncomputable def m4_g :
    GG →* J :=
  PresentedGroup.toGroup (f := fun i : Fin gc => img2 a b i.val) m4_lift_W0

private theorem m4_g_of (i : Fin gc) :
    m4_g (PresentedGroup.of i) = img2 a b i.val := by
  simp only [m4_g, PresentedGroup.toGroup.of]

private theorem m4_g_aG :
    m4_g aG = a := by
  change m4_g (PresentedGroup.of ga) = a
  rw [m4_g_of]
  simp [img2, ga]

private theorem m4_g_bG :
    m4_g bG = b := by
  change m4_g (PresentedGroup.of gb) = b
  rw [m4_g_of]
  simp [img2, gb]

private theorem m4_g_xG (k : ℕ) :
    m4_g (xG k) = (b ^ k)⁻¹ * a * b ^ k := by
  change m4_g ((bG ^ k)⁻¹ * aG * bG ^ k) = (b ^ k)⁻¹ * a * b ^ k
  simp only [map_mul, map_inv, map_pow, m4_g_aG, m4_g_bG]

private theorem m4_g_surjective :
    Function.Surjective m4_g := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab, Subgroup.closure_le]
  rintro g (h | h)
  · exact ⟨PresentedGroup.of ga, by
      rw [m4_g_of, h]
      simp [img2, ga]⟩
  · rw [Set.mem_singleton_iff] at h
    exact ⟨PresentedGroup.of gb, by
      rw [m4_g_of, h]
      simp [img2, gb]⟩

private theorem m4_closure_xG :
    Subgroup.closure (Set.range fun l : Fin 6 => xG l.val) = ⊤ := by
  have h := MonoidHom.map_closure thetaHom (Set.range (fun l : Fin 6 => PresentedGroup.of l))
  rw [PresentedGroup.closure_range_of, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr thetaHom_surjective] at h
  rw [← Set.range_comp thetaHom (fun l : Fin 6 => PresentedGroup.of l)] at h
  simp only [Function.comp_def] at h
  have hcomp : (fun l : Fin 6 => thetaHom (PresentedGroup.of l)) =
      (fun l : Fin 6 => xG l.val) := funext fun l => thetaHom_of l
  rw [hcomp] at h
  exact h.symm

private theorem m4_closure_range_equiv {G H ι : Type*} [Group G] [Group H] (e : G ≃* H)
    (f : ι → G) (hf : Subgroup.closure (Set.range f) = ⊤) :
    Subgroup.closure (Set.range fun i => (e : G →* H) (f i)) = ⊤ := by
  have h := MonoidHom.map_closure (e : G →* H) (Set.range f)
  rw [hf, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective] at h
  rw [← Set.range_comp (e : G →* H) f] at h
  simpa only [Function.comp_def] using h.symm

private theorem m4_witness_of_map {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') (s : S) :
    InvolutionWitness (e s) → InvolutionWitness s := by
  rintro (h | h | h)
  · obtain ⟨c, hc⟩ := h
    refine Or.inl ⟨e.symm c, ?_⟩
    have h1 : e (s * (e.symm c * s * (e.symm c)⁻¹)) = e s * (c * e s * c⁻¹) := by
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    rwa [← h1, MulEquiv.orderOf_eq] at hc
  · obtain ⟨c, g, hc, hg⟩ := h
    refine Or.inr (Or.inl ⟨e.symm c, e.symm g, ?_, ?_⟩)
    · have h1 : e (s * (e.symm c * s * (e.symm c)⁻¹)) = e s * (c * e s * c⁻¹) := by
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      rwa [← h1, MulEquiv.orderOf_eq] at hc
    · apply e.injective
      simp only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply]
      exact hg
  · obtain ⟨cs, hlen, hcl⟩ := h
    refine Or.inr (Or.inr ⟨cs.map e.symm, by simpa using hlen, ?_⟩)
    have h := MonoidHom.map_closure (e.symm : S' →* S) {v : S' | ∃ c ∈ cs, v = c * e s * c⁻¹}
    rw [hcl, Subgroup.map_top, MulEquiv.range_eq_top e.symm] at h
    change ⊤ = Subgroup.closure (e.symm '' {v : S' | ∃ c ∈ cs, v = c * e s * c⁻¹}) at h
    have hset : e.symm '' {v : S' | ∃ c ∈ cs, v = c * e s * c⁻¹} =
        {v : S | ∃ c ∈ cs.map e.symm, v = c * s * c⁻¹} := by
      ext v
      constructor
      · rintro ⟨w, ⟨c, hc, rfl⟩, rfl⟩
        exact ⟨e.symm c, List.mem_map_of_mem hc, by
          simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]⟩
      · rintro ⟨c, hc, rfl⟩
        rw [List.mem_map] at hc
        obtain ⟨c₀, hc₀, rfl⟩ := hc
        exact ⟨c₀ * e s * c₀⁻¹, ⟨c₀, hc₀, rfl⟩, by
          simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]⟩
    rw [hset] at h
    exact h.symm

theorem fi22_sixGen :
    ∃ gs : List ↥fi22P, gs.length ≤ 6 ∧
      Subgroup.closure {v : ↥fi22P | ∃ d ∈ gs, v = d * fi22OuterZP * d⁻¹} = ⊤ := by
  have hJ : Subgroup.closure (Set.range fun l : Fin 6 => (b ^ l.val)⁻¹ * a * b ^ l.val) = ⊤ := by
    have h := MonoidHom.map_closure m4_g (Set.range fun l : Fin 6 => xG l.val)
    rw [m4_closure_xG, Subgroup.map_top, MonoidHom.range_eq_top.mpr m4_g_surjective] at h
    rw [← Set.range_comp m4_g (fun l : Fin 6 => xG l.val)] at h
    simp only [Function.comp_def] at h
    have hcomp : (fun l : Fin 6 => m4_g (xG l.val)) =
        (fun l : Fin 6 => (b ^ l.val)⁻¹ * a * b ^ l.val) := funext fun l => m4_g_xG l.val
    rw [hcomp] at h
    exact h.symm
  let c : Fin 6 → ↥fi22P := fun l => (fi22PJ.symm : J →* ↥fi22P) ((b ^ l.val)⁻¹)
  have hP : Subgroup.closure (Set.range fun l : Fin 6 => c l * fi22Ya * (c l)⁻¹) = ⊤ := by
    have h := @m4_closure_range_equiv J ↥fi22P (Fin 6) inferInstance inferInstance
      fi22PJ.symm (fun l : Fin 6 => (b ^ l.val)⁻¹ * a * b ^ l.val) hJ
    have hcomp : (fun l : Fin 6 =>
        (fi22PJ.symm : J →* ↥fi22P) ((b ^ l.val)⁻¹ * a * b ^ l.val)) =
        (fun l : Fin 6 => c l * fi22Ya * (c l)⁻¹) := by
      funext l
      show (fi22PJ.symm : J →* ↥fi22P) ((b ^ l.val)⁻¹ * a * b ^ l.val) =
        c l * fi22Ya * (c l)⁻¹
      rw [show fi22Ya = (fi22PJ.symm : J →* ↥fi22P) a from rfl]
      simp only [c, map_mul, map_inv, inv_inv]
    rw [hcomp] at h
    exact h
  obtain ⟨r, hr⟩ := isConj_iff.1 isConj_fi22OuterZP_fi22Ya
  refine ⟨(List.finRange 6).map (fun l => c l * r), by simp, ?_⟩
  have hgen : (fun l : Fin 6 => c l * fi22Ya * (c l)⁻¹) =
      (fun l : Fin 6 => (c l * r) * fi22OuterZP * (c l * r)⁻¹) := by
    funext l
    rw [← hr]
    group
  have hds : Subgroup.closure (Set.range fun l : Fin 6 =>
      (c l * r) * fi22OuterZP * (c l * r)⁻¹) = ⊤ := by
    rw [← hgen]
    exact hP
  have hset : {v : ↥fi22P | ∃ d ∈ (List.finRange 6).map (fun l => c l * r),
      v = d * fi22OuterZP * d⁻¹} =
      Set.range (fun l : Fin 6 => (c l * r) * fi22OuterZP * (c l * r)⁻¹) := by
    ext v
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [List.mem_map] at hd
      obtain ⟨l, -, rfl⟩ := hd
      exact ⟨l, rfl⟩
    · rintro ⟨l, rfl⟩
      exact ⟨c l * r, List.mem_map_of_mem (List.mem_finRange l), rfl⟩
  rw [hset, hds]

theorem fi22_involutionWitness :
    ∀ s : CFSG.Blueprint.NativeSporadic.Fi22, s * s = 1 → s ≠ 1 → InvolutionWitness s := by
  intro s hs2 hsne
  refine @m4_witness_of_map CFSG.Blueprint.NativeSporadic.Fi22 ↥fi22P inferInstance
    inferInstance fi22PermEquiv s ?_
  set s' : ↥fi22P := fi22PermEquiv s with hs'_def
  have hs'2 : s' * s' = 1 := by
    rw [hs'_def, ← map_mul, hs2, map_one]
  have hs'ne : s' ≠ 1 := by
    intro h
    apply hsne
    apply fi22PermEquiv.injective
    rw [← hs'_def, h, map_one]
  have hτ2 : orderOf (s' : Equiv.Perm (Fin 3510)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hs'2) hs'ne
  obtain ⟨k, hk6, r, hrR, hrconj⟩ := fi22R_involution_conj (fi22P_le_R s'.2) hτ2
  have hk3 : k < 3 := by
    by_contra h
    have hk3' : 3 ≤ k := not_lt.1 h
    have hnotmem : fi22ExtRep k ∉ fi22P := by
      have := (CTUC_Fi22_all_extension_involutions_covered.2.1 (k - 3) (by omega)).2
      rwa [show 3 + (k - 3) = k from by omega] at this
    have hmem : r * (s' : Equiv.Perm (Fin 3510)) * r⁻¹ ∈ fi22P :=
      (Subgroup.mem_normalizer_iff.1 (fi22R_le_normalizer hrR)
        (s' : Equiv.Perm (Fin 3510))).1 s'.2
    rw [hrconj] at hmem
    exact hnotmem hmem
  have hkP : fi22ExtRep k ∈ fi22P := CTUC_Fi22_all_extension_involutions_covered.1 k hk3
  let t : ↥fi22P := ⟨fi22ExtRep k, hkP⟩
  have hwit_t : InvolutionWitness t := by
    interval_cases k
    · obtain ⟨c0, hc0P, hc0⟩ := fi22_ext_dihedral.1
      refine Or.inl ⟨⟨c0, hc0P⟩, ?_⟩
      rw [← Subgroup.orderOf_coe]
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, t] using hc0
    · obtain ⟨c1, hc1P, hc1ord, g1, hg1P, hg1conj⟩ := fi22_ext_five
      refine Or.inr (Or.inl ⟨⟨c1, hc1P⟩, ⟨g1, hg1P⟩, ?_, ?_⟩)
      · rw [← Subgroup.orderOf_coe]
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, t] using hc1ord
      · apply Subtype.ext
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, t] using hg1conj
    · obtain ⟨gs, hdslen, hdscl⟩ := fi22_sixGen
      refine Or.inr (Or.inr ⟨gs, hdslen, ?_⟩)
      have ht : t = fi22OuterZP := Subtype.ext fi22ExtRep_two
      rw [ht]
      exact hdscl
  have hconj : fi22ConjHom ⟨r, hrR⟩ s' = t := by
    apply Subtype.ext
    rw [fi22ConjHom_apply]
    exact hrconj
  exact @m4_witness_of_map ↥fi22P ↥fi22P inferInstance inferInstance (fi22ConjHom ⟨r, hrR⟩) s'
    (hconj ▸ hwit_t)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
