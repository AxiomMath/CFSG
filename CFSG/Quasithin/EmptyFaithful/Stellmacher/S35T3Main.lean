module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T3Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T3Cen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T3Idx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T3

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem step3 (hS : Sit H M S) (hII : CaseII H M) (h21 : S35.II.Step21 H M)
    (h6 : S35.II.ClaimS6 H M) : S35.II.Step3 H M := by
  intro hN β hβ x hx hxQ K hK hcen
  obtain ⟨hKn, hVK, -, hKl⟩ := hK
  have hC : x ∈ Cen β K hKn := ⟨hx, fun w hw => hcen w hw⟩
  have hCQ : ¬ Cen β K hKn ≤ pCoreOf 2 (stab β) := fun h => hxQ (h hC)
  obtain ⟨l₀, hl₀⟩ := exists_adj β
  have hl₀ : l₀ ∈ nbrs β := hl₀
  have hl₀S : vtype l₀ = true := Std.vtype_nbr_S5 hβ hl₀
  obtain ⟨δ₀, δ₁, hδ₀, -, hδ₀β, -, -⟩ :=
    Std.exists_two_others hS hl₀S (Std.mem_nbrs_symm.mp hl₀)
  obtain ⟨δ'', -, hδ''β, hδ''δ, hall⟩ :=
    Std.nbrs_S3_third hS hl₀S (Std.mem_nbrs_symm.mp hl₀) hδ₀ (Ne.symm hδ₀β)
  have hQst : ∀ q ∈ Qv β, q ∈ stab β := fun q hq => ((Std.mem_Qv_iff hS β).mp hq).1
  have hQHM : Qv β ≤ H ⊔ M := fun q hq => stab_le β (hQst q hq)
  have horb : ∀ q (hq : q ∈ Qv β), (⟨q, hQHM hq⟩ : ↥(H ⊔ M)) • δ₀ = δ₀ ∨
      (⟨q, hQHM hq⟩ : ↥(H ⊔ M)) • δ₀ = δ'' := by
    intro q hq
    set g : ↥(H ⊔ M) := ⟨q, hQHM hq⟩ with hg
    have hgl : g • l₀ = l₀ := smul_eq_of_mem_stab (Std.Qv_le_stab hS hl₀ hq)
    have hgβ : g • β = β := smul_eq_of_mem_stab (hQst q hq)
    have h1 : g • δ₀ ∈ nbrs l₀ := by
      have := (Std.smul_mem_nbrs_iff' g).mpr hδ₀
      rwa [hgl] at this
    have h2 : g • δ₀ ≠ β := fun h => hδ₀β (MulAction.injective g (h.trans hgβ.symm))
    rcases hall _ h1 with h | h | h
    · exact absurd h h2
    · exact Or.inl h
    · exact Or.inr h
  have hidx := relIndex_stab_le_two hQHM hδ''δ horb
  have hKb : Qv β ⊓ stab δ₀ ≤ Kb β := by
    rintro q ⟨hq, hqδ⟩
    have hA : ∀ l ∈ nbrs β, q ∈ Qv l := by
      intro l hl
      obtain ⟨c, hcC, hcl⟩ := exists_smul_eq_of_normal_not_le hS.glob.amalg hl₀ hl
        (C := Cen β K hKn) (fun g hg => hg.1) (Cen_normal β K hKn) hCQ
      have hlS := Std.vtype_nbr_S5 hβ hl
      have hu : c • δ₀ ∈ nbrs l := by
        have := (Std.smul_mem_nbrs_iff' c).mpr hδ₀
        rwa [hcl] at this
      have hcβ : c • β = β := smul_eq_of_mem_stab hcC.1
      have huβ : c • δ₀ ≠ β := fun h => hδ₀β (MulAction.injective c (h.trans hcβ.symm))
      set q' : ↥(H ⊔ M) := ⟨q, hQHM hq⟩ with hq'
      have hq'δ : q' • δ₀ = δ₀ := smul_eq_of_mem_stab hqδ
      have hq'l : q' • l = l := smul_eq_of_mem_stab (Std.Qv_le_stab hS hl hq)
      have hq'β : q' • β = β := smul_eq_of_mem_stab (hQst q hq)
      have hq'u : q' • c • δ₀ ∈ nbrs l := by
        have := (Std.smul_mem_nbrs_iff' q').mpr hu
        rwa [hq'l] at this
      have hq'uβ : q' • c • δ₀ ≠ β := fun h => huβ (MulAction.injective q' (h.trans hq'β.symm))
      have hc₂ : ((q' * c * q'⁻¹ : ↥(H ⊔ M)) : G) ∈ Cen β K hKn := by
        have := (Subgroup.mem_normalizer_iff.mp (Cen_normal β K hKn (hQst q hq)) (c : G)).mp hcC
        simpa [hq'] using this
      have hc₂δ : (q' * c * q'⁻¹) • δ₀ = q' • c • δ₀ := by
        rw [mul_smul, mul_smul]
        congr 2
        rw [inv_smul_eq_iff]
        exact hq'δ.symm
      have hPz : Pz β K (q' • c • δ₀) = Pz β K (c • δ₀) := by
        rw [← hc₂δ, Pz_smul hVK _ hc₂ δ₀]
        exact (Pz_smul hVK c hcC δ₀).symm
      have hux : q' • c • δ₀ = c • δ₀ := by
        by_contra hne
        exact Pz_ne hS hII h21 hN hβ hl hu hq'u huβ hq'uβ (Ne.symm hne) hVK (hKl l hl).2.1
          hPz.symm
      exact Std.mem_Qv_of_fix_two hS hlS (Std.mem_nbrs_symm.mp hl) hu (Ne.symm huβ)
        (Std.Qv_le_stab hS hl hq) (hQst q hq) (mem_stab_of_smul_eq hux)
    refine ⟨hq, ?_⟩
    show q ∈ Subgroup.centralizer (Vn β : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvc : Vn β ≤ Subgroup.centralizer ({q} : Set G) := by
      unfold Vn
      refine iSup₂_le fun μ hμ z hz => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact Subgroup.mem_centralizer_iff.mp
        (Zv_le_centerOf_Qv hS.glob.amalg μ hz).2 h (hA μ hμ)
    exact (Subgroup.mem_centralizer_iff.mp (hvc hv) q rfl).symm
  have h4 := h6 β hβ
  have h5 : (Kb β).relIndex (Qv β) ≤ (Qv β ⊓ stab δ₀).relIndex (Qv β) :=
    Subgroup.relIndex_le_of_le_left hKb Subgroup.index_ne_zero_of_finite
  omega

end S35.T3

end F53.Stellmacher

end CFSG.Quasithin
