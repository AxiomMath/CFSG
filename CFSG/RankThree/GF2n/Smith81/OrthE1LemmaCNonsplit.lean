module

public import CFSG.RankThree.GF2n.Smith81.OrthE1LemmaCData

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open Module

@[expose] def HasInvComplement {K : Type} [Field K] (S : QSpace K) (V : Submodule K S.E)
    (Xg : Subgroup (S.E ≃ₗ[K] S.E)) : Prop :=
  ∃ V' : Submodule K S.E, IsCompl V V' ∧ ∀ g ∈ Xg, ∀ v ∈ V', g v ∈ V'

namespace LCData

variable {K : Type} [Field K] {S : QSpace K} {V : Submodule K S.E}
  {Xg : Subgroup (S.E ≃ₗ[K] S.E)} (D : LCData S V Xg)

include D

theorem stab {g : S.E ≃ₗ[K] S.E} (hg : g ∈ Xg) {v : S.E} (hv : v ∈ V) : g v ∈ V := by
  have := D.act_coe ⟨g, hg⟩ ⟨v, hv⟩
  rw [← this]
  exact (D.act ⟨g, hg⟩ ⟨v, hv⟩).2

theorem exists_ne_zero : ∃ v ∈ V, v ≠ 0 := by
  have h : 0 < Module.finrank K V := by rw [D.dimV]; norm_num
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp h
  exact ⟨v, v.2, fun h0 => hv (Subtype.ext h0)⟩

theorem stab_of_cent (hns : ¬ HasInvComplement S V Xg) {g : S.E ≃ₗ[K] S.E}
    (hcomm : ∀ x ∈ Xg, ∀ e, x (g e) = g (x e)) : ∀ v ∈ V, g v ∈ V := by
  let a : V →ₗ[K] V := D.β0 ∘ₗ (g : S.E →ₗ[K] S.E) ∘ₗ V.subtype
  obtain ⟨l, hl⟩ := D.schur a (by
    intro x v
    simp only [a, LinearMap.comp_apply, Submodule.subtype_apply, D.act_coe, LinearEquiv.coe_coe]
    rw [← hcomm x x.2, D.β0_act])
  by_cases hl0 : l = 0
  · intro v hv
    have := hl ⟨v, hv⟩
    simp only [a, LinearMap.comp_apply, Submodule.subtype_apply, hl0, zero_smul] at this
    exact (D.β0_eq_zero_iff _).1 this
  · exfalso
    apply hns
    refine ⟨V.map (g : S.E →ₗ[K] S.E), ?_, ?_⟩
    · have hinf : V ⊓ V.map (g : S.E →ₗ[K] S.E) = ⊥ := by
        rw [eq_bot_iff]
        rintro e ⟨hV, w, hw, rfl⟩
        have h1 := hl ⟨w, hw⟩
        simp only [a, LinearMap.comp_apply, Submodule.subtype_apply] at h1
        have h2 : D.β0 ((g : S.E →ₗ[K] S.E) w) = 0 := (D.β0_eq_zero_iff _).2 hV
        rw [h2] at h1
        have h3 : w = 0 := by
          by_contra hne
          have : l • (⟨w, hw⟩ : V) ≠ 0 := smul_ne_zero hl0 (fun h => hne (congrArg Subtype.val h))
          exact this h1.symm
        simp [h3]
      have hfin : Module.finrank K (V.map (g : S.E →ₗ[K] S.E)) = 4 := by
        have := LinearEquiv.finrank_map_eq g V
        rw [← D.dimV]
        exact this
      refine IsCompl.of_eq hinf ?_
      apply Submodule.eq_top_of_finrank_eq
      have h := Submodule.finrank_sup_add_finrank_inf_eq V (V.map (g : S.E →ₗ[K] S.E))
      rw [hinf, finrank_bot, hfin, D.dimV] at h
      rw [D.dimE]
      omega
    · rintro x hx _ ⟨w, hw, rfl⟩
      refine ⟨x w, D.stab hx hw, ?_⟩
      exact (hcomm x hx w).symm

theorem nonsplit_cent [CharP K 2] (hns : ¬ HasInvComplement S V Xg) {g : S.E ≃ₗ[K] S.E}
    (hg : g ∈ S.Cent (Xg : Set (S.E ≃ₗ[K] S.E))) : ∃ c : K, ∀ e, g e = e + c • D.β e := by
  obtain ⟨hgO, hgc⟩ := (S.mem_Cent_iff _ g).1 hg
  have hcomm : ∀ x ∈ Xg, ∀ e, x (g e) = g (x e) := fun x hx => hgc x hx
  have hstab := D.stab_of_cent hns hcomm
  let a : V →ₗ[K] V := (g : S.E →ₗ[K] S.E).restrict hstab
  obtain ⟨μ, hμ⟩ := D.schur a (by
    intro x v
    apply Subtype.ext
    simp only [a, LinearMap.restrict_coe_apply, D.act_coe, LinearEquiv.coe_coe]
    exact (hcomm x x.2 v).symm)
  have hμv : ∀ v ∈ V, g v = μ • v := fun v hv => congrArg Subtype.val (hμ ⟨v, hv⟩)
  have hμ0 : μ ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := D.exists_ne_zero
    intro h
    apply hv0
    have := hμv v hv
    rw [h, zero_smul] at this
    exact g.injective (this.trans (map_zero g).symm)
  have hB : ∀ e, ∀ w ∈ V, S.B (g e) w = μ⁻¹ * S.B e w := by
    intro e w hw
    have h1 := S.B_isometry hgO e w
    rw [hμv w hw, map_smul, smul_eq_mul] at h1
    rw [← h1, ← mul_assoc, inv_mul_cancel₀ hμ0, one_mul]
  let n : S.E →ₗ[K] S.E := (g : S.E →ₗ[K] S.E) - μ⁻¹ • LinearMap.id
  have hn_apply : ∀ e, n e = g e - μ⁻¹ • e := by intro e; simp [n]
  have hn_comm : ∀ (x : ↥Xg) e, n ((x : S.E ≃ₗ[K] S.E) e) = (x : S.E ≃ₗ[K] S.E) (n e) := by
    intro x e
    rw [hn_apply, hn_apply, map_sub, map_smul, hcomm x x.2 e]
  have hn_range : ∀ e, n e ∈ V := by
    intro e
    apply D.perp
    intro w hw
    rw [hn_apply, map_sub, LinearMap.sub_apply, hB e w hw, map_smul, LinearMap.smul_apply,
      smul_eq_mul, sub_self]
  have hn_V : ∀ v ∈ V, n v = (μ - μ⁻¹) • v := by
    intro v hv
    rw [hn_apply, hμv v hv, sub_smul]
  have hμ1 : μ = 1 := by
    by_contra hne
    have hs : μ - μ⁻¹ ≠ 0 := by
      intro h
      apply hne
      have h1 : μ = μ⁻¹ := sub_eq_zero.mp h
      have h2 : μ * μ = 1 := by
        calc μ * μ = μ * μ⁻¹ := by rw [← h1]
          _ = 1 := mul_inv_cancel₀ hμ0
      have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
      have h3 : (μ + 1) ^ 2 = 0 := by linear_combination h2 + μ * h2' + h2'
      have h4 : μ + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
      have h5 : μ = -1 := eq_neg_of_add_eq_zero_left h4
      rw [h5, CharTwo.neg_eq]
    apply hns
    refine ⟨LinearMap.ker n, ?_, ?_⟩
    · refine IsCompl.of_eq ?_ ?_
      · rw [eq_bot_iff]
        rintro e ⟨hV, hk⟩
        have h1 := hn_V e hV
        rw [LinearMap.mem_ker.1 hk] at h1
        have h2 : e = 0 := by
          by_contra h0
          exact smul_ne_zero hs h0 h1.symm
        simp [h2]
      · rw [eq_top_iff]
        intro e _
        have h1 : (μ - μ⁻¹)⁻¹ • n e ∈ V := V.smul_mem _ (hn_range e)
        have h2 : e - (μ - μ⁻¹)⁻¹ • n e ∈ LinearMap.ker n := by
          rw [LinearMap.mem_ker, map_sub, map_smul, hn_V _ (hn_range e), smul_smul,
            inv_mul_cancel₀ hs, one_smul, sub_self]
        exact Submodule.mem_sup.2 ⟨_, h1, _, h2, add_sub_cancel _ _⟩
    · intro x hx w hw
      rw [LinearMap.mem_ker] at hw ⊢
      rw [hn_comm ⟨x, hx⟩ w, hw, map_zero]
  obtain ⟨c, hc⟩ := D.schur_β n hn_comm hn_range (fun v hv => by rw [hn_V v hv, hμ1]; simp)
  refine ⟨c, fun e => ?_⟩
  have h := hc e
  rw [hn_apply, hμ1, inv_one, one_smul] at h
  exact sub_eq_iff_eq_add'.mp h

end LCData

end CFSG.RankThree.GF2n.Smith81.Smith23E1
