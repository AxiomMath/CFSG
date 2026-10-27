module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Statement
import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86FpfAlg
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86FpfGen
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps86Tools

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv Equiv.Perm

section Aux

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 10)}

private def diagAlt (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) :
    alternatingGroup (Fin 5) →* alternatingGroup (Fin 10) :=
  ((diagHom e).comp (alternatingGroup (Fin 5)).subtype).codRestrict (alternatingGroup (Fin 10))
    fun σ => diagHom_mem_alternatingGroup e σ.2

private theorem permCongr_sumComm_mul_self (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) :
    e.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) * e.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) =
      1 := by
  rw [← Equiv.permCongr_mul]
  ext y
  simp

private theorem not_card_alternatingGroup_five_dvd :
    ¬ Nat.card (alternatingGroup (Fin 5)) ∣ 168 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

private theorem index_conj (k t : ↥H) :
    (fixV (Subgroup.zpowers ((k * t * k⁻¹ : ↥H) : MulAut V))).index =
      (fixV (Subgroup.zpowers (t : MulAut V))).index :=
  FixVLat.index_fixV_zpowers_conj (k : MulAut V) (t : MulAut V)

private theorem mem_fixV_altPre_of_diag (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 10) ≤ ψ.range) {e₁ e₂ : Fin 5 ⊕ Fin 5 ≃ Fin 10}
    (hgen : alternatingGroup (Fin 10) ≤ Subgroup.closure
      (diagHom e₁ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) ∪
        diagHom e₂ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5)))))
    {w : V} (h₁ : ∀ σ : alternatingGroup (Fin 5), altRho hψ hA (diagAlt e₁ σ) w = w)
    (h₂ : ∀ σ : alternatingGroup (Fin 5), altRho hψ hA (diagAlt e₂ σ) w = w) :
    w ∈ fixV (altPre ψ) := by
  have hmap : ∀ (e : Fin 5 ⊕ Fin 5 ≃ Fin 10),
      (∀ σ : alternatingGroup (Fin 5), altRho hψ hA (diagAlt e σ) w = w) →
      ∀ σ : alternatingGroup (Fin 5),
        diagHom e σ ∈ ((MulAction.stabilizer (MulAut V) w).comap H.subtype).map ψ :=
    fun e h σ => ⟨⟨altRho hψ hA (diagAlt e σ), altRho_mem hψ hA _⟩,
      by simpa [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] using h σ,
      apply_altRho hψ hA (diagAlt e σ)⟩
  have hle : alternatingGroup (Fin 10) ≤
      ((MulAction.stabilizer (MulAut V) w).comap H.subtype).map ψ := by
    refine hgen.trans (Subgroup.closure_le _ |>.mpr ?_)
    rintro _ (⟨σ, hσ, rfl⟩ | ⟨σ, hσ, rfl⟩)
    · exact hmap e₁ h₁ ⟨σ, hσ⟩
    · exact hmap e₂ h₂ ⟨σ, hσ⟩
  intro x hx
  obtain ⟨hxH, hxA⟩ := mem_altPre_iff.mp hx
  obtain ⟨y, hy, hyx⟩ := hle hxA
  obtain rfl : y = ⟨x, hxH⟩ := hψ hyx
  simpa [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, MulAut.smul_def] using hy

private theorem altRho_diagAlt_commute (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 10) ≤ ψ.range) (e : Fin 5 ⊕ Fin 5 ≃ Fin 10) {s : ↥H}
    (hs : ψ s = e.permCongr (Equiv.sumComm (Fin 5) (Fin 5))) (σ : alternatingGroup (Fin 5)) :
    altRho hψ hA (diagAlt e σ) * (s : MulAut V) = (s : MulAut V) * altRho hψ hA (diagAlt e σ) := by
  have h : (⟨altRho hψ hA (diagAlt e σ), altRho_mem hψ hA _⟩ : ↥H) * s =
      s * ⟨altRho hψ hA (diagAlt e σ), altRho_mem hψ hA _⟩ := by
    refine hψ ?_
    rw [map_mul, map_mul, apply_altRho hψ hA, hs]
    exact diagHom_commute e σ
  exact congrArg Subtype.val h

private theorem ti_of_diag [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 10) ≤ ψ.range) (hfix : fixV (altPre ψ) = ⊥)
    {e₁ e₂ : Fin 5 ⊕ Fin 5 ≃ Fin 10}
    (hgen : alternatingGroup (Fin 10) ≤ Subgroup.closure
      (diagHom e₁ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5))) ∪
        diagHom e₂ '' (alternatingGroup (Fin 5) : Set (Perm (Fin 5)))))
    {s₁ s₂ : ↥H} (h₁ : ψ s₁ = e₁.permCongr (Equiv.sumComm (Fin 5) (Fin 5)))
    (h₂ : ψ s₂ = e₂.permCongr (Equiv.sumComm (Fin 5) (Fin 5)))
    (hi₁ : (fixV (Subgroup.zpowers (s₁ : MulAut V))).index ≤ 8)
    (hi₂ : (fixV (Subgroup.zpowers (s₂ : MulAut V))).index ≤ 8) (x y : V)
    (hxy : x * (s₁ : MulAut V) x = y * (s₂ : MulAut V) y) : x * (s₁ : MulAut V) x = 1 := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hX : ∀ v : V, v⁻¹ = v := fun v =>
    inv_eq_of_mul_eq_one_right (by simpa [sq] using hV v)
  have hmem : ∀ (s : MulAut V) (u : V), u * s u ∈ commV (Subgroup.zpowers s) := fun s u => by
    have h : s u * u⁻¹ ∈ commV (Subgroup.zpowers s) :=
      Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, u, rfl⟩
    rwa [hX u, mul_comm] at h
  have hsq : ∀ {s : ↥H} {e : Fin 5 ⊕ Fin 5 ≃ Fin 10},
      ψ s = e.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) → (s : MulAut V) ^ 2 = 1 :=
    fun {s e} hs => by
      have h : s * s = 1 := hψ (by rw [map_mul, hs, permCongr_sumComm_mul_self, map_one])
      rw [sq]
      exact congrArg Subtype.val h
  have hw : x * (s₁ : MulAut V) x ∈ fixV (altPre ψ) := by
    refine mem_fixV_altPre_of_diag hψ hA hgen (fun σ => ?_) (fun σ => ?_)
    · exact centralizes_commV_of_simple hV not_card_alternatingGroup_five_dvd
        ((altRho hψ hA).comp (diagAlt e₁)) (hsq h₁) (altRho_diagAlt_commute hψ hA e₁ h₁) hi₁ σ
        (hmem _ x)
    · rw [hxy]
      exact centralizes_commV_of_simple hV not_card_alternatingGroup_five_dvd
        ((altRho hψ hA).comp (diagAlt e₂)) (hsq h₂) (altRho_diagAlt_commute hψ hA e₂ h₂) hi₂ σ
        (hmem _ y)
  rw [hfix] at hw
  exact Subgroup.mem_bot.mp hw

private theorem fpfP_mul_fpfT_mul_fpfP : fpfP * fpfT * fpfP = fpfT * (fpfT * fpfP) ^ 2 := by
  decide +kernel

private theorem fpfT_mul_fpfP_mul_fpfT : fpfT * fpfP * fpfT = fpfP * (fpfT * fpfP) ^ 2 := by
  decide +kernel

private theorem false_of_fpfT_fpfP [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hA : alternatingGroup (Fin 10) ≤ ψ.range)
    (hfix : fixV (altPre ψ) = ⊥) {t p : ↥H} (ht : ψ t = fpfT) (hp : ψ p = fpfP)
    (hit : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8)
    (hip : (fixV (Subgroup.zpowers (p : MulAut V))).index ≤ 8) : False := by
  have htt : t * t = 1 := hψ (by rw [map_mul, ht, fpfT_mul_self, map_one])
  have hpp : p * p = 1 := hψ (by rw [map_mul, hp, fpfP_mul_self, map_one])
  have h4 : (t * p) ^ 4 = 1 :=
    hψ (by rw [map_pow, map_mul, ht, hp, fpfT_mul_fpfP_pow_four, map_one])
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hpp
  have hi₂ : (fixV (Subgroup.zpowers ((p * t * p : ↥H) : MulAut V))).index ≤ 8 := by
    have e : p * t * p = p * t * p⁻¹ := by rw [hpi]
    rw [e]
    exact (index_conj p t).trans_le hit
  have hi₄ : (fixV (Subgroup.zpowers ((t * p * t : ↥H) : MulAut V))).index ≤ 8 := by
    have e : t * p * t = t * p * t⁻¹ := by rw [hti]
    rw [e]
    exact (index_conj t p).trans_le hip
  have hs₁ : ψ t = fpfLab₁.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) := by
    rw [fpfLab₁_swap, ht]
  have hs₂ : ψ (p * t * p) = fpfLab₂.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) := by
    rw [fpfLab₂_swap, map_mul, map_mul, ht, hp, fpfP_mul_fpfT_mul_fpfP]
  have hs₃ : ψ p = fpfLab₃.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) := by
    rw [fpfLab₃_swap, hp]
  have hs₄ : ψ (t * p * t) = fpfLab₄.permCongr (Equiv.sumComm (Fin 5) (Fin 5)) := by
    rw [fpfLab₄_swap, map_mul, map_mul, ht, hp, fpfT_mul_fpfP_mul_fpfT]
  have hX : ∀ x : V, x * x = 1 := fun x => by simpa [sq] using hV x
  have hd8 : ((t : MulAut V) * p) ^ 2 = 1 :=
    d8_trivial hX (t : MulAut V) (p : MulAut V) (congrArg Subtype.val htt)
      (congrArg Subtype.val hpp) (by simpa using congrArg Subtype.val h4)
      (fun x y hxy => ti_of_diag hV hψ hA hfix alternatingGroup_le_closure_diag₁₂ hs₁ hs₂ hit hi₂
        x y hxy)
      (fun x y hxy => ti_of_diag hV hψ hA hfix alternatingGroup_le_closure_diag₃₄ hs₃ hs₄ hip hi₄
        x y hxy)
  have hd8' : (t * p) ^ 2 = 1 := Subtype.ext (by simpa using hd8)
  exact fpfT_mul_fpfP_sq_ne_one (by rw [← ht, ← hp, ← map_mul, ← map_pow, hd8', map_one])

end Aux

theorem false_of_fpf_ten {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {ψ : ↥H →* Perm (Fin 10)} (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin 10) ≤ ψ.range) (hfix : fixV (altPre ψ) = ⊥) {t : ↥H}
    (ht : t ^ 2 = 1) (htf : ∀ i, ψ t i ≠ i)
    (hidx : (fixV (Subgroup.zpowers (t : MulAut V))).index ≤ 8) : False := by
  have hts : ψ t * ψ t = 1 := by rw [← map_mul, ← sq, ht, map_one]
  obtain ⟨g, hg, hgt⟩ := exists_conj_eq_fpfT hts htf
  obtain ⟨k, hk⟩ := hA hg
  have ht₁ : ψ (k * t * k⁻¹) = fpfT := by rw [map_mul, map_mul, map_inv, hk]; exact hgt
  obtain ⟨g', hg', hgp⟩ := exists_conj_fpfT_eq_fpfP
  obtain ⟨k', hk'⟩ := hA hg'
  have hp : ψ (k' * (k * t * k⁻¹) * k'⁻¹) = fpfP := by
    rw [map_mul, map_mul, map_inv, hk', ht₁]
    exact hgp
  exact false_of_fpfT_fpfP hV hψ hA hfix ht₁ hp ((index_conj k t).trans_le hidx)
    (((index_conj k' (k * t * k⁻¹)).trans (index_conj k t)).trans_le hidx)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
