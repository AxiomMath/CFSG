module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4F
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3CoordC
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13F4GAux1

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin
  CFSG.Open Subgroup Matrix
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem f4g_mem_sup {K K' : Subgroup (MulAut W)}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) {x : MulAut W}
    (hx : x ∈ K ⊔ K') : ∃ a ∈ K, ∃ b ∈ K', a * b = x := by
  let hom : ↥K × ↥K' →* MulAut W :=
    MonoidHom.noncommCoprod K.subtype K'.subtype
      (fun a b => show Commute (K.subtype a) (K'.subtype b) from hKK' a a.2 b b.2)
  have hrange : hom.range = K ⊔ K' := by
    show (MonoidHom.noncommCoprod K.subtype K'.subtype _).range = K ⊔ K'
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hx' : x ∈ hom.range := by rwa [hrange]
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.mp hx'
  exact ⟨p.1, p.1.2, p.2, p.2.2, hp⟩

theorem s134b_tensor_of_irr (hW : ∀ w : W, w ^ 2 = 1) {K K' : Subgroup (MulAut W)}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a) (hL3 : UC22.IsL3 ↥K 1) (hL3' : UC22.IsL3 ↥K' 1)
    {R : Subgroup W} (hcard : Nat.card ↥R = 2 ^ 9) (hirr : IsIrrOn (K ⊔ K') R ⊥)
    (hKnt : ¬ ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r = r)
    (hK'nt : ¬ ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r = r) :
    NatTensor (K ⊔ K') R ⊥ 3 1 := by
  classical
  obtain ⟨I, hnat, hind, hsup, hiso⟩ :=
    s134b_three_summands hW hKK' hL3 hL3' hcard hirr hKnt hK'nt
  obtain ⟨ρ, ψ, hψ⟩ := s16h_e3_l3_coord_of_iso (L := K) hL3 hnat hind hsup 0 hiso
  have hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R :=
    fun k hk r hr => hirr.2.1 k (Subgroup.mem_sup_left hk) r hr
  have hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R :=
    fun k hk r hr => hirr.2.1 k (Subgroup.mem_sup_right hk) r hr
  obtain ⟨σ, hσ⟩ := f4g_sigma_of_coords hKK' hKR hK'R ρ ψ hψ
    (s134b_isSimpleGroup_of_isL3 hL3') (card_eq_of_isL3 hL3') hK'nt
  let hTop : StatedSL 3 (ZMod 2) = ⊤ :=
    le_antisymm le_top (fun x _ => FFC.mem_statedSL_zmod x)
  let ιe : GL (Fin 3) (ZMod 2) ≃* ↥(StatedSL 3 (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop).symm
  have hιe : ∀ δ : GL (Fin 3) (ZMod 2),
      ((ιe δ : ↥(StatedSL 3 (ZMod 2))) : GL (Fin 3) (ZMod 2)) = δ := fun _ => rfl
  let f₁ : ↥(StatedSL 3 (ZMod 2)) →* ↥(K ⊔ K') :=
    (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ K')).comp
      (ρ.symm.toMonoidHom.comp ιe.symm.toMonoidHom)
  let f₂ : ↥(StatedSL 3 (ZMod 2)) →* ↥(K ⊔ K') :=
    (Subgroup.inclusion (le_sup_right : K' ≤ K ⊔ K')).comp
      (σ.symm.toMonoidHom.comp ιe.symm.toMonoidHom)
  have hcomm : ∀ m n, Commute (f₁ m) (f₂ n) := fun m n =>
    Subtype.ext (hKK' (ρ.symm (ιe.symm m) : MulAut W) (ρ.symm (ιe.symm m)).2
      (σ.symm (ιe.symm n) : MulAut W) (σ.symm (ιe.symm n)).2)
  let π : (↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) →* ↥(K ⊔ K') :=
    MonoidHom.noncommCoprod f₁ f₂ hcomm
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨a, ha, b, hb, hab⟩ :=
      f4g_mem_sup hKK' (show (x : MulAut W) ∈ K ⊔ K' from x.2)
    refine ⟨(ιe (ρ ⟨a, ha⟩), ιe (σ ⟨b, hb⟩)), ?_⟩
    rw [MonoidHom.noncommCoprod_apply]
    apply Subtype.ext
    change ((Subgroup.inclusion (le_sup_left : K ≤ K ⊔ K')
        (ρ.symm (ιe.symm (ιe (ρ ⟨a, ha⟩)))) : MulAut W) *
      (Subgroup.inclusion (le_sup_right : K' ≤ K ⊔ K')
        (σ.symm (ιe.symm (ιe (σ ⟨b, hb⟩)))) : MulAut W)) = (x : MulAut W)
    rw [show ιe.symm (ιe (ρ ⟨a, ha⟩)) = ρ ⟨a, ha⟩ from MulEquiv.symm_apply_apply ιe _,
      show ιe.symm (ιe (σ ⟨b, hb⟩)) = σ ⟨b, hb⟩ from MulEquiv.symm_apply_apply ιe _,
      show ρ.symm (ρ ⟨a, ha⟩) = ⟨a, ha⟩ from MulEquiv.symm_apply_apply ρ _,
      show σ.symm (σ ⟨b, hb⟩) = ⟨b, hb⟩ from MulEquiv.symm_apply_apply σ _]
    simp only [Subgroup.coe_inclusion]
    exact hab
  have he : ∀ (γ : ↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2))) (u : ↥R)
      (hu : ((π γ : ↥(K ⊔ K')) : MulAut W) (u : W) ∈ R),
      ψ ⟨((π γ : ↥(K ⊔ K')) : MulAut W) (u : W), hu⟩ =
        tensorAct 3 (ZMod 2) γ (ψ u) := by
    intro γ u hu
    let l : ↥K := ρ.symm (ιe.symm γ.1)
    let k : ↥K' := σ.symm (ιe.symm γ.2)
    have hιe1 : (ιe.symm γ.1 : GL (Fin 3) (ZMod 2)) = (γ.1 : GL (Fin 3) (ZMod 2)) := by
      rw [← hιe (ιe.symm γ.1), ιe.apply_symm_apply]
    have hιe2 : (ιe.symm γ.2 : GL (Fin 3) (ZMod 2)) = (γ.2 : GL (Fin 3) (ZMod 2)) := by
      rw [← hιe (ιe.symm γ.2), ιe.apply_symm_apply]
    have hρl : (ρ l : GL (Fin 3) (ZMod 2)) = ιe.symm γ.1 := by
      show ρ (ρ.symm (ιe.symm γ.1)) = ιe.symm γ.1
      exact ρ.apply_symm_apply (ιe.symm γ.1)
    have hσk : (σ k : GL (Fin 3) (ZMod 2)) = ιe.symm γ.2 := by
      show σ (σ.symm (ιe.symm γ.2)) = ιe.symm γ.2
      exact σ.apply_symm_apply (ιe.symm γ.2)
    have hπγ : (π γ : MulAut W) = (l : MulAut W) * (k : MulAut W) := by
      show ((f₁ γ.1 * f₂ γ.2 : ↥(K ⊔ K')) : MulAut W) = (l : MulAut W) * (k : MulAut W)
      rw [Subgroup.coe_mul]
      rfl
    have hπγ_apply : (π γ : MulAut W) (u : W) =
        (l : MulAut W) ((k : MulAut W) (u : W)) := by
      rw [hπγ, MulAut.mul_apply]
    have hsub : (⟨(π γ : MulAut W) (u : W), hu⟩ : ↥R) =
        ⟨(l : MulAut W) ((k : MulAut W) (u : W)),
          hKR l l.2 _ (hK'R k k.2 (u : W) u.2)⟩ :=
      Subtype.ext hπγ_apply
    have h1 : ψ ⟨(l : MulAut W) ((k : MulAut W) (u : W)),
        hKR l l.2 _ (hK'R k k.2 (u : W) u.2)⟩ =
        Multiplicative.ofAdd ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          Multiplicative.toAdd (ψ ⟨(k : MulAut W) (u : W),
            hK'R k k.2 (u : W) u.2⟩)) :=
      hψ l ((k : MulAut W) (u : W)) (hK'R k k.2 (u : W) u.2)
        (hKR l l.2 _ (hK'R k k.2 (u : W) u.2))
    have h2 : ψ ⟨(k : MulAut W) (u : W), hK'R k k.2 (u : W) u.2⟩ =
        Multiplicative.ofAdd (Multiplicative.toAdd (ψ ⟨(u : W), u.2⟩) *
          ((σ k : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)) :=
      hσ k (u : W) u.2 (hK'R k k.2 (u : W) u.2)
    have h3 : ψ ⟨(π γ : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
          (Multiplicative.toAdd (ψ ⟨(u : W), u.2⟩) *
            ((σ k : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ))) := by
      rw [hsub, h1, h2, toAdd_ofAdd]
    have hρlm : (ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        ((γ.1 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      have h : (ρ l : GL (Fin 3) (ZMod 2)) = (γ.1 : GL (Fin 3) (ZMod 2)) := by
        rw [hρl, hιe1]
      exact congrArg (fun u : GL (Fin 3) (ZMod 2) =>
        (u : Matrix (Fin 3) (Fin 3) (ZMod 2))) h
    have hσkm : ((σ k : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ) =
        (((γ.2 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))ᵀ := by
      have h : (σ k : GL (Fin 3) (ZMod 2)) = (γ.2 : GL (Fin 3) (ZMod 2)) := by
        rw [hσk, hιe2]
      exact congrArg (fun u : GL (Fin 3) (ZMod 2) =>
        ((u : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)) h
    rw [h3, hρlm, hσkm, tensorAct]
    congr 1
    rw [mul_assoc]
  refine ⟨ZMod 2, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Nat.card_zmod]
    decide
  · have hact1 : ∀ γ : ↥(StatedSL 3 (ZMod 2)) × ↥(StatedSL 3 (ZMod 2)),
        tensorAct 3 (ZMod 2) γ 1 = 1 := by
      intro γ
      simp [tensorAct]
    exact ⟨π, S153EB6.realizesVia_of_equiv (tensorAct 3 (ZMod 2)) hact1 π hπ
      (fun h u hu => hirr.2.1 h h.2 u hu) ψ he⟩

end CFSG.LocalAnalysis.WeakClosure81
