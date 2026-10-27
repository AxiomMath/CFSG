module

public import CFSG.ClassicalInvolution.WeakCT.FieldTwo
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogE
public import CFSG.LocalAnalysis.StandardType.FS81.FrameEm
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNative

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.ClassicalInvolution.WeakCT CFSG.LieType CFSG.Timmesfeld

private lemma edgeE_castSucc_iff {n : ℕ} (i j : Fin n) :
    edgeE (n + 1) i.castSucc j.castSucc ↔ edgeE n i j := by
  simp only [edgeE, Fin.coe_castSucc]

theorem weakCT_e7_two_rankOne {X : Type} [Group X] (U : Fin 7 → Subgroup X)
    (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) :
    ∃ Ψ : (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1)) →* X,
      Function.Surjective Ψ ∧ Ψ.ker ≤ Subgroup.center _ ∧
      Subgroup.center X = (Subgroup.center
        (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1))).map Ψ ∧
      ∀ k, (CurtisTits.rankOne
        (Steinberg.Minuscule.e7Datum (GaloisField 2 1)).rootGroup k).map Ψ = U k := by
  have hroot : ∃ c : Fin 7, edgeE 7 ⟨0, by norm_num⟩ c ∨ edgeE 7 c ⟨0, by norm_num⟩ :=
    ⟨⟨2, by norm_num⟩, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
  obtain ⟨ρ, hρ, hψ⟩ :=
    exists_frame_of_tree_two (K := ZMod 2) (Nat.card_zmod 2)
      (rootedTree_edgeE (r := 7) (by norm_num)) hroot hcomm hpair
  obtain ⟨e⟩ : Nonempty (ZMod 2 ≃+* GaloisField 2 1) := by
    have := Fintype.ofFinite (ZMod 2)
    have := Fintype.ofFinite (GaloisField 2 1)
    exact ⟨FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_zmod,
        GaloisField.card 2 1 (by norm_num), pow_one])⟩
  obtain ⟨O⟩ := Steinberg.nonempty_commOrder_ofCartan
    (Steinberg.Minuscule.e7Datum (GaloisField 2 1)).isFiniteType
    (Dv := (Steinberg.Minuscule.e7Datum (GaloisField 2 1)).divisible) rfl
  obtain ⟨h1, h2, h3, h4⟩ := edgeE_orientation (τ := .E7) (Or.inr (Or.inl rfl))
  obtain ⟨x', hD, -⟩ := exists_simplyLacedLevis
    (Steinberg.Minuscule.e7_chevalleyExtras (GaloisField 2 1) O _
      (Steinberg.Minuscule.e7Data_valid.commutatorFormula_commC (GaloisField 2 1)
        Steinberg.Minuscule.posDef_cartan_E7 _
        (Steinberg.Minuscule.roots_eq Steinberg.Minuscule.isFiniteType_cartan_E7) O))
    rfl (fun α _ β _ _ _ =>
      Steinberg.Minuscule.e7Data_valid.commC_natAbs (GaloisField 2 1) α β (1, 1)) h1 h2 h3 h4
    (Steinberg.Minuscule.e7Datum_steinbergExtras (GaloisField 2 1)).torus_iSupIndep
    (fun (k : Fin 7) => by
      have h := (Steinberg.Minuscule.e7Datum_isCTGroupDatum (GaloisField 2 1)).sq_mem k
      have he := Steinberg.Minuscule.e7Data_valid.weylElement_xm (GaloisField 2 1) k 1
      rw [he]
      exact h)
  obtain ⟨Ψ, hsurj, hker, -, hcent, -, hrank⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.weakCT_of_frame_of_equiv e
    (CurtisTits.curtisTitsConclusion_e7 2 1 ⟨Nat.prime_two, le_rfl, rfl⟩)
    (leviConePresented_e7 _) hD (⟨0, by norm_num⟩ : Fin 7) hgen hcomm hρ hψ
  exact ⟨Ψ, hsurj, hker, hcent, hrank⟩

theorem exists_mulEquiv_L7_frame (hnat : E7Frame.E7NatFrame) {X : Type} [Group X]
    (U : Fin 7 → Subgroup X) (hgen : ⨆ k, U k = ⊤)
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j))
    (hZ : Subgroup.center X = ⊥) :
    ∃ φ : X ≃* ↥E7Frame.L7,
      ∀ k, (U k).map φ.toMonoidHom = (E7Frame.Jn k).subgroupOf E7Frame.L7 := by
  unfold E7Frame.E7NatFrame at hnat
  obtain ⟨hle, hcomm8, hpair8, hgen8⟩ := hnat
  have hcommV : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ a ∈ (E7Frame.Jn i).subgroupOf E7Frame.L7,
        ∀ b ∈ (E7Frame.Jn j).subgroupOf E7Frame.L7, a * b = b * a := by
    intro i j hij h1 h2 a ha b hb
    exact Subtype.ext (hcomm8 i j hij
      (fun h => h1 ((edgeE_castSucc_iff i j).mp h))
      (fun h => h2 ((edgeE_castSucc_iff j i).mp h))
      a.1 (Subgroup.mem_subgroupOf.mp ha) b.1 (Subgroup.mem_subgroupOf.mp hb))
  have hpairV : ∀ i j : Fin 7, edgeE 7 i j →
      ∃ W, LinearBlockStandardPair (ZMod 2) W
        ((E7Frame.Jn i).subgroupOf E7Frame.L7) ((E7Frame.Jn j).subgroupOf E7Frame.L7) := by
    intro i j hij
    obtain ⟨W, hW⟩ := hpair8 i j ((edgeE_castSucc_iff i j).mpr hij)
    exact ⟨W.subgroupOf E7Frame.L7, linearBlockStandardPair_subgroupOf (hle i) (hle j) hW⟩
  have hgenV : ⨆ k, (E7Frame.Jn k).subgroupOf E7Frame.L7 = ⊤ := by
    apply Subgroup.map_injective (f := E7Frame.L7.subtype) E7Frame.L7.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp_rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hle _)]
    exact le_antisymm (iSup_le hle) (hgen8 _ fun k => le_iSup (fun k => E7Frame.Jn k) k)
  obtain ⟨Ψ', hsurj', hker', hcent', hrank'⟩ :=
    weakCT_e7_two_rankOne (fun k => (E7Frame.Jn k).subgroupOf E7Frame.L7) hgenV hcommV hpairV
  obtain ⟨Ψ, hsurj, hker, hcent, hrank⟩ := weakCT_e7_two_rankOne U hgen hcomm hpair
  have hZ7 : Subgroup.center ↥E7Frame.L7 = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := ZMod 2)
  have hmapX : (Subgroup.center
      (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1))).map Ψ = ⊥ := by
    rw [← hcent, hZ]
  have hmapL : (Subgroup.center
      (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1))).map Ψ' = ⊥ := by
    rw [← hcent', hZ7]
  have hkerX : Ψ.ker = Subgroup.center
      (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1)) :=
    le_antisymm hker ((Subgroup.map_eq_bot_iff (f := Ψ) (Subgroup.center _)).1 hmapX)
  have hkerL : Ψ'.ker = Subgroup.center
      (Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 2 1)) :=
    le_antisymm hker' ((Subgroup.map_eq_bot_iff (f := Ψ') (Subgroup.center _)).1 hmapL)
  have hker_le : Ψ.ker ≤ Ψ'.ker := (le_of_eq hkerX).trans (le_of_eq hkerL.symm)
  have hker_ge : Ψ'.ker ≤ Ψ.ker := (le_of_eq hkerL).trans (le_of_eq hkerX.symm)
  set F : X →* ↥E7Frame.L7 := (MonoidHom.liftOfSurjective Ψ hsurj) ⟨Ψ', hker_le⟩ with hF
  have hcomp : F.comp Ψ = Ψ' := by
    rw [hF, MonoidHom.liftOfSurjective]
    rw [MonoidHom.liftOfRightInverse_comp]
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨a, rfl⟩ := hsurj' y
    exact ⟨Ψ a, DFunLike.congr_fun hcomp a⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨b, rfl⟩ := hsurj y
    have h1 : F (Ψ a) = Ψ' a := DFunLike.congr_fun hcomp a
    have h2 : F (Ψ b) = Ψ' b := DFunLike.congr_fun hcomp b
    have hab : Ψ' a = Ψ' b := by rw [← h1, ← h2, hxy]
    have hmem' : a⁻¹ * b ∈ Ψ'.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    have hmem : a⁻¹ * b ∈ Ψ.ker := hker_ge hmem'
    have hab2 : Ψ a = Ψ b := by
      have h := hmem
      simp only [MonoidHom.mem_ker, map_mul, map_inv] at h
      exact inv_mul_eq_one.mp h
    exact hab2
  set φ : X ≃* ↥E7Frame.L7 := MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩ with hφdef
  have hφΨ : ∀ a, φ (Ψ a) = Ψ' a := by
    intro a
    rw [hφdef]
    change F (Ψ a) = Ψ' a
    exact DFunLike.congr_fun hcomp a
  have hcompφ : φ.toMonoidHom.comp Ψ = Ψ' := by
    apply MonoidHom.ext
    intro a
    change φ (Ψ a) = Ψ' a
    exact hφΨ a
  refine ⟨φ, fun k => ?_⟩
  calc (U k).map φ.toMonoidHom
      = ((CurtisTits.rankOne
          (Steinberg.Minuscule.e7Datum (GaloisField 2 1)).rootGroup k).map Ψ).map
            φ.toMonoidHom := by rw [hrank k]
    _ = (CurtisTits.rankOne
          (Steinberg.Minuscule.e7Datum (GaloisField 2 1)).rootGroup k).map
            (φ.toMonoidHom.comp Ψ) := by rw [Subgroup.map_map]
    _ = (CurtisTits.rankOne
          (Steinberg.Minuscule.e7Datum (GaloisField 2 1)).rootGroup k).map Ψ' := by
          rw [hcompφ]
    _ = (E7Frame.Jn k).subgroupOf E7Frame.L7 := hrank' k

end CFSG.StandardType.FrameRoute.FS81
