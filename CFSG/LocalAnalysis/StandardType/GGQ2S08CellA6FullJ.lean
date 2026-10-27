module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNJBlock
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNCoords
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNData
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RoNComponents
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellA7Full

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin E6QTwo

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}

theorem ggQ2s08_a6f_jPos
    (hRig : GGLabelRigidInput) {B D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) {labL : LargeEvenLabel}
    (hMark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab = labL))
    (hLab : labL.tag = .twA ∧ labL.rank = 6 ∧ GGLabQTwo 3 labL)
    (hWeyl : GGQ2LabelWeyl labL M.coxeter) (κ : M.V ≃ₗ[ZMod 3] Vn 7) (hκx : κ M.xV = oneN 7)
    (hW : (ggAutomizer L Bs).map (ggQ2CellLin M κ) ≤ permGroup 7) :
    ∃ S : Finset (Fin 7), 5 ≤ S.card ∧ ∀ b : ↥Bs, (b : G) ∈ Subgroup.centralizer (J : Set G) →
      ∀ a ∈ S, ∀ a' ∈ S, κ (M.model (Additive.ofMul b)) a = κ (M.model (Additive.ofMul b)) a' := by
  classical
  have hbasis : ⇑(Pi.basisFun (ZMod 3) (Fin 7)) = fun i : Fin 7 => (Pi.single i 1 : Vn 7) :=
    funext fun i => Pi.basisFun_apply _ _ i
  set f : Fin (6 + 1) → M.V := fun i => κ.symm (Pi.single i 1) with hf
  have hFrame : GGQ2S08ROFrame M f :=
    ggQ2s08_roFrame_of_coords M κ hκx hW (fun i => Pi.single i 1)
      (by rw [← hbasis]; exact (Pi.basisFun (ZMod 3) (Fin 7)).linearIndependent)
      (by rw [← hbasis]; exact (Pi.basisFun (ZMod 3) (Fin 7)).span_eq) (by decide +kernel)
      (fun σ i => permN_single σ i)
  have hWn : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 6).reindex e := by
    have key : ∀ m : ℕ, m = 6 → (∃ e : Fin m ≃ M.Λ, M.coxeter = (CoxeterMatrix.A m).reindex e) →
        ∃ e : Fin 6 ≃ M.Λ, M.coxeter = (CoxeterMatrix.A 6).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hLab.2.1 (by simpa only [GGQ2LabelWeyl, hLab.1] using hWeyl)
  obtain ⟨e, he⟩ := hWn
  obtain ⟨c⟩ := ggQ2s08rN_exists_data hRig (n := 6) le_rfl (by decide) hS M hMark hLab f hFrame
  obtain ⟨w, hw⟩ := c.frame_cmp M (ggQ2s08rN_rootMap_surjective M e he (by decide)) he f hFrame
  obtain ⟨I, hI4, hJ⟩ := c.exists_jBlock hS
  have hJL : J ≤ L := hS.1.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hcen := fun b => c.centralizes_iff_diag (c.hZcop.resolve_right fun h => h.2 ⟨2, rfl⟩)
    (by decide : Even 6) hJL hJ b
  have hco := c.vdiag_eq_iff_coords M κ hκx w hw
  have hdiag : ∀ b : ↥Bs, c.diag b = c.vdiag M (M.model (Additive.ofMul b)) := fun b => by
    rw [GGQ2S08RoN.vdiag, AddEquiv.symm_apply_apply, toMul_ofMul]
  refine ⟨I.map w.symm.toEmbedding, ?_, fun b hb a ha a' ha' => ?_⟩
  swap
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨i', hi', rfl⟩ := Finset.mem_map.mp ha'
    have h1 := (hcen b).mp hb i hi i' hi'
    rw [hdiag] at h1
    exact (hco _ i i').mp h1
  rw [Finset.card_map]
  by_contra hlt
  have hI : I.card = 4 := by omega
  set S : Finset (Fin 7) := I.map w.symm.toEmbedding with hSdef
  have hScard : S.card = 4 := by rw [hSdef, Finset.card_map, hI]
  have hmemS : ∀ i, i ∈ I → w.symm i ∈ S := fun i hi =>
    Finset.mem_map.mpr ⟨i, hi, rfl⟩
  let T := {u : Vn 7 // ∀ a ∈ S, ∀ a' ∈ S, u a = u a'}
  have hTC : Nat.card T ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
    refine Nat.card_le_card_of_injective (fun u => ⟨((Additive.toMul (M.model.symm (κ.symm u.1)) :
      ↥Bs) : G), (Additive.toMul (M.model.symm (κ.symm u.1)) : ↥Bs).2, ?_⟩) ?_
    · refine (hcen _).mpr fun i hi i' hi' => ?_
      rw [hdiag, ofMul_toMul, AddEquiv.apply_symm_apply]
      refine (hco _ i i').mpr ?_
      rw [LinearEquiv.apply_symm_apply]
      exact u.2 _ (hmemS i hi) _ (hmemS i' hi')
    · intro u u' huu
      have h1 : (Additive.toMul (M.model.symm (κ.symm u.1)) : ↥Bs) =
          Additive.toMul (M.model.symm (κ.symm u'.1)) :=
        Subtype.ext (congrArg (fun z : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) => (z : G)) huu)
      have h2 := congrArg (fun z : ↥Bs => κ (M.model (Additive.ofMul z))) h1
      simp only [ofMul_toMul, AddEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h2
      exact Subtype.ext h2
  have hT : 81 ≤ Nat.card T := by
    obtain ⟨s₀, hs₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hinj : Function.Injective (fun p : ({i // i ∉ S} → ZMod 3) × ZMod 3 =>
        (⟨fun i => if h : i ∈ S then p.2 else p.1 ⟨i, h⟩, fun a ha a' ha' => by
          simp only [dif_pos ha, dif_pos ha']⟩ : T)) := by
      rintro ⟨g, α⟩ ⟨g', α'⟩ h
      have h' := congrArg Subtype.val h
      refine Prod.ext (funext fun i => ?_) ?_
      · have := congrFun h' i.1
        simpa only [dif_neg i.2] using this
      · have := congrFun h' s₀
        simpa only [dif_pos hs₀] using this
    have hcard : Nat.card (({i // i ∉ S} → ZMod 3) × ZMod 3) ≤ Nat.card T :=
      Nat.card_le_card_of_injective _ hinj
    have hc : Nat.card (({i // i ∉ S} → ZMod 3) × ZMod 3) = 81 := by
      rw [Nat.card_prod, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hScard]
      norm_num
    omega
  have hle := ggQ2_card_bstar_centralizer_le hS
  omega

end CFSG.StandardType

end
