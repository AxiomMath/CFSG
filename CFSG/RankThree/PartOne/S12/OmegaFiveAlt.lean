module

public import CFSG.RankThree.PartOne.LIT.KF126

public section

namespace CFSG.RankThree.PartOne

namespace OmegaAlt

open Matrix Equiv CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.LIT

@[expose] def altA : Perm (Fin 5) := swap 2 3 * swap 3 4

@[expose] def altB : Perm (Fin 5) := finRotate 5

@[expose] def genP (b : Bool) : Perm (Fin 5) := if b then altB else altA

@[expose] def evalP (w : List Bool) : Perm (Fin 5) := w.foldl (fun acc b => acc * genP b) 1

theorem step_table : ∀ w ∈ Lwords, ∀ b : Bool, ∃ w' ∈ Lwords,
    evalR w' = R3.mul (evalR w) (genR b) ∧ evalP w' = evalP w * genP b := by
  decide +kernel

theorem one_table : ∀ w ∈ Lwords, evalP w = 1 → evalR w = R3.one := by
  decide +kernel

theorem even_table : ∀ w ∈ Lwords, Perm.sign (evalP w) = 1 := by
  decide +kernel

theorem exists_word (x : Kfive) : ∃ w ∈ Lwords, evalR w = R3.ofM (x.1 : M3) := by
  have h : R3.ofM (x.1 : M3) ∈ Lwords.map evalR := ofM_mem_Lr x.2
  obtain ⟨w, hw, hwe⟩ := List.mem_map.mp h
  exact ⟨w, hw, hwe⟩

theorem word_unique {w w' : List Bool} (hw : w ∈ Lwords) (hw' : w' ∈ Lwords)
    (h : evalR w = evalR w') : w = w' :=
  List.inj_on_of_nodup_map Lr_nodup hw hw' h

noncomputable def phiFun (x : Kfive) : Perm (Fin 5) := evalP (Classical.choose (exists_word x))

theorem phiFun_spec {x : Kfive} {w : List Bool} (hw : w ∈ Lwords)
    (h : evalR w = R3.ofM (x.1 : M3)) : phiFun x = evalP w := by
  have hc := Classical.choose_spec (exists_word x)
  have e : Classical.choose (exists_word x) = w := word_unique hc.1 hw (hc.2.trans h.symm)
  unfold phiFun
  rw [e]

theorem phiFun_one : phiFun 1 = 1 := by
  have h := phiFun_spec (x := 1) (w := []) (by decide) (by
    show evalR [] = R3.ofM ((1 : GL (Fin 3) (ZMod 5)) : M3)
    rw [Units.val_one, R3.ofM_one]
    rfl)
  rw [h]
  rfl

theorem phiFun_mul_gen (x : Kfive) (b : Bool) :
    phiFun (x * ⟨genGL b, genGL_mem b⟩) = phiFun x * genP b := by
  obtain ⟨w, hw, hwe⟩ := exists_word x
  obtain ⟨w', hw', he', hp'⟩ := step_table w hw b
  have h1 : phiFun x = evalP w := phiFun_spec hw hwe
  have h2 : phiFun (x * ⟨genGL b, genGL_mem b⟩) = evalP w' := by
    apply phiFun_spec hw'
    rw [he']
    show _ = R3.ofM ((x.1 * genGL b : GL (Fin 3) (ZMod 5)) : M3)
    rw [Units.val_mul, R3.ofM_mul, ofM_genGL, hwe]
  rw [h1, h2, hp']

theorem phiFun_mul_gen_inv (x : Kfive) (b : Bool) :
    phiFun (x * (⟨genGL b, genGL_mem b⟩ : Kfive)⁻¹) = phiFun x * (genP b)⁻¹ := by
  have h := phiFun_mul_gen (x * (⟨genGL b, genGL_mem b⟩ : Kfive)⁻¹) b
  rw [mul_assoc, inv_mul_cancel, mul_one] at h
  rw [h]
  group

theorem mul_gen_step (b : Bool) (g : Kfive)
    (ih : ∀ x, phiFun (x * g) = phiFun x * phiFun g) (x : Kfive) :
    phiFun (x * (g * ⟨genGL b, genGL_mem b⟩)) =
      phiFun x * phiFun (g * ⟨genGL b, genGL_mem b⟩) := by
  rw [← mul_assoc, phiFun_mul_gen, ih, phiFun_mul_gen, mul_assoc]

theorem mul_gen_inv_step (b : Bool) (g : Kfive)
    (ih : ∀ x, phiFun (x * g) = phiFun x * phiFun g) (x : Kfive) :
    phiFun (x * (g * (⟨genGL b, genGL_mem b⟩ : Kfive)⁻¹)) =
      phiFun x * phiFun (g * (⟨genGL b, genGL_mem b⟩ : Kfive)⁻¹) := by
  rw [← mul_assoc, phiFun_mul_gen_inv, ih, phiFun_mul_gen_inv, mul_assoc]

theorem phiFun_mul (x y : Kfive) : phiFun (x * y) = phiFun x * phiFun y := by
  obtain ⟨y, hy⟩ := y
  induction hy using Subgroup.closure_induction_right generalizing x with
  | one =>
    show phiFun (x * 1) = phiFun x * phiFun 1
    rw [mul_one, phiFun_one, mul_one]
  | mul_right g hg s hs ih =>
    rcases hs with rfl | rfl
    · exact mul_gen_step false ⟨g, hg⟩ ih x
    · exact mul_gen_step true ⟨g, hg⟩ ih x
  | mul_inv_cancel g hg s hs ih =>
    rcases hs with rfl | rfl
    · exact mul_gen_inv_step false ⟨g, hg⟩ ih x
    · exact mul_gen_inv_step true ⟨g, hg⟩ ih x

noncomputable def phiHom : Kfive →* Perm (Fin 5) where
  toFun := phiFun
  map_one' := phiFun_one
  map_mul' := phiFun_mul

theorem phiHom_injective : Function.Injective phiHom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨w, hw, hwe⟩ := exists_word x
  have h1 : evalP w = 1 := by
    rw [← phiFun_spec hw hwe]
    exact hx
  have h2 := one_table w hw h1
  have h3 : R3.ofM (x.1 : M3) = R3.ofM ((1 : GL (Fin 3) (ZMod 5)) : M3) := by
    rw [← hwe, h2, Units.val_one, R3.ofM_one]
  exact Subtype.ext (Units.ext (R3.ofM_inj h3))

theorem sign_phiFun (x : Kfive) : Perm.sign (phiFun x) = 1 := by
  obtain ⟨w, hw, hwe⟩ := exists_word x
  rw [phiFun_spec hw hwe]
  exact even_table w hw

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  have h := two_mul_nat_card_alternatingGroup (α := Fin 5)
  have e : Nat.card (Fin 5) = 5 := by simp
  rw [Nat.card_perm, e] at h
  have h5 : Nat.factorial 5 = 120 := by decide
  omega

noncomputable def phiAlt : Kfive →* alternatingGroup (Fin 5) :=
  phiHom.codRestrict _ fun x => Equiv.Perm.mem_alternatingGroup.mpr (sign_phiFun x)

theorem phiAlt_bijective : Function.Bijective phiAlt := by
  have hinj : Function.Injective phiAlt := fun x y h =>
    phiHom_injective (congrArg Subtype.val h)
  exact hinj.bijective_of_nat_card_le (by rw [card_alt_five, natCard_Kfive])

noncomputable def kfiveEquiv : Kfive ≃* alternatingGroup (Fin 5) :=
  MulEquiv.ofBijective phiAlt phiAlt_bijective

theorem omegaGL_equiv_alternating (M : Matrix (Fin 3) (Fin 3) (ZMod 5)) (hMt : Mᵀ = M)
    (hdet : M.det ≠ 0) : Nonempty (omegaGL M ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨g, c, hc, hgc⟩ := exists_congr_scalar_five M hMt hdet
  have hΩ : (omegaGL M).comap (MulAut.conj g : GL (Fin 3) (ZMod 5) →* GL (Fin 3) (ZMod 5)) =
      omegaGL (1 : M3) := by
    rw [← omegaGL_congr, hgc, omegaGL_smul 1 hc]
  have hsurj : Function.Surjective
      (MulAut.conj g : GL (Fin 3) (ZMod 5) →* GL (Fin 3) (ZMod 5)) :=
    (MulAut.conj g).surjective
  have hmap : (omegaGL (1 : M3)).map
      (MulAut.conj g : GL (Fin 3) (ZMod 5) →* GL (Fin 3) (ZMod 5)) = omegaGL M := by
    rw [← hΩ, Subgroup.map_comap_eq_self_of_surjective hsurj]
  have e1 : omegaGL (1 : M3) ≃* omegaGL M :=
    ((omegaGL (1 : M3)).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hmap)
  have e2 : omegaGL (1 : M3) ≃* Kfive :=
    MulEquiv.subgroupCongr (omega_eq_Kfive natCard_soGL_one_five)
  exact ⟨e1.symm.trans (e2.trans kfiveEquiv)⟩

theorem alt_five_noncomm : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x :=
  ⟨⟨swap 0 1 * swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
    ⟨swap 2 3 * swap 3 4, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, fun h => by
      have h' := congrArg Subtype.val h
      revert h'
      decide⟩

theorem not_isCyclic_of_equiv_alternating {H : Type*} [Group H]
    (e : H ≃* alternatingGroup (Fin 5)) : ¬ IsCyclic H := by
  intro hc
  have hc' : IsCyclic (alternatingGroup (Fin 5)) := isCyclic_of_surjective e e.surjective
  have hcomm : IsMulCommutative (alternatingGroup (Fin 5)) := IsCyclic.isMulCommutative
  obtain ⟨x, y, hxy⟩ := alt_five_noncomm
  exact hxy (hcomm.is_comm.comm x y)

end OmegaAlt

end CFSG.RankThree.PartOne
