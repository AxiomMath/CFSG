module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3Conj
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613CfgSplit

public section

namespace CFSG.StandardType

namespace L613O4

open Module Multiplicative CFSG.StandardType.Triality
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.AUTSL CFSG.StandardType.D4Rank CFSG.StandardType.L613KG
  CFSG.StandardType.L613C3 CFSG.StandardType.NoOffOm CFSG.StandardType.OrthD4 QuadraticMap
open scoped Matrix

variable {K : Type} [Field K]

section Eigen

variable [CharP K 2]

theorem exists_eigen_pair {z : Om8 K} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ a b : Fin (2 * 4) → K, act z a = ω • a ∧ act z b = ω ^ 2 • b ∧
      polar (coordinateQuadPlus 4 K) a b = 1 := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have h3 := omega_cube hω
  have h6 := omega_sq_cube hω
  by_contra hcon
  have key : ∀ a b : Fin (2 * 4) → K, act z a = ω • a → act z b = ω ^ 2 • b →
      polar (coordinateQuadPlus 4 K) a b = 0 := by
    intro a b ha hb
    by_contra hne
    refine hcon ⟨(polar (coordinateQuadPlus 4 K) a b)⁻¹ • a, b, ?_, hb, ?_⟩
    · rw [act_smul, ha, smul_comm]
    · rw [polar_smul_left, smul_eq_mul, inv_mul_cancel₀ hne]
  have hA : ∀ a : Fin (2 * 4) → K, act z a = ω • a → a = 0 := by
    intro a ha
    refine hnd.1 _ fun x => ?_
    rw [polarBilin_apply_apply, eq_eproj_add (z := z) hω x, polar_add_right, polar_add_right,
      polar_eq_zero_of_eigen ha (act_eproj hz3 (one_pow 3) x)
        (by rw [mul_one]; exact omega_ne_one hω),
      polar_eq_zero_of_eigen ha (act_eproj hz3 h3 x) (omega_mul_self_ne_one hω),
      key a _ ha (act_eproj hz3 h6 x), add_zero, add_zero]
  have hB : ∀ b : Fin (2 * 4) → K, act z b = ω ^ 2 • b → b = 0 := by
    intro b hb
    refine hnd.1 _ fun x => ?_
    rw [polarBilin_apply_apply, eq_eproj_add (z := z) hω x, polar_add_right, polar_add_right,
      polar_eq_zero_of_eigen hb (act_eproj hz3 (one_pow 3) x)
        (by rw [mul_one]; exact omega_sq_ne_one hω),
      polar_comm, key _ b (act_eproj hz3 h3 x) hb,
      polar_eq_zero_of_eigen hb (act_eproj hz3 h6 x) (omega_sq_mul_sq_ne_one hω), add_zero,
      add_zero]
  apply hz1
  refine om8_ext fun v => ?_
  rw [act_one]
  have e := eq_eproj_add (z := z) hω v
  rw [hA _ (act_eproj hz3 h3 v), hB _ (act_eproj hz3 h6 v), add_zero, add_zero] at e
  have h1 := act_eproj hz3 (one_pow 3) v
  rw [one_smul] at h1
  rw [e]
  exact h1

end Eigen

section HypFrame

@[expose] def IsHypFrame {n : ℕ} (F G : Fin n → Fin (2 * 4) → K) : Prop :=
  (∀ i, coordinateQuadPlus 4 K (F i) = 0) ∧ (∀ i, coordinateQuadPlus 4 K (G i) = 0) ∧
    (∀ i j, polar (coordinateQuadPlus 4 K) (F i) (F j) = 0) ∧
    (∀ i j, polar (coordinateQuadPlus 4 K) (G i) (G j) = 0) ∧
    ∀ i j, polar (coordinateQuadPlus 4 K) (F i) (G j) = if i = j then 1 else 0

omit [Field K] in
theorem castAdd_ne_natAdd {n : ℕ} (a b : Fin n) : Fin.castAdd n a ≠ Fin.natAdd n b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
  omega

theorem IsHypFrame.polar_dual {n : ℕ} {F G : Fin n → Fin (2 * 4) → K} (h : IsHypFrame F G)
    (i j : Fin (n + n)) :
    polar (coordinateQuadPlus 4 K) (Fin.append F G i) (Fin.append G F j) =
      if i = j then 1 else 0 := by
  obtain ⟨-, -, hFF, hGG, hFG⟩ := h
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right]
  · rw [hFG]
    exact if_congr Fin.castAdd_inj.symm rfl rfl
  · rw [hFF, ite_eq_right (castAdd_ne_natAdd a b)]
  · rw [hGG, ite_eq_right (castAdd_ne_natAdd b a).symm]
  · rw [polar_comm, hFG]
    exact if_congr ((Fin.natAdd_inj n).trans eq_comm).symm rfl rfl

theorem IsHypFrame.linIndep {n : ℕ} {F G : Fin n → Fin (2 * 4) → K} (h : IsHypFrame F G) :
    LinearIndependent K (Fin.append F G) :=
  linIndep_of_dual (w := Fin.append G F) h.polar_dual

theorem IsHypFrame.Q_append {n : ℕ} {F G : Fin n → Fin (2 * 4) → K} (h : IsHypFrame F G)
    (i : Fin (n + n)) : coordinateQuadPlus 4 K (Fin.append F G i) = 0 := by
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · rw [Fin.append_left]
    exact h.1 a
  · rw [Fin.append_right]
    exact h.2.1 a

theorem IsHypFrame.polar_append_eq {n : ℕ} {F G F' G' : Fin n → Fin (2 * 4) → K}
    (h : IsHypFrame F G) (h' : IsHypFrame F' G') (i j : Fin (n + n)) :
    polar (coordinateQuadPlus 4 K) (Fin.append F' G' i) (Fin.append F' G' j) =
      polar (coordinateQuadPlus 4 K) (Fin.append F G i) (Fin.append F G j) := by
  obtain ⟨-, -, hFF, hGG, hFG⟩ := h
  obtain ⟨-, -, hFF', hGG', hFG'⟩ := h'
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
    simp only [Fin.append_left, Fin.append_right]
  · rw [hFF', hFF]
  · rw [hFG', hFG]
  · rw [polar_comm, hFG', polar_comm, hFG]
  · rw [hGG', hGG]

theorem isHypFrame_std :
    IsHypFrame (fun m : Fin 4 => (AutOm.pvec m true : Fin (2 * 4) → K))
      (fun m : Fin 4 => AutOm.pvec m false) := by
  refine ⟨fun i => AutOm.form_pvec _ _, fun i => AutOm.form_pvec _ _, fun i j => ?_,
    fun i j => ?_, fun i j => ?_⟩ <;> rw [AutOm.polar_pvec] <;> simp

end HypFrame

section Witt

variable [Finite K] [CharP K 2]

theorem exists_om8_of_hypFrame {F G : Fin 4 → Fin (2 * 4) → K} (hF : IsHypFrame F G)
    (i : Fin 4) :
    ∃ h : Om8 K, (∀ m, m ≠ i → act h (AutOm.pvec m true) = F m ∧
        act h (AutOm.pvec m false) = G m) ∧
      ((act h (AutOm.pvec i true) = F i ∧ act h (AutOm.pvec i false) = G i) ∨
        (act h (AutOm.pvec i true) = G i ∧ act h (AutOm.pvec i false) = F i)) := by
  have hnd := (regular_coordinateQuadPlus 4 K (by norm_num)).1
  have hT := (regular_coordinateQuadPlus 4 K (by norm_num)).2
  obtain ⟨g, hgO, hg⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd _ (Fin.append F G) isHypFrame_std.linIndep hF.linIndep
    (fun a => by rw [hF.Q_append, isHypFrame_std.Q_append])
    (isHypFrame_std.polar_append_eq hF)
  have hgF : ∀ m : Fin 4, g (AutOm.pvec m true) = F m := fun m => by
    have h := hg (Fin.castAdd 4 m)
    rwa [Fin.append_left, Fin.append_left] at h
  have hgG : ∀ m : Fin 4, g (AutOm.pvec m false) = G m := fun m => by
    have h := hg (Fin.natAdd 4 m)
    rwa [Fin.append_right, Fin.append_right] at h
  set M := matrixLinearIso.symm g with hM
  have hMI := symm_mem_isometries hgO
  set u₀ : Fin (2 * 4) → K := AutOm.pvec i true + AutOm.pvec i false with hu₀
  have hu : coordinateQuadPlus 4 K u₀ = 1 := by
    have h := AutOm.polar_pvec_not (K := K) (n := 4) i true
    rw [polar, AutOm.form_pvec, AutOm.form_pvec, sub_zero, sub_zero] at h
    exact h
  have hu0 : coordinateQuadPlus 4 K u₀ ≠ 0 := by
    rw [hu]
    exact one_ne_zero
  rcases mem_or_mul_reflMat_mem hnd hT hMI u₀ hu0 with hMΩ | hMrΩ
  · have hact : ∀ v, act (⟨M, hMΩ⟩ : Om8 K) v = g v := fun v => symm_mulVec g v
    exact ⟨⟨M, hMΩ⟩, fun m _ => ⟨by rw [hact, hgF], by rw [hact, hgG]⟩,
      Or.inl ⟨by rw [hact, hgF], by rw [hact, hgG]⟩⟩
  · have hact : ∀ v, act (⟨M * reflMat (coordinateQuadPlus 4 K) u₀ hu0, hMrΩ⟩ : Om8 K) v =
        g (v + polar (coordinateQuadPlus 4 K) u₀ v • u₀) := fun v => by
      change (M * reflMat (coordinateQuadPlus 4 K) u₀ hu0).val *ᵥ v = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, reflMat_mulVec_one u₀ hu hu0, symm_mulVec]
    have hpol_ne : ∀ m r, m ≠ i → polar (coordinateQuadPlus 4 K) u₀ (AutOm.pvec m r) = 0 := by
      intro m r hm
      rw [hu₀, polar_add_left, AutOm.polar_pvec_of_ne (Ne.symm hm),
        AutOm.polar_pvec_of_ne (Ne.symm hm), add_zero]
    have hpt : polar (coordinateQuadPlus 4 K) u₀ (AutOm.pvec i true) = 1 := by
      rw [hu₀, polar_add_left, AutOm.polar_pvec, AutOm.polar_pvec]
      simp
    have hpf : polar (coordinateQuadPlus 4 K) u₀ (AutOm.pvec i false) = 1 := by
      rw [hu₀, polar_add_left, AutOm.polar_pvec, AutOm.polar_pvec]
      simp
    refine ⟨⟨M * reflMat (coordinateQuadPlus 4 K) u₀ hu0, hMrΩ⟩, fun m hm => ⟨?_, ?_⟩,
      Or.inr ⟨?_, ?_⟩⟩
    · rw [hact, hpol_ne m true hm, zero_smul, add_zero, hgF]
    · rw [hact, hpol_ne m false hm, zero_smul, add_zero, hgG]
    · rw [hact, hpt, one_smul, hu₀, ← add_assoc, two_smul_vec, zero_add, hgG]
    · rw [hact, hpf, one_smul, hu₀, add_comm (AutOm.pvec i true), ← add_assoc, two_smul_vec,
        zero_add, hgF]

end Witt

section FrameEigen

variable [CharP K 2]

theorem exists_frame_eigen {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}
    (hfr : ∀ s s' : Fin 4 → ZMod 3,
      (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ SuppLE s s')
    (hdim : ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8)
    {ω : Kˣ} (hω : orderOf ω = 3) :
    ∃ u w : Fin 4 → Fin (2 * 4) → K,
      (∀ m, act (ι₁ (ofAdd (Pi.single m 1))) (u m) = (ω : K) • u m) ∧
      (∀ m, act (ι₁ (ofAdd (Pi.single m 1))) (w m) = ((ω⁻¹ : Kˣ) : K) • w m) ∧
      (∀ m n, n ≠ m → act (ι₁ (ofAdd (Pi.single n 1))) (u m) = u m ∧
        act (ι₁ (ofAdd (Pi.single n 1))) (w m) = w m) ∧
      IsHypFrame u w := by
  have hw := omega_sq_add_of_orderOf hω
  have hinv : ((ω⁻¹ : Kˣ) : K) = (ω : K) ^ 2 := by
    rw [Units.val_inv_eq_inv_val, omega_inv hw]
  set b : Fin 4 → Om8 K := fun m => ι₁ (ofAdd (Pi.single m 1)) with hb
  have hb3 : ∀ m, b m ^ 3 = 1 := fun m => L613Cfg.frame_pow_three ι₁ _
  have hb1 : ∀ m, b m ≠ 1 := by
    intro m h1
    have hd := hdim (Pi.single m 1)
    have hs : (supp (Pi.single m (1 : ZMod 3) : Fin 4 → ZMod 3)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨m, ?_⟩
      ext n
      rw [mem_supp, L613Cfg.single_ne_zero_iff, Finset.mem_singleton]
    change omFixDim (b m) + _ = 8 at hd
    rw [h1, omFixDim_one, hs] at hd
    omega
  choose u w hu hw' huw using fun m => exists_eigen_pair (hb3 m) (hb1 m) hw
  have hω1 : (ω : K) - 1 ≠ 0 := sub_ne_zero.mpr (omega_ne_one hw)
  have hω2 : (ω : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr (omega_sq_ne_one hw)
  have hother : ∀ (m : Fin 4) (a : Fin (2 * 4) → K) (l : K), act (b m) a = l • a → l - 1 ≠ 0 →
      ∀ n, n ≠ m → act (b n) a = a := by
    intro m a l ha hl n hnm
    have e : a = act (b m) ((l - 1)⁻¹ • a) - (l - 1)⁻¹ • a := by
      rw [act_smul, ha, smul_smul, ← sub_smul,
        show (l - 1)⁻¹ * l - (l - 1)⁻¹ = (l - 1)⁻¹ * (l - 1) by ring, inv_mul_cancel₀ hl,
        one_smul]
    rw [e]
    refine L613Cfg.act_comm_of_disjoint hfr hdim (fun x hx => ?_) _
    rw [L613Cfg.single_ne_zero_iff] at hx
    subst hx
    exact Pi.single_eq_of_ne hnm _
  have huo : ∀ m n, n ≠ m → act (b n) (u m) = u m := fun m n hnm =>
    hother m (u m) _ (hu m) hω1 n hnm
  have hwo : ∀ m n, n ≠ m → act (b n) (w m) = w m := fun m n hnm =>
    hother m (w m) _ (hw' m) hω2 n hnm
  refine ⟨u, w, hu, fun m => by rw [hinv]; exact hw' m, fun m n hnm => ⟨huo m n hnm,
    hwo m n hnm⟩, fun m => Q_eq_zero_of_eigen (hu m) (omega_mul_self_ne_one hw),
    fun m => Q_eq_zero_of_eigen (hw' m) (omega_sq_mul_sq_ne_one hw), fun m n => ?_,
    fun m n => ?_, fun m n => ?_⟩
  · by_cases hmn : m = n
    · subst hmn
      exact polar_eq_zero_of_eigen (hu m) (hu m) (omega_mul_self_ne_one hw)
    · exact polar_eq_zero_of_eigen (z := b m) (hu m) (m := 1)
        (by rw [one_smul]; exact huo n m hmn) (by rw [mul_one]; exact omega_ne_one hw)
  · by_cases hmn : m = n
    · subst hmn
      exact polar_eq_zero_of_eigen (hw' m) (hw' m) (omega_sq_mul_sq_ne_one hw)
    · exact polar_eq_zero_of_eigen (z := b m) (hw' m) (m := 1)
        (by rw [one_smul]; exact hwo n m hmn) (by rw [mul_one]; exact omega_sq_ne_one hw)
  · split_ifs with hmn
    · subst hmn
      exact huw m
    · exact polar_eq_zero_of_eigen (z := b m) (hu m) (m := 1)
        (by rw [one_smul]; exact hwo n m hmn) (by rw [mul_one]; exact omega_ne_one hw)

end FrameEigen

end L613O4

end CFSG.StandardType
