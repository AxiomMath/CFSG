module

public import CFSG.Quasithin.Vol2.Ch11SecBK7B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

namespace K7

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem acomm_add_le_of_hyp {y y' : Fin 2 ⊕ Fin 2 → K}
    (hb : Matrix.toBilin' (spJ K) y y' ≠ 0) :
    acomm π (y + y') ≤ acomm (W := W) π y ⊔ acomm π y' := by
  set t := trv y' (Matrix.toBilin' (spJ K) y y')⁻¹ with ht
  have hty : mat 2 K t *ᵥ y = y + y' := by
    rw [ht, trv_mulVec, inv_mul_cancel₀ hb, one_smul]
  intro a ha
  have hb' : ((π t⁻¹ : ↥H) : MulAut W) a ∈ acomm π y := by
    have h1 := map_mem_acomm (π := π) t⁻¹ ha
    rwa [← hty, mat_inv_mulVec] at h1
  set b := ((π t⁻¹ : ↥H) : MulAut W) a with hbdef
  have hab : a = (((π t : ↥H) : MulAut W) b * b⁻¹) * b := by
    rw [inv_mul_cancel_right, hbdef, ← MulAut.mul_apply, ← Subgroup.coe_mul, ← map_mul,
      mul_inv_cancel, map_one, Subgroup.coe_one, MulAut.one_apply]
  rw [hab]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (gen_mem_acomm π y' _ b))
    (Subgroup.mem_sup_left hb')

theorem mem_acomm_add_of_hyp (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) {y y' : Fin 2 ⊕ Fin 2 → K}
    (hb : Matrix.toBilin' (spJ K) y y' ≠ 0) {v w : W} (hv : v ∈ acomm π y)
    (hw : w ∈ acomm π y') (hfv : f v = y) (hfw : f w = y') : v * w ∈ acomm π (y + y') := by
  have hy : y ≠ 0 := by rintro rfl; simp at hb
  have hy' : y' ≠ 0 := by rintro rfl; simp at hb
  have hyy : y + y' ≠ 0 := by
    intro h
    apply hb
    rw [show y' = y + y' - y by abel, h, zero_sub, map_neg, bil_self, neg_zero]
  obtain ⟨b, hb₀, hfb⟩ := exists_mem_acomm hf hyy 1
  rw [one_smul] at hfb
  obtain ⟨a, ha, a', ha', rfl⟩ := Subgroup.mem_sup.mp (acomm_add_le_of_hyp hb hb₀)
  obtain ⟨d, hd⟩ := exists_smul_of_mem_acomm hf ha
  obtain ⟨d', hd'⟩ := exists_smul_of_mem_acomm hf ha'
  rw [hf.map_mul, hd, hd'] at hfb
  have e1 := congrArg (fun x => Matrix.toBilin' (spJ K) x y') hfb
  have e2 := congrArg (fun x => Matrix.toBilin' (spJ K) y x) hfb
  simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_self,
    mul_zero, add_zero, zero_add] at e1 e2
  have hd1 : d = 1 := mul_right_cancel₀ hb (e1.trans (one_mul _).symm)
  have hd1' : d' = 1 := mul_right_cancel₀ hb (e2.trans (one_mul _).symm)
  rw [hd1, one_smul] at hd
  rw [hd1', one_smul] at hd'
  have hZ₀ : ∀ {u : Fin 2 ⊕ Fin 2 → K} (hu : u ≠ 0) {x : W}, x ∈ acomm π u → f x = 0 →
      x ∈ acomm π (y + y') := fun hu x hx hfx =>
    acomm_inf_le hZ hu hyy ⟨hx, (hf.ker x).mp hfx⟩
  have h1 : v * a⁻¹ ∈ acomm π (y + y') :=
    hZ₀ hy (Subgroup.mul_mem _ hv (Subgroup.inv_mem _ ha))
      (by rw [hf.map_mul_inv, hfv, hd, sub_self])
  have h2 : w * a'⁻¹ ∈ acomm π (y + y') :=
    hZ₀ hy' (Subgroup.mul_mem _ hw (Subgroup.inv_mem _ ha'))
      (by rw [hf.map_mul_inv, hfw, hd', sub_self])
  have e : v * w = (a * a') * ((v * a⁻¹) * (w * a'⁻¹)) := by
    calc v * w = v * w * (a * a⁻¹) * (a' * a'⁻¹) := by
          rw [mul_inv_cancel, mul_inv_cancel, mul_one, mul_one]
      _ = (a * a') * ((v * a⁻¹) * (w * a'⁻¹)) := by ac_rfl
  rw [e]
  exact Subgroup.mul_mem _ hb₀ (Subgroup.mul_mem _ h1 h2)

theorem exists_bil_pair {x y : Fin 2 ⊕ Fin 2 → K} (hx : x ≠ 0) (hxy : ∀ μ : K, y ≠ μ • x)
    (hb : Matrix.toBilin' (spJ K) x y = 0) (l : K) :
    ∃ u, Matrix.toBilin' (spJ K) x u = 1 ∧ Matrix.toBilin' (spJ K) y u = l := by
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨γ, hγ⟩ := exists_sp4_lin_eq _ x he0 hx
  rw [linModelNat_lin] at hγ
  change mat 2 K γ *ᵥ vec4 1 0 0 0 = x at hγ
  set y' := mat 2 K γ⁻¹ *ᵥ y with hy'
  have hyy : y = mat 2 K γ *ᵥ y' := by rw [hy', mat_mulVec_inv]
  have h0 : y' (.inr 0) = 0 := by
    rw [← spB_e0 y', ← spB_mat γ (vec4 1 0 0 0) y', hγ, ← hyy, hb]
  have hne : y' (.inl 1) ≠ 0 ∨ y' (.inr 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hxy (y' (.inl 0))
    rw [hyy, ← hγ, ← Matrix.mulVec_smul]
    congr 1
    exact vec4_eq (by simp [vec4]) (by simp [vec4, h.1]) (by simp [vec4, h0])
      (by simp [vec4, h.2])
  obtain ⟨u', hu1, hu2⟩ : ∃ u' : Fin 2 ⊕ Fin 2 → K,
      Matrix.toBilin' (spJ K) (vec4 1 0 0 0) u' = 1 ∧ Matrix.toBilin' (spJ K) y' u' = l := by
    by_cases h1 : y' (.inl 1) ≠ 0
    · refine ⟨vec4 0 0 1 ((l - y' (.inl 0)) / y' (.inl 1)), ?_, ?_⟩
      · rw [spB_e0]
        rfl
      · rw [toBilin'_spJ_apply]
        simp only [Fin.sum_univ_two, vec4, Sum.elim_inl, Sum.elim_inr, h0]
        simp
        field_simp
        ring
    · have h2 : y' (.inl 1) = 0 := not_not.mp h1
      have h3 : y' (.inr 1) ≠ 0 := hne.resolve_left (not_not.mpr h2)
      refine ⟨vec4 0 ((y' (.inl 0) - l) / y' (.inr 1)) 1 0, ?_, ?_⟩
      · rw [spB_e0]
        rfl
      · rw [toBilin'_spJ_apply]
        simp only [Fin.sum_univ_two, vec4, Sum.elim_inl, Sum.elim_inr, h0]
        simp [h2]
        field_simp
        ring
  refine ⟨mat 2 K γ *ᵥ u', ?_, ?_⟩
  · rw [← hγ, spB_mat, hu1]
  · rw [hyy, spB_mat, hu2]

variable [CharP K 2]

theorem mem_acomm_add_of_orth (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hW : ∀ w : W, w ^ 2 = 1) {l : K} (hl0 : l ≠ 0)
    (hl1 : l ≠ 1) {y y' : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (hyy : ∀ μ : K, y' ≠ μ • y)
    (hb : Matrix.toBilin' (spJ K) y y' = 0) {v w : W} (hv : v ∈ acomm π y)
    (hw : w ∈ acomm π y') (hfv : f v = y) (hfw : f w = y') : v * w ∈ acomm π (y + y') := by
  obtain ⟨u, hu1, hul⟩ := exists_bil_pair hy hyy hb l
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  obtain ⟨c, hc, hfc⟩ := exists_mem_acomm hf hu0 1
  rw [one_smul] at hfc
  have h1 : v * c ∈ acomm π (y + u) :=
    mem_acomm_add_of_hyp hf hZ (by rw [hu1]; exact one_ne_zero) hv hc hfv hfc
  have h2 : w * c ∈ acomm π (y' + u) :=
    mem_acomm_add_of_hyp hf hZ (by rw [hul]; exact hl0) hw hc hfw hfc
  have hb3 : Matrix.toBilin' (spJ K) (y + u) (y' + u) ≠ 0 := by
    rw [bil_add_left, bil_add_right, bil_add_right, bil_self, hb, hu1, bil_comm u y', hul,
      zero_add, add_zero]
    intro h
    apply hl1
    rw [← sub_eq_zero, sub_eq_add_neg, CharTwo.neg_eq, add_comm]
    exact h
  have h3 := mem_acomm_add_of_hyp hf hZ hb3 h1 h2 (by rw [hf.map_mul, hfv, hfc])
    (by rw [hf.map_mul, hfw, hfc])
  have e1 : y + u + (y' + u) = y + y' := by
    have huu : u + u = 0 := funext fun i => CharTwo.add_self_eq_zero (u i)
    rw [add_add_add_comm, huu, add_zero]
  have e2 : v * c * (w * c) = v * w := by
    rw [mul_mul_mul_comm, ← sq c, hW c, mul_one]
  rwa [e1, e2] at h3

theorem le_acomm (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (hcomm : commV H = ⊤) (hW : ∀ w : W, w ^ 2 = 1)
    {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) :
    Z ≤ acomm π y := by
  set e₀ : Fin 2 ⊕ Fin 2 → K := vec4 1 0 0 0 with he₀
  have he0 : e₀ ≠ 0 := fun h => (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  have hinv : ∀ v : W, v⁻¹ = v := fun v => by
    rw [inv_eq_iff_mul_eq_one, ← sq, hW]
  have hZ₀ : ∀ {u u' : Fin 2 ⊕ Fin 2 → K}, u ≠ 0 → u' ≠ 0 → ∀ {x : W}, x ∈ acomm π u →
      f x = 0 → x ∈ acomm π u' := fun hu hu' x hx hfx =>
    acomm_inf_le hZ hu hu' ⟨hx, (hf.ker x).mp hfx⟩
  let S : Subgroup W :=
    { carrier := {v | (f v = 0 ∧ v ∈ acomm π e₀) ∨ (f v ≠ 0 ∧ v ∈ acomm π (f v))}
      one_mem' := Or.inl ⟨hf.map_one, Subgroup.one_mem _⟩
      inv_mem' := fun {v} hv => by rw [Set.mem_ofPred_eq, hinv]; exact hv
      mul_mem' := fun {v w} hv hw => by
        rcases hv with ⟨hv0, hv⟩ | ⟨hv0, hv⟩ <;> rcases hw with ⟨hw0, hw⟩ | ⟨hw0, hw⟩
        · exact Or.inl ⟨by rw [hf.map_mul, hv0, hw0, add_zero], Subgroup.mul_mem _ hv hw⟩
        · refine Or.inr ⟨by rw [hf.map_mul, hv0, zero_add]; exact hw0, ?_⟩
          rw [hf.map_mul, hv0, zero_add]
          exact Subgroup.mul_mem _ (hZ₀ he0 hw0 hv hv0) hw
        · refine Or.inr ⟨by rw [hf.map_mul, hw0, add_zero]; exact hv0, ?_⟩
          rw [hf.map_mul, hw0, add_zero]
          exact Subgroup.mul_mem _ hv (hZ₀ he0 hv0 hw hw0)
        · by_cases hprop : ∃ μ : K, f w = μ • f v
          · obtain ⟨μ, hμ⟩ := hprop
            have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_smul] at hμ; exact hw0 hμ
            rw [hμ, acomm_smul hμ0] at hw
            have hvw := Subgroup.mul_mem _ hv hw
            have hfvw : f (v * w) = (1 + μ) • f v := by rw [hf.map_mul, hμ, add_smul, one_smul]
            by_cases h1 : 1 + μ = 0
            · refine Or.inl ⟨by rw [hfvw, h1, zero_smul], hZ₀ hv0 he0 hvw ?_⟩
              rw [hfvw, h1, zero_smul]
            · refine Or.inr ⟨by rw [hfvw]; exact smul_ne_zero h1 hv0, ?_⟩
              rw [hfvw, acomm_smul h1]
              exact hvw
          · push Not at hprop
            have hne : f v + f w ≠ 0 := by
              intro h
              apply hprop (-1)
              rw [neg_one_smul, eq_neg_iff_add_eq_zero, add_comm]
              exact h
            refine Or.inr ⟨by rw [hf.map_mul]; exact hne, ?_⟩
            rw [hf.map_mul]
            by_cases hb : Matrix.toBilin' (spJ K) (f v) (f w) = 0
            · exact mem_acomm_add_of_orth hf hZ hW hl0 hl1 hv0 hprop hb hv hw rfl rfl
            · exact mem_acomm_add_of_hyp hf hZ hb hv hw rfl rfl }
  have hS_inv : ∀ h ∈ H, ∀ v ∈ S, h v ∈ S := by
    intro h hh v hv
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSp 2 K), π γ = ⟨h, hh⟩ := hf.onto ⟨h, hh⟩
    have hhγ : h = ((π γ : ↥H) : MulAut W) := by rw [hγ]
    rcases hv with ⟨hv0, hv⟩ | ⟨hv0, hv⟩
    · rw [hZ h hh v ((hf.ker v).mp hv0)]
      exact Or.inl ⟨hv0, hv⟩
    · have hfh : f (h v) = mat 2 K γ *ᵥ f v := by rw [hhγ, hf.act4]
      refine Or.inr ⟨?_, ?_⟩
      · rw [hfh]
        intro h0
        apply hv0
        have := congrArg (fun x => mat 2 K γ⁻¹ *ᵥ x) h0
        simpa only [mat_inv_mulVec, Matrix.mulVec_zero] using this
      · rw [hfh, hhγ]
        exact map_mem_acomm γ hv
  have hSZ : ∀ v : W, ∃ s ∈ S, ∃ z ∈ Z, v = s * z := by
    intro v
    by_cases hv0 : f v = 0
    · exact ⟨1, Subgroup.one_mem _, v, (hf.ker v).mp hv0, by rw [one_mul]⟩
    · obtain ⟨a, ha, hfa⟩ := exists_mem_acomm hf hv0 1
      rw [one_smul] at hfa
      refine ⟨a, Or.inr ⟨by rw [hfa]; exact hv0, by rw [hfa]; exact ha⟩, a⁻¹ * v,
        (hf.ker _).mp ?_, by rw [mul_inv_cancel_left]⟩
      rw [hf.map_mul, hf.map_inv, hfa, neg_add_cancel]
  have hle : commV H ≤ S := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨h, hh, v, rfl⟩
    obtain ⟨s, hs, z, hz, rfl⟩ := hSZ v
    have e : h (s * z) * (s * z)⁻¹ = h s * s⁻¹ := by
      rw [map_mul, hZ h hh z hz, _root_.mul_inv_rev, mul_comm z⁻¹ s⁻¹, mul_assoc,
        mul_comm s⁻¹ z⁻¹, mul_inv_cancel_left]
    rw [e]
    exact Subgroup.mul_mem _ (hS_inv h hh s hs) (Subgroup.inv_mem _ hs)
  intro z hz
  have hzS := hle (hcomm ▸ Subgroup.mem_top z)
  have hfz : f z = 0 := (hf.ker z).mpr hz
  rcases hzS with ⟨-, hz'⟩ | ⟨hz0, -⟩
  · exact hZ₀ he0 hy hz' hfz
  · exact absurd hfz hz0

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
