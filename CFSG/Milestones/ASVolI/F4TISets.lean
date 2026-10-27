module

public import CFSG.Milestones.ASVolI.F4Conjugacy
import all CFSG.Milestones.ASVolI.F4
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Open
section PartBurnsideF4jSp

section BurnsideF4jbNative

open Matrix CFSG.ASVolI.ChF CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a

variable {K : Type} [Field K]

@[expose] def burnsideF4jb_det (g : StatedSp 2 K) : K :=
  burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1) (Sum.inl 0) *
      burnsideF4gSpInv_mv g (Pi.single (Sum.inl 1) 1) (Sum.inl 1) -
    burnsideF4gSpInv_mv g (Pi.single (Sum.inl 1) 1) (Sum.inl 0) *
      burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1) (Sum.inl 1)

theorem burnsideF4jb_form_e1_left (y : Fin 2 ⊕ Fin 2 → K) :
    burnsideF4gSpInv_form (Pi.single (Sum.inl 1) 1) y = y (Sum.inr 1) := by
  simp [burnsideF4gSpInv_form, Pi.single_apply]

theorem burnsideF4jb_Q2_one_e {g : StatedSp 2 K} (hg : g ∈ Q2 K 1) (i : Fin 2) :
    burnsideF4gSpInv_mv g (Pi.single (Sum.inl i) 1) (Sum.inr 0) = 0 ∧
      burnsideF4gSpInv_mv g (Pi.single (Sum.inl i) 1) (Sum.inr 1) = 0 := by
  have h := (burnsideF4gSpInv_mem_Q2_one g).1 hg (Pi.single (Sum.inl i) 1)
  have he : (Pi.single (Sum.inl i) 1 : Fin 2 ⊕ Fin 2 → K) ∈ flag 2 K 2 := by
    rw [burnsideF4gSpInv_mem_flag_two]
    simp [Pi.single_apply]
  exact (burnsideF4gSpInv_mem_flag_two _).1 (h.2 he)

theorem burnsideF4jb_mul_xs [CharP K 2] {g : StatedSp 2 K} (hg : g ∈ Q2 K 1) (s : K) :
    g * burnsideF4gSpInv_xs s = burnsideF4gSpInv_xs (burnsideF4jb_det g * s) * g := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨hX0, hX1⟩ := burnsideF4jb_Q2_one_e hg 0
  obtain ⟨hY0, hY1⟩ := burnsideF4jb_Q2_one_e hg 1
  apply burnsideF4gSpInv_ext
  intro v
  rw [burnsideF4gSpInv_mv_mul, burnsideF4gSpInv_mv_mul, burnsideF4gSpInv_xs_mv,
    burnsideF4gSpInv_xs_mv, burnsideF4gSpInv_mv_add, burnsideF4gSpInv_mv_add,
    burnsideF4gSpInv_mv_smul, burnsideF4gSpInv_mv_smul]
  have hf0 := burnsideF4gSpInv_form_mv g (Pi.single (Sum.inl 0) 1) v
  have hf1 := burnsideF4gSpInv_form_mv g (Pi.single (Sum.inl 1) 1) v
  rw [burnsideF4gSpInv_form_e0_left] at hf0
  rw [burnsideF4jb_form_e1_left] at hf1
  unfold burnsideF4jb_det
  generalize burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1) = X at *
  generalize burnsideF4gSpInv_mv g (Pi.single (Sum.inl 1) 1) = Y at *
  generalize burnsideF4gSpInv_mv g v = u at *
  simp only [burnsideF4gSpInv_form, hX0, hX1, hY0, hY1, zero_mul, add_zero, sub_zero] at hf0 hf1
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Pi.single_apply, hX0, hX1, hY0, hY1]
  · linear_combination (-(s * Y (Sum.inl 0))) * hf0 + (-(s * X (Sum.inl 0))) * hf1 +
      (s * X (Sum.inl 0) * Y (Sum.inl 0) * u (Sum.inr 0) +
        s * X (Sum.inl 1) * Y (Sum.inl 0) * u (Sum.inr 1)) * h2
  · linear_combination (-(s * Y (Sum.inl 1))) * hf0 + (-(s * X (Sum.inl 1))) * hf1 +
      (s * X (Sum.inl 1) * Y (Sum.inl 0) * u (Sum.inr 0) +
        s * X (Sum.inl 1) * Y (Sum.inl 1) * u (Sum.inr 1)) * h2

theorem burnsideF4jb_pow_mul_xs [CharP K 2] {g : StatedSp 2 K} (hg : g ∈ Q2 K 1) (n : ℕ)
    (s : K) :
    g ^ n * burnsideF4gSpInv_xs s = burnsideF4gSpInv_xs (burnsideF4jb_det g ^ n * s) * g ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, burnsideF4jb_mul_xs hg, mul_assoc, pow_succ',
      mul_assoc]

theorem burnsideF4jb_comm_xs [CharP K 2] {g : StatedSp 2 K} (hg : g ∈ Q2 K 1) {k : ℕ}
    (hk : orderOf g = 2 ^ k) (s : K) :
    g * burnsideF4gSpInv_xs s = burnsideF4gSpInv_xs s * g := by
  have h1 : g ^ (2 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have h := burnsideF4jb_pow_mul_xs hg (2 ^ k) 1
  rw [h1, one_mul, mul_one, mul_one] at h
  have hd : burnsideF4jb_det g ^ (2 ^ k) = 1 := (burnsideF4gSpInv_xs_injective h).symm
  have hd1 : burnsideF4jb_det g = 1 := burnsideF4gSpInv_eq_one_of_pow hd
  rw [burnsideF4jb_mul_xs hg, hd1, one_mul]

theorem burnsideF4jb_mem_oPPrime_of_sq {x : StatedSp 2 K} (hx : x ∈ Q2 K 1) (h : x * x = 1) :
    x ∈ oPPrime 2 (Q2 K 1) := by
  refine Subgroup.subset_closure ⟨hx, ?_⟩
  by_cases h1 : x = 1
  · exact ⟨0, by simp [h1]⟩
  · exact ⟨1, by rw [pow_one]; exact orderOf_eq_prime (by rwa [sq]) h1⟩

theorem burnsideF4jb_xs_mem_Q2_one (t : K) : burnsideF4gSpInv_xs t ∈ Q2 K 1 :=
  burnsideF4gSpInv_Rad2_le_Q2 (burnsideF4gSpInv_xs_mem_Rad2 t)

theorem burnsideF4jb_xs_mem_ctr [CharP K 2] (t : K) :
    burnsideF4gSpInv_xs t ∈ ctr (oPPrime 2 (Q2 K 1)) := by
  refine ⟨burnsideF4jb_mem_oPPrime_of_sq (burnsideF4jb_xs_mem_Q2_one t)
    (burnsideF4gSpInv_xs_sq t), ?_⟩
  have hle : oPPrime 2 (Q2 K 1) ≤
      Subgroup.centralizer ({burnsideF4gSpInv_xs t} : Set (StatedSp 2 K)) := by
    unfold oPPrime
    rw [Subgroup.closure_le]
    rintro x ⟨hxQ, k, hk⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (burnsideF4jb_comm_xs hxQ hk t)
  exact Subgroup.mem_centralizer_iff.2 fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle hh)

@[expose] def burnsideF4jb_xd (t : K) : StatedSp 2 K :=
  pairRootElt (a := Sum.inl 0) (b := Sum.inl 1) (by simp) t

@[expose] def burnsideF4jb_xe (t : K) : StatedSp 2 K :=
  pairRootElt (a := Sum.inl 1) (b := Sum.inl 0) (by simp) t

theorem burnsideF4jb_xd_mv (t : K) (v : Fin 2 ⊕ Fin 2 → K) :
    burnsideF4gSpInv_mv (burnsideF4jb_xd t) v =
      v + (t * v (Sum.inl 1)) • Pi.single (Sum.inl 0) 1 -
        (t * v (Sum.inr 0)) • Pi.single (Sum.inr 1) 1 := by
  simp only [burnsideF4gSpInv_mv, burnsideF4jb_xd, coe_pairRootElt, pairRootMat_inl_inl]
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq, smul_smul, smul_smul,
    one_mul, one_mul]

theorem burnsideF4jb_xe_mv (t : K) (v : Fin 2 ⊕ Fin 2 → K) :
    burnsideF4gSpInv_mv (burnsideF4jb_xe t) v =
      v + (t * v (Sum.inl 0)) • Pi.single (Sum.inl 1) 1 -
        (t * v (Sum.inr 1)) • Pi.single (Sum.inr 0) 1 := by
  simp only [burnsideF4gSpInv_mv, burnsideF4jb_xe, coe_pairRootElt, pairRootMat_inl_inl]
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq, smul_smul, smul_smul,
    one_mul, one_mul]

theorem burnsideF4jb_xd_mem_Q2_one (t : K) : burnsideF4jb_xd t ∈ Q2 K 1 := by
  rw [burnsideF4gSpInv_mem_Q2_one]
  intro v
  have e0 : burnsideF4gSpInv_mv (burnsideF4jb_xd t) v (Sum.inr 0) = v (Sum.inr 0) := by
    rw [burnsideF4jb_xd_mv]
    simp [Pi.single_apply]
  have e1 : burnsideF4gSpInv_mv (burnsideF4jb_xd t) v (Sum.inr 1) =
      v (Sum.inr 1) - t * v (Sum.inr 0) := by
    rw [burnsideF4jb_xd_mv]
    simp [Pi.single_apply]
  rw [burnsideF4gSpInv_mem_flag_two, burnsideF4gSpInv_mem_flag_two, e0, e1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h1, mul_zero, sub_zero] at h2
    exact h2
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h1, h2, mul_zero, sub_zero]⟩

theorem burnsideF4jb_xe_mem_Q2_one (t : K) : burnsideF4jb_xe t ∈ Q2 K 1 := by
  rw [burnsideF4gSpInv_mem_Q2_one]
  intro v
  have e0 : burnsideF4gSpInv_mv (burnsideF4jb_xe t) v (Sum.inr 0) =
      v (Sum.inr 0) - t * v (Sum.inr 1) := by
    rw [burnsideF4jb_xe_mv]
    simp [Pi.single_apply]
  have e1 : burnsideF4gSpInv_mv (burnsideF4jb_xe t) v (Sum.inr 1) = v (Sum.inr 1) := by
    rw [burnsideF4jb_xe_mv]
    simp [Pi.single_apply]
  rw [burnsideF4gSpInv_mem_flag_two, burnsideF4gSpInv_mem_flag_two, e0, e1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rw [h2, mul_zero, sub_zero] at h1
    exact h1
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, h2, mul_zero, sub_zero], h2⟩

theorem burnsideF4jb_xd_sq [CharP K 2] (t : K) : burnsideF4jb_xd t * burnsideF4jb_xd t = 1 := by
  have h := ((root_matrix_data (r := 2) (K := K)).1 (Sum.inl 0) (Sum.inl 1) (by simp) t t).2.1
  show pairRootElt _ t * pairRootElt _ t = 1
  rw [h, CharTwo.add_self_eq_zero]
  exact statedSp_ext (by rw [coe_pairRootElt, pairRootMat_zero]; rfl)

theorem burnsideF4jb_xe_sq [CharP K 2] (t : K) : burnsideF4jb_xe t * burnsideF4jb_xe t = 1 := by
  have h := ((root_matrix_data (r := 2) (K := K)).1 (Sum.inl 1) (Sum.inl 0) (by simp) t t).2.1
  show pairRootElt _ t * pairRootElt _ t = 1
  rw [h, CharTwo.add_self_eq_zero]
  exact statedSp_ext (by rw [coe_pairRootElt, pairRootMat_zero]; rfl)

theorem burnsideF4jb_xl_mem_Rad2 (t : K) : burnsideF4gSpInv_xl t ∈ burnsideF4gSpInv_Rad2 K := by
  refine ⟨fun v => ?_, fun w hw => ?_⟩
  · rw [burnsideF4gSpInv_xl_mv, add_sub_cancel_left, burnsideF4gSpInv_mem_flag_two]
    simp [Pi.single_apply]
  · rw [burnsideF4gSpInv_mem_flag_two] at hw
    rw [burnsideF4gSpInv_xl_mv, hw.1]
    simp

theorem burnsideF4jb_ctr_oPPrime_le [CharP K 2] {z : StatedSp 2 K}
    (hz : z ∈ ctr (oPPrime 2 (Q2 K 1))) : ∃ t : K, z = burnsideF4gSpInv_xs t := by
  obtain ⟨-, hzC⟩ := hz
  have hc := Subgroup.mem_centralizer_iff.1 hzC
  have hl : burnsideF4gSpInv_xl 1 * z = z * burnsideF4gSpInv_xl 1 :=
    hc _ (burnsideF4jb_mem_oPPrime_of_sq
      (burnsideF4gSpInv_Rad2_le_Q2 (burnsideF4jb_xl_mem_Rad2 1)) (burnsideF4gSpInv_xl_sq 1))
  have hd : burnsideF4jb_xd 1 * z = z * burnsideF4jb_xd 1 :=
    hc _ (burnsideF4jb_mem_oPPrime_of_sq (burnsideF4jb_xd_mem_Q2_one 1) (burnsideF4jb_xd_sq 1))
  have he : burnsideF4jb_xe 1 * z = z * burnsideF4jb_xe 1 :=
    hc _ (burnsideF4jb_mem_oPPrime_of_sq (burnsideF4jb_xe_mem_Q2_one 1) (burnsideF4jb_xe_sq 1))
  have he0 : burnsideF4gSpInv_mv z (Pi.single (Sum.inl 0) 1) = Pi.single (Sum.inl 0) 1 := by
    have h : z ∈ Subgroup.centralizer ({burnsideF4gSpInv_xl (1 : K)} : Set (StatedSp 2 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hl.symm
    rw [burnsideF4gSpInv_centralizer_xl one_ne_zero] at h
    exact h
  have hxe0 : burnsideF4gSpInv_mv (burnsideF4jb_xe (1 : K)) (Pi.single (Sum.inl 0) 1) =
      Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inl 1) 1 := by
    rw [burnsideF4jb_xe_mv]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply]
  have he1 : burnsideF4gSpInv_mv z (Pi.single (Sum.inl 1) 1) = Pi.single (Sum.inl 1) 1 := by
    have h := congrArg (fun g => burnsideF4gSpInv_mv g (Pi.single (Sum.inl 0) 1)) he
    simp only [burnsideF4gSpInv_mv_mul] at h
    rw [he0, hxe0, burnsideF4gSpInv_mv_add, he0] at h
    exact (add_left_cancel h).symm
  have hxdf0 : burnsideF4gSpInv_mv (burnsideF4jb_xd (1 : K)) (Pi.single (Sum.inr 0) 1) =
      Pi.single (Sum.inr 0) 1 - Pi.single (Sum.inr 1) 1 := by
    rw [burnsideF4jb_xd_mv]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply]
  have hxef1 : burnsideF4gSpInv_mv (burnsideF4jb_xe (1 : K)) (Pi.single (Sum.inr 1) 1) =
      Pi.single (Sum.inr 1) 1 - Pi.single (Sum.inr 0) 1 := by
    rw [burnsideF4jb_xe_mv]
    ext i
    rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply]
  have hD := congrArg (fun g => burnsideF4gSpInv_mv g (Pi.single (Sum.inr 0) 1)) hd
  have hE := congrArg (fun g => burnsideF4gSpInv_mv g (Pi.single (Sum.inr 1) 1)) he
  simp only [burnsideF4gSpInv_mv_mul] at hD hE
  rw [hxdf0, burnsideF4gSpInv_mv_sub, burnsideF4jb_xd_mv] at hD
  rw [hxef1, burnsideF4gSpInv_mv_sub, burnsideF4jb_xe_mv] at hE
  have hD1 := congrFun hD (Sum.inl 1)
  have hE0 := congrFun hE (Sum.inl 0)
  have a00 := burnsideF4gSpInv_form_mv z (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1)
  have a01 := burnsideF4gSpInv_form_mv z (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 1) 1)
  have a10 := burnsideF4gSpInv_form_mv z (Pi.single (Sum.inl 1) 1) (Pi.single (Sum.inr 0) 1)
  have a11 := burnsideF4gSpInv_form_mv z (Pi.single (Sum.inl 1) 1) (Pi.single (Sum.inr 1) 1)
  have aff := burnsideF4gSpInv_form_mv z (Pi.single (Sum.inr 0) 1) (Pi.single (Sum.inr 1) 1)
  rw [he0, burnsideF4gSpInv_form_e0_left, burnsideF4gSpInv_form_e0_left] at a00 a01
  rw [he1, burnsideF4jb_form_e1_left, burnsideF4jb_form_e1_left] at a10 a11
  generalize hc1 : burnsideF4gSpInv_mv z (Pi.single (Sum.inr 0) 1) = c1 at *
  generalize hc2 : burnsideF4gSpInv_mv z (Pi.single (Sum.inr 1) 1) = c2 at *
  simp [Pi.single_apply] at a00 a01 a10 a11 hD1 hE0
  simp only [burnsideF4gSpInv_form, a00, a01, a10, a11] at aff
  simp [Pi.single_apply] at aff
  have g21 : c2 (Sum.inl 1) = 0 := by linear_combination hD1
  have g10 : c1 (Sum.inl 0) = 0 := by linear_combination hE0
  have sym : c1 (Sum.inl 1) = c2 (Sum.inl 0) := by linear_combination aff
  refine ⟨c2 (Sum.inl 0), burnsideF4gSpInv_ext fun v => ?_⟩
  conv_lhs => rw [burnsideF4gSpInv_vec_decomp v]
  simp only [burnsideF4gSpInv_mv_add, burnsideF4gSpInv_mv_smul, he0, he1, hc1, hc2]
  rw [burnsideF4gSpInv_xs_mv]
  ext i
  rcases i with i | i <;> fin_cases i <;>
    simp [Pi.single_apply, a00, a01, a10, a11, g21, g10, sym] <;> ring

theorem burnsideF4jb_ctr_oPPrime_Q2_one [CharP K 2] :
    ctr (oPPrime 2 (Q2 K 1)) = burnsideF4gSpInv_Xs K := by
  ext z
  rw [burnsideF4gSpInv_mem_Xs]
  constructor
  · intro hz
    obtain ⟨t, rfl⟩ := burnsideF4jb_ctr_oPPrime_le hz
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact burnsideF4jb_xs_mem_ctr t

theorem burnsideF4jb_torus_mul_xs (a : Fin 2 → Kˣ) (t : K) :
    torusHom a * burnsideF4gSpInv_xs t =
      burnsideF4gSpInv_xs ((a 0 : K) * (a 1 : K) * t) * torusHom a := by
  have h0 : (a 0 : K) ≠ 0 := (a 0).ne_zero
  have h1 : (a 1 : K) ≠ 0 := (a 1).ne_zero
  apply burnsideF4gSpInv_ext
  intro v
  rw [burnsideF4gSpInv_mv_mul, burnsideF4gSpInv_mv_mul, burnsideF4gSpInv_xs_mv,
    burnsideF4gSpInv_xs_mv]
  ext i
  simp only [burnsideF4gSpInv_mv, coe_torusHom, Matrix.mulVec_diagonal, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rcases i with i | i <;> fin_cases i <;> simp [Pi.single_apply] <;> field_simp <;> ring

theorem burnsideF4jb_torus_conj_xs (a : Fin 2 → Kˣ) (t : K) :
    torusHom a * burnsideF4gSpInv_xs t * (torusHom a)⁻¹ =
      burnsideF4gSpInv_xs ((a 0 : K) * (a 1 : K) * t) := by
  rw [burnsideF4jb_torus_mul_xs, mul_inv_cancel_right]

theorem burnsideF4jb_xs_conj {t t' : K} (ht : t ≠ 0) (ht' : t' ≠ 0) :
    ∃ m ∈ Q2 K 0 ⊓ Q2 K 1, m * burnsideF4gSpInv_xs t * m⁻¹ = burnsideF4gSpInv_xs t' := by
  refine ⟨torusHom (Pi.mulSingle 0 (Units.mk0 (t' / t) (div_ne_zero ht' ht))), ?_, ?_⟩
  · rw [burnsideF4gSpInv_Q2_inf_eq_borel]
    exact torus_le_borelSubgroup (torusHom_mem_torus _)
  · rw [burnsideF4jb_torus_conj_xs]
    congr 1
    simp [Pi.mulSingle_apply]
    field_simp

end BurnsideF4jbNative

section BurnsideF4jbTransport

open CFSG.ASVolI.ChF

variable {G E : Type} [Group G] [Group E]

theorem burnsideF4jb_ctr_map (φ : G →* E) (hφ : Function.Injective φ) (H : Subgroup G) :
    ctr (H.map φ) = (ctr H).map φ := by
  ext y
  constructor
  · rintro ⟨hy, hc⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hc (φ h) (Subgroup.mem_map_of_mem _ hh)
    exact hφ (by simpa using this)
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hx, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hc h hh
    simpa using congrArg φ this

end BurnsideF4jbTransport

section BurnsideF4jbFinal

open Matrix CFSG.ASVolI.ChF CFSG.ASVolI.ChF.ClassicalRoots CFSG.QuasithinUnique.Setup.X7a
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem burnsideF4jb_Z2_conj {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : ChF.HypF_4_4 .Sp4 2 f Gp M₁ M₂) :
    (∃ w ∈ ChF.ctr (ChF.oPPrime 2 (Gp ⊓ M₂)), w ≠ 1) ∧
    ∀ w ∈ ChF.ctr (ChF.oPPrime 2 (Gp ⊓ M₂)), w ≠ 1 →
      ∀ w' ∈ ChF.ctr (ChF.oPPrime 2 (Gp ⊓ M₂)), w' ≠ 1 →
        ∃ m ∈ Gp ⊓ (M₁ ⊓ M₂), m * w * m⁻¹ = w' := by
  have hM : hyp.toHypF_4_4g.chart.Matches M₁ M₂ := hyp.toHypF_4_4g.chart_matches
  obtain ⟨marking, hpts, hlines, -, -⟩ :=
    burnsideF4gSpInv_marking_of_chart hyp.toHypF_4_4g.chart
  have hK : Nat.card marking.field = 2 ^ f := by
    have := marking.field_card
    simpa using this
  haveI : CharP marking.field 2 := burnsideF4gSp_charP_of_card hK
  have hbasis : marking.basis = 1 := marking.basis_compatible
  let φ : StatedSp 2 marking.field →* E := Gp.subtype.comp marking.transport
  have hφinj : Function.Injective φ := by
    refine (injective_iff_map_eq_one φ).2 fun a ha => ?_
    have h1 : marking.transport a = 1 := Subtype.ext ha
    have h2 := (burnsideF4f_transport_eq_one_iff marking a).1 h1
    exact Subtype.ext (burnsideF4gSpInv_scalar_eq_one h2 a.2)
  have keyS : ∀ (S : Set (Fin 2 ⊕ Fin 2))
      (W : Submodule marking.field (Fin 2 ⊕ Fin 2 → marking.field))
      (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) marking.field),
      (∀ v, v ∈ coordinateSpace S ↔ v ∈ W) →
      ((∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ coordinateSpace S ↔
          v ∈ coordinateSpace S) ↔
        ∀ v : Fin 2 ⊕ Fin 2 → marking.field, A.mulVec v ∈ W ↔ v ∈ W) := by
    intro S W A hS
    simp only [hS]
  have key : ∀ b : Bool, nativeParabolic .Sp4 (2 ^ f) marking.field marking.basis b =
      Q2 marking.field (if b then 1 else 0) := by
    intro b
    rw [hbasis]
    ext g
    have h1 : g ∈ nativeParabolic .Sp4 (2 ^ f) marking.field 1 b ↔
        (g : GL (Coord .Sp4) marking.field) ∈ rawStabilizer ((fun vector =>
            ((1 : GL (Coord .Sp4) marking.field) : Matrix (Coord .Sp4) (Coord .Sp4)
              marking.field).mulVec vector) ''
          coordinateSpace (if b then flagTwo .Sp4 else flagOne .Sp4 : Set (Coord .Sp4))) :=
      Iff.rfl
    rw [h1, burnsideF4gSp_mem_rawStabilizer, burnsideF4gSp_image_one, Q2]
    refine Iff.trans ?_
      (burnsideF4gSp_mem_stabilizer_iff (r := 2) (K := marking.field) _ g).symm
    cases b
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).1)
    · exact keyS _ _ _ (fun v => (burnsideF4gSp_coordinateSpace_flag v).2)
  have hpar : ∀ b : Bool, (marking.parabolic b).map Gp.subtype =
      (Q2 marking.field (if b then 1 else 0)).map φ := by
    intro b
    have e1 : marking.parabolic b =
        (Q2 marking.field (if b then 1 else 0)).map marking.transport :=
      congrArg (Subgroup.map marking.transport) (key b)
    calc (marking.parabolic b).map Gp.subtype
        = ((Q2 marking.field (if b then 1 else 0)).map marking.transport).map
            Gp.subtype := by rw [e1]
      _ = (Q2 marking.field (if b then 1 else 0)).map
            (Gp.subtype.comp marking.transport) := Subgroup.map_map _ _ _
      _ = (Q2 marking.field (if b then 1 else 0)).map φ := rfl
  have hM₁ : Gp ⊓ M₁ = (Q2 marking.field 0).map φ := by
    rw [hM.2.1, hpts]
    simpa using hpar false
  have hM₂ : Gp ⊓ M₂ = (Q2 marking.field 1).map φ := by
    rw [hM.2.2, hlines]
    simpa using hpar true
  have hB : Gp ⊓ (M₁ ⊓ M₂) = (Q2 marking.field 0 ⊓ Q2 marking.field 1).map φ := by
    rw [Subgroup.map_inf_eq _ _ _ hφinj, ← hM₁, ← hM₂]
    exact inf_inf_distrib_left Gp M₁ M₂
  have hZ : ∀ w : E, w ∈ ctr (oPPrime 2 (Gp ⊓ M₂)) ↔
      ∃ t : marking.field, w = φ (burnsideF4gSpInv_xs t) := by
    intro w
    rw [hM₂, burnsideF4d_oPPrime_map φ hφinj, burnsideF4jb_ctr_map φ hφinj,
      burnsideF4jb_ctr_oPPrime_Q2_one]
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨t, rfl⟩ := burnsideF4gSpInv_mem_Xs.1 hz
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact Subgroup.mem_map_of_mem φ (burnsideF4gSpInv_mem_Xs.2 ⟨t, rfl⟩)
  have hne : ∀ t : marking.field, φ (burnsideF4gSpInv_xs t) ≠ 1 → t ≠ 0 := by
    rintro t ht rfl
    exact ht (by rw [burnsideF4gSpInv_xs_zero, map_one])
  refine ⟨⟨φ (burnsideF4gSpInv_xs 1), (hZ _).2 ⟨1, rfl⟩, fun h => ?_⟩, ?_⟩
  · exact burnsideF4gSpInv_xs_ne_one (K := marking.field) one_ne_zero
      (hφinj (h.trans (map_one φ).symm))
  · intro w hw hw1 w' hw' hw1'
    obtain ⟨t, rfl⟩ := (hZ w).1 hw
    obtain ⟨t', rfl⟩ := (hZ w').1 hw'
    obtain ⟨m, hm, hmc⟩ := burnsideF4jb_xs_conj (hne t hw1) (hne t' hw1')
    refine ⟨φ m, ?_, ?_⟩
    · rw [hB]
      exact Subgroup.mem_map_of_mem φ hm
    · rw [← hmc, map_mul, map_mul, map_inv]

end BurnsideF4jbFinal

end PartBurnsideF4jSp

section PartBurnsideF4j

section RestrictHyp

open CFSG.ASVolI.ChF CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem burnsideF4j_isGenLie_congr {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {κ : GLKind}
    {p f : ℕ} (h : IsGenLie H κ p f) : IsGenLie H' κ p f := by
  cases κ
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, σ, hσ, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc (Exists.intro σ (And.intro hσ ⟨e.symm.trans e'⟩)))))))
  · obtain ⟨h1, h2, h3 | h3⟩ := h
    · obtain ⟨h4, K, fK, finK, hc, ⟨e'⟩⟩ := h3
      exact And.intro h1 (And.intro h2 (Or.inl (And.intro h4 (Exists.intro K (Exists.intro fK
        (Exists.intro finK (And.intro hc ⟨e.symm.trans e'⟩)))))))
    · obtain ⟨h4, h5, a, ha, K, fK, finK, hc, ⟨e'⟩⟩ := h3
      exact And.intro h1 (And.intro h2 (Or.inr (And.intro h4 (And.intro h5 (Exists.intro a
        (And.intro ha (Exists.intro K (Exists.intro fK (Exists.intro finK
          (And.intro hc ⟨e.symm.trans e'⟩))))))))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (Exists.intro K (Exists.intro fK (Exists.intro finK
      (And.intro hc ⟨e.symm.trans e'⟩)))))
  · obtain ⟨h1, h2, h3, a, ha, K, fK, finK, hc, ⟨e'⟩⟩ := h
    exact And.intro h1 (And.intro h2 (And.intro h3 (Exists.intro a (And.intro ha
      (Exists.intro K (Exists.intro fK (Exists.intro finK (And.intro hc ⟨e.symm.trans e'⟩))))))))

end RestrictHyp

section RestrictChart

open CFSG.ASVolI.ChF

theorem burnsideF4j_map_trans {A B C : Type} [Group A] [Group B] [Group C] (f : A ≃* B)
    (e : B ≃* C) (X : Subgroup A) :
    X.map (f.trans e).toMonoidHom = (X.map f.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

@[expose] def burnsideF4j_markingMap {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H') :
    ClassicalRoots.Marking kind p exponent H' :=
  { m with identification := m.identification.trans e }

theorem burnsideF4j_markingMap_borel {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H') :
    (burnsideF4j_markingMap m e).borel = m.borel.map e.toMonoidHom := by
  unfold ClassicalRoots.Marking.borel ClassicalRoots.Marking.transport
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4j_markingMap_parabolic {kind : ClassicalRoots.Kind} {p exponent : ℕ}
    {H H' : Type} [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H)
    (e : H ≃* H') (b : Bool) :
    (burnsideF4j_markingMap m e).parabolic b = (m.parabolic b).map e.toMonoidHom := by
  unfold ClassicalRoots.Marking.parabolic ClassicalRoots.Marking.transport
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4j_markingMap_root {kind : ClassicalRoots.Kind} {p exponent : ℕ} {H H' : Type}
    [Group H] [Group H'] (m : ClassicalRoots.Marking kind p exponent H) (e : H ≃* H')
    (r : ClassicalRoots.PositiveRoot) (b : Bool) :
    (burnsideF4j_markingMap m e).root r b = (m.root r b).map e.toMonoidHom := by
  unfold ClassicalRoots.Marking.root ClassicalRoots.Marking.transport
  rw [Subgroup.map_map]
  rfl

theorem burnsideF4j_fullImage_trans {K : Type} [Field K] [Finite K] {H H' : Type} [Group H]
    [Group H'] (m : G2Native.FullModel K ≃* H) (e : H ≃* H') (X : Subgroup (G2Native.Parent K)) :
    G2Native.fullImage K (m.trans e) X = (G2Native.fullImage K m X).map e.toMonoidHom :=
  burnsideF4j_map_trans _ _ _

theorem burnsideF4j_smallImage_trans {K : Type} [Field K] [Finite K] {H H' : Type} [Group H]
    [Group H'] (m : G2Native.SmallModel K ≃* H) (e : H ≃* H') (X : Subgroup (G2Native.Parent K)) :
    G2Native.smallImage K (m.trans e) X = (G2Native.smallImage K m X).map e.toMonoidHom :=
  burnsideF4j_map_trans _ _ _

variable {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF4j_restrict_eq (Y : Subgroup ↥Gp) (Z : Subgroup E) (hZ : Z = Y.map Gp.subtype) :
    Z.subgroupOf Gp =
      (Y.map (Subgroup.topEquiv (G := ↥Gp)).symm.toMonoidHom).map (⊤ : Subgroup ↥Gp).subtype := by
  rw [hZ, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Gp.subtype_injective,
    Subgroup.map_map]
  have : ((⊤ : Subgroup ↥Gp).subtype.comp (Subgroup.topEquiv (G := ↥Gp)).symm.toMonoidHom) =
      MonoidHom.id ↥Gp := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

end RestrictChart

section RestrictChart2

open CFSG.ASVolI.ChF

variable {E : Type} [Group E] {Gp : Subgroup E}

theorem burnsideF4j_chart_restrict {κ : GLKind} {p f : ℕ} {M₁ M₂ : Subgroup E}
    (chart : NativeChart κ p f Gp) (hm : chart.Matches M₁ M₂) :
    ∃ chart' : NativeChart κ p f (⊤ : Subgroup ↥Gp),
      chart'.Matches ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp) := by
  obtain ⟨hb, hpt, hl⟩ := hm
  let e : ↥Gp ≃* ↥(⊤ : Subgroup ↥Gp) := (Subgroup.topEquiv (G := ↥Gp)).symm
  have hm1 : (⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp) =
      chart.borel.subgroupOf Gp := by
    ext x
    have hx := x.2
    simp only [Subgroup.mem_inf, Subgroup.mem_top, Subgroup.mem_subgroupOf, true_and]
    rw [← hb]
    simp only [Subgroup.mem_inf]
    tauto
  have hm2 : (⊤ : Subgroup ↥Gp) ⊓ (Gp ⊓ M₁).subgroupOf Gp = chart.points.subgroupOf Gp := by
    rw [top_inf_eq, ← hpt]
  have hm3 : (⊤ : Subgroup ↥Gp) ⊓ (Gp ⊓ M₂).subgroupOf Gp = chart.lines.subgroupOf Gp := by
    rw [top_inf_eq, ← hl]
  have hmatch := And.intro hm1 (And.intro hm2 hm3)
  rcases chart.coordinates with
    ⟨c, hk, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, card, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking, h1, h2, h3, h4, h5⟩ |
    ⟨hp, exponent, K, fK, finK, charK, scope,
      ⟨hk, hd, marking, h1, h2, h3, h4, h5⟩ | ⟨hk, hd, he, marking, h1, h2, h3, h4, h5⟩⟩
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inl ⟨c, hk, burnsideF4j_markingMap marking e, ?_, ?_, ?_, ?_, ?_⟩⟩, hmatch⟩
    · rw [burnsideF4j_markingMap_borel]; exact burnsideF4j_restrict_eq _ _ h1
    · rw [burnsideF4j_markingMap_parabolic]; exact burnsideF4j_restrict_eq _ _ h2
    · rw [burnsideF4j_markingMap_parabolic]; exact burnsideF4j_restrict_eq _ _ h3
    · rw [burnsideF4j_markingMap_root]; exact burnsideF4j_restrict_eq _ _ h4
    · rw [burnsideF4j_markingMap_root]; exact burnsideF4j_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inl ⟨hk, hp, hd, K, fK, finK, card, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩)⟩,
        hmatch⟩
    · rw [burnsideF4j_fullImage_trans]; exact burnsideF4j_restrict_eq _ _ h1
    · rw [burnsideF4j_fullImage_trans]; exact burnsideF4j_restrict_eq _ _ h2
    · rw [burnsideF4j_fullImage_trans]; exact burnsideF4j_restrict_eq _ _ h3
    · rw [burnsideF4j_fullImage_trans]; exact burnsideF4j_restrict_eq _ _ h4
    · rw [burnsideF4j_fullImage_trans]; exact burnsideF4j_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inl ⟨hk, hp, hd, K, fK, finK, card, marking.trans e, ?_, ?_, ?_, ?_,
        ?_⟩))⟩, hmatch⟩
    · rw [burnsideF4j_smallImage_trans]; exact burnsideF4j_restrict_eq _ _ h1
    · rw [burnsideF4j_smallImage_trans]; exact burnsideF4j_restrict_eq _ _ h2
    · rw [burnsideF4j_smallImage_trans]; exact burnsideF4j_restrict_eq _ _ h3
    · rw [burnsideF4j_smallImage_trans]; exact burnsideF4j_restrict_eq _ _ h4
    · rw [burnsideF4j_smallImage_trans]; exact burnsideF4j_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inr (Or.inl ⟨hk, hp, hd, K, fK, finK, sigma, scope, marking.trans e,
        ?_, ?_, ?_, ?_, ?_⟩)))⟩, hmatch⟩
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h1
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h2
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h3
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h4
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, exponent, K, fK, finK, charK, scope,
        Or.inl ⟨hk, hd, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩⟩)))⟩, hmatch⟩
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h1
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h2
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h3
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h4
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h5
  · refine ⟨⟨chart.borel.subgroupOf Gp, chart.points.subgroupOf Gp, chart.lines.subgroupOf Gp,
      chart.longRoot.subgroupOf Gp, chart.shortRoot.subgroupOf Gp,
      Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, exponent, K, fK, finK, charK, scope,
        Or.inr ⟨hk, hd, he, marking.trans e, ?_, ?_, ?_, ?_, ?_⟩⟩)))⟩, hmatch⟩
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h1
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h2
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h3
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h4
    · rw [burnsideF4j_map_trans]; exact burnsideF4j_restrict_eq _ _ h5

end RestrictChart2

section RestrictHyp2

open CFSG.ASVolI.ChF

theorem burnsideF4j_parabolics (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂) := by
  obtain ⟨h1, h2, h3⟩ := hyp.toHypF_4_4g.chart_matches
  have hlp := (hcompat κ p f E Gp hyp.toHypF_4_4g.chart).1
  rw [← h1, ← h2, ← h3] at hlp
  exact hlp

theorem burnsideF4j_parabolics_gen {E : Type} [Group E] {p : ℕ} {H B P₁ P₂ : Subgroup E}
    (hP : IsLieParabolics p H B P₁ P₂) : P₁ ⊔ P₂ = H := by
  obtain ⟨-, hne, -, hmax⟩ := hP
  obtain ⟨-, hP1H, -, hP1max⟩ := (hmax P₁).mpr (Or.inl rfl)
  obtain ⟨-, hP2H, -, hP2max⟩ := (hmax P₂).mpr (Or.inr rfl)
  by_contra hR
  have hRle : P₁ ⊔ P₂ ≤ H := sup_le hP1H hP2H
  have h1 : P₁ ⊔ P₂ = P₁ := by
    by_contra h
    exact hR (hP1max _ (lt_of_le_of_ne le_sup_left (Ne.symm h)) hRle)
  have h2 : P₁ ⊔ P₂ = P₂ := by
    by_contra h
    exact hR (hP2max _ (lt_of_le_of_ne le_sup_right (Ne.symm h)) hRle)
  exact hne (h1.symm.trans h2)

theorem burnsideF4j_mem_normalizer_subgroupOf {E : Type} [Group E] {Gp X : Subgroup E}
    (hX : X ≤ Gp) (g : ↥Gp) :
    g ∈ Subgroup.normalizer ((X.subgroupOf Gp : Subgroup ↥Gp) : Set ↥Gp) ↔
      (g : E) ∈ Subgroup.normalizer (X : Set E) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    by_cases hx : x ∈ Gp
    · have := h ⟨x, hx⟩
      simpa [Subgroup.mem_subgroupOf] using this
    · constructor
      · intro hxX
        exact absurd (hX hxX) hx
      · intro hgx
        exfalso
        apply hx
        have h1 : (g : E)⁻¹ * ((g : E) * x * (g : E)⁻¹) * (g : E) ∈ Gp :=
          Gp.mul_mem (Gp.mul_mem (Gp.inv_mem g.2) (hX hgx)) g.2
        simpa [mul_assoc] using h1
  · intro h x
    have := h (x : E)
    simpa [Subgroup.mem_subgroupOf] using this

theorem burnsideF4j_restrict (hcompat : NativeChartCompatibilityGoal) {κ : GLKind} {p f : ℕ}
    {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) :
    HypF_4_4 κ p f (⊤ : Subgroup ↥Gp) ((Gp ⊓ M₁).subgroupOf Gp) ((Gp ⊓ M₂).subgroupOf Gp) := by
  haveI := hyp.finite
  have hP := burnsideF4j_parabolics hcompat hyp
  obtain ⟨chart, hchart⟩ := hyp.lie_amalgam
  obtain ⟨chart', hchart'⟩ := burnsideF4j_chart_restrict chart hchart
  have hBB : (⊤ : Subgroup ↥Gp) ⊓ ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp) =
      (Gp ⊓ (M₁ ⊓ M₂)).subgroupOf Gp := by
    ext x
    have hx := x.2
    simp only [Subgroup.mem_inf, Subgroup.mem_top, Subgroup.mem_subgroupOf, true_and]
    tauto
  refine ⟨⟨inferInstance, burnsideF4j_isGenLie_congr (Subgroup.topEquiv (G := ↥Gp)).symm hyp.model,
    inferInstance, ?_, ?_, ⟨chart', hchart'⟩, fun e => ⟨e, Subgroup.mem_top _, 1,
      Subgroup.one_mem _, (mul_one e).symm⟩, ?_⟩, fun _ => rfl⟩
  ·
    rw [eq_bot_iff]
    intro z hz
    have h1 : (z : E) ∈ Subgroup.centralizer (Gp : Set E) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := (Subgroup.mem_centralizer_iff.mp hz) ⟨g, hg⟩ (Subgroup.mem_top _)
      exact congrArg Subtype.val this
    rw [hyp.centralizer_trivial] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  ·
    apply Subgroup.map_injective Gp.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_left,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left, burnsideF4j_parabolics_gen hP,
      Subgroup.map_top, Subgroup.range_subtype]
  ·
    intro g hg
    rw [hBB, burnsideF4j_mem_normalizer_subgroupOf inf_le_left] at hg
    rw [top_inf_eq, burnsideF4j_mem_normalizer_subgroupOf inf_le_left]
    exact hyp.dynkin g hg

end RestrictHyp2

section Transport

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique

theorem burnsideF4j_ctr_map {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (X : Subgroup A) : ctr (X.map φ) = (ctr X).map φ := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, rfl⟩
    have := (Subgroup.mem_centralizer_iff.1 hc) (φ h) ⟨h, hh, rfl⟩
    apply hφ
    simpa using this
  · rintro ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have := (Subgroup.mem_centralizer_iff.1 hc) h hh
    simpa using congrArg φ this

theorem burnsideF4j_pCoreOf_map {A B : Type} [Group A] [Group B] (φ : A →* B)
    (hφ : Function.Injective φ) (X : Subgroup A) :
    pCoreOf 2 (X.map φ) = (pCoreOf 2 X).map φ := by
  let ψ : ↥X ≃* ↥(X.map φ) := X.equivMapOfInjective φ hφ
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 ψ, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem burnsideF4j_conj_mem_ctr {G : Type} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ ctr K) :
    g * x * g⁻¹ ∈ ctr K := by
  obtain ⟨hxK, hxc⟩ := hx
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hxK, Subgroup.mem_centralizer_iff.2 ?_⟩
  intro k hk
  have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hg' k).1 hk
  have hc := (Subgroup.mem_centralizer_iff.1 hxc) _ hk'
  simp only [inv_inv] at hc
  calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * k := by group

theorem burnsideF4j_mem_normalizer_ctr {G : Type} [Group G] {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer (ctr K : Set G) := by
  have hg' : g⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hg
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => burnsideF4j_conj_mem_ctr hg hx,
    fun hx => ?_⟩
  have := burnsideF4j_conj_mem_ctr hg' hx
  simpa [mul_assoc] using this

theorem burnsideF4j_centralizer_conj {G : Type} [Group G] (c a : G) :
    Subgroup.centralizer ({c * a * c⁻¹} : Set G) =
      conjSub c (Subgroup.centralizer ({a} : Set G)) := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, mem_conjSub,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc c⁻¹ * y * c * a = c⁻¹ * (y * (c * a * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * a * c⁻¹) * y) * c := by rw [h]
      _ = a * (c⁻¹ * y * c) := by group
  · intro h
    calc y * (c * a * c⁻¹) = c * ((c⁻¹ * y * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * y * c)) * c⁻¹ := by rw [h]
      _ = c * a * c⁻¹ * y := by group

theorem burnsideF4j_card_conjSub {G : Type} [Group G] (g : G) (K : Subgroup G) :
    Nat.card (conjSub g K) = Nat.card K :=
  (Nat.card_congr (K.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv).symm

theorem burnsideF4j_conj_into_normalizer {P : Type} [Group P] [Finite P] {S : Subgroup P}
    (hS : IsSylowTwoOf S ⊤) {a b c : P} (hab : c * a * c⁻¹ = b)
    (hSa : S ≤ Subgroup.centralizer ({a} : Set P))
    (hSb : S ≤ Subgroup.centralizer ({b} : Set P)) :
    ∃ m ∈ Subgroup.normalizer (S : Set P), m * a * m⁻¹ = b := by
  have hCb : Subgroup.centralizer ({b} : Set P) =
      conjSub c (Subgroup.centralizer ({a} : Set P)) := by
    rw [← hab]; exact burnsideF4j_centralizer_conj c a
  have h1 : conjSub c⁻¹ S ≤ Subgroup.centralizer ({a} : Set P) := by
    have := conjSub_mono c⁻¹ (hSb.trans hCb.le)
    rwa [conjSub_conjSub_inv] at this
  have hSyl : IsSylowTwoOf S (Subgroup.centralizer ({a} : Set P)) :=
    F7.isSylowTwoOf_mono_right hS hSa le_top
  obtain ⟨x, hx, hle⟩ := F7.isSylowTwoOf_exists_conj_le hSyl h1 (F7.isPGroup_conjSub hS.2.1)
  have heq : conjSub c⁻¹ S = conjSub x S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [burnsideF4j_card_conjSub, burnsideF4j_card_conjSub])
  have hN : conjSub (c * x) S = S := by
    rw [conjSub_mul, ← heq, ← conjSub_mul, mul_inv_cancel, conjSub_one]
  refine ⟨c * x, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : (c * x) * y * (c * x)⁻¹ ∈ conjSub (c * x) S := by
        rw [mem_conjSub]; simpa [mul_assoc] using hy
      rwa [hN] at this
    · intro hy
      rw [← hN, mem_conjSub] at hy
      simpa [mul_assoc] using hy
  · have hxa : x * a * x⁻¹ = a := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hx
      calc x * a * x⁻¹ = a * x * x⁻¹ := by rw [this]
        _ = a := by group
    calc c * x * a * (c * x)⁻¹ = c * (x * a * x⁻¹) * c⁻¹ := by group
      _ = b := by rw [hxa, hab]

theorem burnsideF4j_isConj_of_unique {P : Type} [Group P] {X : Subgroup P}
    (huniq : ∃! C : ConjClasses P, C ∈ InvClasses P ∧ ClassMeetsCenter X C)
    {a b : P} (ha1 : a ≠ 1) (ha2 : a * a = 1) (hb1 : b ≠ 1) (hb2 : b * b = 1)
    (ha : ∃ c : P, c * a * c⁻¹ ∈ ctr X) (hb : ∃ c : P, c * b * c⁻¹ ∈ ctr X) : IsConj a b := by
  have key : ∀ y : P, y ≠ 1 → y * y = 1 → (∃ c : P, c * y * c⁻¹ ∈ ctr X) →
      ConjClasses.mk y ∈ InvClasses P ∧ ClassMeetsCenter X (ConjClasses.mk y) := by
    intro y hy1 hy2 ⟨c, hc⟩
    refine ⟨⟨y, ConjClasses.mem_carrier_mk, hy1, hy2⟩, ⟨c * y * c⁻¹, ?_, hc⟩⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
    exact (isConj_iff.2 ⟨c, rfl⟩).symm
  obtain ⟨C, -, hC⟩ := huniq
  have h1 := hC _ (key a ha1 ha2 ha)
  have h2 := hC _ (key b hb1 hb2 hb)
  exact ConjClasses.mk_eq_mk_iff_isConj.1 (h1.trans h2.symm)

end Transport

section F427Lie

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique

set_option linter.unusedSectionVars false


theorem burnsideF4j_top_long_isConj {κ : GLKind} {f : ℕ} {P : Type} [Group P]
    {M₁ M₂ : Subgroup P} (hyp : HypF_4_4 κ 2 f (⊤ : Subgroup P) M₁ M₂) (hL3 : κ ≠ .L3)
    (hG2d : κ ≠ .G2d) {w w' : P} (hw : hyp.toHypF_4_4g.chart.RootInvolution false w)
    (hw' : hyp.toHypF_4_4g.chart.RootInvolution false w') : IsConj w w' := by
  have h27 := as_F_4_27 κ f P ⊤ M₁ M₂ hyp rfl
  dsimp only at h27
  obtain ⟨-, -, h2, h3, -, -⟩ := h27
  by_cases hSp : κ = .Sp4
  · subst hSp
    obtain ⟨-, -, long, -, -, -, -, -, -, -, -, -, -, -, -, hRL, -, -⟩ := h2 rfl
    exact ((hRL w).1 hw).trans ((hRL w').1 hw').symm
  · obtain ⟨-, huniq, -, hlong, -⟩ := h3 ⟨hL3, hSp, hG2d⟩
    obtain ⟨c, -, hc⟩ := (hlong w hw.2.1 hw.2.2.1).1 hw
    obtain ⟨c', -, hc'⟩ := (hlong w' hw'.2.1 hw'.2.2.1).1 hw'
    exact burnsideF4j_isConj_of_unique huniq hw.2.1 hw.2.2.1 hw'.2.1 hw'.2.2.1 ⟨c, hc⟩ ⟨c', hc'⟩

theorem burnsideF4j_top_sylow {κ : GLKind} {f : ℕ} {P : Type} [Group P]
    {M₁ M₂ : Subgroup P} (hyp : HypF_4_4 κ 2 f (⊤ : Subgroup P) M₁ M₂) :
    ∃ S : Subgroup P, IsSylowTwoOf S ⊤ ∧ M₁ ⊓ M₂ = Subgroup.normalizer (S : Set P) := by
  obtain ⟨⟨S, hS, hB⟩, -⟩ := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  refine ⟨S, hS, ?_⟩
  rw [top_inf_eq, top_inf_eq] at hB
  exact hB

theorem burnsideF4j_top_Z1_conj {κ : GLKind} {f : ℕ} {P : Type} [Group P]
    {M₁ M₂ : Subgroup P} (hyp : HypF_4_4 κ 2 f (⊤ : Subgroup P) M₁ M₂) (hL3 : κ ≠ .L3)
    (hG2d : κ ≠ .G2d) {w w' : P} (hw : w ∈ ctr (oPPrime 2 M₁)) (hw1 : w ≠ 1)
    (hw' : w' ∈ ctr (oPPrime 2 M₁)) (hw1' : w' ≠ 1) :
    ∃ m ∈ M₁ ⊓ M₂, m * w * m⁻¹ = w' := by
  haveI := hyp.finite
  have h27 := as_F_4_27 κ f P ⊤ M₁ M₂ hyp rfl
  dsimp only at h27
  obtain ⟨-, -, -, -, h4, -⟩ := h27
  obtain ⟨hZ1, -⟩ := h4 hL3
  have hlw := (hZ1 w hw hw1).1 hG2d
  have hlw' := (hZ1 w' hw' hw1').1 hG2d
  obtain ⟨c, hc⟩ := isConj_iff.1 (burnsideF4j_top_long_isConj hyp hL3 hG2d hlw hlw')
  obtain ⟨S, hS, hB⟩ := burnsideF4j_top_sylow hyp
  have hSM : S ≤ M₁ := by
    have : S ≤ M₁ ⊓ M₂ := hB ▸ Subgroup.le_normalizer
    exact this.trans inf_le_left
  have hSO : S ≤ oPPrime 2 M₁ := burnsideF4d_Z1_le_oPPrime hS.2.1 hSM
  have hcent : ∀ x ∈ ctr (oPPrime 2 M₁), S ≤ Subgroup.centralizer ({x} : Set P) := by
    intro x hx s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx.2) s (hSO hs)
  obtain ⟨m, hm, hmw⟩ := burnsideF4j_conj_into_normalizer hS hc (hcent w hw) (hcent w' hw')
  exact ⟨m, hB ▸ hm, hmw⟩

theorem burnsideF4j_top_ZS_inv_mem_Z1 {κ : GLKind} {f : ℕ} {P : Type} [Group P]
    {M₁ M₂ : Subgroup P} (hyp : HypF_4_4 κ 2 f (⊤ : Subgroup P) M₁ M₂) (hL3 : κ ≠ .L3)
    (hSp : κ ≠ .Sp4) (hG2d : κ ≠ .G2d) {z : P} (hz : z ∈ ctr (oPPrime 2 M₁)) (hz1 : z ≠ 1)
    {w : P} (hw : w ∈ ctr (pCoreOf 2 (M₁ ⊓ M₂))) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    w ∈ ctr (oPPrime 2 M₁) := by
  haveI := hyp.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h27 := as_F_4_27 κ f P ⊤ M₁ M₂ hyp rfl
  dsimp only at h27
  obtain ⟨-, -, -, h3, h4, -⟩ := h27
  obtain ⟨-, huniq, -, hlong, -⟩ := h3 ⟨hL3, hSp, hG2d⟩
  obtain ⟨hZ1, -⟩ := h4 hL3
  have hlz := (hZ1 z hz hz1).1 hG2d
  have hlw : hyp.toHypF_4_4g.chart.RootInvolution false w :=
    (hlong w hw1 hw2).2 ⟨1, Subgroup.mem_top _, by simpa using hw⟩
  obtain ⟨c, hc⟩ := isConj_iff.1 (burnsideF4j_top_long_isConj hyp hL3 hG2d hlz hlw)
  obtain ⟨S, hS, hB⟩ := burnsideF4j_top_sylow hyp
  have hSB : S ≤ M₁ ⊓ M₂ := hB ▸ Subgroup.le_normalizer
  have hSM : S ≤ M₁ := hSB.trans inf_le_left
  have hSO : S ≤ oPPrime 2 M₁ := burnsideF4d_Z1_le_oPPrime hS.2.1 hSM
  have hSP : S ≤ pCoreOf 2 (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSB hB.le hS.2.1
  have hSz : S ≤ Subgroup.centralizer ({z} : Set P) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hz.2) s (hSO hs)
  have hSw : S ≤ Subgroup.centralizer ({w} : Set P) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hw.2) s (hSP hs)
  obtain ⟨m, hm, hmw⟩ := burnsideF4j_conj_into_normalizer hS hc hSz hSw
  have hmM : m ∈ M₁ := (hB ▸ hm : m ∈ M₁ ⊓ M₂).1
  rw [← hmw]
  exact burnsideF4j_conj_mem_ctr
    (burnsideF4d_le_normalizer_oPPrime M₁ hmM) hz

theorem burnsideF4j_inf_eq_map {E : Type} [Group E] (Gp X : Subgroup E) :
    Gp ⊓ X = ((Gp ⊓ X).subgroupOf Gp).map Gp.subtype :=
  (Subgroup.map_subgroupOf_eq_of_le inf_le_left).symm

theorem burnsideF4j_inf_inf_eq_map {E : Type} [Group E] (Gp M₁ M₂ : Subgroup E) :
    Gp ⊓ (M₁ ⊓ M₂) =
      ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp).map Gp.subtype := by
  rw [Subgroup.map_inf _ _ _ Gp.subtype_injective, ← burnsideF4j_inf_eq_map,
    ← burnsideF4j_inf_eq_map]
  ext x
  simp only [Subgroup.mem_inf]
  tauto

theorem burnsideF4j_Z1_conj {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3) (hG2d : κ ≠ .G2d) {w w' : E}
    (hw : w ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hw1 : w ≠ 1)
    (hw' : w' ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hw1' : w' ≠ 1) :
    ∃ m ∈ Gp ⊓ (M₁ ⊓ M₂), m * w * m⁻¹ = w' := by
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp
  have hZ : ctr (oPPrime 2 (Gp ⊓ M₁)) =
      (ctr (oPPrime 2 ((Gp ⊓ M₁).subgroupOf Gp))).map Gp.subtype := by
    rw [burnsideF4j_inf_eq_map Gp M₁, burnsideF4d_oPPrime_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective, ← burnsideF4j_inf_eq_map]
  rw [hZ] at hw hw'
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨w₀', hw₀', rfl⟩ := hw'
  have h1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; rfl)
  have h1' : w₀' ≠ 1 := fun h => hw1' (by rw [h]; rfl)
  obtain ⟨m, hm, hmw⟩ := burnsideF4j_top_Z1_conj hyp' hL3 hG2d hw₀ h1 hw₀' h1'
  refine ⟨(m : E), ?_, ?_⟩
  · rw [burnsideF4j_inf_inf_eq_map]
    exact ⟨m, hm, rfl⟩
  · rw [← hmw]
    rfl

theorem burnsideF4j_ZS_inv_mem_Z1 {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4)
    (hG2d : κ ≠ .G2d) {z : E} (hz : z ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hz1 : z ≠ 1) {w : E}
    (hw : w ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))) (hw1 : w ≠ 1) (hw2 : w * w = 1) :
    w ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp
  have hZ : ctr (oPPrime 2 (Gp ⊓ M₁)) =
      (ctr (oPPrime 2 ((Gp ⊓ M₁).subgroupOf Gp))).map Gp.subtype := by
    rw [burnsideF4j_inf_eq_map Gp M₁, burnsideF4d_oPPrime_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective, ← burnsideF4j_inf_eq_map]
  have hS : ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) =
      (ctr (pCoreOf 2 ((Gp ⊓ M₁).subgroupOf Gp ⊓ (Gp ⊓ M₂).subgroupOf Gp))).map Gp.subtype := by
    rw [burnsideF4j_inf_inf_eq_map, burnsideF4j_pCoreOf_map _ Gp.subtype_injective,
      burnsideF4j_ctr_map _ Gp.subtype_injective]
  rw [hZ] at hz ⊢
  rw [hS] at hw
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  have h1 : z₀ ≠ 1 := fun h => hz1 (by rw [h]; rfl)
  have h2 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; rfl)
  have h3 : w₀ * w₀ = 1 := Subtype.ext hw2
  exact ⟨w₀, burnsideF4j_top_ZS_inv_mem_Z1 hyp' hL3 hSp hG2d hz₀ h1 hw₀ h2 h3, rfl⟩

end F427Lie

section MSide

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF4j_ctr_subgroupOf {G : Type} [Group G] {N X : Subgroup G} (hX : X ≤ N) :
    ctr (X.subgroupOf N) = (ctr X).subgroupOf N := by
  ext y
  simp only [ctr, Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff,
    SetLike.mem_coe]
  constructor
  · rintro ⟨hy, hc⟩
    refine ⟨hy, fun k hk => ?_⟩
    have := hc ⟨k, hX hk⟩ hk
    exact congrArg Subtype.val this
  · rintro ⟨hy, hc⟩
    exact ⟨hy, fun k hk => Subtype.ext (hc k hk)⟩

theorem burnsideF4j_ctr_subImg {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) :
    ctr (subImg b X) = subImg b (ctr X) := by
  unfold subImg
  rw [burnsideF4j_ctr_map b hb, burnsideF4j_ctr_subgroupOf hX]

theorem burnsideF4j_trans_subImg {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) {X H : Subgroup Mb} (hX : X ≤ N) (hH : H ≤ N)
    (htr : ∀ w ∈ X, w ≠ 1 → ∀ w' ∈ X, w' ≠ 1 → ∃ m ∈ H, m * w * m⁻¹ = w') :
    ∀ x ∈ subImg b X, x ≠ 1 → ∀ x' ∈ subImg b X, x' ≠ 1 →
      ∃ h ∈ subImg b H, h * x * h⁻¹ = x' := by
  intro x hx hx1 x' hx' hx1'
  obtain ⟨w, hwN, hwX, rfl⟩ := mem_subImg.mp hx
  obtain ⟨w', hwN', hwX', rfl⟩ := mem_subImg.mp hx'
  have hw1 : w ≠ 1 := by
    rintro rfl
    exact hx1 (by rw [show (⟨1, hwN⟩ : ↥N) = 1 from rfl, map_one])
  have hw1' : w' ≠ 1 := by
    rintro rfl
    exact hx1' (by rw [show (⟨1, hwN'⟩ : ↥N) = 1 from rfl, map_one])
  obtain ⟨m, hm, hmw⟩ := htr w hwX hw1 w' hwX' hw1'
  refine ⟨b ⟨m, hH hm⟩, mem_subImg_of_mem b (hH hm) hm, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (by simp [hmw])

theorem burnsideF4j_TI_of_trans {G : Type} [Group G] {Z H : Subgroup G} {z : G} (hz : z ∈ Z)
    (hz1 : z ≠ 1) (hC : Subgroup.centralizer ({z} : Set G) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Z : Set G))
    (htr : ∀ x ∈ Z, x ≠ 1 → ∃ h ∈ H, h * z * h⁻¹ = x) :
    IsTISet Z ∧ H = Subgroup.normalizer (Z : Set G) := by
  have hNH : Subgroup.normalizer (Z : Set G) ≤ H := by
    intro g hg
    have hgz : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.1 hg z).1 hz
    have hgz1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    obtain ⟨h, hh, hhz⟩ := htr _ hgz hgz1
    have hc : h⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h⁻¹ * g * z = h⁻¹ * (g * z * g⁻¹) * g := by group
        _ = h⁻¹ * (h * z * h⁻¹) * g := by rw [hhz]
        _ = z * (h⁻¹ * g) := by group
    have := H.mul_mem hh (hC hc)
    simpa using this
  have heq : H = Subgroup.normalizer (Z : Set G) := le_antisymm hHN hNH
  refine ⟨fun g => ?_, heq⟩
  by_cases hbot : Z ⊓ cj g Z = ⊥
  · exact Or.inr hbot
  · left
    obtain ⟨x, hx, hx1⟩ : ∃ x ∈ Z ⊓ cj g Z, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hbot ((Subgroup.eq_bot_iff_forall _).mpr hcon)
    obtain ⟨hxZ, y, hyZ, hyx⟩ := hx
    have hyx' : g * y * g⁻¹ = x := by simpa [MulAut.conj_apply] using hyx
    have hy1 : y ≠ 1 := by
      rintro rfl
      apply hx1
      rw [← hyx']
      group
    obtain ⟨h, hh, hhz⟩ := htr x hxZ hx1
    obtain ⟨h', hh', hhz'⟩ := htr y hyZ hy1
    have hc : h⁻¹ * g * h' ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc h⁻¹ * g * h' * z = h⁻¹ * (g * (h' * z * h'⁻¹) * g⁻¹) * (g * h') := by group
        _ = h⁻¹ * (g * y * g⁻¹) * (g * h') := by rw [hhz']
        _ = h⁻¹ * (h * z * h⁻¹) * (g * h') := by rw [hyx', hhz]
        _ = z * (h⁻¹ * g * h') := by group
    have hgH : g ∈ H := by
      have := H.mul_mem (H.mul_mem hh (hC hc)) (H.inv_mem hh')
      simpa [mul_assoc] using this
    have hgN := hHN hgH
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hgN v).1 hv
    · intro hw
      refine ⟨g⁻¹ * w * g, (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hgN) w).1 hw |>
        fun h => by simpa using h, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]

theorem burnsideF4j_bOne_injective {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    Function.Injective (burnsideF4d_bOne β ε) :=
  hyp.inj.comp (f1_injective β hyp.faithful)

theorem burnsideF4j_bTwo_injective {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    Function.Injective (burnsideF4d_bTwo β ε) :=
  hyp.inj.comp (f2_injective β hyp.faithful)

theorem burnsideF4j_le_normalizer_inf {E : Type} [Group E] {Gp : Subgroup E} (hGp : Gp.Normal)
    (X : Subgroup E) : X ≤ Subgroup.normalizer ((Gp ⊓ X : Subgroup E) : Set E) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx, hxX⟩
    exact ⟨hGp.conj_mem x hx k, X.mul_mem (X.mul_mem hk hxX) (X.inv_mem hk)⟩
  · rintro ⟨hx, hxX⟩
    refine ⟨?_, ?_⟩
    · have := hGp.conj_mem _ hx k⁻¹
      simpa [mul_assoc] using this
    · have := X.mul_mem (X.mul_mem (X.inv_mem hk) hxX) hk
      simpa [mul_assoc] using this

theorem burnsideF4j_Z1_eq {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    ctr (oPPrime 2 (GiOne Gp β ε)) =
      subImg (burnsideF4d_bOne β ε) (ctr (oPPrime 2 (Gp ⊓ M₁))) := by
  have hb := burnsideF4j_bOne_injective hyp
  have hle : oPPrime 2 (Gp ⊓ M₁) ≤ M₁ := (burnsideF4d_oPPrime_le _).trans inf_le_right
  rw [burnsideF4d_GiOne_eq, burnsideF4d_subImg_oPPrime _ hb inf_le_right,
    burnsideF4j_ctr_subImg _ hb hle]

theorem burnsideF4j_Z2_eq {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    ctr (oPPrime 2 (GiTwo Gp β ε)) =
      subImg (burnsideF4d_bTwo β ε) (ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  have hb := burnsideF4j_bTwo_injective hyp
  have hle : oPPrime 2 (Gp ⊓ M₂) ≤ M₂ := (burnsideF4d_oPPrime_le _).trans inf_le_right
  rw [burnsideF4d_GiTwo_eq, burnsideF4d_subImg_oPPrime _ hb inf_le_right,
    burnsideF4j_ctr_subImg _ hb hle]

theorem burnsideF4j_MiOne_le_normalizer {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    MiOne β ε ≤ Subgroup.normalizer (ctr (oPPrime 2 (GiOne Gp β ε)) : Set M) := by
  intro g hg
  have h1 : g ∈ Subgroup.normalizer (GiOne Gp β ε : Set M) := by
    rw [burnsideF4d_MiOne_eq] at hg
    rw [burnsideF4d_GiOne_eq]
    exact subImg_le_normalizer _ (burnsideF4j_le_normalizer_inf hyp.amalgam.normal M₁) hg
  exact burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime h1)

theorem burnsideF4j_MiTwo_le_normalizer {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) :
    MiTwo β ε ≤ Subgroup.normalizer (ctr (oPPrime 2 (GiTwo Gp β ε)) : Set M) := by
  intro g hg
  have h1 : g ∈ Subgroup.normalizer (GiTwo Gp β ε : Set M) := by
    rw [burnsideF4d_MiTwo_eq] at hg
    rw [burnsideF4d_GiTwo_eq]
    exact subImg_le_normalizer _ (burnsideF4j_le_normalizer_inf hyp.amalgam.normal M₂) hg
  exact burnsideF4j_mem_normalizer_ctr (burnsideF4d_Z1_normalizer_oPPrime h1)

end MSide

section F434

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

set_option linter.unusedSectionVars false



@[expose] def burnsideF4j_Z2TransInput : Prop :=
  ∀ (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 .Sp4 2 f Gp M₁ M₂ →
    (∃ w ∈ ctr (oPPrime 2 (Gp ⊓ M₂)), w ≠ 1) ∧
    ∀ w ∈ ctr (oPPrime 2 (Gp ⊓ M₂)), w ≠ 1 → ∀ w' ∈ ctr (oPPrime 2 (Gp ⊓ M₂)), w' ≠ 1 →
      ∃ m ∈ Gp ⊓ (M₁ ⊓ M₂), m * w * m⁻¹ = w'

theorem burnsideF4j_F_4_34_one {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hκ : κ ≠ .L3) :
    IsTISet (ctr (oPPrime 2 (GiOne Gp β ε))) ∧
      MiOne β ε = Subgroup.normalizer ((ctr (oPPrime 2 (GiOne Gp β ε)) : Subgroup M) : Set M) := by
  have hb := burnsideF4j_bOne_injective hyp
  have hZ := burnsideF4j_Z1_eq hyp
  have hle : ctr (oPPrime 2 (Gp ⊓ M₁)) ≤ M₁ :=
    inf_le_left.trans ((burnsideF4d_oPPrime_le _).trans inf_le_right)
  have htr := burnsideF4j_trans_subImg (burnsideF4d_bOne β ε) hle
    ((inf_le_right : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊓ M₂).trans inf_le_left)
    (fun w hw hw1 w' hw' hw1' => burnsideF4j_Z1_conj hyp.amalgam hκ hyp.not_G2d hw hw1 hw' hw1')
  refine burnsideF4j_TI_of_trans (hyp.z_mem.1 hκ) hyp.z_inv.1 hyp.hb
    (burnsideF4j_MiOne_le_normalizer hyp) fun x hx hx1 => ?_
  rw [hZ] at hx
  have hz := hyp.z_mem.1 hκ
  rw [hZ] at hz
  obtain ⟨h, hh, hhz⟩ := htr z hz hyp.z_inv.1 x hx hx1
  refine ⟨h, ?_, hhz⟩
  rw [burnsideF4d_MiOne_eq]
  exact subImg_mono _ ((inf_le_right : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊓ M₂).trans inf_le_left) hh

theorem burnsideF4j_F_4_34_two (hZ2 : burnsideF4j_Z2TransInput) {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z) :
    IsTISet (ctr (oPPrime 2 (GiTwo Gp β ε))) ∧
      MiTwo β ε = Subgroup.normalizer ((ctr (oPPrime 2 (GiTwo Gp β ε)) : Subgroup M) : Set M) := by
  have hb := burnsideF4j_bTwo_injective hyp
  have hZ := burnsideF4j_Z2_eq hyp
  obtain ⟨⟨w₀, hw₀, hw₀1⟩, hconj⟩ := hZ2 f E Gp M₁ M₂ hyp.amalgam
  have hle : ctr (oPPrime 2 (Gp ⊓ M₂)) ≤ M₂ :=
    inf_le_left.trans ((burnsideF4d_oPPrime_le _).trans inf_le_right)
  have htr := burnsideF4j_trans_subImg (burnsideF4d_bTwo β ε) hle
    ((inf_le_right : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊓ M₂).trans inf_le_right) hconj
  have hw₀M : w₀ ∈ M₂ := hle hw₀
  set z₂ : M := burnsideF4d_bTwo β ε ⟨w₀, hw₀M⟩ with hz₂
  have hz₂Z : z₂ ∈ ctr (oPPrime 2 (GiTwo Gp β ε)) := by
    rw [hZ]; exact mem_subImg_of_mem _ hw₀M hw₀
  have hz₂1 : z₂ ≠ 1 := by
    intro h
    apply hw₀1
    have : (⟨w₀, hw₀M⟩ : ↥M₂) = 1 := hb (by rw [← hz₂, h, map_one])
    exact congrArg Subtype.val this
  refine burnsideF4j_TI_of_trans hz₂Z hz₂1 ((hyp.hc rfl).1 z₂ hz₂Z hz₂1)
    (burnsideF4j_MiTwo_le_normalizer hyp) fun x hx hx1 => ?_
  have hz₂Z' := hz₂Z
  rw [hZ] at hx hz₂Z'
  obtain ⟨h, hh, hhz⟩ := htr z₂ hz₂Z' hz₂1 x hx hx1
  refine ⟨h, ?_, hhz⟩
  rw [burnsideF4d_MiTwo_eq]
  exact subImg_mono _ ((inf_le_right : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊓ M₂).trans inf_le_right) hh

theorem burnsideF4j_F_4_34_of (hZ2 : burnsideF4j_Z2TransInput) : F_4_34 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp
  refine ⟨fun hκ => burnsideF4j_F_4_34_one hyp hκ, fun hκ => ?_, fun hκ => ?_⟩
  · subst hκ
    exact burnsideF4j_F_4_34_two hZ2 hyp
  · subst hκ
    exact burnsideF4d_Z6_F_4_34_L3 hyp

end F434

section F433Lie

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431

set_option linter.unusedSectionVars false



theorem burnsideF4j_eq_of_sylow_le {G : Type} [Group G] [Finite G] {S H P : Subgroup G}
    (hS : IsSylowTwoOf S H) (hP : IsPGroup 2 P) (hSP : S ≤ P) (hPH : P ≤ H) : P = S := by
  obtain ⟨x, -, hx⟩ := F7.isSylowTwoOf_exists_conj_le hS hPH hP
  have h1 : Nat.card P ≤ Nat.card S := by
    have := Subgroup.card_le_of_le hx
    rwa [burnsideF4j_card_conjSub] at this
  exact (Subgroup.eq_of_le_of_card_ge hSP h1).symm

theorem burnsideF4j_pCoreOf_borel {G : Type} [Group G] [Finite G] {S H B : Subgroup G}
    (hS : IsSylowTwoOf S H) (hB : B = H ⊓ Subgroup.normalizer (S : Set G)) :
    pCoreOf 2 B = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSB : S ≤ B := hB ▸ le_inf hS.1 Subgroup.le_normalizer
  have hBN : B ≤ Subgroup.normalizer (S : Set G) := hB ▸ inf_le_right
  have hBH : B ≤ H := hB ▸ inf_le_left
  have h1 : S ≤ pCoreOf 2 B :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSB hBN hS.2.1
  exact burnsideF4j_eq_of_sylow_le hS (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 B) h1
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 B).trans hBH)

section Amalgam

variable {κ : GLKind} {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4j_sylow_data (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) :
    IsSylowTwoOf (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) Gp ∧
      Gp ⊓ (M₁ ⊓ M₂) = Gp ⊓ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
  haveI := hyp.finite
  obtain ⟨⟨S, hS, hB⟩, -⟩ := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  have hS' : IsSylowTwoOf S Gp := hS
  have hP := burnsideF4j_pCoreOf_borel hS' hB
  rw [hP]
  exact ⟨hS', hB⟩

theorem burnsideF4j_normalizer_S_le (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) :
    Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) ≤ M₁ ⊓ M₂ := by
  obtain ⟨-, hB⟩ := burnsideF4j_sylow_data hyp
  intro x hx
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split x
  have hhN : h ∈ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
      (burnsideF4j_le_normalizer_inf hyp.normal (M₁ ⊓ M₂) hh)
  have hnN : n ∈ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
    have := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hhN)
    simpa using this
  have hnB : n ∈ Gp ⊓ (M₁ ⊓ M₂) := hB ▸ ⟨hn, hnN⟩
  exact Subgroup.mul_mem _ hnB.2 hh

theorem burnsideF4j_S_le_sylow (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ T := by
  haveI := hyp.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) ≤ pCoreOf 2 (M₁ ⊓ M₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right)
      ((burnsideF4j_le_normalizer_inf hyp.normal (M₁ ⊓ M₂)).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  exact h1.trans (F7.isSylowTwoOf_pCoreOf_le hT)

theorem burnsideF4j_sylow_inf_Gp (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) : T ⊓ Gp = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
  haveI := hyp.finite
  obtain ⟨hS, -⟩ := burnsideF4j_sylow_data hyp
  have hSle := burnsideF4j_S_le_sylow hyp hT
  exact burnsideF4j_eq_of_sylow_le hS (hT.2.1.to_le inf_le_left)
    (le_inf hSle ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)) inf_le_right

theorem burnsideF4j_sylow_M1 (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) {T : Subgroup E}
    (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) : IsSylowTwoOf T M₁ := by
  haveI := hyp.finite
  obtain ⟨hS, -⟩ := burnsideF4j_sylow_data hyp
  refine CFSG.Quasithin.H13.F431.L3.isSylowTwoOf_of_max (hT.1.trans inf_le_left) hT.2.1
    fun P hP hTP hPM => ?_
  have hPG : P ⊓ Gp = pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) :=
    burnsideF4j_eq_of_sylow_le hS (hP.to_le inf_le_left)
      (le_inf ((burnsideF4j_S_le_sylow hyp hT).trans hTP)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left)) inf_le_right
  have hPN : P ≤ Subgroup.normalizer ((pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) : Subgroup E) : Set E) := by
    intro x hx
    rw [← hPG, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyP, hyG⟩
      exact ⟨P.mul_mem (P.mul_mem hx hyP) (P.inv_mem hx), hyp.normal.conj_mem y hyG x⟩
    · rintro ⟨hyP, hyG⟩
      refine ⟨?_, ?_⟩
      · have := P.mul_mem (P.mul_mem (P.inv_mem hx) hyP) hx
        simpa [mul_assoc] using this
      · have := hyp.normal.conj_mem _ hyG x⁻¹
        simpa [mul_assoc] using this
  exact burnsideF4j_eq_of_sylow_le hT hP hTP (hPN.trans (burnsideF4j_normalizer_S_le hyp))

theorem burnsideF4j_ZT_inv_mem_Z1
    (hyp : HypF_4_4 κ 2 f Gp M₁ M₂) (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4) (hG2d : κ ≠ .G2d)
    (hout : ∀ x ∈ M₁ ⊓ M₂, x ∉ Gp → x * x = 1 →
      ∃ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), x * s ≠ s * x)
    {z : E} (hz : z ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) (hz1 : z ≠ 1) {T : Subgroup E}
    (hT : IsSylowTwoOf T (M₁ ⊓ M₂)) {x : E} (hx : x ∈ ctr T) (hx1 : x ≠ 1) (hx2 : x * x = 1) :
    x ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  have hSle := burnsideF4j_S_le_sylow hyp hT
  by_cases hxG : x ∈ Gp
  · have hxS : x ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)) := by
      rw [← burnsideF4j_sylow_inf_Gp hyp hT]
      exact ⟨hx.1, hxG⟩
    refine burnsideF4j_ZS_inv_mem_Z1 hyp hL3 hSp hG2d hz hz1
      (show x ∈ ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) from
        ⟨hxS, Subgroup.mem_centralizer_iff.2 fun s hs =>
          (Subgroup.mem_centralizer_iff.1 hx.2) s (hSle hs)⟩) hx1 hx2
  · exfalso
    obtain ⟨s, hs, hne⟩ := hout x (hT.1 hx.1) hxG hx2
    exact hne ((Subgroup.mem_centralizer_iff.1 hx.2) s (hSle hs)).symm

end Amalgam

end F433Lie

section F433

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

theorem burnsideF4j_relIndex_subImg {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {X Y : Subgroup Mb} (hY : Y ≤ N) :
    (subImg b X).relIndex (subImg b Y) = X.relIndex Y := by
  unfold subImg
  rw [Subgroup.relIndex_map_map_of_injective _ _ hb, Subgroup.relIndex_subgroupOf hY]

@[expose] noncomputable def burnsideF4j_subImgEquiv {Mb G : Type} [Group Mb] [Group G]
    {N : Subgroup Mb} (b : ↥N →* G) (hb : Function.Injective b) {X : Subgroup Mb} (hX : X ≤ N) :
    ↥X ≃* ↥(subImg b X) :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans (Subgroup.equivMapOfInjective _ b hb)

theorem burnsideF4j_isSylow_subImg_iff {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {X Y : Subgroup Mb} (hX : X ≤ N) (hY : Y ≤ N) :
    IsSylowTwoOf (subImg b X) (subImg b Y) ↔ IsSylowTwoOf X Y := by
  have hidx := burnsideF4j_relIndex_subImg b hb (X := X) hY
  have hp : IsPGroup 2 (subImg b X) ↔ IsPGroup 2 X :=
    ⟨fun h => h.of_equiv (burnsideF4j_subImgEquiv b hb hX).symm,
      fun h => h.of_equiv (burnsideF4j_subImgEquiv b hb hX)⟩
  have hle : subImg b X ≤ subImg b Y ↔ X ≤ Y := by
    constructor
    · intro h x hx
      have h1 := h (mem_subImg_of_mem b (hX hx) hx)
      exact (mem_subImg_iff_of_injective hb (hX hx)).1 h1
    · exact subImg_mono b
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hle.1 h1, hp.1 h2, fun h => h3 (by
      show 2 ∣ (subImg b X).relIndex (subImg b Y)
      rw [hidx]; exact h)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨hle.2 h1, hp.2 h2, fun h => h3 (by
      have : 2 ∣ (subImg b X).relIndex (subImg b Y) := h
      rwa [hidx] at this)⟩

theorem burnsideF4j_exists_preimage {Mb G : Type} [Group Mb] [Group G] {N : Subgroup Mb}
    (b : ↥N →* G) (hb : Function.Injective b) {Y : Subgroup Mb} {T : Subgroup G}
    (hT : T ≤ subImg b Y) : ∃ X : Subgroup Mb, X ≤ Y ∧ X ≤ N ∧ subImg b X = T := by
  refine ⟨(T.comap b).map N.subtype, ?_, Subgroup.map_subtype_le _, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨y, hyN, hyY, hy⟩ := mem_subImg.mp (hT hn)
    have : (⟨y, hyN⟩ : ↥N) = n := hb hy
    rw [← this]
    exact hyY
  · ext g
    rw [mem_subImg]
    constructor
    · rintro ⟨x, hxN, ⟨n, hn, hnx⟩, rfl⟩
      have : n = ⟨x, hxN⟩ := Subtype.ext hnx
      rw [← this]
      exact hn
    · intro hg
      obtain ⟨y, hyN, -, hy⟩ := mem_subImg.mp (hT hg)
      exact ⟨y, hyN, ⟨⟨y, hyN⟩, show b ⟨y, hyN⟩ ∈ T by rw [hy]; exact hg, rfl⟩, hy⟩

@[expose] def burnsideF4j_omegaCtr {G : Type} [Group G] (T : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ ctr T ∧ x * x = 1}
  one_mem' := ⟨(ctr T).one_mem, mul_one 1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
    refine ⟨(ctr T).mul_mem ha hb, ?_⟩
    have hab : b * a = a * b := (Subgroup.mem_centralizer_iff.1 ha.2) b hb.1
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨ha, ha2⟩
    refine ⟨(ctr T).inv_mem ha, ?_⟩
    rw [← mul_inv_rev, ha2, inv_one]

theorem burnsideF4j_mem_omegaCtr {G : Type} [Group G] {T : Subgroup G} {x : G} :
    x ∈ burnsideF4j_omegaCtr T ↔ x ∈ ctr T ∧ x * x = 1 :=
  Iff.rfl

theorem burnsideF4j_exists_omegaCtr {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) (hne : T ≠ ⊥) : ∃ w ∈ burnsideF4j_omegaCtr T, w ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).mpr hne
  have hZ : Nontrivial (Subgroup.center ↥T) := hT.center_nontrivial
  have hdvd : 2 ∣ Nat.card (Subgroup.center ↥T) := by
    obtain ⟨n, hn⟩ := (hT.to_subgroup (Subgroup.center ↥T)).exists_card_eq
    rcases n with _ | n
    · exfalso
      rw [pow_zero] at hn
      have := (Finite.one_lt_card_iff_nontrivial (α := ↥(Subgroup.center ↥T))).mpr hZ
      omega
    · rw [hn]; exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥T) 2 hdvd
  refine ⟨((w : ↥T) : G), ⟨⟨(w : ↥T).2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, ?_⟩, ?_⟩
  · have := Subgroup.mem_center_iff.1 w.2 ⟨y, hy⟩
    exact congrArg Subtype.val this
  · have h2 : w ^ 2 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
    have : (w * w : Subgroup.center ↥T) = 1 := by rw [← pow_two]; exact h2
    exact congrArg (fun u : Subgroup.center ↥T => ((u : ↥T) : G)) this
  · intro h
    have : w = 1 := Subtype.ext (Subtype.ext h)
    rw [this, orderOf_one] at hw
    exact absurd hw (by norm_num)

end F433

section F433Main

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

set_option linter.unusedSectionVars false



@[expose] def burnsideF4j_OuterInvInput : Prop :=
  ∀ (κ : GLKind) (f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E), HypF_4_4 κ 2 f Gp M₁ M₂ →
    κ ≠ .L3 → κ ≠ .Sp4 → κ ≠ .G2d →
    ∀ x ∈ M₁ ⊓ M₂, x ∉ Gp → x * x = 1 → ∃ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), x * s ≠ s * x

theorem burnsideF4j_Z1_trans_M {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hκ : κ ≠ .L3) :
    ∀ x ∈ ctr (oPPrime 2 (GiOne Gp β ε)), x ≠ 1 → ∃ h ∈ MiOne β ε, h * z * h⁻¹ = x := by
  have hZ := burnsideF4j_Z1_eq hyp
  have hle : ctr (oPPrime 2 (Gp ⊓ M₁)) ≤ M₁ :=
    inf_le_left.trans ((burnsideF4d_oPPrime_le _).trans inf_le_right)
  have htr := burnsideF4j_trans_subImg (burnsideF4d_bOne β ε) hle
    ((inf_le_right : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊓ M₂).trans inf_le_left)
    (fun w hw hw1 w' hw' hw1' => burnsideF4j_Z1_conj hyp.amalgam hκ hyp.not_G2d hw hw1 hw' hw1')
  intro x hx hx1
  rw [hZ] at hx
  have hz := hyp.z_mem.1 hκ
  rw [hZ] at hz
  obtain ⟨h, hh, hhz⟩ := htr z hz hyp.z_inv.1 x hx hx1
  refine ⟨h, ?_, hhz⟩
  rw [burnsideF4d_MiOne_eq]
  exact subImg_mono _ ((inf_le_right : Gp ⊓ (M₁ ⊓ M₂) ≤ M₁ ⊓ M₂).trans inf_le_left) hh

theorem burnsideF4j_centralizer_Z1_le {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hκ : κ ≠ .L3) {w : M}
    (hw : w ∈ ctr (oPPrime 2 (GiOne Gp β ε))) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set M) ≤ MiOne β ε := by
  obtain ⟨h, hh, rfl⟩ := burnsideF4j_Z1_trans_M hyp hκ w hw hw1
  rw [burnsideF4j_centralizer_conj]
  intro y hy
  rw [mem_conjSub] at hy
  have := (MiOne β ε).mul_mem (MiOne β ε |>.mul_mem hh (hyp.hb hy)) ((MiOne β ε).inv_mem hh)
  simpa [mul_assoc] using this

theorem burnsideF4j_F_4_33_main {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hL3 : κ ≠ .L3) (hSp : κ ≠ .Sp4)
    (hout : ∀ x ∈ M₁ ⊓ M₂, x ∉ Gp → x * x = 1 →
      ∃ s ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)), x * s ≠ s * x)
    {T : Subgroup M} (hT : ChF.IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) : ChF.IsSylowOf 2 T ⊤ := by
  haveI := hyp.finite_M
  haveI := hyp.amalgam.finite
  set b := burnsideF4d_bOne β ε with hbdef
  have hb : Function.Injective b := burnsideF4j_bOne_injective hyp
  have hinter : MiOne β ε ⊓ MiTwo β ε = subImg b (M₁ ⊓ M₂) :=
    burnsideF4d_inter_eq β hyp.faithful ε hyp.inj
  have hT' : IsSylowTwoOf T (subImg b (M₁ ⊓ M₂)) := hinter ▸ hT
  obtain ⟨Tb, hTbY, hTbN, hTbeq⟩ := burnsideF4j_exists_preimage b hb hT'.1
  have hTbsyl : IsSylowTwoOf Tb (M₁ ⊓ M₂) :=
    (burnsideF4j_isSylow_subImg_iff b hb hTbN inf_le_left).1 (hTbeq ▸ hT')
  have hTb1 : IsSylowTwoOf Tb M₁ := burnsideF4j_sylow_M1 hyp.amalgam hTbsyl
  have hT1 : IsSylowTwoOf T (MiOne β ε) := by
    rw [← hTbeq, burnsideF4d_MiOne_eq]
    exact (burnsideF4j_isSylow_subImg_iff b hb hTbN le_rfl).2 hTb1
  have hZ := burnsideF4j_Z1_eq hyp
  have hz := hyp.z_mem.1 hL3
  have hz' := hz
  rw [hZ] at hz'
  obtain ⟨zb, hzbN, hzb, hzbe⟩ := mem_subImg.mp hz'
  have hzb1 : zb ≠ 1 := by
    rintro rfl
    exact hyp.z_inv.1 (by rw [← hzbe]; exact map_one b)
  have hTne : T ≠ ⊥ := by
    intro hbot
    have hzM : z ∈ MiOne β ε := hyp.hb (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    have h2 : orderOf (⟨z, hzM⟩ : ↥(MiOne β ε)) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_two]; exact hyp.z_inv.2) hyp.z_inv.1
    have hdvd : 2 ∣ Nat.card ↥(MiOne β ε) := h2 ▸ orderOf_dvd_natCard _
    apply hT1.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
    exact hdvd
  have hZT : ∀ w ∈ burnsideF4j_omegaCtr T, w ≠ 1 →
      Subgroup.centralizer ({w} : Set M) ≤ MiOne β ε := by
    intro w hw hw1
    obtain ⟨hwT, hw2⟩ := burnsideF4j_mem_omegaCtr.1 hw
    rw [← hTbeq, burnsideF4j_ctr_subImg b hb hTbN] at hwT
    obtain ⟨wb, hwbN, hwb, rfl⟩ := mem_subImg.mp hwT
    have hwb1 : wb ≠ 1 := by
      rintro rfl
      exact hw1 (map_one b)
    have hwb2 : wb * wb = 1 := by
      have : (⟨wb, hwbN⟩ : ↥M₁) * ⟨wb, hwbN⟩ = 1 := hb (by rw [map_mul, hw2, map_one])
      exact congrArg Subtype.val this
    have hwZ : wb ∈ ctr (oPPrime 2 (Gp ⊓ M₁)) :=
      burnsideF4j_ZT_inv_mem_Z1 hyp.amalgam hL3 hSp hyp.not_G2d hout hzb hzb1 hTbsyl hwb hwb1
        hwb2
    have hwZ1 : b ⟨wb, hwbN⟩ ∈ ctr (oPPrime 2 (GiOne Gp β ε)) := by
      rw [hZ]; exact mem_subImg_of_mem b hwbN hwZ
    exact burnsideF4j_centralizer_Z1_le hyp hL3 hwZ1 hw1
  have hmax := CFSG.Quasithin.H13.F431.L3.maximal_two_of_char (H := ⊤) hT1
    (fun x hx => (burnsideF4j_mem_omegaCtr.1 hx).1.1)
    (burnsideF4j_exists_omegaCtr hT.2.1 hTne)
    (fun n _ hn x hx => by
      obtain ⟨hxT, hx2⟩ := burnsideF4j_mem_omegaCtr.1 hx
      refine burnsideF4j_mem_omegaCtr.2 ⟨burnsideF4j_conj_mem_ctr hn hxT, ?_⟩
      calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
        _ = 1 := by rw [hx2]; group)
    (fun w hw hw1 y _ hy => hZT w hw hw1 (Subgroup.mem_centralizer_singleton_iff.2 hy))
  exact CFSG.Quasithin.H13.F431.L3.isSylowTwoOf_of_max le_top hT.2.1 hmax

theorem burnsideF4j_F_4_33_Sp4 {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 .Sp4 f Gp M₁ M₂ β ε z)
    {T : Subgroup M} (hT : ChF.IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) : ChF.IsSylowOf 2 T ⊤ := by
  refine ⟨le_top, hT.2.1, ?_⟩
  rw [Subgroup.relIndex_top_right, ← Subgroup.relIndex_mul_index hT.1]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h1 | h1
  · exact hT.2.2 h1
  · exact (Nat.not_even_iff_odd.mpr (hyp.hd rfl)) (even_iff_two_dvd.mpr h1)

theorem burnsideF4j_F_4_33_of (hout : burnsideF4j_OuterInvInput) : F_4_33 := by
  intro κ f E _ Gp M₁ M₂ Y _ β M _ ε z hyp T hT
  by_cases hL3 : κ = .L3
  · subst hL3
    exact burnsideF4d_Z6_F_4_33_L3 hyp hT
  by_cases hSp : κ = .Sp4
  · subst hSp
    exact burnsideF4j_F_4_33_Sp4 hyp hT
  exact burnsideF4j_F_4_33_main hyp hL3 hSp
    (hout κ f E Gp M₁ M₂ hyp.amalgam hL3 hSp hyp.not_G2d) hT

theorem burnsideF4j_F_4_33_odd {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (hodd : Odd Gp.index)
    {T : Subgroup M} (hT : ChF.IsSylowOf 2 T (MiOne β ε ⊓ MiTwo β ε)) : ChF.IsSylowOf 2 T ⊤ := by
  haveI := hyp.amalgam.finite
  haveI := hyp.amalgam.normal
  by_cases hL3 : κ = .L3
  · subst hL3
    exact burnsideF4d_Z6_F_4_33_L3 hyp hT
  by_cases hSp : κ = .Sp4
  · subst hSp
    exact burnsideF4j_F_4_33_Sp4 hyp hT
  refine burnsideF4j_F_4_33_main hyp hL3 hSp (fun x _ hxG hx2 => ?_) hT
  exact absurd (burnsideF4d_two_elt_mem hodd (k := 1) (by rw [pow_one, pow_two]; exact hx2)) hxG

end F433Main

section F435

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431
  CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion

set_option linter.unusedSectionVars false



theorem burnsideF4j_exists_sylow {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ∃ T : Subgroup G, ChF.IsSylowOf 2 T H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥H) := inferInstance
  refine ⟨(P : Subgroup ↥H).map H.subtype, Subgroup.map_subtype_le _,
    P.isPGroup'.map _, ?_⟩
  have h : ((P : Subgroup ↥H).map H.subtype).subgroupOf H = (P : Subgroup ↥H) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  show ¬ 2 ∣ (((P : Subgroup ↥H).map H.subtype).subgroupOf H).index
  rw [h]
  exact P.not_dvd_index

theorem burnsideF4j_F_4_35_forward {κ : GLKind} {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 κ f Gp M₁ M₂ β ε z) (i j : ↥(M₁ ⊓ M₂))
    (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hg : ∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) : IsConj (bM β ε i) (bM β ε j) := by
  haveI := hyp.amalgam.finite
  obtain ⟨T, hT⟩ := burnsideF4j_exists_sylow (M₁ ⊓ M₂)
  have hST := burnsideF4j_S_le_sylow hyp.amalgam (show IsSylowTwoOf T (M₁ ⊓ M₂) from hT)
  obtain ⟨g, -, hgij⟩ := hg
  obtain ⟨h, hh⟩ := as_F_4_30 κ f E Gp M₁ M₂ hyp.amalgam T hT Y β hyp.faithful {i} {j}
    (by rintro u rfl; exact hST hi) (by rintro u rfl; exact hST hj) ⟨g, by
      rw [Set.image_singleton, Set.image_singleton, Set.image_singleton, hgij]⟩
  rw [Set.image_singleton, Set.image_singleton, Set.image_singleton] at hh
  have hh' : h * bmap β i * h⁻¹ = bmap β j := Set.singleton_eq_singleton_iff.1 hh
  refine isConj_iff.2 ⟨epsG β ε h, ?_⟩
  show epsG β ε h * epsG β ε (bmap β i) * (epsG β ε h)⁻¹ = epsG β ε (bmap β j)
  rw [← hh', map_mul, map_mul, map_inv]

theorem burnsideF4j_F_4_35_L3 {f : ℕ} {E : Type} [Group E]
    {Gp M₁ M₂ : Subgroup E} {Y : Type} [Group Y] {β : Cpl M₁ M₂ Y} {M : Type} [Group M]
    {ε : Y →* M} {z : M} (hyp : HypF_4_31 .L3 f Gp M₁ M₂ β ε z) (i j : ↥(M₁ ⊓ M₂))
    (hi : (i : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) (hj : (j : E) ∈ pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂)))
    (hi1 : i ≠ 1) (hj1 : j ≠ 1) (hi2 : i * i = 1) (hj2 : j * j = 1) :
    ((∃ g ∈ Gp, g * (i : E) * g⁻¹ = (j : E)) ↔ IsConj (bM β ε i) (bM β ε j)) := by
  haveI := hyp.amalgam.finite
  refine ⟨burnsideF4j_F_4_35_forward hyp i j hi hj, fun _ => ?_⟩
  have hyp' := burnsideF4j_restrict ChF.nativeChartCompatibility hyp.amalgam
  have h27 := as_F_4_27 .L3 f ↥Gp ⊤ _ _ hyp' rfl
  dsimp only at h27
  obtain ⟨-, h1, -⟩ := h27
  obtain ⟨hcard, -⟩ := h1 (Or.inl rfl)
  have hiG : (i : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hi).1
  have hjG : (j : E) ∈ Gp := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hj).1
  set i' : ↥Gp := ⟨i, hiG⟩
  set j' : ↥Gp := ⟨j, hjG⟩
  have hi'1 : i' ≠ 1 := fun h => hi1 (Subtype.ext (congrArg (fun x : ↥Gp => (x : E)) h))
  have hj'1 : j' ≠ 1 := fun h => hj1 (Subtype.ext (congrArg (fun x : ↥Gp => (x : E)) h))
  have hi'2 : i' * i' = 1 := Subtype.ext (show (i : E) * i = 1 from congrArg Subtype.val hi2)
  have hj'2 : j' * j' = 1 := Subtype.ext (show (j : E) * j = 1 from congrArg Subtype.val hj2)
  have hmi : ConjClasses.mk i' ∈ InvClasses ↥Gp := ⟨i', ConjClasses.mem_carrier_mk, hi'1, hi'2⟩
  have hmj : ConjClasses.mk j' ∈ InvClasses ↥Gp := ⟨j', ConjClasses.mem_carrier_mk, hj'1, hj'2⟩
  have hfin : (InvClasses ↥Gp).Finite := Set.toFinite _
  obtain ⟨C, hC⟩ := Set.ncard_eq_one.1 hcard
  have h1 : ConjClasses.mk i' = C := by
    have := hmi; rw [hC] at this; exact this
  have h2 : ConjClasses.mk j' = C := by
    have := hmj; rw [hC] at this; exact this
  obtain ⟨c, hc⟩ := isConj_iff.1 (ConjClasses.mk_eq_mk_iff_isConj.1 (h1.trans h2.symm))
  exact ⟨c, c.2, congrArg Subtype.val hc⟩

end F435

section Final

open CFSG.ASVolI.ChF

set_option linter.unusedSectionVars false



theorem as_F_4_34 : F_4_34 :=
  burnsideF4j_F_4_34_of fun _ _ _ _ _ _ hyp => burnsideF4jb_Z2_conj hyp

end Final

end PartBurnsideF4j


end CFSG.ASVolI
