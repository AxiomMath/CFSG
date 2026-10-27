module

public import CFSG.RankThree.PartOne.KLAY10.Std
public import CFSG.RankThree.PartOne.KLAY10.Block

public section

namespace CFSG.RankThree.PartOne.KLAY10

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

section Form

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def Bf : LinearMap.BilinForm K (QV K (Fin 3)) :=
  ∑ i : Fin 3, (qForm (K := K)).compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem Bf_apply (x y : QV K (Fin 3)) : Bf x y = ∑ i, qForm (x i) (y i) := by
  simp [Bf, LinearMap.sum_apply]

theorem Bf_self (x : QV K (Fin 3)) : Bf x x = 0 := by
  rw [Bf_apply]
  exact Finset.sum_eq_zero fun i _ => qForm_isAlt (x i)

theorem Bf_comm (x y : QV K (Fin 3)) : Bf x y = Bf y x := by
  have h := Bf_self (x + y)
  simp only [map_add, LinearMap.add_apply, Bf_self] at h
  have h2 : Bf x y + Bf y x = 0 := by
    rw [add_comm]
    simpa using h
  exact CharTwo.add_eq_zero.1 h2

omit [Finite K] in
theorem two_eq_zero_K : (2 : K) = 0 := CharP.cast_eq_zero K 2

theorem mem_M10_iff_Bf (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) :
    g ∈ M10 K ↔ ∀ x y, Bf (g x) (g y) = Bf x y := by
  rw [mem_M10_iff]
  simp only [Bf_apply]

end Form

section Maps

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def tvLin (e : QV K (Fin 3)) : QV K (Fin 3) →ₗ[K] QV K (Fin 3) :=
  LinearMap.id + (Bf.flip e).smulRight e

theorem tvLin_apply (e x : QV K (Fin 3)) : tvLin e x = x + Bf x e • e := rfl

theorem tvLin_invol (e x : QV K (Fin 3)) : tvLin e (tvLin e x) = x := by
  simp only [tvLin_apply, map_add, map_smul, Bf_self, zero_smul, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

@[expose] noncomputable def tvAut (e : QV K (Fin 3)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  LinearEquiv.ofInvolutive (tvLin e) (tvLin_invol e)

theorem tvAut_apply (e x : QV K (Fin 3)) : tvAut e x = x + Bf x e • e := rfl

theorem tvAut_mul_self (e : QV K (Fin 3)) : tvAut e * tvAut e = 1 := by
  refine LinearEquiv.ext fun x => ?_
  exact tvLin_invol e x

theorem Bf_tvAut (e x y : QV K (Fin 3)) : Bf (tvAut e x) (tvAut e y) = Bf x y := by
  simp only [tvAut_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, Bf_self, Bf_comm e y]
  linear_combination (Bf y e * Bf x e) * two_eq_zero_K (K := K)

theorem tvAut_mem_M10 (e : QV K (Fin 3)) : tvAut e ∈ M10 K :=
  (mem_M10_iff_Bf _).2 (Bf_tvAut e)

theorem tvAut_comm {e e' : QV K (Fin 3)} (h : Bf e e' = 0) :
    tvAut e * tvAut e' = tvAut e' * tvAut e := by
  refine LinearEquiv.ext fun x => ?_
  have h' : Bf e' e = 0 := by rw [Bf_comm]; exact h
  simp only [LinearEquiv.mul_apply, tvAut_apply, map_add, map_smul, h, h', zero_smul, add_zero]
  abel

theorem conj_tvAut {g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)} (hg : g ∈ M10 K) (e : QV K (Fin 3)) :
    g * tvAut e * g⁻¹ = tvAut (g e) := by
  refine LinearEquiv.ext fun x => ?_
  have hB := (mem_M10_iff_Bf g).1 hg
  have h1 : Bf (g.symm x) e = Bf x (g e) := by
    rw [← hB (g.symm x) e, LinearEquiv.apply_symm_apply]
  show g (g.symm x + Bf (g.symm x) e • e) = x + Bf x (g e) • g e
  rw [map_add, map_smul, LinearEquiv.apply_symm_apply, h1]

end Maps

section EAut

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def eLin (a b : QV K (Fin 3)) : QV K (Fin 3) →ₗ[K] QV K (Fin 3) :=
  LinearMap.id + (Bf.flip a).smulRight b + (Bf.flip b).smulRight a

theorem eLin_apply (a b x : QV K (Fin 3)) : eLin a b x = x + Bf x a • b + Bf x b • a := rfl

theorem smul_add_self (c : K) (v : QV K (Fin 3)) : c • v + c • v = 0 := by
  rw [← add_smul, CharTwo.add_self_eq_zero, zero_smul]

theorem eLin_invol {a b : QV K (Fin 3)} (hab : Bf a b = 0) (x : QV K (Fin 3)) :
    eLin a b (eLin a b x) = x := by
  have hba : Bf b a = 0 := by rw [Bf_comm]; exact hab
  simp only [eLin_apply, map_add, map_smul, Bf_self, hab, hba, zero_smul, add_zero]
  calc x + Bf x a • b + Bf x b • a + Bf x a • b + Bf x b • a =
      x + (Bf x a • b + Bf x a • b) + (Bf x b • a + Bf x b • a) := by abel
    _ = x := by rw [smul_add_self, smul_add_self]; simp

@[expose] noncomputable def eAut {a b : QV K (Fin 3)} (hab : Bf a b = 0) :
    QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) :=
  LinearEquiv.ofInvolutive (eLin a b) (eLin_invol hab)

theorem eAut_apply {a b : QV K (Fin 3)} (hab : Bf a b = 0) (x : QV K (Fin 3)) :
    eAut hab x = x + Bf x a • b + Bf x b • a := rfl

theorem eAut_mul_self {a b : QV K (Fin 3)} (hab : Bf a b = 0) : eAut hab * eAut hab = 1 := by
  refine LinearEquiv.ext fun x => ?_
  exact eLin_invol hab x

theorem Bf_eAut {a b : QV K (Fin 3)} (hab : Bf a b = 0) (x y : QV K (Fin 3)) :
    Bf (eAut hab x) (eAut hab y) = Bf x y := by
  have hba : Bf b a = 0 := by rw [Bf_comm]; exact hab
  simp only [eAut_apply, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    Bf_self, hab, hba, Bf_comm b y, Bf_comm a y]
  linear_combination (Bf y a * Bf x b + Bf x a * Bf y b) * two_eq_zero_K (K := K)

theorem eAut_mem_M10 {a b : QV K (Fin 3)} (hab : Bf a b = 0) : eAut hab ∈ M10 K :=
  (mem_M10_iff_Bf _).2 (Bf_eAut hab)

end EAut

section EConj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem conj_eAut {g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)} (hg : g ∈ M10 K) {a b : QV K (Fin 3)}
    (hab : Bf a b = 0) (hgab : Bf (g a) (g b) = 0) : g * eAut hab * g⁻¹ = eAut hgab := by
  refine LinearEquiv.ext fun x => ?_
  have hB := (mem_M10_iff_Bf g).1 hg
  have h1 : Bf (g.symm x) a = Bf x (g a) := by
    rw [← hB (g.symm x) a, LinearEquiv.apply_symm_apply]
  have h2 : Bf (g.symm x) b = Bf x (g b) := by
    rw [← hB (g.symm x) b, LinearEquiv.apply_symm_apply]
  show g (g.symm x + Bf (g.symm x) a • b + Bf (g.symm x) b • a) =
    x + Bf x (g a) • g b + Bf x (g b) • g a
  rw [map_add, map_add, map_smul, map_smul, LinearEquiv.apply_symm_apply, h1, h2]

end EConj

section Closure

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem isPGroup_two_closure {G : Set ↥(M10 K)} (hinv : ∀ g ∈ G, g * g = 1)
    (hcomm : ∀ g ∈ G, ∀ g' ∈ G, g * g' = g' * g) : IsPGroup 2 ↥(Subgroup.closure G) := by
  have hA : ∀ u ∈ Subgroup.closure G, ∀ g ∈ G, u * g = g * u := by
    intro u hu g hg
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact hcomm x hx g hg
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx => exact (Commute.inv_left (show Commute x g from hx)).eq
  have hB : ∀ u ∈ Subgroup.closure G, ∀ v ∈ Subgroup.closure G, u * v = v * u := by
    intro u hu v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx => exact hA u hu x hx
    | one => simp
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx => exact (Commute.inv_right (show Commute u x from hx)).eq
  have hC : ∀ u ∈ Subgroup.closure G, u * u = 1 := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact hinv x hx
    | one => simp
    | mul x y hxm hym hx hy =>
      calc x * y * (x * y) = x * (y * x) * y := by simp only [mul_assoc]
        _ = x * (x * y) * y := by rw [hB y hym x hxm]
        _ = (x * x) * (y * y) := by simp only [mul_assoc]
        _ = 1 := by rw [hx, hy, one_mul]
    | inv x _ hx => rw [← mul_inv_rev, hx, inv_one]
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := hC g.1 g.2
  simpa [pow_one, sq] using this

theorem le_normalizer_closure {G : Set ↥(M10 K)} {T : Subgroup ↥(M10 K)}
    (hT : ∀ t ∈ T, ∀ g ∈ G, t * g * t⁻¹ ∈ G) :
    T ≤ Subgroup.normalizer (Subgroup.closure G : Set ↥(M10 K)) := by
  have hfwd : ∀ t ∈ T, ∀ u ∈ Subgroup.closure G, t * u * t⁻¹ ∈ Subgroup.closure G := by
    intro t ht u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hT t ht x hx)
    | one => simp
    | mul x y _ _ hx hy =>
      have : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ hx hy
    | inv x _ hx =>
      have : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      rw [this]
      exact Subgroup.inv_mem _ hx
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact hfwd t ht u hu
  · intro hu
    have := hfwd t⁻¹ (T.inv_mem ht) _ hu
    simpa [mul_assoc] using this

end Closure

section FixB

variable {K : Type} [Field K] [Finite K] [CharP K 2] {z : (Qext K)ˣ}
  {g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)}

theorem bAut_of_coord_two_zero (v : QV K (Fin 3)) (hv : v 2 = 0) : bAut z v = v := by
  funext k
  fin_cases k
  · exact bAut_apply_zero z v
  · exact bAut_apply_one z v
  · show bAut z v 2 = v 2
    rw [bAut_apply_two, hv, mul_zero]

theorem bAut_e2v (c : Qext K) : bAut z (e2v c) = e2v ((z : Qext K) * c) := by
  funext k
  fin_cases k
  · show bAut z (e2v c) 0 = e2v ((z : Qext K) * c) 0
    rw [bAut_apply_zero, e2v_zero_coord, e2v_zero_coord]
  · show bAut z (e2v c) 1 = e2v ((z : Qext K) * c) 1
    rw [bAut_apply_one, e2v_one_coord, e2v_one_coord]
  · show bAut z (e2v c) 2 = e2v ((z : Qext K) * c) 2
    rw [bAut_apply_two, e2v_two_coord, e2v_two_coord]

theorem Bf_e2v (x : QV K (Fin 3)) (c : Qext K) : Bf x (e2v c) = qForm (x 2) c := by
  rw [Bf_apply]
  exact sum_qForm_single x 2 c

theorem coord_two_of_fix (hgM : g ∈ M10 K) (hfix : ∀ c : Qext K, g (e2v c) = e2v c)
    (v : QV K (Fin 3)) (hv : v 2 = 0) : g v 2 = 0 := by
  apply qForm_nondegenerate.1
  intro c
  have h1 : qForm (g v 2) c = Bf (g v) (e2v c) := (Bf_e2v _ c).symm
  rw [h1]
  calc Bf (g v) (e2v c) = Bf (g v) (g (e2v c)) := by rw [hfix c]
    _ = Bf v (e2v c) := (mem_M10_iff_Bf g).1 hgM _ _
    _ = 0 := by rw [Bf_e2v, hv]; simp

theorem comm_of_fix (hgM : g ∈ M10 K) (hfix : ∀ c : Qext K, g (e2v c) = e2v c) :
    g * bAut z = bAut z * g := by
  refine LinearEquiv.ext fun v => ?_
  show g (bAut z v) = bAut z (g v)
  have hv := vec_eq_front_add v
  have hix2 : (split3.symm (front v, 0) : QV K (Fin 3)) 2 = 0 := rfl
  have h1 : bAut z v = split3.symm (front v, 0) + e2v ((z : Qext K) * v 2) := by
    conv_lhs => rw [hv]
    rw [map_add, bAut_of_coord_two_zero _ hix2, bAut_e2v]
  have h2 : g v = g (split3.symm (front v, 0)) + e2v (v 2) := by
    conv_lhs => rw [hv]
    rw [map_add, hfix]
  rw [h1, map_add, hfix, h2, map_add,
    bAut_of_coord_two_zero _ (coord_two_of_fix hgM hfix _ hix2), bAut_e2v]

theorem exists_blk2_of_fix (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) (hgM : g ∈ M10 K)
    (hfix : ∀ c : Qext K, g (e2v c) = e2v c) : ∃ h ∈ M2 K, blk2Aut h = g :=
  exists_blk2_of_wOf_one hz1 hzK hgM (comm_of_fix hgM hfix) (by
    simp only [wOf, hfix, e2v_two_coord])

theorem front_e2v (c : Qext K) : front (e2v c) = (0 : QV K (Fin 2)) := by
  funext i
  fin_cases i <;> simp [front, e2v]

theorem blk2Aut_e2v (h : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) (c : Qext K) :
    blk2Aut h (e2v c) = e2v c := by
  funext k
  fin_cases k
  · show blk2Aut h (e2v c) 0 = e2v c 0
    rw [blk2Aut_apply_zero, e2v_zero_coord, front_e2v, map_zero]
    rfl
  · show blk2Aut h (e2v c) 1 = e2v c 1
    rw [blk2Aut_apply_one, e2v_one_coord, front_e2v, map_zero]
    rfl
  · show blk2Aut h (e2v c) 2 = e2v c 2
    rw [blk2Aut_apply_two]

end FixB

section TypeI

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def evec (i : Fin 3) (u : Qext K) : QV K (Fin 3) := Pi.single i u

theorem evec_apply_same (i : Fin 3) (u : Qext K) : evec i u i = u := by simp [evec]

theorem evec_apply_ne {i j : Fin 3} (h : j ≠ i) (u : Qext K) : evec i u j = 0 := by
  simp [evec, Pi.single_eq_of_ne h]

theorem evec_add (i : Fin 3) (u v : Qext K) : evec i (u + v) = evec i u + evec i v := by
  funext k
  by_cases h : k = i
  · subst h
    simp [evec]
  · simp [evec_apply_ne h]

theorem evec_zero (i : Fin 3) : evec i (0 : Qext K) = 0 := by
  funext k
  simp [evec]

theorem Bf_evec_evec_ne {i j : Fin 3} (h : i ≠ j) (u v : Qext K) :
    Bf (evec i u) (evec j v) = 0 := by
  rw [Bf_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = i
  · subst hk
    rw [evec_apply_ne h, map_zero]
  · rw [evec_apply_ne hk, map_zero, LinearMap.zero_apply]

theorem Bf_evec_right (x : QV K (Fin 3)) (i : Fin 3) (u : Qext K) :
    Bf x (evec i u) = qForm (x i) u := by
  rw [Bf_apply]
  exact sum_qForm_single x i u

theorem hI (w : Qext K) : Bf (evec 0 (1 : Qext K)) (evec 1 w) = 0 :=
  Bf_evec_evec_ne (by decide) _ _

@[expose] noncomputable def gI (w : Qext K) : ↥(M10 K) := ⟨eAut (hI w), eAut_mem_M10 (hI w)⟩

theorem coe_gI (w : Qext K) : (gI w : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = eAut (hI w) := rfl

theorem gI_mul_self (w : Qext K) : gI w * gI w = 1 :=
  Subtype.ext (eAut_mul_self (hI w))

theorem gI_apply (w : Qext K) (x : QV K (Fin 3)) :
    (gI w : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) x =
      x + Bf x (evec 0 1) • evec 1 w + Bf x (evec 1 w) • evec 0 (1 : Qext K) := rfl

theorem gI_comm (w w' : Qext K) : gI w * gI w' = gI w' * gI w := by
  apply Subtype.ext
  refine LinearEquiv.ext fun x => ?_
  have h1 : Bf (evec 1 w) (evec 0 (1 : Qext K)) = 0 := by rw [Bf_comm]; exact hI w
  have h2 : Bf (evec 1 w') (evec 0 (1 : Qext K)) = 0 := by rw [Bf_comm]; exact hI w'
  have h3 : Bf (evec 0 (1 : Qext K)) (evec 1 w) = 0 := hI w
  have h4 : Bf (evec 0 (1 : Qext K)) (evec 1 w') = 0 := hI w'
  have h5 : Bf (evec 1 w') (evec 1 w) = Bf (evec 1 w) (evec 1 w') := Bf_comm _ _
  show (gI w : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ((gI w' : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) x) =
    (gI w' : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) ((gI w : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) x)
  simp only [gI_apply, map_add, map_smul, Bf_self, h1, h2, h3, h4, h5, zero_smul, add_zero]
  module

end TypeI

section TypeIb

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} {z : (Qext K)ˣ}

theorem torusEquiv_evec (x : Fin 3 → (Qext K)ˣ) (i : Fin 3) (u : Qext K) :
    torusEquiv x (evec i u) = evec i ((x i : Qext K) * u) := by
  funext k
  by_cases h : k = i
  · subst h
    rw [torusEquiv_apply, evec_apply_same, evec_apply_same]
  · rw [torusEquiv_apply, evec_apply_ne h, evec_apply_ne h, mul_zero]

theorem eAut_congr {a b a' b' : QV K (Fin 3)} (ha : a = a') (hb : b = b') (hab : Bf a b = 0)
    (hab' : Bf a' b' = 0) : eAut hab = eAut hab' := by
  subst ha
  subst hb
  rfl

theorem conj_gI {t : ↥(M10 K)} {x : Fin 3 → (Qext K)ˣ}
    (ht : (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x) (hx0 : x 0 = 1) (w : Qext K) :
    t * gI w * t⁻¹ = gI ((x 1 : Qext K) * w) := by
  apply Subtype.ext
  have h1 : torusEquiv x (evec 0 (1 : Qext K)) = evec 0 1 := by
    rw [torusEquiv_evec, hx0]
    simp
  have h2 : torusEquiv x (evec 1 w) = evec 1 ((x 1 : Qext K) * w) := torusEquiv_evec x 1 w
  have hM : torusEquiv x ∈ M10 K := ht ▸ t.2
  have hgab : Bf (torusEquiv x (evec 0 (1 : Qext K))) (torusEquiv x (evec 1 w)) = 0 := by
    rw [h1, h2]
    exact hI _
  show (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) * eAut (hI w) *
    (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))⁻¹ = eAut (hI ((x 1 : Qext K) * w))
  rw [ht, conj_eAut hM (hI w) hgab]
  exact eAut_congr h1 h2 _ _

theorem gI_fix (w c : Qext K) :
    (gI w : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (e2v c) = e2v c := by
  have e1 : Bf (e2v c) (evec 0 (1 : Qext K)) = 0 := by
    rw [Bf_evec_right]
    have : e2v c 0 = 0 := e2v_zero_coord c
    rw [this]
    simp
  have e2 : Bf (e2v c) (evec 1 w) = 0 := by
    rw [Bf_evec_right]
    have : e2v c 1 = 0 := e2v_one_coord c
    rw [this]
    simp
  rw [gI_apply, e1, e2]
  simp

theorem gI_mem_range (hz1 : z ≠ 1) (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (w : Qext K) : gI w ∈ (blk2 (K := K)).range := by
  obtain ⟨h, hh, hh'⟩ := exists_blk2_of_fix hz1 hzK (gI w).2 (gI_fix w)
  exact ⟨⟨h, hh⟩, Subtype.ext hh'⟩

end TypeIb

section TypeIc

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} {z : (Qext K)ˣ}

theorem exists_trace_one : ∃ b : Qext K, trQ b = 1 := by
  obtain ⟨b₀, hb₀⟩ : ∃ b : Qext K, trQ b ≠ 0 := by
    by_contra h
    push Not at h
    exact trQ_ne_zero (LinearMap.ext h)
  refine ⟨(trQ b₀)⁻¹ • b₀, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hb₀]

theorem qForm_one_right (b : Qext K) : qForm b (1 : Qext K) = trQ b := by
  rw [qForm_apply, map_one, mul_one]

theorem gI_apply_evec_zero {b : Qext K} (hb : trQ b = 1) (w : Qext K) :
    (gI w : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (evec 0 b) = evec 0 b + evec 1 w := by
  have e1 : Bf (evec 0 b) (evec 0 (1 : Qext K)) = 1 := by
    rw [Bf_evec_right, evec_apply_same, qForm_one_right, hb]
  have e2 : Bf (evec 0 b) (evec 1 w) = 0 := Bf_evec_evec_ne (by decide) _ _
  rw [gI_apply, e1, e2]
  simp

theorem exists_U_typeI (hpq : p ∣ Nat.card K + 1) (hzp : z ^ p = 1) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) :
    ∃ U : Subgroup ↥(M10 K), U ≤ (blk2 (K := K)).range ∧ IsPGroup 2 ↥U ∧
      TI p K ≤ Subgroup.normalizer (U : Set ↥(M10 K)) ∧
      ∃ u ∈ U, ∃ t ∈ TI p K, u * t ≠ t * u := by
  refine ⟨Subgroup.closure (Set.range (gI (K := K))), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨w, rfl⟩
    exact gI_mem_range hz1 hzK w
  · exact isPGroup_two_closure (by rintro _ ⟨w, rfl⟩; exact gI_mul_self w) (by
      rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩
      exact gI_comm w w')
  · apply le_normalizer_closure
    rintro t ht _ ⟨w, rfl⟩
    obtain ⟨x, hxP, htx⟩ := mem_torusSub.1 ht
    exact ⟨(x 1 : Qext K) * w, (conj_gI htx hxP.2 w).symm⟩
  · have hx : ∀ i, (![1, z, 1] i : (Qext K)ˣ) ^ p = 1 := fun i => by
      fin_cases i <;> simp [hzp]
    set ρ : ↥(M10 K) := ⟨torusEquiv ![1, z, 1], torusEquiv_mem_M10 hpq hx⟩ with hρ
    have hρT : ρ ∈ TI p K := ⟨![1, z, 1], ⟨hx, rfl⟩, rfl⟩
    refine ⟨gI 1, Subgroup.subset_closure ⟨1, rfl⟩, ρ, hρT, fun hcomm => ?_⟩
    have hc : ρ * gI 1 * ρ⁻¹ = gI 1 := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hρx : (ρ : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv ![1, z, 1] := rfl
    rw [conj_gI hρx rfl 1] at hc
    obtain ⟨b, hb⟩ := exists_trace_one (K := K)
    have h1 := congrArg (fun g : ↥(M10 K) =>
      (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (evec 0 b)) hc
    simp only [gI_apply_evec_zero hb] at h1
    have h2 := congrFun (add_left_cancel h1) 1
    rw [evec_apply_same, evec_apply_same] at h2
    apply hz1
    apply Units.ext
    simpa using h2

end TypeIc

section TypeII

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} {z : (Qext K)ˣ}

@[expose] noncomputable def pv (u : Qext K) : QV K (Fin 3) := ![u, u, 0]

theorem pv_apply_zero (u : Qext K) : pv u 0 = u := rfl

theorem pv_apply_one (u : Qext K) : pv u 1 = u := rfl

theorem pv_apply_two (u : Qext K) : pv u 2 = 0 := rfl

theorem Bf_pv (u v : Qext K) : Bf (pv u) (pv v) = 0 := by
  rw [Bf_apply, Fin.sum_univ_three, pv_apply_zero, pv_apply_zero, pv_apply_one, pv_apply_one,
    pv_apply_two, pv_apply_two]
  simp [CharTwo.add_self_eq_zero]

@[expose] noncomputable def gII (u : Qext K) : ↥(M10 K) := ⟨tvAut (pv u), tvAut_mem_M10 _⟩

theorem coe_gII (u : Qext K) : (gII u : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = tvAut (pv u) := rfl

theorem gII_mul_self (u : Qext K) : gII u * gII u = 1 := Subtype.ext (tvAut_mul_self _)

theorem gII_comm (u v : Qext K) : gII u * gII v = gII v * gII u :=
  Subtype.ext (tvAut_comm (Bf_pv u v))

theorem torusEquiv_pv (x : Fin 3 → (Qext K)ˣ) (hx : x 0 = x 1) (u : Qext K) :
    torusEquiv x (pv u) = pv ((x 0 : Qext K) * u) := by
  funext k
  fin_cases k
  · show (x 0 : Qext K) * pv u 0 = pv ((x 0 : Qext K) * u) 0
    rfl
  · show (x 1 : Qext K) * pv u 1 = pv ((x 0 : Qext K) * u) 1
    rw [← hx]
    rfl
  · show (x 2 : Qext K) * pv u 2 = pv ((x 0 : Qext K) * u) 2
    rw [pv_apply_two, pv_apply_two, mul_zero]

theorem conj_gII {t : ↥(M10 K)} {x : Fin 3 → (Qext K)ˣ}
    (ht : (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x) (hx : x 0 = x 1) (u : Qext K) :
    t * gII u * t⁻¹ = gII ((x 0 : Qext K) * u) := by
  apply Subtype.ext
  have hM : torusEquiv x ∈ M10 K := ht ▸ t.2
  show (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) * tvAut (pv u) *
    (t : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))⁻¹ = tvAut (pv ((x 0 : Qext K) * u))
  rw [ht, conj_tvAut hM, torusEquiv_pv x hx]

theorem gII_fix (u c : Qext K) :
    (gII u : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (e2v c) = e2v c := by
  have e1 : Bf (e2v c) (pv u) = 0 := by
    rw [Bf_apply, Fin.sum_univ_three, pv_apply_zero, pv_apply_one, pv_apply_two,
      e2v_zero_coord, e2v_one_coord]
    simp
  rw [coe_gII, tvAut_apply, e1]
  simp

theorem gII_mem_range (hz1 : z ≠ 1) (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (u : Qext K) : gII u ∈ (blk2 (K := K)).range := by
  obtain ⟨h, hh, hh'⟩ := exists_blk2_of_fix hz1 hzK (gII u).2 (gII_fix u)
  exact ⟨⟨h, hh⟩, Subtype.ext hh'⟩

theorem gII_apply_evec_zero (b u : Qext K) :
    (gII u : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (evec 0 b) = evec 0 b + qForm b u • pv u := by
  have e1 : Bf (evec 0 b) (pv u) = qForm b u := by
    rw [Bf_apply, Fin.sum_univ_three, evec_apply_same, evec_apply_ne (by decide),
      evec_apply_ne (by decide), pv_apply_zero, pv_apply_one, pv_apply_two]
    simp
  rw [coe_gII, tvAut_apply, e1]

theorem exists_U_typeII (hpq : p ∣ Nat.card K + 1) (hzp : z ^ p = 1) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) :
    ∃ U : Subgroup ↥(M10 K), U ≤ (blk2 (K := K)).range ∧ IsPGroup 2 ↥U ∧
      TII p K ≤ Subgroup.normalizer (U : Set ↥(M10 K)) ∧
      ∃ u ∈ U, ∃ t ∈ TII p K, u * t ≠ t * u := by
  refine ⟨Subgroup.closure (Set.range (gII (K := K))), ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    exact gII_mem_range hz1 hzK u
  · exact isPGroup_two_closure (by rintro _ ⟨u, rfl⟩; exact gII_mul_self u) (by
      rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
      exact gII_comm u v)
  · apply le_normalizer_closure
    rintro t ht _ ⟨u, rfl⟩
    obtain ⟨x, hxP, htx⟩ := mem_torusSub.1 ht
    exact ⟨(x 0 : Qext K) * u, (conj_gII htx hxP.2 u).symm⟩
  · have hx : ∀ i, (![z, z, 1] i : (Qext K)ˣ) ^ p = 1 := fun i => by
      fin_cases i <;> simp [hzp]
    set ρ : ↥(M10 K) := ⟨torusEquiv ![z, z, 1], torusEquiv_mem_M10 hpq hx⟩ with hρ
    have hρT : ρ ∈ TII p K := ⟨![z, z, 1], ⟨hx, rfl⟩, rfl⟩
    refine ⟨gII 1, Subgroup.subset_closure ⟨1, rfl⟩, ρ, hρT, fun hcomm => ?_⟩
    have hc : ρ * gII 1 * ρ⁻¹ = gII 1 := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hρx : (ρ : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv ![z, z, 1] := rfl
    rw [conj_gII hρx rfl 1] at hc
    simp only [Matrix.cons_val_zero, mul_one] at hc
    obtain ⟨b, hb⟩ := exists_trace_one (K := K)
    have h1 := congrArg (fun g : ↥(M10 K) =>
      (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) (evec 0 b)) hc
    simp only [gII_apply_evec_zero] at h1
    have h2 := congrFun (add_left_cancel h1) 1
    simp only [Pi.smul_apply, pv_apply_one, Algebra.smul_def, qForm_one_right, hb, map_one,
      mul_one] at h2
    apply hzK
    refine ⟨(qForm b (z : Qext K))⁻¹, ?_⟩
    rw [map_inv₀]
    exact (eq_inv_of_mul_eq_one_right h2).symm

end TypeII

section Count

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} {z : (Qext K)ˣ}

theorem torusSub_mem_blk2_iff (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) {g : ↥(M10 K)}
    {x : Fin 3 → (Qext K)ˣ} (hg : (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3)) = torusEquiv x) :
    g ∈ (blk2 (K := K)).range ↔ x 2 = 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    have h1 : torusEquiv x (e2v 1) = e2v 1 := by
      rw [← hg]
      exact blk2Aut_e2v h.1 1
    have h2 : torusEquiv x (e2v 1) = e2v ((x 2 : Qext K) * 1) := torusEquiv_evec x 2 1
    rw [h2] at h1
    have h3 := congrFun h1 2
    rw [e2v_two_coord, e2v_two_coord, mul_one] at h3
    exact Units.ext h3
  · intro hx2
    obtain ⟨h, hh, hh'⟩ := exists_blk2_of_fix hz1 hzK g.2 (fun c => by
      rw [hg]
      have : torusEquiv x (e2v c) = e2v ((x 2 : Qext K) * c) := torusEquiv_evec x 2 c
      rw [this, hx2]
      simp)
    exact ⟨⟨h, hh⟩, Subtype.ext hh'⟩

theorem card_torusSub_inf_blk2 (hpq : p ∣ Nat.card K + 1) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    {P : Subgroup (Fin 3 → (Qext K)ˣ)} (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1)
    (ψ : ↥(rootsOfUnity p (Qext K)) → (Fin 3 → (Qext K)ˣ)) (hψP : ∀ u, ψ u ∈ P)
    (hψ2 : ∀ u, ψ u 2 = 1) (hψinj : Function.Injective ψ)
    (hψsurj : ∀ x ∈ P, x 2 = 1 → ∃ u, ψ u = x) :
    Nat.card ↥(torusSub P ⊓ (blk2 (K := K)).range) = Nat.card ↥(rootsOfUnity p (Qext K)) := by
  have hmem : ∀ u, (⟨torusEquiv (ψ u), torusEquiv_mem_M10 hpq (hPe _ (hψP u))⟩ : ↥(M10 K)) ∈
      torusSub P ⊓ (blk2 (K := K)).range := fun u =>
    ⟨⟨ψ u, hψP u, rfl⟩, (torusSub_mem_blk2_iff hz1 hzK rfl).2 (hψ2 u)⟩
  let ι : ↥(rootsOfUnity p (Qext K)) → ↥(torusSub P ⊓ (blk2 (K := K)).range) := fun u =>
    ⟨⟨torusEquiv (ψ u), torusEquiv_mem_M10 hpq (hPe _ (hψP u))⟩, hmem u⟩
  have hinj : Function.Injective ι := by
    intro u u' h
    apply hψinj
    have h1 : torusEquiv (ψ u) = torusEquiv (ψ u') := congrArg (fun g :
      ↥(torusSub P ⊓ (blk2 (K := K)).range) =>
        ((g : ↥(M10 K)) : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))) h
    funext k
    have := congrFun (congrArg (fun g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3) =>
      g (evec k 1)) h1) k
    simp only [torusEquiv_evec, evec_apply_same, mul_one] at this
    exact Units.ext this
  have hsurj : Function.Surjective ι := by
    rintro ⟨g, hgP, hgB⟩
    obtain ⟨x, hxP, hgx⟩ := mem_torusSub.1 hgP
    have hx2 : x 2 = 1 := (torusSub_mem_blk2_iff hz1 hzK hgx).1 hgB
    obtain ⟨u, hu⟩ := hψsurj x hxP hx2
    refine ⟨u, Subtype.ext (Subtype.ext ?_)⟩
    show torusEquiv (ψ u) = (g : QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))
    rw [hu, hgx]
  exact (Nat.card_congr (Equiv.ofBijective ι ⟨hinj, hsurj⟩)).symm

theorem card_TI_inf_blk2 (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) :
    Nat.card ↥(TI p K ⊓ (blk2 (K := K)).range) = p := by
  rw [TI, card_torusSub_inf_blk2 hpq hz1 hzK (P := planeI p K) (fun x hx => hx.1)
    (fun u => ![1, ((u : (Qext K)ˣ)), 1]) ?_ ?_ ?_ ?_, card_rootsOfUnity_eq' hp.pos hζ]
  · intro u
    refine ⟨fun i => ?_, rfl⟩
    fin_cases i
    · simp
    · exact (mem_rootsOfUnity p _).1 u.2
    · simp
  · intro u
    rfl
  · intro u u' h
    apply Subtype.ext
    have := congrFun h 1
    simpa using this
  · intro x hx hx2
    refine ⟨⟨x 1, (mem_rootsOfUnity p _).2 (hx.1 1)⟩, ?_⟩
    funext k
    fin_cases k
    · exact hx.2.symm
    · rfl
    · exact hx2.symm

theorem card_TII_inf_blk2 (hp : p.Prime) (hpq : p ∣ Nat.card K + 1)
    (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) (hz1 : z ≠ 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K))) :
    Nat.card ↥(TII p K ⊓ (blk2 (K := K)).range) = p := by
  rw [TII, card_torusSub_inf_blk2 hpq hz1 hzK (P := planeII p K) (fun x hx => hx.1)
    (fun u => ![((u : (Qext K)ˣ)), ((u : (Qext K)ˣ)), 1]) ?_ ?_ ?_ ?_,
    card_rootsOfUnity_eq' hp.pos hζ]
  · intro u
    refine ⟨fun i => ?_, rfl⟩
    fin_cases i
    · exact (mem_rootsOfUnity p _).1 u.2
    · exact (mem_rootsOfUnity p _).1 u.2
    · simp
  · intro u
    rfl
  · intro u u' h
    apply Subtype.ext
    have := congrFun h 0
    simpa using this
  · intro x hx hx2
    refine ⟨⟨x 1, (mem_rootsOfUnity p _).2 (hx.1 1)⟩, ?_⟩
    funext k
    fin_cases k
    · exact hx.2.symm
    · rfl
    · exact hx2.symm

theorem b10_mem_TI (hzp : z ^ p = 1) (hmem : bAut z ∈ M10 K) : b10 z hmem ∈ TI p K := by
  have hx : ∀ i, (![1, 1, z] i : (Qext K)ˣ) ^ p = 1 := fun i => by
    fin_cases i <;> simp [hzp]
  exact ⟨![1, 1, z], ⟨hx, rfl⟩, rfl⟩

theorem b10_mem_TII (hzp : z ^ p = 1) (hmem : bAut z ∈ M10 K) : b10 z hmem ∈ TII p K := by
  have hx : ∀ i, (![1, 1, z] i : (Qext K)ˣ) ^ p = 1 := fun i => by
    fin_cases i <;> simp [hzp]
  exact ⟨![1, 1, z], ⟨hx, rfl⟩, rfl⟩

theorem pow_eq_one_of_mem_torusSub {P : Subgroup (Fin 3 → (Qext K)ˣ)}
    (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1) {g : ↥(M10 K)} (hg : g ∈ torusSub P) : g ^ p = 1 := by
  obtain ⟨x, hxP, hgx⟩ := mem_torusSub.1 hg
  apply Subtype.ext
  rw [Subgroup.coe_pow, hgx, Subgroup.coe_one]
  have : torusEquiv x ^ p = torusEquiv (x ^ p) := (map_pow torusHom x p).symm
  rw [this]
  have hxp : x ^ p = 1 := funext fun i => hPe x hxP i
  rw [hxp, torusEquiv_one]

end Count

end CFSG.RankThree.PartOne.KLAY10
