module

public import CFSG.Quasithin.AppendixH.H9.NaturalDualModel
import CFSG.Quasithin.AppendixH.H9.F2Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

variable {n : ℕ}

private theorem mult_mul_self_eq_one (x : Multiplicative (Fin n → ZMod 2)) : x * x = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_one]
  exact vec_add_self x.toAdd

@[expose] def pairVec (a b : Fin n → ZMod 2) : PairN n :=
  (Multiplicative.ofAdd a, Multiplicative.ofAdd b)

theorem pairVec_mul (a b a' b' : Fin n → ZMod 2) :
    pairVec a b * pairVec a' b' = pairVec (a + a') (b + b') := by
  rfl

theorem pairVec_one : (1 : PairN n) = pairVec 0 0 := by
  rfl

theorem pairVec_surj (x : PairN n) : ∃ a b : Fin n → ZMod 2, x = pairVec a b :=
  ⟨x.1.toAdd, x.2.toAdd, by ext <;> simp [pairVec]⟩

theorem pairVec_inj {a b a' b' : Fin n → ZMod 2} :
    pairVec a b = pairVec a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    rw [pairVec, pairVec, Prod.ext_iff] at h
    exact ⟨Multiplicative.ofAdd.injective h.1, Multiplicative.ofAdd.injective h.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem pairVec_inv (a b : Fin n → ZMod 2) : (pairVec a b)⁻¹ = pairVec a b := by
  apply inv_eq_of_mul_eq_one_right
  calc pairVec a b * pairVec a b = pairVec (a + a) (b + b) := pairVec_mul a b a b
    _ = pairVec 0 0 := by
      rw [show a + a = 0 from vec_add_self a, show b + b = 0 from vec_add_self b]
    _ = 1 := pairVec_one.symm

theorem pairN_sq (x : PairN n) : x ^ 2 = 1 := by
  rw [pow_two]
  exact Prod.ext (mult_mul_self_eq_one x.1) (mult_mul_self_eq_one x.2)

theorem mem_V1n {x : PairN n} : x ∈ V1n n ↔ x.2 = 1 := by
  rw [V1n, Subgroup.mem_prod]
  simp

theorem mem_V2n {x : PairN n} : x ∈ V2n n ↔ x.1 = 1 := by
  rw [V2n, Subgroup.mem_prod]
  simp

theorem pairVec_mem_V1n (a : Fin n → ZMod 2) : pairVec a 0 ∈ V1n n :=
  mem_V1n.mpr rfl

theorem pairVec_mem_V2n (b : Fin n → ZMod 2) : pairVec 0 b ∈ V2n n :=
  mem_V2n.mpr rfl

theorem dualGLn_val (A : GL (Fin n) (ZMod 2)) :
    ((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((A⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ := by
  rfl

theorem dualGLn_dualGLn (A : GL (Fin n) (ZMod 2)) : dualGLn n (dualGLn n A) = A := by
  apply Units.ext
  change ((((dualGLn n A)⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)))ᵀ = ((A : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2))
  rw [show (((dualGLn n A)⁻¹ : GL (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
      ((A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ from rfl,
    Matrix.transpose_transpose]

theorem pairActN_pairVec (A : GL (Fin n) (ZMod 2)) (a b : Fin n → ZMod 2) :
    pairActN n A (pairVec a b) =
      pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)
        (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b) := by
  rfl

theorem swapN_pairVec (a b : Fin n → ZMod 2) : swapN n (pairVec a b) = pairVec b a := by
  rfl

theorem swapN_apply (x : PairN n) : swapN n x = (x.2, x.1) := by
  rfl

theorem swapN_mul_self : swapN n * swapN n = 1 := by
  apply MulEquiv.ext
  intro x
  rfl

theorem swapN_inv : (swapN n)⁻¹ = swapN n :=
  inv_eq_of_mul_eq_one_right (swapN_mul_self (n := n))

theorem swapN_mul_pairActN (A : GL (Fin n) (ZMod 2)) :
    swapN n * pairActN n A = pairActN n (dualGLn n A) * swapN n := by
  apply MulEquiv.ext
  intro x
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  simp only [MulAut.mul_apply, pairActN_pairVec, swapN_pairVec, dualGLn_dualGLn]

private theorem swap_mul_pairAct_mul_swap (A : GL (Fin n) (ZMod 2)) :
    swapN n * pairActN n A * swapN n = pairActN n (dualGLn n A) := by
  rw [swapN_mul_pairActN, mul_assoc, swapN_mul_self, mul_one]

theorem pairActN_injective : Function.Injective (pairActN n) := by
  intro A B h
  have h1 : ∀ a : Fin n → ZMod 2,
      (A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a =
        (B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a := by
    intro a
    have h2 := congrArg (fun e : MulAut (PairN n) => e (pairVec a 0)) h
    simp only [pairActN_pairVec, Matrix.mulVec_zero] at h2
    exact (pairVec_inj.mp h2).1
  apply Units.ext
  exact Matrix.ext_of_mulVec_single fun j => h1 (Pi.single j 1)

theorem mem_Lg_iff {g : MulAut (PairN n)} : g ∈ Lg n ↔ ∃ A : GL (Fin n) (ZMod 2), pairActN n A = g := by
  rw [Lg, MonoidHom.mem_range]

theorem pairActN_mem_Lg (A : GL (Fin n) (ZMod 2)) : pairActN n A ∈ Lg n := by
  rw [mem_Lg_iff]
  exact ⟨A, rfl⟩

theorem Lg_le_Mg : Lg n ≤ Mg n := le_sup_left

theorem swapN_mem_Mg : swapN n ∈ Mg n :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers (swapN n))

theorem outer_mem_Mg (A : GL (Fin n) (ZMod 2)) : pairActN n A * swapN n ∈ Mg n :=
  (Mg n).mul_mem (Lg_le_Mg (pairActN_mem_Lg A)) swapN_mem_Mg

private theorem mem_zpowers_swapN {z : MulAut (PairN n)}
    (hz : z ∈ Subgroup.zpowers (swapN n)) : z = 1 ∨ z = swapN n := by
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨k, hk⟩ := hz
  rw [← hk]
  have h2 : (swapN n) ^ (2 : ℕ) = 1 := by
    rw [pow_two, swapN_mul_self]
  rw [zpow_eq_zpow_emod' k h2]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

theorem mem_Mg_iff {g : MulAut (PairN n)} :
    g ∈ Mg n ↔ g ∈ Lg n ∨ ∃ A : GL (Fin n) (ZMod 2), g = pairActN n A * swapN n := by
  have hnorm : Subgroup.zpowers (swapN n) ≤
      Subgroup.normalizer ((Lg n : Set (MulAut (PairN n)))) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh l hl
    rcases mem_zpowers_swapN hh with rfl | rfl
    · simpa using hl
    · rw [mem_Lg_iff] at hl
      obtain ⟨B, rfl⟩ := hl
      rw [swapN_inv, swap_mul_pairAct_mul_swap]
      exact pairActN_mem_Lg _
  have hset : g ∈ (Lg n ⊔ Subgroup.zpowers (swapN n) : Subgroup (MulAut (PairN n))) ↔
      ∃ l ∈ (Lg n : Set (MulAut (PairN n))),
        ∃ z ∈ (Subgroup.zpowers (swapN n) : Set (MulAut (PairN n))), l * z = g := by
    rw [← SetLike.mem_coe,
      Subgroup.coe_mul_of_right_le_normalizer_left (Lg n) (Subgroup.zpowers (swapN n)) hnorm,
      Set.mem_mul]
  rw [Mg, hset]
  constructor
  · rintro ⟨l, hl, z, hz, hgz⟩
    rcases mem_zpowers_swapN hz with rfl | rfl
    · left
      rw [← hgz, mul_one]
      exact hl
    · right
      change l ∈ Lg n at hl
      rw [mem_Lg_iff] at hl
      obtain ⟨A, rfl⟩ := hl
      exact ⟨A, hgz.symm⟩
  · rintro (hg | ⟨A, rfl⟩)
    · exact ⟨g, hg, 1, Subgroup.one_mem _, mul_one g⟩
    · exact ⟨pairActN n A, pairActN_mem_Lg A, swapN n, Subgroup.mem_zpowers _, rfl⟩

theorem swapN_not_mem_Lg (hn : 0 < n) : swapN n ∉ Lg n := by
  intro h
  rw [mem_Lg_iff] at h
  obtain ⟨A, hA⟩ := h
  let i : Fin n := ⟨0, hn⟩
  have h1 := congrArg (fun e : MulAut (PairN n) => e (pairVec (Pi.single i 1) 0)) hA
  rw [pairActN_pairVec A (Pi.single i 1) 0, swapN_pairVec, Matrix.mulVec_zero] at h1
  have h2 : (0 : Fin n → ZMod 2) = Pi.single i 1 := (pairVec_inj.mp h1).2
  have h3 := congrFun h2 i
  simp at h3

theorem outer_not_mem_Lg (hn : 0 < n) (A : GL (Fin n) (ZMod 2)) :
    pairActN n A * swapN n ∉ Lg n := by
  intro h
  have hmem : (pairActN n A)⁻¹ ∈ Lg n := (Lg n).inv_mem (pairActN_mem_Lg A)
  have h2 : (pairActN n A)⁻¹ * (pairActN n A * swapN n) ∈ Lg n := (Lg n).mul_mem hmem h
  rw [← mul_assoc, inv_mul_cancel, one_mul] at h2
  exact swapN_not_mem_Lg hn h2

theorem conj_mem_Lg {g : MulAut (PairN n)} (hg : g ∈ Mg n) {l : MulAut (PairN n)} (hl : l ∈ Lg n) :
    g * l * g⁻¹ ∈ Lg n := by
  rw [mem_Mg_iff] at hg
  rcases hg with hg | ⟨A, rfl⟩
  · exact (Lg n).mul_mem ((Lg n).mul_mem hg hl) ((Lg n).inv_mem hg)
  · rw [mem_Lg_iff] at hl
    obtain ⟨B, rfl⟩ := hl
    have hconj : pairActN n A * (swapN n * pairActN n B * swapN n) * (pairActN n A)⁻¹ ∈ Lg n :=
      (Lg n).mul_mem ((Lg n).mul_mem (pairActN_mem_Lg A)
        (by rw [swap_mul_pairAct_mul_swap]; exact pairActN_mem_Lg _))
        ((Lg n).inv_mem (pairActN_mem_Lg A))
    convert hconj using 1
    rw [mul_inv_rev, swapN_inv]
    group

theorem Lg_le_stabSub_V1n : Lg n ≤ stabSub (V1n n) := by
  rintro g hg u
  rw [mem_Lg_iff] at hg
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨a, b, rfl⟩ := pairVec_surj u
  change pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)
      (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b) ∈
      V1n n ↔ pairVec a b ∈ V1n n
  simp only [mem_V1n, pairVec, toAdd_ofAdd, ofAdd_eq_one]
  exact GL_mulVec_eq_zero_iff (dualGLn n A) b

theorem Lg_le_stabSub_V2n : Lg n ≤ stabSub (V2n n) := by
  rintro g hg u
  rw [mem_Lg_iff] at hg
  obtain ⟨A, rfl⟩ := hg
  obtain ⟨a, b, rfl⟩ := pairVec_surj u
  change pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)
      (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b) ∈
      V2n n ↔ pairVec a b ∈ V2n n
  simp only [mem_V2n, pairVec, toAdd_ofAdd, ofAdd_eq_one]
  exact GL_mulVec_eq_zero_iff A a

private theorem pairActN_mul_swapN_not_mem_stabSub (hn : 0 < n) (A : GL (Fin n) (ZMod 2)) :
    pairActN n A * swapN n ∉ stabSub (V1n n) := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hu : pairVec (Pi.single i 1) 0 ∈ V1n n := pairVec_mem_V1n _
  have hmem : (pairActN n A * swapN n) (pairVec (Pi.single i 1) 0) ∈ V1n n :=
    (mem_stabSub.mp h _).mpr hu
  rw [MulAut.mul_apply, swapN_pairVec] at hmem
  rw [show pairActN n A (pairVec 0 (Pi.single i 1)) =
      pairVec ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ 0)
        (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          Pi.single i 1) from rfl] at hmem
  simp only [Matrix.mulVec_zero, mem_V1n, pairVec, toAdd_ofAdd, ofAdd_eq_one] at hmem
  have hzero : (Pi.single i 1 : Fin n → ZMod 2) = 0 :=
    (GL_mulVec_eq_zero_iff (dualGLn n A) _).mp hmem
  have h3 : (1 : ZMod 2) = 0 := by simpa using congrFun hzero i
  exact one_ne_zero h3

theorem Mg_inf_stabSub_V1n (hn : 0 < n) : Mg n ⊓ stabSub (V1n n) = Lg n := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgM, hgS⟩ := (show g ∈ Mg n ∧ g ∈ stabSub (V1n n) from hg)
    rw [mem_Mg_iff] at hgM
    rcases hgM with hgL | ⟨A, hA⟩
    · exact hgL
    · exfalso
      rw [hA] at hgS
      exact pairActN_mul_swapN_not_mem_stabSub hn A hgS
  · intro g hg
    exact ⟨Lg_le_Mg hg, Lg_le_stabSub_V1n hg⟩

theorem card_Lg : Nat.card (Lg n) = Nat.card (GL (Fin n) (ZMod 2)) := by
  rw [Lg, ← Subgroup.map_top (pairActN n),
    Subgroup.card_map_of_injective (pairActN_injective (n := n))]
  exact Subgroup.card_top

theorem relIndex_Lg_Mg (hn : 0 < n) : (Lg n).relIndex (Mg n) = 2 := by
  rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
  refine ⟨swapN n, swapN_mem_Mg, swapN_not_mem_Lg hn, ?_⟩
  intro b hb
  rw [mem_Mg_iff] at hb
  rcases hb with hb | ⟨A, rfl⟩
  · exact Or.inr hb
  · left
    rw [mul_assoc, swapN_mul_self, mul_one]
    exact pairActN_mem_Lg A

theorem card_Mg (hn : 0 < n) : Nat.card (Mg n) = 2 * Nat.card (GL (Fin n) (ZMod 2)) := by
  have h := Subgroup.relIndex_mul_card (H := Lg n) (K := Mg n)
  rw [inf_eq_left.mpr Lg_le_Mg, relIndex_Lg_Mg hn, card_Lg] at h
  exact h.symm

theorem pairQn_pairVec (a b : Fin n → ZMod 2) : pairQn n (pairVec a b) = a ⬝ᵥ b := by
  rfl

theorem pairQn_mul (x y : PairN n) : pairQn n (x * y) = pairQn n x + pairQn n y + polarN n x y := by
  simp only [pairQn, polarN, Prod.fst_mul, Prod.snd_mul, toAdd_mul, Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem polarN_pairVec (a b a' b' : Fin n → ZMod 2) :
    polarN n (pairVec a b) (pairVec a' b') = a ⬝ᵥ b' + a' ⬝ᵥ b := by
  simp only [polarN, pairVec, toAdd_ofAdd, dotProduct, Finset.sum_add_distrib]

theorem pairQn_pairActN (A : GL (Fin n) (ZMod 2)) (x : PairN n) :
    pairQn n (pairActN n A x) = pairQn n x := by
  obtain ⟨a, b, rfl⟩ := pairVec_surj x
  rw [pairActN_pairVec]
  change ((A : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a) ⬝ᵥ
    (((dualGLn n A : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ b) =
    a ⬝ᵥ b
  rw [dualGLn_val, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem pairQn_swapN (x : PairN n) : pairQn n (swapN n x) = pairQn n x := by
  rw [swapN_apply]
  simp only [pairQn]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem pairQn_of_mem_Mg {g : MulAut (PairN n)} (hg : g ∈ Mg n) (x : PairN n) :
    pairQn n (g x) = pairQn n x := by
  rw [mem_Mg_iff] at hg
  rcases hg with hg | ⟨A, hA⟩
  · rw [mem_Lg_iff] at hg
    obtain ⟨B, rfl⟩ := hg
    exact pairQn_pairActN B x
  · rw [hA, MulAut.mul_apply, pairQn_pairActN, pairQn_swapN]

private theorem polarN_eq (x y : PairN n) :
    polarN n x y = pairQn n (x * y) + pairQn n x + pairQn n y := by
  rw [pairQn_mul]
  have h : (pairQn n x + pairQn n y + polarN n x y) + pairQn n x + pairQn n y =
      polarN n x y + (pairQn n x + pairQn n x) + (pairQn n y + pairQn n y) := by abel
  rw [h, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero, add_zero]

theorem polarN_of_mem_Mg {g : MulAut (PairN n)} (hg : g ∈ Mg n) (x y : PairN n) :
    polarN n (g x) (g y) = polarN n x y := by
  have h1 : polarN n (g x) (g y) =
      pairQn n (g (x * y)) + pairQn n (g x) + pairQn n (g y) := by
    rw [polarN_eq, map_mul g x y]
  rw [h1, pairQn_of_mem_Mg hg (x * y), pairQn_of_mem_Mg hg x, pairQn_of_mem_Mg hg y,
    polarN_eq]

theorem polarN_comm (x y : PairN n) : polarN n x y = polarN n y x := by
  simp only [polarN]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem polarN_one_left (y : PairN n) : polarN n 1 y = 0 := by
  simp [polarN]

theorem perpN_map_of_mem_Mg {g : MulAut (PairN n)} (hg : g ∈ Mg n) (S : Subgroup (PairN n)) :
    perpN n (S.map (g : MulAut (PairN n)).toMonoidHom) = (perpN n S).map (g : MulAut (PairN n)).toMonoidHom := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ x, ?_, ?_⟩
    · change ∀ s ∈ S, polarN n (g⁻¹ x) s = 0
      have hx' : ∀ t ∈ S.map (g : MulAut (PairN n)).toMonoidHom, polarN n x t = 0 := hx
      intro s hs
      have h1 : g s ∈ S.map (g : MulAut (PairN n)).toMonoidHom :=
        (Subgroup.mem_map).mpr ⟨s, hs, rfl⟩
      have h2 : polarN n x (g s) = 0 := hx' (g s) h1
      have h3 : polarN n (g (g⁻¹ x)) (g s) = polarN n (g⁻¹ x) s :=
        polarN_of_mem_Mg hg (g⁻¹ x) s
      rw [show g (g⁻¹ x) = x from MulEquiv.apply_symm_apply g x] at h3
      rw [← h3]
      exact h2
    · exact MulEquiv.apply_symm_apply g x
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [← hxy]
    change ∀ t ∈ S.map (g : MulAut (PairN n)).toMonoidHom, polarN n (g y) t = 0
    intro t ht
    rw [Subgroup.mem_map] at ht
    obtain ⟨s, hs, hts⟩ := ht
    subst hts
    change polarN n (g y) (g s) = 0
    rw [polarN_of_mem_Mg hg y s]
    exact (show ∀ s ∈ S, polarN n y s = 0 from hy) s hs

theorem mem_perpN {S : Subgroup (PairN n)} {x : PairN n} :
    x ∈ perpN n S ↔ ∀ s ∈ S, polarN n x s = 0 := Iff.rfl

end CFSG.ASVolI.ChH
