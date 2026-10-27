module

public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
import CFSG.LocalAnalysis.StandardType.GGSignedCoordReflGroup

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

open scoped BigOperators

variable {n p : ℕ}

private theorem prod_toAdd_permAut_coord (σ : Equiv.Perm (Fin n))
    (f : Fin n → Multiplicative (ZMod p)) :
    ∏ i, toAdd (permAut σ f i) = ∏ i, toAdd (f i) := by
  have h : (fun i => toAdd (permAut σ f i)) = fun i => toAdd (f (σ⁻¹ i)) := by
    funext i
    rw [permAut_apply, Function.comp_apply]
  rw [h]
  exact Equiv.prod_comp σ⁻¹ (fun i => toAdd (f i))

private theorem prod_toAdd_sgnAut_coord (i : Fin n) (f : Fin n → Multiplicative (ZMod p)) :
    ∏ j, toAdd (sgnAut i f j) = -∏ j, toAdd (f j) := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => toAdd (sgnAut i f j))
      (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => toAdd (f j)) (Finset.mem_univ i)]
  have h : ∏ j ∈ Finset.univ.erase i, toAdd (sgnAut i f j) =
      ∏ j ∈ Finset.univ.erase i, toAdd (f j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [sgnAut_apply, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h, sgnAut_apply, Function.update_self, toAdd_inv]
  ring

private theorem sgnAut_inv (i : Fin n) :
    (sgnAut i : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = sgnAut i :=
  inv_eq_of_mul_eq_one_right (by simpa [sq] using sgnAut_sq i)

private theorem negTrans_mem_coordProdStab_coord (a b : Fin n) :
    sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ ∈ coordProdStab n p := by
  intro f
  rw [sgnAut_inv, MulAut.mul_apply, MulAut.mul_apply,
    prod_toAdd_sgnAut_coord a (permAut (Equiv.swap a b) (sgnAut a f)),
    prod_toAdd_permAut_coord (Equiv.swap a b) (sgnAut a f),
    prod_toAdd_sgnAut_coord a f]
  ring

private theorem prod_toAdd_of_signedPerm_coord {u : MulAut (Fin n → Multiplicative (ZMod p))}
    {π : Equiv.Perm (Fin n)} {ε : Fin n → ZMod p}
    (hu : ∀ f i, toAdd (u f (π i)) = ε i * toAdd (f i))
    (f : Fin n → Multiplicative (ZMod p)) :
    ∏ i, toAdd (u f i) = (∏ i, ε i) * ∏ i, toAdd (f i) := by
  rw [← Equiv.prod_comp π (fun i => toAdd (u f i))]
  rw [show ∏ i, toAdd (u f (π i)) = ∏ i, ε i * toAdd (f i) from
    Finset.prod_congr rfl fun i _ => hu f i]
  exact Finset.prod_mul_distrib

private theorem diagAut_mul (d e : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1)
    (he : ∀ i, e i * e i = 1) (hde : ∀ i, (d i * e i) * (d i * e i) = 1) :
    diagAut d hd * diagAut e he = diagAut (fun i => d i * e i) hde := by
  refine MulEquiv.ext fun f => ?_
  funext i
  rw [MulAut.mul_apply, diagAut_apply, diagAut_apply, diagAut_apply, toAdd_ofAdd,
    mul_assoc]

private theorem diagAut_mul_self (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1) :
    diagAut d hd * diagAut d hd = 1 := by
  refine MulEquiv.ext fun f => ?_
  funext i
  rw [MulAut.mul_apply, diagAut_apply, diagAut_apply, toAdd_ofAdd, ← mul_assoc, hd i,
    one_mul, ofAdd_toAdd]
  rfl

private theorem diagAut_inv (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1) :
    (diagAut d hd)⁻¹ = diagAut d hd :=
  inv_eq_of_mul_eq_one_right (diagAut_mul_self d hd)

private theorem diagAut_one :
    diagAut (fun _ : Fin n => (1 : ZMod p)) (fun _ => one_mul 1) = 1 := by
  refine MulEquiv.ext fun f => ?_
  funext i
  rw [diagAut_apply, one_mul, ofAdd_toAdd]
  rfl

private theorem sgnAut_eq_diagAut (k : Fin n)
    (hd : ∀ i, Function.update (fun _ : Fin n => (1 : ZMod p)) k (-1) i *
      Function.update (fun _ : Fin n => (1 : ZMod p)) k (-1) i = 1) :
    (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p))) =
      diagAut (Function.update (fun _ : Fin n => (1 : ZMod p)) k (-1)) hd := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
  rw [sgnAut_apply, diagAut_apply, toAdd_ofAdd]
  by_cases hi : i = k
  · subst hi
    rw [Function.update_self, Function.update_self, toAdd_inv]
    ring
  · rw [Function.update_of_ne hi, Function.update_of_ne hi, one_mul]

private theorem toAdd_diagAut_conj_permAut_swap_apply (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) (a b : Fin n)
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    toAdd (((diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ :
      MulAut (Fin n → Multiplicative (ZMod p))) f) i) =
      if i = a then d a * d b * toAdd (f b)
      else if i = b then d a * d b * toAdd (f a) else toAdd (f i) := by
  rw [diagAut_inv, MulAut.mul_apply, MulAut.mul_apply, diagAut_apply, permAut_apply,
    Function.comp_apply, Equiv.swap_inv, diagAut_apply, toAdd_ofAdd, toAdd_ofAdd]
  by_cases hia : i = a
  · rw [hia, if_pos rfl, Equiv.swap_apply_left]
    ring
  · rw [if_neg hia]
    by_cases hib : i = b
    · rw [hib, if_pos rfl, Equiv.swap_apply_right]
      ring
    · rw [if_neg hib, Equiv.swap_apply_of_ne_of_ne hia hib, ← mul_assoc, hd i, one_mul]

private theorem diagAut_conj_permAut_swap_eq_of_mul_eq_one (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (hs : d a * d b = 1) :
    diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ =
      permAut (Equiv.swap a b) := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
  rw [toAdd_diagAut_conj_permAut_swap_apply d hd a b f i, permAut_apply,
    Function.comp_apply, Equiv.swap_inv]
  by_cases hia : i = a
  · rw [hia, Equiv.swap_apply_left]
    simp only [if_true, hs, one_mul]
  · by_cases hib : i = b
    · rw [hib, Equiv.swap_apply_right]
      simp only [if_true, if_neg (Ne.symm hab), hs, one_mul]
    · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
      simp only [if_neg hia, if_neg hib]

private theorem diagAut_conj_permAut_swap_eq_of_mul_eq_neg_one (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (hs : d a * d b = -1) :
    diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ =
      sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
  rw [toAdd_diagAut_conj_permAut_swap_apply d hd a b f i,
    negTrans_apply (p := p) a b hab f i]
  by_cases hia : i = a
  · rw [hia]
    simp only [if_true, hs, toAdd_inv]
    ring
  · by_cases hib : i = b
    · rw [hib]
      simp only [if_true, if_neg (Ne.symm hab), hs, toAdd_inv]
      ring
    · simp only [if_neg hia, if_neg hib]

private theorem toAdd_diagAut_conj_negTrans_apply (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b)
    (f : Fin n → Multiplicative (ZMod p)) (i : Fin n) :
    toAdd (((diagAut d hd * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) *
      (diagAut d hd)⁻¹ : MulAut (Fin n → Multiplicative (ZMod p))) f) i) =
      if i = a then -(d a * d b) * toAdd (f b)
      else if i = b then -(d a * d b) * toAdd (f a) else toAdd (f i) := by
  rw [diagAut_inv, MulAut.mul_apply, MulAut.mul_apply, diagAut_apply,
    toAdd_ofAdd]
  by_cases hia : i = a
  · rw [hia]
    simp [negTrans_apply (p := p) a b hab, toAdd_inv, diagAut_apply]
    ring_nf
  · rw [if_neg hia]
    by_cases hib : i = b
    · rw [hib]
      simp [negTrans_apply (p := p) a b hab, toAdd_inv, diagAut_apply, Ne.symm hab]
      ring_nf
    · rw [negTrans_apply (p := p) a b hab, if_neg hia, if_neg hib, diagAut_apply,
        toAdd_ofAdd, if_neg hib, ← mul_assoc, hd i, one_mul]

private theorem diagAut_conj_negTrans_eq_of_mul_eq_one (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (hs : d a * d b = 1) :
    diagAut d hd * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) *
        (diagAut d hd)⁻¹ =
      sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
  rw [toAdd_diagAut_conj_negTrans_apply d hd hab f i,
    negTrans_apply (p := p) a b hab f i]
  by_cases hia : i = a
  · rw [hia]
    simp only [if_true, hs, toAdd_inv]
    ring
  · by_cases hib : i = b
    · rw [hib]
      simp only [if_true, if_neg (Ne.symm hab), hs, toAdd_inv]
      ring
    · simp only [if_neg hia, if_neg hib]

private theorem diagAut_conj_negTrans_eq_of_mul_eq_neg_one (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) (hs : d a * d b = -1) :
    diagAut d hd * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) *
        (diagAut d hd)⁻¹ =
      permAut (Equiv.swap a b) := by
  refine MulEquiv.ext fun f => eq_of_toAdd_eq fun i => ?_
  rw [toAdd_diagAut_conj_negTrans_apply d hd hab f i, permAut_apply, Function.comp_apply,
    Equiv.swap_inv]
  by_cases hia : i = a
  · simp only [hia, Equiv.swap_apply_left, if_true, hs]
    ring
  · by_cases hib : i = b
    · simp only [hib, Equiv.swap_apply_right, if_true, if_neg (Ne.symm hab), hs]
      ring
    · simp only [Equiv.swap_apply_of_ne_of_ne hia hib, if_neg hia, if_neg hib]

private theorem exists_diagAut_signs_of_mem_closure
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ Subgroup.closure
      (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p))))) :
    ∃ (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1),
      (∀ i, d i = 1 ∨ d i = -1) ∧ u = diagAut d hd := by
  classical
  induction hu using Subgroup.closure_induction with
  | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      refine ⟨Function.update (fun _ : Fin n => (1 : ZMod p)) k (-1), fun i => ?_,
        fun i => ?_, sgnAut_eq_diagAut k _⟩
      · by_cases hi : i = k
        · subst hi
          simp
        · simp [Function.update_of_ne hi]
      · by_cases hi : i = k
        · subst hi
          simp
        · rw [Function.update_of_ne hi]
          exact Or.inl rfl
  | one =>
      refine ⟨fun _ => 1, fun _ => one_mul 1, fun _ => Or.inl rfl, diagAut_one.symm⟩
  | mul u v _ _ ihu ihv =>
      obtain ⟨d, hd, hsign, rfl⟩ := ihu
      obtain ⟨e, he, hesign, rfl⟩ := ihv
      refine ⟨fun i => d i * e i, fun i => ?_, fun i => ?_, diagAut_mul d e hd he _⟩
      · rw [mul_mul_mul_comm, hd i, he i, one_mul]
      · rcases hsign i with h | h <;> rcases hesign i with h' | h' <;>
          change d i * e i = 1 ∨ d i * e i = -1
        <;> rw [h, h'] <;> norm_num
  | inv u _ ihu =>
      obtain ⟨d, hd, hsign, rfl⟩ := ihu
      exact ⟨d, hd, hsign, diagAut_inv d hd⟩

private theorem sign_eq_one_or_neg_one_of_mul_self (hp : p.Prime) {d : Fin n → ZMod p}
    (hd : ∀ i, d i * d i = 1) (i : Fin n) : d i = 1 ∨ d i = -1 := by
  have := Fact.mk hp
  exact mul_self_eq_one_iff.mp (hd i)

private theorem sign_mul_eq_of_signs {d : Fin n → ZMod p}
    (hsign : ∀ i, d i = 1 ∨ d i = -1) (a b : Fin n) :
    d a * d b = 1 ∨ d a * d b = -1 := by
  rcases hsign a with ha | ha <;> rcases hsign b with hb | hb <;> rw [ha, hb] <;> norm_num

private theorem permAut_conj_sgnAut_coord (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (permAut σ : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut i * (permAut σ)⁻¹ =
      sgnAut (σ i) := by
  have h := IsSignedPerm.mul_sgnAut (u := permAut σ) (π := σ) (ε := fun _ => (1 : ZMod p))
    (fun f j => by simp [permAut_apply]) i
  calc permAut σ * sgnAut i * (permAut σ)⁻¹
      = sgnAut (σ i) * permAut σ * (permAut σ)⁻¹ := by rw [h]
    _ = sgnAut (σ i) := by rw [mul_assoc, mul_inv_cancel, mul_one]

private theorem diagAut_conj_permAut_swap_mem_coordProdStab (d : Fin n → ZMod p)
    (hd : ∀ i, d i * d i = 1) {a b : Fin n} (hab : a ≠ b) :
    diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ ∈ coordProdStab n p := by
  set c : ZMod p := d a * d b with hc
  have hu : ∀ f i, toAdd (((diagAut d hd * permAut (Equiv.swap a b) *
      (diagAut d hd)⁻¹ : MulAut (Fin n → Multiplicative (ZMod p))) f (Equiv.swap a b i))) =
      (if i = a ∨ i = b then c else 1) * toAdd (f i) := by
    intro f i
    rw [toAdd_diagAut_conj_permAut_swap_apply d hd a b f (Equiv.swap a b i)]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left]
      simp [Ne.symm hab, hc]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right]
        simp [hc]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib, hc]
        simp [hia, hib]
  intro f
  rw [prod_toAdd_of_signedPerm_coord hu f]
  have hcc : c * c = 1 := by
    rw [hc, mul_mul_mul_comm, hd a, hd b, one_mul]
  have hprod : ∏ i, (if i = a ∨ i = b then c else (1 : ZMod p)) = 1 := by
    rw [show (fun i => if i = a ∨ i = b then c else (1 : ZMod p)) =
        (fun i => if i ∈ ({a, b} : Finset (Fin n)) then c else 1) from by
      funext i
      simp [Finset.mem_insert, Finset.mem_singleton]]
    rw [Fintype.prod_ite_mem, Finset.prod_const, Finset.card_pair hab, pow_two, hcc]
  rw [hprod, one_mul]

private theorem card_fix_map_conj_eq (S : Subgroup (MulAut (Fin n → Multiplicative (ZMod p))))
    (δ : MulAut (Fin n → Multiplicative (ZMod p))) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ S.map (MulAut.conj δ).toMonoidHom, u f = f} =
      Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ S, u f = f} := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun f => ⟨δ⁻¹ f.1, (forall_map_conj_fix_iff S δ f.1).mp f.2⟩
      invFun := fun g => ⟨δ g.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · exact (forall_map_conj_fix_iff S δ (δ g.1)).mpr (by simpa using g.2)
  · intro f
    exact Subtype.ext (by simp)
  · intro g
    exact Subtype.ext (by simp)

private theorem card_fix_map_conj_aPermutationOn (hp : p.Prime) (I : Finset (Fin n))
    (d : Fin n → ZMod p) (hd : ∀ i, d i * d i = 1) :
    Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ (aPermutationOn n p I).map (MulAut.conj (diagAut d hd)).toMonoidHom,
          u f = f} =
      if I.Nonempty then p ^ (n - I.card + 1) else p ^ n := by
  have : Fact p.Prime := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [card_fix_map_conj_eq]
  by_cases hI : I.Nonempty
  · rw [if_pos hI, card_fix_aPermutationOn hI]
  · rw [if_neg hI]
    have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst hIempty
    have hbot : aPermutationOn n p (∅ : Finset (Fin n)) = ⊥ := by
      rw [aPermutationOn]
      convert Subgroup.closure_empty using 2
      ext r
      simp
    rw [hbot]
    have hall : ∀ f : Fin n → Multiplicative (ZMod p),
        ∀ u ∈ (⊥ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))), u f = f := by
      intro f u hu
      rw [Subgroup.mem_bot.mp hu]
      rfl
    rw [show Nat.card {f : Fin n → Multiplicative (ZMod p) //
        ∀ u ∈ (⊥ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))), u f = f} =
        Nat.card (Fin n → Multiplicative (ZMod p)) from
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)]
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_multiplicative, ZMod.card]

private theorem signedTransposition_mulSingle_apply {d e : Fin n} (hde : d ≠ e)
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u = permAut (Equiv.swap d e) ∨
      u = sgnAut d * permAut (Equiv.swap d e) * (sgnAut d)⁻¹) (x : ZMod p) :
    u (Pi.mulSingle d (ofAdd x)) = Pi.mulSingle e (ofAdd x) ∨
      u (Pi.mulSingle d (ofAdd x)) = Pi.mulSingle e (ofAdd (-x)) := by
  rcases hu with rfl | rfl
  · left
    rw [permAut_mulSingle, Equiv.swap_apply_left]
  · right
    rw [MulAut.mul_apply, MulAut.mul_apply, sgnAut_inv, sgnAut_mulSingle_self,
      ← Pi.mulSingle_inv, ← ofAdd_neg, permAut_mulSingle, Equiv.swap_apply_left,
      sgnAut_mulSingle_of_ne (Ne.symm hde)]

private theorem signedTransposition_fix_mulSingle {d e y : Fin n} (hdy : y ≠ d) (hey : y ≠ e)
    {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u = permAut (Equiv.swap d e) ∨
      u = sgnAut d * permAut (Equiv.swap d e) * (sgnAut d)⁻¹) (x : ZMod p) :
    u (Pi.mulSingle y (ofAdd x)) = Pi.mulSingle y (ofAdd x) := by
  rcases hu with rfl | rfl
  · rw [permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hdy hey]
  · rw [MulAut.mul_apply, MulAut.mul_apply, sgnAut_inv, sgnAut_mulSingle_of_ne hdy,
      permAut_mulSingle, Equiv.swap_apply_of_ne_of_ne hdy hey, sgnAut_mulSingle_of_ne hdy]

private theorem signedTransposition_mul_ne_mul (hp : p.Prime) {a b c : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {u v : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u = permAut (Equiv.swap a b) ∨
      u = sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹)
    (hv : v = permAut (Equiv.swap a c) ∨
      v = sgnAut a * permAut (Equiv.swap a c) * (sgnAut a)⁻¹) :
    u * v ≠ v * u := by
  intro hcomm
  have h1 : (1 : ZMod p) ≠ 0 := fun h => coord_zero_ne_one hp h.symm
  have hm1 : (-1 : ZMod p) ≠ 0 := fun h => h1 (by linear_combination -h)
  have huf := signedTransposition_mulSingle_apply hab hu 1
  have hvf := signedTransposition_mulSingle_apply hac hv 1
  have hleft : toAdd ((u * v) (Pi.mulSingle a (ofAdd 1)) b) = 0 := by
    rw [MulAut.mul_apply]
    rcases hvf with hv1 | hv1
    · rw [hv1, signedTransposition_fix_mulSingle (Ne.symm hac) (Ne.symm hbc) hu 1,
        toAdd_mulSingle, if_neg hbc]
    · rw [hv1, signedTransposition_fix_mulSingle (Ne.symm hac) (Ne.symm hbc) hu (-1),
        toAdd_mulSingle, if_neg hbc]
  have hright : toAdd ((v * u) (Pi.mulSingle a (ofAdd 1)) b) ≠ 0 := by
    rw [MulAut.mul_apply]
    rcases huf with hu1 | hu1
    · rw [hu1, signedTransposition_fix_mulSingle (Ne.symm hab) hbc hv 1,
        toAdd_mulSingle, if_pos rfl]
      exact h1
    · rw [hu1, signedTransposition_fix_mulSingle (Ne.symm hab) hbc hv (-1),
        toAdd_mulSingle, if_pos rfl]
      exact hm1
  have hcoord : toAdd ((u * v) (Pi.mulSingle a (ofAdd 1)) b) =
      toAdd ((v * u) (Pi.mulSingle a (ofAdd 1)) b) :=
    congrArg (fun w => toAdd (w (Pi.mulSingle a (ofAdd 1)) b)) hcomm
  rw [hleft] at hcoord
  exact hright hcoord.symm

@[expose] def HasSignedSwap (Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))) (a b : Fin n) :
    Prop :=
  permAut (Equiv.swap a b) ∈ Γ ∨ sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹ ∈ Γ

theorem IsSignedBlockOn.hasSignedSwap (hp : p.Prime) {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (hΓ : IsSignedBlockOn n p I Γ)
    {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I) (hab : a ≠ b) : HasSignedSwap Γ a b := by
  have hgen : permAut (Equiv.swap a b) ∈ aPermutationOn n p I :=
    Subgroup.subset_closure ⟨a, ha, b, hb, hab, rfl⟩
  rcases hΓ with rfl | ⟨-, rfl⟩ | ⟨d, hd, rfl⟩
  · exact Or.inl (Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, hab, rfl⟩))
  · exact Or.inl (Subgroup.subset_closure (Or.inl ⟨a, ha, b, hb, hab, rfl⟩))
  · rcases sign_mul_eq_of_signs (fun i => sign_eq_one_or_neg_one_of_mul_self hp hd i) a b with
      hs | hs
    · refine Or.inl ?_
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj (diagAut d hd)).toMonoidHom hgen
      rw [show (MulAut.conj (diagAut d hd)).toMonoidHom (permAut (Equiv.swap a b)) =
          diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ from
        MulAut.conj_apply _ _, diagAut_conj_permAut_swap_eq_of_mul_eq_one d hd hab hs] at hmem
      exact hmem
    · refine Or.inr ?_
      have hmem := Subgroup.mem_map_of_mem (MulAut.conj (diagAut d hd)).toMonoidHom hgen
      rw [show (MulAut.conj (diagAut d hd)).toMonoidHom (permAut (Equiv.swap a b)) =
          diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ from
        MulAut.conj_apply _ _, diagAut_conj_permAut_swap_eq_of_mul_eq_neg_one d hd hab hs] at hmem
      exact hmem

theorem HasSignedSwap.map_conj_of_mem_closure
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {a b : Fin n}
    (h : HasSignedSwap Γ a b) {u : MulAut (Fin n → Multiplicative (ZMod p))}
    (hu : u ∈ Subgroup.closure
      (Set.range fun k : Fin n => (sgnAut k : MulAut (Fin n → Multiplicative (ZMod p))))) :
    HasSignedSwap (Γ.map (MulAut.conj u).toMonoidHom) a b := by
  by_cases hab : a = b
  · subst hab
    have hone : (permAut (Equiv.swap a a) : MulAut (Fin n → Multiplicative (ZMod p))) = 1 := by
      refine MulEquiv.ext fun f => ?_
      rw [permAut_apply, Equiv.swap_self]
      rfl
    change permAut (Equiv.swap a a) ∈ _ ∨
      sgnAut a * permAut (Equiv.swap a a) * (sgnAut a)⁻¹ ∈ _
    rw [hone]
    exact Or.inl (Subgroup.one_mem _)
  · obtain ⟨d, hd, hsign, rfl⟩ := exists_diagAut_signs_of_mem_closure hu
    rcases h with hP | hN
    · rcases sign_mul_eq_of_signs hsign a b with hs | hs
      · refine Or.inl ?_
        have hmem := Subgroup.mem_map_of_mem (MulAut.conj (diagAut d hd)).toMonoidHom hP
        rw [show (MulAut.conj (diagAut d hd)).toMonoidHom (permAut (Equiv.swap a b)) =
            diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ from
          MulAut.conj_apply _ _, diagAut_conj_permAut_swap_eq_of_mul_eq_one d hd hab hs] at hmem
        exact hmem
      · refine Or.inr ?_
        have hmem := Subgroup.mem_map_of_mem (MulAut.conj (diagAut d hd)).toMonoidHom hP
        rw [show (MulAut.conj (diagAut d hd)).toMonoidHom (permAut (Equiv.swap a b)) =
            diagAut d hd * permAut (Equiv.swap a b) * (diagAut d hd)⁻¹ from
          MulAut.conj_apply _ _, diagAut_conj_permAut_swap_eq_of_mul_eq_neg_one d hd hab hs] at hmem
        exact hmem
    · rcases sign_mul_eq_of_signs hsign a b with hs | hs
      · refine Or.inr ?_
        have hmem := Subgroup.mem_map_of_mem (MulAut.conj (diagAut d hd)).toMonoidHom hN
        rw [show (MulAut.conj (diagAut d hd)).toMonoidHom
            (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) =
            diagAut d hd * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) *
              (diagAut d hd)⁻¹ from MulAut.conj_apply _ _,
          diagAut_conj_negTrans_eq_of_mul_eq_one d hd hab hs] at hmem
        exact hmem
      · refine Or.inl ?_
        have hmem := Subgroup.mem_map_of_mem (MulAut.conj (diagAut d hd)).toMonoidHom hN
        rw [show (MulAut.conj (diagAut d hd)).toMonoidHom
            (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) =
            diagAut d hd * (sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹) *
              (diagAut d hd)⁻¹ from MulAut.conj_apply _ _,
          diagAut_conj_negTrans_eq_of_mul_eq_neg_one d hd hab hs] at hmem
        exact hmem

theorem exists_not_commute_of_hasSignedSwap (hp : p.Prime)
    {Γ Γ' : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {a b c : Fin n} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) (h : HasSignedSwap Γ a b) (h' : HasSignedSwap Γ' a c) :
    ∃ u ∈ Γ, ∃ v ∈ Γ', u * v ≠ v * u := by
  rcases h with hP | hN
  · rcases h' with hP' | hN'
    · exact ⟨permAut (Equiv.swap a b), hP, permAut (Equiv.swap a c), hP',
        signedTransposition_mul_ne_mul hp hab hac hbc (Or.inl rfl) (Or.inl rfl)⟩
    · exact ⟨permAut (Equiv.swap a b), hP,
        sgnAut a * permAut (Equiv.swap a c) * (sgnAut a)⁻¹, hN',
        signedTransposition_mul_ne_mul hp hab hac hbc (Or.inl rfl) (Or.inr rfl)⟩
  · rcases h' with hP' | hN'
    · exact ⟨sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹, hN,
        permAut (Equiv.swap a c), hP',
        signedTransposition_mul_ne_mul hp hab hac hbc (Or.inr rfl) (Or.inl rfl)⟩
    · exact ⟨sgnAut a * permAut (Equiv.swap a b) * (sgnAut a)⁻¹, hN,
        sgnAut a * permAut (Equiv.swap a c) * (sgnAut a)⁻¹, hN',
        signedTransposition_mul_ne_mul hp hab hac hbc (Or.inr rfl) (Or.inr rfl)⟩

theorem IsSignedBlockOn.le_card_add_two (hp : p.Prime) (hp2 : p ≠ 2) {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (hΓ : IsSignedBlockOn n p I Γ)
    (hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) // ∀ u ∈ Γ, u f = f} ≤ p ^ 2) :
    n ≤ I.card + 2 := by
  rcases hΓ with rfl | ⟨hI2, rfl⟩ | ⟨d, hd, rfl⟩
  · rw [card_fix_bBlockOn hp hp2 I] at hfix
    have hle : n - I.card ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hfix
    have hcard : I.card ≤ n := by simpa using Finset.card_le_univ I
    omega
  · rw [card_fix_dBlockOn hp hp2 hI2] at hfix
    have hle : n - I.card ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hfix
    have hcard : I.card ≤ n := by simpa using Finset.card_le_univ I
    omega
  · rw [card_fix_map_conj_aPermutationOn hp I d hd] at hfix
    by_cases hI : I.Nonempty
    · rw [if_pos hI] at hfix
      have hle : n - I.card + 1 ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hfix
      have hcard : I.card ≤ n := by simpa using Finset.card_le_univ I
      omega
    · rw [if_neg hI] at hfix
      have hle : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hfix
      omega

theorem le_card_add_one_of_map_conj_aPermutationOn (hp : p.Prime) (hn : 3 ≤ n)
    {I : Finset (Fin n)} {d : Fin n → ZMod p} {hd : ∀ i, d i * d i = 1}
    (hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) //
      ∀ u ∈ (aPermutationOn n p I).map (MulAut.conj (diagAut d hd)).toMonoidHom, u f = f} ≤ p ^ 2) :
    n ≤ I.card + 1 := by
  rw [card_fix_map_conj_aPermutationOn hp I d hd] at hfix
  by_cases hI : I.Nonempty
  · rw [if_pos hI] at hfix
    have hle : n - I.card + 1 ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hfix
    have hcard : I.card ≤ n := by simpa using Finset.card_le_univ I
    omega
  · rw [if_neg hI] at hfix
    have hle : n ≤ 2 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hfix
    omega

private theorem negTrans_conj_sgnAut {i0 k : Fin n} :
    (sgnAut i0 * permAut (Equiv.swap i0 k) * (sgnAut i0)⁻¹ :
      MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut k *
      (sgnAut i0 * permAut (Equiv.swap i0 k) * (sgnAut i0)⁻¹)⁻¹ = sgnAut i0 := by
  have hs2 : (sgnAut i0 : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut i0 = 1 := by
    simpa [sq] using sgnAut_sq i0
  have hinv : (sgnAut i0 : MulAut (Fin n → Multiplicative (ZMod p)))⁻¹ = sgnAut i0 :=
    inv_eq_of_mul_eq_one_right hs2
  have hst : (sgnAut i0 : MulAut (Fin n → Multiplicative (ZMod p))) * sgnAut k =
      sgnAut k * sgnAut i0 := sgnAut_mul_comm i0 k
  have hconjP : (permAut (Equiv.swap i0 k) : MulAut (Fin n → Multiplicative (ZMod p))) *
      sgnAut k * (permAut (Equiv.swap i0 k))⁻¹ = sgnAut i0 := by
    rw [permAut_conj_sgnAut_coord (Equiv.swap i0 k) k, Equiv.swap_apply_right]
  rw [hinv]
  calc (sgnAut i0 * permAut (Equiv.swap i0 k) * sgnAut i0) * sgnAut k *
      (sgnAut i0 * permAut (Equiv.swap i0 k) * sgnAut i0)⁻¹
      = sgnAut i0 * permAut (Equiv.swap i0 k) * (sgnAut i0 * sgnAut k) * sgnAut i0 *
          (permAut (Equiv.swap i0 k))⁻¹ * sgnAut i0 := by
          rw [mul_inv_rev, mul_inv_rev, hinv]
          group
    _ = sgnAut i0 * permAut (Equiv.swap i0 k) * (sgnAut k * sgnAut i0) * sgnAut i0 *
          (permAut (Equiv.swap i0 k))⁻¹ * sgnAut i0 := by rw [hst]
    _ = sgnAut i0 * permAut (Equiv.swap i0 k) * sgnAut k * (sgnAut i0 * sgnAut i0) *
          (permAut (Equiv.swap i0 k))⁻¹ * sgnAut i0 := by group
    _ = sgnAut i0 * permAut (Equiv.swap i0 k) * sgnAut k *
          (permAut (Equiv.swap i0 k))⁻¹ * sgnAut i0 := by rw [hs2, mul_one]
    _ = sgnAut i0 * (permAut (Equiv.swap i0 k) * sgnAut k *
          (permAut (Equiv.swap i0 k))⁻¹) * sgnAut i0 := by group
    _ = sgnAut i0 * sgnAut i0 * sgnAut i0 := by rw [hconjP]
    _ = sgnAut i0 := by rw [mul_assoc, hs2, mul_one]

theorem sgnAut_mem_bCoordinateBlock_sup_of_hasSignedSwap
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {i0 k : Fin n} (hk : k ≠ i0)
    (h : HasSignedSwap Γ i0 k) : sgnAut i0 ∈ bCoordinateBlock n p i0 ⊔ Γ := by
  have hsk' : sgnAut k ∈ bCoordinateBlock n p i0 :=
    Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)
  have hsk : sgnAut k ∈ bCoordinateBlock n p i0 ⊔ Γ :=
    Subgroup.mem_sup_left (S := bCoordinateBlock n p i0) (T := Γ) hsk'
  have hconjP : (permAut (Equiv.swap i0 k) : MulAut (Fin n → Multiplicative (ZMod p))) *
      sgnAut k * (permAut (Equiv.swap i0 k))⁻¹ = sgnAut i0 := by
    rw [permAut_conj_sgnAut_coord (Equiv.swap i0 k) k, Equiv.swap_apply_right]
  rcases h with hP | hN
  · have hmem : permAut (Equiv.swap i0 k) * sgnAut k * (permAut (Equiv.swap i0 k))⁻¹ ∈
        bCoordinateBlock n p i0 ⊔ Γ :=
      Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_right (S := bCoordinateBlock n p i0) (T := Γ) hP)
          hsk)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right (S := bCoordinateBlock n p i0) (T := Γ) hP))
    rwa [hconjP] at hmem
  · have hconjN := negTrans_conj_sgnAut (p := p) (i0 := i0) (k := k)
    have hmem : (sgnAut i0 * permAut (Equiv.swap i0 k) * (sgnAut i0)⁻¹) * sgnAut k *
        (sgnAut i0 * permAut (Equiv.swap i0 k) * (sgnAut i0)⁻¹)⁻¹ ∈
        bCoordinateBlock n p i0 ⊔ Γ :=
      Subgroup.mul_mem _
        (Subgroup.mul_mem _ (Subgroup.mem_sup_right (S := bCoordinateBlock n p i0) (T := Γ) hN)
          hsk)
        (Subgroup.inv_mem _ (Subgroup.mem_sup_right (S := bCoordinateBlock n p i0) (T := Γ) hN))
    rwa [hconjN] at hmem

theorem sgnAut_mem_aPermutationFull_sup {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    {m : Fin n} (hm : sgnAut m ∈ Γ) (k : Fin n) : sgnAut k ∈ aPermutationFull n p ⊔ Γ := by
  by_cases hk : k = m
  · subst hk
    exact Subgroup.mem_sup_right hm
  · have hP : permAut (Equiv.swap m k) ∈ aPermutationFull n p :=
      Subgroup.subset_closure ⟨m, k, Ne.symm hk, rfl⟩
    have hconj : (permAut (Equiv.swap m k) : MulAut (Fin n → Multiplicative (ZMod p))) *
        sgnAut m * (permAut (Equiv.swap m k))⁻¹ = sgnAut k := by
      rw [permAut_conj_sgnAut_coord (Equiv.swap m k) m, Equiv.swap_apply_left]
    have hmem : permAut (Equiv.swap m k) * sgnAut m * (permAut (Equiv.swap m k))⁻¹ ∈
        aPermutationFull n p ⊔ Γ :=
      Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (Subgroup.mem_sup_left (S := aPermutationFull n p) (T := Γ) hP)
          (Subgroup.mem_sup_right (S := aPermutationFull n p) (T := Γ) hm))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left (S := aPermutationFull n p) (T := Γ) hP))
    rwa [hconj] at hmem

theorem IsSignedBlockOn.le_coordProdStab_or {I : Finset (Fin n)}
    {Γ : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} (hΓ : IsSignedBlockOn n p I Γ) :
    Γ ≤ coordProdStab n p ∨ (Γ = bBlockOn n p I ∧ I.Nonempty) := by
  rcases hΓ with rfl | ⟨-, rfl⟩ | ⟨d, hd, rfl⟩
  · by_cases hI : I.Nonempty
    · exact Or.inr ⟨rfl, hI⟩
    · refine Or.inl ?_
      have hempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      subst hempty
      have hbot : bBlockOn n p (∅ : Finset (Fin n)) = ⊥ := by
        rw [bBlockOn]
        convert Subgroup.closure_empty using 2
        ext r
        simp
      rw [hbot]
      exact bot_le
  · refine Or.inl ?_
    refine (Subgroup.closure_le _).mpr ?_
    rintro r (⟨a, -, b, -, -, rfl⟩ | ⟨a, -, b, -, -, rfl⟩)
    · exact fun f => prod_toAdd_permAut_coord (Equiv.swap a b) f
    · exact negTrans_mem_coordProdStab_coord a b
  · refine Or.inl ?_
    rw [aPermutationOn, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro r ⟨g, ⟨a, -, b, -, hab, rfl⟩, rfl⟩
    show MulAut.conj (diagAut d hd) (permAut (Equiv.swap a b)) ∈ coordProdStab n p
    rw [MulAut.conj_apply]
    exact diagAut_conj_permAut_swap_mem_coordProdStab d hd hab

theorem exists_bBlockOn_of_sup_eq_bSignedFull (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n)
    {ι : Type*} {ΓL : Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))} {𝒦 : Finset ι}
    {Γ : ι → Subgroup (MulAut (Fin n → Multiplicative (ZMod p)))}
    (hL : ΓL ≤ coordProdStab n p) (hΓ : ∀ k ∈ 𝒦, ∃ I : Finset (Fin n), IsSignedBlockOn n p I (Γ k))
    (hsup : ΓL ⊔ ⨆ k ∈ 𝒦, Γ k = bSignedFull n p) :
    ∃ k ∈ 𝒦, ∃ I : Finset (Fin n), I.Nonempty ∧ Γ k = bBlockOn n p I := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ k ∈ 𝒦, Γ k ≤ coordProdStab n p := by
    intro k hk
    obtain ⟨I, hI⟩ := hΓ k hk
    rcases IsSignedBlockOn.le_coordProdStab_or hI with hle | ⟨heq, hIne⟩
    · exact hle
    · exact absurd heq (hcon k hk I hIne)
  have hsup_le : bSignedFull n p ≤ coordProdStab n p := by
    rw [← hsup]
    refine sup_le hL ?_
    refine iSup_le fun k => iSup_le fun hk => hle k hk
  let i : Fin n := ⟨0, by omega⟩
  have hgen : sgnAut i ∈ bSignedFull n p :=
    Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  exact sgnAut_not_mem_coordProdStab hp hp2 i (hsup_le hgen)

end CFSG.StandardType

end
