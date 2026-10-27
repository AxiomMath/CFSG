module

public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestPairing
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Gen

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434Cover

open Subgroup CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement

@[expose] def cubeRelations {n m : ℕ} (M : Fin m → Fin n → Fin n → ℕ) : List (Fin n → ZMod 3) :=
  (List.finRange m).flatMap fun j => (List.finRange n).map fun i =>
    (fun k => ((M j k i : ℕ) : ZMod 3)) - Pi.single i 1

theorem eq_one_of_cubeRelations {C : Type*} [CommGroup C] {n m : ℕ}
    (M : Fin m → Fin n → Fin n → ℕ) (u : Fin n → C) (hu : ∀ i, u i ^ 3 = 1)
    (hinv : ∀ j i, u i = ∏ k, u k ^ M j k i) (cs : Fin n → List (ℕ × ℕ))
    (hlin : ∀ i, Pi.single i 1 =
      ((cs i).map fun p => p.1 • (cubeRelations M).getD p.2 0).sum) (i : Fin n) : u i = 1 := by
  have hR : ∀ v ∈ cubeRelations M, powHom u hu (Multiplicative.ofAdd v) = 1 := by
    intro v hv
    simp only [cubeRelations, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hv
    obtain ⟨j, i, rfl⟩ := hv
    rw [ofAdd_sub, map_div, powHom_single, div_eq_one, powHom_natCast u hu fun k => M j k i]
    exact (hinv j i).symm
  have h := powHom_sum_getD u hu _ hR (cs i)
  rw [← hlin, powHom_single] at h
  exact h

section Lift

variable {L X : Type*} [Group L] [Group X] {π : L →* X}

theorem commute_lifts (hπ : Function.Surjective π) (hker : π.ker ≤ center L) {n m : ℕ}
    (x : Fin n → X) (hx3 : ∀ i, x i ^ 3 = 1) (hxc : ∀ i j, x i * x j = x j * x i)
    (g : Fin m → X) (M : Fin m → Fin n → Fin n → ℕ)
    (hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ M j k i).prod)
    (k₀ l₀ : Fin n) (cs : Fin n → Fin n → List (ℕ × ℕ))
    (hlin : ∀ k l, Pi.single (k, l) 1 =
      ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum) (i j : Fin n) :
    ⁅Function.surjInv hπ (x i), Function.surjInv hπ (x j)⁆ = 1 := by
  classical
  set Q : Subgroup X := closure (Set.range x) with hQdef
  have hxQ : ∀ i, x i ∈ Q := fun i => subset_closure ⟨i, rfl⟩
  have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    have : IsMulCommutative Q := isMulCommutative_closure (by
      rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
      exact hxc i j)
    intro a ha b hb
    exact congrArg Subtype.val (this.is_comm.comm (⟨a, ha⟩ : Q) ⟨b, hb⟩)
  let x' : Fin n → Q := fun i => ⟨x i, hxQ i⟩
  let _ : CommGroup π.ker := CFSG.Semidihedral.CentralTransferSplitting.centralCommGroup π.ker hker
  let u : Fin n × Fin n → π.ker := fun kl => pair hπ hQc (x' kl.1) (x' kl.2)
  have hu3 : ∀ kl, u kl ^ 3 = 1 := by
    intro kl
    have h1 : x' kl.1 ^ 3 = 1 := Subtype.ext (by simp [x', hx3])
    change pairL hπ hQc hker (x' kl.2) (x' kl.1) ^ 3 = 1
    rw [← map_pow, h1, map_one]
  have hanti : ∀ k l, u (k, l) * u (l, k) = 1 := fun k l =>
    Subtype.ext (liftComm_mul_liftComm_swap hπ (x k) (x l))
  have hcoe : ∀ e : Fin n → ℕ,
      ((List.ofFn fun k => x' k ^ e k).prod : X) = (List.ofFn fun k => x k ^ e k).prod := by
    intro e
    have h := map_list_prod Q.subtype (List.ofFn fun k => x' k ^ e k)
    rw [List.map_ofFn] at h
    exact h
  have hinv : ∀ j i i', u (i, i') = ∏ k, ∏ l, u (k, l) ^ (M j k i * M j l i') := by
    intro j i i'
    have hmem : ∀ i, g j * x i * (g j)⁻¹ ∈ Q := fun i => by
      rw [hrel, ← hcoe]
      exact SetLike.coe_mem _
    have he : ∀ i, (⟨_, hmem i⟩ : Q) = (List.ofFn fun k => x' k ^ M j k i).prod := fun i =>
      Subtype.ext (by rw [hcoe]; exact hrel j i)
    have e1 : u (i, i') = pair hπ hQc ⟨_, hmem i⟩ ⟨_, hmem i'⟩ :=
      (pair_conj hπ hQc hker (g j) (x' i) (x' i') (hmem i) (hmem i')).symm
    rw [e1, he i, he i', ← pairL_apply hπ hQc hker, map_list_prod, List.map_ofFn,
      List.prod_ofFn]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Function.comp_apply, map_pow, pairL_apply, ← pairR_apply hπ hQc hker, map_list_prod,
      List.map_ofFn, List.prod_ofFn, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Function.comp_apply, map_pow, pairR_apply, ← pow_mul, mul_comm]
  have hgen : ∀ k l, u (k, l) = u (k₀, l₀) ^ (fun _ _ => 0 : Fin n → Fin n → ℕ) k l :=
    eq_pow_of_pairingRelations M u hu3 hanti hinv k₀ l₀ (fun _ _ => 0) cs (fun k l => by
      rw [Nat.cast_zero, zero_smul]
      refine Eq.trans ?_ (hlin k l)
      ext kl
      simp)
  have h1 : u (i, j) = 1 := by
    rw [hgen i j]
    exact pow_zero _
  have h2 := congrArg Subtype.val h1
  exact h2

theorem list_prod_pow_three {Y : Type*} [Monoid Y] (l : List Y) (hl : l.Pairwise Commute) :
    l.prod ^ 3 = (l.map fun a => a ^ 3).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h := List.pairwise_cons.mp hl
    have hc : Commute a l.prod := Commute.list_prod_right _ _ h.1
    rw [List.prod_cons, List.map_cons, List.prod_cons, hc.mul_pow, ih h.2]

theorem exists_lift (hπ : Function.Surjective π) (hker : π.ker ≤ center L) {n m : ℕ}
    (x : Fin n → X) (hx3 : ∀ i, x i ^ 3 = 1) (hxc : ∀ i j, x i * x j = x j * x i)
    (g : Fin m → X) (M : Fin m → Fin n → Fin n → ℕ)
    (hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ M j k i).prod)
    (k₀ l₀ : Fin n) (cs : Fin n → Fin n → List (ℕ × ℕ))
    (hlin : ∀ k l, Pi.single (k, l) 1 =
      ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum)
    (cs' : Fin n → List (ℕ × ℕ))
    (hlin' : ∀ i, Pi.single i 1 =
      ((cs' i).map fun p => p.1 • (cubeRelations M).getD p.2 0).sum) :
    ∃ y : Fin n → L, (∀ i, π (y i) = x i) ∧ (∀ i, y i ^ 3 = 1) ∧
      ∀ i j, y i * y j = y j * y i := by
  classical
  set w : Fin n → L := fun i => Function.surjInv hπ (x i) with hw
  have hwπ : ∀ i, π (w i) = x i := fun i => Function.surjInv_eq hπ _
  have hwc : ∀ i j, w i * w j = w j * w i := fun i j =>
    commutatorElement_eq_one_iff_mul_comm.mp
      (commute_lifts hπ hker x hx3 hxc g M hrel k₀ l₀ cs hlin i j)
  have hcube_mem : ∀ i, w i ^ 3 ∈ π.ker := fun i => by
    rw [MonoidHom.mem_ker, map_pow, hwπ, hx3]
  let _ : CommGroup π.ker := CFSG.Semidihedral.CentralTransferSplitting.centralCommGroup π.ker hker
  let N : Subgroup π.ker := (powMonoidHom 3 : π.ker →* π.ker).range
  have : N.Normal := Subgroup.normal_of_isMulCommutative N
  let d : Fin n → π.ker := fun i => ⟨w i ^ 3, hcube_mem i⟩
  let u : Fin n → π.ker ⧸ N := fun i => QuotientGroup.mk (d i)
  have hu3 : ∀ i, u i ^ 3 = 1 := fun i => by
    show (QuotientGroup.mk (d i) : π.ker ⧸ N) ^ 3 = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨d i, rfl⟩
  have hcomm_list : ∀ (j : Fin m) (i : Fin n),
      (List.ofFn fun k => w k ^ M j k i).Pairwise Commute := by
    intro j i
    rw [List.pairwise_ofFn]
    intro a b _
    exact Commute.pow_pow (hwc a b) _ _
  have hrelu : ∀ j i, u i = ∏ k, u k ^ M j k i := by
    intro j i
    set ĝ : L := Function.surjInv hπ (g j) with hĝ
    have hĝπ : π ĝ = g j := Function.surjInv_eq hπ _
    set P : L := (List.ofFn fun k => w k ^ M j k i).prod with hP
    have hPπ : π P = g j * x i * (g j)⁻¹ := by
      rw [hP, map_list_prod, List.map_ofFn, hrel j i]
      rw [show (⇑π ∘ fun k => w k ^ M j k i) = fun k => x k ^ M j k i from by
        funext k
        simp [hwπ]]
    set z : L := P⁻¹ * (ĝ * w i * ĝ⁻¹) with hz
    have hzker : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hPπ, map_mul, map_mul, map_inv, hĝπ, hwπ]
      group
    have hzc : z ∈ center L := hker hzker
    have hconj : ĝ * w i * ĝ⁻¹ = P * z := by rw [hz]; group
    have hcube1 : (ĝ * w i * ĝ⁻¹) ^ 3 = w i ^ 3 := by
      rw [conj_pow]
      have := Subgroup.mem_center_iff.mp (hker (hcube_mem i)) ĝ
      calc ĝ * w i ^ 3 * ĝ⁻¹ = w i ^ 3 * ĝ * ĝ⁻¹ := by rw [this]
        _ = w i ^ 3 := by group
    have hcube2 : (P * z) ^ 3 = P ^ 3 * z ^ 3 :=
      Commute.mul_pow (Subgroup.mem_center_iff.mp hzc P) 3
    have hP3 : P ^ 3 = (List.ofFn fun k => (w k ^ 3) ^ M j k i).prod := by
      rw [hP, list_prod_pow_three _ (hcomm_list j i), List.map_ofFn]
      rw [show ((fun a : L => a ^ 3) ∘ fun k => w k ^ M j k i) =
          fun k => (w k ^ 3) ^ M j k i from by
        funext k
        simp only [Function.comp_apply]
        rw [← pow_mul, mul_comm, pow_mul]]
    have hprod : (((∏ k, d k ^ M j k i : π.ker)) : L) =
        (List.ofFn fun k => (w k ^ 3) ^ M j k i).prod := by
      have h := map_list_prod π.ker.subtype (List.ofFn fun k => d k ^ M j k i)
      rw [List.map_ofFn, List.prod_ofFn] at h
      exact h
    have hd : d i = (∏ k, d k ^ M j k i) * (⟨z, hzker⟩ : π.ker) ^ 3 := by
      refine Subtype.ext ?_
      change w i ^ 3 = _
      rw [Subgroup.coe_mul, hprod, Subgroup.coe_pow, ← hP3, ← hcube2, ← hconj, hcube1]
    show (QuotientGroup.mk (d i) : π.ker ⧸ N) = ∏ k, (QuotientGroup.mk (d k)) ^ M j k i
    rw [hd, QuotientGroup.mk_mul, QuotientGroup.mk_prod,
      QuotientGroup.mk_pow N (⟨z, hzker⟩ : π.ker) 3]
    have : (QuotientGroup.mk (⟨z, hzker⟩ : π.ker) : π.ker ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨⟨z, hzker⟩, rfl⟩
    rw [this, mul_one]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [QuotientGroup.mk_pow]
  have hu1 : ∀ i, u i = 1 := fun i => eq_one_of_cubeRelations M u hu3 hrelu cs' hlin' i
  have hcubes : ∀ i, ∃ t : π.ker, t ^ 3 = d i := fun i => by
    have h := hu1 i
    change (QuotientGroup.mk (d i) : π.ker ⧸ N) = 1 at h
    rw [QuotientGroup.eq_one_iff] at h
    obtain ⟨t, ht⟩ := h
    exact ⟨t, ht⟩
  choose t ht using hcubes
  have htc : ∀ i, ((t i : π.ker) : L) ∈ center L := fun i => hker (t i).2
  have htπ : ∀ i, π ((t i : π.ker) : L) = 1 := fun i => (t i).2
  have htcube : ∀ i, ((t i : π.ker) : L) ^ 3 = w i ^ 3 := fun i => by
    have h := congrArg Subtype.val (ht i)
    exact h
  have cen : ∀ (z g : L), z ∈ center L → Commute g z := fun z g hz =>
    Subgroup.mem_center_iff.mp hz g
  refine ⟨fun i => w i * ((t i : π.ker) : L)⁻¹, fun i => ?_, fun i => ?_, fun i j => ?_⟩
  · rw [map_mul, map_inv, htπ, hwπ, inv_one, mul_one]
  · have hc' : Commute (w i) (((t i : π.ker) : L)⁻¹) :=
      Commute.inv_right (cen _ _ (htc i))
    rw [hc'.mul_pow, inv_pow, htcube i, mul_inv_cancel]
  · have hs : ∀ i, ((t i : π.ker) : L)⁻¹ ∈ center L := fun i => Subgroup.inv_mem _ (htc i)
    show Commute (w i * ((t i : π.ker) : L)⁻¹) (w j * ((t j : π.ker) : L)⁻¹)
    exact Commute.mul_left (Commute.mul_right (hwc i j) (cen _ (w i) (hs j)))
      (Commute.mul_right (cen _ (w j) (hs i)).symm
        (cen _ (((t j : π.ker) : L)⁻¹) (hs i)).symm)

theorem exists_elemAbelian_lift [Finite L] [Finite X] (hπ : Function.Surjective π)
    (hker : π.ker ≤ center L) {n m : ℕ}
    (x : Fin n → X) (hx3 : ∀ i, x i ^ 3 = 1) (hxc : ∀ i j, x i * x j = x j * x i)
    (g : Fin m → X) (M : Fin m → Fin n → Fin n → ℕ)
    (hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ M j k i).prod)
    (k₀ l₀ : Fin n) (cs : Fin n → Fin n → List (ℕ × ℕ))
    (hlin : ∀ k l, Pi.single (k, l) 1 =
      ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum)
    (cs' : Fin n → List (ℕ × ℕ))
    (hlin' : ∀ i, Pi.single i 1 =
      ((cs' i).map fun p => p.1 • (cubeRelations M).getD p.2 0).sum)
    (hx27 : 27 ≤ Nat.card (closure (Set.range x))) {c : L} (hc : c ∈ π.ker) (hc1 : c ≠ 1)
    (hc3 : c ^ 3 = 1) :
    ∃ E : Subgroup L, CFSG.Assembly.IsElemAbelian 3 E ∧ 81 ≤ Nat.card E ∧
      ∀ y ∈ E, π y ∈ closure (Set.range x) := by
  obtain ⟨y, hyπ, hy3, hyc⟩ := exists_lift hπ hker x hx3 hxc g M hrel k₀ l₀ cs hlin cs' hlin'
  have hcen : ∀ a : L, Commute a c := fun a => Subgroup.mem_center_iff.mp (hker hc) a
  set S : Set L := Set.range y ∪ {c} with hS
  have hSc : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    rintro a (⟨i, rfl⟩ | rfl) b (⟨j, rfl⟩ | rfl)
    · exact hyc i j
    · exact hcen _
    · exact (hcen _).symm
    · exact Commute.refl _
  have hS3 : ∀ a ∈ S, a ^ 3 = 1 := by
    rintro a (⟨i, rfl⟩ | rfl)
    · exact hy3 i
    · exact hc3
  have hE := Item434SporE81.isElemAbelian_closure_of_comm hSc hS3
  have hyE : ∀ i, y i ∈ closure S := fun i => subset_closure (Or.inl ⟨i, rfl⟩)
  have hcE : c ∈ closure S := subset_closure (Or.inr rfl)
  refine ⟨closure S, hE, ?_, ?_⟩
  · let φ : closure S →* X := π.comp (closure S).subtype
    have hrange : closure (Set.range x) ≤ φ.range := by
      rw [closure_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨⟨y i, hyE i⟩, hyπ i⟩
    have hc' : (⟨c, hcE⟩ : closure S) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hc
    have h3 : 3 ∣ Nat.card φ.ker := by
      have hord : orderOf (⟨⟨c, hcE⟩, hc'⟩ : φ.ker) = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
        exact orderOf_eq_prime hc3 hc1
      rw [← hord]
      exact orderOf_dvd_natCard _
    have hker3 : 3 ≤ Nat.card φ.ker := Nat.le_of_dvd Nat.card_pos h3
    have hcard := Subgroup.card_ker_mul_card_range φ
    have hr : 27 ≤ Nat.card φ.range := hx27.trans (Subgroup.card_le_of_le hrange)
    calc 81 = 3 * 27 := by norm_num
      _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul hker3 hr
      _ = Nat.card (closure S) := hcard
  · intro a ha
    have hle : closure S ≤ (closure (Set.range x)).comap π := by
      rw [closure_le]
      rintro _ (⟨i, rfl⟩ | rfl)
      · rw [SetLike.mem_coe, mem_comap, hyπ]
        exact subset_closure ⟨i, rfl⟩
      · rw [SetLike.mem_coe, mem_comap, MonoidHom.mem_ker.mp hc]
        exact one_mem _
    exact hle ha

end Lift

end CFSG.RankThree.PartTwo.Sec4.Item434Cover
