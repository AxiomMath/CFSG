module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralSylowTransfer
public import CFSG.CharacterTheory.Semidihedral.CentralTransferSplitting

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest

open Subgroup
open scoped commutatorElement

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_center_left {a b z : G} (hz : z ∈ center G) :
    ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h : ∀ g, g * z = z * g := mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_center_right {a b z : G} (hz : z ∈ center G) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h : ∀ g, g * z = z * g := mem_center_iff.mp hz
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_left_of_mem_center {a a' b : G} (h : ⁅a', b⁆ ∈ center G) :
    ⁅a * a', b⁆ = ⁅a', b⁆ * ⁅a, b⁆ := by
  have hc : ∀ g, g * ⁅a', b⁆ = ⁅a', b⁆ * g := mem_center_iff.mp h
  calc ⁅a * a', b⁆ = a * ⁅a', b⁆ * (b * a⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅a', b⁆ * a * (b * a⁻¹ * b⁻¹) := by rw [hc a]
    _ = ⁅a', b⁆ * ⁅a, b⁆ := by rw [commutatorElement_def a b]; group

theorem commutatorElement_mul_right_of_mem_center {a b b' : G} (h : ⁅a, b'⁆ ∈ center G) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * ⁅a, b'⁆ := by
  have hc : ∀ g, g * ⁅a, b'⁆ = ⁅a, b'⁆ * g := mem_center_iff.mp h
  calc ⁅a, b * b'⁆ = a * b * a⁻¹ * (⁅a, b'⁆ * b⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = a * b * a⁻¹ * (b⁻¹ * ⁅a, b'⁆) := by rw [hc b⁻¹]
    _ = ⁅a, b⁆ * ⁅a, b'⁆ := by rw [commutatorElement_def a b]; group

theorem commutatorElement_conj (g a b : G) :
    ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ := by
  simp only [commutatorElement_def]; group

end Commutators

section Pairing

variable {X S : Type*} [Group X] [Group S] {π : X →* S} (hπ : Function.Surjective π)

@[expose] noncomputable def liftComm (a b : S) : X :=
  ⁅Function.surjInv hπ a, Function.surjInv hπ b⁆

theorem commutatorElement_eq_liftComm (hker : π.ker ≤ center X) (a' b' : X) :
    ⁅a', b'⁆ = liftComm hπ (π a') (π b') := by
  have ea : π (Function.surjInv hπ (π a')) = π a' := Function.surjInv_eq hπ _
  have eb : π (Function.surjInv hπ (π b')) = π b' := Function.surjInv_eq hπ _
  have ha : (Function.surjInv hπ (π a'))⁻¹ * a' ∈ center X := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ea, inv_mul_cancel])
  have hb : (Function.surjInv hπ (π b'))⁻¹ * b' ∈ center X := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, eb, inv_mul_cancel])
  calc ⁅a', b'⁆ = ⁅Function.surjInv hπ (π a') * ((Function.surjInv hπ (π a'))⁻¹ * a'),
        Function.surjInv hπ (π b') * ((Function.surjInv hπ (π b'))⁻¹ * b')⁆ := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
    _ = liftComm hπ (π a') (π b') := by
        rw [commutatorElement_mul_center_left ha, commutatorElement_mul_center_right hb,
          liftComm]

theorem liftComm_mem_ker {a b : S} (hab : a * b = b * a) : liftComm hπ a b ∈ π.ker := by
  rw [MonoidHom.mem_ker, liftComm, map_commutatorElement, Function.surjInv_eq hπ,
    Function.surjInv_eq hπ, commutatorElement_eq_one_iff_mul_comm]
  exact hab

theorem liftComm_one_left (hker : π.ker ≤ center X) (b : S) : liftComm hπ 1 b = 1 := by
  have h := commutatorElement_eq_liftComm hπ hker 1 (Function.surjInv hπ b)
  rw [map_one, Function.surjInv_eq hπ, commutatorElement_one_left] at h
  exact h.symm

theorem liftComm_one_right (hker : π.ker ≤ center X) (a : S) : liftComm hπ a 1 = 1 := by
  have h := commutatorElement_eq_liftComm hπ hker (Function.surjInv hπ a) 1
  rw [map_one, Function.surjInv_eq hπ, commutatorElement_one_right] at h
  exact h.symm

theorem liftComm_mul_left (hker : π.ker ≤ center X) {a a' b : S} (h : a' * b = b * a') :
    liftComm hπ (a * a') b = liftComm hπ a' b * liftComm hπ a b := by
  have hm : π (Function.surjInv hπ a * Function.surjInv hπ a') = a * a' := by
    rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ]
  have h1 := commutatorElement_eq_liftComm hπ hker
    (Function.surjInv hπ a * Function.surjInv hπ a') (Function.surjInv hπ b)
  rw [hm, Function.surjInv_eq hπ] at h1
  rw [← h1, commutatorElement_mul_left_of_mem_center (hker (liftComm_mem_ker hπ h))]
  rfl

theorem liftComm_mul_right (hker : π.ker ≤ center X) {a b b' : S} (h : a * b' = b' * a) :
    liftComm hπ a (b * b') = liftComm hπ a b * liftComm hπ a b' := by
  have hm : π (Function.surjInv hπ b * Function.surjInv hπ b') = b * b' := by
    rw [map_mul, Function.surjInv_eq hπ, Function.surjInv_eq hπ]
  have h1 := commutatorElement_eq_liftComm hπ hker
    (Function.surjInv hπ a) (Function.surjInv hπ b * Function.surjInv hπ b')
  rw [hm, Function.surjInv_eq hπ] at h1
  rw [← h1, commutatorElement_mul_right_of_mem_center (hker (liftComm_mem_ker hπ h))]
  rfl

theorem liftComm_conj (hker : π.ker ≤ center X) (g : S) {a b : S} (h : a * b = b * a) :
    liftComm hπ (g * a * g⁻¹) (g * b * g⁻¹) = liftComm hπ a b := by
  have hg : π (Function.surjInv hπ g) = g := Function.surjInv_eq hπ g
  have h1 := commutatorElement_eq_liftComm hπ hker
    (Function.surjInv hπ g * Function.surjInv hπ a * (Function.surjInv hπ g)⁻¹)
    (Function.surjInv hπ g * Function.surjInv hπ b * (Function.surjInv hπ g)⁻¹)
  simp only [map_mul, map_inv, hg, Function.surjInv_eq hπ] at h1
  rw [← h1, commutatorElement_conj]
  have hc := mem_center_iff.mp (hker (liftComm_mem_ker hπ h)) (Function.surjInv hπ g)
  rw [liftComm] at hc
  rw [hc, mul_inv_cancel_right]
  rfl

theorem liftComm_mul_liftComm_swap (a b : S) :
    liftComm hπ a b * liftComm hπ b a = 1 := by
  rw [liftComm, liftComm, ← commutatorElement_inv, inv_mul_cancel]

variable {Q : Subgroup S} (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)

@[expose] noncomputable def pair (a b : Q) : π.ker :=
  ⟨liftComm hπ a b, liftComm_mem_ker hπ (hQ a a.2 b b.2)⟩

theorem coe_pair (a b : Q) : (pair hπ hQ a b : X) = liftComm hπ a b := rfl

theorem ker_mul_comm (hker : π.ker ≤ center X) (u v : π.ker) : u * v = v * u :=
  Subtype.ext (mem_center_iff.mp (hker v.2) u)

@[expose] noncomputable def pairL (hker : π.ker ≤ center X) (b : Q) : Q →* π.ker where
  toFun a := pair hπ hQ a b
  map_one' := Subtype.ext (liftComm_one_left hπ hker _)
  map_mul' a a' := by
    rw [ker_mul_comm hker (pair hπ hQ a b)]
    exact Subtype.ext (liftComm_mul_left hπ hker (hQ a' a'.2 b b.2))

@[expose] noncomputable def pairR (hker : π.ker ≤ center X) (a : Q) : Q →* π.ker where
  toFun b := pair hπ hQ a b
  map_one' := Subtype.ext (liftComm_one_right hπ hker _)
  map_mul' _ b' := Subtype.ext (liftComm_mul_right hπ hker (hQ a a.2 b' b'.2))

theorem pairL_apply (hker : π.ker ≤ center X) (a b : Q) :
    pairL hπ hQ hker b a = pair hπ hQ a b := rfl

theorem pairR_apply (hker : π.ker ≤ center X) (a b : Q) :
    pairR hπ hQ hker a b = pair hπ hQ a b := rfl

theorem pair_conj (hker : π.ker ≤ center X) (g : S) (a b : Q) (ha : g * a * g⁻¹ ∈ Q)
    (hb : g * b * g⁻¹ ∈ Q) : pair hπ hQ ⟨_, ha⟩ ⟨_, hb⟩ = pair hπ hQ a b :=
  Subtype.ext (liftComm_conj hπ hker g (hQ a a.2 b b.2))

end Pairing

section LinearAlgebra

variable {C : Type*} [CommGroup C] {ι : Type*} [Fintype ι]

@[expose] noncomputable def powHom (u : ι → C) (hu : ∀ r, u r ^ 3 = 1) :
    Multiplicative (ι → ZMod 3) →* C where
  toFun t := ∏ r, u r ^ (Multiplicative.toAdd t r).val
  map_one' := by simp
  map_mul' a b := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu r), pow_add]

theorem powHom_apply (u : ι → C) (hu : ∀ r, u r ^ 3 = 1) (t : ι → ZMod 3) :
    powHom u hu (Multiplicative.ofAdd t) = ∏ r, u r ^ (t r).val := rfl

theorem powHom_single [DecidableEq ι] (u : ι → C) (hu : ∀ r, u r ^ 3 = 1) (i : ι) :
    powHom u hu (Multiplicative.ofAdd (Pi.single i 1)) = u i := by
  rw [powHom_apply, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
  · intro r _ hr
    rw [Pi.single_eq_of_ne hr, ZMod.val_zero, pow_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem powHom_natCast (u : ι → C) (hu : ∀ r, u r ^ 3 = 1) (t : ι → ℕ) :
    powHom u hu (Multiplicative.ofAdd fun r => ((t r : ℕ) : ZMod 3)) = ∏ r, u r ^ t r := by
  rw [powHom_apply]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hu r)]

theorem powHom_sum_getD (u : ι → C) (hu : ∀ r, u r ^ 3 = 1) (R : List (ι → ZMod 3))
    (hR : ∀ v ∈ R, powHom u hu (Multiplicative.ofAdd v) = 1) :
    ∀ ps : List (ℕ × ℕ),
      powHom u hu (Multiplicative.ofAdd ((ps.map fun p => p.1 • R.getD p.2 0).sum)) = 1
  | [] => by simp
  | p :: ps => by
    rw [List.map_cons, List.sum_cons, ofAdd_add, map_mul, powHom_sum_getD u hu R hR ps,
      mul_one, ofAdd_nsmul, map_pow]
    have h : powHom u hu (Multiplicative.ofAdd (R.getD p.2 0)) = 1 := by
      rw [List.getD_eq_getElem?_getD]
      cases hv : R[p.2]? with
      | none => simp
      | some v => exact hR v (List.mem_of_getElem? hv)
    rw [h, one_pow]

end LinearAlgebra

@[expose] def pairingRelations {n m : ℕ} (M : Fin m → Fin n → Fin n → ℕ) :
    List (Fin n × Fin n → ZMod 3) :=
  ((List.finRange m).flatMap fun j => (List.finRange n).flatMap fun i =>
      (List.finRange n).map fun i' =>
        (fun kl : Fin n × Fin n => ((M j kl.1 i * M j kl.2 i' : ℕ) : ZMod 3)) -
          Pi.single (i, i') 1) ++
    ((List.finRange n).flatMap fun k => (List.finRange n).map fun l =>
      Pi.single (k, l) 1 + Pi.single (l, k) 1)

theorem eq_pow_of_pairingRelations {C : Type*} [CommGroup C] {n m : ℕ}
    (M : Fin m → Fin n → Fin n → ℕ) (u : Fin n × Fin n → C) (hu : ∀ kl, u kl ^ 3 = 1)
    (hanti : ∀ k l, u (k, l) * u (l, k) = 1)
    (hinv : ∀ j i i', u (i, i') = ∏ k, ∏ l, u (k, l) ^ (M j k i * M j l i'))
    (k₀ l₀ : Fin n) (c : Fin n → Fin n → ℕ) (cs : Fin n → Fin n → List (ℕ × ℕ))
    (hlin : ∀ k l, Pi.single (k, l) 1 - ((c k l : ℕ) : ZMod 3) • Pi.single (k₀, l₀) 1 =
      ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum)
    (k l : Fin n) : u (k, l) = u (k₀, l₀) ^ c k l := by
  have hR : ∀ v ∈ pairingRelations M, powHom u hu (Multiplicative.ofAdd v) = 1 := by
    intro v hv
    simp only [pairingRelations, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_finRange, true_and] at hv
    rcases hv with ⟨j, i, i', rfl⟩ | ⟨k, l, rfl⟩
    · rw [ofAdd_sub, map_div, powHom_single, div_eq_one,
        powHom_natCast u hu fun kl => M j kl.1 i * M j kl.2 i', Fintype.prod_prod_type]
      exact (hinv j i i').symm
    · rw [ofAdd_add, map_mul, powHom_single, powHom_single]
      exact hanti k l
  have h := powHom_sum_getD u hu _ hR (cs k l)
  rw [← hlin, ofAdd_sub, map_div, powHom_single, Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow,
    powHom_single, div_eq_one] at h
  exact h

theorem card_ker_le_three_of_pairing {X S : Type*} [Group X] [Group S] [Finite X]
    [Group.IsPerfect X] {π : X →* S} (hπ : Function.Surjective π) (hker : π.ker ≤ center X)
    (hp : IsPGroup 3 π.ker) {n m : ℕ} (x : Fin n → S) (hx3 : ∀ i, x i ^ 3 = 1)
    (hxc : ∀ i j, x i * x j = x j * x i) (hQp : IsPGroup 3 (closure (Set.range x)))
    (hQi : ¬ 3 ∣ (closure (Set.range x)).index) (g : Fin m → S)
    (M : Fin m → Fin n → Fin n → ℕ)
    (hrel : ∀ j i, g j * x i * (g j)⁻¹ = (List.ofFn fun k => x k ^ M j k i).prod)
    (k₀ l₀ : Fin n) (c : Fin n → Fin n → ℕ) (cs : Fin n → Fin n → List (ℕ × ℕ))
    (hlin : ∀ k l, Pi.single (k, l) 1 - ((c k l : ℕ) : ZMod 3) • Pi.single (k₀, l₀) 1 =
      ((cs k l).map fun p => p.1 • (pairingRelations M).getD p.2 0).sum) :
    Nat.card π.ker ≤ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Q : Subgroup S := closure (Set.range x) with hQdef
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
      ((List.ofFn fun k => x' k ^ e k).prod : S) = (List.ofFn fun k => x k ^ e k).prod := by
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
  have hgen : ∀ k l, u (k, l) = u (k₀, l₀) ^ c k l :=
    eq_pow_of_pairingRelations M u hu3 hanti hinv k₀ l₀ c cs hlin
  set H : Subgroup π.ker := zpowers (u (k₀, l₀)) with hH
  have htop : closure (Set.range x') = ⊤ := by
    have h := closure_closure_coe_preimage (k := Set.range x)
    convert h using 2
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, Subtype.ext hi⟩
  have hallL : ∀ (a : Q) (l : Fin n), pair hπ hQc a (x' l) ∈ H := by
    intro a l
    have hle : closure (Set.range x') ≤ H.comap (pairL hπ hQc hker (x' l)) := by
      rw [closure_le]
      rintro _ ⟨k, rfl⟩
      change u (k, l) ∈ H
      rw [hgen k l]
      exact pow_mem (mem_zpowers _) _
    rw [htop] at hle
    exact hle (mem_top a)
  have hall : ∀ a b : Q, pair hπ hQc a b ∈ H := by
    intro a b
    have hle : closure (Set.range x') ≤ H.comap (pairR hπ hQc hker a) := by
      rw [closure_le]
      rintro _ ⟨l, rfl⟩
      exact hallL a l
    rw [htop] at hle
    exact hle (mem_top b)
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hπ 3 (hQp.toSylow hQi)
  have hPQ : (P : Subgroup X).map π = Q := by
    rw [← Sylow.coe_mapSurjective hπ P, hP, IsPGroup.toSylow_coe]
  have hle : π.ker ≤ zpowers ((u (k₀, l₀) : π.ker) : X) := by
    refine (CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived P π.ker hker hp).trans ?_
    rw [map_le_iff_le_comap, _root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_comap, map_commutatorElement, coe_subtype]
    have ha : π a ∈ Q := hPQ ▸ mem_map_of_mem π a.2
    have hb : π b ∈ Q := hPQ ▸ mem_map_of_mem π b.2
    rw [commutatorElement_eq_liftComm hπ hker, ← coe_pair hπ hQc (Q := Q) ⟨π a, ha⟩ ⟨π b, hb⟩]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hall ⟨π a, ha⟩ ⟨π b, hb⟩)
    exact mem_zpowers_iff.mpr ⟨k, by rw [← hk]; rfl⟩
  have hpow : ((u (k₀, l₀) : π.ker) : X) ^ 3 = 1 := by
    rw [← coe_pow, hu3]
    rfl
  calc Nat.card π.ker ≤ Nat.card (zpowers ((u (k₀, l₀) : π.ker) : X)) :=
        Subgroup.card_le_of_le hle
    _ = orderOf ((u (k₀, l₀) : π.ker) : X) := Nat.card_zpowers _
    _ ≤ 3 := orderOf_le_of_pow_eq_one (by norm_num) hpow

end CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
