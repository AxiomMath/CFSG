module

public import CFSG.Quasithin.EmptyFaithful.S1422LocTitsDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Ops

variable {N : ℕ}

structure VOps (N : ℕ) where
  mul : Fin N → Fin N → Fin N
  inv : Fin N → Fin N
  one : Fin N
  zI : Fin N

@[expose] def VOps.comm (O : VOps N) (i j : Fin N) : Fin N :=
  O.mul (O.mul (O.mul i j) (O.inv i)) (O.inv j)

@[expose] def wordsOf (mul : Fin N → Fin N → Fin N) (one : Fin N) (cc : Fin N → Fin N)
    (x : Fin N) : List (Fin N) :=
  (List.range 5).foldl (fun W k => W ++ W.map fun w => mul w (cc^[k] x)) [one]

@[expose] def conjWord {m : ℕ} (cj : Fin m → Fin N → Fin N) : List (Fin m) → Fin N → Fin N
  | [], i => i
  | k :: w, i => cj k (conjWord cj w i)

@[expose] def VCondsA (O : VOps N) (eB fB : Fin N → Bool) : Prop :=
  (∀ i, eB i = true ↔ ∀ j, O.comm i j = O.one ∨ O.comm i j = O.zI) ∧
  (∀ i, fB i = true ↔ ∀ e, eB e = true → O.mul i e = O.mul e i)

@[expose] def VCondsB (O : VOps N) (eB fB : Fin N → Bool) : Prop :=
  (∀ i j, eB i = true → eB j = true → eB (O.mul i j) = true) ∧
  (∀ i, eB i = true → eB (O.inv i) = true) ∧ eB O.one = true ∧
  (∀ i j, fB i = true → fB j = true → fB (O.mul i j) = true) ∧
  (∀ i, fB i = true → fB (O.inv i) = true) ∧ fB O.one = true

@[expose] def VCondsC (O : VOps N) (eB fB : Fin N → Bool) : Prop :=
  (∀ e, eB e = true → O.mul e e = O.one) ∧
  (∀ e e', eB e = true → eB e' = true → O.mul e e' = O.mul e' e) ∧
  16 * (Finset.univ.filter fun i : Fin N => fB i = true).card = N ∧
  (Finset.univ.filter fun i : Fin N => fB i = true).card ≤
    2 * (Finset.univ.filter fun i : Fin N => eB i = true).card ∧
  (∀ e, eB e = true → (∀ j, O.mul e j = O.mul j e) → e = O.one ∨ e = O.zI) ∧
  (∀ i j, fB (O.comm i j) = true)

@[expose] def VCondsD (O : VOps N) (eB : Fin N → Bool) (cc : Fin N → Fin N) : Prop :=
  ∀ i, eB i = false → (List.finRange N).all (fun z =>
    (wordsOf O.mul O.one cc i).any fun w => eB (O.mul z (O.inv w))) = true

@[expose] def VCondsE {m : ℕ} (O : VOps N) (fB : Fin N → Bool) (cc : Fin N → Fin N)
    (cj : Fin m → Fin N → Fin N) (i₀ : Fin N) (wtab : Fin N → List (Fin m)) : Prop :=
  (fB i₀ = false ∧ O.mul i₀ i₀ = O.one) ∧
  (∀ j, fB j = false → O.mul j j = O.one → conjWord cj (wtab j) i₀ = j) ∧
  (∀ i, fB i = false → fB (O.mul (cc i) (O.inv i)) = false)

@[expose] def VConds {m : ℕ} (O : VOps N) (eB fB : Fin N → Bool)
    (cc : Fin N → Fin N) (cj : Fin m → Fin N → Fin N) (i₀ : Fin N)
    (wtab : Fin N → List (Fin m)) : Prop :=
  VCondsA O eB fB ∧ VCondsB O eB fB ∧ VCondsC O eB fB ∧ VCondsD O eB cc ∧
    VCondsE O fB cc cj i₀ wtab

instance (O : VOps N) (eB fB : Fin N → Bool) : Decidable (VCondsA O eB fB) := by
  unfold VCondsA
  infer_instance

instance (O : VOps N) (eB fB : Fin N → Bool) : Decidable (VCondsB O eB fB) := by
  unfold VCondsB
  infer_instance

instance (O : VOps N) (eB fB : Fin N → Bool) : Decidable (VCondsC O eB fB) := by
  unfold VCondsC
  infer_instance

instance (O : VOps N) (eB : Fin N → Bool) (cc : Fin N → Fin N) :
    Decidable (VCondsD O eB cc) := by
  unfold VCondsD
  infer_instance

instance {m : ℕ} (O : VOps N) (fB : Fin N → Bool) (cc : Fin N → Fin N)
    (cj : Fin m → Fin N → Fin N) (i₀ : Fin N) (wtab : Fin N → List (Fin m)) :
    Decidable (VCondsE O fB cc cj i₀ wtab) := by
  unfold VCondsE
  infer_instance

instance {m : ℕ} (O : VOps N) (eB fB : Fin N → Bool)
    (cc : Fin N → Fin N) (cj : Fin m → Fin N → Fin N) (i₀ : Fin N)
    (wtab : Fin N → List (Fin m)) : Decidable (VConds O eB fB cc cj i₀ wtab) := by
  unfold VConds
  infer_instance

end Ops

section Table

variable {G : Type*} [Group G] (H L2 : Subgroup G) (N : ℕ)

structure VTable extends VOps N where
  el : Fin N → G
  el_inj : Function.Injective el
  el_range : ∀ x, x ∈ pCoreOf 2 H ↔ ∃ i, el i = x
  el_mul : ∀ i j, el (mul i j) = el i * el j
  el_inv : ∀ i, el (inv i) = (el i)⁻¹
  el_one : el one = 1
  Z_iff : ∀ x, x ∈ quasithinOmegaOneCenter (H ⊓ L2) ↔ x = 1 ∨ x = el zI

variable {H L2 N} (T : VTable H L2 N)

namespace VTable

theorem el_comm (i j : Fin N) :
    T.el (T.toVOps.comm i j) = T.el i * T.el j * (T.el i)⁻¹ * (T.el j)⁻¹ := by
  simp only [VOps.comm, T.el_mul, T.el_inv]

theorem mem_pCoreOf_el (i : Fin N) : T.el i ∈ pCoreOf 2 H := (T.el_range _).2 ⟨i, rfl⟩

theorem comm_eq_iff {i j : Fin N} (h : T.el (T.toVOps.comm i j) = 1 ∨ T.el (T.toVOps.comm i j) = T.el T.zI) :
    T.toVOps.comm i j = T.one ∨ T.toVOps.comm i j = T.zI :=
  h.imp (fun h => T.el_inj (h.trans T.el_one.symm)) fun h => T.el_inj h

end VTable

theorem conjWord_spec {m : ℕ} {g : Fin m → G} (hgH : ∀ k, g k ∈ H) {cj : Fin m → Fin N → Fin N}
    (hcj : ∀ k i, T.el (cj k i) = g k * T.el i * (g k)⁻¹) :
    ∀ (w : List (Fin m)) (i : Fin N), ∃ h ∈ H, T.el (conjWord cj w i) = h * T.el i * h⁻¹
  | [], i => ⟨1, H.one_mem, by simp [conjWord]⟩
  | k :: w, i => by
    obtain ⟨h, hh, e⟩ := conjWord_spec hgH hcj w i
    refine ⟨g k * h, H.mul_mem (hgH k) hh, ?_⟩
    simp only [conjWord, hcj, e]
    group

theorem mem_wordsOf {Q : Subgroup G} {cc : Fin N → Fin N} {i : Fin N}
    (hcc : ∀ k, T.el (cc^[k] i) ∈ Q) (hone : T.el T.one ∈ Q) :
    ∀ w ∈ wordsOf T.mul T.one cc i, T.el w ∈ Q := by
  have key : ∀ (ks : List ℕ) (W : List (Fin N)), (∀ w ∈ W, T.el w ∈ Q) →
      ∀ w ∈ ks.foldl (fun W k => W ++ W.map fun w => T.mul w (cc^[k] i)) W, T.el w ∈ Q := by
    intro ks
    induction ks with
    | nil => intro W hW; exact hW
    | cons k ks ih =>
      intro W hW
      refine ih _ ?_
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · exact hW w hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
        rw [T.el_mul]
        exact Q.mul_mem (hW v hv) (hcc k)
  exact key (List.range 5) [T.one] (by simpa using hone)

theorem titsLikeVertexFacts_of_table {m : ℕ} {eB fB : Fin N → Bool}
    {cc : Fin N → Fin N} {cj : Fin m → Fin N → Fin N} {i₀ : Fin N}
    {wtab : Fin N → List (Fin m)} (hC : VConds T.toVOps eB fB cc cj i₀ wtab)
    (c : G) (hcH : c ∈ H) (hc5 : c ^ 5 = 1) (hcc : ∀ i, T.el (cc i) = c * T.el i * c⁻¹)
    (g : Fin m → G) (hgH : ∀ k, g k ∈ H) (hcj : ∀ k i, T.el (cj k i) = g k * T.el i * (g k)⁻¹) :
    TitsLikeVertexFacts H L2 := by
  obtain ⟨⟨eB_spec, fB_spec⟩, ⟨e_mul, e_inv, e_one, f_mul, f_inv, f_one⟩,
    ⟨e_sq, e_comm, card_f, card_ef, e_central, comm_f⟩, cover,
    ⟨invol_zero, invol_trans, cc_f⟩⟩ := hC
  let E : Subgroup G :=
    { carrier := {x | ∃ i, eB i = true ∧ T.el i = x}
      mul_mem' := by
        rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
        exact ⟨T.mul i j, e_mul i j hi hj, T.el_mul i j⟩
      one_mem' := ⟨T.one, e_one, T.el_one⟩
      inv_mem' := by
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨T.inv i, e_inv i hi, T.el_inv i⟩ }
  let F : Subgroup G :=
    { carrier := {x | ∃ i, fB i = true ∧ T.el i = x}
      mul_mem' := by
        rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
        exact ⟨T.mul i j, f_mul i j hi hj, T.el_mul i j⟩
      one_mem' := ⟨T.one, f_one, T.el_one⟩
      inv_mem' := by
        rintro _ ⟨i, hi, rfl⟩
        exact ⟨T.inv i, f_inv i hi, T.el_inv i⟩ }
  have hmemE : ∀ i, T.el i ∈ E ↔ eB i = true := fun i =>
    ⟨fun ⟨j, hj, h⟩ => by rw [← T.el_inj h]; exact hj, fun h => ⟨i, h, rfl⟩⟩
  have hmemF : ∀ i, T.el i ∈ F ↔ fB i = true := fun i =>
    ⟨fun ⟨j, hj, h⟩ => by rw [← T.el_inj h]; exact hj, fun h => ⟨i, h, rfl⟩⟩
  have hc1 : ∀ x, x ∈ E ↔ x ∈ pCoreOf 2 H ∧
      ∀ y ∈ pCoreOf 2 H, x * y * x⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter (H ⊓ L2) := by
    intro x
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨T.mem_pCoreOf_el i, fun y hy => ?_⟩
      obtain ⟨j, rfl⟩ := (T.el_range _).1 hy
      rw [← T.el_comm, T.Z_iff]
      rcases (eB_spec i).1 hi j with h | h
      · left; rw [h, T.el_one]
      · right; rw [h]
    · rintro ⟨hx, hy⟩
      obtain ⟨i, rfl⟩ := (T.el_range _).1 hx
      refine ⟨i, (eB_spec i).2 fun j => ?_, rfl⟩
      have := hy (T.el j) (T.mem_pCoreOf_el j)
      rw [← T.el_comm, T.Z_iff] at this
      exact T.comm_eq_iff this
  have hcardP : Nat.card ↥(pCoreOf 2 H) = N := by
    have h := Nat.card_eq_of_bijective (α := Fin N) (β := ↥(pCoreOf 2 H))
      (fun i => ⟨T.el i, T.mem_pCoreOf_el i⟩) ⟨fun i j hij => T.el_inj (congrArg Subtype.val hij),
        fun ⟨y, hy⟩ => by
          obtain ⟨i, rfl⟩ := (T.el_range _).1 hy
          exact ⟨i, rfl⟩⟩
    rw [← h, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcardSub : ∀ (K : Subgroup G) (b : Fin N → Bool),
      (∀ x, x ∈ K ↔ ∃ i, b i = true ∧ T.el i = x) →
      Nat.card ↥K = (Finset.univ.filter fun i : Fin N => b i = true).card := by
    intro K b hK
    have h := Nat.card_eq_of_bijective (α := {i : Fin N // b i = true}) (β := ↥K)
      (fun i => ⟨T.el i.1, (hK _).2 ⟨i.1, i.2, rfl⟩⟩)
      ⟨fun i j hij => Subtype.ext (T.el_inj (congrArg Subtype.val hij)), fun ⟨y, hy⟩ => by
        obtain ⟨i, hi, rfl⟩ := (hK _).1 hy
        exact ⟨⟨i, hi⟩, rfl⟩⟩
    rw [← h, Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine ⟨E, F, hc1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨T.mem_pCoreOf_el i, fun e he => ?_⟩
      obtain ⟨j, hj, rfl⟩ := he
      rw [← T.el_mul, ← T.el_mul, (fB_spec i).1 hi j hj]
    · rintro ⟨hx, hy⟩
      obtain ⟨i, rfl⟩ := (T.el_range _).1 hx
      refine ⟨i, (fB_spec i).2 fun e he => ?_, rfl⟩
      have := hy (T.el e) ((hmemE e).2 he)
      rw [← T.el_mul, ← T.el_mul] at this
      exact T.el_inj this
  · rintro _ ⟨i, hi, rfl⟩
    rw [← T.el_mul, e_sq i hi, T.el_one]
  · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    rw [← T.el_mul, ← T.el_mul, e_comm i j hi hj]
  · rw [hcardP, hcardSub F fB fun x => Iff.rfl]
    exact card_f.symm
  · rw [hcardSub F fB fun x => Iff.rfl, hcardSub E eB fun x => Iff.rfl]
    exact card_ef
  · rintro _ ⟨i, hi, rfl⟩ hy
    have hcomm : ∀ j, T.mul i j = T.mul j i := fun j =>
      T.el_inj (by rw [T.el_mul, T.el_mul]; exact hy (T.el j) (T.mem_pCoreOf_el j))
    rw [T.Z_iff]
    rcases e_central i hi hcomm with rfl | rfl
    · exact Or.inl T.el_one
    · exact Or.inr rfl
  · intro x hx y hy
    obtain ⟨i, rfl⟩ := (T.el_range _).1 hx
    obtain ⟨j, rfl⟩ := (T.el_range _).1 hy
    exact ⟨T.toVOps.comm i j, comm_f i j, T.el_comm i j⟩
  · intro Q hEQ hQP hHQ
    by_cases hall : ∀ x ∈ Q, x ∈ E
    · exact Or.inl fun x hx _ => hall x hx
    · push Not at hall
      obtain ⟨x, hxQ, hxE⟩ := hall
      obtain ⟨i, rfl⟩ := (T.el_range _).1 (hQP hxQ)
      have hi : eB i = false := by
        by_contra h
        exact hxE ((hmemE i).2 (by simpa using h))
      have hcc_mem : ∀ y, T.el y ∈ Q → T.el (cc y) ∈ Q := fun y hy => by
        rw [hcc]
        exact (Subgroup.mem_normalizer_iff.1 (hHQ hcH) (T.el y)).1 hy
      have hiter : ∀ k, T.el (cc^[k] i) ∈ Q := by
        intro k
        induction k with
        | zero => exact hxQ
        | succ k ih => rw [Function.iterate_succ_apply']; exact hcc_mem _ ih
      have hone : T.el T.one ∈ Q := by rw [T.el_one]; exact Q.one_mem
      have hwords := mem_wordsOf T hiter hone
      have hPQ : ∀ y ∈ pCoreOf 2 H, y ∈ Q := by
        intro y hy
        obtain ⟨z, rfl⟩ := (T.el_range _).1 hy
        obtain ⟨w, hw, he⟩ := List.any_eq_true.1
          (List.all_eq_true.1 (cover i hi) z (List.mem_finRange z))
        have hz : T.el z = T.el (T.mul z (T.inv w)) * T.el w := by
          rw [T.el_mul, T.el_inv]
          group
        rw [hz]
        exact Q.mul_mem (hEQ ((hmemE _).2 he)) (hwords w hw)
      refine Or.inl fun x' hx' hcomm => (hc1 x').2 ⟨hQP hx', fun y hy => hcomm y (hPQ y hy)⟩
  · refine ⟨T.el i₀, T.mem_pCoreOf_el i₀, ?_, ?_⟩
    · rintro ⟨k, hk, hkk⟩
      have hk' := T.el_inj hkk
      rw [hk', invol_zero.1] at hk
      exact Bool.false_ne_true hk
    · rw [← T.el_mul, invol_zero.2, T.el_one]
  · intro j hjP hjF hj2 j' hj'P hj'F hj'2
    obtain ⟨a, rfl⟩ := (T.el_range _).1 hjP
    obtain ⟨b, rfl⟩ := (T.el_range _).1 hj'P
    have hfa : fB a = false := by
      by_contra h
      exact hjF ((hmemF a).2 (by simpa using h))
    have hfb : fB b = false := by
      by_contra h
      exact hj'F ((hmemF b).2 (by simpa using h))
    have ha2 : T.mul a a = T.one := T.el_inj (by rw [T.el_mul, hj2, T.el_one])
    have hb2 : T.mul b b = T.one := T.el_inj (by rw [T.el_mul, hj'2, T.el_one])
    obtain ⟨ha, haH, hae⟩ := conjWord_spec T hgH hcj (wtab a) i₀
    obtain ⟨hb, hbH, hbe⟩ := conjWord_spec T hgH hcj (wtab b) i₀
    rw [invol_trans a hfa ha2] at hae
    rw [invol_trans b hfb hb2] at hbe
    refine ⟨hb * ha⁻¹, H.mul_mem hbH (H.inv_mem haH), ?_⟩
    rw [hae, hbe]
    group
  · refine ⟨c, hcH, hc5, fun x hx hxF h => ?_⟩
    obtain ⟨i, rfl⟩ := (T.el_range _).1 hx
    have hfi : fB i = false := by
      by_contra hne
      exact hxF ((hmemF i).2 (by simpa using hne))
    have e : c * T.el i * c⁻¹ * (T.el i)⁻¹ = T.el (T.mul (cc i) (T.inv i)) := by
      rw [T.el_mul, hcc, T.el_inv]
    rw [e, hmemF] at h
    rw [cc_f i hfi] at h
    exact Bool.false_ne_true h

end Table

end CFSG.Quasithin
