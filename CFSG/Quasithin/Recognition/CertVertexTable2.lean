module

public import CFSG.Quasithin.Recognition.CertVertexTable

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Ops2

variable {N : ℕ}

@[expose] def VCondsD2 (O : VOps N) (eB fB rB : Fin N → Bool) (cc : Fin N → Fin N) : Prop :=
  (∀ i, fB i = false → (List.finRange N).all (fun z => !rB z ||
    (wordsOf O.mul O.one cc i).any fun w => eB (O.mul z (O.inv w))) = true) ∧
  (∀ x, fB x = true → O.mul x x = O.one → eB x = true) ∧
  (∀ x, eB x = false → (List.finRange N).all (fun r => !rB r ||
    (O.comm x r == O.one || O.comm x r == O.zI)) = false)

@[expose] def VConds2 {m : ℕ} (O : VOps N) (eB fB rB : Fin N → Bool)
    (cc : Fin N → Fin N) (cj : Fin m → Fin N → Fin N) (i₀ : Fin N)
    (wtab : Fin N → List (Fin m)) : Prop :=
  VCondsA O eB fB ∧ VCondsB O eB fB ∧ VCondsC O eB fB ∧ VCondsD2 O eB fB rB cc ∧
    VCondsE O fB cc cj i₀ wtab

instance (O : VOps N) (eB fB rB : Fin N → Bool) (cc : Fin N → Fin N) :
    Decidable (VCondsD2 O eB fB rB cc) := by
  unfold VCondsD2
  infer_instance

instance {m : ℕ} (O : VOps N) (eB fB rB : Fin N → Bool)
    (cc : Fin N → Fin N) (cj : Fin m → Fin N → Fin N) (i₀ : Fin N)
    (wtab : Fin N → List (Fin m)) : Decidable (VConds2 O eB fB rB cc cj i₀ wtab) := by
  unfold VConds2
  infer_instance

end Ops2

section Table2

variable {G : Type*} [Group G] {H L2 : Subgroup G} {N : ℕ} (T : VTable H L2 N)

theorem titsLikeVertexFacts_of_table2 {m : ℕ} {eB fB rB : Fin N → Bool}
    {cc : Fin N → Fin N} {cj : Fin m → Fin N → Fin N} {i₀ : Fin N}
    {wtab : Fin N → List (Fin m)} (hC : VConds2 T.toVOps eB fB rB cc cj i₀ wtab)
    (c : G) (hcH : c ∈ H) (hc5 : c ^ 5 = 1) (hcc : ∀ i, T.el (cc i) = c * T.el i * c⁻¹)
    (g : Fin m → G) (hgH : ∀ k, g k ∈ H) (hcj : ∀ k i, T.el (cj k i) = g k * T.el i * (g k)⁻¹) :
    TitsLikeVertexFacts H L2 := by
  obtain ⟨⟨eB_spec, fB_spec⟩, ⟨e_mul, e_inv, e_one, f_mul, f_inv, f_one⟩,
    ⟨e_sq, e_comm, card_f, card_ef, e_central, comm_f⟩, ⟨cover, invF, rfirst⟩,
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
    by_cases hQF : ∀ x ∈ Q, x ∈ F
    · refine Or.inr fun x hxQ hx2 => ?_
      obtain ⟨i, hi, rfl⟩ := hQF x hxQ
      have h2 : T.mul i i = T.one := T.el_inj (by rw [T.el_mul, hx2, T.el_one])
      exact (hmemE i).2 (invF i hi h2)
    · push Not at hQF
      obtain ⟨x, hxQ, hxF⟩ := hQF
      obtain ⟨i, rfl⟩ := (T.el_range _).1 (hQP hxQ)
      have hfi : fB i = false := by
        by_contra h
        exact hxF ((hmemF i).2 (by simpa using h))
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
      have hRQ : ∀ z, rB z = true → T.el z ∈ Q := by
        intro z hz
        obtain ⟨w, hw, he⟩ := List.any_eq_true.1 (by
          have := List.all_eq_true.1 (cover i hfi) z (List.mem_finRange z)
          simpa [hz] using this)
        have hz' : T.el z = T.el (T.mul z (T.inv w)) * T.el w := by
          rw [T.el_mul, T.el_inv]
          group
        rw [hz']
        exact Q.mul_mem (hEQ ((hmemE _).2 he)) (hwords w hw)
      refine Or.inl fun x' hx' hcomm => ?_
      obtain ⟨i', rfl⟩ := (T.el_range _).1 (hQP hx')
      by_contra hne
      have hei : eB i' = false := by
        by_contra h
        exact hne ((hmemE i').2 (by simpa using h))
      have hall := rfirst i' hei
      have hall' : (List.finRange N).all (fun r => !rB r ||
          (T.toVOps.comm i' r == T.one || T.toVOps.comm i' r == T.zI)) = true := by
        refine List.all_eq_true.2 fun r _ => ?_
        by_cases hr : rB r = true
        · have h1 := hcomm (T.el r) (hRQ r hr)
          rw [← T.el_comm, T.Z_iff] at h1
          have h2 := T.comm_eq_iff h1
          simp [hr, h2]
        · simp [hr]
      rw [hall'] at hall
      exact Bool.noConfusion hall
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


end Table2

end CFSG.Quasithin
