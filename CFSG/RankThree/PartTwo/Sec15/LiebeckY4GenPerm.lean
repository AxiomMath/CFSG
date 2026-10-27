module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec15.LiebeckY4GenPermPack
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
import CFSG.RankThree.PartTwo.Sec4.Census.Item44EndSix

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4.Gen

open Equiv CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

private def PInvG {K : Type*} [Group K] (g t : K) : Prop :=
  t * t = 1 ∧ t ≠ 1 ∧ g * t * g⁻¹ ≠ t ∧ t * (g * t * g⁻¹) = (g * t * g⁻¹) * t ∧
    g * (g * t * g⁻¹) * g⁻¹ = t * (g * t * g⁻¹)

private def QNonG {K : Type*} [Group K] (g t₁ t₂ : K) : Prop :=
  t₂ * t₁ * t₂⁻¹ ≠ 1 ∧ t₂ * t₁ * t₂⁻¹ ≠ t₁ ∧ t₂ * t₁ * t₂⁻¹ ≠ g * t₁ * g⁻¹ ∧
    t₂ * t₁ * t₂⁻¹ ≠ g * (g * t₁ * g⁻¹) * g⁻¹

private instance {n : ℕ} (g t : Perm (Fin n)) : Decidable (PInvG g t) := by
  unfold PInvG; infer_instance

private instance {n : ℕ} (g t₁ t₂ : Perm (Fin n)) : Decidable (QNonG g t₁ t₂) := by
  unfold QNonG; infer_instance

private theorem pInvG_map {K K' : Type*} [Group K] [Group K'] (f : K →* K')
    (hf : Function.Injective f) {g t : K} : PInvG (f g) (f t) ↔ PInvG g t := by
  unfold PInvG
  simp only [← map_mul, ← map_inv, ← map_one f, hf.eq_iff, hf.ne_iff]

private theorem qNonG_map {K K' : Type*} [Group K] [Group K'] (f : K →* K')
    (hf : Function.Injective f) {g t₁ t₂ : K} :
    QNonG (f g) (f t₁) (f t₂) ↔ QNonG g t₁ t₂ := by
  unfold QNonG
  simp only [← map_mul, ← map_inv, ← map_one f, hf.eq_iff, hf.ne_iff]

private def cyc3 {n : ℕ} (a b c : Fin n) : Perm (Fin n) := swap a b * swap b c

private theorem witness_five : PInvG (cyc3 (0 : Fin 5) 1 2) (swap 0 1 * swap 2 3) ∧
    PInvG (cyc3 (0 : Fin 5) 1 2) (swap 0 1 * swap 2 4) ∧
    QNonG (cyc3 (0 : Fin 5) 1 2) (swap 0 1 * swap 2 3) (swap 0 1 * swap 2 4) := by
  unfold cyc3; decide +kernel

private theorem witness_six_a : PInvG (cyc3 (0 : Fin 6) 1 2) (swap 0 1 * swap 2 3) ∧
    PInvG (cyc3 (0 : Fin 6) 1 2) (swap 0 1 * swap 2 4) ∧
    QNonG (cyc3 (0 : Fin 6) 1 2) (swap 0 1 * swap 2 3) (swap 0 1 * swap 2 4) := by
  unfold cyc3; decide +kernel

private theorem witness_six_b : PInvG (cyc3 (0 : Fin 6) 1 2 * cyc3 3 4 5) (swap 0 3 * swap 1 4) ∧
    PInvG (cyc3 (0 : Fin 6) 1 2 * cyc3 3 4 5) (swap 0 4 * swap 1 5) ∧
    QNonG (cyc3 (0 : Fin 6) 1 2 * cyc3 3 4 5) (swap 0 3 * swap 1 4) (swap 0 4 * swap 1 5) := by
  unfold cyc3; decide +kernel

private theorem sign_witness : Perm.sign (swap (0 : Fin 5) 1 * swap 2 3) = 1 ∧
    Perm.sign (swap (0 : Fin 5) 1 * swap 2 4) = 1 ∧
    Perm.sign (swap (0 : Fin 6) 1 * swap 2 3) = 1 ∧ Perm.sign (swap (0 : Fin 6) 1 * swap 2 4) = 1 ∧
    Perm.sign (swap (0 : Fin 6) 3 * swap 1 4) = 1 ∧
    Perm.sign (swap (0 : Fin 6) 4 * swap 1 5) = 1 := by
  decide +kernel

private theorem conj_six : ∀ g : Perm (Fin 6), g ^ 3 = 1 → g ≠ 1 →
    ∃ c : Perm (Fin 6), c * g * c⁻¹ = cyc3 0 1 2 ∨ c * g * c⁻¹ = cyc3 0 1 2 * cyc3 3 4 5 := by
  unfold cyc3
  exact LiebeckY4Pack.conj_six_K

private theorem conj_five : ∀ g : Perm (Fin 5), g ^ 3 = 1 → g ≠ 1 →
    ∃ c : Perm (Fin 5), c * g * c⁻¹ = cyc3 0 1 2 := by
  unfold cyc3; decide +kernel

private theorem sign_conj_eq {n : ℕ} (c t : Perm (Fin n)) :
    Perm.sign (c⁻¹ * t * c) = Perm.sign t := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]

private theorem exists_pair_five (g : Perm (Fin 5)) (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    ∃ t₁ t₂ : Perm (Fin 5), Perm.sign t₁ = 1 ∧ Perm.sign t₂ = 1 ∧
      PInvG g t₁ ∧ PInvG g t₂ ∧ QNonG g t₁ t₂ := by
  obtain ⟨c, hc⟩ := conj_five g h3 h1
  obtain ⟨hw1, hw2, hw3⟩ := witness_five
  obtain ⟨hs1, hs2, -⟩ := sign_witness
  let f : Perm (Fin 5) →* Perm (Fin 5) := (MulAut.conj c).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj c).injective
  have hfg : f g = cyc3 0 1 2 := by simpa [f, MulAut.conj_apply] using hc
  have hft : ∀ t : Perm (Fin 5), f (c⁻¹ * t * c) = t := by
    intro t; simp [f, MulAut.conj_apply, mul_assoc]
  refine ⟨c⁻¹ * (swap 0 1 * swap 2 3) * c, c⁻¹ * (swap 0 1 * swap 2 4) * c,
    by rw [sign_conj_eq]; exact hs1, by rw [sign_conj_eq]; exact hs2, ?_, ?_, ?_⟩
  · rw [← pInvG_map f hf, hfg, hft]; exact hw1
  · rw [← pInvG_map f hf, hfg, hft]; exact hw2
  · rw [← qNonG_map f hf, hfg, hft, hft]; exact hw3

private theorem exists_pair_six (g : Perm (Fin 6)) (h3 : g ^ 3 = 1) (h1 : g ≠ 1) :
    ∃ t₁ t₂ : Perm (Fin 6), Perm.sign t₁ = 1 ∧ Perm.sign t₂ = 1 ∧
      PInvG g t₁ ∧ PInvG g t₂ ∧ QNonG g t₁ t₂ := by
  obtain ⟨c, hc⟩ := conj_six g h3 h1
  obtain ⟨hw1, hw2, hw3⟩ := witness_six_a
  obtain ⟨hv1, hv2, hv3⟩ := witness_six_b
  obtain ⟨-, -, hs1, hs2, hs3, hs4⟩ := sign_witness
  let f : Perm (Fin 6) →* Perm (Fin 6) := (MulAut.conj c).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj c).injective
  have hft : ∀ t : Perm (Fin 6), f (c⁻¹ * t * c) = t := by
    intro t; simp [f, MulAut.conj_apply, mul_assoc]
  rcases hc with hc | hc
  · have hfg : f g = cyc3 0 1 2 := by simpa [f, MulAut.conj_apply] using hc
    refine ⟨c⁻¹ * (swap 0 1 * swap 2 3) * c, c⁻¹ * (swap 0 1 * swap 2 4) * c,
      by rw [sign_conj_eq]; exact hs1, by rw [sign_conj_eq]; exact hs2, ?_, ?_, ?_⟩
    · rw [← pInvG_map f hf, hfg, hft]; exact hw1
    · rw [← pInvG_map f hf, hfg, hft]; exact hw2
    · rw [← qNonG_map f hf, hfg, hft, hft]; exact hw3
  · have hfg : f g = cyc3 0 1 2 * cyc3 3 4 5 := by simpa [f, MulAut.conj_apply] using hc
    refine ⟨c⁻¹ * (swap 0 3 * swap 1 4) * c, c⁻¹ * (swap 0 4 * swap 1 5) * c,
      by rw [sign_conj_eq]; exact hs3, by rw [sign_conj_eq]; exact hs4, ?_, ?_, ?_⟩
    · rw [← pInvG_map f hf, hfg, hft]; exact hv1
    · rw [← pInvG_map f hf, hfg, hft]; exact hv2
    · rw [← qNonG_map f hf, hfg, hft, hft]; exact hv3

private theorem mem_closure_pair {X : Type*} [Group X] {a b : X} (hab : a * b = b * a)
    (ha : a * a = 1) (hb : b * b = 1) {v : X} (hv : v ∈ Subgroup.closure ({a, b} : Set X)) :
    v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
  have hba : b * a = a * b := hab.symm
  have haI : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbI : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have e1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have e2 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have e3 : a * b * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have e4 : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have e5 : a * b * (a * b) = 1 := by rw [← mul_assoc, e3, hb]
  induction hv using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp [e1, e2, e3, e4, e5, ha, hb, hba]
  | inv x _ hx =>
    rcases hx with rfl | rfl | rfl | rfl <;> simp [haI, hbI, hba]

private theorem commute_of_lift {X K : Type*} [Group X] [Group K] (p : X →* K)
    (hker : ∀ y, p y = 1 → y ∈ Subgroup.center X ∧ y ^ 3 = 1) {a b : X} (ha : a * a = 1)
    (hab : p a * p b = p b * p a) : a * b = b * a := by
  set c := ⁅a, b⁆ with hc
  have hcd : c = a * b * a⁻¹ * b⁻¹ := commutatorElement_def a b
  have hpc : p c = 1 := by
    rw [hc, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab
  obtain ⟨hcZ, hc3⟩ := hker c hpc
  have haI : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have h1 : a * c * a⁻¹ = c⁻¹ := by
    rw [hcd, haI]
    calc a * (a * b * a * b⁻¹) * a = (a * a) * b * a * b⁻¹ * a := by group
      _ = b * a * b⁻¹ * a := by rw [ha, one_mul]
      _ = (a * b * a * b⁻¹)⁻¹ := by
        have : (a * b * a * b⁻¹)⁻¹ = b * a⁻¹ * b⁻¹ * a⁻¹ := by group
        rw [this, haI]
  have h2 : a * c * a⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hcZ a]; group
  have hcc : c * c = 1 := by
    have : c = c⁻¹ := h2.symm.trans h1
    calc c * c = c * c⁻¹ := by rw [← this]
      _ = 1 := mul_inv_cancel c
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hcc, inv_one, mul_one]
  exact (commutatorElement_eq_one_iff_mul_comm.mp hc1)

private theorem exists_invariant_four {X K : Type*} [Group X] [Finite X] [Group K] (p : X →* K)
    (hker : ∀ y, p y = 1 → y ∈ Subgroup.center X ∧ y ^ 3 = 1) {x : X} {P : Subgroup X}
    (hxP : x ∈ Subgroup.normalizer (P : Set X)) {t : K} (ht : PInvG (p x) t)
    (htP : t ∈ P.map p) :
    ∃ V : Subgroup X, V ≤ P ∧ (∀ v ∈ V, v * v = 1) ∧ x ∈ Subgroup.normalizer (V : Set X) ∧
      (∀ v ∈ V, v * x = x * v → v = 1) ∧
      (∀ w ∈ V, p w = 1 ∨ p w = t ∨ p w = p x * t * (p x)⁻¹ ∨
        p w = p x * (p x * t * (p x)⁻¹) * (p x)⁻¹) ∧ ∃ w ∈ V, p w = t := by
  obtain ⟨ht2, ht1, hst, hts, hr⟩ := ht
  obtain ⟨y, hyP, hyt⟩ := htP
  set a := y ^ 3 with ha_def
  have hpa : p a = t := by
    rw [ha_def, map_pow, hyt]
    calc t ^ 3 = t * t * t := by rw [pow_succ, pow_two]
      _ = t := by rw [ht2, one_mul]
  have haP : a ∈ P := pow_mem hyP 3
  have ha2 : a * a = 1 := by
    have hy2 : p (y * y) = 1 := by rw [map_mul, hyt, ht2]
    obtain ⟨-, hy3⟩ := hker _ hy2
    calc a * a = (y * y) ^ 3 := by
          rw [ha_def, ← pow_add, ← pow_two, ← pow_mul]
      _ = 1 := hy3
  set b := x * a * x⁻¹ with hb_def
  set r := x * b * x⁻¹ with hr_def
  have hconj : ∀ z ∈ P, x * z * x⁻¹ ∈ P := fun z hz => (Subgroup.mem_normalizer_iff.mp hxP z).mp hz
  have hbP : b ∈ P := hconj a haP
  have hpb : p b = p x * t * (p x)⁻¹ := by rw [hb_def, map_mul, map_mul, map_inv, hpa]
  have hpr : p r = p x * (p x * t * (p x)⁻¹) * (p x)⁻¹ := by
    rw [hr_def, map_mul, map_mul, map_inv, hpb]
  have hb2 : b * b = 1 := by
    calc b * b = x * (a * a) * x⁻¹ := by rw [hb_def]; group
      _ = 1 := by rw [ha2]; group
  have hr2 : r * r = 1 := by
    calc r * r = x * (b * b) * x⁻¹ := by rw [hr_def]; group
      _ = 1 := by rw [hb2]; group
  have hab : a * b = b * a :=
    commute_of_lift p hker ha2 (by rw [hpa, hpb]; exact hts)
  have hab2 : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]
  have hrab : r = a * b := by
    have hp : p r = p (a * b) := by rw [hpr, map_mul, hpa, hpb]; exact hr
    set z := (a * b)⁻¹ * r with hz_def
    have hz : p z = 1 := by rw [hz_def, map_mul, map_inv, hp]; exact inv_mul_cancel _
    obtain ⟨hzZ, hz3⟩ := hker z hz
    have hzc := Subgroup.mem_center_iff.mp hzZ
    have hrz : r = a * b * z := by rw [hz_def]; group
    have hzz : z * z = 1 := by
      calc z * z = (a * b * (a * b)) * (z * z) := by rw [hab2, one_mul]
        _ = (a * b * z) * (a * b * z) := by
          have : z * (a * b) = (a * b) * z := (hzc (a * b)).symm
          calc (a * b * (a * b)) * (z * z) = a * b * ((a * b) * z) * z := by group
            _ = a * b * (z * (a * b)) * z := by rw [this]
            _ = (a * b * z) * (a * b * z) := by group
        _ = r * r := by rw [← hrz]
        _ = 1 := hr2
    have hz1 : z = 1 := by
      calc z = z ^ 3 * (z * z)⁻¹ := by group
        _ = 1 := by rw [hz3, hzz, inv_one, mul_one]
    rw [hrz, hz1, mul_one]
  have hxbr : x * (a * b) * x⁻¹ = a := by
    calc x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      _ = b * r := by rw [← hb_def, ← hr_def]
      _ = b * (a * b) := by rw [hrab]
      _ = a * (b * b) := by rw [← mul_assoc, ← hab]; group
      _ = a := by rw [hb2, mul_one]
  set V := Subgroup.closure ({a, b} : Set X) with hV_def
  have hV4 : ∀ v ∈ V, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := fun v hv =>
    mem_closure_pair hab ha2 hb2 hv
  have haV : a ∈ V := Subgroup.subset_closure (Set.mem_insert a {b})
  have hbV : b ∈ V := Subgroup.subset_closure (Set.mem_insert_of_mem a rfl)
  have hVP : V ≤ P := (Subgroup.closure_le P).mpr (by
    rintro _ (rfl | rfl)
    · exact haP
    · exact hbP)
  refine ⟨V, hVP, fun v hv => ?_, ?_, fun v hv hvx => ?_, fun w hw => ?_, ⟨a, haV, hpa⟩⟩
  · rcases hV4 v hv with rfl | rfl | rfl | rfl
    · exact one_mul 1
    · exact ha2
    · exact hb2
    · exact hab2
  · refine Item148HJ.mem_normalizer_of_conj_mem fun v hv => ?_
    rcases hV4 v hv with rfl | rfl | rfl | rfl
    · simpa using V.one_mem
    · exact hbV
    · rw [← hr_def, hrab]; exact V.mul_mem haV hbV
    · rw [hxbr]; exact haV
  ·
    have hxv : x * v * x⁻¹ = v := by
      calc x * v * x⁻¹ = v * x * x⁻¹ := by rw [← hvx]
        _ = v := by group
    rcases hV4 v hv with rfl | rfl | rfl | rfl
    · rfl
    · exfalso
      apply hst
      rw [← hpb, ← hpa]
      exact congrArg p hxv
    · exfalso
      have h1 : a * b = b := hrab.symm.trans hxv
      have ha1 : a = 1 := mul_right_cancel (h1.trans (one_mul b).symm)
      exact ht1 (by rw [← hpa, ha1, map_one])
    · exfalso
      have h1 : a = a * b := hxbr.symm.trans hxv
      have hb1 : b = 1 := mul_left_cancel (h1.symm.trans (mul_one a).symm)
      apply ht1
      have : p b = 1 := by rw [hb1, map_one]
      rw [hpb] at this
      calc t = (p x)⁻¹ * (p x * t * (p x)⁻¹) * p x := by group
        _ = 1 := by rw [this]; group
  · rcases hV4 w hw with rfl | rfl | rfl | rfl
    · exact Or.inl (map_one p)
    · exact Or.inr (Or.inl hpa)
    · exact Or.inr (Or.inr (Or.inl hpb))
    · refine Or.inr (Or.inr (Or.inr ?_))
      rw [map_mul, hpa, hpb]; exact hr.symm

private theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

private theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

private theorem mem_of_mem_normalizer_six {Pb : Subgroup (Perm (Fin 6))} (hPb : Nat.card Pb = 60)
    (hPbA : Pb ≤ alternatingGroup (Fin 6)) {g : Perm (Fin 6)} (hgA : g ∈ alternatingGroup (Fin 6))
    (hg : g ∈ Subgroup.normalizer (Pb : Set (Perm (Fin 6)))) : g ∈ Pb := by
  by_contra hgP
  set K := Pb ⊔ Subgroup.zpowers g with hK
  have hKA : K ≤ alternatingGroup (Fin 6) := sup_le hPbA (Subgroup.zpowers_le.mpr hgA)
  have hgK : g ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hlt : Pb < K := lt_of_le_of_ne le_sup_left fun h => hgP (by rw [h]; exact hgK)
  have hcard : 60 < Nat.card K := hPb ▸ Subgroup.card_lt_of_lt hlt
  have hKtop : K = alternatingGroup (Fin 6) := by
    by_contra hne
    have := Item148HJ.card_le_sixty_of_lt hKA hne
    omega
  have hN : K ≤ Subgroup.normalizer (Pb : Set (Perm (Fin 6))) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hg)
  rw [hKtop] at hN
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have hn : (Pb.subgroupOf (alternatingGroup (Fin 6))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPbA).mpr hN
  have hc : Nat.card (Pb.subgroupOf (alternatingGroup (Fin 6))) = 60 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPbA).toEquiv, hPb]
  haveI := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Pb.subgroupOf (alternatingGroup (Fin 6))) with h | h
  · rw [h, Subgroup.card_bot] at hc; omega
  · rw [h, Subgroup.card_top, card_alt_six] at hc; omega

private theorem not_three_dvd_of_sq {X : Type*} [Group X] [Finite X] {V : Subgroup X}
    (h : ∀ v ∈ V, v * v = 1) : ¬ 3 ∣ Nat.card V := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := V) 3 h3
  have h2 : (v : X) * v = 1 := h v v.2
  have h3' : orderOf (v : X) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
  rw [Subgroup.orderOf_coe, hv] at h3'
  omega

private theorem exists_two_invariant {X : Type*} [Group X] [Finite X]
    (hX : Sec4.IsTripleCover X (alternatingGroup (Fin 6))) {x : X} (hx3 : x ^ 3 = 1)
    (hxZ : x ∉ Subgroup.center X) {P : Subgroup X} (hPp : Group.IsPerfect P) (hP1 : P ≠ ⊥)
    (hxP : x ∈ Subgroup.normalizer (P : Set X)) :
    ∃ V₁ V₂ : Subgroup X, V₁ ≤ P ∧ V₂ ≤ P ∧ ¬ 3 ∣ Nat.card V₁ ∧ ¬ 3 ∣ Nat.card V₂ ∧
      x ∈ Subgroup.normalizer (V₁ : Set X) ∧ x ∈ Subgroup.normalizer (V₂ : Set X) ∧
      ¬ V₂ ≤ Subgroup.normalizer (V₁ : Set X) ∧
      (∀ v ∈ V₁, v * x = x * v → v = 1) ∧ (∀ v ∈ V₂, v * x = x * v → v = 1) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ3, ⟨e⟩⟩ := hX
  set Z := Subgroup.center X with hZdef
  set p : X →* Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Z)) with hp
  have hpker : ∀ g : X, p g = 1 ↔ g ∈ Z := by
    intro g
    simp only [hp, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, OneMemClass.coe_eq_one, map_eq_one_iff _ e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hpA : ∀ g : X, p g ∈ alternatingGroup (Fin 6) := fun g => (e (QuotientGroup.mk g)).2
  have hz3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz => by
    have := Subgroup.orderOf_dvd_natCard Z hz
    rw [hZ3] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  have hker : ∀ y, p y = 1 → y ∈ Subgroup.center X ∧ y ^ 3 = 1 := fun y hy =>
    ⟨(hpker y).mp hy, hz3 y ((hpker y).mp hy)⟩
  set g := p x with hg
  have hg3 : g ^ 3 = 1 := by rw [hg, ← map_pow, hx3, map_one]
  have hg1 : g ≠ 1 := fun h => hxZ ((hpker x).mp h)
  set Pb := P.map p with hPb
  have hPbp : Group.IsPerfect Pb := Group.IsPerfect.map (H := P) p
  have hPbne : Pb ≠ ⊥ := by
    intro h
    have hPZ : P ≤ Z := fun g hg => (hpker g).mp (by
      have : p g ∈ Pb := ⟨g, hg, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this)
    apply hP1
    have hZZ : ⁅Z, Z⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.center_le_centralizer _)
    rw [← Subgroup.isPerfect_iff.mp hPp]
    exact le_bot_iff.mp (hZZ ▸ Subgroup.commutator_mono hPZ hPZ)
  have hgN : g ∈ Subgroup.normalizer (Pb : Set (Perm (Fin 6))) :=
    Subgroup.le_normalizer_map p ⟨x, hxP, rfl⟩
  obtain ⟨t₁, t₂, ht₁P, ht₂P, hP₁, hP₂, hQ⟩ : ∃ t₁ t₂ : Perm (Fin 6), t₁ ∈ Pb ∧ t₂ ∈ Pb ∧
      PInvG g t₁ ∧ PInvG g t₂ ∧ QNonG g t₁ t₂ := by
    rcases Sec4.Census.perfect_perm_six hPbp hPbne with hA6 | hA5
    · obtain ⟨t₁, t₂, hs₁, hs₂, h₁, h₂, hq⟩ := exists_pair_six g hg3 hg1
      exact ⟨t₁, t₂, hA6 ▸ Equiv.Perm.mem_alternatingGroup.mpr hs₁,
        hA6 ▸ Equiv.Perm.mem_alternatingGroup.mpr hs₂, h₁, h₂, hq⟩
    · obtain ⟨e5⟩ := hA5
      have hPbA : Pb ≤ alternatingGroup (Fin 6) := by
        rintro _ ⟨y, -, rfl⟩
        exact hpA y
      have hPb60 : Nat.card Pb = 60 := by rw [Nat.card_congr e5.toEquiv, card_alt_five]
      have hgPb : g ∈ Pb := mem_of_mem_normalizer_six hPb60 hPbA (hpA x) hgN
      set h : alternatingGroup (Fin 5) := e5 ⟨g, hgPb⟩ with hh
      have hh3 : h ^ 3 = 1 := by
        rw [hh, ← map_pow]
        have : (⟨g, hgPb⟩ : Pb) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
        rw [this, map_one]
      have hh1 : h ≠ 1 := by
        intro h1
        rw [hh, map_eq_one_iff _ e5.injective] at h1
        exact hg1 (congrArg Subtype.val h1)
      obtain ⟨t₁', t₂', hs₁, hs₂, h₁, h₂, hq⟩ := exists_pair_five (h : Perm (Fin 5))
        (by simpa using congrArg Subtype.val hh3) (fun h' => hh1 (Subtype.ext h'))
      set u₁ : alternatingGroup (Fin 5) :=
        ⟨t₁', Equiv.Perm.mem_alternatingGroup.mpr hs₁⟩ with hu₁
      set u₂ : alternatingGroup (Fin 5) :=
        ⟨t₂', Equiv.Perm.mem_alternatingGroup.mpr hs₂⟩ with hu₂
      let ι : alternatingGroup (Fin 5) →* Perm (Fin 6) := Pb.subtype.comp e5.symm.toMonoidHom
      have hι : Function.Injective ι := Pb.subtype_injective.comp e5.symm.injective
      have hιh : ι h = g := by simp [ι, hh]
      have hA5 : Function.Injective (alternatingGroup (Fin 5)).subtype :=
        Subgroup.subtype_injective _
      have h₁' : PInvG h u₁ := (pInvG_map _ hA5).mp h₁
      have h₂' : PInvG h u₂ := (pInvG_map _ hA5).mp h₂
      have hq' : QNonG h u₁ u₂ := (qNonG_map _ hA5).mp hq
      refine ⟨ι u₁, ι u₂, (e5.symm u₁).2, (e5.symm u₂).2, ?_, ?_, ?_⟩
      · rw [← hιh]; exact (pInvG_map ι hι).mpr h₁'
      · rw [← hιh]; exact (pInvG_map ι hι).mpr h₂'
      · rw [← hιh]; exact (qNonG_map ι hι).mpr hq'
  obtain ⟨V₁, hV₁P, hV₁2, hV₁N, hV₁c, hV₁p, w₁, hw₁V, hw₁p⟩ :=
    exists_invariant_four p hker hxP hP₁ ht₁P
  obtain ⟨V₂, hV₂P, hV₂2, hV₂N, hV₂c, -, w₂, hw₂V, hw₂p⟩ :=
    exists_invariant_four p hker hxP hP₂ ht₂P
  refine ⟨V₁, V₂, hV₁P, hV₂P, not_three_dvd_of_sq hV₁2, not_three_dvd_of_sq hV₂2, hV₁N, hV₂N,
    fun hle => ?_, hV₁c, hV₂c⟩
  have hmem : w₂ * w₁ * w₂⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp (hle hw₂V) w₁).mp hw₁V
  have hpm : p (w₂ * w₁ * w₂⁻¹) = t₂ * t₁ * t₂⁻¹ := by
    rw [map_mul, map_mul, map_inv, hw₁p, hw₂p]
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hQ
  rcases hV₁p _ hmem with h | h | h | h
  · exact hq1 (hpm ▸ h)
  · exact hq2 (hpm ▸ h)
  · exact hq3 (hpm ▸ h)
  · exact hq4 (hpm ▸ h)

theorem exists_two_invariant_in {H : Type*} [Group H] [Finite H] {𝔍 : Subgroup H}
    (h𝔍 : Sec4.IsTripleCover ↥𝔍 (alternatingGroup (Fin 6))) {x : H} (hx𝔍 : x ∈ 𝔍)
    (hx3 : x ^ 3 = 1) (hxZ : ∃ y ∈ 𝔍, x * y ≠ y * x) {P : Subgroup H} (hP𝔍 : P ≤ 𝔍)
    (hPp : Group.IsPerfect P) (hP1 : P ≠ ⊥) (hxP : x ∈ Subgroup.normalizer (P : Set H)) :
    ∃ V₁ V₂ : Subgroup H, V₁ ≤ P ∧ V₂ ≤ P ∧ ¬ 3 ∣ Nat.card V₁ ∧ ¬ 3 ∣ Nat.card V₂ ∧
      x ∈ Subgroup.normalizer (V₁ : Set H) ∧ x ∈ Subgroup.normalizer (V₂ : Set H) ∧
      ¬ V₂ ≤ Subgroup.normalizer (V₁ : Set H) ∧
      (∀ v ∈ V₁, v * x = x * v → v = 1) ∧ (∀ v ∈ V₂, v * x = x * v → v = 1) := by
  set x' : 𝔍 := ⟨x, hx𝔍⟩ with hx'
  have hx3' : x' ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxZ' : x' ∉ Subgroup.center ↥𝔍 := by
    intro hc
    obtain ⟨y, hy, hxy⟩ := hxZ
    exact hxy (congrArg Subtype.val (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩).symm)
  have hPp' : Group.IsPerfect (P.subgroupOf 𝔍) := by
    have := hPp
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hP𝔍).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hP𝔍).symm.surjective
  have hP1' : P.subgroupOf 𝔍 ≠ ⊥ := by
    intro h
    apply hP1
    rw [← Subgroup.map_subgroupOf_eq_of_le hP𝔍, h, Subgroup.map_bot]
  have hxP' : x' ∈ Subgroup.normalizer ((P.subgroupOf 𝔍 : Subgroup ↥𝔍) : Set ↥𝔍) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hxP y
  obtain ⟨V₁, V₂, hV₁P, hV₂P, h₁3, h₂3, hxV₁, hxV₂, hnn, hc₁, hc₂⟩ :=
    exists_two_invariant h𝔍 hx3' hxZ' hPp' hP1' hxP'
  have hmapP : ∀ V : Subgroup ↥𝔍, V ≤ P.subgroupOf 𝔍 → V.map 𝔍.subtype ≤ P := fun V hV =>
    (Subgroup.map_mono hV).trans (by rw [Subgroup.map_subgroupOf_eq_of_le hP𝔍])
  have hcard : ∀ V : Subgroup ↥𝔍, Nat.card (V.map 𝔍.subtype) = Nat.card V := fun V =>
    Subgroup.card_map_of_injective 𝔍.subtype_injective
  have hnorm : ∀ V : Subgroup ↥𝔍, x' ∈ Subgroup.normalizer (V : Set ↥𝔍) →
      x ∈ Subgroup.normalizer ((V.map 𝔍.subtype : Subgroup H) : Set H) := fun V hV =>
    Subgroup.le_normalizer_map 𝔍.subtype ⟨x', hV, rfl⟩
  have hfix : ∀ V : Subgroup ↥𝔍, (∀ v ∈ V, v * x' = x' * v → v = 1) →
      ∀ v ∈ V.map 𝔍.subtype, v * x = x * v → v = 1 := by
    rintro V hV _ ⟨v, hv, rfl⟩ hvx
    have : v = 1 := hV v hv (Subtype.ext hvx)
    rw [this]; rfl
  refine ⟨V₁.map 𝔍.subtype, V₂.map 𝔍.subtype, hmapP _ hV₁P, hmapP _ hV₂P,
    by rw [hcard]; exact h₁3, by rw [hcard]; exact h₂3, hnorm _ hxV₁, hnorm _ hxV₂, ?_,
    hfix _ hc₁, hfix _ hc₂⟩
  intro hle
  apply hnn
  intro v hv
  rw [Subgroup.mem_normalizer_iff]
  intro w
  have h := Subgroup.mem_normalizer_iff.mp (hle (Subgroup.mem_map_of_mem 𝔍.subtype hv)) (w : H)
  have hw : ∀ u : ↥𝔍, u ∈ V₁ ↔ (u : H) ∈ V₁.map 𝔍.subtype := fun u =>
    (Subgroup.mem_map_iff_mem 𝔍.subtype_injective).symm
  rw [hw w, hw (v * w * v⁻¹)]
  simpa using h

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4.Gen
