module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourFieldCentralizer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

open Subgroup CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts

theorem exists_rep
    {B : Subgroup R} (hB4 : Nat.card B = 4) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBS : ¬ B ≤ S.subgroupOf R) :
    ∃ b ∈ B, IsConj b r₂R ∨ IsConj b r₃R ∨
      (IsConj b r₄R ∧ ∃ s ∈ B, (s : Equiv.Perm (Fin 42)) ∈ S ∧ s ≠ 1) := by
  classical
  obtain ⟨b, hbB, hbS⟩ := Set.not_subset.mp hBS
  have hbS' : (b : Equiv.Perm (Fin 42)) ∉ S := fun h => hbS (Subgroup.mem_subgroupOf.mpr h)
  have hb1 : b ≠ 1 := by
    intro h
    apply hbS
    rw [h]
    exact (S.subgroupOf R).one_mem
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hB2 b hbB
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbord : orderOf b = 2 := orderOf_eq_prime hb2 hb1
  rcases (orderOf_eq_two_iff b).1 hbord with hbconj | hbconj | hbconj | hbconj
  · exact absurd (mem_S_of_isConj₁ hbconj) hbS'
  · exact ⟨b, hbB, Or.inl hbconj⟩
  · exact ⟨b, hbB, Or.inr (Or.inl hbconj)⟩
  · have hcardB : Fintype.card B = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact hB4
    let bB : B := ⟨b, hbB⟩
    have hbB1 : bB ≠ 1 := by
      intro h
      exact hb1 (by simpa [bB] using congrArg (fun x : B => (x : R)) h)
    have hcardErase : (Finset.univ.erase (1 : B)).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardB]
    have hbB_mem : bB ∈ Finset.univ.erase (1 : B) := by
      rw [Finset.mem_erase]
      exact ⟨hbB1, Finset.mem_univ _⟩
    have hcardErase2 : ((Finset.univ.erase (1 : B)).erase bB).card = 2 := by
      rw [Finset.card_erase_of_mem hbB_mem, hcardErase]
    obtain ⟨b₂, hb₂u⟩ := Finset.card_pos.mp (by rw [hcardErase2]; norm_num)
    have hb₂1 : b₂ ≠ 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hb₂u)).1
    have hb₂b : b₂ ≠ bB := (Finset.mem_erase.mp hb₂u).1
    have hb₂R1 : (b₂ : R) ≠ 1 := fun h => hb₂1 (Subtype.ext (by simpa using h))
    by_cases hb₂S : (b₂ : Equiv.Perm (Fin 42)) ∈ S
    · exact ⟨b, hbB, Or.inr (Or.inr ⟨hbconj, (b₂ : R), b₂.2, hb₂S, hb₂R1⟩)⟩
    · have hb₂2 : (b₂ : R) ^ 2 = 1 := by
        rw [pow_two]; exact hB2 (b₂ : R) b₂.2
      have hb₂ord : orderOf (b₂ : R) = 2 := orderOf_eq_prime hb₂2 hb₂R1
      rcases (orderOf_eq_two_iff (b₂ : R)).1 hb₂ord with h | h | h | h
      · exact absurd (mem_S_of_isConj₁ h) hb₂S
      · exact ⟨(b₂ : R), b₂.2, Or.inl h⟩
      · exact ⟨(b₂ : R), b₂.2, Or.inr (Or.inl h)⟩
      · obtain ⟨c, hcR, hc⟩ := eq_conj_of_isConj hbconj
        obtain ⟨d, hdR, hd⟩ := eq_conj_of_isConj h
        have hr₄inv : r₄⁻¹ = r₄ := inv_eq_of_mul_eq_one_right r₄_mul_self
        have hb₂sq : (b₂ : Equiv.Perm (Fin 42)) * (b₂ : Equiv.Perm (Fin 42)) = 1 := by
          simpa using congrArg (fun x : R => (x : Equiv.Perm (Fin 42)))
            (hB2 (b₂ : R) b₂.2)
        have hb₂inv : (b₂ : Equiv.Perm (Fin 42))⁻¹ = (b₂ : Equiv.Perm (Fin 42)) :=
          inv_eq_of_mul_eq_one_right hb₂sq
        have hbr₄S : (b : Equiv.Perm (Fin 42)) * r₄ ∈ S := by
          rw [hc]
          exact CFSG.ComponentClassification.TBLit.L34FU.conj_r₄_mul_r₄_mem_S hcR
        have hb₂r₄S : (b₂ : Equiv.Perm (Fin 42)) * r₄ ∈ S := by
          rw [hd]
          exact CFSG.ComponentClassification.TBLit.L34FU.conj_r₄_mul_r₄_mem_S hdR
        have hbb₂ : ((b * (b₂ : R) : R) : Equiv.Perm (Fin 42)) =
            (b : Equiv.Perm (Fin 42)) * (b₂ : Equiv.Perm (Fin 42)) := rfl
        have hprod : ((b * (b₂ : R) : R) : Equiv.Perm (Fin 42)) =
            ((b : Equiv.Perm (Fin 42)) * r₄) *
              (((b₂ : Equiv.Perm (Fin 42)) * r₄)⁻¹) := by
          rw [hbb₂, mul_inv_rev, hr₄inv, hb₂inv]
          calc (b : Equiv.Perm (Fin 42)) * (b₂ : Equiv.Perm (Fin 42)) =
                b * (r₄ * r₄) * (b₂ : Equiv.Perm (Fin 42)) := by rw [r₄_mul_self, mul_one]
            _ = (b * r₄) * (r₄ * (b₂ : Equiv.Perm (Fin 42))) := by group
        have hprodS : ((b * (b₂ : R) : R) : Equiv.Perm (Fin 42)) ∈ S := by
          rw [hprod]
          exact S.mul_mem hbr₄S (S.inv_mem hb₂r₄S)
        have hprod_ne : (b * (b₂ : R) : R) ≠ 1 := by
          intro h
          apply hb₂b
          have h2' : (b : Equiv.Perm (Fin 42)) * (b₂ : Equiv.Perm (Fin 42)) = 1 := by
            simpa using congrArg (fun x : R => (x : Equiv.Perm (Fin 42))) h
          have hbb : (b : Equiv.Perm (Fin 42)) * (b : Equiv.Perm (Fin 42)) = 1 := by
            simpa using congrArg (fun x : R => (x : Equiv.Perm (Fin 42))) (hB2 b hbB)
          exact Subtype.ext (Subtype.ext (mul_left_cancel (h2'.trans hbb.symm)))
        exact ⟨b, hbB, Or.inr (Or.inr ⟨hbconj, b * (b₂ : R), B.mul_mem hbB b₂.2,
          hprodS, hprod_ne⟩)⟩

theorem card_centralizer_r₃_inf_R :
    Nat.card ↥(centralizer ({r₃} : Set (Equiv.Perm (Fin 42))) ⊓ R) = 240 := by
  have h := card_centralizer_mul_of_isConj (IsConj.refl r₃R) conjClass₃.2
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1008) (h.trans (by norm_num))

theorem exists_mem_C₃_of_commute_r₃ {r : Equiv.Perm (Fin 42)}
    (hr : r ∈ R) (hc : r * r₃ = r₃ * r) :
    ∃ c ∈ C₃, r = c ∨ r = c * r₂ ∨ r = c * r₃ ∨ r = c * r₄ := by
  have h23c : r₂ * r₃ = r₃ * r₂ := CFSG.ComponentClassification.TBLit.L34FU.r₂_mul_r₃
  have h24c : r₂ * r₄ = r₄ * r₂ := CFSG.ComponentClassification.TBLit.L34FU.r₂_mul_r₄
  have h34c : r₃ * r₄ = r₄ * r₃ := CFSG.ComponentClassification.TBLit.L34FU.r₃_mul_r₄
  set u : Fin 4 → Equiv.Perm (Fin 42) := ![1, r₂, r₃, r₄] with hu
  have huR : ∀ i, u i ∈ R := by
    intro i
    fin_cases i
    · exact R.one_mem
    · exact r₂_mem_R
    · exact r₃_mem_R
    · exact r₄_mem_R
  have huc : ∀ i, u i * r₃ = r₃ * u i := by
    intro i
    fin_cases i
    · show 1 * r₃ = r₃ * 1
      group
    · simpa [hu] using h23c
    · rfl
    · simpa [hu] using h34c.symm
  have h2 : r₂⁻¹ = r₂ := inv_eq_of_mul_eq_one_right r₂_mul_self
  have h3 : r₃⁻¹ = r₃ := inv_eq_of_mul_eq_one_right r₃_mul_self
  have h4 : r₄⁻¹ = r₄ := inv_eq_of_mul_eq_one_right r₄_mul_self
  have h23 : r₂ * r₃ = r₄ := rfl
  have h32 : r₃ * r₂ = r₄ := h23c.symm
  have h24 : r₂ * r₄ = r₃ := by
    show g₅ * (g₅ * g₆) = g₆
    rw [← mul_assoc, show g₅ * g₅ = 1 from r₂_mul_self, one_mul]
  have h34 : r₃ * r₄ = r₂ := by
    have hc56 : g₅ * g₆ = g₆ * g₅ := h23c
    show g₆ * (g₅ * g₆) = g₅
    rw [hc56, ← mul_assoc, show g₆ * g₆ = 1 from r₃_mul_self, one_mul]
  have h42 : r₄ * r₂ = r₃ := by rw [← h24c, h24]
  have h43 : r₄ * r₃ = r₂ := by rw [← h34c, h34]
  have hS2 : r₂ ∉ S := not_mem_S_r₂
  have hS3 : r₃ ∉ S := not_mem_S_r₃
  have hS4 : r₄ ∉ S := not_mem_S_r₄
  have hdist : ∀ i j, u i * (u j)⁻¹ ∈ S → i = j := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [hu, h2, h3, h4, h23, h32, h24, h34, h42, h43] at hij ⊢ <;>
      first | exact absurd hij hS2 | exact absurd hij hS3 | exact absurd hij hS4
  set T : Subgroup (Equiv.Perm (Fin 42)) := centralizer ({r₃} : Set (Equiv.Perm (Fin 42))) ⊓ R
    with hT
  have hmemT : ∀ (c : ↥C₃) (i : Fin 4), (c : Equiv.Perm (Fin 42)) * u i ∈ T := by
    intro c i
    have hcC := mem_inf.mp c.2
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_,
      R.mul_mem (S_le_R hcC.2) (huR i)⟩
    have hc3 := mem_centralizer_singleton_iff.mp hcC.1
    rw [mul_assoc, huc i, ← mul_assoc, hc3, mul_assoc]
  let f : ↥C₃ × Fin 4 → ↥T := fun p => ⟨(p.1 : Equiv.Perm (Fin 42)) * u p.2, hmemT p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    have h1 : (c : Equiv.Perm (Fin 42)) * u i = c' * u j := congrArg Subtype.val h
    have h2 : u i * (u j)⁻¹ ∈ S := by
      have : u i * (u j)⁻¹ = (c : Equiv.Perm (Fin 42))⁻¹ * c' := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h1, mul_inv_cancel_right]
      rw [this]
      exact S.mul_mem (S.inv_mem (mem_inf.mp c.2).2) (mem_inf.mp c'.2).2
    obtain rfl := hdist i j h2
    have h3 : c = c' := Subtype.ext (mul_right_cancel h1)
    rw [h3]
  have hcard : Nat.card ↥T ≤ Nat.card (↥C₃ × Fin 4) := by
    rw [hT, card_centralizer_r₃_inf_R, Nat.card_prod, card_C₃, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  obtain ⟨⟨c, i⟩, hci⟩ := (hf.bijective_of_nat_card_le hcard).2
    ⟨r, mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hc, hr⟩⟩
  have hr' : (c : Equiv.Perm (Fin 42)) * u i = r := congrArg Subtype.val hci
  refine ⟨c, c.2, ?_⟩
  fin_cases i
  · exact Or.inl (by rw [← hr']; exact mul_one _)
  · exact Or.inr (Or.inl hr'.symm)
  · exact Or.inr (Or.inr (Or.inl hr'.symm))
  · exact Or.inr (Or.inr (Or.inr hr'.symm))

private theorem eq_one_of_forall_mem_commute {C : Subgroup (Equiv.Perm (Fin 42))}
    [IsSimpleGroup C] (hnc : ∃ a b : C, a * b ≠ b * a)
    {c : Equiv.Perm (Fin 42)} (hc : c ∈ C) (hcomm : ∀ d ∈ C, c * d = d * c) : c = 1 := by
  have hnot : ¬ IsMulCommutative C := by
    intro h
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (isMulCommutative_iff.mp h a b)
  have hmem : (⟨c, hc⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro d
    exact Subtype.ext (hcomm d d.2).symm
  rw [TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnot] at hmem
  have h1 : (⟨c, hc⟩ : C) = 1 := Subgroup.mem_bot.mp hmem
  simpa using congrArg (fun x : C => (x : Equiv.Perm (Fin 42))) h1

private theorem commute_of_mul_commute {C : Subgroup (Equiv.Perm (Fin 42))}
    {c u : Equiv.Perm (Fin 42)}
    (hu : ∀ d ∈ C, u * d = d * u) (hcomm : ∀ d ∈ C, (c * u) * d = d * (c * u)) :
    ∀ d ∈ C, c * d = d * c := by
  intro d hd
  apply mul_right_cancel (b := u)
  calc c * d * u = c * (d * u) := by group
    _ = c * (u * d) := by rw [← hu d hd]
    _ = (c * u) * d := by group
    _ = d * (c * u) := hcomm d hd
    _ = d * c * u := by group

private theorem false_of_mul_r₄_eq_mul_of_commute
    {C : Subgroup (Equiv.Perm (Fin 42))}
    {r u c : Equiv.Perm (Fin 42)}
    (hcard : Nat.card C = 168 ∨ Nat.card C = 60) (hCS : C ≤ S) (hcS : c ∈ S)
    (h2 : (c * r₄) * (c * r₄) = 1) (hcu : c * r₄ = r * u)
    (hr : ∀ d ∈ C, r * d = d * r) (hu : ∀ d ∈ C, u * d = d * u) : False := by
  have h72 :
      Nat.card ↥(centralizer ({c * r₄} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 :=
    (card_centralizer_S_of_isConj (isConj_r₄_of_mem_S_mul_r₄ hcS h2)).trans card_C₄
  have hle : C ≤ centralizer ({c * r₄} : Set (Equiv.Perm (Fin 42))) ⊓ S := by
    intro d hd
    refine Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hCS hd⟩
    rw [hcu]
    calc d * (r * u) = (d * r) * u := by group
      _ = (r * d) * u := by rw [hr d hd]
      _ = r * (d * u) := by group
      _ = r * (u * d) := by rw [hu d hd]
      _ = (r * u) * d := by group
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h72] at hdvd
  rcases hcard with hcard | hcard <;> rw [hcard] at hdvd <;> norm_num at hdvd

theorem eq_one_or_eq_r₂
    {r : Equiv.Perm (Fin 42)} (hr : r ∈ R) (h2 : r * r = 1) (hc : r * r₂ = r₂ * r)
    (hC : ∀ c ∈ C₂, r * c = c * r) : r = 1 ∨ r = r₂ := by
  haveI : IsSimpleGroup C₂ := isSimpleGroup_C₂
  obtain ⟨c, hcC, hrc⟩ := exists_mem_C₂_of_commute_r₂ hr hc
  have hcS : c ∈ S := (Subgroup.mem_inf.mp hcC).2
  have h32 : r₃ * r₂ = r₄ := CFSG.ComponentClassification.TBLit.L34FU.r₂_mul_r₃.symm
  rcases hrc with hrc | hrc | hrc | hrc
  · left
    have hc1 : c = 1 :=
      eq_one_of_forall_mem_commute exists_mul_ne_C₂ hcC (by simpa [hrc] using hC)
    rw [hrc, hc1]
  · right
    have hc1 : c = 1 :=
      eq_one_of_forall_mem_commute exists_mul_ne_C₂ hcC <| by
        refine commute_of_mul_commute (C := C₂) (u := r₂) ?_ ?_
        · intro d hd
          exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1).symm
        · intro d hd
          simpa [hrc] using hC d hd
    rw [hrc, hc1, one_mul]
  · exfalso
    have hcr₄ : c * r₄ = r * r₂ := by rw [← h32, ← mul_assoc, hrc]
    have h2cr : (c * r₄) * (c * r₄) = 1 := by
      rw [hcr₄, ← pow_two, Commute.mul_pow ((commute_iff_eq r r₂).mpr hc) 2, pow_two r, pow_two r₂,
        h2, r₂_mul_self, mul_one]
    exact false_of_mul_r₄_eq_mul_of_commute (Or.inl card_C₂) inf_le_right hcS h2cr hcr₄
      (fun d hd => hC d hd)
      (fun d hd =>
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1).symm)
  · exfalso
    have h2' : (c * r₄) * (c * r₄) = 1 := by simpa [hrc] using h2
    exact false_of_mul_r₄_eq_mul_of_commute (Or.inl card_C₂) inf_le_right hcS h2'
      (by rw [hrc, mul_one]) (fun d hd => hC d hd) (fun _ _ => by simp)

theorem eq_one_or_eq_r₃
    {r : Equiv.Perm (Fin 42)} (hr : r ∈ R) (h2 : r * r = 1) (hc : r * r₃ = r₃ * r)
    (hC : ∀ c ∈ C₃, r * c = c * r) : r = 1 ∨ r = r₃ := by
  haveI : IsSimpleGroup C₃ := isSimpleGroup_C₃
  obtain ⟨c, hcC, hrc⟩ := exists_mem_C₃_of_commute_r₃ hr hc
  have hcS : c ∈ S := (Subgroup.mem_inf.mp hcC).2
  have h23 : r₂ * r₃ = r₄ := rfl
  rcases hrc with hrc | hrc | hrc | hrc
  · left
    have hc1 : c = 1 :=
      eq_one_of_forall_mem_commute exists_mul_ne_C₃ hcC (by simpa [hrc] using hC)
    rw [hrc, hc1]
  · exfalso
    have hcr₄ : c * r₄ = r * r₃ := by rw [hrc, mul_assoc, h23]
    have h2cr : (c * r₄) * (c * r₄) = 1 := by
      rw [hcr₄, ← pow_two, Commute.mul_pow ((commute_iff_eq r r₃).mpr hc) 2, pow_two r, pow_two r₃,
        h2, r₃_mul_self, mul_one]
    exact false_of_mul_r₄_eq_mul_of_commute (Or.inr card_C₃) inf_le_right hcS h2cr hcr₄
      (fun d hd => hC d hd)
      (fun d hd =>
        (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1).symm)
  · right
    have hc1 : c = 1 :=
      eq_one_of_forall_mem_commute exists_mul_ne_C₃ hcC <| by
        refine commute_of_mul_commute (C := C₃) (u := r₃) ?_ ?_
        · intro d hd
          exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hd).1).symm
        · intro d hd
          simpa [hrc] using hC d hd
    rw [hrc, hc1, one_mul]
  · exfalso
    have h2' : (c * r₄) * (c * r₄) = 1 := by simpa [hrc] using h2
    exact false_of_mul_r₄_eq_mul_of_commute (Or.inr card_C₃) inf_le_right hcS h2'
      (by rw [hrc, mul_one]) (fun d hd => hC d hd) (fun _ _ => by simp)

end CFSG.LocalAnalysis.WeakClosure81.Asch6.L34

end
