module

public import CFSG.Quasithin.Background.FLcR2Grp

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

variable {G : Type} [Group G]

theorem inf_le_pCoreOf [Finite G] {E Y P : Subgroup G} (hE : IsPGroup 2 ↥E)
    (hEn : P ≤ Subgroup.normalizer (E : Set G)) (hYn : P ≤ Subgroup.normalizer (Y : Set G))
    (hYP : Y ≤ P) : E ⊓ Y ≤ pCoreOf 2 Y := by
  refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_ (hE.to_le inf_le_left)
  intro y hy
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hEn (hYP hy), hYn (hYP hy)⟩

namespace P0Setup

variable {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G} (D : P0Setup L S UL n W)

@[expose] def Ebk [Finite G] {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n} (hP : P.val + 1 = i)
    (hQ : Q.val = i) : Subgroup G where
  carrier := {x | x ∈ parab (L ⊔ S) n W i ∧ ∃ l : ↥L, Dec L S UL x l ∧ blk P Q (D.α l) = 1}
  one_mem' := by
    have hne : P ≠ Q := fun h => by rw [h] at hP; omega
    exact ⟨(parab (L ⊔ S) n W i).one_mem, 1, ⟨1, (Kc L S UL).one_mem, by simp⟩, by
      rw [map_one]; exact blk_one hne⟩
  mul_mem' := by
    rintro x₁ x₂ ⟨hx₁, l₁, hd₁, hb₁⟩ ⟨hx₂, l₂, hd₂, hb₂⟩
    refine ⟨(parab (L ⊔ S) n W i).mul_mem hx₁ hx₂, l₁ * l₂, D.dec_mul hd₁ hd₂, ?_⟩
    rw [map_mul, blk_mul_Qn hi hin hP hQ (D.alpha_mem_Qn hx₁ hd₁) (D.alpha_mem_Qn hx₂ hd₂),
      hb₁, hb₂, one_mul]
  inv_mem' := by
    have hne : P ≠ Q := fun h => by rw [h] at hP; omega
    rintro x ⟨hx, l, hd, hb⟩
    refine ⟨(parab (L ⊔ S) n W i).inv_mem hx, l⁻¹, D.dec_inv hd, ?_⟩
    have hα := D.alpha_mem_Qn hx hd
    have h1 : blk P Q (D.α l⁻¹ * D.α l) = 1 := by
      rw [← map_mul, inv_mul_cancel, map_one]
      exact blk_one hne
    rw [map_inv] at h1 ⊢
    rw [blk_mul_Qn hi hin hP hQ ((Qn n i).inv_mem hα) hα, hb, mul_one] at h1
    exact h1

variable [Finite G]

theorem Ebk_normal {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n} (hP : P.val + 1 = i)
    (hQ : Q.val = i) :
    parab (L ⊔ S) n W i ≤ Subgroup.normalizer ((D.Ebk hi hin hP hQ : Subgroup G) : Set G) := by
  have hne : P ≠ Q := fun h => by rw [h] at hP; omega
  refine le_normalizer_of_conj_mem fun p hp e he => ?_
  obtain ⟨he₁, le, hde, hbe⟩ := he
  obtain ⟨lp, cp, hcp, hpl⟩ := D.decomp (mem_parab.1 hp).1
  have hdp : Dec L S UL p lp := ⟨cp, hcp, hpl⟩
  have hαp := D.alpha_mem_Qn hp hdp
  have hαe := D.alpha_mem_Qn he₁ hde
  refine ⟨(parab (L ⊔ S) n W i).mul_mem ((parab (L ⊔ S) n W i).mul_mem hp he₁)
    ((parab (L ⊔ S) n W i).inv_mem hp), lp * le * lp⁻¹,
    D.dec_mul (D.dec_mul hdp hde) (D.dec_inv hdp), ?_⟩
  rw [map_mul, map_mul, map_inv,
    blk_mul_Qn hi hin hP hQ ((Qn n i).mul_mem hαp hαe) ((Qn n i).inv_mem hαp),
    blk_mul_Qn hi hin hP hQ hαp hαe, hbe, mul_one,
    ← blk_mul_Qn hi hin hP hQ hαp ((Qn n i).inv_mem hαp), mul_inv_cancel]
  exact blk_one hne

theorem Ebk_isPGroup {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n} (hP : P.val + 1 = i)
    (hQ : Q.val = i) : IsPGroup 2 ↥(D.Ebk hi hin hP hQ) := by
  refine isPGroup_two_of_forall fun x hx => ?_
  obtain ⟨hx₁, l, hd, hb⟩ := hx
  exact D.two_elt_of_blk hi hin hP hQ hx₁ hd hb

theorem Ebk_le_pCoreOf {i : ℕ} (hi : 1 ≤ i) (hin : i + 1 < n) {P Q : Fin n}
    (hP : P.val + 1 = i) (hQ : Q.val = i) :
    D.Ebk hi hin hP hQ ≤ pCoreOf 2 (parab (L ⊔ S) n W i) :=
  le_pCoreOf_of_le_normalizer 2 (fun _ hx => hx.1) (D.Ebk_normal hi hin hP hQ)
    (D.Ebk_isPGroup hi hin hP hQ)

include D

theorem exists_odd_lift {s : SLt n} (hs : s * s * s = 1) :
    ∃ l : ↥L, Odd (orderOf (l : G)) ∧ (D.α l = s ∨ D.α l = s * s) := by
  obtain ⟨l₀, hl₀⟩ := D.surj s
  have hpos : 0 < orderOf (l₀ : G) := orderOf_pos _
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨l₀ ^ 2 ^ k, ?_, ?_⟩
  · have h1 : orderOf ((l₀ : G) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact dvd_mul_right _ _), hkm]
      exact Nat.mul_div_cancel_left _ (by positivity)
    have h2 : (((l₀ ^ 2 ^ k : ↥L)) : G) = (l₀ : G) ^ 2 ^ k := rfl
    rw [h2, h1]
    exact hm
  · rw [map_pow, hl₀]
    exact pow_two_pow_cases hs k

theorem exists_comm_lift {j : ℕ} {t u : SLt n} (ht3 : t * t * t = 1) (hu2 : u * u = 1)
    (ht : t ∈ Qn n j) (hu : u ∈ Ut n) :
    ∃ l : ↥L, (l : G) ∈ oTwoUpper (parab (L ⊔ S) n W j) ∧
      (D.α l = t * u * (t * t) * u ∨ D.α l = (t * t) * u * t * u) := by
  obtain ⟨tl, hodd, hαt⟩ := D.exists_odd_lift ht3
  obtain ⟨ul, hul⟩ := D.surj u
  have hu' : u ∈ Qn n j := Ut_le_Qn n j hu
  have ht2 : t * t ∈ Qn n j := (Qn n j).mul_mem ht ht
  have hαtQ : D.α tl ∈ Qn n j := by
    rcases hαt with h | h
    · rw [h]; exact ht
    · rw [h]; exact ht2
  have htP : (tl : G) ∈ parab (L ⊔ S) n W j := D.mem_parab_of_alpha tl hαtQ
  have huP : (ul : G) ∈ parab (L ⊔ S) n W j := D.mem_parab_of_alpha ul (hul ▸ hu')
  have htY : (tl : G) ∈ oTwoUpper (parab (L ⊔ S) n W j) := mem_oTwoUpper_of_odd htP hodd
  have htiY : (tl : G)⁻¹ ∈ oTwoUpper (parab (L ⊔ S) n W j) :=
    (oTwoUpper (parab (L ⊔ S) n W j)).inv_mem htY
  have hconj : (ul : G) * (tl : G)⁻¹ * (ul : G)⁻¹ ∈ oTwoUpper (parab (L ⊔ S) n W j) :=
    conj_mem_oTwoUpper (Subgroup.le_normalizer huP) htiY
  refine ⟨tl * ul * tl⁻¹ * ul⁻¹, ?_, ?_⟩
  · have e : (((tl * ul * tl⁻¹ * ul⁻¹ : ↥L)) : G) =
        (tl : G) * ((ul : G) * (tl : G)⁻¹ * (ul : G)⁻¹) := by
      simp [mul_assoc]
    rw [e]
    exact (oTwoUpper (parab (L ⊔ S) n W j)).mul_mem htY hconj
  · have e2 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hul]
    rcases hαt with h | h
    · left
      rw [h]
      have e1 : t⁻¹ = t * t := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact ht3)
      rw [e1, e2]
    · right
      rw [h]
      have e1 : (t * t)⁻¹ = t := inv_eq_of_mul_eq_one_right ht3
      rw [e1, e2]

end P0Setup

end CFSG.Quasithin.FLc
