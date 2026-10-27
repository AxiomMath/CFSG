module

public import CFSG.Sporadic.J4.QTRankProof
public import Certificates.Data.J4Loc.Native

public section

namespace CFSG.Quasithin.J4Loc

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] noncomputable def z0 : J := eta uJ 11 1131

@[expose] noncomputable def V0 : Subgroup J :=
  Subgroup.closure {eta uJ 11 422, eta uJ 11 553, eta uJ 11 1131}

@[expose] noncomputable def maskSub (B : List ℕ) : Subgroup J :=
  Subgroup.closure ((eta uJ 11) '' {c | c ∈ B})

theorem V0L_closed : 0 ∈ V0L ∧ ∀ x ∈ V0L, ∀ y ∈ V0L, x ^^^ y ∈ V0L := by
  refine ⟨by simp [V0L], ?_⟩
  intro x hx y hy
  simp only [V0L, List.mem_cons, List.not_mem_nil, or_false] at hx hy ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

@[expose] def MaskList (A : Subgroup J) (B : List ℕ) : Prop :=
  ∀ c, c ∈ B ↔ (c < 2048 ∧ eta uJ 11 c ∈ A)

section WithFacts

variable (hM : MatFacts)
include hM

theorem eta_inj' {c d : ℕ} (hc : c < 2048) (hd : d < 2048)
    (h : eta uJ 11 c = eta uJ 11 d) : c = d := eta_inj hM c hc d hd h

theorem eta_mul_eta (c d : ℕ) :
    eta uJ 11 c * eta uJ 11 d = eta uJ 11 (c ^^^ d) :=
  (eta_xor (elem_uJ hM) le_rfl c d).symm

theorem eta_inv (c : ℕ) : (eta uJ 11 c)⁻¹ = eta uJ 11 c :=
  inv_eq_of_mul_eq_one_right (eta_sq (elem_uJ hM) c)

theorem mem_maskSub_iff {B : List ℕ} (h0 : 0 ∈ B)
    (hx : ∀ x ∈ B, ∀ y ∈ B, x ^^^ y ∈ B) {x : J} :
    x ∈ maskSub B ↔ ∃ c ∈ B, x = eta uJ 11 c := by
  constructor
  · intro hx'
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨c, hc, rfl⟩
    | one => exact ⟨0, h0, (eta_zero _ _).symm⟩
    | mul y z _ _ hy hz =>
      obtain ⟨c, hc, rfl⟩ := hy
      obtain ⟨d, hd, rfl⟩ := hz
      exact ⟨c ^^^ d, hx c hc d hd, eta_mul_eta hM c d⟩
    | inv y _ hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      exact ⟨c, hc, eta_inv hM c⟩
  · rintro ⟨c, hc, rfl⟩
    exact Subgroup.subset_closure ⟨c, hc, rfl⟩

omit hM in
theorem maskSub_le_Eg (B : List ℕ) : maskSub B ≤ Eg uJ 11 := by
  rw [maskSub, Subgroup.closure_le]
  rintro _ ⟨c, -, rfl⟩
  exact eta_mem_Eg 11 le_rfl c

theorem V0_eq_maskSub : V0 = maskSub V0L := by
  have hsub : ∀ c ∈ V0L, eta uJ 11 c ∈ V0 := by
    intro c hc
    have g1 : eta uJ 11 422 ∈ V0 := Subgroup.subset_closure (by simp)
    have g2 : eta uJ 11 553 ∈ V0 := Subgroup.subset_closure (by simp)
    have g3 : eta uJ 11 1131 ∈ V0 := Subgroup.subset_closure (by simp)
    have g4 : eta uJ 11 911 ∈ V0 := by
      rw [show (911 : ℕ) = 422 ^^^ 553 by decide, ← eta_mul_eta hM]
      exact V0.mul_mem g1 g2
    simp only [V0L, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [eta_zero]; exact V0.one_mem
    · exact g1
    · exact g2
    · exact g4
    · exact g3
    · rw [show (1485 : ℕ) = 422 ^^^ 1131 by decide, ← eta_mul_eta hM]
      exact V0.mul_mem g1 g3
    · rw [show (1602 : ℕ) = 553 ^^^ 1131 by decide, ← eta_mul_eta hM]
      exact V0.mul_mem g2 g3
    · rw [show (2020 : ℕ) = 911 ^^^ 1131 by decide, ← eta_mul_eta hM]
      exact V0.mul_mem g4 g3
  apply le_antisymm
  · rw [V0, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl | rfl <;> exact Subgroup.subset_closure ⟨_, by simp [V0L], rfl⟩
  · rw [maskSub, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact hsub c hc

theorem mem_V0_iff {x : J} :
    x ∈ V0 ↔ ∃ c ∈ V0L, x = eta uJ 11 c := by
  rw [V0_eq_maskSub hM]
  exact mem_maskSub_iff hM V0L_closed.1 V0L_closed.2

theorem normalized_of_gens
    {K : Subgroup J} (hKE : K ≤ Eg uJ 11)
    (hk : ∀ i < 4, ∀ c < 2048, eta uJ 11 c ∈ K →
      eta uJ 11 (actT (kTab i) c) ∈ K ∧ eta uJ 11 (actT (kInvTab i) c) ∈ K) :
    ∀ g ∈ P0, ∀ x ∈ K, g * x * g⁻¹ ∈ K ∧ g⁻¹ * x * g ∈ K := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    intro x hx
    rcases hy with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
    · have hc : uJ j * x = x * uJ j := Eg_comm (elem_uJ hM) (u_mem_Eg hj) (hKE hx)
      have h1 : uJ j * x * (uJ j)⁻¹ = x := by rw [hc]; group
      have h2 : (uJ j)⁻¹ * x * uJ j = x := by
        rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
      exact ⟨by rw [h1]; exact hx, by rw [h2]; exact hx⟩
    · obtain ⟨c, hc, rfl⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hKE hx)
      have h1 := (Acts_kJ hM hi).2 c hc
      have h2 := (Acts_kJ_inv hM hi).2 c hc
      rw [inv_inv] at h2
      have hc' : c < 2048 := hc
      obtain ⟨k1, k2⟩ := hk i hi c hc' hx
      exact ⟨by rw [h1]; exact k1, by rw [h2]; exact k2⟩
  | one => intro x hx; simp [hx]
  | mul y z _ _ hy hz =>
    intro x hx
    obtain ⟨hz1, hz2⟩ := hz x hx
    obtain ⟨hy1, hy2⟩ := hy _ hz1
    obtain ⟨hy3, hy4⟩ := hy _ hx
    obtain ⟨hz3, hz4⟩ := hz _ hy4
    refine ⟨?_, ?_⟩
    · have : y * z * x * (y * z)⁻¹ = y * (z * x * z⁻¹) * y⁻¹ := by group
      rw [this]; exact (hy _ hz1).1
    · have : (y * z)⁻¹ * x * (y * z) = z⁻¹ * (y⁻¹ * x * y) * z := by group
      rw [this]; exact (hz _ (hy _ hx).2).2
  | inv y _ hy =>
    intro x hx
    obtain ⟨h1, h2⟩ := hy x hx
    exact ⟨by simpa using h2, by simpa using h1⟩

theorem MaskList.card {A : Subgroup J} {B : List ℕ}
    (hAE : A ≤ Eg uJ 11) (h : MaskList A B) (hnd : B.Nodup) : Nat.card A = B.length := by
  classical
  let f : {c : ℕ // c ∈ B} → A := fun c => ⟨eta uJ 11 c, ((h c).1 c.2).2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro c d hcd
      have h1 : eta uJ 11 c = eta uJ 11 d := congrArg Subtype.val hcd
      exact Subtype.ext (eta_inj' hM ((h c).1 c.2).1 ((h d).1 d.2).1 h1)
    · intro x
      obtain ⟨c, hc, hxc⟩ := (mem_Eg_iff (elem_uJ hM)).1 (hAE x.2)
      have hcB : c ∈ B := (h c).2 ⟨hc, by rw [← hxc]; exact x.2⟩
      exact ⟨⟨c, hcB⟩, Subtype.ext hxc.symm⟩
  have h1 : Nat.card A = Nat.card {c : ℕ // c ∈ B} := (Nat.card_congr (Equiv.ofBijective f hf)).symm
  have h2 : Nat.card {c : ℕ // c ∈ B} = Nat.card ↥B.toFinset :=
    Nat.card_congr (Equiv.subtypeEquivRight fun c => (List.mem_toFinset).symm)
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

end WithFacts

theorem isPGroup_P0 (hF : J4Facts) :
    IsPGroup 2 P0 := IsPGroup.of_card (card_P0 hF.mat hF)

end CFSG.Quasithin.J4Loc
