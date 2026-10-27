module

public import CFSG.Milestones.ASVolI.C31.J4NP.Prop12

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.J4Loc (omegaZ)

variable {R : Subgroup J}

theorem burnsideJ4NP_exists_not_mem_Hj
    (hR : burnsideJ4NP_Hyp R) :
    ∃ l ∈ Subgroup.normalizer (R : Set J), l ∉ Hj := by
  by_contra h
  push_neg at h
  apply burnsideJ4NP_not_le_Hj_conj hR 1
  intro x hx
  rw [burnsideJ4NP_mem_map_conj]
  simpa using h x hx

theorem burnsideJ4NP_card_mul_le {G : Type*} [Group G] [Finite G] {A B Z : Subgroup G}
    (hA : A ≤ Z) (hB : B ≤ Z) :
    Nat.card ↥A * Nat.card ↥B ≤ Nat.card ↥Z * Nat.card ↥(A ⊓ B) := by
  have h1 := Subgroup.relIndex_mul_card (H := B) (K := A)
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := Z)
  rw [inf_eq_left.mpr hB] at h2
  rw [inf_comm] at h1
  have hpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hne : B.relIndex Z ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    omega
  have h3 : B.relIndex A ≤ B.relIndex Z := Subgroup.relIndex_le_of_le_right hA hne
  calc Nat.card ↥A * Nat.card ↥B = B.relIndex A * Nat.card ↥(A ⊓ B) * Nat.card ↥B := by rw [h1]
    _ ≤ B.relIndex Z * Nat.card ↥(A ⊓ B) * Nat.card ↥B := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul_right _ h3
    _ = Nat.card ↥Z * Nat.card ↥(A ⊓ B) := by rw [← h2]; ring

theorem burnsideJ4NP_lemma9_sq
    (hR : burnsideJ4NP_Hyp R) :
    Nat.card ↥(omegaZ R ⊓ Eg uJ 11) ^ 2 ≤ 8 * Nat.card ↥(omegaZ R) := by
  have hF := j4Facts
  obtain ⟨l, hlN, hlH⟩ := burnsideJ4NP_exists_not_mem_Hj hR
  set A := omegaZ R ⊓ Eg uJ 11 with hA
  set B := A.map (MulAut.conj l).toMonoidHom with hB
  have hAZ : A ≤ omegaZ R := inf_le_left
  have hBZ : B ≤ omegaZ R := by
    rintro _ ⟨a, ha, rfl⟩
    exact CFSG.Quasithin.J4Loc.omegaZ_conj hlN (Subgroup.mem_inf.mp ha).1
  have hcardB : Nat.card ↥B = Nat.card ↥A := burnsideJ4KW_card_map_conj A l
  have hAB : Nat.card ↥(A ⊓ B) ≤ 8 := by
    have hsub : ((A ⊓ B : Subgroup J) : Set J) ⊆
        {x : J | x ∈ Eg uJ 11 ∧ l⁻¹ * x * l ∈ Eg uJ 11} := by
      intro x hx
      obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
      refine ⟨(Subgroup.mem_inf.mp hxA).2, ?_⟩
      rw [hB, burnsideJ4NP_mem_map_conj] at hxB
      exact (Subgroup.mem_inf.mp hxB).2
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : Nat.card ↥(A ⊓ B) = ((A ⊓ B : Subgroup J) : Set J).ncard := Nat.card_coe_set_eq _
    rw [h2]
    exact h1.trans (card_inter_le hF hlH)
  have hmul := burnsideJ4NP_card_mul_le hAZ hBZ
  rw [hcardB] at hmul
  calc Nat.card ↥A ^ 2 = Nat.card ↥A * Nat.card ↥A := sq _
    _ ≤ Nat.card ↥(omegaZ R) * Nat.card ↥(A ⊓ B) := hmul
    _ ≤ Nat.card ↥(omegaZ R) * 8 := Nat.mul_le_mul_left _ hAB
    _ = 8 * Nat.card ↥(omegaZ R) := mul_comm _ _

theorem burnsideJ4NP_lemma9_le_E
    (hR : burnsideJ4NP_Hyp R)
    (hZE : omegaZ R ≤ Eg uJ 11) : Nat.card ↥(omegaZ R) ≤ 8 := by
  have h := burnsideJ4NP_lemma9_sq hR
  rw [inf_eq_left.mpr hZE] at h
  have hpos : 0 < Nat.card ↥(omegaZ R) := Nat.card_pos
  nlinarith

@[expose] def burnsideJ4NP_StarProp : Prop :=
  ∀ A : Subgroup J, A ≤ P0 → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) → (∀ x ∈ A, x * x = 1) →
    ¬ A ≤ Eg uJ 11 → Nat.card ↥A ≤ 2 ^ 10

theorem burnsideJ4NP_lemma9_of_star
    (hstar : burnsideJ4NP_StarProp) (hR : burnsideJ4NP_Hyp R) :
    Nat.card ↥(omegaZ R) ≤ 2 ^ 10 ∧ Nat.card ↥(omegaZ R ⊓ Eg uJ 11) ≤ 2 ^ 6 := by
  have hZ : Nat.card ↥(omegaZ R) ≤ 2 ^ 10 := by
    by_cases hZE : omegaZ R ≤ Eg uJ 11
    · exact (burnsideJ4NP_lemma9_le_E hR hZE).trans (by norm_num)
    · refine hstar _ ((CFSG.Quasithin.J4Loc.omegaZ_le R).trans hR.le)
        (fun x hx y hy => hx.2.1 y hy.1) (fun x hx => hx.2.2) hZE
  refine ⟨hZ, ?_⟩
  have h := burnsideJ4NP_lemma9_sq hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥(omegaZ R ⊓ Eg uJ 11) := (burnsideJ4NP_Z_isPGroup hR).to_le inf_le_left
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  rw [hk] at h ⊢
  have h3 : 2 ^ (2 * k) ≤ 2 ^ 13 := by
    calc 2 ^ (2 * k) = (2 ^ k) ^ 2 := by rw [mul_comm, pow_mul]
      _ ≤ 8 * Nat.card ↥(omegaZ R) := h
      _ ≤ 8 * 2 ^ 10 := Nat.mul_le_mul_left _ hZ
      _ = 2 ^ 13 := by norm_num
  have h4 : 2 * k ≤ 13 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

inductive burnsideJ4NP_ReachP : Subgroup J → Prop
  | base : burnsideJ4NP_ReachP (Subgroup.zpowers CFSG.Quasithin.J4Loc.z0)
  | step {A B : Subgroup J} {x : J} : burnsideJ4NP_ReachP A →
      x ∈ Hj ⊓ Subgroup.centralizer (A : Set J) → burnsideJ4NP_Is2A x → x ∉ A →
      burnsideJ4NP_IsHCl (A ⊔ Subgroup.zpowers x) B → Nat.card ↥B ≤ 2 ^ 10 →
      Nat.card ↥(B ⊓ Eg uJ 11) ≤ 2 ^ 6 → burnsideJ4NP_ReachP B

theorem burnsideJ4NP_chain_stepP
    (hstar : burnsideJ4NP_StarProp) (hR : burnsideJ4NP_Hyp R)
    {A : Subgroup J} (hA : burnsideJ4NP_ReachP A) (hAZ : A ≤ omegaZ R) {y : J}
    (hy : y ∈ omegaZ R) (hy2A : burnsideJ4NP_Is2A y) (hyA : y ∉ A) :
    ∃ B : Subgroup J, burnsideJ4NP_ReachP B ∧ B ≤ omegaZ R ∧ A ≤ B ∧ y ∈ B := by
  have hF := j4Facts
  obtain ⟨hZ10, hZE6⟩ := burnsideJ4NP_lemma9_of_star hstar hR
  set Z := omegaZ R with hZ
  obtain ⟨hZcl, hPZH, hPZmax⟩ := burnsideJ4NP_Z_Hclosed hR
  set A' := A ⊔ Subgroup.zpowers y with hA'
  have hyZ' : Subgroup.zpowers y ≤ Z := by
    rw [Subgroup.zpowers_le]
    exact hy
  have hA'Z : A' ≤ Z := sup_le hAZ hyZ'
  have hZH : Z ≤ Hj := (CFSG.Quasithin.J4Loc.omegaZ_le R).trans (hR.le.trans P0_le_Hj)
  have hCC : Subgroup.centralizer (Z : Set J) ≤ Subgroup.centralizer (A' : Set J) :=
    Subgroup.centralizer_le hA'Z
  have hPZK : P0 ⊓ Subgroup.centralizer (Z : Set J) ≤ Hj ⊓ Subgroup.centralizer (A' : Set J) :=
    le_inf (inf_le_left.trans P0_le_Hj) (inf_le_right.trans hCC)
  have hPZ2 : IsPGroup 2 ↥(P0 ⊓ Subgroup.centralizer (Z : Set J)) :=
    (CFSG.Quasithin.J4Loc.isPGroup_P0 hF).to_le inf_le_left
  obtain ⟨P, hPZP, hPK, hP2, hPmax⟩ := burnsideJ4NP_exists_max hPZK hPZ2
  have hBZ : omegaZ P ≤ Z :=
    burnsideJ4NP_cl_le hZcl hPZH hPZmax (hPK.trans inf_le_left) hP2 hPZP
  have hZc : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => ha.2.1 b hb.1
  have hZs : ∀ a ∈ Z, a * a = 1 := fun a ha => ha.2.2
  have hA'B : A' ≤ omegaZ P :=
    burnsideJ4NP_le_omegaZ_of_max (hA'Z.trans hZH)
      ((burnsideJ4NP_Z_isPGroup hR).to_le hA'Z)
      (fun a ha b hb => hZc a (hA'Z ha) b (hA'Z hb)) (fun a ha => hZs a (hA'Z ha)) hPK hP2 hPmax
  refine ⟨omegaZ P, ?_, hBZ, le_sup_left.trans hA'B,
    hA'B (le_sup_right (a := A) (Subgroup.mem_zpowers y))⟩
  exact burnsideJ4NP_ReachP.step hA (Subgroup.mem_inf.mpr ⟨hZH hy,
    Subgroup.mem_centralizer_iff.mpr fun a ha => hZc a (hAZ ha) y hy⟩) hy2A hyA
    ⟨P, hPK, hP2, hPmax, rfl⟩ ((Subgroup.card_le_of_le hBZ).trans hZ10)
    ((Subgroup.card_le_of_le (inf_le_inf_right _ hBZ)).trans hZE6)

theorem burnsideJ4NP_chainP
    (hstar : burnsideJ4NP_StarProp) (hR : burnsideJ4NP_Hyp R) :
    ∀ (l : List J) (A : Subgroup J), burnsideJ4NP_ReachP A → A ≤ omegaZ R →
      (∀ y ∈ l, y ∈ omegaZ R ∧ burnsideJ4NP_Is2A y) →
      ∃ B : Subgroup J, burnsideJ4NP_ReachP B ∧ B ≤ omegaZ R ∧ A ≤ B ∧ ∀ y ∈ l, y ∈ B
  | [], A, hA, hAZ, _ => ⟨A, hA, hAZ, le_rfl, by simp⟩
  | y :: l, A, hA, hAZ, hl => by
    have hy := hl y (List.mem_cons_self ..)
    have hl' : ∀ y' ∈ l, y' ∈ omegaZ R ∧ burnsideJ4NP_Is2A y' :=
      fun y' hy' => hl y' (List.mem_cons_of_mem _ hy')
    by_cases hyA : y ∈ A
    · obtain ⟨B, hB, hBZ, hAB, hlB⟩ := burnsideJ4NP_chainP hstar hR l A hA hAZ hl'
      refine ⟨B, hB, hBZ, hAB, fun y' hy' => ?_⟩
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hAB hyA
      · exact hlB y' hy'
    · obtain ⟨A₁, hA₁, hA₁Z, hAA₁, hyA₁⟩ :=
        burnsideJ4NP_chain_stepP hstar hR hA hAZ hy.1 hy.2 hyA
      obtain ⟨B, hB, hBZ, hA₁B, hlB⟩ := burnsideJ4NP_chainP hstar hR l A₁ hA₁ hA₁Z hl'
      refine ⟨B, hB, hBZ, hAA₁.trans hA₁B, fun y' hy' => ?_⟩
      rcases List.mem_cons.mp hy' with rfl | hy'
      · exact hA₁B hyA₁
      · exact hlB y' hy'

theorem burnsideJ4NP_prop12P_of_star
    (hstar : burnsideJ4NP_StarProp) (hR : burnsideJ4NP_Hyp R) :
    ∃ A : Subgroup J, burnsideJ4NP_ReachP A ∧ A ≤ omegaZ R ∧ burnsideJ4NP_W R ≤ A := by
  classical
  have hfin : Set.Finite {x : J | x ∈ omegaZ R ∧ burnsideJ4NP_Is2A x} := Set.toFinite _
  obtain ⟨B, hB, hBZ, -, hlB⟩ := burnsideJ4NP_chainP hstar hR hfin.toFinset.toList
    (Subgroup.zpowers CFSG.Quasithin.J4Loc.z0) burnsideJ4NP_ReachP.base
    (by rw [Subgroup.zpowers_le]; exact burnsideJ4NP_z0_mem_Z hR)
    (fun y hy => by simpa using hy)
  refine ⟨B, hB, hBZ, ?_⟩
  rw [burnsideJ4NP_W, Subgroup.closure_le]
  rintro x ⟨hxZ, g, rfl⟩
  exact hlB _ (by simpa using (show _ ∧ _ from ⟨hxZ, g, rfl⟩))

@[expose] def burnsideJ4NP_OpenReachP : Prop :=
  ∀ A : Subgroup J, burnsideJ4NP_ReachP A → ∀ R : Subgroup J, burnsideJ4NP_Hyp R →
    A ≤ omegaZ R → burnsideJ4NP_W R ≤ A →
      ∃ c : J, burnsideJ4NP_F.map (MulAut.conj c).toMonoidHom ≤ burnsideJ4NP_W R

theorem burnsideJ4NP_maxNonParabolicP0_of_openReachP_of_star
    (hstar : burnsideJ4NP_StarProp) (h : burnsideJ4NP_OpenReachP) :
    burnsideJ4KW_MaxNonParabolicP0 := by
  refine burnsideJ4NP_maxNonParabolicP0_of_openW fun R hR => ?_
  obtain ⟨A, hA, hAZ, hWA⟩ := burnsideJ4NP_prop12P_of_star hstar hR
  exact h A hA R hR hAZ hWA

end CFSG.ASVolI
