module

public import CFSG.Quasithin.Background.SzG11G94Plane
public import CFSG.Quasithin.Background.SzG11G94Solv
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzG11G94

open CFSG.Quasithin.G11 CFSG.Open CFSG.Quasithin.SzN31 CFSG.Quasithin.SzN31.CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem fitting_eq_of_card_three {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hV : Module.finrank (ZMod 2) V = 4) (hR5 : pCoreOf 5 Γ = ⊥)
    (hP : Nat.card (pCoreOf 3 Γ) = 3) :
    (genFittingFitting ↥Γ).map Γ.subtype = pCoreOf 3 Γ := by
  have := SzN31.finite_linearEquiv_zmod2 V
  have hbot : ∀ d : ℕ, d.Prime → d ≠ 3 → pCoreOf d Γ = ⊥ := by
    intro d hd hd3
    by_contra hne
    rcases prime_three_or_five_of_pCoreOf_ne_bot hyp hV hd hne with h | h
    · exact hd3 h
    · subst h
      exact hne hR5
  set F : Subgroup (GLV V) := (genFittingFitting ↥Γ).map Γ.subtype with hFdef
  have hF3 : Nat.card F = 3 := by
    have hpos : Nat.card F ≠ 0 := Nat.card_pos.ne'
    have huniq : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card F → d = 3 := by
      intro d hd hdvd
      by_contra hd3
      have h1 : Nat.card (pCoreOf d Γ) = d ^ (Nat.card F).factorization d :=
        card_pCoreOf_eq_fitting hd Γ
      rw [hbot d hd hd3, Subgroup.card_bot] at h1
      have hf := hd.factorization_pos_of_dvd hpos hdvd
      have : 1 < d ^ (Nat.card F).factorization d := Nat.one_lt_pow hf.ne' hd.one_lt
      omega
    obtain ⟨L, hL⟩ : ∃ L : ℕ, Nat.card F = 3 ^ L :=
      ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hpos huniq⟩
    have h3 : Nat.card (pCoreOf 3 Γ) = 3 ^ (Nat.card F).factorization 3 :=
      card_pCoreOf_eq_fitting Nat.prime_three Γ
    rw [hP, hL, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same] at h3
    rw [hL, ← h3]
  exact (Subgroup.eq_of_le_of_card_ge (pCoreOf_le_fitting Nat.prime_three Γ)
    (by rw [hF3, hP])).symm

theorem three_nonsolv {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hV : Module.finrank (ZMod 2) V = 4) (hR5 : pCoreOf 5 Γ = ⊥)
    (hP : Nat.card (pCoreOf 3 Γ) = 3) (hns : ¬ Group.IsSolvable ↥Γ) :
    m = 1 ∧ IsGammaL24 Γ ∧ 10 ∣ Nat.card ↥Γ := by
  classical
  have := SzN31.finite_linearEquiv_zmod2 V
  set P := pCoreOf 3 Γ with hPdef
  have hPne : P ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hP; omega
  have hfixP : fixedSpace P = ⊥ := g94_fixedSpace_pCoreOf_eq_bot hyp hPne
  obtain ⟨w, hwP, hw1, hw3, hord, hPz⟩ := SmD4Three.exists_generator_three hP
  have hfpf : ∀ v, w v = v → v = 0 := by
    intro v hv
    have : v ∈ fixedSpace P := by rw [hPz]; exact mem_fixedSpace_zpowers_iff.2 hv
    rw [hfixP] at this
    simpa using this
  have hw : ∀ v, w (w v) + w v + v = 0 := by
    intro v
    apply hfpf
    have h3 : w (w (w v)) = v := by
      have := DFunLike.congr_fun hw3 v
      simpa [pow_succ, LinearEquiv.mul_apply] using this
    rw [map_add, map_add, h3]
    abel
  have hFP : (genFittingFitting ↥Γ).map Γ.subtype = P := fitting_eq_of_card_three hyp hV hR5 hP
  have hcommP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    rw [hPz] at hx hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self w i j).eq
  have hinv : ∀ b ∈ A, b ≠ 1 → ∀ x ∈ P, b * x * b⁻¹ = x⁻¹ := by
    intro b hbA hb1
    have hb2 : b * b = 1 := by
      have := hyp.A_elem.2 b hbA
      rwa [pow_two] at this
    rcases SmD4Five.centralizes_or_inverts Nat.prime_three hP hcommP hb2
      (fun x hx => pCoreOf_normal_conj 3 Γ b (hyp.A_le hbA) x hx) with h | h
    · exfalso
      apply hb1
      apply hyp.faithful b hbA
      intro f hf
      have hfP : f ∈ P := hFP ▸ hf
      exact mul_inv_eq_iff_eq_mul.1 (h f hfP)
    · exact h
  obtain ⟨a', ha'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (SmD4.A_ne_bot hyp)
  set a : GLV V := (a' : GLV V) with hadef
  have haA : a ∈ A := a'.2
  have ha1 : a ≠ 1 := fun h => ha'1 (Subtype.ext h)
  have haΓ : a ∈ Γ := hyp.A_le haA
  have hm1 : m = 1 := by
    have hAle : ∀ b ∈ A, b = 1 ∨ b = a := by
      intro b hb
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · right
        have hab : a⁻¹ * b ∈ A := A.mul_mem (A.inv_mem haA) hb
        have h1 : a⁻¹ * b = 1 := by
          apply hyp.faithful _ hab
          intro f hf
          have hfP : f ∈ P := hFP ▸ hf
          have e1 := hinv b hb hb1 f hfP
          have e2 := hinv a haA ha1 f hfP
          have : (a⁻¹ * b) * f * (a⁻¹ * b)⁻¹ = f := by
            calc (a⁻¹ * b) * f * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * f * b⁻¹) * a := by group
              _ = a⁻¹ * (a * f * a⁻¹) * a := by rw [e1, e2]
              _ = f := by group
          exact mul_inv_eq_iff_eq_mul.1 this
        have h2 : b = a := by
          have := congrArg (fun x => a * x) h1
          simpa using this
        exact h2
    have hcardA : Nat.card A ≤ 2 := by
      have hsub : (A : Set (GLV V)) ⊆ {1, a} := fun b hb => by
        rcases hAle b hb with h | h <;> simp [h]
      calc Nat.card A = (A : Set (GLV V)).ncard := (Nat.card_coe_set_eq _).symm ▸ rfl
        _ ≤ ({1, a} : Set (GLV V)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := (Set.ncard_insert_le _ _).trans (by simp)
    have hA := hyp.A_card
    have hm := hyp.A_ne
    by_contra hne
    have h2 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hPΓ : P ≤ Γ := Subgroup.map_subtype_le _
  obtain ⟨h180, hΓeq⟩ := eq_normalizer_zpowers_of_nonsolvable (card_linearEquiv_four hV) hord
    (hPΓ hwP) haΓ (fun γ hγ => by rw [← hPz]; exact pCoreOf_normal_conj 3 Γ γ hγ w hwP)
    (hinv a haA ha1 w hwP) hns (card_centralizer_le hw hV)
  refine ⟨hm1, ⟨P, hP, ?_, by rw [hPz]; exact hΓeq⟩, (by norm_num : 10 ∣ 180).trans h180⟩
  intro b hb hb1 v hbv
  have hb' : b ∈ Subgroup.zpowers w := by rw [← hPz]; exact hb
  rcases mem_zpowers_cases_of_orderOf_three hord hb' with h | h | h
  · exact absurd h hb1
  · apply hfpf
    rw [← h]
    exact hbv
  · apply hfpf
    have h1 := apply_inv_apply w v
    rw [h] at hbv
    rw [hbv] at h1
    exact h1

open SmD4 SmD4Five

theorem smallCase4_ns {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m)
    (hns : ¬ Group.IsSolvable ↥Γ) (hm : m ≤ 2) (hd : Module.finrank (ZMod 2) V = 4) :
    G94Concl Γ A m := by
  have := SzN31.finite_linearEquiv_zmod2 V
  by_cases h5 : A ≤ Subgroup.centralizer (pCoreOf 5 Γ : Set (GLV V))
  ·
    have hR5 : pCoreOf 5 Γ = ⊥ := by
      by_contra hne
      obtain ⟨-, c, hcR, -, hc5, -, -, hc0⟩ := exists_generator_five hyp hd hne
      obtain ⟨a', ha'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (A_ne_bot hyp)
      have ha2 : (a' : GLV V) * a' = 1 := by
        have := hyp.A_elem.2 a' a'.2
        rwa [pow_two] at this
      have hac : (a' : GLV V) * c = c * a' :=
        ((Subgroup.mem_centralizer_iff.1 (h5 a'.2)) c hcR).symm
      exact ha'1 (Subtype.ext (five_invol hd hc5 hc0 ha2 hac))
    have hPne : pCoreOf 3 Γ ≠ ⊥ := by
      intro h3
      refine A_ne_bot hyp (g94_eq_bot_of_le_centralizer_pCoreOf hyp le_rfl fun p hp hp2 => ?_)
      by_cases hp3 : p = 3
      · subst hp3
        rw [h3]
        exact le_centralizer_bot A
      · by_cases hp5 : p = 5
        · subst hp5
          exact h5
        · have : pCoreOf p Γ = ⊥ := by
            by_contra hne
            rcases prime_three_or_five_of_pCoreOf_ne_bot hyp hd hp hne with h | h
            · exact hp3 h
            · exact hp5 h
          rw [this]
          exact le_centralizer_bot A
    have hcard : Nat.card (pCoreOf 3 Γ) = 3 ∨ Nat.card (pCoreOf 3 Γ) = 9 := by
      have hdvd := card_dvd_nine_of_isPGroup_three hd (isPGroup_pCoreOf 3 Γ)
      obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (by simpa using hdvd :
        Nat.card (pCoreOf 3 Γ) ∣ 3 ^ 2)
      have hne1 : Nat.card (pCoreOf 3 Γ) ≠ 1 := fun h => hPne (Subgroup.card_eq_one.1 h)
      interval_cases i
      · have h1 : Nat.card (pCoreOf 3 Γ) = 1 := by rw [hi']; norm_num
        exact absurd h1 hne1
      · left
        simpa using hi'
      · right
        simpa using hi'
    rcases hcard with h3 | h9
    · obtain ⟨hm1, hGL, h10⟩ := three_nonsolv hyp hd hR5 h3 hns
      exact Or.inr (Or.inr (Or.inl ⟨hm1, hd, Or.inl ⟨hGL, h10⟩⟩))
    · have hfixP : fixedSpace (pCoreOf 3 Γ) = ⊥ := g94_fixedSpace_pCoreOf_eq_bot hyp hPne
      obtain ⟨Ψ, hΨ⟩ := SmD4Nine.exists_equiv_of_nine hd h9 hfixP
      have hΓO : Γ ≤ orthogonalSubgroupOf (fun v => q0 (Ψ v)) :=
        SmD4Nine.orthogonal_of_normalizes hΨ fun γ hγ p hp => pCoreOf_normal_conj 3 Γ γ hγ p hp
      have hplus := isPlusQuadForm_comp Ψ
      have hcardO := card_orthogonal_le Ψ
      have hPΓ : pCoreOf 3 Γ ≤ Γ := Subgroup.map_subtype_le _
      have h9Γ : 9 ∣ Nat.card ↥Γ := h9 ▸ Subgroup.card_dvd_of_le hPΓ
      have h2Γ : 2 ^ m ∣ Nat.card ↥Γ := hyp.A_card ▸ Subgroup.card_dvd_of_le hyp.A_le
      rcases (by have := hyp.A_ne; omega : m = 1 ∨ m = 2) with hm1 | hm2
      · subst hm1
        have h18 : 18 ∣ Nat.card ↥Γ := by
          have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 2) h9Γ
            (by simpa using h2Γ)
          simpa using this
        refine Or.inr (Or.inr (Or.inl ⟨rfl, hd, Or.inr ⟨fun v => q0 (Ψ v), hplus, ?_, hΓO, h18⟩⟩))
        exact (pCoreOf_le_of_card_nine hd (hPΓ.trans hΓO) h9).trans hPΓ
      · subst hm2
        have h36 : 36 ∣ Nat.card ↥Γ := by
          have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 9 4) h9Γ
            (by simpa using h2Γ)
          simpa using this
        have h18 : 18 ∣ Nat.card ↥Γ := (by norm_num : (18 : ℕ) ∣ 36).trans h36
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hd,
          ⟨fun v => q0 (Ψ v), hplus, hΓO, relIndex_le_two hΓO hcardO h36⟩, h18⟩)))
  ·
    have hm1 : m = 1 := (counting_prime_ge_five hyp Nat.prime_five le_rfl h5).1
    obtain ⟨hdih, h10⟩ := five_case hyp hd hm1 h5
    exact Or.inr (Or.inl ⟨hm1, hd, hdih, h10⟩)

end CFSG.Quasithin.SzG11G94
