module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmallStmt
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Nine
public import CFSG.Quasithin.EmptyFaithful.SzN31SmD4Three
public import CFSG.Quasithin.EmptyFaithful.SzN31CntM3p

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

namespace SmD4

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem pCoreOf_le_of_card_nine (hV : Module.finrank (ZMod 2) V = 4) {O P : Subgroup (GLV V)}
    (hPO : P ≤ O) (hP : Nat.card P = 9) : pCoreOf 3 O ≤ P := by
  have := finite_linearEquiv_zmod2 V
  have hP' : Nat.card (P.subgroupOf O) = 9 := by
    rw [← hP]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPO).toEquiv
  have hP3 : IsPGroup 3 (P.subgroupOf O) := IsPGroup.of_card (n := 2) (by rw [hP']; norm_num)
  have hcore : CFSG.pCore 3 ↥O ≤ P.subgroupOf O := by
    refine sSup_le fun K hK => ?_
    obtain ⟨hKn, hK3⟩ := hK
    have hsup : IsPGroup 3 ↥(P.subgroupOf O ⊔ K) := hP3.to_sup_of_normal_right hK3
    have hmap : IsPGroup 3 ↥((P.subgroupOf O ⊔ K).map O.subtype) := hsup.map O.subtype
    have hdvd := card_dvd_nine_of_isPGroup_three hV hmap
    rw [Subgroup.card_map_of_injective O.subtype_injective] at hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have heq : P.subgroupOf O ⊔ K = P.subgroupOf O :=
      (Subgroup.eq_of_le_of_card_ge (le_sup_left : P.subgroupOf O ≤ P.subgroupOf O ⊔ K)
        (by rw [hP']; exact hle)).symm
    rw [← heq]
    exact le_sup_right
  have h := (CFSG.pCore_eq_open (↥O) 3).symm
  unfold pCoreOf
  rw [h]
  calc (CFSG.pCore 3 ↥O).map O.subtype ≤ (P.subgroupOf O).map O.subtype := Subgroup.map_mono hcore
    _ = P := Subgroup.map_subgroupOf_eq_of_le hPO

theorem relIndex_le_two {Γ O : Subgroup (GLV V)} (hΓO : Γ ≤ O) (hO : Nat.card O ≤ 72)
    (hΓ : 36 ∣ Nat.card Γ) : Γ.relIndex O ≤ 2 := by
  have hcard : Nat.card (Γ.subgroupOf O) = Nat.card Γ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓO).toEquiv
  have hmul := Subgroup.card_mul_index (Γ.subgroupOf O)
  rw [hcard] at hmul
  have h36 : 36 ≤ Nat.card Γ := Nat.le_of_dvd Nat.card_pos hΓ
  by_contra hcon
  push Not at hcon
  have h3 : 3 ≤ Γ.relIndex O := hcon
  have := Nat.mul_le_mul h36 h3
  have hrel : Γ.relIndex O = (Γ.subgroupOf O).index := rfl
  rw [hrel] at this
  omega

omit [Finite V] in
theorem A_ne_bot {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m) : A ≠ ⊥ := by
  intro h
  have h1 := hyp.A_card
  rw [h, Subgroup.card_bot] at h1
  have := Nat.one_lt_two_pow (n := m) (by have := hyp.A_ne; omega)
  omega

omit [Finite V] in
theorem le_centralizer_bot (A : Subgroup (GLV V)) :
    A ≤ Subgroup.centralizer ((⊥ : Subgroup (GLV V)) : Set (GLV V)) := by
  intro a _
  exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Subgroup.mem_bot.mp hg]; simp

end SmD4

open SmD4 SmD4Five

theorem smallCase4 : SmallCase 4 := by
  intro V _ _ _ Γ A m hyp hsolv _ hm hd
  have := finite_linearEquiv_zmod2 V
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
    · exact (SmD4Three.three_false hyp hsolv hd hR5 h3).elim
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

end CFSG.Quasithin.SzN31
