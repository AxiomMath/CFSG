module

public import CFSG.Quasithin.EmptyFaithful.S152Y14
public import CFSG.Quasithin.EmptyFaithful.S152NAbs
public import CFSG.Quasithin.EmptyFaithful.S152Y03
public import CFSG.Quasithin.EmptyFaithful.S152Y13

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S152Y

variable {G : Type} [Group G] [Finite G]

section Small

variable {Γ : Type*} [Group Γ]

theorem exists_involution_of_equiv_dihedral' {A : Subgroup Γ} {n : ℕ} [NeZero n]
    (e : ↥A ≃* DihedralGroup n) : ∃ u ∈ A, u ^ 2 = 1 ∧ u ≠ 1 := by
  refine ⟨((e.symm (DihedralGroup.sr 0) : ↥A) : Γ), (e.symm (DihedralGroup.sr 0)).2, ?_, ?_⟩
  · have h : e.symm (DihedralGroup.sr 0) ^ 2 = 1 := by
      rw [← map_pow, pow_two, DihedralGroup.sr_mul_self, map_one]
    exact congrArg Subtype.val h
  · intro h1
    have h2 : e.symm (DihedralGroup.sr 0) = 1 := Subtype.ext h1
    have h3 : DihedralGroup.sr (0 : ZMod n) = 1 := by
      have := congrArg e h2
      simpa using this
    rw [DihedralGroup.one_def] at h3
    cases h3

theorem exists_involution_of_ne_bot [Finite Γ] {P : Subgroup Γ} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    ∃ b ∈ P, b ≠ 1 ∧ b ^ 2 = 1 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.mp hk
  have h2 : 2 ∣ Nat.card P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 h2
  refine ⟨x, x.2, ?_, ?_⟩
  · intro h1
    have : orderOf (x : Γ) = 1 := by rw [h1]; exact orderOf_one
    rw [Subgroup.orderOf_coe, hx] at this
    omega
  · have : (x : Γ) ^ orderOf (x : Γ) = 1 := pow_orderOf_eq_one _
    rwa [Subgroup.orderOf_coe, hx] at this

end Small

section Main

variable {T Mc M : Subgroup G}

theorem involution_mem_of_card {Γ : Type*} [Group Γ] [Finite Γ] {Mb Tb M0 : Subgroup Γ}
    (hsyl : IsSylowTwoOf Tb Mb) (h4 : ¬ 4 ∣ Nat.card Mb) (hM0 : M0 ≤ Mb)
    (hnorm : ∀ g ∈ Mb, ∀ y ∈ M0, g * y * g⁻¹ ∈ M0) {u : Γ} (hu : u ∈ M0) (hu2 : u ^ 2 = 1)
    (hu1 : u ≠ 1) : ∀ x ∈ Tb, x ^ 2 = 1 → x ≠ 1 → x ∈ M0 := by
  have hcard : Nat.card Tb ≤ 2 :=
    S152N.card_le_two_of_dvd hsyl.2.1 (Subgroup.card_dvd_of_le hsyl.1) h4
  intro x hx hx2 hx1
  exact S152N.involution_mem_of_normal hsyl hM0 hnorm
    (fun a ha b hb _ _ ha1 hb1 => S152N.eq_of_card_le_two hcard ha hb ha1 hb1) hu hu2 hu1 hx hx2 hx1

theorem involution_mem_mBar0 (h : Data T Mc M)
    (hc : Case1517One M (V154 T Mc M) (mBar0 T Mc M) ∨
      Case1517Two M (V154 T Mc M) (mBar0 T Mc M) ∨ Case1517Five T M (V154 T Mc M) (mBar0 T Mc M)) :
    ∀ x ∈ autOn T (V154 T Mc M), x ^ 2 = 1 → x ≠ 1 → x ∈ mBar0 T Mc M := by
  have hsyl := isSylowTwoOf_Tb h
  have hM0le := mBar0_le T Mc M
  have hnorm := mBar0_normalized T Mc M
  rcases hc with ⟨-, hA, ⟨e⟩⟩ | ⟨-, ⟨e⟩, ⟨e'⟩⟩ | ⟨-, ⟨e⟩, hT, -⟩
  · obtain ⟨u, hu, hu2, hu1⟩ := exists_involution_of_equiv_dihedral' e
    refine involution_mem_of_card hsyl ?_ hM0le hnorm hu hu2 hu1
    have : Nat.card (autOn M (V154 T Mc M)) = 6 := by
      rw [hA, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  · obtain ⟨u, hu, hu2, hu1⟩ := exists_involution_of_equiv_dihedral' e
    refine involution_mem_of_card hsyl ?_ hM0le hnorm hu hu2 hu1
    have : Nat.card (autOn M (V154 T Mc M)) = 18 := by
      rw [Nat.card_congr e'.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      have : Nat.card (Multiplicative (ZMod 3)) = 3 := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [this]
    omega
  · obtain ⟨u, hu, hu2, hu1⟩ := exists_involution_of_equiv_dihedral' e
    have huniq : ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a ^ 2 = 1 →
        b ^ 2 = 1 → a ≠ 1 → b ≠ 1 → a = b := by
      have key : ∀ {n : ℕ} (f : ↥(autOn T (V154 T Mc M)) ≃* Multiplicative (ZMod n)),
          (∀ x y : Multiplicative (ZMod n), x ^ 2 = 1 → y ^ 2 = 1 → x ≠ 1 → y ≠ 1 → x = y) →
          ∀ a ∈ autOn T (V154 T Mc M), ∀ b ∈ autOn T (V154 T Mc M), a ^ 2 = 1 → b ^ 2 = 1 →
            a ≠ 1 → b ≠ 1 → a = b := by
        intro n f hall a ha b hb ha2 hb2 ha1 hb1
        have h1 : f ⟨a, ha⟩ ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨a, ha⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext ha2
          rw [this, map_one]
        have h2 : f ⟨b, hb⟩ ^ 2 = 1 := by
          rw [← map_pow]
          have : (⟨b, hb⟩ : ↥(autOn T (V154 T Mc M))) ^ 2 = 1 := Subtype.ext hb2
          rw [this, map_one]
        have h3 : f ⟨a, ha⟩ ≠ 1 := fun h =>
          ha1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
        have h4 : f ⟨b, hb⟩ ≠ 1 := fun h =>
          hb1 (congrArg Subtype.val (f.injective (h.trans (map_one f).symm)))
        exact congrArg Subtype.val (f.injective (hall _ _ h1 h2 h3 h4))
      rcases hT with hT | hT
      · obtain ⟨f⟩ := hT
        exact key f (by decide)
      · obtain ⟨f⟩ := hT
        exact key f (by decide)
    intro x hx hx2 hx1
    exact S152N.involution_mem_of_normal hsyl hM0le hnorm huniq hu hu2 hu1 hx hx2 hx1

theorem nonThree_main (h : Data T Mc M) (h113 : StageLemma14113) {n : ℕ} [NeZero n]
    [Fact n.Prime] (hn : Odd n) (e : ↥(mBar0 T Mc M) ≃* DihedralGroup n)
    (hinv : ∀ x ∈ autOn T (V154 T Mc M), x ^ 2 = 1 → x ≠ 1 → x ∈ mBar0 T Mc M) :
    Nat.card (oTwoUpper (mBar0 T Mc M)) = n ∧
      autOn (yOf152 T Mc M) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) ∧
      autOn (yOf152 T Mc M) (V154 T Mc M) =
        ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ ∧
      Ys T Mc M ⊓ (piStar h).ker = ⊥ ∧
      yOf152 T Mc M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ pCoreOf 2 M := by
  obtain ⟨hcardE, -, hinvD⟩ := dihedral_shape hn e
  set Eb : Subgroup (MulAut (V154 T Mc M)) := oTwoUpper (mBar0 T Mc M) with hEb
  have hEodd : Odd (Nat.card Eb) := by rw [hcardE]; exact hn
  have hEcyc : IsCyclic ↥Eb := isCyclic_of_prime_card hcardE
  have hEab : ∀ a ∈ Eb, ∀ b ∈ Eb, a * b = b * a := fun a ha b hb => by
    have := mul_comm' (⟨a, ha⟩ : ↥Eb) ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hRb : autOn (rcOf Mc M) (V154 T Mc M) ≠ ⊥ := lemma_14_1_17_one h113 h.qtfe h.hyp
  have hRV : rcOf Mc M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := h.rc_le_M.trans h.hMV
  have hR2 : IsPGroup 2 (autOn (rcOf Mc M) (V154 T Mc M)) :=
    isPGroup_autOn (rc_isPGroup Mc M) hRV
  obtain ⟨b, hbR, hb1, hb2⟩ := exists_involution_of_ne_bot hR2 hRb
  have hbT : b ∈ autOn T (V154 T Mc M) := A4.autOn_mono h.rc_le_T hbR
  have hbM0 : b ∈ mBar0 T Mc M := hinv b hbT hb2 hb1
  have hbinv : ∀ a ∈ Eb, b * a * b⁻¹ = a⁻¹ :=
    hinvD b hbM0 (orderOf_eq_prime hb2 hb1)
  have hY : autOn (yOf152 T Mc M) (V154 T Mc M) =
      ⁅Eb, autOn (rcOf Mc M) (V154 T Mc M)⁆ := by
    have hodd0 : Odd (Nat.card (autOn (y0Of T Mc M) (V154 T Mc M))) := by
      rw [h.autOn_y0Of]; exact hEodd
    have := lemma_14_1_17_two h.qtfe h.hyp (y0Of_le T Mc M) h.T_le_normalizer_y0Of hodd0
    rw [h.autOn_y0Of] at this
    exact this
  have hRbE : autOn (rcOf Mc M) (V154 T Mc M) ≤ Subgroup.normalizer (Eb : Set (MulAut (V154 T Mc M))) :=
    ((A4.autOn_mono h.rc_le_M).trans (mBar0_normalizer T Mc M)).trans
      (normalizer_le_normalizer_oTwoUpper _)
  have hYE : ⁅Eb, autOn (rcOf Mc M) (V154 T Mc M)⁆ = Eb := by
    apply le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hRbE)
    intro ε hε
    set ε' := ε ^ ((n + 1) / 2) with hε'
    have hε'E : ε' ∈ Eb := Eb.pow_mem hε _
    have hεn : ε ^ n = 1 := by
      have : (⟨ε, hε⟩ : ↥Eb) ^ Nat.card Eb = 1 := pow_card_eq_one'
      rw [hcardE] at this
      simpa using congrArg Subtype.val this
    have h1 : b * ε'⁻¹ * b⁻¹ = ε' := by
      rw [hbinv _ (Eb.inv_mem hε'E), inv_inv]
    have h2 : ε' * ε' = ε := by
      obtain ⟨j, hj⟩ := hn
      have : (n + 1) / 2 = j + 1 := by omega
      rw [hε', this, ← pow_add, show j + 1 + (j + 1) = n + 1 by omega, pow_succ, hεn, one_mul]
    have key : ⁅ε', b⁆ = ε := by
      calc ⁅ε', b⁆ = ε' * (b * ε'⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
        _ = ε := by rw [h1, h2]
    rw [← key]
    exact Subgroup.commutator_mem_commutator hε'E hbR
  have hYb : autOn (yOf152 T Mc M) (V154 T Mc M) = Eb := hY.trans hYE
  have hab : ∀ a ∈ Ys T Mc M, ∀ b ∈ Ys T Mc M, a * b = b * a := by
    let f : ↥(Ys T Mc M) →* ↥Eb :=
      MonoidHom.codRestrict ((piStar h).comp (Ys T Mc M).subtype) Eb
        (fun u => Data.piStar_mem_of_mem_Ys h u.2)
    have hf : f.ker ≤ Subgroup.center ↥(Ys T Mc M) := by
      intro u hu
      rw [Subgroup.mem_center_iff]
      intro g
      have hu1 : piStar h (u : OTwoQuot M) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hu)
        simpa [f] using this
      have hmem : (u : OTwoQuot M) ∈ Ys T Mc M ⊓ (piStar h).ker := ⟨u.2, hu1⟩
      exact Subtype.ext (Data.K_central h _ hmem (g : OTwoQuot M) (Data.Ys_le_Ls h g.2))
    intro a ha b hb
    have : IsMulCommutative ↥(Ys T Mc M) := MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center f hf
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥(Ys T Mc M)) ⟨b, hb⟩)
  have hK : Ys T Mc M ⊓ (piStar h).ker = ⊥ := Data.K_eq_bot_of_abelian h hEodd hab
  refine ⟨hcardE, hYb, ?_, hK, yOf_inf_centralizer_le h hK⟩
  calc autOn (yOf152 T Mc M) (V154 T Mc M) = Eb := hYb
    _ = ⁅Eb, autOn (rcOf Mc M) (V154 T Mc M)⁆ := hYE.symm
    _ = ⁅autOn (yOf152 T Mc M) (V154 T Mc M), autOn (rcOf Mc M) (V154 T Mc M)⁆ := by rw [hYb]

end Main

end S152Y

end CFSG.Quasithin
