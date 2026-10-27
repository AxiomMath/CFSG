module

public import CFSG.Quasithin.EmptyFaithful.S153QPD1
public import CFSG.Quasithin.EmptyFaithful.A38cAutOn

public section

namespace CFSG.Quasithin.QP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin

theorem not_dvd_four_pow_sub_one {n b : ℕ} (hn : 3 ≤ n) : ¬ (4 ^ n - 1) ∣ 2 ^ b * 60 := by
  intro h
  have hodd : Odd (4 ^ n - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by norm_num)) (Nat.even_pow.2 ⟨by decide, by omega⟩) odd_one
  have hco : Nat.Coprime (4 ^ n - 1) (2 ^ b * 4) := by
    have h2 : Nat.Coprime 2 (4 ^ n - 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd.not_two_dvd_nat
    have h3 : Nat.Coprime (2 ^ (b + 2)) (4 ^ n - 1) := Nat.Coprime.pow_left (b + 2) h2
    have h4 : 2 ^ b * 4 = 2 ^ (b + 2) := by ring
    rw [h4]
    exact h3.symm
  have h15 : (4 ^ n - 1) ∣ 15 := by
    have h1 : 2 ^ b * 60 = (2 ^ b * 4) * 15 := by ring
    rw [h1] at h
    exact hco.dvd_of_dvd_mul_left h
  have hle := Nat.le_of_dvd (by norm_num) h15
  have h64 : 64 ≤ 4 ^ n :=
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem four_pow_sub_one_dvd_card_sl3 {n : ℕ} (hn : 1 ≤ n) (hFn : Nat.card F = 2 ^ n) :
    (4 ^ n - 1) ∣ Nat.card (SpecialLinearGroup (Fin 3) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hq : Fintype.card F = 2 ^ n := by rw [← Nat.card_eq_fintype_card]; exact hFn
  have h1 : Nat.card (SpecialLinearGroup (Fin 3) F) * Nat.card Fˣ = Nat.card (GL (Fin 3) F) :=
    Matrix.card_SL_mul_card_units
  have h2 : Nat.card (GL (Fin 3) F) =
      ∏ i : Fin 3, (Fintype.card F ^ 3 - Fintype.card F ^ (i : ℕ)) := Matrix.card_GL_field 3
  rw [Nat.card_units, hFn, h2, Fin.prod_univ_three, hq] at h1
  set q := 2 ^ n with hqdef
  have hq2 : 2 ≤ q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have e1 : (q ^ 3 - q ^ ((0 : Fin 3) : ℕ)) * (q ^ 3 - q ^ ((1 : Fin 3) : ℕ)) *
      (q ^ 3 - q ^ ((2 : Fin 3) : ℕ)) = (q - 1) * (q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1)) := by
    have hq1 : 1 ≤ q := by omega
    have a1 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
    have a2 : q ≤ q ^ 3 := by
      calc q = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have a3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have a4 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
    zify [a1, a2, a3, a4, hq1]
    ring
  rw [e1] at h1
  have hpos : 0 < q - 1 := by omega
  have h3 : Nat.card (SpecialLinearGroup (Fin 3) F) = q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have := h1
    rw [mul_comm] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h4 : q ^ 2 = 4 ^ n := by rw [hqdef, ← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h3, h4]
  exact ⟨q ^ 3 * (q ^ 3 - 1), by ring⟩

omit [CharP F 2] in
theorem false_of_unitriangular_normalizes_sl3 {n : ℕ} (hn3 : 3 ≤ n) (hFn : Nat.card F = 2 ^ n)
    {X : Subgroup (SpecialLinearGroup (Fin 3) F)}
    (hN : unitriangular 3 F ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 3) F)))
    {N : Type} [Group N] [Finite N] [IsSimpleGroup N] (hN60 : Nat.card N = 60)
    (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperfN : Group.IsPerfect N := isPerfect_of_simple_card_sixty hN60
  have hK2 : ∃ k : ℕ, Nat.card F = 2 ^ k := ⟨n, hFn⟩
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    have h4 : 4 ≤ Nat.card F := by
      rw [hFn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F))
      (by simpa [Nat.card_eq_fintype_card] using h4)
    exact ⟨s, hs⟩
  set U := unitriangular 3 F with hU
  have hUp : IsPGroup 2 U :=
    IsPGroup.of_card (n := n * (3 * (3 - 1) / 2)) (by rw [hU, card_unitriangular, hFn, pow_mul])
  set A := X ⊔ U with hA
  have hAN : A ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin 3) F)) :=
    sup_le Subgroup.le_normalizer hN
  have : Group.IsPerfect (SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
  by_cases hAtop : A = ⊤
  · have hX : X = ⊤ := eq_top_of_sup_isPGroup_of_isPerfect hUp hN hAtop
    have hφ : Function.Surjective X.subtype := fun g => ⟨⟨g, hX ▸ Subgroup.mem_top g⟩, rfl⟩
    obtain ⟨b, hb⟩ := card_dvd_two_pow_mul_of_surjective X.subtype hφ θ hθ hk hN60
    exact not_dvd_four_pow_sub_one hn3 ((four_pow_sub_one_dvd_card_sl3 (by omega) hFn).trans hb)
  · have hXns : ¬ Group.IsSolvable ↥X := fun hs =>
      not_isSolvable_of_simple_card_sixty hN60 (Group.isSolvable_of_surjective hθ)
    have hAns : ¬ Group.IsSolvable ↥A := fun hs =>
      hXns (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (le_sup_left : X ≤ A))
        (Subgroup.inclusion_injective _))
    have key : ∀ j : Fin 2, A ≤ Q3 F j → False := by
      intro j hj
      have hB := isSolvable_upperTriangular (n := 3) hK2
      have hH3 : H3 F j ≤ A := H3_le_of_nonsolvable hB j le_sup_right hj hAns
      have hpc : perfectCore (Q3 F j) ≤ A :=
        calc perfectCore (Q3 F j) = ⁅perfectCore (Q3 F j), perfectCore (Q3 F j)⁆ :=
              (perfectCore_perfect _).symm
          _ ≤ ⁅Q3 F j, Q3 F j⁆ := Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
          _ ≤ H3 F j := commutator_Q3_le j
          _ ≤ A := hH3
      set P := perfectCore X with hP
      have hPX : P ≤ X := perfectCore_le X
      have hPperf : ⁅P, P⁆ = P := perfectCore_perfect X
      have hPC : P ≤ perfectCore (Q3 F j) :=
        le_perfectCore_of_perfect (hPX.trans (le_sup_left.trans hj)) hPperf
      have hPN : ∀ a ∈ A, ∀ p, p ∈ P ↔ a * p * a⁻¹ ∈ P := fun a ha p =>
        Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_perfectCore X (hAN ha)) p
      have hmapP : (perfectCore (⊤ : Subgroup ↥X)).map θ = ⊤ := by
        rw [map_perfectCore, Subgroup.map_top_of_surjective θ hθ]
        exact perfectCore_eq_self_of_perfect (by
          have := Group.isPerfect_def.1 hperfN
          rwa [commutator_def] at this)
      have hmapX : (perfectCore (⊤ : Subgroup ↥X)).map X.subtype = P := by
        rw [map_perfectCore, Subgroup.map_top, Subgroup.range_subtype]
      let θP : ↥P →* N := θ.comp (Subgroup.inclusion hPX)
      have hθP : Function.Surjective θP := by
        intro m
        have hm : m ∈ (perfectCore (⊤ : Subgroup ↥X)).map θ := by rw [hmapP]; trivial
        obtain ⟨p', hp', rfl⟩ := hm
        have hp'P : (p' : SpecialLinearGroup (Fin 3) F) ∈ P := by
          rw [← hmapX]; exact ⟨p', hp', rfl⟩
        exact ⟨⟨p', hp'P⟩, rfl⟩
      have hkP : IsPGroup 2 θP.ker := by
        intro z
        have hz : Subgroup.inclusion hPX (z : ↥P) ∈ θ.ker := z.2
        obtain ⟨k, hk'⟩ := hk ⟨_, hz⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have h1 := congrArg Subtype.val (congrArg Subtype.val hk')
        simpa using h1
      have hK4' := hK4
      set C := perfectCore (Q3 F j) with hC
      set Bp : Subgroup (SpecialLinearGroup (Fin 2) F) := (P.subgroupOf C).map (blk3 j) with hBp
      have hBpn : Bp.Normal := by
        refine ⟨fun b hb h => ?_⟩
        obtain ⟨p', hp', rfl⟩ := hb
        obtain ⟨c, rfl⟩ := blk3_surjective hK4 j h
        refine ⟨c * p' * c⁻¹, ?_, by simp⟩
        have hcA : ((c : ↥C) : SpecialLinearGroup (Fin 3) F) ∈ A := hpc c.2
        have hp'P : ((p' : ↥C) : SpecialLinearGroup (Fin 3) F) ∈ P := hp'
        show ((c * p' * c⁻¹ : ↥C) : SpecialLinearGroup (Fin 3) F) ∈ P
        simpa using (hPN _ hcA _).1 hp'P
      have hsimp : IsSimpleGroup (SpecialLinearGroup (Fin 2) F) := by
        let _ := Fintype.ofFinite F
        exact isSimpleGroup_sl_two_pow (n := n) (by omega)
          (by rw [← Nat.card_eq_fintype_card]; exact hFn)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Bp with h | h
      ·
        have hPU : P ≤ U := by
          intro p hp
          have hpC : p ∈ C := hPC hp
          have hb : blk3 j ⟨p, hpC⟩ ∈ Bp := ⟨⟨p, hpC⟩, hp, rfl⟩
          rw [h, Subgroup.mem_bot] at hb
          exact blk3_ker j ⟨p, hpC⟩ hb
        have hP2 : IsPGroup 2 ↥P := hUp.to_le hPU
        exact not_isPGroup_two_of_card_sixty hN60 (IsPGroup.of_surjective hP2 θP hθP)
      · let ψ : ↥P →* SpecialLinearGroup (Fin 2) F := (blk3 j).comp (Subgroup.inclusion hPC)
        have hψ : Function.Surjective ψ := by
          intro h'
          have hb : h' ∈ Bp := by rw [h]; trivial
          obtain ⟨p', hp', rfl⟩ := hb
          exact ⟨⟨(p' : SpecialLinearGroup (Fin 3) F), hp'⟩, rfl⟩
        obtain ⟨b, hb⟩ := card_dvd_two_pow_mul_of_surjective ψ hψ θP hθP hkP hN60
        have hcard : Nat.card (SpecialLinearGroup (Fin 2) F) = 2 ^ n * (4 ^ n - 1) :=
          CFSG.Quasithin.Vol2.Ch10.SecA.card_SL_two_pow hFn
        rw [hcard] at hb
        exact not_dvd_four_pow_sub_one hn3 ((Dvd.intro_left _ rfl).trans hb)
    rcases contained_in_Q3 (le_sup_right : U ≤ A) hAtop with h | h
    exacts [key 0 h, key 1 h]

end CFSG.Quasithin.QP
