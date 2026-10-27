module

public import CFSG.Adapters.RankTwoModelTransports
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalEvenLinearSource
public import CFSG.Quasithin.SteinbergCDUnitaryThreeSylowSixteen

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly.LowTwoRank

namespace Z2D8Facts

theorem pow_four (x : Multiplicative (ZMod 2) × DihedralGroup 4) : x ^ 4 = 1 := by
  revert x
  decide

theorem not_comm :
    ¬ ∀ x y : Multiplicative (ZMod 2) × DihedralGroup 4, x * y = y * x := by
  decide

theorem card : Nat.card (Multiplicative (ZMod 2) × DihedralGroup 4) = 16 := by
  rw [Nat.card_prod, DihedralGroup.nat_card]
  simp

theorem not_dihedral_pow_equiv {m : ℕ} (hm : 2 ^ m = 8)
    (g : DihedralGroup (2 ^ m) ≃* Multiplicative (ZMod 2) × DihedralGroup 4) : False := by
  have h := pow_four (g (DihedralGroup.r 1))
  rw [← map_pow] at h
  have h1 : (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ 4 = 1 :=
    g.injective (h.trans (map_one g).symm)
  have := orderOf_dvd_of_pow_eq_one h1
  rw [DihedralGroup.orderOf_r_one, hm] at this
  omega

end Z2D8Facts

@[expose] def NoSylowZ2D8 (S : Type) [Group S] : Prop :=
  ∀ P : Sylow 2 S, ¬ Nonempty (↥(P : Subgroup S) ≃* Multiplicative (ZMod 2) × DihedralGroup 4)

namespace NoSylowZ2D8

theorem exists_sylow_mulEquiv {A B : Type*} [Group A] [Finite A] [Group B] (ψ : A ≃* B)
    (Q : Sylow 2 A) :
    ∃ Q' : Sylow 2 B, Nonempty (↥(Q : Subgroup A) ≃* ↥(Q' : Subgroup B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Q.mapSurjective (f := ψ.toMonoidHom) ψ.surjective, ⟨?_⟩⟩
  exact ((Q : Subgroup A).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
    (MulEquiv.subgroupCongr (Sylow.coe_mapSurjective _ _).symm)

theorem of_mulEquiv {S T : Type} [Group S] [Finite S] [Group T] (e : S ≃* T)
    (h : NoSylowZ2D8 T) : NoSylowZ2D8 S := by
  rintro P ⟨f⟩
  obtain ⟨Q, ⟨ι⟩⟩ := exists_sylow_mulEquiv e P
  exact h Q ⟨ι.symm.trans f⟩

end NoSylowZ2D8

theorem noSylowZ2D8_of_orderOf_eq_eight {S : Type} [Group S] [Finite S] {a : S}
    (ha : orderOf a = 8) : NoSylowZ2D8 S := by
  rintro P ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 3) (by rw [Nat.card_zpowers, ha]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  let g : ↥(Q : Subgroup S) ≃* Multiplicative (ZMod 2) × DihedralGroup 4 :=
    (Sylow.equiv Q P).trans e
  let a' : ↥(Q : Subgroup S) := ⟨a, hQ (Subgroup.mem_zpowers a)⟩
  have h4 : a' ^ 4 = 1 := g.injective (by rw [map_pow, map_one]; exact Z2D8Facts.pow_four _)
  have h4' : a ^ 4 = 1 := congrArg Subtype.val h4
  have := orderOf_dvd_of_pow_eq_one h4'
  rw [ha] at this
  omega

theorem noSylowZ2D8_of_card_eq {S : Type} [Group S] [Finite S] {a : ℕ} (ha : a ≠ 4)
    (hS : ∃ m : ℕ, Odd m ∧ Nat.card S = 2 ^ a * m) : NoSylowZ2D8 S := by
  rintro P ⟨e⟩
  obtain ⟨m, hm, hS⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(P : Subgroup S) = 2 ^ (Nat.card S).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : (Nat.card S).factorization 2 = a := by
    rw [hS, Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by simpa [even_iff_two_dvd] using hm.not_two_dvd_nat)]
    simp
  rw [h2, Nat.card_congr e.toEquiv, Z2D8Facts.card] at h1
  have : (2 : ℕ) ^ 4 = 2 ^ a := by rw [← h1]; norm_num
  exact ha (Nat.pow_right_injective le_rfl this).symm

theorem noSylowZ2D8_of_card_eq_of_two_part {S : Type} [Group S] [Finite S] {m N : ℕ}
    (hS : Nat.card S = m) (hm : ∃ r : ℕ, Odd r ∧ m = 2 ^ N * r) (hN : N ≠ 4) :
    NoSylowZ2D8 S := by
  obtain ⟨r, hr, hmr⟩ := hm
  exact noSylowZ2D8_of_card_eq hN ⟨r, hr, hS.trans hmr⟩

theorem noSylowZ2D8_of_two_part_sixteen {S : Type} [Group S] [Finite S]
    (h : 2 ^ (Nat.card S).factorization 2 = 16 → ∃ a : S, orderOf a = 8) : NoSylowZ2D8 S := by
  intro P hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card ↥(P : Subgroup S) = 2 ^ (Nat.card S).factorization 2 :=
    Sylow.card_eq_multiplicity P
  have h2 : Nat.card ↥(P : Subgroup S) = 16 := (Nat.card_congr hP.some.toEquiv).trans Z2D8Facts.card
  obtain ⟨a, ha⟩ := h (h1.symm.trans h2)
  exact noSylowZ2D8_of_orderOf_eq_eight ha P hP

theorem noSylowZ2D8_of_alternating {S : Type} [Group S] [Finite S] {n : ℕ} (h5 : 5 ≤ n)
    (h8 : n ≤ 8) (e : S ≃* alternatingGroup (Fin n)) : NoSylowZ2D8 S := by
  have hc : Nat.card S = Nat.card (alternatingGroup (Fin n)) := Nat.card_congr e.toEquiv
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup] at hc
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hc
  interval_cases n
  · exact noSylowZ2D8_of_card_eq (a := 2) (by norm_num) ⟨15, by decide, by rw [hc]; decide⟩
  · exact noSylowZ2D8_of_card_eq (a := 3) (by norm_num) ⟨45, by decide, by rw [hc]; decide⟩
  · exact noSylowZ2D8_of_card_eq (a := 3) (by norm_num) ⟨315, by decide, by rw [hc]; decide⟩
  · exact noSylowZ2D8_of_card_eq (a := 6) (by norm_num) ⟨315, by decide, by rw [hc]; decide⟩

theorem noSylowZ2D8_of_psl_two_odd {S : Type} [Group S] [Finite S] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSL 2 p f) : NoSylowZ2D8 S := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hK⟩
  let ε : S ≃* CFSG.GorensteinWalter.PSL2 K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  refine NoSylowZ2D8.of_mulEquiv ε ?_
  rintro Q ⟨φ⟩
  obtain ⟨m, -, ⟨d⟩⟩ := CFSG.GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model K hodd Q
  let g : DihedralGroup (2 ^ m) ≃* Multiplicative (ZMod 2) × DihedralGroup 4 := d.symm.trans φ
  have hc := Nat.card_congr g.toEquiv
  rw [DihedralGroup.nat_card, Z2D8Facts.card] at hc
  have h8 : 2 ^ m = 8 := by omega
  exact Z2D8Facts.not_dihedral_pow_equiv h8 g

theorem noSylowZ2D8_of_psl_two_even {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : StatedClassicalModel S .PSL 2 2 f) : NoSylowZ2D8 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ε⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField S 2 2 f h
  refine NoSylowZ2D8.of_mulEquiv ε ?_
  rintro Q ⟨g⟩
  obtain ⟨hab, -⟩ := CFSG.Walter.psl2_even_sylow_two hf Q
  refine Z2D8Facts.not_comm fun x y => ?_
  have := hab.toIsMulCommutative.is_comm.comm (g.symm x) (g.symm y)
  have h2 := congrArg g this
  simpa using h2

theorem noSylowZ2D8_of_psl_three_odd {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSL 3 p 1) : NoSylowZ2D8 S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hodd : Odd (Nat.card K) := by rw [hK, pow_one]; exact hp.odd_of_ne_two hp2
  let ε : S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.trans (CFSG.ComponentClassification.SymmetricLocal.statedProjEquivProjectiveSL 3 K)
  refine noSylowZ2D8_of_two_part_sixteen fun h16 => ?_
  rw [Nat.card_congr ε.toEquiv] at h16
  obtain ⟨a, -, ha, -, -⟩ := (CFSG.Quasithin.SteinbergCD.projectiveSL_three_two_part hodd).2 h16
  exact ⟨ε.symm a, by rw [MulEquiv.orderOf_eq]; exact ha⟩

theorem noSylowZ2D8_of_psu_three_odd {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : StatedClassicalModel S .PSU 3 p 1) : NoSylowZ2D8 S := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 K :=
    ⟨hp, le_rfl, by rw [hK]; ring⟩
  let ε : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (by norm_num)).symm
  refine noSylowZ2D8_of_two_part_sixteen fun h16 => ?_
  rw [Nat.card_congr ε.toEquiv] at h16
  obtain ⟨a, -, ha, -, -⟩ := (CFSG.Quasithin.SteinbergCD.unitaryPSU_three_two_part hU hp2).2 h16
  exact ⟨ε.symm a, by rw [MulEquiv.orderOf_eq]; exact ha⟩

theorem noSylowZ2D8_of_psl_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSL n 2 f) (hN : f * ((n - 1) * (n - 1 + 1) / 2) ≠ 4) :
    NoSylowZ2D8 S := by
  obtain ⟨-, hf, hn, -, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordA (by omega) hf).two hN

theorem noSylowZ2D8_of_psu_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSU n 2 f) (hN : f * ((n - 1) * (n - 1 + 1) / 2) ≠ 4) :
    NoSylowZ2D8 S := by
  obtain ⟨-, hf, hn, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordTwistedA (by omega) hf).two hN

theorem noSylowZ2D8_of_psp_char_two {S : Type} [Group S] [Finite S] {n f : ℕ}
    (h : StatedClassicalModel S .PSp n 2 f) (hN : f * (n * n) ≠ 4) : NoSylowZ2D8 S := by
  obtain ⟨-, hf, -⟩ := h.1
  have hcard := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  exact noSylowZ2D8_of_card_eq_of_two_part hcard
    (CFSG.Timmesfeld.Orders.profile_ordBC hf).two hN

end CFSG.Quasithin.F6
