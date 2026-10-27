module

public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorLinearInvolutions

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open scoped MatrixGroups

noncomputable def sl2RingEquiv' {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map e.toRingHom)
    (Matrix.SpecialLinearGroup.map e.symm.toRingHom) (by ext A i j; simp) (by ext A i j; simp)

theorem sl2_eq_top_of_sylow_le
    {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2 ^ m) (S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F))
    {Q : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)} (hSQ : (S : Subgroup _) ≤ Q)
    (hQ : ¬ Group.IsSolvable Q) : Q = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hc : Fintype.card F = Fintype.card (GaloisField 2 m) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 m (by omega)]
  let e1 := sl2RingEquiv' (FiniteField.ringEquivOfCardEq hc)
  let e2 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m) ≃* PSL(2, GaloisField 2 m) :=
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.psl2CharTwoEquivSL).symm
  let e := e1.trans e2
  let U : Sylow 2 PSL(2, GaloisField 2 m) := S.mapSurjective (f := e.toMonoidHom) e.surjective
  by_contra hne
  have hY : Q.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hne
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ Q.map e.toMonoidHom := by rw [htop]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← e.injective hyx]
    exact hy
  have hUQ : (U : Subgroup PSL(2, GaloisField 2 m)) ≤ Q.map e.toMonoidHom :=
    Subgroup.map_mono hSQ
  exact hQ (CFSG.Walter.isSolvable_map_mulEquiv e Q
    (CFSG.Walter.psl2_even_isSolvable_of_sylow_le hm U hUQ hY))

theorem psl2_prime_eq_top_or_alt5
    {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    {Q : Subgroup PSL(2, ZMod p)} (hQ : ¬ Group.IsSolvable Q) :
    Q = ⊤ ∨ Nonempty (Q ≃* alternatingGroup (Fin 5)) := by
  classical
  have hFc : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hcardL : Nat.card PSL(2, ZMod p) = p * (p ^ 2 - 1) / 2 := by
    have := CFSG.GorensteinWalter.psl2_card_formula (ZMod p)
      (CFSG.Walter.isOddPrimePower_of_card hFc hodd one_pos)
    rwa [Nat.card_zmod] at this
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFc Q with
    hEl | ⟨z, -, -, hcyc⟩ | ⟨z, -, hYz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, he⟩ |
      ⟨m, s, -, -, N, C, hN, hNel, -, hCcyc, -, -, hsup⟩ | ⟨m, hm, hmf, ⟨e⟩⟩ | ⟨m, hm, hmf, -⟩
  · exact absurd (Group.isSolvable_of_comm fun a b => hEl.toIsMulCommutative.is_comm.comm a b) hQ
  · exfalso
    let : CommGroup Q := IsCyclic.commGroup
    exact hQ inferInstance
  · exfalso
    have : NeZero z := ⟨fun hz0 => by
      rw [hz0, mul_zero] at hYz
      exact Nat.card_pos.ne' hYz⟩
    have := CFSG.Walter.isSolvable_dihedralGroup' z
    exact hQ (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · exfalso
    have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact hQ (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · exfalso
    have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hQ (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective)
  · exact Or.inr he
  · exfalso
    have : N.Normal := hN
    let : CommGroup C := IsCyclic.commGroup
    exact hQ (CFSG.Walter.isSolvable_of_sup_eq_top hNel.toIsMulCommutative
      ⟨⟨fun a b => mul_comm a b⟩⟩ hsup)
  · left
    have hm1 : m = 1 := Nat.eq_one_of_dvd_one hmf |>.symm ▸ rfl
    subst hm1
    have hGc : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
    have hcQ : Nat.card Q = p * (p ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv]
      have := CFSG.GorensteinWalter.psl2_card_formula (GaloisField p 1)
        (CFSG.Walter.isOddPrimePower_of_card hGc hodd one_pos)
      rwa [hGc, pow_one] at this
    exact Subgroup.eq_top_of_card_eq Q (hcQ.trans hcardL.symm)
  · exfalso
    have : 2 * m ≤ 1 := Nat.le_of_dvd one_pos hmf
    omega

theorem isSolvable_psl2_three : Group.IsSolvable PSL(2, ZMod 3) := by
  have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
  exact Group.isSolvable_of_surjective
    (f := CFSG.GorensteinWalter.psl2_three_equiv_alternatingGroup.symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem nonempty_sl2_equiv_psl2 {F : Type} [Field F] [Finite F] {m : ℕ} (hm : 1 ≤ m)
    (hF : Nat.card F = 2 ^ m) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) F ≃* PSL(2, GaloisField 2 m)) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hc : Fintype.card F = Fintype.card (GaloisField 2 m) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF,
      GaloisField.card 2 m (by omega)]
  exact ⟨(sl2RingEquiv' (FiniteField.ringEquivOfCardEq hc)).trans
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.psl2CharTwoEquivSL).symm⟩

theorem isSimpleGroup_of_sl2 {Y : Type*} [Group Y] {F : Type} [Field F] [Finite F] {m : ℕ}
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) :
    IsSimpleGroup Y := by
  obtain ⟨e'⟩ := nonempty_sl2_equiv_psl2 (by omega) hF
  have hc : 4 ≤ Nat.card (GaloisField 2 m) := by
    rw [GaloisField.card 2 m (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : IsSimpleGroup PSL(2, GaloisField 2 m) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hc
  have : Nontrivial Y := (e.trans e').toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective (e.trans e').symm.toMonoidHom
    (MulEquiv.surjective _)

theorem two_dvd_card_of_sl2 {Y : Type*} [Group Y] {F : Type} [Field F] [Finite F] {m : ℕ}
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 2) F) (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m) :
    2 ∣ Nat.card Y := by
  obtain ⟨e'⟩ := nonempty_sl2_equiv_psl2 hm hF
  rw [Nat.card_congr (e.trans e').toEquiv, CFSG.Walter.psl2_even_card (by omega)]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _

theorem isSimpleGroup_of_psl2 {Y : Type*} [Group Y] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (e : Y ≃* PSL(2, ZMod p)) : IsSimpleGroup Y := by
  have : IsSimpleGroup PSL(2, ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [Nat.card_zmod]; omega)
  have : Nontrivial Y := e.toEquiv.nontrivial
  exact IsSimpleGroup.isSimpleGroup_of_surjective e.symm.toMonoidHom (MulEquiv.surjective _)

theorem two_dvd_card_of_psl2 {Y : Type*} [Group Y] {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (e : Y ≃* PSL(2, ZMod p)) : 2 ∣ Nat.card Y := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hFc : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hcardL := CFSG.GorensteinWalter.psl2_card_formula (ZMod p)
    (CFSG.Walter.isOddPrimePower_of_card hFc hodd one_pos)
  rw [Nat.card_zmod] at hcardL
  rw [Nat.card_congr e.toEquiv, hcardL]
  obtain ⟨k, hk⟩ := Nat.eight_dvd_sq_sub_one_of_odd hodd
  rw [hk]
  exact ⟨2 * p * k, by rw [show p * (8 * k) = 2 * (2 * (2 * p * k)) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]⟩

end CFSG.Quasithin.Vol2.Ch10.SecD
