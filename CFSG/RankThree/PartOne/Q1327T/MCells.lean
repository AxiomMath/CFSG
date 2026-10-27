module

public import CFSG.RankThree.PartOne.Q1327C.BFinal
public import CFSG.RankThree.PartOne.Q1327C.BL4
public import CFSG.RankThree.PartOne.Q1327C.BU5b
public import CFSG.RankThree.PartOne.Q1327C.BOm8
public import CFSG.RankThree.PartOne.Q1327T.MInv
public import CFSG.RankThree.PartOne.CTP.SpinRankFour
public import CFSG.RankThree.PartOne.Q1327C.BClassify
public import CFSG.RankThree.PartOne.Q1327C.BSp6
public import CFSG.RankThree.PartTwo.Census.Exceptional.Main
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327C

@[expose] def KF1327BM : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (X A₀ F : Subgroup G), Q1327.T123Base p X A₀ F →
    Census3.TheoremThreeList (↥X ⧸ Subgroup.center ↥X) →
    CFSG.Blueprint.EvenLieType (↥X ⧸ Subgroup.center ↥X) →
    Group.IsSolvable ↥(torusImage F X) →
    (∀ φ ∈ torusImage F X, ∃ f : F, φ f ≠ f⁻¹) →
    (∀ B : Subgroup G, B ≤ F → torusInvariant F X B → B = ⊥ ∨ B = F) →
    (∃ (t : MulAut F) (K : Subgroup G) (f : ℕ), t ∈ torusImage F X ∧ IsAutReflection p F t ∧
      K ≤ X ⊓ Subgroup.centralizer (autFixedInG F t : Set G) ∧
      K.subgroupOf (X ⊓ Subgroup.centralizer (autFixedInG F t : Set G)) ∈
        thetaComponents p ↥(X ⊓ Subgroup.centralizer (autFixedInG F t : Set G)) ∧
      autMovedInG F t ≤ K ∧ StatedClassicalModel ↥K .PSL 2 2 f ∧ 2 ≤ f ∧ p ∣ 2 ^ f + 1) →
    ∃ f' : ℕ, 1 ≤ f' ∧ p ∣ 2 ^ f' + 1 ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSU 4 2 f'

section Rows

variable {G : Type} [Group G] {p : ℕ} {X F : Subgroup G}

theorem false_of_weyl_rowM (hcomm : ∀ a b : F, a * b = b * a)
    (hirr : ∀ B : Subgroup G, B ≤ F → torusInvariant F X B → B = ⊥ ∨ B = F)
    (hneg : ∀ φ ∈ torusImage F X, ∃ f : F, φ f ≠ f⁻¹)
    (hsolv : Group.IsSolvable ↥(torusImage F X)) {r : ℕ} (hr : r = 10 ∨ r = 12)
    (hd : RowData p X F r) : False := by
  have h2 := hd.2.2.1
  rcases hr with rfl | rfl
  · obtain ⟨e⟩ := h2
    let z0 : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4) := (Multiplicative.ofAdd 1, 1)
    have hz0sq : z0 * z0 = 1 := by decide
    have hz01 : z0 ≠ 1 := by decide
    have hz0c : ∀ x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), x * z0 = z0 * x := by decide
    let z : ↥(torusImage F X) := e.symm z0
    have hz2 : (z : MulAut F) * (z : MulAut F) = 1 := by
      have : z * z = 1 := e.injective (by rw [map_mul, MulEquiv.apply_symm_apply, hz0sq, map_one])
      exact congrArg Subtype.val this
    have hz1 : (z : MulAut F) ≠ 1 := fun h1 => hz01 (by
      have : z = 1 := Subtype.ext h1
      have h3 := congrArg e this
      rwa [MulEquiv.apply_symm_apply, map_one] at h3)
    have hcen : ∀ g ∈ torusImage F X, g * (z : MulAut F) = (z : MulAut F) * g := by
      intro g hg
      have : (⟨g, hg⟩ : ↥(torusImage F X)) * z = z * ⟨g, hg⟩ := e.injective (by
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hz0c _)
      exact congrArg Subtype.val this
    have hinv := eq_inv_of_central_involution hcomm hirr hz2 hz1 hcen
    obtain ⟨f, hf⟩ := hneg z z.2
    exact hf (hinv f)
  · obtain ⟨e⟩ := h2
    have hs : Group.IsSolvable (Equiv.Perm (Fin 5)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact Equiv.Perm.not_isSolvable_fin_5 hs

end Rows

section Sp6

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.RankThree.PartTwo.Census

variable {G : Type} [Group G] [Finite G]

theorem false_of_sp6_splitM {p : ℕ} {X A₀ F : Subgroup G} (h : Q1327.T123Base p X A₀ F)
    (hneg : ∀ φ ∈ torusImage F X, ∃ f : F, φ f ≠ f⁻¹)
    (hm : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .PSp 3 2 f) : False := by
  classical
  obtain ⟨f, hf1, hpq, hcl⟩ := hm
  have hcl' := hcl
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨e⟩⟩ := hcl'
  have hp := h.prime
  have hp5 := h.five_le
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by rw [Fintype.card_eq_nat_card]; exact hK)
  let N : Subgroup ↥(StatedSp 3 K) := (StatedScalars (Fin 3 ⊕ Fin 3) K).subgroupOf (StatedSp 3 K)
  have hN : N = ⊥ :=
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)
  let Ψ : (↥X ⧸ Subgroup.center ↥X) ≃* StatedSp 3 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot)
  have hordY : Nat.card (↥X ⧸ Subgroup.center ↥X) = CFSG.Open.ordBC 3 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hcl).2.2.1 rfl
  have hcardM : Nat.card (StatedSp 3 K) = CFSG.Open.ordBC 3 (2 ^ f) := by
    rw [← hordY]
    exact (Nat.card_congr Ψ.toEquiv).symm
  have hKu : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  have hrK : p ∣ Nat.card Kˣ := by rw [hKu]; exact hpq
  have hTcard : Nat.card (torus 3 K) = (2 ^ f - 1) ^ 3 := by
    have h1 : Nat.card (torus 3 K) = Nat.card (Fin 3 → Kˣ) :=
      (Nat.card_congr (MonoidHom.ofInjective (torusHom_injective (r := 3) (k := K))).toEquiv).symm
    rw [h1, Nat.card_fun, hKu, Nat.card_fin]
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hidx : ¬ p ∣ (torus 3 K).index := by
    apply not_dvd_index_of_val
    rw [hcardM, hTcard]
    have hpq1 : ¬ p ∣ 2 ^ f := by
      intro hd
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
      omega
    have hprod : CFSG.Open.ordBC 3 (2 ^ f) =
        (2 ^ f) ^ 9 * (((2 ^ f) ^ 2 - 1) * (((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1))) := by
      rw [CFSG.Open.ordBC, gcd_two_two_pow_sub_one hf1, Nat.div_one]
      have : Finset.Icc 1 3 = {1, 2, 3} := by decide
      rw [this, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
        Finset.prod_singleton]
    have hne1 : (2 ^ f - 1) ≠ 0 := by omega
    have hn2 : ∀ m : ℕ, 1 ≤ m → (2 ^ f) ^ m - 1 ≠ 0 := fun m hm1 => by
      have : 1 < (2 ^ f) ^ m := Nat.one_lt_pow (by omega) (by omega)
      omega
    have hnd2 : ¬ p ∣ 2 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hnd4 : ¬ p ∣ 4 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    have hnd6 : ¬ p ∣ 6 := fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases p
      · omega
      · exact absurd hp (by norm_num)
    have hvals : ∀ m : ℕ, 1 ≤ m → ¬ p ∣ m →
        padicValNat p ((2 ^ f) ^ m - 1) = padicValNat p (2 ^ f - 1) := fun m hm1 hmp => by
      have := padicValNat_pow_sub_one_eq (p := p) (q := 2 ^ f) (m := m) hp5 hq2 hpq hm1 hmp
      simpa using this
    have hv2 := hvals 2 (by norm_num) hnd2
    have hv4 := hvals 4 (by norm_num) hnd4
    have hv6 := hvals 6 (by norm_num) hnd6
    have hz : padicValNat p ((2 ^ f) ^ 9) = 0 := padicValNat.eq_zero_of_not_dvd (fun hd =>
      hpq1 (hp.dvd_of_dvd_pow hd))
    have hM : padicValNat p (CFSG.Open.ordBC 3 (2 ^ f)) = 3 * padicValNat p (2 ^ f - 1) := by
      rw [hprod, padicValNat.mul (pow_ne_zero 9 (by omega))
        (mul_ne_zero (hn2 2 (by omega)) (mul_ne_zero (hn2 4 (by omega)) (hn2 6 (by omega)))),
        padicValNat.mul (hn2 2 (by omega)) (mul_ne_zero (hn2 4 (by omega)) (hn2 6 (by omega))),
        padicValNat.mul (hn2 4 (by omega)) (hn2 6 (by omega)), hz, hv2, hv4, hv6]
      ring
    have hT : padicValNat p ((2 ^ f - 1) ^ 3) = 3 * padicValNat p (2 ^ f - 1) :=
      padicValNat.pow (2 ^ f - 1) 3
    rw [hM, hT]
  let E : Subgroup (↥X ⧸ Subgroup.center ↥X) := bar X F
  have hEel : IsElementaryAbelian p E := barF_elem h
  let Em : Subgroup (StatedSp 3 K) := E.map Ψ.toMonoidHom
  have hEmP : IsPGroup p Em := (IsElementaryAbelian.isPGroup p E).map Ψ.toMonoidHom
  obtain ⟨g, hg⟩ := N143X.exists_conj_map_le_of_not_dvd_index' hidx hEmP
  let χ : (↥X ⧸ Subgroup.center ↥X) ≃* StatedSp 3 K := Ψ.trans (MulAut.conj g)
  have hEχ : E.map χ.toMonoidHom = Em.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_map]
    rfl
  have hle : E.map χ.toMonoidHom ≤ torusP p K := by
    rintro x hx
    have hxT : x ∈ torus 3 K := hg (hEχ ▸ hx)
    obtain ⟨t, rfl⟩ := hxT
    obtain ⟨y, hy, hyx⟩ := hx
    have hyp : y ^ p = 1 := barF_exp h y hy
    have h1 : torusHom (t ^ p) = (1 : StatedSp 3 K) := by
      rw [map_pow]
      have : (χ y) ^ p = 1 := by rw [← map_pow, hyp, map_one]
      rwa [show χ y = torusHom t from hyx] at this
    have h2 : t ^ p = 1 := torusHom_injective (by rw [h1, map_one])
    exact mem_torusP.2 ⟨t, fun i => by simpa using congrFun h2 i, rfl⟩
  have hcardE : Nat.card (E.map χ.toMonoidHom) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective χ.injective]
    exact barF_card h
  have hE : E.map χ.toMonoidHom = torusP p K :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_torusP hp hrK, hcardE])
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hrK
  obtain ⟨e', w, -, heE, hind, hwN, -, hwe, -, -, -⟩ :=
    sp3_signed_perm_data hζ E χ hE
  exact false_of_signed_permM h hneg e' w heE hind hwN hwe

end Sp6

section Om8

open QuadraticMap CFSG.RankThree.PartOne.KFR4 CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.S15K CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

theorem false_of_om8M {G : Type} [Group G] [Finite G] {p : ℕ} {X A₀ F : Subgroup G}
    (h : Q1327.T123Base p X A₀ F) (hneg : ∀ φ ∈ torusImage F X, ∃ f : F, φ f ≠ f⁻¹)
    (hm : ∃ f : ℕ, 1 ≤ f ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
      StatedClassicalModel (↥X ⧸ Subgroup.center ↥X) .POmegaMinus 4 2 f) : False := by
  obtain ⟨f, hf1, hpq, hmod⟩ := hm
  obtain ⟨b, c, hbc, ⟨φ₀⟩⟩ := projOmegaMinus_of_statedClassicalModel hmod
  have hel := barF_elem h
  have hcomm : ∀ x ∈ bar X F, ∀ y ∈ bar X F, x * y = y * x := fun x hx y hy => by
    have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := bar X F)).comm ⟨x, hx⟩ ⟨y, hy⟩)
    simpa using this
  obtain ⟨e, w, -, heE, hind, hwN, -, hwe, -, -, -⟩ :=
    exists_signed_perm_data hf1 hbc φ₀ h.prime h.five_le hpq (bar X F) (barF_card h) (barF_exp h)
      hcomm
  exact false_of_signed_permM h hneg e w heE hind hwN hwe

end Om8

section Holds

theorem kf1327BM_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF1327BM := by
  intro G _ _ p X A₀ F h _ hLie hsolv hneg hirr hdat
  have hcomm : ∀ a b : F, a * b = b * a := fun a b => h.F_elem.is_comm.comm a b
  have hdat' := hdat
  obtain ⟨t, K, f, -, -, -, -, -, -, -, hpf⟩ := hdat
  have h7 : p ≠ 7 := by
    rintro rfl
    exact seven_not_dvd_two_pow_add_one f hpf
  rcases bClassify hGA CTP.spinRankFour PartTwo.Census.Exceptional.exceptionalRankFour h h7
    hLie with h9 | h10 | h12 | hM3
  · exact h9
  · exact (false_of_weyl_rowM hcomm hirr hneg hsolv (Or.inl rfl)
      (rowData_core_ten (T123Base.toCore h) h10)).elim
  · exact (false_of_weyl_rowM hcomm hirr hneg hsolv (Or.inr rfl)
      (rowData_core_twelve (T123Base.toCore h) h12)).elim
  · rcases hM3 with hm | hm | hm | hm
    · exact (false_of_l4_split h hdat' hm).elim
    · exact (false_of_sp6_splitM h hneg hm).elim
    · exact (false_of_om8M h hneg hm).elim
    · by_cases hp5 : p = 5
      · subst hp5
        obtain ⟨f, hf1, -, h25, hcl⟩ := hm
        obtain ⟨t, -, -, htT, htR, -⟩ := hdat'
        refine (false_of_u5_five h hirr ⟨t, htT, htR⟩ ⟨f, hf1, ?_, hcl⟩).elim
        rcases h25 with hne | h25
        · exact absurd rfl hne
        · exact h25
      · exact (false_of_u5_ne_five h hp5 hm).elim

end Holds

end CFSG.RankThree.PartOne.Q1327T
