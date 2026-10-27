module

public import CFSG.RankThree.PartOne.CTP.ExtA
public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.BenderSuzuki.MatrixGroups

@[expose] noncomputable def pslTwoEquivSL (K : Type) [Field K] [CharP K 2] :
    PSL2MatrixGroup K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 2
    K).trans (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSLTwoEquivSL K)

theorem card_psl2_charTwo (L : Type) [Field L] [Finite L] [CharP L 2] :
    Nat.card (PSL2MatrixGroup L) = Nat.card L * (Nat.card L ^ 2 - 1) := by
  rw [Nat.card_congr (pslTwoEquivSL L).toEquiv]
  exact CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two L

theorem dvd_of_card_dvd {k m : ℕ} (hk : 1 ≤ k)
    (h : 2 ^ k * ((2 ^ k) ^ 2 - 1) ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1)) : k ∣ m := by
  have hu : (2 ^ k) ^ 2 - 1 ∣ 2 ^ m * ((2 ^ m) ^ 2 - 1) := (Dvd.intro_left _ rfl).trans h
  have hodd : Nat.Coprime ((2 ^ k) ^ 2 - 1) (2 ^ m) := by
    apply Nat.Coprime.pow_right
    have h2 : (2 ^ k) ^ 2 - 1 = 2 ^ (2 * k) - 1 := by rw [← pow_mul, mul_comm]
    rw [h2]
    refine Nat.coprime_two_right.mpr (Nat.Even.sub_odd Nat.one_le_two_pow ?_ odd_one)
    have : 2 * k ≠ 0 := by omega
    exact Nat.even_pow.mpr ⟨even_two, this⟩
  have hv : (2 ^ k) ^ 2 - 1 ∣ (2 ^ m) ^ 2 - 1 := hodd.dvd_of_dvd_mul_left hu
  have h2k : (2 ^ k) ^ 2 - 1 = 2 ^ (2 * k) - 1 := by rw [← pow_mul, mul_comm]
  have h2m : (2 ^ m) ^ 2 - 1 = 2 ^ (2 * m) - 1 := by rw [← pow_mul, mul_comm]
  rw [h2k, h2m] at hv
  have hg := Nat.pow_sub_one_gcd_pow_sub_one 2 (2 * k) (2 * m)
  rw [Nat.gcd_eq_left hv] at hg
  have hpos1 : 1 ≤ 2 ^ (2 * k) := Nat.one_le_two_pow
  have hpos2 : 1 ≤ 2 ^ (Nat.gcd (2 * k) (2 * m)) := Nat.one_le_two_pow
  have hpow : 2 ^ (2 * k) = 2 ^ (Nat.gcd (2 * k) (2 * m)) := by omega
  have hgk : 2 * k = Nat.gcd (2 * k) (2 * m) := Nat.pow_right_injective (le_refl 2) hpow
  have : 2 * k ∣ 2 * m := by
    rw [hgk]
    exact Nat.gcd_dvd_right _ _
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this

theorem isSolvable_of_isCyclic (G : Type*) [Group G] [IsCyclic G] : Group.IsSolvable G := by
  refine Group.isSolvable_of_comm (fun a b => ?_)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm]

theorem sl2_subfield_coatom {X : Type} [Group X] {k : ℕ}
    (hk : 2 ≤ k)
    (hX : StatedClassicalModel X .PSL 2 2 (5 * k)) {J H : Subgroup X}
    (hJ : StatedClassicalModel ↥J .PSL 2 2 k) (hJH : J < H) : H = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨L, _, _, _, hLcard, ⟨eL⟩⟩ := exists_sl2_equiv_of_model hX
  obtain ⟨L₀, _, _, _, hL₀card, ⟨e₀⟩⟩ := exists_sl2_equiv_of_model hJ
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have : Finite X := Finite.of_equiv (Matrix.SpecialLinearGroup (Fin 2) L) eL.toEquiv
  have hJcard : Nat.card J = 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
    rw [← Nat.card_congr e₀.toEquiv, CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two,
      hL₀card]
  have hJperf : Group.IsPerfect ↥J := by
    have : ∃ s : Finset L₀, s.card = 4 := by
      have := Fintype.ofFinite L₀
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset L₀)) (n := 4) (by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hL₀card]
          exact hq4)
      exact ⟨s, hs⟩
    have h1 := CFSG.LinearGroups.special_linear_dimension_two_perfect this
    exact Group.IsPerfect.ofSurjective (f := e₀.toMonoidHom) e₀.surjective
  have hJnt : Nontrivial ↥J := by
    rw [← Finite.one_lt_card_iff_nontrivial, hJcard]
    have h16 : 4 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hq4 2
    have h15 : 15 ≤ (2 ^ k) ^ 2 - 1 := by omega
    have := Nat.mul_le_mul hq4 h15
    omega
  have hJns : ¬ Group.IsSolvable ↥J := Group.IsPerfect.not_isSolvable ↥J
  have hHns : ¬ Group.IsSolvable ↥H := fun hs =>
    hJns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJH.le))
  let ψ : X ≃* PSL2MatrixGroup L := eL.symm.trans (pslTwoEquivSL L).symm
  let Hs : Subgroup (PSL2MatrixGroup L) := H.map ψ.toMonoidHom
  have eH : ↥H ≃* ↥Hs := Subgroup.equivMapOfInjective H ψ.toMonoidHom ψ.injective
  have hHsns : ¬ Group.IsSolvable ↥Hs := fun hs =>
    hHns (Group.isSolvable_of_surjective (f := eH.symm.toMonoidHom) eH.symm.surjective)
  have hHscard : Nat.card Hs = Nat.card H := (Nat.card_congr eH.toEquiv).symm
  have hdvd : Nat.card J ∣ Nat.card H := Subgroup.card_dvd_of_le hJH.le
  have hXcard : Nat.card X = 2 ^ (5 * k) * ((2 ^ (5 * k)) ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, card_psl2_charTwo, hLcard]
  have hHpos : 0 < Nat.card H := Nat.card_pos
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification (p := 2)
    (f := 5 * k) hLcard Hs with
    hEl | ⟨z, hz, hcard, hcyc⟩ | ⟨z, hz, hcard, ⟨eD⟩⟩ | ⟨hA4, ⟨eA⟩⟩ | ⟨hS4, ⟨eS⟩⟩ |
    ⟨hA5, ⟨eA5⟩⟩ | ⟨m, t, htm, htq, N, C, hN, hNel, hNcard, hCcyc, hCcard, hdisj, hsup⟩ |
    ⟨m, hm0, hm5, ⟨ePSL⟩⟩ | ⟨m, hm0, hm5, ⟨ePGL⟩⟩
  ·
    have := hEl.toIsMulCommutative
    exact (hHsns inferInstance).elim
  ·
    have := hcyc
    exact (hHsns (isSolvable_of_isCyclic _)).elim
  ·
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0, mul_zero, hHscard] at hcard
      omega
    have : NeZero z := ⟨hz0⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact (hHsns (Group.isSolvable_of_surjective (f := eD.symm.toMonoidHom)
      eD.symm.surjective)).elim
  ·
    have := alternatingGroup.isSolvable (α := Fin 4) (by simp)
    exact (hHsns (Group.isSolvable_of_surjective (f := eA.symm.toMonoidHom)
      eA.symm.surjective)).elim
  ·
    have := Equiv.Perm.isSolvable (α := Fin 4) (by simp)
    exact (hHsns (Group.isSolvable_of_surjective (f := eS.symm.toMonoidHom)
      eS.symm.surjective)).elim
  ·
    exfalso
    have hcard60 : Nat.card H = 60 := by
      rw [← hHscard, Nat.card_congr eA5.toEquiv, Nat.card_eq_fintype_card,
        card_alternatingGroup]
      simp [Nat.factorial]
    have hle : 2 ^ k * ((2 ^ k) ^ 2 - 1) ≤ 60 :=
      Nat.le_of_dvd (by norm_num) (hJcard ▸ hcard60 ▸ hdvd)
    have hge : 60 ≤ 2 ^ k * ((2 ^ k) ^ 2 - 1) := by
      have h16 : 4 ^ 2 ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left hq4 2
      have : 4 * (4 ^ 2 - 1) ≤ 2 ^ k * ((2 ^ k) ^ 2 - 1) :=
        Nat.mul_le_mul hq4 (Nat.sub_le_sub_right h16 1)
      simpa using this
    have heq : J = H := Subgroup.eq_of_le_of_card_ge hJH.le (by rw [hcard60, hJcard]; omega)
    exact hJH.ne heq
  ·
    have hNsolv : Group.IsSolvable ↥N := by
      have := hNel.toIsMulCommutative
      infer_instance
    have hquot : Group.IsSolvable (↥Hs ⧸ N) := by
      let g : ↥C →* (↥Hs ⧸ N) := (QuotientGroup.mk' N).comp C.subtype
      have hg : Function.Surjective g := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
        obtain ⟨n, hn, c, hc, rfl⟩ :=
          Subgroup.mem_sup_of_normal_left.mp (hsup ▸ Subgroup.mem_top x)
        refine ⟨⟨c, hc⟩, ?_⟩
        show ((c : ↥Hs) : ↥Hs ⧸ N) = ((n * c : ↥Hs) : ↥Hs ⧸ N)
        rw [QuotientGroup.eq]
        have := hN.conj_mem n hn c⁻¹
        simpa [mul_assoc] using this
      have := hCcyc
      have hCsolv : Group.IsSolvable ↥C := isSolvable_of_isCyclic _
      exact Group.isSolvable_of_surjective hg
    have : Group.IsSolvable ↥Hs :=
      Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
        intro x hx
        exact ⟨⟨x, (QuotientGroup.eq_one_iff x).mp hx⟩, rfl⟩)
    exact absurd this hHsns
  ·
    have hmcard : Nat.card Hs = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr ePSL.toEquiv, card_psl2_charTwo, GaloisField.card 2 m hm0]
    have hkm : k ∣ m := by
      refine dvd_of_card_dvd (by omega) ?_
      rw [← hmcard, hHscard, ← hJcard]
      exact hdvd
    obtain ⟨a, rfl⟩ := hkm
    have ha : a ∣ 5 := by
      have : k * a ∣ k * 5 := by
        rw [mul_comm k 5]
        exact hm5
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) this
    have hapos : 0 < a := Nat.pos_of_ne_zero (fun h0 => hm0 (by simp [h0]))
    have ha15 : a = 1 ∨ a = 5 := (Nat.dvd_prime Nat.prime_five).mp ha
    rcases ha15 with rfl | rfl
    · exfalso
      have : J = H := Subgroup.eq_of_le_of_card_ge hJH.le (by
        rw [← hHscard, hmcard, mul_one, hJcard])
      exact hJH.ne this
    · refine Subgroup.eq_top_of_card_eq H ?_
      rw [← hHscard, hmcard, hXcard, mul_comm k 5]
  ·
    exfalso
    have hmcard : Nat.card Hs = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
      rw [Nat.card_congr ePGL.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_pgl2_galoisField hm0,
        ← pow_mul, mul_comm m 2, pow_mul]
    have hkm : k ∣ m := by
      refine dvd_of_card_dvd (by omega) ?_
      rw [← hmcard, hHscard, ← hJcard]
      exact hdvd
    obtain ⟨a, rfl⟩ := hkm
    have : 2 * a ∣ 5 := by
      have h1 : k * (2 * a) ∣ k * 5 := by
        rw [mul_comm k 5]
        calc k * (2 * a) = 2 * (k * a) := by ring
          _ ∣ 5 * k := hm5
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) h1
    have h2 : 2 ∣ 5 := (Dvd.intro _ rfl).trans this
    omega

theorem sl2_sup_zpowers_eq_top {X : Type} [Group X] {k : ℕ}
    (hk : 2 ≤ k)
    (hX : StatedClassicalModel X .PSL 2 2 (5 * k)) {J : Subgroup X}
    (hJ : StatedClassicalModel ↥J .PSL 2 2 k) {x : X} (hx : x ∉ J) :
    J ⊔ Subgroup.zpowers x = ⊤ := by
  refine sl2_subfield_coatom hk hX hJ (lt_of_le_of_ne le_sup_left ?_)
  intro h
  exact hx (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

end CFSG.RankThree.PartOne.CTP
