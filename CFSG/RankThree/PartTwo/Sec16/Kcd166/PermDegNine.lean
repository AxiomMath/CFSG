module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreCharacteristic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3A6Orbits

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open MulAction Subgroup
open scoped Pointwise

private noncomputable def blockPerm {Ω P : Type*} [Group P] [MulAction P Ω]
    (B : Set Ω) (g : P) : Equiv.Perm (MulAction.orbit P B) where
  toFun C := ⟨g • (C : Set Ω), by
    obtain ⟨p, hp⟩ := C.2
    refine ⟨g * p, ?_⟩
    change (g * p) • B = g • (C : Set Ω)
    rw [← hp, mul_smul]⟩
  invFun C := ⟨g⁻¹ • (C : Set Ω), by
    obtain ⟨p, hp⟩ := C.2
    refine ⟨g⁻¹ * p, ?_⟩
    change (g⁻¹ * p) • B = g⁻¹ • (C : Set Ω)
    rw [← hp, mul_smul]⟩
  left_inv C := by
    apply Subtype.ext
    simp [smul_smul]
  right_inv C := by
    apply Subtype.ext
    simp [smul_smul]

private noncomputable def blockHom {Ω P : Type*} [Group P] [MulAction P Ω]
    (B : Set Ω) : P →* Equiv.Perm (MulAction.orbit P B) where
  toFun := blockPerm B
  map_one' := by
    apply Equiv.ext
    intro C
    apply Subtype.ext
    ext x
    simp [blockPerm]
  map_mul' := by
    intro g h
    apply Equiv.ext
    intro C
    apply Subtype.ext
    ext x
    simp [blockPerm, mul_smul]

private lemma card_eq_six_and_fixed_eq_one (a c : ℕ) (ha6 : 6 ≤ a) (ha9 : a ≤ 9)
    (hc : c ∣ a) (hclt : c < a) (h5 : 5 ∣ a - c) : a = 6 ∧ c = 1 := by
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · omega
    · exact h
  obtain ⟨m, hm⟩ := h5
  have hdiff : a - c = 5 := by
    have hpos : 0 < a - c := by omega
    have hle : a - c ≤ 8 := by omega
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with rfl | h
      · omega
      · exact h
    have hmle : 5 * m ≤ 8 := by omega
    omega
  have ha_eq : a = c + 5 := by omega
  have hc5 : c ∣ 5 := by
    have h : c ∣ c + 5 := by rwa [← ha_eq]
    rw [add_comm] at h
    exact (Nat.dvd_add_self_right).mp h
  have hc_le : c ≤ 4 := by omega
  interval_cases c
  · exact ⟨by omega, rfl⟩
  · norm_num at hc5
  · norm_num at hc5
  · norm_num at hc5

private lemma not_card_six_of_isElementaryAbelian {A : Type*} [Group A] [Finite A]
    {p : ℕ} (hp : p.Prime) (hA : IsElementaryAbelian p A) (h6 : Nat.card A = 6) : False := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : IsElementaryAbelian p A := hA
  have hpdvd : p ∣ 6 := by
    rcases (IsElementaryAbelian.isPGroup p A).card_eq_or_dvd with h1 | hd
    · omega
    · rwa [h6] at hd
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by norm_num) hpdvd
  have hp_cases : p = 2 ∨ p = 3 := by
    have h23 : p ∣ 2 * 3 := by norm_num at hpdvd ⊢; exact hpdvd
    rcases (Nat.Prime.dvd_mul hp).mp h23 with h2 | h3
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp h2
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h3
  rcases hp_cases with rfl | rfl
  · have h3 : 3 ∣ Nat.card A := by rw [h6]; norm_num
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 h3
    have hb2 : b ^ 2 = 1 := by
      simpa using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) b
    have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hb2
    rw [hb] at hdvd
    norm_num at hdvd
  · have h2 : 2 ∣ Nat.card A := by rw [h6]; norm_num
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 h2
    have hb3 : b ^ 3 = 1 := by
      simpa using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 A) b
    have hdvd : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one hb3
    rw [hb] at hdvd
    norm_num at hdvd

private lemma isPretransitive_of_nontrivial_abelian_normal {Ω P : Type*} [Fintype Ω]
    [Group P] [MulAction P Ω] [Finite P] [FaithfulSMul P Ω] (hΩ : Fintype.card Ω ≤ 9)
    (htrans : MulAction.IsPretransitive P Ω) (hperf : Group.IsPerfect P)
    (A : Subgroup P) [A.Normal] (hAne : A ≠ ⊥) (hAab : IsMulCommutative A) :
    MulAction.IsPretransitive A Ω := by
  classical
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have ha_moves : ∃ α : Ω, (a : P) • α ≠ α := by
    by_contra h
    push Not at h
    apply ha1
    apply Subtype.ext
    apply MulAction.toPerm_injective (α := P) (β := Ω)
    apply Equiv.ext
    intro x
    simpa using h x
  obtain ⟨x0, hx0⟩ := ha_moves
  let B : Set Ω := MulAction.orbit A x0
  have hBblock : MulAction.IsBlock P B := MulAction.IsBlock.orbit_of_normal (N := A) x0
  have hBne : B.Nonempty := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hB2 : 2 ≤ Set.ncard B := by
    have hmem : ({x0, (a : P) • x0} : Set Ω) ⊆ B := by
      rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨MulAction.mem_orbit_self x0, MulAction.mem_orbit x0 a⟩
    have hpair : ({x0, (a : P) • x0} : Set Ω).ncard = 2 := Set.ncard_pair (Ne.symm hx0)
    rw [← hpair]
    exact Set.ncard_le_ncard hmem (Set.toFinite B)
  have hblock_card : Set.ncard (MulAction.orbit P B) ≤ 4 := by
    have hprod := hBblock.ncard_block_mul_ncard_orbit_eq hBne
    have hn9 : Nat.card Ω ≤ 9 := by rw [Nat.card_eq_fintype_card]; exact hΩ
    have h2k : 2 * Set.ncard (MulAction.orbit P B) ≤ Nat.card Ω := by
      rw [← hprod]
      exact Nat.mul_le_mul_right _ hB2
    omega
  let ψ : P →* Equiv.Perm (MulAction.orbit P B) := blockHom B
  have hψperf : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  have hψsolv : Group.IsSolvable ψ.range := by
    have hk4 : Nat.card (MulAction.orbit P B) ≤ 4 := by
      rwa [Nat.card_coe_set_eq]
    letI : Group.IsSolvable (Equiv.Perm (MulAction.orbit P B)) :=
      Equiv.Perm.isSolvable hk4
    exact Group.instIsSolvableSubtypeMemSubgroup ψ.range
  have hψsub : Subsingleton ψ.range := by
    by_contra h
    rw [not_subsingleton_iff_nontrivial] at h
    letI : Nontrivial ψ.range := h
    letI : Group.IsPerfect ψ.range := hψperf
    exact (Group.IsPerfect.not_isSolvable ψ.range) hψsolv
  have hψone : ψ = 1 := by
    apply MonoidHom.ext
    intro g
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨ψ g, ⟨g, rfl⟩⟩ : ψ.range) ⟨1, ⟨1, map_one ψ⟩⟩)
  have hfixB : ∀ g : P, g • B = B := by
    intro g
    have hg : ψ g = 1 := by rw [hψone]; rfl
    have h' : (ψ g) ⟨B, MulAction.mem_orbit_self B⟩ =
        ⟨B, MulAction.mem_orbit_self B⟩ := by
      simpa [ψ, blockHom, blockPerm] using
        congrArg (fun e : Equiv.Perm (MulAction.orbit P B) =>
          e ⟨B, MulAction.mem_orbit_self B⟩) hg
    exact congrArg Subtype.val h'
  have hBuniv : B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x0 x
    rw [← hg]
    have hx0B : x0 ∈ B := MulAction.mem_orbit_self x0
    have : g • x0 ∈ g • B := Set.smul_mem_smul_set hx0B
    rwa [hfixB g] at this
  exact (MulAction.isPretransitive_iff_orbit_eq_univ x0).mpr hBuniv

private lemma centralizer_eq_of_abelian_regular {Ω P : Type*} [Group P] [MulAction P Ω]
    [FaithfulSMul P Ω] (A : Subgroup P) (hAab : IsMulCommutative A)
    (hAtrans : MulAction.IsPretransitive A Ω) (α : Ω)
    (hstab : MulAction.stabilizer A α = ⊥) :
    Subgroup.centralizer (A : Set P) = A := by
  letI : IsMulCommutative A := hAab
  apply le_antisymm
  · intro g hg
    obtain ⟨a, haeq⟩ := MulAction.exists_smul_eq A α (g • α)
    have hga : g = (a : P) := by
      apply MulAction.toPerm_injective (α := P) (β := Ω)
      apply Equiv.ext
      intro x
      obtain ⟨b, hbx⟩ := MulAction.exists_smul_eq A α x
      have hbxP : (b : P) • α = x := hbx
      have haeqP : (a : P) • α = g • α := haeq
      calc
        g • x = g • ((b : P) • α) := by rw [hbxP]
        _ = (g * (b : P)) • α := by rw [mul_smul]
        _ = ((b : P) * g) • α := by
          rw [Subgroup.mem_centralizer_iff.mp hg (b : P) b.2]
        _ = (b : P) • (g • α) := by rw [mul_smul]
        _ = (b : P) • ((a : P) • α) := by rw [← haeqP]
        _ = ((b : P) * (a : P)) • α := by rw [mul_smul]
        _ = ((a : P) * (b : P)) • α := by
          congr 1
          exact congrArg Subtype.val (hAab.is_comm.comm b a)
        _ = (a : P) • ((b : P) • α) := by rw [mul_smul]
        _ = (a : P) • x := by rw [hbxP]
    rw [hga]
    exact a.2
  · exact Subgroup.le_centralizer A

private lemma stabilizer_eq_bot_of_abelian_transitive {Ω P : Type*} [Group P] [MulAction P Ω]
    (A : Subgroup P) [FaithfulSMul A Ω] (hAab : IsMulCommutative A)
    (hAtrans : MulAction.IsPretransitive A Ω) (α : Ω) :
    MulAction.stabilizer A α = ⊥ := by
  letI : IsMulCommutative A := hAab
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  apply MulAction.toPerm_injective (α := A) (β := Ω)
  apply Equiv.ext
  intro x
  obtain ⟨b, hbx⟩ := MulAction.exists_smul_eq A α x
  have hbxP : (b : P) • α = x := hbx
  have haP : (a : P) • α = α := ha
  simp only [MulAction.toPerm_apply, one_smul]
  calc
    (a : P) • x = (a : P) • ((b : P) • α) := by rw [hbxP]
    _ = ((a : P) * (b : P)) • α := by rw [mul_smul]
    _ = ((b : P) * (a : P)) • α := by
      congr 1
      exact congrArg Subtype.val (hAab.is_comm.comm a b)
    _ = (b : P) • ((a : P) • α) := by rw [mul_smul]
    _ = (b : P) • α := by rw [haP]
    _ = x := hbxP

private lemma ker_eq_bot {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω ≤ 9) (hn6 : 6 ≤ Fintype.card Ω)
    (P : Subgroup (Equiv.Perm Ω))
    (htrans : MulAction.IsPretransitive P Ω) (hperf : Group.IsPerfect P)
    (φ : P →* alternatingGroup (Fin 6)) (hφ : Function.Surjective φ)
    (hker : Group.IsSolvable φ.ker) (h360 : 360 ∣ Nat.card P) :
    φ.ker = ⊥ := by
  classical
  by_contra hne
  letI : Nontrivial φ.ker := (Subgroup.nontrivial_iff_ne_bot φ.ker).mpr hne
  obtain ⟨A0, p, hA0char, hA0ne, hp, hA0elem⟩ :=
    CFSG.ComponentClassification.CatalogueBHeldSmallCore.exists_characteristic_elementaryAbelian
      φ.ker
  let A : Subgroup P := A0.map (φ.ker).subtype
  have hAnorm : A.Normal := by
    letI : A0.Characteristic := hA0char
    exact ConjAct.normal_of_characteristic_of_normal (H := φ.ker) (K := A0)
  letI : A.Normal := hAnorm
  have hAne : A ≠ ⊥ := by
    intro h
    apply hA0ne
    rw [eq_bot_iff]
    intro x hx
    have hxA : (x : P) ∈ A := Subgroup.mem_map_of_mem (φ.ker).subtype hx
    rw [h, Subgroup.mem_bot] at hxA
    exact Subtype.ext hxA
  have hAle : A ≤ φ.ker := Subgroup.map_subtype_le _
  have hAelem : IsElementaryAbelian p A := by
    letI : Fact p.Prime := ⟨hp⟩
    letI : IsElementaryAbelian p A0 := hA0elem
    exact IsElementaryAbelian.map_subtype
  have hAab : IsMulCommutative A := hAelem.toIsMulCommutative
  haveI : FaithfulSMul P Ω := by
    rw [faithfulSMul_iff]
    intro g hg
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact hg x
  have hAtrans : MulAction.IsPretransitive A Ω :=
    isPretransitive_of_nontrivial_abelian_normal hΩ htrans hperf A hAne hAab
  haveI : FaithfulSMul A Ω := by
    rw [faithfulSMul_iff]
    intro a ha
    apply Subtype.ext
    apply (Subgroup.subtype_injective P)
    apply Equiv.ext
    intro x
    exact ha x
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨α⟩ := ‹Nonempty Ω›
  have hstab : MulAction.stabilizer A α = ⊥ :=
    stabilizer_eq_bot_of_abelian_transitive A hAab hAtrans α
  have hAcard : Nat.card A = Nat.card Ω := by
    have hidx := MulAction.index_stabilizer_of_transitive (G := A) (x := α)
    have hcard := Subgroup.card_mul_index (MulAction.stabilizer A α)
    rw [hidx, hstab] at hcard
    simpa using hcard.symm
  have hcentralizer : Subgroup.centralizer (A : Set P) = A :=
    centralizer_eq_of_abelian_regular A hAab hAtrans α hstab
  have h5dvdP : 5 ∣ Nat.card P := dvd_trans (by norm_num : 5 ∣ 360) h360
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5dvdP
  have hx_notA : x ∉ A := by
    intro hxA
    have h5dvdA : 5 ∣ Nat.card A := by
      rw [← hx]
      exact Subgroup.orderOf_dvd_natCard A hxA
    rw [hAcard, Nat.card_eq_fintype_card] at h5dvdA
    interval_cases Fintype.card Ω <;> norm_num at h5dvdA
  let F : MulAut A := MulAut.conjNormal x
  have hFne : F ≠ 1 := by
    intro hF
    apply hx_notA
    rw [← hcentralizer]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h := congrArg (fun F : MulAut A => (F ⟨a, ha⟩ : A)) hF
    simp only [MulAut.one_apply] at h
    have h' : x * a * x⁻¹ = a := by
      have := congrArg Subtype.val h
      simpa [F, MulAut.conjNormal_apply] using this
    calc a * x = (x * a * x⁻¹) * x := by rw [h']
      _ = x * a := by group
  have hx5 : x ^ 5 = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hF5 : F ^ 5 = 1 := by
    change (MulAut.conjNormal x) ^ 5 = 1
    rw [← map_pow, hx5, map_one]
  have hForder : orderOf F = 5 := by
    have hdvd : orderOf F ∣ 5 := orderOf_dvd_of_pow_eq_one hF5
    have hcases : orderOf F = 1 ∨ orderOf F = 5 := by
      simpa using (Nat.dvd_prime Nat.prime_five).mp hdvd
    rcases hcases with h1 | h5
    · exact absurd (orderOf_eq_one_iff.mp h1) hFne
    · exact h5
  let G5 : Subgroup P := Subgroup.zpowers x
  have hG5card : Nat.card G5 = 5 := by
    rw [Nat.card_zpowers, hx]
  have hG5p : IsPGroup 5 G5 := IsPGroup.of_card (n := 1) (by rw [hG5card]; norm_num)
  letI : MulDistribMulAction G5 A :=
    MulDistribMulAction.compHom A ((MulAut.conjNormal (H := A)).comp G5.subtype)
  have hcong : Nat.card A ≡ Nat.card (MulAction.fixedPoints G5 A) [MOD 5] :=
    hG5p.card_modEq_card_fixedPoints A
  let C : Subgroup A := FixedPoints.subgroup G5 A
  have hCcard : Nat.card C = Nat.card (MulAction.fixedPoints G5 A) := rfl
  have hcongC : Nat.card A ≡ Nat.card C [MOD 5] := by
    rwa [← hCcard] at hcong
  have hCne : C ≠ ⊤ := by
    intro hCtop
    apply hFne
    apply MulEquiv.ext
    intro a
    have hfix : a ∈ C := by rw [hCtop]; exact Subgroup.mem_top a
    have hxfix : (⟨x, Subgroup.mem_zpowers x⟩ : G5) • a = a :=
      (FixedPoints.mem_subgroup G5 A a).mp hfix _
    change (MulAut.conjNormal x) a = a at hxfix
    simpa [F] using hxfix
  have hC_le : Nat.card C ≤ Nat.card A :=
    Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_subgroup_dvd_card C)
  have hC_lt : Nat.card C < Nat.card A := by
    have hne_card : Nat.card C ≠ Nat.card A := by
      intro heq
      apply hCne
      exact Subgroup.eq_of_le_of_card_ge le_top (by rw [Subgroup.card_top, heq])
    omega
  have h5div : 5 ∣ Nat.card A - Nat.card C :=
    (Nat.modEq_iff_dvd' hC_le).mp hcongC.symm
  have hA6' : 6 ≤ Nat.card A := by
    rw [hAcard, Nat.card_eq_fintype_card]
    exact hn6
  have hA9 : Nat.card A ≤ 9 := by
    rw [hAcard, Nat.card_eq_fintype_card]
    exact hΩ
  obtain ⟨hA6, _⟩ := card_eq_six_and_fixed_eq_one (Nat.card A) (Nat.card C)
    hA6' hA9 (Subgroup.card_subgroup_dvd_card C) hC_lt h5div
  exact not_card_six_of_isElementaryAbelian hp hAelem hA6

theorem card_eq_six_and_eq_alternatingGroup {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (hΩ : Fintype.card Ω ≤ 9) (P : Subgroup (Equiv.Perm Ω))
    (htrans : MulAction.IsPretransitive P Ω) (hperf : Group.IsPerfect P)
    (φ : P →* alternatingGroup (Fin 6)) (hφ : Function.Surjective φ)
    (hker : Group.IsSolvable φ.ker) :
    Fintype.card Ω = 6 ∧ P = alternatingGroup Ω := by
  classical
  have hcardA6 : Fintype.card (alternatingGroup (Fin 6)) = 360 := by
    rw [card_alternatingGroup]
    norm_num [Nat.factorial]
  have h360 : 360 ∣ Nat.card P := by
    have h := Subgroup.card_ker_mul_card_of_surjective hφ
    have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rwa [Nat.card_eq_fintype_card]
    rw [hA6, mul_comm] at h
    exact ⟨Nat.card φ.ker, h.symm⟩
  have hn6 : 6 ≤ Fintype.card Ω := by
    by_contra h
    have hdvd : 360 ∣ Nat.factorial (Fintype.card Ω) := by
      have h1 : 360 ∣ Nat.card (Equiv.Perm Ω) :=
        dvd_trans h360 (Subgroup.card_subgroup_dvd_card P)
      have h2 : Nat.card (Equiv.Perm Ω) = Nat.factorial (Fintype.card Ω) := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card]
      rwa [h2] at h1
    have h5 : Fintype.card Ω ≤ 5 := by omega
    obtain ⟨k, hk⟩ := hdvd
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · have hpos := Nat.factorial_pos (Fintype.card Ω)
        simp at hk
        omega
      · exact h
    have hfactpos : 0 < Nat.factorial (Fintype.card Ω) := Nat.factorial_pos _
    have hfactle : Nat.factorial (Fintype.card Ω) ≤ 120 := by
      have hle := Nat.factorial_le h5
      norm_num [Nat.factorial] at hle ⊢
      exact hle
    omega
  have hker_bot : φ.ker = ⊥ := ker_eq_bot hΩ hn6 P htrans hperf φ hφ hker h360
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hker_bot
  have hPcard : Nat.card P = 360 := by
    have h := Subgroup.card_ker_mul_card_of_surjective hφ
    have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rwa [Nat.card_eq_fintype_card]
    rw [hker_bot, hA6] at h
    simpa using h.symm
  haveI : Nonempty Ω := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨α⟩ := ‹Nonempty Ω›
  have hn_dvd360 : Nat.card Ω ∣ 360 := by
    have hidx := MulAction.index_stabilizer_of_transitive (G := P) (x := α)
    have hcard := Subgroup.card_mul_index (MulAction.stabilizer P α)
    rw [hPcard, hidx] at hcard
    exact ⟨Nat.card (MulAction.stabilizer P α), by rw [mul_comm]; exact hcard.symm⟩
  have hstab_card : Nat.card (MulAction.stabilizer P α) = 360 / Fintype.card Ω := by
    have hidx := MulAction.index_stabilizer_of_transitive (G := P) (x := α)
    have hcard := Subgroup.card_mul_index (MulAction.stabilizer P α)
    rw [hPcard, hidx] at hcard
    have hcard' : Fintype.card Ω * Nat.card (MulAction.stabilizer P α) = 360 := by
      rw [← Nat.card_eq_fintype_card (α := Ω), mul_comm]
      exact hcard
    exact Nat.eq_div_of_mul_eq_right (by omega) hcard' 
  let e : P ≃* alternatingGroup (Fin 6) := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have hno40 : Nat.card (MulAction.stabilizer P α) ≠ 40 := by
    intro h40
    let K : Subgroup (alternatingGroup (Fin 6)) :=
      (MulAction.stabilizer P α).map e.toMonoidHom
    have hKcard : Nat.card K = 40 := by
      dsimp [K]
      change Nat.card (Subgroup.map e.toMonoidHom (MulAction.stabilizer P α)) = 40
      rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h40]
    exact CFSG.QuasithinUnique.Setup.X3.no_subgroup_order (K := K) (Or.inr (Or.inl hKcard))
  have hno45 : Nat.card (MulAction.stabilizer P α) ≠ 45 := by
    intro h45
    let K : Subgroup (alternatingGroup (Fin 6)) :=
      (MulAction.stabilizer P α).map e.toMonoidHom
    have hKcard : Nat.card K = 45 := by
      dsimp [K]
      change Nat.card (Subgroup.map e.toMonoidHom (MulAction.stabilizer P α)) = 45
      rw [Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, h45]
    exact CFSG.QuasithinUnique.Setup.X3.no_subgroup_order (K := K) (Or.inr (Or.inr hKcard))
  have hn_eq6 : Fintype.card Ω = 6 := by
    interval_cases hΩ' : Fintype.card Ω
    · rfl
    · exfalso
      norm_num [hΩ'] at hn_dvd360
    · exfalso
      have h45 : Nat.card (MulAction.stabilizer P α) = 45 := by
        rw [hstab_card]
      exact hno45 h45
    · exfalso
      have h40 : Nat.card (MulAction.stabilizer P α) = 40 := by
        rw [hstab_card]
      exact hno40 h40
  have hP_eq : P = alternatingGroup Ω := by
    have hindex : P.index = 2 := by
      have hPermCard : Nat.card (Equiv.Perm Ω) = 720 := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, hn_eq6]
        norm_num [Nat.factorial]
      have hmul := Subgroup.card_mul_index P
      rw [hPcard, hPermCard] at hmul
      omega
    exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  exact ⟨hn_eq6, hP_eq⟩

end CFSG.RankThree.PartTwo.Sec16.Kcd166
