module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFactsU3Model
public import CFSG.Quasithin.Recognition.Stroth.SubconstUnitaryNonabelian
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiRadical
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryCentralizerBasic
public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.RankOneFacts2
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.Timmesfeld.Bridge.Asc72Unitary

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.Stroth.WeissDelta

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.SeitzReduction.RankOne CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.UnitaryModel CFSG.ShultStronglyClosedTI.TwoCoreGrowth
  CFSG.ProperTwoGeneratedCore.RootCenter CFSG.Timmesfeld.Bridge.Asc72
open Matrix

private lemma eq_one_of_odd_order_of_dvd_two_pow {G : Type*} [Group G] {x : G} {n : ℕ}
    (hodd : Odd (orderOf x)) (hdvd : orderOf x ∣ 2 ^ n) : x = 1 := by
  have hcop : Nat.Coprime (orderOf x) (2 ^ n) :=
    (Nat.coprime_two_right.mpr hodd).pow_right n
  have hone : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  exact orderOf_eq_one_iff.mp hone

private lemma dihedral_two_element_mem_complement {M : Type*} [Group M] [Finite M]
    {A C D O : Subgroup M} {m : ℕ} (hC : C ≤ A) (hCn : (C.subgroupOf A).Normal)
    (hCD : C ⊓ D = ⊥) (hsup : C ⊔ D = A)
    (hD : Nonempty (D ≃* DihedralGroup m)) (hm : Odd m)
    (hO : O ≤ A) (hOodd : Odd (Nat.card O)) (hOC : O ⊓ C = ⊥) (hOne : O ≠ ⊥) :
    ∀ γ ∈ A, IsPSingular 2 γ → (∀ o ∈ O, γ * o = o * γ) → γ ∈ C := by
  classical
  obtain ⟨eD⟩ := hD
  obtain ⟨π, -, hπker⟩ := exists_proj_of_complement hCD hsup hCn
  let πD : A →* DihedralGroup m := eD.toMonoidHom.comp π
  have hπDker : ∀ y : A, πD y = 1 ↔ (y : M) ∈ C := by
    intro y
    constructor
    · intro h
      apply (hπker y).mp
      exact eD.injective (by simpa [πD] using h)
    · intro h
      have h1 : π y = 1 := (hπker y).mpr h
      simp [πD, h1]
  intro γ hγA hγ2 hγcomm
  obtain ⟨a, ha⟩ := hγ2
  let γA : A := ⟨γ, hγA⟩
  obtain ⟨o, ho1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hOne
  have hoO : (o : M) ∈ O := o.2
  let oA : A := ⟨o, hO hoO⟩
  have hoC : (o : M) ∉ C := by
    intro hoc
    have hmem : (o : M) ∈ O ⊓ C := ⟨hoO, hoc⟩
    rw [hOC, Subgroup.mem_bot] at hmem
    exact ho1 (Subtype.ext hmem)
  have hπo : πD oA ≠ 1 := fun h => hoC ((hπDker oA).mp h)
  have hγpow : (πD γA) ^ 2 ^ a = 1 := by
    have h1 : γA ^ 2 ^ a = 1 := by
      apply Subtype.ext
      simpa [γA, ha] using pow_orderOf_eq_one γ
    simpa using congrArg πD h1
  have hoPow : (πD oA) ^ Nat.card O = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    have h1 : orderOf (πD oA) ∣ orderOf oA := orderOf_map_dvd πD oA
    have h2 : orderOf oA ∣ Nat.card O := by
      simpa [oA] using Subgroup.orderOf_dvd_natCard O hoO
    exact h1.trans h2
  have hcommA : Commute γA oA := by
    apply Subtype.ext
    exact hγcomm (o : M) hoO
  have hcomm : Commute (πD γA) (πD oA) := hcommA.map πD
  have hcommut : ⁅πD γA, πD oA⁆ ^ 2 ^ 0 = 1 := by
    have h1 : ⁅πD γA, πD oA⁆ = 1 := by
      rw [commutatorElement_def, hcomm.eq]
      group
    rw [h1, one_pow]
  rcases dihedral_eq_one_or_eq_one_of_commutator hm hγpow hoPow hOodd hcommut with h | h
  · exact (hπDker γA).mp h
  · exact absurd h hπo

private lemma dihedral_odd_pow_mem_complement {M : Type*} [Group M] [Finite M]
    {A C D : Subgroup M} {m : ℕ} (hC : C ≤ A) (hCn : (C.subgroupOf A).Normal)
    (hCD : C ⊓ D = ⊥) (hsup : C ⊔ D = A)
    (hD : Nonempty (D ≃* DihedralGroup m)) :
    ∀ γ ∈ A, Odd (orderOf γ) → γ ^ m ∈ C := by
  classical
  obtain ⟨eD⟩ := hD
  obtain ⟨π, -, hπker⟩ := exists_proj_of_complement hCD hsup hCn
  let πD : A →* DihedralGroup m := eD.toMonoidHom.comp π
  have hπDker : ∀ y : A, πD y = 1 ↔ (y : M) ∈ C := by
    intro y
    constructor
    · intro h
      apply (hπker y).mp
      exact eD.injective (by simpa [πD] using h)
    · intro h
      have h1 : π y = 1 := (hπker y).mpr h
      simp [πD, h1]
  intro γ hγA hodd
  let γA : A := ⟨γ, hγA⟩
  have hoddπ : Odd (orderOf (πD γA)) :=
    hodd.of_dvd_nat (by simpa [γA] using orderOf_map_dvd πD γA)
  have hpow : (πD γA) ^ m = 1 := by
    rcases dihedral_pow_eq_one_or_sq_eq_one (πD γA) with h | h
    · exact h
    · have hone : πD γA = 1 :=
        eq_one_of_odd_order_of_dvd_two_pow (n := 1) hoddπ
          (by simpa using (orderOf_dvd_of_pow_eq_one h))
      rw [hone, one_pow]
  have hmem : ((γA ^ m : A) : M) ∈ C :=
    (hπDker (γA ^ m)).mp (by simpa [map_pow, hpow])
  simpa [γA] using hmem

private lemma eq_of_normal_root {N : Type*} [Group N] [Finite N] {Ω : Type} [MulAction N Ω]
    {ω ω' : Ω} (hωω' : ω ≠ ω') {A B : Subgroup N}
    (hA : A ≤ MulAction.stabilizer N ω)
    (hAn : (A.subgroupOf (MulAction.stabilizer N ω)).Normal) (hA2 : IsPGroup 2 A)
    (hAreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! a : A, (a : N) • α = β)
    (hB : B ≤ MulAction.stabilizer N ω)
    (hBn : (B.subgroupOf (MulAction.stabilizer N ω)).Normal) (hB2 : IsPGroup 2 B)
    (hBreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! b : B, (b : N) • α = β)
    (hTodd : Odd (Nat.card ↥(MulAction.stabilizer N ω ⊓
      MulAction.stabilizer N ω'))) : A = B := by
  classical
  have hstab_le_normA : MulAction.stabilizer N ω ≤
      Subgroup.normalizer (A : Set N) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mp hAn
  have hBnormA : B ≤ Subgroup.normalizer (A : Set N) := hB.trans hstab_le_normA
  have hAB2 : IsPGroup 2 ↥(A ⊔ B) :=
    IsPGroup.to_sup_of_normal_left' hA2 hB2 hBnormA
  have hBleA : B ≤ A := by
    intro b hb
    have hbω : (b : N) • ω = ω := MulAction.mem_stabilizer_iff.mp (hB hb)
    have hbω' : (b : N) • ω' ≠ ω := by
      intro h1
      have h2 : ω' = ω := by
        calc ω' = (b : N)⁻¹ • ((b : N) • ω') := (inv_smul_smul (b : N) ω').symm
          _ = (b : N)⁻¹ • ω := by rw [h1]
          _ = ω := by
              conv_lhs => rw [← hbω]
              exact inv_smul_smul (b : N) ω
      exact hωω' h2.symm
    obtain ⟨a, ha, haeq⟩ := hAreg ω' ((b : N) • ω') hωω'.symm hbω'
    have hmem : (a : N)⁻¹ * (b : N) ∈ (A ⊔ B : Subgroup N) :=
      (A ⊔ B).mul_mem ((A ⊔ B).inv_mem (Subgroup.mem_sup_left a.2))
        (Subgroup.mem_sup_right hb)
    let m : ↥(A ⊔ B) := ⟨(a : N)⁻¹ * (b : N), hmem⟩
    have haω : (a : N) • ω = ω := MulAction.mem_stabilizer_iff.mp (hA a.2)
    have hmω : (m : N) • ω = ω := by
      change ((a : N)⁻¹ * (b : N)) • ω = ω
      rw [mul_smul, hbω]
      conv_lhs => rw [← haω]
      exact inv_smul_smul (a : N) ω
    have hmω' : (m : N) • ω' = ω' := by
      change ((a : N)⁻¹ * (b : N)) • ω' = ω'
      rw [mul_smul, ← ha]
      exact inv_smul_smul (a : N) ω'
    have hmT : (m : N) ∈ MulAction.stabilizer N ω ⊓ MulAction.stabilizer N ω' :=
      ⟨hmω, hmω'⟩
    have hdivT : orderOf (m : N) ∣
        Nat.card ↥(MulAction.stabilizer N ω ⊓ MulAction.stabilizer N ω') :=
      Subgroup.orderOf_dvd_natCard _ hmT
    have hdivAB : orderOf (m : N) ∣ Nat.card ↥(A ⊔ B) := by
      simpa using Subgroup.orderOf_dvd_natCard (A ⊔ B) m.2
    obtain ⟨n, hn⟩ := hAB2.exists_card_eq
    have hcop : Nat.Coprime (2 ^ n)
        (Nat.card ↥(MulAction.stabilizer N ω ⊓ MulAction.stabilizer N ω')) :=
      (Nat.coprime_two_left.mpr hTodd).pow_left n
    have hone : orderOf (m : N) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (by rwa [hn] at hdivAB) hdivT
    have hm1 : (m : N) = 1 := orderOf_eq_one_iff.mp hone
    have hab : (a : N) = (b : N) := by
      have h1 : (a : N)⁻¹ * (b : N) = 1 := hm1
      calc (a : N) = (a : N) * ((a : N)⁻¹ * (b : N)) := by rw [h1, mul_one]
        _ = (b : N) := by group
    show (b : N) ∈ A
    exact hab ▸ a.2
  have hAleB : A ≤ B := by
    have hstab_le_normB : MulAction.stabilizer N ω ≤
        Subgroup.normalizer (B : Set N) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hB).mp hBn
    have hAnormB : A ≤ Subgroup.normalizer (B : Set N) := hA.trans hstab_le_normB
    have hBA2 : IsPGroup 2 ↥(B ⊔ A) :=
      IsPGroup.to_sup_of_normal_left' hB2 hA2 hAnormB
    intro a ha
    have haω : (a : N) • ω = ω := MulAction.mem_stabilizer_iff.mp (hA ha)
    have haω' : (a : N) • ω' ≠ ω := by
      intro h1
      have h2 : ω' = ω := by
        calc ω' = (a : N)⁻¹ • ((a : N) • ω') := (inv_smul_smul (a : N) ω').symm
          _ = (a : N)⁻¹ • ω := by rw [h1]
          _ = ω := by
              conv_lhs => rw [← haω]
              exact inv_smul_smul (a : N) ω
      exact hωω' h2.symm
    obtain ⟨b, hb, hbeq⟩ := hBreg ω' ((a : N) • ω') hωω'.symm haω'
    have hmem : (b : N)⁻¹ * (a : N) ∈ (B ⊔ A : Subgroup N) :=
      (B ⊔ A).mul_mem ((B ⊔ A).inv_mem (Subgroup.mem_sup_left b.2))
        (Subgroup.mem_sup_right ha)
    let m : ↥(B ⊔ A) := ⟨(b : N)⁻¹ * (a : N), hmem⟩
    have hbω : (b : N) • ω = ω := MulAction.mem_stabilizer_iff.mp (hB b.2)
    have hmω : (m : N) • ω = ω := by
      change ((b : N)⁻¹ * (a : N)) • ω = ω
      rw [mul_smul, haω]
      conv_lhs => rw [← hbω]
      exact inv_smul_smul (b : N) ω
    have hmω' : (m : N) • ω' = ω' := by
      change ((b : N)⁻¹ * (a : N)) • ω' = ω'
      rw [mul_smul, ← hb]
      exact inv_smul_smul (b : N) ω'
    have hmT : (m : N) ∈ MulAction.stabilizer N ω ⊓ MulAction.stabilizer N ω' :=
      ⟨hmω, hmω'⟩
    have hdivT : orderOf (m : N) ∣
        Nat.card ↥(MulAction.stabilizer N ω ⊓ MulAction.stabilizer N ω') :=
      Subgroup.orderOf_dvd_natCard _ hmT
    have hdivBA : orderOf (m : N) ∣ Nat.card ↥(B ⊔ A) := by
      simpa using Subgroup.orderOf_dvd_natCard (B ⊔ A) m.2
    obtain ⟨n, hn⟩ := hBA2.exists_card_eq
    have hcop : Nat.Coprime (2 ^ n)
        (Nat.card ↥(MulAction.stabilizer N ω ⊓ MulAction.stabilizer N ω')) :=
      (Nat.coprime_two_left.mpr hTodd).pow_left n
    have hone : orderOf (m : N) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (by rwa [hn] at hdivBA) hdivT
    have hm1 : (m : N) = 1 := orderOf_eq_one_iff.mp hone
    have hba : (b : N) = (a : N) := by
      have h1 : (b : N)⁻¹ * (a : N) = 1 := hm1
      calc (b : N) = (b : N) * ((b : N)⁻¹ * (a : N)) := by rw [h1, mul_one]
        _ = (a : N) := by group
    show (a : N) ∈ B
    exact hba ▸ b.2
  exact le_antisymm hAleB hBleA

private lemma mem_center_map_conj {N : Type*} [Group N] {U : Subgroup N} {g x : N} :
    (x ∈ U.map (MulAut.conj g).toMonoidHom ∧
      ∀ y ∈ U.map (MulAut.conj g).toMonoidHom, x * y = y * x) ↔
      ∃ u ∈ U, (∀ v ∈ U, u * v = v * u) ∧ x = MulAut.conj g u := by
  constructor
  · rintro ⟨hx, hxc⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨u, hu, ?_, rfl⟩
    intro v hv
    have hv' : MulAut.conj g v ∈ U.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hv
    have h := hxc _ hv'
    apply (MulAut.conj g).injective
    simpa [map_mul] using h
  · rintro ⟨u, hu, hcomm, rfl⟩
    constructor
    · exact Subgroup.mem_map_of_mem _ hu
    · intro y hy
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
      have h := hcomm v hv
      calc MulAut.conj g u * MulAut.conj g v
          = MulAut.conj g (u * v) := (map_mul _ _ _).symm
        _ = MulAut.conj g (v * u) := by rw [h]
        _ = MulAut.conj g v * MulAut.conj g u := map_mul _ _ _

private lemma exists_torus_centralizing_rootCenter {K : Type} [Field K] [Finite K]
    (J : HermitianForm 3 K) (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : ℕ) (hk : 2 ≤ k) (hconj : ∀ z : K, J.conj z = z ^ (2 ^ k))
    (hcard : Nat.card K = (2 ^ k) ^ 2) :
    ∃ c : Kˣ, (c : K) * J.conj c = 1 ∧ torusPSU J hJ c ≠ 1 ∧
      ∀ u ∈ CFSG.ProperTwoGeneratedCore.RootCenter.unitaryRootCenter J hJ,
        Commute u (torusPSU J hJ c) := by
  classical
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨c, hcq, hc3⟩ := exists_unit_pow_succ_eq_one (K := K) (q := 2 ^ k) hq4 hcard
  have hc : (c : K) * J.conj c = 1 := by
    rw [hconj, ← pow_succ', ← Units.val_pow_eq_pow_val, hcq, Units.val_one]
  refine ⟨c, hc, torusPSU_ne_one J hJ hc hc3, ?_⟩
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) (by
    rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  intro u hu
  obtain ⟨b, M, hb, hM, hgM⟩ :=
    (CFSG.ProperTwoGeneratedCore.RootCenter.mem_unitaryRootCenter_iff_heisenberg J hJ u).mp hu
  have hM' : (M : Matrix (Fin 3) (Fin 3) K) = !![1, 0, b; 0, 1, 0; 0, 0, 1] := by
    rw [hM, CFSG.ShultStronglyClosedTI.UnitaryModel.heisenbergMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact commute_torusPSU_of_root J hJ hc hM' hgM

private structure PSU3RootData {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [Field F] [Finite F] {N : Subgroup X} [N.Normal] (k : ℕ)
    (M : PSU3IsotropicModel X Ω F N k) (ω ω' : Ω) (R : Subgroup X) : Type where
  RN : Subgroup ↥N
  RN_eq : RN = R.subgroupOf N
  root_le : R ≤ MulAction.stabilizer X ω
  root_normal : (R.subgroupOf (MulAction.stabilizer X ω)).Normal
  card_R : Nat.card R = (2 ^ k) ^ 3
  card_RN : Nat.card RN = (2 ^ k) ^ 3
  U : Subgroup ↥N
  U_eq : U = (CFSG.omega₁ (G := RN) (p := 2)).map RN.subtype
  U_center : ∀ x : ↥N, x ∈ U ↔ x ∈ RN ∧ ∀ y ∈ RN, x * y = y * x
  U_card : Nat.card U = 2 ^ k
  A : Subgroup (MulAut ↥N)
  A_eq : A = rootCenterAut RN U
  D : Subgroup (MulAut ↥N)
  inf_D : RN.map (MulAut.conj (G := ↥N)) ⊓ D = ⊥
  sup_D : RN.map (MulAut.conj (G := ↥N)) ⊔ D = A
  normal_C : ((RN.map (MulAut.conj (G := ↥N))).subgroupOf A).Normal
  card_D : Nat.card D = 2 * (2 ^ k + 1)
  D_dih : Nonempty (D ≃* DihedralGroup (2 ^ k + 1))
  inj_conj : Set.InjOn (MulAut.conj (G := ↥N)) (RN : Set ↥N)
  RN_2 : IsPGroup 2 RN
  C_2 : IsPGroup 2 (RN.map (MulAut.conj (G := ↥N)))
  card_C : Nat.card (RN.map (MulAut.conj (G := ↥N))) = (2 ^ k) ^ 3
  sigma_inj : Function.Injective (MulAut.conjNormal (G := X) (H := N))
  t : ↥N
  t_ne : t ≠ 1
  t_mem : (t : X) ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
  t_center : ∀ u ∈ U, MulAut.conj t u = u
  t_A : MulAut.conj t ∈ A
  transitive : ∀ u v : ↥N, u ∈ U → v ∈ U → u ≠ 1 → v ≠ 1 →
      ∃ s : ↥N, (s : X) ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω' ∧
        (s : X) * (u : X) * (s : X)⁻¹ = (v : X)

private lemma exists_rootData {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] [Field F] [Finite F] {N : Subgroup X}
    (hN : N.Normal) {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = (2 ^ k) ^ 2)
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2)
    (M : PSU3IsotropicModel X Ω F N k) (h : RankOneLocal X Ω N)
    {ω ω' : Ω} (hne : ω ≠ ω') (R : Subgroup X)
    (hR : R ≤ MulAction.stabilizer X ω)
    (hRn : (R.subgroupOf (MulAction.stabilizer X ω)).Normal)
    (hR2 : IsPGroup 2 R)
    (hreg : ∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) :
    Nonempty (PSU3RootData k M ω ω' R) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  letI : Fintype F := Fintype.ofFinite F
  let α : Ω := M.φ.symm (unitaryOuterIsotropicPoint M.J M.hJ 0 (by decide))
  let β : Ω := M.φ.symm (unitaryOuterIsotropicPoint M.J M.hJ 2 (by decide))
  have hP : UnitaryPointStructure ↥N Ω α β M.U' M.T' M.B' := M.hP
  have hB'eq : M.B' = MulAction.stabilizer ↥N α := hP.eq_stabilizer
  have hsupα : M.U' ⊔ M.T' = MulAction.stabilizer ↥N α := hP.sup_eq_stabilizer
  obtain ⟨g, hgα, hgβ, hgT⟩ := hP.exists_conj_torus (a := ω) (y := ω') hne.symm
  have hRleN : R ≤ N := RankOneLocal.le_socle hN h ⟨ω', hne.symm⟩ hR hRn hR2 hreg
  let Q : Subgroup ↥N := M.U'.map (MulAut.conj g).toMonoidHom
  have hU'le : M.U' ≤ MulAction.stabilizer ↥N α := by
    rw [← hsupα]
    exact le_sup_left
  have hU'leB' : M.U' ≤ M.B' := by
    rw [hB'eq, ← hsupα]
    exact le_sup_left
  have hB'norm : M.B' ≤ Subgroup.normalizer (M.U' : Set ↥N) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hU'leB').mp hP.root_normal
  have hQle : Q ≤ MulAction.stabilizer ↥N ω := by
    have h := (Subgroup.map_mono hU'le).trans
      (le_of_eq (MulAction.stabilizer_smul_eq_stabilizer_map_conj g α).symm)
    simpa [Q, hgα] using h
  have hQn : (Q.subgroupOf (MulAction.stabilizer ↥N ω)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQle).mpr ?_
    have h := (Subgroup.map_mono hB'norm).trans
      (Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom)
    rw [show ω = g • α from hgα.symm,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj g α, ← hP.eq_stabilizer]
    exact h
  have hQ2 : IsPGroup 2 Q := M.hdata.isPGroup.map (MulAut.conj g).toMonoidHom
  have hQreg : ∀ x y : Ω, x ≠ ω → y ≠ ω → ∃! q : Q, (q : ↥N) • x = y := by
    intro x y hx hy
    have h := UnitaryPointStructure.regular_map_conj hP.regular g x y
      (by simpa [hgα] using hx) (by simpa [hgα] using hy)
    simpa [Q] using h
  let RN₀ : Subgroup ↥N := R.subgroupOf N
  have hRN₀le : RN₀ ≤ MulAction.stabilizer ↥N ω := by
    intro r hr
    change (r : X) • ω = ω
    exact MulAction.mem_stabilizer_iff.mp (hR hr)
  have hRN₀n : (RN₀.subgroupOf (MulAction.stabilizer ↥N ω)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hRN₀le]
    intro r n hr hn
    change (n : X) * (r : X) * (n : X)⁻¹ ∈ R
    exact (Subgroup.normal_subgroupOf_iff hR).mp hRn (r : X) (n : X) hr
      (MulAction.mem_stabilizer_iff.mp hn)
  have hRN₀2 : IsPGroup 2 RN₀ := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRleN).symm
  have hRN₀reg : ∀ x y : Ω, x ≠ ω → y ≠ ω → ∃! r : RN₀, (r : ↥N) • x = y := by
    intro x y hx hy
    obtain ⟨r, hr, huniq⟩ := hreg x y hx hy
    refine ⟨⟨⟨r, hRleN r.2⟩, r.2⟩, ?_, ?_⟩
    · simpa using hr
    · intro s hs
      apply Subtype.ext
      apply Subtype.ext
      have hs' : ((s : ↥N) : X) • x = y := hs
      exact congrArg (fun t : R => (t : X)) (huniq ⟨(s : ↥N), s.2⟩ hs')
  have hTodd : Odd (Nat.card ↥(MulAction.stabilizer ↥N ω ⊓
      MulAction.stabilizer ↥N ω')) := by
    rw [hgT, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hP.odd_T
  have hRNQ : RN₀ = Q :=
    eq_of_normal_root hne hRN₀le hRN₀n hRN₀2 hRN₀reg hQle hQn hQ2 hQreg hTodd
  obtain ⟨S₀, hS₀⟩ := M.hdata.isSylow
  let S : Sylow 2 ↥N := S₀.mapSurjective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective
  have hScoe : (S : Subgroup ↥N) = Q := by
    dsimp only [S]
    rw [Sylow.coe_mapSurjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective, hS₀]
  let RN : Subgroup ↥N := (S : Subgroup ↥N)
  have hRN_eq : RN = R.subgroupOf N := hScoe.trans hRNQ.symm
  let U : Subgroup ↥N :=
    (CFSG.omega₁ (G := (S : Subgroup ↥N)) (p := 2)).map (S : Subgroup ↥N).subtype
  obtain ⟨⟨ε, hεroot, hεcenter, hεA⟩, hUcenterS, hInjS, ⟨D, hDbot, hDsup, hDnorm, hDcard,
      hDdih⟩, hsq, hfix, hElem, hUcardMap⟩ :=
    CFSG.ProperTwoGeneratedCore.RootCenter.even_unitary_root_center_automorphisms_of_mulEquiv
      M.J k hk hF M.hfixed M.hJ M.eN S U rfl
  have hUcenter : ∀ x : ↥N, x ∈ U ↔ x ∈ RN ∧ ∀ y ∈ RN, x * y = y * x := by
    intro x
    rw [hUcenterS]
  have hUleRN : U ≤ RN := fun x hx => (hUcenter x).mp hx |>.1
  have hcardUmap : Nat.card ↥(U.map (MulAut.conj (G := ↥N))) = Nat.card ↥U := by
    change Nat.card ↥((MulAut.conj (G := ↥N)) '' (U : Set ↥N)) = Nat.card ↥U
    exact Nat.card_image_of_injOn (hInjS.mono hUleRN)
  have hUcard : Nat.card U = 2 ^ k := by
    rw [← hcardUmap]
    exact hUcardMap
  have hcardQ : Nat.card Q = (2 ^ k) ^ 3 := by
    dsimp [Q]
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact M.hcardU'
  have hcardRN : Nat.card RN = (2 ^ k) ^ 3 := by
    rw [show RN = Q from hScoe, hcardQ]
  have hcardR : Nat.card R = (2 ^ k) ^ 3 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRleN).toEquiv]
    rw [show R.subgroupOf N = RN from hRN_eq.symm, hcardRN]
  have hNnoncomm : ¬ IsMulCommutative ↥N := by
    intro hcomm
    have hRNleU : RN ≤ U := by
      intro x hx
      exact (hUcenter x).mpr ⟨hx, fun y _ => (IsMulCommutative.is_comm (M := ↥N)).comm x y⟩
    have hle := Subgroup.card_le_of_le hRNleU
    rw [hcardRN, hUcard] at hle
    have hq4 : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hqpos : 0 < 2 ^ k := by positivity
    have hlt : 2 ^ k < (2 ^ k) ^ 3 := by nlinarith
    exact (Nat.not_lt.mpr hle) hlt
  have hcent : Subgroup.centralizer (N : Set X) = ⊥ :=
    centralizer_eq_bot_of_isMultiplyPretransitive hNnoncomm h2
  have hsigma_inj : Function.Injective (MulAut.conjNormal (G := X) (H := N)) := by
    intro a b hab
    have hmem : a * b⁻¹ ∈ (MulAut.conjNormal (G := X) (H := N)).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel]
    have hker : (MulAut.conjNormal (G := X) (H := N)).ker =
        Subgroup.centralizer (N : Set X) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_centralizer_iff]
        intro n hn
        change MulAut.conjNormal (G := X) (H := N) x = 1 at hx
        have h := congrArg (fun f : MulAut ↥N => (f ⟨n, hn⟩ : ↥N)) hx
        have hX := congrArg (fun y : ↥N => (y : X)) h
        rw [MulAut.conjNormal_apply] at hX
        simp only [MulAut.one_apply, Subgroup.coe_one, mul_one] at hX
        have h' : x * n * x⁻¹ = n := hX
        have h2 : x * n = n * x := by
          calc x * n = (x * n * x⁻¹) * x := by group
            _ = n * x := by rw [h']
        exact h2.symm
      · intro hx
        change MulAut.conjNormal (G := X) (H := N) x = 1
        apply MulEquiv.ext
        intro n
        apply Subtype.ext
        show x * (n : X) * x⁻¹ = (n : X)
        have h := Subgroup.mem_centralizer_iff.mp hx (n : X) n.2
        rw [← h]
        group
    rw [hker, hcent, Subgroup.mem_bot] at hmem
    calc a = (a * b⁻¹) * b := by group
      _ = b := by rw [hmem, one_mul]
  have hcenterU' : {x : ↥N | x ∈ M.U' ∧ ∀ y ∈ M.U', x * y = y * x} =
      ((unitaryRootCenter M.J M.hJ).map M.eN.symm.toMonoidHom : Set ↥N) :=
    center_unitaryRootCenter_eq hk hF M
  let UC : Subgroup ↥N := (unitaryRootCenter M.J M.hJ).map M.eN.symm.toMonoidHom
  have hU_eq : U = UC.map (MulAut.conj g).toMonoidHom := by
    ext x
    have hxU_iff : x ∈ U ↔ x ∈ Q ∧ ∀ y ∈ Q, x * y = y * x := by
      rw [hUcenter x, show RN = Q from hScoe]
    rw [hxU_iff]
    change (x ∈ M.U'.map (MulAut.conj g).toMonoidHom ∧
      ∀ y ∈ M.U'.map (MulAut.conj g).toMonoidHom, x * y = y * x) ↔
        x ∈ UC.map (MulAut.conj g).toMonoidHom
    have hmem := mem_center_map_conj (U := M.U') (g := g) (x := x)
    rw [hmem]
    constructor
    · rintro ⟨u, hu, hcomm, rfl⟩
      refine Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ?_
      have hmemU : u ∈ UC := by
        change u ∈ ((unitaryRootCenter M.J M.hJ).map M.eN.symm.toMonoidHom : Set ↥N)
        rw [← hcenterU']
        exact ⟨hu, hcomm⟩
      exact hmemU
    · intro hx
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have hu' : u ∈ M.U' ∧ ∀ v ∈ M.U', u * v = v * u := by
        have h : u ∈ ((unitaryRootCenter M.J M.hJ).map M.eN.symm.toMonoidHom : Set ↥N) :=
          hu
        rw [← hcenterU'] at h
        exact h
      exact ⟨u, hu'.1, hu'.2, rfl⟩
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * k) (by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have htrans : ∀ u v : ↥N, u ∈ U → v ∈ U → u ≠ 1 → v ≠ 1 →
      ∃ s : ↥N, (s : X) ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω' ∧
        (s : X) * (u : X) * (s : X)⁻¹ = (v : X) := by
    intro u v hu hv hu1 hv1
    rw [hU_eq] at hu hv
    obtain ⟨u₀, hu₀, hu_eq⟩ := Subgroup.mem_map.mp hu
    obtain ⟨v₀, hv₀, hv_eq⟩ := Subgroup.mem_map.mp hv
    obtain ⟨uu, huu, huu_eq⟩ := Subgroup.mem_map.mp hu₀
    obtain ⟨vv, hvv, hvv_eq⟩ := Subgroup.mem_map.mp hv₀
    have hu_expr : u = MulAut.conj g (M.eN.symm uu) := by
      rw [← hu_eq, ← huu_eq]
      rfl
    have hv_expr : v = MulAut.conj g (M.eN.symm vv) := by
      rw [← hv_eq, ← hvv_eq]
      rfl
    have huu1 : uu ≠ 1 := by
      intro h1
      apply hu1
      rw [hu_expr, h1]
      simp
    have hvv1 : vv ≠ 1 := by
      intro h1
      apply hv1
      rw [hv_expr, h1]
      simp
    have huu1' : (⟨uu, huu⟩ : ↥(unitaryRootCenter M.J M.hJ)) ≠ 1 := by
      intro h
      apply huu1
      exact congrArg Subtype.val h
    have hvv1' : (⟨vv, hvv⟩ : ↥(unitaryRootCenter M.J M.hJ)) ≠ 1 := by
      intro h
      apply hvv1
      exact congrArg Subtype.val h
    obtain ⟨τ, hτ, hτconj⟩ :=
      torusPSU_transitive_rootCenter M.J M.hJ k hF M.hfixed ⟨uu, huu⟩ ⟨vv, hvv⟩
        huu1' hvv1'
    let t' : ↥N := M.eN.symm τ
    have ht'T : t' ∈ M.T' := by
      rw [M.hT']
      exact Subgroup.mem_map_of_mem _ hτ
    let s : ↥N := MulAut.conj g t'
    have hsT : s ∈ MulAction.stabilizer ↥N ω ⊓ MulAction.stabilizer ↥N ω' := by
      rw [hgT]
      exact Subgroup.mem_map_of_mem _ ht'T
    refine ⟨s, ?_, ?_⟩
    · rw [UnitaryPointStructure.pair_eq_stabilizer_inf]
      exact Subgroup.mem_map_of_mem _ hsT
    · rw [hu_expr, hv_expr]
      have hconjN : s * MulAut.conj g (M.eN.symm uu) * s⁻¹ =
          MulAut.conj g (M.eN.symm vv) := by
        have h1 : t' * M.eN.symm uu * t'⁻¹ = M.eN.symm vv := by
          apply M.eN.injective
          simpa [t'] using hτconj
        calc s * MulAut.conj g (M.eN.symm uu) * s⁻¹
            = MulAut.conj g (t' * M.eN.symm uu * t'⁻¹) := by
              simp [s, MulAut.conj_apply]
              group
          _ = MulAut.conj g (M.eN.symm vv) := by rw [h1]
      exact congrArg N.subtype hconjN
  obtain ⟨c, hc, hτne, hτU⟩ :=
    exists_torus_centralizing_rootCenter M.J M.hJ k hk M.hconj hF
  let τ := torusPSU M.J M.hJ c
  let t' : ↥N := M.eN.symm τ
  have ht'T : t' ∈ M.T' := by
    rw [M.hT']
    exact Subgroup.mem_map_of_mem _ ⟨c, rfl⟩
  let t : ↥N := MulAut.conj g t'
  have htT : t ∈ MulAction.stabilizer ↥N ω ⊓ MulAction.stabilizer ↥N ω' := by
    rw [hgT]
    exact Subgroup.mem_map_of_mem _ ht'T
  have ht_ne : t ≠ 1 := by
    intro h1
    have h2 : t' = 1 := (MulAut.conj g).injective (by simpa [t] using h1)
    have h3 : τ = 1 := M.eN.symm.injective (by simpa [t'] using h2)
    exact hτne h3
  have ht_center : ∀ u ∈ U, MulAut.conj t u = u := by
    intro u hu
    rw [hU_eq] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨uu, huu, rfl⟩ := Subgroup.mem_map.mp hu₀
    have hcomm : Commute (M.eN.symm τ) (M.eN.symm uu) :=
      ((hτU uu huu).map M.eN.symm.toMonoidHom).symm
    rw [MulAut.conj_apply]
    calc (t * (MulAut.conj g (M.eN.symm uu)) * t⁻¹ : ↥N)
        = MulAut.conj g ((M.eN.symm τ) * (M.eN.symm uu) * (M.eN.symm τ)⁻¹) := by
            simp only [t, t', MulAut.conj_apply]
            group
      _ = MulAut.conj g (M.eN.symm uu) := by
            congr 1
            rw [hcomm.eq]
            group
  have hRNle : RN ≤ MulAction.stabilizer ↥N ω := by
    rw [hRN_eq]
    exact hRN₀le
  have hRNn : (RN.subgroupOf (MulAction.stabilizer ↥N ω)).Normal := by
    rw [hRN_eq]
    exact hRN₀n
  have hnormstab : MulAction.stabilizer ↥N ω ≤ Subgroup.normalizer (RN : Set ↥N) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRNle).mp hRNn
  have ht_normalizer : t ∈ Subgroup.normalizer (RN : Set ↥N) := hnormstab htT.1
  have ht_A : MulAut.conj t ∈ rootCenterAut RN U := by
    refine (mem_rootCenterAut).mpr ⟨?_, ht_center⟩
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).mp ht_normalizer
  exact ⟨{
    RN := RN
    RN_eq := hRN_eq
    root_le := hR
    root_normal := hRn
    card_R := hcardR
    card_RN := hcardRN
    U := U
    U_eq := rfl
    U_center := hUcenter
    U_card := hUcard
    A := rootCenterAut RN U
    A_eq := rfl
    D := D
    inf_D := hDbot
    sup_D := hDsup
    normal_C := hDnorm
    card_D := hDcard
    D_dih := hDdih
    inj_conj := hInjS
    RN_2 := S.isPGroup'
    C_2 := S.isPGroup'.map (MulAut.conj (G := ↥N))
    card_C := by
      change Nat.card ↥((MulAut.conj (G := ↥N)) '' (RN : Set ↥N)) = (2 ^ k) ^ 3
      rw [Nat.card_image_of_injOn hInjS]
      exact hcardRN
    sigma_inj := hsigma_inj
    t := t
    t_ne := ht_ne
    t_mem := by
      rw [UnitaryPointStructure.pair_eq_stabilizer_inf]
      exact Subgroup.mem_map_of_mem _ htT
    t_center := ht_center
    t_A := ht_A
    transitive := htrans }⟩

private lemma map_conjNormal_root_eq {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [Field F] [Finite F] {N : Subgroup X} [N.Normal] {k : ℕ}
    {M : PSU3IsotropicModel X Ω F N k} {ω ω' : Ω} {R : Subgroup X}
    (S : PSU3RootData k M ω ω' R) {g : X} (hg : g ∈ MulAction.stabilizer X ω) :
    S.RN.map (MulAut.conjNormal (G := X) (H := N) g).toMonoidHom = S.RN := by
  rw [S.RN_eq]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change g * (x : X) * g⁻¹ ∈ R
    exact (Subgroup.normal_subgroupOf_iff S.root_le).mp S.root_normal (x : X) g hx hg
  · intro hy
    refine ⟨⟨g⁻¹ * (y : X) * g, ?_⟩, ?_, ?_⟩
    · simpa using Subgroup.Normal.conj_mem ‹N.Normal› (y : X) y.2 g⁻¹
    · change g⁻¹ * (y : X) * g ∈ R
      simpa using (Subgroup.normal_subgroupOf_iff S.root_le).mp S.root_normal (y : X) g⁻¹ hy
        ((MulAction.stabilizer X ω).inv_mem hg)
    · apply Subtype.ext
      change g * (g⁻¹ * (y : X) * g) * g⁻¹ = (y : X)
      group

private lemma conjNormal_mem_U {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [Field F] [Finite F] {N : Subgroup X} [N.Normal] {k : ℕ}
    {M : PSU3IsotropicModel X Ω F N k} {ω ω' : Ω} {R : Subgroup X}
    (S : PSU3RootData k M ω ω' R) {g : X} (hg : g ∈ MulAction.stabilizer X ω)
    {u : ↥N} (hu : u ∈ S.U) :
    MulAut.conjNormal (G := X) (H := N) g u ∈ S.U := by
  have hmap := map_conjNormal_root_eq S hg
  have hu' := (S.U_center u).mp hu
  refine (S.U_center _).mpr ⟨?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hu'.1
  · intro y hy
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact hy)
    calc (MulAut.conjNormal (G := X) (H := N) g u) *
          (MulAut.conjNormal (G := X) (H := N) g v)
        = MulAut.conjNormal (G := X) (H := N) g (u * v) := (map_mul _ _ _).symm
      _ = MulAut.conjNormal (G := X) (H := N) g (v * u) := by rw [hu'.2 v hv]
      _ = (MulAut.conjNormal (G := X) (H := N) g v) *
          (MulAut.conjNormal (G := X) (H := N) g u) := map_mul _ _ _

private lemma conjNormal_mem_A {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [Field F] [Finite F] {N : Subgroup X} [N.Normal] {k : ℕ}
    {M : PSU3IsotropicModel X Ω F N k} {ω ω' : Ω} {R : Subgroup X}
    (S : PSU3RootData k M ω ω' R) {g : X} (hg : g ∈ MulAction.stabilizer X ω)
    (hfix : ∀ u ∈ S.U, MulAut.conjNormal (G := X) (H := N) g u = u) :
    MulAut.conjNormal (G := X) (H := N) g ∈ S.A := by
  rw [S.A_eq]
  exact (mem_rootCenterAut).mpr ⟨map_conjNormal_root_eq S hg, hfix⟩

private lemma psu3_center_le {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] [Field F] [Finite F] {N : Subgroup X}
    (hN : N.Normal) {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = (2 ^ k) ^ 2)
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2)
    (M : PSU3IsotropicModel X Ω F N k) (h : RankOneLocal X Ω N) :
    ∀ (ω ω' : Ω), ω ≠ ω' → ∀ R Z : Subgroup X,
      R ≤ MulAction.stabilizer X ω →
      (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
      (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
      Z ≤ R → (∀ r ∈ R, ∀ y ∈ Z, r * y = y * r) →
      (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
        ∀ y ∈ Z, t * y * t⁻¹ ∈ Z) → Z ≠ ⊥ →
      ∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Z := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  letI : Fintype F := Fintype.ofFinite F
  intro ω ω' hne R Z hR hRn hR2 hreg hZR hZcent hZinv hZne y hyR hycent
  obtain ⟨S⟩ := exists_rootData hN hk hF h2 M h hne R hR hRn hR2 hreg
  have hRleN : R ≤ N := RankOneLocal.le_socle hN h ⟨ω', hne.symm⟩ hR hRn hR2 hreg
  have hZleN : Z ≤ N := hZR.trans hRleN
  have hZleU : Z ≤ S.U.map N.subtype := by
    intro z hz
    have hzN : (⟨z, hZleN hz⟩ : ↥N) ∈ S.U := by
      refine (S.U_center _).mpr ⟨?_, ?_⟩
      · rw [S.RN_eq]
        exact hZR hz
      · intro w hw
        rw [S.RN_eq] at hw
        change (w : X) ∈ R at hw
        apply Subtype.ext
        exact (hZcent (w : X) hw (z : X) hz).symm
    exact Subgroup.mem_map_of_mem _ hzN
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  have hzZ : (z : X) ∈ Z := z.2
  have hzN : (⟨(z : X), hZleN hzZ⟩ : ↥N) ∈ S.U := by
    refine (S.U_center _).mpr ⟨?_, ?_⟩
    · rw [S.RN_eq]
      exact hZR hzZ
    · intro w hw
      rw [S.RN_eq] at hw
      change (w : X) ∈ R at hw
      apply Subtype.ext
      exact (hZcent (w : X) hw (z : X) hzZ).symm
  have hzN1 : (⟨(z : X), hZleN hzZ⟩ : ↥N) ≠ 1 := by
    intro h1
    apply hz1
    apply Subtype.ext
    exact congrArg (fun t : ↥N => (t : X)) h1
  have hUleZ : S.U.map N.subtype ≤ Z := by
    intro u hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    by_cases hu₀1 : u₀ = 1
    · subst hu₀1
      simp
    · obtain ⟨t, htT, htconj⟩ :=
        S.transitive ⟨(z : X), hZleN hzZ⟩ u₀ hzN hu₀ hzN1 hu₀1
      have hmem : (t : X) * (z : X) * (t : X)⁻¹ ∈ Z := hZinv t htT (z : X) hzZ
      rwa [htconj] at hmem
  have hyN : (⟨y, hRleN hyR⟩ : ↥N) ∈ S.U := by
    refine (S.U_center _).mpr ⟨?_, ?_⟩
    · rw [S.RN_eq]
      exact hyR
    · intro w hw
      rw [S.RN_eq] at hw
      change (w : X) ∈ R at hw
      apply Subtype.ext
      exact (hycent (w : X) hw).symm
  exact hUleZ (Subgroup.mem_map_of_mem _ hyN)

private lemma psu3_centralizer_center {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] [Field F] [Finite F] {N : Subgroup X}
    (hN : N.Normal) {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = (2 ^ k) ^ 2)
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2)
    (M : PSU3IsotropicModel X Ω F N k) (h : RankOneLocal X Ω N) :
    ∀ (ω ω' : Ω), ω ≠ ω' → ∀ R : Subgroup X,
      R ≤ MulAction.stabilizer X ω →
      (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
      (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
      ∀ g ∈ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', Odd (orderOf g) →
      (∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → g * y = y * g) →
      g ^ (2 ^ k + 1) = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  letI : Fintype F := Fintype.ofFinite F
  intro ω ω' hne R hR hRn hR2 hreg g hg hodd hgU
  obtain ⟨S⟩ := exists_rootData hN hk hF h2 M h hne R hR hRn hR2 hreg
  have hRleN : R ≤ N := RankOneLocal.le_socle hN h ⟨ω', hne.symm⟩ hR hRn hR2 hreg
  let T : Subgroup X := N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
  let σ : X →* MulAut ↥N := MulAut.conjNormal (G := X) (H := N)
  have hgnorm : g ∈ MulAction.stabilizer X ω := hg.1
  have hσg_fix : ∀ u ∈ S.U, σ g u = u := by
    intro u hu
    have hu' := (S.U_center u).mp hu
    have huR : (u : X) ∈ R := by
      rw [S.RN_eq] at hu'
      exact hu'.1
    have hcent : ∀ r ∈ R, r * (u : X) = (u : X) * r := by
      intro r hr
      have hrN : (⟨r, hRleN hr⟩ : ↥N) ∈ S.RN := by
        rw [S.RN_eq]
        exact hr
      have h := hu'.2 ⟨r, hRleN hr⟩ hrN
      simpa using (congrArg Subtype.val h).symm
    have hcomm : g * (u : X) = (u : X) * g := hgU (u : X) huR hcent
    apply Subtype.ext
    change ((MulAut.conjNormal (G := X) (H := N) g) u : X) = (u : X)
    rw [MulAut.conjNormal_apply]
    rw [hcomm]
    group
  have hσgA : σ g ∈ S.A := conjNormal_mem_A S hgnorm hσg_fix
  have hoddσ : Odd (orderOf (σ g)) := hodd.of_dvd_nat (orderOf_map_dvd σ g)
  have hC_le_A : S.RN.map (MulAut.conj (G := ↥N)) ≤ S.A := by
    rw [← S.sup_D]
    exact le_sup_left
  have hOddm : Odd (2 ^ k + 1) := by
    have hqeven : Even (2 ^ k) := (show Even 2 from ⟨1, rfl⟩).pow_of_ne_zero (by omega : k ≠ 0)
    simpa [Nat.add_comm] using Odd.add_even odd_one hqeven
  have hpowC : (σ g) ^ (2 ^ k + 1) ∈ S.RN.map (MulAut.conj (G := ↥N)) :=
    dihedral_odd_pow_mem_complement hC_le_A S.normal_C S.inf_D S.sup_D S.D_dih
      (σ g) hσgA hoddσ
  have hpow1 : (σ g) ^ (2 ^ k + 1) = 1 := by
    by_contra hne
    let γ : ↥(S.RN.map (MulAut.conj (G := ↥N))) := ⟨(σ g) ^ (2 ^ k + 1), hpowC⟩
    have hγne : γ ≠ 1 := fun h => hne (congrArg Subtype.val h)
    have h2dvdγ : 2 ∣ orderOf γ := S.C_2.dvd_orderOf hγne
    have h2dvd : 2 ∣ orderOf ((σ g) ^ (2 ^ k + 1)) := by
      rw [Subgroup.orderOf_coe γ]
      exact h2dvdγ
    have hoddpow : Odd (orderOf ((σ g) ^ (2 ^ k + 1))) :=
      hoddσ.of_dvd_nat (orderOf_pow_dvd (x := σ g) (n := 2 ^ k + 1))
    exact (Nat.not_even_iff_odd.mpr hoddpow) (even_iff_two_dvd.mpr h2dvd)
  have hσpow : σ (g ^ (2 ^ k + 1)) = 1 := by
    rw [map_pow, hpow1]
  exact S.sigma_inj (by simpa using hσpow)

private lemma pSingular_mem_of_mul {M : Type*} [Group M] [Finite M] {A : Subgroup M}
    {a x y : M} (ha : a ∈ A) (hxy : x * y = a) (hyx : y * x = a)
    (hx : IsPSingular 2 x) (hy : IsPRegular 2 y) : x ∈ A := by
  have hcomm : Commute x y := (commute_iff_eq x y).mpr (hxy.trans hyx.symm)
  have hfin : IsOfFinOrder a := by
    rw [← hxy]
    exact hcomm.isOfFinOrder_mul (isOfFinOrder_of_finite x) (isOfFinOrder_of_finite y)
  obtain ⟨hxeq, -⟩ := Group.pSingular_pRegular_unique 2 hfin hxy hyx hx hy
  rw [hxeq]
  have hmem : Group.pSingular 2 a ∈ Subgroup.zpowers a := by
    unfold Group.pSingular
    exact Subgroup.zpow_mem_zpowers _ _
  exact Subgroup.zpowers_le.mpr ha hmem

private lemma centralizes_of_fixing_one {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [Field F] [Finite F] {N : Subgroup X} [N.Normal] {k : ℕ}
    {M : PSU3IsotropicModel X Ω F N k} {ω ω' : Ω} {R : Subgroup X}
    (S : PSU3RootData k M ω ω' R) {h : X} {u₀ : ↥N} (hu₀ : u₀ ∈ S.U) (hu₀1 : u₀ ≠ 1)
    (hcomm : ∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
      h * t = t * h)
    (hfix : h * (u₀ : X) * h⁻¹ = (u₀ : X)) :
    ∀ u ∈ S.U, h * (u : X) * h⁻¹ = (u : X) := by
  intro u hu
  by_cases hu1 : u = 1
  · subst hu1
    simp
  · obtain ⟨t, htT, htconj⟩ := S.transitive u₀ u hu₀ hu hu₀1 hu1
    have hcommt : h * (t : X) = (t : X) * h := hcomm t htT
    have hcommtinv : (t : X)⁻¹ * h⁻¹ = h⁻¹ * (t : X)⁻¹ := by
      have h := congrArg (fun z : X => z⁻¹) hcommt
      simpa [_root_.mul_inv_rev] using h
    calc h * (u : X) * h⁻¹
        = h * ((t : X) * (u₀ : X) * (t : X)⁻¹) * h⁻¹ := by rw [htconj]
      _ = (h * (t : X)) * (u₀ : X) * ((t : X)⁻¹ * h⁻¹) := by group
      _ = ((t : X) * h) * (u₀ : X) * (h⁻¹ * (t : X)⁻¹) := by
          rw [hcommt, hcommtinv]
      _ = (t : X) * (h * (u₀ : X) * h⁻¹) * (t : X)⁻¹ := by group
      _ = (t : X) * (u₀ : X) * (t : X)⁻¹ := by rw [hfix]
      _ = (u : X) := htconj

private lemma psu3_centralizer {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] [Field F] [Finite F] {N : Subgroup X}
    (hN : N.Normal) {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = (2 ^ k) ^ 2)
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2)
    (M : PSU3IsotropicModel X Ω F N k) (h : RankOneLocal X Ω N) :
    ∀ (ω ω' : Ω), ω ≠ ω' → ∀ g ∈
      MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
      (∃ n : ℕ, g ^ 2 ^ n = 1) →
      (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', g * t = t * g) →
      g = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : N.Normal := hN
  letI : Fintype F := Fintype.ofFinite F
  intro ω ω' hne g hg hg2 hgT
  obtain ⟨R, hR, hRn, hR2, hreg⟩ := h.root ω
  obtain ⟨S⟩ := exists_rootData hN hk hF h2 M h hne R hR hRn hR2 hreg
  let T : Subgroup X := N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω'
  let σ : X →* MulAut ↥N := MulAut.conjNormal (G := X) (H := N)
  have hgnorm : g ∈ MulAction.stabilizer X ω := hg.1
  have hUne : S.U ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card S.U = 1 := by rw [hbot, Subgroup.card_bot]
    rw [S.U_card] at h1
    have h2 : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
    omega
  obtain ⟨u₀, hu₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
  have hu₀ : (u₀ : ↥N) ∈ S.U := u₀.2
  have hu₀N1 : (u₀ : ↥N) ≠ 1 := fun h => hu₀1 (Subtype.ext h)
  have hσu₀ : σ g (u₀ : ↥N) ∈ S.U := conjNormal_mem_U S hgnorm hu₀
  have hσu₀1 : σ g (u₀ : ↥N) ≠ 1 := by
    intro h1
    apply hu₀N1
    exact (MulEquiv.map_eq_one_iff (σ g)).mp h1
  obtain ⟨t₀, ht₀T, ht₀conj⟩ :=
    S.transitive (u₀ : ↥N) (σ g (u₀ : ↥N)) hu₀ hσu₀ hu₀N1 hσu₀1
  have ht₀X : (t₀ : X) ∈ T := ht₀T
  let hX : X := (t₀ : X)⁻¹ * g
  have hhω : hX ∈ MulAction.stabilizer X ω :=
    (MulAction.stabilizer X ω).mul_mem
      ((MulAction.stabilizer X ω).inv_mem ht₀T.1.2) hgnorm
  have hTcyc : IsCyclic ↥T := h.torus_cyclic ω ω' hne
  letI : CommGroup ↥T := IsCyclic.commGroup
  have hcomm_g_t₀ : g * (t₀ : X) = (t₀ : X) * g := hgT t₀ ht₀X
  have hhT : ∀ t ∈ T, hX * t = t * hX := by
    intro t ht
    have hgt : g * t = t * g := hgT t ht
    have ht₀t : (t₀ : X) * t = t * (t₀ : X) := by
      have h := mul_comm (⟨t₀, ht₀X⟩ : ↥T) (⟨t, ht⟩ : ↥T)
      exact congrArg Subtype.val h
    have ht₀tinv : (t₀ : X)⁻¹ * t = t * (t₀ : X)⁻¹ := by
      calc (t₀ : X)⁻¹ * t
          = (t₀ : X)⁻¹ * (t * (t₀ : X)) * (t₀ : X)⁻¹ := by group
        _ = (t₀ : X)⁻¹ * ((t₀ : X) * t) * (t₀ : X)⁻¹ := by rw [← ht₀t]
        _ = t * (t₀ : X)⁻¹ := by group
    calc hX * t = (t₀ : X)⁻¹ * g * t := by rfl
      _ = (t₀ : X)⁻¹ * (g * t) := by group
      _ = (t₀ : X)⁻¹ * (t * g) := by rw [hgt]
      _ = ((t₀ : X)⁻¹ * t) * g := by group
      _ = (t * (t₀ : X)⁻¹) * g := by rw [ht₀tinv]
      _ = t * ((t₀ : X)⁻¹ * g) := by group
      _ = t * hX := by rfl

  have hh_u₀ : hX * (u₀ : X) * hX⁻¹ = (u₀ : X) := by
    have hσgval : (σ g (u₀ : ↥N) : X) = g * (u₀ : X) * g⁻¹ := by
      change ((MulAut.conjNormal (G := X) (H := N) g) (u₀ : ↥N) : X) =
        g * (u₀ : X) * g⁻¹
      rw [MulAut.conjNormal_apply]
    have h2 : (t₀ : X)⁻¹ * (g * (u₀ : X) * g⁻¹) * (t₀ : X) = (u₀ : X) := by
      have h1 : (t₀ : X)⁻¹ * (σ g (u₀ : ↥N) : X) * (t₀ : X) = (u₀ : X) := by
        calc (t₀ : X)⁻¹ * (σ g (u₀ : ↥N) : X) * (t₀ : X)
            = (t₀ : X)⁻¹ * ((t₀ : X) * (u₀ : X) * (t₀ : X)⁻¹) * (t₀ : X) := by
                rw [ht₀conj]
          _ = (u₀ : X) := by group
      rwa [hσgval] at h1
    calc hX * (u₀ : X) * hX⁻¹
        = (t₀ : X)⁻¹ * g * (u₀ : X) * g⁻¹ * (t₀ : X) := by
            simp only [hX]
            group
      _ = (t₀ : X)⁻¹ * (g * (u₀ : X) * g⁻¹) * (t₀ : X) := by group
      _ = (u₀ : X) := h2

  have hh_fix : ∀ u ∈ S.U, σ hX u = u := by
    intro u hu
    apply Subtype.ext
    exact centralizes_of_fixing_one S hu₀ hu₀N1 (fun t ht => hhT t ht) hh_u₀ u hu
  have hσhA : σ hX ∈ S.A := conjNormal_mem_A S hhω hh_fix
  have hσh_eq : σ hX = (σ (t₀ : X))⁻¹ * σ g := by
    simp only [hX, map_mul, map_inv]
  have hσg_sing : IsPSingular 2 (σ g) := by
    obtain ⟨n, hn⟩ := hg2
    have hdvd : orderOf (σ g) ∣ 2 ^ n :=
      (orderOf_map_dvd σ g).trans (orderOf_dvd_iff_pow_eq_one.mpr hn)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  have hσt0_reg : IsPRegular 2 (σ (t₀ : X))⁻¹ := by
    have hodd : Odd (orderOf (σ (t₀ : X))⁻¹) := by
      rw [orderOf_inv]
      exact (h.torus_odd ω ω' hne).of_dvd_nat
        ((orderOf_map_dvd σ (t₀ : X)).trans (Subgroup.orderOf_dvd_natCard T ht₀X))
    exact Nat.coprime_two_right.mpr hodd
  have hcommσ : ∀ x y : X, x * y = y * x → σ x * σ y = σ y * σ x := by
    intro x y hxy
    simpa [map_mul] using congrArg σ hxy
  have hcommgt : Commute (σ g) (σ (t₀ : X)) :=
    (commute_iff_eq _ _).mpr (hcommσ g (t₀ : X) (hgT t₀ ht₀X))
  have hσgA : σ g ∈ S.A := by
    apply pSingular_mem_of_mul hσhA ?_ ?_ hσg_sing hσt0_reg
    · rw [hσh_eq]
      exact hcommgt.inv_right.eq
    · rw [hσh_eq]
  let O : Subgroup (MulAut ↥N) := Subgroup.zpowers (MulAut.conj S.t)
  have hO_le : O ≤ S.A := Subgroup.zpowers_le.mpr S.t_A
  have hO_odd : Odd (Nat.card O) := by
    rw [show O = Subgroup.zpowers (MulAut.conj S.t) from rfl, Nat.card_zpowers]
    have hdiv : orderOf (MulAut.conj S.t) ∣ Nat.card ↥T :=
      (orderOf_map_dvd (MulAut.conj (G := ↥N)) S.t).trans
        (by simpa [Subgroup.orderOf_coe] using Subgroup.orderOf_dvd_natCard T S.t_mem)
    exact (h.torus_odd ω ω' hne).of_dvd_nat hdiv
  have hO_ne : O ≠ ⊥ := by
    intro hbot
    have h1 : MulAut.conj S.t = 1 := by
      have hmem : MulAut.conj S.t ∈ O := Subgroup.mem_zpowers _
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have h2 : σ (S.t : X) = 1 := by
      rwa [show σ (S.t : X) = MulAut.conj S.t from MulAut.conjNormal_val]
    have h3 : (S.t : X) = 1 := S.sigma_inj (by simpa using h2)
    exact S.t_ne (Subtype.ext h3)
  have hO_inf_C : O ⊓ S.RN.map (MulAut.conj (G := ↥N)) = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [S.card_C]
    exact (by
      simpa [pow_mul, mul_comm] using
        (Nat.coprime_two_right.mpr hO_odd).pow_right (3 * k))
  have hcommO : ∀ o ∈ O, σ g * o = o * σ g := by
    intro o ho
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ho
    have hσt : σ g * σ (S.t : X) = σ (S.t : X) * σ g :=
      hcommσ g (S.t : X) (hgT S.t S.t_mem)
    have hσt' : σ g * MulAut.conj S.t = MulAut.conj S.t * σ g := by
      rwa [show σ (S.t : X) = MulAut.conj S.t from MulAut.conjNormal_val] at hσt
    exact (commute_iff_eq (σ g) (MulAut.conj S.t)).mpr hσt' |>.zpow_right n
  have hOddm : Odd (2 ^ k + 1) := by
    have hqeven : Even (2 ^ k) := (show Even 2 from ⟨1, rfl⟩).pow_of_ne_zero (by omega : k ≠ 0)
    simpa [Nat.add_comm] using Odd.add_even odd_one hqeven
  have hC_le_A : S.RN.map (MulAut.conj (G := ↥N)) ≤ S.A := by
    rw [← S.sup_D]
    exact le_sup_left
  have hσgC : σ g ∈ S.RN.map (MulAut.conj (G := ↥N)) :=
    dihedral_two_element_mem_complement hC_le_A S.normal_C S.inf_D S.sup_D S.D_dih hOddm
      hO_le hO_odd hO_inf_C hO_ne (σ g) hσgA hσg_sing hcommO
  obtain ⟨r, hrRN, hrconj⟩ := Subgroup.mem_map.mp hσgC
  have hσr : σ (r : X) = MulAut.conj r := MulAut.conjNormal_val
  have hgr : g = (r : X) :=
    S.sigma_inj (by rw [hσr, hrconj])
  have hrR : (r : X) ∈ R := by
    rw [S.RN_eq] at hrRN
    exact hrRN
  have hgR : g ∈ R := by
    rw [hgr]
    exact hrR
  have hgfix : (g : X) • ω' = ω' := MulAction.mem_stabilizer_iff.mp hg.2
  have huniq := hreg ω' ω' hne.symm hne.symm
  have hg1 : (⟨g, hgR⟩ : R) = 1 := by
    apply huniq.unique
    · show (g : X) • ω' = ω'
      exact hgfix
    · simp
  simpa using congrArg Subtype.val hg1

private structure PSU3Conditions {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] [Field F] [Finite F] (N : Subgroup X) (k : ℕ) : Prop where
  isLocal : RankOneLocal X Ω N
  centralizer : ∀ ω ω' : Ω, ω ≠ ω' → ∀ g ∈
    MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω',
    (∃ n : ℕ, g ^ 2 ^ n = 1) →
    (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', g * t = t * g) →
    g = 1
  center_le : ∀ (ω ω' : Ω), ω ≠ ω' → ∀ R Z : Subgroup X,
    R ≤ MulAction.stabilizer X ω →
    (R.subgroupOf (MulAction.stabilizer X ω)).Normal → IsPGroup 2 R →
    (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    Z ≤ R → (∀ r ∈ R, ∀ y ∈ Z, r * y = y * r) →
    (∀ t ∈ N ⊓ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', ∀ y ∈ Z,
      t * y * t⁻¹ ∈ Z) → Z ≠ ⊥ →
    ∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → y ∈ Z
  centralizer_center : ∀ (ω ω' : Ω), ω ≠ ω' → ∀ R : Subgroup X,
    R ≤ MulAction.stabilizer X ω → (R.subgroupOf (MulAction.stabilizer X ω)).Normal →
    IsPGroup 2 R → (∀ α β : Ω, α ≠ ω → β ≠ ω → ∃! r : R, (r : X) • α = β) →
    ∀ g ∈ MulAction.stabilizer X ω ⊓ MulAction.stabilizer X ω', Odd (orderOf g) →
      (∀ y ∈ R, (∀ r ∈ R, r * y = y * r) → g * y = y * g) → g ^ (2 ^ k + 1) = 1

private lemma psu3_conditions {X Ω F : Type} [Group X] [Finite X] [Fintype Ω]
    [MulAction X Ω] [FaithfulSMul X Ω] [Field F] [Finite F] {N : Subgroup X}
    (hN : N.Normal) {k : ℕ} (hk : 2 ≤ k) (hF : Nat.card F = (2 ^ k) ^ 2)
    (h2 : MulAction.IsMultiplyPretransitive X Ω 2)
    (M : PSU3IsotropicModel X Ω F N k) (h : RankOneLocal X Ω N) :
    PSU3Conditions (Ω := Ω) (F := F) N k := by
  refine
    { isLocal := h
      centralizer := psu3_centralizer hN hk hF h2 M h
      center_le := psu3_center_le hN hk hF h2 M h
      centralizer_center := psu3_centralizer_center hN hk hF h2 M h }

theorem rankOneNonabelian_psu3 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (k : ℕ) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))
    (hΩ : Fintype.card Ω = 2 ^ (3 * k) + 1) :
    RankOneNonabelian X Ω := by
  refine ⟨?not_comm⟩
  intro ω R hR hRn hR2 hreg
  have hdeg : ∃ e : ℕ, 1 ≤ e ∧ Fintype.card Ω = 1 + 2 ^ e := by
    refine ⟨3 * k, by omega, ?_⟩
    rw [hΩ]
    exact Nat.add_comm _ 1
  have hcopy : HasNormalCopy X (StatedProj (StatedSU 3 (2 ^ k) F)) := ⟨N, hN, ⟨e⟩⟩
  exact subconstUnitaryNonabelian X Ω k F hk hF h2 hdeg hcopy ω R hR hreg

theorem rankOneRoot_psu3 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (k : ℕ) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))
    (hΩ : Fintype.card Ω = 2 ^ (3 * k) + 1) :
    RankOneRoot X Ω N := by
  classical
  letI : N.Normal := hN
  letI : Fintype F := Fintype.ofFinite F
  let M := Classical.choice (exists_psu3_isotropicModel h2 k hk F hF N hN e hΩ)
  let h : RankOneLocal X Ω N := rankOneLocal_psu3 h2 k hk F hF N hN e hΩ
  exact h.rankOneRoot_of_centralizer (psu3_conditions hN hk hF h2 M h).centralizer

theorem rankOneCenter_psu3 {X Ω : Type} [Group X] [Finite X] [Fintype Ω] [MulAction X Ω]
    [FaithfulSMul X Ω] (h2 : MulAction.IsMultiplyPretransitive X Ω 2) (k : ℕ) (hk : 2 ≤ k)
    (F : Type) [Field F] [Finite F] (hF : Nat.card F = (2 ^ k) ^ 2)
    (N : Subgroup X) (hN : N.Normal) (e : ↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))
    (hΩ : Fintype.card Ω = 2 ^ (3 * k) + 1) :
    RankOneCenter X Ω N (2 ^ k + 1) := by
  classical
  letI : N.Normal := hN
  letI : Fintype F := Fintype.ofFinite F
  let M := Classical.choice (exists_psu3_isotropicModel h2 k hk F hF N hN e hΩ)
  let h : RankOneLocal X Ω N := rankOneLocal_psu3 h2 k hk F hF N hN e hΩ
  have hC := psu3_conditions hN hk hF h2 M h
  have hA7 : RankOneRoot X Ω N := h.rankOneRoot_of_centralizer hC.centralizer
  exact
    { centralizer_le := RankOneRoot.centralizer_le hA7
      center_le := hC.center_le
      centralizer_center := hC.centralizer_center }

end CFSG.Quasithin.Stroth.WeissDelta

end
