module

public import CFSG.Quasithin.Vol2.E2SevenKG1
public import CFSG.Quasithin.Vol2.E2SevenKG2U3
public import CFSG.Quasithin.H13.L32ACSkPfU3
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.B6Offenders
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS4
public import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open Matrix CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryModel
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth

variable {G : Type} [Group G] [Finite G]

theorem comm_of_involution_of_isPSU3 {K S : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hK : IsPSU 3 2 n ↥K) (hS : IsSylowTwoOf S K) :
    ∀ x ∈ S, x ^ 2 = 1 → ∀ y ∈ S, x * y = y * x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hx2 y hy
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  obtain ⟨e⟩ := nonempty_mulEquiv_psu_binary hn hK
  set J := binaryQuadraticHermitian n (by omega) with hJdef
  have hEcard : Nat.card (FiniteField.Extension (GaloisField 2 n) 2 2) = (2 ^ n) ^ 2 := by
    rw [FiniteField.natCard_extension, GaloisField.card 2 n (by omega)]
  have hfixed : Nat.card {x : FiniteField.Extension (GaloisField 2 n) 2 2 // J.conj x = x} =
      2 ^ n := quadraticBinaryFrobenius_fixed_card n (by omega)
  have hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := rfl
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv ↥K e.toEquiv
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, -, -, hUTB, -, -, -, ⟨S₀, hS₀⟩, -,
    -, -, -, -, hinvU, -, -⟩ := unitary_three_point_structure J n hn hEcard hfixed hJ
  set U := (hermitianUnipotentPSU J hJ).range with hUdef
  set Bα := unitaryCoordinateStabilizer J 0 with hBα
  have hUB : U ≤ Bα := hUTB ▸ le_sup_left
  set P' := toSylow2 hS
  have hP'c : (P' : Subgroup ↥K) = S.subgroupOf K := toSylow2_coe hS
  set P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPc : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (P' : Subgroup ↥K).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hmemP : ∀ k : ↥K, e k ∈ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ↔
      (k : G) ∈ S := by
    intro k
    rw [hPc, ← MulEquiv.coe_toMonoidHom, Subgroup.mem_map_equiv, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, hP'c, Subgroup.mem_subgroupOf]
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S₀ P
  have hconj : ∀ z ∈ (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      c⁻¹ * z * c ∈ U := by
    intro z hz
    rw [← hc, Sylow.coe_subgroup_smul, hS₀] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    simpa [MulAut.conj_apply, mul_assoc] using hu
  set x' := e ⟨x, hS.1 hx⟩ with hx'
  set y' := e ⟨y, hS.1 hy⟩ with hy'
  have hxU := hconj x' ((hmemP _).mpr hx)
  have hyU := hconj y' ((hmemP _).mpr hy)
  have hx'1 : c⁻¹ * x' * c ≠ 1 := by
    intro h
    apply hx1
    have h1 : x' = 1 := by
      have := congrArg (fun w => c * w * c⁻¹) h
      simpa [mul_assoc] using this
    have h2 : (⟨x, hS.1 hx⟩ : ↥K) = 1 := e.injective (by rw [← hx', h1, map_one])
    exact congrArg Subtype.val h2
  have hx'2 : (c⁻¹ * x' * c) ^ 2 = 1 := by
    have h1 : x' ^ 2 = 1 := by
      rw [hx', ← map_pow]
      have : (⟨x, hS.1 hx⟩ : ↥K) ^ 2 = 1 := Subtype.ext (by simpa using hx2)
      rw [this, map_one]
    have := conj_pow (a := c⁻¹) (b := x') (i := 2)
    rw [inv_inv] at this
    rw [this, h1, mul_one, inv_mul_cancel]
  have hcomm := (hinvU _ (hUB hxU) (orderOf_eq_prime hx'2 hx'1)).2 _ hyU
  have h1 : y' * x' = x' * y' := by
    calc y' * x' = c * (c⁻¹ * y' * c * (c⁻¹ * x' * c)) * c⁻¹ := by group
      _ = c * (c⁻¹ * x' * c * (c⁻¹ * y' * c)) * c⁻¹ := by rw [hcomm]
      _ = x' * y' := by group
  have h2 : e (⟨x, hS.1 hx⟩ * ⟨y, hS.1 hy⟩) = e (⟨y, hS.1 hy⟩ * ⟨x, hS.1 hx⟩) := by
    rw [map_mul, map_mul]
    exact h1.symm
  exact congrArg Subtype.val (e.injective h2)

theorem ordTwistedA_two_ne {q : ℕ} (hq : 4 ≤ q) : CFSG.Open.ordTwistedA 2 q ≠ 20160 := by
  intro h
  have hg : Nat.gcd (2 + 1) (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have hg0 : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have a1 : 64 ≤ q ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have a2 : (16 : ℤ) ≤ (q : ℤ) ^ 2 := by
    have : 16 ≤ q ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
    exact_mod_cast this
  have a3 : (64 : ℤ) ≤ (q : ℤ) ^ 3 := by exact_mod_cast a1
  unfold CFSG.Open.ordTwistedA at h
  rw [show 2 * (2 + 1) / 2 = 3 from rfl, show Finset.Icc 2 (2 + 1) = {2, 3} from rfl,
    Finset.prod_pair (by norm_num)] at h
  generalize hA : ((q : ℤ) ^ 2 - (-1 : ℤ) ^ 2).toNat = A at h
  generalize hB : ((q : ℤ) ^ 3 - (-1 : ℤ) ^ 3).toNat = B at h
  have hA' : 15 ≤ A := by
    rw [← hA]
    norm_num
    omega
  have hB' : 65 ≤ B := by
    rw [← hB]
    norm_num
    omega
  have hN : 64 * (15 * 65) ≤ q ^ 3 * (A * B) := Nat.mul_le_mul a1 (Nat.mul_le_mul hA' hB')
  have h3 := Nat.div_le_div_left hg hg0 (a := q ^ 3 * (A * B))
  rw [h] at h3
  have h4 := Nat.div_le_div_right (c := 3) hN
  omega

omit [Finite G] in
private theorem mem_normalizer_inf_of_mem4 {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro z
  exact and_congr (hA z) (hB z)

theorem kgBenderInnerU3_holds : KGBenderInnerU3 := by
  intro G _ _ X T M K n hP hJ hKX hXN hC hKT hn hK hMK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTK : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hP.isSylow hKX hXN
  refine ⟨?_, fun x hx hx2 => ?_⟩
  swap
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (comm_of_involution_of_isPSU3 hn hK hTK x hx hx2 y hy).symm
  intro u hu
  obtain ⟨hMmax, hTM⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.le
  have huM : u ∈ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M hu
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hTsylM : IsSylowTwoOf T M := isSylowTwoOf_mono hP.isSylow hTM hMX
  have hO2T : pCoreOf 2 M ≤ T := A4.le_of_normal_of_isSylowTwoOf hTsylM
    (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 M)).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)) hO2
  have huT : u ∈ T := hO2T hu
  have huNK : u ∈ Subgroup.normalizer (K : Set G) := hXN (hMX huM)
  have huNTK : u ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem4 (Subgroup.le_normalizer huT) huNK
  obtain ⟨m, hm⟩ := hO2 ⟨u, hu⟩
  have hum : u ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hcomm : ∀ b ∈ K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G),
      u * b * u⁻¹ * b⁻¹ ∈ T ⊓ K := by
    intro b hb
    have hbM : b ∈ M := (hMK ▸ hb : b ∈ M ⊓ K).1
    have hc1 : u * b * u⁻¹ * b⁻¹ ∈ pCoreOf 2 M := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf
        2 M hbM) u⁻¹).mp ((pCoreOf 2 M).inv_mem hu)
      have := (pCoreOf 2 M).mul_mem hu h1
      simpa [mul_assoc] using this
    have hc2 : u * b * u⁻¹ * b⁻¹ ∈ K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp huNK b).mp hb.1
      exact K.mul_mem h1 (K.inv_mem hb.1)
    have hc3 : u * b * u⁻¹ * b⁻¹ ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huNTK hb.2)
        (Subgroup.inv_mem _ huNTK)) (Subgroup.inv_mem _ hb.2)
    exact le_of_le_normalizer_of_isSylowTwoOf hTK (hO2.to_le (Subgroup.zpowers_le.mpr hc1))
      (Subgroup.zpowers_le.mpr hc2) (Subgroup.zpowers_le.mpr hc3) (Subgroup.mem_zpowers _)
  have hmapK : K.map (MulAut.conj u).toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp huNK k).mp hk
    · intro hx
      refine ⟨u⁻¹ * x * u, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huNK) x).mp hx
      simpa using this
  let β : ↥K ≃* ↥K := ((MulAut.conj u).subgroupMap K).trans (MulEquiv.subgroupCongr hmapK)
  have hβ : ∀ k : ↥K, ((β k : ↥K) : G) = u * k * u⁻¹ := fun k => rfl
  have hβpow : ∀ j : ℕ, ∀ k : ↥K, (((β ^ j) k : ↥K) : G) = u ^ j * k * (u ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro k; simp
    | succ j ih =>
      intro k
      rw [pow_succ']
      change ((β ((β ^ j) k) : ↥K) : G) = _
      rw [hβ, ih k]
      group
  have hβm : β ^ (2 ^ m) = 1 := by
    ext k
    rw [hβpow, hum, one_mul, inv_one, mul_one]
    rfl
  have hU : IsSylowTwoOf ((T ⊓ K).subgroupOf K) ⊤ := by
    refine ⟨le_top, hTK.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTK.1).symm, ?_⟩
    have h3 : (((T ⊓ K).subgroupOf K).subgroupOf ⊤).index = ((T ⊓ K).subgroupOf K).index :=
      Subgroup.relIndex_top_right _
    rw [h3]
    exact hTK.2.2
  have hβU : ((T ⊓ K).subgroupOf K).map β.toMonoidHom = (T ⊓ K).subgroupOf K := by
    ext k
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hw' : (w : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hw
      exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp huNTK _).mp hw')
    · intro hk
      have hk' : (k : G) ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hk
      refine ⟨⟨u⁻¹ * k * u, ?_⟩, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huNK) (k : G)).mp k.2
        simpa using this
      · apply Subgroup.mem_subgroupOf.mpr
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huNTK) k).mp hk'
        simpa using this
      · apply Subtype.ext
        change u * (u⁻¹ * k * u) * u⁻¹ = k
        group
  have hβcent : Subgroup.normalizer (((T ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K) ≤
      CFSG.Quasithin.H13.L32A.C.SkPf.centMod ((T ⊓ K).subgroupOf K) β := by
    intro b hb
    refine ⟨hb, ?_⟩
    have hbN : (b : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 := (Subgroup.mem_normalizer_iff.mp hb ⟨z, hz.2⟩).mp
          (Subgroup.mem_subgroupOf.mpr hz)
        exact Subgroup.mem_subgroupOf.mp h1
      · intro hz
        have hzK : z ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem b.2) hz.2) b.2
          simpa [mul_assoc] using this
        have h1 := (Subgroup.mem_normalizer_iff.mp hb ⟨z, hzK⟩).mpr
          (Subgroup.mem_subgroupOf.mpr hz)
        exact Subgroup.mem_subgroupOf.mp h1
    have hc := hcomm b ⟨b.2, hbN⟩
    apply Subgroup.mem_subgroupOf.mpr
    simpa [hβ, mul_assoc] using hc
  rcases (CFSG.Quasithin.H13.L32A.C.SkPf.n2Model_n4Model_of_isPSU3 (by omega) hK).2 _ hU β
      ⟨m, hβm⟩ hβU hβcent with ⟨k, hk⟩ | h34
  ·
    have hag : ∀ x ∈ K, u * x * u⁻¹ = (k : G) * x * (k : G)⁻¹ := by
      intro x hx
      have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : G)) hk
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h1
      rw [← hβ ⟨x, hx⟩, ← h1]
    have hc : (k : G)⁻¹ * u ∈ X ⊓ Subgroup.centralizer (K : Set G) := by
      refine ⟨X.mul_mem (X.inv_mem (hKX k.2)) (hMX huM), ?_⟩
      show (k : G)⁻¹ * u ∈ Subgroup.centralizer (K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 := hag y hy
      calc y * ((k : G)⁻¹ * u) = (k : G)⁻¹ * ((k : G) * y * (k : G)⁻¹) * u := by group
        _ = (k : G)⁻¹ * (u * y * u⁻¹) * u := by rw [h1]
        _ = (k : G)⁻¹ * u * y := by group
    rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [← hc]
    exact k.2
  ·
    exfalso
    have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two h34).1 rfl
    have h2 := (CFSG.Timmesfeld.card_statedClassicalModel_two hK).2.1 rfl
    have h4 : 4 ≤ 2 ^ n :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have hA : CFSG.Open.ordA (3 - 1) (2 ^ 2) = 20160 := by decide
    rw [h1, hA] at h2
    exact ordTwistedA_two_ne h4 h2.symm

end E2

end CFSG.Quasithin
