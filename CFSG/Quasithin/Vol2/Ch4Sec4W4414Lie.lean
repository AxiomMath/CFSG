module

public import CFSG.Quasithin.Vol2.Ch4Sec4W4414F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

@[expose] def Stmt4_4_14Lie : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V₀ H : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    V₀ ≤ conjClosure L T ⊔ T → IsPrimeReduced 2 (V₀.subgroupOf (conjClosure L T ⊔ T)) →
    IsHStar T M H →
    ⁅V₀, conjClosure L T⁆ ≠ ⊥ →
    V₀ = conjClosure (V₀ ⊓ Subgroup.centralizer (T : Set G)) (conjClosure L T) →
    (∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
      ¬ IsFFModule (V := ↥⁅V₀, conjClosure L T⁆)
        (autOn (conjClosure L T ⊔ T) ⁅V₀, conjClosure L T⁆)) →
    (∃ K ∈ cComp H, H = K ⊔ T ∧ E2.E22LieCases H T (H ⊓ M) K) →
      ((∃ P : Subgroup G, QuasithinUnique.IsSylowTwoOf P (oTwoUpper H ⊓ M) ∧
          oTwoUpper H ⊓ M ≤ Subgroup.normalizer (P : Set G)) ∧
        ∀ B : Subgroup G, B ≤ H ⊓ M → Odd (Nat.card B) → (∃ k : ℕ, B.relIndex (H ⊓ M) = 2 ^ k) →
          ∀ b ∈ B, (∀ m ∈ conjClosure L T, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 (conjClosure L T)) →
            b = 1) ∨
      (∃ n : ℕ, 1 ≤ n ∧
        LieModel (↥(conjClosure L T) ⧸ CFSG.pCore 2 ↥(conjClosure L T)) .PSL 2 2 (2 * n) ∧
        ∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
          BinaryOrthogonalFour (V := ↥⁅V₀, conjClosure L T⁆)
            (autOn (conjClosure L T) ⁅V₀, conjClosure L T⁆) ⊤ ⊥ n) ∨
      (LieModel (↥(conjClosure L T) ⧸ CFSG.pCore 2 ↥(conjClosure L T)) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥⁅V₀, conjClosure L T⁆,
          FanoCoreModule (V := ↥⁅V₀, conjClosure L T⁆)
            (autOn (conjClosure L T) ⁅V₀, conjClosure L T⁆) ⊤ ⊥)

namespace Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open scoped Pointwise

theorem stmt4_4_14Lie_of (h443 : Stmt4_4_3Orbit')
    (hZ : Thm4414ZCentral) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Stmt4_4_14Lie := by
  intro G _ _ T M L V₀ H hs hnab hK hT hM hTM hL hLf hLM hq hV₀ hV₀r hH hV1 hV₀gen hnFF hLie
  have h421 : Hyp4_2_1 G T M L := ⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq⟩
  set Mp := conjClosure L T with hMp
  set V := ⁅V₀, Mp⁆ with hVdef
  have hMN : M ≤ Subgroup.normalizer (Mp : Set G) := h421.le_normalizer_conjClosure h37 h38 h39
  have hMpM : Mp ≤ M := h421.conjClosure_le
  have hperf : ⁅Mp, Mp⁆ = Mp := conjClosure_perfect h421.perfect
  have hMO : M ≤ Subgroup.normalizer (pCoreOf 2 Mp : Set G) :=
    hMN.trans (normalizer_le_normalizer_pCoreOf 2 Mp)
  have hTH : T ≤ H := hH.1.1
  have hO2H : pCoreOf 2 H ≠ ⊥ := hH.1.2
  have hSyl : IsSylowTwoOf T H := isSylowTwoOf_of_isSylowTwo hT hTH
  have hUMO : IsUniqueMaxOver H T (H ⊓ M) := by
    obtain ⟨S, hS⟩ := exists_sylow_coe_eq hT
    have := IsHStar.isUniqueMaxOver S (hS ▸ hH) (hS ▸ hTM)
    rwa [hS] at this
  obtain ⟨h2cl, h4413B⟩ := stmt4_4_13Lie_holds G H T (H ⊓ M) hs hnab hK hO2H hLie hSyl hUMO
  have h2cl' : ∃ P : Subgroup G, IsSylowTwoOf P (oTwoUpper H ⊓ M) ∧
      oTwoUpper H ⊓ M ≤ Subgroup.normalizer (P : Set G) := by
    have he : H ⊓ M ⊓ oTwoUpper H = oTwoUpper H ⊓ M := by
      rw [inf_comm, ← inf_assoc, inf_eq_left.mpr (oTwoUpper_le H)]
    rwa [he] at h2cl
  by_cases hfaith : ∀ B : Subgroup G, B ≤ H ⊓ M → Odd (Nat.card B) →
      (∃ k : ℕ, B.relIndex (H ⊓ M) = 2 ^ k) →
      ∀ b ∈ B, (∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp) → b = 1
  · exact Or.inl ⟨h2cl', hfaith⟩
  push Not at hfaith
  obtain ⟨BH, hBHM, hBHo, hBHi, b, hbB, hbC, hb1⟩ := hfaith
  have hBHc : IsMulCommutative ↥BH :=
    (e22BorelFactsLie_holds G H T (H ⊓ M) hs hnab hK hO2H hLie hSyl hUMO).2 BH hBHM hBHo hBHi
  have hBHle : BH ≤ M := hBHM.trans inf_le_right
  set D := BH ⊓ centralizerSection M Mp (pCoreOf 2 Mp) with hD
  have hmemD : ∀ x, x ∈ D ↔ x ∈ BH ∧ ∀ m ∈ Mp, x * m * x⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp := by
    intro x
    constructor
    · rintro ⟨hxB, -, -, -, hx⟩
      refine ⟨hxB, fun m hm => ?_⟩
      have := (pCoreOf 2 Mp).inv_mem (hx m hm)
      have e : (m * x * m⁻¹ * x⁻¹)⁻¹ = x * m * x⁻¹ * m⁻¹ := by group
      rwa [e] at this
    · rintro ⟨hxB, hx⟩
      refine ⟨hxB, hBHle hxB, hMN (hBHle hxB), hMO (hBHle hxB), fun m hm => ?_⟩
      have := (pCoreOf 2 Mp).inv_mem (hx m hm)
      have e : (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ := by group
      rwa [e] at this
  have hDB : D ≤ BH := inf_le_left
  have hDc : IsMulCommutative ↥D := ⟨⟨fun a c => by
    have := mul_comm (⟨a, hDB a.2⟩ : ↥BH) ⟨c, hDB c.2⟩
    apply Subtype.ext
    show (a : G) * c = c * a
    exact congrArg Subtype.val this⟩⟩
  have hDodd : Odd (Nat.card D) := by
    have h1 := Subgroup.card_dvd_of_le hDB
    exact Odd.of_dvd_nat hBHo h1
  have hbD : b ∈ D := (hmemD b).mpr ⟨hbB, hbC⟩
  have hD1 : D ≠ ⊥ := fun h => hb1 (by rw [h] at hbD; exact (Subgroup.mem_bot.mp hbD))
  have hDT : (D : Set G) * (T : Set G) = (T : Set G) * (D : Set G) := by
    have h2 := (h4413B BH hBHM hBHo hBHi).2 M Mp hM hTM (inf_comm H M)
      h421.oTwoUpper_conjClosure hMpM hMN
    have hset : (D : Set G) = {b | b ∈ BH ∧ ∀ m ∈ Mp, b * m * b⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp} := by
      ext x
      exact hmemD x
    rw [hset]
    exact h2
  have hDcomm : ⁅Mp, D⁆ ≤ pCoreOf 2 Mp := by
    rw [Subgroup.commutator_le]
    intro m hm x hx
    have := ((hmemD x).mp hx).2 m hm
    have := (pCoreOf 2 Mp).inv_mem this
    have e : (x * m * x⁻¹ * m⁻¹)⁻¹ = m * x * m⁻¹ * x⁻¹ := by group
    rw [e] at this
    exact this
  have hDM : D ≤ M := hDB.trans hBHle
  have hOrbitT : ∀ t ∈ T, ∃ s ∈ T, CFSG.conjugate L t = CFSG.conjugate L s :=
    fun t ht => ⟨t, ht, rfl⟩
  have hCoreD : Hyp4_4_1Core G T M L D T :=
    ⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq, hDM, hD1, hDc, hDodd, hDcomm, le_rfl, hDT⟩
  have hTwoD : Hyp4_4_1TwoOrbit G T M L D T := ⟨hCoreD, hOrbitT⟩
  have h445 := lemma_4_4_5_orbit hTwoD
  have hZH := hZ G T M L V₀ H hs hnab hK hT hM hTM hL hLf hLM hq hV₀ hV₀r hH hV1 hV₀gen hnFF
  obtain ⟨hV₀Z, -⟩ := le_omegaOneCenter_of_isPrimeReduced hV₀ hV₀r
  have hV₀n : Mp ⊔ T ≤ Subgroup.normalizer (V₀ : Set G) := by
    have hnorm : (V₀.subgroupOf (Mp ⊔ T)).Normal := hV₀r.1
    have key : ∀ x ∈ Mp ⊔ T, ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀ := fun x hx v hv =>
      hnorm.conj_mem ⟨v, hV₀ hv⟩ hv ⟨x, hx⟩
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => key x hx v hv, fun hv => ?_⟩
    have := key x⁻¹ (Subgroup.inv_mem _ hx) _ hv
    simpa [mul_assoc] using this
  have hTMp : T ≤ Subgroup.normalizer (Mp : Set G) := hTM.trans hMN
  have hO2T : pCoreOf 2 Mp ≤ T := by
    have hTsyl : IsSylowTwoOf T (Mp ⊔ T) := isSylowTwoOf_of_isSylowTwo hT le_sup_right
    refine (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Mp).trans le_sup_left) ?_
      (pCoreOf_isPGroup 2 Mp)).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
    exact (_root_.sup_le Subgroup.le_normalizer hTMp).trans (normalizer_le_normalizer_pCoreOf 2 Mp)
  have hV₀D : V₀ ≤ Subgroup.centralizer (D : Set G) := by
    rw [hV₀gen]
    refine conjClosure_le fun m hm x hx => ?_
    have hxO := mem_quasithinOmegaOneCenter_iff.mp (hV₀Z hx.1)
    have hxT : x ∈ T := (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_isSylowTwo hT
      le_sup_right)) hxO.1
    have hx2 : x ^ 2 = 1 := hxO.2.2
    have hxZ : x ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hxT, hx.2⟩, hx2⟩
    have hxD : x ∈ Subgroup.centralizer (D : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have := Subgroup.mem_centralizer_iff.mp (hZH (hBHM (hDB hd)).1) x hxZ
      exact this.symm
    have hm' : m ∈ ((perfectCore (Mp ⊓ Subgroup.centralizer (D : Set G)) : Set G) *
        (pCoreOf 2 Mp : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (fun l hl => le_normalizer_pCoreOf 2 Mp ((perfectCore_le _).trans inf_le_left hl))]
      rw [← h445]
      exact hm
    obtain ⟨l, hl, q, hq', rfl⟩ := hm'
    have hlD : l ∈ Subgroup.centralizer (D : Set G) := ((perfectCore_le _).trans inf_le_right) hl
    have hqx : q * x * q⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.mp hx.2 q (hO2T hq')
      rw [this]
      group
    have e : l * q * x * (l * q)⁻¹ = l * x * l⁻¹ := by
      calc l * q * x * (l * q)⁻¹ = l * (q * x * q⁻¹) * l⁻¹ := by group
        _ = l * x * l⁻¹ := by rw [hqx]
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlD hxD) (Subgroup.inv_mem _ hlD)
  have hVV₀ : V ≤ V₀ :=
    commutator_le_left_of_le_normalizer (le_sup_left.trans hV₀n)
  have hcard1 : Nat.card D ≠ 1 := fun h => hD1 (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpD⟩ := Nat.exists_prime_and_dvd hcard1
  have : Fact p.Prime := ⟨hp⟩
  set A := omegaOnePOf p D with hA
  have hAD : A ≤ D := omegaOnePOf_le p D
  have hA1 : A ≠ ⊥ := omegaOnePOf_ne_bot hpD
  have hAel : IsElemAbelian p A := isElemAbelian_omegaOnePOf p D
  have hAc : IsMulCommutative ↥A := hAel.1
  have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hAD)
  have h444 := lemma_4_4_4_orbit hTwoD
  have hAT : (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) := by
    have hDN : D ≤ Subgroup.normalizer ((pCoreOf 2 (T ⊔ D) : Subgroup G) : Set G) :=
      le_sup_right.trans (le_normalizer_pCoreOf 2 (T ⊔ D))
    refine coe_mul_comm_of_eq_sup h444 (fun a ha => mem_normalizer_commutator
        (hDN (hAD ha)) (Subgroup.le_normalizer (hAD ha)))
      (fun x hx => le_normalizer_omegaOnePOf p D hx.2)
      (fun x hx => mem_normalizer_commutator
        (le_sup_left.trans (le_normalizer_pCoreOf 2 (T ⊔ D)) hx.1) hx.2)
  have hAM : A ≤ M := hAD.trans hDM
  have hAcomm : ⁅Mp, A⁆ ≤ pCoreOf 2 Mp := (Subgroup.commutator_mono le_rfl hAD).trans hDcomm
  have hVle : V ≤ quasithinOmegaOneCenter (pCoreOf 2 (Mp ⊔ T)) := hVV₀.trans hV₀Z
  have hVn : Mp ⊔ T ≤ Subgroup.normalizer (V : Set G) := fun x hx =>
    mem_normalizer_commutator (hV₀n hx) ((_root_.sup_le Subgroup.le_normalizer hTMp) hx)
  have hVeq : V = ⁅V, Mp⁆ :=
    commutator_eq_commutator_commutator_of_perfect' hperf
      (hV₀.trans (_root_.sup_le Subgroup.le_normalizer hTMp))
  have hVA : ⁅V, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp
      (hAD.trans (Subgroup.le_centralizer_iff.mp (hVV₀.trans hV₀D)))
  have hconcl := h443 G T M L A T V hs hnab hK hT hM hTM hL hLf hLM hq hAM hA1 hAc hAodd hAcomm
    le_rfl hAT hOrbitT hVle hVn hVeq hV1 hVA
  rcases hconcl with hNA | ⟨hLn, -, hcases⟩
  ·
    exfalso
    have h1 := (h4413B BH hBHM hBHo hBHi).1 p A hp (hAD.trans hDB) hAel hAT
    exact h1.2 (fun x hx => ⟨hx.1, hNA hx.2⟩)
  · have hMpL : Mp = L := conjClosure_eq_self (hTM.trans hLn)
    have hcl : conjClosure L T = L := conjClosure_eq_self (hTM.trans hLn)
    rcases hcases with ⟨⟨hc, hFF⟩, -⟩ | h2 | h3
    · exfalso
      obtain ⟨hc', hnFF'⟩ := hnFF
      apply hnFF'
      rw [hMpL]
      exact hFF
    · right; left
      exact of_eq_subst hcl.symm (P := fun X => ∃ n : ℕ, 1 ≤ n ∧
        LieModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 2 2 (2 * n) ∧
        ∃ _ : IsMulCommutative ↥V, BinaryOrthogonalFour (V := ↥V) (autOn X V) ⊤ ⊥ n) h2
    · right; right
      exact of_eq_subst hcl.symm (P := fun X => LieModel (↥X ⧸ CFSG.pCore 2 ↥X) .PSL 3 2 1 ∧
        ∃ _ : IsMulCommutative ↥V, FanoCoreModule (V := ↥V) (autOn X V) ⊤ ⊥) h3

theorem stmt4_4_14Lie_of_steps (h443 : Stmt4_4_3Orbit')
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) : Stmt4_4_14Lie :=
  stmt4_4_14Lie_of h443 (thm4414ZCentral_holds hC58 h317 h37 h38 h39) h37 h38 h39

end Ch4

end CFSG.Quasithin.H13
