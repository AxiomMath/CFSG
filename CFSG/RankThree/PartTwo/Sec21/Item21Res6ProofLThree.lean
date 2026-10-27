module

public import CFSG.RankThree.PartTwo.Sec21.Item218Res2ProofDefs
public import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofFrame
public import CFSG.RankThree.PartTwo.Sec21.Item21LateProofFrame
public import CFSG.RankThree.PartTwo.Sec21.Item21Res6ProofLThreeTools
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.KFacts.KSL3PiOrder3TypeC
public import CFSG.RankThree.PartTwo.Sec21.Item215

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res6Proof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {G : Type} [Group G]

theorem conj_eq_self_of_mem_zpowers {c w : G} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hw3 : w ^ 3 * c * (w ^ 3)⁻¹ = c) (h : w * c * w⁻¹ ∈ Subgroup.zpowers c) :
    w * c * w⁻¹ = c := by
  obtain ⟨k, hk, hck⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hc3 h
  have hconjpow : ∀ (x : G) (j : ℕ), w * x ^ j * w⁻¹ = (w * x * w⁻¹) ^ j := fun x j => by
    rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply]
  interval_cases k
  · exfalso
    apply hc1
    rw [pow_zero] at hck
    calc c = w⁻¹ * (w * c * w⁻¹) * w := by group
      _ = 1 := by rw [hck]; group
  · rwa [pow_one] at hck
  · exfalso
    apply hc1
    have h2 : w * c ^ 2 * w⁻¹ = c := by
      rw [hconjpow, hck, ← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hc3, one_mul]
    have hw2 : w ^ 2 * c * (w ^ 2)⁻¹ = c := by
      calc w ^ 2 * c * (w ^ 2)⁻¹ = w * (w * c * w⁻¹) * w⁻¹ := by rw [pow_two]; group
        _ = c := by rw [hck, h2]
    have hw3' : w ^ 3 * c * (w ^ 3)⁻¹ = c ^ 2 := by
      calc w ^ 3 * c * (w ^ 3)⁻¹ = w * (w ^ 2 * c * (w ^ 2)⁻¹) * w⁻¹ := by
            rw [pow_succ' w 2]; group
        _ = c ^ 2 := by rw [hw2, hck]
    have hcc : c = c ^ 2 := hw3.symm.trans hw3'
    calc c = c ^ 2 * c⁻¹ * c⁻¹ * c := by group
      _ = c * c⁻¹ * c⁻¹ * c := by rw [← hcc]
      _ = 1 := by group

theorem false_of_SLThree [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U₀ X : Subgroup G} {a c : G} (hpair : Sec21Pair G A E U₀ a X)
    (hn : ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar X ≃* SL3 n)) (hC : IsTypeCOnBarSL A X)
    (h27 : Nat.card A = 3 ^ 3) (hS3 : Nonempty (starOf A X ≃* Equiv.Perm (Fin 3)))
    (hcA : c ∈ A) (hca : c ∉ Subgroup.zpowers a)
    (hXc : X ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) : False := by
  obtain ⟨haX, hB9, w, ⟨hwX, hwN⟩, hw3, hwb, hwa⟩ :=
    Item21LateProof.item2118Frame_of h45 h66 G A E U₀ a X hpair hn hC h27 hS3
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA27 : Nat.card A = 27 := by rw [h27]; norm_num
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs.2.2.1
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hwa' : w * a * w⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hwX), mul_inv_cancel_right]
  have nA : ∀ {g : G}, g ∈ Subgroup.normalizer (A : Set G) → ∀ x ∈ A, g * x * g⁻¹ ∈ A :=
    fun hg x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hwB : ∀ y ∈ A ⊓ X, w * y * w⁻¹ ∈ A ⊓ X := fun y hy =>
    ⟨nA hwN y hy.1, X.mul_mem (X.mul_mem hwX hy.2) (X.inv_mem hwX)⟩
  obtain ⟨hfix, -⟩ := Item21LateProof.eq_of_conj_invariant hcomm h3 hA27 inf_le_left hB9
    ⟨haA, haX⟩ ha1 (nA hwN) hwB hw3 hwa' hwb hwa
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hwc : w * c * w⁻¹ = c := conj_eq_self_of_mem_zpowers (h3 c hcA) hc1 (hw3 c hcA)
    ((Subgroup.mem_normalizer_iff.mp (hXc ⟨hwX, hwN⟩) c).mp (Subgroup.mem_zpowers c))
  exact hca (hfix c hcA hwc)

theorem eq_one_of_commute_typeOne [Finite G] {X : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (eL : lBar X ≃* projSL 3 (GaloisField 2 n)) {d : G} (hdX : d ∈ X)
    (hd : Sec4.InducesTypeOn X d 1) {m : lBar X}
    (hmd : m * ((⟨d, hdX⟩ : X) : lBar X) = ((⟨d, hdX⟩ : X) : lBar X) * m)
    (hm2 : ∀ z : lBar X, m * m * z = z * (m * m)) : m = 1 := by
  obtain ⟨hx, π, p, f, K, _, hK, hq, e, y, -, hy1, hact⟩ := hd
  have hcard := Sec13.card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hK.prime hK.one_le
    (by omega) hq hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have : CharP K 2 := hK.charP
  have hq2 : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hn
  set D' : lBar X := ((⟨d, hdX⟩ : X) : lBar X) with hD'
  have hey : (e D' : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk y := by
    refine Item21Late2Proof.coe_e_eq_mk_of_inner hK hq hq2 e D' y fun z => ?_
    rw [← Item21Late2Proof.thetaQuotMulAut_inner hdX hx z]
    exact hact z
  obtain ⟨M, hMS, hMm⟩ := (e m).2
  have hcoe : ∀ u v : lBar X, ((e (u * v) : projImage (Sec4.slPi true 3 (2 ^ f) K)) :
      ProjGenLinGroup (Fin 3) K) = (e u : ProjGenLinGroup (Fin 3) K) * (e v) := fun u v => by
    rw [map_mul, Subgroup.coe_mul]
  have hc1 : ProjGenLinGroup.mk M * ProjGenLinGroup.mk y =
      ProjGenLinGroup.mk y * ProjGenLinGroup.mk M := by
    have h1 := congrArg (fun u : lBar X =>
      ((e u : projImage (Sec4.slPi true 3 (2 ^ f) K)) : ProjGenLinGroup (Fin 3) K)) hmd
    simp only [hcoe] at h1
    rwa [← hMm, hey] at h1
  have hs1 : M * y * M⁻¹ * y⁻¹ ∈ StatedScalars (Fin 3) K := by
    apply KFacts.mk_eq_one_iff_mem_statedScalars'.mp
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc1]
    group
  obtain ⟨ℓ, hℓ⟩ := hs1
  have hMy : M * y * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ℓ * y := by
    rw [hℓ]
    group
  have hM2 : M * M ∈ StatedScalars (Fin 3) K := by
    refine Sec13.mem_statedScalars_of_commute_mk hK hq hq2 fun s hs => ?_
    set z := e.symm ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩ with hz
    have hez : (e z : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk s := by
      rw [hz, MulEquiv.apply_symm_apply]
    have h1 := congrArg (fun u : lBar X =>
      ((e u : projImage (Sec4.slPi true 3 (2 ^ f) K)) : ProjGenLinGroup (Fin 3) K)) (hm2 z)
    simp only [hcoe] at h1
    rw [← hMm, hez] at h1
    rw [map_mul]
    exact h1
  obtain ⟨τ, hτ, hτ1, z₀, hz₀, g, -, hD⟩ := hy1
  have hz₀s : z₀ ∈ StatedScalars (Fin 3) K := Sec4.mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz₀
  obtain ⟨ζ, hζ⟩ := hz₀s
  have hscomm : ∀ (u : Kˣ) (P : GL (Fin 3) K),
      GeneralLinearGroup.scalar (Fin 3) u * P = P * GeneralLinearGroup.scalar (Fin 3) u := by
    intro u P
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hSc : ∀ (u : Kˣ) (P : GL (Fin 3) K),
      P * GeneralLinearGroup.scalar (Fin 3) u * P⁻¹ = GeneralLinearGroup.scalar (Fin 3) u := by
    intro u P
    rw [← hscomm u P]
    group
  have hSc' : ∀ (u : Kˣ) (P : GL (Fin 3) K),
      P⁻¹ * GeneralLinearGroup.scalar (Fin 3) u * P = GeneralLinearGroup.scalar (Fin 3) u := by
    intro u P
    have := hSc u P⁻¹
    rwa [inv_inv] at this
  have hNδ : (g⁻¹ * M * g) * Sec4.diagTau hτ * (g⁻¹ * M * g)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) ℓ * Sec4.diagTau hτ := by
    rw [← hD, ← hζ]
    calc g⁻¹ * M * g * (g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) ζ) * g) *
          (g⁻¹ * M * g)⁻¹
        = g⁻¹ * (M * y * M⁻¹) * (M * GeneralLinearGroup.scalar (Fin 3) ζ * M⁻¹) * g := by
          group
      _ = g⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ℓ * y) *
            GeneralLinearGroup.scalar (Fin 3) ζ * g := by rw [hMy, hSc]
      _ = (g⁻¹ * GeneralLinearGroup.scalar (Fin 3) ℓ * g) *
            (g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) ζ) * g) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ℓ *
            (g⁻¹ * (y * GeneralLinearGroup.scalar (Fin 3) ζ) * g) := by rw [hSc']
  have hN2 : (g⁻¹ * M * g) * (g⁻¹ * M * g) ∈ StatedScalars (Fin 3) K := by
    obtain ⟨μ, hμ⟩ := hM2
    refine ⟨μ, ?_⟩
    calc GeneralLinearGroup.scalar (Fin 3) μ = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ * g :=
          (hSc' μ g).symm
      _ = (g⁻¹ * M * g) * (g⁻¹ * M * g) := by rw [hμ]; group
  obtain ⟨ν, hν⟩ := mem_statedScalars_of_conj_diagTau hτ hτ1 hNδ hN2
  have hMs : M ∈ StatedScalars (Fin 3) K := by
    refine ⟨ν, ?_⟩
    calc GeneralLinearGroup.scalar (Fin 3) ν = g * GeneralLinearGroup.scalar (Fin 3) ν * g⁻¹ :=
          (hSc ν g).symm
      _ = M := by rw [hν]; group
  have hem : e m = 1 := by
    apply Subtype.ext
    rw [← hMm, Subgroup.coe_one]
    exact Item21Late2Proof.mk_eq_one_of_mem_statedScalars hMs
  rw [← map_one e] at hem
  exact e.injective hem

theorem false_of_LThree [Finite G] (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U₀ X : Subgroup G} {a c : G} (hcfg : Config2119 G A E U₀ a X)
    (hU₀ : U₀ ∈ fourGroupsMinus E) (hcA : c ∈ A) (hca : c ∉ Subgroup.zpowers a)
    (hcU : c ∈ Subgroup.centralizer (U₀ : Set G))
    (hXc : X ⊓ Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers c : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, d₀, hd₀B, hd₀1, hd₀T, -, -, -, -, ⟨w, ⟨hwX, hwN⟩, hw31, hwd, -, hwmove⟩, t,
    ⟨htX, htN⟩, htd⟩ := Item21Late2Proof.frame_of h45 h66 hcfg
  have hpair := hcfg.pair
  obtain ⟨n, hn0, hev, ⟨eL⟩⟩ := hcfg.lthree
  have hn : 2 ≤ n := by obtain ⟨k, hk⟩ := hev; omega
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hA27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have haA : a ∈ A := hpair.mem_E.2 hpairs.1.1
  have ha1 : a ≠ 1 := hpairs.2.1
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hac : a ∉ Subgroup.zpowers c := fun h => hca (mem_zpowers_of_mem_zpowers (h3 c hcA) ha1 h)
  have hXa : X ∈ thetaComponentsAt 3 a := lZeroStarAt_subset A a hpairs.2.2.1
  have hXC : X ≤ Subgroup.centralizer ({a} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hXa
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe haA ha1 X
      hXa
  have hfixa : ∀ x ∈ X, x * a * x⁻¹ = a := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hXC hx), mul_inv_cancel_right]
  have hnc : ∀ x ∈ X ⊓ Subgroup.normalizer (A : Set G), x * c * x⁻¹ ∈ Subgroup.zpowers c :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp (hXc hx) c).mp (Subgroup.mem_zpowers c)
  have hwc : w * c * w⁻¹ = c := conj_eq_self_of_mem_zpowers (h3 c hcA) hc1
    (by rw [hw31, one_mul, inv_one, mul_one]) (hnc w ⟨hwX, hwN⟩)
  set B : Subgroup G := Subgroup.zpowers c ⊔ Subgroup.zpowers a with hBdef
  have hB9 : Nat.card B = 9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA a haA)
    (h3 c hcA) (h3 a haA) hc1 hac
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr haA)
  have hd₀B' : d₀ ∈ B := by
    by_contra hd
    obtain ⟨a', ha'A, ha'⟩ := hwmove
    apply ha'
    have hBw : B ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc c * w = w * (w⁻¹ * c * w) := by group
          _ = w * c := by
            congr 1
            calc w⁻¹ * c * w = w⁻¹ * (w * c * w⁻¹) * w := by rw [hwc]
              _ = c := by group
      · rw [Subgroup.mem_centralizer_singleton_iff]
        calc a * w = w * (w⁻¹ * a * w) := by group
          _ = w * a := by
            congr 1
            calc w⁻¹ * a * w = w⁻¹ * (w * a * w⁻¹) * w := by rw [hfixa w hwX]
              _ = a := by group
    obtain ⟨k, -, y, hyB, rfl⟩ := Item21LateProof.exists_pow_mul_of_card hcomm h3 hBA
      (by rw [hA27, hB9]) hd₀B.1 hd a' ha'A
    have hy : w * y * w⁻¹ = y := by
      rw [(Subgroup.mem_centralizer_singleton_iff.mp (hBw hyB)).symm, mul_inv_cancel_right]
    rw [← MulAut.conj_apply, map_mul, map_pow, MulAut.conj_apply, MulAut.conj_apply, hwd, hy]
  have hd₀c : d₀ ∈ Subgroup.zpowers c := by
    have hcB : Nat.card B = 3 * Nat.card (Subgroup.zpowers c) := by
      rw [hB9, Nat.card_zpowers, orderOf_eq_prime (h3 c hcA) hc1]
    have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => hcomm x (hBA hx) y (hBA hy)
    obtain ⟨j, -, y, hy, hd₀⟩ := Item21LateProof.exists_pow_mul_of_card hBc
      (fun x hx => h3 x (hBA hx)) le_sup_left hcB (le_sup_right (b := Subgroup.zpowers a)
        (Subgroup.mem_zpowers a)) hac d₀ hd₀B'
    have hyA : y ∈ A := Subgroup.zpowers_le.mpr hcA hy
    have hty : t * y * t⁻¹ ∈ Subgroup.zpowers c := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
      exact (Subgroup.zpowers c).zpow_mem (hnc t ⟨htX, htN⟩) i
    have htaj : t * a ^ j * t⁻¹ = a ^ j := by
      rw [← MulAut.conj_apply, map_pow, MulAut.conj_apply, hfixa t htX]
    have h2j : a ^ j * a ^ j ∈ Subgroup.zpowers c := by
      have e1 : t * d₀ * t⁻¹ = a ^ j * (t * y * t⁻¹) := by
        rw [hd₀, ← MulAut.conj_apply, map_mul, MulAut.conj_apply, MulAut.conj_apply, htaj]
      have e2 : a ^ j * a ^ j = y⁻¹ * (t * y * t⁻¹)⁻¹ := by
        have h1 : a ^ j * (t * y * t⁻¹) = (a ^ j * y)⁻¹ := by rw [← hd₀, ← htd, e1]
        have hya : y * a ^ j = a ^ j * y := hcomm y hyA _ (A.pow_mem haA j)
        calc a ^ j * a ^ j = a ^ j * (a ^ j * (t * y * t⁻¹)) * (t * y * t⁻¹)⁻¹ := by group
          _ = a ^ j * (a ^ j * y)⁻¹ * (t * y * t⁻¹)⁻¹ := by rw [h1]
          _ = a ^ j * (y * a ^ j)⁻¹ * (t * y * t⁻¹)⁻¹ := by rw [hya]
          _ = y⁻¹ * (t * y * t⁻¹)⁻¹ := by group
      rw [e2]
      exact (Subgroup.zpowers c).mul_mem ((Subgroup.zpowers c).inv_mem hy)
        ((Subgroup.zpowers c).inv_mem hty)
    have haj : a ^ j = 1 := by
      have hmem : a ^ j * a ^ j ∈ Subgroup.zpowers a :=
        (Subgroup.zpowers a).mul_mem ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) j)
          ((Subgroup.zpowers a).pow_mem (Subgroup.mem_zpowers a) j)
      have h1 : a ^ j * a ^ j = 1 := by
        by_contra h1
        exact hac ((Subgroup.zpowers_le.mpr h2j) (mem_zpowers_of_mem_zpowers (h3 a haA) h1 hmem))
      have h2 : (a ^ j) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3 a haA, one_pow]
      calc a ^ j = (a ^ j) ^ 3 * (a ^ j * a ^ j)⁻¹ := by group
        _ = 1 := by rw [h2, h1]; group
    rw [hd₀, haj, one_mul]
    exact hy
  have hUd : ∀ u ∈ U₀, u * d₀ * u⁻¹ = d₀ := by
    intro u hu
    have hcu : u * c = c * u := (Subgroup.mem_centralizer_iff.mp hcU) u hu
    have huc : u * c * u⁻¹ = c := by
      calc u * c * u⁻¹ = c * u * u⁻¹ := by rw [hcu]
        _ = c := by group
    exact Item21LateProof.conj_eq_of_mem_zpowers huc hd₀c
  set T : Subgroup.normalizer (X : Set G) →* MulAut (lBar X) :=
    (Sec4.thetaQuotMulAut X).comp X.normalizerMonoidHom with hT
  have hU₀X : U₀ ≤ Subgroup.normalizer (X : Set G) := hpairs.2.2.2.1
  have hEX : E ≤ Subgroup.normalizer (X : Set G) := hpair.mem_E.2.trans hAX
  have hTcomm : ∀ u (hu : u ∈ U₀), T ⟨u, hU₀X hu⟩ ∈ commutator (MulAut (lBar X)) := by
    intro u hu
    have hmap : (⁅U₀.subgroupOf (Subgroup.normalizer (X : Set G)),
        E.subgroupOf (Subgroup.normalizer (X : Set G))⁆).map
          (Subgroup.normalizer (X : Set G)).subtype = U₀ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hU₀X,
        Subgroup.map_subgroupOf_eq_of_le hEX, ← hU₀.2]
    have hmem : (⟨u, hU₀X hu⟩ : Subgroup.normalizer (X : Set G)) ∈
        ⁅U₀.subgroupOf (Subgroup.normalizer (X : Set G)),
          E.subgroupOf (Subgroup.normalizer (X : Set G))⁆ := by
      have hu' := hu
      rw [← hmap] at hu'
      obtain ⟨x, hx, hxu⟩ := hu'
      rwa [show x = ⟨u, hU₀X hu⟩ from Subtype.ext hxu] at hx
    have h1 : T ⟨u, hU₀X hu⟩ ∈ (⁅U₀.subgroupOf (Subgroup.normalizer (X : Set G)),
        E.subgroupOf (Subgroup.normalizer (X : Set G))⁆).map T := ⟨_, hmem, rfl⟩
    rw [Subgroup.map_commutator] at h1
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  have hTone : ∀ u (hu : u ∈ U₀), T ⟨u, hU₀X hu⟩ = 1 := by
    intro u hu
    have hu2 : u * u = 1 := by rw [← pow_two]; exact hU₀.1.2.1.2 u hu
    have hsq : T ⟨u, hU₀X hu⟩ * T ⟨u, hU₀X hu⟩ = 1 := by
      rw [← map_mul]
      have : (⟨u, hU₀X hu⟩ : Subgroup.normalizer (X : Set G)) * ⟨u, hU₀X hu⟩ = 1 :=
        Subtype.ext hu2
      rw [this, map_one]
    obtain ⟨m, hm⟩ := mem_inner_of_mulEquiv_projSL eL (hTcomm u hu) hsq
    have hmd : m * ((⟨d₀, hd₀B.2⟩ : X) : lBar X) = ((⟨d₀, hd₀B.2⟩ : X) : lBar X) * m := by
      have h1 : T ⟨u, hU₀X hu⟩ ((⟨d₀, hd₀B.2⟩ : X) : lBar X) = ((⟨d₀, hd₀B.2⟩ : X) : lBar X) := by
        rw [hT, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk]
        congr 1
        exact Subtype.ext (hUd u hu)
      rw [← hm, MulAut.conj_apply] at h1
      calc m * ((⟨d₀, hd₀B.2⟩ : X) : lBar X) =
          m * ((⟨d₀, hd₀B.2⟩ : X) : lBar X) * m⁻¹ * m := by group
        _ = ((⟨d₀, hd₀B.2⟩ : X) : lBar X) * m := by rw [h1]
    have hm2 : ∀ z : lBar X, m * m * z = z * (m * m) := by
      intro z
      have h1 : MulAut.conj (m * m) z = z := by
        rw [map_mul, hm, hsq, MulAut.one_apply]
      rw [MulAut.conj_apply] at h1
      calc m * m * z = m * m * z * (m * m)⁻¹ * (m * m) := by group
        _ = z * (m * m) := by rw [h1]
    have hm1 := eq_one_of_commute_typeOne hn eL hd₀B.2 hd₀T hmd hm2
    rw [← hm, hm1, map_one]
  have hθ : ⁅X, U₀⁆ ≤ inSubgroup (aschbacherSolvableCore 3) X := by
    rw [Subgroup.commutator_le]
    intro x hx u hu
    have h1 := congrArg (fun σ : MulAut (lBar X) => σ ((⟨x, hx⟩ : X) : lBar X)) (hTone u hu)
    simp only [hT, MonoidHom.comp_apply, Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have h2 := (inferInstance : (aschbacherSolvableCore 3 X).Normal).conj_mem _ h1 ⟨x, hx⟩
    refine ⟨_, h2, ?_⟩
    rw [commutatorElement_def]
    change x * ((u * x * u⁻¹)⁻¹ * x) * x⁻¹ = x * u * x⁻¹ * u⁻¹
    group
  have hXθ : X ≤ inSubgroup (aschbacherSolvableCore 3) X :=
    hpairs.2.2.2.2.2.1.symm.le.trans hθ
  have := Item222Proof.isSimpleGroup_projSL_three (GaloisField 2 n)
  have hsimp : IsSimpleGroup (lBar X) := eL.isSimpleGroup
  obtain ⟨z, hz⟩ := exists_ne (1 : lBar X)
  apply hz
  induction z using QuotientGroup.induction_on with
  | H x =>
    rw [QuotientGroup.eq_one_iff]
    obtain ⟨y, hy, hyx⟩ := hXθ x.2
    rwa [show y = x from Subtype.ext hyx] at hy

end CFSG.RankThree.PartTwo.Sec21.Item21Res6Proof

namespace CFSG.RankThree.PartTwo.Sec21

theorem item2115LThree_of (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) : Item2115LThree := by
  intro G _ _ A E U₀ a X c hpair hU₀ ⟨⟨n, hn, he, hcase⟩, h27, hS3⟩ hcA hca hcU hXc
  rcases hcase with ⟨heL, hC⟩ | ⟨heL, hC⟩
  · exact Item21Res6Proof.false_of_LThree h45 h66 ⟨hpair, ⟨n, hn, he, heL⟩, hC, h27, hS3⟩ hU₀
      hcA hca hcU hXc
  · exact Item21Res6Proof.false_of_SLThree h45 h66 hpair ⟨n, hn, he, heL⟩ hC h27 hS3 hcA hca hXc

end CFSG.RankThree.PartTwo.Sec21
