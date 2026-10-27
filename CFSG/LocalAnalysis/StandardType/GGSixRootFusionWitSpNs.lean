module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsCore
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitComp
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSpNs
public import CFSG.Sporadic.Suz.Setup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open scoped MatrixGroups

namespace WitSpNs

theorem bstarWit_of_planeMat {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2]
    {n p f : ℕ} (hn : 4 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2) (hK : ¬ p ∣ Nat.card K - 1)
    {ψS : StatedSp n K →* G} (hψ : Function.Injective ψS) {Bs G₀ : Subgroup G}
    (hrange : ψS.range = G₀) {A₀ : StatedSp n K} {C : Matrix (Fin 2) (Fin 2) K}
    (hCp : C ^ p = 1) (hcunit : ∀ j : ℕ, ¬ p ∣ j → ∀ c : K, IsUnit (C ^ j - c • 1))
    (hreal : ∀ k : Fin n → ℕ, ∃ Dk : StatedSp n K,
      mat n K Dk = planeMat (fun j => C ^ k j) ∧ ψS (A₀ * Dk * A₀⁻¹) ∈ Bs)
    (hrep : ∀ b ∈ Bs, ∃ (k : Fin n → ℕ) (Dk : StatedSp n K),
      mat n K Dk = planeMat (fun j => C ^ k j) ∧ b = ψS (A₀ * Dk * A₀⁻¹))
    (π : Equiv.Perm (Fin n)) {k : Fin n → ℕ} (hk : RootPlaneSp.PlaneSupp k)
    {D₁ : StatedSp n K} (hD₁ : mat n K D₁ = planeMat (fun j => C ^ k (π j))) (hD₁1 : D₁ ≠ 1)
    (t : StatedLieTag) : GGSixBstarWit p Bs G₀ t f (ψS (A₀ * D₁ * A₀⁻¹)) := by
  classical
  have hmemB : ψS (A₀ * D₁ * A₀⁻¹) ∈ Bs := by
    obtain ⟨Dk, hDk, hmem⟩ := hreal (fun j => k (π j))
    rwa [mat_injective (hDk.trans hD₁.symm)] at hmem
  have hX1 : A₀ * D₁ * A₀⁻¹ ≠ 1 := by
    intro h
    apply hD₁1
    calc D₁ = A₀⁻¹ * (A₀ * D₁ * A₀⁻¹) * A₀ := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  refine ⟨hmemB, fun h => hX1 (hψ (by rw [h, map_one])), ?_⟩
  have hrealπ : ∀ k' : Fin n → ℕ, ∃ X : StatedSp n K,
      RootPlaneSp.SpBlockMat (A₀ : GL (Fin n ⊕ Fin n) K) (epsPlane π) C X k' := by
    intro k'
    obtain ⟨Dk, hDk, -⟩ := hreal (fun j => k' (π j))
    exact ⟨_, spBlockMat_of_planeMat A₀ Dk π C k' hDk⟩
  obtain ⟨L₀, hL₀, hL₀c⟩ := ggSpNonsplitCompInput_holds K n 2 n 0 p hp hp2 hK le_rfl hn C
    (epsPlane π) (A₀ : GL (Fin n ⊕ Fin n) K) hCp hcunit hrealπ (A₀ * D₁ * A₀⁻¹) k hk
    (spBlockMat_of_planeMat A₀ D₁ π C k hD₁) hX1
  have hmapC : (Subgroup.centralizer {A₀ * D₁ * A₀⁻¹}).map ψS =
      ψS.range ⊓ Subgroup.centralizer {ψS (A₀ * D₁ * A₀⁻¹)} := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, rfl⟩, by rw [← map_mul, ← map_mul, hz]⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨z, hψ ((map_mul ψS _ _).trans (hz.trans (map_mul ψS _ _).symm)), rfl⟩
  refine ⟨L₀.map ψS, ?_, Or.inl ?_⟩
  · have h1 := isComponentOf_map_of_injective ψS hψ hL₀
    rwa [hmapC, hrange] at h1
  have : NeZero p := ⟨hp.ne_zero⟩
  have hb1 : ∀ b : ↥(Bs ⊓ Subgroup.centralizer ((L₀.map ψS : Subgroup G) : Set G)), b.1 ∈ Bs :=
    fun b => (Subgroup.mem_inf.mp b.2).1
  have hb2 : ∀ b : ↥(Bs ⊓ Subgroup.centralizer ((L₀.map ψS : Subgroup G) : Set G)),
      b.1 ∈ Subgroup.centralizer ((L₀.map ψS : Subgroup G) : Set G) :=
    fun b => (Subgroup.mem_inf.mp b.2).2
  have hi₀ : 0 < n := by omega
  have hi₁ : 1 < n := by omega
  choose kOf DOf hDOf hbOf using hrep
  let θ : ↥(Bs ⊓ Subgroup.centralizer ((L₀.map ψS : Subgroup G) : Set G)) →
      ZMod p × ZMod p :=
    fun b => (((kOf b.1 (hb1 b) (π.symm ⟨0, hi₀⟩) : ℕ) : ZMod p),
      ((kOf b.1 (hb1 b) (π.symm ⟨1, hi₁⟩) : ℕ) : ZMod p))
  have hdvd : ∀ b : ↥(Bs ⊓ Subgroup.centralizer ((L₀.map ψS : Subgroup G) : Set G)),
      ∀ j : Fin n, 2 ≤ ((π j : Fin n) : ℕ) → p ∣ kOf b.1 (hb1 b) j := by
    intro b j hj
    have hY : RootPlaneSp.SpBlockMat (A₀ : GL (Fin n ⊕ Fin n) K) (epsPlane π) C
        (A₀ * DOf b.1 (hb1 b) * A₀⁻¹) (fun i => kOf b.1 (hb1 b) (π.symm i)) :=
      spBlockMat_of_planeMat A₀ _ π C _ (by
        rw [hDOf]
        simp only [Equiv.symm_apply_apply])
    have hYc : A₀ * DOf b.1 (hb1 b) * A₀⁻¹ ∈
        Subgroup.centralizer (L₀ : Set (StatedSp n K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      apply hψ
      have := (Subgroup.mem_centralizer_iff.mp (hb2 b)) (ψS l) ⟨l, hl, rfl⟩
      rw [map_mul ψS l, map_mul ψS (A₀ * DOf b.1 (hb1 b) * A₀⁻¹) l, ← hbOf b.1 (hb1 b)]
      exact this
    have h1 := hL₀c _ _ hY hYc (π j) hj
    simpa using h1
  have hθ : Function.Injective θ := by
    intro b b' hbb
    have hmod : ∀ j : Fin n, kOf b.1 (hb1 b) j % p = kOf b'.1 (hb1 b') j % p := by
      intro j
      by_cases hj0 : π j = ⟨0, hi₀⟩
      · have h1 := congrArg Prod.fst hbb
        simp only [θ] at h1
        rw [← hj0, Equiv.symm_apply_apply, ZMod.natCast_eq_natCast_iff'] at h1
        exact h1
      by_cases hj1 : π j = ⟨1, hi₁⟩
      · have h1 := congrArg Prod.snd hbb
        simp only [θ] at h1
        rw [← hj1, Equiv.symm_apply_apply, ZMod.natCast_eq_natCast_iff'] at h1
        exact h1
      have h2 : 2 ≤ ((π j : Fin n) : ℕ) := by
        have h0' : ((π j : Fin n) : ℕ) ≠ 0 := fun h => hj0 (Fin.ext h)
        have h1' : ((π j : Fin n) : ℕ) ≠ 1 := fun h => hj1 (Fin.ext h)
        omega
      rw [Nat.mod_eq_zero_of_dvd (hdvd b j h2), Nat.mod_eq_zero_of_dvd (hdvd b' j h2)]
    have hD : DOf b.1 (hb1 b) = DOf b'.1 (hb1 b') := by
      apply mat_injective
      rw [hDOf, hDOf]
      congr 1
      funext j
      rw [pow_eq_pow_mod _ hCp, hmod j, ← pow_eq_pow_mod _ hCp]
    apply Subtype.ext
    calc b.1 = ψS (A₀ * DOf b.1 (hb1 b) * A₀⁻¹) := hbOf _ _
      _ = ψS (A₀ * DOf b'.1 (hb1 b') * A₀⁻¹) := by rw [hD]
      _ = b'.1 := (hbOf _ _).symm
  calc Nat.card ↥(Bs ⊓ Subgroup.centralizer ((L₀.map ψS : Subgroup G) : Set G))
      ≤ Nat.card (ZMod p × ZMod p) := Nat.card_le_card_of_injective θ hθ
    _ = p ^ 2 := by rw [Nat.card_prod, Nat.card_zmod, sq]

theorem exists_perm_two {n : ℕ} {i j a b : Fin n} (hij : i ≠ j) (hab : a ≠ b) :
    ∃ π : Equiv.Perm (Fin n), π i = a ∧ π j = b := by
  refine ⟨(Equiv.swap i a).trans (Equiv.swap (Equiv.swap i a j) b), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => ?_) hab
    have h1 := Equiv.swap_apply_eq_iff.mp h.symm
    rw [Equiv.swap_apply_right] at h1
    exact hij h1.symm
  · rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem ne_one_of_isUnit {K : Type} [Field K] {C : Matrix (Fin 2) (Fin 2) K}
    (h : IsUnit (C ^ 1 - (1 : K) • 1)) : C ≠ 1 := by
  rintro rfl
  rw [pow_one, one_smul, sub_self] at h
  exact not_isUnit_zero h

end WitSpNs

open WitSpNs in
theorem planeWitness_core {G : Type} [Group G] {f n p : ℕ} (hf : 1 ≤ f) (hrk : 2 ≤ n)
    {ψ : StatedSp n (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)))
    (hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥) (hp : p.Prime) (hp2 : p ≠ 2)
    {B Bs G₀ : Subgroup G} (hBs : GGBstar p B Bs) (hrange : ψ.range = G₀)
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b)
    (hcard : p ^ 4 ≤ Nat.card Bs) (hpq : p ∣ 2 ^ f + 1) :
    3 ≤ n ∧ ∃ (A₀ : StatedSp n (GaloisField 2 f)) (T : SL(2, GaloisField 2 f)),
      (∀ i : Fin n, GGSixBstarWit p Bs G₀ .PSp f
        (ψ (A₀ * longBlock (GaloisField 2 f) n i T * A₀⁻¹))) ∧
      ∀ i j : Fin n, i ≠ j → GGSixBstarWit p Bs G₀ .PSp f
        (ψ (A₀ * (longBlock (GaloisField 2 f) n i T * longBlock (GaloisField 2 f) n j T) *
          A₀⁻¹)) := by
  classical
  have : NeZero n := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [AutPSp.center_eq_bot] at hz
    exact Subgroup.mem_bot.mp hz
  have hmem : ∀ b ∈ Bs, b ∈ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ
      hker (hdiag b hb)
    rw [hCψ, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  have hn4 : 4 ≤ n :=
    AutPSp.four_le_of_bstar (K := GaloisField 2 f) hrk ψ hker hCψ hp hp2 hBs.2.1 hcard hdiag
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq' : p ∣ Nat.card (GaloisField 2 f) + 1 := by
    rw [hcardF]
    exact hpq
  have hK : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := SpNS.not_dvd_card_sub_one hp hp2 hpq'
  have hmax : ∀ Y : StatedSp n (GaloisField 2 f), (∀ X, ψ X ∈ Bs → Commute Y X) →
      Y ^ p = 1 → ψ Y ∈ Bs := by
    intro Y hY hYp
    refine hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
      (by rw [← map_pow, hYp, map_one])
    obtain ⟨X, rfl⟩ := hmem b hb
    rw [← map_mul, ← map_mul, (hY X hb).eq]
  obtain ⟨A₀, T, hTp, hunit, hreal, hrep⟩ := exists_symplecticPlaneFrame
    (K := GaloisField 2 f) (n := n) (by omega) hp hpq' (fun X => ψ X ∈ Bs)
    (fun X X' hX hX' => hψ (by
      rw [map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hBs.2.1 hX hX'))
    (fun X hX => hψ (by rw [map_pow, map_one]; exact hBs.2.1.2 _ hX)) hmax
  have hrep' : ∀ b ∈ Bs, ∃ (k : Fin n → ℕ) (Dk : StatedSp n (GaloisField 2 f)),
      mat n _ Dk = planeMat (fun j => (T : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) ^ k j) ∧
        b = ψ (A₀ * Dk * A₀⁻¹) := by
    intro b hb
    obtain ⟨X, rfl⟩ := hmem b hb
    obtain ⟨k, Dk, hDk, hX⟩ := hrep X hb
    exact ⟨k, Dk, hDk, by rw [hX]⟩
  have hT1 := ne_one_of_isUnit (hunit 1 (Nat.Prime.not_dvd_one hp) 1)
  have hi₀ : 0 < n := by omega
  have hi₁ : 1 < n := by omega
  have h01 : (⟨0, hi₀⟩ : Fin n) ≠ ⟨1, hi₁⟩ := fun h => by simp at h
  refine ⟨by omega, A₀, T, fun i => ?_, fun i j hij => ?_⟩
  ·
    refine bstarWit_of_planeMat hn4 hp hp2 hK hψ hrange hTp hunit hreal hrep'
      (Equiv.swap i ⟨0, hi₀⟩) (k := Pi.single ⟨0, hi₀⟩ 1) (fun b hb => ?_) ?_ ?_ .PSp
    · refine Pi.single_eq_of_ne (fun h => ?_) _
      rw [h] at hb
      simp at hb
    · rw [mat_longBlock_eq_planeMat]
      congr 1
      funext l
      by_cases hl : l = i
      · subst hl
        simp
      · have h1 : Equiv.swap i ⟨0, hi₀⟩ l ≠ ⟨0, hi₀⟩ := fun h => by
          rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
          exact hl h
        rw [Function.update_of_ne hl, Pi.single_eq_of_ne h1, pow_zero]
    · intro h1
      have h2 := congrArg (mat n (GaloisField 2 f)) h1
      rw [mat_longBlock_eq_planeMat, map_one, ← planeMat_one] at h2
      have h3 := congrFun (planeMat_injective h2) i
      rw [Function.update_self] at h3
      exact hT1 h3
  ·
    obtain ⟨π, hπi, hπj⟩ := exists_perm_two hij h01
    have hmat : mat n (GaloisField 2 f) (longBlock (GaloisField 2 f) n i T *
        longBlock (GaloisField 2 f) n j T) =
        planeMat fun l => Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) _)) i
          (T : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) l *
          Function.update (fun _ => (1 : Matrix (Fin 2) (Fin 2) _)) j
            (T : Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) l := by
      rw [map_mul, mat_longBlock_eq_planeMat, mat_longBlock_eq_planeMat, planeMat_mul]
    refine bstarWit_of_planeMat hn4 hp hp2 hK hψ hrange hTp hunit hreal hrep' π
      (k := Pi.single ⟨0, hi₀⟩ 1 + Pi.single ⟨1, hi₁⟩ 1) (fun b hb => ?_) ?_ ?_ .PSp
    · have hb0 : b ≠ ⟨0, hi₀⟩ := fun h => by rw [h] at hb; simp at hb
      have hb1 : b ≠ ⟨1, hi₁⟩ := fun h => by rw [h] at hb; simp at hb
      rw [Pi.add_apply, Pi.single_eq_of_ne hb0, Pi.single_eq_of_ne hb1, add_zero]
    · rw [hmat]
      congr 1
      funext l
      by_cases hli : l = i
      · subst hli
        rw [Function.update_self, Function.update_of_ne hij, mul_one, hπi, Pi.add_apply,
          Pi.single_eq_same, Pi.single_eq_of_ne h01, add_zero, pow_one]
      by_cases hlj : l = j
      · subst hlj
        rw [Function.update_self, Function.update_of_ne (Ne.symm hij), one_mul, hπj,
          Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm h01), zero_add, pow_one]
      · have h0 : π l ≠ ⟨0, hi₀⟩ := fun h => hli (π.injective (h.trans hπi.symm))
        have h1 : π l ≠ ⟨1, hi₁⟩ := fun h => hlj (π.injective (h.trans hπj.symm))
        rw [Function.update_of_ne hli, Function.update_of_ne hlj, mul_one, Pi.add_apply,
          Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, add_zero, pow_zero]
    · intro h1
      have h2 := congrArg (mat n (GaloisField 2 f)) h1
      rw [hmat, map_one, ← planeMat_one] at h2
      have h3 := congrFun (planeMat_injective h2) i
      simp only [Function.update_self, Function.update_of_ne hij, mul_one] at h3
      exact hT1 h3

section Inputs

theorem ggSpPlaneWitnessInputOn_nonsplit :
    GGSpPlaneWitnessInputOn fun _ f p => p ∣ 2 ^ f + 1 := by
  intro G _ _ p B Bs x L D J n f ψ hpq hctx s1
  have hadm := hctx.2.2.2.1.1
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hctx.range_eq]
    exact s1.1
  have hcard : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.sstar.1.2.1
    have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.bstar.1
    have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hctx.beta.2.2.2
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hctx.prime.pos hr4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBBs
  exact planeWitness_core hadm.2.1 hadm.2.2.1 hctx.2.2.2.2.1.2 hCψ hctx.prime hctx.ne_two
    hctx.bstar hctx.range_eq (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb) hcard hpq

end Inputs

end CFSG.StandardType
