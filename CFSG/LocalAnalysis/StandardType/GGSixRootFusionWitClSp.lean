module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitClSpInv
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

namespace WitClSp

variable {K : Type} [Field K] {n p : ℕ}

theorem mulSingle_pow_eq_one {ζ : Kˣ} (hζ : ζ ^ p = 1) (j k : Fin n) :
    (Pi.mulSingle j ζ : Fin n → Kˣ) k ^ p = 1 := by
  by_cases hk : k = j
  · subst hk
    rw [Pi.mulSingle_eq_same, hζ]
  · rw [Pi.mulSingle_eq_of_ne hk, one_pow]

theorem conj_commute_witness {G : Type} [Group G] {φ : StatedSp n K →* G}
    {v g d : StatedSp n K} (hg : Commute (g * v * g⁻¹) d) :
    φ (g⁻¹ * d * g) * φ v = φ v * φ (g⁻¹ * d * g) ∧
      φ g * φ (g⁻¹ * d * g) * (φ g)⁻¹ = φ d := by
  constructor
  · rw [← map_mul, ← map_mul]
    congr 1
    calc g⁻¹ * d * g * v = g⁻¹ * (d * (g * v * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * v * g⁻¹ * d) * g := by rw [hg.eq]
      _ = v * (g⁻¹ * d * g) := by group
  · rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group

end WitClSp

section Inputs

open WitSp WitClSp CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot in
theorem exists_spSplit_frame {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU .PSp n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .PSp n f).D .PSp n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f - 1) :
    ∃ (A₀ : StatedSp n (GaloisField 2 f)) (φ₀ : StatedSp n (GaloisField 2 f) →* G),
      (∀ a, φ₀ a = ψ (A₀ * a * A₀⁻¹)) ∧ Function.Injective φ₀ ∧ φ₀.range = ggG0 p B x L D J ∧
      (∀ y ∈ Bs, ∃ u, y = φ₀ (diagSp (GaloisField 2 f) n u)) ∧ 4 ≤ n ∧
      4 ≤ Nat.card (GaloisField 2 f) ∧ p ∣ Nat.card (GaloisField 2 f) - 1 ∧ p.Prime ∧
      GGBstar p B Bs ∧ ∃ ζu : (GaloisField 2 f)ˣ, ζu ≠ 1 ∧ ζu ^ p = 1 := by
  obtain ⟨A₀, hA₀⟩ := ggSpBstarFrameInput_holds G p B Bs x L D J n f ψ hctx s1 hpq
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hadm := hctx.2.2.2.1.1
  have hf : 1 ≤ f := hadm.2.1
  have hn2 : 2 ≤ n := hadm.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hcardF]; exact hpq
  have hq4 : 4 ≤ 2 ^ f := by
    have h1 : 1 < 2 ^ f := Nat.one_lt_two_pow (by omega)
    have h2 := Nat.le_of_dvd (by omega) hpq
    have h3 := hp.two_le
    have h5 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have h4 : 4 ≤ Nat.card (GaloisField 2 f) := hcardF ▸ hq4
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hBs : GGBstar p B Bs := hctx.2.1
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : a ∈ Subgroup.center (StatedSp n (GaloisField 2 f)) := hker ha
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  obtain ⟨ψS, hψS⟩ : ∃ ψS : StatedSp n (GaloisField 2 f) →* G, ∀ a, ψS a = ψ a :=
    ⟨ψ, fun _ => rfl⟩
  have hψS' : Function.Injective ψS := fun a c h => hψ (by rw [← hψS, ← hψS]; exact h)
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : StatedSp n (GaloisField 2 f) →* G,
      φ₀ = ψS.comp (MulAut.conj A₀).toMonoidHom := ⟨_, rfl⟩
  have hφ₀a : ∀ a, φ₀ a = ψS (A₀ * a * A₀⁻¹) := fun a => by
    rw [hφ₀, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hframe₀ : ∀ y ∈ Bs, ∃ u, y = φ₀ (diagSp (GaloisField 2 f) n u) := by
    intro y hy
    obtain ⟨u, hu⟩ := hA₀ y hy
    refine ⟨u, ?_⟩
    rw [hu, RestSp.frameDiag, equivStatedSp_diagonal, hφ₀a, hψS]
  have hφinj : Function.Injective φ₀ := by
    intro a c h
    rw [hφ₀a, hφ₀a] at h
    exact mul_left_cancel (mul_right_cancel (hψS' h))
  have hrangeS : ψS.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, (hψS a).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a, hψS a⟩
  have hφrange : φ₀.range = ggG0 p B x L D J := by
    rw [← hrangeS]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [hφ₀a]
      exact ⟨_, rfl⟩
    · rintro ⟨a, rfl⟩
      refine ⟨A₀⁻¹ * a * A₀, ?_⟩
      rw [hφ₀a]
      congr 1
      group
  have hBsge : p ^ 4 ≤ Nat.card Bs := by
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have h4r : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
    exact (Nat.pow_le_pow_right hp.pos h4r).trans (hBcard ▸ hBle)
  have hn4 : 4 ≤ n := by
    have h := card_le_of_diag (φ := φ₀) hp hpF (X := Bs) Finset.univ fun y hy => by
      obtain ⟨u, rfl⟩ := hframe₀ y hy
      have hup : u ^ p = 1 := diagSp_injective (hφinj (by
        rw [map_pow, map_pow, hBs.2.1.2 _ hy, map_one, map_one]))
      exact ⟨u, rfl, fun k => congrFun hup k, fun k hk => absurd (Finset.mem_univ k) hk⟩
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (hBsge.trans h)
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpF
  obtain ⟨ζu, hζu⟩ : ∃ ζu : (GaloisField 2 f)ˣ, (ζu : GaloisField 2 f) = ζ :=
    ⟨Units.mk0 ζ (hζ.ne_zero hp.ne_zero), rfl⟩
  have hζu1 : ζu ≠ 1 := fun h => hζ.ne_one hp.one_lt (by rw [← hζu, h, Units.val_one])
  have hζup : ζu ^ p = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one,
    Units.val_one])
  exact ⟨A₀, φ₀, fun a => by rw [hφ₀a, hψS], hφinj, hφrange, hframe₀, hn4, h4, hpF, hp, hBs,
    ζu, hζu1, hζup⟩

open WitSp WitClSp CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.SeitzReduction.SymplecticPilot in
theorem ggSixRootFusionWitnessOn_PSpSplit : GGSixRootFusionWitnessOn GGPSpSplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 _ E r _ _ _ s hs hs2
  obtain ⟨rfl, hpq⟩ := hP
  obtain ⟨A₀, φ₀, -, hφinj, hφrange, hframe₀, hn4, h4, hpF, hp, hBs, ζu, hζu1, hζup⟩ :=
    exists_spSplit_frame hctx s1 hpq
  rw [← hφrange] at hs
  obtain ⟨v, rfl⟩ := hs
  have hv : v * v = 1 := by
    have h2 := pow_orderOf_eq_one (φ₀ v)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hφinj (by rw [h2, map_one])
  have hM : ∀ g, φ₀ g ∈ ggM p B x L D J := fun g =>
    Subgroup.le_normalizer (hφrange ▸ ⟨g, rfl⟩)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have h01 : (0 : Fin (m + 1 + 1 + 1)) ≠ 1 := by simp
  obtain ⟨g, hg | hg⟩ := exists_conj_commute_torusWit v hv ζu
  ·
    obtain ⟨heB, he1, L₂, hL₂, hcard⟩ := witness_of_diag h4 hp hpF hBs hφinj hφrange hframe₀
      (s := Pi.mulSingle 0 ζu) (mulSingle_pow_eq_one hζup 0) (j₁ := 0) (j₂ := 0)
      (by rw [Pi.mulSingle_eq_same]; exact hζu1)
      (fun k hk _ => by rw [Pi.mulSingle_eq_of_ne hk]) (k₀ := 1) h01.symm h01.symm
    obtain ⟨hcomm, hconj⟩ := conj_commute_witness (φ := φ₀) hg
    refine Or.inr (Or.inl ⟨_, hcomm, φ₀ g, hM g, ?_⟩)
    rw [hconj]
    exact ⟨he1, Or.inr (Or.inr ⟨heB, L₂, hL₂, Or.inl hcard⟩)⟩
  ·
    have h02 : (2 : Fin (m + 1 + 1 + 1)) ≠ 0 := by
      simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 1 + 1 + 1 by omega)]
    have h12 : (2 : Fin (m + 1 + 1 + 1)) ≠ 1 := by
      simp [Fin.ext_iff, Nat.mod_eq_of_lt (show 2 < m + 1 + 1 + 1 by omega)]
    obtain ⟨heB, he1, L₂, hL₂, hcard⟩ := witness_of_diag h4 hp hpF hBs hφinj hφrange hframe₀
      (s := Pi.mulSingle 0 ζu * Pi.mulSingle 1 ζu)
      (fun k => by rw [Pi.mul_apply, mul_pow, mulSingle_pow_eq_one hζup 0 k,
        mulSingle_pow_eq_one hζup 1 k, one_mul]) (j₁ := 0) (j₂ := 1)
      (by rw [Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h01, mul_one]
          exact hζu1)
      (fun k hk₁ hk₂ => by rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hk₁,
        Pi.mulSingle_eq_of_ne hk₂, mul_one]) (k₀ := 2) h02 h12
    obtain ⟨hcomm, hconj⟩ := conj_commute_witness (φ := φ₀) hg
    refine Or.inr (Or.inl ⟨_, hcomm, φ₀ g, hM g, ?_⟩)
    rw [hconj]
    exact ⟨he1, Or.inr (Or.inr ⟨heB, L₂, hL₂, Or.inl hcard⟩)⟩

end Inputs

end CFSG.StandardType
