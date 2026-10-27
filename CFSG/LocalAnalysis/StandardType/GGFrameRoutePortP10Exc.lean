module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGTableBExcBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGTorusE7Lang
import CFSG.LocalAnalysis.StandardType.GGTorusE8Scalar
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Cover
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10Bstar

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Blueprint.Chevalley

private theorem p10cAux_sc_map {K H : Type} [Group K] [Group H] (e : K ≃* H)
    {E : Subgroup K}
    (hSC : ∀ k : K, (∀ x ∈ E, k * x = x * k) → k ^ 3 = 1 → k ∈ E) :
    ∀ g : H, (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ 3 = 1 →
      g ∈ E.map e.toMonoidHom := by
  intro g hg hg3
  have hk3 : e.symm g ^ 3 = 1 := by
    refine e.injective ?_
    rw [map_pow, map_one, e.apply_symm_apply, hg3]
  have hkg : ∀ x ∈ E, e.symm g * x = x * e.symm g := by
    intro x hx
    have hx' : e x ∈ E.map e.toMonoidHom := Subgroup.mem_map_of_mem e.toMonoidHom hx
    have hcomm := hg (e x) hx'
    refine e.injective ?_
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact hcomm
  have hkE : e.symm g ∈ E := hSC (e.symm g) hkg hk3
  obtain ⟨y, hy, hyg⟩ : ∃ y ∈ E, e y = g := ⟨e.symm g, hkE, e.apply_symm_apply g⟩
  rw [← hyg]
  exact Subgroup.mem_map_of_mem e.toMonoidHom hy

private theorem p10cAux_hinn {G : Type} [Group G] {Bs K : Subgroup G}
    {H : Type} [Group H] {θ : ↥K ⧸ Subgroup.center ↥K ≃* H} {I : Set (MulAut H)}
    (hBsN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hbs : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hZ : Subgroup.center ↥K = ⊥)
    (hφinn : ∀ φ ∈ I, ∃ k₀ : ↥K, ∀ k : ↥K,
      φ (θ (QuotientGroup.mk k)) = θ (QuotientGroup.mk (k₀ * k * k₀⁻¹))) :
    ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹ := by
  intro b hb
  obtain ⟨φ, hφI, hφ⟩ := hbs b⁻¹ (Bs.inv_mem hb)
  obtain ⟨k₀, hk₀⟩ := hφinn φ hφI
  refine ⟨(k₀ : G), k₀.2, fun l hl => ?_⟩
  have hmem : b * l * b⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (hBsN hb) l).mp hl
  let l' : ↥K := ⟨b * l * b⁻¹, hmem⟩
  have hrel : (l' : G) = (b⁻¹)⁻¹ * (⟨l, hl⟩ : ↥K) * b⁻¹ := by
    simp [l']
  have h1 := hφ (⟨l, hl⟩ : ↥K) l' hrel
  have h2 := hk₀ (⟨l, hl⟩ : ↥K)
  have hquot : (QuotientGroup.mk l' : ↥K ⧸ Subgroup.center ↥K) =
      QuotientGroup.mk (k₀ * (⟨l, hl⟩ : ↥K) * k₀⁻¹) :=
    θ.injective (h1.symm.trans h2)
  have hmemc : (l')⁻¹ * (k₀ * (⟨l, hl⟩ : ↥K) * k₀⁻¹) ∈ Subgroup.center ↥K :=
    QuotientGroup.eq.mp hquot
  rw [hZ, Subgroup.mem_bot] at hmemc
  have hK' : l' = k₀ * (⟨l, hl⟩ : ↥K) * k₀⁻¹ := by
    calc l' = l' * ((l')⁻¹ * (k₀ * (⟨l, hl⟩ : ↥K) * k₀⁻¹)) := by rw [hmemc, mul_one]
      _ = k₀ * (⟨l, hl⟩ : ↥K) * k₀⁻¹ := by rw [mul_inv_cancel_left]
  have hG : (l' : G) = (k₀ : G) * l * (k₀ : G)⁻¹ := by
    have h := congrArg Subtype.val hK'
    simpa using h
  calc b * l * b⁻¹ = (l' : G) := by simp [l']
    _ = (k₀ : G) * l * (k₀ : G)⁻¹ := hG

private theorem p10cAux_data {G : Type} [Group G] {Bs K : Subgroup G} {τ : Tag}
    {t : LargeEvenLieTag} (hτ : (τ = .E7 ∧ t = .E7) ∨ (τ = .E8 ∧ t = .E8))
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = t ∧ lab.n = 1) 3 Bs K) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ θ : ↥K ⧸ Subgroup.center ↥K ≃* TableBExc.RecipeGroup τ F,
        commutator ↥K = ⊤ ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ TableBExc.RecipeID τ F,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  rcases hτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    obtain ⟨hperf, lab, _, hraw⟩ := hK
    obtain ⟨R, _, I, Fd, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
    obtain ⟨-, -, -, ⟨⟨htag, hn1⟩, -, -⟩⟩ := hQ
    obtain ⟨tag, rank, m⟩ := lab
    subst htag
    subst hn1
    simp only at hraw
    obtain ⟨F, fieldF, finiteF, hcardF, hQ2⟩ := hraw
    obtain ⟨-, -, θ, ⟨⟨-, -⟩, hBsN, hbs⟩⟩ := hQ2
    exact ⟨F, fieldF, finiteF, by simpa using hcardF, θ, hperf, hBsN, hbs⟩

private theorem p10cAux_decomp {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {z : G} {n : ℕ} {H : Type} [Group H] (e : ↥K ≃* H)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hZ : Subgroup.center ↥K = ⊥)
    (hinn : ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹) :
    IsElemAbelian 3 (((Bs ⊓ K).subgroupOf K).map e.toMonoidHom) ∧
      Nat.card (((Bs ⊓ K).subgroupOf K).map e.toMonoidHom) = 3 ^ (n - 1) ∧
      ∀ g : H, (∀ x ∈ ((Bs ⊓ K).subgroupOf K).map e.toMonoidHom, g * x = x * g) →
        g ^ 3 = 1 → g ∈ ((Bs ⊓ K).subgroupOf K).map e.toMonoidHom := by
  obtain ⟨-, hcardEK, -, -, hSC⟩ :=
    P10b_bstar_decomp hBs hcard hz hz1 hN hker hZ hinn hBstar
  refine ⟨?_, ?_, p10cAux_sc_map e hSC⟩
  · exact ((hBs.subgroupOf K).mono (by intro x hx; exact hx.1)).map e.toMonoidHom
  · rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Bs ⊓ K ≤ K)).toEquiv,
      hcardEK]

theorem P10c_E7_eight
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G} {n : ℕ}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 7 ≤ n) (hz : z ∈ Bs)
    (hz1 : z ≠ 1) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∧ lab.n = 1) 3 Bs K) :
    n = 8 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ eK : ↥K ≃* adjointGroup .E7 F,
        IsElemAbelian 3 (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) ∧
        Nat.card (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) = 3 ^ 7 ∧
        ∀ g : adjointGroup .E7 F,
          (∀ x ∈ ((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom, g * x = x * g) → g ^ 3 = 1 →
            g ∈ ((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom := by
  obtain ⟨F, fieldF, finiteF, hcardF, θ, hperf, hBsN, hbs⟩ :=
    p10cAux_data (τ := .E7) (t := .E7) (Or.inl ⟨rfl, rfl⟩) hK
  have hF2 : Nat.card F = 2 := by simpa using hcardF
  obtain ⟨hZ, eK, -, hφinn⟩ := P10a_cover_E7 (F := F) (K := ↥K) hF2 hperf θ
  have hinn : ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹ :=
    p10cAux_hinn hBsN hbs hZ hφinn
  obtain ⟨hEel, hEcard, hESC⟩ :=
    p10cAux_decomp (n := n) eK hBs hcard hz hz1 hN hker hBstar hZ hinn
  have hcharF : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
      rw [Fintype.card_eq_nat_card]
      simpa using hF2)
  have : NeZero 3 := ⟨by norm_num⟩
  have hq : 3 ∣ Nat.card F + 1 := ⟨1, by rw [hF2]⟩
  have hcard6 : 3 ^ 6 ≤ Nat.card (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega : 6 ≤ n - 1)
  obtain ⟨-, Fr, ζ, hζ, ι, nn, hFr, hΦ, hwneg, hζo, hιinj, hιrange, -, -, -, -⟩ :=
    exists_e7_scalar_frame (K := F) (p := 3) Nat.prime_three (by norm_num) hq
      (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) hEel hcard6 hESC
  have hdom : Nat.card (Multiplicative (Fin Tag.E7.rank → ZMod 3)) = 3 ^ 7 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hcardι : Nat.card ι.range = 3 ^ 7 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hιinj, Subgroup.card_top, hdom]
  have hEcard7 : Nat.card (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) = 3 ^ 7 := by
    rw [← hιrange, hcardι]
  have hpow : 3 ^ 7 = 3 ^ (n - 1) := hEcard7.symm.trans hEcard
  have hn1 : 7 = n - 1 := Nat.pow_right_injective (a := 3) (by norm_num) hpow
  have hn8 : n = 8 := by omega
  exact ⟨hn8, F, fieldF, finiteF, hF2, eK, hEel, hEcard7, hESC⟩

theorem P10d_E8_not_eight
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {z : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 8) (hz : z ∈ Bs) (hz1 : z ≠ 1)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hK : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E8 ∧ lab.n = 1) 3 Bs K) : False := by
  obtain ⟨F, fieldF, finiteF, hcardF, θ, hperf, hBsN, hbs⟩ :=
    p10cAux_data (τ := .E8) (t := .E8) (Or.inr ⟨rfl, rfl⟩) hK
  have hF2 : Nat.card F = 2 := by simpa using hcardF
  obtain ⟨hZ, eK, -, hφinn⟩ := P10a_cover_E8 (F := F) (K := ↥K) hF2 hperf θ
  have hinn : ∀ b ∈ Bs, ∃ k ∈ K, ∀ l ∈ K, b * l * b⁻¹ = k * l * k⁻¹ :=
    p10cAux_hinn hBsN hbs hZ hφinn
  obtain ⟨hEel, hEcard, hESC⟩ :=
    p10cAux_decomp (n := 8) eK hBs hcard hz hz1 hN hker hBstar hZ hinn
  have hEcard7 : Nat.card (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) = 3 ^ 7 := by
    simpa using hEcard
  have hcharF : CharP F 2 := by
    have : Fintype F := Fintype.ofFinite F
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
      rw [Fintype.card_eq_nat_card]
      simpa using hF2)
  have hq : 3 ∣ Nat.card F + 1 := ⟨1, by rw [hF2]⟩
  obtain ⟨-, Fr, ζ, hζ, ι, nn, hFr, hΦ, hwneg, hζo, hιinj, hιrange, -, -, -, -⟩ :=
    E8ScalarTorus.exists_frame_of_selfCentralizing_three (K := F) hq
      (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) hEel (le_of_eq hEcard7.symm) hESC
  have hdom : Nat.card (Multiplicative (Fin Tag.E8.rank → ZMod 3)) = 3 ^ 8 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rfl
  have hcardι : Nat.card ι.range = 3 ^ 8 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hιinj, Subgroup.card_top, hdom]
  have hEcard8 : Nat.card (((Bs ⊓ K).subgroupOf K).map eK.toMonoidHom) = 3 ^ 8 := by
    rw [← hιrange, hcardι]
  have hcontra : 3 ^ 7 = 3 ^ 8 := hEcard7.symm.trans hEcard8
  have h78 : 7 = 8 := Nat.pow_right_injective (a := 3) (by norm_num) hcontra
  omega

theorem P10ef_E8_twoLocalRank
    {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G)) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hK : LargeEvenMarking K fun lab _ _ _ _ _ => lab.tag = .E8) :
    8 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨hperf, lab, _, hraw⟩ := hK
  obtain ⟨R, _, I, Fd, hQ⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, htag⟩ := hQ
  obtain ⟨tag, rank, m⟩ := lab
  subst htag
  simp only at hraw
  obtain ⟨F, fieldF, finiteF, hcardF, hQ2⟩ := hraw
  obtain ⟨-, -, θ, -⟩ := hQ2
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharF : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m) (by
    rw [Fintype.card_eq_nat_card]
    exact hcardF)
  have hlift : GGTorusLift 3 7 (TableBExc.RecipeGroup .E8 F) :=
    TableBExcTwo.ggTorusLift_E8Two
  have h8 := succ_le_twoLocalRank_of_torusLift (p := 3) (r := 7) Nat.prime_three
    hKz hz3 hz1 hperf θ hlift
  simpa using h8

end CFSG.StandardType.FrameRoute
