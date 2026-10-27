module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneMoving

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Core

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem ggL46_torus_of_cent (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hC : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d)
    (htorus : ∃ s : ℕ, 2 ≤ s ∧
        (∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        (∀ u ∈ U₁, u ^ p ^ s ∈ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        (∃ u ∈ U₁, u ^ p ^ (s - 1) ∉ U ⊓ Subgroup.centralizer (K : Set G)) ∧
        ∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
          ∀ u ∈ U₁, (u ^ (1 + p ^ (s - 1)))⁻¹ * (x'⁻¹ * u * x') ∈
            U ⊓ Subgroup.centralizer (K : Set G)) :
    (∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) ∧ ∃ s : ℕ, 2 ≤ s ∧ (∀ u ∈ U₁, u ^ p ^ s = 1) ∧
      (∃ u ∈ U₁, orderOf u = p ^ s) ∧
      ∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
        ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1)) := by
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨c, hc, t, ht, hr, hrd⟩ := hcfg.exists_moving_ct
  have hii := ggL45_inf_conj_eq_one_of_cent hraw hiso hcfg hC hr hrd
  have hrU₁ : c * t ∈ Subgroup.normalizer (U₁ : Set G) := hS.2.2.2.2.2.2.2.2 hr
  have hconj : ∀ a ∈ U₁, (c * t) * a * (c * t)⁻¹ ∈ U₁ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hrU₁ a).mp ha
  obtain ⟨s, hs, hcommV, hexpV, ⟨u₀, hu₀, hu₀V⟩, x', hx'x, hx'V⟩ := htorus
  have hab : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := by
    intro a ha b hb
    have h2 : (c * t) * (a * b * a⁻¹ * b⁻¹) * (c * t)⁻¹ ∈
        U ⊓ Subgroup.centralizer (K : Set G) := by
      have := hcommV _ (hconj a ha) _ (hconj b hb)
      have e : (c * t) * (a * b * a⁻¹ * b⁻¹) * (c * t)⁻¹ =
          ((c * t) * a * (c * t)⁻¹) * ((c * t) * b * (c * t)⁻¹) *
            ((c * t) * a * (c * t)⁻¹)⁻¹ * ((c * t) * b * (c * t)⁻¹)⁻¹ := by group
      rw [e]
      exact this
    have h3 := hii _ (hcommV a ha b hb) h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hexp : ∀ u ∈ U₁, u ^ p ^ s = 1 := by
    intro u hu
    refine hii _ (hexpV u hu) ?_
    rw [← conj_pow]
    exact hexpV _ (hconj u hu)
  have hs1 : 1 ≤ s := by omega
  have hord : ∃ u ∈ U₁, orderOf u = p ^ s := by
    refine ⟨u₀, hu₀, ?_⟩
    have hne : ¬ u₀ ^ p ^ (s - 1) = 1 := fun h => hu₀V (h ▸ one_mem _)
    have h := orderOf_eq_prime_pow hne (by rw [Nat.sub_add_cancel hs1]; exact hexp u₀ hu₀)
    rwa [Nat.sub_add_cancel hs1] at h
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have htx : t * x * t⁻¹ = x := by
    have h1 := Subgroup.mem_centralizer_iff.mp (hLx ht.1) x rfl
    rw [← h1, mul_inv_cancel_right]
  have hrx : (c * t) * x * (c * t)⁻¹ = c * x * c⁻¹ := by
    rw [show (c * t) * x * (c * t)⁻¹ = c * (t * x * t⁻¹) * c⁻¹ by group, htx]
  have hcB₁ : c ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hc
  have hcd : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    le_normalizer_zpowers_of_le hcfg.d_mem le_rfl hc
  have hcK := ggL45_normalizer_le_of_canonical hcfg.1 hcfg.2.2.2.2.2.1 ⟨hcB₁, hcd⟩
  have hcxU : c * x * c⁻¹ ∈ U := by
    rw [← hrx]
    exact (Subgroup.mem_normalizer_iff.mp hr.1 x).mp hxU
  have hw₀ : (c * t) * x * (c * t)⁻¹ * x⁻¹ ∈ U₁ := by
    rw [hrx]
    exact ggL4546_comm_mem hraw hcen hiso hcfg hcK hcxU
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, x ^ j = x' := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hx'x ▸ Subgroup.mem_zpowers x'))
  have hxN : x ∈ Subgroup.normalizer (U₁ : Set G) := hcfg.le_normalizer_part hxU
  have hw' : (c * t) * x ^ j * (c * t)⁻¹ * (x ^ j)⁻¹ ∈ U₁ := by
    have h := mul_pow_mul_inv_pow_mem hw₀ hxN j
    rw [show (c * t) * x * (c * t)⁻¹ * x⁻¹ * x = (c * t) * x * (c * t)⁻¹ by group,
      conj_pow] at h
    exact h
  set w' := (c * t) * x ^ j * (c * t)⁻¹ * (x ^ j)⁻¹ with hw'def
  have hy : (c * t) * x ^ j * (c * t)⁻¹ = w' * x ^ j := by rw [hw'def]; group
  refine ⟨hab, s, hs, hexp, hord, x ^ j, hx'x, fun u hu => ?_⟩
  set e := 1 + p ^ (s - 1) with he
  have hu' : (c * t) * u * (c * t)⁻¹ ∈ U₁ := hconj u hu
  have hw'u : w'⁻¹ * ((c * t) * u * (c * t)⁻¹) * w' = (c * t) * u * (c * t)⁻¹ := by
    rw [mul_assoc, hab _ hu' _ hw', inv_mul_cancel_left]
  have key : (c * t) * ((u ^ e)⁻¹ * ((x ^ j)⁻¹ * u * x ^ j)) * (c * t)⁻¹ =
      (((c * t) * u * (c * t)⁻¹) ^ e)⁻¹ *
        ((x ^ j)⁻¹ * ((c * t) * u * (c * t)⁻¹) * x ^ j) := by
    have h1 : ((c * t) * u * (c * t)⁻¹) ^ e = (c * t) * u ^ e * (c * t)⁻¹ := conj_pow
    calc (c * t) * ((u ^ e)⁻¹ * ((x ^ j)⁻¹ * u * x ^ j)) * (c * t)⁻¹
        = ((c * t) * u ^ e * (c * t)⁻¹)⁻¹ * (((c * t) * x ^ j * (c * t)⁻¹)⁻¹ *
            ((c * t) * u * (c * t)⁻¹) * ((c * t) * x ^ j * (c * t)⁻¹)) := by group
      _ = (((c * t) * u * (c * t)⁻¹) ^ e)⁻¹ * ((w' * x ^ j)⁻¹ *
            ((c * t) * u * (c * t)⁻¹) * (w' * x ^ j)) := by rw [h1, hy]
      _ = (((c * t) * u * (c * t)⁻¹) ^ e)⁻¹ * ((x ^ j)⁻¹ *
            (w'⁻¹ * ((c * t) * u * (c * t)⁻¹) * w') * x ^ j) := by group
      _ = _ := by rw [hw'u]
  have h1 := hii _ (hx'V u hu) (by rw [key]; exact hx'V _ hu')
  have h2 := congrArg (fun g => u ^ e * g) h1
  simp only [mul_one, mul_inv_cancel_left] at h2
  exact h2

theorem ggL46Struct_of_core (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (hcore : GGL46Core p Bs x X U U₁) {g : G} (hgU : g ∈ U)
    (hcycU : U ≤ Subgroup.zpowers g ⊔ U₁) : GGL46Struct p Bs x X U U₁ := by
  obtain ⟨hab, hii, hΩ₁, hΩU⟩ := hcore
  refine ⟨hab, hii, ?_, hΩ₁, hΩU⟩
  obtain ⟨s, hs, hexp, hord, ⟨x', hx'x, hx'⟩, H, r, hHU₁, -, hHcard, hHB₁, hB₁card⟩ := hii
  have hcfg := hS.1.1
  have : Fact p.Prime := ⟨hcfg.1.2.2.2.2.2.1.1⟩
  have hp := (Fact.out : p.Prime)
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hBs.2 x hxBs
  obtain ⟨hUC, hUp, -, hBsU⟩ := hS.2.2.2.2.2.2.1
  have hU₁U : U₁ ≤ U := hS.2.2.2.2.2.2.2.1.2.1
  have hUN : U ≤ Subgroup.normalizer (U₁ : Set G) := fun u hu =>
    hS.2.2.2.2.2.2.2.2 ⟨Subgroup.le_normalizer hu,
      Subgroup.centralizer_le_normalizer _ (hUC hu)⟩
  have hx'zx : x' ∈ Subgroup.zpowers x := hx'x ▸ Subgroup.mem_zpowers x'
  have hx'U : x' ∈ U := Subgroup.zpowers_le.mpr (hBsU hxBs) hx'zx
  have hx'p : x' ^ p = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx'zx
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard := card_le_mul_card_ggPowSubgroup hp (by omega) hab hΩ₁ hHU₁ hHcard hHB₁ hB₁card
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hL43 : GGL43 Bs x X := hS.2.2.1
  have hBsB₁ : Nat.card Bs ≤ Nat.card B₁ * p := by
    have hxN : x ∈ Subgroup.normalizer (B₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
        mul_comm_of_isElemAbelian hBs hb.1 hxBs)
    have h := card_le_card_inf_mul_of_le_sup hxBs hxN
      (by rw [hL43.2, sup_comm]) hp.pos (by rw [hxp]; exact B₁.one_mem)
    rwa [inf_eq_right.mpr (inf_le_left : B₁ ≤ Bs)] at h
  have hB4 : p ^ 4 ≤ Nat.card Bs := by
    have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
      _ = Nat.card B := hBc.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  have hbig : p ^ 2 ≤ Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1))) := by
    have h1 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1))) := by
      have e1 : p ^ 2 * p ^ 2 = p ^ 4 := by ring
      have e2 : Nat.card Bs ≤ p * Nat.card (ggPowSubgroup U₁ hab (p ^ (s - 1))) * p :=
        hBsB₁.trans (Nat.mul_le_mul_right p hcard)
      nlinarith
    exact Nat.le_of_mul_le_mul_left h1 (pow_pos hp.pos 2)
  exact thompsonAbelianSubgroups_eq_of_cyclic hs hU₁U hUN hUp hab hexp hord hx'U hx'p hx' hgU
    hcycU hbig

end Core

@[expose] def GGL46CoreIOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → GGL46Core p Bs x X U U₁

@[expose] def GGL46IOneInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D → GGL46 p Bs x X U U₁

theorem ggL46CoreIOneInput_of_torus (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (h3 : GGNbrSubcomponentInput) (htorus : GGL45TorusIOneInput)
    (hcyc : GGL46CyclicIOneInput) : GGL46CoreIOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hI1
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨hab, s, hs, hexp, hord, x', hx'x, hact⟩ :=
    ggL46_torus_of_cent hraw hcen hiso hS (hcfg.cent_le_of_iOne h3 hI1)
      (htorus G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1)
  have habU : IsMulCommutative U₁ := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  obtain ⟨g₀, hg₀, hcycU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS hI1
  obtain ⟨hΩU, hΩ₁⟩ := ggL46_omega_of_cyclic hraw hiso hcfg hab hs hexp hx'x hact hg₀ hcycU
  have hcard := ggL46_card_le_of_cyclic hS habU hs hexp hx'x hact hΩU hΩ₁ hg₀ hcycU
  have hOU₁ : ggPowSubgroup U₁ habU (p ^ (s - 1)) ≤ U₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact U₁.pow_mem hu _
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp ((hcfg.isPGroup.to_le hcfg.part_le).to_le hOU₁)
  obtain ⟨H, hHU₁, hHcard, hHB₁⟩ := exists_ggHomocyclic hp (by omega) habU hexp hΩ₁ hr
  refine ⟨habU, ⟨s, hs, hexp, hord, ⟨x', hx'x, hact⟩, H, r, hHU₁, fun h hh => hexp h (hHU₁ hh),
    hHcard, hHB₁, ?_⟩, hΩ₁, hΩU⟩
  rw [hr] at hcard
  rw [pow_succ, mul_comm]
  exact hcard

theorem ggL46IOneInput_of_core (h43 : GGL43Input) (hcore : GGL46CoreIOneInput)
    (hcyc : GGL46CyclicIOneInput) : GGL46IOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS hI1
  obtain ⟨g, hgU, hcycU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS hI1
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    ggL46Struct_of_core hS (hcore G p B Bs x L D J X B₂ d y K U U₁ hS hI1) hgU hcycU
  exact ⟨h1, h2, h3, h4, h5, ggOpAutTrivial_of_omega h43 hS.1 hS.2.2.2.2.2.2.1 h5⟩

theorem ggL46IOneInput_of_tableB (hTB : GGTableBCxInput) (hNN : GGXNotNormalInput)
    (hTBM : GGTableBModuleInput) (hTBA : GGTableBActionInput) (hcore : GGL46CoreIOneInput)
    (hcyc : GGL46CyclicIOneInput) : GGL46IOneInput :=
  ggL46IOneInput_of_core
    (ggL43Input_of_inputs hTB hNN (ggL43ProdInput_of_hard hTBM (ggL43HardInput_of_tableB hTB hTBA)))
    hcore hcyc

end CFSG.StandardType

end
