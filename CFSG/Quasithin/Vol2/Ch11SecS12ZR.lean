module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZP
public import CFSG.Quasithin.Vol2.Ch11SecS12ZQ
public import CFSG.Quasithin.Vol2.Ch11SecS12ZN3
public import CFSG.Quasithin.Vol2.Ch11SecS12YJ
public import CFSG.Quasithin.Vol2.Ch11SecS12ZB
public import CFSG.Quasithin.Vol2.Ch11SecS12ZC
public import CFSG.Quasithin.Vol2.Ch11SecS12ZH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

theorem catalog_of_component {G : Type} [Group G] [Finite G] (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    {X₁ J : Subgroup G} (hX₁ : Nat.card ↥X₁ = 3)
    (hJ : CFSG.GorensteinWalter.IsComponentOf J (Subgroup.normalizer (X₁ : Set G))) :
    CFSG.Blueprint.Catalog (↥J ⧸ Subgroup.center ↥J) := by
  have hJtop : J ≠ ⊤ := by
    intro hJt
    have hle : (⊤ : Subgroup G) ≤ Subgroup.normalizer (X₁ : Set G) := hJt ▸ hJ.1
    have hXn : X₁.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
    rcases @Subgroup.Normal.eq_bot_or_eq_top G _ hsimp X₁ hXn with h | h
    · rw [h, Subgroup.card_bot] at hX₁
      omega
    · obtain ⟨a, b, hab⟩ := hnab
      have hG3 : Nat.card G = 3 := by rw [← hX₁, h, Subgroup.card_top]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hcyc : IsCyclic G := isCyclic_of_prime_card hG3
      exact hab ((IsCyclic.isMulCommutative (α := G)).is_comm.comm a b)
  have hsub : ((Subgroup.center ↥J).map J.subtype).subgroupOf J = Subgroup.center ↥J :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective J) _
  have key := @hK J ((Subgroup.center ↥J).map J.subtype) hJtop (Subgroup.map_subtype_le _)
  rw [hsub] at key
  exact key hJ.2.2.2.2 (cfsgQuasisimple_of_gw hJ.2.2).2.2

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

theorem obl11_1_2StarSL3AbCore_of (h4213 : TmpL6_4_2_13) (hNot4213 : SecB.FactNot4213)
    (h331 : Stmt3_3_1) (h128 : ASInputs.AS_A_1_28) (hAm : Obl11_1_2StarAmalgam)
    (hSh : Obl11_1_2StarShape) (hW : FactShapeWeyl) (hF : FactL34Parab) (hLevi : FactL34Levi)
    (hT : FactPGL34Torus) (hNo : FactL34NoE9) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hOrb : FactCompOrbit) (hSch : FactSchreierComp) (hJ4 : FactJ4Inspect)
    (hJ4M : FactJ4Multiplier) (hC : CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2) :
    Obl11_1_2StarSL3AbCore := by
  intro G _ _ T L I V₁ V₂ X K h hSL3 hEel hE16 ⟨y, hy, e, he, hye⟩ hU
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X₁ := SecA.xOne X (LOf L V₁) with hX₁def
  set H := Subgroup.normalizer (X₁ : Set G) with hHdef
  have hsimp := h.hyp.fsu.simple
  have hnab := h.hyp.fsu.nonabelian
  have hqtke := h.hyp.fsu.qtke
  have hc := (cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hX₁3 : Nat.card ↥X₁ = 3 := hc.cardX₁
  have hLperf : ⁅L, L⁆ = L := SecD.perfect_of_hyp11 h.hyp
  have hSL := isSL3_four_of h1102 h.hyp hSL3
  have hX₁p : IsPGroup 3 ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁3, pow_one])
  have hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L, l * b ∈ Subgroup.normalizer (X₁ : Set G) := by
    intro l hl
    obtain ⟨b, hb, hlb⟩ := exists_mul_mem_centralizer hX₁p
      (fun x hx => Subgroup.le_normalizer ((h.cartan.1 hx.1).1)) (fun x hx l hl =>
        SecA.C11P9B.commutator_mem_of_isSL3 hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL hx hl) hl
    exact ⟨b, hb, Subgroup.centralizer_le_normalizer _ hlb⟩
  have hL'perf : ⁅lXOne L X₁, lXOne L X₁⁆ = lXOne L X₁ := perfectCore_perfect _
  have hL'H : lXOne L X₁ ≤ H := (perfectCore_le _).trans inf_le_right
  obtain ⟨q, hq, l, hl, hql⟩ := exists_comm_lXOne hC hN hG2 hFb h1102 h hSL3 hU hy he hye
  have hO2 : pCoreOf 2 (lXOne L X₁) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at hq
    exact hql (by rw [hq]; group)
  have hUM := isUniqueM_lXOne h4213 hNot4213 h331 hC hN hG2 hFb h1102 h hSL3 hO2
  have hnle := not_normalizer_xOne_le hW hAm hSh hF hLevi hT hNo h37 h38 h39 hC hN hG2 hFb
    h1102 h hSL3
  have hO2H := pCoreOf_normalizer_eq_bot hUM hL'H hnle
  have hEH : conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (X₁ : Set G) ≤ H :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hcentp : ∀ p : ℕ, p.Prime → p ≠ 2 →
      lXOne L X₁ ≤ Subgroup.centralizer (pCoreOf p H : Set G) := by
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    exact lXOne_le_centralizer_pCoreOf hLperf hcov hSL hp2 hL'H
      (pRank_pCoreOf_le_two h128 hqtke hEel hE16 hEH hp hp2)
  have hFit := le_centralizer_fitting hL'H hO2H hcentp
  have hnorm : ∀ J, CFSG.GorensteinWalter.IsComponentOf J H →
      lXOne L X₁ ≤ Subgroup.normalizer (J : Set G) := fun J hJ =>
    le_normalizer_of_ncard_le hL'H (commutator_lXOne_eq_top L X₁)
      ((hOrb G hsimp hnab hqtke X₁ J hX₁3 hJ).trans (by norm_num))
  have hinn : ∀ J, CFSG.GorensteinWalter.IsComponentOf J H →
      ∀ ℓ ∈ lXOne L X₁, ∃ j ∈ J, j⁻¹ * ℓ ∈ Subgroup.centralizer (J : Set G) := fun J hJ =>
    hSch G hsimp hnab hqtke X₁ J _ hX₁3 hJ (catalog_of_component hsimp hnab hqtke.1 hX₁3 hJ)
      hL'perf hL'H (hnorm J hJ)
  have hLE := le_componentLayerOf hL'H hL'perf hFit hinn
  obtain ⟨F, _, _, -, π, hπ, hker⟩ := exists_pi_lXOne (X₁ := X₁) hLperf hcov hSL
  have hMN : Subgroup.normalizer (L : Set G) ⊓ H ≤ Subgroup.normalizer (lXOne L X₁ : Set G) := by
    rintro g ⟨hgL, hgX⟩
    refine normalizer_le_normalizer_perfectCore _ ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← Subgroup.mem_normalizer_iff.mp hgL x]
    refine and_congr_right fun _ => ⟨fun hx => H.mul_mem (H.mul_mem hgX hx) (H.inv_mem hgX),
      fun hx => ?_⟩
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ H := H.mul_mem (H.mul_mem (H.inv_mem hgX) hx) hgX
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rwa [e] at h1
  obtain ⟨K₀, hK₀, hLK₀⟩ := exists_component_le_of_uniqueM hUM hMN hL'perf
    (commutator_lXOne_eq_top L X₁) π hπ hker hLE hinn hq hl hql
  have hX₁L' : X₁ ≤ lXOne L X₁ := by
    refine xOne_le_lXOne hLperf hcov (fun x hx => (h.cartan.1 hx.1).1) fun x hx => ?_
    have := pow_card_eq_one' (G := ↥X₁) (x := ⟨x, hx⟩)
    rw [hX₁3] at this
    simpa using congrArg Subtype.val this
  have hQ : ⁅pCoreOf 2 (lXOne L X₁), lXOne L X₁⁆ ≠ ⊥ := by
    intro hb
    apply hql
    have : l * q * l⁻¹ * q⁻¹ ∈ ⁅lXOne L X₁, pCoreOf 2 (lXOne L X₁)⁆ :=
      Subgroup.commutator_mem_commutator hl hq
    rw [Subgroup.commutator_comm, hb, Subgroup.mem_bot] at this
    exact this
  obtain ⟨eJ⟩ := hJ4 G hsimp hnab hqtke X₁ K₀ (lXOne L X₁) hX₁3 hK₀ hX₁L' hLK₀ hL'perf
    (isSL3_lXOne hLperf hcov hSL) hQ
  have hZ := not_three_dvd_card_center_of_J4 hJ4M hK₀.2.2 eJ
  have hX₁K₀ : X₁ ≤ K₀ := hX₁L'.trans hLK₀
  obtain ⟨hnt, hperf, hsimple⟩ := hK₀.2.2
  have hquasi : CFSG.Open.IsQuasisimple ↥K₀ := ⟨hperf, hsimple⟩
  have hn : (X₁.subgroupOf K₀).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₁K₀).mpr hK₀.1
  have hcard : Nat.card ↥(X₁.subgroupOf K₀) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁K₀).toEquiv, hX₁3]
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi
    (X₁.subgroupOf K₀) with hcent | htop
  · apply hZ
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hcent
  ·
    have hK3 : Nat.card ↥K₀ = 3 := by
      rw [← hcard, htop, Subgroup.card_top]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcyc : IsCyclic ↥K₀ := isCyclic_of_prime_card hK3
    have hcomm : ∀ a b : ↥K₀, a * b = b * a := fun a b =>
      (IsCyclic.isMulCommutative (α := ↥K₀)).is_comm.comm a b
    have hbot : commutator ↥K₀ = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y _
      exact hcomm y x
    obtain ⟨a, b, hab⟩ := hnt
    have htopbot : (⊤ : Subgroup ↥K₀) = ⊥ := hperf.symm.trans hbot
    exact hab (Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top a) |>.trans
      (Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top b)).symm)

end CFSG.Quasithin.Vol2.Ch11.SecS
