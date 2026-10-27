module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelAbelianLift
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsT
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP10E6Real
public import CFSG.LocalAnalysis.StandardType.GGKGTwModelDiag
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneTableVec

public section

open Certificates

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6DD2
  CFSG.StandardType.E6ThreeModel

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem adAct_eq_smul (w : WeylGroup Tag.E6) (x : NTPlane.X3) :
    TableBExc.E6Three.adAct Tag.E6 3 w x = w • x := by
  funext i
  rw [TableBExc.E6Three.adAct]
  change (∑ j, (((w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j : ℤ) : ZMod 3) * x j) =
    ∑ j, x j * (((w⁻¹ • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) j : ℤ) : ZMod 3)
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

private theorem adRefl_eq_smul (i : Fin Tag.E6.rank) (x : NTPlane.X3) :
    TableBExc.E6Three.adRefl Tag.E6 3 i x = simple Tag.E6 i • x := by
  rw [← TableBExc.E6Three.adAct_simple (τ := Tag.E6) (p := 3) i x]
  exact adAct_eq_smul _ _

private theorem weyl_realized_top {G : Type} [Group G] {Bs L : Subgroup G}
    {u : G → NTPlane.X3}
    (hsimple : ∀ i : Fin Tag.E6.rank, ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = simple Tag.E6 i • u b)
    (w : WeylGroup Tag.E6) :
    ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b := by
  let S : Subgroup (WeylGroup Tag.E6) :=
    { carrier := {w | ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b}
      one_mem' := ⟨1, L.one_mem, Subgroup.one_mem _, by
        intro b _; rw [one_mul, inv_one, mul_one, one_smul]⟩
      mul_mem' := by
        rintro w₁ w₂ ⟨m₁, hm₁L, hm₁N, hm₁⟩ ⟨m₂, hm₂L, hm₂N, hm₂⟩
        refine ⟨m₁ * m₂, L.mul_mem hm₁L hm₂L, Subgroup.mul_mem _ hm₁N hm₂N,
          fun b hb => ?_⟩
        have hb' : m₂ * b * m₂⁻¹ ∈ Bs :=
          (Subgroup.mem_normalizer_iff.mp hm₂N b).mp hb
        have he : (m₁ * m₂) * b * (m₁ * m₂)⁻¹ = m₁ * (m₂ * b * m₂⁻¹) * m₁⁻¹ := by
          group
        rw [he, hm₁ _ hb', hm₂ b hb, mul_smul]
      inv_mem' := by
        rintro w ⟨m, hmL, hmN, hm⟩
        refine ⟨m⁻¹, L.inv_mem hmL, Subgroup.inv_mem _ hmN, fun b hb => ?_⟩
        have hb'm : m⁻¹ * b * (m⁻¹)⁻¹ ∈ Bs :=
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) b).mp hb
        have h := hm (m⁻¹ * b * (m⁻¹)⁻¹) hb'm
        have hmb : m * (m⁻¹ * b * (m⁻¹)⁻¹) * m⁻¹ = b := by group
        rw [hmb] at h
        show u (m⁻¹ * b * (m⁻¹)⁻¹) = w⁻¹ • u b
        rw [h, inv_smul_smul] }
  have htop : S = ⊤ := by
    refine le_antisymm le_top ?_
    rw [← (coxeterSystem Tag.E6).subgroup_closure_range_simple]
    refine (Subgroup.closure_le S).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hsimple i
  have hw : w ∈ S := by rw [htop]; exact Subgroup.mem_top w
  exact hw

private theorem twE6_A_facts {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs) :
    IsElemAbelian 3 (ggGamma L hN).range ∧ GGTorusSelfCent 3 (ggGamma L hN).range := by
  refine ⟨isElemAbelian_range (fun a b => ?_) (fun a => ?_) (ggGamma L hN),
    ggTorusSelfCent_ggGamma hN hBstar⟩
  · exact Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  · exact Subtype.ext (by simpa using hBs.2 (a : G) a.2)

private theorem rho_gamma_eq_diag {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {C : Type} [Group C]
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* C) (ρ : MulAut ↥L →* MulAut C)
    (hρ : ∀ (a : MulAut ↥L) (l : ↥L), ρ a (ggQuotHom θ l) = ggQuotHom θ (a l)) (b : Bs) :
    ρ (ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩) =
      ggLAut L θ ⟨((b : G))⁻¹, Subgroup.inv_mem _ (hN b.2)⟩ := by
  refine MulEquiv.ext fun r => ?_
  obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
  exact (hρ _ l).trans
    (ggBeta_ggQuotHom L hN θ ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩ l).symm

private theorem twE6_rho_gamma
    {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (ρ : MulAut ↥L →* MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hρ : ∀ (a : MulAut ↥L) (l : ↥L), ρ a (ggQuotHom θ l) = ggQuotHom θ (a l))
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hζ : ζ ^ 3 = 1) {u : G → NTPlane.X3}
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec (n := 1) le_rfl hK σ hσ Fr hFr g hζ D)
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩))
    (b : Bs) :
    ρ (ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩) = D.ad (u b) := by
  obtain ⟨hbR, hInd⟩ := hact b b.2
  have h1 := rho_gamma_eq_diag hN θ ρ hρ b
  have h2 : rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hbR⟩ =
      ggLAut L θ ⟨((b : G))⁻¹, Subgroup.inv_mem _ (hN b.2)⟩ :=
    eq_ggLAut_of_induces L θ (hN b.2) hInd
  obtain ⟨hx, hDx⟩ := hD.diag_eq (u b)
  have h3 : rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hx⟩ =
      rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hbR⟩ := by
    congr 1
  rw [h1, ← h2, ← h3, ← hDx]

private theorem conj_ggGamma_inv {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (w : ↥L) (b : Bs) {z : G} (hz : z ∈ Bs)
    (hz_eq : z = (w : G) * (b : G) * (w : G)⁻¹) :
    MulAut.conj w * ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩ *
        (MulAut.conj w)⁻¹ = ggGamma L hN ⟨z⁻¹, Bs.inv_mem hz⟩ := by
  ext l
  rw [show (MulAut.conj w)⁻¹ = MulAut.conj (w⁻¹ : ↥L) from
    (map_inv (MulAut.conj : ↥L →* MulAut ↥L) w).symm]
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv, ggGamma_coe]
  rw [hz_eq]
  group

private theorem twE6_normalizes {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {A : Subgroup (MulAut ↥L)} (hAeq : A = (ggGamma L hN).range)
    {T : Subgroup ↥L} {wl : Fin 6 → ↥L} (i : Fin 6)
    (hfix : ∀ a ∈ A, ∀ t ∈ T, a t = t)
    (hcob : ∀ i, ∀ a ∈ A,
      wl i * (a (wl i))⁻¹ ∈ T ∧ (wl i * (a (wl i))⁻¹) ^ 3 = 1) :
    ((wl i : ↥L) : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  let m : G := (wl i : ↥L)
  have hmem : ∀ b : Bs, m * (b : G) * m⁻¹ ∈ Bs := by
    intro b
    let a : A := ⟨ggGamma L hN b, by
      rw [hAeq]; exact MonoidHom.mem_range.mpr ⟨b, rfl⟩⟩
    let c : ↥L := wl i * ((a : MulAut ↥L) (wl i))⁻¹
    obtain ⟨hcT, hc3⟩ := hcob i (a : MulAut ↥L) a.2
    have hcG3 : ((c : ↥L) : G) ^ 3 = 1 := by
      simpa [c] using congrArg Subtype.val hc3
    have hcC : ((c : ↥L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have hmemA : ggGamma L hN ⟨((b' : G))⁻¹, Bs.inv_mem hb'⟩ ∈ A := by
        rw [hAeq]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
      have h1 : ((b' : G))⁻¹ * ((c : ↥L) : G) * b' = ((c : ↥L) : G) := by
        have := congrArg Subtype.val (hfix _ hmemA c hcT)
        rw [ggGamma_coe] at this
        simpa using this
      have h2 : ((c : ↥L) : G) * b' = b' * ((c : ↥L) : G) := by
        calc ((c : ↥L) : G) * b' =
            b' * ((b' : G)⁻¹ * ((c : ↥L) : G) * b') := by group
          _ = b' * ((c : ↥L) : G) := by rw [h1]
      exact h2.symm
    have hcBs : ((c : ↥L) : G) ∈ Bs := hBstar _ hcC hcG3
    have hc_eq : ((c : ↥L) : G) * (b : G) = m * (b : G) * m⁻¹ := by
      have h1 : ((ggGamma L hN b (wl i) : ↥L) : G) = (b : G) * m * (b : G)⁻¹ :=
        ggGamma_coe L hN b (wl i)
      dsimp only [c, a]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h1]
      dsimp only [m]
      group
    rw [← hc_eq]
    exact Bs.mul_mem hcBs b.2
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge ?_ ?_)
  · rintro _ ⟨b, hb, rfl⟩
    exact hmem ⟨b, hb⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective]

private theorem twE6_simple {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {u : G → NTPlane.X3}
    {A : Subgroup (MulAut ↥L)} (hAeq : A = (ggGamma L hN).range)
    {Φ : A →* Multiplicative NTPlane.X3} {wl : Fin 6 → ↥L}
    (hcoord : ∀ (b : Bs)
      (h : ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩ ∈ A),
      Multiplicative.toAdd (Φ ⟨ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩, h⟩) = u b)
    (hrefl : ∀ i (a : A), ∃ b : A,
      MulAut.conj (wl i) * (a : MulAut ↥L) * (MulAut.conj (wl i))⁻¹ = b ∧
      Multiplicative.toAdd (Φ b) = TableBExc.E6Three.adRefl Tag.E6 3 i
        (Multiplicative.toAdd (Φ a)))
    (i : Fin 6)
    (hnorm : ((wl i : ↥L) : G) ∈ Subgroup.normalizer (Bs : Set G)) :
    ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = simple Tag.E6 i • u b := by
  refine ⟨((wl i : ↥L) : G), (wl i).2, hnorm, fun b hb => ?_⟩
  have hbN : ((wl i : ↥L) : G) * (b : G) * (((wl i : ↥L) : G))⁻¹ ∈ Bs :=
    (Subgroup.mem_normalizer_iff.mp hnorm b).mp hb
  let a : A := ⟨ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem hb⟩, by
    rw [hAeq]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩
  obtain ⟨b', hb'conj, hb'coord⟩ := hrefl i a
  have hcoorda : Multiplicative.toAdd (Φ a) = u b := hcoord ⟨b, hb⟩ a.2
  have hb'eq : (b' : MulAut ↥L) = ggGamma L hN
      ⟨(((wl i : ↥L) : G) * (b : G) * (((wl i : ↥L) : G))⁻¹)⁻¹, Bs.inv_mem hbN⟩ := by
    rw [← hb'conj]
    exact conj_ggGamma_inv hN (wl i) ⟨b, hb⟩ hbN rfl
  have hb'coord' : Multiplicative.toAdd (Φ b') =
      u (⟨((wl i : ↥L) : G) * (b : G) * (((wl i : ↥L) : G))⁻¹, hbN⟩ : Bs) := by
    have hsub : b' = ⟨ggGamma L hN
        ⟨(((wl i : ↥L) : G) * (b : G) * (((wl i : ↥L) : G))⁻¹)⁻¹, Bs.inv_mem hbN⟩,
        by rw [hAeq]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩ := Subtype.ext hb'eq
    rw [hsub]
    exact hcoord ⟨_, hbN⟩ _
  calc u (((wl i : ↥L) : G) * b * (((wl i : ↥L) : G))⁻¹)
      = Multiplicative.toAdd (Φ b') := hb'coord'.symm
    _ = TableBExc.E6Three.adRefl Tag.E6 3 i (Multiplicative.toAdd (Φ a)) := hb'coord
    _ = TableBExc.E6Three.adRefl Tag.E6 3 i (u b) := by rw [hcoorda]
    _ = simple Tag.E6 i • u b := adRefl_eq_smul i (u b)

private theorem twE6_frame
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (h3 : 3 ∣ 2 ^ 1 + 1) {g : ModGL Tag.E6 (AlgebraicClosure K)} (hL : IsLang Fr g)
    {ζ : (AlgebraicClosure K)ˣ} (hζ : ζ ^ 3 = 1) (hζo : orderOf ζ = 3) :
    ∃ D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      TSpec (n := 1) le_rfl hK σ hσ Fr hFr g hζ D ∧ D.Good ∧
        CoverOdd ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := by
  obtain ⟨D, hD⟩ := exists_tFrame (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo
  have hgood : D.Good :=
    { center := tFrame_center (n := 1) le_rfl hK σ hσ
      faithful := tFrame_faithful (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      shape := tFrame_shape (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      torus := tFrame_torus (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      cent := tFrame_cent (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      inner := tFrame_inner (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      weyl := tFrame_weyl (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      modules := tFrame_modules (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      norm := tFrame_norm (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD
      aut := tFrame_aut (n := 1) le_rfl hK σ hσ Fr hFr h3 hL hζ hζo hD }
  exact ⟨D, hD, hgood, coverOdd_T (n := 1) le_rfl hK σ hσ h3⟩

private theorem twE6_diag_mem
    {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (ρ : MulAut ↥L →* MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hρ : ∀ (a : MulAut ↥L) (l : ↥L), ρ a (ggQuotHom θ l) = ggQuotHom θ (a l))
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hζ : ζ ^ 3 = 1) {u : G → NTPlane.X3}
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩))
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec (n := 1) le_rfl hK σ hσ Fr hFr g hζ D) :
    ∀ a ∈ (ggGamma L hN).range, ρ a ∈ D.diag.range := by
  rintro a ⟨c, rfl⟩
  have h := twE6_rho_gamma hN hK hσ hFr θ ρ hρ hζ hD hact
    (⟨(c : G)⁻¹, Bs.inv_mem c.2⟩ : Bs)
  refine ⟨Multiplicative.ofAdd (u (⟨(c : G)⁻¹, Bs.inv_mem c.2⟩ : Bs)), ?_⟩
  show D.ad (u (⟨(c : G)⁻¹, Bs.inv_mem c.2⟩ : Bs)) = ρ ((ggGamma L hN) c)
  simpa [inv_inv] using h.symm

private theorem twE6_model_data
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hperf : commutator ↥L = ⊤)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ}
    (hζ : ζ ^ 3 = 1) {u : G → NTPlane.X3}
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩))
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec (n := 1) le_rfl hK σ hσ Fr hFr g hζ D) (hgood : D.Good)
    (hcov : CoverOdd ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ∃ (A : Subgroup (MulAut ↥L)) (Φ : A →* Multiplicative NTPlane.X3)
      (T : Subgroup ↥L) (wl : Fin 6 → ↥L),
      A = (ggGamma L hN).range ∧
      (∀ (b : Bs) (h : ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩ ∈ A),
        Multiplicative.toAdd (Φ ⟨ggGamma L hN ⟨((b : G))⁻¹, Bs.inv_mem b.2⟩, h⟩) = u b) ∧
      Body (ggQuotHom θ).ker A Φ T wl := by
  let ρ : MulAut ↥L →* MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    BstarDesc.descAut (ggQuotHom_surjective θ) (ker_ggQuotHom θ)
  have hρ : ∀ a l, ρ a (ggQuotHom θ l) = ggQuotHom θ (a l) :=
    fun a l => BstarDesc.descAut_apply _ _ a l
  obtain ⟨hA, hsc⟩ := twE6_A_facts hBs hN hBstar
  have hal : ∀ a ∈ (ggGamma L hN).range, ρ a ∈ D.diag.range :=
    twE6_diag_mem hN hK σ hσ hFr θ ρ hρ hζ hact hD
  obtain ⟨Φ, hΦ, T, wl, hbody⟩ :=
    KGL.modelDiag_of_good_cover ggAbelianLift D hgood hcov (ggQuotHom_surjective θ)
      (le_of_eq (ker_ggQuotHom θ)) hperf hρ
      (BstarDesc.descAut_injective (ggQuotHom_surjective θ) (ker_ggQuotHom θ) hperf)
      hA hsc hal
  refine ⟨(ggGamma L hN).range, Φ, T, wl, rfl, ?_, hbody⟩
  intro b h
  exact congrArg Multiplicative.toAdd (hgood.faithful (by
    rw [hΦ]; exact twE6_rho_gamma hN hK hσ hFr θ ρ hρ hζ hD hact b))

theorem exists_weyl_of_twE6Coord
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hperf : commutator ↥L = ⊤)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    {g : ModGL Tag.E6 (AlgebraicClosure K)} {ζ : (AlgebraicClosure K)ˣ} {u : G → NTPlane.X3}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    (hζ : orderOf ζ = 3)
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩))
    (w : WeylGroup Tag.E6) :
    ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b := by
  have hζ3 : ζ ^ 3 = 1 := by simpa [hζ] using pow_orderOf_eq_one ζ
  have hL : IsLang Fr g := ⟨hg, hgn⟩
  have h3 : 3 ∣ 2 ^ 1 + 1 := by norm_num
  obtain ⟨D, hD, hgood, hcov⟩ := twE6_frame hK σ hσ hFr h3 hL hζ3 hζ
  obtain ⟨A, Φ, T, wl, hAeq, hcoord, hbody⟩ :=
    twE6_model_data hBs hN hBstar hperf hK σ hσ hFr θ hζ3 hact hD hgood hcov
  obtain ⟨-, -, -, -, hfix, -, hcob, hrefl, -, -, -, -⟩ := hbody
  refine weyl_realized_top (fun i => twE6_simple hN hAeq hcoord hrefl i
    (twE6_normalizes hN hBstar hAeq i hfix hcob)) w

end CFSG.StandardType.FrameRoute.TwE6Model

end
