module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5StdSub
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6Comp
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6CompD5
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6Coord
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6Plane
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6Weyl
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneHyperplane

public section

namespace CFSG.StandardType.FrameRoute.TwE6Model

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TwE6DD2

private abbrev TwE6Out {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
    (L : Subgroup G) (u : G → NTPlane.X3) : Prop :=
  ∃ (z : G) (J₁ : Subgroup G) (lab : LargeEvenLabel),
    P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
    J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
    LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = lab) ∧
    ((B = Bs ∧ lab = ⟨.twD, 5, 1⟩) ∨ (B ≠ Bs ∧ lab = ⟨.twA, 5, 1⟩)) ∧
    z ∈ Bs ∧ (∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') ∧
    (∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x) ∧ (∀ v, ∃ b ∈ Bs, u b = v) ∧
    ((NTPlane.kerRoots (u z)).ncard = 30 ∨ (NTPlane.kerRoots (u z)).ncard = 40) ∧
    ∀ w : WeylGroup Tag.E6, ∃ m ∈ L,
      m ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b

section CertsD5


private theorem d5_case {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcard : Nat.card Bs = 3 ^ 7) (hBeq : B = Bs)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : NTPlane.X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    {u : G → NTPlane.X3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v, ∃ b ∈ Bs, u b = v)
    (hWeyl : ∀ w : WeylGroup Tag.E6, ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b)
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩)) :
    TwE6Out B Bs x L u := by
  obtain ⟨hBge, hTLR, -⟩ := ggBstar_card_bounds hThm hBs (n := 6) (by simpa using hcard)
  have hm : LargeEvenTwoLocalRank 3 G < 2 * 4 + 1 := by omega
  have hB9 : 9 < Nat.card B := lt_of_lt_of_le (by norm_num : 9 < 3 ^ 6) hBge
  obtain ⟨z, hzBs, hzu⟩ := hsurj (NTPlane.reps 0)
  have hzB : z ∈ B := hBeq.symm ▸ hzBs
  have hznot : z ∉ Subgroup.zpowers x := fun hz => (by decide : NTPlane.reps 0 ≠ 0)
    (by rw [← hzu]; exact (hu0 z hzBs).mpr hz)
  have hv40 : (NTPlane.kerRoots (u z)).ncard = 40 := by
    rw [hzu, NTPlane.ncard_kerRoots_reps]; norm_num [NTPlane.repKerCard]
  let φ : NTPlane.X3 → MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    fun w => rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩
  obtain ⟨J, hJq, hJfix, hJnorm, hJsolv, hJbig, hJmark, hJdet, hJcov⟩ :=
    exists_twE6Component_D5 hK σ hσ Fr hFr hg hgn hζ hR hv40
  have hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) (φ (u z)) :=
    (hact z hzBs).elim fun _ hbz => by simpa [φ] using hbz
  have hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (φ (u b)) :=
    fun b hb => (hact b hb).elim fun _ hbact => by simpa [φ] using hbact
  obtain ⟨J₁, hP5, hlay, hmark⟩ :=
    p5Out_of_twE6Component (θ := θ) (u := u) (φ := φ) (J := J) hThm hBs hN hker hadd hu0
      hzB hznot hB9 (by norm_num : 1 ≤ 4) hJq hJfix hJnorm (hJsolv hJnorm) hJbig hJmark
      hJdet hJcov hm hφ hψ
  exact ⟨z, J₁, (⟨.twD, 5, 1⟩ : LargeEvenLabel), hP5, hlay, hmark, Or.inl ⟨hBeq, rfl⟩,
    hBs.1 hzB, hadd, hu0, hsurj, Or.inr hv40, hWeyl⟩

end CertsD5

section CertsA5


private theorem a5_case {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcard : Nat.card Bs = 3 ^ 7) (hBne : B ≠ Bs)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    (hR : ∀ w : NTPlane.X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    {u : G → NTPlane.X3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v, ∃ b ∈ Bs, u b = v)
    (hWeyl : ∀ w : WeylGroup Tag.E6, ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b)
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩)) :
    TwE6Out B Bs x L u := by
  obtain ⟨hBge, hTLR, hTLRne⟩ :=
    ggBstar_card_bounds hThm hBs (n := 6) (by simpa using hcard)
  have hm : LargeEvenTwoLocalRank 3 G < 2 * 3 + 1 := by have := hTLRne hBne; omega
  have hB9 : 9 < Nat.card B := lt_of_lt_of_le (by norm_num : 9 < 3 ^ 6) hBge
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨z, hzB, hz30, hznot⟩ :=
    exists_point_typeA5 hBs.1 hS.2.1 hS.2.2.1 (hS.1.1.2 x hS.2.1) hadd hu0 hBge
  have hzBs : z ∈ Bs := hBs.1 hzB
  let φ : NTPlane.X3 → MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    fun w => rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hR w⟩
  obtain ⟨J, hJq, hJfix, hJnorm, hJsolv, hJbig, hJmark, hJdet, hJcov⟩ :=
    exists_twE6Component_A5 hK σ hσ Fr hFr hg hgn hζ hR hz30
  have hφ : LargeEvenInduces θ (fun l l' => (l' : G) = z⁻¹ * l * z) (φ (u z)) :=
    (hact z hzBs).elim fun _ hbz => by simpa [φ] using hbz
  have hψ : ∀ b ∈ Bs, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) (φ (u b)) :=
    fun b hb => (hact b hb).elim fun _ hbact => by simpa [φ] using hbact
  obtain ⟨J₁, hP5, hlay, hmark⟩ :=
    p5Out_of_twE6Component (θ := θ) (u := u) (φ := φ) (J := J)
      hThm hBs hN hker hadd hu0 hzB hznot hB9 (by norm_num : 1 ≤ 3)
      hJq hJfix hJnorm (hJsolv hJnorm) hJbig hJmark hJdet hJcov hm hφ hψ
  exact ⟨z, J₁, (⟨.twA, 5, 1⟩ : LargeEvenLabel), hP5, hlay, hmark, Or.inr ⟨hBne, rfl⟩,
    hzBs, hadd, hu0, hsurj, Or.inl hz30, hWeyl⟩

end CertsA5

section CertsAll


private theorem twE6Out_of_coord {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcard : Nat.card Bs = 3 ^ 7) (hperf : commutator ↥L = ⊤)
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K} (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hσ : ∀ c, σ c = c ^ 2 ^ 1) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ 2 ^ 1) {g : ModGL Tag.E6 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E6 (AlgebraicClosure K))
    (hgn : g⁻¹ * twistE6 (AlgebraicClosure K) Fr g = TwistedDiag.n0 (AlgebraicClosure K))
    {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3)
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    {u : G → NTPlane.X3}
    (hadd : ∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b')
    (hu0 : ∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x)
    (hsurj : ∀ v, ∃ b ∈ Bs, u b = v)
    (hact : ∀ b ∈ Bs, ∃ hb : g * rootDiagUnit Tag.E6 (fun i => ζ ^ (u b i).val) * g⁻¹ ∈
        TwistedDiag.Rgrp (AlgebraicClosure K) Fr,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
        (rgrpConjAut le_rfl hK σ hσ Fr hFr ⟨_, hb⟩)) :
    TwE6Out B Bs x L u := by
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hR : ∀ w : NTPlane.X3, g * rootDiagUnit Tag.E6 (fun i => ζ ^ (w i).val) * g⁻¹ ∈
      TwistedDiag.Rgrp (AlgebraicClosure K) Fr := fun w =>
    conj_rootDiagUnit_zeta_mem_Rgrp hFr (by norm_num) hg hgn hζ3 w
  have hWeyl : ∀ w : WeylGroup Tag.E6, ∃ m ∈ L, m ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b := fun w =>
    exists_weyl_of_twE6Coord hBs.2.1 hN hBs.2.2.2 hperf hK hσ hFr θ hg hgn hζ hact w
  rcases eq_or_ne B Bs with hBeq | hne
  · exact d5_case hThm hBs hN hker hcard hBeq hK hσ hFr hg hgn hζ hR (θ := θ) (u := u)
      hadd hu0 hsurj hWeyl hact
  · exact a5_case hThm hBs hN hker hcard hne hK hσ hFr hg hgn hζ hR (θ := θ) (u := u)
      hadd hu0 hsurj hWeyl hact

end CertsAll

theorem exists_p5Out_of_twE6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hcard : Nat.card Bs = 3 ^ 7)
    (hL : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs L) :
    ∃ (z : G) (J₁ : Subgroup G) (lab : LargeEvenLabel) (u : G → NTPlane.X3),
      P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = lab) ∧
      ((B = Bs ∧ lab = ⟨.twD, 5, 1⟩) ∨ (B ≠ Bs ∧ lab = ⟨.twA, 5, 1⟩)) ∧
      z ∈ Bs ∧ (∀ b ∈ Bs, ∀ b' ∈ Bs, u (b * b') = u b + u b') ∧
      (∀ b ∈ Bs, u b = 0 ↔ b ∈ Subgroup.zpowers x) ∧ (∀ v, ∃ b ∈ Bs, u b = v) ∧
      ((NTPlane.kerRoots (u z)).ncard = 30 ∨ (NTPlane.kerRoots (u z)).ncard = 40) ∧
      ∀ w : WeylGroup Tag.E6, ∃ m ∈ L,
        m ∈ Subgroup.normalizer (Bs : Set G) ∧ ∀ b ∈ Bs, u (m * b * m⁻¹) = w • u b := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨-, hperf, K, instK, instFinK, σ, hK, hσ, Fr, hFr, θ, g, ζ, u, hg, hgn, hζ, hact,
    hadd, hu0, hsurj⟩ :=
    exists_twE6Coord (n := 7) hBs.2.1 hcard le_rfl (hBs.1 hS.2.1) hS.2.2.1 hN hker
      hBs.2.2.2 hL
  have hout := twE6Out_of_coord hThm hBs hN hker hcard hperf hK hσ hFr hg hgn hζ
    (θ := θ) (u := u) hadd hu0 hsurj hact
  obtain ⟨z, J₁, lab, hbody⟩ := hout
  exact ⟨z, J₁, lab, u, hbody⟩

end CFSG.StandardType.FrameRoute.TwE6Model

end
