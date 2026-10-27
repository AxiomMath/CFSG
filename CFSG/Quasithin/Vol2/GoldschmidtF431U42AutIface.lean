module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Main
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43ModelData
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Gen
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP2Gen
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Comp2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42LieData
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Plain
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Trans
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodes

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.U42 CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Pointwise

abbrev Ah : Type := ↥QA45.originalSubgroup

@[expose] def Yh : Subgroup Ah := QP45.originalSubgroup.subgroupOf QA45.originalSubgroup

@[expose] def P1h : Subgroup Ah := MulAction.stabilizer Ah (0 : Fin 45)

@[expose] def P2h : Subgroup Ah := MulAction.stabilizer Ah L0S

abbrev Bh : Subgroup Ah := P1h ⊓ P2h

abbrev AutAm : RankTwoAmalgam.{0} := RankTwoAmalgam.ofSubgroups P1h P2h

abbrev AutIso {G : Type} [Group G] (M₁ M₂ : Subgroup G) : Type :=
  AutAm.Iso (RankTwoAmalgam.ofSubgroups M₁ M₂)

@[expose] def AutIso.phi1 {G : Type} [Group G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) :
    ↥P1h ≃* ↥M₁ := iso.φ1

@[expose] def AutIso.phi2 {G : Type} [Group G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) :
    ↥P2h ≃* ↥M₂ := iso.φ2

@[expose] def AutIso.phiB {G : Type} [Group G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) :
    ↥Bh ≃* ↥(M₁ ⊓ M₂) := iso.φ12

@[expose] def AutIso.toG {G : Type} [Group G] {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂)
    (x : Bh) : G :=
  ((iso.phiB x : ↥(M₁ ⊓ M₂)) : G)

@[expose] def IsGoodInv (f : Ah) : Prop :=
  f ∈ Bh ∧ f ∉ Yh ∧ f ^ 2 = 1 ∧ Nat.card ↥(Subgroup.centralizer ({f} : Set Ah)) = 1440

structure AutCtx (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) where
  res : pResidual 2 G = ⊤
  iso : AutIso M₁ M₂
  o2 : pCoreOf 2 (M₁ ⊔ M₂) = ⊥
  z2 : z ^ 2 = 1
  z1 : z ≠ 1
  zc : z ∈ centerOf (M₁ ⊓ M₂)
  cz : Subgroup.centralizer ({z} : Set G) ≤ M₁
  N1 : Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁
  N2 : Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂

@[expose] def AutCtx.ofSimple {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}
    (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (iso : AutIso M₁ M₂)
    (o2 : pCoreOf 2 (M₁ ⊔ M₂) = ⊥) (z2 : z ^ 2 = 1) (z1 : z ≠ 1)
    (zc : z ∈ centerOf (M₁ ⊓ M₂)) (cz : Subgroup.centralizer ({z} : Set G) ≤ M₁)
    (N1 : Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁)
    (N2 : Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂) : AutCtx G M₁ M₂ z :=
  ⟨pResidual_two_eq_top hG hnab, iso, o2, z2, z1, zc, cz, N1, N2⟩

section Helpers

variable {G : Type} [Group G]

@[expose] def sOf (M₁ M₂ : Subgroup G) : Subgroup G := pCoreOf 2 (M₁ ⊓ M₂)

@[expose] def cenOf (f : G) : Subgroup G := Subgroup.centralizer ({f} : Set G)

@[expose] def aOf (Mi : Subgroup G) (f : G) : Subgroup G := pCoreOf 2 (Mi ⊓ cenOf f)

end Helpers

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

@[expose] def AutCtx.IsGoodAt (c : AutCtx G M₁ M₂ z) (f : G) : Prop :=
  ∃ f' : Bh, IsGoodInv (f' : Ah) ∧ c.iso.toG f' = f

@[expose] def U42AutModelGood : Prop := ∃ f : Ah, IsGoodInv f

@[expose] def U42AutNorm : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G) (z : G),
      IsU4ExtTwo 1 (RankTwoAmalgam.ofSubgroups M₁ M₂) →
      pCoreOf 2 (M₁ ⊔ M₂) = ⊥ → z ^ 2 = 1 → z ≠ 1 → z ∈ centerOf (M₁ ⊓ M₂) →
      Subgroup.centralizer ({z} : Set G) ≤ M₁ →
      Nonempty (AutIso M₁ M₂)

@[expose] def U42AutSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G), AutCtx G M₁ M₂ z →
    ∀ T : Subgroup G, IsSylowTwoOf T (M₁ ⊓ M₂) → IsSylowTwoOf T ⊤

@[expose] def U42AutFusion : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G), AutCtx G M₁ M₂ z →
    ∀ T : Subgroup G, IsSylowTwoOf T (M₁ ⊓ M₂) →
      ∀ u ∈ sOf M₁ M₂, u ^ 2 = 1 → u ≠ 1 →
        ∃ g u' : G, u' ∈ sOf M₁ M₂ ∧ u' ^ 2 = 1 ∧ g * u * g⁻¹ = u' ∧
          2 ^ 6 ≤ Nat.card ↥(T ⊓ cenOf u')

@[expose] def NotExtremalStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G), AutCtx G M₁ M₂ z →
    ∀ T : Subgroup G, IsSylowTwoOf T (M₁ ⊓ M₂) →
      ∀ f ∈ T, f ∉ sOf M₁ M₂ → f ^ 2 = 1 →
        ¬ IsSylowTwoOf (T ⊓ cenOf f) (cenOf f)

@[expose] def U42AutNotExtremal : Prop :=
  U42AutSylow → U42AutFusion → NotExtremalStmt

@[expose] def U42AutFusionZ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z) (f : G),
    c.IsGoodAt f → ¬ IsConj f z

@[expose] def Conf437 (z f : G) (T R : Subgroup G) : Prop :=
  Nat.card ↥R = 2 ^ 6 ∧ ¬ IsConj f z ∧ IsConj (f * z) z ∧
    (∃ t ∈ T, t ^ 2 = 1 ∧ Nat.card ↥(T ⊓ cenOf t) = 2 ^ 6 ∧ IsConj t f) ∧
    ∀ u : G, u ^ 2 = 1 → u ≠ 1 → IsConj u z ∨ IsConj u f

@[expose] def InvStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (T : Subgroup G), IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ f ∈ T, c.IsGoodAt f →
      ∀ R : Subgroup G, IsSylowTwoOf R (cenOf f) → T ⊓ cenOf f ≤ R → Conf437 z f T R

@[expose] def U42AutInv : Prop :=
  U42AutSylow → NotExtremalStmt → U42AutFusionZ → InvStmt

@[expose] def Conf54 (M₁ M₂ : Subgroup G) (f : G) (R : Subgroup G) : Prop :=
  Subgroup.centralizer (aOf M₁ f : Set G) = aOf M₁ f ∧
    Subgroup.centralizer (aOf M₂ f : Set G) = aOf M₂ f ∧
    Nat.card ↥(aOf M₁ f) = 16 ∧ Nat.card ↥(aOf M₂ f) = 16 ∧
    Nonempty (↥R ≃* DihedralGroup 4 × DihedralGroup 4) ∧
    Nat.card ↥(Subgroup.normalizer (aOf M₂ f : Set G)) = 576 ∧
    Nonempty (↥(Subgroup.normalizer (aOf M₂ f : Set G)) ⧸
      (aOf M₂ f).subgroupOf (Subgroup.normalizer (aOf M₂ f : Set G)) ≃*
        Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    Nonempty (↥(Subgroup.normalizer (aOf M₁ f : Set G)) ⧸
      (aOf M₁ f).subgroupOf (Subgroup.normalizer (aOf M₁ f : Set G)) ≃* Equiv.Perm (Fin 5))

@[expose] def U42AutF54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (T : Subgroup G), IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ f ∈ T, c.IsGoodAt f →
      ∀ R : Subgroup G, IsSylowTwoOf R (cenOf f) → T ⊓ cenOf f ≤ R → Conf437 z f T R →
        Conf54 M₁ M₂ f R

@[expose] def Conf55 (c : AutCtx G M₁ M₂ z) (f : G) : Prop :=
  Nat.card ↥(cenOf f) = 2880 ∧ Nat.card ↥((M₁ ⊔ M₂) ⊓ cenOf f) = 1440 ∧
    ∃ ι : Ah ≃* ↥(M₁ ⊔ M₂),
      (∀ x : P1h, (ι x : G) = (c.iso.phi1 x : G)) ∧ (∀ x : P2h, (ι x : G) = (c.iso.phi2 x : G))

@[expose] def U42AutF55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (T : Subgroup G), IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ f ∈ T, c.IsGoodAt f →
      ∀ R : Subgroup G, IsSylowTwoOf R (cenOf f) → T ⊓ cenOf f ≤ R → Conf437 z f T R →
        Conf54 M₁ M₂ f R → Conf55 c f

@[expose] def U42AutF56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (T : Subgroup G), IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ f ∈ T, c.IsGoodAt f →
      ∀ R : Subgroup G, IsSylowTwoOf R (cenOf f) → T ⊓ cenOf f ≤ R → Conf437 z f T R →
        Conf54 M₁ M₂ f R → Conf55 c f →
          (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (aOf M₂ f : Set G) = ⊤

@[expose] def U42AutIdent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M₁ M₂ : Subgroup G) (z : G) (c : AutCtx G M₁ M₂ z)
    (T : Subgroup G), IsSylowTwoOf T (M₁ ⊓ M₂) → ∀ f ∈ T, c.IsGoodAt f →
      ∀ R : Subgroup G, IsSylowTwoOf R (cenOf f) → T ⊓ cenOf f ≤ R → Conf437 z f T R →
        Conf54 M₁ M₂ f R → Conf55 c f →
          (M₁ ⊔ M₂) ⊔ Subgroup.normalizer (aOf M₂ f : Set G) = ⊤ → LieModel G .PSL 4 3 1

omit [Finite G] in
theorem AutIso.toG_mul {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) (x y : Bh) :
    iso.toG (x * y) = iso.toG x * iso.toG y := by
  simp only [AutIso.toG, map_mul, Subgroup.coe_mul]

omit [Finite G] in
theorem AutIso.toG_mem {M₁ M₂ : Subgroup G} (iso : AutIso M₁ M₂) (x : Bh) :
    iso.toG x ∈ M₁ ⊓ M₂ :=
  (iso.phiB x).2

theorem u42AutHalf_of_pieces (p0 : U42AutModelGood) (p1 : U42AutNorm) (p2 : U42AutSylow)
    (p3 : U42AutFusion) (p4 : U42AutNotExtremal) (p5 : U42AutFusionZ) (p6 : U42AutInv)
    (p7 : U42AutF54) (p8 : U42AutF55) (p9 : U42AutF56) (p10 : U42AutIdent) : U42AutHalf := by
  intro G _ _ hG hnab M₁ M₂ z hAm hO2 hz2 hz1 hzc hcz hN1 hN2
  obtain ⟨iso⟩ := p1 G hG hnab M₁ M₂ z hAm hO2 hz2 hz1 hzc hcz
  let c : AutCtx G M₁ M₂ z := AutCtx.ofSimple hG hnab iso hO2 hz2 hz1 hzc hcz hN1 hN2
  obtain ⟨f₀, hf₀⟩ := p0
  let f' : Bh := ⟨f₀, hf₀.1⟩
  set f : G := c.iso.toG f' with hf
  have hgood : c.IsGoodAt f := ⟨f', hf₀, rfl⟩
  have hf2 : f ^ 2 = 1 := by
    have h1 : f' * f' = 1 := Subtype.ext (by simpa [sq] using hf₀.2.2.1)
    have := congrArg c.iso.toG h1
    rw [AutIso.toG_mul] at this
    have h0 : c.iso.toG 1 = 1 := by simp only [AutIso.toG, map_one, Subgroup.coe_one]
    rw [h0] at this
    rw [sq]
    exact this
  have hfB : f ∈ M₁ ⊓ M₂ := c.iso.toG_mem f'
  have hfp : IsPGroup 2 ↥(Subgroup.zpowers f) := by
    have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one hf2
    have hdvd' : orderOf f ∣ 2 ^ 1 := by rw [pow_one]; exact hdvd
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  obtain ⟨T, hT, hfT⟩ := A4.exists_isSylowTwoOf_ge (Subgroup.zpowers_le.mpr hfB) hfp
  have hfT' : f ∈ T := hfT (Subgroup.mem_zpowers f)
  have hTp : IsPGroup 2 ↥(T ⊓ cenOf f) := hT.2.1.to_le inf_le_left
  obtain ⟨R, hR, hTR⟩ := A4.exists_isSylowTwoOf_ge (inf_le_right : T ⊓ cenOf f ≤ cenOf f) hTp
  have hconf := p6 p2 (p4 p2 p3) p5 G M₁ M₂ z c T hT f hfT' hgood R hR hTR
  have h54 := p7 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf
  have h55 := p8 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf h54
  have h56 := p9 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf h54 h55
  exact Or.inr (p10 G M₁ M₂ z c T hT f hfT' hgood R hR hTR hconf h54 h55 h56)

end CFSG.Quasithin.H13.F431.U42Aut
