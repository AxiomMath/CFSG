module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCentJLieStar
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagNbr
public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualSplit
public import CFSG.LocalAnalysis.StandardType.GGSixCtxKnownSupply

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def GGSixTCConfig
    (t : StatedLieTag) {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (n f : ℕ) (ψ : (ggU t n f).K →* G) : Prop :=
  GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ ∧
    Subgroup.centralizer (D : Set G) ≤ ggM p B x L D J ∧
    Odd (Nat.card (Subgroup.centralizer (ggG0 p B x L D J : Set G))) ∧
    (∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) ∧
    (∀ d ∈ D, d ≠ 1 → Odd (Nat.card (Subgroup.center ↥(ggKd p B x L D J d)))) ∧
    ¬ GGSixLSevenA3Case J ∧ ¬ GGSixLSevenE6Case p L J t f ∧ GGSixLSevenFieldExtCase J t f

structure GGSixTCPos
    (t : StatedLieTag) {X : Type} [Group X] [Finite X] (n f : ℕ)
    (ψ : (ggU t n f).K →* X) (p : ℕ) (G₀ B₁ D J L : Subgroup X) (x : X) : Prop where
  range_eq : ψ.range = G₀
  ker_le : ψ.ker ≤ Subgroup.center (ggU t n f).K
  model : LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) t n 2 f
  odd_C : Odd (Nat.card (Subgroup.centralizer (G₀ : Set X)))
  prime : p.Prime
  ne_two : p ≠ 2
  le_N_G0 : B₁ ≤ Subgroup.normalizer (G₀ : Set X)
  innerDiag : ∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b
  elemAbelian : IsElemAbelian p B₁
  four_le : p ^ 4 ≤ Nat.card B₁
  D_le : D ≤ B₁
  card_D : Nat.card D = p ^ 2
  B_le_N_J : B₁ ≤ Subgroup.normalizer (J : Set X)
  B_inf_C_J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D
  J_comp : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X))
  odd_Z_J : Odd (Nat.card (Subgroup.center ↥J))
  x_mem : x ∈ D
  x_ne_one : x ≠ 1
  L_le : L ≤ G₀
  L_comp : IsComponentOf L (G₀ ⊓ Subgroup.centralizer {x})
  J_le_L : J ≤ L
  not_D_le_C_L : ¬ D ≤ Subgroup.centralizer (L : Set X)
  L_split : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab)
  B_le_N_L : B₁ ≤ Subgroup.normalizer (L : Set X)
  L_innerDiag : LargeEvenMarking ↥L (fun _ _ _ I _ θ => ∀ b ∈ B₁, ∃ φ ∈ I,
    LargeEvenInduces θ (fun l l' => (l' : X) = b⁻¹ * l * b) φ)
  not_A3 : ¬ GGSixLSevenA3Case J
  not_E6 : ¬ GGSixLSevenE6Case p L J t f
  fieldExt : GGSixLSevenFieldExtCase J t f
  B_inf_C_L : B₁ ⊓ Subgroup.centralizer (L : Set X) = Subgroup.zpowers x
  B_inf_C_G0 : B₁ ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥
  rank_B : p ^ LargeEvenTwoLocalRank p ↥(B₁ ⊔ G₀) ≤ Nat.card B₁
  nbr : ∀ d ∈ D, d ∉ Subgroup.zpowers x → ∀ K : Subgroup X,
    IsComponentOf K (G₀ ⊓ Subgroup.centralizer {d}) → J ≤ K → K ≠ J →
      B₁ ≤ Subgroup.normalizer (K : Set X) ∧ GGNbrClauseFiveMarking p x K

@[expose] def GGSixTCKnownAt
    (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ) (ψ : (ggU t n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X),
    GGSixTCPos t n f ψ p G₀ B₁ D J L x → t = .PSL ∧ Nat.Coprime n (2 ^ f - 1)

theorem ggSixTC_eq_of_centralizes
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d}))
    {d : G} (hd : d ∈ D) (hd1 : d ≠ 1)
    (hDK : D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G)) :
    ggKd p B x L D J d = J := by
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hctx.j_comp.2.2
  have hKd := hcomp d hd hd1
  have hKG0 : ggKd p B x L D J d ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer {d} :=
    le_inf (hctx.ggKd_le_ggG0 hd) (hctx.ggKd_le_centralizer hd)
  have hKc : IsComponentOf (ggKd p B x L D J d) (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKd hKG0 inf_le_right
  have hKD : ggKd p B x L D J d ≤ ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G) :=
    le_inf (hctx.ggKd_le_ggG0 hd) (Subgroup.le_centralizer_iff.mp hDK)
  have hDd : ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G) ≤
      ggG0 p B x L D J ⊓ Subgroup.centralizer {d} :=
    inf_le_inf_left _ (Subgroup.centralizer_le (by simpa using hd))
  have hKc' : IsComponentOf (ggKd p B x L D J d)
      (ggG0 p B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hKc hKD hDd
  exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_of_le hJq hKc'
    hctx.j_isComponentOf_inf (le_ggKd p B x L D J d) le_rfl

theorem ggSixTC_nbr
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hP : GGStdSubPrimeInput)
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (hcomp : ∀ d ∈ D, d ≠ 1 → IsComponentOf (ggKd p B x L D J d) (Subgroup.centralizer {d})) :
    ∀ d ∈ D, d ∉ Subgroup.zpowers x → ∀ K : Subgroup G,
      IsComponentOf K (ggG0 p B x L D J ⊓ Subgroup.centralizer {d}) → J ≤ K → K ≠ J →
        B ≤ Subgroup.normalizer (K : Set G) ∧ GGNbrClauseFiveMarking p x K := by
  intro d hd hdx K hK hJK hKJ
  have hd1 : d ≠ 1 := fun h => hdx (h ▸ Subgroup.one_mem _)
  have hKeq : ggKd p B x L D J d = K :=
    ggKd_eq_of_le_component hK hctx.j_comp.2.2 hJK
  have hDK : ¬ D ≤ Subgroup.centralizer (ggKd p B x L D J d : Set G) := fun h =>
    hKJ (hKeq ▸ ggSixTC_eq_of_centralizes hctx hcomp hd hd1 h)
  have hnbr := ggSixKdNbrInput_of_prime hP G p B Bs x L D J t n f ψ hctx hcomp d hd hdx hDK
  have h5 := hctx.stdType.2.2.1 d (ggKd p B x L D J d)
    (isNeighborOf_of_ggNbr hctx.stdSub hnbr)
  rw [hKeq] at h5
  exact h5

theorem ggSixTC_rank_B
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) :
    p ^ LargeEvenTwoLocalRank p ↥(B ⊔ ggG0 p B x L D J) ≤ Nat.card B := by
  have hp : p.Prime := hctx.prime
  calc p ^ LargeEvenTwoLocalRank p ↥(B ⊔ ggG0 p B x L D J)
      ≤ p ^ LargeEvenTwoLocalRank p G :=
        Nat.pow_le_pow_right hp.pos
          (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp _)
    _ = Nat.card B := hctx.sstar.1.2.1.symm

theorem GGSixTCConfig.toPos
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hnc : GGLNoncyclicInput) (h64 : GGSixCentreOddInput)
    (hP : GGStdSubPrimeInput) (h : GGSixTCConfig t p B Bs x L D J n f ψ) :
    GGSixTCPos t n f ψ p (ggG0 p B x L D J) B D J L x := by
  obtain ⟨hctx, hC2, hodd, hcomp, hZ, hA, hE, hF⟩ := h
  obtain ⟨-, -, ⟨hadm, hrk⟩, ⟨hrange, hker⟩, ⟨hperf0, hmodel⟩, ⟨hBsN, hVI⟩, -, -⟩ := hctx.2
  have hBBs : B ≤ Bs := hctx.bstar.1
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hctx.sstar.2.2.2.1
  have hLc : IsComponentOf L (ggG0 p B x L D J ⊓ Subgroup.centralizer {x}) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL
      (le_inf le_sup_left hL.1) inf_le_right
  have hmkL : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hctx.stdType.1
  have hHL := ggSixCtx_normalizer_and_innerDiag_on_L hctx
  exact
    { range_eq := hrange
      ker_le := hker
      model := hmodel
      odd_C := hodd
      prime := hctx.prime
      ne_two := hctx.ne_two
      le_N_G0 := hBBs.trans hBsN
      innerDiag := fun b hb => hVI b (hBBs hb)
      elemAbelian := hctx.sstar.1.1
      four_le := hctx.pow_four_le_card_b
      D_le := hctx.stdSub.1.1
      card_D := hctx.card_d
      B_le_N_J := hBBs.trans (hctx.bstar_le_normalizer_j hnc)
      B_inf_C_J := hctx.stdSub.1.2.2.2.2.2.2.symm
      J_comp := hctx.j_isComponentOf_inf
      odd_Z_J := (h64 G p B Bs x L D J t n f ψ hctx hodd).1
      x_mem := hctx.x_mem_d
      x_ne_one := hctx.sstar.2.2.1
      L_le := le_sup_left
      L_comp := hLc
      J_le_L := hctx.j_le_inf.trans inf_le_left
      not_D_le_C_L := hctx.not_le_centralizer_L
      L_split := hmkL
      B_le_N_L := hHL.1
      L_innerDiag := hHL.2
      not_A3 := hA
      not_E6 := hE
      fieldExt := hF
      B_inf_C_L := inf_centralizer_eq_zpowers_of_sstar hctx.prime hctx.sstar
      B_inf_C_G0 := eq_bot_iff.mpr ((inf_le_inf_right _ hctx.bstar.1).trans
        (bstar_inf_centralizer_ggG0_eq_bot hctx.config).le)
      rank_B := ggSixTC_rank_B hctx
      nbr := ggSixTC_nbr hP hctx hcomp }

theorem ggSixFieldExtTableCAt_of_known
    (hnc : GGLNoncyclicInput) (h64 : GGSixCentreOddInput)
    (hP : GGStdSubPrimeInput) {t : StatedLieTag} (hK : GGSixTCKnownAt t) :
    GGSixFieldExtTableCAt t := by
  intro G _ _ p B Bs x L D J n f ψ hctx hC2 hodd hcomp hZ hA hE hF
  exact hK G n f ψ p (ggG0 p B x L D J) B D J L x
    (GGSixTCConfig.toPos hnc h64 hP ⟨hctx, hC2, hodd, hcomp, hZ, hA, hE, hF⟩)

end CFSG.StandardType

end
