module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeEnvelopePieces
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassical
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCNoSU3Alg
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCNoSU3Tor

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore CFSG.RankThree.PartOne.KE
open CFSG.Open (StatedLieTag)

theorem rckSU3_centralizes_of_partner {X Y : Type} [Group X] [Group Y] (G₀ K : Subgroup X)
    (hKG : K ≤ G₀) [Group.IsPerfect ↥K] (η : ↥G₀ →* Y) (Kb : Subgroup Y)
    (hK : (K.subgroupOf G₀).map η = Kb) (hker : η.ker = Subgroup.center ↥G₀) {b : X}
    (hbN : b ∈ Subgroup.normalizer (K : Set X)) {z : Y} (hbz : GGLiePartner G₀ η b z)
    (hz : ∀ x ∈ Kb, z * x * z⁻¹ = x) : ∀ x ∈ K, b * x * b⁻¹ = x := by
  obtain ⟨ηK, -, hηKv, hηKk⟩ := rckNC_etaK G₀ K hKG η Kb hK hker
  have hmain : ∀ x : ↥K, b * (x : X) * b⁻¹ = (x : X) := by
    apply rck_conj_commutes_of_central K b hbN
    intro x hx
    have hηx : ηK (⟨b * (x : X) * b⁻¹, hx⟩ : ↥K) = ηK x := by
      apply Subtype.ext
      rw [hηKv, hηKv]
      rw [hbz ⟨(x : X), hKG x.2⟩ (hKG hx)]
      exact hz _ (by
        rw [← hK]
        exact ⟨⟨(x : X), hKG x.2⟩, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩)
    have hker1 : (⟨b * (x : X) * b⁻¹, hx⟩ : ↥K) * x⁻¹ ∈ ηK.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hηx]
      exact mul_inv_cancel _
    exact hηKk hker1
  intro x hx
  exact hmain ⟨x, hx⟩

theorem rckNC_two_lt_compRank
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* X}
    {p : ℕ} {G₀ A B₁ D J L R Rm K : Subgroup X} {e : X} (ht : GGExcFive t)
    (hcfg : RCKRPConfig t n f ψ p G₀ A B₁ D J L R Rm K e) (hKJ : K ≠ J)
    {θ : ↥G₀ →* ModGL (langTag t) GGL} {A' : Subgroup (ModGL (langTag t) GGL)}
    {η : ↥G₀ →* ModGL (langTag t) GGL} {E' : Subgroup (ModGL (langTag t) GGL)}
    {S : LangSetup (langTag t) GGL 5} {a : Fin (langTag t).rank → GGLˣ}
    {i : KernelComponent (rootCharHom a)}
    (hfp : RCKFirstPassAt t f p G₀ A B₁ D J K e θ A' η E' S a i) :
    2 < compRank (componentRoots (rootCharHom a) i) := by
  by_contra hlt
  have hrk : compRank (componentRoots (rootCharHom a) i) ≤ 2 := not_lt.1 hlt
  obtain ⟨hbr, htoral, hKG, hker, hrange, hq, hΦ, hη, hE', hEt, hEel, hfwd, hrE, hr1, hap, hpe,
    hK, hqs, hKqs, hoddK, hB1N, d, hdD, hdne, hJcomp⟩ := hfp
  have hcfg' := hcfg
  unfold RCKRPConfig at hcfg'
  obtain ⟨-, -, hp, hp2, -, hB1A, hDB1, hDcard, hAN, -, -, hB1J, hB1card, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hcfg'
  haveI hKperf : Group.IsPerfect ↥K := ⟨hKqs.1⟩
  have hp0 : 0 < p := hp.pos
  have hJK : J ≤ K := hJcomp.1.trans inf_le_left
  obtain ⟨β, hβ⟩ := rckSU3_exists_span_basis (componentRoots (rootCharHom a) i) hrk
  choose pa hpaE hpaP using fun b : ↥B₁ => hfwd (b : X) (hB1A b.2)
  have hpaT : ∀ b : ↥B₁, pa b ∈ torusGroup (langTag t) GGL := fun b =>
    (mem_twistedTorusOf.1 (hEt (hpaE b))).1
  have hpap : ∀ b : ↥B₁, pa b ^ p = 1 := fun b => hEel.2 (pa b) (hpaE b)
  obtain ⟨hVfin, hVcard⟩ := rckSU3_pow_eq_one (F := GGL) hp0
  haveI : Finite {u : GGLˣ // u ^ p = 1} := hVfin
  let F : ↥B₁ → (Fin 2 → {u : GGLˣ // u ^ p = 1}) := fun b j =>
    ⟨rckRootVal (pa b) (β j), rckSU3_rootVal_pow (hpaT b) (hpap b) (β j)⟩
  have hF : ∀ b b' : ↥B₁, F b = F b' →
      ((b⁻¹ * b' : ↥B₁) : X) ∈ B₁ ⊓ Subgroup.centralizer (K : Set X) := by
    intro b b' hbb
    refine Subgroup.mem_inf.2 ⟨(b⁻¹ * b').2, ?_⟩
    have hbN : ((b⁻¹ * b' : ↥B₁) : X) ∈ Subgroup.normalizer (K : Set X) := hB1N (b⁻¹ * b').2
    have hbG : (b : X) ∈ Subgroup.normalizer (G₀ : Set X) := hAN (hB1A b.2)
    have hbG' : (b' : X) ∈ Subgroup.normalizer (G₀ : Set X) := hAN (hB1A b'.2)
    have hbz : GGLiePartner G₀ η (((b⁻¹ * b' : ↥B₁)) : X) ((pa b)⁻¹ * pa b') :=
      GGLiePartner.mul (inv_mem hbG) hbG' (GGLiePartner.inv hbG (hpaP b)) (hpaP b')
    have hzE : (pa b)⁻¹ * pa b' ∈ E' := E'.mul_mem (E'.inv_mem (hpaE b)) (hpaE b')
    have hzT : (pa b)⁻¹ * pa b' ∈ S.D.torus := hEt hzE
    have hβz : ∀ j, rckRootVal ((pa b)⁻¹ * pa b') (β j) = 1 := by
      intro j
      have h2 : rckRootVal (pa b) (β j) = rckRootVal (pa b') (β j) :=
        congrArg Subtype.val (congrFun hbb j)
      rw [rckSU3_rootVal_inv_mul (hpaT b) (hpaT b') (β j), h2]
      exact inv_mul_cancel _
    have h1 : ∀ γ ∈ componentRoots (rootCharHom a) i,
        rckRootVal ((pa b)⁻¹ * pa b') γ = 1 :=
      rckSU3_char_trivial_of_span hβ (rootCharHom (rckTorusCoord ((pa b)⁻¹ * pa b'))) hβz
    have hzc : ∀ x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i,
        (pa b)⁻¹ * pa b' * x * ((pa b)⁻¹ * pa b')⁻¹ = x := fun x hx =>
      rckSU3_centralizes_rationalComponent S a i hzT h1 hx
    have hcent := rckSU3_centralizes_of_partner G₀ K hKG η _ hK hker hbN hbz hzc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h3 := hcent x hx
    calc x * ((b⁻¹ * b' : ↥B₁) : X) = (((b⁻¹ * b' : ↥B₁) : X) * x * ((b⁻¹ * b' : ↥B₁) : X)⁻¹) *
          ((b⁻¹ * b' : ↥B₁) : X) := by rw [h3]
      _ = ((b⁻¹ * b' : ↥B₁) : X) * x := by group
  have hcount := rckSU3_card_le_mul B₁ (B₁ ⊓ Subgroup.centralizer (K : Set X)) inf_le_left F hF
  have hS : Nat.card (Fin 2 → {u : GGLˣ // u ^ p = 1}) ≤ p ^ 2 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
    exact Nat.pow_le_pow_left hVcard 2
  have hHD : B₁ ⊓ Subgroup.centralizer (K : Set X) ≤ D := by
    intro x hx
    rw [← hB1J]
    exact ⟨hx.1, Subgroup.centralizer_le (show (J : Set X) ⊆ K from hJK) hx.2⟩
  have hHge : Nat.card ↥D ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) := by
    rw [hDcard]
    have h1 : p ^ 2 * p ^ 2 ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) * p ^ 2 :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card ↥B₁ := hB1card
        _ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) *
              Nat.card (Fin 2 → {u : GGLˣ // u ^ p = 1}) := hcount
        _ ≤ Nat.card ↥(B₁ ⊓ Subgroup.centralizer (K : Set X)) * p ^ 2 :=
          Nat.mul_le_mul_left _ hS
    exact Nat.le_of_mul_le_mul_right h1 (pow_pos hp0 2)
  have hHeq : B₁ ⊓ Subgroup.centralizer (K : Set X) = D :=
    Subgroup.eq_of_le_of_card_ge hHD hHge
  have hdH : d ∈ B₁ ⊓ Subgroup.centralizer (K : Set X) := by rw [hHeq]; exact hdD
  have hcent : ∀ x ∈ K, d * x * d⁻¹ = x := by
    intro x hx
    have h1 := (Subgroup.mem_centralizer_iff.1 hdH.2) x hx
    calc d * x * d⁻¹ = x * d * d⁻¹ := by rw [← h1]
      _ = x := by group
  exact hKJ (rckNC_comp_eq_of_centralizes K J d hKqs hJcomp hcent).symm

theorem rckNoSmallSU3_holds :
    RCKNoSmallSU3 := by
  intro X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp hsmall
  exact (rckNC_two_lt_compRank ht hcfg hKJ hfp).ne' hsmall.2

end CFSG.StandardType.RCKRP

end
