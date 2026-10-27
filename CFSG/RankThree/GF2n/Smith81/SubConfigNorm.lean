module

public import CFSG.RankThree.GF2n.Smith81.SubConfigWidth
public import CFSG.RankThree.GF2n.Smith81.SubConfigDich
import CFSG.RankThree.GF2n.Smith81.SubConfigOrders
import CFSG.RankThree.GF2n.Stroth80.Sec7EndClassical
import CFSG.RankThree.GF2n.Smith81.InspOrth
import CFSG.Adapters.StatedQuasisimple

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def SubConfigNorm (M Q Z B : Subgroup G) (t : G) [(Q.subgroupOf (H0 M Z)).Normal]
    (B' : Subgroup (SubCfgGroup M Q Z)) : Prop :=
  Lgen (SubCfgM M Q Z (Nt M (LB M Q B) t))
      (LB (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t)) B') ≤
    Subgroup.normalizer (bar (H0 M Z) Q (Rt M (LB M Q B) t) : Set (SubCfgGroup M Q Z))

@[expose] def SubConfigE4NormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G),
    Smith1981Below (Nat.card G) → SmithECfg M Q Z B → CaseE4 M Q Z B t →
      ∀ [(Q.subgroupOf (H0 M Z)).Normal],
        StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
          (SubCfgZ M Q Z (Nt M (LB M Q B) t)) →
        ∀ B' : Subgroup (SubCfgGroup M Q Z),
          (∃ g, B' = conjSubgroup g (SubCfgZ M Q Z (Nt M (LB M Q B) t))) →
          B' ≤ SubCfgQ M Q Z (Nt M (LB M Q B) t) → B' ≠ SubCfgZ M Q Z (Nt M (LB M Q B) t) →
          StrothConclusion (SubCfgM M Q Z (Nt M (LB M Q B) t))
            (SubCfgQ M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' →
          SubConfigNorm M Q Z B t B'

@[expose] def SubConfigE5NormStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (t : G),
    Smith1981Below (Nat.card G) → SmithECfg M Q Z B → CaseE5 M Q Z B t →
      ∀ [(Q.subgroupOf (H0 M Z)).Normal],
        StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
          (SubCfgZ M Q Z (Nt M (LB M Q B) t)) →
        ∀ B' : Subgroup (SubCfgGroup M Q Z),
          (∃ g, B' = conjSubgroup g (SubCfgZ M Q Z (Nt M (LB M Q B) t))) →
          B' ≤ SubCfgQ M Q Z (Nt M (LB M Q B) t) → B' ≠ SubCfgZ M Q Z (Nt M (LB M Q B) t) →
          StrothConclusion (SubCfgM M Q Z (Nt M (LB M Q B) t))
            (SubCfgQ M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' →
          SubConfigNorm M Q Z B t B'

section Rho

variable {H Q : Subgroup G} [(Q.subgroupOf H).Normal]

theorem barMap_mem_bar_iff {S N : Subgroup G} (hSH : S ≤ H) (hQN : Q ≤ N) (x : ↥S) :
    ((barMap (Q := Q) hSH x : ↥(bar H Q S)) : ↥H ⧸ Q.subgroupOf H) ∈ bar H Q N ↔
      (x : G) ∈ N := by
  refine ⟨fun hx => ?_, fun hx => barMap_mem hSH hx⟩
  obtain ⟨y, hyN, hyx⟩ := Subgroup.mem_map.mp hx
  have h1 : y⁻¹ * Subgroup.inclusion hSH x ∈ Q.subgroupOf H := QuotientGroup.eq.mp hyx
  have h2 : (y : G)⁻¹ * (x : G) ∈ Q := h1
  have h3 : (x : G) = (y : G) * ((y : G)⁻¹ * (x : G)) := by group
  rw [h3]
  exact N.mul_mem (Subgroup.mem_subgroupOf.mp hyN) (hQN h2)

variable {S N : Subgroup G} (hSH : S ≤ H) {S' : Subgroup (↥H ⧸ Q.subgroupOf H)}
  (hSS : bar H Q S ≤ S') {Y : Type} [Group Y] (ψ : ↥S' →* Y)

@[expose] noncomputable def rho : ↥S →* Y :=
  ψ.comp ((Subgroup.inclusion hSS).comp (barMap (Q := Q) hSH))

theorem ker_rho (hQN : Q ≤ N) (hψ : ψ.ker = (bar H Q N).subgroupOf S') :
    (rho hSH hSS ψ).ker = N.subgroupOf S := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← barMap_mem_bar_iff hSH hQN x]
  show ψ (Subgroup.inclusion hSS (barMap hSH x)) = 1 ↔ _
  rw [← MonoidHom.mem_ker, hψ, Subgroup.mem_subgroupOf]
  rfl

theorem rho_range_conj (hnorm : S' ≤ Subgroup.normalizer (bar H Q S : Set (↥H ⧸ Q.subgroupOf H)))
    (s : ↥S') {y : Y} (hy : y ∈ (rho hSH hSS ψ).range) :
    ψ s * y * (ψ s)⁻¹ ∈ (rho hSH hSS ψ).range := by
  obtain ⟨x, rfl⟩ := hy
  have hmem : (s : ↥H ⧸ Q.subgroupOf H) * ((barMap (Q := Q) hSH x : ↥(bar H Q S)) : _) *
      (s : ↥H ⧸ Q.subgroupOf H)⁻¹ ∈ bar H Q S :=
    (Subgroup.mem_normalizer_iff.mp (hnorm s.2) _).mp (barMap hSH x).2
  obtain ⟨x', hx'⟩ := barMap_surjective hSH ⟨_, hmem⟩
  refine ⟨x', ?_⟩
  show ψ (Subgroup.inclusion hSS (barMap hSH x')) =
    ψ s * ψ (Subgroup.inclusion hSS (barMap hSH x)) * (ψ s)⁻¹
  rw [hx', ← map_inv, ← map_mul, ← map_mul]
  exact congrArg ψ (Subtype.ext rfl)

noncomputable def rhoRangeEquiv {R Y : Type} [Group R] [Group Y] (N₀ : Subgroup R) [N₀.Normal]
    (ρ : R →* Y) (hker : ρ.ker = N₀) : ↥ρ.range ≃* R ⧸ N₀ :=
  (QuotientGroup.quotientKerEquivRange ρ).symm.trans (QuotientGroup.quotientMulEquivOfEq hker)

end Rho

theorem le_of_ordD_dvd_prod_GL {f g m n : ℕ} (hf : 1 ≤ f) (hm : 1 ≤ m) (hg : 1 ≤ g)
    (h : ordD m (2 ^ f) ∣ ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ))) :
    f * (m * (m - 1)) ≤ g * (n * (n - 1) / 2) := by
  obtain ⟨r, -, hr⟩ := (Timmesfeld.Orders.profile_ordD hm hf).two
  obtain ⟨s, hs, hs'⟩ := prod_GL_two_part (n := n) hg
  rw [hr, hs'] at h
  have h2 : 2 ^ (f * (m * (m - 1))) ∣ 2 ^ (g * (n * (n - 1) / 2)) * s :=
    (dvd_mul_right _ _).trans h
  have hcop : Nat.Coprime (2 ^ (f * (m * (m - 1)))) s :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hs)
  have h3 := hcop.dvd_of_dvd_mul_right h2
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h3

section Steps

variable [Finite G] {M Q Z B : Subgroup G} {t : G}
  [(Q.subgroupOf (H0 M Z)).Normal]

theorem false_of_centTrivial (hc : Ctx M Q Z B) (hQN : Q ≤ Nt M (LB M Q B) t)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (h1 : 1 < Nat.card (↥(Rt M (LB M Q B) t) ⧸
      (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)))
    (hRH : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      H0 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    {S : Subgroup (SubCfgGroup M Q Z)}
    (hCT : CentTrivial (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)) S)
    (hcomm : ∀ h ∈ bar (H0 M Z) Q (Rt M (LB M Q B) t), ∀ y ∈ S,
      ⁅h, y⁆ ∈ SubCfgQ M Q Z (Nt M (LB M Q B) t)) : False := by
  have hle : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤ SubCfgQ M Q Z (Nt M (LB M Q B) t) :=
    fun h hh => hCT h (hRH hh) (hcomm h hh)
  have hcard := Subgroup.card_le_of_le hle
  rw [card_bar_Rt_eq hc t hQN] at hcard
  have hpos : 0 < Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) := Nat.card_pos
  nlinarith

theorem false_of_centDvd (hc : Ctx M Q Z B) (hQN : Q ≤ Nt M (LB M Q B) t)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (h2 : 2 ∣ Nat.card (↥(Rt M (LB M Q B) t) ⧸
      (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)))
    {g : ℕ} (hg1 : 1 ≤ g) (hg : Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) = 2 ^ g)
    (hRH : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      H0 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    {S : Subgroup (SubCfgGroup M Q Z)}
    (hCD : CentDvd (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)) S)
    (hcomm : ∀ h ∈ bar (H0 M Z) Q (Rt M (LB M Q B) t), ∀ y ∈ S,
      ⁅h, y⁆ ∈ SubCfgQ M Q Z (Nt M (LB M Q B) t)) : False := by
  obtain ⟨C, -, -, hC, hCdvd⟩ := hCD
  have hle : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤ C :=
    fun h hh => (hC h).mpr ⟨hRH hh, hcomm h hh⟩
  have hdvd := (Subgroup.card_dvd_of_le hle).trans hCdvd
  rw [card_bar_Rt_eq hc t hQN, hg] at hdvd
  have hdvd' := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hdvd
  have hodd : Odd (2 ^ g - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
    ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have := (Nat.odd_iff.mp hodd)
  have h22 := h2.trans hdvd'
  omega

theorem card_quot_dvd_or_eq_of_prod (hc : Ctx M Q Z B) (hQN : Q ≤ Nt M (LB M Q B) t)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    {X : Type} [Group X] [IsSimpleGroup X]
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* X)
    {S : Subgroup (SubCfgGroup M Q Z)}
    (hNorm : S ≤
      Subgroup.normalizer (bar (H0 M Z) Q (Rt M (LB M Q B) t) : Set (SubCfgGroup M Q Z)))
    (hRS : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤ S)
    [hnS : ((SubCfgQ M Q Z (Nt M (LB M Q B) t)).subgroupOf S).Normal] {A Bg : Type} [Group A]
    [Group Bg] [Finite A] [Finite Bg] [IsSimpleGroup Bg]
    (eAB : ↥S ⧸ (SubCfgQ M Q Z (Nt M (LB M Q B) t)).subgroupOf S ≃* A × Bg) :
    Nat.card X ∣ Nat.card A ∨ Nat.card X = Nat.card Bg := by
  have hRH := Rt_le_H0 hc t
  let ψ : ↥S →* A × Bg := eAB.toMonoidHom.comp (QuotientGroup.mk' _)
  have hψ : ψ.ker = (SubCfgQ M Q Z (Nt M (LB M Q B) t)).subgroupOf S := by
    ext x
    rw [MonoidHom.mem_ker]
    show eAB (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff _ eAB.injective, QuotientGroup.eq_one_iff]
  have hker := ker_rho hRH hRS ψ hQN hψ
  have hP : (rho hRH hRS ψ).range.Normal := by
    constructor
    intro y hy z
    obtain ⟨s, rfl⟩ : ∃ s, ψ s = z := by
      obtain ⟨w, rfl⟩ := eAB.surjective z
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective w
      exact ⟨s, rfl⟩
    exact rho_range_conj hRH hRS ψ hNorm s hy
  exact card_dvd_or_eq_of_normal_prod hP ((rhoRangeEquiv _ _ hker).trans e)

theorem card_quot_of_SL (hc : Ctx M Q Z B) (hQN : Q ≤ Nt M (LB M Q B) t)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    {X : Type} [Group X] (hXp : Group.IsPerfect X) [Nontrivial X]
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* X)
    {S : Subgroup (SubCfgGroup M Q Z)}
    (hNorm : S ≤
      Subgroup.normalizer (bar (H0 M Z) Q (Rt M (LB M Q B) t) : Set (SubCfgGroup M Q Z)))
    (hRS : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤ S) {n : ℕ} {K : Type} [Field K] [Finite K]
    (φ : ↥S →* GL (Fin n) K) (hφr : φ.range = StatedSL n K)
    (hφk : φ.ker = (SubCfgQ M Q Z (Nt M (LB M Q B) t)).subgroupOf S) :
    Nat.card X ∣ Nat.card (GL (Fin n) K) ∧
      (3 ≤ n → Nat.card X = Nat.card (Matrix.SpecialLinearGroup (Fin n) K)) := by
  have hRH := Rt_le_H0 hc t
  have hker := ker_rho hRH hRS φ hQN hφk
  have eR : ↥(rho hRH hRS φ).range ≃* X := (rhoRangeEquiv _ _ hker).trans e
  refine ⟨?_, fun hn3 => ?_⟩
  · rw [← Nat.card_congr eR.toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  · have hle : (rho hRH hRS φ).range ≤ StatedSL n K := by
      rw [← hφr]
      rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    let P : Subgroup ↥(StatedSL n K) := (rho hRH hRS φ).range.subgroupOf (StatedSL n K)
    have hPn : P.Normal := by
      constructor
      intro y hy z
      have hz : (z : GL (Fin n) K) ∈ φ.range := by
        rw [hφr]
        exact z.2
      obtain ⟨s, hs⟩ := hz
      have := rho_range_conj hRH hRS φ hNorm s hy
      rw [hs] at this
      exact this
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hq := CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := m) (by omega) K
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hPn with hP | hP
    · have hrange : (rho hRH hRS φ).range = StatedSL (m + 1) K := by
        apply le_antisymm hle
        intro y hy
        have : (⟨y, hy⟩ : ↥(StatedSL (m + 1) K)) ∈ P := hP ▸ Subgroup.mem_top _
        exact this
      rw [← Nat.card_congr eR.toEquiv, hrange, CFSG.Open.StatedAPI.card_statedSL]
    · exfalso
      have hcomm : ∀ a b : X, a * b = b * a := by
        intro a b
        have ha : (⟨(eR.symm a : GL (Fin (m + 1)) K), hle (eR.symm a).2⟩ :
            ↥(StatedSL (m + 1) K)) ∈ P := (eR.symm a).2
        have hb : (⟨(eR.symm b : GL (Fin (m + 1)) K), hle (eR.symm b).2⟩ :
            ↥(StatedSL (m + 1) K)) ∈ P := (eR.symm b).2
        have hab := Subgroup.mem_center_iff.mp (hP ha) ⟨_, hle (eR.symm b).2⟩
        apply eR.symm.injective
        apply Subtype.ext
        rw [map_mul, map_mul]
        have := congrArg Subtype.val hab
        exact this.symm
      have hbot : commutator X = ⊥ := by
        rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm a b
      rw [hXp.commutator_eq_top] at hbot
      exact (top_ne_bot hbot).elim

end Steps

section E4

variable [Finite G] {M Q Z B : Subgroup G} {t : G}
  [(Q.subgroupOf (H0 M Z)).Normal]

theorem subConfigE4_main (hc : Ctx M Q Z B) (h4 : CaseE4 M Q Z B t)
    (hH' : StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    {B' : Subgroup (SubCfgGroup M Q Z)} (hNorm : SubConfigNorm M Q Z B t B')
    (hB'c : ∃ g, B' = conjSubgroup g (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    (hB'le : B' ≤ SubCfgQ M Q Z (Nt M (LB M Q B) t))
    (hB'ne : B' ≠ SubCfgZ M Q Z (Nt M (LB M Q B) t))
    (hC' : StrothConclusion (SubCfgM M Q Z (Nt M (LB M Q B) t))
      (SubCfgQ M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B') :
    ∃ t' : SubCfgGroup M Q Z,
      CtxD4 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
          (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' t' ∧
        CaseE2Plus (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
          (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' t' 4 := by
  classical
  have hF := hC'.2
  obtain ⟨hQ17, d, hd, h17⟩ := subConfig_width_E4 hc h4 hH' hF
  obtain ⟨-, hN17, hR, -⟩ := h4
  obtain ⟨f, -, hf, -⟩ := hc.hyp.cp
  have hf2 : 2 ≤ f := by
    have h4 := hc.hyp.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  obtain ⟨hQN, -⟩ := card_subCfgQ_of hc hN17
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := hR
  haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans hf)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨hΩs, h16, -⟩ := endg_omegaPlus_facts (K := K) hK4 (m := 4) (by norm_num)
  have hΩp := CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 4)
    (by norm_num)
  have hΩo : Nat.card ↥(StatedOmega (StatedQuadPlus 4 K)) = ordD 4 (2 ^ f) :=
    card_omegaPlus_eq_ordD (by norm_num) (by omega) (hK.trans hf)
  haveI : IsSimpleGroup (↥(Rt M (LB M Q B) t) ⧸
    (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) := e.isSimpleGroup
  have hcardq := Nat.card_congr e.toEquiv
  obtain ⟨g, -, hg, -⟩ := hH'.cp
  have hq'4 := hH'.q4
  have hg1 : 1 ≤ g := by
    rw [hg] at hq'4
    by_contra h0
    push Not at h0
    interval_cases g
    norm_num at hq'4
  have hgd : g * (d + 1) = 17 * f := by
    have h := hd.symm.trans hQ17
    rw [hg, hf, ← pow_mul, ← pow_mul] at h
    have := Nat.pow_right_injective (le_refl 2) h
    linarith
  have hd17 : 17 ≤ d + 1 := Nat.le_of_dvd (by omega) h17
  have hgf : g ≤ f := by nlinarith
  have hRH := Rt_le_H0 hc t
  have hR'M := bar_Rt_le_subCfgM (Q := Q) (Z := Z) (M := M) (LB M Q B) t
  have hRC := bar_Rt_centralizes hc t hF hΩp e
  have hRH' : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      H0 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)) := fun r hr =>
    ⟨hR'M hr, Subgroup.mem_centralizer_iff.mpr fun z hz => (hRC r hr z hz).symm⟩
  have hctx' : Ctx (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' := ⟨hH', hB'c, hB'le, hB'ne⟩
  have hNS := Lgen_normalizes (SubCfgM M Q Z (Nt M (LB M Q B) t))
    (LB (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t)) B')
  have hQS : SubCfgQ M Q Z (Nt M (LB M Q B) t) ≤
      Lgen (SubCfgM M Q Z (Nt M (LB M Q B) t))
        (LB (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t)) B') :=
    le_sup_left.trans (le_Lgen_self _ _)
  have hdich := dichotomy ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) (barMap hRH)
    (barMap_surjective hRH) (fun x => (barMap_mem_bar_iff hRH hQN x).trans
      Subgroup.mem_subgroupOf.symm) hQS hR'M hNorm hNS
  have h1 : 1 < Nat.card (↥(Rt M (LB M Q B) t) ⧸
      (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) := by
    rw [hcardq]
    have := Nat.le_of_dvd (Nat.card_pos) h16
    omega
  obtain ⟨hTI, hcase⟩ := strothConclusion_cases_of_card hq'4 hd (by omega) (by omega) (by omega)
    (by omega) (by omega) hC'
  rcases hcase with ⟨hNA, t', ht', ht'Q, hCT, hii | hiv⟩ | h6
  ·
    rcases hdich with hcomm | hRS
    · exact (false_of_centTrivial hc hQN h1 hRH' hCT hcomm).elim
    obtain ⟨m, hm2, hQm, hNm', hpm⟩ := hii
    have hdm : d + 1 = 4 * m + 1 :=
      Nat.pow_right_injective (by omega : 2 ≤ Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
        (hd.symm.trans hQm)
    have hm4 : 4 ≤ m := by omega
    have hgm : g * (4 * m + 1) = 17 * f := hdm ▸ hgd
    rcases hpm with ⟨hRp, hSp⟩ | ⟨hRm, hSm⟩
    · obtain ⟨hnS, A, Bg, _, _, ⟨KA, _, _, hKA, ⟨eA⟩⟩, ⟨KB, _, _, hKB, ⟨eB⟩⟩, ⟨eAB⟩⟩ := hSp
      haveI : Finite A := Finite.of_equiv _ eA.symm.toEquiv
      haveI : Finite Bg := Finite.of_equiv _ eB.symm.toEquiv
      have hKB' : Nat.card KB = 2 ^ g := hKB.trans hg
      haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKB'
      haveI : IsSimpleGroup Bg := @MulEquiv.isSimpleGroup _ _ _ _
        (endg_omegaPlus_facts (K := KB) (by rw [hKB']; exact hg ▸ hq'4) (by omega)).1 eB
      rcases card_quot_dvd_or_eq_of_prod hc hQN e hNorm hRS eAB with hA | hB
      · exfalso
        rw [Nat.card_congr eA.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKA, hg,
          hΩo] at hA
        have := le_of_ordD_dvd_SL2 (by omega) (by norm_num) hg1 hA
        omega
      · rw [Nat.card_congr eB.toEquiv, card_omegaPlus_eq_ordD (by omega) hg1 hKB', hΩo] at hB
        have h2p := two_part_eq_of_ordD_eq_ordD (by omega) hg1 (by norm_num) (by omega) hB
        obtain ⟨rfl, -⟩ := e4_width_eq (by omega) (by linarith) hgm
        exact ⟨t', ⟨hTI, ht', ht'Q, hCT⟩, le_refl _ |>.trans (by norm_num), hQm, hNm', hRp,
          ⟨hnS, A, Bg, inferInstance, inferInstance, ⟨KA, inferInstance, inferInstance, hKA,
            ⟨eA⟩⟩, ⟨KB, inferInstance, inferInstance, hKB, ⟨eB⟩⟩, ⟨eAB⟩⟩⟩
    · exfalso
      obtain ⟨hnS, A, Bg, _, _, ⟨KA, _, _, hKA, ⟨eA⟩⟩, ⟨KB, _, _, hKB, b, c, hirr, ⟨eB⟩⟩,
        ⟨eAB⟩⟩ := hSm
      haveI : Finite A := Finite.of_equiv _ eA.symm.toEquiv
      haveI : Finite Bg := Finite.of_equiv _ eB.symm.toEquiv
      have hKB' : Nat.card KB = 2 ^ g := hKB.trans hg
      haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKB'
      haveI : IsSimpleGroup Bg := @MulEquiv.isSimpleGroup _ _ _ _
        (endg_omegaMinus_facts (K := KB) (by rw [hKB']; exact hg ▸ hq'4) hm2 hirr).1 eB
      rcases card_quot_dvd_or_eq_of_prod hc hQN e hNorm hRS eAB with hA | hB
      · rw [Nat.card_congr eA.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKA, hg,
          hΩo] at hA
        have := le_of_ordD_dvd_SL2 (by omega) (by norm_num) hg1 hA
        omega
      · rw [Nat.card_congr eB.toEquiv, Insp.card_statedOmega_minus_eq_ordTwistedD hm2 hirr,
          hKB', hΩo] at hB
        have h2p := two_part_eq_of_ordD_eq_ordTwistedD (by omega) hg1 (by norm_num) (by omega) hB
        obtain ⟨rfl, rfl⟩ := e4_width_eq (by omega) (by linarith) hgm
        exact (Insp.not_ordD_dvd_ordTwistedD hf2 (by norm_num)).1 hB.dvd
  ·
    exfalso
    have h33 : d + 1 = 33 :=
      Nat.pow_right_injective (by omega : 2 ≤ Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
        (hd.symm.trans hiv.1)
    omega
  ·
    exfalso
    obtain ⟨n, K', _, _, hK', φ, hφr, hφk, -, -, -, -, -, -, -, -, -, -, -, hCD⟩ := h6
    rcases hdich with hcomm | hRS
    · exact false_of_centDvd hc hQN (hcardq ▸ (dvd_trans (by norm_num) h16)) hg1 hg hRH' hCD
        hcomm
    have hK'g : Nat.card K' = 2 ^ g := hK'.trans hg
    haveI : Nontrivial ↥(StatedOmega (StatedQuadPlus 4 K)) := hΩs.toNontrivial
    obtain ⟨hGL, hSL⟩ := card_quot_of_SL hc hQN hΩp e hNorm hRS φ hφr hφk
    have hGLc : Nat.card (GL (Fin n) K') = ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) := by
      haveI := Fintype.ofFinite K'
      rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK'g]
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · rw [hGLc, hΩo] at hGL
      have := le_of_ordD_dvd_prod_GL (by omega) (by norm_num) hg1 hGL
      have hn2 : n * (n - 1) / 2 ≤ 1 := by interval_cases n <;> norm_num
      have : g * (n * (n - 1) / 2) ≤ g := by nlinarith
      omega
    · have hSLc := hSL hn3
      haveI : NeZero n := ⟨by omega⟩
      have hunits := Matrix.card_SL_mul_card_units (n := Fin n) (R := K')
      rw [Nat.card_units, hK'g, ← hSLc, hΩo, hGLc] at hunits
      exact e4_ordD_mul_ne_prod_GL hf2 hg1 hunits

end E4

section E5

variable [Finite G] {M Q Z B : Subgroup G} {t : G}
  [(Q.subgroupOf (H0 M Z)).Normal]

theorem subConfigE5_main (hc : Ctx M Q Z B) (h5 : CaseE5 M Q Z B t)
    (hH' : StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    {B' : Subgroup (SubCfgGroup M Q Z)} (hNorm : SubConfigNorm M Q Z B t B')
    (hB'c : ∃ g, B' = conjSubgroup g (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    (hB'le : B' ≤ SubCfgQ M Q Z (Nt M (LB M Q B) t))
    (hB'ne : B' ≠ SubCfgZ M Q Z (Nt M (LB M Q B) t))
    (hC' : StrothConclusion (SubCfgM M Q Z (Nt M (LB M Q B) t))
      (SubCfgQ M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B') :
    ∃ t' : SubCfgGroup M Q Z,
      CtxD4 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
          (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' t' ∧
        CaseE4 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
          (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' t' := by
  classical
  have hF := hC'.2
  obtain ⟨hQ33, d, hd, h11⟩ := subConfig_width_E5 hc h5 hH' hF
  obtain ⟨-, hN33, hR, -⟩ := h5
  obtain ⟨f, -, hf, -⟩ := hc.hyp.cp
  have hf2 : 2 ≤ f := by
    have h4 := hc.hyp.q4
    rw [hf] at h4
    by_contra hlt
    push Not at hlt
    interval_cases f <;> norm_num at h4
  obtain ⟨hQN, -⟩ := card_subCfgQ_of hc hN33
  obtain ⟨hn, K, _, _, hK, ⟨e⟩⟩ := hR
  haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq (hK.trans hf)
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  obtain ⟨hΩs, h16, -⟩ := endg_omegaPlus_facts (K := K) hK4 (m := 6) (by norm_num)
  have hΩp := CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadPlus (K := K) (n := 6)
    (by norm_num)
  have hΩo : Nat.card ↥(StatedOmega (StatedQuadPlus 6 K)) = ordD 6 (2 ^ f) :=
    card_omegaPlus_eq_ordD (by norm_num) (by omega) (hK.trans hf)
  haveI : IsSimpleGroup (↥(Rt M (LB M Q B) t) ⧸
    (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) := e.isSimpleGroup
  have hcardq := Nat.card_congr e.toEquiv
  obtain ⟨g, -, hg, -⟩ := hH'.cp
  have hq'4 := hH'.q4
  have hg1 : 1 ≤ g := by
    rw [hg] at hq'4
    by_contra h0
    push Not at h0
    interval_cases g
    norm_num at hq'4
  have hgd : g * (d + 1) = 33 * f := by
    have h := hd.symm.trans hQ33
    rw [hg, hf, ← pow_mul, ← pow_mul] at h
    have := Nat.pow_right_injective (le_refl 2) h
    linarith
  have hd11 : 11 ≤ d + 1 := Nat.le_of_dvd (by omega) h11
  have hgf : g ≤ 3 * f := by nlinarith
  have hRH := Rt_le_H0 hc t
  have hR'M := bar_Rt_le_subCfgM (Q := Q) (Z := Z) (M := M) (LB M Q B) t
  have hRC := bar_Rt_centralizes hc t hF hΩp e
  have hRH' : bar (H0 M Z) Q (Rt M (LB M Q B) t) ≤
      H0 (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)) := fun r hr =>
    ⟨hR'M hr, Subgroup.mem_centralizer_iff.mpr fun z hz => (hRC r hr z hz).symm⟩
  have hctx' : Ctx (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)) B' := ⟨hH', hB'c, hB'le, hB'ne⟩
  have hNS := Lgen_normalizes (SubCfgM M Q Z (Nt M (LB M Q B) t))
    (LB (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t)) B')
  have hQS : SubCfgQ M Q Z (Nt M (LB M Q B) t) ≤
      Lgen (SubCfgM M Q Z (Nt M (LB M Q B) t))
        (LB (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t)) B') :=
    le_sup_left.trans (le_Lgen_self _ _)
  have hdich := dichotomy ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) (barMap hRH)
    (barMap_surjective hRH) (fun x => (barMap_mem_bar_iff hRH hQN x).trans
      Subgroup.mem_subgroupOf.symm) hQS hR'M hNorm hNS
  have h1 : 1 < Nat.card (↥(Rt M (LB M Q B) t) ⧸
      (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) := by
    rw [hcardq]
    have := Nat.le_of_dvd (Nat.card_pos) h16
    omega
  obtain ⟨hTI, hcase⟩ := strothConclusion_cases_of_card hq'4 hd (by omega) (by omega) (by omega)
    (by omega) (by omega) hC'
  rcases hcase with ⟨hNA, t', ht', ht'Q, hCT, hii | hiv⟩ | h6
  ·
    exfalso
    rcases hdich with hcomm | hRS
    · exact false_of_centTrivial hc hQN h1 hRH' hCT hcomm
    obtain ⟨m, hm2, hQm, -, hpm⟩ := hii
    have hdm : d + 1 = 4 * m + 1 :=
      Nat.pow_right_injective (by omega : 2 ≤ Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
        (hd.symm.trans hQm)
    have hm3 : 3 ≤ m := by omega
    have hgm : g * (4 * m + 1) = 33 * f := hdm ▸ hgd
    rcases hpm with ⟨-, hSp⟩ | ⟨-, hSm⟩
    · obtain ⟨hnS, A, Bg, _, _, ⟨KA, _, _, hKA, ⟨eA⟩⟩, ⟨KB, _, _, hKB, ⟨eB⟩⟩, ⟨eAB⟩⟩ := hSp
      haveI : Finite A := Finite.of_equiv _ eA.symm.toEquiv
      haveI : Finite Bg := Finite.of_equiv _ eB.symm.toEquiv
      have hKB' : Nat.card KB = 2 ^ g := hKB.trans hg
      haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKB'
      haveI : IsSimpleGroup Bg := @MulEquiv.isSimpleGroup _ _ _ _
        (endg_omegaPlus_facts (K := KB) (by rw [hKB']; exact hg ▸ hq'4) hm3).1 eB
      rcases card_quot_dvd_or_eq_of_prod hc hQN e hNorm hRS eAB with hA | hB
      · rw [Nat.card_congr eA.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKA, hg,
          hΩo] at hA
        have := le_of_ordD_dvd_SL2 (by omega) (by norm_num) hg1 hA
        omega
      · rw [Nat.card_congr eB.toEquiv, card_omegaPlus_eq_ordD hm3 hg1 hKB', hΩo] at hB
        have h2p := two_part_eq_of_ordD_eq_ordD (by omega) hg1 (by norm_num) (by omega) hB
        exact e5_no_width (by omega) (by linarith) hgm
    · obtain ⟨hnS, A, Bg, _, _, ⟨KA, _, _, hKA, ⟨eA⟩⟩, ⟨KB, _, _, hKB, b, c, hirr, ⟨eB⟩⟩,
        ⟨eAB⟩⟩ := hSm
      haveI : Finite A := Finite.of_equiv _ eA.symm.toEquiv
      haveI : Finite Bg := Finite.of_equiv _ eB.symm.toEquiv
      have hKB' : Nat.card KB = 2 ^ g := hKB.trans hg
      haveI := Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKB'
      haveI : IsSimpleGroup Bg := @MulEquiv.isSimpleGroup _ _ _ _
        (endg_omegaMinus_facts (K := KB) (by rw [hKB']; exact hg ▸ hq'4) hm2 hirr).1 eB
      rcases card_quot_dvd_or_eq_of_prod hc hQN e hNorm hRS eAB with hA | hB
      · rw [Nat.card_congr eA.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hKA, hg,
          hΩo] at hA
        have := le_of_ordD_dvd_SL2 (by omega) (by norm_num) hg1 hA
        omega
      · rw [Nat.card_congr eB.toEquiv, Insp.card_statedOmega_minus_eq_ordTwistedD hm2 hirr,
          hKB', hΩo] at hB
        have h2p := two_part_eq_of_ordD_eq_ordTwistedD (by omega) hg1 (by norm_num) (by omega) hB
        exact e5_no_width (by omega) (by linarith) hgm
  ·
    exact ⟨t', ⟨hTI, ht', ht'Q, hCT⟩, hiv⟩
  ·
    exfalso
    obtain ⟨n, K', _, _, hK', φ, hφr, hφk, -, -, -, -, -, -, -, -, -, -, -, hCD⟩ := h6
    rcases hdich with hcomm | hRS
    · exact false_of_centDvd hc hQN (hcardq ▸ (dvd_trans (by norm_num) h16)) hg1 hg hRH' hCD
        hcomm
    have hK'g : Nat.card K' = 2 ^ g := hK'.trans hg
    haveI : Nontrivial ↥(StatedOmega (StatedQuadPlus 6 K)) := hΩs.toNontrivial
    obtain ⟨hGL, hSL⟩ := card_quot_of_SL hc hQN hΩp e hNorm hRS φ hφr hφk
    have hGLc : Nat.card (GL (Fin n) K') = ∏ i : Fin n, ((2 ^ g) ^ n - (2 ^ g) ^ (i : ℕ)) := by
      haveI := Fintype.ofFinite K'
      rw [Matrix.card_GL_field, ← Nat.card_eq_fintype_card, hK'g]
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · rw [hGLc, hΩo] at hGL
      have := le_of_ordD_dvd_prod_GL (by omega) (by norm_num) hg1 hGL
      have hn2 : n * (n - 1) / 2 ≤ 1 := by interval_cases n <;> norm_num
      have : g * (n * (n - 1) / 2) ≤ g := by nlinarith
      omega
    · have hSLc := hSL hn3
      haveI : NeZero n := ⟨by omega⟩
      have hunits := Matrix.card_SL_mul_card_units (n := Fin n) (R := K')
      rw [Nat.card_units, hK'g, ← hSLc, hΩo, hGLc] at hunits
      exact e5_ordD_mul_ne_prod_GL hf2 hg1 hunits

end E5

theorem subConfigE4_of_norm (hN : SubConfigE4NormStatement) :
    SubConfigE4Statement := by
  intro G _ _ M Q Z B t N hNdef hb hE h4 _ hH' B' hB'c hB'le hB'ne hC'
  subst hNdef
  exact subConfigE4_main hE.ctx h4 hH' (hN G M Q Z B t hb hE h4 hH' B' hB'c hB'le hB'ne hC')
    hB'c hB'le hB'ne hC'

theorem subConfigE5_of_norm (hN : SubConfigE5NormStatement) :
    SubConfigE5Statement := by
  intro G _ _ M Q Z B t N hNdef hb hE h5 _ hH' B' hB'c hB'le hB'ne hC'
  subst hNdef
  exact subConfigE5_main hE.ctx h5 hH' (hN G M Q Z B t hb hE h5 hH' B' hB'c hB'le hB'ne hC')
    hB'c hB'le hB'ne hC'

end CFSG.RankThree.GF2n.Smith81.SubCfg
