module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Setup4S21Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PSplitDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3POdd
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PTwoSplit
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3PRoot
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3P149
import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameLin
import CFSG.LocalAnalysis.UniquenessCase.UC22L3FrameUni
import CFSG.LocalAnalysis.UniquenessCase.UC22L3ThreeNoFive
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aULift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Holds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3BadNoStrongHolds
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeKIBA6
import CFSG.LocalAnalysis.UniquenessCase.UCK35wHolds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZHolds
import CFSG.HardMathSupport.Foote.FamilyReduction.ClassicalFive
import CFSG.Quasithin.Background.A3FactsA134
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
import CFSG.GroupTheory.SylowIntersectionControl.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped Pointwise
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree)

section Local

variable {G : Type} [Group G] [Finite G]

theorem uc22l3p4_false_of_kf7 {D : Data G} (hKF7 : KF7Use D) {p : ℕ} (hpσ : p ∈ D.sig)
    (hp5 : p ≠ 5) (hM : IsStronglyPEmbedded p D.M) {H : Subgroup G} (hHne : H ≠ ⊤)
    (hHM : ¬ H ≤ D.M) (hrank : 2 ≤ Open.pRank p (H ⊓ D.M)) {J : Subgroup G}
    (hJ : J ≤ H ⊓ D.M) {X : Type} [Group X] (f : ↥J →* X) {K : Subgroup X} (hK : ⁅K, K⁆ = K)
    (hKf : K ≤ f.range) (hpK : p ∣ Nat.card K) : False := by
  classical
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have : Fact p.Prime := ⟨hp⟩
  have hJH : J ≤ H := hJ.trans inf_le_left
  have hKF := hKF7 p hpσ H ⟨hp, hp2, hM, hHne, hHM, by omega⟩
  let ψ : ↥J →* F07.QuotK7 p H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hJH)
  have hψle : ψ.range ≤
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hJ x.2))
  have hKD : ∀ m : ℕ, K ≤ (derivedSeries ↥J m).map f := by
    intro m
    induction m with
    | zero => simpa only [derivedSeries_zero, Subgroup.map_top] using hKf
    | succ m ih =>
      rw [derivedSeries_succ (G := ↥J) m, Subgroup.map_commutator, ← hK]
      exact Subgroup.commutator_mono ih ih
  rcases hKF with hsolv | ⟨hp5', -⟩
  · have : Group.IsSolvable
        ↥(((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hsolv
    have : Group.IsSolvable ↥ψ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hψle)
        (Subgroup.inclusion_injective hψle)
    obtain ⟨n, hn⟩ :=
      (Group.isSolvable_def ↥ψ.range).mp (inferInstance : Group.IsSolvable ↥ψ.range)
    have hmap : (derivedSeries ↥J n).map ψ.rangeRestrict = ⊥ := by
      rw [map_derivedSeries_eq (MonoidHom.rangeRestrict_surjective ψ) n, hn]
    have hker : derivedSeries ↥J n ≤ ψ.ker := by
      have h := (Subgroup.map_eq_bot_iff (derivedSeries ↥J n)
        (f := ψ.rangeRestrict)).1 hmap
      rwa [MonoidHom.ker_rangeRestrict] at h
    have hKmap : K ≤ (ψ.ker).map f := (hKD n).trans (Subgroup.map_mono hker)
    have hψker : ψ.ker = (CFSG.pPrimeCore p ↥H).comap (Subgroup.inclusion hJH) := by
      ext x
      show ψ x = 1 ↔ Subgroup.inclusion hJH x ∈ CFSG.pPrimeCore p ↥H
      exact QuotientGroup.eq_one_iff (Subgroup.inclusion hJH x)
    have hdvd₁ : Nat.card ↥ψ.ker ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H) := by
      rw [hψker]
      exact Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hJH)
    have hpI : ¬ p ∣ Nat.card ↥(CFSG.pPrimeCore p ↥H) :=
      (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
    have hpn : ¬ p ∣ Nat.card ↥((ψ.ker).map f) := fun h =>
      hpI (h.trans ((Subgroup.card_map_dvd ψ.ker f).trans hdvd₁))
    exact hpn (hpK.trans (Subgroup.card_dvd_of_le hKmap))
  · exact hp5 hp5'

theorem uc22l3p4_exists_conj_isSylowOf (D : Data G) (L : Subgroup G) :
    ∃ g ∈ D.M, CFSG.ABGLocalTools.IsSylowOf 2
      (D.T ⊓ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
      (D.M ⊓ normalizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
  classical
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (D.M ⊓ normalizer (L : Set G))
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  obtain ⟨g, -, hconj⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (⊤ : Subgroup ↥D.M) S le_top (R.subgroupOf D.M) le_top hR.isPGroup.comap_subtype
  have hgM : (g : G) ∈ D.M := g.2
  have hRM : R ≤ D.M := hR.le.trans inf_le_left
  have hcomp : (D.M).subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp (D.M).subtype := by
    ext x
    rfl
  have hmap : ((R.subgroupOf D.M).map (MulAut.conj g).toMonoidHom).map (D.M).subtype =
      R.map (MulAut.conj (g : G)).toMonoidHom := by
    rw [Subgroup.map_map, hcomp]
    conv_rhs => rw [← Subgroup.map_subgroupOf_eq_of_le hRM]
    rw [Subgroup.map_map]
  have hleT : R.map (MulAut.conj (g : G)).toMonoidHom ≤ D.T := by
    have h := Subgroup.map_mono (f := (D.M).subtype) hconj
    rw [hmap, hS, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr D.sylowM.le] at h
    exact h
  have hMmap : D.M.map (MulAut.conj (g : G)).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hgM)
  have hNmap : (D.M ⊓ normalizer (L : Set G)).map (MulAut.conj (g : G)).toMonoidHom =
      D.M ⊓ normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (g : G)).injective, hMmap,
      Subgroup.map_normalizer_eq_of_bijective L (MulAut.conj (g : G)).bijective]
  have hR'syl : CFSG.ABGLocalTools.IsSylowOf 2 (R.map (MulAut.conj (g : G)).toMonoidHom)
      (D.M ⊓ normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G)) := by
    rw [← hNmap]
    exact CFSG.GroupTheory.isSylowOf_map_conj hR (g : G)
  have hRLmap : R.map (MulAut.conj (g : G)).toMonoidHom ≤
      normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj (g : G)).toMonoidHom)
      (hR.le.trans inf_le_right)
    rwa [Subgroup.map_normalizer_eq_of_bijective L (MulAut.conj (g : G)).bijective] at h
  refine ⟨(g : G), hgM, ?_⟩
  have hPR : R.map (MulAut.conj (g : G)).toMonoidHom ≤
      D.T ⊓ normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G) :=
    le_inf hleT hRLmap
  have hQle : D.T ⊓ normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G)
      ≤ D.M ⊓ normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G) :=
    inf_le_inf D.sylowM.le le_rfl
  have hQp : IsPGroup 2
      ↥(D.T ⊓ normalizer ((L.map (MulAut.conj (g : G)).toMonoidHom : Subgroup G) : Set G)) :=
    D.sylowM.isPGroup.to_inf_left
  have heq := hR'syl.eq_of_le hPR hQle hQp
  rw [heq]
  exact hR'syl

omit [Finite G] in
private theorem dvd_card_conj_calC {L : Subgroup G} {g x : G} {q : ℕ}
    (h : q ∣ Nat.card ↥(L ⊓ centralizer ({g⁻¹ * x * g} : Set G))) :
    q ∣ Nat.card ↥(L.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({x} : Set G)) := by
  rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _)] at h
  refine h.trans (card_dvd_of_le ?_)
  rintro _ ⟨y, hy, rfl⟩
  rw [SetLike.mem_coe, mem_inf, mem_centralizer_singleton_iff] at hy
  refine mem_inf.2 ⟨mem_map_of_mem _ hy.1, mem_centralizer_singleton_iff.2 ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc g * y * g⁻¹ * x = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by group
    _ = g * (g⁻¹ * x * g * y) * g⁻¹ := by rw [hy.2]
    _ = x * (g * y * g⁻¹) := by group

private theorem two_le_pRank_of_ne_calC {M L L' C : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hL : L ∈ calC M) (hL' : L' ∈ calC M) (hne : L ≠ L')
    (hZ : ¬ q ∣ Nat.card (center (Bar2 L))) (hCM : C ≤ M) (h : q ∣ Nat.card ↥(L ⊓ C))
    (h' : q ∣ Nat.card ↥(L' ⊓ C)) : 2 ≤ Open.pRank q C := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have h1 : ∀ X : Subgroup G, X ≤ M → q ∣ Nat.card X → 1 ≤ Open.pRank q (barImage M X) := by
    intro X hXM hX
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hX
    have hxo : orderOf (x : G) = q := by rw [Subgroup.orderOf_coe, hx]
    rw [show Open.pRank q (barImage M X) = Open.pRank q X from
      CFSG.AGLEmbedding.pRank_barM_eq hq hq2 M X hXM]
    exact UC6S846.le_pRank' hq (zpowers_le.2 x.2)
      (CFSG.Open.isElemAbelian_zpowers (by rw [← hxo]; exact pow_orderOf_eq_one _))
      (by rw [Nat.card_zpowers, hxo, pow_one])
  have hA := h1 _ (inf_le_left.trans hL.1.le) h
  have hB := h1 _ (inf_le_left.trans hL'.1.le) h'
  have hAL : barImage M (L ⊓ C) ≤ barImage M L := map_mono (comap_mono inf_le_left)
  have hBL : barImage M (L' ⊓ C) ≤ barImage M L' := map_mono (comap_mono inf_le_left)
  have hcomm := uc22p22l_barImage_commute hL hL' hne
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv hL
  have hle : barImage M (L ⊓ C) ⊓ barImage M (L' ⊓ C) ≤
      (center ↥(barImage M L)).map (barImage M L).subtype := fun z hz =>
    ⟨⟨z, hAL hz.1⟩, mem_center_iff.2 fun w => Subtype.ext (hcomm w w.2 z (hBL hz.2)), rfl⟩
  have hZ' := (Nat.card_congr (centerCongr e).toEquiv) ▸ hZ
  have hcop : Nat.Coprime q (Nat.card ↥(barImage M (L ⊓ C) ⊓ barImage M (L' ⊓ C))) :=
    (hq.coprime_iff_not_dvd).2 fun hd =>
      hZ' (card_map_of_injective (subtype_injective (barImage M L)) ▸ hd.trans (card_dvd_of_le hle))
  have hsum := CFSG.AGLEmbedding.pRank_add_le_pRank_sup_of_coprime hq
    (fun x hx y hy => hcomm x (hAL hx) y (hBL hy)) hcop
  have hmono := CFSG.SectionRank.pRank_mono hq.one_lt
    (sup_le (map_mono (comap_mono inf_le_right)) (map_mono (comap_mono inf_le_right)) :
      barImage M (L ⊓ C) ⊔ barImage M (L' ⊓ C) ≤ barImage M C)
  have hC : Open.pRank q (barImage M C) = Open.pRank q C :=
    CFSG.AGLEmbedding.pRank_barM_eq hq hq2 M C hCM
  omega

theorem uc22l3p4_false_of_invertSplit (hIS : L3InvertSplit) {D : Data G} (h149 : R149L3P D)
    (hH : H1930 D) (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n) (hn2 : IsPowTwo c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1)
    (hBN : c.B0 ≤ normalizer (L : Set G))
    (hfaith : ∀ b ∈ c.B0, ∀ hb : b ∈ normalizer (L : Set G),
      inducedBarInfAutHom L ⟨b, hb⟩ = 1 → b = 1)
    (hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ normalizer (L : Set G))
      (D.M ⊓ normalizer (L : Set G)))
    (hinv : ∀ d ∈ c.B0, (orderOf d).Prime → ∀ hd : d ∈ normalizer (L : Set G),
      ∀ K : Subgroup (BarInf L), ⁅K, K⁆ = K → p ∣ Nat.card K →
        (∀ k ∈ K, inducedBarInfAutHom L ⟨d, hd⟩ k = k) →
          ∀ m ∈ D.M, m * d * m⁻¹ = d⁻¹ → m ∈ normalizer (L : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ : Subgroup G := D.M ⊓ normalizer (L : Set G)
  have hΓN : Γ ≤ normalizer (L : Set G) := inf_le_right
  have hLΓ : L ≤ Γ := le_inf hL.1.le le_normalizer
  have hBΓ : c.B0 ≤ Γ := le_inf c.hBM hBN
  have hTΓ : D.T ⊓ normalizer (L : Set G) ≤ Γ := inf_le_inf_right _ D.sylowM.le
  obtain ⟨-, hBab, -, -, -, -, -, -, -, hBT, -, -⟩ := c.hB0
  have hBT' : (c.B0 : Set G) * (D.T : Set G) = (D.T : Set G) * (c.B0 : Set G) := hBT
  have hBo : Odd (Nat.card ↥c.B0) := ch214_odd_card c.hpi
  obtain ⟨h3, h5⟩ := uc22s2112l3p_three_five_dvd c hn3 hn2
  have hB0ne : c.B0 ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at h3
    exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
  let θ : ↥Γ →* MulAut (BarInf L) := (inducedBarInfAutHom L).comp (Subgroup.inclusion hΓN)
  let B' : Subgroup ↥Γ := c.B0.subgroupOf Γ
  let T' : Subgroup ↥Γ := (D.T ⊓ normalizer (L : Set G)).subgroupOf Γ
  have hfθ : ∀ b ∈ B', θ b = 1 → b = 1 := fun b hb h1 => Subtype.ext (hfaith b hb (hΓN b.2) h1)
  have hinj : Function.Injective (θ.domRestrict B') := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hfθ x x.2 hx)
  have hT'2 : IsPGroup 2 ↥T' :=
    D.sylowM.isPGroup.to_inf_left.of_equiv (Subgroup.subgroupOfEquivOfLe hTΓ).symm
  have hB'o : Odd (Nat.card ↥B') := by
    rw [show Nat.card ↥B' = Nat.card ↥c.B0 from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv]
    exact hBo
  have hperm' : (B' : Set ↥Γ) * (T' : Set ↥Γ) = (T' : Set ↥Γ) * (B' : Set ↥Γ) := by
    ext x
    simp only [Set.mem_mul]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have hb' : (b : G) ∈ D.T ⊓ normalizer (L : Set G) := hb
      have h : (a : G) * b ∈ (c.B0 : Set G) * (D.T : Set G) := Set.mul_mem_mul ha hb'.1
      rw [hBT'] at h
      obtain ⟨t, ht, b₁, hb₁, he⟩ := h
      have htN : t ∈ normalizer (L : Set G) := by
        have hte : t = (a : G) * b * b₁⁻¹ := by rw [← he]; group
        rw [hte]
        exact mul_mem (mul_mem (hBN ha) hb'.2) (inv_mem (hBN hb₁))
      exact ⟨⟨t, hTΓ ⟨ht, htN⟩⟩, ⟨ht, htN⟩, ⟨b₁, hBΓ hb₁⟩, hb₁, Subtype.ext he⟩
    · rintro ⟨a, ha, b, hb, rfl⟩
      have ha' : (a : G) ∈ D.T ⊓ normalizer (L : Set G) := ha
      have h : (a : G) * b ∈ (D.T : Set G) * (c.B0 : Set G) := Set.mul_mem_mul ha'.1 hb
      rw [← hBT'] at h
      obtain ⟨b₁, hb₁, t, ht, he⟩ := h
      have htN : t ∈ normalizer (L : Set G) := by
        have hte : t = b₁⁻¹ * ((a : G) * b) := by rw [← he]; group
        rw [hte]
        exact mul_mem (inv_mem (hBN hb₁)) (mul_mem ha'.2 (hBN hb))
      exact ⟨⟨b₁, hBΓ hb₁⟩, hb₁, ⟨t, hTΓ ⟨ht, htN⟩⟩, ⟨ht, htN⟩, Subtype.ext he⟩
  have hInn : (MulAut.conj : BarInf L →* MulAut (BarInf L)).range ≤ θ.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨⟨l, hLΓ l.2⟩, uc22s2113_inducedBarInfAutHom_of_mem l.2⟩
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T'.map θ) θ.range := by
    have hT : CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ := by
      rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff Γ, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hTΓ, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hTsyl
    have h := PartTwo.s16c7_isSylowOf_map hT θ
    rwa [← MonoidHom.range_eq_map] at h
  have hBab' : IsMulCommutative ↥(B'.map θ) := by
    refine ⟨⟨fun x y => ?_⟩⟩
    obtain ⟨x', hx', hx⟩ := x.2
    obtain ⟨y', hy', hy⟩ := y.2
    apply Subtype.ext
    change (x : MulAut (BarInf L)) * y = y * x
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h := congrArg Subtype.val (hBab.is_comm.comm ⟨(x' : G), hx'⟩ ⟨(y' : G), hy'⟩)
    exact h
  have hcard : Nat.card ↥(B'.map θ) = Nat.card ↥c.B0 := by
    rw [← MonoidHom.restrict_range B' θ, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBΓ).toEquiv
  have hperm : ((B'.map θ : Subgroup _) : Set (MulAut (BarInf L))) *
      ((T'.map θ : Subgroup _) : Set (MulAut (BarInf L))) =
      ((T'.map θ : Subgroup _) : Set (MulAut (BarInf L))) *
        ((B'.map θ : Subgroup _) : Set (MulAut (BarInf L))) := by
    rw [Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hperm', Set.image_mul]
  have hfin : (∃ s ∈ T'.map θ, ∀ b ∈ B'.map θ, s * b * s⁻¹ = b⁻¹) → False := by
    rintro ⟨_, ⟨τ, hτ, rfl⟩, hs⟩
    obtain ⟨t, htT, ht⟩ := uc22s2112u_lift_inv θ hT'2 hB'o hperm' hfθ hτ
      (fun b hb => hs (θ b) (mem_map_of_mem θ hb))
    have hinvG : ∀ b ∈ c.B0, (t : G) * b * (t : G)⁻¹ = b⁻¹ := fun b hb =>
      congrArg Subtype.val (ht ⟨b, hBΓ hb⟩ hb)
    have htT' : (t : G) ∈ D.T ⊓ normalizer (L : Set G) := htT
    obtain ⟨hi, -⟩ := c.hch
    exact hi hB0ne (t : G) htT'.1 (uc22s2112u_mem_normalizer_of_inv hinvG) hinvG
  refine hfin (hIS (BarInf L) p hp hp2 hX θ.range (T'.map θ) (B'.map θ)
    hInn hSyl (Subgroup.map_le_range (f := θ) B') hBab' (by rw [hcard]; exact hBo)
    (by rw [hcard]; exact h3) (by rw [hcard]; exact h5) hperm ?_)
  intro K hKperf hKcard d hdB hdp hdK
  obtain ⟨d₀, hd₀B, rfl⟩ := hdB
  have hd₀B' : (d₀ : G) ∈ c.B0 := hd₀B
  have hord : orderOf (d₀ : G) = orderOf (θ d₀) := by
    calc orderOf (d₀ : G) = orderOf d₀ := Subgroup.orderOf_coe d₀
      _ = orderOf (⟨d₀, hd₀B⟩ : ↥B') := (Subgroup.orderOf_mk d₀ hd₀B).symm
      _ = orderOf (θ.domRestrict B' ⟨d₀, hd₀B⟩) := (orderOf_injective _ hinj _).symm
      _ = orderOf (θ d₀) := rfl
  have hd₀p : (orderOf (d₀ : G)).Prime := by rw [hord]; exact hdp
  have hd₀2 : orderOf (d₀ : G) ≠ 2 := fun h2 => by
    have hdvd : orderOf (d₀ : G) ∣ Nat.card ↥c.B0 :=
      Subgroup.orderOf_dvd_natCard c.B0 hd₀B'
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.2 hBo) (even_iff_two_dvd.2 hdvd)
  have hLM : L ≤ D.M := hL.1.le
  have hdvdK := uc22s2112l3p_card_dvd_of_fixes hL.2.2 (hΓN d₀.2) hd₀p hd₀2 hKperf hdK
  obtain ⟨r, hr, hrd, hrM⟩ := h149 L hL p hp hp2 hX
  have : Fact r.Prime := ⟨hr⟩
  have hdvd' : r ∣ Nat.card ↥(L ⊓ centralizer ({(d₀ : G)} : Set G)) :=
    hrd.trans (by rw [← hKcard]; exact hdvdK)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hdvd'
  have hyo : orderOf (y : G) = r := by rw [Subgroup.orderOf_coe, hy]
  have hyL := mem_inf.1 y.2
  have hX0 : zpowers (y : G) ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  have hX0p : IsPGroup r (zpowers (y : G)) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hX0U := mem_uniqueSet_of_isStronglyPEmbedded hr hrM (zpowers_le.2 (hLM hyL.1)) hX0 hX0p
  obtain ⟨-, -, hCN, -⟩ := uc22s2112r2_normalizer hH c hLM hd₀B' hd₀p
  have hb0 : zpowers (d₀ : G) ≠ ⊥ := fun h => by
    rw [zpowers_eq_bot] at h
    rw [h, orderOf_one] at hd₀p
    exact Nat.not_prime_one hd₀p
  let c₀ : Ctx21 D (Choice214U D) := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  obtain ⟨m, hm, hminv⟩ := s21_10 D (Choice214U D) hH c₀ (zpowers (d₀ : G)) hb0
    (zpowers_le.2 hd₀B') (zpowers (y : G)) hX0 ⟨r, hr, hX0p⟩ (zpowers_le.2 (hCN hyL.2)) hX0U
  have hmd : m * (d₀ : G) * m⁻¹ = (d₀ : G)⁻¹ := hminv _ (mem_zpowers _)
  have hmN : m ∈ normalizer (L : Set G) :=
    hinv d₀ hd₀B' hd₀p (hΓN d₀.2) K hKperf (hKcard ▸ dvd_mul_right p _) hdK m hm hmd
  refine ⟨θ ⟨m, hm, hmN⟩, ⟨⟨m, hm, hmN⟩, rfl⟩, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
  congr 1
  exact Subtype.ext hmd

omit [Finite G] in
private theorem barInf_perfect {L : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅(⊤ : Subgroup (BarInf L)), (⊤ : Subgroup (BarInf L))⁆ = (⊤ : Subgroup (BarInf L)) := by
  have hLtop : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    rw [← Subgroup.map_subtype_inj (H := L), Subgroup.map_commutator]
    have hmap : (⊤ : Subgroup ↥L).map L.subtype = L := by
      ext x
      exact ⟨by rintro ⟨y, -, rfl⟩; exact y.2, fun hx => ⟨⟨x, hx⟩, trivial, rfl⟩⟩
    rw [hmap, hL]
  have hsurj : Function.Surjective (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hmap : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) =
      ⁅(⊤ : Subgroup (BarInf L)), (⊤ : Subgroup (BarInf L))⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hsurj]
  rw [← hmap, hLtop, Subgroup.map_top_of_surjective _ hsurj]

theorem uc22l3p4_eq_one_of_kf7 {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hp5 : p ≠ 5)
    (hM : IsStronglyPEmbedded p D.M) (hZ : ¬ p ∣ Nat.card (center (Bar2 L)))
    (hpL : 2 ≤ Open.pRank p L) {b : G} (hbB : b ∈ c.B0) (hb : b ∈ normalizer (L : Set G))
    (h1 : inducedBarInfAutHom L ⟨b, hb⟩ = 1) : b = 1 := by
  by_contra hbne
  have hodd : Odd (orderOf b) :=
    (ch214_odd_card c.hpi).of_dvd_nat (Subgroup.orderOf_dvd_natCard c.B0 hbB)
  have ho1 : orderOf b ≠ 1 := fun h => hbne (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd ho1
  have hq2 : q ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (h ▸ hqdvd))
  let b' : G := b ^ (orderOf b / q)
  have hb'B : b' ∈ c.B0 := Subgroup.pow_mem c.B0 hbB _
  have hb'N : b' ∈ normalizer (L : Set G) := Subgroup.pow_mem _ hb _
  have hord : orderOf b' = q :=
    orderOf_pow_orderOf_div (orderOf_pos b).ne' hqdvd
  have hb'p : (orderOf b').Prime := by rw [hord]; exact hq
  have hb'2 : orderOf b' ≠ 2 := by rw [hord]; exact hq2
  have hb'pow : (⟨b, hb⟩ : ↥(normalizer (L : Set G))) ^ (orderOf b / q) = ⟨b', hb'N⟩ := by
    ext
    rfl
  have h1' : inducedBarInfAutHom L ⟨b', hb'N⟩ = 1 := by
    rw [← hb'pow, map_pow, h1, one_pow]
  have hperf : ⁅(⊤ : Subgroup (BarInf L)), (⊤ : Subgroup (BarInf L))⁆ =
      (⊤ : Subgroup (BarInf L)) := barInf_perfect hL.2.1
  have htop : ⊤ ≤ ((centralizer ({b'} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) :=
    uc22s2112l3p_le_map_centralizer hL.2.2 hb'N hb'p hb'2 hperf
      (fun k _ => by rw [h1']; rfl)
  let J : Subgroup G := L ⊓ centralizer ({b'} : Set G)
  let f : ↥J →* BarInf L :=
    (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp (Subgroup.inclusion (inf_le_left : J ≤ L))
  have hfrange : f.range = ((centralizer ({b'} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 j.2).2)
    · intro hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hx
      refine ⟨⟨l, ⟨l.2, Subgroup.mem_subgroupOf.1 hl⟩⟩, ?_⟩
      change (QuotientGroup.mk' (CFSG.solvableRadical ↥L))
        (Subgroup.inclusion (inf_le_left : J ≤ L) ⟨l, ⟨l.2, Subgroup.mem_subgroupOf.1 hl⟩⟩) =
        QuotientGroup.mk' (CFSG.solvableRadical ↥L) l
      rw [show Subgroup.inclusion (inf_le_left : J ≤ L)
          ⟨l, ⟨l.2, Subgroup.mem_subgroupOf.1 hl⟩⟩ = l from Subtype.ext rfl]
  have hKf : (⊤ : Subgroup (BarInf L)) ≤ f.range := by
    rw [hfrange]
    exact htop
  obtain ⟨hHne, hHM, -, hCH⟩ := uc22s2112r2_normalizer hH c hL.1.le hb'B hb'p
  have hOcop : p.Coprime (Nat.card ↥(CFSG.solvableRadical ↥L)) :=
    (hp.coprime_iff_not_dvd).2 (not_dvd_card_solvableRadical hL.2.2 hp hp2 hZ)
  have hYtop : ((centralizer ({b'} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) = ⊤ := top_le_iff.mp htop
  have hpeq := CFSG.AGLEmbedding.pRank_map_mk_eq_pRank_map_subtype (p := p) (H := L) hp
    (CFSG.solvableRadical ↥L) hOcop ((centralizer ({b'} : Set G)).subgroupOf L)
  have hJeq : ((centralizer ({b'} : Set G)).subgroupOf L).map L.subtype = J := by
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrankJ : 2 ≤ Open.pRank p J := by
    rw [← hJeq, ← hpeq, hYtop, uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact hpL
  have hrank : 2 ≤ Open.pRank p (normalizer ((zpowers b' : Subgroup G) : Set G) ⊓ D.M) :=
    hrankJ.trans (CFSG.SectionRank.pRank_mono hp.one_lt hCH)
  have hrankT : 2 ≤ Open.pRank p (⊤ : Subgroup (BarInf L)) := by
    rw [← hYtop, hpeq, hJeq]
    exact hrankJ
  have hpK : p ∣ Nat.card (⊤ : Subgroup (BarInf L)) := by
    obtain ⟨E, hE, -, hEcard⟩ :=
      CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (BarInf L))
    have hpk : p ∣ Nat.card E := by
      rw [hEcard]
      exact dvd_pow_self p (by omega)
    exact hpk.trans (Subgroup.card_dvd_of_le hE)
  exact uc22l3p4_false_of_kf7 hKF7 hpσ hp5 hM hHne hHM hrank hCH f (K := ⊤) hperf hKf hpK

theorem uc22l3p4_mem_normalizer_of_inv {D : Data G} {Ch : Choice2011 G} (hKF7 : KF7Use D)
    (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpσ : p ∈ D.sig) (hp5 : p ≠ 5)
    (hM : IsStronglyPEmbedded p D.M) (hZ : ¬ p ∣ Nat.card (center (Bar2 L))) {d : G}
    (hdB : d ∈ c.B0) (hdp : (orderOf d).Prime) (hd : d ∈ normalizer (L : Set G))
    {K : Subgroup (BarInf L)} (hK : ⁅K, K⁆ = K) (hpK : p ∣ Nat.card K)
    (hfix : ∀ k ∈ K, inducedBarInfAutHom L ⟨d, hd⟩ k = k) {m : G} (hm : m ∈ D.M)
    (hmd : m * d * m⁻¹ = d⁻¹) : m ∈ normalizer (L : Set G) := by
  classical
  by_contra hmN
  set L' : Subgroup G := L.map (MulAut.conj m).toMonoidHom with hL'def
  have hL'mem : L' ∈ calC D.M := by
    rw [hL'def]
    exact UC6S846.calC_map D.M (MulAut.conj m)
      (UC6S846.mem_normalizer_iff_map_conj.1 (le_normalizer hm)) hL
  have hne : L ≠ L' :=
    fun hEq => hmN (UC6S846.mem_normalizer_iff_map_conj.2 (hEq.trans hL'def).symm)
  have hd2 : orderOf d ≠ 2 := by
    intro h2
    have hdvd : orderOf d ∣ Nat.card ↥c.B0 := Subgroup.orderOf_dvd_natCard c.B0 hdB
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.2 (ch214_odd_card c.hpi)) (even_iff_two_dvd.2 hdvd)
  have hdvd : p ∣ Nat.card ↥(L ⊓ centralizer ({d} : Set G)) :=
    hpK.trans (uc22s2112l3p_card_dvd_of_fixes hL.2.2 hd hdp hd2 hK hfix)
  have hm'd : m⁻¹ * d * m = d⁻¹ := by
    have h1 : d = m⁻¹ * d⁻¹ * m := by
      calc d = m⁻¹ * (m * d * m⁻¹) * m := by group
        _ = m⁻¹ * d⁻¹ * m := by rw [hmd]
    calc m⁻¹ * d * m = (m⁻¹ * d⁻¹ * m)⁻¹ := by group
      _ = d⁻¹ := by rw [← h1]
  have hCinv : centralizer ({d⁻¹} : Set G) = centralizer ({d} : Set G) := by
    ext y
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    exact Commute.inv_right_iff
  have hdvd' : p ∣ Nat.card ↥(L' ⊓ centralizer ({d} : Set G)) := by
    rw [hL'def]
    refine dvd_card_conj_calC (L := L) (g := m) (x := d) (q := p) ?_
    rw [hm'd, hCinv]
    exact hdvd
  obtain ⟨hHne, hHM, hCN, hCH⟩ := uc22s2112r2_normalizer hH c hL.1.le hdB hdp
  have h1 : p ∣ Nat.card ↥(L ⊓ (normalizer ((zpowers d : Subgroup G) : Set G) ⊓ D.M)) :=
    hdvd.trans (card_dvd_of_le (le_inf inf_le_left
      (le_inf (inf_le_right.trans hCN) (inf_le_left.trans hL.1.le))))
  have h2 : p ∣ Nat.card ↥(L' ⊓ (normalizer ((zpowers d : Subgroup G) : Set G) ⊓ D.M)) :=
    hdvd'.trans (card_dvd_of_le (le_inf inf_le_left
      (le_inf (inf_le_right.trans hCN) (inf_le_left.trans hL'mem.1.le))))
  have hrank : 2 ≤ Open.pRank p (normalizer ((zpowers d : Subgroup G) : Set G) ⊓ D.M) :=
    two_le_pRank_of_ne_calC hp hp2 hL hL'mem hne hZ
      (C := normalizer ((zpowers d : Subgroup G) : Set G) ⊓ D.M) inf_le_right h1 h2
  let f : ↥(L ⊓ centralizer ({d} : Set G)) →* BarInf L :=
    (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp (Subgroup.inclusion inf_le_left)
  have hfr : f.range = ((centralizer ({d} : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.solvableRadical ↥L)) := by
    rw [show f = (QuotientGroup.mk' (CFSG.solvableRadical ↥L)).comp
        (Subgroup.inclusion inf_le_left) from rfl,
      MonoidHom.range_comp, Subgroup.inclusion_range inf_le_left, Subgroup.inf_subgroupOf_left]
  have hKf : K ≤ f.range := by
    rw [hfr]
    exact uc22s2112l3p_le_map_centralizer hL.2.2 hd hdp hd2 hK hfix
  exact uc22l3p4_false_of_kf7 hKF7 hpσ hp5 hM hHne hHM hrank hCH f hK hKf hpK

theorem uc22l3p4_false (hGA : GriessAllModelsStatement) (hIS : L3InvertSplit) {D : Data G}
    (h149 : R149L3P D) (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (h5 : S21_5 D (Choice214U D)) (hH : H1930 D) (c : Ctx21 D (Choice214U D)) (hn3 : 3 ≤ c.n)
    (hn2 : IsPowTwo c.n) {L : Subgroup G} (hL : L ∈ calC D.M) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hX : LieModel (BarInf L) .PSL 3 p 1 ∨ LieModel (BarInf L) .PSU 3 p 1)
    (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1) : False := by
  classical
  have hZ : ∀ {K : Subgroup G}, K ∈ calC D.M →
      (LieModel (BarInf K) .PSL 3 p 1 ∨ LieModel (BarInf K) .PSU 3 p 1) →
        ¬ p ∣ Nat.card (center (Bar2 K)) := fun hK hXK => by
    rcases hXK with h | h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hK (.inl rfl) hp2 h
    · exact uc22s213_not_dvd_card_center_of_rank_three_odd hGA hK (.inr rfl) hp2 h
  have hpL : ∀ {K : Subgroup G}, K ∈ calC D.M →
      (LieModel (BarInf K) .PSL 3 p 1 ∨ LieModel (BarInf K) .PSU 3 p 1) →
        2 ≤ Open.pRank p K := fun hK hXK => by
    rw [← uc22s213_pRank_barInf_of_prime hK.2.2 hp hp2 (hZ hK hXK)]
    exact CFSG.Quasithin.A3Facts.two_le_pRank_psl_psu_three hp2
      (hXK.imp (·.statedClassicalModel_of_ne_zero (by norm_num))
        (·.statedClassicalModel_of_ne_zero (by norm_num)))
  by_cases hMN : D.M ≤ normalizer (L : Set G)
  · exact uc22s2112l3p_false_of_invertSplit hIS h149 hH c hn3 hn2 hL hp hp2 hX hfaith hMN
  obtain ⟨g, hg, hgN⟩ := SetLike.not_le_iff_exists.1 hMN
  have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
    hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have h4 := uc22s213_four_le_pRank_of_two_conj hL
    (PartOne.Section8.mem_conjSetOf_self D.M L) ⟨g, hg, rfl⟩ hne hp hp2 (hpL hL hX) (hZ hL hX)
  have hpσ := hσ.four_mem p hp hp2 h4
  have hMs := UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have hp5 : p ≠ 5 := by
    rintro rfl
    exact uc22s2112r34_not_mem_sig hσ hH c hL
      ⟨by norm_num, (uc22s2112l3p_three_five_dvd c hn3 hn2).2⟩ hpσ
  obtain ⟨g', hg', hsyl⟩ := uc22l3p4_exists_conj_isSylowOf D L
  have hL' : L.map (MulAut.conj g').toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M _
    (UC6S846.mem_normalizer_iff_map_conj.1 (le_normalizer hg')) hL
  have hX' : LieModel (BarInf (L.map (MulAut.conj g').toMonoidHom)) .PSL 3 p 1 ∨
      LieModel (BarInf (L.map (MulAut.conj g').toMonoidHom)) .PSU 3 p 1 := by
    obtain ⟨e⟩ := uc22p20c_barInf_equiv_map L g'
    exact hX.imp (·.of_mulEquiv e) (·.of_mulEquiv e)
  exact uc22l3p4_false_of_invertSplit hIS h149 hH c hn3 hn2 hL' hp hp2 hX'
    (uc22s2114_B0_le_normalizer h5 hH c hL')
    (fun _ hbB hb h1 => uc22l3p4_eq_one_of_kf7 hKF7 hH c hL' hp hp2 hpσ hp5 hMs (hZ hL' hX')
      (hpL hL' hX') hbB hb h1) hsyl
    (fun _ hdB hdp hd _ hK hpK hfix _ hm hmd => uc22l3p4_mem_normalizer_of_inv hKF7 hH c hL' hp
      hp2 hpσ hp5 hMs (hZ hL' hX') hdB hdp hd hK hpK hfix hm hmd)

theorem uc22l3p4_s21_12aFR34L3PTwo (hGA : GriessAllModelsStatement) (hIS : L3InvertSplit)
    {D : Data G} (h149 : R149L3P D) (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D)
    (h5 : S21_5 D (Choice214U D)) : S21_12aFR34L3PTwo D (Choice214U D) := by
  intro hH c hn3 hn2 L hL p hp hp2 hX _ hfaith
  exact (uc22l3p4_false hGA hIS h149 hσ hKF7 h5 hH c hn3 hn2 hL hp hp2 hX hfaith).elim

end Local


theorem s21_12aFR34L3PTwo_core {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M) :
    S21_12aFR34L3PTwo (UC6.dataOfSetup4 hS hU S) (Choice214U (UC6.dataOfSetup4 hS hU S)) := by
  have hs := setup4S21PreRestFacts_dataOfSetup4 hS hU S hMS hPart
  have hgr := CFSG.HardMathSupport.Foote.FamilyReduction.griessAllModelsStatement
  have hSE : StronglyEmbeddedFive := PartOne.Section7.SEFive.stronglyEmbeddedFive_holds
  have hB3 : BadNoStrongThree := PartOne.Section7.badNoStrongThree_holds
  have hG3 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.gls3StronglyThreeEmbeddedPlus_holds
  have hK3 : StronglyEmbeddedThree :=
    PartOne.Section7.StronglyEmbeddedThree_of_KIB hG3 CFSG.AGLEmbedding.kFactCatalogSchreier_holds
      (PartOne.Section7.StronglyEmbeddedThreeKIB_of_small hG3 PartOne.Section7.KIB3Small_holds)
  have hCh : ∀ L₀ B₀ : Subgroup G, Choice214U (UC6.dataOfSetup4 hS hU S) L₀ B₀ → True :=
    fun _ _ _ => trivial
  exact uc22l3p4_s21_12aFR34L3PTwo hgr (l3InvertSplit_of_frames l3FrameExists_psl l3FrameExists_psu
      l3ThreeNoFive_holds)
    (uc22s2112l3p_r149_setup4 hgr UCK.k35w_holds PartOne.Section8.stronglyEmbeddedCentralFree_holds
      hS hU S hMS hPart hSE hK3 hB3 CFSG.LocalAnalysis.RankThreeTheoremC.kFactOutCyclic_holds)
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hs.kf7 (fun hH c => hs.s21_5 hH (c.mono hCh))

end CFSG.LocalAnalysis.UniquenessCase.UC22
