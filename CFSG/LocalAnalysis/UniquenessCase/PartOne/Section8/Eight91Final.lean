module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91OrderArithmetic
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91CongruenceSupport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialTransport
import CFSG.LocalAnalysis.GH72.Sec5Tools
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Cover
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL2Main
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups (IsExtraspecialExpP)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem r891f_mem_of_conj_mem {p : ℕ} {M : Subgroup G} (hM : IsStronglyPEmbedded p M)
    {t y : G}
    (ht : t ∈ M) (hto : orderOf t = p) (hy : y * t * y⁻¹ ∈ M) : y ∈ M := by
  by_contra hyM
  apply hM.2.2 y hyM
  have hmem : y * t * y⁻¹ ∈ M ⊓ M.map (MulAut.conj y).toMonoidHom :=
    ⟨hy, ⟨t, ht, by simp [MulAut.conj_apply]⟩⟩
  have h := Subgroup.orderOf_dvd_natCard _ hmem
  have hord : orderOf (y * t * y⁻¹) = orderOf t := by
    have := orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective t
    simpa [MulAut.conj_apply] using this
  rwa [hord, hto] at h

omit [Finite G] in
private theorem r891f_comm_of_mem_centralizer {Z : Subgroup G} {h z : G}
    (hh : h ∈ centralizer (Z : Set G))
    (hz : z ∈ Z) : h * z = z * h :=
  ((Subgroup.mem_centralizer_iff.mp hh) z hz).symm

omit [Finite G] in
private theorem r891f_normal_subgroupOf_centralizer (Z : Subgroup G) :
    (Z.subgroupOf (centralizer (Z : Set G))).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : G) ∈ Z := Subgroup.mem_subgroupOf.mp hn
  have hcomm : (g : G) * n * (g : G)⁻¹ = n := by
    rw [r891f_comm_of_mem_centralizer g.2 hn', mul_inv_cancel_right]
  rw [Subgroup.mem_subgroupOf]
  simpa [hcomm] using hn'

private theorem r891f_Y_le_pre {H Z : Subgroup G} (Ys : Subgroup (R891Star H Z)) :
    R891Y H Z Ys ≤ (Ys.comap (QuotientGroup.mk' (R891Ker H Z))).map H.subtype := by
  unfold R891Y DerInf8
  exact Subgroup.map_subtype_le _

private theorem r891f_Y_le_H {H Z : Subgroup G} (Ys : Subgroup (R891Star H Z)) : R891Y H Z Ys ≤ H :=
  (r891f_Y_le_pre Ys).trans (Subgroup.map_subtype_le _)

private theorem r891f_mk_mem_of_mem_Y {H Z : Subgroup G} {Ys : Subgroup (R891Star H Z)} {y : G}
    (hy : y ∈ R891Y H Z Ys) :
    QuotientGroup.mk' (R891Ker H Z) ⟨y, r891f_Y_le_H Ys hy⟩ ∈ Ys := by
  obtain ⟨h, hh, rfl⟩ := r891f_Y_le_pre Ys hy
  exact hh

private theorem r891f_ker_le_sup (Z : Subgroup G) :
    R891Ker (centralizer (Z : Set G)) Z ≤
      CFSG.pPrimeCore 3 ↥(centralizer (Z : Set G)) ⊔ Z.subgroupOf (centralizer (Z : Set G)) := by
  have : (CFSG.pPrimeCore 3 ↥(centralizer (Z : Set G))).Normal := CFSG.pPrimeCore_normal
  have := r891f_normal_subgroupOf_centralizer Z
  refine Subgroup.normalClosure_le_normal ?_
  rintro x (hx | hx)
  · exact Subgroup.mem_sup_left hx
  · exact Subgroup.mem_sup_right hx

private theorem r891f_exists_mul_of_mem_ker {Z : Subgroup G} {x : G}
    (hx : x ∈ centralizer (Z : Set G))
    (h1 : QuotientGroup.mk' (R891Ker (centralizer (Z : Set G)) Z) ⟨x, hx⟩ = 1) :
    ∃ a ∈ (CFSG.pPrimeCore 3 ↥(centralizer (Z : Set G))).map (centralizer (Z : Set G)).subtype,
      ∃ z ∈ Z, a * z = x := by
  have := r891f_normal_subgroupOf_centralizer Z
  have hk : (⟨x, hx⟩ : ↥(centralizer (Z : Set G))) ∈
      CFSG.pPrimeCore 3 ↥(centralizer (Z : Set G)) ⊔ Z.subgroupOf (centralizer (Z : Set G)) :=
    r891f_ker_le_sup Z ((QuotientGroup.eq_one_iff _).mp h1)
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hk
  obtain ⟨a, ha, z, hz, haz⟩ := hk
  refine ⟨a, ⟨a, ha, rfl⟩, z, (Subgroup.mem_subgroupOf).mp hz, ?_⟩
  exact congrArg Subtype.val haz

private theorem r891f_mem_pPrimeCore_of_mem {H Y : Subgroup G} (hYH : Y ≤ H) {a : G} (haY : a ∈ Y)
    (haO : a ∈ (CFSG.pPrimeCore 3 ↥H).map H.subtype) :
    a ∈ (CFSG.pPrimeCore 3 ↥Y).map Y.subtype := by
  set K := (CFSG.pPrimeCore 3 ↥H).map H.subtype
  have hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    rintro h hh _ ⟨k, hk, rfl⟩
    refine ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    exact (CFSG.pPrimeCore_normal (p := 3) (G := ↥H)).conj_mem k hk ⟨h, hh⟩
  have hW : (K.subgroupOf Y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hKn g (hYH g.2) n hn
  have hWc : Nat.Coprime 3 (Nat.card (K.subgroupOf Y)) := by
    have h1 : Nat.card (K.subgroupOf Y) ∣ Nat.card K :=
      Subgroup.card_comap_dvd_of_injective K Y.subtype Y.subtype_injective
    have h2 : Nat.card K = Nat.card (CFSG.pPrimeCore 3 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    exact Nat.Coprime.coprime_dvd_right h1 (h2 ▸ CFSG.pPrimeCore_coprime_card)
  have hle : K.subgroupOf Y ≤ CFSG.pPrimeCore 3 ↥Y := le_sSup ⟨hW, hWc⟩
  exact ⟨⟨a, haY⟩, hle (Subgroup.mem_subgroupOf.mpr haO), rfl⟩

omit [Finite G] in
private theorem r891f_derInf8_normal (X : Subgroup G) : ((DerInf8 X).subgroupOf X).Normal := by
  unfold DerInf8
  rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
  exact Subgroup.normal_iInf_normal fun n => derivedSeries_normal _ n

private theorem r891f_pPrimeCore_Y_le {H Z : Subgroup G} {Ys : Subgroup (R891Star H Z)}
    (hc : IsComponentOf Ys ⊤) :
    (CFSG.pPrimeCore 3 ↥(R891Y H Z Ys)).map (R891Y H Z Ys).subtype ≤
      (CFSG.pPrimeCore 3 ↥H).map H.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y₁ : Subgroup ↥H := Ys.comap (QuotientGroup.mk' (R891Ker H Z)) with hY₁
  have h1 : CFSG.Open.IsSubnormal Y₁ ⊤ := by
    have := hc.2.1.comap (QuotientGroup.mk' (R891Ker H Z))
    rwa [Subgroup.comap_top] at this
  have h2 : CFSG.Open.IsSubnormal (Y₁.map H.subtype) H := by
    have := h1.map H.subtype
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have hYle : R891Y H Z Ys ≤ Y₁.map H.subtype := r891f_Y_le_pre Ys
  have hYn : ((R891Y H Z Ys).subgroupOf (Y₁.map H.subtype)).Normal := r891f_derInf8_normal _
  have h3 : CFSG.Open.IsSubnormal (R891Y H Z Ys) H :=
    (CFSG.Open.IsSubnormal.step hYle hYn (CFSG.Open.IsSubnormal.refl _)).trans h2
  have h5 := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal (X := ↥H) 3 h3.subgroupOf
  let e : ↥((R891Y H Z Ys).subgroupOf H) ≃* ↥(R891Y H Z Ys) :=
    Subgroup.subgroupOfEquivOfLe (r891f_Y_le_H Ys)
  have h6 : (CFSG.pPrimeCore 3 ↥(R891Y H Z Ys)).map (R891Y H Z Ys).subtype =
      (CFSG.GH74.GLS.pPrimeCoreOf 3 ((R891Y H Z Ys).subgroupOf H)).map H.subtype := by
    unfold CFSG.GH74.GLS.pPrimeCoreOf
    rw [Subgroup.map_map, ← CFSG.pPrimeCore_map_iso 3 e, Subgroup.map_map]
    rfl
  rw [h6]
  exact Subgroup.map_mono h5

private noncomputable def r891f_barOf (Y P : Subgroup G) : Subgroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
  (P.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))

private theorem r891f_nonempty_barOf_equiv {Y P : Subgroup G} (hPY : P ≤ Y) (hP : IsPGroup 3 P) :
    Nonempty (↥(r891f_barOf Y P) ≃* ↥P) := by
  have hinj : ∀ x ∈ P.subgroupOf Y, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) x = 1 → x = 1 := by
    intro x hx h1
    have hxO : x ∈ CFSG.pPrimeCore 3 ↥Y := (QuotientGroup.eq_one_iff x).mp h1
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    have ho1 : orderOf x ∣ Nat.card (CFSG.pPrimeCore 3 ↥Y) := Subgroup.orderOf_dvd_natCard _ hxO
    obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
    have ho2 : orderOf x ∣ 3 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have hcop : Nat.Coprime (3 ^ k) (Nat.card (CFSG.pPrimeCore 3 ↥Y)) :=
      Nat.Coprime.pow_left k CFSG.pPrimeCore_coprime_card
    exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left ho2 hcop).eq_one_of_dvd ho1)
  obtain ⟨e, -⟩ := K328.exists_mulEquiv_map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) hinj
  exact ⟨e.symm.trans (Subgroup.subgroupOfEquivOfLe hPY)⟩

private theorem r891f_card_barOf {Y P : Subgroup G} (hPY : P ≤ Y) (hP : IsPGroup 3 P) :
    Nat.card (r891f_barOf Y P) = Nat.card P := by
  obtain ⟨e⟩ := r891f_nonempty_barOf_equiv hPY hP
  exact Nat.card_congr e.toEquiv

omit [Finite G] in
private theorem r891f_barOf_mono {Y P Q : Subgroup G} (hPQ : P ≤ Q) :
    r891f_barOf Y P ≤ r891f_barOf Y Q := by
  apply Subgroup.map_mono
  intro x hx
  exact Subgroup.mem_subgroupOf.mpr (hPQ (Subgroup.mem_subgroupOf.mp hx))

private theorem r891f_center_eq_barOf {Z : Subgroup G}
    {Ys : Subgroup (R891Star (centralizer (Z : Set G)) Z)}
    (hZY : Z ≤ R891Y (centralizer (Z : Set G)) Z Ys) (hZ3 : Nat.card Z = 3)
    (hc3 : Nat.card (center (R891Ybar (centralizer (Z : Set G)) Z Ys)) = 3) :
    center (R891Ybar (centralizer (Z : Set G)) Z Ys) =
      r891f_barOf (R891Y (centralizer (Z : Set G)) Z Ys) Z := by
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [hZ3, pow_one])
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H y =>
      have hyz : y * z = z * y := Subtype.ext
        (r891f_comm_of_mem_centralizer (r891f_Y_le_H Ys y.2) (Subgroup.mem_subgroupOf.mp hz))
      simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, hyz]
  · rw [hc3, r891f_card_barOf hZY hZp, hZ3]

private theorem r891f_mem_M_of_mem_center {D : Data G} {L S R : Subgroup G} (hS : S ≤ D.M)
    (hgam : R891Gamma895 D L S R) {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hc : IsComponentOf Ys ⊤)
    (hcen : center (R891Ybar (R891H L S) (R891Z L S) Ys) =
      r891f_barOf (R891Y (R891H L S) (R891Z L S) Ys) (R891Z L S))
    (y : ↥(R891Y (R891H L S) (R891Z L S) Ys))
    (hy : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys)) y ∈
      center (R891Ybar (R891H L S) (R891Z L S) Ys)) : (y : G) ∈ D.M := by
  rw [hcen] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  have hzy' : z⁻¹ * y ∈ CFSG.pPrimeCore 3 ↥(R891Y (R891H L S) (R891Z L S) Ys) :=
    QuotientGroup.eq.mp hzy
  have hO : ((z⁻¹ * y : ↥(R891Y (R891H L S) (R891Z L S) Ys)) : G) ∈ D.M :=
    hgam.2.2 (r891f_pPrimeCore_Y_le hc ⟨_, hzy', rfl⟩)
  have hzZ : (z : G) ∈ R891Z L S := Subgroup.mem_subgroupOf.mp hz
  have hzM : (z : G) ∈ D.M := by
    unfold R891Z ZOf at hzZ
    exact hS hzZ.1.1
  have : (y : G) = (z : G) * ((z⁻¹ * y : ↥(R891Y (R891H L S) (R891Z L S) Ys)) : G) := by
    simp
  rw [this]
  exact D.M.mul_mem hzM hO

private theorem r891f_mem_normalizer_of_comm {L : Subgroup G} {x : G}
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L) : x ∈ normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨l, hl, rfl⟩
    have h : x * l * x⁻¹ = (x * l * x⁻¹ * l⁻¹) * l := by group
    have h2 : x * l * x⁻¹ ∈ L := by
      rw [h]
      exact L.mul_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 L (hx l hl)) hl
    simpa [MulAut.conj_apply] using h2
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

private theorem r891f_mem_centOverO2 {X L : Subgroup G} {x : G} (hx : x ∈ CentOverO2 X L) :
    x ∈ X ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  unfold CentOverO2 at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy
  | one => exact ⟨X.one_mem, fun l _ => by simp⟩
  | mul a b _ _ ha hb =>
    refine ⟨X.mul_mem ha.1 hb.1, fun l hl => ?_⟩
    have hbl : b * l * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (r891f_mem_normalizer_of_comm hb.2) l).mp hl
    have e : a * b * l * (a * b)⁻¹ * l⁻¹ =
        (a * (b * l * b⁻¹) * a⁻¹ * (b * l * b⁻¹)⁻¹) * (b * l * b⁻¹ * l⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 L).mul_mem (ha.2 _ hbl) (hb.2 l hl)
  | inv a _ ha =>
    refine ⟨X.inv_mem ha.1, fun l hl => ?_⟩
    have hal : a⁻¹ * l * a ∈ L :=
      (Subgroup.mem_normalizer_iff''.mp (r891f_mem_normalizer_of_comm ha.2) l).mp hl
    have h1 := ha.2 _ hal
    have e : a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ = (a * (a⁻¹ * l * a) * a⁻¹ * (a⁻¹ * l * a)⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 L).inv_mem h1

private theorem r891f_exists_centralizing {D : Data G} {L S R A : Subgroup G} {n p : ℕ}
    (hst : R891State D L S R A n) (hp : p ∈ D.sig) (hp3 : p ≠ 3) :
    ∃ t ∈ D.M, orderOf t = p ∧ ∀ r ∈ R, t * r = r * t := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrk : CFSG.Open.pRank p (CentOverO2 D.M L) = 1 := (hst.f893.rank p hp).2
  obtain ⟨t₀, ht₀C, ht₀o⟩ := CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank hpp hrk.ge
  obtain ⟨ht₀M, ht₀L⟩ := r891f_mem_centOverO2 ht₀C
  set O := pCoreOf 2 L with hO
  have hRL : R ≤ L := hst.ctx.xShape.rSylow.trans inf_le_right
  have hOL : O ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hLM : L ≤ D.M := hst.set.mem.1.le
  have hRnO : R ≤ normalizer (O : Set G) :=
    hRL.trans (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hRc : Nat.card R = 3 ^ 3 := by
    have h := hst.ctx.xShape.rExtra
    unfold IsExtraspecialExpP at h
    simpa using h.1
  have hRp : IsPGroup 3 R := IsPGroup.of_card hRc
  have hOp : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hpO : ¬ p ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hOp
    rw [hk]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp (hpp.dvd_of_dvd_pow h))
  have hpR : ¬ p ∣ Nat.card R := by
    rw [hRc]
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp (hpp.dvd_of_dvd_pow h))
  have hOR : Disjoint O R := IsPGroup.disjoint_of_ne 2 3 (by norm_num) O R hOp hRp
  have hcardB : Nat.card (O ⊔ R : Subgroup G) = Nat.card O * Nat.card R :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O R hRnO hOR
  have hB : ¬ p ∣ Nat.card (O ⊔ R : Subgroup G) := by
    rw [hcardB]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).mp h with h | h
    · exact hpO h
    · exact hpR h
  have ht₀B : t₀ ∈ normalizer ((O ⊔ R : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.map_sup, sup_le_iff]
      constructor
      · rintro _ ⟨u, hu, rfl⟩
        have h1 := ht₀L u (hOL hu)
        have h2 : t₀ * u * t₀⁻¹ ∈ O ⊔ R := by
          have : t₀ * u * t₀⁻¹ = (t₀ * u * t₀⁻¹ * u⁻¹) * u := by group
          rw [this]
          exact Subgroup.mem_sup_left (O.mul_mem h1 hu)
        simpa [MulAut.conj_apply] using h2
      · rintro _ ⟨r, hr, rfl⟩
        have h1 := ht₀L r (hRL hr)
        have h2 : t₀ * r * t₀⁻¹ ∈ O ⊔ R := by
          have : t₀ * r * t₀⁻¹ = (t₀ * r * t₀⁻¹ * r⁻¹) * r := by group
          rw [this]
          exact (O ⊔ R).mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hr)
        simpa [MulAut.conj_apply] using h2
    · rw [Subgroup.card_map_of_injective (MulAut.conj t₀).injective]
  have hA : IsPGroup p (Subgroup.zpowers t₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht₀o, pow_one])
  obtain ⟨R₁, hR₁, hR₁n⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime hpp
    Nat.prime_three hA ((Subgroup.zpowers_le).mpr ht₀B) hB
  have hRsyl : IsSylowOf 3 R (O ⊔ R) := by
    refine CFSG.GH74.GLS.Stage2.Signalizer.Odd87.isSylowOf_of_card_eq le_sup_right hRp
      (m := Nat.card O) (by rw [hcardB, mul_comm]) ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hOp
    rw [hk]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    norm_num at this
  obtain ⟨b, hbB, hbR⟩ := CFSG.GH72.exists_map_conj_eq_of_isSylowOf hRsyl hR₁
  have hR₁O : R₁ ⊓ O = ⊥ :=
    IsPGroup.disjoint_of_ne 3 2 (by norm_num) R₁ O hR₁.isPGroup hOp |>.eq_bot
  have hcR₁ : ∀ r ∈ R₁, t₀ * r = r * t₀ := by
    intro r hr
    have hrL : r ∈ L := sup_le hOL hRL (hR₁.le hr)
    have h1 : t₀ * r * t₀⁻¹ * r⁻¹ ∈ O := ht₀L r hrL
    have hnR₁ : t₀ ∈ normalizer (R₁ : Set G) := hR₁n (Subgroup.mem_zpowers t₀)
    have h2 : t₀ * r * t₀⁻¹ * r⁻¹ ∈ R₁ :=
      R₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hnR₁ r).mp hr) (R₁.inv_mem hr)
    have h3 : t₀ * r * t₀⁻¹ * r⁻¹ = 1 := by
      have : t₀ * r * t₀⁻¹ * r⁻¹ ∈ R₁ ⊓ O := ⟨h2, h1⟩
      rwa [hR₁O, Subgroup.mem_bot] at this
    calc t₀ * r = (t₀ * r * t₀⁻¹ * r⁻¹) * (r * t₀) := by group
      _ = r * t₀ := by rw [h3, one_mul]
  have hbM : b ∈ D.M := hLM (sup_le hOL hRL hbB)
  refine ⟨b⁻¹ * t₀ * b, D.M.mul_mem (D.M.mul_mem (D.M.inv_mem hbM) ht₀M) hbM, ?_, ?_⟩
  · rw [← ht₀o]
    exact (SemiconjBy.orderOf_eq b⁻¹ (x := t₀) (y := b⁻¹ * t₀ * b) (by
      simp only [SemiconjBy]; group)).symm
  · intro r hr
    have hr₁ : b * r * b⁻¹ ∈ R₁ := by
      rw [← hbR]
      exact ⟨r, hr, by simp [MulAut.conj_apply]⟩
    have := hcR₁ _ hr₁
    calc b⁻¹ * t₀ * b * r = b⁻¹ * (t₀ * (b * r * b⁻¹)) * b := by group
      _ = b⁻¹ * ((b * r * b⁻¹) * t₀) * b := by rw [this]
      _ = r * (b⁻¹ * t₀ * b) := by group

private theorem r891f_derInf8_map_conj (X : Subgroup G) (g : G) :
    DerInf8 (X.map (MulAut.conj g).toMonoidHom) =
      (DerInf8 X).map (MulAut.conj g).toMonoidHom := by
  have h := CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
    (MulAut.conj g).toMonoidHom X
  simpa only [DerInf8, CFSG.perfectResidual] using h.symm

private theorem r891f_isComponentOf_map_mulAut {Q : Type} [Group Q] (α : MulAut Q)
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) : IsComponentOf (K.map α.toMonoidHom) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · have h := hK.2.1.map α.toMonoidHom
    rwa [Subgroup.map_top_of_surjective _ α.surjective] at h
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (K.equivMapOfInjective α.toMonoidHom α.injective).symm hK.2.2

private theorem r891f_comm_of_not_mem_normalizer {Q : Type} [Group Q] [Finite Q] {K : Subgroup Q}
    (hK : IsComponentOf K ⊤) {c x : Q} (hxK : x ∈ K) (hcx : c * x * c⁻¹ = x)
    (hc : c ∉ normalizer (K : Set Q)) : ∀ y ∈ K, x * y = y * x := by
  have hK' : IsComponentOf (K.map (MulAut.conj c).toMonoidHom) ⊤ :=
    r891f_isComponentOf_map_mulAut _ hK
  have hne : K ≠ K.map (MulAut.conj c).toMonoidHom := fun h =>
    hc (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hbot := (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hK hK').resolve_left
    hne
  have hx' : x ∈ K.map (MulAut.conj c).toMonoidHom :=
    ⟨x, hxK, by simp [MulAut.conj_apply, hcx]⟩
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hy) x hx')

private theorem r891f_mem_normalizer_Y {Z R : Subgroup G}
    {Ys : Subgroup (R891Star (centralizer (Z : Set G)) Z)} (hc : IsComponentOf Ys ⊤)
    (hRY : R ≤ R891Y (centralizer (Z : Set G)) Z Ys)
    (hRY' : ⁅R891Img (centralizer (Z : Set G)) Z R, Ys⁆ ≠ ⊥)
    {t : G} (htH : t ∈ centralizer (Z : Set G)) (htR : ∀ r ∈ R, t * r = r * t) :
    t ∈ normalizer ((R891Y (centralizer (Z : Set G)) Z Ys : Subgroup G) : Set G) := by
  let th : ↥(centralizer (Z : Set G)) := ⟨t, htH⟩
  let π := QuotientGroup.mk' (R891Ker (centralizer (Z : Set G)) Z)
  have hRs : R891Img (centralizer (Z : Set G)) Z R ≤ Ys := by
    rintro _ ⟨h, hh, rfl⟩
    exact r891f_mk_mem_of_mem_Y (hRY (Subgroup.mem_subgroupOf.mp hh))
  have hfix : ∀ x ∈ R891Img (centralizer (Z : Set G)) Z R, π th * x * (π th)⁻¹ = x := by
    rintro _ ⟨h, hh, rfl⟩
    have hcomm : th * h * th⁻¹ = h := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, th]
      rw [htR _ (Subgroup.mem_subgroupOf.mp hh), mul_inv_cancel_right])
    rw [← map_inv, ← map_mul, ← map_mul, hcomm]
  have hts : π th ∈ normalizer (Ys : Set (R891Star (centralizer (Z : Set G)) Z)) := by
    by_contra hn
    apply hRY'
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (r891f_comm_of_not_mem_normalizer hc (hRs hx) (hfix x hx) hn y hy).symm
  have htY₁ : t ∈ normalizer (((Ys.comap π).map (centralizer (Z : Set G)).subtype :
      Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨h, hh, rfl⟩
      refine ⟨th * h * th⁻¹, ?_, rfl⟩
      have hh' : π h ∈ Ys := hh
      show π (th * h * th⁻¹) ∈ Ys
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hts _).mp hh'
    · rintro ⟨h, hh, hhy⟩
      refine ⟨th⁻¹ * h * th, ?_, ?_⟩
      · have hh' : π h ∈ Ys := hh
        show π (th⁻¹ * h * th) ∈ Ys
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff''.mp hts _).mp hh'
      · have hhy' : (h : G) = t * y * t⁻¹ := hhy
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, th, hhy']
        group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at htY₁ ⊢
  rw [← MulEquiv.toMonoidHom_eq_coe] at htY₁ ⊢
  unfold R891Y
  rw [← r891f_derInf8_map_conj, htY₁]

private def r891f_conjAut {Y : Subgroup G} {t : G} (ht : t ∈ normalizer (Y : Set G)) :
    ↥Y ≃* ↥Y where
  toFun y := ⟨t * y * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht y).mp y.2⟩
  invFun y := ⟨t⁻¹ * y * t, (Subgroup.mem_normalizer_iff''.mp ht y).mp y.2⟩
  left_inv y := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

omit [Finite G] in
@[simp] private theorem r891f_coe_conjAut {Y : Subgroup G} {t : G}
    (ht : t ∈ normalizer (Y : Set G)) (y : ↥Y) :
    ((r891f_conjAut ht y : ↥Y) : G) = t * y * t⁻¹ := rfl

private noncomputable def r891f_barAut {Y : Subgroup G} {t : G} (ht : t ∈ normalizer (Y : Set G)) :
    MulAut ((↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) :=
  QuotientGroup.congr _ _
    (QuotientGroup.congr _ _ (r891f_conjAut ht) (by
      have h := CFSG.pPrimeCore_map_iso 3 (r891f_conjAut ht)
      rwa [MulEquiv.toMonoidHom_eq_coe] at h))
    (Subgroup.map_center_eq _)

omit [Finite G] in
private theorem r891f_barAut_mk {Y : Subgroup G} {t : G} (ht : t ∈ normalizer (Y : Set G))
    (y : ↥Y) :
    r891f_barAut ht ((y : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :
      (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) =
      ((r891f_conjAut ht y : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :
        (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) := by
  rw [r891f_barAut, QuotientGroup.congr_mk, QuotientGroup.congr_mk]

omit [Finite G] in
private theorem r891f_barAut_pow_mk {Y : Subgroup G} {t : G} (ht : t ∈ normalizer (Y : Set G))
    (k : ℕ)
    (y : ↥Y) :
    (r891f_barAut ht ^ k) ((y : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :
      (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) =
      ((r891f_conjAut (Subgroup.pow_mem _ ht k) y : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :
        (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)) := by
  induction k with
  | zero =>
    have : r891f_conjAut (Subgroup.pow_mem _ ht 0) y = y := Subtype.ext (by simp)
    rw [this, pow_zero, MulAut.one_apply]
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, r891f_barAut_mk]
    have : r891f_conjAut ht (r891f_conjAut (Subgroup.pow_mem _ ht k) y) =
        r891f_conjAut (Subgroup.pow_mem _ ht (k + 1)) y :=
      Subtype.ext (by simp only [r891f_coe_conjAut]; rw [pow_succ']; group)
    rw [this]

omit [Finite G] in
private theorem r891f_barAut_pow_eq_one {Y : Subgroup G} {t : G}
    (ht : t ∈ normalizer (Y : Set G)) {k : ℕ}
    (hk : t ^ k = 1) : r891f_barAut ht ^ k = 1 := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    induction x using QuotientGroup.induction_on with
    | H y =>
      rw [r891f_barAut_pow_mk, MulAut.one_apply]
      have : r891f_conjAut (Subgroup.pow_mem _ ht k) y = y := Subtype.ext (by simp [hk])
      rw [this]

private theorem r891f_eq_seven_of_cong_one {p : ℕ} (hp : p.Prime)
    (h : ((2 : ℤ) ^ (3 * 1) ≡ -R891Pi 1 [ZMOD p]) ∧ ¬ ((2 : ℤ) ^ 1 ≡ -R891Pi 1 [ZMOD p])) :
    p = 7 := by
  have h1 : (1 : ℤ) ≡ 8 [ZMOD p] := by
    have := h.1.symm
    simpa [R891Pi] using this
  have h2 : (p : ℤ) ∣ 7 := by
    have := Int.ModEq.dvd h1
    norm_num at this
    exact this
  have h3 : p ∣ 7 := by exact_mod_cast h2
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h3 with h4 | h4
  · exact absurd h4 hp.one_lt.ne'
  · exact h4

private theorem r891f_mem_center_of_comm_mem_center {Q : Type} [Group Q]
    (hperf : Group.IsPerfect Q) {a : Q}
    (h : ∀ b : Q, a * b * a⁻¹ * b⁻¹ ∈ center Q) : a ∈ center Q := by
  have hmem : (a : Q ⧸ center Q) ∈ center (Q ⧸ center Q) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      have hc : a * b⁻¹ * a⁻¹ * b ∈ center Q := by simpa using h b⁻¹
      have hc' : (a * b⁻¹ * a⁻¹ * b)⁻¹ ∈ center Q := (center Q).inv_mem hc
      have e1 : (a * b⁻¹ * a⁻¹ * b)⁻¹ = b⁻¹ * a * b * a⁻¹ := by group
      rw [e1] at hc'
      have e2 : (b * a)⁻¹ * (a * b) = a⁻¹ * (b⁻¹ * a * b * a⁻¹) * a := by group
      rw [e2, (Subgroup.mem_center_iff.mp hc') a⁻¹, mul_assoc, inv_mul_cancel, mul_one]
      exact hc'
  rw [Group.IsPerfect.center_quotient_center_eq_bot Q, Subgroup.mem_bot,
    QuotientGroup.eq_one_iff] at hmem
  exact hmem

private theorem r891f_rNotCent_of_card {Z R : Subgroup G}
    {Ys : Subgroup (R891Star (centralizer (Z : Set G)) Z)}
    (hRY : R ≤ R891Y (centralizer (Z : Set G)) Z Ys)
    (hZY : Z ≤ R891Y (centralizer (Z : Set G)) Z Ys)
    (hR : Nat.card R = 27)
    (hperf : Group.IsPerfect (R891Ybar (centralizer (Z : Set G)) Z Ys))
    (hc3 : Nat.card (center (R891Ybar (centralizer (Z : Set G)) Z Ys)) = 3) :
    ⁅R891Img (centralizer (Z : Set G)) Z R, Ys⁆ ≠ ⊥ := by
  intro hbot
  set Y := R891Y (centralizer (Z : Set G)) Z Ys with hYdef
  have hYH : Y ≤ centralizer (Z : Set G) := r891f_Y_le_H Ys
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by rw [hR]; norm_num)
  have hcen : r891f_barOf Y R ≤ center (R891Ybar (centralizer (Z : Set G)) Z Ys) := by
    rintro _ ⟨r, hr, rfl⟩
    have hrR : (r : G) ∈ R := Subgroup.mem_subgroupOf.mp hr
    apply r891f_mem_center_of_comm_mem_center hperf
    intro b
    induction b using QuotientGroup.induction_on with
    | H y =>
      have hrs : QuotientGroup.mk' (R891Ker (centralizer (Z : Set G)) Z) ⟨r, hYH r.2⟩ ∈
          R891Img (centralizer (Z : Set G)) Z R :=
        ⟨⟨r, hYH r.2⟩, Subgroup.mem_subgroupOf.mpr hrR, rfl⟩
      have hys := r891f_mk_mem_of_mem_Y (H := centralizer (Z : Set G)) (Z := Z) (Ys := Ys) y.2
      have hcomm := (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot) hrs)) _ hys
      set ry : ↥(centralizer (Z : Set G)) := ⟨r * y * r⁻¹ * y⁻¹,
        (centralizer (Z : Set G)).mul_mem ((centralizer (Z : Set G)).mul_mem
          ((centralizer (Z : Set G)).mul_mem (hYH r.2) (hYH y.2))
          ((centralizer (Z : Set G)).inv_mem (hYH r.2)))
          ((centralizer (Z : Set G)).inv_mem (hYH y.2))⟩
        with hry
      have h1 : QuotientGroup.mk' (R891Ker (centralizer (Z : Set G)) Z) ry = 1 := by
        have : ry = ⟨r, hYH r.2⟩ * ⟨y, hYH y.2⟩ * (⟨r, hYH r.2⟩)⁻¹ * (⟨y, hYH y.2⟩)⁻¹ := rfl
        rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
        group
      obtain ⟨a, haO, z, hz, haz⟩ := r891f_exists_mul_of_mem_ker _ h1
      have hzY : z ∈ Y := hZY hz
      have haY : a ∈ Y := by
        have : a = (r * y * r⁻¹ * y⁻¹) * z⁻¹ := by rw [← haz]; group
        rw [this]
        exact Y.mul_mem (Y.mul_mem (Y.mul_mem (Y.mul_mem r.2 y.2) (Y.inv_mem r.2))
          (Y.inv_mem y.2)) (Y.inv_mem hzY)
      have haO' := r891f_mem_pPrimeCore_of_mem hYH haY haO
      obtain ⟨a', ha'O, ha'⟩ := haO'
      have ha'' : (a' : G) = a := ha'
      have hrz : (r * y * r⁻¹ * y⁻¹ : ↥Y) = a' * ⟨z, hzY⟩ := by
        apply Subtype.ext
        have h1 : ((a' * ⟨z, hzY⟩ : ↥Y) : G) = a * z := by
          rw [Subgroup.coe_mul, ha'']
        rw [h1, haz]
        simp
      have hmk : ((r : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) * (y : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) *
          (r : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)⁻¹ * (y : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y)⁻¹) =
          ((⟨z, hzY⟩ : ↥Y) : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hrz, QuotientGroup.mk_mul,
          (QuotientGroup.eq_one_iff a').mpr ha'O, one_mul]
      simp only [QuotientGroup.mk'_apply]
      rw [hmk, Subgroup.mem_center_iff]
      intro w
      induction w using QuotientGroup.induction_on with
      | H w =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (r891f_comm_of_mem_centralizer (hYH w.2) hz)
  have h := Subgroup.card_le_of_le hcen
  rw [r891f_card_barOf hRY hRp, hR, hc3] at h
  norm_num at h

theorem r891_final_core {D : Data G} (hSg : SigmaStd D) (hSeven : R891SevenCore)
    {L S R A : Subgroup G} {n : ℕ} (hst : R891State D L S R A n) (hgam : R891Gamma895 D L S R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys)
    (h897 : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys))
    (hAut : ∀ p ∈ D.sig, p ≠ 7 → ∀ φ : MulAut (R891Ybar (R891H L S) (R891Z L S) Ys ⧸
      center (R891Ybar (R891H L S) (R891Z L S) Ys)), φ ^ p = 1 → φ = 1) :
    False := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, -⟩ := D.sig_prime p hp
  have hns := CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hst.set.mem
  have hsp := CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns hp
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact hst.set.notStrong hsp
  obtain ⟨t, htM, hto, htR⟩ := r891f_exists_centralizing hst hp hp3
  have hZR : R891Z L S ≤ R := hst.ctx.xShape.zLe
  have htH : t ∈ R891H L S := Subgroup.mem_centralizer_iff.mpr fun z hz => (htR z (hZR hz)).symm
  have hc3 : Nat.card (center (R891Ybar (R891H L S) (R891Z L S) Ys)) = 3 := by
    rcases h897 with h | h | h
    · exact h.2.1
    · exact h.2.1
    · exact h.2.1
  have hperf : Group.IsPerfect (R891Ybar (R891H L S) (R891Z L S) Ys) := by
    rcases h897 with h | h | h
    · exact h.1.1
    · exact ⟨h.1.1⟩
    · exact ⟨h.1.1⟩
  have hRc : Nat.card R = 27 := by
    have h := hst.ctx.xShape.rExtra
    unfold IsExtraspecialExpP at h
    simpa using h.1
  have htN := r891f_mem_normalizer_Y hY.comp hY.rLe
    (r891f_rNotCent_of_card hY.rLe hY.zLe hRc hperf hc3) htH htR
  have hcen := r891f_center_eq_barOf hY.zLe hst.basic.zOrder hc3
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 3) (by rw [hRc]; norm_num)
  obtain ⟨eR⟩ := r891f_nonempty_barOf_equiv hY.rLe hRp
  have hRbar : IsExtraspecialExpP 3 1 ↥(r891f_barOf (R891Y (R891H L S) (R891Z L S) Ys) R) :=
    isExtraspecialExpP_of_mulEquiv eR hst.ctx.xShape.rExtra
  have hZRbar : center (R891Ybar (R891H L S) (R891Z L S) Ys) ≤
      r891f_barOf (R891Y (R891H L S) (R891Z L S) Ys) R := hcen ▸ r891f_barOf_mono hZR
  set φ := r891f_barAut htN with hφ
  have hfix : ∀ x ∈ ((r891f_barOf (R891Y (R891H L S) (R891Z L S) Ys) R).map
      (QuotientGroup.mk' (center (R891Ybar (R891H L S) (R891Z L S) Ys)))), φ x = x := by
    rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    have : r891f_conjAut htN r = r := Subtype.ext (by
      simp only [r891f_coe_conjAut]
      rw [htR _ (Subgroup.mem_subgroupOf.mp hr), mul_inv_cancel_right])
    simp only [QuotientGroup.mk'_apply]
    rw [hφ, r891f_barAut_mk, this]
  have hφp : φ ^ p = 1 := r891f_barAut_pow_eq_one htN (hto ▸ pow_orderOf_eq_one t)
  have hφ1 : φ = 1 := by
    by_cases hp7 : p = 7
    · subst hp7
      by_contra hne
      exact hSeven _ h897 _ hRbar hZRbar φ hfix (orderOf_eq_prime hφp hne)
    · exact hAut p hp hp7 φ hφp
  have hcomm : ∀ y : ↥(R891Y (R891H L S) (R891Z L S) Ys), (y : G)⁻¹ * (t * y * t⁻¹) ∈ D.M := by
    intro y
    have h1 : φ ((y : R891Ybar (R891H L S) (R891Z L S) Ys) :
        R891Ybar (R891H L S) (R891Z L S) Ys ⧸ center (R891Ybar (R891H L S) (R891Z L S) Ys)) =
        (y : R891Ybar (R891H L S) (R891Z L S) Ys) := by
      rw [hφ1, MulAut.one_apply]
    rw [hφ, r891f_barAut_mk] at h1
    have h2 := QuotientGroup.eq.mp h1.symm
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at h2
    have := r891f_mem_M_of_mem_center (hst.set.sylow.le) hgam hY.comp hcen
      (y⁻¹ * r891f_conjAut htN y) h2
    simpa using this
  apply hY.notM
  intro y hy
  apply r891f_mem_of_conj_mem hsp htM hto
  have h := hcomm ⟨y, hy⟩⁻¹
  simp only [Subgroup.coe_inv, inv_inv] at h
  have : y * t * y⁻¹ = (y * (t * y⁻¹ * t⁻¹)) * t := by group
  rw [this]
  exact D.M.mul_mem h htM

theorem s891_final (D : Data G) (hSg : SigmaStd D) (hSeven : R891SevenCore)
    (L S R A : Subgroup G) (hst : R891State D L S R A 1) (h895 : R891Facts895 D L S 1 R)
    (Ys : Subgroup (R891Star (R891H L S) (R891Z L S))) (hY : R891YSet D L S 1 R Ys)
    (h897 : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    False :=
  r891_final_core hSg hSeven hst h895.gammaO3 hY h897 fun p hp hp7 =>
    absurd (r891f_eq_seven_of_cong_one (D.sig_prime p hp).1 (hst.f893.normZ.1 p hp)) hp7

private theorem r891f_Y_eq_map {H Z : Subgroup G} (Ys : Subgroup (R891Star H Z)) :
    R891Y H Z Ys = ((CFSG.perfectResidual ↥(Ys.comap (QuotientGroup.mk' (R891Ker H Z)))).map
      (Ys.comap (QuotientGroup.mk' (R891Ker H Z))).subtype).map H.subtype := by
  rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map H.subtype]
  rfl

private theorem r891f_perfectResidual_eq_top {Q : Type} [Group Q] (hperf : commutator Q = ⊤) :
    CFSG.perfectResidual Q = ⊤ := by
  have h : ∀ n : ℕ, derivedSeries Q n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]
  unfold CFSG.perfectResidual
  simp [h]

private theorem r891f_map_perfectResidual_pre {H Z : Subgroup G} {Ys : Subgroup (R891Star H Z)}
    (hperf : commutator ↥Ys = ⊤) :
    ((CFSG.perfectResidual ↥(Ys.comap (QuotientGroup.mk' (R891Ker H Z)))).map
      (Ys.comap (QuotientGroup.mk' (R891Ker H Z))).subtype).map
        (QuotientGroup.mk' (R891Ker H Z)) = Ys := by
  rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    r891f_perfectResidual_eq_top hperf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

private noncomputable def r891f_toStar {H Z : Subgroup G} (Ys : Subgroup (R891Star H Z)) :
    ↥(R891Y H Z Ys) →* ↥Ys :=
  ((QuotientGroup.mk' (R891Ker H Z)).comp (Subgroup.inclusion (r891f_Y_le_H Ys))).codRestrict Ys
    fun y => r891f_mk_mem_of_mem_Y y.2

private theorem r891f_coe_toStar {H Z : Subgroup G} (Ys : Subgroup (R891Star H Z))
    (y : ↥(R891Y H Z Ys)) :
    (r891f_toStar Ys y : R891Star H Z) =
      QuotientGroup.mk' (R891Ker H Z) ⟨y, r891f_Y_le_H Ys y.2⟩ := rfl

private theorem r891f_toStar_surjective {H Z : Subgroup G} {Ys : Subgroup (R891Star H Z)}
    (hperf : commutator ↥Ys = ⊤) : Function.Surjective (r891f_toStar Ys) := by
  rintro ⟨x, hx⟩
  rw [← r891f_map_perfectResidual_pre hperf] at hx
  obtain ⟨h, hh, rfl⟩ := hx
  have hhY : (h : G) ∈ R891Y H Z Ys := by
    rw [r891f_Y_eq_map]
    exact ⟨h, hh, rfl⟩
  exact ⟨⟨h, hhY⟩, Subtype.ext rfl⟩

private noncomputable def r891f_toBar (Y : Subgroup G) :
    ↥Y →* (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) ⧸ center (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
  (QuotientGroup.mk' _).comp (QuotientGroup.mk' _)

omit [Finite G] in
private theorem r891f_toBar_surjective (Y : Subgroup G) : Function.Surjective (r891f_toBar Y) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

private theorem r891f_ker_toStar_eq {Z : Subgroup G}
    {Ys : Subgroup (R891Star (centralizer (Z : Set G)) Z)}
    (hc : IsComponentOf Ys ⊤) (hZY : Z ≤ R891Y (centralizer (Z : Set G)) Z Ys)
    (hZ3 : Nat.card Z = 3)
    (hc3 : Nat.card (center (R891Ybar (centralizer (Z : Set G)) Z Ys)) = 3) :
    (r891f_toStar Ys).ker = (r891f_toBar (R891Y (centralizer (Z : Set G)) Z Ys)).ker := by
  have hcen := r891f_center_eq_barOf hZY hZ3 hc3
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, r891f_toBar, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hcen]
  constructor
  · intro h1
    have h1' : QuotientGroup.mk' (R891Ker (centralizer (Z : Set G)) Z)
        ⟨y, r891f_Y_le_H Ys y.2⟩ = 1 := congrArg Subtype.val h1
    obtain ⟨a, haO, z, hz, haz⟩ := r891f_exists_mul_of_mem_ker _ h1'
    have hzY : z ∈ R891Y (centralizer (Z : Set G)) Z Ys := hZY hz
    have haY : a ∈ R891Y (centralizer (Z : Set G)) Z Ys := by
      have : a = (y : G) * z⁻¹ := by rw [← haz]; group
      rw [this]
      exact Subgroup.mul_mem _ y.2 (Subgroup.inv_mem _ hzY)
    obtain ⟨a', ha'O, ha'⟩ := r891f_mem_pPrimeCore_of_mem (r891f_Y_le_H Ys) haY haO
    refine ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have : (⟨z, hzY⟩ : ↥(R891Y (centralizer (Z : Set G)) Z Ys))⁻¹ * y = a' := by
      apply Subtype.ext
      have ha'' : (a' : G) = a := ha'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [ha'', ← haz, r891f_comm_of_mem_centralizer (r891f_Y_le_H Ys haY) hz]
      group
    rw [this]
    exact ha'O
  · rintro ⟨z, hz, hzy⟩
    have hzy' := QuotientGroup.eq.mp hzy
    have hO : ((z⁻¹ * y : ↥(R891Y (centralizer (Z : Set G)) Z Ys)) : G) ∈
        (CFSG.pPrimeCore 3 ↥(centralizer (Z : Set G))).map (centralizer (Z : Set G)).subtype :=
      r891f_pPrimeCore_Y_le hc ⟨_, hzy', rfl⟩
    obtain ⟨o, hoO, hoe⟩ := hO
    apply Subtype.ext
    rw [r891f_coe_toStar, OneMemClass.coe_one, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hzK : (⟨z, r891f_Y_le_H Ys z.2⟩ : ↥(centralizer (Z : Set G))) ∈
        R891Ker (centralizer (Z : Set G)) Z :=
      Subgroup.subset_normalClosure (Or.inr (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hz)))
    have hoK : o ∈ R891Ker (centralizer (Z : Set G)) Z :=
      Subgroup.subset_normalClosure (Or.inl hoO)
    have : (⟨y, r891f_Y_le_H Ys y.2⟩ : ↥(centralizer (Z : Set G))) =
        ⟨z, r891f_Y_le_H Ys z.2⟩ * o := by
      apply Subtype.ext
      have hoe' : (o : G) = ((z⁻¹ * y : ↥(R891Y (centralizer (Z : Set G)) Z Ys)) : G) := hoe
      simp only [Subgroup.coe_mul, hoe', Subgroup.coe_inv, mul_inv_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ hzK hoK

private theorem r891f_exists_mulEquiv_star_bar {Z : Subgroup G}
    {Ys : Subgroup (R891Star (centralizer (Z : Set G)) Z)}
    (hc : IsComponentOf Ys ⊤) (hZY : Z ≤ R891Y (centralizer (Z : Set G)) Z Ys)
    (hZ3 : Nat.card Z = 3)
    (hc3 : Nat.card (center (R891Ybar (centralizer (Z : Set G)) Z Ys)) = 3) :
    ∃ e : ↥Ys ≃* (R891Ybar (centralizer (Z : Set G)) Z Ys ⧸
        center (R891Ybar (centralizer (Z : Set G)) Z Ys)),
      ∀ y : ↥(R891Y (centralizer (Z : Set G)) Z Ys),
        e (r891f_toStar Ys y) = r891f_toBar (R891Y (centralizer (Z : Set G)) Z Ys) y := by
  have hperf : commutator ↥Ys = ⊤ := hc.2.2.1
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective (r891f_toStar Ys)
    (r891f_toStar_surjective hperf)
  let e₂ := QuotientGroup.quotientMulEquivOfEq (r891f_ker_toStar_eq hc hZY hZ3 hc3)
  let e₃ := QuotientGroup.quotientKerEquivOfSurjective
    (r891f_toBar (R891Y (centralizer (Z : Set G)) Z Ys)) (r891f_toBar_surjective _)
  refine ⟨e₁.symm.trans (e₂.trans e₃), fun y => ?_⟩
  have h1 : e₁.symm (r891f_toStar Ys y) = (y : ↥(R891Y (centralizer (Z : Set G)) Z Ys) ⧸
      (r891f_toStar Ys).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MulEquiv.trans_apply, h1]
  rfl

theorem r891_final_of_sig
    {D : Data G} (hSg : SigmaStd D) (hSeven : R891SevenCore)
    (hFeit : ∀ (Y : Type) [Group Y] [Finite Y], R891List897 Y → ∀ {p : ℕ}, (p = 13 ∨ p = 73) →
      ∀ α : MulAut (Y ⧸ center Y), α ^ p = 1 → α = 1)
    {L S R A : Subgroup G} {n : ℕ} (hst : R891State D L S R A n) (h895 : R891Facts895 D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys)
    (h897 : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys)) : False :=
  r891_final_core hSg hSeven hst h895.gammaO3 hY h897 fun p hp hp7 φ hφ => by
    have hp1373 : p = 13 ∨ p = 73 := by
      rcases prime_cases_of_R891XShape_of_R891YSet
        hst.ctx.xShape hst.f893.normZ.1 hY h897 hp with
        ⟨_, hp7'⟩ | ⟨_, hp13⟩ | ⟨_, hp73⟩
      · exact (hp7 hp7').elim
      · exact Or.inl hp13
      · exact Or.inr hp73
    exact hFeit _ h897 hp1373 φ hφ

theorem r891_final_of_primes {D : Data G} (hSg : SigmaStd D) (hSeven : R891SevenCore)
    (hAut : ∀ (Y : Type) [Group Y] [Finite Y], R891List897 Y → ∀ {p : ℕ}, p.Prime →
      p ≠ 2 → p ≠ 3 → p ≠ 5 → p ≠ 7 → p ≠ 11 → p ≠ 19 → p ≠ 31 →
      ∀ α : MulAut (Y ⧸ center Y), α ^ p = 1 → α = 1)
    {L S R A : Subgroup G} {n : ℕ} (hst : R891State D L S R A n) (h895 : R891Facts895 D L S n R)
    {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))} (hY : R891YSet D L S n R Ys)
    (h897 : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys)) : False :=
  r891_final_core hSg hSeven hst h895.gammaO3 hY h897 fun p hp hp7 φ hφ => by
    obtain ⟨h2, h3, h5, h11, h19, h31⟩ :=
      prime_exclusions_of_R891_congruences n p (D.sig_prime p hp).1
      (hst.f893.normZ.1 p hp).1 (hst.f893.normZ.1 p hp).2
    exact hAut _ h897 (D.sig_prime p hp).1 h2 h3 h5 hp7 h11 h19 h31 φ hφ

theorem r891_exists_mulEquiv_star_bar_of_card {Z : Subgroup G}
    {Ys : Subgroup (R891Star (centralizer (Z : Set G)) Z)}
    (hc : IsComponentOf Ys ⊤) (hZY : Z ≤ R891Y (centralizer (Z : Set G)) Z Ys)
    (hZ3 : Nat.card Z = 3)
    (hc3 : Nat.card (center (R891Ybar (centralizer (Z : Set G)) Z Ys)) = 3) :
    ∃ e : ↥Ys ≃* (R891Ybar (centralizer (Z : Set G)) Z Ys ⧸
        center (R891Ybar (centralizer (Z : Set G)) Z Ys)),
      ∀ (y : ↥(R891Y (centralizer (Z : Set G)) Z Ys)) (h : (y : G) ∈ centralizer (Z : Set G))
        (hs : QuotientGroup.mk' (R891Ker (centralizer (Z : Set G)) Z) ⟨y, h⟩ ∈ Ys),
        e ⟨_, hs⟩ = ((y : R891Ybar (centralizer (Z : Set G)) Z Ys) :
          R891Ybar (centralizer (Z : Set G)) Z Ys ⧸
            center (R891Ybar (centralizer (Z : Set G)) Z Ys)) := by
  obtain ⟨e, he⟩ := r891f_exists_mulEquiv_star_bar hc hZY hZ3 hc3
  exact ⟨e, fun y h hs => he y⟩

theorem r891_exists_mulEquiv_star_bar {D : Data G} {L S R A : Subgroup G} {n : ℕ}
    (hst : R891State D L S R A n) {Ys : Subgroup (R891Star (R891H L S) (R891Z L S))}
    (hY : R891YSet D L S n R Ys) (h897 : R891List897 (R891Ybar (R891H L S) (R891Z L S) Ys)) :
    ∃ e : ↥Ys ≃* (R891Ybar (R891H L S) (R891Z L S) Ys ⧸
        center (R891Ybar (R891H L S) (R891Z L S) Ys)),
      ∀ (y : ↥(R891Y (R891H L S) (R891Z L S) Ys)) (h : (y : G) ∈ R891H L S)
        (hs : QuotientGroup.mk' (R891Ker (R891H L S) (R891Z L S)) ⟨y, h⟩ ∈ Ys),
        e ⟨_, hs⟩ = ((y : R891Ybar (R891H L S) (R891Z L S) Ys) :
          R891Ybar (R891H L S) (R891Z L S) Ys ⧸ center (R891Ybar (R891H L S) (R891Z L S) Ys)) := by
  have hc3 : Nat.card (center (R891Ybar (R891H L S) (R891Z L S) Ys)) = 3 := by
    rcases h897 with h | h | h
    · exact h.2.1
    · exact h.2.1
    · exact h.2.1
  obtain ⟨e, he⟩ := r891f_exists_mulEquiv_star_bar hY.comp hY.zLe hst.basic.zOrder hc3
  exact ⟨e, fun y h hs => he y⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
