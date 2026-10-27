module

public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
import CFSG.RankThree.PartTwo.Sec12.Item123Inputs
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.CentralCover.FourGroupWitness
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec19.Step1914E
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec18
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open scoped Pointwise

theorem rank3II_19_14E_of_tri (htri : Step1914Tri) (hK : KFacts.KS18M12) : Step1914E := by
  intro G _ _ A c L E M hctx hLM
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hA : CFSG.Assembly.IsElemAbelian 3 A := hctx.mem_partTwoE.1
  have hc := hctx.zpowers_mem_omegaA
  have hcA : c ∈ A := hc.1 (Subgroup.mem_zpowers c)
  have hcE : c ∈ E :=
    mem_of_le_centralizer hctx.toPartTwoStanding hctx.partTwoS_eq hEE (hA.2 c hcA)
      hctx.le_centralizer
  have hcL : c ∉ L := hctx.hypS.2.2 c hc L hctx.mem_lA
  have hc3 : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hc.2.1
  have hcard : E = Subgroup.zpowers c ⊔ (E ⊓ L) → Nat.card (E ⊓ L : Subgroup G) = 9 := by
    intro hEeq
    have hle : E ⊓ L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (inf_le_left.trans (le_centralizer_of_mem hE.1.1 hcE)).trans
        (centralizer_le_normalizer_zpowers c)
    have hdisj : Subgroup.zpowers c ⊓ (E ⊓ L) = ⊥ := by
      by_contra hne
      obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hxc : (x : G) ∈ Subgroup.zpowers c := x.2.1
      have hx1' : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      have hzx : Subgroup.zpowers (x : G) = Subgroup.zpowers c := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hc3]
        have hd : orderOf (x : G) ∣ 3 := by
          have := Subgroup.orderOf_dvd_natCard (Subgroup.zpowers c) hxc
          rwa [Nat.card_zpowers, hc3] at this
        rcases Nat.prime_three.eq_one_or_self_of_dvd _ hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hx1'
        · exact h.ge
      have hcx : c ∈ Subgroup.zpowers (x : G) := by
        rw [hzx]
        exact Subgroup.mem_zpowers c
      exact hcL ((Subgroup.zpowers_le.mpr x.2.2.2) hcx)
    have h1 := CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj
    rw [← hEeq, hE.2, Nat.card_zpowers, hc3] at h1
    omega
  rcases htri G A c L E M hctx with hLM' | ⟨-, hEeq, -⟩ | hM12
  · exact absurd hLM' hLM
  · exact hcard hEeq
  obtain ⟨φ⟩ := hM12
  obtain ⟨-, -, -, hsol⟩ := hK _ ⟨φ⟩
  have hθeq := theta_eq_pCore_two_of_solvable hsol
  set θL := aschbacherSolvableCore 3 L with hθL
  obtain ⟨hL3, hZ, hinn, -⟩ := hK (L ⧸ θL) ⟨(QuotientGroup.quotientMulEquivOfEq hθeq).trans φ⟩
  refine hcard ?_
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  have hFE : partTwoF G = partTwoE G :=
    (hctx.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hctx.toPartTwoStanding, hctx.partTwoS_eq,
    hFE ▸ hctx.mem_partTwoE, hctx.not_mem_partTwoT, hc, hctx.mem_lA⟩
  have hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A :=
    hD.mem_partTwoF.2.1
  have hLc : L ∈ thetaComponentsAt 3 c := hD.mem_thetaComponentsAt
  have huniq := (hctx.chosen136.2 c hc L hctx.mem_lA).2
  have hLcard : 3 ∣ Nat.card L := hL3.trans (Subgroup.card_quotient_dvd_card _)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hmem := map_mem_thetaComponentsAt (MulAut.conj h) hLc
    have hhc : h * c * h⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp hh c).mp (Subgroup.mem_zpowers c)
    have hzp : Subgroup.zpowers (h * c * h⁻¹) = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hhc) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers]
      exact ((MulAut.conj h).orderOf_eq c).ge
    have hθc : thetaComponentsAt 3 (h * c * h⁻¹) = thetaComponentsAt 3 c := by
      rw [thetaComponentsAt_eq_thetaComponentsIn, thetaComponentsAt_eq_thetaComponentsIn,
        centralizer_singleton_eq_of_zpowers_eq hzp]
    have hmem' : L.map (MulAut.conj h).toMonoidHom ∈ thetaComponentsAt 3 c := by
      rw [← hθc]
      exact hmem
    exact huniq _ hmem'
      (by rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]; exact hLcard)
  have hLH : L ≤ H := le_normalizer_zpowers_of_mem hLc
  have hEAH : E ⊔ A ≤ H :=
    sup_le (hctx.le_centralizer.trans (centralizer_le_normalizer_zpowers c))
      ((le_centralizer_of_mem hA.1 hcA).trans (centralizer_le_normalizer_zpowers c))
  obtain ⟨Q₀, hQ₀⟩ := (hctx.isPGroup_sup.comap_subtype (K := H)).exists_le_sylow
  set P := (Q₀ : Subgroup H).map H.subtype with hPdef
  have hP : CFSG.ABGLocalTools.IsSylowOf 3 P H := ⟨Q₀, rfl⟩
  have hEAP : E ⊔ A ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hEAH]
    exact Subgroup.map_mono hQ₀
  have hAP : A ≤ P := le_sup_right.trans hEAP
  have hEP : E ≤ P := le_sup_left.trans hEAP
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPC : P ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec12.le_centralizer_of_isPGroup hc3 hP3 hP.le
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hP.le.trans hHL
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hPθ : ∀ x : L, (x : G) ∈ P → x ∈ θL → x = 1 := by
    intro x hxP hxθ
    obtain ⟨k, hk⟩ := hP3 ⟨x, hxP⟩
    have h1 : x ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf x ∣ Nat.card θL := by
      have := orderOf_dvd_natCard (⟨x, hxθ⟩ : θL)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (3 ^ k) (Nat.card θL) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1)
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1) h2)
  set ρ : Subgroup.normalizer (L : Set G) →* MulAut (L ⧸ θL) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom with hρ
  have hρmk : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)) (y : L),
      ρ ⟨x, hx⟩ (y : L ⧸ θL) = ((L.normalizerMonoidHom ⟨x, hx⟩ y : L) : L ⧸ θL) :=
    fun x hx y => rfl
  have hnm : ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)) (y : L),
      ((L.normalizerMonoidHom ⟨x, hx⟩ y : L) : G) = x * y * x⁻¹ :=
    fun x hx y => Sec4.normalizerMonoidHom_apply_coe hx y
  have hρL : ∀ (l : L) (hl : (l : G) ∈ Subgroup.normalizer (L : Set G)),
      ρ ⟨l, hl⟩ = MulAut.conj (l : L ⧸ θL) := by
    intro l hl
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hρmk, MulAut.conj_apply]
    have : (L.normalizerMonoidHom ⟨(l : G), hl⟩ y : L) = l * y * l⁻¹ :=
      Subtype.ext (by rw [hnm]; simp)
    rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hPLρ : ∀ (l : L) (hlP : (l : G) ∈ P), ρ ⟨l, hPN hlP⟩ = 1 → l = 1 := by
    intro l hlP hρl
    rw [hρL] at hρl
    have h1 : (l : L ⧸ θL) ∈ Subgroup.center (L ⧸ θL) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := congrArg (fun σ : MulAut (L ⧸ θL) => σ y) hρl
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc y * (l : L ⧸ θL) = (l : L ⧸ θL) * y * (l : L ⧸ θL)⁻¹ * (l : L ⧸ θL) := by rw [h2]
        _ = (l : L ⧸ θL) * y := by group
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
    exact hPθ l hlP h1
  have hρinner : ∀ (x : G) (hx : x ∈ P), ∃ s : L ⧸ θL, ρ ⟨x, hPN hx⟩ = MulAut.conj s := by
    intro x hx
    obtain ⟨k, hk⟩ := hP3 ⟨x, hx⟩
    have h1 : (⟨x, hPN hx⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    exact hinn _ ⟨k, by rw [← map_pow, h1, map_one]⟩
  set ρP : Subgroup (MulAut (L ⧸ θL)) :=
    (P.subgroupOf (Subgroup.normalizer (L : Set G))).map ρ with hρP
  have hρP3 : IsPGroup 3 ρP := (hP3.comap_subtype (K := Subgroup.normalizer (L : Set G))).map ρ
  set R : Subgroup (L ⧸ θL) := ρP.comap (MulAut.conj : L ⧸ θL →* MulAut (L ⧸ θL)) with hR
  have hR3 : IsPGroup 3 R := by
    rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := hρP3 ⟨_, hs⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : MulAut.conj (s ^ 3 ^ k) = 1 := by
      rw [map_pow]
      simpa using congrArg Subtype.val hk
    have h2 : s ^ 3 ^ k ∈ Subgroup.center (L ⧸ θL) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 := congrArg (fun σ : MulAut (L ⧸ θL) => σ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * s ^ 3 ^ k = s ^ 3 ^ k * y * (s ^ 3 ^ k)⁻¹ * s ^ 3 ^ k := by rw [h3]
        _ = s ^ 3 ^ k * y := by group
    rw [hZ, Subgroup.mem_bot] at h2
    simpa using h2
  obtain ⟨Q, hQ⟩ := hP.inf_of_le_normalizer hLH hHL
  have hQmem : ∀ l : L, l ∈ Q ↔ (l : G) ∈ P := by
    intro l
    constructor
    · intro hl
      have : (l : G) ∈ P ⊓ L := hQ ▸ Subgroup.mem_map_of_mem L.subtype hl
      exact this.1
    · intro hl
      have : (l : G) ∈ (Q : Subgroup L).map L.subtype := hQ ▸ ⟨hl, l.2⟩
      obtain ⟨l', hl', hll'⟩ := this
      rwa [show l = l' from Subtype.ext hll'.symm]
  set Qb := Q.mapSurjective (QuotientGroup.mk'_surjective θL) with hQb
  have hQbR : (Qb : Subgroup (L ⧸ θL)) ≤ R := by
    rintro _ ⟨l, hl, rfl⟩
    have hlP : (l : G) ∈ P := (hQmem l).mp hl
    change MulAut.conj (QuotientGroup.mk' θL l) ∈ ρP
    rw [QuotientGroup.mk'_apply, ← hρL l (hPN hlP)]
    exact ⟨⟨(l : G), hPN hlP⟩, Subgroup.mem_subgroupOf.mpr hlP, rfl⟩
  have hRQ : R = Qb := Qb.is_maximal' hR3 hQbR
  have hdecomp : ∀ x ∈ P, ∃ l : L, (l : G) ∈ P ∧
      ∀ hy : (l : G)⁻¹ * x ∈ Subgroup.normalizer (L : Set G), ρ ⟨(l : G)⁻¹ * x, hy⟩ = 1 := by
    intro x hx
    obtain ⟨s, hs⟩ := hρinner x hx
    have hsR : s ∈ R := by
      change MulAut.conj s ∈ ρP
      rw [← hs]
      exact ⟨⟨x, hPN hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [hRQ] at hsR
    obtain ⟨l, hl, rfl⟩ := hsR
    have hlP : (l : G) ∈ P := (hQmem l).mp hl
    refine ⟨l, hlP, fun hy => ?_⟩
    have h1 : (⟨(l : G)⁻¹ * x, hy⟩ : Subgroup.normalizer (L : Set G)) =
        (⟨(l : G), hPN hlP⟩ : Subgroup.normalizer (L : Set G))⁻¹ * ⟨x, hPN hx⟩ := rfl
    rw [h1, map_mul, map_inv, hs, hρL l (hPN hlP), QuotientGroup.mk'_apply, inv_mul_cancel]
  have hcomm : ∀ l : L, (l : G) ∈ P → ∀ y (hy : y ∈ P), ρ ⟨y, hPN hy⟩ = 1 →
      (l : G) * y = y * l := by
    intro l hlP y hy hρy
    have h1 := congrArg (fun σ : MulAut (L ⧸ θL) => σ (l : L ⧸ θL)) hρy
    simp only [MulAut.one_apply] at h1
    rw [hρmk, QuotientGroup.eq] at h1
    set n := L.normalizerMonoidHom ⟨y, hPN hy⟩ l with hn
    have hnG : (n : G) = y * l * y⁻¹ := hnm y (hPN hy) l
    have h2 : n⁻¹ * l = 1 := by
      refine hPθ _ ?_ h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hnG]
      exact P.mul_mem (P.inv_mem (P.mul_mem (P.mul_mem hy hlP) (P.inv_mem hy))) hlP
    have h3 : (n : G) = l := by
      rw [show n = l from inv_mul_eq_one.mp h2]
    rw [hnG] at h3
    calc (l : G) * y = y * l * y⁻¹ * y := by rw [h3]
      _ = y * l := by group
  have hAF : ∀ a (ha : a ∈ A), ρ ⟨a, hPN (hAP ha)⟩ = 1 → a ∈ Subgroup.zpowers c := by
    intro a ha hρa
    have hsc : a ∈ sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨ha, fun x hx => ?_⟩
      have h1 := congrArg (fun σ : MulAut (L ⧸ θL) => σ ((⟨x, hx⟩ : L) : L ⧸ θL)) hρa
      simp only [MulAut.one_apply] at h1
      rw [hρmk] at h1
      set n := L.normalizerMonoidHom ⟨a, hPN (hAP ha)⟩ ⟨x, hx⟩ with hn
      have hnG : (n : G) = a * x * a⁻¹ := hnm a (hPN (hAP ha)) ⟨x, hx⟩
      have h2 : n * (⟨x, hx⟩ : L)⁻¹ ∈ θL := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
          mul_inv_cancel]
      refine ⟨_, h2, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hnG]
    have := hctx.mem_lA.2.2.1
    rw [this] at hsc
    exact hsc
  have hcompcomm : ∀ x₁ (h₁ : x₁ ∈ P) x₂ (h₂ : x₂ ∈ P) (l₁ l₂ : L) (hl₁ : (l₁ : G) ∈ P)
      (hl₂ : (l₂ : G) ∈ P), ρ ⟨(l₁ : G)⁻¹ * x₁, hPN (P.mul_mem (P.inv_mem hl₁) h₁)⟩ = 1 →
      ρ ⟨(l₂ : G)⁻¹ * x₂, hPN (P.mul_mem (P.inv_mem hl₂) h₂)⟩ = 1 →
      x₁ * x₂ = x₂ * x₁ →
      ((l₁ : G)⁻¹ * x₁) * ((l₂ : G)⁻¹ * x₂) = ((l₂ : G)⁻¹ * x₂) * ((l₁ : G)⁻¹ * x₁) := by
    intro x₁ h₁ x₂ h₂ l₁ l₂ hl₁ hl₂ hρ₁ hρ₂ hx
    set y₁ := (l₁ : G)⁻¹ * x₁ with hy₁
    set y₂ := (l₂ : G)⁻¹ * x₂ with hy₂
    have hy₁P : y₁ ∈ P := P.mul_mem (P.inv_mem hl₁) h₁
    have hy₂P : y₂ ∈ P := P.mul_mem (P.inv_mem hl₂) h₂
    have hc₁₂ := hcomm l₁ hl₁ y₂ hy₂P hρ₂
    have hc₂₁ := hcomm l₂ hl₂ y₁ hy₁P hρ₁
    set w : L := (l₂ * l₁)⁻¹ * (l₁ * l₂) with hw
    have hwG : (w : G) = (y₂ * y₁) * (y₁ * y₂)⁻¹ := by
      have e₁ : x₁ = (l₁ : G) * y₁ := by rw [hy₁]; group
      have e₂ : x₂ = (l₂ : G) * y₂ := by rw [hy₂]; group
      have hx' : (l₁ : G) * y₁ * ((l₂ : G) * y₂) = (l₂ : G) * y₂ * ((l₁ : G) * y₁) := by
        rw [← e₁, ← e₂]
        exact hx
      have k₁ : (l₁ : G) * y₁ * ((l₂ : G) * y₂) = (l₁ : G) * l₂ * (y₁ * y₂) := by
        calc (l₁ : G) * y₁ * ((l₂ : G) * y₂) = (l₁ : G) * (y₁ * l₂) * y₂ := by group
          _ = (l₁ : G) * (l₂ * y₁) * y₂ := by rw [hc₂₁]
          _ = (l₁ : G) * l₂ * (y₁ * y₂) := by group
      have k₂ : (l₂ : G) * y₂ * ((l₁ : G) * y₁) = (l₂ : G) * l₁ * (y₂ * y₁) := by
        calc (l₂ : G) * y₂ * ((l₁ : G) * y₁) = (l₂ : G) * (y₂ * l₁) * y₁ := by group
          _ = (l₂ : G) * (l₁ * y₂) * y₁ := by rw [hc₁₂]
          _ = (l₂ : G) * l₁ * (y₂ * y₁) := by group
      rw [k₁, k₂] at hx'
      simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
      calc ((l₂ : G) * l₁)⁻¹ * ((l₁ : G) * l₂)
          = ((l₂ : G) * l₁)⁻¹ * ((l₁ : G) * l₂ * (y₁ * y₂)) * (y₁ * y₂)⁻¹ := by group
        _ = ((l₂ : G) * l₁)⁻¹ * ((l₂ : G) * l₁ * (y₂ * y₁)) * (y₁ * y₂)⁻¹ := by rw [hx']
        _ = (y₂ * y₁) * (y₁ * y₂)⁻¹ := by group
    have hwP : (w : G) ∈ P := by
      rw [hwG]
      exact P.mul_mem (P.mul_mem hy₂P hy₁P) (P.inv_mem (P.mul_mem hy₁P hy₂P))
    have hρw : ρ ⟨w, hPN hwP⟩ = 1 := by
      have e : (⟨w, hPN hwP⟩ : Subgroup.normalizer (L : Set G)) =
          (⟨y₂, hPN hy₂P⟩ * ⟨y₁, hPN hy₁P⟩) * (⟨y₁, hPN hy₁P⟩ * ⟨y₂, hPN hy₂P⟩)⁻¹ :=
        Subtype.ext (by rw [hwG]; rfl)
      rw [e, map_mul, map_inv, map_mul, map_mul, hρ₁, hρ₂]
      simp
    have hw1 : w = 1 := hPLρ w hwP hρw
    have h1 : (w : G) = 1 := by rw [hw1]; rfl
    rw [hwG, mul_inv_eq_one] at h1
    exact h1.symm
  have hcomp3 : ∀ x (hx : x ∈ P) (l : L) (hl : (l : G) ∈ P),
      ρ ⟨(l : G)⁻¹ * x, hPN (P.mul_mem (P.inv_mem hl) hx)⟩ = 1 → x ^ 3 = 1 →
      ((l : G)⁻¹ * x) ^ 3 = 1 := by
    intro x hx l hl hρy hx3
    set y := (l : G)⁻¹ * x with hy
    have hyP : y ∈ P := P.mul_mem (P.inv_mem hl) hx
    have hly := hcomm l hl y hyP hρy
    have h1 : x ^ 3 = (l : G) ^ 3 * y ^ 3 := by
      have : x = (l : G) * y := by rw [hy]; group
      rw [this]
      exact Commute.mul_pow hly 3
    rw [hx3] at h1
    have hl3 : (l ^ 3 : L) = 1 := by
      have hl3P : ((l ^ 3 : L) : G) ∈ P := by
        simpa using P.pow_mem hl 3
      refine hPLρ _ hl3P ?_
      have e : (⟨((l ^ 3 : L) : G), hPN hl3P⟩ : Subgroup.normalizer (L : Set G)) =
          (⟨y, hPN hyP⟩ ^ 3)⁻¹ := by
        apply Subtype.ext
        have : (l : G) ^ 3 = (y ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1.symm
        simpa using this
      rw [e, map_inv, map_pow, hρy, one_pow, inv_one]
    have h2 : (l : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hl3
    rw [h2, one_mul] at h1
    exact h1.symm
  have hAdec : ∀ a ∈ A, ∃ l : L, (l : G) ∈ P ∧ (l : G) ∈ A ∧
      (l : G)⁻¹ * a ∈ Subgroup.zpowers c := by
    intro a ha
    obtain ⟨l, hlP, hy⟩ := hdecomp a (hAP ha)
    have hyP : (l : G)⁻¹ * a ∈ P := P.mul_mem (P.inv_mem hlP) (hAP ha)
    have hρy := hy (hPN hyP)
    have hy3 := hcomp3 a (hAP ha) l hlP hρy (hA.2 a ha)
    have hyc : ∀ a' ∈ A, a' * ((l : G)⁻¹ * a) = ((l : G)⁻¹ * a) * a' := by
      intro a' ha'
      obtain ⟨l', hl'P, hy'⟩ := hdecomp a' (hAP ha')
      have hy'P : (l' : G)⁻¹ * a' ∈ P := P.mul_mem (P.inv_mem hl'P) (hAP ha')
      have hcc := hcompcomm a (hAP ha) a' (hAP ha') l l' hlP hl'P hρy (hy' (hPN hy'P))
        (congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩))
      have hlc := hcomm l' hl'P _ hyP hρy
      calc a' * ((l : G)⁻¹ * a) = (l' : G) * ((l' : G)⁻¹ * a') * ((l : G)⁻¹ * a) := by group
        _ = (l' : G) * (((l : G)⁻¹ * a) * ((l' : G)⁻¹ * a')) := by rw [mul_assoc, ← hcc]
        _ = ((l : G)⁻¹ * a) * ((l' : G) * ((l' : G)⁻¹ * a')) := by
          rw [← mul_assoc, hlc, mul_assoc]
        _ = ((l : G)⁻¹ * a) * a' := by group
    have hab' := Sec15.isElemAbelian_sup_zpowers hA hy3 hyc
    have heq := hAmax _ hab' le_sup_left
    have hyA : (l : G)⁻¹ * a ∈ A := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyc' := hAF _ hyA hρy
    refine ⟨l, hlP, ?_, hyc'⟩
    have hlA : (l : G) = a * ((l : G)⁻¹ * a)⁻¹ := by group
    rw [hlA]
    exact A.mul_mem ha (A.inv_mem hyA)
  apply le_antisymm
  · intro e he
    obtain ⟨l, hlP, hy⟩ := hdecomp e (hEP he)
    have hyP : (l : G)⁻¹ * e ∈ P := P.mul_mem (P.inv_mem hlP) (hEP he)
    have hρy := hy (hPN hyP)
    have hy3 := hcomp3 e (hEP he) l hlP hρy (hE.1.2 e he)
    have hyc : ∀ a ∈ A, a * ((l : G)⁻¹ * e) = ((l : G)⁻¹ * e) * a := by
      intro a ha
      obtain ⟨l', hl'P, hl'A, hl'c⟩ := hAdec a ha
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hl'c
      have hak : a = (l' : G) * c ^ k := by rw [hk]; group
      have h1 := hcomm l' hl'P _ hyP hρy
      have h2 : c ^ k * ((l : G)⁻¹ * e) = ((l : G)⁻¹ * e) * c ^ k := by
        have hyc0 : ((l : G)⁻¹ * e) * c = c * ((l : G)⁻¹ * e) :=
          Subgroup.mem_centralizer_singleton_iff.mp (hPC hyP)
        exact (Commute.zpow_left hyc0.symm k).eq
      rw [hak, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
    have hab' := Sec15.isElemAbelian_sup_zpowers hA hy3 hyc
    have heq := hAmax _ hab' le_sup_left
    have hyA : (l : G)⁻¹ * e ∈ A := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    have hyc' := hAF _ hyA hρy
    have hyE : (l : G)⁻¹ * e ∈ E := Subgroup.zpowers_le.mpr hcE hyc'
    have hlE : (l : G) ∈ E := by
      have : (l : G) = e * ((l : G)⁻¹ * e)⁻¹ := by group
      rw [this]
      exact E.mul_mem he (E.inv_mem hyE)
    have he' : e = (l : G) * ((l : G)⁻¹ * e) := by group
    rw [he']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hlE, l.2⟩) (Subgroup.mem_sup_left hyc')
  · exact sup_le (Subgroup.zpowers_le.mpr hcE) inf_le_left

end CFSG.RankThree.PartTwo.Sec19
