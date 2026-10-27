module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Quot
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK335Inputs
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.Goldschmidt.StrongClosure
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.RankThree.PartTwo.KFacts.L34Sylow
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

private theorem k335nhyp_glbCore_le_of_forall {G : Type} [Group G] [Finite G] {p k : ℕ}
    {P M : Subgroup G}
    (h : ∀ Q : Subgroup G, Q ≤ P → k ≤ CFSG.Open.pRank p Q →
      Subgroup.normalizer (Q : Set G) ≤ M) :
    CFSG.Open.GLBCore p k P ≤ M := by
  unfold CFSG.Open.GLBCore
  refine sSup_le ?_
  rintro N ⟨Q, hQP, hk, rfl⟩
  exact h Q hQP hk

private theorem k335nhyp_sylow {G : Type} [Group G] [Finite G] {L P H : Subgroup G}
    (hLH : L ≤ H) (hPH : P ≤ H) (h : CFSG.ABGLocalTools.IsSylowOf 3 P L) :
    CFSG.ABGLocalTools.IsSylowOf 3 (P.subgroupOf H) (L.subgroupOf H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).1 ?_
  rw [Subgroup.subgroupOf_map_subtype P H, Subgroup.subgroupOf_map_subtype L H,
    inf_eq_left.mpr hPH, inf_eq_left.mpr hLH]
  exact h

private theorem k335nhyp_gamma {G : Type} [Group G] [Finite G] {L P H : Subgroup G}
    (hLH : L ≤ H) (hPH : P ≤ H)
    (hgamma : CFSG.Open.rankThreeGamma 1 3 P ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.rankThreeGamma 1 3 (P.subgroupOf H) ≤
      Subgroup.normalizer (L.subgroupOf H : Set ↥H) := by
  change CFSG.Open.GLBCore 3 1 (P.subgroupOf H) ≤
    Subgroup.normalizer (L.subgroupOf H : Set ↥H)
  refine k335nhyp_glbCore_le_of_forall ?_
  intro Q hQP hk
  let Q' : Subgroup G := Q.map H.subtype
  have hQ'P : Q' ≤ P := by
    have hmap : (P.subgroupOf H).map H.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPH]
    exact (Subgroup.map_mono hQP).trans hmap.le
  have hQ'H : Q' ≤ H := hQ'P.trans hPH
  have hk' : 1 ≤ CFSG.Open.pRank 3 Q' :=
    hk.trans (CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) H.subtype
      H.subtype_injective Q)
  have hnormQ : Subgroup.normalizer (Q : Set ↥H) =
      (Subgroup.normalizer (Q' : Set G)).subgroupOf H := by
    have hQeq : Q'.subgroupOf H = Q :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective Q
    rw [Subgroup.subgroupOf_normalizer_eq (H := Q') (N := H) hQ'H, hQeq]
  have h1 : Subgroup.normalizer (Q' : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 P := by
    change Subgroup.normalizer (Q' : Set G) ≤ CFSG.Open.GLBCore 3 1 P
    exact le_sSup ⟨Q', hQ'P, hk', rfl⟩
  have h3 : (Subgroup.normalizer (Q' : Set G)).subgroupOf H ≤
      (Subgroup.normalizer (L : Set G)).subgroupOf H :=
    Subgroup.comap_mono (f := H.subtype) (h1.trans hgamma)
  rw [Subgroup.subgroupOf_normalizer_eq hLH] at h3
  rw [hnormQ]
  exact h3

private theorem k335nhyp_closed {G : Type} [Group G] [Finite G] {P H : Subgroup G}
    (hPH : P ≤ H)
    (hclosed : ∀ a ∈ P, ∀ g : G, g⁻¹ * a * g ∈ Subgroup.normalizer (P : Set G) →
      g⁻¹ * a * g ∈ P) :
    ∀ a ∈ P.subgroupOf H, ∀ g : ↥H,
      g⁻¹ * a * g ∈ Subgroup.normalizer (P.subgroupOf H : Set ↥H) →
      g⁻¹ * a * g ∈ P.subgroupOf H := by
  intro a ha g hg
  have haG : (a : G) ∈ P := ha
  have hnorm : Subgroup.normalizer (P.subgroupOf H : Set ↥H) =
      (Subgroup.normalizer (P : Set G)).subgroupOf H := by
    rw [Subgroup.subgroupOf_normalizer_eq hPH]
  have hmemNorm : (g : G)⁻¹ * (a : G) * (g : G) ∈ Subgroup.normalizer (P : Set G) := by
    rw [hnorm] at hg
    have := Subgroup.mem_subgroupOf.mp hg
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
  have hmemP : (g : G)⁻¹ * (a : G) * (g : G) ∈ P :=
    hclosed (a : G) haG (g : G) hmemNorm
  refine Subgroup.mem_subgroupOf.mpr ?_
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hmemP

theorem k335_hyp_subgroup {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (h : K335Hyp G L P) (H : Subgroup G) (hLH : L ≤ H) :
    K335Hyp ↥H (L.subgroupOf H) (P.subgroupOf H) := by
  have hPH : P ≤ H := h.sylow.le.trans hLH
  exact
    { kGroup := h.kGroup.subgroup H
      rank := (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) H.subtype
        H.subtype_injective).trans h.rank
      lie := CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm h.lie
      sylow := k335nhyp_sylow hLH hPH h.sylow
      gamma := k335nhyp_gamma hLH hPH h.gamma
      closed := k335nhyp_closed hPH h.closed }

private theorem k335nmem_eNine (X : Type) [Group X] (h : LieModel X .PSL 3 2 2) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  refine ⟨(CFSG.RankThree.PartTwo.KFacts.L34.eZero k).map e.symm.toMonoidHom, ?_, ?_⟩
  · refine CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr
      (CFSG.IsElementaryAbelian.of_forall ?_ ?_)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul,
        CFSG.RankThree.PartTwo.KFacts.L34.commute_of_mem_eZero hk ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, CFSG.RankThree.PartTwo.KFacts.L34.pow_three_of_mem_eZero hk ha, map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact CFSG.RankThree.PartTwo.KFacts.L34.card_eZero hk

private theorem k335nmem_commute_of_disjoint {G : Type} [Group G] {L L' : Subgroup G}
    (hLL' : L ≤ Subgroup.normalizer (L' : Set G))
    (hL'L : L' ≤ Subgroup.normalizer (L : Set G)) (hdisj : Disjoint L' L) :
    ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l := by
  intro l hl l' hl'
  have h1 : l * l' * l⁻¹ ∈ L' :=
    (Subgroup.mem_normalizer_iff.mp (hLL' hl) l').mp hl'
  have h2 : l' * l⁻¹ * l'⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (hL'L hl') l⁻¹).mp (L.inv_mem hl)
  have hmem : l * l' * l⁻¹ * l'⁻¹ ∈ L' ⊓ L :=
    Subgroup.mem_inf.mpr ⟨L'.mul_mem h1 (L'.inv_mem hl'), by
      simpa only [mul_assoc, Subgroup.mem_toSubmonoid] using L.mul_mem hl h2⟩
  have hone : l * l' * l⁻¹ * l'⁻¹ = 1 :=
    Subgroup.mem_bot.mp (by rwa [disjoint_iff.mp hdisj] at hmem)
  calc l * l' = (l * l' * l⁻¹ * l'⁻¹) * (l' * l) := by group
    _ = l' * l := by rw [hone, one_mul]

private theorem k335nmem_le_normalizer_of_commute {G : Type} [Group G] {A B : Subgroup G}
    (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro b hb a ha
  rw [show b * a * b⁻¹ = a from by rw [← (hc a ha b hb)]; group]
  exact ha

theorem k335_mem_normalizer {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hr : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3) (hL : LieModel ↥L .PSL 3 2 2) {H : Subgroup G}
    (hH : H.Normal) (hLH : L ≤ H) (hHL : H ≤ Subgroup.normalizer (L : Set G)) (g : G) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  let L' : Subgroup G := L.map (MulAut.conj g).toMonoidHom
  have hL'H : L' ≤ H := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    show g * y * g⁻¹ ∈ H
    exact hH.conj_mem y (hLH hy) g
  have hHL' : H ≤ Subgroup.normalizer (L' : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hyx]
    change h * (g * y * g⁻¹) * h⁻¹ ∈ L'
    refine Subgroup.mem_map.mpr ⟨(g⁻¹ * h * g) * y * (g⁻¹ * h * g)⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hHL (hH.conj_mem' h hh g)) y).mp hy
    · show g * ((g⁻¹ * h * g) * y * (g⁻¹ * h * g)⁻¹) * g⁻¹ = h * (g * y * g⁻¹) * h⁻¹
      group
  have hLL' : L ≤ Subgroup.normalizer (L' : Set G) := hLH.trans hHL'
  have hL'L : L' ≤ Subgroup.normalizer (L : Set G) := hL'H.trans hHL
  have hL'eq : L' = L := by
    by_contra hne
    have hNormal : (L'.subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf, Subgroup.le_normalizer_iff]
      intro l hl x hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hLL' hl) x).mp hx.1,
        L.mul_mem (L.mul_mem hl hx.2) (L.inv_mem hl)⟩
    have hsimple : IsSimpleGroup ↥L := k335_simple_L hL
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal ↥L _ hsimple (L'.subgroupOf L) hNormal with
      hbot | htop
    · have hdisj : Disjoint L' L := Subgroup.subgroupOf_eq_bot.mp hbot
      have hcomm := k335nmem_commute_of_disjoint hLL' hL'L hdisj
      obtain ⟨E, hEelem, hEcard⟩ := k335nmem_eNine ↥L hL
      let E₁ : Subgroup G := E.map L.subtype
      have hE₁le : E₁ ≤ L := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
        rw [← hyx]
        exact y.2
      have hE₁card : Nat.card E₁ = 9 := by
        change Nat.card (E.map L.subtype) = 9
        rw [Subgroup.card_map_of_injective L.subtype_injective]
        exact hEcard
      have hE₁elem : CFSG.Open.IsElemAbelian 3 E₁ := by
        change CFSG.Open.IsElemAbelian 3 (E.map L.subtype)
        exact hEelem.map L.subtype
      let E₂ : Subgroup G := E₁.map (MulAut.conj g).toMonoidHom
      have hE₂le : E₂ ≤ L' := Subgroup.map_mono hE₁le
      have hE₂card : Nat.card E₂ = 9 := by
        change Nat.card (E₁.map (MulAut.conj g).toMonoidHom) = 9
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact hE₁card
      have hE₂elem : CFSG.Open.IsElemAbelian 3 E₂ := by
        change CFSG.Open.IsElemAbelian 3 (E₁.map (MulAut.conj g).toMonoidHom)
        exact hE₁elem.map (MulAut.conj g).toMonoidHom
      have hcommE : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a :=
        fun a ha b hb => hcomm a (hE₁le ha) b (hE₂le hb)
      have hdisjE : Disjoint E₁ E₂ := (hdisj.mono hE₂le hE₁le).symm
      have hE₂norm : E₂ ≤ Subgroup.normalizer (E₁ : Set G) :=
        k335nmem_le_normalizer_of_commute hcommE
      have hcardsup : Nat.card ↥(E₁ ⊔ E₂) = 3 ^ 4 := by
        rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E₁ E₂ hE₂norm
          hdisjE, hE₁card, hE₂card]
        norm_num
      have hsupelem : CFSG.Open.IsElemAbelian 3 (E₁ ⊔ E₂) :=
        CFSG.Open.IsElemAbelian.sup_of_commute hE₁elem hE₂elem hcommE
      have hle4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) :=
        CFSG.SectionRank.le_pRank (by norm_num) le_top hsupelem hcardsup
      omega
    · have hle : L ≤ L' := Subgroup.subgroupOf_eq_top.mp htop
      have hcardL' : Nat.card L' = Nat.card L :=
        Subgroup.card_map_of_injective (K := L) (MulAut.conj g).injective
      exact hne ((Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardL')).symm)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  simpa only [L'] using hL'eq

theorem k335_pPrimeCore_normal {G : Type} [Group G] [Finite G] (hO : CFSG.pPrimeCore 3 G = ⊥)
    (N : Subgroup G) (hN : N.Normal) : CFSG.pPrimeCore 3 ↥N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := CFSG.ABGLocalTools.pPrimeCore_map_subtype_eq_inf (p := 3) hN
  rwa [hO, inf_bot_eq, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h

private theorem k335nzs_comm {G : Type} [Group G] {P : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 3 P) {u v : G} (hu : u ∈ P) (hv : v ∈ P) :
    u * v = v * u :=
  congrArg Subtype.val (hE.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem k335_conj_eq_of_commute {G : Type} [Group G] [Finite G] {P S : Subgroup G}
    (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤) (hPS : P ≤ S) (hE : CFSG.Open.IsElemAbelian 3 P)
    (hcl : CFSG.Open.fusionStronglyClosed (P : Set G) S) {N : Subgroup G} (hN : N.Normal)
    (hPN : P ⊓ N = ⊥) {a : G} (ha : a ∈ P) {x : G} (hx : x ∈ P ⊔ N)
    (hc : x⁻¹ * a * x * a = a * (x⁻¹ * a * x)) : x⁻¹ * a * x = a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : N.Normal := hN
  let X : Subgroup G := P ⊔ N
  let C : Subgroup G := X ⊓ Subgroup.centralizer ({a} : Set G)
  let b : G := x⁻¹ * a * x
  have haX : a ∈ X := Subgroup.mem_sup_left ha
  have hxX : x ∈ X := hx
  have hbX : b ∈ X := X.mul_mem (X.mul_mem (X.inv_mem hxX) haX) hxX
  have hbcomm : b ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc
  have hbC : b ∈ C := ⟨hbX, hbcomm⟩
  have hPC : P ≤ C := by
    refine le_inf le_sup_left ?_
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact k335nzs_comm hE hp ha
  have hPp : IsPGroup 3 P := hS.isPGroup.to_le hPS
  have hPpC : IsPGroup 3 (P.comap C.subtype) := hPp.comap_subtype (K := C)
  obtain ⟨T₀, hPT₀⟩ := hPpC.exists_le_sylow
  have hbord_a : orderOf b = orderOf a := by
    have hsc : SemiconjBy x⁻¹ a b := by
      show x⁻¹ * a = b * x⁻¹
      simp only [b]
      group
    exact (SemiconjBy.orderOf_eq x⁻¹ hsc).symm
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Sylow 3 C, Subgroup.zpowers (⟨b, hbC⟩ : C) ≤ Q₁ := by
    apply IsPGroup.exists_le_sylow
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [pow_one, Nat.card_zpowers, Subgroup.orderOf_mk, hbord_a]
    exact orderOf_dvd_iff_pow_eq_one.mpr (hE.2 a ha)
  obtain ⟨c, hc_smul⟩ := MulAction.exists_smul_eq C T₀ Q₁
  have hbcQ : (⟨b, hbC⟩ : C) ∈ (c • T₀ : Sylow 3 C) := by
    rw [hc_smul]
    exact hQ₁ (Subgroup.mem_zpowers _)
  have hmemT : c⁻¹ * (⟨b, hbC⟩ : C) * c ∈ (T₀ : Subgroup C) := by
    have h' := hbcQ
    change (⟨b, hbC⟩ : C) ∈ ((c • T₀ : Sylow 3 C) : Set C) at h'
    rw [Sylow.coe_smul, Set.mem_smul_set] at h'
    obtain ⟨y, hy, hyeq⟩ := h'
    have : y = c⁻¹ * (⟨b, hbC⟩ : C) * c := by
      rw [← hyeq]
      simp only [MulAut.smul_def, MulAut.conj_apply]
      group
    rwa [this] at hy
  have hmemGT : (c : G)⁻¹ * b * (c : G) ∈ T₀.map C.subtype := by
    refine Subgroup.mem_map.mpr ⟨c⁻¹ * (⟨b, hbC⟩ : C) * c, hmemT, ?_⟩
    rfl
  let y : G := x * (c : G)
  have hcX : (c : G) ∈ X := (Subgroup.mem_inf.mp c.2).1
  have hyX : y ∈ X := X.mul_mem hxX hcX
  have hy_eq : y⁻¹ * a * y = (c : G)⁻¹ * b * (c : G) := by
    show (x * (c : G))⁻¹ * a * (x * (c : G)) = (c : G)⁻¹ * b * (c : G)
    simp only [b]
    group
  have hSp : IsPGroup 3 S := hS.isPGroup
  have hSidx : ¬ 3 ∣ S.index := by
    have h := (CFSG.ABGLocalTools.isSylowOf_iff (p := 3) (P := S) (K := ⊤)).1 hS
    rw [Subgroup.relIndex_top_right] at h
    exact h.2.2
  let T : Sylow 3 G := hSp.toSylow hSidx
  have hT : (T : Subgroup G) = S := IsPGroup.toSylow_coe hSp hSidx
  have hclT : CFSG.Open.fusionStronglyClosed (P : Set G) (T : Subgroup G) := by
    rw [hT]; exact hcl
  have hR : IsPGroup 3 (T₀.map C.subtype) := T₀.isPGroup'.map C.subtype
  have hAR : P ≤ T₀.map C.subtype := by
    intro p hp
    exact Subgroup.mem_map.mpr
      ⟨⟨p, hPC hp⟩, hPT₀ (Subgroup.mem_comap.mpr hp), rfl⟩
  obtain ⟨Q, hRQ, hclQ⟩ :=
    CFSG.Goldschmidt.stronglyClosed_of_le_pGroup (p := 3) T hclT hR hAR
  have hmemQ : y⁻¹ * a * y ∈ T₀.map C.subtype := by
    rw [hy_eq]
    exact hmemGT
  have hyP : y⁻¹ * a * y ∈ P := hclQ a ha y (hRQ hmemQ)
  obtain ⟨p, hp, n, hn, hpn⟩ := Subgroup.mem_sup_of_normal_right.mp (show y ∈ P ⊔ N from hyX)
  have hpinv : p⁻¹ * a * p = a := by
    calc p⁻¹ * a * p = p⁻¹ * (a * p) := by group
      _ = p⁻¹ * (p * a) := by rw [k335nzs_comm hE ha hp]
      _ = a := by group
  have hyn : y⁻¹ * a * y = n⁻¹ * a * n := by
    rw [← hpn]
    calc (p * n)⁻¹ * a * (p * n) = n⁻¹ * (p⁻¹ * a * p) * n := by group
      _ = n⁻¹ * a * n := by rw [hpinv]
  have htN : a⁻¹ * (y⁻¹ * a * y) ∈ N := by
    rw [hyn]
    have hgrp : a⁻¹ * (n⁻¹ * a * n) = (a⁻¹ * n⁻¹ * a) * n := by group
    rw [hgrp]
    exact N.mul_mem (hN.conj_mem' (n⁻¹) (N.inv_mem hn) a) hn
  have htP : a⁻¹ * (y⁻¹ * a * y) ∈ P := P.mul_mem (P.inv_mem ha) hyP
  have ht_eq_a : y⁻¹ * a * y = a := by
    have h1 : a⁻¹ * (y⁻¹ * a * y) = 1 := by
      have h2 : a⁻¹ * (y⁻¹ * a * y) ∈ P ⊓ N := ⟨htP, htN⟩
      rw [hPN] at h2
      exact Subgroup.mem_bot.mp h2
    have h3 := congrArg (fun z => a * z) h1
    rw [mul_one, mul_inv_cancel_left] at h3
    exact h3
  have hcba : (c : G)⁻¹ * b * (c : G) = a := by
    rw [← hy_eq]; exact ht_eq_a
  have hb_eq_a : b = a := by
    have hca : (c : G) * a = a * (c : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
    have hb : b = (c : G) * a * (c : G)⁻¹ := by
      rw [← hcba]
      group
    rw [hb, hca]
    group
  exact hb_eq_a

private theorem k335nzs_mem_normal_of_coprime {G : Type} [Group G] [Finite G]
    {P N : Subgroup G} (hE : CFSG.Open.IsElemAbelian 3 P) (hN : N.Normal) {k : G}
    (hk : k ∈ P ⊔ N) (hk3 : Nat.Coprime 3 (orderOf k)) : k ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : N.Normal := hN
  obtain ⟨p, hp, m, hm, hpm⟩ := Subgroup.mem_sup_of_normal_right.mp hk
  have hk' : (QuotientGroup.mk' N) k = (QuotientGroup.mk' N) p := by
    rw [← hpm, map_mul]
    have hm1 : (QuotientGroup.mk' N) m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [hm1, mul_one]
  have hdvd : orderOf ((QuotientGroup.mk' N) k) ∣ 3 := by
    rw [hk']
    exact (orderOf_map_dvd (QuotientGroup.mk' N) p).trans
      (orderOf_dvd_iff_pow_eq_one.mpr (hE.2 p hp))
  have hcop' : Nat.Coprime 3 (orderOf ((QuotientGroup.mk' N) k)) :=
    Nat.Coprime.of_dvd_right (orderOf_map_dvd (QuotientGroup.mk' N) k) hk3
  have hone : orderOf ((QuotientGroup.mk' N) k) = 1 := hcop'.symm.eq_one_of_dvd hdvd
  exact (QuotientGroup.eq_one_iff k).mp (orderOf_eq_one_iff.mp hone)

theorem k335_commute_of_inf_eq_bot (hZ : K335OddZStar) {G : Type} [Group G] [Finite G]
    {P S : Subgroup G} (hK : CFSG.Open.IsKGroup G)
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup G) ≤ 3) (hS : CFSG.ABGLocalTools.IsSylowOf 3 S ⊤)
    (hPS : P ≤ S) (hE : CFSG.Open.IsElemAbelian 3 P)
    (hcl : CFSG.Open.fusionStronglyClosed (P : Set G) S) {N : Subgroup G} (hN : N.Normal)
    (hON : CFSG.pPrimeCore 3 ↥N = ⊥) (hPN : P ⊓ N = ⊥) : ∀ a ∈ P, ∀ n ∈ N, a * n = n * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : N.Normal := hN
  intro a ha n hn
  by_cases ha1 : a = 1
  · subst ha1
    simp
  · have horder : orderOf a = 3 := orderOf_eq_prime (hE.2 a ha) ha1
    let X : Subgroup G := P ⊔ N
    let ā : X := ⟨a, Subgroup.mem_sup_left ha⟩
    have hXK : CFSG.Open.IsKGroup X := hK.subgroup X
    have horderX : orderOf ā = 3 := by
      rw [Subgroup.orderOf_mk]
      exact horder
    have hconj : ∀ g : X, g⁻¹ * ā * g * ā = ā * (g⁻¹ * ā * g) → g⁻¹ * ā * g = ā := by
      intro g hgc
      apply Subtype.ext
      have hc : (g : G)⁻¹ * a * (g : G) * a = a * ((g : G)⁻¹ * a * (g : G)) := by
        have := congrArg Subtype.val hgc
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this
      exact k335_conj_eq_of_commute hS hPS hE hcl hN hPN ha g.2 hc
    have hrankX : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 :=
      (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) X.subtype
        X.subtype_injective).trans hrank
    have hbot : CFSG.pPrimeCore 3 X = ⊥ := by
      rw [CFSG.pPrimeCore_eq_bot_iff]
      intro K hKnorm hKcop
      let K' : Subgroup G := K.map X.subtype
      have hK'card : Nat.card K' = Nat.card K :=
        Subgroup.card_map_of_injective (K := K) (f := X.subtype) X.subtype_injective
      have hK'le : K' ≤ N := by
        intro k hk
        obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hk
        refine k335nzs_mem_normal_of_coprime hE hN h₀.2 ?_
        rw [show orderOf (X.subtype h₀) = orderOf h₀ from Subgroup.orderOf_coe h₀]
        exact Nat.Coprime.of_dvd_right
          (Subgroup.orderOf_mk h₀ hh₀ ▸ orderOf_dvd_natCard (⟨h₀, hh₀⟩ : K)) hKcop
      have hK'norm : (K'.subgroupOf N).Normal := by
        rw [Subgroup.normal_subgroupOf_iff hK'le]
        intro h k hh hk
        obtain ⟨h₀, hh₀, rfl⟩ := Subgroup.mem_map.mp hh
        have hkX : k ∈ X := Subgroup.mem_sup_right hk
        refine Subgroup.mem_map.mpr ⟨(⟨k, hkX⟩ : X) * h₀ * (⟨k, hkX⟩ : X)⁻¹, ?_, rfl⟩
        exact hKnorm.conj_mem h₀ hh₀ ⟨k, hkX⟩
      have hK'cop : Nat.Coprime 3 (Nat.card (K'.subgroupOf N)) := by
        have hsubcard : Nat.card (K'.subgroupOf N) = Nat.card K := by
          have h1 : Nat.card ((K'.subgroupOf N).map N.subtype) = Nat.card (K'.subgroupOf N) :=
            Subgroup.card_map_of_injective (K := K'.subgroupOf N) (f := N.subtype)
              N.subtype_injective
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK'le, hK'card] at h1
          exact h1.symm
        rw [hsubcard]
        exact hKcop
      have hK'bot : K' = ⊥ := by
        have hsub := (CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := ↥N)).1 hON
          (K'.subgroupOf N) hK'norm hK'cop
        have hmap : (K'.subgroupOf N).map N.subtype = K' := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK'le]
        rw [hsub, Subgroup.map_bot] at hmap
        exact hmap.symm
      exact (Subgroup.map_eq_bot_iff_of_injective K X.subtype_injective).1 hK'bot
    let nX : X := ⟨n, Subgroup.mem_sup_right hn⟩
    have hres : ā * nX = nX * ā := hZ X hXK hrankX hbot ā horderX hconj nX
    simpa only [Subgroup.coe_mul] using congrArg Subtype.val hres

theorem k335_isQuasisimple {G : Type} [Group G] [Finite G] (hperf : commutator G = ⊤)
    (hZ : Subgroup.center G ≠ ⊤)
    (hcent : ∀ N : Subgroup G, N.Normal → N ≠ ⊤ → N ≤ Subgroup.center G) :
    CFSG.Open.IsQuasisimple G := by
  have hnt : Nontrivial (G ⧸ Subgroup.center G) := QuotientGroup.nontrivial_iff.mpr hZ
  refine ⟨hperf, ?_⟩
  refine { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := ?_ }
  intro Mbar hMbar
  let f : G →* G ⧸ Subgroup.center G := QuotientGroup.mk' (Subgroup.center G)
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective (Subgroup.center G)
  have hMnorm : (Mbar.comap f).Normal := hMbar.comap f
  by_cases hMtop : Mbar.comap f = ⊤
  · right
    have h := Subgroup.map_comap_eq_self_of_surjective hsurj Mbar
    rw [← h, hMtop, Subgroup.map_top_of_surjective f hsurj]
  · left
    have hMle : Mbar.comap f ≤ Subgroup.center G := hcent (Mbar.comap f) hMnorm hMtop
    have hmapbot : (Mbar.comap f).map f = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      rwa [QuotientGroup.ker_mk']
    have h := Subgroup.map_comap_eq_self_of_surjective hsurj Mbar
    rw [← h]
    exact hmapbot

private theorem k335nqs_zpowers_eq_bot_of_coprime {G : Type} [Group G] [Finite G]
    (hO : CFSG.pPrimeCore 3 G = ⊥) {w : G} (hw : w ∈ Subgroup.center G)
    (hcop : Nat.Coprime 3 (orderOf w)) : w = 1 := by
  have hle : Subgroup.zpowers w ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hw
  have hnorm : (Subgroup.zpowers w).Normal := Subgroup.normal_of_le_center hle
  have hbot : Subgroup.zpowers w = ⊥ :=
    (CFSG.pPrimeCore_eq_bot_iff (p := 3) (G := G)).1 hO (Subgroup.zpowers w) hnorm
      (by rwa [Nat.card_zpowers])
  have hwW : w ∈ Subgroup.zpowers w := Subgroup.mem_zpowers w
  rw [hbot] at hwW
  simpa using hwW

theorem k335_isPGroup_center {G : Type} [Group G] [Finite G] (hO : CFSG.pPrimeCore 3 G = ⊥) :
    IsPGroup 3 (Subgroup.center G) := by
  intro z
  have hz0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  obtain ⟨k, m, hm3, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd hz0 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hord
    exact hz0 hord
  have hdiv : orderOf (z : G) / m = 3 ^ k := by
    rw [Subgroup.orderOf_coe z, hord, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hx0 : orderOf (z : G) ≠ 0 := by rwa [Subgroup.orderOf_coe z]
  have hmdvd : m ∣ orderOf (z : G) := by
    rw [Subgroup.orderOf_coe z, hord]
    exact dvd_mul_left m (3 ^ k)
  have hw_ord : orderOf ((z : G) ^ (3 ^ k)) = m := by
    rw [← hdiv]
    exact orderOf_pow_orderOf_div hx0 hmdvd
  have hwcop : Nat.Coprime 3 (orderOf ((z : G) ^ (3 ^ k))) := by
    rw [hw_ord]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3
  have hwcent : (z : G) ^ (3 ^ k) ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem z.2 (3 ^ k)
  have hw1 : (z : G) ^ (3 ^ k) = 1 := k335nqs_zpowers_eq_bot_of_coprime hO hwcent hwcop
  exact ⟨k, Subtype.ext (by simpa using hw1)⟩

theorem K335MinCex.eq_top_of_le {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (h : K335MinCex G L P) {H : Subgroup G} (hH : H.Normal) (hLH : L ≤ H) : H = ⊤ := by
  by_contra hne
  have hlt : Nat.card H < Nat.card G :=
    lt_of_le_of_ne (Subgroup.card_le_card_group H) fun h' =>
      hne ((Subgroup.card_eq_iff_eq_top H).1 h')
  have hmin := h.min H hlt _ _ (k335_hyp_subgroup h.hyp H hLH)
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := by
    rw [← Subgroup.subgroupOf_eq_top, Subgroup.subgroupOf_normalizer_eq hLH]
    exact hmin
  exact h.ne_top (eq_top_iff.2 fun g _ => k335_mem_normalizer h.hyp.rank h.hyp.lie hH hLH hHL g)

theorem K335MinCex.inf_eq_bot {G : Type} [Group G] [Finite G] {L P : Subgroup G}
    (h : K335MinCex G L P) {N : Subgroup G} (hN : N.Normal) (hNt : N ≠ ⊤) : P ⊓ N = ⊥ :=
  (k335_inf_normal h.hyp.lie h.hyp.sylow hN).resolve_right fun hPN =>
    hNt (h.eq_top_of_le hN (k335_le_of_normal h.hyp.lie h.hyp.sylow hN hPN))

theorem K335MinCex.exists_quasi (hZ : K335OddZStar) {G : Type} [Group G] [Finite G]
    {L P : Subgroup G} (h : K335MinCex G L P) : ∃ S : Subgroup G, K335Quasi G L P S := by
  obtain ⟨hE, h9⟩ := k335_sylowL h.hyp.lie h.hyp.sylow
  obtain ⟨S, hS, hPS, hSN⟩ := k335_exists_sylow h.hyp.sylow.isPGroup h.hyp.closed
  have hcl : CFSG.Open.fusionStronglyClosed (P : Set G) S := fun a ha g hg =>
    h.hyp.closed a ha g (hSN hg)
  have hO := h.pPrimeCore_eq_bot
  have hcent : ∀ N : Subgroup G, N.Normal → N ≠ ⊤ → N ≤ Subgroup.center G := by
    intro N hN hNt
    have := hN
    have hc := k335_commute_of_inf_eq_bot hZ h.hyp.kGroup h.hyp.rank hS hPS hE hcl hN
      (k335_pPrimeCore_normal hO N hN) (h.inf_eq_bot hN hNt)
    have hPC : P ≤ Subgroup.centralizer (N : Set G) := fun a ha =>
      Subgroup.mem_centralizer_iff.2 fun n hn => (hc a ha n hn).symm
    have htop := h.eq_top_of_le inferInstance
      (k335_le_of_normal h.hyp.lie h.hyp.sylow inferInstance hPC)
    intro n hn
    refine Subgroup.mem_center_iff.2 fun g => ?_
    have hg : g ∈ Subgroup.centralizer (N : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 hg n hn).symm
  have hZt : Subgroup.center G ≠ ⊤ := by
    intro hZt
    refine h.ne_top (eq_top_iff.2 fun g _ => Subgroup.mem_normalizer_iff.2 fun x => ?_)
    have hg : g ∈ Subgroup.center G := hZt ▸ Subgroup.mem_top g
    have hx : g * x * g⁻¹ = x := by
      rw [← Subgroup.mem_center_iff.1 hg x]
      group
    rw [hx]
  exact ⟨S, h.hyp.kGroup, h.hyp.rank, h.hyp.lie, h.hyp.sylow, h.hyp.gamma, h.ne_top, hE, h9, hS,
    hPS, hSN, hcl,
    k335_isQuasisimple (h.eq_top_of_le inferInstance (k335_le_commutator h.hyp.lie)) hZt hcent,
    k335_isPGroup_center hO, h.inf_eq_bot inferInstance hZt⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
