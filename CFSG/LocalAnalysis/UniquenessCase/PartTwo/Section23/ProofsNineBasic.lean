module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74ThreeNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem isSylowOf_map_conj_of_map_eq {H Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H) {i : G}
    (hH : H.map (MulAut.conj i).toMonoidHom = H) :
    CFSG.ABGLocalTools.IsSylowOf q (Q.map (MulAut.conj i).toMonoidHom) H := by
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hQ ⊢
  obtain ⟨hQH, hQp, hQidx⟩ := hQ
  refine ⟨?_, hQp.map _, ?_⟩
  · intro x hx
    rw [← hH]
    exact Subgroup.map_mono hQH hx
  · rw [← hH, Subgroup.relIndex_map_map_of_injective Q H (MulAut.conj i).injective]
    exact hQidx

private theorem mem_normalizer_of_forall_mem_iff {Q : Subgroup G} {i c : G}
    (h : ∀ x : G, x ∈ Q.map (MulAut.conj i).toMonoidHom ↔ c⁻¹ * x * c ∈ Q) :
    c⁻¹ * i ∈ Subgroup.normalizer (Q : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : Q.map (MulAut.conj (c⁻¹ * i)).toMonoidHom ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : i * x * i⁻¹ ∈ Q.map (MulAut.conj i).toMonoidHom := ⟨x, hx, rfl⟩
    have hc := (h (i * x * i⁻¹)).mp hx'
    have heq : (MulAut.conj (c⁻¹ * i)).toMonoidHom x = c⁻¹ * (i * x * i⁻¹) * c := by
      change (c⁻¹ * i) * x * (c⁻¹ * i)⁻¹ = c⁻¹ * (i * x * i⁻¹) * c
      group
    rw [heq]
    exact hc
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj (c⁻¹ * i)).injective]

private theorem le_sylow_of_isPGroup_le_normalizer {T P : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hP : IsPGroup 2 P)
    (hTP : T ≤ Subgroup.normalizer (P : Set G)) : P ≤ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (T ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' (H := T) (K := P) hT.isPGroup hP hTP
  have hEq : T ⊔ P = T := hT.eq_of_le le_sup_left le_top h2
  exact le_of_le_of_eq le_sup_right hEq

theorem s23_9_O2L_of {D : Data G} {Ch : Choice2011 G} : S23_9_O2L D Ch := by
  intro _ c
  have hTL : D.T ≤ Subgroup.normalizer (c.L : Set G) := c.hL.1.1
  have hnorm : ∀ n ∈ D.T, ∀ k ∈ c.L, n * k * n⁻¹ ∈ c.L :=
    fun n hn k hk => (Subgroup.mem_normalizer_iff.mp (hTL hn) k).1 hk
  have hTP : D.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 c.L : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact uc22main1_conj_mem_pCoreOf (N := D.T) (K := c.L) hnorm ht hx
    · intro hx
      have ht' : t⁻¹ ∈ D.T := D.T.inv_mem ht
      have h := uc22main1_conj_mem_pCoreOf (N := D.T) (K := c.L) hnorm ht' hx
      have hx' : t⁻¹ * (t * x * t⁻¹) * (t⁻¹)⁻¹ = x := by group
      rwa [hx'] at h
  exact (le_sylow_of_isPGroup_le_normalizer D.sylowG
    (uc22main1_isPGroup_pCoreOf c.L) hTP).trans D.sylowM.le

theorem s23_9_NoInv_of {D : Data G} {Ch : Choice2011 G}
    (h4 : S23_4 D Ch) :
    H1930 D → ∀ c : Ctx23L D Ch, ∀ e ∈ D.M,
      e ∉ Subgroup.centralizer (D.Z : Set G) →
        ¬ InvertedIn D.M (Subgroup.zpowers e) := by
  intro h1930 c e heM heNC hinv
  have h4c := h4 h1930 c
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := by
    simpa [h4c.1] using h4c.2.2
  let CM : Subgroup G := D.M ⊓ Subgroup.centralizer (D.Z : Set G)
  let N : Subgroup ↥D.M := CM.subgroupOf D.M
  have hCMle : CM ≤ D.M := inf_le_left
  have hMC : D.M ≤ Subgroup.normalizer (Subgroup.centralizer (D.Z : Set G) : Set G) :=
    hMZ.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.Z)
  have hMCM : D.M ≤ Subgroup.normalizer (CM : Set G) :=
    (le_inf Subgroup.le_normalizer hMC).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCMle).2 hMCM
  have hTleN : D.T.subgroupOf D.M ≤ N := by
    intro t ht
    exact Subgroup.mem_subgroupOf.mpr
      ⟨D.sylowM.le (Subgroup.mem_subgroupOf.mp ht),
        uc22main1_T_le_centralizer D (Subgroup.mem_subgroupOf.mp ht)⟩
  obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
  have hTnot : ¬ 2 ∣ (D.T.subgroupOf D.M).index := by
    rw [← hS]
    exact S.not_dvd_index
  have hdvd : N.index ∣ (D.T.subgroupOf D.M).index := Subgroup.index_dvd_of_le hTleN
  have hodd : ¬ 2 ∣ N.index := fun h2 => hTnot (h2.trans hdvd)
  haveI : N.Normal := hNnormal
  obtain ⟨m, hmM, hm⟩ := hinv
  have hconj :
      (⟨m, hmM⟩ : ↥D.M) * ⟨e, heM⟩ * (⟨m, hmM⟩ : ↥D.M)⁻¹ = ⟨e, heM⟩⁻¹ := by
    ext
    simpa using hm e (Subgroup.mem_zpowers e)
  have hmem : (⟨e, heM⟩ : ↥D.M) ∈ N :=
    CFSG.ComponentClassification.HarrisLit.T1.S74.mem_of_conj_eq_inv_of_odd_index hodd hconj
  exact heNC (Subgroup.mem_subgroupOf.mp hmem).2

private theorem sylow_le_of_mem_uniqueSet {M Q X : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : rankThreeIsMaxTwoLocal M) (hXU : X ∈ uniqueSet M) (hXQ : X ≤ Q)
    (hQp : IsPGroup q Q) : Q ≤ M := by
  by_contra hnot
  have hlt : Q ⊓ M < Q :=
    lt_of_le_of_ne inf_le_left (fun hEq => hnot (hEq ▸ inf_le_right))
  have hgrow : Q ⊓ M < Q ⊓ Subgroup.normalizer (Q ⊓ M : Set G) :=
    CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hQp hlt
  have hYU : Q ⊓ M ∈ uniqueSet M :=
    mem_uniqueSet_of_le hXU (le_inf hXQ hXU.1) inf_le_right
  have hNY : Subgroup.normalizer (Q ⊓ M : Set G) ≤ M :=
    normalizer_le_of_mem_uniqueSet hM hYU
  exact (not_lt_of_ge (le_inf inf_le_left (inf_le_right.trans hNY))) hgrow

private theorem map_centralizer_conj_eq_of_inverts {A : Subgroup G} {i : G}
    (hinv : ∀ a ∈ A, i * a * i⁻¹ = a⁻¹) :
    (Subgroup.centralizer (A : Set G)).map (MulAut.conj i).toMonoidHom =
      Subgroup.centralizer (A : Set G) := by
  have hinvA' : ∀ a ∈ A, i⁻¹ * a * i ∈ A := by
    intro a ha
    have h1 : i * a⁻¹ * i⁻¹ = a := by
      simpa using hinv a⁻¹ (A.inv_mem ha)
    have h2 : i⁻¹ * a * i = a⁻¹ := by
      calc i⁻¹ * a * i = i⁻¹ * (i * a⁻¹ * i⁻¹) * i := by rw [h1]
        _ = a⁻¹ := by group
    rw [h2]
    exact A.inv_mem ha
  have hle : (Subgroup.centralizer (A : Set G)).map (MulAut.conj i).toMonoidHom ≤
      Subgroup.centralizer (A : Set G) := by
    rintro _ ⟨h, hh, rfl⟩
    change (MulAut.conj i).toMonoidHom h ∈ Subgroup.centralizer (A : Set G)
    have hh' : h ∈ Subgroup.centralizer (A : Set G) := hh
    rw [Subgroup.mem_centralizer_iff] at hh' ⊢
    intro a ha
    have hcomm := hh' (i⁻¹ * a * i) (hinvA' a ha)
    calc a * (i * h * i⁻¹) = i * ((i⁻¹ * a * i) * h) * i⁻¹ := by group
      _ = i * (h * (i⁻¹ * a * i)) * i⁻¹ := by rw [hcomm]
      _ = (i * h * i⁻¹) * a := by group
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj i).injective]

private theorem exists_mem_centralizer_conj_normalizer {H Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] {i : G} (hQ : CFSG.ABGLocalTools.IsSylowOf q Q H)
    (hH : H.map (MulAut.conj i).toMonoidHom = H) :
    ∃ c ∈ H, c⁻¹ * i ∈ Subgroup.normalizer (Q : Set G) := by
  have hQiSyl := isSylowOf_map_conj_of_map_eq hQ hH
  obtain ⟨c, hcH, hc⟩ := hQ.exists_mem_conj hQiSyl
  exact ⟨c, hcH, mem_normalizer_of_forall_mem_iff (Q := Q) (i := i) (c := c) fun x => hc x⟩

theorem invertedInOfUnique_holds :
    ∀ (G : Type) [Group G] [Finite G] (M A X : Subgroup G) (q : ℕ) (i : G),
      rankThreeIsMaxTwoLocal M → q.Prime →
      X ≠ ⊥ → IsPGroup q ↥X → X ≤ Subgroup.centralizer (A : Set G) →
      X ∈ uniqueSet M →
      (∀ a ∈ A, i * a * i⁻¹ = a⁻¹) → InvertedIn M A := by
  intro G _ _ M A X q i hM hq hXne hXp hXA hXU hinv
  haveI : Fact q.Prime := ⟨hq⟩
  let H : Subgroup G := Subgroup.centralizer (A : Set G)
  have hXH : X ≤ H := hXA
  have hXsub : IsPGroup q (X.subgroupOf H) :=
    hXp.of_equiv (Subgroup.subgroupOfEquivOfLe hXH).symm
  obtain ⟨Q, hXQ⟩ := hXsub.exists_le_sylow
  let Q₁ : Subgroup G := (Q : Subgroup ↥H).map H.subtype
  have hQ₁syl : CFSG.ABGLocalTools.IsSylowOf q Q₁ H := ⟨Q, rfl⟩
  have hQ₁p : IsPGroup q Q₁ := hQ₁syl.isPGroup
  have hXQ₁ : X ≤ Q₁ := fun x hx =>
    ⟨⟨x, hXH hx⟩, hXQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hQ₁leM : Q₁ ≤ M := sylow_le_of_mem_uniqueSet hM hXU hXQ₁ hQ₁p
  have hQ₁U : Q₁ ∈ uniqueSet M := mem_uniqueSet_of_le hXU hXQ₁ hQ₁leM
  have hNQ₁M : Subgroup.normalizer (Q₁ : Set G) ≤ M :=
    normalizer_le_of_mem_uniqueSet hM hQ₁U
  have hHmap : H.map (MulAut.conj i).toMonoidHom = H :=
    map_centralizer_conj_eq_of_inverts hinv
  obtain ⟨c, hcH, hmN⟩ := exists_mem_centralizer_conj_normalizer hQ₁syl hHmap
  refine ⟨c⁻¹ * i, hNQ₁M hmN, fun a ha => ?_⟩
  have hcommca : a * c = c * a := (Subgroup.mem_centralizer_iff.mp hcH) a ha
  have hcac : c⁻¹ * a * c = a := by
    calc c⁻¹ * a * c = c⁻¹ * (a * c) := by group
      _ = c⁻¹ * (c * a) := by rw [hcommca]
      _ = a := by group
  calc (c⁻¹ * i) * a * (c⁻¹ * i)⁻¹ = c⁻¹ * (i * a * i⁻¹) * c := by group
    _ = c⁻¹ * a⁻¹ * c := by rw [hinv a ha]
    _ = a⁻¹ := by
      calc c⁻¹ * a⁻¹ * c = (c⁻¹ * a * c)⁻¹ := by group
        _ = a⁻¹ := by rw [hcac]

private theorem pCoreOf_le_normalizer_hinf (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.pCoreOf 2 D.M ≤ Subgroup.normalizer (Hinf (D.M ⊓ L) : Set G) := by
  have hO2_le_T : CFSG.Open.pCoreOf 2 D.M ≤ D.T := by
    obtain ⟨S, hS⟩ := D.sylowM.exists_sylow_eq_subgroupOf
    have hpcS : CFSG.pCore 2 ↥D.M ≤ (S : Subgroup ↥D.M) :=
      CFSG.pCore_isPGroup.le_sylow_of_normal S
    rw [hS] at hpcS
    exact Subgroup.map_le_iff_le_comap.2 hpcS
  have hO2_le_NL : CFSG.Open.pCoreOf 2 D.M ≤
      Subgroup.normalizer (L : Set G) := hO2_le_T.trans hTL
  have hO2_le_M : CFSG.Open.pCoreOf 2 D.M ≤ D.M := Subgroup.map_subtype_le _
  have hQ_le_NM : CFSG.Open.pCoreOf 2 D.M ≤
      Subgroup.normalizer (D.M : Set G) := fun x hx => Subgroup.le_normalizer (hO2_le_M hx)
  have hQ_le_NML : CFSG.Open.pCoreOf 2 D.M ≤
      Subgroup.normalizer ((D.M ⊓ L : Subgroup G) : Set G) :=
    (le_inf hQ_le_NM hO2_le_NL).trans Subgroup.inf_normalizer_le_normalizer_inf
  intro q hq
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hMLmap : (D.M ⊓ L).map (MulAut.conj q).toMonoidHom = D.M ⊓ L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQ_le_NML hq)
  calc (Hinf (D.M ⊓ L)).map (MulAut.conj q).toMonoidHom
      = Hinf ((D.M ⊓ L).map (MulAut.conj q).toMonoidHom) := Hinf_map _ _
    _ = Hinf (D.M ⊓ L) := by rw [hMLmap]

private theorem isSubnormal_hinf_of_barImage (D : Data G) {L : Subgroup G}
    (hTL : D.T ≤ Subgroup.normalizer (L : Set G))
    (hKsub : CFSG.Open.IsSubnormal (barImage D.M (Hinf (D.M ⊓ L))) ⊤) :
    CFSG.Open.IsSubnormal (Hinf (D.M ⊓ L)) D.M := by
  let K : Subgroup G := Hinf (D.M ⊓ L)
  have hKleML : K ≤ D.M ⊓ L := by
    simpa [K] using uc22p21c_Hinf_le (D.M ⊓ L)
  have hKleM : K ≤ D.M := hKleML.trans inf_le_left
  have hQ_le_NK : CFSG.Open.pCoreOf 2 D.M ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using pCoreOf_le_normalizer_hinf D hTL
  have hKnormal : (K.subgroupOf (K ⊔ CFSG.Open.pCoreOf 2 D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hQ_le_NK)
  have hKsub' : CFSG.Open.IsSubnormal (barImage D.M K) ⊤ := by
    simpa [K] using hKsub
  have hpre : barPreimage D.M (barImage D.M K) = K ⊔ CFSG.Open.pCoreOf 2 D.M := by
    unfold barPreimage barImage
    rw [QuotientGroup.comap_map_mk' (CFSG.pCore 2 ↥D.M) (K.subgroupOf D.M),
      Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKleM, sup_comm]
    rfl
  have hPre : CFSG.Open.IsSubnormal (barPreimage D.M (barImage D.M K)) D.M := by
    have h1 := hKsub'.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    have h2 := h1.map D.M.subtype
    simpa [barPreimage, Subgroup.map_top] using h2
  have hmid : CFSG.Open.IsSubnormal (K ⊔ CFSG.Open.pCoreOf 2 D.M) D.M := by
    rwa [hpre] at hPre
  exact CFSG.Open.IsSubnormal.step le_sup_left hKnormal hmid

private theorem isQuasisimple_open_of_isQuasisimple {Q : Type} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Open.IsQuasisimple Q :=
  ⟨Group.isPerfect_def.1 h.1, h.2.1⟩

theorem s23_9_C0_of {D : Data G} {Ch : Choice2011 G} :
    H1930 D → ∀ c : Ctx23L D Ch,
      let K : Subgroup G := Hinf (D.M ⊓ c.L)
      K ≠ ⊥ → IsQuasisimple (Bar2 K) → CFSG.Open.IsSubnormal (barImage D.M K) ⊤ →
        K ∈ calC D.M := by
  intro h1930 c
  dsimp only
  intro _ hKq hKsub
  have hKperf : ⁅Hinf (D.M ⊓ c.L), Hinf (D.M ⊓ c.L)⁆ = Hinf (D.M ⊓ c.L) :=
    uc22p21c_Hinf_perfect (D.M ⊓ c.L)
  have hKsubM : CFSG.Open.IsSubnormal (Hinf (D.M ⊓ c.L)) D.M :=
    isSubnormal_hinf_of_barImage D c.hL.1.1 hKsub
  exact ⟨hKsubM, hKperf, isQuasisimple_open_of_isQuasisimple hKq⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
