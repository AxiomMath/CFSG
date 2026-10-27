module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3
public import CFSG.CGT.PushingUpLit.Glue.LocalFactorization
public import CFSG.CGT.PushingUpLit.Glue.SixSixteenRel
public import CFSG.CGT.PushingUpLit.BHS7.SevenSix
public import CFSG.CGT.PushingUpLit.EightOneBlocksBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure IsBHSFamily (K Q : Subgroup G) (𝒢 : Set (Subgroup G)) : Prop where
  isBlock : ∀ E ∈ 𝒢, IsBTBlock K Q E
  conj_mem : ∀ E ∈ 𝒢, ∀ g ∈ K, A1b.conjSub g E ∈ 𝒢
  comm : ∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x
  sup_eq : cStarIn K Q ⊔ (⨆ E ∈ 𝒢, E) = K
  cover : ∀ F : Subgroup G, IsBTBlock K Q F → ¬ F ≤ cStarIn K Q → ∃ E ∈ 𝒢, F ≤ E
  inf_eq : cStarIn K Q ⊓ (⨆ E ∈ 𝒢, E) = ⨆ E ∈ 𝒢, cStarIn K Q ⊓ E
  shape : ∀ E ∈ 𝒢,
    ((∃ n : ℕ, 2 ≤ n ∧ IsNaturalSLTwoModule ↥E n) ∧
      cStarIn K Q ⊓ E = Subgroup.normalizer ((Q ⊓ E : Subgroup G) : Set G) ⊓ E) ∨
    (∃ m : ℕ, 1 ≤ m ∧ IsNaturalAltModule ↥E m ∧
      Nonempty ((((cStarIn K Q ⊓ E).subgroupOf E).map (QuotientGroup.mk' (pCore 2 ↥E))) ≃*
        alternatingGroup (Fin (2 * m))))

theorem exists_isBHSFamily {K Q : Subgroup G} (hK : CharTwo K)
    (hQ : IsSylowOf 2 Q K) (hne : cStarIn K Q ≠ K) :
    ∃ 𝒢 : Set (Subgroup G), IsBHSFamily K Q 𝒢 := by
  obtain ⟨𝒢, h1, h2, h3, h4, h5, h6, h7⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved G K Q hK hQ hne
  exact ⟨𝒢, ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

theorem isBTBlock_of_le {K K' Q E : Subgroup G} (h : IsBTBlock K Q E) (hE : E ≤ K') :
    IsBTBlock K' Q E :=
  { h with le := hE }

theorem b114_ElevenFourBFam_conjSub_subgroupOf {K : Subgroup G} (g : ↥K) (E : Subgroup G) :
    A1b.conjSub g (E.subgroupOf K) = (A1b.conjSub (g : G) E).subgroupOf K := by
  ext x
  rw [A1b.mem_conjSub_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, A1b.mem_conjSub_iff]
  exact Iff.rfl

theorem isSubnormal_subgroupOf_of_mem_family {K : Subgroup G} {𝒢 : Set (Subgroup G)}
    (hle : ∀ E ∈ 𝒢, E ≤ K) (hinv : ∀ E ∈ 𝒢, ∀ g ∈ K, A1b.conjSub g E ∈ 𝒢)
    (hcomm : ∀ E ∈ 𝒢, ∀ E' ∈ 𝒢, E ≠ E' → ∀ x ∈ E, ∀ y ∈ E', x * y = y * x)
    {E : Subgroup G} (hE : E ∈ 𝒢) : (E.subgroupOf K).IsSubnormal := by
  let 𝒢' : Set (Subgroup ↥K) := {F | ∃ E ∈ 𝒢, F = E.subgroupOf K}
  have hinv' : ∀ F ∈ 𝒢', ∀ g : ↥K, A1b.conjSub g F ∈ 𝒢' := by
    rintro F ⟨E₁, hE₁, rfl⟩ g
    exact ⟨A1b.conjSub (g : G) E₁, hinv E₁ hE₁ g g.2,
      b114_ElevenFourBFam_conjSub_subgroupOf g E₁⟩
  have hcomm' : ∀ F ∈ 𝒢', ∀ F' ∈ 𝒢', F ≠ F' → ∀ x ∈ F, ∀ y ∈ F', x * y = y * x := by
    rintro F ⟨E₁, hE₁, rfl⟩ F' ⟨E₂, hE₂, rfl⟩ hne x hx y hy
    exact Subtype.ext
      (hcomm E₁ hE₁ E₂ hE₂ (fun h => hne (by rw [h])) (x : G) hx (y : G) hy)
  exact Glue.isSubnormal_of_mem_family hinv' hcomm' ⟨E, hE, rfl⟩

theorem isSylowOf_inf_of_isSubnormal_rel {K Q E : Subgroup G} (hQ : IsSylowOf 2 Q K) (hEK : E ≤ K)
    (hE : (E.subgroupOf K).IsSubnormal) : IsSylowOf 2 (Q ⊓ E) E := by
  have hQ' : IsSylowOf 2 (Q.subgroupOf K) ⊤ := by
    have h := (Glue.isSylowOf_subgroupOf_iff' (S := Q) (X := K) hQ.1 le_rfl).mpr hQ
    rwa [Subgroup.subgroupOf_self] at h
  have h1 := Glue.isSylowOf_inf_of_isSubnormal hQ' hE
  have hqi : Q.subgroupOf K ⊓ E.subgroupOf K = (Q ⊓ E).subgroupOf K := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_inf]
  rw [hqi] at h1
  exact (Glue.isSylowOf_subgroupOf_iff' (S := Q ⊓ E) (X := E) (K := K)
    (inf_le_left.trans hQ.1) hEK).mp h1

theorem b114_ElevenFourBFam_false_of_sl_normalizes {Q E : Subgroup G}
    (hS : IsSylowOf 2 (Q ⊓ E) E) {n : ℕ} (hE : IsNaturalSLTwoModule ↥E n)
    (hnorm : E ≤ Subgroup.normalizer ((Q ⊓ E : Subgroup G) : Set G)) : False := by
  obtain ⟨-, hp, hodd⟩ := hS
  have hPn : ((Q ⊓ E).subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hnorm
  have hPp : IsPGroup 2 ((Q ⊓ E).subgroupOf E) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hPcore : (Q ⊓ E).subgroupOf E ≤ pCore 2 ↥E := le_sSup ⟨hPn, hPp⟩
  have hdvd : (pCore 2 ↥E).index ∣ ((Q ⊓ E).subgroupOf E).index :=
    Subgroup.index_dvd_of_le hPcore
  have hodd' : ¬ 2 ∣ (pCore 2 ↥E).index := fun h => hodd (h.trans hdvd)
  obtain ⟨φ, -⟩ := hE
  have hcard : (pCore 2 ↥E).index =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr φ.toEquiv
  exact hodd' (hcard ▸ Glue.two_dvd_card_sl2 (GaloisField 2 n))

@[expose] def bhsBlocks (K Q : Subgroup G) : Set (Subgroup G) :=
  {E | IsBTBlock K Q E ∧ ¬ E ≤ cStarIn K Q ∧
    ∀ F : Subgroup G, IsBTBlock K Q F → E ≤ F → F = E}

namespace IsBHSFamily

variable {K Q : Subgroup G} {𝒢 : Set (Subgroup G)}

theorem le (h : IsBHSFamily K Q 𝒢) {E : Subgroup G} (hE : E ∈ 𝒢) : E ≤ K :=
  (h.isBlock E hE).le

theorem isSubnormal (h : IsBHSFamily K Q 𝒢) {E : Subgroup G} (hE : E ∈ 𝒢) :
    (E.subgroupOf K).IsSubnormal :=
  isSubnormal_subgroupOf_of_mem_family (fun _ hE' => h.le hE') h.conj_mem h.comm hE

theorem isSylowOf_inf (h : IsBHSFamily K Q 𝒢) (hQ : IsSylowOf 2 Q K) {E : Subgroup G}
    (hE : E ∈ 𝒢) : IsSylowOf 2 (Q ⊓ E) E :=
  isSylowOf_inf_of_isSubnormal_rel hQ (h.le hE) (h.isSubnormal hE)

theorem charTwo (h : IsBHSFamily K Q 𝒢) (hK : CharTwo K) (hQ : IsSylowOf 2 Q K) {E : Subgroup G}
    (hE : E ∈ 𝒢) : CharTwo E :=
  charTwo_of_isBTBlock hK hQ (h.isBlock E hE)

theorem inClassX (h : IsBHSFamily K Q 𝒢) (hK : CharTwo K) (hQ : IsSylowOf 2 Q K) {E : Subgroup G}
    (hE : E ∈ 𝒢) : InClassX ↥E :=
  Glue.inClassX_of_isBTBlock (h.isBlock E hE) (h.charTwo hK hQ hE)

theorem isBlockOfInX (h : IsBHSFamily K Q 𝒢) (hK : CharTwo K) (hQ : IsSylowOf 2 Q K)
    {E : Subgroup G} (hE : E ∈ 𝒢) : IsBlockOfInX K E :=
  ⟨h.le hE, h.isSubnormal hE, h.inClassX hK hQ hE⟩

theorem not_le_cStarIn (h : IsBHSFamily K Q 𝒢) (hQ : IsSylowOf 2 Q K) {E : Subgroup G}
    (hE : E ∈ 𝒢) : ¬ E ≤ cStarIn K Q := by
  intro hEC
  have hS : IsSylowOf 2 (Q ⊓ E) E := h.isSylowOf_inf hQ hE
  rcases h.shape E hE with ⟨⟨n, _, hEsl⟩, hCE⟩ | ⟨m, hm, hEalt, ⟨e⟩⟩
  · refine b114_ElevenFourBFam_false_of_sl_normalizes hS hEsl fun x hx => ?_
    have hx' : x ∈ cStarIn K Q ⊓ E := ⟨hEC hx, hx⟩
    rw [hCE] at hx'
    exact hx'.1
  · have htop : (cStarIn K Q ⊓ E).subgroupOf E = ⊤ :=
      Subgroup.subgroupOf_eq_top.mpr (le_inf hEC le_rfl)
    rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at e
    exact Glue.false_of_alt_top hm hEalt e

theorem eq_of_le_of_le (h : IsBHSFamily K Q 𝒢) {E E' F : Subgroup G} (hE : E ∈ 𝒢)
    (hE' : E' ∈ 𝒢) (hFE : F ≤ E) (hFE' : F ≤ E')
    (hF : ¬ ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) : E = E' := by
  by_contra hne
  exact hF fun a ha b hb => h.comm E hE E' hE' hne a (hFE ha) b (hFE' hb)

theorem eq_of_le (h : IsBHSFamily K Q 𝒢) (hK : CharTwo K) (hQ : IsSylowOf 2 Q K)
    {E E' : Subgroup G} (hE : E ∈ 𝒢) (hE' : E' ∈ 𝒢) (hle : E ≤ E') : E = E' := by
  refine h.eq_of_le_of_le hE hE' le_rfl hle fun hab => ?_
  refine InClassX.commutator_ne_bot (h.inClassX hK hQ hE) (le_bot_iff.1 ?_)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [Subgroup.mem_bot, commutatorElement_def, hab a ha b hb]
  group

theorem mem_iff (h : IsBHSFamily K Q 𝒢) (hK : CharTwo K) (hQ : IsSylowOf 2 Q K)
    {E : Subgroup G} : E ∈ 𝒢 ↔ E ∈ bhsBlocks K Q := by
  constructor
  · intro hE
    refine ⟨h.isBlock E hE, h.not_le_cStarIn hQ hE, ?_⟩
    intro F hF hEF
    have hFnot : ¬ F ≤ cStarIn K Q := fun hFc => h.not_le_cStarIn hQ hE (hEF.trans hFc)
    obtain ⟨E', hE', hFE'⟩ := h.cover F hF hFnot
    have hEq : E = E' := h.eq_of_le hK hQ hE hE' (hEF.trans hFE')
    exact le_antisymm (by rw [← hEq] at hFE'; exact hFE') hEF
  · intro hE
    rw [bhsBlocks] at hE
    obtain ⟨hB, hnotC, hmax⟩ := hE
    obtain ⟨E', hE', hEE'⟩ := h.cover E hB hnotC
    have hEq : E' = E := hmax E' (h.isBlock E' hE') hEE'
    rw [← hEq]
    exact hE'

theorem pCoreOf_le_cStarIn (h : IsBHSFamily K Q 𝒢) (hQ : IsSylowOf 2 Q K)
    (hne : cStarIn K Q ≠ K) {E : Subgroup G} (hE : E ∈ 𝒢) : pCoreOf 2 E ≤ cStarIn K Q := by
  have hS : IsSylowOf 2 (Q ⊓ E) E := h.isSylowOf_inf hQ hE
  obtain ⟨T, hT⟩ := CFSG.CGT.PushingUpLit.sylow_of_isSylowOf hS
  have h1 : pCore 2 ↥E ≤ (T : Subgroup ↥E) := CFSG.fitting_pCore_le_sylow T
  rw [hT] at h1
  have h2 : pCoreOf 2 E ≤ Q ⊓ E := by
    rw [pCoreOf]
    calc (pCore 2 ↥E).map E.subtype ≤ ((Q ⊓ E).subgroupOf E).map E.subtype :=
          Subgroup.map_mono h1
      _ = Q ⊓ E := Subgroup.map_subgroupOf_eq_of_le inf_le_right
  have hQc : Q ≤ cStarIn K Q :=
    CFSG.CGT.PushingUpLit.BHS7.le_cStarIn_self ⟨hQ.1, hQ.2.1, hQ.2.2⟩ hne
  exact h2.trans (le_trans inf_le_left hQc)

end IsBHSFamily

end CFSG.LocalAnalysis.WeakClosure81
