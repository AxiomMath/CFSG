module

public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenInputs
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenBar
public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenAMain
public import CFSG.LocalAnalysis.WeakClosure81.SevenSevenARank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open scoped commutatorElement

theorem pCore_eq_bot_of_isL2OrSz {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 1 < n)
    (hS : IsL2OrSz S n) : CFSG.pCore 2 S = ⊥ := by
  haveI : IsSimpleGroup S := CFSG.Quasithin.E2.isSimpleGroup_of_psl_or_sz hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore 2 S) with hbot | htop
  · exact hbot
  · exfalso
    have hp : IsPGroup 2 (CFSG.pCore 2 S) := CFSG.pCore_isPGroup (p := 2) (G := S)
    rw [htop] at hp
    exact not_isPGroup_two_of_isL2OrSz hn hS
      (hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S))

variable {G : Type} [Group G] [Finite G] {V H E : Subgroup G}

theorem exists_conj_dSet_of_isConj_barSub (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hconj : ∀ s ∈ barSub (kSub V H E) φ V, ∀ t ∈ barSub (kSub V H E) φ V, s ≠ 1 → t ≠ 1 →
      IsConj s t) :
    ∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹ := by
  have hJK : pCoreOf 2 (kSub V H E) ≤ kSub V H E :=
    CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E)
  refine exists_conj_of_isConj_barSet h.toHyp73 hJK hφ ?_
  intro x hx y hy
  rw [barSet_dSet_eq h.toHyp73 h.transitive hφ] at hx hy
  obtain ⟨s, hs, hsx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨t, ht, hty⟩ := Group.mem_conjugatesOfSet_iff.mp hy
  have hsV : s ∈ barSub (kSub V H E) φ V := hs.1
  have hs1 : s ≠ 1 := by simpa using hs.2
  have htV : t ∈ barSub (kSub V H E) φ V := ht.1
  have ht1 : t ≠ 1 := by simpa using ht.2
  exact (hty.symm).trans ((hconj t htV s hsV ht1 hs1).trans hsx)

section Core


theorem commute_of_isPGroup_barSub_sup_conj (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) (g : X)
    (hg : IsPGroup 2 ↥(barSub (kSub V H E) φ V ⊔ conjSubgroup (barSub (kSub V H E) φ V) g)) :
    ∀ a ∈ barSub (kSub V H E) φ V, ∀ b ∈ conjSubgroup (barSub (kSub V H E) φ V) g,
      a * b = b * a := by
  obtain ⟨k, rfl⟩ := hφ.surjective g
  intro a ha b hb
  have hcomm : ⁅V, conjSubgroup V (k : G)⁆ = ⊥ :=
    (isPGroup_barSub_sup_conj_iff h hφ k).mp hg
  obtain ⟨v, hv, rfl⟩ := mem_barSub.mp ha
  have hb' : b ∈ barSub (kSub V H E) φ (conjSubgroup V (k : G)) := by
    rw [barSub_conjSubgroup (K := kSub V H E) φ V k]
    exact hb
  obtain ⟨w, hw, rfl⟩ := mem_barSub.mp hb'
  have hmem : ⁅(v : G), (w : G)⁆ ∈ ⁅V, conjSubgroup V (k : G)⁆ :=
    Subgroup.commutator_mem_commutator hv hw
  rw [hcomm] at hmem
  have h1 : ⁅(v : G), (w : G)⁆ = 1 := Subgroup.mem_bot.mp hmem
  have hvw : v * w = w * v := Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp h1)
  calc φ v * φ w = φ (v * w) := (map_mul φ v w).symm
    _ = φ (w * v) := by rw [hvw]
    _ = φ w * φ v := map_mul φ w v

theorem pRank_barSub_eq_of_isL2OrSz_sup (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ) {n : ℕ}
    (hn : 1 < n) (k : ↥(kSub V H E))
    (hL : IsL2OrSz
      ↥(barSub (kSub V H E) φ V ⊔ conjSubgroup (barSub (kSub V H E) φ V) (φ k)) n) :
    CFSG.pRank 2 ↥(barSub (kSub V H E) φ V) = n := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let J : Subgroup G := pCoreOf 2 K
  let Y : Subgroup G := V ⊔ conjSubgroup V (k : G)
  let Lbar : Subgroup X := barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k)
  change IsBarMap K J φ at hφ
  change IsL2OrSz ↥Lbar n at hL
  change CFSG.pRank 2 ↥(barSub K φ V) = n
  have hVK : V ≤ K := le_kSub h.mem
  have hkH : (k : G) ∈ H := kSub_le_of_forall_le h.omega_le k.2
  have hconjK : conjSubgroup V (k : G) ≤ K :=
    le_kSub (conjSubgroup_mem_omegaSet h.le h.normal h.mem hkH)
  have hYK : Y ≤ K := sup_le hVK hconjK
  have hVY : V ≤ Y := le_sup_left
  have hbarY : barSub K φ Y = Lbar := by
    change barSub K φ (V ⊔ conjSubgroup V (k : G)) =
      barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k)
    rw [barSub_sup hVK hconjK φ, barSub_conjSubgroup (K := K) φ V k]
  let ψ : ↥Y →* ↥Lbar :=
    (φ.comp (Subgroup.inclusion hYK)).codRestrict Lbar (fun y => by
      change φ (Subgroup.inclusion hYK y) ∈ Lbar
      rw [← hbarY]
      exact mem_barSub.mpr ⟨Subgroup.inclusion hYK y, y.2, rfl⟩)
  have hψ : Function.Surjective ψ := by
    intro x
    have hx : (x : X) ∈ barSub K φ Y := by rw [hbarY]; exact x.2
    obtain ⟨a, ha, haφ⟩ := mem_barSub.mp hx
    refine ⟨⟨a, ha⟩, ?_⟩
    apply Subtype.ext
    show φ (Subgroup.inclusion hYK ⟨a, ha⟩) = (x : X)
    rw [← haφ]
    exact congrArg φ (Subtype.ext (by rw [Subgroup.coe_inclusion]))
  have hJ2 : IsPGroup 2 J := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
  have hKNJ : K ≤ Subgroup.normalizer (J : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K
  have hYNJ : Y ≤ Subgroup.normalizer (J : Set G) := hYK.trans hKNJ
  have hnorm : Y ≤ Subgroup.normalizer ((Y ⊓ J : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer hYNJ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hJY : Y ⊓ J ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) inf_le_left hnorm
      (hJ2.to_le inf_le_right)
  have hkerJ : ∀ a : ↥Y, ψ a = 1 ↔ (a : G) ∈ J := by
    intro a
    constructor
    · intro h
      have h1 : (ψ a : X) = 1 := by rw [h]; rfl
      exact (hφ.ker_iff (Subgroup.inclusion hYK a)).mp h1
    · intro haJ
      apply Subtype.ext
      show φ (Subgroup.inclusion hYK a) = 1
      exact (hφ.ker_iff (Subgroup.inclusion hYK a)).mpr haJ
  have hLbot : CFSG.pCore 2 ↥Lbar = ⊥ := pCore_eq_bot_of_isL2OrSz hn hL
  have hPsub : ((pCoreOf 2 Y).subgroupOf Y) = CFSG.pCore 2 ↥Y :=
    Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _
  have hPmap_bot : ((pCoreOf 2 Y).subgroupOf Y).map ψ = ⊥ := by
    have hnormal : (((pCoreOf 2 Y).subgroupOf Y).map ψ).Normal := by
      rw [hPsub]
      exact (inferInstance : (CFSG.pCore 2 ↥Y).Normal).map ψ hψ
    have hpgroup : IsPGroup 2 (((pCoreOf 2 Y).subgroupOf Y).map ψ) := by
      rw [hPsub]
      exact (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map ψ
    have hle := CFSG.LieType.BorelTits.le_pCore (r := 2) hnormal hpgroup
    rw [hLbot] at hle
    exact le_bot_iff.mp hle
  have hker : ∀ a : ↥Y, ψ a = 1 ↔ (a : G) ∈ pCoreOf 2 Y := by
    intro a
    rw [hkerJ a]
    constructor
    · intro haJ
      exact hJY (Subgroup.mem_inf.mpr ⟨a.2, haJ⟩)
    · intro haP
      have haPsub : a ∈ (pCoreOf 2 Y).subgroupOf Y := Subgroup.mem_subgroupOf.mpr haP
      have hmem : ψ a ∈ ((pCoreOf 2 Y).subgroupOf Y).map ψ := ⟨a, haPsub, rfl⟩
      rw [hPmap_bot] at hmem
      exact (hkerJ a).mp (Subgroup.mem_bot.mp hmem)
  have hne : ⁅V, conjSubgroup V (k : G)⁆ ≠ ⊥ := by
    intro hcomm
    have hP : IsPGroup 2 ↥Lbar := (isPGroup_barSub_sup_conj_iff h hφ k).mpr hcomm
    exact not_isPGroup_two_of_isL2OrSz hn hL hP
  have hstep := pRank_image_eq_pRank_of_sup_conj h k.2 hne ψ hψ hker
  let A : Subgroup ↥Lbar := (V.subgroupOf Y).map ψ
  have hrankL : CFSG.pRank 2 ↥Lbar = n := pRank_eq_of_isL2OrSz hn hL
  have hmap : A.map Lbar.subtype = barSub K φ V := by
    change (((V.subgroupOf Y).map ψ).map Lbar.subtype) = barSub K φ V
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨v, hv, hvψ⟩ := Subgroup.mem_map.mp hy
      rw [← hvψ]
      exact mem_barSub.mpr ⟨Subgroup.inclusion hYK v, Subgroup.mem_subgroupOf.mp hv, rfl⟩
    · intro hx
      obtain ⟨v, hv, hvφ⟩ := mem_barSub.mp hx
      refine Subgroup.mem_map.mpr ⟨ψ ⟨(v : G), hVY hv⟩, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨⟨(v : G), hVY hv⟩,
          Subgroup.mem_subgroupOf.mpr hv, rfl⟩
      · rw [← hvφ]
        exact congrArg φ (Subtype.ext rfl)
  have hAV : CFSG.pRank 2 ↥A = CFSG.pRank 2 ↥(barSub K φ V) := by
    have h1 := CFSG.GH74.GLS.Bg.pRank_mulEquiv (p := 2) one_lt_two
      (Subgroup.equivMapOfInjective A Lbar.subtype Lbar.subtype_injective)
    rwa [hmap] at h1
  exact hAV.symm.trans (hstep.trans hrankL)

theorem barSub_eq_of_le_root (hGen : TwoConjugateGeneration) (h : Hyp711 V H E) {X : Type}
    [Group X] {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hbig : 2 < Nat.card (barSub (kSub V H E) φ V)) {n : ℕ} (hn : 1 < n) {W : Subgroup X}
    (hVW : barSub (kSub V H E) φ V ≤ W) (hW : Nat.card W = 2 ^ n) {g : X}
    (hL : IsL2OrSz ↥(W ⊔ conjSubgroup W g) n) :
    barSub (kSub V H E) φ V = W := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let K : Subgroup G := kSub V H E
  let M : Subgroup X := W ⊔ conjSubgroup W g
  change IsBarMap K (pCoreOf 2 K) φ at hφ
  change barSub K φ V ≤ W at hVW
  change IsL2OrSz ↥M n at hL
  change barSub K φ V = W
  have hSM : barSub K φ V ≤ M := hVW.trans le_sup_left
  let A : Subgroup ↥M := (barSub K φ V).subgroupOf M
  have hA : IsElemAbelian 2 A :=
    CFSG.Open.IsElemAbelian.comap (isElemAbelian_barSub h.elemAbelian φ) M.subtype_injective
  have hcardA : 2 < Nat.card A := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv]
    exact hbig
  obtain ⟨g', hg'⟩ := hGen ↥M n hn hL A hA hcardA
  have hAeq : A.map M.subtype = barSub K φ V := Subgroup.map_subgroupOf_eq_of_le hSM
  have hcomp : M.subtype.comp (MulAut.conj (g')⁻¹).toMonoidHom =
      (MulAut.conj ((g' : X))⁻¹).toMonoidHom.comp M.subtype := by
    ext a
    simp [MulAut.conj_apply]
  have hconjmap : (conjSubgroup A g').map M.subtype =
      conjSubgroup (A.map M.subtype) (g' : X) := by
    change (conjSubgroup ((barSub K φ V).subgroupOf M) g').map M.subtype =
      conjSubgroup (((barSub K φ V).subgroupOf M).map M.subtype) (g' : X)
    rw [CFSG.Quasithin.conjSubgroup, CFSG.Quasithin.conjSubgroup, Subgroup.map_map,
      Subgroup.map_map, hcomp]
  have htop : (⊤ : Subgroup ↥M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapEq : (A ⊔ conjSubgroup A g').map M.subtype =
      barSub K φ V ⊔ conjSubgroup (barSub K φ V) (g' : X) := by
    rw [Subgroup.map_sup, hAeq, hconjmap, hAeq]
  have hM : barSub K φ V ⊔ conjSubgroup (barSub K φ V) (g' : X) = M := by
    have h := congrArg (Subgroup.map M.subtype) hg'
    rw [hmapEq, htop] at h
    exact h
  obtain ⟨k, hk⟩ := hφ.surjective (g' : X)
  have hMk : barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k) = M := by
    rw [hk]
    exact hM
  have hLk : IsL2OrSz ↥(barSub K φ V ⊔ conjSubgroup (barSub K φ V) (φ k)) n := by
    rw [hMk]
    exact hL
  have hrank : CFSG.pRank 2 ↥(barSub K φ V) = n :=
    pRank_barSub_eq_of_isL2OrSz_sup h hφ hn k hLk
  have hcardV : Nat.card (barSub K φ V) = 2 ^ n :=
    card_eq_two_pow_of_pRank_eq (isElemAbelian_barSub h.elemAbelian φ) hrank
  exact Subgroup.eq_of_le_of_card_ge hVW (by simp [hW, hcardV])

theorem seven_eleven_big (hTim : TimmesfeldTIRootInput) (hGen : TwoConjugateGeneration)
    (hA6 : SevenElevenASixInput G) (h : Hyp711 V H E) {X : Type} [Group X]
    {φ : ↥(kSub V H E) →* X} (hφ : IsBarMap (kSub V H E) (pCoreOf 2 (kSub V H E)) φ)
    (hbig : 2 < Nat.card (barSub (kSub V H E) φ V)) :
    (∀ u ∈ dSet V H E, ∀ v ∈ dSet V H E, ∃ k ∈ kSub V H E, u = k * v * k⁻¹) ∧
      SevenElevenAlt X (barSub (kSub V H E) φ V) := by
  haveI : Finite X := Finite.of_surjective φ hφ.surjective
  let S : Subgroup X := barSub (kSub V H E) φ V
  have hroot : CFSG.Timmesfeld.IsRootInvolutionSet
      (Group.conjugatesOfSet ((S : Set X) \ {1})) := by
    have hrootSet := isRootInvolutionSet_barSet h.toHyp73 hφ
    rwa [barSet_dSet_eq h.toHyp73 h.transitive hφ] at hrootSet
  have hcomm : ∀ g : X, IsPGroup 2 ↥(S ⊔ conjSubgroup S g) →
      ∀ a ∈ S, ∀ b ∈ conjSubgroup S g, a * b = b * a :=
    fun g hg => commute_of_isPGroup_barSub_sup_conj h hφ g hg
  obtain ⟨hconj, halt⟩ := hTim X S (isElemAbelian_barSub h.elemAbelian φ) hbig
    (isTI_barSub h hφ) (normalClosure_barSub_eq_top h hφ) (pCore_eq_bot_of_isBarMap hφ)
    (fusionOddCore_le_center_of_two_lt_card h hφ hbig) hroot hcomm
  refine ⟨exists_conj_dSet_of_isConj_barSub h hφ hconj, ?_⟩
  rcases halt with hA6shape | hlin | ⟨n, hn, W, hVW, -, hWcard, ⟨g, hg⟩, hshape, hodd⟩
  · unfold SevenElevenASixShape at hA6shape
    obtain ⟨he, h4, hT⟩ := hA6shape
    exact Or.inr (Or.inr (Or.inl ⟨hA6 V H E h X φ hφ he h4, ⟨he, h4, hT⟩⟩))
  · exact Or.inr (Or.inl hlin)
  · have hVeqW : barSub (kSub V H E) φ V = W :=
      barSub_eq_of_le_root hGen h hφ hbig hn hVW hWcard hg
    exact Or.inl ⟨⟨n, by rw [hVeqW]; exact hshape⟩, by rw [hVeqW]; exact hodd⟩

end Core

end CFSG.LocalAnalysis.WeakClosure81
