module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LieType.BorelTits
  (pCoreOf_le pCoreOf_isPGroup le_pCoreOf_of_le_normalizer le_normalizer_pCoreOf
    normalizer_le_normalizer_pCoreOf)
open scoped Pointwise

@[expose] def InS889 {G : Type} [Group G] [Finite G] (D : Data G) (K Y : Subgroup G) : Prop :=
  K ≤ Y ∧ Y ≤ D.M ∧ Y ≤ K ⊔ pCoreOf 2 Y ∧ pCoreOf 2 Y ≠ ⊥ ∧
    ∃ N' : Subgroup G, rankThreeIsMaxTwoLocal N' ∧ Y ≤ N' ∧ N' ≠ D.M

theorem r889_inS_of_le {G : Type} [Group G] [Finite G] (D : Data G) {K Y W : Subgroup G}
    (hKY : K ≤ Y) (hYM : Y ≤ D.M) (hW : IsPGroup 2 W) (hW0 : W ≠ ⊥) (hWY : W ≤ Y)
    (hYW : Y ≤ normalizer (W : Set G)) (hYKW : Y ≤ K ⊔ W)
    (hN : ∃ N' : Subgroup G, rankThreeIsMaxTwoLocal N' ∧ Y ≤ N' ∧ N' ≠ D.M) :
    InS889 D K Y ∧ W ≤ pCoreOf 2 Y := by
  have hWO : W ≤ pCoreOf 2 Y := le_pCoreOf_of_le_normalizer 2 hWY hYW hW
  refine ⟨⟨hKY, hYM, hYKW.trans (sup_le_sup_left hWO K), fun h => hW0 ?_, hN⟩, hWO⟩
  rw [h] at hWO
  exact le_bot_iff.1 hWO

theorem r889_twoLocal_ne_top {G : Type} [Group G] [Finite G] (D : Data G) {X : Subgroup G}
    (hX : IsTwoLocal X) : X ≠ ⊤ :=
  haveI := D.standing.simple
  CFSG.RankThreeCoreUniqueness.Helpers.twoLocal_ne_top D.standing.nonab X hX

theorem r889_of_parts {G : Type} [Group G] [Finite G]
    (D : Data G) (h881 : R881 D) (h882 : R882 D) (h885 : R885 D) (h869M : R869M D)
    (hOmega : S889Omega D) (hO2 : S889O2 D) (hChief : S889Chief D) (hJ2 : S889J2Aut D)
    (hMod : S889Mod2 D) : R889 D := by
  intro L P hS
  by_contra hPL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := D.standing.simple
  obtain ⟨ω, hω⟩ := hOmega L P hS hPL
  have hLM : L ≤ D.M := r889_le_M hS
  have hKM : K889 L ω ≤ D.M := (r889_K889_le_left L ω).trans hLM
  have hnormL : D.M ≤ normalizer (L : Set G) := r889_normalizes_of_inputs h882 h885 hS
  have hUL : calMOf L = {D.M} := h869M L (Or.inl hS.mem) (r889_not_thin_of_r881 h881 hS)
  have hLloc : ∀ X : Subgroup G, IsTwoLocal X → L ≤ X → X ≤ D.M := by
    intro X hX hLX
    obtain ⟨N', hN', hXN'⟩ := r889_exists_maxTwoLocal_ge hX
    have hmem : N' ∈ calMOf L := ⟨hN', hLX.trans hXN'⟩
    rw [hUL] at hmem
    exact (Set.mem_singleton_iff.1 hmem) ▸ hXN'
  have hHtop : centralizer ({ω} : Set G) ≠ ⊤ := by
    intro htop
    have hω1 : ω ≠ 1 := by
      intro h
      have := hω.order
      rw [h, orderOf_one] at this
      omega
    have hcent : ω ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ centralizer ({ω} : Set G) := htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.1 hg ω rfl).symm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact hω1 (by simpa [h] using hcent)
    · obtain ⟨a, b, hab⟩ := D.standing.nonab
      have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  obtain ⟨N, hNc, hHN⟩ := (IsCoatomic.eq_top_or_exists_le_coatom _).resolve_left hHtop
  have hNM : N ≠ D.M := fun h => hω.notM (h ▸ hHN)
  have hKN : K889 L ω ≤ N := (r889_K889_le_centralizer L ω).trans hHN
  have hU0 : pCoreOf 2 N ≠ ⊥ := hO2 L P ω hω N ⟨hNc, hHN⟩
  have hUp : IsPGroup 2 (pCoreOf 2 N) := pCoreOf_isPGroup 2 N
  have hNnorm : N ≤ normalizer (pCoreOf 2 N : Set G) := le_normalizer_pCoreOf 2 N
  have hNeq : N = normalizer (pCoreOf 2 N : Set G) := by
    by_contra hne
    exact r889_twoLocal_ne_top D (r889_isTwoLocal_normalizer hU0 hUp)
      (hNc.2 _ (lt_of_le_of_ne hNnorm hne))
  have hNmax : rankThreeIsMaxTwoLocal N := by
    refine ⟨⟨pCoreOf 2 N, hU0, hUp, hNeq⟩, fun X hX hNX => ?_⟩
    by_contra hne
    exact r889_twoLocal_ne_top D hX (hNc.2 X (lt_of_le_of_ne hNX (Ne.symm hne)))
  have hKnormU : K889 L ω ≤ normalizer (pCoreOf 2 N : Set G) := hKN.trans hNnorm
  have hUM : pCoreOf 2 N ⊓ D.M ≠ ⊥ := hMod L P ω hω _ hUp hU0 hKnormU
  have hVp : IsPGroup 2 (pCoreOf 2 N ⊓ D.M : Subgroup G) := hUp.to_le inf_le_left
  have hKnormV : K889 L ω ≤ normalizer ((pCoreOf 2 N ⊓ D.M : Subgroup G) : Set G) :=
    fun x hx => r889_mem_normalizer_inf (hKnormU hx) (Subgroup.le_normalizer (hKM hx))
  have hVN : pCoreOf 2 N ⊓ D.M ≤ N := inf_le_left.trans (pCoreOf_le 2 N)
  have hY0 : InS889 D (K889 L ω) (K889 L ω ⊔ (pCoreOf 2 N ⊓ D.M)) :=
    (r889_inS_of_le D (K := K889 L ω) (Y := K889 L ω ⊔ (pCoreOf 2 N ⊓ D.M))
      (W := pCoreOf 2 N ⊓ D.M) le_sup_left (sup_le hKM inf_le_right) hVp hUM le_sup_right
      (sup_le hKnormV Subgroup.le_normalizer) le_rfl ⟨N, hNmax, sup_le hKN hVN, hNM⟩).1
  obtain ⟨Y, hYS, hYmax⟩ := Set.exists_max_image {Y : Subgroup G | InS889 D (K889 L ω) Y}
    (fun Y => Nat.card (pCoreOf 2 Y)) (Set.toFinite _) ⟨_, hY0⟩
  obtain ⟨hKY, hYM, hYKR, hR0, N₁, hN₁, hYN₁, hN₁M⟩ := hYS
  have hRp : IsPGroup 2 (pCoreOf 2 Y) := pCoreOf_isPGroup 2 Y
  have hRY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y
  have hYnormR : Y ≤ normalizer (pCoreOf 2 Y : Set G) := le_normalizer_pCoreOf 2 Y
  have hRM : pCoreOf 2 Y ≤ D.M := hRY.trans hYM
  have hKnormR : K889 L ω ≤ normalizer (pCoreOf 2 Y : Set G) := hKY.trans hYnormR
  have hRloc : IsTwoLocal (normalizer (pCoreOf 2 Y : Set G)) :=
    r889_isTwoLocal_normalizer hR0 hRp
  have hNR : normalizer (pCoreOf 2 Y : Set G) ≤ D.M := by
    obtain ⟨S, ⟨hSp, hSM, hYnormS, hRS⟩, hSmax⟩ := Set.exists_max_image
      {S : Subgroup G | IsPGroup 2 S ∧ S ≤ D.M ∧ Y ≤ normalizer (S : Set G) ∧ pCoreOf 2 Y ≤ S}
      (fun S => Nat.card S) (Set.toFinite _) ⟨pCoreOf 2 Y, hRp, hRM, hYnormR, le_rfl⟩
    rcases hRS.eq_or_lt with hEq | hLt
    ·
      subst hEq
      have hOLp : IsPGroup 2 (pCoreOf 2 L) := pCoreOf_isPGroup 2 L
      have hMnormO : D.M ≤ normalizer (pCoreOf 2 L : Set G) :=
        hnormL.trans (normalizer_le_normalizer_pCoreOf 2 L)
      have hRnormO : pCoreOf 2 Y ≤ normalizer (pCoreOf 2 L : Set G) := hRM.trans hMnormO
      have hS'p : IsPGroup 2 ↥(pCoreOf 2 Y ⊔ pCoreOf 2 L) := r889_isPGroup_sup hRp hOLp hRnormO
      have hS'mem : pCoreOf 2 Y ⊔ pCoreOf 2 L ∈
          {S : Subgroup G | IsPGroup 2 S ∧ S ≤ D.M ∧ Y ≤ normalizer (S : Set G) ∧
            pCoreOf 2 Y ≤ S} :=
        ⟨hS'p, sup_le hRM ((pCoreOf_le 2 L).trans hLM),
          fun y hy => r889_mem_normalizer_sup (hYnormR hy) (hMnormO (hYM hy)), le_sup_left⟩
      have hle : Nat.card ↥(pCoreOf 2 Y ⊔ pCoreOf 2 L) ≤ Nat.card ↥(pCoreOf 2 Y) :=
        hSmax _ hS'mem
      have heq : pCoreOf 2 Y = pCoreOf 2 Y ⊔ pCoreOf 2 L :=
        Subgroup.eq_of_le_of_card_ge le_sup_left hle
      have hOL : pCoreOf 2 L ≤ pCoreOf 2 Y := by
        have h : pCoreOf 2 L ≤ pCoreOf 2 Y ⊔ pCoreOf 2 L := le_sup_right
        rwa [← heq] at h
      have hcent := hJ2 L P ω hω (pCoreOf 2 Y) hRp hRM hKnormR hOL
      have hLnormR : L ≤ normalizer (pCoreOf 2 Y : Set G) := by
        have key : ∀ l ∈ L, ∀ r ∈ pCoreOf 2 Y, l * r * l⁻¹ ∈ pCoreOf 2 Y := by
          intro l hl r hr
          have h1 : r * l * r⁻¹ * l⁻¹ ∈ pCoreOf 2 L := hcent r hr l hl
          have h2 : l * r * l⁻¹ * r⁻¹ ∈ pCoreOf 2 Y := by
            have := inv_mem (hOL h1)
            simpa [mul_assoc] using this
          have := mul_mem h2 hr
          simpa [mul_assoc] using this
        intro l hl
        rw [Subgroup.mem_normalizer_iff]
        intro h
        exact ⟨key l hl h, fun hh => by simpa [mul_assoc] using key l⁻¹ (inv_mem hl) _ hh⟩
      exact hLloc _ hRloc hLnormR
    ·
      obtain ⟨x, hxS, hxN, hxR⟩ := r889_exists_mem_normalizer_of_lt hSp hLt
      have hTp : IsPGroup 2 (S ⊓ normalizer (pCoreOf 2 Y : Set G) : Subgroup G) :=
        hSp.to_le inf_le_left
      have hRT : pCoreOf 2 Y ≤ S ⊓ normalizer (pCoreOf 2 Y : Set G) :=
        le_inf hRS Subgroup.le_normalizer
      have hRTlt : pCoreOf 2 Y < S ⊓ normalizer (pCoreOf 2 Y : Set G) :=
        lt_of_le_of_ne hRT fun h => hxR (h ▸ ⟨hxS, hxN⟩)
      have hYnormT : Y ≤ normalizer ((S ⊓ normalizer (pCoreOf 2 Y : Set G) : Subgroup G) : Set G) :=
        fun y hy => r889_mem_normalizer_inf (hYnormS hy) (Subgroup.le_normalizer (hYnormR hy))
      have hTM : S ⊓ normalizer (pCoreOf 2 Y : Set G) ≤ D.M := inf_le_left.trans hSM
      have hT0 : S ⊓ normalizer (pCoreOf 2 Y : Set G) ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (h ▸ hRT))
      have hno : ∀ N'' : Subgroup G, rankThreeIsMaxTwoLocal N'' →
          Y ⊔ (S ⊓ normalizer (pCoreOf 2 Y : Set G)) ≤ N'' → N'' = D.M := by
        intro N'' hN'' hYsN''
        by_contra hne
        obtain ⟨hInS, hTO⟩ := r889_inS_of_le D (K := K889 L ω)
          (Y := Y ⊔ (S ⊓ normalizer (pCoreOf 2 Y : Set G)))
          (W := S ⊓ normalizer (pCoreOf 2 Y : Set G)) (hKY.trans le_sup_left)
          (sup_le hYM hTM) hTp hT0 le_sup_right (sup_le hYnormT Subgroup.le_normalizer)
          (sup_le (hYKR.trans (sup_le le_sup_left (hRT.trans le_sup_right))) le_sup_right)
          ⟨N'', hN'', hYsN'', hne⟩
        have h1 : Nat.card (pCoreOf 2 (Y ⊔ (S ⊓ normalizer (pCoreOf 2 Y : Set G)))) ≤
            Nat.card (pCoreOf 2 Y) := hYmax _ hInS
        have h2 := r889_card_lt_of_lt hRTlt
        have h3 := Subgroup.card_le_of_le hTO
        omega
      obtain ⟨N'', hN'', hN''le⟩ := r889_exists_maxTwoLocal_ge hRloc
      have hYsN : Y ⊔ (S ⊓ normalizer (pCoreOf 2 Y : Set G)) ≤ normalizer (pCoreOf 2 Y : Set G) :=
        sup_le hYnormR inf_le_right
      exact (hno N'' hN'' (hYsN.trans hN''le)) ▸ hN''le
  have hchief : N₁ ≤ pCoreOf 2 N₁ ⊔ (N₁ ⊓ D.M) :=
    hChief L P ω hω N₁ ⟨hN₁, hKY.trans hYN₁⟩ hN₁M
  have hU₁p : IsPGroup 2 (pCoreOf 2 N₁) := pCoreOf_isPGroup 2 N₁
  have hU₁le : pCoreOf 2 N₁ ≤ N₁ := pCoreOf_le 2 N₁
  have hN₁norm : N₁ ≤ normalizer (pCoreOf 2 N₁ : Set G) := le_normalizer_pCoreOf 2 N₁
  have hV₁p : IsPGroup 2 (pCoreOf 2 N₁ ⊓ D.M : Subgroup G) := hU₁p.to_le inf_le_left
  have hYnormV₁ : Y ≤ normalizer ((pCoreOf 2 N₁ ⊓ D.M : Subgroup G) : Set G) :=
    fun y hy => r889_mem_normalizer_inf (hN₁norm (hYN₁ hy)) (Subgroup.le_normalizer (hYM hy))
  have hRnormV₁ : pCoreOf 2 Y ≤ normalizer ((pCoreOf 2 N₁ ⊓ D.M : Subgroup G) : Set G) :=
    hRY.trans hYnormV₁
  have hR₂p : IsPGroup 2 ↥(pCoreOf 2 Y ⊔ (pCoreOf 2 N₁ ⊓ D.M)) :=
    r889_isPGroup_sup hRp hV₁p hRnormV₁
  have hR₂0 : pCoreOf 2 Y ⊔ (pCoreOf 2 N₁ ⊓ D.M) ≠ ⊥ :=
    fun h => hR0 (le_bot_iff.1 (h ▸ (le_sup_left : pCoreOf 2 Y ≤ _)))
  obtain ⟨hInS₂, hR₂O⟩ := r889_inS_of_le D (K := K889 L ω)
    (Y := Y ⊔ (pCoreOf 2 N₁ ⊓ D.M)) (W := pCoreOf 2 Y ⊔ (pCoreOf 2 N₁ ⊓ D.M))
    (hKY.trans le_sup_left) (sup_le hYM inf_le_right) hR₂p hR₂0
    (sup_le (hRY.trans le_sup_left) le_sup_right)
    (sup_le (fun y hy => r889_mem_normalizer_sup (hYnormR hy) (hYnormV₁ hy))
      ((le_sup_right : pCoreOf 2 N₁ ⊓ D.M ≤ pCoreOf 2 Y ⊔ (pCoreOf 2 N₁ ⊓ D.M)).trans
        Subgroup.le_normalizer))
    (sup_le (hYKR.trans (sup_le_sup_left le_sup_left _)) (le_sup_right.trans le_sup_right))
    ⟨N₁, hN₁, sup_le hYN₁ (inf_le_left.trans hU₁le), hN₁M⟩
  have h5 : Nat.card (pCoreOf 2 (Y ⊔ (pCoreOf 2 N₁ ⊓ D.M))) ≤ Nat.card (pCoreOf 2 Y) :=
    hYmax _ hInS₂
  have hReq : pCoreOf 2 Y = pCoreOf 2 Y ⊔ (pCoreOf 2 N₁ ⊓ D.M) :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (le_trans (Subgroup.card_le_of_le hR₂O) h5)
  have hV₁R : pCoreOf 2 N₁ ⊓ D.M ≤ pCoreOf 2 Y := by
    have h : pCoreOf 2 N₁ ⊓ D.M ≤ pCoreOf 2 Y ⊔ (pCoreOf 2 N₁ ⊓ D.M) := le_sup_right
    rwa [← hReq] at h
  have hU₁R : pCoreOf 2 N₁ ≤ pCoreOf 2 Y := by
    by_contra hnot
    have hRnormU₁ : pCoreOf 2 Y ≤ normalizer (pCoreOf 2 N₁ : Set G) :=
      (hRY.trans hYN₁).trans hN₁norm
    have hAp : IsPGroup 2 ↥(pCoreOf 2 Y ⊔ pCoreOf 2 N₁) := r889_isPGroup_sup hRp hU₁p hRnormU₁
    have hRA : pCoreOf 2 Y < pCoreOf 2 Y ⊔ pCoreOf 2 N₁ :=
      lt_of_le_of_ne le_sup_left fun h => hnot (by
        have h' : pCoreOf 2 N₁ ≤ pCoreOf 2 Y ⊔ pCoreOf 2 N₁ := le_sup_right
        rwa [← h] at h')
    obtain ⟨x, hxA, hxN, hxR⟩ := r889_exists_mem_normalizer_of_lt hAp hRA
    obtain ⟨r, hr, u, hu, hru⟩ := r889_mem_sup_of_le_normalizer hRnormU₁ hxA
    have hu_norm : u ∈ normalizer (pCoreOf 2 Y : Set G) := by
      have hu' : u = r⁻¹ * x := by rw [← hru]; group
      rw [hu']
      exact mul_mem (inv_mem (Subgroup.le_normalizer hr)) hxN
    have huR : u ∈ pCoreOf 2 Y := hV₁R ⟨hu, hNR hu_norm⟩
    exact hxR (by rw [← hru]; exact mul_mem hr huR)
  have hN₁le : N₁ ≤ D.M := hchief.trans (sup_le (hU₁R.trans hRM) inf_le_right)
  exact hN₁M (hN₁.2 D.M D.maxLocal.1 hN₁le).symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
