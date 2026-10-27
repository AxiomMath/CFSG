module

public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.B2Thompson
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

variable {G : Type*} [Group G]

namespace MinParabolic

variable [Finite G] {H T M : Subgroup G}

theorem le_of_lt (h : MinParabolic H T M) {X : Subgroup G} (hTX : T ≤ X) (hXH : X < H) :
    X ≤ M := by
  obtain ⟨N, hN, hXN⟩ := exists_isMaxSubgroupIn hXH
  have := h.eq_of_maximal hN (hTX.trans hXN)
  rw [← this]
  exact hXN

theorem eq_of_not_le (h : MinParabolic H T M) {X : Subgroup G} (hTX : T ≤ X) (hXH : X ≤ H)
    (hXM : ¬ X ≤ M) : X = H := by
  by_contra hne
  exact hXM (h.le_of_lt hTX (lt_of_le_of_ne hXH hne))

theorem inf_normalizer_le (h : MinParabolic H T M) :
    H ⊓ Subgroup.normalizer (T : Set G) ≤ M := by
  by_contra hXM
  have := h.eq_of_not_le (X := H ⊓ Subgroup.normalizer (T : Set G))
    (le_inf h.isSylow.1 Subgroup.le_normalizer) inf_le_left hXM
  exact h.not_normal (this.symm.le.trans inf_le_right)

omit [Finite G] in
theorem kerIn_le_H (h : MinParabolic H T M) : kerIn M H ≤ H :=
  kerIn_le.trans h.maximal.1.le

theorem pCoreOf_le_kerIn (h : MinParabolic H T M) : pCoreOf 2 H ≤ kerIn M H :=
  le_kerIn_of_le_normalizer ((pCoreOf_two_le_of_isSylowTwoOf h.isSylow).trans h.le)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)

theorem pCoreOf_eq_pCoreOf_kerIn (h : MinParabolic H T M) :
    pCoreOf 2 H = pCoreOf 2 (kerIn M H) := by
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.pCoreOf_le_kerIn
      (h.kerIn_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans h.kerIn_le_H) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact (le_normalizer_kerIn M H).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)


theorem not_twoResidual_le_kerIn (h : MinParabolic H T M) :
    ¬ twoResidual H ≤ kerIn M H := by
  intro hK
  have hH : T ⊔ twoResidual H = H := sup_twoResidual_eq h.isSylow
  have : H ≤ M := by
    rw [← hH]
    exact sup_le h.le (hK.trans kerIn_le)
  exact absurd (lt_of_le_of_lt this h.maximal.1) (lt_irrefl _)

theorem le_kerIn_or_twoResidual_le (h : MinParabolic H T M) {Y : Subgroup G} (hYH : Y ≤ H)
    (hYn : H ≤ Subgroup.normalizer (Y : Set G)) : Y ≤ kerIn M H ∨ twoResidual H ≤ Y := by
  by_cases hY : Y ≤ M
  · exact Or.inl (le_kerIn_of_le_normalizer hY hYn)
  · right
    have hsup : T ⊔ Y = H :=
      h.eq_of_not_le le_sup_left (sup_le h.isSylow.1 hYH) fun hle => hY (le_sup_right.trans hle)
    exact twoResidual_le_of_isTwoQuotient hYH hYn
      (isTwoQuotient_of_sup_eq h.isSylow.2.1 hYn hsup)

theorem isSylowTwoOf_pCoreOf_kerIn (h : MinParabolic H T M) :
    IsSylowTwoOf (pCoreOf 2 H) (kerIn M H) := by
  have hJn : H ≤ Subgroup.normalizer (kerIn M H : Set G) := le_normalizer_kerIn M H
  have hR : IsSylowTwoOf (T ⊓ kerIn M H) (kerIn M H) :=
    isSylowTwoOf_inf_normal h.isSylow h.kerIn_le_H hJn
  have hTR : T ≤ Subgroup.normalizer ((T ⊓ kerIn M H : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, hJn (h.isSylow.1 ht)⟩
  have hfr := frattini_two h.kerIn_le_H hJn hR
  have hHN : H ≤ Subgroup.normalizer ((T ⊓ kerIn M H : Subgroup G) : Set G) := by
    by_contra hnot
    have hX : H ⊓ Subgroup.normalizer ((T ⊓ kerIn M H : Subgroup G) : Set G) = H := by
      refine h.eq_of_not_le (le_inf h.isSylow.1 hTR) inf_le_left fun hle => ?_
      have hHM : H ≤ M := hfr.trans (sup_le kerIn_le hle)
      exact absurd (lt_of_le_of_lt hHM h.maximal.1) (lt_irrefl _)
    exact hnot (hX.symm.le.trans inf_le_right)
  have h1 : T ⊓ kerIn M H ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans h.isSylow.1) hHN
      (hR.2.1)
  have h2 : pCoreOf 2 H ≤ T ⊓ kerIn M H :=
    le_inf (pCoreOf_two_le_of_isSylowTwoOf h.isSylow) h.pCoreOf_le_kerIn
  have : T ⊓ kerIn M H = pCoreOf 2 H := le_antisymm h1 h2
  rwa [this] at hR


theorem le_pCoreOf_of_isPGroup_of_le_kerIn (h : MinParabolic H T M) {X : Subgroup G}
    (hX : IsPGroup 2 X) (hXJ : X ≤ kerIn M H) : X ≤ pCoreOf 2 H := by
  obtain ⟨S, hS, hXS⟩ := exists_isSylowTwoOf_ge hX hXJ
  obtain ⟨g, hg, hgS⟩ := isSylowTwoOf_exists_conj h.isSylowTwoOf_pCoreOf_kerIn hS
  have hgH : g ∈ H := h.kerIn_le_H hg
  have : conjSub g (pCoreOf 2 H) = pCoreOf 2 H :=
    conjSub_eq_self (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hgH)
  rw [this] at hgS
  exact hXS.trans hgS.le

theorem le_kerIn_of_not_twoResidual_le (h : MinParabolic H T M) {C : Subgroup G} (hCH : C ≤ H)
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hK : ¬ twoResidual H ≤ C) :
    C ≤ kerIn M H :=
  (h.le_kerIn_or_twoResidual_le hCH hCn).resolve_right hK

theorem le_kerIn_and_isSylowTwoOf_of_le (h : MinParabolic H T M) {C : Subgroup G}
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hCM : C ≤ M) :
    C ≤ kerIn M H ∧ IsSylowTwoOf (pCoreOf 2 H ⊓ C) C := by
  have hCJ : C ≤ kerIn M H := le_kerIn_of_le_normalizer hCM hCn
  exact ⟨hCJ, isSylowTwoOf_inf_normal h.isSylowTwoOf_pCoreOf_kerIn hCJ
    (h.kerIn_le_H.trans hCn)⟩

theorem le_of_isTwoQuotient_of_pCoreOf_le (h : MinParabolic H T M) {C : Subgroup G}
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hQC : pCoreOf 2 H ≤ C)
    (hCM : C ≤ M) {D : Subgroup G} (hCD : C ≤ D) (hDH : D ≤ H)
    (hDn : H ≤ Subgroup.normalizer (D : Set G)) (hD2 : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ C) :
    D ≤ C := by
  have hS : IsSylowTwoOf (T ⊓ D) D := isSylowTwoOf_inf_normal h.isSylow hDH hDn
  have hDsup : C ⊔ (T ⊓ D) = D := sup_eq_of_isTwoQuotient hCD (hDH.trans hCn) hD2 hS
  have hfr := frattini_two hDH hDn hS
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ D : Subgroup G) : Set G) :=
    fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ht, hDn (h.isSylow.1 ht)⟩
  have hHN : H ≤ Subgroup.normalizer ((T ⊓ D : Subgroup G) : Set G) := by
    by_contra hnot
    have hX : H ⊓ Subgroup.normalizer ((T ⊓ D : Subgroup G) : Set G) = H := by
      refine h.eq_of_not_le (le_inf h.isSylow.1 hTN) inf_le_left fun hle => ?_
      have hDM : D ≤ M := by
        rw [← hDsup]
        exact sup_le hCM (inf_le_left.trans h.le)
      have hHM : H ≤ M := hfr.trans (sup_le hDM hle)
      exact absurd (lt_of_le_of_lt hHM h.maximal.1) (lt_irrefl _)
    exact hnot (hX.symm.le.trans inf_le_right)
  have hSQ : T ⊓ D ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans h.isSylow.1) hHN
      hS.2.1
  rw [← hDsup]
  exact sup_le le_rfl (hSQ.trans hQC)

end MinParabolic

namespace B6


theorem isElemAbelian_iff {A : Subgroup G} :
    IsElemAbelian 2 A ↔ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ ∀ a ∈ A, a ^ 2 = 1 := by
  constructor
  · intro h
    refine ⟨fun a ha b hb => ?_, h.2⟩
    have := h.1
    exact setLike_mul_comm ha hb
  · rintro ⟨hc, h2⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, h2⟩

theorem isElemAbelian_conjSub {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (conjSub g A) := by
  rw [isElemAbelian_iff] at hA ⊢
  refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
  · rw [mem_conjSub] at ha hb
    have := hA.1 _ ha _ hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  · rw [mem_conjSub] at ha
    have := hA.2 _ ha
    have e : a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    calc a ^ 2 = (g * (g⁻¹ * a * g) * g⁻¹) ^ 2 := by rw [← e]
      _ = g * (g⁻¹ * a * g) ^ 2 * g⁻¹ := conj_pow
      _ = 1 := by rw [this]; group

theorem card_conjSub (A : Subgroup G) (g : G) : Nat.card (conjSub g A) = Nat.card A :=
  Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv.symm

theorem isMaxElemAbelian_conjSub {H A : Subgroup G} (hA : IsMaxElemAbelian H A) (g : G) :
    IsMaxElemAbelian (conjSub g H) (conjSub g A) := by
  obtain ⟨hAH, hAe, hmax⟩ := hA
  refine ⟨(conjSub g).le_iff_le.mpr hAH, isElemAbelian_conjSub hAe g, fun B hBH hB => ?_⟩
  have h1 : conjSub g⁻¹ B ≤ H := by
    have := (conjSub g⁻¹).le_iff_le.mpr hBH
    have e : conjSub g⁻¹ (conjSub g H) = H := by
      rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
    rwa [e] at this
  have h2 := hmax _ h1 (isElemAbelian_conjSub hB g⁻¹)
  rw [card_conjSub] at h2
  rw [card_conjSub]
  exact h2

theorem thompsonJ_conjSub (H : Subgroup G) (g : G) :
    thompsonJ (conjSub g H) = conjSub g (thompsonJ H) := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hA' : IsMaxElemAbelian H (conjSub g⁻¹ A) := by
      have := isMaxElemAbelian_conjSub hA g⁻¹
      rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
    have : conjSub g⁻¹ A ≤ thompsonJ H := le_iSup₂_of_le _ hA' le_rfl
    have h2 := (conjSub g).le_iff_le.mpr this
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h2
  · unfold thompsonJ
    simp only [OrderIso.map_iSup]
    exact iSup_le fun A => iSup_le fun hA =>
      le_iSup₂_of_le (conjSub g A) (isMaxElemAbelian_conjSub hA g) le_rfl

theorem le_normalizer_thompsonJ (H : Subgroup G) :
    H ≤ Subgroup.normalizer (thompsonJ H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have e : conjSub g H = H := conjSub_eq_self (Subgroup.le_normalizer hg)
  have := thompsonJ_conjSub H g
  rw [e] at this
  exact this.symm

theorem thompsonJ_le (S : Subgroup G) : thompsonJ S ≤ S := iSup₂_le fun _ hA => hA.1

theorem le_thompsonJ {S A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ thompsonJ S :=
  le_iSup₂_of_le A hA le_rfl

theorem thompsonJ_eq_of_le [Finite G] {S R : Subgroup G} (hJ : thompsonJ S ≤ R) (hRS : R ≤ S) :
    thompsonJ R = thompsonJ S := by
  obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian S
  apply le_antisymm
  · refine iSup₂_le fun B hB => ?_
    have hB' : IsMaxElemAbelian S B := by
      refine ⟨hB.1.trans hRS, hB.2.1, fun C hCS hC => ?_⟩
      have h1 : Nat.card A₀ ≤ Nat.card B := hB.2.2 A₀ ((le_thompsonJ hA₀).trans hJ) hA₀.2.1
      exact (hA₀.2.2 C hCS hC).trans h1
    exact le_thompsonJ hB'
  · refine iSup₂_le fun A hA => ?_
    have hA' : IsMaxElemAbelian R A :=
      ⟨(le_thompsonJ hA).trans hJ, hA.2.1, fun B hBR hB => hA.2.2 B (hBR.trans hRS) hB⟩
    exact le_thompsonJ hA'

theorem isPGroup_of_isElemAbelian {A : Subgroup G} (hA : IsElemAbelian 2 A) : IsPGroup 2 A :=
  CFSG.Open.IsElemAbelian.isPGroup hA

theorem exists_conj_isMaxElemAbelian_of_sylow [Finite G] {H T A : Subgroup G}
    (hT : IsSylowTwoOf T H) (hA : IsMaxElemAbelian H A) :
    ∃ g ∈ H, IsMaxElemAbelian T (conjSub g A) := by
  obtain ⟨S, hS, hAS⟩ := exists_isSylowTwoOf_ge (isPGroup_of_isElemAbelian hA.2.1) hA.1
  obtain ⟨g, hg, hgS⟩ := isSylowTwoOf_exists_conj hS hT
  refine ⟨g, hg, ?_⟩
  refine ⟨?_, isElemAbelian_conjSub hA.2.1 g, fun B hBT hB => ?_⟩
  · rw [hgS]
    exact (conjSub g).le_iff_le.mpr hAS
  · rw [card_conjSub]
    exact hA.2.2 B (hBT.trans hT.1) hB

theorem isMaxElemAbelian_of_sylow [Finite G] {H T A : Subgroup G} (hT : IsSylowTwoOf T H)
    (hA : IsMaxElemAbelian T A) : IsMaxElemAbelian H A := by
  refine ⟨hA.1.trans hT.1, hA.2.1, fun B hBH hB => ?_⟩
  obtain ⟨S, hS, hBS⟩ := exists_isSylowTwoOf_ge (isPGroup_of_isElemAbelian hB) hBH
  obtain ⟨g, hg, hgS⟩ := isSylowTwoOf_exists_conj hS hT
  have h1 : conjSub g B ≤ T := by
    rw [hgS]
    exact (conjSub g).le_iff_le.mpr hBS
  have := hA.2.2 _ h1 (isElemAbelian_conjSub hB g)
  rwa [card_conjSub] at this

theorem thompsonJ_le_of_sylow [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    thompsonJ T ≤ thompsonJ H :=
  iSup₂_le fun _ hA => le_thompsonJ (isMaxElemAbelian_of_sylow hT hA)

theorem thompsonJ_le_of_sylow_of_le [Finite G] {H T L : Subgroup G} (hT : IsSylowTwoOf T H)
    (hJL : thompsonJ T ≤ L) (hL : H ≤ Subgroup.normalizer (L : Set G)) : thompsonJ H ≤ L := by
  refine iSup₂_le fun A hA => ?_
  obtain ⟨g, hg, hgA⟩ := exists_conj_isMaxElemAbelian_of_sylow hT hA
  have h1 : conjSub g A ≤ L := (le_thompsonJ hgA).trans hJL
  have h2 : conjSub g⁻¹ (conjSub g A) ≤ L := by
    have h3 : conjSub g⁻¹ L = L := conjSub_eq_self (hL (H.inv_mem hg))
    rw [← h3]
    exact (conjSub g⁻¹).le_iff_le.mpr h1
  rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at h2



theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup G} {g c : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
  have key := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * v := by group

theorem le_normalizer_centralizer {H V : Subgroup G} (hHV : H ≤ Subgroup.normalizer (V : Set G)) :
    H ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  intro g hg
  refine mem_normalizer_of_forall_mem (fun c hc => ?_) (fun c hc => ?_)
  · exact conj_mem_centralizer_of_mem_normalizer (hHV hg) hc
  · simpa using conj_mem_centralizer_of_mem_normalizer (hHV (H.inv_mem hg)) hc

theorem thompsonJ_le_baum (S : Subgroup G) : thompsonJ S ≤ baum S := by
  refine le_inf (thompsonJ_le S) ?_
  rw [Subgroup.le_centralizer_iff]
  intro x hx
  have h1 : x ∈ centerOf (thompsonJ S) :=
    (Subgroup.closure_le (centerOf (thompsonJ S))).mpr (fun y hy => hy.1) hx
  exact h1.2


end B6

open scoped commutatorElement

namespace MinParabolic

variable [Finite G] {H T M : Subgroup G}

theorem commutator_lt_iff_le_pCoreOf (h : MinParabolic H T M) {N : Subgroup G} (hNT : N ≤ T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) :
    ⁅twoResidual H, N⁆ < twoResidual H ↔ N ≤ pCoreOf 2 H := by
  set K := twoResidual H with hK
  have hKH : K ≤ H := twoResidual_le H
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_twoResidual H
  have hNH : N ≤ H := hNT.trans h.isSylow.1
  have hAK : ⁅K, N⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp (hNH.trans hHK)
  constructor
  · intro hlt
    set A := ⁅K, N⁆ with hA
    have hKA : K ≤ Subgroup.normalizer (A : Set G) := Subgroup.normalizer_commutator_ge_left K N
    have hNA : N ≤ Subgroup.normalizer (A : Set G) := Subgroup.normalizer_commutator_ge_right K N
    have hTA : T ≤ Subgroup.normalizer (A : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hA, Subgroup.map_commutator,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHK (h.isSylow.1 ht)),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTN ht)]
    set X := A ⊔ N with hX
    have hXH : X ≤ H := sup_le (hAK.trans hKH) hNH
    have hconj : ∀ g ∈ K, conjSub g X ≤ X := by
      intro g hg
      show Subgroup.map (MulAut.conj g).toMonoidHom (A ⊔ N) ≤ A ⊔ N
      rw [Subgroup.map_sup]
      refine sup_le ?_ ?_
      · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hKA hg)).le.trans le_sup_left
      · rintro _ ⟨n, hn, rfl⟩
        have : (MulAut.conj g).toMonoidHom n = ⁅g, n⁆ * n := conj_eq_commutatorElement_mul
        rw [this]
        exact (A ⊔ N).mul_mem (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hg hn))
          (Subgroup.mem_sup_right hn)
    have hKX : K ≤ Subgroup.normalizer (X : Set G) := fun g hg =>
      mem_normalizer_of_conjSub_le (hconj g hg) (hconj g⁻¹ (K.inv_mem hg))
    have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
      Subgroup.inf_normalizer_le_normalizer_sup A N ⟨hTA ht, hTN ht⟩
    have hXn : H ≤ Subgroup.normalizer (X : Set G) := by
      calc H = T ⊔ K := (sup_twoResidual_eq h.isSylow).symm
        _ ≤ _ := sup_le hTX hKX
    rcases h.le_kerIn_or_twoResidual_le hXH hXn with hXJ | hKX'
    · exact le_pCoreOf_of_isPGroup_of_le_kerIn h (h.isSylow.2.1.to_le hNT)
        (le_sup_right.trans hXJ)
    · exfalso
      have hsup : (N ⊓ K) ⊔ A = K := by
        refine le_antisymm (sup_le inf_le_right hAK) fun k hk => ?_
        have hk' : k ∈ ((A ⊔ N : Subgroup G) : Set G) := hKX' hk
        rw [Subgroup.coe_mul_of_right_le_normalizer_left A N hNA] at hk'
        obtain ⟨a, ha, n, hn, rfl⟩ := hk'
        have hnK : n ∈ K := by
          have := K.mul_mem (K.inv_mem (hAK ha)) hk
          simpa using this
        exact ((N ⊓ K) ⊔ A).mul_mem (Subgroup.mem_sup_right ha)
          (Subgroup.mem_sup_left ⟨hn, hnK⟩)
      have h2 := isTwoQuotient_of_sup_eq (h.isSylow.2.1.to_le (inf_le_left.trans hNT)) hKA hsup
      have := twoResidual_le_of_isTwoQuotient hAK hKA h2
      rw [hK, twoResidual_twoResidual] at this
      exact absurd hlt (not_lt_of_ge this)
  · intro hNQ
    have hAQ : ⁅K, N⁆ ≤ pCoreOf 2 H := by
      rw [Subgroup.commutator_le]
      intro k hk n hn
      have hn' : n ∈ pCoreOf 2 H := hNQ hn
      have hkn : k * n * k⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk)) n).mp hn'
      exact (pCoreOf 2 H).mul_mem hkn ((pCoreOf 2 H).inv_mem hn')
    refine lt_of_le_of_ne hAK fun heq => ?_
    apply h.not_twoResidual_le_kerIn
    exact (heq ▸ hAQ).trans h.pCoreOf_le_kerIn

end MinParabolic

namespace MinParabolic

variable [Finite G] {H T M : Subgroup G}

theorem pCoreOf_le_centralizer {V : Subgroup G} (hV : IsTwoReducedIn H V) :
    pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) := by
  refine hV.2.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 H)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H) fun d hd => ?_
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

theorem not_twoResidual_le_centralizer {V : Subgroup G} (hV : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    ¬ twoResidual H ≤ Subgroup.centralizer (V : Set G) := fun hK =>
  hHV (hV.2.2.2 H le_rfl Subgroup.le_normalizer fun d hd => by
    obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient H d hd
    exact ⟨k, hK hk⟩)

theorem inf_centralizer_le_kerIn (h : MinParabolic H T M) {V : Subgroup G}
    (hV : IsTwoReducedIn H V) (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    H ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn M H := by
  have hCn : H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer hV.2.1 hg⟩
  exact h.le_kerIn_of_not_twoResidual_le inf_le_left hCn fun hK =>
    not_twoResidual_le_centralizer hV hHV (hK.trans inf_le_right)

theorem inf_centralizer_eq_pCoreOf (h : MinParabolic H T M) {V : Subgroup G}
    (hV : IsTwoReducedIn H V) (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 H := by
  refine le_antisymm ?_ (le_inf (pCoreOf_two_le_of_isSylowTwoOf h.isSylow)
    (pCoreOf_le_centralizer hV))
  exact le_pCoreOf_of_isPGroup_of_le_kerIn h (h.isSylow.2.1.to_le inf_le_left)
    ((inf_le_inf_right _ h.isSylow.1).trans (h.inf_centralizer_le_kerIn hV hHV))

theorem le_pCoreOf_iff_le_centralizer (h : MinParabolic H T M) {V : Subgroup G}
    (hV : IsTwoReducedIn H V) (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) (N : Subgroup G) :
    N ≤ pCoreOf 2 H ↔ N ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  rw [h.inf_centralizer_eq_pCoreOf hV hHV]

end MinParabolic

namespace MinParabolic

variable [Finite G] {H T M : Subgroup G}

omit [Finite G] in
theorem le_pCoreOf_of_isTwoReduced {V : Subgroup G} (hV : IsTwoReducedIn H V) :
    V ≤ pCoreOf 2 H :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hV.1 hV.2.1
    (isPGroup_of_isElemAbelian hV.2.2.1)

theorem tfae_thompsonJ (h : MinParabolic H T M) {V : Subgroup G} (hV : IsTwoReducedIn H V)
    (hHV : ¬ H ≤ Subgroup.centralizer (V : Set G)) :
    List.TFAE [⁅V, thompsonJ T⁆ = ⊥, thompsonJ T = thompsonJ (pCoreOf 2 H),
      baum T = baum (pCoreOf 2 H)] := by
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf h.isSylow
  have hinf := h.inf_centralizer_eq_pCoreOf hV hHV
  have hVT : V ≤ T := (le_pCoreOf_of_isTwoReduced hV).trans hQT
  have hcomm : ⁅V, thompsonJ T⁆ = ⊥ ↔ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  have h1 : thompsonJ T ≤ Subgroup.centralizer (V : Set G) ↔ thompsonJ T ≤ pCoreOf 2 H := by
    rw [← hinf]
    exact ⟨fun hh => le_inf (thompsonJ_le T) hh, fun hh => hh.trans inf_le_right⟩
  tfae_have 1 ↔ 2 := by
    rw [hcomm, h1]
    constructor
    · intro hh
      exact (thompsonJ_eq_of_le hh hQT).symm
    · intro hh
      rw [hh]
      exact thompsonJ_le _
  tfae_have 1 → 3 := by
    intro hh
    rw [hcomm] at hh
    have hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G) := le_inf (thompsonJ_le T) hh
    rw [baum_eq_baum_centralizer hV.2.2.1 hVT hJ, hinf]
  tfae_have 3 → 1 := by
    intro hh
    rw [hcomm]
    have : thompsonJ T ≤ pCoreOf 2 H := by
      calc thompsonJ T ≤ baum T := thompsonJ_le_baum T
        _ = baum (pCoreOf 2 H) := hh
        _ ≤ pCoreOf 2 H := inf_le_left
    exact h1.mpr this
  tfae_finish

theorem thompsonJ_eq_sup (h : MinParabolic H T M) {V : Subgroup G} (hV : IsTwoReducedIn H V)
    (hJ : ⁅V, thompsonJ T⁆ ≠ ⊥) :
    thompsonJ H = twoResidual H ⊔ thompsonJ T := by
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf h.isSylow
  have hJT : thompsonJ T ≤ thompsonJ H := thompsonJ_le_of_sylow h.isSylow
  have hnotJ : ¬ thompsonJ H ≤ kerIn M H := by
    intro hle
    apply hJ
    have h1 : thompsonJ T ≤ pCoreOf 2 H :=
      le_pCoreOf_of_isPGroup_of_le_kerIn h (h.isSylow.2.1.to_le (thompsonJ_le T)) (hJT.trans hle)
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact h1.trans (pCoreOf_le_centralizer hV)
  have hKJ : twoResidual H ≤ thompsonJ H :=
    (h.le_kerIn_or_twoResidual_le (thompsonJ_le H) (le_normalizer_thompsonJ H)).resolve_left hnotJ
  apply le_antisymm
  · have hTn : T ≤ Subgroup.normalizer ((twoResidual H ⊔ thompsonJ T : Subgroup G) : Set G) :=
      fun t ht => Subgroup.inf_normalizer_le_normalizer_sup _ _
        ⟨(le_normalizer_twoResidual H) (h.isSylow.1 ht), le_normalizer_thompsonJ T ht⟩
    have hHn : H ≤ Subgroup.normalizer ((twoResidual H ⊔ thompsonJ T : Subgroup G) : Set G) := by
      calc H = T ⊔ twoResidual H := (sup_twoResidual_eq h.isSylow).symm
        _ ≤ _ := sup_le hTn (le_sup_left.trans Subgroup.le_normalizer)
    exact thompsonJ_le_of_sylow_of_le h.isSylow le_sup_right hHn
  · exact sup_le hKJ hJT

theorem isFFModule_autOn_of_not_commutator_eq_bot (h : MinParabolic H T M) {V : Subgroup G}
    (hV : IsTwoReducedIn H V) (hJ : ⁅V, thompsonJ T⁆ ≠ ⊥) :
    @IsFFModule V (commGroupOfElemAbelian hV.2.2.1) (autOn H V) := by
  have hVT : V ≤ T := (le_pCoreOf_of_isTwoReduced hV).trans
    (pCoreOf_two_le_of_isSylowTwoOf h.isSylow)
  have hnot : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) := fun hle =>
    hJ (by rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hle)
  obtain ⟨A, hA, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    refine hnot (iSup₂_le fun A hA => ?_)
    by_contra hAV
    exact hcon ⟨A, hA, hAV⟩
  exact isFFModule_autOn hV.2.2.1 hVT hV.2.1 (hA.1.trans h.isSylow.1) hA hAV

end MinParabolic

end CFSG.Quasithin
