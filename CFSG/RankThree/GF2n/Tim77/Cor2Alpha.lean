module

public import CFSG.RankThree.GF2n.Tim77.Cor2AlphaBasic
public import CFSG.RankThree.GF2n.Tim77.Cor2AlphaDefs
public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.RankThree.GF2n.Tim77.Cor2One
public import CFSG.Timmesfeld.CorollaryB
public import CFSG.LargeExtraspecial.S8CorBUniv

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75 CFSG.Timmesfeld.RootInvolutions CFSG.Open Subgroup
open CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem alpha_conj_le_normalClosure (A : Subgroup G) (g : G) :
    conjSubgroup g A ≤ normalClosure (A : Set G) := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h := Subgroup.Normal.conj_mem (normalClosure_normal : (normalClosure (A : Set G)).Normal)
    (g⁻¹ * x * g) (subset_normalClosure hx) g
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h

theorem alpha_le_centralizer_of_comm {S T : Subgroup G}
    (h : ∀ a ∈ S, ∀ b ∈ T, a * b = b * a) : S ≤ centralizer (T : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (h a ha b hb).symm

theorem alpha_le_centralizer_conj {A : Subgroup G} {g : G}
    (hg : conjSubgroup g A ≤ centralizer (A : Set G)) :
    A ≤ centralizer (conjSubgroup g A : Set G) :=
  alpha_le_centralizer_of_comm fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hg hb) a ha

theorem alpha_mem_of_mul_mem {A : Subgroup G} (hTI : IsTI A) {k a b : G}
    (ha : a ∈ conjSubgroup k A) (hb : b ∈ conjSubgroup k A) (hab : a * b ∈ A)
    (hab1 : a * b ≠ 1) : a ∈ A := by
  have hmem : a * b ∈ A ⊓ conjSubgroup k A := Subgroup.mem_inf.mpr ⟨hab, mul_mem ha hb⟩
  have h1 : A ⊓ conjSubgroup k A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hmem
    exact hab1 hmem
  rw [CFSG.RankThree.GF2n.conjSubgroup_eq_of_isTI hTI h1] at ha
  exact ha

theorem alpha_not_mem_conj {A : Subgroup G} (hTI : IsTI A) {g t : G}
    (hgA : conjSubgroup g A ≠ A) (ht : t ∈ A) (ht1 : t ≠ 1) : t ∉ conjSubgroup g A := by
  intro h
  have hm : t ∈ A ⊓ conjSubgroup g A := Subgroup.mem_inf.mpr ⟨ht, h⟩
  rw [CFSG.RankThree.GF2n.inf_conjSubgroup_eq_bot_of_isTI hTI hgA, Subgroup.mem_bot] at hm
  exact ht1 hm

theorem alpha_exists_conj_elem {A : Subgroup G} (hTI : IsTI A) {g t : G} (ht : t ∈ A)
    (ht1 : t ≠ 1) (hgA : conjSubgroup g A ≠ A) :
    ∃ x ∈ conjSubgroup g A, x ≠ 1 ∧ x ∉ A := by
  have hx : g * t * g⁻¹ ∈ conjSubgroup g A := by
    rw [mem_conjSubgroup, show g⁻¹ * (g * t * g⁻¹) * g = t by group]
    exact ht
  refine ⟨g * t * g⁻¹, hx, ?_, ?_⟩
  · intro h
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro h
    have hm : g * t * g⁻¹ ∈ A ⊓ conjSubgroup g A := Subgroup.mem_inf.mpr ⟨h, hx⟩
    rw [CFSG.RankThree.GF2n.inf_conjSubgroup_eq_bot_of_isTI hTI hgA, Subgroup.mem_bot] at hm
    apply ht1
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [hm]; group

theorem alpha_exists_conj_le_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hne : ⁅WAC A, WAC A⁆ ≠ ⊥) :
    ∃ g : G, conjSubgroup g A ≤ centralizer (A : Set G) ∧ conjSubgroup g A ≠ A := by
  by_contra! h
  apply hne
  rw [wac_eq_self hA h, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact alpha_le_centralizer_of_comm fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem alpha_conj_le_centralizer_of_comm {A : Subgroup G} (hroot : IsRootType 2 A) {c t τ : G}
    (ht : t ∈ A) (ht1 : t ≠ 1) (hτ : τ ∈ conjSubgroup c A) (hτ1 : τ ≠ 1)
    (hc : τ * t = t * τ) : conjSubgroup c A ≤ centralizer (A : Set G) := by
  have ht' : t ∈ conjSubgroup 1 A := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_one]
    exact ht
  have h := commute_of_mem_conj hroot hτ hτ1 ht' ht1 hc
  simp only [CFSG.RankThree.GF2n.conjSubgroup_one] at h
  exact alpha_le_centralizer_of_comm h

theorem alpha_false_of_involution {K : Subgroup G} (hodd : Odd (Nat.card K)) {y : G}
    (hy : y ∈ K) (hy2 : y * y = 1) (hy1 : y ≠ 1) : False := by
  have hord : orderOf (⟨y, hy⟩ : K) = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      show y ^ 2 = 1
      rw [sq]
      exact hy2
    · intro h
      apply hy1
      have := congrArg Subtype.val h
      simpa using this
  have h2 : orderOf (⟨y, hy⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
  rw [hord] at h2
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨k, hk⟩ := h2
  omega

theorem alpha_exists_noncomm {A : Subgroup G} (hne : ⁅WAC A, WAC A⁆ ≠ ⊥) :
    ∃ g h : G, conjSubgroup g A ≤ centralizer (A : Set G) ∧
      conjSubgroup h A ≤ centralizer (A : Set G) ∧
      ∃ x ∈ conjSubgroup g A, ∃ y ∈ conjSubgroup h A, x * y ≠ y * x := by
  by_contra! hcon
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hgen : ∀ g : G, conjSubgroup g A ≤ centralizer (A : Set G) →
      conjSubgroup g A ≤ centralizer (WAC A : Set G) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hle : WAC A ≤ centralizer ({x} : Set G) := by
      unfold WAC
      refine iSup₂_le fun h hh => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact hcon g h hg hh x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) x (Set.mem_singleton x)).symm
  exact iSup₂_le fun g hg => hgen g hg

theorem isConj_of_mem {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥)
    {t τ : G} (ht : t ∈ A) (ht1 : t ≠ 1) (hτ : τ ∈ A) (hτ1 : τ ≠ 1) : IsConj t τ := by
  by_cases htτ : t = τ
  · rw [htτ]
  obtain ⟨g, hgC, hgA⟩ := alpha_exists_conj_le_centralizer hA hne
  obtain ⟨x, hxB, hx1, hxA⟩ := alpha_exists_conj_elem hTI ht ht1 hgA
  have ht2 : t * t = 1 := by rw [← sq]; exact hA.2 t ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hτ2 : τ * τ = 1 := by rw [← sq]; exact hA.2 τ hτ
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hx2 : x * x = 1 := by
    rw [← sq]
    exact (isElemAbelian_conj hA g).2 x hxB
  have hAB : ∀ a ∈ A, ∀ b ∈ conjSubgroup g A, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hgC hb) a ha
  have hcomm_tτ : t * τ = τ * t := congrArg Subtype.val (hA.1.is_comm.comm ⟨t, ht⟩ ⟨τ, hτ⟩)
  have hxt : x * t = t * x := (hAB t ht x hxB).symm
  have hxτ : x * τ = τ * x := (hAB τ hτ x hxB).symm
  have hk0 : conjSubgroup 1 A ≤ centralizer (conjSubgroup g A : Set G) := by
    rw [CFSG.RankThree.GF2n.conjSubgroup_one]
    exact alpha_le_centralizer_conj hgC
  have htB : t ∉ conjSubgroup g A := alpha_not_mem_conj hTI hgA ht ht1
  have hτB : τ ∉ conjSubgroup g A := alpha_not_mem_conj hTI hgA hτ hτ1
  have hTt := isConj_mul_of_not_mem hA hTI hroot hW hne (g := 1) (k := g) (τ := t) hk0
    (by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact ht) htB
  have hTτ := isConj_mul_of_not_mem hA hTI hroot hW hne (g := 1) (k := g) (τ := τ) hk0
    (by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact hτ) hτB
  have hP : IsConj t (t * x) := hTt x hxB
  have hQ : IsConj τ (τ * x) := hTτ x hxB
  obtain ⟨c, hc⟩ := isConj_iff.mp hP
  obtain ⟨c', hc'⟩ := isConj_iff.mp hQ
  have hPc : t * x ∈ conjSubgroup c A := by
    rw [mem_conjSubgroup, ← hc, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
    exact ht
  have hQc : τ * x ∈ conjSubgroup c' A := by
    rw [mem_conjSubgroup, ← hc', show c'⁻¹ * (c' * τ * c'⁻¹) * c' = τ by group]
    exact hτ
  have hPx1 : t * x ≠ 1 := by
    intro h
    apply hxA
    rw [eq_inv_of_mul_eq_one_right h, htinv]
    exact ht
  have hQx1 : τ * x ≠ 1 := by
    intro h
    apply hxA
    rw [eq_inv_of_mul_eq_one_right h, hτinv]
    exact hτ
  have hPQ : t * x * (τ * x) = t * τ := by
    calc t * x * (τ * x) = t * (x * τ) * x := by group
      _ = t * (τ * x) * x := by rw [hxτ]
      _ = t * τ * (x * x) := by group
      _ = t * τ := by rw [hx2, mul_one]
  have hQP : τ * x * (t * x) = τ * t := by
    calc τ * x * (t * x) = τ * (x * t) * x := by group
      _ = τ * (t * x) * x := by rw [hxt]
      _ = τ * t * (x * x) := by group
      _ = τ * t := by rw [hx2, mul_one]
  have htτ1 : t * τ ≠ 1 := by
    intro h
    apply htτ
    rw [eq_inv_of_mul_eq_one_right h, htinv]
  have hτt1 : τ * t ≠ 1 := by
    intro h
    apply htτ
    rw [eq_inv_of_mul_eq_one_left h, htinv]
  have hcc : ∀ a ∈ conjSubgroup c A, ∀ b ∈ conjSubgroup c' A, a * b = b * a :=
    commute_of_mem_conj hroot hPc hPx1 hQc hQx1 (by rw [hPQ, hQP, hcomm_tτ])
  have hk1 : conjSubgroup c A ≤ centralizer (conjSubgroup c' A : Set G) :=
    alpha_le_centralizer_of_comm hcc
  have hk2 : conjSubgroup c' A ≤ centralizer (conjSubgroup c A : Set G) :=
    alpha_le_centralizer_of_comm fun a ha b hb => (hcc b hb a ha).symm
  have hPnot : t * x ∉ conjSubgroup c' A := by
    intro h
    apply hxA
    have hmem : t * x ∈ A :=
      alpha_mem_of_mul_mem hTI h hQc (by rw [hPQ]; exact mul_mem ht hτ)
        (by rw [hPQ]; exact htτ1)
    rw [show x = t⁻¹ * (t * x) by group]
    exact A.mul_mem (A.inv_mem ht) hmem
  have hQnot : τ * x ∉ conjSubgroup c A := by
    intro h
    apply hxA
    have hmem : τ * x ∈ A :=
      alpha_mem_of_mul_mem hTI h hPc (by rw [hQP]; exact mul_mem hτ ht)
        (by rw [hQP]; exact hτt1)
    rw [show x = τ⁻¹ * (τ * x) by group]
    exact A.mul_mem (A.inv_mem hτ) hmem
  have hS4P := isConj_mul_of_not_mem hA hTI hroot hW hne (g := c) (k := c') (τ := t * x)
    hk1 hPc hPnot
  have hS4Q := isConj_mul_of_not_mem hA hTI hroot hW hne (g := c') (k := c) (τ := τ * x)
    hk2 hQc hQnot
  have hP2 : IsConj (t * x) (t * τ) := by
    have h := hS4P (τ * x) hQc
    rw [hPQ] at h
    exact h
  have hQ2 : IsConj (τ * x) (t * τ) := by
    have h := hS4Q (t * x) hPc
    rw [hQP, ← hcomm_tτ] at h
    exact h
  exact hP.trans (hP2.trans (hQ2.symm.trans hQ.symm))

theorem alpha_isConj_of_mem_conj {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥)
    {t g x : G} (ht : t ∈ A) (ht1 : t ≠ 1) (hx : x ∈ conjSubgroup g A) (hx1 : x ≠ 1) :
    IsConj t x := by
  have ha : g⁻¹ * x * g ∈ A := mem_conjSubgroup.mp hx
  have ha1 : g⁻¹ * x * g ≠ 1 := by
    intro h
    apply hx1
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  have h1 : IsConj (g⁻¹ * x * g) x := isConj_iff.mpr ⟨g, by group⟩
  exact (isConj_of_mem hA hTI hroot hW hne ht ht1 ha ha1).trans h1

theorem corBSetup {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥)
    {t : G} (ht : t ∈ A) (ht1 : t ≠ 1) : CFSG.Timmesfeld.CorB.Setup t := by
  have ht2 : t * t = 1 := by rw [← sq]; exact hA.2 t ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hWC : WAC A ≤ centralizer (A : Set G) := iSup₂_le fun g hg => hg
  have hcent : CFSG.Timmesfeld.CorB.weakClosure t ≤ WAC A := by
    unfold CFSG.Timmesfeld.CorB.weakClosure
    rw [Subgroup.closure_le]
    rintro τ ⟨hcomm, hconj⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hτc : τ ∈ conjSubgroup c A := by
      rw [mem_conjSubgroup, ← hc, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
      exact ht
    have hτ1 : τ ≠ 1 := by
      intro h
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc, h]; group
    exact conj_le_WAC (alpha_conj_le_centralizer_of_comm hroot ht ht1 hτc hτ1 hcomm) hτc
  have hPG : IsPGroup 2 ↥(WAC A) := by
    rw [wac_eq_weakClosure A]
    apply isPGroup_weakClosure hA
    rw [← wac_eq_weakClosure A]
    exact hW
  have hVP : IsPGroup 2 ↥(CFSG.Timmesfeld.CorB.weakClosure t) := IsPGroup.to_le hPG hcent
  have hVV : ⁅CFSG.Timmesfeld.CorB.weakClosure t, CFSG.Timmesfeld.CorB.weakClosure t⁆ ≤ A :=
    (Subgroup.commutator_mono hcent hcent).trans hW
  have hAW : ⁅A, WAC A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWC hw) a ha).symm
  refine
    { orderOf_eq := orderOf_eq_prime (hA.2 t ht) ht1
      isPGroup := hVP
      class_two := le_bot_iff.mp ((Subgroup.commutator_mono hVV hcent).trans hAW.le)
      fusion := ?_ }
  intro τ hcomm hconj hτt
  by_cases hτA : τ ∈ A
  · have htτ : t * τ ∈ A := A.mul_mem ht hτA
    have htτ1 : t * τ ≠ 1 := by
      intro h
      apply hτt
      rw [eq_inv_of_mul_eq_one_right h, htinv]
    exact isConj_of_mem hA hTI hroot hW hne ht ht1 htτ htτ1
  · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
    have hτc : τ ∈ conjSubgroup c A := by
      rw [mem_conjSubgroup, ← hc, show c⁻¹ * (c * t * c⁻¹) * c = t by group]
      exact ht
    have hτ1 : τ ≠ 1 := by
      intro h
      apply ht1
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [hc, h]; group
    have hle := alpha_conj_le_centralizer_of_comm hroot ht ht1 hτc hτ1 hcomm
    have hS4 := isConj_mul_of_not_mem hA hTI hroot hW hne (g := c) (k := 1) (τ := τ)
      (by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact hle) hτc
      (by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact hτA) t
      (by rw [CFSG.RankThree.GF2n.conjSubgroup_one]; exact ht)
    rw [hcomm] at hS4
    exact hconj.trans hS4

theorem cor2Alpha_of_rootType (hCorB : CorBFineStatement) (hSimp : CorBListSimpleStatement)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hroot : IsRootType 2 A) (hW : ⁅WAC A, WAC A⁆ ≤ A) (hne : ⁅WAC A, WAC A⁆ ≠ ⊥) :
    IsCoveringOf Tim77Cor2AlphaList ↥(normalClosure (A : Set G)) := by
  obtain ⟨t, ht, ht1⟩ : ∃ t ∈ A, t ≠ 1 := by
    by_contra! h
    apply hne
    have hW0 : WAC A = ⊥ := by
      unfold WAC
      refine le_bot_iff.mp (iSup₂_le fun g hg => ?_)
      intro x hx
      rw [Subgroup.mem_bot]
      have h1 := h _ (mem_conjSubgroup.mp hx)
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    rw [hW0]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr bot_le
  have hsetup : CFSG.Timmesfeld.CorB.Setup t := corBSetup hA hTI hroot hW hne ht ht1
  have ht2 : t * t = 1 := by rw [← sq]; exact hA.2 t ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hUA : normalClosure (A : Set G) = normalClosure ({t} : Set G) := by
    apply le_antisymm
    · apply normalClosure_le_normal
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]
        exact one_mem _
      · obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_mem hA hTI hroot hW hne ht ht1 ha ha1)
        rw [← hc]
        exact (normalClosure_normal : (normalClosure ({t} : Set G)).Normal).conj_mem t
          (subset_normalClosure (Set.mem_singleton t)) c
    · apply normalClosure_le_normal
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact subset_normalClosure ht
  rw [hUA]
  obtain ⟨g₀, hg₀C, hg₀A⟩ := alpha_exists_conj_le_centralizer hA hne
  rcases hCorB G t hsetup with ⟨K, hKU, hKn, hodd, hUK⟩ | hcomm | hdiv | ⟨D, hD⟩
  ·
    exfalso
    obtain ⟨x, hxB, hx1, hxA⟩ := alpha_exists_conj_elem hTI ht ht1 hg₀A
    have hxU : x ∈ normalClosure ({t} : Set G) := by
      rw [← hUA]
      exact alpha_conj_le_normalClosure A g₀ hxB
    have hxt : x * t = t * x := (Subgroup.mem_centralizer_iff.mp (hg₀C hxB) t ht).symm
    have hx2 : x * x = 1 := by
      rw [← sq]
      exact (isElemAbelian_conj hA g₀).2 x hxB
    have hKt : ∀ k ∈ K, t * k * t ∈ K := by
      intro k hk
      have hkU : k ∈ normalClosure ({t} : Set G) := by
        rw [hUK]
        exact Subgroup.mem_sup_left hk
      have htU : t ∈ normalClosure ({t} : Set G) := subset_normalClosure (Set.mem_singleton t)
      have hmem := hKn.conj_mem ⟨k, hkU⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨t, htU⟩
      have h2 := Subgroup.mem_subgroupOf.mp hmem
      simpa [htinv] using h2
    have hle : K ⊔ zpowers t ≤ closure ((K : Set G) ∪ {t}) := by
      apply sup_le
      · intro k hk
        exact subset_closure (Or.inl hk)
      · rw [zpowers_le]
        exact subset_closure (Or.inr (Set.mem_singleton t))
    have key : ∀ u ∈ closure ((K : Set G) ∪ {t}), u ∈ K ∨ u * t ∈ K := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem v hv =>
        rcases hv with hv | hv
        · exact Or.inl hv
        · rw [Set.mem_singleton_iff] at hv
          rw [hv]
          exact Or.inr (by rw [ht2]; exact K.one_mem)
      | one => exact Or.inl K.one_mem
      | mul a b _ _ iha ihb =>
        rcases iha with ha | ha <;> rcases ihb with hb | hb
        · exact Or.inl (K.mul_mem ha hb)
        · exact Or.inr (by rw [mul_assoc]; exact K.mul_mem ha hb)
        · refine Or.inr ?_
          have e : (a * t) * (t * b * t) = a * b * t := by
            calc (a * t) * (t * b * t) = a * (t * t) * b * t := by group
              _ = a * b * t := by rw [ht2, mul_one]
          rw [← e]
          exact K.mul_mem ha (hKt b hb)
        · refine Or.inl ?_
          have e : (a * t) * (t * (b * t) * t) = a * b := by
            calc (a * t) * (t * (b * t) * t) = a * (t * t) * b * (t * t) := by group
              _ = a * b := by simp only [ht2, mul_one]
          rw [← e]
          exact K.mul_mem ha (hKt _ hb)
      | inv a _ iha =>
        rcases iha with ha | ha
        · exact Or.inl (K.inv_mem ha)
        · refine Or.inr ?_
          have e : a⁻¹ * t = t * (a * t)⁻¹ * t := by group
          rw [e]
          exact hKt _ (K.inv_mem ha)
    have hxKZ : x ∈ K ⊔ zpowers t := by
      rw [← hUK]
      exact hxU
    have hxt1 : x * t ≠ 1 := by
      intro h
      apply hxA
      rw [eq_inv_of_mul_eq_one_left h, htinv]
      exact ht
    have hxt2 : x * t * (x * t) = 1 := by
      calc x * t * (x * t) = x * (t * x) * t := by group
        _ = x * (x * t) * t := by rw [← hxt]
        _ = x * x * (t * t) := by group
        _ = 1 := by rw [hx2, ht2, mul_one]
    rcases key x (hle hxKZ) with hxK | hxK
    · exact alpha_false_of_involution hodd hxK hx2 hx1
    · exact alpha_false_of_involution hodd hxK hxt2 hxt1
  ·
    exfalso
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hWU : WAC A ≤ normalClosure ({t} : Set G) := by
      rw [← hUA]
      unfold WAC
      exact iSup₂_le fun g _ => alpha_conj_le_normalClosure A g
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro w' hw'
    exact (hcomm w (hWU hw) w' (hWU hw')).1.symm
  ·
    exfalso
    obtain ⟨g, h, hgC, hhC, x, hx, y, hy, hxy⟩ := alpha_exists_noncomm hne
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hxy (by simp)
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hxy (by simp)
    have hxcls : IsConj t x := alpha_isConj_of_mem_conj hA hTI hroot hW hne ht ht1 hx hx1
    have hycls : IsConj t y := alpha_isConj_of_mem_conj hA hTI hroot hW hne ht ht1 hy hy1
    have hxW : x ∈ WAC A := conj_le_WAC hgC hx
    have hyW : y ∈ WAC A := conj_le_WAC hhC hy
    have hx2 : x * x = 1 := by
      rw [← sq]
      exact (isElemAbelian_conj hA g).2 x hx
    have hy2 : y * y = 1 := by
      rw [← sq]
      exact (isElemAbelian_conj hA h).2 y hy
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have hcm : ⁅x, y⁆ ∈ A := hW (Subgroup.commutator_mem_commutator hxW hyW)
    have hcm2 : ⁅x, y⁆ ^ 2 = 1 := hA.2 _ hcm
    have hsq : (x * y) ^ 2 = ⁅x, y⁆ := by
      rw [commutatorElement_def, hxinv, hyinv, sq]
      group
    have hxy' : (x * y) * (x * y) ≠ 1 := by
      intro hc
      apply hxy
      have h1 : x * y = (x * y)⁻¹ := eq_inv_of_mul_eq_one_left hc
      rw [mul_inv_rev, hxinv, hyinv] at h1
      exact h1
    have h4 : (x * y) ^ 4 = 1 := by
      have e : (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by group
      rw [e, hsq, hcm2]
    have hnot : ¬ (x * y) ^ (2 ^ 1) = 1 := fun h' => hxy' (by rw [← sq]; exact h')
    have hfin : (x * y) ^ (2 ^ (1 + 1)) = 1 := h4
    have hord4 : orderOf (x * y) = 4 := orderOf_eq_prime_pow hnot hfin
    exact hdiv x hxcls y hycls hord4
  ·
    have hsimp : IsSimpleGroup
        (↥(normalClosure ({t} : Set G)) ⧸ center ↥(normalClosure ({t} : Set G))) :=
      hSimp _ (CFSG.Timmesfeld.CorB.corBList_of_outcomeTwo hD)
    have hperf : ⁅normalClosure ({t} : Set G), normalClosure ({t} : Set G)⁆ =
        normalClosure ({t} : Set G) :=
      CFSG.LargeExtraspecial.S8.commutator_normalClosure_eq_of_isConj_mul
        hsetup.orderOf_eq hsetup.fusion hsimp
    unfold IsCoveringOf
    refine ⟨?_, center ↥(normalClosure ({t} : Set G)), le_rfl, inferInstance, ?_⟩
    · apply Subgroup.map_injective (normalClosure ({t} : Set G)).subtype_injective
      unfold _root_.commutator
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hperf
    · rcases hD with ⟨f, hf, -, hL⟩ | ⟨f, hf, -, hL⟩ | ⟨f, hf, -, hL⟩ | hU | hA6 | hJ2
      · exact Or.inl ⟨f, hf, CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero
          (by norm_num) hL⟩
      · exact Or.inr (Or.inl ⟨f, by omega, hL⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, hL⟩)))
      · exact Or.inr (Or.inr (Or.inl
          (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hU)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA6))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ2))))

end CFSG.RankThree.GF2n.Tim77
