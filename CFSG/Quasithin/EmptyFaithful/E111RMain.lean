module

public import CFSG.Quasithin.EmptyFaithful.E111RMemC
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.EmptyFaithful.E22NE111

public section

namespace CFSG.Quasithin.E2.E22N

open CFSG.Open CFSG.Quasithin.A1b CFSG.Quasithin.Vol2.Ch11.SecB
open scoped Pointwise

namespace E111R

variable {G : Type} [Group G]

theorem le_normalizer_of_comm {X N : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ N, x * y = y * x) :
    X ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h1 := h x hx _ hy
    have : y = x * y * x⁻¹ := by
      calc y = x⁻¹ * ((x * y * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * y * x⁻¹)) := by rw [← h1]
        _ = x * y * x⁻¹ := by group
    rw [this]
    exact hy

theorem exists_mul_of_mem_sup {V U : Subgroup G} (hUV : U ≤ Subgroup.normalizer (V : Set G))
    {x : G} (hx : x ∈ V ⊔ U) : ∃ v ∈ V, ∃ u ∈ U, x = v * u := by
  have hx' : x ∈ (V : Set G) * (U : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left V U hUV]
    exact hx
  obtain ⟨v, hv, u, hu, rfl⟩ := hx'
  exact ⟨v, hv, u, hu, rfl⟩

theorem isElemAbelian_of_le {E F : Subgroup G} (hE : IsElemAbelian 2 E) (hFE : F ≤ E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

variable [Finite G]

theorem exists_compl {E U : Subgroup G} (hE : IsElemAbelian 2 E) (hUE : U ≤ E) :
    ∃ C : Subgroup G, C ≤ E ∧ C ⊓ U = ⊥ ∧ C ⊔ U = E := by
  classical
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun C : Subgroup G => C ≤ E ∧ C ⊓ U = ⊥)
    (fun C : Subgroup G => Nat.card C) ⟨⊥, by simp⟩
  obtain ⟨hCE, hCU⟩ := (Finset.mem_filter.mp hC).2
  refine ⟨C, hCE, hCU, ?_⟩
  by_contra hne
  obtain ⟨e, heE, heCU⟩ : ∃ e ∈ E, e ∉ C ⊔ U := by
    by_contra h
    push Not at h
    exact hne (le_antisymm (sup_le hCE hUE) h)
  have he2 : e ^ 2 = 1 := hE.2 e heE
  have hZE : Subgroup.zpowers e ≤ E := Subgroup.zpowers_le.mpr heE
  have hN : Subgroup.zpowers e ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_of_comm fun a ha b hb => hcomm a (hZE ha) b (hCE hb)
  have hC'E : C ⊔ Subgroup.zpowers e ≤ E := sup_le hCE hZE
  have hC'U : (C ⊔ Subgroup.zpowers e) ⊓ U = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨c, hc, b, hb, rfl⟩ := exists_mul_of_mem_sup hN hx1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hsq : e ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, he2]
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, hsq, one_zpow, mul_one] at hx2 ⊢
      have : c ∈ C ⊓ U := ⟨hc, hx2⟩
      rw [hCU] at this
      exact this
    · exfalso
      rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul] at hx2
      apply heCU
      have : e = c⁻¹ * (c * e) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hc))
        (Subgroup.mem_sup_right hx2)
  have hcard : Nat.card (C ⊔ Subgroup.zpowers e : Subgroup G) ≤ Nat.card C :=
    hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC'E, hC'U⟩)
  have hEq : C = C ⊔ Subgroup.zpowers e := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  apply heCU
  have hmem : e ∈ C ⊔ Subgroup.zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  rw [← hEq] at hmem
  exact Subgroup.mem_sup_left hmem

theorem relIndex_eq_two {A V Z C : Subgroup G} (hA : IsElemAbelian 2 A) (hZA : Z ≤ A)
    (hZV : Z ⊓ V = ⊥) (hVA : V ≤ A) {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1) (hCZ : C ≤ Z)
    (hCz : C ⊓ Subgroup.zpowers z = ⊥) (hCzZ : C ⊔ Subgroup.zpowers z = Z)
    (hZVA : Z ⊔ V = A) : (C ⊔ V).relIndex A = 2 := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hz2 : z ^ 2 = 1 := hA.2 z (hZA hzZ)
  have hCVA : C ⊔ V ≤ A := sup_le (hCZ.trans hZA) hVA
  have hN : C ⊔ V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    le_normalizer_of_comm fun a ha b hb => hcomm a (hCVA ha) b
      (Subgroup.zpowers_le.mpr (hZA hzZ) hb)
  have hsup : C ⊔ V ⊔ Subgroup.zpowers z = A := by
    rw [← hZVA, ← hCzZ]
    exact le_antisymm (sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
      (le_sup_right.trans le_sup_left)) (sup_le (sup_le (le_sup_left.trans le_sup_left)
      le_sup_right) (le_sup_right.trans le_sup_left))
  have hinf : (C ⊔ V) ⊓ Subgroup.zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx2
    have hsq : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← sq, hz2]
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · rw [zpow_mul, hsq, one_zpow]
      exact Subgroup.one_mem _
    · exfalso
      rw [zpow_add_one, zpow_mul, hsq, one_zpow, one_mul] at hx1
      have hVC : V ≤ Subgroup.normalizer (C : Set G) :=
        le_normalizer_of_comm fun a ha b hb => hcomm a (hVA ha) b (hCZ.trans hZA hb)
      obtain ⟨c, hc, v, hv, hcv⟩ := exists_mul_of_mem_sup hVC hx1
      have hvZ : v ∈ Z := by
        have : v = c⁻¹ * z := by rw [hcv]; group
        rw [this]
        exact Z.mul_mem (Z.inv_mem (hCZ hc)) hzZ
      have hv1 : v = 1 := by
        have : v ∈ Z ⊓ V := ⟨hvZ, hv⟩
        rwa [hZV] at this
      rw [hv1, mul_one] at hcv
      have : z ∈ C ⊓ Subgroup.zpowers z := ⟨hcv ▸ hc, Subgroup.mem_zpowers z⟩
      rw [hCz] at this
      exact hz1 this
  have key := B6.relIndex_inf_eq_relIndex_sup hN
  rw [hinf, Subgroup.relIndex_bot_left, Nat.card_zpowers, hsup] at key
  rw [← key]
  exact orderOf_eq_prime hz2 hz1

theorem exists_member {X T : Subgroup G} (hR : E111Reduced G X T) {n : ℕ} (hn : 1 ≤ n)
    (hQ : ∀ S, IsComp X S → AutRankLe n ↥S) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥) :
    ∃ S K, IsComp X S ∧ E1.IsE n ⊤ T A K ∧
      ∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
  obtain ⟨S, hS, hAS⟩ := exists_isComp_not_le hR hA1
  set V := A ⊓ Subgroup.normalizer (S : Set G) with hVdef
  obtain ⟨Z, hZA, hZV, hZVA⟩ := exists_compl hA (inf_le_left : V ≤ A)
  by_cases hV : V ≤ Subgroup.centralizer (S : Set G)
  ·
    have hZ1 : Z ≠ ⊥ := by
      intro hZ
      rw [hZ, bot_sup_eq] at hZVA
      exact hAS (hZVA ▸ hV)
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hZ1 ((Subgroup.eq_bot_iff_forall Z).mpr hc)
    have hZe := isElemAbelian_of_le hA hZA
    obtain ⟨C, hCZ, hCz, hCzZ⟩ := exists_compl hZe (Subgroup.zpowers_le.mpr hzZ)
    have hidx := relIndex_eq_two hA hZA hZV inf_le_left hzZ hz1 hCZ hCz hCzZ hZVA
    have hset : DiagSetting X T A S C :=
      ⟨hR, hAT, hA, hS, hCZ.trans hZA, le_bot_iff.mp ((inf_le_inf_right _ hCZ).trans hZV.le)⟩
    let _ : Fintype ↥C := Fintype.ofFinite _
    exact ⟨S, _, hS, hset.isE_diagK hn (Or.inr ⟨hV, hidx⟩), fun x hx => by
      obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
      exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩
  ·
    have hset : DiagSetting X T A S Z := ⟨hR, hAT, hA, hS, hZA, hZV⟩
    let _ : Fintype ↥Z := Fintype.ofFinite _
    exact ⟨S, _, hS, hset.isE_diagK hn (Or.inl ⟨hZVA, hV, (hQ S hS).2⟩), fun x hx => by
      obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
      exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩

theorem inEFor_of_reduced_autRankLe {X T : Subgroup G} (hR : E111Reduced G X T) {n : ℕ}
    (hn : 1 ≤ n) (hQ : ∀ S, IsComp X S → AutRankLe n ↥S) : E1.InEFor n ⊤ T := by
  intro Ω hΩ
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥
  · obtain ⟨A, hAΩ, hAT, hA1⟩ := hex
    obtain ⟨S, K, hS, hK, hdiag⟩ := exists_member hR hn hQ hAT (hΩ.isElemAbelian A hAΩ) hA1
    set G₁ := E1.eGen n ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G))
    have hKe : K ≤ E1.eGen n ⊤ T Ω := by
      unfold E1.eGen
      exact le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT
        (le_iSup₂_of_le (f := fun K (_ : K ∈ {K | E1.IsE n ⊤ T A K}) => K) K hK le_rfl))
    have hKG : K ≤ G₁ := hKe.trans le_sup_left
    have hTG : T ≤ G₁ := fun t ht =>
      Subgroup.mem_sup_right ⟨Subgroup.mem_top t, E1.le_normalizer_weakClosure hΩ ht⟩
    obtain ⟨⟨x, hx1, hx2⟩, -⟩ := hQ S hS
    have hSG : S ≤ G₁ := le_of_diag hS.simple
      (inf_ne_bot hR hS ⟨x, x.2, fun h => hx1 (Subtype.ext h), by
        simpa using congrArg Subtype.val hx2⟩) hTG
      fun y hy => by
        obtain ⟨k, hk, hc⟩ := hdiag y hy
        exact ⟨k, hKG hk, hc⟩
    have hXG : X ≤ G₁ := by
      rw [← iSup_conj_eq hR hS]
      refine iSup₂_le fun t ht => ?_
      rintro _ ⟨s, hs, rfl⟩
      exact G₁.mul_mem (G₁.mul_mem (hTG ht) (hSG hs)) (G₁.inv_mem (hTG ht))
    refine le_antisymm le_top ?_
    rw [← hR.2.2.2.2.2.2]
    exact sup_le hXG hTG
  · push Not at hex
    have hW : E1.weakClosure T Ω = ⊥ :=
      le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => (hex A hA hAT).le)
    rw [hW, Subgroup.normalizer_eq_top, inf_top_eq, sup_top_eq]

end E111R

theorem e111CoreMultiQn_autRankLe {n : ℕ} (hn : 1 ≤ n) : E111CoreMultiQn (AutRankLe n) n := by
  intro G _ _ X T _ hsec _ hR _
  refine E111R.inEFor_of_reduced_autRankLe hR hn fun S hS => ?_
  have hsub : S.IsSubnormal :=
    Subgroup.IsSubnormal.trans hS.le hS.2.1.isSubnormal hR.1.isSubnormal
  have := hS.simple
  have hq : IsSimpleGroup (↥S ⧸ (⊥ : Subgroup ↥S)) :=
    (MulEquiv.isSimpleGroup_congr QuotientGroup.quotientBot).mpr this
  have hP := hsec S ⊥ hsub hq (nonabelian_of_mulEquiv QuotientGroup.quotientBot hS.nonabelian)
  exact autRankLe_isoInv n _ _ QuotientGroup.quotientBot.symm hP

theorem e111ForQn_autRankLe {n : ℕ} (hn : 1 ≤ n) : E111ForQn (AutRankLe n) n :=
  e111ForQn_of_core (autRankLe_isoInv n) hn (e111CoreMultiQn_autRankLe hn)

end CFSG.Quasithin.E2.E22N
