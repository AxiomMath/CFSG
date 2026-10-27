module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_le_four_of_order_eight {E A : Subgroup G} (hE : Nat.card E = 8)
    (hnc : ¬ IsMulCommutative E) (hAE : A ≤ E) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 4 := by
  by_contra hlt
  have hdvd : Nat.card A ∣ 8 := hE ▸ Subgroup.card_dvd_of_le hAE
  have hle8 : Nat.card A ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have h8 : Nat.card A = 8 := by
    have h5 : 5 ≤ Nat.card A := by omega
    generalize Nat.card A = m at hdvd hle8 h5
    interval_cases m <;> simp_all
  have hAeq : A = E := Subgroup.eq_of_le_of_card_ge hAE (by omega)
  subst hAeq
  exact hnc hA.1

private theorem b15_S4A_comm {p : ℕ} {A : Subgroup G} (hA : IsElemAbelian p A) {x y : G}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x := by
  have := hA.1
  exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)

private theorem b15_S4A_inv_mul_mem {A B : Subgroup G} (hindex : A.relIndex B = 2)
    {x y : G} (hx : x ∈ B) (hy : y ∈ B) (hxA : x ∉ A) (hyA : y ∉ A) : x⁻¹ * y ∈ A := by
  have h2 : (A.subgroupOf B).index = 2 := hindex
  have hx' : (⟨x, hx⟩ : B)⁻¹ ∉ A.subgroupOf B := by
    intro h
    rw [Subgroup.mem_subgroupOf] at h
    exact hxA (by simpa using h)
  have hy' : (⟨y, hy⟩ : B) ∉ A.subgroupOf B := fun h => hyA (Subgroup.mem_subgroupOf.mp h)
  have key := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨x, hx⟩ : B)⁻¹)
    (b := (⟨y, hy⟩ : B))).2 (iff_of_false hx' hy')
  simpa using Subgroup.mem_subgroupOf.mp key

private theorem b15_S4A_card_sup {U U' : Subgroup G} (hcomm : U' ≤ centralizer (U : Set G))
    (hdisj : U ⊓ U' = ⊥) : Nat.card (U ⊔ U' : Subgroup G) = Nat.card U * Nat.card U' := by
  have hc : ∀ (m : U) (n : U'), Commute (U.subtype m) (U'.subtype n) := fun m n =>
    (Subgroup.mem_centralizer_iff.mp (hcomm n.2)) m m.2
  have hinj : Function.Injective (U.subtype.noncommCoprod U'.subtype hc) := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨U.subtype_injective, U'.subtype_injective, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
    exact hdisj
  have hrange : (U.subtype.noncommCoprod U'.subtype hc).range = U ⊔ U' := by
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_prod]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

private theorem b15_S4A_isElemAbelian_sup {A B : Subgroup G} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) (hAB : B ≤ centralizer (A : Set G)) : IsElemAbelian 2 (A ⊔ B) := by
  have hAn : A ≤ normalizer (B : Set G) :=
    (Subgroup.le_centralizer_iff.1 hAB).trans (Subgroup.centralizer_le_normalizer _)
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    have hx' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hAn] at hx'
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a, ha, b, hb, rfl⟩
  have hcom : ∀ {a b : G}, a ∈ A → b ∈ B → a * b = b * a := fun {a b} ha hb =>
    Subgroup.mem_centralizer_iff.1 (hAB hb) a ha
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem y hy
    change a * b * (a' * b') = a' * b' * (a * b)
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [← hcom ha' hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by
        rw [b15_S4A_comm hA ha ha', b15_S4A_comm hB hb hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hcom ha hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    have hab : Commute a b := hcom ha hb
    rw [hab.mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

private theorem b15_S4A_ncard_coe (B : Subgroup G) : (B : Set G).ncard = Nat.card B := by
  rw [← Nat.card_coe_set_eq]
  rfl

private theorem b15_S4A_ncard_nonid (B : Subgroup G) :
    ((B : Set G) \ {1}).ncard = Nat.card B - 1 := by
  rw [Set.ncard_diff_singleton_of_mem B.one_mem, b15_S4A_ncard_coe]

private theorem b15_S4A_ncard_nonid_inter_le {B B' : Subgroup G} (h4 : Nat.card B = 4)
    (h4' : Nat.card B' = 4) (hne : B ≠ B') :
    (((B : Set G) \ {1}) ∩ ((B' : Set G) \ {1})).ncard ≤ 1 := by
  have hset : ((B : Set G) \ {1}) ∩ ((B' : Set G) \ {1}) =
      ((B ⊓ B' : Subgroup G) : Set G) \ {1} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_diff, SetLike.mem_coe, Set.mem_singleton_iff,
      Subgroup.mem_inf]
    tauto
  rw [hset, b15_S4A_ncard_nonid]
  have hdvd : Nat.card (B ⊓ B' : Subgroup G) ∣ 4 := h4 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne4 : Nat.card (B ⊓ B' : Subgroup G) ≠ 4 := by
    intro h
    apply hne
    have e1 : B ⊓ B' = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    have e2 : B ⊓ B' = B' := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
    rw [← e1, e2]
  have hle4 := Nat.le_of_dvd (by norm_num) hdvd
  generalize Nat.card (B ⊓ B' : Subgroup G) = m at hdvd hne4 hle4
  interval_cases m <;> simp_all

private theorem b15_S4A_six_le_ncard_union {X Y Z : Set G} (hX : X.ncard = 3) (hY : Y.ncard = 3)
    (hZ : Z.ncard = 3) (hXY : (X ∩ Y).ncard ≤ 1) (hXZ : (X ∩ Z).ncard ≤ 1)
    (hYZ : (Y ∩ Z).ncard ≤ 1) : 6 ≤ (X ∪ Y ∪ Z).ncard := by
  have h1 := Set.ncard_union_add_ncard_inter X Y (Set.toFinite _) (Set.toFinite _)
  have h2 := Set.ncard_union_add_ncard_inter (X ∪ Y) Z (Set.toFinite _) (Set.toFinite _)
  have h3 : ((X ∪ Y) ∩ Z).ncard ≤ 2 := by
    rw [Set.union_inter_distrib_right]
    exact (Set.ncard_union_le _ _).trans (by omega)
  omega

theorem eq_or_eq_of_order_eight_card_four {E I W A : Subgroup G} (hE : Nat.card E = 8)
    (hnc : ¬ IsMulCommutative E) (hIE : I ≤ E) (hI : IsElemAbelian 2 I) (hI4 : Nat.card I = 4)
    (hWE : W ≤ E) (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) (hIW : I ≠ W)
    (hAE : A ≤ E) (hA : IsElemAbelian 2 A) (hA4 : Nat.card A = 4) : A = I ∨ A = W := by
  by_contra hcon
  have hAI : A ≠ I := fun h => hcon (Or.inl h)
  have hAW : A ≠ W := fun h => hcon (Or.inr h)
  obtain ⟨g, hgE, hg⟩ : ∃ g ∈ E, g * g ≠ 1 := by
    by_contra hall
    have hall' : ∀ g ∈ E, g * g = 1 := fun g hg => by
      by_contra h
      exact hall ⟨g, hg, h⟩
    refine hnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    change a * b = b * a
    have h1 := hall' (a * b) (E.mul_mem ha hb)
    have h2 := hall' a ha
    have h3 := hall' b hb
    calc a * b = a * (a * b * (a * b)) * b := by rw [h1]; group
      _ = (a * a) * b * a * (b * b) := by group
      _ = b * a := by rw [h2, h3]; group
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (mul_one 1)
  have hggi : g ≠ g⁻¹ := by
    intro h
    apply hg
    nth_rewrite 2 [h]
    exact mul_inv_cancel g
  have hgi1 : g⁻¹ ≠ 1 := fun h => hg1 (inv_eq_one.1 h)
  have hP : (({1, g, g⁻¹} : Set G)).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, g, g⁻¹, hg1.symm, hgi1.symm, hggi, rfl⟩
  have hsq : ∀ {B : Subgroup G}, IsElemAbelian 2 B → ∀ x ∈ B, x * x = 1 := fun hB x hx => by
    simpa [pow_two] using hB.2 x hx
  have hU : 6 ≤ (((I : Set G) \ {1}) ∪ ((W : Set G) \ {1}) ∪ ((A : Set G) \ {1})).ncard :=
    b15_S4A_six_le_ncard_union (by rw [b15_S4A_ncard_nonid, hI4]) (by rw [b15_S4A_ncard_nonid, hW4])
      (by rw [b15_S4A_ncard_nonid, hA4]) (b15_S4A_ncard_nonid_inter_le hI4 hW4 hIW)
      (b15_S4A_ncard_nonid_inter_le hI4 hA4 hAI.symm)
      (b15_S4A_ncard_nonid_inter_le hW4 hA4 hAW.symm)
  have hinv : ∀ x ∈ ((I : Set G) \ {1}) ∪ ((W : Set G) \ {1}) ∪ ((A : Set G) \ {1}),
      x ≠ 1 ∧ x * x = 1 ∧ x ∈ E := by
    intro x hx
    rcases hx with (hx | hx) | hx
    · exact ⟨hx.2, hsq hI x hx.1, hIE hx.1⟩
    · exact ⟨hx.2, hsq hW x hx.1, hWE hx.1⟩
    · exact ⟨hx.2, hsq hA x hx.1, hAE hx.1⟩
  have hdisj : Disjoint (((I : Set G) \ {1}) ∪ ((W : Set G) \ {1}) ∪ ((A : Set G) \ {1}))
      ({1, g, g⁻¹} : Set G) := by
    rw [Set.disjoint_left]
    intro x hx hxP
    obtain ⟨hx1, hxx, -⟩ := hinv x hx
    rcases hxP with h | h | h
    · exact hx1 h
    · rw [h] at hxx
      exact hg hxx
    · rw [h] at hxx
      apply hg
      have : (g * g)⁻¹ = 1 := by rw [mul_inv_rev]; exact hxx
      exact inv_eq_one.1 this
  have hsub : (((I : Set G) \ {1}) ∪ ((W : Set G) \ {1}) ∪ ((A : Set G) \ {1})) ∪
      ({1, g, g⁻¹} : Set G) ⊆ (E : Set G) := by
    intro x hx
    rcases hx with hx | hx
    · exact (hinv x hx).2.2
    · rcases hx with rfl | rfl | rfl
      · exact E.one_mem
      · exact hgE
      · exact E.inv_mem hgE
  have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), hP, b15_S4A_ncard_coe,
    hE] at hcard
  omega

theorem inf_centralizer_eq_of_order_eight_card_four {E W : Subgroup G} (hE : Nat.card E = 8)
    (hnc : ¬ IsMulCommutative E) (hWE : W ≤ E) (hW : IsElemAbelian 2 W)
    (hW4 : Nat.card W = 4) : E ⊓ centralizer (W : Set G) = W := by
  have hWN : W ≤ E ⊓ centralizer (W : Set G) := fun x hx =>
    ⟨hWE hx, Subgroup.mem_centralizer_iff.2 fun w hw => (b15_S4A_comm hW hx hw).symm⟩
  have hdvd : Nat.card (E ⊓ centralizer (W : Set G) : Subgroup G) ∣ 8 :=
    hE ▸ Subgroup.card_dvd_of_le inf_le_left
  have hdvd4 : 4 ∣ Nat.card (E ⊓ centralizer (W : Set G) : Subgroup G) :=
    hW4 ▸ Subgroup.card_dvd_of_le hWN
  have hcases : Nat.card (E ⊓ centralizer (W : Set G) : Subgroup G) = 4 ∨
      Nat.card (E ⊓ centralizer (W : Set G) : Subgroup G) = 8 := by
    have hle8 := Nat.le_of_dvd (by norm_num) hdvd
    generalize Nat.card (E ⊓ centralizer (W : Set G) : Subgroup G) = m at hdvd hdvd4 hle8
    interval_cases m <;> simp_all
  rcases hcases with h4 | h8
  · exact (Subgroup.eq_of_le_of_card_ge hWN (by omega)).symm
  · exfalso
    have hNE : E ⊓ centralizer (W : Set G) = E :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ centralizer (W : Set G) ≤ E) (by omega)
    have hEc : E ≤ centralizer (W : Set G) := inf_eq_left.1 hNE
    have hindex : W.relIndex E = 2 := by
      have h := Subgroup.relIndex_mul_card (H := W) (K := E)
      rw [inf_eq_left.2 hWE, hW4, hE] at h
      omega
    refine hnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have hcomW : ∀ {x w : G}, x ∈ E → w ∈ W → w * x = x * w := fun {x w} hx hw =>
      Subgroup.mem_centralizer_iff.1 (hEc hx) w hw
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    change a * b = b * a
    by_cases haW : a ∈ W
    · exact hcomW hb haW
    by_cases hbW : b ∈ W
    · exact (hcomW ha hbW).symm
    have hw : a⁻¹ * b ∈ W := b15_S4A_inv_mul_mem hindex ha hb haW hbW
    have hc : (a⁻¹ * b) * a = a * (a⁻¹ * b) := hcomW ha hw
    have hc' : a⁻¹ * b * a = b := by rw [hc]; group
    calc a * b = a * (a⁻¹ * b * a) := by rw [hc']
      _ = b * a := by group

theorem elemFamilyIn_two_eq_of_order_eight {T E C I W : Subgroup G} (hT : T = E ⊔ C)
    (hEC : C ≤ centralizer (E : Set G)) (hdisj : E ⊓ C = ⊥) (hC : IsElemAbelian 2 C)
    (hE : Nat.card E = 8) (hnc : ¬ IsMulCommutative E)
    (hIE : I ≤ E) (hI : IsElemAbelian 2 I) (hI4 : Nat.card I = 4)
    (hWE : W ≤ E) (hW : IsElemAbelian 2 W) (hW4 : Nat.card W = 4) (hIW : I ≠ W) :
    elemFamilyIn 2 T = {I ⊔ C, W ⊔ C} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEn : E ≤ normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.1 hEC).trans (Subgroup.centralizer_le_normalizer _)
  have hdecomp : ∀ t ∈ T, ∃ e ∈ E, ∃ c ∈ C, t = e * c := by
    intro t ht
    have ht' : t ∈ ((E ⊔ C : Subgroup G) : Set G) := hT ▸ ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E C hEn] at ht'
    obtain ⟨e, he, c, hc, rfl⟩ := ht'
    exact ⟨e, he, c, hc, rfl⟩
  have hCE : ∀ {e c : G}, e ∈ E → c ∈ C → e * c = c * e := fun {e c} he hc =>
    Subgroup.mem_centralizer_iff.1 (hEC hc) e he
  have hCT : ∀ {t c : G}, t ∈ T → c ∈ C → t * c = c * t := by
    intro t c ht hc
    obtain ⟨e, he, c', hc', rfl⟩ := hdecomp t ht
    calc e * c' * c = e * (c' * c) := by group
      _ = e * (c * c') := by rw [b15_S4A_comm hC hc' hc]
      _ = (e * c) * c' := by group
      _ = (c * e) * c' := by rw [hCE he hc]
      _ = c * (e * c') := by group
  have hET : E ≤ T := hT ▸ le_sup_left
  have hCT' : C ≤ T := hT ▸ le_sup_right
  have hn0 : 0 < Nat.card C := Nat.card_pos
  have hCcomm : ∀ {B : Subgroup G}, B ≤ T → C ≤ centralizer (B : Set G) := fun hB c hc =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hCT (hB hb) hc
  have hsup : ∀ {B : Subgroup G}, B ≤ T → IsElemAbelian 2 B → IsElemAbelian 2 (B ⊔ C) :=
    fun hB hBe => b15_S4A_isElemAbelian_sup hBe hC (hCcomm hB)
  have hcardsup : ∀ {B : Subgroup G}, B ≤ E →
      Nat.card (B ⊔ C : Subgroup G) = Nat.card B * Nat.card C := by
    intro B hB
    refine b15_S4A_card_sup (hCcomm (hB.trans hET)) ?_
    exact le_antisymm ((inf_le_inf_right C hB).trans hdisj.le) bot_le
  have hIC : Nat.card (I ⊔ C : Subgroup G) = 4 * Nat.card C := by rw [hcardsup hIE, hI4]
  have hWC : Nat.card (W ⊔ C : Subgroup G) = 4 * Nat.card C := by rw [hcardsup hWE, hW4]
  have hbound : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A →
      Nat.card A ≤ 4 * Nat.card C ∧ (Nat.card A = 4 * Nat.card C → A = I ⊔ C ∨ A = W ⊔ C) := by
    intro A hAT hAe
    have hAC : IsElemAbelian 2 (A ⊔ C) := hsup hAT hAe
    have hAbE : (A ⊔ C) ⊓ E ≤ E := inf_le_right
    have hAbe : IsElemAbelian 2 ((A ⊔ C) ⊓ E) := hAC.mono inf_le_left
    have hAb4 : Nat.card ((A ⊔ C) ⊓ E : Subgroup G) ≤ 4 :=
      card_le_four_of_order_eight hE hnc hAbE hAbe
    have hAle : A ≤ ((A ⊔ C) ⊓ E) ⊔ C := by
      intro a ha
      obtain ⟨e, he, c', hc', rfl⟩ := hdecomp a (hAT ha)
      have he' : e ∈ A ⊔ C := by
        have : e = (e * c') * c'⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem_sup ha (C.inv_mem hc')
      exact Subgroup.mul_mem_sup ⟨he', he⟩ hc'
    have hcardAb : Nat.card (((A ⊔ C) ⊓ E) ⊔ C : Subgroup G) =
        Nat.card ((A ⊔ C) ⊓ E : Subgroup G) * Nat.card C := hcardsup hAbE
    have hAcard : Nat.card A ≤ Nat.card ((A ⊔ C) ⊓ E : Subgroup G) * Nat.card C :=
      hcardAb ▸ Subgroup.card_le_of_le hAle
    refine ⟨hAcard.trans (Nat.mul_le_mul_right _ hAb4), fun h4 => ?_⟩
    have hAb4' : Nat.card ((A ⊔ C) ⊓ E : Subgroup G) = 4 := by
      have h' : 4 * Nat.card C ≤ Nat.card ((A ⊔ C) ⊓ E : Subgroup G) * Nat.card C := h4 ▸ hAcard
      exact le_antisymm hAb4 (Nat.le_of_mul_le_mul_right h' hn0)
    have hAeq : A = ((A ⊔ C) ⊓ E) ⊔ C :=
      Subgroup.eq_of_le_of_card_ge hAle (by rw [hcardAb, hAb4', h4])
    rcases eq_or_eq_of_order_eight_card_four hE hnc hIE hI hI4 hWE hW hW4 hIW hAbE hAbe hAb4'
      with h | h
    · left
      rw [hAeq, h]
    · right
      rw [hAeq, h]
  have hrank : 2 ^ CFSG.pRank 2 ↥T = 4 * Nat.card C := by
    apply le_antisymm
    · obtain ⟨A₀, hA₀, hcard⟩ := CFSG.Quasithin.BlueprintB2.exists_card_eq_pow_pRank ↥T 2
      have hA₁ : IsElemAbelian 2 (A₀.map T.subtype) :=
        isElemAbelian_iff_isElementaryAbelian.2 (hA₀.subgroup_map T.subtype)
      have := (hbound _ (Subgroup.map_subtype_le A₀) hA₁).1
      rwa [Subgroup.card_map_of_injective T.subtype_injective, hcard] at this
    · have := card_le_pow_pRank_of_le (Q := T) (A := I ⊔ C) (sup_le (hIE.trans hET) hCT')
        (isElemAbelian_iff_isElementaryAbelian.1 (hsup (hIE.trans hET) hI))
      rwa [hIC] at this
  ext B
  rw [mem_elemFamilyIn, hrank]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hBT, hBe, hBcard⟩
    exact (hbound B hBT (isElemAbelian_iff_isElementaryAbelian.2 hBe)).2 hBcard
  · rintro (rfl | rfl)
    · exact ⟨sup_le (hIE.trans hET) hCT',
        isElemAbelian_iff_isElementaryAbelian.1 (hsup (hIE.trans hET) hI), hIC⟩
    · exact ⟨sup_le (hWE.trans hET) hCT',
        isElemAbelian_iff_isElementaryAbelian.1 (hsup (hWE.trans hET) hW), hWC⟩

end CFSG.LocalAnalysis.WeakClosure81
