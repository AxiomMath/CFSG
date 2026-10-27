module

public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.EmptyFaithful.S146R4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_sup_of_mem_GB2 {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h1 : conjSub g (A ⊔ B) = A ⊔ B := by
    rw [show conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B from Subgroup.map_sup _ _ _,
      conjSub_eq_of_mem_normalizer hA, conjSub_eq_of_mem_normalizer hB]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h1

omit [Finite G] in
theorem mem_normalizer_inf_of_mem_GB2 {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  have h1 : conjSub g (A ⊓ B) = A ⊓ B := by
    rw [conjSub_inf, conjSub_eq_of_mem_normalizer hA, conjSub_eq_of_mem_normalizer hB]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h1

omit [Finite G] in
theorem mem_normalizer_centralizer_pCoreOf {H : Subgroup G} {g : G} (hg : g ∈ H) :
    g ∈ Subgroup.normalizer
      ((Subgroup.centralizer (pCoreOf 2 H : Set G) : Subgroup G) : Set G) := by
  have h1 : conjSub g (Subgroup.centralizer (pCoreOf 2 H : Set G)) =
      Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [← conjSub_centralizer, conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hg)]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h1

theorem Setting146.duality_data (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) *
        Nat.card (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) :
          Subgroup G) = Nat.card (pCoreOf 2 H) ∧
      conjClosure (VZ T M) H ≤
        pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) := by
  set Q := pCoreOf 2 H with hQ
  set U := conjClosure (VZ T M) H with hU
  have hUQ : U ≤ Q := S.conjClosure_le_pCoreOf hH
  have hUab : IsElemAbelian 2 U := S.lemma_14_5_15_two hH
  have hdual :
      (Q ⊓ Subgroup.centralizer (U : Set G)).relIndex Q =
        (U ⊓ Subgroup.centralizer (Q : Set G)).relIndex U :=
    (S.lemma_14_5_14 (S.isHz_iff.mpr hH)).2.toHypF91.F97_relIndex hUab
  have hUA : U ≤ Q ⊓ Subgroup.centralizer (U : Set G) := by
    refine le_inf hUQ fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact congrArg Subtype.val (hUab.1.is_comm.comm (⟨y, hy⟩ : U) ⟨x, hx⟩)
  have hAQ : Q ⊓ Subgroup.centralizer (U : Set G) ≤ Q := inf_le_left
  have hQcard : (Q ⊓ Subgroup.centralizer (U : Set G)).relIndex Q *
      Nat.card (Q ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) = Nat.card Q := by
    have := Subgroup.relIndex_mul_card (H := Q ⊓ Subgroup.centralizer (U : Set G)) (K := Q)
    rwa [inf_eq_left.mpr hAQ] at this
  have hrel : (Subgroup.centralizer (Q : Set G)).relIndex U =
      (U ⊓ Subgroup.centralizer (Q : Set G)).relIndex U := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  refine ⟨?_, hUA⟩
  rw [hrel, ← hdual]
  exact hQcard

theorem Setting146.sixteen_le_relIndex_centralizer (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H)
    (hirr : ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W →
      W ≤ uK T M H ⊔ quasithinOmegaOneCenter T → H ≤ Subgroup.normalizer (W : Set G) →
      W = quasithinOmegaOneCenter T ∨ W = uK T M H ⊔ quasithinOmegaOneCenter T)
    (hcard : Nat.card ↥(uK T M H ⊔ quasithinOmegaOneCenter T) = 2 ^ 5)
    (hnc : ¬ uK T M H ≤ Subgroup.centralizer (pCoreOf 2 H : Set G)) :
    16 ≤ (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set Q := pCoreOf 2 H with hQ
  set C : Subgroup G := Subgroup.centralizer (Q : Set G) with hC
  set KG : Subgroup G := uK T M H ⊔ Z with hKG
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have huKU : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have hZU : Z ≤ conjClosure (VZ T M) H := Z_le_conjClosure_VZ T M H
  have hKU : KG ≤ conjClosure (VZ T M) H := sup_le huKU hZU
  have hZC : Z ≤ C := Subgroup.le_centralizer_iff.mp
    ((S.pCoreOf_le_T hH).trans (le_centralizer_quasithinOmegaOneCenter T))
  have hHuK : H ≤ Subgroup.normalizer (uK T M H : Set G) :=
    S145.le_normalizer_commutator hHU Subgroup.le_normalizer
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := fun g hg => by
    rw [S.normalizer_Z]; exact S.le_mcOf hH hg
  have hHKG : H ≤ Subgroup.normalizer (KG : Set G) := fun g hg =>
    mem_normalizer_sup_of_mem_GB2 (hHuK hg) (hHZ hg)
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := fun g hg =>
    mem_normalizer_centralizer_pCoreOf hg
  have hHW : H ≤ Subgroup.normalizer ((KG ⊓ C : Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_of_mem_GB2 (hHKG hg) (hHC hg)
  rcases hirr (KG ⊓ C) (le_inf le_sup_right hZC) inf_le_left hHW with h | h
  · have e := Subgroup.relIndex_mul_card C KG
    rw [inf_comm, h, S.card_Z, hcard] at e
    have h16 : C.relIndex KG = 16 := by omega
    have hne : C.relIndex (conjClosure (VZ T M) H) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have := Subgroup.relIndex_le_of_le_right hKU hne
    omega
  · exact absurd (le_sup_left.trans (inf_eq_left.mp h)) hnc

theorem Setting146.two_pow_nine_le_card_pCoreOf_of_irreducible (S : Setting146 G T M)
    {H : Subgroup G} (hH : IsHTM T M H)
    (hirr : ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W →
      W ≤ uK T M H ⊔ quasithinOmegaOneCenter T → H ≤ Subgroup.normalizer (W : Set G) →
      W = quasithinOmegaOneCenter T ∨ W = uK T M H ⊔ quasithinOmegaOneCenter T)
    (hcard : Nat.card ↥(uK T M H ⊔ quasithinOmegaOneCenter T) = 2 ^ 5)
    (hnc : ¬ uK T M H ≤ Subgroup.centralizer (pCoreOf 2 H : Set G)) :
    2 ^ 9 ≤ Nat.card (pCoreOf 2 H) := by
  obtain ⟨hd, hUA⟩ := S.duality_data hH
  have h16 := S.sixteen_le_relIndex_centralizer hH hirr hcard hnc
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have huKU : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have hKU : uK T M H ⊔ quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    sup_le huKU (Z_le_conjClosure_VZ T M H)
  have h32 : 2 ^ 5 ≤ Nat.card (conjClosure (VZ T M) H) := hcard ▸ Subgroup.card_le_of_le hKU
  have hA32 : Nat.card (conjClosure (VZ T M) H) ≤ Nat.card (pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure (VZ T M) H : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hUA
  rw [← hd]
  calc 2 ^ 9 = 16 * 2 ^ 5 := by norm_num
    _ ≤ _ := Nat.mul_le_mul h16 (h32.trans hA32)

theorem Setting146.equality_case_of_irreducible (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H)
    (hirr : ∀ W : Subgroup G, quasithinOmegaOneCenter T ≤ W →
      W ≤ uK T M H ⊔ quasithinOmegaOneCenter T → H ≤ Subgroup.normalizer (W : Set G) →
      W = quasithinOmegaOneCenter T ∨ W = uK T M H ⊔ quasithinOmegaOneCenter T)
    (hcard : Nat.card ↥(uK T M H ⊔ quasithinOmegaOneCenter T) = 2 ^ 5)
    (hnc : ¬ uK T M H ≤ Subgroup.centralizer (pCoreOf 2 H : Set G))
    (hQ : Nat.card (pCoreOf 2 H) = 2 ^ 9) :
    conjClosure (VZ T M) H = uK T M H ⊔ quasithinOmegaOneCenter T ∧
      Nat.card (conjClosure (VZ T M) H) = 2 ^ 5 ∧
      pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
        conjClosure (VZ T M) H ∧
      conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) =
        quasithinOmegaOneCenter T ∧
      (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) = 2 ^ 4 := by
  obtain ⟨hd, hUA⟩ := S.duality_data hH
  have h16 := S.sixteen_le_relIndex_centralizer hH hirr hcard hnc
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have huKU : uK T M H ≤ conjClosure (VZ T M) H := S145.commutator_le_of_le_normalizer hHU
  have hKU : uK T M H ⊔ quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    sup_le huKU (Z_le_conjClosure_VZ T M H)
  have h32 : 2 ^ 5 ≤ Nat.card (conjClosure (VZ T M) H) := hcard ▸ Subgroup.card_le_of_le hKU
  have hA32 : Nat.card (conjClosure (VZ T M) H) ≤ Nat.card (pCoreOf 2 H ⊓
      Subgroup.centralizer (conjClosure (VZ T M) H : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hUA
  set N := (Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex (conjClosure (VZ T M) H) with hN
  set u := Nat.card (conjClosure (VZ T M) H) with hu
  set a := Nat.card (pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) :
    Subgroup G) with ha
  rw [hQ] at hd
  have hNa : N * a = 2 ^ 9 := hd
  have hNu : N * u ≤ 2 ^ 9 := hNa ▸ Nat.mul_le_mul_left N hA32
  have hN16 : N = 2 ^ 4 := by nlinarith
  have hu32 : u = 2 ^ 5 := by nlinarith
  have ha32 : a = 2 ^ 5 := by rw [hN16] at hNa; omega
  have hKGU : uK T M H ⊔ quasithinOmegaOneCenter T = conjClosure (VZ T M) H :=
    Subgroup.eq_of_le_of_card_ge hKU (by rw [hcard]; omega)
  have hAU : pCoreOf 2 H ⊓ Subgroup.centralizer (conjClosure (VZ T M) H : Set G) =
      conjClosure (VZ T M) H :=
    (Subgroup.eq_of_le_of_card_ge hUA (by omega)).symm
  have hZB : quasithinOmegaOneCenter T ≤
      conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :=
    le_inf (Z_le_conjClosure_VZ T M H) (Subgroup.le_centralizer_iff.mp
      ((S.pCoreOf_le_T hH).trans (le_centralizer_quasithinOmegaOneCenter T)))
  have hBcard : Nat.card (conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) :
      Subgroup G) = 2 := by
    have e := Subgroup.relIndex_mul_card
      (conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G))
      (conjClosure (VZ T M) H)
    rw [inf_eq_left.mpr (inf_le_left : conjClosure (VZ T M) H ⊓
      Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ conjClosure (VZ T M) H)] at e
    have hrel : (conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G)).relIndex
        (conjClosure (VZ T M) H) = N := by
      rw [hN, inf_comm, Subgroup.inf_relIndex_right]
    have hu32' : Nat.card ↥(conjClosure (VZ T M) H) = 2 ^ 5 := hu32
    rw [hrel, hN16, hu32'] at e
    omega
  have hBZ : conjClosure (VZ T M) H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) =
      quasithinOmegaOneCenter T :=
    (Subgroup.eq_of_le_of_card_ge hZB (by rw [hBcard, S.card_Z])).symm
  exact ⟨hKGU.symm, hu32, hAU, hBZ, hN16⟩

theorem Setting146.card_T_of_card_pCoreOf (S : Setting146 G T M) {H : Subgroup G}
    (hH : IsHTM T M H) (h4 : (pCoreOf 2 H).relIndex T = 4) (hQ : Nat.card (pCoreOf 2 H) = 2 ^ 9) :
    Nat.card T = 2 ^ 11 := by
  have e := Subgroup.relIndex_mul_card (pCoreOf 2 H) T
  rw [inf_eq_left.mpr (S.pCoreOf_le_T hH), h4, hQ] at e
  omega

end CFSG.Quasithin
