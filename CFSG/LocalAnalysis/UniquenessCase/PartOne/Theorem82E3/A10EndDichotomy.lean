module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace A10Dichotomy

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

private lemma coprime_card_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C W : Subgroup G} (hWC : W ≤ C)
    (hW : Nat.Coprime (Nat.card W) p) :
    Nat.Coprime p (Nat.card ↥(W ⊔ CFSG.Open.relPPrimeCore p C)) := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOsub : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  have hOcop : Nat.Coprime p (Nat.card ↥(CFSG.Open.relPPrimeCore p C)) :=
    coprime_card_relPPrimeCore hp C
  have h := CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_sup_coprime p
    (W.subgroupOf C) ((CFSG.Open.relPPrimeCore p C).subgroupOf C) hOsub
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv]; exact hW.symm)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv]; exact hOcop)
  have hmap : ((W.subgroupOf C) ⊔
      ((CFSG.Open.relPPrimeCore p C).subgroupOf C)).map C.subtype =
      W ⊔ CFSG.Open.relPPrimeCore p C := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hWC,
      Subgroup.map_subgroupOf_eq_of_le hOle]
  have hcard : Nat.card ↥(W ⊔ CFSG.Open.relPPrimeCore p C) =
      Nat.card ↥(W.subgroupOf C ⊔
        ((CFSG.Open.relPPrimeCore p C).subgroupOf C)) := by
    rw [← hmap, Subgroup.card_map_of_injective C.subtype_injective]
  rw [hcard]
  exact h

private lemma le_normalizer_inf_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K A W : Subgroup G} (hKC : K ≤ C) (hAK : A ≤ K)
    (hWA : A ≤ Subgroup.normalizer (W : Set G)) :
    A ≤ Subgroup.normalizer
      (((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K : Subgroup G) : Set G) := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOsub : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  have hAO : A ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore p C : Set G) :=
    hAK.trans (hKC.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOsub))
  have hAsup : A ≤ Subgroup.normalizer
      ((W ⊔ CFSG.Open.relPPrimeCore p C : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hxW := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hWA hx)
    have hxO := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAO hx)
    rw [Subgroup.map_sup, hxW, hxO]
  have hAKN : A ≤ Subgroup.normalizer (K : Set G) := hAK.trans Subgroup.le_normalizer
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hAsup hx) y).mp hy.1,
      (Subgroup.mem_normalizer_iff.mp (hAKN hx) y).mp hy.2⟩
  · intro hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hAsup hx) y).mpr hy.1,
      (Subgroup.mem_normalizer_iff.mp (hAKN hx) y).mpr hy.2⟩

private lemma coprime_card_inf_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K W : Subgroup G} (hWC : W ≤ C)
    (hW : Nat.Coprime (Nat.card W) p) :
    Nat.Coprime (Nat.card ↥((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K)) p := by
  exact (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
    (coprime_card_sup_relPPrimeCore hp hWC hW)).symm

private lemma coprime_card_sup_relPPrimeCore_of_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K : Subgroup G} (hKC : K ≤ C) :
    Nat.Coprime p
      (Nat.card ↥(CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C)) := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOKleC : CFSG.Open.relPPrimeCore p K ≤ C := (relPPrimeCore_le K).trans hKC
  have hOsub : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  have hOcop : Nat.Coprime p (Nat.card ↥(CFSG.Open.relPPrimeCore p C)) :=
    coprime_card_relPPrimeCore hp C
  have hOKcop : Nat.Coprime p (Nat.card ↥(CFSG.Open.relPPrimeCore p K)) :=
    coprime_card_relPPrimeCore hp K
  have h := CFSG.RankThreeCoreUniqueness.Helpers.normal_coprime_sup_coprime p
    ((CFSG.Open.relPPrimeCore p K).subgroupOf C)
    ((CFSG.Open.relPPrimeCore p C).subgroupOf C) hOsub
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOKleC).toEquiv]; exact hOKcop)
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOle).toEquiv]; exact hOcop)
  have hmap : (((CFSG.Open.relPPrimeCore p K).subgroupOf C) ⊔
      ((CFSG.Open.relPPrimeCore p C).subgroupOf C)).map C.subtype =
      CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hOKleC,
      Subgroup.map_subgroupOf_eq_of_le hOle]
  have hcard : Nat.card ↥(CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C) =
      Nat.card ↥(((CFSG.Open.relPPrimeCore p K).subgroupOf C) ⊔
        ((CFSG.Open.relPPrimeCore p C).subgroupOf C)) := by
    rw [← hmap, Subgroup.card_map_of_injective C.subtype_injective]
  rw [hcard]
  exact h

private lemma le_normalizer_sup_relPPrimeCore_of_K {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K : Subgroup G} (hKC : K ≤ C) :
    K ≤ Subgroup.normalizer
      ((CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C : Subgroup G) : Set G) := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOsub : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  have hOKsub : ((CFSG.Open.relPPrimeCore p K).subgroupOf K).Normal :=
    relPPrimeCore_normal hp K
  intro k hk
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hkOK : (CFSG.Open.relPPrimeCore p K).map (↑(MulAut.conj k)) =
      CFSG.Open.relPPrimeCore p K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (relPPrimeCore_le K)).mp hOKsub hk)
  have hkO : (CFSG.Open.relPPrimeCore p C).map (↑(MulAut.conj k)) =
      CFSG.Open.relPPrimeCore p C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOsub (hKC hk))
  rw [Subgroup.map_sup, hkOK, hkO]

private lemma conj_mem_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K : Subgroup G} (hKC : K ≤ C) {o y : G}
    (ho : o ∈ CFSG.Open.relPPrimeCore p C)
    (hy : y ∈ CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C) :
    o * y * o⁻¹ ∈ CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOKleC : CFSG.Open.relPPrimeCore p K ≤ C := (relPPrimeCore_le K).trans hKC
  have hOsub : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  haveI : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal := hOsub
  have hyC : y ∈ C := (sup_le hOKleC hOle) hy
  have hySupC : (⟨y, hyC⟩ : ↥C) ∈
      ((CFSG.Open.relPPrimeCore p K).subgroupOf C) ⊔
        ((CFSG.Open.relPPrimeCore p C).subgroupOf C) := by
    rw [← Subgroup.subgroupOf_sup hOKleC hOle]
    exact hy
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hySupC
  have haOK : (a : G) ∈ CFSG.Open.relPPrimeCore p K := Subgroup.mem_subgroupOf.mp ha
  have hbO : (b : G) ∈ CFSG.Open.relPPrimeCore p C := Subgroup.mem_subgroupOf.mp hb
  have hya : y = (a : G) * (b : G) := by
    have := congrArg Subtype.val hab
    simpa using this.symm
  have hoa : o * (a : G) * o⁻¹ ∈
      CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C := by
    have hxa : (a : G) * o * (a : G)⁻¹ ∈ CFSG.Open.relPPrimeCore p C :=
      (Subgroup.normal_subgroupOf_iff hOle).mp hOsub o (a : G) ho a.2
    have heq : o * (a : G) * o⁻¹ =
        (o * ((a : G) * o * (a : G)⁻¹)⁻¹) * (a : G) := by group
    rw [heq]
    exact Subgroup.mul_mem _
      (Subgroup.mul_mem _
        ((le_sup_right : CFSG.Open.relPPrimeCore p C ≤
          CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C) ho)
        ((le_sup_right : CFSG.Open.relPPrimeCore p C ≤
          CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C)
            ((CFSG.Open.relPPrimeCore p C).inv_mem hxa)))
      ((le_sup_left : CFSG.Open.relPPrimeCore p K ≤
        CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C) haOK)
  have hob : o * (b : G) * o⁻¹ ∈
      CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C :=
    (le_sup_right : CFSG.Open.relPPrimeCore p C ≤
      CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C)
      ((CFSG.Open.relPPrimeCore p C).mul_mem
        ((CFSG.Open.relPPrimeCore p C).mul_mem ho hbO)
        ((CFSG.Open.relPPrimeCore p C).inv_mem ho))
  have heq : o * y * o⁻¹ = (o * (a : G) * o⁻¹) * (o * (b : G) * o⁻¹) := by
    rw [hya]; group
  rw [heq]
  exact Subgroup.mul_mem _ hoa hob

private lemma le_normalizer_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K : Subgroup G} (hKC : K ≤ C) :
    CFSG.Open.relPPrimeCore p C ≤ Subgroup.normalizer
      ((CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C : Subgroup G) : Set G) := by
  intro o ho
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact conj_mem_sup_relPPrimeCore hp hKC ho hy
  · intro hy
    have hz : o⁻¹ * (o * y * o⁻¹) * o ∈
        CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C := by
      simpa using conj_mem_sup_relPPrimeCore hp hKC
        ((CFSG.Open.relPPrimeCore p C).inv_mem ho) hy
    have heq : o⁻¹ * (o * y * o⁻¹) * o = y := by group
    rwa [heq] at hz

private lemma normal_subgroupOf_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K : Subgroup G} (hKC : K ≤ C)
    (hC : C ≤ K ⊔ CFSG.Open.relPPrimeCore p C) :
    ((CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal := by
  let O : Subgroup G := CFSG.Open.relPPrimeCore p C
  have hOle : O ≤ C := relPPrimeCore_le C
  have hOKleC : CFSG.Open.relPPrimeCore p K ≤ C := (relPPrimeCore_le K).trans hKC
  have hCeq : C = K ⊔ O := le_antisymm hC (sup_le hKC hOle)
  have hgoal : ((CFSG.Open.relPPrimeCore p K ⊔ O).subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hOKleC hOle), hCeq]
    exact sup_le
      (le_normalizer_sup_relPPrimeCore_of_K (C := C) (K := K) hp hKC)
      (le_normalizer_sup_relPPrimeCore (C := C) (K := K) hp hKC)
  simpa [O] using hgoal

private lemma relPPrimeCore_sup_relPPrimeCore_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K : Subgroup G} (hKC : K ≤ C)
    (hC : C ≤ K ⊔ CFSG.Open.relPPrimeCore p C) :
    CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C ≤
      CFSG.Open.relPPrimeCore p C := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOKleC : CFSG.Open.relPPrimeCore p K ≤ C := (relPPrimeCore_le K).trans hKC
  exact le_sSup ⟨sup_le hOKleC hOle,
    normal_subgroupOf_sup_relPPrimeCore hp hKC hC,
    coprime_card_sup_relPPrimeCore_of_le hp hKC⟩

private lemma sup_eq_inf_sup_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {C K W : Subgroup G} (hKC : K ≤ C)
    (hC : C ≤ K ⊔ CFSG.Open.relPPrimeCore p C) (hWC : W ≤ C) :
    W ⊔ CFSG.Open.relPPrimeCore p C =
      ((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K) ⊔ CFSG.Open.relPPrimeCore p C := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOsub : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  haveI : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal := hOsub
  apply le_antisymm
  · apply sup_le
    · intro w hw
      have hwC : w ∈ C := hWC hw
      have hwSupC : (⟨w, hwC⟩ : ↥C) ∈
          (K.subgroupOf C) ⊔ ((CFSG.Open.relPPrimeCore p C).subgroupOf C) := by
        rw [← Subgroup.subgroupOf_sup hKC hOle]
        exact hC (hWC hw)
      obtain ⟨k, hk, o, ho, hko⟩ := Subgroup.mem_sup_of_normal_right.mp hwSupC
      have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
      have hoO : (o : G) ∈ CFSG.Open.relPPrimeCore p C := Subgroup.mem_subgroupOf.mp ho
      have hw_eq : w = (k : G) * (o : G) := by
        have := congrArg Subtype.val hko
        simpa using this.symm
      have hkW : (k : G) ∈ W ⊔ CFSG.Open.relPPrimeCore p C := by
        have hkeq : (k : G) = w * (o : G)⁻¹ := by rw [hw_eq]; group
        rw [hkeq]
        exact Subgroup.mul_mem _
          ((le_sup_left : W ≤ W ⊔ CFSG.Open.relPPrimeCore p C) hw)
          ((le_sup_right : CFSG.Open.relPPrimeCore p C ≤
            W ⊔ CFSG.Open.relPPrimeCore p C)
            ((CFSG.Open.relPPrimeCore p C).inv_mem hoO))
      have hk_W₁ : (k : G) ∈ (W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K := ⟨hkW, hkK⟩
      rw [hw_eq]
      exact Subgroup.mul_mem _
        ((le_sup_left : (W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K ≤
          ((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K) ⊔
            CFSG.Open.relPPrimeCore p C) hk_W₁)
        ((le_sup_right : CFSG.Open.relPPrimeCore p C ≤
          ((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K) ⊔
            CFSG.Open.relPPrimeCore p C) hoO)
    · exact le_sup_right
  · exact sup_le inf_le_left le_sup_right

theorem inf_le_relPPrimeCore {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C X : Subgroup G} (hXC : X ≤ C) :
    CFSG.Open.relPPrimeCore p C ⊓ X ≤ CFSG.Open.relPPrimeCore p X := by
  have hOle : CFSG.Open.relPPrimeCore p C ≤ C := relPPrimeCore_le C
  have hOnorm : ((CFSG.Open.relPPrimeCore p C).subgroupOf C).Normal :=
    relPPrimeCore_normal hp C
  have hCnorm : C ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore p C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOnorm
  have hXnorm : X ≤ Subgroup.normalizer (CFSG.Open.relPPrimeCore p C : Set G) :=
    hXC.trans hCnorm
  refine le_sSup ⟨inf_le_right, ?_, ?_⟩
  · rw [Subgroup.inf_subgroupOf_right]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hXnorm
  · exact Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_relPPrimeCore hp C)

theorem le_relPPrimeCore_of_le_sup {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {C K A W : Subgroup G} (hKC : K ≤ C)
    (hC : C ≤ K ⊔ CFSG.Open.relPPrimeCore p C)
    (hAK : A ≤ K)
    (hK : ∀ W₁ : Subgroup G, W₁ ≤ K → A ≤ Subgroup.normalizer (W₁ : Set G) →
      Nat.Coprime (Nat.card W₁) p → W₁ ≤ CFSG.Open.relPPrimeCore p K)
    (hWC : W ≤ C) (hWA : A ≤ Subgroup.normalizer (W : Set G))
    (hW : Nat.Coprime (Nat.card W) p) : W ≤ CFSG.Open.relPPrimeCore p C := by
  have hW₁cop : Nat.Coprime
      (Nat.card ↥((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K)) p :=
    coprime_card_inf_sup_relPPrimeCore (K := K) hp hWC hW
  have hAW₁ : A ≤ Subgroup.normalizer
      (((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K : Subgroup G) : Set G) :=
    le_normalizer_inf_sup_relPPrimeCore (C := C) (K := K) (A := A) hp hKC hAK hWA
  have hW₁OK : (W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K ≤
      CFSG.Open.relPPrimeCore p K :=
    hK _ inf_le_right hAW₁ hW₁cop
  have hOKO : CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C ≤
      CFSG.Open.relPPrimeCore p C :=
    relPPrimeCore_sup_relPPrimeCore_le hp hKC hC
  have hDed : W ⊔ CFSG.Open.relPPrimeCore p C =
      ((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K) ⊔ CFSG.Open.relPPrimeCore p C :=
    sup_eq_inf_sup_relPPrimeCore (C := C) (K := K) (W := W) hp hKC hC hWC
  calc W ≤ W ⊔ CFSG.Open.relPPrimeCore p C := le_sup_left
    _ = ((W ⊔ CFSG.Open.relPPrimeCore p C) ⊓ K) ⊔
        CFSG.Open.relPPrimeCore p C := hDed
    _ ≤ CFSG.Open.relPPrimeCore p K ⊔ CFSG.Open.relPPrimeCore p C :=
        sup_le (hW₁OK.trans le_sup_left) le_sup_right
    _ ≤ CFSG.Open.relPPrimeCore p C := hOKO

end A10Dichotomy

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

theorem deg_zpowers_mem {F : A10Frame c} {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1) :
    F.deg (Subgroup.zpowers a) = 3 ∨ F.deg (Subgroup.zpowers a) = 6 ∨
      F.deg (Subgroup.zpowers a) = 9 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have hx : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  have hx1 : F.phiA ⟨a, F.A_le_M haA⟩ ≠ 1 := by
    intro h1
    have hker : (⟨a, F.A_le_M haA⟩ : ↥D.M) ∈ F.phiA.ker := MonoidHom.mem_ker.mpr h1
    have hdvd : orderOf (⟨a, F.A_le_M haA⟩ : ↥D.M) ∣ Nat.card ↥F.phiA.ker :=
      Subgroup.orderOf_dvd_natCard _ hker
    have hordM : orderOf (⟨a, F.A_le_M haA⟩ : ↥D.M) = 3 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_eq_prime (F.elemAbelian.2 a haA) ha1
    rw [hordM] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).mp
      F.coprime_card_ker_phiA.symm hdvd
  have hsupp := A10Perm.card_support_of_mem_atilde hx hx1
  have hdeq : F.deg (Subgroup.zpowers a) =
      (F.phiA ⟨a, F.A_le_M haA⟩).support.card := F.deg_zpowers_eq haL
  rw [hdeq]
  exact hsupp

private theorem le_relPPrimeCore_of_map_subgroupOf {F : A10Frame c} {X W : Subgroup G}
    (hXM : X ≤ D.M) (hWX : W ≤ X)
    (hmap : (W.subgroupOf D.M).map F.phiA ≤
      CFSG.Open.relPPrimeCore 3 ((X.subgroupOf D.M).map F.phiA)) :
    W ≤ CFSG.Open.relPPrimeCore 3 X := by
  have hWm : W.subgroupOf D.M ≤ CFSG.Open.relPPrimeCore 3 (X.subgroupOf D.M) :=
    CoprimeImage.le_relPPrimeCore_of_map_le F.phiA F.coprime_card_ker_phiA
      (by
        intro w hw
        exact Subgroup.mem_subgroupOf.mpr (hWX (Subgroup.mem_subgroupOf.mp hw)))
      hmap
  have hker : Nat.Coprime (Nat.card ↥(D.M.subtype.ker)) 3 := by
    rw [Subgroup.ker_subtype, Subgroup.card_bot]
    exact Nat.coprime_one_left 3
  have h := Subgroup.map_mono (f := D.M.subtype) hWm
  rw [CoprimeImage.relPPrimeCore_map_of_coprime_ker D.M.subtype hker (X.subgroupOf D.M),
    Subgroup.map_subgroupOf_eq_of_le hXM,
    Subgroup.map_subgroupOf_eq_of_le (hWX.trans hXM)] at h
  exact h

private theorem map_le_centralizer_of_le_centralizer {F : A10Frame c}
    {a : G} (haA : a ∈ F.A) {K : Subgroup G}
    (hKleC : K ≤ Subgroup.centralizer ({a} : Set G)) :
    (K.subgroupOf D.M).map F.phiA ≤
      Subgroup.centralizer ({(F.phiA ⟨a, F.A_le_M haA⟩)} : Set (Equiv.Perm (Fin 10))) := by
  intro y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmC : (m : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    hKleC (Subgroup.mem_subgroupOf.mp hm)
  have hcomm : Commute m (⟨a, F.A_le_M haA⟩ : ↥D.M) := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hmC
  exact hcomm.map F.phiA

private theorem map_le_relPPrimeCore_of_inf_centralizer {F : A10Frame c}
    {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdeg : F.deg (Subgroup.zpowers a) = 6 ∨ F.deg (Subgroup.zpowers a) = 9)
    {W₁ K : Subgroup G} (hW₁K : W₁ ≤ K) (hKM : K ≤ D.M)
    (hKleC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hAW₁ : F.A ≤ Subgroup.normalizer (W₁ : Set G))
    (hW₁cop : Nat.Coprime (Nat.card W₁) 3) :
    (W₁.subgroupOf D.M).map F.phiA ≤
      CFSG.Open.relPPrimeCore 3 ((K.subgroupOf D.M).map F.phiA) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have hdeq : F.deg (Subgroup.zpowers a) =
      (F.phiA ⟨a, F.A_le_M haA⟩).support.card := F.deg_zpowers_eq haL
  have hx : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  have hsupp : (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 6 ∨
      (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 9 := by
    rw [← hdeq]
    exact hdeg
  have hYx := map_le_centralizer_of_le_centralizer (F := F) haA hKleC
  have hWmapY : (W₁.subgroupOf D.M).map F.phiA ≤ (K.subgroupOf D.M).map F.phiA :=
    Subgroup.map_mono (by
      intro w hw
      exact Subgroup.mem_subgroupOf.mpr (hW₁K (Subgroup.mem_subgroupOf.mp hw)))
  have hAWm : F.A.subgroupOf D.M ≤
      Subgroup.normalizer ((W₁.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hAW₁ (Subgroup.mem_subgroupOf.mp hm)) (w : G)).mp hw
  have hAWmap : A10Perm.atilde ≤ Subgroup.normalizer
      (((W₁.subgroupOf D.M).map F.phiA) : Set (Equiv.Perm (Fin 10))) := by
    rw [← F.map_A_phiA]
    exact CoprimeImage.map_le_normalizer_map F.phiA hAWm
  have hW₁M : W₁ ≤ D.M := hW₁K.trans hKM
  have hWmcop : Nat.Coprime (Nat.card ↥(W₁.subgroupOf D.M)) 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW₁M).toEquiv]
    exact hW₁cop
  have hWmapcop : Nat.Coprime (Nat.card ↥((W₁.subgroupOf D.M).map F.phiA)) 3 :=
    (Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ _) hWmcop.symm).symm
  exact A10Perm.le_relPPrimeCore_of_card_support hx hsupp hYx hWmapY hAWmap hWmapcop

private theorem le_relPPrimeCore_of_inf_centralizer {F : A10Frame c}
    {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdeg : F.deg (Subgroup.zpowers a) = 6 ∨ F.deg (Subgroup.zpowers a) = 9)
    {W₁ K : Subgroup G} (hW₁K : W₁ ≤ K) (hKM : K ≤ D.M)
    (hKleC : K ≤ Subgroup.centralizer ({a} : Set G))
    (hAW₁ : F.A ≤ Subgroup.normalizer (W₁ : Set G))
    (hW₁cop : Nat.Coprime (Nat.card W₁) 3) :
    W₁ ≤ CFSG.Open.relPPrimeCore 3 K :=
  le_relPPrimeCore_of_map_subgroupOf hKM hW₁K
    (map_le_relPPrimeCore_of_inf_centralizer haA ha1 hdeg hW₁K hKM hKleC hAW₁ hW₁cop)

private theorem degree_six_nine {F : A10Frame c}
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {H : Subgroup G} {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdeg : F.deg (Subgroup.zpowers a) = 6 ∨ F.deg (Subgroup.zpowers a) = 9)
    {W : Subgroup G} (hWX : W ≤ H ⊓ Subgroup.centralizer ({a} : Set G))
    (hWA : F.A ≤ Subgroup.normalizer (W : Set G))
    (hWcop : Nat.Coprime (Nat.card W) 3) :
    W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf a = 3 := orderOf_eq_prime (F.elemAbelian.2 a haA) ha1
  have hBA : Subgroup.zpowers a ≤ F.A := Subgroup.zpowers_le.mpr haA
  have hBcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hCdef
  set K : Subgroup G := C ⊓ D.M with hKdef
  have hKC : K ≤ C := by rw [hKdef]; exact inf_le_left
  have hKM : K ≤ D.M := by rw [hKdef]; exact inf_le_right
  have hCz : C ≤ K ⊔ CFSG.Open.relPPrimeCore 3 C := by
    have hz := hC (Subgroup.zpowers a) hBA hBcard
    have hcent : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) = C := by
      rw [hCdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [hcent] at hz
    simpa [hKdef] using hz
  have hAK : F.A ≤ K := by
    rw [hKdef]
    refine le_inf ?_ F.A_le_M
    intro x hx
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (F.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)
  have hK' : ∀ W₁ : Subgroup G, W₁ ≤ K → F.A ≤ Subgroup.normalizer (W₁ : Set G) →
      Nat.Coprime (Nat.card W₁) 3 → W₁ ≤ CFSG.Open.relPPrimeCore 3 K :=
    fun W₁ hW₁K hAW₁ hW₁cop =>
      le_relPPrimeCore_of_inf_centralizer haA ha1 hdeg hW₁K hKM hKC hAW₁ hW₁cop
  have hW_C : W ≤ C := hWX.trans inf_le_right
  have hWcore : W ≤ CFSG.Open.relPPrimeCore 3 C :=
    A10Dichotomy.le_relPPrimeCore_of_le_sup (p := 3) (by norm_num)
      (C := C) (K := K) (A := F.A) (W := W) hKC hCz hAK hK' hW_C hWA hWcop
  have hWX' : W ≤ H ⊓ C := hWX
  exact (le_inf hWcore hWX').trans
    (A10Dichotomy.inf_le_relPPrimeCore (p := 3) (by norm_num) (C := C) (X := H ⊓ C) inf_le_right)

private theorem degree_three_le_M {F : A10Frame c} (hF : A10Facts F)
    {H : Subgroup G} {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdeg : F.deg (Subgroup.zpowers a) = 3) :
    H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hord : orderOf a = 3 := orderOf_eq_prime (F.elemAbelian.2 a haA) ha1
  have hBA : Subgroup.zpowers a ≤ F.A := Subgroup.zpowers_le.mpr haA
  have hBcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hNA : Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ D.M :=
    hF.normalizer_A1 _ hBA hBcard hdeg
  have hcent : Subgroup.centralizer ({a} : Set G) =
      Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  calc H ⊓ Subgroup.centralizer ({a} : Set G)
      ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right
    _ = Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := hcent
    _ ≤ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _
    _ ≤ D.M := hNA

private theorem degree_three_atilde_le_map {F : A10Frame c}
    {H : Subgroup G} (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A) :
    A10Perm.atilde ≤
      ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA := by
  have hAX : F.A ≤ H ⊓ Subgroup.centralizer ({a} : Set G) := by
    refine le_inf hAH ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (F.elemAbelian.1.is_comm.comm ⟨x, hx⟩ ⟨a, haA⟩)
  rw [← F.map_A_phiA]
  exact Subgroup.map_mono (by
    intro m hm
    exact Subgroup.mem_subgroupOf.mpr (hAX (Subgroup.mem_subgroupOf.mp hm)))

private theorem degree_three_map_le_centralizer {F : A10Frame c}
    {H : Subgroup G} {a : G} (haA : a ∈ F.A) :
    ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA ≤
      Subgroup.centralizer
        ({(F.phiA ⟨a, F.A_le_M haA⟩)} : Set (Equiv.Perm (Fin 10))) :=
  map_le_centralizer_of_le_centralizer (F := F) haA inf_le_right

private theorem degree_three_core {F : A10Frame c}
    {H : Subgroup G} {a : G} (haA : a ∈ F.A)
    (hXM : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M)
    (hcore : ∀ W' : Subgroup (Equiv.Perm (Fin 10)),
      W' ≤ ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA →
      A10Perm.atilde ≤ Subgroup.normalizer (W' : Set (Equiv.Perm (Fin 10))) →
      Nat.Coprime (Nat.card W') 3 →
      W' ≤ CFSG.Open.relPPrimeCore 3
        (((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA))
    {W : Subgroup G} (hWX : W ≤ H ⊓ Subgroup.centralizer ({a} : Set G))
    (hWA : F.A ≤ Subgroup.normalizer (W : Set G))
    (hWcop : Nat.Coprime (Nat.card W) 3) :
    W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G)) := by
  have hWM : W ≤ D.M := hWX.trans hXM
  have hWmX : W.subgroupOf D.M ≤
      (H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M := by
    intro w hw
    exact Subgroup.mem_subgroupOf.mpr (hWX (Subgroup.mem_subgroupOf.mp hw))
  have hAWm : F.A.subgroupOf D.M ≤
      Subgroup.normalizer ((W.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
    rw [Subgroup.le_normalizer_iff]
    intro m hm w hw
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hWA (Subgroup.mem_subgroupOf.mp hm)) (w : G)).mp hw
  have hAWmap : A10Perm.atilde ≤ Subgroup.normalizer
      (((W.subgroupOf D.M).map F.phiA) : Set (Equiv.Perm (Fin 10))) := by
    rw [← F.map_A_phiA]
    exact CoprimeImage.map_le_normalizer_map F.phiA hAWm
  have hWmcop : Nat.Coprime (Nat.card ↥(W.subgroupOf D.M)) 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWM).toEquiv]
    exact hWcop
  have hWmapcop : Nat.Coprime (Nat.card ↥((W.subgroupOf D.M).map F.phiA)) 3 :=
    (Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ _) hWmcop.symm).symm
  have hWmapcore : (W.subgroupOf D.M).map F.phiA ≤
      CFSG.Open.relPPrimeCore 3
        (((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA) :=
    hcore _ (Subgroup.map_mono hWmX) hAWmap hWmapcop
  exact le_relPPrimeCore_of_map_subgroupOf hXM hWX hWmapcore

private theorem degree_three_dichotomy {F : A10Frame c} (hF : A10Facts F)
    {H : Subgroup G} (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdeg : F.deg (Subgroup.zpowers a) = 3) :
    (∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
        F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
        W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G))) ∨
      (H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M ∧
        A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
          ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA) := by
  have hXM : H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M :=
    degree_three_le_M (H := H) hF haA ha1 hdeg
  have hAY := degree_three_atilde_le_map (F := F) (H := H) hAH haA
  have hYx := degree_three_map_le_centralizer (F := F) (H := H) haA
  have haL : a ∈ c.L := F.P_le_L (F.A_le haA)
  have hsupp3 : (F.phiA ⟨a, F.A_le_M haA⟩).support.card = 3 := by
    rw [← F.deg_zpowers_eq haL]
    exact hdeg
  have hx : F.phiA ⟨a, F.A_le_M haA⟩ ∈ A10Perm.atilde := by
    rw [← F.map_A_phiA]
    exact Subgroup.mem_map_of_mem F.phiA (Subgroup.mem_subgroupOf.mpr haA)
  rcases A10Perm.le_relPPrimeCore_or_altOff_le hx hsupp3 hAY hYx with hcore | halt
  · exact Or.inl fun W hWX hWA hWcop => degree_three_core haA hXM hcore hWX hWA hWcop
  · exact Or.inr ⟨hXM, halt⟩

private theorem degree_three (F : A10Frame c) (hF : A10Facts F)
    {H : Subgroup G} (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1)
    (hdeg : F.deg (Subgroup.zpowers a) = 3) :
    (∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
        F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
        W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G))) ∨
      (F.deg (Subgroup.zpowers a) = 3 ∧ H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M ∧
        A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
          ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA) := by
  rcases degree_three_dichotomy hF hAH haA ha1 hdeg with h | ⟨hXM, halt⟩
  · exact Or.inl h
  · exact Or.inr ⟨hdeg, hXM, halt⟩

theorem dichotomy_centralizer (F : A10Frame c) (hF : A10Facts F)
    (hC : ∀ B ≤ F.A, Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ (Subgroup.centralizer (B : Set G) ⊓ D.M) ⊔
        CFSG.Open.relPPrimeCore 3 (Subgroup.centralizer (B : Set G)))
    {H : Subgroup G} (hAH : F.A ≤ H) {a : G} (haA : a ∈ F.A) (ha1 : a ≠ 1) :
    (∀ W : Subgroup G, W ≤ H ⊓ Subgroup.centralizer ({a} : Set G) →
        F.A ≤ Subgroup.normalizer (W : Set G) → Nat.Coprime (Nat.card W) 3 →
        W ≤ CFSG.Open.relPPrimeCore 3 (H ⊓ Subgroup.centralizer ({a} : Set G))) ∨
      (F.deg (Subgroup.zpowers a) = 3 ∧ H ⊓ Subgroup.centralizer ({a} : Set G) ≤ D.M ∧
        A10Perm.altOff (F.phiA ⟨a, F.A_le_M haA⟩).support ≤
          ((H ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf D.M).map F.phiA) := by
  rcases deg_zpowers_mem (F := F) haA ha1 with hdeg | hdeg | hdeg
  · exact degree_three F hF hAH haA ha1 hdeg
  · exact Or.inl fun W hWX hWA hWcop =>
      degree_six_nine hC haA ha1 (Or.inl hdeg) hWX hWA hWcop
  · exact Or.inl fun W hWX hWA hWcop =>
      degree_six_nine hC haA ha1 (Or.inr hdeg) hWX hWA hWcop

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
