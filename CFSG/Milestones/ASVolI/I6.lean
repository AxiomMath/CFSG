module

public import Mathlib
public import CFSG.Foundations.Basic
public import CFSG.Open.QuasithinDefs
public import CFSG.Open.LocalVocabulary
public import CFSG.Blueprint.Catalog
public import CFSG.Milestones.ASVolI.I1
public import CFSG.Milestones.ASVolI.I2
public import CFSG.Quasithin.Background.I62Main
public import CFSG.RankThree.GF2n.Tim77Prop24Two
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimpleProof
public import CFSG.Timmesfeld.ARS.NaturalModule
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Foundations.HigherElementaryThompson
public import CFSG.GH74.SmallRanks.PSL
public import CFSG.RankThree.GF2n.Tim78Lemma218
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.Special.TwoCore

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section TI

variable {G : Type} [Group G]

@[expose] def IsTISubgroup (X : Subgroup G) : Prop :=
  ∀ g : G, g ∉ Subgroup.normalizer (X : Set G) → X ⊓ CFSG.conjugate X g = ⊥

@[expose] def ControlsFusionOfElements (M X : Subgroup G) : Prop :=
  ∀ x ∈ X, ∀ g : G, g⁻¹ * x * g ∈ X → ∃ m ∈ M, m⁻¹ * x * m = g⁻¹ * x * g

@[expose] def IsDirectProductOf (A B X : Subgroup G) : Prop :=
  (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) ∧ A ⊓ B = ⊥ ∧ A ⊔ B = X

@[expose] def IsInvariantUnder (X B : Subgroup G) : Prop :=
  X ≤ Subgroup.normalizer (B : Set G)

@[expose] def IsChiefSection (X Y P Q : Subgroup G) : Prop :=
  Q < P ∧ P ≤ Y ∧ IsInvariantUnder X P ∧ IsInvariantUnder X Q ∧
    ∀ B : Subgroup G, IsInvariantUnder X B → Q ≤ B → B ≤ P → B = Q ∨ B = P

@[expose] def IsConjModuleIso (X P Q : Subgroup G) (M : Type) [AddCommGroup M]
    (act : ↥X → M → M) : Prop :=
  IsInvariantUnder X P ∧ IsInvariantUnder X Q ∧
  ∃ φ : ↥P →* Multiplicative M, Function.Surjective φ ∧ φ.ker = Q.subgroupOf P ∧
    ∀ (x : ↥X) (p q : ↥P), (q : G) = (x : G) * p * (x : G)⁻¹ →
      φ q = Multiplicative.ofAdd (act x (Multiplicative.toAdd (φ p)))

@[expose] def ActsTriviallyOnSection (P Q : Subgroup G) (x : G) : Prop :=
  ∀ p ∈ P, x⁻¹ * p * x * p⁻¹ ∈ Q

@[expose] def IsNaturalSection (X Y P Q : Subgroup G) [(Y.subgroupOf X).Normal] : Prop :=
  (∃ m : ℕ, Odd m ∧ 1 < m ∧ Nonempty (↥X ⧸ Y.subgroupOf X ≃* DihedralGroup m) ∧
    ∀ x ∈ X, ActsTriviallyOnSection P Q x → x ∈ Y) ∨
  (∃ (n : ℕ) (_ : 1 ≤ n) (e : ↥X ⧸ Y.subgroupOf X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)),
    IsConjModuleIso X P Q (Fin 2 → GaloisField 2 n)
      (fun x v => ((e (x : ↥X ⧸ Y.subgroupOf X) : Matrix.SpecialLinearGroup (Fin 2)
        (GaloisField 2 n)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec v)) ∨
  (∃ (n : ℕ) (_ : 1 ≤ n) (e : ↥X ⧸ Y.subgroupOf X ≃* Sz n),
    IsConjModuleIso X P Q (Fin 4 → GaloisField 2 (2 * n + 1))
      (fun x v => (((e (x : ↥X ⧸ Y.subgroupOf X) : GL (Fin 4) (GaloisField 2 (2 * n + 1))) :
        Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1)))).mulVec v))

@[expose] def NIn (V A : Subgroup G) : Subgroup G := V ⊓ Subgroup.normalizer (A : Set G)

@[expose] def pairY (V A : Subgroup G) : Subgroup G := NIn V A ⊔ NIn A V

@[expose] def QuotientIsDihedralL2OrSz (X Y : Subgroup G) [(Y.subgroupOf X).Normal] : Prop :=
  (∃ m : ℕ, Odd m ∧ Nonempty (↥X ⧸ Y.subgroupOf X ≃* DihedralGroup m)) ∨
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (↥X ⧸ Y.subgroupOf X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) ∨
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (↥X ⧸ Y.subgroupOf X ≃* Sz n))

@[expose] def QuotientIsL2OrDihedral (X Y : Subgroup G) [(Y.subgroupOf X).Normal] : Prop :=
  (∃ n : ℕ, 1 ≤ n ∧ Nonempty (↥X ⧸ Y.subgroupOf X ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))) ∨
  (∃ m : ℕ, Odd m ∧ Nonempty (↥X ⧸ Y.subgroupOf X ≃* DihedralGroup m))

@[expose] def IsCompletelyReducibleUnder (X Y : Subgroup G) : Prop :=
  ∀ B : Subgroup G, IsInvariantUnder X B → B ≤ Y →
    ∃ C : Subgroup G, IsInvariantUnder X C ∧ C ≤ Y ∧ B ⊓ C = ⊥ ∧ B ⊔ C = Y

@[expose] def ImageRankEqRank (V X Y : Subgroup G) [(Y.subgroupOf X).Normal] : Prop :=
  CFSG.pRank 2 ↥((V.subgroupOf X).map (QuotientGroup.mk' (Y.subgroupOf X))) =
    CFSG.pRank 2 (↥X ⧸ Y.subgroupOf X)

end TI

end CFSG.ASVolI.ChIJK

namespace CFSG.ASVolI

open CFSG.Open CFSG.Blueprint CFSG.ASVolI.ChIJK
open scoped MatrixGroups

@[expose] def I_6_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X : Subgroup G), IsPGroup 2 X →
    (((∀ x ∈ X, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G)) ∧
        ControlsFusionOfElements (Subgroup.normalizer (X : Set G)) X) → IsTISubgroup X) ∧
    ((∃ L : Subgroup G, L ≤ Subgroup.centralizer (X : Set G) ∧
        CFSG.maximalTwoLocalsContaining (L : Set G) = {Subgroup.normalizer (X : Set G)}) →
      IsTISubgroup X)

section BurnsideIc6

private theorem burnsideIc_ti_mem_conjugate {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_ti_of_centralizer_fusion {G : Type} [Group G] {X : Subgroup G}
    (hC : ∀ x ∈ X, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (X : Set G))
    (hF : ControlsFusionOfElements (Subgroup.normalizer (X : Set G)) X) : IsTISubgroup X := by
  intro g hg
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  apply hg
  have hxg : g * x * g⁻¹ ∈ X := burnsideIc_ti_mem_conjugate.1 hx.2
  obtain ⟨m, hm, hmx⟩ := hF x hx.1 g⁻¹ (by simpa using hxg)
  rw [inv_inv] at hmx
  have hc : m * g ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    calc h * (m * g) = m * (m⁻¹ * h * m) * g := by group
      _ = m * (g * h * g⁻¹) * g := by rw [hmx]
      _ = m * g * h := by group
  have hmg := hC x hx.1 hx1 hc
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hm) hmg
  simpa using this

private theorem burnsideIc_ti_map_conj_eq_iff {G : Type} [Group G] (U : Subgroup G) (g : G) :
    U.map (MulAut.conj g).toMonoidHom = U ↔ g ∈ Subgroup.normalizer (U : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.symm

private theorem burnsideIc_ti_card_conjugate {G : Type} [Group G] (H : Subgroup G) (g : G) :
    Nat.card (CFSG.conjugate H g) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

private theorem burnsideIc_ti_conjugate_ne_bot {G : Type} [Group G] {H : Subgroup G} (hH : H ≠ ⊥)
    (g : G) : CFSG.conjugate H g ≠ ⊥ := by
  intro h
  apply hH
  rw [Subgroup.eq_bot_iff_card] at h ⊢
  rwa [burnsideIc_ti_card_conjugate] at h

private theorem burnsideIc_ti_conjugate_normalizer {G : Type} [Group G] (P : Subgroup G) (g : G) :
    CFSG.conjugate (Subgroup.normalizer (P : Set G)) g =
      Subgroup.normalizer ((CFSG.conjugate P g : Subgroup G) : Set G) := by
  ext n
  rw [burnsideIc_ti_mem_conjugate, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [burnsideIc_ti_mem_conjugate, burnsideIc_ti_mem_conjugate]
    have e : g * (n * x * n⁻¹) * g⁻¹ = g * n * g⁻¹ * (g * x * g⁻¹) * (g * n * g⁻¹)⁻¹ := by group
    rw [e]
    exact h (g * x * g⁻¹)
  · intro h p
    have := h (g⁻¹ * p * g)
    rw [burnsideIc_ti_mem_conjugate, burnsideIc_ti_mem_conjugate] at this
    have e1 : g * (g⁻¹ * p * g) * g⁻¹ = p := by group
    have e2 : g * (n * (g⁻¹ * p * g) * n⁻¹) * g⁻¹ = g * n * g⁻¹ * p * (g * n * g⁻¹)⁻¹ := by group
    rwa [e1, e2] at this

private theorem burnsideIc_ti_isPLocal_conjugate {G : Type} [Group G] {H : Subgroup G}
    (hH : CFSG.IsPLocal 2 H) (g : G) : CFSG.IsPLocal 2 (CFSG.conjugate H g) := by
  obtain ⟨P, hP1, hP2, rfl⟩ := hH
  exact ⟨CFSG.conjugate P g, burnsideIc_ti_conjugate_ne_bot hP1 g, hP2.map _,
    burnsideIc_ti_conjugate_normalizer P g⟩

private theorem burnsideIc_ti_exists_maximal {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : CFSG.IsPLocal 2 H) : ∃ H' : Subgroup G, CFSG.IsMaximalTwoLocal H' ∧ H ≤ H' := by
  obtain ⟨H', ⟨hH'1, hH'2⟩, hmax⟩ := Set.exists_max_image
    {K : Subgroup G | CFSG.IsPLocal 2 K ∧ H ≤ K} (fun K => Nat.card K) (Set.toFinite _)
    ⟨H, hH, le_rfl⟩
  refine ⟨H', ⟨hH'1, fun K hK hloc => ?_⟩, hH'2⟩
  have := hmax K ⟨hloc, hH'2.trans hK.le⟩
  exact absurd (Subgroup.card_lt_of_lt hK) (not_lt.2 this)

private theorem burnsideIc_ti_le_of_twoLocal {G : Type} [Group G] [Finite G] {L M H : Subgroup G}
    (hL : CFSG.maximalTwoLocalsContaining (L : Set G) = {M}) (hH : CFSG.IsPLocal 2 H)
    (hLH : L ≤ H) : H ≤ M := by
  obtain ⟨H', hH'max, hHH'⟩ := burnsideIc_ti_exists_maximal hH
  have hmem : H' ∈ CFSG.maximalTwoLocalsContaining (L : Set G) := ⟨hH'max, hLH.trans hHH'⟩
  rw [hL, Set.mem_singleton_iff] at hmem
  exact hmem ▸ hHH'

private theorem burnsideIc_ti_conj_mem_normalizer {G : Type} [Group G] {D : Subgroup G} {n : G}
    (g : G)
    (hn : n ∈ Subgroup.normalizer (D : Set G)) :
    g * n * g⁻¹ ∈
      Subgroup.normalizer ((D.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [← burnsideIc_ti_map_conj_eq_iff, Subgroup.map_map]
  have hcomp : (MulAut.conj (g * n * g⁻¹)).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj n).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← Subgroup.map_map, (burnsideIc_ti_map_conj_eq_iff D n).2 hn]

private theorem burnsideIc_ti_mem_normalizer_sup {G : Type} [Group G] {A B : Subgroup G} {m : G}
    (hA : m ∈ Subgroup.normalizer (A : Set G)) (hB : m ∈ Subgroup.normalizer (B : Set G)) :
    m ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [← burnsideIc_ti_map_conj_eq_iff, Subgroup.map_sup, (burnsideIc_ti_map_conj_eq_iff A m).2 hA,
    (burnsideIc_ti_map_conj_eq_iff B m).2 hB]

open CFSG.ASVolI.ChIJK in
private theorem burnsideIc_ti_of_unique_twoLocal {G : Type} [Group G] [Finite G] {X L : Subgroup G}
    (hX : IsPGroup 2 X) (hLC : L ≤ Subgroup.centralizer (X : Set G))
    (hL : CFSG.maximalTwoLocalsContaining (L : Set G) = {Subgroup.normalizer (X : Set G)}) :
    IsTISubgroup X := by
  intro g hg
  by_contra hD
  have hMmem : Subgroup.normalizer (X : Set G) ∈ CFSG.maximalTwoLocalsContaining (L : Set G) := by
    rw [hL]
    exact Set.mem_singleton _
  have hMmax : CFSG.IsMaximalTwoLocal (Subgroup.normalizer (X : Set G)) := hMmem.1
  have hX1 : X ≠ ⊥ := fun h => hD (by rw [h]; simp)
  have hDX : X ⊓ CFSG.conjugate X g ≤ X := inf_le_left
  have hE_le : (X ⊓ CFSG.conjugate X g).map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨d, hd, rfl⟩
    exact burnsideIc_ti_mem_conjugate.1 hd.2
  have hE1 : (X ⊓ CFSG.conjugate X g).map (MulAut.conj g).toMonoidHom ≠ ⊥ := by
    intro h
    apply hD
    rw [Subgroup.eq_bot_iff_card] at h ⊢
    rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h
  have hE2 : IsPGroup 2 ((X ⊓ CFSG.conjugate X g).map (MulAut.conj g).toMonoidHom) :=
    (hX.to_le hDX).map _
  have hLE : L ≤ Subgroup.normalizer
      (((X ⊓ CFSG.conjugate X g).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    hLC.trans ((Subgroup.centralizer_le hE_le).trans (Subgroup.centralizer_le_normalizer _))
  have hNE := burnsideIc_ti_le_of_twoLocal hL ⟨_, hE1, hE2, rfl⟩ hLE
  have hND : Subgroup.normalizer ((X ⊓ CFSG.conjugate X g : Subgroup G) : Set G) ≤
      CFSG.conjugate (Subgroup.normalizer (X : Set G)) g := by
    intro n hn
    rw [burnsideIc_ti_mem_conjugate]
    exact hNE (burnsideIc_ti_conj_mem_normalizer g hn)
  have hLD : L ≤ CFSG.conjugate (Subgroup.normalizer (X : Set G)) g :=
    hLC.trans ((Subgroup.centralizer_le hDX).trans
      ((Subgroup.centralizer_le_normalizer _).trans hND))
  have hMgM : CFSG.conjugate (Subgroup.normalizer (X : Set G)) g ≤
      Subgroup.normalizer (X : Set G) :=
    burnsideIc_ti_le_of_twoLocal hL (burnsideIc_ti_isPLocal_conjugate hMmax.1 g) hLD
  have hMg : CFSG.conjugate (Subgroup.normalizer (X : Set G)) g =
      Subgroup.normalizer (X : Set G) :=
    Subgroup.eq_of_le_of_card_ge hMgM (burnsideIc_ti_card_conjugate _ _).ge
  set M := Subgroup.normalizer (X : Set G) with hMdef
  obtain ⟨Y, ⟨hY1, hY2, hMY⟩, hYmax⟩ := Set.exists_max_image
    {Y : Subgroup G | Y ≠ ⊥ ∧ IsPGroup 2 Y ∧ M ≤ Subgroup.normalizer (Y : Set G)}
    (fun Y => Nat.card Y) (Set.toFinite _) ⟨X, hX1, hX, le_rfl⟩
  have hnorm : ∀ Z : Subgroup G, Z ≠ ⊥ → IsPGroup 2 Z → M ≤ Subgroup.normalizer (Z : Set G) →
      Subgroup.normalizer (Z : Set G) = M := by
    intro Z hZ1 hZ2 hMZ
    by_contra hne
    exact hMmax.2 _ (lt_of_le_of_ne hMZ (fun h => hne h.symm)) ⟨Z, hZ1, hZ2, rfl⟩
  have hNY : Subgroup.normalizer (Y : Set G) = M := hnorm Y hY1 hY2 hMY
  have hNY1 : Subgroup.normalizer ((CFSG.conjugate Y g : Subgroup G) : Set G) = M := by
    rw [← burnsideIc_ti_conjugate_normalizer, hNY, hMg]
  have hY1' : CFSG.conjugate Y g ≠ ⊥ := burnsideIc_ti_conjugate_ne_bot hY1 g
  have hY2' : IsPGroup 2 (CFSG.conjugate Y g) := hY2.map _
  have hYM : Y ≤ M := hNY ▸ Subgroup.le_normalizer
  have hsup2 : IsPGroup 2 (Y ⊔ CFSG.conjugate Y g : Subgroup G) :=
    hY2.to_sup_of_normal_right' hY2' (hYM.trans hNY1.ge)
  have hsupmem : Y ⊔ CFSG.conjugate Y g ∈
      {Y : Subgroup G | Y ≠ ⊥ ∧ IsPGroup 2 Y ∧ M ≤ Subgroup.normalizer (Y : Set G)} :=
    ⟨ne_bot_of_le_ne_bot hY1 le_sup_left, hsup2, fun m hm =>
      burnsideIc_ti_mem_normalizer_sup (hMY hm) (hNY1.ge hm)⟩
  have hcard := hYmax _ hsupmem
  have heq1 : Y = Y ⊔ CFSG.conjugate Y g := Subgroup.eq_of_le_of_card_ge le_sup_left hcard
  have hY1le : CFSG.conjugate Y g ≤ Y := calc
    CFSG.conjugate Y g ≤ Y ⊔ CFSG.conjugate Y g := le_sup_right
    _ = Y := heq1.symm
  have heq2 : CFSG.conjugate Y g = Y :=
    Subgroup.eq_of_le_of_card_ge hY1le (burnsideIc_ti_card_conjugate _ _).ge
  have hgY : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (burnsideIc_ti_map_conj_eq_iff Y g⁻¹).1 heq2
  rw [hNY] at hgY
  exact hg (by simpa using M.inv_mem hgY)

end BurnsideIc6

theorem as_I_6_1 : I_6_1 := by
  intro G _ _ X hX
  exact ⟨fun h => burnsideIc_ti_of_centralizer_fusion h.1 h.2,
    fun ⟨L, hLC, hL⟩ => burnsideIc_ti_of_unique_twoLocal hX hLC hL⟩

@[expose] def I_6_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (V A : Subgroup G),
    IsElemAbelian 2 V → IsElemAbelian 2 A → CFSG.pRank 2 ↥V = CFSG.pRank 2 ↥A →
    IsTISubgroup V → IsTISubgroup A →
    V ≠ A →
    (∀ g : G, CFSG.conjugate A g ≠ V → CFSG.conjugate A g ⊓ V = ⊥) →
    NIn V A ≠ ⊥ →
      ((NIn V A = V → IsDirectProductOf V A (V ⊔ A)) ∧
        (A ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ → NIn V A = V)) ∧
      (NIn V A < V →
        (IsDirectProductOf (NIn V A) (NIn A V) (pairY V A) ∧ IsNormalIn (pairY V A) (V ⊔ A) ∧
          ∀ v ∈ V, v ∉ NIn V A →
            NIn V A = pairY V A ⊓ Subgroup.centralizer ({v} : Set G) ∧
            NIn V A = ⁅pairY V A, Subgroup.zpowers v⁆) ∧
        ∀ [((pairY V A).subgroupOf (V ⊔ A)).Normal],
          (QuotientIsDihedralL2OrSz (V ⊔ A) (pairY V A) ∧ ImageRankEqRank V (V ⊔ A) (pairY V A)) ∧
          ((∀ P Q : Subgroup G, IsChiefSection (V ⊔ A) (pairY V A) P Q →
              IsNaturalSection (V ⊔ A) (pairY V A) P Q) ∧
            (QuotientIsL2OrDihedral (V ⊔ A) (pairY V A) →
              IsCompletelyReducibleUnder (V ⊔ A) (pairY V A))))

section BurnsideI62

section BurnsideI62

variable {G : Type} [Group G]

open CFSG.ASVolI.ChIJK in
private theorem burnsideI62_isTISetIn {V : Subgroup G} (h : IsTISubgroup V) :
    CFSG.Quasithin.IsTISetIn V ⊤ :=
  ⟨le_top, fun g _ hg => h g hg⟩

private theorem burnsideI62_card_eq_two_pow [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Nat.card V = 2 ^ CFSG.pRank 2 ↥V := by
  have : CFSG.IsElementaryAbelian 2 V := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hV
  obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 V).exists_card_eq
  rw [CFSG.pRank_eq_of_card_eq_pow one_lt_two hk]
  exact hk

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_base {V A : Subgroup G} (hVe : IsElemAbelian 2 V) (hAe :
    IsElemAbelian 2 A)
    (hTIV : IsTISubgroup V) (hTIA : IsTISubgroup A) (hne : V ≠ A)
    (hcross : ∀ g : G, CFSG.conjugate A g ≠ V → CFSG.conjugate A g ⊓ V = ⊥) :
    CFSG.Quasithin.I62.Base V A := by
  refine ⟨hVe, hAe, burnsideI62_isTISetIn hTIV, burnsideI62_isTISetIn hTIA, ?_⟩
  have h1 := hcross 1
  have : CFSG.conjugate A 1 = A := by
    ext x
    simp [CFSG.conjugate, Subgroup.mem_map, MulAut.conj_apply]
  rw [this] at h1
  rw [inf_comm]
  exact h1 hne.symm

private theorem burnsideI62_card_lt_of_not_mem [Finite G] {H K : Subgroup G} (hHK : H ≤ K) {x : G}
    (hxK : x ∈ K) (hxH : x ∉ H) : Nat.card H < Nat.card K := by
  by_contra hge
  push Not at hge
  exact hxH ((Subgroup.eq_of_le_of_card_ge hHK hge) ▸ hxK)

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_part1 [Finite G] {V A : Subgroup G} (h : Base V A)
    (hcard : Nat.card V = Nat.card A) :
    (NIn V A = V → IsDirectProductOf V A (V ⊔ A)) ∧
      (A ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ → NIn V A = V) := by
  constructor
  · intro hU
    have hU' : V ⊓ Subgroup.normalizer (A : Set G) = V := hU
    have hAN : ∀ a ∈ A, a ∈ Subgroup.normalizer (V : Set G) := by
      intro a ha
      by_contra haV
      have hle : Nat.card ↥(V ⊓ Subgroup.normalizer (A : Set G)) ≤
          Nat.card ↥(A ⊓ Subgroup.normalizer (V : Set G)) :=
        h.symm.card_tiB_le (v := a) ha (fun hmem => haV hmem.2)
      rw [hU'] at hle
      have hlt : Nat.card ↥(A ⊓ Subgroup.normalizer (V : Set G)) < Nat.card A :=
        burnsideI62_card_lt_of_not_mem inf_le_left ha (fun hm => haV hm.2)
      omega
    refine ⟨fun v hv a ha => ?_, h.inf, rfl⟩
    have hvA : v ∈ Subgroup.normalizer (A : Set G) := by
      have : v ∈ V ⊓ Subgroup.normalizer (A : Set G) := by rw [hU']; exact hv
      exact this.2
    have h1 : v * a * v⁻¹ * a⁻¹ ∈ A :=
      A.mul_mem ((Subgroup.mem_normalizer_iff.mp hvA a).mp ha) (A.inv_mem ha)
    have h2 : v * a * v⁻¹ * a⁻¹ ∈ V := by
      rw [show v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) by group]
      exact V.mul_mem hv ((Subgroup.mem_normalizer_iff.mp (hAN a ha) v⁻¹).mp (V.inv_mem hv))
    have h3 : v * a * v⁻¹ * a⁻¹ ∈ V ⊓ A := ⟨h2, h1⟩
    rw [h.inf, Subgroup.mem_bot] at h3
    calc v * a = (v * a * v⁻¹ * a⁻¹) * (a * v) := by group
      _ = a * v := by rw [h3, one_mul]
  · intro hb
    obtain ⟨⟨b, hbmem⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
    have hb1' : b ≠ 1 := fun e => hb1 (Subtype.ext e)
    have hbA : b ∈ A := hbmem.1
    have hbC : b ∈ Subgroup.centralizer (V : Set G) := hbmem.2
    have hbN : b ∈ A ⊓ Subgroup.normalizer (V : Set G) :=
      ⟨hbA, Subgroup.centralizer_le_normalizer _ hbC⟩
    have h1 := h.inf_centralizer_eq' (b := b) hbN hb1'
    show V ⊓ Subgroup.normalizer (A : Set G) = V
    refine le_antisymm inf_le_left (fun v hv => ?_)
    have : v ∈ V ⊓ Subgroup.centralizer ({b} : Set G) :=
      ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hbC v hv)⟩
    rw [h1] at this
    exact this

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_hyp [Finite G] {V A : Subgroup G} (h : Base V A)
    (hcard : Nat.card V = Nat.card A)
    (hcross : ∀ g : G, CFSG.conjugate A g ≠ V → CFSG.conjugate A g ⊓ V = ⊥)
    (hU : NIn V A ≠ ⊥) (hlt : NIn V A < V) : Hyp V A :=
  Hyp.mk' h.hV h.hA hcard h.tiV h.tiA (fun g hg => hcross g (fun e => hg e.symm)) hU hlt

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_pairY_le (V A : Subgroup G) : pairY V A ≤ V ⊔ A :=
  sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_part2a [Finite G] {V A : Subgroup G} (h : Hyp V A) :
    IsDirectProductOf (NIn V A) (NIn A V) (pairY V A) ∧ IsNormalIn (pairY V A) (V ⊔ A) ∧
      ∀ v ∈ V, v ∉ NIn V A →
        NIn V A = pairY V A ⊓ Subgroup.centralizer ({v} : Set G) ∧
          NIn V A = ⁅pairY V A, Subgroup.zpowers v⁆ := by
  have hb := h.toBase
  refine ⟨⟨fun u hu b hb' => hb.comm_tiU_tiB hu hb', hb.tiU_inf_tiB, rfl⟩,
    ⟨burnsideI62_pairY_le V A, ?_⟩, fun v hv hvU => ⟨(hb.inf_centralizer_tiY hv hvU).symm,
      h.tiU_eq_commutator hv hvU⟩⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (burnsideI62_pairY_le V A)).mpr
    hb.tiX_le_normalizer_tiY

private theorem burnsideI62_t75conj (g : G) (T : Subgroup G) :
    CFSG.CGT.Timmesfeld75.conjSubgroup g T = CFSG.Quasithin.conjSubgroup T g⁻¹ := by
  simp [CFSG.Quasithin.conjSubgroup, CFSG.CGT.Timmesfeld75.conjSubgroup]

open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_prop24 [Finite G] {V A : Subgroup G} (h : Hyp V A) :
    Prop24Setup V A (tiU V A) (tiB V A) (tiY V A) := by
  refine ⟨h.hV, ?_, ?_, rfl, rfl, rfl, h.ne, h.lt.ne⟩
  · intro g
    by_cases hg : g ∈ Subgroup.normalizer (V : Set G)
    · right
      have h1 : CFSG.CGT.Timmesfeld75.conjSubgroup g V = V :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
      rw [h1, inf_idem]
    · left
      have hg' : g⁻¹ ∉ Subgroup.normalizer (V : Set G) := by
        intro hm
        apply hg
        have := (Subgroup.normalizer (V : Set G)).inv_mem hm
        rwa [inv_inv] at this
      have h2 := h.tiV.2 g⁻¹ trivial hg'
      rw [burnsideI62_t75conj]
      exact h2
  · obtain ⟨x, -, hx⟩ := h.exists_conjSubgroup_eq
    refine ⟨x⁻¹, ?_⟩
    rw [burnsideI62_t75conj, inv_inv, ← hx, conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]

open scoped MatrixGroups in
private theorem burnsideI62_pRank_psl {K : Type} [Group K] [Finite K] {f : ℕ} (hf : 2 ≤ f)
    (e : K ≃* PSL(2, GaloisField 2 f)) : CFSG.pRank 2 K = f := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.GH74.SmallRanks.twoRank_eq_of_statedClassicalModel_PSL_two_two
    (CFSG.Quasithin.I62.isPSL_two_two_of_mulEquiv hf e)

private theorem burnsideI62_twoRank_dihedral {m : ℕ} [NeZero m] (hm : Odd m) :
    CFSG.Open.twoRank (DihedralGroup m) = 1 := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨Subgroup.zpowers (DihedralGroup.sr 0), le_top, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩,
    ?_⟩
  · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h2 : (DihedralGroup.sr (0 : ZMod m)) ^ 2 = 1 := by
      rw [sq]; exact DihedralGroup.sr_mul_self 0
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h2, one_zpow]
  · rw [Nat.card_zpowers, DihedralGroup.orderOf_sr, pow_one]
  · rintro k ⟨E, -, -, hEcard⟩
    have hdvd : 2 ^ k ∣ 2 * m := by
      rw [← hEcard, ← DihedralGroup.nat_card]
      exact Subgroup.card_subgroup_dvd_card E
    by_contra hk
    push Not at hk
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk
    have : 4 ∣ 2 * m := (by simpa using h4 : 4 ∣ 2 ^ k).trans hdvd
    have h2 : 2 ∣ m := by omega
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

open CFSG.ASVolI.ChIJK in
open scoped MatrixGroups in
@[expose] def burnsideI62_Models (V A : Subgroup G) [((pairY V A).subgroupOf (V ⊔ A)).Normal] : Prop :=
  (∃ f : ℕ, 2 ≤ f ∧ (NIn V A).relIndex V = 2 ^ f ∧
      Nonempty (↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* PSL(2, GaloisField 2 f))) ∨
    (∃ a : ℕ, 1 ≤ a ∧ (NIn V A).relIndex V = 2 ^ (2 * a + 1) ∧
      Nonempty (↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* Sz a)) ∨
    (∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ (NIn V A).relIndex V = 2 ∧
      Nonempty (↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* DihedralGroup m))

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 CFSG.CGT.T75N in
private theorem burnsideI62_models [Finite G]
    {V A : Subgroup G} (h : Hyp V A) :
    ∃ _ : ((pairY V A).subgroupOf (V ⊔ A)).Normal, burnsideI62_Models V A := by
  obtain ⟨hN, -, hmod⟩ := (burnsideI62_prop24 h).tim77_2_4_one benderCenterInput
    unitaryTwoGenerationInput
  exact ⟨hN, hmod⟩

@[expose] def burnsideI62_SzRank : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (a : ℕ), 1 ≤ a → Nonempty (K ≃* Sz a) →
    CFSG.pRank 2 K = 2 * a + 1

private theorem burnsideI62_szRank : burnsideI62_SzRank := by
  intro K _ _ a ha ⟨e⟩
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_eq_of_mulEquiv hK
    (e.trans (CFSG.QuasithinUnique.szEquivSuzukiGroup a))

open CFSG.ASVolI.ChIJK in
open CFSG.RankThree.GF2n.Tim77 CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_pRank_image [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] {k : ℕ}
    (hk : (NIn V A).relIndex V = 2 ^ k) :
    CFSG.pRank 2 ↥((V.subgroupOf (V ⊔ A)).map
      (QuotientGroup.mk' ((pairY V A).subgroupOf (V ⊔ A)))) = k := by
  have S := burnsideI62_prop24 h
  haveI : ((tiY V A).subgroupOf (V ⊔ A)).Normal := hN
  have hcard := S.relIndex_eq_card_image
  have hel : IsElemAbelian 2 ((V.subgroupOf (V ⊔ A)).map
      (QuotientGroup.mk' ((pairY V A).subgroupOf (V ⊔ A)))) :=
    isElemAbelian_map' (isElemAbelian_subgroupOf h.hV _) _
  haveI := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hel
  refine CFSG.pRank_eq_of_card_eq_pow one_lt_two ?_
  exact hcard.symm.trans hk

open CFSG.ASVolI.ChIJK in
open scoped MatrixGroups in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_part2b [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] (hSz : burnsideI62_SzRank)
    (hM : burnsideI62_Models V A) :
    QuotientIsDihedralL2OrSz (V ⊔ A) (pairY V A) ∧ ImageRankEqRank V (V ⊔ A) (pairY V A) := by
  rcases hM with ⟨f, hf, hrel, ⟨e⟩⟩ | ⟨a, ha, hrel, ⟨e⟩⟩ | ⟨m, hm, h3, hrel, ⟨e⟩⟩
  · refine ⟨Or.inr (Or.inl ⟨f, by omega, ⟨e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo⟩⟩), ?_⟩
    have := Finite.of_equiv _ e.symm.toEquiv
    show CFSG.pRank 2 _ = CFSG.pRank 2 _
    rw [burnsideI62_pRank_image h hrel, burnsideI62_pRank_psl hf e]
  · refine ⟨Or.inr (Or.inr ⟨a, ha, ⟨e⟩⟩), ?_⟩
    have := Finite.of_equiv _ e.symm.toEquiv
    show CFSG.pRank 2 _ = CFSG.pRank 2 _
    rw [burnsideI62_pRank_image h hrel, hSz _ a ha ⟨e⟩]
  · refine ⟨Or.inl ⟨m, hm, ⟨e⟩⟩, ?_⟩
    haveI : NeZero m := ⟨hm.pos.ne'⟩
    have := Finite.of_equiv _ e.symm.toEquiv
    show CFSG.pRank 2 _ = CFSG.pRank 2 _
    rw [burnsideI62_pRank_image h (k := 1) (by simpa using hrel),
      CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact ((CFSG.GH74.twoRank_eq_of_mulEquiv e).trans (burnsideI62_twoRank_dihedral hm)).symm

private theorem burnsideI62_le_normalizer_finset_sup {X : Subgroup G} (t : Finset (Subgroup G))
    (ht : ∀ W ∈ t, X ≤ Subgroup.normalizer (W : Set G)) :
    X ≤ Subgroup.normalizer ((t.sup id : Subgroup G) : Set G) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have h : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    intro x _
    rw [Finset.sup_empty, h]
    exact Subgroup.mem_top x
  | insert W t hWt ih =>
    rw [Finset.sup_insert]
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨ht W (Finset.mem_insert_self _ _) hx, ih (fun W' hW' => ht W' (Finset.mem_insert_of_mem hW')) hx⟩

open scoped IsMulCommutative in
private theorem burnsideI62_exists_compl [Finite G] {X Y : Subgroup G}
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) {s : Finset (Subgroup G)} (hsup : s.sup id = Y)
    (hW : ∀ W ∈ s, W ≤ Y ∧ X ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
      ∀ U : Subgroup G, U ≤ W → X ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = W)
    {B : Subgroup G} (hBY : B ≤ Y) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    ∃ C : Subgroup G, X ≤ Subgroup.normalizer (C : Set G) ∧ C ≤ Y ∧ B ⊓ C = ⊥ ∧ B ⊔ C = Y := by
  classical
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image
    (s.powerset.filter fun t => B ⊓ t.sup id = ⊥) Finset.card
    ⟨∅, by simp⟩
  obtain ⟨hts, htB⟩ := Finset.mem_filter.mp ht
  have hts' : t ⊆ s := Finset.mem_powerset.mp hts
  set C : Subgroup G := t.sup id with hC
  have hCY : C ≤ Y := by
    rw [hC]
    exact Finset.sup_le fun W hWt => (hW W (hts' hWt)).1
  have hCX : X ≤ Subgroup.normalizer (C : Set G) :=
    burnsideI62_le_normalizer_finset_sup t fun W hWt => (hW W (hts' hWt)).2.1
  refine ⟨C, hCX, hCY, htB, le_antisymm (sup_le hBY hCY) ?_⟩
  rw [← hsup]
  refine Finset.sup_le fun W hWs => ?_
  by_contra hWle
  have hWt : W ∉ t := fun hWt => hWle ((Finset.le_sup (f := id) hWt).trans le_sup_right)
  obtain ⟨hWY, hWX, hW0, hWirr⟩ := hW W hWs
  have hBCX : X ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hB hx, hCX hx⟩
  have hD : W ⊓ (B ⊔ C) = ⊥ := by
    have hDX : X ≤ Subgroup.normalizer ((W ⊓ (B ⊔ C) : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hWX hx, hBCX hx⟩
    rcases hWirr _ inf_le_left hDX with h | h
    · exact h
    · exact absurd (inf_eq_left.mp h) hWle
  have hWCcomm : ∀ x ∈ W, ∀ y ∈ C, x * y = y * x := fun x hx y hy => hYc x (hWY hx) y (hCY hy)
  have hindep : B ⊓ (insert W t).sup id = ⊥ := by
    rw [Finset.sup_insert, id, eq_bot_iff]
    rintro b ⟨hbB, hbWC⟩
    obtain ⟨w, hw, c, hc, rfl⟩ := CFSG.RankThree.GF2n.exists_mul_of_mem_sup
      (CFSG.RankThree.GF2n.le_normalizer_of_comm (fun x hx y hy => (hWCcomm y hy x hx).symm))
      hbWC
    have hwBC : w ∈ B ⊔ C := by
      have : w = (w * c) * c⁻¹ := by group
      rw [this]
      exact (B ⊔ C).mul_mem (Subgroup.mem_sup_left hbB) ((B ⊔ C).inv_mem (Subgroup.mem_sup_right hc))
    have hw1 : w = 1 := by
      have : w ∈ W ⊓ (B ⊔ C) := ⟨hw, hwBC⟩
      rw [hD, Subgroup.mem_bot] at this
      exact this
    subst hw1
    rw [one_mul] at hbB ⊢
    have : c ∈ B ⊓ C := ⟨hbB, hc⟩
    rw [htB] at this
    exact this
  have hmem : insert W t ∈ s.powerset.filter fun t => B ⊓ t.sup id = ⊥ :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hWs hts'), hindep⟩
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hWt] at this
  omega

open scoped MatrixGroups in
private theorem burnsideI62_card_sl2_two : Nat.card SL(2, GaloisField 2 1) = 6 := by
  letI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]
    simpa using GaloisField.card 2 1 (by norm_num)
  rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
  norm_num

open CFSG.ASVolI.ChIJK in
open CFSG.RankThree.GF2n.Tim77 CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_relIndex_eq_two [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] {m : ℕ} (hm : Odd m)
    (hcard : Nat.card (↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A)) = 2 * m) :
    (NIn V A).relIndex V = 2 := by
  have S := burnsideI62_prop24 h
  haveI : ((tiY V A).subgroupOf (V ⊔ A)).Normal := hN
  have hrel := S.relIndex_eq_card_image
  have hel : IsElemAbelian 2 ((V.subgroupOf (V ⊔ A)).map
      (QuotientGroup.mk' ((pairY V A).subgroupOf (V ⊔ A)))) :=
    isElemAbelian_map' (isElemAbelian_subgroupOf h.hV _) _
  haveI := CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hel
  obtain ⟨k, hk⟩ := (CFSG.IsElementaryAbelian.isPGroup 2 ↥((V.subgroupOf (V ⊔ A)).map
    (QuotientGroup.mk' ((pairY V A).subgroupOf (V ⊔ A))))).exists_card_eq
  have hrel' : (NIn V A).relIndex V = 2 ^ k := hrel.trans hk
  have hdvd : 2 ^ k ∣ 2 * m := by
    rw [← hk, ← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hk1 : k ≤ 1 := by
    by_contra hk2
    push Not at hk2
    have h4 : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
    have : 4 ∣ 2 * m := (by simpa using h4 : 4 ∣ 2 ^ k).trans hdvd
    have h2 : 2 ∣ m := by omega
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)
  have hne : (NIn V A).relIndex V ≠ 1 := by
    intro h1
    have := (Subgroup.relIndex_eq_one.mp h1)
    exact h.lt.ne (le_antisymm inf_le_left this)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hrel')
  have : k = 1 := by omega
  subst this
  simpa using hrel'

open CFSG.ASVolI.ChIJK in
open scoped MatrixGroups in
open CFSG.RankThree.GF2n.Tim77 CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_part2c2 [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] :
    QuotientIsL2OrDihedral (V ⊔ A) (pairY V A) →
      IsCompletelyReducibleUnder (V ⊔ A) (pairY V A) := by
  intro hQ
  have S := burnsideI62_prop24 h
  haveI : ((tiY V A).subgroupOf (V ⊔ A)).Normal := hN
  have hYc : ∀ a ∈ pairY V A, ∀ b ∈ pairY V A, a * b = b * a := fun a ha b hb => S.comm_M ha hb
  have hdec : ∃ s : Finset (Subgroup G), s.sup id = pairY V A ∧
      ∀ W ∈ s, W ≤ pairY V A ∧ V ⊔ A ≤ Subgroup.normalizer (W : Set G) ∧ W ≠ ⊥ ∧
        ∀ U : Subgroup G, U ≤ W → V ⊔ A ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = W := by
    by_cases hrel : (NIn V A).relIndex V = 2
    · obtain ⟨s, -, hsup, hW⟩ := S.tim77_2_4_two_dihedral hrel
      exact ⟨s, hsup, hW⟩
    · rcases hQ with ⟨n, hn, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩
      · by_cases hn1 : n = 1
        · subst hn1
          exfalso
          apply hrel
          refine burnsideI62_relIndex_eq_two h (m := 3) (by decide) ?_
          rw [Nat.card_congr e.toEquiv, burnsideI62_card_sl2_two]
        · obtain ⟨F, _, _, _, ψ, _, _, _, s, _, hsup, hW⟩ :=
            S.tim77_2_4_two_psl (by omega : 2 ≤ n)
              (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo.symm)
          exact ⟨s, hsup, fun W hW' => ⟨(hW W hW').1, (hW W hW').2.1, (hW W hW').2.2.1,
            (hW W hW').2.2.2.1⟩⟩
      · exfalso
        apply hrel
        haveI : NeZero m := ⟨hm.pos.ne'⟩
        refine burnsideI62_relIndex_eq_two h hm ?_
        rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨s, hsup, hW⟩ := hdec
  intro B hB hBY
  exact burnsideI62_exists_compl hYc hsup hW hBY hB

private theorem burnsideI62_norm_section {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    (T : AddMonoid.End M) {k : ℕ} (hk : Odd k) (hTk : T ^ k = 1) (Q : AddSubgroup M)
    (hQ : ∀ q ∈ Q, T q ∈ Q) {c : M} (hc : T c - c ∈ Q) : ∃ y : M, T y = y ∧ y - c ∈ Q := by
  classical
  have emul : ∀ (F G : AddMonoid.End M) (x : M), (F * G) x = F (G x) := fun _ _ _ => rfl
  have ha : ∀ i : ℕ, (T ^ i) c - c ∈ Q := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have : (T ^ (i + 1)) c - c = T ((T ^ i) c - c) + (T c - c) := by
        rw [pow_succ', emul, map_sub]
        abel
      rw [this]
      exact Q.add_mem (hQ _ ih) hc
  set N : AddMonoid.End M := ∑ i ∈ Finset.range k, T ^ i with hN
  have hTN : T * N = N := by
    rw [hN, Finset.mul_sum]
    have h1 : ∑ i ∈ Finset.range k, T * T ^ i = ∑ i ∈ Finset.range k, T ^ (i + 1) :=
      Finset.sum_congr rfl fun i _ => (pow_succ' T i).symm
    rw [h1]
    have h2 := Finset.sum_range_succ' (fun i => T ^ i) k
    have h3 := Finset.sum_range_succ (fun i => T ^ i) k
    rw [hTk] at h3
    simp only [pow_zero] at h2
    have h4 : ∑ i ∈ Finset.range k, T ^ (i + 1) + 1 = ∑ i ∈ Finset.range k, T ^ i + 1 := by
      rw [← h2, h3]
    exact add_right_cancel h4
  have hNc : T (N c) = N c := by
    have := congrArg (fun F : AddMonoid.End M => F c) hTN
    simpa [emul] using this
  have hNapp : N c = ∑ i ∈ Finset.range k, (T ^ i) c := by
    rw [hN]
    exact AddMonoidHom.finset_sum_apply (fun i => (T ^ i : M →+ M)) (Finset.range k) c
  have hsum : N c - k • c ∈ Q := by
    have : N c - k • c = ∑ i ∈ Finset.range k, ((T ^ i) c - c) := by
      rw [Finset.sum_sub_distrib, hNapp]
      simp
    rw [this]
    exact Q.sum_mem fun i _ => ha i
  have h2c : 2 • c = 0 := by rw [two_nsmul]; exact h2 c
  have key : ∀ j : ℕ, (2 * j + 1) • c = c := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, add_nsmul, ih, h2c, add_zero]
  have hkc : k • c = c := by
    obtain ⟨j, hj⟩ := hk
    rw [hj]
    exact key j
  rw [hkc] at hsum
  exact ⟨N c, hNc, hsum⟩

open scoped IsMulCommutative in
private theorem burnsideI62_fixed_section_grp {Y Q : Subgroup G} [IsMulCommutative ↥Y]
    (hY2 : ∀ y ∈ Y, y * y = 1) {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) {k : ℕ}
    (hk : Odd k) (hgk : ∀ y ∈ Y, g ^ k * y * (g ^ k)⁻¹ = y)
    (hQg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {c : G} (hcY : c ∈ Y)
    (hc : g * c * g⁻¹ * c⁻¹ ∈ Q) : ∃ y ∈ Y, g * y * g⁻¹ = y ∧ y * c⁻¹ ∈ Q := by
  let T : AddMonoid.End (Additive ↥Y) :=
    MonoidHom.toAdditive (CFSG.RankThree.GF2n.conjHom Y g hg)
  have hT : ∀ y : ↥Y, (((T (Additive.ofMul y)).toMul : ↥Y) : G) = g * y * g⁻¹ := fun y => rfl
  have hTi : ∀ (i : ℕ) (y : ↥Y),
      (((T ^ i) (Additive.ofMul y)).toMul : G) = g ^ i * (y : G) * (g ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih =>
      intro y
      obtain ⟨y', hy'⟩ := Additive.ofMul.surjective ((T ^ i) (Additive.ofMul y))
      have h1 : (T ^ (i + 1)) (Additive.ofMul y) = T (Additive.ofMul y') := by
        rw [pow_succ', hy']
        rfl
      have h2 : (y' : G) = g ^ i * (y : G) * (g ^ i)⁻¹ := by
        have := ih y
        rwa [← hy', toMul_ofMul] at this
      rw [h1, hT, h2, pow_succ']
      group
  let Q' : AddSubgroup (Additive ↥Y) :=
    { carrier := {v | ((v.toMul : ↥Y) : G) ∈ Q}
      add_mem' := fun {a b} ha hb => Q.mul_mem ha hb
      zero_mem' := Q.one_mem
      neg_mem' := fun {a} ha => Q.inv_mem ha }
  have h2 : ∀ x : Additive ↥Y, x + x = 0 := fun x =>
    Additive.toMul.injective (Subtype.ext (hY2 _ x.toMul.2))
  have hTk : T ^ k = 1 := by
    refine DFunLike.ext _ _ fun v => ?_
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective v
    refine Additive.toMul.injective (Subtype.ext ?_)
    rw [hTi]
    exact hgk y y.2
  have hQ' : ∀ q ∈ Q', T q ∈ Q' := by
    intro q hq
    obtain ⟨y, rfl⟩ := Additive.ofMul.surjective q
    change (((T (Additive.ofMul y)).toMul : ↥Y) : G) ∈ Q
    rw [hT]
    exact hQg _ hq
  obtain ⟨v, hv, hvc⟩ := burnsideI62_norm_section h2 T hk hTk Q' hQ'
    (c := Additive.ofMul ⟨c, hcY⟩)
    (by
      change (((T (Additive.ofMul (⟨c, hcY⟩ : ↥Y)) - Additive.ofMul (⟨c, hcY⟩ : ↥Y)).toMul : ↥Y) :
        G) ∈ Q
      rw [toMul_sub, Subgroup.coe_div, hT, div_eq_mul_inv]
      exact hc)
  obtain ⟨y, rfl⟩ := Additive.ofMul.surjective v
  refine ⟨y, y.2, ?_, ?_⟩
  · have h1 := congrArg (fun w : Additive ↥Y => ((w.toMul : ↥Y) : G)) hv
    simp only [hT] at h1
    exact h1
  · change (((Additive.ofMul y - Additive.ofMul (⟨c, hcY⟩ : ↥Y)).toMul : ↥Y) : G) ∈ Q at hvc
    rw [toMul_sub, Subgroup.coe_div, div_eq_mul_inv] at hvc
    exact hvc

open scoped IsMulCommutative in
private theorem burnsideI62_fpf_section_grp {Y Q : Subgroup G} [IsMulCommutative ↥Y]
    (hY2 : ∀ y ∈ Y, y * y = 1) {g : G} (hg : g ∈ Subgroup.normalizer (Y : Set G)) {k : ℕ}
    (hk : Odd k) (hgk : ∀ y ∈ Y, g ^ k * y * (g ^ k)⁻¹ = y)
    (hfix : ∀ y ∈ Y, g * y * g⁻¹ = y → y = 1)
    (hQg : ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) {c : G} (hcY : c ∈ Y)
    (hc : g * c * g⁻¹ * c⁻¹ ∈ Q) : c ∈ Q := by
  obtain ⟨y, hyY, hy, hyc⟩ := burnsideI62_fixed_section_grp hY2 hg hk hgk hQg hcY hc
  rw [hfix y hyY hy, one_mul] at hyc
  simpa using Q.inv_mem hyc

section SecModule

open scoped IsMulCommutative

variable {X P Q : Subgroup G}

@[expose] noncomputable def burnsideI62_secAct [IsMulCommutative ↥P]
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (x : ↥X) : Additive (↥P ⧸ Q.subgroupOf P) →+ Additive (↥P ⧸ Q.subgroupOf P) :=
  MonoidHom.toAdditive (QuotientGroup.map (Q.subgroupOf P) (Q.subgroupOf P)
    (CFSG.RankThree.GF2n.conjHom P x (hXP x.2)) (by
      intro p hp
      show CFSG.RankThree.GF2n.conjHom P (x : G) (hXP x.2) p ∈ Q.subgroupOf P
      rw [Subgroup.mem_subgroupOf, CFSG.RankThree.GF2n.coe_conjHom_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hXQ x.2) p).mp (Subgroup.mem_subgroupOf.mp hp)))

private theorem burnsideI62_secAct_ofMul_mk [IsMulCommutative ↥P]
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (x : ↥X) (p : ↥P) :
    burnsideI62_secAct hXP hXQ x (Additive.ofMul (QuotientGroup.mk p)) =
      Additive.ofMul (QuotientGroup.mk (CFSG.RankThree.GF2n.conjHom P x (hXP x.2) p)) := rfl

private theorem burnsideI62_secAct_mk [IsMulCommutative ↥P]
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (x : ↥X) (p q : ↥P) (hpq : (q : G) = (x : G) * p * (x : G)⁻¹) :
    burnsideI62_secAct hXP hXQ x (Additive.ofMul (QuotientGroup.mk p)) =
      Additive.ofMul (QuotientGroup.mk q) := by
  rw [burnsideI62_secAct_ofMul_mk]
  congr 2
  exact Subtype.ext (by rw [CFSG.RankThree.GF2n.coe_conjHom_apply, hpq])

theorem burnsideI62_secAct_one [IsMulCommutative ↥P]
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (v : Additive (↥P ⧸ Q.subgroupOf P)) : burnsideI62_secAct hXP hXQ 1 v = v := by
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective v
  induction c using QuotientGroup.induction_on with
  | H p =>
    rw [burnsideI62_secAct_mk hXP hXQ 1 p p (by simp)]

theorem burnsideI62_secAct_mul [IsMulCommutative ↥P]
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (x y : ↥X) (v : Additive (↥P ⧸ Q.subgroupOf P)) :
    burnsideI62_secAct hXP hXQ (x * y) v =
      burnsideI62_secAct hXP hXQ x (burnsideI62_secAct hXP hXQ y v) := by
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective v
  induction c using QuotientGroup.induction_on with
  | H p =>
    have hy : burnsideI62_secAct hXP hXQ y (Additive.ofMul (QuotientGroup.mk p)) =
        Additive.ofMul (QuotientGroup.mk (CFSG.RankThree.GF2n.conjHom P y (hXP y.2) p)) :=
      burnsideI62_secAct_ofMul_mk hXP hXQ y p
    rw [hy, burnsideI62_secAct_ofMul_mk hXP hXQ x, burnsideI62_secAct_ofMul_mk]
    congr 2
    apply Subtype.ext
    simp only [CFSG.RankThree.GF2n.coe_conjHom_apply, Subgroup.coe_mul, mul_inv_rev]
    group

@[expose, instance_reducible] def burnsideI62_secModule [IsMulCommutative ↥P] (hP2 : ∀ p ∈ P, p * p = 1) :
    Module (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)) :=
  AddCommGroup.zmodModule fun v => by
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective v
    induction c using QuotientGroup.induction_on with
    | H p =>
      rw [two_nsmul]
      apply Additive.toMul.injective
      show (QuotientGroup.mk p : ↥P ⧸ Q.subgroupOf P) * (QuotientGroup.mk p) = 1
      rw [← QuotientGroup.mk_mul]
      have : p * p = 1 := Subtype.ext (hP2 p p.2)
      rw [this]
      rfl

variable [IsMulCommutative ↥P] [Module (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P))]

@[expose] noncomputable def burnsideI62_secRep (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    ↥X →* Module.End (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)) where
  toFun x := (burnsideI62_secAct hXP hXQ x).toZModLinearMap 2
  map_one' := LinearMap.ext fun v => burnsideI62_secAct_one hXP hXQ v
  map_mul' x y := LinearMap.ext fun v => burnsideI62_secAct_mul hXP hXQ x y v

private theorem burnsideI62_secRep_apply (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (x : ↥X) (v : Additive (↥P ⧸ Q.subgroupOf P)) :
    burnsideI62_secRep hXP hXQ x v = burnsideI62_secAct hXP hXQ x v := rfl

theorem burnsideI62_secRep_ker {Y : Subgroup G} (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hY : ∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ = p)
    (x : ↥X) (hx : x ∈ Y.subgroupOf X) : burnsideI62_secRep hXP hXQ x = 1 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective v
  induction c using QuotientGroup.induction_on with
  | H p =>
    show burnsideI62_secAct hXP hXQ x _ = _
    rw [burnsideI62_secAct_mk hXP hXQ x p p (hY x (Subgroup.mem_subgroupOf.mp hx) p p.2).symm]
    rfl

open CFSG.ASVolI.ChIJK in
private theorem burnsideI62_conjModuleIso (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) {M : Type} [AddCommGroup M]
    (act : ↥X → M → M) (θ : M ≃+ Additive (↥P ⧸ Q.subgroupOf P))
    (hθ : ∀ (x : ↥X) (v : M), θ (act x v) = burnsideI62_secAct hXP hXQ x (θ v)) :
    IsConjModuleIso X P Q M act := by
  refine ⟨hXP, hXQ, ?_⟩
  let φ : ↥P →* Multiplicative M :=
    { toFun := fun p => Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk p)))
      map_one' := by
        show Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk 1))) = 1
        have : (Additive.ofMul (QuotientGroup.mk (1 : ↥P) : ↥P ⧸ Q.subgroupOf P)) = 0 := rfl
        rw [this, map_zero]
        rfl
      map_mul' := fun p q => by
        show Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk (p * q)))) =
          Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk p))) *
            Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk q)))
        have : (Additive.ofMul (QuotientGroup.mk (p * q) : ↥P ⧸ Q.subgroupOf P)) =
            Additive.ofMul (QuotientGroup.mk p) + Additive.ofMul (QuotientGroup.mk q) := rfl
        rw [this, map_add]
        rfl }
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro m
    obtain ⟨c, hc⟩ := Additive.ofMul.surjective (θ (Multiplicative.toAdd m))
    induction c using QuotientGroup.induction_on with
    | H p =>
      refine ⟨p, ?_⟩
      show Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk p))) = m
      rw [hc, AddEquiv.symm_apply_apply]
      rfl
  · ext p
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk p))) = 1 ↔ p ∈ Q.subgroupOf P
    rw [← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      have h0 : θ.symm (Additive.ofMul (QuotientGroup.mk p)) = 0 := h
      have := (θ.symm.map_eq_zero_iff).mp h0
      exact Additive.toMul.injective this
    · intro h
      have : (Additive.ofMul (QuotientGroup.mk p : ↥P ⧸ Q.subgroupOf P)) = 0 := by
        rw [h]; rfl
      rw [this, map_zero]
      rfl
  · intro x p q hpq
    show Multiplicative.ofAdd (θ.symm (Additive.ofMul (QuotientGroup.mk q))) =
      Multiplicative.ofAdd (act x (θ.symm (Additive.ofMul (QuotientGroup.mk p))))
    have h1 := hθ x (θ.symm (Additive.ofMul (QuotientGroup.mk p)))
    rw [AddEquiv.apply_symm_apply, burnsideI62_secAct_mk hXP hXQ x p q hpq] at h1
    rw [← h1, AddEquiv.symm_apply_apply]

private theorem burnsideI62_le_normalizer_of_conj_mem {B : Subgroup G}
    (hB : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B) : X ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨hB x hx y, fun hy => ?_⟩
  have := hB x⁻¹ (X.inv_mem hx) _ hy
  simpa [mul_assoc] using this

private theorem burnsideI62_sec_irred (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hQP : Q ≤ P)
    (hchief : ∀ B : Subgroup G, X ≤ Subgroup.normalizer (B : Set G) → Q ≤ B → B ≤ P →
      B = Q ∨ B = P)
    (W : Submodule (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)))
    (hW : ∀ (x : ↥X), ∀ w ∈ W, burnsideI62_secRep hXP hXQ x w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let Bp : Subgroup ↥P :=
    { carrier := {p | Additive.ofMul (QuotientGroup.mk p : ↥P ⧸ Q.subgroupOf P) ∈ W}
      mul_mem' := fun {a b} ha hb => by
        have : (Additive.ofMul (QuotientGroup.mk (a * b) : ↥P ⧸ Q.subgroupOf P)) =
            Additive.ofMul (QuotientGroup.mk a) + Additive.ofMul (QuotientGroup.mk b) := rfl
        show Additive.ofMul (QuotientGroup.mk (a * b) : ↥P ⧸ Q.subgroupOf P) ∈ W
        rw [this]
        exact W.add_mem ha hb
      one_mem' := by
        show Additive.ofMul (QuotientGroup.mk (1 : ↥P) : ↥P ⧸ Q.subgroupOf P) ∈ W
        exact W.zero_mem
      inv_mem' := fun {a} ha => by
        have : (Additive.ofMul (QuotientGroup.mk a⁻¹ : ↥P ⧸ Q.subgroupOf P)) =
            -Additive.ofMul (QuotientGroup.mk a) := rfl
        show Additive.ofMul (QuotientGroup.mk a⁻¹ : ↥P ⧸ Q.subgroupOf P) ∈ W
        rw [this]
        exact W.neg_mem ha }
  let B : Subgroup G := Bp.map P.subtype
  have hBmem : ∀ x : G, x ∈ B ↔ ∃ hx : x ∈ P,
      Additive.ofMul (QuotientGroup.mk (⟨x, hx⟩ : ↥P) : ↥P ⧸ Q.subgroupOf P) ∈ W := by
    intro x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hBP : B ≤ P := Subgroup.map_subtype_le _
  have hQB : Q ≤ B := by
    intro q hq
    rw [hBmem]
    refine ⟨hQP hq, ?_⟩
    have : (QuotientGroup.mk (⟨q, hQP hq⟩ : ↥P) : ↥P ⧸ Q.subgroupOf P) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hq)
    rw [this]
    exact W.zero_mem
  have hBX : X ≤ Subgroup.normalizer (B : Set G) := by
    refine burnsideI62_le_normalizer_of_conj_mem fun x hx b hb => ?_
    obtain ⟨hbP, hbW⟩ := (hBmem b).mp hb
    rw [hBmem]
    have h1 := hW ⟨x, hx⟩ _ hbW
    rw [burnsideI62_secRep_apply, burnsideI62_secAct_ofMul_mk] at h1
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hXP hx) b).mp hbP, h1⟩
  rcases hchief B hBX hQB hBP with h | h
  · left
    refine (Submodule.eq_bot_iff W).mpr fun w hw => ?_
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective w
    induction c using QuotientGroup.induction_on with
    | H p =>
      have : (p : G) ∈ B := (hBmem p).mpr ⟨p.2, hw⟩
      rw [h] at this
      have h1 : (QuotientGroup.mk p : ↥P ⧸ Q.subgroupOf P) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr this)
      rw [h1]
      rfl
  · right
    refine (Submodule.eq_top_iff').mpr fun w => ?_
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective w
    induction c using QuotientGroup.induction_on with
    | H p =>
      have : (p : G) ∈ B := by rw [h]; exact p.2
      obtain ⟨hx, hW'⟩ := (hBmem p).mp this
      exact hW'

@[expose] noncomputable def burnsideI62_secRepΓ {Γ : Type} [Group Γ] {Y : Subgroup G}
    [(Y.subgroupOf X).Normal] (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hY : ∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ = p)
    (e : ↥X ⧸ Y.subgroupOf X ≃* Γ) :
    Γ →* Module.End (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)) :=
  (QuotientGroup.lift (Y.subgroupOf X) (burnsideI62_secRep hXP hXQ)
    (fun x hx => MonoidHom.mem_ker.mpr (burnsideI62_secRep_ker hXP hXQ hY x hx))).comp
    e.symm.toMonoidHom

private theorem burnsideI62_secRepΓ_apply {Γ : Type} [Group Γ] {Y : Subgroup G}
    [(Y.subgroupOf X).Normal] (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) (hY : ∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ = p)
    (e : ↥X ⧸ Y.subgroupOf X ≃* Γ) (x : ↥X) :
    burnsideI62_secRepΓ hXP hXQ hY e (e (QuotientGroup.mk x)) = burnsideI62_secRep hXP hXQ x := by
  unfold burnsideI62_secRepΓ
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
    QuotientGroup.lift_mk]

end SecModule

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_sec_facts [Finite G] {V A : Subgroup G} (h : Hyp V A) {P Q : Subgroup G}
    (hPQ : IsChiefSection (V ⊔ A) (pairY V A) P Q) :
    IsMulCommutative ↥P ∧ (∀ p ∈ P, p * p = 1) ∧
      (∀ y ∈ pairY V A, ∀ p ∈ P, y * p * y⁻¹ = p) ∧ Q ≤ P := by
  have S := burnsideI62_prop24 h
  obtain ⟨hlt, hPY, -, -, -⟩ := hPQ
  have hYc : ∀ a ∈ pairY V A, ∀ b ∈ pairY V A, a * b = b * a := fun a ha b hb => S.comm_M ha hb
  refine ⟨⟨⟨fun a b => Subtype.ext (hYc a (hPY a.2) b (hPY b.2))⟩⟩,
    fun p hp => S.mem_M_sq (hPY hp), fun y hy p hp => ?_, hlt.le⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact hYc y hy p (hPY hp)

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_xy_section [Finite G] {V A : Subgroup G} (h : Hyp V A) {Q : Subgroup G}
    (hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G)) {x y : G} (hx : x ∈ V)
    (hxU : x ∉ NIn V A) (hy : y ∈ A) (hyB : y ∉ NIn A V) {c : G} (hcY : c ∈ pairY V A)
    (hc : x * y * c * (x * y)⁻¹ * c⁻¹ ∈ Q) : c ∈ Q := by
  have S := burnsideI62_prop24 h
  haveI : IsMulCommutative ↥(pairY V A) := S.isCommutative_M
  have hxyX : x * y ∈ V ⊔ A :=
    (V ⊔ A).mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
  refine burnsideI62_fpf_section_grp (Y := pairY V A) (Q := Q)
    (fun y' hy' => S.mem_M_sq hy') (g := x * y) (S.sup_le_normalizer_M hxyX)
    (k := orderOf (x * y)) (S.odd_orderOf_mul hx hxU hy hyB) (fun y' _ => ?_)
    (fun y' hy' hc' => ?_)
    (fun q hq => (Subgroup.mem_normalizer_iff.mp (hXQ hxyX) q).mp hq) hcY hc
  · rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  · refine S.eq_one_of_commute_mul hx hxU hy hyB hy' ?_
    calc x * y * y' = (x * y * y' * (x * y)⁻¹) * (x * y) := by group
      _ = y' * (x * y) := by rw [hc']

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_sec_fpf [Finite G] {V A : Subgroup G} (h : Hyp V A)
    {P Q : Subgroup G} [IsMulCommutative ↥P] [Module (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P))]
    (hPY : P ≤ pairY V A) (hXP : V ⊔ A ≤ Subgroup.normalizer (P : Set G))
    (hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G))
    {x y : ↥(V ⊔ A)} (hx : (x : G) ∈ V) (hxU : (x : G) ∉ NIn V A) (hy : (y : G) ∈ A)
    (hyB : (y : G) ∉ NIn A V) (v : Additive (↥P ⧸ Q.subgroupOf P))
    (hv : burnsideI62_secRep hXP hXQ (x * y) v = v) : v = 0 := by
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective v
  induction c using QuotientGroup.induction_on with
  | H p =>
    have hQ1 : (QuotientGroup.mk p : ↥P ⧸ Q.subgroupOf P) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hv' : Additive.ofMul (QuotientGroup.mk
          (CFSG.RankThree.GF2n.conjHom P (↑(x * y) : G) (hXP (x * y).2) p) : ↥P ⧸ Q.subgroupOf P) =
            Additive.ofMul (QuotientGroup.mk p) := hv
      have hv'' := Additive.ofMul.injective hv'
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hv''
      refine burnsideI62_xy_section h hXQ hx hxU hy hyB (hPY p.2) ?_
      have hconj : ((CFSG.RankThree.GF2n.conjHom P (↑(x * y) : G) (hXP (x * y).2) p : ↥P) : G) =
          (↑(x * y) : G) * p * (↑(x * y))⁻¹ := CFSG.RankThree.GF2n.coe_conjHom_apply _ _
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hconj] at hv''
      have hv3 : ((p : G))⁻¹ * ((↑(x * y) : G) * p * (↑(x * y))⁻¹) ∈ Q := by
        have := Q.inv_mem hv''
        simpa [mul_assoc] using this
      have hcomm : ((p : G))⁻¹ * ((↑(x * y) : G) * p * (↑(x * y))⁻¹) =
          ((↑(x * y) : G) * p * (↑(x * y))⁻¹) * (p : G)⁻¹ := by
        have h1 : (↑(x * y) : G) * p * (↑(x * y))⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp
          (hXP (x * y).2) p).mp p.2
        exact congrArg Subtype.val (mul_comm (⟨(p : G)⁻¹, P.inv_mem p.2⟩ : ↥P)
          ⟨_, h1⟩)
      rw [hcomm] at hv3
      exact hv3
    rw [hQ1]
    rfl

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_natural_sz [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal]
    (hSzNat : CFSG.CGT.PushingUpLit.SolKNA.SzFpfSimpleNatural) {a : ℕ} (ha : 1 ≤ a)
    (e : ↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* Sz a)
    (hpair : ∃ x y : ↥(V ⊔ A), (x : G) ∈ V ∧ (x : G) ∉ NIn V A ∧ (y : G) ∈ A ∧
      (y : G) ∉ NIn A V ∧ orderOf (e (QuotientGroup.mk (x * y))) = 5)
    {P Q : Subgroup G} (hPQ : IsChiefSection (V ⊔ A) (pairY V A) P Q) :
    IsNaturalSection (V ⊔ A) (pairY V A) P Q := by
  obtain ⟨hPcomm, hP2, hYP, hQP⟩ := burnsideI62_sec_facts h hPQ
  obtain ⟨hlt, hPY, hXP0, hXQ0, hchief⟩ := hPQ
  have hXP : V ⊔ A ≤ Subgroup.normalizer (P : Set G) := hXP0
  have hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G) := hXQ0
  haveI := hPcomm
  letI : Module (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)) := burnsideI62_secModule hP2
  right
  right
  refine ⟨a, ha, e, ?_⟩
  set ρ := burnsideI62_secRepΓ hXP hXQ hYP e with hρ
  obtain ⟨x, y, hx, hxU, hy, hyB, hord⟩ := hpair
  have hfpf : ∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ g v = v → v = 0 := by
    refine ⟨e (QuotientGroup.mk (x * y)), hord, fun v hv => ?_⟩
    rw [hρ, burnsideI62_secRepΓ_apply] at hv
    exact burnsideI62_sec_fpf h hPY hXP hXQ hx hxU hy hyB v hv
  have hnt : Nontrivial (Additive (↥P ⧸ Q.subgroupOf P)) := by
    obtain ⟨p, hp, hpQ⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Additive.ofMul (QuotientGroup.mk ⟨p, hp⟩), 0, fun h0 => hpQ ?_⟩⟩
    have h1 : (QuotientGroup.mk (⟨p, hp⟩ : ↥P) : ↥P ⧸ Q.subgroupOf P) = 1 := Additive.ofMul.injective h0
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  have hirr : ∀ W : Submodule (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)),
      (∀ g, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine burnsideI62_sec_irred hXP hXQ hQP hchief W fun x' w hw => ?_
    have := hW (e (QuotientGroup.mk x')) w hw
    rwa [hρ, burnsideI62_secRepΓ_apply] at this
  obtain ⟨θ, hθbij, hθ⟩ := hSzNat a ha (Additive (↥P ⧸ Q.subgroupOf P)) ρ hfpf hnt hirr
  refine burnsideI62_conjModuleIso hXP hXQ _ (AddEquiv.ofBijective θ hθbij) fun x' v => ?_
  have := hθ (e (QuotientGroup.mk x')) v
  rw [hρ, burnsideI62_secRepΓ_apply] at this
  exact this

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim77 CFSG.CGT.Timmesfeld75 CFSG.GH74.Uniqueness.Bender in
private theorem burnsideI62_sz_pair [Finite G] {V A : Subgroup G}
    (h : Hyp V A) [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] {a : ℕ} (ha : 1 ≤ a)
    (e : ↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* Sz a) :
    ∃ x y : ↥(V ⊔ A), (x : G) ∈ V ∧ (x : G) ∉ NIn V A ∧ (y : G) ∈ A ∧
      (y : G) ∉ NIn A V ∧ orderOf (e (QuotientGroup.mk (x * y))) = 5 := by
  have S := burnsideI62_prop24 h
  haveI : ((tiY V A).subgroupOf (V ⊔ A)).Normal := hN
  let e' : ↥(V ⊔ A) ⧸ (tiY V A).subgroupOf (V ⊔ A) ≃* Sz a := e
  have hBT : BenderType (↥(V ⊔ A) ⧸ (tiY V A).subgroupOf (V ⊔ A)) (2 * a + 1) 2 1 :=
    .suzuki a ha (e'.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hS := S.strongWC_image
  have hT0 := S.image_ne_bot
  obtain ⟨x₀, hx₀⟩ := S.exists_image_conj
  obtain ⟨b₀, hb₀, hb₀L⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hb₀mem : QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A)) ⟨b₀, Subgroup.mem_sup_right hb₀⟩ ∈
      (A.subgroupOf (V ⊔ A)).map (QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A))) :=
    ⟨_, hb₀, rfl⟩
  have hS' : StrongWC ((A.subgroupOf (V ⊔ A)).map
      (QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A)))) := by
    rw [hx₀]
    exact StrongWC.conj hS _
  have hT0' : (A.subgroupOf (V ⊔ A)).map (QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A))) ≠ ⊥ :=
    fun h' => (S.mk_not_mem_image hb₀ hb₀L) (by
      rw [h', Subgroup.mem_bot] at hb₀mem
      rw [hb₀mem]
      exact Subgroup.one_mem _)
  have hne : (V.subgroupOf (V ⊔ A)).map (QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A))) ≠
      (A.subgroupOf (V ⊔ A)).map (QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A))) :=
    fun h' => S.mk_not_mem_image hb₀ hb₀L (h' ▸ hb₀mem)
  have hwu : e'.symm (SzExplicit.w a) * e'.symm (SzExplicit.w a) = 1 := by
    rw [← map_mul, SzExplicit.w_mul_self, map_one]
  have huu : e'.symm (SzExplicit.u a) * e'.symm (SzExplicit.u a) = 1 := by
    rw [← map_mul, SzExplicit.u_mul_self, map_one]
  have hord5 : orderOf (e'.symm (SzExplicit.w a) * e'.symm (SzExplicit.u a)) = 5 := by
    rw [← map_mul, MulEquiv.orderOf_eq, SzExplicit.orderOf_w_mul_u]
  obtain ⟨t, ht, s', hs', hts⟩ := exists_mul_orderOf_eq hBT hS hT0 hS' hT0' hne hwu huu
    (by rw [hord5]; decide)
    (fun h' => by rw [h', orderOf_one] at hord5; exact absurd hord5 (by decide))
  rw [hord5] at hts
  obtain ⟨a₁, ha₁, rfl⟩ := ht
  obtain ⟨b₁, hb₁, rfl⟩ := hs'
  have hsq : ∀ (z : ↥(V ⊔ A)), (z : G) * z = 1 →
      QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A)) z *
        QuotientGroup.mk' ((tiY V A).subgroupOf (V ⊔ A)) z = 1 := fun z hz => by
    rw [← map_mul, show z * z = 1 from Subtype.ext hz, map_one]
  have hnot5 : ∀ y : ↥(V ⊔ A) ⧸ (tiY V A).subgroupOf (V ⊔ A), y * y = 1 → orderOf y ≠ 5 := by
    intro y hy h5
    have := orderOf_dvd_of_pow_eq_one (show y ^ 2 = 1 by rw [sq]; exact hy)
    rw [h5] at this
    exact absurd this (by decide)
  have ha₁L : (a₁ : G) ∉ tiU V A := fun h' => hnot5 _
    (hsq b₁ (S.sq_Ab (Subgroup.mem_subgroupOf.mp hb₁)))
    (by rwa [(Prop24Setup.mk_eq_one_iff (A := V) (Ab := A) (M := tiY V A) a₁).mpr (S.L_le_M h'),
      one_mul] at hts)
  have hb₁L : (b₁ : G) ∉ tiB V A := fun h' => hnot5 _
    (hsq a₁ (S.sq_A (Subgroup.mem_subgroupOf.mp ha₁)))
    (by rwa [(Prop24Setup.mk_eq_one_iff (A := V) (Ab := A) (M := tiY V A) b₁).mpr (S.Lb_le_M h'),
      mul_one] at hts)
  refine ⟨a₁, b₁, Subgroup.mem_subgroupOf.mp ha₁, ha₁L, Subgroup.mem_subgroupOf.mp hb₁, hb₁L, ?_⟩
  show orderOf (e' (QuotientGroup.mk (a₁ * b₁))) = 5
  rw [MulEquiv.orderOf_eq, QuotientGroup.mk_mul]
  exact hts

open scoped MatrixGroups Pointwise in
private theorem burnsideI62_exists_equiv_upper {K0 : Type} [Group K0] {f : ℕ} (hf : f ≠ 0)
    (e₀ : K0 ≃* SL(2, GaloisField 2 f)) {R : Subgroup K0} (hR : IsPGroup 2 R)
    (hcard : Nat.card R = 2 ^ f) :
    ∃ e' : K0 ≃* SL(2, GaloisField 2 f),
      R.map e'.toMonoidHom = CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR' : IsPGroup 2 (R.map e₀.toMonoidHom) := hR.map _
  obtain ⟨S₁, hS₁⟩ := hR'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, GaloisField 2 f)
    (CFSG.RankThree.GF2n.Tim78.sylowUpper hf) S₁
  have hcard1 : Nat.card (S₁ : Subgroup SL(2, GaloisField 2 f)) = 2 ^ f := by
    rw [Sylow.card_eq_multiplicity, ← CFSG.RankThree.GF2n.Tim78.two_pow_eq_factorization hf]
  have hRS : R.map e₀.toMonoidHom = (S₁ : Subgroup SL(2, GaloisField 2 f)) := by
    refine Subgroup.eq_of_le_of_card_ge hS₁ ?_
    rw [Subgroup.card_map_of_injective e₀.injective, hcard1, hcard]
  refine ⟨e₀.trans (MulAut.conj g⁻¹), ?_⟩
  have h1 : (S₁ : Subgroup SL(2, GaloisField 2 f)) = MulAut.conj g •
      ((CFSG.RankThree.GF2n.Tim78.sylowUpper hf : Sylow 2 SL(2, GaloisField 2 f)) :
        Subgroup SL(2, GaloisField 2 f)) := by
    rw [← Sylow.coe_subgroup_smul, hg]
  rw [← CFSG.RankThree.GF2n.Tim78.coe_sylowUpper hf]
  ext y
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : e₀ r ∈ (S₁ : Subgroup SL(2, GaloisField 2 f)) := hRS ▸ ⟨r, hr, rfl⟩
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hr'
    simpa [MulAut.conj_inv_apply, mul_assoc] using hr'
  · intro hy
    have hy' : (MulAut.conj g) y ∈ (S₁ : Subgroup SL(2, GaloisField 2 f)) := by
      rw [h1]
      exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g) _ hy
    rw [← hRS] at hy'
    obtain ⟨r, hr, hre⟩ := hy'
    refine ⟨r, hr, ?_⟩
    have : e₀ r = (MulAut.conj g) y := hre
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.trans_apply, this]
    simp [MulAut.conj_apply, mul_assoc]

open CFSG.ASVolI.ChIJK in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_comm_mem_U [Finite G] {V A : Subgroup G} (h : Hyp V A) {x p : G}
    (hx : x ∈ V)
    (hp : p ∈ pairY V A) : x * p * x⁻¹ * p⁻¹ ∈ NIn V A := by
  have hb := h.toBase
  by_cases hxU : x ∈ NIn V A
  · have hxY : x ∈ tiY V A := Subgroup.mem_sup_left hxU
    have hcomm : x * p = p * x := hb.comm_tiY hxY hp
    rw [show x * p * x⁻¹ * p⁻¹ = (x * p) * x⁻¹ * p⁻¹ by group, hcomm]
    simp
  · have hxX : x ∈ tiX V A := Subgroup.mem_sup_left hx
    have hx2 := hb.mul_self_V hx
    have h1 := hb.commutatorElement_mem_centralizer hxX hx2 hp
    rw [hb.inf_centralizer_tiY hx hxU] at h1
    have h2 := (NIn V A).inv_mem h1
    rw [commutatorElement_def] at h2
    have : (p * x * p⁻¹ * x⁻¹)⁻¹ = x * p * x⁻¹ * p⁻¹ := by group
    rw [this] at h2
    exact h2

private theorem burnsideI62_dih_two_mul {m : ℕ} (hm : Odd m) (a : ZMod m) (h : a + a = 0) : a =
    0 := by
  obtain ⟨j, rfl⟩ := hm
  have h1 : ((2 * j + 1 : ℕ) : ZMod (2 * j + 1)) = 0 := ZMod.natCast_self _
  push_cast at h1
  calc a = (2 * (j : ZMod (2 * j + 1)) + 1) * a - (j : ZMod (2 * j + 1)) * (a + a) := by ring
    _ = 0 := by rw [h1, h]; ring

private theorem burnsideI62_dih_r_pow {m : ℕ} [NeZero m] (i : ZMod m) :
    (DihedralGroup.r i : DihedralGroup m) ^ m = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, DihedralGroup.orderOf_r]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m i.val)

private theorem burnsideI62_dih_comm_pow {m : ℕ} (hm : Odd m) (z s : DihedralGroup m) (hs : s *
    s = 1) :
    (z * s * z⁻¹ * s⁻¹) ^ m = 1 := by
  haveI : NeZero m := ⟨hm.pos.ne'⟩
  rcases s with b | b
  · have hb : b = 0 := by
      have h1 : (DihedralGroup.r b : DihedralGroup m) * DihedralGroup.r b = 1 := hs
      rw [DihedralGroup.r_mul_r, DihedralGroup.one_def] at h1
      exact burnsideI62_dih_two_mul hm b (DihedralGroup.r.inj h1)
    subst hb
    rw [DihedralGroup.r_zero]
    simp
  · rcases z with a | a
    · have : (DihedralGroup.r a : DihedralGroup m) * DihedralGroup.sr b * (DihedralGroup.r a)⁻¹ *
          (DihedralGroup.sr b)⁻¹ = DihedralGroup.r (2 * a) := by
        simp [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
        ring_nf
      rw [this]
      exact burnsideI62_dih_r_pow _
    · have : (DihedralGroup.sr a : DihedralGroup m) * DihedralGroup.sr b * (DihedralGroup.sr a)⁻¹ *
          (DihedralGroup.sr b)⁻¹ = DihedralGroup.r (2 * b - 2 * a) := by
        simp [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
        ring_nf
      rw [this]
      exact burnsideI62_dih_r_pow _

private theorem burnsideI62_dih_centralizer {m : ℕ} (hm : Odd m) {z s : DihedralGroup m} (hs :
    s * s = 1)
    (hs1 : s ≠ 1) (hzs : z * s = s * z) : z = 1 ∨ z = s := by
  rcases s with b | b
  · exfalso
    apply hs1
    have h1 : (DihedralGroup.r b : DihedralGroup m) * DihedralGroup.r b = 1 := hs
    rw [DihedralGroup.r_mul_r, DihedralGroup.one_def] at h1
    have := burnsideI62_dih_two_mul hm b (DihedralGroup.r.inj h1)
    rw [this]
    rfl
  · rcases z with a | a
    · left
      simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at hzs
      have h1 := DihedralGroup.sr.inj hzs
      have h2 : a + a = 0 := by linear_combination -h1
      rw [burnsideI62_dih_two_mul hm a h2]
      rfl
    · right
      simp only [DihedralGroup.sr_mul_sr] at hzs
      have h1 := DihedralGroup.r.inj hzs
      have h2 : (b - a) + (b - a) = 0 := by linear_combination h1
      have := burnsideI62_dih_two_mul hm _ h2
      rw [sub_eq_zero.mp this]

open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_eq_one_of_centralizes [Finite G] {V A : Subgroup G} (h : Hyp V A)
    {x t u : G} (hx : x ∈ V) (hu : u ∈ V) (hu1 : u ≠ 1) (htu : t * u = u * t) {n : ℕ}
    (hn : Odd n) (htn : t ^ n = 1) (hxt : x * t * x⁻¹ = t⁻¹) : t = 1 := by
  have hb := h.toBase
  have hN : t ∈ Subgroup.normalizer (V : Set G) := hb.mem_normalizer_of_comm hu hu1 htu
  have h1 : t * x * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have h2 : x * t⁻¹ * x⁻¹ = t := by
    have := congrArg (fun w => w⁻¹) hxt
    simpa [mul_assoc] using this
  have h3 : t * x * t⁻¹ = (t * t) * x := by
    calc t * x * t⁻¹ = t * (x * t⁻¹ * x⁻¹) * x := by group
      _ = t * t * x := by rw [h2]
  have h4 : t * t ∈ V := by
    have := V.mul_mem (h3 ▸ h1) (V.inv_mem hx)
    simpa using this
  obtain ⟨j, rfl⟩ := hn
  have e1 : t = (t * t) ^ (j + 1) := by
    calc t = t ^ (2 * j + 1) * t := by rw [htn, one_mul]
      _ = (t * t) ^ (j + 1) := by
        rw [← pow_succ, ← sq, ← pow_mul]
        exact congrArg (t ^ ·) (by omega)
  have htV : t ∈ V := by
    rw [e1]
    exact V.pow_mem h4 _
  rw [e1, hb.mul_self_V htV, one_pow]

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_eq_one_of_triv [Finite G] {V A : Subgroup G} (h : Hyp V A) {P Q :
    Subgroup G}
    (hlt : Q < P) (hPY : P ≤ pairY V A) (hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G))
    {x t : G} (hx : x ∈ V) (hxU : x ∉ NIn V A) (htX : t ∈ V ⊔ A)
    (htP : ∀ p ∈ P, t * p * t⁻¹ * p⁻¹ ∈ Q) {n : ℕ} (hn : Odd n) (htn : t ^ n = 1)
    (hxt : x * t * x⁻¹ = t⁻¹) : t = 1 := by
  have S := burnsideI62_prop24 h
  have hb := h.toBase
  haveI : IsMulCommutative ↥(pairY V A) := S.isCommutative_M
  obtain ⟨p₀, hp₀P, hp₀Q⟩ := SetLike.exists_of_lt hlt
  obtain ⟨p, hpY, htp, hpc⟩ := burnsideI62_fixed_section_grp (Y := pairY V A) (Q := Q)
    (fun y' hy' => S.mem_M_sq hy') (g := t) (S.sup_le_normalizer_M htX) (k := n) hn
    (fun y _ => by rw [htn]; simp)
    (fun q hq => (Subgroup.mem_normalizer_iff.mp (hXQ htX) q).mp hq)
    (hPY hp₀P) (htP p₀ hp₀P)
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply hp₀Q
    simpa using Q.inv_mem hpc
  have h5 : t * x = x * t⁻¹ := by
    have h2 : x * t⁻¹ * x⁻¹ = t := by
      have := congrArg (fun w => w⁻¹) hxt
      simpa [mul_assoc] using this
    calc t * x = (x * t⁻¹ * x⁻¹) * x := by rw [h2]
      _ = x * t⁻¹ := by group
  have h6 : t⁻¹ * p * t = p := by
    calc t⁻¹ * p * t = t⁻¹ * (t * p * t⁻¹) * t := by rw [htp]
      _ = p := by group
  by_cases hxp : x * p * x⁻¹ = p
  · have hpU : p ∈ NIn V A := by
      have h7 := hb.inf_centralizer_tiY hx hxU
      have : p ∈ tiY V A ⊓ Subgroup.centralizer ({x} : Set G) := by
        refine ⟨hpY, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        rw [mul_inv_eq_iff_eq_mul] at hxp
        exact hxp.symm
      rw [h7] at this
      exact this
    refine burnsideI62_eq_one_of_centralizes h hx hpU.1 hp1 ?_ hn htn hxt
    exact (mul_inv_eq_iff_eq_mul.mp htp)
  · have huU : x * p * x⁻¹ * p⁻¹ ∈ NIn V A := burnsideI62_comm_mem_U h hx hpY
    have hu1 : x * p * x⁻¹ * p⁻¹ ≠ 1 := by
      intro h1
      exact hxp (mul_inv_eq_one.mp h1)
    have hconj : t * (x * p * x⁻¹) * t⁻¹ = x * p * x⁻¹ := by
      calc t * (x * p * x⁻¹) * t⁻¹ = (t * x) * p * (t * x)⁻¹ := by group
        _ = (x * t⁻¹) * p * (x * t⁻¹)⁻¹ := by rw [h5]
        _ = x * (t⁻¹ * p * t) * x⁻¹ := by group
        _ = x * p * x⁻¹ := by rw [h6]
    have hpinv : t * p⁻¹ * t⁻¹ = p⁻¹ := by
      calc t * p⁻¹ * t⁻¹ = (t * p * t⁻¹)⁻¹ := by group
        _ = p⁻¹ := by rw [htp]
    have hu : t * (x * p * x⁻¹ * p⁻¹) * t⁻¹ = x * p * x⁻¹ * p⁻¹ := by
      calc t * (x * p * x⁻¹ * p⁻¹) * t⁻¹
          = (t * (x * p * x⁻¹) * t⁻¹) * (t * p⁻¹ * t⁻¹) := by group
        _ = x * p * x⁻¹ * p⁻¹ := by rw [hconj, hpinv]
    exact burnsideI62_eq_one_of_centralizes h hx huU.1 hu1 (mul_inv_eq_iff_eq_mul.mp hu) hn htn hxt

open CFSG.ASVolI.ChIJK in
@[expose] def burnsideI62_kernel {X P Q : Subgroup G} (hXP : X ≤ Subgroup.normalizer (P : Set G))
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) : Subgroup G where
  carrier := {z | z ∈ X ∧ ActsTriviallyOnSection P Q z}
  mul_mem' := by
    rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
    refine ⟨X.mul_mem haX hbX, fun p hp => ?_⟩
    have h1 := ha p hp
    have h2 := hb p hp
    have h3 : b⁻¹ * (a⁻¹ * p * a * p⁻¹) * (b⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hXQ (X.inv_mem hbX)) _).mp h1
    have e : (a * b)⁻¹ * p * (a * b) * p⁻¹ =
        (b⁻¹ * (a⁻¹ * p * a * p⁻¹) * (b⁻¹)⁻¹) * (b⁻¹ * p * b * p⁻¹) := by group
    rw [e]
    exact Q.mul_mem h3 h2
  one_mem' := ⟨X.one_mem, fun p hp => by simpa using Q.one_mem⟩
  inv_mem' := by
    rintro a ⟨haX, ha⟩
    refine ⟨X.inv_mem haX, fun p hp => ?_⟩
    have hpP : a * p * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hXP haX) p).mp hp
    have h1 := Q.inv_mem (ha _ hpP)
    have e : (a⁻¹ * (a * p * a⁻¹) * a * (a * p * a⁻¹)⁻¹)⁻¹ = (a⁻¹)⁻¹ * p * a⁻¹ * p⁻¹ := by group
    rwa [e] at h1

private theorem burnsideI62_kernel_conj {X P Q : Subgroup G} {hXP : X ≤ Subgroup.normalizer (P
    : Set G)}
    {hXQ : X ≤ Subgroup.normalizer (Q : Set G)} {w z : G} (hw : w ∈ X)
    (hz : z ∈ burnsideI62_kernel hXP hXQ) : w * z * w⁻¹ ∈ burnsideI62_kernel hXP hXQ := by
  obtain ⟨hzX, hz⟩ := hz
  refine ⟨X.mul_mem (X.mul_mem hw hzX) (X.inv_mem hw), fun p hp => ?_⟩
  have hp1 : w⁻¹ * p * (w⁻¹)⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hXP (X.inv_mem hw)) p).mp hp
  have h1 := hz _ (by simpa using hp1)
  have h2 : w * (z⁻¹ * (w⁻¹ * p * w) * z * (w⁻¹ * p * w)⁻¹) * w⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hXQ hw) _).mp (by simpa using h1)
  have e : (w * z * w⁻¹)⁻¹ * p * (w * z * w⁻¹) * p⁻¹ =
      w * (z⁻¹ * (w⁻¹ * p * w) * z * (w⁻¹ * p * w)⁻¹) * w⁻¹ := by group
  rw [e]
  exact h2

private theorem burnsideI62_mem_kernel_of_centralizes {X Y P Q : Subgroup G}
    {hXP : X ≤ Subgroup.normalizer (P : Set G)} {hXQ : X ≤ Subgroup.normalizer (Q : Set G)}
    (hYX : Y ≤ X) (hY : ∀ y ∈ Y, ∀ p ∈ P, y * p * y⁻¹ = p) {y : G} (hy : y ∈ Y) :
    y ∈ burnsideI62_kernel hXP hXQ := by
  refine ⟨hYX hy, fun p hp => ?_⟩
  have := hY y⁻¹ (Y.inv_mem hy) p hp
  rw [inv_inv] at this
  rw [this]
  simp

private theorem burnsideI62_conj_swap {x y : G} (hx2 : x * x = 1) (hy2 : y * y = 1) {j : ℕ}
    (hg : (x * y) ^ (2 * j + 1) = 1) : y = (x * y) ^ j * x * ((x * y) ^ j)⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hinv : x * (x * y) * x⁻¹ = (x * y)⁻¹ := by
    calc x * (x * y) * x⁻¹ = (x * x) * y * x⁻¹ := by group
      _ = y⁻¹ * x⁻¹ := by rw [hx2, one_mul, hyi]
      _ = (x * y)⁻¹ := by rw [mul_inv_rev]
  have hpowinv : x * (x * y) ^ j * x⁻¹ = ((x * y) ^ j)⁻¹ := by
    rw [← inv_pow, ← hinv, conj_pow]
  have h1 : x * ((x * y) ^ j)⁻¹ * x⁻¹ = (x * y) ^ j := by
    have e : ∀ c : G, x * c⁻¹ * x⁻¹ = (x * c * x⁻¹)⁻¹ := fun c => by group
    rw [e, hpowinv, inv_inv]
  have h2 : (x * y) ^ (2 * j) = (x * y)⁻¹ := by
    have : (x * y) ^ (2 * j) * (x * y) = 1 := by rw [← pow_succ]; exact hg
    exact eq_inv_of_mul_eq_one_left this
  calc y = y⁻¹ := hyi.symm
    _ = (x * y)⁻¹ * x := by rw [mul_inv_rev, inv_mul_cancel_right]
    _ = (x * y) ^ (2 * j) * x := by rw [h2]
    _ = (x * y) ^ j * (x * y) ^ j * x := by rw [two_mul, pow_add]
    _ = (x * y) ^ j * (x * ((x * y) ^ j)⁻¹ * x⁻¹) * x := by rw [h1]
    _ = (x * y) ^ j * x * ((x * y) ^ j)⁻¹ := by
      generalize (x * y) ^ j = c
      group

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_natural_dihedral [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] {m : ℕ} (hm : Odd m) (h3 : 3 ≤ m)
    (e : ↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* DihedralGroup m)
    {P Q : Subgroup G} (hPQ : IsChiefSection (V ⊔ A) (pairY V A) P Q) :
    IsNaturalSection (V ⊔ A) (pairY V A) P Q := by
  obtain ⟨hPcomm, hP2, hYP, hQP⟩ := burnsideI62_sec_facts h hPQ
  obtain ⟨hlt, hPY, hXP0, hXQ0, hchief⟩ := hPQ
  have hXP : V ⊔ A ≤ Subgroup.normalizer (P : Set G) := hXP0
  have hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G) := hXQ0
  have S := burnsideI62_prop24 h
  have hb := h.toBase
  left
  refine ⟨m, hm, by omega, ⟨e⟩, fun k hkX hk => ?_⟩
  by_contra hkY
  obtain ⟨x, hx, hxU⟩ := h.exists_mem_not_mem
  obtain ⟨y, hy, hyB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hxU' : x ∉ NIn V A := hxU
  have hyB' : y ∉ NIn A V := hyB
  have hxX : x ∈ V ⊔ A := Subgroup.mem_sup_left hx
  have hyX : y ∈ V ⊔ A := Subgroup.mem_sup_right hy
  have hx2 : x * x = 1 := hb.mul_self_V hx
  have hy2 : y * y = 1 := S.sq_Ab hy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxY : x ∉ pairY V A := fun hxY => hxU' ((hb.inf_centralizer_tiY hx hxU).le
    ⟨hxY, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩)
  have hkK : k ∈ burnsideI62_kernel hXP hXQ := ⟨hkX, hk⟩
  have hYK : ∀ z ∈ pairY V A, z ∈ burnsideI62_kernel hXP hXQ := fun z hz =>
    burnsideI62_mem_kernel_of_centralizes (burnsideI62_pairY_le V A) hYP hz
  let eb : ↥(V ⊔ A) →* DihedralGroup m :=
    e.toMonoidHom.comp (QuotientGroup.mk' ((pairY V A).subgroupOf (V ⊔ A)))
  have heb : ∀ z : ↥(V ⊔ A), eb z = 1 ↔ (z : G) ∈ pairY V A := by
    intro z
    show e (QuotientGroup.mk z) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  let kk : ↥(V ⊔ A) := ⟨k, hkX⟩
  let xx : ↥(V ⊔ A) := ⟨x, hxX⟩
  have hxx2 : eb xx * eb xx = 1 := by
    rw [← map_mul]
    have : xx * xx = 1 := Subtype.ext hx2
    rw [this, map_one]
  have hxx1 : eb xx ≠ 1 := fun h1 => hxY ((heb xx).mp h1)
  by_cases hc₁ : k * x * k⁻¹ * x⁻¹ ∈ pairY V A
  ·
    have hcomm : eb kk * eb xx = eb xx * eb kk := by
      have h1 : eb (kk * xx * kk⁻¹ * xx⁻¹) = 1 := (heb _).mpr hc₁
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    rcases burnsideI62_dih_centralizer hm hxx2 hxx1 hcomm with h0 | h0
    · exact hkY ((heb kk).mp h0)
    · have hkx : k⁻¹ * x ∈ pairY V A := by
        have h1 : eb (kk⁻¹ * xx) = 1 := by rw [map_mul, map_inv, h0, inv_mul_cancel]
        exact (heb _).mp h1
      have hxK : x ∈ burnsideI62_kernel hXP hXQ := by
        have : x = k * (k⁻¹ * x) := by group
        rw [this]
        exact (burnsideI62_kernel hXP hXQ).mul_mem hkK (hYK _ hkx)
      obtain ⟨j, hj⟩ := S.odd_orderOf_mul hx hxU' hy hyB'
      have hgpow : (x * y) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
      have hyK : y ∈ burnsideI62_kernel hXP hXQ := by
        rw [burnsideI62_conj_swap hx2 hy2 hgpow]
        exact burnsideI62_kernel_conj ((V ⊔ A).pow_mem ((V ⊔ A).mul_mem hxX hyX) j) hxK
      have hgK : x * y ∈ burnsideI62_kernel hXP hXQ :=
        (burnsideI62_kernel hXP hXQ).mul_mem hxK hyK
      obtain ⟨p₀, hp₀P, hp₀Q⟩ := SetLike.exists_of_lt hlt
      refine hp₀Q (burnsideI62_xy_section h hXQ hx hxU' hy hyB' (hPY hp₀P) ?_)
      have := ((burnsideI62_kernel hXP hXQ).inv_mem hgK).2 p₀ hp₀P
      rwa [inv_inv] at this
  ·
    obtain ⟨c₁, hc₁def⟩ : ∃ c₁, c₁ = k * x * k⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hc₁def] at hc₁
    have hc₁X : c₁ ∈ V ⊔ A := by
      rw [hc₁def]
      exact (V ⊔ A).mul_mem ((V ⊔ A).mul_mem ((V ⊔ A).mul_mem hkX hxX) ((V ⊔ A).inv_mem hkX))
        ((V ⊔ A).inv_mem hxX)
    have hc₁K : c₁ ∈ burnsideI62_kernel hXP hXQ := by
      have h1 : x * k⁻¹ * x⁻¹ ∈ burnsideI62_kernel hXP hXQ :=
        burnsideI62_kernel_conj hxX ((burnsideI62_kernel hXP hXQ).inv_mem hkK)
      have : c₁ = k * (x * k⁻¹ * x⁻¹) := by rw [hc₁def]; group
      rw [this]
      exact (burnsideI62_kernel hXP hXQ).mul_mem hkK h1
    have hc₁m : c₁ ^ m ∈ pairY V A := by
      have h1 : eb (⟨c₁, hc₁X⟩ ^ m) = 1 := by
        rw [map_pow]
        have e1 : (⟨c₁, hc₁X⟩ : ↥(V ⊔ A)) = kk * xx * kk⁻¹ * xx⁻¹ := Subtype.ext hc₁def
        rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv]
        exact burnsideI62_dih_comm_pow hm _ _ hxx2
      exact (heb _).mp h1
    obtain ⟨t, htdef⟩ : ∃ t, t = c₁ ^ (m + 1) := ⟨_, rfl⟩
    have htK : t ∈ burnsideI62_kernel hXP hXQ := by
      rw [htdef]
      exact (burnsideI62_kernel hXP hXQ).pow_mem hc₁K _
    have hc₁m2 : (c₁ ^ m) * (c₁ ^ m) = 1 := S.mem_M_sq hc₁m
    have htn : t ^ m = 1 := by
      have h1 : t ^ m = (c₁ ^ m) ^ (m + 1) := by
        rw [htdef, ← pow_mul, ← pow_mul, mul_comm]
      have h2 : (c₁ ^ m) ^ (m + 1) = 1 := by
        obtain ⟨j, hj⟩ := hm
        rw [show m + 1 = 2 * (j + 1) by omega, pow_mul, sq, hc₁m2, one_pow]
      rw [h1, h2]
    have hxinv : x * c₁ * x⁻¹ = c₁⁻¹ := by
      have e1 : x * c₁ * x⁻¹ = x * k * x * k⁻¹ := by
        rw [hc₁def]
        calc x * (k * x * k⁻¹ * x⁻¹) * x⁻¹ = x * k * x * k⁻¹ * (x⁻¹ * x⁻¹) := by group
          _ = x * k * x * k⁻¹ := by rw [← mul_inv_rev, hx2, inv_one, mul_one]
      have e2 : c₁⁻¹ = x * k * x * k⁻¹ := by
        rw [hc₁def]
        calc (k * x * k⁻¹ * x⁻¹)⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
          _ = x * k * x * k⁻¹ := by rw [hxi]
      rw [e1, e2]
    have hxt : x * t * x⁻¹ = t⁻¹ := by
      rw [htdef, ← conj_pow, hxinv, inv_pow]
    have htP : ∀ p ∈ P, t * p * t⁻¹ * p⁻¹ ∈ Q := by
      intro p hp
      have := ((burnsideI62_kernel hXP hXQ).inv_mem htK).2 p hp
      rwa [inv_inv] at this
    have ht1 : t = 1 :=
      burnsideI62_eq_one_of_triv h hlt hPY hXQ hx hxU' htK.1 htP hm htn hxt
    apply hc₁
    have hc₁eq : c₁ = t * (c₁ ^ m)⁻¹ := by rw [htdef, pow_succ', mul_inv_cancel_right]
    rw [hc₁eq, ht1, one_mul]
    exact (pairY V A).inv_mem hc₁m

open CFSG.ASVolI.ChIJK in
open scoped IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 in
private theorem burnsideI62_secRep_quad [Finite G] {V A : Subgroup G} (h : Hyp V A) {P Q :
    Subgroup G}
    [IsMulCommutative ↥P] [Module (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P))]
    (hPY : P ≤ pairY V A) (hXP : V ⊔ A ≤ Subgroup.normalizer (P : Set G))
    (hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G)) {z z' : ↥(V ⊔ A)} (hz : (z : G) ∈ V)
    (hz' : (z' : G) ∈ V) (v : Additive (↥P ⧸ Q.subgroupOf P)) :
    burnsideI62_secRep hXP hXQ z' (burnsideI62_secRep hXP hXQ z v - v) =
      burnsideI62_secRep hXP hXQ z v - v := by
  have hb := h.toBase
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective v
  induction c using QuotientGroup.induction_on with
  | H p =>
    have e1 : burnsideI62_secRep hXP hXQ z (Additive.ofMul (QuotientGroup.mk p)) -
        Additive.ofMul (QuotientGroup.mk p) = Additive.ofMul (QuotientGroup.mk
          (CFSG.RankThree.GF2n.conjHom P (z : G) (hXP z.2) p * p⁻¹)) := by
      rw [burnsideI62_secRep_apply, burnsideI62_secAct_ofMul_mk, ← ofMul_div]
      congr 1
      rw [div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [e1, burnsideI62_secRep_apply, burnsideI62_secAct_ofMul_mk]
    congr 2
    apply Subtype.ext
    have hu : (z : G) * p * (z : G)⁻¹ * (p : G)⁻¹ ∈ NIn V A :=
      burnsideI62_comm_mem_U h hz (hPY p.2)
    have hcomm := hb.comm_V hz' hu.1
    simp only [CFSG.RankThree.GF2n.coe_conjHom_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [mul_inv_eq_iff_eq_mul]
    exact hcomm

open CFSG.ASVolI.ChIJK in
open scoped MatrixGroups IsMulCommutative in
open CFSG.Quasithin CFSG.Quasithin.ASInputs CFSG.Quasithin.I62 CFSG.RankThree.GF2n.Tim77 in
private theorem burnsideI62_natural_l2 [Finite G] {V A : Subgroup G} (h : Hyp V A)
    [hN : ((pairY V A).subgroupOf (V ⊔ A)).Normal] {f : ℕ} (hf : 2 ≤ f)
    (hrel : (NIn V A).relIndex V = 2 ^ f)
    (e : ↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A) ≃* PSL(2, GaloisField 2 f))
    {P Q : Subgroup G} (hPQ : IsChiefSection (V ⊔ A) (pairY V A) P Q) :
    IsNaturalSection (V ⊔ A) (pairY V A) P Q := by
  obtain ⟨hPcomm, hP2, hYP, hQP⟩ := burnsideI62_sec_facts h hPQ
  obtain ⟨hlt, hPY, hXP0, hXQ0, hchief⟩ := hPQ
  have hXP : V ⊔ A ≤ Subgroup.normalizer (P : Set G) := hXP0
  have hXQ : V ⊔ A ≤ Subgroup.normalizer (Q : Set G) := hXQ0
  haveI := hPcomm
  letI : Module (ZMod 2) (Additive (↥P ⧸ Q.subgroupOf P)) := burnsideI62_secModule hP2
  have S := burnsideI62_prop24 h
  have hb := h.toBase
  haveI : ((tiY V A).subgroupOf (V ⊔ A)).Normal := hN
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup (↥(V ⊔ A) ⧸ (pairY V A).subgroupOf (V ⊔ A)),
      R = (V.subgroupOf (V ⊔ A)).map (QuotientGroup.mk' ((pairY V A).subgroupOf (V ⊔ A))) :=
    ⟨_, rfl⟩
  have hRcard : Nat.card ↥R = 2 ^ f := by
    rw [hRdef]
    exact S.relIndex_eq_card_image.symm.trans hrel
  have hRp : IsPGroup 2 ↥R := IsPGroup.of_card hRcard
  obtain ⟨e', he'⟩ := burnsideI62_exists_equiv_upper (by omega : f ≠ 0)
    (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo) hRp hRcard
  set ρ := burnsideI62_secRepΓ hXP hXQ hYP e' with hρ
  letI : DistribMulAction SL(2, GaloisField 2 f) (Additive (↥P ⧸ Q.subgroupOf P)) :=
    { smul := fun g v => ρ g v
      one_smul := fun v => by
        show ρ 1 v = v
        rw [map_one]
        rfl
      mul_smul := fun g g' v => by
        show ρ (g * g') v = ρ g (ρ g' v)
        rw [map_mul]
        rfl
      smul_zero := fun g => map_zero (ρ g)
      smul_add := fun g v v' => map_add (ρ g) v v' }
  obtain ⟨x, hx, hxU⟩ := h.exists_mem_not_mem
  obtain ⟨y, hy, hyB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  have hxU' : x ∉ NIn V A := hxU
  have hyB' : y ∉ NIn A V := hyB
  have hxX : x ∈ V ⊔ A := Subgroup.mem_sup_left hx
  have hyX : y ∈ V ⊔ A := Subgroup.mem_sup_right hy
  have hfix : ∀ v : Additive (↥P ⧸ Q.subgroupOf P),
      (∀ g : SL(2, GaloisField 2 f), g • v = v) → v = 0 := by
    intro v hv
    have h2 : ρ (e' (QuotientGroup.mk (⟨x, hxX⟩ * ⟨y, hyX⟩ : ↥(V ⊔ A)))) v = v :=
      hv (e' (QuotientGroup.mk (⟨x, hxX⟩ * ⟨y, hyX⟩ : ↥(V ⊔ A))))
    rw [hρ, burnsideI62_secRepΓ_apply] at h2
    exact burnsideI62_sec_fpf h hPY hXP hXQ (x := ⟨x, hxX⟩) (y := ⟨y, hyX⟩) hx hxU' hy hyB' v h2
  have hquad : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f),
      ∀ a' ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f),
      ∀ v : Additive (↥P ⧸ Q.subgroupOf P), a' • (a • v - v) = a • v - v := by
    intro a ha a' ha' v
    rw [← he', hRdef] at ha ha'
    obtain ⟨r, ⟨z, hz, rfl⟩, rfl⟩ := ha
    obtain ⟨r', ⟨z', hz', rfl⟩, rfl⟩ := ha'
    have h1 := burnsideI62_secRep_quad h hPY hXP hXQ (z := z) (z' := z')
      (Subgroup.mem_subgroupOf.mp hz) (Subgroup.mem_subgroupOf.mp hz') v
    have hk : ∀ (w : ↥(V ⊔ A)) (u : Additive (↥P ⧸ Q.subgroupOf P)),
        ρ (e' (QuotientGroup.mk w)) u = burnsideI62_secRep hXP hXQ w u := by
      intro w u
      rw [hρ, burnsideI62_secRepΓ_apply]
    show ρ (e' (QuotientGroup.mk z')) (ρ (e' (QuotientGroup.mk z)) v - v) =
      ρ (e' (QuotientGroup.mk z)) v - v
    rw [hk, hk]
    exact h1
  have hnt : Nontrivial (Additive (↥P ⧸ Q.subgroupOf P)) := by
    obtain ⟨p, hp, hpQ⟩ := SetLike.exists_of_lt hlt
    refine ⟨⟨Additive.ofMul (QuotientGroup.mk ⟨p, hp⟩), 0, fun h0 => hpQ ?_⟩⟩
    have h1 : (QuotientGroup.mk (⟨p, hp⟩ : ↥P) : ↥P ⧸ Q.subgroupOf P) = 1 :=
      Additive.ofMul.injective h0
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)
  obtain ⟨w, hw0, hwfix⟩ : ∃ w : Additive (↥P ⧸ Q.subgroupOf P), w ≠ 0 ∧
      ∀ a ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f), a • w = w := by
    by_cases htriv : ∀ a ∈ CFSG.Timmesfeld.upperUnipotent (GaloisField 2 f),
        ∀ v : Additive (↥P ⧸ Q.subgroupOf P), a • v = v
    · obtain ⟨v₀, hv₀⟩ := exists_ne (0 : Additive (↥P ⧸ Q.subgroupOf P))
      exact ⟨v₀, hv₀, fun a ha => htriv a ha v₀⟩
    · push Not at htriv
      obtain ⟨a, ha, v, hav⟩ := htriv
      exact ⟨a • v - v, sub_ne_zero.mpr hav, fun a' ha' => hquad a ha a' ha' v⟩
  obtain ⟨θ, hθinj, hθrange, hθe1, hθ⟩ :=
    CFSG.Timmesfeld.ARS.exists_natural_of_quadratic hfix hquad hwfix hw0
  have hθsurj : Function.Surjective θ := by
    have hW : ∀ x' : ↥(V ⊔ A), ∀ u ∈ AddSubgroup.toZModSubmodule 2 θ.range,
        burnsideI62_secRep hXP hXQ x' u ∈ AddSubgroup.toZModSubmodule 2 θ.range := by
      intro x' u hu
      have hu' : u ∈ θ.range := hu
      obtain ⟨v, rfl⟩ := hu'
      show _ ∈ θ.range
      refine ⟨Matrix.mulVec ((e' (QuotientGroup.mk x') : SL(2, GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) v, ?_⟩
      rw [hθ]
      show ρ (e' (QuotientGroup.mk x')) (θ v) = _
      rw [hρ, burnsideI62_secRepΓ_apply]
    rcases burnsideI62_sec_irred hXP hXQ hQP hchief _ hW with h0 | h0
    · exfalso
      have hwW : w ∈ AddSubgroup.toZModSubmodule 2 θ.range := ⟨![1, 0], hθe1⟩
      rw [h0] at hwW
      exact hw0 ((Submodule.mem_bot _).mp hwW)
    · intro u
      have : u ∈ AddSubgroup.toZModSubmodule 2 θ.range := by rw [h0]; trivial
      exact this
  right
  left
  refine ⟨f, by omega, e', ?_⟩
  refine burnsideI62_conjModuleIso hXP hXQ _ (AddEquiv.ofBijective θ ⟨hθinj, hθsurj⟩)
    fun x' v => ?_
  have h1 := hθ (e' (QuotientGroup.mk x')) v
  show θ _ = _
  rw [h1]
  show ρ (e' (QuotientGroup.mk x')) (θ v) = _
  rw [hρ, burnsideI62_secRepΓ_apply]
  rfl

end BurnsideI62

end BurnsideI62

section

theorem as_I_6_2 : I_6_2 := by
  intro G _ _ V A hVe hAe hrank hTIV hTIA hne hcross hU
  have hb := burnsideI62_base hVe hAe hTIV hTIA hne hcross
  have hcard : Nat.card V = Nat.card A := by
    rw [burnsideI62_card_eq_two_pow hVe, burnsideI62_card_eq_two_pow hAe, hrank]
  refine ⟨burnsideI62_part1 hb hcard, fun hlt => ?_⟩
  have hH := burnsideI62_hyp hb hcard hcross hU hlt
  refine ⟨burnsideI62_part2a hH, ?_⟩
  intro hN
  obtain ⟨hN', hM⟩ := burnsideI62_models hH
  refine ⟨burnsideI62_part2b hH burnsideI62_szRank hM, fun P Q hPQ => ?_,
    burnsideI62_part2c2 hH⟩
  rcases hM with ⟨f, hf, hrel, ⟨e⟩⟩ | ⟨a, ha, hrel, ⟨e⟩⟩ | ⟨m, hm, h3, hrel, ⟨e⟩⟩
  · exact burnsideI62_natural_l2 hH hf hrel e hPQ
  · exact burnsideI62_natural_sz hH CFSG.CGT.PushingUpLit.SolKNA.szFpfSimpleNatural_of_certificate
      ha e (burnsideI62_sz_pair hH ha e) hPQ
  · exact burnsideI62_natural_dihedral hH hm h3 e hPQ

end

end CFSG.ASVolI
