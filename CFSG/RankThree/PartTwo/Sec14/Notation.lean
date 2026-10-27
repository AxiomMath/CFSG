module

public import CFSG.RankThree.PartTwo.Notation
public import CFSG.GH74.GLS.Basic
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree.PartTwo CFSG.GH74.GLS

variable {G : Type*} [Group G]

theorem pPrimeCoreOf_le (p : ℕ) (X : Subgroup G) : pPrimeCoreOf p X ≤ X :=
  Subgroup.map_subtype_le _

theorem normalizer_le_normalizer_pPrimeCoreOf (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (pPrimeCoreOf p X : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pPrimeCore p X)

theorem le_normalizer_pPrimeCoreOf (p : ℕ) (X : Subgroup G) :
    X ≤ Subgroup.normalizer (pPrimeCoreOf p X : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_pPrimeCoreOf p X)

theorem coprime_card_pPrimeCoreOf [Finite G] (p : ℕ) [Fact p.Prime] (X : Subgroup G) :
    Nat.Coprime p (Nat.card (pPrimeCoreOf p X)) := by
  rw [pPrimeCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  exact pPrimeCore_coprime_card

theorem le_pPrimeCoreOf {p : ℕ} {N X : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime p (Nat.card N)) :
    N ≤ pPrimeCoreOf p X := by
  have hnormal : (N.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime p (Nat.card (N.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv]
  have hle : N.subgroupOf X ≤ pPrimeCore p X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hNX]
  exact Subgroup.map_mono hle

theorem map_pPrimeCoreOf {G' : Type*} [Group G'] (p : ℕ) (φ : G ≃* G') (X : Subgroup G) :
    (pPrimeCoreOf p X).map φ.toMonoidHom = pPrimeCoreOf p (X.map φ.toMonoidHom) := by
  unfold pPrimeCoreOf
  let ψ : X ≃* X.map φ.toMonoidHom := φ.subgroupMap X
  rw [← pPrimeCore_map_iso p ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem map_conj_centralizer (S : Subgroup G) (w : G) :
    (Subgroup.centralizer (S : Set G)).map (MulAut.conj w).toMonoidHom =
      Subgroup.centralizer ((S.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  constructor
  · rintro ⟨y, hy, rfl⟩ s hs
    rw [show w * s * w⁻¹ * (w * y * w⁻¹) = w * (s * y) * w⁻¹ by group, hy s hs]
    group
  · intro h
    refine ⟨w⁻¹ * x * w, fun s hs => ?_, by group⟩
    have := h s hs
    calc s * (w⁻¹ * x * w) = w⁻¹ * ((w * s * w⁻¹) * x) * w := by group
      _ = w⁻¹ * (x * (w * s * w⁻¹)) * w := by rw [this]
      _ = w⁻¹ * x * w * s := by group

@[expose] def IsHyperplane (A B : Subgroup G) : Prop :=
  B ≤ A ∧ Nat.card A = 3 * Nat.card B

theorem IsHyperplane.map_conj {A B : Subgroup G} (hB : IsHyperplane A B) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) :
    IsHyperplane A (B.map (MulAut.conj w).toMonoidHom) := by
  have hA : A.map (MulAut.conj w).toMonoidHom = A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hw y).mp hy
    · intro hx
      refine ⟨w⁻¹ * x * w, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hw) x).mp hx
      simpa [mul_assoc] using this
  refine ⟨hA ▸ Subgroup.map_mono hB.1, ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj w).injective]
  exact hB.2

@[expose] def IsNaturalFamily (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ∀ w ∈ Subgroup.normalizer (A : Set G), ∀ B, IsHyperplane A B →
    (LB B).map (MulAut.conj w).toMonoidHom = LB (B.map (MulAut.conj w).toMonoidHom)

@[expose] def qBound (A : Subgroup G) (LB : Subgroup G → Subgroup G) (B : Subgroup G) :
    Subgroup G :=
  pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
    pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ LB B

@[expose] def scriptQ (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Q | Q ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧
    ∀ B, IsHyperplane A B → Q ⊓ Subgroup.centralizer (B : Set G) ≤ qBound A LB B}

@[expose] def scriptQZero (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Q | Q ∈ scriptQ A LB ∧ Q = ⁅Q, A⁆}

theorem mem_scriptQ_iff {A Q : Subgroup G} {LB : Subgroup G → Subgroup G} :
    Q ∈ scriptQ A LB ↔ IsPiSubgroup (piCompl 3) Q ∧ A ≤ Subgroup.normalizer (Q : Set G) ∧
      ∀ B, IsHyperplane A B → Q ⊓ Subgroup.centralizer (B : Set G) ≤ qBound A LB B :=
  ⟨fun h => ⟨h.1.2.1, h.1.2.2, h.2⟩, fun h => ⟨⟨le_top, h.1, h.2.1⟩, h.2.2⟩⟩

theorem mem_scriptQ_of_le {A Q R : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hQ : Q ∈ scriptQ A LB) (hRQ : R ≤ Q) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    R ∈ scriptQ A LB := by
  refine ⟨⟨le_top, fun q hq => hQ.1.2.1 q (hq.trans (Subgroup.card_dvd_of_le hRQ)), hAR⟩,
    fun B hB => (inf_le_inf_right _ hRQ).trans (hQ.2 B hB)⟩

@[expose] def scriptY (A : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ≠ ⊤ ∧ A ≤ Subgroup.normalizer (Y : Set G)}

@[expose] noncomputable def delta (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (Y : Subgroup G) : Subgroup G :=
  sSup (collectionIn (scriptQ A LB) Y)

@[expose] noncomputable def deltaZero (A : Subgroup G) (LB : Subgroup G → Subgroup G)
    (Y : Subgroup G) : Subgroup G :=
  sSup (collectionIn (scriptQZero A LB) Y)

@[expose] def scriptY2 (A : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY A ∧ CFSG.Open.pCoreOf 2 Y ≠ ⊥}

@[expose] def scriptY3 (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ scriptY2 A ∧ Y = delta A LB Y}

@[expose] def scriptQPi (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G)
    (π : Set Nat.Primes) : Set (Subgroup G) :=
  {Q | Q ∈ collectionIn (scriptQ A LB) Y ∧ IsPiSubgroup π Q}

@[expose] def scriptQPiStar (A : Subgroup G) (LB : Subgroup G → Subgroup G) (Y : Subgroup G)
    (π : Set Nat.Primes) : Set (Subgroup G) :=
  {Q | Maximal (· ∈ scriptQPi A LB Y π) Q}

section Delta

variable {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem le_delta {Q Y : Subgroup G} (hQ : Q ∈ scriptQ A LB) (hQY : Q ≤ Y) :
    Q ≤ delta A LB Y :=
  le_sSup ⟨hQ, hQY⟩

theorem le_deltaZero {Q Y : Subgroup G} (hQ : Q ∈ scriptQZero A LB) (hQY : Q ≤ Y) :
    Q ≤ deltaZero A LB Y :=
  le_sSup ⟨hQ, hQY⟩

theorem delta_le (Y : Subgroup G) : delta A LB Y ≤ Y :=
  sSup_le fun _ hQ => hQ.2

theorem deltaZero_le_delta (Y : Subgroup G) : deltaZero A LB Y ≤ delta A LB Y :=
  sSup_le fun _ hQ => le_delta hQ.1.1 hQ.2

theorem deltaZero_le (Y : Subgroup G) : deltaZero A LB Y ≤ Y :=
  (deltaZero_le_delta Y).trans (delta_le Y)

end Delta

end CFSG.RankThree.PartTwo.Sec14
