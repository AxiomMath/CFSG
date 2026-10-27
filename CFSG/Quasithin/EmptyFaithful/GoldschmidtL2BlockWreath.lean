module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtL2BlockCarrier
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtMLAMain

public section

namespace CFSG.Quasithin.GoldMLA

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem conjByElt_injective (g : G) {K₁ K₂ : Subgroup G} (h : conjByElt g K₁ = conjByElt g K₂) :
    K₁ = K₂ := by
  have h1 := congrArg (conjByElt g⁻¹) h
  rwa [← conjByElt_mul', ← conjByElt_mul', inv_mul_cancel, conjByElt_one', conjByElt_one'] at h1

theorem conj_le_normalizer_of_orbits {X S L : Subgroup G} {t : G} (hLX : L ≤ X) (htX : t ∈ X)
    (horb : conjSubgroupsBy X L = conjSubgroupsBy S L)
    (hconj : conjSubgroupsBy S L = {L, conjByElt t L})
    (htN : t ∉ Subgroup.normalizer (L : Set G)) :
    conjByElt t L ≤ Subgroup.normalizer (L : Set G) := by
  intro x hx
  have hxX : x ∈ X := by
    have h1 : t⁻¹ * x * t ∈ X := hLX (mem_conjByElt.mp hx)
    have := X.mul_mem (X.mul_mem htX h1) (X.inv_mem htX)
    simpa [mul_assoc] using this
  have hm : conjByElt x L ∈ conjSubgroupsBy X L := ⟨x, hxX, rfl⟩
  rw [horb, hconj] at hm
  rcases hm with h | h
  · exact mem_normalizer_of_conjByElt_eq h
  · exfalso
    have h2 : conjByElt x (conjByElt t L) = conjByElt t L :=
      conjByElt_eq_of_mem_normalizer (Subgroup.le_normalizer hx)
    have h3 : conjByElt x L = conjByElt x (conjByElt t L) := h.trans h2.symm
    exact htN (mem_normalizer_of_conjByElt_eq (conjByElt_injective x h3).symm)

theorem le_normalizer_conj_of_orbits {X S L : Subgroup G} {t : G} (hLX : L ≤ X) (htX : t ∈ X)
    (horb : conjSubgroupsBy X L = conjSubgroupsBy S L)
    (hconj : conjSubgroupsBy S L = {L, conjByElt t L})
    (htN : t ∉ Subgroup.normalizer (L : Set G)) :
    L ≤ Subgroup.normalizer ((conjByElt t L : Subgroup G) : Set G) := by
  intro y hy
  have hm : conjByElt (y * t) L ∈ conjSubgroupsBy X L := ⟨y * t, X.mul_mem (hLX hy) htX, rfl⟩
  rw [horb, hconj, conjByElt_mul'] at hm
  rcases hm with h | h
  · exfalso
    have h2 : conjByElt y L = L := conjByElt_eq_of_mem_normalizer (Subgroup.le_normalizer hy)
    have h3 : conjByElt y (conjByElt t L) = conjByElt y L := h.trans h2.symm
    exact htN (mem_normalizer_of_conjByElt_eq (conjByElt_injective y h3))
  · exact mem_normalizer_of_conjByElt_eq h

section Finite

variable [Finite G]

theorem inf_pCoreOf_le_pCoreOf {X L : Subgroup G} (hLX : L ≤ X) :
    pCoreOf 2 X ⊓ L ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : L ≤ Subgroup.normalizer ((pCoreOf 2 X ⊓ L : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (le_normalizer_pCoreOf 2 X (hLX hx)) (Subgroup.le_normalizer hx)
  have hp : IsPGroup 2 ↥(pCoreOf 2 X ⊓ L) := (pCoreOf_isPGroup 2 X).to_le inf_le_left
  exact le_pCoreOf_of_le_normalizer 2 inf_le_right hn hp

theorem exists_carrier_conjClosure_mod {X S L P : Subgroup G} (hLX : L ≤ X) (hSX : S ≤ X)
    (hP : IsSylowTwoOf P L) (hPe : P = S ⊓ L) (hB : fusionIsBenderGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (horb : conjSubgroupsBy X L = conjSubgroupsBy S L)
    (hcase : (∀ t ∈ S, t ∈ Subgroup.normalizer (L : Set G)) ∨
      ∃ t ∈ S, t ∉ Subgroup.normalizer (L : Set G) ∧
        conjSubgroupsBy S L = {L, conjByElt t L} ∧ ⁅L, conjByElt t L⁆ ≤ pCoreOf 2 X ∧
        (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) = pCoreOf 2 X) :
    ∃ K Q : Subgroup G,
      conjClosure (L ⊓ Subgroup.normalizer (P : Set G)) S = K ∧ IsCarrier K Q := by
  rcases hcase with hSN | ⟨t, htS, htN, hconj, hcom, hint0⟩
  · exact exists_carrier_conjClosure hLX hP hPe hB (Or.inl hSN)
  set B := L ⊓ Subgroup.normalizer (P : Set G) with hBdef
  have hBc : IsCarrier B P := isCarrier_borel hP hB
  have hsB : ∀ s ∈ S, s ∈ Subgroup.normalizer (L : Set G) →
      s ∈ Subgroup.normalizer (B : Set G) := by
    intro s hs hsL
    have hsP : s ∈ Subgroup.normalizer (P : Set G) := by
      rw [hPe]
      exact mem_normalizer_inf (Subgroup.le_normalizer hs) hsL
    exact mem_normalizer_inf hsL (Subgroup.le_normalizer hsP)
  have htX : t ∈ X := hSX htS
  have hL'N := conj_le_normalizer_of_orbits hLX htX horb hconj htN
  have hLN := le_normalizer_conj_of_orbits hLX htX horb hconj htN
  have hYt : ∀ y ∈ pCoreOf 2 X, t⁻¹ * y * t ∈ pCoreOf 2 X := fun y hy => by
    have := Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (pCoreOf 2 X : Set G)).inv_mem (le_normalizer_pCoreOf 2 X htX)) y
    simpa using this.mp hy
  have hYL : pCoreOf 2 X ⊓ L ≤ P := inf_pCoreOf_le hLX hP
  have hYL' : pCoreOf 2 X ⊓ conjByElt t L ≤ conjByElt t P := fun x hx =>
    mem_conjByElt.mpr (hYL ⟨hYt x hx.1, mem_conjByElt.mp hx.2⟩)
  have hBc' : IsCarrier (conjByElt t B) (conjByElt t P) := hBc.conj t
  have hBL' : conjByElt t B ≤ conjByElt t L := Subgroup.map_mono inf_le_left
  have hc : ∀ x ∈ B, (∀ p ∈ P, x * p * x⁻¹ * p⁻¹ ∈ pCoreOf 2 X) → x ∈ P := by
    intro x hx hxc
    refine mem_of_centralizes_mod hP hB hx.1 fun p hp => ?_
    refine inf_pCoreOf_le_pCoreOf hLX ⟨hxc p hp, ?_⟩
    exact L.mul_mem (L.mul_mem (L.mul_mem hx.1 (hP.1 hp)) (L.inv_mem hx.1)) (L.inv_mem (hP.1 hp))
  have hc' : ∀ x ∈ conjByElt t B, (∀ p ∈ conjByElt t P, x * p * x⁻¹ * p⁻¹ ∈ pCoreOf 2 X) →
      x ∈ conjByElt t P := by
    intro x hx hxc
    refine mem_conjByElt.mpr (hc _ (mem_conjByElt.mp hx) fun p hp => ?_)
    have hp' : t * p * t⁻¹ ∈ conjByElt t P := by
      rw [mem_conjByElt, show t⁻¹ * (t * p * t⁻¹) * t = p by group]
      exact hp
    have h1 := hYt _ (hxc _ hp')
    have e : t⁻¹ * (x * (t * p * t⁻¹) * x⁻¹ * (t * p * t⁻¹)⁻¹) * t =
        (t⁻¹ * x * t) * p * (t⁻¹ * x * t)⁻¹ * p⁻¹ := by group
    rwa [e] at h1
  have hsup : IsCarrier (B ⊔ conjByElt t B) (P ⊔ conjByElt t P) :=
    hBc.sup_mod hBc' inf_le_left hBL' hLN hL'N
      (fun a ha b hb => hcom (Subgroup.commutator_mem_commutator ha hb)) hYL hYL'
      (fun x hx => by
        have h1 : x ∈ (L ⊔ pCoreOf 2 X) ⊓ (conjByElt t L ⊔ pCoreOf 2 X) :=
          ⟨Subgroup.mem_sup_left hx.1, Subgroup.mem_sup_left hx.2⟩
        rwa [hint0] at h1) hc hc'
  refine ⟨_, _, ?_, hsup⟩
  show conjClosure B S = B ⊔ conjByElt t B
  apply le_antisymm
  · refine conjClosure_le fun s hs b hb => ?_
    have hmem : conjByElt s L ∈ conjSubgroupsBy S L := ⟨s, hs, rfl⟩
    rw [hconj] at hmem
    rcases hmem with h1 | h1
    · have hsL := mem_normalizer_of_conjByElt_eq h1
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hsB s hs hsL) b).mp hb)
    · have h1 : conjByElt s L = conjByElt t L := h1
      have hnL : t⁻¹ * s ∈ Subgroup.normalizer (L : Set G) := by
        refine mem_normalizer_of_conjByElt_eq ?_
        rw [conjByElt_mul', h1, ← conjByElt_mul', inv_mul_cancel, conjByElt_one']
      have hnS : t⁻¹ * s ∈ S := S.mul_mem (S.inv_mem htS) hs
      have hb' := (Subgroup.mem_normalizer_iff.mp (hsB _ hnS hnL) b).mp hb
      refine Subgroup.mem_sup_right ?_
      rw [mem_conjByElt]
      have e : t⁻¹ * (s * b * s⁻¹) * t = (t⁻¹ * s) * b * (t⁻¹ * s)⁻¹ := by group
      rw [e]
      exact hb'
  · refine sup_le (le_conjClosure _ _) ?_
    intro x hx
    rw [mem_conjByElt] at hx
    have := mem_conjClosure (Z := B) (H := S) htS hx
    simpa [mul_assoc] using this

end Finite

end CFSG.Quasithin.GoldMLA
