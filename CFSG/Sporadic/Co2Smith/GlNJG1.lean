module

public import CFSG.Sporadic.Co2Smith.GlC0Fusion
public import CFSG.Sporadic.Co2Smith.GlNJKPerm

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.RankThree.Co2 CFSG.Certificates

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section G

variable
  {G : Type} [Group G] {z : G} (φ : centralizer ({z} : Set G) ≃* Cz)

@[expose] noncomputable def JGc : Subgroup G := (Jc.subgroupOf Cz).map (phiH φ)

theorem mem_JGc {x : G} : x ∈ JGc φ ↔ ∃ y : Cz, (y : K) ∈ Jc ∧ phiH φ y = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem JGc_le_H : JGc φ ≤ centralizer ({z} : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  exact (φ.symm y).2

@[expose] noncomputable def omCz (k : Fin 77) : Cz := ⟨omK k, Jc_le_Cz (omK_mem_Jc k)⟩

@[expose] noncomputable def omG (k : Fin 77) : G := phiH φ (omCz k)

theorem omCz_injective : Function.Injective omCz := fun _ _ h =>
  omK_injective (congrArg Subtype.val h)

theorem omG_injective : Function.Injective (omG φ) :=
  (phiH_injective φ).comp omCz_injective

theorem omG_mem (k : Fin 77) : omG φ k ∈ JGc φ := (mem_JGc φ).2 ⟨omCz k, omK_mem_Jc k, rfl⟩

theorem omG_zero (hφz : φ (zH z) = z0C) : omG φ 0 = z := by
  have e : omCz 0 = z0C := Subtype.ext omK_zero
  rw [omG, e, phiH_apply, ← hφz, MulEquiv.symm_apply_apply]
  rfl

theorem isConj_z_phiH_iff [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (t : Cz) :
    IsConj z (phiH φ t) ↔ IsConj z0 (t : K) := by
  have := CFSG.Sporadic.Co2.isSimpleGroup_Co2
  have hG := (hypG hz φ).isConj_z_iff (φ.symm t)
  have hK : IsConj z0 (t : K) ↔ hypK.φ (toHK t) = rCr ∨ IsConj (hypK.φ (toHK t)) (rep 2) ∨
      IsConj (hypK.φ (toHK t)) (rep 7) := hypK.isConj_z_iff (toHK t)
  rw [hypG_φ, MulEquiv.apply_symm_apply] at hG
  rw [phiH_apply]
  exact hG.trans hK.symm

theorem isConj_z_omG [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (k : Fin 77) :
    IsConj z (omG φ k) := by
  rw [omG, isConj_z_phiH_iff φ hz]
  show IsConj z0 (omK k)
  rw [← omK_conj_z0 k]
  exact isConj_iff.2 ⟨_, rfl⟩

theorem stableG [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) :
    ∀ g ∈ normalizer (JGc φ : Set G), ConjStable (omG φ) g := by
  intro g hg k
  have hmem : g * omG φ k * g⁻¹ ∈ JGc φ := (mem_normalizer_iff.1 hg _).1 (omG_mem φ k)
  obtain ⟨y, hy, hye⟩ := (mem_JGc φ).1 hmem
  have hc : IsConj z (phiH φ y) := by
    rw [hye]
    exact (isConj_z_omG φ hz k).trans (isConj_iff.2 ⟨g, rfl⟩)
  obtain ⟨k', hk'⟩ := exists_omK_of_isConj hy ((isConj_z_phiH_iff φ hz y).1 hc)
  refine ⟨k', ?_⟩
  rw [← hye, omG]
  exact congrArg (phiH φ) (Subtype.ext hk'.symm)

@[expose] noncomputable def piG [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) :
    normalizer (JGc φ : Set G) →* Equiv.Perm (Fin 77) :=
  chom (omG_injective φ) _ (stableG φ hz)

theorem piG_spec [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (g : normalizer (JGc φ : Set G)) (k : Fin 77) :
    omG φ (piG φ hz g k) = g * omG φ k * (g : G)⁻¹ :=
  chom_spec (omG_injective φ) _ (stableG φ hz) g k

theorem adj_omG_iff (a b : Fin 77) : adj (omG φ) a b ↔ adj omK a b := by
  have h1 : omG φ = phiH φ ∘ omCz := rfl
  have h2 : omK = Cz.subtype ∘ omCz := rfl
  rw [h1, adj_map _ (phiH_injective φ), h2, adj_map _ Subtype.val_injective]

theorem piG_mem_njAut [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (g : normalizer (JGc φ : Set G)) : piG φ hz g ∈ njAut := by
  intro x y
  rw [mem_glNJNbr_iff, mem_glNJNbr_iff, ← adj_omG_iff φ, ← adj_omG_iff φ, piG,
    adj_chom (omG_injective φ) _ (stableG φ hz) g]

theorem phiH_mem_NG {y : Cz} (hy : (y : K) ∈ normalizer (Jc : Set K)) :
    phiH φ y ∈ normalizer (JGc φ : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨y * w * y⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact (mem_normalizer_iff.1 hy _).1 hw
  · intro hx
    obtain ⟨w, hw, hwe⟩ := (mem_JGc φ).1 hx
    refine (mem_JGc φ).2 ⟨y⁻¹ * w * y, ?_, ?_⟩
    · have hy' := inv_mem hy
      have := (mem_normalizer_iff.1 hy' _).1 hw
      simpa using this
    · simp only [map_mul, map_inv, hwe]
      group

theorem piG_phiH [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2) (y : Cz)
    (hy : (y : K) ∈ normalizer (Jc : Set K)) :
    piG φ hz ⟨phiH φ y, phiH_mem_NG φ hy⟩ = piK ⟨y, hy⟩ := by
  refine chom_eq_of_spec (omG_injective φ) _ (stableG φ hz) _ _ fun k => ?_
  have e : omCz (piK ⟨y, hy⟩ k) = y * omCz k * y⁻¹ := Subtype.ext (piK_spec ⟨y, hy⟩ k)
  rw [omG, e, map_mul, map_mul, map_inv]
  rfl

theorem mem_JGc_of_piG_eq_one [Finite G] [IsSimpleGroup G] (hz : orderOf z = 2)
    (hφz : φ (zH z) = z0C) {g : normalizer (JGc φ : Set G)} (h : piG φ hz g = 1) :
    (g : G) ∈ JGc φ := by
  have hc := (chom_eq_one_iff (omG_injective φ) _ (stableG φ hz) g).1 h
  have hgH : (g : G) ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e := hc 0
    rw [omG_zero φ hφz] at e
    exact e
  have hck : ∀ k, (φ ⟨g, hgH⟩ : K) * omK k = omK k * φ ⟨g, hgH⟩ := by
    intro k
    have e := hc k
    have e' : phiH φ (φ ⟨g, hgH⟩ * omCz k) = phiH φ (omCz k * φ ⟨g, hgH⟩) := by
      rw [map_mul, map_mul, phiH_apply_symm]
      exact e
    exact congrArg Subtype.val (phiH_injective φ e')
  have hcJ : (φ ⟨g, hgH⟩ : K) ∈ Jc := by
    apply centralizer_Jc_le
    have h1 : (φ ⟨g, hgH⟩ : K) ∈ centralizer (Set.range omK) := by
      refine mem_centralizer_iff.2 ?_
      rintro _ ⟨k, rfl⟩
      exact (hck k).symm
    rw [← centralizer_closure] at h1
    exact centralizer_le Jc_le_closure_omK h1
  exact (mem_JGc φ).2 ⟨_, hcJ, phiH_apply_symm φ g hgH⟩

end G

end CFSG.Sporadic.Co2Smith
