module

public import CFSG.Quasithin.Vol2.Ch3Sec3InputsA131
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

abbrev gZero (X T : Subgroup G) (g : G) : Subgroup G :=
  X ⊔ T ⊔ conjByElt g (X ⊔ T)

abbrev plus (I K : Subgroup G) : Subgroup (↥I ⧸ CFSG.pPrimeCore 3 ↥I) :=
  (K.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))

omit [Finite G] in
theorem pCoreOf_conj (g : G) (K : Subgroup G) :
    pCoreOf 2 (conjByElt g K) = conjByElt g (pCoreOf 2 K) :=
  CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj g) K

omit [Finite G] in
theorem pCoreOf_subgroupOf_map {K I : Subgroup G} (hKI : K ≤ I) :
    (pCoreOf 2 (K.subgroupOf I)).map I.subtype = pCoreOf 2 K := by
  let e := Subgroup.subgroupOfEquivOfLe hKI
  have hc : I.subtype.comp (K.subgroupOf I).subtype = K.subtype.comp e.toMonoidHom := by
    ext x
    rfl
  unfold pCoreOf
  rw [Subgroup.map_map, hc, ← Subgroup.map_map, CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e]

omit [Finite G] in
theorem le_normalizer_conjByElt {K L : Subgroup G} {d : G}
    (hL : L ≤ Subgroup.normalizer (K : Set G)) (hd : ∀ t ∈ L, d⁻¹ * t * d ∈ L) :
    L ≤ Subgroup.normalizer (conjByElt d K : Set G) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjByElt, mem_conjByElt]
  have e : d⁻¹ * (t * y * t⁻¹) * d = (d⁻¹ * t * d) * (d⁻¹ * y * d) * (d⁻¹ * t * d)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp (hL (hd t ht)) _

omit [Finite G] in
theorem card_conjByElt (g : G) (K : Subgroup G) : Nat.card ↥(conjByElt g K) = Nat.card ↥K :=
  (Nat.card_congr ((MulAut.conj g).subgroupMap K).toEquiv).symm

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

theorem conj_inv_mem {d : G} (hd : d ∈ D) {t : G} (ht : t ∈ T) : d⁻¹ * t * d ∈ T := by
  have := (Subgroup.mem_normalizer_iff.mp (H.h.DN (D.inv_mem hd)) t).mp ht
  simpa using this

theorem conjByElt_T {g : G} (hg : g ∈ D) : conjByElt g T = T :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.h.DN hg)

theorem conjByElt_sup_eq {g : G} (hg : g ∈ D) : conjByElt g (X ⊔ T) = conjByElt g X ⊔ T := by
  have h1 : conjByElt g (X ⊔ T) = conjByElt g X ⊔ conjByElt g T := Subgroup.map_sup _ _ _
  rw [h1, H.conjByElt_T hg]

theorem T_le_conj {g : G} (hg : g ∈ D) : T ≤ conjByElt g (X ⊔ T) := by
  rw [H.conjByElt_sup_eq hg]
  exact le_sup_right

omit [Finite G] H in
theorem conj_le_B {g : G} (hg : g ∈ D) : conjByElt g (X ⊔ T) ≤ X ⊔ T ⊔ D := by
  intro y hy
  rw [mem_conjByElt] at hy
  have e : y = g * (g⁻¹ * y * g) * g⁻¹ := by group
  rw [e]
  have hgB : g ∈ X ⊔ T ⊔ D := Subgroup.mem_sup_right hg
  exact (X ⊔ T ⊔ D).mul_mem ((X ⊔ T ⊔ D).mul_mem hgB ((le_sup_left : X ⊔ T ≤ X ⊔ T ⊔ D) hy))
    ((X ⊔ T ⊔ D).inv_mem hgB)

omit [Finite G] H in
theorem gZero_le {g : G} (hg : g ∈ D) : gZero X T g ≤ X ⊔ T ⊔ D :=
  sup_le le_sup_left (conj_le_B hg)

theorem T_le_normalizer_conj {K : Subgroup G} (hK : T ≤ Subgroup.normalizer (K : Set G))
    {d : G} (hd : d ∈ D) : T ≤ Subgroup.normalizer (conjByElt d K : Set G) :=
  le_normalizer_conjByElt hK fun _ ht => H.conj_inv_mem hd ht

theorem mem_normalizer_of_le {g : G} (hg : g ∈ D) (hle : X ≤ conjByElt g X ⊔ T) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  have h1 : X ≤ conjByElt g X :=
    le_of_le_sup_pgroup H.hXX (H.T_le_normalizer_conj H.hTX hg) H.h.sylow.1 hle
  have h2 : X = conjByElt g X := Subgroup.eq_of_le_of_card_ge h1 (card_conjByElt g X).le
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2.symm

theorem inf_conj_eq {g : G} (hg : g ∈ D) (hgX : g ∉ Subgroup.normalizer (X : Set G)) :
    (X ⊔ T) ⊓ conjByElt g (X ⊔ T) = T := by
  obtain ⟨e⟩ := H.hS3
  have hidx := Lem3320.relIndex_eq_three_of_iso H.isSylowTwoOf_XT e
  have hTK : T ≤ (X ⊔ T) ⊓ conjByElt g (X ⊔ T) := le_inf le_sup_right (H.T_le_conj hg)
  have h1 := Subgroup.relIndex_mul_relIndex T _ (X ⊔ T) hTK inf_le_left
  rw [hidx] at h1
  rcases (Nat.dvd_prime Nat.prime_three).mp (Dvd.intro _ h1) with h | h
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h) hTK
  · exfalso
    rw [h] at h1
    have h2 : ((X ⊔ T) ⊓ conjByElt g (X ⊔ T)).relIndex (X ⊔ T) = 1 := by omega
    have h3 := Subgroup.relIndex_eq_one.mp h2
    apply hgX
    refine H.mem_normalizer_of_le hg ?_
    rw [← H.conjByElt_sup_eq hg]
    exact le_sup_left.trans (h3.trans inf_le_right)

theorem isoS3_open : Nonempty (↥(X ⊔ T) ⧸ Open.pCore 2 ↥(X ⊔ T) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := H.hS3
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2).symm).trans e⟩

theorem isoS3_conj (g : G) :
    Nonempty (↥(conjByElt g (X ⊔ T)) ⧸ Open.pCore 2 ↥(conjByElt g (X ⊔ T)) ≃*
      Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := H.isoS3_open
  let ψ : ↥(X ⊔ T) ≃* ↥(conjByElt g (X ⊔ T)) :=
    Subgroup.equivMapOfInjective (X ⊔ T) (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine gold_isoS3_of_surjective_kernel ψ.toMonoidHom ψ.surjective ?_ e
  rw [(MonoidHom.ker_eq_bot_iff _).mpr ψ.injective]
  exact IsPGroup.of_bot

theorem isSylowTwoOf_gZero (g : G) : IsSylowTwoOf T (gZero X T g) := by
  have hTI : T ≤ gZero X T g := le_sup_right.trans le_sup_left
  exact ⟨hTI, H.h.sylow.1, fun h2 => H.h.sylow.2
    (h2.trans (Subgroup.relIndex_dvd_index_of_le hTI))⟩

theorem isGoldschmidtTripleIn {g : G} (hg : g ∈ D)
    (hgX : g ∉ Subgroup.normalizer (X : Set G)) :
    F6.IsGoldschmidtTripleIn (gZero X T g) (X ⊔ T) (conjByElt g (X ⊔ T)) := by
  refine ⟨rfl, H.isoS3_open, H.isoS3_conj g, ?_⟩
  rw [H.inf_conj_eq hg hgX]
  exact H.isSylowTwoOf_gZero g

theorem isSQTKCat_B : CFSG.SectionRank.IsSQTKCat ↥(X ⊔ T ⊔ D) := by
  have := H.h.simple
  exact (qtkeCore_of_cat H.h.nonabelian H.h.qtke).1 _ H.hB.2

theorem isSQTKCat_gZero {g : G} (hg : g ∈ D) : CFSG.SectionRank.IsSQTKCat ↥(gZero X T g) := by
  have h1 := H.isSQTKCat_B.subgroup ((gZero X T g).subgroupOf (X ⊔ T ⊔ D))
  let e := Subgroup.subgroupOfEquivOfLe (gZero_le (X := X) (T := T) hg)
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm h1.1, h1.2.of_mulEquiv e.symm⟩

theorem not_mem_normalizer_X {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    g ∉ Subgroup.normalizer (X : Set G) := by
  intro hgX
  apply hgR
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hgX ⊢
  have h1 : conjByElt g (X ⊔ T) = X ⊔ T := by
    rw [H.conjByElt_sup_eq hg]
    exact congrArg (· ⊔ T) hgX
  have h2 := pCoreOf_conj g (X ⊔ T)
  rw [h1] at h2
  exact h2.symm

theorem f618 (hF : F6.TheoremF618Cat) {g : G} (hg : g ∈ D)
    (hgR : g ∉ Subgroup.normalizer (pCoreOf 2 (X ⊔ T) : Set G)) :
    plus (gZero X T g) (X ⊔ T) ⊓ plus (gZero X T g) (conjByElt g (X ⊔ T)) =
        ((X ⊔ T).subgroupOf (gZero X T g) ⊓ (conjByElt g (X ⊔ T)).subgroupOf (gZero X T g)).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(gZero X T g))) ∧
      IsGoldschmidtAmalgam (plus (gZero X T g) (X ⊔ T))
        (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∧
      F6.IsAmalgamIso (((X ⊔ T).subgroupOf (gZero X T g)).map
          (QuotientGroup.mk' (Open.pCore 2 ↥(gZero X T g))))
        (((conjByElt g (X ⊔ T)).subgroupOf (gZero X T g)).map
          (QuotientGroup.mk' (Open.pCore 2 ↥(gZero X T g))))
        (plus (gZero X T g) (X ⊔ T)) (plus (gZero X T g) (conjByElt g (X ⊔ T))) ∧
      F6.F618ConclusionCat (plus (gZero X T g) (X ⊔ T))
        (plus (gZero X T g) (conjByElt g (X ⊔ T))) := by
  have hgX := H.not_mem_normalizer_X hg hgR
  have hSQ := H.isSQTKCat_gZero hg
  rcases (H.isGoldschmidtTripleIn hg hgX).f6_18Cat hF
      (CFSG.SectionRank.isStronglyQuasithin_iff.mp hSQ.1) hSQ.2 with h | ⟨h₁, h₂, -⟩
  · exact h
  · exfalso
    apply hgR
    have e1 := pCoreOf_subgroupOf_map (le_sup_left : X ⊔ T ≤ gZero X T g)
    have e2 := pCoreOf_subgroupOf_map (le_sup_right : conjByElt g (X ⊔ T) ≤ gZero X T g)
    rw [h₁] at e1
    rw [h₂, pCoreOf_conj] at e2
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact e2.symm.trans e1

end Hyp3320

end S3320

end CFSG.Quasithin.H13
