module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellThompson

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_centralizer_of_le_normalizer {A B : Subgroup G}
    (h : A ≤ normalizer (B : Set G)) : A ≤ normalizer (centralizer (B : Set G) : Set G) := by
  have key : ∀ a ∈ A, ∀ x ∈ centralizer (B : Set G),
      a * x * a⁻¹ ∈ centralizer (B : Set G) := by
    intro a ha x hx
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : a⁻¹ * w * a ∈ B := by
      simpa using (Subgroup.mem_normalizer_iff.1 (h (A.inv_mem ha)) w).1 hw
    have hc := Subgroup.mem_centralizer_iff.1 hx _ hw'
    calc w * (a * x * a⁻¹) = a * ((a⁻¹ * w * a) * x) * a⁻¹ := by group
      _ = a * (x * (a⁻¹ * w * a)) * a⁻¹ := by rw [hc]
      _ = a * x * a⁻¹ * w := by group
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key a ha x, fun hx => ?_⟩
  simpa [mul_assoc] using key a⁻¹ (A.inv_mem ha) _ hx

theorem conj_mem_elemCenterIn_of_mem_normalizer (p : ℕ) [Fact p.Prime] {T : Subgroup G} {g : G}
    (hg : g ∈ normalizer (T : Set G)) {z : G} (hz : z ∈ elemCenterIn p T) :
    g * z * g⁻¹ ∈ elemCenterIn p T := by
  obtain ⟨e, he, rfl⟩ := hz
  let φ : MulAut T := Subgroup.normalizerMonoidHom T ⟨g, hg⟩
  have hφ : φ e ∈ elemThompsonCenterTorsion T p :=
    Subgroup.characteristic_iff_le_comap.mp (elemThompsonCenterTorsion_characteristic T p) φ he
  exact ⟨φ e, hφ, rfl⟩

theorem normalizer_le_normalizer_elemCenterIn (p : ℕ) [Fact p.Prime] (T : Subgroup G) :
    normalizer (T : Set G) ≤ normalizer (elemCenterIn p T : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_elemCenterIn_of_mem_normalizer p hg, fun hx => ?_⟩
  have := conj_mem_elemCenterIn_of_mem_normalizer p (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem exists_mem_elemFamilyIn (p : ℕ) [Fact p.Prime] (T : Subgroup G) :
    ∃ A : Subgroup G, A ∈ elemFamilyIn p T := by
  obtain ⟨A, hA, hc⟩ := exists_card_eq_pow_pRank T p
  exact ⟨A.map T.subtype, ⟨A, ⟨hA, hc⟩, rfl⟩⟩

theorem elemCenterIn_eq_of_forall_le (p : ℕ) [Fact p.Prime] {Q T : Subgroup G} (hQT : Q ≤ T)
    (h : ∀ A ∈ elemFamilyIn p T, A ≤ Q) : elemCenterIn p Q = elemCenterIn p T := by
  obtain ⟨A₀, hA₀⟩ := exists_mem_elemFamilyIn p T
  obtain ⟨-, hA₀e, hA₀c⟩ := mem_elemFamilyIn.1 hA₀
  have hrk : pRank p Q = pRank p T :=
    le_antisymm (pRank_mono hQT) (pRank_le_of_card_le (h A₀ hA₀) hA₀e hA₀c)
  have hfam : ∀ A : Subgroup G, A ∈ elemFamilyIn p Q ↔ A ∈ elemFamilyIn p T := by
    intro A
    constructor
    · rintro hA
      obtain ⟨hAQ, hAe, hAc⟩ := mem_elemFamilyIn.1 hA
      exact mem_elemFamilyIn.2 ⟨hAQ.trans hQT, hAe, hrk ▸ hAc⟩
    · intro hA
      obtain ⟨-, hAe, hAc⟩ := mem_elemFamilyIn.1 hA
      exact mem_elemFamilyIn.2 ⟨h A hA, hAe, hrk ▸ hAc⟩
  ext x
  rw [mem_elemCenterIn_iff, mem_elemCenterIn_iff]
  constructor
  · rintro ⟨hxQ, hx⟩
    exact ⟨hQT hxQ, fun A hA => hx A ((hfam A).2 hA)⟩
  · rintro ⟨-, hx⟩
    exact ⟨h A₀ hA₀ (hx A₀ hA₀), fun A hA => hx A ((hfam A).1 hA)⟩

theorem normalizer_le_normalizer_elemCenterIn_of_forall_le (p : ℕ) [Fact p.Prime]
    {Q T : Subgroup G} (hQT : Q ≤ T) (h : ∀ A ∈ elemFamilyIn p T, A ≤ Q) :
    normalizer (T : Set G) ≤ normalizer (elemCenterIn p Q : Set G) := by
  rw [elemCenterIn_eq_of_forall_le p hQT h]
  exact normalizer_le_normalizer_elemCenterIn p T

theorem map_conj_mem_elemFamilyIn (p : ℕ) [Fact p.Prime] {T A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (T : Set G)) (hA : A ∈ elemFamilyIn p T) :
    A.map (MulAut.conj g).toMonoidHom ∈ elemFamilyIn p T := by
  obtain ⟨hAT, hAe, hAc⟩ := mem_elemFamilyIn.1 hA
  refine mem_elemFamilyIn.2 ⟨?_, isElementaryAbelian_map hAe _, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hg a).1 (hAT ha)
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hAc

theorem normalizer_inf_le_normalizer_elemCenterIn_of_family_eq (p : ℕ) [Fact p.Prime]
    {Q T D : Subgroup G} (hfam : elemFamilyIn p T = {D, Q}) :
    normalizer (T : Set G) ⊓ normalizer (D : Set G) ≤ normalizer (elemCenterIn p Q : Set G) := by
  have hQ : Q ∈ elemFamilyIn p T := by
    rw [hfam]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨hQT, hQe, hQc⟩ := mem_elemFamilyIn.1 hQ
  have hrk : pRank p Q = pRank p T :=
    le_antisymm (pRank_mono hQT) (pRank_le_of_card_le le_rfl hQe hQc)
  have hZ : elemCenterIn p Q = Q := by
    ext x
    rw [mem_elemCenterIn_iff]
    refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun A hA => ?_⟩⟩
    obtain ⟨hAQ, -, hAc⟩ := mem_elemFamilyIn.1 hA
    have hcard : Nat.card Q ≤ Nat.card A := by rw [hAc, hrk, ← hQc]
    exact (Subgroup.eq_of_le_of_card_ge hAQ hcard) ▸ hx
  rw [hZ]
  rintro g ⟨hgT, hgD⟩
  have hmap : Q.map (MulAut.conj g).toMonoidHom = Q := by
    have h1 : Q.map (MulAut.conj g).toMonoidHom ∈ elemFamilyIn p T :=
      map_conj_mem_elemFamilyIn p hgT hQ
    rw [hfam] at h1
    rcases h1 with h1 | h1
    · have hD : D.map (MulAut.conj g).toMonoidHom = D := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨d, hd, rfl⟩
          exact (Subgroup.mem_normalizer_iff.1 hgD d).1 hd
        · intro d hd
          refine ⟨g⁻¹ * d * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
          have := (Subgroup.mem_normalizer_iff.1 (inv_mem hgD) d).1 hd
          simpa [mul_assoc] using this
      have hQD : Q = D := Subgroup.map_injective (MulAut.conj g).injective (h1.trans hD.symm)
      exact h1.trans hQD.symm
    · exact h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hmap]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by simpa [MulAut.conj_apply] using hyx
    exact this ▸ hy

end CFSG.LocalAnalysis.WeakClosure81
