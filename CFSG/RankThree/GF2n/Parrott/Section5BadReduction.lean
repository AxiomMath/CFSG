module

public import CFSG.RankThree.GF2n.Parrott.Section5Lemma51
public import CFSG.RankThree.GF2n.Parrott.Section5FusionConj

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

private theorem exists_conj_bad_qH_eq {σ y : G} (hyH : y ∈ H z) (hy : orderOf y = 2)
    (hyz : y ≠ z) (hbad : ∀ c ∈ H z, c * y * c⁻¹ ∉ lemma54T₂ D σ) {a : A45}
    (hc : IsConj (qH (z := z) D ⟨y, hyH⟩) a) :
    ∃ g ∈ H z, ∃ hgy : g * y * g⁻¹ ∈ H z, orderOf (g * y * g⁻¹) = 2 ∧ g * y * g⁻¹ ≠ z ∧
      (∀ c ∈ H z, c * (g * y * g⁻¹) * c⁻¹ ∉ lemma54T₂ D σ) ∧
      qH (z := z) D ⟨g * y * g⁻¹, hgy⟩ = a := by
  obtain ⟨b, hb⟩ := isConj_iff.mp hc
  obtain ⟨g, rfl⟩ := qH_surjective D b
  have hgy : (g : G) * y * (g : G)⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem g.2 hyH) ((H z).inv_mem g.2)
  refine ⟨g, g.2, hgy, ?_, fun heq => hyz ?_, fun c hcH => ?_, ?_⟩
  · rw [← hy]
    exact orderOf_injective (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective y
  · have hgz : (g : G) * z = z * g := mem_centralizer_singleton_iff.mp g.2
    calc y = (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * g := by group
      _ = (g : G)⁻¹ * (z * g) := by rw [heq, mul_assoc]
      _ = z := by rw [← hgz, inv_mul_cancel_left]
  · have hcg := hbad (c * g) ((H z).mul_mem hcH g.2)
    rwa [show c * g * y * (c * g)⁻¹ = c * ((g : G) * y * (g : G)⁻¹) * c⁻¹ by group] at hcg
  · rw [← hb, ← map_inv, ← map_mul, ← map_mul]
    rfl

theorem forall_exists_conj_mem_ne_of_qH_tA_utA (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂)
    (hD : ∀ y (hyH : y ∈ H z), orderOf y = 2 → y ≠ z →
      (∀ c ∈ H z,
        c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
      qH (z := z) D ⟨y, hyH⟩ = tA →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y)
    (hE : ∀ y (hyH : y ∈ H z), orderOf y = 2 → y ≠ z →
      (∀ c ∈ H z,
        c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
      qH (z := z) D ⟨y, hyH⟩ = uA * tA →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y) :
    ∀ y ∈ H z, orderOf y = 2 → y ≠ z →
      (∀ c ∈ H z,
        c * y * c⁻¹ ∉ lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)) →
      ∀ B : Subgroup G, B ≤ H z ⊓ centralizer ({y} : Set G) →
        (∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ b ∈ B, c * b * c⁻¹ ∈ B) →
        IsPGroup 2 B → y ∈ B → z ∉ B →
        Nat.card ↥(J z ⊓ centralizer ({y} : Set G)) ≤ Nat.card B →
        ∃ c ∈ H z, c * y * c⁻¹ ∈ B ∧ c * y * c⁻¹ ≠ y := by
  intro y hyH hy hyz hbad
  rcases isConj_tA_or_utA_of_forall_conj_not_mem_lemma54T₂ D h hIII P hP hσ₂ hq₂ hc₂ hyH hy hyz
    hbad with hc | hc
  · obtain ⟨g, hg, hgy, hord, hne, hbad', hq⟩ := exists_conj_bad_qH_eq D hyH hy hyz hbad hc
    exact forall_exists_conj_mem_ne_of_conj hg (hD _ hgy hord hne hbad' hq)
  · obtain ⟨g, hg, hgy, hord, hne, hbad', hq⟩ := exists_conj_bad_qH_eq D hyH hy hyz hbad hc
    exact forall_exists_conj_mem_ne_of_conj hg (hE _ hgy hord hne hbad' hq)

end CFSG.RankThree.GF2n.Parrott
