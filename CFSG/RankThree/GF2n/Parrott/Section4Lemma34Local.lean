module

public import CFSG.RankThree.GF2n.Parrott.Section4Defs
public import CFSG.RankThree.GF2n.Parrott.QuadraticV

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Basic

omit [Finite G] in
theorem lemma34_exists_mul_of_mem_sup {A E : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ A ⊔ E) :
    ∃ a ∈ A, ∃ e ∈ E, x = a * e := by
  have hEN : E ≤ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer
  have hxN : x ∈ Subgroup.normalizer (E : Set G) := sup_le hA hEN hx
  have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (E : Set G))) ∈
      A.subgroupOf (Subgroup.normalizer (E : Set G)) ⊔
        E.subgroupOf (Subgroup.normalizer (E : Set G)) := by
    rw [← Subgroup.subgroupOf_sup hA hEN]
    exact hx
  obtain ⟨a, ha, e, he, hae⟩ := Subgroup.mem_sup_of_normal_right.mp h1
  exact ⟨(a : G), ha, (e : G), he, (congrArg Subtype.val hae).symm⟩

omit [Finite G] in
theorem lemma34_eq_one_or_eq_of_mem_zpowers {x : G} (hz : orderOf z = 2)
    (hx : x ∈ Subgroup.zpowers z) : x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hk' : z ^ (k % 2) = z ^ k := by
    have := zpow_mod_orderOf z k
    rwa [hz] at this
  have hmod : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · left
    rw [← hk', h0, zpow_zero]
  · right
    rw [← hk', h1, zpow_one]

theorem lemma34_conj_mem_J {g j : G} (hg : g ∈ H z) (hj : j ∈ J z) : g * j * g⁻¹ ∈ J z :=
  Subgroup.mem_subgroupOf.mp ((J_subgroupOf_normal z).conj_mem ⟨j, J_le_H hj⟩
    (Subgroup.mem_subgroupOf.mpr hj) ⟨g, hg⟩)

theorem lemma34_mem_normalizer_conj_iff {A : Type*} [Group A] {Ebar S : Subgroup A} {c a : A}
    (hS : ∀ s, s ∈ S ↔ c⁻¹ * s * c ∈ Ebar) :
    a ∈ Subgroup.normalizer (Ebar : Set A) ↔ c * a * c⁻¹ ∈ Subgroup.normalizer (S : Set A) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro ha k
    rw [hS k, hS ((c * a * c⁻¹) * k * (c * a * c⁻¹)⁻¹)]
    have e : c⁻¹ * ((c * a * c⁻¹) * k * (c * a * c⁻¹)⁻¹) * c = a * (c⁻¹ * k * c) * a⁻¹ := by
      group
    rw [e]
    exact ha (c⁻¹ * k * c)
  · intro ha k
    have := ha (c * k * c⁻¹)
    rw [hS (c * k * c⁻¹), hS ((c * a * c⁻¹) * (c * k * c⁻¹) * (c * a * c⁻¹)⁻¹)] at this
    have e1 : c⁻¹ * (c * k * c⁻¹) * c = k := by group
    have e2 : c⁻¹ * ((c * a * c⁻¹) * (c * k * c⁻¹) * (c * a * c⁻¹)⁻¹) * c = a * k * a⁻¹ := by
      group
    rwa [e1, e2] at this

end Basic

section Obligations

theorem J_le_normalizer_of_isParrottE (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) : J z ≤ Subgroup.normalizer (E : Set G) := by
  obtain ⟨hEH, -, hZE, hEab, -, -, hEC, -⟩ := hE
  have hzJ : z ∈ J z := z_mem_J h
  have hzE : z ∈ E := hZE ⟨hzJ, z_centralizes_J h⟩
  have hzF : Subgroup.zpowers z ≤ E ⊓ J z := Subgroup.zpowers_le.mpr ⟨hzE, hzJ⟩
  have key : ∀ j ∈ J z, ∀ f ∈ E ⊓ J z, j * f * j⁻¹ ∈ E ⊓ J z := by
    intro j hj f hf
    have hjf : ⁅j, f⁆ ∈ Subgroup.zpowers z := commutator_mem_zpowers_z h hj hf.2
    have h1 : j * f * j⁻¹ = ⁅j, f⁆ * f := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact (E ⊓ J z).mul_mem (hzF hjf) hf
  have hcent : ∀ e ∈ E, ∀ f ∈ E ⊓ J z, f * e = e * f := by
    intro e he f hf
    have : e ∈ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) := by
      rw [hEC] at he
      exact he.2
    exact Subgroup.mem_centralizer_iff.mp this f hf
  rw [Subgroup.le_set_normalizer_iff]
  intro j hj e he
  have hjH : j ∈ H z := J_le_H hj
  have heH : e ∈ H z := hEH he
  rw [SetLike.mem_coe, hEC]
  refine ⟨(H z).mul_mem ((H z).mul_mem hjH heH) ((H z).inv_mem hjH), ?_⟩
  show j * e * j⁻¹ ∈ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  have h1 := hcent e he (j⁻¹ * f * j) (by
    have := key j⁻¹ ((J z).inv_mem hj) f hf
    simpa using this)
  show f * (j * e * j⁻¹) = j * e * j⁻¹ * f
  calc f * (j * e * j⁻¹) = j * ((j⁻¹ * f * j) * e) * j⁻¹ := by group
    _ = j * (e * (j⁻¹ * f * j)) * j⁻¹ := by rw [h1]
    _ = j * e * j⁻¹ * f := by group


theorem relIndex_sup_J_of_isParrottE (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) : E.relIndex (J z ⊔ E) = 16 := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  obtain ⟨-, -, -, -, -, hFcard, -, -⟩ := hE
  have hEN : E ≤ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer
  have hKN : J z ⊔ E ≤ Subgroup.normalizer (E : Set G) := sup_le hJN hEN
  rw [← Subgroup.relIndex_subgroupOf hKN, Subgroup.subgroupOf_sup hJN hEN,
    Subgroup.relIndex_sup_right, Subgroup.relIndex_subgroupOf hJN]
  have h1 := Subgroup.relIndex_mul_card E (J z)
  rw [hFcard, card_J h] at h1
  omega

theorem commutator_mem_of_mem_J_sup (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) {r s : G} (hr : r ∈ J z ⊔ E) (hs : s ∈ J z ⊔ E) : ⁅r, s⁆ ∈ E := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  have hzE : z ∈ E := hE.2.2.1 ⟨z_mem_J h, z_centralizes_J h⟩
  have hconj : ∀ j ∈ J z, ∀ e ∈ E, j * e * j⁻¹ ∈ E := fun j hj e he =>
    (Subgroup.mem_normalizer_iff.mp (hJN hj) e).mp he
  have hconj' : ∀ j ∈ J z, ∀ e ∈ E, j⁻¹ * e * j ∈ E := fun j hj e he => by
    simpa using hconj j⁻¹ ((J z).inv_mem hj) e he
  obtain ⟨j, hj, e, he, rfl⟩ := lemma34_exists_mul_of_mem_sup hJN hr
  obtain ⟨j', hj', e', he', rfl⟩ := lemma34_exists_mul_of_mem_sup hJN hs
  have hX : (j'⁻¹ * e * j') * e' * ((j⁻¹ * e' * j) * e)⁻¹ ∈ E :=
    E.mul_mem (E.mul_mem (hconj' j' hj' e he) he')
      (E.inv_mem (E.mul_mem (hconj' j hj e' he') he))
  have hjj : ⁅j, j'⁆ ∈ E := Subgroup.zpowers_le.mpr hzE (commutator_mem_zpowers_z h hj hj')
  have hid : ⁅j * e, j' * e'⁆ =
      ((j * j') * ((j'⁻¹ * e * j') * e' * ((j⁻¹ * e' * j) * e)⁻¹) * (j * j')⁻¹) * ⁅j, j'⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hid]
  exact E.mul_mem (hconj (j * j') ((J z).mul_mem hj hj') _ hX) hjj

theorem mul_self_mem_of_mem_J_sup (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) {r : G} (hr : r ∈ J z ⊔ E) : r * r ∈ E := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  have hzE : z ∈ E := hE.2.2.1 ⟨z_mem_J h, z_centralizes_J h⟩
  have hconj' : ∀ j ∈ J z, ∀ e ∈ E, j⁻¹ * e * j ∈ E := fun j hj e he => by
    simpa using (Subgroup.mem_normalizer_iff.mp (hJN ((J z).inv_mem hj)) e).mp he
  obtain ⟨j, hj, e, he, rfl⟩ := lemma34_exists_mul_of_mem_sup hJN hr
  have hjj : j * j ∈ E := Subgroup.zpowers_le.mpr hzE (sq_mem_zpowers_z h hj)
  have hid : j * e * (j * e) = (j * j) * ((j⁻¹ * e * j) * e) := by group
  rw [hid]
  exact E.mul_mem hjj (E.mul_mem (hconj' j hj e he) he)

theorem exists_commutator_eq_z (h : Tim79a.ParrottHyp z) {E : Subgroup G} (hE : IsParrottE z E)
    {r : G} (hr : r ∈ J z ⊔ E) (hrE : r ∉ E) : ∃ e ∈ E, ⁅r, e⁆ = z := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  obtain ⟨j, hj, e', he', rfl⟩ := lemma34_exists_mul_of_mem_sup hJN hr
  obtain ⟨hEH, -, hZE, hEab, -, -, hEC, -⟩ := hE
  have hjE : j ∉ E := fun hjE => hrE (E.mul_mem hjE he')
  have hjC : j ∉ Subgroup.centralizer ((E ⊓ J z : Subgroup G) : Set G) := fun hC =>
    hjE (by rw [hEC]; exact ⟨J_le_H hj, hC⟩)
  rw [Subgroup.mem_centralizer_iff] at hjC
  push Not at hjC
  obtain ⟨f, hf, hfj⟩ := hjC
  refine ⟨f, hf.1, ?_⟩
  have hne1 : ⁅j, f⁆ ≠ 1 := fun h1 => hfj (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  have hjf : ⁅j, f⁆ = z := by
    rcases lemma34_eq_one_or_eq_of_mem_zpowers h.1 (commutator_mem_zpowers_z h hj hf.2) with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have he'f : e' * f = f * e' :=
    Subtype.ext_iff.mp (hEab.1.is_comm.comm (⟨e', he'⟩ : E) ⟨f, hf.1⟩)
  have h1 : e' * f * e'⁻¹ = f := by rw [he'f]; group
  calc ⁅j * e', f⁆ = j * (e' * f * e'⁻¹) * j⁻¹ * f⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ⁅j, f⁆ := by rw [h1]; simp only [commutatorElement_def]
    _ = z := hjf

theorem commutator_eq_z_of_isConj (h : Tim79a.ParrottHyp z) {E : Subgroup G}
    (hE : IsParrottE z E) (hJ : ∀ j ∈ J z, j ∉ Subgroup.zpowers z → ¬ IsConj z j)
    {r e : G} (hr : r ∈ J z ⊔ E) (he : e ∈ E) (hc : IsConj z ⁅r, e⁆) : ⁅r, e⁆ = z := by
  have hJN := J_le_normalizer_of_isParrottE h hE
  obtain ⟨j, hj, e', he', rfl⟩ := lemma34_exists_mul_of_mem_sup hJN hr
  have hEH : E ≤ H z := hE.1
  have hEab := hE.2.2.2.1
  have he'e : e' * e = e * e' :=
    Subtype.ext_iff.mp (hEab.1.is_comm.comm (⟨e', he'⟩ : E) ⟨e, he⟩)
  have h1 : e' * e * e'⁻¹ = e := by rw [he'e]; group
  have h2 : ⁅j * e', e⁆ = ⁅j, e⁆ := by
    calc ⁅j * e', e⁆ = j * (e' * e * e'⁻¹) * j⁻¹ * e⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅j, e⁆ := by rw [h1]; simp only [commutatorElement_def]
  have hJmem : ⁅j, e⁆ ∈ J z := by
    have h3 : ⁅j, e⁆ = j * (e * j⁻¹ * e⁻¹) := by simp only [commutatorElement_def]; group
    rw [h3]
    exact (J z).mul_mem hj (lemma34_conj_mem_J (hEH he) ((J z).inv_mem hj))
  rw [h2] at hc ⊢
  by_contra hne
  have hnot : ⁅j, e⁆ ∉ Subgroup.zpowers z := by
    intro hmem
    rcases lemma34_eq_one_or_eq_of_mem_zpowers h.1 hmem with h1 | h1
    · rw [h1] at hc
      have := isConj_one_left.mp hc
      rw [this] at h
      exact absurd h.1 (by simp)
    · exact hne h1
  exact hJ _ hJmem hnot hc

end Obligations

omit [Finite G] in
theorem lemma34_eq_one_of_mem_of_card {K : Subgroup G} (hK : Nat.card K = 2 ^ 10)
    {x : G} (hx : x ∈ K) {p : ℕ} (hp : Nat.Coprime p (2 ^ 10)) (hxp : x ^ p = 1) : x = 1 := by
  have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have h2 : orderOf x ∣ 2 ^ 10 := by
    rw [← Subgroup.orderOf_mk x hx]
    exact hK ▸ orderOf_dvd_natCard (⟨x, hx⟩ : K)
  have h3 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hp) h2
  exact orderOf_eq_one_iff.mp h3

omit [Finite G] in
theorem lemma34_card_normalizer_inf_H {E : Subgroup G} (hE : IsParrottE z E) :
    Nat.card ↥(Subgroup.normalizer (E : Set G) ⊓ H z) = 2 ^ 17 * 15 := by
  have hEM : E ≤ Subgroup.normalizer (E : Set G) ⊓ H z := le_inf Subgroup.le_normalizer hE.1
  have h1 := Subgroup.relIndex_mul_card E (Subgroup.normalizer (E : Set G) ⊓ H z)
  rw [inf_eq_left.mpr hEM] at h1
  have h2 : E.relIndex (Subgroup.normalizer (E : Set G) ⊓ H z) = 1920 := hE.2.2.2.2.2.2.2
  have h3 : Nat.card E = 2 ^ 10 := hE.2.2.2.2.1
  rw [h2, h3] at h1
  omega

end CFSG.RankThree.GF2n.Parrott
