module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.Data.Nat.Prime.Pow

public section

namespace CFSG.StandardType

namespace NoOffE8Five

open scoped Pointwise

lemma le_normalizer_of_normal_subgroupOf_pow {H : Type*} [Group H] {p : ℕ}
    {P Q T X : Subgroup H} (hQP : Q ≤ P) (hQn : (Q.subgroupOf P).Normal) (hQT : Q ≤ T) (hXQ : X ≤ Q)
    (hXp : ∀ x ∈ X, x ^ p = 1) (hTp : ∀ t ∈ T, t ^ p = 1 → t ∈ X) :
    P ≤ Subgroup.normalizer (X : Set H) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  have hstep : ∀ b ∈ P, ∀ x ∈ X, b * x * b⁻¹ ∈ X := by
    intro b hb x hx
    have hyQ : b * x * b⁻¹ ∈ Q := by
      have h := hQn.conj_mem ⟨x, hQP (hXQ hx)⟩ (hXQ hx) ⟨b, hb⟩
      change ((⟨b, hb⟩ * ⟨x, hQP (hXQ hx)⟩ * ⟨b, hb⟩⁻¹ : P) : H) ∈ Q
      exact h
    have hyT : b * x * b⁻¹ ∈ T := hQT hyQ
    refine hTp _ hyT ?_
    rw [conj_pow, hXp x hx]
    group
  intro x
  constructor
  · intro hx; exact hstep a ha x hx
  · intro hx
    have h := hstep a⁻¹ (P.inv_mem ha) (a * x * a⁻¹) hx
    convert h using 1
    group

theorem exists_conj_map_eq_of_exponent_card {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {T X : Subgroup H} (hT : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hXT : X ≤ T)
    (hXp : ∀ x ∈ X, x ^ p = 1) (hTp : ∀ t ∈ T, t ^ p = 1 → t ∈ X)
    (hX4 : Nat.card X ≤ p ^ 4)
    (hord : (Nat.card H).factorization p = (Nat.card T).factorization p + 1)
    (hcent : ∀ c : H, (∀ x ∈ X, c * x = x * c) → c ∈ T)
    (hfix : ∀ a : H, a ∈ Subgroup.normalizer (X : Set H) → a ^ p = 1 →
      (∃ x ∈ X, a * x ≠ x * a) → Nat.card {x : X // a * (x : H) = (x : H) * a} < p ^ 3)
    {A : Subgroup H} (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hA4 : p ^ 4 ≤ Nat.card A) :
    ∃ c : H, X.map (MulAut.conj c).toMonoidHom = A := by
  have hp : p.Prime := Fact.out
  have hp_pos : 0 < p := hp.pos
  have hp_ne : p ≠ 0 := hp.ne_zero
  haveI : Finite T := Finite.of_injective (Subtype.val) Subtype.coe_injective
  have hXpg : IsPGroup p X := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    exact ⟨1, by apply Subtype.ext; simpa using hXp x x.2⟩
  have hXpgT : IsPGroup p (X.comap T.subtype) := hXpg.comap_subtype
  obtain ⟨Q₀, hXQ₀⟩ := hXpgT.exists_le_sylow
  set Q : Subgroup H := Q₀.toSubgroup.map T.subtype with hQdef
  have hXQ : X ≤ Q := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hXT hx⟩, hXQ₀ hx, rfl⟩
  have hQT : Q ≤ T := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.2
  have hQpg : IsPGroup p Q := Q₀.isPGroup'.map T.subtype
  obtain ⟨P, hQP⟩ := hQpg.exists_le_sylow
  have hcardP : Nat.card P = p ^ (Nat.card H).factorization p := Sylow.card_eq_multiplicity P
  have hcardQ0 : Nat.card Q₀ = p ^ (Nat.card T).factorization p := Sylow.card_eq_multiplicity Q₀
  have hcardQ : Nat.card Q = Nat.card Q₀ :=
    Subgroup.card_map_of_injective (K := Q₀.toSubgroup) (f := T.subtype) Subtype.coe_injective
  have hcardPQ : Nat.card P = p * Nat.card Q := by
    rw [hcardP, hord, pow_succ, hcardQ, hcardQ0]
    ring
  have hQrel : Q.relIndex P = p := by
    have h := Subgroup.relIndex_mul_card (H := Q) (K := P)
    rw [inf_eq_left.mpr hQP] at h
    rw [hcardPQ] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q)) h
  have hQindex : (Q.subgroupOf P).index = p := hQrel
  have hQn : (Q.subgroupOf P).Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hQindex, hcardP, hord, Nat.Prime.pow_minFac hp (by omega)]
  have hPX : P ≤ Subgroup.normalizer (X : Set H) :=
    le_normalizer_of_normal_subgroupOf_pow hQP hQn hQT hXQ hXp hTp
  have hApg : IsPGroup p A := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro a
    exact ⟨1, by apply Subtype.ext; simpa using hAp a a.2⟩
  obtain ⟨P', hAP'⟩ := hApg.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H P P'
  set A' : Subgroup H := A.map (MulAut.conj c⁻¹).toMonoidHom with hA'def
  have hA'P : A' ≤ P := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨a, ha, rfl⟩
    have hc' : MulAut.conj c • (P : Subgroup H) = (P' : Subgroup H) := by
      rw [← Sylow.coe_subgroup_smul, hc]
    have haP' : a ∈ (P' : Subgroup H) := hAP' ha
    rw [← hc'] at haP'
    rcases (Subgroup.mem_smul_pointwise_iff_exists a (MulAut.conj c) P).mp haP' with ⟨q, hqP, hqa⟩
    have hq : MulAut.conj c⁻¹ a = q := by
      rw [← hqa, MulAut.smul_def, MulAut.conj_apply, MulAut.conj_apply, inv_inv]
      group
    change MulAut.conj c⁻¹ a ∈ P
    rw [hq]
    exact hqP
  have hA'comm : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    rcases Subgroup.mem_map.mp hx with ⟨x₀, hx₀, hxx⟩
    rcases Subgroup.mem_map.mp hy with ⟨y₀, hy₀, hyy⟩
    rw [← hxx, ← hyy, ← map_mul, hA x₀ hx₀ y₀ hy₀, map_mul]
  have hA'p : ∀ a ∈ A', a ^ p = 1 := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨x₀, hx₀, hxx⟩
    rw [← hxx, ← map_pow, hAp x₀ hx₀, map_one]
  have hA'card : p ^ 4 ≤ Nat.card A' := by
    rw [Subgroup.card_map_of_injective (K := A) (f := (MulAut.conj c⁻¹).toMonoidHom)
      (MulAut.conj c⁻¹).injective]
    exact hA4
  have hA'X : A' = X := by
    by_cases hAQ : A' ≤ Q
    · have hA'Xle : A' ≤ X := by
        intro a ha
        exact hTp a (hQT (hAQ ha)) (hA'p a ha)
      exact Subgroup.eq_of_le_of_card_ge hA'Xle (le_trans hX4 hA'card)
    · change ¬ (A' : Set H) ⊆ (Q : Set H) at hAQ
      obtain ⟨a, haA', haQ⟩ := Set.not_subset.mp hAQ
      have haP : a ∈ P := hA'P haA'
      have haN : a ∈ Subgroup.normalizer (X : Set H) := hPX haP
      have hap : a ^ p = 1 := hA'p a haA'
      have hnc : ∃ x ∈ X, a * x ≠ x * a := by
        by_contra hcon
        push Not at hcon
        have haT : a ∈ T := hcent a hcon
        have haX : a ∈ X := hTp a haT hap
        exact haQ (hXQ haX)
      have hfixa := hfix a haN hap hnc
      set B : Subgroup H := A' ⊓ Q with hBdef
      have hBX : B ≤ X := by
        intro b hb
        have hb' : (b : H) ∈ A' ⊓ Q := by rw [← hBdef]; exact hb
        exact hTp b (hQT hb'.2) (hA'p b hb'.1)
      have hinj : Function.Injective
          (fun b : B => (⟨⟨b, hBX b.2⟩, by
            show a * (b : H) = (b : H) * a
            have hb' : (b : H) ∈ A' ⊓ Q := by rw [← hBdef]; exact b.2
            exact hA'comm a haA' (b : H) hb'.1⟩ : {x : X // a * (x : H) = (x : H) * a})) := by
        intro b₁ b₂ h
        apply Subtype.ext
        exact congrArg (fun y : {x : X // a * (x : H) = (x : H) * a} => ((y.1 : X) : H)) h
      have hBcard : Nat.card B ≤
          Nat.card {x : X // a * (x : H) = (x : H) * a} :=
        Nat.card_le_card_of_injective _ hinj
      have hrelB : B.relIndex A' ≤ p := by
        rw [hBdef, Subgroup.inf_relIndex_left]
        exact (Subgroup.relIndex_le_of_le_right hA'P (by rw [hQrel]; exact hp_ne)).trans (le_of_eq hQrel)
      have hmul : B.relIndex A' * Nat.card B = Nat.card A' := by
        have h := Subgroup.relIndex_mul_card (H := B) (K := A')
        rwa [inf_eq_left.mpr (by rw [hBdef]; exact inf_le_left)] at h
      have hp3 : p ^ 3 ≤ Nat.card B := by
        have h := hA'card
        rw [← hmul] at h
        have hmul2 : p * p ^ 3 ≤ p * Nat.card B := by
          calc p * p ^ 3 = p ^ 4 := by ring
            _ ≤ B.relIndex A' * Nat.card B := h
            _ ≤ p * Nat.card B := Nat.mul_le_mul_right _ hrelB
        exact Nat.le_of_mul_le_mul_left hmul2 hp_pos
      exact absurd (le_trans hp3 hBcard) (not_le.mpr hfixa)
  refine ⟨c, ?_⟩
  rw [← hA'X, hA'def]
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    have hxz : x = z := by
      rw [← hxy, ← hyz]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hxz]
  · intro hx
    exact ⟨MulAut.conj c⁻¹ x, ⟨x, hx, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]; group⟩

end NoOffE8Five

end CFSG.StandardType
