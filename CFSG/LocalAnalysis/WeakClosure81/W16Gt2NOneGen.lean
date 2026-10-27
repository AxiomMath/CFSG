module

public import CFSG.Quasithin.Background.G118Apply
public import CFSG.GH74.Uniqueness.Section171Group
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace NOne

theorem exists_mem_zpowers_conj_eq {X : Type*} [Group X] {t y : X} (ht : t * t = 1)
    (hty : t * y * t⁻¹ = y⁻¹) (hy : Odd (orderOf y)) :
    ∃ x ∈ Subgroup.zpowers y, x⁻¹ * t * x = y * t := by
  obtain ⟨n, hn⟩ := CFSG.GH74.Uniqueness.exists_pow_conj_of_inverted hy hty ht
  refine ⟨(y ^ n)⁻¹, Subgroup.inv_mem _ (Subgroup.npow_mem_zpowers y n), ?_⟩
  rw [inv_inv]
  exact hn.symm

private lemma zpow_eq_one_or_self {w : G} (hw2 : w * w = 1) (k : ℤ) :
    w ^ k = 1 ∨ w ^ k = w := by
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · left
    rw [hn, zpow_mul]
    have h2 : w ^ (2 : ℤ) = 1 := by simpa [pow_two] using hw2
    rw [h2, one_zpow]
  · right
    rw [hn, zpow_add_one, zpow_mul]
    have h2 : w ^ (2 : ℤ) = 1 := by simpa [pow_two] using hw2
    rw [h2, one_zpow, one_mul]

private lemma eq_self_of_ne_one_zpow {w : G} (hw2 : w * w = 1) {k : ℤ} (hk : w ^ k ≠ 1) :
    w ^ k = w := by
  rcases zpow_eq_one_or_self hw2 k with h | h
  · exact absurd h hk
  · exact h

private lemma zpow_eq_one_of_two {u w : G} (hu2 : u * u = 1) (hu1 : u ≠ 1)
    (hw2 : w * w = 1) {k : ℤ} (hk : u ^ k = 1) : w ^ k = 1 := by
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' k
  · rw [hn, zpow_mul]
    have h2 : w ^ (2 : ℤ) = 1 := by simpa [pow_two] using hw2
    rw [h2, one_zpow]
  · exfalso
    rw [hn, zpow_add_one, zpow_mul] at hk
    have h2 : u ^ (2 : ℤ) = 1 := by simpa [pow_two] using hu2
    rw [h2, one_zpow, one_mul] at hk
    exact hu1 hk

private lemma zpow_eq_self_of_two {u w : G} (hu2 : u * u = 1) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    {j : ℤ} (h : w ^ j = w) : u ^ j = u := by
  obtain ⟨n, hn | hn⟩ := Int.even_or_odd' j
  · exfalso
    rw [hn, zpow_mul] at h
    have h2 : w ^ (2 : ℤ) = 1 := by simpa [pow_two] using hw2
    rw [h2, one_zpow] at h
    exact hw1 h.symm
  · rw [hn, zpow_add_one, zpow_mul]
    have h2 : u ^ (2 : ℤ) = 1 := by simpa [pow_two] using hu2
    rw [h2, one_zpow, one_mul]

private lemma mem_sup_iff_exists_mul_of_comm {P Q : Subgroup G}
    (hcomm : ∀ a ∈ P, ∀ b ∈ Q, a * b = b * a) {x : G} :
    x ∈ P ⊔ Q ↔ ∃ a ∈ P, ∃ b ∈ Q, a * b = x := by
  have hnorm : P ≤ normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp q hq
    rw [hcomm p hp q hq, mul_assoc, mul_inv_cancel, mul_one]
    exact hq
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right P Q hnorm]
  exact Set.mem_mul

private lemma eq_of_mul_eq_mul {A₁ A₂ : Subgroup G} (hdisj : A₁ ⊓ A₂ = ⊥) {a a' w w' : G}
    (ha : a ∈ A₁) (ha' : a' ∈ A₁) (hw : w ∈ A₂) (hw' : w' ∈ A₂)
    (h : a * w = a' * w') : a = a' ∧ w = w' := by
  have h1 : a'⁻¹ * a = w' * w⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * w) * w⁻¹ := by group
      _ = a'⁻¹ * (a' * w') * w⁻¹ := by rw [h]
      _ = w' * w⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ A₁ ⊓ A₂ :=
    ⟨A₁.mul_mem (A₁.inv_mem ha') ha, h1 ▸ A₂.mul_mem hw' (A₂.inv_mem hw)⟩
  rw [hdisj] at hmem
  have h2 : a'⁻¹ * a = 1 := by simpa using hmem
  have haa : a = a' := (inv_mul_eq_one.mp h2).symm
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact mul_left_cancel h

private lemma snd_eq_zpow_of_mem_sup {A₁ A₂ : Subgroup G} (hdisj : A₁ ⊓ A₂ = ⊥)
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    {C : Subgroup G} (hC : C ≤ A₁) {u w a b c : G} (hu : u ∈ A₁) (hw : w ∈ A₂)
    (ha : a ∈ A₁) (hb : b ∈ A₂) (hc : c ∈ C) {k : ℤ}
    (h : a * b = c * (u * w) ^ k) : b = w ^ k ∧ a = c * u ^ k := by
  have huw : Commute u w := hcomm u hu w hw
  have h' : a * b = (c * u ^ k) * w ^ k := by
    rw [h, huw.mul_zpow, mul_assoc]
  obtain ⟨haa, hbb⟩ := eq_of_mul_eq_mul hdisj ha (A₁.mul_mem (hC hc) (A₁.zpow_mem hu k)) hb
    (A₂.zpow_mem hw k) h'
  exact ⟨hbb, haa⟩

private lemma sup_zpowers_le_sup {A₁ A₂ : Subgroup G} {C : Subgroup G} (hC : C ≤ A₁)
    {u w : G} (hu : u ∈ A₁) (hw : w ∈ A₂) : C ⊔ Subgroup.zpowers (u * w) ≤ A₁ ⊔ A₂ := by
  refine sup_le (le_trans hC le_sup_left) ?_
  rw [Subgroup.zpowers_le]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hw)

private lemma sup_zpowers_inf_eq_bot {A₁ A₂ : Subgroup G} (hW : IsElemAbelian 2 (A₁ ⊔ A₂))
    (hdisj : A₁ ⊓ A₂ = ⊥)
    (hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x)
    {C : Subgroup G} (hC : C ≤ A₁) {u : G} (hCinf : C ⊓ Subgroup.zpowers u = ⊥)
    (hu : u ∈ A₁) (hu1 : u ≠ 1) {w : G} (hw : w ∈ A₂)
    (hu2 : u * u = 1) (hw2 : w * w = 1) :
    (C ⊔ Subgroup.zpowers (u * w)) ⊓ A₂ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxD, hxA₂⟩ := hx
  have hcommC : ∀ a ∈ C, ∀ b ∈ Subgroup.zpowers (u * w), a * b = b * a := by
    intro a ha b hb
    have hbW : b ∈ A₁ ⊔ A₂ :=
      (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
        (Subgroup.mem_sup_right hw))) hb
    exact B2F.isElemAbelian_comm hW (Subgroup.mem_sup_left (hC ha)) hbW
  obtain ⟨c, hc, q, hq, hcq⟩ := (mem_sup_iff_exists_mul_of_comm hcommC).mp hxD
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  have h1x : (1 : G) * x = c * (u * w) ^ k := by rw [one_mul]; exact hcq.symm
  obtain ⟨hb, ha⟩ := snd_eq_zpow_of_mem_sup hdisj hcomm hC hu hw A₁.one_mem hxA₂ hc h1x
  have hcu : c = (u ^ k)⁻¹ := by
    calc c = c * u ^ k * (u ^ k)⁻¹ := by group
      _ = 1 * (u ^ k)⁻¹ := by rw [ha.symm]
      _ = (u ^ k)⁻¹ := by rw [one_mul]
  have hcbot : c ∈ C ⊓ Subgroup.zpowers u :=
    ⟨hc, by rw [hcu]; exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers u k)⟩
  rw [hCinf] at hcbot
  have hc1 : c = 1 := by simpa using hcbot
  have huk : u ^ k = 1 := by
    have h := ha
    rw [hc1, one_mul] at h
    exact h.symm
  rw [hb]
  exact zpow_eq_one_of_two hu2 hu1 hw2 huk

private lemma sup_zpowers_sup_eq {A₁ A₂ : Subgroup G} {C : Subgroup G} (hC : C ≤ A₁)
    {u w : G} (hu : u ∈ A₁) (hw : w ∈ A₂) (hCsup : C ⊔ Subgroup.zpowers u = A₁) :
    (C ⊔ Subgroup.zpowers (u * w)) ⊔ A₂ = A₁ ⊔ A₂ := by
  refine le_antisymm ?_ ?_
  · exact sup_le (sup_zpowers_le_sup hC hu hw) le_sup_right
  · rw [← hCsup]
    refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact le_trans (le_sup_left : C ≤ C ⊔ Subgroup.zpowers (u * w))
        (le_sup_left : C ⊔ Subgroup.zpowers (u * w) ≤
          (C ⊔ Subgroup.zpowers (u * w)) ⊔ A₂)
    · rw [Subgroup.zpowers_le]
      have huwD : u * w ∈ (C ⊔ Subgroup.zpowers (u * w)) ⊔ A₂ :=
        Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers (u * w)))
      have h3 : (u * w) * w⁻¹ ∈ (C ⊔ Subgroup.zpowers (u * w)) ⊔ A₂ :=
        Subgroup.mul_mem _ huwD (Subgroup.mem_sup_right (A₂.inv_mem hw))
      rwa [show (u * w) * w⁻¹ = u by group] at h3

private theorem conj_eq_self_of_mem_A₂ {A₁ A₂ : Subgroup G} {z : G}
    (hW : IsElemAbelian 2 (A₁ ⊔ A₂))
    (h₁ : A₁ ≠ ⊥) (hdisj : A₁ ⊓ A₂ = ⊥)
    (hz : ∀ D : Subgroup G, D ≤ A₁ ⊔ A₂ → D ⊓ A₂ = ⊥ → D ⊔ A₂ = A₁ ⊔ A₂ →
      z ∈ normalizer (D : Set G))
    (hz₂ : z ∈ normalizer (A₂ : Set G))
    {w : G} (hw : w ∈ A₂) : z * w * z⁻¹ = w := by
  by_cases hw1 : w = 1
  · rw [hw1]; group
  have hA₁ea : IsElemAbelian 2 A₁ := B2F.isElemAbelian_mono le_sup_left hW
  have hA₂ea : IsElemAbelian 2 A₂ := B2F.isElemAbelian_mono le_sup_right hW
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hW (Subgroup.mem_sup_left hx)
      (Subgroup.mem_sup_right hy)
  have hcommA₁ : ∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hA₁ea hx hy
  have hsqA₁ : ∀ x ∈ A₁, x * x = 1 := fun x hx => by
    simpa [pow_two] using hA₁ea.2 x hx
  have hw2 : w * w = 1 := by simpa [pow_two] using hA₂ea.2 w hw
  obtain ⟨u₀, hu₀, hu₀1⟩ := (Subgroup.nontrivial_iff_exists_ne_one A₁).mp
    ((Subgroup.nontrivial_iff_ne_bot A₁).mpr h₁)
  obtain ⟨C, hCA₁, hCinf, hCsup⟩ :=
    CFSG.Quasithin.G11.G118.exists_complement_of_isElemTwo (E := A₁)
      (F := Subgroup.zpowers u₀) hcommA₁ hsqA₁ (Subgroup.zpowers_le.mpr hu₀)
  have hu₀2 : u₀ * u₀ = 1 := hsqA₁ u₀ hu₀
  have hDle : C ⊔ Subgroup.zpowers (u₀ * w) ≤ A₁ ⊔ A₂ := sup_zpowers_le_sup hCA₁ hu₀ hw
  have hDinf : (C ⊔ Subgroup.zpowers (u₀ * w)) ⊓ A₂ = ⊥ :=
    sup_zpowers_inf_eq_bot hW hdisj hcomm hCA₁ hCinf hu₀ hu₀1 hw hu₀2 hw2
  have hDsup : (C ⊔ Subgroup.zpowers (u₀ * w)) ⊔ A₂ = A₁ ⊔ A₂ :=
    sup_zpowers_sup_eq hCA₁ hu₀ hw hCsup
  have hnormD := hz (C ⊔ Subgroup.zpowers (u₀ * w)) hDle hDinf hDsup
  have hzA₁ : z ∈ normalizer (A₁ : Set G) := hz A₁ le_sup_left hdisj rfl
  have hmemD : u₀ * w ∈ C ⊔ Subgroup.zpowers (u₀ * w) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers (u₀ * w))
  have hconjmem : z * (u₀ * w) * z⁻¹ ∈ C ⊔ Subgroup.zpowers (u₀ * w) :=
    (Subgroup.mem_normalizer_iff.mp hnormD (u₀ * w)).mp hmemD
  have hconjeq : z * (u₀ * w) * z⁻¹ = (z * u₀ * z⁻¹) * (z * w * z⁻¹) := by group
  rw [hconjeq] at hconjmem
  have hcommC : ∀ a ∈ C, ∀ b ∈ Subgroup.zpowers (u₀ * w), a * b = b * a := by
    intro a ha b hb
    have hbW : b ∈ A₁ ⊔ A₂ :=
      (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₀)
        (Subgroup.mem_sup_right hw))) hb
    exact B2F.isElemAbelian_comm hW (Subgroup.mem_sup_left (hCA₁ ha)) hbW
  obtain ⟨c, hc, q, hq, hcq⟩ := (mem_sup_iff_exists_mul_of_comm hcommC).mp hconjmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  have hu₁ : z * u₀ * z⁻¹ ∈ A₁ := (Subgroup.mem_normalizer_iff.mp hzA₁ u₀).mp hu₀
  have hw₁ : z * w * z⁻¹ ∈ A₂ := (Subgroup.mem_normalizer_iff.mp hz₂ w).mp hw
  obtain ⟨hb, -⟩ := snd_eq_zpow_of_mem_sup hdisj hcomm hCA₁ hu₀ hw hu₁ hw₁ hc hcq.symm
  have hw₁ne : z * w * z⁻¹ ≠ 1 := by
    intro h
    have h2 : z * w = z * 1 := by
      have h3 := congrArg (fun t => t * z) h
      simpa [mul_assoc] using h3
    exact hw1 (mul_left_cancel h2)
  exact hb.trans (eq_self_of_ne_one_zpow hw2 (by rw [← hb]; exact hw₁ne))

private theorem conj_eq_self_of_mem_A₁ {A₁ A₂ : Subgroup G} {z : G}
    (hW : IsElemAbelian 2 (A₁ ⊔ A₂))
    (h₂ : A₂ ≠ ⊥) (hdisj : A₁ ⊓ A₂ = ⊥)
    (hz : ∀ D : Subgroup G, D ≤ A₁ ⊔ A₂ → D ⊓ A₂ = ⊥ → D ⊔ A₂ = A₁ ⊔ A₂ →
      z ∈ normalizer (D : Set G))
    (hz₂ : z ∈ normalizer (A₂ : Set G))
    {u : G} (hu : u ∈ A₁) : z * u * z⁻¹ = u := by
  by_cases hu1 : u = 1
  · rw [hu1]; group
  have hA₁ea : IsElemAbelian 2 A₁ := B2F.isElemAbelian_mono le_sup_left hW
  have hA₂ea : IsElemAbelian 2 A₂ := B2F.isElemAbelian_mono le_sup_right hW
  have hcomm : ∀ x ∈ A₁, ∀ y ∈ A₂, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hW (Subgroup.mem_sup_left hx)
      (Subgroup.mem_sup_right hy)
  have hcommA₁ : ∀ x ∈ A₁, ∀ y ∈ A₁, x * y = y * x :=
    fun x hx y hy => B2F.isElemAbelian_comm hA₁ea hx hy
  have hsqA₁ : ∀ x ∈ A₁, x * x = 1 := fun x hx => by
    simpa [pow_two] using hA₁ea.2 x hx
  have hu2 : u * u = 1 := hsqA₁ u hu
  obtain ⟨w, hw, hw1⟩ := (Subgroup.nontrivial_iff_exists_ne_one A₂).mp
    ((Subgroup.nontrivial_iff_ne_bot A₂).mpr h₂)
  have hw2 : w * w = 1 := by simpa [pow_two] using hA₂ea.2 w hw
  have h₁ : A₁ ≠ ⊥ := by
    intro hbot
    exact hu1 (by rw [hbot] at hu; simpa using hu)
  have hwconj : z * w * z⁻¹ = w := conj_eq_self_of_mem_A₂ hW h₁ hdisj hz hz₂ hw
  have hzA₁ : z ∈ normalizer (A₁ : Set G) := hz A₁ le_sup_left hdisj rfl
  have hu₁ : z * u * z⁻¹ ∈ A₁ := (Subgroup.mem_normalizer_iff.mp hzA₁ u).mp hu
  have hmain : ∀ K : Subgroup G, K ≤ A₁ → K ⊓ Subgroup.zpowers u = ⊥ →
      K ⊔ Subgroup.zpowers u = A₁ → (z * u * z⁻¹) * u⁻¹ ∈ K := by
    intro K hK hKinf hKsup
    have hDle : K ⊔ Subgroup.zpowers (u * w) ≤ A₁ ⊔ A₂ := sup_zpowers_le_sup hK hu hw
    have hDinf : (K ⊔ Subgroup.zpowers (u * w)) ⊓ A₂ = ⊥ :=
      sup_zpowers_inf_eq_bot hW hdisj hcomm hK hKinf hu hu1 hw hu2 hw2
    have hDsup : (K ⊔ Subgroup.zpowers (u * w)) ⊔ A₂ = A₁ ⊔ A₂ :=
      sup_zpowers_sup_eq hK hu hw hKsup
    have hnormD := hz (K ⊔ Subgroup.zpowers (u * w)) hDle hDinf hDsup
    have hmemD : u * w ∈ K ⊔ Subgroup.zpowers (u * w) :=
      Subgroup.mem_sup_right (Subgroup.mem_zpowers (u * w))
    have hconjmem : z * (u * w) * z⁻¹ ∈ K ⊔ Subgroup.zpowers (u * w) :=
      (Subgroup.mem_normalizer_iff.mp hnormD (u * w)).mp hmemD
    have hconjeq : z * (u * w) * z⁻¹ = (z * u * z⁻¹) * (z * w * z⁻¹) := by group
    rw [hconjeq, hwconj] at hconjmem
    have hcommK : ∀ a ∈ K, ∀ b ∈ Subgroup.zpowers (u * w), a * b = b * a := by
      intro a ha b hb
      have hbW : b ∈ A₁ ⊔ A₂ :=
        (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _ (Subgroup.mem_sup_left hu)
          (Subgroup.mem_sup_right hw))) hb
      exact B2F.isElemAbelian_comm hW (Subgroup.mem_sup_left (hK ha)) hbW
    obtain ⟨c, hc, q, hq, hcq⟩ := (mem_sup_iff_exists_mul_of_comm hcommK).mp hconjmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    obtain ⟨hb, haa⟩ := snd_eq_zpow_of_mem_sup hdisj hcomm hK hu hw hu₁ hw hc hcq.symm
    have huk : u ^ k = u := zpow_eq_self_of_two hu2 hw2 hw1 hb.symm
    have hcc : (z * u * z⁻¹) * u⁻¹ = c := by rw [haa, huk]; group
    rw [hcc]; exact hc
  set c₀ : G := (z * u * z⁻¹) * u⁻¹ with hc₀
  by_cases hc₀1 : c₀ = 1
  · rw [hc₀] at hc₀1
    have h := congrArg (fun t => t * u) hc₀1
    rwa [show ((z * u * z⁻¹) * u⁻¹) * u = z * u * z⁻¹ by group, one_mul] at h
  · exfalso
    have hc₀A₁ : c₀ ∈ A₁ := by
      rw [hc₀]
      exact A₁.mul_mem hu₁ (A₁.inv_mem hu)
    have hc₀2 : c₀ * c₀ = 1 := hsqA₁ c₀ hc₀A₁
    have hc₀notu : c₀ ∉ Subgroup.zpowers u := by
      intro hmem
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hcu : c₀ = u := by
        rcases zpow_eq_one_or_self hu2 m with h1 | h1
        · exact absurd (by rw [← hm, h1] : c₀ = 1) hc₀1
        · rw [← hm]; exact h1
      rw [hc₀] at hcu
      have hzu : z * u * z⁻¹ = 1 := by
        have h3 := congrArg (fun t => t * u) hcu
        rw [show ((z * u * z⁻¹) * u⁻¹) * u = z * u * z⁻¹ by group,
          show u * u = 1 from hu2] at h3
        exact h3
      have hu_eq1 : u = 1 := by
        have h2 : z * u = z * 1 := by
          have h3 := congrArg (fun t => t * z) hzu
          simpa [mul_assoc] using h3
        exact mul_left_cancel h2
      exact hu1 hu_eq1
    obtain ⟨C₀, hC₀A₁, hC₀inf, hC₀sup⟩ :=
      CFSG.Quasithin.G11.G118.exists_complement_of_isElemTwo (E := A₁)
        (F := Subgroup.zpowers u ⊔ Subgroup.zpowers c₀) hcommA₁ hsqA₁
        (sup_le (Subgroup.zpowers_le.mpr hu) (Subgroup.zpowers_le.mpr hc₀A₁))
    have hc₀u2 : (c₀ * u) * (c₀ * u) = 1 := by
      calc (c₀ * u) * (c₀ * u) = c₀ * (u * c₀) * u := by group
        _ = c₀ * (c₀ * u) * u := by rw [hcommA₁ u hu c₀ hc₀A₁]
        _ = (c₀ * c₀) * (u * u) := by group
        _ = 1 := by rw [hc₀2, hu2, mul_one]
    have hK'A₁ : C₀ ⊔ Subgroup.zpowers (c₀ * u) ≤ A₁ := by
      refine sup_le hC₀A₁ ?_
      rw [Subgroup.zpowers_le]
      exact A₁.mul_mem hc₀A₁ hu
    have hK'inf : (C₀ ⊔ Subgroup.zpowers (c₀ * u)) ⊓ Subgroup.zpowers u = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hxK', hxu⟩ := hx
      have hcommC₀ : ∀ a ∈ C₀, ∀ b ∈ Subgroup.zpowers (c₀ * u), a * b = b * a := by
        intro a ha b hb
        exact B2F.isElemAbelian_comm hA₁ea (hC₀A₁ ha)
          ((Subgroup.zpowers_le.mpr (A₁.mul_mem hc₀A₁ hu)) hb)
      obtain ⟨d, hd, q, hq, hdq⟩ := (mem_sup_iff_exists_mul_of_comm hcommC₀).mp hxK'
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      have hcu_mem : (c₀ * u) ^ j ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers c₀ :=
        (Subgroup.zpowers_le.mpr (Subgroup.mul_mem _
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₀))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))))
          (Subgroup.zpow_mem_zpowers (c₀ * u) j)
      have h' : d * (c₀ * u) ^ j = (1 : G) * x := by rw [one_mul]; exact hdq
      have hd1 : d = 1 :=
        (eq_of_mul_eq_mul hC₀inf hd C₀.one_mem hcu_mem (Subgroup.mem_sup_left hxu) h').1
      have hjx : (c₀ * u) ^ j = x :=
        (eq_of_mul_eq_mul hC₀inf hd C₀.one_mem hcu_mem (Subgroup.mem_sup_left hxu) h').2
      rcases zpow_eq_one_or_self hc₀u2 j with hj | hj
      · rw [← hjx, hj]
      · exfalso
        have h1 : c₀ * u ∈ Subgroup.zpowers u := by
          have hx' : x ∈ Subgroup.zpowers u := hxu
          rwa [← hjx, hj] at hx'
        have h2 : c₀ ∈ Subgroup.zpowers u := by
          have h3 := Subgroup.mul_mem (Subgroup.zpowers u) h1 (Subgroup.mem_zpowers u)
          rwa [show (c₀ * u) * u = c₀ by rw [mul_assoc, hu2, mul_one]] at h3
        exact hc₀notu h2
    have hK'sup : (C₀ ⊔ Subgroup.zpowers (c₀ * u)) ⊔ Subgroup.zpowers u = A₁ := by
      refine le_antisymm ?_ ?_
      · exact sup_le hK'A₁ (Subgroup.zpowers_le.mpr hu)
      · rw [← hC₀sup]
        refine sup_le ?_ (sup_le le_sup_right ?_)
        · exact le_trans (le_sup_left : C₀ ≤ C₀ ⊔ Subgroup.zpowers (c₀ * u))
            (le_sup_left : C₀ ⊔ Subgroup.zpowers (c₀ * u) ≤
              (C₀ ⊔ Subgroup.zpowers (c₀ * u)) ⊔ Subgroup.zpowers u)
        · rw [Subgroup.zpowers_le]
          have h1 : c₀ * u ∈ (C₀ ⊔ Subgroup.zpowers (c₀ * u)) ⊔ Subgroup.zpowers u :=
            Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers (c₀ * u)))
          have h2 : u ∈ (C₀ ⊔ Subgroup.zpowers (c₀ * u)) ⊔ Subgroup.zpowers u :=
            Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
          have h3 : (c₀ * u) * u ∈ (C₀ ⊔ Subgroup.zpowers (c₀ * u)) ⊔ Subgroup.zpowers u :=
            Subgroup.mul_mem _ h1 h2
          rwa [show (c₀ * u) * u = c₀ by rw [mul_assoc, hu2, mul_one]] at h3
    have hc₀inK' : c₀ ∈ C₀ ⊔ Subgroup.zpowers (c₀ * u) := by
      rw [hc₀]
      exact hmain _ hK'A₁ hK'inf hK'sup
    have hc₀notK' : c₀ ∉ C₀ ⊔ Subgroup.zpowers (c₀ * u) := by
      intro hmem
      have hcommC₀ : ∀ a ∈ C₀, ∀ b ∈ Subgroup.zpowers (c₀ * u), a * b = b * a := by
        intro a ha b hb
        exact B2F.isElemAbelian_comm hA₁ea (hC₀A₁ ha)
          ((Subgroup.zpowers_le.mpr (A₁.mul_mem hc₀A₁ hu)) hb)
      obtain ⟨d, hd, q, hq, hdq⟩ := (mem_sup_iff_exists_mul_of_comm hcommC₀).mp hmem
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
      rcases zpow_eq_one_or_self hc₀u2 j with hj | hj
      · rw [hj, mul_one] at hdq
        have hdc : d = c₀ := hdq
        have hd1 : d = 1 := by
          have hdmem : d ∈ C₀ ⊓ (Subgroup.zpowers u ⊔ Subgroup.zpowers c₀) :=
            ⟨hd, hdc.symm ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c₀)⟩
          rw [hC₀inf] at hdmem
          simpa using hdmem
        exact hc₀1 (by rw [← hdc, hd1])
      · rw [hj] at hdq
        have hd_eq : d = u := by
          have h3 : d = c₀ * (c₀ * u)⁻¹ := eq_mul_inv_of_mul_eq hdq
          rw [h3]
          have h4 : (c₀ * u)⁻¹ = c₀ * u := by
            rw [inv_eq_iff_mul_eq_one]
            exact hc₀u2
          rw [h4, show c₀ * (c₀ * u) = (c₀ * c₀) * u by group, hc₀2, one_mul]
        have hd1 : d = 1 := by
          have hdmem : d ∈ C₀ ⊓ (Subgroup.zpowers u ⊔ Subgroup.zpowers c₀) :=
            ⟨hd, hd_eq.symm ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers u)⟩
          rw [hC₀inf] at hdmem
          simpa using hdmem
        exact hu1 (by rw [← hd_eq, hd1])
    exact hc₀notK' hc₀inK'

theorem mem_centralizer_of_conj_eq_complements {A₁ A₂ : Subgroup G} {z : G}
    (hW : IsElemAbelian 2 (A₁ ⊔ A₂)) (h₁ : A₁ ≠ ⊥) (h₂ : A₂ ≠ ⊥) (hdisj : A₁ ⊓ A₂ = ⊥)
    (hzW : z ∈ normalizer ((A₁ ⊔ A₂ : Subgroup G) : Set G))
    (hz₂ : z ∈ normalizer (A₂ : Set G))
    (hz : ∀ D : Subgroup G, D ≤ A₁ ⊔ A₂ → D ⊓ A₂ = ⊥ → D ⊔ A₂ = A₁ ⊔ A₂ →
      z ∈ normalizer (D : Set G)) :
    z ∈ centralizer ((A₁ ⊔ A₂ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a :=
    fun a ha b hb => B2F.isElemAbelian_comm hW (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right hb)
  obtain ⟨u, hu, w, hw, rfl⟩ := (mem_sup_iff_exists_mul_of_comm hcomm).mp hx
  have hzu : z * u * z⁻¹ = u := conj_eq_self_of_mem_A₁ hW h₂ hdisj hz hz₂ hu
  have hzw : z * w * z⁻¹ = w := conj_eq_self_of_mem_A₂ hW h₁ hdisj hz hz₂ hw
  have hzu' : z * u = u * z := by
    calc z * u = (z * u * z⁻¹) * z := by group
      _ = u * z := by rw [hzu]
  have hzw' : z * w = w * z := by
    calc z * w = (z * w * z⁻¹) * z := by group
      _ = w * z := by rw [hzw]
  calc u * w * z = u * (w * z) := by group
    _ = u * (z * w) := by rw [hzw']
    _ = (u * z) * w := by group
    _ = (z * u) * w := by rw [hzu']
    _ = z * (u * w) := by group

end NOne

end CFSG.LocalAnalysis.WeakClosure81
