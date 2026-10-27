module

public import CFSG.Quasithin.Vol2.Ch11SecDK
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecDFacts2
public import CFSG.Quasithin.Vol2.Ch11StatementsH

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem card_conjSubgroup (A : Subgroup G) (g : G) : Nat.card (conjSubgroup A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem normalizer_zpowers_le (h1142 : Stmt11_4_2) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hK : KOf L V₁ V₁ = LOf L V₁) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) (hz1 : z ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤
      Subgroup.normalizer (LOf L V₁ : Set G) := by
  have hKz := h1142 G T L I n V₁ h hV₁ z hz hz1
  rw [hK] at hKz
  rw [← hKz]
  exact le_normalizer_conjClosure _ _

omit [Finite G] in
theorem lOf_conj_le {V₁ : Subgroup G} {z g u y y' : G} (hy' : y' ∈ L)
    (hN : Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤
      Subgroup.normalizer (LOf L V₁ : Set G))
    (hu : y * z * y⁻¹ = u) (hgu : y' * z * y'⁻¹ = g * u * g⁻¹) :
    conjSubgroup (LOf L V₁) y⁻¹ ≤ conjSubgroup L g := by
  set c := y⁻¹ * g⁻¹ * y' with hc
  have hcz : c ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    have : c * z * c⁻¹ = z := by
      calc c * z * c⁻¹ = y⁻¹ * g⁻¹ * (y' * z * y'⁻¹) * g * y := by rw [hc]; group
        _ = z := by rw [hgu, ← hu]; group
    calc z * c = c * z * c⁻¹ * c := by rw [this]
      _ = c * z := by group
  have hcL := hN (mem_normalizer_zpowers_of_mem_centralizer hcz)
  intro x hx
  rw [mem_conjSubgroup_iff] at hx ⊢
  have h1 : c⁻¹ * (y⁻¹ * x * y⁻¹⁻¹) * c⁻¹⁻¹ ∈ LOf L V₁ :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcL) _).mp hx
  have h2 : y' * (c⁻¹ * (y⁻¹ * x * y⁻¹⁻¹) * c⁻¹⁻¹) * y'⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hy' ((perfectCore_le _).trans inf_le_left h1)) (L.inv_mem hy')
  convert h2 using 1
  rw [hc]
  group

theorem stmt11_5_3_one (hTwo : TwoPointsFact) (h1102 : Stmt11_0_2) (h1003 : Stmt11_0_3)
    (h1141 : Stmt11_4_1) (h1142 : Stmt11_4_2) (h1151 : Stmt11_5_1) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hK : KOf L V₁ V₁ = LOf L V₁) {g : G}
    (hg : g ∉ Subgroup.normalizer (fsuV T I : Set G)) :
    ∃ y ∈ L, fsuV T I ⊓ conjSubgroup (fsuV T I) g ≤ conjSubgroup V₁ y := by
  have hset := natSetting11_of h1102 h1141 h hV₁
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have htrans := (h1141 G T L I n V₁ X h hV₁ hX).1.2
  obtain ⟨z, hzV₁, hz1, hzT⟩ := exists_z h hV₁
  have hzV : z ∈ fsuV T I := SecA.IsVi.le_fsuV hV₁ hzV₁
  have hN := normalizer_zpowers_le h1142 h hV₁ hK ⟨hzV, hzT⟩ hz1
  have hpt : ∀ u ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) g, u ≠ 1 →
      ∃ y ∈ L, y * z * y⁻¹ = u ∧ conjSubgroup (LOf L V₁) y⁻¹ ≤ conjSubgroup L g := by
    intro u hu hu1
    obtain ⟨y, hy, hyu⟩ := htrans z hzV u hu.1 hz1 hu1
    have hgu : g * u * g⁻¹ ∈ fsuV T I := mem_conjSubgroup_iff.mp hu.2
    have hgu1 : g * u * g⁻¹ ≠ 1 := fun h1 => hu1 (by
      have : u = g⁻¹ * (g * u * g⁻¹) * g := by group
      rw [this, h1]
      group)
    obtain ⟨y', hy', hy'u⟩ := htrans z hzV _ hgu hz1 hgu1
    exact ⟨y, hy, hyu, lOf_conj_le hy' hN hyu hy'u⟩
  by_contra hcon
  push Not at hcon
  have hne : fsuV T I ⊓ conjSubgroup (fsuV T I) g ≠ ⊥ := fun hb =>
    hcon 1 L.one_mem (by rw [hb]; exact bot_le)
  obtain ⟨u₁, hu₁, hu₁1⟩ : ∃ u ∈ fsuV T I ⊓ conjSubgroup (fsuV T I) g, u ≠ 1 := by
    obtain ⟨⟨u, hu⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨u, hu, fun h1 => hne1 (Subtype.ext h1)⟩
  obtain ⟨y₁, hy₁, -, hy₁L⟩ := hpt u₁ hu₁ hu₁1
  obtain ⟨u₂, hu₂, hu₂P⟩ := IsConcreteLE.not_le_iff_exists.mp (hcon y₁⁻¹ (L.inv_mem hy₁))
  have hu₂1 : u₂ ≠ 1 := fun h1 => hu₂P (h1 ▸ Subgroup.one_mem _)
  obtain ⟨y₂, hy₂, hy₂u, hy₂L⟩ := hpt u₂ hu₂ hu₂1
  have hP : conjSubgroup V₁ y₁⁻¹ ≠ conjSubgroup V₁ y₂⁻¹ := by
    intro hP
    apply hu₂P
    rw [hP, mem_conjSubgroup_iff, ← hy₂u]
    simpa [mul_assoc] using hzV₁
  have hgen := hTwo G T L I n V₁ hset (h1151 G T L I n h) hV₁ _ (L.inv_mem hy₁) _
    (L.inv_mem hy₂) hP
  have hLg : L ≤ conjSubgroup L g := calc
    L = _ := hgen.symm
    _ ≤ conjSubgroup L g := sup_le hy₁L hy₂L
  have hLeq : conjSubgroup L g = L :=
    (Subgroup.eq_of_le_of_card_ge hLg (le_of_eq (card_conjSubgroup L g))).symm
  exact hne ((h1003 G T L I n h).2.2.2.1.2 g (conjSubgroup_eq_iff_mem_normalizer.mp hLeq) hg)

theorem card_V₁ (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n) {V₁ : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) : Nat.card V₁ = 2 ^ n := by
  obtain ⟨X, hX⟩ := exists_isCartanX h
  have hr := SecA.IsVi.relIndex_eq hV₁
  rw [(h1141 G T L I n V₁ X h hV₁ hX).1.1, Subgroup.relIndex_bot_left, mul_one] at hr
  exact hr

theorem rParam_ge_of_card {V V₁ L : Subgroup G} {n k : ℕ}
    (hone : ∀ g : G, g ∉ Subgroup.normalizer (V : Set G) →
      ∃ y ∈ L, V ⊓ conjSubgroup V g ≤ conjSubgroup V₁ y)
    (hV₁ : Nat.card V₁ = 2 ^ n) (hV : Nat.card V = 2 ^ ((k + 1) * n)) (hV2 : IsPGroup 2 V) :
    ((k * n : ℕ) : ℕ∞) ≤ E3.rParam V := by
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUV, hnc⟩ := hU
  by_contra hlt
  push Not at hlt
  have hlt' : E3.mQuot V U < k * n := by exact_mod_cast hlt
  obtain ⟨c, hcU, hcN⟩ := IsConcreteLE.not_le_iff_exists.mp hnc
  have hUc : U ≤ V ⊓ conjSubgroup V c := fun u hu => ⟨hUV hu, mem_conjSubgroup_iff.mpr (by
    have hcu := Subgroup.mem_centralizer_iff.mp hcU u hu
    have : c * u * c⁻¹ = u := by rw [← hcu]; group
    rw [this]
    exact hUV hu)⟩
  obtain ⟨y, -, hy⟩ := hone c hcN
  have hcardU := Subgroup.card_le_of_le (hUc.trans hy)
  rw [card_conjSubgroup, hV₁] at hcardU
  have hcard := E3.card_eq_two_pow_mul hV2 hUV
  rw [hV] at hcard
  have hle : 2 ^ ((k + 1) * n) ≤ 2 ^ (E3.mQuot V U + n) := by
    rw [hcard, pow_add]
    exact Nat.mul_le_mul_left _ hcardU
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  nlinarith

end CFSG.Quasithin.Vol2.Ch11.SecD
