module

public import CFSG.RankThree.GF2n.Basic
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.GF2n.Tim78Normal

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev cent (V A : Subgroup G) : Subgroup G := V ⊓ Subgroup.centralizer (A : Set G)

theorem tim78_2_4 {L K V : Subgroup G} {n : ℕ} (hLcard : Nat.card L = 2 ^ n)
    (hKcard : Nat.card K = Nat.card L - 1) (hKL : K ≤ Subgroup.normalizer (L : Set G))
    (hfrob : ∀ k ∈ K, k ≠ 1 → ∀ x ∈ L, k * x * k⁻¹ = x → x = 1)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hV : Assembly.IsElemAbelian 2 V)
    (hKV : K ≤ Subgroup.normalizer (V : Set G))
    (hA : ∃ A : Subgroup G, A ≤ L ∧ A ≠ ⊥ ∧ Nat.card V ≤ Nat.card A * Nat.card (cent V A)) :
    Nat.card V ≤ Nat.card L * Nat.card (cent V L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hconjL : ∀ k ∈ K, ∀ x ∈ L, k * x * k⁻¹ ∈ L := fun k hk x hx =>
    (Subgroup.mem_normalizer_iff.mp (hKL hk) x).mp hx
  have htrans : ∀ x ∈ L, x ≠ 1 → ∀ y ∈ L, y ≠ 1 → ∃ k ∈ K, k * x * k⁻¹ = y := by
    intro x hx hx1 y hy hy1
    let f : K → {z : L // z ≠ 1} := fun k => ⟨⟨(k : G) * x * (k : G)⁻¹, hconjL k k.2 x hx⟩,
      fun h => hx1 (by
      have := congrArg Subtype.val h
      simp only [OneMemClass.coe_one] at this
      calc x = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) := by group
        _ = 1 := by rw [this]; group)⟩
    have hf : Function.Injective f := by
      intro k k' hkk'
      have h1 : (k : G) * x * (k : G)⁻¹ = k' * x * (k' : G)⁻¹ :=
        congrArg (fun z : {z : L // z ≠ 1} => ((z.1 : L) : G)) hkk'
      by_contra hne
      have hne' : (k' : G)⁻¹ * k ≠ 1 := fun h => hne (Subtype.ext (by
        calc (k : G) = k' * ((k' : G)⁻¹ * k) := by group
          _ = k' := by rw [h, mul_one]))
      apply hx1
      refine hfrob _ (K.mul_mem (K.inv_mem k'.2) k.2) hne' x hx ?_
      calc (k' : G)⁻¹ * k * x * ((k' : G)⁻¹ * k)⁻¹ = (k' : G)⁻¹ * (k * x * (k : G)⁻¹) * k' := by
            group
        _ = (k' : G)⁻¹ * (k' * x * (k' : G)⁻¹) * k' := by rw [h1]
        _ = x := by group
    have hcard1 : Nat.card {z : L // z ≠ 1} = Nat.card L - 1 := by
      have h := Nat.card_congr (Equiv.sumCompl (fun z : L => z = 1))
      rw [Nat.card_sum, Nat.card_unique] at h
      show Nat.card {z : L // ¬ z = 1} = Nat.card L - 1
      omega
    obtain ⟨k, hk⟩ := (hf.bijective_of_nat_card_le (by rw [hcard1, hKcard])).2
      ⟨⟨y, hy⟩, fun h => hy1 (congrArg Subtype.val h)⟩
    exact ⟨k, k.2, congrArg (fun z : {z : L // z ≠ 1} => ((z.1 : L) : G)) hk⟩
  have hinvL : ∀ U : Subgroup G, U ≤ L → U ≠ ⊥ → (∀ k ∈ K, ∀ u ∈ U, k * u * k⁻¹ ∈ U) →
      U = L := by
    intro U hUL hU hKU
    refine le_antisymm hUL fun y hy => ?_
    by_cases hy1 : y = 1
    · rw [hy1]
      exact U.one_mem
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
    obtain ⟨k, hk, rfl⟩ := htrans u (hUL hu) (fun h => hu1 (Subtype.ext h)) y hy hy1
    exact hKU k hk u hu
  have hL2 : IsPGroup 2 L := IsPGroup.of_card hLcard
  have hLc : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
    by_cases hLbot : L = ⊥
    · intro a ha b hb
      rw [hLbot, Subgroup.mem_bot] at ha hb
      rw [ha, hb]
    have hZ : L ⊓ Subgroup.centralizer (L : Set G) = L := by
      refine hinvL _ inf_le_left ?_ ?_
      · obtain ⟨d, hdL, hd1, hdc⟩ := exists_mem_not_mem_commutator_mem (p := 2) (P := L)
          (B := ⊥) (N := L) hL2 (bot_lt_iff_ne_bot.mpr hLbot) le_rfl
          (by rw [Subgroup.normalizer_eq_top]; exact le_top) Subgroup.le_normalizer
        intro hbot
        apply hd1
        have : d ∈ L ⊓ Subgroup.centralizer (L : Set G) :=
          ⟨hdL, Subgroup.mem_centralizer_iff.mpr fun b hb => by
            have := hdc b hb
            rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
            exact this.symm⟩
        rw [hbot] at this
        exact this
      · intro k hk u ⟨huL, huC⟩
        exact ⟨hconjL k hk u huL, mem_normalizer_centralizer (hKL hk) |> fun h =>
          (Subgroup.mem_normalizer_iff.mp h u).mp huC⟩
    intro a ha b hb
    have hb' : b ∈ L ⊓ Subgroup.centralizer (L : Set G) := hZ.symm ▸ hb
    exact Subgroup.mem_centralizer_iff.mp hb'.2 a ha
  set val : Subgroup G → ℕ := fun A => Nat.card A * Nat.card (cent V A) with hval
  have : Finite (Subgroup G) :=
    Finite.of_injective (SetLike.coe : Subgroup G → Set G) SetLike.coe_injective
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  set 𝔐 := Finset.univ.filter fun A : Subgroup G => A ≤ L ∧ A ≠ ⊥ with h𝔐
  obtain ⟨A₁, hA₁L, hA₁, hA₁V⟩ := hA
  have h𝔐ne : 𝔐.Nonempty := ⟨A₁, by simp [h𝔐, hA₁L, hA₁]⟩
  obtain ⟨Am, hAm, hmax⟩ := Finset.exists_max_image 𝔐 val h𝔐ne
  set m := val Am with hm
  set 𝔐m := 𝔐.filter fun A => val A = m with h𝔐m
  have h𝔐mne : 𝔐m.Nonempty := ⟨Am, Finset.mem_filter.mpr ⟨hAm, rfl⟩⟩
  obtain ⟨A₀, hA₀mem, hmin⟩ := Finset.exists_min_image 𝔐m (fun A : Subgroup G => Nat.card A)
    h𝔐mne
  have hA₀ : A₀ ∈ 𝔐 ∧ val A₀ = m := Finset.mem_filter.mp hA₀mem
  have hA₀L : A₀ ≤ L := (Finset.mem_filter.mp hA₀.1).2.1
  have hA₀bot : A₀ ≠ ⊥ := (Finset.mem_filter.mp hA₀.1).2.2
  have hmV : Nat.card V ≤ m := hA₁V.trans (hmax A₁ (by simp [h𝔐, hA₁L, hA₁]))
  have hval_le : ∀ A : Subgroup G, A ≤ L → A ≠ ⊥ → val A ≤ m := fun A hAL hA =>
    hmax A (by simp [h𝔐, hAL, hA])
  have hval_lt : ∀ A : Subgroup G, A ≤ L → A ≠ ⊥ → Nat.card A < Nat.card A₀ → val A < m := by
    intro A hAL hA hlt
    rcases lt_or_eq_of_le (hval_le A hAL hA) with h | h
    · exact h
    · exact absurd (hmin A (by simp [h𝔐m, h𝔐, hAL, hA, h])) (not_le.mpr hlt)
  have hcardconj : ∀ k ∈ K, ∀ A : Subgroup G, Nat.card (conjSubgroup k A) = Nat.card A :=
    fun k _ A => card_conjSubgroup k A
  have hconjle : ∀ k ∈ K, ∀ A : Subgroup G, A ≤ L → conjSubgroup k A ≤ L := by
    intro k hk A hAL x hx
    have := hconjL k hk _ (hAL (mem_conjSubgroup.mp hx))
    rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at this
  have hcentconj : ∀ k ∈ K, ∀ A : Subgroup G,
      Nat.card (cent V (conjSubgroup k A)) = Nat.card (cent V A) := by
    intro k hk A
    have e : cent V (conjSubgroup k A) = conjSubgroup k (cent V A) := by
      ext x
      rw [mem_conjSubgroup]
      constructor
      · rintro ⟨hxV, hxA⟩
        refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hKV (K.inv_mem hk)) x).mp hxV
          rwa [inv_inv] at this
        · have hka : k * a * k⁻¹ ∈ conjSubgroup k A := by
            rw [mem_conjSubgroup, show k⁻¹ * (k * a * k⁻¹) * k = a by group]
            exact ha
          have h1 := Subgroup.mem_centralizer_iff.mp hxA _ hka
          calc a * (k⁻¹ * x * k) = k⁻¹ * ((k * a * k⁻¹) * x) * k := by group
            _ = k⁻¹ * (x * (k * a * k⁻¹)) * k := by rw [h1]
            _ = k⁻¹ * x * k * a := by group
      · rintro ⟨hxV, hxA⟩
        refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hKV hk) _).mp hxV
          rwa [show k * (k⁻¹ * x * k) * k⁻¹ = x by group] at this
        · have h1 := Subgroup.mem_centralizer_iff.mp hxA _ (mem_conjSubgroup.mp ha)
          calc a * x = k * ((k⁻¹ * a * k) * (k⁻¹ * x * k)) * k⁻¹ := by group
            _ = k * ((k⁻¹ * x * k) * (k⁻¹ * a * k)) * k⁻¹ := by rw [h1]
            _ = x * a := by group
    rw [e, card_conjSubgroup]
  have hvalconj : ∀ k ∈ K, ∀ A : Subgroup G, val (conjSubgroup k A) = val A := fun k hk A => by
    simp only [hval, hcardconj k hk, hcentconj k hk]
  have hNL : ∀ A B : Subgroup G, A ≤ L → B ≤ L → A ≤ Subgroup.normalizer (B : Set G) :=
    fun A B hAL hBL => le_normalizer_of_comm fun a ha b hb => hLc a (hAL ha) b (hBL hb)
  have hNV : ∀ A B : Subgroup G, A ≤ V → B ≤ V → A ≤ Subgroup.normalizer (B : Set G) :=
    fun A B hAV hBV => le_normalizer_of_comm fun a ha b hb => hVc a (hAV ha) b (hBV hb)
  have hTI : ∀ k ∈ K, A₀ ⊓ conjSubgroup k A₀ = ⊥ ∨ A₀ ⊓ conjSubgroup k A₀ = A₀ := by
    intro k hk
    by_contra hcon
    push Not at hcon
    obtain ⟨hB1, hBA⟩ := hcon
    set B := A₀ ⊓ conjSubgroup k A₀ with hB
    set A' := conjSubgroup k A₀ with hA'
    have hA'L : A' ≤ L := hconjle k hk A₀ hA₀L
    have hBlt : Nat.card B < Nat.card A₀ :=
      Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left hBA)
    have hvB := hval_lt B (inf_le_left.trans hA₀L) hB1 hBlt
    set X := cent V A₀
    set Y := cent V A'
    have hXY : X ⊔ Y ≤ cent V B := sup_le (inf_le_inf_left _
      (Subgroup.centralizer_le (Set.subset_def.mpr fun x hx => hx.1)))
      (inf_le_inf_left _ (Subgroup.centralizer_le (Set.subset_def.mpr fun x hx => hx.2)))
    have hXYcard := PartTwo.Sec6.card_sup_mul_card_inf (hNV X Y inf_le_left inf_le_left)
    have hY : Nat.card Y = Nat.card X := hcentconj k hk A₀
    set D := A₀ ⊔ A' with hD
    have hDcard := PartTwo.Sec6.card_sup_mul_card_inf (hNL A₀ A' hA₀L hA'L)
    have hDI : X ⊓ Y ≤ cent V D := by
      intro v ⟨hvX, hvY⟩
      refine ⟨hvX.1, ?_⟩
      have hle : D ≤ Subgroup.centralizer ({v} : Set G) := by
        refine sup_le (fun a ha => ?_) (fun a ha => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hvX.2 a ha)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hvY.2 a ha)
      exact Subgroup.mem_centralizer_iff.mpr fun d hd =>
        (Subgroup.mem_centralizer_singleton_iff.mp (hle hd))
    have hvD := hval_le D (sup_le hA₀L hA'L) (fun h => hA₀bot (le_bot_iff.mp (h ▸ le_sup_left)))
    have h1 : Nat.card B * Nat.card (X ⊔ Y : Subgroup G) < m :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hXY)) hvB
    have h2 : Nat.card D * Nat.card (X ⊓ Y : Subgroup G) ≤ m :=
      le_trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hDI)) hvD
    have hm0 : m = Nat.card A₀ * Nat.card X := hA₀.2.symm
    rw [hcardconj k hk] at hDcard
    rw [hY] at hXYcard
    have hpos1 : 0 < Nat.card B * Nat.card (X ⊔ Y : Subgroup G) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have hprod : (Nat.card D * Nat.card (X ⊓ Y : Subgroup G)) *
        (Nat.card B * Nat.card (X ⊔ Y : Subgroup G)) = m * m := by
      rw [hm0]
      calc (Nat.card D * Nat.card (X ⊓ Y : Subgroup G)) *
            (Nat.card B * Nat.card (X ⊔ Y : Subgroup G))
          = (Nat.card D * Nat.card B) *
              (Nat.card (X ⊔ Y : Subgroup G) * Nat.card (X ⊓ Y : Subgroup G)) := by ring
        _ = (Nat.card A₀ * Nat.card A₀) * (Nat.card X * Nat.card X) := by
            rw [show B = A₀ ⊓ A' from rfl, hDcard, hXYcard]
        _ = Nat.card A₀ * Nat.card X * (Nat.card A₀ * Nat.card X) := by ring
    nlinarith
  set H := K ⊓ Subgroup.normalizer (A₀ : Set G) with hHdef
  have hHconj : ∀ k ∈ K, ∀ h ∈ H, h ∈ Subgroup.normalizer (conjSubgroup k A₀ : Set G) := by
    intro k hk h hh
    rw [← conjSubgroup_eq_self_iff, ← conjSubgroup_mul,
      show h * k = k * h from hKc h hh.1 k hk, conjSubgroup_mul,
      conjSubgroup_eq_self_iff.mpr hh.2]
  have hconjTI : ∀ k ∈ K, ∀ k' ∈ K, conjSubgroup k A₀ ⊓ conjSubgroup k' A₀ ≠ ⊥ →
      conjSubgroup k A₀ = conjSubgroup k' A₀ := by
    intro k hk k' hk' hne
    have e : conjSubgroup k' A₀ = conjSubgroup k (conjSubgroup (k⁻¹ * k') A₀) := by
      rw [← conjSubgroup_mul, mul_inv_cancel_left]
    have hk'' : k⁻¹ * k' ∈ K := K.mul_mem (K.inv_mem hk) hk'
    rcases hTI _ hk'' with h | h
    · exfalso
      apply hne
      rw [e, ← conjSubgroup_inf, h]
      exact Subgroup.map_bot _
    · rw [e]
      have hle : A₀ ≤ conjSubgroup (k⁻¹ * k') A₀ := inf_eq_left.mp h
      have heq' : conjSubgroup (k⁻¹ * k') A₀ = A₀ :=
        (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])).symm
      rw [heq']
  have hHtrans : ∀ k ∈ K, ∀ x ∈ conjSubgroup k A₀, x ≠ 1 → ∀ y ∈ conjSubgroup k A₀, y ≠ 1 →
      ∃ h ∈ H, h * x * h⁻¹ = y := by
    intro k hk x hx hx1 y hy hy1
    obtain ⟨k', hk', rfl⟩ := htrans x (hconjle k hk A₀ hA₀L hx) hx1 y
      (hconjle k hk A₀ hA₀L hy) hy1
    have hyB : k' * x * k'⁻¹ ∈ conjSubgroup (k' * k) A₀ := by
      rw [mem_conjSubgroup, show (k' * k)⁻¹ * (k' * x * k'⁻¹) * (k' * k) = k⁻¹ * x * k by group]
      exact mem_conjSubgroup.mp hx
    have heq := hconjTI _ (K.mul_mem hk' hk) _ hk fun hbot => hy1 (by
      have : k' * x * k'⁻¹ ∈ conjSubgroup (k' * k) A₀ ⊓ conjSubgroup k A₀ := ⟨hyB, hy⟩
      rw [hbot] at this
      exact this)
    refine ⟨k', Subgroup.mem_inf.mpr ⟨hk', ?_⟩, rfl⟩
    rw [← conjSubgroup_eq_self_iff]
    have e : conjSubgroup k' A₀ = conjSubgroup k⁻¹ (conjSubgroup (k' * k) A₀) := by
      rw [← conjSubgroup_mul, show k⁻¹ * (k' * k) = k' by
        rw [show k' * k = k * k' from hKc k' hk' k hk]; group]
    rw [e, heq, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
  set 𝔇 := Finset.univ.filter fun D : Subgroup G => D ≤ L ∧ H ≤ Subgroup.normalizer (D : Set G) ∧
    Nat.card V ≤ Nat.card D * Nat.card (cent V D) with h𝔇
  have hA₀𝔇 : A₀ ∈ 𝔇 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA₀L, fun h hh => hh.2, ?_⟩
    exact hmV.trans hA₀.2.ge
  obtain ⟨D, hD𝔇, hDmax⟩ := Finset.exists_max_image 𝔇 (fun D : Subgroup G => Nat.card D)
    ⟨A₀, hA₀𝔇⟩
  obtain ⟨hDL, hHD, hDV⟩ := (Finset.mem_filter.mp hD𝔇).2
  by_cases hDeq : D = L
  · rw [← hDeq]
    exact hDV
  exfalso
  obtain ⟨x, hxL, hxD⟩ : ∃ x ∈ L, x ∉ D := by
    by_contra h
    push Not at h
    exact hDeq (le_antisymm hDL h)
  have hx1 : x ≠ 1 := fun h => hxD (h ▸ D.one_mem)
  obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA₀bot
  obtain ⟨k, hk, hkx⟩ := htrans a (hA₀L ha) (fun h => ha1 (Subtype.ext h)) x hxL hx1
  set B := conjSubgroup k A₀ with hBdef
  have hxB : x ∈ B := by
    rw [← hkx, mem_conjSubgroup, show k⁻¹ * (k * a * k⁻¹) * k = a by group]
    exact ha
  have hBL : B ≤ L := hconjle k hk A₀ hA₀L
  have hBD : B ⊓ D = ⊥ := by
    by_contra hne
    obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    obtain ⟨h, hh, rfl⟩ := hHtrans k hk z hz.1 (fun h => hz1 (Subtype.ext h)) x hxB hx1
    exact hxD ((Subgroup.mem_normalizer_iff.mp (hHD hh) z).mp hz.2)
  set D' := D ⊔ B with hD'
  have hD'card : Nat.card D' = Nat.card D * Nat.card B := by
    have h := PartTwo.Sec6.card_sup_mul_card_inf (hNL D B hDL hBL)
    rw [inf_comm, hBD, Subgroup.card_bot, mul_one] at h
    exact h
  have hcentD' : cent V D' = cent V D ⊓ cent V B := by
    ext v
    simp only [cent, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hv, hvD'⟩
      exact ⟨⟨hv, fun d hd => hvD' d (Subgroup.mem_sup_left hd)⟩,
        ⟨hv, fun b hb => hvD' b (Subgroup.mem_sup_right hb)⟩⟩
    · rintro ⟨⟨hv, hvD⟩, -, hvB⟩
      refine ⟨hv, fun d hd => ?_⟩
      have hle : D' ≤ Subgroup.centralizer ({v} : Set G) := by
        refine sup_le (fun d hd => ?_) (fun b hb => ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hvD d hd)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr (hvB b hb)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hd)
  have hcardInt : Nat.card (cent V D) * Nat.card (cent V B) ≤
      Nat.card V * Nat.card (cent V D ⊓ cent V B : Subgroup G) := by
    have h := PartTwo.Sec6.card_sup_mul_card_inf (hNV (cent V D) (cent V B) inf_le_left
      inf_le_left)
    rw [← h]
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le (sup_le inf_le_left inf_le_left))
  have hBval : val B = m := (hvalconj k hk A₀).trans hA₀.2
  have hD'V : Nat.card V ≤ Nat.card D' * Nat.card (cent V D') := by
    rw [hD'card, hcentD']
    have hBm : Nat.card V ≤ Nat.card B * Nat.card (cent V B) := hmV.trans hBval.ge
    have hVpos : 0 < Nat.card V := Nat.card_pos
    nlinarith
  have hD'𝔇 : D' ∈ 𝔇 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, sup_le hDL hBL, fun h hh => ?_, hD'V⟩
    exact mem_normalizer_sup (hHD hh) (hHconj k hk h hh)
  have hlt : Nat.card D < Nat.card D' := by
    rw [hD'card]
    have hB2 : 2 ≤ Nat.card B := by
      have := (Subgroup.one_lt_card_iff_ne_bot B).mpr (fun h => hx1 (by
        rw [h] at hxB
        exact hxB))
      omega
    have : 0 < Nat.card D := Nat.card_pos
    nlinarith
  exact absurd (hDmax D' hD'𝔇) (not_le.mpr hlt)

end CFSG.RankThree.GF2n.Tim78
