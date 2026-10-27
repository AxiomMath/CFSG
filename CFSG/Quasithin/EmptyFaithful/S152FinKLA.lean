module

public import CFSG.Quasithin.EmptyFaithful.S152FinKLB
public import CFSG.Quasithin.EmptyFaithful.S152FinNat
public import CFSG.Quasithin.EmptyFaithful.S152FinShape

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]

namespace S152Fin

theorem le_normalizer_of_conj {F K : Subgroup G} (h : ∀ f ∈ F, ∀ x ∈ K, f * x * f⁻¹ ∈ K) :
    F ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h g hg x hx, fun hx => ?_⟩
  have := h g⁻¹ (F.inv_mem hg) _ hx
  simpa [mul_assoc] using this

@[expose] def fixOne (x : G) (L N : Subgroup G) (hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    (hLN : L ≤ N) : Subgroup G where
  carrier := {n | n ∈ N ∧ x * n * x⁻¹ * n⁻¹ ∈ L}
  one_mem' := ⟨N.one_mem, by simp⟩
  mul_mem' := by
    rintro n₁ n₂ ⟨hn₁, h₁⟩ ⟨hn₂, h₂⟩
    refine ⟨N.mul_mem hn₁ hn₂, ?_⟩
    have hcomm : n₁ * (x * n₂ * x⁻¹ * n₂⁻¹) * n₁⁻¹ = x * n₂ * x⁻¹ * n₂⁻¹ := by
      have := hab n₁ hn₁ _ (hLN h₂)
      rw [this]; group
    have e : x * (n₁ * n₂) * x⁻¹ * (n₁ * n₂)⁻¹ =
        (x * n₁ * x⁻¹ * n₁⁻¹) * (n₁ * (x * n₂ * x⁻¹ * n₂⁻¹) * n₁⁻¹) := by group
    rw [e, hcomm]
    exact L.mul_mem h₁ h₂
  inv_mem' := by
    rintro n ⟨hn, h⟩
    refine ⟨N.inv_mem hn, ?_⟩
    have hcomm : n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * n = (x * n * x⁻¹ * n⁻¹)⁻¹ := by
      have := hab n⁻¹ (N.inv_mem hn) _ (hLN (L.inv_mem h))
      rw [this]; group
    have e : x * n⁻¹ * x⁻¹ * n⁻¹⁻¹ = n⁻¹ * (x * n * x⁻¹ * n⁻¹)⁻¹ * n := by group
    rw [e, hcomm]
    exact L.inv_mem h

theorem mem_fixOne {x : G} {L N : Subgroup G} {hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a}
    {hLN : L ≤ N} {n : G} :
    n ∈ fixOne x L N hab hLN ↔ n ∈ N ∧ x * n * x⁻¹ * n⁻¹ ∈ L := Iff.rfl

theorem eq_two_of_mul_eq_four {a b : ℕ} (h : a * b = 4) (h1 : a ≠ 1) (h2 : b ≠ 1) (h3 : a ≠ 0)
    (h4 : b ≠ 0) : a = 2 ∧ b = 2 := by
  have ha : a ∣ 4 := ⟨b, h.symm⟩
  have : a ≤ 4 := Nat.le_of_dvd (by norm_num) ha
  interval_cases a <;> omega

theorem relIndex_cSecIn_le_two [Finite G] {X L X₁ : Subgroup G}
    (hX : IsElemAbelian 2 X) (hX₁ : IsElemAbelian 2 X₁) (hLX₁ : L ≤ X₁)
    (h4 : L.relIndex X₁ = 4) (hXL : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hXX₁ : ∀ x ∈ X, ∀ n ∈ X₁, x * n * x⁻¹ ∈ X₁) :
    (cSecIn X L X₁).relIndex X ≤ 2 := by
  have hab : ∀ a ∈ X₁, ∀ b ∈ X₁, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hX₁ ha hb
  have hsq : ∀ n ∈ X₁, n * n = 1 := fun n hn => by
    have := F7.isElemAbelian_pow_eq_one hX₁ hn
    rwa [sq] at this
  have hXsq : ∀ x ∈ X, x * x = 1 := fun x hx => by
    have := F7.isElemAbelian_pow_eq_one hX hx
    rwa [sq] at this
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => F7.isElemAbelian_comm hX hx hy
  have hXN : X ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_conj hXL
  have hXinv : ∀ x ∈ X, ∀ l ∈ L, x⁻¹ * l * x ∈ L := fun x hx l hl => by
    simpa using hXL x⁻¹ (X.inv_mem hx) l hl
  have hmemA : ∀ x ∈ X, x ∈ cSecIn X L X₁ ↔ ∀ n ∈ X₁, x * n * x⁻¹ * n⁻¹ ∈ L := fun x hx =>
    ⟨fun h => (mem_cSecIn hXN h).2, fun h => Subgroup.subset_closure ⟨hx, h⟩⟩
  have hnontriv : ∀ z ∈ X, z ∉ cSecIn X L X₁ → ∃ n ∈ X₁, z * n * z⁻¹ * n⁻¹ ∉ L := by
    intro z hz hzA
    by_contra h
    push Not at h
    exact hzA ((hmemA z hz).mpr h)
  have hcommF : ∀ z ∈ X, ∀ n ∈ X₁, z * n * z⁻¹ * n⁻¹ ∈ fixOne z L X₁ hab hLX₁ := by
    intro z hz n hn
    have hzz := hXsq z hz
    have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hn' : z * n * z⁻¹ ∈ X₁ := hXX₁ z hz n hn
    have hm : z * n * z⁻¹ * n⁻¹ ∈ X₁ := X₁.mul_mem hn' (X₁.inv_mem hn)
    refine ⟨hm, ?_⟩
    have e : z * (z * n * z⁻¹ * n⁻¹) * z⁻¹ = (z * n * z⁻¹ * n⁻¹)⁻¹ := by
      calc z * (z * n * z⁻¹ * n⁻¹) * z⁻¹ = (z * z) * n * z⁻¹ * n⁻¹ * z⁻¹ := by group
        _ = n * z⁻¹ * n⁻¹ * z⁻¹ := by rw [hzz, one_mul]
        _ = n * z * n⁻¹ * z⁻¹ := by rw [hz']
        _ = (z * n * z⁻¹ * n⁻¹)⁻¹ := by group
    have h1 : z * (z * n * z⁻¹ * n⁻¹) * z⁻¹ * (z * n * z⁻¹ * n⁻¹)⁻¹ = 1 := by
      rw [e, ← mul_inv_rev, hsq _ hm, inv_one]
    rw [h1]
    exact L.one_mem
  have hLF : ∀ z ∈ X, L ≤ fixOne z L X₁ hab hLX₁ := by
    intro z hz l hl
    refine ⟨hLX₁ hl, ?_⟩
    have h1 : z * l * z⁻¹ ∈ L := hXL z hz l hl
    exact L.mul_mem h1 (L.inv_mem hl)
  have hFidx : ∀ z ∈ X, z ∉ cSecIn X L X₁ → L.relIndex (fixOne z L X₁ hab hLX₁) = 2 ∧
      (fixOne z L X₁ hab hLX₁).relIndex X₁ = 2 := by
    intro z hz hzA
    obtain ⟨n, hn, hnc⟩ := hnontriv z hz hzA
    have hFX : fixOne z L X₁ hab hLX₁ ≤ X₁ := fun n hn => hn.1
    have hmF := hcommF z hz n hn
    have hnF : n ∉ fixOne z L X₁ hab hLX₁ := fun h => hnc h.2
    have h1 : L.relIndex (fixOne z L X₁ hab hLX₁) ≠ 1 := fun h =>
      hnc (Subgroup.relIndex_eq_one.mp h hmF)
    have h2 : (fixOne z L X₁ hab hLX₁).relIndex X₁ ≠ 1 := fun h =>
      hnF (Subgroup.relIndex_eq_one.mp h hn)
    have h3 := Subgroup.relIndex_mul_relIndex L (fixOne z L X₁ hab hLX₁) X₁ (hLF z hz) hFX
    rw [h4] at h3
    exact eq_two_of_mul_eq_four h3 h1 h2 Subgroup.index_ne_zero_of_finite
      Subgroup.index_ne_zero_of_finite
  have htwo : ∀ F : Subgroup G, L.relIndex F = 2 → ∀ a ∈ F, a ∉ L → ∀ b ∈ F, b ∉ L →
      a * b⁻¹ ∈ L := by
    intro F hF a ha haL b hb hbL
    obtain ⟨c, hcF, hcL, hc⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hF
    have h1 : a * c ∈ L := (hc a ha).resolve_right haL
    have h2 : b * c ∈ L := (hc b hb).resolve_right hbL
    have := L.mul_mem h1 (L.inv_mem h2)
    have e : a * c * (b * c)⁻¹ = a * b⁻¹ := by group
    rwa [e] at this
  have hFle : ∀ x ∈ X, ∀ y ∈ X, x ∉ cSecIn X L X₁ → y ∉ cSecIn X L X₁ →
      fixOne x L X₁ hab hLX₁ ≤ fixOne y L X₁ hab hLX₁ := by
    intro x hx y hy hxA hyA f hf
    by_cases hfL : f ∈ L
    · exact hLF y hy hfL
    · have hfX : f ∈ X₁ := hf.1
      have hf' : y * f * y⁻¹ ∈ X₁ := hXX₁ y hy f hfX
      have hxy : x * y = y * x := hXc x hx y hy
      have hinv : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hxy]
      have hcx : x * (y * f * y⁻¹) * x⁻¹ * (y * f * y⁻¹)⁻¹ ∈ L := by
        have e : x * (y * f * y⁻¹) * x⁻¹ * (y * f * y⁻¹)⁻¹ = y * (x * f * x⁻¹ * f⁻¹) * y⁻¹ := by
          calc x * (y * f * y⁻¹) * x⁻¹ * (y * f * y⁻¹)⁻¹
              = (x * y) * f * (y⁻¹ * x⁻¹) * (y * f⁻¹ * y⁻¹) := by group
            _ = (y * x) * f * (x⁻¹ * y⁻¹) * (y * f⁻¹ * y⁻¹) := by rw [hxy, hinv]
            _ = y * (x * f * x⁻¹ * f⁻¹) * y⁻¹ := by group
        rw [e]
        exact hXL y hy _ hf.2
      have hf'F : y * f * y⁻¹ ∈ fixOne x L X₁ hab hLX₁ := ⟨hf', hcx⟩
      have hf'L : y * f * y⁻¹ ∉ L := by
        intro h
        have := hXinv y hy _ h
        have e : y⁻¹ * (y * f * y⁻¹) * y = f := by group
        rw [e] at this
        exact hfL this
      have := htwo _ (hFidx x hx hxA).1 _ hf'F hf'L f hf hfL
      exact ⟨hfX, by simpa [mul_assoc] using this⟩
  have hFeq : ∀ x ∈ X, ∀ y ∈ X, x ∉ cSecIn X L X₁ → y ∉ cSecIn X L X₁ →
      fixOne x L X₁ hab hLX₁ = fixOne y L X₁ hab hLX₁ := fun x hx y hy hxA hyA =>
    le_antisymm (hFle x hx y hy hxA hyA) (hFle y hy x hx hyA hxA)
  have key : ∀ x ∈ X, ∀ y ∈ X, x ∉ cSecIn X L X₁ → y ∉ cSecIn X L X₁ → x * y ∈ cSecIn X L X₁ := by
    intro x hx y hy hxA hyA
    refine (hmemA _ (X.mul_mem hx hy)).mpr fun n hn => ?_
    have hFE := hFeq x hx y hy hxA hyA
    have e : x * y * n * (x * y)⁻¹ * n⁻¹ =
        (x * (y * n * y⁻¹ * n⁻¹) * x⁻¹) * (x * n * x⁻¹ * n⁻¹) := by group
    rw [e]
    by_cases hnF : n ∈ fixOne x L X₁ hab hLX₁
    · have hu : x * n * x⁻¹ * n⁻¹ ∈ L := hnF.2
      have hnFy : n ∈ fixOne y L X₁ hab hLX₁ := hFE ▸ hnF
      have hw : y * n * y⁻¹ * n⁻¹ ∈ L := hnFy.2
      exact L.mul_mem (hXL x hx _ hw) hu
    · have hnFy : n ∉ fixOne y L X₁ hab hLX₁ := hFE ▸ hnF
      have hu : x * n * x⁻¹ * n⁻¹ ∉ L := fun h => hnF ⟨hn, h⟩
      have hw : y * n * y⁻¹ * n⁻¹ ∉ L := fun h => hnFy ⟨hn, h⟩
      have huF : x * n * x⁻¹ * n⁻¹ ∈ fixOne x L X₁ hab hLX₁ := hcommF x hx n hn
      have hwF : y * n * y⁻¹ * n⁻¹ ∈ fixOne x L X₁ hab hLX₁ := hFE ▸ hcommF y hy n hn
      have hwX : y * n * y⁻¹ * n⁻¹ ∈ X₁ := hwF.1
      have huX : x * n * x⁻¹ * n⁻¹ ∈ X₁ := huF.1
      have h1 := htwo _ (hFidx x hx hxA).1 _ huF hu _ hwF hw
      have hw1 : (y * n * y⁻¹ * n⁻¹) * (y * n * y⁻¹ * n⁻¹) = 1 := hsq _ hwX
      rw [inv_eq_of_mul_eq_one_right hw1] at h1
      have h2 : (y * n * y⁻¹ * n⁻¹) * (x * n * x⁻¹ * n⁻¹) ∈ L := by
        rw [hab _ hwX _ huX]; exact h1
      have h3 : x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ * (y * n * y⁻¹ * n⁻¹)⁻¹ ∈ L := hwF.2
      have e2 : x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ =
          (x * (y * n * y⁻¹ * n⁻¹) * x⁻¹ * (y * n * y⁻¹ * n⁻¹)⁻¹) * (y * n * y⁻¹ * n⁻¹) := by
        group
      rw [e2, mul_assoc]
      exact L.mul_mem h3 h2
  by_cases hAX : X ≤ cSecIn X L X₁
  · rw [Subgroup.relIndex_eq_one.mpr hAX]; norm_num
  · have : ∃ a ∈ X, a ∉ cSecIn X L X₁ := by
      by_contra hcon
      push Not at hcon
      exact hAX fun a ha => hcon a ha
    obtain ⟨a, haX, haA⟩ := this
    have h2 : (cSecIn X L X₁).relIndex X = 2 := by
      refine Subgroup.relIndex_eq_two_iff_exists_notMem_and.mpr ⟨a, haX, haA, fun b hb => ?_⟩
      by_cases hbA : b ∈ cSecIn X L X₁
      · exact Or.inr hbA
      · exact Or.inl (key b hb a haX hbA haA)
    rw [h2]

theorem exists_nontrivial_action [Finite G] {H U L N X Y Y' : Subgroup G} (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N) (hK : cSecIn H L N = pCoreOf 2 H) (hXH : X ≤ H)
    (hXab : IsElemAbelian 2 X) (hX : 2 < (pCoreOf 2 H).relIndex X)
    (hYN : Y ≤ N) (hYY' : Y ⊔ Y' = N) (hLY : L ≤ Y)
    (h4 : L.relIndex Y = 4) (hXY : ∀ x ∈ X, ∀ n ∈ Y, x * n * x⁻¹ ∈ Y) :
    ∃ x ∈ X, ∃ n ∈ Y', x * n * x⁻¹ * n⁻¹ ∉ L := by
  by_contra htriv
  push Not at htriv
  have hNU : N ≤ U := hs.1.1
  have hLL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_isNormalIn hs.2.1
  have hYU : Y ≤ U := hYN.trans hNU
  have hKL := relIndex_cSecIn_le_two hXab (F7.isElemAbelian_mono hU hYU) hLY h4
    (fun x hx l hl => (Subgroup.mem_normalizer_iff.mp (hLL (hXH hx)) l).mp hl) hXY
  have hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm hU (hNU ha) (hNU hb)
  have hLN : L ≤ N := hs.2.2.1.le
  have hY'N : Y' ≤ N := le_sup_right.trans hYY'.le
  have hAQ : cSecIn X L Y ≤ pCoreOf 2 H := by
    intro x hx
    have hXLx : X ≤ Subgroup.normalizer (L : Set G) := fun g hg => hLL (hXH hg)
    obtain ⟨hxX, hxY⟩ := mem_cSecIn hXLx hx
    rw [← hK]
    apply Subgroup.subset_closure
    refine ⟨hXH hxX, fun n hn => ?_⟩
    have hN : N ≤ fixOne x L N hab hLN := by
      calc N = Y ⊔ Y' := hYY'.symm
        _ ≤ fixOne x L N hab hLN :=
          sup_le (fun n hn => ⟨hYN hn, hxY n hn⟩) (fun n hn => ⟨hY'N hn, htriv x hxX n hn⟩)
    exact (hN hn).2
  have hdvd := Subgroup.relIndex_dvd_of_le_left X hAQ
  have hle : (pCoreOf 2 H).relIndex X ≤ (cSecIn X L Y).relIndex X :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  omega

theorem four_le_relIndex_of_two_lt
    [Finite G] {H U L N X : Subgroup G} (hU : IsElemAbelian 2 U)
    (hs : IsChiefStep H U L N)
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)))
    (hshape : ChiefFactorShape H L N) (hXH : X ≤ H) (hXab : IsElemAbelian 2 X)
    (hX : 2 < (pCoreOf 2 H).relIndex X) :
    4 ≤ (fixU H U L N X hU hs).relIndex N := by
  obtain ⟨hK, hQ, hnat⟩ := shape_eq_wr hU hs hq hshape
  have hBidx : (thompsonJ H ⊔ pCoreOf 2 H).relIndex H = 2 := by
    have hQ' := hQ
    rw [hK] at hQ'
    exact relIndex_thompsonJ_sup_pCoreOf hQ'
  obtain ⟨F₁, F₂, X₁, X₂, hn₁, hn₂, hF₁H, hF₂H, -, -, hLX₁, hX₁N, hLX₂, hX₂N, hX₁₂, hX₁₂N,
    hF₂X₁, hF₁X₂, hFF, hNat₁, hNat₂⟩ := hnat
  have := hn₁
  have := hn₂
  set B := thompsonJ H ⊔ pCoreOf 2 H with hB
  have hFFB : F₁ ⊔ F₂ = B := by rw [hFF, hK]
  have hBH' : B ≤ H := sup_le (thompsonJ_le_left H) (pCoreOf_le 2 H)
  have hNU : N ≤ U := hs.1.1
  have hLN : L ≤ N := hs.2.2.1.le
  have h4₁ : L.relIndex X₁ = 4 := NatSn.relIndex_eq_four hNat₁
  have h4₂ : L.relIndex X₂ = 4 := NatSn.relIndex_eq_four hNat₂
  have hLL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_isNormalIn hs.2.1
  have hF₁X₁ : ∀ f ∈ F₁, ∀ x ∈ X₁, f * x * f⁻¹ ∈ X₁ := NatSn.normalizes hNat₁
  have hF₂X₂ : ∀ f ∈ F₂, ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂ := NatSn.normalizes hNat₂
  have hF₂X₁' : ∀ f ∈ F₂, ∀ x ∈ X₁, f * x * f⁻¹ ∈ X₁ := by
    intro f hf x hx
    have h := hF₂X₁ f hf x hx
    have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact X₁.mul_mem (hLX₁ h) hx
  have hF₁X₂' : ∀ f ∈ F₁, ∀ x ∈ X₂, f * x * f⁻¹ ∈ X₂ := by
    intro f hf x hx
    have h := hF₁X₂ f hf x hx
    have e : f * x * f⁻¹ = (f * x * f⁻¹ * x⁻¹) * x := by group
    rw [e]
    exact X₂.mul_mem (hLX₂ h) hx
  have hBN₁ : B ≤ Subgroup.normalizer (X₁ : Set G) := by
    calc B = F₁ ⊔ F₂ := hFFB.symm
      _ ≤ _ := sup_le (le_normalizer_of_conj hF₁X₁) (le_normalizer_of_conj hF₂X₁')
  have hBN₂ : B ≤ Subgroup.normalizer (X₂ : Set G) := by
    calc B = F₁ ⊔ F₂ := hFFB.symm
      _ ≤ _ := sup_le (le_normalizer_of_conj hF₁X₂') (le_normalizer_of_conj hF₂X₂)
  have hBX₁ : ∀ b ∈ B, ∀ x ∈ X₁, b * x * b⁻¹ ∈ X₁ := fun b hb x hx =>
    (Subgroup.mem_normalizer_iff.mp (hBN₁ hb) x).mp hx
  have hBX₂ : ∀ b ∈ B, ∀ x ∈ X₂, b * x * b⁻¹ ∈ X₂ := fun b hb x hx =>
    (Subgroup.mem_normalizer_iff.mp (hBN₂ hb) x).mp hx
  have hBnormal : (B.subgroupOf H).Normal := Subgroup.normal_of_index_eq_two hBidx
  have hBH : ∀ σ ∈ H, ∀ b ∈ B, σ * b * σ⁻¹ ∈ B := fun σ hσ b hb =>
    hBnormal.conj_mem ⟨b, hBH' hb⟩ (Subgroup.mem_subgroupOf.mpr hb) ⟨σ, hσ⟩
  have hF₁B : F₁ ≤ B := le_sup_left.trans hFFB.le
  have hIL : ∀ Y : Subgroup G, L ≤ Y → Y ≤ X₁ →
      (∀ f ∈ F₁, ∀ y ∈ Y, f * y * f⁻¹ ∈ Y) → Y = L ∨ Y = X₁ :=
    fun Y a b c => NatSn.irreducible hNat₁ a b c
  have hStab : ∀ σ ∈ H, (∀ x ∈ X₁, σ * x * σ⁻¹ ∈ X₁) → σ ∈ B := by
    intro σ hσH hσ
    by_contra hσB
    obtain ⟨a, haH, haB, ha⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hBidx
    have hσa : σ * a ∈ B := (ha σ hσH).resolve_right hσB
    have hall : ∀ h ∈ H, ∀ x ∈ X₁, h * x * h⁻¹ ∈ X₁ := by
      intro h hh x hx
      by_cases hhB : h ∈ B
      · exact hBX₁ h hhB x hx
      · have hha : h * a ∈ B := (ha h hh).resolve_right hhB
        have hb : h * σ⁻¹ ∈ B := by
          have := B.mul_mem hha (B.inv_mem hσa)
          have e : h * a * (σ * a)⁻¹ = h * σ⁻¹ := by group
          rwa [e] at this
        have e2 : h * x * h⁻¹ = (h * σ⁻¹) * (σ * x * σ⁻¹) * (h * σ⁻¹)⁻¹ := by group
        rw [e2]
        exact hBX₁ _ hb _ (hσ x hx)
    have hIN : IsNormalIn H U X₁ := ⟨hX₁N.trans hNU, hall⟩
    rcases hs.2.2.2 X₁ hIN hLX₁ hX₁N with h | h
    · rw [h, Subgroup.relIndex_self] at h4₁
      omega
    · have : X₂ ≤ X₁ := h ▸ hX₂N
      rw [inf_eq_right.mpr this] at hX₁₂
      rw [hX₁₂, Subgroup.relIndex_self] at h4₂
      omega
  by_cases hXB : X ≤ B
  ·
    have hXX₁ : ∀ x ∈ X, ∀ n ∈ X₁, x * n * x⁻¹ ∈ X₁ := fun x hx n hn => hBX₁ x (hXB hx) n hn
    have hXX₂ : ∀ x ∈ X, ∀ n ∈ X₂, x * n * x⁻¹ ∈ X₂ := fun x hx n hn => hBX₂ x (hXB hx) n hn
    obtain ⟨x₁, hx₁, n₁, hn₁X, hc₁⟩ := exists_nontrivial_action hU hs hK hXH hXab hX hX₂N
      (by rw [sup_comm]; exact hX₁₂N) hLX₂ h4₂ hXX₂
    obtain ⟨x₂, hx₂, n₂, hn₂X, hc₂⟩ := exists_nontrivial_action hU hs hK hXH hXab hX hX₁N
      hX₁₂N hLX₁ h4₁ hXX₁
    have hab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
      F7.isElemAbelian_comm hU (hNU ha) (hNU hb)
    have hN2 : IsPGroup 2 N := (F7.isPGroup_of_isElemAbelian hU).to_le hNU
    have hFdef : fixU H U L N X hU hs = fixMod X L N hab hLN := rfl
    rw [hFdef]
    have h₃ : n₁ ∉ fixMod X L N hab hLN := fun h => hc₁ (h.2 x₁ hx₁)
    have h₄ : n₂ ∉ fixMod X L N hab hLN := fun h => hc₂ (h.2 x₂ hx₂)
    have h₅ : n₁ * n₂⁻¹ ∉ fixMod X L N hab hLN := by
      intro h
      have hL := h.2 x₁ hx₁
      have haX₁ : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∈ X₁ :=
        X₁.mul_mem (hXX₁ x₁ hx₁ n₁ hn₁X) (X₁.inv_mem hn₁X)
      have hbX₂ : x₁ * n₂⁻¹ * x₁⁻¹ * n₂ ∈ X₂ :=
        X₂.mul_mem (hXX₂ x₁ hx₁ _ (X₂.inv_mem hn₂X)) hn₂X
      have hcomm : n₁ * (x₁ * n₂⁻¹ * x₁⁻¹ * n₂) = (x₁ * n₂⁻¹ * x₁⁻¹ * n₂) * n₁ :=
        hab n₁ (hX₁N hn₁X) _ (hX₂N hbX₂)
      have e : x₁ * (n₁ * n₂⁻¹) * x₁⁻¹ * (n₁ * n₂⁻¹)⁻¹ =
          (x₁ * n₁ * x₁⁻¹ * n₁⁻¹) * (x₁ * n₂⁻¹ * x₁⁻¹ * n₂) := by
        calc x₁ * (n₁ * n₂⁻¹) * x₁⁻¹ * (n₁ * n₂⁻¹)⁻¹
            = (x₁ * n₁ * x₁⁻¹ * n₁⁻¹) * (n₁ * (x₁ * n₂⁻¹ * x₁⁻¹ * n₂)) * n₁⁻¹ := by group
          _ = (x₁ * n₁ * x₁⁻¹ * n₁⁻¹) * ((x₁ * n₂⁻¹ * x₁⁻¹ * n₂) * n₁) * n₁⁻¹ := by rw [hcomm]
          _ = (x₁ * n₁ * x₁⁻¹ * n₁⁻¹) * (x₁ * n₂⁻¹ * x₁⁻¹ * n₂) := by group
      rw [e] at hL
      have haX₂ : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∈ X₂ := by
        have h1 := X₂.mul_mem (hLX₂ hL) (X₂.inv_mem hbX₂)
        rwa [mul_inv_cancel_right] at h1
      have : x₁ * n₁ * x₁⁻¹ * n₁⁻¹ ∈ X₁ ⊓ X₂ := ⟨haX₁, haX₂⟩
      rw [hX₁₂] at this
      exact hc₁ this
    exact four_le_relIndex_of_three hN2 (hX₁N hn₁X) (hX₂N hn₂X) h₃ h₄ h₅
  · obtain ⟨σ, hσX, hσB⟩ : ∃ σ ∈ X, σ ∉ B := by
      by_contra hcon
      push Not at hcon
      exact hXB fun a ha => hcon a ha
    exact four_le_relIndex_of_not_mem_base hU hs hXH hLX₁ hX₁N h4₁ hBH hBX₁ hF₁B hIL hStab
      hσX hσB

theorem relIndex_pCoreOf_le_two
    [Finite G] {T M V H : Subgroup G} (hC : Concl319 T M V H True)
    (hq : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)))
    {X : Subgroup G} (hXH : X ≤ H) (hXab : IsElemAbelian 2 X)
    (hX : (Subgroup.centralizer (X : Set G)).relIndex (conjClosure V H) ≤ 8) :
    (pCoreOf 2 H).relIndex X ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨L₁, N₁, L₂, N₂, hs₁, hn₁, hs₂, hn₂, h12⟩ :=
    exists_two_noncentral_of_series hC.chief (le_refl 2)
  have hU := hC.elemAbelian
  have h₁ := four_le_relIndex_of_two_lt hU hs₁ hq (hC.shape trivial L₁ N₁ hs₁ hn₁) hXH hXab hlt
  have h₂ := four_le_relIndex_of_two_lt hU hs₂ hq (hC.shape trivial L₂ N₂ hs₂ hn₂) hXH hXab hlt
  have := relIndex_centralizer_ge_sixteen hU hXH hs₁ hs₂ h12 h₁ h₂
  omega

end S152Fin

end CFSG.Quasithin
