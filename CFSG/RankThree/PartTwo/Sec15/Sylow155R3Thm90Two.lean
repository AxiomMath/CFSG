module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Q
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3CtxDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank

theorem exists_second_point_aux {A : Type*} [Group A] [Finite A] (hA27 : Nat.card A = 27)
    (H : Subgroup (MulAut A)) (hH3 : ∀ σ ∈ H, σ ^ 3 = 1)
    (hHc : ∀ σ ∈ H, ∀ τ ∈ H, σ * τ = τ * σ) {c d : A} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hd : ∀ σ ∈ H, σ d = d)
    (hfix : ∃ σ₁ ∈ H, ∃ σ₂ ∈ H, σ₁ ≠ σ₂ ∧ Subgroup.zpowers (σ₁ c) = Subgroup.zpowers (σ₂ c))
    (hmove : ∃ σ ∈ H, Subgroup.zpowers (σ c) ≠ Subgroup.zpowers c) :
    ∃ σ ∈ H, Subgroup.zpowers (σ c) ≠ Subgroup.zpowers c ∧
      d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (σ c) := by
  obtain ⟨σ₁, h1, σ₂, h2, hne, hz⟩ := hfix
  obtain ⟨σ, hσH, hσ⟩ := hmove
  refine ⟨σ, hσH, hσ, ?_⟩
  obtain ⟨s, hs⟩ : ∃ s : MulAut A, s = σ₁⁻¹ * σ₂ := ⟨_, rfl⟩
  have hsH : s ∈ H := by rw [hs]; exact H.mul_mem (H.inv_mem h1) h2
  have hs1 : s ≠ 1 := fun h => hne (inv_mul_eq_one.mp (hs ▸ h))
  have hsc : s c = c := by
    have hmem : σ₂ c ∈ Subgroup.zpowers (σ₁ c) := by
      rw [hz]; exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h3 : s c ∈ Subgroup.zpowers c := by
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h4 : s c = σ₁⁻¹ (σ₂ c) := by rw [hs]; rfl
      rw [h4, ← hk, map_zpow]
      simp
    exact fix_of_mem_zpowers s (hH3 s hsH) hc3 h3
  have hσc : s (σ c) = σ c := by
    have := congrArg (fun τ : MulAut A => τ c) (hHc s hsH σ hσH)
    simpa [hsc] using this
  have hF : fixedSubgroup s ≠ ⊤ := fun h => hs1 (by
    ext a
    have : a ∈ fixedSubgroup s := h ▸ Subgroup.mem_top a
    exact mem_fixedSubgroup.mp this)
  have hcF : c ∈ fixedSubgroup s := mem_fixedSubgroup.mpr hsc
  have hσcF : σ c ∈ fixedSubgroup s := mem_fixedSubgroup.mpr hσc
  have hdF : d ∈ fixedSubgroup s := mem_fixedSubgroup.mpr (hd s hsH)
  have hord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have hcard1 : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hord]
  have hσc3 : (σ c) ^ 3 = 1 := by rw [← map_pow, hc3, map_one]
  have hσc1 : σ c ≠ 1 := fun h => hc1 (σ.injective (by rw [h, map_one]))
  have hcard2 : Nat.card (Subgroup.zpowers (σ c)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hσc3 hσc1]
  have hlt : Subgroup.zpowers c < Subgroup.zpowers c ⊔ Subgroup.zpowers (σ c) := by
    refine lt_of_le_of_ne le_sup_left fun h => hσ ?_
    have hle : Subgroup.zpowers (σ c) ≤ Subgroup.zpowers c := le_of_le_of_eq le_sup_right h.symm
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hdiv27 : ∀ n : ℕ, n ∣ 27 → n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 := by
    intro n hn
    have hle : n ≤ 27 := Nat.le_of_dvd (by norm_num) hn
    interval_cases n <;> omega
  have key : ∀ B : Subgroup A, Subgroup.zpowers c < B → B ≤ fixedSubgroup s →
      B = fixedSubgroup s := by
    intro B hcB hBF
    have hBgt : 3 < Nat.card B := by
      by_contra hle
      push_neg at hle
      exact hcB.ne (Subgroup.eq_of_le_of_card_ge hcB.le (by omega))
    have hBdvd : Nat.card B ∣ 27 := by
      rw [← hA27]; exact Subgroup.card_subgroup_dvd_card B
    have hFdvd : Nat.card (fixedSubgroup s) ∣ 27 := by
      rw [← hA27]; exact Subgroup.card_subgroup_dvd_card _
    have hBd := hdiv27 _ hBdvd
    have hFd := hdiv27 _ hFdvd
    have hF27 : Nat.card (fixedSubgroup s) ≠ 27 := fun h27 =>
      hF (Subgroup.eq_top_of_card_eq _ (by rw [h27, hA27]))
    have hBle : Nat.card B ≤ Nat.card (fixedSubgroup s) := Subgroup.card_le_of_le hBF
    exact Subgroup.eq_of_le_of_card_ge hBF (by omega)
  have hB := key _ hlt (sup_le (Subgroup.zpowers_le.mpr hcF) (Subgroup.zpowers_le.mpr hσcF))
  rw [hB]
  exact hdF

variable {G : Type} [Group G] [Finite G]

theorem second_point {A : Subgroup G} {c : G} {L : Subgroup G} {d : G} {K : Subgroup G}
    (h : Res3Ctx A c L d K) :
    ∃ w : G, w ∈ Subgroup.normalizer (A : Set G) ∧ w * d * w⁻¹ = d ∧
      d ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers (w * c * w⁻¹) := by
  have hAe := h.R.toSec13Data.isElemAbelian
  have hA27 : Nat.card A = 27 := h.R.toSec13Data.card_eq
  have hc3 : c ^ 3 = 1 := hAe.2 c h.c_mem
  have hd3 : d ^ 3 = 1 := hAe.2 d h.d_mem
  have hord : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact (mem_omegaA_iff.mp h.R.zpowers_mem_omegaA).2.1
  have hc1 : c ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hord; omega
  obtain ⟨cA, hcA⟩ : ∃ cA : A, (cA : G) = c := ⟨⟨c, h.c_mem⟩, rfl⟩
  obtain ⟨dA, hdA⟩ : ∃ dA : A, (dA : G) = d := ⟨⟨d, h.d_mem⟩, rfl⟩
  have hcA3 : cA ^ 3 = 1 := Subtype.ext (by simpa [hcA] using hc3)
  have hcA1 : cA ≠ 1 := fun h1 => hc1 (by simpa [hcA] using congrArg Subtype.val h1)
  have hdA3 : dA ^ 3 = 1 := Subtype.ext (by simpa [hdA] using hd3)
  have hH3 : ∀ σ ∈ oThreeWStar A, σ ^ 3 = 1 := h.Pstar_elem.2
  have hHc : ∀ σ ∈ oThreeWStar A, ∀ τ ∈ oThreeWStar A, σ * τ = τ * σ := fun σ hσ τ hτ =>
    congrArg Subtype.val (h.Pstar_elem.1.is_comm.comm ⟨σ, hσ⟩ ⟨τ, hτ⟩)
  have hex : ∀ σ ∈ oThreeWStar A, ∃ w : G, w ∈ Subgroup.normalizer (A : Set G) ∧
      w ∈ oThreeWPre A ∧ ∀ a : A, ((σ a : A) : G) = w * a * w⁻¹ := by
    intro σ hσ
    have hσW : σ ∈ wStar A := by
      obtain ⟨σ', -, rfl⟩ := hσ
      exact σ'.2
    obtain ⟨g, hN, -, hgσ⟩ := Sec4.mem_autIn_iff.mp hσW
    refine ⟨g, hN, ⟨⟨g, hN⟩, ?_, rfl⟩, fun a => ?_⟩
    · show A.normalizerMonoidHom ⟨g, hN⟩ ∈ oThreeWStar A
      rw [hgσ]
      exact hσ
    · rw [← hgσ]
      rfl
  choose! w hwN hwP hwσ using hex
  have hmapσ : ∀ (σ : MulAut A) (x : G), (∀ a : A, ((σ a : A) : G) = x * a * x⁻¹) →
      (Subgroup.zpowers (σ cA)).map A.subtype =
        (Subgroup.zpowers c).map (MulAut.conj x).toMonoidHom := fun σ x hx => by
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    congr 1
    show ((σ cA : A) : G) = x * c * x⁻¹
    rw [hx cA, hcA]
  have hmapc : (Subgroup.zpowers cA).map A.subtype = Subgroup.zpowers c := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hcA
  have hdfix : ∀ σ ∈ oThreeWStar A, σ dA = dA := by
    intro σ hσ
    have hmem : σ dA ∈ Subgroup.zpowers dA := by
      rw [← Subgroup.mem_map_iff_mem A.subtype_injective, MonoidHom.map_zpowers]
      change ((σ dA : A) : G) ∈ Subgroup.zpowers ((dA : A) : G)
      rw [hwσ σ hσ dA, hdA]
      exact (Subgroup.mem_normalizer_iff.mp (h.NA (hwN σ hσ)) d).mp (Subgroup.mem_zpowers d)
    exact fix_of_mem_zpowers σ (hH3 σ hσ) hdA3 hmem
  have hfin : (omegaA A).Finite := Set.finite_of_ncard_ne_zero (by rw [h.ncard]; norm_num)
  have hlt : (omegaA A).ncard <
      ((oThreeWStar A : Subgroup (MulAut A)) : Set (MulAut A)).ncard := by
    rw [h.ncard, ← Nat.card_coe_set_eq]
    change 3 < Nat.card (oThreeWStar A)
    rw [h.Pstar_card]
    norm_num
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hne, heq⟩ := Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt
    (f := fun σ => (Subgroup.zpowers c).map (MulAut.conj (w σ)).toMonoidHom)
    (fun σ hσ => by
      rw [h.omega]
      exact ⟨w σ, hwP σ hσ, rfl⟩) hfin
  have hfix : ∃ σ₁ ∈ oThreeWStar A, ∃ σ₂ ∈ oThreeWStar A, σ₁ ≠ σ₂ ∧
      Subgroup.zpowers (σ₁ cA) = Subgroup.zpowers (σ₂ cA) := by
    refine ⟨σ₁, hσ₁, σ₂, hσ₂, hne, ?_⟩
    apply Subgroup.map_injective A.subtype_injective
    rw [hmapσ σ₁ (w σ₁) (hwσ σ₁ hσ₁), hmapσ σ₂ (w σ₂) (hwσ σ₂ hσ₂)]
    exact heq
  have hmove : ∃ σ ∈ oThreeWStar A, Subgroup.zpowers (σ cA) ≠ Subgroup.zpowers cA := by
    obtain ⟨F, hF, hFne⟩ := Set.exists_ne_of_one_lt_ncard (s := omegaA A)
      (by rw [h.ncard]; norm_num) (Subgroup.zpowers c)
    rw [h.omega] at hF
    obtain ⟨x, hxP, rfl⟩ := hF
    obtain ⟨hxN, hxσ⟩ : ∃ hxN : x ∈ Subgroup.normalizer (A : Set G),
        A.normalizerMonoidHom ⟨x, hxN⟩ ∈ oThreeWStar A := by
      obtain ⟨n, hn, hnx⟩ := hxP
      subst hnx
      exact ⟨n.2, hn⟩
    refine ⟨A.normalizerMonoidHom ⟨x, hxN⟩, hxσ, fun hcon => hFne ?_⟩
    rw [← hmapσ (A.normalizerMonoidHom ⟨x, hxN⟩) x (fun a => rfl), hcon, hmapc]
  obtain ⟨σ, hσH, -, hσd⟩ := exists_second_point_aux hA27 (oThreeWStar A) hH3 hHc hcA3 hcA1
    hdfix hfix hmove
  refine ⟨w σ, hwN σ hσH, ?_, ?_⟩
  · have h1 := hwσ σ hσH dA
    rw [hdfix σ hσH, hdA] at h1
    exact h1.symm
  · have h2 : A.subtype dA ∈ (Subgroup.zpowers cA ⊔ Subgroup.zpowers (σ cA)).map A.subtype :=
      Subgroup.mem_map_of_mem _ hσd
    have h3 : A.subtype dA = d := hdA
    rw [h3, Subgroup.map_sup, hmapc, hmapσ σ (w σ) (hwσ σ hσH), MonoidHom.map_zpowers] at h2
    exact h2

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
