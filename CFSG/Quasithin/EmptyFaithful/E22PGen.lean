module

public import CFSG.Quasithin.Background.E1Solv

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b

variable {G : Type*} [Group G] [Finite G]

theorem le_eGen_sup_normalizer_of_inEFor {n : ℕ} {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hTD : T ≤ D) (hD : InEFor n D T) {Ω : Set (Subgroup G)} (hΩ : IsInvColl ⊤ Ω) :
    D ≤ eGen n ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) := by
  have hTD' : IsSylowIn 2 T D := B6.isSylowTwoOf_mono hT hTD le_top
  set ΩD : Set (Subgroup G) := {A | A ∈ Ω ∧ A ≤ D} with hΩD
  have hΩD' : IsInvColl D ΩD := by
    refine ⟨fun A hA => hA.2, fun A hA => hΩ.isElemAbelian A hA.1, fun A hA d hd => ?_⟩
    refine ⟨hΩ.conj A hA.1 d (Subgroup.mem_top d), ?_⟩
    intro x hx
    have hx' := mem_conjSub_iff.mp hx
    have : d⁻¹ * x * d ∈ D := hA.2 hx'
    have hd' : d * (d⁻¹ * x * d) * d⁻¹ ∈ D := D.mul_mem (D.mul_mem hd this) (D.inv_mem hd)
    simpa [mul_assoc] using hd'
  have hWeq : weakClosure T ΩD = weakClosure T Ω := by
    refine le_antisymm (iSup₂_le fun A hA => iSup_le fun hAT => ?_) ?_
    · exact le_iSup₂_of_le A hA.1 (le_iSup_of_le hAT le_rfl)
    · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
      exact le_iSup₂_of_le A ⟨hA, hAT.trans hTD⟩ (le_iSup_of_le hAT le_rfl)
  have hgen : eGen n D T ΩD ≤ eGen n ⊤ T Ω := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
    have hK' : IsE n ⊤ T A K := by
      refine eight_two (H₁ := ⊤) (H₂ := D) hT hAT (hΩ.isElemAbelian A hA.1) le_top
        ((tauOf_le ⊤ T A).trans (le_inf le_rfl hTD)) ?_ ?_
      · rw [inf_eq_left.mpr hTD]; exact hTD'
      · rw [inf_eq_left.mpr hTD]; exact hK
    exact le_iSup₂_of_le A hA.1 (le_iSup_of_le hAT (le_iSup₂_of_le K hK' le_rfl))
  have hDD := hD ΩD hΩD'
  rw [hWeq] at hDD
  exact hDD.ge.trans (sup_le_sup hgen (inf_le_inf_right _ le_top))

theorem le_eGen_sup_normalizer_of_isSolvable {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hTD : T ≤ D) (hD : Group.IsSolvable ↥D) {Ω : Set (Subgroup G)} (hΩ : IsInvColl ⊤ Ω) :
    D ≤ eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) := by
  have h1 : InE 1 D := (nParam_le_iff (H := D) (n := 1) Nat.one_pos).mp
    (by simpa using solvable_nParam_le_one hD)
  exact le_eGen_sup_normalizer_of_inEFor hT hTD (h1 T (B6.isSylowTwoOf_mono hT hTD le_top)) hΩ

theorem exists_conjSub_le_of_isSylowIn {T A : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hA : IsPGroup 2 A) : ∃ g : G, conjSub g A ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hAS⟩ := exists_isSylowIn_ge 2 (le_top : A ≤ ⊤) hA
  obtain ⟨g, -, hgS⟩ := B6.isSylowTwoOf_exists_conj hT hS
  refine ⟨g⁻¹, fun x hx => ?_⟩
  have hx' := mem_conjSub_iff.mp hx
  have h1 : g⁻¹⁻¹ * x * g⁻¹ ∈ S := hAS hx'
  rw [hgS, B6.mem_conjSub] at h1
  simpa [mul_assoc] using h1

omit [Finite G] in
theorem card_conjSub_eq (g : G) (A : Subgroup G) : Nat.card (conjSub g A) = Nat.card A :=
  Nat.card_congr (Subgroup.equivMapOfInjective A (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv.symm

theorem inEFor_top_of_noTwo {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hII : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤)
    (h : ∀ Ω : Set (Subgroup G), IsInvColl ⊤ Ω → (∀ A ∈ Ω, Nat.card A ≠ 2) →
      eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) = ⊤) :
    InEFor 1 ⊤ T := by
  intro Ω hΩ
  by_cases h2 : ∃ A ∈ Ω, Nat.card A = 2
  · obtain ⟨A, hA, hcard⟩ := h2
    obtain ⟨g, hg⟩ := exists_conjSub_le_of_isSylowIn hT
      (isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA))
    have hA' : conjSub g A ∈ Ω := hΩ.conj A hA g (Subgroup.mem_top g)
    have hcard' : Nat.card (conjSub g A) = 2 := by rw [card_conjSub_eq, hcard]
    have hle := le_eGen (H := ⊤) (i := 1) hA' hg (hII _ hg hcard')
    rw [top_le_iff] at hle
    rw [hle, top_sup_eq]
  · push Not at h2
    exact h Ω hΩ h2

theorem inEFor_top_of_coatom {T D : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hTD : T ≤ D)
    (hDs : Group.IsSolvable ↥D) (hD : IsCoatom D)
    (hII : ∀ A : Subgroup G, A ≤ T → Nat.card A = 2 → IsE 1 ⊤ T A ⊤)
    (hK : ∀ A : Subgroup G, A ≤ T → IsElemAbelian 2 A → 4 ≤ Nat.card A →
      ∃ K : Subgroup G, IsE 1 ⊤ T A K ∧ ¬ K ≤ D) : InEFor 1 ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine inEFor_top_of_noTwo hT hII ?_
  intro Ω hΩ h2
  by_cases h4 : ∃ A ∈ Ω, A ≤ T ∧ 4 ≤ Nat.card A
  · obtain ⟨A, hA, hAT, hA4⟩ := h4
    obtain ⟨K, hK1, hK2⟩ := hK A hAT (hΩ.isElemAbelian A hA) hA4
    have hDX := le_eGen_sup_normalizer_of_isSolvable hT hTD hDs hΩ
    have hKX := (le_eGen hA hAT hK1).trans (le_sup_left :
      eGen 1 ⊤ T Ω ≤ eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)))
    have hlt : D < eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (weakClosure T Ω : Set G)) :=
      lt_of_le_of_ne hDX fun h => hK2 (h ▸ hKX)
    exact hD.2 _ hlt
  · push Not at h4
    have hW : weakClosure T Ω = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
      have hp := isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA)
      obtain ⟨k, hk⟩ := hp.exists_card_eq
      have h4' := h4 A hA hAT
      have h2' := h2 A hA
      rcases k with _ | _ | k
      · exact le_bot_iff.mpr (Subgroup.card_eq_one.mp (by simpa using hk))
      · exact absurd (by simpa using hk) h2'
      · exfalso
        apply h4'.not_ge
        rw [hk]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hW, Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_top_eq]

end E1

end CFSG.Quasithin
