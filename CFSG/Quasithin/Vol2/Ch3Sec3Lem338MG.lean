module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem338MF
public import CFSG.Quasithin.Background.B4L3Syl

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch3Sec3

variable {V : Type} [CommGroup V]

theorem card_conjSub (y : MulAut V) (K : Subgroup (MulAut V)) :
    Nat.card ↥(conjSub y K) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj y).injective

theorem card_map_aut (y : MulAut V) (U : Subgroup V) :
    Nat.card ↥(U.map y.toMonoidHom) = Nat.card ↥U :=
  Subgroup.card_map_of_injective y.injective

theorem sl2_card_ne {q n : ℕ} (hq : q = 2 ^ n) (h4 : 4 ≤ q) : q * (q ^ 2 - 1) ≠ 168 := by
  intro h
  have hq5 : q ≤ 5 := by
    by_contra h5
    have h1 : 6 * (6 ^ 2 - 1) ≤ q * (q ^ 2 - 1) := by
      have : 6 ^ 2 - 1 ≤ q ^ 2 - 1 := Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1
      exact Nat.mul_le_mul (by omega) this
    omega
  interval_cases q
  · norm_num at h
  · have : (5 : ℕ) ≠ 2 ^ n := by
      intro h5
      rcases Nat.lt_or_ge n 3 with hn | hn
      · interval_cases n <;> simp_all
      · have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
    exact this hq

section Case5

variable [Finite V] {J K₁ K₂ : Subgroup (MulAut V)}
  (hq₁ : CFSG.IsQuasisimple ↥K₁) (hs₁ : IsSimpleGroup ↥K₁) (hq₂ : CFSG.IsQuasisimple ↥K₂)
  (hs₂ : IsSimpleGroup ↥K₂) (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a) (hinf : K₁ ⊓ K₂ = ⊥)
  (hK₁J : K₁ ≤ J) (hK₂J : K₂ ≤ J)
  (hJK : J ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup (MulAut V)) : Set (MulAut V)))
  {s : MulAut V} (hs₁₂ : conjSub s K₂ = K₁) (hs₂₁ : conjSub s K₁ = K₂)

include hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hs₁₂ hs₂₁ in
theorem case5_core (h5 : B56Case5 J) :
    (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) ⊓ (commV K₂ ⊔ fixV (K₁ ⊔ K₂)) = fixV (K₁ ⊔ K₂) ∧
      ModType K₁ (commV K₁ ⊔ fixV (K₁ ⊔ K₂)) (fixV (K₁ ⊔ K₂)) := by
  obtain ⟨G₁, G₂, hsup, hinf₁₂, hc₁₂, hdir, ⟨e₁⟩, hcard₁, -, h₂⟩ := h5
  have hF2 : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hf₁ : B56FactorList ↥G₁ :=
    Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, hF2, ⟨e₁⟩⟩)
  have hP₁ : Group.IsPerfect ↥G₁ := isPerfect_of_equiv isPerfect_statedSL_three e₁.symm
  have hcK : Nat.card ↥(commV K₁) = Nat.card ↥(commV K₂) := by
    rw [← hs₁₂, commV_conjSub, card_map_aut]
  have hKK : Nat.card ↥K₁ = Nat.card ↥K₂ := by rw [← hs₁₂, card_conjSub]
  set Z := fixV (K₁ ⊔ K₂) with hZ
  have hsZ : Z.map s.toMonoidHom = Z := by
    rw [hZ, ← fixV_conjSub, conjSub_sup, hs₁₂, hs₂₁, sup_comm]
  rcases h₂ with ⟨⟨e₂⟩, k, hk, hsum⟩ | ⟨n, hbn⟩
  ·
    have hf₂ : B56FactorList ↥G₂ :=
      Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, hF2, ⟨e₂⟩⟩)
    have hP₂ : Group.IsPerfect ↥G₂ := isPerfect_of_equiv isPerfect_statedSL_three e₂.symm
    have hKG : (K₁ = G₁ ∧ K₂ = G₂) ∨ (K₁ = G₂ ∧ K₂ = G₁) := by
      rcases assign hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hsup hinf₁₂ hc₁₂ hf₁ hf₂ with
        ⟨h11, h22⟩ | ⟨h12, h21⟩
      · exact Or.inl ⟨eq_of_isPerfect h11.1 h11.2 hP₁, eq_of_isPerfect h22.1 h22.2 hP₂⟩
      · exact Or.inr ⟨eq_of_isPerfect h12.1 h12.2 hP₂, eq_of_isPerfect h21.1 h21.2 hP₁⟩
    have hcG : Nat.card ↥(commV G₂) = 8 := by
      rcases hKG with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← hcK, hcard₁]; rfl
      · rw [hcK, hcard₁]; rfl
    have hR : ∃ π : (FFModel.nat (StatedSL 3 (ZMod 2))).Gam →* ↥G₂,
        (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia G₂ (commV G₂) ⊥ π := by
      obtain ⟨I, π, -, hind, hsupI, hreal⟩ := hsum
      interval_cases k
      · exfalso
        have h0 : commV G₂ = ⊥ := by
          rw [← hsupI]
          simp
        rw [h0, Subgroup.card_bot] at hcG
        omega
      · have h1 : commV G₂ = I 0 := by
          rw [← hsupI]
          refine le_antisymm (sup_le bot_le (iSup_le fun i => ?_)) (le_sup_of_le_right
            (le_iSup I 0))
          rw [Subsingleton.elim i 0]
        exact ⟨π, h1 ▸ hreal 0⟩
      · exfalso
        have h01 : I 0 ⊓ I 1 = ⊥ := by
          have h0 := hind 0
          have hs1 : (⨆ (j : Fin 2) (_ : j ≠ 0), I j) = I 1 := by
            refine le_antisymm (iSup₂_le fun j hj => ?_)
              (le_iSup₂_of_le (1 : Fin 2) (by decide) le_rfl)
            fin_cases j
            · exact absurd rfl hj
            · exact le_rfl
          rwa [hs1, bot_sup_eq] at h0
        have hc0 := card_of_nat_three (by rw [Nat.card_zmod]) (hreal 0)
        have hc1 := card_of_nat_three (by rw [Nat.card_zmod]) (hreal 1)
        rw [Subgroup.card_bot, mul_one] at hc0 hc1
        have hle : I 0 ⊔ I 1 ≤ commV G₂ := by
          rw [← hsupI]
          exact le_sup_of_le_right (sup_le (le_iSup I 0) (le_iSup I 1))
        have hlt : I 0 < I 0 ⊔ I 1 := by
          refine lt_of_le_of_ne le_sup_left fun h => ?_
          have h1 : I 1 ≤ I 0 := h ▸ le_sup_right
          have : I 1 = ⊥ := by rw [eq_bot_iff, ← h01]; exact le_inf h1 le_rfl
          rw [this, Subgroup.card_bot] at hc1
          omega
        have h2 : Nat.card ↥(I 0) < Nat.card ↥(I 0 ⊔ I 1) :=
          lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left)
            fun h => hlt.ne (Subgroup.eq_of_le_of_card_ge le_sup_left h.ge)
        have h3 := Subgroup.card_le_of_le hle
        omega
    obtain ⟨π, hπ⟩ := hR
    have hG₂K : G₂ ≤ K₁ ⊔ K₂ := by
      rcases hKG with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact le_sup_right
      · exact le_sup_left
    have hG₂J : G₂ ≤ J := by rw [← hsup]; exact le_sup_right
    have hcZ : commV G₂ ⊓ Z = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx, hxZ⟩
      refine mem_of_forall_mul_inv_mem hπ (nat_fix (by norm_num)) hx fun g hg => ?_
      rw [hxZ g (hG₂K hg), mul_inv_cancel]
      exact Subgroup.one_mem _
    have hZinv : ∀ g : ↥G₂, ∀ z ∈ Z, (g : MulAut V) z ∈ Z := fun g z hz =>
      apply_mem_fixV (hJK (hG₂J g.2)) hz
    have hR₂ := realizesVia_sup hπ hcZ hZinv
    have hsG : conjSub s G₂ = G₁ := by
      rcases hKG with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hs₁₂
      · exact hs₂₁
    obtain ⟨π₁, hR₁⟩ := realizesVia_conj' s hR₂ hsG
      (by rw [Subgroup.map_sup, ← commV_conjSub, hsG, hsZ]) hsZ
    have hcZ₁ : commV G₁ ⊓ Z = ⊥ := by
      rw [← hsG, commV_conjSub, ← hsZ, ← Subgroup.map_inf_eq _ _ s.toMonoidHom s.injective, hcZ,
        Subgroup.map_bot]
    have hnat₁ : BinaryNaturalSL G₁ (commV G₁ ⊔ Z) Z 3 1 :=
      ⟨ZMod 2, inferInstance, inferInstance, hF2, π₁, hR₁⟩
    have hnat₂ : BinaryNaturalSL G₂ (commV G₂ ⊔ Z) Z 3 1 :=
      ⟨ZMod 2, inferInstance, inferInstance, hF2, π, hR₂⟩
    have hcc : commV G₁ ⊓ commV G₂ = ⊥ := hdir.2
    have key : ∀ {A B : Subgroup (MulAut V)}, (A = K₁ ∧ B = K₂ ∨ A = K₂ ∧ B = K₁) →
        commV A ⊓ commV B = ⊥ → commV A ⊓ Z = ⊥ →
        (commV A ⊔ Z) ⊓ (commV B ⊔ Z) = Z := by
      intro A B hAB hAB' hAZ
      have hBA : B ≤ Subgroup.normalizer (A : Set (MulAut V)) := by
        rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact le_normalizer_of_commute hc
        · exact le_normalizer_of_commute fun a ha b hb => (hc b hb a ha).symm
      have hAB'' : A ≤ Subgroup.normalizer (B : Set (MulAut V)) := by
        rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact le_normalizer_of_commute fun a ha b hb => (hc b hb a ha).symm
        · exact le_normalizer_of_commute hc
      have hsupAB : A ⊔ B = K₁ ⊔ K₂ := by
        rcases hAB with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact sup_comm _ _
      refine le_antisymm (fun x ⟨hx₁, hx₂⟩ => ?_) (le_inf le_sup_right le_sup_right)
      obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx₁
      obtain ⟨b, hb, z', hz', e⟩ := Subgroup.mem_sup.mp hx₂
      have hBa : ∀ g ∈ B, g a = a := by
        intro g hg
        have h1 : g a * a⁻¹ ∈ commV A ⊓ commV B :=
          ⟨(commV A).mul_mem (apply_mem_commV (hBA hg) ha) ((commV A).inv_mem ha),
            gen_mem_commV hg a⟩
        rw [hAB', Subgroup.mem_bot, mul_inv_eq_one] at h1
        exact h1
      have hAb : ∀ g ∈ A, g b = b := by
        intro g hg
        have h1 : g b * b⁻¹ ∈ commV A ⊓ commV B :=
          ⟨gen_mem_commV hg b,
            (commV B).mul_mem (apply_mem_commV (hAB'' hg) hb) ((commV B).inv_mem hb)⟩
        rw [hAB', Subgroup.mem_bot, mul_inv_eq_one] at h1
        exact h1
      have hab : a * b⁻¹ = z' * z⁻¹ := by
        calc a * b⁻¹ = (a * z) * z⁻¹ * b⁻¹ := by group
          _ = (b * z') * z⁻¹ * b⁻¹ := by rw [e]
          _ = b * (z' * z⁻¹) * b⁻¹ := by group
          _ = z' * z⁻¹ := by rw [mul_comm b, mul_assoc, mul_inv_cancel, mul_one]
      have hZab : a * b⁻¹ ∈ Z := hab ▸ Z.mul_mem hz' (Z.inv_mem hz)
      have haZ : a ∈ Z := by
        have hA' : a ∈ fixV A := by
          intro g hg
          have h1 := hZab g (hsupAB ▸ Subgroup.mem_sup_left hg)
          rw [map_mul, map_inv, hAb g hg] at h1
          exact mul_right_cancel h1
        have hB' : a ∈ fixV B := fun g hg => hBa g hg
        rw [hZ, ← hsupAB]
        exact mem_fixV_sup hA' hB'
      have ha1 : a = 1 := by
        have : a ∈ commV A ⊓ Z := ⟨ha, haZ⟩
        rwa [hAZ, Subgroup.mem_bot] at this
      rw [ha1, one_mul]
      exact hz
    rcases hKG with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨key (Or.inl ⟨rfl, rfl⟩) hcc hcZ₁, Or.inr (Or.inr (Or.inl hnat₁))⟩
    · exact ⟨key (Or.inl ⟨rfl, rfl⟩) (by rw [inf_comm]; exact hcc) hcZ,
        Or.inr (Or.inr (Or.inl hnat₂))⟩
  ·
    exfalso
    obtain ⟨F, _, _, hF, π, hπ⟩ := hbn
    have hinj := injective_of_nat hπ
    obtain ⟨e₂⟩ : Nonempty (↥G₂ ≃* ↥(StatedSL 2 F)) :=
      ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩
    have hf₂ : B56FactorList ↥G₂ :=
      Or.inl ⟨n, F, inferInstance, inferInstance, Hyp331.one_le_of_card hF, hF, ⟨e₂⟩⟩
    have hcard₂ : Nat.card ↥G₂ = Nat.card F * (Nat.card F ^ 2 - 1) := by
      rw [Nat.card_congr e₂.toEquiv, ← Nat.card_congr (specialLinearGroupEquivStatedSL 2 F).toEquiv,
        CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
    have hc168 : Nat.card ↥G₁ = 168 := by
      rw [Nat.card_congr e₁.toEquiv,
        ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 (ZMod 2)).toEquiv]
      exact card_L3Γ
    have hF4 : 4 ≤ Nat.card F ∨ Nat.card F = 2 := by
      have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
      rcases Nat.lt_or_ge (Nat.card F) 4 with h | h
      · right
        have h3 : Nat.card F ≠ 3 := by
          intro h3
          rw [h3] at hF
          rcases Nat.lt_or_ge n 2 with hn | hn
          · interval_cases n <;> simp_all
          · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
            omega
        omega
      · exact Or.inl h
    have hG₂ : ∀ K : Subgroup (MulAut V), CFSG.IsQuasisimple ↥K → InCore K G₂ →
        Nat.card ↥K = Nat.card F * (Nat.card F ^ 2 - 1) := by
      intro K hq hK
      rcases hF4 with h4 | h2
      · rw [eq_of_isPerfect hK.1 hK.2 (isPerfect_of_surjective (isPerfect_statedSL_two h4) π hπ.1),
          hcard₂]
      · exfalso
        apply not_isSolvable_of_isQuasisimple hq
        have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :=
          isSolvable_sl_two_zmodTwo
        have : Group.IsSolvable ↥(StatedSL 2 F) :=
          Group.isSolvable_of_surjective (f := (statedSLEquivZModTwo (n := 2) h2).symm.toMonoidHom)
            (statedSLEquivZModTwo (n := 2) h2).symm.surjective
        have : Group.IsSolvable (FFModel.nat (StatedSL 2 F)).Gam := this
        have : Group.IsSolvable ↥G₂ := Group.isSolvable_of_surjective (f := π) hπ.1
        exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hK.1)
    have hne : Nat.card F * (Nat.card F ^ 2 - 1) ≠ 168 := by
      rcases hF4 with h4 | h2
      · exact sl2_card_ne hF h4
      · rw [h2]; norm_num
    rcases assign hq₁ hs₁ hq₂ hs₂ hc hinf hK₁J hK₂J hJK hsup hinf₁₂ hc₁₂ hf₁ hf₂ with
      ⟨h11, h22⟩ | ⟨h12, h21⟩
    · apply hne
      rw [← hG₂ K₂ hq₂ h22, ← hKK, eq_of_isPerfect h11.1 h11.2 hP₁, hc168]
    · apply hne
      rw [← hG₂ K₁ hq₁ h12, hKK, eq_of_isPerfect h21.1 h21.2 hP₁, hc168]

end Case5

end CFSG.Quasithin.H13.M338
