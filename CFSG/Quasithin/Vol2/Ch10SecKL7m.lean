module

public import CFSG.Quasithin.Vol2.Ch10SecKL7l

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem eq_one_or_of_sq {G : Type*} [Group G] {t y : G} (ht : t ^ 2 = 1)
    (hy : y ∈ Subgroup.zpowers t) : y = 1 ∨ y = t := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht
  let S : Subgroup G :=
    { carrier := {1, t}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
        · exact Or.inl (one_mul 1)
        · exact Or.inr (one_mul t)
        · exact Or.inr (mul_one t)
        · exact Or.inl htt
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with ha | ha <;> rw [ha]
        · exact Or.inl inv_one
        · exact Or.inr (inv_eq_of_mul_eq_one_right htt) }
  exact (Subgroup.zpowers_le.2 (show t ∈ S from Or.inr rfl)) hy

variable {W : Type} [CommGroup W]

namespace Hyp

variable {Mb L₁ L₂ R : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}
variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem fixV_eq_of_fixM (c₁ : Coord L₁ W₁) {γ δ : SL32} (hγδ : fixM γ = fixM δ) :
    fixV (Subgroup.zpowers ((c₁.π γ : ↥L₁) : MulAut W)) =
      fixV (Subgroup.zpowers ((c₁.π δ : ↥L₁) : MulAut W)) := by
  suffices key : ∀ γ δ : SL32, fixM γ = fixM δ →
      fixV (Subgroup.zpowers ((c₁.π γ : ↥L₁) : MulAut W)) ≤
        fixV (Subgroup.zpowers ((c₁.π δ : ↥L₁) : MulAut W)) from
    le_antisymm (key γ δ hγδ) (key δ γ hγδ.symm)
  intro γ δ hγδ w hw
  rw [mem_fixV_zp] at hw ⊢
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 (h.sup ▸ Subgroup.mem_top w)
  have hfa : ∀ ε : SL32, ((c₁.π ε : ↥L₁) : MulAut W) (a * b) = a * b ↔
      ((c₁.π ε : ↥L₁) : MulAut W) a = a := fun ε => by
    rw [map_mul, h.fix₁ _ (c₁.π ε).2 b hb, mul_left_inj]
  rw [hfa] at hw ⊢
  obtain ⟨v, rfl⟩ := c₁.exists_Ψ ha
  rw [c₁.fix_iff] at hw ⊢
  intro i
  have hvi : v i ∈ fixM γ := mem_fixM.2 (hw i)
  rw [hγδ] at hvi
  exact mem_fixM.1 hvi

theorem aSet_two_nonempty : (E3.aSet 2 Mb).Nonempty := by
  obtain ⟨c₁⟩ := h.coord
  have : Finite W := h.finite_W
  have := h.finite_aut
  set t₁ : MulAut W := ((c₁.π gA : ↥L₁) : MulAut W) with ht₁def
  set t₂ : MulAut W := ((c₁.π gQ : ↥L₁) : MulAut W) with ht₂def
  have hgA2 : gA ^ 2 = 1 := ext_mat (by rw [pow_two, mat_mul, mat_one]; exact tA_sq)
  have hgQ2 : gQ ^ 2 = 1 := ext_mat (by rw [pow_two, mat_mul, mat_one]; exact tQ_sq)
  have hgAQ : gA * gQ = gQ * gA := ext_mat (by rw [mat_mul, mat_mul]; exact tA_tQ_comm)
  have hcoe : ∀ γ δ : SL32, ((c₁.π γ : ↥L₁) : MulAut W) * ((c₁.π δ : ↥L₁) : MulAut W) =
      ((c₁.π (γ * δ) : ↥L₁) : MulAut W) := fun γ δ => by rw [map_mul]; rfl
  have hsq : ∀ γ : SL32, γ ^ 2 = 1 → ((c₁.π γ : ↥L₁) : MulAut W) ^ 2 = 1 := fun γ hγ => by
    rw [pow_two, hcoe, ← pow_two, hγ, map_one]
    rfl
  have hne : ∀ γ : SL32, γ ≠ 1 → ((c₁.π γ : ↥L₁) : MulAut W) ≠ 1 := fun γ hγ h0 =>
    hγ (c₁.π.injective (by rw [map_one]; exact Subtype.ext h0))
  have hmatne : ∀ γ : SL32, mat γ ≠ 1 → γ ≠ 1 := fun γ hγ h0 => hγ (by rw [h0, mat_one])
  have ht₁ : t₁ ^ 2 = 1 := hsq gA hgA2
  have ht₂ : t₂ ^ 2 = 1 := hsq gQ hgQ2
  have ht₁₂ : Commute t₁ t₂ := by
    show t₁ * t₂ = t₂ * t₁
    rw [ht₁def, ht₂def, hcoe, hcoe, hgAQ]
  have ht₁1 : t₁ ≠ 1 := hne gA (hmatne gA tA_ne_one)
  have ht₂1 : t₂ ≠ 1 := hne gQ (hmatne gQ tQ_ne_one)
  have ht₁₂1 : t₁ * t₂ ≠ 1 := by
    rw [ht₁def, ht₂def, hcoe]
    exact hne _ (hmatne _ (by rw [mat_mul]; exact tAQ_ne_one))
  have ht₂ne₁ : t₂ ≠ t₁ := fun h0 => tA_ne_tQ (by
    have := c₁.π.injective (Subtype.ext h0)
    exact (congrArg mat this).symm)
  have hf₂ : fixV (Subgroup.zpowers t₂) = fixV (Subgroup.zpowers t₁) :=
    h.fixV_eq_of_fixM c₁ fixM_gQ
  have hf₁₂ : fixV (Subgroup.zpowers (t₁ * t₂)) = fixV (Subgroup.zpowers t₁) := by
    rw [ht₁def, ht₂def, hcoe]
    exact h.fixV_eq_of_fixM c₁ fixM_gAQ
  set A₀ := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hA₀
  have hcomm : ∀ (x : ↥(Subgroup.zpowers t₁)) (z : ↥(Subgroup.zpowers t₂)),
      Commute ((Subgroup.zpowers t₁).subtype x) ((Subgroup.zpowers t₂).subtype z) := by
    rintro ⟨x, m, rfl⟩ ⟨z, n, rfl⟩
    exact ht₁₂.zpow_zpow m n
  have hmem : ∀ y ∈ A₀, ∃ x ∈ Subgroup.zpowers t₁, ∃ z ∈ Subgroup.zpowers t₂, y = x * z := by
    intro y hy
    rw [← (show ((Subgroup.zpowers t₁).subtype.noncommCoprod (Subgroup.zpowers t₂).subtype
        hcomm).range = A₀ by rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype,
          Subgroup.range_subtype])] at hy
    obtain ⟨⟨x, z⟩, rfl⟩ := hy
    exact ⟨x, x.2, z, z.2, rfl⟩
  have hfour : ∀ y ∈ A₀, y = 1 ∨ y = t₁ ∨ y = t₂ ∨ y = t₁ * t₂ := by
    intro y hy
    obtain ⟨x, hx, z, hz, rfl⟩ := hmem y hy
    rcases eq_one_or_of_sq ht₁ hx with rfl | rfl <;>
      rcases eq_one_or_of_sq ht₂ hz with rfl | rfl <;> simp
  have hfixA : fixV A₀ = fixV (Subgroup.zpowers t₁) := by
    apply le_antisymm
    · exact fun w hw g hg => hw g (Subgroup.mem_sup_left hg)
    · intro w hw g hg
      rcases hfour g hg with rfl | rfl | rfl | rfl
      · rfl
      · exact mem_fixV_zp.1 hw
      · exact mem_fixV_zp.1 (hf₂ ▸ hw)
      · exact mem_fixV_zp.1 (hf₁₂ ▸ hw)
  have hsqA : ∀ y ∈ A₀, y ^ 2 = 1 := fun y hy => by
    rcases hfour y hy with rfl | rfl | rfl | rfl
    · exact one_pow 2
    · exact ht₁
    · exact ht₂
    · rw [ht₁₂.mul_pow, ht₁, ht₂, one_mul]
  have hP : IsPGroup 2 ↥A₀ := fun y => ⟨1, Subtype.ext (by simpa using hsqA y y.2)⟩
  have hcardA : 2 < Nat.card A₀ := by
    have hle : Subgroup.zpowers t₁ ≤ A₀ := le_sup_left
    have hne' : Subgroup.zpowers t₁ ≠ A₀ := fun h0 => by
      have : t₂ ∈ Subgroup.zpowers t₁ := h0 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂)
      rcases eq_one_or_of_sq ht₁ this with h1 | h1
      · exact ht₂1 h1
      · exact ht₂ne₁ h1
    have hord : orderOf t₁ = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime ht₁ ht₁1
    have h2 : Nat.card (Subgroup.zpowers t₁) = 2 := by rw [Nat.card_zpowers, hord]
    by_contra hlt
    exact hne' (Subgroup.eq_of_le_of_card_ge hle (by omega))
  refine ⟨A₀, sup_le (Subgroup.zpowers_le.2 (h.le₁ (c₁.π gA).2))
    (Subgroup.zpowers_le.2 (h.le₁ (c₁.π gQ).2)), fun h0 => ht₁1 ?_, ⟨fun a ha b hb => ?_, hsqA⟩,
    fun B hB hlt => ?_⟩
  · have : t₁ ∈ A₀ := Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁)
    rw [h0] at this
    exact this
  · obtain ⟨x, ⟨m, rfl⟩, z, ⟨n, rfl⟩, rfl⟩ := hmem a ha
    obtain ⟨x', ⟨m', rfl⟩, z', ⟨n', rfl⟩, rfl⟩ := hmem b hb
    exact Commute.mul_left
      (Commute.mul_right ((Commute.refl t₁).zpow_zpow m m') (ht₁₂.zpow_zpow m n'))
      (Commute.mul_right (ht₁₂.symm.zpow_zpow n m') ((Commute.refl t₂).zpow_zpow n n'))
  · have hB1 : B ≠ ⊥ := by
      rintro rfl
      rw [E3.mQuot, Subgroup.relIndex_bot_left] at hlt
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hP
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [hk, padicValNat.prime_pow] at hlt
      rw [hk] at hcardA
      interval_cases k <;> omega
    obtain ⟨⟨s, hsB⟩, hs1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB1
    have hs1' : s ≠ 1 := fun h0 => hs1 (Subtype.ext h0)
    have hfs : fixV (Subgroup.zpowers s) = fixV A₀ := by
      rw [hfixA]
      rcases hfour s (hB hsB) with rfl | rfl | rfl | rfl
      · exact absurd rfl hs1'
      · rfl
      · exact hf₂
      · exact hf₁₂
    apply le_antisymm
    · rw [← hfs]
      exact fun w hw g hg => hw g ((Subgroup.zpowers_le.2 hsB) hg)
    · exact fun w hw g hg => hw g (hB hg)

variable (hR : RHyp Mb L₁ L₂ R)
include hR

theorem aParam_eq : E3.aParam Mb = 2 := by
  obtain ⟨c₁⟩ := h.coord
  have heven : Even (Nat.card Mb) := by
    have h1 := Subgroup.card_dvd_of_le h.le₁
    rw [c₁.card_L] at h1
    exact even_iff_two_dvd.2 ((by norm_num : 2 ∣ 168).trans h1)
  simp only [E3.aParam, heven, ↓reduceIte]
  have h2 : 2 ∈ {k : ℕ | 0 < k ∧ (E3.aSet k Mb).Nonempty} := ⟨by norm_num, h.aSet_two_nonempty⟩
  have hb : ∀ k ∈ {k : ℕ | 0 < k ∧ (E3.aSet k Mb).Nonempty}, k ≤ 2 := by
    rintro k ⟨-, A, hA⟩
    by_contra hk
    have hA3 : A ∈ E3.aSet 3 Mb :=
      ⟨hA.1, hA.2.1, hA.2.2.1, fun B hB hlt => hA.2.2.2 B hB (by omega)⟩
    rw [h.aSet_three_eq_empty hR] at hA3
    exact hA3
  exact le_antisymm (csSup_le ⟨2, h2⟩ hb) (le_csSup ⟨2, hb⟩ h2)

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
