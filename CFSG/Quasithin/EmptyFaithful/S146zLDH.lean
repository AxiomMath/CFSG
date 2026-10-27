module

public import CFSG.Quasithin.EmptyFaithful.S146zJVtx

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Pure

variable {G : Type*} [Group G] [Finite G]

theorem relIndex_cent_le_two {D A : Subgroup G} (hA : Nat.card A = 2) {w : G}
    (hcomm : ∀ d ∈ D, d * w * d⁻¹ * w⁻¹ ∈ A) :
    (D ⊓ Subgroup.centralizer ({w} : Set G)).relIndex D ≤ 2 := by
  classical
  have hcent : ∀ d : G, d * w = w * d → d ∈ Subgroup.centralizer ({w} : Set G) := fun d hd =>
    Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hd.symm
  by_cases hall : ∀ d ∈ D, d * w = w * d
  · have : D ⊓ Subgroup.centralizer ({w} : Set G) = D :=
      inf_eq_left.mpr fun d hd => hcent d (hall d hd)
    rw [this, Subgroup.relIndex_self]
    norm_num
  · push Not at hall
    obtain ⟨d₀, hd₀, hd₀w⟩ := hall
    have hc₀ : d₀ * w * d₀⁻¹ * w⁻¹ ≠ 1 := fun e => hd₀w (by
      have := congrArg (fun x => x * w * d₀) e
      simpa [mul_assoc] using this)
    unfold Subgroup.relIndex
    refine index_le_two_of_forall _ (⟨d₀, hd₀⟩ : ↥D) fun z => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    by_cases hzw : (z : G) * w = w * z
    · exact Or.inl ⟨z.2, hcent _ hzw⟩
    · right
      refine ⟨D.mul_mem (D.inv_mem hd₀) z.2, hcent _ ?_⟩
      have hcz : (z : G) * w * (z : G)⁻¹ * w⁻¹ ≠ 1 := fun e => hzw (by
        have := congrArg (fun y => y * w * (z : G)) e
        simpa [mul_assoc] using this)
      rcases eq_one_or_eq_of_card_subgroup_two _ hA (hcomm d₀ hd₀) hc₀ (hcomm z z.2) with h1 | h1
      · exact absurd h1 hcz
      · have e3 : (z : G) * w * (z : G)⁻¹ = d₀ * w * d₀⁻¹ := mul_right_cancel h1
        calc d₀⁻¹ * (z : G) * w = d₀⁻¹ * ((z : G) * w * (z : G)⁻¹) * (z : G) := by group
          _ = d₀⁻¹ * (d₀ * w * d₀⁻¹) * (z : G) := by rw [e3]
          _ = w * (d₀⁻¹ * (z : G)) := by group

end Pure

section DH

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G}

theorem Setting146.index_fix_le (S : Setting146 G T M) (hH : IsHTM T M H)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {w : G} (hw : w ∈ F8.Uγ (VZ T M) H (k : G)) (hwH : w ∈ H) :
    (fixSubOf (rhoH h91 ⟨w, hwH⟩)).index ≤
      2 * 2 ^ mIdx (conjClosure (VZ T M) H)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
  classical
  obtain ⟨h81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHC : ∀ y ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y := by
    intro y hy z hz
    have h1 := hHN hy
    rw [normalizer_eq_centralizer_of_card_eq_two S.card_Z] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hDU : F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G) ≤ conjClosure (VZ T M) H :=
    centralizerMod_le_left _ _ _
  have hZD := S.Z_le_DH hH sk
  set DH := F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G) with hDH
  set D' : Subgroup G := DH ⊓ Subgroup.centralizer ({w} : Set G) with hD'
  have hD'DH : D' ≤ DH := inf_le_left
  have hZD' : quasithinOmegaOneCenter T ≤ D' := fun z hz =>
    ⟨hZD hz, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hHC x hwH z hz⟩
  have hA₁ : Nat.card (F8.A₁ (quasithinOmegaOneCenter T) (k : G)) = 2 := h98.card_A₁ (g := k)
  have hidx : D'.relIndex DH ≤ 2 :=
    relIndex_cent_le_two hA₁ (fun d hd => hd.2.2 w hw)
  have hWD' : Wsub h91 D' ≤ fixSubOf (rhoH h91 ⟨w, hwH⟩) := by
    intro x hx
    obtain ⟨d, hdU, hdD', rfl⟩ := exists_clsU_of_mem_Wsub h91 (hD'DH.trans hDU) hx
    show rhoH h91 ⟨w, hwH⟩ (clsU h91 hdU) = clsU h91 hdU
    rw [rhoH_clsU_eq_iff]
    have hdw : w * d = d * w := Subgroup.mem_centralizer_iff.mp hdD'.2 w (Set.mem_singleton w)
    have e : w * d * w⁻¹ * d⁻¹ = 1 := by
      rw [hdw]
      group
    show w * d * w⁻¹ * d⁻¹ ∈ quasithinOmegaOneCenter T
    rw [e]
    exact (quasithinOmegaOneCenter T).one_mem
  have hindexW : (Wsub h91 D').index = D'.relIndex (conjClosure (VZ T M) H) :=
    Wsub_index_eq h91 (hD'DH.trans hDU) hZD'
  have h1 := Subgroup.relIndex_mul_relIndex D' DH (conjClosure (VZ T M) H) hD'DH hDU
  have h2 : DH.relIndex (conjClosure (VZ T M) H) = 2 ^ mIdx (conjClosure (VZ T M) H) DH :=
    HypF98.relIndex_eq_two_pow_mIdx hUp
  have hfix : (fixSubOf (rhoH h91 ⟨w, hwH⟩)).index ≤ (Wsub h91 D').index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hWD')
  rw [hindexW] at hfix
  calc (fixSubOf (rhoH h91 ⟨w, hwH⟩)).index ≤ D'.relIndex (conjClosure (VZ T M) H) := hfix
    _ = D'.relIndex DH * DH.relIndex (conjClosure (VZ T M) H) := h1.symm
    _ ≤ 2 * 2 ^ mIdx (conjClosure (VZ T M) H) DH := by
        rw [h2]
        exact Nat.mul_le_mul hidx le_rfl

theorem Setting146.index_fix_le₂ (S : Setting146 G T M) (hH : IsHTM T M H)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (h91 : HypF91 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M) H)
    {w₁ w₂ : G} (hw₁ : w₁ ∈ F8.Uγ (VZ T M) H (k : G)) (hw₁H : w₁ ∈ H)
    (hw₂ : w₂ ∈ F8.Uγ (VZ T M) H (k : G)) (hw₂H : w₂ ∈ H) :
    (fixSubOf (rhoH h91 ⟨w₁, hw₁H⟩) ⊓ fixSubOf (rhoH h91 ⟨w₂, hw₂H⟩)).index ≤
      4 * 2 ^ mIdx (conjClosure (VZ T M) H)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) := by
  classical
  obtain ⟨h81, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHC : ∀ y ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y := by
    intro y hy z hz
    have h1 := hHN hy
    rw [normalizer_eq_centralizer_of_card_eq_two S.card_Z] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hDU : F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G) ≤ conjClosure (VZ T M) H :=
    centralizerMod_le_left _ _ _
  have hZD := S.Z_le_DH hH sk
  set DH := F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G) with hDH
  set D' : Subgroup G := DH ⊓ Subgroup.centralizer ({w₁} : Set G) with hD'
  set D'' : Subgroup G := D' ⊓ Subgroup.centralizer ({w₂} : Set G) with hD''
  have hD'DH : D' ≤ DH := inf_le_left
  have hD''D' : D'' ≤ D' := inf_le_left
  have hD''DH : D'' ≤ DH := hD''D'.trans hD'DH
  have hZD'' : quasithinOmegaOneCenter T ≤ D'' := fun z hz =>
    ⟨⟨hZD hz, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hHC x hw₁H z hz⟩, Subgroup.mem_centralizer_iff.mpr fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hHC x hw₂H z hz⟩
  have hA₁ : Nat.card (F8.A₁ (quasithinOmegaOneCenter T) (k : G)) = 2 := h98.card_A₁ (g := k)
  have hidx₁ : D'.relIndex DH ≤ 2 :=
    relIndex_cent_le_two hA₁ (fun d hd => hd.2.2 w₁ hw₁)
  have hidx₂ : D''.relIndex D' ≤ 2 :=
    relIndex_cent_le_two (D := D') hA₁ (fun d hd => (hD'DH hd).2.2 w₂ hw₂)
  have hWD'' : Wsub h91 D'' ≤
      fixSubOf (rhoH h91 ⟨w₁, hw₁H⟩) ⊓ fixSubOf (rhoH h91 ⟨w₂, hw₂H⟩) := by
    intro x hx
    obtain ⟨d, hdU, hdD'', rfl⟩ := exists_clsU_of_mem_Wsub h91 (hD''DH.trans hDU) hx
    have hdw₁ : w₁ * d = d * w₁ :=
      Subgroup.mem_centralizer_iff.mp hdD''.1.2 w₁ (Set.mem_singleton w₁)
    have hdw₂ : w₂ * d = d * w₂ :=
      Subgroup.mem_centralizer_iff.mp hdD''.2 w₂ (Set.mem_singleton w₂)
    have hfix : ∀ (w : G) (hwH : w ∈ H), w * d = d * w →
        rhoH h91 ⟨w, hwH⟩ (clsU h91 hdU) = clsU h91 hdU := by
      intro w hwH hdw
      rw [rhoH_clsU_eq_iff]
      have e : w * d * w⁻¹ * d⁻¹ = 1 := by
        rw [hdw]
        group
      show w * d * w⁻¹ * d⁻¹ ∈ quasithinOmegaOneCenter T
      rw [e]
      exact (quasithinOmegaOneCenter T).one_mem
    exact ⟨hfix w₁ hw₁H hdw₁, hfix w₂ hw₂H hdw₂⟩
  have hindexW : (Wsub h91 D'').index = D''.relIndex (conjClosure (VZ T M) H) :=
    Wsub_index_eq h91 (hD''DH.trans hDU) hZD''
  have h1 := Subgroup.relIndex_mul_relIndex D'' D' (conjClosure (VZ T M) H) hD''D'
    (hD'DH.trans hDU)
  have h1' := Subgroup.relIndex_mul_relIndex D' DH (conjClosure (VZ T M) H) hD'DH hDU
  have h2 : DH.relIndex (conjClosure (VZ T M) H) = 2 ^ mIdx (conjClosure (VZ T M) H) DH :=
    HypF98.relIndex_eq_two_pow_mIdx hUp
  have hfix : (fixSubOf (rhoH h91 ⟨w₁, hw₁H⟩) ⊓ fixSubOf (rhoH h91 ⟨w₂, hw₂H⟩)).index ≤
      (Wsub h91 D'').index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hWD'')
  rw [hindexW, ← h1, ← h1'] at hfix
  refine hfix.trans ?_
  rw [h2, ← mul_assoc]
  exact Nat.mul_le_mul (Nat.mul_le_mul hidx₂ hidx₁) le_rfl

end DH

end CFSG.Quasithin
