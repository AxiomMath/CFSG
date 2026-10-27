module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_qm_isPGroup_top_of_sq_eq_one {W : Type} [Group W]
    (h : ∀ x : W, x ^ 2 = 1) : IsPGroup 2 (⊤ : Subgroup W) := fun x =>
  ⟨1, Subtype.ext (by simpa using h (x : W))⟩

private theorem s16k_qm_exists_induced_hom {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
    {Z : Subgroup W} (hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z) :
    ∃ ρ : ↥A →* MulAut (W ⧸ Z),
      ∀ (a : ↥A) (w : W), ρ a (QuotientGroup.mk' Z w) = QuotientGroup.mk' Z ((a : MulAut W) w) := by
  have hex : ∀ a : ↥A, ∃ ψ : MulAut (W ⧸ Z),
      ∀ w : W, ψ (QuotientGroup.mk' Z w) = QuotientGroup.mk' Z ((a : MulAut W) w) := by
    intro a
    refine s16g_exists_induced_aut (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) ?_
    intro w
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact ⟨fun hw => (QuotientGroup.eq_one_iff ((a : MulAut W) w)).2
        (hZA a a.2 w ((QuotientGroup.eq_one_iff w).1 hw)), fun haw => by
      have haw' := (QuotientGroup.eq_one_iff ((a : MulAut W) w)).1 haw
      have h2 := hZA a⁻¹ (inv_mem a.2) ((a : MulAut W) w) haw'
      exact (QuotientGroup.eq_one_iff w).2 (by simpa using h2)⟩
  choose ρ₀ hρ₀ using hex
  have hmul : ∀ a b : ↥A, ρ₀ (a * b) = ρ₀ a * ρ₀ b := by
    intro a b
    ext q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [hρ₀ (a * b) w, MulAut.mul_apply, hρ₀ b w, hρ₀ a ((b : MulAut W) w)]
    rfl
  exact ⟨MonoidHom.mk' ρ₀ hmul, fun a w => hρ₀ a w⟩

private theorem s16k_qm_rho_injective {W : Type} [CommGroup W] [Finite W]
    {H A : Subgroup (MulAut W)} (hHA : H ≤ A)
    (hHn : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H)
    (hq : CFSG.Open.IsQuasisimple ↥H) (hcomm : commSub ⊤ H = ⊤)
    (ρ : ↥A →* MulAut (W ⧸ fixV H))
    (hρ : ∀ (a : ↥A) (w : W), ρ a (QuotientGroup.mk' (fixV H) w) =
      QuotientGroup.mk' (fixV H) ((a : MulAut W) w)) :
    Function.Injective ρ := by
  let ρH : ↥H →* MulAut (W ⧸ fixV H) := ρ.comp (Subgroup.inclusion hHA)
  have hρH : ∀ (x : ↥H) (w : W), ρH x (QuotientGroup.mk' (fixV H) w) =
      QuotientGroup.mk' (fixV H) ((x : MulAut W) w) :=
    fun x w => hρ ⟨(x : MulAut W), hHA x.2⟩ w
  have hKne : ρH.ker ≠ ⊤ := by
    intro hKtop
    have hZtop : fixV H = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← hcomm, commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, -, rfl⟩
      have hx1 : ρH ⟨x, hx⟩ = 1 :=
        MonoidHom.mem_ker.mp (by rw [hKtop]; exact Subgroup.mem_top _)
      have h2 := congrArg (fun f : MulAut (W ⧸ fixV H) =>
        f (QuotientGroup.mk' (fixV H) w)) hx1
      simp only [MulAut.one_apply] at h2
      rw [hρH ⟨x, hx⟩ w] at h2
      have h3 : QuotientGroup.mk' (fixV H) (x w * w⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h3
    have hHbot : H = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro h hh
      ext w
      exact mem_fixV.1 (hZtop ▸ Subgroup.mem_top w) h hh
    haveI : Subsingleton ↥H := by rw [hHbot]; infer_instance
    obtain ⟨x, y, hxy⟩ := (CFSG.ComponentClassification.Quasisimple.nontrivial hq).exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  have hKcenter : ρH.ker ≤ Subgroup.center ↥H :=
    CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hq ρH.ker hKne
  have hKbot : ρH.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    have hxc : ∀ h ∈ H, (x : MulAut W) * h = h * (x : MulAut W) := by
      intro h hh
      have h1 := (congrArg Subtype.val
        (Subgroup.mem_center_iff.1 (hKcenter hx) (⟨h, hh⟩ : ↥H))).symm
      simpa using h1
    have hxfix : ∀ w : W, (x : MulAut W) w * w⁻¹ ∈ fixV H := by
      intro w
      have h1 : ρH x = 1 := MonoidHom.mem_ker.1 hx
      have h2 := congrArg (fun f : MulAut (W ⧸ fixV H) =>
        f (QuotientGroup.mk' (fixV H) w)) h1
      simp only [MulAut.one_apply] at h2
      rw [hρH x w] at h2
      have h3 : QuotientGroup.mk' (fixV H) ((x : MulAut W) w * w⁻¹) = 1 := by
        rw [map_mul, map_inv, h2, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).1 h3
    exact s16g_eq_one_of_commSub hcomm hxc hxfix
  rw [injective_iff_map_eq_one]
  intro a ha
  apply Subtype.ext
  have hac : ∀ h ∈ H, (a : MulAut W) * h = h * (a : MulAut W) := by
    intro h hh
    have hmem : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ ∈ H :=
      H.mul_mem (hHn a a.2 h hh) (H.inv_mem hh)
    have hker : (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hmem⟩ : ↥H) ∈ ρH.ker := by
      rw [MonoidHom.mem_ker]
      change ρ (Subgroup.inclusion hHA
        ⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hmem⟩) = 1
      have heq : Subgroup.inclusion hHA
            (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hmem⟩ : ↥H) =
          (⟨(a : MulAut W), a.2⟩ : ↥A) * ⟨h, hHA hh⟩ *
            (⟨(a : MulAut W), a.2⟩ : ↥A)⁻¹ * (⟨h, hHA hh⟩ : ↥A)⁻¹ :=
        Subtype.ext rfl
      rw [heq]
      have ha' : ρ (⟨(a : MulAut W), a.2⟩ : ↥A) = 1 := ha
      simp only [map_mul, map_inv, ha', one_mul, inv_one, mul_one, mul_inv_cancel]
    have h1 : (⟨(a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹, hmem⟩ : ↥H) = 1 := by
      have h2 := hker
      rw [hKbot] at h2
      exact Subgroup.mem_bot.1 h2
    have h3 : (a : MulAut W) * h * (a : MulAut W)⁻¹ * h⁻¹ = 1 := by
      simpa using congrArg Subtype.val h1
    have h4 : (a : MulAut W) * h * (a : MulAut W)⁻¹ = h := mul_inv_eq_one.1 h3
    calc (a : MulAut W) * h
        = (a : MulAut W) * h * (a : MulAut W)⁻¹ * (a : MulAut W) := by group
      _ = h * (a : MulAut W) := by rw [h4]
  have hfix : ∀ w : W, (a : MulAut W) w * w⁻¹ ∈ fixV H := by
    intro w
    have h2 : ρ a (QuotientGroup.mk' (fixV H) w) = QuotientGroup.mk' (fixV H) w := by
      rw [ha]; rfl
    rw [hρ a w] at h2
    have h3 : QuotientGroup.mk' (fixV H) ((a : MulAut W) w * w⁻¹) = 1 := by
      rw [map_mul, map_inv, h2, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).1 h3
  exact s16g_eq_one_of_commSub hcomm hac hfix

theorem s16k_qm_quotMap {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} (hq : CFSG.Open.IsQuasisimple ↥H) (hcomm : commSub ⊤ H = ⊤)
    (hsq : ∀ x : W, x ^ 2 = 1) :
    ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (q : W →* Q) (ρ : ↥H →* MulAut Q),
      Function.Surjective q ∧ (∀ x : W, q x = 1 ↔ x ∈ fixV H) ∧
      Function.Injective ρ ∧
      (∀ (l : ↥H) (x : W), q ((l : MulAut W) x) = ρ l (q x)) ∧
      (∀ x : Q, x ^ 2 = 1) ∧
      Nat.card Q = 2 ^ E3.mQuot (⊤ : Subgroup W) (fixV H) ∧
      (commSub ⊤ H ∈ irrSet H →
        ∀ B : Subgroup Q, (∀ (l : ↥H), ∀ b ∈ B, ρ l b ∈ B) → B = ⊥ ∨ B = ⊤) := by
  classical
  have hHn : ∀ a ∈ H, ∀ b ∈ H, a * b * a⁻¹ ∈ H := fun a ha b hb =>
    H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)
  have hZA : ∀ a ∈ H, ∀ z ∈ fixV H, a z ∈ fixV H := by
    intro a ha z hz
    rw [mem_fixV] at hz ⊢
    intro b hb
    have hmem : a⁻¹ * b * a ∈ H := H.mul_mem (H.mul_mem (H.inv_mem ha) hb) ha
    calc b (a z) = a ((a⁻¹ * b * a) z) := by simp [MulAut.mul_apply]
      _ = a z := by rw [hz _ hmem]
  obtain ⟨ρ, hρ⟩ := s16k_qm_exists_induced_hom (A := H) (Z := fixV H) hZA
  have hρinj : Function.Injective ρ :=
    s16k_qm_rho_injective (H := H) (A := H) le_rfl hHn hq hcomm ρ hρ
  have hWp : IsPGroup 2 (⊤ : Subgroup W) := s16k_qm_isPGroup_top_of_sq_eq_one hsq
  have hcardQ : Nat.card (W ⧸ fixV H) = 2 ^ E3.mQuot (⊤ : Subgroup W) (fixV H) := by
    have h1 : Nat.card (⊤ : Subgroup W) =
        2 ^ E3.mQuot (⊤ : Subgroup W) (fixV H) * Nat.card (fixV H) :=
      E3.card_eq_two_pow_mul hWp le_top
    rw [Subgroup.card_top] at h1
    have h2 : Nat.card W = Nat.card (W ⧸ fixV H) * Nat.card (fixV H) := by
      rw [← Subgroup.card_mul_index (H := fixV H), Subgroup.index_eq_card, mul_comm]
    have h3 : 2 ^ E3.mQuot (⊤ : Subgroup W) (fixV H) * Nat.card (fixV H) =
        Nat.card (W ⧸ fixV H) * Nat.card (fixV H) := by
      rw [← h1, h2]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3.symm
  refine ⟨W ⧸ fixV H, inferInstance, inferInstance, QuotientGroup.mk' (fixV H), ρ,
    QuotientGroup.mk'_surjective (fixV H), ?_, hρinj, ?_, ?_, hcardQ, ?_⟩
  · intro x
    exact QuotientGroup.eq_one_iff x
  · intro l x
    exact (hρ l x).symm
  · intro x
    induction x using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow, hsq w, QuotientGroup.mk_one]
  · intro hirr B hB
    have hIrr : IsIrrOn H ⊤ (fixV H) := by
      have h' := hirr
      simp only [irrSet, Set.mem_setOf_eq] at h'
      rw [hcomm, top_inf_eq] at h'
      exact h'.2
    let J : Subgroup W := B.comap (QuotientGroup.mk' (fixV H))
    have hZJ : fixV H ≤ J := by
      intro z hz
      rw [Subgroup.mem_comap]
      rw [show QuotientGroup.mk' (fixV H) z = (1 : W ⧸ fixV H) from
        (QuotientGroup.eq_one_iff z).2 hz]
      exact B.one_mem
    have hStabJ : StableUnder H J := by
      intro x hx j hj
      rw [Subgroup.mem_comap] at hj ⊢
      rw [← hρ ⟨x, hx⟩ j]
      exact hB ⟨x, hx⟩ (QuotientGroup.mk' (fixV H) j) hj
    have hBmap : (B.comap (QuotientGroup.mk' (fixV H))).map (QuotientGroup.mk' (fixV H)) = B :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (fixV H)) B
    rcases hIrr.2.2.2 J hStabJ hZJ le_top with hJ | hJ
    · left
      rw [← hBmap]
      change J.map (QuotientGroup.mk' (fixV H)) = ⊥
      rw [hJ, Subgroup.map_eq_bot_iff]
      intro z hz
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff z).2 hz
    · right
      rw [← hBmap]
      change J.map (QuotientGroup.mk' (fixV H)) = ⊤
      rw [hJ]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (fixV H))

theorem s16k_exists_quot_map (h : S16gRowCtx D V₀ V L hV) :
    ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (q : Vtil V₀ V hV →* Q)
      (ρ : ↥(lBar V₀ V hV L) →* MulAut Q),
      Function.Surjective q ∧ (∀ x : Vtil V₀ V hV, q x = 1 ↔ x ∈ fixV (lBar V₀ V hV L)) ∧
      Function.Injective ρ ∧
      (∀ (l : ↥(lBar V₀ V hV L)) (x : Vtil V₀ V hV),
        q ((l : MulAut (Vtil V₀ V hV)) x) = ρ l (q x)) ∧
      (∀ x : Q, x ^ 2 = 1) ∧
      Nat.card Q = 2 ^ E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∧
      (commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L) →
        ∀ B : Subgroup Q, (∀ (l : ↥(lBar V₀ V hV L)), ∀ b ∈ B, ρ l b ∈ B) → B = ⊥ ∨ B = ⊤) := by
  obtain ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, heq, hexp, hcard, hirr⟩ :=
    s16k_qm_quotMap (W := Vtil V₀ V hV) (H := lBar V₀ V hV L) h.quasi h.comm_top
      (s15_Infra_vtil_sq_eq_one V₀ V hV)
  refine ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, heq, hexp, ?_, ?_⟩
  · rw [h.comm_top, top_inf_eq]
    exact hcard
  · intro hirrB
    exact hirr hirrB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
