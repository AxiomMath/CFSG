module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_isPGroup_top_of_sq_eq_one {W : Type} [Group W]
    (h : ∀ x : W, x ^ 2 = 1) : IsPGroup 2 (⊤ : Subgroup W) := fun x =>
  ⟨1, Subtype.ext (by simpa using h (x : W))⟩

private theorem s16k_exists_induced_hom {W : Type} [CommGroup W] {A : Subgroup (MulAut W)}
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

private theorem s16k_rho_injective {W : Type} [CommGroup W] [Finite W]
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

private theorem s16k_realizes_quot {W : Type} [CommGroup W] {Z : Subgroup W}
    {H : Subgroup (MulAut W)} (ρH : ↥H →* MulAut (W ⧸ Z))
    (hρH : ∀ (x : ↥H) (w : W), ρH x (QuotientGroup.mk' Z w) =
      QuotientGroup.mk' Z ((x : MulAut W) w))
    (hρHinj : Function.Injective ρH) (M : FFModel) (hMR : M.Realizes H ⊤ Z) :
    M.Realizes ρH.range ⊤ ⊥ := by
  classical
  unfold FFModel.Realizes FFModel.RealizesVia at hMR ⊢
  obtain ⟨π, hπs, -, hkerle, -, -, hsec, hker, β, hβs, hβk, hβe⟩ := hMR
  let e : ↥H ≃* ↥(ρH.range) := MonoidHom.ofInjective hρHinj
  let π' : M.Gam →* ↥(ρH.range) := e.toMonoidHom.comp π
  have hπ's : Function.Surjective π' := e.surjective.comp hπs
  let C := ↥M.sec ⧸ M.ker.subgroupOf M.sec
  let f : W →* C :=
    { toFun := fun w => β (⟨w, trivial⟩ : ↥(⊤ : Subgroup W))
      map_one' := map_one β
      map_mul' := fun a b => map_mul β ⟨a, trivial⟩ ⟨b, trivial⟩ }
  have hf : ∀ w : W, f w = 1 ↔ w ∈ Z := fun w => hβk ⟨w, trivial⟩
  have hfker : f.ker = Z := by
    ext w
    rw [MonoidHom.mem_ker, hf]
  let β' : W ⧸ Z →* C := QuotientGroup.lift Z f hfker.ge
  have hβ' : ∀ w : W, β' (QuotientGroup.mk' Z w) = f w :=
    fun w => QuotientGroup.lift_mk' Z hfker.ge w
  have hβ'inj : Function.Injective β' :=
    (QuotientGroup.injective_lift_iff Z f hfker.ge).2 hfker.symm
  have hβ'ker : β'.ker = ⊥ := (MonoidHom.ker_eq_bot_iff β').2 hβ'inj
  let β'' : ↥(⊤ : Subgroup (W ⧸ Z)) →* C :=
    β'.comp (Subgroup.topEquiv (G := W ⧸ Z)).toMonoidHom
  refine ⟨π', hπ's, bot_le, hkerle, ?_, ?_, hsec, hker, β'', ?_, ?_, ?_⟩
  · intro h u _
    exact Subgroup.mem_top _
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · have hfs : Function.Surjective f := by
      intro c
      obtain ⟨u, hu⟩ := hβs c
      exact ⟨(u : W), by
        show β (⟨(u : W), trivial⟩ : ↥(⊤ : Subgroup W)) = c
        rw [show (⟨(u : W), trivial⟩ : ↥(⊤ : Subgroup W)) = u from Subtype.ext rfl]
        exact hu⟩
    have hβ's : Function.Surjective β' :=
      QuotientGroup.lift_surjective_of_surjective Z f hfs hfker.ge
    exact hβ's.comp (Subgroup.topEquiv (G := W ⧸ Z)).surjective
  · intro u
    show β'' u = 1 ↔ (u : W ⧸ Z) ∈ (⊥ : Subgroup (W ⧸ Z))
    have h1 : β'' u = β' (u : W ⧸ Z) := rfl
    rw [h1, ← hβ'ker]
    exact MonoidHom.mem_ker.symm
  · intro γ u m _ hm hβu
    obtain ⟨w, hw⟩ : ∃ w : W, QuotientGroup.mk' Z w = (u : W ⧸ Z) :=
      QuotientGroup.mk'_surjective Z _
    have hfw : f w = QuotientGroup.mk m := by
      have h := hβu
      rw [show β'' u = β' (u : W ⧸ Z) from rfl, ← hw, hβ'] at h
      exact h
    have hfw' : β (⟨w, trivial⟩ : ↥(⊤ : Subgroup W)) = QuotientGroup.mk m := by
      exact hfw
    have hres := hβe γ (⟨w, trivial⟩ : ↥(⊤ : Subgroup W)) m (Subgroup.mem_top _) hm hfw'
    have harg : ((π' γ : ↥(ρH.range)) : MulAut (W ⧸ Z)) (u : W ⧸ Z) =
        QuotientGroup.mk' Z (((π γ : ↥H) : MulAut W) w) := by
      show ρH (π γ) (u : W ⧸ Z) = _
      rw [← hw, hρH (π γ) w]
    rw [show (⟨((π' γ : ↥(ρH.range)) : MulAut (W ⧸ Z)) (u : W ⧸ Z), _⟩ :
          ↥(⊤ : Subgroup (W ⧸ Z))) =
        (⟨QuotientGroup.mk' Z (((π γ : ↥H) : MulAut W) w), Subgroup.mem_top _⟩ :
          ↥(⊤ : Subgroup (W ⧸ Z))) from Subtype.ext harg]
    have hL : β'' (⟨QuotientGroup.mk' Z (((π γ : ↥H) : MulAut W) w), Subgroup.mem_top _⟩ :
        ↥(⊤ : Subgroup (W ⧸ Z))) =
        β (⟨((π γ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) := by
      show β' (QuotientGroup.mk' Z (((π γ : ↥H) : MulAut W) w)) = β _
      rw [hβ']
      rfl
    rw [hL]
    exact hres

private theorem s16k_quotData {W : Type} [CommGroup W] [Finite W]
    {H A : Subgroup (MulAut W)} (hHA : H ≤ A)
    (hHn : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H)
    (hq : CFSG.Open.IsQuasisimple ↥H) (hcomm : commSub ⊤ H = ⊤)
    (hsq : ∀ x : W, x ^ 2 = 1) :
    ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (L' N : Subgroup (MulAut Q)),
      (∀ x : Q, x ^ 2 = 1) ∧
      Nat.card Q = 2 ^ E3.mQuot (⊤ : Subgroup W) (fixV H) ∧
      Nonempty (↥H ≃* ↥L') ∧
      (commSub ⊤ H ∈ irrSet H →
        ∀ B : Subgroup Q, (∀ l ∈ L', ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) ∧
      (∀ n ∈ N, ∀ l ∈ L', n * l * n⁻¹ ∈ L') ∧
      (∀ p : ℕ, p.Prime → CFSG.Open.pRank p A ≤ CFSG.Open.pRank p N) ∧
      (∀ M : FFModel, M.Realizes H ⊤ (fixV H) → M.Realizes L' ⊤ ⊥) := by
  classical
  have hZA : ∀ a ∈ A, ∀ z ∈ fixV H, a z ∈ fixV H := by
    intro a ha z hz
    rw [mem_fixV] at hz ⊢
    intro h hh
    have hmem : a⁻¹ * h * a ∈ H := by
      have h2 := hHn a⁻¹ (inv_mem ha) h hh
      simpa using h2
    calc h (a z) = a ((a⁻¹ * h * a) z) := by simp [MulAut.mul_apply]
      _ = a z := by rw [hz _ hmem]
  obtain ⟨ρ, hρ⟩ := s16k_exists_induced_hom (A := A) (Z := fixV H) hZA
  have hρinj : Function.Injective ρ := s16k_rho_injective hHA hHn hq hcomm ρ hρ
  let ρH : ↥H →* MulAut (W ⧸ fixV H) := ρ.comp (Subgroup.inclusion hHA)
  have hρH : ∀ (x : ↥H) (w : W), ρH x (QuotientGroup.mk' (fixV H) w) =
      QuotientGroup.mk' (fixV H) ((x : MulAut W) w) :=
    fun x w => hρ ⟨(x : MulAut W), hHA x.2⟩ w
  have hρHinj : Function.Injective ρH := hρinj.comp (Subgroup.inclusion_injective hHA)
  have hcardQ : Nat.card (W ⧸ fixV H) = 2 ^ E3.mQuot (⊤ : Subgroup W) (fixV H) := by
    have hWp : IsPGroup 2 (⊤ : Subgroup W) := s16k_isPGroup_top_of_sq_eq_one hsq
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
  refine ⟨W ⧸ fixV H, inferInstance, inferInstance, ρH.range, ρ.range, ?_, hcardQ, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro x
    induction x using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow, hsq w, QuotientGroup.mk_one]
  · exact ⟨MonoidHom.ofInjective hρHinj⟩
  · intro hirr B hB
    have hIrr : IsIrrOn H ⊤ (fixV H) := by
      have h := hirr
      simp only [irrSet, Set.mem_setOf_eq] at h
      rw [hcomm, top_inf_eq] at h
      exact h.2
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
      have h1 : QuotientGroup.mk' (fixV H) (x j) =
          ρH ⟨x, hx⟩ (QuotientGroup.mk' (fixV H) j) := by
        rw [hρH ⟨x, hx⟩ j]
      rw [h1]
      exact hB (ρH ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ (QuotientGroup.mk' (fixV H) j) hj
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
  · intro n hn l hl
    obtain ⟨a, rfl⟩ := hn
    obtain ⟨x, rfl⟩ := hl
    refine ⟨⟨(a : MulAut W) * (x : MulAut W) * (a : MulAut W)⁻¹, hHn a a.2 x x.2⟩, ?_⟩
    have heq : Subgroup.inclusion hHA
          (⟨(a : MulAut W) * (x : MulAut W) * (a : MulAut W)⁻¹,
            hHn a a.2 x x.2⟩ : ↥H) =
        (⟨(a : MulAut W), a.2⟩ : ↥A) * (⟨(x : MulAut W), hHA x.2⟩ : ↥A) *
          (⟨(a : MulAut W), a.2⟩ : ↥A)⁻¹ := Subtype.ext rfl
    change ρH ⟨(a : MulAut W) * (x : MulAut W) * (a : MulAut W)⁻¹,
      hHn a a.2 x x.2⟩ = ρ a * ρH x * (ρ a)⁻¹
    rw [show ρH ⟨(a : MulAut W) * (x : MulAut W) * (a : MulAut W)⁻¹,
        hHn a a.2 x x.2⟩ =
        ρ (⟨(a : MulAut W), a.2⟩ : ↥A) * ρ (⟨(x : MulAut W), hHA x.2⟩ : ↥A) *
          (ρ (⟨(a : MulAut W), a.2⟩ : ↥A))⁻¹ by
      change ρ (Subgroup.inclusion hHA _) = _
      rw [heq, map_mul, map_mul, map_inv]]
    rfl
  · intro p hp
    obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt A
    have h1 : (E.subgroupOf A).map ρ ≤ ρ.range := by
      rintro _ ⟨y, -, rfl⟩
      exact ⟨y, rfl⟩
    have h2 : Nat.card ((E.subgroupOf A).map ρ) = p ^ CFSG.Open.pRank p A := by
      rw [Subgroup.card_map_of_injective hρinj,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEA).toEquiv, hcard]
    exact CFSG.SectionRank.le_pRank hp.one_lt h1 ((hE.subgroupOf A).map ρ) h2
  · intro M hMR
    exact s16k_realizes_quot ρH hρH hρHinj M hMR

theorem s16k_exists_quot_data (h : S16gRowCtx D V₀ V L hV) :
    ∃ (Q : Type) (_ : CommGroup Q) (_ : Finite Q) (L' N : Subgroup (MulAut Q)),
      (∀ x : Q, x ^ 2 = 1) ∧
      Nat.card Q = 2 ^ E3.mQuot (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) ∧
      Nonempty (↥(lBar V₀ V hV L) ≃* ↥L') ∧
      (commSub ⊤ (lBar V₀ V hV L) ∈ irrSet (lBar V₀ V hV L) →
        ∀ B : Subgroup Q, (∀ l ∈ L', ∀ b ∈ B, l b ∈ B) → B = ⊥ ∨ B = ⊤) ∧
      (∀ n ∈ N, ∀ l ∈ L', n * l * n⁻¹ ∈ L') ∧
      (∀ p : ℕ, p.Prime → CFSG.Open.pRank p (Mbar D.M V₀ V hV) ≤ CFSG.Open.pRank p N) ∧
      (∀ M : CFSG.Quasithin.FFModel, M.Realizes (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
        (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) → M.Realizes L' ⊤ ⊥) := by
  obtain ⟨Q, hQc, hQf, L', N, hexp, hcard, hiso, hirr, hnorm, hrank, hmodel⟩ :=
    s16k_quotData (W := Vtil V₀ V hV) (H := lBar V₀ V hV L) (A := Mbar D.M V₀ V hV)
      (barSub_mono V₀ V hV h.setting.hyp151.le)
      (fun a ha x hx =>
        (Subgroup.mem_normalizer_iff.1 (h.mBar_le_normalizer ha) x).1 hx)
      h.quasi h.comm_top (s15_Infra_vtil_sq_eq_one V₀ V hV)
  refine ⟨Q, hQc, hQf, L', N, hexp, ?_, hiso, ?_, hnorm, hrank, ?_⟩
  · rw [h.comm_top, top_inf_eq]
    exact hcard
  · intro hirrB
    exact hirr hirrB
  · intro M hM
    rw [h.comm_top, top_inf_eq] at hM
    exact hmodel M hM

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
