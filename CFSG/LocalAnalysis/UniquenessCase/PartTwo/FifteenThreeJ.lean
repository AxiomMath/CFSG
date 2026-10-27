module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

variable {W : Type} [CommGroup W] [Finite W]

theorem s15_Three_tgroup_fix_S {A : Subgroup (MulAut W)} {t : MulAut W} {S : Subgroup W}
    (hS : StableUnder A S) (htS : S ≤ fixV (Subgroup.zpowers t)) :
    S ≤ fixV (s15TGroup A t) := by
  intro s hs j hj
  have hle : s15TGroup A t ≤ MulAction.stabilizer (MulAut W) s := by
    rw [s15TGroup, Subgroup.closure_le]
    rintro x ⟨a, ha, rfl⟩
    have h2 : t (a s) = a s := htS (hS a ha s hs) t (Subgroup.mem_zpowers t)
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    simp [MulAut.mul_apply, MulAut.inv_apply, h2]
  have := MulAction.mem_stabilizer_iff.1 (hle hj)
  rwa [MulAut.smul_def] at this

theorem s15_Three_tgroup_faithful {A : Subgroup (MulAut W)} {t : MulAut W} {R S : Subgroup W}
    (hRS' : R ⊔ S = ⊤) (hfix : S ≤ fixV (s15TGroup A t)) :
    ∀ j ∈ s15TGroup A t, (∀ r ∈ R, j r = r) → j = 1 := by
  intro j hj hr
  ext w
  have hw : w ∈ R ⊔ S := by rw [hRS']; trivial
  obtain ⟨r, hr', s, hs, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul, hr r hr', hfix hs j hj]
  rfl

theorem s15_Three_gen_transvections (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)}
    {t : MulAut W} (ht : InducesTransvection t ⊤) {R S : Subgroup W} (hR : IsIrrOn A R ⊥)
    (hRt : StableUnder (Subgroup.zpowers t) R) (hS : StableUnder A S) (hRS' : R ⊔ S = ⊤)
    (htS : S ≤ fixV (Subgroup.zpowers t)) (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) :
    GenByTransvections (s15TGroup A t) R := by
  have hrk1 : rk ↥(commSub R (Subgroup.zpowers t)) = 1 := by
    have h1 : rk ↥(commSub R (Subgroup.zpowers t)) ≤ rk ↥(commSub ⊤ (Subgroup.zpowers t)) :=
      rk_mono (commSub_mono le_top le_rfl)
    have h2 : rk ↥(commSub R (Subgroup.zpowers t)) ≠ 0 := fun h =>
      htR ((rk_eq_zero_iff hW).1 h)
    have h3 := ht.2
    omega
  have hAR : ∀ a ∈ A, ∀ u : W, a u ∈ R ↔ u ∈ R := by
    intro a ha u
    refine ⟨fun h => ?_, hR.2.1 a ha u⟩
    have := hR.2.1 a⁻¹ (A.inv_mem ha) (a u) h
    simpa [MulAut.inv_apply] using this
  have htR' : t ∈ stabSub R := by
    intro u
    refine ⟨fun h => ?_, hRt t (Subgroup.mem_zpowers t) u⟩
    have := hRt t⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)) (t u) h
    simpa [MulAut.inv_apply] using this
  apply le_antisymm
  · refine (Subgroup.closure_le (K := Subgroup.closure
      {t' | t' ∈ s15TGroup A t ∧ InducesTransvection t' R})).2 ?_
    rintro x ⟨a, ha, rfl⟩
    refine Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨a, ha, rfl⟩, ?_, ?_⟩
    · have haS : a ∈ stabSub R := fun u => hAR a ha u
      exact (stabSub R).mul_mem ((stabSub R).mul_mem ((stabSub R).inv_mem haS) htR') haS
    · have hconj : ∀ k : ℤ, (a⁻¹ * t * a) ^ k = a⁻¹ * t ^ k * a := by
        intro k
        have := conj_zpow (a := a⁻¹) (b := t) (i := k)
        simpa using this
      have key : commSub R (Subgroup.zpowers (a⁻¹ * t * a)) =
          (commSub R (Subgroup.zpowers t)).map (a⁻¹ : MulAut W).toMonoidHom := by
        apply le_antisymm
        · rw [commSub, Subgroup.closure_le]
          rintro _ ⟨x, hx, w, hw, rfl⟩
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [hconj]
          refine ⟨(t ^ k) (a w) * (a w)⁻¹, Subgroup.subset_closure
            ⟨t ^ k, Subgroup.zpow_mem_zpowers t k, a w, (hAR a ha w).2 hw, rfl⟩, ?_⟩
          simp [MulAut.mul_apply, MulAut.inv_apply]
        · rw [Subgroup.map_le_iff_le_comap, commSub, Subgroup.closure_le]
          rintro _ ⟨x, hx, w, hw, rfl⟩
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          rw [SetLike.mem_coe, Subgroup.mem_comap]
          refine Subgroup.subset_closure ⟨(a⁻¹ * t * a) ^ k, Subgroup.zpow_mem_zpowers _ k,
            a⁻¹ w, (hAR a⁻¹ (A.inv_mem ha) w).2 hw, ?_⟩
          rw [hconj]
          simp [MulAut.mul_apply, MulAut.inv_apply]
      rw [key]
      unfold rk at hrk1 ⊢
      rw [Subgroup.card_map_of_injective (f := (a⁻¹ : MulAut W).toMonoidHom)
        (a⁻¹ : MulAut W).injective]
      exact hrk1
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1

@[expose] def s15Blocks (A : Subgroup (MulAut W)) (R₁ : Subgroup W) : Set (Subgroup W) :=
  {X | ∃ a ∈ A, X = R₁.map a.toMonoidHom}

private lemma s15_Three_mem_fixV_zpowers_of {t : MulAut W} {x : W} (h : t x = x) :
    x ∈ fixV (Subgroup.zpowers t) := by
  rw [mem_fixV]
  intro s hs
  have hle : Subgroup.zpowers t ≤ MulAction.stabilizer (MulAut W) x := by
    rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact h
  have := hle hs
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

private theorem s15_Three_tconj_mem {A : Subgroup (MulAut W)} {t a : MulAut W} (ha : a ∈ A) :
    a⁻¹ * t * a ∈ s15TGroup A t :=
  Subgroup.subset_closure ⟨a, ha, rfl⟩

private theorem s15_Three_tgroup_conj {A : Subgroup (MulAut W)} {t a j : MulAut W} (ha : a ∈ A)
    (hj : j ∈ s15TGroup A t) : a⁻¹ * j * a ∈ s15TGroup A t := by
  refine Subgroup.closure_induction (p := fun g _ => a⁻¹ * g * a ∈ s15TGroup A t) ?_ ?_ ?_ ?_ hj
  · rintro x ⟨b, hb, rfl⟩
    have h : a⁻¹ * (b⁻¹ * t * b) * a = (b * a)⁻¹ * t * (b * a) := by group
    rw [h]
    exact Subgroup.subset_closure ⟨b * a, A.mul_mem hb ha, rfl⟩
  · simp
  · intro x y _ _ ihx ihy
    have h : a⁻¹ * (x * y) * a = (a⁻¹ * x * a) * (a⁻¹ * y * a) := by group
    rw [h]
    exact (s15TGroup A t).mul_mem ihx ihy
  · intro x _ ihx
    have h : a⁻¹ * x⁻¹ * a = (a⁻¹ * x * a)⁻¹ := by group
    rw [h]
    exact (s15TGroup A t).inv_mem ihx

private theorem s15_Three_tgroup_stable {A : Subgroup (MulAut W)} {t : MulAut W}
    {R : Subgroup W} (hR : StableUnder A R) (hRt : StableUnder (Subgroup.zpowers t) R) :
    StableUnder (s15TGroup A t) R := by
  have hgen : ∀ x ∈ ({x | ∃ a ∈ A, x = a⁻¹ * t * a} : Set (MulAut W)), x ∈ stabSub R := by
    rintro x ⟨b, hb, rfl⟩ u
    constructor
    · intro h
      have h1 : b ((b⁻¹ * t * b) u) ∈ R := hR b hb _ h
      have h1' : t (b u) ∈ R := by
        convert h1 using 1
        simp [MulAut.mul_apply, MulAut.inv_apply]
      have h2 : t⁻¹ (t (b u)) ∈ R :=
        hRt t⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers t)) _ h1'
      have h2' : b u ∈ R := by simpa [MulAut.inv_apply] using h2
      have h3 : b⁻¹ (b u) ∈ R := hR b⁻¹ (A.inv_mem hb) _ h2'
      simpa [MulAut.inv_apply] using h3
    · intro h
      have h1 : b u ∈ R := hR b hb u h
      have h2 : t (b u) ∈ R := hRt t (Subgroup.mem_zpowers t) _ h1
      have h3 : b⁻¹ (t (b u)) ∈ R := hR b⁻¹ (A.inv_mem hb) _ h2
      simpa [MulAut.mul_apply, MulAut.inv_apply] using h3
  intro j hj u hu
  exact ((((Subgroup.closure_le (stabSub R)).2 hgen) hj) u).2 hu

private theorem s15_Three_J_exists_irr_le {J : Subgroup (MulAut W)} {X : Subgroup W}
    (hX : StableUnder J X) (h : X ≠ ⊥) : ∃ I : Subgroup W, I ≤ X ∧ IsIrrOn J I ⊥ := by
  classical
  let s : Set (Subgroup W) := {I | I ≤ X ∧ StableUnder J I ∧ I ≠ ⊥}
  have hwf : WellFounded (InvImage (· < ·) (fun a : Subgroup W => Nat.card a)) :=
    InvImage.wf (fun a : Subgroup W => Nat.card a) wellFounded_lt
  have hsne : s.Nonempty := ⟨X, le_rfl, hX, h⟩
  obtain ⟨I, hIs, hImin⟩ := hwf.has_min s hsne
  refine ⟨I, hIs.1, ?_⟩
  refine ⟨bot_lt_iff_ne_bot.2 hIs.2.2, hIs.2.1, ?_, ?_⟩
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu
    rw [Subgroup.mem_bot, hu, map_one]
  · intro K hK _ hKI
    by_cases hKbot : K = ⊥
    · exact Or.inl hKbot
    · refine Or.inr ?_
      by_contra hne
      have hKs : K ∈ s := ⟨hKI.trans hIs.1, hK, hKbot⟩
      exact hImin K hKs (Subgroup.card_lt_of_lt (lt_of_le_of_ne hKI hne))

private theorem s15_Three_irr_map_tgroup {A : Subgroup (MulAut W)} {t a : MulAut W}
    {X : Subgroup W} (hX : IsIrrOn (s15TGroup A t) X ⊥) (ha : a ∈ A) :
    IsIrrOn (s15TGroup A t) (X.map a.toMonoidHom) ⊥ := by
  have hne : X.map a.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hX.1.ne' ((Subgroup.map_eq_bot_iff_of_injective (f := a.toMonoidHom) X
      a.injective).1 hbot)
  refine ⟨bot_lt_iff_ne_bot.2 hne, ?_, ?_, ?_⟩
  · rintro j hj y ⟨x, hxX, hxeq⟩
    refine ⟨(a⁻¹ * j * a) x, hX.2.1 _ (s15_Three_tgroup_conj ha hj) x hxX, ?_⟩
    rw [← hxeq]
    simp [MulAut.mul_apply, MulAut.inv_apply]
  · intro x _ u hu
    rw [Subgroup.mem_bot] at hu
    rw [Subgroup.mem_bot, hu, map_one]
  · intro K hK _ hKle
    have hYstab : StableUnder (s15TGroup A t) (K.comap a.toMonoidHom) := by
      intro j hj y hy
      have hconj : a * j * a⁻¹ ∈ s15TGroup A t := by
        have := s15_Three_tgroup_conj (A := A) (t := t) (a := a⁻¹) (j := j) (A.inv_mem ha) hj
        simpa [MulAut.inv_apply] using this
      have hmem : (a * j * a⁻¹) (a y) ∈ K := hK _ hconj _ hy
      have heq : a.toMonoidHom (j y) = (a * j * a⁻¹) (a y) := by
        simp [MulAut.mul_apply, MulAut.inv_apply]
      show a.toMonoidHom (j y) ∈ K
      rw [heq]
      exact hmem
    have hYle : K.comap a.toMonoidHom ≤ X := by
      intro y hy
      obtain ⟨x, hxX, hx⟩ := Subgroup.mem_map.1 (hKle hy)
      have hxy : x = y := a.injective hx
      rwa [← hxy]
    rcases hX.2.2.2 (K.comap a.toMonoidHom) hYstab bot_le hYle with hY | hY
    · left
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := a.toMonoidHom) a.surjective K, hY,
        Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self_of_surjective (f := a.toMonoidHom) a.surjective K, hY]

private theorem s15_Three_card_comm_two (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : InducesTransvection t ⊤) : Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) = 2 := by
  rw [card_eq_two_pow hW (commSub ⊤ (Subgroup.zpowers t)), ht.2, pow_one]

private theorem s15_Three_blocks_map {A : Subgroup (MulAut W)} {R₁ X : Subgroup W}
    {a : MulAut W} (ha : a ∈ A) (hX : X ∈ s15Blocks A R₁) :
    X.map a.toMonoidHom ∈ s15Blocks A R₁ := by
  obtain ⟨b, hb, rfl⟩ := hX
  refine ⟨a * b, A.mul_mem ha hb, ?_⟩
  rw [Subgroup.map_map]
  rfl

private theorem s15_Three_blocks_inf {A : Subgroup (MulAut W)} {t : MulAut W}
    {R₁ X : Subgroup W} (hJ : IsIrrOn (s15TGroup A t) R₁ ⊥)
    (hX : X ∈ s15Blocks A R₁) (hne : X ≠ R₁) : X ⊓ R₁ = ⊥ := by
  obtain ⟨a, ha, rfl⟩ := hX
  have hXirr : IsIrrOn (s15TGroup A t) (R₁.map a.toMonoidHom) ⊥ :=
    s15_Three_irr_map_tgroup hJ ha
  have hstab : StableUnder (s15TGroup A t) (R₁.map a.toMonoidHom ⊓ R₁) := fun j hj u hu =>
    ⟨hXirr.2.1 j hj u hu.1, hJ.2.1 j hj u hu.2⟩
  rcases hJ.2.2.2 (R₁.map a.toMonoidHom ⊓ R₁) hstab bot_le inf_le_right with h | h
  · exact h
  · exfalso
    have hle : R₁ ≤ R₁.map a.toMonoidHom := (le_of_eq h.symm).trans inf_le_left
    rcases hXirr.2.2.2 R₁ hJ.2.1 bot_le hle with hbot | heq
    · exact (ne_of_gt hJ.1) hbot
    · exact hne heq.symm

private theorem s15_Three_sSup_blocks_stable {A : Subgroup (MulAut W)} {R₁ : Subgroup W} :
    StableUnder A (sSup (s15Blocks A R₁)) := by
  intro a ha u hu
  have hmap : (sSup (s15Blocks A R₁)).map a.toMonoidHom ≤ sSup (s15Blocks A R₁) := by
    rw [sSup_eq_iSup', Subgroup.map_iSup]
    exact iSup_le fun X =>
      le_iSup (fun Y : ↥(s15Blocks A R₁) => (Y : Subgroup W))
        ⟨(X : Subgroup W).map a.toMonoidHom, s15_Three_blocks_map ha X.2⟩
  exact hmap (Subgroup.mem_map_of_mem a.toMonoidHom hu)

private theorem s15_Three_blocks_conj_eq {A : Subgroup (MulAut W)} {R₀ : Subgroup W}
    {a₀ : MulAut W} (ha₀ : a₀ ∈ A) :
    s15Blocks A (R₀.map a₀.toMonoidHom) = s15Blocks A R₀ := by
  ext X
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a * a₀, A.mul_mem ha ha₀, ?_⟩
    rw [Subgroup.map_map]
    rfl
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a * a₀⁻¹, A.mul_mem ha (A.inv_mem ha₀), ?_⟩
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.mul_apply, MulAut.inv_apply]

private theorem s15_Three_sSup_blocks_of_stab {A : Subgroup (MulAut W)} {R₁ : Subgroup W}
    (h : ∀ a ∈ A, R₁.map a.toMonoidHom = R₁) : sSup (s15Blocks A R₁) = R₁ := by
  apply le_antisymm
  · apply sSup_le
    rintro X ⟨a, ha, rfl⟩
    exact le_of_eq (h a ha)
  · refine le_sSup ⟨1, A.one_mem, ?_⟩
    change R₁ = Subgroup.map (MonoidHom.id W) R₁
    rw [Subgroup.map_id]

theorem s15_Three_blocks_exists {A : Subgroup (MulAut W)} {t : MulAut W} {R : Subgroup W}
    (hR : IsIrrOn A R ⊥) (hRt : StableUnder (Subgroup.zpowers t) R)
    (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) :
    ∃ R₁ : Subgroup W, R₁ ≤ R ∧ IsIrrOn (s15TGroup A t) R₁ ⊥ ∧
      commSub R₁ (Subgroup.zpowers t) ≠ ⊥ ∧ sSup (s15Blocks A R₁) = R := by
  have hRstab : StableUnder (s15TGroup A t) R := s15_Three_tgroup_stable hR.2.1 hRt
  obtain ⟨R₀, hR₀R, hR₀⟩ := s15_Three_J_exists_irr_le hRstab hR.1.ne'
  have hle : ∀ a ∈ A, R₀.map a.toMonoidHom ≤ R := by
    intro a ha
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    exact hR.2.1 a ha x (hR₀R hx)
  have hsum_le : sSup (s15Blocks A R₀) ≤ R := by
    apply sSup_le
    rintro X ⟨a, ha, rfl⟩
    exact hle a ha
  have hsum_ge : R₀ ≤ sSup (s15Blocks A R₀) := by
    refine le_sSup ⟨1, A.one_mem, ?_⟩
    change R₀ = Subgroup.map (MonoidHom.id W) R₀
    rw [Subgroup.map_id]
  have hsum_ne : sSup (s15Blocks A R₀) ≠ ⊥ := by
    intro hbot
    exact hR₀.1.ne' (le_bot_iff.mp (hsum_ge.trans (le_of_eq hbot)))
  have hsum : sSup (s15Blocks A R₀) = R := by
    rcases hR.2.2.2 (sSup (s15Blocks A R₀)) s15_Three_sSup_blocks_stable bot_le hsum_le with
      h | h
    · exact absurd h hsum_ne
    · exact h
  have hex : ∃ a ∈ A, ¬ R₀.map a.toMonoidHom ≤ fixV (Subgroup.zpowers t) := by
    by_contra hnone
    push Not at hnone
    have hfixle : sSup (s15Blocks A R₀) ≤ fixV (Subgroup.zpowers t) := by
      apply sSup_le
      rintro X ⟨a, ha, rfl⟩
      exact hnone a ha
    rw [hsum] at hfixle
    exact htR (commSub_eq_bot_iff.2 hfixle)
  obtain ⟨a₀, ha₀, ha₀fix⟩ := hex
  refine ⟨R₀.map a₀.toMonoidHom, hle a₀ ha₀, s15_Three_irr_map_tgroup hR₀ ha₀, ?_, ?_⟩
  · intro hbot
    exact ha₀fix (commSub_eq_bot_iff.1 hbot)
  · rw [s15_Three_blocks_conj_eq ha₀, hsum]

theorem s15_Three_blocks_fix (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) {R₁ : Subgroup W} (hJ : IsIrrOn (s15TGroup A t) R₁ ⊥)
    (htR₁ : commSub R₁ (Subgroup.zpowers t) ≠ ⊥) :
    ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t) := by
  intro X hX hne
  obtain ⟨a, ha, rfl⟩ := hX
  have hXirr : IsIrrOn (s15TGroup A t) (R₁.map a.toMonoidHom) ⊥ :=
    s15_Three_irr_map_tgroup hJ ha
  have hinf : R₁.map a.toMonoidHom ⊓ R₁ = ⊥ := s15_Three_blocks_inf hJ ⟨a, ha, rfl⟩ hne
  have htJ : t ∈ s15TGroup A t := by
    have := s15_Three_tconj_mem (A := A) (t := t) (a := 1) A.one_mem
    simpa using this
  have hzt : Subgroup.zpowers t ≤ s15TGroup A t := Subgroup.zpowers_le.2 htJ
  have hXt : StableUnder (Subgroup.zpowers t) (R₁.map a.toMonoidHom) :=
    fun s hs u hu => hXirr.2.1 s (hzt hs) u hu
  have hR₁t : StableUnder (Subgroup.zpowers t) R₁ :=
    fun s hs u hu => hJ.2.1 s (hzt hs) u hu
  by_contra hXle
  have hxexists : ∃ x ∈ R₁.map a.toMonoidHom, x ∉ fixV (Subgroup.zpowers t) := by
    by_contra h
    apply hXle
    intro x hx
    by_contra hxnot
    exact h ⟨x, hx, hxnot⟩
  obtain ⟨x, hxX, hxfix⟩ := hxexists
  have htx : t x ≠ x := fun h => hxfix (s15_Three_mem_fixV_zpowers_of h)
  have hnotfixR₁ : ¬ R₁ ≤ fixV (Subgroup.zpowers t) :=
    fun h => htR₁ (commSub_eq_bot_iff.2 h)
  have hrexists : ∃ r ∈ R₁, r ∉ fixV (Subgroup.zpowers t) := by
    by_contra h
    apply hnotfixR₁
    intro r hr
    by_contra hrnot
    exact h ⟨r, hr, hrnot⟩
  obtain ⟨r, hrR₁, hrfix⟩ := hrexists
  have htr : t r ≠ r := fun h => hrfix (s15_Three_mem_fixV_zpowers_of h)
  have hc₁mem : t x * x⁻¹ ∈ R₁.map a.toMonoidHom :=
    (R₁.map a.toMonoidHom).mul_mem (hXt t (Subgroup.mem_zpowers t) x hxX)
      ((R₁.map a.toMonoidHom).inv_mem hxX)
  have hc₁ne : t x * x⁻¹ ≠ 1 := fun h => htx (mul_inv_eq_one.mp h)
  have hc₁comm : t x * x⁻¹ ∈ commSub ⊤ (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, x, Subgroup.mem_top x, rfl⟩
  have hc₂mem : t r * r⁻¹ ∈ R₁ :=
    R₁.mul_mem (hR₁t t (Subgroup.mem_zpowers t) r hrR₁) (R₁.inv_mem hrR₁)
  have hc₂ne : t r * r⁻¹ ≠ 1 := fun h => htr (mul_inv_eq_one.mp h)
  have hc₂comm : t r * r⁻¹ ∈ commSub ⊤ (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, r, Subgroup.mem_top r, rfl⟩
  have hcard : Nat.card ↥(commSub ⊤ (Subgroup.zpowers t)) = 2 :=
    s15_Three_card_comm_two hW ht
  obtain ⟨y, _, hyuniq⟩ :=
    (Nat.card_eq_two_iff' (1 : ↥(commSub ⊤ (Subgroup.zpowers t)))).1 hcard
  have h1 : (⟨t x * x⁻¹, hc₁comm⟩ : ↥(commSub ⊤ (Subgroup.zpowers t))) = y :=
    hyuniq _ (fun h => hc₁ne (by simpa using Subtype.ext_iff.mp h))
  have h2 : (⟨t r * r⁻¹, hc₂comm⟩ : ↥(commSub ⊤ (Subgroup.zpowers t))) = y :=
    hyuniq _ (fun h => hc₂ne (by simpa using Subtype.ext_iff.mp h))
  have hceq : t x * x⁻¹ = t r * r⁻¹ := by
    have := h1.trans h2.symm
    exact congrArg Subtype.val this
  have : t x * x⁻¹ ∈ R₁.map a.toMonoidHom ⊓ R₁ :=
    ⟨hc₁mem, by rw [hceq]; exact hc₂mem⟩
  rw [hinf] at this
  exact hc₁ne (Subgroup.mem_bot.1 this)

theorem s15_Three_blocks (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {t : MulAut W}
    (ht : InducesTransvection t ⊤) {R : Subgroup W} (hR : IsIrrOn A R ⊥)
    (hRt : StableUnder (Subgroup.zpowers t) R) (htR : commSub R (Subgroup.zpowers t) ≠ ⊥) :
    ∃ R₁ : Subgroup W, R₁ ≤ R ∧ IsIrrOn (s15TGroup A t) R₁ ⊥ ∧
      commSub R₁ (Subgroup.zpowers t) ≠ ⊥ ∧ sSup (s15Blocks A R₁) = R ∧
      ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t) := by
  obtain ⟨R₁, h1, h2, h3, h4⟩ := s15_Three_blocks_exists hR hRt htR
  exact ⟨R₁, h1, h2, h3, h4, s15_Three_blocks_fix hW ht h2 h3⟩

theorem s15_Three_one_block_conj {A : Subgroup (MulAut W)} {t : MulAut W} {R R₁ : Subgroup W}
    (hJ : IsIrrOn (s15TGroup A t) R₁ ⊥) (htR₁ : commSub R₁ (Subgroup.zpowers t) ≠ ⊥)
    (hsup : sSup (s15Blocks A R₁) = R)
    (hfix : ∀ X ∈ s15Blocks A R₁, X ≠ R₁ → X ≤ fixV (Subgroup.zpowers t))
    (hconj : ∀ a ∈ A, ∃ e ∈ s15TGroup A t, a⁻¹ * t * a = e⁻¹ * t * e) : R₁ = R := by
  have hstab : ∀ a ∈ A, R₁.map a.toMonoidHom = R₁ := by
    intro a ha
    by_contra hne
    have hle := hfix (R₁.map a.toMonoidHom) ⟨a, ha, rfl⟩ hne
    have hnotfix : ¬ R₁ ≤ fixV (Subgroup.zpowers t) :=
      fun h => htR₁ (commSub_eq_bot_iff.2 h)
    have hrexists : ∃ r ∈ R₁, r ∉ fixV (Subgroup.zpowers t) := by
      by_contra h
      apply hnotfix
      intro r hr
      by_contra hrnot
      exact h ⟨r, hr, hrnot⟩
    obtain ⟨r, hrR₁, hrfix⟩ := hrexists
    have htr : t r ≠ r := fun h => hrfix (s15_Three_mem_fixV_zpowers_of h)
    obtain ⟨e, he, heq⟩ := hconj a ha
    have heu : e⁻¹ r ∈ R₁ := hJ.2.1 e⁻¹ ((s15TGroup A t).inv_mem he) r hrR₁
    have hkey : t (a (e⁻¹ r)) ≠ a (e⁻¹ r) := by
      intro hta
      have h1 : (a⁻¹ * t * a) (e⁻¹ r) = e⁻¹ r := by
        rw [show (a⁻¹ * t * a) (e⁻¹ r) = a⁻¹ (t (a (e⁻¹ r))) by
          simp [MulAut.mul_apply], hta]
        simp [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [heq] at h1
      have h2 : (e⁻¹ * t * e) (e⁻¹ r) = e⁻¹ (t r) := by
        simp [MulAut.mul_apply, MulAut.inv_apply]
      rw [h2] at h1
      exact htr ((e⁻¹).injective h1)
    have hyfix : a (e⁻¹ r) ∉ fixV (Subgroup.zpowers t) := fun hy =>
      hkey ((mem_fixV.1 hy) t (Subgroup.mem_zpowers t))
    exact hyfix (hle ⟨e⁻¹ r, heu, rfl⟩)
  exact (s15_Three_sSup_blocks_of_stab hstab).symm.trans hsup

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
