module

public import CFSG.RankThree.GF2n.Tim79aSUGenFour
public import CFSG.Timmesfeld.Transvection.ModelSUTransitiveWitt
public import CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput.SUEmbed

public section

namespace CFSG.Timmesfeld.Transvection.ModelRank

open Matrix CFSG.LieType.Universal.Unitary CFSG.Timmesfeld.LieEmbed CFSG.LieType.BorelTits
  CFSG.AGLEmbedding.LeviBlock CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput

section Extend

variable {F : Type} [Field F] {σ : F ≃+* F} {n' n : ℕ} {τ : Fin n' → Fin n}

@[expose] noncomputable def extByZero (τ : Fin n' → Fin n) (u : Fin n' → F) : Fin n → F :=
  Function.extend τ u 0

theorem extByZero_apply (hτ : Function.Injective τ) (u : Fin n' → F) (i : Fin n') :
    extByZero τ u (τ i) = u i :=
  hτ.extend_apply u 0 i

theorem extByZero_apply_of_not_mem (u : Fin n' → F) {x : Fin n} (hx : x ∉ Set.range τ) :
    extByZero τ u x = 0 :=
  Function.extend_apply' _ _ _ hx

theorem extByZero_eq_of_apply (hτ : Function.Injective τ) {v : Fin n → F}
    (hv : ∀ x, x ∉ Set.range τ → v x = 0) : extByZero τ (v ∘ τ) = v := by
  funext x
  by_cases hx : x ∈ Set.range τ
  · obtain ⟨i, rfl⟩ := hx
    rw [extByZero_apply hτ]
    rfl
  · rw [extByZero_apply_of_not_mem _ hx, hv x hx]

theorem uForm_extByZero (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))
    (u u' : Fin n' → F) : uForm σ (extByZero τ u) (extByZero τ u') = uForm σ u u' := by
  rw [uForm_eq, uForm_eq]
  symm
  refine Fintype.sum_of_injective τ hτ (fun i => σ (u i) * u' (Fin.rev i)) _
    (fun x hx => ?_) fun i => ?_
  · rw [extByZero_apply_of_not_mem _ hx, map_zero, zero_mul]
  · rw [extByZero_apply hτ, ← hr, extByZero_apply hτ]

theorem extByZero_ne_zero (hτ : Function.Injective τ) {u : Fin n' → F} (hu : u ≠ 0) :
    extByZero τ u ≠ 0 := by
  intro h
  apply hu
  funext i
  have := congrFun h (τ i)
  rwa [extByZero_apply hτ] at this

theorem extendMat_mulVec_extByZero (hτ : Function.Injective τ) (B : Matrix (Fin n') (Fin n') F)
    (u : Fin n' → F) : extendMat hτ B *ᵥ extByZero τ u = extByZero τ (B *ᵥ u) := by
  funext x
  by_cases hx : x ∈ Set.range τ
  · obtain ⟨i, rfl⟩ := hx
    rw [extByZero_apply hτ]
    simp only [mulVec, dotProduct]
    symm
    refine Fintype.sum_of_injective τ hτ _ _ (fun y hy => ?_) fun j => ?_
    · rw [extByZero_apply_of_not_mem _ hy, mul_zero]
    · rw [extendMat_apply_map, extByZero_apply hτ]
  · rw [extByZero_apply_of_not_mem _ hx]
    have h : ∀ y, extendMat hτ B x y = (1 : Matrix (Fin n) (Fin n) F) x y := fun y =>
      extendMat_apply_of_not_mem hτ B (Or.inl hx)
    simp only [mulVec, dotProduct, h]
    exact (congrFun (one_mulVec (extByZero τ u)) x).trans (extByZero_apply_of_not_mem _ hx)

theorem extendMat_mulVec_single (hτ : Function.Injective τ) (B : Matrix (Fin n') (Fin n') F)
    {k : Fin n} (hk : k ∉ Set.range τ) :
    extendMat hτ B *ᵥ (Pi.single k 1 : Fin n → F) = Pi.single k 1 := by
  rw [mulVec_single_one]
  funext x
  show extendMat hτ B x k = _
  rw [extendMat_apply_of_not_mem hτ B (Or.inr hk), Matrix.one_apply, Pi.single_apply]

theorem extendMat_uTrans (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))
    (u : Fin n' → F) (c : F) : extendMat hτ (uTrans σ u c) = uTrans σ (extByZero τ u) c := by
  ext x y
  simp only [uTrans, uNil, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, uRow_apply,
    smul_eq_mul]
  by_cases hxy : x ∈ Set.range τ ∧ y ∈ Set.range τ
  · obtain ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩ := hxy
    rw [extendMat_apply_map, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, uRow_apply,
      smul_eq_mul, ← hr, extByZero_apply hτ, extByZero_apply hτ]
    congr 1
    simp only [Matrix.one_apply, hτ.eq_iff]
  · have h : x ∉ Set.range τ ∨ y ∉ Set.range τ := by tauto
    rw [extendMat_apply_of_not_mem hτ _ h]
    have h0 : extByZero τ u x * σ (extByZero τ u (Fin.rev y)) = 0 := by
      rcases h with hx | hy
      · rw [extByZero_apply_of_not_mem _ hx, zero_mul]
      · have hy' : Fin.rev y ∉ Set.range τ := fun ⟨i, hi⟩ =>
          hy ⟨Fin.rev i, by rw [hr, hi, Fin.rev_rev]⟩
        rw [extByZero_apply_of_not_mem _ hy', map_zero, mul_zero]
    rw [h0, mul_zero, add_zero]

variable (σ) in
theorem suMat_suEmbed_eq (hτ : Function.Injective τ) (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i))
    (g : SU σ n') : suMat σ n (suEmbed σ hτ hr g) = extendMat hτ (suMat σ n' g) :=
  rfl

theorem comap_eq_top_of_frame (hσ : ∀ c, σ (σ c) = c) (hτ : Function.Injective τ)
    (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) {U : List (Fin n' → F)}
    (hU : ∀ L : Subgroup (SU σ n'), (∀ u ∈ U, UTransLe L u) → L = ⊤)
    {L : Subgroup (SU σ n)} (hL : ∀ u ∈ U, UTransLe L (extByZero τ u)) :
    L.comap (suEmbed σ hτ hr) = ⊤ := by
  refine hU _ fun u hu c y hc hy => ?_
  show suEmbed σ hτ hr y ∈ L
  refine hL u hu c _ hc ?_
  rw [suMat_suEmbed_eq, hy, extendMat_uTrans hτ hr]

theorem uTransLe_extByZero_of_comap (hσ : ∀ c, σ (σ c) = c) (hτ : Function.Injective τ)
    (hr : ∀ i, τ (Fin.rev i) = Fin.rev (τ i)) {L : Subgroup (SU σ n)}
    (hL : L.comap (suEmbed σ hτ hr) = ⊤) {v : Fin n' → F} (hvv : uForm σ v v = 0) :
    UTransLe L (extByZero τ v) := by
  intro c x hc hx
  obtain ⟨y, hy⟩ := exists_suMat_eq_uTrans hσ hvv hc
  have hyL : suEmbed σ hτ hr y ∈ L := by
    have : y ∈ L.comap (suEmbed σ hτ hr) := by rw [hL]; trivial
    exact this
  have hxy : suEmbed σ hτ hr y = x := by
    apply suMat_injective σ
    rw [suMat_suEmbed_eq, hy, extendMat_uTrans hτ hr, hx]
  rwa [hxy] at hyL

end Extend

section Steps

variable {F : Type} [Field F]

@[expose] def innerEmb (m : ℕ) : Fin m → Fin (m + 2) := fun i => i.castSucc.succ

theorem innerEmb_injective (m : ℕ) : Function.Injective (innerEmb m) :=
  fun _ _ h => Fin.castSucc_injective _ (Fin.succ_injective _ h)

theorem innerEmb_rev (m : ℕ) (i : Fin m) : innerEmb m (Fin.rev i) = Fin.rev (innerEmb m i) := by
  ext
  simp only [innerEmb, Fin.val_succ, Fin.coe_castSucc, Fin.val_rev]
  omega

theorem mem_range_innerEmb {m : ℕ} {x : Fin (m + 2)} (h0 : x ≠ 0) (hl : x ≠ Fin.last (m + 1)) :
    x ∈ Set.range (innerEmb m) := by
  have h0' : x.val ≠ 0 := fun h => h0 (Fin.ext h)
  have hl' : x.val ≠ m + 1 := fun h => hl (Fin.ext h)
  refine ⟨⟨x.val - 1, by omega⟩, ?_⟩
  ext
  simp only [innerEmb, Fin.val_succ, Fin.coe_castSucc]
  omega

theorem zero_not_mem_range_innerEmb (m : ℕ) : (0 : Fin (m + 2)) ∉ Set.range (innerEmb m) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp [innerEmb] at this

theorem last_not_mem_range_innerEmb (m : ℕ) :
    Fin.last (m + 1) ∉ Set.range (innerEmb m) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp only [innerEmb, Fin.val_succ, Fin.coe_castSucc, Fin.val_last] at this
  omega

variable [Finite F] [CharP F 2] {f : ℕ}

theorem suFrameGen_add_two (hF : Nat.card F = (2 ^ f) ^ 2) {m k : ℕ} (hm : 2 ≤ m)
    (h : SUFrameGen (unitaryInvolution F 2 f) m k) :
    SUFrameGen (unitaryInvolution F 2 f) (m + 2) (k + 4) := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨U, hUlen, hUiso, hU⟩ := h
  obtain ⟨l, hl⟩ := exists_add_unitaryInvolution_eq hF (a := 1) (map_one _)
  have hτ := innerEmb_injective m
  have hr := innerEmb_rev m
  set a : Fin (m + 2) → F := Pi.single 0 1 with hadef
  set d : Fin (m + 2) → F := Pi.single (Fin.last (m + 1)) 1 with hddef
  set i₀ : Fin m := ⟨0, by omega⟩ with hi₀
  set w₀ : Fin (m + 2) → F := extByZero (innerEmb m) (Pi.single i₀ 1) with hw₀def
  have hi₀r : i₀ ≠ Fin.rev i₀ := by
    intro h
    have := congrArg Fin.val h
    simp [hi₀, Fin.val_rev] at this
    omega
  have h0l : (0 : Fin (m + 2)) ≠ Fin.rev 0 := by
    rw [Fin.rev_zero]
    intro h
    have := congrArg Fin.val h
    simp at this
  have hl0 : Fin.last (m + 1) ≠ Fin.rev (Fin.last (m + 1)) := by
    rw [Fin.rev_last]
    intro h
    have := congrArg Fin.val h
    simp at this
  have haa : uForm (unitaryInvolution F 2 f) a a = 0 := uForm_single_self h0l
  have hdd : uForm (unitaryInvolution F 2 f) d d = 0 := uForm_single_self hl0
  have had : uForm (unitaryInvolution F 2 f) a d = 1 := by
    rw [hadef, hddef, uForm_single_left, Fin.rev_zero, Pi.single_eq_same]
  have ha_x : ∀ x : Fin (m + 2) → F, uForm (unitaryInvolution F 2 f) a x = x (Fin.last (m + 1)) :=
    fun x => by rw [hadef, uForm_single_left, Fin.rev_zero]
  have hd_x : ∀ x : Fin (m + 2) → F, uForm (unitaryInvolution F 2 f) d x = x 0 :=
    fun x => by rw [hddef, uForm_single_left, Fin.rev_last]
  have hw₀0' : w₀ 0 = 0 := extByZero_apply_of_not_mem _ (zero_not_mem_range_innerEmb m)
  have hw₀l : w₀ (Fin.last (m + 1)) = 0 :=
    extByZero_apply_of_not_mem _ (last_not_mem_range_innerEmb m)
  have hw₀ : w₀ ∈ perpPair (unitaryInvolution F 2 f) a d :=
    ⟨by rw [ha_x, hw₀l], by rw [hd_x, hw₀0']⟩
  have hw₀0 : w₀ ≠ 0 := extByZero_ne_zero hτ (single_one_ne_zero i₀)
  have hw₀w₀ : uForm (unitaryInvolution F 2 f) w₀ w₀ = 0 := by
    rw [hw₀def, uForm_extByZero hτ hr, uForm_single_self hi₀r]
  have hsum_iso : ∀ c : F, uForm (unitaryInvolution F 2 f) (a + c • w₀) (a + c • w₀) = 0 := by
    intro c
    have hwa : uForm (unitaryInvolution F 2 f) w₀ a = 0 := uForm_eq_zero_comm hσ hw₀.1
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right, haa, hw₀w₀,
      hw₀.1, hwa, mul_zero, add_zero]
  have hsum_ne : ∀ c : F, a + c • w₀ ≠ 0 := by
    intro c h0
    have := congrFun h0 0
    rw [Pi.add_apply, Pi.smul_apply, hw₀0', smul_zero, add_zero, hadef, Pi.single_eq_same] at this
    exact one_ne_zero this
  refine ⟨[a, d, a + (1 : F) • w₀, a + l • w₀] ++ U.map (extByZero (innerEmb m)), ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
    omega
  · intro u hu
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map] at hu
    rcases hu with ((rfl | rfl | rfl | rfl) | ⟨u', hu', rfl⟩)
    · exact ⟨single_one_ne_zero _, haa⟩
    · exact ⟨single_one_ne_zero _, hdd⟩
    · exact ⟨hsum_ne 1, hsum_iso 1⟩
    · exact ⟨hsum_ne l, hsum_iso l⟩
    · exact ⟨extByZero_ne_zero hτ (hUiso u' hu').1, by rw [uForm_extByZero hτ hr, (hUiso u' hu').2]⟩
  · intro L hL
    have hLa : UTransLe L a := hL a (by simp)
    have hLd : UTransLe L d := hL d (by simp)
    have hL1 : UTransLe L (a + (1 : F) • w₀) := hL _ (by simp)
    have hLl : UTransLe L (a + l • w₀) := hL _ (by simp)
    have hcomap := comap_eq_top_of_frame hσ hτ hr hU (L := L)
      (fun u hu => hL _ (List.mem_append_right _ (List.mem_map_of_mem hu)))
    have hP : ∀ v ∈ perpPair (unitaryInvolution F 2 f) a d,
        uForm (unitaryInvolution F 2 f) v v = 0 → UTransLe L v := by
      intro v hv hvv
      have hvext : extByZero (innerEmb m) (v ∘ innerEmb m) = v := by
        refine extByZero_eq_of_apply hτ fun x hx => ?_
        by_cases hx0 : x = 0
        · rw [hx0, ← hd_x v]
          exact hv.2
        · by_cases hxl : x = Fin.last (m + 1)
          · rw [hxl, ← ha_x v]
            exact hv.1
          · exact absurd (mem_range_innerEmb hx0 hxl) hx
      rw [← hvext]
      refine uTransLe_extByZero_of_comap hσ hτ hr hcomap ?_
      rw [← uForm_extByZero hτ hr, hvext, hvv]
    have hLw : UTransLe L w₀ := hP w₀ hw₀ hw₀w₀
    have haw : uForm (unitaryInvolution F 2 f) a w₀ = 0 := hw₀.1
    refine eq_top_of_uTransLe_pair hF (by omega) haa hdd had hw₀ hw₀0 hw₀w₀ hLa hLd hP ?_
    intro ν
    obtain ⟨c₂, hc₂def⟩ : ∃ c : F, c = ν + unitaryInvolution F 2 f ν := ⟨_, rfl⟩
    obtain ⟨c₁, hc₁def⟩ : ∃ c : F, c = ν + c₂ * l := ⟨_, rfl⟩
    have hσc₂ : unitaryInvolution F 2 f c₂ = c₂ := by rw [hc₂def, map_add, hσ, add_comm]
    have hc₂ : c₂ + unitaryInvolution F 2 f c₂ = 0 := by
      rw [hσc₂]; exact CharTwo.add_self_eq_zero c₂
    have hc₁ : c₁ + unitaryInvolution F 2 f c₁ = 0 := by
      rw [hc₁def, map_add, map_mul, hσc₂]
      grind
    obtain ⟨z₁, hz₁L, hz₁⟩ := exists_mem_eichler_of_uTransLe hσ haa hw₀w₀ haw hLa hLw hL1 hc₁
    obtain ⟨z₂, hz₂L, hz₂⟩ := exists_mem_eichler_of_uTransLe hσ haa hw₀w₀ haw hLa hLw hLl hc₂
    obtain ⟨hz₁R, hz₁v⟩ := eichler_mem_uRad_radVec hσ haa hdd had hw₀ hz₁
    obtain ⟨hz₂R, hz₂v⟩ := eichler_mem_uRad_radVec hσ haa hdd had hw₀ hz₂
    refine ⟨z₁ * z₂, L.mul_mem hz₁L hz₂L, (uRad _ _).mul_mem hz₁R hz₂R, ?_⟩
    rw [radVec_mul_of_mem_uRad hσ haa hdd had hz₁R hz₂R, hz₁v, hz₂v, ← add_smul]
    congr 1
    rw [hc₁def]
    grind

theorem suFrameGen_succ (hF : Nat.card F = (2 ^ f) ^ 2) {n k : ℕ} (hn : 4 ≤ n)
    {p : Fin (n + 1)} (hp : Fin.rev p = p) (h : SUFrameGen (unitaryInvolution F 2 f) n k) :
    SUFrameGen (unitaryInvolution F 2 f) (n + 1) (k + 1) := by
  have hσ : ∀ c, unitaryInvolution F 2 f (unitaryInvolution F 2 f c) = c :=
    unitaryInvolution_involutive hF
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨U, hUlen, hUiso, hU⟩ := h
  obtain ⟨μ, hμ⟩ := exists_add_unitaryInvolution_eq hF (a := 1) (map_one _)
  have hτ : Function.Injective p.succAbove := Fin.succAbove_right_injective
  have hr : ∀ i, p.succAbove (Fin.rev i) = Fin.rev (p.succAbove i) := fun i => by
    rw [Fin.rev_succAbove, hp]
  have hrange : ∀ x, x ∉ Set.range p.succAbove → x = p := fun x hx => by
    rw [Fin.range_succAbove] at hx
    simpa using hx
  have hp_nmem : p ∉ Set.range p.succAbove := fun ⟨i, hi⟩ => Fin.succAbove_ne p i hi
  have h0l : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have h0p : (0 : Fin (n + 1)) ≠ p := by
    intro h0
    have h1 := hp
    rw [← h0, Fin.rev_zero] at h1
    exact h0l h1.symm
  have hlp : Fin.last n ≠ p := by
    intro hl
    have h1 := hp
    rw [← hl, Fin.rev_last] at h1
    exact h0l h1
  obtain ⟨e, hedef⟩ : ∃ e : Fin (n + 1) → F, e = Pi.single p 1 := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀def⟩ : ∃ x : Fin (n + 1) → F,
      x = Pi.single 0 1 + μ • Pi.single (Fin.last n) 1 := ⟨_, rfl⟩
  have hep : e p = 1 := by rw [hedef, Pi.single_eq_same]
  have hx₀p : x₀ p = 0 := by
    rw [hx₀def, Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne' h0p,
      Pi.single_eq_of_ne' hlp, smul_zero, add_zero]
  have he_x : ∀ x : Fin (n + 1) → F, uForm (unitaryInvolution F 2 f) e x = x p :=
    fun x => by rw [hedef, uForm_single_left, hp]
  have hx_e : ∀ x : Fin (n + 1) → F,
      uForm (unitaryInvolution F 2 f) x e = unitaryInvolution F 2 f (x p) :=
    fun x => by rw [hedef, uForm_single_right, hp]
  have hx₀x₀ : uForm (unitaryInvolution F 2 f) x₀ x₀ = 1 := by
    have h0r : (0 : Fin (n + 1)) ≠ Fin.rev 0 := by rw [Fin.rev_zero]; exact h0l
    have hlr : Fin.last n ≠ Fin.rev (Fin.last n) := by rw [Fin.rev_last]; exact h0l.symm
    rw [hx₀def]
    simp only [uForm_add_left, uForm_add_right, uForm_smul_left, uForm_smul_right,
      uForm_single_self h0r, uForm_single_self hlr, uForm_single_left, Fin.rev_zero,
      Fin.rev_last, Pi.single_eq_same, Pi.single_eq_of_ne h0l, Pi.single_eq_of_ne h0l.symm]
    grind
  obtain ⟨y, hydef⟩ : ∃ y : Fin (n + 1) → F, y = x₀ + e := ⟨_, rfl⟩
  have hyy : uForm (unitaryInvolution F 2 f) y y = 0 := by
    rw [hydef, uForm_add_left, uForm_add_right, uForm_add_right, hx₀x₀, hx_e, hx₀p, map_zero,
      he_x, he_x, hx₀p, hep]
    grind
  have hy0 : y ≠ 0 := by
    intro h0
    have := congrFun h0 p
    rw [hydef, Pi.add_apply, hx₀p, zero_add, hep] at this
    exact one_ne_zero this
  have hx₀ext : extByZero p.succAbove (x₀ ∘ p.succAbove) = x₀ :=
    extByZero_eq_of_apply hτ fun x hx => by rw [hrange x hx, hx₀p]
  refine ⟨y :: U.map (extByZero p.succAbove), ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_map]
    omega
  · intro u hu
    simp only [List.mem_cons, List.mem_map] at hu
    rcases hu with rfl | ⟨u', hu', rfl⟩
    · exact ⟨hy0, hyy⟩
    · exact ⟨extByZero_ne_zero hτ (hUiso u' hu').1, by rw [uForm_extByZero hτ hr, (hUiso u' hu').2]⟩
  · intro L hL
    have hLy : UTransLe L y := hL y (by simp)
    have hcomap := comap_eq_top_of_frame hσ hτ hr hU (L := L)
      (fun u hu => hL _ (List.mem_cons_of_mem _ (List.mem_map_of_mem hu)))
    have hall : ∀ v : Fin (n + 1) → F, uForm (unitaryInvolution F 2 f) v v = 0 →
        UTransLe L v := by
      intro v hvv
      by_cases hvp : v p = 0
      · have hvext : extByZero p.succAbove (v ∘ p.succAbove) = v :=
          extByZero_eq_of_apply hτ fun x hx => by rw [hrange x hx, hvp]
        rw [← hvext]
        refine uTransLe_extByZero_of_comap hσ hτ hr hcomap ?_
        rw [← uForm_extByZero hτ hr, hvext, hvv]
      · obtain ⟨v', hv'def⟩ : ∃ w : Fin (n + 1) → F, w = (v p)⁻¹ • v := ⟨_, rfl⟩
        have hv'p : v' p = 1 := by
          rw [hv'def, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hvp]
        have hv'v' : uForm (unitaryInvolution F 2 f) v' v' = 0 := by
          rw [hv'def, uForm_smul_left, uForm_smul_right, hvv, mul_zero, mul_zero]
        obtain ⟨x, hxdef⟩ : ∃ x : Fin (n + 1) → F, x = v' - e := ⟨_, rfl⟩
        have hxp : x p = 0 := by rw [hxdef, Pi.sub_apply, hv'p, hep, sub_self]
        have hv'eq : v' = x + e := by rw [hxdef, sub_add_cancel]
        have hxx : uForm (unitaryInvolution F 2 f) x x = 1 := by
          rw [hv'eq, uForm_add_left, uForm_add_right, uForm_add_right, hx_e, hxp, map_zero,
            he_x, he_x, hxp, hep] at hv'v'
          grind
        have hxext : extByZero p.succAbove (x ∘ p.succAbove) = x :=
          extByZero_eq_of_apply hτ fun x' hx' => by rw [hrange x' hx', hxp]
        have hu₀ : uForm (unitaryInvolution F 2 f) (x₀ ∘ p.succAbove) (x₀ ∘ p.succAbove) = 1 := by
          rw [← uForm_extByZero hτ hr, hx₀ext, hx₀x₀]
        have hu : uForm (unitaryInvolution F 2 f) (x ∘ p.succAbove) (x ∘ p.succAbove) = 1 := by
          rw [← uForm_extByZero hτ hr, hxext, hxx]
        obtain ⟨g, hg⟩ := exists_suMat_mulVec_eq_of_norm_one hF hn hu₀ hu
        have hgL : suEmbed (unitaryInvolution F 2 f) hτ hr g ∈ L := by
          have : g ∈ L.comap (suEmbed (unitaryInvolution F 2 f) hτ hr) := by
            rw [hcomap]; trivial
          exact this
        have hgy : suMat (unitaryInvolution F 2 f) (n + 1)
            (suEmbed (unitaryInvolution F 2 f) hτ hr g) *ᵥ y = v' := by
          rw [suMat_suEmbed_eq, hydef, mulVec_add, ← hx₀ext, extendMat_mulVec_extByZero, hg, hxext,
            hedef, extendMat_mulVec_single hτ _ hp_nmem, ← hedef, hv'eq]
        have hv' := uTransLe_conj hLy hgL
        rw [hgy, hv'def] at hv'
        exact uTransLe_of_smul hσ (inv_ne_zero hvp) hv'
    exact eq_top_of_forall_isUTransGroup_le hF (by omega)
      fun v X hvv hX => (uTransLe_iff hX).1 (hall v hvv)

end Steps

end CFSG.Timmesfeld.Transvection.ModelRank
