module

public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3PlusInn

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement MatrixGroups

namespace Item211Lie3Proof

open Item211Lie2Proof

structure SL2Like (L : Type*) [Group L] (z₀ : L) : Prop where
  gen : ∀ N : Subgroup L, (∀ A : L, A ^ 3 = 1 → A ∈ N) → z₀ ∈ N → N = ⊤
  norm : ∀ N : Subgroup L, N.Normal → (∀ a ∈ N, ∃ e : ℕ, a ^ 2 ^ e = 1) →
    ∀ a ∈ N, a = 1 ∨ a = z₀
  perf : Group.IsPerfect L

theorem SL2Like.of_mulEquiv {L L' : Type*} [Group L] [Group L'] {z₀ : L} (e : L ≃* L')
    (h : SL2Like L z₀) : SL2Like L' (e z₀) where
  gen N h3 hz := by
    have htop := h.gen (N.comap (e : L →* L')) (fun A hA => h3 _ (by rw [← map_pow, hA, map_one]))
      hz
    rw [eq_top_iff]
    intro a _
    have ha : e.symm a ∈ N.comap (e : L →* L') := by rw [htop]; exact Subgroup.mem_top _
    simpa using ha
  norm N hN h2 a ha := by
    have hN' : (N.comap (e : L →* L')).Normal := Subgroup.Normal.comap hN _
    have h2' : ∀ b ∈ N.comap (e : L →* L'), ∃ k : ℕ, b ^ 2 ^ k = 1 := by
      intro b hb
      obtain ⟨k, hk⟩ := h2 _ hb
      exact ⟨k, e.injective (by rw [map_pow, map_one]; exact hk)⟩
    have hb : e.symm a ∈ N.comap (e : L →* L') := by
      change e (e.symm a) ∈ N
      rw [MulEquiv.apply_symm_apply]
      exact ha
    rcases h.norm _ hN' h2' _ hb with h1 | h1
    · left
      rw [← e.apply_symm_apply a, h1, map_one]
    · right
      rw [← e.apply_symm_apply a, h1]
  perf := by
    have := h.perf
    exact Group.IsPerfect.ofSurjective (f := (e : L →* L')) e.surjective

theorem sl2Like_specialLinear {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    SL2Like SL(2, F) (-1) where
  gen N h3 hz := eq_top_of_three hF N h3 fun A hA => by
    rcases eq_one_or_eq_neg_one_of_mem_center hA with rfl | rfl
    · exact N.one_mem
    · exact hz
  norm N hN h2 a ha := eq_one_or_eq_neg_one_of_mem_center (le_center_of_normal_two hF N h2 ha)
  perf := CFSG.LinearGroups.special_linear_dimension_two_perfect
    (CFSG.LinearGroups.exists_finset_card_eq_four hF)

theorem eq_bot_of_sl2Like {X L : Type*} [Group X] [Group L]
    (hinj : Function.Injective (MulAut.conj : X →* MulAut X))
    {D T V W : Subgroup (MulAut X)} [Finite D] [Finite V] (hDodd : Odd (Nat.card D))
    (hTD : T ≤ Subgroup.centralizer (D : Set (MulAut X)))
    (hVi : V ≤ (MulAut.conj : X →* MulAut X).range) (hV2 : IsPGroup 2 V)
    (hDV : D ≤ Subgroup.normalizer (V : Set (MulAut X))) (hVD : ⁅V, D⁆ = V)
    (hW2 : IsPGroup 2 W) (hVW : V ≤ W)
    (hWT : W ≤ Subgroup.centralizer (T : Set (MulAut X)))
    (hτ : ∀ τ ∈ (MulAut.conj : X →* MulAut X).range ⊓ Subgroup.centralizer (T : Set (MulAut X)),
      τ ^ 3 = 1 → τ ∈ Subgroup.normalizer (W : Set (MulAut X)))
    {x : X} (hxT : MulAut.conj x ∈ T) (ι : L →* X) (hιinj : Function.Injective ι)
    (hιT : ∀ A, MulAut.conj (ι A) ∈ Subgroup.centralizer (T : Set (MulAut X)))
    {z₀ : L} (hz₀ : ι z₀ = x) (hL : SL2Like L z₀)
    (hcomm : ∀ w : X, MulAut.conj w ∈ W → ∀ A : L, ∃ A' : L, ι A' = w * ι A * w⁻¹ * (ι A)⁻¹)
    (hcent : ∀ y y' : X, (∀ A, y * ι A = ι A * y) → (∀ A, y' * ι A = ι A * y') →
      y * y' = y' * y)
    (hinv : ∀ y : X, (∀ A, y * ι A = ι A * y) → y ^ 2 = 1 → y = 1 ∨ y = x) :
    V = ⊥ := by
  classical
  have hxι : ∀ A, x * ι A = ι A * x := fun A => hinj (by
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp (hιT A) _ hxT)
  have hNW : ∀ A : L, MulAut.conj (ι A) ∈ Subgroup.normalizer (W : Set (MulAut X)) := by
    have htop := hL.gen ((Subgroup.normalizer (W : Set (MulAut X))).comap
        ((MulAut.conj : X →* MulAut X).comp ι))
      (fun A hA => hτ _ (Subgroup.mem_inf.mpr ⟨⟨ι A, rfl⟩, hιT A⟩)
        (by rw [← map_pow, hA, map_one]))
      (by
        rw [Subgroup.mem_comap, MonoidHom.comp_apply, hz₀]
        exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun w hw =>
          (Subgroup.mem_centralizer_iff.mp (hWT hw) _ hxT).symm))
    intro A
    have hA : A ∈ (Subgroup.normalizer (W : Set (MulAut X))).comap
        ((MulAut.conj : X →* MulAut X).comp ι) := by
      rw [htop]
      exact Subgroup.mem_top A
    exact hA
  set 𝒲 := W.comap ((MulAut.conj : X →* MulAut X).comp ι) with h𝒲
  have h𝒲n : 𝒲.Normal := ⟨fun B hB A => by
    show MulAut.conj (ι (A * B * A⁻¹)) ∈ W
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hNW A) _).mp hB⟩
  have h𝒲2 : ∀ a ∈ 𝒲, ∃ e : ℕ, a ^ 2 ^ e = 1 := by
    intro a ha
    obtain ⟨e, he⟩ := hW2 ⟨_, ha⟩
    refine ⟨e, hιinj (hinj ?_)⟩
    rw [map_pow, map_pow, map_one, map_one]
    simpa using congrArg Subtype.val he
  have h𝒲v := hL.norm 𝒲 h𝒲n h𝒲2
  have hWι : ∀ w : X, MulAut.conj w ∈ W → ∀ A, w * ι A = ι A * w := by
    intro w hw
    have hval : ∀ A : L, w * ι A * w⁻¹ * (ι A)⁻¹ = 1 ∨ w * ι A * w⁻¹ * (ι A)⁻¹ = x := by
      intro A
      obtain ⟨A', hA'⟩ := hcomm w hw A
      have hA'W : A' ∈ 𝒲 := by
        show MulAut.conj (ι A') ∈ W
        rw [hA', map_mul, map_mul, map_mul, map_inv, map_inv]
        have h1 : MulAut.conj (ι A) * (MulAut.conj w)⁻¹ * (MulAut.conj (ι A))⁻¹ ∈ W :=
          (Subgroup.mem_normalizer_iff.mp (hNW A) _).mp (W.inv_mem hw)
        have h2 := W.mul_mem hw h1
        simpa only [mul_assoc] using h2
      rcases h𝒲v A' hA'W with h | h
      · left
        rw [← hA', h, map_one]
      · right
        rw [← hA', h, hz₀]
    have hcomm_val : ∀ A B : L, (w * ι A * w⁻¹ * (ι A)⁻¹) * (w * ι B * w⁻¹ * (ι B)⁻¹) =
        (w * ι B * w⁻¹ * (ι B)⁻¹) * (w * ι A * w⁻¹ * (ι A)⁻¹) := by
      intro A B
      rcases hval A with h | h <;> rcases hval B with h' | h' <;> rw [h, h'] <;> simp
    let φ : L →* X :=
      { toFun := fun A => w * ι A * w⁻¹ * (ι A)⁻¹
        map_one' := by simp
        map_mul' := fun A B => by
          have hcB : (w * ι B * w⁻¹ * (ι B)⁻¹) * (ι A)⁻¹ =
              (ι A)⁻¹ * (w * ι B * w⁻¹ * (ι B)⁻¹) := by
            rcases hval B with h | h <;> rw [h]
            · simp
            · rw [← map_inv]
              exact hxι A⁻¹
          calc w * ι (A * B) * w⁻¹ * (ι (A * B))⁻¹
              = w * ι A * w⁻¹ * ((w * ι B * w⁻¹ * (ι B)⁻¹) * (ι A)⁻¹) := by
                rw [map_mul]; group
            _ = w * ι A * w⁻¹ * ((ι A)⁻¹ * (w * ι B * w⁻¹ * (ι B)⁻¹)) := by rw [hcB]
            _ = (w * ι A * w⁻¹ * (ι A)⁻¹) * (w * ι B * w⁻¹ * (ι B)⁻¹) := by group }
    have hφ1 : ∀ A : L, φ A = 1 := by
      have := hL.perf
      have hle : commutator L ≤ φ.ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm_val a b
      intro A
      exact hle (by rw [Group.IsPerfect.commutator_eq_top]; exact Subgroup.mem_top A)
    intro A
    have h1 : w * ι A * w⁻¹ * (ι A)⁻¹ = 1 := hφ1 A
    calc w * ι A = (w * ι A * w⁻¹ * (ι A)⁻¹) * (ι A * w) := by group
      _ = ι A * w := by rw [h1, one_mul]
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    obtain ⟨y, rfl⟩ := hVi ha
    obtain ⟨y', rfl⟩ := hVi hb
    rw [← map_mul, ← map_mul, hcent y y' (hWι y (hVW ha)) (hWι y' (hVW hb))]
  refine eq_bot_of_comm_of_fixed hVc hDodd hV2 hDV hVD fun v hv hv2 d hd => ?_
  obtain ⟨y, rfl⟩ := hVi hv
  have hy2 : y ^ 2 = 1 := hinj (by rw [map_pow, hv2, map_one])
  rcases hinv y (hWι y (hVW hv)) hy2 with rfl | rfl
  · rw [map_one, one_mul, mul_one]
  · exact Subgroup.mem_centralizer_iff.mp (hTD hxT) d hd

end Item211Lie3Proof

end CFSG.RankThree.PartTwo.Sec21
