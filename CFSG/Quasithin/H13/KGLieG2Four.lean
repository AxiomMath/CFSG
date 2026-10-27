module

public import CFSG.Quasithin.H13.KGLieSL3Four
public import CFSG.Quasithin.Vol2.Ch11G2Q8RootLine

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_g2_four (hV2 : ∀ w : V, w ^ 2 = 1) {G L : Subgroup (MulAut V)}
    {v : MulAut V} (hB4 : B4Hyp G L) (hc : A5.Cond1321 G L v) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (hr : (FFModel.zornQ (quasithinG2 K)).Realizes L ⊤ ⊥) : False := by
  classical
  have : CharP K 2 := charP_two_of_card_four hK
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨ω, hω⟩ := exists_omega hK
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω
  have hω1 : ω ≠ 1 := by
    rintro rfl
    have h1 : (1 : K) = 0 := by linear_combination hω - h2
    exact one_ne_zero h1
  have hd : ⁅quasithinG2 K, quasithinG2 K⁆ = quasithinG2 K := by
    rw [g2Derived_eq hω0 hω1, CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup]
  rw [← hd] at hr
  obtain ⟨π, hπ⟩ := hr
  obtain ⟨f, hf⟩ := CFSG.Quasithin.Vol2.KGNat.exists_isCoord (lmG K) hπ
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 := (hf.eq_iff a b).1 hab
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at h1
  have hvN : v ∈ normalizer (L : Set (MulAut V)) := by
    rw [hB4.2.1]
    exact le_normalizer_quasithinGenFitting G hc.mem
  have hτH : ∀ h ∈ L, v * h * v⁻¹ ∈ L := fun h hh => (mem_normalizer_iff.1 hvN h).1 hh
  have hτH' : ∀ h ∈ L, v⁻¹ * h * v ∈ L := fun h hh => by
    have := (mem_normalizer_iff.1 (Subgroup.inv_mem _ hvN) h).1 hh
    simpa using this
  have hK' : Nat.card K = 2 ^ 2 := by rw [hK]; norm_num
  obtain ⟨c, γ, σ, hc0, hcγ⟩ := exists_smul_frob_of_normalizes hf hω0 hω1 hK' le_rfl v
    (fun z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one])
    (fun z hz => by rw [Subgroup.mem_bot] at hz ⊢; rw [hz, map_one]) hτH hτH'
  have hcardQ : Nat.card (Ix3 → K) = 4 ^ 6 := by
    rw [Nat.card_fun, hK]
    simp
  have hcardV : Nat.card V = 4 ^ 6 := by
    rw [← hcardQ]
    exact Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hf.surj⟩)
  have hrk : (commHom v).ker.index ≤ 4 := by
    rw [← fixV_zpowers_eq_ker]
    exact index_le_four_of_rkIdx hV2 hc.rank
  have hfixV : 4 ^ 5 ≤ Nat.card (commHom v).ker := by
    have h1 := (commHom v).ker.card_mul_index
    rw [hcardV] at h1
    have h3 : 4 ^ 6 ≤ Nat.card (commHom v).ker * 4 := h1 ▸ Nat.mul_le_mul_left _ hrk
    omega
  have hσ : ∀ θ, σ θ = θ := by
    by_contra hσ
    obtain ⟨θ, hθ⟩ := not_forall.mp hσ
    let Te : (Ix3 → K) →+ (Ix3 → K) :=
      { toFun := fun x => c • g2Act γ (frobQ σ x)
        map_zero' := by
          rw [show frobQ (σ : K →+* K) 0 = 0 from funext fun j => map_zero σ, map_zero,
            smul_zero]
        map_add' := fun x y => by
          rw [show frobQ (σ : K →+* K) (x + y) = frobQ σ x + frobQ σ y from
            funext fun j => map_add σ (x j) (y j), map_add, smul_add] }
    have hTe : ∀ (a : K) (x : Ix3 → K), Te (a • x) = (σ : K →+* K) a • Te x := by
      intro a x
      show c • g2Act γ (frobQ σ (a • x)) = (σ : K →+* K) a • (c • g2Act γ (frobQ σ x))
      rw [frobQ_smul, CFSG.Quasithin.Vol2.Ch11.G2Q8.g2Act_smul, smul_comm]
    have h1 := card_fix_sq_le Te (σ : K →+* K) hθ hTe
    have h3 : Nat.card (commHom v).ker ≤ Nat.card {x : Ix3 → K // Te x = x} := by
      refine Nat.card_le_card_of_injective (fun w => ⟨f w.1, ?_⟩) ?_
      · show c • g2Act γ (frobQ σ (f w.1)) = f w.1
        rw [← hcγ, mem_ker_commHom.1 w.2]
      · intro w w' h
        exact Subtype.ext (hfinj (congrArg Subtype.val h))
    rw [hcardQ] at h1
    have h4 := Nat.pow_le_pow_left (hfixV.trans h3) 2
    have h5 := h4.trans h1
    norm_num at h5
  have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => funext fun j => hσ (x j)
  have hcγ' : ∀ w, f (v w) = c • g2Act γ (f w) := fun w => by rw [hcγ, hfrob]
  have hvv : ∀ w : V, v (v w) = w := by
    intro w
    have := congrArg (fun g : MulAut V => g w) hc.sq
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  have hsq : ∀ x, g2Act (γ * γ) x = (c * c)⁻¹ • x := by
    intro x
    obtain ⟨w, rfl⟩ := hf.surj x
    have h1 := congrArg f (hvv w)
    rw [hcγ', hcγ', CFSG.Quasithin.Vol2.Ch11.G2Q8.g2Act_smul, smul_smul] at h1
    rw [g2Act_mul_apply]
    conv_rhs => rw [← h1]
    rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc0 hc0), one_smul]
  have hcc : (c * c)⁻¹ = 1 := scalar_eq_one hsq
  have hc1 : c = 1 := by
    have h3 : c * c = 1 := by rw [← inv_inv (c * c), hcc, inv_one]
    have h4 : (c - 1) ^ 2 = 0 := by linear_combination h3 + (1 - c) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
  have hγγ : γ * γ = 1 := cayley_eq_one fun x => by rw [hsq, hcc, one_smul]
  have hvγ : ∀ w, f (v w) = g2Act γ (f w) := fun w => by rw [hcγ', hc1, one_smul]
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    apply hc.ne_one
    ext w
    apply hfinj
    rw [hvγ, map_one]
    rfl
  have hfix5 : 4 ^ 5 ≤ Nat.card (fixQ γ) := by
    refine hfixV.trans (Nat.card_le_card_of_injective (fun w => ⟨f w.1, ?_⟩) ?_)
    · rw [mem_fixQ, ← hvγ, mem_ker_commHom.1 w.2]
    · intro w w' h
      exact Subtype.ext (hfinj (congrArg Subtype.val h))
  have hfix4 : Nat.card K ^ 4 ≤ Nat.card (fixQ γ) := by
    rw [hK]
    exact le_trans (by norm_num) hfix5
  obtain ⟨x, hx⟩ := eq_conj_tL_of_fix hγγ hγ1 hfix4
  have hle : Nat.card (fixQ γ) ≤ Nat.card (Fin 4 → K) := by
    refine Nat.card_le_card_of_injective (fun y => ![(g2Act x⁻¹ y.1) (.inl 0),
      (g2Act x⁻¹ y.1) (.inl 1), (g2Act x⁻¹ y.1) (.inr 1), (g2Act x⁻¹ y.1) (.inr 2)]) ?_
    intro y y' h
    have hy : InC (g2Act x⁻¹ y.1) := by
      rw [← mem_fixQ_conj_tL, ← hx]
      exact y.2
    have hy' : InC (g2Act x⁻¹ y'.1) := by
      rw [← mem_fixQ_conj_tL, ← hx]
      exact y'.2
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2' := congrFun h 2
    have h3 := congrFun h 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at h0 h1 h2' h3
    have hz : g2Act x⁻¹ y.1 = g2Act x⁻¹ y'.1 := by
      funext k
      rcases k with k | k <;> fin_cases k
      · exact h0
      · exact h1
      · exact hy.1.trans hy'.1.symm
      · exact hy.2.trans hy'.2.symm
      · exact h2'
      · exact h3
    apply Subtype.ext
    rw [← g2Act_apply_inv x y.1, hz, g2Act_apply_inv]
  rw [Nat.card_fun, hK, Nat.card_fin] at hle
  have := hfix5.trans hle
  norm_num at this

theorem factLieG2FourRow1321_holds : A5.FactLieG2FourRow1321 := by
  intro V _ _ hV2 G L v hB4 hc h
  obtain ⟨K, _, _, hK, hr⟩ := h
  exact false_of_g2_four hV2 hB4 hc (by rw [hK]; norm_num) hr

end CFSG.Quasithin.H13.KGLie
