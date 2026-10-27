module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CellD7FullK
public import CFSG.LocalAnalysis.StandardType.GGQ2S08RestOut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TestLin

private lemma d7_pair_sum (v : Vn 8) (a b : Fin 7) :
    ((frameE 7 a + frameE 7 b) ⬝ᵥ v) • (frameE 7 a + frameE 7 b) +
      ((frameE 7 a - frameE 7 b) ⬝ᵥ v) • (frameE 7 a - frameE 7 b) =
        (2 * v a.castSucc) • frameE 7 a + (2 * v b.castSucc) • frameE 7 b := by
  rw [frameE_add_dot, frameE_sub_dot]
  funext m
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private lemma d7_sgnDiff_coord (v : Vn 8) {a b : Fin 7} (h : a ≠ b) :
    sgnDiff a b h v b.castSucc = v a.castSucc := by
  have hab : b.castSucc ≠ a.castSucc := fun h' => h (Fin.castSucc_injective _ h').symm
  change (v - ((frameE 7 a - frameE 7 b) ⬝ᵥ v) • (frameE 7 a - frameE 7 b)) b.castSucc = _
  rw [frameE_sub_dot]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, frameE_apply, if_neg hab, ↓reduceIte]
  ring

private lemma d7_three : ∀ i : Fin 7, ∃ j k : Fin 7, i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide

private lemma d7_frame_mem {P : Set (Vn 8)} (hsub : ∀ a ∈ P, ∀ b ∈ P, a - b ∈ P)
    (hadd : ∀ a ∈ P, ∀ b ∈ P, a + b ∈ P) {v : Vn 8}
    (hv : ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k), w v ∈ P)
    {i₀ : Fin 7} (hi₀ : v i₀.castSucc ≠ 0) (i : Fin 7) : frameE 7 i ∈ P := by
  obtain ⟨v', hv'i, hv'W⟩ : ∃ v' : Vn 8, v' i.castSucc ≠ 0 ∧
      ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k), w v' ∈ P := by
    by_cases hi : v i.castSucc = 0
    · have hne : i₀ ≠ i := fun h => hi₀ (h ▸ hi)
      refine ⟨sgnDiff i₀ i hne v, ?_, fun w hw => ?_⟩
      · rw [d7_sgnDiff_coord v hne]
        exact hi₀
      · have h := hv (w * sgnDiff i₀ i hne) (Subgroup.mul_mem _ hw (d7f_sgnDiff_mem i₀ i hne))
        rwa [LinearEquiv.mul_apply] at h
    · exact ⟨v, hi, hv⟩
  have hv'P : v' ∈ P := by
    simpa using hv'W 1 (Subgroup.one_mem _)
  have hY : ∀ (a b : Fin 7) (h : a ≠ b),
      (2 * v' a.castSucc) • frameE 7 a + (2 * v' b.castSucc) • frameE 7 b ∈ P := by
    intro a b h
    have h1 : v' - sgnSum a b h v' ∈ P := hsub _ hv'P _ (hv'W _ (d7f_sgnSum_mem a b h))
    have h2 : v' - sgnDiff a b h v' ∈ P := hsub _ hv'P _ (hv'W _ (d7f_sgnDiff_mem a b h))
    have e1 : v' - sgnSum a b h v' =
        ((frameE 7 a + frameE 7 b) ⬝ᵥ v') • (frameE 7 a + frameE 7 b) := by
      rw [sgnSum, refl_apply, sub_sub_cancel]
    have e2 : v' - sgnDiff a b h v' =
        ((frameE 7 a - frameE 7 b) ⬝ᵥ v') • (frameE 7 a - frameE 7 b) := by
      change v' - (v' - ((frameE 7 a - frameE 7 b) ⬝ᵥ v') • (frameE 7 a - frameE 7 b)) = _
      rw [sub_sub_cancel]
    rw [← d7_pair_sum, ← e1, ← e2]
    exact hadd _ h1 _ h2
  obtain ⟨j, k, hij, hik, hjk⟩ := d7_three i
  have hZ := hsub _ (hadd _ (hY i j hij) _ (hY i k hik)) _ (hY j k hjk)
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hZeq : (2 * v' i.castSucc) • frameE 7 i + (2 * v' j.castSucc) • frameE 7 j +
      ((2 * v' i.castSucc) • frameE 7 i + (2 * v' k.castSucc) • frameE 7 k) -
      ((2 * v' j.castSucc) • frameE 7 j + (2 * v' k.castSucc) • frameE 7 k) =
        v' i.castSucc • frameE 7 i := by
    funext m
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (v' i.castSucc * frameE 7 i m) * h3
  rw [hZeq] at hZ
  have hsmul : ∀ s : ZMod 3, ∀ w ∈ P, s • w ∈ P := by
    intro s w hw
    rcases (by decide : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2) s with rfl | rfl | rfl
    · rw [zero_smul, ← sub_self w]
      exact hsub _ hw _ hw
    · rwa [one_smul]
    · rw [two_smul]
      exact hadd _ hw _ hw
  have he : frameE 7 i = v' i.castSucc • (v' i.castSucc • frameE 7 i) := by
    rw [smul_smul, zmod3_sq_eq_one _ hv'i, one_smul]
  rw [he]
  exact hsmul _ _ hZ

theorem ggQ2s08_cellE_twD7 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08CellE .twD 7 .full := by
  intro G _ _ B Bs x L D J hS hI1 hCav M hShape labL hMark htag hrank hq hWeyl g φ hInd hRefl
    hMx hCen _
  have hK : GGQ2S08CellK .twD 7 .full := ggQ2s08_cellK_twD7 hLB hP hΓi hTBN
  have hW' : ∃ e : Fin 7 ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD 7).reindex e := by
    have key : ∀ m : ℕ, m = 7 → (∃ e : Fin m ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD m).reindex e) →
        ∃ e : Fin 7 ≃ M.Λ, M.coxeter = (ggCoxeterMatrixD 7).reindex e := by
      rintro m rfl h
      exact h
    exact key _ hrank (by simpa only [GGQ2LabelWeyl, htag] using hWeyl)
  obtain ⟨e, he⟩ := hW'
  obtain ⟨κ, hκx, hκs⟩ := ggQ2_fullCoords_D 7 (by norm_num) (by norm_num) M hShape.2.2.1 e
    (ggQ2_cartan_D e he M.isCartan)
  have hκx' : κ M.xV = xLast 7 := hκx
  have hW := ggQ2Cell_map_automizer_L M κ e (dFullS 7) hκs
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer {x} := (hcfg.1.2.2.2.2.2.2.1 : LargeEvenSStar 3 B x L).2.2.2.1.1
  obtain ⟨u, hu, hnE⟩ : ∃ u ∈ ggAutomizer L Bs, ¬ GGQ2EForm Bs J (u * φ * u⁻¹) := by
    by_contra hall
    push Not at hall
    obtain ⟨b₀, hb₀⟩ := hCen
    set c : ↥Bs := b₀⁻¹ * φ b₀ with hc
    have huc : ∀ u ∈ ggAutomizer L Bs, ((u c : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G) := by
      intro u hu
      have h := (hall u hu).1 (u b₀)
      have hval : (u b₀)⁻¹ * (u * φ * u⁻¹) (u b₀) = u c := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, map_mul, map_inv]
      rwa [hval] at h
    let Φ : Vn 8 → ↥Bs := fun v => Additive.toMul (M.model.symm (κ.symm v))
    let P : Set (Vn 8) := {v | ((Φ v : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G)}
    have hΦadd : ∀ a b, Φ (a + b) = Φ a * Φ b := fun a b => by
      simp only [Φ, map_add, toMul_add]
    have hΦsub : ∀ a b, Φ (a - b) = Φ a * (Φ b)⁻¹ := fun a b => by
      simp only [Φ, map_sub, toMul_sub, div_eq_mul_inv]
    have hsub : ∀ a ∈ P, ∀ b ∈ P, a - b ∈ P := fun a ha b hb => by
      show ((Φ (a - b) : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G)
      rw [hΦsub, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hb)
    have hadd : ∀ a ∈ P, ∀ b ∈ P, a + b ∈ P := fun a ha b hb => by
      show ((Φ (a + b) : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G)
      rw [hΦadd, Subgroup.coe_mul]
      exact Subgroup.mul_mem _ ha hb
    have hΦκ : ∀ b : ↥Bs, Φ (κ (M.model (Additive.ofMul b))) = b := fun b => by
      simp only [Φ, LinearEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, toMul_ofMul]
    set vc : Vn 8 := κ (M.model (Additive.ofMul c)) with hvc
    have hvW : ∀ w ∈ Subgroup.closure (Set.range fun k : Fin 7 => dFullS 7 k), w vc ∈ P := by
      intro w hw
      rw [← hW] at hw
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
      show ((Φ (ggQ2CellLin M κ u vc) : ↥Bs) : G) ∈ Subgroup.centralizer (J : Set G)
      rw [hvc, ggQ2CellLin_apply, LinearEquiv.symm_apply_apply, ggLin_apply_ofMul (p := 3), hΦκ]
      exact huc u hu
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin 7, vc i₀.castSucc ≠ 0 := by
      by_contra hzero
      push Not at hzero
      apply hb₀
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ZMod 3) = vc (Fin.last 7) := ⟨_, ZMod.natCast_zmod_val _⟩
      have hvx : vc = (n : ZMod 3) • κ M.xV := by
        rw [hn, hκx']
        funext m
        induction m using Fin.lastCases with
        | last => rw [Pi.smul_apply, smul_eq_mul, xLast_apply, if_pos rfl, mul_one]
        | cast i =>
            rw [hzero i, Pi.smul_apply, smul_eq_mul, xLast_apply, if_neg (Fin.castSucc_ne_last i),
              mul_zero]
      have hcx : c = ⟨x, M.hx⟩ ^ n := by
        have h1 : κ (M.model (Additive.ofMul c)) =
            κ (M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ n))) := by
          rw [← hvc, hvx, ofMul_pow, map_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul,
            GGQ2LDatum.xV]
        exact Additive.ofMul.injective (M.model.injective (κ.injective h1))
      change ((c : ↥Bs) : G) ∈ D
      rw [hcx, Subgroup.coe_pow]
      exact Subgroup.pow_mem _ hxD _
    have hframe := d7_frame_mem hsub hadd hvW hi₀
    have h0P : (0 : Vn 8) ∈ P := by
      have := hsub _ (hframe 0) _ (hframe 0)
      rwa [sub_self] at this
    let F : (Fin 7 → ZMod 3) → Vn 8 := fun f => ∑ i, f i • frameE 7 i
    have hFP : ∀ f, F f ∈ P := by
      intro f
      refine Finset.sum_induction _ (· ∈ P) (fun a b ha hb => hadd _ ha _ hb) h0P fun i _ => ?_
      rcases (by decide : ∀ s : ZMod 3, s = 0 ∨ s = 1 ∨ s = 2) (f i) with h | h | h
      · rw [h, zero_smul]
        exact h0P
      · rw [h, one_smul]
        exact hframe i
      · rw [h, two_smul]
        exact hadd _ (hframe i) _ (hframe i)
    have hFcoord : ∀ f (i : Fin 7), F f i.castSucc = f i := by
      intro f i
      simp only [F, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, frameE_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        rw [if_neg (fun h => hji (Fin.castSucc_injective _ h).symm), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hinj : Function.Injective (fun f : Fin 7 → ZMod 3 =>
        (⟨((Φ (F f) : ↥Bs) : G), (Φ (F f)).2, hFP f⟩ : ↥(Bs ⊓ Subgroup.centralizer (J : Set G)))) := by
      intro f f' h
      have h1 : Φ (F f) = Φ (F f') := Subtype.ext (by simpa using congrArg Subtype.val h)
      have h2 : F f = F f' := by
        have := congrArg (fun b => κ (M.model (Additive.ofMul b))) h1
        simpa [Φ] using this
      funext i
      rw [← hFcoord f i, ← hFcoord f' i, h2]
    have hcard := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
    have hle := ggQ2_card_bstar_centralizer_le hS
    omega
  obtain ⟨l, hlL, hlN, hul⟩ := mem_ggAutomizer_iff.mp hu
  have hui := inv_apply_of_forall hul
  have hInd' : GGQ2Ind Bs (l * g * l⁻¹) (u * φ * u⁻¹) := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hInd.1) (Subgroup.inv_mem _ hlN),
      fun b => ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hul, hInd.2, hui]
    group
  have hRefl' : GGIsReflection 3 (u * φ * u⁻¹) := hRefl.conj' u
  have hMx' : GGQ2MovesX Bs x (u * φ * u⁻¹) := by
    obtain ⟨b₁, hb₁x, hb₁⟩ := hMx
    have hufix : u⁻¹ b₁ = b₁ := by
      apply Subtype.ext
      rw [hui, hb₁x]
      have := Subgroup.mem_centralizer_iff.mp (hLx hlL) x (Set.mem_singleton x)
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    refine ⟨b₁, hb₁x, fun h => hb₁ ?_⟩
    rw [MulAut.mul_apply, MulAut.mul_apply, hufix] at h
    have := congrArg (u⁻¹ : MulAut ↥Bs) h
    rwa [MulAut.inv_apply_self, hufix] at this
  have hkey : l * g * l⁻¹ ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    by_cases hC' : GGQ2CentreNotIn Bs D (u * φ * u⁻¹)
    · by_cases hRK : ∃ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K ∧
          (∀ c : ↥Bs, (c : G) = y → (u * φ * u⁻¹) c = c) ∧
          (¬ ∃ k ∈ K, GGQ2Ind Bs k (u * φ * u⁻¹)) ∧
          ¬ ∃ k ∈ K, k ∈ Subgroup.normalizer (Bs : Set G) ∧
            k * x * k⁻¹ = (l * g * l⁻¹) * x * (l * g * l⁻¹)⁻¹
      · obtain ⟨y, K, hnb, hfix, hnI, hnA⟩ := hRK
        exact hK hS hI1 hCav M hShape hMark htag hrank hq hWeyl _ _ hInd' hRefl' hMx' hC' hnE
          y K hnb hfix hnI hnA
      · exact ggQ2s08_reflRestOut_holds hLB hP hΓi hS rfl hI1 hCav _ _ hInd' hRefl' hMx' hC'
          ⟨hnE, hRK⟩
    · exact ggQ2n_reflCentre hLB hP hS.1 rfl hCav _ _ hInd' hC'
  have hlG : l ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    Subgroup.le_normalizer (le_ggG0_left 3 B x L D J hlL)
  have hg : g = l⁻¹ * (l * g * l⁻¹) * l := by group
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hlG) hkey) hlG

theorem ggQ2s08_cell_twD7 (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hΓi : GGQ2GammaXOffI1Input) (hTBN : GGQ2TableBNbr) : GGQ2S08CellEK .twD 7 .full :=
  GGQ2S08CellEK.of_halves (ggQ2s08_cellE_twD7 hLB hP hΓi hTBN) (ggQ2s08_cellK_twD7 hLB hP hΓi hTBN)

end CFSG.StandardType

end
