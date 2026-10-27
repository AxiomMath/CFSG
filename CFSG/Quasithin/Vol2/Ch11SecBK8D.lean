module

public import CFSG.Quasithin.Vol2.Ch11SecBK8A
public import CFSG.Quasithin.Vol2.Ch11SecBK8B
public import CFSG.Quasithin.Vol2.Ch11SecBK8C

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank K8
open scoped Matrix

theorem factVMRootInv_holds : FactVMRootInv := by
  intro G _ _ L V W X T V₁ V₂ n h x hx hx2 hxW hm
  obtain ⟨K, _, _, _, hK, Φ, a, b, hL, hX, hab, hV, S₁, S₂, hd₁, -, hS₁, -⟩ := exists_model36 h
  have hxN : x ∈ Subgroup.normalizer (W : Set G) := hx.2
  have hyN : hat Φ x hxN ∈ normD K := hat_mem_normD Φ hL hxN (h.normalizer_le_W hx)
  have hsq : hat Φ x hxN ^ 2 = 1 := by
    rw [← hat_pow Φ hxN 2 (Subgroup.pow_mem _ hxN 2), hat_eq_one_iff]
    exact hx2
  have hfix : Nat.card (FixW (hat Φ x hxN)) = Nat.card K ^ 4 := by
    rw [card_fix_hat]
    have h1 := two_pow_mQuot_mul_card Φ hK
      (inf_le_left : W ⊓ Subgroup.centralizer ({x} : Set G) ≤ W)
    rw [hm, show 6 * n = 2 * n + 4 * n by ring, pow_add] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1, hK, ← pow_mul, mul_comm]
  obtain ⟨g, -, -, hgy, -, -, -, -, hd⟩ := trv_of_card_fix hyN hsq hfix
  obtain ⟨hv, hvmem, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun hb : fixSub g = ⊥ => by rw [hb, finrank_bot] at hd; omega)
  obtain ⟨u₁, hu₁, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fun hb : S₁ = ⊥ => by rw [hb, finrank_bot] at hd₁; omega)
  obtain ⟨γ, hγ, hγv⟩ := exists_sl_mulVec hv0 hu₁0
  have hmem : matAut (dgHom γ) ∈ (autI h.elemW L).map (congrHom Φ) := by
    rw [hL]
    exact matAut_dgHom_mem_diagSL hγ
  obtain ⟨l, hlN, hlL, hle⟩ := (mem_map_autI Φ).mp hmem
  refine ⟨l, hlL, fun z hz => ?_⟩
  rw [mem_conjSubgroup_iff] at hz
  have hzW : z ∈ W := by
    have h1 : l * z * l⁻¹ ∈ W := h.le_W (h.le₁₂.trans h.le₂ hz)
    exact (Subgroup.mem_normalizer_iff.mp hlN z).mpr h1
  obtain ⟨v, rfl⟩ := exists_psi_eq Φ hzW
  have h3 : matAut (dgHom γ) v ∈ V₁.comap (psi Φ) := by
    change psi Φ (matAut (dgHom γ) v) ∈ V₁
    rw [← hle, psi_hat]
    exact hz
  rw [hS₁] at h3
  obtain ⟨s, hs, hse⟩ := mem_natSubOf.mp h3
  obtain ⟨κ, hκ⟩ := (finrank_eq_one_iff_of_nonzero' (⟨u₁, hu₁⟩ : ↥S₁)
    (fun h0 => hu₁0 (congrArg Subtype.val h0))).mp hd₁ ⟨s, hs⟩
  have hκs : κ • u₁ = s := congrArg Subtype.val hκ
  have hv' : v = natEmb a b (Multiplicative.ofAdd (κ • hv)) := by
    apply (matAut (dgHom γ)).injective
    rw [matAut_dgHom_natEmb, ← hse, ← hκs, ← hγv]
    congr 1
    apply Multiplicative.toAdd.injective
    change κ • ((γ : Matrix (Fin 3) (Fin 3) K) *ᵥ hv) = (γ : Matrix (Fin 3) (Fin 3) K) *ᵥ (κ • hv)
    rw [Matrix.mulVec_smul]
  have hfixv : hat Φ x hxN v = v := by
    rw [hgy, hv', matAut_dgHom_natEmb]
    congr 1
    apply Multiplicative.toAdd.injective
    change (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (κ • hv) = κ • hv
    rw [Matrix.mulVec_smul, mem_fixSub.mp hvmem]
  refine ⟨psi_mem Φ v, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h4 := psi_hat Φ hxN v
  rw [hfixv] at h4
  calc psi Φ v * x = x * psi Φ v * x⁻¹ * x := by rw [← h4]
    _ = x * psi Φ v := by group

theorem K8.eq_of_sqSub_eq {K : Type} [Field K] {S S' : Submodule K (Fin 3 → K)}
    (h : sqSub S = sqSub S') : S = S' := by
  ext u
  have key : ∀ S₀ : Submodule K (Fin 3 → K),
      u ∈ S₀ ↔ Multiplicative.ofAdd (Sum.elim u (0 : Fin 3 → K)) ∈ sqSub S₀ := fun S₀ =>
    ⟨fun hu => ⟨hu, S₀.zero_mem⟩, fun hu => hu.1⟩
  rw [key S, key S', h]

theorem K8.comm_natEmb_trvW {K : Type} [Field K] {f : (Fin 3 → K) →ₗ[K] K} {w : Fin 3 → K}
    {y : MulAut (W6 K)} (hy : ∀ v, toAddMap y v = trvW f w v) (a b : K) (u : Fin 3 → K) :
    y (natEmb a b (Multiplicative.ofAdd u)) * (natEmb a b (Multiplicative.ofAdd u))⁻¹ =
      natEmb a b (Multiplicative.ofAdd (f u • w)) := by
  rw [trvW_natEmb hy, toAdd_ofAdd, ofAdd_add, map_mul, mul_inv_cancel_comm]

theorem factVMRootElt_holds : FactVMRootElt := by
  intro G _ _ L V W X T V₁ V₂ n h E hE hEe P hPW hmP hcomm
  obtain ⟨K, _, _, _, hK, Φ, a, b, hL, hX, hab, hV, -, -, -, -, -, -⟩ := exists_model36 h
  have hEN : E ≤ Subgroup.normalizer (W : Set G) := hE.trans inf_le_right
  by_cases hEC : E ≤ Subgroup.centralizer (W : Set G)
  · left
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEC he) v (h.le_W hv)).symm
  right
  obtain ⟨e₀, he₀E, he₀⟩ : ∃ e ∈ E, e ∉ Subgroup.centralizer (W : Set G) := by
    by_contra hc
    push Not at hc
    exact hEC hc
  have hPc : Nat.card ↥(P.comap (psi Φ)) = Nat.card K ^ 2 := by
    rw [card_comap_psi Φ hPW]
    have h1 := E3.relIndex_eq_two_pow (isPGroup_of_le h.elemW hPW) ⊥
    rw [Subgroup.relIndex_bot_left, hmP] at h1
    rw [h1, hK, ← pow_mul, mul_comm]
  have hstr : ∀ e (he : e ∈ E), e ∉ Subgroup.centralizer (W : Set G) → ∃ w ψ : Fin 3 → K,
      ψ ≠ 0 ∧ dotL ψ w = 0 ∧ (∀ v, toAddMap (hat Φ e (hEN he)) v = trvW (dotL ψ) w v) ∧
        sqSub (K ∙ w) = P.comap (psi Φ) := by
    intro e he heW
    have hyN : hat Φ e (hEN he) ∈ normD K := hat_mem_normD Φ hL (hEN he) (h.normalizer_le_W
      ⟨hE he |>.1, hEN he⟩)
    have hsq : hat Φ e (hEN he) ^ 2 = 1 := by
      rw [← hat_pow Φ (hEN he) 2 (Subgroup.pow_mem _ (hEN he) 2), hat_eq_one_iff, hEe.2 e he]
      exact Subgroup.one_mem _
    have hc1 : commSub ⊤ (Subgroup.zpowers (hat Φ e (hEN he))) = P.comap (psi Φ) := by
      rw [← hcomm e he heW, commutator_zpowers_eq Φ (hEN he),
        Subgroup.comap_map_eq_self_of_injective (psi_injective Φ)]
    have hfix : Nat.card (FixW (hat Φ e (hEN he))) = Nat.card K ^ 4 := by
      have h1 := card_commSub_mul_card_fix (hat Φ e (hEN he))
      rw [hc1, hPc, card_stdMod, card_I6,
        show Nat.card K ^ 6 = Nat.card K ^ 2 * Nat.card K ^ 4 by ring] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 2) h1
    obtain ⟨g, w, ψ, hgy, hg, hψw, hw, hψ, -⟩ := trv_of_card_fix hyN hsq hfix
    have hy : ∀ v, toAddMap (hat Φ e (hEN he)) v = trvW (dotL ψ) w v := fun v => by
      rw [hgy]
      exact dg_eq_trvW hg v
    refine ⟨w, ψ, hψ, hψw, hy, ?_⟩
    rw [← commSub_top_trvW hy (dotL_ne_zero hψ) hψw, hc1]
  obtain ⟨w₀, ψ₀, hψ₀, hψw₀, hy₀, hP₀⟩ := hstr e₀ he₀E he₀
  have hw₀ : w₀ ≠ 0 := by
    intro h0
    have h1 := congrArg (fun S : Subgroup (W6 K) => Nat.card ↥S) hP₀
    rw [h0, Submodule.span_singleton_eq_bot.mpr rfl, card_sqSub, hPc] at h1
    have h2 : Nat.card ↥(⊥ : Submodule K (Fin 3 → K)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨inferInstance, inferInstance⟩
    rw [h2] at h1
    have hq : 1 < Nat.card K := Finite.one_lt_card
    have : 1 < Nat.card K ^ 2 := Nat.one_lt_pow (by norm_num) hq
    omega
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : Fin 3 → K, dotL ψ₀ v₀ = 1 := by
    obtain ⟨j, hj⟩ : ∃ j, ψ₀ j ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hψ₀ (funext hc)
    exact ⟨Pi.single j (ψ₀ j)⁻¹, by rw [dotL_apply, dotProduct_single, mul_inv_cancel₀ hj]⟩
  set ℓ : Submodule K (Fin 3 → K) := K ∙ w₀ with hℓ
  have hcomm' : commSub (natSub a b) ((autI h.elemW E).map (congrHom Φ)) = natSubOf a b ℓ := by
    apply le_antisymm
    · rw [commSub, Subgroup.closure_le]
      rintro _ ⟨y, hy, v, ⟨u, rfl⟩, rfl⟩
      obtain ⟨e, he, heE, rfl⟩ := (mem_map_autI Φ).mp hy
      by_cases heW : e ∈ Subgroup.centralizer (W : Set G)
      · rw [(hat_eq_one_iff Φ he).mpr heW, MulAut.one_apply, mul_inv_cancel]
        exact (natSubOf a b ℓ).one_mem
      · obtain ⟨w, ψ, -, -, hyw, hPw⟩ := hstr e heE heW
        have hwℓ : w ∈ ℓ := by
          have := eq_of_sqSub_eq (hPw.trans hP₀.symm)
          rw [← this]
          exact Submodule.mem_span_singleton_self w
        rw [← ofAdd_toAdd u, comm_natEmb_trvW hyw]
        exact mem_natSubOf.mpr ⟨_, ℓ.smul_mem _ hwℓ, rfl⟩
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := mem_natSubOf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs
      refine Subgroup.subset_closure ⟨_, hat_mem_map_autI Φ (hEN he₀E) he₀E,
        natEmb a b (Multiplicative.ofAdd (c • v₀)), ⟨_, rfl⟩, ?_⟩
      rw [comm_natEmb_trvW hy₀, LinearMap.map_smul, hv₀, smul_eq_mul, mul_one]
  have hVE : ⁅V, E⁆ = (natSubOf a b ℓ).map (psi Φ) := by
    rw [commutator_eq_map Φ h.le_W hEN, hV, hcomm']
  have hcV := h.cV
  refine ⟨?_, ?_, ?_⟩
  · rw [hVE]
    calc (natSubOf a b ℓ).map (psi Φ) ≤ (natSub a b).map (psi Φ) :=
          Subgroup.map_mono (natSubOf_le ℓ)
      _ = (V.comap (psi Φ)).map (psi Φ) := by rw [hV]
      _ = V := map_comap_psi Φ h.le_W
  · rw [hcV]
    refine isEndStable_of_scal Φ hL h.le_W hab hV fun c x hx => ?_
    rw [hVE, Subgroup.mem_map_iff_mem (psi_injective Φ)] at hx ⊢
    obtain ⟨s, hs, rfl⟩ := mem_natSubOf.mp hx
    rw [scalHom_natEmb, toAdd_ofAdd]
    exact mem_natSubOf.mpr ⟨_, ℓ.smul_mem c hs, rfl⟩
  · rw [hcV, Subgroup.relIndex_bot_left, hVE,
      Subgroup.card_map_of_injective (psi_injective Φ), card_natSubOf hab,
      Module.natCard_eq_pow_finrank (K := K), finrank_span_singleton hw₀, pow_one, hK]

theorem factsVM_holds : FactsVM :=
  ⟨factVMParam_holds, factVMRank_holds, factVMOffender_holds, factVMR2_holds,
    factVMRootElt_holds, factVMOddCent_holds, factVMRootInv_holds, factVMR2Pair_holds⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
