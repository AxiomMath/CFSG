module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base21
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base19
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base20

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank K8

theorem K8.finrank_ker_eq {K : Type} [Field K] {f : (Fin 3 → K) →ₗ[K] K} (hf : f ≠ 0) :
    Module.finrank K (LinearMap.ker f) = 2 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at h1
  have h2 : Module.finrank K (LinearMap.range f) ≤ 1 := by
    have := Submodule.finrank_le (LinearMap.range f)
    rwa [Module.finrank_self] at this
  have h3 : Module.finrank K (LinearMap.range f) ≠ 0 := fun h0 =>
    hf (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
  omega

theorem factVMR2_holds : FactVMR2 := by
  intro G _ _ L V W X T V₁ V₂ n h B hBT hBe hBa hmW
  obtain ⟨K, _, _, _, hK, Φ, a, b, hL, hX, hab, hV, S₁, S₂, -, hd₂, -, hS₂⟩ := exists_model36 h
  have hBN : B ≤ Subgroup.normalizer (W : Set G) := hBT.trans h.T_le_W
  set Bh := (autI h.elemW B).map (congrHom Φ) with hBh
  obtain ⟨hBhD, hBhc⟩ := offender_model h.two_le hK hX ((map_mem_aSet_iff Φ).mpr hBa)
  have hBhe : IsElemAbelian2 Bh :=
    (isElemAbelian2_map_congrHom Φ).mpr (isElemAbelian2_autI h.elemW hBe hBN)
  have hfixc : Nat.card ↥(fixV Bh) = Nat.card K ^ 4 := by
    rw [hBh, ← comap_psi_inf_centralizer Φ hBN, card_comap_psi Φ inf_le_left]
    have h1 := two_pow_mQuot_mul_card Φ hK
      (inf_le_left : W ⊓ Subgroup.centralizer (B : Set G) ≤ W)
    rw [hmW, show 6 * n = 2 * n + 4 * n by ring, pow_add] at h1
    rw [Nat.eq_of_mul_eq_mul_left (by positivity) h1, hK, ← pow_mul, mul_comm]
  obtain ⟨f, hf0, hkerf, hform, hsurj⟩ := axis_model hBhD hBhe hBhc hfixc
  have hS₂f : S₂ = LinearMap.ker f := by
    have hmove : ∀ u ∈ S₂, ∀ w, f w = 0 → f u • w ∈ S₂ := by
      intro u hu w hw
      obtain ⟨y, hy, hyw⟩ := hsurj w hw
      obtain ⟨x, hxN, hxB, rfl⟩ := (mem_map_autI Φ).mp hy
      have h1 : psi Φ (natEmb a b (Multiplicative.ofAdd u)) ∈ V₂ := by
        have : natEmb a b (Multiplicative.ofAdd u) ∈ V₂.comap (psi Φ) := by
          rw [hS₂]
          exact mem_natSubOf.mpr ⟨u, hu, rfl⟩
        exact this
      have h2 := (Subgroup.mem_normalizer_iff.mp (h.T_le_V₂ (hBT hxB)) _).mp h1
      rw [← psi_hat Φ hxN, trvW_natEmb hyw, toAdd_ofAdd] at h2
      have h3 : natEmb a b (Multiplicative.ofAdd (u + f u • w)) ∈ natSubOf a b S₂ := by
        rw [← hS₂]
        exact h2
      obtain ⟨u', hu', hu'e⟩ := mem_natSubOf.mp h3
      have h4 : u' = u + f u • w :=
        congrArg Multiplicative.toAdd (natEmb_injective hab hu'e)
      have h5 := S₂.sub_mem (h4 ▸ hu') hu
      rwa [add_sub_cancel_left] at h5
    have hle : S₂ ≤ LinearMap.ker f := by
      intro u hu
      by_contra hfu
      have hker : LinearMap.ker f ≤ S₂ := fun w hw => by
        have := S₂.smul_mem (f u)⁻¹ (hmove u hu w hw)
        rwa [smul_smul, inv_mul_cancel₀ hfu, one_smul] at this
      have heq := Submodule.eq_of_le_of_finrank_eq hker (by rw [finrank_ker_eq hf0, hd₂])
      exact hfu (heq ▸ hu : u ∈ LinearMap.ker f)
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_ker_eq hf0, hd₂])
  have hfixV : fixV Bh = sqSub (LinearMap.ker f) := by
    ext v
    rw [mem_fixV_iff_fixPlane hBhD, hkerf]
    rfl
  have hV₂W : V₂ ≤ W := h.le₂.trans h.le_W
  refine ⟨?_, ?_, ?_⟩
  ·
    have hle : V ⊓ Subgroup.centralizer (B : Set G) ≤ W := inf_le_left.trans h.le_W
    have e : V ⊓ Subgroup.centralizer (B : Set G) =
        V ⊓ (W ⊓ Subgroup.centralizer (B : Set G)) := by
      rw [← inf_assoc, inf_eq_left.mpr h.le_W]
    have hc : (V ⊓ Subgroup.centralizer (B : Set G)).comap (psi Φ) = V₂.comap (psi Φ) := by
      rw [e, Subgroup.comap_inf, hV, comap_psi_inf_centralizer Φ hBN, hfixV,
        natSub_inf_sqSub hab, hS₂, hS₂f]
    calc V ⊓ Subgroup.centralizer (B : Set G)
        = ((V ⊓ Subgroup.centralizer (B : Set G)).comap (psi Φ)).map (psi Φ) :=
          (map_comap_psi Φ hle).symm
      _ = (V₂.comap (psi Φ)).map (psi Φ) := by rw [hc]
      _ = V₂ := map_comap_psi Φ hV₂W
  ·
    intro v hv hv₂
    obtain ⟨x, rfl⟩ := exists_psi_eq Φ (h.le_W hv)
    have hx : x ∈ natSub a b := by rw [← hV]; exact hv
    obtain ⟨u₀, rfl⟩ := hx
    have hfu : f (Multiplicative.toAdd u₀) ≠ 0 := by
      intro hfu
      apply hv₂
      have : natEmb a b u₀ ∈ V₂.comap (psi Φ) := by
        rw [hS₂, hS₂f]
        exact mem_natSubOf.mpr ⟨_, hfu, rfl⟩
      exact this
    rw [commutator_eq_map Φ (Subgroup.zpowers_le.mpr (h.le_W hv)) hBN, comap_psi_zpowers,
      ← ofAdd_toAdd u₀, commSub_zpowers_natEmb hform hsurj a b hfu, ← hS₂f, ← hS₂,
      map_comap_psi Φ hV₂W]
  ·
    intro A hAB
    have hcV := h.cV
    rw [hcV]
    have hAN : A ≤ Subgroup.normalizer (W : Set G) := hAB.trans hBN
    have hÂ : (autI h.elemW A).map (congrHom Φ) ≤ linSub :=
      ((Subgroup.map_mono (autI_mono h.elemW hAB)).trans hBhD).trans dgSub_le_linSub
    refine isEndStable_of_scal Φ hL h.le_W hab hV fun c x hx => ?_
    rw [commutator_eq_map Φ h.le_W hAN, hV] at hx ⊢
    rw [Subgroup.mem_map_iff_mem (psi_injective Φ)] at hx ⊢
    exact commSub_natSub_scal hÂ a b c hx

end CFSG.Quasithin.Vol2.Ch11.SecB
