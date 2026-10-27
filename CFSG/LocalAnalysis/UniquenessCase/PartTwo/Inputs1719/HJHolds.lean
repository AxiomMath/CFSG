module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJDataModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Stab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Facts92
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirty
public import CFSG.Quasithin.Background.SimsD1TransGrp
public import CFSG.RankThree.PartTwo.Sec14.Ronan148JProd

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem k_HJData_holds :
    S17.K_HJData := by
  intro W _ _ hW hrk Y L hLY hN hspor hirr
  obtain ⟨ψ, hψ, hLY', hN'⟩ := exists_model hW hrk hLY hN hspor hirr
  obtain ⟨h7, h3⟩ := hjData_model hLY' hN'
  have hinj := (MulAut.congr ψ).injective
  refine ⟨?_, fun x hx hx7 => ?_, fun x hx hx3 => ?_⟩
  · have h := card_dvd_six_mul_of_normal hLY' hN'
    rwa [← hψ, Subgroup.card_map_of_injective hinj, Subgroup.card_map_of_injective hinj] at h
  · have h := h7 ((MulAut.congr ψ) x) ⟨x, hx, rfl⟩ (by rw [MulEquiv.orderOf_eq]; exact hx7)
    have e := fixV_map_congr_equiv ψ (Subgroup.zpowers x)
    rw [MonoidHom.map_zpowers] at e
    exact (Subgroup.map_eq_bot_iff_of_injective _ ψ.injective).1 (e.symm.trans h)
  · have h := h3 ((MulAut.congr ψ) x) ⟨x, hx, rfl⟩ (by rw [MulEquiv.orderOf_eq]; exact hx3)
    have e := commSub_map_mulAutCongr ψ (⊤ : Subgroup W) (Subgroup.zpowers x)
    rw [Subgroup.map_top_of_surjective _ ψ.surjective, MonoidHom.map_zpowers] at e
    calc 4 ≤ rk ↥(commSub (⊤ : Subgroup W12) (Subgroup.zpowers ((MulAut.congr ψ) x))) := h
      _ = rk ↥((commSub (⊤ : Subgroup W) (Subgroup.zpowers x)).map ψ.toMonoidHom) :=
        congrArg (fun H : Subgroup W12 => rk ↥H) e
      _ = rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers x)) :=
        rk_map_eq_of_injective _ ψ.injective

theorem k_HJGammaOne_holds :
    K_HJGammaOne := by
  intro W _ _ hW Y L hset T hTY hT v₂ hv₂ hcard A hAT hA hA16
  obtain ⟨ψ, hψ, hLY', hN'⟩ := exists_model_of_setup hW hset
  obtain ⟨-, hv2ne, -, -, -, h240⟩ := hjOrbit_facts
  obtain ⟨-, -, -, -, -, -, -, -, hE16, -⟩ := hjT1_facts
  have hT' : IsSylowIn 2 (T.map (MulAut.congr ψ).toMonoidHom)
      (Y.map (MulAut.congr ψ).toMonoidHom) := (E1.isSylowIn_map_mulEquiv (MulAut.congr ψ)).2 hT
  obtain ⟨g, hg, hTg⟩ := exists_conj_hjT1_of_sylow hLY' hN' (Subgroup.map_mono hTY) hT'
  set A' := A.map (MulAut.congr ψ).toMonoidHom with hA'
  set A'' := A'.map (MulAut.conj g⁻¹).toMonoidHom with hA''
  have hA''T : A'' ≤ hjT1 := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a ∈ T.map (MulAut.congr ψ).toMonoidHom := Subgroup.map_mono hAT ha
    have hX : ∀ X : Subgroup (MulAut W12), X ≤ hjT1 →
        a ∈ X.map (MulAut.conj g).toMonoidHom → (MulAut.conj g⁻¹).toMonoidHom a ∈ hjT1 := by
      rintro X hX ⟨t, ht, rfl⟩
      show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ ∈ hjT1
      rw [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group]
      exact hX ht
    rcases hTg with h | h
    · exact hX hjT1 le_rfl (h ▸ ha')
    · exact hX _ inf_le_left (h ▸ ha')
  have hA''16 : Nat.card A'' = 16 := by
    rw [hA'', hA', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.congr ψ).injective, hA16]
  have hA''el : IsElemAbelian2 A'' :=
    (CFSG.Quasithin.FixVLat.isElemAbelian2_map_iff_of_injective
      (MulAut.conj g⁻¹).injective).2
      ((CFSG.Quasithin.FixVLat.isElemAbelian2_map_congr_iff ψ).2 hA)
  have hA''eq := (hE16 A'' hA''T hA''el).2 hA''16
  obtain ⟨l, hl, hlv⟩ := hjGamma_facts A'' hA''eq
  have e0 : (A'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A' := by
    rw [Subgroup.map_conj_map_conj, mul_inv_cancel, map_one]
    exact Subgroup.map_id A'
  have e1 := e0.symm.trans
    (congrArg (fun φ => A''.map φ) (conj_toMonoidHom_eq_congr g))
  have h1 := (Subgroup.ext_iff.1 (gamma_map_congr g A'') (g (l hjV2))).2 ⟨_, hlv, rfl⟩
  have h1' : g (l hjV2) ∈ gammaComm A' :=
    cast (congrArg (fun H => g (l hjV2) ∈ gammaComm H) e1.symm) h1
  obtain ⟨u, hu, hwu⟩ := (Subgroup.ext_iff.1 (gamma_map_congr ψ A) (g (l hjV2))).1 h1'
  have hψv : ψ v₂ ≠ 1 := fun h => hv₂ (ψ.injective (h.trans (map_one ψ).symm))
  have hcard' : Nat.card ↥(MulAction.stabilizer (MulAut W12) (ψ v₂) ⊓ hjL0) = 240 := by
    have e : MulAction.stabilizer (MulAut W12) (ψ v₂) ⊓ hjL0 =
        (MulAction.stabilizer (MulAut W) v₂ ⊓ L).map (MulAut.congr ψ).toMonoidHom := by
      rw [← hψ]
      exact (stab_inf_map_congr ψ v₂ L).symm
    rw [e, Subgroup.card_map_of_injective (MulAut.congr ψ).injective]
    exact hcard
  obtain ⟨l₁, hl₁, hl₁v⟩ := (mem_orbit_v2_iff hψv).2 hcard'
  have hgv : g hjV2 ≠ 1 := fun h => hv2ne (g.injective (h.trans (map_one g).symm))
  obtain ⟨l₂, hl₂, hl₂v⟩ := (mem_orbit_v2_iff hgv).2 (by
    rw [card_stab_of_mem_normalizer hg]
    exact h240)
  have hm : g * l * g⁻¹ * l₂⁻¹ * l₁ ∈ hjL0 :=
    mul_mem (mul_mem ((Subgroup.mem_normalizer_iff.1 hg l).1 hl) (inv_mem hl₂)) hl₁
  rw [← hψ] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  refine ⟨n, hn, ?_⟩
  have h2' : l₂⁻¹ hjV2 = g hjV2 := by
    calc l₂⁻¹ hjV2 = l₂⁻¹ (l₂ (g hjV2)) := by rw [hl₂v]
      _ = g hjV2 := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have h3 : ψ (n v₂) = ψ u := by
    have e2 : (MulAut.congr ψ).toMonoidHom n (ψ v₂) = ψ (n v₂) := by
      show ψ (n (ψ.symm (ψ v₂))) = _
      rw [ψ.symm_apply_apply]
    have e3 : g⁻¹ (g hjV2) = hjV2 := by
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← e2, hnm]
    simp only [MulAut.mul_apply, hl₁v, h2', e3]
    exact hwu.symm
  rw [ψ.injective h3]
  exact hu

theorem k_HJLineScalars_holds :
    K_HJLineScalars := by
  classical
  have : Finite (MulAut W12) := Finite.of_injective (fun e : MulAut W12 => (e : W12 → W12))
    (fun a b h => MulEquiv.ext (congrFun h))
  intro W _ _ hW Y L hset T hTY hT
  obtain ⟨ψ, hψ, hLY', hN'⟩ := exists_model_of_setup hW hset
  obtain ⟨hv1ne, hv2ne, horb, -, h384, h240⟩ := hjOrbit_facts
  obtain ⟨-, hT0L, hT0T1, -, -, -, hA1T0, hA2T0, -, hJ⟩ := hjT1_facts
  obtain ⟨hS1, hS1N, hS2, hEK, hcomm, ⟨eE⟩, ⟨eK⟩⟩ := hjStab_facts
  have hinj : Function.Injective (MulAut.congr ψ).toMonoidHom := (MulAut.congr ψ).injective
  have hT' : IsSylowIn 2 (T.map (MulAut.congr ψ).toMonoidHom)
      (Y.map (MulAut.congr ψ).toMonoidHom) := (E1.isSylowIn_map_mulEquiv (MulAut.congr ψ)).2 hT
  obtain ⟨g, hg, hTg⟩ := exists_conj_hjT1_of_sylow hLY' hN' (Subgroup.map_mono hTY) hT'
  have hstab : ∀ w : W, MulAction.stabilizer (MulAut W12) (ψ w) ⊓ hjL0 =
      (MulAction.stabilizer (MulAut W) w ⊓ L).map (MulAut.congr ψ).toMonoidHom := by
    intro w
    rw [← hψ]
    exact (stab_inf_map_congr ψ w L).symm
  have hcst : ∀ w : W, Nat.card ↥(MulAction.stabilizer (MulAut W) w ⊓ L) =
      Nat.card ↥(MulAction.stabilizer (MulAut W12) (ψ w) ⊓ hjL0) := by
    intro w
    rw [hstab, Subgroup.card_map_of_injective hinj]
  have horbT : ∀ v w : W, (∃ l ∈ L, l v = w) ↔ ∃ m ∈ hjL0, m (ψ v) = ψ w := by
    intro v w
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨(MulAut.congr ψ).toMonoidHom l, by rw [← hψ]; exact ⟨l, hl, rfl⟩, ?_⟩
      show ψ (l (ψ.symm (ψ v))) = ψ (l v)
      rw [ψ.symm_apply_apply]
    · rintro ⟨m, hm, hmv⟩
      rw [← hψ] at hm
      obtain ⟨n, hn, rfl⟩ := hm
      refine ⟨n, hn, ψ.injective ?_⟩
      rw [← hmv]
      show ψ (n v) = ψ (n (ψ.symm (ψ v)))
      rw [ψ.symm_apply_apply]
  have hne : ∀ w : W, w ≠ 1 → ψ w ≠ 1 := fun w hw => (map_ne_one_iff ψ ψ.injective).2 hw
  have hcard_of : ∀ {w w' : W12} {m : MulAut W12}, m ∈ hjL0 → m w = w' →
      Nat.card ↥(MulAction.stabilizer (MulAut W12) w' ⊓ hjL0) =
        Nat.card ↥(MulAction.stabilizer (MulAut W12) w ⊓ hjL0) := by
    intro w w' m hm hmw
    rw [← hmw]
    exact card_stab_of_mem_normalizer (Subgroup.le_normalizer hm) w
  have hgv1 : Nat.card ↥(MulAction.stabilizer (MulAut W12) (g hjV1) ⊓ hjL0) = 384 := by
    rw [card_stab_of_mem_normalizer hg]
    exact h384
  have hgv1ne : g hjV1 ≠ 1 := (map_ne_one_iff g g.injective).2 hv1ne
  obtain ⟨m₁, hm₁, hm₁v⟩ : ∃ m ∈ hjL0, m (g hjV1) = hjV1 := by
    rcases horb _ hgv1ne with h | ⟨m, hm, hmv⟩
    · exact h
    · have h' := hcard_of hm hmv
      rw [h240, hgv1] at h'
      norm_num at h'
  have hψv₁ : ψ (ψ.symm (g hjV1)) = g hjV1 := ψ.apply_symm_apply _
  have hψv₂ : ψ (ψ.symm hjV2) = hjV2 := ψ.apply_symm_apply _
  refine ⟨ψ.symm (g hjV1), ψ.symm hjV2, (map_ne_one_iff _ ψ.symm.injective).2 hgv1ne,
    (map_ne_one_iff _ ψ.symm.injective).2 hv2ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro v hv
    rw [horbT, horbT, hψv₁, hψv₂]
    rcases horb _ (hne v hv) with ⟨m, hm, hmv⟩ | h
    · have hm₁' : m₁⁻¹ hjV1 = g hjV1 := by
        calc m₁⁻¹ hjV1 = m₁⁻¹ (m₁ (g hjV1)) := by rw [hm₁v]
          _ = g hjV1 := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      refine Or.inl ⟨m₁⁻¹ * m, mul_mem (inv_mem hm₁) hm, ?_⟩
      rw [MulAut.mul_apply, hmv, hm₁']
    · exact Or.inr h
  ·
    rw [horbT, hψv₁, hψv₂]
    rintro ⟨m, hm, hmv⟩
    have h' := hcard_of hm hmv
    rw [h240, hgv1] at h'
    norm_num at h'
  ·
    rw [hcst, hψv₁]
    exact hgv1
  ·
    intro x hx
    refine ⟨hx.2, ?_⟩
    have hfx : (MulAut.congr ψ).toMonoidHom x ∈ hjS1.map (MulAut.conj g).toMonoidHom := by
      have h1 : (MulAut.congr ψ).toMonoidHom x ∈
          MulAction.stabilizer (MulAut W12) (ψ (ψ.symm (g hjV1))) ⊓ hjL0 := by
        rw [hstab]
        exact ⟨x, hx, rfl⟩
      rw [hψv₁, ← map_stab_inf_of_mem_normalizer hg, hS1] at h1
      exact h1
    have hJ0 : thompsonJ (hjT1 ⊓ hjL0) = hjA1 ⊔ hjA2 := by
      rw [← hJ]
      refine B6.thompsonJ_eq_of_le ?_ inf_le_left
      rw [hJ]
      exact sup_le (le_inf (hA1T0.trans hT0T1) (hA1T0.trans hT0L))
        (le_inf (hA2T0.trans hT0T1) (hA2T0.trans hT0L))
    have hJT : (thompsonJ T).map (MulAut.congr ψ).toMonoidHom =
        (hjA1 ⊔ hjA2).map (MulAut.conj g).toMonoidHom := by
      rw [← SimsD1.TransGrp.thompsonJ_map_eq _ hinj]
      rcases hTg with h | h <;>
        rw [h, SimsD1.TransGrp.thompsonJ_map_eq _ (MulAut.conj g).injective]
      · rw [hJ]
      · rw [hJ0]
    have hN2 : (MulAut.congr ψ).toMonoidHom x ∈ Subgroup.normalizer
        (((thompsonJ T).map (MulAut.congr ψ).toMonoidHom : Subgroup (MulAut W12)) :
          Set (MulAut W12)) := by
      rw [hJT, ← Subgroup.map_equiv_normalizer_eq]
      obtain ⟨s, hs, hsx⟩ := hfx
      exact ⟨s, hS1N hs, hsx⟩
    rw [← Subgroup.map_equiv_normalizer_eq] at hN2
    exact (Subgroup.mem_map_iff_mem hinj).1 hN2
  ·
    have e1 : ↥(MulAction.stabilizer (MulAut W) (ψ.symm hjV2) ⊓ L) ≃*
        ↥(MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0) :=
      (Subgroup.equivMapOfInjective _ _ hinj).trans
        (MulEquiv.subgroupCongr (by rw [← hstab, hψv₂]))
    obtain ⟨e2⟩ :=
      CFSG.RankThree.PartTwo.Sec14.Ronan148J.nonempty_mulEquiv_prod_of_commute_of_equiv
        hcomm hEK hS2 eE eK
    exact ⟨e1.trans e2⟩
  ·
    intro v hv hcv t htY ht2 hrk
    have htY' : (MulAut.congr ψ) t ∈ Y.map (MulAut.congr ψ).toMonoidHom := ⟨t, htY, rfl⟩
    have ht2' : orderOf ((MulAut.congr ψ) t) = 2 := (MulEquiv.orderOf_eq _ t).trans ht2
    obtain ⟨S, hS, htS⟩ := exists_isSylowIn_ge 2 (Subgroup.zpowers_le.2 htY')
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2', pow_one]))
    obtain ⟨g', hg', hSg'⟩ := exists_conj_hjT1_of_sylow hLY' hN' hS.le hS
    have htS' : (MulAut.congr ψ) t ∈ S := htS (Subgroup.mem_zpowers _)
    set t₀ := g'⁻¹ * (MulAut.congr ψ) t * g' with ht₀
    have ht₀T : t₀ ∈ hjT1 := by
      have hX : ∀ X : Subgroup (MulAut W12), X ≤ hjT1 →
          (MulAut.congr ψ) t ∈ X.map (MulAut.conj g').toMonoidHom → t₀ ∈ hjT1 := by
        rintro X hX ⟨s, hs, hst⟩
        have e : t₀ = s := by
          rw [ht₀, ← hst]
          show g'⁻¹ * (g' * s * g'⁻¹) * g' = s
          group
        rw [e]
        exact hX hs
      rcases hSg' with h | h
      · exact hX hjT1 le_rfl (h ▸ htS')
      · exact hX _ inf_le_left (h ▸ htS')
    have hct : MulAut.congr g' t₀ = (MulAut.congr ψ) t := by
      refine MulEquiv.ext fun w => ?_
      show g' (t₀ (g'.symm w)) = (MulAut.congr ψ) t w
      rw [ht₀]
      simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply]
    have ht₀2 : orderOf t₀ = 2 :=
      (MulEquiv.orderOf_eq (MulAut.congr g') t₀).symm.trans
        ((congrArg orderOf hct).trans ht2')
    have hrk₀ : rk ↥(commSub (⊤ : Subgroup W12) (Subgroup.zpowers t₀)) =
        rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) :=
      (rk_commSub_congr g' t₀).symm.trans
        ((congrArg (fun z : MulAut W12 =>
          rk ↥(commSub (⊤ : Subgroup W12) (Subgroup.zpowers z))) hct).trans
          (rk_commSub_congr ψ t))
    obtain ⟨h4, s₁, hs₁, s₂, hs₂, ho₁, ho₂, ho₁₂⟩ :=
      hjInvolution_facts t₀ ht₀T ht₀2 (hrk₀.trans_lt hrk)
    refine ⟨hrk₀.symm.trans h4, fun H hH hidx => ?_⟩
    have hF : ∀ s ∈ fixV (Subgroup.zpowers t₀),
        ψ.symm (g' s) ∈ fixV (Subgroup.zpowers t) := by
      intro s hs
      have h2 := (Subgroup.ext_iff.1 (fixV_zpowers_congr g' t₀) (g' s)).2 ⟨s, hs, rfl⟩
      have h3 : g' s ∈ fixV (Subgroup.zpowers ((MulAut.congr ψ) t)) :=
        cast (congrArg (fun z : MulAut W12 => g' s ∈ fixV (Subgroup.zpowers z)) hct) h2
      exact Subgroup.mem_map_equiv.1 ((Subgroup.ext_iff.1 (fixV_zpowers_congr ψ t) (g' s)).1 h3)
    have key : ∀ w : W12, (∃ l ∈ hjL0, l hjV2 = w) → ψ.symm (g' w) ∈ H →
        ∃ n ∈ L, n v ∈ H := by
      rintro w ⟨l, hl, rfl⟩ hwH
      obtain ⟨m, hm, hmv⟩ := exists_mem_hjL0_apply_eq_of_card (hne v hv)
        ((map_ne_one_iff g' g'.injective).2 ((map_ne_one_iff l l.injective).2 hv2ne))
        ((hcst v).symm.trans hcv) (card_stab_conj_v2 hg' hl)
      obtain ⟨n, hn, hnv⟩ := (horbT v (ψ.symm (g' (l hjV2)))).2
        ⟨m, hm, by rw [hmv, ψ.apply_symm_apply]⟩
      exact ⟨n, hn, by rw [hnv]; exact hwH⟩
    have hu₁ := hF s₁ hs₁
    have hu₂ := hF s₂ hs₂
    by_cases h1 : ψ.symm (g' s₁) ∈ H
    · exact key s₁ ho₁ h1
    by_cases h2 : ψ.symm (g' s₂) ∈ H
    · exact key s₂ ho₂ h2
    have h12 : (⟨_, hu₁⟩ : ↥(fixV (Subgroup.zpowers t))) * ⟨_, hu₂⟩ ∈
        H.subgroupOf (fixV (Subgroup.zpowers t)) :=
      (Subgroup.mul_mem_iff_of_index_two hidx).2 (iff_of_false h1 h2)
    refine key (s₁ * s₂) ho₁₂ ?_
    have e : ψ.symm (g' (s₁ * s₂)) = ψ.symm (g' s₁) * ψ.symm (g' s₂) := by
      rw [map_mul, map_mul]
    rw [e]
    exact h12

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
