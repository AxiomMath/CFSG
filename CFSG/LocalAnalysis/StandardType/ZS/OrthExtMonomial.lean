module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtMonomialFree
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtStab

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {G H B : Subgroup (U ≃ₗ[ZMod p] U)} {h : U ≃ₗ[ZMod p] U}

private def reflGenSet (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (H : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) : Set (U ≃ₗ[ZMod p] U) :=
  {t | t ∈ H ∧ IsRefl p t ∧ ∀ v, t v - v ∈ LinearMap.ker ((h : U →ₗ[ZMod p] U) - 1)}

private theorem reflStab_eq_closure (H : Subgroup (U ≃ₗ[ZMod p] U)) (h : U ≃ₗ[ZMod p] U) :
    reflStab p H h = Subgroup.closure (reflGenSet p H h) := rfl

private theorem exists_monomialAction_of_mem
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hB : movedGroup B = gmmn p f i₀ i₁ ζ ∨ movedGroup B = g2mmn p f i₀ i₁ ζ)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ B) :
    ∃ d σ, MonomialAction f t d σ := by
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let φ : B →* (V ≃ₗ[ZMod p] V) :=
    restrictHom B V fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  have hg : φ ⟨t, ht⟩ ∈ movedGroup B := MonoidHom.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩
  rcases hB with hB | hB
  · obtain ⟨d, σ, -, -, hdσ⟩ := exists_eq_diagMap_mul_permMap_of_mem_gmmn f hi (hB ▸ hg)
    refine ⟨d, σ, fun v => ?_⟩
    rw [show t ↑v = (((φ ⟨t, ht⟩) v : V) : U) from
      (restrictHom_apply B V _ ⟨t, ht⟩ v).symm, hdσ]
  · obtain ⟨d, σ, -, -, hdσ⟩ := exists_eq_diagMap_mul_permMap_of_mem_g2mmn f hi (hB ▸ hg)
    refine ⟨d, σ, fun v => ?_⟩
    rw [show t ↑v = (((φ ⟨t, ht⟩) v : V) : U) from
      (restrictHom_apply B V _ ⟨t, ht⟩ v).symm, hdσ]

private theorem mem_commutatorSpace_of_scale_ne_one
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {l : Fin 3} {d : reflGenSet p H h → Fin 3 → (ZMod p)ˣ}
    {σ : reflGenSet p H h → Equiv.Perm (Fin 3)}
    (hds : ∀ t : reflGenSet p H h, MonomialAction f ↑t (d t) (σ t))
    (hσ : ∀ t : reflGenSet p H h, σ t l = l)
    (t₀ : reflGenSet p H h) (ht₀ : (d t₀ l : ZMod p) ≠ 1) :
    (f l : U) ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
  have hmem : (↑t₀ : U ≃ₗ[ZMod p] U) ∈ reflStab p H h := by
    rw [reflStab_eq_closure]; exact Subgroup.subset_closure t₀.2
  have hm : (↑t₀ : U ≃ₗ[ZMod p] U) (f l : U) - (f l : U) ∈
      HardMathSupport.Kantor79.movedSpace (↑t₀ : U ≃ₗ[ZMod p] U) := ⟨(f l : U), rfl⟩
  have hsub : (↑t₀ : U ≃ₗ[ZMod p] U) (f l : U) - (f l : U) =
      ((d t₀ l : ZMod p) - 1) • (f l : U) := by
    rw [apply_eq_smul_of_permMap_fixes (hσ t₀) (hds t₀), sub_smul, one_smul]
  have hcoef : (d t₀ l : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr ht₀
  have heq : (f l : U) = ((d t₀ l : ZMod p) - 1)⁻¹ •
      ((↑t₀ : U ≃ₗ[ZMod p] U) (f l : U) - (f l : U)) := by
    rw [hsub, smul_smul, inv_mul_cancel₀ hcoef, one_smul]
  rw [heq]
  exact Submodule.smul_mem _ _ (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hmem hm)

private theorem false_of_scale_ne_one
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {l : Fin 3}
    {d : reflGenSet p H h → Fin 3 → (ZMod p)ˣ}
    {σ : reflGenSet p H h → Equiv.Perm (Fin 3)}
    (hds : ∀ t : reflGenSet p H h, MonomialAction f ↑t (d t) (σ t))
    (hσ : ∀ t : reflGenSet p H h, σ t l = l)
    (t₀ : reflGenSet p H h) (ht₀ : (d t₀ l : ZMod p) ≠ 1) : False := by
  have hsplit : SplitSupport (reflStab p H h) 2 := by
    have h := splitSupport_reflStab hp hD.setting.four_le
      (fun hp3 => by have := hD.setting.five_le_of_eq_three hp3; omega)
      hD.setting.sub.2.1 hD.setting.sub.2.2.2.1 hD.mem hD.isRefl hirr₁
    simpa [h4] using h
  have hfl : ∀ t : reflGenSet p H h,
      (↑t : U ≃ₗ[ZMod p] U) ((f l : HardMathSupport.Kantor79.commutatorSpace B) : U) =
        (d t l : ZMod p) • (f l : U) :=
    fun t => apply_eq_smul_of_permMap_fixes (hσ t) (hds t)
  have hfl_ne : (f l : U) ≠ 0 := fun h0 => f.ne_zero l (Subtype.ext h0)
  let L : Submodule (ZMod p) U := ZMod p ∙ (f l : U)
  have hflV := mem_commutatorSpace_of_scale_ne_one hds hσ t₀ ht₀
  have hLle : L ≤ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := by
    rw [Submodule.span_le]
    exact Set.singleton_subset_iff.mpr hflV
  have hgen : ∀ t ∈ reflGenSet p H h, ∀ w ∈ L, (↑t : U ≃ₗ[ZMod p] U) w ∈ L := by
    intro t htS w hw
    rw [Submodule.mem_span_singleton] at hw ⊢
    obtain ⟨c, rfl⟩ := hw
    refine ⟨c * (d ⟨t, htS⟩ l : ZMod p), ?_⟩
    rw [map_smul, hfl ⟨t, htS⟩, smul_smul]
  have hinv : ∀ g ∈ reflStab p H h, ∀ w ∈ L, g w ∈ L := by
    rw [reflStab_eq_closure]
    exact forall_mem_closure_mapsTo_of_forall hgen
  rcases hirr₁ L bot_le hLle hinv with hbot | htop
  · have hmem : (f l : U) ∈ L := Submodule.mem_span_singleton_self _
    rw [hbot] at hmem
    exact hfl_ne (by simpa using hmem)
  · have hdim : Module.finrank (ZMod p) L =
        Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)) := by
      rw [htop]
    rw [finrank_span_singleton hfl_ne, hsplit.2.1] at hdim
    exact (by norm_num : (1 : ℕ) ≠ 2) hdim

private theorem root_repr_zero
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {l : Fin 3}
    (hle : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B)
    {t : U ≃ₗ[ZMod p] U} (ht : t ∈ reflGenSet p H h)
    {d : Fin 3 → (ZMod p)ˣ} {σ : Equiv.Perm (Fin 3)}
    (hds : MonomialAction f t d σ) (hσ : σ l = l)
    (hfix : t ((f l : HardMathSupport.Kantor79.commutatorSpace B) : U) = (f l : U))
    {a : U} (ha : a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h))
    (ham : a ∈ HardMathSupport.Kantor79.movedSpace t) :
    f.repr (Submodule.inclusion hle ⟨a, ha⟩) l = 0 := by
  have h2p : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hat : t a = -a :=
    HardMathSupport.Kantor79.apply_eq_neg_of_mem_movedSpace ht.2.1.1 ham
  have hfl_ne : (f l : U) ≠ 0 := fun h0 => f.ne_zero l (Subtype.ext h0)
  have hdl : (d l : ZMod p) = 1 := by
    have h3 : (d l : ZMod p) • (f l : U) = (f l : U) := by
      rw [← apply_eq_smul_of_permMap_fixes hσ hds]; exact hfix
    have h4 : ((d l : ZMod p) - 1) • (f l : U) = 0 := by
      rw [sub_smul, one_smul, sub_eq_zero]; exact h3
    exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hfl_ne)
  have htHh : t ∈ reflStab p H h := Subgroup.subset_closure ht
  have ht_aV : t a ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) :=
    apply_mem_commutatorSpace htHh ha
  have hV_eq : (⟨t a, hle ht_aV⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
      (diagMap p f d * permMap p f σ) (Submodule.inclusion hle ⟨a, ha⟩) := by
    refine Subtype.ext ?_
    exact hds (Submodule.inclusion hle ⟨a, ha⟩)
  have hrepr1 : f.repr (⟨t a, hle ht_aV⟩ : HardMathSupport.Kantor79.commutatorSpace B) l =
      (d l : ZMod p) * f.repr (Submodule.inclusion hle ⟨a, ha⟩) (σ.symm l) := by
    have h := congrArg (fun w => f.repr w l) hV_eq
    rwa [repr_diagMap_mul_permMap] at h
  have hneg : f.repr (⟨t a, hle ht_aV⟩ : HardMathSupport.Kantor79.commutatorSpace B) l =
      - f.repr (Submodule.inclusion hle ⟨a, ha⟩) l := by
    have h2 : (⟨t a, hle ht_aV⟩ : HardMathSupport.Kantor79.commutatorSpace B) =
        -(Submodule.inclusion hle ⟨a, ha⟩) :=
      Subtype.ext (by simpa [Submodule.inclusion_apply] using hat)
    rw [h2, map_neg]
    simp
  have hσl : σ.symm l = l := by
    rw [Equiv.symm_apply_eq]; exact hσ.symm
  rw [hσl, hdl, one_mul] at hrepr1
  rw [hrepr1] at hneg
  exact eq_zero_of_eq_neg h2p hneg

private theorem repr_zero_of_scale_eq_one
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {l : Fin 3}
    (hle : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B)
    {d : reflGenSet p H h → Fin 3 → (ZMod p)ˣ}
    {σ : reflGenSet p H h → Equiv.Perm (Fin 3)}
    (hds : ∀ t : reflGenSet p H h, MonomialAction f ↑t (d t) (σ t))
    (hσ : ∀ t : reflGenSet p H h, σ t l = l)
    (hfix : ∀ t : reflGenSet p H h,
      (↑t : U ≃ₗ[ZMod p] U) ((f l : HardMathSupport.Kantor79.commutatorSpace B) : U) =
        (f l : U)) :
    ∀ (v : U) (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)),
      f.repr (Submodule.inclusion hle ⟨v, hv⟩) l = 0 := by
  have hmem : ∀ t : reflGenSet p H h, (↑t : U ≃ₗ[ZMod p] U) ∈ reflStab p H h := by
    intro t; rw [reflStab_eq_closure]; exact Subgroup.subset_closure t.2
  let ψ : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) →ₗ[ZMod p] ZMod p :=
    (Finsupp.lapply l).comp (f.repr.comp (Submodule.inclusion hle))
  have hVs : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) =
      ⨆ t : reflGenSet p H h, HardMathSupport.Kantor79.movedSpace (↑t) := by
    rw [reflStab_eq_closure]
    have h := HardMathSupport.Kantor79.commutatorSpace_closure_eq_iSup_movedSpace
      (Subtype.val : reflGenSet p H h → U ≃ₗ[ZMod p] U)
    simpa [Subtype.range_coe] using h
  have hK : ∀ t : reflGenSet p H h,
      HardMathSupport.Kantor79.movedSpace (↑t : U ≃ₗ[ZMod p] U) ≤
        (LinearMap.ker ψ).map
          (Submodule.subtype (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h))) := by
    intro t a ha
    refine Submodule.mem_map.mpr ⟨⟨a, (HardMathSupport.Kantor79.movedSpace_le_commutatorSpace
      (H := reflStab p H h) (x := (↑t : U ≃ₗ[ZMod p] U)) (hmem t)) ha⟩, ?_, rfl⟩
    exact root_repr_zero hp hle t.2 (hds t) (hσ t) (hfix t) _ ha
  intro v hv
  let v' : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) := ⟨v, hv⟩
  have hv' : v ∈ ⨆ t : reflGenSet p H h,
      HardMathSupport.Kantor79.movedSpace (↑t : U ≃ₗ[ZMod p] U) := by
    rw [← hVs]; exact hv
  rw [Submodule.mem_iSup] at hv'
  obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp (hv' _ hK)
  have hwv' : w = v' := Subtype.ext hwv
  have hψ : ψ v' = 0 := by rwa [hwv'] at hw
  simpa [ψ, v'] using hψ

private theorem false_of_zero_coordinate
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    (hB : movedGroup B = gmmn p f i₀ i₁ ζ ∨ movedGroup B = g2mmn p f i₀ i₁ ζ)
    {l : Fin 3}
    (hle : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B)
    (hzero : ∀ (v : U) (hv : v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)),
      f.repr (Submodule.inclusion hle ⟨v, hv⟩) l = 0) : False := by
  obtain ⟨i, j, hij, hil, hjl, hcover⟩ := exists_pair_fin_three l
  let V := HardMathSupport.Kantor79.commutatorSpace B
  let z : V ≃ₗ[ZMod p] V :=
    diagMap p f (pairUnit p i l ζ) * diagMap p f (pairUnit p j l ζ)
  have hz : z ∈ gmmn p f i₀ i₁ ζ :=
    Subgroup.mul_mem _ (diagMap_pairUnit_mem_gmmn f hi hil (Subgroup.mem_zpowers ζ))
      (diagMap_pairUnit_mem_gmmn f hi hjl (Subgroup.mem_zpowers ζ))
  have hzmem : z ∈ movedGroup B := by
    rcases hB with hB | hB
    · rw [hB]; exact hz
    · rw [hB]; exact gmmn_le_g2mmn f i₀ i₁ ζ hz
  let φ : B →* (V ≃ₗ[ZMod p] V) :=
    restrictHom B V fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  obtain ⟨gB, hgB⟩ := MonoidHom.mem_range.mp hzmem
  have hz_eq : z = diagMap p f (pairUnit p i l ζ * pairUnit p j l ζ) := by
    show diagMap p f (pairUnit p i l ζ) * diagMap p f (pairUnit p j l ζ) = _
    rw [diagMap_mul]
  have hzsmul : ∀ v : V, f.repr v l = 0 → z v = (ζ : ZMod p) • v := by
    intro v hv
    refine f.ext_elem fun m => ?_
    rw [hz_eq, repr_diagMap, map_smul, Finsupp.smul_apply, smul_eq_mul]
    by_cases hml : m = l
    · subst hml; rw [hv, mul_zero, mul_zero]
    · rcases hcover m hml with rfl | rfl <;>
        simp [pairUnit, Pi.mul_apply, hil, hjl, hij, Ne.symm hij]
  have hgζ : ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace (reflStab p H h),
      (gB : U ≃ₗ[ZMod p] U) v = (ζ : ZMod p) • v := by
    intro v hv
    have hφ : ((φ gB) ⟨v, hle hv⟩ : V) = z ⟨v, hle hv⟩ := by rw [hgB]
    have h1 : (gB : U ≃ₗ[ZMod p] U) v = (((φ gB) ⟨v, hle hv⟩ : V) : U) :=
      (restrictHom_apply B V _ gB ⟨v, hle hv⟩).symm
    rw [h1, hφ, show (⟨v, hle hv⟩ : V) = Submodule.inclusion hle ⟨v, hv⟩ from
      (Submodule.inclusion_apply hle ⟨v, hv⟩).symm, hzsmul _ (hzero v hv)]
    rfl
  have hζ' : (ζ : ZMod p) * ζ ≠ 1 := by
    intro h
    exact hζ (Units.ext (by rwa [Units.val_mul, Units.val_one]))
  exact false_of_mem_smul hp hD gB.2 hζ' hgζ

private theorem exists_monomialAction_fixedPointFree
    (hD : LemmaTwoSevenData p G H B h)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ}
    (hB : movedGroup B = gmmn p f i₀ i₁ ζ ∨ movedGroup B = g2mmn p f i₀ i₁ ζ)
    (hnotA : ¬ ∃ l : Fin 3, ∀ t ∈ reflGenSet p H h, ∃ d σ,
      MonomialAction f t d σ ∧ σ l = l) :
    ∃ (x : U ≃ₗ[ZMod p] U) (d : Fin 3 → (ZMod p)ˣ) (σ : Equiv.Perm (Fin 3)),
      x ∈ H ∧ MonomialAction f x d σ ∧ ∀ l, σ l ≠ l := by
  have hstep : ∀ l : Fin 3, ∃ t : U ≃ₗ[ZMod p] U, t ∈ reflGenSet p H h ∧
      ∀ (d : Fin 3 → (ZMod p)ˣ) (σ : Equiv.Perm (Fin 3)),
        MonomialAction f t d σ → σ l ≠ l := by
    intro l
    by_contra hcon
    apply hnotA
    refine ⟨l, fun t htS => ?_⟩
    by_contra hcon2
    exact hcon ⟨t, htS, fun d σ hm hσ => hcon2 ⟨d, σ, hm, hσ⟩⟩
  choose t htS hdec using hstep
  have htB : ∀ l, t l ∈ B := fun l => hD.split.2.2.2.2 (Subgroup.subset_closure (htS l))
  have htH : ∀ l, t l ∈ H := fun l => reflSubgroupIn_le H _ (Subgroup.subset_closure (htS l))
  choose d σ hds using fun l => exists_monomialAction_of_mem hi hB (htB l)
  have hne : ∀ l, σ l l ≠ l := fun l => hdec l (d l) (σ l) (hds l)
  obtain ⟨τ, hτ, hτfree⟩ :=
    exists_fixedPointFree_of_apply_ne (σ₀ := σ 0) (σ₁ := σ 1) (σ₂ := σ 2)
      (hne 0) (hne 1) (hne 2)
  rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨t 0, d 0, σ 0, htH 0, hds 0, hτfree⟩
  · exact ⟨t 1, d 1, σ 1, htH 1, hds 1, hτfree⟩
  · exact ⟨t 2, d 2, σ 2, htH 2, hds 2, hτfree⟩
  · exact ⟨t 0 * t 1, d 0 * (d 1 ∘ (σ 0).symm), σ 0 * σ 1,
      Subgroup.mul_mem _ (htH 0) (htH 1), monomialAction_mul (hds 0) (hds 1), hτfree⟩
  · exact ⟨t 0 * t 2, d 0 * (d 2 ∘ (σ 0).symm), σ 0 * σ 2,
      Subgroup.mul_mem _ (htH 0) (htH 2), monomialAction_mul (hds 0) (hds 2), hτfree⟩
  · exact ⟨t 1 * t 2, d 1 * (d 2 ∘ (σ 1).symm), σ 1 * σ 2,
      Subgroup.mul_mem _ (htH 1) (htH 2), monomialAction_mul (hds 1) (hds 2), hτfree⟩

private theorem false_of_caseB
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    (hB : movedGroup B = gmmn p f i₀ i₁ ζ ∨ movedGroup B = g2mmn p f i₀ i₁ ζ)
    (hnotA : ¬ ∃ l : Fin 3, ∀ t ∈ reflGenSet p H h, ∃ d σ,
      MonomialAction f t d σ ∧ σ l = l) : False := by
  obtain ⟨x, d, σ, hxH, hxd, hσ⟩ :=
    exists_monomialAction_fixedPointFree hD hi hB hnotA
  have hBle : gmmn p f i₀ i₁ ζ ≤ movedGroup B := by
    rcases hB with hB | hB
    · rw [hB]
    · rw [hB]; exact gmmn_le_g2mmn f i₀ i₁ ζ
  exact false_of_apply_eq_diagMap_mul_permMap hp hD h4 hi hζ hBle hxH hσ hxd

private theorem false_of_caseA
    (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    (hB : movedGroup B = gmmn p f i₀ i₁ ζ ∨ movedGroup B = g2mmn p f i₀ i₁ ζ)
    (hA : ∃ l : Fin 3, ∀ t ∈ reflGenSet p H h, ∃ d σ,
      MonomialAction f t d σ ∧ σ l = l) : False := by
  obtain ⟨l, hA'⟩ := hA
  choose d σ hds hσ using fun t : reflGenSet p H h => hA' ↑t t.2
  have hle : HardMathSupport.Kantor79.commutatorSpace (reflStab p H h) ≤
      HardMathSupport.Kantor79.commutatorSpace B := by
    have h3 : 3 ≤ Module.finrank (ZMod p) U := le_trans (by norm_num) hD.setting.four_le
    rw [(commutatorSpace_eq_ker_of_isCentralizingSplit hp h3 hD.split hD.isRefl).1]
    exact commutatorSpace_reflSubgroupIn_le H _
  by_cases hex : ∃ t : reflGenSet p H h, (d t l : ZMod p) ≠ 1
  · exact false_of_scale_ne_one hp hD h4 hirr₁ hds hσ hex.choose hex.choose_spec
  · push Not at hex
    have hfix : ∀ t : reflGenSet p H h,
        (↑t : U ≃ₗ[ZMod p] U) ((f l : HardMathSupport.Kantor79.commutatorSpace B) : U) =
          (f l : U) := by
      intro t
      rw [apply_eq_smul_of_permMap_fixes (hσ t) (hds t), hex t, one_smul]
    exact false_of_zero_coordinate hp hD hi hζ hB hle
      (repr_zero_of_scale_eq_one hp hle hds hσ hfix)

theorem false_of_monomial_of_mul_self_ne_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hD : LemmaTwoSevenData p G H B h) (h4 : Module.finrank (ZMod p) U = 4)
    (hirr₁ : IrredOnSection (reflStab p H h) ⊥
      (HardMathSupport.Kantor79.commutatorSpace (reflStab p H h)))
    {f : Module.Basis (Fin 3) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B)}
    {i₀ i₁ : Fin 3} (hi : i₀ ≠ i₁) {ζ : (ZMod p)ˣ} (hζ : ζ * ζ ≠ 1)
    (hB : movedGroup B = gmmn p f i₀ i₁ ζ ∨ movedGroup B = g2mmn p f i₀ i₁ ζ) : False := by
  by_cases hA : ∃ l : Fin 3, ∀ t ∈ reflGenSet p H h, ∃ d σ,
    MonomialAction f t d σ ∧ σ l = l
  · exact false_of_caseA hp hD h4 hirr₁ hi hζ hB hA
  · exact false_of_caseB hp hD h4 hi hζ hB hA

end CFSG.StandardType.ZS

end
