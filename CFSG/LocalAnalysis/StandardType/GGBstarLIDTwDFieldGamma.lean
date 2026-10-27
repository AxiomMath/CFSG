module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDTwDFieldInd
public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldR

public section

namespace CFSG.StandardType

namespace LIDTwDF

open CFSG.Assembly CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL Matrix
  OrthBstarOdd Module QuadraticMap

section Transport

variable {R R' : Type} [Group R] [Group R']

theorem ggFieldInnR_of_mulEquiv {p r : ℕ} (e : R ≃* R')
    (h : GGFieldInnR p r R' (LargeEvenInnSet R')) : GGFieldInnR p r R (LargeEvenInnSet R) := by
  intro Eb Eh hEbI hEb hr h3 ⟨V, hV1, hV2, hV⟩ hle hEh ⟨f, hfEh, hfI⟩
  set c := MulAut.congr e with hc
  have hcapp : ∀ (φ : MulAut R) (x : R), c φ (e x) = e (φ x) := fun φ x => by
    change e (φ (e.symm (e x))) = e (φ x)
    rw [MulEquiv.symm_apply_apply]
  have hcard' : ∀ H : Subgroup (MulAut R), Nat.card (H.map c.toMonoidHom) = Nat.card H :=
    fun H => Subgroup.card_map_of_injective c.injective
  obtain ⟨E'', hlt, hE''le, W, hW1, hW2, hW⟩ := h (Eb.map c.toMonoidHom) (Eh.map c.toMonoidHom)
    (by
      rintro _ ⟨φ, hφ, rfl⟩
      obtain ⟨x, rfl⟩ := hEbI hφ
      exact ⟨e x, (OuterAutomorphisms.congr_conj e x).symm⟩)
    (TableB.isElemAbelian_map hEb _) (by rw [hcard']; exact hr) (by rw [hcard']; exact h3)
    ⟨V.map e.toMonoidHom,
      fun h0 => hV1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h0),
      hV2.map _, by
        rintro _ ⟨φ, hφ, rfl⟩ _ ⟨v, hv, rfl⟩
        exact ⟨φ v, hV φ hφ v hv, (hcapp φ v).symm⟩⟩
    (Subgroup.map_mono hle) (TableB.isElemAbelian_map hEh _)
    ⟨c f, ⟨f, hfEh, rfl⟩, fun hcf => hfI (by
      obtain ⟨x', hx'⟩ := hcf
      refine ⟨e.symm x', c.injective ?_⟩
      rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hx'])⟩
  have hE''eq : (E''.comap c.toMonoidHom).map c.toMonoidHom = E'' :=
    Subgroup.map_comap_eq_self_of_surjective c.surjective _
  refine ⟨E''.comap c.toMonoidHom, lt_of_le_of_ne (fun φ hφ => hlt.le ⟨φ, hφ, rfl⟩) fun heq => ?_,
    fun φ hφ => ?_, W.comap e.toMonoidHom, fun h0 => hW1 ?_, ?_, fun φ hφ w hw => ?_⟩
  · apply hlt.ne
    rw [← hE''eq, ← heq]
  · obtain ⟨ψ, hψ, hψφ⟩ := hE''le hφ
    have : ψ = φ := c.injective hψφ
    exact this ▸ hψ
  · rw [eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := e.surjective w
    have hx : x ∈ W.comap e.toMonoidHom := hw
    rw [h0, Subgroup.mem_bot] at hx
    rw [hx, map_one]
    exact one_mem _
  · exact hW2.comap_of_injective e.toMonoidHom e.injective
  · change e (φ w) ∈ W
    rw [← hcapp]
    exact hW _ hφ _ hw

end Transport

theorem symm_mem_of_mem {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Finite V]
    (G : V ≃+ V) {Y : Submodule K V} (hGY : ∀ y ∈ Y, G y ∈ Y) {y : V} (hy : y ∈ Y) :
    G.symm y ∈ Y := by
  have hinj : Function.Injective (fun z : Y => (⟨G z, hGY z z.2⟩ : Y)) := fun z z' h =>
    Subtype.ext (G.injective (congrArg Subtype.val h))
  obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨y, hy⟩
  have h1 : G (z : V) = y := congrArg Subtype.val hz
  rw [← h1, AddEquiv.symm_apply_apply]
  exact z.2

section Gamma

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ggFieldInnR_gamma {f n p : ℕ} (hf : Nat.card K = 2 ^ f) (hn4 : 4 ≤ n) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) :
    GGFieldInnR p (n - 1) (matrixDerived (Qm n hn4 b c)) (LargeEvenInnSet _) := by
  classical
  intro Eb Eh hEbI hEb hr _ ⟨U, hU1, hU2, hUinv⟩ hle hEh ⟨φ, hφEh, hφI⟩
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hf, h0, pow_zero] at h1
      omega
    · exact h0
  obtain ⟨hnd, hT3⟩ := regular_coordinateQuadMinus n K b c hn4 hirr
  have hZ : Subgroup.center (matrixDerived (Qm n hn4 b c)) = ⊥ :=
    OrthRestOdd.center_matrixDerived_eq_bot hnd (by omega)
  have hinj := OrthRest.conj_injective hZ
  have : Finite (GL (Fin (2 * n)) K) := Finite.of_injective (fun g : GL (Fin (2 * n)) K =>
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) K)) Units.val_injective
  have hIsoΓ : ∀ x : matrixDerived (Qm n hn4 b c), ∀ v,
      Qm n hn4 b c (((x : GL (Fin (2 * n)) K)).val *ᵥ v) = Qm n hn4 b c v := fun x v =>
    (mem_matrixIsometries_iff _ _).1 (matrixDerived_le_isometries _ x.2) v
  set Ab := Eb.comap (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) with hAb
  have hEbInn : Eb ≤ OuterAutomorphisms.inner (matrixDerived (Qm n hn4 b c)) := fun ψ hψ =>
    hEbI hψ
  have hcAb : Nat.card Ab = Nat.card Eb := by
    have hmc : Ab.map (MulAut.conj : matrixDerived (Qm n hn4 b c) →* _) = Eb :=
      Subgroup.map_comap_eq_self hEbInn
    rw [← hmc, Subgroup.card_map_of_injective hinj]
  have hAbab : IsElemAbelian p Ab := isElemAbelian_comap hEb hinj
  obtain ⟨G, σ, μ, a, hGs, hμ, hGQ, hGp, hσp, hσ1, hGconj⟩ :=
    exists_semi_of_aut hn4 hirr hpo (hEh.2 φ hφEh) hφI
  have hφfix : ∀ t ∈ Ab, φ t = t := by
    intro t ht
    have hcomm := TableB.IsElemAbelian.comm hEh hφEh (hle ht)
    apply hinj
    rw [← OrthRestOdd.conj_map_mulAut, hcomm, mul_inv_cancel_right]
  have hGT : ∀ t ∈ Ab, ∀ w, ((t : GL (Fin (2 * n)) K)).val *ᵥ G w =
      G (((t : GL (Fin (2 * n)) K)).val *ᵥ w) := by
    intro t ht w
    have h := hGconj t w
    rwa [hφfix t ht] at h
  set ι : matrixDerived (Qm n hn4 b c) →* ((Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)) :=
    matrixLinearIso.toMonoidHom.comp (matrixDerived (Qm n hn4 b c)).subtype with hι
  have hιinj : Function.Injective ι := matrixLinearIso.injective.comp Subtype.val_injective
  have hιQ : ∀ x : matrixDerived (Qm n hn4 b c), ∀ v, (Qm n hn4 b c) (ι x v) = (Qm n hn4 b c) v :=
    fun x v => (mem_matrixIsometries_iff (Qm n hn4 b c) _).1
      (matrixDerived_le_isometries (Qm n hn4 b c) x.2) v
  set E := Ab.map ι with hE
  have hEc : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, TableB.IsElemAbelian.comm hAbab hx hy]
  have hEp : ∀ g ∈ E, g ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hAbab.2 x hx, map_one]
  have hEQ : ∀ g ∈ E, ∀ v, (Qm n hn4 b c) (g v) = (Qm n hn4 b c) v := by
    rintro _ ⟨x, -, rfl⟩ v
    exact hιQ x v
  have hEcard : p ^ (n - 1) ≤ Nat.card E := by
    rw [hE, Subgroup.card_map_of_injective hιinj, hcAb]
    exact hr
  have ha0 : a ≠ 0 := by
    intro ha0
    have hv : ((Pi.single (⟨0, by omega⟩ : Fin (2 * n)) (1 : K)) : Fin (2 * n) → K) ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
    apply hv
    apply Function.Injective.iterate G.injective p
    rw [hGp, ha0, zero_smul]
    exact (Function.iterate_fixed (map_zero G) p).symm
  let S : SemiSim (Qm n hn4 b c) p σ :=
    { G := G.toAddMonoidHom
      μ := μ
      a := a
      smul := hGs
      quad := hGQ
      pow := hGp
      hμ := hμ
      ha := ha0 }
  have hSE : ∀ g ∈ E, ∀ v, S.G (g v) = g (S.G v) := by
    rintro _ ⟨t, ht, rfl⟩ v
    exact (hGT t ht v).symm
  have hfin : finrank K (Fin (2 * n) → K) = 2 * n := Module.finrank_fin_fun K
  obtain ⟨Y, hY0, hYinv, hYsing⟩ := exists_singular_of_two hnd hK1 (S := U.map ι) (N := E)
    (hU2.map ι) (fun h0 => hU1 ((Subgroup.map_eq_bot_iff_of_injective _ hιinj).mp h0))
    (by rintro _ ⟨u, -, rfl⟩ v; exact hιQ u v)
    (by
      rintro _ ⟨u, -, rfl⟩
      exact (mem_matrixDerived_iff_even hnd hT3
        (matrixDerived_le_isometries (Qm n hn4 b c) u.2)).mp u.2)
    hEQ hEp
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨u, hu, rfl⟩
      exact ⟨e * u * e⁻¹, by simpa [MulAut.conj_apply] using hUinv _ he u hu,
        by rw [map_mul, map_mul, map_inv]⟩)
  obtain ⟨Y', hY'0, hY'E, hY'G, hY'sing⟩ := exists_inv_singular hp hp2 hK1 hf hf1 hσp hσ1 n
    (Fin (2 * n) → K) hfin (Qm n hn4 b c) hnd E hEc hEp hEQ hEcard S hSE Y hY0 hYinv hYsing
  have hY'p := polar_zero_of_sing hY'sing
  obtain ⟨x, hxY, w, hwP, hsing, hind⟩ :=
    exists_siegel_pair hnd (by rw [hfin]; omega) hY'0 hY'sing
  set H := (matrixDerived (Qm n hn4 b c)).map
    (matrixLinearIso (d := 2 * n) (K := K)).toMonoidHom with hH
  have hlinH : ∀ g, ι g ∈ H := fun g => ⟨g.val, g.2, rfl⟩
  have hsiegH : siegEquiv hsing ∈ H := by
    refine ⟨matrixLinearIso.symm (siegEquiv hsing), ?_, by simp⟩
    rw [SetLike.mem_coe, mem_matrixDerived_iff hnd hT3, MulEquiv.apply_symm_apply]
    exact siegEquiv_mem_omegaGroup hnd hsing
  set U₂ := (radSub (Qm n hn4 b c) Y' hY'p H).comap ι with hU₂
  have hsieg := siegEquiv_mem_radSub (hY := hY'p) hsing hxY hwP hsiegH
  obtain ⟨h₀, hh₀Γ, hh₀⟩ := hsiegH
  have hU₂1 : U₂ ≠ ⊥ := by
    intro h0
    have hmem : (⟨h₀, hh₀Γ⟩ : matrixDerived (Qm n hn4 b c)) ∈ U₂ := by
      change ι ⟨h₀, hh₀Γ⟩ ∈ radSub (Qm n hn4 b c) Y' hY'p H
      rw [show ι ⟨h₀, hh₀Γ⟩ = siegEquiv hsing from hh₀]
      exact hsieg
    rw [h0, Subgroup.mem_bot] at hmem
    apply siegEquiv_ne_one hnd hsing hind
    rw [← hh₀]
    change ι ⟨h₀, hh₀Γ⟩ = 1
    rw [hmem, map_one]
  have hU₂2 : IsPGroup 2 U₂ := fun u => ⟨2, Subtype.ext (hιinj (by
    rw [show 2 ^ 2 = 4 from rfl, Subgroup.coe_pow, map_pow, OneMemClass.coe_one, map_one]
    exact radSub_pow_four (hY := hY'p) (H := H) u.2))⟩
  have hEbU : ∀ ψ ∈ Eb, ∀ v ∈ U₂, ψ v ∈ U₂ := by
    intro ψ hψ v hv
    obtain ⟨e, rfl⟩ := hEbI hψ
    have he : e ∈ Ab := hψ
    have heE : ι e ∈ E := ⟨e, he, rfl⟩
    change ι (MulAut.conj e v) ∈ radSub (Qm n hn4 b c) Y' hY'p H
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    refine conj_mem_radSub (hιQ e) (hY'E _ heE) (hY'E _ (E.inv_mem heE)) ?_ hv
    rintro _ ⟨h', hh', rfl⟩
    refine ⟨(e : GL (Fin (2 * n)) K) * h' * (e : GL (Fin (2 * n)) K)⁻¹,
      mul_mem (mul_mem e.2 hh') (inv_mem e.2), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    rfl
  have hlinφ : ∀ v w, ι (φ v) w = G (ι v (G.symm w)) := fun v w => by
    have h := hGconj v (G.symm w)
    rwa [AddEquiv.apply_symm_apply] at h
  have hfinV : Finite (Fin (2 * n) → K) := inferInstance
  have hφU : ∀ v ∈ U₂, φ v ∈ U₂ := by
    intro v hv
    obtain ⟨hvH, hvC⟩ := hv
    exact ⟨hlinH (φ v), radCond_semiConj hμ hGQ hY'G
      (fun y hy => symm_mem_of_mem G hY'G hy) hvC (hlinφ v)⟩
  have : Finite U₂ := inferInstance
  have hstab : Eb ⊔ Subgroup.zpowers φ ≤ stabSub U₂ :=
    sup_le (fun ψ hψ => mem_stabSub (hEbU ψ hψ))
      (Subgroup.zpowers_le.mpr (mem_stabSub hφU))
  refine ⟨Eb ⊔ Subgroup.zpowers φ, lt_of_le_of_ne le_sup_left fun heq => hφI ?_,
    sup_le hle (Subgroup.zpowers_le.mpr hφEh), U₂, hU₂1, hU₂2,
    fun ψ hψ v hv => apply_mem_of_mem_stabSub (hstab hψ) hv⟩
  exact hEbI (heq ▸ (le_sup_right : Subgroup.zpowers φ ≤ Eb ⊔ Subgroup.zpowers φ)
    (Subgroup.mem_zpowers φ))

end Gamma

section Recipe

variable {K : Type} [Field K] [Finite K]

theorem ggFieldInnR_omegaMinus {n m p : ℕ} {b c : K} (hK : Nat.card K = 2 ^ n) (hm : 3 ≤ m)
    (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGFieldInnR p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · have h1 : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, h0, pow_zero] at h1
      omega
    · exact h0
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hK
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hodd : ¬ 2 ∣ 2 ^ n + 1 := by
      rw [Nat.dvd_add_right (dvd_pow_self 2 (by omega))]
      norm_num
    exact hodd hpq
  have hn4 : 4 ≤ m + 1 := by omega
  exact ggFieldInnR_of_mulEquiv (RecipeFieldOmega.minusEquiv hn4 b c)
    (ggFieldInnR_gamma hK hn4 hbc hp hp2 (OrthRestOdd.eq_one_of_pow_eq_one_of_dvd hK hp hpq))

end Recipe

end LIDTwDF

end CFSG.StandardType
