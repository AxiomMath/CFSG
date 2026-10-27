module

public import CFSG.Sporadic.Schreier.LyGLQExclusion
public import CFSG.Sporadic.Schreier.LyOddCoreInner
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.SymmetricLocal
  (perfect_central_two_cover_alternating_outer_fixed_odd_core)

theorem fixes_centralizer_cases {T : Type*} [Group T] (hT : Nonempty (T ≃* NativeSporadic.Ly))
    {a : T} (ha : orderOf a = 2) {γ : MulAut T}
    (hγ : ∀ c ∈ Subgroup.centralizer ({a} : Set T), γ c = c) :
    γ = 1 ∨ γ = MulAut.conj a := by
  obtain ⟨e₀⟩ := hT
  have e : T ≃* J := e₀.trans lyEquivJ
  have hτ : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq, ha]
  obtain ⟨x, hx⟩ := involution_centralizer_fusion_generator.2 (e a) hτ
  obtain ⟨θ, hθa⟩ : ∃ θ : T ≃* J, θ a = lyz := by
    refine ⟨{ toFun := fun t => x⁻¹ * e t * x
              invFun := fun y => e.symm (x * y * x⁻¹)
              left_inv := fun t => by
                show e.symm (x * (x⁻¹ * e t * x) * x⁻¹) = t
                rw [show x * (x⁻¹ * e t * x) * x⁻¹ = e t by group, MulEquiv.symm_apply_apply]
              right_inv := fun y => by
                show x⁻¹ * e (e.symm (x * y * x⁻¹)) * x = y
                rw [MulEquiv.apply_symm_apply]
                group
              map_mul' := fun s t => by
                show x⁻¹ * e (s * t) * x = x⁻¹ * e s * x * (x⁻¹ * e t * x)
                rw [map_mul]
                group }, ?_⟩
    show x⁻¹ * e a * x = lyz
    rw [← hx]
    group
  have hγ' : ∀ c ∈ lyC, (θ.symm.trans (γ.trans θ) : MulAut J) c = c := by
    intro c hc
    rw [lyC_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hc
    have hmem : θ.symm c ∈ Subgroup.centralizer ({a} : Set T) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply θ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hθa, hc]
    show θ (γ (θ.symm c)) = c
    rw [hγ _ hmem, MulEquiv.apply_symm_apply]
  rcases fixes_C_cases hγ' with h | h
  · left
    apply MulEquiv.ext
    intro t
    have h1 := DFunLike.congr_fun h (θ t)
    have h2 : θ (γ t) = θ t := by
      have : θ (γ (θ.symm (θ t))) = θ t := h1
      rwa [MulEquiv.symm_apply_apply] at this
    exact θ.injective h2
  · right
    apply MulEquiv.ext
    intro t
    have h1 := DFunLike.congr_fun h (θ t)
    have h2 : θ (γ t) = lyz * θ t * lyz⁻¹ := by
      have : θ (γ (θ.symm (θ t))) = lyz * θ t * lyz⁻¹ := h1
      rwa [MulEquiv.symm_apply_apply] at this
    rw [MulAut.conj_apply]
    apply θ.injective
    rw [h2, map_mul, map_mul, map_inv, hθa]

theorem apply_mem_centralizer {T : Type*} [Group T] {α : MulAut T} {a : T} (ha : α a = a)
    {x : T} (hx : x ∈ Subgroup.centralizer ({a} : Set T)) :
    α x ∈ Subgroup.centralizer ({a} : Set T) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc α x * a = α x * α a := by rw [ha]
    _ = α (x * a) := (map_mul α _ _).symm
    _ = α (a * x) := by rw [hx]
    _ = α a * α x := map_mul α _ _
    _ = a * α x := by rw [ha]

theorem map_centralizer_eq {T : Type*} [Group T] {α : MulAut T} {a : T} (ha : α a = a) :
    (Subgroup.centralizer ({a} : Set T)).map α.toMonoidHom =
      Subgroup.centralizer ({a} : Set T) := by
  have ha' : α⁻¹ a = a := by
    calc α⁻¹ a = α⁻¹ (α a) := by rw [ha]
      _ = a := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact apply_mem_centralizer ha hx
  · intro hy
    refine ⟨α⁻¹ y, apply_mem_centralizer ha' hy, ?_⟩
    show α (α⁻¹ y) = y
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

@[expose] def restrictCent {T : Type*} [Group T] (α : MulAut T) (a : T) (ha : α a = a) :
    MulAut (Subgroup.centralizer ({a} : Set T)) :=
  (α.subgroupMap (Subgroup.centralizer ({a} : Set T))).trans
    (MulEquiv.subgroupCongr (map_centralizer_eq ha))

theorem restrictCent_apply {T : Type*} [Group T] (α : MulAut T) (a : T) (ha : α a = a)
    (x : Subgroup.centralizer ({a} : Set T)) : (restrictCent α a ha x : T) = α x := rfl

theorem le_oddCore_of_odd {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hodd : Odd (Nat.card N)) : N ≤ CFSG.oddCore G :=
  le_sSup ⟨hN, hodd⟩

variable {T : Type*} [Group T] [Finite T]

theorem oddCore_fixed_restrict (hT : Nonempty (T ≃* NativeSporadic.Ly)) {α : MulAut T}
    (hα : α * α = 1) (hout : α ∉ (MulAut.conj : T →* MulAut T).range) {a : T}
    (ha : orderOf a = 2) (hfa : α a = a) :
    CFSG.oddCore (fixedSubgroup (restrictCent α a hfa)) = ⊥ := by
  obtain ⟨hq, hZ, hiso⟩ := involution_centralizers_quasisimple hT a ha
  have : Group.IsPerfect (Subgroup.centralizer ({a} : Set T)) := hq.1
  have hZ2 : IsPGroup 2 (Subgroup.center (Subgroup.centralizer ({a} : Set T))) :=
    IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hβ : restrictCent α a hfa * restrictCent α a hfa = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [MulAut.mul_apply, restrictCent_apply, restrictCent_apply, MulAut.one_apply,
      ← MulAut.mul_apply, hα, MulAut.one_apply]
  have hβout : restrictCent α a hfa ∉
      (MulAut.conj : Subgroup.centralizer ({a} : Set T) →* MulAut _).range := by
    rintro ⟨u, hu⟩
    have hfixH : ∀ c ∈ Subgroup.centralizer ({a} : Set T),
        (MulAut.conj (u : T)⁻¹ * α) c = c := by
      intro c hc
      have h1 := congrArg (fun γ : MulAut (Subgroup.centralizer ({a} : Set T)) =>
        ((γ ⟨c, hc⟩ : Subgroup.centralizer ({a} : Set T)) : T)) hu
      have h2 : (u : T) * c * (u : T)⁻¹ = α c := by
        simp only [MulAut.conj_apply, restrictCent_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h1
        exact h1
      rw [MulAut.mul_apply, ← h2, MulAut.conj_apply]
      group
    apply hout
    rcases fixes_centralizer_cases hT ha hfixH with h | h
    · refine ⟨(u : T), ?_⟩
      have h2 : α = (MulAut.conj (u : T)⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h2, map_inv, inv_inv]
    · refine ⟨(u : T) * a, ?_⟩
      have h2 : α = MulAut.conj (u : T) * MulAut.conj a := by
        rw [← h, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
      rw [h2, map_mul]
  exact perfect_central_two_cover_alternating_outer_fixed_odd_core (n := 11) (by norm_num)
    (by norm_num) hZ2 hiso _ hβ hβout

theorem outer_involution_fixed_odd_core (hT : Nonempty (T ≃* NativeSporadic.Ly)) (α : MulAut T)
    (hα : α ^ 2 = 1) (hout : α ∉ (MulAut.conj : T →* MulAut T).range) :
    CFSG.oddCore (fixedSubgroup α) = ⊥ := by
  have hα' : α * α = 1 := by rw [← pow_two]; exact hα
  set D := fixedSubgroup α with hD
  obtain ⟨⟨E, hED, hea, hcard⟩, -⟩ := outer_involution_fixed_rank_one_exclusion hT α hα
  set R := (CFSG.oddCore D).map D.subtype with hR
  have hRD : R ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hRodd : Odd (Nat.card R) := by
    rw [hR, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact odd_card_oddCore_ly D
  have hRnorm : ∀ d ∈ D, ∀ r ∈ R, d * r * d⁻¹ ∈ R := by
    rintro d hd _ ⟨r, hr, rfl⟩
    refine ⟨⟨d, hd⟩ * r * ⟨d, hd⟩⁻¹, (CFSG.oddCore_normal (G := D)).conj_mem r hr _, ?_⟩
    rfl
  have hloc : ∀ a ∈ E, a ≠ 1 → R ⊓ Subgroup.centralizer ({a} : Set T) = ⊥ := by
    intro a haE ha1
    have ha2 : orderOf a = 2 := by
      apply orderOf_eq_prime _ ha1
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
    have hfa : α a = a := hED haE
    have hcore := oddCore_fixed_restrict hT hα' hout ha2 hfa
    set H := Subgroup.centralizer ({a} : Set T)
    set Fβ := fixedSubgroup (restrictCent α a hfa)
    set K : Subgroup Fβ := R.comap (H.subtype.comp Fβ.subtype) with hK
    have hKn : K.Normal := by
      constructor
      intro k hk x
      show ((x * k * x⁻¹ : Fβ) : H).1 ∈ R
      have hxD : (((x : Fβ) : H) : T) ∈ D := by
        have h := congrArg Subtype.val (x.2 : restrictCent α a hfa (x : H) = (x : H))
        change (restrictCent α a hfa (x : H) : T) = ((x : H) : T) at h
        rw [restrictCent_apply] at h
        exact h
      have := hRnorm _ hxD _ hk
      simpa using this
    have hKodd : Odd (Nat.card K) := by
      let φ : K →* R := MonoidHom.codRestrict ((H.subtype.comp Fβ.subtype).comp K.subtype) R
        fun x => x.2
      have hφ : Function.Injective φ := by
        intro x y h
        have h' := congrArg (fun z : R => (z : T)) h
        exact Subtype.ext (Subtype.ext (Subtype.ext h'))
      exact Odd.of_dvd_nat hRodd (Subgroup.card_dvd_of_injective φ hφ)
    have hKbot : K = ⊥ := by
      have := le_oddCore_of_odd hKn hKodd
      rw [hcore] at this
      exact le_bot_iff.1 this
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyR, hyH⟩ := hy
    have hyFβ : (⟨y, hyH⟩ : H) ∈ Fβ := by
      show (restrictCent α a hfa ⟨y, hyH⟩ : H) = ⟨y, hyH⟩
      apply Subtype.ext
      rw [restrictCent_apply]
      exact hRD hyR
    have hyK : (⟨⟨y, hyH⟩, hyFβ⟩ : Fβ) ∈ K := hyR
    rw [hKbot, Subgroup.mem_bot] at hyK
    have := congrArg (fun z : Fβ => ((z : H) : T)) hyK
    simpa using this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane
    2 Nat.prime_two E R
    (fun m => Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) m m.2))
    (by rw [hcard]; norm_num) (fun h => (Nat.not_even_iff_odd.2 hRodd) (even_iff_two_dvd.2 h))
    (by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        exact hRnorm m (hED hm) r hr
      · intro hr
        have := hRnorm m⁻¹ (D.inv_mem (hED hm)) _ hr
        simpa [mul_assoc] using this)
  have hRbot : R = ⊥ := by
    rw [hgen]
    refine iSup_eq_bot.2 fun m => iSup_eq_bot.2 fun hm => hloc m m.2 ?_
    intro h
    exact hm (Subtype.ext h)
  rw [hR, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at hRbot
  exact hRbot

end CFSG.Sporadic.LySchreier
