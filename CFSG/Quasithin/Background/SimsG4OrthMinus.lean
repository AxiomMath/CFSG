module

public import CFSG.Quasithin.Background.SimsG4OrthMinusOmega
import CFSG.Quasithin.Background.SimsG4Core
import CFSG.Quasithin.Background.SimsG4OrthMinusDickson
import CFSG.Quasithin.Background.SimsG4OrthU

public section

namespace CFSG.Quasithin.SimsG4

open Module QuadraticMap Matrix CFSG.Quasithin.SimsG4.OrthMinus

namespace OrthMinus

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem false_of_irred_of_fixed (hdim : 2 ≤ finrank K W) {H : Subgroup (W ≃ₗ[K] W)}
    (hH : IsIrredOnV H) {w : W} (hw : w ≠ 0) (hfix : ∀ h ∈ H, h w = w) : False := by
  have hfin : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  rcases hH (K ∙ w) (fun h hh v hv => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [map_smul, hfix h hh]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self w)) with h | h
  · exact hw ((Submodule.span_singleton_eq_bot).1 h)
  · have h1 := finrank_span_singleton (K := K) hw
    rw [h, finrank_top] at h1
    omega

theorem conj_mem_closure {Γ : Type*} [Group Γ] {S : Set Γ} {g : Γ}
    (hS : ∀ s ∈ S, g * s * g⁻¹ ∈ S) :
    ∀ x ∈ Subgroup.closure S, g * x * g⁻¹ ∈ Subgroup.closure S := by
  intro x hx
  have hsub : S ⊆ ((Subgroup.closure S).comap (MulAut.conj g).toMonoidHom : Set Γ) :=
    fun s hs => Subgroup.subset_closure (hS s hs)
  exact ((Subgroup.closure_le _).mpr hsub) hx

end OrthMinus

theorem orthIdent_minus {K : Type} [Field K] [Finite K] [CharP K 2]
    {W : Type} [AddCommGroup W] [Module K W] (Q : QuadraticForm K W)
    (hdim : Module.finrank K W = 4)
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hminus : ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → Module.finrank K U ≤ 1)
    (R : Set W) (hR1 : ∀ r ∈ R, Q r = 1)
    (hfield : ∀ K₁ : Subfield K, (∀ r ∈ R, ∀ s ∈ R, QuadraticMap.polar Q r s ∈ K₁) → K₁ = ⊤)
    (hirr : IsIrredOnV (Subgroup.closure
      {g : W ≃ₗ[K] W | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r}))
    (hprim : ¬ IsImprimitiveOnV (Subgroup.closure
      {g : W ≃ₗ[K] W | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r})) :
    ∀ g : W ≃ₗ[K] W, (∀ x, Q (g x) = Q x) →
      g ∈ Subgroup.closure
        {g : W ≃ₗ[K] W | ∃ r ∈ R, ∀ x, g x = x + QuadraticMap.polar Q x r • r} := by
  classical
  set T : Set (W ≃ₗ[K] W) := {g | ∃ r ∈ R, ∀ x, g x = x + polar Q x r • r} with hTdef
  set G := Subgroup.closure T with hG
  have hreflT : ∀ r ∈ R, reflK Q r ∈ T := fun r hr => ⟨r, hr, fun x => reflK_apply Q r x⟩
  have hreflG : ∀ r ∈ R, reflK Q r ∈ G := fun r hr => Subgroup.subset_closure (hreflT r hr)
  have hr0 : ∀ r ∈ R, r ≠ 0 := fun r hr h => by
    have := hR1 r hr
    rw [h, QuadraticMap.map_zero] at this
    exact zero_ne_one this
  have hfin : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  obtain ⟨hWfin, hWeven⟩ := finite_even_card (F := K) (V := W) hdim
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hdim2 : 2 ≤ finrank K W := by omega
  obtain ⟨r₀, hr₀⟩ : R.Nonempty := by
    by_contra hR
    rw [Set.not_nonempty_iff_eq_empty] at hR
    have hGbot : G = ⊥ := by
      rw [hG, Subgroup.closure_eq_bot_iff]
      rintro g ⟨r, hr, -⟩
      rw [hR] at hr
      exact hr.elim
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact false_of_irred_of_fixed hdim2 hirr hw fun h hh => by
      rw [hGbot, Subgroup.mem_bot] at hh
      rw [hh]
      rfl
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  obtain ⟨L, _, _, _, ι, ρ, hL, -, hιsub, hρinj, hρQ, hρtr, hρfix, -⟩ :=
    exists_sl2_model Q hdim hnd hminus
  obtain ⟨hrange, hidx⟩ := range_eq_commutator Q hdim hnd hminus hL ρ hρinj hρQ
  set Ω := ⁅O, O⁆ with hΩ
  have hGO : G ≤ O := by
    rw [hG, Subgroup.closure_le]
    rintro g ⟨r, hr, hg⟩
    have : g = reflK Q r := LinearEquiv.ext fun x => by rw [hg, reflK_apply]
    rw [this]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 (reflK_isometry Q (hR1 r hr))
  have hΩO : Ω ≤ O := by
    rw [hΩ, Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem hg hh) (O.inv_mem hg)) (O.inv_mem hh)
  have hreflΩ : ∀ r ∈ R, reflK Q r ∉ Ω := fun r hr =>
    reflK_not_mem_commutator Q hdim hnd (hr0 r hr)
  have hΩn : ∀ g ∈ O, ∀ h ∈ Ω, g * h * g⁻¹ ∈ Ω := by
    intro g hg h hh
    have hnorm := Subgroup.normal_of_index_eq_two hidx
    have := hnorm.conj_mem ⟨h, hΩO hh⟩ (Subgroup.mem_subgroupOf.2 hh) ⟨g, hg⟩
    exact Subgroup.mem_subgroupOf.1 this
  set H := G ⊓ Ω with hH
  have hHn : ∀ g ∈ G, ∀ h ∈ H, g * h * g⁻¹ ∈ H := fun g hg h hh =>
    ⟨G.mul_mem (G.mul_mem hg hh.1) (G.inv_mem hg), hΩn g (hGO hg) h hh.2⟩
  have hcos : ∀ g ∈ G, g ∈ H ∨ g * reflK Q r₀ ∈ H := by
    intro g hg
    by_cases hgΩ : g ∈ Ω
    · exact Or.inl ⟨hg, hgΩ⟩
    · right
      refine ⟨G.mul_mem hg (hreflG r₀ hr₀), ?_⟩
      have key : (⟨g, hGO hg⟩ : O) * ⟨reflK Q r₀, hGO (hreflG r₀ hr₀)⟩ ∈ Ω.subgroupOf O := by
        rw [Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mem_subgroupOf,
          Subgroup.mem_subgroupOf]
        exact iff_of_false hgΩ (hreflΩ r₀ hr₀)
      exact Subgroup.mem_subgroupOf.1 key
  have hHirr : IsIrredOnV H := irreducible_of_index_two hirr hprim hHn (hreflG r₀ hr₀) hcos
  set M := H.comap ρ with hM
  have hHrange : ∀ h ∈ H, ∃ g ∈ M, ρ g = h := by
    intro h hh
    obtain ⟨g, hg⟩ : h ∈ ρ.range := hrange ▸ hh.2
    exact ⟨g, show ρ g ∈ H by rw [hg]; exact hh, hg⟩
  have himg : ∀ n : ℕ, (Subgroup.closure (powOneSet M n)).map ρ =
      Subgroup.closure {h | h ∈ H ∧ h ^ n = 1} := by
    intro n
    rw [MonoidHom.map_closure]
    congr 1
    ext h
    constructor
    · rintro ⟨g, ⟨hgM, hgn⟩, rfl⟩
      exact ⟨hgM, by rw [← map_pow, hgn, map_one]⟩
    · rintro ⟨hh, hhn⟩
      obtain ⟨g, hgM, rfl⟩ := hHrange h hh
      exact ⟨g, ⟨hgM, hρinj (by rw [map_pow, hhn, map_one])⟩, rfl⟩
  have hGinv : ∀ n : ℕ, ∀ g ∈ G, ∀ h ∈ Subgroup.closure {h | h ∈ H ∧ h ^ n = 1},
      g * h * g⁻¹ ∈ Subgroup.closure {h | h ∈ H ∧ h ^ n = 1} := by
    intro n g hg
    refine conj_mem_closure fun h hh => ⟨hHn g hg h hh.1, ?_⟩
    rw [conj_pow, hh.2, mul_one, mul_inv_cancel]
  have h2 : ∀ n : ℕ, IsPGroup 2 (Subgroup.closure (powOneSet M n)) →
      Subgroup.closure (powOneSet M n) = ⊥ := by
    intro n hP
    have hP' := hP.map ρ
    rw [himg] at hP'
    have hbot := core_trivial G hirr hWeven _ hP' (hGinv n)
    rw [← himg] at hbot
    exact (Subgroup.map_eq_bot_iff_of_injective _ hρinj).1 hbot
  have hodd : ∀ n : ℕ, Odd n →
      (∀ x ∈ Subgroup.closure (powOneSet M n), ∀ y ∈ Subgroup.closure (powOneSet M n),
        x * y = y * x) → Subgroup.closure (powOneSet M n) = ⊥ := by
    intro n hn hcomm
    by_contra hne
    set P := Subgroup.closure (powOneSet M n) with hP
    have hPpow : ∀ x ∈ P, x ^ n = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx => exact hx.2
      | one => exact one_pow n
      | mul x y hx hy ihx ihy =>
        rw [(show Commute x y from hcomm x hx y hy).mul_pow, ihx, ihy, mul_one]
      | inv x _ ihx => rw [inv_pow, ihx, inv_one]
    apply false_of_abelian_odd_normal_of_isometry Q hnd (by omega) hprim (hreflG r₀ hr₀)
      (isTransv_reflK Q hnd (hr0 r₀ hr₀)) (C := P.map ρ)
    · intro hbot
      exact hne ((Subgroup.map_eq_bot_iff_of_injective _ hρinj).1 hbot)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hcomm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      refine Odd.of_dvd_nat hn (orderOf_dvd_of_pow_eq_one ?_)
      rw [← map_pow, hPpow x hx, map_one]
    · rw [hP, himg]
      exact hGinv n
    · rintro _ ⟨x, -, rfl⟩ v
      exact hρQ x v
  have htr : ∀ K₀ : Subfield L, (∀ m ∈ M, (m : Matrix (Fin 2) (Fin 2) L).trace ∈ K₀) →
      (∃ a ∈ M, ∃ b ∈ M, a * a = 1 ∧ b * b = 1 ∧ a * b ≠ b * a) → K₀ = ⊤ := by
    rintro K₀ htrM ⟨a, ha, b, hb, ha2, hb2, hab⟩
    have hsub : ι.fieldRange ≤ K₀ := by
      have hK₁ : K₀.comap ι = ⊤ := hfield (K₀.comap ι) fun r hr s hs => by
        have hrs : reflK Q r * reflK Q s ∈ H :=
          ⟨G.mul_mem (hreflG r hr) (hreflG s hs),
            reflK_mul_mem_commutator Q hdim hnd hidx (hR1 r hr) (hR1 s hs)⟩
        obtain ⟨g, hgM, hg⟩ := hHrange _ hrs
        have h := hρtr r s g hg.symm
        have hmem : ι (polar Q r s) ^ 2 ∈ K₀ := by
          rw [h]
          exact K₀.mul_mem (htrM g hgM) (K₀.pow_mem (htrM g hgM) _)
        exact mem_of_sq_mem_subfield K₀ hmem
      rintro _ ⟨x, rfl⟩
      have hx : x ∈ K₀.comap ι := by
        rw [hK₁]
        trivial
      exact hx
    rcases hιsub K₀ hsub with hK | hK
    ·
      exfalso
      set S : Set (Matrix (Fin 2) (Fin 2) L) :=
        (fun m : SpecialLinearGroup (Fin 2) L => (m : Matrix (Fin 2) (Fin 2) L)) '' (M : Set _)
        with hS
      have hSmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact ⟨x * y, M.mul_mem hx hy, rfl⟩
      have hStr : ∀ x ∈ S, x.trace ∈ K₀ := by
        rintro _ ⟨x, hx, rfl⟩
        exact htrM x hx
      obtain ⟨P, P', hPP', hP'P, hent⟩ := exists_conj_entries_mem_subfield K₀ S hSmul hStr
        ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ a.2 b.2
        (show (a : Matrix (Fin 2) (Fin 2) L) * a = 1 from
          congrArg (fun x : SpecialLinearGroup (Fin 2) L => (x : Matrix (Fin 2) (Fin 2) L)) ha2)
        (show (b : Matrix (Fin 2) (Fin 2) L) * b = 1 from
          congrArg (fun x : SpecialLinearGroup (Fin 2) L => (x : Matrix (Fin 2) (Fin 2) L)) hb2)
        (fun h => hab (Subtype.ext h))
      let PG : GL (Fin 2) L := ⟨P, P', hPP', hP'P⟩
      obtain ⟨w, hw0, hwfix⟩ := hρfix PG
      refine false_of_irred_of_fixed hdim2 hHirr hw0 fun h hh => ?_
      obtain ⟨g, hgM, rfl⟩ := hHrange h hh
      exact hwfix g fun i j => by
        rw [← hK]
        exact hent _ ⟨g, hgM, rfl⟩ i j
    · exact hK
  have hMne : M ≠ ⊥ := by
    intro hbot
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    refine false_of_irred_of_fixed hdim2 hHirr hw fun h hh => ?_
    obtain ⟨g, hgM, rfl⟩ := hHrange h hh
    rw [hbot, Subgroup.mem_bot] at hgM
    rw [hgM, map_one]
    rfl
  have hMtop := eq_top_of_dickson M hMne h2 hodd htr
  have hΩG : Ω ≤ G := by
    intro x hx
    obtain ⟨g, rfl⟩ : x ∈ ρ.range := hrange ▸ hx
    have hg : g ∈ M := by
      rw [hMtop]
      trivial
    exact hg.1
  have hGeq : G = O := eq_of_index_two_le hΩG hGO hidx fun h => hreflΩ r₀ hr₀ (h (hreflG r₀ hr₀))
  intro g hg
  change g ∈ G
  rw [hGeq]
  exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 hg

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem omega4minus_structure [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : finrank K W = 4) (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hminus : ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → finrank K U ≤ 1) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (ρ : SpecialLinearGroup (Fin 2) L →* (W ≃ₗ[K] W)),
      Nat.card L = Nat.card K ^ 2 ∧ Function.Injective ρ ∧
      ρ.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      ((⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup Q)).index = 2 ∧
      (∀ r : W, r ≠ 0 → reflK Q r ∉
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
      (∀ r s : W, Q r = 1 → Q s = 1 → reflK Q r * reflK Q s ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) ∧
      (∀ c : W ≃ₗ[K] W, (∀ h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆, c * h = h * c) → ∃ a : K, ∀ x, c x = a • x) ∧
      (∀ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q, (∀ h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆, c * h = h * c) → c = 1) := by
  obtain ⟨L, _, _, _, ι, ρ, hL, -, -, hρinj, hρQ, -, -, w₁, hw₁, hw₁fix, hw₁line, hw₁span⟩ :=
    exists_sl2_model Q hdim hnd hminus
  obtain ⟨hrange, hidx⟩ := range_eq_commutator Q hdim hnd hminus hL ρ hρinj hρQ
  have hscalar : ∀ c : W ≃ₗ[K] W, (∀ h ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, c * h = h * c) → ∃ a : K, ∀ x, c x = a • x := by
    intro c hc
    have hcρ : ∀ g x, c (ρ g x) = ρ g (c x) := fun g x =>
      LinearEquiv.congr_fun (hc (ρ g) (hrange ▸ ⟨g, rfl⟩)) x
    obtain ⟨a, ha⟩ := hw₁line (c w₁) fun b => by rw [← hcρ, hw₁fix]
    refine ⟨a, fun x => ?_⟩
    have hext : (c : W →ₗ[K] W) = a • LinearMap.id := by
      refine LinearMap.ext_on_range hw₁span fun g => ?_
      simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hcρ, ha, map_smul]
    exact LinearMap.congr_fun hext x
  refine ⟨L, inferInstance, inferInstance, ρ, hL, hρinj, hrange, hidx,
    fun r hr => reflK_not_mem_commutator Q hdim hnd hr,
    fun r s hr hs => reflK_mul_mem_commutator Q hdim hnd hidx hr hs, hscalar, ?_⟩
  intro c hcO hc
  obtain ⟨a, ha⟩ := hscalar c hc
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨x₀, hx₀⟩ := exists_ne_zero_of_polar_nondeg Q hnd
  have ha1 : a = 1 := scalar_eq_one_of_isometry Q hx₀ (by
    rw [← ha]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hcO x₀)
  ext x
  rw [ha, ha1, one_smul]
  rfl

end CFSG.Quasithin.SimsG4
