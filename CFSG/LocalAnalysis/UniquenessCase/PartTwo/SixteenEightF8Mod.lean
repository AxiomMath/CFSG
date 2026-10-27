module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RepresentationTheory.Submodule
public import CFSG.RankThree.PartTwo.KFacts.KS116LinAbelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix

private theorem s16g_exists_invariant_isCompl {k G V : Type*} [Field k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [NeZero (Nat.card G : k)]
    (ρ : Representation k G V) (U : Submodule k V) (hU : ∀ g : G, ∀ u ∈ U, ρ g u ∈ U) :
    ∃ U' : Submodule k V, IsCompl U U' ∧ ∀ g : G, ∀ u ∈ U', ρ g u ∈ U' := by
  classical
  have hUmem : U ∈ ρ.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro g
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hU g
  let Upack : ρ.invtSubmodule := ⟨U, hUmem⟩
  obtain ⟨q, hq⟩ := MonoidAlgebra.Submodule.exists_isCompl (ρ.mapSubmodule Upack)
  have hcompl_pack : IsCompl Upack (ρ.mapSubmodule.symm q) :=
    (ρ.mapSubmodule.isCompl_iff).2 (by simpa using hq)
  refine ⟨(ρ.mapSubmodule.symm q : ρ.invtSubmodule), ?_, ?_⟩
  · rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    exact ⟨by simpa [Upack] using congrArg Subtype.val hcompl_pack.1,
      by simpa [Upack] using congrArg Subtype.val hcompl_pack.2⟩
  · intro g u hu
    have hmem : ((ρ.mapSubmodule.symm q : ρ.invtSubmodule) : Submodule k V) ∈
        ρ.invtSubmodule := (ρ.mapSubmodule.symm q : ρ.invtSubmodule).2
    rw [Representation.mem_invtSubmodule] at hmem
    exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (ρ g)).1 (hmem g) u hu

private noncomputable def s16g_natRep {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (E : Subgroup (Matrix.GeneralLinearGroup ι K)) : Representation K ↥E (ι → K) :=
  { toFun := fun e =>
      (Matrix.GeneralLinearGroup.toLin ((e : ↥E) : Matrix.GeneralLinearGroup ι K) :
        (ι → K) →ₗ[K] (ι → K))
    map_one' := by
      ext u
      simp
    map_mul' := by
      intro e f
      ext u
      simp }

private theorem s16g_natRep_apply {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (E : Subgroup (Matrix.GeneralLinearGroup ι K)) (e : ↥E) (u : ι → K) :
    s16g_natRep E e u =
      ((e : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u :=
  rfl

theorem s16g_exists_fixing_space {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (E : Subgroup (Matrix.GeneralLinearGroup ι K)) (hE : ∀ x ∈ E, x ^ p = 1)
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hcard : p ^ 3 ≤ Nat.card E) :
    ∃ (B : Subgroup (Matrix.GeneralLinearGroup ι K)) (U : Submodule K (ι → K))
      (g : Matrix.GeneralLinearGroup ι K), B ≤ E ∧ Nat.card B = p ^ 2 ∧ g ∈ E ∧ U ≠ ⊥ ∧
      (∀ h ∈ E, ∀ u ∈ U, (h : Matrix ι ι K) *ᵥ u ∈ U) ∧
      (∀ b ∈ B, ∀ u ∈ U, (b : Matrix ι ι K) *ᵥ u = u) ∧
      (∀ u ∈ U, (g : Matrix ι ι K) *ᵥ u = u → u = 0) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact p.Prime := ⟨hp⟩
  let ρ : Representation K ↥E (ι → K) := s16g_natRep E
  have hρ : ∀ (e : ↥E) (u : ι → K),
      ρ e u = ((e : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u :=
    fun e u => s16g_natRep_apply E e u
  have hEpow : ∀ x : ↥E, x ^ p = 1 := by
    intro x
    exact Subtype.ext (by simpa using hE (x : Matrix.GeneralLinearGroup ι K) x.2)
  have hEp : IsPGroup p ↥E :=
    IsPGroup.of_exponent_dvd_pow (n := 1)
      (by simpa using Monoid.exponent_dvd_of_forall_pow_eq_one hEpow)
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hk3 : 3 ≤ k := by
    have h := hcard
    rw [hk] at h
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h
  have hchar_ne : ringChar K ≠ p := by
    intro h
    apply hpK
    obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hn, h]
    simpa using pow_dvd_pow p (Nat.succ_le_of_lt n.pos)
  have hp_ne : (p : K) ≠ 0 := by
    rw [Ne, ringChar.spec]
    intro hdvd
    exact hchar_ne (((Nat.dvd_prime hp).1 hdvd).resolve_left CharP.ringChar_ne_one)
  have hpK_pow : ((p : K) ^ k) ≠ 0 := pow_ne_zero k hp_ne
  have hne : (Nat.card ↥E : K) ≠ 0 := by
    rw [hk, Nat.cast_pow]
    exact hpK_pow
  haveI : NeZero (Nat.card ↥E : K) := ⟨hne⟩
  have hPtop : (∀ e : ↥E, ∀ u ∈ (⊤ : Submodule K (ι → K)),
        ρ e u ∈ (⊤ : Submodule K (ι → K))) ∧
      ∃ e : ↥E, ∃ u ∈ (⊤ : Submodule K (ι → K)), ρ e u ≠ u := by
    refine ⟨fun _ _ _ => Submodule.mem_top, ?_⟩
    have hcard_gt : 1 < Nat.card ↥E := by
      calc 1 < p ^ 3 := one_lt_pow' hp.one_lt (by norm_num : (3 : ℕ) ≠ 0)
        _ ≤ Nat.card ↥E := hcard
    haveI : Nontrivial ↥E := Finite.one_lt_card_iff_nontrivial.mp hcard_gt
    obtain ⟨e, he⟩ := exists_ne (1 : ↥E)
    have hρinj : Function.Injective ρ := by
      intro x y hxy
      have h1 : Matrix.GeneralLinearGroup.toLin ((x : ↥E) : Matrix.GeneralLinearGroup ι K) =
          Matrix.GeneralLinearGroup.toLin ((y : ↥E) : Matrix.GeneralLinearGroup ι K) :=
        Units.ext hxy
      have h2 : ((x : ↥E) : Matrix.GeneralLinearGroup ι K) =
          ((y : ↥E) : Matrix.GeneralLinearGroup ι K) :=
        (Matrix.GeneralLinearGroup.toLin).injective h1
      exact Subtype.ext h2
    have hρe_ne : ρ e ≠ 1 := by
      intro h
      exact he (hρinj (by rw [h, map_one]))
    have : ∃ u : ι → K, ρ e u ≠ u := by
      by_contra hcon
      apply hρe_ne
      apply LinearMap.ext
      intro u
      exact not_not.mp (not_exists.mp hcon u)
    obtain ⟨u, hu⟩ := this
    exact ⟨e, u, Submodule.mem_top, hu⟩
  have hex : ∃ n, ∃ V : Submodule K (ι → K),
      (∀ e : ↥E, ∀ u ∈ V, ρ e u ∈ V) ∧
      (∃ e : ↥E, ∃ u ∈ V, ρ e u ≠ u) ∧ Module.finrank K V = n :=
    ⟨_, ⊤, hPtop.1, hPtop.2, rfl⟩
  obtain ⟨U, hUinv, hUmove, hUn⟩ := Nat.find_spec hex
  have hUmin : ∀ V : Submodule K (ι → K),
      (∀ e : ↥E, ∀ u ∈ V, ρ e u ∈ V) →
      (∃ e : ↥E, ∃ u ∈ V, ρ e u ≠ u) → Module.finrank K U ≤ Module.finrank K V := by
    intro V hVinv hVmove
    rw [hUn]
    exact Nat.find_min' hex ⟨V, hVinv, hVmove, rfl⟩
  have hUne : U ≠ ⊥ := by
    intro hbot
    obtain ⟨e, u, hu, hne'⟩ := hUmove
    rw [hbot, Submodule.mem_bot] at hu
    rw [hu] at hne'
    exact hne' (map_zero (ρ e))
  have hTrivOfLt : ∀ V : Submodule K (ι → K),
      (∀ e : ↥E, ∀ u ∈ V, ρ e u ∈ V) →
      Module.finrank K V < Module.finrank K U → ∀ e : ↥E, ∀ u ∈ V, ρ e u = u := by
    intro V hVinv hlt e u hu
    by_contra hne'
    have := hUmin V hVinv ⟨e, u, hu, hne'⟩
    omega
  have hIrred : ∀ V : Submodule K (ι → K), V ≤ U →
      (∀ e : ↥E, ∀ u ∈ V, ρ e u ∈ V) → V = ⊥ ∨ V = U := by
    intro V hVU hVinv
    by_cases hVbot : V = ⊥
    · exact Or.inl hVbot
    right
    by_contra hVne
    have hVlt : V < U := lt_of_le_of_ne hVU hVne
    obtain ⟨V', hCompl, hV'inv⟩ := s16g_exists_invariant_isCompl ρ V hVinv
    have hVU' : V ⊔ (V' ⊓ U) = U := by
      rw [← sup_inf_assoc_of_le V' hVU, hCompl.sup_eq_top, top_inf_eq]
    have htrivV : ∀ e : ↥E, ∀ u ∈ V, ρ e u = u :=
      hTrivOfLt V hVinv (Submodule.finrank_lt_finrank_of_lt hVlt)
    have hV''inv : ∀ e : ↥E, ∀ u ∈ V' ⊓ U, ρ e u ∈ V' ⊓ U :=
      fun e u hu => ⟨hV'inv e u hu.1, hUinv e u hu.2⟩
    have hV''lt : V' ⊓ U < U := by
      refine lt_of_le_of_ne inf_le_right ?_
      intro heq
      apply hVbot
      calc V = V ⊓ U := (inf_eq_left.mpr hVU).symm
        _ = V ⊓ (V' ⊓ U) := by rw [heq]
        _ = (V ⊓ V') ⊓ U := by rw [inf_assoc]
        _ = ⊥ := by rw [hCompl.inf_eq_bot, bot_inf_eq]
    have htrivV'' : ∀ e : ↥E, ∀ u ∈ V' ⊓ U, ρ e u = u :=
      hTrivOfLt (V' ⊓ U) hV''inv (Submodule.finrank_lt_finrank_of_lt hV''lt)
    obtain ⟨e, u, hu, hne'⟩ := hUmove
    have hu' : u ∈ V ⊔ (V' ⊓ U) := by rw [hVU']; exact hu
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu'
    apply hne'
    rw [← hab, map_add, htrivV e a ha, htrivV'' e b hb]
  let ρU : Representation K ↥E ↥U :=
    { toFun := fun e => LinearMap.restrict (ρ e) (hUinv e)
      map_one' := by
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        simp [LinearMap.restrict_apply]
      map_mul' := by
        intro e f
        apply LinearMap.ext
        intro u
        apply Subtype.ext
        simp [LinearMap.restrict_apply] }
  have hsimple : ∀ W₁ : Submodule K ↥U,
      (∀ b ∈ (⊤ : Subgroup ↥E), W₁ ≤ W₁.comap (ρU b)) → W₁ = ⊥ ∨ W₁ = ⊤ := by
    intro W₁ hW₁
    have hmapinv : ∀ e : ↥E, ∀ u ∈ W₁.map U.subtype, ρ e u ∈ W₁.map U.subtype := by
      rintro e _ ⟨w, hw, rfl⟩
      have hmem : ρU e w ∈ W₁ := hW₁ e trivial hw
      exact ⟨ρU e w, hmem, rfl⟩
    have hmaple : W₁.map U.subtype ≤ U := Submodule.map_subtype_le _ _
    rcases hIrred (W₁.map U.subtype) hmaple hmapinv with h | h
    · left
      rw [← Submodule.map_bot U.subtype] at h
      exact Submodule.map_injective_of_injective U.injective_subtype h
    · right
      have h2 : W₁.map U.subtype = (⊤ : Submodule K ↥U).map U.subtype := by
        rw [h, Submodule.map_top, Submodule.range_subtype]
      exact Submodule.map_injective_of_injective U.injective_subtype h2
  haveI : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.mpr hUne
  have hcyc : IsCyclic ((⊤ : Subgroup ↥E).map ρU.toHomUnits) :=
    CFSG.RankThree.PartTwo.KFacts.NDC.isCyclic_image_of_simple_abelian
      (ρ := ρU) (B := ⊤) (by
        intro b _ b' _
        have hbb : b * b' = b' * b := Subtype.ext (hc b b.2 b' b'.2)
        simpa only [map_mul] using congrArg ρU hbb) hsimple
  have hcyc' : IsCyclic ρU.toHomUnits.range := by
    rw [MonoidHom.range_eq_map]
    exact hcyc
  have hrange_dvd : Nat.card ρU.toHomUnits.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    obtain ⟨_, e, rfl⟩ := x
    refine Subtype.ext ?_
    show (ρU.toHomUnits e) ^ p = 1
    rw [← map_pow, hEpow e, map_one]
  have hrange_ne_one : Nat.card ρU.toHomUnits.range ≠ 1 := by
    intro h1
    obtain ⟨e, u, hu, hne'⟩ := hUmove
    have he_mem : ρU.toHomUnits e ∈ ρU.toHomUnits.range := ⟨e, rfl⟩
    rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at he_mem
    have hρUe : ρU e = 1 := by
      have h := congrArg (fun x : (↥U →ₗ[K] ↥U)ˣ => (x : ↥U →ₗ[K] ↥U)) he_mem
      simpa using h
    have hfix : ρU e ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hρUe, Module.End.one_apply]
    exact hne' (Subtype.ext_iff.mp hfix)
  have hrange : Nat.card ρU.toHomUnits.range = p :=
    ((Nat.dvd_prime hp).mp hrange_dvd).resolve_left hrange_ne_one
  have hker_card : Nat.card ρU.toHomUnits.ker = p ^ (k - 1) := by
    have h := Subgroup.card_ker_mul_card_range ρU.toHomUnits
    rw [hrange, hk] at h
    have hk1 : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rw [hk1] at h
    exact Nat.eq_of_mul_eq_mul_right hp.pos h
  have hdvd : p ^ 2 ∣ Nat.card ρU.toHomUnits.ker := by
    rw [hker_card]
    exact pow_dvd_pow p (by omega : 2 ≤ k - 1)
  obtain ⟨K₀, hK₀card⟩ := Sylow.exists_subgroup_card_pow_prime p (n := 2) hdvd
  let B : Subgroup (Matrix.GeneralLinearGroup ι K) :=
    K₀.map (E.subtype.comp ρU.toHomUnits.ker.subtype)
  have hBle : B ≤ E := by
    intro b hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨x, -, rfl⟩ := hb
    exact (x : ↥E).2
  have hBcard : Nat.card B = p ^ 2 := by
    have hinj : Function.Injective (E.subtype.comp ρU.toHomUnits.ker.subtype) :=
      fun a b hab => Subtype.ext (Subtype.ext hab)
    change Nat.card (K₀.map (E.subtype.comp ρU.toHomUnits.ker.subtype)) = p ^ 2
    rw [Subgroup.card_map_of_injective hinj, hK₀card]
  have hBfix : ∀ b ∈ B, ∀ u ∈ U, (b : Matrix ι ι K) *ᵥ u = u := by
    intro b hb u hu
    rw [Subgroup.mem_map] at hb
    obtain ⟨x, hxK, rfl⟩ := hb
    have hxker : ρU.toHomUnits (x : ↥E) = 1 := MonoidHom.mem_ker.mp x.2
    have hρUx : ρU x = 1 := by
      have h := congrArg (fun y : (↥U →ₗ[K] ↥U)ˣ => (y : ↥U →ₗ[K] ↥U)) hxker
      simpa using h
    have hfix : ρU x ⟨u, hu⟩ = ⟨u, hu⟩ := by rw [hρUx, Module.End.one_apply]
    have hρu : ρ (x : ↥E) u = u := Subtype.ext_iff.mp hfix
    change (((x : ↥E) : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u = u
    rw [← hρ]
    exact hρu
  have hker_index : ρU.toHomUnits.ker.index = p := by
    rw [Subgroup.index_ker, hrange]
  have hker_ne_top : ρU.toHomUnits.ker ≠ ⊤ := by
    intro htop
    have h1 : ρU.toHomUnits.ker.index = 1 := by rw [htop, Subgroup.index_top]
    rw [hker_index] at h1
    exact hp.ne_one h1
  have hnotle : ¬ (⊤ : Subgroup ↥E) ≤ ρU.toHomUnits.ker :=
    fun hle => hker_ne_top (top_le_iff.mp hle)
  obtain ⟨g, -, hgker⟩ := Set.not_subset.mp hnotle
  let g' : Matrix.GeneralLinearGroup ι K := ((g : ↥E) : Matrix.GeneralLinearGroup ι K)
  have hgfree : ∀ u ∈ U, (g' : Matrix ι ι K) *ᵥ u = u → u = 0 := by
    intro u hu hfix
    have hgfix : ρ g u = u := by
      rw [hρ]
      exact hfix
    let C : Submodule K (ι → K) := (LinearMap.ker (ρ g - 1)) ⊓ U
    have hCinv : ∀ e : ↥E, ∀ u ∈ C, ρ e u ∈ C := by
      intro e u hu
      refine ⟨?_, hUinv e u hu.2⟩
      have hgu : ρ g u = u := by
        have h := LinearMap.mem_ker.mp hu.1
        rw [LinearMap.sub_apply, Module.End.one_apply] at h
        exact sub_eq_zero.mp h
      have hge : ρ g * ρ e = ρ e * ρ g := by
        rw [← map_mul, ← map_mul]
        exact congrArg ρ (Subtype.ext (hc g g.2 e e.2))
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      calc ρ g (ρ e u) = (ρ g * ρ e) u := rfl
        _ = (ρ e * ρ g) u := by rw [hge]
        _ = ρ e (ρ g u) := rfl
        _ = ρ e u := by rw [hgu]
    have hCbot_or : C = ⊥ ∨ C = U := hIrred C inf_le_right hCinv
    have hCbot : C = ⊥ := by
      rcases hCbot_or with h | h
      · exact h
      · exfalso
        apply hgker
        refine MonoidHom.mem_ker.mpr ?_
        apply Units.ext
        apply LinearMap.ext
        intro w
        have hwC : (w : ι → K) ∈ C := by
          rw [h]
          exact w.2
        have hwfix : ρ g (w : ι → K) = (w : ι → K) := by
          have h' := LinearMap.mem_ker.mp hwC.1
          rw [LinearMap.sub_apply, Module.End.one_apply] at h'
          exact sub_eq_zero.mp h'
        exact Subtype.ext (show ((ρU g) w : ι → K) = (w : ι → K) from hwfix)
    have huC : u ∈ C := by
      refine ⟨?_, hu⟩
      refine LinearMap.mem_ker.mpr ?_
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact hgfix
    rw [hCbot, Submodule.mem_bot] at huC
    exact huC
  refine ⟨B, U, g', hBle, hBcard, (g : ↥E).2, hUne, ?_, hBfix, hgfree⟩
  intro h hh u hu
  simpa [hρ] using hUinv ⟨h, hh⟩ u hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
