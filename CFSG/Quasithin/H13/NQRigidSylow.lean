module

public import CFSG.Quasithin.H13.NQRigidBridge
public import CFSG.Quasithin.H13.NQSetupOrbitTwo
public import CFSG.Quasithin.SteinbergCBTwoNaturalOrbits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt5
public import CFSG.Quasithin.SteinbergCBIndexTwoCentralizer
public import CFSG.Quasithin.H13.NQSetupOddCore
public import CFSG.Quasithin.H13.NQRigidSeed

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open Equiv
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct permU)
open CFSG.QuasithinUnique.Setup.Offender (commGL)
open CFSG.Quasithin.H13.NQSetup (ExplicitNaturalFour ExplicitDeletedFive
  ExplicitNaturalThreeDouble ExplicitNaturalThreeExtension conjGL)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped IsMulCommutative Pointwise

section Orbits

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem card_orbit_map_conjGL {F : Type*} [AddCommGroup F] [Module (ZMod 2) F]
    (ψ : E ≃ₗ[ZMod 2] F) (H : Subgroup (E ≃ₗ[ZMod 2] E)) (e : E) :
    Nat.card (MulAction.orbit (H.map (conjGL ψ).toMonoidHom) (ψ e)) =
      Nat.card (MulAction.orbit H e) := by
  have hset : MulAction.orbit (H.map (conjGL ψ).toMonoidHom) (ψ e) =
      ψ '' MulAction.orbit H e := by
    ext y
    simp only [MulAction.mem_orbit_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨_, h, hh, rfl⟩, rfl⟩
      exact ⟨h e, ⟨⟨h, hh⟩, rfl⟩, by
        change ψ (h e) = conjGL ψ h (ψ e)
        rw [NQSetup.conjGL_apply, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨_, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
      refine ⟨⟨conjGL ψ h, h, hh, rfl⟩, ?_⟩
      change conjGL ψ h (ψ e) = ψ (h e)
      rw [NQSetup.conjGL_apply, LinearEquiv.symm_apply_apply]
  rw [hset, Nat.card_image_of_injective ψ.injective]

theorem not_four_dvd_card_orbit_of_double [FiniteDimensional (ZMod 2) E]
    {S H : Subgroup (E ≃ₗ[ZMod 2] E)} (hSH : S ≤ H)
    (hHN : H ≤ normalizer (S : Set (E ≃ₗ[ZMod 2] E))) (hc : ExplicitNaturalThreeDouble S)
    (e : E) : ¬ 4 ∣ Nat.card (MulAction.orbit H e) := by
  classical
  obtain ⟨V, _, _, hV, β, ψ, hψ⟩ := hc
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have hdiag : ∀ s : S, conjGL ψ (s : E ≃ₗ[ZMod 2] E) = SteinbergCB.diagHom (β s) := by
    intro s
    refine LinearEquiv.ext fun x => ?_
    rw [NQSetup.conjGL_apply, hψ, LinearEquiv.apply_symm_apply]
    rfl
  set H' := H.map (conjGL ψ).toMonoidHom with hH'
  have hSH' : (SteinbergCB.diagHom (V := V)).range ≤ H' := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨s, rfl⟩ := β.surjective g
    exact ⟨s, hSH s.2, hdiag s⟩
  have hHN' : H' ≤ normalizer ((SteinbergCB.diagHom (V := V)).range :
      Set ((V × V) ≃ₗ[ZMod 2] (V × V))) := by
    rintro _ ⟨h, hh, rfl⟩
    rw [mem_normalizer_iff]
    intro d
    have hmemS : ∀ g : E ≃ₗ[ZMod 2] E, g ∈ S →
        conjGL ψ g ∈ (SteinbergCB.diagHom (V := V)).range := fun g hg =>
      ⟨β ⟨g, hg⟩, (hdiag ⟨g, hg⟩).symm⟩
    have hmemS' : ∀ g : E ≃ₗ[ZMod 2] E,
        conjGL ψ g ∈ (SteinbergCB.diagHom (V := V)).range → g ∈ S := by
      rintro g ⟨a, ha⟩
      obtain ⟨s, hs⟩ := β.surjective a
      have : g = s := by
        apply (conjGL ψ).injective
        rw [hdiag, hs, ha]
      rw [this]
      exact s.2
    constructor
    · intro hd
      obtain ⟨g, rfl⟩ := (conjGL ψ).surjective d
      have hg := hmemS' g hd
      have h1 := (mem_normalizer_iff.mp (hHN hh) g).mp hg
      have h2 := hmemS _ h1
      simpa [map_mul, map_inv] using h2
    · intro hd
      obtain ⟨g, rfl⟩ := (conjGL ψ).surjective d
      have h1 : h * g * h⁻¹ ∈ S := hmemS' _ (by simpa [map_mul, map_inv] using hd)
      exact hmemS g ((mem_normalizer_iff.mp (hHN hh) g).mpr h1)
  have h1 := (SteinbergCB.nq_two_natural_three_space_normalizer_orbits hV hSH' hHN' (ψ e)).2
  rwa [card_orbit_map_conjGL] at h1


@[expose] noncomputable def conjUnits {F : Type*} [AddCommMonoid F] [Module (ZMod 2) F]
    (ψ : E ≃ₗ[ZMod 2] F) : (E ≃ₗ[ZMod 2] E) →* (Module.End (ZMod 2) F)ˣ where
  toFun g := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) F).symm
    (ψ.symm.trans (g.trans ψ))
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    change ψ (ψ.symm x) = x
    exact ψ.apply_symm_apply x
  map_mul' g h := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    change ψ (g (h (ψ.symm x))) = ψ (g (ψ.symm (ψ (h (ψ.symm x)))))
    rw [LinearEquiv.symm_apply_apply]

theorem conjUnits_val_apply {F : Type*} [AddCommMonoid F] [Module (ZMod 2) F]
    (ψ : E ≃ₗ[ZMod 2] F) (g : E ≃ₗ[ZMod 2] E) (x : F) :
    (conjUnits ψ g).val x = ψ (g (ψ.symm x)) := rfl

theorem not_four_dvd_card_orbit_of_deleted {S H : Subgroup (E ≃ₗ[ZMod 2] E)} (hSH : S ≤ H)
    (hHN : H ≤ normalizer (S : Set (E ≃ₗ[ZMod 2] E))) (hb : ExplicitDeletedFive S) (e : E) :
    ¬ 4 ∣ Nat.card (MulAction.orbit H e) := by
  classical
  obtain ⟨Ω, _, _, hΩ, β, ψ, hψ⟩ := hb
  have hperm : ∀ s : S, conjUnits ψ (s : E ≃ₗ[ZMod 2] E) = permU (β s : Perm Ω) := by
    intro s
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [conjUnits_val_apply, hψ, LinearEquiv.apply_symm_apply]
    rfl
  set H'' := H.map (conjUnits ψ) with hH''
  have hSH'' : ∀ σ ∈ alternatingGroup Ω, permU σ ∈ H'' := by
    intro σ hσ
    obtain ⟨s, hs⟩ := β.surjective ⟨σ, hσ⟩
    refine ⟨s, hSH s.2, ?_⟩
    rw [hperm, hs]
  have hHN'' : ∀ h ∈ H'', ∀ σ ∈ alternatingGroup Ω, ∃ σ' ∈ alternatingGroup Ω,
      h * permU σ * h⁻¹ = permU σ' := by
    rintro _ ⟨h, hh, rfl⟩ σ hσ
    obtain ⟨s, hs⟩ := β.surjective ⟨σ, hσ⟩
    have hconj : h * (s : E ≃ₗ[ZMod 2] E) * h⁻¹ ∈ S :=
      (mem_normalizer_iff.mp (hHN hh) s).mp s.2
    refine ⟨(β ⟨_, hconj⟩ : Perm Ω), (β ⟨_, hconj⟩).2, ?_⟩
    have h1 : permU σ = conjUnits ψ (s : E ≃ₗ[ZMod 2] E) := by rw [hperm, hs]
    rw [h1, ← hperm ⟨_, hconj⟩, map_mul, map_mul, map_inv]
  have h1 := (CFSG.QuasithinUnique.Setup.SL2Modules.alternating_five_deleted_normalizer_orbits hΩ
    H'' hSH'' hHN'').2.2.2.2 (ψ e)
  have hset : {y : evenWeight Ω | ∃ g ∈ H'', g.val (ψ e) = y} = ψ '' MulAction.orbit H e := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      exact ⟨h e, ⟨⟨h, hh⟩, rfl⟩, by rw [conjUnits_val_apply, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨_, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
      exact ⟨conjUnits ψ h, ⟨h, hh, rfl⟩, by
        rw [conjUnits_val_apply, LinearEquiv.symm_apply_apply]; rfl⟩
  have hcard : Nat.card {y : evenWeight Ω // ∃ g ∈ H'', g.val (ψ e) = y} =
      Nat.card (MulAction.orbit H e) := by
    change Nat.card ↥{y : evenWeight Ω | ∃ g ∈ H'', g.val (ψ e) = y} = _
    rw [hset, Nat.card_image_of_injective ψ.injective]
  rwa [hcard] at h1

end Orbits

section QTNQOrbits

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

theorem qtnqS_le_range_and_normalizer (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)] :
    qtnqS h ≤ (qtnqAction h).range ∧
      (qtnqAction h).range ≤ normalizer ((qtnqS h : Set (Additive (qtnqU L M) ≃ₗ[ZMod 2]
        Additive (qtnqU L M)))) := by
  refine ⟨map_le_range _ _, ?_⟩
  have hLn : (L.subgroupOf M).Normal :=
    (normal_subgroupOf_iff_le_normalizer h.l_le).mpr h.eq_normalizer.le
  have htop : normalizer ((L.subgroupOf M : Subgroup M) : Set M) = ⊤ :=
    normalizer_eq_top_iff.mpr hLn
  have h1 := le_normalizer_map (H := L.subgroupOf M) (qtnqAction h)
  rw [htop, ← MonoidHom.range_eq_map] at h1
  exact h1

theorem not_four_dvd_card_orbit_qtnq (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    (hmod : QTNQExplicitModule L M) (e : Additive (qtnqU L M)) :
    ¬ 4 ∣ Nat.card (MulAction.orbit (qtnqAction h).range e) := by
  have : Finite (Additive (qtnqU L M)) := inferInstanceAs (Finite (qtnqU L M))
  have : FiniteDimensional (ZMod 2) (Additive (qtnqU L M)) := Module.Finite.of_finite
  obtain ⟨hSH, hHN⟩ := qtnqS_le_range_and_normalizer h
  rcases explicitModule_of_qtnqExplicitModule h hmod with ha | hb | hc | hc
  · exact NQSetup.nq_natural_trivial_kernel_extension_orbit_two_bound _ _ hSH hHN
      (commGL_qtnqS_eq_top h) (Or.inl ha) e
  · exact not_four_dvd_card_orbit_of_deleted hSH hHN hb e
  · exact not_four_dvd_card_orbit_of_double hSH hHN hc e
  · exact NQSetup.nq_natural_trivial_kernel_extension_orbit_two_bound _ _ hSH hHN
      (commGL_qtnqS_eq_top h) (Or.inr hc) e

theorem relIndex_centralizer_eq_card_orbit (h : QTNQ T L M) [IsElementaryAbelian 2 (qtnqU L M)]
    {u : G} (hu : u ∈ qtnqU L M) :
    (M ⊓ centralizer {u}).relIndex M =
      Nat.card (MulAction.orbit (qtnqAction h).range (Additive.ofMul (⟨u, hu⟩ : qtnqU L M))) := by
  set e := Additive.ofMul (⟨u, hu⟩ : qtnqU L M) with he
  have hstab : (M ⊓ centralizer {u}).subgroupOf M =
      (MulAction.stabilizer (qtnqAction h).range e).comap (qtnqAction h).rangeRestrict := by
    ext m
    rw [mem_subgroupOf, mem_comap, MulAction.mem_stabilizer_iff]
    change (m : G) ∈ M ⊓ centralizer {u} ↔ qtnqAction h m e = e
    constructor
    · intro hm
      have hmu : (m : G) * u * (m : G)⁻¹ = u := by
        rw [(mem_centralizer_singleton_iff.mp (mem_inf.mp hm).2), mul_inv_cancel_right]
      apply Additive.toMul.injective
      exact Subtype.ext hmu
    · intro hm
      have hmu : (m : G) * u * (m : G)⁻¹ = u := congrArg (fun x : Additive (qtnqU L M) =>
        ((x.toMul : qtnqU L M) : G)) hm
      refine mem_inf.mpr ⟨m.2, mem_centralizer_singleton_iff.mpr ?_⟩
      calc (m : G) * u = (m : G) * u * (m : G)⁻¹ * m := by group
        _ = u * m := by rw [hmu]
  rw [relIndex, hstab, Subgroup.index_comap_of_surjective _
    (MonoidHom.rangeRestrict_surjective (qtnqAction h)), MulAction.index_stabilizer,
    Nat.card_coe_set_eq]

theorem not_four_dvd_relIndex_centralizer (h : QTNQ T L M) (hmod : QTNQExplicitModule L M)
    {u : G} (hu : u ∈ qtnqU L M) : ¬ 4 ∣ (M ⊓ centralizer {u}).relIndex M := by
  have := qtnqU_isElementaryAbelian h
  rw [relIndex_centralizer_eq_card_orbit h hu]
  exact not_four_dvd_card_orbit_qtnq h hmod _

end QTNQOrbits

section Sylow

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

omit [Finite G] in
theorem conj_inv_smul_eq_conjugate (M : Subgroup G) (g : G) :
    MulAut.conj g⁻¹ • M = CFSG.conjugate M g := by
  ext x
  rw [mem_pointwise_smul_iff_inv_smul_mem, mem_conjugate_iff, MulAut.smul_def, ← map_inv,
    inv_inv, MulAut.conj_apply]

theorem exists_conj_le_of_isPGroup {P M T : Subgroup G} (hPM : P ≤ M) (hP : IsPGroup 2 P)
    (hT : IsSylowOf 2 T M) : ∃ m ∈ M, ∀ x ∈ P, m⁻¹ * x * m ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP' : IsPGroup 2 (P.subgroupOf M) := hP.comap_subtype
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  obtain ⟨T', hT'⟩ := hT.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M S' T'
  refine ⟨(g⁻¹ : M), (g⁻¹ : M).2, fun x hx => ?_⟩
  have hxS : (⟨x, hPM hx⟩ : M) ∈ (S' : Subgroup M) := hS' hx
  have h1 : g * ⟨x, hPM hx⟩ * g⁻¹ ∈ (T' : Subgroup M) := by
    rw [← hg]
    change g * ⟨x, hPM hx⟩ * g⁻¹ ∈ MulAut.conj g • (S' : Subgroup M)
    exact ⟨_, hxS, rfl⟩
  rw [hT'] at h1
  simpa [mem_subgroupOf] using h1

theorem explicit_module_ambient_centralizer_Sylow_position
    (h : QTNQ T L M)
    (hmod : QTNQExplicitModule L M) :
    (∀ u ∈ qtnqU L M, ¬ 4 ∣ (M ⊓ centralizer {u}).relIndex M) ∧
    ∀ u ∈ qtnqU L M, u ≠ 1 → ∃ m ∈ M,
      IsSylowOf 2 (T ⊓ centralizer {m⁻¹ * u * m}) (M ⊓ centralizer {m⁻¹ * u * m}) ∧
      (T ⊓ centralizer {m⁻¹ * u * m}).relIndex T ≤ 2 ∧
      IsSylowOf 2 (T ⊓ centralizer {m⁻¹ * u * m}) (centralizer {m⁻¹ * u * m}) ∧
      ((T ⊓ centralizer {m⁻¹ * u * m}).relIndex T = 1 → centralizer {u} ≤ M) ∧
      (¬ centralizer {u} ≤ M → (T ⊓ centralizer {m⁻¹ * u * m}).relIndex T = 2) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 := fun u hu => not_four_dvd_relIndex_centralizer h hmod (u := u) hu
  refine ⟨h4, fun u hu hu1 => ?_⟩
  have hUM : M ≤ normalizer (qtnqU L M : Set G) := le_normalizer_qtnqU h
  have hUel := qtnqU_isElementaryAbelian h
  have hTM : IsSylowOf 2 T M := isSylowOf_of_qtnq h
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ centralizer {u})
  obtain ⟨m, hm, hmP⟩ := exists_conj_le_of_isPGroup (hP.le.trans inf_le_left) hP.isPGroup hTM
  set v := m⁻¹ * u * m with hv
  have hvU : v ∈ qtnqU L M := by
    have := (mem_normalizer_iff.mp (hUM (M.inv_mem hm)) u).mp hu
    simpa [hv] using this
  have hv1 : v ≠ 1 := by
    intro h1
    apply hu1
    have : u = m * v * m⁻¹ := by rw [hv]; group
    rw [this, h1]
    group
  set Q := T ⊓ centralizer {v} with hQ
  set C := M ⊓ centralizer {v} with hC
  set Pm := P.map (MulAut.conj m⁻¹).toMonoidHom with hPm
  have hconjC : ∀ x, x ∈ M ⊓ centralizer {u} → m⁻¹ * x * m ∈ C := by
    intro x hx
    obtain ⟨hxM, hxC⟩ := mem_inf.mp hx
    refine mem_inf.mpr ⟨M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm, ?_⟩
    rw [mem_centralizer_singleton_iff] at hxC ⊢
    rw [hv]
    calc m⁻¹ * x * m * (m⁻¹ * u * m) = m⁻¹ * (x * u) * m := by group
      _ = m⁻¹ * (u * x) * m := by rw [hxC]
      _ = m⁻¹ * u * m * (m⁻¹ * x * m) := by group
  have hCcard : Nat.card C = Nat.card ↥(M ⊓ centralizer {u}) := by
    have hCeq : C = (M ⊓ centralizer {u}).map (MulAut.conj m⁻¹).toMonoidHom := by
      ext y
      constructor
      · intro hy
        refine ⟨m * y * m⁻¹, ?_, by simp [mul_assoc]⟩
        have h1 := hconjC (m * y * m⁻¹)
        obtain ⟨hyM, hyC⟩ := mem_inf.mp hy
        refine mem_inf.mpr ⟨M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm), ?_⟩
        rw [mem_centralizer_singleton_iff] at hyC ⊢
        have hu' : u = m * v * m⁻¹ := by rw [hv]; group
        rw [hu']
        calc m * y * m⁻¹ * (m * v * m⁻¹) = m * (y * v) * m⁻¹ := by group
          _ = m * (v * y) * m⁻¹ := by rw [hyC]
          _ = m * v * m⁻¹ * (m * y * m⁻¹) := by group
      · rintro ⟨x, hx, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hconjC x hx
    rw [hCeq, card_map_of_injective (MulAut.conj m⁻¹).injective]
  have hPmC : IsSylowOf 2 Pm C := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hconjC x (hP.le hx)
    · rw [card_map_of_injective (MulAut.conj m⁻¹).injective, hP.card_eq, hCcard]
  have hPmQ : Pm ≤ Q := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : m⁻¹ * x * m ∈ C := hconjC x (hP.le hx)
    change m⁻¹ * x * m⁻¹⁻¹ ∈ T ⊓ centralizer {v}
    rw [inv_inv]
    exact mem_inf.mpr ⟨hmP x hx, (mem_inf.mp h1).2⟩
  have hQC : Q ≤ C := inf_le_inf_right _ h.t_le
  have hQ2 : IsPGroup 2 Q := h.sylow.1.to_le inf_le_left
  have hQeq : Q = Pm := hPmC.eq_of_le hPmQ hQC hQ2
  have hQsyl : IsSylowOf 2 Q C := hQeq ▸ hPmC
  have hQT : Q ≤ T := inf_le_left
  have hTQ : Q.relIndex T ≤ 2 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.sylow.1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (hn ▸ (Q.relIndex_dvd_card (K := T)))
    have hodd1 : ¬ 2 ∣ T.relIndex M := (CFSG.ABGLocalTools.isSylowOf_iff.mp hTM).2.2
    have hodd2 : ¬ 2 ∣ Q.relIndex C := (CFSG.ABGLocalTools.isSylowOf_iff.mp hQsyl).2.2
    have heq : Q.relIndex T * T.relIndex M = Q.relIndex C * C.relIndex M := by
      rw [relIndex_mul_relIndex Q T M hQT h.t_le, relIndex_mul_relIndex Q C M hQC inf_le_left]
    have hdvd : 2 ^ k ∣ C.relIndex M := by
      have h1 : 2 ^ k ∣ Q.relIndex C * C.relIndex M := by
        rw [← heq, ← hk]
        exact dvd_mul_right _ _
      refine (Nat.Coprime.dvd_of_dvd_mul_left ?_ h1)
      exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd2)
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      apply h4 v hvU
      exact (pow_dvd_pow 2 hk2).trans hdvd
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 2 := rfl
  set T' : Sylow 2 G := h.sylow.1.toSylow h.sylow.2 with hT'
  have hT'T : (T' : Subgroup G) = T := IsPGroup.toSylow_coe h.sylow.1 h.sylow.2
  have hvT : v ∈ T := NQSetup.qtnqU_le_t h hvU
  have hv2 : orderOf v = 2 := by
    have hsq : v ^ 2 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian v hvU
    exact orderOf_eq_prime hsq hv1
  have hZ : ∀ z ∈ (T' : Subgroup G), (∀ t ∈ (T' : Subgroup G), t * z = z * t) →
      orderOf z = 2 → centralizer {z} ≤ M := by
    intro z hzT hzc hz2
    rw [hT'T] at hzT hzc
    have hzZ : z ∈ quasithinOmegaOneCenter T :=
      QuasithinUnique.mem_quasithinOmegaOneCenter_iff.mpr ⟨hzT,
        mem_centralizer_iff.mpr fun t ht => hzc t ht, by rw [← hz2]; exact pow_orderOf_eq_one z⟩
    refine centralizer_le_of_mem_omegaOneCenter h hzZ fun hz1 => ?_
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  obtain ⟨-, -, -, X, -, -, -, -, -, -, -, -, -, -, hconj⟩ :=
    explicit_module_centralizer_irreducibility h hmod
  have hMg : ∀ g : G, M ⊓ centralizer {v} ≤ MulAut.conj g⁻¹ • M → MulAut.conj g⁻¹ • M = M := by
    intro g hg
    rw [conj_inv_smul_eq_conjugate] at hg ⊢
    exact (hconj v hvU g hg).2
  have hQsyl' : CFSG.QuasithinUnique.IsSylowTwoOf ((T' : Subgroup G) ⊓ centralizer {v})
      (M ⊓ centralizer {v}) := by
    rw [hT'T]
    exact CFSG.ABGLocalTools.isSylowOf_iff.mp hQsyl
  obtain ⟨hsylG, hQTle⟩ := SteinbergCB.nq_index_two_centralizer_Sylow_transfer T'
    (hT'T ▸ h.t_le) (hT'T ▸ hvT) hv2 hQsyl' (by rw [hT'T]; exact hTQ) hZ hMg
  rw [hT'T] at hsylG hQTle
  have hsylG' : IsSylowOf 2 Q (centralizer {v}) := CFSG.ABGLocalTools.isSylowOf_iff.mpr hsylG
  have hone : Q.relIndex T = 1 → centralizer {u} ≤ M := by
    intro h1
    have hQTeq : Q = T := le_antisymm hQT (relIndex_eq_one.mp h1)
    have hCv := hQTle hQTeq
    intro x hx
    have h2 : m⁻¹ * x * m ∈ centralizer {v} := by
      rw [mem_centralizer_singleton_iff] at hx ⊢
      rw [hv]
      calc m⁻¹ * x * m * (m⁻¹ * u * m) = m⁻¹ * (x * u) * m := by group
        _ = m⁻¹ * (u * x) * m := by rw [hx]
        _ = m⁻¹ * u * m * (m⁻¹ * x * m) := by group
    have h3 := hCv h2
    have : x = m * (m⁻¹ * x * m) * m⁻¹ := by group
    rw [this]
    exact M.mul_mem (M.mul_mem hm h3) (M.inv_mem hm)
  refine ⟨m, hm, hQsyl, hTQ, hsylG', hone, fun hCu => ?_⟩
  have hne : Q.relIndex T ≠ 1 := fun h1 => hCu (hone h1)
  have hpos : Q.relIndex T ≠ 0 := Subgroup.index_ne_zero_of_finite
  change Q.relIndex T = 2
  omega

end Sylow

end CFSG.Quasithin.H13.NQRigid
