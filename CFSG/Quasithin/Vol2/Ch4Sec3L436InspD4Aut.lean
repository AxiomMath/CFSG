module

public import CFSG.Quasithin.Vol2.RootDataD4
public import CFSG.Quasithin.Background.SmithB42D4Main
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors
public import CFSG.LieType.Chevalley.RootCharacterConjugation
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.ExactNormalFormE

public section

namespace CFSG.Quasithin.H13.Ch4.D4A

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4 CFSG.Quasithin.H13.NQCat
  CFSG.Quasithin.H13.RootData.D4
open CFSG.Quasithin (perfectCore le_perfectCore_of_perfect)

theorem map_entrywise_posUnipotent_d4
    {K : Type} [Field K] (δ : K ≃+* K) :
    (posUnipotent TwistTag.D4.tag K).map (Units.map (entrywiseHom δ.toRingHom)) =
      posUnipotent TwistTag.D4.tag K := by
  simp only [posUnipotent, rootSpan, Subgroup.map_iSup, map_entrywise_rootSubgroup]

theorem exists_fixed_pow_ne {f : ℕ} (hf : 2 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∃ s : K, σ s = s ∧ s ^ 2 ^ (f / 2) ≠ s := by
  set k := trialityFixedField K σ.toRingHom with hk
  have hcard : Nat.card k = 2 ^ f := CFSG.Quasithin.B42D4.card_fixedField (by omega) hK σ hσ
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf ζ = 2 ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units, hcard]
  refine ⟨((ζ : k) : K), ?_, ?_⟩
  · exact (mem_trialityFixedField).1 (ζ : k).2
  · intro h
    have h1 : ζ ^ 2 ^ (f / 2) = ζ := by
      apply Units.ext
      apply Subtype.ext
      simpa using h
    have hpos : 1 ≤ 2 ^ (f / 2) := Nat.one_le_two_pow
    have h2 : ζ ^ (2 ^ (f / 2) - 1) = 1 := by
      have : ζ ^ (2 ^ (f / 2) - 1) * ζ = 1 * ζ := by
        rw [← pow_succ, Nat.sub_add_cancel hpos, h1, one_mul]
      exact mul_right_cancel this
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hord] at h3
    have hlt : 2 ^ (f / 2) < 2 ^ f := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hle := Nat.le_of_dvd (by
      have : 2 ^ 1 ≤ 2 ^ (f / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega) h3
    omega

section


variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

include hσ3 in
theorem orbitX_mem_perfectCore (a : Fin TwistTag.D4.foldedTag.rank)
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4)
    (c : orbitField TwistTag.D4 K σ.toRingHom a) :
    (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
      perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
  obtain ⟨R, hRx, -, -, hRP, -, -⟩ := levi_package σ a (isPGroup_posUnipotent σ hσ3) hL4
  rw [← hRx c]
  exact hRP ⟨_, rfl⟩

include hσ3 in
theorem orbitY_mem_perfectCore (a : Fin TwistTag.D4.foldedTag.rank)
    (hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4)
    (c : orbitField TwistTag.D4 K σ.toRingHom a) :
    (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
      perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) := by
  obtain ⟨R, hRx, -, hRW, hRP, -, -⟩ := levi_package σ a (isPGroup_posUnipotent σ hσ3) hL4
  obtain ⟨-, -, -, -, -, -, -, -, -, himage⟩ := fixed_simple_positive_complement TwistTag.D4 K σ a
  have hy : (orbitY TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K) ∈
      (fun g => canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
        g * (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹) ''
        Set.range (fun c : orbitField TwistTag.D4 K σ.toRingHom a =>
          (orbitX TwistTag.D4 K σ.toRingHom a c : ModGL TwistTag.D4.tag K)) := by
    rw [himage]
    exact ⟨c, rfl⟩
  obtain ⟨_, ⟨c', rfl⟩, hyc⟩ := hy
  rw [← hyc]
  show canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) *
      (orbitX TwistTag.D4 K σ.toRingHom a c' : ModGL TwistTag.D4.tag K) *
      (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹ ∈ _
  rw [← hRW, ← hRx c', ← map_mul, ← map_inv, ← map_mul]
  exact hRP ⟨_, rfl⟩

omit [Finite K] [CharP K 2] in
theorem mem_graphFixedPosUnipotent_entrywise {δ : K ≃+* K} (hδ : ∀ c, σ (δ c) = δ (σ c))
    {u : ModGL TwistTag.D4.tag K} (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom) :
    Units.map (entrywiseHom δ.toRingHom) u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  refine ⟨?_, ?_⟩
  · have h := map_entrywise_posUnipotent_d4 δ
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hu.1
  · rw [← map_entrywise_twistedFixedGroup hδ]
    exact Subgroup.mem_map_of_mem _ hu.2

include hσ3 in
theorem aut_eq_one_of_fixes_sq {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (ψ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hψ2 : ψ ^ 2 = 1)
    (hψ : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (x : ModGL TwistTag.D4.tag K) ∈ perfectCore (P1 σ) → ψ x = x) :
    ψ = 1 := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hf1 : 1 ≤ f := by omega
  obtain ⟨hact, hnf, ⟨Θ, hΘ, -, -, hinv⟩, -⟩ :=
    even_triality_exact_automorphism_normal_form hf1 K hK σ hσ
  obtain ⟨⟨g, δ⟩, hgδ, -⟩ := hnf ψ
  have hgδ' : ψ = MulAut.conj g * fieldActor σ δ := hgδ
  have hΘψ : Θ ψ = δ := hΘ ψ g δ hgδ'
  set ψ' : ModGL TwistTag.D4.tag K →* ModGL TwistTag.D4.tag K :=
    Units.map (entrywiseHom δ.toRingHom) with hψ'
  have hψx : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (ψ x : ModGL TwistTag.D4.tag K) = (g : ModGL TwistTag.D4.tag K) * ψ' x *
        (g : ModGL TwistTag.D4.tag K)⁻¹ := by
    intro x
    rw [hgδ', MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hact δ x]
  have hδσ : ∀ c, σ (δ c) = δ (σ c) := fun c => by rw [hσ, hσ, map_pow]
  have hδσ' : ∀ c, σ (δ.symm c) = δ.symm (σ c) := fun c => by rw [hσ, hσ, map_pow]
  have hk := CFSG.Quasithin.B42D4.card_fixedField hf1 hK σ hσ
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := hk ▸ h4
  have hL1 := card_orbitField_D4_orientation Nat.prime_two hf1 hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) fa1
  have hL0 := card_orbitField_D4_orientation Nat.prime_two hf1 hK (r := 1) (Or.inl rfl)
    (σ := σ.toRingHom) (fun c => by rw [pow_one]; exact hσ c) fa0
  rw [orbit_card_fa1, pow_one] at hL1
  rw [orbit_card_fa0] at hL0
  have hL4 : ∀ a, 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom a) →
      ∃ s : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a), s.card = 4 := fun a h => by
    have : Fintype ↥(orbitField TwistTag.D4 K σ.toRingHom a) := Fintype.ofFinite _
    have h' : 4 ≤ (Finset.univ : Finset ↥(orbitField TwistTag.D4 K σ.toRingHom a)).card := by
      rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq h'
    exact ⟨t, ht⟩
  have hL41 := hL4 fa1 (hL1 ▸ h4)
  have hL40 := hL4 fa0 (hL0 ▸ h4.trans (Nat.le_self_pow (by norm_num) _))
  have hUP := graphFixedPosUnipotent_le_perfectCore_one σ hσ3 hk4 hL41
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hfixU : ∀ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      (g : ModGL TwistTag.D4.tag K) * ψ' u * (g : ModGL TwistTag.D4.tag K)⁻¹ = u := by
    intro u hu
    have h1 := hψx ⟨u, hUC hu⟩
    rw [hψ ⟨u, hUC hu⟩ (hUP hu)] at h1
    exact h1.symm
  have hψU1 : ∀ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
      ψ' u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := fun u hu =>
    mem_graphFixedPosUnipotent_entrywise σ hδσ hu
  have hgN : (g : ModGL TwistTag.D4.tag K) ∈ Subgroup.normalizer
      (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom : Set (ModGL TwistTag.D4.tag K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hv := mem_graphFixedPosUnipotent_entrywise σ hδσ' hh
      have e : ψ' (Units.map (entrywiseHom δ.symm.toRingHom) h) = h :=
        exactEntrywiseAut_right_inv δ h
      rw [← e, hfixU _ hv]
      exact hv
    · intro hh
      have h1 := hfixU _ hh
      have h2 : ψ' ((g : ModGL TwistTag.D4.tag K) * h * (g : ModGL TwistTag.D4.tag K)⁻¹) = h := by
        have := congrArg (fun y => (g : ModGL TwistTag.D4.tag K)⁻¹ * y *
          (g : ModGL TwistTag.D4.tag K)) h1
        simpa [mul_assoc] using this
      rw [← h2]
      exact hψU1 _ hh
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨-, -, -, -, -, -, hNU, -⟩ := fixed_Borel_self_normalizers TwistTag.D4 K σ w₀ hw₀
  have hgB : (g : ModGL TwistTag.D4.tag K) ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom := by
    rw [← hNU]
    exact ⟨g.2, hgN⟩
  obtain ⟨t, ht, u, hu, htu⟩ := exists_torus_mul_eq_of_mem_graphFixedRootBorel σ.toRingHom hgB
  obtain ⟨l, hl⟩ := torus_conj_highestRoot ht
  have hc : ∀ s : trialityFixedField K σ.toRingHom, (s : K) = (l : K) * δ s := by
    intro s
    have h1 := hfixU (ox₆ σ s) ((ox_data σ hσ3).2.1.2.2.2.2.2 s)
    have h2 : ψ' (ox₆ σ s) = pinnedX TwistTag.D4.tag K (trialityRoot 5) (δ s) :=
      Units.ext (entrywise_pinnedX δ.toRingHom _ _)
    rw [h2, ← htu] at h1
    have hcomm : u * pinnedX TwistTag.D4.tag K (trialityRoot 5) (δ s) * u⁻¹ =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) (δ s) := by
      rw [commute_highestRoot _ hu, mul_inv_cancel_right]
    have h3 : pinnedX TwistTag.D4.tag K (trialityRoot 5) (s : K) =
        pinnedX TwistTag.D4.tag K (trialityRoot 5) ((l : K) * δ s) := by
      calc pinnedX TwistTag.D4.tag K (trialityRoot 5) (s : K) = ox₆ σ s := rfl
        _ = t * u * pinnedX TwistTag.D4.tag K (trialityRoot 5) (δ s) * (t * u)⁻¹ := h1.symm
        _ = t * (u * pinnedX TwistTag.D4.tag K (trialityRoot 5) (δ s) * u⁻¹) * t⁻¹ := by group
        _ = t * pinnedX TwistTag.D4.tag K (trialityRoot 5) (δ s) * t⁻¹ := by rw [hcomm]
        _ = pinnedX TwistTag.D4.tag K (trialityRoot 5) ((l : K) * δ s) := hl _
    exact pinnedX_injective TwistTag.D4.tag K _ h3
  have hl1 : (l : K) = 1 := by
    have h := hc 1
    simp only [OneMemClass.coe_one, map_one, mul_one] at h
    exact h.symm
  have hδk : ∀ s : K, σ s = s → δ s = s := fun s hs => by
    have h := hc ⟨s, (mem_trialityFixedField).2 hs⟩
    rw [hl1, one_mul] at h
    exact h.symm
  have hδ1 : δ = 1 := by
    rcases hinv ψ hψ2 with h1 | ⟨hfe, h2⟩
    · rw [← hΘψ, h1]
    · exfalso
      obtain ⟨s, hs, hsne⟩ := exists_fixed_pow_ne hf hK σ hσ
      have h3 : δ s = s ^ 2 ^ (3 * f / 2) := by
        rw [← hΘψ]
        exact h2 s
      have hs2 : s ^ 2 ^ f = s := by rw [← hσ]; exact hs
      have h4 : s ^ 2 ^ (3 * f / 2) = s ^ 2 ^ (f / 2) := by
        obtain ⟨e, he⟩ := hfe
        have h5 : 3 * f / 2 = f + f / 2 := by omega
        rw [h5, pow_add, pow_mul, hs2]
      exact hsne (by rw [← h4, ← h3]; exact hδk s hs)
  subst hδ1
  rw [CFSG.LieType.Chevalley.fieldActor_one σ, mul_one] at hgδ'
  have hgcent : ∀ y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (y : ModGL TwistTag.D4.tag K) ∈ perfectCore (P1 σ) →
      (y : ModGL TwistTag.D4.tag K) * g = g * y := by
    intro y hy
    have h1 := congrArg Subtype.val (hψ y hy)
    rw [hgδ', MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc (y : ModGL TwistTag.D4.tag K) * g = g * y * (g : ModGL TwistTag.D4.tag K)⁻¹ * g := by
          rw [h1]
      _ = g * y := by group
  obtain ⟨d, hd⟩ := exists_eq_ox₆_of_centralizer σ hσ3 g.2 fun y hy => hgcent ⟨y, hUC hy⟩ (hUP hy)
  have hgZ : (g : ModGL TwistTag.D4.tag K) ∈ CFSG.Quasithin.centerOf (Q0 σ) := by
    refine Subgroup.mem_inf.2 ⟨hd ▸ ox₆_mem_Q0 σ hσ3 d, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hgcent ⟨y, hUC (graphFixedParabolicRadical_le_graphFixedPosUnipotent _ hy)⟩
      (hUP (graphFixedParabolicRadical_le_graphFixedPosUnipotent _ hy))
  have hP0 := D4Irred.perfectCore_le_centralizer σ hσ3
  have hcases : ∀ a : Fin TwistTag.D4.foldedTag.rank, a = fa0 ∨ a = fa1 := by decide
  have hfix : ∀ (a : Fin TwistTag.D4.foldedTag.rank) (x : ↥(graphFixedRootGroup TwistTag.D4 K
      σ.toRingHom)), (x : ModGL TwistTag.D4.tag K) ∈
      perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}) → ψ x = x := by
    intro a x hx
    rcases hcases a with rfl | rfl
    · rw [hgδ', MulAut.conj_apply]
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h1 := Subgroup.mem_centralizer_iff.mp (hP0 hx) _ hgZ
      rw [h1, mul_inv_cancel_right]
    · exact hψ x hx
  refine graphFixedRootGroup_mulAut_ext σ.surjective (fun a c => ?_) fun a c => ?_
  · rw [MulAut.one_apply]
    rcases hcases a with rfl | rfl
    · exact hfix fa0 _ (orbitX_mem_perfectCore σ hσ3 fa0 hL40 c)
    · exact hfix fa1 _ (orbitX_mem_perfectCore σ hσ3 fa1 hL41 c)
  · rw [MulAut.one_apply]
    rcases hcases a with rfl | rfl
    · exact hfix fa0 _ (orbitY_mem_perfectCore σ hσ3 fa0 hL40 c)
    · exact hfix fa1 _ (orbitY_mem_perfectCore σ hσ3 fa1 hL41 c)

include hσ3 in
theorem aut_eq_one_of_fixes {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) (ψ : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {m : ℕ} (hm : ψ ^ (2 ^ m) = 1)
    (hψ : ∀ x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      (x : ModGL TwistTag.D4.tag K) ∈ perfectCore (P1 σ) → ψ x = x) :
    ψ = 1 := by
  induction m generalizing ψ with
  | zero => rwa [pow_zero, pow_one] at hm
  | succ m ih =>
    have hpow : ∀ (k : ℕ) (x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
        (x : ModGL TwistTag.D4.tag K) ∈ perfectCore (P1 σ) → (ψ ^ k) x = x := by
      intro k x hx
      induction k with
      | zero => rfl
      | succ k ihk => rw [pow_succ, MulAut.mul_apply, hψ x hx, ihk]
    have h2 : (ψ ^ (2 ^ m)) ^ 2 = 1 := by rw [← pow_mul, ← pow_succ]; exact hm
    exact ih ψ (aut_eq_one_of_fixes_sq σ hσ3 hf hK hσ _ h2 fun x hx => hpow _ x hx) hψ

end

end CFSG.Quasithin.H13.Ch4.D4A
