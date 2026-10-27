module

public import CFSG.Quasithin.Recognition.SzVBBender
public import CFSG.Quasithin.Background.Harris.R1.Fam

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Quasithin CFSG.Holt.H78 CFSG.GH74.Uniqueness.Bender

theorem exists_equivariant_equiv_of_stabilizer {H K Ω Ω' : Type*} [Group H] [Group K]
    [MulAction K Ω] (π : H →* K) (hπ : Function.Surjective π) (ρ : H →* Equiv.Perm Ω') (ω₀ : Ω)
    (ω₀' : Ω') (hΩ : ∀ ω : Ω, ∃ x : K, x • ω₀ = ω) (hΩ' : ∀ ω' : Ω', ∃ h : H, ρ h ω₀' = ω')
    (hstab : ∀ h : H, π h • ω₀ = ω₀ ↔ ρ h ω₀' = ω₀') :
    ∃ Φ : Ω ≃ Ω', ∀ (h : H) (ω : Ω), Φ (π h • ω) = ρ h (Φ ω) := by
  let _ : MulAction H Ω' := MulAction.compHom Ω' ρ
  have hρ : ∀ (h : H) (ω' : Ω'), ρ h ω' = h • ω' := fun _ _ => rfl
  have hΩH : ∀ ω : Ω, ∃ h : H, π h • ω₀ = ω := by
    intro ω
    obtain ⟨x, hx⟩ := hΩ ω
    obtain ⟨h, rfl⟩ := hπ x
    exact ⟨h, hx⟩
  choose g hg using hΩH
  have wd : ∀ h h' : H, π h • ω₀ = π h' • ω₀ → h • ω₀' = h' • ω₀' := by
    intro h h' hh
    have h1 : π (h'⁻¹ * h) • ω₀ = ω₀ := by
      rw [map_mul, map_inv, mul_smul, hh, inv_smul_smul]
    have h2 := (hstab _).mp h1
    rw [hρ, mul_smul, inv_smul_eq_iff] at h2
    exact h2
  obtain ⟨f, hf⟩ : ∃ f : Ω → Ω', ∀ ω, f ω = g ω • ω₀' := ⟨fun ω => g ω • ω₀', fun _ => rfl⟩
  have key : ∀ h : H, f (π h • ω₀) = h • ω₀' := fun h => by
    rw [hf]
    exact wd _ _ (hg _)
  have hequiv : ∀ (h : H) (ω : Ω), f (π h • ω) = h • f ω := by
    intro h ω
    have e : π h • ω = π (h * g ω) • ω₀ := by rw [map_mul, mul_smul, hg]
    rw [e, key, mul_smul, hf ω]
  have hinj : Function.Injective f := by
    intro ω ω' hωω
    rw [hf, hf] at hωω
    have h1 : ((g ω)⁻¹ * g ω') • ω₀' = ω₀' := by
      rw [mul_smul, inv_smul_eq_iff]
      exact hωω.symm
    have h2 := (hstab ((g ω)⁻¹ * g ω')).mpr ((hρ _ _).trans h1)
    rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff, hg, hg] at h2
    exact h2.symm
  have hsurj : Function.Surjective f := by
    intro ω'
    obtain ⟨h, rfl⟩ := hΩ' ω'
    exact ⟨π h • ω₀, by rw [key, hρ]⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun h ω => (hequiv h ω).trans (hρ h _).symm⟩

theorem exists_mulEquiv_of_surjective_ker_eq {H K M : Type*} [Group H] [Group K] [Group M]
    (π : H →* K) (g : H →* M) (hπ : Function.Surjective π) (hg : Function.Surjective g)
    (hker : g.ker = π.ker) : ∃ φ : K ≃* M, ∀ h : H, φ (π h) = g h := by
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : K →* M, ∀ h : H, φ₀ (π h) = g h :=
    ⟨π.liftOfSurjective hπ ⟨g, hker.ge⟩, fun h =>
      π.liftOfRightInverse_comp_apply (Function.surjInv hπ) (Function.rightInverse_surjInv hπ)
        ⟨g, hker.ge⟩ h⟩
  have hinj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨h, rfl⟩ := hπ x
    have h1 : h ∈ g.ker := by rw [MonoidHom.mem_ker, ← hφ₀]; exact hx
    rw [hker, MonoidHom.mem_ker] at h1
    exact h1
  have hsurj : Function.Surjective φ₀ := fun m => by
    obtain ⟨h, rfl⟩ := hg m
    exact ⟨π h, hφ₀ h⟩
  exact ⟨MulEquiv.ofBijective φ₀ ⟨hinj, hsurj⟩, hφ₀⟩

theorem smul_one_eq_one_iff_mem_normalizer {H K : Type} [Group H] [Group K] (Qs : Sylow 2 H)
    (ψ : H →* K) (Qt : Sylow 2 K) (hQt : (Qt : Subgroup K) = (Qs : Subgroup H).map ψ)
    (hY : ψ.ker ≤ Subgroup.normalizer ((Qs : Subgroup H) : Set H)) (h : H) :
    ψ h • ((1 : K) : K ⧸ borel (Qt : Subgroup K)) = ((1 : K) : K ⧸ borel (Qt : Subgroup K)) ↔
      h ∈ Subgroup.normalizer ((Qs : Subgroup H) : Set H) := by
  have e1 : ψ h • ((1 : K) : K ⧸ borel (Qt : Subgroup K)) =
      ((1 : K) : K ⧸ borel (Qt : Subgroup K)) ↔ ψ h ∈ borel (Qt : Subgroup K) := by
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
    simp
  rw [e1]
  constructor
  · intro hh
    refine CFSG.Quasithin.Background.Harris.R1.mem_normalizer_of_map Qs ψ hY ?_
    rw [← hQt]
    exact hh
  · intro hh
    have : ψ h ∈ Subgroup.normalizer (((Qs : Subgroup H).map ψ : Subgroup K) : Set K) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨q, hq, rfl⟩
        have := (Subgroup.mem_normalizer_iff.mp hh q).mp hq
        exact ⟨_, this, by simp⟩
      · rintro ⟨q, hq, hqx⟩
        have hq2 := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hh) q).mp hq
        rw [inv_inv] at hq2
        refine ⟨h⁻¹ * q * h, hq2, ?_⟩
        have : x = (ψ h)⁻¹ * (ψ h * x * (ψ h)⁻¹) * ψ h := by group
        rw [this, ← hqx]
        simp
    rw [← hQt] at this
    exact this

theorem isBenderAction_borelCosets {K : Type*} [Group K] [Finite K]
    {n i e : ℕ} (hB : BenderType K n i e) (Q : Sylow 2 K) :
    IsBenderAction K (K ⧸ borel (Q : Subgroup K)) n i e := by
  obtain ⟨t, hc⟩ := hB.exists_benderCore Q
  exact ⟨hB, inferInstance, hc.index_eq⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_isBenderAction_imgK_of_bender {K1 P V B : Subgroup G}
    (hKP : K1 ≤ P) (hconj : ∀ k ∈ K1, ∀ k' ∈ K1, conjSub k V = conjSub k' V ↔ k⁻¹ * k' ∈ B)
    (hsurj : ∀ x ∈ P, ∃ k ∈ K1, conjSub x V = conjSub k V) {K : Type} [Group K]
    (π : ↥K1 →* K) (hπ : Function.Surjective π) (Qs : Sylow 2 ↥K1)
    (hQs : ∀ k : ↥K1, k ∈ Subgroup.normalizer ((Qs : Subgroup ↥K1) : Set ↥K1) ↔ (k : G) ∈ B)
    (hY : π.ker ≤ Subgroup.normalizer ((Qs : Subgroup ↥K1) : Set ↥K1)) {n i e : ℕ}
    (hB : BenderType K n i e) : IsBenderAction ↥(imgK K1 P V) (ConjSet P V) n i e := by
  have : Finite K := Finite.of_surjective π hπ
  obtain ⟨Qt, hQt⟩ : ∃ Qt : Sylow 2 K, (Qt : Subgroup K) = (Qs : Subgroup ↥K1).map π :=
    ⟨Qs.mapSurjective hπ, Sylow.coe_mapSurjective hπ Qs⟩
  have hA : IsBenderAction K (K ⧸ borel (Qt : Subgroup K)) n i e :=
    isBenderAction_borelCosets hB Qt
  have hfaith := hA.faithfulSMul
  have hpre := hA.isPretransitive
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ↥K1 →* Equiv.Perm (ConjSet P V),
      ∀ (k : ↥K1) (U : ConjSet P V), ρ k U = Subgroup.inclusion hKP k • U :=
    ⟨(MulAction.toPermHom ↥P (ConjSet P V)).comp (Subgroup.inclusion hKP), fun _ _ => rfl⟩
  have hρval : ∀ (k : ↥K1) (U : ConjSet P V), (ρ k U).1 = conjSub (k : G) U.1 := fun k U =>
    (congrArg Subtype.val (hρ k U)).trans (ConjSet.smul_val P V (Subgroup.inclusion hKP k) U)
  obtain ⟨g, hg, hgk⟩ := exists_surjective_imgK V hKP
  have hgρ : ∀ (k : ↥K1) (U : ConjSet P V),
      ((g k : ↥(imgK K1 P V)) : Equiv.Perm (ConjSet P V)) U = ρ k U := fun k U =>
    (hgk k U).trans (hρ k U).symm
  have hΩ : ∀ ω : K ⧸ borel (Qt : Subgroup K),
      ∃ x : K, x • ((1 : K) : K ⧸ borel (Qt : Subgroup K)) = ω := fun ω =>
    MulAction.exists_smul_eq K _ ω
  have hΩ' : ∀ U : ConjSet P V, ∃ k : ↥K1, ρ k (ConjSet.base P V) = U := by
    intro U
    obtain ⟨x, hx, hU⟩ := U.2
    obtain ⟨k, hk, hxk⟩ := hsurj x hx
    refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
    rw [hρval]
    exact (hU.trans hxk).symm
  have h1 : ∀ k : ↥K1, ρ k (ConjSet.base P V) = ConjSet.base P V ↔ conjSub (k : G) V = V := by
    intro k
    constructor
    · intro hk
      exact (hρval k _).symm.trans (congrArg Subtype.val hk)
    · intro hk
      exact Subtype.ext ((hρval k _).trans hk)
  have hstab : ∀ k : ↥K1, π k • ((1 : K) : K ⧸ borel (Qt : Subgroup K)) =
      ((1 : K) : K ⧸ borel (Qt : Subgroup K)) ↔ ρ k (ConjSet.base P V) = ConjSet.base P V := by
    intro k
    have h2 := hconj 1 K1.one_mem (k : G) k.2
    rw [conjSub_one, inv_one, one_mul] at h2
    rw [smul_one_eq_one_iff_mem_normalizer Qs π Qt hQt hY k, hQs k, h1 k]
    exact h2.symm.trans eq_comm
  obtain ⟨Φ, hΦ⟩ := exists_equivariant_equiv_of_stabilizer π hπ ρ
    ((1 : K) : K ⧸ borel (Qt : Subgroup K)) (ConjSet.base P V) hΩ hΩ' hstab
  have hker : g.ker = π.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hk
      have h : ∀ U : ConjSet P V, ρ k U = U := fun U =>
        (hgρ k U).symm.trans
          (congrArg (fun m : ↥(imgK K1 P V) => (m : Equiv.Perm (ConjSet P V)) U) hk)
      refine hfaith.eq_of_smul_eq_smul fun ω => ?_
      rw [one_smul]
      exact Φ.injective ((hΦ k ω).trans (h (Φ ω)))
    · intro hk
      refine Subtype.ext (Equiv.ext fun U => ?_)
      obtain ⟨ω, rfl⟩ := Φ.surjective U
      have h : ρ k (Φ ω) = Φ ω := by rw [← hΦ, hk, one_smul]
      exact (hgρ k (Φ ω)).trans h
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_of_surjective_ker_eq π g hπ hg hker
  have hΦ' : ∀ (x : K) (ω : K ⧸ borel (Qt : Subgroup K)), Φ (x • ω) = φ x • Φ ω := by
    intro x ω
    obtain ⟨k, rfl⟩ := hπ x
    rw [hΦ, hφ]
    exact (hgρ k (Φ ω)).symm
  exact hA.of_equiv φ Φ hΦ'

end CFSG.Quasithin.SzVB
