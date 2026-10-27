module

public import CFSG.Quasithin.H13.A5S136f
public import CFSG.Quasithin.Background.FFC4Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

@[expose] def core5Hom : ↥(G6.coreMod 5) →* W5 where
  toFun x := Multiplicative.ofAdd
    ⟨Multiplicative.toAdd (x : G6.PermMod 5), mem_Ev.2 (G6.mem_coreMod.1 x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem core5Hom_injective : Function.Injective core5Hom := by
  intro x y h
  have h1 : Multiplicative.toAdd (x : G6.PermMod 5) = Multiplicative.toAdd (y : G6.PermMod 5) :=
    congrArg (fun w : W5 => ((Multiplicative.toAdd w : ↥Ev) : Fin 5 → ZMod 2)) h
  exact Subtype.ext (Multiplicative.toAdd.injective h1)

theorem core5Hom_surjective : Function.Surjective core5Hom := fun w =>
  ⟨⟨Multiplicative.ofAdd ((Multiplicative.toAdd w : ↥Ev) : Fin 5 → ZMod 2),
    G6.mem_coreMod.2 (mem_Ev.1 (Multiplicative.toAdd w).2)⟩, rfl⟩

theorem core5Hom_permAct (σ : Equiv.Perm (Fin 5)) (x : ↥(G6.coreMod 5)) :
    core5Hom ⟨G6.permAct 5 σ x, G6.permAct_mem_coreMod σ x.2⟩ = pact σ (core5Hom x) := rfl

theorem mul_pact_wA_ne_one : ∀ (s : Equiv.Perm (Fin 5)) (p : Fin 5),
    Multiplicative.ofAdd (wA p) * pact s (Multiplicative.ofAdd (wA p)) *
      pact s (pact s (Multiplicative.ofAdd (wA p))) ≠ 1 := by
  decide +kernel

theorem eq_one_of_pact_c234_c3p : ∀ x : W5, pact c234 x = x → pact c3p x = x → x = 1 := by
  decide +kernel

theorem exists_eq_wA_of_isSylowTwoOf {D : Subgroup ↥(alternatingGroup (Fin 5))}
    (hD : IsSylowTwoOf D ⊤) {x : W5} (hx : x ≠ 1)
    (hfix : ∀ σ ∈ D, pact (σ : Equiv.Perm (Fin 5)) x = x) :
    ∃ p : Fin 5, x = Multiplicative.ofAdd (wA p) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : IsSylowTwoOf K4 ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 2) (by rw [card_K4]; norm_num), ?_⟩
    show ¬ 2 ∣ K4.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact K4_index_odd
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hK4)
    (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hD)
  set x' := pact ((k : Equiv.Perm (Fin 5))⁻¹) x with hx'
  have hfix' : ∀ σ : Equiv.Perm (Fin 5), InK4 σ → pact σ x' = x' := by
    intro σ hσ
    have hσA : σ ∈ alternatingGroup (Fin 5) :=
      Equiv.Perm.mem_alternatingGroup.2 (sign_klein σ hσ)
    set σA : ↥(alternatingGroup (Fin 5)) := ⟨σ, hσA⟩ with hσAdef
    have hmem : k * σA * k⁻¹ ∈ D := by
      rw [hk]
      have e : k⁻¹ * (k * σA * k⁻¹) * k = σA := by group
      rw [e]
      exact hσ
    have h1 := hfix _ hmem
    have e2 : ((k * σA * k⁻¹ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) =
        (k : Equiv.Perm (Fin 5)) * σ * (k : Equiv.Perm (Fin 5))⁻¹ := rfl
    rw [e2, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply] at h1
    rw [hx']
    have h2 := congrArg (pact ((k : Equiv.Perm (Fin 5))⁻¹)) h1
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h2
    exact h2
  rcases fixed_K4 x' hfix' with h | h
  · exfalso
    apply hx
    have h3 := congrArg (pact (k : Equiv.Perm (Fin 5))) h
    rw [hx', ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply,
      map_one] at h3
    exact h3
  · refine ⟨(k : Equiv.Perm (Fin 5)) 4, ?_⟩
    have h3 := congrArg (pact (k : Equiv.Perm (Fin 5))) h
    rw [hx', ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply] at h3
    rw [h3, W4, pact_wA]

theorem comap_eq_alternatingGroup {X : Type} [Group X] {N : Subgroup X}
    {φ : Equiv.Perm (Fin 5) →* X} (hφ : Function.Injective φ) (hN : N ≤ φ.range)
    (hp : ⁅N, N⁆ = N) (h60 : Nat.card ↥N = 60) : N.comap φ = alternatingGroup (Fin 5) := by
  set A := N.comap φ with hAdef
  have hmap : A.map φ = N := Subgroup.map_comap_eq_self hN
  have hAp : ⁅A, A⁆ = A := by
    apply Subgroup.map_injective hφ
    rw [Subgroup.map_commutator, hmap, hp]
  have hle : A ≤ alternatingGroup (Fin 5) := by
    intro σ hσ
    rw [← hAp] at hσ
    have h1 : σ ∈ commutator (Equiv.Perm (Fin 5)) := by
      rw [commutator_def]
      exact Subgroup.commutator_mono le_top le_top hσ
    rw [Equiv.Perm.mem_alternatingGroup]
    exact Abelianization.commutator_subset_ker Equiv.Perm.sign h1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hA : Nat.card ↥A = 60 := by rw [← h60, ← hmap, Subgroup.card_map_of_injective hφ]
  rw [hA]
  exact card_A5.le

theorem exists_delta5_quot {M : Type} [CommGroup M] {G₁ : Subgroup (MulAut M)}
    {W₁ W₂ C : Subgroup M} {π : Equiv.Perm (Fin 5) →* ↥G₁}
    (hπ : (FFModel.symDn 5).RealizesVia G₁ W₁ C π) (hsup : W₁ ⊔ W₂ = ⊤) (hinf : W₁ ⊓ W₂ = C)
    (hW₂ : ∀ g ∈ G₁, ∀ w ∈ W₂, g w ∈ W₂) :
    ∃ Ψ : M →* W5, Function.Surjective Ψ ∧ (∀ m, Ψ m = 1 ↔ m ∈ W₂) ∧
      ∀ σ m, Ψ (((π σ : ↥G₁) : MulAut M) m) = pact σ (Ψ m) := by
  obtain ⟨f₀, hfs, hfk, hfe⟩ := FFC.RealizesVia.secMap FFC.symDn_ker_five hπ
  let f : ↥W₁ →* ↥(G6.coreMod 5) := f₀
  have hW₁ : ∀ h : ↥G₁, ∀ u ∈ W₁, (h : MulAut M) u ∈ W₁ := hπ.2.2.2.1
  let g : ↥W₁ →* W5 := core5Hom.comp f
  have hgs : Function.Surjective g := core5Hom_surjective.comp hfs
  let ι : ↥W₁ →* M ⧸ W₂ := (QuotientGroup.mk' W₂).comp W₁.subtype
  have hιs : Function.Surjective ι := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective W₂ q
    have hm : m ∈ W₁ ⊔ W₂ := hsup ▸ Subgroup.mem_top m
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hm
    refine ⟨⟨a, ha⟩, ?_⟩
    have hb1 : (QuotientGroup.mk' W₂) b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    show (QuotientGroup.mk' W₂) a = (QuotientGroup.mk' W₂) (a * b)
    rw [map_mul, hb1, mul_one]
  have hker : ι.ker = g.ker := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h
      have hu : (u : M) ∈ W₂ := (QuotientGroup.eq_one_iff _).mp h
      have hC : (u : M) ∈ C := hinf ▸ ⟨u.2, hu⟩
      have h1 : f u = 1 := (hfk u).mpr hC
      show core5Hom (f u) = 1
      rw [h1, map_one]
    · intro h
      have h1 : f u = 1 := core5Hom_injective (h.trans (map_one _).symm)
      have hC : (u : M) ∈ C := (hfk u).mp h1
      rw [← hinf] at hC
      exact (QuotientGroup.eq_one_iff _).mpr hC.2
  let E : M ⧸ W₂ ≃* W5 := ((QuotientGroup.quotientKerEquivOfSurjective ι hιs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)
  let Ψ : M →* W5 := E.toMonoidHom.comp (QuotientGroup.mk' W₂)
  have hΨ₁ : ∀ u : ↥W₁, Ψ u = g u := by
    intro u
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective ι hιs).symm
        (QuotientGroup.mk' W₂ (u : M)) = (u : ↥W₁ ⧸ ι.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show (QuotientGroup.quotientKerEquivOfSurjective g hgs)
      ((QuotientGroup.quotientMulEquivOfEq hker)
        ((QuotientGroup.quotientKerEquivOfSurjective ι hιs).symm
          (QuotientGroup.mk' W₂ (u : M)))) = g u
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hΨk : ∀ m, Ψ m = 1 ↔ m ∈ W₂ := by
    intro m
    show E (QuotientGroup.mk' W₂ m) = 1 ↔ m ∈ W₂
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨Ψ, E.surjective.comp (QuotientGroup.mk'_surjective W₂), hΨk, fun σ m => ?_⟩
  have hm : m ∈ W₁ ⊔ W₂ := hsup ▸ Subgroup.mem_top m
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hm
  have hb' : Ψ (((π σ : ↥G₁) : MulAut M) b) = 1 := (hΨk _).mpr (hW₂ _ (π σ).2 b hb)
  have hb1 : Ψ b = 1 := (hΨk b).mpr hb
  have ha' := hW₁ (π σ) a ha
  rw [map_mul, map_mul, map_mul, hb', hb1, mul_one, mul_one]
  have h3 : Ψ (((π σ : ↥G₁) : MulAut M) a) = g ⟨_, ha'⟩ := hΨ₁ ⟨_, ha'⟩
  have h4 : Ψ a = g ⟨a, ha⟩ := hΨ₁ ⟨a, ha⟩
  rw [h3, h4]
  have h2 : f ⟨_, ha'⟩ = ⟨G6.permAct 5 σ (f ⟨a, ha⟩), G6.permAct_mem_coreMod σ (f ⟨a, ha⟩).2⟩ :=
    Subtype.ext (hfe σ ⟨a, ha⟩ ha')
  show core5Hom (f ⟨_, ha'⟩) = pact σ (core5Hom (f ⟨a, ha⟩))
  rw [h2, core5Hom_permAct]

theorem exists_perm_of_normalizes_quot {M : Type} [CommGroup M] (Ψ : M →* W5)
    (hΨ : Function.Surjective Ψ) (π : Equiv.Perm (Fin 5) → MulAut M)
    (hπ : ∀ σ m, Ψ (π σ m) = pact σ (Ψ m)) (φ : MulAut M)
    (hφ : ∀ m, Ψ m = 1 → Ψ (φ m) = 1) (hφ' : ∀ m, Ψ m = 1 → Ψ (φ.symm m) = 1)
    (h1 : ∀ σ ∈ alternatingGroup (Fin 5), ∃ τ ∈ alternatingGroup (Fin 5),
      ∀ m, φ (π σ m) = π τ (φ m))
    (h2 : ∀ τ ∈ alternatingGroup (Fin 5), ∃ σ ∈ alternatingGroup (Fin 5),
      ∀ m, φ (π σ m) = π τ (φ m)) :
    ∃ s : Equiv.Perm (Fin 5), ∀ m, Ψ (φ m) = pact s (Ψ m) := by
  classical
  have key : ∀ m m', Ψ m = Ψ m' → Ψ (φ m) = Ψ (φ m') := by
    intro m m' h
    have h1 : Ψ (m * m'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
    have h2 := hφ _ h1
    rw [map_mul, map_inv, map_mul, map_inv] at h2
    exact mul_inv_eq_one.mp h2
  set r := Function.surjInv hΨ with hr
  have hr' : ∀ x, Ψ (r x) = x := Function.surjInv_eq hΨ
  let ρf : W5 →* W5 :=
    { toFun := fun x => Ψ (φ (r x))
      map_one' := by
        show Ψ (φ (r 1)) = 1
        rw [key (r 1) 1 (by rw [hr', map_one]), map_one, map_one]
      map_mul' := fun x y => by
        show Ψ (φ (r (x * y))) = Ψ (φ (r x)) * Ψ (φ (r y))
        rw [key (r (x * y)) (r x * r y) (by rw [hr', map_mul, hr', hr']), map_mul, map_mul] }
  have hρ : ∀ m, ρf (Ψ m) = Ψ (φ m) := fun m => key _ _ (hr' _)
  have hinj : Function.Injective ρf := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [← hr' x] at hx ⊢
    rw [hρ] at hx
    have := hφ' _ hx
    rwa [MulEquiv.symm_apply_apply] at this
  let ρ : MulAut W5 := MulEquiv.ofBijective ρf (Finite.injective_iff_bijective.mp hinj)
  have hρ' : ∀ m, ρ (Ψ m) = Ψ (φ m) := hρ
  obtain ⟨s, hs⟩ := exists_pact_of_normalizes ρ
    (fun σ hσ => by
      obtain ⟨τ, hτ, hστ⟩ := h1 σ hσ
      refine ⟨τ, hτ, fun x => ?_⟩
      rw [← hr' x, ← hπ, hρ', hρ', hστ, hπ])
    (fun τ hτ => by
      obtain ⟨σ, hσ, hστ⟩ := h2 τ hτ
      refine ⟨σ, hσ, fun x => ?_⟩
      rw [← hr' x, ← hπ, hρ', hρ', hστ, hπ])
  exact ⟨s, fun m => by rw [← hρ', hs]⟩

end CFSG.Quasithin.H13.A5
