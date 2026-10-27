module

public import CFSG.Quasithin.H13.NQSetupExplicitModule
public import CFSG.Quasithin.SteinbergBSPGroupFixedSpace
public import CFSG.Quasithin.SteinbergBSNormalizerInjection
public import CFSG.Quasithin.SteinbergCBTwoNaturalCentralizer
public import CFSG.Quasithin.SteinbergCBFourFieldNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFour
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQSetup

open Module Subgroup CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.SL2Modules

theorem exists_transvection_apply_ne {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : 2 ≤ finrank K V) {v : V} (hv : v ≠ 0) :
    ∃ (f : Dual K V) (w : V) (h : f w = 0), LinearEquiv.transvection h v ≠ v := by
  let b := finBasis K V
  obtain ⟨j, hj⟩ : ∃ j, b.repr v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (b.repr.injective (by ext j; simp [hcon j]))
  let i : Fin (finrank K V) := ⟨if j.val = 0 then 1 else 0, by split_ifs <;> omega⟩
  have hij : i ≠ j := by
    intro h
    have h' := congrArg Fin.val h
    simp only [i] at h'
    split_ifs at h' with h0 <;> omega
  refine ⟨b.coord j, b i, ?_, ?_⟩
  · rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    simp [hij]
  · rw [LinearEquiv.transvection.apply]
    intro h
    have h1 : b.coord j v • b i = 0 := by
      have := congrArg (· - v) h
      simpa using this
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact hj (by rwa [Basis.coord_apply] at h2)
    · exact b.ne_zero i h2

theorem eq_one_of_pow_two_pow_eq_one_of_card_four {k : Type*} [Field k] [Fintype k]
    (hk : Fintype.card k = 4) {a : k} {m : ℕ} (ha : a ^ 2 ^ m = 1) : a = 1 := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero m two_ne_zero)] at ha
    exact zero_ne_one ha
  have h3 : a ^ 3 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [hk] at this
  have hg : Nat.gcd (2 ^ m) 3 = 1 := Nat.Coprime.pow_left m (by norm_num)
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one h3)
  rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

theorem centralizer_map_mem_fixGL {S : Subgroup (E ≃ₗ[ZMod 2] E)} {b : E ≃ₗ[ZMod 2] E}
    (hb : b ∈ centralizer (S : Set (E ≃ₗ[ZMod 2] E))) {e : E} (he : e ∈ fixGL S) :
    b e ∈ fixGL S := by
  refine mem_fixGL.2 fun s hs => ?_
  have hbs : s * b = b * s := mem_centralizer_iff.1 hb s hs
  rw [← LinearEquiv.mul_apply, hbs, LinearEquiv.mul_apply, mem_fixGL.1 he s hs]

theorem eq_bot_of_natural_extension {V : Type*} [AddCommGroup V]
    (S : Subgroup (E ≃ₗ[ZMod 2] E)) (hES : commGL S ⊤ = ⊤) (ρ : S → V → V) (φ : E →+ V)
    (hφ : Function.Surjective φ)
    (heq : ∀ (s : S) (e : E), φ ((s : E ≃ₗ[ZMod 2] E) e) = ρ s (φ e))
    (hker : ∀ s ∈ S, ∀ e : E, φ e = 0 → s e = e)
    (hfix : ∀ v : V, (∀ s : S, ρ s v = v) → v = 0)
    (hρ : ∀ s : S, (∀ v, ρ s v = v) → s = 1)
    (hscalar : ∀ A : V →+ V, (∀ (s : S) (v : V), A (ρ s v) = ρ s (A v)) →
      ∀ m : ℕ, (∀ v, (⇑A)^[2 ^ m] v = v) → ∀ v, A v = v)
    (B : Subgroup (E ≃ₗ[ZMod 2] E)) (hBS : B ≤ centralizer (S : Set (E ≃ₗ[ZMod 2] E)))
    (hB : IsPGroup 2 B) : B = ⊥ := by
  have hfixE : ∀ e : E, e ∈ fixGL S ↔ φ e = 0 := by
    intro e
    refine ⟨fun he => hfix _ fun s => ?_, fun he => mem_fixGL.2 fun s hs => hker s hs e he⟩
    rw [← heq, mem_fixGL.1 he s s.2]
  have hinj : ∀ s ∈ S, (∀ e, s e - e ∈ fixGL S) → s = 1 := by
    intro s hs h
    have h1 : ∀ v, ρ ⟨s, hs⟩ v = v := by
      intro v
      obtain ⟨e, rfl⟩ := hφ v
      have := (hfixE _).1 (h e)
      rw [map_sub, sub_eq_zero] at this
      rw [← heq]
      exact this
    exact congrArg Subtype.val (hρ ⟨s, hs⟩ h1)
  have hN := (SteinbergBS.trivial_kernel_extension_normalizer_injection S hES hinj).2
  rw [eq_bot_iff]
  intro b hb
  rw [mem_bot]
  have hbC := hBS hb
  let g : E →+ V := φ.comp (b : E →ₗ[ZMod 2] E).toAddMonoidHom
  have hg : φ.ker ≤ g.ker := by
    intro e he
    rw [AddMonoidHom.mem_ker] at he ⊢
    exact (hfixE _).1 (centralizer_map_mem_fixGL hbC ((hfixE e).2 he))
  let A : V →+ V := φ.liftOfSurjective hφ ⟨g, hg⟩
  have hA : ∀ e, A (φ e) = φ (b e) := fun e =>
    φ.liftOfRightInverse_comp_apply (Function.surjInv hφ) (Function.rightInverse_surjInv hφ)
      ⟨g, hg⟩ e
  have hAcomm : ∀ (s : S) (v : V), A (ρ s v) = ρ s (A v) := by
    intro s v
    obtain ⟨e, rfl⟩ := hφ v
    rw [← heq, hA, hA, ← heq]
    congr 1
    have hbs : (s : E ≃ₗ[ZMod 2] E) * b = b * s := mem_centralizer_iff.1 hbC s s.2
    rw [← LinearEquiv.mul_apply, ← hbs, LinearEquiv.mul_apply]
  obtain ⟨m, hm⟩ := hB ⟨b, hb⟩
  have hbm : b ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hiter : ∀ (n : ℕ) (e : E), (⇑A)^[n] (φ e) = φ ((b ^ n) e) := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [Function.iterate_succ_apply, hA, ih, pow_succ, LinearEquiv.mul_apply]
  have hAid := hscalar A hAcomm m fun v => by
    obtain ⟨e, rfl⟩ := hφ v
    rw [hiter, hbm]
    rfl
  refine hN b (centralizer_le_normalizer _ hbC) fun e => ?_
  rw [hfixE, map_sub, sub_eq_zero, ← hA, hAid]

theorem eq_bot_of_explicitNaturalFour {S : Subgroup (E ≃ₗ[ZMod 2] E)} (hES : commGL S ⊤ = ⊤)
    (h : ExplicitNaturalFour S) (B : Subgroup (E ≃ₗ[ZMod 2] E))
    (hBS : B ≤ centralizer (S : Set (E ≃ₗ[ZMod 2] E))) (hB : IsPGroup 2 B) : B = ⊥ := by
  obtain ⟨k, _, _, hk, V, _, _, hV, β, φ, hφ, heq, hker⟩ := h
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  have h2 : (1 + 1 : k) = 0 := SteinbergCB.field_four_two hk
  let _ : Module (ZMod 2) V := AddCommGroup.zmodModule fun v => by
    rw [two_nsmul, ← one_smul k v, ← add_smul, h2, zero_smul]
  refine eq_bot_of_natural_extension S hES (fun s v => β s v) φ hφ heq hker ?_ ?_ ?_ B hBS hB
  · intro v hv
    by_contra hv0
    obtain ⟨f, w, hfw, hne⟩ := exists_transvection_apply_ne (K := k) (by omega) hv0
    let u : SpecialLinearGroup k V :=
      ⟨LinearEquiv.transvection hfw, LinearEquiv.transvection.det_eq_one hfw⟩
    apply hne
    have := hv (β.symm u)
    simp only [MulEquiv.apply_symm_apply] at this
    exact this
  · intro s hs
    apply β.injective
    rw [map_one]
    exact Subtype.ext (LinearEquiv.ext hs)
  · intro A hA m hm v
    obtain ⟨hcen, -⟩ := SteinbergCB.nq_natural_four_field_normalizer_bound hk hV
    obtain ⟨a, ha⟩ := (hcen (A.toZModLinearMap 2)).1 fun s' hs' w => by
      obtain ⟨u, rfl⟩ := hs'
      have := hA (β.symm u) w
      simp only [MulEquiv.apply_symm_apply] at this
      exact this
    have ha' : ∀ w, A w = a • w := ha
    have hiter : ∀ (n : ℕ) (w : V), (⇑A)^[n] w = a ^ n • w := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [Function.iterate_succ_apply, ha', ih, smul_smul, pow_succ]
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
    have hpow : a ^ 2 ^ m = 1 := by
      have h1 := hm w₀
      rw [hiter] at h1
      have h1' : (a ^ 2 ^ m - 1) • w₀ = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      rcases smul_eq_zero.1 h1' with h3 | h3
      · exact sub_eq_zero.1 h3
      · exact absurd h3 hw₀
    rw [ha', eq_one_of_pow_two_pow_eq_one_of_card_four hk hpow, one_smul]

theorem eq_bot_of_explicitNaturalThreeExtension {S : Subgroup (E ≃ₗ[ZMod 2] E)}
    (hES : commGL S ⊤ = ⊤) (h : ExplicitNaturalThreeExtension S) (B : Subgroup (E ≃ₗ[ZMod 2] E))
    (hBS : B ≤ centralizer (S : Set (E ≃ₗ[ZMod 2] E))) (hB : IsPGroup 2 B) : B = ⊥ := by
  obtain ⟨V, _, _, hV, β, φ, hφ, heq, hker⟩ := h
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
  refine eq_bot_of_natural_extension S hES (fun s v => β s v) φ.toAddMonoidHom hφ heq hker ?_ ?_
    ?_ B hBS hB
  · intro v hv
    by_contra hv0
    obtain ⟨f, w, hfw, hne⟩ := exists_transvection_apply_ne (K := ZMod 2) (by omega) hv0
    apply hne
    have := hv (β.symm (LinearEquiv.transvection hfw))
    simp only [MulEquiv.apply_symm_apply] at this
    exact this
  · intro s hs
    apply β.injective
    rw [map_one]
    exact LinearEquiv.ext hs
  · intro A hA m hm v
    let b := finBasisOfFinrankEq (ZMod 2) V hV
    have hcomm : ∀ (i j : Fin 3) (r : ZMod 2), i ≠ j →
        Commute (A.toZModLinearMap 2) (LinearMap.transvection (b.coord i) (r • b j)) := by
      intro i j r hij
      have hfw : (b.coord i) (r • b j) = 0 := by
        rw [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
        simp [hij.symm]
      refine LinearMap.ext fun x => ?_
      have := hA (β.symm (LinearEquiv.transvection hfw)) x
      simp only [MulEquiv.apply_symm_apply] at this
      exact this
    obtain ⟨⟨a, haC⟩, ha⟩ := LinearMap.commute_transvections_iff_of_basis b hcomm
    have ha' : ∀ w, A w = a • w := fun w => by
      have := LinearMap.congr_fun ha w
      simpa [Subring.smul_def] using this
    have hiter : ∀ (n : ℕ) (w : V), (⇑A)^[n] w = a ^ n • w := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [Function.iterate_succ_apply, ha', ih, smul_smul, pow_succ]
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : V)
    have hpow : a ^ 2 ^ m = 1 := by
      have h1 := hm w₀
      rw [hiter] at h1
      have h1' : (a ^ 2 ^ m - 1) • w₀ = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      rcases smul_eq_zero.1 h1' with h3 | h3
      · exact sub_eq_zero.1 h3
      · exact absurd h3 hw₀
    have ha1 : a = 1 := by
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero m two_ne_zero)] at hpow
        exact zero_ne_one hpow
      revert ha0
      generalize a = c
      decide +revert
    rw [ha', ha1, one_smul]

theorem exists_alternatingGroup_apply_eq_apply_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h5 : Fintype.card Ω = 5) {a b c d : Ω} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : alternatingGroup Ω, (σ : Equiv.Perm Ω) a = c ∧ (σ : Equiv.Perm Ω) b = d := by
  have hcard : Nat.card Ω = 5 := by rw [Nat.card_eq_fintype_card, h5]
  have h3 : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω 3 := by
    have := alternatingGroup.isMultiplyPretransitive Ω
    rwa [hcard] at this
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup Ω) Ω 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := 3) (by norm_num) (by rw [hcard]; norm_num)
  let x : Fin 2 ↪ Ω := ⟨![a, b], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Ω := ⟨![c, d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup Ω) x y
  refine ⟨σ, ?_, ?_⟩
  · exact DFunLike.congr_fun hσ 0
  · exact DFunLike.congr_fun hσ 1

theorem isIrrAct_of_explicitDeletedFive {S : Subgroup (E ≃ₗ[ZMod 2] E)}
    (h : ExplicitDeletedFive S) : IsIrrAct S := by
  obtain ⟨Ω, _, _, h5, β, ψ, heq⟩ := h
  intro U hU
  let _ : MulAction S Ω :=
    MulAction.compHom Ω ((alternatingGroup Ω).subtype.comp β.toMonoidHom)
  have hsmul : ∀ (g : S) (ω : Ω), g • ω = (β g : Equiv.Perm Ω) ω := fun _ _ => rfl
  have hperm : ∀ g : S, MulAction.toPerm g = (β g : Equiv.Perm Ω) := fun g =>
    Equiv.ext fun ω => hsmul g ω
  set N : Submodule (ZMod 2) (Ω → ZMod 2) :=
    (U.map (ψ : E →ₗ[ZMod 2] evenWeight Ω)).map (evenWeight Ω).subtype with hNdef
  have hNE : N ≤ evenWeight Ω := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hN : ∀ g : S, ∀ x ∈ N, permAct (MulAction.toPerm g) x ∈ N := by
    rintro g _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨ψ ((g : E ≃ₗ[ZMod 2] E) u), ⟨_, hU g g.2 u hu, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply]
    rw [heq, hperm]
    rfl
  have h2 : ∀ a b c d : Ω, a ≠ b → c ≠ d → ∃ g : S, g • a = c ∧ g • b = d := by
    intro a b c d hab hcd
    obtain ⟨σ, h1, h2⟩ := exists_alternatingGroup_apply_eq_apply_eq h5 hab hcd
    refine ⟨β.symm σ, ?_, ?_⟩
    · rw [hsmul, MulEquiv.apply_symm_apply]
      exact h1
    · rw [hsmul, MulEquiv.apply_symm_apply]
      exact h2
  rcases evenWeight_irreducible_five h5 h2 N hNE hN with hbot | htop
  · left
    rw [eq_bot_iff]
    intro u hu
    have h1 : ((ψ u : evenWeight Ω) : Ω → ZMod 2) ∈ N := ⟨ψ u, ⟨u, hu, rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at h1
    have h1' : ψ u = 0 := Subtype.ext h1
    rw [Submodule.mem_bot]
    exact ψ.map_eq_zero_iff.1 h1'
  · right
    rw [eq_top_iff]
    intro e _
    have h1 : ((ψ e : evenWeight Ω) : Ω → ZMod 2) ∈ N := by
      rw [htop]
      exact (ψ e).2
    obtain ⟨x, ⟨u, hu, rfl⟩, hx⟩ := h1
    have hxe : ψ u = ψ e := Subtype.ext hx
    rw [← ψ.injective hxe]
    exact hu

theorem eq_bot_of_explicitDeletedFive [FiniteDimensional (ZMod 2) E]
    {S : Subgroup (E ≃ₗ[ZMod 2] E)} (h : ExplicitDeletedFive S) (B : Subgroup (E ≃ₗ[ZMod 2] E))
    (hBS : B ≤ centralizer (S : Set (E ≃ₗ[ZMod 2] E))) (hB : IsPGroup 2 B) : B = ⊥ := by
  have hirr := isIrrAct_of_explicitDeletedFive h
  have : Nontrivial E := by
    obtain ⟨Ω, _, _, h5, β, ψ, -⟩ := h
    obtain ⟨a, b, hab⟩ : ∃ a b : Ω, a ≠ b :=
      Fintype.exists_pair_of_one_lt_card (by omega)
    refine ⟨⟨ψ.symm ⟨delta a + delta b, delta_add_delta_mem a b⟩, 0, fun h0 => ?_⟩⟩
    have h1 := congrArg (fun x : evenWeight Ω => (x : Ω → ZMod 2) a)
      (ψ.symm.map_eq_zero_iff.1 h0)
    simp [delta, hab] at h1
  exact SteinbergBS.p_centralizer_irreducible_module_triviality (p := 2) S hirr B hBS hB

@[expose] def conjGL {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ψ : E ≃ₗ[ZMod 2] W) :
    (E ≃ₗ[ZMod 2] E) ≃* (W ≃ₗ[ZMod 2] W) where
  toFun g := ψ.symm.trans (g.trans ψ)
  invFun h := ψ.trans (h.trans ψ.symm)
  left_inv g := LinearEquiv.ext fun x => by simp
  right_inv h := LinearEquiv.ext fun x => by simp
  map_mul' g h := LinearEquiv.ext fun x => by simp

theorem conjGL_apply {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (ψ : E ≃ₗ[ZMod 2] W)
    (g : E ≃ₗ[ZMod 2] E) (x : W) : conjGL ψ g x = ψ (g (ψ.symm x)) :=
  rfl

theorem eq_one_of_explicitNaturalThreeDouble {S : Subgroup (E ≃ₗ[ZMod 2] E)}
    (h : ExplicitNaturalThreeDouble S) (B : Subgroup (E ≃ₗ[ZMod 2] E))
    (hBS : B ≤ centralizer (S : Set (E ≃ₗ[ZMod 2] E))) (hB : IsPGroup 2 B)
    (P : Subgroup (E ≃ₗ[ZMod 2] E)) (hPB : P ≤ normalizer (B : Set (E ≃ₗ[ZMod 2] E)))
    (hP : IsPGroup 2 P) (e : E) (he : ∀ s ∈ S, s e ∉ fixGL P) :
    ∀ b ∈ B, b e = e → b = 1 := by
  obtain ⟨V, _, _, hV, β, ψ, heq⟩ := h
  have : FiniteDimensional (ZMod 2) V := Module.finite_of_finrank_eq_succ hV
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set κ := conjGL ψ with hκ
  have hκS : ∀ s : S, κ s = SteinbergCB.diagHom (β s) := fun s =>
    LinearEquiv.ext fun x => by
      rw [hκ, conjGL_apply, heq, ψ.apply_symm_apply]
      rfl
  have hrange : (SteinbergCB.diagHom (V := V)).range = S.map κ.toMonoidHom := by
    ext d
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨β.symm g, (β.symm g).2, by
        rw [MulEquiv.coe_toMonoidHom, hκS, MulEquiv.apply_symm_apply]⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨β ⟨s, hs⟩, (hκS ⟨s, hs⟩).symm⟩
  set B' := B.map κ.toMonoidHom with hB'def
  have hB'C : B' ≤ centralizer ((SteinbergCB.diagHom (V := V)).range :
      Set ((V × V) ≃ₗ[ZMod 2] (V × V))) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_iff]
    intro d hd
    rw [hrange] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [mem_centralizer_iff.1 (hBS hb) s hs]
  have hB'2 : IsPGroup 2 B' := hB.map _
  intro b hb hbe
  by_contra hb1
  have hκb : κ b ∈ B' := ⟨b, hb, rfl⟩
  have hκb1 : κ b ≠ 1 := fun h1 => hb1 (κ.injective (h1.trans (map_one κ).symm))
  have hB'ne : B' ≠ ⊥ := fun hbot => by
    rw [hbot, mem_bot] at hκb
    exact hκb1 hκb
  obtain ⟨hcard, -, htrans, -⟩ :=
    (SteinbergCB.nq_two_natural_binary_space_centralizer (n := 3) (by norm_num) hV).2.2.2 B'
      hB'C hB'2 hB'ne
  set F : Submodule (ZMod 2) (V × V) := ⨅ b ∈ B',
    LinearMap.ker ((b : (V × V) →ₗ[ZMod 2] (V × V)) - LinearMap.id) with hFdef
  have hmemF : ∀ y, y ∈ F ↔ ∀ b' ∈ B', b' y = y := by
    intro y
    simp [hFdef, Submodule.mem_iInf, sub_eq_zero]
  have hfixx : κ b (ψ e) = ψ e := by rw [hκ, conjGL_apply, ψ.symm_apply_apply, hbe]
  have hxF : ψ e ∈ F := by
    rw [hmemF]
    intro b' hb'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := mem_powers_of_prime_card hcard (g := ⟨κ b, hκb⟩) (g' := ⟨b', hb'⟩)
      (fun h1 => hκb1 (congrArg Subtype.val h1))
    have hb'n : b' = κ b ^ n := by
      have := congrArg Subtype.val hn
      simpa using this.symm
    rw [hb'n]
    clear hn hb'n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hfixx, ih]
  have hx0 : ψ e ≠ 0 := by
    intro h0
    apply he 1 (one_mem S)
    rw [ψ.map_eq_zero_iff.1 h0, map_zero]
    exact zero_mem _
  set P' := P.map κ.toMonoidHom with hP'def
  have hP'2 : IsPGroup 2 P' := hP.map _
  have hFP : ∀ p' ∈ P', ∀ w ∈ F, p' w ∈ F := by
    rintro _ ⟨p, hp, rfl⟩ w hw
    rw [hmemF] at hw ⊢
    rintro _ ⟨c, hc, rfl⟩
    have hc' : p⁻¹ * c * p ∈ B := by
      have := (mem_normalizer_iff.1 (hPB (inv_mem hp)) c).1 hc
      rwa [inv_inv] at this
    have h1 : κ (p⁻¹ * c * p) w = w := hw _ ⟨_, hc', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    calc κ c (κ p w) = κ p (κ (p⁻¹ * c * p) w) := by
          rw [map_mul, map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
            ← LinearEquiv.mul_apply (κ p), mul_inv_cancel]
          rfl
      _ = κ p w := by rw [h1]
  have : Finite F := inferInstance
  have hFbot : F ≠ ⊥ := fun hbot => hx0 (by rw [hbot] at hxF; exact (Submodule.mem_bot _).1 hxF)
  obtain ⟨w, hwF, hw0, hwP⟩ := SteinbergBS.exists_fixed_ne_zero (p := 2) hP'2 F hFbot hFP
  obtain ⟨d, hd, hdx⟩ := htrans (ψ e) hxF w hwF hx0 hw0
  rw [hrange] at hd
  obtain ⟨s, hs, rfl⟩ := hd
  apply he s hs
  refine mem_fixGL.2 fun p hp => ?_
  have h1 := hwP (κ p) ⟨p, hp, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom] at hdx
  rw [hκ, conjGL_apply, ψ.symm_apply_apply] at hdx
  rw [← hdx, hκ, conjGL_apply, ψ.symm_apply_apply] at h1
  exact ψ.injective h1

theorem nq_explicit_module_two_stabilizer_collapse [FiniteDimensional (ZMod 2) E]
    (S : Subgroup (E ≃ₗ[ZMod 2] E)) (hES : commGL S ⊤ = ⊤)
    (hcond : ExplicitNaturalFour S ∨ ExplicitDeletedFive S ∨ ExplicitNaturalThreeDouble S ∨
      ExplicitNaturalThreeExtension S)
    (B : Subgroup (E ≃ₗ[ZMod 2] E)) (hBS : B ≤ centralizer (S : Set (E ≃ₗ[ZMod 2] E)))
    (hB : IsPGroup 2 B) (P : Subgroup (E ≃ₗ[ZMod 2] E))
    (hPS : P ≤ normalizer (S : Set (E ≃ₗ[ZMod 2] E)) ⊓ normalizer (B : Set (E ≃ₗ[ZMod 2] E)))
    (hP : IsPGroup 2 P) :
    (∀ e : E, (∀ s ∈ S, s e ∉ fixGL P) → ∀ b ∈ B, b e = e → b = 1) ∧
      (ExplicitNaturalFour S ∨ ExplicitDeletedFive S ∨ ExplicitNaturalThreeExtension S →
        B = ⊥) := by
  have hbot : ExplicitNaturalFour S ∨ ExplicitDeletedFive S ∨
      ExplicitNaturalThreeExtension S → B = ⊥ := by
    rintro (h | h | h)
    · exact eq_bot_of_explicitNaturalFour hES h B hBS hB
    · exact eq_bot_of_explicitDeletedFive h B hBS hB
    · exact eq_bot_of_explicitNaturalThreeExtension hES h B hBS hB
  refine ⟨fun e he b hb hbe => ?_, hbot⟩
  rcases hcond with h | h | h | h
  · rw [hbot (Or.inl h), mem_bot] at hb
    exact hb
  · rw [hbot (Or.inr (Or.inl h)), mem_bot] at hb
    exact hb
  · exact eq_one_of_explicitNaturalThreeDouble h B hBS hB P (fun p hp => (hPS hp).2) hP e he b
      hb hbe
  · rw [hbot (Or.inr (Or.inr h)), mem_bot] at hb
    exact hb

end CFSG.Quasithin.H13.NQSetup
