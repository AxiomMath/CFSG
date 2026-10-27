module

public import CFSG.Quasithin.Background.B15P4Layer2Flip
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQ4

public section

namespace CFSG.Quasithin.B15P4

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
open TensorProduct Module

universe u

theorem isElementaryAbelian_two_of_le {X : Type*} [Group X] {A B : Subgroup X}
    [hA : CFSG.IsElementaryAbelian 2 A] (hBA : B ≤ A) : CFSG.IsElementaryAbelian 2 ↥B :=
  CFSG.IsElementaryAbelian.of_le inferInstance hBA

theorem no_transitive_perfect_orbit_diag {F : Type u} [Field F] [Finite F] [CharP F 2] {W : Type u}
    [AddCommGroup W] [Module F W] [Nontrivial W] [Finite W] {s : ℕ} (hs : 2 ≤ s)
    (L : Fin s → Subgroup (W ≃ₗ[F] W))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hperf : ∀ i, Group.IsPerfect ↥(L i)) (hnt : ∀ i, Nontrivial ↥(L i))
    (hirr : IsIrrAct (⨆ i, L i))
    (hend : ∀ f : Module.End F W, (∀ h ∈ ⨆ i, L i, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w)
    (A : Subgroup (W ≃ₗ[F] W)) [CFSG.IsElementaryAbelian 2 A]
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, conjSub a (L i) = L j)
    (htrans : ∀ i j, ∃ a ∈ A, conjSub a (L i) = L j)
    (B : Subgroup (W ≃ₗ[F] W)) (hBA : B ≤ A) (hB0 : B ≠ ⊥)
    (hBfix : ∀ b ∈ B, ∀ i, conjSub b (L i) = L i)
    (hBq : ∀ a ∈ A, ∀ b ∈ B, ∀ w, b (a w - w) = a w - w)
    (hoffB : Nat.card W ≤ Nat.card B * Nat.card (fixGL B)) : False := by
  classical
  have hGLfin : Finite (W ≃ₗ[F] W) :=
    Finite.of_injective (fun f : W ≃ₗ[F] W => (f : W → W)) DFunLike.coe_injective
  obtain ⟨V, hV1, hV2, ρ, e, hVnt, hVfin, hρinj, hact, hspan, -, hdim2, hRiff⟩ :=
    commuting_factors_absolutely_irreducible_tensor_decomposition.{u, 0} L hcomm hirr hend
  set R : Fin s → Submodule F (Module.End F W) := fun i =>
    Submodule.span F (Set.range fun l : L i => ((l : W ≃ₗ[F] W) : Module.End F W)) with hR
  have hRfin : ∀ i, Module.finrank F (R i) = Module.finrank F (V i) ^ 2 := fun i =>
    finrank_span_of_tensor e (R i) i (hRiff i)
  have hdim : ∀ i j, Module.finrank F (V i) = Module.finrank F (V j) := by
    intro i j
    obtain ⟨a, ha, hij⟩ := htrans i j
    have h1 : (R i).map (a.conjAlgEquiv F).toLinearMap = R j := conj_map_span a (L i) (L j) hij
    have h2 : Module.finrank F (R i) = Module.finrank F (R j) := by
      rw [← h1]
      exact (LinearEquiv.finrank_map_eq (a.conjAlgEquiv F).toLinearEquiv (R i)).symm
    rw [hRfin, hRfin] at h2
    exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) h2
  let i0 : Fin s := ⟨0, by omega⟩
  let τ : ∀ i, V i ≃ₗ[F] V i0 := fun i => LinearEquiv.ofFinrankEq (V i) (V i0) (hdim i i0)
  let e' : W ≃ₗ[F] ⨂[F] _ : Fin s, V i0 := e.trans (PiTensorProduct.congr τ)
  let A' : Subgroup ((⨂[F] _ : Fin s, V i0) ≃ₗ[F] ⨂[F] _ : Fin s, V i0) :=
    A.map (autConj e').toMonoidHom
  have hel' : CFSG.IsElementaryAbelian 2 ↥A' := isElementaryAbelian_map (autConj e').toMonoidHom A
  have hΨ : ∀ i (X : Module.End F (⨂[F] _ : Fin s, V i0)),
      X ∈ factorAlg (F := F) (V := fun _ : Fin s => V i0) i ↔
        ((e'.conjAlgEquiv F).symm X) ∈ R i := by
    intro i X
    rw [mem_factorAlg_const_iff e τ (R i) i (hRiff i) X]
    rfl
  have hmapeq : ∀ a ∈ A, ∀ i j, conjSub a (L i) = L j →
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map
        ((autConj e' a).conjAlgEquiv F).toAlgHom = factorAlg j := by
    intro a ha i j hj
    have hRj : (R i).map (a.conjAlgEquiv F).toLinearMap = R j := conj_map_span a (L i) (L j) hj
    have hkey : ∀ Y, (e'.conjAlgEquiv F).symm (((autConj e' a).conjAlgEquiv F) Y) =
        a.conjAlgEquiv F ((e'.conjAlgEquiv F).symm Y) := by
      intro Y
      have := conjAlgEquiv_autConj e' a ((e'.conjAlgEquiv F).symm Y)
      rw [AlgEquiv.apply_symm_apply] at this
      rw [this]
      exact AlgEquiv.symm_apply_apply _ _
    apply Subalgebra.ext
    intro X
    rw [Subalgebra.mem_map]
    constructor
    · rintro ⟨Y, hY, rfl⟩
      rw [hΨ] at hY ⊢
      have h1 : a.conjAlgEquiv F ((e'.conjAlgEquiv F).symm Y) ∈
          (R i).map (a.conjAlgEquiv F).toLinearMap := Submodule.mem_map_of_mem hY
      rw [hRj] at h1
      show (e'.conjAlgEquiv F).symm (((autConj e' a).conjAlgEquiv F) Y) ∈ R j
      rw [hkey]
      exact h1
    · intro hX
      rw [hΨ] at hX
      rw [← hRj] at hX
      obtain ⟨T, hT, hTX⟩ := hX
      refine ⟨e'.conjAlgEquiv F T, ?_, ?_⟩
      · rw [hΨ]
        simpa using hT
      · apply (e'.conjAlgEquiv F).symm.injective
        show (e'.conjAlgEquiv F).symm (((autConj e' a).conjAlgEquiv F) (e'.conjAlgEquiv F T)) =
          (e'.conjAlgEquiv F).symm X
        rw [hkey]
        have : (e'.conjAlgEquiv F).symm (e'.conjAlgEquiv F T) = T := AlgEquiv.symm_apply_apply _ _
        rw [this]
        exact hTX
  have hperm' : ∀ a' ∈ A', ∀ i, ∃ j,
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map (a'.conjAlgEquiv F).toAlgHom =
        factorAlg j := by
    rintro _ ⟨a, ha, rfl⟩ i
    obtain ⟨j, hj⟩ := hperm a ha i
    exact ⟨j, hmapeq a ha i j hj⟩
  have htrans' : ∀ i j, ∃ a' ∈ A',
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map (a'.conjAlgEquiv F).toAlgHom =
        factorAlg j := by
    intro i j
    obtain ⟨a, ha, hj⟩ := htrans i j
    exact ⟨autConj e' a, ⟨a, ha, rfl⟩, hmapeq a ha i j hj⟩
  let B' : Subgroup ((⨂[F] _ : Fin s, V i0) ≃ₗ[F] ⨂[F] _ : Fin s, V i0) :=
    B.map (autConj e').toMonoidHom
  have hBA' : B' ≤ A' := Subgroup.map_mono hBA
  have hB0' : B' ≠ ⊥ := fun h =>
    hB0 ((Subgroup.map_eq_bot_iff_of_injective B (autConj e').injective).1 h)
  have hBfix' : ∀ b' ∈ B', ∀ i,
      (factorAlg (F := F) (V := fun _ : Fin s => V i0) i).map (b'.conjAlgEquiv F).toAlgHom =
        factorAlg i := by
    rintro _ ⟨b, hb, rfl⟩ i
    exact hmapeq b (hBA hb) i i (hBfix b hb i)
  have hBq' : ∀ a' ∈ A', ∀ b' ∈ B', ∀ w, b' (a' w - w) = a' w - w := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
    have h1 := hBq a ha b hb (e'.symm w)
    rw [map_sub] at h1
    show (autConj e' b) ((autConj e' a) w - w) = (autConj e' a) w - w
    simp only [autConj_apply, map_sub, LinearEquiv.symm_apply_apply]
    rw [← map_sub e', h1, map_sub, LinearEquiv.apply_symm_apply]
  have hoffB' : Nat.card (⨂[F] _ : Fin s, V i0) ≤ Nat.card ↥B' * Nat.card ↥(fixGL B') :=
    natCard_le_weight_map_autConj e' B hoffB
  have hd : 2 ≤ Module.finrank F (V i0) := hdim2 i0 (hperf i0) (hnt i0)
  exact false_of_diagonal_tensor (F := F) (U := V i0) hd hs A' hperm' htrans' B' hBA' hB0'
    hBfix' hBq' hoffB'

theorem no_transitive_perfect_orbit_k_diag {k : Type*} [Field k] [CharP k 2] {W : Type u}
    [AddCommGroup W] [Module k W] [Finite W] [Nontrivial W] {s : ℕ} (hs : 2 ≤ s)
    (L : Fin s → Subgroup (W ≃ₗ[k] W))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x)
    (hperf : ∀ i, Group.IsPerfect ↥(L i)) (hnt : ∀ i, Nontrivial ↥(L i))
    (hirr : IsIrrAct (⨆ i, L i))
    (A : Subgroup (W ≃ₗ[k] W)) [CFSG.IsElementaryAbelian 2 A]
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, conjSub a (L i) = L j)
    (htrans : ∀ i j, ∃ a ∈ A, conjSub a (L i) = L j)
    (B : Subgroup (W ≃ₗ[k] W)) (hBA : B ≤ A) (hB0 : B ≠ ⊥)
    (hBfix : ∀ b ∈ B, ∀ i, conjSub b (L i) = L i)
    (hBq : ∀ a ∈ A, ∀ b ∈ B, ∀ w, b (a w - w) = a w - w)
    (hoffB : Nat.card W ≤ Nat.card B * Nat.card (fixGL B)) : False := by
  classical
  obtain ⟨F, hF, hFfin, hAlg, hMod, hTower, hcommut, hfinW, hspanF, habs, hsemi⟩ :=
    finite_irreducible_endomorphism_field_density.{u, 0, _} (⨆ i, L i) hirr
  have hFchar : CharP F 2 := charP_of_injective_algebraMap (algebraMap k F).injective 2
  have hlin : ∀ h ∈ (⨆ i, L i), ∀ (c : F) (w : W), h (c • w) = c • h w := by
    intro h hh c w
    let m : Module.End k W :=
      { toFun := fun w => c • w
        map_add' := fun x y => smul_add c x y
        map_smul' := fun a x => smul_comm c a x }
    have := (hcommut m).2 ⟨c, fun w => rfl⟩ h hh w
    exact this.symm
  have hnormA : ∀ a ∈ A, a ∈ Subgroup.normalizer ((⨆ i, L i : Subgroup (W ≃ₗ[k] W)) : Set _) := by
    have hle : ∀ a ∈ A, conjSub a (⨆ i, L i) ≤ ⨆ i, L i := by
      intro a ha
      rw [OrderIso.map_iSup]
      refine iSup_le fun i => ?_
      obtain ⟨j, hj⟩ := hperm a ha i
      rw [hj]
      exact le_iSup L j
    intro a ha
    exact mem_normalizer_of_conjSub_le (hle a ha) (hle a⁻¹ (A.inv_mem ha))
  have hsemiA : ∀ a ∈ A, ∃ σ : F ≃ₐ[k] F, ∀ (c : F) (w : W), a (c • w) = σ c • a w :=
    fun a ha => hsemi a (hnormA a ha)
  have hLle : ∀ i, L i ≤ (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)).range := fun i x hx =>
    mem_range_resK (hlin x (le_iSup L i hx))
  let LF : Fin s → Subgroup (W ≃ₗ[F] W) := fun i =>
    (L i).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
  have hLF : ∀ i, (LF i).map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = L i := fun i => by
    show ((L i).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))).map _ = L i
    rw [Subgroup.map_comap_eq, inf_eq_right.2 (hLle i)]
  have hLFperf : ∀ i, Group.IsPerfect ↥(LF i) := fun i =>
    isPerfect_of_map_eq _ resK_injective (LF i) (hLF i) (hperf i)
  have hLFnt : ∀ i, Nontrivial ↥(LF i) := fun i =>
    have := hnt i
    nontrivial_of_map_eq _ resK_injective (LF i) (hLF i) this
  let i0 : Fin s := ⟨0, by omega⟩
  let permHom : (W ≃ₗ[k] W) →* Equiv.Perm W :=
    { toFun := fun a => a.toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hpermHom : Function.Injective permHom := fun a b h =>
    LinearEquiv.ext fun w => congrArg (fun p : Equiv.Perm W => p w) h
  let Bperm : Subgroup (Equiv.Perm W) := B.map permHom
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := isElementaryAbelian_two_of_le hBA
  have hBpermEl : CFSG.IsElementaryAbelian 2 ↥Bperm := isElementaryAbelian_map permHom B
  have hBlin : ∀ b ∈ B, ∀ (c : F) (w : W), b (c • w) = c • b w := by
    have hoffP : Nat.card W ≤ Nat.card ↥Bperm * Nat.card {w : W // ∀ a ∈ Bperm, a w = w} := by
      have h1 : Nat.card ↥Bperm = Nat.card ↥B := Subgroup.card_map_of_injective hpermHom
      have h2 : Nat.card {w : W // ∀ a ∈ Bperm, a w = w} = Nat.card ↥(fixGL B) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun w => by
          constructor
          · intro h a ha
            exact h (permHom a) ⟨a, ha, rfl⟩
          · rintro h _ ⟨a, ha, rfl⟩
            exact h a ha)
      rw [h1, h2]
      exact hoffB
    have key := no_field_action_of_perfect (F := F) (W := W) Bperm
      (by rintro _ ⟨a, ha, rfl⟩ x y; exact map_add a x y)
      (by
        rintro _ ⟨a, ha, rfl⟩
        obtain ⟨σ, hσ⟩ := hsemiA a (hBA ha)
        exact ⟨σ.toRingEquiv, fun c w => hσ c w⟩)
      (by rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w; exact hBq a (hBA ha) b hb w)
      hoffP (LF i0) (((Subgroup.nontrivial_iff_ne_bot _).1 (hLFnt i0))) (hLFperf i0)
    intro b hb c w
    have := (key (permHom b) ⟨b, hb, rfl⟩).2 c w
    exact this
  have hsq : ∀ a : A, a * a = 1 := fun a => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
    rwa [pow_two] at this
  have hAlin : ∀ a ∈ A, ∀ (c : F) (w : W), a (c • w) = c • a w := by
    intro a ha
    obtain ⟨σ, hσ⟩ := hsemiA a ha
    by_cases hσ1 : σ.toRingEquiv = 1
    · intro c w
      have hc : σ c = c := by
        have := congrArg (fun τ : F ≃+* F => τ c) hσ1
        simpa using this
      rw [hσ c w, hc]
    · exfalso
      obtain ⟨b₀, hb₀⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB0
      have hsem : IsSemilinearWith (permHom a) σ.toRingEquiv := fun c w => hσ c w
      have hb : IsSemilinearWith (permHom (b₀ : W ≃ₗ[k] W)) (1 : F ≃+* F) :=
        fun c w => hBlin b₀ b₀.2 c w
      have ha1 : a * a = 1 := congrArg Subtype.val (hsq ⟨a, ha⟩)
      have ha2' : permHom a * permHom a = 1 := by
        rw [← map_mul, ha1, map_one]
      have hσ2 : σ.toRingEquiv * σ.toRingEquiv = 1 := sq_eq_one_of_semilinear ha2' hsem
      have htr := exists_trace_eq_one σ.toRingEquiv hσ1 hσ2
      have hone := eq_one_of_fixes_image hsem hb (fun x y => map_add a x y)
        (fun x y => map_add (b₀ : W ≃ₗ[k] W) x y)
        (fun w => by
          have := congrArg (fun p : Equiv.Perm W => p w) ha2'
          simpa using this) hσ1 hσ2 htr
        (fun x => hBq a ha b₀ b₀.2 x)
      have hb1 : (b₀ : W ≃ₗ[k] W) = 1 := hpermHom (by rw [hone, map_one])
      exact hb₀ (Subtype.ext hb1)
  have hAle : A ≤ (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)).range := fun x hx =>
    mem_range_resK (hAlin x hx)
  let AF : Subgroup (W ≃ₗ[F] W) := A.comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
  have hAF : AF.map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = A := by
    show (A.comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))).map _ = A
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hAle]
  have hAFel : CFSG.IsElementaryAbelian 2 ↥AF :=
    isElementaryAbelian_comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) resK_injective A
  have hBle : B ≤ (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)).range := fun x hx =>
    mem_range_resK (hBlin x hx)
  let BF : Subgroup (W ≃ₗ[F] W) := B.comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
  have hBF : BF.map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = B := by
    show (B.comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))).map _ = B
    rw [Subgroup.map_comap_eq, inf_eq_right.2 hBle]
  have hcommF : ∀ i j, i ≠ j → ∀ x ∈ LF i, ∀ y ∈ LF j, x * y = y * x := by
    intro i j hij x hx y hy
    apply resK_injective (F := F) (k := k) (W := W)
    rw [map_mul, map_mul]
    exact hcomm i j hij _ hx _ hy
  have hHF : (⨆ i, LF i).map (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W)) = ⨆ i, L i := by
    rw [Subgroup.map_iSup]
    exact iSup_congr hLF
  have hirrF : IsIrrAct (⨆ i, LF i) := by
    intro U hU
    have hUk : ∀ h ∈ (⨆ i, L i), ∀ u ∈ U.restrictScalars k, h u ∈ U.restrictScalars k := by
      intro h hh u hu
      rw [← hHF] at hh
      obtain ⟨y, hy, rfl⟩ := hh
      exact hU y hy u hu
    rcases hirr (U.restrictScalars k) hUk with h | h
    · left
      exact (Submodule.restrictScalars_eq_bot_iff k F W).1 h
    · right
      exact (Submodule.restrictScalars_eq_top_iff k F W).1 h
  have hendF : ∀ f : Module.End F W, (∀ h ∈ ⨆ i, LF i, ∀ w, f (h w) = h (f w)) →
      ∃ c : F, ∀ w, f w = c • w := by
    intro f hf
    have hfk : ∀ h ∈ (⨆ i, L i), ∀ w,
        (f.restrictScalars k) (h w) = h ((f.restrictScalars k) w) := by
      intro h hh w
      rw [← hHF] at hh
      obtain ⟨y, hy, rfl⟩ := hh
      exact hf y hy w
    exact (hcommut (f.restrictScalars k)).1 hfk
  have hconjF : ∀ a ∈ AF, ∀ i j, conjSub (resK k a) (L i) = L j → conjSub a (LF i) = LF j := by
    intro a ha i j h
    show conjSub a ((L i).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))) =
      (L j).comap (resK k : (W ≃ₗ[F] W) →* (W ≃ₗ[k] W))
    rw [conjSub_comap, h]
  have hpermF : ∀ a ∈ AF, ∀ i, ∃ j, conjSub a (LF i) = LF j := fun a ha i =>
    (hperm (resK k a) ha i).imp fun j hj => hconjF a ha i j hj
  have htransF : ∀ i j, ∃ a ∈ AF, conjSub a (LF i) = LF j := by
    intro i j
    obtain ⟨a, ha, h⟩ := htrans i j
    obtain ⟨af, rfl⟩ := hAle ha
    exact ⟨af, ha, hconjF af ha i j h⟩
  have hBFA : BF ≤ AF := fun b hb => hBA hb
  have hBF0 : BF ≠ ⊥ := by
    intro h
    apply hB0
    rw [← hBF, h, Subgroup.map_bot]
  have hBFfix : ∀ b ∈ BF, ∀ i, conjSub b (LF i) = LF i := fun b hb i =>
    hconjF b (hBFA hb) i i (hBfix (resK k b) hb i)
  have hBFq : ∀ a ∈ AF, ∀ b ∈ BF, ∀ w, b (a w - w) = a w - w := fun a ha b hb w =>
    hBq (resK k a) ha (resK k b) hb w
  have hoffBF : Nat.card W ≤ Nat.card ↥BF * Nat.card ↥(fixGL BF) := by
    have h1 : Nat.card ↥BF = Nat.card ↥B := by
      rw [← hBF]
      exact (Subgroup.card_map_of_injective resK_injective).symm
    have h2 : Nat.card ↥(fixGL BF) = Nat.card ↥(fixGL B) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun w => by
        constructor
        · intro h a ha
          obtain ⟨bf, rfl⟩ := hBle ha
          exact h bf ha
        · intro h bf hbf
          exact h (resK k bf) hbf)
    rw [h1, h2]
    exact hoffB
  exact no_transitive_perfect_orbit_diag hs LF hcommF hLFperf hLFnt hirrF hendF AF hpermF htransF
    BF hBFA hBF0 hBFfix hBFq hoffBF

end CFSG.Quasithin.B15P4
