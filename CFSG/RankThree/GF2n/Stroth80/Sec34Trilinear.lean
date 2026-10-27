module

public import CFSG.RankThree.GF2n.Stroth80.Sec34Eichler

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.RankThree.GF2n

section Flag

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

structure FlagData (M₀ : Tim79.QuadModel QF V K γ) (b : M₀.E) (W : Submodule K M₀.E)
    (Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)) : Prop where
  hb0 : b ≠ 0
  hbW : b ∈ W
  hWs : ∀ w ∈ W, M₀.Qf w = 0
  hWperp : ∀ v, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W
  iso : ∀ T ∈ Λ, ∀ e, M₀.Qf (T e) = M₀.Qf e
  fix : ∀ T ∈ Λ, T b = b
  flag2 : ∀ T ∈ Λ, ∀ y, M₀.B y b = 0 → T y - y ∈ W
  flag3 : ∀ T ∈ Λ, ∀ e ∈ W, ∃ c : K, T e - e = c • b
  comm : ∀ T ∈ Λ, ∀ T' ∈ Λ, T * T' = T' * T

@[expose] def flagPsi (M₀ : Tim79.QuadModel QF V K γ) (f₀ : M₀.E) (T : M₀.E ≃ₗ[K] M₀.E)
    (d : M₀.E) : K :=
  M₀.B f₀ (T d - d)

variable {M₀ : Tim79.QuadModel QF V K γ} {b : M₀.E} {W : Submodule K M₀.E}
  {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {f₀ : M₀.E}

theorem FlagData.B_eq_zero (hΛ : FlagData M₀ b W Λ) {u v : M₀.E} (hu : u ∈ W) (hv : v ∈ W) :
    M₀.B u v = 0 := by
  have h := M₀.Qf_add u v
  rw [hΛ.hWs _ (W.add_mem hu hv), hΛ.hWs u hu, hΛ.hWs v hv] at h
  simpa using h.symm

theorem FlagData.sub_eq (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) {d : M₀.E} (hd : d ∈ W) :
    T d - d = flagPsi M₀ f₀ T d • b := by
  obtain ⟨c, hc⟩ := hΛ.flag3 T hT d hd
  have : flagPsi M₀ f₀ T d = c := by
    simp only [flagPsi, hc, map_smul, hf₀, smul_eq_mul, mul_one]
  rw [this, hc]

theorem FlagData.psi_comm (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    {T T' : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (hT' : T' ∈ Λ) {y : M₀.E} (hy : M₀.B y b = 0) :
    flagPsi M₀ f₀ T (T' y - y) = flagPsi M₀ f₀ T' (T y - y) := by
  have hW' : T' y - y ∈ W := hΛ.flag2 T' hT' y hy
  have hW : T y - y ∈ W := hΛ.flag2 T hT y hy
  have e1 := hΛ.sub_eq hf₀ hT hW'
  have e2 := hΛ.sub_eq hf₀ hT' hW
  have hTT : T (T' y) = T' (T y) := by
    have := congrArg (fun S : M₀.E ≃ₗ[K] M₀.E => S y) (hΛ.comm T hT T' hT')
    simpa using this
  have : flagPsi M₀ f₀ T (T' y - y) • b = flagPsi M₀ f₀ T' (T y - y) • b := by
    rw [← e1, ← e2, map_sub, map_sub, hTT]
    abel
  exact smul_left_injective K hΛ.hb0 this

theorem FlagData.beta_symm (hΛ : FlagData M₀ b W Λ) {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ)
    {y y' : M₀.E} (hy : M₀.B y b = 0) (hy' : M₀.B y' b = 0) :
    M₀.B y (T y' - y') = M₀.B y' (T y - y) := by
  have hiso : ∀ e f, M₀.B (T e) (T f) = M₀.B e f := fun e f =>
    Tim79.QuadModel.B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) (hΛ.iso T hT) e f
  have hW : T y - y ∈ W := hΛ.flag2 T hT y hy
  have hW' : T y' - y' ∈ W := hΛ.flag2 T hT y' hy'
  have hNN : M₀.B (T y - y) (T y' - y') = 0 := hΛ.B_eq_zero hW hW'
  obtain ⟨a, ha⟩ : ∃ a, a = T y - y := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = T y' - y' := ⟨_, rfl⟩
  have e1 : T y = y + a := by rw [ha]; abel
  have e2 : T y' = y' + a' := by rw [ha']; abel
  have h := hiso y y'
  rw [e1, e2] at h
  rw [← ha] at hNN
  rw [← ha'] at hNN
  simp only [map_add, LinearMap.add_apply] at h
  rw [← ha, ← ha']
  have hc := Tim79.QuadModel.B_comm a y'
  linear_combination h - hc - hNN

theorem FlagData.eq_of_psi_eq (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1)
    {T T' : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (hT' : T' ∈ Λ)
    (h : ∀ d ∈ W, flagPsi M₀ f₀ T d = flagPsi M₀ f₀ T' d) : T = T' := by
  have hS : T⁻¹ * T' ∈ Λ := Λ.mul_mem (Λ.inv_mem hT) hT'
  have h1 : ∀ e ∈ W, (T⁻¹ * T') e = e := by
    intro e he
    have e1 := hΛ.sub_eq hf₀ hT he
    have e2 := hΛ.sub_eq hf₀ hT' he
    rw [h e he] at e1
    have h2 : T e = T' e := sub_left_injective (e1.trans e2.symm)
    show T.symm (T' e) = e
    rw [← h2]
    exact T.symm_apply_apply e
  exact inv_mul_eq_one.mp (hinj _ hS h1)

@[expose] def flagPsiLin (M₀ : Tim79.QuadModel QF V K γ) (W : Submodule K M₀.E) (f₀ : M₀.E)
    (T : M₀.E ≃ₗ[K] M₀.E) : W →ₗ[K] K :=
  (M₀.B f₀).comp (((T : M₀.E →ₗ[K] M₀.E) - LinearMap.id).comp W.subtype)

theorem flagPsiLin_apply (T : M₀.E ≃ₗ[K] M₀.E) (d : W) :
    flagPsiLin M₀ W f₀ T d = flagPsi M₀ f₀ T d := by
  simp [flagPsiLin, flagPsi]

theorem FlagData.psiLin_b (hΛ : FlagData M₀ b W Λ) {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) :
    flagPsiLin M₀ W f₀ T ⟨b, hΛ.hbW⟩ = 0 := by
  rw [flagPsiLin_apply]
  simp [flagPsi, hΛ.fix T hT]

theorem FlagData.psi_surj [Finite K] (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1) {n : ℕ}
    (hHom0 : Nat.card {φ : W →ₗ[K] K // φ ⟨b, hΛ.hbW⟩ = 0} = Nat.card K ^ (n - 1))
    (hcard : Nat.card Λ = Nat.card K ^ (n - 1))
    (φ : W →ₗ[K] K) (hφ : φ ⟨b, hΛ.hbW⟩ = 0) :
    ∃ T ∈ Λ, ∀ d : W, flagPsi M₀ f₀ T d = φ d := by
  let Ψ : Λ → {φ : W →ₗ[K] K // φ ⟨b, hΛ.hbW⟩ = 0} := fun T =>
    ⟨flagPsiLin M₀ W f₀ T.1, hΛ.psiLin_b T.2⟩
  have hinjΨ : Function.Injective Ψ := by
    intro T T' hTT
    have h2 : ∀ d ∈ W, flagPsi M₀ f₀ T.1 d = flagPsi M₀ f₀ T'.1 d := by
      intro d hd
      have := congrArg (fun z => z.1 ⟨d, hd⟩) hTT
      simpa [Ψ, flagPsiLin_apply] using this
    exact Subtype.ext (hΛ.eq_of_psi_eq hinj hf₀ T.2 T'.2 h2)
  have hfin : Finite {φ : W →ₗ[K] K // φ ⟨b, hΛ.hbW⟩ = 0} := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hHom0]
    exact pow_ne_zero _ (Nat.card_pos (α := K)).ne'
  have hbij : Function.Bijective Ψ :=
    (Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinjΨ, by rw [hcard, hHom0]⟩
  obtain ⟨T, hT⟩ := hbij.2 ⟨φ, hφ⟩
  refine ⟨T.1, T.2, fun d => ?_⟩
  have := congrArg (fun z => z.1 d) hT
  simpa [Ψ, flagPsiLin_apply] using this

theorem FlagData.key (hΛ : FlagData M₀ b W Λ) (hf₀ : M₀.B f₀ b = 1)
    (hsurj : ∀ φ : W →ₗ[K] K, φ ⟨b, hΛ.hbW⟩ = 0 →
      ∃ T ∈ Λ, ∀ d : W, flagPsi M₀ f₀ T d = φ d)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) {y : M₀.E} (hy : M₀.B y b = 0)
    (hTy : ∀ d : W, flagPsi M₀ f₀ T d = M₀.B (d : M₀.E) y) :
    (∀ T' ∈ Λ, T' y - y ∈ Submodule.span K {b}) ↔
      ∀ y'', M₀.B y'' b = 0 → T y'' - y'' ∈ Submodule.span K {b} := by
  constructor
  · intro hF y'' hy''
    obtain ⟨c, hc⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hΛ.hb0
      (v := T y'' - y'') (fun u hu => by
        have hφ : ((M₀.B.flip u).comp W.subtype) ⟨b, hΛ.hbW⟩ = 0 := by
          simp [Tim79.QuadModel.B_comm b u, hu]
        obtain ⟨T', hT', hT'u⟩ := hsurj _ hφ
        have h1 := hΛ.psi_comm hf₀ hT hT' hy''
        have h2 := hTy ⟨T' y'' - y'', hΛ.flag2 T' hT' y'' hy''⟩
        have h3 := hT'u ⟨T y'' - y'', hΛ.flag2 T hT y'' hy''⟩
        simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply] at h3
        rw [h1, h3] at h2
        have h2' : M₀.B (T y'' - y'') u = M₀.B (T' y'' - y'') y := h2
        obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp (hF T' hT')
        have h4 := hΛ.beta_symm hT' hy hy''
        rw [← hc'] at h4
        rw [h2', Tim79.QuadModel.B_comm (T' y'' - y'') y, h4]
        simp [hy''])
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · intro hS T' hT'
    obtain ⟨c, hc⟩ := Tim79.QuadModel.exists_smul_of_orthogonal hΛ.hb0
      (v := T' y - y) (fun u hu => by
        have h1 := hΛ.beta_symm hT' hu hy
        have h2 : flagPsi M₀ f₀ T (T' u - u) = M₀.B (T' u - u) y :=
          hTy ⟨T' u - u, hΛ.flag2 T' hT' u hu⟩
        have h3 := hΛ.psi_comm hf₀ hT hT' hu
        obtain ⟨c', hc'⟩ := Submodule.mem_span_singleton.mp (hS u hu)
        have h4 : flagPsi M₀ f₀ T' (T u - u) = 0 := by
          rw [← hc']
          simp [flagPsi, hΛ.fix T' hT']
        rw [h4] at h3
        rw [Tim79.QuadModel.B_comm (T' y - y) u, h1, Tim79.QuadModel.B_comm y (T' u - u),
          ← h2, h3]
        simp)
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩

theorem FlagData.card_ΛS [Finite K] (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1) {n : ℕ}
    (hWdim : Module.finrank K W = n)
    (hHom0 : Nat.card {φ : W →ₗ[K] K // φ ⟨b, hΛ.hbW⟩ = 0} = Nat.card K ^ (n - 1))
    (hcard : Nat.card Λ = Nat.card K ^ (n - 1))
    (hrep : ∀ φ : W →ₗ[K] K, φ ⟨b, hΛ.hbW⟩ = 0 →
      ∃ a : M₀.E, M₀.B a b = 0 ∧ ∀ d : W, M₀.B (d : M₀.E) a = φ d)
    (F : Submodule K M₀.E)
    (hF : ∀ y, y ∈ F ↔ M₀.B y b = 0 ∧ ∀ T ∈ Λ, T y - y ∈ Submodule.span K {b})
    (ΛS : Subgroup (M₀.E ≃ₗ[K] M₀.E))
    (hΛS : ∀ T, T ∈ ΛS ↔ T ∈ Λ ∧ ∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span K {b}) :
    ∃ d : ℕ, Nat.card ΛS = Nat.card K ^ d ∧ Module.finrank K F = n + d := by
  haveI : Module.Finite K M₀.E := M₀.fin
  have hsurj := hΛ.psi_surj hinj hf₀ hHom0 hcard
  have hWF : W ≤ F := fun d hd =>
    (hF d).mpr ⟨hΛ.B_eq_zero hd hΛ.hbW, fun T hT => by
      obtain ⟨c, hc⟩ := hΛ.flag3 T hT d hd
      exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩⟩
  let LF : M₀.E →ₗ[K] (W →ₗ[K] K) := (LinearMap.lcomp K K W.subtype).comp M₀.B.flip
  have hLF : ∀ (a : M₀.E) (d : W), LF a d = M₀.B (d : M₀.E) a := fun a d => rfl
  let LFF : F →ₗ[K] (W →ₗ[K] K) := LF.domRestrict F
  have hker : LinearMap.ker LFF = W.comap F.subtype := by
    ext a
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro h
      refine hΛ.hWperp a fun u hu => ?_
      have := LinearMap.congr_fun h ⟨u, hu⟩
      have h2 : M₀.B u (a : M₀.E) = 0 := this
      rw [Tim79.QuadModel.B_comm, h2, neg_zero]
    · intro h
      refine LinearMap.ext fun d => ?_
      exact hΛ.B_eq_zero d.2 h
  have hkerdim : Module.finrank K (LinearMap.ker LFF) = n := by
    rw [hker, ← hWdim]
    exact (Submodule.comapSubtypeEquivOfLe hWF).finrank_eq
  have hmem : ∀ T ∈ ΛS, flagPsiLin M₀ W f₀ T ∈ LinearMap.range LFF := by
    intro T hTS
    have hT := (hΛS T).mp hTS
    obtain ⟨a, hab, haW⟩ := hrep (flagPsiLin M₀ W f₀ T) (hΛ.psiLin_b hT.1)
    have hTy : ∀ d : W, flagPsi M₀ f₀ T d = M₀.B (d : M₀.E) a := fun d => by
      rw [haW d, flagPsiLin_apply]
    have haF : a ∈ F := (hF a).mpr ⟨hab, (hΛ.key hf₀ hsurj hT.1 hab hTy).mpr hT.2⟩
    exact ⟨⟨a, haF⟩, LinearMap.ext fun d => by
      rw [flagPsiLin_apply]; exact (hTy d).symm⟩
  let Θ : ΛS → LinearMap.range LFF := fun T => ⟨flagPsiLin M₀ W f₀ T.1, hmem T.1 T.2⟩
  have hΘ : Function.Bijective Θ := by
    constructor
    · intro T T' hTT
      have h2 : ∀ d ∈ W, flagPsi M₀ f₀ T.1 d = flagPsi M₀ f₀ T'.1 d := by
        intro d hd
        have := congrArg (fun z => z.1 ⟨d, hd⟩) hTT
        simpa [Θ, flagPsiLin_apply] using this
      exact Subtype.ext (hΛ.eq_of_psi_eq hinj hf₀ ((hΛS T.1).mp T.2).1 ((hΛS T'.1).mp T'.2).1 h2)
    · rintro ⟨φ, ⟨a, rfl⟩⟩
      have haF := a.2
      have hφ : LFF a ⟨b, hΛ.hbW⟩ = 0 := by
        show M₀.B b (a : M₀.E) = 0
        rw [Tim79.QuadModel.B_comm, ((hF a).mp haF).1, neg_zero]
      obtain ⟨T, hT, hTφ⟩ := hsurj _ hφ
      have hTy : ∀ d : W, flagPsi M₀ f₀ T d = M₀.B (d : M₀.E) a := fun d => hTφ d
      have hTS : T ∈ ΛS := (hΛS T).mpr ⟨hT, (hΛ.key hf₀ hsurj hT ((hF a).mp haF).1 hTy).mp
        ((hF a).mp haF).2⟩
      refine ⟨⟨T, hTS⟩, Subtype.ext (LinearMap.ext fun d => ?_)⟩
      simp only [Θ, flagPsiLin_apply]
      exact hTφ d
  have hcardΘ : Nat.card ΛS = Nat.card (LinearMap.range LFF) :=
    Nat.card_congr (Equiv.ofBijective Θ hΘ)
  refine ⟨Module.finrank K (LinearMap.range LFF), ?_, ?_⟩
  · rw [hcardΘ]
    exact Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range LFF)
  · have := LinearMap.finrank_range_add_finrank_ker LFF
    omega

end Flag

section DualLemmas

theorem card_dual_ker_eval {K V' : Type*} [Field K] [Finite K] [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V'] {n : ℕ} (hW : Module.finrank K V' = n) (v : V') (hv : v ≠ 0) :
    Nat.card {φ : V' →ₗ[K] K // φ v = 0} = Nat.card K ^ (n - 1) := by
  obtain ⟨e, he⟩ : ∃ e : Module.Dual K V' →ₗ[K] K, ∀ ψ : Module.Dual K V', e ψ = ψ v :=
    ⟨Module.Dual.eval K V' v, fun ψ => rfl⟩
  have he_ne : e ≠ 0 := by
    intro h
    refine hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun ψ => ?_)
    rw [← he ψ, h, LinearMap.zero_apply]
  have hsurj : Function.Surjective e := by
    obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K V', e ψ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he_ne (LinearMap.ext fun ψ => by simp [hcon ψ])
    intro c
    exact ⟨(c / e ψ) • ψ, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hψ]⟩
  have hr : Module.finrank K (LinearMap.range e) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker e
  rw [hr, Subspace.dual_finrank_eq, hW] at hrn
  have hk : Module.finrank K (LinearMap.ker e) = n - 1 := by omega
  have hc : Nat.card {φ : V' →ₗ[K] K // φ v = 0} = Nat.card (LinearMap.ker e) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun φ => by rw [LinearMap.mem_ker, he φ])
  have hcard := Module.natCard_eq_pow_finrank (K := K) (V := ↥(LinearMap.ker e))
  rw [hc, hcard]
  exact congrArg (fun m => Nat.card K ^ m) hk

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem exists_perp_rep (M₀ : Tim79.QuadModel QF V K γ) (W : Submodule K M₀.E) {b : M₀.E}
    (hbW : b ∈ W) (φ : W →ₗ[K] K) (hφ : φ ⟨b, hbW⟩ = 0) :
    ∃ a : M₀.E, M₀.B a b = 0 ∧ ∀ d : W, M₀.B (d : M₀.E) a = φ d := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  have hgW : ∀ d : W, g (d : M₀.E) = φ d := fun d => by
    simpa using LinearMap.congr_fun hg d
  have hgb : g b = 0 := (hgW ⟨b, hbW⟩).trans hφ
  have hnd : M₀.B.Nondegenerate := by
    refine ⟨fun x hx => M₀.nondeg x hx, fun y hy => M₀.nondeg y fun f => ?_⟩
    rw [Tim79.QuadModel.B_comm, hy f, neg_zero]
  obtain ⟨v, hv⟩ : ∃ v : M₀.E, ∀ e : M₀.E, M₀.B v e = g e :=
    ⟨(M₀.B.toDual hnd).symm g, fun e => LinearMap.BilinForm.apply_toDual_symm_apply g e⟩
  refine ⟨-v, ?_, fun d => ?_⟩
  · rw [map_neg, LinearMap.neg_apply, hv b, hgb, neg_zero]
  · rw [map_neg, Tim79.QuadModel.B_comm, neg_neg, hv]
    exact hgW d

end DualLemmas

section GroupSide

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

omit [Finite G] in
theorem exists_le_sup_span_of_finrank_le {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W F : Submodule K V} (hWF : W ≤ F)
    (hdim : Module.finrank K F ≤ Module.finrank K W + 1) :
    ∃ f : V, F ≤ W ⊔ Submodule.span K {f} := by
  by_cases hF : F ≤ W
  · exact ⟨0, hF.trans le_sup_left⟩
  · obtain ⟨f, hfF, hfW⟩ := Set.not_subset.mp hF
    have hle : W ⊔ Submodule.span K {f} ≤ F :=
      sup_le hWF (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hfF))
    have hlt : W < W ⊔ Submodule.span K {f} := by
      refine lt_of_le_of_ne le_sup_left fun h => hfW ?_
      rw [h]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : Module.finrank K F ≤ Module.finrank K ↥(W ⊔ Submodule.span K {f}) := by omega
    exact ⟨f, (Submodule.eq_of_le_of_finrank_le hle h2).ge⟩

theorem Ctx.LB_le_H0_cb (hc : Ctx M Q Z B) : LB M Q B ≤ H0 M Z := fun t ht =>
  ⟨hc.LB_le_M ht, Subgroup.mem_centralizer_iff.mpr fun z hz => by
    have := hc.LB_centralizes_Z ht z hz
    calc z * t = (t * z * t⁻¹) * t := by rw [this]
      _ = t * z := by group⟩

theorem Ctx.mem_Q_of_comm_inf_QB (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {l : G} (hl : l ∈ QB B ⊓ M)
    (hlD : ∀ d ∈ Q ⊓ QB B, ⁅l, d⁆ ∈ Z) : l ∈ Q := by
  have hD : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (hc.card_of_3_3 hw (by omega) hno (stroth_3_3 hc hw (by omega))).2
  obtain ⟨g, hg⟩ := hc.conj
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  obtain ⟨K, _, _, _, γ, M₀, hGM⟩ := stroth_globalModelData hc.hyp
  have hK2 : (2 : K) = 0 := by simpa using CharP.cast_eq_zero K 2
  have hKV : Nat.card K = Nat.card (conjSubgroup g Z) := by
    rw [card_conjSubgroup, hGM.card]
  have hw' : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hw
  have hQF : Nat.card (conjSubgroup g Q) = Nat.card (conjSubgroup g Z) ^ (2 * n + 1) := by
    rw [card_conjSubgroup, card_conjSubgroup, hw']
  have R' := Tim79.GammaReg.conj hGM.reg g
  have hE := Stroth57D.finrank_of_card (M₀.conj g) R' hKV hQF
  have hDQF : Q ⊓ QB B ≤ conjSubgroup g Q := fun x hx => by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hx).2
  have hVD : conjSubgroup g Z ≤ Q ⊓ QB B := by
    rw [← hg]
    exact le_inf hc.le hc.B_le_QB
  have hDc : ∀ x ∈ Q ⊓ QB B, ∀ y ∈ Q ⊓ QB B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDcard : Nat.card ↥(Q ⊓ QB B) = Nat.card K ^ (n + 1) := by
    rw [hD, hGM.card]
  have hl' : l ∈ conjSubgroup g Q := by
    rw [← hQB]
    exact (Subgroup.mem_inf.mp hl).1
  have hcomm : ∀ d ∈ Q ⊓ QB B, l * d = d * l := by
    intro d hd
    have h2 : ⁅l, d⁆ ∈ B := by
      rw [hg]
      exact (M₀.conj g).comm_mem l hl' d (hDQF hd)
    have h3 : ⁅l, d⁆ ∈ Z ⊓ B := Subgroup.mem_inf.mpr ⟨hlD d hd, h2⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h3
    exact h3
  exact (Subgroup.mem_inf.mp (Stroth57D.mem_of_comm (M₀.conj g) R' hK2 hKV hE hDQF hVD hDc
    hDcard hl' hcomm)).1

theorem Ctx.mem_Q_of_comm_inf_QB_LB (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) {r : G} (hr : r ∈ LB M Q B)
    (hrD : ∀ d ∈ Q ⊓ QB B, ⁅r, d⁆ ∈ Z) : r ∈ Q := by
  obtain ⟨s, hs, y, hy, rfl⟩ := hc.exists_mul_of_mem_LB hr
  have hsZ : ∀ z ∈ Z, s * z * s⁻¹ ∈ Z := fun z hz =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hs.2) z).mp hz
  have hs' : s ∈ Q := by
    refine hc.mem_Q_of_comm_inf_QB hw hn hno hs fun d hd => ?_
    have e : ⁅s * y, d⁆ = (s * ⁅y, d⁆ * s⁻¹) * ⁅s, d⁆ := by
      simp only [commutatorElement_def]; group
    have h1 : ⁅y, d⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hy (Subgroup.mem_inf.mp hd).1
    have h2 : ⁅s, d⁆ = (s * ⁅y, d⁆ * s⁻¹)⁻¹ * ⁅s * y, d⁆ := by rw [e]; group
    rw [h2]
    exact Z.mul_mem (Z.inv_mem (hsZ _ h1)) (hrD d hd)
  exact Q.mul_mem hs' hy

section Glue

variable {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem Ctx.card_Spure_eq_pow (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n) (hn : 2 < n)
    (hno : NoA2 Q Z (LB M Q B)) (h : GlobalModelData M Q Z γ M₀) (hLH0 : LB M Q B ≤ H0 M Z)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x))
    (hφker : ∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q)
    (hφiso : ∀ (m : H0 M Z) e, M₀.Qf (φ m e) = M₀.Qf e)
    {b : M₀.E} (hb0 : b ≠ 0) (hB : ∀ v : M₀.E, v ∈ M₀.img B ↔ ∃ s : K, v = s • b)
    (hcent : ∀ x ∈ Q, x ∈ Subgroup.centralizer (B : Set G) ↔ M₀.B (M₀.π x) b = 0)
    (W : Submodule K M₀.E) (hWmem : ∀ e, e ∈ M₀.img (Q ⊓ QB B) ↔ e ∈ W)
    (hWdim : Module.finrank K W = n) (hWperp : ∀ v, (∀ u ∈ W, M₀.B v u = 0) → v ∈ W)
    (hbW : b ∈ W)
    (hHom0 : Nat.card {ψ : W →ₗ[K] K // ψ ⟨b, hbW⟩ = 0} = Nat.card K ^ (n - 1))
    (hrep : ∀ ψ : W →ₗ[K] K, ψ ⟨b, hbW⟩ = 0 →
      ∃ a : M₀.E, M₀.B a b = 0 ∧ ∀ d : W, M₀.B (d : M₀.E) a = ψ d) :
    ∃ d : ℕ, Nat.card hc.Spure = Nat.card Q * Nat.card K ^ d ∧
      (d ≤ 1 → ∃ f : M₀.E, ∀ y, M₀.B y b = 0 →
        (∀ r : ↥(LB M Q B), φ (Subgroup.inclusion hLH0 r) y - y ∈ Submodule.span K {b}) →
          y ∈ W ⊔ Submodule.span K {f}) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hSH0 : hc.Spure ≤ H0 M Z := hc.Spure_le_H0
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hQS : Q ≤ hc.Spure := hc.Q_le_Spure
  let ΦL : ↥(LB M Q B) →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hLH0)
  let ΦS : ↥hc.Spure →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hSH0)
  have hΦLπ : ∀ (r : ↥(LB M Q B)) (x : G), x ∈ Q →
      M₀.π ((r : G) * x * (r : G)⁻¹) = ΦL r (M₀.π x) := fun r x hx =>
    hφπ (Subgroup.inclusion hLH0 r) x hx
  have hΦSπ : ∀ (s : ↥hc.Spure) (x : G), x ∈ Q →
      M₀.π ((s : G) * x * (s : G)⁻¹) = ΦS s (M₀.π x) := fun s x hx =>
    hφπ (Subgroup.inclusion hSH0 s) x hx
  have hΦLker : ∀ r : ↥(LB M Q B), ΦL r = 1 ↔ (r : G) ∈ Q := fun r =>
    hφker (Subgroup.inclusion hLH0 r)
  have hΦSker : ∀ s : ↥hc.Spure, ΦS s = 1 ↔ (s : G) ∈ Q := fun s =>
    hφker (Subgroup.inclusion hSH0 s)
  have hcardL : Nat.card (LB M Q B) = Nat.card Q * Nat.card ΦL.range := by
    have hker : ΦL.ker = Q.subgroupOf (LB M Q B) := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hΦLker r
    have h1 : Nat.card ΦL.ker = Nat.card Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQL).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hcardS : Nat.card hc.Spure = Nat.card Q * Nat.card ΦS.range := by
    have hker : ΦS.ker = Q.subgroupOf hc.Spure := by
      ext s
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hΦSker s
    have h1 : Nat.card ΦS.ker = Nat.card Q := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQS).toEquiv
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hcardΛ : Nat.card ΦL.range = Nat.card K ^ (n - 1) := by
    have h33 := (hc.card_of_3_3 hw hn1 hno (stroth_3_3 hc hw hn1)).1
    rw [hcardL] at h33
    rw [Nat.eq_of_mul_eq_mul_left Nat.card_pos h33, h.card]
  have hWs : ∀ w ∈ W, M₀.Qf w = 0 := fun w hw' =>
    (M₀.isElemAbelian_iff h.reg (inf_le_left : Q ⊓ QB B ≤ Q)).mp hc.inf_QB_elemAbelian w
      ((hWmem w).mpr hw')
  have hfix : ∀ r : ↥(LB M Q B), ΦL r b = b := by
    intro r
    obtain ⟨u, huB, huQ, hu⟩ : b ∈ M₀.img B := (hB b).mpr ⟨1, (one_smul K b).symm⟩
    rw [← hu, ← hΦLπ r u huQ]
    exact (M₀.comm_mem_iff huQ ((hc.conj_mem_Q_of_mem_M (hc.LB_le_M r.2)).1 u huQ)).mp
      (hc.comm_B_mem_Z r.2 huB)
  have hflag := fun r : ↥(LB M Q B) => hc.LB_act_flag hw hn hno h hB r.2
    (T := (ΦL r : M₀.E →ₗ[K] M₀.E)) (fun x hx => hΦLπ r x hx)
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E), Λ = ΦL.range := ⟨_, rfl⟩
  have hΛmem : ∀ T, T ∈ Λ ↔ ∃ r : ↥(LB M Q B), ΦL r = T := by
    intro T
    rw [hΛdef]
    exact MonoidHom.mem_range
  have hFD : FlagData M₀ b W Λ := by
    refine ⟨hb0, hbW, hWs, hWperp, ?_, ?_, ?_, ?_, ?_⟩
    · rintro T hT e
      obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
      exact hφiso (Subgroup.inclusion hLH0 r) e
    · rintro T hT
      obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
      exact hfix r
    · rintro T hT y hy
      obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
      exact (hWmem _).mp ((hflag r).2.2 y hy)
    · rintro T hT e he
      obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
      exact (hflag r).2.1 e ((hWmem e).mpr he)
    · rintro T hT T' hT'
      obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
      obtain ⟨r', rfl⟩ := (hΛmem T').mp hT'
      have hcr : (⁅r, r'⁆ : ↥(LB M Q B)) ∈ ΦL.ker := by
        rw [MonoidHom.mem_ker, hΦLker]
        exact hc.commutator_LB_le_Q (Subgroup.commutator_mem_commutator r.2 r'.2)
      have h1 := map_commutatorElement ΦL r r'
      rw [MonoidHom.mem_ker.mp hcr] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1.symm
  have hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1 := by
    intro T hT hTW
    obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
    have hrQ : (r : G) ∈ Q := by
      refine hc.mem_Q_of_comm_inf_QB_LB hw hn hno r.2 fun d hd => ?_
      have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
      have hrd : (r : G) * d * (r : G)⁻¹ ∈ Q :=
        (hc.conj_mem_Q_of_mem_M (hc.LB_le_M r.2)).1 d hdQ
      refine (M₀.comm_mem_iff hdQ hrd).mpr ?_
      rw [hΦLπ r d hdQ]
      exact hTW _ ((hWmem _).mp (M₀.pi_mem_img hd hdQ))
    exact (hΦLker r).mpr hrQ
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
  have hf₀ : M₀.B ((M₀.B f₁ b)⁻¹ • f₁) b = 1 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]
  let F : Submodule K M₀.E :=
    { carrier := {y | M₀.B y b = 0 ∧ ∀ T ∈ Λ, T y - y ∈ Submodule.span K {b}}
      add_mem' := by
        rintro y y' ⟨h1, h2⟩ ⟨h1', h2'⟩
        refine ⟨by rw [map_add, LinearMap.add_apply, h1, h1', add_zero], fun T hT => ?_⟩
        have : T (y + y') - (y + y') = (T y - y) + (T y' - y') := by rw [map_add]; abel
        rw [this]
        exact Submodule.add_mem _ (h2 T hT) (h2' T hT)
      zero_mem' := ⟨by simp, fun T _ => by simp⟩
      smul_mem' := by
        rintro c y ⟨h1, h2⟩
        refine ⟨by rw [map_smul, LinearMap.smul_apply, h1, smul_zero], fun T hT => ?_⟩
        have : T (c • y) - c • y = c • (T y - y) := by rw [map_smul, smul_sub]
        rw [this]
        exact Submodule.smul_mem _ c (h2 T hT) }
  have hF : ∀ y, y ∈ F ↔ M₀.B y b = 0 ∧ ∀ T ∈ Λ, T y - y ∈ Submodule.span K {b} :=
    fun y => Iff.rfl
  obtain ⟨ΛS, hΛSdef⟩ : ∃ ΛS : Subgroup (M₀.E ≃ₗ[K] M₀.E), ΛS = ΦS.range := ⟨_, rfl⟩
  have hΛS : ∀ T, T ∈ ΛS ↔ T ∈ Λ ∧ ∀ y, M₀.B y b = 0 → T y - y ∈ Submodule.span K {b} := by
    intro T
    rw [hΛSdef]
    constructor
    · rintro ⟨s, rfl⟩
      refine ⟨(hΛmem _).mpr ⟨⟨s, s.2.1⟩, rfl⟩, fun y hy => ?_⟩
      obtain ⟨-, hr⟩ := hc.Spure_act h hB hcent s.2 (T := (ΦS s : M₀.E → M₀.E))
        (fun x hx => hΦSπ s x hx)
      obtain ⟨c, hc'⟩ := hr y hy
      exact Submodule.mem_span_singleton.mpr ⟨c, by rw [hc']; abel⟩
    · rintro ⟨hTΛ, hTS⟩
      obtain ⟨r, rfl⟩ := (hΛmem T).mp hTΛ
      have hrS : (r : G) ∈ hc.Spure := by
        refine hc.mem_Spure.mpr ⟨r.2, fun y hy => ?_⟩
        obtain ⟨hyQ, hyC⟩ := hy
        obtain ⟨hQn, hQn'⟩ := hc.conj_mem_Q_of_mem_M (hc.LB_le_M r.2)
        have hkQ : ⁅(r : G), y⁆ ∈ Q := by
          rw [show ⁅(r : G), y⁆ = ((r : G) * y * (r : G)⁻¹) * y⁻¹ by rw [commutatorElement_def]]
          exact Q.mul_mem (hQn y hyQ) (Q.inv_mem hyQ)
        have hπ : M₀.π ⁅(r : G), y⁆ = ΦL r (M₀.π y) - M₀.π y := by
          rw [show ⁅(r : G), y⁆ = ((r : G) * y * (r : G)⁻¹) * y⁻¹ by rw [commutatorElement_def],
            M₀.π_mul _ (hQn y hyQ) _ (Q.inv_mem hyQ), hΦLπ r y hyQ,
            Tim79.QuadModel.pi_inv M₀ hyQ, sub_eq_add_neg]
        obtain ⟨c, hc'⟩ := Submodule.mem_span_singleton.mp (hTS _ ((hcent y hyQ).mp hyC))
        have hmem : M₀.π ⁅(r : G), y⁆ ∈ M₀.img B := (hB _).mpr ⟨c, by rw [hπ, ← hc']⟩
        exact (M₀.mem_img_iff le_sup_right hkQ).mp (M₀.img_mono le_sup_left hmem)
      exact ⟨⟨r, hrS⟩, rfl⟩
  have hWF : W ≤ F := fun d hd =>
    (hF d).mpr ⟨hFD.B_eq_zero hd hbW, fun T hT => by
      obtain ⟨c, hc'⟩ := hFD.flag3 T hT d hd
      exact Submodule.mem_span_singleton.mpr ⟨c, hc'.symm⟩⟩
  have hΛcard' : Nat.card Λ = Nat.card K ^ (n - 1) := by rw [hΛdef]; exact hcardΛ
  obtain ⟨d, hd1, hd2⟩ := hFD.card_ΛS hinj hf₀ hWdim hHom0 hΛcard' hrep F hF ΛS hΛS
  refine ⟨d, ?_, fun hd => ?_⟩
  · rw [hcardS, ← hΛSdef, hd1]
  · obtain ⟨f, hfF⟩ := exists_le_sup_span_of_finrank_le hWF (by omega)
    refine ⟨f, fun y hy hyr => hfF ((hF y).mpr ⟨hy, fun T hT => ?_⟩)⟩
    obtain ⟨r, rfl⟩ := (hΛmem T).mp hT
    exact hyr r

end Glue

end GroupSide

end CFSG.RankThree.GF2n.Stroth80
