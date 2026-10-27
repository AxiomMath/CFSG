module

public import CFSG.RankThree.GF2n.Stroth80.Core4Noncomm
public import CFSG.RankThree.GF2n.Stroth80.Sec9CentreMpr

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix Pointwise

section LinAlg

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem le_finrank_inf_orthogonal (B : LinearMap.BilinForm K E) (hB : B.Nondegenerate) {n : ℕ}
    (hE : Module.finrank K E = 2 * n) (U Vs : Submodule K E) (hU : Module.finrank K U = n)
    (hUlag : B.orthogonal U = U) (hV : Module.finrank K Vs ≤ 4)
    (hUV : 3 ≤ Module.finrank K ↥(U ⊓ Vs)) :
    n - 1 ≤ Module.finrank K ↥(U ⊓ B.orthogonal Vs) := by
  have e1 : B.orthogonal (U ⊔ Vs) = U ⊓ B.orthogonal Vs := by
    ext e
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, Submodule.mem_inf]
    constructor
    · intro h
      refine ⟨?_, fun v hv => h v (Submodule.mem_sup_right hv)⟩
      rw [← hUlag, LinearMap.BilinForm.mem_orthogonal_iff]
      exact fun u hu => h u (Submodule.mem_sup_left hu)
    · rintro ⟨h1, h2⟩ x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
      have h1' : e ∈ B.orthogonal U := by rw [hUlag]; exact h1
      have h3 := LinearMap.BilinForm.isOrtho_def.mp
        ((LinearMap.BilinForm.mem_orthogonal_iff.mp h1') u hu)
      rw [map_add, LinearMap.add_apply, h3, h2 v hv, add_zero]
  have e2 := LinearMap.BilinForm.finrank_orthogonal hB (U ⊔ Vs)
  rw [e1] at e2
  have e3 := Submodule.finrank_sup_add_finrank_inf_eq U Vs
  omega

end LinAlg

section FlagCount

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}
  {M₀ : Tim79.QuadModel QF V K γ} {b : M₀.E} {W : Submodule K M₀.E}
  {Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E)} {f₀ : M₀.E}

theorem FlagData.mem_of_psi_vanishing [Finite K] (hΛ : FlagData M₀ b W Λ)
    (hinj : ∀ T ∈ Λ, (∀ e ∈ W, T e = e) → T = 1) (hf₀ : M₀.B f₀ b = 1) {n : ℕ}
    (hWn : Module.finrank K W = n) (Y : Submodule K W) (hY : n - 1 ≤ Module.finrank K Y)
    (S : Subgroup (M₀.E ≃ₗ[K] M₀.E)) (hSΛ : S ≤ Λ)
    (hS : ∀ T ∈ S, ∀ y ∈ Y, flagPsiLin M₀ W f₀ T y = 0) (hScard : Nat.card K ≤ Nat.card S)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : T ∈ Λ) (hTY : ∀ y ∈ Y, flagPsiLin M₀ W f₀ T y = 0) :
    T ∈ S := by
  classical
  let Ann : Submodule K (W →ₗ[K] K) := Y.dualAnnihilator
  have hAnn : ∀ f, f ∈ Ann ↔ ∀ v ∈ Y, f v = 0 := fun f => by
    simp only [Ann, Submodule.mem_dualAnnihilator]
  have hdim : Module.finrank K Y + Module.finrank K Ann = n := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq Y
    rw [hWn] at this
    exact this
  have hq : 0 < Nat.card K := Nat.card_pos
  have hAnncard : Nat.card Ann ≤ Nat.card K := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := Ann)]
    calc Nat.card K ^ Module.finrank K Ann ≤ Nat.card K ^ 1 :=
          Nat.pow_le_pow_right hq (by omega)
      _ = Nat.card K := pow_one _
  have hfinAnn : Finite Ann := Module.finite_of_finite K
  let Ψ : S → Ann := fun s => ⟨flagPsiLin M₀ W f₀ s.1, (hAnn _).mpr (hS s.1 s.2)⟩
  have hΨinj : Function.Injective Ψ := by
    intro s s' h
    refine Subtype.ext (hΛ.eq_of_psi_eq hinj hf₀ (hSΛ s.2) (hSΛ s'.2) fun d hd => ?_)
    have := congrArg (fun z : Ann => (z.1 : W →ₗ[K] K) ⟨d, hd⟩) h
    simpa [Ψ, flagPsiLin_apply] using this
  have hbij : Function.Bijective Ψ := hΨinj.bijective_of_nat_card_le (hAnncard.trans hScard)
  obtain ⟨s, hs⟩ := hbij.2 ⟨flagPsiLin M₀ W f₀ T, (hAnn _).mpr hTY⟩
  have hsT : s.1 = T := by
    refine hΛ.eq_of_psi_eq hinj hf₀ (hSΛ s.2) hT fun d hd => ?_
    have := congrArg (fun z : Ann => (z.1 : W →ₗ[K] K) ⟨d, hd⟩) hs
    simpa [Ψ, flagPsiLin_apply] using this
  rw [← hsT]
  exact s.2

end FlagCount

section Hyperbolic

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec7A.inv (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G}
    (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r) : Sec7A hc t r⁻¹ := by
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hinvM : r⁻¹ ∈ M := M.inv_mem hrM
  refine ⟨(Rt M (LB M Q B) t).inv_mem hrR, ?_, ?_⟩
  · obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := HS9.exists_pts91 h34 hs
    haveI := hn
    let ρ : ↥(Rt M (LB M Q B) t) := ⟨r, hrR⟩
    have h1 := (HS9.hypPlane_iff_polar91 h34 hs P ρ).mp hr.plane
    refine (HS9.hypPlane_iff_polar91 h34 hs P ρ⁻¹).mpr ?_
    have hg : φ ρ ∈ StatedOmega (StatedQuadPlus 2 K) := by
      rw [← P.range]
      exact ⟨ρ, rfl⟩
    have hiso : ∀ x, quadPlus 2 K ((φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x) =
        quadPlus 2 K x := fun x =>
      mem_statedOmega_preserves (Q := quadPlus 2 K) (coe_quadPlus 2 K) hg x
    have hgg : (φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
        (φ ρ⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    intro h0
    apply h1
    have e1 : polar (quadPlus 2 K) ((φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u)
        ((φ ρ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
          ((φ ρ⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u)) =
        polar (quadPlus 2 K) u ((φ ρ⁻¹ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) := by
      simp only [polar, ← Matrix.mulVec_add, hiso]
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec, h0, polar_comm] at e1
    exact e1
  · have hRn : ∀ g ∈ Rt M (LB M Q B) t,
        g ∈ Subgroup.normalizer ((Rt M (LB M Q B) t : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        exact mul_mem (mul_mem hg hh) (inv_mem hg)
      · intro hh
        have := mul_mem (mul_mem (inv_mem hg) hh) hg
        simpa [mul_assoc] using this
    have hRn' : conjSubgroup r⁻¹ (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
      conjSubgroup_eq_self_iff.mpr (hRn _ ((Rt M (LB M Q B) t).inv_mem hrR))
    have h1 := congrArg (conjSubgroup r⁻¹) hr.gen
    rw [hRn', conjSubgroup_sup, hc.LB_conj hrM, ← conjSubgroup_mul, inv_mul_cancel,
      conjSubgroup_one, ← hc.LB_conj hinvM] at h1
    exact h1.trans (sup_comm _ _)

theorem not_le_QB_conj (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G}
    (hs : Sec9Hyp hc n t) (hr : Sec7A hc t r) : ¬ B ≤ QB (conjSubgroup r B) := by
  intro hle
  refine HS9.conj_not_le_QB91 h34 hs (Sec7A.inv h34 hs hr) ?_
  have h1 := conjSubgroup_mono (g := r⁻¹) hle
  rwa [QB_conj, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at h1

end Hyperbolic

section Pairing

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem mem_Z0_of_fix_perp (Pk : GlobalModelAction M Q Z K γ M₀) (h91 : Step91OrderVQBStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {Z0 : Subgroup G}
    (hcen : HS9.Centre95 hc t Z0) (hQZ0 : Q ≤ Z0) {x : G} (hx : x ∈ LB M Q B ⊓ hc.CN t)
    (hfix : ∀ e ∈ imgQInfQB M₀ B,
      (∀ v ∈ M₀.img (Vt M (LB M Q B) B Z t), M₀.B e v = 0) → Pk.act x e = e) : x ∈ Z0 := by
  classical
  have hs5 := hs.toSec5
  have hrR1 : (1 : G) ∈ Rt M (LB M Q B) t := (Rt M (LB M Q B) t).one_mem
  set V := Vt M (LB M Q B) B Z t with hV
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hLBH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hKZ : Nat.card K = Nat.card Z := Pk.h.card
  have hq4 := hc.hyp.q4
  have hK2 : 1 < Nat.card K := by rw [hKZ]; omega
  have hE : Module.finrank K M₀.E = 2 * n := Pk.h.finrank_E hs5.width hK2
  have hB : M₀.B.Nondegenerate := modelB_nondegenerate M₀
  obtain ⟨b, hb0, -, hbL, -, -⟩ := hc.dictB Pk.h
  obtain ⟨hFD, hfaith, -⟩ := hc.flagData_lam hs5.width hs5.n_gt hs5.noA2 Pk hb0 hbL
  obtain ⟨hTn, hTperp, -⟩ := hc.imgQInfQB_lagr hs5.width hs5.n_gt hs5.noA2 Pk.h
  have hTmem := hc.mem_imgQInfQB_iff hs5.width hs5.n_gt hs5.noA2 Pk.h
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero hb0
  have hf₀ : M₀.B ((M₀.B f₁ b)⁻¹ • f₁) b = 1 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]
  set f₀ := (M₀.B f₁ b)⁻¹ • f₁ with hf₀def
  set T := imgQInfQB M₀ B with hTdef
  have hTlag : M₀.B.orthogonal T = T := by
    refine le_antisymm (fun v hv => hTperp v fun u hu => ?_) (fun e he f hf => ?_)
    · have h1 : M₀.B u v = 0 := LinearMap.BilinForm.mem_orthogonal_iff.mp hv u hu
      rw [Tim79.QuadModel.B_comm, h1, neg_zero]
    · exact hFD.B_eq_zero hf he
  let Vsub : Submodule K M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt Pk.h t c he)
  have hVsub_mem : ∀ e, e ∈ Vsub ↔ e ∈ M₀.img V := fun e => mem_imgSub
  have hVdim : Module.finrank K Vsub = 4 := by
    have hVcardImg : Nat.card ↥Vsub = Nat.card (M₀.img V) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun e => (hVsub_mem e).symm)
    have hQcard : Nat.card ↥V = Nat.card Z * Nat.card (M₀.img V) :=
      M₀.card_eq hVQ (sec39_Z_le_Vt : Z ≤ V)
    have hVcard : Nat.card ↥Vsub = Nat.card Z ^ 4 := by
      rw [hVcardImg]
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Z)) ?_
      rw [← hQcard, hs.card_V]; ring
    have h1 : Nat.card K ^ Module.finrank K Vsub = Nat.card K ^ 4 := by
      rw [← Module.natCard_eq_pow_finrank, hVcard, hKZ]
    exact Nat.pow_right_injective hK2 h1
  have hcard3 : Nat.card ↥(M₀.img (V ⊓ QB B)) = Nat.card K ^ 3 := by
    have := card_img_Vt_inf_QB_conj Pk hc hs h91 hrR1
    rwa [conjSubgroup_one] at this
  have hUVdim : 3 ≤ Module.finrank K ↥(T ⊓ Vsub) := by
    let ι : ↥(M₀.img (V ⊓ QB B)) → ↥(T ⊓ Vsub) := fun e =>
      ⟨e.1, ⟨(hTmem e.1).mpr (M₀.img_mono (inf_le_inf_right _ hVQ) e.2),
        (hVsub_mem e.1).mpr (M₀.img_mono inf_le_left e.2)⟩⟩
    have hι : Function.Injective ι := fun e e' h => Subtype.ext (congrArg (fun z => z.1) h)
    haveI : Finite ↥(T ⊓ Vsub) := Module.finite_of_finite K
    have h1 := Nat.card_le_card_of_injective ι hι
    rw [hcard3, Module.natCard_eq_pow_finrank (K := K) (V := ↥(T ⊓ Vsub))] at h1
    exact (Nat.pow_le_pow_iff_right hK2).mp h1
  have hYdim := le_finrank_inf_orthogonal M₀.B hB hE T Vsub hTn hTlag hVdim.le hUVdim
  let Y : Submodule K T := (M₀.B.orthogonal Vsub).comap T.subtype
  have hYmem : ∀ y : T, y ∈ Y ↔ ∀ v ∈ M₀.img V, M₀.B (y : M₀.E) v = 0 := by
    intro y
    simp only [Y, Submodule.mem_comap, Submodule.subtype_apply,
      LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h v hv
      have := h v ((hVsub_mem v).mpr hv)
      rw [Tim79.QuadModel.B_comm, LinearMap.BilinForm.isOrtho_def.mp this, neg_zero]
    · intro h v hv
      have := h v ((hVsub_mem v).mp hv)
      rw [Tim79.QuadModel.B_comm, this, neg_zero]
  have hYfin : Module.finrank K Y = Module.finrank K ↥(T ⊓ M₀.B.orthogonal Vsub) := by
    rw [← Submodule.finrank_map_subtype_eq T Y, Submodule.map_comap_subtype]
  have hZ0LB : Z0 ≤ LB M Q B ⊓ hc.CN t := hcen.1
  have hZ0H0 : Z0 ≤ H0 M Z := (hZ0LB.trans inf_le_left).trans hLBH0
  let S : Subgroup (M₀.E ≃ₗ[K] M₀.E) := (Z0.subgroupOf (H0 M Z)).map Pk.φ
  have hSmem : ∀ T', T' ∈ S ↔ ∃ z ∈ Z0, Pk.act z = T' := by
    intro T'
    simp only [S, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m, hm, Pk.act_of_mem m.2⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hZ0H0 hz⟩, hz, (Pk.act_of_mem (hZ0H0 hz)).symm⟩
  have hlam : ∀ g ∈ LB M Q B, Pk.act g ∈ Pk.lam B := fun g hg => by
    rw [Pk.act_of_mem (hLBH0 hg)]
    exact (Pk.phi_mem_lam_iff ⟨g, hLBH0 hg⟩).mpr hg
  have hSΛ : S ≤ Pk.lam B := by
    intro T' hT'
    obtain ⟨z, hz, rfl⟩ := (hSmem T').mp hT'
    exact hlam z (hZ0LB hz).1
  have hScard : Nat.card K ≤ Nat.card S := by
    have h1 : Nat.card S = Q.relIndex Z0 := card_phi_image Pk hQZ0 hZ0H0
    rw [h1, hcen.2.1, hKZ]
  have hS : ∀ T' ∈ S, ∀ y ∈ Y, flagPsiLin M₀ T f₀ T' y = 0 := by
    intro T' hT' y hy
    obtain ⟨z, hz, rfl⟩ := (hSmem T').mp hT'
    have hyW : (y : M₀.E) ∈ M₀.img (Wt Q V) :=
      (mem_img_Wt_iff M₀ Pk.h.reg hVQ).mpr ((hYmem y).mp hy)
    obtain ⟨w, hwW, hwQ, hwy⟩ := hyW
    have hfixz : Pk.act z (y : M₀.E) = y := by
      rw [← hwy]
      exact Pk.act_fix (hZ0H0 hz) hQn hwQ (HS9.Centre95.comm_mem_Z_of_mem_Wt hc hcen hz hwW)
    rw [flagPsiLin_apply]
    simp [flagPsi, hfixz]
  have hTY : ∀ y ∈ Y, flagPsiLin M₀ T f₀ (Pk.act x) y = 0 := by
    intro y hy
    have hfixx := hfix y y.2 ((hYmem y).mp hy)
    rw [flagPsiLin_apply]
    simp [flagPsi, hfixx]
  have hxS : Pk.act x ∈ S :=
    hFD.mem_of_psi_vanishing hfaith hf₀ hTn Y (by omega) S hSΛ hS hScard (hlam x hx.1) hTY
  obtain ⟨z, hz, hzx⟩ := (hSmem _).mp hxS
  have hxH0 : x ∈ H0 M Z := hLBH0 hx.1
  have hzH0 : z ∈ H0 M Z := hZ0H0 hz
  have h1 : Pk.act (z⁻¹ * x) = 1 := by
    rw [Pk.act_mul ((H0 M Z).inv_mem hzH0) hxH0, Pk.act_inv hzH0, hzx, inv_mul_cancel]
  have h2 : z⁻¹ * x ∈ Q := (Pk.act_eq_one_iff ((H0 M Z).mul_mem ((H0 M Z).inv_mem hzH0) hxH0)).mp h1
  have h3 : x = z * (z⁻¹ * x) := by group
  rw [h3]
  exact Z0.mul_mem hz (hQZ0 h2)

theorem noncomm_core (Pk : GlobalModelAction M Q Z K γ M₀) (h34 : Stroth34Statement)
    (h91 : Step91OrderVQBStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t)
    {r : G} (hr : Sec7A hc t r) {Z0 : Subgroup G} (hcen : HS9.Centre95 hc t Z0) (hQZ0 : Q ≤ Z0)
    {x : G} (hx : x ∈ LB M Q B ⊓ hc.CN t) (hxZ : x ∉ Z0) :
    ∃ y ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, ⁅x, y⁆ ∉ Q := by
  classical
  have hs5 := hs.toSec5
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  set V := Vt M (LB M Q B) B Z t with hV
  set A := conjSubgroup r B with hAdef
  have hcA : Ctx M Q Z A := hc.conj_of_mem hrM
  have hnoA : NoA2 Q Z (LB M Q A) := hc.noA2_conj hs5.noA2 hrM
  have hLBH0 : LB M Q B ≤ H0 M Z := hc.LB_le_H0_cb
  have hLAH0 : LB M Q A ≤ H0 M Z := hcA.LB_le_H0_cb
  have hxL : x ∈ LB M Q B := hx.1
  have hxH0 : x ∈ H0 M Z := hLBH0 hxL
  obtain ⟨b, hb0, -, hbL, -, -⟩ := hc.dictB Pk.h
  obtain ⟨a, ha0, -, haL, -, -⟩ := hcA.dictB Pk.h
  obtain ⟨hFDB, -, -⟩ := hc.flagData_lam hs5.width hs5.n_gt hs5.noA2 Pk hb0 hbL
  obtain ⟨hFDA, hfaithA, -⟩ := hcA.flagData_lam hs5.width hs5.n_gt hnoA Pk ha0 haL
  obtain ⟨f₁, hf₁⟩ := Tim79.QuadModel.exists_B_ne_zero ha0
  have hf₀ : M₀.B ((M₀.B f₁ a)⁻¹ • f₁) a = 1 := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₁]
  set f₀ := (M₀.B f₁ a)⁻¹ • f₁ with hf₀def
  have haA : a ∈ M₀.img A := (haL a).mpr ⟨1, (one_smul K a).symm⟩
  have hWmemA := hcA.mem_imgQInfQB_iff hs5.width hs5.n_gt hnoA Pk.h
  obtain ⟨-, hTAperp, -⟩ := hcA.imgQInfQB_lagr hs5.width hs5.n_gt hnoA Pk.h
  have hlamB : ∀ g ∈ LB M Q B, Pk.act g ∈ Pk.lam B := fun g hg => by
    rw [Pk.act_of_mem (hLBH0 hg)]
    exact (Pk.phi_mem_lam_iff ⟨g, hLBH0 hg⟩).mpr hg
  have hxlamB : Pk.act x ∈ Pk.lam B := hlamB x hxL
  have hex : ∃ e ∈ imgQInfQB M₀ B, (∀ v ∈ M₀.img V, M₀.B e v = 0) ∧ Pk.act x e ≠ e := by
    by_contra hall
    push Not at hall
    exact hxZ (mem_Z0_of_fix_perp Pk h91 hc hs hcen hQZ0 hx fun e he hev => hall e he hev)
  obtain ⟨e, heT, heperp, hxe⟩ := hex
  obtain ⟨c, hcb⟩ := hFDB.flag3 _ hxlamB e heT
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hxe
    rw [zero_smul, sub_eq_zero] at hcb
    exact hcb
  have hxinv : x⁻¹ ∈ LB M Q B ⊓ hc.CN t := (LB M Q B ⊓ hc.CN t).inv_mem hx
  have hξinv : Pk.act x⁻¹ = (Pk.act x)⁻¹ := Pk.act_inv hxH0
  have hξinvW : ∀ u ∈ imgQInfQB M₀ A, (Pk.act x)⁻¹ u ∈ imgQInfQB M₀ A := fun u hu => by
    rw [← hξinv]
    exact (hWmemA _).mpr (act_mem_img_QInfQB Pk hc hs hrR hxinv.1 hxinv.2 ((hWmemA u).mp hu))
  have hiso : ∀ u w, M₀.B (Pk.act x u) (Pk.act x w) = M₀.B u w := fun u w =>
    Tim79.QuadModel.B_iso (T := ((Pk.act x : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E))
      (hFDB.iso _ hxlamB) u w
  have hadj : ∀ u w, M₀.B ((Pk.act x)⁻¹ u) w = M₀.B u (Pk.act x w) := fun u w => by
    have h := hiso ((Pk.act x)⁻¹ u) w
    rw [show Pk.act x ((Pk.act x)⁻¹ u) = u from (Pk.act x).apply_symm_apply u] at h
    exact h.symm
  have hu : ∃ u ∈ imgQInfQB M₀ A, (Pk.act x)⁻¹ u - u ∉ M₀.img V := by
    by_contra hall
    push Not at hall
    have hbA : b ∈ imgQInfQB M₀ A := by
      refine hTAperp b fun u hu => ?_
      have hw : M₀.B ((Pk.act x)⁻¹ u - u) e = 0 := by
        have h1 := heperp _ (hall u hu)
        rw [Tim79.QuadModel.B_comm, h1, neg_zero]
      have hexp : M₀.B ((Pk.act x)⁻¹ u - u) e = c * M₀.B u b := by
        rw [map_sub, LinearMap.sub_apply, hadj, ← map_sub (M₀.B u), hcb, map_smul, smul_eq_mul]
      have h3 : c * M₀.B u b = 0 := by rw [← hexp]; exact hw
      have h4 : M₀.B u b = 0 := (mul_eq_zero.mp h3).resolve_left hc0
      rw [Tim79.QuadModel.B_comm, h4, neg_zero]
    exact not_le_QB_conj h34 hs hr
      ((hcA.le_QB_iff_mem_imgQInfQB hs5.width hs5.n_gt hnoA Pk.h hc hbL).mpr hbA)
  obtain ⟨u, huTA, hwV⟩ := hu
  have hwTA : (Pk.act x)⁻¹ u - u ∈ imgQInfQB M₀ A :=
    (imgQInfQB M₀ A).sub_mem (hξinvW u huTA) huTA
  let Vsub : Submodule K M₀.E := imgSub M₀ V (fun c e he => hc.smul_mem_img_Vt Pk.h t c he)
  have hVsub_mem : ∀ v, v ∈ Vsub ↔ v ∈ M₀.img V := fun v => mem_imgSub
  let Sg : Submodule K (imgQInfQB M₀ A) := Vsub.comap (imgQInfQB M₀ A).subtype
  have hwSg : (⟨(Pk.act x)⁻¹ u - u, hwTA⟩ : imgQInfQB M₀ A) ∉ Sg := fun h =>
    hwV ((hVsub_mem _).mp h)
  obtain ⟨f, hfw, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwSg inferInstance
  have hfvan : ∀ v : imgQInfQB M₀ A, (v : M₀.E) ∈ M₀.img (V ⊓ QB A) → f v = 0 := by
    intro v hv
    have hvSg : v ∈ Sg := (hVsub_mem _).mpr (M₀.img_mono inf_le_left hv)
    have h1 : f v ∈ Submodule.map f Sg := Submodule.mem_map_of_mem hvSg
    rw [hfmap] at h1
    exact (Submodule.mem_bot K).mp h1
  obtain ⟨y, hyT, hy⟩ := exists_act_psi_eq Pk h34 h91 hc hs hrR hFDA hfaithA hf₀ f hfvan
  refine ⟨y, hyT, fun hxyQ => ?_⟩
  have hyH0 : y ∈ H0 M Z := hLAH0 hyT.1
  have hxyH0 : ⁅x, y⁆ ∈ H0 M Z := by
    rw [commutatorElement_def]
    exact (H0 M Z).mul_mem ((H0 M Z).mul_mem ((H0 M Z).mul_mem hxH0 hyH0)
      ((H0 M Z).inv_mem hxH0)) ((H0 M Z).inv_mem hyH0)
  have h1 : Pk.act ⁅x, y⁆ = 1 := (Pk.act_eq_one_iff hxyH0).mpr hxyQ
  have h2 := flagPsi_comm_apply Pk hc hs hrR hFDA hf₀ haA hx hyT huTA
  have h3 : flagPsi M₀ f₀ (1 : M₀.E ≃ₗ[K] M₀.E) u = 0 := by simp [flagPsi]
  rw [h1, h3] at h2
  apply hfw
  rw [← hy, flagPsiLin_apply]
  exact h2.symm

end Pairing

theorem sec97Noncomm_holds (h34 : Stroth34Statement) (hCentre : Step95CentreStatement)
    (h91 : Step91OrderVQBStatement) : Sec97NoncommStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 x hx hxZ
  have hcen := hCentre G M Q Z B hc n t hs Z0 hZ0
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre hs.toSec5.mem hZ0
  obtain ⟨K, _, _, _, γ, M₀, ⟨Pk⟩⟩ := exists_globalModelAction hc.hyp
  exact noncomm_core Pk h34 h91 hc hs hr hcen hQZ0 hx hxZ

theorem core4_holds (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement)
    (hA : Sec9AExistsStatement) (hn5 : Sec9NGeFiveStatement) (hS4 : Sec4Statement)
    (hCentre : Step95CentreStatement) (h91 : Step91OrderVQBStatement) :
    Sec97FourCore94Statement :=
  core4_of_noncomm h34 h311a h311bComm h312b hA hn5 hS4 hCentre h91
    (sec97Noncomm_holds h34 hCentre h91)

end CFSG.RankThree.GF2n.Stroth80
