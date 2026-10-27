module

public import CFSG.RankThree.GF2n.Stroth80.Sec7EndLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetup
public import CFSG.RankThree.GF2n.Stroth80.Sec111Order
public import CFSG.RankThree.GF2n.Stroth80.Sec7Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Stmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def NaturalScalarData (hc : Ctx M Q Z B) (t : G) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : Finite K') (ι : Type) (_ : Fintype ι)
    (_ : DecidableEq ι) (_ : Nonempty ι) (Xcl : Subgroup (GL ι K')),
    Nat.card K' = Nat.card Z ∧ AddCommutantScalar Xcl ∧
    NaturalRep K' Xcl (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)

theorem endg_comm_centre [(Q.subgroupOf M).Normal] {R Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 R Q) (hRM : R ≤ M) {z : ↥M} (hz : (z : G) ∈ Z0)
    {x : Mbar M Q} (hx : x ∈ bar M Q R) :
    (QuotientGroup.mk z : Mbar M Q) * x = x * QuotientGroup.mk z := by
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
  exact ((mk_commute_iff z r).mpr (hZ0.comm_mem hz (Subgroup.mem_subgroupOf.mp hr))).eq

theorem endg_act_data [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K]
    [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} (h : GlobalModelData M Q Z γ M₀)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E))
    (hρ : ∀ (t : ↥M) (x : G), x ∈ Q →
      M₀.π ((t : G) * x * (t : G)⁻¹) = (ρ (QuotientGroup.mk t)).toAdd (M₀.π x)) :
    ∃ act : Mbar M Q →* Equiv.Perm M₀.E, (∀ g e, act g e = (ρ g).toAdd e) ∧
      Function.Injective act ∧
      ∀ g : Mbar M Q, ∃ σ : K ≃+* K, ∀ (c : K) (e : M₀.E), act g (c • e) = σ c • act g e := by
  obtain ⟨φ, hφπ, hφker, -, hφsemi⟩ := exists_actionHom_M hc.hyp h
  have hact : ∀ m : ↥M, ∀ e, (ρ (QuotientGroup.mk m)).toAdd e = φ m e := fun m e =>
    congrFun (eq_of_pi_conj_eq (M₀ := M₀) (g := (m : G))
      (S₁ := fun e => (ρ (QuotientGroup.mk m)).toAdd e) (S₂ := fun e => φ m e)
      (fun x hx => hρ m x hx) (fun x hx => hφπ m x hx)) e
  let act : Mbar M Q →* Equiv.Perm M₀.E :=
    MonoidHom.mk' (fun g => (ρ g).toAdd.toEquiv)
      (fun a b => Equiv.ext fun e => act_mul_apply ρ a b e)
  refine ⟨act, fun g e => rfl, ?_, ?_⟩
  · refine (injective_iff_map_eq_one act).mpr fun g hg => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 : φ m = 1 := Equiv.ext fun e =>
      (hact m e).symm.trans (congrArg (fun f : Equiv.Perm M₀.E => f e) hg)
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ((hφker m).mp h1))
  · intro g
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨σ, hσ⟩ := hφsemi m
    refine ⟨σ, fun c e => ?_⟩
    show (ρ (QuotientGroup.mk m)).toAdd (c • e) = σ c • (ρ (QuotientGroup.mk m)).toAdd e
    rw [hact, hact]
    exact hσ c e

theorem endg_linModel [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hSpOm : SpNat hc t ∨ OmegaNat hc t) (hnat : NaturalScalarData hc t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hW : ∀ z ∈ Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅z, w⁆ ∈ Z)
    (hZV : ∀ u ∈ Z0, u ∉ Q → Ut Q Z u = Vt M (LB M Q B) B Z t) :
    EndLinModel (Mbar M Q) (bar M Q (H0 M Z)) (bar M Q Z0) := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨K, hF, hFin, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n
    hs.width hs.n_gt hs.noA2 hs.gen
  obtain ⟨act, hactρ, hinj, hsemi⟩ := endg_act_data hc hS.model ρ hS.conj
  obtain ⟨K', hF', hFin', ι, hFι, hDι, hNι, Xcl, hK', hcomm, hnat⟩ := hnat
  obtain ⟨θ, Ψ, π, hπr, hπk, hΨc, hΨx⟩ := hc.natural_transport hS ht hK' hcomm hnat
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hH0 : ∀ r : ↥M, (r : G) ∈ Rt M (LB M Q B) t →
      (QuotientGroup.mk r : Mbar M Q) ∈ bar M Q (H0 M Z) := fun r hr =>
    Subgroup.mem_map.mpr ⟨r, Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t hr), rfl⟩
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  let tm : ↥M := ⟨t, htM⟩
  have htbH : (QuotientGroup.mk tm : Mbar M Q) ∈ bar M Q (H0 M Z) := hH0 tm (hZ0.le htZ0)
  let Tl : ∀ g : Mbar M Q, g ∈ bar M Q (H0 M Z) → (M₀.E ≃ₗ[K] M₀.E) := fun g hg =>
    AddEquiv.toLinearEquiv (ρ g).toAdd (hS.lin g hg)
  let ψ : M₀.E →ₗ[K] M₀.E := ((Tl _ htbH : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1
  have hψ : ∀ e, ψ e = (ρ (QuotientGroup.mk tm)).toAdd e - e := fun e => rfl
  obtain ⟨hVeq, hWeq⟩ := h310chi G M Q Z B hc n t hs hSpOm
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hrange : LinearMap.range ψ = hc.VtSub hS.model t := by
    refine Submodule.ext fun e => ?_
    rw [hc.mem_VtSub hS.model t, hVeq]
    exact (mem_img_comm_zpowers_sup_iff M₀ hS.model.reg (Tl _ htbH) htQ htQ'
      (fun x hx => hS.conj tm x hx) e).symm
  have hker_t : ∀ x ∈ Q, ψ (M₀.π x) = 0 → ∀ z ∈ Z0, ⁅z, x⁆ ∈ Z := by
    intro x hxQ hx0 z hz
    have h1 : (ρ (QuotientGroup.mk tm)).toAdd (M₀.π x) = M₀.π x := by
      rw [hψ] at hx0
      exact sub_eq_zero.mp hx0
    have h2 : M₀.π (t * x * t⁻¹) = M₀.π x := by
      rw [hS.conj tm x hxQ]
      exact h1
    have h3 : ⁅t, x⁆ ∈ Z := (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ (htQ x hxQ)).mpr h2
    have h4 : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      rw [hWeq, hc.mem_Q1_iff htM]
      exact ⟨hxQ, h3⟩
    exact hW z hz x h4
  have hcomm_act : ∀ a b : Mbar M Q, a * b = b * a → ∀ e,
      (ρ a).toAdd ((ρ b).toAdd e) = (ρ b).toAdd ((ρ a).toAdd e) := by
    intro a b hab e
    rw [← act_mul_apply ρ a b e, ← act_mul_apply ρ b a e, hab]
  have hψS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
      ψ ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (ψ e) := by
    intro x e
    rw [hψ, hψ, map_sub, hcomm_act _ _ (endg_comm_centre hZ0 hRM (z := tm) htZ0 x.2) e]
  have hA : ∀ a ∈ bar M Q Z0, ∃ c : K, ∀ e, (ρ a).toAdd e = e + c • ψ e := by
    intro a ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    have hzZ0 : (z : G) ∈ Z0 := Subgroup.mem_subgroupOf.mp hz
    have hzR : (z : G) ∈ Rt M (LB M Q B) t := hZ0.le hzZ0
    have hzH : (QuotientGroup.mk z : Mbar M Q) ∈ bar M Q (H0 M Z) := hH0 z hzR
    by_cases hzQ : (z : G) ∈ Q
    · have h1 : (QuotientGroup.mk' (Q.subgroupOf M) z : Mbar M Q) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hzQ)
      refine ⟨0, fun e => ?_⟩
      rw [h1, map_one, zero_smul, add_zero]
      rfl
    · let φ : M₀.E →ₗ[K] M₀.E := ((Tl _ hzH : M₀.E ≃ₗ[K] M₀.E) : M₀.E →ₗ[K] M₀.E) - 1
      have hφ : ∀ e, φ e = (ρ (QuotientGroup.mk z)).toAdd e - e := fun e => rfl
      have hUz := hZV z hzZ0 hzQ
      obtain ⟨hzQ1, hzQ2⟩ := hc.conj_mem_Q_of_mem_M z.2
      have hφP : LinearMap.range φ ≤ hc.VtSub hS.model t := by
        intro v hv
        have h1 : v ∈ M₀.img (Ut Q Z (z : G)) :=
          (mem_img_comm_zpowers_sup_iff M₀ hS.model.reg (Tl _ hzH) hzQ1 hzQ2
            (fun x hx => hS.conj z x hx) v).mpr hv
        rw [hUz] at h1
        exact (hc.mem_VtSub hS.model t).mpr h1
      have hker : LinearMap.ker ψ ≤ LinearMap.ker φ := by
        intro e he
        obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
        have h1 := hker_t x hxQ (LinearMap.mem_ker.mp he) z hzZ0
        refine LinearMap.mem_ker.mpr ?_
        rw [hφ, ← hS.conj z x hxQ]
        exact sub_eq_zero.mpr ((Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ (hzQ1 x hxQ)).mp h1)
      have hφS : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
          φ ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (φ e) := by
        intro x e
        rw [hφ, hφ, map_sub, hcomm_act _ _ (endg_comm_centre hZ0 hRM hzZ0 x.2) e]
      obtain ⟨c, hcφ⟩ := endg_schur hcomm (hc.VtSub hS.model t) θ Ψ hΨc π hπr
        (fun (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : M₀.E) => (ρ (x : Mbar M Q)).toAdd w)
        (fun x w hw => hc.act_mem_VtSub hS ht x x.2 w hw) hΨx ψ φ hrange hker hφP hψS hφS
      refine ⟨c, fun e => ?_⟩
      have h2 := hcφ e
      rw [hφ] at h2
      rw [← h2]
      abel
  refine ⟨⟨K, hF, M₀.E, inferInstance, inferInstance, act, ψ, hinj, ?_, hsemi, ?_, ?_⟩⟩
  · intro g e e'
    rw [hactρ, hactρ, hactρ]
    exact map_add (ρ g).toAdd e e'
  · intro h hh c e
    rw [hactρ, hactρ]
    exact hS.lin h hh c e
  · intro a ha
    obtain ⟨c, hc'⟩ := hA a ha
    exact ⟨c, fun e => by rw [hactρ]; exact hc' e⟩

end Model

end CFSG.RankThree.GF2n.Stroth80
