module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndMain

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_linModelData [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hW : ∀ z ∈ Z0, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅z, w⁆ ∈ Z)
    (hZV : ∀ u ∈ Z0, u ∉ Q → Ut Q Z u = Vt M (LB M Q B) B Z t) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E)
      (hS : IsTensorSetup hc n M₀ ρ b),
      (∀ g : Mbar M Q, ∃ σ : K ≃+* K, ∀ (c : K) (e : M₀.E),
        (ρ g).toAdd (c • e) = σ c • (ρ g).toAdd e) ∧
      (∀ a a' : Mbar M Q, (∀ e, (ρ a).toAdd e = (ρ a').toAdd e) → a = a') ∧
      ∃ ψ : M₀.E →ₗ[K] M₀.E,
        (∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M hs.toSec5.mem⟩ : ↥M))).toAdd e - e) ∧
        (∀ x ∈ Q, ψ (M₀.π x) = 0 → x ∈ Wt Q (Vt M (LB M Q B) B Z t)) ∧
        (∀ a ∈ bar M Q Z0, ∃ c : K, ∀ e : M₀.E, (ρ a).toAdd e = e + c • ψ e) ∧
        (∀ φ : M₀.E →ₗ[K] M₀.E, LinearMap.ker ψ ≤ LinearMap.ker φ →
          LinearMap.range φ ≤ hc.VtSub hS.model t →
          (∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (e : M₀.E),
            φ ((ρ (x : Mbar M Q)).toAdd e) = (ρ (x : Mbar M Q)).toAdd (φ e)) →
          ∃ c : K, ∀ e, φ e = c • ψ e) := by
  classical
  have hs5 : Sec5Hyp hc n t := hs.toSec5
  have hSpOm : SpNat hc t ∨ OmegaNat hc t := Or.inr hs.omegaNat
  have hnat : NaturalScalarData hc t := sec7_natural_data hc hs
  have ht : t ∈ LB M Q B := hs5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨K, hF, hFin, γ, M₀, ρ, b, hS⟩ := tensorSetup_of_34 h34 G M Q Z B hc n
    hs5.width hs5.n_gt hs5.noA2 hs5.gen
  obtain ⟨act, hactρ, hinj, hsemi⟩ := endg_act_data hc hS.model ρ hS.conj
  have hsemi' : ∀ g : Mbar M Q, ∃ σ : K ≃+* K, ∀ (c : K) (e : M₀.E),
      (ρ g).toAdd (c • e) = σ c • (ρ g).toAdd e := by
    intro g
    obtain ⟨σ, hσ⟩ := hsemi g
    exact ⟨σ, fun c e => by rw [← hactρ, ← hactρ]; exact hσ c e⟩
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
  obtain ⟨hVeq, hWeq⟩ := h310chi G M Q Z B hc n t hs5 hSpOm
  obtain ⟨htQ, htQ'⟩ := hc.conj_mem_Q_of_mem_M htM
  have hrange : LinearMap.range ψ = hc.VtSub hS.model t := by
    refine Submodule.ext fun e => ?_
    rw [hc.mem_VtSub hS.model t, hVeq]
    exact (mem_img_comm_zpowers_sup_iff M₀ hS.model.reg (Tl _ htbH) htQ htQ'
      (fun x hx => hS.conj tm x hx) e).symm
  have hker_W : ∀ x ∈ Q, ψ (M₀.π x) = 0 → x ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro x hxQ hx0
    have h1 : (ρ (QuotientGroup.mk tm)).toAdd (M₀.π x) = M₀.π x := by
      rw [hψ] at hx0
      exact sub_eq_zero.mp hx0
    have h2 : M₀.π (t * x * t⁻¹) = M₀.π x := by
      rw [hS.conj tm x hxQ]
      exact h1
    have h3 : ⁅t, x⁆ ∈ Z := (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ (htQ x hxQ)).mpr h2
    rw [hWeq, hc.mem_Q1_iff htM]
    exact ⟨hxQ, h3⟩
  have hker_t : ∀ x ∈ Q, ψ (M₀.π x) = 0 → ∀ z ∈ Z0, ⁅z, x⁆ ∈ Z := fun x hxQ hx0 z hz =>
    hW z hz x (hker_W x hxQ hx0)
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
  have hρinj : ∀ a a' : Mbar M Q, (∀ e, (ρ a).toAdd e = (ρ a').toAdd e) → a = a' := fun a a' h =>
    hinj (Equiv.ext fun e => by rw [hactρ, hactρ]; exact h e)
  refine ⟨K, hF, hFin, γ, M₀, ρ, b, hS, hsemi', hρinj, ψ, hψ, hker_W, hA, ?_⟩
  intro φ hker hφP hφS
  exact endg_schur hcomm (hc.VtSub hS.model t) θ Ψ hΨc π hπr
    (fun (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : M₀.E) => (ρ (x : Mbar M Q)).toAdd w)
    (fun x w hw => hc.act_mem_VtSub hS ht x x.2 w hw) hΨx ψ φ hrange hker hφP hψS hφS

end Model

section Conj

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E] {Γ : Type*} [Group Γ]

theorem act_conj_form (ρ : Γ →* Multiplicative (AddAut E))
    (g z t : Γ) (c : K) (σ : K ≃+* K)
    (hσ : ∀ (c : K) (e : E), (ρ g).toAdd (c • e) = σ c • (ρ g).toAdd e)
    (hz : ∀ e, (ρ z).toAdd e = e + c • ((ρ t).toAdd e - e)) (e : E) :
    (ρ (g * z * g⁻¹)).toAdd e = e + σ c • ((ρ (g * t * g⁻¹)).toAdd e - e) := by
  have h1 : (ρ g).toAdd ((ρ g⁻¹).toAdd e) = e := by
    rw [← act_mul_apply, mul_inv_cancel, map_one]
    rfl
  have h2 : (ρ (g * t * g⁻¹)).toAdd e = (ρ g).toAdd ((ρ t).toAdd ((ρ g⁻¹).toAdd e)) := by
    rw [act_mul_apply, act_mul_apply]
  have h3 : (ρ (g * z * g⁻¹)).toAdd e = (ρ g).toAdd ((ρ z).toAdd ((ρ g⁻¹).toAdd e)) := by
    rw [act_mul_apply, act_mul_apply]
  rw [h3, hz, map_add, h1, hσ, map_sub, h1, h2]

end Conj

section LemmaS

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_conj_scalar [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {g : G} (hg : g ∈ M) {y : G} (hy : y ∈ conjSubgroup g Z0) :
    y ∈ M ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ)
      (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
      (σ : K ≃+* K) (c : K), (∀ (c : K) (e : M₀.E),
        (ρ (QuotientGroup.mk (⟨g, hg⟩ : ↥M))).toAdd (c • e) =
          σ c • (ρ (QuotientGroup.mk (⟨g, hg⟩ : ↥M))).toAdd e) ∧
      ∀ (hyM : y ∈ M) (e : M₀.E), (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e = e + σ c •
        ((ρ (QuotientGroup.mk (⟨g * t * g⁻¹, M.mul_mem (M.mul_mem hg (hc.LB_le_M hs.toSec5.mem))
          (M.inv_mem hg)⟩ : ↥M))).toAdd e - e) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hzZ0 : g⁻¹ * y * g ∈ Z0 := mem_conjSubgroup.mp hy
  have hzM : g⁻¹ * y * g ∈ M := hc.centre_le_M t hZ0 hzZ0
  have hyM : y ∈ M := by
    have := M.mul_mem (M.mul_mem hg hzM) (M.inv_mem hg)
    simpa [mul_assoc] using this
  refine ⟨hyM, ?_⟩
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, hsemi, -, ψ, hψ, -, hA, -⟩ :=
    sec7_linModelData h34 h310chi hc hs hZ0
      (fun z hz w hw => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).2 w hw)
      (fun u hu huQ => hZV G M Q Z B hc n t hs Z0 hZ0 u hu huQ)
  obtain ⟨σ, hσ⟩ := hsemi (QuotientGroup.mk (⟨g, hg⟩ : ↥M))
  have hzbar : (QuotientGroup.mk (⟨g⁻¹ * y * g, hzM⟩ : ↥M) : Mbar M Q) ∈ bar M Q Z0 :=
    Subgroup.mem_map.mpr ⟨⟨g⁻¹ * y * g, hzM⟩, Subgroup.mem_subgroupOf.mpr hzZ0, rfl⟩
  obtain ⟨c, hc'⟩ := hA _ hzbar
  refine ⟨K, fK, finK, γ, M₀, ρ, b, hS, σ, c, hσ, fun hyM' e => ?_⟩
  have e1 : (QuotientGroup.mk (⟨y, hyM'⟩ : ↥M) : Mbar M Q) =
      QuotientGroup.mk (⟨g, hg⟩ : ↥M) * QuotientGroup.mk (⟨g⁻¹ * y * g, hzM⟩ : ↥M) *
        (QuotientGroup.mk (⟨g, hg⟩ : ↥M))⁻¹ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])
  have e2 : (QuotientGroup.mk (⟨g * t * g⁻¹, M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)⟩ :
      ↥M) : Mbar M Q) =
      QuotientGroup.mk (⟨g, hg⟩ : ↥M) * QuotientGroup.mk (⟨t, htM⟩ : ↥M) *
        (QuotientGroup.mk (⟨g, hg⟩ : ↥M))⁻¹ := by
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  rw [e1, e2]
  exact act_conj_form ρ _ _ _ c σ hσ (fun e' => by rw [hc' e', hψ]) e

theorem sec7SV_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) : Sec7SVStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 g hg hvan y hy v hv
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨hyM, K, fK, finK, γ, M₀, ρ, b, hS, σ, c, hσ, hform⟩ :=
    sec7_conj_scalar h34 h310chi hZc hZV hc hs hZ0 hg hy
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hQn : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  have hvQ : v ∈ Q := hc.Vt_le_Q t hv
  have h1 : (ρ (QuotientGroup.mk (⟨g * t * g⁻¹, hxM⟩ : ↥M))).toAdd (M₀.π v) = M₀.π v := by
    rw [← hS.conj ⟨g * t * g⁻¹, hxM⟩ v hvQ]
    exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hvQ (hQn _ hxM v hvQ)).mp (hvan v hv)
  refine (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hvQ (hQn y hyM v hvQ)).mpr ?_
  rw [hS.conj ⟨y, hyM⟩ v hvQ, hform hyM, h1]
  simp

theorem sec7SW_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) : Sec7SWStatement := by
  intro G _ _ M Q Z B hc n t hs Z0 hZ0 g hg hvan y hy w hw
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  obtain ⟨hyM, K, fK, finK, γ, M₀, ρ, b, hS, σ, c, hσ, hform⟩ :=
    sec7_conj_scalar h34 h310chi hZc hZV hc hs hZ0 hg hy
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hxM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)
  have hQn : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  have hwQ : w ∈ Q := hw.1
  have h1 := (comm_mem_sub_iff M₀ (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z)
    (t := t)) hwQ (hQn _ hxM w hwQ)).mp (hvan w hw)
  refine (comm_mem_sub_iff M₀ (sec39_Z_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z)
    (t := t)) hwQ (hQn y hyM w hwQ)).mpr ?_
  rw [hS.conj ⟨y, hyM⟩ w hwQ, hform hyM, ← hS.conj ⟨g * t * g⁻¹, hxM⟩ w hwQ]
  have h2 : σ c • (M₀.π (g * t * g⁻¹ * w * (g * t * g⁻¹)⁻¹) - M₀.π w) ∈
      M₀.img (Vt M (LB M Q B) B Z t) := by
    exact hc.smul_mem_img_Vt hS.model t (σ c) h1
  have e : M₀.π w + σ c • (M₀.π (g * t * g⁻¹ * w * (g * t * g⁻¹)⁻¹) - M₀.π w) - M₀.π w =
      σ c • (M₀.π (g * t * g⁻¹ * w * (g * t * g⁻¹)⁻¹) - M₀.π w) := by abel
  rw [e]
  exact h2

end LemmaS

end CFSG.RankThree.GF2n.Stroth80
