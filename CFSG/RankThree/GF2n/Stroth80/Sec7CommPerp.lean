module

public import CFSG.RankThree.GF2n.Stroth80.Sec7LinA0

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_comm_mem_Q_of_perp [(Q.subgroupOf M).Normal] (h34 : Stroth34Statement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {y₁ y₂ : G}
    (hy₁ : y₁ ∈ H0 M Z) (hy₂ : y₂ ∈ H0 M Z) (hy₁2 : y₁ ^ 2 ∈ Q) (hy₂2 : y₂ ^ 2 ∈ Q)
    (hperp : ∀ a ∈ Ut Q Z y₁, ∀ b ∈ Ut Q Z y₂, ⁅a, b⁆ = 1) : ⁅y₁, y₂⁆ ∈ Q := by
  classical
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA, -⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  have hy₁M : y₁ ∈ M := hy₁.1
  have hy₂M : y₂ ∈ M := hy₂.1
  have hQn : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hm) x).mp hx
  have hreg := hS.model.reg
  set ζ₁ : Mbar M Q := QuotientGroup.mk (⟨y₁, hy₁M⟩ : ↥M) with hζ₁
  set ζ₂ : Mbar M Q := QuotientGroup.mk (⟨y₂, hy₂M⟩ : ↥M) with hζ₂
  have hζ₁H : ζ₁ ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨y₁, hy₁M⟩, Subgroup.mem_subgroupOf.mpr hy₁, rfl⟩
  have hζ₂H : ζ₂ ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨y₂, hy₂M⟩, Subgroup.mem_subgroupOf.mpr hy₂, rfl⟩
  have hsq : ∀ (y : G) (hyM : y ∈ M), y ^ 2 ∈ Q →
      ∀ e, (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd
        ((ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e) = e := by
    intro y hyM hy2 e
    have h1 : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨y, hyM⟩ : ↥M) = 1 := by
      rw [← QuotientGroup.mk_mul]
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [pow_two] using hy2
    rw [← act_mul_apply ρ, h1, map_one]
    rfl
  have hcomm_pi : ∀ (y : G) (hyM : y ∈ M) (x : G), x ∈ Q →
      M₀.π ⁅y, x⁆ = (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd (M₀.π x) - M₀.π x := by
    intro y hyM x hx
    have hyx : y * x * y⁻¹ ∈ Q := hQn y hyM x hx
    have e : ⁅y, x⁆ = (y * x * y⁻¹) * x⁻¹ := by rw [commutatorElement_def]
    rw [e, M₀.π_mul _ hyx _ (Q.inv_mem hx), Tim79.QuadModel.pi_inv M₀ hx,
      ← hS.conj ⟨y, hyM⟩ x hx, sub_eq_add_neg]
  have himg : ∀ (y : G) (hyM : y ∈ M) (e : M₀.E),
      (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e - e ∈ M₀.img (Ut Q Z y) := by
    intro y hyM e
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj e
    rw [← hcomm_pi y hyM x hxQ]
    have h1 : ⁅x, y⁆ ∈ ⁅Q, Subgroup.zpowers y⁆ :=
      Subgroup.commutator_mem_commutator hxQ (Subgroup.mem_zpowers y)
    have h2 : ⁅y, x⁆ ∈ Ut Q Z y := by
      rw [← commutatorElement_inv]
      exact (Ut Q Z y).inv_mem (Subgroup.mem_sup_left h1)
    refine M₀.pi_mem_img h2 ?_
    have h3 : ⁅y, x⁆ = (y * x * y⁻¹) * x⁻¹ := by rw [commutatorElement_def]
    rw [h3]
    exact Q.mul_mem (hQn y hyM x hxQ) (Q.inv_mem hxQ)
  have hBperp : ∀ d₁ ∈ M₀.img (Ut Q Z y₁), ∀ d₂ ∈ M₀.img (Ut Q Z y₂), M₀.B d₁ d₂ = 0 := by
    rintro _ ⟨a, ha, haQ, rfl⟩ _ ⟨c, hc', hcQ, rfl⟩
    exact (M₀.comm_iff_B hreg haQ hcQ).mp (commutatorElement_eq_one_iff_mul_comm.mp
      (hperp a ha c hc'))
  have hfix : ∀ (y : G) (hyM : y ∈ M), y ^ 2 ∈ Q → y ∈ H0 M Z → ∀ d : M₀.E,
      (∀ e', M₀.B d ((ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e' - e') = 0) →
      (ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd d = d := by
    intro y hyM hy2 hyH d hd
    have hζH : (QuotientGroup.mk (⟨y, hyM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
      Subgroup.mem_map.mpr ⟨⟨y, hyM⟩, Subgroup.mem_subgroupOf.mpr hyH, rfl⟩
    refine sub_eq_zero.mp (M₀.nondeg _ fun e' => ?_)
    have h1 := hS.iso _ hζH d ((ρ (QuotientGroup.mk (⟨y, hyM⟩ : ↥M))).toAdd e')
    rw [hsq y hyM hy2 e'] at h1
    rw [map_sub, LinearMap.sub_apply, h1, ← map_sub (M₀.B d)]
    exact hd e'
  have hT12 : ∀ e, (ρ ζ₁).toAdd ((ρ ζ₂).toAdd e) = (ρ ζ₂).toAdd ((ρ ζ₁).toAdd e) := by
    intro e
    obtain ⟨d₁, hd₁eq⟩ : ∃ d₁, d₁ = (ρ ζ₁).toAdd e - e := ⟨_, rfl⟩
    obtain ⟨d₂, hd₂eq⟩ : ∃ d₂, d₂ = (ρ ζ₂).toAdd e - e := ⟨_, rfl⟩
    have hd₁ : d₁ ∈ M₀.img (Ut Q Z y₁) := by rw [hd₁eq]; exact himg y₁ hy₁M e
    have hd₂ : d₂ ∈ M₀.img (Ut Q Z y₂) := by rw [hd₂eq]; exact himg y₂ hy₂M e
    have hA₁ : (ρ ζ₁).toAdd d₂ = d₂ := by
      refine hfix y₁ hy₁M hy₁2 hy₁ d₂ fun e' => ?_
      rw [Tim79.QuadModel.B_comm, hBperp _ (himg y₁ hy₁M e') _ hd₂, neg_zero]
    have hA₂ : (ρ ζ₂).toAdd d₁ = d₁ := by
      refine hfix y₂ hy₂M hy₂2 hy₂ d₁ fun e' => ?_
      exact hBperp _ hd₁ _ (himg y₂ hy₂M e')
    have hT1 : (ρ ζ₁).toAdd e = e + d₁ := by rw [hd₁eq]; abel
    have hT2 : (ρ ζ₂).toAdd e = e + d₂ := by rw [hd₂eq]; abel
    rw [hT2, map_add, hA₁, hT1, map_add, hA₂, hT2]
    abel
  have hmk : ζ₁ * ζ₂ = ζ₂ * ζ₁ := hinj _ _ fun e => by
    rw [act_mul_apply ρ, act_mul_apply ρ]
    exact hT12 e
  rw [hζ₁, hζ₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hmk
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hmk
  have e : ⁅y₁, y₂⁆ = (y₁ * y₂) * ((y₁ * y₂)⁻¹ * (y₂ * y₁))⁻¹ * (y₁ * y₂)⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hQn (y₁ * y₂) (M.mul_mem hy₁M hy₂M) _ (Q.inv_mem hmk)

end CFSG.RankThree.GF2n.Stroth80
