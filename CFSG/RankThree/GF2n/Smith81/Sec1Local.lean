module

public import CFSG.RankThree.GF2n.Smith81.Sec1Fusion

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def centreCQ (Q : Subgroup G) (a : G) : Subgroup G :=
  Q ⊓ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G)

section Smith114

variable [Finite G] {M Q Z : Subgroup G}

theorem smith_1_14_analysis (H : StrothHyp M Q Z) {a : G} (haQ : a ∈ Q) (haZ : a ∉ Z) {r : G}
    (hrM : r ∈ M) (hr : ∀ c ∈ Q ⊓ Subgroup.centralizer ({a} : Set G), r * c = c * r) :
    (∀ q ∈ Q, ⁅q, r⁆ ∈ centreCQ Q a) ∧ (a ^ 2 = 1 → r ∈ Q) := by
  have hrZ : ∀ z ∈ Z, r * z * r⁻¹ = z := by
    intro z hz
    have hzC : z ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨H.Z_normal.1 hz, Subgroup.mem_centralizer_singleton_iff.mpr (Z_central H hz haQ)⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact hr z hzC
  obtain ⟨K, _, _, _, γ, M₀, hD⟩ := stroth_globalModelData H
  obtain ⟨T, hTπ, hTQ, hTB⟩ := hD.linear_of_centralizes hrM hrZ
  set e₀ := M₀.π a with he₀
  have he₀0 : e₀ ≠ 0 := fun h => haZ ((M₀.π_ker a haQ).mp h)
  have hfix : ∀ e, M₀.B e e₀ = 0 → T e = e := by
    intro e he
    obtain ⟨y, hyQ, rfl⟩ := M₀.π_surj e
    have hya : ⁅y, a⁆ = 1 := (GM.comm_eq_one_iff hD hyQ haQ).mpr he
    have hyC : y ∈ Q ⊓ Subgroup.centralizer ({a} : Set G) :=
      ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr
        (commutatorElement_eq_one_iff_mul_comm.mp hya)⟩
    have h1 := hr y hyC
    rw [← hTπ y hyQ]
    congr 1
    rw [mul_inv_eq_iff_eq_mul]
    exact h1
  obtain ⟨e₁, he₁⟩ : ∃ e₁, M₀.B e₁ e₀ = 1 := by
    obtain ⟨f, hf⟩ : ∃ f, M₀.B f e₀ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact he₀0 (M₀.nondeg e₀ fun f => by rw [Tim79.QuadModel.B_comm e₀ f, hcon f, neg_zero])
    refine ⟨(M₀.B f e₀)⁻¹ • f, ?_⟩
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
  have hdecomp : ∀ e, e - M₀.B e e₀ • e₁ ∈ {h : M₀.E | M₀.B h e₀ = 0} := by
    intro e
    show M₀.B (e - M₀.B e e₀ • e₁) e₀ = 0
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, he₁, mul_one,
      sub_self]
  have hTe : ∀ e, T e = e + M₀.B e e₀ • (T e₁ - e₁) := by
    intro e
    have h1 := hfix _ (hdecomp e)
    rw [map_sub, map_smul] at h1
    have h2 : T e = (T e - M₀.B e e₀ • T e₁) + M₀.B e e₀ • T e₁ := (sub_add_cancel _ _).symm
    rw [h2, h1, smul_sub]
    abel
  have hw : ∀ h, M₀.B h e₀ = 0 → M₀.B (T e₁ - e₁) h = 0 := by
    intro h hh
    rw [map_sub, LinearMap.sub_apply, ← hfix h hh, hTB e₁ h, hfix h hh, sub_self]
  have hBw : ∀ e, M₀.B (T e₁ - e₁) e = M₀.B e e₀ * M₀.B (T e₁ - e₁) e₁ := by
    intro e
    have h1 := hw _ (hdecomp e)
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h1
    exact h1
  obtain ⟨c, hc⟩ : ∃ c : K, T e₁ - e₁ = c • e₀ := by
    refine ⟨-M₀.B (T e₁ - e₁) e₁, ?_⟩
    have h0 : T e₁ - e₁ + M₀.B (T e₁ - e₁) e₁ • e₀ = 0 := by
      refine M₀.nondeg _ fun f => ?_
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hBw f,
        Tim79.QuadModel.B_comm e₀ f]
      ring
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left h0
  have hTform : ∀ e, T e = e + (c * M₀.B e e₀) • e₀ := by
    intro e
    rw [hTe e, hc, smul_smul, mul_comm]
  refine ⟨?_, ?_⟩
  · intro q hq
    refine ⟨comm_mem_Q H hrM hq, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    obtain ⟨hdQ, hdC⟩ := Subgroup.mem_inf.mp hd
    have hd0 : M₀.B (M₀.π d) e₀ = 0 :=
      (GM.comm_eq_one_iff hD hdQ haQ).mp
        (commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_centralizer_singleton_iff.mp hdC))
    have hπ : M₀.π ⁅q, r⁆ = -((c * M₀.B (M₀.π q) e₀) • e₀) := by
      have e1 : ⁅q, r⁆ = q * (r * q * r⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
      have hu := conj_mem_Q H hrM hq
      rw [e1, M₀.π_mul q hq _ (Q.inv_mem hu), Tim79.QuadModel.pi_inv M₀ hu, hTπ q hq, hTform]
      abel
    have h1 : ⁅d, ⁅q, r⁆⁆ = 1 := by
      refine (GM.comm_eq_one_iff hD hdQ (comm_mem_Q H hrM hq)).mpr ?_
      rw [hπ, map_neg, map_smul, smul_eq_mul, hd0]
      simp
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  · intro ha2
    have hQf : M₀.Qf e₀ = 0 := (GM.sq_eq_one_iff hD haQ).mp ha2
    have hc0 : c = 0 := by
      have h1 := hTQ e₁
      rw [hTform e₁, he₁, mul_one] at h1
      have h2 := M₀.Qf_add e₁ (c • e₀)
      rw [M₀.Qf_smul, map_smul, smul_eq_mul, he₁, hQf] at h2
      rw [h2] at h1
      linear_combination h1
    refine H.centralizer_Qt r hrM fun y hy => ?_
    have e : ⁅r, y⁆ = (r * y * r⁻¹) * y⁻¹ := by simp only [commutatorElement_def]
    have hryQ : ⁅r, y⁆ ∈ Q := by
      rw [e]; exact Q.mul_mem (conj_mem_Q H hrM hy) (Q.inv_mem hy)
    refine (M₀.π_ker _ hryQ).mp ?_
    rw [e, M₀.π_mul _ (conj_mem_Q H hrM hy) _ (Q.inv_mem hy), Tim79.QuadModel.pi_inv M₀ hy,
      hTπ y hy, hTform, hc0]
    simp

end Smith114

section Smith115

variable [Finite G] {M Q Z X : Subgroup G} {x : G}

theorem Kx_eq_of_mem (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X) {w : G} (hw : w ∈ X)
    (hw1 : w ≠ 1) : Kx Q X = Q ⊓ Subgroup.centralizer ({w} : Set G) := by
  apply le_antisymm
  · intro k hk
    exact ⟨hk.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw)
      (Kx_le_centralizer_X hs h12 hk)⟩
  · intro y hy
    obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
    have hcomm : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    exact ⟨hyQ, Tim77.mem_normalizer_of_commute_of_isTI hs.X_isTI hw hw1 hcomm⟩

theorem smith_1_15_direct (hs : Sit M Q Z X x) (h12 : Post12 M Q Z X)
    (hQ : Q ⊓ QB X = ⊥) :
    (∀ k ∈ Kx Q X, ∀ l ∈ Lx M X, k * l = l * k) ∧ Kx Q X ⊓ Lx M X = ⊥ ∧
      ∀ l ∈ Lx M X, l ^ 2 ≠ 1 →
        l ^ 2 ∈ X ∧ Q ⊓ Subgroup.centralizer ({l} : Set G) = Kx Q X := by
  obtain ⟨h1, -, -, -, -⟩ := smith_1_13_of_post12 hs h12
  have hcomm : ∀ k ∈ Kx Q X, ∀ l ∈ Lx M X, k * l = l * k := by
    intro k hk l hl
    have := h1 (Subgroup.commutator_mem_commutator hk hl)
    rw [hQ, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  refine ⟨hcomm, ?_, ?_⟩
  · rw [Kx_inf_Lx hs, hQ]
  · intro l hl hl2
    obtain ⟨g, hg, hQB, -⟩ := hs.QB_eq
    have hlB : l ∈ QB X := (Subgroup.mem_inf.mp hl).1
    have hl2X : l ^ 2 ∈ X := by
      rw [hQB] at hlB
      rw [hg]
      exact hs.hyp.toHyp79.sq_mem_conj g hlB
    refine ⟨hl2X, le_antisymm ?_ ?_⟩
    · intro y hy
      obtain ⟨hyQ, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyl : y * l = l * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      rw [Kx_eq_of_mem hs h12 hl2X hl2]
      refine ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      rw [pow_two, ← mul_assoc, hyl, mul_assoc, hyl, ← mul_assoc]
    · intro k hk
      exact ⟨hk.1, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm k hk l hl)⟩

end Smith115

end CFSG.RankThree.GF2n.Smith81
