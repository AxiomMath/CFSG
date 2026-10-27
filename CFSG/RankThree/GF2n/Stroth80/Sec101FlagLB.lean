module

public import CFSG.RankThree.GF2n.Stroth80.Sec34CaseB

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

section Lam

variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def GlobalModelAction.lam (Pk : GlobalModelAction M Q Z K γ M₀) (C : Subgroup G) :
    Subgroup (M₀.E ≃ₗ[K] M₀.E) :=
  ((LB M Q C).subgroupOf (H0 M Z)).map Pk.φ

theorem GlobalModelAction.mem_lam (Pk : GlobalModelAction M Q Z K γ M₀) {C : Subgroup G}
    {T : M₀.E ≃ₗ[K] M₀.E} :
    T ∈ Pk.lam C ↔ ∃ m : ↥(H0 M Z), (m : G) ∈ LB M Q C ∧ Pk.φ m = T := by
  simp only [GlobalModelAction.lam, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem GlobalModelAction.phi_mem_lam_iff (Pk : GlobalModelAction M Q Z K γ M₀)
    {C : Subgroup G} (m : ↥(H0 M Z)) :
    Pk.φ m ∈ Pk.lam C ↔ (m : G) ∈ LB M Q C := by
  rw [Pk.mem_lam]
  constructor
  · rintro ⟨m', hm', he⟩
    have h1 : Pk.φ (m'⁻¹ * m) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have h2 : ((m'⁻¹ * m : ↥(H0 M Z)) : G) ∈ Q := (Pk.hφker _).mp h1
    have h3 : (m : G) = m' * ((m'⁻¹ * m : ↥(H0 M Z)) : G) := by simp
    rw [h3]
    exact (LB M Q C).mul_mem hm' (sec39_Q_le_LB h2)
  · intro h
    exact ⟨m, h, rfl⟩

theorem GlobalModelAction.finite_lam (Pk : GlobalModelAction M Q Z K γ M₀) (C : Subgroup G) :
    Finite (Pk.lam C) := by
  refine Finite.of_surjective
    (fun x : ↥((LB M Q C).subgroupOf (H0 M Z)) => (⟨Pk.φ x, Subgroup.mem_map_of_mem _ x.2⟩ :
      ↥(Pk.lam C))) ?_
  rintro ⟨T, m, hm, rfl⟩
  exact ⟨⟨m, hm⟩, rfl⟩

theorem GlobalModelAction.phi_mem_normalizer_iff (Pk : GlobalModelAction M Q Z K γ M₀)
    {C : Subgroup G} (hcC : Ctx M Q Z C) (m : ↥(H0 M Z)) :
    Pk.φ m ∈ Subgroup.normalizer (Pk.lam C : Set (M₀.E ≃ₗ[K] M₀.E)) ↔
      (m : G) ∈ Subgroup.normalizer (LB M Q C : Set G) := by
  haveI : Finite (Pk.lam C) := Pk.finite_lam C
  constructor
  · intro hm
    refine Subgroup.mem_normalizer_fintype fun l hl => ?_
    have hlH : l ∈ H0 M Z := hcC.LB_le_H0_cb hl
    have h1 : Pk.φ m * Pk.φ ⟨l, hlH⟩ * (Pk.φ m)⁻¹ ∈ Pk.lam C :=
      (Subgroup.mem_normalizer_iff.mp hm _).mp ((Pk.phi_mem_lam_iff _).mpr hl)
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact (Pk.phi_mem_lam_iff _).mp h1
  · intro hm
    refine Subgroup.mem_normalizer_fintype fun T hT => ?_
    obtain ⟨l, hl, rfl⟩ := Pk.mem_lam.mp hT
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (Pk.phi_mem_lam_iff _).mpr ((Subgroup.mem_normalizer_iff.mp hm _).mp hl)

theorem GlobalModelAction.phi_comm_iff (Pk : GlobalModelAction M Q Z K γ M₀)
    (s t : ↥(H0 M Z)) : Pk.φ s * Pk.φ t = Pk.φ t * Pk.φ s ↔ ⁅(s : G), (t : G)⁆ ∈ Q := by
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, Pk.hφker]
  rfl

theorem GlobalModelAction.lam_inf_eq_bot (Pk : GlobalModelAction M Q Z K γ M₀)
    {C D : Subgroup G} (hcC : Ctx M Q Z C) (hcD : Ctx M Q Z D)
    (h : LB M Q C ⊓ LB M Q D = Q) : Pk.lam C ⊓ Pk.lam D = ⊥ := by
  refine eq_bot_iff.mpr fun T hT => ?_
  obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hT.1
  have hmD := (Pk.phi_mem_lam_iff m).mp hT.2
  have hmQ : (m : G) ∈ Q := h ▸ ⟨hm, hmD⟩
  exact Subgroup.mem_bot.mpr ((Pk.hφker m).mpr hmQ)

theorem GlobalModelAction.lam_comm (Pk : GlobalModelAction M Q Z K γ M₀) {C : Subgroup G}
    (hcC : Ctx M Q Z C) : ∀ x ∈ Pk.lam C, ∀ y ∈ Pk.lam C, x * y = y * x := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := Pk.mem_lam.mp hx
  obtain ⟨b, hb, rfl⟩ := Pk.mem_lam.mp hy
  exact (Pk.phi_comm_iff a b).mpr
    (hcC.commutator_LB_le_Q (Subgroup.commutator_mem_commutator ha hb))

theorem GlobalModelAction.lam_mul_self (Pk : GlobalModelAction M Q Z K γ M₀)
    {C : Subgroup G} (hcC : Ctx M Q Z C) : ∀ x ∈ Pk.lam C, x * x = 1 := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Pk.mem_lam.mp hx
  rw [← map_mul]
  refine (Pk.hφker _).mpr ?_
  have h2 := hcC.sq_mem_Q_of_mem_LB ha
  rwa [sq] at h2

private theorem flagData_lam_isFlag [CharP K 2] {C : Subgroup G} (hcC : Ctx M Q Z C) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q C))
    (Pk : GlobalModelAction M Q Z K γ M₀) {c : M₀.E} (hc0 : c ≠ 0) (hcl : IsLineGen M₀ C c) :
    FlagData M₀ c (imgQInfQB M₀ C) (Pk.lam C) := by
  classical
  obtain ⟨hWn, hWp, hWs⟩ := hcC.imgQInfQB_lagr hw hn hno Pk.h
  have hWmem := hcC.mem_imgQInfQB_iff hw hn hno Pk.h
  have hcW : c ∈ imgQInfQB M₀ C := (hWmem c).mpr
    (M₀.img_mono (le_inf hcC.le hcC.B_le_QB : C ≤ Q ⊓ QB C)
      ((hcl c).mpr ⟨1, (one_smul K c).symm⟩))
  have hflag := fun (m : ↥(H0 M Z)) (hm : (m : G) ∈ LB M Q C) =>
    hcC.LB_act_flag hw hn hno Pk.h hcl hm (T := (Pk.φ m : M₀.E →ₗ[K] M₀.E))
      fun x hx => Pk.hφπ m x hx
  refine ⟨hc0, hcW, hWs, hWp, ?_, ?_, ?_, ?_, Pk.lam_comm hcC⟩
  · rintro T hT e
    obtain ⟨m, -, rfl⟩ := Pk.mem_lam.mp hT
    exact Pk.hφiso m e
  · rintro T hT
    obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hT
    obtain ⟨u, huC, huQ, hu⟩ : c ∈ M₀.img C := (hcl c).mpr ⟨1, (one_smul K c).symm⟩
    rw [← hu, ← Pk.hφπ m u huQ]
    exact (M₀.comm_mem_iff huQ ((hcC.conj_mem_Q_of_mem_M (hcC.LB_le_M hm)).1 u huQ)).mp
      (hcC.comm_B_mem_Z hm huC)
  · rintro T hT y hy
    obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hT
    exact (hWmem _).mpr ((hflag m hm).2.2 y hy)
  · rintro T hT e he
    obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hT
    exact (hflag m hm).2.1 e ((hWmem e).mp he)

private theorem flagData_lam_faithful {C : Subgroup G} (hcC : Ctx M Q Z C) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q C))
    (Pk : GlobalModelAction M Q Z K γ M₀) :
    ∀ T ∈ Pk.lam C, (∀ e ∈ imgQInfQB M₀ C, T e = e) → T = 1 := by
  intro T hT hTW
  obtain ⟨m, hm, rfl⟩ := Pk.mem_lam.mp hT
  refine (Pk.hφker m).mpr (hcC.mem_Q_of_comm_inf_QB_LB hw hn hno hm fun d hd => ?_)
  have hdQ : d ∈ Q := (Subgroup.mem_inf.mp hd).1
  have hrd : (m : G) * d * (m : G)⁻¹ ∈ Q :=
    (hcC.conj_mem_Q_of_mem_M (hcC.LB_le_M hm)).1 d hdQ
  refine (M₀.comm_mem_iff hdQ hrd).mpr ?_
  rw [Pk.hφπ m d hdQ]
  exact hTW _ (Submodule.subset_span (M₀.pi_mem_img hd hdQ))

private theorem flagData_lam_card {C : Subgroup G} (hcC : Ctx M Q Z C) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q C))
    (Pk : GlobalModelAction M Q Z K γ M₀) :
    Nat.card (Pk.lam C) = Nat.card K ^ (n - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hLH0 : LB M Q C ≤ H0 M Z := hcC.LB_le_H0_cb
  let ΦL : ↥(LB M Q C) →* (M₀.E ≃ₗ[K] M₀.E) := Pk.φ.comp (Subgroup.inclusion hLH0)
  have hrange : ΦL.range = Pk.lam C := by
    ext T
    rw [MonoidHom.mem_range, Pk.mem_lam]
    constructor
    · rintro ⟨r, rfl⟩
      exact ⟨Subgroup.inclusion hLH0 r, r.2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  have hker : ΦL.ker = Q.subgroupOf (LB M Q C) := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact Pk.hφker (Subgroup.inclusion hLH0 r)
  have h1 : Nat.card ΦL.ker = Nat.card Q := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Q_le_LB).toEquiv
  have hcardL : Nat.card (LB M Q C) = Nat.card Q * Nat.card ΦL.range := by
    rw [← h1, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have h33 := (hcC.card_of_3_3 hw hn1 hno (stroth_3_3 hcC hw hn1)).1
  rw [hcardL] at h33
  rw [← hrange, Nat.eq_of_mul_eq_mul_left Nat.card_pos h33, Pk.h.card]

theorem Ctx.flagData_lam [CharP K 2] {C : Subgroup G} (hcC : Ctx M Q Z C) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (hno : NoA2 Q Z (LB M Q C))
    (Pk : GlobalModelAction M Q Z K γ M₀) {c : M₀.E} (hc0 : c ≠ 0) (hcl : IsLineGen M₀ C c) :
    FlagData M₀ c (imgQInfQB M₀ C) (Pk.lam C) ∧
      (∀ T ∈ Pk.lam C, (∀ e ∈ imgQInfQB M₀ C, T e = e) → T = 1) ∧
      Nat.card (Pk.lam C) = Nat.card K ^ (n - 1) :=
  ⟨flagData_lam_isFlag hcC hw hn hno Pk hc0 hcl,
    flagData_lam_faithful hcC hw hn hno Pk,
    flagData_lam_card hcC hw hn hno Pk⟩

end Lam

theorem exists_globalModelAction (H : StrothHyp M Q Z) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), Nonempty (GlobalModelAction M Q Z K γ M₀) := by
  obtain ⟨K, _, _, _, γ, M₀, h⟩ := stroth_globalModelData H
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 H h
  exact ⟨K, inferInstance, inferInstance, inferInstance, γ, M₀, ⟨⟨h, φ, hφπ, hφker, hφiso⟩⟩⟩

end CFSG.RankThree.GF2n.Stroth80
