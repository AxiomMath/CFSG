module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsTwelveA
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHatVec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace HatU

variable {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)

theorem comm_mem_centerOf_of_fix {x u : G} (hxN : x ∈ Subgroup.normalizer (U : Set G))
    (hu : u ∈ U) (hfix : D.ρ ⟨x, hxN⟩ (D.π u) = D.π u) :
    x * u * x⁻¹ * u⁻¹ ∈ centerOf U := by
  have h1 := rho_sub_π D hxN hu
  rw [hfix, sub_self] at h1
  have hmem : x * u * x⁻¹ * u⁻¹ ∈ U := U.mul_mem (conj_mem hxN hu) (U.inv_mem hu)
  exact (π_eq_zero_iff D hmem).mp h1.symm

end HatU

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem X_comm_img (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) :
    ∀ γ ∈ D.img (rconj (wA V V₁) g), ∀ δ ∈ D.img (rconj (wA V V₁) g), γ * δ = δ * γ := by
  intro γ hγ δ hδ
  obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
  obtain ⟨y, hyX, hyN, rfl⟩ := (HatU.mem_img D).mp hδ
  have hxU : x ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g hxX
  have hyU : y ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g hyX
  have hc : x * y * x⁻¹ * y⁻¹ ∈ V := S.commutator_rconj_uA_mem hg hxU hyU
  have hcU : x * y * x⁻¹ * y⁻¹ ∈ uA V V₁ := le_uA V V₁ hc
  have hcN : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (uA V V₁ : Set G) :=
    Subgroup.le_normalizer hcU
  have key : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (uA V V₁ : Set G))) * ⟨y, hyN⟩ =
      ⟨x * y * x⁻¹ * y⁻¹, hcN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩) := by
    apply Subtype.ext
    show x * y = (x * y * x⁻¹ * y⁻¹) * (y * x)
    group
  calc D.ρ ⟨x, hxN⟩ * D.ρ ⟨y, hyN⟩ = D.ρ (⟨x, hxN⟩ * ⟨y, hyN⟩) := (map_mul _ _ _).symm
    _ = D.ρ (⟨x * y * x⁻¹ * y⁻¹, hcN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩)) := by rw [key]
    _ = D.ρ ⟨x * y * x⁻¹ * y⁻¹, hcN⟩ * D.ρ (⟨y, hyN⟩ * ⟨x, hxN⟩) := map_mul _ _ _
    _ = D.ρ (⟨y, hyN⟩ * ⟨x, hxN⟩) := by
      rw [HatU.rho_eq_one_of_mem D S.commutator_mem_centerOf hcU hcN, one_mul]
    _ = D.ρ ⟨y, hyN⟩ * D.ρ ⟨x, hxN⟩ := map_mul _ _ _

theorem X_sq_img (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) :
    ∀ γ ∈ D.img (rconj (wA V V₁) g), γ * γ = 1 := by
  intro γ hγ
  obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
  have hxU : x ∈ rconj (uA V V₁) g := rconj_le_rconj (wA_le_uA V V₁) g hxX
  have hxx : x * x ∈ rconj (V₁) g := by
    rw [mem_rconj]
    have h1 := S.sq_mem (mem_rconj.mp hxU)
    have e : g * (x * x) * g⁻¹ = (g * x * g⁻¹) ^ 2 := by
      rw [pow_two]
      group
    rw [e]
    exact h1
  have hxxU : x * x ∈ uA V V₁ :=
    le_uA V V₁ ((S.l2Setting).V₁_le_rconj_V hg.mem hxx)
  have hxxN : x * x ∈ Subgroup.normalizer (uA V V₁ : Set G) := Subgroup.le_normalizer hxxU
  calc D.ρ ⟨x, hxN⟩ * D.ρ ⟨x, hxN⟩ = D.ρ (⟨x, hxN⟩ * ⟨x, hxN⟩) := (map_mul _ _ _).symm
    _ = D.ρ ⟨x * x, hxxN⟩ := rfl
    _ = 1 := HatU.rho_eq_one_of_mem D S.commutator_mem_centerOf hxxU hxxN

theorem X_fixes_img (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) :
    ∀ γ ∈ D.img (rconj (wA V V₁) g), γ (D.π a) = D.π a := by
  intro γ hγ
  obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
  have hxa : x * a * x⁻¹ = a := by
    have := Subgroup.mem_centralizer_iff.mp (S.rconj_wA_le_centralizer_V hg hxX) a haV
    calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [this]
      _ = a := by group
  rw [D.ρ_π ⟨x, hxN⟩ _ (le_uA V V₁ haV)]
  show D.π (x * a * x⁻¹) = D.π a
  rw [hxa]

theorem span_orbit_img (S : Setting V V₁ L T)
    (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    Submodule.span (ZMod 2) (MulAction.orbit
      ↥(D.img (Subgroup.normalizer (V₁ : Set G)))
        (D.π a)) = ⊤ := by
  classical
  obtain ⟨hπa, -, hhatV⟩ := S.hat_V_cases D haV haZ
  have key : ∀ u, u ∈ conjClosure (V)
      (Subgroup.normalizer (V₁ : Set G)) →
      D.π u ∈ Submodule.span (ZMod 2) (MulAction.orbit
        ↥(D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)) := by
    intro u hu'
    unfold conjClosure at hu'
    induction hu' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hcH, z, hzV, rfl⟩ := hx
      have hcN : c ∈ Subgroup.normalizer (uA V V₁ : Set G) := normalizer_le_normalizer_uA V V₁ hcH
      have hzU : z ∈ uA V V₁ := le_uA V V₁ hzV
      have e : D.π (c * z * c⁻¹) = D.ρ ⟨c, hcN⟩ (D.π z) := (D.ρ_π ⟨c, hcN⟩ _ hzU).symm
      rw [e]
      rcases hhatV (D.π z) (HatU.π_mem_hat D hzV hzU) with h0 | h0
      · rw [h0, map_zero]
        exact Submodule.zero_mem _
      · rw [h0]
        refine Submodule.subset_span ?_
        exact ⟨⟨D.ρ ⟨c, hcN⟩, HatU.rho_mem_img D hcH hcN⟩, rfl⟩
    | one =>
      rw [HatU.π_one D]
      exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy =>
      have hxU : x ∈ uA V V₁ := hx
      have hyU : y ∈ uA V V₁ := hy
      rw [D.π_mul x hxU y hyU]
      exact Submodule.add_mem _ ihx ihy
    | inv x hx ih =>
      have hxU : x ∈ uA V V₁ := hx
      have h1 : D.π x⁻¹ = - D.π x := by
        have h2 := D.π_mul x⁻¹ ((uA V V₁).inv_mem hxU) x hxU
        rw [inv_mul_cancel, HatU.π_one D] at h2
        exact eq_neg_of_add_eq_zero_left h2.symm
      rw [h1]
      exact Submodule.neg_mem _ ih
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  exact key u hu

theorem img_T_le_stabilizer (S : Setting V V₁ L T)
    (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    D.img T ≤ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
  classical
  obtain ⟨hπa, -, hhatV⟩ := S.hat_V_cases D haV haZ
  intro γ hγ
  obtain ⟨t, htT, htN, rfl⟩ := (HatU.mem_img D).mp hγ
  rw [MulAction.mem_stabilizer_iff]
  have h1 : D.ρ ⟨t, htN⟩ (D.π a) = D.π (t * a * t⁻¹) := D.ρ_π _ _ (le_uA V V₁ haV)
  have hTM : t ∈ Subgroup.normalizer (V : Set G) := S.base.T_le_normV htT
  have h2 : t * a * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hTM a).mp haV
  have h3 := hhatV (D.π (t * a * t⁻¹)) (HatU.π_mem_hat D h2 (le_uA V V₁ h2))
  show D.ρ ⟨t, htN⟩ (D.π a) = D.π a
  rw [h1]
  rcases h3 with h0 | h0
  · exfalso
    apply hπa
    have h4 : D.ρ ⟨t, htN⟩ (D.π a) = 0 := by rw [h1, h0]
    exact (LinearEquiv.map_eq_zero_iff _).mp h4
  · exact h0

omit [Finite G] in
theorem relIndex_img_T_dvd (D : HatModelU (uA V V₁)) :
    (D.img T).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ∣
      T.relIndex (Subgroup.normalizer (V₁ : Set G)) := by
  have hHN : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (uA V V₁ : Set G) := fun x hx => normalizer_le_normalizer_uA V V₁ hx
  unfold HatModelU.img
  rw [← Subgroup.relIndex_comap]
  have h2 : T.subgroupOf (Subgroup.normalizer (uA V V₁ : Set G)) ≤
      Subgroup.comap D.ρ
        ((T.subgroupOf (Subgroup.normalizer (uA V V₁ : Set G))).map D.ρ) :=
    Subgroup.le_comap_map _ _
  refine (Subgroup.relIndex_dvd_of_le_left
    ((Subgroup.normalizer (V₁ : Set G)).subgroupOf
      (Subgroup.normalizer (uA V V₁ : Set G))) h2).trans ?_
  rw [Subgroup.relIndex_subgroupOf hHN]

omit [Finite G] in
theorem odd_relIndex_T (S : Setting V V₁ L T) :
    Odd (T.relIndex (Subgroup.normalizer (V₁ : Set G))) :=
  Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.base.sylow_H.2.2)

theorem odd_index_img (S : Setting V V₁ L T)
    (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V) (haZ : a ∉ V₁) :
    Odd (MulAction.stabilizer
      ↥(D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)).index := by
  classical
  have hstab : MulAction.stabilizer
      ↥(D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a) =
      (MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)).subgroupOf
        (D.img (Subgroup.normalizer (V₁ : Set G))) := by
    ext γ
    simp [MulAction.mem_stabilizer_iff]
  have hdvd1 : (MulAction.stabilizer
      ↥(D.img (Subgroup.normalizer (V₁ : Set G))) (D.π a)).index ∣
      (D.img T).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) := by
    rw [hstab]
    exact Subgroup.relIndex_dvd_of_le_left _ (S.img_T_le_stabilizer D haV haZ)
  exact Odd.of_dvd_nat S.odd_relIndex_T (hdvd1.trans (relIndex_img_T_dvd D))

theorem commutator_le_img (S : Setting V V₁ L T) {g : G}
    (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V)
    (haZ : a ∉ V₁) :
    ∀ γ ∈ D.img (rconj (wA V V₁) g), ∀ v, D.B (D.π a) v = 0 →
      γ v - v ∈ D.hat (wA V V₁ ⊓ rconj (wA V V₁) g) := by
  intro γ hγ v hv
  obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
  obtain ⟨w, hwW, hwU, rfl⟩ := (HatU.mem_hat D).mp ((S.mem_hat_wA_iff D haV haZ).mpr hv)
  rw [HatU.rho_sub_π D hxN hwU]
  have hc : ⁅w, x⁆ ∈ wA V V₁ ⊓ rconj (wA V V₁) g :=
    S.eleven_one hg (Subgroup.commutator_mem_commutator hwW hxX)
  have hinv : x * w * x⁻¹ * w⁻¹ = ⁅w, x⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hinv]
  have hcE : ⁅w, x⁆⁻¹ ∈ wA V V₁ ⊓ rconj (wA V V₁) g :=
    (wA V V₁ ⊓ rconj (wA V V₁) g).inv_mem hc
  exact HatU.π_mem_hat D hcE (inf_le_left.trans (wA_le_uA V V₁) hcE)

theorem centralizer_le_img (S : Setting V V₁ L T)
    {g : G} (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {a : G} (haV : a ∈ V)
    (haZ : a ∉ V₁) :
    ∀ γ ∈ D.img (rconj (wA V V₁) g), γ ∉ D.img (rconj (centerOf (uA V V₁)) g) →
      ∀ v, γ v = v → D.B (D.π a) v = 0 := by
  intro γ hγ hγZ v hv
  obtain ⟨x, hxX, hxN, rfl⟩ := (HatU.mem_img D).mp hγ
  by_contra hB
  obtain ⟨u, huU, rfl⟩ := D.π_surj v
  have huW : u ∉ wA V V₁ := fun huW =>
    hB ((S.mem_hat_wA_iff D haV haZ).mp (HatU.π_mem_hat D huW huU))
  have hcomm := HatU.comm_mem_centerOf_of_fix D hxN huU hv
  have h9 := S.nine_six hg huU huW hxX hcomm
  apply hγZ
  have hEU : wA V V₁ ⊓ rconj (wA V V₁) g ≤ uA V V₁ :=
    inf_le_left.trans (wA_le_uA V V₁)
  rw [← HatU.img_sup_eq_of_le D S.commutator_mem_centerOf
    ((rconj_centerOf_le_rconj_wA V V₁ g).trans (S.rconj_wA_le_normalizer_uA hg)) hEU]
  exact HatU.rho_mem_img D h9 hxN

end Setting

end L128A

end CFSG.Quasithin.H13
