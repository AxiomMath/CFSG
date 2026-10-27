module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabTwelveA
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatVec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace HatModel

variable {G : Type} [Group G] {T M : Subgroup G} (D : HatModel T M)

theorem comm_mem_centerOf_of_fix {x u : G} (hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G))
    (hu : u ∈ uOfL22 T M) (hfix : D.rho ⟨x, hxN⟩ (D.π u) = D.π u) :
    x * u * x⁻¹ * u⁻¹ ∈ centerOf (uOfL22 T M) := by
  have h1 := HatModel.rho_sub_π (D := D) hxN hu
  rw [hfix, sub_self] at h1
  have hmem : x * u * x⁻¹ * u⁻¹ ∈ uOfL22 T M :=
    (uOfL22 T M).mul_mem (HatModel.conj_mem_uOfL22 hxN hu) ((uOfL22 T M).inv_mem hu)
  exact (D.π_eq_zero_iff hmem).mp h1.symm

theorem img_eq_map (K : Subgroup G) :
    D.img K = (K.subgroupOf (Subgroup.normalizer (uOfL22 T M : Set G))).map D.rho := by
  ext γ
  rw [HatModel.mem_img, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hxK, hxN, rfl⟩
    exact ⟨⟨x, hxN⟩, hxK, rfl⟩
  · rintro ⟨x, hxK, rfl⟩
    exact ⟨x.1, hxK, x.2, rfl⟩

end HatModel

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem X_comm_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) :
    ∀ γ ∈ D.img (rconj (wOfU T M) g), ∀ δ ∈ D.img (rconj (wOfU T M) g), γ * δ = δ * γ := by
  intro γ hγ δ hδ
  obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  obtain ⟨y, hyX, hyN, rfl⟩ := HatModel.mem_img.mp hδ
  have hxU : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hxX
  have hyU : y ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hyX
  have hc : x * y * x⁻¹ * y⁻¹ ∈ VZ T M := h.commutator_rconj_uOfL22_mem_VZ hU hg hxU hyU
  have hcU : x * y * x⁻¹ * y⁻¹ ∈ uOfL22 T M := VZ_le_uOfL22 T M hc
  have hcN : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.normalizer (uOfL22 T M : Set G) :=
    Subgroup.le_normalizer hcU
  have key : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (uOfL22 T M : Set G))) * ⟨y, hyN⟩ =
      ⟨x * y * x⁻¹ * y⁻¹, hcN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩) := by
    apply Subtype.ext
    show x * y = (x * y * x⁻¹ * y⁻¹) * (y * x)
    group
  calc D.rho ⟨x, hxN⟩ * D.rho ⟨y, hyN⟩ = D.rho (⟨x, hxN⟩ * ⟨y, hyN⟩) := (map_mul _ _ _).symm
    _ = D.rho (⟨x * y * x⁻¹ * y⁻¹, hcN⟩ * (⟨y, hyN⟩ * ⟨x, hxN⟩)) := by rw [key]
    _ = D.rho ⟨x * y * x⁻¹ * y⁻¹, hcN⟩ * D.rho (⟨y, hyN⟩ * ⟨x, hxN⟩) := map_mul _ _ _
    _ = D.rho (⟨y, hyN⟩ * ⟨x, hxN⟩) := by rw [h.rho_eq_one_of_mem D hcU hcN, one_mul]
    _ = D.rho ⟨y, hyN⟩ * D.rho ⟨x, hxN⟩ := map_mul _ _ _

theorem X_sq_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) :
    ∀ γ ∈ D.img (rconj (wOfU T M) g), γ * γ = 1 := by
  intro γ hγ
  obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  have hxU : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hxX
  have hxx : x * x ∈ rconj (quasithinOmegaOneCenter T) g := by
    rw [mem_rconj]
    have h1 := h.sq_mem_omegaOneCenter (mem_rconj.mp hxU)
    have e : g * (x * x) * g⁻¹ = (g * x * g⁻¹) ^ 2 := by
      rw [pow_two]
      group
    rw [e]
    exact h1
  have hxxU : x * x ∈ uOfL22 T M :=
    VZ_le_uOfL22 T M ((h.l2Setting128 hU).V₁_le_rconj_V hg.mem hxx)
  have hxxN : x * x ∈ Subgroup.normalizer (uOfL22 T M : Set G) := Subgroup.le_normalizer hxxU
  calc D.rho ⟨x, hxN⟩ * D.rho ⟨x, hxN⟩ = D.rho (⟨x, hxN⟩ * ⟨x, hxN⟩) := (map_mul _ _ _).symm
    _ = D.rho ⟨x * x, hxxN⟩ := rfl
    _ = 1 := h.rho_eq_one_of_mem D hxxU hxxN

theorem X_fixes_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) :
    ∀ γ ∈ D.img (rconj (wOfU T M) g), γ (D.π a) = D.π a := by
  intro γ hγ
  obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  have hxa : x * a * x⁻¹ = a := by
    have := Subgroup.mem_centralizer_iff.mp (h.rconj_wOfU_le_centralizer_VZ hU hg hxX) a haV
    calc x * a * x⁻¹ = (a * x) * x⁻¹ := by rw [this]
      _ = a := by group
  rw [D.rho_π ⟨x, hxN⟩ (VZ_le_uOfL22 T M haV)]
  show D.π (x * a * x⁻¹) = D.π a
  rw [hxa]

theorem span_orbit_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T) :
    Submodule.span (ZMod 2) (MulAction.orbit
      ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)))
        (D.π a)) = ⊤ := by
  classical
  obtain ⟨hπa, -, hhatV⟩ := h.hat_VZ_cases hU D haV haZ
  have key : ∀ u, u ∈ conjClosure (VZ T M)
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) →
      D.π u ∈ Submodule.span (ZMod 2) (MulAction.orbit
        ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) (D.π a)) := by
    intro u hu'
    unfold conjClosure at hu'
    induction hu' using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hcH, z, hzV, rfl⟩ := hx
      have hcN : c ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hcH
      have hzU : z ∈ uOfL22 T M := VZ_le_uOfL22 T M hzV
      have e : D.π (c * z * c⁻¹) = D.rho ⟨c, hcN⟩ (D.π z) := (D.rho_π ⟨c, hcN⟩ hzU).symm
      rw [e]
      rcases hhatV (D.π z) (D.π_mem_hat hzV hzU) with h0 | h0
      · rw [h0, map_zero]
        exact Submodule.zero_mem _
      · rw [h0]
        refine Submodule.subset_span ?_
        exact ⟨⟨D.rho ⟨c, hcN⟩, HatModel.rho_mem_img hcH hcN⟩, rfl⟩
    | one =>
      rw [D.π_one]
      exact Submodule.zero_mem _
    | mul x y hx hy ihx ihy =>
      have hxU : x ∈ uOfL22 T M := hx
      have hyU : y ∈ uOfL22 T M := hy
      rw [D.π_mul x hxU y hyU]
      exact Submodule.add_mem _ ihx ihy
    | inv x hx ih =>
      have hxU : x ∈ uOfL22 T M := hx
      have h1 : D.π x⁻¹ = - D.π x := by
        have h2 := D.π_mul x⁻¹ ((uOfL22 T M).inv_mem hxU) x hxU
        rw [inv_mul_cancel, D.π_one] at h2
        exact eq_neg_of_add_eq_zero_left h2.symm
      rw [h1]
      exact Submodule.neg_mem _ ih
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, hu, rfl⟩ := D.π_surj v
  exact key u hu

theorem img_T_le_stabilizer (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T) :
    D.img T ≤ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
  classical
  obtain ⟨hπa, -, hhatV⟩ := h.hat_VZ_cases hU D haV haZ
  intro γ hγ
  obtain ⟨t, htT, htN, rfl⟩ := HatModel.mem_img.mp hγ
  rw [MulAction.mem_stabilizer_iff]
  have h1 : D.rho ⟨t, htN⟩ (D.π a) = D.π (t * a * t⁻¹) := D.rho_π _ (VZ_le_uOfL22 T M haV)
  have hTM : t ∈ Subgroup.normalizer (VZ T M : Set G) := by
    rw [h.normalizer_VZ]
    exact h.inM.2 htT
  have h2 : t * a * t⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp hTM a).mp haV
  have h3 := hhatV (D.π (t * a * t⁻¹)) (D.π_mem_hat h2 (VZ_le_uOfL22 T M h2))
  show D.rho ⟨t, htN⟩ (D.π a) = D.π a
  rw [h1]
  rcases h3 with h0 | h0
  · exfalso
    apply hπa
    have h4 : D.rho ⟨t, htN⟩ (D.π a) = 0 := by rw [h1, h0]
    exact (LinearEquiv.map_eq_zero_iff _).mp h4
  · exact h0

theorem relIndex_img_T_dvd (h : Hyp1281Two G T M L) (D : HatModel T M) :
    (D.img T).relIndex (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) ∣
      T.index := by
  have hTH : T ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    h.almostSpecialHyp_g1.T_le_H
  have hHN : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (uOfL22 T M : Set G) := fun x hx => h.g1_le_normalizer_uOfL22 hx
  rw [D.img_eq_map T, D.img_eq_map (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)),
    ← Subgroup.relIndex_comap]
  have h2 : T.subgroupOf (Subgroup.normalizer (uOfL22 T M : Set G)) ≤
      Subgroup.comap D.rho
        ((T.subgroupOf (Subgroup.normalizer (uOfL22 T M : Set G))).map D.rho) :=
    Subgroup.le_comap_map _ _
  refine (Subgroup.relIndex_dvd_of_le_left
    ((Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).subgroupOf
      (Subgroup.normalizer (uOfL22 T M : Set G))) h2).trans ?_
  rw [Subgroup.relIndex_subgroupOf hHN]
  exact Subgroup.relIndex_dvd_index_of_le hTH

theorem odd_index_T (h : Hyp1281Two G T M L) : Odd T.index := by
  have := h.sylow.2
  exact Nat.odd_iff.mpr (by omega)

theorem odd_index_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (D : HatModel T M) {a : G} (haV : a ∈ VZ T M) (haZ : a ∉ quasithinOmegaOneCenter T) :
    Odd (MulAction.stabilizer
      ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) (D.π a)).index := by
  classical
  have hstab : MulAction.stabilizer
      ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) (D.π a) =
      (MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a)).subgroupOf
        (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) := by
    ext γ
    simp [MulAction.mem_stabilizer_iff]
  have hdvd1 : (MulAction.stabilizer
      ↥(D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) (D.π a)).index ∣
      (D.img T).relIndex (D.img (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))) := by
    rw [hstab]
    exact Subgroup.relIndex_dvd_of_le_left _ (h.img_T_le_stabilizer hU D haV haZ)
  exact Odd.of_dvd_nat h.odd_index_T (hdvd1.trans (h.relIndex_img_T_dvd D))

theorem commutator_le_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
    (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T) :
    ∀ γ ∈ D.img (rconj (wOfU T M) g), ∀ v, D.B (D.π a) v = 0 →
      γ v - v ∈ D.hat (wOfU T M ⊓ rconj (wOfU T M) g) := by
  intro γ hγ v hv
  obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  obtain ⟨w, hwW, hwU, rfl⟩ := D.mem_hat.mp ((h.mem_hat_wOfU_iff D haV haZ).mpr hv)
  rw [HatModel.rho_sub_π (D := D) hxN hwU]
  have hc : ⁅w, x⁆ ∈ wOfU T M ⊓ rconj (wOfU T M) g :=
    h.lemma_12_8_11_one hU hg (Subgroup.commutator_mem_commutator hwW hxX)
  have hinv : x * w * x⁻¹ * w⁻¹ = ⁅w, x⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hinv]
  have hcE : ⁅w, x⁆⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g :=
    (wOfU T M ⊓ rconj (wOfU T M) g).inv_mem hc
  exact D.π_mem_hat hcE (inf_le_left.trans (wOfU_le_uOfL22 T M) hcE)

theorem centralizer_le_img (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T) :
    ∀ γ ∈ D.img (rconj (wOfU T M) g), γ ∉ D.img (rconj (centerOf (uOfL22 T M)) g) →
      ∀ v, γ v = v → D.B (D.π a) v = 0 := by
  intro γ hγ hγZ v hv
  obtain ⟨x, hxX, hxN, rfl⟩ := HatModel.mem_img.mp hγ
  by_contra hB
  obtain ⟨u, huU, rfl⟩ := D.π_surj v
  have huW : u ∉ wOfU T M := fun huW =>
    hB ((h.mem_hat_wOfU_iff D haV haZ).mp (D.π_mem_hat huW huU))
  have hcomm := D.comm_mem_centerOf_of_fix hxN huU hv
  have h9 := h.lemma_12_8_9_six hU hg huU huW hxX hcomm
  apply hγZ
  have hEU : wOfU T M ⊓ rconj (wOfU T M) g ≤ uOfL22 T M :=
    inf_le_left.trans (wOfU_le_uOfL22 T M)
  rw [← h.img_sup_eq_of_le D
    ((rconj_centerOf_le_rconj_wOfU T M g).trans (h.rconj_wOfU_le_normalizer_uOfL22 hU hg)) hEU]
  exact HatModel.rho_mem_img h9 hxN

end Hyp1281Two

end CFSG.Quasithin
