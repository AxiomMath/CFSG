module

public import CFSG.Quasithin.EmptyFaithful.S153EH60A
public import CFSG.Quasithin.EmptyFaithful.S153E59E

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153EH60

theorem commute_of_conj_central {Γ : Type*} [Group Γ] {d x c : Γ} (hc : ∀ g : Γ, g * c = c * g)
    (hc2 : c * c = 1) (hdx : d * x * d⁻¹ = x * c) (hd3 : d ^ 3 = 1) : d * x = x * d := by
  have h2 : d * d * x * (d * d)⁻¹ = x := by
    calc d * d * x * (d * d)⁻¹ = d * (d * x * d⁻¹) * d⁻¹ := by group
      _ = d * (x * c) * d⁻¹ := by rw [hdx]
      _ = (d * x * d⁻¹) * (d * c * d⁻¹) := by group
      _ = x * c * c := by rw [hdx, hc d, mul_inv_cancel_right]
      _ = x := by rw [mul_assoc, hc2, mul_one]
  have h4 : d = (d * d) * (d * d) := by
    calc d = d * d ^ 3 := by rw [hd3, mul_one]
      _ = (d * d) * (d * d) := by rw [pow_three]; simp only [mul_assoc]
  have h5 : (d * d) * x = x * (d * d) := mul_inv_eq_iff_eq_mul.mp h2
  calc d * x = ((d * d) * (d * d)) * x := by rw [← h4]
    _ = (d * d) * ((d * d) * x) := by group
    _ = (d * d) * (x * (d * d)) := by rw [h5]
    _ = ((d * d) * x) * (d * d) := by group
    _ = x * (d * d) * (d * d) := by rw [h5]
    _ = x * d := by rw [mul_assoc, ← h4]

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem ker_rho_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    (S153E59.rho cx).ker = (pCoreOf 2 Mc).subgroupOf Mc := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, S153E59.rho_eq_one_iff]

theorem isPGroup_ker_rho (cx : Ctx15350 T Mc M V₁ V₂ t) : IsPGroup 2 (S153E59.rho cx).ker := by
  rw [ker_rho_eq cx]
  exact (pCoreOf_isPGroup 2 Mc).of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 Mc)).symm

theorem sq_eq_one_of_mem_Z (cx : Ctx15350 T Mc M V₁ V₂ t) {z : G}
    (hz : z ∈ quasithinOmegaOneCenter T) : z * z = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : ↥(quasithinOmegaOneCenter T)))
  rw [S153E59.card_Z cx, pow_two] at h
  exact congrArg Subtype.val h

theorem secH_mem_UT (cx : Ctx15350 T Mc M V₁ V₂ t) {x : ↥Mc} (hx : (x : G) ∈ UH153 T M V₁ Mc) :
    S153E59.secH cx x ∈ S153E59.UT T M V₁ Mc :=
  secMk_mem_secImg (x := Subgroup.inclusion cx.hF.H_normalizes_V₁ x) hx

theorem rho_fix_of_mem (cx : Ctx15350 T Mc M V₁ V₂ t) {D : Subgroup ↥Mc} {x : ↥Mc}
    (hx : x ∈ Subgroup.centralizer (D : Set ↥Mc)) {d : ↥Mc} (hd : d ∈ D)
    (w : ↥(S153E59.UT T M V₁ Mc)) (hw : (w : S153E59.GT T) = S153E59.secH cx x) :
    S153E59.rho cx d w = w := by
  apply Subtype.ext
  rw [S153E59.rho_apply_coe, hw]
  have h1 : d * x = x * d := Subgroup.mem_centralizer_iff.mp hx d hd
  calc S153E59.secH cx d * S153E59.secH cx x * (S153E59.secH cx d)⁻¹
      = S153E59.secH cx (d * x * d⁻¹) := by simp only [map_mul, map_inv]
    _ = S153E59.secH cx x := by rw [h1, mul_inv_cancel_right]

theorem mem_centralizer_of_fix (cx : Ctx15350 T Mc M V₁ V₂ t) {D : Subgroup ↥Mc}
    (hD3 : ∀ d ∈ D, d ^ 3 = 1) {x : ↥Mc} (hxU : (x : G) ∈ UH153 T M V₁ Mc)
    (hfix : ∀ d ∈ D, S153E59.rho cx d ⟨S153E59.secH cx x, secH_mem_UT cx hxU⟩ =
      ⟨S153E59.secH cx x, secH_mem_UT cx hxU⟩) :
    x ∈ Subgroup.centralizer (D : Set ↥Mc) := by
  refine Subgroup.mem_centralizer_iff.mpr fun d hd => ?_
  have h1 := congrArg Subtype.val (hfix d hd)
  rw [S153E59.rho_apply_coe] at h1
  have h2 : S153E59.secH cx (d * x * d⁻¹) = S153E59.secH cx x := by
    simp only [map_mul, map_inv]
    exact h1
  have h3 := (secMk_eq_secMk_iff (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (x := Subgroup.inclusion cx.hF.H_normalizes_V₁ x)
    (y := Subgroup.inclusion cx.hF.H_normalizes_V₁ (d * x * d⁻¹))).mp h2.symm
  have hcZ : (x : G)⁻¹ * ((d : G) * x * (d : G)⁻¹) ∈ quasithinOmegaOneCenter T := h3
  have hcMc : (x : G)⁻¹ * ((d : G) * x * (d : G)⁻¹) ∈ Mc :=
    S153E59.U_le_Mc cx (S153E59.Z_le_U cx hcZ)
  set c : ↥Mc := ⟨(x : G)⁻¹ * ((d : G) * x * (d : G)⁻¹), hcMc⟩ with hc
  refine commute_of_conj_central (c := c) (fun g => Subtype.ext (S153E59.Z_central cx g.2 hcZ))
    (Subtype.ext (sq_eq_one_of_mem_Z cx hcZ)) ?_ (hD3 d hd)
  apply Subtype.ext
  simp [hc]

theorem mem_UT_of_mem_map (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc) {D : Subgroup ↥Mc} {y : S153E59.GT T}
    (hy : y ∈ ((S153E59.rho cx).ker ⊓ Subgroup.centralizer (D : Set ↥Mc)).map (S153E59.secH cx)) :
    y ∈ S153E59.UT T M V₁ Mc := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  refine secH_mem_UT cx ?_
  rw [hUQ]
  exact (S153E59.rho_eq_one_iff cx x).mp (MonoidHom.mem_ker.mp hx.1)

theorem rho_fix_of_mem_map (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc) {D : Subgroup ↥Mc} {y : S153E59.GT T}
    (hy : y ∈ ((S153E59.rho cx).ker ⊓ Subgroup.centralizer (D : Set ↥Mc)).map (S153E59.secH cx))
    {d : ↥Mc} (hd : d ∈ D) :
    S153E59.rho cx d ⟨y, mem_UT_of_mem_map cx hUQ hy⟩ = ⟨y, mem_UT_of_mem_map cx hUQ hy⟩ := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact rho_fix_of_mem cx hx.2 hd _ rfl

theorem mem_map_of_fix (cx : Ctx15350 T Mc M V₁ V₂ t) (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc)
    {D : Subgroup ↥Mc} (hD3 : ∀ d ∈ D, d ^ 3 = 1) (w : ↥(S153E59.UT T M V₁ Mc))
    (hw : ∀ d ∈ D, S153E59.rho cx d w = w) :
    (w : S153E59.GT T) ∈ ((S153E59.rho cx).ker ⊓ Subgroup.centralizer (D : Set ↥Mc)).map
      (S153E59.secH cx) := by
  obtain ⟨u, huU, huw⟩ := S153E59.exists_eq_secMk_of_mem_UT w
  set x : ↥Mc := ⟨(u : G), S153E59.U_le_Mc cx huU⟩ with hx
  have hxw : S153E59.secH cx x = (w : S153E59.GT T) := by
    rw [← huw]
    rfl
  have hker : x ∈ (S153E59.rho cx).ker := by
    rw [MonoidHom.mem_ker, S153E59.rho_eq_one_iff, ← hUQ]
    exact huU
  have hfix : ∀ d ∈ D, S153E59.rho cx d ⟨S153E59.secH cx x, secH_mem_UT cx huU⟩ =
      ⟨S153E59.secH cx x, secH_mem_UT cx huU⟩ := by
    intro d hd
    have : (⟨S153E59.secH cx x, secH_mem_UT cx huU⟩ : ↥(S153E59.UT T M V₁ Mc)) = w :=
      Subtype.ext hxw
    rw [this]
    exact hw d hd
  exact ⟨x, ⟨hker, mem_centralizer_of_fix cx hD3 huU hfix⟩, hxw⟩

theorem card_ker_inf_centralizer (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hUQ : UH153 T M V₁ Mc = pCoreOf 2 Mc) {D : Subgroup ↥Mc} (hD3 : ∀ d ∈ D, d ^ 3 = 1) :
    Nat.card ↥((S153E59.rho cx).ker ⊓ Subgroup.centralizer (D : Set ↥Mc)) =
      2 * Nat.card {w : ↥(S153E59.UT T M V₁ Mc) // ∀ d ∈ D, S153E59.rho cx d w = w} := by
  set Cu := (S153E59.rho cx).ker ⊓ Subgroup.centralizer (D : Set ↥Mc) with hCu
  have h1 := card_map_mul_card_inf_ker (S153E59.secH cx) Cu
  have hZ : quasithinOmegaOneCenter T ≤ Mc := (S153E59.Z_le_U cx).trans (S153E59.U_le_Mc cx)
  have hker : (S153E59.secH cx).ker ⊓ Cu = (quasithinOmegaOneCenter T).subgroupOf Mc := by
    ext x
    constructor
    · rintro ⟨hx1, -⟩
      exact secMk_eq_one_iff.mp hx1
    · intro hx
      have hxZ : (x : G) ∈ quasithinOmegaOneCenter T := hx
      refine ⟨secMk_eq_one_iff.mpr hxZ, ?_, ?_⟩
      · change x ∈ (S153E59.rho cx).ker
        rw [MonoidHom.mem_ker, S153E59.rho_eq_one_iff, ← hUQ]
        exact S153E59.Z_le_U cx hxZ
      · refine Subgroup.mem_centralizer_iff.mpr fun d _ => Subtype.ext ?_
        exact S153E59.Z_central cx d.2 hxZ
  have hcard : Nat.card ↥((S153E59.secH cx).ker ⊓ Cu) = 2 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ).toEquiv, S153E59.card_Z cx]
  have himg : Nat.card ↥(Cu.map (S153E59.secH cx)) =
      Nat.card {w : ↥(S153E59.UT T M V₁ Mc) // ∀ d ∈ D, S153E59.rho cx d w = w} := by
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, mem_UT_of_mem_map cx hUQ y.2⟩, fun d hd =>
          rho_fix_of_mem_map cx hUQ y.2 hd⟩
        invFun := fun w => ⟨w.1.1, mem_map_of_fix cx hUQ hD3 w.1 w.2⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun w => Subtype.ext (Subtype.ext rfl) }
  rw [← h1, hcard, himg, mul_comm]

end Context

end S153EH60

end CFSG.Quasithin
