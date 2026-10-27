module

public import CFSG.Quasithin.H13.A6S13825x

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

theorem V3_le_of_v2_mem {g : ↥(Subgroup.normalizer (V : Set G))}
    (hg : S.frame.ρ g = swap 0 1 * swap 1 2) {W : Subgroup G} (hV₁W : fsuV1 T V ≤ W)
    (hgW : (g : G) ∈ Subgroup.normalizer (W : Set G)) (hv : S.v2 ∈ W) : S.V3 ≤ W := by
  have hg2W : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hgW 2
  have h1 : (g : G) * S.v2 * (g : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hgW _).mp hv
  have h2 : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hg2W _).mp hv
  intro u hu
  rcases S.mem_V3_cases hg hu with h | h | h | h
  · exact hV₁W h
  · have := W.mul_mem (hV₁W h) (W.inv_mem hv)
    rwa [mul_inv_cancel_right] at this
  · have := W.mul_mem (hV₁W h) (W.inv_mem h1)
    rwa [mul_inv_cancel_right] at this
  · have := W.mul_mem (hV₁W h) (W.inv_mem h2)
    rwa [mul_inv_cancel_right] at this

variable {S}

theorem v2_not_mem {H : Subgroup G} (hH : H ∈ S.Hz) {W : Subgroup G}
    (hV₁W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) : S.v2 ∉ W := by
  intro hv
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have h3 := S.V3_le_of_v2_mem hg hV₁W (hHW (hL1H hgL)) hv
  exact hWU.not_ge (conjClosure_le fun h hh v hv =>
    (Subgroup.mem_normalizer_iff.mp (hHW hh) v).mp (h3 hv))

theorem comm_v2_not_mem {H : Subgroup G} (hH : H ∈ S.Hz) {W : Subgroup G}
    (hV₁W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G)) {g : ↥(Subgroup.normalizer (V : Set G))}
    (hgL : (g : G) ∈ S.L1) (hg : S.frame.ρ g = swap 0 1 * swap 1 2) :
    (g : G) * S.v2 * (g : G)⁻¹ * S.v2⁻¹ ∉ W := by
  intro hc
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hgW : (g : G) ∈ Subgroup.normalizer (W : Set G) := hHW (hL1H hgL)
  have hv2 : S.v2 * S.v2 = 1 := S.v2_mul_self
  have hcomm : S.v2 * ((g : G) * S.v2 * (g : G)⁻¹) =
      (g : G) * S.v2 * (g : G)⁻¹ * S.v2⁻¹ := by
    have hV : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
      F7.isElemAbelian_comm S.elemAbelian_V hx hy
    rw [hV _ S.v2_mem_V _ (S.conj_v2_mem_V g), inv_eq_of_mul_eq_one_right hv2]
  have h2 : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) * S.v2 *
      ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ ∈ W := by
    rw [← S.v2_mul_conj hg, hcomm]
    exact hc
  have hg2W : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
      Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ hgW 2
  exact v2_not_mem hH hV₁W hWU hHW ((Subgroup.mem_normalizer_iff.mp hg2W _).mpr h2)

variable (S) in
theorem comm_T_v2 {t : G} (ht : t ∈ T) : t * S.v2 * t⁻¹ * S.v2⁻¹ ∈ fsuV1 T V := by
  have htV1 : t ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.T_le_NV1 ht
  have hx : t * S.v2 * t⁻¹ ∈ S.V2 :=
    (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_V2 ht) _).mp S.v2_mem_V2
  have hidx : ((fsuV1 T V).subgroupOf S.V2).index = 2 := by
    have h1 := ((fsuV1 T V).subgroupOf S.V2).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.V1_le_V2).toEquiv, S.card_V2,
      S.card_V1] at h1
    omega
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨_, hx⟩)
    (b := (⟨S.v2, S.v2_mem_V2⟩ : ↥S.V2)⁻¹)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
  have hxV1 : t * S.v2 * t⁻¹ ∉ fsuV1 T V := fun h =>
    S.v2_not_mem_V1 ((Subgroup.mem_normalizer_iff.mp htV1 _).mpr h)
  have hv2V1 : S.v2⁻¹ ∉ fsuV1 T V := fun h =>
    S.v2_not_mem_V1 (by simpa using (fsuV1 T V).inv_mem h)
  exact key.2 ⟨fun h => absurd h hxV1, fun h => absurd h hv2V1⟩

theorem x4_mem_unitriangular (s : Fin 3) : B42Ln.x4 s ∈ unitriangular 4 (ZMod 2) := by
  rw [mem_unitriangular, B42Ln.coe_x4]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · simp only [B42Ln.xM4, Matrix.of_apply]
    split_ifs with h1 h2
    · exact absurd h1 hji.ne'
    · obtain ⟨rfl, rfl⟩ := h2
      exact absurd Fin.castSucc_lt_succ (lt_asymm hji)
    · rfl
  · simp [B42Ln.xM4]

theorem false_of_wedge {M : Type} [CommGroup M] [Module (ZMod 2) (Additive M)]
    {X : Subgroup (MulAut M)} (e' : ↥X ≃* SpecialLinearGroup (Fin 4) (ZMod 2))
    {β : Additive M ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}
    (hβ : ∀ g w, β (B42Ln.repOf4 (B42Ln.phiOf4 (e'.trans B42Ln.E4)) g w) =
      B42Ln.wedgeRep4' g (β w))
    {v : M} (hv1 : v ≠ 1)
    (hfix : ∀ i : Fin 3, ∃ x : ↥X, e' x = B42Ln.x4 i ∧ (x : MulAut M) v = v)
    {y : MulAut M} (hy : y ∈ X) (hyQ : e' ⟨y, hy⟩ ∈ flagStabilizer 4 (ZMod 2) {2})
    (hyv : y v ≠ v) : False := by
  have hphi : ∀ x : ↥X, B42Ln.phiOf4 (e'.trans B42Ln.E4) x = e' x := fun x => by
    simp [B42Ln.phiOf4]
  have hwedge : ∀ (x : ↥X) (u : M), β (Additive.ofMul ((x : MulAut M) u)) =
      JonesParshall.wedgeMat4 ((e' x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ β (Additive.ofMul u) := by
    intro x u
    have := hβ (B42Ln.phiOf4 (e'.trans B42Ln.E4) x) (Additive.ofMul u)
    rw [B42Ln.repOf4_apply_iso, B42Ln.wedgeRep4'_apply, hphi] at this
    exact this
  set w := β (Additive.ofMul v) with hw
  have hfixs : ∀ i : Fin 3, JonesParshall.wedgeMat4 (B42Ln.xM4 i) *ᵥ w = w := by
    intro i
    obtain ⟨x, hxe, hxv⟩ := hfix i
    have h1 := hwedge x v
    rw [hxe, B42Ln.coe_x4, hxv] at h1
    exact h1.symm
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv1
    have : Additive.ofMul v = 0 := β.injective (h0.trans β.map_zero.symm)
    exact Additive.ofMul.injective (this.trans ofMul_one.symm)
  have hwe : w = Pi.single 0 1 := (B42Ln.fixed_checks.2.2 w hfixs).resolve_left hw0
  have h1 := hwedge ⟨y, hy⟩ v
  rw [← hw, hwe, L13825.wedge_fix_of_mem_flag hyQ, ← hwe] at h1
  exact hyv (Additive.ofMul.injective (β.injective h1))

end Setting4

end CFSG.Quasithin.H13.A6
