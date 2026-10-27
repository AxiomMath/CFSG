module

public import CFSG.Quasithin.EmptyFaithful.S153NBForm
public import CFSG.Quasithin.EmptyFaithful.S153NBb3
public import CFSG.Quasithin.EmptyFaithful.S153NBb4
public import CFSG.Quasithin.EmptyFaithful.S153NBb5
public import CFSG.Quasithin.EmptyFaithful.S153NBb2

public section

namespace CFSG.Quasithin.S153N

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise
open CFSG.Quasithin.S153N.Bb

theorem formHyp_of_ctx67 {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t : G}
    (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (hcount : ∀ A : Subgroup G, IsMaxElemAbelian (TE153 T E) A →
        Nat.card (VE67 T M E) ≤ ((A ⊓ S1567.K167 T M E).relIndex A) ^ 2 *
          Nat.card ↥(VE67 T M E ⊓ Subgroup.centralizer (A : Set G))) :
    Nonempty (FormHyp G (Subgroup.centralizer (E : Set G)) (S1567.K167 T M E) M
      {A | IsMaxElemAbelian (TE153 T E) A}) := by
  have : IsMulCommutative ↥(VE67 T M E) := (S1567.VE67_isElemAbelian k).1
  obtain ⟨y, τ, hc⟩ := exists_choice h113 k
  have hN := S1567.normalizer_le_normalizer_VE67 T M E
  have hV0 : VZ T M ≤ VE67 T M E := S1567.VZ_le_VE67
  have hEV0 : E ≤ VZ T M := k.L.le_V
  have hNV : Subgroup.normalizer (VZ T M : Set G) = M := S1567.normalizer_V_eq k.c.hyp
  have hVE2 : ∀ v ∈ VE67 T M E, v ^ 2 = 1 := S1567.VE67_sq k
  have hN' : E ≤ VE67 T M E := hEV0.trans hV0
  let a : ↥(Subgroup.normalizer (E : Set G)) := ⟨y, hc.y_N⟩
  let b : ↥(Subgroup.normalizer (E : Set G)) := ⟨τ, hc.τ_N⟩
  have hω3 := actN_cube_apply hN a hc.y_cube
  have hσ2 := actN_sq_apply hN b (fun v hv => hc.τ_sq.2 v hv)
  have hωM : (a : G) ∈ Subgroup.normalizer (VZ T M : Set G) := by rw [hNV]; exact hc.y_M
  have hσM : (b : G) ∈ Subgroup.normalizer (VZ T M : Set G) := by rw [hNV]; exact hc.τ_M
  have hcard : Nat.card ↥(imgQ (VE67 T M E) E (VZ T M) hV0) = 4 := by
    have h := card_eq_mul_range hV0 hEV0
    rw [k.c.hyp.card_VZ, k.L.card_eq] at h
    change Nat.card ↥(projOn (VE67 T M E) E (VZ T M) hV0).range = 4
    omega
  have hmove := exists_moved_of_comm_not_mem hV0 hN a hc.y_V
  have hsq := Qt_sq (V := VE67 T M E) (E := E) hVE2
  exact ⟨{ Vb := Qt (VE67 T M E) E
           cg := cgQt (VE67 T M E) E
           fin := inferInstance
           sq := hsq
           ω := actN _ E hN a
           σ := actN _ E hN b
           ρ := rhoC _ E hN
           ω3 := hω3
           σ2 := hσ2
           ρω := fun c u => actN_comm_apply hN ⟨c, Subgroup.centralizer_le_normalizer _ c.2⟩ a
             (fun v hv => comm_mem_of_centralizer (hc.comm_y c c.2) v hv) u
           ρσ := fun c u => (actN_comm_apply hN b ⟨c, Subgroup.centralizer_le_normalizer _ c.2⟩
             (fun v hv => (hc.comm_τ c c.2).2 v hv) u).symm
           ker_eq := by
             ext c
             rw [Subgroup.mem_subgroupOf]
             exact ⟨fun h => ⟨c.2, (rhoC_ker hN c).1 h⟩, fun h => (rhoC_ker hN c).2 h.2⟩
           Vbar := imgQ (VE67 T M E) E (VZ T M) hV0
           card_Vbar := hcard
           ω_mem := fun u hu => actN_mem_imgQ hV0 hN a hωM hu
           σ_mem := fun u hu => actN_mem_imgQ hV0 hN b hσM hu
           ω_fpf := fpf_of_moves hsq _ hcard _ hω3 (fun u hu => actN_mem_imgQ hV0 hN a hωM hu) hmove
           σω_Vbar := fun u _ => actN_rel_apply hN a b
             (fun v hv => comm_mem_of_centralizer hc.rel v hv) hω3 u
           stab_iff := fun c => (stab_iff_abstract hEV0 hV0 hN c).trans (by rw [hNV])
           gen := closure_rhoC_eq_top rfl hN hV0 (fun g hg v hv => exists_conj_decomp k hg hv)
           elem := fun A hA => by
             refine ⟨le_centralizer_of_isMaxElemAbelian k hA, fun x hx z hz => ?_, hA.2.1.2⟩
             have := hA.2.1.1
             exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : ↥A) ⟨z, hz⟩)
           offender := fun A hA => by
             have hAE := le_centralizer_of_isMaxElemAbelian k hA
             have h1 := hcount A hA
             have h2 := card_inf_centralizer_le hN' hN hAE
             have h3 := card_Qt (V := VE67 T M E) (E := E) hN'
             have hE4 : Nat.card E = 4 := k.L.card_eq
             rw [hE4] at h2 h3
             have h4 : 4 * Nat.card (Qt (VE67 T M E) E) ≤
                 4 * (((A ⊓ S1567.K167 T M E).relIndex A) ^ 2 * Nat.card ↥(@fixV (Qt (VE67 T M E) E)
                  (cgQt (VE67 T M E) E) ((A.subgroupOf (Subgroup.centralizer (E : Set G))).map
                    (rhoC (VE67 T M E) E hN)))) := by
               calc 4 * Nat.card (Qt (VE67 T M E) E) = Nat.card (VE67 T M E) := h3.symm
                 _ ≤ _ := h1
                 _ ≤ ((A ⊓ S1567.K167 T M E).relIndex A) ^ 2 * (4 * Nat.card ↥(@fixV (Qt (VE67 T M E) E)
                  (cgQt (VE67 T M E) E) ((A.subgroupOf (Subgroup.centralizer (E : Set G))).map
                    (rhoC (VE67 T M E) E hN)))) := Nat.mul_le_mul_left _ h2
                 _ = _ := by ring
             exact Nat.le_of_mul_le_mul_left h4 (by norm_num) }⟩

end CFSG.Quasithin.S153N
