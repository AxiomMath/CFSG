module

public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
import CFSG.RankThree.GF2n.Stroth80.Sec123Order

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.comm_T_Wt_mem_Z (hc : Ctx M Q Z B)
    (h35 : CQt Q Z (LB M Q B) = ((B ⊔ Z : Subgroup G) : Set G)) {t : G}
    (ht : t ∈ LB M Q B) (hnotQB : ¬ Vt M (LB M Q B) B Z t ≤ QB B) {x : G}
    (hxL : x ∈ LB M Q B) (hxR : ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ Q) {w : G}
    (hw : w ∈ Wt Q (Vt M (LB M Q B) B Z t)) : ⁅x, w⁆ ∈ Z := by
  set V := Vt M (LB M Q B) B Z t
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hxM : x ∈ M := hc.LB_le_M hxL
  have hxH : x ∈ H0 M Z := hc.LB_le_H0 hxL
  have hZQB : Z ≤ Q ⊓ QB B := le_inf hc.Z_le_Q (hc.Z_le_QB).1
  have hBV : B ≤ V := by
    have h := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t)
      M.one_mem (show t ∈ conjSubgroup (1 : G) (LB M Q B) by rw [conjSubgroup_one]; exact ht)
    rwa [conjSubgroup_one] at h
  obtain ⟨n, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, -, -⟩ := exists_actionHom_H0 hc.hyp h
  let Wsub : Submodule (GaloisField 2 n) M₀.E :=
    imgSub M₀ (Wt Q V) (fun c _ he => smul_mem_img_Wt M₀ h.reg hVQ c he)
  let S : M₀.E ≃ₗ[GaloisField 2 n] M₀.E := φ ⟨x, hxH⟩
  let A : M₀.E →ₗ[GaloisField 2 n] M₀.E := (S : M₀.E →ₗ[GaloisField 2 n] M₀.E) - 1
  have hAapp : ∀ e, A e = S e - e := fun e => rfl
  let Sp : Submodule (GaloisField 2 n) M₀.E := Wsub.map A
  have hWB : ∀ u ∈ Wt Q V, ⁅x, u⁆ ∈ Q ⊓ QB B := fun u hu =>
    hc.comm_LB_mem_inf hxL hu.1 (Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_iff.mp hu.2 g (hBV hg))
  have hAπ : ∀ u ∈ Wt Q V, A (M₀.π u) = M₀.π ⁅x, u⁆ := by
    intro u hu
    have huQ : u ∈ Q := hu.1
    have hxu : x * u * x⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hxM) u).mp huQ
    have huinv : u⁻¹ ∈ Q := Q.inv_mem huQ
    have e1 : ⁅x, u⁆ = (x * u * x⁻¹) * u⁻¹ := by rw [commutatorElement_def]
    have e4 : M₀.π (x * u * x⁻¹) = S (M₀.π u) := hφπ ⟨x, hxH⟩ u huQ
    rw [hAapp, e1, M₀.π_mul _ hxu _ huinv, M₀.pi_inv huQ, e4, sub_eq_add_neg]
  have hAmem : ∀ u ∈ Wt Q V, M₀.π ⁅x, u⁆ ∈ M₀.img (Q ⊓ QB B) := fun u hu =>
    M₀.pi_mem_img (hWB u hu) (Subgroup.mem_inf.mp (hWB u hu)).1
  have hSp_sub : ∀ e ∈ Sp, e ∈ M₀.img (Q ⊓ QB B) := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp he
    obtain ⟨u, hu, -, rfl⟩ := (M₀.mem_img).mp (mem_imgSub.mp hv)
    rw [hAπ u hu]
    exact hAmem u hu
  have hSp_ne : ¬ ⁅x, w⁆ ∈ Z → Sp ≠ ⊥ := by
    intro hcon hbot
    have hmem : M₀.π ⁅x, w⁆ ∈ Sp :=
      Submodule.mem_map.mpr ⟨M₀.π w, mem_imgSub.mpr (M₀.pi_mem_img hw hw.1), hAπ w hw⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hcon ((M₀.π_ker _ (Subgroup.mem_inf.mp (hWB w hw)).1).mp hmem)
  have hInv : ∀ l ∈ Rt M (LB M Q B) t, ∀ S' : M₀.E ≃ₗ[GaloisField 2 n] M₀.E,
      (∀ y ∈ Q, M₀.π (l * y * l⁻¹) = S' (M₀.π y)) → (∀ e, M₀.Qf (S' e) = M₀.Qf e) →
        ∀ v ∈ Sp, S' v ∈ Sp := by
    intro l hl S' hS' _ v hv
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
    have hcomm : ∀ e, S' (S e) = S (S' e) := fun e =>
      hc.hyp.comm_action (hc.Rt_le_M t hl) hxM (hxR l hl) hS'
        (fun y hy => hφπ ⟨x, hxH⟩ y hy) e
    obtain ⟨w₀, hw₀, -, rfl⟩ := (M₀.mem_img).mp (mem_imgSub.mp hu)
    have hlw : l * w₀ * l⁻¹ ∈ Wt Q V :=
      conj_mem_Wt (hc.hyp.Q_normal.2 (hc.Rt_le_M t hl)) (hc.Rt_normalizes_Vt ht hl) hw₀
    have hSu : S' (M₀.π w₀) ∈ Wsub := by
      rw [← hS' w₀ hw₀.1]
      exact mem_imgSub.mpr (M₀.pi_mem_img hlw hlw.1)
    refine Submodule.mem_map.mpr ⟨S' (M₀.π w₀), hSu, ?_⟩
    rw [hAapp, hAapp, map_sub, hcomm]
  by_contra hcon
  have hinv := hc.img_Vt_le_of_invariant h35 h t Sp (hSp_ne hcon) hInv
  apply hnotQB
  intro v hv
  have hvQ : v ∈ Q := hVQ hv
  have h1 : M₀.π v ∈ M₀.img (Q ⊓ QB B) := hSp_sub _ (hinv _ (M₀.pi_mem_img hv hvQ))
  exact (Subgroup.mem_inf.mp ((M₀.mem_img_iff hZQB hvQ).mp h1)).2

end CFSG.RankThree.GF2n.Stroth80
