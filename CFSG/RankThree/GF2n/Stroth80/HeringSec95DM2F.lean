module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM2E
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DMT
public import CFSG.RankThree.GF2n.Stroth80.Sec78CV

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups Pointwise


theorem m1_of_module (hMod : Step95ModuleStatement) (h34 : Stroth34Statement)
    (h91b : Stroth91bStatement) (hA : Sec9AExistsStatement) (n0 : ℕ) :
    Step95M1Statement n0 := by
  intro G _ _ M Q Z B hc n t hs _hn K _ _ _ γ M₀ hglob φ hφπ hφQ
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  obtain ⟨vd⟩ := HS9.exists_vdesc95 h34 hA hs hglob hφπ
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨hdir, hWV⟩ := h91b G M Q Z B hc n t hs r hr _ _ rfl rfl
  have hcwr := cwr95_of h91b hA G M Q Z B hc n t hs
  have hcwlb := cwlb95_of h91b hA G M Q Z B hc n t hs
  have hVW := sec7ctr_Vt_le_Wt h34 hc hs5
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hel := hc.Vt_isElemAbelian h35 ht hs5.notQ
  let S : HS9.SetupW hc t M₀ φ :=
    { glob := hglob
      hφπ := hφπ
      hφQ := hφQ
      hφQf := HS9.qf_phi_inv hc M₀ φ hφπ
      hWV := hWV
      ht := ht
      hVW := hVW
      vd := vd
      hVsq := fun v hv => by
        rw [← pow_two]
        exact hel.2 v hv }
  have hq4 : 4 ≤ Nat.card K := by
    rw [hglob.card]
    exact hc.hyp.q4
  have hD : ∃ g h : SL(2, K), (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
      (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∧
      IsCompl S.Xfix (S.Xfix.map ((S.Act (g, h) : S.Wq ≃ₗ[K] S.Wq) : S.Wq →ₗ[K] S.Wq)) :=
    ⟨(S.vd.ρ ⟨r, hr.mem⟩).1, (S.vd.ρ ⟨r, hr.mem⟩).2, (S.rho_opposite hr).1,
      (S.rho_opposite hr).2, S.isCompl_Xfix h34 hs hr rfl rfl rfl rfl hdir hcwlb⟩
  have hΘ : ∃ Θ : AddSubgroup (S.Wq →ₗ[K] Matrix (Fin 2) (Fin 2) K),
      (∀ θ ∈ Θ, ∀ (a a' : K) w, θ (S.Act (HS9.M1.uSL a, HS9.M1.uSL a') w) =
        HS9.M1.uMat a * θ w * (HS9.M1.uMat a')ᵀ) ∧
      ∀ x ∈ S.Xfix, (∀ θ ∈ Θ, θ x = 0) → x = 0 :=
    ⟨S.Theta, fun θ hθ a a' w => S.Theta_equivariant h34 hs hθ a a' w,
      fun x hx hθ => S.eq_zero_of_Theta_eq_zero h34 hs hcwlb hx hθ⟩
  obtain ⟨Y₁, Y₂, i1, i2, i3, i4, β₁, β₂, c, hβ₁a, hβ₁n, hβ₂a, hβ₂n, hcact, hform⟩ :=
    hMod K hq4 S.Wq S.Act S.bwq S.qwq S.bwq_alt S.bwq_nondeg S.Act_bwq S.qwq_smul S.qwq_add
      S.Act_qwq S.Xfix (fun a a' w => S.act_sub_mem_Xfix h34 hs a a' w)
      (fun a a' x hx => hx a a') (fun w hw => hw) hD
      (fun w hw => S.eq_zero_of_fix_Gamma hcwr w hw) hΘ
  refine ⟨Y₁, Y₂, i1, i2, i3, i4, ?_⟩
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective S.Wsub.subtype
    (Submodule.ker_subtype _)
  have hPw : ∀ (w : M₀.E) (hw : w ∈ S.Wsub), P w = ⟨w, hw⟩ := fun w hw => by
    have := LinearMap.congr_fun hP ⟨w, hw⟩
    simpa using this
  let cW : M₀.E →ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂) :=
    (c : S.Wq ≃ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂)).toLinearMap ∘ₗ S.mkW ∘ₗ P
  have hcW : ∀ (w : M₀.E) (hw : w ∈ S.Wsub), cW w = c (S.mkW ⟨w, hw⟩) := fun w hw => by
    show c (S.mkW (P w)) = _
    rw [hPw w hw]
  exact ⟨
    { β₁ := β₁
      β₂ := β₂
      cV := S.vd.cV
      cW := cW
      ρ := S.vd.ρ
      β₁_alt := hβ₁a
      β₁_nd := hβ₁n
      β₂_alt := hβ₂a
      β₂_nd := hβ₂n
      cV_inj := S.vd.cV_inj
      cV_surj := S.vd.cV_surj
      cW_ker := fun w hw => by
        rw [hcW w hw, c.map_eq_zero_iff, S.mkW_eq_zero_iff]
        exact S.mem_Vsub
      cW_surj := fun y => by
        obtain ⟨u, hu⟩ := S.mkW_surjective (c.symm y)
        refine ⟨u, u.2, ?_⟩
        rw [hcW u u.2, hu]
        exact c.apply_symm_apply y
      ρ_surj := S.vd.ρ_surj
      cV_act := S.vd.cV_act
      cW_act := fun r w hw => by
        have hrH := hc.Rt_le_H0 t r.2
        have hwW : w ∈ S.Wsub := hw
        have hgw : HS9.actM φ (r : G) w ∈ S.Wsub := S.actM_mem_W r.2 hw
        have h1 : φ ⟨(r : G), hrH⟩ w = HS9.actM φ (r : G) w := by
          rw [HS9.actM_of_mem (φ := φ) hrH]
        rw [h1, hcW _ hgw, hcW w hwW]
        have h2 : S.mkW ⟨HS9.actM φ (r : G) w, hgw⟩ = S.Act (S.vd.ρ r) (S.mkW ⟨w, hwW⟩) := by
          rw [S.Act_rho]
          rfl
        rw [h2, hcact]
        rfl
      form := fun w hw w' hw' => by
        rw [hcW w hw, hcW w' hw', ← hform]
        rfl
      point := S.vd.point }⟩

end CFSG.RankThree.GF2n.Stroth80
