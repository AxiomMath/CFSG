module

public import CFSG.Quasithin.Background.Harris.R1.R1bLoc
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Lift
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Close
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Rel3
public import CFSG.Quasithin.Background.Harris.R1.NormGensL28Prod
public import CFSG.Quasithin.Background.Harris.R1.L28BorelModel

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.LieType.BorelTits
open D4Vert

theorem normGensL28Stmt_of_model
    (hM : L28BorelModel) : NormGensL28Stmt := by
  intro G _ _ K1 L2 S Zs hset hZS hL hna hQK hSK
  classical
  obtain ⟨Ω, hΩf, C, hodd, hcard, -⟩ :=
    famStmt_holds G K1 L2 S Zs hset 3 (by norm_num) (Or.inl hL) hna
  have hΩ : Fintype.card Ω = 9 := by rw [hcard hL]; norm_num
  have hcen := centerBender_holds G K1 L2 S Zs hset ⟨3, by norm_num, Or.inl hL⟩ hna
  have hWK : vBeta K1 L2 S Zs ≤ K1 := by rw [← hQK]; exact pCoreOf_le 2 K1
  obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j : Ω, i ≠ j := Fintype.exists_pair_of_one_lt_card (by omega)
  set z : G := C.cm i₀ j₀ with hzdef
  have hz : z ∈ Zs := C.cm_mem i₀ j₀
  have hz1 : z ≠ 1 := C.cm_ne_one hij₀
  have hz2 : z * z = 1 := C.Zs_sq hz
  have hσ0 : IsSignChoice C z C.zf := fun ω => Or.inl rfl
  obtain ⟨a, b, ha, hb, hl28, huc, haB, hcos, hab⟩ :=
    exists_l28_signStab C hM hΩ hL hQK hSK hcen hz hz1 hσ0
  have haK : a ∈ K1 := signStab_le C C.zf ha
  have hbK : b ∈ K1 := signStab_le C C.zf hb
  set h : Fin 9 → G := fun i => evalWord ![a, b] (l28H.getD i []) with hhdef
  have hh : ∀ i, h i ∈ signStab C C.zf := fun i => lift28_evalWord_mem _ ha hb _
  have hzK : ∀ k ∈ K1, z * k = k * z := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) z hz
  obtain ⟨σ, hσ, hst, hP⟩ := l28_sign_relator C hz hz1 hij₀ rfl hσ0 hcen hΩ h
    (fun i => signStab_le C C.zf (hh i)) hh hcos
  have ha' : a ∈ signStab C σ := hst ▸ ha
  have hb' : b ∈ signStab C σ := hst ▸ hb
  have hcl : Subgroup.closure ({a, b} : Set G) ≤ signStab C σ := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    exacts [ha', hb']
  set x : G := σ C.D.pt with hxdef
  have hxW : x ∈ vBeta K1 L2 S Zs := hσ.mem_vBeta C hz _
  have hxV : x ∈ conjClosure Zs L2 := by
    have hzV : z ∈ conjClosure Zs L2 := le_conjClosure Zs L2 hz
    have hf : C.zf C.D.pt ∈ conjClosure Zs L2 := C.Vf_pt ▸ C.zf_mem C.D.pt
    rcases hσ C.D.pt with h1 | h1
    · rw [hxdef, h1]; exact hf
    · rw [hxdef, h1]; exact (conjClosure Zs L2).mul_mem hzV hf
  have hxZ : x ∉ Zs := by
    intro hx
    rcases hσ C.D.pt with h1 | h1
    · exact C.zf_not_mem C.D.pt (h1 ▸ hx)
    · apply C.zf_not_mem C.D.pt
      have : C.zf C.D.pt = z⁻¹ * x := by rw [hxdef, h1]; group
      rw [this]
      exact Zs.mul_mem (Zs.inv_mem hz) hx
  have hcomm_of : ∀ y ∈ l28Borel a b, x * y = y * x := by
    intro y hy
    have hyB := huc hy
    have hyσ : y ∈ signStab C σ := by
      have : l28Borel a b ≤ Subgroup.closure ({a, b} : Set G) := by
        rw [l28Borel, Subgroup.closure_le]
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact lift28_evalWord_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)) _
        · exact lift28_evalWord_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp)) _
      exact hcl (this hy)
    have := conj_sigma_pt C hyσ hyB
    calc x * y = (y * x * y⁻¹) * y := by rw [hxdef, this]
      _ = y * x := by group
  have hxc : x * evalWord ![a, b] l28C = evalWord ![a, b] l28C * x :=
    hcomm_of _ (Subgroup.subset_closure (by simp))
  have hxu : x * evalWord ![a, b] l28U = evalWord ![a, b] l28U * x :=
    hcomm_of _ (Subgroup.subset_closure (by simp))
  have hxa : x * a * x * a⁻¹ * x⁻¹ * a * x⁻¹ * a⁻¹ = z := by
    have h11 := rel11_of_sign C hz hij₀ rfl hσ ha' haB
    rw [← hxdef] at h11
    rw [← h11]
    group
  refine ⟨z, x, a, b, hz, hz1, hxV, hxZ, haK, hbK, ?_,
    closure_signStab_eq C hz hz1 hσ hWK ha' hb' hab (Or.inl rfl)⟩
  exact evalWord_hRels hz2 (C.Zs_central hxW hz).symm (hzK a haK) (hzK b hbK)
    (hσ.sq_eq_one C hz _) hl28 hxc hxu hxa hP

theorem normGensL28Stmt_holds :
    NormGensL28Stmt :=
  normGensL28Stmt_of_model l28BorelModel_holds

end CFSG.Quasithin.Background.Harris.R1
