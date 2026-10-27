module

public import CFSG.Quasithin.Background.RonanG25GroupV

public section

namespace CFSG.Quasithin.RonanG25

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SL2Model
  CFSG.Quasithin.SL3Model
open scoped MatrixGroups Pointwise commutatorElement

section GroupOrd

variable {G : Type} [Group G] [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G}

theorem mem_normalizer_inf_pair {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  have h : x ∈ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (B : Set G) :=
    Subgroup.mem_inf.2 ⟨hA, hB⟩
  exact Subgroup.inf_normalizer_le_normalizer_inf h

theorem gS_le_LU : gS V H L ≤ L ⊔ conjClosure V H := Subgroup.map_subtype_le _

theorem SU_le_normalizer_lOne (St : L3Setting n V V₁ L T H) {g h : G}
    (hsub : SubFacts V L H g h) :
    gS V H L ⊔ conjClosure V H ≤ Subgroup.normalizer (lOne L V₁ : Set G) := by
  have hUL : conjClosure V H ≤ Subgroup.normalizer (L : Set G) := fun u hu => St.U_le_normL hu
  have hLU : L ⊔ conjClosure V H ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer hUL
  have hN : gS V H L ⊔ conjClosure V H ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₁ : Set G) : Subgroup G) : Set G) := by
    refine sup_le ?_ ?_
    · intro s hs
      have hsL : s ∈ Subgroup.normalizer (L : Set G) := hLU (gS_le_LU hs)
      have hsV₁ : s ∈ Subgroup.normalizer (V₁ : Set G) := by
        have hcen : ∀ v ∈ V, s * v = v * s := by
          intro v hv
          have hzc : v ∈ gS V H L ⊓ Subgroup.centralizer (gS V H L : Set G) :=
            hsub.V_le_center hv
          exact Subgroup.mem_centralizer_iff.1 hzc.2 s hs
        rw [Subgroup.mem_normalizer_iff]
        intro h
        constructor
        · intro hh
          have e : s * h * s⁻¹ = h := by
            rw [hcen h (St.hyp.base.le_V hh), mul_inv_cancel_right]
          rw [e]
          exact hh
        · intro hh
          have hc := hcen _ (St.hyp.base.le_V hh)
          have e : s * h * s⁻¹ = h := by
            calc s * h * s⁻¹ = s⁻¹ * (s * (s * h * s⁻¹)) := by group
              _ = s⁻¹ * (s * h * s⁻¹ * s) := by rw [hc]
              _ = h := by group
          rw [e] at hh
          exact hh
      exact mem_normalizer_inf_pair hsL (Subgroup.le_normalizer hsV₁)
    · intro u hu
      exact mem_normalizer_inf_pair (St.U_le_normL hu)
        (Subgroup.le_normalizer (St.hyp.base.T_le_normV₁ (St.U_le_T hu)))
  exact hN.trans (normalizer_le_normalizer_oTwoUpper _)

@[expose] noncomputable def piHom (St : L3Setting n V V₁ L T H) :
    ↥(lOne L V₁) →* Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 n) :=
  ablkHom.comp ((rho St.D).codRestrict (Pt (vE (GaloisField 2 n) 0))
    (fun x => St.theta_mem_Pt_of_normalizer ⟨x, lOne_le_L x.2⟩ (lOne_le_normalizer x.2)))

theorem piHom_coe (St : L3Setting n V V₁ L T H) (x : ↥(lOne L V₁)) :
    ((piHom St x : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 n)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) = ablk (rho St.D x) := by
  exact ablkHom_coe _

theorem piHom_ker (St : L3Setting n V V₁ L T H) {g h : G} (hsub : SubFacts V L H g h)
    (x : ↥(lOne L V₁)) :
    piHom St x = 1 ↔ (x : G) ∈ gS V H L ⊔ conjClosure V H := by
  have hxL : (x : G) ∈ L := lOne_le_L x.2
  have hxJ : (x : G) ∈ L ⊔ conjClosure V H := Subgroup.mem_sup_left hxL
  have hPhi : St.Phi ⟨(x : G), hxJ⟩ = rho St.D x := St.Phi_of_L ⟨(x : G), hxL⟩
  have hblk : piHom St x = 1 ↔ ablk (rho St.D x) = 1 := by
    constructor
    · intro h1
      have h2 : ((piHom St x : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 n)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) = 1 := by
        rw [h1, Units.val_one]
      rwa [piHom_coe] at h2
    · intro h1
      apply Units.ext
      rw [piHom_coe, Units.val_one]
      exact h1
  rw [hblk]
  have hSU : gS V H L ⊔ conjClosure V H ≤
      ((Qv (vE (GaloisField 2 n) 0)).comap St.Phi).map (L ⊔ conjClosure V H).subtype := by
    refine sup_le ?_ ?_
    · intro s hs
      have hsJ : s ∈ L ⊔ conjClosure V H := gS_le_LU hs
      refine Subgroup.mem_map.2 ⟨⟨s, hsJ⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      rw [(St.Phi_eq_one_iff_mem_S ⟨s, hsJ⟩).2 hs]
      exact one_mem _
    · intro u hu
      refine Subgroup.mem_map.2 ⟨⟨u, Subgroup.mem_sup_right hu⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      have h1 := St.betaU_mem_Qv ⟨u, hu⟩
      rw [St.betaU_apply] at h1
      exact h1
  constructor
  ·
    intro hblk1
    have hgPt : rho St.D x ∈ Pt (vE (GaloisField 2 n) 0) :=
      St.theta_mem_Pt_of_normalizer ⟨(x : G), lOne_le_L x.2⟩ (lOne_le_normalizer x.2)
    obtain ⟨h10, h20⟩ := Pt_entries hgPt
    have e11 : (rho St.D x).1 1 1 = 1 := by
      have h := congrFun (congrFun hblk1 0) 0
      simpa [ablk] using h
    have e12 : (rho St.D x).1 1 2 = 0 := by
      have h := congrFun (congrFun hblk1 0) 1
      simpa [ablk] using h
    have e21 : (rho St.D x).1 2 1 = 0 := by
      have h := congrFun (congrFun hblk1 1) 0
      simpa [ablk] using h
    have e22 : (rho St.D x).1 2 2 = 1 := by
      have h := congrFun (congrFun hblk1 1) 1
      simpa [ablk] using h
    have hdet : (rho St.D x).1.det = 1 := Matrix.SpecialLinearGroup.det_coe _
    have hg00 : (rho St.D x).1 0 0 = 1 := by
      rw [Matrix.det_fin_three, h10, h20, e11, e12, e21, e22] at hdet
      simpa using hdet
    have hgtq : tq ((rho St.D x).1 0 1) ((rho St.D x).1 0 2) = rho St.D x := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [tq_coe, h10, h20, e11, e12, e21, e22, hg00]
    have hgQv : rho St.D x ∈ Qv (vE (GaloisField 2 n) 0) := by
      rw [← hgtq]
      exact tq_mem_Qv _ _
    have hUbar : rho St.D x ∈ St.betaU.range := by
      show rho St.D x ∈ St.Ubar
      rw [St.Ubar_eq_Qv]
      exact hgQv
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hUbar
    rw [St.betaU_apply] at hu
    have huJ : (u : G) ∈ L ⊔ conjClosure V H := Subgroup.mem_sup_right u.2
    have hy : St.Phi (⟨(x : G), hxJ⟩ * (⟨(u : G), huJ⟩ : ↥(L ⊔ conjClosure V H))⁻¹) = 1 := by
      rw [map_mul, map_inv, hPhi, hu, mul_inv_cancel]
    have hxu : (x : G) * (u : G)⁻¹ ∈ gS V H L := (St.Phi_eq_one_iff_mem_S _).1 hy
    have hx' : (x : G) = (x : G) * (u : G)⁻¹ * (u : G) := by group
    rw [hx']
    exact mul_mem (Subgroup.mem_sup_left hxu) (Subgroup.mem_sup_right u.2)
  ·
    intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hSU hx)
    have hzeq : z = ⟨(x : G), hxJ⟩ := Subtype.ext hzx
    have hQ : St.Phi ⟨(x : G), hxJ⟩ ∈ Qv (vE (GaloisField 2 n) 0) := by
      rw [← hzeq]
      exact Subgroup.mem_comap.1 hz
    rw [hPhi, mem_Qv_e0] at hQ
    obtain ⟨b, c, hbc⟩ := hQ
    rw [← hbc]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ablk, tq_coe]

theorem piHom_surj_SL (St : L3Setting n V V₁ L T H) (hF : 2 < Nat.card (GaloisField 2 n))
    (M : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
    ∃ x : ↥(lOne L V₁),
      ((piHom St x : Matrix.GeneralLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) = (M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) := by
  have hM : M ∈ commutator SL(2, GaloisField 2 n) := by
    rw [commutator_eq_top_of_two_lt hF]
    exact Subgroup.mem_top M
  obtain ⟨x, hx⟩ := (l1Rep St).blk M hM
  refine ⟨x, ?_⟩
  rw [piHom_coe, hx, ablk_blk]

end GroupOrd

end CFSG.Quasithin.RonanG25
