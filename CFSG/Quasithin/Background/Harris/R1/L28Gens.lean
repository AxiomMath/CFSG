module

public import CFSG.Quasithin.Recognition.CertF8
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Quasithin.Background.Harris.R1.D4VertWords

public section

namespace CFSG.Quasithin.Background.Harris.R1.L28Gens

open CFSG.Quasithin

@[expose] def gA : Matrix.SpecialLinearGroup (Fin 2) GF8 :=
  ⟨!![GF8.ofNat' 0, GF8.ofNat' 1; GF8.ofNat' 1, GF8.ofNat' 0], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def gB : Matrix.SpecialLinearGroup (Fin 2) GF8 :=
  ⟨!![GF8.ofNat' 0, GF8.ofNat' 2; GF8.ofNat' 5, GF8.ofNat' 1], by
    rw [Matrix.det_fin_two_of]; decide⟩

@[expose] def H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) GF8) := Subgroup.closure {gA, gB}

@[expose] def ev (w : List Bool) : Matrix.SpecialLinearGroup (Fin 2) GF8 :=
  (w.map fun b => if b then gB else gA).prod

theorem ev_mem (w : List Bool) : ev w ∈ H := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hx
  cases b
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

theorem mem_of_eq {g : Matrix.SpecialLinearGroup (Fin 2) GF8} {w : List Bool} (h : ev w = g) :
    g ∈ H :=
  h ▸ ev_mem w

theorem gf8_cases : ∀ a : GF8, a = GF8.ofNat' 0 ∨ a = GF8.ofNat' 1 ∨ a = GF8.ofNat' 2 ∨
    a = GF8.ofNat' 3 ∨ a = GF8.ofNat' 4 ∨ a = GF8.ofNat' 5 ∨ a = GF8.ofNat' 6 ∨ a = GF8.ofNat' 7 := by
  decide

theorem rels_SL : ∀ r ∈ CFSG.Quasithin.Background.Harris.R1.D4Vert.l28Rels,
    (r.map fun p => if p.2 then ![gA, gB] p.1 else (![gA, gB] p.1)⁻¹).prod = 1 := by
  decide +kernel

theorem tv01_mem (a : GF8) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) a ∈ H := by
  rcases gf8_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 0)) (w := []) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 1)) (w := [false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 2)) (w := [true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 3)) (w := [true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 4)) (w := [false, true, true, false, true, false, true, true, false, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 5)) (w := [true, true, false, true, false, true, false, true, true, false, true, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 6)) (w := [true, false, true, false, true, true, false, true, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 7)) (w := [false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true, false]) (by decide +kernel)

theorem tv10_mem (a : GF8) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) a ∈ H := by
  rcases gf8_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 0)) (w := []) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 1)) (w := [true, false, true, true, false, true, false, true, true, false, true, false, true, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 2)) (w := [false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 3)) (w := [false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 4)) (w := [true, true, false, true, false, true, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 5)) (w := [false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 6)) (w := [false, true, false, true, false, true, true, false, true, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 7)) (w := [true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) (by decide +kernel)

theorem dg01_mem (c : GF8) (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) c hc ∈ H := by
  rcases gf8_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by decide : GF8.ofNat' 0 = 0) hc
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 1) (by decide)) (w := []) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 2) (by decide)) (w := [true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 3) (by decide)) (w := [true, false, true, false, true, true, false, true, false, true, true, false, true, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 4) (by decide)) (w := [true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 5) (by decide)) (w := [true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 6) (by decide)) (w := [false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (0 : Fin 2) ≠ 1) (GF8.ofNat' 7) (by decide)) (w := [true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false]) (by decide +kernel)

theorem dg10_mem (c : GF8) (hc : c ≠ 0) :
    Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) c hc ∈ H := by
  rcases gf8_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (by decide : GF8.ofNat' 0 = 0) hc
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 1) (by decide)) (w := []) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 2) (by decide)) (w := [true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 3) (by decide)) (w := [false, true, false, true, false, true, true, false, true, false, true, true, false, true, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 4) (by decide)) (w := [true, false, true, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 5) (by decide)) (w := [true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 6) (by decide)) (w := [true, false, true, false, true, true, false, true, false, true, true, false, true, true, false]) (by decide +kernel)
  · exact mem_of_eq (g := Matrix.SpecialLinearGroup.diag2n (by decide : (1 : Fin 2) ≠ 0) (GF8.ofNat' 7) (by decide)) (w := [true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, true]) (by decide +kernel)

theorem gen_SL (g : Matrix.SpecialLinearGroup (Fin 2) GF8) : g ∈ H := by
  refine Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ H) g ?_ ?_ ?_
  · intro i j hij c hc
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact dg01_mem c hc
    · exact dg10_mem c hc
    · exact absurd rfl hij
  · intro i j hij a
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact tv01_mem a
    · exact tv10_mem a
    · exact absurd rfl hij
  · intro A B hA hB
    exact H.mul_mem hA hB

end CFSG.Quasithin.Background.Harris.R1.L28Gens

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.Background.Harris.R1.L28Gens

theorem card_GF8 : Nat.card GF8 = 2 ^ 3 := by
  rw [Nat.card_eq_fintype_card]
  rfl

@[expose] noncomputable def fieldIso : GF8 ≃+* GaloisField 2 3 :=
  CFSG.ClassicalModels.finiteFieldEquivGaloisField GF8 2 3 (by norm_num) card_GF8

@[expose] noncomputable def psiIso : Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF8 ≃*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
  CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv fieldIso (Fin 2)

@[expose] noncomputable def phi : Matrix.SpecialLinearGroup (Fin 2) GF8 →*
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3) :=
  psiIso.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) GF8)))

theorem phi_apply (g : Matrix.SpecialLinearGroup (Fin 2) GF8) :
    phi g = psiIso (QuotientGroup.mk g) := rfl

theorem phi_surj : Function.Surjective phi := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (psiIso.symm x)
  exact ⟨g, by rw [phi_apply, hg, MulEquiv.apply_symm_apply]⟩

theorem phi_vec (p : Fin 2 × Bool) :
    phi (if p.2 then ![gA, gB] p.1 else (![gA, gB] p.1)⁻¹) =
      if p.2 then ![phi gA, phi gB] p.1 else (![phi gA, phi gB] p.1)⁻¹ := by
  obtain ⟨i, b⟩ := p
  cases b <;> fin_cases i <;> simp [map_inv]

theorem rels_phi : ∀ r ∈ D4Vert.l28Rels,
    (r.map fun p => if p.2 then ![phi gA, phi gB] p.1 else (![phi gA, phi gB] p.1)⁻¹).prod = 1 := by
  intro r hr
  have h2 : r.map (fun p => if p.2 then ![phi gA, phi gB] p.1 else (![phi gA, phi gB] p.1)⁻¹) =
      (r.map fun p => if p.2 then ![gA, gB] p.1 else (![gA, gB] p.1)⁻¹).map phi := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => (phi_vec p).symm
  rw [h2, ← map_list_prod, rels_SL r hr, map_one]

theorem closure_top : Subgroup.closure {phi gA, phi gB} = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨g, rfl⟩ := phi_surj x
  have hg : phi g ∈ Subgroup.map phi (Subgroup.closure {gA, gB}) :=
    Subgroup.mem_map_of_mem phi (gen_SL g)
  rw [MonoidHom.map_closure, Set.image_pair] at hg
  exact hg

end CFSG.Quasithin.Background.Harris.R1
