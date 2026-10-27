module

public import CFSG.Quasithin.Vol2.KGFactC31LieSylRoot
public import CFSG.Quasithin.Vol2.KGFactC31LieSylTorus

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint

theorem c1_check_G2 :
    ∀ b ∈ Certificates.Data.LieSylRootWt.Ty.G2.roots,
      ∀ c ∈ Certificates.Data.LieSylRootWt.Ty.G2.roots,
        (∀ i < 2, (b.getD i 0 - c.getD i 0) % 11 = 0) → b = c := by
  decide +kernel

theorem c1_check_D4 :
    ∀ b ∈ Certificates.Data.LieSylRootWt.Ty.D4.roots,
      ∀ c ∈ Certificates.Data.LieSylRootWt.Ty.D4.roots,
        (∀ i < 4, (b.getD i 0 - c.getD i 0) % 11 = 0) → b = c := by
  decide +kernel

theorem c1_check_F4 :
    ∀ b ∈ Certificates.Data.LieSylRootWt.Ty.F4.roots,
      ∀ c ∈ Certificates.Data.LieSylRootWt.Ty.F4.roots,
        (∀ i < 4, (b.getD i 0 - c.getD i 0) % 11 = 0) → b = c := by
  decide +kernel

theorem nz_check_G2 : ∀ b ∈ Certificates.Data.LieSylRootWt.Ty.G2.roots,
    ∃ i < 2, b.getD i 0 % 11 ≠ 0 := by
  decide +kernel

theorem nz_check_D4 : ∀ b ∈ Certificates.Data.LieSylRootWt.Ty.D4.roots,
    ∃ i < 4, b.getD i 0 % 11 ≠ 0 := by
  decide +kernel

theorem nz_check_F4 : ∀ b ∈ Certificates.Data.LieSylRootWt.Ty.F4.roots,
    ∃ i < 4, b.getD i 0 % 11 ≠ 0 := by
  decide +kernel

theorem getD_ofFn_eq {n : ℕ} (f : Fin n → ℤ) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i 0 = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]

theorem eq_of_congr_mem {n : ℕ} (L : List (List ℤ))
    (hc : ∀ b ∈ L, ∀ c ∈ L, (∀ i < n, (b.getD i 0 - c.getD i 0) % 11 = 0) → b = c)
    {β γ : Fin n → ℤ} (hβ : List.ofFn β ∈ L) (hγ : List.ofFn γ ∈ L)
    (h : ∀ i : Fin n, (β i - γ i) % 11 = 0) : β = γ := by
  have key := hc _ hβ _ hγ (fun i hi => by
    rw [getD_ofFn_eq β i hi, getD_ofFn_eq γ i hi]
    exact h ⟨i, hi⟩)
  exact List.ofFn_injective key

theorem wt_eq_imp_eq {τ : Tag} (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {β γ : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) (hγ : IsRoot τ γ) (h : wt τ 11 β = wt τ 11 γ) : β = γ := by
  have hA : IsUnit ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).det) := isUnit_det_cartan_map11 τ
  have h' : Matrix.mulVec (τ.cartan.map (Int.cast : ℤ → ZMod 11))
      (fun j => ((β j : ℤ) : ZMod 11)) =
      Matrix.mulVec (τ.cartan.map (Int.cast : ℤ → ZMod 11))
        (fun j => ((γ j : ℤ) : ZMod 11)) := h
  have hc := mulVec_cancel _ hA h'
  have hcong : ∀ i : Fin τ.rank, (β i - γ i) % 11 = 0 := fun i => by
    have h2 := congrFun hc i
    have h3 := (ZMod.intCast_eq_intCast_iff' (β i) (γ i) 11).1 h2
    omega
  rcases hτ with rfl | rfl | rfl
  · exact eq_of_congr_mem _ c1_check_G2
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.G2.roots) rootCert_check_G2
        rfl β).1 hβ)
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.G2.roots) rootCert_check_G2
        rfl γ).1 hγ) hcong
  · exact eq_of_congr_mem _ c1_check_D4
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.D4.roots) rootCert_check_D4
        rfl β).1 hβ)
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.D4.roots) rootCert_check_D4
        rfl γ).1 hγ) hcong
  · exact eq_of_congr_mem _ c1_check_F4
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.F4.roots) rootCert_check_F4
        rfl β).1 hβ)
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.F4.roots) rootCert_check_F4
        rfl γ).1 hγ) hcong

theorem wt_ne_zero {τ : Tag} (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {β : Fin τ.rank → ℤ}
    (hβ : IsRoot τ β) : wt τ 11 β ≠ 0 := by
  intro h
  have hA : IsUnit ((τ.cartan.map (Int.cast : ℤ → ZMod 11)).det) := isUnit_det_cartan_map11 τ
  have h' : Matrix.mulVec (τ.cartan.map (Int.cast : ℤ → ZMod 11))
      (fun j => ((β j : ℤ) : ZMod 11)) =
      Matrix.mulVec (τ.cartan.map (Int.cast : ℤ → ZMod 11)) (0 : Fin τ.rank → ZMod 11) := by
    rw [Matrix.mulVec_zero]
    exact h
  have hc := mulVec_cancel _ hA h'
  have hzero : ∀ i : Fin τ.rank, (β i) % 11 = 0 := fun i => by
    have h2 := congrFun hc i
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd (β i) 11).1 h2
    omega
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨i, hi, hne⟩ := nz_check_G2 _
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.G2.roots) rootCert_check_G2
        rfl β).1 hβ)
    exact hne (by rw [getD_ofFn_eq β i hi]; exact hzero ⟨i, hi⟩)
  · obtain ⟨i, hi, hne⟩ := nz_check_D4 _
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.D4.roots) rootCert_check_D4
        rfl β).1 hβ)
    exact hne (by rw [getD_ofFn_eq β i hi]; exact hzero ⟨i, hi⟩)
  · obtain ⟨i, hi, hne⟩ := nz_check_F4 _
      ((isRoot_iff_mem_of_check (Certificates.Data.LieSylRootWt.Ty.F4.roots) rootCert_check_F4
        rfl β).1 hβ)
    exact hne (by rw [getD_ofFn_eq β i hi]; exact hzero ⟨i, hi⟩)

end CFSG.Quasithin.KGC31
