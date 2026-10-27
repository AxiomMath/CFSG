module

public import CFSG.Quasithin.EmptyFaithful.ModGData
public import CFSG.Quasithin.EmptyFaithful.ModGWord

public section

namespace CFSG.Quasithin.ModG

open CFSG.Blueprint

@[expose] def cd (x : Mg) : ℕ := pk (x : Equiv.Perm (Fin 22))

theorem cd_mul (x y : Mg) : cd (x * y) = comp (cd x) (cd y) := by
  simp only [cd, Subgroup.coe_mul, pk_mul]

theorem cd_one : cd 1 = kId := by
  simp only [cd, OneMemClass.coe_one, pk_one]

theorem cd_injective : Function.Injective cd := by
  intro x y h
  exact Subtype.ext (pk_injective h)

@[expose] def invAlph (ls : List Mg) : List Mg := ls ++ ls.map (·⁻¹)

theorem invAlph_length (ls : List Mg) : (invAlph ls).length = 2 * ls.length := by
  simp [invAlph]; omega

theorem invAlph_inv (ls : List Mg) :
    ∀ l < ls.length, (invAlph ls).getD (l + ls.length) 1 = ((invAlph ls).getD l 1)⁻¹ := by
  intro l hl
  have h1 : (invAlph ls).getD l 1 = ls.getD l 1 := by
    simp only [invAlph]
    rw [List.getD_append _ _ _ _ hl]
  have h2 : (invAlph ls).getD (l + ls.length) 1 = (ls.map (·⁻¹)).getD l 1 := by
    simp only [invAlph]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega
  rw [h1, h2]
  have := List.getD_map ls 1 (n := l) (fun x : Mg => x⁻¹)
  simpa using this

theorem map_cd_ev (A : List Mg) (ws : List (List ℕ)) :
    (ws.map (ev A)).map cd = ws.map (evc (A.map cd)) :=
  map_c_ev cd cd_mul cd_one A ws

theorem map_cd_inv_ev {A : List Mg} {r : ℕ} (hA : ∀ l < r, A.getD (l + r) 1 = (A.getD l 1)⁻¹)
    (ws : List (List ℕ)) (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 2 * r) :
    (ws.map fun w => (ev A w)⁻¹).map cd = ws.map (fun w => evc (A.map cd) (invW r w)) :=
  map_c_inv_ev cd cd_mul cd_one hA ws hw

@[expose] def Lks8 : List Mg := invAlph (ksWd.map (ev Lab))

@[expose] def Ls : List Mg := invAlph (sWd.map (ev Lks8))

theorem Lab_cd : Lab.map cd = LabK := by decide +kernel

theorem Lab_inv : ∀ l < 2, Lab.getD (l + 2) 1 = (Lab.getD l 1)⁻¹ :=
  invAlph_inv [CFSG.Sporadic.Mathieu.m22a, CFSG.Sporadic.Mathieu.m22b]

theorem invAlph_ev_cd {A : List Mg} {r : ℕ} (hA : ∀ l < r, A.getD (l + r) 1 = (A.getD l 1)⁻¹)
    (ws : List (List ℕ)) (hw : ∀ w ∈ ws, ∀ l ∈ w, l < 2 * r) :
    (invAlph (ws.map (ev A))).map cd =
      ws.map (evc (A.map cd)) ++ ws.map (fun w => evc (A.map cd) (invW r w)) := by
  have h1 : (ws.map (ev A)).map (fun x : Mg => x⁻¹) = ws.map (fun w => (ev A w)⁻¹) := by
    rw [List.map_map]
    rfl
  simp only [invAlph]
  rw [List.map_append, h1, map_cd_ev, map_cd_inv_ev hA ws hw]

theorem ksWd_len : ksWd.length = 4 := by decide +kernel
theorem ksWd_lt : ∀ w ∈ ksWd, ∀ l ∈ w, l < 2 * 2 := by decide +kernel
theorem sWd_len : sWd.length = 3 := by decide +kernel
theorem sWd_lt : ∀ w ∈ sWd, ∀ l ∈ w, l < 2 * 4 := by decide +kernel

theorem Lks8_inv : ∀ l < 4, Lks8.getD (l + 4) 1 = (Lks8.getD l 1)⁻¹ := by
  have h := invAlph_inv (ksWd.map (ev Lab))
  rw [List.length_map, ksWd_len] at h
  exact h

theorem Lks8_cd : Lks8.map cd = Lks8K := by
  have h := invAlph_ev_cd (A := Lab) (r := 2) Lab_inv ksWd ksWd_lt
  rw [Lab_cd] at h
  show (invAlph (ksWd.map (ev Lab))).map cd = Lks8K
  rw [h]
  decide +kernel

theorem Ls_inv : ∀ l < 3, Ls.getD (l + 3) 1 = (Ls.getD l 1)⁻¹ := by
  have h := invAlph_inv (sWd.map (ev Lks8))
  rw [List.length_map, sWd_len] at h
  exact h

theorem Ls_cd : Ls.map cd = LsK := by
  have h := invAlph_ev_cd (A := Lks8) (r := 4) Lks8_inv sWd sWd_lt
  rw [Lks8_cd] at h
  show (invAlph (sWd.map (ev Lks8))).map cd = LsK
  rw [h]
  decide +kernel

@[expose] def SEl : List Mg := SWd.map (ev Ls)

theorem SEl_cd : SEl.map cd = SK := by
  rw [SEl, map_cd_ev, Ls_cd]
  decide +kernel

@[expose] def zEl : List Mg := zWd.map (ev Lab)

theorem zEl_cd : zEl.map cd = zK := by
  rw [zEl, map_cd_ev, Lab_cd]
  decide +kernel

theorem zWd_lt : ∀ w ∈ zWd, ∀ l ∈ w, l < 2 * 2 := by decide +kernel

theorem zinv_cd : (zWd.map fun w => (ev Lab w)⁻¹).map cd = zinvK := by
  rw [map_cd_inv_ev Lab_inv zWd zWd_lt, Lab_cd]
  decide +kernel

@[expose] def dEl : List Mg := dWd.map (ev Lks8)

theorem dEl_cd : dEl.map cd = dK := by
  rw [dEl, map_cd_ev, Lks8_cd]
  decide +kernel

theorem dWd_lt : ∀ w ∈ dWd, ∀ l ∈ w, l < 2 * 4 := by decide +kernel

theorem dinv_cd : (dWd.map fun w => (ev Lks8 w)⁻¹).map cd = dinvK := by
  rw [map_cd_inv_ev Lks8_inv dWd dWd_lt, Lks8_cd]
  decide +kernel

end CFSG.Quasithin.ModG
