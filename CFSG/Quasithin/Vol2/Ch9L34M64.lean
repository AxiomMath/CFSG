module

public import Certificates.Certificate7241

public section

namespace CFSG.Quasithin.H13.Ch9.L34M

open CFSG.Fischer Matrix CFSG.Quasithin CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.Mathieu
  CFSG.Monster.Code

theorem std64_vm (m : ℕ) : (MaskCoords.std 64).vm m = toW 64 m := rfl

theorem actsBy_mask64 {s : MulAut (Wn 64)} {f : ℕ → ℕ} (hf : XorLin f)
    (h : ∀ m < 2 ^ 64, s (toW 64 m) = toW 64 (f m)) :
    ActsBy (MaskCoords.std 64) s (matOf 64 f) := by
  intro m hm
  rw [std64_vm, std64_vm, h m hm, actM_matOf hf 64 m hm]

theorem allLt_matOf64 (f : ℕ → ℕ) (hf : ∀ m, f m < 2 ^ 64) : AllLt 64 (matOf 64 f) = true := by
  simp only [AllLt, matOf, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
  exact fun _ _ => hf _

theorem allLt_comp64 {cs ds : List ℕ} (hcs : AllLt 64 cs = true) :
    AllLt 64 (comp cs ds) = true := by
  simp only [AllLt, comp, List.all_map, List.all_eq_true, Function.comp_apply, decide_eq_true_eq]
  exact fun d _ => actM_lt (allLt_spec hcs) d

theorem fldC64_eq : fldC64 = matOf 64 fld64N := by
  simp only [fldC64, matOf, fldN64_eq]

theorem actsBy_fld64 : ActsBy (MaskCoords.std 64) fld64 fldC64 := by
  rw [fldC64_eq]
  exact actsBy_mask64 xorLin_fld64N fun _ hm => fld64_toW hm

theorem actsBy_gr64 : ActsBy (MaskCoords.std 64) gr64 grC64 := by
  rw [grC64, colsN64_eq (rep8_codes8 _)]
  exact actsBy_mask64 (xorLin_actH8 _) fun _ hm => gr64_toW hm

theorem actsBy_one64 : ActsBy (MaskCoords.std 64) 1 idC64 := by
  have h : idC64 = matOf 64 id := rfl
  rw [h]
  exact actsBy_mask64 (fun _ _ => rfl) fun _ _ => rfl

theorem allLt_fldC64 : AllLt 64 fldC64 = true := by
  rw [fldC64_eq]
  exact allLt_matOf64 _ fld64N_lt

theorem allLt_grC64 : AllLt 64 grC64 = true := by
  rw [grC64, colsN64_eq (rep8_codes8 _)]
  exact allLt_matOf64 _ (actH8_lt _)

theorem allLt_idC64 : AllLt 64 idC64 = true := by decide

theorem actsBy_out64 (f t : ℕ) :
    ActsBy (MaskCoords.std 64) (out64 (Multiplicative.ofAdd (((f % 2 : ℕ) : ZMod 2),
      ((t % 2 : ℕ) : ZMod 2)))) (outC64 (f % 2) (t % 2)) ∧
      AllLt 64 (outC64 (f % 2) (t % 2)) = true := by
  rw [out64, c22Hom_apply, toAdd_ofAdd]
  simp only [ite_cast_zero]
  unfold outC64
  rcases Nat.mod_two_eq_zero_or_one f with hf | hf <;>
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht <;>
    simp only [hf, ht, ite_true, ite_false, zero_ne_one, mul_one, one_mul]
  · exact ⟨actsBy_one64, allLt_idC64⟩
  · exact ⟨actsBy_gr64, allLt_grC64⟩
  · exact ⟨actsBy_fld64, allLt_fldC64⟩
  · exact ⟨actsBy_mul actsBy_fld64 actsBy_gr64 allLt_grC64, allLt_comp64 allLt_fldC64⟩

theorem actsBy_rho64GL_cols (g : GL (Fin 3) F4) :
    ActsBy (MaskCoords.std 64) (rho64GL g) (colsN64 (codes8 (adGL g))) ∧
      AllLt 64 (colsN64 (codes8 (adGL g))) = true := by
  rw [colsN64_eq (rep8_codes8 _)]
  exact ⟨actsBy_mask64 (xorLin_actH8 _) fun _ hm => rho64GL_toW g hm,
    allLt_matOf64 _ (actH8_lt _)⟩

theorem getD_range_map {f : ℕ → List ℕ} {N u : ℕ} (hu : u < N) :
    ((List.range N).map f).getD u [] = f u := by
  rw [List.getD_eq_getElem _ _ (by simpa using hu)]
  simp

theorem actsBy_x64 {t : ℕ} (ht : t < 4) :
    (ActsBy (MaskCoords.std 64) (rho64GL (uGL (f4c t) 0 0)) (tabX12_64.getD t []) ∧
      AllLt 64 (tabX12_64.getD t []) = true) ∧
    (ActsBy (MaskCoords.std 64) (rho64GL (uGL 0 (f4c t) 0)) (tabX13_64.getD t []) ∧
      AllLt 64 (tabX13_64.getD t []) = true) ∧
    (ActsBy (MaskCoords.std 64) (rho64GL (uGL 0 0 (f4c t))) (tabX23_64.getD t []) ∧
      AllLt 64 (tabX23_64.getD t []) = true) := by
  have e1 := actsBy_rho64GL_cols (uGL (f4c t) 0 0)
  have e2 := actsBy_rho64GL_cols (uGL 0 (f4c t) 0)
  have e3 := actsBy_rho64GL_cols (uGL 0 0 (f4c t))
  simp only [adGL, coe_uGL, coe_uGL_inv, mul_zero, zero_mul, add_zero, zero_add] at e1 e2 e3
  rw [tabX12_64, tabX13_64, tabX23_64, getD_range_map ht, getD_range_map ht, getD_range_map ht]
  exact ⟨e1, e2, e3⟩

theorem actsBy_uGL64 (p : ℕ) :
    ActsBy (MaskCoords.std 64) (rho64GL (uGL (f4c p) (f4c (p / 4)) (f4c (p / 16))))
      (tabU64.getD (p % 64) []) := by
  have ha := actsBy_x64 (Nat.mod_lt p (show 0 < 4 by norm_num))
  have hb := actsBy_x64 (Nat.mod_lt (p / 4) (show 0 < 4 by norm_num))
  have hc := actsBy_x64 (Nat.mod_lt (p / 16) (show 0 < 4 by norm_num))
  rw [f4c_of_mod (n := p % 4) (x := f4c p) (by unfold f4c; simp only; omega)] at ha
  rw [f4c_of_mod (n := p / 4 % 4) (x := f4c (p / 4)) (by unfold f4c; simp only; omega)] at hb
  rw [f4c_of_mod (n := p / 16 % 4) (x := f4c (p / 16)) (by unfold f4c; simp only; omega)] at hc
  rw [tabU64, getD_range_map (Nat.mod_lt _ (by norm_num)), show p % 64 % 4 = p % 4 by omega,
    show p % 64 / 4 % 4 = p / 4 % 4 by omega, show p % 64 / 16 % 4 = p / 16 % 4 by omega,
    uGL_decomp, map_mul, map_mul]
  exact actsBy_mul hc.2.2.1 (actsBy_mul ha.1.1 hb.2.1.1 hb.2.1.2) (allLt_comp64 ha.1.2)

theorem actsBy_cols64 (p : ℕ) : ActsBy (MaskCoords.std 64) (rho64 (sig p)) (cols64 p) := by
  have h := actsBy_out64 (p / 64) (p / 128)
  rw [rho64_apply]
  exact actsBy_mul (actsBy_uGL64 p) h.1 h.2

theorem allLt_cols64 (p : ℕ) : AllLt 64 (cols64 p) = true := by
  refine allLt_comp64 ?_
  rw [tabU64, getD_range_map (Nat.mod_lt _ (by norm_num))]
  exact allLt_comp64 (actsBy_x64 (Nat.mod_lt _ (by norm_num))).2.2.2

theorem isInvC64_cols64 {p : ℕ} (hsq : rho64 (sig p) * rho64 (sig p) = 1)
    (h1 : rho64 (sig p) ≠ 1) : isInvC64 (cols64 p) = true := by
  simp only [isInvC64, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
  refine ⟨fun i hi => ?_, fun he => h1 ?_⟩
  · have hi' : 2 ^ i < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) hi
    have hlt := actM_lt (allLt_spec (allLt_cols64 p)) (2 ^ i)
    have h := congrArg (fun f : MulAut (Wn 64) => f (toW 64 (2 ^ i))) hsq
    simp only [MulAut.mul_apply, MulAut.one_apply] at h
    have e1 : rho64 (sig p) (toW 64 (2 ^ i)) = toW 64 (actM (cols64 p) (2 ^ i)) :=
      actsBy_cols64 p _ hi'
    have e2 : rho64 (sig p) (toW 64 (actM (cols64 p) (2 ^ i))) =
        toW 64 (actM (cols64 p) (actM (cols64 p) (2 ^ i))) := actsBy_cols64 p _ hlt
    rw [e1, e2] at h
    exact toW_inj (actM_lt (allLt_spec (allLt_cols64 p)) _) hi' h
  · have h := actsBy_cols64 p
    rw [he] at h
    exact actsBy_unique h actsBy_one64

theorem cov64 : ∀ s ∈ Sig.map rho64, s * s = 1 → s ≠ 1 →
    ∃ d ∈ dat64, ActsBy (MaskCoords.std 64) s d.1 := by
  rintro _ ⟨x, hx, rfl⟩ hsq h1
  obtain ⟨p, hp, rfl⟩ := exists_sig hx
  refine ⟨(cols64 p, pickWit 64 3 (cols64 p)), ?_, actsBy_cols64 p⟩
  refine List.mem_map.2 ⟨cols64 p, List.mem_filter.2 ⟨?_, isInvC64_cols64 hsq h1⟩, rfl⟩
  exact List.mem_map.2 ⟨p, List.mem_range.2 hp, rfl⟩

theorem cube64 {B : Subgroup (MulAut (Wn 64))}
    (hB : B ≤ rho64.range) (hB1 : B ≠ ⊥) (hsq : ∀ s ∈ B, s * s = 1)
    (hq : ∀ s ∈ B, ∀ t ∈ B, ∀ v, s (t v * v) = t v * v) :
    Nat.card B ^ 3 * Nat.card (fixV B) ≤ 2 ^ 64 :=
  cube_of_cov1 (MaskCoords.std 64) rho64 sylSig dat64 (by rw [coe_sylSig]; exact cov64)
    Certificates.certificate7241 hB hB1 hsq hq

end CFSG.Quasithin.H13.Ch9.L34M
