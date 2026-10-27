module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenJParts
public import CFSG.Certificates.Kernel.BabyMonster.B7J.All
public import Certificates.Kernel.BabyMonster.B7EParts
public import Certificates.Kernel.BabyMonster.SevenLocal
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Check0
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Check1
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Check2
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Check3
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Check4
public import CFSG.Certificates.Kernel.BabyMonster.B7J.Wf
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CertificateChecks.KernelBM.B7JParts

open CFSG.Monster.B CFSG.Blueprint CFSG.KC.BM CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Native CFSG.Sporadic.Bridge
  CFSG.Sporadic.Bridge.TwoGen CFSG.LieType.Multipliers CertificateChecks.KernelBM.SevenGen
  CertificateChecks.KernelBM.SevenFacts

set_option maxRecDepth 100000

section Monoid

variable {M : Type*} [Monoid M]

theorem pow7_of {c c2 c4 X : M} (h2 : c * c = c2) (h4 : c2 * c2 = c4) (h : c4 * c2 * c = X) :
    c ^ 7 = X := by
  rw [← h, ← h4, ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow4_of {d d2 X : M} (h2 : d * d = d2) (h : d2 * d2 = X) : d ^ 4 = X := by
  rw [← h, ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow3_of {f f2 X : M} (h2 : f * f = f2) (h : f2 * f = X) : f ^ 3 = X := by
  rw [← h, ← h2]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

end Monoid

theorem wordProd_rep {G : Type*} [Group G] (x : ℕ → G) (w : List (ℕ × Bool)) :
    ∀ k : ℕ, wordProd x (List.replicate k w).flatten = wordProd x w ^ k
  | 0 => by simp [wordProd]
  | k + 1 => by
    rw [List.replicate_succ, List.flatten_cons, pow_succ', ← wordProd_rep x w k]
    simp [wordProd, List.map_append, List.prod_append]

theorem rels_eq : L34.rels.map (List.map fun l => ((l.1 : ℕ), l.2)) =
    [(List.replicate 2 [(0, true)]).flatten, (List.replicate 5 [(1, true)]).flatten,
      (List.replicate 7 [(0, true), (1, true)]).flatten,
      (List.replicate 4 [(0, true), (1, true), (0, true), (1, false)]).flatten,
      (List.replicate 3 [(0, true), (1, true), (1, true), (0, false), (1, false), (1, false)]).flatten,
      (List.replicate 7 [(0, true), (1, true), (1, true)]).flatten,
      (List.replicate 7
        [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false)]).flatten] := by
  decide +kernel

theorem eWord_eq : b7JEWord () = [(0, true), (1, true), (1, true), (0, true), (1, false),
    (0, true), (1, true), (0, true), (1, false), (1, false), (0, true), (1, false), (0, true),
    (1, true), (1, true)] := by
  decide +kernel

theorem parts_of {M : Type*} [Monoid M] (f : NativeSporadic.B →* M) (hf : Function.Injective f)
    {a e y : NativeSporadic.B} {A E Y Y2 Y3 Y4 E2 U Bm Ey Ey2 Ey4 C1 C2 C4 D D2 F F2 Gg G2 G4 H H2 H4 : M}
    (ha2 : a * a = 1) (hy5 : y ^ 5 = 1) (he3 : e ^ 3 = 1)
    (fa : f a = A) (fe : f e = E) (fy : f y = Y)
    (hY2 : Y2 = Y ^ 2) (hY3 : Y3 = Y ^ 3) (hY4 : Y4 = Y ^ 4) (hE2 : E2 = E ^ 2)
    (k_ey : E * Y = Ey) (k_ey2 : Ey * Ey = Ey2) (k_ey4 : Ey2 * Ey2 = Ey4)
    (k_ord : Ey4 * Ey2 * Ey = A)
    (k_b : Y4 * E * Y4 * E2 = Bm) (k_u : Bm * Bm = U) (k_inv : U * U = 1)
    (k_c1 : U * Y3 = C1) (k_c2 : C1 * C1 = C2) (k_c4 : C2 * C2 = C4) (k_rc : C4 * C2 * C1 = A)
    (k_d : U * Y3 * U * Y2 = D) (k_d2 : D * D = D2) (k_rd : D2 * D2 = 1)
    (k_f : U * Y * U * Y4 = F) (k_f2 : F * F = F2) (k_rf : F2 * F = 1)
    (k_g : U * Y = Gg) (k_g2 : Gg * Gg = G2) (k_g4 : G2 * G2 = G4) (k_rg : G4 * G2 * Gg = A)
    (k_h : U * Y3 * U * Y * U * Y2 = H) (k_h2 : H * H = H2) (k_h4 : H2 * H2 = H4)
    (k_rh : H4 * H2 * H = 1)
    (k_ew : U * Y * U * Y2 * U * Y3 * U * Y4 * U * Y2 * U * Y = E)
    (k_ne1 : U ≠ 1) (k_neA : U ≠ A) :
    B7JParts a e y (wordProd (img2 y e) (b7JUWord ())) (y ^ 3) := by
  have hyi : y⁻¹ = y ^ 4 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hy5)
  have hei : e⁻¹ = e ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact he3)
  have hvi : (y ^ 3)⁻¹ = y ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_add]; exact hy5)
  have h33 : ∀ X : NativeSporadic.B, y ^ 3 * (y ^ 3 * X) = y * X := by
    intro X
    rw [← mul_assoc, ← pow_add, (by norm_num : 3 + 3 = 5 + 1), pow_succ, hy5, one_mul]
  have h33' : y ^ 3 * y ^ 3 = y := by
    rw [← pow_add, (by norm_num : 3 + 3 = 5 + 1), pow_succ, hy5, one_mul]
  have h22 : ∀ X : NativeSporadic.B, y ^ 2 * (y ^ 2 * X) = y ^ 4 * X := by
    intro X
    rw [← mul_assoc, ← pow_add]
  have h22' : y ^ 2 * y ^ 2 = y ^ 4 := by rw [← pow_add]
  set u := wordProd (img2 y e) (b7JUWord ()) with hu_def
  have hw : u = y ^ 4 * e * y ^ 4 * e ^ 2 * (y ^ 4 * e * y ^ 4 * e ^ 2) := by
    simp [hu_def, wordProd, b7JUWord, img2, hyi, hei, mul_assoc]
  have hU : f u = U := by
    rw [hw]
    simp only [map_mul, map_pow, fy, fe]
    rw [← hY4, ← hE2, k_b, k_u]
  have hu2 : u * u = 1 := hf (by rw [map_mul, hU, map_one]; exact k_inv)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have r3 : (u * y ^ 3) ^ 7 = a := hf (by
    simp only [map_pow, map_mul, hU, fy, fa]
    rw [← hY3, k_c1]
    exact pow7_of k_c2 k_c4 k_rc)
  have r4 : (u * y ^ 3 * u * y ^ 2) ^ 4 = 1 := hf (by
    simp only [map_pow, map_mul, map_one, hU, fy]
    rw [← hY3, ← hY2, k_d]
    exact pow4_of k_d2 k_rd)
  have r5 : (u * y * u * y ^ 4) ^ 3 = 1 := hf (by
    simp only [map_pow, map_mul, map_one, hU, fy]
    rw [← hY4, k_f]
    exact pow3_of k_f2 k_rf)
  have r6 : (u * y) ^ 7 = a := hf (by
    simp only [map_pow, map_mul, hU, fy, fa]
    rw [k_g]
    exact pow7_of k_g2 k_g4 k_rg)
  have r7 : (u * y ^ 3 * u * y * u * y ^ 2) ^ 7 = 1 := hf (by
    simp only [map_pow, map_mul, map_one, hU, fy]
    rw [← hY3, ← hY2, k_h]
    exact pow7_of k_h2 k_h4 k_rh)
  have r2 : (y ^ 3) ^ 5 = 1 := by
    rw [← pow_mul, (by norm_num : 3 * 5 = 5 * 3), pow_mul, hy5, one_pow]
  refine
    { a_sq := ha2
      y_pow := hy5
      e_pow := he3
      seven := hf (by rw [map_pow, map_mul, fe, fy, k_ey, fa]; exact pow7_of k_ey2 k_ey4 k_ord)
      u_sq := hu2
      rels_mem := ?_
      u_ne_one := fun h => k_ne1 (by rw [← hU, h, map_one])
      u_ne_a := fun h => k_neA (by rw [← hU, ← fa, h])
      e_word := ?_ }
  · intro w hw'
    rw [rels_eq] at hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [wordProd_rep]
    · have hb : wordProd (img2 u (y ^ 3)) [(0, true)] = u := by simp [wordProd, img2]
      rw [hb, sq, hu2]
      exact Subgroup.one_mem _
    · have hb : wordProd (img2 u (y ^ 3)) [(1, true)] = y ^ 3 := by simp [wordProd, img2]
      rw [hb, r2]
      exact Subgroup.one_mem _
    · have hb : wordProd (img2 u (y ^ 3)) [(0, true), (1, true)] = u * y ^ 3 := by
        simp [wordProd, img2]
      rw [hb, r3]
      exact Subgroup.mem_zpowers a
    · have hb : wordProd (img2 u (y ^ 3)) [(0, true), (1, true), (0, true), (1, false)] =
          u * y ^ 3 * u * y ^ 2 := by
        simp [wordProd, img2, hvi, mul_assoc, -inv_pow]
      rw [hb, r4]
      exact Subgroup.one_mem _
    · have hb : wordProd (img2 u (y ^ 3))
          [(0, true), (1, true), (1, true), (0, false), (1, false), (1, false)] =
          u * y * u * y ^ 4 := by
        simp [wordProd, img2, hvi, hui, mul_assoc, h33, h22', -inv_pow]
      rw [hb, r5]
      exact Subgroup.one_mem _
    · have hb : wordProd (img2 u (y ^ 3)) [(0, true), (1, true), (1, true)] = u * y := by
        simp [wordProd, img2, h33']
      rw [hb, r6]
      exact Subgroup.mem_zpowers a
    · have hb : wordProd (img2 u (y ^ 3))
          [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, false)] =
          u * y ^ 3 * u * y * u * y ^ 2 := by
        simp [wordProd, img2, hvi, mul_assoc, h33, -inv_pow]
      rw [hb, r7]
      exact Subgroup.one_mem _
  · have hT : wordProd (img2 u (y ^ 3)) (b7JEWord ()) =
        u * y * u * y ^ 2 * u * y ^ 3 * u * y ^ 4 * u * y ^ 2 * u * y := by
      rw [eWord_eq]
      simp [wordProd, img2, hvi, mul_assoc, h33, h33', h22, -inv_pow]
    refine hf ?_
    rw [hT]
    simp only [map_mul, map_pow, hU, fy, fe]
    rw [← hY2, ← hY3, ← hY4]
    exact k_ew

theorem b7JParts : B7JParts a0B7 eB7 yB7 uB7 vB7 := by
  have P := KernelBM.B7EParts.b7EParts
  obtain ⟨h0, -, h2, -, -, h5⟩ := KernelBM.B7EParts.b7E_bMat
  have hy5 : yB7 ^ 5 = 1 := by rw [← P.order_y]; exact pow_orderOf_eq_one _
  have he3 : eB7 ^ 3 = 1 := by rw [← P.order_e]; exact pow_orderOf_eq_one _
  have k_h : stripMat B7J.u * stripMat Seven.y3 * stripMat B7J.u * stripMat Seven.y *
      stripMat B7J.u * stripMat Seven.y2 = stripMat B7J.h := by
    have e := stripMat_mul_of_allStrips (C := B7J.h)
      (Ws := [Seven.y3, B7J.u, Seven.y, B7J.u, Seven.y2])
      (by simp [Seven.wf_y3, B7J.wf_u, Seven.wf_y, Seven.wf_y2]) B7J.wf_u
      (by bm_strips4 CFSG.KC.BM.B7J.c_h 69)
    simpa using e
  have k_rh : stripMat B7J.h4 * stripMat B7J.h2 * stripMat B7J.h = 1 := by
    have e := stripMat_mul_eq_one (Ws := [B7J.h2, B7J.h]) (by simp [B7J.wf_h2, B7J.wf_h])
      B7J.wf_h4 (by bm_strips4 CFSG.KC.BM.B7J.rel_h 69)
    simpa using e
  have k_ew : stripMat B7J.u * stripMat Seven.y * stripMat B7J.u * stripMat Seven.y2 *
      stripMat B7J.u * stripMat Seven.y3 * stripMat B7J.u * stripMat Seven.y4 * stripMat B7J.u *
      stripMat Seven.y2 * stripMat B7J.u * stripMat Seven.y = stripMat Seven.e3 := by
    have e := stripMat_mul_of_allStrips (C := Seven.e3)
      (Ws := [Seven.y, B7J.u, Seven.y2, B7J.u, Seven.y3, B7J.u, Seven.y4, B7J.u, Seven.y2, B7J.u,
        Seven.y])
      (by simp [Seven.wf_y, B7J.wf_u, Seven.wf_y2, Seven.wf_y3, Seven.wf_y4]) B7J.wf_u
      (by bm_strips4 CFSG.KC.BM.B7J.e_word 69)
    simpa using e
  exact parts_of bMat bMat_injective P.mul_self_a hy5 he3 h0 h5 h2 y2_eq y3_eq y4_eq e2_eq
    (p1 B7J.ey Seven.wf_e3 Seven.wf_y (by bm_strips4 CFSG.KC.BM.B7J.c_ey 69))
    (p1 B7J.ey2 B7J.wf_ey B7J.wf_ey (by bm_strips4 CFSG.KC.BM.B7J.c_ey2 69))
    (p1 B7J.ey4 B7J.wf_ey2 B7J.wf_ey2 (by bm_strips4 CFSG.KC.BM.B7J.c_ey4 69))
    (p2 Seven.al B7J.wf_ey4 B7J.wf_ey2 B7J.wf_ey (by bm_strips4 CFSG.KC.BM.B7J.ord_ey 69))
    (p3 B7J.b Seven.wf_y4 Seven.wf_e3 Seven.wf_y4 SevenElem.wf_e2
      (by bm_strips4 CFSG.KC.BM.B7J.c_b 69))
    (p1 B7J.u B7J.wf_b B7J.wf_b (by bm_strips4 CFSG.KC.BM.B7J.c_u 69))
    (p1one B7J.wf_u B7J.wf_u (by bm_strips4 CFSG.KC.BM.B7J.inv_u 69))
    (p1 B7J.c1 B7J.wf_u Seven.wf_y3 (by bm_strips4 CFSG.KC.BM.B7J.c_c1 69))
    (p1 B7J.c2 B7J.wf_c1 B7J.wf_c1 (by bm_strips4 CFSG.KC.BM.B7J.c_c2 69))
    (p1 B7J.c4 B7J.wf_c2 B7J.wf_c2 (by bm_strips4 CFSG.KC.BM.B7J.c_c4 69))
    (p2 Seven.al B7J.wf_c4 B7J.wf_c2 B7J.wf_c1 (by bm_strips4 CFSG.KC.BM.B7J.rel_c 69))
    (p3 B7J.d B7J.wf_u Seven.wf_y3 B7J.wf_u Seven.wf_y2 (by bm_strips4 CFSG.KC.BM.B7J.c_d 69))
    (p1 B7J.d2 B7J.wf_d B7J.wf_d (by bm_strips4 CFSG.KC.BM.B7J.c_d2 69))
    (p1one B7J.wf_d2 B7J.wf_d2 (by bm_strips4 CFSG.KC.BM.B7J.rel_d 69))
    (p3 B7J.f B7J.wf_u Seven.wf_y B7J.wf_u Seven.wf_y4 (by bm_strips4 CFSG.KC.BM.B7J.c_f 69))
    (p1 B7J.f2 B7J.wf_f B7J.wf_f (by bm_strips4 CFSG.KC.BM.B7J.c_f2 69))
    (p1one B7J.wf_f2 B7J.wf_f (by bm_strips4 CFSG.KC.BM.B7J.rel_f 69))
    (p1 B7J.g B7J.wf_u Seven.wf_y (by bm_strips4 CFSG.KC.BM.B7J.c_g 69))
    (p1 B7J.g2 B7J.wf_g B7J.wf_g (by bm_strips4 CFSG.KC.BM.B7J.c_g2 69))
    (p1 B7J.g4 B7J.wf_g2 B7J.wf_g2 (by bm_strips4 CFSG.KC.BM.B7J.c_g4 69))
    (p2 Seven.al B7J.wf_g4 B7J.wf_g2 B7J.wf_g (by bm_strips4 CFSG.KC.BM.B7J.rel_g 69))
    k_h (p1 B7J.h2 B7J.wf_h B7J.wf_h (by bm_strips4 CFSG.KC.BM.B7J.c_h2 69))
    (p1 B7J.h4 B7J.wf_h2 B7J.wf_h2 (by bm_strips4 CFSG.KC.BM.B7J.c_h4 69)) k_rh k_ew
    (notId_sound B7J.wf_u B7J.ne_u) (eqMat_sound B7J.wf_u Seven.wf_al B7J.ne_u_al)

end CertificateChecks.KernelBM.B7JParts

end
