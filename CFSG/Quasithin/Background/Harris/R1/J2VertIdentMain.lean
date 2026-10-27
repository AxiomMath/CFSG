module

public import CFSG.Quasithin.Background.Harris.R1.J2VertIdent
public import CFSG.Quasithin.Background.Harris.R1.J2VertWords

public section

namespace CFSG.Quasithin.Background.Harris.R1.J2Vert

open CFSG.Quasithin CFSG.Quasithin.J2Cz CFSG.Quasithin.J2Cz.F2 CFSG.Quasithin.J2Cz.QM Equiv
  CFSG.CosetTable

namespace VertGens

variable {H : Type} [Group H] {g : VertGens H}

theorem chi_x0 : g.chi (x 0) = g.y 0 * g.y 1 * g.y 2 * g.y 3 := by
  show liftT g.z g.y ⟨o, i, i, i, i⟩ 1 = _
  simp [liftT, mul_assoc]

variable (hχ : Function.Injective g.chi) [g.Q.Normal]
  (hC : ∀ h : H, (∀ q ∈ g.Q, h * q = q * h) → h = 1 ∨ h = g.z)

include hC in
theorem eq_of_kappa_eq_one {h : H} (hk : kappa hχ h = 1) : h = 1 ∨ h = g.z :=
  hC h (kappa_eq_one hχ hk)

include hC in
theorem kappa_injOn_L (hLQ : g.L ⊓ g.Q = ⊥) {l m : H} (hl : l ∈ g.L) (hm : m ∈ g.L)
    (h : kappa hχ l = kappa hχ m) : l = m := by
  have h1 : kappa hχ (l⁻¹ * m) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 : l⁻¹ * m ∈ g.L ⊓ g.Q := by
    refine ⟨g.L.mul_mem (g.L.inv_mem hl) hm, ?_⟩
    rcases eq_of_kappa_eq_one hχ hC h1 with h3 | h3
    · rw [h3]; exact one_mem _
    · rw [h3]; exact g.z_mem_Q
  rw [hLQ, Subgroup.mem_bot] at h2
  calc l = l * (l⁻¹ * m) := by rw [h2, mul_one]
    _ = m := by group

include hC in
theorem exists_kappa_eq_tau {s : H} (hs : s ∉ g.Q ⊔ g.L) : ∃ t : H, kappa hχ t = tau := by
  obtain ⟨p, φ, hφ, h | h⟩ := aut_eq (kappa hχ s)
  · exfalso
    obtain ⟨l, hl, hlφ⟩ := exists_mem_L hχ hφ
    have h1 : kappa hχ ((g.chi p * l)⁻¹ * s) = 1 := by
      rw [map_mul, map_inv, map_mul, kappa_chi, hlφ, h]
      group
    apply hs
    have e : s = g.chi p * l * ((g.chi p * l)⁻¹ * s) := by group
    rw [e]
    rcases eq_of_kappa_eq_one hχ hC h1 with h2 | h2
    · rw [h2, mul_one]
      exact Subgroup.mul_mem_sup ⟨p, rfl⟩ hl
    · rw [h2]
      have e2 : g.chi p * l * g.z = (g.chi p * (l * g.z * l⁻¹)) * l := by group
      rw [e2]
      have hlz : l * g.z * l⁻¹ ∈ g.Q := ‹g.Q.Normal›.conj_mem _ g.z_mem_Q l
      exact Subgroup.mul_mem_sup (mul_mem ⟨p, rfl⟩ hlz) hl
  · obtain ⟨l, hl, hlφ⟩ := exists_mem_L hχ hφ
    refine ⟨(g.chi p * l)⁻¹ * s, ?_⟩
    rw [map_mul, map_inv, map_mul, kappa_chi, hlφ, h]
    group

@[expose] def gens (g : VertGens H) (t : H) : Fin 8 → H
  | 0 => g.z
  | 1 => g.y 0
  | 2 => g.y 1
  | 3 => g.y 2
  | 4 => g.y 3
  | 5 => g.a
  | 6 => g.b
  | 7 => t

theorem anti_rel {u v w : H} (hwu : w * u = u * w) (hu : u * u = 1) (hv : v * v = 1)
    (h : v * u = w * (u * v)) : u * v * u * v * w⁻¹ = 1 := by
  calc u * v * u * v * w⁻¹ = u * (v * u) * v * w⁻¹ := by group
    _ = u * (w * (u * v)) * v * w⁻¹ := by rw [h]
    _ = u * (w * u) * (v * v) * w⁻¹ := by group
    _ = u * (u * w) * (v * v) * w⁻¹ := by rw [hwu]
    _ = 1 := by rw [hv, mul_one, ← mul_assoc, hu, one_mul, mul_inv_cancel]

omit [g.Q.Normal] in
theorem chi_xsucc (j : Fin 4) : g.chi (x j.succ) = g.y j := by
  fin_cases j
  · exact g.chi_x1
  · exact g.chi_x2
  · exact g.chi_x3
  · exact g.chi_x4

omit [g.Q.Normal] in
theorem chi_tauImg :
    g.chi (tauImg 0) = (g.y 1)⁻¹ * (g.y 0)⁻¹ * (g.y 2)⁻¹ * (g.y 3)⁻¹ ∧
    g.chi (tauImg 1) = (g.y 1)⁻¹ * g.z⁻¹ ∧ g.chi (tauImg 2) = g.z⁻¹ * (g.y 2)⁻¹ ∧
    g.chi (tauImg 3) = g.z⁻¹ * (g.y 3)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  simp only [tauImg, map_mul, map_inv, g.chi_x1, g.chi_x2, g.chi_x3, g.chi_x4, g.chi_z]

omit [g.Q.Normal] in
theorem rels_hold (t : H) (ε : Bool) (htz : t * g.z = g.z * t)
    (htx : ∀ j : Fin 4, t * g.y j * t⁻¹ = g.chi (tauImg j))
    (hta : t * g.a * t⁻¹ = g.a⁻¹)
    (htb : t * g.b * t⁻¹ = g.a⁻¹ * g.b⁻¹ * g.a⁻¹ * g.b * g.a * g.b⁻¹)
    (ht2 : t * t = if ε then g.z else 1) :
    ∀ r ∈ vRels ε, (r.map fun p => if p.2 then gens g t p.1 else (gens g t p.1)⁻¹).prod = 1 := by
  obtain ⟨hτ0, hτ1, hτ2, hτ3⟩ := chi_tauImg (g := g)
  have hz2 := g.lift.w_sq
  have hy2 := g.lift.y_sq
  have hzy := g.lift.w_comm
  have han := g.lift.anti
  have hax0 : g.a * g.y 0 * g.a⁻¹ = g.y 0 * g.y 1 * g.y 2 * g.y 3 := by
    have := g.ax 1; rwa [g.chi_x1, show pa 1 = 0 by decide, chi_x0] at this
  have hax1 : g.a * g.y 1 * g.a⁻¹ = g.y 2 := by
    have := g.ax 2; rwa [g.chi_x2, show pa 2 = 3 by decide, g.chi_x3] at this
  have hax2 : g.a * g.y 2 * g.a⁻¹ = g.y 1 := by
    have := g.ax 3; rwa [g.chi_x3, show pa 3 = 2 by decide, g.chi_x2] at this
  have hax3 : g.a * g.y 3 * g.a⁻¹ = g.y 3 := by
    have := g.ax 4; rwa [g.chi_x4, show pa 4 = 4 by decide, g.chi_x4] at this
  have hbx0 : g.b * g.y 0 * g.b⁻¹ = g.y 0 := by
    have := g.bx 1; rwa [g.chi_x1, show pb 1 = 1 by decide, g.chi_x1] at this
  have hbx1 : g.b * g.y 1 * g.b⁻¹ = g.y 3 := by
    have := g.bx 2; rwa [g.chi_x2, show pb 2 = 4 by decide, g.chi_x4] at this
  have hbx2 : g.b * g.y 2 * g.b⁻¹ = g.y 2 := by
    have := g.bx 3; rwa [g.chi_x3, show pb 3 = 3 by decide, g.chi_x3] at this
  have hbx3 : g.b * g.y 3 * g.b⁻¹ = g.y 0 * g.y 1 * g.y 2 * g.y 3 := by
    have := g.bx 4; rwa [g.chi_x4, show pb 4 = 0 by decide, chi_x0] at this
  have htx0 := htx 0
  have htx1 := htx 1
  have htx2 := htx 2
  have htx3 := htx 3
  rw [hτ0] at htx0
  rw [hτ1] at htx1
  rw [hτ2] at htx2
  rw [hτ3] at htx3
  have conj_rel : ∀ {c u w : H}, c * u * c⁻¹ = w → c * u * c⁻¹ * w⁻¹ = 1 := fun h => by
    rw [h, mul_inv_cancel]
  have h10 := anti_rel (hzy 0) (hy2 0) (hy2 1) (han 0 1 (by decide))
  have h11 := anti_rel (hzy 0) (hy2 0) (hy2 2) (han 0 2 (by decide))
  have h12 := anti_rel (hzy 0) (hy2 0) (hy2 3) (han 0 3 (by decide))
  have h13 := anti_rel (hzy 1) (hy2 1) (hy2 2) (han 1 2 (by decide))
  have h14 := anti_rel (hzy 1) (hy2 1) (hy2 3) (han 1 3 (by decide))
  have h15 := anti_rel (hzy 2) (hy2 2) (hy2 3) (han 2 3 (by decide))
  have h5 := g.ab_five
  have hb3 := g.b_cube
  have hcj : ∀ {c u w v : H}, c * u * c⁻¹ = w → w * v = 1 → c * (u * (c⁻¹ * v)) = 1 :=
    fun {c u w v} h hv => by rw [← hv, ← h]; group
  cases ε <;>
  simp only [vRels, baseRels, List.cons_append, List.nil_append, List.forall_mem_cons,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gens, ↓reduceIte,
    Bool.false_eq_true, mul_one] at ht2 ⊢ <;>
  refine ⟨hz2, hy2 0, hy2 1, hy2 2, hy2 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g.a_sq, ?_, ?_,
    ?_, ?_, hcj hax0 (by group), hcj hax1 (by group), hcj hax2 (by group),
    hcj hax3 (by group), hcj hbx0 (by group), hcj hbx1 (by group), hcj hbx2 (by group),
    hcj hbx3 (by group), ?_, hcj htx0 (by group), hcj htx1 (by group), hcj htx2 (by group),
    hcj htx3 (by group), hcj hta (by group), hcj htb (by group), ?_,
    fun _ h => by simp at h⟩ <;>
  first
    | (rw [hzy _]; group)
    | (simpa [mul_assoc] using h10) | (simpa [mul_assoc] using h11)
    | (simpa [mul_assoc] using h12) | (simpa [mul_assoc] using h13)
    | (simpa [mul_assoc] using h14) | (simpa [mul_assoc] using h15)
    | (simpa [mul_assoc] using hb3)
    | (simpa [pow_succ, mul_assoc] using h5)
    | (rw [g.za]; group) | (rw [g.zb]; group) | (rw [← htz]; group)
    | (rw [← mul_assoc, ht2]; group) | (rw [ht2])

end VertGens

end CFSG.Quasithin.Background.Harris.R1.J2Vert
