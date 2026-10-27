module

public import CFSG.Quasithin.Background.F918W7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.D35ValChk

open Matrix

private theorem expand_kid : expand kid = idm := by decide

private theorem toM_expand_kid : toM (expand kid) = 1 := by
  rw [expand_kid, toM_idm]

private theorem kid_lt : kid < 2 ^ 18 := by decide

private theorem toM_expand_kmul {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18) :
    toM (expand (kmul a b)) = toM (expand a) * toM (expand b) := by
  rw [expand_kmul ha hb, toM_bmul]

private theorem code_inj {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (h : toM (expand a) = toM (expand b)) : a = b :=
  expand_inj ha hb (toM_inj (expand_lt a) (expand_lt b) h)

private theorem isScalK_iff (m : Nat) : isScalK m = true ↔ m = kid ∨ m = kom ∨ m = kom2 := by
  unfold isScalK
  simp [Nat.beq_eq, or_assoc]

private theorem scal_lt {c : Nat} (h : isScalK c = true) : c < 2 ^ 18 := by
  rcases (isScalK_iff c).mp h with rfl | rfl | rfl <;> decide

private def mat (g : G0) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  ((g : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2))

private theorem mat_mul (g h : G0) : mat (g * h) = mat g * mat h := rfl

private theorem mat_one : mat (1 : G0) = 1 := rfl

private theorem mat_pow (g : G0) (n : ℕ) : mat (g ^ n) = mat g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, mat_mul, ih, pow_succ]

private theorem mat_inj {g h : G0} (e : mat g = mat h) : g = h :=
  Subtype.ext (Units.ext e)

private theorem mat_mul_code {g h : G0} {a b : Nat} (ha : a < 2 ^ 18) (hb : b < 2 ^ 18)
    (hg : mat g = toM (expand a)) (hh : mat h = toM (expand b)) :
    mat (g * h) = toM (expand (kmul a b)) := by
  rw [mat_mul, hg, hh, toM_expand_kmul ha hb]

private theorem not_central_of_code (hF : D35Facts) {r : G0} {m : Nat} (hm : m < 2 ^ 18)
    (h : mat r = toM (expand m)) (hs : isScalK m = false) : r ∉ Subgroup.center G0 := by
  intro hr
  obtain ⟨c, hc, hrc⟩ := (center_G0 hF r).mp hr
  have hcm : m = c := code_inj hm (scal_lt hc) (by rw [← h]; exact hrc)
  rw [hcm, hc] at hs
  exact absurd hs (by decide)

private theorem invol_eq_of_mk_eq (hF : D35Facts) {x f : G0} (hx : x * x = 1) (hf : f * f = 1)
    (h : (QuotientGroup.mk x : G0 ⧸ Subgroup.center G0) = QuotientGroup.mk f) : x = f := by
  have hz : f⁻¹ * x ∈ Subgroup.center G0 := QuotientGroup.eq.mp h.symm
  have hxz : x = f * (f⁻¹ * x) := by rw [mul_inv_cancel_left]
  have hcomm : f * (f⁻¹ * x) = (f⁻¹ * x) * f := Subgroup.mem_center_iff.mp hz f
  have hzz : (f⁻¹ * x) * (f⁻¹ * x) = 1 := by
    have : x * x = (f⁻¹ * x) * (f⁻¹ * x) := by
      calc x * x = (f * (f⁻¹ * x)) * (f * (f⁻¹ * x)) := by rw [← hxz]
        _ = f * ((f⁻¹ * x) * f) * (f⁻¹ * x) := by simp only [mul_assoc]
        _ = f * (f * (f⁻¹ * x)) * (f⁻¹ * x) := by rw [← hcomm]
        _ = (f * f) * ((f⁻¹ * x) * (f⁻¹ * x)) := by simp only [mul_assoc]
        _ = (f⁻¹ * x) * (f⁻¹ * x) := by rw [hf, one_mul]
    rw [← this, hx]
  have hz3 := center_pow_three hF hz
  have hz1 : f⁻¹ * x = 1 := by
    calc f⁻¹ * x = (f⁻¹ * x) * ((f⁻¹ * x) * (f⁻¹ * x)) := by rw [hzz, mul_one]
      _ = (f⁻¹ * x) ^ 3 := (pow_three _).symm
      _ = 1 := hz3
  calc x = f * (f⁻¹ * x) := hxz
    _ = f * 1 := by rw [hz1]
    _ = f := mul_one f

private theorem exists_lift_with_code (hF : D35Facts)
    (α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)) {r : G0} (hr : r * r = 1)
    (hrc : r ∉ Subgroup.center G0) :
    ∃ x : G0, x * x = 1 ∧ x ≠ 1 ∧ (QuotientGroup.mk x : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r) ∧
      ∃ c ∈ invList, mat x = toM (expand c) := by
  have h1 : α (QuotientGroup.mk r) * α (QuotientGroup.mk r) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, hr, QuotientGroup.mk_one, map_one]
  obtain ⟨x, hx, hxm⟩ := exists_invol_lift hF _ h1
  have hx1 : x ≠ 1 := by
    intro h
    apply hrc
    rw [← QuotientGroup.eq_one_iff]
    have : α (QuotientGroup.mk r) = 1 := by rw [← hxm, h, QuotientGroup.mk_one]
    exact (α.map_eq_one_iff).mp this
  obtain ⟨c, hc, hxc⟩ := G0_code hF x
  have hxc' : mat x = toM (expand c) := hxc
  refine ⟨x, hx, hx1, hxm, c, ?_, hxc'⟩
  rw [mem_invList]
  refine ⟨hc, ?_, ?_⟩
  · intro hck
    apply hx1
    apply mat_inj
    rw [hxc', hck, toM_expand_kid, mat_one]
  · apply code_inj (kmul_lt _ _) kid_lt
    rw [toM_expand_kmul (hF.gl_lt c hc) (hF.gl_lt c hc), toM_expand_kid, ← hxc', ← mat_mul, hx, mat_one]

private theorem mk_mul_eq {α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)} {r1 r2 x1 x2 : G0}
    (h1 : (QuotientGroup.mk x1 : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r1))
    (h2 : (QuotientGroup.mk x2 : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r2)) :
    (QuotientGroup.mk (x1 * x2) : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk (r1 * r2)) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, h1, h2, map_mul]

private theorem mk_pow_eq {α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)} {r x : G0}
    (h : (QuotientGroup.mk x : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r)) (n : ℕ) :
    (QuotientGroup.mk (x ^ n) : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk (r ^ n)) := by
  rw [QuotientGroup.mk_pow, QuotientGroup.mk_pow, h, map_pow]

private theorem central_of_mk_eq {α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)} {r x : G0}
    (h : (QuotientGroup.mk x : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r))
    (hr : r ∈ Subgroup.center G0) : x ∈ Subgroup.center G0 := by
  rw [← QuotientGroup.eq_one_iff] at hr ⊢
  rw [h, hr, map_one]

private theorem scalar_of_central (hF : D35Facts) {g : G0} {m : Nat} (hm : m < 2 ^ 18)
    (h : mat g = toM (expand m)) (hg : g ∈ Subgroup.center G0) : isScalK m = true := by
  obtain ⟨c, hc, hgc⟩ := (center_G0 hF g).mp hg
  have : m = c := code_inj hm (scal_lt hc) (by rw [← h]; exact hgc)
  rw [this]
  exact hc

private theorem mat_pow3 {g : G0} {m : Nat} (hm : m < 2 ^ 18) (h : mat g = toM (expand m)) :
    mat (g ^ 3) = toM (expand (kpow3 m)) := by
  rw [mat_pow, h, pow_three, ← toM_expand_kmul hm hm, ← toM_expand_kmul hm (kmul_lt _ _)]
  rfl

private theorem mat_pow4 {g : G0} {m : Nat} (hm : m < 2 ^ 18) (h : mat g = toM (expand m)) :
    mat (g ^ 4) = toM (expand (kpow4 m)) := by
  rw [mat_pow, h, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, ← toM_expand_kmul hm hm,
    ← toM_expand_kmul (kmul_lt _ _) (kmul_lt _ _)]
  rfl

private theorem mat_pow5 {g : G0} {m : Nat} (hm : m < 2 ^ 18) (h : mat g = toM (expand m)) :
    mat (g ^ 5) = toM (expand (kpow5 m)) := by
  have h4 := mat_pow4 hm h
  rw [pow_succ', mat_mul, h, h4]
  exact (toM_expand_kmul hm (kmul_lt _ _ : kpow4 m < 2 ^ 18)).symm

private theorem memF_lt (hF : D35Facts) {a b c : Nat} (hab : (a, b) ∈ offPairs) (h : memF a b c = true) :
    c < 2 ^ 18 := by
  have hab' := mem_offPairs.mp hab
  have ha := hF.gl_lt a (mem_invList.mp hab'.1).1
  have hb := hF.gl_lt b (mem_invList.mp hab'.2.1).1
  unfold memF at h
  simp only [Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with (h | h) | h
  · rw [h]
    exact ha
  · rw [h]
    exact hb
  · rw [h]
    exact kmul_lt _ _

theorem exists_triple_data (hF : D35Facts) (r1 r2 r3 : G0)
    (h1 : ((r1 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand u0))
    (h2 : ((r2 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand a0))
    (h3 : ((r3 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = toM (expand b0))
    (α : (G0 ⧸ Subgroup.center G0) ≃* (G0 ⧸ Subgroup.center G0)) (E F : Subgroup G0)
    (hE : ∀ h : G0, h ∈ E ↔ h ∈ V4set e1 e2) (hF' : OffF2 F)
    (hα : (E.map (QuotientGroup.mk' (Subgroup.center G0))).map α.toMonoidHom =
      F.map (QuotientGroup.mk' (Subgroup.center G0))) :
    ∃ (x1 x2 x3 : G0) (P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)), P * Q = 1 ∧ Q * P = 1 ∧
      QuotientGroup.mk x1 = α (QuotientGroup.mk r1) ∧ QuotientGroup.mk x2 = α (QuotientGroup.mk r2) ∧
      QuotientGroup.mk x3 = α (QuotientGroup.mk r3) ∧
      P * ((r1 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        ((x1 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * P ∧
      P * ((r2 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        ((x2 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * P ∧
      P * ((r3 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        ((x3 : Matrix.GeneralLinearGroup (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) * P := by
  have hu : u0 ∈ gl := hF.gl_mem.2.1
  have ha : a0 ∈ gl := hF.gl_mem.2.2.1
  have hb : b0 ∈ gl := hF.gl_mem.2.2.2
  have hu' : u0 < 2 ^ 18 := hF.gl_lt _ hu
  have ha' : a0 < 2 ^ 18 := hF.gl_lt _ ha
  have hb' : b0 < 2 ^ 18 := hF.gl_lt _ hb
  have h1' : mat r1 = toM (expand u0) := h1
  have h2' : mat r2 = toM (expand a0) := h2
  have h3' : mat r3 = toM (expand b0) := h3
  have hsq : ∀ (r : G0) (m : Nat), m < 2 ^ 18 → mat r = toM (expand m) → kmul m m = kid → r * r = 1 :=
    fun r m hm hr hmm => mat_inj (by rw [mat_mul, hr, ← toM_expand_kmul hm hm, hmm, toM_expand_kid, mat_one])
  have hr1 : r1 * r1 = 1 := hsq r1 u0 hu' h1' (by decide)
  have hr2 : r2 * r2 = 1 := hsq r2 a0 ha' h2' (by decide)
  have hr3 : r3 * r3 = 1 := hsq r3 b0 hb' h3' (by decide)
  have hnc1 : r1 ∉ Subgroup.center G0 := not_central_of_code hF hu' h1' (by decide)
  have hnc2 : r2 ∉ Subgroup.center G0 := not_central_of_code hF ha' h2' (by decide)
  have hnc3 : r3 ∉ Subgroup.center G0 := not_central_of_code hF hb' h3' (by decide)
  have m12 := mat_mul_code hu' ha' h1' h2'
  have m13 := mat_mul_code hu' hb' h1' h3'
  have m23 := mat_mul_code ha' hb' h2' h3'
  have hn12 : r1 * r2 ∉ Subgroup.center G0 := not_central_of_code hF (kmul_lt _ _) m12 (by decide)
  have hn13 : r1 * r3 ∉ Subgroup.center G0 := not_central_of_code hF (kmul_lt _ _) m13 (by decide)
  have hn23 : r2 * r3 ∉ Subgroup.center G0 := not_central_of_code hF (kmul_lt _ _) m23 (by decide)
  obtain ⟨x1, hx1, hx1n, hm1, c1, hc1i, hxc1⟩ := exists_lift_with_code hF α hr1 hnc1
  obtain ⟨x2, hx2, hx2n, hm2, c2, hc2i, hxc2⟩ := exists_lift_with_code hF α hr2 hnc2
  obtain ⟨x3, hx3, hx3n, hm3, c3, hc3i, hxc3⟩ := exists_lift_with_code hF α hr3 hnc3
  have hc1g := (mem_invList.mp hc1i).1
  have hc2g := (mem_invList.mp hc2i).1
  have hc3g := (mem_invList.mp hc3i).1
  have hc1' := hF.gl_lt _ hc1g
  have hc2' := hF.gl_lt _ hc2g
  have hc3' := hF.gl_lt _ hc3g
  have hdist : ∀ (r r' x x' : G0), r * r = 1 → r * r' ∉ Subgroup.center G0 →
      (QuotientGroup.mk x : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r) →
      (QuotientGroup.mk x' : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk r') → x ≠ x' := by
    intro r r' x x' hr hrr hx hx' h
    have : (QuotientGroup.mk r : G0 ⧸ Subgroup.center G0) = QuotientGroup.mk r' :=
      α.injective (by rw [← hx, ← hx', h])
    have hz : r⁻¹ * r' ∈ Subgroup.center G0 := QuotientGroup.eq.mp this
    rw [inv_eq_of_mul_eq_one_right hr] at hz
    exact hrr hz
  have hne12 : c2 ≠ c1 := fun h => hdist r1 r2 x1 x2 hr1 hn12 hm1 hm2 (mat_inj (by rw [hxc1, hxc2, h]))
  have hne13 : c3 ≠ c1 := fun h => hdist r1 r3 x1 x3 hr1 hn13 hm1 hm3 (mat_inj (by rw [hxc1, hxc3, h]))
  have hne23 : c3 ≠ c2 := fun h => hdist r2 r3 x2 x3 hr2 hn23 hm2 hm3 (mat_inj (by rw [hxc2, hxc3, h]))
  have rr12 : (r1 * r2) ^ 3 ∈ Subgroup.center G0 :=
    (center_G0 hF _).mpr ⟨kpow3 (kmul u0 a0), by decide, mat_pow3 (kmul_lt _ _) m12⟩
  have rr13 : (r1 * r3) ^ 3 ∈ Subgroup.center G0 :=
    (center_G0 hF _).mpr ⟨kpow3 (kmul u0 b0), by decide, mat_pow3 (kmul_lt _ _) m13⟩
  have rr23 : (r2 * r3) ^ 4 ∈ Subgroup.center G0 :=
    (center_G0 hF _).mpr ⟨kpow4 (kmul a0 b0), by decide, mat_pow4 (kmul_lt _ _) m23⟩
  have rr123 : (r1 * r2 * r3) ^ 5 ∈ Subgroup.center G0 :=
    (center_G0 hF _).mpr ⟨kpow5 (kmul (kmul u0 a0) b0), by decide,
      mat_pow5 (kmul_lt _ _) (mat_mul_code (kmul_lt _ _) hb' m12 h3')⟩
  have n12 := mat_mul_code hc1' hc2' hxc1 hxc2
  have n13 := mat_mul_code hc1' hc3' hxc1 hxc3
  have n23 := mat_mul_code hc2' hc3' hxc2 hxc3
  have n123 := mat_mul_code (kmul_lt _ _) hc3' n12 hxc3
  have rx12 : rel12 c1 c2 = true :=
    scalar_of_central hF (kmul_lt _ _) (mat_pow3 (kmul_lt _ _) n12)
      (central_of_mk_eq (mk_pow_eq (mk_mul_eq hm1 hm2) 3) rr12)
  have rx13 : rel12 c1 c3 = true :=
    scalar_of_central hF (kmul_lt _ _) (mat_pow3 (kmul_lt _ _) n13)
      (central_of_mk_eq (mk_pow_eq (mk_mul_eq hm1 hm3) 3) rr13)
  have rx23 : rel23 c2 c3 = true :=
    scalar_of_central hF (kmul_lt _ _) (mat_pow4 (kmul_lt _ _) n23)
      (central_of_mk_eq (mk_pow_eq (mk_mul_eq hm2 hm3) 4) rr23)
  have rx123 : rel123 c1 c2 c3 = true :=
    scalar_of_central hF (kmul_lt _ _) (mat_pow5 (kmul_lt _ _) n123)
      (central_of_mk_eq (mk_pow_eq (mk_mul_eq (mk_mul_eq hm1 hm2) hm3) 5) rr123)
  obtain ⟨a, b, hab, hFab⟩ := offender_classification hF hF'
  have hr2E : r2 ∈ E := (hE r2).mpr (Or.inr ⟨e1, by decide, h2'⟩)
  have mr323 : mat (r3 * r2 * r3) = toM (expand e2) :=
    mat_mul_code (kmul_lt _ _) hb' (mat_mul_code hb' ha' h3' h2') h3'
  have hr323E : r3 * r2 * r3 ∈ E := (hE _).mpr (Or.inr ⟨e2, by decide, mr323⟩)
  have himg : ∀ g ∈ E, ∃ f ∈ F, (QuotientGroup.mk f : G0 ⧸ Subgroup.center G0) = α (QuotientGroup.mk g) := by
    intro g hg
    have : α (QuotientGroup.mk g) ∈ (E.map (QuotientGroup.mk' (Subgroup.center G0))).map α.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hg)
    rw [hα] at this
    obtain ⟨f, hf, hfe⟩ := Subgroup.mem_map.mp this
    exact ⟨f, hf, hfe⟩
  have hFsq : ∀ f ∈ F, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hF'.2.2.1 f hf
  obtain ⟨f2, hf2, hmf2⟩ := himg r2 hr2E
  have hx2F : x2 ∈ F := by
    have := invol_eq_of_mk_eq hF hx2 (hFsq f2 hf2) (hm2.trans hmf2.symm)
    rw [this]
    exact hf2
  have hyy : (x3 * x2 * x3) * (x3 * x2 * x3) = 1 := by
    calc (x3 * x2 * x3) * (x3 * x2 * x3) = x3 * (x2 * (x3 * x3) * x2) * x3 := by simp only [mul_assoc]
      _ = x3 * (x2 * x2) * x3 := by rw [hx3, mul_one]
      _ = x3 * x3 := by rw [hx2, mul_one]
      _ = 1 := hx3
  obtain ⟨f', hf', hmf'⟩ := himg _ hr323E
  have hyF : x3 * x2 * x3 ∈ F := by
    have := invol_eq_of_mk_eq hF hyy (hFsq f' hf') ((mk_mul_eq (mk_mul_eq hm3 hm2) hm3).trans hmf'.symm)
    rw [this]
    exact hf'
  have hy1 : x3 * x2 * x3 ≠ 1 := by
    intro h
    apply hx2n
    calc x2 = (x3 * x3) * x2 * (x3 * x3) := by rw [hx3, one_mul, mul_one]
      _ = x3 * (x3 * x2 * x3) * x3 := by simp only [mul_assoc]
      _ = x3 * 1 * x3 := by rw [h]
      _ = 1 := by rw [mul_one, hx3]
  have key : ∀ (x : G0) (c : Nat), x ∈ F → x ≠ 1 → mat x = toM (expand c) → c < 2 ^ 18 →
      memF a b c = true := by
    intro x c hxF hx1 hxc hc
    rcases (hFab x).mp hxF with h | ⟨c', hc', hxc'⟩
    · exact absurd h hx1
    · have : c' = c := code_inj (memF_lt hF hab hc') hc (hxc'.symm.trans hxc)
      rw [← this]
      exact hc'
  have hcls : classPres c2 (kmul (kmul c3 c2) c3) = true := by
    rw [classPres_iff]
    refine ⟨(a, b), hab, key x2 c2 hx2F hx2n hxc2 hc2', ?_⟩
    exact key _ _ hyF hy1 (mat_mul_code (kmul_lt _ _) hc3' (mat_mul_code hc3' hc2' hxc3 hxc2) hxc3) (kmul_lt _ _)
  have hpres : (c1, c2, c3) ∈ presList :=
    mem_presList.mpr ⟨hc1i, ⟨hc2i, hne12, rx12⟩, ⟨hc3i, hne13, rx13⟩, hne23, rx23, rx123, hcls⟩
  obtain ⟨P, Q, hP, hQ, e1', e2', e3', hPQ⟩ := hF.triple_bij c1 c2 c3 hpres
  have hPQ' : toM P * toM Q = 1 := by rw [← toM_bmul, hPQ, toM_idm]
  refine ⟨x1, x2, x3, toM P, toM Q, hPQ', mul_eq_one_comm.mp hPQ', hm1, hm2, hm3, ?_, ?_, ?_⟩
  · have := congrArg toM e1'
    rw [toM_bmul, toM_bmul] at this
    show toM P * mat r1 = mat x1 * toM P
    rw [h1', hxc1]
    exact this
  · have := congrArg toM e2'
    rw [toM_bmul, toM_bmul] at this
    show toM P * mat r2 = mat x2 * toM P
    rw [h2', hxc2]
    exact this
  · have := congrArg toM e3'
    rw [toM_bmul, toM_bmul] at this
    show toM P * mat r3 = mat x3 * toM P
    rw [h3', hxc3]
    exact this

end CFSG.Quasithin.D35ValChk
