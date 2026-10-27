module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Quat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Abs

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.A312U3 CFSG.Quasithin.B6
  CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def ofSL2 (p : ℕ) [Fact p.Prime] : SL(2, ZMod p) →* PSL3 p :=
  (piL p).comp ((leviHom p).comp Matrix.SpecialLinearGroup.toGL)

theorem ofSL2_mem_leviC (A : SL(2, ZMod p)) : ofSL2 p A ∈ leviC p :=
  ⟨leviHom p (Matrix.SpecialLinearGroup.toGL A), ⟨_, rfl⟩, rfl⟩

theorem exists_special_sylow (hp2 : p ≠ 2) :
    ∃ (U : Subgroup (PSL3 p)) (c d : SL(2, ZMod p)), IsSylowTwoOf U ⊤ ∧ U ≤ leviC p ∧
      QuatPair c d ∧ ofSL2 p c ∈ U ∧ ofSL2 p d ∈ U := by
  obtain ⟨c, d, hQ⟩ := exists_quatPair_sl2 hp2
  have hX : IsPGroup 2 ↥((Subgroup.closure ({c, d} : Set SL(2, ZMod p))).map (ofSL2 p)) :=
    hQ.isPGroup_two_closure.map _
  have hXB : (Subgroup.closure ({c, d} : Set SL(2, ZMod p))).map (ofSL2 p) ≤ leviC p := by
    rintro _ ⟨x, -, rfl⟩
    exact ofSL2_mem_leviC x
  obtain ⟨S, hS, hXS⟩ := exists_isSylowTwoOf_ge hX hXB
  refine ⟨S, c, d, isSylowTwoOf_top_of_odd_index (odd_index_leviC hp2) hS, hS.1, hQ, ?_, ?_⟩
  · exact hXS ⟨c, Subgroup.subset_closure (by simp), rfl⟩
  · exact hXS ⟨d, Subgroup.subset_closure (by simp), rfl⟩

theorem eq_one_of_piL_leviHom_eq_one {X : GL (Fin 2) (ZMod p)}
    (hdet : (X : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1) (h : piL p (leviHom p X) = 1) :
    X = 1 := by
  have hk : leviHom p X ∈ (piL p).ker := h
  rw [ker_piL] at hk
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  have h22 := congrFun (congrFun hr 2) 2
  simp [coe_leviHom, hdet, Matrix.scalar_apply] at h22
  have hr1 : r = 1 := h22
  have : leviHom p X = 1 := by
    apply Subtype.ext
    rw [← hr, hr1]
    simp
  exact leviHom_injective (this.trans (map_one (leviHom p)).symm)

theorem commute_of_piL_commute {A B : GL (Fin 2) (ZMod p)}
    (h : piL p (leviHom p A) * piL p (leviHom p B) = piL p (leviHom p B) * piL p (leviHom p A)) :
    A * B = B * A := by
  have hdet : ((A * B * A⁻¹ * B⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det =
      1 := by
    have hc : ∀ a b : (ZMod p)ˣ, a * b * a⁻¹ * b⁻¹ = 1 := fun a b => by
      rw [mul_comm a b, mul_inv_cancel_right, mul_inv_cancel]
    have h1 : Matrix.GeneralLinearGroup.det (A * B * A⁻¹ * B⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      exact hc _ _
    have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) h1
    rw [Matrix.GeneralLinearGroup.val_det_apply] at this
    simpa using this
  have h1 : piL p (leviHom p (A * B * A⁻¹ * B⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    rw [h]
    group
  have := eq_one_of_piL_leviHom_eq_one hdet h1
  calc A * B = A * B * A⁻¹ * B⁻¹ * (B * A) := by group
    _ = B * A := by rw [this, one_mul]

theorem two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)

theorem zOf_comm_levi (hp2 : p ≠ 2) {U : Subgroup (PSL3 p)} {c d : SL(2, ZMod p)}
    (hQ : QuatPair c d) (hc : ofSL2 p c ∈ U) (hd : ofSL2 p d ∈ U) (hUB : U ≤ leviC p)
    {w b : PSL3 p} (hw : w ∈ zOf U) (hb : b ∈ leviC p) : w * b = b * w := by
  have h2 := two_ne_zero_zmod hp2
  obtain ⟨gw, ⟨A, rfl⟩, rfl⟩ := hUB hw.1
  obtain ⟨gb, ⟨B, rfl⟩, rfl⟩ := hb
  have hQ' := hQ.map (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod p) →* GL (Fin 2) (ZMod p))
    Matrix.SpecialLinearGroup.toGL_injective
  obtain ⟨hC, hD, hDC⟩ := quat_relations h2
    (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact c.2) hQ'
  have hAcomm : ∀ e : SL(2, ZMod p), ofSL2 p e ∈ U →
      (A : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (Matrix.SpecialLinearGroup.toGL e : Matrix (Fin 2) (Fin 2) (ZMod p)) =
      (Matrix.SpecialLinearGroup.toGL e : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        (A : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.mp hw.2 (ofSL2 p e) he
    have h2' := commute_of_piL_commute (A := A) (B := Matrix.SpecialLinearGroup.toGL e) h1.symm
    have := congrArg (fun g : GL (Fin 2) (ZMod p) => (g : Matrix (Fin 2) (Fin 2) (ZMod p))) h2'
    simpa [Units.val_mul] using this
  obtain ⟨x, hx⟩ := scalar_of_commute_quat h2 hC hD hDC (hAcomm c hc) (hAcomm d hd)
  have hAB : A * B = B * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hx]
    exact (Matrix.scalar_commute x (fun r => Commute.all _ _) _).eq
  show piL p (leviHom p A) * piL p (leviHom p B) = piL p (leviHom p B) * piL p (leviHom p A)
  calc piL p (leviHom p A) * piL p (leviHom p B) = piL p (leviHom p (A * B)) := by
        simp only [map_mul]
    _ = piL p (leviHom p (B * A)) := by rw [hAB]
    _ = piL p (leviHom p B) * piL p (leviHom p A) := by simp only [map_mul]

@[expose] noncomputable def zt (p : ℕ) [Fact p.Prime] : SL(3, ZMod p) := leviHom p (-1)

theorem coe_zt : ((zt p : SL(3, ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
    !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zt, coe_leviHom, Matrix.det_neg]

@[expose] noncomputable def zc (p : ℕ) [Fact p.Prime] : PSL3 p := piL p (zt p)

theorem mem_leviC_of_commute_z (hp2 : p ≠ 2) {g : PSL3 p} (h : g * zc p = zc p * g) :
    g ∈ leviC p := by
  obtain ⟨g, rfl⟩ := piL_surjective g
  have h1 : piL p ((g * zt p)⁻¹ * (zt p * g)) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul]
    exact inv_mul_eq_one.mpr h
  have hk : (g * zt p)⁻¹ * (zt p * g) ∈ Subgroup.center SL(3, ZMod p) := by
    rw [← ker_piL]
    exact h1
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
  set q := (g * zt p)⁻¹ * (zt p * g) with hqdef
  have hq : (g * zt p) * q = zt p * g := mul_inv_cancel_left _ _
  have hm := congrArg (fun x : SL(3, ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) hq
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hm
  rw [← hr, coe_zt] at hm
  have hr1 : r + 1 ≠ 0 := by
    intro h0
    have : r = -1 := by linear_combination h0
    rw [this] at hr3
    simp at hr3
    exact two_ne_zero_zmod hp2 (by linear_combination -hr3)
  have e02 := congrFun (congrFun hm 0) 2
  have e12 := congrFun (congrFun hm 1) 2
  have e20 := congrFun (congrFun hm 2) 0
  have e21 := congrFun (congrFun hm 2) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply]
    at e02 e12 e20 e21
  refine ⟨g, mem_leviBlock_iff.mpr ⟨?_, ?_, ?_, ?_⟩, rfl⟩
  · exact (mul_eq_zero.mp (by linear_combination e02 :
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2 * (r + 1) = 0)).resolve_right hr1
  · exact (mul_eq_zero.mp (by linear_combination e12 :
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 1 2 * (r + 1) = 0)).resolve_right hr1
  · exact (mul_eq_zero.mp (by linear_combination -e20 :
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 0 * (r + 1) = 0)).resolve_right hr1
  · exact (mul_eq_zero.mp (by linear_combination -e21 :
      (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 2 1 * (r + 1) = 0)).resolve_right hr1

theorem zc_comm_levi {b : PSL3 p} (hb : b ∈ leviC p) : zc p * b = b * zc p := by
  obtain ⟨gb, ⟨B, rfl⟩, rfl⟩ := hb
  have h : (-1 : GL (Fin 2) (ZMod p)) * B = B * (-1) := by
    apply Units.ext
    simp
  show piL p (leviHom p (-1)) * piL p (leviHom p B) = piL p (leviHom p B) * piL p (leviHom p (-1))
  calc piL p (leviHom p (-1)) * piL p (leviHom p B) = piL p (leviHom p ((-1) * B)) := by
        simp only [map_mul]
    _ = piL p (leviHom p (B * (-1))) := by rw [h]
    _ = piL p (leviHom p B) * piL p (leviHom p (-1)) := by simp only [map_mul]

theorem zc_eq_sq (hp2 : p ≠ 2) {c d : SL(2, ZMod p)} (hQ : QuatPair c d) :
    zc p = ofSL2 p c * ofSL2 p c := by
  have h2 := two_ne_zero_zmod hp2
  have hQ' := hQ.map (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod p) →* GL (Fin 2) (ZMod p))
    Matrix.SpecialLinearGroup.toGL_injective
  obtain ⟨hC, -, -⟩ := quat_relations h2
    (by rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact c.2) hQ'
  have hc : Matrix.SpecialLinearGroup.toGL c * Matrix.SpecialLinearGroup.toGL c = -1 := by
    apply Units.ext
    simpa using hC
  show piL p (leviHom p (-1)) = piL p (leviHom p (Matrix.SpecialLinearGroup.toGL c)) *
    piL p (leviHom p (Matrix.SpecialLinearGroup.toGL c))
  rw [← map_mul, ← map_mul, hc]

theorem centralizer_zOf_eq_special (hp2 : p ≠ 2) {U : Subgroup (PSL3 p)} {c d : SL(2, ZMod p)}
    (hQ : QuatPair c d) (hc : ofSL2 p c ∈ U) (hd : ofSL2 p d ∈ U) (hUB : U ≤ leviC p) :
    Subgroup.centralizer (zOf U : Set (PSL3 p)) = leviC p := by
  have hzU : zc p ∈ zOf U := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    · rw [zc_eq_sq hp2 hQ]
      exact U.mul_mem hc hc
    · exact (zc_comm_levi (hUB hu)).symm
  apply le_antisymm
  · intro g hg
    exact mem_leviC_of_commute_z hp2 (Subgroup.mem_centralizer_iff.mp hg (zc p) hzU).symm
  · intro b hb
    exact Subgroup.mem_centralizer_iff.mpr fun w hw => zOf_comm_levi hp2 hQ hc hd hUB hw hb

theorem centralizer_zOf_eq_leviC (hp2 : p ≠ 2) {U : Subgroup (PSL3 p)} (hU : IsSylowTwoOf U ⊤)
    (hUB : U ≤ leviC p) : Subgroup.centralizer (zOf U : Set (PSL3 p)) = leviC p := by
  obtain ⟨U₀, c, d, hU₀, hU₀B, hQ, hc, hd⟩ := exists_special_sylow hp2
  obtain ⟨g, hg, hUg⟩ := isSylowTwoOf_exists_conj (isSylowTwoOf_mono hU₀ hU₀B le_top)
    (isSylowTwoOf_mono hU hUB le_top)
  have hUeq : U = U₀.map (MulAut.conj g).toMonoidHom := hUg
  rw [hUeq, ← map_zOf, ← map_centralizer_eq, centralizer_zOf_eq_special hp2 hQ hc hd hU₀B]
  exact conjSub_eq_self (Subgroup.le_normalizer hg)

end CFSG.Quasithin.E2P.Asc80
