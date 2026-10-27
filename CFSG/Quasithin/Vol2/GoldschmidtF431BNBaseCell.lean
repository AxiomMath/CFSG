module

public import CFSG.Quasithin.Vol2.GoldschmidtF431BNAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad

public noncomputable section

namespace CFSG.Quasithin.H13.F431.BN

open CFSG.GH74.BNPair CFSG.QuasithinUnique
open scoped Pointwise

section Generic

variable {X : Type*} [Group X] {B N : Subgroup X} [(cartan B N).Normal]
  {S : Finset (WeylGroup B N)} {a b : WeylGroup B N} {m : ℕ}

theorem same_cell_eq_of_ascent (R : Rank2 B N S a b m) {k : Bool} {w : WeylGroup B N}
    (hlt : wordLength (S : Set (WeylGroup B N)) w <
      wordLength (S : Set (WeylGroup B N)) (gen a b k * w)) {y y' : X}
    (hy : y ∈ dc B N w) (hy' : y' ∈ dc B N w) (h : y' * y⁻¹ ∈ pgen B N a b k) :
    y' * y⁻¹ ∈ B := by
  rcases (mem_parabolic_single_iff R.tits (R.gen_mem k)).1 h with hB | hdc
  · exact hB
  · exfalso
    have hmul : y' ∈ dc B N (gen a b k) * dc B N w :=
      Set.mem_mul.2 ⟨y' * y⁻¹, hdc, y, hy, by group⟩
    have hsub := R.tits.bnCore.mul_subset_of_lt (Finset.mem_coe.2 (R.gen_mem k))
      (R.tits.mem_closure w) hlt hmul
    have := R.tits.dc_injective (dc_eq_of_mem hy' hsub)
    rw [← this] at hlt
    exact lt_irrefl _ hlt

@[expose] def oppType (m : ℕ) (i : Bool) : Bool :=
  if Even m then i else !i

@[expose] def altStar (a b : WeylGroup B N) (m : ℕ) (i : Bool) : WeylGroup B N :=
  altWord (gen a b (!i)) (gen a b i) (m - 1)

theorem altStar_ascent (R : Rank2 B N S a b m) (i : Bool) {k : Bool} (hk : k = oppType m i) :
    wordLength (S : Set (WeylGroup B N)) (altStar a b m i) <
      wordLength (S : Set (WeylGroup B N)) (gen a b k * altStar a b m i) := by
  have hn := R.dih.three_le
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hnj : m - 1 = j := by omega
  have hlet : gen a b k * altStar a b m i = altWord (gen a b (!i)) (gen a b i) m := by
    have h := altWord_succ_left (gen a b (!i)) (gen a b i) j
    rw [← hj] at h
    rw [h, altStar, hnj]
    have hk' : k = if Even (j + 1) then i else !i := by rw [hk, oppType, hj]
    rw [hk']
    by_cases he : Even j <;> simp [he, Nat.even_add_one]
  rw [hlet]
  have h1 := R.ell_alt (!i) (j := m) le_rfl
  have h2 := R.ell_alt (!i) (j := m - 1) (by omega)
  rw [Bool.not_not] at h1 h2
  show wordLength _ (altWord _ _ (m - 1)) < _
  rw [h1, h2]
  omega

end Generic

variable {X : Type*} [Group X] {n : ℕ} (D : RankTwoSystem X n)

@[expose] def wS (i : Bool) : D.Weyl :=
  altStar D.w₁ D.w₂ n i

theorem coe_UwMinus_wS (i : Bool) :
    (D.UwMinusSub (D.lift (wS D i)) : Set X) = (Uplus D i : Set X) := by
  have hn := D.three_le
  cases i
  · have h := (D.eq30_5_A (i := n - 1) (by omega) (D.lift (wS D false))
      (by rw [D.lift_mk]; rfl)).1
    have e : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    rw [e] at h
    show D.UwMinus _ = _
    rw [h, coe_Uplus_false]
  · have h := (D.eq30_5_B (i := n - 1) (by omega) (D.lift (wS D true))
      (by rw [D.lift_mk]; rfl)).1
    have e : (n : ℤ) - ((n - 1 : ℕ) : ℤ) + 1 = 2 := by omega
    rw [e] at h
    show D.UwMinus _ = _
    rw [h, coe_Uplus_true, ← D.chainProd_intList_reverse (a := 2) (b := n) (by norm_num) le_rfl]

section Sylow

variable [Finite X]

theorem Q_eq_UwMinus (hU : IsSylowTwoOf D.U ⊤) (i : Bool) :
    Q D i = D.UwMinusSub (D.lift (wS D i)) :=
  (SetLike.coe_injective ((coe_UwMinus_wS D i).trans (congrArg _ (Q_eq_Uplus D hU i).symm))).symm

theorem mem_Q_iff_UwMinus (hU : IsSylowTwoOf D.U ⊤) (i : Bool) {x : X} :
    x ∈ Q D i ↔ x ∈ D.UwMinus (D.lift (wS D i)) := by
  rw [Q_eq_UwMinus D hU i]
  rfl

end Sylow

theorem adj_vt_vt (i : Bool) : (Γ D).Adj (vt D i 1) (vt D (!i) 1) := by
  refine ⟨vt_ne_of_ne i (!i) (by cases i <;> simp) 1 1, 1, mem_self_vtx, mem_self_vtx⟩

theorem exists_cell_rep (i : Bool) {b : V D} (hb : (Γ D).dist (v D i) b = n) :
    ∃ y ∈ dc D.B D.N (wS D i), b = vt D (oppType n i) y := by
  have hn := D.three_le
  rw [v_eq_vt] at hb
  obtain ⟨l, hl, hh, hla, hlen, h1⟩ := D.polyHyp.exists_path_through hb (adj_vt_vt D i)
  obtain ⟨f, k, hk, hf0, hfk, hfadj, hfnb, hfl⟩ := hl.exists_fun hh hla
  have hkn : k = n := by omega
  rw [hkn] at hfk hfadj hfnb hfl
  have hf1 : f 1 = vt D (!i) 1 := by
    have := hfl 1 (by omega)
    rw [h1] at this
    exact (Option.some.inj this).symm
  obtain ⟨y, hy1, hy2⟩ := (hfadj (n - 1) (by omega)).2
  rw [show n - 1 + 1 = n by omega] at hy2
  have hty0 : vtype D.B D.N D.w₁ D.w₂ (f 0) = i := by rw [hf0]; exact vtype_vt D i 1
  have hw := D.rank2.gallery f n le_rfl hfadj hfnb (n - 1) (by omega) 1 y
    (by rw [hf0]; exact mem_self_vtx) (by rw [hf1]; exact mem_self_vtx) hy1 (by
      rw [show n - 1 + 1 = n by omega]; exact hy2)
  rw [hty0] at hw
  refine ⟨y, by simpa [WPos, wS, altStar] using hw, ?_⟩
  have hbe := D.rank2.eq_vtx_of_mem hy2
  rw [hfk] at hbe
  have hty : vtype D.B D.N D.w₁ D.w₂ (f n) = oppType n i := by
    have := D.rank2.vtype_path hfadj n le_rfl
    rw [this, hty0, oppType]
  rw [hfk] at hty
  rw [hty] at hbe
  exact hbe

section Regular

variable [Finite X]

theorem cell_trans (hU : IsSylowTwoOf D.U ⊤) (i : Bool) {b c : V D}
    (hb : (Γ D).dist (v D i) b = n) (hc : (Γ D).dist (v D i) c = n) :
    ∃ q ∈ Q D i, q • b = c := by
  obtain ⟨y, hy, rfl⟩ := exists_cell_rep D i hb
  obtain ⟨z, hz, rfl⟩ := exists_cell_rep D i hc
  obtain ⟨b₁, hb₁, u, hu, rfl⟩ := (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).1 hy
  obtain ⟨b₂, hb₂, u', hu', rfl⟩ := (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).1 hz
  refine ⟨u'⁻¹ * u, ?_, ?_⟩
  · rw [mem_Q_iff_UwMinus D hU]
    exact (D.UwMinusSub (D.lift (wS D i))).mul_mem
      ((D.UwMinusSub (D.lift (wS D i))).inv_mem hu') hu
  · rw [smul_vt, vt_eq_vt_iff]
    have e : b₁ * (D.lift (wS D i) : X) * u * (u'⁻¹ * u)⁻¹ *
        (b₂ * (D.lift (wS D i) : X) * u')⁻¹ = b₁ * b₂⁻¹ := by group
    rw [e]
    exact D.rank2.B_le_pgen _ (D.B.mul_mem hb₁ (D.B.inv_mem hb₂))

theorem cell_free (hU : IsSylowTwoOf D.U ⊤) (i : Bool) {b : V D}
    (hb : (Γ D).dist (v D i) b = n) {q : X} (hq : q ∈ Q D i) (hqb : q • b = b) : q = 1 := by
  obtain ⟨y, hy, rfl⟩ := exists_cell_rep D i hb
  have hqU : q ∈ D.UwMinus (D.lift (wS D i)) := (mem_Q_iff_UwMinus D hU i).1 hq
  obtain ⟨b₁, hb₁, u, hu, rfl⟩ := (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).1 hy
  rw [smul_vt, vt_eq_vt_iff] at hqb
  have huq : u * q⁻¹ ∈ D.UwMinus (D.lift (wS D i)) :=
    (D.UwMinusSub (D.lift (wS D i))).mul_mem hu ((D.UwMinusSub (D.lift (wS D i))).inv_mem hqU)
  have hy' : b₁ * (D.lift (wS D i) : X) * (u * q⁻¹) ∈ dc D.B D.N (wS D i) :=
    (D.mem_dc_iff_coord (D.lift (wS D i)) (D.lift_mk _)).2 ⟨b₁, hb₁, u * q⁻¹, huq, rfl⟩
  have hbB := same_cell_eq_of_ascent D.rank2 (altStar_ascent D.rank2 i rfl) hy hy'
    (by simpa [mul_assoc] using hqb)
  have := D.coord_unique (D.lift (wS D i)) (b := b₁)
    (b' := (b₁ * (D.lift (wS D i) : X) * (u * q⁻¹) *
      (b₁ * (D.lift (wS D i) : X) * u)⁻¹) * b₁) hb₁ (D.B.mul_mem hbB hb₁) huq hu (by group)
  simpa using this

end Regular

end CFSG.Quasithin.H13.F431.BN
