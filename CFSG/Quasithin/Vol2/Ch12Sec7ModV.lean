module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModU
public import CFSG.Quasithin.Vol2.Ch12Sec7ModR

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem pn_oPts : ∀ p ∈ oPts, pn p = p := by decide

theorem zs6_app' : ∀ z ∈ zs6, ∃ c < 4, c ≠ 0 ∧ ∀ v < 64, z.app v = sV c v := by decide

abbrev OP : Type := {p : ℕ // p ∈ oPts}

theorem card_OP : Nat.card OP = 6 := by
  have e : OP ≃ ↥oPts.toFinset := Equiv.subtypeEquivRight fun p => by simp
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup oPts_nodup]
  rfl

instance : Finite OP := (List.finite_toSet oPts).to_subtype

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem linOrSemi
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {m : MulAut ↥V}
    (hm : m ∈ h.hyp.MVbar) : IsLin (C.cB m) ∨ IsSemi (C.cB m) := by
  by_cases hmL : m ∈ autOn L V
  · exact Or.inl ((MVbar_code h hC hm).2.2.1.1 hmL)
  · exact Or.inr ((MVbar_code h hC hm).2.2.2 hmL)

theorem ptmap_mem
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {m : MulAut ↥V}
    (hm : m ∈ h.hyp.MVbar) {p : ℕ} (hp : p ∈ oPts) : pn ((C.cB m).app p) ∈ oPts := by
  have hO := (MVbar_code h hC hm).2.1 p (oPts_oVec p hp)
  exact ((oVecL_iff _ (oVecL_lt _ hO)).1 hO).2

omit [Finite G] in
theorem app_ne_zero_of_oPts {C : Coding ↥V} (m : MulAut ↥V) {p : ℕ} (hp : p ∈ oPts) :
    (C.cB m).app p ≠ 0 := by
  intro h0
  have := C.cB_app_injective m (oPts_lt p hp) (by norm_num : 0 < 64)
    (by rw [h0, B6.app_zero])
  exact oPts_ne_zero p hp this

theorem pn_comp_app
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {m n : MulAut ↥V}
    (hm : m ∈ h.hyp.MVbar) {p : ℕ} (hp : p ∈ oPts) :
    pn ((C.cB m).app (pn ((C.cB n).app p))) = pn ((C.cB (m * n)).app p) := by
  rw [pn_app_pn (C.cB_valid m) (linOrSemi h hC hm) (B6.app_lt (C.cB_valid n) p)
    (app_ne_zero_of_oPts n hp), C.cB_mul, B6.app_comp]

@[expose] noncomputable def piPts
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    ↥h.hyp.MVbar →* Equiv.Perm OP where
  toFun m :=
    { toFun := fun p => ⟨pn ((C.cB m).app p), ptmap_mem h hC m.2 p.2⟩
      invFun := fun p => ⟨pn ((C.cB (m⁻¹ : ↥h.hyp.MVbar)).app p), ptmap_mem h hC (m⁻¹).2 p.2⟩
      left_inv := fun p => Subtype.ext (by
        show pn ((C.cB ((m⁻¹ : ↥h.hyp.MVbar) : MulAut ↥V)).app (pn ((C.cB m).app p))) = p
        rw [pn_comp_app h hC (m⁻¹).2 p.2, Subgroup.coe_inv, inv_mul_cancel, C.cB_one,
          B6.id_app _ (oPts_lt _ p.2), pn_oPts _ p.2])
      right_inv := fun p => Subtype.ext (by
        show pn ((C.cB (m : MulAut ↥V)).app (pn ((C.cB ((m⁻¹ : ↥h.hyp.MVbar) :
          MulAut ↥V)).app p))) = p
        rw [pn_comp_app h hC m.2 p.2, Subgroup.coe_inv, mul_inv_cancel, C.cB_one,
          B6.id_app _ (oPts_lt _ p.2), pn_oPts _ p.2]) }
  map_one' := by
    ext p
    show pn ((C.cB 1).app p) = p
    rw [C.cB_one, B6.id_app _ (oPts_lt _ p.2), pn_oPts _ p.2]
  map_mul' m n := by
    ext p
    show pn ((C.cB ((m : MulAut ↥V) * n)).app p) =
      pn ((C.cB (m : MulAut ↥V)).app (pn ((C.cB (n : MulAut ↥V)).app p)))
    rw [pn_comp_app h hC m.2 p.2]

theorem mem_ker_piPts
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) (m : ↥h.hyp.MVbar) :
    m ∈ (piPts h hC).ker ↔ C.cB m ∈ zs6 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hm
    refine cert_ker6 _ (MVbar_code h hC m.2).1 fun p hp => ?_
    have := congrArg (fun σ : Equiv.Perm OP => ((σ ⟨p, hp⟩ : OP) : ℕ)) hm
    exact this
  · intro hz
    obtain ⟨c, hc, hc0, hzc⟩ := zs6_app' _ hz
    ext p
    show pn ((C.cB m).app p) = p
    rw [hzc _ (oPts_lt _ p.2), pn_sV _ (oPts_lt _ p.2) _ hc hc0, pn_oPts _ p.2]

theorem card_ker_piPts
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) :
    Nat.card (piPts h hC).ker = 3 := by
  classical
  have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
  have e : ↥(piPts h hC).ker ≃ {B : B6 // B ∈ zs6} :=
    Equiv.ofBijective (fun m => ⟨C.cB ((m : ↥h.hyp.MVbar) : MulAut ↥V),
      (mem_ker_piPts h hC m).1 m.2⟩)
      ⟨fun a b hab => Subtype.ext (Subtype.ext (C.cB_injective (congrArg Subtype.val hab))),
        fun B => by
          obtain ⟨a, ha⟩ := hC.2 B.1 (zs6_sub_gm6 _ B.2)
          have haM : a ∈ h.hyp.MVbar := hLM ((hC.1 a).2 (ha ▸ zs6_sub_gm6 _ B.2))
          exact ⟨⟨⟨a, haM⟩, (mem_ker_piPts h hC _).2 (ha ▸ B.2)⟩, Subtype.ext ha⟩⟩
  rw [Nat.card_congr e]
  have e2 : {B : B6 // B ∈ zs6} ≃ ↥zs6.toFinset := Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup zs6_nodup]
  rfl

theorem lemma12_7_2_one
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    h.hyp.MVbar = autOn L V ∨
      (h.hyp.MVbar = autOn L V ⊔ autOn T V ∧
        Nonempty (↥h.hyp.MVbar ⧸ CFSG.pCore 3 ↥h.hyp.MVbar ≃* Equiv.Perm (Fin 6))) := by
  obtain ⟨C, hC⟩ := exists_identL_G h1222 h
  by_cases hne : h.hyp.MVbar = autOn L V
  · exact Or.inl hne
  right
  have hLM : autOn L V ≤ h.hyp.MVbar := A4.autOn_mono (L_le_MV h)
  have hTM : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  obtain ⟨τ, hτT, hτL⟩ := exists_T_not_L h1222 h hC hne
  have hτM := hTM hτT
  refine ⟨le_antisymm (fun m hm => ?_) (sup_le hLM hTM), ?_⟩
  · by_cases hmL : m ∈ autOn L V
    · exact le_sup_left (a := autOn L V) hmL
    ·
      have hτi : τ⁻¹ ∈ h.hyp.MVbar := h.hyp.MVbar.inv_mem hτM
      have hτiL : τ⁻¹ ∉ autOn L V := fun h' => hτL (by simpa using (autOn L V).inv_mem h')
      have hs1 := (MVbar_code h hC hm).2.2.2 hmL
      have hs2 := (MVbar_code h hC hτi).2.2.2 hτiL
      have hlin : IsLin (C.cB (m * τ⁻¹)) := by
        rw [C.cB_mul]
        exact isLin_comp_semi hs1 hs2 (C.cB_valid _) (C.cB_valid _)
      have hmτ := (MVbar_code h hC (h.hyp.MVbar.mul_mem hm hτi)).2.2.1.2 hlin
      have e : m = m * τ⁻¹ * τ := by group
      rw [e]
      exact Subgroup.mul_mem _ (le_sup_left (a := autOn L V) hmτ)
        (le_sup_right (b := autOn T V) hτT)
  ·
    set π := piPts h hC with hπ
    have hcard := card_MVbar_of_ne h hC hne
    have hker := card_ker_piPts h hC
    have hrange : Nat.card π.range = 720 := by
      have := Subgroup.card_ker_mul_card_range π
      rw [hker, hcard] at this
      omega
    have hsurj : Function.Surjective π := by
      rw [← MonoidHom.range_eq_top]
      apply Subgroup.eq_top_of_card_eq
      rw [hrange, Nat.card_perm, card_OP]
      decide
    have hkerP : π.ker = CFSG.pCore 3 ↥h.hyp.MVbar := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      apply le_antisymm
      · exact le_sSup ⟨MonoidHom.normal_ker π, IsPGroup.of_card (n := 1) (by rw [hker]; rfl)⟩
      · set e : OP ≃ Fin 6 := (Finite.equivFin OP).trans (finCongr card_OP) with he
        set π' := (Equiv.permCongrHom e).toMonoidHom.comp π with hπ'
        have hsurj' : Function.Surjective π' :=
          (Equiv.permCongrHom e).surjective.comp hsurj
        have hN := (CFSG.pCore_normal (p := 3) (G := ↥h.hyp.MVbar)).map π' hsurj'
        have hP : IsPGroup 3 ((CFSG.pCore 3 ↥h.hyp.MVbar).map π') :=
          (CFSG.pCore_isPGroup (p := 3)).map π'
        have hbot := no_normal_three (α := Fin 6) (by simp) hN hP
        intro x hx
        have hx' : π' x = 1 := by
          have : π' x ∈ (CFSG.pCore 3 ↥h.hyp.MVbar).map π' := ⟨x, hx, rfl⟩
          rw [hbot] at this
          exact this
        rw [MonoidHom.mem_ker]
        have : (Equiv.permCongrHom e) (π x) = 1 := hx'
        exact (MulEquiv.map_eq_one_iff _).1 this
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerP.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective π hsurj).trans
        (Equiv.permCongrHom ((Finite.equivFin OP).trans (finCongr card_OP))))⟩

end CFSG.Quasithin.H13.S127.Mod

end
