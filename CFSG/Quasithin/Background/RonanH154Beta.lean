module

public import CFSG.Quasithin.Background.RonanH154Gen
public import CFSG.Quasithin.Background.RonanH163Beta

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH154

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163
  CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def betaColsX : List ℕ := [17, 18, 20, 24, 30, 0, 30, 0, 6, 0]

@[expose] def betaLinX : (Fin 10 → ZMod 2) →+ (Fin 5 → ZMod 2) where
  toFun v i := ∑ j : Fin 10, v j * bvec 5 (betaColsX.getD j 0) i
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp [add_mul, Finset.sum_add_distrib]

theorem betaLinX_cols :
    ∀ j < 10, betaLinX (bvec 10 (2 ^ j)) = bvec 5 (betaColsX.getD j 0) := by
  decide +kernel

@[expose] def betaHomX : W10 →* G6.PermMod 5 := AddMonoidHom.toMultiplicative betaLinX

theorem betaHomX_toW (k : ℕ) : betaHomX (toW 10 k) = toW 5 (actM betaColsX k) :=
  congrArg Multiplicative.ofAdd (addHom_bvec betaLinX betaColsX rfl betaLinX_cols k)

@[expose] def betaT : ↥(⊤ : Subgroup W10) →* G6.PermMod 5 :=
  betaHomX.comp (⊤ : Subgroup W10).subtype

theorem betaColsX_lt : ∀ c ∈ betaColsX, c < 2 ^ 5 := by
  decide +kernel

theorem betaColsX_ker : ∀ m < 2 ^ 10, (actM betaColsX m = 0 ↔ m ∈ combos w6) := by
  decide +kernel

theorem betaColsX_range : ∀ y : Fin 5 → ZMod 2,
    (∑ i, y i = 0) ↔ ∃ m < 2 ^ 10, bvec 5 (actM betaColsX m) = y := by
  decide +kernel

@[expose] def sig1invTab : Fin 5 → Fin 5 := ![4, 0, 3, 1, 2]

@[expose] def sig2invTab : Fin 5 → Fin 5 := ![0, 1, 3, 2, 4]

theorem sig1inv_eq : ∀ i, sig1⁻¹ i = sig1invTab i := by decide +kernel

theorem sig2inv_eq : ∀ i, sig2⁻¹ i = sig2invTab i := by decide +kernel

theorem betaColsX_sig1_tab : ∀ m < 2 ^ 10,
    bvec 5 (actM betaColsX (act10 g1Arr m)) =
      fun i => bvec 5 (actM betaColsX m) (sig1invTab i) := by
  decide +kernel

theorem betaColsX_sig2_tab : ∀ m < 2 ^ 10,
    bvec 5 (actM betaColsX (act10 g2Arr m)) =
      fun i => bvec 5 (actM betaColsX m) (sig2invTab i) := by
  decide +kernel

theorem betaColsX_sig1 : ∀ m < 2 ^ 10,
    bvec 5 (actM betaColsX (act10 g1Arr m)) = fun i => bvec 5 (actM betaColsX m) (sig1⁻¹ i) := by
  intro m hm
  rw [betaColsX_sig1_tab m hm]
  funext i
  rw [sig1inv_eq]

theorem betaColsX_sig2 : ∀ m < 2 ^ 10,
    bvec 5 (actM betaColsX (act10 g2Arr m)) = fun i => bvec 5 (actM betaColsX m) (sig2⁻¹ i) := by
  intro m hm
  rw [betaColsX_sig2_tab m hm]
  funext i
  rw [sig2inv_eq]

theorem xorLin_ext_units {f g : ℕ → ℕ} (hf : XorLin f) (hg : XorLin g)
    (h : ∀ j < 10, f (2 ^ j) = g (2 ^ j)) : ∀ m < 2 ^ 10, f m = g m := by
  intro m hm
  rw [← actM_matOf hf 10 m hm, ← actM_matOf hg 10 m hm]
  congr 1
  unfold matOf
  exact List.map_congr_left (fun j hj => h j (List.mem_range.1 hj))

theorem betaColsX_nq2_units : ∀ u < 32, ∀ j < 10,
    actM betaColsX (act10 (nq2Arr u) (2 ^ j)) = actM betaColsX (2 ^ j) := by
  decide +kernel

theorem betaColsX_nq2 : ∀ u < 32, ∀ m < 2 ^ 10,
    actM betaColsX (act10 (nq2Arr u) m) = actM betaColsX m := by
  intro u hu
  exact xorLin_ext_units ((actM_xor betaColsX).comp (xorLin_act10 (nq2Arr u))) (actM_xor betaColsX)
    (betaColsX_nq2_units u hu)

theorem nq2_triv_X6_units : ∀ u < 32, ∀ j < 10,
    act10 (nq2Arr u) (2 ^ j) ^^^ 2 ^ j ∈ combos w6 := by
  decide +kernel

theorem bt_xor4 (A B x y : ℕ) : (A ^^^ B) ^^^ (x ^^^ y) = (A ^^^ x) ^^^ (B ^^^ y) := by
  rw [Nat.xor_assoc A B (x ^^^ y), ← Nat.xor_assoc B x y, Nat.xor_comm B x,
    Nat.xor_assoc x B y, ← Nat.xor_assoc A x (B ^^^ y)]

theorem nq2_triv_X6 : ∀ u < 32, ∀ m < 2 ^ 10, act10 (nq2Arr u) m ^^^ m ∈ combos w6 := by
  intro u hu
  refine mem_combos_of_xorLin (n := 10) (f := fun m => act10 (nq2Arr u) m ^^^ m) ?_
    (nq2_triv_X6_units u hu)
  intro a b
  show act10 (nq2Arr u) (a ^^^ b) ^^^ (a ^^^ b) =
    (act10 (nq2Arr u) a ^^^ a) ^^^ (act10 (nq2Arr u) b ^^^ b)
  rw [xorLin_act10 (nq2Arr u) a b]
  exact bt_xor4 _ _ _ _

theorem toW10_inv_c (k : ℕ) : (toW 10 k)⁻¹ = toW 10 k := by
  have h : toW 10 k * toW 10 k = 1 :=
    (toW_xor 10 k k).symm.trans (by rw [Nat.xor_self]; exact toW_zero 10)
  exact inv_eq_of_mul_eq_one_right h

@[expose] def pairFun5 (i j : Fin 5) : Fin 5 → ZMod 2 :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

theorem pairFun5_sum : ∀ i j : Fin 5, ∑ k, pairFun5 i j k = 0 := by decide +kernel

theorem core5_pair_aux : ∀ i t : Fin 5, (pairFun5 i (i + 1) t = pairFun5 i (i + 1) i ∧
    pairFun5 i (i + 2) t = pairFun5 i (i + 2) i) → t = i := by
  decide +kernel

theorem core5_faithful (σ : Equiv.Perm (Fin 5))
    (h : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 → ∀ i, y (σ⁻¹ i) = y i) : σ = 1 := by
  have h1 : ∀ i, σ⁻¹ i = i := fun i =>
    core5_pair_aux i (σ⁻¹ i) ⟨h _ (pairFun5_sum i (i + 1)) i, h _ (pairFun5_sum i (i + 2)) i⟩
  have h2 : σ⁻¹ = 1 := Equiv.ext fun i => h1 i
  exact inv_eq_one.1 h2

theorem betaHomX_range : betaT.range = G6.coreMod 5 := by
  ext x
  rw [MonoidHom.mem_range, G6.mem_coreMod]
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨m, hm, hmu⟩ := toW_surj 10 (u : W10)
    have h1 : betaT u = toW 5 (actM betaColsX m) := by
      change betaHomX (u : W10) = _
      rw [← hmu, betaHomX_toW]
    rw [h1]
    exact (betaColsX_range (bvec 5 (actM betaColsX m))).2 ⟨m, hm, rfl⟩
  · intro hx
    obtain ⟨m, hm, hmx⟩ := (betaColsX_range (Multiplicative.toAdd x)).1 hx
    refine ⟨⟨toW 10 m, Subgroup.mem_top _⟩, ?_⟩
    change betaHomX (toW 10 m) = x
    rw [betaHomX_toW]
    exact congrArg Multiplicative.ofAdd hmx

theorem betaHomX_eq_one_iff (w : W10) : betaHomX w = 1 ↔ w ∈ X6 := by
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
  rw [betaHomX_toW, toW_mem_X6_iff hm, ← betaColsX_ker m hm]
  constructor
  · intro h
    have hlt : actM betaColsX m < 2 ^ 5 := actM_lt betaColsX_lt m
    exact toW_inj hlt (by norm_num) (by rw [h, toW_zero])
  · intro h
    rw [h, toW_zero]

theorem betaT_eq_one (u : ↥(⊤ : Subgroup W10)) : betaT u = 1 ↔ (u : W10) ∈ X6 :=
  betaHomX_eq_one_iff (u : W10)

@[expose] def EqvX (g : P24) : Prop :=
  ∀ hg : g ∈ MY mog22plus Qstd, ∀ w : W10,
    betaHomX (Rc ⟨g, (mem_MY_iff.1 hg).1⟩ w) = G6.permAct 5 (piQ mog22plus ⟨g, hg⟩) (betaHomX w)

theorem eqvX_NQ2 {x : P24}
    (hx : x ∈ NQ2) : EqvX x := by
  intro hgM w
  have h1 : (⟨x, hgM⟩ : ↥(MY mog22plus Qstd)) ∈ (piQ mog22plus).ker := by
    rw [ker_piQ_L2]
    exact Subgroup.mem_subgroupOf.2 hx
  have hpiQ : piQ mog22plus ⟨x, hgM⟩ = 1 := MonoidHom.mem_ker.1 h1
  obtain ⟨u, hu⟩ := mem_NQ2_iff.1 hx
  have hR : Rc ⟨x, (mem_MY_iff.1 hgM).1⟩ = Rc (nq2Elt u) :=
    congrArg Rc (Subtype.ext hu)
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
  rw [hpiQ, hR, Rc_nq2, betaHomX_toW, betaHomX_toW, betaColsX_nq2 u.1 u.2 m hm, map_one,
    MulAut.one_apply]

theorem eqvX_g1 :
    EqvX g1Perm := by
  intro hgM w
  have hpiQ : piQ mog22plus ⟨g1Perm, hgM⟩ = sig1 := piQ_eq_of_smul _ sig1 g1_smul_Zq
  have hR : Rc ⟨g1Perm, (mem_MY_iff.1 hgM).1⟩ = Rc g1Elt := rfl
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
  rw [hpiQ, hR, Rc_g1, betaHomX_toW, betaHomX_toW]
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  exact congrFun (betaColsX_sig1 m hm) i

theorem eqvX_g2 :
    EqvX g2Perm := by
  intro hgM w
  have hpiQ : piQ mog22plus ⟨g2Perm, hgM⟩ = sig2 := piQ_eq_of_smul _ sig2 g2_smul_Zq
  have hR : Rc ⟨g2Perm, (mem_MY_iff.1 hgM).1⟩ = Rc g2Elt := rfl
  obtain ⟨m, hm, rfl⟩ := toW_surj 10 w
  rw [hpiQ, hR, Rc_g2, betaHomX_toW, betaHomX_toW]
  apply Multiplicative.toAdd.injective
  funext i
  rw [G6.permAct_apply]
  exact congrFun (betaColsX_sig2 m hm) i

theorem eqvX_one : EqvX 1 := by
  intro hg w
  have h1 : Rc ⟨1, (mem_MY_iff.1 hg).1⟩ = 1 := map_one Rc
  have h2 : piQ mog22plus ⟨1, hg⟩ = 1 := map_one (piQ mog22plus)
  rw [h1, h2, map_one, MulAut.one_apply, MulAut.one_apply]

theorem eqvX_mul {x y : P24}
    (hx : x ∈ MY mog22plus Qstd) (hy : y ∈ MY mog22plus Qstd) (ihx : EqvX x) (ihy : EqvX y) :
    EqvX (x * y) := by
  intro hxy w
  have hx1 : x ∈ mog22plus := (mem_MY_iff.1 hx).1
  have hy1 : y ∈ mog22plus := (mem_MY_iff.1 hy).1
  have hab : (⟨x * y, (mem_MY_iff.1 hxy).1⟩ : ↥mog22plus) = ⟨x, hx1⟩ * ⟨y, hy1⟩ := rfl
  have hab' : (⟨x * y, hxy⟩ : ↥(MY mog22plus Qstd)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [hab, hab', map_mul Rc ⟨x, hx1⟩ ⟨y, hy1⟩,
    MulAut.mul_apply W10 (Rc ⟨x, hx1⟩) (Rc ⟨y, hy1⟩) w,
    map_mul (piQ mog22plus) ⟨x, hx⟩ ⟨y, hy⟩,
    map_mul (G6.permAct 5) (piQ mog22plus ⟨x, hx⟩) (piQ mog22plus ⟨y, hy⟩),
    MulAut.mul_apply (G6.PermMod 5) (G6.permAct 5 (piQ mog22plus ⟨x, hx⟩))
      (G6.permAct 5 (piQ mog22plus ⟨y, hy⟩)) (betaHomX w),
    ihx hx _, ihy hy w]

theorem eqvX_inv {x : P24}
    (hx : x ∈ MY mog22plus Qstd) (ihx : EqvX x) : EqvX x⁻¹ := by
  intro hgM w
  have hx1 : x ∈ mog22plus := (mem_MY_iff.1 hx).1
  have hi1 : x⁻¹ ∈ mog22plus := (mem_MY_iff.1 hgM).1
  have h1 := ihx hx (Rc ⟨x⁻¹, hi1⟩ w)
  have hm : (⟨x, hx1⟩ : ↥mog22plus) * ⟨x⁻¹, hi1⟩ = 1 := Subtype.ext (mul_inv_cancel x)
  have hm1 : Rc ⟨x, hx1⟩ * Rc ⟨x⁻¹, hi1⟩ = 1 := by
    rw [← map_mul Rc ⟨x, hx1⟩ ⟨x⁻¹, hi1⟩, hm, map_one Rc]
  have h2 : Rc ⟨x, hx1⟩ (Rc ⟨x⁻¹, hi1⟩ w) = w :=
    (MulAut.mul_apply W10 (Rc ⟨x, hx1⟩) (Rc ⟨x⁻¹, hi1⟩) w).symm.trans
      ((congrArg (fun f : MulAut W10 => f w) hm1).trans (MulAut.one_apply W10 w))
  have h3 : betaHomX w =
      G6.permAct 5 (piQ mog22plus ⟨x, hx⟩) (betaHomX (Rc ⟨x⁻¹, hi1⟩ w)) :=
    (congrArg betaHomX h2.symm).trans h1
  exact perm_inv_eq hx hgM _ _ (permAct_inv_apply hx _ _ h3)

theorem eqvX_closure :
    ∀ g ∈ Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}), EqvX g := by
  have hMY : Subgroup.closure ((NQ2 : Set P24) ∪ {g1Perm, g2Perm}) ≤ MY mog22plus Qstd := by
    rw [Subgroup.closure_le]
    rintro x (hx | rfl | rfl)
    · exact NQ2_le_MY_Q hx
    · exact g1Perm_mem_MY g1Perm_mem_mog22plus
    · exact g2Perm_mem_MY g2Perm_mem_mog22plus
  intro g hg
  refine Subgroup.closure_induction (p := fun g _ => EqvX g) ?_ ?_ ?_ ?_ hg
  · rintro x (hx | rfl | rfl)
    · exact eqvX_NQ2 hx
    · exact eqvX_g1
    · exact eqvX_g2
  · exact eqvX_one
  · intro x y hx hy ihx ihy
    exact eqvX_mul (hMY hx) (hMY hy) ihx ihy
  · intro x hx ihx
    exact eqvX_inv (hMY hx) ihx

theorem betaHomX_Rc {g : P24}
    (hg : g ∈ MY mog22plus Qstd) (w : W10) :
    betaHomX (Rc ⟨g, (mem_MY_iff.1 hg).1⟩ w) =
      G6.permAct 5 (piQ mog22plus ⟨g, hg⟩) (betaHomX w) :=
  eqvX_closure g (MQ_le_closure hg) hg w

theorem induces_std_X :
    InducesOnSub (rImg Rc (MY mog22plus Qstd)) ⊤ X6 (G6.PermMod 5) (G6.coreMod 5)
      (G6.permAct 5).range := by
  unfold InducesOnSub
  refine ⟨le_top, fun g _ u _ => Subgroup.mem_top _, fun g hg z hz => inv_X6 g hg z hz,
    betaT, betaHomX_range, betaT_eq_one, ?_, ?_⟩
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
    have hxM : (x : P24) ∈ MY mog22plus Qstd := Subgroup.mem_subgroupOf.1 hx
    refine ⟨G6.permAct 5 (piQ mog22plus ⟨(x : P24), hxM⟩), MonoidHom.mem_range.2 ⟨_, rfl⟩, ?_⟩
    intro u u' huu'
    change betaHomX (u' : W10) =
      G6.permAct 5 (piQ mog22plus ⟨(x : P24), hxM⟩) (betaHomX (u : W10))
    rw [huu']
    exact betaHomX_Rc hxM (u : W10)
  · intro γ hγ
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.1 hγ
    have hσ : σ ∈ (piQ mog22plus).range := by
      rw [piQ_range_top_L2]
      exact Subgroup.mem_top σ
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hσ
    refine ⟨Rc ⟨(y : P24), (mem_MY_iff.1 y.2).1⟩,
      Subgroup.mem_map_of_mem Rc (Subgroup.mem_subgroupOf.2 y.2), ?_⟩
    intro u u' huu'
    change betaHomX (u' : W10) = G6.permAct 5 (piQ mog22plus y) (betaHomX (u : W10))
    rw [huu']
    exact betaHomX_Rc y.2 (u : W10)

theorem kernel_std_X :
    ∀ g : ↥mog22plus, (g : P24) ∈ MY mog22plus Qstd →
      ((∀ x : W10, Rc g x * x⁻¹ ∈ X6) ↔ (g : P24) ∈ KY mog22plus Qstd) := by
  intro g hgM
  rw [KY_Q_L2]
  constructor
  · intro hall
    set σ : Equiv.Perm (Fin 5) := piQ mog22plus ⟨(g : P24), hgM⟩ with hσ
    have hfix : ∀ y : Fin 5 → ZMod 2, ∑ i, y i = 0 → ∀ i, y (σ⁻¹ i) = y i := by
      intro y hy i
      have hyc : Multiplicative.ofAdd y ∈ G6.coreMod 5 := hy
      rw [← betaHomX_range] at hyc
      obtain ⟨u, hu⟩ := MonoidHom.mem_range.1 hyc
      have hu' : betaHomX (u : W10) = Multiplicative.ofAdd y := hu
      have h1 := betaHomX_Rc hgM (u : W10)
      have hW : ∀ x : W10, x⁻¹ = x := fun x => by
        obtain ⟨m, -, rfl⟩ := toW_surj 10 x
        exact toW10_inv_c m
      have h2 : betaHomX (Rc g (u : W10) * (u : W10)) = 1 := by
        have h2' := (betaHomX_eq_one_iff _).2 (hall (u : W10))
        rwa [hW] at h2'
      rw [map_mul] at h2
      have h4 := congrFun (congrArg Multiplicative.toAdd h2) i
      simp only [toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply] at h4
      have h5 := zmod2_eq_of_add h4
      have h1' : betaHomX (Rc g (u : W10)) =
          G6.permAct 5 (piQ mog22plus ⟨(g : P24), hgM⟩) (betaHomX (u : W10)) := h1
      rw [h1', hu', G6.permAct_apply] at h5
      exact h5
    have hσ1 : σ = 1 := core5_faithful σ hfix
    have hker : (⟨(g : P24), hgM⟩ : ↥(MY mog22plus Qstd)) ∈ (piQ mog22plus).ker :=
      MonoidHom.mem_ker.2 hσ1
    rw [ker_piQ_L2, Subgroup.mem_subgroupOf] at hker
    exact hker
  · intro hg x
    obtain ⟨u, hu⟩ := mem_NQ2_iff.1 hg
    have hR : Rc g = Rc (nq2Elt u) := congrArg Rc (Subtype.ext hu)
    obtain ⟨m, hm, rfl⟩ := toW_surj 10 x
    rw [hR, Rc_nq2, toW10_inv_c, ← toW_xor]
    exact toW_mem_maskSub (n := 10) (nq2_triv_X6 u.1 u.2 m hm)

end CFSG.Quasithin.RonanH154
