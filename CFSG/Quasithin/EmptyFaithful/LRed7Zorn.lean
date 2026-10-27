module

public import CFSG.Quasithin.EmptyFaithful.LRed7Abs
public import CFSG.Quasithin.EmptyFaithful.LRed6G2
public import CFSG.Quasithin.Background.JonesParshallG2Two
public import CFSG.Quasithin.Background.JonesParshallG2Derived
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57G2Eq
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.FFC4Tr2

public section

namespace CFSG.Quasithin.LRed7

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open
open scoped Matrix commutatorElement

local notation "Amb" => quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)

@[expose] def code (w : Ix3 → ZMod 2) : Nat :=
  (w (.inl 0)).val + 2 * (w (.inl 1)).val + 4 * (w (.inl 2)).val + 8 * (w (.inr 0)).val +
    16 * (w (.inr 1)).val + 32 * (w (.inr 2)).val

theorem code_lt (w : Ix3 → ZMod 2) : code w < 64 := by
  have h0 := ZMod.val_lt (w (.inl 0))
  have h1 := ZMod.val_lt (w (.inl 1))
  have h2 := ZMod.val_lt (w (.inl 2))
  have h3 := ZMod.val_lt (w (.inr 0))
  have h4 := ZMod.val_lt (w (.inr 1))
  have h5 := ZMod.val_lt (w (.inr 2))
  unfold code
  omega

theorem code_inj {w w' : Ix3 → ZMod 2} (h : code w = code w') : w = w' := by
  have h0 := ZMod.val_lt (w (.inl 0))
  have h1 := ZMod.val_lt (w (.inl 1))
  have h2 := ZMod.val_lt (w (.inl 2))
  have h3 := ZMod.val_lt (w (.inr 0))
  have h4 := ZMod.val_lt (w (.inr 1))
  have h5 := ZMod.val_lt (w (.inr 2))
  have h0' := ZMod.val_lt (w' (.inl 0))
  have h1' := ZMod.val_lt (w' (.inl 1))
  have h2' := ZMod.val_lt (w' (.inl 2))
  have h3' := ZMod.val_lt (w' (.inr 0))
  have h4' := ZMod.val_lt (w' (.inr 1))
  have h5' := ZMod.val_lt (w' (.inr 2))
  unfold code at h
  have e0 : (w (.inl 0)).val = (w' (.inl 0)).val := by omega
  have e1 : (w (.inl 1)).val = (w' (.inl 1)).val := by omega
  have e2 : (w (.inl 2)).val = (w' (.inl 2)).val := by omega
  have e3 : (w (.inr 0)).val = (w' (.inr 0)).val := by omega
  have e4 : (w (.inr 1)).val = (w' (.inr 1)).val := by omega
  have e5 : (w (.inr 2)).val = (w' (.inr 2)).val := by omega
  funext i
  rcases i with i | i <;> fin_cases i
  · exact ZMod.val_injective 2 e0
  · exact ZMod.val_injective 2 e1
  · exact ZMod.val_injective 2 e2
  · exact ZMod.val_injective 2 e3
  · exact ZMod.val_injective 2 e4
  · exact ZMod.val_injective 2 e5

theorem code_zero : code (0 : Ix3 → ZMod 2) = 0 := rfl

@[expose] def A6 : Matrix Ix3 Ix3 (ZMod 2) := matA2.submatrix embQ embQ

@[expose] def B6 : Matrix Ix3 Ix3 (ZMod 2) := matB2.submatrix embQ embQ

@[expose] def applyM (cols : List Nat) (c : Nat) : Nat :=
  (List.range 6).foldl (fun acc j => if c.testBit j then acc ^^^ cols.getD j 0 else acc) 0

@[expose] def colsA : List Nat := [19, 47, 57, 26, 15, 50]

@[expose] def colsB : List Nat := [1, 5, 7, 40, 48, 16]

theorem code_mulVec_A : ∀ a b c d e f : ZMod 2,
    code (A6 *ᵥ q6 a b c d e f) = applyM colsA (code (q6 a b c d e f)) := by
  decide +kernel

theorem code_mulVec_B : ∀ a b c d e f : ZMod 2,
    code (B6 *ᵥ q6 a b c d e f) = applyM colsB (code (q6 a b c d e f)) := by
  decide +kernel


@[expose] def wordTable : List (List Bool) :=
  [[],
  [],
  [false, true, false, true, true, false, false],
  [true, true, false, true, false],
  [false, true, false],
  [false, true, false, true, false],
  [true, false, true, false, true, false],
  [true, false, true, false],
  [true, false, false, true, true, false],
  [true, false, false, true, false],
  [false, true, true, false, false],
  [false, true, false, false],
  [false, false, true, false, true, true, false],
  [false, true, false, false, true, false, true, false],
  [false, true, false, true, true, false],
  [true, false, true, true, false, true, false],
  [true, false, true, false, false, true, false, false],
  [false, true, false, true, false, false],
  [true, false, false, true, false, false],
  [false],
  [true, true, false, true, true, false],
  [true, false, true, true, false, true, false, false],
  [false, true, false, true, false, true, false],
  [true, true, false, false],
  [false, true, false, false, true, false, false, true, false, false],
  [false, false, true, false, true, false, true, false],
  [false, true, false, false, true, true, false],
  [false, false, true, true, false, false, true, false],
  [false, false, true, false, true, false, false],
  [false, false, true, true, false, true, false, false],
  [false, false, true, true, false, true, false],
  [true, false, false, true, false, true, false, false],
  [false, true, false, false, true, false, false],
  [true, true, false, true, false, true, false, false],
  [false, true, true, false, true, false, false],
  [true, false, true, true, false],
  [true, false, false],
  [true, false, false, true, false, false, true, false, false],
  [false, false, true, false, false],
  [true, true, false],
  [true, true, false, false, true, true, false],
  [true, true, false, false, true, false],
  [false, false, true, false, true, false],
  [true, true, false, true, true, false, true, false],
  [true, false, true, false, false],
  [true, false, true, true, false, false],
  [false, true, false, true, false, true, false, false],
  [false, false, true, false, true, true, false, false],
  [true, true, false, true, false, false, true, false, false],
  [true, false, true, false, true, false, false],
  [false, false, true, false, false, true, false, false],
  [false, false],
  [true, false],
  [false, false, true, true, false, false],
  [false, true, true, false, true, true, false],
  [false, true, true, false],
  [false, false, true, true, false],
  [false, false, true, false],
  [false, false, true, false, false, true, true, false],
  [false, true, true, false, false, true, false],
  [false, true, true, false, true, false],
  [true, false, false, true, false, true, false],
  [true, true, false, true, true, false, false],
  [true, true, false, true, false, false]]

@[expose] def applyW (ws : List Bool) : Nat :=
  ws.foldr (fun b acc => if b then applyM colsB acc else applyM colsA acc) 1

theorem wordTable_spec : ∀ c : Fin 64, 0 < c.val → applyW (wordTable.getD c.val []) = c.val := by
  decide +kernel

abbrev M2 : Type := Multiplicative (Ix3 → ZMod 2)

theorem subG2_le_cayley :
    subG2 ≤ cayleyGroup (ZMod 2) := by
  rw [← g2Two_commutator_eq]
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact (cayleyGroup (ZMod 2)).mul_mem ((cayleyGroup (ZMod 2)).mul_mem
    ((cayleyGroup (ZMod 2)).mul_mem ha hb) ((cayleyGroup (ZMod 2)).inv_mem ha))
    ((cayleyGroup (ZMod 2)).inv_mem hb)

theorem code_mulVec_A' (v : Ix3 → ZMod 2) : code (A6 *ᵥ v) = applyM colsA (code v) := by
  have h := code_mulVec_A (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 0)) (v (.inr 1))
    (v (.inr 2))
  rw [← q6_eta v] at h
  exact h

theorem code_mulVec_B' (v : Ix3 → ZMod 2) : code (B6 *ᵥ v) = applyM colsB (code v) := by
  have h := code_mulVec_B (v (.inl 0)) (v (.inl 1)) (v (.inl 2)) (v (.inr 0)) (v (.inr 1))
    (v (.inr 2))
  rw [← q6_eta v] at h
  exact h

@[expose] def w₀ : Ix3 → ZMod 2 := q6 1 0 0 0 0 0

theorem code_w₀ : code w₀ = 1 := by decide +kernel

theorem card_M2 : Nat.card M2 = 2 ^ 6 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := Ix3),
    Fintype.card_sum, Fintype.card_fin]
  simp

theorem sq_M2 (m : M2) : m ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  have h2 : ∀ x : ZMod 2, x + x = 0 := by decide
  simp only [two_nsmul, Pi.add_apply, Pi.zero_apply]
  exact h2 _

@[expose] def PH : Multiplicative (quasithinZorn (ZMod 2)) →* M2 where
  toFun x := Multiplicative.ofAdd (zP (Multiplicative.toAdd x))
  map_one' := by
    change Multiplicative.ofAdd (zP (0 : quasithinZorn (ZMod 2))) = 1
    rw [← zmk_zero, zP_zmk, q6_zero]
    rfl
  map_mul' x y := by
    change Multiplicative.ofAdd (zP (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [zP_add]
    rfl

theorem PH_apply (x : Multiplicative (quasithinZorn (ZMod 2))) :
    PH x = Multiplicative.ofAdd (zP (Multiplicative.toAdd x)) := rfl

theorem PH_eq_one_of_mem {r : Multiplicative (quasithinZorn (ZMod 2))} (hr : r ∈ zornR (ZMod 2)) :
    PH r = 1 := by
  obtain ⟨c, hc⟩ := hr
  change Multiplicative.ofAdd (zP (Multiplicative.toAdd r)) = 1
  rw [hc]
  change Multiplicative.ofAdd (zP (zmk c 0 0 0 0 0 0 c)) = 1
  rw [zP_zmk, q6_zero]
  rfl

theorem mem_zornR_of_PH {x : Multiplicative (quasithinZorn (ZMod 2))} (hx : x ∈ zornO0 (ZMod 2))
    (h : PH x = 1) : x ∈ zornR (ZMod 2) :=
  zornPHom_eq_one (x := ⟨x, hx⟩) h

theorem card_map_PH {Wm : Subgroup (Multiplicative (quasithinZorn (ZMod 2)))}
    (hWO : Wm ≤ zornO0 (ZMod 2)) (hRW : zornR (ZMod 2) ≤ Wm) (hcard : Nat.card Wm = 32) :
    Nat.card (Wm.map PH) = 16 := by
  set f : ↥Wm →* M2 := PH.comp Wm.subtype with hf
  have hrange : Wm.map PH = f.range := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker = (zornR (ZMod 2)).subgroupOf Wm := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact mem_zornR_of_PH (hWO m.2) h
    · intro h
      exact PH_eq_one_of_mem h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker, hcard] at h1
  have h2 : Nat.card ↥((zornR (ZMod 2)).subgroupOf Wm) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRW).toEquiv, LRed6.card_zornR]
    simp
  rw [h2] at h1
  rw [hrange]
  omega


@[expose] noncomputable def actEnd : U33G →* AddMonoid.End (Ix3 → ZMod 2) :=
  g2Act.comp ((Subgroup.inclusion subG2_le_cayley).comp u33EquivSubG2.toMonoidHom)

theorem actEnd_mul (g h : U33G) (w : Ix3 → ZMod 2) : actEnd (g * h) w = actEnd g (actEnd h w) := by
  rw [map_mul]
  rfl

theorem actEnd_one (w : Ix3 → ZMod 2) : actEnd 1 w = w := by
  rw [map_one]
  rfl

@[expose] noncomputable def phi : U33G →* MulAut M2 where
  toFun g :=
    { toFun := fun w => Multiplicative.ofAdd (actEnd g (Multiplicative.toAdd w))
      invFun := fun w => Multiplicative.ofAdd (actEnd g⁻¹ (Multiplicative.toAdd w))
      left_inv := fun w => by
        show Multiplicative.ofAdd (actEnd g⁻¹ (actEnd g (Multiplicative.toAdd w))) = w
        rw [← actEnd_mul, inv_mul_cancel, actEnd_one]
        rfl
      right_inv := fun w => by
        show Multiplicative.ofAdd (actEnd g (actEnd g⁻¹ (Multiplicative.toAdd w))) = w
        rw [← actEnd_mul, mul_inv_cancel, actEnd_one]
        rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (actEnd g (Multiplicative.toAdd a + Multiplicative.toAdd b)) = _
        rw [map_add]
        rfl }
  map_one' := MulEquiv.ext fun w => by
    show Multiplicative.ofAdd (actEnd 1 (Multiplicative.toAdd w)) = w
    rw [actEnd_one]
    rfl
  map_mul' g h := MulEquiv.ext fun w => by
    show Multiplicative.ofAdd (actEnd (g * h) (Multiplicative.toAdd w)) =
      Multiplicative.ofAdd (actEnd g (Multiplicative.toAdd
        (Multiplicative.ofAdd (actEnd h (Multiplicative.toAdd w)))))
    rw [actEnd_mul]
    rfl

theorem phi_apply (g : U33G) (w : M2) :
    phi g w = Multiplicative.ofAdd (actEnd g (Multiplicative.toAdd w)) := rfl


@[expose] noncomputable def ga : U33G := u33EquivSubG2.symm ⟨(g2a : Amb), ab_mem_subG2 0⟩

@[expose] noncomputable def gb : U33G := u33EquivSubG2.symm ⟨(g2b : Amb), ab_mem_subG2 1⟩

theorem actEnd_ga (w : Ix3 → ZMod 2) : actEnd ga w = A6 *ᵥ w := by
  show g2Act (Subgroup.inclusion subG2_le_cayley (u33EquivSubG2 (u33EquivSubG2.symm
    ⟨(g2a : Amb), ab_mem_subG2 0⟩))) w = _
  rw [MulEquiv.apply_symm_apply]
  have : Subgroup.inclusion subG2_le_cayley ⟨(g2a : Amb), ab_mem_subG2 0⟩ = g2a := Subtype.ext rfl
  rw [this, g2Act_eq_mulVec, cmat_g2a]
  rfl

theorem actEnd_gb (w : Ix3 → ZMod 2) : actEnd gb w = B6 *ᵥ w := by
  show g2Act (Subgroup.inclusion subG2_le_cayley (u33EquivSubG2 (u33EquivSubG2.symm
    ⟨(g2b : Amb), ab_mem_subG2 1⟩))) w = _
  rw [MulEquiv.apply_symm_apply]
  have : Subgroup.inclusion subG2_le_cayley ⟨(g2b : Amb), ab_mem_subG2 1⟩ = g2b := Subtype.ext rfl
  rw [this, g2Act_eq_mulVec, cmat_g2b]
  rfl

theorem reach_mem : ∀ ws : List Bool, ∃ g : U33G, code (actEnd g w₀) = applyW ws := by
  intro ws
  induction ws with
  | nil => exact ⟨1, by rw [actEnd_one]; exact code_w₀⟩
  | cons b ws ih =>
    obtain ⟨g, hg⟩ := ih
    cases b
    · refine ⟨ga * g, ?_⟩
      rw [actEnd_mul, actEnd_ga, code_mulVec_A', hg]
      simp [applyW]
    · refine ⟨gb * g, ?_⟩
      rw [actEnd_mul, actEnd_gb, code_mulVec_B', hg]
      simp [applyW]

theorem trans_nonzero : ∀ m : M2, m ≠ 1 → ∃ g : U33G, phi g (Multiplicative.ofAdd w₀) = m := by
  intro m hm
  have hw : Multiplicative.toAdd m ≠ 0 := fun h => hm (by
    apply Multiplicative.toAdd.injective
    rw [h, toAdd_one])
  have hc0 : 0 < code (Multiplicative.toAdd m) := by
    by_contra h
    have : code (Multiplicative.toAdd m) = 0 := by omega
    exact hw (code_inj (this.trans code_zero.symm))
  have hspec := wordTable_spec ⟨code (Multiplicative.toAdd m), code_lt _⟩ hc0
  obtain ⟨g, hg⟩ := reach_mem (wordTable.getD (code (Multiplicative.toAdd m)) [])
  refine ⟨g, ?_⟩
  rw [phi_apply, toAdd_ofAdd]
  have h1 : code (actEnd g w₀) = code (Multiplicative.toAdd m) := hg.trans hspec
  exact (congrArg Multiplicative.ofAdd (code_inj h1)).trans (ofAdd_toAdd m)

theorem hirr : ∀ N : Subgroup M2, (∀ g : U33G, ∀ n ∈ N, phi g n ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro N hN
  by_cases hb : N = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hb
    have hnm : (n : M2) ≠ 1 := fun h => hn1 (Subtype.ext h)
    obtain ⟨g, hg⟩ := trans_nonzero n hnm
    have hw₀ : Multiplicative.ofAdd w₀ ∈ N := by
      have := hN g⁻¹ _ n.2
      rw [← hg, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one] at this
      exact this
    rw [eq_top_iff]
    intro m _
    by_cases hm1 : m = 1
    · rw [hm1]; exact N.one_mem
    · obtain ⟨g', hg'⟩ := trans_nonzero m hm1
      rw [← hg']
      exact hN g' _ hw₀

theorem exists_fixed_T : ∃ z : M2, z ≠ 1 ∧ ∀ g ∈ u33Data.T, phi g z = z := by
  classical
  let : MulAction ↥u33Data.T M2 := MulAction.compHom M2 (phi.comp u33Data.T.subtype)
  have hp : IsPGroup 2 ↥u33Data.T := u33_syl.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfix1 : (1 : M2) ∈ MulAction.fixedPoints ↥u33Data.T M2 := fun g => map_one (phi g)
  have h2 : 2 ∣ Nat.card M2 := by rw [card_M2]; norm_num
  have : Finite M2 := Nat.finite_of_card_ne_zero (by rw [card_M2]; norm_num)
  obtain ⟨z, hz, hne⟩ := hp.exists_fixed_point_of_prime_dvd_card_of_fixed_point M2 h2 hfix1
  exact ⟨z, fun h => hne h.symm, fun g hg => hz ⟨g, hg⟩⟩


theorem phi_PH {g : U33G} {m : Multiplicative (quasithinZorn (ZMod 2))} (hm : m ∈ zornO0 (ZMod 2)) :
    phi g (PH m) = PH (Multiplicative.ofAdd
      (((u33EquivSubG2 g : ↥subG2) : Amb) (Multiplicative.toAdd m))) := by
  rw [phi_apply, PH_apply, PH_apply, toAdd_ofAdd]
  congr 1
  have h1 : cayleyTr (Multiplicative.toAdd m) = 0 := hm
  show g2Act (Subgroup.inclusion subG2_le_cayley (u33EquivSubG2 g)) (zP (Multiplicative.toAdd m)) = _
  rw [g2Act_apply, ← g2_zP_apply _ _ h1]
  rfl

theorem g2FixBound_two (Wm : Subgroup (Multiplicative (quasithinZorn (ZMod 2))))
    (hWO : Wm ≤ zornO0 (ZMod 2)) (hRW : zornR (ZMod 2) ≤ Wm) (hcard : Nat.card Wm = 32) :
    Nat.card {γ : ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ //
      ∀ m ∈ Wm, zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ γ m * m⁻¹ ∈
        zornR (ZMod 2)} ≤ 2 := by
  have hG : quasithinG2 (ZMod 2) = cayleyGroup (ZMod 2) :=
    CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup
  have hc : ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ = subG2 := by
    rw [hG, g2Two_commutator_eq]
  obtain ⟨z, hz, hzT⟩ := exists_fixed_T
  have hbound := u33_fixbound card_M2 phi hirr hz (sq_M2 z) hzT (Wm.map PH)
    (card_map_PH hWO hRW hcard)
  have : Finite U33G := finite_u33
  refine le_trans ?_ hbound
  refine Nat.card_le_card_of_injective
    (fun γ => ⟨u33EquivSubG2.symm ⟨(γ.1 : Amb), hc ▸ γ.1.2⟩, ?_⟩) ?_
  · intro w hw
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hw
    rw [phi_PH (hWO hm), MulEquiv.apply_symm_apply]
    have hr := γ.2 m hm
    have h1 : PH (zornAct ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ γ.1 m * m⁻¹) = 1 :=
      PH_eq_one_of_mem hr
    have hinv : PH m⁻¹ = (PH m)⁻¹ := map_inv PH m
    rw [map_mul, hinv] at h1
    exact mul_inv_eq_one.mp h1
  · intro a b hab
    have h1 := congrArg (fun x : {g : U33G // ∀ w ∈ Wm.map PH, phi g w = w} => x.1) hab
    simp only at h1
    have h2 := u33EquivSubG2.symm.injective h1
    have h3 : (a.1 : Amb) = (b.1 : Amb) := by
      have h4 := congrArg Subtype.val h2
      exact h4
    exact Subtype.ext (Subtype.ext h3)

end CFSG.Quasithin.LRed7
