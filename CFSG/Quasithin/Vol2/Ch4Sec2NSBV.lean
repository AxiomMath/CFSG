module

public import CFSG.Quasithin.Vol2.Ch4Sec2NoSum2
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213C9

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L I H K : Subgroup G}

theorem conjClosure_perfectCore (c : Conf4212 G T M L I H K) :
    conjClosure (perfectCore (L ⊓ H)) (H ⊓ M) = perfectCore (L ⊓ H) :=
  le_antisymm (conjClosure_le fun _ hk z hz =>
      (Subgroup.mem_normalizer_iff.mp (c.LH_normal hk) z).mp hz)
    (le_conjClosure _ _)

theorem V_le_perfectCore (c : Conf4212 G T M L I H K) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ perfectCore (L ⊓ H) := by
  have h := c.hypC28.V_le
  rwa [conjClosure_perfectCore c] at h

theorem pCoreOf_I_le_normalizer (c : Conf4212 G T M L I H K) :
    pCoreOf 2 I ≤ Subgroup.normalizer (perfectCore (L ⊓ H) : Set G) :=
  fun r hr => c.LH_normal (c.hypC28.le_M hr)

theorem pCoreOf_perfectCore_le_pCoreOf_sup (c : Conf4212 G T M L I H K) :
    pCoreOf 2 (perfectCore (L ⊓ H)) ≤ pCoreOf 2 (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := by
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 _)
  refine sup_le (le_normalizer_pCoreOf 2 _) fun r hr => ?_
  exact normalizer_le_normalizer_pCoreOf 2 _ (pCoreOf_I_le_normalizer c hr)

theorem inf_pCoreOf_sup_le_pCoreOf (c : Conf4212 G T M L I H K) :
    perfectCore (L ⊓ H) ⊓ pCoreOf 2 (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ≤
      pCoreOf 2 (perfectCore (L ⊓ H)) := by
  set LH := perfectCore (L ⊓ H) with hLH
  set P := pCoreOf 2 (LH ⊔ pCoreOf 2 I) with hP
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hxP : x ∈ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hx)
  have hxP' := Subgroup.mem_normalizer_iff.mp hxP g
  have hxL := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) g
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hxP', hxL]

theorem V_le_pCoreOf (c : Conf4212 G T M L I H K) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤ pCoreOf 2 (perfectCore (L ⊓ H)) := by
  intro v hv
  have hvL := V_le_perfectCore c hv
  have hvZ := c.hypC28.V_center hv
  rw [conjClosure_perfectCore c] at hvZ
  have hvP : v ∈ pCoreOf 2 (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := (Subgroup.mem_inf.mp hvZ).1
  exact inf_pCoreOf_sup_le_pCoreOf c (Subgroup.mem_inf.mpr ⟨hvL, hvP⟩)

theorem V_le_centralizer_pCoreOf (c : Conf4212 G T M L I H K) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ≤
      Subgroup.centralizer (pCoreOf 2 (perfectCore (L ⊓ H)) : Set G) := by
  intro v hv
  have hvZ := c.hypC28.V_center hv
  rw [conjClosure_perfectCore c] at hvZ
  have hvC : v ∈ Subgroup.centralizer (pCoreOf 2 (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) : Set G) :=
    (Subgroup.mem_inf.mp hvZ).2
  rw [Subgroup.mem_centralizer_iff] at hvC ⊢
  intro x hx
  exact hvC x (pCoreOf_perfectCore_le_pCoreOf_sup c hx)

theorem eq_zero_of_mulVec_eq_self {m : ℕ} (hm : 2 ≤ m) (w : Fin m → ZMod 2)
    (hw : ∀ g : Matrix.GeneralLinearGroup (Fin m) (ZMod 2),
      (g : Matrix (Fin m) (Fin m) (ZMod 2)).mulVec w = w) : w = 0 := by
  funext j
  obtain ⟨i, hij⟩ : ∃ i : Fin m, i ≠ j := by
    by_contra hcon
    push_neg at hcon
    have h0 : (⟨0, by omega⟩ : Fin m) = j := hcon _
    have h1 : (⟨1, by omega⟩ : Fin m) = j := hcon _
    have h2 := h0.trans h1.symm
    simp [Fin.ext_iff] at h2
  set E : Matrix (Fin m) (Fin m) (ZMod 2) := Matrix.single i j 1 with hE
  have hEE : E * E = 0 := by simp [E, hij.symm]
  have h2 : E + E = 0 := by
    ext a b
    simp only [E, Matrix.add_apply, Matrix.single_apply, Matrix.zero_apply]
    split_ifs <;> decide
  have hunit : (1 + E) * (1 + E) = 1 := by
    calc (1 + E) * (1 + E) = 1 + (E + E) + E * E := by noncomm_ring
      _ = 1 := by rw [hEE, h2, add_zero, add_zero]
  let t : Matrix.GeneralLinearGroup (Fin m) (ZMod 2) := Units.mk (1 + E) (1 + E) hunit hunit
  have h := congrFun (hw t) i
  have hsw : (Matrix.mulVec (1 + E) w) i = w i + w j := by
    simp [E, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  change (Matrix.mulVec (1 + E) w) i = w i at h
  rw [hsw] at h
  have : w j = 0 := by simpa using h
  simpa using this

theorem card_V_of_isSum {A V : Subgroup G} {N : Subgroup ↥A} {m k : ℕ}
    (h : IsSumOfNaturalModules A V ⊥ N (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k) :
    Nat.card V = 2 ^ (m * k) := by
  obtain ⟨α, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : x ∈ β.ker := MonoidHom.mem_ker.mpr hx
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx'
    exact Subtype.ext (by simpa using hx')
  rw [Nat.card_congr (MulEquiv.ofBijective β ⟨hinj, hβs⟩).toEquiv]
  rw [Nat.card_congr (Multiplicative.ofAdd : (Fin k → Fin m → ZMod 2) ≃ _).symm]
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card,
    Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin, Nat.card_eq_fintype_card (α := Fin k),
    Fintype.card_fin, ← pow_mul]

theorem nine_le_card_V {A V : Subgroup G} {N : Subgroup ↥A} {m k : ℕ} (hm : 3 ≤ m) (hmk : m ≤ k)
    (h : IsSumOfNaturalModules A V ⊥ N (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k) :
    2 ^ 9 ≤ Nat.card V := by
  rw [card_V_of_isSum h]
  exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)

theorem V_inf_centralizer (c : Conf4212 G T M L I H K) (m k : ℕ) (hm : 2 ≤ m)
    (hsum : IsSumOfNaturalModules (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) ⁅reducedAggregate (L ⊔ T), L⁆ ⊥
      ((pCoreOf 2 I).subgroupOf (perfectCore (L ⊓ H) ⊔ pCoreOf 2 I))
      (CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2)) false k) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥ := by
  obtain ⟨α, hαs, hαk, -, -, β, -, hβk, hβe⟩ := hsum
  have hLR : perfectCore (L ⊓ H) ≤ Subgroup.normalizer (pCoreOf 2 I : Set G) :=
    c.perfectCore_le_normalizer_pCoreOf_I
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvV, hvc⟩ := Subgroup.mem_inf.mp hv
  set vv : ↥⁅reducedAggregate (L ⊔ T), L⁆ := ⟨v, hvV⟩ with hvv
  have hfix : ∀ i : Fin k, Multiplicative.toAdd (β vv) i = 0 := by
    intro i
    apply eq_zero_of_mulVec_eq_self hm
    intro g
    have hgΓ : g ∈ CFSG.Assembly.LowTwoRank.StatedSL m (ZMod 2) :=
      CFSG.Open.StatedAPI.mem_statedSL_zmod_two g
    obtain ⟨x, hx⟩ := hαs ⟨g, hgΓ⟩
    have hxmem : (x : G) ∈ (perfectCore (L ⊓ H) : Set G) * (pCoreOf 2 I : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLR]
      exact x.2
    obtain ⟨l, hl, r, hr, hlr⟩ := Set.mem_mul.mp hxmem
    have hlA : l ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_left hl
    have hrA : r ∈ perfectCore (L ⊓ H) ⊔ pCoreOf 2 I := Subgroup.mem_sup_right hr
    set a : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := ⟨l, hlA⟩ with ha
    set y : ↥(perfectCore (L ⊓ H) ⊔ pCoreOf 2 I) := ⟨r, hrA⟩ with hy
    have hyker : y ∈ α.ker := by
      rw [hαk]
      exact Subgroup.mem_subgroupOf.mpr hr
    have hxay : x = a * y := Subtype.ext (by simp [a, y, hlr.symm])
    have hαa : α a = ⟨g, hgΓ⟩ := by
      have h1 : α x = α a := by
        rw [hxay, map_mul, MonoidHom.mem_ker.mp hyker, mul_one]
      rw [← h1, hx]
    have hconj : (vv : G) = (a : G) * (vv : G) * (a : G)⁻¹ := by
      have hlv : l * v = v * l := (Subgroup.mem_centralizer_iff.mp hvc) l hl
      show v = l * v * l⁻¹
      rw [hlv, mul_assoc, mul_inv_cancel, mul_one]
    have h := hβe a vv vv hconj i
    have hgα : ((α a : Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))
        = (g : Matrix (Fin m) (Fin m) (ZMod 2)) := by
      rw [hαa]
    simp only [moduleAct, if_neg Bool.false_ne_true] at h
    rw [hgα] at h
    exact h.symm
  have hβ0 : β vv = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    exact hfix i
  have hvk : vv ∈ β.ker := MonoidHom.mem_ker.mpr hβ0
  rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hvk
  exact hvk

theorem V_inf_centerOf (c : Conf4212 G T M L I H K) (hA : ⁅reducedAggregate (L ⊔ T), L⁆ ⊓
      Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) = ⊥) :
    ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ centerOf K = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvV, hvZ⟩ := Subgroup.mem_inf.mp hv
  have hvK : v ∈ Subgroup.centralizer (K : Set G) := (Subgroup.mem_inf.mp hvZ).2
  have hvL : v ∈ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hvK ⊢
    intro h hh
    exact hvK h (c.LH_le hh)
  have : v ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) :=
    Subgroup.mem_inf.mpr ⟨hvV, hvL⟩
  rw [hA] at this
  exact this

theorem card_modO2_of_isPSL {m : ℕ} (hm : m = 3 ∨ m = 4) {X : Type} [Group X]
    (hX : IsPSL m 2 1 X) :
    (m = 3 ∧ Nat.card X = 168) ∨ (m = 4 ∧ Nat.card X = 20160) := by
  rw [C489.card_of_isPSL_two hX]
  rcases hm with rfl | rfl
  · exact Or.inl ⟨rfl, by decide⟩
  · exact Or.inr ⟨rfl, by decide⟩

end CFSG.Quasithin.H13.Ch4.NSB
