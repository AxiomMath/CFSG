module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

public section

namespace CFSG

namespace FiveTransitive.AbelianNormalObstruction

theorem false_of_regular_normal_subgroup
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (hcard : 5 ≤ Fintype.card X)
    (h4 : MulAction.IsMultiplyPretransitive G X 4)
    (N : Subgroup G) [N.Normal]
    [IsCancelSMul N X] [MulAction.IsPretransitive N X] : False := by
  classical
  have hX5 : 5 ≤ Nat.card X := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  let _ : MulAction.IsMultiplyPretransitive G X 4 := h4
  have h3 : MulAction.IsMultiplyPretransitive G X 3 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := G) (α := X) (m := 3) (n := 4) (by omega) (by omega)
  have hNtrans : MulAction.IsPretransitive N X := inferInstance
  have hfree : ∀ (a : N) (x : X), a • x = x → a = 1 := by
    intro a x hax
    apply IsCancelSMul.right_cancel a 1 x
    simpa only [one_smul] using hax
  let _ : Nontrivial X := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Nontrivial N := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    obtain ⟨g, hg⟩ := hNtrans.exists_smul_eq x y
    refine ⟨⟨g, 1, ?_⟩⟩
    intro hg1
    apply hxy
    simpa only [hg1, one_smul] using hg
  let x : X := Classical.choice (Fintype.card_pos_iff.mp (by omega))
  have hinv : ∀ a : N, a⁻¹ = a := by
    intro a
    by_cases ha : a = 1
    · simp [ha]
    let y : X := a • x
    let z : X := a⁻¹ • x
    have hyx : y ≠ x := by
      intro hyx
      exact ha (hfree a x hyx)
    have hzx : z ≠ x := by
      intro hzx
      have : a⁻¹ = (1 : N) := hfree a⁻¹ x hzx
      exact ha (inv_eq_one.mp this)
    by_contra hne
    have hzy : z ≠ y := by
      intro hzy
      apply hne
      exact IsCancelSMul.right_cancel a⁻¹ a x hzy
    obtain ⟨w, hw⟩ :=
      Finset.exists_not_mem_of_card_lt_enatCard
        (s := {x, y, z}) (by
          have hx_yz : x ∉ ({y, z} : Finset X) := by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hyx.symm, hzx.symm⟩
          have hy_z : y ∉ ({z} : Finset X) := by
            simpa only [Finset.mem_singleton] using hzy.symm
          have hxyz : ({x, y, z} : Finset X).card = 3 := by
            rw [Finset.card_insert_of_notMem hx_yz,
              Finset.card_insert_of_notMem hy_z]
            simp
          rw [ENat.card_eq_coe_fintype_card]
          rw [hxyz]
          exact_mod_cast (show 3 < Fintype.card X by omega))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    have hwx : w ≠ x := hw.1
    have hwy : w ≠ y := hw.2.1
    have hwz : w ≠ z := hw.2.2
    let source : Fin 3 → X := ![x, y, z]
    let target : Fin 3 → X := ![x, y, w]
    have hsource : Function.Injective source := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [source, hyx, hyx.symm, hzx, hzx.symm,
          hzy, hzy.symm] at hij ⊢
    have htarget : Function.Injective target := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [target, hyx, hyx.symm, hwx, hwx.symm,
          hwy, hwy.symm] at hij ⊢
    rw [MulAction.isMultiplyPretransitive_iff] at h3
    obtain ⟨g, hg⟩ := h3 ⟨source, hsource⟩ ⟨target, htarget⟩
    have hg0 : g • x = x := by
      have := DFunLike.congr_fun hg (0 : Fin 3)
      simpa [Function.Embedding.smul_apply, source, target] using this
    have hg1 : g • y = y := by
      have := DFunLike.congr_fun hg (1 : Fin 3)
      simpa [Function.Embedding.smul_apply, source, target] using this
    have hg2 : g • z = w := by
      have := DFunLike.congr_fun hg (2 : Fin 3)
      simpa [Function.Embedding.smul_apply, source, target] using this
    have hginv0 : g⁻¹ • x = x := by
      rw [← smul_left_cancel_iff g]
      simpa using hg0.symm
    let qa : N :=
      ⟨g * (a : G) * g⁻¹,
        (inferInstance : N.Normal).conj_mem (a : G) a.prop g⟩
    have hqax : qa • x = a • x := by
      change (g * (a : G) * g⁻¹) • x = (a : G) • x
      calc
        (g * (a : G) * g⁻¹) • x =
            g • ((a : G) • (g⁻¹ • x)) := by simp only [mul_smul]
        _ = g • ((a : G) • x) := by rw [hginv0]
        _ = g • y := rfl
        _ = y := hg1
        _ = (a : G) • x := rfl
    have hqa : qa = a := IsCancelSMul.right_cancel qa a x hqax
    have hcomm : g * (a : G) = (a : G) * g := by
      have hconj : g * (a : G) * g⁻¹ = (a : G) :=
        congrArg Subtype.val hqa
      calc
        g * (a : G) = (g * (a : G) * g⁻¹) * g := by group
        _ = (a : G) * g := by rw [hconj]
    have hcommInv : g * ((a : G)⁻¹) = ((a : G)⁻¹) * g :=
      (show Commute g (a : G) from hcomm).inv_right
    have hgz : g • z = z := by
      change g • ((a : G)⁻¹ • x) = (a : G)⁻¹ • x
      rw [← mul_smul, hcommInv, mul_smul, hg0]
    exact hwz (hg2.symm.trans hgz)
  obtain ⟨a, ha⟩ := exists_ne (1 : N)
  let y : X := a • x
  have hyx : y ≠ x := by
    intro hyx
    exact ha (hfree a x hyx)
  obtain ⟨z, hz⟩ :=
    Finset.exists_not_mem_of_card_lt_enatCard
      (s := {x, y}) (by
        have hx_y : x ∉ ({y} : Finset X) := by
          simpa only [Finset.mem_singleton] using hyx.symm
        have hxy : ({x, y} : Finset X).card = 2 := by
          rw [Finset.card_insert_of_notMem hx_y]
          simp
        rw [ENat.card_eq_coe_fintype_card]
        rw [hxy]
        exact_mod_cast (show 2 < Fintype.card X by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  have hzx : z ≠ x := hz.1
  have hzy : z ≠ y := hz.2
  obtain ⟨b, hb⟩ := hNtrans.exists_smul_eq x z
  have hb1 : b ≠ 1 := by
    intro hb1
    subst b
    apply hzx
    simpa using hb.symm
  have hba : b ≠ a := by
    intro hba
    subst b
    apply hzy
    simpa [y] using hb.symm
  let c : X := (a * b) • x
  have hcx : c ≠ x := by
    intro hcx
    have hab1 : a * b = (1 : N) := hfree (a * b) x hcx
    have hbaInv : b = a⁻¹ := by
      calc
        b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ := by rw [hab1]; simp
    exact hba (hbaInv.trans (hinv a))
  have hcy : c ≠ y := by
    intro hcy
    have habA : a * b = a := IsCancelSMul.right_cancel (a * b) a x hcy
    apply hb1
    apply mul_left_cancel (a := a)
    simpa using habA
  have hcz : c ≠ z := by
    intro hcz
    have habB : a * b = b := IsCancelSMul.right_cancel (a * b) b x (hcz.trans hb.symm)
    apply ha
    apply mul_right_cancel (b := b)
    simpa using habB
  obtain ⟨d, hd⟩ :=
    Finset.exists_not_mem_of_card_lt_enatCard
      (s := {x, y, z, c}) (by
        have hx_yzc : x ∉ ({y, z, c} : Finset X) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hyx.symm, hzx.symm, hcx.symm⟩
        have hy_zc : y ∉ ({z, c} : Finset X) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hzy.symm, hcy.symm⟩
        have hz_c : z ∉ ({c} : Finset X) := by
          simpa only [Finset.mem_singleton] using hcz.symm
        have hxyzc : ({x, y, z, c} : Finset X).card = 4 := by
          rw [Finset.card_insert_of_notMem hx_yzc,
            Finset.card_insert_of_notMem hy_zc,
            Finset.card_insert_of_notMem hz_c]
          simp
        rw [ENat.card_eq_coe_fintype_card]
        rw [hxyzc]
        exact_mod_cast (show 4 < Fintype.card X by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  have hdx : d ≠ x := hd.1
  have hdy : d ≠ y := hd.2.1
  have hdz : d ≠ z := hd.2.2.1
  have hdc : d ≠ c := hd.2.2.2
  let source : Fin 4 → X := ![x, y, z, c]
  let target : Fin 4 → X := ![x, y, z, d]
  have hsource : Function.Injective source := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [source, hyx, hyx.symm, hzx, hzx.symm, hzy, hzy.symm,
        hcx, hcx.symm, hcy, hcy.symm, hcz, hcz.symm] at hij ⊢
  have htarget : Function.Injective target := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [target, hyx, hyx.symm, hzx, hzx.symm, hzy, hzy.symm,
        hdx, hdx.symm, hdy, hdy.symm, hdz, hdz.symm] at hij ⊢
  rw [MulAction.isMultiplyPretransitive_iff] at h4
  obtain ⟨g, hg⟩ := h4 ⟨source, hsource⟩ ⟨target, htarget⟩
  have hg0 : g • x = x := by
    have := DFunLike.congr_fun hg (0 : Fin 4)
    simpa [Function.Embedding.smul_apply, source, target] using this
  have hg1 : g • y = y := by
    have := DFunLike.congr_fun hg (1 : Fin 4)
    simpa [Function.Embedding.smul_apply, source, target] using this
  have hg2 : g • z = z := by
    have := DFunLike.congr_fun hg (2 : Fin 4)
    simpa [Function.Embedding.smul_apply, source, target] using this
  have hg3 : g • c = d := by
    have := DFunLike.congr_fun hg (3 : Fin 4)
    simpa [Function.Embedding.smul_apply, source, target] using this
  have hginv0 : g⁻¹ • x = x := by
    rw [← smul_left_cancel_iff g]
    simpa using hg0.symm
  let qa : N :=
    ⟨g * (a : G) * g⁻¹,
      (inferInstance : N.Normal).conj_mem (a : G) a.prop g⟩
  let qb : N :=
    ⟨g * (b : G) * g⁻¹,
      (inferInstance : N.Normal).conj_mem (b : G) b.prop g⟩
  have hqa : qa = a := by
    apply IsCancelSMul.right_cancel qa a x
    change (g * (a : G) * g⁻¹) • x = (a : G) • x
    calc
      (g * (a : G) * g⁻¹) • x =
          g • ((a : G) • (g⁻¹ • x)) := by simp only [mul_smul]
      _ = g • ((a : G) • x) := by rw [hginv0]
      _ = g • y := rfl
      _ = y := hg1
      _ = (a : G) • x := rfl
  have hqb : qb = b := by
    apply IsCancelSMul.right_cancel qb b x
    change (g * (b : G) * g⁻¹) • x = (b : G) • x
    calc
      (g * (b : G) * g⁻¹) • x =
          g • ((b : G) • (g⁻¹ • x)) := by simp only [mul_smul]
      _ = g • ((b : G) • x) := by rw [hginv0]
      _ = g • z := by
        have hbG : (b : G) • x = z := by
          simpa only [Subgroup.smul_def] using hb
        rw [hbG]
      _ = z := hg2
      _ = (b : G) • x := hb.symm
  have hconjAB : g * ((a * b : N) : G) * g⁻¹ = ((a * b : N) : G) := by
    have hqa' : g * (a : G) * g⁻¹ = (a : G) := congrArg Subtype.val hqa
    have hqb' : g * (b : G) * g⁻¹ = (b : G) := congrArg Subtype.val hqb
    rw [Subgroup.coe_mul]
    calc
      g * ((a : G) * (b : G)) * g⁻¹ =
          (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹) := by group
      _ = (a : G) * (b : G) := by rw [hqa', hqb']
  have hcommAB : g * ((a * b : N) : G) = ((a * b : N) : G) * g := by
    calc
      g * ((a * b : N) : G) =
          (g * ((a * b : N) : G) * g⁻¹) * g := by group
      _ = ((a * b : N) : G) * g := by rw [hconjAB]
  have hgc : g • c = c := by
    change g • (((a * b : N) : G) • x) = ((a * b : N) : G) • x
    rw [← mul_smul, hcommAB, mul_smul, hg0]
  exact hdc (hg3.symm.trans hgc)

theorem false_of_regular_normal_of_five_transitive
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal]
    [IsCancelSMul N X] [MulAction.IsPretransitive N X] : False := by
  have h5G : MulAction.IsMultiplyPretransitive G X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    exact ⟨g, Function.Embedding.ext hg⟩
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5G
  have h4 : MulAction.IsMultiplyPretransitive G X 4 :=
    MulAction.isMultiplyPretransitive_of_le
      (G := G) (α := X) (m := 4) (n := 5) (by omega)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact false_of_regular_normal_subgroup G X hcard h4 N

theorem false_of_commutative_nontrivial_normal_subgroup
    (G X : Type*) [Group G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ g : G, ∀ i, g • a i = b i)
    (N : Subgroup G) [N.Normal] [Nontrivial N]
    [IsMulCommutative N] :
    False := by
  classical
  have h5G : MulAction.IsMultiplyPretransitive G X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, Function.Embedding.ext ?_⟩
    exact hg
  have hX5 : 5 ≤ Nat.card X := by
    simpa [Nat.card_eq_fintype_card] using hcard
  let _ : MulAction.IsMultiplyPretransitive G X 5 := h5G
  have h2 : MulAction.IsMultiplyPretransitive G X 2 :=
    MulAction.isMultiplyPretransitive_of_le (G := G) (α := X) (n := 5) (by omega) hX5
  have hprim : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2
  let _ : MulAction.IsQuasiPreprimitive G X := hprim.isQuasiPreprimitive
  have hNtrans : MulAction.IsPretransitive N X := by
    apply MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    intro hfixed
    apply not_subsingleton N
    constructor
    intro a b
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro x
    have hx : x ∈ MulAction.fixedPoints N X := by
      rw [hfixed]
      exact Set.mem_univ x
    exact ((MulAction.mem_fixedPoints.mp hx) a).trans
      ((MulAction.mem_fixedPoints.mp hx) b).symm
  let _ : MulAction.IsPretransitive N X := hNtrans
  have hfree : ∀ (a : N) (x : X), a • x = x → a = 1 := by
    intro a x hax
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨b, rfl⟩ := hNtrans.exists_smul_eq x y
    change (a : G) • ((b : G) • x) = (1 : G) • ((b : G) • x)
    have hab : (a : G) * (b : G) = (b : G) * (a : G) :=
      congrArg Subtype.val
        (isMulCommutative_iff.mp (inferInstance : IsMulCommutative N) a b)
    rw [← mul_smul, hab, mul_smul]
    simp only [Subgroup.smul_def] at hax
    rw [hax]
    simp
  let _ : IsCancelSMul N X :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr hfree
  exact false_of_regular_normal_of_five_transitive G X hcard h5 N

end FiveTransitive.AbelianNormalObstruction

end CFSG
