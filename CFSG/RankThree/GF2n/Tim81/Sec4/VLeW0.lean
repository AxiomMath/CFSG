module

public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthExt
public import CFSG.RankThree.GF2n.DihedralCompl
public import CFSG.RankThree.GF2n.Tim81.Sec2.OrthModelOrder3
public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Factor
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveGeneral
public import CFSG.GroupActions.ThreeTranspositionFixedPoint
public import CFSG.RankThree.GF2n.Tim81.Sec4.ConjRepLattice

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.QuasithinUnique.Setup.X7
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

private theorem exists_order_three_pair
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F)) :
    ∃ x : ↥H, (x : G) ∈ Pc M V ∧ ∃ y : ↥H, (y : G) ∈ conjSubgroup h₀ (Pc M V) ∧
      piK V H x ≠ 1 ∧ piK V H y ≠ 1 ∧
      piK V H x * piK V H x = 1 ∧ piK V H y * piK V H y = 1 ∧
      orderOf (ψ (piK V H x) * ψ (piK V H y)) = 3 := by
  classical
  obtain ⟨hsq, -, a, b, ha, hb, hne⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  set A : Subgroup (SL(2, F)) := (imgK V H (Pc M V)).map ψ.toMonoidHom with hA
  set A' : Subgroup (SL(2, F)) :=
    (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ.toMonoidHom with hA'
  have hsqA : ∀ z ∈ A, z * z = 1 := hsq
  obtain ⟨y₀, hy₀H, hPy₀, -, hH₀⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  have hA'eq : A' = conjSubgroup (ψ (piK V H ⟨y₀, hy₀H⟩)) A := by
    rw [hA', hA, hPy₀, imgK_conjSubgroup hy₀H hPH, map_conjSubgroup]
    rfl
  have hsqA' : ∀ z ∈ A', z * z = 1 := by
    intro z hz
    rw [hA'eq] at hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    have h := hsq w hw
    calc (MulAut.conj (ψ (piK V H ⟨y₀, hy₀H⟩))) w *
        (MulAut.conj (ψ (piK V H ⟨y₀, hy₀H⟩))) w =
        (MulAut.conj (ψ (piK V H ⟨y₀, hy₀H⟩))) (w * w) := by rw [map_mul]
      _ = 1 := by rw [h, map_one]
  obtain ⟨u, hu, hu1, v, hv, hv1, huv3⟩ :=
    exists_mul_orderOf_three_of_conj_ne (a := a) (b := b) hne
  have huA : u ∈ A := by rw [ha]; exact hu
  have hvA' : v ∈ A' := by rw [hb]; exact hv
  obtain ⟨xbar, hxbar, hxu⟩ := Subgroup.mem_map.mp huA
  obtain ⟨x, hxP, hxpi⟩ := mem_imgK_iff.mp hxbar
  obtain ⟨ybar, hybar, hyu⟩ := Subgroup.mem_map.mp hvA'
  obtain ⟨y, hyP, hypi⟩ := mem_imgK_iff.mp hybar
  refine ⟨x, hxP, y, hyP, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hu1 (by rw [← hxu, ← hxpi, h1, map_one])
  · intro h1
    exact hv1 (by rw [← hyu, ← hypi, h1, map_one])
  · rw [hxpi]
    apply ψ.injective
    rw [map_mul, map_one]
    exact hsqA (ψ xbar) (by rw [hA]; exact ⟨xbar, hxbar, rfl⟩)
  · rw [hypi]
    apply ψ.injective
    rw [map_mul, map_one]
    exact hsqA' (ψ ybar) (by rw [hA']; exact ⟨ybar, hybar, rfl⟩)
  · rw [hxpi, hypi]
    have hx' : ψ xbar = u := hxu
    have hy' : ψ ybar = v := hyu
    rw [hx', hy']
    exact huv3

private theorem exists_split_fixed_mem_W0
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {t : G} (htP : t ∈ Pc M V) (htW : t ∈ Tim79a.xOf V H) :
    ∃ v w0 : G, v ∈ V ∧ w0 ∈ Pc M V ⊓ W₀ ∧ t = v * w0 ∧
      ∀ p ∈ Pc M V, ⁅p, v⁆ = 1 := by
  classical
  have hcomm : Pc M V ⊓ W₀ = ⁅W₀, Pc M V⁆ :=
    le_antisymm hPW (commutator_W0_Pc_le h hPH hVH hW₀ hN)
  have hcommV : ∀ a ∈ V, ∀ b ∈ Pc M V ⊓ W₀, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hW.1.is_comm.comm
      ⟨a, le_xOf_self V H ha⟩ ⟨b, hW₀ hb.2⟩)
  have ht_split : t ∈ V ⊔ (Pc M V ⊓ W₀) := hstar ⟨htP, htW⟩
  obtain ⟨v, hvV, w0, hw0, rfl⟩ := exists_mul_of_mem_sup
    (V := V) (U := Pc M V ⊓ W₀)
    (le_normalizer_of_comm fun b hb a ha => (hcommV a ha b hb).symm) ht_split
  have hpv : ∀ p ∈ Pc M V, ⁅p, v⁆ = 1 := by
    intro p hp
    have hc : p ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp hp).2
    have h1 : v * p = p * v := (Subgroup.mem_centralizer_iff.mp hc) v hvV
    rw [commutatorElement_def]
    calc p * v * p⁻¹ * v⁻¹ = v * p * p⁻¹ * v⁻¹ := by rw [h1.symm]
      _ = 1 := by group
  exact ⟨v, w0, hvV, hw0, rfl, hpv⟩

private theorem fixed_mem_W0
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {t y : G} (htP : t ∈ Pc M V) (htW : t ∈ Tim79a.xOf V H)
    (hy : y ∈ conjSubgroup h₀ (Pc M V)) (hyK : y ∉ kOf V H)
    (hfix : y * t * y⁻¹ = t) :
    t ∈ W₀ := by
  classical
  obtain ⟨v, w0, hvV, hw0, rfl, hpv⟩ :=
    exists_split_fixed_mem_W0 (hW := hW) h hPH hVH hW₀ hN hPW hstar htP htW
  have hvP : ∀ p ∈ Pc M V, ⁅p, v * w0⁆ ∈ W₀ := by
    intro p hp
    have hpw : ⁅p, w0⁆ ∈ W₀ := by
      have hwP : w0 ∈ Pc M V := hw0.1
      have hwW : w0 ∈ W₀ := hw0.2
      have heq : conjSubgroup p W₀ = W₀ :=
        conjSubgroup_eq_self_iff.mpr (hN (hPH hp))
      have h1 : p * w0 * p⁻¹ ∈ W₀ := by
        rw [← heq]
        exact Subgroup.mem_map.mpr ⟨w0, hwW, by simp [MulAut.conj_apply]⟩
      have h2 : p * w0 * p⁻¹ * w0⁻¹ ∈ W₀ := W₀.mul_mem h1 (W₀.inv_mem hwW)
      simpa [commutatorElement_def] using h2
    rw [commutatorElement_mul_right_eq_mul_conj, hpv p hp, one_mul]
    have hcommvw : v * ⁅p, w0⁆ = ⁅p, w0⁆ * v :=
      congrArg Subtype.val (hW.1.is_comm.comm
        ⟨v, le_xOf_self V H hvV⟩ ⟨⁅p, w0⁆, hW₀ hpw⟩)
    have hEq : v * ⁅p, w0⁆ * v⁻¹ = ⁅p, w0⁆ := by
      calc v * ⁅p, w0⁆ * v⁻¹ = (⁅p, w0⁆ * v) * v⁻¹ := by rw [hcommvw]
        _ = ⁅p, w0⁆ := by group
    rw [hEq]
    exact hpw
  have hvK : ∀ k ∈ kOf V H, k * (v * w0) = (v * w0) * k := by
    intro k hk
    have hc := (mem_kOf_iff.mp hk).2
    have h1 : k * (v * w0) = (v * w0) * k := by
      have hkv : v * k = k * v := (Subgroup.mem_centralizer_iff.mp hc) v
        (le_xOf_self V H hvV)
      have hkw : w0 * k = k * w0 := (Subgroup.mem_centralizer_iff.mp hc) w0
        (hW₀ hw0.2)
      calc k * (v * w0) = k * v * w0 := by group
        _ = v * k * w0 := by rw [← hkv]
        _ = v * (k * w0) := by group
        _ = v * (w0 * k) := by rw [hkw]
        _ = (v * w0) * k := by group
    exact h1
  have hvy : ⁅y, v * w0⁆ ∈ W₀ := by
    rw [commutatorElement_def, hfix]
    group
    exact W₀.one_mem
  exact mem_of_isOrthModule_of_commutator_mem_beta h hPH hVH hH hnM ψ hl hW₀ hN horth
    hvK hvP hy hyK hvy

private theorem braid_vec_fixed {X 𝕎 : Type} [Group X] [AddCommGroup 𝕎]
    [Module (ZMod 2) 𝕎] (ρ : Representation (ZMod 2) X 𝕎) {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) (hbraid : a * b * a = b * a * b)
    {v : 𝕎} (hv : ρ a v = v) :
    ρ a (v + ρ b v + ρ (a * b) v) = v + ρ b v + ρ (a * b) v ∧
      ρ b (v + ρ b v + ρ (a * b) v) = v + ρ b v + ρ (a * b) v := by
  have hab : ρ a (ρ b v) = ρ (a * b) v := by
    rw [← Module.End.mul_apply, ← map_mul]
  have hba : ρ a (ρ (a * b) v) = ρ b v := by
    rw [← Module.End.mul_apply, ← map_mul]
    rw [show a * (a * b) = b from by rw [← mul_assoc, ha, one_mul]]
  constructor
  · rw [map_add, map_add, hv, hab, hba]
    abel
  · have hbb : ρ b (ρ b v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, hb, map_one, Module.End.one_apply]
    have hbb' : ρ b (ρ a v) = ρ b v := by rw [hv]
    have h2 : ρ b (ρ (a * b) v) = ρ a (ρ b v) := by
      have hba' : ρ (b * a) v = ρ b v := by
        rw [map_mul, Module.End.mul_apply, hv]
      calc ρ b (ρ (a * b) v) = ρ (b * (a * b)) v := by
            rw [← Module.End.mul_apply, ← map_mul]
        _ = ρ (a * (b * a)) v := by
            rw [show b * (a * b) = a * (b * a) from by
              rw [← mul_assoc b a b, ← hbraid, mul_assoc a b a]]
        _ = ρ a (ρ (b * a) v) := by rw [map_mul, Module.End.mul_apply]
        _ = ρ a (ρ b v) := by rw [hba']
    rw [map_add, map_add, hbb, h2, hab]
    abel

private noncomputable def tau {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F)) (x y : ↥H)
    (s : ↥(Tim79a.xOf V H)) : Additive (IntMod (Tim79a.xOf V H) hW) :=
  ofW hW s + repW hW ψ (ψ (piK V H y)) (ofW hW s) +
    repW hW ψ (ψ (piK V H x) * ψ (piK V H y)) (ofW hW s)

private theorem tau_eq_add_sub {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F)) (x y : ↥H)
    (s : ↥(Tim79a.xOf V H)) :
    tau ψ x y s = ofW hW s +
      (repW hW ψ (ψ (piK V H x)) - 1) (repW hW ψ (ψ (piK V H y)) (ofW hW s)) := by
  rw [tau, sub_eq_add_neg, ZModModule.neg_eq_self]
  have h1 : repW hW ψ (ψ (piK V H x)) (repW hW ψ (ψ (piK V H y)) (ofW hW s)) =
      repW hW ψ (ψ (piK V H x) * ψ (piK V H y)) (ofW hW s) := by
    rw [← Module.End.mul_apply, ← map_mul]
  rw [LinearMap.add_apply, Module.End.one_apply, h1]
  abel

private theorem tau_mem_Pc_inf_xOf
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {x y : ↥H} (hx : (x : G) ∈ Pc M V) {s : G} (hs : s ∈ V) :
    ((toW hW (tau ψ x y ⟨s, le_xOf_self V H hs⟩) : ↥(Tim79a.xOf V H)) : G) ∈
      Pc M V ⊓ Tim79a.xOf V H := by
  classical
  let sW : ↥(Tim79a.xOf V H) := ⟨s, le_xOf_self V H hs⟩
  let v : Additive (IntMod (Tim79a.xOf V H) hW) := ofW hW sW
  let a : SL(2, F) := ψ (piK V H x)
  let b : SL(2, F) := ψ (piK V H y)
  have hva : (sW : G) ∈ V := hs
  have hva' : ofW hW sW ∈ subW hW V := hva
  have hmem : (repW hW ψ a - 1) (repW hW ψ b v) ∈
      subW hW ⁅Tim79a.xOf V H, Pc M V⁆ := by
    have hmem0 : (repW hW ψ a - 1) (repW hW ψ b v) ∈
        commSub (repW hW ψ) ((imgK V H (Pc M V)).map ψ.toMonoidHom) := by
      refine range_le_commSub (a := a) ?_ ⟨repW hW ψ b v, rfl⟩
      rw [MulEquiv.toMonoidHom_eq_coe]
      exact Subgroup.mem_map.mpr
        ⟨piK V H x, (mem_imgK_iff).mpr ⟨x, hx, rfl⟩, rfl⟩
    rw [MulEquiv.toMonoidHom_eq_coe] at hmem0
    rw [commSub_repW hW ψ hPH] at hmem0
    exact hmem0
  have htau : tau ψ x y sW = v + (repW hW ψ a - 1) (repW hW ψ b v) :=
    tau_eq_add_sub ψ x y sW
  have hle : ((toW hW (tau ψ x y sW) : ↥(Tim79a.xOf V H)) : G) ∈
      V ⊔ ⁅Tim79a.xOf V H, Pc M V⁆ := by
    rw [htau, toW_add]
    exact Subgroup.mul_mem_sup hva hmem
  have hcomm : ⁅Tim79a.xOf V H, Pc M V⁆ ≤ Pc M V :=
    (commutator_W0_Pc_le h hPH hVH (le_refl _)
      (Tim79a.H_le_normalizer_xOf V H)).trans inf_le_left
  exact Subgroup.mem_inf.mpr
    ⟨(sup_le h.toHyp.le_Pc hcomm) hle, (toW hW (tau ψ x y sW)).2⟩


private theorem repW_apply_of_mem_Pc
    (h : RootHyp M V)
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {x : ↥H} (hx : (x : G) ∈ Pc M V) {s : G} (hs : s ∈ V) :
    repW hW ψ (ψ (piK V H x)) (ofW hW ⟨s, le_xOf_self V H hs⟩) =
      ofW hW ⟨s, le_xOf_self V H hs⟩ := by
  have hPcentV : Pc M V ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.le_centralizer_iff, h.toHyp.centralizer_Pc]
  have hxs : (x : G) * s = s * (x : G) :=
    (Subgroup.mem_centralizer_iff.mp (hPcentV hx) s hs).symm
  rw [repW_apply_piK, toW_ofW]
  congr 1
  apply Subtype.ext
  rw [conjH_apply_coe]
  rw [hxs, mul_assoc, mul_inv_cancel, mul_one]

private theorem tau_mem_W0
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha2 : ψ (piK V H x) * ψ (piK V H x) = 1)
    (hb2 : ψ (piK V H y) * ψ (piK V H y) = 1)
    (hb1 : ψ (piK V H y) ≠ 1)
    (hbraid : ψ (piK V H x) * ψ (piK V H y) * ψ (piK V H x) =
      ψ (piK V H y) * ψ (piK V H x) * ψ (piK V H y))
    {s : G} (hs : s ∈ V) :
    ((toW hW (tau ψ x y ⟨s, le_xOf_self V H hs⟩) : ↥(Tim79a.xOf V H)) : G) ∈ W₀ := by
  classical
  let sW : ↥(Tim79a.xOf V H) := ⟨s, le_xOf_self V H hs⟩
  let t : G := ((toW hW (tau ψ x y sW) : ↥(Tim79a.xOf V H)) : G)
  have hPcentV : Pc M V ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.le_centralizer_iff, h.toHyp.centralizer_Pc]
  have hxcent : (x : G) * s = s * (x : G) :=
    (Subgroup.mem_centralizer_iff.mp (hPcentV hx) s hs).symm
  have hfixa : repW hW ψ (ψ (piK V H x)) (ofW hW sW) = ofW hW sW :=
    repW_apply_of_mem_Pc h ψ hx hs
  have hfixed := braid_vec_fixed (ρ := repW hW ψ) (a := ψ (piK V H x))
    (b := ψ (piK V H y)) ha2 hb2 hbraid hfixa
  have hb_fix : repW hW ψ (ψ (piK V H y)) (tau ψ x y sW) = tau ψ x y sW := hfixed.2
  have hyK : (y : G) ∉ kOf V H := by
    intro hyK
    exact hb1 ((piK_eq_one_iff y).mpr hyK ▸ map_one ψ)
  have hfix_grp : (y : G) * t * (y : G)⁻¹ = t := by
    have h1 := congrArg (toW hW) hb_fix
    rw [repW_apply_piK, toW_ofW] at h1
    calc (y : G) * t * (y : G)⁻¹ =
        ((conjH V H y (toW hW (tau ψ x y sW)) : ↥(Tim79a.xOf V H)) : G) :=
          (conjH_apply_coe y (toW hW (tau ψ x y sW))).symm
      _ = t := by rw [h1]
  have htP := tau_mem_Pc_inf_xOf (h := h) (hPH := hPH) (hVH := hVH) (ψ := ψ)
    (x := x) (y := y) (hx := hx) (s := s) hs
  simpa [t, sW] using fixed_mem_W0 h hPH hVH hH hnM ψ hl hW₀ hN horth hPW hstar
    (t := t) (y := (y : G)) htP.1 htP.2 hy hyK hfix_grp


private theorem conjSubgroup_mul_of_braid {F : Type} [Field F]
    {S S' : Subgroup (SL(2, F))} {a b : SL(2, F)}
    (ha2 : a * a = 1) (hb2 : b * b = 1) (hbraid : a * b * a = b * a * b)
    (haS : a ∈ S) (hbS' : b ∈ S') (ha1 : a ≠ 1)
    (hS : ∃ s : SL(2, F), S = conjSubgroup s (utri F))
    (hS' : ∃ t : SL(2, F), S' = conjSubgroup t (utri F)) :
    conjSubgroup (a * b) S = S' := by
  obtain ⟨s, rfl⟩ := hS
  obtain ⟨t, rfl⟩ := hS'
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hmem1 : b * a * b ∈ conjSubgroup b (conjSubgroup s (utri F)) := by
    rw [mem_conjSubgroup]
    have h : b⁻¹ * (b * a * b) * b = a := by
      rw [hb']
      calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
        _ = a := by rw [show b * b = 1 from hb2]; group
    rw [h]
    exact haS
  have hmem2 : b * a * b ∈ conjSubgroup a (conjSubgroup t (utri F)) := by
    rw [← hbraid, mem_conjSubgroup]
    have h : a⁻¹ * (a * b * a) * a = b := by
      rw [ha']
      calc a * (a * b * a) * a = (a * a) * b * (a * a) := by group
        _ = b := by rw [show a * a = 1 from ha2]; group
    rw [h]
    exact hbS'
  have hconj : b⁻¹ * (b * a * b) * b = a := by
    rw [hb']
    calc b * (b * a * b) * b = (b * b) * a * (b * b) := by group
      _ = a := by rw [show b * b = 1 from hb2]; group
  have hne1 : b * a * b ≠ 1 := by
    intro h1
    apply ha1
    calc a = b⁻¹ * (b * a * b) * b := hconj.symm
      _ = b⁻¹ * 1 * b := by rw [h1]
      _ = 1 := by rw [hb']; simp [hb2]
  have heq : conjSubgroup b (conjSubgroup s (utri F)) =
      conjSubgroup a (conjSubgroup t (utri F)) := by
    by_contra hne
    have hbne : conjSubgroup (b * s) (utri F) ≠ conjSubgroup (a * t) (utri F) := by
      intro h
      apply hne
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
        CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
      exact h
    have hbot : conjSubgroup (b * s) (utri F) ⊓ conjSubgroup (a * t) (utri F) = ⊥ :=
      inf_conjSubgroup_utri_eq_bot hbne
    have h1' : b * a * b ∈ conjSubgroup (b * s) (utri F) := by
      rwa [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hmem1
    have h2' : b * a * b ∈ conjSubgroup (a * t) (utri F) := by
      rwa [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hmem2
    have hmem : b * a * b ∈ (⊥ : Subgroup (SL(2, F))) := by
      rw [← hbot]
      exact ⟨h1', h2'⟩
    exact hne1 (Subgroup.mem_bot.mp hmem)
  calc conjSubgroup (a * b) (conjSubgroup s (utri F))
      = conjSubgroup a (conjSubgroup b (conjSubgroup s (utri F))) :=
        (CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup a b _).symm
    _ = conjSubgroup a (conjSubgroup a (conjSubgroup t (utri F))) := by rw [heq]
    _ = conjSubgroup (a * a) (conjSubgroup t (utri F)) :=
        CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup a a _
    _ = conjSubgroup t (utri F) := by
        rw [ha2, CFSG.CGT.Timmesfeld75.conjSubgroup_one]

private theorem subRepW_sub_apply_coe {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (g : SL(2, F)) (z : subW hW W₀) :
    (((subRepW hW ψ hW₀ hN g - 1) z : subW hW W₀) :
      Additive (IntMod (Tim79a.xOf V H) hW)) =
      (repW hW ψ g - 1) (z : Additive (IntMod (Tim79a.xOf V H) hW)) := by
  change (((subRepW hW ψ hW₀ hN g z - z : subW hW W₀) :
    Additive (IntMod (Tim79a.xOf V H) hW)) =
    ((repW hW ψ g) (z : Additive (IntMod (Tim79a.xOf V H) hW)) -
      (z : Additive (IntMod (Tim79a.xOf V H) hW))))
  rw [Submodule.coe_sub, show subRepW hW ψ hW₀ hN =
      CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW W₀)
        ((normalizer_subW_iff hW ψ hW₀).mp hN) from rfl,
    CFSG.Quasithin.B45U33.subRep_apply]


private theorem sec_data
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V) (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (S S' : Subgroup (SL(2, F)))
    (hSdef : S = (imgK V H (Pc M V)).map ψ)
    (hS'def : S' = (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ) :
    ∃ a₀ b₀ : SL(2, F),
      S = conjSubgroup a₀ (utri F) ∧ S' = conjSubgroup b₀ (utri F) ∧
      (∀ z ∈ S, z * z = 1) ∧ (∀ z ∈ S', z * z = 1) ∧
      Nat.card S = 2 ^ (2 * l) ∧ Nat.card S' = 2 ^ (2 * l) ∧
      S ≠ S' ∧ ψ (piK V H x) ∈ S ∧ ψ (piK V H y) ∈ S' := by
  obtain ⟨hsq, -, a₀, b₀, hS₀, hS'₀, hne₀⟩ := imgK_map_sl2 h hPH hVH hH hnM ψ
  have hS_eq : S = conjSubgroup a₀ (utri F) := by
    rw [hSdef, ← MulEquiv.toMonoidHom_eq_coe]
    exact hS₀
  have hS'_eq : S' = conjSubgroup b₀ (utri F) := by
    rw [hS'def, ← MulEquiv.toMonoidHom_eq_coe]
    exact hS'₀
  have hS2 : ∀ z ∈ S, z * z = 1 := by
    intro z hz
    exact hsq z (by rwa [hSdef, ← MulEquiv.toMonoidHom_eq_coe] at hz)
  have hS'2 : ∀ z ∈ S', z * z = 1 := by
    intro z hz
    rw [hS'_eq] at hz
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨c, rfl⟩ := mem_utri_iff.mp hu
    rw [← map_mul, utriElt_mul_self, map_one]
  have hScard : Nat.card S = 2 ^ (2 * l) := by
    rw [hS_eq, card_conjSubgroup, card_utri, Nat.card_eq_fintype_card, hl]
  have hS'card : Nat.card S' = 2 ^ (2 * l) := by
    rw [hS'_eq, card_conjSubgroup, card_utri, Nat.card_eq_fintype_card, hl]
  have hSne : S ≠ S' := by
    intro hSS
    exact hne₀ (hS_eq.symm.trans (hSS.trans hS'_eq))
  have haS : ψ (piK V H x) ∈ S := by
    rw [hSdef]
    exact Subgroup.mem_map.mpr
      ⟨piK V H x, (mem_imgK_iff).mpr ⟨x, hx, rfl⟩, rfl⟩
  have hbS' : ψ (piK V H y) ∈ S' := by
    rw [hS'def]
    exact Subgroup.mem_map.mpr
      ⟨piK V H y, (mem_imgK_iff).mpr ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨a₀, b₀, hS_eq, hS'_eq, hS2, hS'2, hScard, hS'card, hSne, haS, hbS'⟩

private theorem tau_sub_mem_fixedSub_and_commSub
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    {s : G} (hs : s ∈ V)
    {S : Subgroup (SL(2, F))} {a b : SL(2, F)}
    (hSdef : S = (imgK V H (Pc M V)).map ψ)
    (hadef : a = ψ (piK V H x)) (hbdef : b = ψ (piK V H y))
    (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hbraid : a * b * a = b * a * b)
    (hτW0 : tau ψ x y ⟨s, le_xOf_self V H hs⟩ ∈ subW hW W₀) :
    (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) ∈
        fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers a) ∧
      (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) ∈
        commSub (subRepW hW ψ hW₀ hN) S := by
  classical
  let sW : ↥(Tim79a.xOf V H) := ⟨s, le_xOf_self V H hs⟩
  let τ_sub : subW hW W₀ := ⟨tau ψ x y sW, hτW0⟩
  have hτval : (τ_sub : Additive (IntMod (Tim79a.xOf V H) hW)) =
      ofW hW sW + repW hW ψ b (ofW hW sW) +
        repW hW ψ (a * b) (ofW hW sW) := by
    change tau ψ x y sW = _
    rw [tau, ← hadef, ← hbdef]
  have hfixa : repW hW ψ a (ofW hW sW) = ofW hW sW := by
    rw [hadef]
    exact repW_apply_of_mem_Pc h ψ (x := x) hx (s := s) hs
  have hfixed := braid_vec_fixed (ρ := repW hW ψ) (a := a) (b := b) ha2 hb2 hbraid hfixa
  constructor
  · rw [mem_fixedSub_zpowers]
    apply Subtype.ext
    rw [show subRepW hW ψ hW₀ hN =
        CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW W₀)
          ((normalizer_subW_iff hW ψ hW₀).mp hN) from rfl,
      CFSG.Quasithin.B45U33.subRep_apply, hτval]
    exact hfixed.1
  · have htP := tau_mem_Pc_inf_xOf (h := h) (hPH := hPH) (hVH := hVH) (ψ := ψ)
      (x := x) (y := y) (hx := hx) (s := s) hs
    have hmem : tau ψ x y sW ∈ subW hW ⁅W₀, Pc M V⁆ := hPW ⟨htP.1, hτW0⟩
    have hmap := commSub_subRepW hW ψ hW₀ hN (S := Pc M V) hPH
    rw [← hSdef] at hmap
    have hmemMap : tau ψ x y sW ∈ (commSub (subRepW hW ψ hW₀ hN) S).map
        (subW hW W₀).subtype := by
      rw [hmap]
      exact hmem
    obtain ⟨z, hz, hzval⟩ := Submodule.mem_map.mp hmemMap
    have hzEq : z = τ_sub := Subtype.ext hzval
    rwa [hzEq] at hz

private theorem tau_mem_fixedSup_of_braid
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha1 : ψ (piK V H x) ≠ 1)
    (ha2 : ψ (piK V H x) * ψ (piK V H x) = 1)
    (hb2 : ψ (piK V H y) * ψ (piK V H y) = 1)
    (hord : orderOf (ψ (piK V H x) * ψ (piK V H y)) = 3)
    {s : G} (hs : s ∈ V)
    {S S' : Subgroup (SL(2, F))} {a b : SL(2, F)}
    (hSdef : S = (imgK V H (Pc M V)).map ψ)
    (hS'def : S' = (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ)
    (hadef : a = ψ (piK V H x)) (hbdef : b = ψ (piK V H y))
    (hτW0 : tau ψ x y ⟨s, le_xOf_self V H hs⟩ ∈ subW hW W₀) :
    (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) ∈
      fixedSub (subRepW hW ψ hW₀ hN) S ⊔
        (fixedSub (subRepW hW ψ hW₀ hN) S').map
          (subRepW hW ψ hW₀ hN a - 1) := by
  classical
  obtain ⟨a₀, b₀, hS_eq, hS'_eq, hS2, hS'2, hScard, hS'card, hSne, haSψ, hbS'ψ⟩ :=
    sec_data h hPH hVH hH hnM ψ hl hx hy S S' hSdef hS'def
  have haS : a ∈ S := by rw [hadef]; exact haSψ
  have hbS' : b ∈ S' := by rw [hbdef]; exact hbS'ψ
  have ha2' : a * a = 1 := by rw [hadef]; exact ha2
  have hb2' : b * b = 1 := by rw [hbdef]; exact hb2
  have ha1' : a ≠ 1 := by rw [hadef]; exact ha1
  have hord' : orderOf (a * b) = 3 := by rw [hadef, hbdef]; exact hord
  have h3 : (a * b) ^ 3 = 1 := by rw [← hord']; exact pow_orderOf_eq_one _
  have hbraid : a * b * a = b * a * b :=
    CFSG.GroupActions.braid_of_involutions ha2' hb2' h3
  have hdata := tau_sub_mem_fixedSub_and_commSub h hPH hVH ψ hW₀ hN hPW hx hs
    hSdef hadef hbdef ha2' hb2' hbraid hτW0
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hO4 := horth.fixedSub_zpowers_inf_commSub_eq_sup_map (hF := hl) S S' hS2 hScard
    hS'2 hS'card hSne (x := a) haS ha1'
  have hτRHS : (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) ∈
      fixedSub (subRepW hW ψ hW₀ hN) S ⊔
        (fixedSub (subRepW hW ψ hW₀ hN) S').map
          (subRepW hW ψ hW₀ hN a - 1) := by
    rw [← hO4]
    exact Submodule.mem_inf.mpr ⟨hdata.1, hdata.2⟩
  exact hτRHS

private theorem fixedSub_conj_eq_map {F : Type} [Field F]
    (ψ : HBar V H ≃* SL(2, F)) {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {S S' : Subgroup (SL(2, F))} {a b : SL(2, F)}
    (hconj : conjSubgroup (a * b) S = S') :
    fixedSub (subRepW hW ψ hW₀ hN) S' =
      (fixedSub (subRepW hW ψ hW₀ hN) S).map
        (subRepW hW ψ hW₀ hN (a * b)) := by
  have hS'conj : S' = S.map (MulAut.conj (a * b)).toMonoidHom := by
    rw [← hconj]
    rfl
  rw [hS'conj, fixedSub_map_conj]

private theorem exists_decomp_of_fixedSub_sup_map
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {S S' : Subgroup (SL(2, F))} {a b : SL(2, F)}
    (ha2 : a * a = 1) (hconj : conjSubgroup (a * b) S = S')
    {x : subW hW W₀}
    (hx : x ∈ fixedSub (subRepW hW ψ hW₀ hN) S ⊔
      (fixedSub (subRepW hW ψ hW₀ hN) S').map
        (subRepW hW ψ hW₀ hN a - 1)) :
    ∃ v₀ c₁ : subW hW W₀,
      v₀ ∈ fixedSub (subRepW hW ψ hW₀ hN) S ∧
      c₁ ∈ fixedSub (subRepW hW ψ hW₀ hN) S ∧
      x = v₀ + (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁) := by
  classical
  obtain ⟨v₀, hv₀, c, hc, hv₀c⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c₀, hc₀, hc_eq⟩ := Submodule.mem_map.mp hc
  have hfixS' := fixedSub_conj_eq_map (hW := hW) ψ hW₀ hN hconj
  have hc₀' : c₀ ∈ (fixedSub (subRepW hW ψ hW₀ hN) S).map
      (subRepW hW ψ hW₀ hN (a * b)) := by
    rwa [← hfixS']
  obtain ⟨c₁, hc₁, hc₁_eq⟩ := Submodule.mem_map.mp hc₀'
  have hc' : c = (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN (a * b) c₁) := by
    rw [← hc_eq, ← hc₁_eq]
  have hsubeq : (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN (a * b) c₁) =
      (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁) := by
    have h1 : subRepW hW ψ hW₀ hN (a * b) c₁ =
        subRepW hW ψ hW₀ hN a (subRepW hW ψ hW₀ hN b c₁) := by
      rw [map_mul, Module.End.mul_apply]
    have h2 : subRepW hW ψ hW₀ hN a (subRepW hW ψ hW₀ hN a
        (subRepW hW ψ hW₀ hN b c₁)) = subRepW hW ψ hW₀ hN b c₁ := by
      rw [← Module.End.mul_apply, ← map_mul, ha2, map_one, Module.End.one_apply]
    rw [h1]
    have hL : (subRepW hW ψ hW₀ hN a - 1)
        (subRepW hW ψ hW₀ hN a (subRepW hW ψ hW₀ hN b c₁)) =
        subRepW hW ψ hW₀ hN a (subRepW hW ψ hW₀ hN a
          (subRepW hW ψ hW₀ hN b c₁)) - subRepW hW ψ hW₀ hN a
            (subRepW hW ψ hW₀ hN b c₁) := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    have hR : (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁) =
        subRepW hW ψ hW₀ hN a (subRepW hW ψ hW₀ hN b c₁) -
          subRepW hW ψ hW₀ hN b c₁ := by
      rw [LinearMap.sub_apply, Module.End.one_apply]
    rw [hL, hR, h2, sub_eq_add_neg, sub_eq_add_neg, ZModModule.neg_eq_self,
      ZModModule.neg_eq_self]
    abel
  have hc'' : c = (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁) :=
    hc'.trans hsubeq
  refine ⟨v₀, c₁, hv₀, hc₁, ?_⟩
  rw [hc''] at hv₀c
  exact hv₀c.symm

private theorem exists_decomp_of_mem_fixedSup
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha1 : ψ (piK V H x) ≠ 1)
    (ha2 : ψ (piK V H x) * ψ (piK V H x) = 1)
    (hb2 : ψ (piK V H y) * ψ (piK V H y) = 1)
    (hord : orderOf (ψ (piK V H x) * ψ (piK V H y)) = 3)
    {s : G} (hs : s ∈ V)
    {S S' : Subgroup (SL(2, F))} {a b : SL(2, F)}
    (hSdef : S = (imgK V H (Pc M V)).map ψ)
    (hS'def : S' = (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ)
    (hadef : a = ψ (piK V H x)) (hbdef : b = ψ (piK V H y))
    (hτW0 : tau ψ x y ⟨s, le_xOf_self V H hs⟩ ∈ subW hW W₀)
    (hτRHS : (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) ∈
      fixedSub (subRepW hW ψ hW₀ hN) S ⊔
        (fixedSub (subRepW hW ψ hW₀ hN) S').map
          (subRepW hW ψ hW₀ hN a - 1)) :
    ∃ v₀ c₁ : subW hW W₀,
      v₀ ∈ fixedSub (subRepW hW ψ hW₀ hN) S ∧
      c₁ ∈ fixedSub (subRepW hW ψ hW₀ hN) S ∧
      (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) =
        v₀ + (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁) := by
  classical
  obtain ⟨a₀, b₀, hS_eq, hS'_eq, hS2, hS'2, hScard, hS'card, hSne, haSψ, hbS'ψ⟩ :=
    sec_data h hPH hVH hH hnM ψ hl hx hy S S' hSdef hS'def
  have haS : a ∈ S := by rw [hadef]; exact haSψ
  have hbS' : b ∈ S' := by rw [hbdef]; exact hbS'ψ
  have ha2' : a * a = 1 := by rw [hadef]; exact ha2
  have hb2' : b * b = 1 := by rw [hbdef]; exact hb2
  have ha1' : a ≠ 1 := by rw [hadef]; exact ha1
  have hord' : orderOf (a * b) = 3 := by rw [hadef, hbdef]; exact hord
  have h3 : (a * b) ^ 3 = 1 := by rw [← hord']; exact pow_orderOf_eq_one _
  have hbraid : a * b * a = b * a * b :=
    CFSG.GroupActions.braid_of_involutions ha2' hb2' h3
  have hconj : conjSubgroup (a * b) S = S' :=
    conjSubgroup_mul_of_braid ha2' hb2' hbraid haS hbS' ha1'
      ⟨a₀, hS_eq⟩ ⟨b₀, hS'_eq⟩
  obtain ⟨v₀, c₁, hv₀, hc₁, hdecomp⟩ :=
    exists_decomp_of_fixedSub_sup_map ψ hW₀ hN ha2' hconj hτRHS
  exact ⟨v₀, c₁, hv₀, hc₁, hdecomp⟩

private theorem exists_tau_decomp_of_subW_decomp
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {x y : ↥H} {s : G} (hs : s ∈ V)
    {S : Subgroup (SL(2, F))} (hSdef : S = (imgK V H (Pc M V)).map ψ)
    {a b : SL(2, F)}
    {v₀ c₁ : subW hW W₀}
    (hτW0 : tau ψ x y ⟨s, le_xOf_self V H hs⟩ ∈ subW hW W₀)
    (hv₀ : v₀ ∈ fixedSub (subRepW hW ψ hW₀ hN) S)
    (hc₁ : c₁ ∈ fixedSub (subRepW hW ψ hW₀ hN) S)
    (hdecomp : (⟨tau ψ x y ⟨s, le_xOf_self V H hs⟩, hτW0⟩ : subW hW W₀) =
      v₀ + (subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁)) :
    ∃ v₀' v₁ : Additive (IntMod (Tim79a.xOf V H) hW),
      v₀' ∈ subW hW (V ⊓ W₀) ∧ v₁ ∈ subW hW (V ⊓ W₀) ∧
        tau ψ x y ⟨s, le_xOf_self V H hs⟩ =
          v₀' + (repW hW ψ a - 1) (repW hW ψ b v₁) := by
  classical
  let v₀' : Additive (IntMod (Tim79a.xOf V H) hW) :=
    (v₀ : Additive (IntMod (Tim79a.xOf V H) hW))
  let v₁ : Additive (IntMod (Tim79a.xOf V H) hW) :=
    (c₁ : Additive (IntMod (Tim79a.xOf V H) hW))
  have hv₀'sub : v₀' ∈ subW hW (V ⊓ W₀) := by
    have hmap := fixedSub_subRepW hW ψ hW₀ hN (S := Pc M V) hPH
    rw [← hSdef] at hmap
    have hmem : v₀' ∈ (fixedSub (subRepW hW ψ hW₀ hN) S).map
        (subW hW W₀).subtype :=
      Submodule.mem_map.mpr ⟨v₀, hv₀, rfl⟩
    rw [hmap] at hmem
    rwa [inf_centralizer_Pc_eq_inf (h := h)] at hmem
  have hv₁sub : v₁ ∈ subW hW (V ⊓ W₀) := by
    have hmap := fixedSub_subRepW hW ψ hW₀ hN (S := Pc M V) hPH
    rw [← hSdef] at hmap
    have hmem : v₁ ∈ (fixedSub (subRepW hW ψ hW₀ hN) S).map
        (subW hW W₀).subtype :=
      Submodule.mem_map.mpr ⟨c₁, hc₁, rfl⟩
    rw [hmap] at hmem
    rwa [inf_centralizer_Pc_eq_inf (h := h)] at hmem
  have hval : tau ψ x y ⟨s, le_xOf_self V H hs⟩ = v₀' +
      (((subRepW hW ψ hW₀ hN a - 1) (subRepW hW ψ hW₀ hN b c₁) : subW hW W₀) :
        Additive (IntMod (Tim79a.xOf V H) hW)) := by
    have hcoe := congrArg (fun z : subW hW W₀ =>
      (z : Additive (IntMod (Tim79a.xOf V H) hW))) hdecomp
    rw [Submodule.coe_add] at hcoe
    simpa [v₀', Submodule.coe_sub] using hcoe
  have hcoecoe : (((subRepW hW ψ hW₀ hN a - 1)
      (subRepW hW ψ hW₀ hN b c₁) : subW hW W₀) :
        Additive (IntMod (Tim79a.xOf V H) hW)) =
      (repW hW ψ a - 1) (repW hW ψ b v₁) := by
    rw [subRepW_sub_apply_coe]
    rfl
  refine ⟨v₀', v₁, hv₀'sub, hv₁sub, ?_⟩
  change tau ψ x y ⟨s, le_xOf_self V H hs⟩ =
    v₀' + (repW hW ψ a - 1) (repW hW ψ b v₁)
  rw [hval, hcoecoe]

private theorem exists_tau_decomp
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha1 : ψ (piK V H x) ≠ 1)
    (ha2 : ψ (piK V H x) * ψ (piK V H x) = 1)
    (hb1 : ψ (piK V H y) ≠ 1)
    (hb2 : ψ (piK V H y) * ψ (piK V H y) = 1)
    (hord : orderOf (ψ (piK V H x) * ψ (piK V H y)) = 3)
    {s : G} (hs : s ∈ V) :
    ∃ v₀ v₁ : Additive (IntMod (Tim79a.xOf V H) hW),
      v₀ ∈ subW hW (V ⊓ W₀) ∧ v₁ ∈ subW hW (V ⊓ W₀) ∧
        tau ψ x y ⟨s, le_xOf_self V H hs⟩ =
          v₀ + (repW hW ψ (ψ (piK V H x)) - 1) (repW hW ψ (ψ (piK V H y)) v₁) := by
  classical
  set S : Subgroup (SL(2, F)) := (imgK V H (Pc M V)).map ψ with hSdef
  set S' : Subgroup (SL(2, F)) :=
    (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ with hS'def
  set a : SL(2, F) := ψ (piK V H x) with hadef
  set b : SL(2, F) := ψ (piK V H y) with hbdef
  let sW : ↥(Tim79a.xOf V H) := ⟨s, le_xOf_self V H hs⟩
  let τ : Additive (IntMod (Tim79a.xOf V H) hW) := tau ψ x y sW
  have hbraid : ψ (piK V H x) * ψ (piK V H y) * ψ (piK V H x) =
      ψ (piK V H y) * ψ (piK V H x) * ψ (piK V H y) :=
    CFSG.GroupActions.braid_of_involutions ha2 hb2
      (by rw [← hord]; exact pow_orderOf_eq_one _)
  have hτW0 : τ ∈ subW hW W₀ := by
    change ((toW hW τ : ↥(Tim79a.xOf V H)) : G) ∈ W₀
    simpa [τ, sW] using tau_mem_W0 h hPH hVH hH hnM ψ hl hW₀ hN horth hPW hstar
      hx hy ha2 hb2 hb1 hbraid hs
  have hτRHS := tau_mem_fixedSup_of_braid h hPH hVH hH hnM ψ hl hW₀ hN horth hPW
    hx hy ha1 ha2 hb2 hord hs hSdef hS'def hadef hbdef hτW0
  obtain ⟨v₀, c₁, hv₀, hc₁, hdecomp⟩ :=
    exists_decomp_of_mem_fixedSup h hPH hVH hH hnM ψ hl hW₀ hN
      hx hy ha1 ha2 hb2 hord hs hSdef hS'def hadef hbdef hτW0 hτRHS
  have hres := exists_tau_decomp_of_subW_decomp h hPH ψ hW₀ hN hs hSdef
    hτW0 hv₀ hc₁ hdecomp
  simpa [hadef, hbdef] using hres

private theorem not_mem_W0_of_add_not_mem
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} {s : G} (hs : s ∈ V) (hsW0 : s ∉ W₀)
    {v₁ : Additive (IntMod (Tim79a.xOf V H) hW)}
    (hv₁ : v₁ ∈ subW hW (V ⊓ W₀)) :
    ((toW hW (ofW hW ⟨s, le_xOf_self V H hs⟩ + v₁) :
      ↥(Tim79a.xOf V H)) : G) ∉ W₀ := by
  have hv₁W0 : ((toW hW v₁ : ↥(Tim79a.xOf V H)) : G) ∈ W₀ :=
    (subW_mono (hW := hW) inf_le_right) hv₁
  have hrv : ((toW hW (ofW hW ⟨s, le_xOf_self V H hs⟩ + v₁) :
      ↥(Tim79a.xOf V H)) : G) =
      s * ((toW hW v₁ : ↥(Tim79a.xOf V H)) : G) := by
    rw [toW_add, toW_ofW, Subgroup.coe_mul]
  intro hrW0
  apply hsW0
  have hs_eq : s = ((toW hW (ofW hW ⟨s, le_xOf_self V H hs⟩ + v₁) :
      ↥(Tim79a.xOf V H)) : G) * ((toW hW v₁ : ↥(Tim79a.xOf V H)) : G)⁻¹ := by
    calc s = (s * ((toW hW v₁ : ↥(Tim79a.xOf V H)) : G)) *
        ((toW hW v₁ : ↥(Tim79a.xOf V H)) : G)⁻¹ := by group
      _ = ((toW hW (ofW hW ⟨s, le_xOf_self V H hs⟩ + v₁) :
          ↥(Tim79a.xOf V H)) : G) *
          ((toW hW v₁ : ↥(Tim79a.xOf V H)) : G)⁻¹ := by rw [hrv]
  rw [hs_eq]
  exact W₀.mul_mem hrW0 (W₀.inv_mem hv₁W0)

private theorem exists_u_aux
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {W₀ : Subgroup G} {x y : ↥H} {s : G} (hs : s ∈ V) (hsW0 : s ∉ W₀)
    {v₀ v₁ : Additive (IntMod (Tim79a.xOf V H) hW)}
    (hv₀ : v₀ ∈ subW hW (V ⊓ W₀)) (hv₁ : v₁ ∈ subW hW (V ⊓ W₀))
    (hτeq : tau ψ x y ⟨s, le_xOf_self V H hs⟩ =
      v₀ + (repW hW ψ (ψ (piK V H x)) - 1) (repW hW ψ (ψ (piK V H y)) v₁)) :
    ∃ r u : Additive (IntMod (Tim79a.xOf V H) hW),
      r ∈ subW hW V ∧
      ((toW hW r : ↥(Tim79a.xOf V H)) : G) ∉ W₀ ∧
      (repW hW ψ (ψ (piK V H x)) - 1) u ∈ subW hW V ∧
      u = repW hW ψ (ψ (piK V H y)) r := by
  classical
  let sW : ↥(Tim79a.xOf V H) := ⟨s, le_xOf_self V H hs⟩
  let aρ : Module.End (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    repW hW ψ (ψ (piK V H x))
  let bρ : Module.End (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW)) :=
    repW hW ψ (ψ (piK V H y))
  let r : Additive (IntMod (Tim79a.xOf V H) hW) := ofW hW sW + v₁
  let u : Additive (IntMod (Tim79a.xOf V H) hW) := bρ r
  have hofV : ofW hW sW ∈ subW hW V := by
    change (sW : G) ∈ V
    exact hs
  have hv₁V : v₁ ∈ subW hW V := subW_mono inf_le_left hv₁
  have hrV : r ∈ subW hW V := (subW hW V).add_mem hofV hv₁V
  have hrnot : ((toW hW r : ↥(Tim79a.xOf V H)) : G) ∉ W₀ := by
    change ((toW hW (ofW hW sW + v₁) : ↥(Tim79a.xOf V H)) : G) ∉ W₀
    exact not_mem_W0_of_add_not_mem hs hsW0 hv₁
  have hX₁ : (aρ - 1) (bρ (ofW hW sW)) = tau ψ x y sW + ofW hW sW := by
    have h := tau_eq_add_sub ψ x y sW
    change tau ψ x y sW = ofW hW sW + (aρ - 1) (bρ (ofW hW sW)) at h
    rw [h]
    calc (aρ - 1) (bρ (ofW hW sW)) =
        (aρ - 1) (bρ (ofW hW sW)) + (ofW hW sW + ofW hW sW) := by
          rw [ZModModule.add_self, add_zero]
      _ = (ofW hW sW + (aρ - 1) (bρ (ofW hW sW))) + ofW hW sW := by abel
  have hX₂ : (aρ - 1) (bρ v₁) = tau ψ x y sW + v₀ := by
    rw [hτeq]
    calc (aρ - 1) (bρ v₁) = (aρ - 1) (bρ v₁) + (v₀ + v₀) := by
          rw [ZModModule.add_self, add_zero]
      _ = (v₀ + (aρ - 1) (bρ v₁)) + v₀ := by abel
  have hr_add : r = ofW hW sW + v₁ := rfl
  have hbr : bρ r = bρ (ofW hW sW) + bρ v₁ := by rw [hr_add, map_add]
  have hu_eq : (aρ - 1) u = ofW hW sW + v₀ := by
    change (aρ - 1) (bρ r) = ofW hW sW + v₀
    rw [hr_add, map_add, map_add, hX₁, hX₂]
    calc (tau ψ x y sW + ofW hW sW) + (tau ψ x y sW + v₀) =
        (tau ψ x y sW + tau ψ x y sW) + (ofW hW sW + v₀) := by abel
      _ = ofW hW sW + v₀ := by rw [ZModModule.add_self, zero_add]
  have hdV : (aρ - 1) u ∈ subW hW V := by
    rw [hu_eq]
    exact (subW hW V).add_mem hofV (subW_mono inf_le_left hv₀)
  exact ⟨r, u, hrV, hrnot, hdV, rfl⟩

private theorem exists_u
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha1 : ψ (piK V H x) ≠ 1)
    (ha2 : ψ (piK V H x) * ψ (piK V H x) = 1)
    (hb2 : ψ (piK V H y) * ψ (piK V H y) = 1)
    (hb1 : ψ (piK V H y) ≠ 1)
    (hord : orderOf (ψ (piK V H x) * ψ (piK V H y)) = 3)
    {s : G} (hs : s ∈ V) (hsW0 : s ∉ W₀) :
    ∃ u' : G, u' ∈ conjSubgroup (y : G) V ∧ u' ∈ Tim79a.xOf V H ∧ u' ≠ 1 ∧
      ⁅(x : G), u'⁆ ∈ V := by
  classical
  obtain ⟨v₀, v₁, hv₀, hv₁, hτeq⟩ :=
    exists_tau_decomp h hPH hVH hH hnM ψ hl hW₀ hN horth hPW hstar hx hy
      ha1 ha2 hb1 hb2 hord hs
  obtain ⟨r, u, hrV, hrnot, hdV, hu_def⟩ :=
    exists_u_aux (hW := hW) ψ hs hsW0 hv₀ hv₁ hτeq
  let sW : ↥(Tim79a.xOf V H) := ⟨s, le_xOf_self V H hs⟩
  have hu'_eq : (toW hW u : ↥(Tim79a.xOf V H)) = conjH V H y (toW hW r) := by
    rw [hu_def]
    rw [repW_apply_piK, toW_ofW]
  have hu'V : ((toW hW u : ↥(Tim79a.xOf V H)) : G) ∈ conjSubgroup (y : G) V := by
    rw [hu'_eq, conjH_apply_coe]
    exact Subgroup.mem_map.mpr ⟨((toW hW r : ↥(Tim79a.xOf V H)) : G),
      (mem_subW_iff hW).mp hrV, rfl⟩
  have hu'W : ((toW hW u : ↥(Tim79a.xOf V H)) : G) ∈ Tim79a.xOf V H := (toW hW u).2
  have hu'ne : ((toW hW u : ↥(Tim79a.xOf V H)) : G) ≠ 1 := by
    intro h1
    apply hrnot
    have h2 : (toW hW u : ↥(Tim79a.xOf V H)) = 1 := Subtype.ext h1
    rw [hu'_eq] at h2
    have h3 : toW hW r = 1 := by
      have := congrArg (fun w => (conjH V H y).symm w) h2
      simpa using this
    rw [h3]
    exact W₀.one_mem
  have hneg : toW hW (-u) = (toW hW u)⁻¹ := by
    have h := ofW_inv (hW := hW) (toW hW u)
    rw [ofW_toW] at h
    exact (congrArg (toW hW) h).symm
  have hu_comm : ((toW hW ((repW hW ψ (ψ (piK V H x)) - 1) u) :
      ↥(Tim79a.xOf V H)) : G) =
      ⁅(x : G), ((toW hW u : ↥(Tim79a.xOf V H)) : G)⁆ := by
    have h := repW_apply_piK_sub (hW := hW) (ψ := ψ) x (toW hW u)
    simpa [LinearMap.sub_apply, Module.End.one_apply] using
      congrArg (fun w : ↥(Tim79a.xOf V H) => (w : G)) (congrArg (toW hW) h)
  refine ⟨((toW hW u : ↥(Tim79a.xOf V H)) : G), hu'V, hu'W, hu'ne, ?_⟩
  rw [← hu_comm]
  exact hdV

private theorem commutator_commutator_u_Pc_x_eq_one
    (h : RootHyp M V) {x : ↥H} (hx : (x : G) ∈ Pc M V)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {u' : G} (hu'W : u' ∈ Tim79a.xOf V H) (hu'ne : u' ≠ 1)
    (hxu'V : ⁅(x : G), u'⁆ ∈ V) :
    ∀ p ∈ Pc M V, ⁅⁅u', p⁆, (x : G)⁆ = 1 := by
  classical
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hPP : ⁅Pc M V, Pc M V⁆ ≤ inSubgroup frattini (Pc M V) := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact Tim78.commutatorElement_mem_inSubgroup_frattini hP2 ha hb
  have hPx : ⁅Pc M V, Subgroup.zpowers (x : G)⁆ ≤ V :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hx)).trans
      (hPP.trans h.toHyp.frattini_Pc_le)
  have hu'2 : u' * u' = 1 := by
    have h := hW.2 u' hu'W
    rwa [pow_two] at h
  have hu'order : orderOf u' = 2 := orderOf_eq_prime (by rwa [pow_two]) hu'ne
  have hVcentZ : V ≤ Subgroup.centralizer (Subgroup.zpowers u' : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact congrArg Subtype.val (hW.1.is_comm.comm
      ⟨v, le_xOf_self V H hv⟩ ⟨u', hu'W⟩)
  have h1 : ⁅⁅Pc M V, Subgroup.zpowers (x : G)⁆, Subgroup.zpowers u'⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hPx.trans hVcentZ)
  have hxN : (x : G) ∈ Subgroup.normalizer (V : Set G) :=
    h.toHyp.le_normalizer (h.toHyp.Pc_le_M hx)
  have hLnorm : Subgroup.zpowers (x : G) ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  let L : Subgroup G := Subgroup.zpowers (x : G)
  let C : Subgroup G := CFSG.GroupTheory.commMemSubgroup L V hLnorm u'
  have hxC : (x : G) ∈ C := ⟨Subgroup.mem_zpowers (x : G), hxu'V⟩
  have hLC : L ≤ C := Subgroup.zpowers_le.mpr hxC
  have hu'_le : ⁅L, Subgroup.zpowers u'⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hb' : b = 1 ∨ b = u' :=
      CFSG.OddStandard.eq_one_or_eq_of_mem_zpowers_of_mul_self hu'2 hb
    rcases hb' with rfl | rfl
    · simp
    · exact (hLC ha).2
  have hVcentP : V ≤ Subgroup.centralizer (Pc M V : Set G) := by
    rw [h.toHyp.centralizer_Pc]
  have h2 : ⁅⁅Subgroup.zpowers (x : G), Subgroup.zpowers u'⁆, Pc M V⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hu'_le.trans hVcentP)
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := Subgroup.zpowers u') (H₂ := Pc M V) (H₃ := Subgroup.zpowers (x : G)) h1 h2
  intro p hp
  have hmem : ⁅u', p⁆ ∈ ⁅Subgroup.zpowers u', Pc M V⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u') hp
  have hxmem : (x : G) ∈ Subgroup.zpowers (x : G) := Subgroup.mem_zpowers (x : G)
  have hmem2 : ⁅⁅u', p⁆, (x : G)⁆ ∈ (⊥ : Subgroup G) := by
    rw [← h3]
    exact Subgroup.commutator_mem_commutator hmem hxmem
  exact Subgroup.mem_bot.mp hmem2


private theorem exists_decomp_commutator_u_z
    (h : RootHyp M V)
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    {x : ↥H} {u' z : G} (hx : (x : G) ∈ Pc M V)
    (hzP : z ∈ Pc M V)
    (hL8 : ∀ p ∈ Pc M V, ⁅⁅u', p⁆, (x : G)⁆ = 1)
    (hc_mem : ⁅u', z⁆ ∈ Pc M V ⊓ Tim79a.xOf V H)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀)) :
    ∃ v' w₀ : G, v' ∈ V ∧ w₀ ∈ Pc M V ⊓ W₀ ∧
      ⁅u', z⁆ = v' * w₀ ∧ (x : G) * w₀ = w₀ * (x : G) := by
  classical
  have hcommVW0 : ∀ a ∈ V, ∀ b ∈ Pc M V ⊓ W₀, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hW.1.is_comm.comm
      ⟨a, le_xOf_self V H ha⟩ ⟨b, hW₀ hb.2⟩)
  obtain ⟨v', hv'V, w₀, hw₀, hv'w⟩ := exists_mul_of_mem_sup
    (V := V) (U := Pc M V ⊓ W₀)
    (le_normalizer_of_comm fun b hb a ha => (hcommVW0 a ha b hb).symm)
    (hstar hc_mem)
  have hw₀W : w₀ ∈ Tim79a.xOf V H := hW₀ hw₀.2
  have hPcentV : Pc M V ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.le_centralizer_iff, h.toHyp.centralizer_Pc]
  have hx_c : (x : G) * ⁅u', z⁆ = ⁅u', z⁆ * (x : G) :=
    ((commutatorElement_eq_one_iff_mul_comm (g₁ := ⁅u', z⁆) (g₂ := (x : G))).mp
      (hL8 z hzP)).symm
  have hx_v' : (x : G) * v' = v' * (x : G) :=
    (Subgroup.mem_centralizer_iff.mp (hPcentV hx) v' hv'V).symm
  have hv'w₀ : v' * w₀ = w₀ * v' :=
    congrArg Subtype.val (hW.1.is_comm.comm ⟨v', le_xOf_self V H hv'V⟩ ⟨w₀, hw₀W⟩)
  have hx_w₀ : (x : G) * w₀ = w₀ * (x : G) := by
    have h1 : (x : G) * (v' * w₀) = (v' * w₀) * (x : G) := by rw [← hv'w, hx_c]
    rw [← mul_assoc, hx_v', mul_assoc, mul_assoc] at h1
    exact mul_left_cancel h1
  exact ⟨v', w₀, hv'V, hw₀, hv'w, hx_w₀⟩

private theorem commute_z_of_commutator_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H)
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {u' : G} (hu'W : u' ∈ Tim79a.xOf V H)
    {z : ↥H} (hzP : (z : G) ∈ Pc M V)
    (hz_u'_W : ⁅(z : G), u'⁆ ∈ Tim79a.xOf V H)
    {v' w₀ : G} (hv'V : v' ∈ V) (hv'w : ⁅u', (z : G)⁆ = v' * w₀) :
    (z : G) * w₀ = w₀ * (z : G) := by
  classical
  have hP2 : IsPGroup 2 (Pc M V) := (inSubgroup_pCore_two M).1.to_le inf_le_left
  have hz2V : (z : G) * (z : G) ∈ V := by
    have hfr := Tim78.sq_mem_inSubgroup_frattini hP2 hzP
    have h' := h.toHyp.frattini_Pc_le hfr
    simpa [pow_two] using h'
  have hzK : (z : G) * (z : G) ∈ kOf V H := le_kOf h hPH hVH hz2V
  have hu'2 : u' * u' = 1 := by
    have h := hW.2 u' hu'W
    rwa [pow_two] at h
  have hz_c : (z : G) * ⁅u', (z : G)⁆ = ⁅u', (z : G)⁆ * (z : G) := by
    have hzpi : ψ (piK V H z) * ψ (piK V H z) = 1 := by
      have h1 : piK V H (z * z) = 1 :=
        (piK_eq_one_iff (z * z)).mpr (by simpa [pow_two] using hzK)
      rw [← map_mul, ← map_mul, h1, map_one]
    have hzero := CFSG.RankThree.GF2n.sub_one_apply_sub_one_apply
      (a := repW hW ψ (ψ (piK V H z))) (by rw [← map_mul, hzpi, map_one])
      (ofW hW ⟨u', hu'W⟩)
    have hdiff : (repW hW ψ (ψ (piK V H z)) - 1) (ofW hW ⟨u', hu'W⟩) =
        ofW hW ⟨⁅(z : G), u'⁆, hz_u'_W⟩ := by
      simpa using repW_apply_piK_sub (hW := hW) (ψ := ψ) z ⟨u', hu'W⟩
    have hfix : repW hW ψ (ψ (piK V H z)) (ofW hW ⟨⁅(z : G), u'⁆, hz_u'_W⟩) =
        ofW hW ⟨⁅(z : G), u'⁆, hz_u'_W⟩ := by
      have h0 : (repW hW ψ (ψ (piK V H z)) - 1)
          (ofW hW ⟨⁅(z : G), u'⁆, hz_u'_W⟩) = 0 := by
        rw [← hdiff]
        exact hzero
      exact sub_eq_zero.mp h0
    have hzc : Commute (z : G) ⁅(z : G), u'⁆ := by
      have h1 := congrArg (toW hW) hfix
      rw [repW_apply_piK, toW_ofW] at h1
      have h2 : (z : G) * ((toW hW (ofW hW ⟨⁅(z : G), u'⁆, hz_u'_W⟩) :
          ↥(Tim79a.xOf V H)) : G) * (z : G)⁻¹ =
          ((toW hW (ofW hW ⟨⁅(z : G), u'⁆, hz_u'_W⟩) :
            ↥(Tim79a.xOf V H)) : G) := by
        rw [← conjH_apply_coe]
        exact congrArg (fun w : ↥(Tim79a.xOf V H) => (w : G)) h1
      rw [toW_ofW] at h2
      calc (z : G) * ⁅(z : G), u'⁆ = ((z : G) * ⁅(z : G), u'⁆ * (z : G)⁻¹) * (z : G) := by
            group
        _ = ⁅(z : G), u'⁆ * (z : G) := by rw [h2]
    have hcomm_inv' : ⁅u', (z : G)⁆ = (⁅(z : G), u'⁆)⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [hcomm_inv']
    exact hzc.inv_right
  have hPcentV : Pc M V ≤ Subgroup.centralizer (V : Set G) := by
    rw [← Subgroup.le_centralizer_iff, h.toHyp.centralizer_Pc]
  have hz_v' : (z : G) * v' = v' * (z : G) :=
    (Subgroup.mem_centralizer_iff.mp (hPcentV hzP) v' hv'V).symm
  have h1 : (z : G) * (v' * w₀) = (v' * w₀) * (z : G) := by rw [← hv'w, hz_c]
  rw [← mul_assoc, hz_v', mul_assoc, mul_assoc] at h1
  exact mul_left_cancel h1

private theorem mem_V_of_fixed_of_fixedSub
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {F : Type} [Field F] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    {x z : ↥H} {w₀ : G} (hw₀ : w₀ ∈ Pc M V ⊓ W₀)
    (hx_w₀ : (x : G) * w₀ = w₀ * (x : G))
    (hz_w₀ : (z : G) * w₀ = w₀ * (z : G))
    (hzZ : fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H x))) ⊓
        fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H z))) =
        fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H (Pc M V)).map ψ)) :
    w₀ ∈ V := by
  classical
  have hw₀W : w₀ ∈ Tim79a.xOf V H := hW₀ hw₀.2
  have hw₀_mem : ofW hW ⟨w₀, hw₀W⟩ ∈ subW hW W₀ := by
    change ((toW hW (ofW hW ⟨w₀, hw₀W⟩) : ↥(Tim79a.xOf V H)) : G) ∈ W₀
    rw [toW_ofW]
    exact hw₀.2
  have hfix_x : (⟨ofW hW ⟨w₀, hw₀W⟩, hw₀_mem⟩ : subW hW W₀) ∈
      fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H x))) := by
    rw [mem_fixedSub_zpowers]
    apply Subtype.ext
    rw [show subRepW hW ψ hW₀ hN =
        CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW W₀)
          ((normalizer_subW_iff hW ψ hW₀).mp hN) from rfl,
      CFSG.Quasithin.B45U33.subRep_apply, repW_apply_piK, toW_ofW]
    congr 1
    apply Subtype.ext
    rw [conjH_apply_coe]
    calc (x : G) * w₀ * (x : G)⁻¹ = (w₀ * (x : G)) * (x : G)⁻¹ := by rw [hx_w₀]
      _ = w₀ := by group
  have hfix_z : (⟨ofW hW ⟨w₀, hw₀W⟩, hw₀_mem⟩ : subW hW W₀) ∈
      fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H z))) := by
    rw [mem_fixedSub_zpowers]
    apply Subtype.ext
    rw [show subRepW hW ψ hW₀ hN =
        CFSG.Quasithin.B45U33.subRep (repW hW ψ) (subW hW W₀)
          ((normalizer_subW_iff hW ψ hW₀).mp hN) from rfl,
      CFSG.Quasithin.B45U33.subRep_apply, repW_apply_piK, toW_ofW]
    congr 1
    apply Subtype.ext
    rw [conjH_apply_coe]
    calc (z : G) * w₀ * (z : G)⁻¹ = (w₀ * (z : G)) * (z : G)⁻¹ := by rw [hz_w₀]
      _ = w₀ := by group
  have hfix_S : (⟨ofW hW ⟨w₀, hw₀W⟩, hw₀_mem⟩ : subW hW W₀) ∈
      fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H (Pc M V)).map ψ) := by
    rw [← hzZ]
    exact Submodule.mem_inf.mpr ⟨hfix_x, hfix_z⟩
  have hmap := fixedSub_subRepW hW ψ hW₀ hN (S := Pc M V) hPH
  have hmem : (ofW hW ⟨w₀, hw₀W⟩) ∈ (fixedSub (subRepW hW ψ hW₀ hN)
      ((imgK V H (Pc M V)).map ψ)).map (subW hW W₀).subtype :=
    Submodule.mem_map.mpr ⟨⟨ofW hW ⟨w₀, hw₀W⟩, hw₀_mem⟩, hfix_S, rfl⟩
  rw [hmap] at hmem
  rw [inf_centralizer_Pc_eq_inf (h := h)] at hmem
  have h1 : w₀ ∈ V ⊓ W₀ := by
    have h2 := hmem
    change ((toW hW (ofW hW ⟨w₀, hw₀W⟩) : ↥(Tim79a.xOf V H)) : G) ∈ V ⊓ W₀
    rw [toW_ofW]
    exact h2
  exact h1.1

private theorem commutator_u_z_mem_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    {u' : G} (hu'V : u' ∈ conjSubgroup (y : G) V)
    (hu'W : u' ∈ Tim79a.xOf V H)
    (hL8 : ∀ p ∈ Pc M V, ⁅⁅u', p⁆, (x : G)⁆ = 1)
    {z : ↥H} (hzP : (z : G) ∈ Pc M V)
    (hzZ : ψ (piK V H z) ∈ (imgK V H (Pc M V)).map ψ ∧
      fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H x))) ⊓
        fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H z))) =
        fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H (Pc M V)).map ψ)) :
    ⁅u', (z : G)⁆ ∈ V := by
  classical
  have hPyH : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
  have hyH : (y : G) ∈ H := hPyH hy
  have hu'M : u' ∈ M :=
    kOf_le_M h (conjSubgroup_le_kOf_of_mem h hPH hVH hyH hu'V)
  have hzW : (z : G) ∈ Subgroup.normalizer (Tim79a.xOf V H : Set G) :=
    Tim79a.H_le_normalizer_xOf V H z.2
  have hz_u'_W : ⁅(z : G), u'⁆ ∈ Tim79a.xOf V H := by
    have h1 : (z : G) * u' * (z : G)⁻¹ ∈ Tim79a.xOf V H :=
      (Subgroup.mem_normalizer_iff.mp hzW u').mp hu'W
    rw [commutatorElement_def]
    exact (Tim79a.xOf V H).mul_mem h1 ((Tim79a.xOf V H).inv_mem hu'W)
  have hcomm_inv : ⁅u', (z : G)⁆ = (⁅(z : G), u'⁆)⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    group
  have hu'_z_W : ⁅u', (z : G)⁆ ∈ Tim79a.xOf V H := by
    rw [hcomm_inv]
    exact (Tim79a.xOf V H).inv_mem hz_u'_W
  have hu'_z_P : ⁅u', (z : G)⁆ ∈ Pc M V := by
    have hu'N : u' ∈ Subgroup.normalizer (Pc M V : Set G) :=
      h.toHyp.le_normalizer_Pc hu'M
    have h1 : u' * (z : G) * u'⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp hu'N (z : G)).mp hzP
    rw [commutatorElement_def]
    exact (Pc M V).mul_mem h1 ((Pc M V).inv_mem hzP)
  have hc_mem : ⁅u', (z : G)⁆ ∈ Pc M V ⊓ Tim79a.xOf V H := ⟨hu'_z_P, hu'_z_W⟩
  obtain ⟨v', w₀, hv'V, hw₀, hv'w, hx_w₀⟩ :=
    exists_decomp_commutator_u_z h hW₀ hx hzP hL8 hc_mem hstar
  have hz_w₀ := commute_z_of_commutator_eq h hPH hVH ψ hu'W hzP hz_u'_W hv'V hv'w
  have hw₀V := mem_V_of_fixed_of_fixedSub h hPH ψ hW₀ hN hw₀ hx_w₀ hz_w₀ hzZ.2
  rw [hv'w]
  exact V.mul_mem hv'V hw₀V

private theorem exists_commMemSubgroup_le
    (h : RootHyp M V) {u' : G} (hu'W : u' ∈ Tim79a.xOf V H) :
    ∃ P₁ : Subgroup G, P₁ ≤ Pc M V ∧ (∀ p ∈ P₁, ⁅u', p⁆ ∈ V) ∧
      (∀ p : ↥H, (p : G) ∈ Pc M V → ⁅(p : G), u'⁆ ∈ V → (p : G) ∈ P₁) ∧
      Pc M V ⊓ kOf V H ≤ P₁ := by
  classical
  let P₁ : Subgroup G := CFSG.GroupTheory.commMemSubgroup (Pc M V) V
    (fun p hp => h.toHyp.le_normalizer (h.toHyp.Pc_le_M hp)) u'
  have hP₁P : P₁ ≤ Pc M V := fun p hp => hp.1
  have hP₁V : ∀ p ∈ P₁, ⁅u', p⁆ ∈ V := by
    intro p hp
    rw [← inv_inv ⁅u', p⁆, commutatorElement_inv]
    exact V.inv_mem hp.2
  have hPK_le : Pc M V ⊓ kOf V H ≤ P₁ := by
    intro p hp
    refine ⟨hp.1, ?_⟩
    have hcent := (mem_kOf_iff.mp hp.2).2
    have hcomm : u' * p = p * u' :=
      Subgroup.mem_centralizer_iff.mp hcent u' hu'W
    have h1 : ⁅p, u'⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
    rw [h1]
    exact V.one_mem
  have hP₁mem : ∀ p : ↥H, (p : G) ∈ Pc M V → ⁅(p : G), u'⁆ ∈ V → (p : G) ∈ P₁ :=
    fun p hp hpV => ⟨hp, hpV⟩
  exact ⟨P₁, hP₁P, hP₁V, hP₁mem, hPK_le⟩

private theorem imgK_le_of_closure_subset
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V) (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha1 : ψ (piK V H x) ≠ 1)
    {u' : G} (hu'V : u' ∈ conjSubgroup (y : G) V)
    (hu'W : u' ∈ Tim79a.xOf V H)
    (hL8 : ∀ p ∈ Pc M V, ⁅⁅u', p⁆, (x : G)⁆ = 1)
    {P₁ : Subgroup G}
    (hP₁mem : ∀ p : ↥H, (p : G) ∈ Pc M V → ⁅(p : G), u'⁆ ∈ V → (p : G) ∈ P₁) :
    (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) ≤
      (imgK V H P₁).map (ψ : HBar V H →* SL(2, F)) := by
  set S : Subgroup (SL(2, F)) := (imgK V H (Pc M V)).map ψ with hSdef
  set S' : Subgroup (SL(2, F)) := (imgK V H (conjSubgroup h₀ (Pc M V))).map ψ with hS'def
  set Zbar : Set (SL(2, F)) := {w | w ∈ S ∧
    fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H x))) ⊓
      fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers w) =
      fixedSub (subRepW hW ψ hW₀ hN) S} with hZbardef
  obtain ⟨a₀, b₀, hS_eq, hS'_eq, hS2, hS'2, hScard, hS'card, hSne, haS, hbS'⟩ :=
    sec_data h hPH hVH hH hnM ψ hl hx hy S S' hSdef hS'def
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hclosure : S = Subgroup.closure Zbar :=
    horth.eq_closure_fixedSub_zpowers (hF := hl) S S' hS2 hScard hS'2 hS'card hSne
      (x := ψ (piK V H x)) haS ha1
  have hZ_le : Zbar ⊆ ((imgK V H P₁).map ψ).carrier := by
    intro w hw
    have hwS : w ∈ (imgK V H (Pc M V)).map ψ := by
      rw [← hSdef]
      exact hw.1
    obtain ⟨ybar, hybar, hyw⟩ := Subgroup.mem_map.mp hwS
    obtain ⟨z, hzP, hzpi⟩ := (mem_imgK_iff).mp hybar
    have hzpsi : ψ (piK V H z) = w := by
      rw [hzpi]
      exact hyw
    have hzZ : ψ (piK V H z) ∈ (imgK V H (Pc M V)).map ψ ∧
        fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H x))) ⊓
          fixedSub (subRepW hW ψ hW₀ hN) (Subgroup.zpowers (ψ (piK V H z))) =
          fixedSub (subRepW hW ψ hW₀ hN) ((imgK V H (Pc M V)).map ψ) := by
      refine ⟨?_, ?_⟩
      · rw [hzpsi]
        exact hw.1
      · rw [hzpsi]
        exact hw.2
    have hzu'V : ⁅u', (z : G)⁆ ∈ V :=
      commutator_u_z_mem_V h hPH hVH hH ψ hW₀ hN hstar hx hy
        hu'V hu'W hL8 hzP hzZ
    have hzu'V' : ⁅(z : G), u'⁆ ∈ V := by
      rw [← inv_inv ⁅(z : G), u'⁆, commutatorElement_inv]
      exact V.inv_mem hzu'V
    refine Subgroup.mem_map.mpr ⟨piK V H z, ?_, hzpsi⟩
    exact (mem_imgK_iff).mpr ⟨z, hP₁mem z hzP hzu'V', rfl⟩
  have hS_le : S ≤ (imgK V H P₁).map (ψ : HBar V H →* SL(2, F)) := by
    rw [← MulEquiv.toMonoidHom_eq_coe ψ]
    rw [hclosure]
    have hZ_le' : Zbar ⊆ ((imgK V H P₁).map ψ.toMonoidHom).carrier := by
      rwa [← MulEquiv.toMonoidHom_eq_coe ψ] at hZ_le
    exact (Subgroup.closure_le (K := (imgK V H P₁).map ψ.toMonoidHom)).mpr hZ_le'
  exact hS_le

private theorem commutator_zpowers_le_of_imgK_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {u' : G} (hu'W : u' ∈ Tim79a.xOf V H)
    {P₁ : Subgroup G} (hP₁P : P₁ ≤ Pc M V)
    (hP₁V : ∀ p ∈ P₁, ⁅u', p⁆ ∈ V)
    (hPK_le : Pc M V ⊓ kOf V H ≤ P₁)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    (hS_le : (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) ≤
      (imgK V H P₁).map (ψ : HBar V H →* SL(2, F))) :
    ⁅Subgroup.zpowers u', Pc M V⁆ ≤ V := by
  classical
  set S : Subgroup (SL(2, F)) := (imgK V H (Pc M V)).map ψ with hSdef
  have hmap_le : (imgK V H P₁).map ψ ≤ S := by
    rw [hSdef]
    exact Subgroup.map_mono (f := (ψ : HBar V H →* SL(2, F))) (imgK_mono hP₁P)
  have hSeq : (imgK V H P₁).map (ψ : HBar V H →* SL(2, F)) =
      (imgK V H (Pc M V)).map (ψ : HBar V H →* SL(2, F)) := by
    rw [← hSdef]
    exact le_antisymm hmap_le hS_le
  have himg : imgK V H P₁ = imgK V H (Pc M V) :=
    Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (by simpa using hSeq)
  have hP₁H : P₁ ≤ H := hP₁P.trans hPH
  have hsup : P₁ ⊔ kOf V H = Pc M V ⊔ kOf V H :=
    (imgK_eq_iff_sup_kOf_eq (V := V) (H := H) hP₁H hPH).mp himg
  have hP_le_P₁ : Pc M V ≤ P₁ := by
    intro p hp
    have hmem : p ∈ P₁ ⊔ kOf V H := by
      rw [hsup]
      exact Subgroup.mem_sup_left hp
    rw [sup_comm] at hmem
    obtain ⟨k, hkK, a, haP₁, hka⟩ := exists_mul_of_mem_sup
      (V := kOf V H) (U := P₁) (hP₁H.trans (le_normalizer_kOf V H)) hmem
    have hkP : k ∈ Pc M V := by
      have hk_eq : k = p * a⁻¹ := by rw [hka]; group
      rw [hk_eq]
      exact (Pc M V).mul_mem hp ((Pc M V).inv_mem (hP₁P haP₁))
    have hkP₁ : k ∈ P₁ := hPK_le ⟨hkP, hkK⟩
    rw [hka]
    exact P₁.mul_mem hkP₁ haP₁
  have hP₁_eq : P₁ = Pc M V := le_antisymm hP₁P hP_le_P₁
  have hu'2 : u' * u' = 1 := by
    have h := hW.2 u' hu'W
    rwa [pow_two] at h
  rw [Subgroup.commutator_le]
  intro a ha p hp
  have ha' : a = 1 ∨ a = u' :=
    CFSG.OddStandard.eq_one_or_eq_of_mem_zpowers_of_mul_self hu'2 ha
  rcases ha' with rfl | rfl
  · simp
  · exact hP₁V p (hP₁_eq ▸ hp)

private theorem commutator_u_Pc_le_V
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H)
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀))
    {x y : ↥H} (hx : (x : G) ∈ Pc M V)
    (hy : (y : G) ∈ conjSubgroup h₀ (Pc M V))
    (ha1 : ψ (piK V H x) ≠ 1)
    {u' : G} (hu'V : u' ∈ conjSubgroup (y : G) V)
    (hu'W : u' ∈ Tim79a.xOf V H)
    (hL8 : ∀ p ∈ Pc M V, ⁅⁅u', p⁆, (x : G)⁆ = 1) :
    ⁅Subgroup.zpowers u', Pc M V⁆ ≤ V := by
  classical
  obtain ⟨P₁, hP₁P, hP₁V, hP₁mem, hPK_le⟩ := exists_commMemSubgroup_le h hu'W
  have hS_le := imgK_le_of_closure_subset h hPH hVH hH hnM ψ hl hW₀ hN horth hstar
    hx hy ha1 hu'V hu'W hL8 hP₁mem
  exact commutator_zpowers_le_of_imgK_le h hPH hW hu'W hP₁P hP₁V hPK_le ψ hS_le

private theorem mem_Pc_of_mem_conj_of_commutator_le
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V))
    (hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H))
    {y u' : G} (hy : y ∈ conjSubgroup h₀ (Pc M V))
    (hu'V : u' ∈ conjSubgroup y V) (hu'W : u' ∈ Tim79a.xOf V H)
    (hcomm : ⁅Subgroup.zpowers u', Pc M V⁆ ≤ V) : u' ∈ Pc M V := by
  have hPyH : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
  have hyH : y ∈ H := hPyH hy
  have hu'M : u' ∈ M :=
    kOf_le_M h (conjSubgroup_le_kOf_of_mem h hPH hVH hyH hu'V)
  have hu'centV : u' ∈ Subgroup.centralizer (V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (congrArg Subtype.val (hW.1.is_comm.comm
      ⟨u', hu'W⟩ ⟨v, le_xOf_self V H hv⟩)).symm
  have hPcomm : ⁅Pc M V, Subgroup.zpowers u'⁆ ≤ V := by
    rwa [Subgroup.commutator_comm] at hcomm
  have hStab : Subgroup.zpowers u' ≤ inSubgroup (pCore 2) M :=
    h.toHyp.le_pCore_of_commutator_le (Subgroup.zpowers_le.mpr hu'M)
      (Subgroup.zpowers_le.mpr hu'centV) hPcomm
  have hu'Q : u' ∈ inSubgroup (pCore 2) M := hStab (Subgroup.mem_zpowers u')
  exact Subgroup.mem_inf.mpr ⟨hu'Q, hu'centV⟩

private theorem conjSubgroup_eq_of_mem_conj_of_mem_Pc (h : RootHyp M V)
    {y u' : G} (hu'V : u' ∈ conjSubgroup y V) (hu'P : u' ∈ Pc M V) (hu'ne : u' ≠ 1) :
    conjSubgroup y V = V := by
  have hu''V : y⁻¹ * u' * y ∈ V := mem_conjSubgroup.mp hu'V
  have hu''P : y⁻¹ * u' * y ∈ conjSubgroup y⁻¹ (Pc M V) := by
    rw [mem_conjSubgroup]
    rw [show (y⁻¹)⁻¹ * (y⁻¹ * u' * y) * y⁻¹ = u' by group]
    exact hu'P
  have hu''ne : y⁻¹ * u' * y ≠ 1 := by
    intro h1
    apply hu'ne
    calc u' = y * (y⁻¹ * u' * y) * y⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hne : V ⊓ conjSubgroup y⁻¹ (Pc M V) ≠ ⊥ := by
    intro hbot
    have hmem : y⁻¹ * u' * y ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hu''V, hu''P⟩
    exact hu''ne (Subgroup.mem_bot.mp hmem)
  have hconj_inv : conjSubgroup y⁻¹ V = V := conj_eq_of_inf_conj_Pc_ne_bot h hne
  have hconj : conjSubgroup y V = V := by
    have h1 : conjSubgroup y (conjSubgroup y⁻¹ V) = conjSubgroup y V := by
      rw [hconj_inv]
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CFSG.CGT.Timmesfeld75.conjSubgroup_one] at h1
    exact h1.symm
  exact hconj

private theorem piK_eq_one_of_conjSubgroup_eq
    (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {y : G} (hyH : y ∈ H) (hy : y ∈ conjSubgroup h₀ (Pc M V))
    (hconj : conjSubgroup y V = V) : piK V H ⟨y, hyH⟩ = 1 := by
  have hyM : y ∈ M := by
    rw [← h.toHyp.normalizer_eq]
    exact conjSubgroup_eq_self_iff.mp hconj
  have hyNP : y ∈ Subgroup.normalizer (Pc M V : Set G) :=
    h.toHyp.le_normalizer_Pc hyM
  have hconjP : conjSubgroup y (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr hyNP
  have hpiN : piK V H ⟨y, hyH⟩ ∈
      Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
    rw [← conjSubgroup_eq_self_iff]
    have h1 := imgK_conjSubgroup (V := V) (H := H) (S := Pc M V) hyH hPH
    rw [hconjP] at h1
    exact h1.symm
  have hpiMem : piK V H ⟨y, hyH⟩ ∈ imgK V H (conjSubgroup h₀ (Pc M V)) :=
    (mem_imgK_iff).mpr ⟨⟨y, hyH⟩, hy, rfl⟩
  have hbot := imgK_conj_inf_normalizer_eq_bot_of_sl2 h hPH hH hnM ψ
  have hmem : piK V H ⟨y, hyH⟩ ∈ (⊥ : Subgroup (HBar V H)) := by
    rw [← hbot]
    exact ⟨hpiMem, hpiN⟩
  exact Subgroup.mem_bot.mp hmem

theorem le_of_isOrthModule
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    {F : Type} [Field F] [Fintype F] [CharP F 2] (ψ : HBar V H ≃* SL(2, F))
    {l : ℕ} (hl : Fintype.card F = 2 ^ (2 * l))
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    {W₀ : Subgroup G} (hW₀ : W₀ ≤ Tim79a.xOf V H) (hN : H ≤ Subgroup.normalizer (W₀ : Set G))
    (horth : Sec2.IsOrthModule hl (subRepW hW ψ hW₀ hN))
    (hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆)
    (hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀)) :
    V ≤ W₀ := by
  classical
  by_contra hle
  obtain ⟨s, hs, hsW0⟩ := Set.not_subset.mp hle
  obtain ⟨x, hx, y, hy, ha1', hb1', ha2', hb2', hord⟩ :=
    exists_order_three_pair h hPH hVH hH hnM ψ
  have ha1 : ψ (piK V H x) ≠ 1 := fun h1 => ha1' (ψ.injective (by simpa using h1))
  have hb1 : ψ (piK V H y) ≠ 1 := fun h1 => hb1' (ψ.injective (by simpa using h1))
  have ha2 : ψ (piK V H x) * ψ (piK V H x) = 1 := by
    rw [← map_mul, ha2', map_one]
  have hb2 : ψ (piK V H y) * ψ (piK V H y) = 1 := by
    rw [← map_mul, hb2', map_one]
  obtain ⟨u', hu'V, hu'W, hu'ne, hxu'V⟩ :=
    exists_u h hPH hVH hH hnM ψ hl hW₀ hN horth hPW hstar hx hy
      ha1 ha2 hb2 hb1 hord hs hsW0
  have hL8 := commutator_commutator_u_Pc_x_eq_one h hx hW hu'W hu'ne hxu'V
  have hcomm := commutator_u_Pc_le_V h hPH hVH hH hnM ψ hl hW₀ hN horth hstar
    hx hy ha1 hu'V hu'W hL8
  have hu'P := mem_Pc_of_mem_conj_of_commutator_le h hPH hVH hH hW hy hu'V hu'W hcomm
  have hconj := conjSubgroup_eq_of_mem_conj_of_mem_Pc h hu'V hu'P hu'ne
  have hPyH : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
  have hpi1 := piK_eq_one_of_conjSubgroup_eq h hPH hH hnM ψ y.2 hy hconj
  exact hb1 (by rw [hpi1, map_one])

end RootHyp

end CFSG.RankThree.GF2n.Tim81

end
