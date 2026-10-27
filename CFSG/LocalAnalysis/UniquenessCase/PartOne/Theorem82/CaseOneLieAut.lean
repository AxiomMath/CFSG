module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLieCross
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseOneLieChar
import CFSG.GroupTheory.PGroup.CentralizeE27

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Case811Sylow

private theorem signed_e2_ne_smul_e1 :
    ∀ t : ZMod 3, (![0, 1, 0] : Fin 3 → ZMod 3) ≠
      fun i => t * ![1, 0, 0] i := by
  decide

private theorem signed_perm_e1_ne_e123 :
    ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod 3), (∀ i, ε i ≠ 0) →
      ∀ t : ZMod 3,
        (fun i => ε i * ![1, 0, 0] (σ i)) ≠
          fun i => t * ![1, 1, 1] i := by
  decide

private theorem sumZero_z2_swap_not_same :
    ∀ t d : ZMod 3,
      (![1, 0, -1, 0] : Fin 4 → ZMod 3) ≠
        fun i => t * ![1, -1, 0, 0] i + d := by
  decide

private theorem sumZero_perm_z2_ne_z1 :
    ∀ (σ : Equiv.Perm (Fin 4)) (t d : ZMod 3),
      (fun i => ![1, -1, 0, 0] (σ i)) ≠
        fun i => t * ![1, 1, -1, -1] i + d := by
  decide

private theorem sumZero_z1_nonconstant :
    ¬ ∃ d : ZMod 3, (![1, 1, -1, -1] : Fin 4 → ZMod 3) = fun _ => d := by
  decide

private theorem sumZero_z2_nonconstant :
    ¬ ∃ d : ZMod 3, (![1, -1, 0, 0] : Fin 4 → ZMod 3) = fun _ => d := by
  decide

private lemma map_mem_normalizer_lbar {c : Counterexample4 G} (h : Case811Sylow c)
    {k : G} (hkL : k ∈ c.L) (hkN : k ∈ Subgroup.normalizer (h.A : Set G)) :
    QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨k, hkL⟩ ∈
      Subgroup.normalizer (h.Abar : Set c.Lbar) := by
  have hkSub : (⟨k, hkL⟩ : ↥c.L) ∈
      (Subgroup.normalizer (h.A : Set G)).subgroupOf c.L :=
    Subgroup.mem_subgroupOf.mpr hkN
  rw [Subgroup.subgroupOf_normalizer_eq (h.A_le.trans h.P_le_L)] at hkSub
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L))
    (Subgroup.mem_map_of_mem _ hkSub)

private lemma conj_apply_of_mem_normalizer {c : Counterexample4 G} (h : Case811Sylow c)
    {V : Type*} [Group V] (a : V →* ↥c.L)
    {c₀ : V →* c.Lbar}
    (ha_range : a.range = h.A.subgroupOf c.L)
    (ha_apply : ∀ v, QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) (a v) = c₀ v)
    (hXinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)).comp (h.A.subgroupOf c.L).subtype))
    {k : G} (hkL : k ∈ c.L) (hkN : k ∈ Subgroup.normalizer (h.A : Set G))
    {n : c.Lbar}
    (hnπ : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨k, hkL⟩ = n)
    {φ : V → V} (hform : ∀ v, n * c₀ v * n⁻¹ = c₀ (φ v)) :
    ∀ v, k * ((a v : ↥c.L) : G) * k⁻¹ = ((a (φ v) : ↥c.L) : G) := by
  classical
  let π : ↥c.L →* c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L)
  have hkNAL : (⟨k, hkL⟩ : ↥c.L) ∈
      Subgroup.normalizer (h.A.subgroupOf c.L : Set ↥c.L) := by
    have hkSub : (⟨k, hkL⟩ : ↥c.L) ∈
        (Subgroup.normalizer (h.A : Set G)).subgroupOf c.L :=
      Subgroup.mem_subgroupOf.mpr hkN
    rwa [Subgroup.subgroupOf_normalizer_eq (h.A_le.trans h.P_le_L)] at hkSub
  intro v
  have havAL : a v ∈ h.A.subgroupOf c.L := by
    have hav : a v ∈ a.range := MonoidHom.mem_range.mpr ⟨v, rfl⟩
    rwa [ha_range] at hav
  let x : ↥c.L := ⟨k, hkL⟩ * a v * ⟨k, hkL⟩⁻¹
  have hxAL : x ∈ h.A.subgroupOf c.L :=
    (Subgroup.mem_normalizer_iff.mp hkNAL (a v)).mp havAL
  have hφAL : a (φ v) ∈ h.A.subgroupOf c.L := by
    have hφ : a (φ v) ∈ a.range := MonoidHom.mem_range.mpr ⟨φ v, rfl⟩
    rwa [ha_range] at hφ
  have himg : π x = π (a (φ v)) := by
    show π (⟨k, hkL⟩ * a v * ⟨k, hkL⟩⁻¹) = π (a (φ v))
    rw [map_mul, map_mul, map_inv, hnπ, ha_apply, hform, ha_apply]
  have hxeq : x = a (φ v) := by
    have hsub : (⟨x, hxAL⟩ : h.A.subgroupOf c.L) = ⟨a (φ v), hφAL⟩ :=
      hXinj (by simpa [π] using himg)
    exact congrArg Subtype.val hsub
  have := congrArg (fun z : ↥c.L => (z : G)) hxeq
  simpa [x] using this

private lemma exists_moving_point_signed {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f)
    (hfam : fam ≠ .l4) :
    ∃ X Y : Subgroup G, X ≤ h.A ∧ Y ≤ h.A ∧ Nat.card X = 3 ∧ Nat.card Y = 3 ∧
      (∃ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
        X.map (MulAut.conj k).toMonoidHom ≠ X) ∧
      (∀ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
        X.map (MulAut.conj k).toMonoidHom ≠ Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_inj, ha_memA, ha_order⟩ :=
    h.signed_coords_setup hK6c hlie hfam
  let aG : Multiplicative (Fin 3 → ZMod 3) → G := fun v => ((a v : ↥c.L) : G)
  let e1 : Fin 3 → ZMod 3 := ![1, 0, 0]
  let e2 : Fin 3 → ZMod 3 := ![0, 1, 0]
  let e123 : Fin 3 → ZMod 3 := ![1, 1, 1]
  have he1 : e1 ≠ 0 := by
    intro hh
    have := congrFun hh 0
    norm_num [e1] at this
  have he123 : e123 ≠ 0 := by
    intro hh
    have := congrFun hh 0
    norm_num [e123] at this
  let X : Subgroup G := Subgroup.zpowers (aG (Multiplicative.ofAdd e1))
  let Y : Subgroup G := Subgroup.zpowers (aG (Multiplicative.ofAdd e123))
  have hXA : X ≤ h.A := Subgroup.zpowers_le.mpr (ha_memA _)
  have hYA : Y ≤ h.A := Subgroup.zpowers_le.mpr (ha_memA _)
  have hX : Nat.card X = 3 := by
    change Nat.card (Subgroup.zpowers (aG (Multiplicative.ofAdd e1))) = 3
    rw [Nat.card_zpowers]
    exact ha_order e1 he1
  have hY : Nat.card Y = 3 := by
    change Nat.card (Subgroup.zpowers (aG (Multiplicative.ofAdd e123))) = 3
    rw [Nat.card_zpowers]
    exact ha_order e123 he123
  have hmove : ∃ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
      X.map (MulAut.conj k).toMonoidHom ≠ X := by
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    let ε : Fin 3 → ZMod 3 := fun _ => 1
    have hε : ∀ i, ε i ≠ 0 := by intro i; norm_num [ε]
    obtain ⟨n, hnform⟩ := hc₀.2.2.2 σ ε hε
    let φ : Multiplicative (Fin 3 → ZMod 3) → Multiplicative (Fin 3 → ZMod 3) :=
      fun w => Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd w (σ i)
    have hnN : n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) :=
      h.mem_normalizer_of_coords hc₀.2.1 hnform
    obtain ⟨k, hkA, hkπ, hconj⟩ :=
      exists_conj_of_coords h a ha_range ha_apply hXinj φ hnN hnform
    refine ⟨(k : G), ⟨k.2, hkA⟩, ?_⟩
    have hφ : φ (Multiplicative.ofAdd e1) = Multiplicative.ofAdd e2 := by
      apply congrArg Multiplicative.ofAdd
      funext i
      fin_cases i <;> rfl
    have hmap : X.map (MulAut.conj (k : G)).toMonoidHom =
        Subgroup.zpowers (aG (Multiplicative.ofAdd e2)) := by
      change (Subgroup.zpowers (aG (Multiplicative.ofAdd e1))).map
        (MulAut.conj (k : G)).toMonoidHom =
          Subgroup.zpowers (aG (Multiplicative.ofAdd e2))
      rw [MonoidHom.map_zpowers]
      congr 1
      exact (hconj (Multiplicative.ofAdd e1)).trans (congrArg aG hφ)
    intro hEq
    have hsub : Subgroup.zpowers (aG (Multiplicative.ofAdd e2)) =
        Subgroup.zpowers (aG (Multiplicative.ofAdd e1)) := by
      rw [← hmap, hEq]
    have hmem : aG (Multiplicative.ofAdd e2) ∈
        Subgroup.zpowers (aG (Multiplicative.ofAdd e1)) := by
      rw [← hsub]
      exact Subgroup.mem_zpowers _
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hz' : a (Multiplicative.ofAdd e2) = (a (Multiplicative.ofAdd e1)) ^ z := by
      apply Subtype.ext
      simpa [aG] using hz.symm
    have hz'' : a (Multiplicative.ofAdd e2) =
        a ((Multiplicative.ofAdd e1) ^ z) := by
      rw [map_zpow]
      exact hz'
    have hv : Multiplicative.ofAdd e2 = (Multiplicative.ofAdd e1) ^ z := ha_inj hz''
    rw [← ofAdd_zsmul] at hv
    have hvec : (![0, 1, 0] : Fin 3 → ZMod 3) =
        fun i => (z : ZMod 3) * ![1, 0, 0] i := by
      have := congrArg Multiplicative.toAdd hv
      simpa [zsmul_eq_mul, e1, e2] using this
    exact signed_e2_ne_smul_e1 (z : ZMod 3) hvec
  have hmiss : ∀ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
      X.map (MulAut.conj k).toMonoidHom ≠ Y := by
    intro k hkH
    have hkL : k ∈ c.L := hkH.1
    have hkN : k ∈ Subgroup.normalizer (h.A : Set G) := hkH.2
    let n : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨k, hkL⟩
    have hnN : n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) :=
      map_mem_normalizer_lbar h hkL hkN
    obtain ⟨σ, ε, hε, hform⟩ := hc₀.2.2.1 n hnN
    let φ : Multiplicative (Fin 3 → ZMod 3) → Multiplicative (Fin 3 → ZMod 3) :=
      fun w => Multiplicative.ofAdd fun i => ε i * Multiplicative.toAdd w (σ i)
    have hconj := conj_apply_of_mem_normalizer h a ha_range ha_apply hXinj hkL hkN
      (φ := φ) (n := n) (c₀ := c₀) rfl hform
    have hmap : X.map (MulAut.conj k).toMonoidHom =
        Subgroup.zpowers (aG (φ (Multiplicative.ofAdd e1))) := by
      change (Subgroup.zpowers (aG (Multiplicative.ofAdd e1))).map
        (MulAut.conj k).toMonoidHom =
          Subgroup.zpowers (aG (φ (Multiplicative.ofAdd e1)))
      rw [MonoidHom.map_zpowers]
      congr 1
      exact hconj (Multiplicative.ofAdd e1)
    intro hEq
    have hsub : Subgroup.zpowers (aG (φ (Multiplicative.ofAdd e1))) = Y := by
      rw [← hmap, hEq]
    have hmem : aG (φ (Multiplicative.ofAdd e1)) ∈
        Subgroup.zpowers (aG (Multiplicative.ofAdd e123)) := by
      change aG (φ (Multiplicative.ofAdd e1)) ∈ Y
      rw [← hsub]
      exact Subgroup.mem_zpowers _
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hz' : a (φ (Multiplicative.ofAdd e1)) =
        (a (Multiplicative.ofAdd e123)) ^ z := by
      apply Subtype.ext
      simpa [aG] using hz.symm
    have hz'' : a (φ (Multiplicative.ofAdd e1)) =
        a ((Multiplicative.ofAdd e123) ^ z) := by
      rw [map_zpow]
      exact hz'
    have hv : φ (Multiplicative.ofAdd e1) =
        (Multiplicative.ofAdd e123) ^ z := ha_inj hz''
    rw [← ofAdd_zsmul] at hv
    have hφv : φ (Multiplicative.ofAdd e1) =
        Multiplicative.ofAdd (fun i => ε i * ![1, 0, 0] (σ i)) := rfl
    rw [hφv] at hv
    have hvec : (fun i => ε i * ![1, 0, 0] (σ i)) =
        fun i => (z : ZMod 3) * ![1, 1, 1] i := by
      funext i
      have h := congrFun (congrArg Multiplicative.toAdd hv) i
      fin_cases i <;> simpa [zsmul_eq_mul, Pi.smul_apply, e123] using h
    exact signed_perm_e1_ne_e123 σ ε hε (z : ZMod 3) hvec
  exact ⟨X, Y, hXA, hYA, hX, hY, hmove, hmiss⟩

private lemma exists_moving_point_sumZero {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f)
    (hfam : fam = .l4) :
    ∃ X Y : Subgroup G, X ≤ h.A ∧ Y ≤ h.A ∧ Nat.card X = 3 ∧ Nat.card Y = 3 ∧
      (∃ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
        X.map (MulAut.conj k).toMonoidHom ≠ X) ∧
      (∀ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
        X.map (MulAut.conj k).toMonoidHom ≠ Y) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨c₀, a, hc₀, ha_range, ha_apply, hXinj, ha_one_iff, ha_memA, ha_order⟩ :=
    h.sumZero_coords_setup hK6c hlie hfam
  let aG : Multiplicative (Fin 4 → ZMod 3) → G := fun v => ((a v : ↥c.L) : G)
  let z1 : Fin 4 → ZMod 3 := ![1, 1, -1, -1]
  let z2 : Fin 4 → ZMod 3 := ![1, -1, 0, 0]
  have hz1 : ¬ ∃ d : ZMod 3, z1 = fun _ => d := by
    intro hd
    exact sumZero_z1_nonconstant hd
  have hz2 : ¬ ∃ d : ZMod 3, z2 = fun _ => d := by
    intro hd
    exact sumZero_z2_nonconstant hd
  let X : Subgroup G := Subgroup.zpowers (aG (Multiplicative.ofAdd z2))
  let Y : Subgroup G := Subgroup.zpowers (aG (Multiplicative.ofAdd z1))
  have hXA : X ≤ h.A := Subgroup.zpowers_le.mpr (ha_memA _)
  have hYA : Y ≤ h.A := Subgroup.zpowers_le.mpr (ha_memA _)
  have hX : Nat.card X = 3 := by
    change Nat.card (Subgroup.zpowers (aG (Multiplicative.ofAdd z2))) = 3
    rw [Nat.card_zpowers]
    exact ha_order z2 hz2
  have hY : Nat.card Y = 3 := by
    change Nat.card (Subgroup.zpowers (aG (Multiplicative.ofAdd z1))) = 3
    rw [Nat.card_zpowers]
    exact ha_order z1 hz1
  have hmove : ∃ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
      X.map (MulAut.conj k).toMonoidHom ≠ X := by
    let σ : Equiv.Perm (Fin 4) := Equiv.swap 1 2
    obtain ⟨n, hnform⟩ := hc₀.2.2.2 σ
    let φ : Multiplicative (Fin 4 → ZMod 3) → Multiplicative (Fin 4 → ZMod 3) :=
      fun w => Multiplicative.ofAdd fun i => Multiplicative.toAdd w (σ i)
    have hnN : n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) :=
      h.mem_normalizer_of_coords hc₀.1 hnform
    obtain ⟨k, hkA, hkπ, hconj⟩ :=
      exists_conj_of_coords h a ha_range ha_apply hXinj φ hnN hnform
    refine ⟨(k : G), ⟨k.2, hkA⟩, ?_⟩
    have hφ : φ (Multiplicative.ofAdd z2) =
        Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3) := by
      apply congrArg Multiplicative.ofAdd
      funext i
      fin_cases i <;> rfl
    have hmap : X.map (MulAut.conj (k : G)).toMonoidHom =
        Subgroup.zpowers (aG (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3))) := by
      change (Subgroup.zpowers (aG (Multiplicative.ofAdd z2))).map
        (MulAut.conj (k : G)).toMonoidHom =
          Subgroup.zpowers (aG (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)))
      rw [MonoidHom.map_zpowers]
      congr 1
      exact (hconj (Multiplicative.ofAdd z2)).trans (congrArg aG hφ)
    intro hEq
    have hsub : Subgroup.zpowers
          (aG (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3))) =
        Subgroup.zpowers (aG (Multiplicative.ofAdd z2)) := by
      rw [← hmap, hEq]
    have hmem : aG (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)) ∈
        Subgroup.zpowers (aG (Multiplicative.ofAdd z2)) := by
      rw [← hsub]
      exact Subgroup.mem_zpowers _
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hz' : a (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)) =
        (a (Multiplicative.ofAdd z2)) ^ z := by
      apply Subtype.ext
      simpa [aG] using hz.symm
    have hz'' : a (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)) =
        a ((Multiplicative.ofAdd z2) ^ z) := by
      rw [map_zpow]
      exact hz'
    have hc0eq : c₀ (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)) =
        c₀ ((Multiplicative.ofAdd z2) ^ z) := by
      rw [← ha_apply, ← ha_apply, hz'']
    have hc1 : c₀ (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3) *
        ((Multiplicative.ofAdd z2) ^ z)⁻¹) = 1 := by
      calc c₀ (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3) *
            ((Multiplicative.ofAdd z2) ^ z)⁻¹)
          = c₀ (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)) *
              c₀ (((Multiplicative.ofAdd z2) ^ z)⁻¹) := map_mul c₀ _ _
        _ = c₀ (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3)) *
              (c₀ ((Multiplicative.ofAdd z2) ^ z))⁻¹ :=
            congrArg (fun t => c₀ (Multiplicative.ofAdd
              (![1, 0, -1, 0] : Fin 4 → ZMod 3)) * t)
              (map_inv c₀ ((Multiplicative.ofAdd z2) ^ z))
        _ = c₀ ((Multiplicative.ofAdd z2) ^ z) *
              (c₀ ((Multiplicative.ofAdd z2) ^ z))⁻¹ := by rw [hc0eq]
        _ = 1 := mul_inv_cancel _
    obtain ⟨d, hd⟩ :=
      (hc₀.2.1 (Multiplicative.ofAdd (![1, 0, -1, 0] : Fin 4 → ZMod 3) *
        ((Multiplicative.ofAdd z2) ^ z)⁻¹)).mp hc1
    have hd' : (![1, 0, -1, 0] : Fin 4 → ZMod 3) + -(z • z2) = fun _ => d := by
      simpa only [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply]
        using hd
    have hvec : (![1, 0, -1, 0] : Fin 4 → ZMod 3) =
        fun i => (z : ZMod 3) • z2 i + d := by
      funext i
      have hi := congrFun hd' i
      have hi' : (![1, 0, -1, 0] : Fin 4 → ZMod 3) i + -(z • z2) i = d := by
        simpa [Pi.add_apply, Pi.neg_apply] using hi
      have hi'' : (![1, 0, -1, 0] : Fin 4 → ZMod 3) i = d + (z • z2) i :=
        eq_add_of_add_neg_eq hi'
      simpa [Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, add_comm] using hi''
    exact sumZero_z2_swap_not_same (z : ZMod 3) d (by simpa [z2] using hvec)
  have hmiss : ∀ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
      X.map (MulAut.conj k).toMonoidHom ≠ Y := by
    intro k hkH
    have hkL : k ∈ c.L := hkH.1
    have hkN : k ∈ Subgroup.normalizer (h.A : Set G) := hkH.2
    let n : c.Lbar := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥c.L) ⟨k, hkL⟩
    have hnN : n ∈ Subgroup.normalizer (h.Abar : Set c.Lbar) :=
      map_mem_normalizer_lbar h hkL hkN
    obtain ⟨σ, hform⟩ := hc₀.2.2.1 n hnN
    let φ : Multiplicative (Fin 4 → ZMod 3) → Multiplicative (Fin 4 → ZMod 3) :=
      fun w => Multiplicative.ofAdd fun i => Multiplicative.toAdd w (σ i)
    have hconj := conj_apply_of_mem_normalizer h a ha_range ha_apply hXinj hkL hkN
      (φ := φ) (n := n) (c₀ := c₀) rfl hform
    have hmap : X.map (MulAut.conj k).toMonoidHom =
        Subgroup.zpowers (aG (φ (Multiplicative.ofAdd z2))) := by
      change (Subgroup.zpowers (aG (Multiplicative.ofAdd z2))).map
        (MulAut.conj k).toMonoidHom =
          Subgroup.zpowers (aG (φ (Multiplicative.ofAdd z2)))
      rw [MonoidHom.map_zpowers]
      congr 1
      exact hconj (Multiplicative.ofAdd z2)
    intro hEq
    have hsub : Subgroup.zpowers (aG (φ (Multiplicative.ofAdd z2))) = Y := by
      rw [← hmap, hEq]
    have hmem : aG (φ (Multiplicative.ofAdd z2)) ∈
        Subgroup.zpowers (aG (Multiplicative.ofAdd z1)) := by
      change aG (φ (Multiplicative.ofAdd z2)) ∈ Y
      rw [← hsub]
      exact Subgroup.mem_zpowers _
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hz' : a (φ (Multiplicative.ofAdd z2)) =
        (a (Multiplicative.ofAdd z1)) ^ z := by
      apply Subtype.ext
      simpa [aG] using hz.symm
    have hz'' : a (φ (Multiplicative.ofAdd z2)) =
        a ((Multiplicative.ofAdd z1) ^ z) := by
      rw [map_zpow]
      exact hz'
    have hc0eq : c₀ (φ (Multiplicative.ofAdd z2)) =
        c₀ ((Multiplicative.ofAdd z1) ^ z) := by
      rw [← ha_apply, ← ha_apply, hz'']
    have hc1 : c₀ (φ (Multiplicative.ofAdd z2) *
        ((Multiplicative.ofAdd z1) ^ z)⁻¹) = 1 := by
      calc c₀ (φ (Multiplicative.ofAdd z2) *
            ((Multiplicative.ofAdd z1) ^ z)⁻¹)
          = c₀ (φ (Multiplicative.ofAdd z2)) *
              c₀ (((Multiplicative.ofAdd z1) ^ z)⁻¹) := map_mul c₀ _ _
        _ = c₀ (φ (Multiplicative.ofAdd z2)) *
              (c₀ ((Multiplicative.ofAdd z1) ^ z))⁻¹ :=
            congrArg (fun t => c₀ (φ (Multiplicative.ofAdd z2)) * t)
              (map_inv c₀ ((Multiplicative.ofAdd z1) ^ z))
        _ = c₀ ((Multiplicative.ofAdd z1) ^ z) *
              (c₀ ((Multiplicative.ofAdd z1) ^ z))⁻¹ := by rw [hc0eq]
        _ = 1 := mul_inv_cancel _
    obtain ⟨d, hd⟩ :=
      (hc₀.2.1 (φ (Multiplicative.ofAdd z2) *
        ((Multiplicative.ofAdd z1) ^ z)⁻¹)).mp hc1
    have hφz : φ (Multiplicative.ofAdd z2) =
        Multiplicative.ofAdd (fun i => z2 (σ i)) := rfl
    rw [hφz] at hd
    have hd' : (fun i => z2 (σ i)) + -(z • z1) = fun _ => d := by
      simpa only [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, Pi.add_apply, Pi.neg_apply]
        using hd
    have hvec : (fun i => (![1, -1, 0, 0] : Fin 4 → ZMod 3) (σ i)) =
        fun i => (z : ZMod 3) • (![1, 1, -1, -1] : Fin 4 → ZMod 3) i + d := by
      funext i
      have hi := congrFun hd' i
      have hi' : (![1, -1, 0, 0] : Fin 4 → ZMod 3) (σ i) + -(z • z1) i = d := by
        simpa [Pi.add_apply, Pi.neg_apply] using hi
      have hi'' : (![1, -1, 0, 0] : Fin 4 → ZMod 3) (σ i) = d + (z • z1) i :=
        eq_add_of_add_neg_eq hi'
      simpa [z1, Pi.smul_apply, zsmul_eq_mul, smul_eq_mul, add_comm] using hi''
    exact sumZero_perm_z2_ne_z1 σ (z : ZMod 3) d hvec
  exact ⟨X, Y, hXA, hYA, hX, hY, hmove, hmiss⟩

theorem mem_centralizer_of_isPGroup {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) {fam : LieFam811} {r f : ℕ} (hlie : IsLie811 c.Lbar fam r f)
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∀ g ∈ c.S.M ⊓ Subgroup.normalizer (h.A : Set G),
      IsPGroup p (Subgroup.zpowers g) → g ∈ Subgroup.centralizer (h.A : Set G) := by
  intro g hg hgp
  have hgH : g ∈ Subgroup.normalizer (c.L ⊓ Subgroup.normalizer (h.A : Set G) : Subgroup G) := by
    have hgNL : g ∈ Subgroup.normalizer (c.L : Set G) := c.le_normalizer_L hg.1
    have hgNNA : g ∈ Subgroup.normalizer
        (Subgroup.normalizer (h.A : Set G) : Set G) := Subgroup.le_normalizer hg.2
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hgNL, hgNNA⟩
  have hmoving : ∃ X Y : Subgroup G, X ≤ h.A ∧ Y ≤ h.A ∧
      Nat.card X = 3 ∧ Nat.card Y = 3 ∧
      (∃ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
        X.map (MulAut.conj k).toMonoidHom ≠ X) ∧
      (∀ k ∈ c.L ⊓ Subgroup.normalizer (h.A : Set G),
        X.map (MulAut.conj k).toMonoidHom ≠ Y) := by
    by_cases hfam : fam = .l4
    · exact exists_moving_point_sumZero h hK6c hlie hfam
    · exact exists_moving_point_signed h hK6c hlie hfam
  obtain ⟨X, Y, hXA, hYA, hX, hY, hmove, hmiss⟩ := hmoving
  exact CFSG.GroupTheory.mem_centralizer_of_isPGroup_of_le_normalizer h.elemAbelian h.card_A hp5
    hg.2 hgp inf_le_right hgH hXA hX hmove ⟨Y, hYA, hY, hmiss⟩

theorem false_of_ne_char {c : Counterexample4 G} (h : Case811Sylow c)
    (hK6c : K6c) (hK7 : K7) {fam : LieFam811} {r f : ℕ}
    (hlie : IsLie811 c.Lbar fam r f) {p : ℕ}
    (hp : p ∈ CFSG.Open.uniqueFourSigma c.S.M)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (hpr : p ≠ r) : False := by
  haveI : Fact p.Prime := ⟨hp.1.1⟩
  exact false_of_ne_char_of_forall_pElement h hK7 hlie hp h76 hpr
    (h.mem_centralizer_of_isPGroup hK6c hlie (c.five_le_of_mem_sigma hp))

end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
