module

public import CFSG.Quasithin.Background.B3Sec
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.B3

variable {Γ : Type*} [Group Γ] {V : Type*} [CommGroup V]

@[expose] def IsDer (ρ : Γ →* MulAut V) (d : Γ → V) : Prop :=
  ∀ x y, d (x * y) = d x * ρ x (d y)

@[expose] def pder (ρ : Γ →* MulAut V) (v : V) : Γ → V := fun x => ρ x v * v⁻¹

@[expose] def IsPrin (ρ : Γ →* MulAut V) (d : Γ → V) : Prop := ∃ v : V, d = pder ρ v

theorem IsDer.map_one {ρ : Γ →* MulAut V} {d : Γ → V} (h : IsDer ρ d) : d 1 = 1 := by
  have h1 := h 1 1
  have h2 : ρ 1 (d 1) = d 1 := by rw [_root_.map_one]; rfl
  rw [mul_one, h2] at h1
  exact (mul_eq_left.mp h1.symm)

theorem isDer_pder (ρ : Γ →* MulAut V) (v : V) : IsDer ρ (pder ρ v) := by
  intro x y
  simp only [pder, map_mul, MulAut.mul_apply, map_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem IsDer.mul {ρ : Γ →* MulAut V} {d e : Γ → V} (hd : IsDer ρ d) (he : IsDer ρ e) :
    IsDer ρ (d * e) := by
  intro x y
  simp only [Pi.mul_apply, hd x y, he x y, map_mul]
  exact mul_mul_mul_comm _ _ _ _

theorem IsDer.inv {ρ : Γ →* MulAut V} {d : Γ → V} (hd : IsDer ρ d) : IsDer ρ d⁻¹ := by
  intro x y
  simp only [Pi.inv_apply, hd x y, mul_inv, map_inv]

theorem IsPrin.mul {ρ : Γ →* MulAut V} {d e : Γ → V} (hd : IsPrin ρ d) (he : IsPrin ρ e) :
    IsPrin ρ (d * e) := by
  obtain ⟨v, rfl⟩ := hd
  obtain ⟨w, rfl⟩ := he
  refine ⟨v * w, ?_⟩
  funext x
  simp only [Pi.mul_apply, pder, map_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

@[expose] def Z1 (ρ : Γ →* MulAut V) : Subgroup (Γ → V) where
  carrier := {d | IsDer ρ d}
  one_mem' := fun x y => by simp
  mul_mem' := fun {_ _} hd he => IsDer.mul hd he
  inv_mem' := fun {_} hd => IsDer.inv hd

@[expose] def B1 (ρ : Γ →* MulAut V) : Subgroup (Γ → V) where
  carrier := {d | IsPrin ρ d}
  one_mem' := ⟨1, by funext x; simp [pder]⟩
  mul_mem' := fun {_ _} hd he => IsPrin.mul hd he
  inv_mem' := fun {d} hd => by
    obtain ⟨v, rfl⟩ := hd
    exact ⟨v⁻¹, by funext x; simp [pder, mul_comm]⟩

abbrev H1 (ρ : Γ →* MulAut V) : Type _ := ↥(Z1 ρ) ⧸ (B1 ρ).subgroupOf (Z1 ρ)

@[expose] def ZeroClass (ρ : Γ →* MulAut V) : Prop := ∀ d, IsDer ρ d → IsPrin ρ d

@[expose] def TwoClass (ρ : Γ →* MulAut V) (d₀ : Γ → V) : Prop :=
  IsDer ρ d₀ ∧ ¬ IsPrin ρ d₀ ∧ ∀ d, IsDer ρ d → IsPrin ρ d ∨ IsPrin ρ (d * d₀)

theorem ZeroClass.card_H1 {ρ : Γ →* MulAut V} (h : ZeroClass ρ) : Nat.card (H1 ρ) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
  induction a using QuotientGroup.induction_on with
  | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
      have ha : a ∈ (B1 ρ).subgroupOf (Z1 ρ) := h a a.2
      have hb : b ∈ (B1 ρ).subgroupOf (Z1 ρ) := h b b.2
      rw [(QuotientGroup.eq_one_iff a).2 ha, (QuotientGroup.eq_one_iff b).2 hb]

theorem TwoClass.card_H1 {ρ : Γ →* MulAut V} {d₀ : Γ → V} (hV : ∀ v : V, v ^ 2 = 1)
    (h : TwoClass ρ d₀) : Nat.card (H1 ρ) = 2 := by
  obtain ⟨hd₀, hnp, hall⟩ := h
  rw [Nat.card_eq_two_iff]
  let c : H1 ρ := QuotientGroup.mk ⟨d₀, hd₀⟩
  refine ⟨1, c, ?_, ?_⟩
  · intro h1
    apply hnp
    have : (⟨d₀, hd₀⟩ : ↥(Z1 ρ)) ∈ (B1 ρ).subgroupOf (Z1 ρ) := by
      rw [← QuotientGroup.eq_one_iff]
      exact h1.symm
    exact this
  · ext q
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction q using QuotientGroup.induction_on with
    | H a =>
      rcases hall a a.2 with hp | hp
      · left
        exact ((QuotientGroup.eq_one_iff a).2 hp)
      · right
        rw [QuotientGroup.eq]
        show IsPrin ρ (((a⁻¹ * ⟨d₀, hd₀⟩ : ↥(Z1 ρ)) : Γ → V))
        have hinv : ((a : Γ → V))⁻¹ = (a : Γ → V) := by
          funext x
          have h2 : (a.1 x) * (a.1 x) = 1 := by rw [← pow_two]; exact hV _
          exact inv_eq_of_mul_eq_one_right h2
        have : (((a⁻¹ * ⟨d₀, hd₀⟩ : ↥(Z1 ρ)) : Γ → V)) = (a : Γ → V) * d₀ := by
          show ((a : Γ → V))⁻¹ * d₀ = (a : Γ → V) * d₀
          rw [hinv]
        rw [this]
        exact hp

@[expose] def IsModIso {V' : Type*} [CommGroup V'] (ρ : Γ →* MulAut V) (ρ' : Γ →* MulAut V')
    (φ : V ≃* V') : Prop := ∀ g v, φ (ρ g v) = ρ' g (φ v)

theorem IsModIso.symm {V' : Type*} [CommGroup V'] {ρ : Γ →* MulAut V} {ρ' : Γ →* MulAut V'}
    {φ : V ≃* V'} (h : IsModIso ρ ρ' φ) : IsModIso ρ' ρ φ.symm := by
  intro g v
  apply φ.injective
  rw [h g, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

theorem IsModIso.isDer {V' : Type*} [CommGroup V'] {ρ : Γ →* MulAut V} {ρ' : Γ →* MulAut V'}
    {φ : V ≃* V'} (h : IsModIso ρ ρ' φ) {d : Γ → V} (hd : IsDer ρ d) :
    IsDer ρ' (fun x => φ (d x)) := by
  intro x y
  simp only [hd x y, map_mul, h x]

theorem IsModIso.isPrin {V' : Type*} [CommGroup V'] {ρ : Γ →* MulAut V} {ρ' : Γ →* MulAut V'}
    {φ : V ≃* V'} (h : IsModIso ρ ρ' φ) {d : Γ → V} (hd : IsPrin ρ d) :
    IsPrin ρ' (fun x => φ (d x)) := by
  obtain ⟨v, rfl⟩ := hd
  refine ⟨φ v, ?_⟩
  funext x
  simp only [pder, map_mul, map_inv, h x]

theorem IsModIso.zeroClass {V' : Type*} [CommGroup V'] {ρ : Γ →* MulAut V}
    {ρ' : Γ →* MulAut V'} {φ : V ≃* V'} (h : IsModIso ρ ρ' φ) (hz : ZeroClass ρ) :
    ZeroClass ρ' := by
  intro d' hd'
  have hd : IsDer ρ (fun x => φ.symm (d' x)) := h.symm.isDer hd'
  have := h.isPrin (hz _ hd)
  have e : (fun x => φ (φ.symm (d' x))) = d' := by funext x; simp
  simpa [e] using this

@[expose] def fixG (ρ : Γ →* MulAut V) : Subgroup V where
  carrier := {v | ∀ g, ρ g v = v}
  one_mem' := fun g => _root_.map_one _
  mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
  inv_mem' := fun {a} ha g => by rw [map_inv, ha g]

theorem mem_fixG {ρ : Γ →* MulAut V} {v : V} : v ∈ fixG ρ ↔ ∀ g, ρ g v = v := Iff.rfl

@[expose] def commOn (ρ : Γ →* MulAut V) (M : Subgroup V) : Subgroup V :=
  Subgroup.closure {w | ∃ g, ∃ m ∈ M, w = ρ g m * m⁻¹}

@[expose] def commG (ρ : Γ →* MulAut V) : Subgroup V := commOn ρ ⊤

theorem mul_inv_mem_commOn {ρ : Γ →* MulAut V} {M : Subgroup V} (g : Γ) {m : V} (hm : m ∈ M) :
    ρ g m * m⁻¹ ∈ commOn ρ M :=
  Subgroup.subset_closure ⟨g, m, hm, rfl⟩

theorem commOn_le {ρ : Γ →* MulAut V} {M N : Subgroup V}
    (h : ∀ g, ∀ m ∈ M, ρ g m * m⁻¹ ∈ N) : commOn ρ M ≤ N := by
  refine (Subgroup.closure_le N).2 ?_
  rintro w ⟨g, m, hm, rfl⟩
  exact h g m hm

theorem mul_inv_mem_commG {ρ : Γ →* MulAut V} (g : Γ) (v : V) : ρ g v * v⁻¹ ∈ commG ρ :=
  mul_inv_mem_commOn g (Subgroup.mem_top v)

theorem isInv_of_trivQ {ρ : Γ →* MulAut V} {M : Subgroup V}
    (h : ∀ g v, ρ g v * v⁻¹ ∈ M) : IsInv ρ M := by
  intro g m hm
  have := M.mul_mem (h g m) hm
  simpa [mul_assoc] using this

theorem isInv_commG (ρ : Γ →* MulAut V) : IsInv ρ (commG ρ) :=
  isInv_of_trivQ (fun g v => mul_inv_mem_commG g v)

theorem isInv_fixG (ρ : Γ →* MulAut V) : IsInv ρ (fixG ρ) := by
  intro g v hv
  rw [hv g]
  exact hv

theorem eq_one_of_perfect {E : Type*} [CommGroup E] (hperf : commutator Γ = ⊤) (f : Γ →* E)
    (x : Γ) : f x = 1 := by
  have h : (⊤ : Subgroup Γ) ≤ f.ker := by
    rw [← hperf, commutator_def]
    refine Subgroup.commutator_le.2 (fun g₁ _ g₂ _ => ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Commute.all _ _
  exact f.mem_ker.1 (h (Subgroup.mem_top x))

theorem der_eq_one_of_trivial (hperf : commutator Γ = ⊤) {ρ : Γ →* MulAut V} {N : Subgroup V}
    (hN : ∀ g, ∀ x ∈ N, ρ g x = x) {d : Γ → V} (hd : IsDer ρ d) (hdN : ∀ x, d x ∈ N)
    (x : Γ) : d x = 1 := by
  let f : Γ →* N :=
    { toFun := fun x => ⟨d x, hdN x⟩
      map_one' := Subtype.ext hd.map_one
      map_mul' := fun x y => Subtype.ext (by
        show d (x * y) = d x * d y
        rw [hd x y, hN x (d y) (hdN y)]) }
  exact congrArg Subtype.val (eq_one_of_perfect hperf f x)

theorem exists_complement (hV : ∀ v : V, v ^ 2 = 1) (M : Subgroup V) :
    ∃ S : Subgroup V, M ⊓ S = ⊥ ∧ M ⊔ S = ⊤ := by
  have : IsElementaryAbelian 2 V := ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hV⟩
  obtain ⟨S, hS⟩ := IsElementaryAbelian.exists_isCompl 2 V M
  exact ⟨S, disjoint_iff.1 hS.disjoint, codisjoint_iff.1 hS.codisjoint⟩

theorem exists_hyperplane (hV : ∀ v : V, v ^ 2 = 1) (M : Subgroup V) {c : V} (hc : c ∉ M) :
    ∃ N : Subgroup V, M ≤ N ∧ c ∉ N ∧ N ⊔ Subgroup.zpowers c = ⊤ := by
  have hq : ∀ q : V ⧸ M, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hV]; rfl
  have : IsElementaryAbelian 2 (V ⧸ M) :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.2 hq⟩
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl 2 (V ⧸ M)
    (Subgroup.zpowers (QuotientGroup.mk c : V ⧸ M))
  refine ⟨C.comap (QuotientGroup.mk' M), fun m hm => ?_, fun hcN => ?_, ?_⟩
  · show (QuotientGroup.mk m : V ⧸ M) ∈ C
    rw [(QuotientGroup.eq_one_iff m).2 hm]
    exact C.one_mem
  · have h1 : (QuotientGroup.mk c : V ⧸ M) ∈ C := hcN
    have h2 : (QuotientGroup.mk c : V ⧸ M) ∈ Subgroup.zpowers (QuotientGroup.mk c : V ⧸ M) :=
      Subgroup.mem_zpowers _
    have h3 := Subgroup.disjoint_def.1 hC.disjoint h2 h1
    exact hc ((QuotientGroup.eq_one_iff c).1 h3)
  · rw [eq_top_iff]
    intro v _
    have hv : (QuotientGroup.mk v : V ⧸ M) ∈ Subgroup.zpowers (QuotientGroup.mk c : V ⧸ M) ⊔ C := by
      rw [codisjoint_iff.1 hC.codisjoint]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup.1 hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hn : v * c ^ (-k) ∈ C.comap (QuotientGroup.mk' M) := by
      show QuotientGroup.mk' M (v * c ^ (-k)) ∈ C
      have : QuotientGroup.mk' M (v * c ^ (-k)) = z := by
        rw [map_mul, map_zpow]
        show (QuotientGroup.mk v : V ⧸ M) * (QuotientGroup.mk c : V ⧸ M) ^ (-k) = z
        rw [← hyz, zpow_neg]
        simp [mul_comm]
      rw [this]
      exact hz
    have : v = (v * c ^ (-k)) * c ^ k := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hn (Subgroup.zpow_mem_zpowers c k)

end CFSG.Quasithin.B3
