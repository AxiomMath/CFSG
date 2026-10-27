module

public import CFSG.Monster.B.GSide.HClasses

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

section Generic

variable {G K : Type*} [Group G] [Group K] {d : G}

@[expose] def dH (ψ : Subgroup.centralizer {d} ≃* K) : Set K :=
  {y | IsConj d ((ψ.symm y : Subgroup.centralizer {d}) : G)}

theorem mem_dH_iff (ψ : Subgroup.centralizer {d} ≃* K) (y : K) :
    y ∈ dH ψ ↔ IsConj d ((ψ.symm y : Subgroup.centralizer {d}) : G) :=
  Iff.rfl

theorem mem_dH_of_isConj (ψ : Subgroup.centralizer {d} ≃* K) {y y' : K} (hy : y ∈ dH ψ)
    (h : IsConj y y') : y' ∈ dH ψ := by
  have h1 : IsConj (ψ.symm y) (ψ.symm y') := ψ.symm.toMonoidHom.map_isConj h
  exact hy.trans ((Subgroup.centralizer {d}).subtype.map_isConj h1)

theorem conjEquiv_trans_mem_dH_iff (ψ : Subgroup.centralizer {d} ≃* K) {a : G} (g : G)
    (hg : g * d * g⁻¹ = a) (x : Subgroup.centralizer {a}) :
    (centralizerConjEquiv g hg).trans ψ x ∈ dH ψ ↔ IsConj d (x : G) := by
  rw [mem_dH_iff, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, coe_centralizerConjEquiv]
  have hc : IsConj (g⁻¹ * (x : G) * g) (x : G) := isConj_iff.2 ⟨g, by group⟩
  exact ⟨fun h => h.trans hc, fun h => h.trans hc.symm⟩

theorem self_mem_center_centralizer (d : G) :
    (⟨d, mem_centralizer_singleton_self d⟩ : Subgroup.centralizer {d}) ∈
      Subgroup.center (Subgroup.centralizer {d}) := by
  rw [Subgroup.mem_center_iff]
  intro z
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 z.2)

theorem psi_self_mem_center (ψ : Subgroup.centralizer {d} ≃* K) :
    ψ ⟨d, mem_centralizer_singleton_self d⟩ ∈ Subgroup.center K :=
  (mem_center_iff_of_mulEquiv ψ).1 (self_mem_center_centralizer d)

theorem psi_self_mem_centralizer (ψ : Subgroup.centralizer {d} ≃* K) (w : K) :
    ψ ⟨d, mem_centralizer_singleton_self d⟩ ∈ Subgroup.centralizer {w} :=
  Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_center_iff.1 (psi_self_mem_center ψ) w).symm

@[expose] def centralizerCommEquiv (x : Subgroup.centralizer {d})
    (hxd : d ∈ Subgroup.centralizer {(x : G)}) :
    Subgroup.centralizer {x} ≃*
      Subgroup.centralizer {(⟨d, hxd⟩ : Subgroup.centralizer {(x : G)})} where
  toFun z := ⟨⟨((z : Subgroup.centralizer {d}) : G), by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 z.2)⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (z : Subgroup.centralizer {d}).2)⟩
  invFun z := ⟨⟨((z : Subgroup.centralizer {(x : G)}) : G), by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 z.2)⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.1 (z : Subgroup.centralizer {(x : G)}).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem coe_coe_centralizerCommEquiv (x : Subgroup.centralizer {d})
    (hxd : d ∈ Subgroup.centralizer {(x : G)}) (z : Subgroup.centralizer {x}) :
    ((centralizerCommEquiv x hxd z : Subgroup.centralizer {(x : G)}) : G) =
      ((z : Subgroup.centralizer {d}) : G) :=
  rfl

theorem exists_swap_centralizer (ψ : Subgroup.centralizer {d} ≃* K) {y : K} (hy : y ∈ dH ψ)
    (hne : y ≠ ψ ⟨d, mem_centralizer_singleton_self d⟩) :
    ∃ y' ∈ dH ψ, y' ≠ ψ ⟨d, mem_centralizer_singleton_self d⟩ ∧
      ∃ θ : Subgroup.centralizer {y} ≃* Subgroup.centralizer {y'},
        (θ ⟨_, psi_self_mem_centralizer ψ y⟩ : K) = y' ∧
        (θ ⟨y, mem_centralizer_singleton_self y⟩ : K) = ψ ⟨d, mem_centralizer_singleton_self d⟩ ∧
        (∀ w : Subgroup.centralizer {y}, (θ w : K) ∈ dH ψ ↔ (w : K) ∈ dH ψ) ∧
        Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {y'}) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hy
  set x : Subgroup.centralizer {d} := ψ.symm y with hx
  have hxd : d ∈ Subgroup.centralizer {(x : G)} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 x.2).symm
  set ψx := (centralizerConjEquiv g hg).trans ψ with hψx
  set y' := ψx ⟨d, hxd⟩ with hy'
  have hψxx : ψx ⟨(x : G), mem_centralizer_singleton_self _⟩ =
      ψ ⟨d, mem_centralizer_singleton_self d⟩ := by
    rw [hψx, MulEquiv.trans_apply]
    refine congrArg ψ (Subtype.ext ?_)
    rw [coe_centralizerConjEquiv, ← hg]
    show g⁻¹ * (g * d * g⁻¹) * g = d
    group
  set θ := (CTIB.centralizerEquiv ψ.symm y).trans
    ((centralizerCommEquiv x hxd).trans (CTIB.centralizerEquiv ψx ⟨d, hxd⟩)) with hθ
  have hθw : ∀ w : Subgroup.centralizer {y}, (θ w : K) =
      ψx ⟨((ψ.symm (w : K) : Subgroup.centralizer {d}) : G), by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := Subgroup.mem_centralizer_singleton_iff.1
          ((CTIB.centralizerEquiv ψ.symm y w : Subgroup.centralizer {x})).2
        exact congrArg Subtype.val h⟩ := fun w => rfl
  have hy'D : y' ∈ dH ψ := (conjEquiv_trans_mem_dH_iff ψ g hg ⟨d, hxd⟩).2 (IsConj.refl d)
  refine ⟨y', hy'D, ?_, θ, ?_, ?_, fun w => ?_, Nat.card_congr θ.toEquiv⟩
  · intro e
    rw [← hψxx] at e
    have e1 := congrArg Subtype.val (ψx.injective e)
    apply hne
    rw [← hψxx]
    have e2 : x = ⟨d, mem_centralizer_singleton_self d⟩ := Subtype.ext e1.symm
    rw [hψxx, ← e2, hx, MulEquiv.apply_symm_apply]
  · rw [hθw]
    refine congrArg ψx (Subtype.ext ?_)
    show ((ψ.symm (ψ ⟨d, mem_centralizer_singleton_self d⟩) : Subgroup.centralizer {d}) : G) = d
    rw [MulEquiv.symm_apply_apply]
  · rw [hθw, ← hψxx]
  · rw [hθw, conjEquiv_trans_mem_dH_iff, mem_dH_iff]

theorem exists_swap_centralizer_of_eq (ψ : Subgroup.centralizer {d} ≃* K) {z₀ : K}
    (hz₀ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = z₀)
    (hz₀c : ∀ w : K, z₀ ∈ Subgroup.centralizer {w}) {y : K} (hy : y ∈ dH ψ) (hne : y ≠ z₀) :
    ∃ y' ∈ dH ψ, y' ≠ z₀ ∧ ∃ θ : Subgroup.centralizer {y} ≃* Subgroup.centralizer {y'},
      (θ ⟨z₀, hz₀c y⟩ : K) = y' ∧ (θ ⟨y, mem_centralizer_singleton_self y⟩ : K) = z₀ ∧
      (∀ w : Subgroup.centralizer {y}, (θ w : K) ∈ dH ψ ↔ (w : K) ∈ dH ψ) ∧
      Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {y'}) := by
  subst hz₀
  exact exists_swap_centralizer ψ hy hne

end Generic

section Adjacency

variable {G K : Type*} [Group G] [Group K] {d : G}

theorem conjEquiv_trans_eq_conj (ψ : Subgroup.centralizer {d} ≃* K) {a : G} (g g' : G)
    (hg : g * d * g⁻¹ = a) (hg' : g' * d * g'⁻¹ = a) :
    ∃ y : K, ∀ x : Subgroup.centralizer {a},
      (centralizerConjEquiv g' hg').trans ψ x =
        y * (centralizerConjEquiv g hg).trans ψ x * y⁻¹ := by
  have hk : g'⁻¹ * g ∈ Subgroup.centralizer {d} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g'⁻¹ * g * d = g'⁻¹ * (g * d * g⁻¹) * g := by group
      _ = g'⁻¹ * (g' * d * g'⁻¹) * g := by rw [hg, hg']
      _ = d * (g'⁻¹ * g) := by group
  refine ⟨ψ ⟨_, hk⟩, fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, ← map_inv, ← map_mul, ← map_mul]
  refine congrArg ψ (Subtype.ext ?_)
  show g'⁻¹ * (x : G) * g' = g'⁻¹ * g * (g⁻¹ * x * g) * (g'⁻¹ * g)⁻¹
  group

theorem conjEquiv_trans_conj (ψ : Subgroup.centralizer {d} ≃* K) {a b : G} (g : G)
    (hg : g * d * g⁻¹ = a) (h : G) (hab : h * a * h⁻¹ = b) (hhg : h * g * d * (h * g)⁻¹ = b)
    (x : Subgroup.centralizer {a}) :
    (centralizerConjEquiv (h * g) hhg).trans ψ ((centralizerConjEquiv h hab).symm x) =
      (centralizerConjEquiv g hg).trans ψ x := by
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
  refine congrArg ψ (Subtype.ext ?_)
  show (h * g)⁻¹ * (h * (x : G) * h⁻¹) * (h * g) = g⁻¹ * x * g
  group

@[expose] def adjR (R : Set K) (ψ : Subgroup.centralizer {d} ≃* K) (a b : G) : Prop :=
  ∃ (ha : IsConj d a) (hb : b ∈ Subgroup.centralizer {a}),
    (centralizerConjEquiv (conjugator ha) (conjugator_spec ha)).trans ψ ⟨b, hb⟩ ∈ R

variable {R : Set K} (hR : ∀ y y' : K, y ∈ R → IsConj y y' → y' ∈ R)
include hR

theorem adjR_iff (ψ : Subgroup.centralizer {d} ≃* K) {a b : G} (ha : IsConj d a) (g : G)
    (hg : g * d * g⁻¹ = a) (hb : b ∈ Subgroup.centralizer {a}) :
    adjR R ψ a b ↔ (centralizerConjEquiv g hg).trans ψ ⟨b, hb⟩ ∈ R := by
  obtain ⟨y, hy⟩ := conjEquiv_trans_eq_conj ψ g (conjugator ha) hg (conjugator_spec ha)
  obtain ⟨y', hy'⟩ := conjEquiv_trans_eq_conj ψ (conjugator ha) g (conjugator_spec ha) hg
  constructor
  · rintro ⟨_, _, h⟩
    rw [hy']
    exact hR _ _ h (isConj_iff.2 ⟨y', rfl⟩)
  · intro h
    refine ⟨ha, hb, ?_⟩
    rw [hy]
    exact hR _ _ h (isConj_iff.2 ⟨y, rfl⟩)

theorem adjR_conj (ψ : Subgroup.centralizer {d} ≃* K) {a b : G} (h : G) (hab : adjR R ψ a b) :
    adjR R ψ (h * a * h⁻¹) (h * b * h⁻¹) := by
  obtain ⟨ha, hb, hR'⟩ := hab
  have hg := conjugator_spec ha
  have hhg : h * conjugator ha * d * (h * conjugator ha)⁻¹ = h * a * h⁻¹ :=
    calc h * conjugator ha * d * (h * conjugator ha)⁻¹ =
        h * (conjugator ha * d * (conjugator ha)⁻¹) * h⁻¹ := by group
      _ = h * a * h⁻¹ := by rw [hg]
  have ha' : IsConj d (h * a * h⁻¹) := isConj_iff.2 ⟨_, hhg⟩
  have hb' : h * b * h⁻¹ ∈ Subgroup.centralizer {h * a * h⁻¹} :=
    ((centralizerConjEquiv h rfl).symm ⟨b, hb⟩).2
  rw [adjR_iff hR ψ ha' _ hhg hb']
  have e := conjEquiv_trans_conj ψ (conjugator ha) hg h rfl hhg ⟨b, hb⟩
  exact e ▸ hR'

theorem adjR_self_iff (ψ : Subgroup.centralizer {d} ≃* K) {b : G}
    (hb : b ∈ Subgroup.centralizer {d}) : adjR R ψ d b ↔ ψ ⟨b, hb⟩ ∈ R := by
  have h1 : (1 : G) * d * 1⁻¹ = d := by group
  rw [adjR_iff hR ψ (IsConj.refl d) 1 h1 hb, MulEquiv.trans_apply]
  have e : centralizerConjEquiv 1 h1 ⟨b, hb⟩ = ⟨b, hb⟩ :=
    Subtype.ext (show (1 : G)⁻¹ * b * 1 = b by group)
  rw [e]

omit hR in
theorem exists_centralizer_conj_of_adjR (hR1 : ∀ y y' : K, y ∈ R → y' ∈ R → IsConj y y')
    (ψ : Subgroup.centralizer {d} ≃* K) {a b b' : G} (h : adjR R ψ a b) (h' : adjR R ψ a b') :
    ∃ k ∈ Subgroup.centralizer {a}, k * b * k⁻¹ = b' := by
  obtain ⟨ha, hb, hbR⟩ := h
  obtain ⟨_, hb', hb'R⟩ := h'
  set φ := (centralizerConjEquiv (conjugator ha) (conjugator_spec ha)).trans ψ with hφ
  obtain ⟨w, hw⟩ := isConj_iff.1 (hR1 _ _ hbR hb'R)
  refine ⟨(φ.symm w : G), (φ.symm w).2, ?_⟩
  have e : φ.symm w * ⟨b, hb⟩ * (φ.symm w)⁻¹ = ⟨b', hb'⟩ := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hw
  exact congrArg Subtype.val e

theorem exists_conj_pair_of_adjR (hR1 : ∀ y y' : K, y ∈ R → y' ∈ R → IsConj y y')
    (ψ : Subgroup.centralizer {d} ≃* K) {a b a' b' : G} (h : adjR R ψ a b)
    (h' : adjR R ψ a' b') : ∃ s : G, s * a * s⁻¹ = a' ∧ s * b * s⁻¹ = b' := by
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 (h.1.symm.trans h'.1)
  have h2 := adjR_conj hR ψ g₁ h
  rw [hg₁] at h2
  obtain ⟨k, hk, hkb⟩ := exists_centralizer_conj_of_adjR hR1 ψ h2 h'
  refine ⟨k * g₁, ?_, ?_⟩
  · have hka : k * a' = a' * k := Subgroup.mem_centralizer_singleton_iff.1 hk
    calc k * g₁ * a * (k * g₁)⁻¹ = k * (g₁ * a * g₁⁻¹) * k⁻¹ := by group
      _ = a' := by rw [hg₁, hka, mul_inv_cancel_right]
  · rw [← hkb]
    group

theorem exists_swap_of_adjR (hR1 : ∀ y y' : K, y ∈ R → y' ∈ R → IsConj y y')
    (ψ : Subgroup.centralizer {d} ≃* K) {a b : G} (h : adjR R ψ a b) (h' : adjR R ψ b a) :
    ∃ s : G, s * a * s⁻¹ = b ∧ s * b * s⁻¹ = a :=
  exists_conj_pair_of_adjR hR hR1 ψ h h'

omit hR in
theorem adjR_ne (ψ : Subgroup.centralizer {d} ≃* K)
    (hR0 : ψ ⟨d, mem_centralizer_singleton_self d⟩ ∉ R) {a b : G} (h : adjR R ψ a b) : b ≠ a := by
  rintro rfl
  obtain ⟨ha, hb, hbR⟩ := h
  apply hR0
  convert hbR using 1
  rw [MulEquiv.trans_apply]
  refine congrArg ψ (Subtype.ext ?_)
  show d = (conjugator ha)⁻¹ * b * conjugator ha
  have hs := conjugator_spec ha
  calc d = (conjugator ha)⁻¹ * (conjugator ha * d * (conjugator ha)⁻¹) * conjugator ha := by group
    _ = (conjugator ha)⁻¹ * b * conjugator ha := by rw [hs]

omit hR in
theorem natCard_centralizer_swap (ψ : Subgroup.centralizer {d} ≃* K)
    (x : Subgroup.centralizer {d}) (g : G) (hg : g * d * g⁻¹ = (x : G))
    (hxd : d ∈ Subgroup.centralizer {(x : G)}) :
    Nat.card (Subgroup.centralizer {ψ x}) =
      Nat.card (Subgroup.centralizer {(centralizerConjEquiv g hg).trans ψ ⟨d, hxd⟩}) :=
  Nat.card_congr ((CTIB.centralizerEquiv ψ x).symm.trans ((centralizerCommEquiv x hxd).trans
    (CTIB.centralizerEquiv ((centralizerConjEquiv g hg).trans ψ) ⟨d, hxd⟩))).toEquiv

omit hR in
theorem natCard_centralizer_of_isConj {y y' : K} (h : IsConj y y') :
    Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {y'}) := by
  obtain ⟨w, rfl⟩ := isConj_iff.1 h
  exact (Nat.card_congr (CTIB.centralizerEquiv (MulAut.conj w) y).toEquiv)

theorem adjR_symm (hR1 : ∀ y y' : K, y ∈ R → y' ∈ R → IsConj y y')
    (ψ : Subgroup.centralizer {d} ≃* K) (hR0 : ψ ⟨d, mem_centralizer_singleton_self d⟩ ∉ R)
    (hRD : R ⊆ dH ψ) {r₀ : K} (hr₀ : r₀ ∈ R)
    (hcls : ∀ y ∈ dH ψ, y ≠ ψ ⟨d, mem_centralizer_singleton_self d⟩ →
      Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {r₀}) → y ∈ R)
    {a b : G} (h : adjR R ψ a b) : adjR R ψ b a := by
  obtain ⟨g₀, hg⟩ := isConj_iff.1 h.1
  have h0 := adjR_conj hR ψ g₀⁻¹ h
  have hd : g₀⁻¹ * a * g₀⁻¹⁻¹ = d := by rw [← hg]; group
  rw [hd] at h0
  have hb₀C := h0.2.1
  have hyR : ψ ⟨_, hb₀C⟩ ∈ R := (adjR_self_iff hR ψ hb₀C).1 h0
  set x : Subgroup.centralizer {d} := ⟨_, hb₀C⟩ with hx
  have hxD : IsConj d (x : G) := by
    have h1 := hRD hyR
    rwa [mem_dH_iff, MulEquiv.symm_apply_apply] at h1
  obtain ⟨g, hg'⟩ := isConj_iff.1 hxD
  have hxd : d ∈ Subgroup.centralizer {(x : G)} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.1 x.2).symm
  set ψx := (centralizerConjEquiv g hg').trans ψ with hψx
  have hψxx : ψx ⟨(x : G), mem_centralizer_singleton_self _⟩ =
      ψ ⟨d, mem_centralizer_singleton_self d⟩ := by
    rw [hψx, MulEquiv.trans_apply]
    refine congrArg ψ (Subtype.ext ?_)
    rw [coe_centralizerConjEquiv, ← hg']
    show g⁻¹ * (g * d * g⁻¹) * g = d
    group
  have hy'D : ψx ⟨d, hxd⟩ ∈ dH ψ := (conjEquiv_trans_mem_dH_iff ψ g hg' ⟨d, hxd⟩).2 (IsConj.refl d)
  have hy'ne : ψx ⟨d, hxd⟩ ≠ ψ ⟨d, mem_centralizer_singleton_self d⟩ := by
    intro e
    rw [← hψxx] at e
    have e1 := congrArg Subtype.val (ψx.injective e)
    have e2 : x = ⟨d, mem_centralizer_singleton_self d⟩ := Subtype.ext e1.symm
    apply hR0
    rw [← e2]
    exact hyR
  have hcard : Nat.card (Subgroup.centralizer {ψx ⟨d, hxd⟩}) =
      Nat.card (Subgroup.centralizer {r₀}) := by
    rw [← natCard_centralizer_swap ψ x g hg' hxd]
    exact natCard_centralizer_of_isConj (hR1 _ _ hyR hr₀)
  have hy'R := hcls _ hy'D hy'ne hcard
  have h1 : adjR R ψ (x : G) d := (adjR_iff hR ψ hxD g hg' hxd).2 hy'R
  have h2 := adjR_conj hR ψ g₀ h1
  have e3 : g₀ * (x : G) * g₀⁻¹ = b := by
    show g₀ * (g₀⁻¹ * b * g₀⁻¹⁻¹) * g₀⁻¹ = b
    group
  rw [e3, hg] at h2
  exact h2

end Adjacency

theorem cV0_mem_centralizer
    (w : vStab cv0) : cV0 ∈ Subgroup.centralizer {w} := by
  have h : cV0 ∈ Subgroup.center (vStab cv0) := by
    rw [center_vStab_cv0]
    exact Subgroup.mem_zpowers cV0
  exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_center_iff.1 h w).symm

variable {G : Type*} [Group G] {d : G}

theorem psiAt_mem_dH_iff
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) {a : G} (ha : IsConj d a)
    (x : Subgroup.centralizer {a}) : psiAt ψ ha x ∈ dH ψ ↔ IsConj d (x : G) :=
  conjEquiv_trans_mem_dH_iff ψ (conjugator ha) (conjugator_spec ha) x

theorem exists_swap_cV0
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0)
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {y : vStab cv0} (hy : y ∈ dH ψ)
    (hne : y ≠ cV0) :
    ∃ y' ∈ dH ψ, y' ≠ cV0 ∧ ∃ θ : Subgroup.centralizer {y} ≃* Subgroup.centralizer {y'},
      (θ ⟨cV0, cV0_mem_centralizer y⟩ : vStab cv0) = y' ∧
      (θ ⟨y, mem_centralizer_singleton_self y⟩ : vStab cv0) = cV0 ∧
      (∀ w : Subgroup.centralizer {y}, (θ w : vStab cv0) ∈ dH ψ ↔ (w : vStab cv0) ∈ dH ψ) ∧
      Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {y'}) :=
  exists_swap_centralizer_of_eq ψ hψ cV0_mem_centralizer hy hne

theorem RA_conj
    (y y' : vStab cv0) (hy : y ∈ RA) (h : IsConj y y') : y' ∈ RA :=
  (mem_RA_iff_isConj y').2 (((mem_RA_iff_isConj y).1 hy).trans h)

theorem RA_isConj
    (y y' : vStab cv0) (hy : y ∈ RA) (hy' : y' ∈ RA) : IsConj y y' :=
  ((mem_RA_iff_isConj y).1 hy).symm.trans ((mem_RA_iff_isConj y').1 hy')

theorem cV0_not_mem_RA :
    cV0 ∉ RA := by
  rintro ⟨w, hw, e⟩
  have e' := congrArg Subtype.val e
  rw [coe_cV0, coe_clabelS, coe_clabelS] at e'
  have := native_global_label_bijection_and_full_vertex_centralizer.1 e'
  subst this
  exact cgraph.loopless.irrefl _ hw

@[expose] def gAdj
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (a b : G) : Prop :=
  ∃ (ha : IsConj d a) (hb : b ∈ Subgroup.centralizer {a}), psiAt ψ ha ⟨b, hb⟩ ∈ RA

theorem gAdj_iff_adjR
    (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (a b : G) :
    gAdj ψ a b ↔ adjR RA ψ a b :=
  Iff.rfl

variable (ψ : Subgroup.centralizer {d} ≃* vStab cv0)

theorem gAdj_iff_conjEquiv
    {a b : G} (ha : IsConj d a) (g : G) (hg : g * d * g⁻¹ = a)
    (hb : b ∈ Subgroup.centralizer {a}) :
    gAdj ψ a b ↔ (centralizerConjEquiv g hg).trans ψ ⟨b, hb⟩ ∈ RA :=
  adjR_iff RA_conj ψ ha g hg hb

theorem gAdj_conj
    {a b : G} (h : G) (hab : gAdj ψ a b) : gAdj ψ (h * a * h⁻¹) (h * b * h⁻¹) :=
  adjR_conj RA_conj ψ h hab

theorem gAdj_self_iff
    {b : G} (hb : b ∈ Subgroup.centralizer {d}) :
    gAdj ψ d b ↔ ψ ⟨b, hb⟩ ∈ RA :=
  adjR_self_iff RA_conj ψ hb

theorem exists_centralizer_conj_of_gAdj
    {a b b' : G} (h : gAdj ψ a b) (h' : gAdj ψ a b') :
    ∃ k ∈ Subgroup.centralizer {a}, k * b * k⁻¹ = b' :=
  exists_centralizer_conj_of_adjR RA_isConj ψ h h'

theorem exists_conj_pair_of_gAdj
    {a b a' b' : G} (h : gAdj ψ a b) (h' : gAdj ψ a' b') :
    ∃ s : G, s * a * s⁻¹ = a' ∧ s * b * s⁻¹ = b' :=
  exists_conj_pair_of_adjR RA_conj RA_isConj ψ h h'

theorem exists_swap_of_gAdj
    {a b : G} (h : gAdj ψ a b) (h' : gAdj ψ b a) :
    ∃ s : G, s * a * s⁻¹ = b ∧ s * b * s⁻¹ = a :=
  exists_swap_of_adjR RA_conj RA_isConj ψ h h'

theorem gAdj_symm
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) (hRA : RA ⊆ dH ψ)
    (hcls : ∀ y ∈ dH ψ, y ≠ cV0 →
      Nat.card (Subgroup.centralizer {y}) = Nat.card (Subgroup.centralizer {lamW0H}) → y ∈ RA)
    {a b : G} (h : gAdj ψ a b) : gAdj ψ b a :=
  adjR_symm RA_conj RA_isConj ψ (hψ ▸ cV0_not_mem_RA) hRA lamW0H_mem_RA
    (fun y hy hne hc => hcls y hy (hψ ▸ hne) hc) h

theorem gAdj_ne
    (hψ : ψ ⟨d, mem_centralizer_singleton_self d⟩ = cV0) {a b : G}
    (h : gAdj ψ a b) : b ≠ a :=
  adjR_ne ψ (hψ ▸ cV0_not_mem_RA) h

end CFSG.Monster.B.GSide
