module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepKAut
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLTv
public import CFSG.LocalAnalysis.StandardType.GGE6DepStdFrame

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_phi_apply_self {G : Type} [Group G] {Bs : Subgroup G} {φ : MulAut ↥Bs}
    (hφ2 : φ ^ 2 = 1) (b : ↥Bs) : φ (φ b) = b := by
  have h := congrArg (fun ψ : MulAut ↥Bs => ψ b) hφ2
  rw [pow_two, MulAut.mul_apply, MulAut.one_apply] at h
  exact h

private theorem ggTP_zpow_three {M : Type*} [Group M] {a : M} (ha : a ^ 3 = 1) (k : ℤ) :
    (a ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast (a ^ k) 3, ← zpow_mul a k ((3 : ℕ) : ℤ), mul_comm k ((3 : ℕ) : ℤ),
    zpow_mul a ((3 : ℕ) : ℤ) k, zpow_natCast a 3, ha, one_zpow]

private theorem ggTP_automizer_fix_of_centralizes {G : Type} [Group G] {Bs K : Subgroup G} {y : G}
    (hyBs : y ∈ Bs) (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    ∀ φ ∈ ggAutomizer K Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
  intro φ hφ
  obtain ⟨g, hgK, _, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  apply Subtype.ext
  rw [hφg]
  have hyg : y * g = g * y :=
    (Subgroup.mem_centralizer_iff.mp (hKy hgK)) y (Set.mem_singleton y)
  rw [← hyg]
  group

private theorem ggTP_frameK_fix_iff {G : Type} [Group G] {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs)
    (hy3 : y ^ 3 = 1) {κ : Additive ↥Bs →+ E6Dep.Vec6} (hκ : E6Dep.GGE6DepKFrame Bs X y κ)
    {φ : MulAut ↥Bs} (hφ2 : φ ^ 2 = 1) (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) {g : E6Dep.Mat6}
    (hact : E6Dep.ActsAsK κ φ g) (b : ↥Bs) :
    g.mulVec (κ (Additive.ofMul b)) = κ (Additive.ofMul b) ↔ φ b = b := by
  constructor
  · intro hg
    set u : ↥Bs := φ b * b⁻¹ with hu_def
    have huκ : κ (Additive.ofMul u) = 0 := by
      rw [hu_def, ofMul_mul, map_add, ofMul_inv, map_neg, hact b, hg]
      simp
    have hmem : (u : G) ∈ Subgroup.zpowers y := (hκ.1 u).mp huκ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hy3' : (⟨y, hyBs⟩ : ↥Bs) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa using hy3
    have hu_eq : u = (⟨y, hyBs⟩ : ↥Bs) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    have huφu : φ u = u := by
      rw [hu_eq, map_zpow, hφy]
    have huφuinv : φ u = u⁻¹ := by
      rw [hu_def, map_mul, map_inv, ggTP_phi_apply_self hφ2 b, mul_inv_rev, inv_inv]
    have hsymm : u = u⁻¹ := huφu.symm.trans huφuinv
    have huu : u * u = 1 := by
      simpa [← hsymm] using mul_inv_cancel u
    have hu3 : u ^ 3 = 1 := by
      rw [hu_eq]
      exact ggTP_zpow_three hy3' k
    have huu3 : u ^ 3 = u := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two, huu, one_mul]
    have hu1 : u = 1 := huu3.symm.trans hu3
    exact mul_inv_eq_one.mp (by rw [← hu_def]; exact hu1)
  · intro hb
    have h := hact b
    rw [hb] at h
    exact h.symm

private theorem ggTP_aut_eq_one_or_isTransvection {G : Type} [Group G] {Bs : Subgroup G} {y : G}
    (hyBs : y ∈ Bs) (hy1 : y ≠ 1) (hBs : IsElemAbelian 3 Bs) {ψ : MulAut ↥Bs}
    (hψy : ψ ⟨y, hyBs⟩ = ⟨y, hyBs⟩)
    (hψ : ∀ b : ↥Bs, ((b⁻¹ * ψ b : ↥Bs) : G) ∈ Subgroup.zpowers y) :
    ψ = 1 ∨ GGIsTransvection 3 ψ := by
  classical
  haveI : IsMulCommutative ↥Bs := hBs.1
  let c : ↥Bs := ⟨y, hyBs⟩
  have hψc : ψ c = c := by simpa only [c] using hψy
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (y : G) ^ 3 = 1
    exact hBs.2 y hyBs
  have hc1 : c ≠ 1 := by
    intro h
    exact hy1 (by simpa [c] using congrArg Subtype.val h)
  have hc_ord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  let D : ↥Bs →* ↥Bs :=
    { toFun := fun b => b⁻¹ * ψ b
      map_one' := by simp
      map_mul' := by
        intro a b
        show (a * b)⁻¹ * ψ (a * b) = (a⁻¹ * ψ a) * (b⁻¹ * ψ b)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hD_apply : ∀ b : ↥Bs, D b = b⁻¹ * ψ b := fun b => rfl
  have hfix : ∀ b : ↥Bs, ψ (b⁻¹ * ψ b) = b⁻¹ * ψ b := by
    intro b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    have hck : c ^ k = b⁻¹ * ψ b := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
      exact hk
    calc ψ (b⁻¹ * ψ b) = ψ (c ^ k) := by rw [hck]
      _ = (ψ c) ^ k := map_zpow ψ c k
      _ = c ^ k := by rw [hψc]
      _ = b⁻¹ * ψ b := hck
  have hD_ker : Nat.card {b : ↥Bs // ψ b = b} = Nat.card D.ker := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun b => ?_)
    show ψ b = b ↔ b ∈ D.ker
    rw [MonoidHom.mem_ker, hD_apply]
    exact eq_comm.trans inv_mul_eq_one.symm
  have hD_range_le : D.range ≤ Subgroup.zpowers c := by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_zpowers_iff]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hψ b)
    refine ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    change (y : G) ^ k = ((b⁻¹ * ψ b : ↥Bs) : G)
    exact hk
  have hcard_zp : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, hc_ord]
  have hcardD : Nat.card D.ker * Nat.card D.range = Nat.card ↥Bs :=
    Subgroup.card_ker_mul_card_range D
  have hdvd : Nat.card D.range ∣ 3 := by
    have h := Subgroup.card_dvd_of_le hD_range_le
    rwa [hcard_zp] at h
  by_cases hψ1 : ψ = 1
  · exact Or.inl hψ1
  · right
    refine ⟨?_, hfix⟩
    rw [hD_ker]
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (Nat.card D.range) hdvd with h1 | h3
    · exfalso
      have hbot : D.range = ⊥ := Subgroup.eq_bot_of_card_eq D.range h1
      have hD1 : D = 1 := by
        ext b
        have hmem : D b ∈ D.range := MonoidHom.mem_range.mpr ⟨b, rfl⟩
        rw [hbot] at hmem
        simpa using hmem
      apply hψ1
      ext b
      have hb : D b = 1 := by rw [hD1]; rfl
      have hb' : b⁻¹ * ψ b = 1 := by rw [← hD_apply]; exact hb
      exact congrArg Subtype.val (inv_mul_eq_one.mp hb').symm
    · rw [h3] at hcardD
      exact hcardD

private def ggTP_Fx {G : Type} [Group G] {Bs : Subgroup G} (φ : MulAut ↥Bs) :
    AddSubgroup (Additive ↥Bs) where
  carrier := {a | φ (Additive.toMul a) = Additive.toMul a}
  zero_mem' := by
    change φ (Additive.toMul (0 : Additive ↥Bs)) = Additive.toMul (0 : Additive ↥Bs)
    rw [show Additive.toMul (0 : Additive ↥Bs) = 1 from rfl, map_one]
  add_mem' := by
    intro a b ha hb
    change φ (Additive.toMul (a + b)) = Additive.toMul (a + b)
    rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl,
      map_mul, ha, hb]
  neg_mem' := by
    intro a ha
    change φ (Additive.toMul (-a)) = Additive.toMul (-a)
    rw [show Additive.toMul (-a) = (Additive.toMul a)⁻¹ from rfl, map_inv, ha]

private def ggTP_fxEquiv {G : Type} [Group G] {Bs : Subgroup G} (φ : MulAut ↥Bs) :
    ↥(ggTP_Fx φ) ≃ {b : ↥Bs // φ b = b} where
  toFun a := ⟨Additive.toMul (a.1 : Additive ↥Bs), a.2⟩
  invFun b := ⟨Additive.ofMul b.1, by
    change φ b.1 = b.1
    exact b.2⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; rfl

private def ggTP_f {G : Type} [Group G] {Bs : Subgroup G} (κ : Additive ↥Bs →+ E6Dep.Vec6)
    (φ : MulAut ↥Bs) : ↥(ggTP_Fx φ) →+ E6Dep.Vec6 :=
  κ.comp (ggTP_Fx φ).subtype

private noncomputable def ggTP_kerEquiv {G : Type} [Group G] {Bs : Subgroup G} {y : G}
    (hyBs : y ∈ Bs) {κ : Additive ↥Bs →+ E6Dep.Vec6}
    (hκ0 : ∀ b : ↥Bs, κ (Additive.ofMul b) = 0 ↔ (b : G) ∈ Subgroup.zpowers y)
    {φ : MulAut ↥Bs} (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) :
    ↥(ggTP_f κ φ).ker ≃ Subgroup.zpowers y where
  toFun a := by
    have h : ggTP_f κ φ a.1 = 0 := AddMonoidHom.mem_ker.mp a.2
    have h2 : κ (a.1 : Additive ↥Bs) = 0 := h
    refine ⟨((Additive.toMul (a.1 : Additive ↥Bs) : ↥Bs) : G),
      (hκ0 (Additive.toMul (a.1 : Additive ↥Bs))).mp ?_⟩
    rwa [show Additive.ofMul (Additive.toMul (a.1 : Additive ↥Bs)) = (a.1 : Additive ↥Bs)
      from rfl]
  invFun gg := by
    have hgBs : (gg : G) ∈ Bs := (Subgroup.zpowers_le.mpr hyBs) gg.2
    have hfixy : φ (⟨(gg : G), hgBs⟩ : ↥Bs) = ⟨(gg : G), hgBs⟩ := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp gg.2
      have hgb : (⟨(gg : G), hgBs⟩ : ↥Bs) = (⟨y, hyBs⟩ : ↥Bs) ^ k := by
        ext
        simpa [hk]
      rw [hgb, map_zpow, hφy]
    let x : ↥(ggTP_Fx φ) :=
      ⟨Additive.ofMul (⟨(gg : G), hgBs⟩ : ↥Bs), by
        change φ (⟨(gg : G), hgBs⟩ : ↥Bs) = (⟨(gg : G), hgBs⟩ : ↥Bs)
        exact hfixy⟩
    refine ⟨x, ?_⟩
    change κ (Additive.ofMul (⟨(gg : G), hgBs⟩ : ↥Bs)) = 0
    exact (hκ0 (⟨(gg : G), hgBs⟩ : ↥Bs)).mpr gg.2
  left_inv a := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv gg := by apply Subtype.ext; rfl

private lemma ggTP_fixH_refl_finset :
    E6Dep.refl36.filter (fun t : E6Dep.Mat6 =>
      (Finset.univ.filter (fun u : E6Dep.Vec6 => u 5 = 0 ∧ t.mulVec u = u)).card = 3 ^ 4) =
      E6Dep.refl36 := by
  decide +kernel

private lemma ggTP_fixH_refl (t : E6Dep.Mat6) (ht : t ∈ E6Dep.refl36) :
    Nat.card {u : E6Dep.Vec6 // u 5 = 0 ∧ t.mulVec u = u} = 3 ^ 4 := by
  have hmem : t ∈ E6Dep.refl36.filter (fun t : E6Dep.Mat6 =>
      (Finset.univ.filter (fun u : E6Dep.Vec6 => u 5 = 0 ∧ t.mulVec u = u)).card = 3 ^ 4) := by
    rw [ggTP_fixH_refl_finset]; exact ht
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (Finset.mem_filter.mp hmem).2

private theorem ggTP_card_fixH {G : Type} [Group G] {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs)
    (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) {κ : Additive ↥Bs →+ E6Dep.Vec6}
    (hκ : E6Dep.GGE6DepKFrame Bs X y κ) {φ : MulAut ↥Bs}
    (hφy : φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩) {g : E6Dep.Mat6}
    (hfix : ∀ b : ↥Bs,
      g.mulVec (κ (Additive.ofMul b)) = κ (Additive.ofMul b) ↔ φ b = b)
    (hfixg : Nat.card {v : E6Dep.Vec6 // v 5 = 0 ∧ g.mulVec v = v} = 3 ^ 4) :
    Nat.card {b : ↥Bs // φ b = b} = 3 ^ 5 := by
  have hker : Nat.card (ggTP_f κ φ).ker = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    rw [Nat.card_congr (ggTP_kerEquiv hyBs hκ.1 hφy), Nat.card_zpowers]
    exact orderOf_eq_prime hy3 hy1
  have hcardRange : Nat.card (ggTP_f κ φ).range = 3 ^ 4 := by
    have hsub : Nat.card (ggTP_f κ φ).range =
        Nat.card {v : E6Dep.Vec6 // v 5 = 0 ∧ g.mulVec v = v} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
      intro v
      constructor
      · intro hv
        obtain ⟨a, ha⟩ := hv
        have hb5 : v 5 = 0 := by
          rw [← ha]
          exact hκ.2.1 (Additive.toMul (a.1 : Additive ↥Bs))
        have hbφ : φ (Additive.toMul (a.1 : Additive ↥Bs)) =
            Additive.toMul (a.1 : Additive ↥Bs) := a.2
        have hgv : g.mulVec v = v := by
          rw [← ha]
          exact (hfix (Additive.toMul (a.1 : Additive ↥Bs))).mpr hbφ
        exact ⟨hb5, hgv⟩
      · rintro ⟨hv5, hgv⟩
        obtain ⟨b, hb⟩ := hκ.2.2.1 v hv5
        have hφb : φ b = b := (hfix b).mp (by rw [hb]; exact hgv)
        have hbFx : Additive.ofMul b ∈ ggTP_Fx φ := by
          change φ b = b
          exact hφb
        refine ⟨⟨Additive.ofMul b, hbFx⟩, ?_⟩
        change κ (Additive.ofMul b) = v
        exact hb
    rw [hsub, hfixg]
  have hcr := AddSubgroup.card_ker_mul_card_range (ggTP_f κ φ)
  rw [hker, hcardRange] at hcr
  rw [← Nat.card_congr (ggTP_fxEquiv φ), ← hcr]
  norm_num

theorem ggTPAutK_inj {G : Type} [Group G] {Bs K' : Subgroup G} {y' : G} (hy'Bs : y' ∈ Bs)
    (hy'1 : y' ≠ 1) (hBs : IsElemAbelian 3 Bs) (hnt : GGNoTransvection 3 Bs)
    (hKy' : K' ≤ Subgroup.centralizer ({y'} : Set G)) {κ : Additive ↥Bs →+ E6Dep.Vec6}
    (hκ : E6Dep.GGE6DepKFrame Bs K' y' κ) {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer K' Bs)
    (hψ : ψ ∈ ggAutomizer K' Bs) {g : E6Dep.Mat6} (hφg : E6Dep.ActsAsK κ φ g)
    (hψg : E6Dep.ActsAsK κ ψ g) : φ = ψ := by
  set χ : MulAut ↥Bs := φ⁻¹ * ψ with hχdef
  have hχmem : χ ∈ ggAutomizer K' Bs := mul_mem (inv_mem hφ) hψ
  have hφy' : φ ⟨y', hy'Bs⟩ = ⟨y', hy'Bs⟩ :=
    ggTP_automizer_fix_of_centralizes hy'Bs hKy' φ hφ
  have hψy' : ψ ⟨y', hy'Bs⟩ = ⟨y', hy'Bs⟩ :=
    ggTP_automizer_fix_of_centralizes hy'Bs hKy' ψ hψ
  have hφy'inv : φ⁻¹ ⟨y', hy'Bs⟩ = ⟨y', hy'Bs⟩ := by
    rw [← hφy', MulAut.inv_apply_self, hφy']
  have hχy : χ ⟨y', hy'Bs⟩ = ⟨y', hy'Bs⟩ := by
    rw [hχdef, MulAut.mul_apply, hψy']
    exact hφy'inv
  obtain ⟨g₀, hg₀, hφg₀⟩ := hκ.2.2.2.1 φ hφ
  obtain ⟨g₀', _hg₀', _hg₀g₀', hg₀'g₀⟩ := E6Dep.closureL_exists_inv hg₀
  have hgg₀ : ∀ v : E6Dep.Vec6, v 5 = 0 → g.mulVec v = g₀.mulVec v := by
    intro v hv
    obtain ⟨b', hb'⟩ := hκ.2.2.1 v hv
    calc g.mulVec v = g.mulVec (κ (Additive.ofMul b')) := by rw [hb']
      _ = κ (Additive.ofMul (φ b')) := (hφg b').symm
      _ = g₀.mulVec (κ (Additive.ofMul b')) := hφg₀ b'
      _ = g₀.mulVec v := by rw [hb']
  have hkey : ∀ b : ↥Bs, κ (Additive.ofMul (χ b)) = κ (Additive.ofMul b) := by
    intro b
    have h3 : φ (χ b) = ψ b := by
      rw [hχdef, MulAut.mul_apply, MulAut.apply_inv_self]
    have h4 : g.mulVec (κ (Additive.ofMul (χ b))) = g.mulVec (κ (Additive.ofMul b)) := by
      rw [← hφg (χ b), h3, hψg b]
    have hv1 : (κ (Additive.ofMul (χ b))) 5 = 0 := hκ.2.1 (χ b)
    have hv2 : (κ (Additive.ofMul b)) 5 = 0 := hκ.2.1 b
    have h5 := congrArg (fun v => g₀'.mulVec v) h4
    have hL : g₀'.mulVec (g.mulVec (κ (Additive.ofMul (χ b)))) =
        κ (Additive.ofMul (χ b)) := by
      rw [hgg₀ _ hv1, Matrix.mulVec_mulVec, hg₀'g₀, Matrix.one_mulVec]
    have hR : g₀'.mulVec (g.mulVec (κ (Additive.ofMul b))) = κ (Additive.ofMul b) := by
      rw [hgg₀ _ hv2, Matrix.mulVec_mulVec, hg₀'g₀, Matrix.one_mulVec]
    rw [hL, hR] at h5
    exact h5
  have hχ : ∀ b : ↥Bs, ((b⁻¹ * χ b : ↥Bs) : G) ∈ Subgroup.zpowers y' := by
    intro b
    apply (hκ.1 (b⁻¹ * χ b)).mp
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, hkey b]
    simp
  rcases ggTP_aut_eq_one_or_isTransvection hy'Bs hy'1 hBs hχy hχ with h1 | htv
  · have h : φ⁻¹ * ψ = 1 := by rw [← hχdef]; exact h1
    have h2 := congrArg (fun t : MulAut ↥Bs => φ * t) h
    rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
    exact h2.symm
  · exfalso
    have hχInd : χ ∈ ggInduced ⊤ Bs := by
      have h := ggAutomizer_mono Bs (le_top : K' ≤ ⊤) hχmem
      rwa [ggAutomizer_eq] at h
    exact hnt χ hχInd htv

theorem ggTPAutK_lift_refl {G : Type} [Group G] {Bs K' : Subgroup G} {y' : G} (hy'Bs : y' ∈ Bs)
    (hy'1 : y' ≠ 1) (hy'3 : y' ^ 3 = 1) (hBs : IsElemAbelian 3 Bs)
    (hcardBs : Nat.card Bs = 3 ^ 6) (hnt : GGNoTransvection 3 Bs)
    (hKy' : K' ≤ Subgroup.centralizer ({y'} : Set G)) {κ : Additive ↥Bs →+ E6Dep.Vec6}
    (hκ : E6Dep.GGE6DepKFrame Bs K' y' κ) {g : E6Dep.Mat6} (hg : g ∈ E6Dep.refl36) :
    ∃ φ ∈ ggAutomizer K' Bs, E6Dep.ActsAsK κ φ g ∧ GGIsReflection 3 φ := by
  have hgcl : g ∈ E6Dep.closureL := E6Dep.refl36_subset_closureL g hg
  obtain ⟨φ, hφ, hact⟩ := hκ.2.2.2.2 g hgcl
  refine ⟨φ, hφ, hact, ?_⟩
  have hφy : φ ⟨y', hy'Bs⟩ = ⟨y', hy'Bs⟩ :=
    ggTP_automizer_fix_of_centralizes hy'Bs hKy' φ hφ
  have hφ2' : φ * φ = 1 := by
    have hgg : g * g = 1 := E6Dep.refl36_mul_self hg
    have hacts : E6Dep.ActsAsK κ (φ * φ) (g * g) := E6Dep.ActsAsK.mul hact hact
    rw [hgg] at hacts
    exact ggTPAutK_inj hy'Bs hy'1 hBs hnt hKy' hκ (mul_mem hφ hφ) (one_mem _)
      hacts (E6Dep.ActsAsK.one κ)
  have hφ2 : φ ^ 2 = 1 := by rwa [pow_two]
  refine ⟨hφ2, ?_⟩
  have hfix : ∀ b : ↥Bs,
      g.mulVec (κ (Additive.ofMul b)) = κ (Additive.ofMul b) ↔ φ b = b :=
    ggTP_frameK_fix_iff hy'Bs hy'3 hκ hφ2 hφy hact
  have hfixg : Nat.card {v : E6Dep.Vec6 // v 5 = 0 ∧ g.mulVec v = v} = 3 ^ 4 :=
    ggTP_fixH_refl g hg
  have hcardFix : Nat.card {b : ↥Bs // φ b = b} = 3 ^ 5 :=
    ggTP_card_fixH hy'Bs hy'1 hy'3 hκ hφy hfix hfixg
  rw [hcardFix, hcardBs]
  norm_num

end CFSG.StandardType

end
