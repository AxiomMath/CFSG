module

public import CFSG.Quasithin.Vol2.Ch12Sec4N6F3
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.H13

namespace N1246

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.L3
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem comm_of_elem {P : Subgroup G} (hP : IsElemAbelian 3 P) {x y : G} (hx : x ∈ P)
    (hy : y ∈ P) : x * y = y * x := CFSG.Open.IsElemAbelian.comm hP hx hy

omit [Finite G] in
theorem sq_not_mem {D : Subgroup G} {x : G} (hx3 : x * x * x = 1) (hx : x ∉ D) : x * x ∉ D := by
  intro h
  apply hx
  have : x = (x * x) * (x * x) := by
    calc x = (x * x * x) * x := by rw [hx3, one_mul]
      _ = (x * x) * (x * x) := by group
  rw [this]
  exact D.mul_mem h h

omit [Finite G] in
theorem orderOf_eq_three {D : Subgroup G} {x : G} (hx3 : x * x * x = 1) (hx : x ∉ D) :
    orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime (by rw [pow_three', hx3]) fun h => hx ?_
  rw [h]
  exact D.one_mem

theorem eq_one_of_mem_zpowers {D : Subgroup G} {x y : G} (hx3 : x * x * x = 1) (hx : x ∉ D)
    (hy : y ∈ Subgroup.zpowers x) (hyD : y ∈ D) : y = 1 := by
  rcases mem_zpowers_three (orderOf_eq_three hx3 hx) hy with h | h | h
  · exact h
  · exact absurd (h ▸ hyD) hx
  · exact absurd (h ▸ hyD) (sq_not_mem hx3 hx)

theorem card_ge_27 {P D₀ D₁ D₂ : Subgroup G} (hP : IsElemAbelian 3 P) {a b c : G} (ha : a ∈ P)
    (hb : b ∈ P) (hc : c ∈ P) (ha3 : a * a * a = 1) (hb3 : b * b * b = 1) (hc3 : c * c * c = 1)
    (ha0 : a ∉ D₀) (hb1 : b ∉ D₁) (ha1 : a ∈ D₁) (hc2 : c ∉ D₂) (ha2 : a ∈ D₂)
    (hb2 : b ∈ D₂) : 27 ≤ Nat.card P := by
  have hcomm : ∀ X Y : Subgroup G, X ≤ P → Y ≤ P → ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x :=
    fun X Y hX hY x hx y hy => comm_of_elem hP (hX hx) (hY hy)
  have hzP : ∀ x ∈ P, Subgroup.zpowers x ≤ P := fun x hx => Subgroup.zpowers_le.2 hx
  have h1 : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_zpowers hb3 hb1 hx.2 ((Subgroup.zpowers_le.2 ha1) hx.1)
  have hab := B2F.card_sup_mul_card_inf_of_commute
    (hcomm (Subgroup.zpowers a) (Subgroup.zpowers b) (hzP a ha) (hzP b hb))
  rw [h1, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
    orderOf_eq_three ha3 ha0, orderOf_eq_three hb3 hb1] at hab
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ D₂ :=
    sup_le (Subgroup.zpowers_le.2 ha2) (Subgroup.zpowers_le.2 hb2)
  have h2 : (Subgroup.zpowers a ⊔ Subgroup.zpowers b) ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_zpowers hc3 hc2 hx.2 (hle hx.1)
  have habP : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ P := sup_le (hzP a ha) (hzP b hb)
  have habc := B2F.card_sup_mul_card_inf_of_commute
    (hcomm _ (Subgroup.zpowers c) habP (hzP c hc))
  rw [h2, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_three hc3 hc2, hab] at habc
  have := Subgroup.card_le_of_le (sup_le habP (hzP c hc))
  omega

namespace Ctx

variable {T L V E : Subgroup G} {z v : G} [IsMulCommutative ↥V]

namespace Cyc

variable {c : Ctx T L V E z v} {g : G} (hg : c.Cyc g)
include hg

theorem not_mem_NL1
    (hL1 : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)) :
    g ∉ Subgroup.normalizer (c.L1 : Set G) := by
  intro hgL
  apply hL1
  intro h hh
  have hgg : g * g ∈ Subgroup.normalizer (c.L1 : Set G) := Subgroup.mul_mem _ hgL hgL
  rcases hg.conj_z_cases hh with h1 | h1 | h1
  · exact (hg.fix_z hh h1).2
  · have hk : g⁻¹ * h ∈ Subgroup.normalizer (c.R1 : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hg.mem) hh
    have hkz : (g⁻¹ * h) * z * (g⁻¹ * h)⁻¹ = z := by
      calc (g⁻¹ * h) * z * (g⁻¹ * h)⁻¹ = g⁻¹ * (h * z * h⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1, hg.hz]
        _ = z := by group
    have := Subgroup.mul_mem _ hgL (hg.fix_z hk hkz).2
    rwa [mul_inv_cancel_left] at this
  · have hk : (g * g)⁻¹ * h ∈ Subgroup.normalizer (c.R1 : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ hg.mem hg.mem)) hh
    have hkz : ((g * g)⁻¹ * h) * z * ((g * g)⁻¹ * h)⁻¹ = z := by
      calc ((g * g)⁻¹ * h) * z * ((g * g)⁻¹ * h)⁻¹ = (g * g)⁻¹ * (h * z * h⁻¹) * (g * g) := by
            simp only [mul_inv_rev, inv_inv, mul_assoc]
        _ = (g * g)⁻¹ * ((g * g) * z * (g * g)⁻¹) * (g * g) := by rw [h1, hg.sq_z]
        _ = z := by group
    have := Subgroup.mul_mem _ hgg (hg.fix_z hk hkz).2
    rwa [mul_inv_cancel_left] at this

theorem exists_elt {h : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    (P : Sylow 3 ↥(Subgroup.centralizer (E : Set G))) :
    ∃ x ∈ (P : Subgroup ↥(Subgroup.centralizer (E : Set G))).map
      (Subgroup.centralizer (E : Set G)).subtype,
      x ∈ B6.conjSub h c.L1 ∧ x * x * x = 1 ∧
        x ∉ Subgroup.centralizer (B6.conjSub h V : Set G) := by
  obtain ⟨a, haL1, ha3, haV⟩ := c.exists_a
  set x₀ := h * a * h⁻¹ with hx₀
  have hx₀K : x₀ ∈ Subgroup.centralizer (E : Set G) := hg.conj_mem_CE hh (c.L1_le haL1).2
  have hx₀L : x₀ ∈ B6.conjSub h c.L1 := by rw [B6.mem_conjSub, hx₀]; simpa [mul_assoc] using haL1
  have hx₀3 : x₀ * x₀ * x₀ = 1 := by
    rw [hx₀, show h * a * h⁻¹ * (h * a * h⁻¹) * (h * a * h⁻¹) = h * (a * a * a) * h⁻¹ by group,
      ha3]
    group
  have hx₀V : x₀ ∉ Subgroup.centralizer (B6.conjSub h V : Set G) := by
    rw [centralizer_conjSub, B6.mem_conjSub, hx₀]
    simpa [mul_assoc] using haV
  obtain ⟨k, hk⟩ := exists_conj_mem_sylow P (x := ⟨x₀, hx₀K⟩) (Subtype.ext (by simpa using hx₀3))
  have hkK : (k : G) ∈ Subgroup.centralizer (E : Set G) := k.2
  obtain ⟨hkV, hkL⟩ := c.CE_conjSub hh hkK
  have hkVN := mem_normalizer_of_conjSub_eq hkV
  have hkLN := mem_normalizer_of_conjSub_eq hkL
  refine ⟨(k : G) * x₀ * (k : G)⁻¹, ⟨_, hk, rfl⟩, ?_, ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.1 hkLN x₀).1 hx₀L
  · rw [show (k : G) * x₀ * (k : G)⁻¹ * ((k : G) * x₀ * (k : G)⁻¹) * ((k : G) * x₀ * (k : G)⁻¹) =
      (k : G) * (x₀ * x₀ * x₀) * (k : G)⁻¹ by group, hx₀3]
    group
  · intro hV
    apply hx₀V
    exact (Subgroup.mem_normalizer_iff.1
      (F7.normalizer_le_normalizer_centralizer _ hkVN) x₀).2 hV

theorem le_of_mem_centralizer {h h' : G} (hh : h ∈ Subgroup.normalizer (E : Set G))
    (hh' : h' ∈ Subgroup.normalizer (E : Set G)) {x : G} (hx : x ∈ B6.conjSub h c.L1)
    (hx3 : x * x * x = 1) (hx1 : x ∉ Subgroup.centralizer (B6.conjSub h V : Set G))
    (hxC : x ∈ Subgroup.centralizer (B6.conjSub h' V : Set G)) :
    B6.conjSub h c.L1 ≤ Subgroup.centralizer (B6.conjSub h' V : Set G) := by
  refine hg.conjL1_le_of_mem hh (fun k hk => ?_) hx hxC hx3 hx1
  exact F7.normalizer_le_normalizer_centralizer _
    (mem_normalizer_of_conjSub_eq (c.CE_conjSub hh' hk).1)

theorem false_of_not_le_N_L1 (h12210 : Stmt12_2_10) (hcomm : ⁅pCoreOf 2 (L ⊔ T), L⁆ = V)
    (hL1 : ¬ Subgroup.normalizer (c.R1 : Set G) ≤ Subgroup.normalizer (c.L1 : Set G)) : False := by
  have hgE := hg.NR1_le_NE hg.mem
  have hggE : g * g ∈ Subgroup.normalizer (E : Set G) := Subgroup.mul_mem _ hgE hgE
  have h1E : (1 : G) ∈ Subgroup.normalizer (E : Set G) := Subgroup.one_mem _
  have hgL := hg.not_mem_NL1 hL1
  set K := Subgroup.centralizer (E : Set G) with hK
  obtain ⟨P⟩ : Nonempty (Sylow 3 ↥K) := inferInstance
  set Pg := (P : Subgroup ↥K).map K.subtype with hPg
  have hPK : Pg ≤ K := Subgroup.map_subtype_le _
  have hP3 : IsPGroup 3 Pg := P.isPGroup'.map _
  have hPe := hg.isElemAbelian h12210 hcomm hPK hP3
  have hP9 : Nat.card Pg ≤ 9 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := hP3.exists_card_eq
    have hk2 := c.le_two_of_elem3 (hPK.trans c.CE_le_M) hPe hk
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  obtain ⟨a, haP, haL, ha3, haV⟩ := hg.exists_elt h1E P
  obtain ⟨b, hbP, hbL, hb3, hbV⟩ := hg.exists_elt hgE P
  obtain ⟨d, hdP, hdL, hd3, hdV⟩ := hg.exists_elt hggE P
  rw [B6.conjSub_one] at haL haV
  by_cases hα : c.L1 ≤ Subgroup.centralizer (B6.conjSub g V : Set G)
  ·
    obtain ⟨h1, h2, h3, h4, h5⟩ := hg.sym hα
    have := card_ge_27 hPe haP hbP hdP ha3 hb3 hd3 haV hbV (hα haL) hdV (h1 haL) (h3 hbL)
    omega
  ·
    obtain ⟨s1, s2, s3, s4, s5⟩ := hg.sym'
    have haVg : a ∉ Subgroup.centralizer (B6.conjSub g V : Set G) := fun h => hα (by
      have := hg.le_of_mem_centralizer h1E hgE (x := a) (by rwa [B6.conjSub_one])
        ha3 (by rwa [B6.conjSub_one]) h
      rwa [B6.conjSub_one] at this)
    have haVgg : a ∉ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) := fun h => hα (s1 (by
      have := hg.le_of_mem_centralizer h1E hggE (x := a) (by rwa [B6.conjSub_one])
        ha3 (by rwa [B6.conjSub_one]) h
      rwa [B6.conjSub_one] at this))
    have hbV0 : b ∉ Subgroup.centralizer (V : Set G) := fun h => hα (s2 (by
      have := hg.le_of_mem_centralizer hgE h1E hbL hb3 hbV (by rwa [B6.conjSub_one])
      rwa [B6.conjSub_one] at this))
    have hbVgg : b ∉ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) := fun h => hα (s3
      (hg.le_of_mem_centralizer hgE hggE hbL hb3 hbV h))
    have hdV0 : d ∉ Subgroup.centralizer (V : Set G) := fun h => hα (s4 (by
      have := hg.le_of_mem_centralizer hggE h1E hdL hd3 hdV (by rwa [B6.conjSub_one])
      rwa [B6.conjSub_one] at this))
    have hdVg : d ∉ Subgroup.centralizer (B6.conjSub g V : Set G) := fun h => hα (s5
      (hg.le_of_mem_centralizer hggE hgE hdL hd3 hdV h))
    have hcard_eq : ∀ h : G, h ∈ Subgroup.normalizer (E : Set G) →
        B6.conjSub h c.L1 ≤ c.L1 → h ∈ Subgroup.normalizer (c.L1 : Set G) := by
      intro h hh hle
      apply mem_normalizer_of_conjSub_eq
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub])
    have hL1N : K ≤ Subgroup.normalizer (c.L1 : Set G) := c.CE_le_N_L1
    have hb_a : b ∉ Subgroup.zpowers a := by
      intro hb
      have hbL1 : b ∈ c.L1 := (Subgroup.zpowers_le.2 haL) hb
      exact hgL (hcard_eq g hgE (hg.conjL1_le_of_mem hgE hL1N hbL hbL1 hb3 hbV))
    have hd_a : d ∉ Subgroup.zpowers a := by
      intro hd
      have hdL1 : d ∈ c.L1 := (Subgroup.zpowers_le.2 haL) hd
      have hggN := hcard_eq (g * g) hggE (hg.conjL1_le_of_mem hggE hL1N hdL hdL1 hd3 hdV)
      apply hgL
      have hg3 := mem_normalizer_of_conjSub_eq hg.cube_conjSub.2
      have := Subgroup.mul_mem _ hg3 (Subgroup.inv_mem _ hggN)
      rwa [show g * g * g * (g * g)⁻¹ = g by group] at this
    have hd_b : d ∉ Subgroup.zpowers b := by
      intro hd
      have hdL1 : d ∈ B6.conjSub g c.L1 := (Subgroup.zpowers_le.2 hbL) hd
      have hN : K ≤ Subgroup.normalizer (B6.conjSub g c.L1 : Set G) := fun k hk =>
        mem_normalizer_of_conjSub_eq (c.CE_conjSub hgE hk).2
      have hle := hg.conjL1_le_of_mem hggE hN hdL hdL1 hd3 hdV
      have heq : B6.conjSub (g * g) c.L1 = B6.conjSub g c.L1 :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [B6.card_conjSub, B6.card_conjSub])
      apply hgL
      apply mem_normalizer_of_conjSub_eq
      rw [B6.conjSub_mul] at heq
      exact (B6.conjSub g).injective heq
    have haP' := Subgroup.zpowers_le.2 haP
    have hbP' := Subgroup.zpowers_le.2 hbP
    have hcommab : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x :=
      fun x hx y hy => comm_of_elem hPe (haP' hx) (hbP' hy)
    have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      rcases mem_zpowers_three (orderOf_eq_three hb3 hbV) hx.2 with h | h | h
      · exact h
      · exact absurd (h ▸ hx.1) hb_a
      · exfalso
        apply hb_a
        have : b = (b * b) * (b * b) := by
          calc b = (b * b * b) * b := by rw [hb3, one_mul]
            _ = (b * b) * (b * b) := by group
        rw [this, ← h]
        exact Subgroup.mul_mem _ hx.1 hx.1
    have hcab := B2F.card_sup_mul_card_inf_of_commute hcommab
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_three ha3 haV, orderOf_eq_three hb3 hbV] at hcab
    have hPeq : Subgroup.zpowers a ⊔ Subgroup.zpowers b = Pg :=
      Subgroup.eq_of_le_of_card_ge (sup_le haP' hbP') (by rw [hcab]; exact hP9)
    have hdmem : d ∈ (Subgroup.zpowers a : Set G) * (Subgroup.zpowers b : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (fun x hx =>
        Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G)
          (Subgroup.mem_centralizer_iff.2 fun y hy => (hcommab x hx y hy).symm)), hPeq]
      exact hdP
    obtain ⟨α, hα', β, hβ, hdαβ⟩ := hdmem
    have hdαβ' : d = α * β := hdαβ.symm
    have hao := orderOf_eq_three ha3 haV
    have hbo := orderOf_eq_three hb3 hbV
    have hrel : ∀ h ∈ ({1, g, g * g} : Set G), a ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        b ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        d ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        a⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G) ∨
          (a * a)⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G) := by
      intro h hh haC hbC _
      have hhE : h ∈ Subgroup.normalizer (E : Set G) := by
        rcases hh with rfl | rfl | rfl
        · exact h1E
        · exact hgE
        · exact hggE
      rcases hg.idx3 h12210 hhE hPK hP3 haP hbP haC with h | h | h
      · exact absurd h hbC
      · exact Or.inl h
      · exact Or.inr h
    have hα2 : α = a ∨ α = a * a := by
      rcases mem_zpowers_three hao hα' with h | h | h
      · exfalso; apply hd_b; rw [hdαβ', h, one_mul]; exact hβ
      · exact Or.inl h
      · exact Or.inr h
    have hβ2 : β = b ∨ β = b * b := by
      rcases mem_zpowers_three hbo hβ with h | h | h
      · exfalso; apply hd_a; rw [hdαβ', h, mul_one]; exact hα'
      · exact Or.inl h
      · exact Or.inr h
    have hc : a * b = b * a := comm_of_elem hPe haP hbP
    have ha_inv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact ha3)
    have haa_inv : (a * a)⁻¹ = a := inv_eq_of_mul_eq_one_right ha3
    have hsq1 : ((a * a)⁻¹ * b) * ((a * a)⁻¹ * b) = a * a * (b * b) := by
      rw [haa_inv]
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hc]
        _ = a * a * (b * b) := by group
    have hsq2 : (a⁻¹ * b) * (a⁻¹ * b) = a * (b * b) := by
      rw [ha_inv]
      calc a * a * b * (a * a * b) = a * a * (b * a) * a * b := by group
        _ = a * a * (a * b) * a * b := by rw [hc]
        _ = a * a * a * (b * a) * b := by group
        _ = a * a * a * (a * b) * b := by rw [hc]
        _ = (a * a * a) * (a * (b * b)) := by group
        _ = a * (b * b) := by rw [ha3, one_mul]
    have hD : ∀ h ∈ ({1, g, g * g} : Set G),
        a ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        b ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        d ∉ Subgroup.centralizer (B6.conjSub h V : Set G) →
        ((α = a ∧ β = b) ∨ (α = a * a ∧ β = b * b) →
          a⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G)) ∧
        ((α = a ∧ β = b * b) ∨ (α = a * a ∧ β = b) →
          (a * a)⁻¹ * b ∈ Subgroup.centralizer (B6.conjSub h V : Set G)) := by
      intro h hh haC hbC hdC
      have hr := hrel h hh haC hbC hdC
      refine ⟨fun hcase => hr.resolve_right fun hw => hdC ?_,
        fun hcase => hr.resolve_left fun hu => hdC ?_⟩
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hdαβ', h1, h2, ← haa_inv]; exact hw
        · rw [hdαβ', h1, h2, ← hsq1]; exact Subgroup.mul_mem _ hw hw
      · rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [hdαβ', h1, h2, ← hsq2]; exact Subgroup.mul_mem _ hu hu
        · rw [hdαβ', h1, h2, ← ha_inv]; exact hu
    have hm1 : (1 : G) ∈ ({1, g, g * g} : Set G) := Or.inl rfl
    have hmg : g ∈ ({1, g, g * g} : Set G) := Or.inr (Or.inl rfl)
    have hmgg : g * g ∈ ({1, g, g * g} : Set G) := Or.inr (Or.inr rfl)
    have haV' : a ∉ Subgroup.centralizer (B6.conjSub 1 V : Set G) := by rwa [B6.conjSub_one]
    have hbV' : b ∉ Subgroup.centralizer (B6.conjSub 1 V : Set G) := by rwa [B6.conjSub_one]
    have hdV' : d ∉ Subgroup.centralizer (B6.conjSub 1 V : Set G) := by rwa [B6.conjSub_one]
    obtain ⟨k0, k0'⟩ := hD 1 hm1 haV' hbV' hdV'
    obtain ⟨k1, k1'⟩ := hD g hmg haVg hbV hdVg
    obtain ⟨k2, k2'⟩ := hD (g * g) hmgg haVgg hbVgg hdV
    rw [B6.conjSub_one] at k0 k0'
    have hfin : ∀ x ∈ Pg, x ∈ Subgroup.centralizer (V : Set G) →
        x ∈ Subgroup.centralizer (B6.conjSub g V : Set G) →
        x ∈ Subgroup.centralizer (B6.conjSub (g * g) V : Set G) → x = 1 := by
      intro x hx h0 h1 h2
      have hx3 : x * x * x = 1 := by rw [← pow_three']; exact hPe.2 x hx
      exact hg.eq_one_of_odd hcomm h0 h1 h2 (odd_orderOf_of_cube hx3)
    have hxP : a⁻¹ * b ∈ Pg := Pg.mul_mem (Pg.inv_mem haP) hbP
    have hyP : (a * a)⁻¹ * b ∈ Pg := Pg.mul_mem (Pg.inv_mem (Pg.mul_mem haP haP)) hbP
    rcases hα2 with hα1 | hα1 <;> rcases hβ2 with hβ1 | hβ1
    · have h1 := hfin _ hxP (k0 (Or.inl ⟨hα1, hβ1⟩)) (k1 (Or.inl ⟨hα1, hβ1⟩))
        (k2 (Or.inl ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = a * (a⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mem_zpowers a
    · have h1 := hfin _ hyP (k0' (Or.inl ⟨hα1, hβ1⟩)) (k1' (Or.inl ⟨hα1, hβ1⟩))
        (k2' (Or.inl ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = (a * a) * ((a * a)⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    · have h1 := hfin _ hyP (k0' (Or.inr ⟨hα1, hβ1⟩)) (k1' (Or.inr ⟨hα1, hβ1⟩))
        (k2' (Or.inr ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = (a * a) * ((a * a)⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers a) (Subgroup.mem_zpowers a)
    · have h1 := hfin _ hxP (k0 (Or.inr ⟨hα1, hβ1⟩)) (k1 (Or.inr ⟨hα1, hβ1⟩))
        (k2 (Or.inr ⟨hα1, hβ1⟩))
      apply hb_a
      rw [show b = a * (a⁻¹ * b) by group, h1, mul_one]
      exact Subgroup.mem_zpowers a

end Cyc

end Ctx

end N1246

end CFSG.Quasithin.H13
