module

public import CFSG.Monster.GMS.S365Leech
public import CFSG.Monster.GMS.S365Native
public import CFSG.Monster.GMS.Facts.Section4
import CFSG.Assembly.Defs
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

section Conj

variable {G : Type*} [Group G]

theorem conj_eq_conj_iff (g a b : G) : g * a * g⁻¹ = g * b * g⁻¹ ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun u => g⁻¹ * u * g) h
    simpa [mul_assoc] using this
  · rintro rfl
    rfl

theorem isConj_conj_iff (c g u : G) : IsConj c (g * u * g⁻¹) ↔ IsConj c u :=
  ⟨fun h => h.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩),
    fun h => h.trans (isConj_iff.mpr ⟨g, rfl⟩)⟩

open Classical in
theorem twoBCount_conj (z₀ x y t g : G) :
    twoBCount z₀ (g * x * g⁻¹) (g * y * g⁻¹) (g * t * g⁻¹) = twoBCount z₀ x y t := by
  rw [twoBCount_eq_ite, twoBCount_eq_ite]
  have e1 : g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
  have e2 : g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
  have e3 : g * t * g⁻¹ * (g * x * g⁻¹) * (g * y * g⁻¹) = g * (t * x * y) * g⁻¹ := by group
  rw [e3, e1, e2]
  simp only [isConj_conj_iff]

theorem isEightExt_conj {x y t : G} (h : IsEightExt x y t) (g : G) :
    IsEightExt (g * x * g⁻¹) (g * y * g⁻¹) (g * t * g⁻¹) := by
  obtain ⟨htt, htx, hty, ht1, htx', hty', htxy'⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [htt]; group
  · calc g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [htx]
      _ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
  · calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
      _ = g * (y * t) * g⁻¹ := by rw [hty]
      _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group
  · intro h
    apply ht1
    have := (conj_eq_conj_iff g t 1).1 (by rw [h]; group)
    exact this
  · exact fun h => htx' ((conj_eq_conj_iff g t x).1 h)
  · exact fun h => hty' ((conj_eq_conj_iff g t y).1 h)
  · intro h
    apply htxy'
    refine (conj_eq_conj_iff g t (x * y)).1 ?_
    rw [h]
    group

theorem isLineTriple_conj {a x y : G} (h : IsLineTriple a x y) (g : G) :
    IsLineTriple a (g * x * g⁻¹) (g * y * g⁻¹) := by
  obtain ⟨hx, hy, hxy⟩ := h
  refine ⟨(isConj_conj_iff a g x).2 hx, (isConj_conj_iff a g y).2 hy, ?_⟩
  have : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  rw [this]
  exact (isConj_conj_iff a g _).2 hxy

end Conj

section Lifts

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem cls_of_typeSet
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (L : LeechSystem z₀)
    {u : G} (hu : u ∈ leechQ z₀) :
    (L.vec u ∈ co1Orbit 0 → u * u = 1 ∧ u ≠ 1 ∧ IsConj a u ∧ ¬ IsConj z₀ u) ∧
      (L.vec u ∈ co1Orbit 2 → u * u = 1 ∧ u ≠ 1 ∧ IsConj z₀ u) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 : u ∈ L.typeSet 0 := ⟨hu, h⟩
    have hA := isConj_of_mem_typeSet_zero I hG (IsConj.refl z₀) L h0
    exact ⟨L.mul_self_of_mem_typeSet_zero h0, L.ne_one_of_mem_typeSet h0, hA,
      fun hB => hG.not_isConj (hA.trans hB.symm)⟩
  · have h2 : u ∈ L.typeSet 2 := ⟨hu, h⟩
    exact ⟨L.mul_self_of_mem_typeSet_two h2, L.ne_one_of_mem_typeSet h2,
      isConj_of_mem_typeSet_two I hG (IsConj.refl z₀) L h2⟩

open Classical in
theorem isEightExt_of_pattern
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (L : LeechSystem z₀) {x y t : G} (hxQ : x ∈ leechQ z₀) (hyQ : y ∈ leechQ z₀)
    (htQ : t ∈ leechQ z₀) (hx : L.vec x ∈ co1Orbit 0) (hy : L.vec y ∈ co1Orbit 0)
    (hxy : L.vec x + L.vec y ∈ co1Orbit 0) {p₀ p₁ p₂ p₃ : Bool}
    (h0 : (p₀ = true ∧ L.vec t ∈ co1Orbit 2) ∨ (p₀ = false ∧ L.vec t ∈ co1Orbit 0))
    (h1 : (p₁ = true ∧ L.vec t + L.vec x ∈ co1Orbit 2) ∨
      (p₁ = false ∧ L.vec t + L.vec x ∈ co1Orbit 0))
    (h2 : (p₂ = true ∧ L.vec t + L.vec y ∈ co1Orbit 2) ∨
      (p₂ = false ∧ L.vec t + L.vec y ∈ co1Orbit 0))
    (h3 : (p₃ = true ∧ L.vec t + L.vec x + L.vec y ∈ co1Orbit 2) ∨
      (p₃ = false ∧ L.vec t + L.vec x + L.vec y ∈ co1Orbit 0)) :
    IsLineTriple a x y ∧ IsEightExt x y t ∧
      twoBCount z₀ x y t = p₀.toNat + p₁.toNat + p₂.toNat + p₃.toNat := by
  have hxyQ : x * y ∈ leechQ z₀ := (leechQ z₀).mul_mem hxQ hyQ
  have htxQ : t * x ∈ leechQ z₀ := (leechQ z₀).mul_mem htQ hxQ
  have htyQ : t * y ∈ leechQ z₀ := (leechQ z₀).mul_mem htQ hyQ
  have htxyQ : t * x * y ∈ leechQ z₀ := (leechQ z₀).mul_mem htxQ hyQ
  have vx : L.vec (x * y) = L.vec x + L.vec y := L.vec_mul x hxQ y hyQ
  have v1 : L.vec (t * x) = L.vec t + L.vec x := L.vec_mul t htQ x hxQ
  have v2 : L.vec (t * y) = L.vec t + L.vec y := L.vec_mul t htQ y hyQ
  have v3 : L.vec (t * x * y) = L.vec t + L.vec x + L.vec y := by
    rw [L.vec_mul (t * x) htxQ y hyQ, v1]
  have cx := (cls_of_typeSet I hG L hxQ).1 hx
  have cy := (cls_of_typeSet I hG L hyQ).1 hy
  have cxy := (cls_of_typeSet I hG L hxyQ).1 (by rw [vx]; exact hxy)
  have key : ∀ (u : G) (p : Bool) (v : Fin 24 → ZMod 2), u ∈ leechQ z₀ → L.vec u = v →
      ((p = true ∧ v ∈ co1Orbit 2) ∨ (p = false ∧ v ∈ co1Orbit 0)) →
      u * u = 1 ∧ u ≠ 1 ∧ (IsConj z₀ u ↔ p = true) := by
    intro u p v huQ huv hp
    rcases hp with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · obtain ⟨c1, c2, c3⟩ := (cls_of_typeSet I hG L huQ).2 (huv ▸ hv)
      exact ⟨c1, c2, ⟨fun _ => rfl, fun _ => c3⟩⟩
    · obtain ⟨c1, c2, c3, c4⟩ := (cls_of_typeSet I hG L huQ).1 (huv ▸ hv)
      exact ⟨c1, c2, ⟨fun h => absurd h c4, fun h => absurd h (by decide)⟩⟩
  obtain ⟨t0, t0', t0''⟩ := key t p₀ _ htQ rfl h0
  obtain ⟨t1, t1', t1''⟩ := key (t * x) p₁ _ htxQ v1 h1
  obtain ⟨t2, t2', t2''⟩ := key (t * y) p₂ _ htyQ v2 h2
  obtain ⟨t3, t3', t3''⟩ := key (t * x * y) p₃ _ htxyQ v3 h3
  have hxx := cx.1
  have hyy := cy.1
  have hxyxy := cxy.1
  refine ⟨⟨cx.2.2.1, cy.2.2.1, cxy.2.2.1⟩, ⟨t0, ?_, ?_, t0', ?_, ?_, ?_⟩, ?_⟩
  · exact mul_comm_of_mul_self_eq_one t0 hxx t1
  · exact mul_comm_of_mul_self_eq_one t0 hyy t2
  · rintro rfl
    exact t1' hxx
  · rintro rfl
    exact t2' hyy
  · rintro rfl
    apply t3'
    rw [mul_assoc]
    exact hxyxy
  · rw [twoBCount_eq_ite]
    have e : ∀ (u : G) (p : Bool), (IsConj z₀ u ↔ p = true) →
        (if IsConj z₀ u then 1 else 0 : ℕ) = p.toNat := by
      intro u p hp
      cases p
      · have : ¬ IsConj z₀ u := fun h => by simpa using hp.1 h
        simp [this, -isConj_iff]
      · have : IsConj z₀ u := hp.2 rfl
        simp [this, -isConj_iff]
    rw [e _ _ t0'', e _ _ t1'', e _ _ t2'', e _ _ t3'']

theorem exists_model
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hF : Co1EightFacts) :
    ∃ x y : G, IsLineTriple a x y ∧ ∀ n : ℕ, (n = 1 ∨ n = 3 ∨ n = 4) →
      ∃ t : G, IsEightExt x y t ∧ twoBCount z₀ x y t = n := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG (IsConj.refl z₀)
  obtain ⟨xv, yv, hxv, hyv, hxyv, ⟨v1, h1a, h1b, h1c, h1d⟩, ⟨v3, h3a, h3b, h3c, h3d⟩,
    ⟨v4, h4a, h4b, h4c, h4d⟩⟩ := hF
  obtain ⟨x, hxQ, hx⟩ := L.vec_surj xv
  obtain ⟨y, hyQ, hy⟩ := L.vec_surj yv
  obtain ⟨t1, ht1Q, ht1⟩ := L.vec_surj v1
  obtain ⟨t3, ht3Q, ht3⟩ := L.vec_surj v3
  obtain ⟨t4, ht4Q, ht4⟩ := L.vec_surj v4
  have hxo : L.vec x ∈ co1Orbit 0 := by rw [hx]; exact hxv
  have hyo : L.vec y ∈ co1Orbit 0 := by rw [hy]; exact hyv
  have hxyo : L.vec x + L.vec y ∈ co1Orbit 0 := by rw [hx, hy]; exact hxyv
  have k1 := isEightExt_of_pattern I hG L hxQ hyQ ht1Q hxo hyo hxyo (p₀ := true) (p₁ := false)
    (p₂ := false) (p₃ := false) (Or.inl ⟨rfl, by rw [ht1]; exact h1a⟩)
    (Or.inr ⟨rfl, by rw [ht1, hx]; exact h1b⟩) (Or.inr ⟨rfl, by rw [ht1, hy]; exact h1c⟩)
    (Or.inr ⟨rfl, by rw [ht1, hx, hy]; exact h1d⟩)
  have k3 := isEightExt_of_pattern I hG L hxQ hyQ ht3Q hxo hyo hxyo (p₀ := false) (p₁ := true)
    (p₂ := true) (p₃ := true) (Or.inr ⟨rfl, by rw [ht3]; exact h3a⟩)
    (Or.inl ⟨rfl, by rw [ht3, hx]; exact h3b⟩) (Or.inl ⟨rfl, by rw [ht3, hy]; exact h3c⟩)
    (Or.inl ⟨rfl, by rw [ht3, hx, hy]; exact h3d⟩)
  have k4 := isEightExt_of_pattern I hG L hxQ hyQ ht4Q hxo hyo hxyo (p₀ := true) (p₁ := true)
    (p₂ := true) (p₃ := true) (Or.inl ⟨rfl, by rw [ht4]; exact h4a⟩)
    (Or.inl ⟨rfl, by rw [ht4, hx]; exact h4b⟩) (Or.inl ⟨rfl, by rw [ht4, hy]; exact h4c⟩)
    (Or.inl ⟨rfl, by rw [ht4, hx, hy]; exact h4d⟩)
  refine ⟨x, y, k1.1, fun n hn => ?_⟩
  rcases hn with rfl | rfl | rfl
  · exact ⟨t1, k1.2.1, k1.2.2⟩
  · exact ⟨t3, k3.2.1, k3.2.2⟩
  · exact ⟨t4, k4.2.1, k4.2.2⟩

theorem eightGroupExists_of_facts
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hF : Co1EightFacts) : EightGroupExists a z₀ := by
  obtain ⟨x₀, y₀, hl₀, hmodel⟩ := exists_model I hG hF
  intro x y hl n hn
  obtain ⟨t₀, ht₀, hc₀⟩ := hmodel n hn
  obtain ⟨g₁, hg₁⟩ := isConj_iff.mp (hl₀.1.symm.trans hl.1)
  have hl₁ := isLineTriple_conj hl₀ g₁
  rw [hg₁] at hl₁
  obtain ⟨h, hh, hhy⟩ := isConj_of_mem_twoANbr I.sls I.tableV I.leech hG hl.1
    (c := g₁ * y₀ * g₁⁻¹) ⟨hl₁.2.1, hl₁.2.2⟩ ⟨hl.2.1, hl.2.2⟩
  have hhx : h * x * h⁻¹ = x := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_singleton_iff.mp hh |>.symm.symm
  have hgx : h * g₁ * x₀ * (h * g₁)⁻¹ = x := by
    calc h * g₁ * x₀ * (h * g₁)⁻¹ = h * (g₁ * x₀ * g₁⁻¹) * h⁻¹ := by group
      _ = x := by rw [hg₁, hhx]
  have hgy : h * g₁ * y₀ * (h * g₁)⁻¹ = y := by
    calc h * g₁ * y₀ * (h * g₁)⁻¹ = h * (g₁ * y₀ * g₁⁻¹) * h⁻¹ := by group
      _ = y := hhy
  refine ⟨h * g₁ * t₀ * (h * g₁)⁻¹, ?_, ?_⟩
  · have := isEightExt_conj ht₀ (h * g₁)
    rwa [hgx, hgy] at this
  · rw [← hgx, ← hgy, twoBCount_conj]
    exact hc₀

end Lifts

end S365

end CFSG.Monster.GMS
