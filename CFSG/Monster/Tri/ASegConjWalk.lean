module

public import CFSG.Monster.Tri.ConeCover
public import CFSG.Monster.GMS.TwoAGraph

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.B.Recog CFSG.Monster.B.GSide CFSG.Monster.GMS

section Walks

variable {V : Type*} {Γ : SimpleGraph V}

theorem exists_walk_three {u v : V} (c : Γ.Walk u v) (hc : c.length = 3) :
    ∃ (x₁ x₂ : V) (h₀₁ : Γ.Adj u x₁) (h₁₂ : Γ.Adj x₁ x₂) (h₂₃ : Γ.Adj x₂ v),
      c = .cons h₀₁ (.cons h₁₂ (.cons h₂₃ .nil)) := by
  cases c with
  | nil => simp at hc
  | cons h₀₁ c =>
    cases c with
    | nil => simp at hc
    | cons h₁₂ c =>
      cases c with
      | nil => simp at hc
      | cons h₂₃ c =>
        cases c with
        | nil => exact ⟨_, _, h₀₁, h₁₂, h₂₃, rfl⟩
        | cons _ _ => simp at hc

theorem homotopic_of_inducedNull {Φ : Set V} (h : InducedNull Γ Φ) {u v : V}
    {p q : Γ.Walk u v} (hp : ∀ w ∈ p.support, w ∈ Φ) (hq : ∀ w ∈ q.support, w ∈ Φ) :
    Homotopic p q := by
  rw [homotopic_iff_append_reverse_nil]
  refine h u _ fun w hw => ?_
  rcases (Walk.mem_support_append_iff _ _).1 hw with hw | hw
  · exact hp w hw
  · exact hq w (by simpa using hw)

end Walks

section Conj

variable {G : Type*} [Group G] {a : G}

@[expose] def twoAConjHom (a g : G) : twoAGraph a →g twoAGraph a where
  toFun x := g • x
  map_rel' h := twoAGraph_adj_smul g h

theorem twoAConjHom_apply (a g : G) (x : ConjVert a) : twoAConjHom a g x = g • x := rfl

@[expose] def conjWalk {x y : ConjVert a} (g : G) (hx : g • x = x) (hy : g • y = y)
    (p : (twoAGraph a).Walk x y) : (twoAGraph a).Walk x y :=
  (p.map (twoAConjHom a g)).copy ((twoAConjHom_apply a g x).trans hx)
    ((twoAConjHom_apply a g y).trans hy)

theorem support_conjWalk {x y : ConjVert a} (g : G) (hx : g • x = x) (hy : g • y = y)
    (p : (twoAGraph a).Walk x y) :
    (conjWalk g hx hy p).support = p.support.map (g • ·) := by
  rw [conjWalk, Walk.support_copy, Walk.support_map]
  rfl

theorem conjWalk_one {x y : ConjVert a} (hx : (1 : G) • x = x) (hy : (1 : G) • y = y)
    (p : (twoAGraph a).Walk x y) : conjWalk 1 hx hy p = p := by
  apply Walk.ext_support
  simp [support_conjWalk]

theorem conjWalk_mul {x y : ConjVert a} (g h : G) (hgx : g • x = x) (hgy : g • y = y)
    (hhx : h • x = x) (hhy : h • y = y) (hghx : (g * h) • x = x) (hghy : (g * h) • y = y)
    (p : (twoAGraph a).Walk x y) :
    conjWalk (g * h) hghx hghy p = conjWalk g hgx hgy (conjWalk h hhx hhy p) := by
  apply Walk.ext_support
  simp [support_conjWalk, mul_smul, List.map_map, Function.comp_def]

theorem conjWalk_conjWalk_inv {x y : ConjVert a} (g : G) (hgx : g • x = x) (hgy : g • y = y)
    (hix : g⁻¹ • x = x) (hiy : g⁻¹ • y = y) (p : (twoAGraph a).Walk x y) :
    conjWalk g hgx hgy (conjWalk g⁻¹ hix hiy p) = p := by
  apply Walk.ext_support
  simp [support_conjWalk, List.map_map, Function.comp_def]

theorem conjWalk_inv_conjWalk {x y : ConjVert a} (g : G) (hgx : g • x = x) (hgy : g • y = y)
    (hix : g⁻¹ • x = x) (hiy : g⁻¹ • y = y) (p : (twoAGraph a).Walk x y) :
    conjWalk g⁻¹ hix hiy (conjWalk g hgx hgy p) = p := by
  apply Walk.ext_support
  simp [support_conjWalk, List.map_map, Function.comp_def]

theorem homotopic_conjWalk {x y : ConjVert a} (g : G) (hx : g • x = x) (hy : g • y = y)
    {p q : (twoAGraph a).Walk x y} (h : Homotopic p q) :
    Homotopic (conjWalk g hx hy p) (conjWalk g hx hy q) :=
  homotopic_copy (homotopic_map (twoAConjHom a g) h) _ _

@[expose] def walkStab {x y : ConjVert a} (p : (twoAGraph a).Walk x y) : Subgroup G where
  carrier := {h | ∃ (hx : h • x = x) (hy : h • y = y), Homotopic (conjWalk h hx hy p) p}
  one_mem' := ⟨one_smul G x, one_smul G y, by rw [conjWalk_one]⟩
  mul_mem' := by
    rintro g h ⟨hgx, hgy, hg⟩ ⟨hhx, hhy, hh⟩
    have hghx : (g * h) • x = x := by rw [mul_smul, hhx, hgx]
    have hghy : (g * h) • y = y := by rw [mul_smul, hhy, hgy]
    refine ⟨hghx, hghy, ?_⟩
    rw [conjWalk_mul g h hgx hgy hhx hhy hghx hghy]
    exact (homotopic_conjWalk g hgx hgy hh).trans hg
  inv_mem' := by
    rintro g ⟨hgx, hgy, hg⟩
    have hx' : g⁻¹ • x = x := by rw [inv_smul_eq_iff, hgx]
    have hy' : g⁻¹ • y = y := by rw [inv_smul_eq_iff, hgy]
    refine ⟨hx', hy', ?_⟩
    have h1 := homotopic_conjWalk g⁻¹ hx' hy' hg
    rw [conjWalk_inv_conjWalk g hgx hgy hx' hy'] at h1
    exact h1.symm

theorem cen_smul_of_commute {t h : G} {v : ConjVert a} (hht : h * t = t * h)
    (hv : t * (v : G) = v * t) :
    t * ((h • v : ConjVert a) : G) = ((h • v : ConjVert a) : G) * t := by
  have hth : Commute t h := hht.symm
  have htv : Commute t (v : G) := hv
  rw [coe_smul_conjVert]
  exact ((hth.mul_right htv).mul_right hth.inv_right).eq

theorem mem_walkStab_of_push {x y : ConjVert a} {p p' : (twoAGraph a).Walk x y} {t h : G}
    (hn : InducedNull (twoAGraph a) {v : ConjVert a | t * (v : G) = v * t})
    (hp' : ∀ v ∈ p'.support, t * (v : G) = v * t) (hpp' : Homotopic p p')
    (hx : h • x = x) (hy : h • y = y) (hht : h * t = t * h) : h ∈ walkStab p := by
  refine ⟨hx, hy, ?_⟩
  have hr : ∀ v ∈ (conjWalk h hx hy p').support, t * (v : G) = v * t := by
    intro v hv
    rw [support_conjWalk, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    exact cen_smul_of_commute hht (hp' u hu)
  have e1 : Homotopic p' (conjWalk h hx hy p') := homotopic_of_inducedNull hn hp' hr
  exact ((homotopic_conjWalk h hx hy hpp').trans e1.symm).trans hpp'.symm

theorem homotopic_of_push {x y : ConjVert a} {p p₁ q q₁ : (twoAGraph a).Walk x y} {t₁ s g : G}
    (hn : InducedNull (twoAGraph a) {v : ConjVert a | t₁ * (v : G) = v * t₁})
    (hp₁ : ∀ v ∈ p₁.support, t₁ * (v : G) = v * t₁) (hpp : Homotopic p p₁)
    (hq₁ : ∀ v ∈ q₁.support, s * (v : G) = v * s) (hqq : Homotopic q q₁)
    (hgx : g • x = x) (hgy : g • y = y) (hg : g * t₁ * g⁻¹ = s) (hgS : g ∈ walkStab p) :
    Homotopic q p := by
  have hx' : g⁻¹ • x = x := by rw [inv_smul_eq_iff, hgx]
  have hy' : g⁻¹ • y = y := by rw [inv_smul_eq_iff, hgy]
  have ht₁ : t₁ = g⁻¹ * s * g := by rw [← hg]; group
  have hr : ∀ v ∈ (conjWalk g⁻¹ hx' hy' q₁).support, t₁ * (v : G) = v * t₁ := by
    intro v hv
    rw [support_conjWalk, List.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have hsu := hq₁ u hu
    rw [coe_smul_conjVert, ht₁]
    calc g⁻¹ * s * g * (g⁻¹ * (u : G) * g⁻¹⁻¹) = g⁻¹ * (s * u) * g := by group
      _ = g⁻¹ * (u * s) * g := by rw [hsu]
      _ = g⁻¹ * u * g⁻¹⁻¹ * (g⁻¹ * s * g) := by group
  have e1 : Homotopic (conjWalk g⁻¹ hx' hy' q₁) p₁ := homotopic_of_inducedNull hn hr hp₁
  have e2 : conjWalk g hgx hgy (conjWalk g⁻¹ hx' hy' q₁) = q₁ :=
    conjWalk_conjWalk_inv g hgx hgy hx' hy' q₁
  have e3 := homotopic_conjWalk g hgx hgy e1
  rw [e2] at e3
  obtain ⟨_, _, hgp⟩ := hgS
  exact hqq.trans (e3.trans ((homotopic_conjWalk g hgx hgy hpp.symm).trans hgp))

end Conj

section Core

variable {G : Type*} [Group G] {a : G}

abbrev twoStab (x y : ConjVert a) : Subgroup G :=
  Subgroup.centralizer ({(x : G)} : Set G) ⊓ Subgroup.centralizer {(y : G)}

theorem mem_twoStab {x y : ConjVert a} {t : G} :
    t ∈ twoStab x y ↔ t * (x : G) = x * t ∧ t * (y : G) = y * t := by
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem exists_push_three {x y a₁ b₁ : ConjVert a} (hxa : (twoAGraph a).Adj x a₁)
    (hab : (twoAGraph a).Adj a₁ b₁) (hby : (twoAGraph a).Adj b₁ y)
    (h4 : ∀ (u : ConjVert a) (c : (twoAGraph a).Walk u u), c.length ≤ 4 → Homotopic c .nil)
    {t : G} (hxt : t * (x : G) = x * t) (hyt : t * (y : G) = y * t) (hat : t * (a₁ : G) = a₁ * t)
    (hb : ∃ b₂ : ConjVert a, (twoAGraph a).Adj a₁ b₂ ∧ (twoAGraph a).Adj b₂ y ∧
      t * (b₂ : G) = b₂ * t) :
    ∃ p' : (twoAGraph a).Walk x y, (∀ v ∈ p'.support, t * (v : G) = v * t) ∧
      Homotopic (.cons hxa (.cons hab (.cons hby .nil))) p' := by
  obtain ⟨b₂, h₁, h₂, hbt⟩ := hb
  refine ⟨.cons hxa (.cons h₁ (.cons h₂ .nil)), ?_, ?_⟩
  · intro v hv
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hxt
    · exact hat
    · exact hbt
    · exact hyt
  · exact (homotopic_of_length_add_le h4 (.cons hab (.cons hby .nil)) (.cons h₁ (.cons h₂ .nil))
      (by simp)).cons hxa

theorem homotopic_walks_three {x y : ConjVert a}
    (h4 : ∀ (u : ConjVert a) (c : (twoAGraph a).Walk u u), c.length ≤ 4 → Homotopic c .nil)
    (hnull : ∀ t : G, orderOf t = 2 →
      InducedNull (twoAGraph a) {v : ConjVert a | t * (v : G) = v * t})
    (hpush : ∀ t ∈ twoStab x y, orderOf t = 2 → ∀ a₁ b₁ : ConjVert a,
      (twoAGraph a).Adj x a₁ → (twoAGraph a).Adj a₁ b₁ → (twoAGraph a).Adj b₁ y →
        t * (a₁ : G) = a₁ * t → ∃ b₂ : ConjVert a, (twoAGraph a).Adj a₁ b₂ ∧
          (twoAGraph a).Adj b₂ y ∧ t * (b₂ : G) = b₂ * t)
    (hinv : ∀ a₁ b₁ : ConjVert a, (twoAGraph a).Adj x a₁ → (twoAGraph a).Adj a₁ b₁ →
      (twoAGraph a).Adj b₁ y → ∃ t ∈ twoStab x y, orderOf t = 2 ∧ t * (a₁ : G) = a₁ * t)
    (hsec : ∀ a₁ : ConjVert a, (twoAGraph a).Adj x a₁ → ∀ t₁ ∈ twoStab x y, orderOf t₁ = 2 →
      t₁ * (a₁ : G) = a₁ * t₁ → ∃ t₂ ∈ twoStab x y, orderOf t₂ = 2 ∧ t₂ * (a₁ : G) = a₁ * t₂ ∧
        t₂ ≠ t₁)
    (hgen : ∀ t₁ ∈ twoStab x y, ∀ t₂ ∈ twoStab x y, orderOf t₁ = 2 → orderOf t₂ = 2 → t₁ ≠ t₂ →
      twoStab x y ⊓ Subgroup.centralizer {t₁} ⊔ twoStab x y ⊓ Subgroup.centralizer {t₂} =
        twoStab x y)
    (hconj : ∀ t ∈ twoStab x y, ∀ s ∈ twoStab x y, orderOf t = 2 → orderOf s = 2 →
      ∃ g ∈ twoStab x y, g * t * g⁻¹ = s) :
    ∀ p q : (twoAGraph a).Walk x y, p.length = 3 → q.length = 3 → Homotopic p q := by
  intro p q hp hq
  obtain ⟨a₁, b₁, hxa, hab, hby, rfl⟩ := exists_walk_three p hp
  obtain ⟨a₂, b₂, hxa', hab', hby', rfl⟩ := exists_walk_three q hq
  obtain ⟨t₁, ht₁T, ht₁2, ht₁a⟩ := hinv a₁ b₁ hxa hab hby
  obtain ⟨t₂, ht₂T, ht₂2, ht₂a, ht₂ne⟩ := hsec a₁ hxa t₁ ht₁T ht₁2 ht₁a
  obtain ⟨p₁, hp₁, hpp₁⟩ := exists_push_three hxa hab hby h4
    (mem_twoStab.1 ht₁T).1 (mem_twoStab.1 ht₁T).2 ht₁a
    (hpush t₁ ht₁T ht₁2 a₁ b₁ hxa hab hby ht₁a)
  obtain ⟨p₂, hp₂, hpp₂⟩ := exists_push_three hxa hab hby h4
    (mem_twoStab.1 ht₂T).1 (mem_twoStab.1 ht₂T).2 ht₂a
    (hpush t₂ ht₂T ht₂2 a₁ b₁ hxa hab hby ht₂a)
  have hfix : ∀ h ∈ twoStab x y, h • x = x ∧ h • y = y := fun h hh =>
    ⟨(smul_eq_self_iff h x).2 (Subgroup.mem_inf.1 hh).1,
      (smul_eq_self_iff h y).2 (Subgroup.mem_inf.1 hh).2⟩
  have hle : twoStab x y ≤ walkStab (.cons hxa (.cons hab (.cons hby .nil)) :
      (twoAGraph a).Walk x y) := by
    rw [← hgen t₁ ht₁T t₂ ht₂T ht₁2 ht₂2 (Ne.symm ht₂ne)]
    refine sup_le ?_ ?_
    · intro h hh
      obtain ⟨hhT, hht⟩ := Subgroup.mem_inf.1 hh
      exact mem_walkStab_of_push (hnull t₁ ht₁2) hp₁ hpp₁ (hfix h hhT).1 (hfix h hhT).2
        (Subgroup.mem_centralizer_singleton_iff.1 hht)
    · intro h hh
      obtain ⟨hhT, hht⟩ := Subgroup.mem_inf.1 hh
      exact mem_walkStab_of_push (hnull t₂ ht₂2) hp₂ hpp₂ (hfix h hhT).1 (hfix h hhT).2
        (Subgroup.mem_centralizer_singleton_iff.1 hht)
  obtain ⟨s, hsT, hs2, hsa⟩ := hinv a₂ b₂ hxa' hab' hby'
  obtain ⟨q₁, hq₁, hqq₁⟩ := exists_push_three hxa' hab' hby' h4
    (mem_twoStab.1 hsT).1 (mem_twoStab.1 hsT).2 hsa
    (hpush s hsT hs2 a₂ b₂ hxa' hab' hby' hsa)
  obtain ⟨g, hgT, hg⟩ := hconj t₁ ht₁T s hsT ht₁2 hs2
  exact (homotopic_of_push (hnull t₁ ht₁2) hp₁ hpp₁ hq₁ hqq₁ (hfix g hgT).1 (hfix g hgT).2 hg
    (hle hgT)).symm

end Core

end CFSG.Monster.Tri
