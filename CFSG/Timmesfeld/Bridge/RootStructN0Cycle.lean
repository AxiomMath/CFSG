module

public import CFSG.Timmesfeld.Bridge.RootStructN0Bad
public import CFSG.Timmesfeld.Bridge.RootStructR2Degen

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

@[expose] def InvTorus (D : Set G) (g : G) : Prop :=
  (orderOf g).Prime ∧ orderOf g ≠ 2 ∧ ∃ y ∈ D, y * g * y⁻¹ = g⁻¹

@[expose] def FixUnique (D : Set G) : Prop :=
  ∀ ⦃d a e g : G⦄, d ∈ D → a ∈ D → Commute d a → d * a ∈ D → a ∉ rootSet D d → e ∈ D →
    Commute d e → d * e ∈ D → e ∉ rootGroup D d ⊔ rootGroup D a → InvTorus D g →
    g * d * g⁻¹ ∈ rootSet D d →
    (∀ u ∈ rootGroup D d ⊔ rootGroup D a, g * u * g⁻¹ ∈ rootGroup D d ⊔ rootGroup D a) →
    (∀ u ∈ rootGroup D d ⊔ rootGroup D e, g * u * g⁻¹ ∈ rootGroup D d ⊔ rootGroup D e) →
    (∃ t ∈ D, t ∈ rootGroup D d ⊔ rootGroup D a ∧ t ∉ rootSet D d ∧ g * t * g⁻¹ ∈ rootSet D t) ∧
      ∀ t ∈ D, t ∈ rootGroup D d ⊔ rootGroup D a → t ∉ rootSet D d → g * t * g⁻¹ ∈ rootSet D t →
        ∀ t' ∈ D, t' ∈ rootGroup D d ⊔ rootGroup D a → t' ∉ rootSet D d →
          g * t' * g⁻¹ ∈ rootSet D t' → t' ∈ rootSet D t

theorem conj_mem_rootGroup_of_conj_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {g d u : G} (hg : g * d * g⁻¹ ∈ rootSet D d) (hu : u ∈ rootGroup D d) :
    g * u * g⁻¹ ∈ rootGroup D d := by
  have h1 : g * u * g⁻¹ ∈ rootGroup D (g * d * g⁻¹) := by
    rw [rootGroup_conj hclass]
    exact ⟨u, hu, rfl⟩
  rwa [rootGroup_eq_of_mem hg] at h1

theorem conj_mem_sup_of_conj_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    {g d a u : G} (hgd : g * d * g⁻¹ ∈ rootSet D d) (hga : g * a * g⁻¹ ∈ rootSet D a)
    (hu : u ∈ rootGroup D d ⊔ rootGroup D a) : g * u * g⁻¹ ∈ rootGroup D d ⊔ rootGroup D a := by
  have hle : (rootGroup D d ⊔ rootGroup D a).map (MulAut.conj g).toMonoidHom ≤
      rootGroup D d ⊔ rootGroup D a := by
    rw [Subgroup.map_sup]
    refine sup_le_sup ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact conj_mem_rootGroup_of_conj_mem_rootSet hclass hgd hv
    · rintro _ ⟨v, hv, rfl⟩
      exact conj_mem_rootGroup_of_conj_mem_rootSet hclass hga hv
  exact hle ⟨u, hu, rfl⟩

theorem conj_mem_rootSet_iff_mem_normalizer (h : Hyp G D) (hc : RootClosure D) {g d : G}
    (hd : d ∈ D) :
    g * d * g⁻¹ ∈ rootSet D d ↔ g ∈ Subgroup.normalizer (rootGroup D d : Set G) := by
  have := h.finite
  constructor
  · intro hg
    exact RootSubgroup.mem_normalizer_of_map_eq (RootDegen.map_conj_eq_of_forall fun u hu =>
      conj_mem_rootGroup_of_conj_mem_rootSet h.isClass hg hu)
  · intro hg
    have h1 : g * d * g⁻¹ ∈ rootGroup D d :=
      (Subgroup.mem_normalizer_iff.1 hg d).1 (rootSet_subset_rootGroup D d (mem_rootSet_self hd))
    refine mem_rootSet_of_mem_rootGroup_of_ne_one h.root hc hd h1 fun h' => h.root.ne_one hd ?_
    have := congrArg (fun w => g⁻¹ * w * g) h'
    simpa [mul_assoc] using this

theorem conj_mem_rootSet_zpow (h : Hyp G D) (hc : RootClosure D) {g d : G} (hd : d ∈ D)
    (hg : g * d * g⁻¹ ∈ rootSet D d) (n : ℤ) : g ^ n * d * (g ^ n)⁻¹ ∈ rootSet D d :=
  (conj_mem_rootSet_iff_mem_normalizer h hc hd).2
    (Subgroup.zpow_mem _ ((conj_mem_rootSet_iff_mem_normalizer h hc hd).1 hg) n)

theorem conj_mem_rootSet_of_mem_zpowers (h : Hyp G D) (hc : RootClosure D) {g g' d : G}
    (hd : d ∈ D) (hg : g * d * g⁻¹ ∈ rootSet D d) (hg' : g' ∈ Subgroup.zpowers g) :
    g' * d * g'⁻¹ ∈ rootSet D d := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg'
  exact conj_mem_rootSet_zpow h hc hd hg n

theorem conj_mem_rootSet_of_mem_rootSet (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {g d d' : G}
    (hg : g * d * g⁻¹ ∈ rootSet D d) (hd' : d' ∈ rootSet D d) :
    g * d' * g⁻¹ ∈ rootSet D d' := by
  have h1 : g * d' * g⁻¹ ∈ rootSet D (g * d * g⁻¹) := by
    rw [rootSet_conj hclass]
    exact ⟨d', hd', rfl⟩
  rw [rootSet_eq_of_mem hg, ← rootSet_eq_of_mem hd'] at h1
  exact h1

theorem not_mem_sup_of_not_mem_sup (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {a b c : G} (ha : a ∈ D) (hb : b ∈ D) (hcD : c ∈ D) (habT : b ∉ rootSet D a)
    (hbc : Commute b c) (hbcD : b * c ∈ D) (hcT : c ∉ rootSet D b)
    (hcL : c ∉ rootGroup D a ⊔ rootGroup D b) : a ∉ rootGroup D c ⊔ rootGroup D b := by
  intro haL
  have hD := h.root
  rw [sup_comm] at haL
  have haT : a ∉ rootSet D b := fun h' => habT (mem_rootSet_comm hb h')
  have heq := sup_rootGroup_eq_of_mem h hc hs hb hcD hbc hbcD hcT (left_mem_line hb) haL
    (hD.ne_one hb) (hD.ne_one ha) haT
  apply hcL
  rw [sup_comm, heq]
  exact right_mem_line hcD

theorem mem_rootSet_of_mem_two_lines (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {v u e t : G} (hv : v ∈ D) (hu : u ∈ D) (he : e ∈ D)
    (colu : Commute v u ∧ v * u ∈ D ∧ u ∉ rootSet D v)
    (cole : Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v) (heL : e ∉ rootGroup D v ⊔ rootGroup D u)
    (ht : t ∈ D) (htu : t ∈ rootGroup D v ⊔ rootGroup D u)
    (hte : t ∈ rootGroup D v ⊔ rootGroup D e) : t ∈ rootSet D v := by
  by_contra htT
  have hD := h.root
  have h1 := sup_rootGroup_eq_of_mem h hc hs hv hu colu.1 colu.2.1 colu.2.2 (left_mem_line hv) htu
    (hD.ne_one hv) (hD.ne_one ht) htT
  have h2 := sup_rootGroup_eq_of_mem h hc hs hv he cole.1 cole.2.1 cole.2.2 (left_mem_line hv) hte
    (hD.ne_one hv) (hD.ne_one ht) htT
  apply heL
  rw [← h1, h2]
  exact right_mem_line he

theorem conj_mem_other_line (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) {v u e g : G} (hv : v ∈ D) (hu : u ∈ D) (he : e ∈ D)
    (colu : Commute v u ∧ v * u ∈ D ∧ u ∉ rootSet D v)
    (cole : Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v) (heL : e ∉ rootGroup D v ⊔ rootGroup D u)
    (hgv : g * v * g⁻¹ ∈ rootSet D v) (hgu : g * u * g⁻¹ ∈ rootSet D u) {w : G}
    (hw : w ∈ rootGroup D v ⊔ rootGroup D e) : g * w * g⁻¹ ∈ rootGroup D v ⊔ rootGroup D e := by
  have hclass := h.isClass
  have hD := h.root
  have := h.finite
  have he'D : g * e * g⁻¹ ∈ D := conj_mem_of_isClass hclass g he
  have hTv : rootSet D (g * v * g⁻¹) = rootSet D v := rootSet_eq_of_mem hgv
  have he'T : g * e * g⁻¹ ∉ rootSet D v := by
    rw [← hTv, rootSet_conj hclass]
    rintro ⟨y, hy, hye⟩
    have : y = e := by
      have := congrArg (fun z => g⁻¹ * z * g) hye
      simpa [mul_assoc] using this
    exact cole.2.2 (this ▸ hy)
  have hmul' : g * e * g⁻¹ * (g * v * g⁻¹) ∈ D := by
    have := conj_mem_of_isClass hclass g cole.2.1
    rwa [show g * (v * e) * g⁻¹ = g * e * g⁻¹ * (g * v * g⁻¹) by
      rw [show v * e = e * v from cole.1.eq]; group] at this
  obtain ⟨hcomm, hmul⟩ := collinear_of_collinear_mem_rootSet h hc hs hv hgv he'D
    ((Commute.conj_iff g).2 cole.1).symm hmul' he'T
  have hginv : ∀ x ∈ D, g * x * g⁻¹ ∈ rootSet D x → g⁻¹ * x * g⁻¹⁻¹ ∈ rootSet D x :=
    fun x hx hgx =>
    (conj_mem_rootSet_iff_mem_normalizer h hc hx).2
      (Subgroup.inv_mem _ ((conj_mem_rootSet_iff_mem_normalizer h hc hx).1 hgx))
  have he'L : g * e * g⁻¹ ∈ rootGroup D v ⊔ rootGroup D e := by
    rcases mem_line_or_mem_line_of_not_threeLines h3 hv hu he he'D colu cole ⟨hcomm, hmul, he'T⟩
        heL with h' | h'
    · exfalso
      have := conj_mem_sup_of_conj_mem_rootSet hclass (hginv v hv hgv) (hginv u hu hgu) h'
      apply heL
      simpa [mul_assoc] using this
    · exact h'
  have hLeq := sup_rootGroup_eq_of_mem h hc hs hv he cole.1 cole.2.1 cole.2.2 (left_mem_line hv)
    he'L (hD.ne_one hv) (hD.ne_one he'D) he'T
  have hmap : (rootGroup D v ⊔ rootGroup D e).map (MulAut.conj g).toMonoidHom =
      rootGroup D v ⊔ rootGroup D (g * e * g⁻¹) := by
    rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass,
      rootGroup_eq_of_mem hgv]
  have : g * w * g⁻¹ ∈ (rootGroup D v ⊔ rootGroup D e).map (MulAut.conj g).toMonoidHom :=
    ⟨w, hw, rfl⟩
  rwa [hmap, hLeq] at this

structure TorusPath (D : Set G) (g : G) (p : ℤ → G) : Prop where
  mem : ∀ i, p i ∈ D
  comm : ∀ i, Commute (p i) (p (i + 1))
  mul_mem : ∀ i, p i * p (i + 1) ∈ D
  not_mem : ∀ i, p (i + 1) ∉ rootSet D (p i)
  turn : ∀ i, p (i + 1) ∉ rootGroup D (p (i - 1)) ⊔ rootGroup D (p i)
  fix : ∀ i, g * p i * g⁻¹ ∈ rootSet D (p i)

namespace TorusPath

variable {g : G} {p : ℤ → G}

theorem comm_sub (hP : TorusPath D g p) (i : ℤ) : Commute (p (i - 1)) (p i) := by
  have := hP.comm (i - 1)
  rwa [sub_add_cancel] at this

theorem mul_mem_sub (hP : TorusPath D g p) (i : ℤ) : p i * p (i - 1) ∈ D := by
  have := hP.mul_mem (i - 1)
  rwa [sub_add_cancel, (hP.comm_sub i).eq] at this

theorem not_mem_sub (hP : TorusPath D g p) (i : ℤ) : p (i - 1) ∉ rootSet D (p i) := by
  intro h'
  have := hP.not_mem (i - 1)
  rw [sub_add_cancel] at this
  exact this (mem_rootSet_comm (hP.mem _) h')

theorem turn_sub (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hP : TorusPath D g p) (i : ℤ) :
    p (i - 1) ∉ rootGroup D (p (i + 1)) ⊔ rootGroup D (p i) := by
  refine not_mem_sup_of_not_mem_sup h hc hs (hP.mem _) (hP.mem _) (hP.mem _) ?_
    (hP.comm i) (hP.mul_mem i) (hP.not_mem i) (hP.turn i)
  intro h'
  exact hP.not_mem_sub i (mem_rootSet_comm (hP.mem _) h')

theorem conj_mem_line (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hP : TorusPath D g p) (i : ℤ)
    {u : G} (hu : u ∈ rootGroup D (p i) ⊔ rootGroup D (p (i + 1))) :
    g * u * g⁻¹ ∈ rootGroup D (p i) ⊔ rootGroup D (p (i + 1)) :=
  conj_mem_sup_of_conj_mem_rootSet hclass (hP.fix i) (hP.fix (i + 1)) hu

theorem conj_mem_line_sub (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hP : TorusPath D g p)
    (i : ℤ) {u : G} (hu : u ∈ rootGroup D (p i) ⊔ rootGroup D (p (i - 1))) :
    g * u * g⁻¹ ∈ rootGroup D (p i) ⊔ rootGroup D (p (i - 1)) :=
  conj_mem_sup_of_conj_mem_rootSet hclass (hP.fix i) (hP.fix (i - 1)) hu

theorem shift (hP : TorusPath D g p) (c : ℤ) : TorusPath D g (fun i => p (i + c)) where
  mem i := hP.mem _
  comm i := by
    have := hP.comm (i + c)
    rwa [show i + c + 1 = i + 1 + c by ring] at this
  mul_mem i := by
    have := hP.mul_mem (i + c)
    rwa [show i + c + 1 = i + 1 + c by ring] at this
  not_mem i := by
    have := hP.not_mem (i + c)
    rwa [show i + c + 1 = i + 1 + c by ring] at this
  turn i := by
    have := hP.turn (i + c)
    rwa [show i + c + 1 = i + 1 + c by ring, show i + c - 1 = i - 1 + c by ring] at this
  fix i := hP.fix _

theorem reverse (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hP : TorusPath D g p) (c : ℤ) : TorusPath D g (fun i => p (c - i)) where
  mem i := hP.mem _
  comm i := by
    have := hP.comm_sub (c - i)
    rw [show c - i - 1 = c - (i + 1) by ring] at this
    exact this.symm
  mul_mem i := by
    have := hP.mul_mem_sub (c - i)
    rwa [show c - i - 1 = c - (i + 1) by ring] at this
  not_mem i := by
    have := hP.not_mem_sub (c - i)
    rwa [show c - i - 1 = c - (i + 1) by ring] at this
  turn i := by
    have := hP.turn_sub h hc hs (c - i)
    rwa [show c - i - 1 = c - (i + 1) by ring, show c - i + 1 = c - (i - 1) by ring] at this
  fix i := hP.fix _

theorem of_fix {g' : G} (hP : TorusPath D g p)
    (hfix : ∀ d ∈ D, g * d * g⁻¹ ∈ rootSet D d → g' * d * g'⁻¹ ∈ rootSet D d) :
    TorusPath D g' p where
  mem := hP.mem
  comm := hP.comm
  mul_mem := hP.mul_mem
  not_mem := hP.not_mem
  turn := hP.turn
  fix i := hfix _ (hP.mem i) (hP.fix i)

theorem conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hP : TorusPath D g p) (k : G) :
    TorusPath D (k * g * k⁻¹) (fun i => k * p i * k⁻¹) where
  mem i := conj_mem_of_isClass hclass k (hP.mem i)
  comm i := (Commute.conj_iff k).2 (hP.comm i)
  mul_mem i := by
    have := conj_mem_of_isClass hclass k (hP.mul_mem i)
    rwa [show k * (p i * p (i + 1)) * k⁻¹ = k * p i * k⁻¹ * (k * p (i + 1) * k⁻¹) by group]
      at this
  not_mem i := by
    rw [rootSet_conj hclass]
    rintro ⟨x, hx, hxe⟩
    have : x = p (i + 1) := by
      have := congrArg (fun w => k⁻¹ * w * k) hxe
      simpa [mul_assoc] using this
    exact hP.not_mem i (this ▸ hx)
  turn i := by
    rw [rootGroup_conj hclass, rootGroup_conj hclass, ← Subgroup.map_sup]
    rintro ⟨x, hx, hxe⟩
    have : x = p (i + 1) := by
      have := congrArg (fun w => k⁻¹ * w * k) hxe
      simpa [mul_assoc] using this
    exact hP.turn i (this ▸ hx)
  fix i := by
    rw [rootSet_conj hclass]
    exact ⟨g * p i * g⁻¹, hP.fix i, by group⟩

theorem step_fwd (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hg : InvTorus D g) {q : ℤ → G}
    (hP : TorusPath D g p) (hQ : TorusPath D g q) {i : ℤ}
    (h0 : q (i - 1) ∈ rootSet D (p (i - 1))) (h1 : q i ∈ rootSet D (p i)) :
    q (i + 1) ∈ rootSet D (p (i + 1)) := by
  have hclass := h.isClass
  have hpi := hP.mem i
  have hTi : rootSet D (q i) = rootSet D (p i) := rootSet_eq_of_mem h1
  have hqT : q (i + 1) ∉ rootSet D (p i) := by
    rw [← hTi]
    exact hQ.not_mem i
  obtain ⟨hcomm, hmul⟩ := collinear_of_collinear_mem_rootSet h hc hs hpi h1 (hQ.mem (i + 1))
    (hQ.comm i).symm (by rw [← (hQ.comm i).eq]; exact hQ.mul_mem i) hqT
  have hA0 : rootGroup D (q (i - 1)) = rootGroup D (p (i - 1)) := rootGroup_eq_of_mem h0
  have hA1 : rootGroup D (q i) = rootGroup D (p i) := rootGroup_eq_of_mem h1
  have hqL : q (i + 1) ∉ rootGroup D (p (i - 1)) ⊔ rootGroup D (p i) := by
    rw [← hA0, ← hA1]
    exact hQ.turn i
  have hsub := hP.turn_sub h hc hs i
  rw [sup_comm] at hsub
  have hqL' : q (i + 1) ∈ rootGroup D (p i) ⊔ rootGroup D (p (i + 1)) := by
    rcases mem_line_or_mem_line_of_not_threeLines h3 hpi (hP.mem (i + 1)) (hP.mem (i - 1))
        (hQ.mem (i + 1)) ⟨hP.comm i, hP.mul_mem i, hP.not_mem i⟩
        ⟨(hP.comm_sub i).symm, hP.mul_mem_sub i, hP.not_mem_sub i⟩ ⟨hcomm, hmul, hqT⟩ hsub
      with h' | h'
    · exact h'
    · rw [sup_comm] at h'
      exact absurd h' hqL
  exact (hF hpi (hP.mem (i + 1)) (hP.comm i) (hP.mul_mem i) (hP.not_mem i) (hP.mem (i - 1))
    (hP.comm_sub i).symm (hP.mul_mem_sub i) hsub hg (hP.fix i)
    (fun u hu => hP.conj_mem_line hclass i hu)
    (fun u hu => hP.conj_mem_line_sub hclass i hu)).2 _ (hP.mem (i + 1))
    (right_mem_line (hP.mem (i + 1))) (hP.not_mem i) (hP.fix (i + 1)) _ (hQ.mem (i + 1)) hqL'
    hqT (hQ.fix (i + 1))

theorem step_bwd (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hg : InvTorus D g) {q : ℤ → G}
    (hP : TorusPath D g p) (hQ : TorusPath D g q) {i : ℤ}
    (h0 : q (i + 1) ∈ rootSet D (p (i + 1))) (h1 : q i ∈ rootSet D (p i)) :
    q (i - 1) ∈ rootSet D (p (i - 1)) := by
  have e0 : (0 : ℤ) - (-i - 1) = i + 1 := by ring
  have e1 : (0 : ℤ) - -i = i := by ring
  have e2 : (0 : ℤ) - (-i + 1) = i - 1 := by ring
  have h0' : q (0 - (-i - 1)) ∈ rootSet D (p (0 - (-i - 1))) := by rwa [e0]
  have h1' : q (0 - -i) ∈ rootSet D (p (0 - -i)) := by rwa [e1]
  have := step_fwd h hc hs h3 hF hg (hP.reverse h hc hs 0) (hQ.reverse h hc hs 0) (i := -i)
    h0' h1'
  rwa [e2] at this

theorem rootSet_of_rootSet (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) (hg : InvTorus D g) {q : ℤ → G}
    (hP : TorusPath D g p) (hQ : TorusPath D g q) {k : ℤ} (h0 : q k ∈ rootSet D (p k))
    (h1 : q (k + 1) ∈ rootSet D (p (k + 1))) (i : ℤ) : q i ∈ rootSet D (p i) := by
  have hfwd : ∀ n : ℕ, q (k + n) ∈ rootSet D (p (k + n)) ∧
      q (k + n + 1) ∈ rootSet D (p (k + n + 1)) := by
    intro n
    induction n with
    | zero => simpa using ⟨h0, h1⟩
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc]
      refine ⟨ih.2, ?_⟩
      exact step_fwd h hc hs h3 hF hg hP hQ (i := k + n + 1)
        (by rw [add_sub_cancel_right]; exact ih.1) ih.2
  have hbwd : ∀ n : ℕ, q (k - n) ∈ rootSet D (p (k - n)) ∧
      q (k - n + 1) ∈ rootSet D (p (k - n + 1)) := by
    intro n
    induction n with
    | zero => simpa using ⟨h0, h1⟩
    | succ n ih =>
      rw [Nat.cast_succ, show k - (n + 1 : ℤ) + 1 = k - n by ring]
      refine ⟨?_, ih.1⟩
      have := step_bwd h hc hs h3 hF hg hP hQ (i := k - n) ih.2 ih.1
      rwa [show k - (n : ℤ) - 1 = k - (n + 1) by ring] at this
  rcases le_or_gt k i with hki | hki
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = k + n := ⟨(i - k).toNat, by omega⟩
    exact (hfwd n).1
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = k - n := ⟨(k - i).toNat, by omega⟩
    exact (hbwd n).1

end TorusPath

structure FwdPath (D : Set G) (g : G) (f : ℕ → G) : Prop where
  mem : ∀ n, f n ∈ D
  comm : ∀ n, Commute (f n) (f (n + 1))
  mul_mem : ∀ n, f n * f (n + 1) ∈ D
  not_mem : ∀ n, f (n + 1) ∉ rootSet D (f n)
  turn : ∀ n, f (n + 2) ∉ rootGroup D (f n) ⊔ rootGroup D (f (n + 1))
  fix : ∀ n, g * f n * g⁻¹ ∈ rootSet D (f n)

@[expose] def NextPt (D : Set G) (g u v w : G) : Prop :=
  w ∈ D ∧ Commute v w ∧ v * w ∈ D ∧ w ∉ rootSet D v ∧ w ∉ rootGroup D u ⊔ rootGroup D v ∧
    g * w * g⁻¹ ∈ rootSet D w

open Classical in
noncomputable def nextPt (D : Set G) (g u v : G) : G :=
  if h : ∃ w, NextPt D g u v w then h.choose else v

theorem nextPt_spec {g u v : G} (h : ∃ w, NextPt D g u v w) :
    NextPt D g u v (nextPt D g u v) := by
  classical
  unfold nextPt
  split_ifs
  exact h.choose_spec

noncomputable def fwdPair (D : Set G) (g u v : G) : ℕ → G × G
  | 0 => (u, v)
  | n + 1 => ((fwdPair D g u v n).2, nextPt D g (fwdPair D g u v n).1 (fwdPair D g u v n).2)

theorem exists_other_line (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) {b c₁ c₂ : G} (hb : b ∈ D) (hc₁ : c₁ ∈ D) (hc₂ : c₂ ∈ D)
    (col₁ : Commute b c₁ ∧ b * c₁ ∈ D ∧ c₁ ∉ rootSet D b)
    (col₂ : Commute b c₂ ∧ b * c₂ ∈ D ∧ c₂ ∉ rootSet D b)
    (h21 : c₂ ∉ rootGroup D b ⊔ rootGroup D c₁) {v u : G} (hv : v ∈ D) (hu : u ∈ D)
    (hvu : Commute v u) (hvuD : v * u ∈ D) (huT : u ∉ rootSet D v) :
    ∃ e ∈ D, Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v ∧ e ∉ rootGroup D v ⊔ rootGroup D u := by
  have hclass := h.isClass
  have hD := h.root
  obtain ⟨k, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass hb hv)
  have hcol : ∀ {c : G}, c ∈ D → (Commute b c ∧ b * c ∈ D ∧ c ∉ rootSet D b) →
      Commute (k * b * k⁻¹) (k * c * k⁻¹) ∧ k * b * k⁻¹ * (k * c * k⁻¹) ∈ D ∧
        k * c * k⁻¹ ∉ rootSet D (k * b * k⁻¹) := by
    intro c hcD col
    refine ⟨(Commute.conj_iff k).2 col.1, ?_, ?_⟩
    · have := conj_mem_of_isClass hclass k col.2.1
      rwa [show k * (b * c) * k⁻¹ = k * b * k⁻¹ * (k * c * k⁻¹) by group] at this
    · rw [rootSet_conj hclass]
      rintro ⟨y, hy, hye⟩
      have : y = c := by
        have := congrArg (fun z => k⁻¹ * z * k) hye
        simpa [mul_assoc] using this
      exact col.2.2 (this ▸ hy)
  have hmapL : ∀ c : G, (rootGroup D b ⊔ rootGroup D c).map (MulAut.conj k).toMonoidHom =
      rootGroup D (k * b * k⁻¹) ⊔ rootGroup D (k * c * k⁻¹) := fun c => by
    rw [Subgroup.map_sup, ← rootGroup_conj hclass, ← rootGroup_conj hclass]
  have hnot : ∀ {c c' : G}, c' ∉ rootGroup D b ⊔ rootGroup D c →
      k * c' * k⁻¹ ∉ rootGroup D (k * b * k⁻¹) ⊔ rootGroup D (k * c * k⁻¹) := by
    intro c c' hc' h'
    rw [← hmapL] at h'
    obtain ⟨y, hy, hye⟩ := h'
    have : y = c' := by
      have := congrArg (fun z => k⁻¹ * z * k) hye
      simpa [mul_assoc] using this
    exact hc' (this ▸ hy)
  have hc₁' := conj_mem_of_isClass hclass k hc₁
  have hc₂' := conj_mem_of_isClass hclass k hc₂
  have col₁' := hcol hc₁ col₁
  have col₂' := hcol hc₂ col₂
  have h21' := hnot h21
  rcases mem_line_or_mem_line_of_not_threeLines h3 hv hc₁' hc₂' hu col₁' col₂' ⟨hvu, hvuD, huT⟩
      h21' with h' | h'
  · refine ⟨_, hc₂', col₂'.1, col₂'.2.1, col₂'.2.2, ?_⟩
    rw [sup_rootGroup_eq_of_mem h hc hs hv hc₁' col₁'.1 col₁'.2.1 col₁'.2.2 (left_mem_line hv) h'
      (hD.ne_one hv) (hD.ne_one hu) huT]
    exact h21'
  · refine ⟨_, hc₁', col₁'.1, col₁'.2.1, col₁'.2.2, ?_⟩
    have h12 := not_mem_line_symm h hc hs hv hc₁' hc₂' col₂'.1 col₂'.2.1 col₂'.2.2 col₁'.2.2 h21'
    rwa [sup_rootGroup_eq_of_mem h hc hs hv hc₂' col₂'.1 col₂'.2.1 col₂'.2.2 (left_mem_line hv) h'
      (hD.ne_one hv) (hD.ne_one hu) huT]

theorem exists_nextPt (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) {g : G} (hg : InvTorus D g)
    (hTwo : ∀ v ∈ D, ∀ u ∈ D, Commute v u → v * u ∈ D → u ∉ rootSet D v →
      ∃ e ∈ D, Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v ∧ e ∉ rootGroup D v ⊔ rootGroup D u)
    {u v : G} (hu : u ∈ D) (hv : v ∈ D) (hvu : Commute v u) (hvuD : v * u ∈ D)
    (huT : u ∉ rootSet D v) (hgu : g * u * g⁻¹ ∈ rootSet D u)
    (hgv : g * v * g⁻¹ ∈ rootSet D v) : ∃ w, NextPt D g u v w := by
  have hclass := h.isClass
  have hD := h.root
  obtain ⟨e, he, hve, hveD, heT, heL⟩ := hTwo v hv u hu hvu hvuD huT
  have huL : u ∉ rootGroup D v ⊔ rootGroup D e :=
    not_mem_line_symm h hc hs hv hu he hve hveD heT huT heL
  obtain ⟨⟨t, htD, htL, htT, htfix⟩, -⟩ := hF hv he hve hveD heT hu hvu hvuD huL hg hgv
    (fun w hw => conj_mem_other_line h hc hs h3 hv hu he ⟨hvu, hvuD, huT⟩ ⟨hve, hveD, heT⟩ heL
      hgv hgu hw)
    (fun w hw => conj_mem_sup_of_conj_mem_rootSet hclass hgv hgu hw)
  refine ⟨t, htD, commute_of_mem_sup_rootGroup hv he hve (left_mem_line hv) htL, ?_, htT, ?_,
    htfix⟩
  · refine mem_of_mem_sup_rootGroup h hc hs hv he hve hveD heT
      (Subgroup.mul_mem _ (left_mem_line hv) htL) fun h1 => htT ?_
    rw [(eq_inv_of_mul_eq_one_right h1).trans (hD.inv_eq hv)]
    exact mem_rootSet_self hv
  · intro htu
    rw [sup_comm] at htu
    exact htT (mem_rootSet_of_mem_two_lines h hc hs hv hu he ⟨hvu, hvuD, huT⟩
      ⟨hve, hveD, heT⟩ heL htD htu htL)

theorem fwdPath_fwdPair (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) {g : G} (hg : InvTorus D g)
    (hTwo : ∀ v ∈ D, ∀ u ∈ D, Commute v u → v * u ∈ D → u ∉ rootSet D v →
      ∃ e ∈ D, Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v ∧ e ∉ rootGroup D v ⊔ rootGroup D u)
    {u v : G} (hu : u ∈ D) (hv : v ∈ D) (huv : Commute u v) (huvD : u * v ∈ D)
    (hvT : v ∉ rootSet D u) (hgu : g * u * g⁻¹ ∈ rootSet D u)
    (hgv : g * v * g⁻¹ ∈ rootSet D v) : FwdPath D g (fun n => (fwdPair D g u v n).1) := by
  have hD := h.root
  have key : ∀ n, (fwdPair D g u v n).1 ∈ D ∧ (fwdPair D g u v n).2 ∈ D ∧
      Commute (fwdPair D g u v n).1 (fwdPair D g u v n).2 ∧
      (fwdPair D g u v n).1 * (fwdPair D g u v n).2 ∈ D ∧
      (fwdPair D g u v n).2 ∉ rootSet D (fwdPair D g u v n).1 ∧
      g * (fwdPair D g u v n).1 * g⁻¹ ∈ rootSet D (fwdPair D g u v n).1 ∧
      g * (fwdPair D g u v n).2 * g⁻¹ ∈ rootSet D (fwdPair D g u v n).2 := by
    intro n
    induction n with
    | zero => exact ⟨hu, hv, huv, huvD, hvT, hgu, hgv⟩
    | succ n ih =>
      obtain ⟨ha, hb, hab, habD, hbT, hga, hgb⟩ := ih
      have hspec := nextPt_spec (exists_nextPt h hc hs h3 hF hg hTwo ha hb hab.symm
        (by rw [← hab.eq]; exact habD) (fun h' => hbT (mem_rootSet_comm hb h')) hga hgb)
      obtain ⟨hwD, hbw, hbwD, hwT, -, hgw⟩ := hspec
      exact ⟨hb, hwD, hbw, hbwD, hwT, hgb, hgw⟩
  refine ⟨fun n => (key n).1, fun n => (key n).2.2.1, fun n => (key n).2.2.2.1,
    fun n => (key n).2.2.2.2.1, fun n => ?_, fun n => (key n).2.2.2.2.2.1⟩
  obtain ⟨ha, hb, hab, habD, hbT, hga, hgb⟩ := key n
  exact (nextPt_spec (exists_nextPt h hc hs h3 hF hg hTwo ha hb hab.symm
    (by rw [← hab.eq]; exact habD) (fun h' => hbT (mem_rootSet_comm hb h')) hga hgb)).2.2.2.2.1

theorem FwdPath.torusPath_glue (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    {g : G} {f f' : ℕ → G} (hf : FwdPath D g f) (hf' : FwdPath D g f') (h0 : f 0 = f' 1)
    (h1 : f 1 = f' 0) :
    TorusPath D g (fun i => if 0 < i then f i.toNat else f' (1 - i).toNat) := by
  set P : ℤ → G := fun i => if 0 < i then f i.toNat else f' (1 - i).toNat with hP
  have hnat : ∀ n : ℕ, P n = f n := by
    intro n
    rcases n with _ | m
    · simp [hP, h0]
    · simp [hP]
  have hneg : ∀ n : ℕ, P (-(n : ℤ)) = f' (n + 1) := by
    intro n
    have : ¬ (0 : ℤ) < -(n : ℤ) := by omega
    have e : (1 - -(n : ℤ)).toNat = n + 1 := by omega
    simp only [hP, this, e, ↓reduceIte]
  have hneg1 : ∀ n : ℕ, P (-(n : ℤ) + 1) = f' n := by
    intro n
    rcases n with _ | m
    · simpa using (hnat 1).trans h1
    · have := hneg m
      rwa [show -((m + 1 : ℕ) : ℤ) + 1 = -(m : ℤ) by push_cast; ring]
  have hsplit : ∀ i : ℤ, (∃ n : ℕ, i = n + 1) ∨ ∃ n : ℕ, i = -(n : ℤ) := by
    intro i
    rcases lt_or_ge 0 i with hi | hi
    · exact Or.inl ⟨(i - 1).toNat, by omega⟩
    · exact Or.inr ⟨(-i).toNat, by omega⟩
  have hpos : ∀ n : ℕ, P ((n : ℤ) + 1) = f (n + 1) := fun n => by
    have := hnat (n + 1)
    push_cast at this
    exact this
  have hpos2 : ∀ n : ℕ, P ((n : ℤ) + 1 + 1) = f (n + 2) := fun n => by
    have := hnat (n + 2)
    push_cast at this
    rwa [show (n : ℤ) + 2 = n + 1 + 1 by ring] at this
  have hneg2 : ∀ n : ℕ, P (-(n : ℤ) - 1) = f' (n + 2) := fun n => by
    have := hneg (n + 1)
    push_cast at this
    rwa [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring] at this
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  ·
    rcases hsplit i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [hpos]; exact hf.mem _
    · rw [hneg]; exact hf'.mem _
  ·
    rcases hsplit i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [hpos, hpos2]; exact hf.comm _
    · rw [hneg, hneg1]; exact (hf'.comm n).symm
  ·
    rcases hsplit i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [hpos, hpos2]; exact hf.mul_mem _
    · rw [hneg, hneg1, ← (hf'.comm n).eq]; exact hf'.mul_mem n
  ·
    rcases hsplit i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [hpos, hpos2]; exact hf.not_mem _
    · rw [hneg, hneg1]
      exact fun h' => hf'.not_mem n (mem_rootSet_comm (hf'.mem _) h')
  ·
    rcases hsplit i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [hpos2, add_sub_cancel_right, hnat, hpos]
      exact hf.turn n
    · rw [hneg1, hneg2, hneg]
      exact not_mem_sup_of_not_mem_sup h hc hs (hf'.mem n) (hf'.mem (n + 1)) (hf'.mem (n + 2))
        (hf'.not_mem n) (hf'.comm (n + 1)) (hf'.mul_mem (n + 1)) (hf'.not_mem (n + 1))
        (hf'.turn n)
  ·
    rcases hsplit i with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · rw [hpos]; exact hf.fix _
    · rw [hneg]; exact hf'.fix _

theorem exists_torusPath (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (h3 : ¬ ThreeLines D) (hF : FixUnique D) {g : G} (hg : InvTorus D g)
    (hTwo : ∀ v ∈ D, ∀ u ∈ D, Commute v u → v * u ∈ D → u ∉ rootSet D v →
      ∃ e ∈ D, Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v ∧ e ∉ rootGroup D v ⊔ rootGroup D u)
    {u v : G} (hu : u ∈ D) (hv : v ∈ D) (huv : Commute u v) (huvD : u * v ∈ D)
    (hvT : v ∉ rootSet D u) (hgu : g * u * g⁻¹ ∈ rootSet D u)
    (hgv : g * v * g⁻¹ ∈ rootSet D v) : ∃ p : ℤ → G, TorusPath D g p ∧ p 0 = u ∧ p 1 = v := by
  have hf := fwdPath_fwdPair h hc hs h3 hF hg hTwo hu hv huv huvD hvT hgu hgv
  have hf' := fwdPath_fwdPair h hc hs h3 hF hg hTwo hv hu huv.symm
    (by rw [← huv.eq]; exact huvD) (fun h' => hvT (mem_rootSet_comm hv h')) hgv hgu
  refine ⟨_, hf.torusPath_glue h hc hs hf' rfl rfl, ?_, ?_⟩
  · simp [fwdPair]
  · simp [fwdPair]

end CFSG.Timmesfeld.Bridge
