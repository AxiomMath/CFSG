module

public import CFSG.OddTranspositions.SixEight
public import CFSG.OddTranspositions.SecondKindCoset

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def Gamma (hC : HypothesisC D) : Set G := AalphaStar D hC.alpha

@[expose] def cenGen (hC : HypothesisC D) : Subgroup G :=
  Subgroup.closure ((D : Set G) ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G))

@[expose] def cenOrbit (hC : HypothesisC D) (a : G) : Set G :=
  {b | ∃ x ∈ cenGen hC, b = x * a * x⁻¹}

@[expose] def GammaComm (hC : HypothesisC D) (a b : G) : Prop :=
  a ∈ Gamma hC ∧ b ∈ Gamma hC ∧ Commute a b

@[expose] def GammaReach (hC : HypothesisC D) (a b : G) : Prop :=
  Relation.ReflTransGen (GammaComm hC) a b

@[expose] def GammaComp (hC : HypothesisC D) (a : G) : Set G := {b | GammaReach hC a b}

theorem mem_Gamma_iff {hC : HypothesisC D} {a : G} :
    a ∈ Gamma hC ↔ a ∈ D ∧ ¬ Commute a hC.d ∧ a ∉ hC.alpha := by
  rw [Gamma, hC.AalphaStar_eq_diff_alpha]
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, and_assoc]

theorem Gamma_subset_D {hC : HypothesisC D} : Gamma hC ⊆ D := by
  intro a ha
  exact (mem_Gamma_iff.mp ha).1

theorem not_commute_d_of_mem_Gamma {hC : HypothesisC D} {a : G} (ha : a ∈ Gamma hC) :
    ¬ Commute a hC.d :=
  (mem_Gamma_iff.mp ha).2.1

theorem not_mem_alpha_of_mem_Gamma {hC : HypothesisC D} {a : G} (ha : a ∈ Gamma hC) :
    a ∉ hC.alpha :=
  (mem_Gamma_iff.mp ha).2.2

theorem disjoint_Gamma_alpha (hC : HypothesisC D) : Disjoint (Gamma hC) hC.alpha :=
  (disjoint_alpha_AalphaStar hC.isBlock_alpha).symm

theorem disjoint_Gamma_DalphaStar (hC : HypothesisC D) :
    Disjoint (Gamma hC) (DalphaStar D hC.alpha) := by
  rw [Set.disjoint_left]
  intro a ha hb
  obtain ⟨β, hβ, haβ⟩ := mem_AalphaStar_iff.mp ha
  obtain ⟨γ, hγ, haγ⟩ := mem_DalphaStar_iff.mp hb
  have hβclass : β ∈ blockClass hC.alpha := (mem_Aalpha_iff.mp hβ).1
  have hγclass : γ ∈ blockClass hC.alpha := (mem_Dalpha_iff.mp hγ).1
  have hβγ : β = γ :=
    eq_of_mem_of_mem_blockClass hC.isBlock_alpha hβclass hγclass ⟨a, haβ, haγ⟩
  have hβperp : β ∉ perp D hC.alpha := (mem_Aalpha_iff.mp hβ).2
  exact hβperp (hβγ ▸ mem_perp_iff.mpr (Or.inl hγ))

theorem d_mem_cenGen (hC : HypothesisC D) : hC.d ∈ cenGen hC := by
  refine Subgroup.subset_closure ⟨hC.hd, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem cenGen_le_centralizer (hC : HypothesisC D) :
    cenGen hC ≤ Subgroup.centralizer ({hC.d} : Set G) := by
  rw [cenGen, Subgroup.closure_le]
  exact Set.inter_subset_right

theorem cenGen_le_normalizer_alpha (hC : HypothesisC D) :
    cenGen hC ≤ Subgroup.normalizer hC.alpha := by
  rw [cenGen, Subgroup.closure_le]
  rintro x ⟨-, hxc⟩
  have hxd : Commute x hC.d := Subgroup.mem_centralizer_singleton_iff.mp hxc
  have himg : (fun y => x * y * x⁻¹) '' hC.alpha = hC.alpha := by
    have hfix : x * hC.d * x⁻¹ = hC.d := by rw [hxd.eq, mul_inv_cancel_right]
    have hmem : hC.d ∈ (fun y => x * y * x⁻¹) '' hC.alpha :=
      ⟨hC.d, hC.d_mem_alpha, hfix⟩
    exact eq_of_mem_of_mem_blockClass hC.isBlock_alpha
      (mem_blockClass_iff.mpr ⟨x, rfl⟩) (mem_blockClass_self hC.alpha)
      ⟨hC.d, hmem, hC.d_mem_alpha⟩
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mpr himg

theorem DalphaStar_subset_cenGen (hC : HypothesisC D) :
    hC.E ⊆ (cenGen hC : Set G) := by
  intro e he
  have he' : e ∈ DalphaStar D hC.alpha := by rwa [hC.DalphaStar_alpha]
  have hcomm := hC.DalphaStar_subset_commute he'
  refine Subgroup.subset_closure ⟨hcomm.1, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.2

theorem cenGen_maps_Gamma (hC : HypothesisC D) {x a : G} (hx : x ∈ cenGen hC)
    (ha : a ∈ Gamma hC) : x * a * x⁻¹ ∈ Gamma hC := by
  obtain ⟨haD, hanc, haα⟩ := mem_Gamma_iff.mp ha
  have hxc : Commute x hC.d :=
    Subgroup.mem_centralizer_singleton_iff.mp (cenGen_le_centralizer hC hx)
  have hxn : x ∈ Subgroup.normalizer hC.alpha := cenGen_le_normalizer_alpha hC hx
  have hxα : (fun y => x * y * x⁻¹) '' hC.alpha = hC.alpha :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp hxn
  refine mem_Gamma_iff.mpr ⟨hC.setup.normal x a haD, ?_, ?_⟩
  · intro hconj
    apply hanc
    have h2 : Commute (x⁻¹ * (x * a * x⁻¹) * x) (x⁻¹ * hC.d * x) := by
      simpa using hconj.conj x⁻¹
    have e1 : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    have e2 : x⁻¹ * hC.d * x = hC.d := by rw [hxc.inv_left.eq]; group
    rwa [e1, e2] at h2
  · intro hmem
    exact haα ((Subgroup.mem_set_normalizer_iff.mp hxn a).mpr hmem)

theorem cenOrbit_subset_Gamma (hC : HypothesisC D) {a : G} (ha : a ∈ Gamma hC) :
    cenOrbit hC a ⊆ Gamma hC := by
  rintro b ⟨x, hx, rfl⟩
  exact cenGen_maps_Gamma hC hx ha

theorem self_mem_cenOrbit (hC : HypothesisC D) (a : G) : a ∈ cenOrbit hC a :=
  ⟨1, Subgroup.one_mem _, by group⟩

theorem cenOrbit_invariant (hC : HypothesisC D) {a x : G} (hx : x ∈ cenGen hC) :
    ∀ b ∈ cenOrbit hC a, x * b * x⁻¹ ∈ cenOrbit hC a := by
  rintro b ⟨y, hy, rfl⟩
  exact ⟨x * y, (cenGen hC).mul_mem hx hy, by group⟩

theorem eq_top_of_mem_Gamma (hC : HypothesisC D) {Y : Subgroup G}
    (hY : Y = Subgroup.closure ((Y : Set G) ∩ D))
    (hdY : hC.d ∈ Y) (hEY : hC.E ⊆ (Y : Set G))
    {a : G} (haΓ : a ∈ Gamma hC) (haY : a ∈ Y) : Y = ⊤ := by
  by_contra hproper
  have hsub := inter_D_subset_perp hC hY hdY hEY hproper
  have haD : a ∈ D := Gamma_subset_D haΓ
  rcases hsub ⟨haY, haD⟩ with haα | haE
  · exact (Set.disjoint_left.mp (disjoint_Gamma_alpha hC) haΓ) haα
  · exact (Set.disjoint_left.mp (disjoint_Gamma_DalphaStar hC) haΓ) haE

theorem isTriangle_of_mem_Gamma (hC : HypothesisC D) {a b : G}
    (ha : a ∈ Gamma hC) (hb : b ∈ Gamma hC) (hne : a ≠ b) (hcomm : Commute a b) :
    IsTriangle D a hC.d b :=
  ⟨Gamma_subset_D ha, Gamma_subset_D hb, hC.hd, hne, hcomm,
    not_commute_d_of_mem_Gamma ha, not_commute_d_of_mem_Gamma hb⟩

theorem step1_secondKind (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a b : G} (ha : a ∈ Gamma hC) (hb : b ∈ Gamma hC) (hne : a ≠ b) (hcomm : Commute a b) :
    ∃ x ∈ ⁅conjClosure (Subgroup.closure ({a, hC.d} : Set G)) (a * b),
        Subgroup.zpowers hC.d⁆, x * a * x⁻¹ = b ∧ Commute x hC.d := by
  classical
  have htri : IsTriangle D a hC.d b := isTriangle_of_mem_Gamma hC ha hb hne hcomm
  have h4 : orderOf (a * b * hC.d) = 4 := hsecond a hC.d b htri
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({a, hC.d} : Set G) → IsTriangle D a x b →
      ¬ IsThirdKind a x b := by
    intro x _ _ hx hthird
    have h4' : orderOf (a * b * x) = 4 := hsecond a x b hx
    obtain ⟨n, hnodd, _hn1, hord⟩ := hthird
    have hn2 : n = 2 := by omega
    rw [hn2] at hnodd
    obtain ⟨k, hk⟩ := hnodd
    omega
  have hS : SecondKindStructure a hC.d b :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hC.setup.oddT hC.setup.normal
      htri h4 hno
  obtain ⟨x, hx, hxa⟩ := hS.conj
  refine ⟨x, hx, hxa, ?_⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (hS.le_centralizer hx)

theorem commutator_zpowers_le_cenGen (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a b : G} (ha : a ∈ Gamma hC) (hb : b ∈ Gamma hC) (hne : a ≠ b) (hcomm : Commute a b) :
    ⁅conjClosure (Subgroup.closure ({a, hC.d} : Set G)) (a * b),
        Subgroup.zpowers hC.d⁆ ≤ cenGen hC := by
  classical
  have htri : IsTriangle D a hC.d b := isTriangle_of_mem_Gamma hC ha hb hne hcomm
  have h4 : orderOf (a * b * hC.d) = 4 := hsecond a hC.d b htri
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({a, hC.d} : Set G) → IsTriangle D a x b →
      ¬ IsThirdKind a x b := by
    intro x _ _ hx hthird
    have h4' : orderOf (a * b * x) = 4 := hsecond a x b hx
    obtain ⟨n, hnodd, _hn1, hord⟩ := hthird
    have hn2 : n = 2 := by omega
    rw [hn2] at hnodd
    obtain ⟨k, hk⟩ := hnodd
    omega
  set Q : Subgroup G := conjClosure (Subgroup.closure ({a, hC.d} : Set G)) (a * b) with hQ
  have hS : SecondKindStructure a hC.d b :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hC.setup.oddT hC.setup.normal
      htri h4 hno
  have hQle : ⁅Q, Subgroup.zpowers hC.d⁆ ≤ Q :=
    secondKind_commutator_zpowers_le hC.setup.oddT hC.setup.normal htri h4 hno
  have hd2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hzpow : ∀ k : ℤ, hC.d ^ k = 1 ∨ hC.d ^ k = hC.d := by
    intro k
    by_cases hd1 : hC.d = 1
    · left
      simp [hd1]
    · have hord : orderOf hC.d = 2 :=
        (orderOf_eq_prime_iff (x := hC.d)).2 ⟨by simpa [pow_two] using hd2, hd1⟩
      rw [← zpow_mod_orderOf, hord]
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · left
        change k % (2 : ℤ) = 0 at hk
        simp [hk]
      · right
        change k % (2 : ℤ) = 1 at hk
        simp [hk]
  rw [Subgroup.commutator_le]
  intro q hq y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases hzpow k with h | h
  · have h1 : (⁅q, (1 : G)⁆ : G) = 1 := by simp [commutatorElement_def]
    rw [h, h1]
    exact Subgroup.one_mem _
  · rw [h]
    have hmemQ : (⁅q, hC.d⁆ : G) ∈ Q :=
      hQle (Subgroup.commutator_mem_commutator hq (Subgroup.mem_zpowers hC.d))
    have hsq : (⁅q, hC.d⁆ : G) * ⁅q, hC.d⁆ = 1 := hS.sq (⁅q, hC.d⁆ : G) hmemQ
    have hcD : q * hC.d * q⁻¹ ∈ D := hC.setup.normal q hC.d hC.hd
    have hc2 : (q * hC.d * q⁻¹) * (q * hC.d * q⁻¹) = 1 :=
      hC.setup.oddT.mul_self_eq_one hcD
    have heq : (⁅q, hC.d⁆ : G) = (q * hC.d * q⁻¹) * hC.d := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right hd2]
    have hcomm' : Commute (q * hC.d * q⁻¹) hC.d := by
      rw [commute_iff_mul_sq_eq_one hc2 hd2, ← heq, pow_two]
      exact hsq
    have hcX : q * hC.d * q⁻¹ ∈ cenGen hC :=
      Subgroup.subset_closure ⟨hcD, Subgroup.mem_centralizer_singleton_iff.mpr hcomm'⟩
    rw [heq]
    exact (cenGen hC).mul_mem hcX (d_mem_cenGen hC)

theorem step1_of_secondKind (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a b : G} (ha : a ∈ Gamma hC) (hb : b ∈ Gamma hC) (hne : a ≠ b) (hcomm : Commute a b) :
    ∃ x ∈ cenGen hC, x * a * x⁻¹ = b := by
  obtain ⟨x, hx, hxa, -⟩ := step1_secondKind hC hsecond ha hb hne hcomm
  exact ⟨x, commutator_zpowers_le_cenGen hC hsecond ha hb hne hcomm hx, hxa⟩

theorem GammaComp_subset_cenOrbit (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a : G} (ha : a ∈ Gamma hC) : GammaComp hC a ⊆ cenOrbit hC a := by
  intro b hb
  change Relation.ReflTransGen (GammaComm hC) a b at hb
  induction hb with
  | refl => exact self_mem_cenOrbit hC a
  | @tail b c _ hstep ih =>
    obtain ⟨hbΓ, hcΓ, hcomm⟩ := hstep
    by_cases hbc : b = c
    · rw [← hbc]
      exact ih
    · obtain ⟨x, hx, hxc⟩ := step1_of_secondKind hC hsecond hbΓ hcΓ hbc hcomm
      rw [← hxc]
      exact cenOrbit_invariant hC hx b ih

instance gammaComm_symm (hC : HypothesisC D) : Std.Symm (GammaComm hC) where
  symm _ _ h := ⟨h.2.1, h.1, h.2.2.symm⟩

theorem GammaReach_symm {hC : HypothesisC D} {a b : G} (h : GammaReach hC a b) :
    GammaReach hC b a := by
  change Relation.ReflTransGen (GammaComm hC) a b at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    exact Relation.ReflTransGen.head ⟨hcd.2.1, hcd.1, hcd.2.2.symm⟩ ih

theorem GammaReach_trans {hC : HypothesisC D} {a b c : G}
    (hab : GammaReach hC a b) (hbc : GammaReach hC b c) : GammaReach hC a c :=
  Relation.ReflTransGen.trans hab hbc

theorem GammaComp_subset_of_reach {hC : HypothesisC D} {a b : G}
    (h : GammaReach hC a b) : GammaComp hC b ⊆ GammaComp hC a :=
  fun _ hc => GammaReach_trans h hc

theorem GammaComp_eq_of_reach {hC : HypothesisC D} {a b : G}
    (h : GammaReach hC b a) : GammaComp hC a = GammaComp hC b := by
  apply Set.Subset.antisymm
  · exact GammaComp_subset_of_reach h
  · intro c hc
    exact GammaReach_trans (GammaReach_symm h) hc

theorem GammaComp_eq_of_mem {hC : HypothesisC D} {a b : G}
    (ha : a ∈ GammaComp hC b) : GammaComp hC a = GammaComp hC b :=
  GammaComp_eq_of_reach ha

theorem GammaComp_self_mem {hC : HypothesisC D} (a : G) : a ∈ GammaComp hC a :=
  Relation.ReflTransGen.refl

theorem GammaComp_mem_Gamma {hC : HypothesisC D} {a b : G} (ha : a ∈ Gamma hC)
    (hb : b ∈ GammaComp hC a) : b ∈ Gamma hC := by
  change GammaReach hC a b at hb
  induction hb with
  | refl => exact ha
  | @tail c d _ hcd _ => exact hcd.2.1

theorem GammaComp_conj_mem {hC : HypothesisC D} {x : G} (hx : x ∈ cenGen hC) {a b : G}
    (hb : b ∈ GammaComp hC a) : x * b * x⁻¹ ∈ GammaComp hC (x * a * x⁻¹) := by
  change GammaReach hC a b at hb
  change GammaReach hC (x * a * x⁻¹) (x * b * x⁻¹)
  induction hb with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
    exact ih.tail ⟨cenGen_maps_Gamma hC hx hcd.1, cenGen_maps_Gamma hC hx hcd.2.1,
      hcd.2.2.conj x⟩

theorem GammaComp_conj (hC : HypothesisC D) {x : G} (hx : x ∈ cenGen hC) (a : G) :
    (fun y => x * y * x⁻¹) '' GammaComp hC a = GammaComp hC (x * a * x⁻¹) := by
  ext b
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact GammaComp_conj_mem hx hc
  · intro hb
    have hx' : x⁻¹ ∈ cenGen hC := Subgroup.inv_mem _ hx
    have h := GammaComp_conj_mem hx' hb
    have e : x⁻¹ * (x * a * x⁻¹) * x = a := by group
    have h' : x⁻¹ * b * x ∈ GammaComp hC a := by
      simpa only [inv_inv, e] using h
    exact ⟨x⁻¹ * b * x, h', by group⟩

theorem secondKind_middle_conj_commute (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a g : G} (ha : a ∈ Gamma hC) (hgD : g ∈ D) (hgu : Commute g hC.d)
    (hne : g ≠ hC.d) (hga : ¬ Commute g a) :
    let Q := conjClosure (Subgroup.closure ({hC.d, a} : Set G)) (hC.d * g)
    (hC.d * g ∈ Q) ∧ (∀ q ∈ Q, Commute (q * a * q⁻¹) a) ∧
      (∀ q ∈ Q, Commute (q * (hC.d * a * hC.d) * q⁻¹) (hC.d * a * hC.d)) := by
  classical
  let u := hC.d
  have htri : IsTriangle D u a g := by
    refine ⟨hC.hd, hgD, Gamma_subset_D ha, ?_, hgu.symm, ?_, hga⟩
    ·
      intro h
      exact hne h.symm
    ·
      intro h
      exact not_commute_d_of_mem_Gamma ha h.symm
  have h4 : orderOf (u * g * a) = 4 := hsecond u a g htri
  have hno : ∀ x ∈ D, x ∈ Subgroup.closure ({u, a} : Set G) → IsTriangle D u x g →
      ¬ IsThirdKind u x g := by
    intro x _ _ hx hthird
    have h4' : orderOf (u * g * x) = 4 := hsecond u x g hx
    obtain ⟨n, hnodd, _hn1, hord⟩ := hthird
    have hn2 : n = 2 := by omega
    rw [hn2] at hnodd
    obtain ⟨k, hk⟩ := hnodd
    omega
  let Q : Subgroup G := conjClosure (Subgroup.closure ({u, a} : Set G)) (u * g)
  have hS : SecondKindStructure u a g :=
    CFSG.Timmesfeld.Bridge.OddTransp.secondKind_structure hC.setup.oddT hC.setup.normal
      htri h4 hno
  have huaD : u * a * u ∈ D := by
    have h := hC.setup.normal hC.d a (Gamma_subset_D ha)
    rw [hC.setup.oddT.inv_eq hC.hd] at h
    exact h
  have hu2 : u * u = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hK : Subgroup.closure ({u, a} : Set G) ⊔ Q = Subgroup.closure ({u, a, g} : Set G) :=
    secondKind_closure_eq hC.setup.oddT hC.setup.normal htri h4 hno
  have huK : u ∈ Subgroup.closure ({u, a, g} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hmapQ : Q.map (MulAut.conj u).toMonoidHom = Q := by
    apply le_antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact hS.normal u huK q hq
    · intro q hq
      refine ⟨u⁻¹ * q * u, ?_, ?_⟩
      · have h := hS.normal u⁻¹ (Subgroup.inv_mem _ huK) q hq
        rw [inv_inv] at h
        exact h
      · show u * (u⁻¹ * q * u) * u⁻¹ = q
        group
  have hmapzp : (Subgroup.zpowers a).map (MulAut.conj u).toMonoidHom =
      Subgroup.zpowers (u * a * u) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hfa : (MulAut.conj u).toMonoidHom a = u * a * u := by
        show u * a * u⁻¹ = u * a * u
        rw [hC.setup.oddT.inv_eq hC.hd]
      rw [map_zpow, hfa]
      exact Subgroup.zpow_mem (Subgroup.zpowers (u * a * u)) (Subgroup.mem_zpowers _) k
    · rw [Subgroup.zpowers_le]
      refine ⟨a, Subgroup.mem_zpowers a, ?_⟩
      show u * a * u⁻¹ = u * a * u
      rw [hC.setup.oddT.inv_eq hC.hd]
  have hcent_au : ⁅Q, Subgroup.zpowers (u * a * u)⁆ ≤
      Subgroup.centralizer ({u * a * u} : Set G) := by
    have hmap : (⁅Q, Subgroup.zpowers a⁆).map (MulAut.conj u).toMonoidHom =
        ⁅Q, Subgroup.zpowers (u * a * u)⁆ := by
      rw [Subgroup.map_commutator, hmapQ, hmapzp]
    rw [← hmap]
    refine (Subgroup.map_mono hS.le_centralizer).trans ?_
    have hfa : (MulAut.conj u).toMonoidHom a = u * a * u := by
      show u * a * u⁻¹ = u * a * u
      rw [hC.setup.oddT.inv_eq hC.hd]
    simpa only [Set.image_singleton, hfa] using
      Subgroup.map_centralizer_le_centralizer_image ({a} : Set G) (MulAut.conj u).toMonoidHom
  have hqcomm : ∀ (b : G), b ∈ D →
      ⁅Q, Subgroup.zpowers b⁆ ≤ Subgroup.centralizer ({b} : Set G) →
      ∀ q ∈ Q, Commute (q * b * q⁻¹) b := by
    intro b hbD hcent q hq
    have hb2 : b * b = 1 := hC.setup.oddT.mul_self_eq_one hbD
    have hq2 : q * q = 1 := hS.sq q hq
    have hc : ⁅b, q⁆ ∈ ⁅Q, Subgroup.zpowers b⁆ := by
      have hmem : (⁅b, q⁆ : G) ∈ ⁅Subgroup.zpowers b, Q⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hq
      rwa [Subgroup.commutator_comm] at hmem
    have hcb : Commute ⁅b, q⁆ b :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcent hc)
    rw [conj_eq_mul_commutator hb2 hq2]
    exact (Commute.refl b).mul_left hcb
  have hQu : ⁅Q, Subgroup.zpowers u⁆ ≤ Q :=
    secondKind_commutator_zpowers_u_le hC.setup.oddT hC.setup.normal htri h4 hno
  have hQa : ⁅Q, Subgroup.zpowers a⁆ ≤ Q :=
    secondKind_commutator_zpowers_le hC.setup.oddT hC.setup.normal htri h4 hno
  obtain ⟨x, hx, hxu⟩ := hS.conj
  have hxQ : x ∈ Q := hQa hx
  have hx2 : x * x = 1 := hS.sq x hxQ
  have hs_eq : u * g = ⁅u, x⁆ := by
    have hg_eq : g = u * ⁅u, x⁆ := by
      rw [← hxu, conj_eq_mul_commutator hu2 hx2]
    rw [hg_eq, ← mul_assoc, hu2, one_mul]
  have hsQ : u * g ∈ Q := by
    rw [hs_eq]
    have hmem : (⁅u, x⁆ : G) ∈ ⁅Subgroup.zpowers u, Q⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers u) hxQ
    rw [Subgroup.commutator_comm] at hmem
    exact hQu hmem
  exact ⟨hsQ, hqcomm a (Gamma_subset_D ha) hS.le_centralizer,
    hqcomm (u * a * u) huaD hcent_au⟩

theorem cenOrbit_eq_comp_union_conj (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a : G} (ha : a ∈ Gamma hC) :
    cenOrbit hC a =
      GammaComp hC a ∪ (fun y => hC.d * y * hC.d) '' GammaComp hC a := by
  classical
  set B : Set G := GammaComp hC a with hB
  set Bu : Set G := (fun y => hC.d * y * hC.d) '' B with hBu
  have hu : hC.d ∈ cenGen hC := d_mem_cenGen hC
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hu_inv : hC.d⁻¹ = hC.d := hC.setup.oddT.inv_eq hC.hd
  have haB : a ∈ B := by rw [hB]; exact GammaComp_self_mem (hC := hC) a
  have hBΓ : B ⊆ Gamma hC := by
    intro b hb
    rw [hB] at hb
    exact GammaComp_mem_Gamma ha hb
  have hBuΓ : Bu ⊆ Gamma hC := by
    rintro b ⟨c, hc, rfl⟩
    simpa only [hu_inv] using cenGen_maps_Gamma hC hu (hBΓ hc)
  have hBu_eq : Bu = GammaComp hC (hC.d * a * hC.d) := by
    rw [hBu, hB]
    simpa only [hC.setup.oddT.inv_eq hC.hd] using GammaComp_conj hC hu a
  have hBA : B ⊆ cenOrbit hC a := by
    rw [hB]; exact GammaComp_subset_cenOrbit hC hsecond ha
  have hBuA : Bu ⊆ cenOrbit hC a := by
    rintro b ⟨c, hc, rfl⟩
    simpa only [hu_inv] using cenOrbit_invariant hC hu c (hBA hc)
  have huu : (fun y => hC.d * (hC.d * y * hC.d) * hC.d) = id := by
    funext y
    show hC.d * (hC.d * y * hC.d) * hC.d = y
    rw [show hC.d * (hC.d * y * hC.d) * hC.d =
      (hC.d * hC.d) * y * (hC.d * hC.d) by group, hu2]
    group
  have hinner : (fun y => hC.d * y * hC.d) '' ((fun y => hC.d * y * hC.d) '' B) = B := by
    rw [Set.image_image]
    rw [show (fun y => hC.d * (hC.d * y * hC.d) * hC.d) = id from huu, Set.image_id]
  have hgen : ∀ g ∈ (D : Set G) ∩ (Subgroup.centralizer ({hC.d} : Set G) : Set G),
      (fun y => g * y * g⁻¹) '' (B ∪ Bu) = B ∪ Bu := by
    rintro g ⟨hgD, hgc⟩
    have hgu : Commute g hC.d := Subgroup.mem_centralizer_singleton_iff.mp hgc
    have hgS : g ∈ cenGen hC := Subgroup.subset_closure ⟨hgD, hgc⟩
    have hg2 : g * g = 1 := hC.setup.oddT.mul_self_eq_one hgD
    have hg_inv : g⁻¹ = g := hC.setup.oddT.inv_eq hgD
    by_cases hga : Commute g a
    ·
      have hfix : g * a * g⁻¹ = a := by rw [hga.eq, mul_inv_cancel_right]
      have hgB : (fun y => g * y * g⁻¹) '' B = B := by
        rw [hB, GammaComp_conj hC hgS a, hfix]
      have hc : Commute g (hC.d * a * hC.d) := by
        have h1 : Commute g (hC.d * a) := hgu.mul_right hga
        exact h1.mul_right hgu
      have hfixu : g * (hC.d * a * hC.d) * g⁻¹ = hC.d * a * hC.d := by
        rw [hc.eq, mul_inv_cancel_right]
      have hgBu : (fun y => g * y * g⁻¹) '' Bu = Bu := by
        rw [hBu_eq, GammaComp_conj hC hgS (hC.d * a * hC.d), hfixu]
      rw [Set.image_union, hgB, hgBu]
    · by_cases hge : g = hC.d
      ·
        have hgB : (fun y => g * y * g⁻¹) '' B = Bu := by
          rw [hge]
          simpa only [hC.setup.oddT.inv_eq hC.hd] using hBu.symm
        have hgBu : (fun y => g * y * g⁻¹) '' Bu = B := by
          rw [hge, hBu, Set.image_image]
          rw [show (fun y => hC.d * (hC.d * y * hC.d) * hC.d⁻¹) =
            (fun y => hC.d * (hC.d * y * hC.d) * hC.d) by
              funext y; rw [hC.setup.oddT.inv_eq hC.hd]]
          rw [huu, Set.image_id]
        rw [Set.image_union, hgB, hgBu, Set.union_comm]
      ·
        have hdata := secondKind_middle_conj_commute hC hsecond ha hgD hgu hge hga
        obtain ⟨hsQ, hcommA, hcommAu⟩ := hdata
        have hsS : hC.d * g ∈ cenGen hC := (cenGen hC).mul_mem hu hgS
        have hsB : (hC.d * g) * a * (hC.d * g)⁻¹ ∈ B := by
          rw [hB]
          exact Relation.ReflTransGen.single
            ⟨ha, cenGen_maps_Gamma hC hsS ha, (hcommA (hC.d * g) hsQ).symm⟩
        have hsB_eq : (fun y => (hC.d * g) * y * (hC.d * g)⁻¹) '' B = B := by
          rw [hB, GammaComp_conj hC hsS a, GammaComp_eq_of_mem hsB]
        have hugu : hC.d * g * hC.d = g := by
          rw [mul_assoc, hgu.eq, ← mul_assoc, hu2, one_mul]
        have hs_au : (hC.d * g) * (hC.d * a * hC.d) * (hC.d * g)⁻¹ =
            g * a * g⁻¹ := by
          calc (hC.d * g) * (hC.d * a * hC.d) * (hC.d * g)⁻¹
              = (hC.d * g) * (hC.d * a * hC.d) * (g * hC.d) := by
                rw [mul_inv_rev, hu_inv, hg_inv]
            _ = (hC.d * g * hC.d) * a * (hC.d * g * hC.d) := by group
            _ = g * a * g := by rw [hugu]
            _ = g * a * g⁻¹ := by rw [hg_inv]
        have hauΓ : hC.d * a * hC.d ∈ Gamma hC := hBuΓ ⟨a, haB, rfl⟩
        have hgaΓ : g * a * g⁻¹ ∈ Gamma hC := by
          rw [← hs_au]
          exact cenGen_maps_Gamma hC hsS hauΓ
        have hcomm : Commute (hC.d * a * hC.d) (g * a * g⁻¹) := by
          rw [← hs_au]
          exact (hcommAu (hC.d * g) hsQ).symm
        have hsBu_eq : (fun y => (hC.d * g) * y * (hC.d * g)⁻¹) '' Bu = Bu := by
          rw [hBu_eq, GammaComp_conj hC hsS (hC.d * a * hC.d), hs_au]
          have hgag_comp : g * a * g⁻¹ ∈ GammaComp hC (hC.d * a * hC.d) :=
            Relation.ReflTransGen.single ⟨hauΓ, hgaΓ, hcomm⟩
          exact GammaComp_eq_of_mem hgag_comp
        have hg_eq : g = (hC.d * g) * hC.d := by
          rw [mul_assoc, hgu.eq, ← mul_assoc, hu2, one_mul]
        have hgB : (fun y => g * y * g⁻¹) '' B = Bu := by
          rw [hg_eq]
          calc (fun y => ((hC.d * g) * hC.d) * y * ((hC.d * g) * hC.d)⁻¹) '' B
              = (fun y => (hC.d * g) * (hC.d * y * hC.d) * (hC.d * g)⁻¹) '' B := by
                congr 1
                funext y
                rw [show ((hC.d * g) * hC.d) * y * ((hC.d * g) * hC.d)⁻¹ =
                  (hC.d * g) * (hC.d * y * hC.d) * (hC.d * g)⁻¹ by
                    rw [mul_inv_rev, hu_inv]
                    group]
            _ = (fun y => (hC.d * g) * y * (hC.d * g)⁻¹) ''
                  ((fun y => hC.d * y * hC.d) '' B) := by rw [Set.image_image]
            _ = (fun y => (hC.d * g) * y * (hC.d * g)⁻¹) '' Bu := by rw [hBu]
            _ = Bu := hsBu_eq
        have hgBu : (fun y => g * y * g⁻¹) '' Bu = B := by
          rw [hg_eq]
          calc (fun y => ((hC.d * g) * hC.d) * y * ((hC.d * g) * hC.d)⁻¹) '' Bu
              = (fun y => (hC.d * g) * (hC.d * y * hC.d) * (hC.d * g)⁻¹) '' Bu := by
                congr 1
                funext y
                rw [show ((hC.d * g) * hC.d) * y * ((hC.d * g) * hC.d)⁻¹ =
                  (hC.d * g) * (hC.d * y * hC.d) * (hC.d * g)⁻¹ by
                    rw [mul_inv_rev, hu_inv]
                    group]
            _ = (fun y => (hC.d * g) * y * (hC.d * g)⁻¹) '' B := by
                rw [hBu, Set.image_image]
                congr 1
                funext y
                rw [congrFun huu y]
                simp only [id_eq]
            _ = B := hsB_eq
        rw [Set.image_union, hgB, hgBu, Set.union_comm]
  have hnorm : cenGen hC ≤ Subgroup.normalizer ((B ∪ Bu : Set G)) := by
    rw [cenGen, Subgroup.closure_le]
    intro g hg
    exact Subgroup.mem_normalizer_iff_conj_image_eq.mpr (hgen g hg)
  apply Set.Subset.antisymm
  · rintro b ⟨x, hx, rfl⟩
    have hxN : x ∈ Subgroup.normalizer ((B ∪ Bu : Set G)) := hnorm hx
    exact (Subgroup.mem_set_normalizer_iff.mp hxN a).mp (Or.inl haB)
  · intro b hb
    rcases hb with hb | hb
    · exact hBA hb
    · exact hBuA hb

theorem cenOrbit_eq_of_mem (hC : HypothesisC D) {a b : G}
    (ha : a ∈ cenOrbit hC b) : cenOrbit hC a = cenOrbit hC b := by
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := ha
    exact ⟨x * y, (cenGen hC).mul_mem hx hy, by group⟩
  · intro c hc
    obtain ⟨x, hx, rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨x * y⁻¹, (cenGen hC).mul_mem hx (Subgroup.inv_mem _ hy), ?_⟩
    have hb : y⁻¹ * (y * b * y⁻¹) * y = b := by group
    calc x * b * x⁻¹ = x * (y⁻¹ * (y * b * y⁻¹) * y) * x⁻¹ := by rw [hb]
      _ = x * y⁻¹ * (y * b * y⁻¹) * (x * y⁻¹)⁻¹ := by group

theorem cenOrbit_dichotomy (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    {a : G} (ha : a ∈ Gamma hC) :
    GammaComp hC a = cenOrbit hC a ∨
      (Disjoint (GammaComp hC a) ((fun y => hC.d * y * hC.d) '' GammaComp hC a) ∧
       (cenOrbit hC a).ncard = 2 * (GammaComp hC a).ncard) := by
  classical
  have hA := cenOrbit_eq_comp_union_conj hC hsecond ha
  have hBu_eq : (fun y => hC.d * y * hC.d) '' GammaComp hC a =
      GammaComp hC (hC.d * a * hC.d) := by
    simpa only [hC.setup.oddT.inv_eq hC.hd] using
      GammaComp_conj hC (d_mem_cenGen hC) a
  by_cases hdis : Disjoint (GammaComp hC a) ((fun y => hC.d * y * hC.d) '' GammaComp hC a)
  · right
    refine ⟨hdis, ?_⟩
    rw [hA, Set.ncard_union_eq hdis]
    have hinj : Function.Injective (fun y : G => hC.d * y * hC.d) := by
      have hfun : (fun y : G => hC.d * y * hC.d) = MulAut.conj hC.d := by
        funext y
        rw [MulAut.conj_apply, hC.setup.oddT.inv_eq hC.hd]
      rw [hfun]
      exact (MulAut.conj hC.d).injective
    have himg : ((fun y => hC.d * y * hC.d) '' GammaComp hC a).ncard =
        (GammaComp hC a).ncard :=
      Set.ncard_image_of_injective _ hinj
    rw [himg]
    omega
  · left
    rw [Set.not_disjoint_iff] at hdis
    obtain ⟨c, hcB, hcBu⟩ := hdis
    rw [hBu_eq] at hcBu
    have h1 : GammaComp hC c = GammaComp hC a := GammaComp_eq_of_mem hcB
    have h2 : GammaComp hC c = GammaComp hC (hC.d * a * hC.d) := GammaComp_eq_of_mem hcBu
    have hBBu : GammaComp hC a = (fun y => hC.d * y * hC.d) '' GammaComp hC a := by
      rw [hBu_eq]
      exact h1.symm.trans h2
    rw [hA, ← hBBu, Set.union_self]

theorem hstep234_of_step3_step4 (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hstep3 : ∀ (A : Set G) (a : G),
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) → a ∈ A →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A ≠ Gamma hC → GammaComp hC a ≠ A)
    (hstep4 : ∀ (A : Set G) (a : G),
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) → a ∈ A →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A ≠ Gamma hC →
      Disjoint (GammaComp hC a) ((fun y => hC.d * y * hC.d) '' GammaComp hC a) →
      (cenOrbit hC a).ncard = 2 * (GammaComp hC a).ncard → False) :
    ∀ A : Set G,
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) →
      (∀ b ∈ A, GammaComp hC b ⊆ A) →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A = Gamma hC := by
  intro A hAorbit _hcomp hmax
  by_contra hne
  obtain ⟨a₀, ha₀, hA⟩ := hAorbit
  have ha₀A : a₀ ∈ A := by rw [hA]; exact self_mem_cenOrbit hC a₀
  have ha₀Γ : a₀ ∈ Gamma hC := cenOrbit_subset_Gamma hC ha₀ (self_mem_cenOrbit hC a₀)
  rcases cenOrbit_dichotomy hC hsecond ha₀Γ with hB | ⟨hdis, hcard⟩
  · exact hstep3 A a₀ ⟨a₀, ha₀, hA⟩ ha₀A hmax hne (hB.trans hA.symm)
  · exact hstep4 A a₀ ⟨a₀, ha₀, hA⟩ ha₀A hmax hne hdis hcard

theorem commSet_nonempty (hC : HypothesisC D) {c : G} (hc : c ∈ D) :
    (commSet D c).Nonempty := by
  classical
  obtain ⟨e, he, -⟩ := hC.hE
  have heD : e ∈ D := he.1
  have hene : e ≠ hC.d := he.2.2
  by_contra hne
  have honly : ∀ y ∈ D, Commute c y → y = c := by
    intro y hyD hcy
    by_contra hyc
    exact hne ⟨y, hyD, hcy.symm, hyc⟩
  have hy0 : ∃ y ∈ D, y ≠ c := by
    by_cases hc' : c = hC.d
    · exact ⟨e, heD, by rw [hc']; exact hene⟩
    · exact ⟨hC.d, hC.hd, fun h' => hc' h'.symm⟩
  obtain ⟨y0, hy0D, hy0ne⟩ := hy0
  have hreach : Reach D c y0 := reach_of_not_disconnected hC.conn hc hy0D
  have hmem : y0 ∈ ({c} : Set G) :=
    mem_of_reach (D := D) (S := {c}) (by
      intro x hx y hyD hxy
      rw [Set.mem_singleton_iff] at hx
      subst hx
      simpa using honly y hyD hxy) (by simp) hreach
  exact hy0ne (by simpa using hmem)

theorem exists_isMaxOrbit (hC : HypothesisC D) {c : G} (hc : c ∈ D) :
    ∃ E, IsMaxOrbit D c E := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let S : Finset G := Finset.univ.filter (fun e => e ∈ commSet D c)
  have hSne : S.Nonempty := by
    obtain ⟨e, he⟩ := commSet_nonempty hC hc
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩⟩
  let f : G → ℕ := fun e => (orbitIn D c e).ncard
  obtain ⟨e, heS, hemax⟩ := Finset.exists_mem_eq_sup S hSne f
  refine ⟨orbitIn D c e, e, (Finset.mem_filter.mp heS).2, rfl, ?_⟩
  intro e' he'
  have hle : f e' ≤ S.sup f :=
    Finset.le_sup (f := f) (Finset.mem_filter.mpr ⟨Finset.mem_univ e', he'⟩)
  rw [hemax] at hle
  simpa [f] using hle

theorem exists_hypothesisC_d (hC : HypothesisC D) {c : G} (hc : c ∈ D) :
    ∃ hCc : HypothesisC D, hCc.d = c := by
  obtain ⟨E, hE⟩ := exists_isMaxOrbit hC hc
  exact ⟨{ setup := hC.setup, conn := hC.conn, d := c, hd := hc, E := E, hE := hE }, rfl⟩

theorem normalizer_comp_ne_top (hC : HypothesisC D) {B : Set G}
    (hBΓ : B ⊆ Gamma hC) (hBne : B.Nonempty) :
    Subgroup.normalizer B ≠ ⊤ := by
  intro hN
  obtain ⟨b, hb⟩ := hBne
  have hbD : b ∈ D := Gamma_subset_D (hBΓ hb)
  have hDsub : D ⊆ B := by
    rw [hC.setup.eq_setOf_isConj hbD]
    intro y hy
    rw [Set.mem_setOf_eq] at hy
    rw [isConj_iff] at hy
    obtain ⟨g, rfl⟩ := hy
    have hgN : g ∈ Subgroup.normalizer B := hN ▸ Subgroup.mem_top g
    exact (Subgroup.mem_set_normalizer_iff.mp hgN b).mp hb
  have hdD : hC.d ∈ D := hC.hd
  exact (Set.disjoint_left.mp (disjoint_Gamma_alpha hC) (hBΓ (hDsub hdD))) hC.d_mem_alpha

theorem cenGen_transitive_AalphaStar (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hstep234 : ∀ A : Set G,
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) →
      (∀ b ∈ A, GammaComp hC b ⊆ A) →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A = Gamma hC) :
    ∀ a ∈ AalphaStar D hC.alpha, ∀ b ∈ AalphaStar D hC.alpha,
      ∃ x ∈ Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G)),
        x * a * x⁻¹ = b := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  intro a ha b hb
  have ha' : a ∈ Gamma hC := ha
  have hb' : b ∈ Gamma hC := hb
  let f : G → ℕ := fun a => (cenOrbit hC a).ncard
  let s : Finset G := Finset.univ.filter (fun a => a ∈ Gamma hC)
  have hs : s.Nonempty := ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha'⟩⟩
  obtain ⟨a₀, ha₀s, ha₀max⟩ := Finset.exists_mem_eq_sup s hs f
  have ha₀Γ : a₀ ∈ Gamma hC := (Finset.mem_filter.mp ha₀s).2
  set A : Set G := cenOrbit hC a₀ with hA
  have hAorbit : ∃ a₀' ∈ Gamma hC, A = cenOrbit hC a₀' := ⟨a₀, ha₀Γ, hA⟩
  have hAcomp : ∀ b ∈ A, GammaComp hC b ⊆ A := by
    intro b hbA
    have hbΓ : b ∈ Gamma hC := by
      rw [hA] at hbA
      exact cenOrbit_subset_Gamma hC ha₀Γ hbA
    refine (GammaComp_subset_cenOrbit hC hsecond hbΓ).trans ?_
    intro c hc
    rw [hA] at hbA ⊢
    obtain ⟨y, hy, hyb⟩ := hbA
    obtain ⟨x, hx, hxc⟩ := hc
    exact ⟨x * y, (cenGen hC).mul_mem hx hy, by rw [hxc, hyb]; group⟩
  have hAmax : ∀ B : Set G,
      (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard := by
    rintro B ⟨b₀, hb₀, rfl⟩
    have hle : f b₀ ≤ s.sup f :=
      Finset.le_sup (f := f) (Finset.mem_filter.mpr ⟨Finset.mem_univ b₀, hb₀⟩)
    rw [ha₀max] at hle
    simpa [f, hA] using hle
  have hAG : A = Gamma hC := hstep234 A hAorbit hAcomp hAmax
  have haA : a ∈ A := by rw [hAG]; exact ha'
  have hbA : b ∈ A := by rw [hAG]; exact hb'
  rw [hA] at haA hbA
  obtain ⟨x, hx, hxa⟩ := haA
  obtain ⟨y, hy, hyb⟩ := hbA
  refine ⟨y * x⁻¹, (cenGen hC).mul_mem hy (Subgroup.inv_mem _ hx), ?_⟩
  calc y * x⁻¹ * a * (y * x⁻¹)⁻¹
      = y * x⁻¹ * (x * a₀ * x⁻¹) * (y * x⁻¹)⁻¹ := by rw [hxa]
    _ = y * a₀ * y⁻¹ := by group
    _ = b := hyb.symm

theorem cenGen_transitive_AalphaStar_of_step3_step4 (hC : HypothesisC D)
    (hsecond : ∀ u w v : G, IsTriangle D u w v → orderOf (u * v * w) = 4)
    (hstep3 : ∀ (A : Set G) (a : G),
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) → a ∈ A →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A ≠ Gamma hC → GammaComp hC a ≠ A)
    (hstep4 : ∀ (A : Set G) (a : G),
      (∃ a₀ ∈ Gamma hC, A = cenOrbit hC a₀) → a ∈ A →
      (∀ B : Set G, (∃ b₀ ∈ Gamma hC, B = cenOrbit hC b₀) → B.ncard ≤ A.ncard) →
      A ≠ Gamma hC →
      Disjoint (GammaComp hC a) ((fun y => hC.d * y * hC.d) '' GammaComp hC a) →
      (cenOrbit hC a).ncard = 2 * (GammaComp hC a).ncard → False) :
    ∀ a ∈ AalphaStar D hC.alpha, ∀ b ∈ AalphaStar D hC.alpha,
      ∃ x ∈ Subgroup.closure ((D : Set G) ∩ Subgroup.centralizer ({hC.d} : Set G)),
        x * a * x⁻¹ = b :=
  cenGen_transitive_AalphaStar hC hsecond
    (hstep234_of_step3_step4 hC hsecond hstep3 hstep4)

end CFSG.OddTranspositions
