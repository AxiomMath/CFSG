module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfMaxToral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE7Three
public import CFSG.LocalAnalysis.StandardType.GGL45TorusPiKCount
public import CFSG.GroupTheory.CommPowMemCount
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcAbs
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ExcFramesHalf

@[expose] def GGL45E6NonToralThreeCent :
    Prop :=
  ∀ (K₀ : Type) [Field K₀] [Finite K₀] [CharP K₀ 2]
    (Ebar : Subgroup (ModGL .E6 (AlgebraicClosure K₀))),
    Ebar ≤ adjointGroup .E6 (AlgebraicClosure K₀) → IsElemAbelian 3 Ebar →
      ¬ IsToralSubgroup .E6 (AlgebraicClosure K₀) Ebar → Nat.card Ebar = 3 ^ 4 →
        (∀ x ∈ adjointGroup .E6 (AlgebraicClosure K₀),
          ∀ y ∈ adjointGroup .E6 (AlgebraicClosure K₀),
            (∀ e ∈ Ebar, x * e = e * x) → (∀ e ∈ Ebar, y * e = e * y) → x * y = y * x) ∧
        (∀ c ∈ adjointGroup .E6 (AlgebraicClosure K₀), (∀ e ∈ Ebar, c * e = e * c) →
          ∃ e ∈ Ebar, ∃ d : ModGL .E6 (AlgebraicClosure K₀),
            (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 (AlgebraicClosure K₀),
              (∀ e ∈ Ebar, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ c = e * d) ∧
        {d : ModGL .E6 (AlgebraicClosure K₀) |
          (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 (AlgebraicClosure K₀),
            (∀ e ∈ Ebar, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1}.encard ≤ 9

private def powCentralSubgroup {G : Type*} [Group G] (A G₀ : Subgroup G)
    (hcomm : ∀ x ∈ G₀, ∀ y ∈ G₀, (∀ e ∈ A, x * e = e * x) →
      (∀ e ∈ A, y * e = e * y) → x * y = y * x) : Subgroup G where
  carrier := {d : G | ∀ m : ℕ, ∃ c' ∈ G₀,
    (∀ e ∈ A, c' * e = e * c') ∧ d = c' ^ 3 ^ m}
  one_mem' := by
    intro m
    exact ⟨1, G₀.one_mem, by intro e he; simp, (one_pow (3 ^ m)).symm⟩
  mul_mem' := by
    rintro d₁ d₂ hd₁ hd₂ m
    obtain ⟨c₁, hc₁G, hc₁c, hd₁m⟩ := hd₁ m
    obtain ⟨c₂, hc₂G, hc₂c, hd₂m⟩ := hd₂ m
    refine ⟨c₁ * c₂, G₀.mul_mem hc₁G hc₂G, ?_, ?_⟩
    · intro e he
      calc (c₁ * c₂) * e = c₁ * (c₂ * e) := by group
        _ = c₁ * (e * c₂) := by rw [hc₂c e he]
        _ = (c₁ * e) * c₂ := by group
        _ = (e * c₁) * c₂ := by rw [hc₁c e he]
        _ = e * (c₁ * c₂) := by group
    · rw [hd₁m, hd₂m, Commute.mul_pow (hcomm c₁ hc₁G c₂ hc₂G hc₁c hc₂c) (3 ^ m)]
  inv_mem' := by
    rintro d hd m
    obtain ⟨c, hcG, hcc, hdm⟩ := hd m
    refine ⟨c⁻¹, G₀.inv_mem hcG, ?_, ?_⟩
    · intro e he
      exact ((show Commute c e from hcc e he).inv_left).eq
    · rw [hdm, ← inv_pow]

private theorem powCentralSubgroup_le {G : Type*} [Group G] {A G₀ : Subgroup G}
    (hcomm : ∀ x ∈ G₀, ∀ y ∈ G₀, (∀ e ∈ A, x * e = e * x) →
      (∀ e ∈ A, y * e = e * y) → x * y = y * x) :
    powCentralSubgroup A G₀ hcomm ≤ G₀ ⊓ Subgroup.centralizer (A : Set G) := by
  intro d hd
  obtain ⟨c, hcG, hcc, hd0⟩ := hd 0
  have hdc : d = c := by simpa using hd0
  constructor
  · rw [hdc]; exact hcG
  · change d ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    rw [hdc]
    exact (hcc e he).symm

private noncomputable def e67Ebar {K : Type} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K)) : Subgroup (MulAut R) :=
  E.map (ggInducedAut θ)

private noncomputable def e67Bridge {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R] (Θ : H →* MulAut R)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R)
    (E : Subgroup (MulAut K)) : Subgroup (ModGL τ L) :=
  CFSG.HardMathSupport.C14Exc.bridgeSub Θ (e67Ebar θ E)

private noncomputable def e67Centralizer {τ : Tag} {L : Type} [Field L]
    (Ê : Subgroup (ModGL τ L)) : Subgroup (ModGL τ L) :=
  adjointGroup τ L ⊓ Subgroup.centralizer (Ê : Set (ModGL τ L))

private noncomputable def e67T {K : Type} [Group K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) (E : Subgroup (MulAut K))
    (I : Set (MulAut R)) (Ē : Subgroup (MulAut R)) : Set (MulAut R) :=
  {t : MulAut R | t ∈ I ∧
    (∀ e ∈ E, t * ggInducedAut θ e = ggInducedAut θ e * t) ∧ t ^ 3 ∈ Ē}

private theorem e67_finite_mulAut {K : Type} [Group K] [Finite K] {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) : Finite (MulAut R) := by
  haveI : Finite (K ⧸ Subgroup.center K) :=
    Finite.of_surjective (QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)
  haveI : Finite R := Finite.of_equiv _ θ.toEquiv
  exact CFSG.StandardType.TableBSymp.finite_mulAut (R := R)

private theorem e67Bridge_facts {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hH : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)} (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {E : Subgroup (MulAut K)} (hEelem : IsElemAbelian 3 E)
    (hInd : ∀ e ∈ E, GGL45InducesIn θ I e) :
    Nat.card (e67Bridge Θ θ E) = Nat.card E ∧
      e67Bridge Θ θ E ≤ adjointGroup τ L ∧ IsElemAbelian 3 (e67Bridge Θ θ E) := by
  have hEI : ∀ e ∈ e67Ebar θ E, ∃ g : H, Θ g = e := by
    intro e he
    obtain ⟨e₀, he₀, rfl⟩ := Subgroup.mem_map.mp he
    exact (hI _).mp ((ggL45_inducesIn_iff (R := R) θ I e₀).mp (hInd e₀ he₀))
  have hĒcard : Nat.card (e67Ebar θ E) = Nat.card E :=
    Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hK θ)
  have hcard : Nat.card (e67Bridge Θ θ E) = Nat.card (e67Ebar θ E) := by
    rw [e67Bridge]
    exact CFSG.HardMathSupport.C14Exc.bridgeSub_card hΘ hEI
  refine ⟨hcard.trans hĒcard, ?_, ?_⟩
  · intro x hx
    change x ∈ ((e67Ebar θ E).comap Θ).map H.subtype at hx
    obtain ⟨g, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hH g.2
  · rw [e67Bridge]
    exact CFSG.HardMathSupport.C14Exc.bridgeSub_isElemAbelian hΘ
      (hEelem.map (ggInducedAut θ))

private theorem e67_centralizes_bridge {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} {R : Type} [Group R]
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) {E : Subgroup (MulAut K)} {g : H} {x : MulAut R}
    (hg : Θ g = x)
    (hxc : ∀ e ∈ E, x * ggInducedAut θ e = ggInducedAut θ e * x) :
    ∀ u ∈ e67Bridge Θ θ E, (g : ModGL τ L) * u = u * (g : ModGL τ L) := by
  intro u hu
  change u ∈ ((e67Ebar θ E).comap Θ).map H.subtype at hu
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu₀)
  have hcomm : g * u₀ = u₀ * g := by
    apply hΘ
    rw [map_mul, map_mul, hg, ← heq]
    exact hxc e he
  exact congrArg H.subtype hcomm

private theorem e67_commute_of_bridge {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hH : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)} {K : Type} [Group K]
    (θ : K ⧸ Subgroup.center K ≃* R) (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {E : Subgroup (MulAut K)}
    (hcommG : ∀ x ∈ adjointGroup τ L, ∀ y ∈ adjointGroup τ L,
      (∀ e ∈ e67Bridge Θ θ E, x * e = e * x) →
      (∀ e ∈ e67Bridge Θ θ E, y * e = e * y) → x * y = y * x) :
    ∀ x ∈ I, ∀ y ∈ I,
      (∀ e ∈ E, x * ggInducedAut θ e = ggInducedAut θ e * x) →
      (∀ e ∈ E, y * ggInducedAut θ e = ggInducedAut θ e * y) → x * y = y * x := by
  intro x hx y hy hxc hyc
  obtain ⟨g, hg⟩ := (hI x).mp hx
  obtain ⟨h, hh⟩ := (hI y).mp hy
  have hgc := e67_centralizes_bridge θ Θ hΘ hg hxc
  have hhc := e67_centralizes_bridge θ Θ hΘ hh hyc
  have hgh := hcommG (g : ModGL τ L) (hH g.2) (h : ModGL τ L) (hH h.2) hgc hhc
  have hghH : g * h = h * g := by
    apply H.subtype_injective
    rw [map_mul, map_mul]
    exact hgh
  calc x * y = Θ g * Θ h := by rw [hg, hh]
    _ = Θ (g * h) := (map_mul Θ g h).symm
    _ = Θ (h * g) := by rw [hghH]
    _ = Θ h * Θ g := map_mul Θ h g
    _ = y * x := by rw [hh, hg]

private theorem e67_centralizer_facts {τ : Tag} {L : Type} [Field L]
    {Ê : Subgroup (ModGL τ L)} (hÊadj : Ê ≤ adjointGroup τ L)
    (hÊea : IsElemAbelian 3 Ê)
    (hcommG : ∀ x ∈ adjointGroup τ L, ∀ y ∈ adjointGroup τ L,
      (∀ e ∈ Ê, x * e = e * x) → (∀ e ∈ Ê, y * e = e * y) → x * y = y * x)
    (hdec : ∀ c ∈ adjointGroup τ L, (∀ e ∈ Ê, c * e = e * c) →
      ∃ e ∈ Ê, ∃ d : ModGL τ L, (∀ m : ℕ, ∃ c' ∈ adjointGroup τ L,
        (∀ e ∈ Ê, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ c = e * d) :
    Ê ≤ e67Centralizer Ê ∧
      powCentralSubgroup Ê (adjointGroup τ L) hcommG ≤ e67Centralizer Ê ∧
      (∀ x ∈ e67Centralizer Ê, ∀ y ∈ e67Centralizer Ê, x * y = y * x) ∧
      ∀ c ∈ e67Centralizer Ê, ∃ a ∈ Ê,
        ∃ d ∈ powCentralSubgroup Ê (adjointGroup τ L) hcommG, c = a * d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨hÊadj hx, ?_⟩
    change x ∈ Subgroup.centralizer (Ê : Set (ModGL τ L))
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (CFSG.Open.IsElemAbelian.comm hÊea hx he).symm
  · intro d hd
    exact powCentralSubgroup_le (A := Ê) (G₀ := adjointGroup τ L) hcommG hd
  · intro x hx y hy
    exact hcommG x hx.1 y hy.1
      (fun e he => (Subgroup.mem_centralizer_iff.mp hx.2 e he).symm)
      (fun e he => (Subgroup.mem_centralizer_iff.mp hy.2 e he).symm)
  · intro c hc
    obtain ⟨e, he, d, hd, hcd⟩ := hdec c hc.1
      (fun e he => (Subgroup.mem_centralizer_iff.mp hc.2 e he).symm)
    exact ⟨e, he, d, hd, hcd⟩

private theorem e67_count_centralizer {τ : Tag} {L : Type} [Field L]
    {Ê : Subgroup (ModGL τ L)} (hÊadj : Ê ≤ adjointGroup τ L)
    (hÊea : IsElemAbelian 3 Ê)
    (hcommG : ∀ x ∈ adjointGroup τ L, ∀ y ∈ adjointGroup τ L,
      (∀ e ∈ Ê, x * e = e * x) → (∀ e ∈ Ê, y * e = e * y) → x * y = y * x)
    (hdec : ∀ c ∈ adjointGroup τ L, (∀ e ∈ Ê, c * e = e * c) →
      ∃ e ∈ Ê, ∃ d : ModGL τ L, (∀ m : ℕ, ∃ c' ∈ adjointGroup τ L,
        (∀ e ∈ Ê, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ c = e * d)
    (h9 : {d : ModGL τ L | (∀ m : ℕ, ∃ c' ∈ adjointGroup τ L,
        (∀ e ∈ Ê, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1}.encard ≤ 9)
    (hEq : Nat.card Ê = 3 ^ 4) :
    {c : ModGL τ L | c ∈ e67Centralizer Ê ∧ c ^ 3 ∈ Ê}.encard ≤ 3 ^ 4 * 9 := by
  let D : Subgroup (ModGL τ L) := powCentralSubgroup Ê (adjointGroup τ L) hcommG
  obtain ⟨hÊC, hDC, hCcomm, hCAD⟩ :=
    e67_centralizer_facts hÊadj hÊea hcommG hdec
  haveI : Finite Ê := (Nat.card_ne_zero.mp (by rw [hEq]; norm_num)).2
  have hcount := CFSG.GroupTheory.encard_pow_mem_le_card_mul_encard
    (C := e67Centralizer Ê) (A := Ê) (D := D) hÊC hDC hCcomm hCAD 3
  have h9' : {d : ModGL τ L | d ∈ D ∧ d ^ 3 = 1}.encard ≤ 9 := by
    simpa [D, powCentralSubgroup] using h9
  rw [hEq] at hcount
  exact hcount.trans (by
    calc (3 ^ 4 : ℕ∞) * {d : ModGL τ L | d ∈ D ∧ d ^ 3 = 1}.encard
        ≤ (3 ^ 4 : ℕ∞) * 9 := mul_le_mul_right h9' _
      _ = (3 ^ 4 * 9 : ℕ) := by push_cast; ring)

private theorem e67_injection_mem {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hH : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)}
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) {E : Subgroup (MulAut K)} {g : H} {t : MulAut R}
    (hgt : Θ g = t) (ht : t ∈ e67T θ E I (e67Ebar θ E)) :
    (g : ModGL τ L) ∈ e67Centralizer (e67Bridge Θ θ E) ∧
      (g : ModGL τ L) ^ 3 ∈ e67Bridge Θ θ E := by
  have hcomm : ∀ u ∈ e67Bridge Θ θ E,
      (g : ModGL τ L) * u = u * (g : ModGL τ L) := by
    intro u hu
    change u ∈ ((e67Ebar θ E).comap Θ).map H.subtype at hu
    obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hu₀)
    have hc : g * u₀ = u₀ * g := by
      apply hΘ
      rw [map_mul, map_mul, hgt, ← heq]
      exact ht.2.1 e he
    exact congrArg H.subtype hc
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change (g : ModGL τ L) ∈ adjointGroup τ L
    exact hH g.2
  · change (g : ModGL τ L) ∈ Subgroup.centralizer
      (e67Bridge Θ θ E : Set (ModGL τ L))
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hcomm u hu).symm
  · have hmap : Θ (g ^ 3) = t ^ 3 := by rw [map_pow, hgt]
    have hmem : g ^ 3 ∈ (e67Ebar θ E).comap Θ := by
      rw [Subgroup.mem_comap, hmap]
      exact ht.2.2
    have hmem' : H.subtype (g ^ 3) ∈ e67Bridge Θ θ E := by
      change H.subtype (g ^ 3) ∈ CFSG.HardMathSupport.C14Exc.bridgeSub Θ (e67Ebar θ E)
      exact CFSG.HardMathSupport.C14Exc.mem_bridgeSub Θ (e67Ebar θ E) (g ^ 3) |>.mpr
        (by simpa using hmem)
    simpa using hmem'

private theorem e67_injection_le_target {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hH : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)}
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R) (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {E : Subgroup (MulAut K)} [Finite (MulAut R)] :
    (Nat.card (e67T θ E I (e67Ebar θ E)) : ℕ∞) ≤
      {c : ModGL τ L | c ∈ e67Centralizer (e67Bridge Θ θ E) ∧
        c ^ 3 ∈ e67Bridge Θ θ E}.encard := by
  have hTfin : (e67T θ E I (e67Ebar θ E)).Finite := Set.toFinite _
  let sec : (t : MulAut R) → t ∈ I → H := fun t ht => Classical.choose ((hI t).mp ht)
  have hsec : ∀ (t : MulAut R) (ht : t ∈ I), Θ (sec t ht) = t :=
    fun t ht => Classical.choose_spec ((hI t).mp ht)
  let F : e67T θ E I (e67Ebar θ E) → ModGL τ L :=
    fun t => H.subtype (sec t.1 t.2.1)
  have hFmem : ∀ t : e67T θ E I (e67Ebar θ E),
      F t ∈ {c : ModGL τ L | c ∈ e67Centralizer (e67Bridge Θ θ E) ∧
        c ^ 3 ∈ e67Bridge Θ θ E} := by
    intro t
    exact e67_injection_mem hH θ Θ hΘ (hsec t.1 t.2.1) t.2
  have hFinj : Function.Injective F := by
    intro t u htu
    apply Subtype.ext
    have h1 : H.subtype (sec t.1 t.2.1) = H.subtype (sec u.1 u.2.1) := htu
    have h2 : sec t.1 t.2.1 = sec u.1 u.2.1 := H.subtype_injective h1
    calc t.1 = Θ (sec t.1 t.2.1) := (hsec t.1 t.2.1).symm
      _ = Θ (sec u.1 u.2.1) := by rw [h2]
      _ = u.1 := hsec u.1 u.2.1
  have hrange : (Set.range F).encard = (Nat.card (e67T θ E I (e67Ebar θ E)) : ℕ∞) := by
    rw [Function.Injective.encard_range hFinj, ENat.card_eq_coe_natCard]
  rw [← hrange]
  have hsub : Set.range F ⊆ {c : ModGL τ L | c ∈ e67Centralizer (e67Bridge Θ θ E) ∧
      c ^ 3 ∈ e67Bridge Θ θ E} := by
    rw [Set.range_subset_iff]
    exact hFmem
  exact Set.encard_le_encard hsub

private theorem e67_injection_bound {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hH : H ≤ adjointGroup τ L)
    {R : Type} [Group R] {I : Set (MulAut R)} {K : Type} [Group K]
    (θ : K ⧸ Subgroup.center K ≃* R) (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {E : Subgroup (MulAut K)} [Finite (MulAut R)]
    (hcount : {c : ModGL τ L | c ∈ e67Centralizer (e67Bridge Θ θ E) ∧
      c ^ 3 ∈ e67Bridge Θ θ E}.encard ≤ 3 ^ 4 * 9) :
    Nat.card (e67T θ E I (e67Ebar θ E)) ≤ 3 ^ 4 * 9 := by
  have hle := e67_injection_le_target hH θ Θ hΘ hI (E := E)
  exact ENat.coe_le_coe.mp (hle.trans hcount)

private theorem e67_piK_bound {τ : Tag} {L : Type} [Field L]
    {H : Subgroup (ModGL τ L)} (hH : H ≤ adjointGroup τ L)
    {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)}
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (Θ : H →* MulAut R) (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E) (hK : commutator K = ⊤)
    (hcommG : ∀ x ∈ adjointGroup τ L, ∀ y ∈ adjointGroup τ L,
      (∀ e ∈ e67Bridge Θ θ E, x * e = e * x) →
      (∀ e ∈ e67Bridge Θ θ E, y * e = e * y) → x * y = y * x) :
    Nat.card E * Nat.card E ≤ 3 * Nat.card (e67T θ E I (e67Ebar θ E)) := by
  have hcommI := e67_commute_of_bridge hH θ Θ hΘ hI hcommG
  have h := ggL45TorusKGHyp_card_mul_card_le (p := 3) hcyc θ hK hKG hcommI
  exact h

private theorem e67_lower_bound {K : Type} [Group K] {R : Type} [Group R]
    {E : Subgroup (MulAut K)} (T : Set (MulAut R))
    (hPiK : Nat.card E * Nat.card E ≤ 3 * Nat.card T)
    (hEcard : Nat.card E = 3 ^ 4) :
    3 ^ 8 ≤ 3 * Nat.card T := by
  calc
    3 ^ 8 = Nat.card E * Nat.card E := by rw [hEcard]; norm_num
    _ ≤ 3 * Nat.card T := hPiK

private theorem e67_contradiction {R : Type} [Group R] (T : Set (MulAut R))
    (hTle : Nat.card T ≤ 3 ^ 4 * 9) (hLow : 3 ^ 8 ≤ 3 * Nat.card T) : False := by
  have h : 3 ^ 8 ≤ 3 * (3 ^ 4 * 9) := hLow.trans (Nat.mul_le_mul_left 3 hTle)
  norm_num at h

private theorem e67_not_three_dvd_card (K₀ : Type) [Field K₀] [Finite K₀] [CharP K₀ 2] :
    ¬ 3 ∣ Nat.card K₀ := by
  intro h3
  haveI := Fintype.ofFinite K₀
  obtain ⟨n, -, hn⟩ := FiniteField.card K₀ 2
  have hcard : Nat.card K₀ = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rw [hcard] at h3
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at h32

private theorem e67_e6_false
    (hB2 : GGL45E6NonToralThreeCent) {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    {H : Subgroup (ModGL .E6 (AlgebraicClosure K₀))}
    (hH : H ≤ adjointGroup .E6 (AlgebraicClosure K₀))
    {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)} (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hK : commutator K = ⊤) {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E) (hE4 : 3 ^ 4 ≤ Nat.card E)
    (hnt : ¬ IsToralSubgroup .E6 (AlgebraicClosure K₀) (e67Bridge Θ θ E)) : False := by
  have hKG' := hKG
  obtain ⟨-, -, hEelem, -, -, hInd, -, -, -, -⟩ := hKG
  obtain ⟨hÊcard, hÊadj, hÊea⟩ := e67Bridge_facts hH Θ hΘ hI θ hK hEelem hInd
  have hnot3 : ¬ 3 ∣ Nat.card K₀ := e67_not_three_dvd_card K₀
  have hlt : Nat.card (e67Bridge Θ θ E) < 3 ^ 5 := by
    by_contra h
    push Not at h
    exact hnt (bigElemAbelianToralBar_E6_three (K := K₀) hnot3 _
      hÊadj (fun x hx y hy => hÊea.comm hx hy) hÊea.2 h)
  obtain ⟨k, hk⟩ := hEelem.isPGroup.exists_card_eq
  have hk4 : 4 ≤ k :=
    (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 3)).1 (by rw [← hk]; exact hE4)
  have hk5 : k < 5 := by
    have h : 3 ^ k < 3 ^ 5 := by rw [← hk, ← hÊcard]; exact hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : (1 : ℕ) < 3)).mp h
  have hEq : Nat.card (e67Bridge Θ θ E) = 3 ^ 4 := by
    rw [hÊcard, hk]
    congr 1
    omega
  obtain ⟨hcommG, hdec, h9⟩ := hB2 K₀ (e67Bridge Θ θ E) hÊadj hÊea hnt hEq
  have hcount := e67_count_centralizer hÊadj hÊea hcommG hdec h9 hEq
  haveI : Finite (MulAut R) := e67_finite_mulAut θ
  have hTle := e67_injection_bound hH θ Θ hΘ hI hcount
  have hPiK := e67_piK_bound hH θ Θ hΘ hI hcyc hKG' hK hcommG
  have hEcard : Nat.card E = 3 ^ 4 := by rw [← hÊcard]; exact hEq
  exact e67_contradiction _ hTle (e67_lower_bound _ hPiK hEcard)

private theorem e67_e7_false
    {K₀ : Type} [Field K₀] [Finite K₀] [CharP K₀ 2]
    {H : Subgroup (ModGL .E7 (AlgebraicClosure K₀))}
    (hH : H ≤ adjointGroup .E7 (AlgebraicClosure K₀))
    {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)} (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    {K : Type} [Group K] (θ : K ⧸ Subgroup.center K ≃* R)
    (hK : commutator K = ⊤) {ψ : MulAut K} {E : Subgroup (MulAut K)}
    (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E) (hE7 : 3 ^ 6 ≤ Nat.card E)
    (hnt : ¬ IsToralSubgroup .E7 (AlgebraicClosure K₀) (e67Bridge Θ θ E)) : False := by
  obtain ⟨-, -, hEelem, -, -, hInd, -, -, -, -⟩ := hKG
  obtain ⟨hÊcard, hÊadj, hÊea⟩ := e67Bridge_facts hH Θ hΘ hI θ hK hEelem hInd
  have hnot3 : ¬ 3 ∣ Nat.card K₀ := e67_not_three_dvd_card K₀
  have hÊ7 : 3 ^ 6 ≤ Nat.card (e67Bridge Θ θ E) := by rw [hÊcard]; exact hE7
  exact hnt (bigElemAbelianToralBar_E7_three (K := K₀) hnot3 _
    hÊadj (fun x hx y hy => hÊea.comm hx hy) hÊea.2 hÊ7)

theorem ggL45E67_isToralSubgroup
    (hB2 : GGL45E6NonToralThreeCent) {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7) {K₀ : Type} [Field K₀]
    [Finite K₀] [CharP K₀ 2] {H : Subgroup (ModGL τ (AlgebraicClosure K₀))}
    (hH : H ≤ adjointGroup τ (AlgebraicClosure K₀))
    {lab : LargeEvenLabel} {R : Type} [Group R] {I F : Set (MulAut R)} (Θ : H →* MulAut R)
    (hΘ : Function.Injective Θ) (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hcyc : ∃ J S : Subgroup (MulAut R), (J : Set (MulAut R)) = I ∧ J ≤ S ∧
      (J.subgroupOf S).Normal ∧ (∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) ∧
      ∀ α : MulAut R, (∃ k : ℕ, α ^ 3 ^ k = 1) → α ∈ S)
    {K : Type} [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R) (hK : commutator K = ⊤)
    {ψ : MulAut K} {E : Subgroup (MulAut K)} (hKG : GGL45TorusKGHyp 3 lab I F θ ψ E)
    (hE4 : 3 ^ 4 ≤ Nat.card E) (hE7 : τ = .E7 → 3 ^ 6 ≤ Nat.card E) :
    IsToralSubgroup τ (AlgebraicClosure K₀)
      (((E.map (ggInducedAut θ)).comap Θ).map H.subtype) := by
  classical
  by_contra hnt
  change ¬ IsToralSubgroup τ (AlgebraicClosure K₀) (e67Bridge Θ θ E) at hnt
  rcases hτ with hτE6 | hτE7
  · subst hτE6
    exact e67_e6_false hB2 hH Θ hΘ hI hcyc θ hK hKG hE4 hnt
  · have hE7' : 3 ^ 6 ≤ Nat.card E := hE7 hτE7
    subst hτE7
    exact e67_e7_false hH Θ hΘ hI θ hK hKG hE7' hnt

end CFSG.StandardType
