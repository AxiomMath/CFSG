module

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup

public section

namespace CFSG.Quasithin.H13.NQTerm

open CFSG Subgroup
open scoped commutatorElement

variable {E : Type} [Group E]

@[expose] def centerQuotientDerivedPreimage (S : Subgroup (E ⧸ center E)) : Subgroup E :=
  ⁅S.comap (QuotientGroup.mk' (center E)), S.comap (QuotientGroup.mk' (center E))⁆

theorem commutatorElement_center_mul_left {c : E} (hc : c ∈ center E) (a y : E) :
    ⁅c * a, y⁆ = ⁅a, y⁆ := by
  have h := mem_center_iff.mp hc
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have e : c * a * y * (a⁻¹ * c⁻¹) = a * y * a⁻¹ := by
    calc c * a * y * (a⁻¹ * c⁻¹) = c * (a * y * a⁻¹) * c⁻¹ := by group
      _ = (a * y * a⁻¹) * c * c⁻¹ := by rw [← h (a * y * a⁻¹)]
      _ = a * y * a⁻¹ := by group
  rw [e]

theorem commutatorElement_mul_center_right {d : E} (hd : d ∈ center E) (a b : E) :
    ⁅a, d * b⁆ = ⁅a, b⁆ := by
  have h := mem_center_iff.mp hd
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  have e : a * (d * b) * a⁻¹ * (b⁻¹ * d⁻¹) = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by
    calc a * (d * b) * a⁻¹ * (b⁻¹ * d⁻¹) = (a * d) * b * a⁻¹ * b⁻¹ * d⁻¹ := by group
      _ = (d * a) * b * a⁻¹ * b⁻¹ * d⁻¹ := by rw [h a]
      _ = d * (a * b * a⁻¹ * b⁻¹) * d⁻¹ := by group
  rw [e, ← h (a * b * a⁻¹ * b⁻¹)]
  group

theorem commute_derived_of_commutator_le_center {P Q : Subgroup E}
    (hPQ : ⁅P, Q⁆ ≤ center E) {x : E} (hx : x ∈ P) {y : E} (hy : y ∈ ⁅Q, Q⁆) :
    x * y = y * x := by
  have hle : ⁅Q, Q⁆ ≤ centralizer {x} := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    have hc := hPQ (Subgroup.commutator_mem_commutator hx ha)
    have hd := hPQ (Subgroup.commutator_mem_commutator hx hb)
    have hxa : x * a * x⁻¹ = ⁅x, a⁆ * a := by rw [commutatorElement_def]; group
    have hxb : x * b * x⁻¹ = ⁅x, b⁆ * b := by rw [commutatorElement_def]; group
    have key : x * ⁅a, b⁆ * x⁻¹ = ⁅a, b⁆ := by
      have e1 : x * ⁅a, b⁆ * x⁻¹ = ⁅x * a * x⁻¹, x * b * x⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [e1, hxa, hxb, commutatorElement_center_mul_left hc,
        commutatorElement_mul_center_right hd]
    calc x * ⁅a, b⁆ = x * ⁅a, b⁆ * x⁻¹ * x := by group
      _ = ⁅a, b⁆ * x := by rw [key]
  exact mem_centralizer_iff.mp (hle hy) x rfl

theorem add_le_pRank_of_commute [Finite E] {p : ℕ} (hp : p.Prime) {A B : Subgroup E}
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hBp : ∀ x ∈ B, x ^ p = 1)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) (hinf : A ⊓ B = ⊥) {a b : ℕ}
    (ha : Nat.card A = p ^ a) (hb : Nat.card B = p ^ b) : a + b ≤ CFSG.pRank p E := by
  let f : A × B →* E :=
    MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hAB x x.2 y y.2
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    change (x : E) * y = 1 at hxy
    have hx : (x : E) ∈ A ⊓ B := by
      refine ⟨x.2, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hxy]
      exact B.inv_mem y.2
    rw [hinf, mem_bot] at hx
    have hy : (y : E) = 1 := by rw [hx, one_mul] at hxy; exact hxy
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.le_pRank_of_injective hp.one_lt (fun u v => ?_) (fun u => ?_) ?_ f hf
    le_top
  · exact Prod.ext (Subtype.ext (hAc _ u.1.2 _ v.1.2)) (Subtype.ext (hBc _ u.2.2 _ v.2.2))
  · exact Prod.ext (Subtype.ext (by simpa using hAp _ u.1.2))
      (Subtype.ext (by simpa using hBp _ u.2.2))
  · rw [Nat.card_prod, ha, hb, pow_add]

theorem map_centerQuotientDerivedPreimage (S : Subgroup (E ⧸ center E)) (hS : ⁅S, S⁆ = S) :
    (centerQuotientDerivedPreimage S).map (QuotientGroup.mk' (center E)) = S := by
  rw [centerQuotientDerivedPreimage, Subgroup.map_commutator,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _), hS]

theorem commutator_self_le (H : Subgroup E) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

@[expose] def centerQuotientDerivedRestrict (S : Subgroup (E ⧸ center E)) :
    centerQuotientDerivedPreimage S →* S :=
  ((QuotientGroup.mk' (center E)).comp (centerQuotientDerivedPreimage S).subtype).codRestrict S
    fun x => (commutator_self_le _ x.2 : (x : E) ∈ S.comap (QuotientGroup.mk' _))

theorem centerQuotientDerivedPreimage_facts (S : Subgroup (E ⧸ center E)) [S.Normal]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) :
    (centerQuotientDerivedPreimage S).map (QuotientGroup.mk' (center E)) = S ∧
    S.comap (QuotientGroup.mk' (center E)) = centerQuotientDerivedPreimage S ⊔ center E ∧
    (centerQuotientDerivedPreimage S).Normal ∧
    CFSG.IsQuasisimple (centerQuotientDerivedPreimage S) ∧
    Function.Surjective (centerQuotientDerivedRestrict S) ∧
    (∀ x : centerQuotientDerivedPreimage S,
      x ∈ center (centerQuotientDerivedPreimage S) ↔ (x : E) ∈ center E) := by
  set π := QuotientGroup.mk' (center E) with hπ
  set D := centerQuotientDerivedPreimage S with hD
  set P := S.comap π with hP
  obtain ⟨hSq, hSZ⟩ := LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hSperf : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hSq.1
  have hmap : D.map π = S := map_centerQuotientDerivedPreimage S hSperf
  have hPD : P = D ⊔ center E := by
    rw [hP, ← hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hPn : P.Normal := Subgroup.Normal.comap inferInstance π
  have hDn : D.Normal := by
    rw [hD, centerQuotientDerivedPreimage]
    infer_instance
  have hDperf : ⁅D, D⁆ = D := by
    have hC : ∀ X : Subgroup E, ⁅center E, X⁆ = ⊥ := fun X =>
      (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
        (fun z hz => mem_centralizer_iff.mpr fun x _ => mem_center_iff.mp hz x)
    have hC' : ∀ X : Subgroup E, ⁅X, center E⁆ = ⊥ := fun X => by
      rw [Subgroup.commutator_comm]; exact hC X
    have : (D ⊔ center E).Normal := inferInstance
    have e : ⁅D ⊔ center E, D ⊔ center E⁆ = ⁅D, D⁆ := by
      rw [Subgroup.commutator_sup_right, hC, sup_bot_eq, Subgroup.commutator_sup_left, hC',
        sup_bot_eq]
    rw [← e, ← hPD, hP, hD]
    rfl
  have hDP : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDperf
  set f := centerQuotientDerivedRestrict S with hf
  have hfx : ∀ x : D, ((f x : S) : E ⧸ center E) = π x := fun _ => rfl
  have hfs : Function.Surjective f := by
    rintro ⟨s, hs⟩
    rw [← hmap] at hs
    obtain ⟨x, hx, rfl⟩ := hs
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfker : ∀ x : D, f x = 1 ↔ (x : E) ∈ center E := by
    intro x
    rw [Subtype.ext_iff, hfx, Subgroup.coe_one, hπ, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff _
  have hkerc : f.ker ≤ center D := by
    intro x hx
    rw [MonoidHom.mem_ker, hfker] at hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y)
  have hDq : CFSG.IsQuasisimple D :=
    (LocalCores.isQuasisimple_iff_of_surjective hDP f hfs hkerc).mpr hSq
  refine ⟨hmap, hPD, hDn, hDq, hfs, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  ·
    have hc : f x ∈ center S := mem_center_iff.mpr fun s => by
      obtain ⟨y, rfl⟩ := hfs s
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx y]
    rw [hSZ, mem_bot] at hc
    exact (hfker x).mp hc
  · exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hx y)

theorem three_le_pRank_of_commute [Finite E] {p : ℕ} (hp : p.Prime) {D D' A : Subgroup E}
    (hDD' : ∀ a ∈ D, ∀ b ∈ D', a * b = b * a) (hAD : A ≤ D)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hA : Nat.card A = p ^ 2) {x : E} (hxD' : x ∈ D') (hxD : x ∉ D) (hx : orderOf x = p) :
    3 ≤ CFSG.pRank p E := by
  have : Fact p.Prime := ⟨hp⟩
  set X := zpowers x with hXdef
  have hXcard : Nat.card X = p ^ 1 := by rw [Nat.card_zpowers, hx, pow_one]
  have hXD' : X ≤ D' := (zpowers_le).mpr hxD'
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
    rw [← zpow_add, ← zpow_add, add_comm]
  have hXp : ∀ a ∈ X, a ^ p = 1 := fun a ha => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
      one_zpow]
  have hinf : A ⊓ X = ⊥ := by
    have : Fact (Nat.card X).Prime := ⟨by rw [hXcard, pow_one]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((A ⊓ X).subgroupOf X) with h | h
    · rw [eq_bot_iff]
      intro y hy
      have : (⟨y, hy.2⟩ : X) ∈ (A ⊓ X).subgroupOf X := by
        rw [mem_subgroupOf]; exact hy
      rw [h, mem_bot] at this
      rw [mem_bot]
      exact congrArg Subtype.val this
    · exfalso
      have hmem : (⟨x, mem_zpowers x⟩ : X) ∈ (A ⊓ X).subgroupOf X := by
        rw [h]; exact mem_top _
      rw [mem_subgroupOf] at hmem
      exact hxD (hAD hmem.1)
  have h := add_le_pRank_of_commute hp hAc hAp hXc hXp
    (fun a ha b hb => hDD' a (hAD ha) b (hXD' hb)) hinf hA hXcard
  omega

theorem isElemAbelian_map_subtype {p : ℕ} {D : Subgroup E} {A : Subgroup D}
    (hA : CFSG.Open.IsElemAbelian p A) :
    (∀ x ∈ A.map D.subtype, ∀ y ∈ A.map D.subtype, x * y = y * x) ∧
      (∀ x ∈ A.map D.subtype, x ^ p = 1) ∧ Nat.card (A.map D.subtype) = Nat.card A := by
  obtain ⟨hc, hp⟩ := hA
  refine ⟨?_, ?_, Subgroup.card_map_of_injective D.subtype_injective⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    exact congrArg Subtype.val this
  · rintro _ ⟨a, ha, rfl⟩
    have := hp a ha
    change ((a : E)) ^ p = 1
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]

theorem pRank_three_le_one_of_card {Z : Type*} [Group Z] [Finite Z]
    (h : Nat.card Z = 1 ∨ Nat.card Z = 3) : CFSG.pRank 3 Z ≤ 1 := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine CFSG.SectionRank.pRank_le (by norm_num) fun F _ _ => ?_
  have h1 : Nat.card F ≤ Nat.card Z := Subgroup.card_le_card_group F
  rcases h with h | h <;> rw [h] at h1 <;> omega

theorem card_center_centerQuotientDerivedPreimage_dvd [Finite E] (S : Subgroup (E ⧸ center E))
    (hZ : ∀ x : centerQuotientDerivedPreimage S,
      x ∈ center (centerQuotientDerivedPreimage S) ↔ (x : E) ∈ center E) :
    Nat.card (center (centerQuotientDerivedPreimage S)) ∣ Nat.card (center E) := by
  let f : center (centerQuotientDerivedPreimage S) →* center E :=
    { toFun := fun x => ⟨((x : centerQuotientDerivedPreimage S) : E), (hZ x).mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Subgroup.card_dvd_of_injective f fun x y h => ?_
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : center E => (z : E)) h

theorem three_le_pRank_of_card_center_eq_three [Finite E] {D D' : Subgroup E}
    {S S' : Subgroup (E ⧸ center E)} (hDq : CFSG.IsQuasisimple D) (hD'q : CFSG.IsQuasisimple D')
    (hmap : D.map (QuotientGroup.mk' (center E)) = S)
    (hmap' : D'.map (QuotientGroup.mk' (center E)) = S')
    (hZ : ∀ x : D, x ∈ center D ↔ (x : E) ∈ center E)
    (hcomm : ∀ x ∈ D, ∀ y ∈ D', x * y = y * x) (hcard : Nat.card S = Nat.card S')
    (h3 : Nat.card (center D) = 3)
    (h3' : Nat.card (center D') = 1 ∨ Nat.card (center D') = 3) : 3 ≤ CFSG.pRank 3 E := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect D := hDq.1
  have : Group.IsPerfect D' := hD'q.1
  set π := QuotientGroup.mk' (center E) with hπ
  have h3D : 3 ∣ Nat.card D := h3 ▸ Subgroup.card_subgroup_dvd_card (center D)
  have hA := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := D) (p := 3)
    (by norm_num) h3D).2 (by rw [h3])
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hA
  obtain ⟨A, -, hAel, hAcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hA
  obtain ⟨hAc, hAp, hAcard'⟩ := isElemAbelian_map_subtype hAel
  obtain ⟨g, hg, hgZ⟩ := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := D) (p := 3)
    (by norm_num) h3D).1 (pRank_three_le_one_of_card (Or.inr h3))
  have hπg : π g ∈ S := hmap ▸ Subgroup.mem_map_of_mem π g.2
  have hπg1 : π g ≠ 1 := fun h1 => hgZ ((hZ g).mpr ((QuotientGroup.eq_one_iff _).mp h1))
  have hordg : orderOf (π g) = 3 := by
    have hdvd : orderOf (π g) ∣ 3 := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact orderOf_map_dvd π _
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hπg1
    · exact h
  have h3S : 3 ∣ Nat.card S := by
    have := orderOf_dvd_natCard (⟨π g, hπg⟩ : S)
    rwa [Subgroup.orderOf_mk, hordg] at this
  have h3D' : 3 ∣ Nat.card D' := by
    rw [hcard, ← hmap'] at h3S
    exact h3S.trans (Subgroup.card_map_dvd _ _)
  obtain ⟨x, hx, hxZ⟩ := (CFSG.SectionRank.perfect_cyclic_center_odd_elements (L := D') (p := 3)
    (by norm_num) h3D').1 (pRank_three_le_one_of_card h3')
  have hxD : (x : E) ∉ D := fun hxD => hxZ (mem_center_iff.mpr fun y => Subtype.ext
    (hcomm x hxD y y.2).symm)
  exact three_le_pRank_of_commute Nat.prime_three hcomm (Subgroup.map_subtype_le A) hAc hAp
    (by rw [hAcard', hAcard]) x.2 hxD (by rw [Subgroup.orderOf_coe, hx])

theorem sqtk_perfect_odd_central_isotypic_pair_is_centerless
    [Finite E] [Group.IsPerfect E]
    (hE : SectionRank.IsSQTKCat E) (hC : Odd (Nat.card (center E)))
    (S₁ S₂ : Subgroup (E ⧸ center E)) [S₁.Normal] [S₂.Normal]
    (hinf : S₁ ⊓ S₂ = ⊥) (hsup : S₁ ⊔ S₂ = ⊤) [IsSimpleGroup S₁] [IsSimpleGroup S₂]
    (hnab₁ : ∃ a b : S₁, a * b ≠ b * a) (hnab₂ : ∃ a b : S₂, a * b ≠ b * a)
    (hiso : Nonempty (S₁ ≃* S₂)) :
    center E = ⊥ ∧
    (centerQuotientDerivedPreimage S₁ ⊓ centerQuotientDerivedPreimage S₂ = ⊥ ∧
      centerQuotientDerivedPreimage S₁ ⊔ centerQuotientDerivedPreimage S₂ = ⊤ ∧
      ∀ x ∈ centerQuotientDerivedPreimage S₁, ∀ y ∈ centerQuotientDerivedPreimage S₂,
        x * y = y * x) ∧
    ((centerQuotientDerivedPreimage S₁).map (QuotientGroup.mk' (center E)) = S₁ ∧
      Set.InjOn (QuotientGroup.mk' (center E)) (centerQuotientDerivedPreimage S₁)) ∧
    ((centerQuotientDerivedPreimage S₂).map (QuotientGroup.mk' (center E)) = S₂ ∧
      Set.InjOn (QuotientGroup.mk' (center E)) (centerQuotientDerivedPreimage S₂)) ∧
    (∀ p : ℕ, p.Prime → p ≠ 2 →
      (∀ P : Sylow p (centerQuotientDerivedPreimage S₁), IsCyclic P) ∧
      ∀ P : Sylow p (centerQuotientDerivedPreimage S₂), IsCyclic P) ∧
    4 ≤ CFSG.pRank 2 E := by
  classical
  set π := QuotientGroup.mk' (center E) with hπ
  set D₁ := centerQuotientDerivedPreimage S₁ with hD₁
  set D₂ := centerQuotientDerivedPreimage S₂ with hD₂
  obtain ⟨hmap₁, -, hD₁n, hD₁q, -, hZ₁⟩ := centerQuotientDerivedPreimage_facts S₁ hnab₁
  obtain ⟨hmap₂, -, hD₂n, hD₂q, -, hZ₂⟩ := centerQuotientDerivedPreimage_facts S₂ hnab₂
  have hSQT : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.pRank q E ≤ 2 := hE.1
  have hP12 : ⁅S₁.comap π, S₂.comap π⁆ ≤ center E := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h1 : π ⁅x, y⁆ ∈ S₁ ⊓ S₂ := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_le_inf S₁ S₂
        (Subgroup.commutator_mem_commutator (Subgroup.mem_comap.mp hx) (Subgroup.mem_comap.mp hy))
    rw [hinf, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x := fun x hx y hy =>
    commute_derived_of_commutator_le_center hP12 (commutator_self_le _ hx) hy
  have hcomm' : ∀ x ∈ D₂, ∀ y ∈ D₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hsupD : D₁ ⊔ D₂ = ⊤ := by
    have h1 : (D₁ ⊔ D₂) ⊔ center E = ⊤ := by
      rw [← QuotientGroup.ker_mk' (center E), ← Subgroup.comap_map_eq, Subgroup.map_sup,
        ← hπ, hmap₁, hmap₂, hsup, Subgroup.comap_top]
    have hZc : IsMulCommutative (center E) :=
      ⟨⟨fun a b => Subtype.ext (mem_center_iff.mp b.2 a)⟩⟩
    have := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top h1 hZc
    rw [Group.isPerfect_def.mp inferInstance] at this
    exact top_le_iff.mp this
  have hcen : ∀ z ∈ center E, ∃ d₁ ∈ D₁, ∃ d₂ ∈ D₂, (d₁ ∈ center E ∧ d₂ ∈ center E) ∧
      d₁ * d₂ = z := by
    intro z hz
    have hz' : z ∈ ((D₁ ⊔ D₂ : Subgroup E) : Set E) := by rw [hsupD]; exact mem_top z
    rw [Subgroup.normal_mul] at hz'
    obtain ⟨d₁, hd₁, d₂, hd₂, hzd⟩ := hz'
    have hzd' : d₁ * d₂ = z := hzd
    subst hzd'
    have hzc := mem_center_iff.mp hz
    refine ⟨d₁, hd₁, d₂, hd₂, ⟨(hZ₁ ⟨d₁, hd₁⟩).mp ?_, (hZ₂ ⟨d₂, hd₂⟩).mp ?_⟩, rfl⟩
    · refine mem_center_iff.mpr fun x => Subtype.ext ?_
      have h1 : (x : E) * (d₁ * d₂) = d₁ * d₂ * x := hzc x
      have h2 := hcomm x x.2 d₂ hd₂
      change (x : E) * d₁ = d₁ * x
      have : (x : E) * d₁ * d₂ = d₁ * x * d₂ := by
        calc (x : E) * d₁ * d₂ = x * (d₁ * d₂) := mul_assoc _ _ _
          _ = d₁ * d₂ * x := h1
          _ = d₁ * (d₂ * x) := mul_assoc _ _ _
          _ = d₁ * (x * d₂) := by rw [h2]
          _ = d₁ * x * d₂ := (mul_assoc _ _ _).symm
      exact mul_right_cancel this
    · refine mem_center_iff.mpr fun x => Subtype.ext ?_
      have h1 : (x : E) * (d₁ * d₂) = d₁ * d₂ * x := hzc x
      have h2 := hcomm d₁ hd₁ x x.2
      change (x : E) * d₂ = d₂ * x
      have : d₁ * (x * d₂) = d₁ * (d₂ * x) := by
        calc d₁ * (x * d₂) = d₁ * x * d₂ := (mul_assoc _ _ _).symm
          _ = x * d₁ * d₂ := by rw [h2]
          _ = x * (d₁ * d₂) := mul_assoc _ _ _
          _ = d₁ * d₂ * x := h1
          _ = d₁ * (d₂ * x) := mul_assoc _ _ _
      exact mul_left_cancel this
  have hZ₁odd : Odd (Nat.card (center D₁)) :=
    Odd.of_dvd_nat hC (card_center_centerQuotientDerivedPreimage_dvd S₁ hZ₁)
  have hZ₂odd : Odd (Nat.card (center D₂)) :=
    Odd.of_dvd_nat hC (card_center_centerQuotientDerivedPreimage_dvd S₂ hZ₂)
  have hcat₁ := (CFSG.SectionRank.catalogStepHyp D₁ hD₁q (hE.subgroup D₁) hZ₁odd).1
  have hcat₂ := (CFSG.SectionRank.catalogStepHyp D₂ hD₂q (hE.subgroup D₂) hZ₂odd).1
  obtain ⟨e₁₂⟩ := hiso
  have hcardS : Nat.card S₁ = Nat.card S₂ := Nat.card_congr e₁₂.toEquiv
  have hZ₁1 : Nat.card (center D₁) = 1 := by
    rcases hcat₁ with h | h
    · exact h
    · have := three_le_pRank_of_card_center_eq_three hD₁q hD₂q hmap₁ hmap₂ hZ₁ hcomm
        hcardS h hcat₂
      have := hSQT 3 Nat.prime_three (by norm_num)
      omega
  have hZ₂1 : Nat.card (center D₂) = 1 := by
    rcases hcat₂ with h | h
    · exact h
    · have := three_le_pRank_of_card_center_eq_three hD₂q hD₁q hmap₂ hmap₁ hZ₂ hcomm'
        hcardS.symm h hcat₁
      have := hSQT 3 Nat.prime_three (by norm_num)
      omega
  have hZ₁b : center D₁ = ⊥ := Subgroup.card_eq_one.mp hZ₁1
  have hZ₂b : center D₂ = ⊥ := Subgroup.card_eq_one.mp hZ₂1
  have hCb : center E = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨d₁, hd₁, d₂, hd₂, ⟨hd₁c, hd₂c⟩, rfl⟩ := hcen z hz
    have h1 : (⟨d₁, hd₁⟩ : D₁) ∈ center D₁ := (hZ₁ _).mpr hd₁c
    have h2 : (⟨d₂, hd₂⟩ : D₂) ∈ center D₂ := (hZ₂ _).mpr hd₂c
    rw [hZ₁b, mem_bot] at h1
    rw [hZ₂b, mem_bot] at h2
    rw [mem_bot, show d₁ = 1 from congrArg Subtype.val h1, show d₂ = 1 from congrArg Subtype.val h2,
      one_mul]
  have hinfD : D₁ ⊓ D₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx.2⟩ : D₂) ∈ center D₂ := mem_center_iff.mpr fun y => Subtype.ext
      (hcomm x hx.1 y y.2).symm
    rw [hZ₂b, mem_bot] at h1
    rw [mem_bot]
    exact congrArg Subtype.val h1
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk']
    exact hCb
  have hcardD : Nat.card D₁ = Nat.card D₂ := by
    rw [← Subgroup.card_map_of_injective hπinj, hmap₁, hcardS, ← hmap₂,
      Subgroup.card_map_of_injective hπinj]
  have hrank : ∀ {X Y : Subgroup E}, (∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) → X ⊓ Y = ⊥ →
      Nat.card X = Nat.card Y → ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.pRank p X ≤ 1 := by
    intro X Y hXY hXYb hXYc p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    by_contra hlt
    have h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]; omega
    obtain ⟨A, -, hAel, hAcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank h2
    obtain ⟨hAc, hAp, hAcard'⟩ := isElemAbelian_map_subtype hAel
    have hpY : p ∣ Nat.card Y := by
      rw [← hXYc]
      exact (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans
        (hAcard ▸ Subgroup.card_subgroup_dvd_card A)
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpY
    have hyX : (y : E) ∉ X := fun hyX => by
      have : (y : E) ∈ X ⊓ Y := ⟨hyX, y.2⟩
      rw [hXYb, mem_bot] at this
      have h1 : y = 1 := Subtype.ext this
      rw [h1, orderOf_one] at hy
      exact hp.one_lt.ne' hy.symm
    have := three_le_pRank_of_commute hp hXY (Subgroup.map_subtype_le A) hAc hAp
      (by rw [hAcard', hAcard]) y.2 hyX (by rw [Subgroup.orderOf_coe, hy])
    have := hSQT p hp hp2
    omega
  have hcyc : ∀ {X : Subgroup E} {p : ℕ}, p.Prime → p ≠ 2 → CFSG.pRank p X ≤ 1 →
      ∀ P : Sylow p X, IsCyclic P := by
    intro X p hp hp2 hX P
    have : Fact p.Prime := ⟨hp⟩
    have hPr : CFSG.pRank p P ≤ 1 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hX ⊢
      exact (CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt (P : Subgroup X).subtype
        (P : Subgroup X).subtype_injective).trans hX
    rcases (LocalAnalysis.ComponentInitial.pgroup_rank_one_classification hp P.isPGroup').mp hPr
      with h | ⟨h, -⟩
    · exact h
    · exact absurd h hp2
  refine ⟨hCb, ⟨hinfD, hsupD, hcomm⟩, ⟨hmap₁, hπinj.injOn⟩, ⟨hmap₂, hπinj.injOn⟩,
    fun p hp hp2 => ⟨hcyc hp hp2 (hrank hcomm hinfD hcardD p hp hp2),
      hcyc hp hp2 (hrank hcomm' (by rw [inf_comm]; exact hinfD) hcardD.symm p hp hp2)⟩, ?_⟩
  have hodd1 : Odd (Nat.card (center D₁)) := by rw [hZ₁1]; exact odd_one
  have hodd2 : Odd (Nat.card (center D₂)) := by rw [hZ₂1]; exact odd_one
  obtain ⟨A₁, hA₁el, hA₁c⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hD₁q hodd1)
  obtain ⟨A₂, hA₂el, hA₂c⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank
    (LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hD₂q hodd2)
  obtain ⟨h1c, h1p, h1card⟩ := isElemAbelian_map_subtype hA₁el
  obtain ⟨h2c, h2p, h2card⟩ := isElemAbelian_map_subtype hA₂el
  have hinfA : A₁.map D₁.subtype ⊓ A₂.map D₂.subtype = ⊥ :=
    le_bot_iff.mp (hinfD ▸ inf_le_inf (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _))
  have := add_le_pRank_of_commute Nat.prime_two h1c h1p h2c h2p
    (fun x hx y hy => hcomm x (Subgroup.map_subtype_le _ hx) y (Subgroup.map_subtype_le _ hy))
    hinfA (a := 2) (b := 2) (by rw [h1card, hA₁c]; norm_num) (by rw [h2card, hA₂c]; norm_num)
  omega

end CFSG.Quasithin.H13.NQTerm
