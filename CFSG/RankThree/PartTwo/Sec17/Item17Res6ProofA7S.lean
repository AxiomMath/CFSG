module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res6ProofA7
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 Equiv
open CFSG.RankThree.PartTwo.KFacts.KP2

theorem vOneF_trans : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
    ∃ i : Fin 3, cTwo ^ (i : ℕ) * vOneF m * (cTwo ^ (i : ℕ))⁻¹ = vOneF n := by
  decide +kernel

theorem vTwoF_trans : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
    ∃ i : Fin 3, cOne ^ (i : ℕ) * vTwoF m * (cOne ^ (i : ℕ))⁻¹ = vTwoF n := by
  decide +kernel

theorem vOneF_eq_vTwoF : ∀ m n : Fin 4, vOneF m = vTwoF n → m = 0 := by
  decide +kernel

theorem eNineF_conj_vF : ∀ (i j : Fin 3) (m : Fin 4),
    (∃ n : Fin 4, eNineF i j * vOneF m * (eNineF i j)⁻¹ = vOneF n) ∧
    (∃ n : Fin 4, eNineF i j * vTwoF m * (eNineF i j)⁻¹ = vTwoF n) := by
  decide +kernel

theorem cOne_mul_cTwo : cOne * cTwo = cTwo * cOne := by
  decide +kernel

theorem vF_ne_one : vOneF 1 ≠ 1 ∧ vTwoF 1 ≠ 1 := by
  decide +kernel

theorem isPGroup_vOne : IsPGroup 2 vOne := by
  rintro ⟨x, m, rfl⟩
  exact ⟨1, Subtype.ext (by simpa using vOneF_sq m)⟩

theorem isPGroup_vTwo : IsPGroup 2 vTwo := by
  rintro ⟨x, m, rfl⟩
  exact ⟨1, Subtype.ext (by simpa using vTwoF_sq m)⟩

theorem eNine_conj_mem_vOne {x v : Perm (Fin 7)} (hx : x ∈ eNine) (hv : v ∈ vOne) :
    x * v * x⁻¹ ∈ vOne := by
  obtain ⟨i, j, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hv
  obtain ⟨n, hn⟩ := (eNineF_conj_vF i j m).1
  exact ⟨n, hn⟩

theorem eNine_conj_mem_vTwo {x v : Perm (Fin 7)} (hx : x ∈ eNine) (hv : v ∈ vTwo) :
    x * v * x⁻¹ ∈ vTwo := by
  obtain ⟨i, j, rfl⟩ := hx
  obtain ⟨m, rfl⟩ := hv
  obtain ⟨n, hn⟩ := (eNineF_conj_vF i j m).2
  exact ⟨n, hn⟩

theorem vF_irreducible {R K : Subgroup (Perm (Fin 7))} (hK : K = vOne ∨ K = vTwo)
    (hRK : R ≤ K) (hE : eNine ≤ Subgroup.normalizer (R : Set (Perm (Fin 7))))
    (hR : R ≠ ⊥) : R = K := by
  obtain ⟨⟨r, hrR⟩, hr1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hR
  have hr1 : r ≠ 1 := fun h1 => hr1' (Subtype.ext h1)
  have hconj : ∀ x ∈ eNine, ∀ y ∈ R, x * y * x⁻¹ ∈ R := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hE hx) y).mp hy
  refine le_antisymm hRK ?_
  rcases hK with rfl | rfl
  · obtain ⟨m, hm⟩ := hRK hrR
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hr1 (by rw [hm]; rfl)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      exact R.one_mem
    obtain ⟨i, hi⟩ := vOneF_trans m n hm0 hn
    rw [← hi, ← hm]
    exact hconj _ (pow_mem cTwo_mem_eNine i) _ hrR
  · obtain ⟨m, hm⟩ := hRK hrR
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hr1 (by rw [hm]; rfl)
    rintro _ ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst hn
      exact R.one_mem
    obtain ⟨i, hi⟩ := vTwoF_trans m n hm0 hn
    rw [← hi, ← hm]
    exact hconj _ (pow_mem cOne_mem_eNine i) _ hrR

variable {G : Type} [Group G] [Finite G] {A L Y₀ : Subgroup G}
  {φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7)} {g : Perm (Fin 7)}

theorem le_normalizer_of_conj' {X : Type*} [Group X] {B K : Subgroup X}
    (h : ∀ b ∈ B, ∀ y ∈ K, b * y * b⁻¹ ∈ K) : B ≤ Subgroup.normalizer (K : Set X) := by
  intro b hb
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨h b hb y, fun hy => ?_⟩
  have := h b⁻¹ (inv_mem hb) _ hy
  rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at this

omit [Finite G] in
theorem eNine_le_normalizer_cimgSeven (hP : A7Pic A L Y₀ φ g) {X : Subgroup G}
    (hAX : A ⊓ L ≤ Subgroup.normalizer (X : Set G)) :
    eNine ≤ Subgroup.normalizer (cimgSeven Y₀ φ g X : Set (Perm (Fin 7))) := by
  refine le_normalizer_of_conj' fun x hx z hz => ?_
  obtain ⟨a, ha, rfl⟩ := hP.surj x hx
  obtain ⟨y, hy, rfl⟩ := mem_cimgSeven.mp hz
  refine mem_cimgSeven.mpr ⟨a * y * a⁻¹, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp (hAX ha) (y : G)).mp hy
    simpa using this
  · rw [map_mul, map_mul, map_inv]
    group

@[expose] noncomputable def preSeven (Y₀ : Subgroup G)
    (φ : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ ≃* alternatingGroup (Fin 7)) (g : Perm (Fin 7))
    (V : Subgroup (Perm (Fin 7))) : Subgroup G :=
  ((V.comap (MulAut.conj g).toMonoidHom).comap (projSeven Y₀ φ)).map Y₀.subtype

omit [Finite G] in
theorem mem_preSeven {V : Subgroup (Perm (Fin 7))} (y : ↥Y₀) :
    (y : G) ∈ preSeven Y₀ φ g V ↔ g * projSeven Y₀ φ y * g⁻¹ ∈ V := by
  constructor
  · rintro ⟨y', hy', hyy'⟩
    have : y' = y := Subtype.ext hyy'
    subst this
    exact hy'
  · intro hy
    exact ⟨y, hy, rfl⟩

omit [Finite G] in
theorem preSeven_le {V : Subgroup (Perm (Fin 7))} : preSeven Y₀ φ g V ≤ Y₀ :=
  Subgroup.map_subtype_le _

theorem isPGroup_preSeven {V : Subgroup (Perm (Fin 7))} (hV : IsPGroup 2 V) :
    IsPGroup 2 (preSeven Y₀ φ g V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ((hV.comap_of_injective _ (MulAut.conj g).injective).comap_of_ker_isPGroup _
    (projSeven_ker_isPGroup Y₀ φ)).map Y₀.subtype

omit [Finite G] in
theorem mk_eq_of_projSeven_eq [(kerAO2 A Y₀).Normal] {u v : ↥(A ⊔ Y₀)} (hu : (u : G) ∈ Y₀)
    (hv : (v : G) ∈ Y₀) (h : projSeven Y₀ φ ⟨u, hu⟩ = projSeven Y₀ φ ⟨v, hv⟩) :
    QuotientGroup.mk' (kerAO2 A Y₀) u = QuotientGroup.mk' (kerAO2 A Y₀) v := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, kerAO2,
    Subgroup.mem_subgroupOf]
  have := inv_mul_mem_of_projSeven_eq Y₀ φ h
  simpa using this

omit [Finite G] in
theorem projSeven_eq_of_mk_eq [(kerAO2 A Y₀).Normal] {u v : ↥(A ⊔ Y₀)} (hu : (u : G) ∈ Y₀)
    (hv : (v : G) ∈ Y₀)
    (h : QuotientGroup.mk' (kerAO2 A Y₀) u = QuotientGroup.mk' (kerAO2 A Y₀) v) :
    projSeven Y₀ φ ⟨u, hu⟩ = projSeven Y₀ φ ⟨v, hv⟩ := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, kerAO2,
    Subgroup.mem_subgroupOf] at h
  have h1 := projSeven_eq_one_of_mem Y₀ φ (y := (⟨u, hu⟩ : ↥Y₀)⁻¹ * ⟨v, hv⟩)
    (by simpa using h)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

omit [Finite G] in
theorem imgY0_le_of_cimgSeven_le [(kerAO2 A Y₀).Normal] {X X' : Subgroup G} (hX : X ≤ Y₀)
    (h : cimgSeven Y₀ φ g X ≤ cimgSeven Y₀ φ g X') : imgY0 A Y₀ X ≤ imgY0 A Y₀ X' := by
  rintro _ ⟨v, hv, rfl⟩
  have hvX : (v : G) ∈ X := Subgroup.mem_subgroupOf.mp hv
  have hvY : (v : G) ∈ Y₀ := hX hvX
  obtain ⟨z, hzX', hze⟩ := mem_cimgSeven.mp (h (mem_cimgSeven.mpr ⟨⟨v, hvY⟩, hvX, rfl⟩))
  have he : projSeven Y₀ φ z = projSeven Y₀ φ ⟨v, hvY⟩ := by
    have := congrArg (fun w => g⁻¹ * w * g) hze
    simpa [mul_assoc] using this
  refine ⟨⟨z, Subgroup.mem_sup_right z.2⟩, Subgroup.mem_subgroupOf.mpr hzX', ?_⟩
  exact mk_eq_of_projSeven_eq z.2 hvY he

omit [Finite G] in
theorem imgY0_mono [(kerAO2 A Y₀).Normal] {X X' : Subgroup G} (h : X ≤ X') :
    imgY0 A Y₀ X ≤ imgY0 A Y₀ X' := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hv)), rfl⟩

variable {c : G}

theorem false_of_inf_L_le {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A7Pic A L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (hSL : S ⊓ L ≤ CFSG.Open.pCoreOf 2 Y₀) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.toSec13Data
  set π := projSeven Y₀ φ with hπ
  set T := preSeven Y₀ φ g vOne with hT
  set L₁ := L ⊓ T with hL₁
  have hL₁2 : IsPGroup 2 L₁ := (isPGroup_preSeven isPGroup_vOne).to_le inf_le_right
  have hALT : A ⊓ L ≤ Subgroup.normalizer (T : Set G) := by
    refine le_normalizer_of_conj' fun a ha t ht => ?_
    have haY : a ∈ Y₀ := hP.L_le ha.2
    have htY : t ∈ Y₀ := preSeven_le ht
    have ht' := (mem_preSeven (φ := φ) (g := g) (V := vOne) ⟨t, htY⟩).mp ht
    have hk := eNine_conj_mem_vOne (hP.mem ⟨a, haY⟩ ha) ht'
    have hya : g * π (⟨a, haY⟩ * ⟨t, htY⟩ * ⟨a, haY⟩⁻¹) * g⁻¹ =
        (g * π ⟨a, haY⟩ * g⁻¹) * (g * π ⟨t, htY⟩ * g⁻¹) * (g * π ⟨a, haY⟩ * g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
      group
    have hmem := (mem_preSeven (φ := φ) (g := g) (V := vOne)
      (⟨a, haY⟩ * ⟨t, htY⟩ * ⟨a, haY⟩⁻¹)).mpr (by rw [hya]; exact hk)
    simpa using hmem
  have hAL₁ : A ≤ Subgroup.normalizer (L₁ : Set G) :=
    hP.A_norm L₁ inf_le_left (Late.le_normalizer_inf (inf_le_left.trans hD.le_normalizer) hALT)
  have hL₁H : L₁ ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    inf_le_left.trans (hD.le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
  have hL₁inv : L₁ ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
      (piCompl 3) :=
    ⟨hL₁H, (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      (Proof171.not_three_dvd_of_isPGroup_two hL₁2), hAL₁⟩
  obtain ⟨Q, hQ, hL₁Q⟩ := exists_le_mem_maxInvariantPiSubgroups hL₁inv
  have hQQ := (h142 c h.zpowers_mem_omegaA Q hQ).1
  have hL₁P : L₁ ∈ scriptQPi A (lB A) L (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hQQ hL₁Q hAL₁, inf_le_left⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr hL₁2⟩
  have hSLL₁ : S ⊓ L ≤ L₁ := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    have hxO := hSL hx
    have hxY : x ∈ Y₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀ hxO
    refine (mem_preSeven (φ := φ) (g := g) (V := vOne) ⟨x, hxY⟩).mpr ?_
    rw [show π ⟨x, hxY⟩ = 1 from projSeven_eq_one_of_mem Y₀ φ hxO, mul_one, mul_inv_cancel]
    exact vOne.one_mem
  have hle : L₁ ≤ S ⊓ L := h.inf_L_mem_qStar_two.2 hL₁P hSLL₁
  have hzA : g⁻¹ * vOneF 1 * g ∈ alternatingGroup (Fin 7) := by
    have := (alternatingGroup.normal (α := Fin 7)).conj_mem (vOneF 1) (vOneF_spec 1).2 g⁻¹
    simpa using this
  obtain ⟨l, hl, hlz⟩ := hP.L_surj _ hzA
  have hlz' : g * π l * g⁻¹ = vOneF 1 := by
    rw [hlz]
    group
  have hlL₁ : (l : G) ∈ L₁ :=
    ⟨hl, (mem_preSeven (φ := φ) (g := g) (V := vOne) l).mpr (by rw [hlz']; exact ⟨1, rfl⟩)⟩
  have h1 : π l = 1 := projSeven_eq_one_of_mem Y₀ φ (hSL (hle hlL₁))
  rw [h1, mul_one, mul_inv_cancel] at hlz'
  exact vF_ne_one.1 hlz'.symm

theorem cimg_eq {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A7Pic A L Y₀ φ g)
    (h142 : Concl142 A (lB A)) :
    cimgSeven Y₀ φ g (S ⊓ Y₀) = vOne ∨ cimgSeven Y₀ φ g (S ⊓ Y₀) = vTwo := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := cimgSeven Y₀ φ g (S ⊓ Y₀) with hR
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hR3 : ¬ 3 ∣ Nat.card R := not_three_dvd_card_cimgSeven inf_le_right
    (Proof171.not_three_dvd_of_isPGroup_two (hS2.to_le inf_le_left))
  have hAS : A ≤ Subgroup.normalizer ((S ⊓ Y₀ : Subgroup G) : Set G) :=
    Late.le_normalizer_inf h.mem_qStar_two.prop.1.1.1.2.2 h.le_normalizer_y0
  have hER := eNine_le_normalizer_cimgSeven hP (inf_le_left.trans hAS)
  have hR0 : R ≠ ⊥ := by
    intro h0
    refine false_of_inf_L_le h hP h142 fun x hx => ?_
    have hxY : x ∈ Y₀ := hP.L_le hx.2
    have hz : g * projSeven Y₀ φ ⟨x, hxY⟩ * g⁻¹ ∈ R :=
      mem_cimgSeven.mpr ⟨⟨x, hxY⟩, ⟨hx.1, hxY⟩, rfl⟩
    rw [h0, Subgroup.mem_bot, conj_eq_one_iff] at hz
    exact mem_pCoreOf_of_projSeven_eq_one Y₀ φ hz
  rcases le_vOne_or_le_vTwo hR3 (hER cOne_mem_eNine) (hER cTwo_mem_eNine) with h1 | h1
  · exact Or.inl (vF_irreducible (Or.inl rfl) h1 hER hR0)
  · exact Or.inr (vF_irreducible (Or.inr rfl) h1 hER hR0)

theorem le_sup_cQuot_of_a7 {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A7Pic A L Y₀ φ g)
    (h142 : Concl142 A (lB A)) (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G)) :
    S ≤ (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set ψ := actSeven Y₀ φ with hψ
  set R' : Subgroup (Perm (Fin 7)) := ((S.subgroupOf M).map ψ).map (MulAut.conj g).toMonoidHom
    with hR'
  have hmemR' : ∀ z, z ∈ R' ↔ ∃ m : M, (m : G) ∈ S ∧ g * ψ m * g⁻¹ = z := by
    intro z
    constructor
    · rintro ⟨w, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨m, Subgroup.mem_subgroupOf.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨ψ m, ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩, rfl⟩
  have hSQ : S ∈ scriptQ A (lB A) := h.mem_qStar_two.prop.1.1
  have hS2 : IsPGroup 2 S := (isPiSubgroup_piOf_iff Nat.prime_two S).mp h.mem_qStar_two.prop.2
  have hR'3 : ¬ 3 ∣ Nat.card R' := by
    rw [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective]
    intro h3
    have hd := Subgroup.card_map_dvd (S.subgroupOf M) ψ
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv] at hd
    exact Proof171.not_three_dvd_of_isPGroup_two hS2 (h3.trans hd)
  have hER' : eNine ≤ Subgroup.normalizer (R' : Set (Perm (Fin 7))) := by
    refine le_normalizer_of_conj' fun x hx z hz => ?_
    obtain ⟨a, ha, rfl⟩ := hP.surj x hx
    obtain ⟨m, hm, rfl⟩ := (hmemR' z).mp hz
    have haM : (a : G) ∈ M := Y₀.le_normalizer a.2
    refine (hmemR' _).mpr ⟨⟨a, haM⟩ * m * ⟨a, haM⟩⁻¹, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hSQ.1.2.2 ha.1) (m : G)).mp hm
      simpa using this
    · rw [map_mul, map_mul, map_inv, show (⟨a, haM⟩ : M) = ⟨a, Y₀.le_normalizer a.2⟩ from rfl,
        actSeven_eq_projSeven]
      group
  have hle : cimgSeven Y₀ φ g (S ⊓ Y₀) ≤ R' := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_cimgSeven.mp hz
    exact (hmemR' _).mpr ⟨⟨y, Y₀.le_normalizer y.2⟩, hy.1, by rw [actSeven_eq_projSeven]⟩
  have hR'le : R' ≤ cimgSeven Y₀ φ g (S ⊓ Y₀) := by
    have hmem1 : vOneF 1 ∈ vOne := ⟨1, rfl⟩
    have hmem2 : vTwoF 1 ∈ vTwo := ⟨1, rfl⟩
    rcases cimg_eq h hP h142 with h1 | h1 <;> rw [h1] at hle ⊢ <;>
      rcases le_vOne_or_le_vTwo hR'3 (hER' cOne_mem_eNine) (hER' cTwo_mem_eNine) with h2 | h2
    · exact h2
    · obtain ⟨n, hn⟩ := h2 (hle hmem1)
      exact absurd (vOneF_eq_vTwoF 1 n hn) (by decide)
    · obtain ⟨n, hn⟩ := h2 (hle hmem2)
      have h0 := vOneF_eq_vTwoF n 1 hn.symm
      subst h0
      exact absurd hn vF_ne_one.2
    · exact h2
  intro s hs
  have hz : g * ψ ⟨s, hSM hs⟩ * g⁻¹ ∈ cimgSeven Y₀ φ g (S ⊓ Y₀) :=
    hR'le ((hmemR' _).mpr ⟨_, hs, rfl⟩)
  obtain ⟨y, hy, hyz⟩ := mem_cimgSeven.mp hz
  have he : projSeven Y₀ φ y = ψ ⟨s, hSM hs⟩ := by
    have := congrArg (fun z => g⁻¹ * z * g) hyz
    simpa [mul_assoc] using this
  have hu : ψ (⟨y, Y₀.le_normalizer y.2⟩⁻¹ * ⟨s, hSM hs⟩) = 1 := by
    rw [map_mul, map_inv, actSeven_eq_projSeven, he, inv_mul_cancel]
  have huC := mem_cQuot_of_actSeven_eq_one Y₀ φ hu
  have hs' : s = (y : G) * ((y : G)⁻¹ * s) := by group
  rw [hs']
  refine Subgroup.mul_mem_sup hy (Subgroup.mem_inf.mpr
    ⟨mul_mem (inv_mem (Subgroup.mem_inf.mp hy).1) hs, ?_⟩)
  simpa using huC

omit [Finite G] in
theorem conj_commute_iff {X : Type*} [Group X] (k u v : X) :
    k * u * k⁻¹ * (k * v * k⁻¹) = k * v * k⁻¹ * (k * u * k⁻¹) ↔ u * v = v * u := by
  constructor
  · intro h
    have := congrArg (fun w => k⁻¹ * w * k) h
    simpa [mul_assoc] using this
  · intro h
    calc k * u * k⁻¹ * (k * v * k⁻¹) = k * (u * v) * k⁻¹ := by group
      _ = k * (v * u) * k⁻¹ := by rw [h]
      _ = k * v * k⁻¹ * (k * u * k⁻¹) := by group

omit [Finite G] in
theorem mk_inclusion_eq_iff [(kerAO2 A Y₀).Normal] (y y' : ↥Y₀) :
    QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) =
        QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y') ↔
      projSeven Y₀ φ y = projSeven Y₀ φ y' :=
  ⟨fun h => projSeven_eq_of_mk_eq y.2 y'.2 h, fun h => mk_eq_of_projSeven_eq y.2 y'.2 h⟩

omit [Finite G] in
theorem mk_inclusion_commute_iff [(kerAO2 A Y₀).Normal] (y y' : ↥Y₀) :
    QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) *
        QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y') =
      QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y') *
        QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) ↔
      projSeven Y₀ φ y * projSeven Y₀ φ y' = projSeven Y₀ φ y' * projSeven Y₀ φ y := by
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  exact mk_inclusion_eq_iff (y * y') (y' * y)

omit [Finite G] in
theorem mem_imgY0_iff [(kerAO2 A Y₀).Normal] {X : Subgroup G} (hX : X ≤ Y₀)
    (x : ↥(A ⊔ Y₀) ⧸ kerAO2 A Y₀) :
    x ∈ imgY0 A Y₀ X ↔ ∃ y : ↥Y₀, (y : G) ∈ X ∧
      QuotientGroup.mk' (kerAO2 A Y₀) (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) =
        x := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvX : (v : G) ∈ X := Subgroup.mem_subgroupOf.mp hv
    exact ⟨⟨v, hX hvX⟩, hvX, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem oTwoCY0_eq [(kerAO2 A Y₀).Normal] {x₀ y₀ : Perm (Fin 7)} {V : Subgroup (Perm (Fin 7))}
    (hV2 : IsPGroup 2 V) (hVc : ∀ v ∈ V, v * x₀ = x₀ * v)
    (hVn : ∀ z ∈ alternatingGroup (Fin 7), z * x₀ = x₀ * z → ∀ v ∈ V, z * v * z⁻¹ ∈ V)
    (hmax : ∀ Q : Subgroup (Perm (Fin 7)), ¬ 3 ∣ Nat.card Q →
      y₀ ∈ Subgroup.normalizer (Q : Set (Perm (Fin 7))) → ∀ x ∈ Q, x * x₀ = x₀ * x → x ∈ V)
    (hxy : x₀ * y₀ = y₀ * x₀) {a b : ↥Y₀} (ha : (a : G) ∈ A)
    (hax : g * projSeven Y₀ φ a * g⁻¹ = x₀) (hby : g * projSeven Y₀ φ b * g⁻¹ = y₀) :
    oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) = imgY0 A Y₀ (preSeven Y₀ φ g V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := projSeven Y₀ φ with hπ
  set N := kerAO2 A Y₀ with hN
  set κ : ↥Y₀ →* ↥(A ⊔ Y₀) ⧸ N :=
    (QuotientGroup.mk' N).comp (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀)) with hκ
  have hκapp : ∀ y : ↥Y₀, κ y =
      QuotientGroup.mk' N (Subgroup.inclusion (le_sup_right : Y₀ ≤ A ⊔ Y₀) y) := fun _ => rfl
  set T := preSeven Y₀ φ g V with hT
  set H := imgY0 A Y₀ Y₀ ⊓ Subgroup.centralizer {alphaY0 A Y₀ a ha} with hH
  have hαa : alphaY0 A Y₀ a ha = κ a := rfl
  have hcomm : ∀ y : ↥Y₀, κ y ∈ Subgroup.centralizer {alphaY0 A Y₀ a ha} ↔
      g * π y * g⁻¹ * x₀ = x₀ * (g * π y * g⁻¹) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, hαa, hκapp, hκapp, mk_inclusion_commute_iff,
      ← hax, conj_commute_iff]
  have hmemY : ∀ x, x ∈ imgY0 A Y₀ Y₀ ↔ ∃ y : ↥Y₀, κ y = x := by
    intro x
    rw [mem_imgY0_iff le_rfl]
    exact ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, y.2, hy⟩⟩
  have hmemT : ∀ x, x ∈ imgY0 A Y₀ T ↔ ∃ y : ↥Y₀, g * π y * g⁻¹ ∈ V ∧ κ y = x := by
    intro x
    rw [mem_imgY0_iff preSeven_le]
    exact ⟨fun ⟨y, hyT, hy⟩ => ⟨y, (mem_preSeven y).mp hyT, hy⟩,
      fun ⟨y, hyV, hy⟩ => ⟨y, (mem_preSeven y).mpr hyV, hy⟩⟩
  apply le_antisymm
  ·
    set P := CFSG.Open.pCoreOf 2 H with hP
    set P' : Subgroup ↥Y₀ := P.comap κ with hP'
    have hκker : IsPGroup 2 κ.ker := by
      intro ⟨y, hy⟩
      have hy1 : κ y = κ 1 := by rw [MonoidHom.mem_ker.mp hy, map_one]
      have hπy : π y = 1 := by
        have := (mk_inclusion_eq_iff (φ := φ) y 1).mp hy1
        rwa [map_one] at this
      obtain ⟨k, hk⟩ := projSeven_ker_isPGroup Y₀ φ ⟨y, hπy⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hP'2 : IsPGroup 2 P' :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).comap_of_ker_isPGroup κ hκker
    set Q' : Subgroup (Perm (Fin 7)) := P'.map ((MulAut.conj g).toMonoidHom.comp π) with hQ'
    have hQ'3 : ¬ 3 ∣ Nat.card Q' := Proof171.not_three_dvd_of_isPGroup_two (hP'2.map _)
    have hbH : κ b ∈ H := by
      refine ⟨(hmemY _).mpr ⟨b, rfl⟩, (hcomm b).mpr ?_⟩
      rw [hby]
      exact hxy.symm
    have hy₀ : y₀ ∈ Subgroup.normalizer (Q' : Set (Perm (Fin 7))) := by
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨b * y * b⁻¹, ?_, ?_⟩
      · change κ (b * y * b⁻¹) ∈ P
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hbH) _).mp hy
      · change g * π (b * y * b⁻¹) * g⁻¹ = y₀ * (g * π y * g⁻¹) * y₀⁻¹
        rw [← hby, map_mul, map_mul, map_inv]
        group
    have hQc : ∀ x ∈ Q', x * x₀ = x₀ * x := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hcomm y).mp (CFSG.LieType.BorelTits.pCoreOf_le 2 H hy).2
    intro x hx
    have hxH : x ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hx
    obtain ⟨y, rfl⟩ := (hmemY x).mp hxH.1
    exact (hmemT _).mpr ⟨y, hmax Q' hQ'3 hy₀ _ ⟨y, hx, rfl⟩ (hQc _ ⟨y, hx, rfl⟩), rfl⟩
  ·
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ ?_
    · intro x hx
      obtain ⟨y, hyV, rfl⟩ := (hmemT x).mp hx
      exact ⟨(hmemY _).mpr ⟨y, rfl⟩, (hcomm y).mpr (hVc _ hyV)⟩
    · refine le_normalizer_of_conj' fun h' hh' t ht => ?_
      obtain ⟨y', rfl⟩ := (hmemY h').mp hh'.1
      obtain ⟨y, hyV, rfl⟩ := (hmemT t).mp ht
      have hz : g * π y' * g⁻¹ ∈ alternatingGroup (Fin 7) :=
        (alternatingGroup.normal (α := Fin 7)).conj_mem _ (projSeven_mem_alternatingGroup Y₀ φ y')
          g
      have hzV := hVn _ hz ((hcomm y').mp hh'.2) _ hyV
      refine (hmemT _).mpr ⟨y' * y * y'⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      rw [map_mul, map_mul, map_inv]
      convert hzV using 1
      group
    · exact ((isPGroup_preSeven hV2).comap_subtype).map _

theorem cOne_ne_one_and_cTwo_ne_one : cOne ≠ 1 ∧ cTwo ≠ 1 := by
  decide +kernel

theorem oTwoCY0_eq_vOne [(kerAO2 A Y₀).Normal] (hP : A7Pic A L Y₀ φ g) {a : ↥Y₀}
    (ha : (a : G) ∈ A) (hax : g * projSeven Y₀ φ a * g⁻¹ = cOne) :
    oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) = imgY0 A Y₀ (preSeven Y₀ φ g vOne) := by
  obtain ⟨b, -, hb⟩ := hP.surj cTwo cTwo_mem_eNine
  refine oTwoCY0_eq isPGroup_vOne (fun v hv => ?_) (fun z hz hzc v hv => ?_)
    (fun Q hQ3 hQN x hx hxc => mem_vOne_of_commute hQ3 hQN hx hxc) cOne_mul_cTwo ha hax hb
  · obtain ⟨m, rfl⟩ := hv
    exact (vOneF_spec m).1
  · have hzC : z ∈ centOne := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hzc, hz⟩
    have := vOne_normal.conj_mem ⟨v, vOne_le_centOne hv⟩ (Subgroup.mem_subgroupOf.mpr hv)
      ⟨z, hzC⟩
    simpa using Subgroup.mem_subgroupOf.mp this

theorem oTwoCY0_eq_vTwo [(kerAO2 A Y₀).Normal] (hP : A7Pic A L Y₀ φ g) {a : ↥Y₀}
    (ha : (a : G) ∈ A) (hax : g * projSeven Y₀ φ a * g⁻¹ = cTwo) :
    oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) = imgY0 A Y₀ (preSeven Y₀ φ g vTwo) := by
  obtain ⟨b, -, hb⟩ := hP.surj cOne cOne_mem_eNine
  refine oTwoCY0_eq isPGroup_vTwo (fun v hv => ?_) (fun z hz hzc v hv => ?_)
    (fun Q hQ3 hQN x hx hxc => mem_vTwo_of_commute hQ3 hQN hx hxc) cOne_mul_cTwo.symm ha hax hb
  · obtain ⟨m, rfl⟩ := hv
    exact (vTwoF_spec m).1
  · have hzC : z ∈ centTwo := ⟨Subgroup.mem_centralizer_singleton_iff.mpr hzc, hz⟩
    have := vTwo_normal.conj_mem ⟨v, vTwo_le_centTwo hv⟩ (Subgroup.mem_subgroupOf.mpr hv)
      ⟨z, hzC⟩
    simpa using Subgroup.mem_subgroupOf.mp this

theorem item1717One_of_a7 [(kerAO2 A Y₀).Normal] {Y₁ S : Subgroup G} {p : ℕ} {P : Subgroup G}
    (h : Sec17Y1 G A c L Y₀ Y₁ S p P) (hP : A7Pic A L Y₀ φ g) (h142 : Concl142 A (lB A))
    (hSM : S ≤ Subgroup.normalizer (Y₀ : Set G)) :
    S = (S ⊓ Y₀) ⊔ (S ⊓ cQuot Y₀) ∧
      ∃ (a : G) (ha : a ∈ A), a ∈ L ∧ a ≠ 1 ∧
        imgY0 A Y₀ (S ⊓ Y₀) = oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) := by
  refine ⟨le_antisymm (le_sup_cQuot_of_a7 h hP h142 hSM) (sup_le inf_le_left inf_le_left), ?_⟩
  have key : ∀ (V : Subgroup (Perm (Fin 7))) (x₀ : Perm (Fin 7)), x₀ ≠ 1 → x₀ ∈ eNine →
      cimgSeven Y₀ φ g (S ⊓ Y₀) = V →
      (∀ (a : ↥Y₀) (ha : (a : G) ∈ A), g * projSeven Y₀ φ a * g⁻¹ = x₀ →
        oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) = imgY0 A Y₀ (preSeven Y₀ φ g V)) →
      ∃ (a : G) (ha : a ∈ A), a ∈ L ∧ a ≠ 1 ∧
        imgY0 A Y₀ (S ⊓ Y₀) = oTwoCY0 A Y₀ (alphaY0 A Y₀ a ha) := by
    intro V x₀ hx₀ hx₀E hV hO
    obtain ⟨a, haAL, hax⟩ := hP.surj x₀ hx₀E
    refine ⟨a, haAL.1, haAL.2, fun h1 => hx₀ ?_, ?_⟩
    · rw [← hax, show a = 1 from Subtype.ext h1, map_one, mul_one, mul_inv_cancel]
    · rw [hO a haAL.1 hax]
      apply le_antisymm
      · refine imgY0_mono fun x hx => ?_
        have hxY : x ∈ Y₀ := hx.2
        refine (mem_preSeven ⟨x, hxY⟩).mpr ?_
        rw [← hV]
        exact mem_cimgSeven.mpr ⟨⟨x, hxY⟩, hx, rfl⟩
      · refine imgY0_le_of_cimgSeven_le (φ := φ) (g := g) preSeven_le fun z hz => ?_
        obtain ⟨y, hy, rfl⟩ := mem_cimgSeven.mp hz
        rw [hV]
        exact (mem_preSeven y).mp hy
  rcases cimg_eq h hP h142 with hV | hV
  · exact key vOne cOne cOne_ne_one_and_cTwo_ne_one.1 cOne_mem_eNine hV
      fun a ha hax => oTwoCY0_eq_vOne hP ha hax
  · exact key vTwo cTwo cOne_ne_one_and_cTwo_ne_one.2 cTwo_mem_eNine hV
      fun a ha hax => oTwoCY0_eq_vTwo hP ha hax

end CFSG.RankThree.PartTwo.Sec17.Proof17Res6
