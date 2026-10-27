module

public import CFSG.Timmesfeld.Bridge.OddTranspDefs
public import CFSG.Timmesfeld.Bridge.Asc72Local
public import CFSG.Timmesfeld.Bridge.Asc72Width

public section

namespace CFSG.Timmesfeld.Bridge.OddTransp

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

@[expose] def MeetsSq (D : Set G) : Prop :=
  ∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D

theorem commute_iff_mul_of_mem [Finite G] (hS : Setup G D) {u v : G} (hu : u ∈ D)
    (hv : v ∈ D) (hne : u ≠ v) (hc : Commute u v) (huv : u * v ∈ D) {x : G} (hx : x ∈ D) :
    Commute x u ↔ Commute x (u * v) := by
  classical
  set A := {x | x ∈ D ∧ Commute x u}
  set B := {x | x ∈ D ∧ Commute x (u * v)}
  have hBA : B ⊆ A := fun x hx =>
    ⟨hx.1, ((hS.oddT.commute_mul_iff hu hv hx.1 hne hc).mp hx.2).1⟩
  obtain ⟨c, hc'⟩ := isConj_iff.mp (hS.isConj hu huv)
  have hcard : A.ncard = B.ncard := by
    have himage : (fun x => c * x * c⁻¹) '' A = B := by
      ext y
      constructor
      · rintro ⟨x, ⟨hxD, hxu⟩, rfl⟩
        exact ⟨hS.conj_mem c hxD, hc' ▸ (Commute.conj_iff c).mpr hxu⟩
      · rintro ⟨hyD, hyc⟩
        refine ⟨c⁻¹ * y * c⁻¹⁻¹, ⟨hS.conj_mem c⁻¹ hyD, ?_⟩, by group⟩
        have := (Commute.conj_iff c⁻¹).mpr hyc
        rw [← hc'] at this
        simpa [mul_assoc] using this
    rw [← himage, Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)]
  have hAB : A = B := (Set.eq_of_subset_of_ncard_le hBA (by rw [hcard]) (Set.toFinite _)).symm
  constructor
  · intro hxu
    have : x ∈ B := hAB ▸ ⟨hx, hxu⟩
    exact this.2
  · intro hxuv
    exact (hBA ⟨hx, hxuv⟩).2

theorem commute_iff_of_mul_mem [Finite G] (hS : Setup G D) {u v : G} (hu : u ∈ D)
    (hv : v ∈ D) (hne : u ≠ v) (hc : Commute u v) (huv : u * v ∈ D) {x : G} (hx : x ∈ D) :
    Commute x u ↔ Commute x v := by
  rw [commute_iff_mul_of_mem hS hu hv hne hc huv hx]
  have hvu : v * u ∈ D := hc.eq ▸ huv
  rw [commute_iff_mul_of_mem hS hv hu hne.symm hc.symm hvu hx, hc.eq]

theorem exists_mul_mem (hS : Setup G D) (h : MeetsSq D) {a : G} (ha : a ∈ D) :
    ∃ v ∈ D, a ≠ v ∧ Commute a v ∧ a * v ∈ D := by
  obtain ⟨u, hu, v, hv, hne, hc, huv⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hu ha)
  refine ⟨g * v * g⁻¹, hS.conj_mem g hv, fun h => hne ?_, (Commute.conj_iff g).mpr hc, ?_⟩
  · simpa using h
  · have := hS.conj_mem g huv
    simpa [mul_assoc] using this

theorem MeetsSq.map {K : Type*} [Group K] (h : MeetsSq D) (hD : IsOddTransp D) (φ : G →* K)
    (hφ : ∀ d ∈ D, φ d ≠ 1) : ∃ u ∈ φ '' D, ∃ v ∈ φ '' D, u ≠ v ∧ Commute u v ∧ u * v ∈ φ '' D := by
  obtain ⟨u, hu, v, hv, -, hc, huv⟩ := h
  refine ⟨φ u, ⟨u, hu, rfl⟩, φ v, ⟨v, hv, rfl⟩, fun he => hφ _ huv ?_, hc.map φ,
    ⟨u * v, huv, map_mul φ u v⟩⟩
  rw [map_mul, ← he, ← map_mul, hD.mul_self_eq_one hu, map_one]

theorem commutator_eq_top (hS : Setup G D) (h : MeetsSq D) : commutator G = ⊤ := by
  by_contra hne
  obtain ⟨u, hu, v, hv, -, -, huv⟩ := h
  rcases hS.subset_or_disjoint (commutator G) with h' | h'
  · exact hne (hS.eq_top_of_subset _ h')
  · exact h' _ huv (hS.mul_mem_commutator hu hv)

theorem not_isSolvable [Finite G] (hS : Setup G D) (h : MeetsSq D) :
    ¬ Group.IsSolvable G := fun hsol => by
  obtain ⟨u, hu, v, hv, -, -, huv⟩ := h
  exact hS.mul_not_mem_of_isSolvable hsol hu hv huv

theorem not_mem_of_isSolvable [Finite G] (hS : Setup G D) (h : MeetsSq D)
    {N : Subgroup G} [N.Normal] (hN : Group.IsSolvable N) {d : G} (hd : d ∈ D) : d ∉ N := by
  rcases hS.subset_or_disjoint N with h' | h'
  · intro _
    apply not_isSolvable hS h
    have htop := hS.eq_top_of_subset N h'
    exact Group.isSolvable_of_surjective (f := N.subtype) (fun g => ⟨⟨g, htop ▸ trivial⟩, rfl⟩)
  · exact h' d hd

theorem setup_of_disconnected (hD : IsOddTransp D) (hN : IsNormalSet D)
    (hgen : Subgroup.closure D = ⊤) (hdisc : Disconnected D) : Setup G D := by
  obtain ⟨x, hx, -⟩ := id hdisc
  refine ⟨⟨x, ?_⟩, hD, hgen⟩
  ext y
  constructor
  · intro hy
    exact isConj_of_disconnected_of_odd hD.isInvolutionSet hD.oddAcross hdisc hx hy
  · intro hy
    obtain ⟨c, rfl⟩ := isConj_iff.mp hy
    exact hN c x hx

theorem le_solvableRadical {N : Subgroup G} (hN : N.Normal) (hs : Group.IsSolvable N) :
    N ≤ CFSG.solvableRadical G :=
  le_sSup ⟨hN, hs⟩

theorem isSolvable_solvableRadical [Finite G] : Group.IsSolvable (CFSG.solvableRadical G) := by
  obtain ⟨R, -, hRs, hR⟩ := exists_solvableRadical G
  have hle : CFSG.solvableRadical G ≤ R := sSup_le fun N hN => hR N hN.1 hN.2
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem eq_bot_of_quotient_solvableRadical [Finite G]
    (N : Subgroup (G ⧸ CFSG.solvableRadical G)) (hN : N.Normal) (hNs : Group.IsSolvable N) :
    N = ⊥ :=
  eq_bot_of_solvableRadical isSolvable_solvableRadical (fun _ hK hKs => le_solvableRadical hK hKs)
    N hN hNs

theorem mem_zStar_iff {g : G} : g ∈ zStar G ↔ ∀ h : G, ⁅g, h⁆ ∈ CFSG.pCore 2 G := by
  rw [zStar, Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro H h
    have h1 := H (QuotientGroup.mk' _ h)
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    have h2 := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem _ h1 (h * g)
    rw [commutatorElement_def]
    convert h2 using 1
    group
  · intro H q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 G) q
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h2 := (CFSG.pCore_normal (p := 2) (G := G)).conj_mem _ (H h) (h * g)⁻¹
    rw [commutatorElement_def] at h2
    convert h2 using 1
    group

theorem pCore_le_zStar : CFSG.pCore 2 G ≤ zStar G := by
  intro g hg
  rw [mem_zStar_iff]
  intro h
  rw [commutatorElement_def]
  have := (CFSG.pCore 2 G).mul_mem hg
    ((CFSG.pCore_normal (p := 2) (G := G)).conj_mem _ ((CFSG.pCore 2 G).inv_mem hg) h)
  simpa [mul_assoc] using this

theorem isSolvable_zStar [Finite G] : Group.IsSolvable (zStar G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := CFSG.pCore 2 G
  let f : P →* zStar G := Subgroup.inclusion pCore_le_zStar
  let g : zStar G →* Subgroup.center (G ⧸ P) :=
    ((QuotientGroup.mk' P).comp (zStar G).subtype).codRestrict _ fun x => x.2
  have hP : Group.IsSolvable P := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := G)).isNilpotent
    infer_instance
  have hC : Group.IsSolvable (Subgroup.center (G ⧸ P)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro x hx
  have hx' : ((x : G) : G ⧸ P) = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp hx'⟩, rfl⟩

theorem zStar_le_solvableRadical [Finite G] : zStar G ≤ CFSG.solvableRadical G :=
  le_solvableRadical inferInstance isSolvable_zStar

theorem commutatorElement_mem_of_mem_closure {Q K : Subgroup G} (hKQ : K ≤ Q) {T : Set G}
    (hT2 : ∀ t ∈ T, t * t = 1) (hgen : ∀ t ∈ T, ∀ q ∈ Q, ⁅q, t⁆ ∈ K) {g : G}
    (hg : g ∈ Subgroup.closure T) : ∀ q ∈ Q, ⁅q, g⁆ ∈ K := by
  induction hg using Subgroup.closure_induction'' with
  | mem t ht => exact hgen t ht
  | inv_mem t ht =>
    rw [inv_eq_of_mul_eq_one_right (hT2 t ht)]
    exact hgen t ht
  | one => intro q _; rw [commutatorElement_one_right]; exact K.one_mem
  | mul x y _ _ hx hy =>
    intro q hq
    have hk := hy q hq
    have hkx := hx _ (Q.inv_mem (hKQ hk))
    have e : ⁅q, x * y⁆ = ⁅q, x⁆ * (⁅q, y⁆ * ⁅⁅q, y⁆⁻¹, x⁆) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact K.mul_mem (hx q hq) (K.mul_mem hk hkx)

theorem commutator_le_of_closure {Q K : Subgroup G} (hKQ : K ≤ Q) {T : Set G}
    (hT : Subgroup.closure T = ⊤) (hT2 : ∀ t ∈ T, t * t = 1)
    (hgen : ∀ t ∈ T, ∀ q ∈ Q, ⁅q, t⁆ ∈ K) : ⁅Q, (⊤ : Subgroup G)⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro q hq g _
  exact commutatorElement_mem_of_mem_closure hKQ hT2 hgen (hT ▸ Subgroup.mem_top g) q hq

theorem conj_mem_of_mem_closure {Q : Subgroup G} {T : Set G} (hT2 : ∀ t ∈ T, t * t = 1)
    (hgen : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) {g : G} (hg : g ∈ Subgroup.closure T) :
    ∀ q ∈ Q, g * q * g⁻¹ ∈ Q := by
  induction hg using Subgroup.closure_induction'' with
  | mem t ht => exact hgen t ht
  | inv_mem t ht =>
    rw [inv_eq_of_mul_eq_one_right (hT2 t ht)]
    exact hgen t ht
  | one => intro q hq; simpa using hq
  | mul x y _ _ hx hy =>
    intro q hq
    have := hx _ (hy q hq)
    simpa [mul_assoc] using this

theorem eq_one_of_isPGroup_of_odd {P : Subgroup G} (hP : IsPGroup 2 P) {x : G} (hx : x ∈ P)
    (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases i with _ | i
  · rwa [pow_zero, orderOf_eq_one_iff] at hi
  · rw [hi, pow_succ] at hodd
    exact absurd hodd (by simp [Nat.not_odd_iff_even])

end CFSG.Timmesfeld.Bridge.OddTransp
