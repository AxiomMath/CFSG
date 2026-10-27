module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapIndex
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPGapKillAux

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

private lemma wcgapk_mem_centralizer_subgroupOf {G : Type*} [Group G] (S : Subgroup G)
    (x : ↥(normalizer (S : Set G))) :
    x ∈ Subgroup.centralizer
        ((S.subgroupOf (normalizer (S : Set G))) : Set ↥(normalizer (S : Set G)))
      ↔ (x : G) ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, S.le_normalizer hy⟩ hy)
  · intro h y hy
    exact Subtype.ext (h (y : G) (Subgroup.mem_subgroupOf.mp hy))

private lemma wcgapk_inf_centralizer_subgroupOf {G : Type*} [Group G] (S : Subgroup G) :
    (S.subgroupOf (normalizer (S : Set G))) ⊓
        Subgroup.centralizer
          ((S.subgroupOf (normalizer (S : Set G))) : Set ↥(normalizer (S : Set G)))
      = (S ⊓ Subgroup.centralizer (S : Set G)).subgroupOf (normalizer (S : Set G)) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, wcgapk_mem_centralizer_subgroupOf S x]

@[expose] def BorelKills {G : Type} [Group G] (S T : Subgroup G) : Prop :=
  ∀ (E : Type) [Group E], ElemAbOrderEight E →
    ∀ (W : Subgroup (MulAut E)) (X : Type) [Group X] (ψ : ↥W →* X), Function.Surjective ψ →
      ∀ φ : ↥(normalizer (S : Set G)) →* X,
        T.subgroupOf (normalizer (S : Set G)) ≤ φ.ker

@[expose] def OrderFiveData {G : Type} [Group G] (S : Subgroup G) : Prop :=
  ∃ d ∈ normalizer (S : Set G), d ^ 5 = 1 ∧
    (∀ x ∈ S, d * x * d⁻¹ * x⁻¹ ∈ S ⊓ centralizer (S : Set G) →
      x ∈ S ⊓ centralizer (S : Set G)) ∧
    (∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ centralizer (S : Set G)) ∧
    (∀ z ∈ S ⊓ centralizer (S : Set G), ∃ x ∈ S, ∃ y ∈ S, z = x * y * x⁻¹ * y⁻¹)

@[expose] def CenterIrred {G : Type} [Group G] (S : Subgroup G) : Prop :=
  ∀ x ∈ S, x ∉ centralizer (S : Set G) → ∀ Z' : Subgroup G,
    Z' ≤ S ⊓ centralizer (S : Set G) →
    (∀ b ∈ normalizer (S : Set G), ∀ z ∈ Z', b * z * b⁻¹ ∈ Z') →
    (∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z') → Z' = S ⊓ centralizer (S : Set G)

theorem borelKills_sylow_of_orderFive {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (h : OrderFiveData S) : BorelKills S S := by
  obtain ⟨d, hdN, hd5, hfpf, hcomm, hcom⟩ := h
  intro E _ hE W X _ ψ hψ φ
  let B := normalizer (S : Set G)
  let S₀ : Subgroup ↥B := S.subgroupOf B
  let N : Subgroup ↥B := φ.ker
  have hS : S₀.Normal := inferInstance
  have hN : N.Normal := inferInstance
  have hidx : N.index ∣ 168 := index_ker_dvd_168 hE W ψ hψ φ
  have hd0 : (⟨d, hdN⟩ : ↥B) ^ 5 = 1 := by
    apply Subtype.ext
    simpa using hd5
  have hfpf' : ∀ x ∈ S₀, (⟨d, hdN⟩ : ↥B) * x * (⟨d, hdN⟩ : ↥B)⁻¹ * x⁻¹ ∈
      S₀ ⊓ centralizer (S₀ : Set ↥B) → x ∈ S₀ ⊓ centralizer (S₀ : Set ↥B) := by
    intro x hxS hx
    rw [wcgapk_inf_centralizer_subgroupOf S] at hx ⊢
    exact Subgroup.mem_subgroupOf.mpr
      (hfpf (x : G) (Subgroup.mem_subgroupOf.mp hxS) (Subgroup.mem_subgroupOf.mp hx))
  have hcomm' : ∀ x ∈ S₀, ∀ y ∈ S₀, x * y * x⁻¹ * y⁻¹ ∈ centralizer (S₀ : Set ↥B) := by
    intro x hxS y hyS
    exact (wcgapk_mem_centralizer_subgroupOf S (x * y * x⁻¹ * y⁻¹)).mpr
      (hcomm (x : G) (Subgroup.mem_subgroupOf.mp hxS) (y : G) (Subgroup.mem_subgroupOf.mp hyS))
  have hcom' : ∀ z ∈ S₀ ⊓ centralizer (S₀ : Set ↥B), ∃ x ∈ S₀, ∃ y ∈ S₀,
      z = x * y * x⁻¹ * y⁻¹ := by
    intro z hz
    rw [wcgapk_inf_centralizer_subgroupOf S] at hz
    obtain ⟨x, hxS, y, hyS, hxy⟩ := hcom (z : G) (Subgroup.mem_subgroupOf.mp hz)
    refine ⟨⟨x, S.le_normalizer hxS⟩, hxS, ⟨y, S.le_normalizer hyS⟩, hyS, ?_⟩
    exact Subtype.ext hxy
  exact sylow_le_of_orderFive_aux hS hN hidx hd0 hfpf' hcomm' hcom'

theorem borelKills_center_of_irred {G : Type} [Group G] [Finite G] {S : Subgroup G}
    (hp : IsPGroup 2 S) (hbig : 8 * Nat.card ↥(S ⊓ centralizer (S : Set G)) < Nat.card S)
    (hirr : CenterIrred S) : BorelKills S (S ⊓ centralizer (S : Set G)) := by
  intro E _ hE W X _ ψ hψ φ
  let B := normalizer (S : Set G)
  let S₀ : Subgroup ↥B := S.subgroupOf B
  let N : Subgroup ↥B := φ.ker
  have hS : S₀.Normal := inferInstance
  have hN : N.Normal := inferInstance
  have hidx : N.index ∣ 168 := index_ker_dvd_168 hE W ψ hψ φ
  have hp' : IsPGroup 2 ↥S₀ :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := S) (K := B) S.le_normalizer).symm
  have hcardS : Nat.card ↥S₀ = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := S) (K := B) S.le_normalizer).toEquiv
  have hcardT : Nat.card ↥(S₀ ⊓ centralizer (S₀ : Set ↥B))
      = Nat.card ↥(S ⊓ centralizer (S : Set G)) := by
    rw [wcgapk_inf_centralizer_subgroupOf S]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show S ⊓ centralizer (S : Set G) ≤ B from inf_le_left.trans S.le_normalizer)).toEquiv
  have hbig' : 8 * Nat.card ↥(S₀ ⊓ centralizer (S₀ : Set ↥B)) < Nat.card ↥S₀ := by
    rw [hcardT, hcardS]
    exact hbig
  have hirr' : ∀ x ∈ S₀, x ∉ centralizer (S₀ : Set ↥B) → ∀ Z' : Subgroup ↥B,
      Z' ≤ S₀ ⊓ centralizer (S₀ : Set ↥B) →
      (∀ b : ↥B, ∀ z ∈ Z', b * z * b⁻¹ ∈ Z') →
      (∀ y ∈ S₀, x * y * x⁻¹ * y⁻¹ ∈ Z') →
      Z' = S₀ ⊓ centralizer (S₀ : Set ↥B) := by
    intro x hxS hxc Z' hZle hZinv hZcomm
    let Z'G : Subgroup G := Z'.map B.subtype
    have hxG : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hxS
    have hxcG : (x : G) ∉ centralizer (S : Set G) := fun hx =>
      hxc ((wcgapk_mem_centralizer_subgroupOf S x).mpr hx)
    have hZ'Gle : Z'G ≤ S ⊓ centralizer (S : Set G) := by
      intro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      have hwle : w ∈ S₀ ⊓ centralizer (S₀ : Set ↥B) := hZle hw
      exact ⟨Subgroup.mem_subgroupOf.mp hwle.1,
        (wcgapk_mem_centralizer_subgroupOf S w).mp hwle.2⟩
    have hZ'Ginv : ∀ b ∈ normalizer (S : Set G), ∀ z ∈ Z'G, b * z * b⁻¹ ∈ Z'G := by
      intro b hb z hz
      rw [Subgroup.mem_map] at hz ⊢
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨⟨b, hb⟩ * w * ⟨b, hb⟩⁻¹, hZinv ⟨b, hb⟩ w hw, rfl⟩
    have hZ'Gcomm : ∀ y ∈ S, (x : G) * y * (x : G)⁻¹ * y⁻¹ ∈ Z'G := by
      intro y hy
      rw [Subgroup.mem_map]
      exact ⟨x * ⟨y, S.le_normalizer hy⟩ * x⁻¹ * ⟨y, S.le_normalizer hy⟩⁻¹,
        hZcomm ⟨y, S.le_normalizer hy⟩ hy, rfl⟩
    have hZG : Z'G = S ⊓ centralizer (S : Set G) :=
      hirr (x : G) hxG hxcG Z'G hZ'Gle hZ'Ginv hZ'Gcomm
    rw [wcgapk_inf_centralizer_subgroupOf S]
    apply (Subgroup.map_subtype_inj).mp
    rw [Subgroup.map_subgroupOf_eq_of_le
      (show S ⊓ centralizer (S : Set G) ≤ B from inf_le_left.trans S.le_normalizer)]
    exact hZG
  have hle : S₀ ⊓ centralizer (S₀ : Set ↥B) ≤ N :=
    center_le_of_irred_aux hS hN hp' hidx hbig' hirr'
  rw [← wcgapk_inf_centralizer_subgroupOf S]
  exact hle

theorem centerIrred_of_klein {G : Type} [Group G] {S : Subgroup G}
    (hZ : Nat.card ↥(S ⊓ centralizer (S : Set G)) = 4) {h : G}
    (hh : h ∈ normalizer (S : Set G))
    (hfix : ∀ z ∈ S ⊓ centralizer (S : Set G), z ≠ 1 → h * z * h⁻¹ ≠ z) : CenterIrred S := by
  intro x hxS hxc Z' hZle hZinv hZcomm
  have hxc' : ¬ ∀ y ∈ S, y * x = x * y := fun h =>
    hxc (Subgroup.mem_centralizer_iff.mpr h)
  obtain ⟨y, hyimp⟩ := not_forall.mp hxc'
  obtain ⟨hyS, hyx⟩ := not_imp.mp hyimp
  set c : G := x * y * x⁻¹ * y⁻¹ with hcdef
  have hcZ' : c ∈ Z' := by rw [hcdef]; exact hZcomm y hyS
  have hcZ : c ∈ S ⊓ centralizer (S : Set G) := hZle hcZ'
  have hc1 : c ≠ 1 := by
    rw [hcdef]
    intro hc
    apply hyx
    have h1 : x * y * x⁻¹ = y := by
      have := congrArg (· * y) hc
      simpa [mul_assoc] using this
    have h2 : x * y = y * x := by
      have := congrArg (· * x) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have hfixc : h * c * h⁻¹ ≠ c := hfix c hcZ hc1
  have hconjZ' : h * c * h⁻¹ ∈ Z' := hZinv h hh c hcZ'
  have hconj1 : h * c * h⁻¹ ≠ 1 := by
    intro hh1
    apply hc1
    have := congrArg (fun t => h⁻¹ * t * h) hh1
    simpa [mul_assoc] using this
  have hnot1 : (1 : G) ∉ ({c, h * c * h⁻¹} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hc1 h.symm, fun h => hconj1 h.symm⟩
  have hncard3 : ({1, c, h * c * h⁻¹} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem hnot1, Set.ncard_pair (fun h => hfixc h.symm)]
  have hsub : ({1, c, h * c * h⁻¹} : Set G) ⊆ (Z' : Set G) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact Z'.one_mem
    · exact hcZ'
    · exact hconjZ'
  haveI : Finite ↥(S ⊓ centralizer (S : Set G)) :=
    Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have hZfin : (S ⊓ centralizer (S : Set G) : Set G).Finite := Set.toFinite _
  have hge3 : 3 ≤ Nat.card ↥Z' := by
    have := Set.ncard_le_ncard hsub (hZfin.subset hZle)
    rw [hncard3] at this
    exact this
  have hcarddvd : Nat.card ↥Z' ∣ 4 := by
    have := Subgroup.card_dvd_of_le hZle
    rwa [hZ] at this
  have hcard_eq : Nat.card ↥Z' = 4 := by
    have hle := Nat.le_of_dvd (by norm_num : 0 < 4) hcarddvd
    rcases lt_or_eq_of_le hle with hlt | heq
    · have hn3 : Nat.card ↥Z' = 3 := le_antisymm (Nat.lt_succ_iff.mp hlt) hge3
      rw [hn3] at hcarddvd
      norm_num at hcarddvd
    · exact heq
  exact Subgroup.eq_of_le_of_card_ge hZle (by rw [hZ, hcard_eq])

end CFSG.LocalAnalysis.WeakClosure81

end
