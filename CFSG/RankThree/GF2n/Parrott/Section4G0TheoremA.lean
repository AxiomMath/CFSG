module

public import CFSG.RankThree.GF2n.Parrott.Section4G0Inf
public import CFSG.RankThree.GF2n.Parrott.CaseII

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

theorem centerIn_map_of_injective {K M : Type*} [Group K] [Group M] (ι : K →* M)
    (hι : Function.Injective ι) (Q : Subgroup K) :
    centerIn (Q.map ι) = (centerIn Q).map ι := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨q, hq, rfl⟩ := hxQ
    refine ⟨q, Subgroup.mem_inf.mpr ⟨hq, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp hxC (ι y) ⟨y, hy, rfl⟩
    exact hι (by simpa [map_mul] using this)
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨hqQ, hqC⟩ := Subgroup.mem_inf.mp hq
    refine Subgroup.mem_inf.mpr ⟨⟨q, hqQ, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp hqC y hy
    simpa [map_mul] using congrArg ι this

theorem isExtraspecial2_of_map {K M : Type} [Group K] [Group M] (ι : K →* M)
    (hι : Function.Injective ι) {Q : Subgroup K} (h : IsExtraspecial2 (Q.map ι)) :
    IsExtraspecial2 Q := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.of_equiv (Q.equivMapOfInjective ι hι).symm, ?_, ?_⟩
  · rw [← CFSG.centerIn_eq_map_center]
    rw [← CFSG.centerIn_eq_map_center, centerIn_map_of_injective ι hι Q,
      ← Subgroup.map_commutator] at h2
    exact Subgroup.map_injective hι h2
  · rw [← Subgroup.map_commutator] at h3
    rwa [Subgroup.card_map_of_injective hι] at h3

section G0

variable {G : Type} [Group G] [Finite G] {z : G} {G₀ : Subgroup G}

theorem map_H_G₀ (hzG₀ : z ∈ G₀) :
    (H (⟨z, hzG₀⟩ : ↥G₀)).map G₀.subtype = H z ⊓ G₀ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, y.2⟩
    rw [H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
  · intro hx
    obtain ⟨hxH, hxG₀⟩ := Subgroup.mem_inf.mp hx
    refine ⟨⟨x, hxG₀⟩, ?_, rfl⟩
    show (⟨x, hxG₀⟩ : ↥G₀) ∈ Subgroup.centralizer ({(⟨z, hzG₀⟩ : ↥G₀)} : Set ↥G₀)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxH)

theorem map_J_G₀ (hG₀ : G₀.Normal) (hzG₀ : z ∈ G₀) :
    (J (⟨z, hzG₀⟩ : ↥G₀)).map G₀.subtype = J z ⊓ G₀ := by
  have h1 : (J (⟨z, hzG₀⟩ : ↥G₀)).map G₀.subtype =
      inSubgroup (pCore 2) ((H (⟨z, hzG₀⟩ : ↥G₀)).map G₀.subtype) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore_of_injective 2 G₀.subtype
      G₀.subtype_injective _
  rw [h1, map_H_G₀ hzG₀]
  exact inSubgroup_pCore_inf_normal z hG₀

end G0

theorem eq_of_commute_of_sup_pPrimeCore_eq_top {K : Type*} [Group K] [Finite K] {w : K}
    (hw : orderOf w = 2) (hsup : Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤)
    (g : K) (hcomm : (g * w * g⁻¹) * w = w * (g * w * g⁻¹)) : g * w * g⁻¹ = w := by
  have hOn : (pPrimeCore 2 K).Normal := pPrimeCore_normal
  have hw2 : w * w = 1 := by
    have h1 := pow_orderOf_eq_one w
    rwa [hw, pow_two] at h1
  have hg : g ∈ Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K := hsup ▸ Subgroup.mem_top g
  have hmul := Subgroup.mul_normal (Subgroup.centralizer ({w} : Set K)) (pPrimeCore 2 K)
  rw [← SetLike.mem_coe, hmul] at hg
  obtain ⟨c, hc, o, ho, rfl⟩ := hg
  have hcw : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hu : o * w * o⁻¹ * w⁻¹ ∈ pPrimeCore 2 K := by
    have h1 : o * w * o⁻¹ * w⁻¹ = o * (w * o⁻¹ * w⁻¹) := by group
    rw [h1]
    exact Subgroup.mul_mem _ ho (hOn.conj_mem _ (inv_mem ho) w)
  have hu' : c * (o * w * o⁻¹ * w⁻¹) * c⁻¹ ∈ pPrimeCore 2 K := hOn.conj_mem _ hu c
  obtain ⟨u', hu'O, hy⟩ : ∃ u' ∈ pPrimeCore 2 K, c * o * w * (c * o)⁻¹ = u' * w := by
    refine ⟨c * (o * w * o⁻¹ * w⁻¹) * c⁻¹, hu', ?_⟩
    have hcwc : c * w * c⁻¹ = w := by
      calc c * w * c⁻¹ = w * c * c⁻¹ := by rw [hcw]
        _ = w := by group
    calc c * o * w * (c * o)⁻¹ = c * (o * w * o⁻¹ * w⁻¹) * c⁻¹ * (c * w * c⁻¹) := by group
      _ = c * (o * w * o⁻¹ * w⁻¹) * c⁻¹ * w := by rw [hcwc]
  rw [hy] at hcomm ⊢
  have hcomm' : u' * w = w * u' := by
    have h1 : u' * w * w = w * u' * w := by
      calc u' * w * w = w * (u' * w) := hcomm
        _ = w * u' * w := by rw [mul_assoc]
    exact mul_right_cancel h1
  have hy2 : (u' * w) * (u' * w) = 1 := by
    have h1 : (c * o * w * (c * o)⁻¹) * (c * o * w * (c * o)⁻¹) = 1 := by
      calc (c * o * w * (c * o)⁻¹) * (c * o * w * (c * o)⁻¹)
          = (c * o) * (w * w) * (c * o)⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    rwa [hy] at h1
  have hu2 : u' * u' = 1 := by
    calc u' * u' = u' * u' * (w * w) := by rw [hw2, mul_one]
      _ = u' * (u' * w) * w := by group
      _ = u' * (w * u') * w := by rw [hcomm']
      _ = (u' * w) * (u' * w) := by group
      _ = 1 := hy2
  have hu1 : u' = 1 := by
    have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 K)) := pPrimeCore_coprime_card
    have hmem : u' ∈ pPrimeCore 2 K := hu'O
    have hord : orderOf u' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu2)
    have hord' : orderOf u' ∣ Nat.card (pPrimeCore 2 K) := by
      have := Subgroup.orderOf_dvd_natCard (pPrimeCore 2 K) hmem
      exact this
    have : orderOf u' ∣ 1 := by
      have := Nat.dvd_gcd hord hord'
      rwa [hcop.gcd_eq_one] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  rw [hu1, one_mul]

section G0Quotient

variable {G : Type} [Group G] [Finite G] {z : G} {G₀ : Subgroup G}

theorem nonempty_quotientData_G₀ (h : Tim79a.ParrottHyp z) (hG₀n : G₀.Normal)
    (hG₀i : G₀.index = 2) {z₁ : G} (hz₁ : z₁ ∈ J z) (hz₁G₀ : z₁ ∉ G₀) (hzG₀ : z ∈ G₀) :
    Nonempty (QuotientData (⟨z, hzG₀⟩ : ↥G₀) (J_subgroupOf_normal (⟨z, hzG₀⟩ : ↥G₀))) := by
  obtain ⟨hN, ⟨D⟩⟩ := parrottQuotientDataExists h
  let D' : QuotientData z (J_subgroupOf_normal z) := D
  let w : ↥G₀ := ⟨z, hzG₀⟩
  have hHw : ∀ x : ↥(H w), ((x : ↥G₀) : G) ∈ H z := fun x => by
    have h1 := Subgroup.mem_map_of_mem G₀.subtype x.2
    rw [map_H_G₀ hzG₀] at h1
    exact h1.1
  let ι' : ↥(H w) →* ↥(H z) :=
    MonoidHom.codRestrict (G₀.subtype.comp (H w).subtype) (H z) hHw
  let φ : ↥(H w) →* MulAut D'.X :=
    D'.iso.toMonoidHom.comp ((QuotientGroup.mk' ((J z).subgroupOf (H z))).comp ι')
  have hJw : ∀ y : ↥G₀, y ∈ J w ↔ (y : G) ∈ J z := by
    intro y
    rw [← Subgroup.mem_map_iff_mem G₀.subtype_injective, map_J_G₀ hG₀n hzG₀]
    exact ⟨fun h1 => h1.1, fun h1 => Subgroup.mem_inf.mpr ⟨h1, y.2⟩⟩
  have hker : φ.ker = (J w).subgroupOf (H w) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hJw]
    constructor
    · intro hx
      have h1 : QuotientGroup.mk' ((J z).subgroupOf (H z)) (ι' x) = 1 :=
        (D'.iso.map_eq_one_iff).mp hx
      have h2 : ι' x ∈ (J z).subgroupOf (H z) := (QuotientGroup.eq_one_iff _).mp h1
      exact Subgroup.mem_subgroupOf.mp h2
    · intro hx
      have h2 : ι' x ∈ (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hx
      have h1 : QuotientGroup.mk' ((J z).subgroupOf (H z)) (ι' x) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h2
      exact (D'.iso.map_eq_one_iff).mpr h1
  have hφ : Function.Surjective φ := by
    intro a
    obtain ⟨q, rfl⟩ := D'.iso.surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    by_cases hy : (y : G) ∈ G₀
    · refine ⟨⟨⟨y, hy⟩, ?_⟩, ?_⟩
      · show (⟨y, hy⟩ : ↥G₀) ∈ Subgroup.centralizer ({w} : Set ↥G₀)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.2)
      · rfl
    · have hyz : (y : G) * z₁ ∈ G₀ :=
        (Subgroup.mul_mem_iff_of_index_two hG₀i).mpr (iff_of_false hy hz₁G₀)
      have hyzH : (y : G) * z₁ ∈ H z := Subgroup.mul_mem _ y.2 (J_le_H hz₁)
      refine ⟨⟨⟨(y : G) * z₁, hyz⟩, ?_⟩, ?_⟩
      · show (⟨(y : G) * z₁, hyz⟩ : ↥G₀) ∈ Subgroup.centralizer ({w} : Set ↥G₀)
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyzH)
      · show D'.iso (QuotientGroup.mk (⟨(y : G) * z₁, hyzH⟩ : ↥(H z))) = D'.iso (QuotientGroup.mk y)
        congr 1
        rw [QuotientGroup.eq]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have : (((⟨(y : G) * z₁, hyzH⟩ : ↥(H z))⁻¹ * y : ↥(H z)) : G) = z₁⁻¹ := by
          simp
        rw [this]
        exact inv_mem hz₁
  exact ⟨{ X := D'.X
           instX := D'.instX
           lie := D'.lie
           iso := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
             (QuotientGroup.quotientKerEquivOfSurjective φ hφ) }⟩

end G0Quotient

section G0HypA

variable {G : Type} [Group G] [Finite G] {z : G} {G₀ : Subgroup G}

theorem parrottHypA_G₀ (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z))
    {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z)
    (hz₁2 : orderOf z₁ = 2) (hG₀n : G₀.Normal) (hG₀i : G₀.index = 2) (hzG₀ : z ∈ G₀)
    (hz₁G₀ : z₁ ∉ G₀) : Tim79a.ParrottHypA (⟨z, hzG₀⟩ : ↥G₀) := by
  refine ⟨?_, ?_, ?_, ?_, nonempty_quotientData_G₀ h hG₀n hG₀i hz₁.1 hz₁G₀ hzG₀⟩
  · apply isExtraspecial2_of_map G₀.subtype G₀.subtype_injective
    rw [map_J_G₀ hG₀n hzG₀]
    exact isExtraspecial2_J_inf h hz₁ hz₁z hz₁2 hG₀i hzG₀ hz₁G₀
  · have h1 := card_J_inf h hz₁.1 hG₀i hz₁G₀
    rw [← map_J_G₀ hG₀n hzG₀, Subgroup.card_map_of_injective G₀.subtype_injective] at h1
    exact h1
  · apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_commutator, map_J_G₀ hG₀n hzG₀, commutator_J_inf h hz₁ hz₁2 hG₀i hz₁G₀,
      MonoidHom.map_zpowers]
    rfl
  · intro x hx
    obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
    have h1 := Subgroup.mem_map_of_mem G₀.subtype hxH
    rw [map_H_G₀ hzG₀] at h1
    have h2 : (x : G) ∈ Subgroup.centralizer ((J z ⊓ G₀ : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [← map_J_G₀ hG₀n hzG₀] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxC y' hy')
    have h3 := centralizer_inf_le_J_inf h hZ hz₁ hz₁2 hG₀i hz₁G₀ (Subgroup.mem_inf.mpr ⟨h1, h2⟩)
    rw [← Subgroup.mem_map_iff_mem G₀.subtype_injective, map_J_G₀ hG₀n hzG₀]
    exact h3

theorem exists_G₁_of_theoremA
    (hA : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X))
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hz₁2 : orderOf z₁ = 2)
    (hG₀n : G₀.Normal) (hG₀i : G₀.index = 2) (hzG₀ : z ∈ G₀) (hz₁G₀ : z₁ ∉ G₀)
    (hfuse : ∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) :
    ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
      (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
      ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
        Nonempty (↥G₁ ≃* X) := by
  have hHypA := parrottHypA_G₀ h hZ hz₁ hz₁z hz₁2 hG₀n hG₀i hzG₀ hz₁G₀
  rcases hA ↥G₀ ⟨z, hzG₀⟩ hHypA with hsup | ⟨K₁, hK₁i, hK₁c, X, _, hX, ⟨e⟩⟩
  · exfalso
    obtain ⟨g, hg, hgH, hgz⟩ := hfuse
    apply hgz
    have hord : orderOf (⟨z, hzG₀⟩ : ↥G₀) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact h.1
    have hcomm : (⟨g, hg⟩ * ⟨z, hzG₀⟩ * ⟨g, hg⟩⁻¹ : ↥G₀) * ⟨z, hzG₀⟩ =
        ⟨z, hzG₀⟩ * (⟨g, hg⟩ * ⟨z, hzG₀⟩ * ⟨g, hg⟩⁻¹ : ↥G₀) :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgH)
    have := eq_of_commute_of_sup_pPrimeCore_eq_top hord hsup ⟨g, hg⟩ hcomm
    exact congrArg Subtype.val this
  · refine ⟨K₁.map G₀.subtype, Subgroup.map_subtype_le _, ?_, ?_, X, _, hX,
      ⟨(K₁.equivMapOfInjective G₀.subtype G₀.subtype_injective).symm.trans e⟩⟩
    · have h1 := Subgroup.relIndex_map_map_of_injective K₁ ⊤ G₀.subtype_injective
        (f := G₀.subtype)
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, Subgroup.relIndex_top_right,
        hK₁i] at h1
      exact h1
    · intro c hc hcx
      have := hK₁c ⟨c, hc⟩ (fun x hx => Subtype.ext (hcx x ⟨x, hx, rfl⟩))
      exact congrArg Subtype.val this

theorem hB5_of_theoremA
    (hA : ∀ (K : Type) [Group K] [Finite K] (w : K), Tim79a.ParrottHypA w →
      Subgroup.centralizer ({w} : Set K) ⊔ pPrimeCore 2 K = ⊤ ∨
      ∃ K₁ : Subgroup K, K₁.index = 2 ∧ (∀ c : K, (∀ x ∈ K₁, c * x = x * c) → c = 1) ∧
        ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥K₁ ≃* X))
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) = centerIn (H z)) :
    ∀ z₁ ∈ centerIn (J z), z₁ ∉ Subgroup.zpowers z → orderOf z₁ = 2 →
      ∀ G₀ : Subgroup G, G₀.Normal → G₀.index = 2 → z ∈ G₀ → z₁ ∉ G₀ →
        (∃ g ∈ G₀, g * z * g⁻¹ ∈ H z ∧ g * z * g⁻¹ ≠ z) →
        ∃ G₁ : Subgroup G, G₁ ≤ G₀ ∧ G₁.relIndex G₀ = 2 ∧
          (∀ c ∈ G₀, (∀ x ∈ G₁, c * x = x * c) → c = 1) ∧
          ∃ (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
            Nonempty (↥G₁ ≃* X) :=
  fun _ hz₁ hz₁z hz₁2 _ hG₀n hG₀i hzG₀ hz₁G₀ hfuse =>
    exists_G₁_of_theoremA hA h hZ hz₁ hz₁z hz₁2 hG₀n hG₀i hzG₀ hz₁G₀ hfuse

end G0HypA

end CFSG.RankThree.GF2n.Parrott
