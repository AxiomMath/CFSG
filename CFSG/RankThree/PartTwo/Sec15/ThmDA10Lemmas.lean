module

public import CFSG.RankThree.PartTwo.Sec15.ThmDA10Setup
public import CFSG.RankThree.PartTwo.Sec15.ThmDFrattini
public import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
theorem psiOf_eq_one_of_mem {A Y : Subgroup G} (hA3 : IsPGroup 3 A) (hAY : A ≤ Y)
    (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) {a : ↥Y} (ha : (a : G) ∈ A)
    (h : psiOf Y e a = 1) : a = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha' : a ∈ CFSG.pPrimeCore 3 ↥Y := (psiOf_eq_one_iff Y e a).mp h
  have hmem : (a : G) ∈ pPrimeCoreOf 3 Y := Subgroup.mem_map.mpr ⟨a, ha', rfl⟩
  have hcop : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 Y)
  have hbot : A ⊓ pPrimeCoreOf 3 Y = ⊥ := inf_eq_bot_of_isPGroup_of_not_dvd hcop hA3
  have hmem' : (a : G) ∈ A ⊓ pPrimeCoreOf 3 Y := Subgroup.mem_inf.mpr ⟨ha, hmem⟩
  rw [hbot, Subgroup.mem_bot] at hmem'
  exact Subtype.ext hmem'

theorem exists_omega_conj_subgroupOf {A Y F : Subgroup G} (hAY : A ≤ Y) (hF : F ∈ omegaA A)
    {m : ↥Y} (hm : m ∈ Subgroup.normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y)) :
    ∃ F₂ ∈ omegaA A, (F.subgroupOf Y).map (MulAut.conj m).toMonoidHom = F₂.subgroupOf Y := by
  have hFA : F ≤ A := (Sec13.mem_omegaA_iff.mp hF).1
  have hA : ∀ g : ↥Y, g ∈ Subgroup.normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) →
      ∀ h ∈ A, (g : G) * h * (g : G)⁻¹ ∈ A := by
    intro g hg h hh
    have h' : (⟨h, hAY hh⟩ : ↥Y) ∈ A.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hh
    have h2 : (g * ⟨h, hAY hh⟩ * g⁻¹ : ↥Y) ∈ A.subgroupOf Y :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp h'
    have h3 := Subgroup.mem_subgroupOf.mp h2
    simpa using h3
  have hg : (m : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hA m hm x
    · intro hx
      have h2 := hA m⁻¹ (inv_mem hm) ((m : G) * x * (m : G)⁻¹) hx
      have e : ((m⁻¹ : ↥Y) : G) * ((m : G) * x * (m : G)⁻¹) * ((m⁻¹ : ↥Y) : G)⁻¹ = x := by
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rw [e] at h2
      exact h2
  refine ⟨F.map (MulAut.conj (m : G)).toMonoidHom,
    (Sec13.map_conj_mem_omegaA_iff hg).mpr hF, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map.mpr ⟨(y : G), Subgroup.mem_subgroupOf.mp hy, ?_⟩)
    simp
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    refine Subgroup.mem_map.mpr ⟨⟨z, hAY (hFA hz)⟩, Subgroup.mem_subgroupOf.mpr hz, ?_⟩
    apply Subtype.ext
    simpa using hzx

theorem exists_lift_psiOf {A Y : Subgroup G} (hA3 : IsPGroup 3 A)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAY : A ≤ Y)
    (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) {n : alternatingGroup (Fin 10)}
    (hn : n ∈ Subgroup.normalizer
      (((A.subgroupOf Y).map (psiOf Y e) : Subgroup (alternatingGroup (Fin 10))) :
        Set (alternatingGroup (Fin 10)))) :
    ∃ m ∈ Subgroup.normalizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y),
      ∀ a ∈ A.subgroupOf Y, psiOf Y e (m * a * m⁻¹) = n * psiOf Y e a * n⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥Y) :=
    (Nat.prime_three.coprime_iff_not_dvd).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y))
  have hA : IsPGroup 3 (A.subgroupOf Y) := hA3.comap_subtype
  have hAab' : ∀ a ∈ A.subgroupOf Y, ∀ b ∈ A.subgroupOf Y, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hAab _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb))
  obtain ⟨y₀, hy₀⟩ := psiOf_surjective Y e n
  have hy : ∀ a ∈ A.subgroupOf Y,
      QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) (y₀ * a * y₀⁻¹) ∈
        (A.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) := by
    intro a ha
    have hmem : psiOf Y e a ∈
        ((A.subgroupOf Y).map (psiOf Y e) : Subgroup (alternatingGroup (Fin 10))) :=
      Subgroup.mem_map_of_mem _ ha
    have hconj : n * psiOf Y e a * n⁻¹ ∈
        ((A.subgroupOf Y).map (psiOf Y e) : Subgroup (alternatingGroup (Fin 10))) :=
      (Subgroup.mem_normalizer_iff.mp hn (psiOf Y e a)).mp hmem
    have hcomp : n * psiOf Y e a * n⁻¹ = psiOf Y e (y₀ * a * y₀⁻¹) := by
      rw [← hy₀, map_mul, map_mul, map_inv]
    rw [hcomp] at hconj
    obtain ⟨a', ha', h'⟩ := Subgroup.mem_map.mp hconj
    exact Subgroup.mem_map.mpr ⟨a', ha', psiOf_injective_quot Y e h'⟩
  obtain ⟨m, hm, hmeq⟩ :=
    exists_normalizer_lift (N := CFSG.pPrimeCore 3 ↥Y) (A := A.subgroupOf Y) hN hA hAab' y₀ hy
  refine ⟨m, hm, fun a ha => ?_⟩
  have h1 : psiOf Y e (m * a * m⁻¹) = psiOf Y e (y₀ * a * y₀⁻¹) := by
    show e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) (m * a * m⁻¹)) =
      e (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y) (y₀ * a * y₀⁻¹))
    rw [hmeq a ha]
  rw [h1, map_mul, map_mul, map_inv, hy₀]

theorem zpowers_subgroupOf {Y : Subgroup G} {c : G} (hc : c ∈ Y) :
    Subgroup.zpowers (⟨c, hc⟩ : ↥Y) = (Subgroup.zpowers c).subgroupOf Y := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem exists_threeCycle_point (hK7 : A7CentralizerThreeCycle) {A Y : Subgroup G}
    (hA3 : IsPGroup 3 A) (hAY : A ≤ Y)
    (e : ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) (hK : Print148FourK A Y) :
    ∃ c' ∈ A, ∃ hc' : c' ∈ Y, Subgroup.zpowers c' ∈ omegaA A ∧
      ((psiOf Y e ⟨c', hc'⟩ : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).IsThreeCycle := by
  obtain ⟨c', hc'A, hc'Ω, K, hKle, ⟨ι⟩⟩ := hK
  have hc' : c' ∈ Y := hAY hc'A
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf c' = 3 :=
    (Nat.card_zpowers c').symm.trans
      (CFSG.RankThree.PartTwo.Sec13.zpowers_mem_omegaA_iff.mp hc'Ω).2.1
  have hc1 : c' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    norm_num at hord
  have hN : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 Y) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.RankThree.PartTwo.Sec14.coprime_card_pPrimeCoreOf 3 Y)
  have hinf : A ⊓ pPrimeCoreOf 3 Y = ⊥ :=
    CFSG.RankThree.PartTwo.Sec15.ThmD.inf_eq_bot_of_isPGroup_of_not_dvd hN hA3
  have hx1 : psiOf Y e ⟨c', hc'⟩ ≠ 1 := by
    intro h
    have hmem : (⟨c', hc'⟩ : ↥Y) ∈ CFSG.pPrimeCore 3 ↥Y := (psiOf_eq_one_iff Y e _).mp h
    have hmem' : c' ∈ A ⊓ pPrimeCoreOf 3 Y :=
      ⟨hc'A, Subgroup.mem_map.mpr ⟨⟨c', hc'⟩, hmem, rfl⟩⟩
    rw [hinf, Subgroup.mem_bot] at hmem'
    exact hc1 hmem'
  have hc3 : c' ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one c'
  have hy3 : (⟨c', hc'⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
  have hx3 : psiOf Y e ⟨c', hc'⟩ ^ 3 = 1 := by
    rw [← map_pow, hy3, map_one]
  have hord3 : orderOf (psiOf Y e ⟨c', hc'⟩) = 3 := orderOf_eq_prime hx3 hx1
  have hι : Nonempty (↥(((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).map
      e.toMonoidHom) ≃* alternatingGroup (Fin 7)) :=
    ⟨(Subgroup.equivMapOfInjective ((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))
      e.toMonoidHom e.injective).symm.trans ι⟩
  have hcent : psiOf Y e ⟨c', hc'⟩ ∈ Subgroup.centralizer
      ((((K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).map e.toMonoidHom :
        Subgroup (alternatingGroup (Fin 10))) : Set (alternatingGroup (Fin 10))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    rw [Subgroup.mem_map] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    have hvK : (v : G) ∈ K := Subgroup.mem_subgroupOf.mp hv
    have hcomm : (v : G) * c' = c' * (v : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKle hvK).2
    have hC : Commute v (⟨c', hc'⟩ : ↥Y) := by
      show v * (⟨c', hc'⟩ : ↥Y) = (⟨c', hc'⟩ : ↥Y) * v
      exact Subtype.ext (by simp only [Subgroup.coe_mul]; exact hcomm)
    exact (hC.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y))).map e
  exact ⟨c', hc'A, hc', hc'Ω, hK7 _ hι _ hcent hord3⟩

end CFSG.RankThree.PartTwo.Sec15.ThmD
