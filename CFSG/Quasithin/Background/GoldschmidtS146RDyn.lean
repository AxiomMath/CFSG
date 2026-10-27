module

public import CFSG.Quasithin.Background.GoldschmidtS146RAux

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {H J K S : Subgroup G} [(J.subgroupOf H).Normal]

theorem isSylowTwoOf_imgJ_sub (hKH : K ≤ H) (hS : IsSylowTwoOf S K) (hKJS : K ⊓ J ≤ S) :
    IsSylowTwoOf (imgJ H J S) (imgJ H J K) := by
  have hSK : S ≤ K := hS.1
  have hSH : S ≤ H := hSK.trans hKH
  refine ⟨imgJ_mono hSK, ?_, ?_⟩
  · have h1 : IsPGroup 2 ↥(S.subgroupOf H) :=
      hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
    exact IsPGroup.map h1 _
  · have hSJ : S ⊓ J = K ⊓ J := by
      refine le_antisymm (inf_le_inf_right J hSK) (le_inf hKJS inf_le_right)
    have e1 := card_imgJ_mul_inf (H := H) (J := J) hKH
    have e2 := card_imgJ_mul_inf (H := H) (J := J) hSH
    rw [hSJ] at e2
    have e3 : (imgJ H J S).relIndex (imgJ H J K) * Nat.card ↥(imgJ H J S) =
        Nat.card ↥(imgJ H J K) := by
      have := Subgroup.relIndex_mul_card (imgJ H J S) (imgJ H J K)
      rwa [inf_of_le_left (imgJ_mono hSK)] at this
    have e4 : S.relIndex K * Nat.card ↥S = Nat.card ↥K := by
      have := Subgroup.relIndex_mul_card S K
      rwa [inf_of_le_left hSK] at this
    have hpos : 0 < Nat.card ↥(K ⊓ J : Subgroup G) := Nat.card_pos
    have hSpos : 0 < Nat.card ↥S := Nat.card_pos
    have h5 : (imgJ H J S).relIndex (imgJ H J K) * Nat.card ↥S = S.relIndex K * Nat.card ↥S := by
      rw [e4, ← e1, ← e3, ← e2]
      ring
    have h6 : (imgJ H J S).relIndex (imgJ H J K) = S.relIndex K :=
      Nat.eq_of_mul_eq_mul_right hSpos h5
    change ¬ 2 ∣ (imgJ H J S).relIndex (imgJ H J K)
    rw [h6]
    exact hS.2.2

end Sylow

section Parabolic

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_isMaxParabolic2 {L S : Subgroup Y} (hS : IsSylowTwoOf S L)
    (hne : ¬ L ≤ Subgroup.normalizer (S : Set Y)) :
    ∃ P : Subgroup Y, IsMaxParabolic2 L P ∧ L ⊓ Subgroup.normalizer (S : Set Y) ≤ P ∧ P ≤ L ∧
      ∀ Q : Subgroup Y, Q ≤ L → Q ≠ L → P ≤ Q → Q = P := by
  have hne' : {Z : Subgroup Y | L ⊓ Subgroup.normalizer (S : Set Y) ≤ Z ∧ Z ≤ L ∧ Z ≠ L}.Nonempty :=
    ⟨L ⊓ Subgroup.normalizer (S : Set Y), le_rfl, inf_le_left, fun h => hne (h ▸ inf_le_right)⟩
  obtain ⟨P, ⟨hP1, hP2, hP3⟩, hmax⟩ := WellFounded.has_min wellFounded_gt _ hne'
  have hmax' : ∀ Q : Subgroup Y, Q ≤ L → Q ≠ L → P ≤ Q → Q = P := by
    intro Q hQL hQne hPQ
    by_contra hne''
    exact hmax Q ⟨hP1.trans hPQ, hQL, hQne⟩ (lt_of_le_of_ne hPQ (Ne.symm hne''))
  exact ⟨P, ⟨⟨hP2, S, hS, hP1⟩, hP3, fun Q hQ hQL hPQ => hmax' Q hQ.1 hQL hPQ⟩, hP1, hP2, hmax'⟩

end Parabolic

section Outer

variable {G : Type} [Group G] {H J K T : Subgroup G} [(J.subgroupOf H).Normal]

theorem conj_mem_imgJ {X : Subgroup G} {g : ↥H} (hg : (g : G) ∈ Subgroup.normalizer (X : Set G))
    {q : ↥H ⧸ J.subgroupOf H} (hq : q ∈ imgJ H J X) :
    (g : ↥H ⧸ J.subgroupOf H) * q * (g : ↥H ⧸ J.subgroupOf H)⁻¹ ∈ imgJ H J X := by
  obtain ⟨h, hh, rfl⟩ := mem_imgJ.mp hq
  refine mem_imgJ.mpr ⟨g * h * g⁻¹, ?_, ?_⟩
  · have := (Subgroup.mem_normalizer_iff.mp hg (h : G)).mp hh
    simpa using this
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem inducesOuter_of_not_normalizer {P : Subgroup (↥H ⧸ J.subgroupOf H)} (hKH : K ≤ H)
    (hTH : T ≤ H) (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hOJ : pCoreOf 2 K ≤ J)
    (hPB : imgJ H J K ⊓ Subgroup.normalizer ((imgJ H J (T ⊓ K) : Subgroup (↥H ⧸ J.subgroupOf H)) :
      Set (↥H ⧸ J.subgroupOf H)) ≤ P) (hPK : P ≤ imgJ H J K) {t : G} (ht : t ∈ T)
    (hnot : ((⟨t, hTH ht⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∉
      Subgroup.normalizer (P : Set (↥H ⧸ J.subgroupOf H))) : KbarInducesOuter K t := by
  intro k hk
  by_contra hcon
  push Not at hcon
  apply hnot
  set Q := ↥H ⧸ J.subgroupOf H with hQ
  let tb : Q := ((⟨t, hTH ht⟩ : ↥H) : Q)
  let kb : Q := ((⟨k, hKH hk⟩ : ↥H) : Q)
  have htN : (⟨t, hTH ht⟩ : ↥H).1 ∈ Subgroup.normalizer (K : Set G) := hTK ht
  have htinvN : ((⟨t, hTH ht⟩ : ↥H)⁻¹ : ↥H).1 ∈ Subgroup.normalizer (K : Set G) := by
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem htN
  have htN' : (⟨t, hTH ht⟩ : ↥H).1 ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hTK ht⟩
  have htinvN' : ((⟨t, hTH ht⟩ : ↥H)⁻¹ : ↥H).1 ∈
      Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    simpa using (Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)).inv_mem htN'
  have hC : ∀ q ∈ imgJ H J K, (tb * kb⁻¹) * q = q * (tb * kb⁻¹) := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_imgJ.mp hq
    have h1 := hcon (x : G) hx
    have h2 : (⁅t * k⁻¹, (x : G)⁆) ∈ J := hOJ h1
    have h3 : ((⟨t, hTH ht⟩ * ⟨k, hKH hk⟩⁻¹ * x * (⟨t, hTH ht⟩ * ⟨k, hKH hk⟩⁻¹)⁻¹ * x⁻¹ : ↥H) :
        Q) = 1 := by
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
      simpa [commutatorElement_def] using h2
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h3
    have h4 := mul_inv_eq_one.mp h3
    have h5 := mul_inv_eq_iff_eq_mul.mp h4
    simpa [tb, kb, mul_assoc] using h5
  have hkbKs : kb ∈ imgJ H J K := mem_imgJ.mpr ⟨⟨k, hKH hk⟩, hk, rfl⟩
  have hR : ∀ q ∈ imgJ H J K, tb * q * tb⁻¹ = kb * q * kb⁻¹ := by
    intro q hq
    have hq' : kb * q * kb⁻¹ ∈ imgJ H J K :=
      (imgJ H J K).mul_mem ((imgJ H J K).mul_mem hkbKs hq) ((imgJ H J K).inv_mem hkbKs)
    have h1 := hC _ hq'
    calc tb * q * tb⁻¹ = ((tb * kb⁻¹) * (kb * q * kb⁻¹)) * (tb * kb⁻¹)⁻¹ := by group
      _ = ((kb * q * kb⁻¹) * (tb * kb⁻¹)) * (tb * kb⁻¹)⁻¹ := by rw [h1]
      _ = kb * q * kb⁻¹ := by group
  have hR' : ∀ q ∈ imgJ H J K, tb⁻¹ * q * tb = kb⁻¹ * q * kb := by
    intro q hq
    have h1 := hC q hq
    calc tb⁻¹ * q * tb = kb⁻¹ * ((tb * kb⁻¹)⁻¹ * q * (tb * kb⁻¹)) * kb := by group
      _ = kb⁻¹ * ((tb * kb⁻¹)⁻¹ * (q * (tb * kb⁻¹))) * kb := by rw [mul_assoc ((tb * kb⁻¹)⁻¹)]
      _ = kb⁻¹ * ((tb * kb⁻¹)⁻¹ * ((tb * kb⁻¹) * q)) * kb := by rw [h1]
      _ = kb⁻¹ * q * kb := by group
  have hTKs : imgJ H J (T ⊓ K) ≤ imgJ H J K := imgJ_mono inf_le_right
  have hkbN : kb ∈ Subgroup.normalizer ((imgJ H J (T ⊓ K) : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      have h1 := conj_mem_imgJ (J := J) (g := ⟨t, hTH ht⟩) htN' hu
      rw [← hR u (hTKs hu)]
      exact h1
    · intro hw
      have hwK : kb * u * kb⁻¹ ∈ imgJ H J K := hTKs hw
      have h1 := conj_mem_imgJ (J := J) (g := (⟨t, hTH ht⟩ : ↥H)⁻¹) htinvN' hw
      have h2 : u = kb⁻¹ * (kb * u * kb⁻¹) * kb := by group
      have h3 := hR' _ hwK
      rw [h2, ← h3]
      simpa [QuotientGroup.mk_inv] using h1
  have hkbP : kb ∈ P := hPB ⟨hkbKs, hkbN⟩
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have hqK : q ∈ imgJ H J K := hPK hq
    rw [hR q hqK]
    exact P.mul_mem (P.mul_mem hkbP hq) (P.inv_mem hkbP)
  · intro hq
    have hqK' : tb * q * tb⁻¹ ∈ imgJ H J K := hPK hq
    have hqK : q ∈ imgJ H J K := by
      have h1 := conj_mem_imgJ (J := J) (g := (⟨t, hTH ht⟩ : ↥H)⁻¹) htinvN hqK'
      have h2 : tb⁻¹ * (tb * q * tb⁻¹) * tb = q := by group
      have h1' : tb⁻¹ * (tb * q * tb⁻¹) * tb ∈ imgJ H J K := by
        simpa [tb, QuotientGroup.mk_inv] using h1
      rwa [h2] at h1'
    rw [hR q hqK] at hq
    have h2 : q = kb⁻¹ * (kb * q * kb⁻¹) * kb := by group
    rw [h2]
    exact P.mul_mem (P.mul_mem (P.inv_mem hkbP) hq) hkbP

end Outer

end CFSG.Quasithin.GoldS146R
