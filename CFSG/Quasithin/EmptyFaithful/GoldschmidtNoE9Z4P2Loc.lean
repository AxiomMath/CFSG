module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Defs
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique
open scoped Pointwise

namespace E9P2.Loc

section Basic

variable {X : Type} [Group X]

theorem mem_normalizer_inf {A B : Subgroup X} {x : X} (hA : x ∈ Subgroup.normalizer (A : Set X))
    (hB : x ∈ Subgroup.normalizer (B : Set X)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro n
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA n, hB n]

theorem mem_normalizer_of_normal {L : Subgroup X} (hL : L.Normal) (x : X) :
    x ∈ Subgroup.normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hL.conj_mem n hn x, fun hn => ?_⟩
  have h1 := hL.conj_mem _ hn x⁻¹
  rwa [show x⁻¹ * (x * n * x⁻¹) * x⁻¹⁻¹ = n by group] at h1

theorem isSolvable_sup {A B : Subgroup X} (hAB : A ≤ Subgroup.normalizer (B : Set X))
    (hA : Group.IsSolvable ↥A) (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥(A ⊔ B) := by
  set Y := A ⊔ B
  have hBY : B ≤ Y := le_sup_right
  have hAY : A ≤ Y := le_sup_left
  have hBn : (B.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hAB
  have hBs : Group.IsSolvable ↥(B.subgroupOf Y) :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hBY).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hBY).symm.surjective
  have hmul : (↑(A ⊔ B) : Set X) = ↑A * ↑B := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  let ψ : ↥A →* ↥Y ⧸ B.subgroupOf Y :=
    (QuotientGroup.mk' (B.subgroupOf Y)).comp (Subgroup.inclusion hAY)
  have hψ : Function.Surjective ψ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : X) ∈ (↑(A ⊔ B) : Set X) := y.2
      rw [hmul] at hy
      obtain ⟨a, ha, b, hb, hab⟩ := hy
      refine ⟨⟨a, ha⟩, ?_⟩
      show (QuotientGroup.mk (Subgroup.inclusion hAY ⟨a, ha⟩) : ↥Y ⧸ B.subgroupOf Y) =
        QuotientGroup.mk y
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      show ((Subgroup.inclusion hAY ⟨a, ha⟩ : ↥Y) : X)⁻¹ * (y : X) ∈ B
      have : ((Subgroup.inclusion hAY ⟨a, ha⟩ : ↥Y) : X)⁻¹ * (y : X) = b := by
        show a⁻¹ * (y : X) = b
        rw [← hab]; group
      rw [this]
      exact hb
  have : Group.IsSolvable (↥Y ⧸ B.subgroupOf Y) := Group.isSolvable_of_surjective hψ
  exact Group.isSolvable_of_ker_le_range (B.subgroupOf Y).subtype
    (QuotientGroup.mk' (B.subgroupOf Y)) (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem card_mul_relIndex {H K : Subgroup X} (hHK : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have := Subgroup.card_mul_index (H.subgroupOf K)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv] at this

end Basic

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem not_two_dvd_relIndex_inf {Th L : Subgroup X} (hT : IsSylowTwoOf Th ⊤) (hL : L.Normal) :
    ¬ 2 ∣ (Th ⊓ L).relIndex L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ Th.index := by
    have h2 : ¬ 2 ∣ Th.relIndex ⊤ := hT.2.2
    rwa [Subgroup.relIndex_top_right] at h2
  obtain ⟨P, hP⟩ := exists_sylow_map_eq_inf_of_normal (hT.2.1.toSylow hidx) L
  have hPeq : (P : Subgroup L) = (Th ⊓ L).subgroupOf L := by
    apply Subgroup.map_injective L.subtype_injective
    rw [hP, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
    rfl
  have := P.not_dvd_index
  rwa [hPeq] at this

theorem isSylowTwoOf_inf_subgroupOf {Th L : Subgroup X} (hT : IsSylowTwoOf Th ⊤)
    (hL : L.Normal) : IsSylowTwoOf ((Th ⊓ L).subgroupOf L) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact (hT.2.1.to_inf_left (K := L)).of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  · show ¬ 2 ∣ ((Th ⊓ L).subgroupOf L).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact not_two_dvd_relIndex_inf hT hL

end Sylow

end E9P2.Loc

section Local

variable {X : Type} [Group X]

theorem E9Local.normalizes_of_E {L Th Hh Eh R : Subgroup X} (h : E9Local L Th Hh Eh R)
    (hE : ∀ e ∈ Eh, e ∈ Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X)) :
    ∀ x ∈ Hh, x ∈ Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) := by
  intro x hx
  obtain ⟨e, he, t, ht, rfl⟩ := h.dec x hx
  exact mul_mem (hE e he) (E9P2.Loc.mem_normalizer_inf (Subgroup.le_normalizer ht)
    (E9P2.Loc.mem_normalizer_of_normal h.normal_L t))

end Local

section LocalFinite

variable {X : Type} [Group X] [Finite X]

theorem E9Local.normalizer_le {L Th Hh Eh R : Subgroup X} (h : E9Local L Th Hh Eh R)
    (hX : ∀ x : X, ∃ l ∈ L, ∃ t ∈ Th, x = l * t)
    (hHU : ∀ x ∈ Hh, x ∈ Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X))
    (hNs : Group.IsSolvable ↥(Subgroup.normalizer ((Th ⊓ L : Subgroup X) : Set X) ⊓ L))
    (hr : ∀ A : Subgroup X, Hh ≤ A → Group.IsSolvable ↥A → ∀ r : ℕ, r.Prime → r ∣ Nat.card A →
      r = 2 ∨ r = 3)
    (hL3 : ∀ P : Subgroup X, P ≤ L → IsPGroup 3 ↥P → Nat.card P ≤ 9)
    {T0 : Subgroup X} (hRT0 : R ≤ T0) (hT0 : T0 ≤ Th) :
    Subgroup.normalizer (T0 : Set X) ≤ Hh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U : Subgroup X := Th ⊓ L with hU
  set N : Subgroup X := Subgroup.normalizer (U : Set X) ⊓ L with hN
  have hU2 : IsPGroup 2 ↥U := h.sylow_T.2.1.to_inf_left
  have hUR : U ≤ R := h.R_max U hU2 fun x hx => hHU x hx
  have hRH : R ≤ Hh := h.R_le_T.trans h.T_le
  have hUN : U ≤ N := fun u hu => ⟨Subgroup.le_normalizer hu, hu.2⟩
  have hEN : Eh ≤ N := fun e he => ⟨hHU e (h.E_le_H he), h.E_le_L he⟩
  have hNL : N ≤ L := inf_le_right
  have hHN : Hh ≤ Subgroup.normalizer (N : Set X) := fun x hx =>
    E9P2.Loc.mem_normalizer_inf (Subgroup.le_normalizer (hHU x hx))
      (E9P2.Loc.mem_normalizer_of_normal h.normal_L x)
  have hodd : ¬ 2 ∣ U.relIndex L := E9P2.Loc.not_two_dvd_relIndex_inf h.sylow_T h.normal_L
  have hcardN : Nat.card U * U.relIndex N = Nat.card N := E9P2.Loc.card_mul_relIndex hUN
  have hdvd : U.relIndex N ∣ U.relIndex L :=
    ⟨N.relIndex L, (Subgroup.relIndex_mul_relIndex U N L hUN hNL).symm⟩
  set m := U.relIndex N with hm
  have hmodd : ¬ 2 ∣ m := fun h2 => hodd (h2.trans hdvd)
  have hsolv : Group.IsSolvable ↥(Hh ⊔ N) := E9P2.Loc.isSolvable_sup hHN h.solv_H hNs
  have hprime : ∀ r : ℕ, r.Prime → r ∣ Nat.card N → r = 2 ∨ r = 3 := fun r hr' hrN =>
    hr (Hh ⊔ N) le_sup_left hsolv r hr' (hrN.trans (Subgroup.card_dvd_of_le le_sup_right))
  have hm0 : m ≠ 0 := by
    rintro h0
    have : 0 < Nat.card N := Nat.card_pos
    rw [h0, mul_zero] at hcardN
    omega
  have hm3 : ∀ {d : ℕ}, d.Prime → d ∣ m → d = 3 := by
    intro d hd hdm
    have hdN : d ∣ Nat.card N := hcardN ▸ Dvd.dvd.mul_left hdm _
    rcases hprime d hd hdN with rfl | rfl
    · exact absurd hdm hmodd
    · rfl
  have hmpow : m = 3 ^ m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hm0 hm3
  have hm9 : m ≤ 9 := by
    have hdvd3 : 3 ^ m.primeFactorsList.length ∣ Nat.card N := by
      rw [← hmpow, ← hcardN]
      exact Dvd.intro_left _ rfl
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 3 hdvd3
    have hP3 : IsPGroup 3 ↥(K.map N.subtype) := (IsPGroup.of_card hK).map N.subtype
    have := hL3 (K.map N.subtype) ((Subgroup.map_subtype_le K).trans hNL) hP3
    rwa [Subgroup.card_map_of_injective N.subtype_injective, hK, ← hmpow] at this
  set M : Subgroup X := Hh ⊓ N with hM
  have hUM : U ≤ M := le_inf (hUR.trans hRH) hUN
  have hEM : Eh ≤ M := le_inf h.E_le_H hEN
  have hcop : Nat.Coprime (Nat.card U) 9 := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hU2
    rw [ha]
    exact Nat.Coprime.pow_left a (by norm_num)
  have hdivM : Nat.card U * 9 ∣ Nat.card M := by
    apply hcop.mul_dvd_of_dvd_of_dvd (Subgroup.card_dvd_of_le hUM)
    rw [← h.card_E]
    exact Subgroup.card_dvd_of_le hEM
  have hcardM : Nat.card N ≤ Nat.card M :=
    calc Nat.card N = Nat.card U * m := hcardN.symm
      _ ≤ Nat.card U * 9 := Nat.mul_le_mul_left _ hm9
      _ ≤ Nat.card M := Nat.le_of_dvd Nat.card_pos hdivM
  have hNM : M = N := Subgroup.eq_of_le_of_card_ge inf_le_right hcardM
  have hNH : N ≤ Hh := hNM ▸ inf_le_left
  intro x hx
  have hxU : x ∈ Subgroup.normalizer (U : Set X) := by
    have hTL : T0 ⊓ L = U :=
      le_antisymm (inf_le_inf_right L hT0) (le_inf (hUR.trans hRT0) inf_le_right)
    rw [← hTL]
    exact E9P2.Loc.mem_normalizer_inf hx (E9P2.Loc.mem_normalizer_of_normal h.normal_L x)
  obtain ⟨l, hl, t, ht, rfl⟩ := hX x
  have hlU : l ∈ Subgroup.normalizer (U : Set X) := by
    have := mul_mem hxU (inv_mem (hHU t (h.T_le ht)))
    simpa using this
  exact mul_mem (hNH ⟨hlU, hl⟩) (h.T_le ht)

end LocalFinite

end CFSG.Quasithin
