module

public import CFSG.RankThree.PartOne.S11c.J4Key
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LinearAlgebra Module Subgroup
open scoped Pointwise commutatorElement

section Abstract

variable {J : Type*} [Group J] [Finite J] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem exists_conj_map_le_of_isPGroup {p : ℕ} [Fact p.Prime] (Q : Subgroup J) (hQp : IsPGroup p Q)
    (hQ : ¬ p ∣ Q.index) (E : Subgroup J) (hE : IsPGroup p E) :
    ∃ c : J, E.map (MulAut.conj c).toMonoidHom ≤ Q := by
  obtain ⟨P, hP⟩ := hE.exists_le_sylow
  let Qs : Sylow p J := hQp.toSylow hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J P Qs
  refine ⟨g, ?_⟩
  rintro _ ⟨e, he, rfl⟩
  have h1 : MulAut.conj g e ∈ ((g • P : Sylow p J) : Subgroup J) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj g) (P : Subgroup J) (hP he)
  rw [hg] at h1
  exact h1

theorem eq_bot_of_normalized_by_plane (ρ : Representation (ZMod 2) J V)
    (hV : finrank (ZMod 2) V = 112) {b : LinearMap.BilinForm (ZMod 2) V} (hb : b.Nondegenerate)
    (hbρ : ∀ g x y, b (ρ g x) (ρ g y) = b x y) (Q : Subgroup J)
    (hQ : IsExtraspecialPGroup 11 Q) (hexp : Monoid.exponent Q = 11) {x y z : Q}
    (hz : z = ⁅x, y⁆) (hcard : Nat.card Q = 11 ^ 3) (hgen : Subgroup.closure ({x, y} : Set Q) = ⊤)
    (h11 : ¬ 11 ^ 4 ∣ Nat.card J) (hρz : ρ (z : J) ≠ 1)
    (hrank : ∀ g : J, g ≠ 1 → IsPGroup 2 (Subgroup.zpowers g) →
      finrank (ZMod 2) (centralFixed ρ g) ≤ 99)
    (E : Subgroup J) (hEel : IsElementaryAbelian 11 E) (hEcard : Nat.card E = 11 ^ 2)
    (U : Subgroup J) (hU : IsPGroup 2 U) (hEU : E ≤ Subgroup.normalizer (U : Set J)) :
    U = ⊥ := by
  classical
  have hQp : IsPGroup 11 Q := IsPGroup.of_card (n := 3) hcard
  have hQidx : ¬ 11 ∣ Q.index := by
    intro h
    apply h11
    have h1 := Subgroup.card_mul_index Q
    rw [hcard] at h1
    rw [← h1]
    obtain ⟨k, hk⟩ := h
    rw [hk]
    exact ⟨k, by ring⟩
  obtain ⟨c, hc⟩ := exists_conj_map_le_of_isPGroup (p := 11) Q hQp hQidx E
    (IsElementaryAbelian.isPGroup 11 E)
  set f : J →* J := (MulAut.conj c).toMonoidHom with hf
  have hfinj : Function.Injective f := (MulAut.conj c).injective
  set E' : Subgroup J := E.map f with hE'
  set U' : Subgroup J := U.map f with hU'
  have hE'card : Nat.card E' = 11 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective hfinj]
    exact hEcard
  have hE'el : IsElementaryAbelian 11 E' := IsElementaryAbelian.map (A := E) f
  have hU'p : IsPGroup 2 U' := hU.map f
  have hE'norm : E' ≤ Subgroup.normalizer (U' : Set J) :=
    (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map f)
  have hcentral : ∀ m : E', m ≠ 1 → U' ⊓ Subgroup.centralizer ({(m : J)} : Set J) = ⊥ := by
    intro m hm
    have hmQ : (m : J) ∈ Q := hc m.2
    have hm1 : (⟨(m : J), hmQ⟩ : Q) ≠ 1 := fun h => hm (Subtype.ext (by
      simpa using congrArg Subtype.val h))
    have hEQ : E'.subgroupOf Q ≤ ⊤ := le_top
    have hEQcard : Nat.card (E'.subgroupOf Q) = 11 ^ 2 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc).toEquiv]
      exact hE'card
    refine centralizer_two_subgroup_eq_bot ρ hV hb hbρ Q hQ hexp hz hcard hgen hρz hrank
      (E'.subgroupOf Q) hEQcard U' hU'p ?_ (β := ⟨(m : J), hmQ⟩) (Subgroup.mem_subgroupOf.mpr m.2)
      hm1
    intro e he u hu
    have := hE'norm (Subgroup.mem_subgroupOf.mp he)
    rw [Subgroup.mem_normalizer_iff] at this
    exact (this u).mp hu
  have hgenU : U' = ⨆ (m : E') (_ : m ≠ 1), U' ⊓ Subgroup.centralizer ({(m : J)} : Set J) :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane 11
      (by norm_num) E' U' (fun m => by
        obtain ⟨m, hm⟩ := m
        exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian m hm)) hE'card
      (by
        intro h
        obtain ⟨k, hk⟩ := hU'p.exists_card_eq
        rw [hk] at h
        have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) h)
        have := (Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 11) Nat.prime_two).mp this
        omega) hE'norm
  have hU'bot : U' = ⊥ := by
    rw [hgenU]
    refine iSup_eq_bot.mpr fun m => iSup_eq_bot.mpr fun hm => hcentral m hm
  refine (Subgroup.eq_bot_iff_forall U).mpr fun u hu => ?_
  have h1 : f u ∈ U.map f := Subgroup.mem_map_of_mem f hu
  have h2 : f u ∈ (⊥ : Subgroup J) := hU'bot ▸ h1
  exact hfinj (by rw [map_one]; exact (Subgroup.mem_bot.mp h2))

end Abstract

end CFSG.RankThree.PartOne
