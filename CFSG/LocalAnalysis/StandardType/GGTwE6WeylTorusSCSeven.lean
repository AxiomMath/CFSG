module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylRealize
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTwistedTorus
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveConjClass
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesAbstractFrame

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration

section SCSeven


private theorem exists_map_conj_eq_of_sc {C : Type*} [Group C] {p : ℕ} {T E : Subgroup C}
    (hTcomm : IsMulCommutative T)
    (hconj : ∀ P : Subgroup C, IsPGroup p P → ∃ g : C, P ≤ T.map (MulAut.conj g).toMonoidHom)
    (hET : E ≤ T) (htorsE : ∀ x ∈ T, x ^ p = 1 → x ∈ E) (hEel : IsElemAbelian p E)
    {A : Subgroup C} (hA : IsElemAbelian p A)
    (hSC : ∀ c ∈ Subgroup.centralizer (A : Set C), c ^ p = 1 → c ∈ A) :
    ∃ g : C, A = E.map (MulAut.conj g).toMonoidHom := by
  have hAp : IsPGroup p A := by
    apply IsPGroup.of_exponent_dvd_pow (n := 1)
    rw [pow_one]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro element
    exact Subtype.ext (hA.2 element element.property)
  obtain ⟨g, hg⟩ := hconj A hAp
  have hAE : A ≤ E.map (MulAut.conj g).toMonoidHom := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := hg ha
    refine ⟨t, htorsE t ht ?_, hta⟩
    have h1 : a ^ p = 1 := hA.2 a ha
    rw [← hta, ← map_pow] at h1
    exact (MulAut.conj g).injective (h1.trans (map_one (MulAut.conj g)).symm)
  have hE'A : E.map (MulAut.conj g).toMonoidHom ≤ A := by
    intro y hy
    refine hSC y ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      obtain ⟨e, he, rfl⟩ := hy
      obtain ⟨t, ht, rfl⟩ := hg ha
      have hcomm : e * t = t * e :=
        congrArg Subtype.val (hTcomm.is_comm.comm (⟨e, hET he⟩ : T) ⟨t, ht⟩)
      rw [← map_mul, ← map_mul, hcomm]
    · obtain ⟨e, he, rfl⟩ := hy
      rw [← map_pow, hEel.2 e he, map_one]
  exact ⟨g, le_antisymm hAE hE'A⟩

theorem twistedE6SCUnique_ge_seven {f p : ℕ} [Fact p.Prime] [NeZero p] (hp7 : 7 ≤ p) (hf : 1 ≤ f)
    (hpq : p ∣ 2 ^ f + 1) (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) {T : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    {ι₀ : Multiplicative (Fin TwistTag.E6.tag.rank → ZMod p) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ)}
    (hι₀ : Function.Injective ι₀) (hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hrangeT : ι₀.range ≤ T) (htors : ∀ t ∈ T, t ^ p = 1 → t ∈ ι₀.range)
    (hcent : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ x ∈ ι₀.range, c * x = x * c) → c ∈ T)
    {A : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)} (hA : IsElemAbelian p A)
    (hSC : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ), (∀ a ∈ A, c * a = a * c) →
      c ^ p = 1 → c ∈ A) :
    ∃ c : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      ι₀.range.map (MulAut.conj c).toMonoidHom = A := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero 2 (pow_ne_zero f (by norm_num)))
  haveI : IsSimpleRing K := DivisionRing.isSimpleRing K
  have hσbij : Function.Bijective σ :=
    Finite.injective_iff_bijective.mp (RingHom.injective σ)
  let σ' : K ≃+* K := RingEquiv.ofBijective σ hσbij
  have hσ' : ∀ c, σ' c = c ^ (2 ^ f) := fun c => hσ c
  have hpq' : ¬ p ∣ 2 ^ f := by
    intro hd
    have h1 : p ∣ 1 := by
      have h := Nat.dvd_sub hpq hd
      rwa [show 2 ^ f + 1 - 2 ^ f = 1 by omega] at h
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have h2f : (((2 ^ f : ℕ)) : ZMod p) = -1 := by
    have h0 : (((2 ^ f + 1 : ℕ)) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff (2 ^ f + 1) p).2 hpq
    rw [Nat.cast_add, Nat.cast_one] at h0
    rw [eq_neg_iff_add_eq_zero]
    exact h0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he : orderOf (((2 ^ f : ℕ)) : ZMod p) = 2 := by
    apply orderOf_eq_prime
    · rw [h2f]; norm_num
    · intro h1
      have hneg : (-1 : ZMod p) = 1 := by rw [← h2f, h1]
      have h2 : (2 : ZMod p) = 0 := by
        have h := congrArg (fun x : ZMod p => x + 1) hneg
        norm_num at h
        exact h.symm
      have h3 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
      have := Nat.le_of_dvd (by norm_num) h3
      omega
  have hSyl : SylowTorus ↥(graphFixedRootGroup TwistTag.E6 K σ) p 6 :=
    sylowTorus_twistedE6_two Nat.prime_two hf K hK σ' hσ' hp hp7 hpq' he
  obtain ⟨T', E, hT'comm, hconj, hET', htors', hEel, _⟩ := hSyl.exists_torus
  have hXel : IsElemAbelian p ι₀.range := NoOffE8Five.isElemAbelian_range_of_module ι₀
  have hXSC : ∀ c ∈ Subgroup.centralizer (ι₀.range : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      c ^ p = 1 → c ∈ ι₀.range := by
    intro c hc hcp
    exact htors c (hcent c (fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hc x hx).symm)) hcp
  have hASC : ∀ c ∈ Subgroup.centralizer (A : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)),
      c ^ p = 1 → c ∈ A := by
    intro c hc hcp
    exact hSC c (fun a ha => (Subgroup.mem_centralizer_iff.mp hc a ha).symm) hcp
  obtain ⟨g₁, hg₁⟩ := exists_map_conj_eq_of_sc hT'comm hconj hET' htors' hEel hA hASC
  obtain ⟨g₂, hg₂⟩ := exists_map_conj_eq_of_sc hT'comm hconj hET' htors' hEel hXel hXSC
  refine ⟨g₁ * g₂⁻¹, ?_⟩
  calc ι₀.range.map (MulAut.conj (g₁ * g₂⁻¹)).toMonoidHom
      = (E.map (MulAut.conj g₂).toMonoidHom).map (MulAut.conj (g₁ * g₂⁻¹)).toMonoidHom := by
        rw [hg₂]
    _ = E.map ((MulAut.conj (g₁ * g₂⁻¹)).toMonoidHom.comp (MulAut.conj g₂).toMonoidHom) := by
        rw [Subgroup.map_map]
    _ = E.map (MulAut.conj g₁).toMonoidHom := by
        congr 1
        refine MonoidHom.ext fun z => ?_
        show g₁ * g₂⁻¹ * ((MulAut.conj g₂) z) * (g₁ * g₂⁻¹)⁻¹ = g₁ * z * g₁⁻¹
        rw [MulAut.conj_apply]
        group
    _ = A := hg₁.symm

end SCSeven

end ExcFrames

end CFSG.StandardType
