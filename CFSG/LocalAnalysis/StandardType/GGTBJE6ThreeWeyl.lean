module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem e6Three_weylPoint
    {G : Type} [Group G] {C₀ : Subgroup G} {L' : Type} [Group L']
    {ψ₀ : L' →* ↥C₀} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    (hZ : Subgroup.center ↥C₀ = ⊥) (hker3 : ∀ z ∈ ψ₀.ker, z ^ 3 = 1)
    {A : Subgroup (MulAut L')} {κ : A →* Multiplicative (Fin Tag.E6.rank → ZMod 3)}
    (hκinj : Function.Injective κ) {V : Set (Fin Tag.E6.rank → ZMod 3)}
    (hκV : ∀ x, Multiplicative.ofAdd x ∈ κ.range ↔ x ∈ V)
    {t : (Fin Tag.E6.rank → ZMod 3) → G}
    (htmul : ∀ x x', t (x + x') = t x * t x')
    (hconj : ∀ (a : A) (l : L'),
      ((ψ₀ ((a : MulAut L') l) : ↥C₀) : G) =
        t (Multiplicative.toAdd (κ a)) *
          ((ψ₀ l : ↥C₀) : G) *
            (t (Multiplicative.toAdd (κ a)))⁻¹)
    {T : Subgroup L'} (hTodd : ∀ z ∈ ψ₀.ker, Odd (orderOf z) → z ∈ T)
    (hTfix : ∀ a ∈ A, ∀ z ∈ T, a z = z)
    (hHyp : ∀ x ∈ NoOffRest.hypE6, ∃ z ∈ T, z ^ 3 = 1 ∧ ∃ b : A,
      MulAut.conj z = (b : MulAut L') ∧ Multiplicative.toAdd (κ b) = x)
    {s : (Fin Tag.E6.rank → ZMod 3) → Fin Tag.E6.rank → ZMod 3} (hs2 : ∀ x, s (s x) = x)
    (hsV : ∀ x ∈ V, s x ∈ V) (hsH : ∀ x, s x - x ∈ NoOffRest.hypE6) {m : L'}
    (hm : ∀ x, ((ψ₀ m : ↥C₀) : G) * t x *
      ((ψ₀ m : ↥C₀) : G)⁻¹ = t (s x)) :
    ∃ hN : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')),
      GGTorusWeylElt 3 A m ∧
        ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hN a)) = s (Multiplicative.toAdd (κ a)) := by
  classical
  let ψ : L' →* G := C₀.subtype.comp ψ₀
  have hconjψ : ∀ (a : A) (l : L'), ψ ((a : MulAut L') l) =
      t (Multiplicative.toAdd (κ a)) * ψ l * (t (Multiplicative.toAdd (κ a)))⁻¹ :=
    fun a l => hconj a l
  have hmψ : ∀ x, ψ m * t x * (ψ m)⁻¹ = t (s x) := hm
  have hstep1 : ∀ (m' : L'),
      (∀ x, ψ m' * t x * (ψ m')⁻¹ = t (s x)) →
      ∀ a : A, ∃ b : A,
        (b : MulAut L') = MulAut.conj m' * (a : MulAut L') * (MulAut.conj m')⁻¹ ∧
        Multiplicative.toAdd (κ b) = s (Multiplicative.toAdd (κ a)) := by
    intro m' hm' a
    have hxV : s (Multiplicative.toAdd (κ a)) ∈ V :=
      hsV _ ((hκV _).mp ⟨a, rfl⟩)
    obtain ⟨b, hb⟩ := (hκV _).mpr hxV
    have hbκ : Multiplicative.toAdd (κ b) = s (Multiplicative.toAdd (κ a)) := by
      rw [hb, toAdd_ofAdd]
    refine ⟨b, ?_, hbκ⟩
    apply TypeA.mulAut_eq_of_forall ψ₀ hker hperf
    intro l
    apply Subtype.ext
    have hbl : ψ ((b : MulAut L') l) =
        t (s (Multiplicative.toAdd (κ a))) * ψ l *
          (t (s (Multiplicative.toAdd (κ a))))⁻¹ := by
      rw [← hbκ]
      exact hconjψ b l
    have hcl : ψ ((MulAut.conj m' * (a : MulAut L') * (MulAut.conj m')⁻¹) l) =
        t (s (Multiplicative.toAdd (κ a))) * ψ l *
          (t (s (Multiplicative.toAdd (κ a))))⁻¹ := by
      have h1 : ((MulAut.conj m' * (a : MulAut L') * (MulAut.conj m')⁻¹) l) =
          m' * (a : MulAut L') (m'⁻¹ * l * m') * m'⁻¹ := by
        rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
      rw [h1]
      calc ψ (m' * (a : MulAut L') (m'⁻¹ * l * m') * m'⁻¹)
          = ψ m' * ψ ((a : MulAut L') (m'⁻¹ * l * m')) * (ψ m')⁻¹ := by
            rw [map_mul, map_mul, map_inv]
        _ = ψ m' * (t (Multiplicative.toAdd (κ a)) * ψ (m'⁻¹ * l * m') *
              (t (Multiplicative.toAdd (κ a)))⁻¹) * (ψ m')⁻¹ := by
            rw [hconjψ a (m'⁻¹ * l * m')]
        _ = (ψ m' * t (Multiplicative.toAdd (κ a)) * (ψ m')⁻¹) * ψ l *
              (ψ m' * (t (Multiplicative.toAdd (κ a)))⁻¹ * (ψ m')⁻¹) := by
            rw [map_mul, map_mul, map_inv]
            group
        _ = t (s (Multiplicative.toAdd (κ a))) * ψ l *
              (t (s (Multiplicative.toAdd (κ a))))⁻¹ := by
            have hAinv : ψ m' * (t (Multiplicative.toAdd (κ a)))⁻¹ * (ψ m')⁻¹ =
                (t (s (Multiplicative.toAdd (κ a))))⁻¹ := by
              rw [← hm' (Multiplicative.toAdd (κ a))]
              group
            rw [hm' (Multiplicative.toAdd (κ a)), hAinv]
    change ψ ((b : MulAut L') l) = ψ ((MulAut.conj m' * (a : MulAut L') *
      (MulAut.conj m')⁻¹) l)
    rw [hbl, hcl]
  have hm_inv : ∀ x, ψ m⁻¹ * t x * (ψ m⁻¹)⁻¹ = t (s x) := by
    intro x
    have h1 : ψ m * t (s x) * (ψ m)⁻¹ = t x := by
      rw [hmψ (s x), hs2 x]
    have h3 : (ψ m)⁻¹ * t x * ψ m = t (s x) := by
      rw [← h1]
      group
    rwa [map_inv, inv_inv]
  have hN : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      obtain ⟨b, hb, -⟩ := hstep1 m hm ⟨n, hn⟩
      rw [← hb]
      exact b.2
    · intro hn
      obtain ⟨b, hb, -⟩ := hstep1 m⁻¹ hm_inv
        ⟨MulAut.conj m * n * (MulAut.conj m)⁻¹, hn⟩
      have hbn : n = (b : MulAut L') := by
        rw [hb, map_inv (MulAut.conj : L' →* MulAut L') m]
        group
      rw [hbn]
      exact b.2
  have hcoord : ∀ a : A, Multiplicative.toAdd (κ (ggConjAut A hN a)) =
      s (Multiplicative.toAdd (κ a)) := by
    intro a
    obtain ⟨b, hb, hbκ⟩ := hstep1 m hm a
    have hgb : ggConjAut A hN a = b := by
      apply Subtype.ext
      rw [ggConjAut_apply A hN a]
      exact hb.symm
    rw [hgb, hbκ]
  have hweyl : GGTorusWeylElt 3 A m := by
    intro a ha
    let aA : A := ⟨a, ha⟩
    let x : Fin Tag.E6.rank → ZMod 3 := Multiplicative.toAdd (κ aA)
    let h : Fin Tag.E6.rank → ZMod 3 := s x - x
    have hxm : ψ (m * (a m)⁻¹) = t h := by
      have ham : ψ (a m) = t x * ψ m * (t x)⁻¹ := hconjψ aA m
      calc ψ (m * (a m)⁻¹)
          = ψ m * (ψ (a m))⁻¹ := by rw [map_mul, map_inv]
        _ = ψ m * (t x * ψ m * (t x)⁻¹)⁻¹ := by rw [ham]
        _ = (ψ m * t x * (ψ m)⁻¹) * (t x)⁻¹ := by group
        _ = t (s x) * (t x)⁻¹ := by rw [hmψ x]
        _ = t h := by
            have ht : t (s x) = t (s x - x) * t x := by
              simpa only [sub_add_cancel] using htmul (s x - x) x
            rw [ht, mul_inv_cancel_right]
    obtain ⟨z, hzT, hz3, b, hbz, hbκ⟩ := hHyp h (hsH x)
    have h1 : ∀ l, ψ ((b : MulAut L') l) = t h * ψ l * (t h)⁻¹ := by
      intro l
      rw [← hbκ]
      exact hconjψ b l
    have h2 : ∀ l, ψ ((b : MulAut L') l) = ψ (z * l * z⁻¹) := by
      intro l
      rw [← hbz, MulAut.conj_apply]
    have h3 : ∀ l, t h * ψ l * (t h)⁻¹ = ψ z * ψ l * (ψ z)⁻¹ := by
      intro l
      rw [← h1 l, h2 l, map_mul, map_mul, map_inv]
    have h4 : ∀ l, ψ (m * (a m)⁻¹) * ψ l * (ψ (m * (a m)⁻¹))⁻¹ =
        ψ z * ψ l * (ψ z)⁻¹ := by
      intro l
      rw [hxm]
      exact h3 l
    let c : ↥C₀ := (ψ₀ z)⁻¹ * ψ₀ (m * (a m)⁻¹)
    have hc_comm : ∀ l : L', c * ψ₀ l = ψ₀ l * c := by
      intro l
      apply Subtype.ext
      change ((ψ z)⁻¹ * ψ (m * (a m)⁻¹)) * ψ l =
        ψ l * ((ψ z)⁻¹ * ψ (m * (a m)⁻¹))
      calc (ψ z)⁻¹ * ψ (m * (a m)⁻¹) * ψ l
          = (ψ z)⁻¹ * (ψ (m * (a m)⁻¹) * ψ l *
              (ψ (m * (a m)⁻¹))⁻¹) * ψ (m * (a m)⁻¹) := by group
        _ = (ψ z)⁻¹ * (ψ z * ψ l * (ψ z)⁻¹) * ψ (m * (a m)⁻¹) := by rw [h4 l]
        _ = ψ l * ((ψ z)⁻¹ * ψ (m * (a m)⁻¹)) := by group
    have hcZ : c ∈ Subgroup.center ↥C₀ := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := hψ₀ y
      exact (hc_comm l).symm
    have hc1 : c = 1 := by
      have hmem : c ∈ (⊥ : Subgroup ↥C₀) := by
        rw [← hZ]
        exact hcZ
      exact Subgroup.mem_bot.mp hmem
    have hkker : z⁻¹ * (m * (a m)⁻¹) ∈ ψ₀.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      have hc1' : (ψ₀ z)⁻¹ * ψ₀ (m * (a m)⁻¹) = 1 := hc1
      exact hc1'
    have hk3 : (z⁻¹ * (m * (a m)⁻¹)) ^ 3 = 1 := hker3 _ hkker
    have hkodd : Odd (orderOf (z⁻¹ * (m * (a m)⁻¹))) := by
      have hdvd : orderOf (z⁻¹ * (m * (a m)⁻¹)) ∣ 3 :=
        orderOf_dvd_iff_pow_eq_one.mpr hk3
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h <;>
        rw [h] <;> norm_num
    have hkT : z⁻¹ * (m * (a m)⁻¹) ∈ T := hTodd _ hkker hkodd
    have hzk : m * (a m)⁻¹ = z * (z⁻¹ * (m * (a m)⁻¹)) := by group
    have hmemT : m * (a m)⁻¹ ∈ T := by
      rw [hzk]
      exact T.mul_mem hzT hkT
    have hcomm : Commute z (z⁻¹ * (m * (a m)⁻¹)) :=
      Subgroup.mem_center_iff.mp (hker hkker) z
    refine ⟨?_, fun a' ha' => hTfix a' ha' _ hmemT⟩
    rw [hzk, hcomm.mul_pow 3, hz3, hk3, mul_one]
  exact ⟨hN, hweyl, hcoord⟩

end CFSG.StandardType

end
