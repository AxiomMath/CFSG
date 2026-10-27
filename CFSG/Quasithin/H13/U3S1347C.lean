module

public import CFSG.Quasithin.H13.U3S1347B
public import CFSG.Quasithin.H13.U3S1348A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem eq_one_of_two_pow_of_cube {M : Type*} [Group M] {y : M} {k : ℕ} (h2 : y ^ 2 ^ k = 1)
    (h3 : y ^ 3 = 1) : y = 1 := by
  have hco : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have h1 : orderOf y ∣ 1 := by
    rw [← hco.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)

omit [Finite G] in
theorem eq_one_of_mem_of_cube {P : Subgroup G} (hP : IsPGroup 2 P) {y : G} (hy : y ∈ P)
    (h3 : y ^ 3 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  exact eq_one_of_two_pow_of_cube (by simpa using congrArg Subtype.val hk) h3

theorem s1347_reduced (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) : IsTwoReducedIn (H₁ ⊔ H₂) (v0Of T H₁ H₂) :=
  C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hH₀) (A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1)

omit [Finite G] in
theorem s1347_Z_le_V0 {H₁ H₂ : Subgroup G} : quasithinOmegaOneCenter T ≤ v0Of T H₁ H₂ :=
  le_conjClosure _ _

theorem s1347_not_le_centralizer_Z (S : A6.Setting134 G T L V) {H : Subgroup G} (hTH : T ≤ H)
    (hidx : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H)) :
    ¬ oTwoRes H ≤ centralizer (quasithinOmegaOneCenter T : Set G) := by
  intro hK
  have e : cZ T (oTwoRes H) = quasithinOmegaOneCenter T :=
    inf_eq_left.2 fun z hz => mem_centralizer_iff.2 fun k hk =>
      (mem_centralizer_iff.1 (hK hk) z hz).symm
  rw [cZ_eq_cZ_oTwoRes (A5.isSylowTwoOf_of_le S.h13.sylow hTH), e] at hidx
  have := Nat.card_pos (α := ↥(quasithinOmegaOneCenter T))
  omega

theorem s1347_eq_one_of_cube (S : A6.Setting134 G T L V) {H₁ H₂ H : Subgroup G}
    (hH : H ≤ H₁ ⊔ H₂) (hTH : T ≤ H) (h3 : T.relIndex H = 3)
    (hidx : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H))
    (hN : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G)) {y : G}
    (hy : y ∈ oTwoRes H ⊓ centralizer (v0Of T H₁ H₂ : Set G)) (hy3 : y ^ 3 = 1) : y = 1 := by
  by_contra hy1
  have hHN : H ≤ normalizer ((oTwoRes H ⊓ centralizer (v0Of T H₁ H₂ : Set G) :
      Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_of (le_normalizer_oTwoRes H hg)
      (mem_normalizer_centralizer_of_mem (hN (hH hg)))
  have hyT : y ∉ T := fun hyT => hy1 (eq_one_of_mem_of_cube S.h13.sylow.1 hyT hy3)
  have hTN : T ⊔ (oTwoRes H ⊓ centralizer (v0Of T H₁ H₂ : Set G)) = H := by
    rcases eq_or_eq_of_relIndex_three h3 le_sup_left
      (sup_le hTH (inf_le_left.trans (oTwoRes_le H))) with e | e
    · exact absurd (e ▸ mem_sup_right hy) hyT
    · exact e
  have hK : oTwoRes H ≤ oTwoRes H ⊓ centralizer (v0Of T H₁ H₂ : Set G) := by
    refine oTwoRes_le_of_le_sup ?_ S.h13.sylow.1 (hTH.trans hHN)
    rw [sup_comm, hTN]
  exact s1347_not_le_centralizer_Z S hTH hidx fun k hk =>
    centralizer_le (SetLike.coe_subset_coe.2 s1347_Z_le_V0) (hK hk).2

omit [Finite G] in
theorem s1347_centralizer_le_normalizer {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hH₀ : InH T (H₁ ⊔ H₂)) :
    (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) ≤ normalizer (oTwoRes H₁ : Set G) ∧
      (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) ≤ normalizer (oTwoRes H₂ : Set G) := by
  have hle : ∀ X : Subgroup G, (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) ≤
      (H₁ ⊔ H₂) ⊓ centralizer (cZ T X : Set G) := fun X =>
    inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2
      (inf_le_left.trans s1347_Z_le_V0)))
  obtain ⟨⟨h1, h2⟩, -⟩ := h.cent hH₀
  exact ⟨(hle _).trans h1, (hle _).trans h2⟩

theorem s1347_eq_one_of_threePow (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) {x : G}
    (hx : x ∈ (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G)) {k : ℕ} (hxk : x ^ 3 ^ k = 1) :
    x = 1 := by
  have hred := s1347_reduced S hH₀
  have key : ∀ {H : Subgroup G}, H ≤ H₁ ⊔ H₂ → T ≤ H → T.relIndex H = 3 →
      Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(cZ T H) →
      oTwoRes H = oThreePrimeResidual ((H₁ ⊔ H₂) ⊓
        centralizer (cZ T (oTwoRes H) : Set G)) → x = 1 := by
    intro H hH hTH h3 hidx hK
    have hxC : x ∈ (H₁ ⊔ H₂) ⊓ centralizer (cZ T (oTwoRes H) : Set G) :=
      inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2
        (inf_le_left.trans s1347_Z_le_V0))) hx
    have hxK : x ∈ oTwoRes H := by
      rw [hK]
      exact subset_closure ⟨hxC, k, hxk⟩
    have hx3 : x ^ 3 = 1 := pow_three_of_relIndex_three S.h13.sylow.1 hTH h3
      (oTwoRes_le H hxK) (Odd.pow (by decide : Odd 3)) hxk
    exact s1347_eq_one_of_cube S hH hTH h3 hidx hred.2.1 ⟨hxK, hx.2⟩ hx3
  rcases (h.cent hH₀).2 with hK | hK
  · exact key le_sup_left h.inH₁.1 (s1347_relIndex_three S h.inH₁.1 h.s3₁) h.index₁ hK
  · exact key le_sup_right h.inH₂.1 (s1347_relIndex_three S h.inH₂.1 h.s3₂) h.index₂ hK

theorem s1347_T_inf_centralizer (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hH₀ : InH T (H₁ ⊔ H₂)) :
    T ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 (H₁ ⊔ H₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  refine le_antisymm ?_ (le_inf (pCoreOf_two_le_of_isSylowTwoOf
    (A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1)) (pCoreOf_le_centralizer_of_reduced' hred))
  have key : ∀ {H : Subgroup G}, H ≤ H₁ ⊔ H₂ → T ≤ H → T.relIndex H = 3 →
      H ≤ normalizer ((T ⊓ centralizer (v0Of T H₁ H₂ : Set G) : Subgroup G) : Set G) := by
    intro H hH hTH h3
    have hp : IsPGroup 2 ↥(H ⊓ centralizer (v0Of T H₁ H₂ : Set G)) := by
      rintro ⟨x, hx⟩
      obtain ⟨a, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
      refine ⟨a, Subtype.ext ?_⟩
      show x ^ 2 ^ a = 1
      have hx3 := pow_three_of_relIndex_three S.h13.sylow.1 hTH h3 (pow_mem hx.1 (2 ^ a)) hm
        (by rw [← pow_mul, ← hxm, pow_orderOf_eq_one])
      exact s1347_eq_one_of_threePow S h hH₀ ⟨hH (pow_mem hx.1 _), pow_mem hx.2 _⟩ (k := 1)
        (by rwa [pow_one])
    have hHN : H ≤ normalizer ((H ⊓ centralizer (v0Of T H₁ H₂ : Set G) : Subgroup G) :
        Set G) := fun g hg => mem_normalizer_inf_of (le_normalizer hg)
      (mem_normalizer_centralizer_of_mem (hred.2.1 (hH hg)))
    have hle : H ⊓ centralizer (v0Of T H₁ H₂ : Set G) ≤ T :=
      (le_pCoreOf_of_le_normalizer inf_le_left hHN hp).trans
        (pCoreOf_two_le_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hTH))
    have e : H ⊓ centralizer (v0Of T H₁ H₂ : Set G) =
        T ⊓ centralizer (v0Of T H₁ H₂ : Set G) :=
      le_antisymm (le_inf hle inf_le_right) (inf_le_inf_right _ hTH)
    rw [← e]
    exact hHN
  exact le_pCoreOf_of_le_normalizer (inf_le_left.trans hH₀.1) (sup_le
    (key le_sup_left h.inH₁.1 (s1347_relIndex_three S h.inH₁.1 h.s3₁))
    (key le_sup_right h.inH₂.1 (s1347_relIndex_three S h.inH₂.1 h.s3₂)))
    (S.h13.sylow.1.to_le inf_le_left)

end CFSG.Quasithin.H13.U3
