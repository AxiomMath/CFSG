module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Ch1Sec3 CFSG.LieType.BorelTits

variable {G : Type*} [Group G] [Finite G] {T X P : Subgroup G}

section Xi

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_pCoreOf_sup_normalizer (hQT : pCoreOf 2 X ≤ T) (hX : IsXi T X) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    T = pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (P : Set G)) := by
  refine le_antisymm (fun t ht => ?_) (sup_le hQT inf_le_left)
  obtain ⟨g, hgX, hg⟩ := exists_conj_of_isSylowIn hP (isSylowIn_map_conj hP (hX.2.1 ht))
  rw [← hX.pCoreOf_sup_eq hp2 hpX hP] at hgX
  obtain ⟨q, hq, a, ha, rfl⟩ := (mem_sup_iff_of_le_normalizer hP.le_normalizer_pCoreOf_two).1 hgX
  have hn : q⁻¹ * t ∈ T ⊓ Subgroup.normalizer (P : Set G) := by
    refine ⟨T.mul_mem (T.inv_mem (hQT hq)) ht, Subgroup.mem_normalizer_iff.2 fun z => ?_⟩
    constructor
    · intro hz
      have h2 := (hg (t * z * t⁻¹)).1 ⟨z, hz, rfl⟩
      have e : q⁻¹ * t * z * (q⁻¹ * t)⁻¹ =
          a * ((q * a)⁻¹ * (t * z * t⁻¹) * (q * a)) * a⁻¹ := by group
      rw [e]
      exact P.mul_mem (P.mul_mem ha h2) (P.inv_mem ha)
    · intro hz
      have h1 : (q * a)⁻¹ * (t * z * t⁻¹) * (q * a) ∈ P := by
        have e : (q * a)⁻¹ * (t * z * t⁻¹) * (q * a) =
            a⁻¹ * (q⁻¹ * t * z * (q⁻¹ * t)⁻¹) * a := by group
        rw [e]
        exact P.mul_mem (P.mul_mem (P.inv_mem ha) hz) ha
      obtain ⟨w, hw, hwe⟩ := (hg (t * z * t⁻¹)).2 h1
      have hwz : w = z := by
        have hwe' : t * w * t⁻¹ = t * z * t⁻¹ := hwe
        simpa using hwe'
      rw [← hwz]
      exact hw
  have e : t = q * (q⁻¹ * t) := by group
  rw [e]
  exact Subgroup.mul_mem_sup hq hn

theorem irreducible (hQT : pCoreOf 2 X ≤ T) (hX : IsXi T X) (hp2 : p ≠ 2)
    (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    frattiniIn P ≠ P ∧ ∀ U : Subgroup G, frattiniIn P ≤ U → U ≤ P →
      T ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) →
      U = frattiniIn P ∨ U = P := by
  refine ⟨frattiniIn_ne_of_ne_bot (hX.sylow_ne_bot hp2 hpX hP), fun U hΦU hUP hNU => ?_⟩
  obtain ⟨hΦ1, hΦ2⟩ := hX.frattiniIn_eq hp2 hpX hP
  set Q := pCoreOf 2 X with hQ
  have hUQ : U ≤ Subgroup.normalizer (Q : Set G) := hUP.trans hP.le_normalizer_pCoreOf_two
  have hY1 : ⁅X, X⁆ ⊔ Q ≤ Q ⊔ U :=
    sup_le ((hX.commutator_le hp2 hpX hP).trans (sup_le_sup_left (hΦ1 ▸ hΦU) Q)) le_sup_left
  have hY2 : Q ⊔ U ≤ X := sup_le (pCoreOf_le 2 X) (hUP.trans hP.le)
  have hY3 : T ≤ Subgroup.normalizer ((Q ⊔ U : Subgroup G) : Set G) := by
    calc T = Q ⊔ (T ⊓ Subgroup.normalizer (P : Set G)) :=
          eq_pCoreOf_sup_normalizer hQT hX hp2 hpX hP
      _ ≤ _ := sup_le (fun q hq => Subgroup.le_normalizer (Subgroup.mem_sup_left hq))
          fun s hs => Subgroup.inf_normalizer_le_normalizer_sup Q U
            ⟨(hX.2.1.trans (normalizer_le_normalizer_pCoreOf 2 X)) hs.1,
              hNU hs⟩
  have hD : P ⊓ (Q ⊔ U) = U := inf_sup_eq_of_le_normalizer hUP hUQ (hP.inf_pCoreOf_two_eq_bot hp2)
  rcases (hX.prime_spec hp.out hp2 hpX).2.2 (Q ⊔ U) hY1 hY2 hY3 with h | h
  · left
    rw [← hD, h, hΦ2]
  · right
    rw [← hD, h, inf_eq_left.2 hP.le]

theorem eq_commutator_frattiniIn (hQT : pCoreOf 2 X ≤ T) (hT2 : IsPGroup 2 T) (hX : IsXi T X)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    P = ⁅P, frattiniIn (T ⊓ Subgroup.normalizer (P : Set G))⁆ :=
  eq_commutator_frattiniIn_of_irreducible hP.isPGroup (fun _ ha => hX.pow_eq_one hp2 hpX hP ha)
    (hX.sq_le_card_sylow hp2 hpX hP) (hT2.to_le inf_le_left) inf_le_right
    (irreducible hQT hX hp2 hpX hP).2

theorem eq_commutator_normalizer (hQT : pCoreOf 2 X ≤ T) (hT2 : IsPGroup 2 T) (hX : IsXi T X)
    (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X) (hP : IsSylowIn p P X) :
    P = ⁅P, T ⊓ Subgroup.normalizer (P : Set G)⁆ := by
  refine le_antisymm ?_ (commutator_le_left_of_le_normalizer inf_le_right)
  conv_lhs => rw [eq_commutator_frattiniIn hQT hT2 hX hp2 hpX hP]
  exact Subgroup.commutator_mono le_rfl (Subgroup.map_subtype_le _)

end Xi

theorem le_of_isSylowTwoOf {S V H : Subgroup G} (hS : QuasithinUnique.IsSylowTwoOf S H)
    (hSV : S ≤ V) (hVH : V ≤ H) (hV : IsPGroup 2 V) : V ≤ S := by
  have hmul := Subgroup.relIndex_mul_relIndex S V H hSV hVH
  have hSH : ¬ 2 ∣ S.relIndex H := hS.2.2
  have hodd : ¬ 2 ∣ S.relIndex V := fun h => hSH (hmul ▸ Dvd.dvd.mul_right h _)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV
  have hdvd : S.relIndex V ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card S V
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra h
    exact hodd (hj ▸ dvd_pow_self 2 h)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact hj

theorem pCoreOf_le_of_isSylowTwoOf {H : Subgroup G} (hT : QuasithinUnique.IsSylowTwoOf T H)
    (hXH : X ≤ H) (hTX : T ≤ Subgroup.normalizer (X : Set G)) : pCoreOf 2 X ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : T ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
    hTX.trans (normalizer_le_normalizer_pCoreOf 2 X)
  have h1 : IsPGroup 2 (T ⊔ pCoreOf 2 X : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hT.2.1 (pCoreOf_isPGroup 2 X) hN
  have h2 : T ⊔ pCoreOf 2 X ≤ H := sup_le hT.1 ((pCoreOf_le 2 X).trans hXH)
  exact le_trans le_sup_right (le_of_isSylowTwoOf hT le_sup_left h2 h1)

theorem isSylowIn_of_card_nine (hX9 : (pCoreOf 2 X).relIndex X = 9) (hPX : P ≤ X)
    (hP3 : IsPGroup 3 P) (hP9 : Nat.card P = 9) : IsSylowIn 3 P X := by
  refine ⟨hPX, hP3, fun hdvd => ?_⟩
  have h1 := Subgroup.relIndex_mul_card P X
  rw [inf_eq_left.2 hPX, hP9, card_eq_card_pCoreOf_mul_relIndex X, hX9] at h1
  have h2 : P.relIndex X = Nat.card (pCoreOf 2 X) := by omega
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 (pCoreOf_isPGroup 2 X)
  rw [h2, ha] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

end CFSG.Quasithin.P134
