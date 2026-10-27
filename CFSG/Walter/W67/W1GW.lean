module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter

theorem pPrimeCore_quotient_eq_bot {X : Type*} [Group X] [Finite X] :
    CFSG.pPrimeCore 2 (X ⧸ CFSG.pPrimeCore 2 X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 X
  set π := QuotientGroup.mk' O
  have hO : Nat.Coprime 2 (Nat.card O) := CFSG.pPrimeCore_coprime_card
  rw [CFSG.pPrimeCore_eq_bot_iff]
  intro W hWn hW
  set V := W.comap π
  have hVcard : Nat.card V = Nat.card W * Nat.card O := by
    have h1 := card_eq_card_map_mul_card_inf_ker π V
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O),
      QuotientGroup.ker_mk', inf_eq_right.mpr] at h1
    · exact h1
    · intro x hx
      change π x ∈ W
      have : π x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [this]
      exact W.one_mem
  have hVO : V ≤ O := le_sSup ⟨hWn.comap π, by rw [hVcard]; exact Nat.Coprime.mul_right hW hO⟩
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O w
  have : x ∈ O := hVO hw
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr this

theorem mem_of_index_two_of_odd {X : Type*} [Group X] {N : Subgroup X} (hN : N.index = 2)
    {x : X} (hx : Odd (orderOf x)) : x ∈ N := by
  obtain ⟨j, hj⟩ := hx
  have : x = (x ^ (j + 1)) ^ 2 := by
    rw [← pow_mul, show (j + 1) * 2 = 2 * j + 1 + 1 by ring, pow_succ, ← hj, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact Subgroup.sq_mem_of_index_two hN _

theorem exists_psl2_of_kleinFour
    {X : Type} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 2 X = ⊥) (hS : ∀ P : Sylow 2 X, IsKleinFour (P : Subgroup X))
    (h2 : ¬ IsPGroup 2 X) :
    ∃ L : Subgroup X, L.Normal ∧ Odd L.index ∧ ∃ (p' f' : ℕ) (_ : Fact p'.Prime), Odd p' ∧
      0 < f' ∧ Nonempty (L ≃* PSL(2, GaloisField p' f')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : HasDihedralSylowTwo X := by
    intro P
    have := hS P
    refine ⟨1, le_rfl, ?_⟩
    rw [pow_one]
    exact IsKleinFour.nonempty_mulEquiv
  set O := CFSG.pPrimeCore 2 X
  set π := QuotientGroup.mk' O
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hO
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have h4 : ∀ P : Subgroup X, IsPGroup 2 P → Nat.card P ∣ 4 := by
    intro P hP
    obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
    rw [← (hS Q).card_four]
    exact Subgroup.card_dvd_of_le hQ
  rcases gorensteinWalter X hD with ⟨-, hX2⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, K', hK', L, hLn, hLi, hLm⟩
  · exact absurd (hX2.of_injective π hπinj) h2
  · exfalso
    have hcard : Nat.card X = 2520 := by
      have h1 : Nat.card X = Nat.card (X ⧸ O) :=
        Nat.card_congr (MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩).toEquiv
      have h2 : Nat.card (X ⧸ O) = Nat.card (alternatingGroup (Fin 7)) :=
        Nat.card_congr e.toEquiv
      rw [h1, h2, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 2 (n := 3)
      (by rw [hcard]; norm_num)
    have := h4 Q (IsPGroup.of_card hQ)
    rw [hQ] at this
    norm_num at this
  ·
    set L' := L.comap π
    have eL : L' ≃* L := (L'.equivMapOfInjective π hπinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective hπsurj L))
    have hL'n : L'.Normal := hLn.comap π
    have hL'i : Odd L'.index := by
      rw [Subgroup.index_comap_of_surjective L hπsurj]
      exact hLi
    obtain ⟨p', f', hp', hp'odd, hf', hcard⟩ := hK'
    have : Fact p'.Prime := ⟨hp'⟩
    rcases hLm with hPSL | hPGL
    ·
      obtain ⟨eL2⟩ := hPSL
      have : Fintype K' := Fintype.ofFinite K'
      have : Fintype (GaloisField p' f') := Fintype.ofFinite _
      let e3 : K' ≃+* GaloisField p' f' := FiniteField.ringEquivOfCardEq (by
        rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcard,
          GaloisField.card _ _ (by omega)])
      exact ⟨L', hL'n, hL'i, p', f', ⟨hp'⟩, hp'odd, hf',
        ⟨eL.trans (eL2.trans (psl2RingEquiv e3))⟩⟩
    ·
      exfalso
      obtain ⟨eL2⟩ := hPGL
      have h8 : 8 ∣ Nat.card L' := by
        rw [Nat.card_congr (eL.trans eL2).toEquiv, pgl2_card_formula K']
        exact Dvd.dvd.mul_left (Suzuki.eight_dvd_sq_sub_one (by rw [hcard]; exact hp'odd.pow))
          _
      obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := L') 2 (n := 3)
        (by norm_num; exact h8)
      have hQ2 : IsPGroup 2 (Q.map L'.subtype) := (IsPGroup.of_card hQ).map _
      have := h4 _ hQ2
      rw [Subgroup.card_map_of_injective L'.subtype_injective, hQ] at this
      norm_num at this

end CFSG.Walter.W67
