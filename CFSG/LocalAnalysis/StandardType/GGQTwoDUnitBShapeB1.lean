module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBShapeA2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
  [CharP F0 2] {m : ℕ} {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}

theorem qtwoDB3_unpack {D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) :
    GGBstar p B Bs ∧ x ∈ B ∧ IsComponentOf L (Subgroup.centralizer ({x} : Set G)) ∧
      (∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S) ∧
      LargeEvenIsBmax p B ∧
      ∃ T : Subgroup G, T ≤ Subgroup.centralizer ({x} : Set G) ∧ IsPGroup 2 T ∧
        B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ := by
  obtain ⟨hrest, -⟩ := hcfg
  obtain ⟨hI, hBs, -⟩ := hrest.1
  obtain ⟨-, -, -, -, -, -, hS, hstd⟩ := hI
  obtain ⟨hbmax, hxB, -, hcomp, hcyc⟩ := hS
  exact ⟨hBs, hxB, hcomp, hcyc, hbmax, hstd.2.1⟩

theorem qtwoDB3_bmax_le (hp : p.Prime) (hB : LargeEvenIsBmax p B) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E)
    (hU : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G)) :
    Nat.card ↥E ≤ Nat.card ↥B := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hU1, hU2, hEU⟩ := hU
  obtain ⟨k, hk⟩ := (CFSG.Open.IsElemAbelian.isPGroup hE).exists_card_eq
  have hle : k ≤ CFSG.Open.twoLocalPrimeRank p G := by
    have hk' : k ≤ CFSG.Open.pRank p (Subgroup.normalizer (U : Set G)) :=
      CFSG.SectionRank.le_pRank hp.one_lt hEU hE hk
    refine hk'.trans ?_
    unfold CFSG.Open.twoLocalPrimeRank
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨Subgroup.normalizer (U : Set G),
      ⟨U, hU1, hU2, rfl⟩, rfl⟩
    rintro j ⟨H, -, rfl⟩
    exact CFSG.SectionRank.pRank_le_card_of_one_lt hp.one_lt H
  unfold LargeEvenIsBmax LargeEvenTwoLocalRank at hB
  obtain ⟨-, hBcard, -⟩ := hB
  calc Nat.card ↥E = p ^ k := hk
    _ ≤ p ^ CFSG.Open.twoLocalPrimeRank p G := Nat.pow_le_pow_right hp.pos hle
    _ = Nat.card ↥B := hBcard.symm

theorem qtwoDB3_L_normal (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 5 ≤ m)
    (hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G), g ∈ Subgroup.normalizer (L : Set G) := by
  intro g hg
  by_cases hEq : L.map (MulAut.conj g).toMonoidHom = L
  · exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hEq
  · exfalso
    have hCg : (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
        Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hg)
    have hL' : IsComponentOf (L.map (MulAut.conj g).toMonoidHom)
        (Subgroup.centralizer ({x} : Set G)) := by
      have h := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hL g
      rwa [hCg] at h
    rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hL hL' with
      hEq' | hcomm
    · exact hEq hEq'.symm
    · have hS' : (Bs ⊓ L).map (MulAut.conj g).toMonoidHom ≤
          Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.commutator_comm] at hcomm
        exact (Subgroup.map_mono inf_le_right).trans
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
      have hSp : IsPGroup p ↥(Bs ⊓ L) :=
        (CFSG.Open.IsElemAbelian.isPGroup hbase.hyp.bstar.2.1).to_le inf_le_left
      have hS'p : IsPGroup p ↥((Bs ⊓ L).map (MulAut.conj g).toMonoidHom) :=
        hSp.map (MulAut.conj g).toMonoidHom
      have hcycS' : IsCyclic ↥((Bs ⊓ L).map (MulAut.conj g).toMonoidHom) :=
        hcyc _ hS' hS'p
      have hcycS : IsCyclic ↥(Bs ⊓ L) :=
        ((Subgroup.equivMapOfInjective (Bs ⊓ L) (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).isCyclic).mpr hcycS'
      have hexp : Monoid.exponent ↥(Bs ⊓ L) ∣ 3 := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro s
        apply Subtype.ext
        have hs3 : (s : G) ^ 3 = 1 := by
          have h := hbase.hyp.bstar.2.1.2 (s : G) s.2.1
          rwa [hbase.p_eq] at h
        simpa using hs3
      haveI : IsCyclic ↥(Bs ⊓ L) := hcycS
      rw [IsCyclic.exponent_eq_card] at hexp
      have hle3 : Nat.card ↥(Bs ⊓ L) ≤ 3 := Nat.le_of_dvd (by norm_num) hexp
      have h9 := qtwoDB3_card_inf hbase hm
      omega

end CFSG.StandardType.QTwo

end
