module

public import CFSG.Quasithin.Vol2.Ch11SecB21J
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11SecB21Hall

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem le_of_hall_sylow {X B T Y : Subgroup G} (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B X)
    (hTX : T ≤ X) (hT : ¬ 2 ∣ T.relIndex X) (hBY : B ≤ Y) (hTY : T ≤ Y) : X ≤ Y := by
  have h1 : (Y ⊓ X).relIndex X ∣ B.relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X (le_inf hBY hB.1)
  have h2 : (Y ⊓ X).relIndex X ∣ T.relIndex X :=
    Subgroup.relIndex_dvd_of_le_left X (le_inf hTY hTX)
  obtain ⟨k, hk⟩ := hB.2.2
  rw [hk] at h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hj0 : j = 0 := by
    by_contra hj0
    apply hT
    rw [hj] at h2
    exact (dvd_pow_self 2 hj0).trans h2
  rw [hj0, pow_zero] at hj
  exact fun x hx => (Subgroup.relIndex_eq_one.mp hj hx).1

theorem nParam_le_nPrime_of_le_normalizer (h338 : ASInputs.AS_E_3_38_perH) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {H B U : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hn : 1 < E1.nParam H)
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ Subgroup.normalizer (L : Set G)))
    (hU : IsElemAbelian 2 U) (hVU : fsuV T I ≤ U) (hUT : U ≤ T)
    (hLTU : L ⊔ T ≤ Subgroup.normalizer (U : Set G))
    (hHU : H ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (U : Set G))
    (hBU : B ⊓ Subgroup.centralizer (U : Set G) = ⊥) :
    E1.nParam H ≤ (E3.nPrime (autI hU ⊤) : ℕ∞) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hU1 : U ≠ ⊥ := fun h => fsuV_ne_bot hyp (le_bot_iff.mp (h ▸ hVU))
  have hU2 : IsPGroup 2 ↥U := hyp.fsu.sylow.1.to_le hUT
  have hNU : Subgroup.normalizer (U : Set G) ≤ M := normalizer_le_of_isPGroup h331 hyp hU2 hU1 hLTU
  have h322 : E3.HypE322 T U :=
    ⟨isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_top, hUT, le_sup_right.trans hLTU⟩
  have huniq := isUniqueM_normalizer_inf_centralizer h331 h1102 hyp hVU hLTU hUT hU.1 hU1
  have heq : H ⊓ M = H ⊓ Subgroup.normalizer (U : Set G) :=
    le_antisymm (le_inf inf_le_left hHU) (inf_le_inf_left _ hNU)
  have hP2 : IsPGroup 2 ↥(H ⊓ M ⊓ Subgroup.centralizer (U : Set G)) :=
    isPGroup_inf_centralizer_of_hall hB hHU hBU
  have hPn : H ⊓ M ≤ Subgroup.normalizer
      ((H ⊓ M ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) : Set G) :=
    B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hHU)
  exact h338 G T U M H hU hU1 hyp.fsu.simple hyp.fsu.nonabelian h322 hyp.fsu.qtke huniq hH hn
    heq (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hPn hP2)

theorem nParam_le_of_le_normalizer (h338 : ASInputs.AS_E_3_38_perH) (hNP : FactNPrimeNat)
    (h331 : Stmt3_3_1) (h1102 : Stmt11_0_2) (hyp : Hyp11 G T L I n) {H B : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H) (hn : 1 < E1.nParam H)
    (hB : QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ Subgroup.normalizer (L : Set G)))
    (hBV : B ⊓ Subgroup.centralizer (fsuV T I : Set G) = ⊥)
    (hBN : B ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    E1.nParam H ≤ n := by
  set M := Subgroup.normalizer (L : Set G) with hMdef
  have hV := isElemAbelian_fsuV hyp
  have hLV := L_le_normalizer_fsuV hyp
  have hTV := T_le_normalizer_fsuV T I
  have hTX : T ≤ H ⊓ M := le_inf hH.1.1 hyp.normal
  have hTS : QuasithinUnique.IsSylowTwoOf T (H ⊓ M) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTX
  have hHV : H ⊓ M ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    le_of_hall_sylow hB hTX hTS.2.2 hBN hTV
  have h1 := nParam_le_nPrime_of_le_normalizer h338 h331 h1102 hyp hH hn hB hV le_rfl
    (fsuV_le_T hyp) (sup_le hLV hTV) hHV hBV
  have h2 := hNP G L (fsuV T I) n hV hyp.one_lt hLV (commutator_fsuV_eq_self hyp)
    (natModuleOf_fsuV h1102 hyp) ⊤ le_top (inf_le_right.trans (normalizer_fsuV_le h331 hyp))
  exact h1.trans (by exact_mod_cast h2)

end CFSG.Quasithin.Vol2.Ch11.SecB
