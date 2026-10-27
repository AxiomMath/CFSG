module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvariantOddPSubgroupCentralizedMulEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InvariantOddPSubgroupCentralized
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvariantOddPSubgroupCentralized
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.SFourInvariantOddPSubgroupCentralized
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- In a D-group, the commutator of an odd-prime subgroup invariant under
the centralizer of an involution with that involution lies in the odd core. -/
public theorem commutator_le_pPrimeCore_of_isDGroup
    {X : Type u} [Group X] [Finite X]
    (P : Subgroup X) (p : ℕ) (hD : IsDGroup X)
    (hp : p.Prime) (hpodd : Odd p) (hPp : IsPGroup p P)
    {t : X} (ht : IsInvolution t)
    (hPinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (P : Set X)) :
    ⁅P, Subgroup.zpowers t⁆ ≤ pPrimeCore 2 X := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let O : Subgroup X := pPrimeCore 2 X
  let : O.Normal := by dsimp [O]; infer_instance
  let q : X →* (X ⧸ O) := QuotientGroup.mk' O
  let Pbar : Subgroup (X ⧸ O) := P.map q
  let tbar : X ⧸ O := q t
  let T : Subgroup X := Subgroup.zpowers t
  let Tbar : Subgroup (X ⧸ O) := Subgroup.zpowers tbar
  have hPbarp : IsPGroup p Pbar := IsPGroup.map hPp q
  have htbar2 : tbar ^ 2 = 1 := by
    simpa [tbar] using congrArg q ht.2
  have hmap_finish (hcommbar : ⁅Pbar, Tbar⁆ = ⊥) :
      ⁅P, Subgroup.zpowers t⁆ ≤ O := by
    have hmapbot : (⁅P, Subgroup.zpowers t⁆).map q = ⊥ := by
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
      simpa [Pbar, Tbar, tbar] using hcommbar
    have hleker : ⁅P, Subgroup.zpowers t⁆ ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := ⁅P, Subgroup.zpowers t⁆) (f := q)).mp hmapbot
    simpa [q] using hleker
  by_cases htbarone : tbar = 1
  · apply hmap_finish
    simp [Tbar, htbarone]
  have htbar : IsInvolution tbar := ⟨htbarone, htbar2⟩
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using ht.2) ht.1
  have hTcard : Nat.card T = 2 := by
    simp [T, Nat.card_zpowers, htorder]
  have hTtwo : IsPGroup 2 T := by
    refine IsPGroup.of_card (n := 1) ?_
    simp [hTcard]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 T) := ⟨hTtwo⟩
  have hOcop : Nat.Coprime 2 (Nat.card O) := by
    simpa [O] using pPrimeCore_coprime_card (p := 2) (G := X)
  have hTmap : T.map q = Tbar := by
    simpa [T, Tbar, tbar] using MonoidHom.map_zpowers q t
  have hcentT : Subgroup.centralizer (T : Set X) =
      Subgroup.centralizer ({t} : Set X) := by
    dsimp [T]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcentTbar : Subgroup.centralizer (Tbar : Set (X ⧸ O)) =
      Subgroup.centralizer ({tbar} : Set (X ⧸ O)) := by
    dsimp [Tbar]
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hcentLift : Subgroup.centralizer (Tbar : Set (X ⧸ O)) =
      (Subgroup.centralizer (T : Set X)).map q := by
    rw [← hTmap]
    exact centralizer_map_quotient_eq_map_centralizer
      (G := X) (p := 2) T O (by infer_instance) hOcop
  have hQinv : Subgroup.centralizer ({tbar} : Set (X ⧸ O)) ≤
      Subgroup.normalizer (Pbar : Set (X ⧸ O)) := by
    intro c hc
    have hcTbar : c ∈ Subgroup.centralizer (Tbar : Set (X ⧸ O)) := by
      rwa [hcentTbar]
    rw [hcentLift] at hcTbar
    rcases Subgroup.mem_map.mp hcTbar with ⟨a, haT, rfl⟩
    have ha : a ∈ Subgroup.centralizer ({t} : Set X) := by
      rwa [← hcentT]
    apply Subgroup.le_normalizer_map q
    exact Subgroup.mem_map.mpr ⟨a, hPinv ha, rfl⟩
  have hTbarCent : Tbar ≤
      Subgroup.centralizer ({tbar} : Set (X ⧸ O)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    exact (Commute.refl tbar).zpow_left n
  have hTbarNormP : Tbar ≤
      Subgroup.normalizer (Pbar : Set (X ⧸ O)) :=
    hTbarCent.trans hQinv
  have hcommbar : ⁅Pbar, Tbar⁆ = ⊥ := by
    rcases hD with ⟨_hSylow, htwo⟩ | ⟨_hSylow, e7⟩ |
        ⟨_hSylow, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
    · have hPbar2 : IsPGroup 2 Pbar := by
        exact (show IsPGroup 2 (X ⧸ pPrimeCore 2 X) from htwo).to_subgroup Pbar
      have hpne2 : p ≠ 2 := by
        intro h
        subst p
        exact hpodd.not_two_dvd_nat (by norm_num)
      have hcop : Nat.Coprime (Nat.card Pbar) (Nat.card Pbar) :=
        IsPGroup.coprime_card_of_ne p 2 hpne2 Pbar Pbar hPbarp hPbar2
      have hcard : Nat.card Pbar = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (dvd_refl _)
      have hPbarbot : Pbar = ⊥ := Subgroup.eq_bot_of_card_eq Pbar hcard
      simp [hPbarbot]
    · let e : (X ⧸ O) ≃* alternatingGroup (Fin 7) := by
        simpa [O] using e7.some
      have hPbarcent : Pbar ≤
          Subgroup.centralizer ({tbar} : Set (X ⧸ O)) :=
        invariant_oddP_subgroup_centralized_of_mulEquiv e p
          (fun R hRp s hs hRinv =>
            aSeven_invariant_oddP_subgroup_centralized
              p hp hpodd R hRp hs hRinv)
          Pbar hPbarp htbar hQinv
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      rwa [hcentTbar]
    · let : L.Normal := hLnormal
      have htL : tbar ∈ L := by
        let qL : (X ⧸ O) →* ((X ⧸ O) ⧸ L) := QuotientGroup.mk' L
        have hq2 : (qL tbar) ^ 2 = 1 := by
          simpa [qL] using congrArg qL htbar2
        have hord2 : orderOf (qL tbar) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one hq2
        have hordCard : orderOf (qL tbar) ∣ Nat.card ((X ⧸ O) ⧸ L) :=
          orderOf_dvd_natCard (qL tbar)
        have hcardIndex : Nat.card ((X ⧸ O) ⧸ L) = L.index := by
          exact (Subgroup.index_eq_card L).symm
        rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with hone | htwo
        · have hqone : qL tbar = 1 := orderOf_eq_one_iff.mp hone
          exact (QuotientGroup.eq_one_iff tbar).mp (by simpa [qL] using hqone)
        · exfalso
          have h2dvd : 2 ∣ L.index := by
            have h2card : 2 ∣ Nat.card ((X ⧸ O) ⧸ L) := by
              simpa only [htwo] using hordCard
            simpa only [hcardIndex] using h2card
          exact hLindex.not_two_dvd_nat h2dvd
      have hTbarL : Tbar ≤ L :=
        Subgroup.zpowers_le.mpr (by simpa [Tbar] using htL)
      let C : Subgroup (X ⧸ O) := ⁅Pbar, Tbar⁆
      let R : Subgroup (X ⧸ O) := Pbar ⊓ L
      have hCleP : C ≤ Pbar := by
        simpa [C] using
          (Subgroup.le_normalizer_iff_commutator_le_left
            (H := Tbar) (K := Pbar)).mp hTbarNormP
      have hPbarNormL : Pbar ≤ Subgroup.normalizer (L : Set (X ⧸ O)) := by
        rw [L.normalizer_eq_top]
        exact le_top
      have hPbarLleL : ⁅Pbar, L⁆ ≤ L := by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.le_normalizer_iff_commutator_le_left
          (H := Pbar) (K := L)).mp hPbarNormL
      have hCleL : C ≤ L := by
        exact (Subgroup.commutator_mono le_rfl hTbarL).trans hPbarLleL
      have hCleR : C ≤ R := fun x hx => ⟨hCleP hx, hCleL hx⟩
      let tL : L := ⟨tbar, htL⟩
      have htLinv : IsInvolution tL := by
        constructor
        · intro htLone
          exact htbarone (congrArg Subtype.val htLone)
        · exact Subtype.ext htbar2
      let RL : Subgroup L := R.subgroupOf L
      have hRp : IsPGroup p R := hPbarp.to_inf_left
      have hRleL : R ≤ L := inf_le_right
      have hRLp : IsPGroup p RL :=
        hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRleL).symm
      have hRLinv : Subgroup.centralizer ({tL} : Set L) ≤
          Subgroup.normalizer (RL : Set L) := by
        intro c hc
        have hcQ : (c : X ⧸ O) ∈
            Subgroup.centralizer ({tbar} : Set (X ⧸ O)) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val
            (Subgroup.mem_centralizer_singleton_iff.mp hc)
        have hcNormP : (c : X ⧸ O) ∈
            Subgroup.normalizer (Pbar : Set (X ⧸ O)) := hQinv hcQ
        have hcNormL : (c : X ⧸ O) ∈
            Subgroup.normalizer (L : Set (X ⧸ O)) := by
          rw [L.normalizer_eq_top]
          trivial
        rw [Subgroup.mem_normalizer_iff]
        intro x
        change ((x : X ⧸ O) ∈ Pbar ∧ (x : X ⧸ O) ∈ L ↔
          (c : X ⧸ O) * (x : X ⧸ O) * (c : X ⧸ O)⁻¹ ∈ Pbar ∧
            (c : X ⧸ O) * (x : X ⧸ O) * (c : X ⧸ O)⁻¹ ∈ L)
        exact and_congr
          ((Subgroup.mem_normalizer_iff.mp hcNormP) (x : X ⧸ O))
          ((Subgroup.mem_normalizer_iff.mp hcNormL) (x : X ⧸ O))
      rcases hKprime with ⟨r, f, hr, hrodd, hf, hKcard⟩
      let : Fact r.Prime := ⟨hr⟩
      have hKodd : Odd (Nat.card K) := by
        rw [hKcard]
        exact hrodd.pow
      have hKprime' : IsOddPrimePower (Nat.card K) :=
        ⟨r, f, hr, hrodd, hf, hKcard⟩
      let : Finite (PGL2 K) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk
          Matrix.ProjGenLinGroup.mk_surjective
      have hRLcent : RL ≤ Subgroup.centralizer ({tL} : Set L) := by
        rcases hLmodel with hpsl | hpgl
        · exact invariant_oddP_subgroup_centralized_of_mulEquiv
            hpsl.some p
            (fun U hUp s hs hUinv =>
              psl2_invariant_oddP_subgroup_centralized
                hKcard hrodd hpodd U hUp hs hUinv)
            RL hRLp htLinv hRLinv
        · by_cases hK3 : Nat.card K = 3
          · let : Fintype K := Fintype.ofFinite K
            have hKFintype : Fintype.card K = 3 := by
              simpa [Nat.card_eq_fintype_card] using hK3
            let eK : ZMod 3 ≃+* K :=
              ZMod.ringEquivOfPrime K Nat.prime_three hKFintype
            let eModel : PGL2 K ≃* Equiv.Perm (Fin 4) :=
              (pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm
            exact invariant_oddP_subgroup_centralized_of_mulEquiv
              (hpgl.some.trans eModel) p
              (fun U hUp s hs hUinv =>
                sFour_invariant_oddP_subgroup_centralized
                  p hp hpodd U hUp hs hUinv)
              RL hRLp htLinv hRLinv
          · have hKone : 1 < Nat.card K := Finite.one_lt_card
            have hKgt : 3 < Nat.card K := by
              rcases hKodd with ⟨a, ha⟩
              omega
            exact invariant_oddP_subgroup_centralized_of_mulEquiv
              hpgl.some p
              (fun U hUp s hs hUinv =>
                pgl2_invariant_oddP_subgroup_centralized
                  K hKprime' hKgt p hp hpodd U hUp hs hUinv)
              RL hRLp htLinv hRLinv
      have hRcent : R ≤
          Subgroup.centralizer ({tbar} : Set (X ⧸ O)) := by
        intro x hxR
        let xL : L := ⟨x, hxR.2⟩
        have hxRL : xL ∈ RL := hxR
        have hxCent := hRLcent hxRL
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp hxCent)
      have hCcent : C ≤
          Subgroup.centralizer ({tbar} : Set (X ⧸ O)) :=
        hCleR.trans hRcent
      have hCTbot : ⁅C, Tbar⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        rwa [hcentTbar]
      have hTbarTwo : IsPGroup 2 Tbar := by
        rw [← hTmap]
        exact IsPGroup.map hTtwo q
      have hpne2 : p ≠ 2 := by
        intro h
        subst p
        exact hpodd.not_two_dvd_nat (by norm_num)
      have hcop : Nat.Coprime (Nat.card Tbar) (Nat.card Pbar) :=
        IsPGroup.coprime_card_of_ne 2 p hpne2.symm
          Tbar Pbar hTbarTwo hPbarp
      have hCself : ⁅C, Tbar⁆ = C := by
        simpa [C] using
          BenderSuzuki.ig1114_commutator_idempotent_of_coprime
            Pbar Tbar hcop hTbarNormP
      change C = ⊥
      exact hCself.symm.trans hCTbot
  exact hmap_finish hcommbar

end CFSG.GorensteinWalter
