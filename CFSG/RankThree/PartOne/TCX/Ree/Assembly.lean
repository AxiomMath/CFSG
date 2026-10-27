module

public import CFSG.RankThree.PartOne.TCX.Ree.Sector
public import CFSG.RankThree.PartOne.TCX.Ree.Context
public import CFSG.RankThree.PartOne.TCX.Ree.StdForm
public import CFSG.RankThree.PartOne.TCX.Ree.PlaneSplit
public import CFSG.RankThree.PartOne.TCX.AssemblyTools
public import CFSG.RankThree.PartOne.TCX.Transport
public import CFSG.RankThree.PartOne.TCX.Generator
public import CFSG.RankThree.PartOne.TCX.Interface
public import CFSG.RankThree.PartOne.K128.F4Syl
public import CFSG.RankThree.PartOne.S11c.Sec66PSUFrame

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128 CFSG.RankThree.PartOne.KLC
  CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)

open CFSG.RankThree.PartOne.TCX

section Main


theorem threeCompT_twistedF4 : ThreeCompT .twistedF4 := by
  intro T _ _ p hp hp5 hLR hpr n f₀ hf₀ hM α hαp hαinn hLRA hX x hxp hx1 hαx
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  obtain ⟨a, K, hKf, hKfin, hKc, σ, φ, ha, hK, hfa, hσ, hσord, hzp⟩ :=
    stdForm_twistedF4 hp hp5 hM hαp hαinn
  obtain ⟨α', hα'def⟩ : ∃ α' : MulAut (F4.reeGamma K a), α' = MulAut.congr φ α := ⟨_, rfl⟩
  rw [← hα'def] at hzp
  have hαφ : ∀ t, α' (φ t) = φ (α t) := fun t => by
    rw [hα'def]
    exact congrArg φ (congrArg α (φ.symm_apply_apply t))
  have hα'p : α' ^ p = 1 := by rw [hα'def, ← map_pow, hαp, map_one]
  have hα'out : α' ∉ innerAut (F4.reeGamma K a) := by
    rw [hα'def]
    exact fun h => hαinn ((mem_innerAut_congr φ α).mp h)
  have hLRG : LocalRankAut p (F4.reeGamma K a) α' := by
    rw [hα'def]
    exact localRankAut_congr φ hp hLRA
  have hβp : F4.reeGammaFieldAut K a σ ^ p = 1 := by
    rw [← reeGammaFieldAutHom_apply, ← map_pow, ← hσord, pow_orderOf_eq_one, map_one]
  have hxφ : φ x ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hxφ1 : φ x ≠ 1 := fun h => hx1 (φ.injective (by rw [h, map_one]))
  have hxo : orderOf (φ x) = p := orderOf_eq_prime hxφ hxφ1
  have hα'x : α' (φ x) = φ x := by rw [hαφ, hαx]
  have hβx : F4.reeGammaFieldAut K a σ (φ x) = φ x := fixed_of_zpowers_eq hzp.symm hα'x
  have : Finite (ModGL F4.tag K) := finite_modGL
  have : Finite (F4.reeGamma K a) := Subtype.finite
  have hpr' : 2 ≤ CFSG.pRank p (F4.reeGamma K a) := by
    rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt φ]
    exact hpr
  obtain ⟨d, hd, hpd⟩ := ree_class hK hp hp5 hpr'
  have hq1' : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  have hQ : 2 ^ (2 * a + 1) = (2 ^ f₀) ^ p := by rw [hfa, mul_comm, pow_mul]
  have hpdq : p ∣ phiF4 d (2 ^ f₀) := dvd_phiF4_of_dvd_pow hp hq1' hd (by rw [← hQ]; exact hpd)
  obtain ⟨L, _, _, _, _, _, K₀, _, _, _, _, _, a₀, D₀, D, hK₀, hf₀eq, hsh⟩ :=
    ree_sector_context hp hp5 hf₀ hK hfa hσord hσ
  set α₀ : MulAut (F4.reeGamma K a) := (F4.reeGammaFieldAut K a σ) ^ ((p + 1) / 2) with hα₀def
  have hα₀p : α₀ ^ p = 1 := hsh.ordα
  have hzp₀ : Subgroup.zpowers α₀ = Subgroup.zpowers (F4.reeGammaFieldAut K a σ) := by
    have h2 : 2 * ((p + 1) / 2) = p + 1 := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
      omega
    have hsq : α₀ ^ 2 = F4.reeGammaFieldAut K a σ := by
      rw [hα₀def, ← pow_mul, mul_comm, h2, pow_succ, hβp, one_mul]
    refine le_antisymm (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
      (Subgroup.zpowers_le.2 ?_)
    rw [← hsq]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hxα₀ : α₀ (φ x) = φ x := fixed_of_zpowers_eq hzp₀ hβx
  have hzpα : Subgroup.zpowers α' = Subgroup.zpowers α₀ := hzp.trans hzp₀.symm
  have hcases : SectorConclusion p α₀ (φ x) := by
    rcases hd with rfl | rfl | rfl
    ·
      exfalso
      simp only [phiF4] at hpdq
      have hpK : p ∣ Nat.card K - 1 := by
        have h1 : 2 ^ f₀ - 1 ∣ (2 ^ f₀) ^ p - 1 ^ p := Nat.sub_dvd_pow_sub_pow _ _ _
        rw [one_pow] at h1
        rw [hK, hQ]
        exact hpdq.trans h1
      have hσfix : ∀ ζ : Kˣ, ζ ^ p = 1 → Units.map σ.toRingHom.toMonoidHom ζ = ζ := by
        intro ζ hζ
        apply Units.ext
        change σ (ζ : K) = ζ
        rw [hσ]
        obtain ⟨t, ht⟩ := hpdq
        have h1 : 2 ^ f₀ = p * t + 1 := by
          have := Nat.one_le_two_pow (n := f₀)
          omega
        have h2 : ζ ^ (2 ^ f₀) = ζ := by rw [h1, pow_succ, pow_mul, hζ, one_pow, one_mul]
        simpa using congrArg Units.val h2
      obtain ⟨R, U, hR, hRc, hRfix, hU, hU2, hUα, hRU⟩ := ree_plane_split hK hp σ hσfix hpK
      have hstab := mem_stabSubgroup_of_zpowers_eq hp.pos hzp hβp hUα
      exact hLRG hα'p hα'out R hR hRc (fun r hr => fixed_of_zpowers_eq hzp (hRfix r hr)) U hU hU2
        hstab.1 hRU
    · subst hf₀eq
      simp only [phiF4] at hpdq
      exact ree_sector_phi2 D₀ D hp hp5 hK₀ hK hfa hsh hpdq hxo hxα₀
    · subst hf₀eq
      simp only [phiF4] at hpdq
      exact ree_sector_phi4 D₀ D hp hp5 hK₀ hK hfa hsh hpdq hxo hxα₀
  have hlayer : SingleLayerData p α₀ (Subgroup.centralizer ({φ x} : Set (F4.reeGamma K a))) →
      SingleLayerData p α (Subgroup.centralizer ({x} : Set T)) := fun hlay => by
    have hlay' : SingleLayerData p α'
        ((Subgroup.centralizer ({x} : Set T)).map φ.toMonoidHom) := by
      rw [map_centralizer_singleton_mulEquiv']
      exact singleLayerData_of_zpowers_eq hp.pos hzpα hα₀p hlay
    exact singleLayerData_of_mulEquiv (p := p) φ hαφ hlay'
  unfold SectorConclusion at hcases
  refine ⟨fun D' hD hDst => ?_, fun S hS hS2 hSα hxS => ?_⟩
  · rcases hcases with hlay | ⟨hreg, -⟩
    · obtain ⟨D₁, hD₁, hst, huniq, hfix, hclaims⟩ := hlayer hlay
      have hDD₁ := huniq D' hD
      subst hDD₁
      exact hclaims
    · exact (no_component_of_comm (centralizer_comm_of_map φ hreg) hD).elim
  · rcases hcases with hlay | ⟨-, hnorm⟩
    · obtain ⟨D₁, hD₁, hst, huniq, hfix, -⟩ := hlayer hlay
      exact ⟨D₁, hD₁, hst, huniq, hfix⟩
    · exfalso
      have hSG : S.map φ.toMonoidHom ≠ ⊥ := fun hbot =>
        hS ((Subgroup.map_eq_bot_iff_of_injective S φ.injective).mp hbot)
      exact hnorm _ hSG (hS2.map φ.toMonoidHom) (normalizer_map_of_mem φ hxS)

end Main

end CFSG.RankThree.PartOne.TCX.Ree
