module

import CFSG.Quasithin.Background.H158UTrio
import CFSG.Quasithin.Background.H158UHB
import CFSG.Quasithin.Background.H158UV7
public import CFSG.Quasithin.Background.H158N3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.AppendixH.H14.Vocab
public import CFSG.Quasithin.Background.H158TNF
public import CFSG.Quasithin.Background.HZ82Base

public section

namespace CFSG.Quasithin.H158U

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.LU CFSG.Quasithin.H158T
  CFSG.Quasithin.H158N CFSG.Quasithin.H
open scoped Pointwise

theorem eq_one_or_eq_of_orderOf_two {V : Type*} [CommGroup V] {z w : V} (hz : orderOf z = 2)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h1 := zpow_mod_orderOf z i
  rw [hz] at h1
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · left
    rw [← h1]
    simp [h]
  · right
    rw [← h1]
    simp [h]

theorem rImg_fix {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (M : Subgroup S24) {z : V} (hz : orderOf z = 2)
    (hfix : fixV (rImg ρ (pCoreOf 2 M)) = Subgroup.zpowers z) : ∀ g ∈ rImg ρ M, g z = z := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  refine eq_of_fixV_normalized (K := rImg ρ (pCoreOf 2 M)) (P := rImg ρ M) ?_ hz1 ?_ ?_
  · rintro _ ⟨m, hm, rfl⟩ _ ⟨κ, hκ, rfl⟩
    refine ⟨m * κ * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact Subgroup.mem_subgroupOf.2 (conj_mem_pCoreOf 2 (Subgroup.mem_subgroupOf.1 hm)
      (Subgroup.mem_subgroupOf.1 hκ))
  · intro k hk
    exact (mem_fixV.1 (hfix ▸ Subgroup.mem_zpowers z)) k hk
  · intro w hw
    have hwm : w ∈ fixV (rImg ρ (pCoreOf 2 M)) := mem_fixV.2 hw
    rw [hfix] at hwm
    exact eq_one_or_eq_of_orderOf_two hz hwm

private theorem conj_trQ_le_perfectCore {Tr : Finset (Finset (Fin 24))} {h : S24} (hh : h ∈ AutPerm)
    (hTr : Tr = h • labTrio) :
    trQ.map (MulAut.conj h).toMonoidHom ≤ perfectCore (MY M24g Tr) := by
  have hKle : trQ.map (MulAut.conj h).toMonoidHom ≤ MY M24g Tr := by
    rintro _ ⟨q, hq, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, MulAction.mem_stabilizer_iff.2 ?_⟩
    · exact AutPerm.mul_mem (AutPerm.mul_mem hh (trQ_le hq)) (AutPerm.inv_mem hh)
    · have hq' : q • labTrio = labTrio := smul_labTrio (block0_le lab (trQ_le_trioP0 hq))
      show (h * q * h⁻¹) • Tr = Tr
      rw [hTr, smul_smul, show h * q * h⁻¹ * h = h * q by group, mul_smul, hq']
  refine le_perfectCore_of_perfect hKle ?_
  rw [← Subgroup.map_commutator, commutator_trQ]

theorem h158_main
    {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))} {B : Finset (Fin 24)}
    {T₀ : Subgroup S24} (cfg : Cfg14 a b O Tr S B T₀) {V : Type} [CommGroup V]
    (ρ : ↥M24g →* MulAut V)
    (β : ↥(⊤ : Subgroup V) →* ↥(mathModel false 24 a b M24g).sec ⧸
      (mathModel false 24 a b M24g).ker.subgroupOf (mathModel false 24 a b M24g).sec)
    (hreal : RealizesBy (mathModel false 24 a b M24g) ρ.range ⊤ ⊥ ρ.rangeRestrict β)
    {V₇ : Subgroup V} (hrk1 : rk ↥(fixV (rImg ρ (KY M24g S))) = 1)
    (hvec : ∃ z : V, fixV (rImg ρ (KY M24g S)) = Subgroup.zpowers z)
    (hcf : IsChiefFactorUnder (actsOnModule (rImg ρ (MY M24g S))) (fixV (rImg ρ (KY M24g S))) V₇)
    (hrk7 : rk ↥V₇ = 1 + 6) :
    V₇ ≤ commV (rImg ρ (perfectCore (MY M24g Tr))) := by
  have hreal' : RealizesBy (FFModel.golaySec M24g (G6.coreMod 24) golayC) ρ.range ⊤ ⊥
      ρ.rangeRestrict β := hreal
  have hMC : MathieuCocode24 ρ.range ⊤ ⊥ := (realizes_iff _ _ _ _).2 ⟨ρ.rangeRestrict, β, hreal'⟩
  have hVcard : Nat.card V = 2 ^ 11 := cocode24_card hMC
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hVcard]; positivity)
  obtain ⟨e, he⟩ := SecCoords.exists_equiv cocodeCoords (fun _ hσ => preserves_cocode hσ) hreal'
  have hcompat : ∀ (γ : ↥AutPerm) (v : V), e (ρ γ v) = rho11 AutPerm le_rfl γ (e v) :=
    fun γ v => he γ v
  have hinj : Function.Injective ρ := rho_injective ρ e hcompat
  obtain ⟨z, hfixz⟩ := hvec
  have hV₁card : Nat.card ↥(fixV (rImg ρ (KY M24g S))) = 2 := by
    simpa using card_eq_two_pow_of_rk hVcard hrk1
  have hz2 : Nat.card ↥(Subgroup.zpowers z) = 2 := hfixz ▸ hV₁card
  have hzord : orderOf z = 2 := by rwa [Nat.card_zpowers] at hz2
  have hz1 : z ≠ 1 := fun h => by simp [h] at hzord
  have hGz : ∀ g ∈ rImg ρ (MY M24g S), g z = z := rImg_fix ρ (MY M24g S) hzord hfixz
  have hT₀A : T₀ ≤ AutPerm := cfg.sylow.1
  obtain ⟨hTrcard, hTroct, hTrdisj, hTrcov⟩ := cfg.trio
  obtain ⟨h, hh, hTrh, hhT⟩ := trio_conj_form T₀ cfg.sylow Tr hTrcard
    (fun O' hO' => (hTroct O' hO').1) hTrdisj hTrcov cfg.stab_Tr
  set g : ↥AutPerm := ⟨h, hh⟩ with hg
  set T : Subgroup ↥AutPerm := T₀.subgroupOf AutPerm with hT
  have hTcard : Nat.card ↥T = 2 ^ 10 := by
    rw [hT, card_sylow_two cfg.sylow, factor_AutPerm]
  have hTS : ∀ t ∈ T, g⁻¹ * t * g ∈ stabUT := by
    intro t ht
    obtain ⟨x, hx, hxe⟩ := hhT (t : S24) (Subgroup.mem_subgroupOf.1 ht)
    have : x = g⁻¹ * t * g := Subtype.ext hxe
    rwa [← this]
  have hzT : ∀ t ∈ T, ρ t z = z := by
    intro t ht
    have ht' : (t : S24) ∈ T₀ := Subgroup.mem_subgroupOf.1 ht
    exact hGz _ ⟨t, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨t.2,
      MulAction.mem_stabilizer_iff.2 (cfg.stab_S _ ht')⟩), rfl⟩
  obtain ⟨hlt, -, hinvV₇, hmin⟩ := hcf
  have hV7card : Nat.card ↥V₇ = 2 ^ 7 := card_eq_two_pow_of_rk hVcard (by simpa using hrk7)
  have hzS : z ∈ fixV (T.map ρ) := by
    refine mem_fixV.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact hzT t ht
  have hle : V₇ ≤ vZ ρ.range z :=
    le_vZ_of_chief hMC hz1 (Subgroup.map_le_range ρ T) (card_map_sylow ρ hinj T hTcard) hzS
      (G := rImg ρ (MY M24g S)) (Subgroup.map_le_range ρ _) hGz hVcard hV7card hz2
      (hfixz ▸ hlt)
      (fun g' hg' u hu => hinvV₇ (fun v => g' v) ⟨g', hg', rfl⟩ u hu)
      (fun W hzW hWV hWinv => by
        have := hmin W (hfixz ▸ hzW) hWV (by
          rintro f ⟨g', hg', rfl⟩ u hu
          exact hWinv g' hg' u hu)
        rwa [hfixz] at this)
  have hb := hb_conj ρ e hcompat g T hTcard hTS hz1 hzT
  have hK := conj_trQ_le_perfectCore hh hTrh
  refine hle.trans (hb.trans (commV_le_iff.2 fun φ hφ v => mem_commV ?_ v))
  obtain ⟨x, ⟨q, hq, rfl⟩, rfl⟩ := hφ
  exact ⟨g * q * g⁻¹, Subgroup.mem_subgroupOf.2 (hK ⟨(q : S24), Subgroup.mem_subgroupOf.1 hq, rfl⟩),
    rfl⟩

end CFSG.Quasithin.H158U
