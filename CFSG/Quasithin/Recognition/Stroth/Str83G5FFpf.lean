module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1B7
import CFSG.LieType.Ree.SuzukiBorelHall

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree
open CFSG.RankThree.GF2n.Tim81.Sec2 CFSG.QuasithinUnique.Setup.X7

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem mem_of_commutator_mem_of_isSzNatural
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) {L N : Subgroup G}
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G))
    (hHN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hE : IsElemAbelian 2 (Ch3z.chiefMod L N))
    (hO : pCoreOf 2 (L1 ⊔ S) ≤ centralizerMod L (L1 ⊔ S) N)
    (e : oTwoQuot ↥(L1 ⊔ S) ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)))
    (he : (szSbar L1 L2 S).map e.toMonoidHom = suzukiU a (GaloisField 2 (2 * a + 1)))
    (hρ : letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
      letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
      IsSzNatural (sectionRep hHL hHN hNL hE hO e))
    {δ : G} (hδ : δ ∈ borelOf L1 S) (hodd : Odd (orderOf δ)) (h1 : δ ≠ 1)
    {n : G} (hn : n ∈ N) (hδn : δ * n * δ⁻¹ * n⁻¹ ∈ L) : n ∈ L := by
  classical
  let K := GaloisField 2 (2 * a + 1)
  have hK : Nat.card K = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  letI : CommGroup (Ch3z.chiefMod L N) := l2ChiefSectionCommGroup hE
  letI : Module (ZMod 2) (Additive (Ch3z.chiefMod L N)) := l2ChiefSectionModule hE
  let ρ : Representation (ZMod 2) (suzukiGroup a K) (Additive (Ch3z.chiefMod L N)) :=
    sectionRep hHL hHN hNL hE hO e
  have hρ' : IsSzNatural ρ := hρ
  have hδH : δ ∈ L1 ⊔ S :=
    Subgroup.mem_sup_left ((CFSG.Quasithin.F1.borelOf_le L1 S) hδ)
  let δH : ↥(L1 ⊔ S) := ⟨δ, hδH⟩
  let g : suzukiGroup a K := e (QuotientGroup.mk δH)
  have hg1 : g ≠ 1 := by
    intro hg
    have hq : (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) δH = 1 := by
      apply e.injective
      simpa [g] using hg
    have hδcore : δ ∈ pCoreOf 2 (L1 ⊔ S) := by
      have hmem : δH ∈ pCore 2 ↥(L1 ⊔ S) := by
        have hker : δH ∈ MonoidHom.ker (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) := by
          rw [MonoidHom.mem_ker]
          exact hq
        rwa [QuotientGroup.ker_mk'] at hker
      exact (CFSG.Quasithin.F1.mem_pCore_iff_coe δH).mp hmem
    have hone : (⟨δ, hδcore⟩ : ↥(pCoreOf 2 (L1 ⊔ S))) = 1 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hoddCore : Odd (orderOf (⟨δ, hδcore⟩ : ↥(pCoreOf 2 (L1 ⊔ S)))) := by
        rw [Subgroup.orderOf_mk]
        exact hodd
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L1 ⊔ S))) ⟨δ, hδcore⟩
      rw [hj] at hoddCore
      have hj0 : j = 0 := by
        by_contra hne
        exact (Nat.not_odd_iff_even.mpr (by rw [Nat.even_pow]; exact ⟨even_two, hne⟩)) hoddCore
      rw [hj0, pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    exact h1 (by simpa using congrArg Subtype.val hone)
  have hoddg : Odd (orderOf g) := by
    have hoddH : Odd (orderOf δH) := by
      rw [Subgroup.orderOf_mk]
      exact hodd
    have hdvd1 : orderOf ((QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) δH) ∣
        orderOf δH := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) δH
      simpa using h
    have hdvd2 : orderOf g ∣
        orderOf ((QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) δH) := by
      rw [show g = e ((QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S))) δH) from rfl,
        MulEquiv.orderOf_eq]
    exact Odd.of_dvd_nat hoddH (hdvd2.trans hdvd1)
  have hδNS : δ ∈ Subgroup.normalizer (S : Set G) := by
    refine hB ?_
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hδ)
  have hδNH : δH ∈ Subgroup.normalizer ((S.subgroupOf (L1 ⊔ S) : Subgroup ↥(L1 ⊔ S)) :
      Set ↥(L1 ⊔ S)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hδsS : δ * (s : G) * δ⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp hδNS (s : G)).mp hsS
      exact Subgroup.mem_subgroupOf.mpr hδsS
    · intro hs
      have hsS : δ * (s : G) * δ⁻¹ ∈ S := Subgroup.mem_subgroupOf.mp hs
      have hδsS : δ⁻¹ * (δ * (s : G) * δ⁻¹) * δ ∈ S := by
        simpa using
          (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hδNS) _).mp hsS
      have heq : δ⁻¹ * (δ * (s : G) * δ⁻¹) * δ = (s : G) := by group
      rw [heq] at hδsS
      exact Subgroup.mem_subgroupOf.mpr hδsS
  have hqN : QuotientGroup.mk δH ∈ Subgroup.normalizer
      (((S.subgroupOf (L1 ⊔ S)).map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))) :
        Set (oTwoQuot ↥(L1 ⊔ S))) :=
    Subgroup.le_normalizer_map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))
      (Subgroup.mem_map_of_mem _ hδNH)
  have hgNU : g ∈ Subgroup.normalizer ((suzukiU a K) : Set (suzukiGroup a K)) := by
    have h := Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hqN)
    have hmap : Subgroup.map e.toMonoidHom
        (Subgroup.map (QuotientGroup.mk' (pCore 2 ↥(L1 ⊔ S)))
          (S.subgroupOf (L1 ⊔ S))) = suzukiU a K := by
      rw [Subgroup.map_map]
      have h' := he
      rw [Subgroup.map_map] at h'
      simpa [szSbar] using h'
    rwa [hmap] at h
  have hgB : g ∈ suzukiB a K := by
    have h := hgNU
    rwa [CFSG.Quasithin.H13.normalizer_suzukiU_e34 hK] at h
  obtain ⟨v, hvB, htT⟩ :=
    exists_conj_mem_suzukiT_of_mem_suzukiB_of_odd hK hgB hoddg
  let t : suzukiGroup a K := v * g * v⁻¹
  have ht1 : t ≠ 1 := by
    intro ht
    apply hg1
    have h := congrArg (fun z => v⁻¹ * z * v) ht
    simpa [t, mul_assoc] using h
  have hδnN : δ * n * δ⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hHN hδH) n).mp hn
  have hιeq : Ch3z.chiefIota hNL (⟨δ * n * δ⁻¹, hδnN⟩ : ↥N) =
      Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N) := by
    have hcN : δ * n * δ⁻¹ * n⁻¹ ∈ N := mul_mem hδnN (inv_mem hn)
    have hfac : (⟨δ * n * δ⁻¹, hδnN⟩ : ↥N) =
        (⟨δ * n * δ⁻¹ * n⁻¹, hcN⟩ : ↥N) * ⟨n, hn⟩ := by
      apply Subtype.ext
      change δ * n * δ⁻¹ = (δ * n * δ⁻¹ * n⁻¹) * n
      group
    rw [hfac, map_mul,
      (Ch3z.chiefIota_eq_one_iff hNL (⟨δ * n * δ⁻¹ * n⁻¹, hcN⟩ : ↥N)).mpr hδn, one_mul]
  have hw0 : ρ g (Additive.ofMul (Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N))) =
      Additive.ofMul (Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N)) := by
    have h := sectionRep_chiefIota hHL hHN hNL hE hO e δH ⟨n, hn⟩ hδnN
    calc ρ g (Additive.ofMul (Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N)))
        = Additive.ofMul (Ch3z.chiefIota hNL (⟨δ * n * δ⁻¹, hδnN⟩ : ↥N)) := by
          simpa [g] using h
      _ = Additive.ofMul (Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N)) := by rw [hιeq]
  let w0 : Additive (Ch3z.chiefMod L N) :=
    Additive.ofMul (Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N))
  let w1 : Additive (Ch3z.chiefMod L N) := ρ v w0
  have hw1fix : ρ t w1 = w1 := by
    calc ρ t w1 = ρ (v * g * v⁻¹) (ρ v w0) := by rw [show t = v * g * v⁻¹ from rfl]
      _ = ρ v (ρ g (ρ v⁻¹ (ρ v w0))) := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ v (ρ g w0) := by
          have hvinv : ρ v⁻¹ (ρ v w0) = w0 := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]
          rw [hvinv]
      _ = ρ v w0 := by
          rw [show w0 = Additive.ofMul (Ch3z.chiefIota hNL
              (⟨n, hn⟩ : ↥N)) from rfl, hw0]
      _ = w1 := rfl
  let Hfix : Subgroup (suzukiGroup a K) :=
    { carrier := {h | ρ h w1 = w1}
      one_mem' := by
        change ρ 1 w1 = w1
        rw [map_one, Module.End.one_apply]
      mul_mem' := by
        intro a b ha hb
        change ρ (a * b) w1 = w1
        rw [map_mul]
        change (ρ a * ρ b) w1 = w1
        rw [Module.End.mul_apply, hb, ha]
      inv_mem' := by
        intro a ha
        change ρ a⁻¹ w1 = w1
        have h1 : ρ a (ρ a⁻¹ w1) = w1 := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
        have hinj : Function.Injective (ρ a) := by
          intro u v huv
          have h2 := congrArg (ρ a⁻¹) huv
          simpa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] using h2
        exact hinj (h1.trans ha.symm) }
  have htH : t ∈ Hfix := hw1fix
  have hle : Subgroup.zpowers t ≤ Hfix := Subgroup.zpowers_le.mpr htH
  have hmemfix : w1 ∈ fixedSub ρ (Subgroup.zpowers t) :=
    mem_fixedSub.mpr fun h hh => hle hh
  have hbot : fixedSub ρ (Subgroup.zpowers t) = ⊥ :=
    isSzNatural_mem_suzukiT_fixedSub_eq_bot hK ρ hρ' htT ht1
  rw [hbot] at hmemfix
  have hw1zero : w1 = 0 := by simpa using hmemfix
  have hw0zero : w0 = 0 := by
    have hcomp : ρ v⁻¹ w1 = w0 := by
      rw [show w1 = ρ v w0 from rfl, ← Module.End.mul_apply, ← map_mul,
        inv_mul_cancel, map_one, Module.End.one_apply]
    calc w0 = ρ v⁻¹ w1 := hcomp.symm
      _ = ρ v⁻¹ 0 := by rw [hw1zero]
      _ = 0 := map_zero _
  have hix : Ch3z.chiefIota hNL (⟨n, hn⟩ : ↥N) = 1 := by
    have h := congrArg Additive.toMul hw0zero
    simpa [w0] using h
  exact (Ch3z.chiefIota_eq_one_iff hNL (⟨n, hn⟩ : ↥N)).mp hix

end CFSG.Quasithin.Stroth.G5F

end
