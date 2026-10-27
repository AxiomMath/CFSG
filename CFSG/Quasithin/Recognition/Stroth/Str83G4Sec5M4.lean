module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4S1Torus
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtN204Elem

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender
open CFSG.LieType.BorelTits CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G]

theorem sup_pCoreOf_eq_of_normal_of_isSimple {H N : Subgroup G}
    (hsim : IsSimpleGroup (oTwoQuot ↥H)) (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) (hNQ : ¬ N ≤ pCoreOf 2 H) :
    N ⊔ pCoreOf 2 H = H := by
  classical
  let q : ↥H →* oTwoQuot ↥H := QuotientGroup.mk' (pCore 2 ↥H)
  have hker : q.ker = (pCoreOf 2 H).subgroupOf H := by
    rw [QuotientGroup.ker_mk', ← CFSG.openPCoreOf_subgroupOf 2 H]
  have hNsub : (N.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN
  let Nbar : Subgroup (oTwoQuot ↥H) := (N.subgroupOf H).map q
  have hNbarNorm : Nbar.Normal := hNsub.map q (QuotientGroup.mk'_surjective _)
  have hNbarNe : Nbar ≠ ⊥ := by
    intro hbot
    apply hNQ
    intro c hc
    have hcNsub : (⟨c, hNH hc⟩ : ↥H) ∈ N.subgroupOf H := hc
    have hq1 : q ⟨c, hNH hc⟩ = 1 := by
      have hmem : q ⟨c, hNH hc⟩ ∈ Nbar := Subgroup.mem_map_of_mem q hcNsub
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hmemker : (⟨c, hNH hc⟩ : ↥H) ∈ q.ker := hq1
    rw [hker] at hmemker
    exact Subgroup.mem_subgroupOf.mp hmemker
  have hNbarTop : Nbar = ⊤ :=
    (hsim.eq_bot_or_eq_top_of_normal Nbar).resolve_left hNbarNe
  refine le_antisymm (sup_le hNH (pCoreOf_le 2 H)) fun h hh => ?_
  let hH : ↥H := ⟨h, hh⟩
  have hqmem : q hH ∈ Nbar := by rw [hNbarTop]; exact Subgroup.mem_top _
  obtain ⟨n, hnN, hnq⟩ := Subgroup.mem_map.mp hqmem
  have hq1 : q (hH * n⁻¹) = 1 := by rw [map_mul, map_inv, hnq, mul_inv_cancel]
  have hmemker : (hH * n⁻¹ : ↥H) ∈ q.ker := hq1
  rw [hker] at hmemker
  have hmemQ : h * (n : G)⁻¹ ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hmemker
  have heq : h = (h * (n : G)⁻¹) * (n : G) := by group
  rw [heq]
  exact (N ⊔ pCoreOf 2 H).mul_mem (Subgroup.mem_sup_right hmemQ)
    (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hnN))

variable {L1 L2 S : Subgroup G} {a : ℕ}

theorem str83G4_isSimpleGroup_left (hfr : Str83G4Frame L1 L2 S a) :
    IsSimpleGroup (oTwoQuot ↥(L1 ⊔ S)) := by
  obtain ⟨hF, hB, ha, hSz, -, -⟩ := hfr
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hB (Or.inl ⟨a, ha, hSz⟩)
  have hsimpleSz : IsSimpleGroup ↥(Sz a) :=
    @MulEquiv.isSimpleGroup _ _ _ _ ((isQuasisimple_sz a ha).2.1)
      (((QuotientGroup.quotientMulEquivOfEq (center_sz a ha)).trans
        QuotientGroup.quotientBot).symm)
  rw [sup_eq_of_S_eq hS1]
  exact @MulEquiv.isSimpleGroup _ _ _ _ hsimpleSz
    ((oTwoQuotSupEquiv hF.1).trans (Classical.choice hSz))

theorem str83G4_isSimpleGroup_right
    (hfr : Str83G4Frame L1 L2 S a) : IsSimpleGroup (oTwoQuot ↥(L2 ⊔ S)) := by
  obtain ⟨hF, hB, ha, -, hL2, -⟩ := hfr
  exact isSimpleGroup_oTwoQuot_sup_right_of_isL2Quot hF.1
    (eq_sup_pCoreOf_of_bender_right hF.1 hB (Or.inr (Or.inr ⟨2 * a + 1, by omega, hL2⟩)))
    (by omega) hL2

theorem str83G4_mem_of_normal_left (hfr : Str83G4Frame L1 L2 S a)
    {N : Subgroup G} (hNH : N ≤ L1 ⊔ S) (hN : L1 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNQ : ¬ N ≤ Q1 L1 L2 S) {g : G} (hg : g ∈ L1 ⊔ S) (hodd : Odd (orderOf g)) : g ∈ N := by
  have hcore := str83G4_pCoreOf_sup_left hfr
  have hsup : N ⊔ Q1 L1 L2 S = L1 ⊔ S := by
    rw [← hcore]
    exact sup_pCoreOf_eq_of_normal_of_isSimple (str83G4_isSimpleGroup_left hfr) hNH hN
      (by rwa [hcore])
  have hQN : Q1 L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    ((le_sup_right : Q1 L1 L2 S ≤ N ⊔ Q1 L1 L2 S).trans hsup.le).trans hN
  exact N204.mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hQN (hsup.symm ▸ hg) hodd

theorem str83G4_mem_of_normal_right (hfr : Str83G4Frame L1 L2 S a)
    {N : Subgroup G} (hNH : N ≤ L2 ⊔ S) (hN : L2 ⊔ S ≤ Subgroup.normalizer (N : Set G))
    (hNQ : ¬ N ≤ Q2 L1 L2 S) {g : G} (hg : g ∈ L2 ⊔ S) (hodd : Odd (orderOf g)) : g ∈ N := by
  have hcore := str83G4_pCoreOf_sup_right hfr
  have hsup : N ⊔ Q2 L1 L2 S = L2 ⊔ S := by
    rw [← hcore]
    exact sup_pCoreOf_eq_of_normal_of_isSimple (str83G4_isSimpleGroup_right hfr) hNH hN
      (by rwa [hcore])
  have hQN : Q2 L1 L2 S ≤ Subgroup.normalizer (N : Set G) :=
    ((le_sup_right : Q2 L1 L2 S ≤ N ⊔ Q2 L1 L2 S).trans hsup.le).trans hN
  exact N204.mem_of_odd_of_mem_sup (pCoreOf_isPGroup 2 (P2 L1 L2 S)) hQN (hsup.symm ▸ hg) hodd

theorem str83G4Data_D1_ne_bot (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) : d.D1 ≠ ⊥ := by
  obtain ⟨hF, -, ha, ⟨eSz⟩, -, -⟩ := hfr
  have hBT : BenderType (oTwoQuot ↥L1) (2 * a + 1) 2 1 :=
    BenderType.suzuki a ha (eSz.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm))
  have hcard : Nat.card d.D1 = 2 ^ (2 * a + 1) - 1 :=
    (card_isCyclic_of_hallTwoPrime hF.1.h1.sylow d.hD1hall d.hD1sup hBT).1
  intro hbot
  rw [hbot, Subgroup.card_bot] at hcard
  have h8 : 8 ≤ 2 ^ (2 * a + 1) :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem str83G4Data_odd_card_sup (d : Str83G4Data L1 L2 S) : Odd (Nat.card ↥(d.D1 ⊔ d.D2)) := by
  classical
  by_contra hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(d.D1 ⊔ d.D2)) 2
    (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
  have hD2C : d.D2 ≤ Subgroup.centralizer (d.D1 : Set G) := fun y hy =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => d.hcomm z hz y hy
  have hD2N := hD2C.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨u, hu, v, hv, huv⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hD2N).mp x.2
  have hcomm : Commute u v := d.hcomm u hu v hv
  have hu' : Odd (orderOf u) :=
    Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 hu)
  have hv' : Odd (orderOf v) :=
    Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hv)
  have h2 : 2 ∣ orderOf u * orderOf v := by
    have h := hcomm.orderOf_mul_dvd_mul_orderOf
    rw [← huv, Subgroup.orderOf_coe, hx] at h
    exact h
  exact (hu'.mul hv').not_two_dvd_nat h2

theorem str83G4_oTwoUpper_sup_left (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) : oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S = L1 ⊔ S := by
  have hcore := str83G4_pCoreOf_sup_left hfr
  rw [← hcore]
  refine sup_pCoreOf_eq_of_normal_of_isSimple (str83G4_isSimpleGroup_left hfr)
    (oTwoUpper_le _) (CFSG.Quasithin.le_normalizer_oTwoUpper _) ?_
  rw [hcore]
  intro hle
  obtain ⟨x, hx, hx1⟩ :=
    (Subgroup.bot_or_exists_ne_one d.D1).resolve_left (str83G4Data_D1_ne_bot hfr d)
  have hxL : x ∈ L1 ⊔ S := Subgroup.mem_sup_left ((F1.borelOf_le L1 S) (d.hD1hall.1 hx))
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat d.hD1hall.2.1 (Subgroup.orderOf_dvd_natCard d.D1 hx)
  have hbot : d.D1 ⊓ Q1 L1 L2 S = ⊥ := by
    rw [inf_comm]
    exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P1 L1 L2 S)) d.hD1hall.2.1
  have hmem : x ∈ d.D1 ⊓ Q1 L1 L2 S :=
    Subgroup.mem_inf.mpr ⟨hx, hle (mem_oTwoUpper_of_odd hxL hodd)⟩
  rw [hbot] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

theorem str83G4_oTwoUpper_sup_right (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) : oTwoUpper (L2 ⊔ S) ⊔ Q2 L1 L2 S = L2 ⊔ S := by
  have hcore := str83G4_pCoreOf_sup_right hfr
  rw [← hcore]
  refine sup_pCoreOf_eq_of_normal_of_isSimple (str83G4_isSimpleGroup_right hfr)
    (oTwoUpper_le _) (CFSG.Quasithin.le_normalizer_oTwoUpper _) ?_
  rw [hcore]
  intro hle
  obtain ⟨x, hx, hx1⟩ :=
    (Subgroup.bot_or_exists_ne_one d.D2).resolve_left (str83G4Data_D2_ne_bot hfr d)
  have hxL : x ∈ L2 ⊔ S := Subgroup.mem_sup_left ((F1.borelOf_le L2 S) (d.hD2hall.1 hx))
  have hodd : Odd (orderOf x) :=
    Odd.of_dvd_nat d.hD2hall.2.1 (Subgroup.orderOf_dvd_natCard d.D2 hx)
  have hbot : d.D2 ⊓ Q2 L1 L2 S = ⊥ := by
    rw [inf_comm]
    exact RonanF13.inf_eq_bot_of_odd (pCoreOf_isPGroup 2 (P2 L1 L2 S)) d.hD2hall.2.1
  have hmem : x ∈ d.D2 ⊓ Q2 L1 L2 S :=
    Subgroup.mem_inf.mpr ⟨hx, hle (mem_oTwoUpper_of_odd hxL hodd)⟩
  rw [hbot] at hmem
  exact hx1 (Subgroup.mem_bot.mp hmem)

theorem str83G4_eq_one_of_commute_odd
    (hfr : Str83G4Frame L1 L2 S a) (d : Str83G4Data L1 L2 S) {f : G} (hfS : f ∈ S)
    (h1 : ∀ g ∈ L1 ⊔ S, Odd (orderOf g) → f * g = g * f)
    (h2 : ∀ g ∈ L2 ⊔ S, Odd (orderOf g) → f * g = g * f) : f = 1 := by
  have hF := hfr.1
  have hcent : ∀ {X : Subgroup G}, (∀ g ∈ X, Odd (orderOf g) → f * g = g * f) →
      f ∈ Subgroup.centralizer (oTwoUpper X : Set G) := by
    intro X hX
    have hle : oTwoUpper X ≤ Subgroup.centralizer ({f} : Set G) :=
      (Subgroup.closure_le _).mpr fun g hg =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hX g hg.1 hg.2).symm
    exact Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  let F : Subgroup G := S ⊓ Subgroup.centralizer (oTwoUpper (L1 ⊔ S) : Set G) ⊓
    Subgroup.centralizer (oTwoUpper (L2 ⊔ S) : Set G)
  have hfF : f ∈ F := Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hfS, hcent h1⟩, hcent h2⟩
  have hFS : F ≤ S := inf_le_left.trans inf_le_left
  have hSNF : S ≤ Subgroup.normalizer (F : Set G) := by
    intro s hs
    have hO : ∀ {X : Subgroup G}, S ≤ X →
        s ∈ Subgroup.normalizer (Subgroup.centralizer (oTwoUpper X : Set G) : Set G) :=
      fun hSX => F7.normalizer_le_normalizer_centralizer _
        (CFSG.Quasithin.le_normalizer_oTwoUpper _ (hSX hs))
    exact A4.mem_normalizer_inf (A4.mem_normalizer_inf (Subgroup.le_normalizer hs)
      (hO le_sup_right)) (hO le_sup_right)
  have hONF : ∀ {X : Subgroup G}, F ≤ Subgroup.centralizer (oTwoUpper X : Set G) →
      oTwoUpper X ≤ Subgroup.normalizer (F : Set G) := fun hFX =>
    (Subgroup.le_centralizer_iff.mp hFX).trans (Subgroup.centralizer_le_normalizer _)
  have hL1 : L1 ⊔ S ≤ Subgroup.normalizer (F : Set G) :=
    (str83G4_oTwoUpper_sup_left hfr d).symm.le.trans
      (sup_le (hONF (inf_le_left.trans inf_le_right)) ((str83G4_q1_le_s hfr).trans hSNF))
  have hL2 : L2 ⊔ S ≤ Subgroup.normalizer (F : Set G) :=
    (str83G4_oTwoUpper_sup_right hfr d).symm.le.trans
      (sup_le (hONF inf_le_right) ((str83G4_q2_le_s hfr).trans hSNF))
  have hG0 : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (F : Set G) :=
    sup_le (sup_le ((le_sup_left : L1 ≤ L1 ⊔ S).trans hL1)
      ((le_sup_left : L2 ≤ L2 ⊔ S).trans hL2)) hSNF
  have hpc : F ≤ pCoreOf 2 (L1 ⊔ L2 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (hFS.trans (le_sup_right : S ≤ L1 ⊔ L2 ⊔ S)) hG0 (hF.1.h1.pgroup.to_le hFS)
  rw [hF.1.o2] at hpc
  exact Subgroup.mem_bot.mp (hpc hfF)

end CFSG.Quasithin.Stroth

end
