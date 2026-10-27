module

public import CFSG.Monster.GMS.S4FamilyGroup
public import CFSG.Monster.GMS.S316
import CFSG.Monster.GMS.Griess13.ChecksUniqueness
import CFSG.Monster.GMS.Leech.TypeUnique
import CFSG.Sporadic.Co1.Module.Involutions
import CFSG.Sporadic.Co1.Module.TwoB
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3024
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate10073
public import Certificates.Certificate10074
public import Certificates.Certificate10075
public import Certificates.Certificate10077
public import Certificates.Certificate8955
public import Certificates.Certificate10070Base
public import Certificates.Certificate10073Base
public import Certificates.Certificate10074Base
import CFSG.Sporadic.Co1.Module.TwoBCertBase

public section

namespace CFSG.Monster.GMS.S4Family

open CFSG.Blueprint.NativeSporadic CFSG.Monster.GMS.S4Assembly

local notation "C[" x "]" => Subgroup.centralizer ({x} : Set _)

section Leech

variable {G G' : Type} [Group G] [Group G']

theorem mem_leechQ_iff {t q : G} (hq : q ∈ C[t]) :
    q ∈ leechQ t ↔ (⟨q, hq⟩ : ↥C[t]) ∈ CFSG.pCore 2 ↥C[t] := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro h
    exact ⟨⟨q, hq⟩, h, rfl⟩

theorem isIsoOn_mem_leechQ_iff {t q : G} {t' : G'} {f : G → G'} (hf : IsIsoOn f C[t] C[t'])
    (hq : q ∈ C[t]) : q ∈ leechQ t ↔ f q ∈ leechQ t' := by
  have hq' : f q ∈ C[t'] := hf.map_mem q hq
  rw [mem_leechQ_iff hq, mem_leechQ_iff hq']
  have hcore := CFSG.pCore_map_iso 2 (isoEquiv hf)
  have h1 : (isoEquiv hf ⟨q, hq⟩) = ⟨f q, hq'⟩ := rfl
  rw [← h1, ← hcore, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

end Leech

section TwoB

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {d₀ d₀' : B} {a z₀ : G}
  {a' z₀' : G'}

theorem isConj_apply_of_mem_leechQ
    (I : GMSInterfaces d₀ G) (I' : GMSInterfaces d₀' G')
    (hG : GMSF1Type d₀ a z₀) (hG' : GMSF1Type d₀' a' z₀') {t : G} {t' : G'} (ht : IsConj z₀ t)
    (ht' : IsConj z₀' t') {f : G → G'} (hf : IsIsoOn f C[t] C[t']) {q : G} (hq : q ∈ leechQ t)
    (hqA : IsConj a q) : IsConj a' (f q) := by
  have hft : f t = t' := apply_self_twoB hG' (orderOf_eq_two_of_isConj_z₀ hG ht) ht' hf
  have hqC : q ∈ C[t] := leechQ_le_centralizer t hq
  have hq2 : orderOf q = 2 := orderOf_eq_two_of_isConj_a hG hqA
  have hqne : q ≠ t := fun h => not_isConj_of_isConj hG hqA (h ▸ ht)
  have hfqQ : f q ∈ leechQ t' := (isIsoOn_mem_leechQ_iff hf hqC).mp hq
  have hfq2 : orderOf (f q) = 2 := (iso_orderOf hf hqC).trans hq2
  have hfqne : f q ≠ t' := fun h =>
    hqne (hf.injOn hqC (self_mem_centralizer t) (h.trans hft.symm))
  rcases orderOf_eq_two_mem_leechQ I'.sls I'.tableV I'.leech hG' ht' hfqQ hfq2 with h | h | h
  · exact absurd h hfqne
  · exact h
  · exfalso
    have h1 := card_centralizer_inf_of_mem_leechQ_four I'.sls I'.tableV I'.leech hG' ht' hfqQ
      hfqne h
    have h2 := card_centralizer_inf_of_mem_leechQ_two I.sls I.tableV I.leech hG ht hq hqA
    have h3 := isIsoOn_card_eq (isIsoOn_inf_centralizer hf hqC)
    rw [h1, h2] at h3
    norm_num [tableVOrderZ] at h3

variable (I : GMSInterfaces d₀ G) (I' : GMSInterfaces d₀' G') (hG : GMSF1Type d₀ a z₀)
  (hG' : GMSF1Type d₀' a' z₀')

include I I' hG hG' in
theorem exists_isIsoOn_of_twoB
    (hDC : Co1DoubleCoverTwoB) {t : G} {t' : G'} (ht : IsConj z₀ t)
    (ht' : IsConj z₀' t') : ∃ f : G → G', IsIsoOn f C[t] C[t'] := by
  obtain ⟨e⟩ := s31_seven I.sls I'.sls I.tableV I'.tableV I.leech I.leechInv co1ModuleUniqueness
    co1InvolutionFacts co1TwoBFacts (leechTypeUniqueness_of co1ModuleUniqueness hDC) hG hG'
  obtain ⟨c, hc⟩ := isConj_iff.mp ht
  obtain ⟨c', hc'⟩ := isConj_iff.mp ht'
  have h1 : IsIsoOn (fun x => c⁻¹ * x * c) C[t] C[z₀] := by
    have := isIsoOn_conj_inv_centralizer c t
    have e : c⁻¹ * t * c = z₀ := by rw [← hc]; group
    rwa [e] at this
  have h3 : IsIsoOn (fun y => c' * y * c'⁻¹) C[z₀'] C[t'] := by
    have := isIsoOn_conj_centralizer c' z₀'
    rwa [hc'] at this
  exact ⟨_, isIsoOn_comp (isIsoOn_comp h1 (isIsoOn_extendFun e)) h3⟩

include I I' hG hG' in
theorem exists_isIsoOn_apply_eq
    (hDC : Co1DoubleCoverTwoB) {t : G} {t' : G'} (ht : IsConj z₀ t)
    (ht' : IsConj z₀' t') {b : G} {b' : G'} (hbQ : b ∈ leechQ t) (hbA : IsConj a b)
    (hb'Q : b' ∈ leechQ t') (hb'A : IsConj a' b') :
    ∃ f : G → G', IsIsoOn f C[t] C[t'] ∧ f b = b' := by
  obtain ⟨f₀, hf₀⟩ := exists_isIsoOn_of_twoB I I' hG hG' hDC ht ht'
  have hbC : b ∈ C[t] := leechQ_le_centralizer t hbQ
  have h1 : f₀ b ∈ leechQ t' := (isIsoOn_mem_leechQ_iff hf₀ hbC).mp hbQ
  have h2 : IsConj a' (f₀ b) := isConj_apply_of_mem_leechQ I I' hG hG' ht ht' hf₀ hbQ hbA
  obtain ⟨c, hc, hcb⟩ := isConj_of_mem_leechQ_two I'.sls I'.tableV I'.leech hG' ht' h1 hb'Q h2
    hb'A
  exact ⟨fun x => c * f₀ x * c⁻¹, isIsoOn_comp hf₀ (isIsoOn_conj_self hc), hcb⟩

end TwoB

end CFSG.Monster.GMS.S4Family
