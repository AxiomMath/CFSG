module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymMatching
import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMatching
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymSwaps
import CFSG.LocalAnalysis.WeakClosure81.EightTailPThreeSymA
import CFSG.LocalAnalysis.SolvableSignalizer.CoprimeAction
import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm CFSG.Open CFSG.Timmesfeld.Bridge.Asc72

theorem le_iSup_inf_centralizer_of_index_two {Y : Type} [Group Y] [Finite Y] {O Q : Subgroup Y}
    [O.Normal] (hO : Odd (Nat.card O)) (hQ : IsElemAbelian 2 Q) (hQ1 : Q ≠ ⊥) :
    O ≤ ⨆ (B : Subgroup Y) (_ : B ≤ Q) (_ : (B.subgroupOf Q).index = 2),
      O ⊓ Subgroup.centralizer (B : Set Y) := by
  letI : CommGroup ↥Q :=
    { (inferInstance : Group ↥Q) with mul_comm := hQ.1.is_comm.comm }
  haveI : CFSG.IsElementaryAbelian 2 ↥Q :=
    { toIsMulCommutative := hQ.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hQ.2 (g : Y) g.2) }
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
  have hcop : ¬ 2 ∣ Nat.card ↥O := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hO
  let α : ↥Q →* MulAut ↥O := (MulAut.conjNormal (H := O)).comp Q.subtype
  have hgen := CFSG.SolvableSignalizer.iSup_fixedBySubgroup_index_eq_top 2 Nat.prime_two α hcop
  have hmap_top : (⊤ : Subgroup ↥O).map O.subtype = O := by
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro o ho
    exact ⟨⟨o, ho⟩, trivial, rfl⟩
  have hkey : ∀ (B : Subgroup ↥Q) (_ : B.index = 2),
      (CFSG.SolvableSignalizer.fixedBySubgroup α B).map O.subtype ≤
        ⨆ (B' : Subgroup Y) (_ : B' ≤ Q) (_ : (B'.subgroupOf Q).index = 2),
          O ⊓ Subgroup.centralizer (B' : Set Y) := by
    intro B hB
    refine le_iSup_of_le (B.map Q.subtype) ?_
    refine le_iSup_of_le (Subgroup.map_subtype_le B) ?_
    have hsub : (B.map Q.subtype).subgroupOf Q = B :=
      Subgroup.comap_map_eq_self_of_injective Q.subtype_injective B
    refine le_iSup_of_le ?_ ?_
    · rw [hsub]; exact hB
    · intro o ho
      rw [Subgroup.mem_inf]
      constructor
      · exact Subgroup.map_subtype_le (CFSG.SolvableSignalizer.fixedBySubgroup α B) ho
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ho
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hh
        have hfix : α q x = x :=
          (CFSG.SolvableSignalizer.mem_fixedBySubgroup α B x).1 hx q hq
        have hconj : (q : Y) * (x : Y) * (q : Y)⁻¹ = (x : Y) := by
          have := congrArg (fun z : ↥O => (z : Y)) hfix
          simpa [α, MulAut.conjNormal_apply] using this
        calc (q : Y) * (x : Y)
            = (q : Y) * (x : Y) * (q : Y)⁻¹ * (q : Y) := by group
          _ = (x : Y) * (q : Y) := by rw [hconj]
  have htop_le : (⊤ : Subgroup ↥O).map O.subtype ≤
      ⨆ (B' : Subgroup Y) (_ : B' ≤ Q) (_ : (B'.subgroupOf Q).index = 2),
        O ⊓ Subgroup.centralizer (B' : Set Y) := by
    rw [← hgen, Subgroup.map_iSup]
    refine iSup_le fun B => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hB => hkey B hB
  rwa [hmap_top] at htop_le

theorem isElemAbelian_closure_symT {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    IsElemAbelian 2 (Subgroup.closure (symT t (P : Subgroup Y))) := by
  have hmatch := symT_matching h
  have hcomm : IsMulCommutative ↥(Subgroup.closure (symT t (P : Subgroup Y))) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hmatch.2.1 x hx y hy
  refine ⟨hcomm, ?_⟩
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => x ^ 2 = 1) ?_ ?_ ?_ ?_ hx
  · intro z hz
    have hz' : z ∈ ({y : Y | IsConj t y} : Set Y) := hz.1
    simpa [pow_two] using h.oddClass.2.1.mul_self_eq_one hz'
  · exact one_pow 2
  · intro a b ha hb iha ihb
    have hc : Commute a b :=
      (commute_iff_eq a b).mpr (congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    rw [hc.mul_pow, iha, ihb, one_mul]
  · intro a _ iha
    rw [inv_pow, iha, inv_one]

theorem closure_symT_ne_bot {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    Subgroup.closure (symT t (P : Subgroup Y)) ≠ ⊥ := by
  intro hbot
  have ht : t ∈ Subgroup.closure (symT t (P : Subgroup Y)) :=
    Subgroup.subset_closure ⟨IsConj.refl t, h.mem⟩
  rw [hbot, Subgroup.mem_bot] at ht
  exact h.oddClass.2.1.ne_one (IsConj.refl t) ht

theorem exists_ne_mem_symT {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P) :
    ∃ s ∈ symT t (P : Subgroup Y), s ≠ t := by
  have hmatch := symT_matching h
  have hsurj : Function.Surjective (symPi e) := w85g_symPi_surjective e
  let P' : Sylow 2 (Perm (Fin m)) := P.mapSurjective (f := symPi e) hsurj
  have hP'coe : (P' : Subgroup (Perm (Fin m))) = (P : Subgroup Y).map (symPi e) :=
    Sylow.coe_mapSurjective (f := symPi e) hsurj P
  have hPsyl : CFSG.Quasithin.IsSylowIn 2 (P' : Subgroup (Perm (Fin m))) ⊤ :=
    CFSG.Quasithin.isSylowIn_of_card_eq le_top (by
      rw [Subgroup.card_top]
      exact Sylow.card_eq_multiplicity P')
  obtain ⟨σ, hσ, hTσ, hfix⟩ := ThreeOne.exists_matching hPsyl
  obtain ⟨a, b, hab, htab⟩ := h.swap
  have htP' : symPi e t ∈ (P' : Subgroup (Perm (Fin m))) := by
    rw [hP'coe]
    exact Subgroup.mem_map_of_mem (symPi e) h.mem
  have habP' : swap a b ∈ (P' : Subgroup (Perm (Fin m))) := by
    rw [← htab]
    exact htP'
  have hσa : σ a = b := (hTσ a b hab).mp habP'
  have hm5 : 5 ≤ m := le_trans (by norm_num : 5 ≤ 6) h.six_le
  obtain ⟨c, d, hσc, hca, hcb, hda, hdb, hcd⟩ :=
    exists_second_two_cycle hm5 hσ hfix hab hσa
  have hcdP' : swap c d ∈ (P' : Subgroup (Perm (Fin m))) := (hTσ c d hcd).mpr hσc
  have hmemmap : swap c d ∈ (P : Subgroup Y).map (symPi e) := by
    rw [← hP'coe]
    exact hcdP'
  obtain ⟨s, hs, hπs⟩ := hmatch.2.2.2 c d hcd hmemmap
  have hneq : swap c d ≠ swap a b := by
    intro heq
    have h1 : (swap c d) c = (swap a b) c := by rw [heq]
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hca hcb] at h1
    exact hcd h1.symm
  refine ⟨s, hs, ?_⟩
  intro hst
  exact hneq (by rw [← hπs, hst, htab])

theorem fusionOddCore_inf_centralizer_le_centralizer {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    {e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)} {t : Y} {P : Sylow 2 Y} (h : SymSetting e t P)
    {B : Subgroup Y} (hBQ : B ≤ Subgroup.closure (symT t (P : Subgroup Y)))
    (hB : (B.subgroupOf (Subgroup.closure (symT t (P : Subgroup Y)))).index = 2)
    (hno : ∀ s ∈ symT t (P : Subgroup Y), s ∉ B) :
    fusionOddCore Y ⊓ Subgroup.centralizer (B : Set Y) ≤
      Subgroup.centralizer ({t} : Set Y) := by
  intro q hq
  obtain ⟨hqO, hqBmem⟩ := Subgroup.mem_inf.mp hq
  obtain ⟨s, hs, hst⟩ := exists_ne_mem_symT h
  have hmatch := symT_matching h
  have hsD : IsConj t s := hs.1
  have htT : t ∈ symT t (P : Subgroup Y) := ⟨IsConj.refl t, h.mem⟩
  have htD : IsConj t t := IsConj.refl t
  have hQcomm : ∀ x ∈ Subgroup.closure (symT t (P : Subgroup Y)),
      ∀ y ∈ Subgroup.closure (symT t (P : Subgroup Y)), x * y = y * x :=
    fun x hx y hy =>
      congrArg Subtype.val ((isElemAbelian_closure_symT h).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have htQ : t ∈ Subgroup.closure (symT t (P : Subgroup Y)) :=
    Subgroup.subset_closure htT
  have hsQ : s ∈ Subgroup.closure (symT t (P : Subgroup Y)) :=
    Subgroup.subset_closure hs
  have hst_comm : Commute s t := hmatch.2.1 s hs t htT
  have htB : t ∉ B := hno t htT
  have hsB : s ∉ B := hno s hs
  have hqB : ∀ b ∈ B, b * q = q * b := fun b hb =>
    Subgroup.mem_centralizer_iff.mp hqBmem b hb
  have htsB : t * s ∈ B := by
    have hmem : (⟨t, htQ⟩ : ↥(Subgroup.closure (symT t (P : Subgroup Y)))) * ⟨s, hsQ⟩ ∈
        B.subgroupOf (Subgroup.closure (symT t (P : Subgroup Y))) := by
      rw [Subgroup.mul_mem_iff_of_index_two hB]
      exact ⟨fun h => absurd (Subgroup.mem_subgroupOf.mp h) htB,
             fun h => absurd (Subgroup.mem_subgroupOf.mp h) hsB⟩
    simpa using Subgroup.mem_subgroupOf.mp hmem
  let w : Y := s⁻¹ * q⁻¹ * s * q
  have hqs_eq : q⁻¹ * s * q = s * w := by
    show q⁻¹ * s * q = s * (s⁻¹ * q⁻¹ * s * q)
    group
  have hwO : w ∈ fusionOddCore Y := by
    have h1 : s⁻¹ * q⁻¹ * s ∈ fusionOddCore Y := by
      have h2 := (inferInstance : (fusionOddCore Y).Normal).conj_mem q⁻¹
        ((fusionOddCore Y).inv_mem hqO) s⁻¹
      simpa using h2
    show s⁻¹ * q⁻¹ * s * q ∈ fusionOddCore Y
    exact (fusionOddCore Y).mul_mem h1 hqO
  have hwC : w ∈ Subgroup.centralizer (B : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbQ : b ∈ Subgroup.closure (symT t (P : Subgroup Y)) := hBQ hb
    have hbs : Commute b s := hQcomm b hbQ s hsQ
    have hbq : Commute b q := hqB b hb
    have hbw : Commute b w := by
      show Commute b (s⁻¹ * q⁻¹ * s * q)
      exact (((hbs.inv_right.mul_right hbq.inv_right).mul_right hbs).mul_right hbq)
    exact hbw.eq
  have hker : (symPi e).ker = fusionOddCore Y := by
    rw [symPi]
    ext z
    simp [MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hq_ker : symPi e q = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact hqO
  have hqinv_ker : symPi e q⁻¹ = 1 := by rw [map_inv, hq_ker, inv_one]
  have h_img : symPi e (t * (q⁻¹ * s * q)) = symPi e t * symPi e s := by
    rw [map_mul, map_mul, map_mul, hqinv_ker, hq_ker, one_mul, mul_one]
  have ht_inv : symPi e t * symPi e t = 1 := by rw [← map_mul, h.mul_self, map_one]
  have hs_swap : (symPi e s).IsSwap := hmatch.2.2.1 s hs
  have hs_inv : symPi e s * symPi e s = 1 := by
    obtain ⟨c', d', _, hsc'd'⟩ := hs_swap
    rw [hsc'd', Equiv.swap_mul_self]
  have hzt : Commute (symPi e t) (symPi e s) := by
    rw [commute_iff_eq]
    calc symPi e t * symPi e s = symPi e (t * s) := (map_mul (symPi e) t s).symm
      _ = symPi e (s * t) := by rw [hst_comm.eq]
      _ = symPi e s * symPi e t := map_mul (symPi e) s t
  have hz2 : (symPi e t * symPi e s) ^ 2 = 1 :=
    (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one ht_inv hs_inv).mp hzt
  have hz1 : symPi e t * symPi e s ≠ 1 := by
    intro hz
    have heq : symPi e t = symPi e s := by
      calc symPi e t = symPi e t * 1 := (mul_one _).symm
        _ = symPi e t * (symPi e s * symPi e s) := by rw [hs_inv]
        _ = (symPi e t * symPi e s) * symPi e s := by group
        _ = 1 * symPi e s := by rw [hz]
        _ = symPi e s := one_mul _
    exact hst ((hmatch.1 hs htT) heq.symm)
  have hzord : orderOf (symPi e t * symPi e s) = 2 := orderOf_eq_prime hz2 hz1
  have h2dvd : 2 ∣ orderOf (t * (q⁻¹ * s * q)) := by
    have h1 := orderOf_map_dvd (symPi e) (t * (q⁻¹ * s * q))
    rw [h_img, hzord] at h1
    exact h1
  have hqsqD : IsConj t (q⁻¹ * s * q) := by
    obtain ⟨u, hu⟩ := isConj_iff.mp hsD
    refine isConj_iff.mpr ⟨q⁻¹ * u, ?_⟩
    calc (q⁻¹ * u) * t * (q⁻¹ * u)⁻¹ = q⁻¹ * (u * t * u⁻¹) * q := by group
      _ = q⁻¹ * s * q := by rw [hu]
  have htsq_sq : (t * (q⁻¹ * s * q)) ^ 2 = 1 := by
    rcases h.oddClass.2.1.2 t htD (q⁻¹ * s * q) hqsqD with hdvd | hodd
    · exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    · exact absurd h2dvd hodd.not_two_dvd_nat
  have htsw_sq : (t * s * w) ^ 2 = 1 := by
    have h1 : t * (q⁻¹ * s * q) = t * s * w := by rw [hqs_eq]; group
    rwa [h1] at htsq_sq
  have hts_comm_w : Commute (t * s) w :=
    Subgroup.mem_centralizer_iff.mp hwC (t * s) htsB
  have hts_sq : (t * s) ^ 2 = 1 := by
    have ht2 : t * t = 1 := h.mul_self
    have hs2 : s * s = 1 := h.oddClass.2.1.mul_self_eq_one hs.1
    exact (CFSG.Timmesfeld.commute_iff_mul_sq_eq_one ht2 hs2).mp hst_comm.symm
  have hw2 : w ^ 2 = 1 := by
    have h1 : (t * s * w) ^ 2 = (t * s) ^ 2 * w ^ 2 := hts_comm_w.mul_pow 2
    rw [hts_sq, one_mul] at h1
    rw [← h1, htsw_sq]
  have hw1 : w = 1 := by
    have hodd : Odd (orderOf w) :=
      Odd.of_dvd_nat (CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore Y)
        (Subgroup.orderOf_dvd_natCard (fusionOddCore Y) hwO)
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf w) hdvd with h1 | h2
    · exact orderOf_eq_one_iff.mp h1
    · exfalso
      apply hodd.not_two_dvd_nat
      rw [h2]
  have hqs_eq_w1 : q⁻¹ * s * q = s := by rw [hqs_eq, hw1, mul_one]
  have hqs_comm : Commute q s := by
    rw [commute_iff_eq]
    have h2 : q * (q⁻¹ * s * q) = q * s := by rw [hqs_eq_w1]
    rw [← h2]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  have htsq : (t * s) * q = q * (t * s) := hqB (t * s) htsB
  have hsinv_q : s⁻¹ * q = q * s⁻¹ := by
    have h := hqs_comm.eq
    calc s⁻¹ * q = s⁻¹ * (q * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * q) * s⁻¹ := by rw [h]
      _ = q * s⁻¹ := by group
  calc t * q = ((t * s) * s⁻¹) * q := by group
    _ = (t * s) * (s⁻¹ * q) := by group
    _ = (t * s) * (q * s⁻¹) := by rw [hsinv_q]
    _ = ((t * s) * q) * s⁻¹ := by group
    _ = (q * (t * s)) * s⁻¹ := by rw [htsq]
    _ = q * ((t * s) * s⁻¹) := by group
    _ = q * t := by group

end CFSG.LocalAnalysis.WeakClosure81

end
