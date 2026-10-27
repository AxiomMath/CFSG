module

public import CFSG.OddTranspositions.PartThree.Nine.FinalLocal
public import CFSG.OddTranspositions.PartThree.Nine.SevenCore
public import CFSG.Timmesfeld.Bridge.OddLocalQd

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_mem_pResidualOf_of_mem {hC : HypothesisC D} (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {d : G} (hd : d ∈ D) :
    d ∉ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  intro hdL
  have hLH : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) ≤ Halpha D hC.alpha :=
    Subgroup.map_subtype_le _
  have hdu : Commute d hC.d :=
    (Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC (hLH hdL)))
  have huL : hC.d ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
    by_cases hdu' : d = hC.d
    · rw [← hdu']
      exact hdL
    · have hmem : d ∈ commSet D hC.d := ⟨hd, hdu, hdu'⟩
      have h := ((mem_commSet_iff hC hH h3).mp hmem).1
      have : hC.d = hC.d * d * d⁻¹ := by group
      rw [this]
      exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hdL)
  have h := Subgroup.disjoint_def.mp h3.2.2.2 (Subgroup.mem_zpowers hC.d) huL
  exact hC.setup.oddT.ne_one hC.hd h

theorem mul_not_mem_of_commute {hC : HypothesisC D} (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    {d e : G} (hd : d ∈ D) (he : e ∈ D) (hde : d ≠ e) (hc : Commute d e) : d * e ∉ D := by
  intro hdeD
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hd hC.hd)
  have heu : g * e * g⁻¹ ∈ commSet D hC.d := by
    refine ⟨hC.setup.conj_mem g he, ?_, ?_⟩
    · rw [← hg]
      exact ((Commute.conj_iff g).mpr hc).symm
    · intro h
      apply hde
      have h' : g * e * g⁻¹ = g * d * g⁻¹ := by rw [h, hg]
      have := congrArg (fun x => g⁻¹ * x * g) h'
      simpa [mul_assoc] using this.symm
  have hL := ((mem_commSet_iff hC hH h3).mp heu).1
  have hconj : hC.d * (g * e * g⁻¹) = g * (d * e) * g⁻¹ := by rw [← hg]; group
  rw [hconj] at hL
  exact not_mem_pResidualOf_of_mem hH h3 (hC.setup.conj_mem g hdeD) hL

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem mem_normalizer_omega_of_commute (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {s : G} (hs : s ∈ U) (hs1 : s ≠ 1)
    {t : G} (htL : t ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hts : Commute t s) :
    t ∈ Subgroup.normalizer (U : Set G) := by
  classical
  set L := CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) with hLdef
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  have hLB : IsBenderGroup L := isBenderGroup_of_mulEquiv eL hH.bender
  obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
  have hSE := IsBenderGroup.isStronglyEmbeddedOrder_normalizer hLB R
  set s' : L := ⟨s, hU.le_pResidualOf hs⟩ with hs'
  set t' : L := ⟨t, htL⟩ with ht'
  have hs'R : s' ∈ (R : Subgroup L) := by
    have hsm : s ∈ (R : Subgroup L).map L.subtype := by
      rw [hR]
      exact ⟨hU.le_sylow_map hs, hU.le_pResidualOf hs⟩
    obtain ⟨x, hx, hxs⟩ := Subgroup.mem_map.mp hsm
    have : x = s' := Subtype.ext hxs
    rwa [← this]
  have hs'2 : orderOf s' = 2 := by
    rw [← Subgroup.orderOf_coe]
    have := hU.isElementaryAbelian
    exact orderOf_eq_prime (CFSG.elemPow_eq_one_of_isElementaryAbelian s hs) (fun h => hs1 h)
  have ht'N : t' ∈ Subgroup.normalizer ((R : Subgroup L) : Set L) := by
    by_contra hnot
    have hodd := hSE.2.2 t' hnot
    have hmem : s' ∈ Subgroup.normalizer ((R : Subgroup L) : Set L) ⊓
        (Subgroup.normalizer ((R : Subgroup L) : Set L)).map (MulAut.conj t').toMonoidHom := by
      refine ⟨Subgroup.le_normalizer hs'R, ?_⟩
      refine ⟨s', Subgroup.le_normalizer hs'R, ?_⟩
      apply Subtype.ext
      change t * s * t⁻¹ = s
      rw [hts.eq, mul_inv_cancel_right]
    have hdvd := orderOf_dvd_natCard (⟨s', hmem⟩ : (Subgroup.normalizer
      ((R : Subgroup L) : Set L) ⊓ (Subgroup.normalizer ((R : Subgroup L) : Set L)).map
        (MulAut.conj t').toMonoidHom : Subgroup L))
    rw [Subgroup.orderOf_mk, hs'2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hTL : ∀ x, x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ L →
      t * x * t⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ L := by
    intro x hx
    rw [← hR] at hx ⊢
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨t' * x' * t'⁻¹, (ht'N x').mp hx', rfl⟩
  have hTL' : ∀ x, x ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ L →
      t⁻¹ * x * t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓ L := by
    intro x hx
    rw [← hR] at hx ⊢
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨t'⁻¹ * x' * t'⁻¹⁻¹, (Subgroup.inv_mem _ ht'N x').mp hx', ?_⟩
    rw [inv_inv]
    rfl
  rw [hU.eq_closure]
  refine OddLocal.mem_normalizer_closure ?_ ?_
  · rintro x ⟨hx, hx2⟩
    refine ⟨hTL x hx, ?_⟩
    rw [← hx2]
    exact (SemiconjBy.orderOf_eq t (show t * x = t * x * t⁻¹ * t by group)).symm
  · rintro x ⟨hx, hx2⟩
    refine ⟨hTL' x hx, ?_⟩
    rw [← hx2]
    exact (SemiconjBy.orderOf_eq t⁻¹ (show t⁻¹ * x = t⁻¹ * x * t * t⁻¹ by group)).symm

theorem mem_delta_of_commute (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {s : G} (hs : s ∈ U) (hs1 : s ≠ 1)
    {d : G} (hd : d ∈ D) (hds : Commute d s) : d ∈ (fun v : G => hC.d * v) '' (U : Set G) := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have husD : hC.d * s ∈ D := by
    have h : hC.d * s ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨s, hs, rfl⟩
    exact h.2
  have hne : hC.d ≠ hC.d * s := fun h => hs1 (by simpa using h.symm)
  have hsL : s ∈ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := hU.le_pResidualOf hs
  have hus : Commute hC.d s :=
    (Subgroup.mem_centralizer_singleton_iff.mp
      (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ hsL))).symm
  have hcomm : Commute hC.d (hC.d * s) := (Commute.refl _).mul_right hus
  have hsplit : hC.d * (hC.d * s) = s := by rw [← mul_assoc, hu2, one_mul]
  obtain ⟨hdu, -⟩ := (hC.setup.oddT.commute_mul_iff hC.hd husD hd hne hcomm).mp
    (by rw [hsplit]; exact hds)
  by_cases hdu' : d = hC.d
  · exact ⟨1, U.one_mem, by simp only [mul_one, hdu']⟩
  · have hmem : d ∈ commSet D hC.d := ⟨hd, hdu, hdu'⟩
    obtain ⟨htL, ht2⟩ := (mem_commSet_iff hC hH h3).mp hmem
    have hts : Commute (hC.d * d) s := hus.mul_left hds
    have htN := hU.mem_normalizer_omega_of_commute hH h3 h5 hs hs1 htL hts
    have htt : hC.d * d * (hC.d * d) = 1 := by
      rw [← pow_two, ← ht2, pow_orderOf_eq_one]
    have htU := hU.mem_of_involution_normalizer_pResidualOf hH h3 h5 htL htN htt
    exact ⟨hC.d * d, htU, by simp only [← mul_assoc, hu2, one_mul]⟩

theorem mem_delta_iff_commute (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {s : G} (hs : s ∈ U) (hs1 : s ≠ 1)
    (x : G) : x ∈ (fun v : G => hC.d * v) '' (U : Set G) ↔ x ∈ D ∧ Commute x s := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hxD : hC.d * v ∈ (S : Set G) ∩ D := hU.sylow_inter ▸ ⟨v, hv, rfl⟩
    refine ⟨hxD.2, ?_⟩
    have := hU.isElementaryAbelian
    have hvs : Commute v s := by
      have h := (IsMulCommutative.is_comm (M := U)).comm ⟨v, hv⟩ ⟨s, hs⟩
      exact congrArg Subtype.val h
    have hus : Commute hC.d s :=
      (Subgroup.mem_centralizer_singleton_iff.mp
        (PartThree.Halpha_le_centralizer_d hC
          (Subgroup.map_subtype_le _ (hU.le_pResidualOf hs)))).symm
    exact hus.mul_left hvs
  · rintro ⟨hxD, hxs⟩
    exact hU.mem_delta_of_commute hH h3 h5 hs hs1 hxD hxs

theorem centralizer_le_normalizer_delta (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {s : G} (hs : s ∈ U) (hs1 : s ≠ 1) :
    Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) := by
  intro g hg x
  have hgs : g * s * g⁻¹ = s := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp hg), mul_inv_cancel_right]
  rw [hU.mem_delta_iff_commute hH h3 h5 hs hs1, hU.mem_delta_iff_commute hH h3 h5 hs hs1]
  constructor
  · rintro ⟨hxD, hxs⟩
    refine ⟨hC.setup.conj_mem g hxD, ?_⟩
    have h := (Commute.conj_iff g).mpr hxs
    rwa [hgs] at h
  · rintro ⟨hxD, hxs⟩
    refine ⟨?_, ?_⟩
    · have h := hC.setup.conj_mem g⁻¹ hxD
      simpa [mul_assoc] using h
    · rw [← hgs] at hxs
      exact (Commute.conj_iff g).mp hxs

theorem regularCore_eq_centralizer (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q) : Q = Subgroup.centralizer (U : Set G) := by
  have := hU.isElementaryAbelian
  obtain ⟨-, -, ⟨φ, -, hφ⟩, -⟩ := hU.affine h3
  have hQ' : IsRegularCore ((fun v : G => hC.d * v) '' (U : Set G)) Q := hU.sylow_inter ▸ hQ
  refine le_antisymm (hU.regularCore_le_centralizer h3 hQ') fun c hc => ?_
  obtain ⟨⟨s, hs⟩, hs1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU.ne_bot
  have hs1' : s ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hcs : c ∈ Subgroup.centralizer ({s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hc s hs).symm
  have hcN := hU.centralizer_le_normalizer_delta hH h3 h5 hs hs1' hcs
  exact hU.mem_regularCore_of_linear_eq_one h3 hQ' φ hφ (n := ⟨c, hcN⟩)
    ((affine_linear_eq_one_iff φ hφ ⟨c, hcN⟩).mpr hc)

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
