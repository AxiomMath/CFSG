module

public import CFSG.OddTranspositions.PartThree.Nine.Delta
import CFSG.OddTranspositions.SixEight
import CFSG.OddTranspositions.WidthOne
import CFSG.Timmesfeld.Bridge.Asc72Lift
import CFSG.Timmesfeld.Bridge.OddLocalCommonBasic
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem commute_trans_of_mem_commSet_d (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {a b c : G} (ha : a ∈ commSet D hC.d) (hb : b ∈ commSet D hC.d)
    (hc : c ∈ commSet D hC.d) (hac : Commute a c) (hcb : Commute c b) : Commute a b := by
  set H := Halpha D hC.alpha
  set π := QuotientGroup.mk' (Subgroup.center H)
  have hmemH : ∀ {x : G}, x ∈ commSet D hC.d → x ∈ H := fun hx =>
    Subgroup.subset_closure ((DalphaStar_eq_commSet hC h3.1).symm ▸ hx)
  have huH : ∀ h ∈ H, Commute hC.d h := fun h hh =>
    (show Commute h hC.d from
      Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hh)).symm
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hsq : ∀ {x : G}, x ∈ commSet D hC.d → x * x = 1 := fun hx =>
    hC.setup.oddT.mul_self_eq_one hx.1
  have hinv : ∀ {x : G} (hx : x ∈ commSet D hC.d), orderOf (π ⟨x, hmemH hx⟩) = 2 := by
    intro x hx
    refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [← map_pow, pow_two,
        show (⟨x, hmemH hx⟩ : H) * ⟨x, hmemH hx⟩ = 1 from Subtype.ext (hsq hx), map_one]
    · have hZ := (QuotientGroup.eq_one_iff _).mp h1
      have hxc : ∀ h ∈ H, Commute x h := fun h hh =>
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp hZ ⟨h, hh⟩)).symm
      have hlc : ∀ h ∈ H, Commute (hC.d * x) h := fun h hh => (huH h hh).mul_left (hxc h hh)
      have hl2 : hC.d * x * (hC.d * x) = 1 := by
        calc hC.d * x * (hC.d * x) = hC.d * (x * hC.d) * x := by group
          _ = hC.d * (hC.d * x) * x := by rw [hx.2.1.eq]
          _ = hC.d * hC.d * (x * x) := by group
          _ = 1 := by rw [hu2, hsq hx, one_mul]
      have h1' := eq_one_of_mem_pResidualOf_of_commute hC h3 (mul_mem_of_mem_commSet hC h3 hx)
        hlc hl2
      exact hx.2.2 (by rw [eq_inv_of_mul_eq_one_right h1', hC.setup.oddT.inv_eq hC.hd])
  have hcomm : ∀ {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d), Commute x y →
      Commute (π ⟨x, hmemH hx⟩) (π ⟨y, hmemH hy⟩) := fun hx hy h =>
    (show Commute (⟨_, hmemH hx⟩ : H) ⟨_, hmemH hy⟩ from Subtype.ext h).map π
  have hπ := OddLocal.IsBenderGroup.commute_trans hH.bender (hinv ha) (hinv hc) (hinv hb)
    (hcomm ha hc hac) (hcomm hc hb hcb)
  by_contra hab
  have hodd : Odd (orderOf (a * b)) := hC.setup.oddT.odd_of_not_commute ha.1 hb.1 hab
  set a' : H := ⟨a, hmemH ha⟩
  set b' : H := ⟨b, hmemH hb⟩
  have hdvd1 : orderOf (π (a' * b')) ∣ orderOf (a * b) :=
    (orderOf_map_dvd π (a' * b')).trans (Subgroup.orderOf_coe (a' * b')).symm.dvd
  have hdvd2 : orderOf (π (a' * b')) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [map_mul, hπ.mul_pow, ← map_pow, ← map_pow, pow_two, pow_two,
      show a' * a' = 1 from Subtype.ext (hsq ha), show b' * b' = 1 from Subtype.ext (hsq hb),
      map_one, one_mul]
  have h1 : orderOf (π (a' * b')) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · rw [h] at hdvd1
      exact absurd (hodd.of_dvd_nat hdvd1) (Nat.not_odd_iff_even.mpr even_two)
  have hZ : a' * b' ∈ Subgroup.center H :=
    (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
  have hca : a * (a * b) = a * b * a := congrArg Subtype.val (Subgroup.mem_center_iff.mp hZ a')
  have hb' : b = a * b * a := by rw [← hca, ← mul_assoc, hsq ha, one_mul]
  apply hab
  calc a * b = a * (a * b * a) := by rw [← hb']
    _ = a * a * b * a := by group
    _ = b * a := by rw [hsq ha, one_mul]

theorem commute_trans_of_mem_commSet (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {p : G} (hp : p ∈ D) {a b c : G} (ha : a ∈ commSet D p)
    (hb : b ∈ commSet D p) (hc : c ∈ commSet D p) (hac : Commute a c) (hcb : Commute c b) :
    Commute a b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hC.hd hp)
  have hcomm : ∀ {x y : G}, Commute x y → Commute (g⁻¹ * x * g) (g⁻¹ * y * g) := fun h => by
    have h' := (Commute.conj_iff g⁻¹).mpr h
    rwa [inv_inv] at h'
  have hmem : ∀ {x : G}, x ∈ commSet D p → g⁻¹ * x * g ∈ commSet D hC.d := by
    rintro x ⟨hxD, hxp, hxne⟩
    refine ⟨?_, ?_, fun h => hxne ?_⟩
    · have h' := hC.setup.conj_mem g⁻¹ hxD
      rwa [inv_inv] at h'
    · have h := hcomm hxp
      rwa [← hg, show g⁻¹ * (g * hC.d * g⁻¹) * g = hC.d by group] at h
    · rw [← hg, ← h]
      group
  have key := commute_trans_of_mem_commSet_d hC hH h3 (hmem ha) (hmem hb) (hmem hc) (hcomm hac)
    (hcomm hcb)
  have key' := (Commute.conj_iff g).mpr key
  rwa [show g * (g⁻¹ * a * g) * g⁻¹ = a by group, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    at key'

theorem eq_one_of_mem_centralizer_Halpha_of_conj_eq (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {e : G}
    (he : e ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) {w : G} (hw : w ∈ D)
    (hwu : ¬ Commute w hC.d) (hew : e * w * e⁻¹ = w) : e = 1 := by
  classical
  set A : Set G := insert w {x | x ∈ D ∧ Commute x hC.d}
  have hAD : A ⊆ D := by
    rintro x (hx | ⟨hx, -⟩)
    · rw [hx]
      exact hw
    · exact hx
  set X := Subgroup.closure A
  have hXD : X = Subgroup.closure ((X : Set G) ∩ D) :=
    le_antisymm (Subgroup.closure_le _ |>.mpr fun x hx =>
        Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hAD hx⟩)
      (Subgroup.closure_le _ |>.mpr fun x hx => hx.1)
  have hdX : hC.d ∈ X := Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨hC.hd, Commute.refl _⟩)
  have hEX : hC.E ⊆ (X : Set G) := by
    intro x hx
    have hx' : x ∈ DalphaStar D hC.alpha := hC.DalphaStar_alpha ▸ hx
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hC.DalphaStar_subset_commute hx'))
  have hXtop : X = ⊤ := by
    by_contra hne
    have hwX : w ∈ (X : Set G) ∩ D := ⟨Subgroup.subset_closure (Set.mem_insert _ _), hw⟩
    rcases inter_D_subset_perp hC hXD hdX hEX hne hwX with hwα | hwE
    · rw [h3.1, Set.mem_singleton_iff] at hwα
      exact hwu (hwα ▸ Commute.refl _)
    · exact hwu (hC.DalphaStar_subset_commute hwE).2
  have heH : ∀ h ∈ Halpha D hC.alpha, Commute e h := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp he h hh).symm
  have hgen : ∀ x ∈ A, Commute e x := by
    rintro x (hx | ⟨hxD, hxu⟩)
    · rw [hx]
      calc e * w = e * w * e⁻¹ * e := by group
        _ = w * e := by rw [hew]
    · by_cases hxu' : x = hC.d
      · rw [hxu']
        exact heH _ (d_mem_Halpha hC h3)
      · refine heH x (Subgroup.subset_closure ?_)
        rw [DalphaStar_eq_commSet hC h3.1]
        exact ⟨hxD, hxu, hxu'⟩
  have hxc : ∀ g : G, Commute e g := by
    intro g
    have hg : g ∈ X := hXtop ▸ Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one => exact Commute.one_right e
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have heZ : e ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => (hxc g).eq.symm
  have hZ := hH.solv (Subgroup.center G) inferInstance inferInstance
  rw [hZ, Subgroup.mem_bot] at heZ
  exact heZ

theorem eq_of_commute_of_mem_centSet_pair (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {v v' : G} (hv : v ∈ D) (hv' : v' ∈ D) (hvv' : ¬ Commute v v')
    {p p' : G} (hp : p ∈ D) (hpv : Commute p v) (hpv' : Commute p v') (hp' : p' ∈ D)
    (hp'v : Commute p' v) (hp'v' : Commute p' v') (hpp' : Commute p p') : p = p' := by
  by_contra hne
  have hvD : v ∈ commSet D p := ⟨hv, hpv.symm, fun h => hvv' (h ▸ hpv')⟩
  have hv'D : v' ∈ commSet D p := ⟨hv', hpv'.symm, fun h => hvv' (h ▸ hpv.symm)⟩
  have hp'D : p' ∈ commSet D p := ⟨hp', hpp'.symm, fun h => hne h.symm⟩
  exact hvv' (commute_trans_of_mem_commSet hC hH h3 hp hvD hv'D hp'D hp'v.symm hp'v')

theorem odd_card_closure_mul_of_forall_commute (hD : IsOddTransp D) {P : Set G} (hPD : P ⊆ D)
    (hP : ∀ p ∈ P, ∀ p' ∈ P, Commute p p' → p = p')
    (hPn : ∀ y ∈ Subgroup.closure P, ∀ p ∈ P, y * p * y⁻¹ ∈ P) {x : G} (hx : x ∈ P) :
    Odd (Nat.card (Subgroup.closure ((fun p => p * x) '' P))) := by
  classical
  have hxY : x ∈ Subgroup.closure P := Subgroup.subset_closure hx
  set Y := Subgroup.closure P
  have hconj : ∀ p ∈ P, ∃ g ∈ Y, g * x * g⁻¹ = p := by
    intro p hp
    by_cases hpx : p = x
    · exact ⟨1, Y.one_mem, by rw [hpx]; group⟩
    · obtain ⟨g, hg, hgp⟩ := hD.exists_conj (hPD hx) (hPD hp)
        (fun h => hpx (hP p hp x hx h.symm))
      exact ⟨g, Subgroup.closure_mono
        (Set.insert_subset_iff.mpr ⟨hx, Set.singleton_subset_iff.mpr hp⟩) hg, hgp⟩
  have hS : Setup Y (((↑) : Y → G) ⁻¹' P) := by
    refine ⟨⟨⟨x, hxY⟩, ?_⟩, (hD.mono hPD).preimage Y, Subgroup.closure_closure_coe_preimage⟩
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro hg
      obtain ⟨c, hc, hcx⟩ := hconj g hg
      exact isConj_iff.mpr ⟨⟨c, hc⟩, Subtype.ext (by simpa using hcx)⟩
    · intro hg
      obtain ⟨c, hc⟩ := isConj_iff.mp hg
      rw [← hc]
      simpa using hPn c c.2 x hx
  have hW : WidthOne (((↑) : Y → G) ⁻¹' P) :=
    widthOne_of_forall_not_commute hS.oddT hS.normal ⟨⟨x, hxY⟩, hx⟩
      fun a ha b hb hab => Subtype.ext (hP a ha b hb (congrArg Subtype.val hab))
  have hidx : (CFSG.oddCore Y).index = 2 := index_oddCore_eq_two_of_widthOne hS hW
  have hOodd := CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y
  have hnotO : ∀ p ∈ ((↑) : Y → G) ⁻¹' P, p ∉ CFSG.oddCore Y := by
    intro p hp hpO
    have h2 := Subgroup.orderOf_dvd_natCard (CFSG.oddCore Y) hpO
    rw [hS.oddT.orderOf_eq_two hp] at h2
    exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
  have hle : Subgroup.closure ((fun p => p * x) '' P) ≤ (CFSG.oddCore Y).map Y.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, hp, rfl⟩
    have hpY : p ∈ Y := Subgroup.subset_closure hp
    refine ⟨⟨p, hpY⟩ * ⟨x, hxY⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mul_mem_iff_of_index_two hidx]
    exact iff_of_false (hnotO _ hp) (hnotO _ hx)
  have hcard := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective Y.subtype_injective] at hcard
  exact hOodd.of_dvd_nat hcard

theorem eq_d_of_conj_eq_of_commute_pair (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {e : G}
    (he : e ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) (he1 : e ≠ 1) {v v' : G}
    (hv : v ∈ commSet D hC.d) (hv' : v' ∈ commSet D hC.d) (hvv' : ¬ Commute v v') {p : G}
    (hp : p ∈ D) (hpv : Commute p v) (hpv' : Commute p v') (hep : e * p * e⁻¹ = p) :
    p = hC.d := by
  by_contra hpu
  have hpu' : ¬ Commute p hC.d := fun h =>
    hpu (eq_of_commute_of_mem_centSet_pair hC hH h3 hv.1 hv'.1 hvv' hp hpv hpv' hC.hd
      hv.2.1.symm hv'.2.1.symm h)
  exact he1 (eq_one_of_mem_centralizer_Halpha_of_conj_eq hC hH h3 he hp hpu' hep)

theorem eq_d_of_commute_pair_of_involution (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {f : G}
    (hf : f ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) (hf2 : f * f = 1)
    (hf1 : f ≠ 1) (hfu : f ≠ hC.d) {v v' : G} (hv : v ∈ commSet D hC.d)
    (hv' : v' ∈ commSet D hC.d) (hvv' : ¬ Commute v v') {p : G} (hp : p ∈ D)
    (hpv : Commute p v) (hpv' : Commute p v') : p = hC.d := by
  classical
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huinv : hC.d⁻¹ = hC.d := hC.setup.oddT.inv_eq hC.hd
  set P : Set G := {q | q ∈ D ∧ Commute q v ∧ Commute q v'}
  have huP : hC.d ∈ P := ⟨hC.hd, hv.2.1.symm, hv'.2.1.symm⟩
  have hPw : ∀ q ∈ P, ∀ q' ∈ P, Commute q q' → q = q' := fun q hq q' hq' h =>
    eq_of_commute_of_mem_centSet_pair hC hH h3 hv.1 hv'.1 hvv' hq.1 hq.2.1 hq.2.2 hq'.1
      hq'.2.1 hq'.2.2 h
  have hPc : ∀ y : G, Commute y v → Commute y v' → ∀ q ∈ P, y * q * y⁻¹ ∈ P := by
    intro y hyv hyv' q hq
    refine ⟨hC.setup.conj_mem y hq.1, ?_, ?_⟩
    · have h := (Commute.conj_iff y).mpr hq.2.1
      rwa [hyv.eq, mul_inv_cancel_right] at h
    · have h := (Commute.conj_iff y).mpr hq.2.2
      rwa [hyv'.eq, mul_inv_cancel_right] at h
  have hYv : ∀ y ∈ Subgroup.closure P, Commute y v ∧ Commute y v' := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem q hq => exact ⟨hq.2.1, hq.2.2⟩
    | one => exact ⟨Commute.one_left v, Commute.one_left v'⟩
    | mul a b _ _ ha hb => exact ⟨ha.1.mul_left hb.1, ha.2.mul_left hb.2⟩
    | inv a _ ha => exact ⟨ha.1.inv_left, ha.2.inv_left⟩
  obtain ⟨O, hO⟩ : ∃ O : Subgroup G, O = Subgroup.closure ((fun q => q * hC.d) '' P) :=
    ⟨_, rfl⟩
  have hOodd : Odd (Nat.card O) := hO ▸ odd_card_closure_mul_of_forall_commute hC.setup.oddT
    (fun q hq => hq.1) hPw (fun y hy => hPc y (hYv y hy).1 (hYv y hy).2) huP
  have hOY : O ≤ Subgroup.closure P := by
    rw [hO, Subgroup.closure_le]
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.subset_closure hq) (Subgroup.subset_closure huP)
  have hconjO : ∀ t : G, (∀ q ∈ P, t * (q * hC.d) * t⁻¹ ∈ O) → ∀ y ∈ O, t * y * t⁻¹ ∈ O := by
    intro t ht y hy
    rw [hO] at hy ht ⊢
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨q, hq, rfl⟩ := hs
      exact ht q hq
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show t * (a * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  have hnorm : ∀ t : G, t * t = 1 → (∀ y ∈ O, t * y * t⁻¹ ∈ O) →
      t ∈ Subgroup.normalizer (O : Set G) := by
    intro t ht h
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨h y, fun hy => ?_⟩
    have h' := h _ hy
    rwa [show t * (t * y * t⁻¹) * t⁻¹ = t * t * y * (t * t)⁻¹ by group, ht, one_mul, inv_one,
      mul_one] at h'
  have hmemH : ∀ {x : G}, x ∈ commSet D hC.d → x ∈ Halpha D hC.alpha := fun hx =>
    Subgroup.subset_closure ((DalphaStar_eq_commSet hC h3.1).symm ▸ hx)
  have hfc : ∀ h ∈ Halpha D hC.alpha, Commute f h := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp hf h hh).symm
  have hfu' : Commute f hC.d := hfc _ (d_mem_Halpha hC h3)
  have hfO : f ∈ Subgroup.normalizer (O : Set G) := by
    refine hnorm f hf2 (hconjO f fun q hq => ?_)
    have hq' := hPc f (hfc _ (hmemH hv)) (hfc _ (hmemH hv')) q hq
    have e : f * (q * hC.d) * f⁻¹ = f * q * f⁻¹ * hC.d := by
      calc f * (q * hC.d) * f⁻¹ = f * q * f⁻¹ * (f * hC.d * f⁻¹) := by group
        _ = f * q * f⁻¹ * hC.d := by rw [hfu'.eq, mul_inv_cancel_right]
    rw [e, hO]
    exact Subgroup.subset_closure ⟨_, hq', rfl⟩
  have huO : hC.d ∈ Subgroup.normalizer (O : Set G) := by
    refine hnorm hC.d hu2 (hconjO hC.d fun q hq => ?_)
    have e : hC.d * (q * hC.d) * hC.d⁻¹ = (q * hC.d)⁻¹ := by
      calc hC.d * (q * hC.d) * hC.d⁻¹ = hC.d * q := by group
        _ = (q * hC.d)⁻¹ := by rw [mul_inv_rev, huinv, hC.setup.oddT.inv_eq hq.1]
    rw [e, hO]
    exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨q, hq, rfl⟩)
  have hfix : ∀ e ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G), e ≠ 1 →
      ∀ x ∈ O, x * e = e * x → hC.d * x = x * hC.d := by
    intro e he he1 x hxO hxe
    have hxv := hYv x (hOY hxO)
    have hy : x * hC.d * x⁻¹ ∈ P := hPc x hxv.1 hxv.2 _ huP
    have heu : Commute e hC.d :=
      (Subgroup.mem_centralizer_iff.mp he _ (d_mem_Halpha hC h3)).symm
    have hex : Commute e x := hxe.symm
    have hey : e * (x * hC.d * x⁻¹) * e⁻¹ = x * hC.d * x⁻¹ := by
      rw [((hex.mul_right heu).mul_right hex.inv_right).eq, mul_inv_cancel_right]
    have h1 := eq_d_of_conj_eq_of_commute_pair hC hH h3 he he1 hv hv' hvv' hy.1 hy.2.1 hy.2.2 hey
    calc hC.d * x = x * hC.d * x⁻¹ * x := by rw [h1]
      _ = x * hC.d := by group
  have huE : hC.d ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.mp (PartThree.Halpha_le_centralizer_d hC hh)
  have hfu1 : f * hC.d ≠ 1 := fun h => hfu (by rw [eq_inv_of_mul_eq_one_left h, huinv])
  have hkey := CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.commute_of_four_group_centralizers
    hOodd hf2 hu2 hfu'.eq hf1 (hC.setup.oddT.ne_one hC.hd) hfu hfO huO (z := hC.d)
    (fun x hx hxf => hfix f hf hf1 x hx hxf) (fun _ _ hxu => hxu.symm)
    (fun x hx hxfu => hfix (f * hC.d) (Subgroup.mul_mem _ hf huE) hfu1 x hx hxfu)
  have hpP : p ∈ P := ⟨hp, hpv, hpv'⟩
  by_cases hpu : Commute p hC.d
  · exact hPw p hpP _ huP hpu
  · obtain ⟨k, hk⟩ := hC.setup.oddT.odd_of_not_commute hC.hd hp (fun h => hpu h.symm)
    have hupO : hC.d * p ∈ O := by
      have e : hC.d * p = (p * hC.d)⁻¹ := by
        rw [mul_inv_rev, huinv, hC.setup.oddT.inv_eq hp]
      rw [e, hO]
      exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨p, hpP, rfl⟩)
    have hc := hkey _ (Subgroup.pow_mem _ hupO k)
    have hconj := conj_eq_of_odd hu2 (hC.setup.oddT.mul_self_eq_one hp) hk
    rw [← hconj, ← hc, mul_inv_cancel_right]

theorem subsingleton_commSet_inter_of_involution (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC) {f : G}
    (hf : f ∈ Subgroup.centralizer (Halpha D hC.alpha : Set G)) (hf2 : f * f = 1)
    (hf1 : f ≠ 1) (hfu : f ≠ hC.d) :
    ∀ w ∈ D, ¬ Commute w hC.d → (commSet D hC.d ∩ commSet D w).Subsingleton := by
  intro w hw hwu v hv v' hv'
  by_contra hne
  by_cases hvv' : Commute v v'
  ·
    have huv : hC.d ∈ commSet D v := ⟨hC.hd, hv.1.2.1.symm, fun h => hv.1.2.2 h.symm⟩
    have hwv : w ∈ commSet D v := ⟨hw, hv.2.2.1.symm, fun h => hv.2.2.2 h.symm⟩
    have hv'v : v' ∈ commSet D v := ⟨hv'.1.1, hvv'.symm, fun h => hne h.symm⟩
    exact hwu (commute_trans_of_mem_commSet hC hH h3 hv.1.1 hwv huv hv'v hv'.2.2.1.symm
      hv'.1.2.1)
  · have hwu' := eq_d_of_commute_pair_of_involution hC hH h3 hf hf2 hf1 hfu hv.1 hv'.1 hvv' hw
      hv.2.2.1.symm hv'.2.2.1.symm
    subst hwu'
    exact hwu (Commute.refl _)

end CFSG.OddTranspositions.PartThree.Nine
