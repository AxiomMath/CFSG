module

public import CFSG.Timmesfeld.Bridge.OddLocalCommonY

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge.Asc72
open scoped commutatorElement

namespace OddLocal

variable {G : Type} [Group G] {D : Set G}

theorem mk_ne_one_of_isBender {H : Type} [Group H] [Finite H] {K : Set H} (hK : Setup H K)
    {N : Subgroup H} [N.Normal] (hB : CFSG.BenderSuzuki.IsBenderGroup (H ⧸ N)) {k : H}
    (hk : k ∈ K) : QuotientGroup.mk' N k ≠ 1 := by
  intro h1
  have hkN : k ∈ N := by rwa [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
  rcases hK.subset_or_disjoint N with hsub | hdis
  · have htop := hK.eq_top_of_subset N hsub
    obtain ⟨u, v, huv⟩ := Asc72.IsBenderGroup.exists_not_commute hB
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective N v
    have hu : QuotientGroup.mk' N u = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', htop]
      exact Subgroup.mem_top u
    have hv : QuotientGroup.mk' N v = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk', htop]
      exact Subgroup.mem_top v
    rw [hu, hv]
  · exact hdis k hk hkN

section Conf

variable (hS : Setup G D) {d x y : G} (hd : d ∈ D) (hx : x ∈ D) (hdx : ¬ Commute d x)
  (hy : y ∈ D) (hyc : y ∈ Subgroup.closure {d, x}) (hdy : ¬ Commute d y)
  (hno : ∀ e ∈ D, Commute e d → Commute e x → False)
  [Finite G] (hcenter : Subgroup.center G = ⊥) {d₁ : G} {n : ℕ}
  (htri : IsTriangle D d y d₁) (hn : Odd n) (hord : orderOf (d * d₁ * y) = 2 * n)
include hS hd hx hdx hy hyc hdy hno hcenter htri hn hord

omit hn in
theorem false_of_thirdKind_of_mem (h16 : OddTranspZStar) (IH : CNBelow (Nat.card G))
    (Yd : YData D d d₁ y n) {r : G} (htr : IsTriangle D d r Yd.a) {k : ℕ} (hk : Odd k)
    (hordk : orderOf (d * Yd.a * r) = 2 * k) (htD : (d * Yd.a * r) ^ k ∉ D)
    (htS : d * Yd.a * (d * Yd.a * r) ^ k ∈ Yd.S) : False := by
  set a := Yd.a with ha
  set Y := yGroup D Yd.S y with hY
  obtain ⟨htt, ht1, htd, hta, htr', hdat⟩ := htr.third_kind hS.oddT hS.normal hk hordk
  set t := (d * a * r) ^ k with ht
  have haD : a ∈ D := hClass_subset hS.normal hy Yd.a_mem
  have haY : a ∈ Y := hClass_subset_subgroup (mem_yGroup_left D Yd.S y) Yd.a_mem
  have hdY : d ∈ Y := mem_yGroup_of_mem hd Yd.d_memS
  have hrD : r ∈ D := htr.2.2.1
  have hdr : ¬ Commute d r := htr.2.2.2.2.2.1
  have hacomm : Commute a d := Yd.a_comm
  obtain ⟨f, hfE, z', hz'Y, hz'c, heq⟩ := Yd.third _ hdat htS
  have hteq : d * (d * a * t) * a = t := by
    calc d * (d * a * t) * a = (d * d) * (a * (t * a)) := by group
      _ = a * (a * t) := by rw [hS.oddT.mul_self_eq_one hd, one_mul, hta.eq]
      _ = t := by rw [← mul_assoc, hS.oddT.mul_self_eq_one haD, one_mul]
  rw [hteq] at heq
  have hfD : f ∈ D := hClass_subset hS.normal hy hfE
  have hfY : f ∈ Y := hClass_subset_subgroup (mem_yGroup_left D Yd.S y) hfE
  have hf2 := hS.oddT.mul_self_eq_one hfD
  have hz'f : Commute z' f := hz'c f hfY
  have hz'eq : z' = f * t := by
    rw [heq, ← mul_assoc, hf2, one_mul]
  have hft : Commute f t := by
    rw [heq]
    exact (Commute.refl f).mul_right hz'f.symm
  have hfd : Commute f d := by
    have h1 : f = t * z'⁻¹ := by rw [heq]; group
    rw [h1]
    exact htd.mul_left (hz'c d hdY).inv_left
  have hz'1 : z' ≠ 1 := by
    intro h1
    rw [h1, mul_one] at heq
    exact htD (heq ▸ hfD)
  by_cases hrf : Commute r f
  ·
    set R := Subgroup.closure (insert r (Y : Set G)) with hR
    have hYR : Y ≤ R := fun g hg => Subgroup.subset_closure (Set.mem_insert_of_mem r hg)
    have hrR : r ∈ R := Subgroup.subset_closure (Set.mem_insert r _)
    have hyR : y ∈ R := hYR (mem_yGroup_left D Yd.S y)
    have hz'r : Commute z' r := by
      rw [hz'eq]
      exact hrf.symm.mul_left htr'
    have hRc : R ≤ Subgroup.centralizer {z'} := by
      rw [hR, Subgroup.closure_le]
      rintro g (rfl | hg)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hz'r.eq.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hz'c g hg).eq.symm
    have hcardR : Nat.card R < Nat.card G := by
      have hlt : R < ⊤ := by
        refine lt_top_iff_ne_top.mpr fun htop => hz'1 ?_
        have hzc : z' ∈ Subgroup.center G := by
          rw [Subgroup.mem_center_iff]
          intro g
          exact Subgroup.mem_centralizer_singleton_iff.mp (hRc (htop ▸ Subgroup.mem_top g))
        rw [hcenter, Subgroup.mem_bot] at hzc
        exact hzc
      have := Subgroup.card_lt_of_lt hlt
      rwa [Subgroup.card_top] at this
    have hclassmono : hClass Y y ⊆ hClass R y := fun g ⟨h, hh, he⟩ => ⟨h, hYR hh, he⟩
    have hdE : d ∈ hClass Y y :=
      mem_hClass_of_mem_sylow hS hd hx hdx hy hyc hdy hno Yd.d_memS hd Yd.d_memS
    have hdER : d ∈ hClass R y := hclassmono hdE
    have hrER : r ∈ hClass R y := by
      obtain ⟨h₂, hh₂, hh₂e⟩ := hS.oddT.exists_conj hd hrD hdr
      obtain ⟨h', hh', he'⟩ := hdER
      have hh₂R : h₂ ∈ R := by
        have hle : Subgroup.closure ({d, r} : Set G) ≤ R := by
          rw [Subgroup.closure_le]
          rintro w (rfl | rfl)
          · exact hYR hdY
          · exact hrR
        exact hle hh₂
      refine ⟨h₂ * h', R.mul_mem hh₂R hh', ?_⟩
      rw [← hh₂e, he']
      group
    have hgenR : R ≤ Subgroup.closure (hClass R y) := by
      rw [hR, Subgroup.closure_le]
      rintro g (rfl | hg)
      · exact Subgroup.subset_closure hrER
      · exact Subgroup.closure_mono hclassmono
          (yGroup_le_closure_hClass hS hd hx hdx hy hyc hdy hno Yd.d_memS hg)
    have hsqR : ∃ u ∈ hClass R y, ∃ v ∈ hClass R y, u ≠ v ∧ Commute u v ∧
        u * v ∈ hClass R y := by
      obtain ⟨u, hu, v, hv, huv, hc, huvC⟩ := Yd.sq
      exact ⟨u, hclassmono hu, v, hclassmono hv, huv, hc, hclassmono huvC⟩
    by_cases hconnR : ∀ a ∈ hClass R y, ∀ b ∈ hClass R y, Reach (hClass R y) a b
    · obtain ⟨e, he, hed, hey⟩ := exists_common_of_cnBelow hS.oddT hS.normal hyR hy hgenR IH
        hcardR hconnR hsqR hdER (self_mem_hClass R y) hdy
      exact not_commute_pair hS hd hx hdx hy hyc hdy hno (hClass_subset hS.normal hy he) hed hey
    ·
      have hB := isBender_of_not_conn hS.oddT hS.normal hyR hy hgenR h16 hconnR hsqR
      have hSR := setup_hClass hS.oddT hS.normal hyR hy hgenR
      have hfER : f ∈ hClass R y := hclassmono hfE
      set π := QuotientGroup.mk' (zStar R)
      set f' : R := ⟨f, hClass_subset_subgroup hyR hfER⟩
      set r' : R := ⟨r, hrR⟩
      set d' : R := ⟨d, hClass_subset_subgroup hyR hdER⟩
      have hinv : ∀ {k : R}, (k : G) ∈ hClass R y → orderOf (π k) = 2 := fun hk =>
        orderOf_eq_prime (by rw [pow_two, ← map_mul, hSR.oddT.mul_self_eq_one hk, map_one])
          (mk_ne_one_of_isBender hSR hB hk)
      have h1 : Commute r' f' := Subtype.ext hrf.eq
      have h2 : Commute f' d' := Subtype.ext hfd.eq
      have h3 := IsBenderGroup.commute_trans hB (hinv (k := r') hrER) (hinv (k := f') hfER)
        (hinv (k := d') hdER) (h1.map π) (h2.map π)
      have h4 := (commute_iff_mod_zStar hSR.oddT (a := r') (b := d') hrER hdER).mp h3
      exact hdr (h4.map R.subtype).symm
  ·
    obtain ⟨h₁, hh₁, hh₁e⟩ := hS.oddT.exists_conj hrD hfD hrf
    obtain ⟨h₂, hh₂, hh₂e⟩ := hS.oddT.exists_conj hd hrD hdr
    have hle : ∀ {u v : G}, Commute u t → Commute v t →
        Subgroup.closure ({u, v} : Set G) ≤ Subgroup.centralizer {t} := by
      intro u v hu hv
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hu.eq
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hv.eq
    have hh₁t : Commute h₁ t := Subgroup.mem_centralizer_singleton_iff.mp
      (hle htr'.symm hft hh₁)
    have hh₂t : Commute h₂ t := Subgroup.mem_centralizer_singleton_iff.mp
      (hle htd.symm htr'.symm hh₂)
    set h := h₁ * h₂ with hh
    have hht : Commute h t := hh₁t.mul_left hh₂t
    have hhd : h * d * h⁻¹ = f := by
      rw [hh, show h₁ * h₂ * d * (h₁ * h₂)⁻¹ = h₁ * (h₂ * d * h₂⁻¹) * h₁⁻¹ by group, hh₂e, hh₁e]
    have hz'uv : z' = (h * a * h⁻¹) * (h * (d * a * t) * h⁻¹) := by
      rw [hz'eq, ← hhd]
      have e1 : h * a * h⁻¹ * (h * (d * a * t) * h⁻¹) = h * (a * (d * a * t)) * h⁻¹ := by group
      have e2 : a * (d * a * t) = d * t := by
        rw [show a * (d * a * t) = (a * d) * a * t by group, hacomm.eq,
          show d * a * a * t = d * (a * a) * t by group, hS.oddT.mul_self_eq_one haD, mul_one]
      rw [e1, e2]
      calc h * d * h⁻¹ * t = h * d * h⁻¹ * (h * t * h⁻¹) := by rw [hht.eq, mul_inv_cancel_right]
        _ = h * (d * t) * h⁻¹ := by group
    have huD : h * a * h⁻¹ ∈ D := hS.normal h a haD
    have hvD : h * (d * a * t) * h⁻¹ ∈ D := hS.normal h _ hdat
    have hne : h * a * h⁻¹ ≠ h * (d * a * t) * h⁻¹ := by
      intro he
      have : a = d * a * t := by simpa using he
      have hdt : d * t = 1 := by
        have e3 : d * a * t = a * (d * t) := by rw [← hacomm.eq]; group
        rw [e3] at this
        exact (mul_eq_left.mp this.symm)
      apply hdr
      have : d = t := hS.oddT.eq_of_mul_eq_one hd hdt
      rw [this]
      exact htr'
    have huv : Commute (h * a * h⁻¹) (h * (d * a * t) * h⁻¹) :=
      ((hacomm.mul_right (Commute.refl a)).mul_right hta.symm).conj h
    have hcomm : ∀ e ∈ hClass Y y, Commute e (h * a * h⁻¹) := by
      intro e he
      have heD := hClass_subset hS.normal hy he
      have h1 : Commute e z' := (hz'c e (hClass_subset_subgroup (mem_yGroup_left D Yd.S y) he)).symm
      rw [hz'uv] at h1
      exact ((hS.oddT.commute_mul_iff huD hvD heD hne huv).mp h1).1
    have hdE : d ∈ hClass Y y :=
      mem_hClass_of_mem_sylow hS hd hx hdx hy hyc hdy hno Yd.d_memS hd Yd.d_memS
    exact not_commute_pair hS hd hx hdx hy hyc hdy hno huD (hcomm d hdE).symm
      (hcomm y (self_mem_hClass _ _)).symm

omit hn in
theorem false_of_thirdKind (h16 : OddTranspZStar) (IH : CNBelow (Nat.card G))
    (Yd : YData D d d₁ y n) {r : G} (htr : IsTriangle D d r Yd.a) {k : ℕ} (hk : Odd k)
    (hordk : orderOf (d * Yd.a * r) = 2 * k) (htD : (d * Yd.a * r) ^ k ∉ D) : False := by
  set a := Yd.a with ha
  obtain ⟨htt, -, htd, hta, -, hdat⟩ := htr.third_kind hS.oddT hS.normal hk hordk
  set t := (d * a * r) ^ k with ht
  have haD : a ∈ D := hClass_subset hS.normal hy Yd.a_mem
  have hacomm : Commute a d := Yd.a_comm
  obtain ⟨T, hdT, haT, htT⟩ := exists_sylow_of_commute (hS.oddT.mul_self_eq_one hd)
    (hS.oddT.mul_self_eq_one haD) htt hacomm.symm htd.symm hta.symm
  obtain ⟨c, hca, hcd, hcS⟩ := exists_conj_mem_sylow hS Yd.S T haD hd Yd.a_memS Yd.d_memS haT
    hdT hdat (T.mul_mem (T.mul_mem hdT haT) htT)
  have hcd' : c * d * c⁻¹ = d := by rw [hcd.eq, mul_inv_cancel_right]
  have hca' : c * a * c⁻¹ = a := by rw [hca.eq, mul_inv_cancel_right]
  have hconj : ∀ u : G, c * (d * a * u) * c⁻¹ = d * a * (c * u * c⁻¹) := by
    intro u
    calc c * (d * a * u) * c⁻¹ = c * d * c⁻¹ * (c * a * c⁻¹) * (c * u * c⁻¹) := by group
      _ = d * a * (c * u * c⁻¹) := by rw [hcd', hca']
  set r' := c * r * c⁻¹ with hr'
  have htr' : IsTriangle D d r' a := by
    refine ⟨hd, haD, hS.normal c r htr.2.2.1, htr.2.2.2.1, htr.2.2.2.2.1, ?_, ?_⟩
    · intro h
      apply htr.2.2.2.2.2.1
      rw [← hcd', hr', Commute.conj_iff] at h
      exact h
    · intro h
      apply htr.2.2.2.2.2.2
      rw [← hca', hr', Commute.conj_iff] at h
      exact h
  have hord' : orderOf (d * a * r') = 2 * k := by
    rw [hr', ← hconj, orderOf_conj_eq]
    exact hordk
  have hpow : (d * a * r') ^ k = c * t * c⁻¹ := by
    rw [hr', ← hconj, conj_pow]
  refine false_of_thirdKind_of_mem hS hd hx hdx hy hyc hdy hno hcenter htri hord h16 IH Yd htr'
    hk hord' ?_ ?_
  · rw [hpow]
    intro h
    exact htD (by simpa [mul_assoc] using hS.normal c⁻¹ _ h)
  · rw [hpow, ← hconj]
    exact hcS

end Conf

end OddLocal

end CFSG.Timmesfeld.Bridge
