module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClLemmaPDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPairDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClQuad

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {F : LinearMap.BilinForm K V}

theorem span_pair_le_three (e x x' : V) :
    Submodule.span K ({x, x'} : Set V) ≤ Submodule.span K ({e, x, x'} : Set V) :=
  Submodule.span_mono (Set.subset_insert e _)

theorem span_pair_le_four (e f x x' : V) :
    Submodule.span K ({x, x'} : Set V) ≤ Submodule.span K ({e, f, x, x'} : Set V) :=
  Submodule.span_mono ((Set.subset_insert f _).trans (Set.subset_insert e _))

theorem blockQ_of_lemmaPSub (hSub : LemmaPSubStatement) (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (hq : 4 ≤ Nat.card K) {H : Subgroup (V ≃ₗ[K] V)} {e f : V}
    (hef : F e f = 1) (hfe : ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((H : Set _) ∩ pointRad F f) f)
    (hnoT : ¬ ∀ c : K, ∃ g ∈ H, ∀ v, g v = v + (c * F v e) • e) : BlockQ F H e f := by
  unfold BlockQ
  intro x x' hxx' hxe hxf hx'e hx'f
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hD : ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F e) ⊆ pointRad F e := Set.inter_subset_right
  have hD' : ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F f) ⊆ pointRad F f := Set.inter_subset_right
  have hperp : ∀ w ∈ Submodule.span K ({x, x'} : Set V), F w e = 0 ∧ F w f = 0 := by
    intro w hw
    obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hw
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxe,
      hxf, hx'e, hx'f, mul_zero, add_zero, and_self]
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (V ≃ₗ[K] V), ∀ g, g ∈ A ↔
      (g ∈ H ⊓ pointRadSubgroup F e ∧ g f - f ∈ Submodule.span K ({e, x, x'} : Set V)) := by
    refine ⟨{ carrier := {g | g ∈ H ⊓ pointRadSubgroup F e ∧
                g f - f ∈ Submodule.span K ({e, x, x'} : Set V)}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      have ha3 := (Subgroup.mem_inf.mp ha1).2
      have hb3 := (Subgroup.mem_inf.mp hb1).2
      refine ⟨(H ⊓ pointRadSubgroup F e).mul_mem ha1 hb1, ?_⟩
      rw [pointRad_om_mul halt hef ha3 hb3]
      exact Submodule.add_mem _ (Submodule.add_mem _ ha2 hb2)
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · refine ⟨(H ⊓ pointRadSubgroup F e).one_mem, ?_⟩
      simp
    · rintro g ⟨hg1, hg2⟩
      have hgg : g⁻¹ = g :=
        inv_eq_of_mul_eq_one_right (pointRad_mul_self halt hef (Subgroup.mem_inf.mp hg1).2)
      rw [hgg]
      exact ⟨hg1, hg2⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (V ≃ₗ[K] V), ∀ g, g ∈ A' ↔
      (g ∈ H ⊓ pointRadSubgroup F f ∧ g e - e ∈ Submodule.span K ({f, x, x'} : Set V)) := by
    refine ⟨{ carrier := {g | g ∈ H ⊓ pointRadSubgroup F f ∧
                g e - e ∈ Submodule.span K ({f, x, x'} : Set V)}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
      have ha3 := (Subgroup.mem_inf.mp ha1).2
      have hb3 := (Subgroup.mem_inf.mp hb1).2
      refine ⟨(H ⊓ pointRadSubgroup F f).mul_mem ha1 hb1, ?_⟩
      rw [pointRad_om_mul halt hef' ha3 hb3]
      exact Submodule.add_mem _ (Submodule.add_mem _ ha2 hb2)
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    · refine ⟨(H ⊓ pointRadSubgroup F f).one_mem, ?_⟩
      simp
    · rintro g ⟨hg1, hg2⟩
      have hgg : g⁻¹ = g :=
        inv_eq_of_mul_eq_one_right (pointRad_mul_self halt hef' (Subgroup.mem_inf.mp hg1).2)
      rw [hgg]
      exact ⟨hg1, hg2⟩
  have hAle : A ≤ pointRadSubgroup F e := fun g hg => (Subgroup.mem_inf.mp ((hA g).mp hg).1).2
  have hA'le : A' ≤ pointRadSubgroup F f :=
    fun g hg => (Subgroup.mem_inf.mp ((hA' g).mp hg).1).2
  have hAH : A ⊔ A' ≤ H :=
    sup_le (fun g hg => (Subgroup.mem_inf.mp ((hA g).mp hg).1).1)
      (fun g hg => (Subgroup.mem_inf.mp ((hA' g).mp hg).1).1)
  have hAω : ∀ w ∈ Submodule.span K ({x, x'} : Set V),
      ∃ g ∈ A, ∃ c : K, g f - f = w + c • e := by
    intro w hw
    obtain ⟨g, hgD, c, hc⟩ := ElationFull.om hnd halt hef hD hfe (hperp w hw).1
    refine ⟨g, (hA g).mpr ⟨Subgroup.mem_inf.mpr ⟨hgD.1, hgD.2⟩, ?_⟩, c, hc⟩
    rw [hc]
    exact Submodule.add_mem _ (span_pair_le_three e x x' hw)
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hA'ω : ∀ w ∈ Submodule.span K ({x, x'} : Set V),
      ∃ g ∈ A', ∃ c : K, g e - e = w + c • f := by
    intro w hw
    obtain ⟨g, hgD, c, hc⟩ := ElationFull.om hnd halt hef' hD' hff (hperp w hw).2
    refine ⟨g, (hA' g).mpr ⟨Subgroup.mem_inf.mpr ⟨hgD.1, hgD.2⟩, ?_⟩, c, hc⟩
    rw [hc]
    exact Submodule.add_mem _ (span_pair_le_three f x x' hw)
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hfinal := hSub K V F hq hnd halt e f x x' hef hxx' hxe hxf hx'e hx'f A A' hAle hA'le
    (fun g hg => ((hA g).mp hg).2) (fun g hg => ((hA' g).mp hg).2) hAω hA'ω
  rcases hfinal with hcase | ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩
  · exfalso
    apply hnoT
    intro c
    obtain ⟨g, hg, hgc⟩ := hcase c
    exact ⟨g, hAH hg, hgc⟩
  · exact ⟨q, hq1, hq2, hq3, hq4, fun g hg hgS => hq5 g ((hA g).mpr ⟨hg, hgS⟩),
      fun g hg hgS => hq6 g ((hA' g).mpr ⟨hg, hgS⟩)⟩

theorem perp_span_pair {e f x x' : V} (hxe : F x e = 0) (hxf : F x f = 0) (hx'e : F x' e = 0)
    (hx'f : F x' f = 0) {u : V} (hu : u ∈ Submodule.span K ({x, x'} : Set V)) :
    F u e = 0 ∧ F u f = 0 := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hu
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxe,
    hxf, hx'e, hx'f, mul_zero, add_zero, and_self]

theorem form_add_smul_e (halt : F.IsAlt) (e x y : V) (s t : K) :
    F (x + s • e) (y + t • e) = F x y + t * F x e + s * F e y := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    form_self halt e]
  ring

theorem exists_a_of_blockQ (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 4 ≤ Module.finrank K V) {H : Subgroup (V ≃ₗ[K] V)} {e f : V} (hef : F e f = 1)
    (hfe : ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((H : Set _) ∩ pointRad F f) f) (hblk : BlockQ F H e f) :
    ∃ a : V → K, AData F H e f a := by
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hee : F e e = 0 := form_self halt e
  have hD : ((H : Set (V ≃ₗ[K] V)) ∩ pointRad F e) ⊆ pointRad F e := Set.inter_subset_right
  have hex : ∀ w : V, ∃ g : V ≃ₗ[K] V, F w e = 0 → F w f = 0 →
      g ∈ H ⊓ pointRadSubgroup F e ∧ ∃ c : K, g f - f = w + c • e := by
    intro w
    by_cases hw : F w e = 0
    · obtain ⟨g, hgD, c, hc⟩ := ElationFull.om hnd halt hef hD hfe hw
      exact ⟨g, fun _ _ => ⟨Subgroup.mem_inf.mpr ⟨hgD.1, hgD.2⟩, c, hc⟩⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose gsel hgsel using hex
  obtain ⟨a, ha⟩ : ∃ a : V → K, ∀ w, a w = F f (gsel w f - f) :=
    ⟨fun w => F f (gsel w f - f), fun _ => rfl⟩
  have hi : ∀ w, F w e = 0 → F w f = 0 → gsel w f - f = w + a w • e := by
    intro w hwe hwf
    obtain ⟨_, c, hc⟩ := hgsel w hwe hwf
    have hac : a w = c := by
      rw [ha w, hc]
      simp only [map_add, map_smul, smul_eq_mul]
      rw [form_comm halt f w, hwf, hef', zero_add, mul_one]
    rw [hac]
    exact hc
  have h3 : 3 ≤ Module.finrank K V := by omega
  obtain ⟨x0, hx0, hx0e, hx0f⟩ := exists_perp_ne_zero (F := F) h3 e f
  obtain ⟨x0', hx0'e, hx0'f, hx0x0'⟩ := exists_partner hnd halt hef hx0e hx0f hx0
  obtain ⟨q0, hq0a, hq0b, hq0c, hq0d, hq0e, hq0f⟩ :=
    hblk x0 x0' hx0x0' hx0e hx0f hx0'e hx0'f
  have he4 : e ∈ Submodule.span K ({e, f, x0, x0'} : Set V) := Submodule.subset_span (by simp)
  have hf4 : f ∈ Submodule.span K ({e, f, x0, x0'} : Set V) := Submodule.subset_span (by simp)
  have he3 : e ∈ Submodule.span K ({e, x0, x0'} : Set V) := Submodule.subset_span (by simp)
  have hf3 : f ∈ Submodule.span K ({f, x0, x0'} : Set V) := Submodule.subset_span (by simp)
  have hK : ∀ g ∈ H ⊓ pointRadSubgroup F e, ∀ c : K, g f - f = c • e → c = 0 := by
    intro g hg c hc
    have hmem : g f - f ∈ Submodule.span K ({e, x0, x0'} : Set V) := by
      rw [hc]
      exact Submodule.smul_mem _ c he3
    have h1 := hq0e g hg hmem
    have hgf : g f = f + c • e := by rw [← hc]; abel
    have hce : c • e ∈ Submodule.span K ({e, f, x0, x0'} : Set V) :=
      Submodule.smul_mem _ c he4
    have h2 : q0 (f + c • e) = q0 f + c := by
      rw [hq0b f (c • e) hf4 hce, hq0a c e he4, hq0c]
      simp only [mul_zero, add_zero, map_smul, smul_eq_mul, hef', mul_one]
    rw [hgf, h2] at h1
    linear_combination h1
  have h0e : F (0 : V) e = 0 := by simp
  have h0f : F (0 : V) f = 0 := by simp
  have ha0 : a 0 = 0 := by
    have h0 := hi 0 h0e h0f
    exact hK (gsel 0) (hgsel 0 h0e h0f).1 (a 0) (by rw [h0, zero_add])
  have hadd : ∀ w w' : V, F w e = 0 → F w f = 0 → F w' e = 0 → F w' f = 0 →
      a (w + w') = a w + a w' + F w w' := by
    intro w w' hwe hwf hwe' hwf'
    have hwwe : F (w + w') e = 0 := by
      rw [map_add, LinearMap.add_apply, hwe, hwe', zero_add]
    have hwwf : F (w + w') f = 0 := by
      rw [map_add, LinearMap.add_apply, hwf, hwf', zero_add]
    have hF2 : F e (w + w') = 0 := by rw [form_comm halt, hwwe]
    have hg1 := hgsel w hwe hwf
    have hg2 := hgsel w' hwe' hwf'
    have hg3 := hgsel (w + w') hwwe hwwf
    have hd1 := hi w hwe hwf
    have hd2 := hi w' hwe' hwf'
    have hd3 := hi (w + w') hwwe hwwf
    have hQ1 : gsel w ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg1.1).2
    have hQ2 : gsel w' ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg2.1).2
    have hQ3 : gsel (w + w') ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg3.1).2
    have hQ12 : gsel w * gsel w' ∈ pointRadSubgroup F e :=
      (pointRadSubgroup F e).mul_mem hQ1 hQ2
    have hmem : gsel w * gsel w' * gsel (w + w') ∈ H ⊓ pointRadSubgroup F e :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hg1.1 hg2.1) hg3.1
    have h12 : (gsel w * gsel w') f - f = (w + w') + (a w + a w' + F w w') • e := by
      rw [pointRad_om_mul halt hef hQ1 hQ2, hd1, hd2, form_add_smul_e halt e w w' (a w) (a w'),
        hwe, form_comm halt e w', hwe']
      simp only [mul_zero, add_zero]
      module
    have hF0 : F ((w + w') + (a w + a w' + F w w') • e) ((w + w') + a (w + w') • e) = 0 := by
      rw [form_add_smul_e halt e (w + w') (w + w') (a w + a w' + F w w') (a (w + w')),
        form_self halt, hwwe, hF2]
      ring
    have hsplit : (w + w') + (a w + a w' + F w w') • e + ((w + w') + a (w + w') • e) =
        ((w + w') + (w + w')) + (a w + a w' + F w w' + a (w + w')) • e := by
      module
    have h123 : (gsel w * gsel w' * gsel (w + w')) f - f =
        (a w + a w' + F w w' + a (w + w')) • e := by
      rw [pointRad_om_mul halt hef hQ12 hQ3, h12, hd3, hF0, zero_smul, add_zero, hsplit,
        vec_add_self K (w + w'), zero_add]
    have hcomp := hK _ hmem (a w + a w' + F w w' + a (w + w')) h123
    linear_combination hcomp - (a w + a w' + F w w') * two_eq_zero_K (K := K)
  have hK1 : ∀ (x x' : V) (q : V → K), F x e = 0 → F x f = 0 → F x' e = 0 → F x' f = 0 →
      (∀ (c : K) (u : V), u ∈ Submodule.span K ({e, f, x, x'} : Set V) →
        q (c • u) = c ^ 2 * q u) →
      (∀ u u' : V, u ∈ Submodule.span K ({e, f, x, x'} : Set V) →
        u' ∈ Submodule.span K ({e, f, x, x'} : Set V) → q (u + u') = q u + q u' + F u u') →
      q e = 0 →
      (∀ g ∈ H ⊓ pointRadSubgroup F e, g f - f ∈ Submodule.span K ({e, x, x'} : Set V) →
        q (g f) = q f) →
      ∀ u ∈ Submodule.span K ({x, x'} : Set V), q u = a u := by
    intro x x' q hxe hxf hx'e hx'f hq1 hq2 hqe hq5 u hu
    obtain ⟨hue, huf⟩ := perp_span_pair hxe hxf hx'e hx'f hu
    have hu4 : u ∈ Submodule.span K ({e, f, x, x'} : Set V) := span_pair_le_four e f x x' hu
    have hu3 : u ∈ Submodule.span K ({e, x, x'} : Set V) := span_pair_le_three e x x' hu
    have he4' : e ∈ Submodule.span K ({e, f, x, x'} : Set V) := Submodule.subset_span (by simp)
    have hfmem : f ∈ Submodule.span K ({e, f, x, x'} : Set V) := Submodule.subset_span (by simp)
    have hae4 : a u • e ∈ Submodule.span K ({e, f, x, x'} : Set V) :=
      Submodule.smul_mem _ _ he4'
    have hae3 : a u • e ∈ Submodule.span K ({e, x, x'} : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hdu := hi u hue huf
    have hmem5 : gsel u f - f ∈ Submodule.span K ({e, x, x'} : Set V) := by
      rw [hdu]
      exact Submodule.add_mem _ hu3 hae3
    have h5 := hq5 (gsel u) (hgsel u hue huf).1 hmem5
    have hgf : gsel u f = f + (u + a u • e) := by rw [← hdu]; abel
    have hue' : u + a u • e ∈ Submodule.span K ({e, f, x, x'} : Set V) :=
      Submodule.add_mem _ hu4 hae4
    have h6 := hq2 f (u + a u • e) hfmem hue'
    have hFfu : F f (u + a u • e) = a u := by
      simp only [map_add, map_smul, smul_eq_mul]
      rw [form_comm halt f u, huf, hef', zero_add, mul_one]
    have hq_ue : q (u + a u • e) = q u := by
      rw [hq2 u (a u • e) hu4 hae4, hq1 (a u) e he4', hqe]
      simp only [map_smul, smul_eq_mul, hue, mul_zero, zero_add, add_zero]
    rw [hgf, h6, hFfu, hq_ue] at h5
    linear_combination h5 - (a u) * two_eq_zero_K (K := K)
  have hhom : ∀ (c : K) (w : V), F w e = 0 → F w f = 0 → a (c • w) = c ^ 2 * a w := by
    intro c w hwe hwf
    by_cases hw0 : w = 0
    · subst hw0
      simp [ha0]
    · obtain ⟨w', hw'e, hw'f, hww'⟩ := exists_partner hnd halt hef hwe hwf hw0
      obtain ⟨q, hq1, hq2, hq3, _, hq5, _⟩ := hblk w w' hww' hwe hwf hw'e hw'f
      have hw4 : w ∈ Submodule.span K ({e, f, w, w'} : Set V) := Submodule.subset_span (by simp)
      have hw2 : w ∈ Submodule.span K ({w, w'} : Set V) := Submodule.subset_span (by simp)
      have hcw : c • w ∈ Submodule.span K ({w, w'} : Set V) := Submodule.smul_mem _ c hw2
      have hcwq := hK1 w w' q hwe hwf hw'e hw'f hq1 hq2 hq3 hq5 (c • w) hcw
      have hwq := hK1 w w' q hwe hwf hw'e hw'f hq1 hq2 hq3 hq5 w hw2
      rw [← hcwq, hq1 c w hw4, hwq]
  have hDf : ∀ g ∈ H ⊓ pointRadSubgroup F f, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
      g e - e = w + c • f → c = a w := by
    intro g hg w c hwe hwf hc
    by_cases hw0 : w = 0
    · subst hw0
      have hc' : g e - e = c • f := by rw [hc, zero_add]
      have hmem : g e - e ∈ Submodule.span K ({f, x0, x0'} : Set V) := by
        rw [hc']
        exact Submodule.smul_mem _ c hf3
      have h1 := hq0f g hg hmem
      have hge : g e = e + c • f := by rw [← hc']; abel
      have hcf : c • f ∈ Submodule.span K ({e, f, x0, x0'} : Set V) :=
        Submodule.smul_mem _ c hf4
      have h2 : q0 (e + c • f) = q0 e + c := by
        rw [hq0b e (c • f) he4 hcf, hq0a c f hf4, hq0d]
        simp only [mul_zero, add_zero, map_smul, smul_eq_mul, hef, mul_one]
      rw [hge, h2] at h1
      rw [ha0]
      linear_combination h1
    · obtain ⟨w', hw'e, hw'f, hww'⟩ := exists_partner hnd halt hef hwe hwf hw0
      obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := hblk w w' hww' hwe hwf hw'e hw'f
      have hmem : g e - e ∈ Submodule.span K ({f, w, w'} : Set V) := by
        rw [hc]
        exact Submodule.add_mem _ (Submodule.subset_span (by simp))
          (Submodule.smul_mem _ c (Submodule.subset_span (by simp)))
      have h1 := hq6 g hg hmem
      have hge : g e = e + (w + c • f) := by rw [← hc]; abel
      have hw4 : w ∈ Submodule.span K ({e, f, w, w'} : Set V) := Submodule.subset_span (by simp)
      have hf4' : f ∈ Submodule.span K ({e, f, w, w'} : Set V) := Submodule.subset_span (by simp)
      have hcf4 : c • f ∈ Submodule.span K ({e, f, w, w'} : Set V) :=
        Submodule.smul_mem _ c hf4'
      have hwcf4 : w + c • f ∈ Submodule.span K ({e, f, w, w'} : Set V) :=
        Submodule.add_mem _ hw4 hcf4
      have he4' : e ∈ Submodule.span K ({e, f, w, w'} : Set V) := Submodule.subset_span (by simp)
      have h2 : q (e + (w + c • f)) = q e + q w + c := by
        rw [hq2 e (w + c • f) he4' hwcf4, hq2 w (c • f) hw4 hcf4, hq1 c f hf4', hq4]
        simp only [map_add, map_smul, smul_eq_mul, hwf, hwe, hef, form_comm halt e w, mul_zero,
          add_zero, zero_add, mul_one]
      have hw2 : w ∈ Submodule.span K ({w, w'} : Set V) := Submodule.subset_span (by simp)
      have hqw := hK1 w w' q hwe hwf hw'e hw'f hq1 hq2 hq3 hq5 w hw2
      rw [hge, h2] at h1
      linear_combination h1 - hqw - (a w) * two_eq_zero_K (K := K)
  have hDe : ∀ g ∈ H ⊓ pointRadSubgroup F e, ∀ (w : V) (c : K), F w e = 0 → F w f = 0 →
      g f - f = w + c • e → c = a w := by
    intro g hg w c hwe hwf hc
    have hgw := hgsel w hwe hwf
    have hdw := hi w hwe hwf
    have hQg : g ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hg).2
    have hQw : gsel w ∈ pointRadSubgroup F e := (Subgroup.mem_inf.mp hgw.1).2
    have hmul : g * gsel w ∈ H ⊓ pointRadSubgroup F e := Subgroup.mul_mem _ hg hgw.1
    have hww : (w + c • e) + (w + a w • e) = (c + a w) • e := by
      calc (w + c • e) + (w + a w • e) = (w + w) + (c + a w) • e := by module
        _ = (c + a w) • e := by rw [vec_add_self K w, zero_add]
    have hsum : (g * gsel w) f - f = (c + a w) • e := by
      rw [pointRad_om_mul halt hef hQg hQw, hc, hdw, form_add_smul_e halt e w w c (a w),
        form_self halt, form_comm halt e w, hwe]
      simp only [mul_zero, zero_add, add_zero, zero_smul]
      exact hww
    have h0 := hK _ hmul (c + a w) hsum
    linear_combination h0 - (a w) * two_eq_zero_K (K := K)
  exact ⟨a, fun w hwe hwf => ⟨gsel w, (hgsel w hwe hwf).1, hi w hwe hwf⟩, hhom, hadd, hDe, hDf⟩

theorem exists_quadForm_of_aData (halt : F.IsAlt) {H : Subgroup (V ≃ₗ[K] V)} {e f : V}
    (hef : F e f = 1) {a : V → K} (ha : AData F H e f a) :
    ∃ Q : QuadraticForm K V, Q.polarBilin = F ∧ Q e = 0 ∧ Q f = 0 ∧
      H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q ∧ H ⊓ pointRadSubgroup F f ≤ orthSubgroup Q := by
  obtain ⟨-, hhom, hadd, hDe, hDf⟩ := ha
  obtain ⟨Q, hQ, hQv⟩ := exists_quadForm_of_a halt hef a hhom hadd
  have hef' : F f e = 1 := by rw [form_comm halt]; exact hef
  have hee : F e e = 0 := form_self halt e
  have hff0 : F f f = 0 := form_self halt f
  have ha0 : a 0 = 0 := by
    have h := hhom 0 0 (by simp) (by simp)
    simpa using h
  have hpe0 : e + F e f • e + F e e • f = 0 := by
    rw [hef, hee, one_smul, zero_smul, add_zero, vec_add_self K]
  have hpf0 : f + F f f • e + F f e • f = 0 := by
    rw [hff0, hef', zero_smul, one_smul, add_zero, vec_add_self K]
  have hQe : Q e = 0 := by
    rw [hQv e, hpe0, hee, zero_mul, zero_add, ha0]
  have hQf : Q f = 0 := by
    rw [hQv f, hpf0, hff0, mul_zero, zero_add, ha0]
  have hconj4 : ∀ g ∈ H ⊓ pointRadSubgroup F e, Q (g f - f) = F f (g f - f) := by
    intro g hg
    have hωe : F (g f - f) e = 0 := pointRad_om_perp (Subgroup.mem_inf.mp hg).2
    have hwe : F ((g f - f) + F (g f - f) f • e) e = 0 := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hee,
        mul_zero, add_zero, hωe]
    have hwf : F ((g f - f) + F (g f - f) f • e) f = 0 := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hef,
        mul_one, charTwo_add_self]
    have hdec : g f - f = ((g f - f) + F (g f - f) f • e) + F (g f - f) f • e := by
      rw [add_assoc, ← add_smul, charTwo_add_self, zero_smul, add_zero]
    have hcc := hDe g hg _ _ hwe hwf hdec
    rw [hQv (g f - f), hωe, zero_mul, zero_smul, add_zero, zero_add, ← hcc,
      form_comm halt f (g f - f)]
  have hconj5 : ∀ g ∈ H ⊓ pointRadSubgroup F f, Q (g e - e) = F e (g e - e) := by
    intro g hg
    have hωf : F (g e - e) f = 0 :=
      pointRad_om_perp (e := f) (f := e) (Subgroup.mem_inf.mp hg).2
    have hwf : F ((g e - e) + F (g e - e) e • f) f = 0 := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hff0,
        mul_zero, add_zero, hωf]
    have hwe : F ((g e - e) + F (g e - e) e • f) e = 0 := by
      rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hef',
        mul_one, charTwo_add_self]
    have hdec : g e - e = ((g e - e) + F (g e - e) e • f) + F (g e - e) e • f := by
      rw [add_assoc, ← add_smul, charTwo_add_self, zero_smul, add_zero]
    have hcc := hDf g hg _ _ hwe hwf hdec
    rw [hQv (g e - e), hωf, mul_zero, zero_smul, add_zero, zero_add, ← hcc,
      form_comm halt e (g e - e)]
  exact ⟨Q, hQ, hQe, hQf,
    fun g hg => (pointRad_mem_orth_iff halt hef hQ hQe (Subgroup.mem_inf.mp hg).2).mpr
      (hconj4 g hg),
    fun g hg => (pointRad_mem_orth_iff halt hef' hQ hQf (Subgroup.mem_inf.mp hg).2).mpr
      (hconj5 g hg)⟩

theorem exists_quadForm_of_blockQ (hnd : F.Nondegenerate) (halt : F.IsAlt)
    (hdim : 4 ≤ Module.finrank K V) {H : Subgroup (V ≃ₗ[K] V)} {e f : V} (hef : F e f = 1)
    (hfe : ElationFull F ((H : Set _) ∩ pointRad F e) e)
    (hff : ElationFull F ((H : Set _) ∩ pointRad F f) f) (hblk : BlockQ F H e f) :
    ∃ Q : QuadraticForm K V, Q.polarBilin = F ∧ Q e = 0 ∧ Q f = 0 ∧
      H ⊓ pointRadSubgroup F e ≤ orthSubgroup Q ∧ H ⊓ pointRadSubgroup F f ≤ orthSubgroup Q := by
  obtain ⟨a, ha⟩ := exists_a_of_blockQ hnd halt hdim hef hfe hff hblk
  exact exists_quadForm_of_aData halt hef ha

end CFSG.RankThree.GF2n.Stroth80.Classify
