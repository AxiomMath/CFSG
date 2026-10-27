module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.N143.SectionGroup

public section

namespace CFSG.RankThree.PartOne.Q1327C

open CFSG CFSG.RankThree.PartOne

variable {G : Type} [Group G]

noncomputable abbrev proj (X : Subgroup G) : ↥X →* (↥X ⧸ Subgroup.center ↥X) :=
  QuotientGroup.mk' (Subgroup.center ↥X)

@[expose] noncomputable def bar (X H : Subgroup G) : Subgroup (↥X ⧸ Subgroup.center ↥X) :=
  (H.subgroupOf X).map (proj X)

@[expose] def NoZ (p : ℕ) (X : Subgroup G) : Prop := ¬ p ∣ Nat.card (Subgroup.center ↥X)

section

variable {X H : Subgroup G} {p : ℕ}

theorem ker_proj_card (hZ : NoZ p X) : ¬ p ∣ Nat.card (proj X).ker := by
  rw [QuotientGroup.ker_mk']
  exact hZ

theorem isPGroup_subgroupOf (hHX : H ≤ X) (hH : IsPGroup p H) : IsPGroup p (H.subgroupOf X) :=
  hH.of_injective (Subgroup.subgroupOfEquivOfLe hHX).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hHX).injective

theorem disjoint_subgroupOf_ker [Finite G] (hp : p.Prime) (hZ : NoZ p X) (hHX : H ≤ X)
    (hH : IsPGroup p H) : Disjoint (H.subgroupOf X) (proj X).ker :=
  N143.disjoint_ker_of_isPGroup (proj X) hp (isPGroup_subgroupOf hHX hH) (ker_proj_card hZ)

@[expose] noncomputable def barEquiv [Finite G] (hp : p.Prime) (hZ : NoZ p X) (hHX : H ≤ X)
    (hH : IsPGroup p H) : H ≃* bar X H :=
  (Subgroup.subgroupOfEquivOfLe hHX).symm.trans
    (N143.mapEquiv (proj X) (disjoint_subgroupOf_ker hp hZ hHX hH))

theorem coe_barEquiv [Finite G] (hp : p.Prime) (hZ : NoZ p X) (hHX : H ≤ X) (hH : IsPGroup p H)
    (h : H) : ((barEquiv hp hZ hHX hH h : bar X H) : ↥X ⧸ Subgroup.center ↥X) =
      proj X ⟨(h : G), hHX h.2⟩ := rfl

theorem bar_card [Finite G] (hp : p.Prime) (hZ : NoZ p X) (hHX : H ≤ X) (hH : IsPGroup p H) :
    Nat.card (bar X H) = Nat.card H :=
  (Nat.card_congr (barEquiv hp hZ hHX hH).toEquiv).symm

theorem bar_isElementaryAbelian (hp : p.Prime) (hHX : H ≤ X) (hH : IsElementaryAbelian p H) :
    IsElementaryAbelian p (bar X H) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hH
  have : IsElementaryAbelian p (H.subgroupOf X) := IsElementaryAbelian.subgroupOf hHX
  exact IsElementaryAbelian.map (proj X)

theorem commutator_eq_one_of_central (hp : p.Prime) (hZ : NoZ p X) {x a : ↥X} (ha : a ^ p = 1)
    (hc : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.center ↥X) : x * a * x⁻¹ * a⁻¹ = 1 := by
  set c := x * a * x⁻¹ * a⁻¹ with hcdef
  have hcomm : Commute c a := (Subgroup.mem_center_iff.1 hc a).symm
  have hxa : x * a * x⁻¹ = c * a := by rw [hcdef]; group
  have h1 : (c * a) ^ p = c ^ p * a ^ p := hcomm.mul_pow p
  have h2 : (x * a * x⁻¹) ^ p = 1 := by rw [conj_pow, ha]; group
  rw [hxa, h1, ha, mul_one] at h2
  have h3 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one h2
  have h4 : orderOf c ∣ Nat.card (Subgroup.center ↥X) := Subgroup.orderOf_dvd_natCard _ hc
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥X)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hZ
  have h5 : orderOf c ∣ Nat.gcd p (Nat.card (Subgroup.center ↥X)) := Nat.dvd_gcd h3 h4
  rw [hcop] at h5
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)

theorem exists_lift_of_le [Finite G] (hp : p.Prime) (hZ : NoZ p X) (hHX : H ≤ X)
    (hH : IsElementaryAbelian p H) {P' : Subgroup (↥X ⧸ Subgroup.center ↥X)}
    (hP' : IsElementaryAbelian p P') (hle : bar X H ≤ P') :
    ∃ P : Subgroup G, P ≤ X ∧ H ≤ P ∧ IsElementaryAbelian p P ∧ bar X P = P' := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := hH
  have := hP'
  have hP'p : IsPGroup p P' := IsElementaryAbelian.isPGroup p P'
  let Pt : Subgroup ↥X := P'.comap (proj X)
  have hHPt : H.subgroupOf X ≤ Pt := fun x hx => hle ⟨x, hx, rfl⟩
  let H₁ : Subgroup ↥Pt := (H.subgroupOf X).subgroupOf Pt
  have hH₁ : IsPGroup p H₁ :=
    (isPGroup_subgroupOf hHX (IsElementaryAbelian.isPGroup p H)).comap_subtype
  obtain ⟨Q, hQ⟩ := hH₁.exists_le_sylow
  let Q' : Subgroup ↥X := (Q : Subgroup ↥Pt).map Pt.subtype
  have hQ'Pt : Q' ≤ Pt := Subgroup.map_subtype_le _
  have hHQ' : H.subgroupOf X ≤ Q' := fun x hx =>
    ⟨⟨x, hHPt hx⟩, hQ (show (⟨x, hHPt hx⟩ : ↥Pt) ∈ H₁ from hx), rfl⟩
  have hQ'p : IsPGroup p Q' := Q.isPGroup'.map Pt.subtype
  have hdis : Disjoint Q' (proj X).ker :=
    N143.disjoint_ker_of_isPGroup (proj X) hp hQ'p (ker_proj_card hZ)
  have hinj : Function.Injective ((proj X).subgroupMap Q') :=
    N143.injective_subgroupMap_of_disjoint (proj X) hdis
  have hker_le : (proj X).ker ≤ Pt := fun x hx => by
    show proj X x ∈ P'
    rw [MonoidHom.mem_ker.1 hx]
    exact P'.one_mem
  have hcardPt : Nat.card Pt = Nat.card (proj X).ker * Nat.card P' := by
    have h1 := Subgroup.card_ker_mul_card_range ((proj X).comp Pt.subtype)
    have hrange : ((proj X).comp Pt.subtype).range = P' := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) P'
    have hker : ((proj X).comp Pt.subtype).ker = (proj X).ker.subgroupOf Pt := by
      ext x
      simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    rw [hrange, hker] at h1
    rw [← h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv]
  have hcardQ : Nat.card Q' = Nat.card P' := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
    have h1 : Nat.card Q' = Nat.card (Q : Subgroup ↥Pt) :=
      Nat.card_congr ((Q : Subgroup ↥Pt).equivMapOfInjective Pt.subtype
        Pt.subtype_injective).symm.toEquiv
    have h2 : (Nat.card (proj X).ker).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (ker_proj_card hZ)
    rw [h1, Q.card_eq_multiplicity, hcardPt, hn,
      Nat.factorization_mul (Nat.card_pos.ne') (pow_ne_zero n hp.ne_zero), Finsupp.add_apply, h2,
      hp.factorization_pow, Finsupp.single_eq_same, zero_add]
  have hQ'le : Q'.map (proj X) ≤ P' := by
    rintro _ ⟨x, hx, rfl⟩
    exact hQ'Pt hx
  have hQ'eq : Q'.map (proj X) = P' := by
    refine Subgroup.eq_of_le_of_card_ge hQ'le ?_
    rw [N143.card_map_of_disjoint_ker (proj X) hdis]
    exact hcardQ.ge
  have hinj' : ∀ x ∈ Q', ∀ y ∈ Q', proj X x = proj X y → x = y := by
    intro x hx y hy hxy
    have hmem : x⁻¹ * y ∈ Q' ⊓ (proj X).ker :=
      Subgroup.mem_inf.2 ⟨Q'.mul_mem (Q'.inv_mem hx) hy,
        MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    have h1 : x⁻¹ * y = 1 := Subgroup.disjoint_def.1 hdis (Subgroup.mem_inf.1 hmem).1
      (Subgroup.mem_inf.1 hmem).2
    exact inv_mul_eq_one.1 h1
  have hQ'el : IsElementaryAbelian p Q' := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      apply hinj' _ (Q'.mul_mem a.2 b.2) _ (Q'.mul_mem b.2 a.2)
      have ha : proj X (a : ↥X) ∈ P' := hQ'le ⟨a, a.2, rfl⟩
      have hb : proj X (b : ↥X) ∈ P' := hQ'le ⟨b, b.2, rfl⟩
      have := congrArg Subtype.val ((IsMulCommutative.is_comm (M := P')).comm
        ⟨proj X (a : ↥X), ha⟩ ⟨proj X (b : ↥X), hb⟩)
      simpa using this
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      apply Subtype.ext
      apply hinj' _ (Q'.pow_mem x.2 p) 1 Q'.one_mem
      have hx : proj X (x : ↥X) ∈ P' := hQ'le ⟨x, x.2, rfl⟩
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (A := P') _ hx
  refine ⟨Q'.map X.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h hh
    exact ⟨⟨h, hHX hh⟩, hHQ' hh, rfl⟩
  · have := hQ'el
    exact IsElementaryAbelian.map_subtype
  · unfold bar
    have h1 : (Q'.map X.subtype).subgroupOf X = Q' :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q'
    rw [h1]
    exact hQ'eq

theorem eq_one_of_central_pow (hp : p.Prime) (hZ : NoZ p X) {z : ↥X}
    (hzc : z ∈ Subgroup.center ↥X) (hz : z ^ p = 1) : z = 1 := by
  have h3 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hz
  have h4 : orderOf z ∣ Nat.card (Subgroup.center ↥X) := Subgroup.orderOf_dvd_natCard _ hzc
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥X)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 hZ
  have h5 : orderOf z ∣ Nat.gcd p (Nat.card (Subgroup.center ↥X)) := Nat.dvd_gcd h3 h4
  rw [hcop] at h5
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h5)

theorem le_centralizer_of_bar_le (hp : p.Prime) (hZ : NoZ p X) {A P : Subgroup G} (hAX : A ≤ X)
    (hPX : P ≤ X) (hA : ∀ a ∈ A, a ^ p = 1)
    (h : bar X P ≤ Subgroup.centralizer ((bar X A : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
      Set (↥X ⧸ Subgroup.center ↥X))) : P ≤ Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hxP : proj X ⟨x, hPX hx⟩ ∈ bar X P := ⟨⟨x, hPX hx⟩, hx, rfl⟩
  have haA : proj X ⟨a, hAX ha⟩ ∈ bar X A := ⟨⟨a, hAX ha⟩, ha, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 (h hxP) _ haA
  have hap : (⟨a, hAX ha⟩ : ↥X) ^ p = 1 := Subtype.ext (hA a ha)
  have hc : (⟨x, hPX hx⟩ : ↥X) * ⟨a, hAX ha⟩ * ⟨x, hPX hx⟩⁻¹ * ⟨a, hAX ha⟩⁻¹ ∈
      Subgroup.center ↥X := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥X), MonoidHom.mem_ker]
    simp only [map_mul, map_inv, QuotientGroup.mk'_apply] at hcomm ⊢
    rw [← hcomm]
    group
  have h1 := commutator_eq_one_of_central hp hZ hap hc
  have h2 : (⟨x, hPX hx⟩ : ↥X) * ⟨a, hAX ha⟩ = ⟨a, hAX ha⟩ * ⟨x, hPX hx⟩ := by
    calc (⟨x, hPX hx⟩ : ↥X) * ⟨a, hAX ha⟩
        = ((⟨x, hPX hx⟩ : ↥X) * ⟨a, hAX ha⟩ * ⟨x, hPX hx⟩⁻¹ * ⟨a, hAX ha⟩⁻¹) *
          (⟨a, hAX ha⟩ * ⟨x, hPX hx⟩) := by group
      _ = ⟨a, hAX ha⟩ * ⟨x, hPX hx⟩ := by rw [h1, one_mul]
  exact (congrArg Subtype.val h2).symm

theorem bar_maximal [Finite G] (hp : p.Prime) (hZ : NoZ p X) {A₀ F : Subgroup G} (hFX : F ≤ X)
    (hF : IsElementaryAbelian p F) (hA₀F : A₀ ≤ F)
    (hmax : ∀ F' : Subgroup G, F' ≤ X → IsElementaryAbelian p F' →
      F' ≤ Subgroup.centralizer (A₀ : Set G) → F ≤ F' → F' = F)
    {P' : Subgroup (↥X ⧸ Subgroup.center ↥X)} (hP' : IsElementaryAbelian p P')
    (hFP : bar X F ≤ P')
    (hC : P' ≤ Subgroup.centralizer ((bar X A₀ : Subgroup (↥X ⧸ Subgroup.center ↥X)) :
      Set (↥X ⧸ Subgroup.center ↥X))) : P' = bar X F := by
  obtain ⟨P, hPX, hFPle, hPel, hPbar⟩ := exists_lift_of_le hp hZ hFX hF hP' hFP
  have hA : ∀ a ∈ A₀, a ^ p = 1 := fun a ha => by
    have := hF
    exact elemPow_eq_one_of_isElementaryAbelian (A := F) a (hA₀F ha)
  have hPC : P ≤ Subgroup.centralizer (A₀ : Set G) :=
    le_centralizer_of_bar_le hp hZ (hA₀F.trans hFX) hPX hA (hPbar ▸ hC)
  have hPF : P = F := hmax P hPX hPel hPC hFPle
  rw [← hPbar, hPF]

theorem conj_mem_of_bar (hp : p.Prime) (hZ : NoZ p X) {F : Subgroup G}
    (hF : ∀ f ∈ F, f ^ p = 1) {xt : ↥X}
    (hy : ∀ h : ↥X ⧸ Subgroup.center ↥X, h ∈ bar X F →
      proj X xt * h * (proj X xt)⁻¹ ∈ bar X F)
    {f : ↥X} (hf : (f : G) ∈ F) : ((xt * f * xt⁻¹ : ↥X) : G) ∈ F := by
  have hfF : proj X f ∈ bar X F := ⟨f, hf, rfl⟩
  obtain ⟨f'', hf''F, hf''⟩ := hy _ hfF
  have hf''F' : (f'' : G) ∈ F := hf''F
  have hu : proj X (xt * f * xt⁻¹) = proj X f'' := by
    rw [hf'']
    simp
  have hzmem : (xt * f * xt⁻¹) * f''⁻¹ ∈ Subgroup.center ↥X := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center ↥X), MonoidHom.mem_ker, map_mul, map_inv, hu,
      mul_inv_cancel]
  set z := (xt * f * xt⁻¹) * f''⁻¹ with hzdef
  have hfp : f ^ p = 1 := Subtype.ext (hF _ hf)
  have hf''p : f'' ^ p = 1 := Subtype.ext (hF _ hf''F')
  have hup : (xt * f * xt⁻¹) ^ p = 1 := by rw [conj_pow, hfp]; group
  have huz : xt * f * xt⁻¹ = z * f'' := by rw [hzdef]; group
  have hzcomm : Commute z f'' := (Subgroup.mem_center_iff.1 hzmem f'').symm
  have hzp : z ^ p = 1 := by
    rw [huz, hzcomm.mul_pow, hf''p, mul_one] at hup
    exact hup
  have hz1 : z = 1 := eq_one_of_central_pow hp hZ hzmem hzp
  have : xt * f * xt⁻¹ = f'' := by
    rw [huz, hz1, one_mul]
  rw [this]
  exact hf''F'

theorem torusWeyl_bar_le [Finite G] (hp : p.Prime) (hZ : NoZ p X) {F : Subgroup G} (hFX : F ≤ X)
    (hF : IsElementaryAbelian p F) :
    torusWeyl (bar X F) ≤ (torusImage F X).map
      (MulAut.congr (barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F))).toMonoidHom := by
  have : Fact p.Prime := ⟨hp⟩
  have := hF
  have hFp : ∀ f ∈ F, f ^ p = 1 := fun f hf => elemPow_eq_one_of_isElementaryAbelian (A := F) f hf
  intro w hw
  obtain ⟨⟨y, hy⟩, rfl⟩ := hw
  obtain ⟨xt, rfl⟩ := QuotientGroup.mk_surjective y
  have hyN := Subgroup.mem_normalizer_iff.1 hy
  have hy1 : ∀ h : ↥X ⧸ Subgroup.center ↥X, h ∈ bar X F →
      proj X xt * h * (proj X xt)⁻¹ ∈ bar X F := fun h hh => (hyN h).1 hh
  have hy2 : ∀ h : ↥X ⧸ Subgroup.center ↥X, h ∈ bar X F →
      proj X xt⁻¹ * h * (proj X xt⁻¹)⁻¹ ∈ bar X F := by
    intro h hh
    have h1 : (proj X xt)⁻¹ * h * proj X xt ∈ bar X F := by
      refine (hyN _).2 ?_
      have e : proj X xt * ((proj X xt)⁻¹ * h * proj X xt) * (proj X xt)⁻¹ = h := by group
      show proj X xt * ((proj X xt)⁻¹ * h * proj X xt) * (proj X xt)⁻¹ ∈ bar X F
      rw [e]
      exact hh
    rw [map_inv, inv_inv]
    exact h1
  have hxN : (xt : G) ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      exact conj_mem_of_bar hp hZ hFp hy1 (f := ⟨g, hFX hg⟩) hg
    · intro hg
      have h1 := conj_mem_of_bar hp hZ hFp hy2 (f := ⟨(xt : G) * g * (xt : G)⁻¹, hFX hg⟩) hg
      have e : ((xt⁻¹ * ⟨(xt : G) * g * (xt : G)⁻¹, hFX hg⟩ * xt⁻¹⁻¹ : ↥X) : G) = g := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rwa [e] at h1
  have hnX : (⟨(xt : G), hxN⟩ : Subgroup.normalizer (F : Set G)) ∈
      X.subgroupOf (Subgroup.normalizer (F : Set G)) := xt.2
  refine ⟨F.normalizerMonoidHom ⟨(xt : G), hxN⟩, ⟨⟨(xt : G), hxN⟩, hnX, rfl⟩, ?_⟩
  apply MulEquiv.ext
  intro b
  obtain ⟨f, rfl⟩ := (barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F)).surjective b
  apply Subtype.ext
  have h1 : ((MulAut.congr (barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F))).toMonoidHom
      (F.normalizerMonoidHom ⟨(xt : G), hxN⟩))
      (barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F) f) =
      barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F)
        (F.normalizerMonoidHom ⟨(xt : G), hxN⟩ f) := by
    simp [MulAut.congr_apply]
  rw [h1]
  have hL : ((barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F)
      (F.normalizerMonoidHom ⟨(xt : G), hxN⟩ f) : bar X F) : ↥X ⧸ Subgroup.center ↥X) =
      proj X (xt * ⟨(f : G), hFX f.2⟩ * xt⁻¹) := by
    rw [coe_barEquiv]
    rfl
  have hR : (((bar X F).normalizerMonoidHom ⟨(proj X xt), hy⟩
      (barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F) f) : bar X F) :
        ↥X ⧸ Subgroup.center ↥X) =
      proj X xt * proj X ⟨(f : G), hFX f.2⟩ * (proj X xt)⁻¹ := by
    change proj X xt * ((barEquiv hp hZ hFX (IsElementaryAbelian.isPGroup p F) f : bar X F) :
      ↥X ⧸ Subgroup.center ↥X) * (proj X xt)⁻¹ = _
    rw [coe_barEquiv]
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [map_mul, map_mul, map_inv]

end

end CFSG.RankThree.PartOne.Q1327C
