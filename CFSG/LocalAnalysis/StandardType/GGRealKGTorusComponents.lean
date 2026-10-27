module

public import CFSG.LocalAnalysis.StandardType.GGRealKGTorusComponentsDefs
public import CFSG.LocalAnalysis.StandardType.GGRealQFour
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpJr
public import CFSG.LocalAnalysis.StandardType.GGRealKGModelRoot
public import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Bridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Subgroup

theorem ggReflRealizedIn_of_torusComponents {G : Type} [Group G] [Finite G] {p r : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hSC : ∀ g ∈ centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hNT : GGNoTransvection p Bs) (hX : commutator X = ⊤) {R : Type} [Group R]
    {I : Set (MulAut R)} (θ : X ⧸ center X ≃* R) (hBsN : Bs ≤ normalizer (X : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range) (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range)
    (hT : GGTorusComponents p r R I) : GGReflRealizedIn p Bs X := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro t htA ht
  have htI : t ∈ ggInduced X Bs := by
    rw [ggAutomizer_eq] at htA
    exact htA
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hX θ hBsN hBsI hr h3
  obtain ⟨n₀, hn₀, hov₀, hrefl₀, hmem₀⟩ := ggReflection_overGamma_of_induced hp hp2 hBs hBsN htI ht
  obtain ⟨n, hn, J', hW, hnφ, hnJ', hcomp, hpJ'⟩ :=
    hT X (ggQuotHom θ) (ggGamma X hBsN).range hTB _ hmem₀ hrefl₀
  obtain ⟨m, hg, htr, hover⟩ := exists_pow_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hBsN
    hW hn (hnφ ▸ hrefl₀)
  have hgX : (n : G) ^ m ∈ X := X.pow_mem n.2 m
  have hrt : t = ggConjAut Bs hg := by
    refine ggReflection_eq_of_agree_mod hp2 hBs hNT (Z := centralizer (X : Set G))
      ht htr ?_ ?_ ?_ ?_ ?_
    · obtain ⟨g', -, hg'N, hg'⟩ := htI
      exact ⟨g', trivial, hg'N, hg'⟩
    · exact ⟨(n : G) ^ m, trivial, hg, fun b => rfl⟩
    · obtain ⟨g', hg'X, -, hg'⟩ := htI
      intro b hb
      apply Subtype.ext
      rw [hg' b, mem_centralizer_iff.mp hb g' hg'X]
      group
    · intro b hb
      apply Subtype.ext
      rw [ggConjAut_apply Bs hg, mem_centralizer_iff.mp hb ((n : G) ^ m) hgX]
      group
    · intro b
      have h1 : (ggGamma X hBsN).rangeRestrict ((t b)⁻¹ * (ggConjAut Bs hg) b) = 1 := by
        rw [map_mul, map_inv, hov₀ b, hover b, ← hnφ]
        exact inv_mul_cancel _
      have h2 := (ggGamma_eq_one_iff X hBsN ((t b)⁻¹ * (ggConjAut Bs hg) b)).mp (by
        have := congrArg Subtype.val h1
        simpa using this)
      simpa using h2
  subst hrt
  have hmap := map_ggHypCent_eq hp hp2 hBs hBsN hn hgX hg htr.1 (hnφ ▸ hover)
  have hJc : CFSG.Assembly.IsComponentOf (J'.map X.subtype)
      (X ⊓ centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G)) :=
    hmap ▸ isComponentOf_map_of_injective X.subtype X.subtype_injective hcomp
  have hpJ : p ∣ Nat.card (J'.map X.subtype) := by
    rwa [Subgroup.card_map_of_injective X.subtype_injective]
  refine ⟨J'.map X.subtype, ⟨(n : G) ^ m, ⟨n ^ m, J'.pow_mem hnJ' m, by simp⟩, hg, fun b => rfl⟩,
    ?_⟩
  exact (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent hp).mpr
    ⟨hJc.1, isPComponent_subgroupOf_of_isComponentOf_of_dvd hJc hpJ⟩

theorem ggKGComponentDatumAt_of_componentCover {R : Type} [Group R] [Finite R]
    {p : ℕ} {E : Subgroup R} (hE : IsElemAbelian p E)
    {ι : Type} (m : ι → R) (J : ι → Subgroup R)
    (hmJ : ∀ i, m i ∈ J i)
    (hJcomp : ∀ i, CFSG.Assembly.IsComponentOf (J i)
      (Subgroup.centralizer ((E ⊓ Subgroup.centralizer ({m i} : Set R) : Subgroup R) : Set R)))
    (hdvd : ∀ i, p ∣ Nat.card (J i))
    (hcover : ∀ w₀ : R, GGKGIsReflAt p E w₀ →
      ∃ i, ∃ u ∈ Subgroup.normalizer (E : Set R),
        ∀ e ∈ E, w₀ * e * w₀⁻¹ =
          (u * m i * u⁻¹) * e * (u * m i * u⁻¹)⁻¹) :
    GGKGComponentDatumAt p E := by
  classical
  intro w₀ hrefl
  obtain ⟨i, u, huN, hwu⟩ := hcover w₀ hrefl
  set w : R := u * m i * u⁻¹ with hwdef
  set c : R ≃* R := MulAut.conj u with hcdef
  have hw_eq : w = c (m i) := by
    simp [hwdef, hcdef, MulAut.conj_apply]
  have hEN : E.map c.toMonoidHom = E := by
    simpa [hcdef] using Subgroup.mem_normalizer_iff_map_conj_eq.mp huN
  have hA_map : (E ⊓ Subgroup.centralizer ({m i} : Set R)).map c.toMonoidHom =
      E ⊓ Subgroup.centralizer ({w} : Set R) := by
    rw [CFSG.centralizer_inter_map c E (m i), hEN, ← hw_eq]
  have hcent_map :
      (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({m i} : Set R) : Subgroup R) : Set R)).map
        c.toMonoidHom =
      Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R) := by
    rw [CFSG.Glauberman.map_centralizer_eq_of_equiv c
      (E ⊓ Subgroup.centralizer ({m i} : Set R)), hA_map]
  have hJcomp' : CFSG.Assembly.IsComponentOf ((J i).map c.toMonoidHom)
      (Subgroup.centralizer
        ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)) := by
    have h := isComponentOf_map_of_injective c.toMonoidHom c.injective (hJcomp i)
    rwa [hcent_map] at h
  refine ⟨w, ?_, (J i).map c.toMonoidHom, ?_, hJcomp', ?_⟩
  · intro e he
    simpa [hwdef] using (hwu e he).symm
  · rw [hw_eq]
    exact Subgroup.mem_map_of_mem c.toMonoidHom (hmJ i)
  · rw [Subgroup.card_map_of_injective c.injective]
    exact hdvd i

theorem ggTorusComponents_of_componentDatum {p r : ℕ} {R : Type} [Group R] [Finite R]
    {I : Set (MulAut R)} (hp : p.Prime)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥)
    (hclosed : GGCentrallyClosed R) (h : GGKGComponentDatum p r R) :
    GGTorusComponents p r R I := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  intro L' _ _ ψ A hTB φ hφauto hφrefl
  obtain ⟨hψ, hker, hperf, hA, hAI, hr, h3, hsc⟩ := hTB
  have hψinj : Function.Injective ψ := hclosed L' ψ hψ hker hperf
  let Ψ : L' ≃* R := MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩
  have hψsymm : ∀ x : R, ψ (Ψ.symm x) = x := fun x => MulEquiv.apply_symm_apply Ψ x
  let Λ : R →* MulAut L' := (MulAut.conj : L' →* MulAut L').comp Ψ.symm.toMonoidHom
  have hΛeq : ∀ e : R, Λ e = MulAut.conj (Ψ.symm e) := fun e => rfl
  have hZL : Subgroup.center L' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    apply hψinj
    rw [map_one]
    have hzc : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, hz l]
    rw [hZ, Subgroup.mem_bot] at hzc
    exact hzc
  have hcinj : Function.Injective (MulAut.conj : L' →* MulAut L') := by
    intro x y hxy
    have hc : x⁻¹ * y ∈ Subgroup.center L' := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := congrArg (fun f : MulAut L' => f z) hxy
      simp only [MulAut.conj_apply] at h1
      calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
        _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
        _ = x⁻¹ * y * z := by group
    rw [hZL, Subgroup.mem_bot] at hc
    exact inv_mul_eq_one.mp hc
  have hΛinj : Function.Injective Λ := by
    intro e₁ e₂ h
    exact Ψ.symm.injective (hcinj h)
  have hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a := by
    intro a ha
    obtain ⟨φa, hφaI, hφa⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφaI
    refine ⟨e, MulEquiv.ext fun l => ?_⟩
    rw [hΛeq, MulAut.conj_apply]
    apply hψinj
    rw [map_mul, map_mul, map_inv, hψsymm e]
    simpa [MulAut.conj_apply] using hφa l
  set E : Subgroup R := A.comap Λ with hE
  have hΦmem : ∀ e : E, Λ (e : R) ∈ A := fun e => Subgroup.mem_comap.mp (hE ▸ e.2)
  let Φfun : E → A := fun e => (⟨Λ (e : R), hΦmem e⟩ : A)
  have hΦfun_val : ∀ e : E, (Φfun e : MulAut L') = Λ (e : R) := fun e => rfl
  have hΦbij : Function.Bijective Φfun := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective Φfun hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    have hgA : Λ g ∈ A := by
      have hconjA : MulAut.conj (Ψ.symm g) ∈ A := by
        refine hsc (Ψ.symm g) (fun a ha => ?_) ?_
        · obtain ⟨e, he⟩ := hAΛ a ha
          have heE : e ∈ E := Subgroup.mem_comap.mpr (show Λ e ∈ A from he ▸ ha)
          rw [← he, hΛeq, MulAut.conj_apply]
          apply hψinj
          rw [map_mul, map_mul, map_inv, hψsymm e, hψsymm g]
          rw [← hg e heE]
          group
        · apply hψinj
          rw [map_pow, hψsymm g, hgp, map_one]
      simpa [hΛeq] using hconjA
    exact Subgroup.mem_comap.mpr hgA
  have h3' : p ^ 3 ≤ Nat.card E := hcardE ▸ h3
  have hr' : p ^ r ≤ Nat.card E := hcardE ▸ hr
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hφauto
  have hφeq : φ = ggConjAut A hcN := MulEquiv.ext fun b => Subtype.ext (hvc b)
  set w₀ : R := ψ n with hw₀
  have hΛw0 : Λ w₀ = MulAut.conj n := by
    rw [hw₀, hΛeq]
    congr 1
    exact Ψ.symm_apply_apply n
  have hconj : ∀ e : R, Λ (w₀ * e * w₀⁻¹) =
      MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := by
    intro e
    rw [map_mul, map_mul, map_inv, hΛw0]
  have hnorm : w₀ ∈ Subgroup.normalizer (E : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mp (show Λ e ∈ A from he)
      rwa [← hconj e] at h2
    · intro he
      have h2 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A := by
        rw [← hconj e]
        exact he
      exact (Subgroup.mem_normalizer_iff.mp hcN (Λ e)).mpr h2
  have hinv : ∀ e ∈ E, w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹ = e := by
    intro e he
    refine hΛinj ?_
    have hconj2 : ggConjAut A hcN ^ 2 = 1 := by rw [← hφeq, hφrefl.1]
    have hpow : (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ = Λ e := by
      have h1 : (((ggConjAut A hcN ^ 2) ⟨Λ e, show Λ e ∈ A from he⟩ : ↥A) : MulAut L') = Λ e := by
        rw [hconj2]
        rfl
      rwa [ggConjAut_pow_apply A hcN 2 ⟨Λ e, show Λ e ∈ A from he⟩] at h1
    calc Λ (w₀ * (w₀ * e * w₀⁻¹) * w₀⁻¹)
        = MulAut.conj n * (MulAut.conj n * Λ e * (MulAut.conj n)⁻¹) *
            (MulAut.conj n)⁻¹ := by
          rw [map_mul, map_mul, hconj e, map_inv, hΛw0]
      _ = (MulAut.conj n) ^ 2 * Λ e * ((MulAut.conj n) ^ 2)⁻¹ := by
          rw [pow_two]
          group
      _ = Λ e := hpow
  have hfixcard : Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} * p = Nat.card E := by
    rw [show Nat.card {e : E // w₀ * (e : R) * w₀⁻¹ = e} =
        Nat.card {b : A // φ b = b} from
      Nat.card_congr (Equiv.subtypeEquiv
        (Equiv.ofBijective Φfun hΦbij) (fun e => ?_))]
    · rw [hφrefl.2, hcardE]
    · constructor
      · intro he
        apply Subtype.ext
        rw [Equiv.coe_ofBijective, hvc, hΦfun_val e, ← hconj (e : R), he]
      · intro hb
        have h1 : MulAut.conj n * Λ (e : R) * (MulAut.conj n)⁻¹ = Λ (e : R) := by
          have h2 := congrArg (fun b : ↥A => ((b : ↥A) : MulAut L')) hb
          rw [Equiv.coe_ofBijective] at h2
          rw [hvc, hΦfun_val e] at h2
          exact h2
        rw [← hconj (e : R)] at h1
        exact hΛinj h1
  have hreflE : GGKGIsReflAt p E w₀ := ⟨hnorm, hinv, hfixcard⟩
  obtain ⟨w, hw, J, hwJ, hJcomp, hpJ⟩ := h E hEab h3' hr' hscE w₀ hreflE
  set n' : L' := Ψ.symm w with hn'def
  have hψn' : ψ n' = w := hψsymm w
  have hΛw : Λ w = MulAut.conj n' := by rw [hΛeq, hn'def]

  have hψconj : ∀ (y : R) (l : L'), ψ (MulAut.conj (Ψ.symm y) l) = y * ψ l * y⁻¹ := by
    intro y l
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hψsymm y]
  have hHypCent : ggHypCent A n' = (Subgroup.centralizer
      ((E ⊓ Subgroup.centralizer ({w} : Set R) : Subgroup R) : Set R)).comap ψ := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro f hf
      obtain ⟨hfE, hfw⟩ := Subgroup.mem_inf.mp hf
      have hfw' : w * f = f * w := (Subgroup.mem_centralizer_singleton_iff.mp hfw).symm
      have hcommΛ : Λ w * Λ f = Λ f * Λ w := by
        rw [← map_mul, ← map_mul, hfw']
      have hxfix : x ∈ ggFix (Λ f) :=
        Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx (Λ f)) ⟨hfE, hcommΛ⟩
      have h1 : Λ f x = x := mem_ggFix.mp hxfix
      have h2 : f * ψ x * f⁻¹ = ψ x := by
        have h3 : ψ (Λ f x) = ψ x := by rw [h1]
        rw [hΛeq f] at h3
        rw [hψconj f x] at h3
        exact h3
      exact mul_inv_eq_iff_eq_mul.mp h2
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff] at hx
      rw [ggHypCent]
      refine Subgroup.mem_iInf.mpr fun a => Subgroup.mem_iInf.mpr fun ha => ?_
      obtain ⟨e, rfl⟩ := hAΛ a ha.1
      have heE : e ∈ E := ha.1
      have hwe : w * e = e * w := by
        have h0 : (MulAut.conj n' * Λ e) * (MulAut.conj n')⁻¹ = Λ e :=
          mul_inv_eq_iff_eq_mul.mpr ha.2
        have h1 : Λ (w * e * w⁻¹) = Λ e := by
          rw [map_mul, map_mul, map_inv, hΛw]
          exact h0
        exact mul_inv_eq_iff_eq_mul.mp (hΛinj h1)
      have heF : e ∈ E ⊓ Subgroup.centralizer ({w} : Set R) :=
        ⟨heE, Subgroup.mem_centralizer_singleton_iff.mpr hwe.symm⟩
      rw [mem_ggFix]
      change MulAut.conj (Ψ.symm e) x = x
      apply hψinj
      rw [hψconj e x]
      have hxe : e * ψ x = ψ x * e := hx e heF
      rw [hxe, mul_inv_cancel_right]
  have hcomap : ∀ C : Subgroup R, C.comap ψ = C.map Ψ.symm.toMonoidHom := by
    intro C
    ext y
    constructor
    · intro hy
      exact ⟨ψ y, hy, by
        change Ψ.symm (Ψ y) = y
        exact MulEquiv.symm_apply_apply Ψ y⟩
    · rintro ⟨c, hc, rfl⟩
      change ψ (Ψ.symm c) ∈ C
      rw [hψsymm c]
      exact hc
  have hJmap : IsComponentOf (J.map Ψ.symm.toMonoidHom) (ggHypCent A n') := by
    rw [hHypCent, hcomap]
    exact isComponentOf_map_of_injective Ψ.symm.toMonoidHom Ψ.symm.injective hJcomp
  have hpJmap : p ∣ Nat.card (J.map Ψ.symm.toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective Ψ.symm.injective]
  have hWElt : GGTorusWeylElt p A n' := by
    intro a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    let x : L' := Ψ.symm e
    have hψx : ψ x = e := hψsymm e
    have hxp : x ^ p = 1 := by
      apply hψinj
      rw [map_pow, hψx, hEab.2 e heE, map_one]
    set u : L' := n' * x * n'⁻¹ with hudef
    have hψu : ψ u = w * e * w⁻¹ := by
      rw [hudef, map_mul, map_mul, map_inv, hψn', hψx]
    have hup : u ^ p = 1 := by rw [hudef, conj_pow, hxp, mul_one, mul_inv_cancel]
    have hweMem : w * e * w⁻¹ ∈ E := by
      rw [hw e heE]
      exact (Subgroup.mem_normalizer_iff.mp hnorm e).mp heE
    have hψux : ψ (u * x⁻¹) = w * e * w⁻¹ * e⁻¹ := by
      rw [map_mul, map_inv, hψu, hψx]
    have hψuxE : ψ (u * x⁻¹) ∈ E := by
      rw [hψux]
      exact E.mul_mem hweMem (E.inv_mem heE)
    have hψuxMem : w * e * w⁻¹ * e⁻¹ ∈ E := by
      rw [← hψux]
      exact hψuxE
    have hcommψ : ψ x * ψ (u * x⁻¹) = ψ (u * x⁻¹) * ψ x := by
      rw [hψx, hψux]
      exact TableB.IsElemAbelian.comm hEab heE hψuxMem
    have hcx : x * (u * x⁻¹) = (u * x⁻¹) * x := by
      apply hψinj
      rw [map_mul ψ x (u * x⁻¹), map_mul ψ (u * x⁻¹) x, hcommψ]
    have hux : n' * ((Λ e) n')⁻¹ = u * x⁻¹ := by
      rw [hΛeq e, MulAut.conj_apply, hudef]
      dsimp only [x]
      group
    have huxp : (u * x⁻¹) ^ p = 1 := by
      have hc : Commute u x := by
        have h' : x * u * x⁻¹ = u := by simpa [mul_assoc] using hcx
        have hxu : x * u = u * x := by
          calc x * u = (x * u * x⁻¹) * x := by group
            _ = u * x := by rw [h']
        exact hxu.symm
      rw [(hc.inv_right).mul_pow, hup, inv_pow, hxp, inv_one, mul_one]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [hux, huxp]
    · obtain ⟨e', rfl⟩ := hAΛ a' ha'
      have he'E : e' ∈ E := ha'
      let x' : L' := Ψ.symm e'
      have hψx' : ψ x' = e' := hψsymm e'
      have hψuxE' : ψ (u * x⁻¹) ∈ E := hψuxE
      have hcommψ' : ψ x' * ψ (u * x⁻¹) = ψ (u * x⁻¹) * ψ x' := by
        rw [hψx']
        exact TableB.IsElemAbelian.comm hEab he'E hψuxE'
      have hcx' : x' * (u * x⁻¹) = (u * x⁻¹) * x' := by
        apply hψinj
        rw [map_mul ψ x' (u * x⁻¹), map_mul ψ (u * x⁻¹) x', hcommψ']
      rw [hux, hΛeq e', MulAut.conj_apply]
      calc x' * (u * x⁻¹) * x'⁻¹ = ((u * x⁻¹) * x') * x'⁻¹ := by rw [hcx']
        _ = u * x⁻¹ := by group
  refine ⟨n', ?_, J.map Ψ.symm.toMonoidHom, hWElt, ?_, ?_, hJmap, hpJmap⟩
  ·
    refine mem_normalizer_of_forall_conj_mem fun b hb => ?_
    obtain ⟨e, he⟩ := hAΛ b hb
    have heE : e ∈ E := show Λ e ∈ A from he ▸ hb
    have hwNorm : w ∈ Subgroup.normalizer (E : Set R) := by
      have hc : w₀⁻¹ * w ∈ Subgroup.centralizer (E : Set R) := by
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        have h := hw e he
        calc e * (w₀⁻¹ * w) = w₀⁻¹ * (w₀ * e * w₀⁻¹) * w := by group
          _ = w₀⁻¹ * (w * e * w⁻¹) * w := by rw [← h]
          _ = (w₀⁻¹ * w) * e := by group
      have h := Subgroup.mul_mem (Subgroup.normalizer (E : Set R)) hnorm
        (Subgroup.centralizer_le_normalizer (E : Set R) hc)
      simpa [mul_assoc] using h
    have hweMem : w⁻¹ * e * w ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hwNorm) e).mp heE
    have hmem : Λ (w⁻¹ * e * w) ∈ A := hΦmem ⟨w⁻¹ * e * w, hweMem⟩
    rw [map_mul, map_mul, map_inv, hΛw] at hmem
    rw [← he]
    exact hmem
  ·
    rw [show φ = ggConjAut A hcN from hφeq]
    refine MulEquiv.ext fun b => Subtype.ext ?_
    obtain ⟨e, he⟩ := hAΛ (b : MulAut L') b.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ b.2
    rw [ggConjAut_apply, ggConjAut_apply, ← he]
    have hconj' : MulAut.conj n' * Λ e * (MulAut.conj n')⁻¹ =
        MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := by
      calc MulAut.conj n' * Λ e * (MulAut.conj n')⁻¹
          = Λ (w * e * w⁻¹) := by rw [map_mul, map_mul, map_inv, hΛw]
        _ = Λ (w₀ * e * w₀⁻¹) := by rw [hw e heE]
        _ = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := hconj e
    exact hconj'
  · exact Subgroup.mem_map_of_mem Ψ.symm.toMonoidHom hwJ

end CFSG.StandardType

end
