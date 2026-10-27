module

public import CFSG.Quasithin.H13.L32NLem14332c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped commutatorElement

namespace L14332

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g a : G}
  {D : HatModelU (fsuU T V)}

theorem Ctx14332.comm_center (C : Ctx14332 G T L V V₂ g a D) :
    ∀ u ∈ fsuU T V, ∀ w ∈ fsuU T V, u * w * u⁻¹ * w⁻¹ ∈ centerOf (fsuU T V) := fun u hu w hw =>
  C.lt.le (by simpa [commutatorElement_def] using C.comm u hu w hw)

theorem Ctx14332.rho_U (C : Ctx14332 G T L V V₂ g a D) {u : G} (hu : u ∈ fsuU T V)
    (hN : u ∈ Subgroup.normalizer (fsuU T V : Set G)) : D.ρ ⟨u, hN⟩ = 1 :=
  L128A.HatU.rho_eq_one_of_mem D C.comm_center hu hN

omit [Finite G] in
theorem conj_mem_l32nW {k w : G} (hkH : k ∈ l32nH T V)
    (hkC : k ∈ Subgroup.centralizer (V₂ : Set G)) (hw : w ∈ l32nW T V V₂) :
    k * w * k⁻¹ ∈ l32nW T V V₂ := by
  obtain ⟨hwU, hwC⟩ := Subgroup.mem_inf.mp hw
  refine Subgroup.mem_inf.mpr ⟨conj_mem_fsuU hkH hwU, ?_⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hkC hwC) (Subgroup.inv_mem _ hkC)

omit [Finite G] in
theorem conj_mem_l32nE {k e : G} (hV₁₂ : fsuV1 T V ≤ V₂)
    (hgN : g ∈ Subgroup.normalizer (V₂ : Set G)) (hkH : k ∈ l32nH T V)
    (hkC : k ∈ Subgroup.centralizer (V₂ : Set G)) (he : e ∈ l32nE T V V₂ g) :
    k * e * k⁻¹ ∈ l32nE T V V₂ g := by
  obtain ⟨heW, heWg⟩ := Subgroup.mem_inf.mp he
  refine Subgroup.mem_inf.mpr ⟨conj_mem_l32nW hkH hkC heW, ?_⟩
  have hgkC : g * k * g⁻¹ ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V₂ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) v).mp hv
    have hc := Subgroup.mem_centralizer_iff.mp hkC _ hv'
    simp only [inv_inv] at hc
    calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
      _ = g * k * g⁻¹ * v := by group
  have hgkH : g * k * g⁻¹ ∈ l32nH T V :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hV₁₂ hgkC)
  obtain ⟨w, hw, rfl⟩ := heWg
  have := conj_mem_l32nW hgkH hgkC hw
  refine ⟨g * k * g⁻¹ * w * (g * k * g⁻¹)⁻¹, this, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  group

theorem Ctx14332.maps_hatE_of_centralizer (C : Ctx14332 G T L V V₂ g a D) {k : G}
    (hkH : k ∈ l32nH T V) (hkC : k ∈ Subgroup.centralizer (V₂ : Set G))
    (hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    ∀ v ∈ D.hat (l32nE T V V₂ g), D.ρ ⟨k, hkN⟩ v ∈ D.hat (l32nE T V V₂ g) := by
  have hgN : g ∈ Subgroup.normalizer (V₂ : Set G) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp C.gP.2 V₂) ⟨2, le_rfl, C.plane.1⟩
  intro v hv
  have hle : D.hat (l32nE T V V₂ g) ≤
      (D.hat (l32nE T V V₂ g)).comap (D.ρ ⟨k, hkN⟩).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨heE, heU⟩ := Subgroup.mem_inf.mp he
    show D.ρ ⟨k, hkN⟩ (D.π e) ∈ D.hat (l32nE T V V₂ g)
    rw [D.ρ_π ⟨k, hkN⟩ e heU]
    exact Submodule.subset_span ⟨k * e * k⁻¹, Subgroup.mem_inf.mpr
      ⟨conj_mem_l32nE C.plane.2 hgN hkH hkC heE, conj_mem_fsuU hkH heU⟩, rfl⟩
  exact hle hv

theorem Ctx14332.exists_mul_centralizer (C : Ctx14332 G T L V V₂ g a D) {h : G}
    (hh : h ∈ l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)) :
    ∃ u ∈ fsuU T V, ∃ k ∈ l32nH T V, k ∈ Subgroup.centralizer (V₂ : Set G) ∧ h = u * k := by
  obtain ⟨hhH, hhV₂⟩ := Subgroup.mem_inf.mp hh
  have hkcen : ∀ k ∈ l32nH T V, k * a * k⁻¹ = a → k ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro k hk hka
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases C.V₂_cases x hx with hx1 | ⟨c, hc, rfl⟩
    · have := C.H_V1 k hk x hx1
      calc x * k = (k * x * k⁻¹) * k := by rw [this]
        _ = k * x := by group
    · have hc' := C.H_V1 k hk c hc
      calc a * c * k = (k * a * k⁻¹) * (k * c * k⁻¹) * k := by rw [hka, hc']
        _ = k * (a * c) := by group
  have hha : h * a * h⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hhV₂ a).mp C.aV₂
  rcases C.V₂_cases _ hha with h1 | ⟨c, hc, hca⟩
  · exfalso
    apply C.a1
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhH) _).mp h1
    rwa [show h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a by group] at this
  by_cases hc1 : c = 1
  · exact ⟨1, (fsuU T V).one_mem, h, hhH, hkcen h hhH (by rw [hca, hc1, mul_one]), by group⟩
  have haZ : a ∉ centerOf (fsuU T V) := fun hm =>
    C.pi_ne ((L128A.HatU.π_eq_zero_iff D C.aU).mpr hm)
  obtain ⟨u, huU, hua⟩ : ∃ u ∈ fsuU T V, u * a ≠ a * u := by
    by_contra hne
    push Not at hne
    exact haZ (Subgroup.mem_inf.mpr ⟨C.aU, Subgroup.mem_centralizer_iff.mpr fun u hu =>
      hne u hu⟩)
  have huc : ⁅u, a⁆ = c := by
    have hmem := C.comm u huU a C.aU
    have hne1 : ⁅u, a⁆ ≠ 1 := by
      rw [Ne, commutatorElement_eq_one_iff_mul_comm]; exact hua
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp C.card_V1
    have e1 := hy ⟨_, hmem⟩ (fun h0 => hne1 (congrArg Subtype.val h0))
    have e2 := hy ⟨c, hc⟩ (fun h0 => hc1 (congrArg Subtype.val h0))
    exact congrArg Subtype.val (e1.trans e2.symm)
  have hcZ : c ∈ centerOf (fsuU T V) := C.lt.le hc
  have hcc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcZ).2
  have hua' : u * a * u⁻¹ = c * a := by
    calc u * a * u⁻¹ = (u * a * u⁻¹ * a⁻¹) * a := by group
      _ = c * a := by rw [← huc, commutatorElement_def]
  have huH : u ∈ l32nH T V := C.U_le huU
  refine ⟨u, huU, u⁻¹ * h, (l32nH T V).mul_mem ((l32nH T V).inv_mem huH) hhH,
    hkcen _ ((l32nH T V).mul_mem ((l32nH T V).inv_mem huH) hhH) ?_, by group⟩
  calc (u⁻¹ * h) * a * (u⁻¹ * h)⁻¹ = u⁻¹ * (h * a * h⁻¹) * u := by group
    _ = u⁻¹ * (a * c) * u := by rw [hca]
    _ = u⁻¹ * (c * a) * u := by rw [hcc a C.aU]
    _ = u⁻¹ * (u * a * u⁻¹) * u := by rw [hua']
    _ = a := by group

theorem Ctx14332.maps_hatE (C : Ctx14332 G T L V V₂ g a D) {h : G}
    (hh : h ∈ l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G))
    (hN : h ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    ∀ v ∈ D.hat (l32nE T V V₂ g), D.ρ ⟨h, hN⟩ v ∈ D.hat (l32nE T V V₂ g) := by
  obtain ⟨u, huU, k, hkH, hkC, rfl⟩ := C.exists_mul_centralizer hh
  have hkN : k ∈ Subgroup.normalizer (fsuU T V : Set G) := l32nH_le_normalizer_fsuU T V hkH
  have huN : u ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    l32nH_le_normalizer_fsuU T V (C.U_le huU)
  have hρ : D.ρ ⟨u * k, hN⟩ = D.ρ ⟨k, hkN⟩ := by
    have e : (⟨u * k, hN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨u, huN⟩ * ⟨k, hkN⟩ :=
      rfl
    rw [e, map_mul, C.rho_U huU huN, one_mul]
  rw [hρ]
  exact C.maps_hatE_of_centralizer hkH hkC hkN

omit [Finite G] in
theorem zU_comm (U : Subgroup G) : ∀ x ∈ centerOf U, ∀ y ∈ centerOf U, x * y = y * x := by
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hy).2 x (Subgroup.mem_inf.mp hx).1)

theorem frattiniOf_eq_bot_of_sq {Z : Subgroup G} (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hsq : ∀ y ∈ Z, y * y = 1) : frattiniOf Z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hel : CFSG.IsElementaryAbelian 2 ↥Z :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hZab x x.2 y y.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun y => Subtype.ext (by
        simpa [pow_two] using hsq y y.2) }
  have : Fact (IsPGroup 2 ↥Z) := ⟨CFSG.IsElementaryAbelian.isPGroup 2 ↥Z⟩
  rw [frattiniOf, CFSG.frattini_eq_bot_of_isElementaryAbelian (p := 2), Subgroup.map_bot]

theorem Ctx14332.card_le_of_elem (h1288 : Lemma12_8_8_two) (hKG : KGSp4Quad)
    (C : Ctx14332 G T L V V₂ g a D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hsq : ∀ y ∈ centerOf (fsuU T V), y * y = 1) :
    Nat.card ↥(D.img (l32nH T V)) ≤ 120 := by
  obtain ⟨-, -, -, hq⟩ := h1288 G T L V 3 (fsuV1 T V) V₂ C.setting D
  obtain ⟨q, -, hpol, hinv⟩ := hq (frattiniOf_eq_bot_of_sq (zU_comm _) hsq)
  refine hKG D.V D.B (L128A.HatU.B_isAlt D) (L128A.HatU.B_nondegenerate D) hd _ ?_ q hpol hinv
  intro γ hγ v w
  obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w

@[expose] def omegaOneOf (Z : Subgroup G) (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) :
    Subgroup G where
  carrier := {y | y ∈ Z ∧ y * y = 1}
  one_mem' := ⟨Z.one_mem, mul_one 1⟩
  mul_mem' := by
    rintro x y ⟨hx, hxx⟩ ⟨hy, hyy⟩
    refine ⟨Z.mul_mem hx hy, ?_⟩
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hZab y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [hxx, hyy, one_mul]
  inv_mem' := by
    rintro x ⟨hx, hxx⟩
    refine ⟨Z.inv_mem hx, ?_⟩
    rw [← mul_inv_rev, hxx, inv_one]

omit [Finite G] in
theorem mem_omegaOneOf {Z : Subgroup G} {hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x} {y : G} :
    y ∈ omegaOneOf Z hZab ↔ y ∈ Z ∧ y * y = 1 := Iff.rfl

theorem card_omegaOneOf {Z V₁ : Subgroup G} (hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x)
    (hV1 : Nat.card V₁ = 2) (hsq : ∀ y ∈ Z, y * y ∈ V₁) (hne : ∃ y ∈ Z, y * y ≠ 1) :
    Nat.card ↥(omegaOneOf Z hZab) * 2 = Nat.card Z := by
  let σ : ↥Z →* ↥V₁ :=
    { toFun := fun y => ⟨(y : G) * y, hsq y y.2⟩
      map_one' := Subtype.ext (mul_one 1)
      map_mul' := fun x y => Subtype.ext (by
        show (x : G) * y * (x * y) = (x * x) * (y * y)
        calc (x : G) * y * (x * y) = x * (y * x) * y := by group
          _ = x * (x * y) * y := by rw [hZab y y.2 x x.2]
          _ = (x * x) * (y * y) := by group) }
  have hker : σ.ker = (omegaOneOf Z hZab).subgroupOf Z := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact ⟨y.2, congrArg Subtype.val h1⟩
    · intro h1
      exact Subtype.ext h1.2
  have hrange : σ.range = ⊤ := by
    obtain ⟨y, hy, hyy⟩ := hne
    have hmem : (⟨y * y, hsq y hy⟩ : ↥V₁) ∈ σ.range := ⟨⟨y, hy⟩, rfl⟩
    have hne' : σ.range ≠ ⊥ := fun h0 => by
      rw [h0, Subgroup.mem_bot] at hmem
      exact hyy (congrArg Subtype.val hmem)
    have := Subgroup.card_le_card_group σ.range
    rw [hV1] at this
    have h2 : Nat.card σ.range ≠ 1 := fun h1 => hne' (Subgroup.card_eq_one.mp h1)
    have hpos : 0 < Nat.card σ.range := Nat.card_pos
    apply Subgroup.eq_top_of_card_eq
    rw [hV1]
    omega
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv, hrange, Subgroup.card_top,
    hV1, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (fun y hy => (mem_omegaOneOf.mp hy).1)).toEquiv] at h1
  omega

theorem Ctx14332.odd_centralizes_of_not_elem (C : Ctx14332 G T L V V₂ g a D)
    (hcard : Nat.card ↥(centerOf (fsuU T V)) = 4 ∨ Nat.card ↥(centerOf (fsuU T V)) = 8)
    (hne : ∃ y ∈ centerOf (fsuU T V), y * y ≠ 1) :
    ∀ h ∈ l32nH T V, Odd (orderOf h) → ∀ y ∈ centerOf (fsuU T V), h * y * h⁻¹ = y := by
  rcases hcard with h4 | h8
  · exact odd_centralizes_of_card_four C h4
  intro h hh hodd
  have hab := zU_comm (fsuU T V)
  have hsqV : ∀ y ∈ centerOf (fsuU T V), y * y ∈ fsuV1 T V := fun y hy =>
    C.sq y (Subgroup.mem_inf.mp hy).1
  have hΩ4 : Nat.card ↥(omegaOneOf (centerOf (fsuU T V)) hab) = 4 := by
    have := card_omegaOneOf hab C.card_V1 hsqV hne
    rw [h8] at this
    omega
  set Z := centerOf (fsuU T V) with hZ
  set Ω := omegaOneOf Z hab with hΩ
  have hV1Ω : fsuV1 T V ≤ Ω := fun c hc => mem_omegaOneOf.mpr ⟨C.lt.le hc, by
    have := pow_card_eq_one' (G := ↥(fsuV1 T V)) (x := ⟨c, hc⟩)
    rw [C.card_V1, pow_two] at this
    exact congrArg Subtype.val this⟩
  have hΩZ : Ω ≤ Z := fun y hy => (mem_omegaOneOf.mp hy).1
  have hhZ : h ∈ Subgroup.normalizer (Z : Set G) :=
    ((l32nH_le_normalizer_fsuU T V).trans (normalizer_le_normalizer_centerOf _)) hh
  have hhΩ : h ∈ Subgroup.normalizer (Ω : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hZy := Subgroup.mem_normalizer_iff.mp hhZ y
    rw [mem_omegaOneOf, mem_omegaOneOf]
    constructor
    · rintro ⟨hy, hyy⟩
      refine ⟨hZy.mp hy, ?_⟩
      calc h * y * h⁻¹ * (h * y * h⁻¹) = h * (y * y) * h⁻¹ := by group
        _ = 1 := by rw [hyy]; group
    · rintro ⟨hy, hyy⟩
      refine ⟨hZy.mpr hy, ?_⟩
      have : h * (y * y) * h⁻¹ = 1 := by
        calc h * (y * y) * h⁻¹ = h * y * h⁻¹ * (h * y * h⁻¹) := by group
          _ = 1 := hyy
      have e : y * y = h⁻¹ * (h * (y * y) * h⁻¹) * h := by group
      rw [e, this]
      group
  have hr1 : (fsuV1 T V).relIndex Ω = 2 := by
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := Ω)
    rw [inf_eq_left.mpr hV1Ω, C.card_V1, hΩ4] at this
    omega
  have hr2 : Ω.relIndex Z = 2 := by
    have := Subgroup.relIndex_mul_card (H := Ω) (K := Z)
    rw [inf_eq_left.mpr hΩZ, hΩ4, h8] at this
    omega
  have hfixΩ := conj_eq_of_odd_of_relIndex_two hr1 (e := 1) (fun c hc => by
    have := pow_card_eq_one' (G := ↥(fsuV1 T V)) (x := ⟨c, hc⟩)
    rw [C.card_V1] at this
    simpa using congrArg Subtype.val this) hhΩ (C.H_V1 h hh) hodd
  exact conj_eq_of_odd_of_relIndex_two hr2 (e := 1) (fun c hc => by
    rw [pow_one, pow_two]; exact (mem_omegaOneOf.mp hc).2) hhZ hfixΩ hodd

theorem not_case_iii (h1288 : Lemma12_8_8_two) (h14323 : Lemma14323Rest) (hKGq : KGSp4Quad)
    (hKGl : KGSp4Line)
    (C : Ctx14332 G T L V V₂ g a D) (hd : Module.finrank (ZMod 2) D.V = 4)
    (hiii : Case14323iii T V g D) : False := by
  have := finite_linearEquiv D
  have hH360 : 360 ≤ Nat.card ↥(D.img (l32nH T V)) := by
    rcases hiii.iso with he | he <;> obtain ⟨e⟩ := he
    · rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    · rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
  have hne : ∃ y ∈ centerOf (fsuU T V), y * y ≠ 1 := by
    by_contra hall
    push Not at hall
    have := C.card_le_of_elem h1288 hKGq hd hall
    omega
  have hcard : Nat.card ↥(centerOf (fsuU T V)) = 4 ∨ Nat.card ↥(centerOf (fsuU T V)) = 8 := by
    have := C.card_zU
    rcases hiii.card_zU with h2 | h4
    · left; omega
    · right; omega
  have hodd := C.odd_centralizes_of_not_elem hcard hne
  have hstab := stab_le C hodd
  obtain ⟨⟨hVE, hV4⟩, -, -, -⟩ := h14323 G T L V C.hyp V₂ g C.plane C.gP C.gN D hd
  have hiso : ∀ x ∈ D.hat V, ∀ y ∈ D.hat V, D.B x y = 0 := D.isotropic_hat C.V_U C.V_comm
  have hfin : Module.finrank (ZMod 2) ↥(D.hat V) = 2 := by
    have : Module.Finite (ZMod 2) ↥(D.hat V) := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hV4
    have h22 : (2 : ℕ) ^ Module.finrank (ZMod 2) ↥(D.hat V) = 2 ^ 2 := by rw [hV4]; norm_num
    exact Nat.pow_right_injective le_rfl h22
  have hπV : D.π a ∈ D.hat V := L128A.HatU.π_mem_hat D (C.plane.1.1 C.aV₂) C.aU
  have hB : ∀ γ ∈ D.img (l32nH T V), ∀ v w, D.B (γ v) (γ w) = D.B v w := by
    intro γ hγ v w
    obtain ⟨x, -, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact L128A.HatU.B_rho D ⟨x, hxN⟩ v w
  obtain ⟨γ, hγH, hγa, w, hw, hγw⟩ := hKGl D.V D.B (L128A.HatU.B_isAlt D)
    (L128A.HatU.B_nondegenerate D) hd _ hB hH360 (D.π a) C.pi_ne (D.hat V) hπV hfin hiso
  have hγS : γ ∈ D.img (l32nH T V) ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) :=
    Subgroup.mem_inf.mpr ⟨hγH, MulAction.mem_stabilizer_iff.mpr hγa⟩
  obtain ⟨h, hh, hN, rfl⟩ := (L128A.HatU.mem_img D).mp (hstab hγS)
  have hw' : w ∈ D.hat (l32nE T V V₂ g) := hVE ▸ hw
  have := C.maps_hatE hh hN w hw'
  rw [← hVE] at this
  exact hγw this

end L14332

end CFSG.Quasithin.H13
