module

public import CFSG.Quasithin.Background.AutOnPerfect
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Nat
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.C2Blocks
public import CFSG.Quasithin.Background.A4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.Ch4.T4213N

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative Matrix

theorem not_dvd_card_GL {n : ℕ} (hn : n ≤ 5) :
    ¬ 27 ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) =
      ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
    have h1 := Matrix.card_GL_field (𝔽 := ZMod 2) n
    rw [ZMod.card] at h1
    exact h1
  rw [h]
  interval_cases n <;> decide

theorem card_mulAut_vec (n : ℕ) :
    Nat.card (MulAut (Multiplicative (Fin n → ZMod 2))) =
      Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have e1 : MulAut (Multiplicative (Fin n → ZMod 2)) ≃ ((Fin n → ZMod 2) ≃+ (Fin n → ZMod 2)) :=
    AddEquiv.toMultiplicative.symm
  have e2 : ((Fin n → ZMod 2) ≃+ (Fin n → ZMod 2)) ≃
      ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) :=
    { toFun := fun f => { f.toAddMonoidHom.toZModLinearMap 2 with
        invFun := f.symm
        left_inv := f.left_inv
        right_inv := f.right_inv }
      invFun := fun f => f.toAddEquiv
      left_inv := fun f => by ext; rfl
      right_inv := fun f => by ext; rfl }
  have e3 : ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)) ≃
      Matrix.GeneralLinearGroup (Fin n) (ZMod 2) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n → ZMod 2)).symm.toEquiv.trans
      Matrix.GeneralLinearGroup.toLin.symm.toEquiv
  exact Nat.card_congr ((e1.trans e2).trans e3)

variable {P : Type*} [CommGroup P] [Finite P]

theorem nonempty_mulEquiv_vec (hP : ∀ x : P, x ^ 2 = 1) {n : ℕ} (hcard : Nat.card P = 2 ^ n) :
    Nonempty (P ≃* Multiplicative (Fin n → ZMod 2)) := by
  have hA : ∀ x : Additive P, (2 : ℕ) • x = 0 := fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, hP]
    rfl
  let _ : Module (ZMod 2) (Additive P) := AddCommGroup.zmodModule hA
  let _ : Fintype (Additive P) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive P) = n := by
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive P)
    rw [ZMod.card, ← Nat.card_eq_fintype_card, ← Nat.card_congr Additive.ofMul, hcard] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  exact ⟨AddEquiv.toMultiplicativeRight
    (Module.finBasisOfFinrankEq (ZMod 2) (Additive P) hfin).equivFun.toAddEquiv⟩

theorem not_dvd_card_of_le (hP : ∀ x : P, x ^ 2 = 1) (hcard : Nat.card P ≤ 32)
    (A : Subgroup (MulAut P)) : ¬ 27 ∣ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 P := fun x => ⟨1, by rw [pow_one]; exact hP x⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
  have hn5 : n ≤ 5 := by
    by_contra h
    have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨e⟩ := nonempty_mulEquiv_vec hP hn
  intro h27
  apply not_dvd_card_GL hn5
  rw [← card_mulAut_vec, ← Nat.card_congr (MulAut.congr e).toEquiv]
  exact h27.trans (Subgroup.card_subgroup_dvd_card A)

section Sections

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem sec_pow_two (hV : ∀ v : V, v ^ 2 = 1) (W U : Subgroup V) : ∀ x : Sec W U, x ^ 2 = 1 := by
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← QuotientGroup.mk_pow]
  have : w ^ 2 = 1 := Subtype.ext (by simpa using hV (w : V))
  rw [this, QuotientGroup.mk_one]

theorem not_dvd_index_centSec (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    {W U : Subgroup V} (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U)
    (hcard : Nat.card (Sec W U) ≤ 32) :
    ¬ 27 ∣ ((A ⊓ centSec W U).subgroupOf A).index := by
  have h1 := card_autSec_mul hAW hAU
  have h2 := Subgroup.card_mul_index ((A ⊓ centSec W U).subgroupOf A)
  have h3 : Nat.card ((A ⊓ centSec W U).subgroupOf A) = Nat.card ↥(A ⊓ centSec W U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h3] at h2
  have hpos : 0 < Nat.card ↥(A ⊓ centSec W U) := Nat.card_pos
  have hidx : ((A ⊓ centSec W U).subgroupOf A).index = Nat.card (autSec A W U) := by
    have h4 : Nat.card ↥(A ⊓ centSec W U) * ((A ⊓ centSec W U).subgroupOf A).index =
        Nat.card ↥(A ⊓ centSec W U) * Nat.card (autSec A W U) := by
      rw [h2, ← h1, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hpos h4
  rw [hidx]
  exact not_dvd_card_of_le (sec_pow_two hV W U) hcard _

omit [Finite V] in
theorem sq_eq_one_of_cent (hV : ∀ v : V, v ^ 2 = 1) {W : Subgroup V} {a : MulAut V}
    (h1 : ∀ v : V, a v * v⁻¹ ∈ W) (h2 : ∀ w ∈ W, a w = w) : a ^ 2 = 1 := by
  ext v
  set d := a v * v⁻¹ with hd
  have hav : a v = d * v := by rw [hd, inv_mul_cancel_right]
  have hda : a d = d := h2 d (h1 v)
  have hd2 : d * d = 1 := by rw [← sq, hV]
  show a (a v) = v
  rw [hav, map_mul, hda, hav, ← mul_assoc, hd2, one_mul]

omit [Finite V] in
theorem pow_four_eq_one_of_cent (hV : ∀ v : V, v ^ 2 = 1) {C W : Subgroup V}
    {a : MulAut V} (h1 : ∀ v : V, a v * v⁻¹ ∈ W) (h2 : ∀ w ∈ W, a w * w⁻¹ ∈ C)
    (h3 : ∀ c ∈ C, a c = c) : a ^ 4 = 1 := by
  have hb2 : ∀ w ∈ W, (a ^ 2) w = w := by
    intro w hw
    set e := a w * w⁻¹ with he
    have haw : a w = e * w := by rw [he, inv_mul_cancel_right]
    have hea : a e = e := h3 e (h2 w hw)
    have he2 : e * e = 1 := by rw [← sq, hV]
    show a (a w) = w
    rw [haw, map_mul, hea, haw, ← mul_assoc, he2, one_mul]
  have hb1 : ∀ v : V, (a ^ 2) v * v⁻¹ ∈ W := by
    intro v
    have hb : (a ^ 2) v = a (a v) := rfl
    rw [hb]
    have h4 := h1 (a v)
    have h5 := h1 v
    have e : a (a v) * v⁻¹ = (a (a v) * (a v)⁻¹) * (a v * v⁻¹) := by group
    rw [e]
    exact W.mul_mem h4 h5
  have := sq_eq_one_of_cent hV hb1 hb2
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, this]

end Sections

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem autOn_le_stabSub {X V W : Subgroup G} [IsMulCommutative ↥V]
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) : autOn X V ≤ stabSub (W.subgroupOf V) := by
  intro φ hφ
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  intro u
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Setup.coe_conjAct_apply]
  exact (Subgroup.mem_normalizer_iff.mp (hXW hg) u).symm

omit [Finite G] in
theorem relIndex_comap {X V : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (N : Subgroup ↥(autOn X V)) :
    ((N.comap (rhoAut hXV)).map X.subtype).relIndex X = N.index := by
  rw [Subgroup.relIndex]
  show (((N.comap (rhoAut hXV)).map X.subtype).comap X.subtype).index = N.index
  rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective,
    Subgroup.index_comap_of_surjective N (rhoAut_surjective hXV)]

theorem eq_bot_of_perfect_of_isPGroup {Γ : Type*} [Group Γ] [Finite Γ] {K : Subgroup Γ}
    (hK : ⁅K, K⁆ = K) (h2 : IsPGroup 2 ↥K) : K = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hne
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hK
  exact Group.IsPerfect.not_isNilpotent ↥K h2.isNilpotent

omit [Finite G] in
theorem centSec_normal {V : Type*} [CommGroup V] {A : Subgroup (MulAut V)} {W U : Subgroup V}
    (hAW : A ≤ stabSub W) (hAU : A ≤ stabSub U) : ((A ⊓ centSec W U).subgroupOf A).Normal := by
  refine ⟨fun g hg a => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hg ⊢
  obtain ⟨hgA, hgW, hgU⟩ := hg
  refine ⟨(a * g * a⁻¹ : ↥A).2, (stabSub W).mul_mem ((stabSub W).mul_mem (hAW a.2) hgW)
    ((stabSub W).inv_mem (hAW a.2)), fun w hw => ?_⟩
  have hw' : (a : MulAut V)⁻¹ w ∈ W := ((stabSub W).inv_mem (hAW a.2) w).2 hw
  have h1 := hgU _ hw'
  have h2 : (a : MulAut V) ((g : MulAut V) ((a : MulAut V)⁻¹ w) * ((a : MulAut V)⁻¹ w)⁻¹) ∈ U :=
    (hAU a.2 _).2 h1
  have e : ((a * g * a⁻¹ : ↥A) : MulAut V) w * w⁻¹ =
      (a : MulAut V) ((g : MulAut V) ((a : MulAut V)⁻¹ w) * ((a : MulAut V)⁻¹ w)⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, map_mul, map_inv,
      MulAut.apply_inv_self]
  rw [e]
  exact h2

theorem le_normalizer_centralizer_self (X : Subgroup G) :
    X ≤ Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  intro x hx
  refine A4.mem_normalizer_of_conj_mem fun c hc => ?_
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have h1 := hc (x⁻¹ * y * x) (X.mul_mem (X.mul_mem (X.inv_mem hx) hy) hx)
  calc y * (x * c * x⁻¹) = x * ((x⁻¹ * y * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * y * x)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * y := by group

omit [Finite G] in
theorem autOn_perfect {X V : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hXp : ⁅X, X⁆ = X) : ⁅autOn X V, autOn X V⁆ = autOn X V :=
  CFSG.Quasithin.AutOn.autOn_perfect hXV hXp

theorem rhoAut_mem_centSec {X V : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    [IsMulCommutative ↥V] (hP2 : ∀ x : ↥V, x ^ 2 = 1) {W₁ U₁ : Subgroup ↥V}
    (h1 : autOn X V ≤ stabSub W₁) (h2 : autOn X V ≤ stabSub U₁)
    (hc : Nat.card (Sec W₁ U₁) ≤ 32) {x : G} (hx : x ∈ X)
    (hnorm : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      X ⊓ Subgroup.centralizer (V : Set G) ≤ N → ¬ 27 ∣ N.relIndex X → x ∈ N) :
    ((rhoAut hXV ⟨x, hx⟩ : ↥(autOn X V)) : MulAut ↥V) ∈ centSec W₁ U₁ := by
  obtain ⟨N, hN⟩ : ∃ N : Subgroup ↥(autOn X V),
      N = (autOn X V ⊓ centSec W₁ U₁).subgroupOf (autOn X V) := ⟨_, rfl⟩
  have hNn : N.Normal := hN ▸ centSec_normal h1 h2
  have hidxN : ¬ 27 ∣ N.index := hN ▸ not_dvd_index_centSec hP2 h1 h2 hc
  obtain ⟨M, hM⟩ : ∃ M : Subgroup G, M = (N.comap (rhoAut hXV)).map X.subtype := ⟨_, rfl⟩
  have hMX : M ≤ X := hM ▸ Subgroup.map_subtype_le _
  have hNc : (N.comap (rhoAut hXV)).Normal := hNn.comap _
  have hXM : X ≤ Subgroup.normalizer (M : Set G) := by
    intro y hy
    refine A4.mem_normalizer_of_conj_mem fun m hm => ?_
    rw [hM] at hm ⊢
    obtain ⟨m', hm', rfl⟩ := hm
    refine ⟨⟨y, hy⟩ * m' * ⟨y, hy⟩⁻¹, hNc.conj_mem m' hm' ⟨y, hy⟩, ?_⟩
    simp
  have hCM : X ⊓ Subgroup.centralizer (V : Set G) ≤ M := by
    rintro y ⟨hyX, hyV⟩
    rw [hM]
    refine ⟨⟨y, hyX⟩, ?_, rfl⟩
    have h3 : rhoAut hXV ⟨y, hyX⟩ = 1 :=
      Subtype.ext (InternalSec.conjAct_eq_one_of_mem_centralizer _ hyV)
    show rhoAut hXV ⟨y, hyX⟩ ∈ N
    rw [h3]
    exact N.one_mem
  have hrel : M.relIndex X = N.index := by rw [hM]; exact relIndex_comap hXV N
  have hxM := hnorm M hMX hXM hCM (by rw [hrel]; exact hidxN)
  rw [hM] at hxM
  obtain ⟨x', hx', hxx'⟩ := hxM
  have hxx : x' = ⟨x, hx⟩ := Subtype.ext hxx'
  subst hxx
  have h3 : rhoAut hXV ⟨x, hx⟩ ∈ N := hx'
  rw [hN] at h3
  exact (Subgroup.mem_subgroupOf.mp h3).2

theorem eq_or_eq_of_index_le {X V : Subgroup G} (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hXp : ⁅X, X⁆ = X)
    (hne : ¬ X ≤ Subgroup.centralizer (V : Set G))
    (hidx : (V ⊓ Subgroup.centralizer (X : Set G)).relIndex V ≤ 64)
    (hnorm : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      X ⊓ Subgroup.centralizer (V : Set G) ≤ N → ¬ 27 ∣ N.relIndex X → N = X)
    {W : Subgroup G} (hCW : V ⊓ Subgroup.centralizer (X : Set G) ≤ W) (hWV : W ≤ V)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    W = V ⊓ Subgroup.centralizer (X : Set G) ∨ W = V := by
  have : IsMulCommutative ↥V := ⟨⟨fun a b => Subtype.ext (hVc _ a.2 _ b.2)⟩⟩
  have hP2 : ∀ x : ↥V, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hV2 _ x.2)
  set C := V ⊓ Subgroup.centralizer (X : Set G) with hCdef
  set A := autOn X V with hAdef
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    A4.mem_normalizer_inf (hXV hx) (le_normalizer_centralizer_self X hx)
  by_contra hcon
  push Not at hcon
  obtain ⟨hWC, hWV'⟩ := hcon
  set C' : Subgroup ↥V := C.subgroupOf V with hC'
  set W' : Subgroup ↥V := W.subgroupOf V with hW'
  have hC'W' : C' ≤ W' := fun x hx => hCW hx
  have hCV : C ≤ V := inf_le_left
  have hi1 : C'.relIndex W' ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    apply hWC
    have hWC' : W' = C' := le_antisymm hle hC'W'
    have h2 := Subgroup.subgroupOf_inj.mp hWC'
    rwa [inf_eq_left.mpr hWV, inf_eq_left.mpr hCV] at h2
  have hi2 : W'.relIndex ⊤ ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    apply hWV'
    have h1 : W' = ⊤ := top_le_iff.mp hle
    exact le_antisymm hWV (Subgroup.subgroupOf_eq_top.mp h1)
  have hmul : C'.relIndex W' * W'.relIndex ⊤ = C'.relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex C' W' ⊤ hC'W' le_top
  have htop : C'.relIndex ⊤ = C.relIndex V := by
    rw [Subgroup.relIndex_top_right]
    rfl
  have hpos1 : C'.relIndex W' ≠ 0 := (C'.subgroupOf W').index_ne_zero_of_finite
  have hpos2 : W'.relIndex ⊤ ≠ 0 := (W'.subgroupOf ⊤).index_ne_zero_of_finite
  have hprod : C'.relIndex W' * W'.relIndex ⊤ ≤ 64 := by rw [hmul, htop]; exact hidx
  have hb1 : C'.relIndex W' ≤ 32 := by
    by_contra h
    have : 33 * 2 ≤ C'.relIndex W' * W'.relIndex ⊤ := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hb2 : W'.relIndex ⊤ ≤ 32 := by
    by_contra h
    have : 2 * 33 ≤ C'.relIndex W' * W'.relIndex ⊤ := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hcard1 : Nat.card (Sec W' C') ≤ 32 := hb1
  have hcard2 : Nat.card (Sec (⊤ : Subgroup ↥V) W') ≤ 32 := hb2
  have key : ∀ {W₁ U₁ : Subgroup ↥V}, A ≤ stabSub W₁ → A ≤ stabSub U₁ →
      Nat.card (Sec W₁ U₁) ≤ 32 → A ≤ centSec W₁ U₁ := by
    intro W₁ U₁ h1 h2 hc φ hφ
    obtain ⟨x, hx⟩ := rhoAut_surjective hXV ⟨φ, hφ⟩
    have h3 := rhoAut_mem_centSec hXV hP2 h1 h2 hc x.2 fun N hNX hXN hCN hidxN => by
      rw [hnorm N hNX hXN hCN hidxN]
      exact x.2
    rw [hx] at h3
    exact h3
  have hA_W' : A ≤ stabSub W' := autOn_le_stabSub hXW
  have hA_C' : A ≤ stabSub C' := autOn_le_stabSub hXC
  have hA_top : A ≤ stabSub (⊤ : Subgroup ↥V) := fun _ _ _ => by simp
  have hA1 := key hA_W' hA_C' hcard1
  have hA2 := key hA_top hA_W' hcard2
  have hA4 : ∀ a ∈ A, a ^ 4 = 1 := by
    intro a ha
    refine pow_four_eq_one_of_cent hP2 (C := C') (W := W') (fun v => ?_) (fun w hw => ?_)
      (fun c hc => ?_)
    · exact (hA2 ha).2 v (Subgroup.mem_top v)
    · exact (hA1 ha).2 w hw
    · obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.mp ha
      apply Subtype.ext
      rw [Setup.coe_conjAct_apply]
      have hcX : (c : G) ∈ Subgroup.centralizer (X : Set G) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hc)).2
      have h3 := Subgroup.mem_centralizer_iff.mp hcX (g : G) hg
      rw [h3, mul_inv_cancel_right]
  have hA2grp : IsPGroup 2 ↥A := by
    intro a
    refine ⟨2, Subtype.ext ?_⟩
    simpa using hA4 a a.2
  have hAbot := eq_bot_of_perfect_of_isPGroup (autOn_perfect hXV hXp) hA2grp
  apply hne
  intro x hx
  have h3 : rhoAut hXV ⟨x, hx⟩ = 1 := by
    have h4 : ((rhoAut hXV ⟨x, hx⟩ : ↥A) : MulAut ↥V) ∈ (⊥ : Subgroup (MulAut ↥V)) := by
      rw [← hAbot]
      exact (rhoAut hXV ⟨x, hx⟩).2
    exact Subtype.ext ((Subgroup.mem_bot).mp h4)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h4 := congrArg (fun φ : ↥A => (((φ : MulAut ↥V) ⟨v, hv⟩ : ↥V) : G)) h3
  simp only [rhoAut_apply] at h4
  have h5 : x * v * x⁻¹ = v := h4
  calc v * x = (x * v * x⁻¹) * x := by rw [h5]
    _ = x * v := by group

theorem eq_bot_or_eq_of_order_three {X U : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ u ∈ U, u ^ 2 = 1) (hcard : Nat.card U ≤ 64) {z : G} (hzX : z ∈ X)
    (hz3 : z ^ 3 ∈ Subgroup.centralizer (U : Set G)) (hzU : z ∉ Subgroup.centralizer (U : Set G))
    (hnorm : ∀ N : Subgroup G, N ≤ X → X ≤ Subgroup.normalizer (N : Set G) →
      X ⊓ Subgroup.centralizer (U : Set G) ≤ N → ¬ 27 ∣ N.relIndex X → z ∈ N)
    {W : Subgroup G} (hWU : W ≤ U) (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    W = ⊥ ∨ W = U := by
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hUc _ a.2 _ b.2)⟩⟩
  have hP2 : ∀ x : ↥U, x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hU2 _ x.2)
  by_contra hcon
  push Not at hcon
  obtain ⟨hW1, hWU'⟩ := hcon
  set W' : Subgroup ↥U := W.subgroupOf U with hW'
  have hi1 : (⊥ : Subgroup ↥U).relIndex W' ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    apply hW1
    rw [eq_bot_iff]
    intro w hw
    have h1 : (⟨w, hWU hw⟩ : ↥U) ∈ W' := hw
    have h2 := hle h1
    rw [Subgroup.mem_bot] at h2
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  have hi2 : W'.relIndex ⊤ ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact hWU' (le_antisymm hWU (Subgroup.subgroupOf_eq_top.mp (top_le_iff.mp hle)))
  have hmul : (⊥ : Subgroup ↥U).relIndex W' * W'.relIndex ⊤ = (⊥ : Subgroup ↥U).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex ⊥ W' ⊤ bot_le le_top
  have htop : (⊥ : Subgroup ↥U).relIndex ⊤ = Nat.card U := by
    rw [Subgroup.relIndex_top_right, Subgroup.index_bot]
  have hpos1 : (⊥ : Subgroup ↥U).relIndex W' ≠ 0 :=
    ((⊥ : Subgroup ↥U).subgroupOf W').index_ne_zero_of_finite
  have hpos2 : W'.relIndex ⊤ ≠ 0 := (W'.subgroupOf ⊤).index_ne_zero_of_finite
  have hprod : (⊥ : Subgroup ↥U).relIndex W' * W'.relIndex ⊤ ≤ 64 := by
    rw [hmul, htop]
    exact hcard
  have hb1 : (⊥ : Subgroup ↥U).relIndex W' ≤ 32 := by
    by_contra h
    have : 33 * 2 ≤ (⊥ : Subgroup ↥U).relIndex W' * W'.relIndex ⊤ :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hb2 : W'.relIndex ⊤ ≤ 32 := by
    by_contra h
    have : 2 * 33 ≤ (⊥ : Subgroup ↥U).relIndex W' * W'.relIndex ⊤ :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  have hA_W' : autOn X U ≤ stabSub W' := autOn_le_stabSub hXW
  have hA_bot : autOn X U ≤ stabSub (⊥ : Subgroup ↥U) := fun φ _ u => by
    rw [Subgroup.mem_bot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff]
  have hA_top : autOn X U ≤ stabSub (⊤ : Subgroup ↥U) := fun _ _ _ => by simp
  have h1 := rhoAut_mem_centSec hXU hP2 hA_W' hA_bot hb1 hzX hnorm
  have h2 := rhoAut_mem_centSec hXU hP2 hA_top hA_W' hb2 hzX hnorm
  set a := ((rhoAut hXU ⟨z, hzX⟩ : ↥(autOn X U)) : MulAut ↥U) with ha
  have ha2 : a ^ 2 = 1 := by
    refine sq_eq_one_of_cent hP2 (W := W') (fun v => h2.2 v (Subgroup.mem_top v)) fun w hw => ?_
    have h3 := h1.2 w hw
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3
  have ha3 : a ^ 3 = 1 := by
    have h3 : rhoAut hXU ((⟨z, hzX⟩ : ↥X) ^ 3) = 1 := by
      apply Subtype.ext
      exact InternalSec.conjAct_eq_one_of_mem_centralizer _ (by simpa using hz3)
    rw [ha, ← Subgroup.coe_pow, ← map_pow, h3, OneMemClass.coe_one]
  have ha1 : a = 1 := by
    have : a = a ^ 3 * (a ^ 2)⁻¹ := by group
    rw [this, ha2, ha3, inv_one, mul_one]
  apply hzU
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h4 := congrArg (fun φ : MulAut ↥U => ((φ ⟨u, hu⟩ : ↥U) : G)) ha1
  simp only [ha, rhoAut_apply] at h4
  have h5 : z * u * z⁻¹ = u := h4
  calc u * z = (z * u * z⁻¹) * z := by rw [h5]
    _ = z * u := by group

theorem mem_evenWeight' {m : ℕ} {x : Fin m → ZMod 2} : x ∈ evenWeight m ↔ ∑ i, x i = 0 :=
  AddMonoidHom.mem_ker

theorem sum_pair :
    ∀ a b : Fin 8, ∑ i, ((Pi.single a 1 + Pi.single b 1 : Fin 8 → ZMod 2)) i = 0 := by
  decide +kernel

@[expose] def pairVec (a b : Fin 8) : ↥(evenWeight 8) :=
  ⟨(Pi.single a 1 + Pi.single b 1 : Fin 8 → ZMod 2), mem_evenWeight'.mpr (sum_pair a b)⟩

theorem three_cycle_add : ∀ (x : Fin 8 → ZMod 2) (i j k : Fin 8), i ≠ j → j ≠ k → i ≠ k →
    x i = 1 → x k = 1 → x j = 0 → ∀ m : Fin 8,
    x m + x ((Equiv.swap i j * Equiv.swap j k)⁻¹ m) =
      ((Pi.single j 1 + Pi.single k 1 : Fin 8 → ZMod 2)) m := by
  decide +kernel

theorem exists_three : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 → ¬ (∀ i j, x i = x j) →
    ∃ i j k : Fin 8, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i = 1 ∧ x k = 1 ∧ x j = 0 := by
  decide +kernel

theorem decomp_pairs : ∀ x : Fin 8 → ZMod 2, ∑ i, x i = 0 →
    x = ∑ i, (if i ≠ 0 ∧ x i = 1 then (Pi.single 0 1 + Pi.single i 1 : Fin 8 → ZMod 2) else 0) := by
  decide +kernel

theorem permWeight_pairVec (σ : Equiv.Perm (Fin 8)) (a b : Fin 8) :
    permWeight 8 σ (pairVec a b) = pairVec (σ a) (σ b) := by
  apply Subtype.ext
  funext m
  show (Pi.single a 1 + Pi.single b 1 : Fin 8 → ZMod 2) (σ⁻¹ m) =
    (Pi.single (σ a) 1 + Pi.single (σ b) 1 : Fin 8 → ZMod 2) m
  have h1 : (σ⁻¹ m = a) ↔ (m = σ a) := Equiv.Perm.inv_eq_iff_eq
  have h2 : (σ⁻¹ m = b) ↔ (m = σ b) := Equiv.Perm.inv_eq_iff_eq
  simp only [Pi.add_apply, Pi.single_apply, h1, h2]

theorem exists_alt8_pair {a b c d : Fin 8} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : alternatingGroup (Fin 8), (σ : Equiv.Perm (Fin 8)) a = c ∧
      (σ : Equiv.Perm (Fin 8)) b = d := by
  have h6 := alternatingGroup.isMultiplyPretransitive (Fin 8)
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 8)) (Fin 8) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 8) - 2) (by simp) (by simp)
  let x : Fin 2 ↪ Fin 8 := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  let y : Fin 2 ↪ Fin 8 := ⟨![c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) x y
  refine ⟨g, ?_, ?_⟩
  · exact congrArg (fun z : Fin 2 ↪ Fin 8 => z 0) hg
  · exact congrArg (fun z : Fin 2 ↪ Fin 8 => z 1) hg

theorem heart_eq_bot_or_top (X : AddSubgroup (AltHeart 8))
    (hX : ∀ σ : alternatingGroup (Fin 8), ∀ x : ↥(evenWeight 8),
      (QuotientAddGroup.mk x : AltHeart 8) ∈ X →
        (QuotientAddGroup.mk (permWeight 8 (σ : Equiv.Perm (Fin 8)) x) : AltHeart 8) ∈ X) :
    X = ⊥ ∨ X = ⊤ := by
  by_cases hb : X = ⊥
  · exact Or.inl hb
  right
  obtain ⟨⟨y, hyX⟩, hy0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp hb
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  have hy0' : (QuotientAddGroup.mk x : AltHeart 8) ≠ 0 := fun h => hy0 (Subtype.ext h)
  have hc : ¬ ∀ i j, (x : Fin 8 → ZMod 2) i = (x : Fin 8 → ZMod 2) j := by
    intro hc
    apply hy0'
    rw [QuotientAddGroup.eq_zero_iff]
    exact hc
  obtain ⟨i, j, k, hij, hjk, hik, hi, hk, hj⟩ :=
    exists_three x (mem_evenWeight'.mp x.2) hc
  let τ : alternatingGroup (Fin 8) := ⟨Equiv.swap i j * Equiv.swap j k, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
      Equiv.Perm.sign_swap hjk]
    decide⟩
  have hpair : (QuotientAddGroup.mk (pairVec j k) : AltHeart 8) ∈ X := by
    have h1 := X.add_mem hyX (hX τ x hyX)
    have h2 : x + permWeight 8 (τ : Equiv.Perm (Fin 8)) x = pairVec j k := by
      apply Subtype.ext
      funext m
      exact three_cycle_add x i j k hij hjk hik hi hk hj m
    rw [← QuotientAddGroup.mk_add, h2] at h1
    exact h1
  have hall : ∀ a b : Fin 8, a ≠ b → (QuotientAddGroup.mk (pairVec a b) : AltHeart 8) ∈ X := by
    intro a b hab
    obtain ⟨σ, hσa, hσb⟩ := exists_alt8_pair hjk hab
    have h1 := hX σ _ hpair
    rwa [permWeight_pairVec, hσa, hσb] at h1
  rw [eq_top_iff]
  rintro z -
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hw : w = ∑ i, (if i ≠ 0 ∧ (w : Fin 8 → ZMod 2) i = 1 then pairVec 0 i else 0) := by
    apply Subtype.ext
    push_cast
    convert decomp_pairs w (mem_evenWeight'.mp w.2) using 2 with i
    split_ifs <;> rfl
  set X' : AddSubgroup ↥(evenWeight 8) := X.comap (QuotientAddGroup.mk' (constWeight 8)) with hX'
  have hmem : ∀ v, v ∈ X' ↔ (QuotientAddGroup.mk v : AltHeart 8) ∈ X := fun v => Iff.rfl
  rw [← hmem, hw]
  refine X'.sum_mem fun i _ => ?_
  split_ifs with h
  · exact (hmem _).mpr (hall 0 i (Ne.symm h.1))
  · exact X'.zero_mem

end CFSG.Quasithin.H13.Ch4.T4213N
