module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep5
public import CFSG.Quasithin.Vol2.Ch12Sec8OneNineW

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

section GroupFacts

variable {G : Type} [Group G] [Finite G]

theorem conj_mono' {H K : Subgroup G} (h : H ≤ K) (g : G) :
    CFSG.conjugate H g ≤ CFSG.conjugate K g :=
  Subgroup.map_mono h

theorem mem_conj' {H : Subgroup G} {g x : G} : x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    have : g * (MulAut.conj g⁻¹).toMonoidHom h * g⁻¹ = h := by simp [mul_assoc]
    rw [this]
    exact hh
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem zU_le_W {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂) :
    zU128 V V₁ ≤ w128 V V₁ V₂ := by
  intro z hz
  have hzU : z ∈ u128 V V₁ := (Subgroup.mem_inf.1 hz).1
  refine Subgroup.mem_inf.2 ⟨hzU, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hc := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hz).2) v
    (le_conjClosure V _ (hs.v2.1 hv))
  exact hc

theorem pCore_i128_le_T (h1222 : Stmt12_2_2) (h1289 : Lemma12_8_9W)
    {T L V V₁ V₂ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    pCoreOf 2 (i128 T L V V₁) ≤ T := by
  have h9 := h1289 G T L V 4 V₁ V₂ hs g hgP hgN
  have hO : pCoreOf 2 (i128 T L V V₁) = w128 V V₁ V₂ ⊔ CFSG.conjugate (w128 V V₁ V₂) g :=
    h9.2.2
  have hTN : T ≤ Subgroup.normalizer (V₂ : Set G) := hs.v2.2.2
  have hgN2 : g ∈ Subgroup.normalizer (V₂ : Set G) := p128_le_normalizer_V₂ hs hgP
  have hT2 : IsPGroup 2 T := hcx.hyp.hyp.sylow.1
  have hWN : w128 V V₁ V₂ ≤ Subgroup.normalizer (V₂ : Set G) := fun w hw =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.1 hw).2
  have hWgN : CFSG.conjugate (w128 V V₁ V₂) g ≤ Subgroup.normalizer (V₂ : Set G) := by
    intro x hx
    have hgx : g * x * g⁻¹ ∈ w128 V V₁ V₂ := mem_conj'.1 hx
    have hgxN := hWN hgx
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN2) hgxN) hgN2
  have hX : pCoreOf 2 (i128 T L V V₁) ≤ Subgroup.normalizer (V₂ : Set G) := by
    rw [hO]
    exact sup_le hWN hWgN
  have hN2 : Subgroup.normalizer (V₂ : Set G) ≤
      Subgroup.normalizer ((pCoreOf 2 (i128 T L V V₁)) : Set G) := by
    intro x hx
    have hxI : x ∈ Subgroup.normalizer (i128 T L V V₁ : Set G) := h9.2.1 hx
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxI
  have h1 : pCoreOf 2 (i128 T L V V₁) ≤ pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hX hN2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hTK : ¬ 2 ∣ (T.subgroupOf (Subgroup.normalizer (V₂ : Set G))).index := by
    intro h
    have hdiv : (T.subgroupOf (Subgroup.normalizer (V₂ : Set G))).index ∣ T.index := by
      have := Subgroup.relIndex_dvd_index_of_le hTN
      exact this
    exact hcx.hyp.hyp.sylow.2 (h.trans hdiv)
  have h2 : pCoreOf 2 (Subgroup.normalizer (V₂ : Set G)) ≤ pCoreOf 2 T :=
    pCoreOf_le_pCoreOf_of_sylow hTN hT2 le_rfl hTK
  have h3 : pCoreOf 2 T ≤ T := Subgroup.map_subtype_le _
  exact h1.trans (h2.trans h3)

theorem Dg_le_T (h1222 : Stmt12_2_2) (h1289 : Lemma12_8_9W)
    {T L V V₁ V₂ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    CFSG.conjugate (zU128 V V₁) g ≤ T := by
  have h9 := h1289 G T L V 4 V₁ V₂ hs g hgP hgN
  have hO := h9.2.2
  calc CFSG.conjugate (zU128 V V₁) g ≤ CFSG.conjugate (w128 V V₁ V₂) g :=
        conj_mono' (zU_le_W hs) g
    _ ≤ w128 V V₁ V₂ ⊔ CFSG.conjugate (w128 V V₁ V₂) g := le_sup_right
    _ = pCoreOf 2 (i128 T L V V₁) := hO.symm
    _ ≤ T := pCore_i128_le_T h1222 h1289 hcx hs hgP hgN

theorem Dg_le_centralizer_V (h12813 : Lemma12_8_13)
    {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂)
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G)) :
    CFSG.conjugate (zU128 V V₁) g ≤ Subgroup.centralizer (V : Set G) :=
  (h12813 G T L V 4 V₁ V₂ hs g hgP hgN).2.1

end GroupFacts

section DLevel

variable {G : Type} [Group G] [Finite G]

@[expose] def piSub {V V₁ : Subgroup G} (D : HatModelU (u128 V V₁)) (a : G) : Subgroup G where
  carrier := {x | x ∈ u128 V V₁ ∧ D.π x ∈ Submodule.span (ZMod 2) {D.π a}}
  mul_mem' := fun {x y} hx hy =>
    ⟨(u128 V V₁).mul_mem hx.1 hy.1, by
      rw [D.π_mul x hx.1 y hy.1]
      exact Submodule.add_mem _ hx.2 hy.2⟩
  one_mem' := ⟨(u128 V V₁).one_mem, by
    rw [L128A.HatU.π_one D]
    exact Submodule.zero_mem _⟩
  inv_mem' := fun {x} hx =>
    ⟨(u128 V V₁).inv_mem hx.1, by
      rw [L128A.HatU.π_inv D hx.1]
      exact Submodule.neg_mem _ hx.2⟩

theorem mem_piSub {V V₁ : Subgroup G} (D : HatModelU (u128 V V₁)) (a x : G) :
    x ∈ piSub D a ↔ x ∈ u128 V V₁ ∧ D.π x ∈ Submodule.span (ZMod 2) {D.π a} := Iff.rfl

theorem zU_sup_V2_le_piSub (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂)
    (D : HatModelU (u128 V V₁)) {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁) :
    centerOf (u128 V V₁) ⊔ V₂ ≤ piSub D a := by
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, -⟩ := L128P.exists_gens hV₁2 hV₂4
  have hUV : ∀ v ∈ V, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ hv
  have hπz : D.π z = 0 := by
    have hzZ : z ∈ V ⊓ zU128 V V₁ := by
      rw [lemma12_8_8_three h1222 h12213 hs]
      exact hz
    exact (L128A.HatU.π_eq_zero_iff D (hUV z (hs.v1.1 hz))).2 (Subgroup.mem_inf.1 hzZ).2
  have hza : D.π (z * a) = D.π a := by
    rw [D.π_mul z (hUV z (hs.v1.1 hz)) a (hUV a (hs.v2.1 haV₂)), hπz, zero_add]
  apply sup_le
  · intro x hx
    rw [mem_piSub]
    have hxU : x ∈ u128 V V₁ := (Subgroup.mem_inf.1 hx).1
    refine ⟨hxU, ?_⟩
    have h0 : D.π x = 0 := (L128A.HatU.π_eq_zero_iff D hxU).2 hx
    rw [h0]
    exact Submodule.zero_mem _
  · intro x hx
    rw [mem_piSub]
    refine ⟨hUV x (hs.v2.1 hx), ?_⟩
    rcases L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ haV₂ hx with h | h | h | h
    · rw [h, L128A.HatU.π_one D]
      exact Submodule.zero_mem _
    · rw [h, hπz]
      exact Submodule.zero_mem _
    · rw [h]
      exact Submodule.subset_span rfl
    · rw [h, hza]
      exact Submodule.subset_span rfl

theorem rho_Dg_sub_mem_span (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12810 : Lemma12_8_10)
    {T L V V₁ V₂ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁)) {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁)
    {d : G} (hdD : d ∈ CFSG.conjugate (zU128 V V₁) g)
    (hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G))
    {u : G} (hu : u ∈ w128 V V₁ V₂) :
    D.ρ ⟨d, hdN⟩ (D.π u) - D.π u ∈ Submodule.span (ZMod 2) {D.π a} := by
  have hc := (h12810 G T L V 4 V₁ V₂ hs g hgP hgN).2.2.2.1
  have huU : u ∈ u128 V V₁ := (Subgroup.mem_inf.1 hu).1
  have hcm : u * d * u⁻¹ * d⁻¹ ∈ zU128 V V₁ ⊔ V₂ := by
    rw [← commutatorElement_def]
    exact hc.1 (Subgroup.commutator_mem_commutator hu hdD)
  have hcpi : (u * d * u⁻¹ * d⁻¹) ∈ piSub D a :=
    zU_sup_V2_le_piSub h1222 h12213 hs D haV₂ haV₁ hcm
  have hcinv : (u * d * u⁻¹ * d⁻¹)⁻¹ ∈ piSub D a := Subgroup.inv_mem _ hcpi
  have hcinvU : (u * d * u⁻¹ * d⁻¹)⁻¹ ∈ u128 V V₁ := ((mem_piSub D a _).1 hcinv).1
  have e1 : D.ρ ⟨d, hdN⟩ (D.π u) = D.π (d * u * d⁻¹) := D.ρ_π ⟨d, hdN⟩ u huU
  have e2 : d * u * d⁻¹ = (u * d * u⁻¹ * d⁻¹)⁻¹ * u := by group
  rw [e1, e2, D.π_mul _ hcinvU _ huU, add_sub_cancel_right]
  exact ((mem_piSub D a _).1 hcinv).2

theorem piW_perp (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    {T L V V₁ V₂ : Subgroup G} (hs : Setting1282One G T L V 4 V₁ V₂)
    (D : HatModelU (u128 V V₁)) {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁) (x : D.V) :
    D.B x (D.π a) = 0 ↔ ∃ u ∈ w128 V V₁ V₂, D.π u = x := by
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hs.v1.2.1
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  obtain ⟨z, hz, hz1, -⟩ := L128P.exists_gens hV₁2 hV₂4
  have hUV : ∀ v ∈ V, v ∈ u128 V V₁ := fun v hv => le_conjClosure V _ hv
  have haU : a ∈ u128 V V₁ := hUV a (hs.v2.1 haV₂)
  have hzZ : z ∈ V ⊓ zU128 V V₁ := by
    rw [lemma12_8_8_three h1222 h12213 hs]
    exact hz
  have hzc : z ∈ centerOf (u128 V V₁) := (Subgroup.mem_inf.1 hzZ).2
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := D.π_surj x
    have hua : u * a * u⁻¹ * a⁻¹ = 1 := (D.B_spec u hu a haU).1 h
    have hCa : u * a = a * u := by
      calc u * a = (u * a * u⁻¹ * a⁻¹) * a * u := by group
        _ = a * u := by rw [hua, one_mul]
    have hzu : u * z = z * u := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hzc).2) u hu
    refine ⟨u, Subgroup.mem_inf.2 ⟨hu, Subgroup.mem_centralizer_iff.2 ?_⟩, rfl⟩
    intro v hv
    rcases L128P.eq_of_mem_four hs.le hV₁2 hV₂4 hz hz1 haV₁ haV₂ hv with h | h | h | h
    · rw [h, one_mul, mul_one]
    · rw [h, hzu]
    · rw [h, ← hCa]
    · rw [h]
      calc z * a * u = z * (a * u) := by group
        _ = z * (u * a) := by rw [← hCa]
        _ = (z * u) * a := by group
        _ = (u * z) * a := by rw [hzu]
        _ = u * (z * a) := by group
  · rintro ⟨u, hu, rfl⟩
    have hau : a * u = u * a := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hu).2) a haV₂
    have huU : u ∈ u128 V V₁ := (Subgroup.mem_inf.1 hu).1
    refine (D.B_spec u huU a haU).2 ?_
    calc u * a * u⁻¹ * a⁻¹ = (a * u) * u⁻¹ * a⁻¹ := by rw [hau]
      _ = 1 := by group

theorem rho_fix_pi_of_centralizer {V V₁ : Subgroup G} (D : HatModelU (u128 V V₁)) {d : G}
    (hdC : d ∈ Subgroup.centralizer (V : Set G))
    (hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G)) {v : G} (hv : v ∈ V) :
    D.ρ ⟨d, hdN⟩ (D.π v) = D.π v := by
  have hUV : v ∈ u128 V V₁ := le_conjClosure V _ hv
  rw [D.ρ_π ⟨d, hdN⟩ v hUV]
  congr 1
  have hc := Subgroup.mem_centralizer_iff.1 hdC v hv
  rw [← hc]
  group

theorem pi_ne_zero_of_not_mem {T L V V₁ V₂ : Subgroup G} (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (hs : Setting1282One G T L V 4 V₁ V₂) (D : HatModelU (u128 V V₁))
    {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁) : D.π a ≠ 0 := by
  intro h0
  have hU : a ∈ u128 V V₁ := le_conjClosure V _ (hs.v2.1 haV₂)
  have h1 : a ∈ V ⊓ zU128 V V₁ :=
    ⟨hs.v2.1 haV₂, (L128A.HatU.π_eq_zero_iff D hU).1 h0⟩
  rw [lemma12_8_8_three h1222 h12213 hs] at h1
  exact haV₁ h1

theorem rho_Dg_pieces (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h12810 : Lemma12_8_10)
    {T L V V₁ V₂ K₁ : Subgroup G} (hcx : Cx1291 G T L V 4) (hs : Setting1282One G T L V 4 V₁ V₂)
    {g : G} (hgP : g ∈ p128 T L V) (hgN : g ∉ Subgroup.normalizer (V₁ : Set G))
    (D : HatModelU (u128 V V₁)) {q : D.V → ZMod 2}
    (F4 : F4Out q D.B (D.img K₁))
    (S : Submodule (ZMod 2) D.V) (hS3 : Module.finrank (ZMod 2) S = 3)
    (hSq : ∀ s ∈ S, q s = 0) (hSV : ∀ v ∈ V, D.π v ∈ S)
    (hSπ : ∀ s ∈ S, ∃ v ∈ V, D.π v = s)
    (hTS : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G), D.ρ ⟨t, htU⟩ ∈ stabS S)
    (hTΩ : ∀ t ∈ T, ∀ htU : t ∈ Subgroup.normalizer (u128 V V₁ : Set G),
      D.ρ ⟨t, htU⟩ ∈ D.img K₁)
    {a : G} (haV₂ : a ∈ V₂) (haV₁ : a ∉ V₁)
    {d : G} (hdD : d ∈ CFSG.conjugate (zU128 V V₁) g) (hdT : d ∈ T)
    (hdC : d ∈ Subgroup.centralizer (V : Set G))
    (hdN : d ∈ Subgroup.normalizer (u128 V V₁ : Set G)) :
    D.ρ ⟨d, hdN⟩ ∈ pCoreOf 2 (stabS S ⊓ D.img K₁) ∧
      D.ρ ⟨d, hdN⟩ ∈ pCoreOf 2 (stabS (Submodule.span (ZMod 2) {D.π a}) ⊓ D.img K₁) := by
  have hΩd : D.ρ ⟨d, hdN⟩ ∈ D.img K₁ := hTΩ d hdT hdN
  have hSd : D.ρ ⟨d, hdN⟩ ∈ stabS S := hTS d hdT hdN
  have hfixS : ∀ s ∈ S, D.ρ ⟨d, hdN⟩ s = s := by
    intro s hs
    obtain ⟨v, hv, rfl⟩ := hSπ s hs
    exact rho_fix_pi_of_centralizer D hdC hdN hv
  have hSmem : D.ρ ⟨d, hdN⟩ ∈ stabS S ⊓ D.img K₁ := Subgroup.mem_inf.2 ⟨hSd, hΩd⟩
  have hw0 : D.π a ≠ 0 := pi_ne_zero_of_not_mem h1222 h12213 hs D haV₂ haV₁
  have hqw : q (D.π a) = 0 := hSq _ (hSV a (hs.v2.1 haV₂))
  refine ⟨((F4.2.2.1 S hS3 hSq).2.2.2 _ hSmem).mp hfixS, ?_⟩
  have hfixa : D.ρ ⟨d, hdN⟩ (D.π a) = D.π a :=
    rho_fix_pi_of_centralizer D hdC hdN (hs.v2.1 haV₂)
  have hspan : D.ρ ⟨d, hdN⟩ ∈ stabS (Submodule.span (ZMod 2) {D.π a}) :=
    mem_stabS_span_of_fix hfixa
  have hmem' : D.ρ ⟨d, hdN⟩ ∈ stabS (Submodule.span (ZMod 2) {D.π a}) ⊓ D.img K₁ :=
    Subgroup.mem_inf.2 ⟨hspan, hΩd⟩
  have hperp : ∀ x : D.V, D.B x (D.π a) = 0 →
      D.ρ ⟨d, hdN⟩ x - x ∈ Submodule.span (ZMod 2) {D.π a} := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := (piW_perp h1222 h12213 hs D haV₂ haV₁ x).1 hx
    exact rho_Dg_sub_mem_span h1222 h12213 h12810 hcx hs hgP hgN D haV₂ haV₁ hdD hdN hu
  exact ((F4.2.2.2 (D.π a) hw0 hqw).2 _ hmem').mp hperp

end DLevel

end CFSG.Quasithin.H13.C1294
