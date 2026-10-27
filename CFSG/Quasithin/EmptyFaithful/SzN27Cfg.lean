module

public import CFSG.Quasithin.EmptyFaithful.R3c11Cl
public import CFSG.Quasithin.EmptyFaithful.R3c14Red

public section

namespace CFSG.Quasithin.SzN27

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14
open CFSG.ComponentClassification
open scoped commutatorElement

section Cfg

variable {X X' : Type} [Group X] [Group X']

structure ElDataPlus (T V H : Subgroup X) (ζ : MulAut X) : Prop extends ElData T V H ζ where
  quot3 : ∃ P : Subgroup X, P ≤ H ∧ H ≤ Subgroup.normalizer (P : Set X) ∧ IsPGroup 2 ↥P ∧
    ∀ h ∈ H, h ^ 3 ∈ P
  theta : ∀ x ∈ Subgroup.normalizer (H : Set X), x ^ 3 = 1 → x ∈ H

theorem ElDataPlus.map {T V H : Subgroup X} {ζ : MulAut X} (φ : X ≃* X') (h : ElDataPlus T V H ζ) :
    ElDataPlus (T.map φ.toMonoidHom) (V.map φ.toMonoidHom) (H.map φ.toMonoidHom)
      (MulAut.congr φ ζ) where
  toElData := h.toElData.map φ
  quot3 := by
    obtain ⟨P, hPH, hHP, hP2, hP3⟩ := h.quot3
    refine ⟨P.map φ.toMonoidHom, Subgroup.map_mono hPH, ?_, hP2.map φ.toMonoidHom, ?_⟩
    · intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := ht
      exact (R3c11.mem_normalizer_map_equiv_iff φ P t₀).mpr (hHP ht₀)
    · rintro _ ⟨h₀, hh₀, rfl⟩
      exact ⟨h₀ ^ 3, hP3 h₀ hh₀, by simp⟩
  theta := by
    intro x' hx' hx3
    obtain ⟨x, rfl⟩ := φ.surjective x'
    have hxN : x ∈ Subgroup.normalizer (H : Set X) :=
      (R3c11.mem_normalizer_map_equiv_iff φ H x).mp hx'
    have hx3' : x ^ 3 = 1 := φ.injective (by rw [map_pow, hx3, map_one])
    exact ⟨x, h.theta x hxN hx3', rfl⟩

@[expose] def ElConfigPlus (X : Type) [Group X] : Prop :=
  ∃ (T V H : Subgroup X) (ζ : MulAut X), IsSylowTwoOf T ⊤ ∧ ElDataPlus T V H ζ

theorem ElConfigPlus.map (φ : X ≃* X') (h : ElConfigPlus X) : ElConfigPlus X' := by
  obtain ⟨T, V, H, ζ, hT, hd⟩ := h
  have hT' : IsSylowTwoOf (T.map φ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hT
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map φ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact hi
  exact ⟨_, _, _, _, hT', hd.map φ⟩

theorem ElConfigPlus.of_sylow [Finite X] {T₀ : Subgroup X} (hT₀ : IsSylowTwoOf T₀ ⊤)
    (h : ElConfigPlus X) :
    ∃ (V H : Subgroup X) (ζ : MulAut X), ElDataPlus T₀ V H ζ := by
  obtain ⟨T, V, H, ζ, hT, hd⟩ := h
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top hT hT₀
  subst hg
  exact ⟨_, _, _, hd.map (MulAut.conj g)⟩

end Cfg

section Image

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_pCoreOf {Y : Subgroup G} {y u : G} (hy : y ∈ Y) (hu : u ∈ pCoreOf 2 Y) :
    y * u * y⁻¹ ∈ pCoreOf 2 Y := by
  obtain ⟨u', hu', rfl⟩ := hu
  have hn : (CFSG.Open.pCore 2 ↥Y).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  exact ⟨⟨y, hy⟩ * u' * ⟨y, hy⟩⁻¹, hn.conj_mem u' hu' ⟨y, hy⟩, by simp⟩

theorem quot3_image {L Yp : Subgroup G} (hYL : Yp ≤ L)
    (hY3 : ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp) :
    ∃ P : Subgroup (↥L ⧸ Subgroup.center ↥L),
      P ≤ (Yp.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ∧
      (Yp.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
        Subgroup.normalizer (P : Set (↥L ⧸ Subgroup.center ↥L)) ∧ IsPGroup 2 ↥P ∧
      ∀ h ∈ (Yp.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
        h ^ 3 ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  have hO : pCoreOf 2 Yp ≤ L := (CFSG.LieType.BorelTits.pCoreOf_le 2 Yp).trans hYL
  refine ⟨((pCoreOf 2 Yp).subgroupOf L).map π, ?_, ?_, ?_, ?_⟩
  · refine Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ?_
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 Yp (Subgroup.mem_subgroupOf.mp hx)
  · rintro _ ⟨y, hy, rfl⟩
    have hyY : (y : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hy
    refine A4.mem_normalizer_of_conj_mem fun p hp => ?_
    obtain ⟨u, hu, rfl⟩ := hp
    refine ⟨y * u * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
    have : ((y * u * y⁻¹ : ↥L) : G) = (y : G) * (u : G) * (y : G)⁻¹ := rfl
    rw [this]
    exact conj_mem_pCoreOf hyY (Subgroup.mem_subgroupOf.mp hu)
  · have h2 : IsPGroup 2 ↥(pCoreOf 2 Yp) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Yp
    have h2' : IsPGroup 2 ↥((pCoreOf 2 Yp).subgroupOf L) :=
      h2.of_equiv (Subgroup.subgroupOfEquivOfLe hO).symm
    exact h2'.map π
  · rintro _ ⟨y, hy, rfl⟩
    have hyY : (y : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hy
    exact ⟨y ^ 3, Subgroup.mem_subgroupOf.mpr (hY3 y hyY), by simp [map_pow]⟩

theorem mem_normalizer_of_conj_le {U : Subgroup G} {y : G}
    (h : ∀ u ∈ U, y * u * y⁻¹ ∈ U) : y ∈ Subgroup.normalizer (U : Set G) := by
  let f : ↥U → ↥U := fun u => ⟨y * u * y⁻¹, h u u.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have := congrArg Subtype.val hab
    simp only [f, mul_left_inj, mul_right_inj] at this
    exact Subtype.ext this
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fun hg => h g hg, fun hg => ?_⟩
  obtain ⟨w, hw⟩ := hsurj ⟨y * g * y⁻¹, hg⟩
  have := congrArg Subtype.val hw
  simp only [f, mul_left_inj, mul_right_inj] at this
  rw [← this]
  exact w.2

theorem four_pow_eq (m : ℕ) : 4 ^ m = 2 ^ m * 2 ^ m := by
  rw [← mul_pow]
  norm_num

theorem pow_four_pow_eq {M : Type*} [Monoid M] {v : M} (hv : v ^ 3 = 1) (m : ℕ) :
    v ^ 4 ^ m = v := by
  have h1 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  conv_lhs => rw [← Nat.div_add_mod (4 ^ m) 3, h1, pow_add, pow_mul, hv, one_pow, one_mul, pow_one]

theorem theta_image {L Yp : Subgroup G}
    (hZ : centerOf L = CFSG.Open.pCoreOf 2 L) (hYL : Yp ≤ L)
    (hgen3 : Yp ≤ Subgroup.closure {x : G | x ∈ Yp ∧ x ^ 3 = 1})
    (hθ : ∀ x ∈ L, x ∈ Subgroup.normalizer (Yp : Set G) → x ^ 3 = 1 → x ∈ Yp) :
    ∀ x ∈ Subgroup.normalizer (((Yp.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)), x ^ 3 = 1 →
      x ∈ (Yp.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hZ2 : ∀ z : ↥L, z ∈ Z → ∃ m : ℕ, z ^ 2 ^ m = 1 := by
    intro z hz
    have hzc : (z : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hz
    rw [hZ] at hzc
    obtain ⟨z', hz', hzz⟩ := hzc
    have hzz' : z' = z := Subtype.ext hzz
    subst hzz'
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥L)) ⟨z', hz'⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  intro xb hxb hx3
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z xb
  have hx3Z : x ^ 3 ∈ Z := by
    rw [← hker, MonoidHom.mem_ker, map_pow]
    exact hx3
  obtain ⟨k, hk⟩ := hZ2 _ hx3Z
  set x' : ↥L := x ^ 2 ^ k with hx'
  have hx'3 : x' ^ 3 = 1 := by
    rw [hx', ← pow_mul, mul_comm, pow_mul]
    exact hk
  have hπx' : π x' ∈ Subgroup.normalizer
      (((Yp.subgroupOf L).map π : Subgroup (↥L ⧸ Z)) : Set (↥L ⧸ Z)) := by
    rw [hx', map_pow]
    exact Subgroup.pow_mem _ hxb _
  have hgenconj : ∀ u ∈ {w : G | w ∈ Yp ∧ w ^ 3 = 1}, (x' : G) * u * (x' : G)⁻¹ ∈ Yp := by
    rintro u ⟨huY, hu3⟩
    set uL : ↥L := ⟨u, hYL huY⟩ with huL
    have huY' : uL ∈ Yp.subgroupOf L := Subgroup.mem_subgroupOf.mpr huY
    have hπu : π uL ∈ (Yp.subgroupOf L).map π := ⟨uL, huY', rfl⟩
    have hmem : π (x' * uL * x'⁻¹) ∈ (Yp.subgroupOf L).map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hπx' (π uL)).mp hπu
    obtain ⟨y, hy, hyv⟩ := hmem
    set v : ↥L := x' * uL * x'⁻¹ with hv
    have hzZ : y⁻¹ * v ∈ Z := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyv, inv_mul_cancel]
    obtain ⟨m, hm⟩ := hZ2 _ hzZ
    have hcomm : Commute y (y⁻¹ * v) := by
      have hc := Subgroup.mem_center_iff.mp hzZ y
      exact hc
    have hvyz : v = y * (y⁻¹ * v) := by group
    have hv3 : v ^ 3 = 1 := by
      have : uL ^ 3 = 1 := Subtype.ext hu3
      rw [hv, conj_pow, this]
      simp
    have hvm : v ^ 2 ^ m = y ^ 2 ^ m := by
      conv_lhs => rw [hvyz]
      rw [hcomm.mul_pow, hm, mul_one]
    have hvpow : v = y ^ 4 ^ m := by
      calc v = v ^ 4 ^ m := (pow_four_pow_eq hv3 m).symm
        _ = (v ^ 2 ^ m) ^ 2 ^ m := by
          rw [← pow_mul, ← four_pow_eq]
        _ = y ^ 4 ^ m := by
          rw [hvm, ← pow_mul, ← four_pow_eq]
    have hvY : v ∈ Yp.subgroupOf L := by
      rw [hvpow]
      exact Subgroup.pow_mem _ hy _
    exact Subgroup.mem_subgroupOf.mp hvY
  have hconj' : ∀ w ∈ Subgroup.closure {x : G | x ∈ Yp ∧ x ^ 3 = 1},
      (x' : G) * w * (x' : G)⁻¹ ∈ Yp := by
    intro w hw'
    induction hw' using Subgroup.closure_induction with
    | mem a ha => exact hgenconj a ha
    | one => simp
    | mul a b _ _ iha ihb =>
      have : (x' : G) * (a * b) * (x' : G)⁻¹ = ((x' : G) * a * (x' : G)⁻¹) * ((x' : G) * b * (x' : G)⁻¹) := by
        group
      rw [this]
      exact Yp.mul_mem iha ihb
    | inv a _ iha =>
      have : (x' : G) * a⁻¹ * (x' : G)⁻¹ = ((x' : G) * a * (x' : G)⁻¹)⁻¹ := by group
      rw [this]
      exact Yp.inv_mem iha
  have hconj : ∀ w ∈ Yp, (x' : G) * w * (x' : G)⁻¹ ∈ Yp := fun w hw => hconj' w (hgen3 hw)
  have hx'N : (x' : G) ∈ Subgroup.normalizer (Yp : Set G) := mem_normalizer_of_conj_le hconj
  have hx'3G : (x' : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hx'3
    simpa using this
  have hx'Y : (x' : G) ∈ Yp := hθ _ x'.2 hx'N hx'3G
  have hx'Y' : x' ∈ Yp.subgroupOf L := Subgroup.mem_subgroupOf.mpr hx'Y
  have hπx'H : π x' ∈ (Yp.subgroupOf L).map π := ⟨x', hx'Y', rfl⟩
  have hfin : (π x) = (π x') ^ 2 ^ k := by
    calc π x = (π x) ^ 4 ^ k := (pow_four_pow_eq hx3 k).symm
      _ = ((π x) ^ 2 ^ k) ^ 2 ^ k := by rw [← pow_mul, ← four_pow_eq]
      _ = (π x') ^ 2 ^ k := by rw [hx', map_pow]
  rw [hfin]
  exact Subgroup.pow_mem _ hπx'H _

end Image

section Data

variable {G : Type} [Group G] [Finite G]

theorem elConfigPlus_of_data {S Q V₂ Yp L : Subgroup G} [Group.IsPerfect ↥L]
    (hZ : centerOf L = CFSG.Open.pCoreOf 2 L) (hQsyl : IsSylowTwoOf Q L)
    (hSfin : IsPGroup 2 ↥S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hSN : S ≤ Subgroup.normalizer (Yp : Set G)) (hQS : Q ≤ S)
    (hYL : Yp ≤ L) (hV2Y : V₂ ≤ Yp) (hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V₂ : Set G)) (hVQ : V₂ ≤ Q)
    (hV4 : Nat.card V₂ = 4) (hV2sq : ∀ v ∈ V₂, v * v = 1)
    (hfix : ∀ x ∈ V₂, (∀ b ∈ Yp, b * x = x * b) → x = 1)
    (hy : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y)
    (hs : ∃ s ∈ S, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G))
    (hY3 : ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp)
    (hgen3 : Yp ≤ Subgroup.closure {x : G | x ∈ Yp ∧ x ^ 3 = 1})
    (hθ : ∀ x ∈ L, x ∈ Subgroup.normalizer (Yp : Set G) → x ^ 3 = 1 → x ∈ Yp) :
    ElConfigPlus (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : Q ≤ L := hQsyl.1
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  obtain ⟨y₀, hy₀Y, hy₀3, hy₀n⟩ := hy
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQsyl
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hTsyl : IsSylowTwoOf ((Q.subgroupOf L).map π) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hcomm : ∀ (a₀ : ↥L) (v₀ : ↥L), (a₀ : G) ∈ Yp → (v₀ : G) ∈ V₂ →
      π a₀ * π v₀ = π v₀ * π a₀ → (a₀ : G) * v₀ = v₀ * a₀ := by
    intro a₀ v₀ ha hv hc
    have h1 : π (a₀ * v₀ * a₀⁻¹ * v₀⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h2 : a₀ * v₀ * a₀⁻¹ * v₀⁻¹ ∈ Z := by
      rw [← hker]
      exact h1
    have h3 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) ∈ centerOf L :=
      SBc2.mem_centerOf_iff_center.mpr h2
    have h4 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) ∈ V₂ := by
      have h5 : (a₀ : G) * v₀ * (a₀ : G)⁻¹ ∈ V₂ :=
        (Subgroup.mem_normalizer_iff.mp (hYN ha) (v₀ : G)).mp hv
      have h6 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) =
          ((a₀ : G) * v₀ * (a₀ : G)⁻¹) * (v₀ : G)⁻¹ := rfl
      rw [h6]
      exact V₂.mul_mem h5 (V₂.inv_mem hv)
    have h7 := hVz _ h4 h3
    calc (a₀ : G) * v₀ = (a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) * (v₀ * a₀) := by
          rw [show (((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) * ((v₀ : G) * a₀)) = (a₀ : G) * v₀ by
            simp [mul_assoc]]
      _ = v₀ * a₀ := by rw [h7, one_mul]
  have hKcard : Nat.card (V₂.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV2L).toEquiv
  have hinj : Function.Injective (π.comp (V₂.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Z := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  have hVbar4 : Nat.card ((V₂.subgroupOf L).map π) = 4 := by
    have h1 : (π.comp (V₂.subgroupOf L).subtype).range = (V₂.subgroupOf L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  have hVbar2 : ∀ v ∈ (V₂.subgroupOf L).map π, v * v = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have hxV : (x₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hx₀
    have : x₀ * x₀ = 1 := Subtype.ext (hV2sq _ hxV)
    rw [this, map_one]
  have hfixbar : ∀ v ∈ (V₂.subgroupOf L).map π,
      (∀ h ∈ (Yp.subgroupOf L).map π, h * v = v * h) → v = 1 := by
    rintro _ ⟨v₀, hv₀, rfl⟩ hc
    have hv : (v₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hv₀
    have : v₀ = 1 := by
      have h1 : (v₀ : G) = 1 := by
        refine hfix _ hv fun b hb => ?_
        have := hcomm ⟨b, hYL hb⟩ v₀ hb hv (hc _ ⟨⟨b, hYL hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)
        exact this
      exact Subtype.ext h1
    rw [this, map_one]
  have hybar : ∃ y ∈ (Yp.subgroupOf L).map π, y ^ 3 = 1 ∧
      ¬ ∀ v ∈ (V₂.subgroupOf L).map π, y * v = v * y := by
    refine ⟨π ⟨y₀, hYL hy₀Y⟩, ⟨⟨y₀, hYL hy₀Y⟩, Subgroup.mem_subgroupOf.mpr hy₀Y, rfl⟩, ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨y₀, hYL hy₀Y⟩ : ↥L) ^ 3 = 1 := Subtype.ext hy₀3
      rw [this, map_one]
    · intro hall
      apply hy₀n
      intro v hv
      exact hcomm ⟨y₀, hYL hy₀Y⟩ ⟨v, hV2L hv⟩ hy₀Y hv
        (hall _ ⟨⟨v, hV2L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩)
  have hSq : S ≤ Subgroup.normalizer (L : Set G) := hSL
  let ρ : ↥(S) →* MulAut (↥L ⧸ Z) :=
    (PerfectAutomorphisms.centerQuotientHom ↥L).comp
      ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hSq))
  have hρ : ∀ (s : ↥(S)) (l : ↥L),
      ρ s (π l) = π (Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) l) := fun s l =>
    PerfectAutomorphisms.onCenterQuotient_apply_mk _ l
  have hρcoe : ∀ (s : ↥(S)) (l : ↥L),
      ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) l : ↥L) : G) =
        (s : G) * l * (s : G)⁻¹ := fun s l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hSq s) l
  have hρne : ∀ s : ↥(S), (s : G) ∉ Subgroup.centralizer (L : Set G) → ρ s ≠ 1 := by
    intro s hs h1
    apply hs
    have h2 : Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) = 1 :=
      PerfectAutomorphisms.centerQuotientHom_injective ↥L (h1.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 := DFunLike.congr_fun h2 ⟨l, hl⟩
    have h4 := congrArg Subtype.val h3
    rw [hρcoe] at h4
    simp only [MulAut.one_apply] at h4
    show l * (s : G) = (s : G) * l
    calc l * (s : G) = ((s : G) * l * (s : G)⁻¹) * (s : G) := by rw [h4]
      _ = (s : G) * l := by group
  obtain ⟨s₀, hs₀S, hs₀C, hs₀L⟩ := hs
  let W : Subgroup ↥(S) := (Subgroup.centralizer (Yp : Set G)).subgroupOf (S)
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Subgroup.centralizer (Yp : Set G) := hn
    show ((g * n * g⁻¹ : ↥(S)) : G) ∈ Subgroup.centralizer (Yp : Set G)
    rw [Subgroup.mem_centralizer_iff] at hn' ⊢
    intro y hy
    have hy' : (g : G)⁻¹ * y * (g : G) ∈ Yp := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (g⁻¹ : ↥(S)).2) y).mp
      simpa using this hy
    have h1 := hn' _ hy'
    show y * ((g : G) * n * (g : G)⁻¹) = ((g : G) * n * (g : G)⁻¹) * y
    calc y * ((g : G) * n * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * y * (g : G)) * n) * (g : G)⁻¹ := by group
      _ = (g : G) * (n * ((g : G)⁻¹ * y * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * n * (g : G)⁻¹) * y := by group
  have hRp : IsPGroup 2 ↥ρ.range := hSfin.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hRfin : Finite ↥ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hRnil : Group.IsNilpotent ↥ρ.range := hRp.isNilpotent
  have hWpn : (W.map ρ.rangeRestrict).Normal := hWn.map _ ρ.rangeRestrict_surjective
  have hWpne : W.map ρ.rangeRestrict ≠ ⊥ := by
    intro hb
    have hmem : ρ.rangeRestrict ⟨s₀, hs₀S⟩ ∈ W.map ρ.rangeRestrict :=
      ⟨⟨s₀, hs₀S⟩, hs₀C, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    apply hρne ⟨s₀, hs₀S⟩ hs₀L
    exact congrArg Subtype.val hmem
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hWpne
  obtain ⟨⟨ζ', hζ'W, hζ'Z⟩, hζ'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  obtain ⟨w, hwW, hwζ⟩ := hζ'W
  have hwC : (w : G) ∈ Subgroup.centralizer (Yp : Set G) := hwW
  have hζρ : (ζ' : MulAut (↥L ⧸ Z)) = ρ w := (congrArg Subtype.val hwζ).symm
  have hζne : (ζ' : MulAut (↥L ⧸ Z)) ≠ 1 := fun h1 => hζ'1 (Subtype.ext (Subtype.ext h1))
  have hζH : ∀ h ∈ (Yp.subgroupOf L).map π, (ζ' : MulAut (↥L ⧸ Z)) h = h := by
    rintro _ ⟨l₀, hl₀, rfl⟩
    have hl₀Y : (l₀ : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hl₀
    rw [hζρ, hρ]
    congr 1
    refine Subtype.ext ?_
    rw [hρcoe]
    have hc := Subgroup.mem_centralizer_iff.mp hwC (l₀ : G) hl₀Y
    calc (w : G) * (l₀ : G) * (w : G)⁻¹ = (l₀ : G) * (w : G) * (w : G)⁻¹ := by rw [← hc]
      _ = (l₀ : G) := by group
  have hζT : ∀ t ∈ (Q.subgroupOf L).map π, (ζ' : MulAut (↥L ⧸ Z)) t = t := by
    rintro _ ⟨q₀, hq₀, rfl⟩
    have hq₀Q : (q₀ : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq₀
    let sq : ↥(S) := ⟨(q₀ : G), hQS hq₀Q⟩
    have hρsq : ∀ x : ↥L ⧸ Z, ρ sq x = π q₀ * x * (π q₀)⁻¹ := by
      intro x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Z x
      have e : Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq sq) l = q₀ * l * q₀⁻¹ :=
        Subtype.ext (hρcoe sq l)
      show ρ sq (π l) = π q₀ * π l * (π q₀)⁻¹
      rw [hρ, e, map_mul, map_mul, map_inv]
    have hcomm' := Subgroup.mem_center_iff.mp hζ'Z ⟨ρ sq, ⟨sq, rfl⟩⟩
    have hcomm'' : ρ sq * (ζ' : MulAut (↥L ⧸ Z)) = (ζ' : MulAut (↥L ⧸ Z)) * ρ sq :=
      congrArg Subtype.val hcomm'
    have hd : (π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) ∈ Subgroup.center (↥L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := DFunLike.congr_fun hcomm'' ((ζ' : MulAut (↥L ⧸ Z)).symm y)
      simp only [MulAut.mul_apply, hρsq, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      calc y * ((π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀))
          = (π q₀)⁻¹ * (π q₀ * y * (π q₀)⁻¹) * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) := by group
        _ = (π q₀)⁻¹ * ((ζ' : MulAut (↥L ⧸ Z)) (π q₀) * y *
              ((ζ' : MulAut (↥L ⧸ Z)) (π q₀))⁻¹) * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) := by
          rw [h1]
        _ = ((π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀)) * y := by group
    rw [center_quot_eq_bot, Subgroup.mem_bot] at hd
    exact (inv_mul_eq_one.mp hd).symm
  refine ⟨(Q.subgroupOf L).map π, (V₂.subgroupOf L).map π, (Yp.subgroupOf L).map π,
    (ζ' : MulAut (↥L ⧸ Z)), hTsyl, ?_⟩
  obtain ⟨P, hPH, hHP, hP2, hP3⟩ := quot3_image hYL hY3
  exact
    { toElData := ⟨Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
          (hVQ (Subgroup.mem_subgroupOf.mp hx)), hVbar4, hVbar2,
        quot_normalizes hV2L hQV,
        Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
          (hV2Y (Subgroup.mem_subgroupOf.mp hx)),
        quot_normalizes hV2L hYN,
        quot_normalizes hYL (fun q hq => hSN (hQS hq)), hybar, hfixbar, hζne, hζT, hζH⟩
      quot3 := ⟨P, hPH, hHP, hP2, hP3⟩
      theta := theta_image hZ hYL hgen3 hθ }

end Data

section Ctx

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pow_three_mem_pCoreOf {Yp : Subgroup G} (h : ∀ q : OTwoQuot Yp, q ^ 3 = 1) :
    ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp := by
  intro y hy
  have h1 : (QuotientGroup.mk (⟨y, hy⟩ : ↥Yp) : OTwoQuot Yp) ^ 3 = 1 := h _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  exact ⟨⟨y, hy⟩ ^ 3, h1, rfl⟩

omit [Finite G] in
theorem pow_three_of_isElemAbelianOfRank {Q : Type*} [Group Q] (h : IsElemAbelianOfRank 3 2 Q) (q : Q) :
    q ^ 3 = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  ext i
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp [h3]

omit [Finite G] in
theorem exp3_of_struct {Yp : Subgroup G}
    (h : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∨ IsPOnePlusTwo 3 (OTwoQuot Yp)) :
    ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp := by
  refine pow_three_mem_pCoreOf fun q => ?_
  rcases h with h | h
  · exact pow_three_of_isElemAbelianOfRank h q
  · exact h.2.2 q

theorem theta_data {T M V₁ Yp I L : Subgroup G} (hLI : L ≤ I) (f : Facts153 T M V₁ Yp I) :
    Yp ≤ Subgroup.closure {x : G | x ∈ Yp ∧ x ^ 3 = 1} ∧
      ∀ x ∈ L, x ∈ Subgroup.normalizer (Yp : Set G) → x ^ 3 = 1 → x ∈ Yp := by
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [f.theta]
    rw [thetaOf, Subgroup.closure_le]
    intro x hx
    have hxY : x ∈ Yp := by
      rw [f.theta]
      exact Subgroup.subset_closure hx
    refine Subgroup.subset_closure ⟨hxY, ?_⟩
    rw [← hx.2]
    exact pow_orderOf_eq_one x
  · intro x hxL hxN hx3
    by_cases hx1 : x = 1
    · rw [hx1]; exact Yp.one_mem
    have hxM : x ∈ M ⊓ I := by
      rw [← f.norm_eq]
      exact ⟨hLI hxL, hxN⟩
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    rw [f.theta]
    exact Subgroup.subset_closure ⟨hxM, hord⟩

theorem elConfigPlus_of_ctx1 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) :
    ElConfigPlus (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hq : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hperf : Group.IsPerfect ↥L := hq.1
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hMIV : M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) :=
    R3c8.MI_le_normalizer_V₂ hh o.b_V1 o.b_V2.1 c.facts.norm_eq
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs =>
    hMIY ⟨hSM hs, hSI hs⟩
  have hV2Y : V₂ ≤ Yp := by
    have h1 : ⁅V₂, Yp⁆ ≤ Yp := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hvN : v ∈ Subgroup.normalizer (Yp : Set G) := hMIY ⟨hSM (hV2S hv), hSI (hV2S hv)⟩
      have h2 : v * y * v⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp hvN y).mp hy
      have : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
      rw [this]
      exact Yp.mul_mem h2 (Yp.inv_mem hy)
    rwa [o.b_V2.1] at h1
  have hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy => hMIV ⟨hYpM hy, hYpI hy⟩
  obtain ⟨eV⟩ := o.b_V2.2
  have hV4 : Nat.card V₂ = 4 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hV2sq : ∀ v ∈ V₂, v * v = 1 := by
    intro v hv
    have h1 : eV ⟨v, hv⟩ * eV ⟨v, hv⟩ = 1 := by
      ext i
      simp
      exact CharTwo.add_self_eq_zero _
    have : (⟨v, hv⟩ : ↥V₂) * ⟨v, hv⟩ = 1 := eV.injective (by rw [map_mul, h1, map_one])
    simpa using congrArg Subtype.val this
  obtain ⟨a, hcard⟩ : ∃ a : ℕ, Nat.card ↥Yp = 2 ^ a * 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
    refine ⟨a, ?_⟩
    have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 := o.a_ord
    rw [h1, ha, h2, mul_comm]
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    apply le_antisymm
    · conv_lhs => rw [o.a_eq]
      rw [oPrimeResidualOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [o.a_eq]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    have h1 : ⁅Yp, V₂⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h2 : ⁅V₂, Yp⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
    rw [o.b_V2.1] at h2
    have : Nat.card V₂ = 1 := by rw [h2]; simp
    omega
  have hfix : ∀ x ∈ V₂, (∀ b ∈ Yp, b * x = x * b) → x = 1 :=
    fixed_eq_one_of_gen hV4 hgen hYN hact
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Q := le_inf hV2S hV2L
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  have hQL : Q ≤ L := inf_le_right
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hY3e : ∀ x ∈ Yp, (∃ k : ℕ, orderOf x = 3 ^ k) → x ^ 3 = 1 := by
    intro x hx ⟨k, hk⟩
    have hd : orderOf x ∣ 2 ^ a * 3 := hcard ▸ Subgroup.orderOf_dvd_natCard Yp hx
    have hcop : Nat.Coprime (orderOf x) (2 ^ a) := by
      rw [hk]
      exact Nat.Coprime.pow_left k (Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2))
    exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hd)
  obtain ⟨y₀, hy₀Y, hy₀3, hy₀n⟩ : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [hgen, Subgroup.closure_le]
    intro x hx
    obtain ⟨hxY, hxk⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcon x hxY (hY3e x hxY hxk) v hv).symm
  have hy : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := ⟨y₀, hy₀Y, hy₀3, hy₀n⟩
  obtain ⟨s₀, hs₀S, hs₀C, hs₀L⟩ : ∃ s ∈ Sgp153 T V₁, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    apply o.c_cent
    apply le_antisymm
    · intro s hs
      exact ⟨hs.1, hcon s hs.1 hs.2⟩
    · intro s hs
      exact ⟨hs.1, Subgroup.centralizer_le (fun x hx => hYL hx) hs.2⟩
  have hs : ∃ s ∈ Sgp153 T V₁, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G) := ⟨s₀, hs₀S, hs₀C, hs₀L⟩
  have hY3 : ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp := by
    refine pow_three_mem_pCoreOf fun q => ?_
    have := pow_card_eq_one' (G := OTwoQuot Yp) (x := q)
    rwa [o.a_ord] at this
  obtain ⟨hgen3, hθ⟩ := theta_data hLI c.facts
  exact elConfigPlus_of_data hZ hQsyl hSyl.2.1 hSL hSN hQS hYL hV2Y hYN
    (fun q hq => hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩) hVQ hV4 hV2sq hfix hy hs hY3 hgen3 hθ

theorem elConfigPlus_of_ctx2 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L)
    (hU : IsUniqueM (Y153 Mc M ⊔ Sgp153 T V₁) M ∧
      Yp = oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))) :
    ElConfigPlus (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hq : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hperf : Group.IsPerfect ↥L := hq.1
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  obtain ⟨hYN, hfix, hV2Y, hMIV⟩ := R3c10.ctx2_facts h113 c
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs =>
    hMIY ⟨hSM hs, hSI hs⟩
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV2sq : ∀ x ∈ V₂, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₂ hx)
    rw [← sq]
    exact this
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVQ : V₂ ≤ Sgp153 T V₁ ⊓ L := le_inf hV2S hV2L
  have hQS : Sgp153 T V₁ ⊓ L ≤ Sgp153 T V₁ := inf_le_left
  have hQV : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq =>
    hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  obtain ⟨y, hyO, -, hyfpf⟩ := hh.hyp.exists_Yplus_fpf h113 hh.decomp
  have hyYp : y ∈ Yp := by
    rw [hU.2]
    exact hyO
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ orderOf x = 3} := by
    apply le_antisymm
    · conv_lhs => rw [c.facts.theta]
      rw [thetaOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [c.facts.theta]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₂, u ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : V₂ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
      rw [this, Subgroup.card_bot] at hV4
      omega
    apply hyfpf u hu hu1
    have := Subgroup.mem_centralizer_iff.mp (hle hyYp) u hu
    calc y * u * y⁻¹ = (u * y) * y⁻¹ := by rw [this]
      _ = u := by group
  have hy : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [hgen, Subgroup.closure_le]
    intro x hx
    obtain ⟨hxY, hx3⟩ := hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcon x hxY (by rw [← hx3]; exact pow_orderOf_eq_one x) v hv).symm
  have hNV1 : Subgroup.normalizer (V₁ : Set G) ≤ M :=
    (Hyp153.normalizer_V_le h113 hh.hyp hh.decomp hU.1).1
  have hVS : VZ T M ≤ Sgp153 T V₁ := by
    intro v hv
    refine ⟨hh.hyp.VZ_le_T hv, A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
    have hc' := congrArg Subtype.val
      (hh.hyp.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨k, hh.decomp.le₁ hk⟩)
    have : v * k * v⁻¹ = k := by
      have h1 : v * k = k * v := hc'
      rw [h1]
      group
    rw [this]
    exact hk
  have hV1S : V₁ ≤ Sgp153 T V₁ := fun v hv => hVS (hh.decomp.le₁ hv)
  have hYV1 : ∀ v ∈ V₁, v ∈ Subgroup.centralizer (Yp : Set G) := fun v hv => by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : b ∈ Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) := by
      have : b ∈ oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) := hU.2 ▸ hb
      exact oTwoUpper_le _ this
    exact (Subgroup.mem_centralizer_iff.mp hb'.2 v hv).symm
  have hs : ∃ s ∈ Sgp153 T V₁, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hcon
    push Not at hcon
    apply c.c33.not_le
    have hLC : L ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro l hl
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (Subgroup.mem_centralizer_iff.mp (hcon v (hV1S hv) (hYV1 v hv)) l hl).symm
    exact hLC.trans ((Subgroup.centralizer_le_normalizer _).trans hNV1)
  obtain ⟨hgen3', hθ⟩ := theta_data hLI c.facts
  exact elConfigPlus_of_data hZ hQsyl hSyl.2.1 hSL hSN hQS hYL hV2Y hYN hQV hVQ hV4 hV2sq hfix hy hs
    (exp3_of_struct c.facts11.struct_Yp) hgen3' hθ


end Ctx

end CFSG.Quasithin.SzN27
