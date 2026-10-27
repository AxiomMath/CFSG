module

public import CFSG.Quasithin.EmptyFaithful.S146E4
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.EmptyFaithful.S146Six2
public import CFSG.Quasithin.EmptyFaithful.S146xU1Orb

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section SecRhoEq

variable {G : Type} [Group G] {Z U X : Subgroup G}

theorem secRho_apply_tildeElt_eq_iff (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hU : U ≤ Subgroup.normalizer (Z : Set G))
    (x : ↥X) {a b : G} (ha : a ∈ U) (hb : b ∈ U) :
    secRho hXZ hXU x (tildeElt hU a ha) = tildeElt hU b hb ↔
      ((x : G) * a * (x : G)⁻¹)⁻¹ * b ∈ Z := by
  have key : ∀ w : ↥(tildeOf Z U), (secRho hXZ hXU x w : SecQuot (Subgroup.normalizer (Z : Set G)) Z) =
      secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x) * w *
        (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x))⁻¹ :=
    fun w => secRho_coe hXZ hXU x w
  have hconj : secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x) *
      secMk (Subgroup.normalizer (Z : Set G)) Z ⟨a, hU ha⟩ *
        (secMk (Subgroup.normalizer (Z : Set G)) Z (Subgroup.inclusion hXZ x))⁻¹ =
      secMk (Subgroup.normalizer (Z : Set G)) Z
        (Subgroup.inclusion hXZ x * ⟨a, hU ha⟩ * (Subgroup.inclusion hXZ x)⁻¹) := by
    simp only [map_mul, map_inv]
  constructor
  · intro h
    have h1 := congrArg
      (fun w : ↥(tildeOf Z U) => (w : SecQuot (Subgroup.normalizer (Z : Set G)) Z)) h
    simp only [key, tildeElt, hconj] at h1
    have := secMk_eq_secMk_iff.mp h1
    simpa using this
  · intro h
    apply Subtype.ext
    simp only [key, tildeElt, hconj]
    refine secMk_eq_secMk_iff.mpr ?_
    simpa using h

end SecRhoEq

section TZero

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem mem_tZero_iff {u x : G} (hu : u ∈ mcOf T) (hxT : x ∈ T) :
    x ∈ tZero T u ↔ x * u * x⁻¹ * u⁻¹ ∈ Zz := by
  constructor
  · intro h
    exact h.2.2 u (Subgroup.mem_zpowers u)
  · intro h
    exact mem_centralizerMod_zpowers hxT
      (Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hxT))
      (fun z hz => S146T.comm_Z hu hz) h

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_centralizerMod {u h c : G}
    (hh : h ∈ centralizerMod Zz (mcOf T) (Subgroup.zpowers u))
    (hc : c ∈ mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) :
    h * c * h⁻¹ ∈ mcOf T ⊓ Subgroup.centralizer ({u} : Set G) := by
  obtain ⟨hhH, -, hhz⟩ := hh
  have hz := hhz u (Subgroup.mem_zpowers u)
  set z := h * u * h⁻¹ * u⁻¹ with hzdef
  have hzc : ∀ y ∈ mcOf T, Commute y z := fun y hy => S146T.comm_Z hy hz
  refine ⟨(mcOf T).mul_mem ((mcOf T).mul_mem hhH hc.1) ((mcOf T).inv_mem hhH),
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
  have hzu : z * u = h * u * h⁻¹ := by rw [hzdef]; group
  have hzh : h⁻¹ * z = z * h⁻¹ := (hzc _ ((mcOf T).inv_mem hhH)).eq
  have hw : h⁻¹ * u * h = z⁻¹ * u := by
    have h1 : z * (h⁻¹ * u * h) = u := by
      calc z * (h⁻¹ * u * h) = (z * h⁻¹) * u * h := by group
        _ = (h⁻¹ * z) * u * h := by rw [← hzh]
        _ = h⁻¹ * (z * u) * h := by group
        _ = h⁻¹ * (h * u * h⁻¹) * h := by rw [hzu]
        _ = u := by group
    rw [eq_inv_mul_iff_mul_eq]
    exact h1
  have hcc : Commute c z⁻¹ := (hzc c hc.1).inv_right
  have hhc : Commute h z⁻¹ := (hzc h hhH).inv_right
  have hcu' : c * u * c⁻¹ = u := by rw [hcu]; group
  have e : (h * c * h⁻¹) * u * (h * c * h⁻¹)⁻¹ = u := by
    calc (h * c * h⁻¹) * u * (h * c * h⁻¹)⁻¹ = h * (c * (h⁻¹ * u * h) * c⁻¹) * h⁻¹ := by group
      _ = h * (c * (z⁻¹ * u) * c⁻¹) * h⁻¹ := by rw [hw]
      _ = h * (z⁻¹ * (c * u * c⁻¹)) * h⁻¹ := by
          rw [show c * (z⁻¹ * u) * c⁻¹ = (c * z⁻¹) * u * c⁻¹ by group, hcc.eq]; group
      _ = h * (z⁻¹ * u) * h⁻¹ := by rw [hcu']
      _ = (h * z⁻¹) * u * h⁻¹ := by group
      _ = (z⁻¹ * h) * u * h⁻¹ := by rw [hhc.eq]
      _ = z⁻¹ * (h * u * h⁻¹) := by group
      _ = z⁻¹ * (z * u) := by rw [hzu]
      _ = u := by group
  exact mul_inv_eq_iff_eq_mul.mp e

end TZero

section Tail

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

theorem Setting146.isSylowTwoOf_tU_of_odd (S : Setting146 G T M) {u : G} (huG : u ∈ mcOf T)
    (hodd : ¬ 2 ∣ (tZero T u).relIndex (centralizerMod Zz (mcOf T) (Subgroup.zpowers u))) :
    IsSylowTwoOf (tU T u) (mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have hTH : T ≤ mcOf T := S.isSylowTwoOf_mcOf.1
  have hT2 : IsPGroup 2 T := S.hyp.sylow.1
  set H₂ := centralizerMod Zz (mcOf T) (Subgroup.zpowers u) with hH₂
  set N : Subgroup G := mcOf T ⊓ Subgroup.centralizer ({u} : Set G) with hNdef
  have hNH₂ : N ≤ H₂ := by
    intro c hc
    have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    refine mem_centralizerMod_zpowers hc.1 (S.normalizer_Z.ge hc.1)
      (fun z hz => S146T.comm_Z huG hz) ?_
    rw [show c * u * c⁻¹ * u⁻¹ = 1 by rw [hcu]; group]
    exact Subgroup.one_mem _
  have hT₀H₂ : tZero T u ≤ H₂ := fun x hx => ⟨hTH hx.1, hx.2.1, hx.2.2⟩
  have hNn : ∀ t ∈ tZero T u, ∀ n ∈ N, t * n * t⁻¹ ∈ N := fun t ht n hn =>
    conj_mem_centralizer_of_mem_centralizerMod (hT₀H₂ ht) hn
  have hTu : tZero T u ⊓ N = tU T u := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, hx.2.2⟩
    · intro hx
      have hxc : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
      refine ⟨(mem_tZero_iff huG hx.1).mpr ?_, hTH hx.1, hx.2⟩
      rw [show x * u * x⁻¹ * u⁻¹ = 1 by rw [hxc]; group]
      exact Subgroup.one_mem _
  have hodd₃ := not_two_dvd_relIndex_inf_normal hNH₂ hT₀H₂ hNn hodd
  rw [hTu] at hodd₃
  exact ⟨fun x hx => ⟨hTH hx.1, hx.2⟩, hT2.to_le inf_le_left, hodd₃⟩

theorem Setting146.isSylowTwoOf_tU_of_normalizes (S : Setting146 G T M) {u : G} {V L : Subgroup G}
    (huG : u ∈ mcOf T)
    (hH₂V : centralizerMod Zz (mcOf T) (Subgroup.zpowers u) ≤ Subgroup.normalizer (V : Set G))
    (hLH : L ≤ mcOf T) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hHL : ∀ h ∈ mcOf T, ∃ a ∈ L, ∃ b ∈ T, h = a * b)
    (hN : T ⊓ Subgroup.normalizer (V : Set G) ≤ tZero T u) :
    IsSylowTwoOf (tU T u) (mcOf T ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have hTH : T ≤ mcOf T := S.isSylowTwoOf_mcOf.1
  set H₂ := centralizerMod Zz (mcOf T) (Subgroup.zpowers u) with hH₂
  set H₁ : Subgroup G := mcOf T ⊓ Subgroup.normalizer (V : Set G) with hH₁
  have hH₁H : H₁ ≤ mcOf T := inf_le_left
  have hH₂H₁ : H₂ ≤ H₁ := le_inf (centralizerMod_le_left _ _ _) hH₂V
  have hT₀eq : tZero T u = T ⊓ H₂ := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, hTH hx.1, hx.2.1, hx.2.2⟩
    · intro hx
      exact ⟨hx.1, hx.2.2.1, hx.2.2.2⟩
  have hTH₂ : T ⊓ H₁ ≤ H₂ := by
    intro x hx
    have hx' : x ∈ tZero T u := hN ⟨hx.1, hx.2.2⟩
    exact ⟨hTH hx.1, hx'.2.1, hx'.2.2⟩
  have hmul : ∀ h ∈ mcOf T, ∃ a ∈ H₁, ∃ b ∈ T, h = a * b := by
    intro h hh
    obtain ⟨a, ha, b, hb, hab⟩ := hHL h hh
    exact ⟨a, ⟨hLH ha, hLV ha⟩, b, hb, hab⟩
  have hodd : ¬ 2 ∣ (tZero T u).relIndex H₂ := by
    rw [hT₀eq]
    exact not_two_dvd_relIndex_inf_of_forall_mul hH₁H hH₂H₁ hTH₂ hmul S.isSylowTwoOf_mcOf.2.2
  exact S.isSylowTwoOf_tU_of_odd huG hodd

end Tail

end CFSG.Quasithin
