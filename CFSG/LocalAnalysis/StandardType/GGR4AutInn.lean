module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem r4h_eq_one_of_mem_center_pow_eq_one {Y : Type} [Group Y] {p : ℕ}
    (hZ : ∀ g ∈ Subgroup.center Y, Nat.Coprime p (orderOf g)) {z : Y}
    (hz : z ∈ Subgroup.center Y) (hzpow : z ^ p = 1) : z = 1 := by
  have hdvd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzpow
  have hcop : Nat.Coprime p (orderOf z) := hZ z hz
  have h1 : orderOf z = 1 := hcop.symm.eq_one_of_dvd hdvd
  exact orderOf_eq_one_iff.mp h1

private theorem r4h_conj_eq_one_of_mem_subgroupOf {G : Type} [Group G] {p : ℕ}
    {X BX : Subgroup G} (hAb : IsElemAbelian p BX)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    {z : ↥X} (hz : z ∈ BX.subgroupOf X)
    (h : (MulAut.conj : ↥X →* MulAut ↥X) z = 1) : z = 1 := by
  have hzBX : (z : G) ∈ BX := Subgroup.mem_subgroupOf.mp hz
  have hzcenter : z ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : (MulAut.conj : ↥X →* MulAut ↥X) z y = y := by
      simpa using DFunLike.congr_fun h y
    rw [MulAut.conj_apply] at hy
    have hzy : z * y = y * z := by
      calc z * y = (z * y * z⁻¹) * z := by group
        _ = y * z := by rw [hy]
    exact hzy.symm
  have hzpow : z ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hAb.2 (z : G) hzBX)
  exact r4h_eq_one_of_mem_center_pow_eq_one hZ hzcenter hzpow

private theorem r4h_conj_injective_on {G : Type} [Group G] {p : ℕ}
    {X BX : Subgroup G} (hAb : IsElemAbelian p BX)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g)) :
    ∀ y ∈ BX.subgroupOf X, ∀ z ∈ BX.subgroupOf X,
      (MulAut.conj : ↥X →* MulAut ↥X) y = (MulAut.conj : ↥X →* MulAut ↥X) z →
      y = z := by
  intro y hy z hz hyz
  have hmem : y * z⁻¹ ∈ BX.subgroupOf X :=
    (BX.subgroupOf X).mul_mem hy ((BX.subgroupOf X).inv_mem hz)
  have hone : (MulAut.conj : ↥X →* MulAut ↥X) (y * z⁻¹) = 1 := by
    rw [map_mul, map_inv, hyz, mul_inv_cancel]
  have h1 : y * z⁻¹ = 1 := r4h_conj_eq_one_of_mem_subgroupOf hAb hZ hmem hone
  calc y = y * z⁻¹ * z := by group
    _ = 1 * z := by rw [h1]
    _ = z := by group

private theorem r4h_conj_mem_A {G : Type} [Group G] {X BX : Subgroup G}
    {n : G} (hnX : n ∈ X) (hnN : n ∈ Subgroup.normalizer (BX : Set G))
    {a : MulAut ↥X}
    (ha : a ∈ (BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X)) :
    (MulAut.conj : ↥X →* MulAut ↥X) ⟨n, hnX⟩ * a *
        ((MulAut.conj : ↥X →* MulAut ↥X) ⟨n, hnX⟩)⁻¹ ∈
      (BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X) := by
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp ha
  rw [← hyeq]
  refine Subgroup.mem_map.mpr ⟨⟨n, hnX⟩ * y * ⟨n, hnX⟩⁻¹, ?_, ?_⟩
  · apply Subgroup.mem_subgroupOf.mpr
    have hyBX : (y : G) ∈ BX := Subgroup.mem_subgroupOf.mp hy
    have h := (Subgroup.mem_normalizer_iff.mp hnN (y : G)).mp hyBX
    simpa using h
  · rw [map_mul, map_mul, map_inv]

private theorem r4h_conj_mem_normalizer_A {G : Type} [Group G] {X BX : Subgroup G}
    {n : G} (hnX : n ∈ X) (hnN : n ∈ Subgroup.normalizer (BX : Set G)) :
    (MulAut.conj : ↥X →* MulAut ↥X) ⟨n, hnX⟩ ∈
      Subgroup.normalizer
        (((BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X)) : Set (MulAut ↥X)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact r4h_conj_mem_A hnX hnN ha
  · intro ha
    have hnX' : n⁻¹ ∈ X := X.inv_mem hnX
    have hnN' : n⁻¹ ∈ Subgroup.normalizer (BX : Set G) := Subgroup.inv_mem _ hnN
    have h1 := r4h_conj_mem_A hnX' hnN' ha
    have h2 : (MulAut.conj : ↥X →* MulAut ↥X) ⟨n⁻¹, hnX'⟩ =
        ((MulAut.conj : ↥X →* MulAut ↥X) ⟨n, hnX⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [h2] at h1
    convert h1 using 1
    group

private theorem r4h_conj_mem_BX {G : Type} [Group G] {p : ℕ}
    {X BX : Subgroup G} (hBX : BX ≤ X) (hAb : IsElemAbelian p BX)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    {m : ↥X}
    (hm : (MulAut.conj : ↥X →* MulAut ↥X) m ∈
      Subgroup.normalizer
        (((BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X)) : Set (MulAut ↥X)))
    {b : G} (hb : b ∈ BX) : (m : G) * b * (m : G)⁻¹ ∈ BX := by
  let y0 : ↥X := ⟨b, hBX hb⟩
  have hy0pow : y0 ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hAb.2 b hb)
  let w : ↥X := ⟨(m : G) * b * (m : G)⁻¹,
    X.mul_mem (X.mul_mem m.2 (hBX hb)) (X.inv_mem m.2)⟩
  have hwconj : w = m * y0 * m⁻¹ := Subtype.ext rfl
  have hwp : w ^ p = 1 := by
    rw [hwconj, conj_pow, hy0pow]
    group
  have hy0 : y0 ∈ BX.subgroupOf X := Subgroup.mem_subgroupOf.mpr hb
  have hconjy0 : (MulAut.conj : ↥X →* MulAut ↥X) y0 ∈
      (BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X) :=
    Subgroup.mem_map.mpr ⟨y0, hy0, rfl⟩
  have hw : (MulAut.conj : ↥X →* MulAut ↥X) w ∈
      (BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X) := by
    have h := (Subgroup.mem_normalizer_iff.mp hm
      ((MulAut.conj : ↥X →* MulAut ↥X) y0)).mp hconjy0
    have hwconj' : (MulAut.conj : ↥X →* MulAut ↥X) w =
        (MulAut.conj : ↥X →* MulAut ↥X) m * (MulAut.conj : ↥X →* MulAut ↥X) y0 *
          ((MulAut.conj : ↥X →* MulAut ↥X) m)⁻¹ := by
      rw [show w = m * y0 * m⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    exact hwconj' ▸ h
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hw
  let z : ↥X := y⁻¹ * w
  have hzcenter : z ∈ Subgroup.center ↥X := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hconjz : (MulAut.conj : ↥X →* MulAut ↥X) z = 1 := by
      dsimp only [z]
      rw [map_mul, map_inv, hyeq, inv_mul_cancel]
    have hu : (MulAut.conj : ↥X →* MulAut ↥X) z u = u := by
      simpa using DFunLike.congr_fun hconjz u
    rw [MulAut.conj_apply] at hu
    have hzu : z * u = u * z := by
      calc z * u = (z * u * z⁻¹) * z := by group
        _ = u * z := by rw [hu]
    exact hzu.symm
  have hy_pow : y ^ p = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hAb.2 (y : G) (Subgroup.mem_subgroupOf.mp hy))
  have hcomm : Commute y z := Subgroup.mem_center_iff.mp hzcenter y
  have hzpow : z ^ p = 1 := by
    have h := hcomm.mul_pow p
    rw [show y * z = w from by dsimp only [z]; group] at h
    rw [hwp, hy_pow] at h
    simpa using h.symm
  have hz1 : z = 1 := r4h_eq_one_of_mem_center_pow_eq_one hZ hzcenter hzpow
  have hwy : w = y := by
    rw [show w = y * z from by dsimp only [z]; group, hz1, mul_one]
  have hwBX : w ∈ BX.subgroupOf X := hwy ▸ hy
  simpa [w] using Subgroup.mem_subgroupOf.mp hwBX

private theorem r4h_mem_normalizer_of_conj_mem_normalizer {G : Type} [Group G] {p : ℕ}
    {X BX : Subgroup G} (hBX : BX ≤ X) (hAb : IsElemAbelian p BX)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g))
    {m : ↥X}
    (hm : (MulAut.conj : ↥X →* MulAut ↥X) m ∈
      Subgroup.normalizer
        (((BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X)) : Set (MulAut ↥X))) :
    (m : G) ∈ Subgroup.normalizer (BX : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    exact r4h_conj_mem_BX hBX hAb hZ hm hb
  · intro hb
    have hm' : (MulAut.conj : ↥X →* MulAut ↥X) m⁻¹ ∈
        Subgroup.normalizer
          (((BX.subgroupOf X).map (MulAut.conj : ↥X →* MulAut ↥X)) : Set (MulAut ↥X)) := by
      have h2 : (MulAut.conj : ↥X →* MulAut ↥X) m⁻¹ =
          ((MulAut.conj : ↥X →* MulAut ↥X) m)⁻¹ := by
        rw [← map_inv]
      rw [h2]
      exact Subgroup.inv_mem _ hm
    have hmem := r4h_conj_mem_BX hBX hAb hZ hm' hb
    have hmem' : (m : G)⁻¹ * ((m : G) * b * (m : G)⁻¹) * (m : G) ∈ BX := by
      simpa only [Subgroup.coe_inv, inv_inv] using hmem
    have hb_eq : b = (m : G)⁻¹ * ((m : G) * b * (m : G)⁻¹) * (m : G) := by group
    rwa [hb_eq]

theorem ggAutomizer_card_eq_inn {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {X BX : Subgroup G} (hBX : BX ≤ X) (hAb : IsElemAbelian p BX)
    (hZ : ∀ g ∈ Subgroup.center ↥X, Nat.Coprime p (orderOf g)) :
    Nat.card (ggAutomizer X BX) =
      Nat.card (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
        (Subgroup.map (MulAut.conj : ↥X →* MulAut ↥X) (BX.subgroupOf X))) := by
  let c : ↥X →* MulAut ↥X := MulAut.conj
  let A : Subgroup (MulAut ↥X) := Subgroup.map c (BX.subgroupOf X)
  let Inn : Subgroup (MulAut ↥X) := c.range
  change Nat.card (ggAutomizer X BX) = Nat.card (ggAutomizer Inn A)
  let inc : ↥BX →* ↥X := Subgroup.inclusion hBX
  let g : ↥BX →* MulAut ↥X := c.comp inc
  have hinc : inc.range = BX.subgroupOf X := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.2
    · intro hy
      exact ⟨⟨(y : G), hy⟩, Subtype.ext rfl⟩
  have hgrange : g.range = A := by
    rw [show g = c.comp inc from rfl, MonoidHom.range_comp, hinc]
  let gA : ↥BX →* ↥A := g.codRestrict A (fun b => hgrange ▸ ⟨b, rfl⟩)
  have hgA : ∀ b : ↥BX, ((gA b : ↥A) : MulAut ↥X) = c (inc b) := fun b => rfl
  have hinj : Function.Injective gA := by
    intro b1 b2 hb
    apply Subgroup.inclusion_injective hBX
    apply r4h_conj_injective_on hAb hZ
    · exact Subgroup.mem_subgroupOf.mpr b1.2
    · exact Subgroup.mem_subgroupOf.mpr b2.2
    · have h := congrArg (fun x : ↥A => (x : MulAut ↥X)) hb
      rwa [hgA b1, hgA b2] at h
  have hsurj : Function.Surjective gA := by
    intro a
    have ha : (a : MulAut ↥X) ∈ g.range := by
      rw [hgrange]
      exact a.2
    rw [MonoidHom.mem_range] at ha
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext (by rw [hgA b]; exact hb)⟩
  let ε : ↥BX ≃* ↥A := MulEquiv.ofBijective gA ⟨hinj, hsurj⟩
  have hε : ∀ b : ↥BX, (ε b : MulAut ↥X) = MulAut.conj (inc b) := by
    intro b
    rw [show ε b = gA b from MulEquiv.ofBijective_apply gA ⟨hinj, hsurj⟩ b]
    exact hgA b
  let e : MulAut ↥BX ≃* MulAut ↥A := MulAut.congr ε
  have he : ∀ (φ : MulAut ↥BX) (a : ↥A), (e φ) a = ε (φ (ε.symm a)) := by
    intro φ a
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hmap : Subgroup.map e.toMonoidHom (ggAutomizer X BX) = ggAutomizer Inn A := by
    ext ψ
    constructor
    · intro hψ
      rw [Subgroup.mem_map] at hψ
      obtain ⟨φ, hφ, rfl⟩ := hψ
      obtain ⟨n, hnX, hnN, hφn⟩ := mem_ggAutomizer_iff.mp hφ
      refine mem_ggAutomizer_iff.mpr ⟨c ⟨n, hnX⟩, ⟨⟨n, hnX⟩, rfl⟩, ?_, ?_⟩
      · exact r4h_conj_mem_normalizer_A hnX hnN
      · intro a
        have hcoe : ((e.toMonoidHom φ : MulAut ↥A) a : MulAut ↥X) =
            MulAut.conj (inc (φ (ε.symm a))) := by
          change (((e φ : MulAut ↥A)) a : MulAut ↥X) =
            MulAut.conj (inc (φ (ε.symm a)))
          rw [he φ a, hε (φ (ε.symm a))]
        have ha : (a : MulAut ↥X) = MulAut.conj (inc (ε.symm a)) := by
          calc (a : MulAut ↥X) = ((ε (ε.symm a) : ↥A) : MulAut ↥X) := by
                rw [MulEquiv.apply_symm_apply]
            _ = MulAut.conj (inc (ε.symm a)) := hε (ε.symm a)
        rw [hcoe, ha]
        have hinc' : inc (φ (ε.symm a)) = ⟨n, hnX⟩ * inc (ε.symm a) * ⟨n, hnX⟩⁻¹ := by
          apply Subtype.ext
          simpa [inc, Subgroup.inclusion] using hφn (ε.symm a)
        rw [hinc', map_mul, map_mul, map_inv]
    · intro hψ
      rw [Subgroup.mem_map]
      obtain ⟨h, hhInn, hhN, hψa⟩ := mem_ggAutomizer_iff.mp hψ
      obtain ⟨m, hm_eq⟩ := MonoidHom.mem_range.mp hhInn
      have hmN : (m : G) ∈ Subgroup.normalizer (BX : Set G) :=
        r4h_mem_normalizer_of_conj_mem_normalizer hBX hAb hZ (hm_eq ▸ hhN)
      let φ : MulAut ↥BX := e.symm ψ
      have hφ : φ ∈ ggAutomizer X BX := by
        refine mem_ggAutomizer_iff.mpr ⟨(m : G), m.2, hmN, ?_⟩
        intro b
        let w : ↥X := ⟨(m : G) * (b : G) * (m : G)⁻¹,
          X.mul_mem (X.mul_mem m.2 (hBX b.2)) (X.inv_mem m.2)⟩
        have hwBX : w ∈ BX.subgroupOf X :=
          Subgroup.mem_subgroupOf.mpr (r4h_conj_mem_BX hBX hAb hZ (hm_eq ▸ hhN) b.2)
        have hmain : (MulAut.conj : ↥X →* MulAut ↥X) (inc (φ b)) =
            (MulAut.conj : ↥X →* MulAut ↥X) w := by
          have h1 : ((ψ (ε b) : ↥A) : MulAut ↥X) =
              h * (ε b : MulAut ↥X) * h⁻¹ := hψa (ε b)
          have h2 : ψ (ε b) = ε (φ b) := by
            have h3 : ψ = e φ := (MulEquiv.apply_symm_apply e ψ).symm
            rw [h3, he φ (ε b), MulEquiv.symm_apply_apply]
          rw [h2, hε (φ b), hε b, ← hm_eq] at h1
          rw [h1]
          rw [show w = m * inc b * m⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
        have hincφ : inc (φ b) = w :=
          r4h_conj_injective_on hAb hZ (inc (φ b))
            (Subgroup.mem_subgroupOf.mpr (φ b).2) w hwBX hmain
        have := congrArg (fun x : ↥X => (x : G)) hincφ
        simpa [w, inc] using this
      exact ⟨φ, hφ, by
        change e φ = ψ
        exact MulEquiv.apply_symm_apply e ψ⟩
  have hcard := Subgroup.card_map_of_injective (K := ggAutomizer X BX)
    (f := e.toMonoidHom) (EquivLike.injective e)
  rw [hmap] at hcard
  exact hcard.symm

end CFSG.StandardType
