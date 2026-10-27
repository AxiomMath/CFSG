module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrXB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13OneBetaCA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

@[expose] def IsCoord (X : Subgroup (MulAut W)) (p : ℕ)
    (lam : s13IsoComps X → Additive ↥X →+ ZMod p) : Prop :=
  ∀ U : s13IsoComps X, Function.Surjective (lam U) ∧
    ∀ x : ↥X, lam U (Additive.ofMul x) = 0 ↔ (x : MulAut W) ∈ s13KerOn X (U : Subgroup W)

private theorem w16g_odd_card_of_isElemAbelian {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : Odd (Nat.card X) := by
  haveI : Finite X := inferInstance
  haveI : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p X := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hX.2 (x : MulAut W) x.2)⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  rw [hn]
  exact Odd.pow (hp.odd_of_ne_two hp2)

private theorem w16g_exists_coord_one (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) (U : s13IsoComps X) :
    ∃ lam : Additive ↥X →+ ZMod p, Function.Surjective lam ∧
      ∀ x : ↥X, lam (Additive.ofMul x) = 0 ↔
        (x : MulAut W) ∈ s13KerOn X (U : Subgroup W) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative ↥X := hX.1
  obtain ⟨-, hHidx⟩ := s13KerOn_mem_hyperplanes hW hp hp2 hX U.2
  let K : Subgroup ↥X := (s13KerOn X (U : Subgroup W)).subgroupOf X
  have hcardK : Nat.card (↥X ⧸ K) = p := hHidx
  haveI : IsCyclic (↥X ⧸ K) := isCyclic_of_prime_card hcardK
  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  let e : (↥X ⧸ K) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardK hcardZ
  let f : ↥X →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' K)
  refine ⟨MonoidHom.toAdditiveLeft f, ?_, ?_⟩
  · intro y
    obtain ⟨q, hq⟩ := e.surjective (Multiplicative.ofAdd y)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    refine ⟨Additive.ofMul x, ?_⟩
    simp only [MonoidHom.coe_toAdditiveLeft, Function.comp_apply, toMul_ofMul]
    rw [show f x = Multiplicative.ofAdd y from hq]
    rfl
  · intro x
    simp only [MonoidHom.coe_toAdditiveLeft, Function.comp_apply, toMul_ofMul, toAdd_eq_zero]
    have h1 : f x = 1 ↔ QuotientGroup.mk' K x = 1 := by
      rw [show f x = e (QuotientGroup.mk' K x) from rfl, ← map_one e]
      exact e.injective.eq_iff
    rw [h1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change x ∈ (s13KerOn X (U : Subgroup W)).subgroupOf X ↔
      (x : MulAut W) ∈ s13KerOn X (U : Subgroup W)
    simp only [Subgroup.mem_subgroupOf]

theorem exists_coord (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) : ∃ lam, IsCoord X p lam := by
  classical
  refine ⟨fun U => Classical.choose (w16g_exists_coord_one hW hp hp2 hX U), ?_⟩
  intro U
  exact Classical.choose_spec (w16g_exists_coord_one hW hp hp2 hX U)

theorem coord_injective (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {lam : s13IsoComps X → Additive ↥X →+ ZMod p}
    (hl : IsCoord X p lam) {x y : ↥X}
    (h : ∀ U, lam U (Additive.ofMul x) = lam U (Additive.ofMul y)) : x = y := by
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 hX
  have hzmem : ∀ U : s13IsoComps X,
      ((x * y⁻¹ : ↥X) : MulAut W) ∈ s13KerOn X (U : Subgroup W) := by
    intro U
    refine ((hl U).2 (x * y⁻¹)).mp ?_
    have hz : Additive.ofMul (x * y⁻¹) = Additive.ofMul x - Additive.ofMul y := by
      calc Additive.ofMul (x * y⁻¹)
          = Additive.ofMul x + Additive.ofMul y⁻¹ := ofMul_mul x y⁻¹
        _ = Additive.ofMul x + -Additive.ofMul y := by rw [ofMul_inv]
        _ = Additive.ofMul x - Additive.ofMul y := (sub_eq_add_neg _ _).symm
    rw [hz, map_sub, h U, sub_self]
  have hcent : ∀ U : s13IsoComps X,
      ((x * y⁻¹ : ↥X) : MulAut W) ∈ centSub (U : Subgroup W) := fun U => (hzmem U).2
  have hfixcomm : commSub ⊤ X ≤ fixV (Subgroup.zpowers ((x * y⁻¹ : ↥X) : MulAut W)) := by
    rw [← iSup_s13IsoComps hW hodd]
    refine iSup_le fun U => iSup_le fun hU => ?_
    intro u hu
    rw [mem_fixV]
    intro z hz
    exact mem_centSub.mp (Subgroup.zpowers_le.mpr (hcent ⟨U, hU⟩) hz) u hu
  have hfixV : fixV X ≤ fixV (Subgroup.zpowers ((x * y⁻¹ : ↥X) : MulAut W)) := by
    intro w hw
    rw [mem_fixV]
    intro z hz
    exact (mem_fixV.mp hw) z (Subgroup.zpowers_le.mpr (x * y⁻¹).2 hz)
  have htop : fixV X ⊔ commSub ⊤ X = ⊤ := by
    have hd := (B1.coprime_decomp (V := W) (fun v => by rw [pow_two]; exact hW v) hodd
      (M := ⊤) (fun _ _ _ _ => trivial)).1
    simpa using hd
  have hfixall : ∀ w : W, ((x * y⁻¹ : ↥X) : MulAut W) w = w := by
    intro w
    have hw : w ∈ fixV X ⊔ commSub ⊤ X := by rw [htop]; trivial
    rcases Subgroup.mem_sup.mp hw with ⟨a, ha, b, hb, rfl⟩
    have h1 : ((x * y⁻¹ : ↥X) : MulAut W) a = a :=
      (mem_fixV.mp (hfixV ha)) _ (Subgroup.mem_zpowers _)
    have h2 : ((x * y⁻¹ : ↥X) : MulAut W) b = b :=
      (mem_fixV.mp (hfixcomm hb)) _ (Subgroup.mem_zpowers _)
    simp only [map_mul, h1, h2]
  have hzg : ((x * y⁻¹ : ↥X) : MulAut W) = 1 := MulEquiv.ext hfixall
  have hz1 : x * y⁻¹ = 1 := Subtype.ext hzg
  exact mul_inv_eq_one.mp hz1

theorem coord_ne_zero_iff {p : ℕ} {X : Subgroup (MulAut W)}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam) (x : ↥X)
    (U : s13IsoComps X) :
    lam U (Additive.ofMul x) ≠ 0 ↔
      commSub (U : Subgroup W) (Subgroup.zpowers (x : MulAut W)) ≠ ⊥ := by
  rw [ne_eq, (hl U).2 x, ne_eq, not_iff_not]
  simp only [s13KerOn, Subgroup.mem_inf, mem_centSub]
  constructor
  · rintro ⟨-, hcent⟩
    rw [commSub_eq_bot_iff]
    intro u hu
    rw [mem_fixV]
    intro z hz
    exact mem_centSub.mp (Subgroup.zpowers_le.mpr (mem_centSub.mpr hcent) hz) u hu
  · intro hbot
    refine ⟨x.2, ?_⟩
    intro u hu
    exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hbot) hu)) (x : MulAut W) (Subgroup.mem_zpowers _)

theorem mem_s13Supp_iff_coord {p : ℕ} {X : Subgroup (MulAut W)}
    {lam : s13IsoComps X → Additive ↥X →+ ZMod p} (hl : IsCoord X p lam)
    {L : Subgroup (MulAut W)} (hLX : L ≤ X) (U : s13IsoComps X) :
    (U : Subgroup W) ∈ s13Supp X L ↔
      ∃ x : ↥X, (x : MulAut W) ∈ L ∧ lam U (Additive.ofMul x) ≠ 0 := by
  have hUmem : (U : Subgroup W) ∈ s13IsoComps X := U.2
  simp only [s13Supp, Set.mem_setOf_eq, hUmem, true_and]
  constructor
  · intro hne
    by_contra h
    push Not at h
    apply hne
    rw [commSub, Subgroup.closure_eq_bot_iff]
    rintro c ⟨x, hxL, u, hu, rfl⟩
    have hxX : x ∈ X := hLX hxL
    have hx0 : lam U (Additive.ofMul ⟨x, hxX⟩) = 0 := h ⟨x, hxX⟩ hxL
    have hbot : commSub (U : Subgroup W) (Subgroup.zpowers x) = ⊥ := by
      by_contra hc
      exact (coord_ne_zero_iff hl ⟨x, hxX⟩ U).mpr hc hx0
    rw [Set.mem_singleton_iff, mul_inv_eq_one]
    exact (mem_fixV.mp ((commSub_eq_bot_iff.mp hbot) hu)) x (Subgroup.mem_zpowers x)
  · rintro ⟨x, hxL, hne⟩
    have hcomm : commSub (U : Subgroup W) (Subgroup.zpowers (x : MulAut W)) ≠ ⊥ :=
      (coord_ne_zero_iff hl x U).mp hne
    intro hbot
    have hle : Subgroup.zpowers (x : MulAut W) ≤ L := Subgroup.zpowers_le.mpr hxL
    exact hcomm (le_bot_iff.mp (hbot ▸ commSub_mono le_rfl hle))

theorem rk_commSub_top_eq_sum (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {L : Subgroup (MulAut W)} (hLX : L ≤ X) :
    rk ↥(commSub ⊤ L) = ∑ᶠ (U : Subgroup W) (_ : U ∈ s13Supp X L), rk ↥U := by
  classical
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 hX
  haveI : Finite (Subgroup W) :=
    Finite.of_injective (fun S : Subgroup W => (S : Set W)) SetLike.coe_injective
  haveI : Fintype {U : Subgroup W // U ∈ s13Supp X L} := Fintype.ofFinite _
  have hind : sSupIndep (s13Supp X L) :=
    (s13IsoComps_sSupIndep hW hodd).mono (fun U hU => hU.1)
  rw [commSub_top_eq_iSup_s13Supp hW hp hp2 hX hLX, iSup_subtype']
  rw [w16g_rk_iSup_eq_sum (fun w => by rw [pow_two]; exact hW w)
    (fun U : {U : Subgroup W // U ∈ s13Supp X L} => (U : Subgroup W))
    ((sSupIndep_iff _).mp hind)]
  rw [← finsum_subtype_eq_finsum_cond, finsum_eq_sum_of_fintype]

theorem rk_s13IsoComps_eq (hW : ∀ w : W, w * w = 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelian p X) {U : Subgroup W} (hU : U ∈ s13IsoComps X) :
    ∃ s : ℕ, 0 < s ∧ rk ↥U = dParam p * s := by
  have hodd : Odd (Nat.card X) := w16g_odd_card_of_isElemAbelian hp hp2 hX
  obtain ⟨hne, -⟩ := s13IsoComps_le_commSub hW hodd hU
  obtain ⟨s, hs⟩ := dParam_dvd_rk_s13IsoComps hW hp hp2 hX hU
  refine ⟨s, ?_, hs⟩
  by_contra h0
  have hs0 : s = 0 := Nat.eq_zero_of_not_pos h0
  rw [hs0, mul_zero] at hs
  exact hne ((rk_eq_zero_iff (fun v => by rw [pow_two]; exact hW v)).mp hs)

end CFSG.LocalAnalysis.WeakClosure81
