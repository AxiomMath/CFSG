module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJCoord
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly
open Multiplicative

namespace CommonJ

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {R : Type} [Group R] {θ : ↥L ⧸ Subgroup.center ↥L ≃* R} {γ : ↥Bs →* R}

theorem eta_x_eq_one (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs) {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (i0 : Fin n)
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (xb : ↥Bs) (hxb : (xb : G) = x) {j : Fin n} (hj : j ≠ i0) : eta xb j = 1 := by
  obtain ⟨hp, -, -, hLx, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  refine eq_one_of_bCoordinateBlock_fix hp hp2 (F := eta xb) ?_ hj
  intro u hu
  have hu' : u ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
    rw [hA]
    exact hu
  obtain ⟨α, hα, hαu⟩ := Subgroup.mem_map.mp hu'
  have hαfix : α xb = xb := by
    refine Subgroup.closure_induction (p := fun x _ => x xb = xb) ?_ rfl ?_ ?_ hα
    · rintro φ ⟨g, hgL, -, hφ⟩
      have hcomm : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
      refine Subtype.ext ?_
      rw [hφ xb, hxb, hcomm]
      group
    · intro a b _ _ ha hb
      simp only [MulAut.mul_apply, ha, hb]
    · intro a _ ha
      calc a⁻¹ xb = a⁻¹ (a xb) := by rw [ha]
        _ = xb := MulAut.inv_apply_self _ a xb
  have hfix : u (eta xb) = eta xb := by
    rw [← hαu]
    simp [MulAut.congr_apply, hαfix]
  exact hfix

theorem ggCoord_iff_of_signedCoords (hcfg : GGConfig p B Bs x L D J) (hB : B = Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hR : Subgroup.center R = ⊥)
    (hγ : GGGammaHatSpec θ γ) {m : ℕ} (hm : 3 ≤ m)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))) (i0 : Fin (m + 1))
    (hA : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) p i0)
    {H : Type} [Group H] (e : R ≃* H)
    {Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥(γ.range.map e.toMonoidHom)}
    (hΘ : GGSignedCoords (γ.range.map e.toMonoidHom) Θ)
    (b : ↥Bs) (t : ↥(γ.range.map e.toMonoidHom)) (ht : (t : H) = e (γ b)) :
    (GGCoordDense (Θ.symm t) ↔ GGCoordDense fun j => eta b (i0.succAbove j)) ∧
      (GGCoordSparse (Θ.symm t) ↔ GGCoordSparse fun j => eta b (i0.succAbove j)) := by
  obtain ⟨hp, -, hxBs, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hx1 : x ≠ 1 := by
    have hS := hcfg.1.2.2.2.2.2.2.1
    unfold LargeEvenSStar at hS
    exact hS.2.2.1
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let T := γ.range.map e.toMonoidHom
  haveI : Finite R := Finite.of_surjective θ θ.surjective
  haveI : Finite ↥γ.range := Subtype.finite
  haveI : Finite ↥T :=
    Finite.of_surjective
      (fun x : ↥γ.range =>
        (Subgroup.equivMapOfInjective γ.range e.toMonoidHom e.injective x : ↥T))
      (Subgroup.equivMapOfInjective γ.range e.toMonoidHom e.injective).surjective
  let ins : (Fin m → Multiplicative (ZMod p)) →*
      (Fin (m + 1) → Multiplicative (ZMod p)) :=
    { toFun := fun w => Fin.insertNth i0 1 w
      map_one' := by rw [Fin.insertNth_one_right, Pi.mulSingle_one]
      map_mul' := fun w₁ w₂ => by
        simpa using Fin.insertNth_mul (α := fun _ => Multiplicative (ZMod p))
          i0 1 1 w₁ w₂ }
  let base : (Fin m → Multiplicative (ZMod p)) →* ↥Bs := eta.symm.toMonoidHom.comp ins
  let ψ₀ : (Fin m → Multiplicative (ZMod p)) →* ↥T :=
    (e.toMonoidHom.comp (γ.comp base)).codRestrict T
      (fun w => ⟨γ (base w), ⟨base w, rfl⟩, rfl⟩)
  have hψ₀_apply (w : Fin m → Multiplicative (ZMod p)) :
      (ψ₀ w : H) = e (γ (base w)) := rfl
  have hbase_apply (w : Fin m → Multiplicative (ZMod p)) :
      eta (base w) = Fin.insertNth i0 1 w := by
    simp [base, ins]
  have hvec_supp {f : Fin (m + 1) → Multiplicative (ZMod p)}
      (hf : ∀ j, j ≠ i0 → f j = 1) :
      f = Pi.mulSingle i0 (ofAdd (toAdd (f i0))) := by
    have h : f = Fin.insertNth i0 (f i0) 1 := by
      funext j
      rcases Fin.eq_self_or_eq_succAbove i0 j with rfl | ⟨j', rfl⟩
      · rw [Fin.insertNth_apply_same]
      · rw [Fin.insertNth_apply_succAbove, hf _ (Fin.succAbove_ne i0 j')]
        rfl
    rw [h, Fin.insertNth_one_right]
    simp
  have hxvec' (xb' : ↥Bs) (hxb' : (xb' : G) = x) :
      eta xb' = Pi.mulSingle i0 (ofAdd (toAdd (eta xb' i0))) :=
    hvec_supp fun j hj => eta_x_eq_one hcfg hB eta i0 hA xb' hxb' hj
  let xb : ↥Bs := ⟨x, hxBs⟩
  have hxbeq : (xb : G) = x := rfl
  have hxvec : eta xb = Pi.mulSingle i0 (ofAdd (toAdd (eta xb i0))) := hxvec' xb hxbeq
  have hinj : Function.Injective ψ₀ := by
    intro w₁ w₂ hw
    have hγeq : γ (base w₁) = γ (base w₂) := by
      have h := congrArg Subtype.val hw
      rw [hψ₀_apply, hψ₀_apply] at h
      exact e.injective h
    set q : ↥Bs := base w₁ * (base w₂)⁻¹ with hq
    have hγq : γ q = 1 := by
      rw [hq, map_mul, map_inv, hγeq, mul_inv_cancel]
    have hqmem : ((q : ↥Bs) : G) ∈ Subgroup.zpowers x :=
      (gammaHat_eq_one_iff hcfg hB hBsN hR hγ q).mp hγq
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hqmem
    have hqeq : q = xb ^ k := by
      apply Subtype.ext
      rw [show (q : G) = x ^ k from hk.symm, ← hxbeq]
      rfl
    have hqvec : eta q = Fin.insertNth i0 1 w₁ * (Fin.insertNth i0 1 w₂)⁻¹ := by
      rw [hq, map_mul, map_inv, hbase_apply, hbase_apply]
    funext j
    have hcoord : eta q (i0.succAbove j) = 1 := by
      rw [hqeq, map_zpow]
      change (eta xb (i0.succAbove j)) ^ k = 1
      rw [eta_x_eq_one hcfg hB eta i0 hA xb hxbeq (Fin.succAbove_ne i0 j)]
      exact one_zpow k
    have hqcoord : w₁ j * (w₂ j)⁻¹ = 1 := by
      rw [hqvec, Pi.mul_apply, Pi.inv_apply, Fin.insertNth_apply_succAbove,
        Fin.insertNth_apply_succAbove] at hcoord
      exact hcoord
    exact mul_inv_eq_one.mp hqcoord
  have hcardC : Nat.card (Fin m → Multiplicative (ZMod p)) = p ^ m := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardT : Nat.card ↥T = p ^ m := by
    rw [Subgroup.card_map_of_injective e.injective,
      card_range_gammaHat hcfg hB hBsN hR hγ eta,
      show m + 1 - 1 = m by omega]
  have hbij : Function.Bijective ψ₀ :=
    hinj.bijective_of_nat_card_le (le_of_eq (hcardT.trans hcardC.symm))
  let φ : MulAut (Fin m → Multiplicative (ZMod p)) :=
    (MulEquiv.ofBijective ψ₀ hbij).trans Θ.symm
  have hφ_apply (w : Fin m → Multiplicative (ZMod p)) : φ w = Θ.symm (ψ₀ w) := rfl
  have hwvec : eta b = Fin.insertNth i0 (eta b i0)
      (fun j => eta b (i0.succAbove j)) := by
    rw [Fin.eq_insertNth_iff]
    exact ⟨rfl, rfl⟩
  have hb_link : Θ.symm t = φ (fun j => eta b (i0.succAbove j)) := by
    set w : Fin m → Multiplicative (ZMod p) := fun j => eta b (i0.succAbove j) with hwdef
    have hbvec : eta b = Fin.insertNth i0 (eta b i0) w := hwvec
    set c0 : ZMod p := toAdd (eta xb i0) with hc0def
    have hc0' : c0 ≠ 0 := by
      intro h0
      have h1 : eta xb = 1 := by
        rw [hxvec, h0, ofAdd_zero, Pi.mulSingle_one]
      have h2 : xb = 1 := eta.injective (by simpa using h1)
      exact hx1 (by rw [← hxbeq, h2]; rfl)
    let q : ↥Bs := b / base w
    have hqsupp : ∀ j, j ≠ i0 → eta q j = 1 := by
      intro j hj
      rcases Fin.eq_self_or_eq_succAbove i0 j with h | ⟨j', rfl⟩
      · exact absurd h hj
      · have hqdef : q = b * (base w)⁻¹ := by
          change b / base w = b * (base w)⁻¹
          rw [div_eq_mul_inv]
        rw [hqdef, map_mul, map_inv, Pi.mul_apply, Pi.inv_apply, hbvec, hbase_apply,
          Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
        exact mul_inv_cancel (w j')
    have hqvec : eta q = Pi.mulSingle i0 (ofAdd (toAdd (eta q i0))) := hvec_supp hqsupp
    set d : ℕ := (toAdd (eta q i0) * c0⁻¹).val with hddef
    have hpow : eta q = (eta xb) ^ d := by
      have hc0inv : c0⁻¹ * c0 = 1 := inv_mul_cancel₀ (a := c0) hc0'
      rw [hqvec, hxvec, SpCoord.mulSingle_ofAdd_pow, hddef, ZMod.natCast_zmod_val,
        mul_assoc, hc0inv, mul_one]
    have hqeq : q = xb ^ d := by
      apply eta.injective
      rw [map_pow, hpow]
    have hqmem : (q : G) ∈ Subgroup.zpowers x := by
      rw [hqeq]
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨(d : ℤ), ?_⟩
      rw [← hxbeq, zpow_natCast]
      rfl
    have hγb : γ b = γ (base w) := by
      have h1 : γ q = 1 := (gammaHat_eq_one_iff hcfg hB hBsN hR hγ q).mpr hqmem
      have h2 : γ b / γ (base w) = 1 := by
        simpa [q, map_div] using h1
      exact div_eq_one.mp h2
    have ht_eq : t = ⟨e (γ b), ⟨γ b, ⟨b, rfl⟩, rfl⟩⟩ := Subtype.ext ht
    rw [ht_eq, hφ_apply]
    refine congrArg Θ.symm (Subtype.ext ?_)
    show e (γ b) = e (γ (base w))
    rw [hγb]
  have hnorm : ∀ u : MulAut (Fin m → Multiplicative (ZMod p)),
      SpCoord.IsSignedPerm ⇑u → SpCoord.IsSignedPerm ⇑(φ * u * φ⁻¹) := by
    intro u hu
    obtain ⟨U, hUm, hUrestrict⟩ := exists_bCoordinateBlock_restrict (m := m) i0 hu
    have hU' : U ∈ (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom := by
      rw [hA]
      exact hUm
    obtain ⟨α, hα, hαU⟩ := Subgroup.mem_map.mp hU'
    obtain ⟨g, hgL, -, hgα⟩ := mem_ggAutomizer_iff.mp hα
    let gL : ↥L := ⟨g, hgL⟩
    have hγconj : ∀ c : ↥Bs,
        γ (α c) = ggQuotHom θ gL * γ c * (ggQuotHom θ gL)⁻¹ := by
      intro c
      exact gammaHat_conj hR hBsN hγ gL c (α c) (by simpa using hgα c)
    let h : H := e (ggQuotHom θ gL)
    have hN : ∀ s ∈ T, h * s * h⁻¹ ∈ T := by
      intro s hs
      obtain ⟨r, hr, rfl⟩ := hs
      obtain ⟨c, rfl⟩ := hr
      refine ⟨γ (α c), ⟨α c, rfl⟩, ?_⟩
      rw [hγconj c]
      simp [h, map_mul, map_inv]
    have hpoint : ∀ f,
        φ (u f) = Θ.symm ⟨h * (Θ (φ f) : H) * h⁻¹, hN _ (Θ (φ f)).2⟩ := by
      intro f
      have hUF : U (Fin.insertNth i0 1 f) = Fin.insertNth i0 1 (u f) := by
        rw [Fin.eq_insertNth_iff]
        refine ⟨?_, ?_⟩
        · rw [bCoordinateBlock_apply_self hUm, Fin.insertNth_apply_same]
        · funext j
          simpa [Fin.removeNth_apply] using
            congrFun (hUrestrict (Fin.insertNth i0 1 f)) j
      have hαbase : α (base f) = base (u f) := by
        apply eta.injective
        have h1 : eta (α (base f)) = U (eta (base f)) := by
          rw [← hαU]
          simp [MulAut.congr_apply]
        rw [h1, hbase_apply, hUF, hbase_apply]
      have hγrel : γ (base (u f)) = ggQuotHom θ gL * γ (base f) *
          (ggQuotHom θ gL)⁻¹ := by
        rw [← hαbase, hγconj]
      have hThetaφ : (Θ (φ f) : H) = e (γ (base f)) := by
        rw [hφ_apply, MulEquiv.apply_symm_apply]
        rfl
      rw [hφ_apply]
      refine congrArg Θ.symm (Subtype.ext ?_)
      show e (γ (base (u f))) = h * (Θ (φ f) : H) * h⁻¹
      rw [hγrel, hThetaφ]
      simp [h, map_mul, map_inv]
    have hfun : ⇑(φ * u * φ⁻¹) =
        fun f => Θ.symm ⟨h * (Θ f : H) * h⁻¹, hN _ (Θ f).2⟩ := by
      funext f
      have h := hpoint (φ⁻¹ f)
      simpa using h
    rw [hfun]
    exact hΘ h hN
  have hmain := ggCoord_iff_of_normalizes hp hp2 hm hnorm
    (fun j => eta b (i0.succAbove j))
  constructor
  · rw [hb_link]
    exact hmain.1
  · rw [hb_link]
    exact hmain.2

end CommonJ

end CFSG.StandardType

end
