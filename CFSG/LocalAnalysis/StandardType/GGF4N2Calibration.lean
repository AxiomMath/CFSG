module

public import CFSG.LocalAnalysis.StandardType.GGF4OvergroupFixLine

public section

namespace CFSG.StandardType.F4Over

open Multiplicative SpCoord CFSG.Open

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coord

variable {G : Type} [Group G]

@[expose] def powHom (z : G) (hz : z ^ 5 = 1) : Multiplicative (ZMod 5) →* G where
  toFun a := z ^ (toAdd a).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hz, pow_add]

theorem powHom_ofAdd_one (z : G) (hz : z ^ 5 = 1) : powHom z hz (ofAdd 1) = z := by
  change z ^ (toAdd (ofAdd (1 : ZMod 5))).val = z
  rw [show (toAdd (ofAdd (1 : ZMod 5))).val = 1 from rfl, pow_one]

theorem exists_coord [Finite G] {Bs : Subgroup G} (hEl : IsElemAbelian 5 Bs) (n : Fin 4 → G)
    (hnB : ∀ k, n k ∈ Bs) (hgen : Bs ≤ ⨆ k, Subgroup.zpowers (n k))
    (hcard : Nat.card Bs = 5 ^ 4) :
    ∃ κ : V5 ≃* ↥Bs, ∀ k, ((κ (e5 k) : ↥Bs) : G) = n k := by
  classical
  have hn5 : ∀ k, n k ^ 5 = 1 := fun k => hEl.2 _ (hnB k)
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEl.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  let φ : Fin 4 → (Multiplicative (ZMod 5) →* G) := fun k => powHom (n k) (hn5 k)
  have hφB : ∀ k a, φ k a ∈ Bs := fun k a => Bs.pow_mem (hnB k) _
  have hcomm' : Pairwise fun i j => ∀ (a : Multiplicative (ZMod 5)) (b : Multiplicative (ZMod 5)),
      Commute (φ i a) (φ j b) := fun i j _ a b => hcomm _ (hφB i a) _ (hφB j b)
  let κ₀ : V5 →* G := MonoidHom.noncommPiCoprod φ hcomm'
  have hrange : ∀ f, κ₀ f ∈ Bs := by
    intro f
    have h : κ₀.range ≤ Bs := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun k => by
        rintro _ ⟨a, rfl⟩
        exact hφB k a
    exact h ⟨f, rfl⟩
  let κ₁ : V5 →* ↥Bs := κ₀.codRestrict Bs hrange
  have hκ₁ : ∀ k, ((κ₁ (e5 k) : ↥Bs) : G) = n k := fun k => by
    change κ₀ (Pi.mulSingle k (ofAdd 1)) = n k
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    exact powHom_ofAdd_one (n k) (hn5 k)
  have hsurj : Function.Surjective κ₁ := by
    intro b
    have hle : (⨆ k, Subgroup.zpowers (n k)) ≤ κ₀.range :=
      iSup_le fun k => Subgroup.zpowers_le.2 ⟨e5 k, hκ₁ k⟩
    obtain ⟨f, hf⟩ := hle (hgen b.2)
    exact ⟨f, Subtype.ext hf⟩
  have hV : Nat.card V5 = 5 ^ 4 := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 5)),
      Fintype.card_multiplicative, ZMod.card, Nat.card_eq_fintype_card (α := Fin 4),
      Fintype.card_fin]
  have hbij : Function.Bijective κ₁ :=
    hsurj.bijective_of_nat_card_le (by rw [hV, hcard])
  exact ⟨MulEquiv.ofBijective κ₁ hbij, hκ₁⟩

theorem congr_sgnAut_apply {Bs : Subgroup G} (κ : V5 ≃* ↥Bs) (i k : Fin 4) :
    MulAut.congr κ (sgnAut i) (κ (e5 k)) = if k = i then (κ (e5 k))⁻¹ else κ (e5 k) := by
  change κ (sgnAut i (κ.symm (κ (e5 k)))) = _
  rw [MulEquiv.symm_apply_apply]
  by_cases hk : k = i
  · subst hk
    rw [if_pos rfl, e5, sgnAut_mulSingle_self, map_inv]
  · have h1 : (e5 k) i = 1 := by
      rw [e5]
      exact Pi.mulSingle_eq_of_ne (Ne.symm hk) _
    rw [if_neg hk, sgnAut_apply, Function.update_eq_self_iff.2 (by rw [h1, inv_one])]

theorem congr_permAut_apply {Bs : Subgroup G} (κ : V5 ≃* ↥Bs) (σ : Equiv.Perm (Fin 4))
    (k : Fin 4) : MulAut.congr κ (permAut σ) (κ (e5 k)) = κ (e5 (σ k)) := by
  change κ (permAut σ (κ.symm (κ (e5 k)))) = _
  rw [MulEquiv.symm_apply_apply, e5, permAut_mulSingle]
  rfl

end Coord

section Automizer

variable {G : Type} [Group G]

theorem conj_mem_ggAutomizer_map {H Bs : Subgroup G} {ν : G}
    (hν : ν ∈ Subgroup.normalizer (Bs : Set G)) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer H Bs) :
    ggConjAut Bs hν * φ * (ggConjAut Bs hν)⁻¹ ∈
      ggAutomizer (H.map (MulAut.conj ν).toMonoidHom) Bs := by
  obtain ⟨h, hhH, hhN, hφh⟩ := mem_ggAutomizer_iff.1 hφ
  refine mem_ggAutomizer_iff.2 ⟨ν * h * ν⁻¹, ⟨h, hhH, rfl⟩,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hν hhN) (Subgroup.inv_mem _ hν), fun b => ?_⟩
  change ν * ((φ ⟨ν⁻¹ * b * ν, _⟩ : ↥Bs) : G) * ν⁻¹ = _
  rw [hφh]
  group

theorem ggAutomizer_map_conj_le {K L Bs : Subgroup G} {g : G} (hgL : g ∈ L)
    (hgN : g ∈ Subgroup.normalizer (Bs : Set G)) :
    ggAutomizer (K.map (MulAut.conj g).toMonoidHom) Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  intro φ hφ
  obtain ⟨h, ⟨k, hk, rfl⟩, hhN, hφh⟩ := mem_ggAutomizer_iff.1 hφ
  have hkN : k ∈ Subgroup.normalizer (Bs : Set G) := by
    have h1 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hhN) hgN
    rwa [show g⁻¹ * (MulAut.conj g).toMonoidHom k * g = k by
      change g⁻¹ * (g * k * g⁻¹) * g = k
      group] at h1
  have hφ' : φ = ggConjAut Bs hgN * ggConjAut Bs hkN * (ggConjAut Bs hgN)⁻¹ := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [hφh]
    change g * k * g⁻¹ * b * (g * k * g⁻¹)⁻¹ = g * (k * (g⁻¹ * b * g) * k⁻¹) * g⁻¹
    group
  rw [hφ']
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (ggConjAut_mem_ggAutomizer hgL hgN))
    (Subgroup.mem_sup_right (ggConjAut_mem_ggAutomizer hk hkN)))
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left (ggConjAut_mem_ggAutomizer hgL hgN)))

end Automizer

theorem permAut_mul (σ τ : Equiv.Perm (Fin 4)) :
    (permAut (σ * τ) : MulAut V5) = permAut σ * permAut τ := by
  refine MulEquiv.ext fun f => ?_
  rw [MulAut.mul_apply, permAut_apply, permAut_apply, permAut_apply]
  rfl

theorem permAut_conj_sgnAut (σ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    (permAut σ : MulAut V5) * sgnAut i * (permAut σ)⁻¹ = sgnAut (σ i) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [MulAut.mul_apply, MulAut.mul_apply, permAut_apply, permAut_inv_apply, sgnAut_apply,
    sgnAut_apply, Function.comp_apply]
  by_cases hj : j = σ i
  · subst hj
    have h1 : σ⁻¹ (σ i) = i := by simp
    rw [h1, Function.update_self, Function.update_self, Function.comp_apply]
  · have h1 : σ⁻¹ j ≠ i := fun h => hj (by rw [← h]; simp)
    rw [Function.update_of_ne h1, Function.update_of_ne hj, Function.comp_apply]
    congr 1
    simp

theorem permAut_inv (σ : Equiv.Perm (Fin 4)) : (permAut σ⁻¹ : MulAut V5) = (permAut σ)⁻¹ := by
  refine MulEquiv.ext fun f => ?_
  rw [permAut_apply, permAut_inv_apply, inv_inv]

theorem permAut_conj_swap (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) :
    (permAut σ : MulAut V5) * permAut (Equiv.swap a b) * (permAut σ)⁻¹ =
      permAut (Equiv.swap (σ a) (σ b)) := by
  rw [Equiv.swap_apply_apply σ a b, permAut_mul, permAut_mul, permAut_inv]

section Calibration

variable {G : Type} [Group G] [Finite G] {Bs K L : Subgroup G}

theorem ggF4_calibration_signedB4_le (κ : V5 ≃* ↥Bs)
    (hC1s : ∀ i : Fin 4, i ≠ 3 → MulAut.congr κ (sgnAut i) ∈ ggAutomizer K Bs)
    (hC1t : ∀ a b : Fin 4, a ≠ 3 → b ≠ 3 →
      MulAut.congr κ (permAut (Equiv.swap a b)) ∈ ggAutomizer K Bs)
    {m : Fin 4} (hm : m ≠ 3) {ν : G} (hν : ν ∈ Subgroup.normalizer (Bs : Set G))
    (hνκ : ggConjAut Bs hν = MulAut.congr κ (permAut (Equiv.swap m 3)))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hC4 : K.map (MulAut.conj ν).toMonoidHom = K.map (MulAut.conj g).toMonoidHom) :
    signedB4.map (MulAut.congr κ).toMonoidHom ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
  classical
  have hAK : ∀ u, MulAut.congr κ u ∈ ggAutomizer K Bs →
      MulAut.congr κ u ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := fun u hu =>
    Subgroup.mem_sup_right hu
  have hAK₂ : ∀ u, MulAut.congr κ u ∈ ggAutomizer K Bs →
      MulAut.congr κ (permAut (Equiv.swap m 3) * u * (permAut (Equiv.swap m 3))⁻¹) ∈
        ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro u hu
    have h1 := conj_mem_ggAutomizer_map hν hu
    rw [hC4, hνκ] at h1
    have h2 := ggAutomizer_map_conj_le hgL hgN h1
    rwa [← map_inv, ← map_mul, ← map_mul] at h2
  have hs : ∀ i, MulAut.congr κ (sgnAut i) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro i
    by_cases hi : i = 3
    · subst hi
      have h := hAK₂ _ (hC1s m hm)
      rwa [permAut_conj_sgnAut, Equiv.swap_apply_left] at h
    · exact hAK _ (hC1s i hi)
  have ht3 : ∀ a, a ≠ 3 → a ≠ m →
      MulAut.congr κ (permAut (Equiv.swap a 3)) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro a ha3 ham
    have h := hAK₂ _ (hC1t a m ha3 hm)
    rwa [permAut_conj_swap, Equiv.swap_apply_of_ne_of_ne ham ha3, Equiv.swap_apply_left] at h
  have hm3 : MulAut.congr κ (permAut (Equiv.swap m 3)) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    obtain ⟨b, hbm, hb3⟩ : ∃ b : Fin 4, b ≠ m ∧ b ≠ 3 := by
      by_cases h0 : m = 0
      · exact ⟨1, by rw [h0]; decide, by decide⟩
      · exact ⟨0, Ne.symm h0, by decide⟩
    have hmb := hAK _ (hC1t m b hm hb3)
    have hb3' := ht3 b hb3 hbm
    have hprod : (permAut (Equiv.swap m 3) : MulAut V5) =
        permAut (Equiv.swap m b) * permAut (Equiv.swap b 3) * (permAut (Equiv.swap m b))⁻¹ := by
      rw [permAut_conj_swap, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hm) (Ne.symm hb3)]
    rw [hprod, map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmb hb3') (Subgroup.inv_mem _ hmb)
  have ht : ∀ a b : Fin 4, a ≠ b →
      MulAut.congr κ (permAut (Equiv.swap a b)) ∈ ggAutomizer L Bs ⊔ ggAutomizer K Bs := by
    intro a b hab
    by_cases ha : a = 3
    · subst ha
      rw [Equiv.swap_comm]
      by_cases hbm : b = m
      · subst hbm
        exact hm3
      · exact ht3 b (Ne.symm hab) hbm
    · by_cases hb : b = 3
      · subst hb
        by_cases ham : a = m
        · subst ham
          exact hm3
        · exact ht3 a ha ham
      · exact hAK _ (hC1t a b ha hb)
  rw [Subgroup.map_le_iff_le_comap]
  intro u hu
  exact mem_of_isSignedPerm
    (H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs).comap (MulAut.congr κ).toMonoidHom) hs
    (fun a b hab => ht a b hab) hu

theorem ggAutomizer_sup_le_ggInduced :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggInduced ⊤ Bs := by
  intro φ hφ
  have h1 : φ ∈ ggAutomizer ⊤ Bs :=
    sup_le (ggAutomizer_mono Bs le_top) (ggAutomizer_mono Bs le_top) hφ
  rw [ggAutomizer_eq] at h1
  exact h1

theorem ggF4_calibration_zpowers (hEl : IsElemAbelian 5 Bs) (hNT : GGNoTransvection 5 Bs)
    (hA : GGWeylOfType 5 CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs))
    (κ : V5 ≃* ↥Bs)
    (hC1s : ∀ i : Fin 4, i ≠ 3 → MulAut.congr κ (sgnAut i) ∈ ggAutomizer K Bs)
    (hC1t : ∀ a b : Fin 4, a ≠ 3 → b ≠ 3 →
      MulAut.congr κ (permAut (Equiv.swap a b)) ∈ ggAutomizer K Bs)
    {m : Fin 4} (hm : m ≠ 3) {ν : G} (hν : ν ∈ Subgroup.normalizer (Bs : Set G))
    (hνκ : ggConjAut Bs hν = MulAut.congr κ (permAut (Equiv.swap m 3)))
    {g : G} (hgL : g ∈ L) (hgN : g ∈ Subgroup.normalizer (Bs : Set G))
    (hC4 : K.map (MulAut.conj ν).toMonoidHom = K.map (MulAut.conj g).toMonoidHom)
    (hgm : g * ((κ (e5 m) : ↥Bs) : G) * g⁻¹ ∈ Subgroup.zpowers ((κ (e5 3) : ↥Bs) : G))
    (hg3 : g * ((κ (e5 3) : ↥Bs) : G) * g⁻¹ ∈ Subgroup.zpowers ((κ (e5 m) : ↥Bs) : G))
    {x : G} (hxB : x ∈ Bs)
    (hx : x ∈ Subgroup.zpowers ((κ (e5 m) : ↥Bs) : G) ⊔ Subgroup.zpowers ((κ (e5 3) : ↥Bs) : G))
    (hx1 : x ≠ 1) (hgx : g * x * g⁻¹ = x) :
    Subgroup.zpowers x = Subgroup.zpowers (((κ (e5 m) : ↥Bs) : G) * (κ (e5 3) : ↥Bs)) ∨
      Subgroup.zpowers x =
        Subgroup.zpowers (((κ (e5 m) : ↥Bs) : G) * ((κ (e5 3) : ↥Bs) : G)⁻¹) := by
  have hmem : ∀ a b : ↥Bs, g * (a : G) * g⁻¹ ∈ Subgroup.zpowers (b : G) →
      ggConjAut Bs hgN a ∈ Subgroup.zpowers b := by
    intro a b h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow, hn]; rfl)⟩
  exact ggF4_zpowers_eq_of_swap hEl hNT ggAutomizer_sup_le_ggInduced hA κ
    (ggF4_calibration_signedB4_le κ hC1s hC1t hm hν hνκ hgL hgN hC4)
    (Subgroup.mem_sup_left (ggConjAut_mem_ggAutomizer hgL hgN)) hm (hmem _ _ hgm)
    (hmem _ _ hg3) hxB hx hx1 hgx

end Calibration

end CFSG.StandardType.F4Over

end
