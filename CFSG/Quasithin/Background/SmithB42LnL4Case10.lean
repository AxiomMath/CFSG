module

public import CFSG.Quasithin.Background.SmithB42LnL4Ident

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B42Ln

open CFSG.Quasithin.JonesParshall Matrix CFSG.Assembly.LowTwoRank

local notation "𝕄₄" => Matrix (Fin 4) (Fin 4) (ZMod 2)

theorem w4_eq_wedgeMat4 (g : 𝕄₄) : w4 g = wedgeMat4 g := rfl

set_option maxRecDepth 100000 in
theorem fix_q4_le2 : (Finset.univ.filter fun x : Fin 6 → ZMod 2 =>
    ∀ c : Fin 64, InQ4 c → w4 (up4 c) *ᵥ x = x).card ≤ 2 := by
  decide +kernel

abbrev FixW4 (Y : Subgroup G4) : Type :=
  {x : Fin 6 → ZMod 2 // ∀ u ∈ Y, wedgeMat4 (u : 𝕄₄) *ᵥ x = x}

theorem wedgeMat4_mulVec_mul (g h : G4) (x : Fin 6 → ZMod 2) :
    wedgeMat4 ((g * h : G4) : 𝕄₄) *ᵥ x = wedgeMat4 (g : 𝕄₄) *ᵥ (wedgeMat4 (h : 𝕄₄) *ᵥ x) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, wedgeMat4_mul, mulVec_mulVec]

theorem wedgeMat4_mulVec_one (x : Fin 6 → ZMod 2) : wedgeMat4 ((1 : G4) : 𝕄₄) *ᵥ x = x := by
  rw [Matrix.SpecialLinearGroup.coe_one, wedgeMat4_one, one_mulVec]

theorem card_fixW4_conj (Y : Subgroup G4) (h : G4) :
    Nat.card (FixW4 (Y.map (MulAut.conj h).toMonoidHom)) = Nat.card (FixW4 Y) := by
  have hinv : ∀ x, wedgeMat4 ((h⁻¹ : G4) : 𝕄₄) *ᵥ (wedgeMat4 (h : 𝕄₄) *ᵥ x) = x := fun x => by
    rw [← wedgeMat4_mulVec_mul, inv_mul_cancel, wedgeMat4_mulVec_one]
  have hinv' : ∀ x, wedgeMat4 (h : 𝕄₄) *ᵥ (wedgeMat4 ((h⁻¹ : G4) : 𝕄₄) *ᵥ x) = x := fun x => by
    rw [← wedgeMat4_mulVec_mul, mul_inv_cancel, wedgeMat4_mulVec_one]
  symm
  refine Nat.card_congr
    { toFun := fun x => ⟨wedgeMat4 (h : 𝕄₄) *ᵥ x.1, fun u hu => ?_⟩
      invFun := fun x => ⟨wedgeMat4 ((h⁻¹ : G4) : 𝕄₄) *ᵥ x.1, fun u hu => ?_⟩
      left_inv := fun x => Subtype.ext (hinv x.1)
      right_inv := fun x => Subtype.ext (hinv' x.1) }
  · obtain ⟨y, hy, rfl⟩ := hu
    show wedgeMat4 ((h * y * h⁻¹ : G4) : 𝕄₄) *ᵥ (wedgeMat4 (h : 𝕄₄) *ᵥ x.1) = _
    rw [wedgeMat4_mulVec_mul, wedgeMat4_mulVec_mul, hinv, x.2 y hy]
  · have h1 := x.2 (h * u * h⁻¹) ⟨u, hu, rfl⟩
    rw [wedgeMat4_mulVec_mul, wedgeMat4_mulVec_mul] at h1
    have h2 := congrArg (wedgeMat4 ((h⁻¹ : G4) : 𝕄₄) *ᵥ ·) h1
    simp only [hinv] at h2
    exact h2

theorem card_fixW4_le {Y : Subgroup G4} {P : (Fin 6 → ZMod 2) → Prop} [DecidablePred P]
    (h : ∀ x : Fin 6 → ZMod 2, (∀ u ∈ Y, wedgeMat4 (u : 𝕄₄) *ᵥ x = x) → P x) :
    Nat.card (FixW4 Y) ≤ (Finset.univ.filter P).card := by
  rw [← card_subtype_eq]
  exact card_subtype_mono h

theorem card_mul_fixW4_le {Y : Subgroup G4} (hc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (h2 : ∀ a ∈ Y, a * a = 1) :
    Nat.card Y * Nat.card (FixW4 Y) ≤ 64 ∧
      (64 ≤ Nat.card Y * Nat.card (FixW4 Y) → Y ≠ ⊥ → Nat.card Y = 8) := by
  classical
  obtain ⟨h, hh⟩ := exists_conj_le_U4 (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq Y h2)
  set E := Y.map (MulAut.conj h).toMonoidHom with hE
  have hEc : Nat.card E = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hEf : Nat.card (FixW4 E) = Nat.card (FixW4 Y) := card_fixW4_conj Y h
  have hmapE : ∀ {M : G4}, M ∈ E → ∃ y ∈ Y, M = h * y * h⁻¹ := by
    intro M hM
    obtain ⟨y, hy, hyM⟩ := Subgroup.mem_map.1 hM
    refine ⟨y, hy, ?_⟩
    rw [← hyM, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hEU : ∀ M ∈ E, IsUp4 (M : 𝕄₄) := by
    intro M hM
    obtain ⟨y, hy, rfl⟩ := hmapE hM
    exact hh y hy
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := hmapE ha
    obtain ⟨b', hb', rfl⟩ := hmapE hb
    have e1 : h * a' * h⁻¹ * (h * b' * h⁻¹) = h * (a' * b') * h⁻¹ := by group
    have e2 : h * b' * h⁻¹ * (h * a' * h⁻¹) = h * (b' * a') * h⁻¹ := by group
    rw [e1, e2, hc a' ha' b' hb']
  have hEsq : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := hmapE ha
    have e1 : h * a' * h⁻¹ * (h * a' * h⁻¹) = h * (a' * a') * h⁻¹ := by group
    rw [e1, h2 a' ha', mul_one, mul_inv_cancel]
  have key := card_mul_fix4_le hEU hEcomm hEsq
  rw [hEc] at key
  rw [← hEf]
  refine ⟨key, fun hge hY1 => ?_⟩
  set T := codesOf Y h with hT
  have hTg : IsCodeGroup T := isCodeGroup_codesOf hc h2
  have hTc : T.card = Nat.card Y := card_codesOf hh
  have hmemE : ∀ c ∈ T, uOf c ∈ E := fun c hc' => by
    refine Subgroup.mem_map.2 ⟨h⁻¹ * uOf c * h, mem_codesOf.1 hc', ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hfixT : ∀ x : Fin 6 → ZMod 2, (∀ u ∈ E, wedgeMat4 (u : 𝕄₄) *ᵥ x = x) →
      ∀ c ∈ T, w4 (up4 c) *ᵥ x = x := fun x hx c hc' => by
    have h1 := hx _ (hmemE c hc')
    rw [show ((uOf c : G4) : 𝕄₄) = up4 c from rfl, ← w4_eq_wedgeMat4] at h1
    exact h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (CFSG.QuasithinUnique.B42A57.isPGroup_two_of_sq Y h2).exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hY1
    exact Subgroup.card_eq_one.1 (by rw [hk, pow_zero])
  have h4T : ∀ {m : ℕ}, 2 ^ m ≤ T.card → m ≤ k := fun {m} hm => by
    rw [hTc, hk] at hm
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hm
  by_contra h8
  have hk3 : k ≠ 3 := fun h3 => h8 (by rw [hk, h3]; norm_num)
  rcases (by omega : k = 1 ∨ k = 2 ∨ 4 ≤ k) with rfl | rfl | hk4
  ·
    obtain ⟨c, hcT, hc0⟩ : ∃ c ∈ T, c ≠ 0 := by
      by_contra hall
      push Not at hall
      have : T ⊆ {0} := fun c hc' => Finset.mem_singleton.2 (hall c hc')
      have := Finset.card_le_card this
      rw [hTc, hk] at this
      simp at this
    have hle := card_fixW4_le (Y := E) (fun x hx => hfixT x hx c hcT)
    have h16 := fix_one_le c (hTg.sq c hcT) hc0
    rw [hk] at hge
    have : 2 ^ 1 * Nat.card (FixW4 E) ≤ 2 * 16 := Nat.mul_le_mul_left _ (hle.trans h16)
    omega
  ·
    obtain ⟨c, hcT, d, hdT, hc0, hd0, hcd⟩ := exists_two_codes (T := T) (by rw [hTc, hk]; norm_num)
    have hle := card_fixW4_le (Y := E) (P := fun x => w4 (up4 c) *ᵥ x = x ∧
      w4 (up4 d) *ᵥ x = x) (fun x hx => ⟨hfixT x hx c hcT, hfixT x hx d hdT⟩)
    have h8' := fix_two_le c d (hTg.sq c hcT) (hTg.sq d hdT) hc0 hd0 hcd (hTg.comm c hcT d hdT)
    rw [hk] at hge
    have : 2 ^ 2 * Nat.card (FixW4 E) ≤ 4 * 8 := Nat.mul_le_mul_left _ (hle.trans h8')
    omega
  ·
    have h16 : 16 ≤ T.card := by
      rw [hTc, hk]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk4
    obtain ⟨hT16, -, -⟩ := codes_q4 hTg h16
    have hsub : T ⊆ Finset.univ.filter InQ4 := by
      intro c hc'
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, mem_q4 c (hTg.sq c hc') (h16.trans (Finset.card_le_card ?_))⟩
      intro d hd
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hTg.sq d hd, hTg.comm c hc' d hd⟩
    have heq : T = Finset.univ.filter InQ4 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [card_q4, hT16])
    have hle := card_fixW4_le (Y := E) (P := fun x => ∀ c : Fin 64, InQ4 c → w4 (up4 c) *ᵥ x = x)
      (fun x hx c hc' => hfixT x hx c (by rw [heq, Finset.mem_filter]; exact ⟨Finset.mem_univ _,
        hc'⟩))
    have h2' := fix_q4_le2
    rw [← hTc, hT16] at hge
    have : 16 * Nat.card (FixW4 E) ≤ 16 * 2 := Nat.mul_le_mul_left _ (hle.trans h2')
    omega

variable {V : Type} [CommGroup V] [Finite V] {G L A : Subgroup (MulAut V)}

section Coords

variable [Module (ZMod 2) (Additive V)] {e : ↥L ≃* ↥(StatedSL 4 (ZMod 2))}
  {β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}

omit [Finite V] in
theorem coord_fL4 (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w)) (g : G4)
    (v : V) : β (Additive.ofMul (fL4 e g v)) = wedgeMat4 (g : 𝕄₄) *ᵥ β (Additive.ofMul v) := by
  have h := hβ g (Additive.ofMul v)
  rw [repOf4_apply, wedgeRep4'_apply] at h
  exact h

omit [Finite V] in
theorem card_fixV_map_fL4 (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w))
    (Y : Subgroup G4) : Nat.card (fixV (Y.map (fL4 e))) = Nat.card (FixW4 Y) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨β (Additive.ofMul (v : V)), fun u hu => ?_⟩
      invFun := fun x => ⟨Additive.toMul (β.symm x.1), ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun x => Subtype.ext ?_ }
  · rw [← coord_fL4 hβ u v, v.2 (fL4 e u) ⟨u, hu, rfl⟩]
  · rintro _ ⟨u, hu, rfl⟩
    apply Additive.ofMul.injective
    apply β.injective
    rw [coord_fL4 hβ, ofMul_toMul, LinearEquiv.apply_symm_apply]
    exact x.2 u hu
  · show Additive.toMul (β.symm (β (Additive.ofMul (v : V)))) = v
    rw [LinearEquiv.symm_apply_apply, toMul_ofMul]
  · show β (Additive.ofMul (Additive.toMul (β.symm x.1))) = x.1
    rw [ofMul_toMul, LinearEquiv.apply_symm_apply]

omit [Finite V] in
theorem card_V_eq4 (β : Additive V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) : Nat.card V = 2 ^ 6 := by
  rw [show Nat.card V = Nat.card (Additive V) from rfl, Nat.card_congr β.toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  rfl

omit [Finite V] [Module (ZMod 2) (Additive V)] in
theorem map_fL4_comap {B : Subgroup (MulAut V)} (hBL : B ≤ L) :
    (B.comap (fL4 e)).map (fL4 e) = B := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hx
    obtain ⟨g, rfl⟩ := exists_fL4_eq e (hBL hx)
    exact ⟨g, hx, rfl⟩

omit [Finite V] in
theorem card_mul_fixV_le4 (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w))
    {B : Subgroup (MulAut V)} (hBL : B ≤ L) (hB : IsElemAbelian2 B) :
    Nat.card B * Nat.card (fixV B) ≤ 2 ^ 6 ∧
      (2 ^ 6 ≤ Nat.card B * Nat.card (fixV B) → B ≠ ⊥ → Nat.card B = 8) := by
  set Y : Subgroup G4 := B.comap (fL4 e) with hY
  have hBY : Y.map (fL4 e) = B := map_fL4_comap hBL
  have hcard : Nat.card B = Nat.card Y := (card_comap4_eq e hBL).symm
  have hfix : Nat.card (fixV B) = Nat.card (FixW4 Y) := by
    rw [← card_fixV_map_fL4 hβ Y, hBY]
  have key := card_mul_fixW4_le (comm_of_comap4 (e := e) hB) (sq_of_comap4 (e := e) hB)
  rw [hcard, hfix]
  refine ⟨key.1, fun hge hB1 => key.2 hge ?_⟩
  intro h0
  apply hB1
  rw [← hBY, hY, h0, Subgroup.map_bot]

theorem case10_eq_core (hV : ∀ v : V, v ^ 2 = 1) (hHyp : B4HypCore G L)
    (hZ : Subgroup.center ↥L = ⊥) (hA : IsFFStarOffender G A)
    (hβ : ∀ g w, β (repOf4 (phiOf4 e) g w) = wedgeRep4' g (β w)) (hGL : G = L) :
    B42Case10 G L A := by
  have hV6 : Nat.card V = 2 ^ 6 := card_V_eq4 β
  have hJ : ffJ G = L := le_antisymm (hGL ▸ B6.ffJ_le G) (B5.Ln.le_ffJ_of_center_core hHyp hZ hA)
  have hAL : A ≤ L := hGL ▸ hA.1
  have hoff : 2 ^ 6 ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.card_le (bot_le : (⊥ : Subgroup (MulAut V)) ≤ A)
    rwa [B1.card_bot_mul_card_fixV, hV6] at this
  have h8 := (card_mul_fixV_le4 hβ hAL hA.2.2.1).2 hoff hA.2.1
  refine ⟨slExteriorTwo_of_wedge4 e hβ, Or.inl ⟨hGL.trans hJ.symm, hJ, ?_, ?_⟩⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    unfold rk
    rw [h8, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  · refine qOf_eq_of_offenders hV le_rfl (fun B hB => ?_) ⟨A, hA, ?_⟩
    · have hBL : B ≤ L := hGL ▸ hB.1
      have hle := (card_mul_fixV_le4 hβ hBL hB.2.2.1).1
      rw [← not_lt, rAV_lt_one_iff hV hB.isA2, not_lt, hV6]
      exact hle
    · rw [rAV_le_one_iff hV hA.isA2, hV6]
      exact hoff

end Coords

end CFSG.Quasithin.B42Ln
