module

public import CFSG.Quasithin.EmptyFaithful.S153E58P
public import CFSG.Quasithin.EmptyFaithful.S153E58E
public import CFSG.Quasithin.EmptyFaithful.S153E58G
public import CFSG.Quasithin.EmptyFaithful.S153E58J
public import CFSG.Quasithin.EmptyFaithful.S153E58K

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E58

open S153E57

section Core

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem card_eight_of_realizes {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : ↥(StatedSL 3 (ZMod 2)) →* ↥H}
    (h : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia H U ⊥ π) : Nat.card ↥U = 8 := by
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := h
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hbij : Function.Bijective β := ⟨hinj, hβs⟩
  rw [Nat.card_congr (Equiv.ofBijective β hbij)]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((FFModel.nat (StatedSL 3 (ZMod 2))).ker.subgroupOf (FFModel.nat (StatedSL 3 (ZMod 2))).sec)
  have h2 : Nat.card ↥((FFModel.nat (StatedSL 3 (ZMod 2))).ker.subgroupOf
      (FFModel.nat (StatedSL 3 (ZMod 2))).sec) = 1 := by
    show Nat.card ↥((⊥ : Subgroup (Multiplicative (Fin 3 → ZMod 2))).subgroupOf ⊤) = 1
    rw [Subgroup.bot_subgroupOf]
    simp
  have h3 : Nat.card ↥(FFModel.nat (StatedSL 3 (ZMod 2))).sec = 8 := by
    show Nat.card ↥(⊤ : Subgroup (Multiplicative (Fin 3 → ZMod 2))) = 8
    simp [Nat.card_eq_fintype_card]
  rw [h2, mul_one, h3] at h1
  exact h1.symm

end Core

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} {y t₁ : G}

theorem core58 (h09 : Input15309Two) (iTwo : Input15358Two) (iG93 : Input15358G93)
    (cx : Ctx15350 T Mc M V₁ V₂ t) (c : Chain15357 cx N₁ N₂ g s y t₁) :
    s = 1 ∧
      letI : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
        commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
      ∃ (K : Subgroup (MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))))
        (W₁ W₂ : Subgroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)))
        (π : ↥(StatedSL 3 (ZMod 2)) →* ↥K),
        Setup58 (HStar153 T M V₁ Mc) K W₁ W₂ (bilU cx) ∧ ⁅K, K⁆ = K ∧
          (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia K W₁ ⊥ π ∧
          ∃ u₁ ∈ W₁, u₁ ≠ 1 ∧ u₁ ∈ Pt T M V₁ Mc := by
  let _ : CommGroup ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
    commGroupOfElemAbelian cx.hF.isElemAbelian_tilde
  have c56 : Chain15356 cx N₁ N₂ g s y t₁ := c.toChain15356
  have hs : 0 < s := s_pos h09 cx c56.toChain15355.toChain15354
  obtain ⟨a, haV, ha1, ha2, hV⟩ := exists_a c56
  have haH := a_mem_HStar cx haV
  have hV2 : ∀ w ∈ XStar153 T M V₁ Mc (VZ T M), w = 1 ∨ w = a := fun w hw =>
    zpowers_involution_cases ha2 (hV ▸ hw)
  have hW : ∀ w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)), w ^ 2 = 1 := by
    intro w
    have := cx.hF.isElemAbelian_tilde.2 w w.2
    exact Subtype.ext (by simpa using this)
  have hcard : Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) =
      2 ^ (2 * (s + 2)) := card_tilde cx c56
  have hcomm : commV (Subgroup.zpowers a) = Pt T M V₁ Mc := by
    rw [← commIn153_top_eq_commV, ← hV]
    exact commIn153_eq_Pt cx c56
  have hc4 : Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2 := by
    rw [hcomm, card_Pt cx c56]
    norm_num
  have F1 : ∀ h ∈ HStar153 T M V₁ Mc, orderOf h = 3 →
      ∃ r ∈ commV (Subgroup.zpowers a), h r ∉ commV (Subgroup.zpowers a) := by
    intro h hh h3
    rw [hcomm]
    exact threePrime_N cx c56 h hh h3
  obtain ⟨z₀, hz₀1, hz₀ZS, hfixT⟩ := exists_fixed_T c56
  have hmemfix : ∀ w, w ∈ fixV (XStar153 T M V₁ Mc T) ↔ (w = 1 ∨ w = z₀) := fun w =>
    mem_fixV.trans (hfixT w)
  have hfix2 : Nat.card ↥(fixV (XStar153 T M V₁ Mc T)) = 2 := by
    rw [Nat.card_eq_two_iff' (1 : ↥(fixV (XStar153 T M V₁ Mc T)))]
    refine ⟨⟨z₀, (hmemfix z₀).2 (Or.inr rfl)⟩, fun h => hz₀1 (congrArg Subtype.val h), fun y' hy' => ?_⟩
    rcases (hmemfix y').1 y'.2 with h | h
    · exact absurd (Subtype.ext h) hy'
    · exact Subtype.ext h
  have hZS : ∀ z ∈ S153E.tildeZS T M V₁ Mc, z = 1 ∨ z = z₀ := by
    intro z hz
    by_cases hz1 : z = 1
    · exact Or.inl hz1
    · right
      obtain ⟨y', -, hy'⟩ := (Nat.card_eq_two_iff' (1 : ↥(S153E.tildeZS T M V₁ Mc))).1
        (S153E.card_tildeZS cx)
      have h1 : (⟨z, hz⟩ : ↥(S153E.tildeZS T M V₁ Mc)) = y' :=
        hy' _ (fun h => hz1 (congrArg Subtype.val h))
      have h2 : (⟨z₀, hz₀ZS⟩ : ↥(S153E.tildeZS T M V₁ Mc)) = y' :=
        hy' _ (fun h => hz₀1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  have F2 : ∀ h ∈ HStar153 T M V₁ Mc, orderOf h = 3 →
      ∃ z ∈ fixV (XStar153 T M V₁ Mc T), h z ≠ z := by
    intro h hh h3
    obtain ⟨z, hz, hne⟩ := threePrime_ZS cx h hh h3
    exact ⟨z, mem_fixV.2 ((hfixT z).2 (hZS z hz)), hne⟩
  obtain ⟨hAH, hAab, hAsq, hAcard⟩ := XS_data c56
  have haA : a ∈ XS T M V₁ Mc y := Vs_le_XS c56 haV
  obtain ⟨D, hDH, hDa, haD⟩ := exists_D c56 hs haV
  have h57 : Hyp57Two (HStar153 T M V₁ Mc) a s := by
    intro Kst hK1 hK2 hK3 hK4 hK5
    have := c.h57.two Kst hK1 hK2 hK3 hK4 hK5
    rw [hV] at this
    exact this
  obtain ⟨K, W₁, W₂, π, hKmin, hperf, hnonab, hdir, hirr₁, hirr₂, hc₁, hc₂, ha₁, ha₂, hcm₁, hcm₂, hπ⟩ :=
    abs_case_analysis iTwo iG93 hW (irr_H cx c56) (S153E.pCoreOf_HStar_eq_bot cx)
      (S153E.isQuotientOfSQTKCat_HStar cx) haH ha1 ha2 hc4 hs hcard F1 (XStar153 T M V₁ Mc T)
      (S153E.isSylowTwoOf_HStar_T cx) (a_mem_T cx haV) (fun x hx => a_central cx ha1 hV hV2 x hx)
      hfix2 F2 (XS T M V₁ Mc y) hAH hAab hAsq hAcard haA D hDH hDa haD h57
  have h8 : Nat.card ↥W₁ = 8 := card_eight_of_realizes hπ
  have hs1 : s = 1 := by
    have h2 : 2 ^ (s + 2) = 2 ^ 3 := by rw [← hc₁, h8]; norm_num
    have := Nat.pow_right_injective (le_refl 2) h2
    omega
  have hsub₁ : commIn153 (Subgroup.zpowers a) W₁ ≤ W₁ := by
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨b, hb, w, hw, rfl⟩
    have hbw : b w ∈ W₁ := by
      rcases zpowers_involution_cases ha2 hb with rfl | rfl
      · simpa using hw
      · exact ha₁ w hw
    exact W₁.mul_mem hbw (W₁.inv_mem hw)
  have hsubPt : commIn153 (Subgroup.zpowers a) W₁ ≤ Pt T M V₁ Mc := by
    rw [← hcomm, ← commIn153_top_eq_commV]
    refine Subgroup.closure_mono ?_
    rintro x ⟨b, hb, w, hw, rfl⟩
    exact ⟨b, hb, w, Subgroup.mem_top _, rfl⟩
  obtain ⟨y', hne, -⟩ := (Nat.card_eq_two_iff' (1 : ↥(commIn153 (Subgroup.zpowers a) W₁))).1 hcm₁
  refine ⟨hs1, K, W₁, W₂, π, ?_, hperf, hπ,
    (y' : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))), hsub₁ y'.2,
    fun h => hne (Subtype.ext h), hsubPt y'.2⟩
  exact
    { KH := hKmin.1
      Kn := hKmin.2.1
      K1 := hKmin.2.2.1
      dir := hdir
      irr₁ := hirr₁
      irr₂ := hirr₂
      Hirr := irr_H cx c56
      card₁ := h8
      card₂ := by rw [hc₂, hs1]; norm_num
      bil_left := bilU_left cx
      bil_right := bilU_right cx
      bil_symm := bilU_symm cx
      bil_nondeg := bilU_nondeg cx c56.h56.orth_nondeg
      bil_inv := fun h hh a b => bilU_inv cx hh a b }

end Main

end S153E58

end CFSG.Quasithin
