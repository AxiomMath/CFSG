module

public import CFSG.Quasithin.Background.F918Q1

public section

namespace CFSG.Quasithin

section Abstract

variable {Y : Type} [CommGroup Y] [Finite Y]

theorem glued_swap_decomp {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}
    (hP : GluedPair X U U') (hUU' : U ≠ U') (hA : A ∈ QhatStar X) (hAU : ¬ A ≤ stabSub U) :
    ∃ a : MulAut Y, a ∈ A ∧ a ∉ stabSub U ∧ U.map a.toMonoidHom = U' ∧ a * a = 1 ∧
      (∀ g ∈ A ⊓ stabSub U, g * a = a * g) ∧ A = (A ⊓ stabSub U) ⊔ Subgroup.zpowers a ∧
      rk ↥A = rk ↥(A ⊓ stabSub U) + 1 := by
  obtain ⟨r, -, -, hAk, -⟩ := QhatStar_spec hA
  have hA2 : IsA2 X A := hAk.1.1
  have hAel : IsElemAbelian2 A := hA2.2.2
  obtain ⟨a, haA, haU⟩ : ∃ a ∈ A, a ∉ stabSub U := by
    by_contra hcon
    push Not at hcon
    exact hAU fun g hg => hcon g hg
  obtain ⟨ha1, ha2⟩ : U.map a.toMonoidHom = U' ∧ U'.map a.toMonoidHom = U :=
    (hP.perm a (hA2.1 haA)).resolve_left fun h => haU h.1
  have hmem : ∀ g, g ∈ A ⊓ stabSub U ↔ g ∈ A ∧ g ∈ stabSub U := fun g => Subgroup.mem_inf
  have hA₀le : A ⊓ stabSub U ≤ A := inf_le_left
  have haa : a * a = 1 := by simpa [pow_two] using hAel.2 a haA
  have hcomm : ∀ g ∈ A ⊓ stabSub U, g * a = a * g := fun g hg =>
    hAel.1 g (hA₀le hg) a haA
  have fa1 : ∀ x, a x ∈ U' ↔ x ∈ U := fun x => by rw [← ha1]; exact apply_mem_map_iffQ1 a x
  have fa2 : ∀ x, a x ∈ U ↔ x ∈ U' := fun x => by rw [← ha2]; exact apply_mem_map_iffQ1 a x
  have hAeq : A = (A ⊓ stabSub U) ⊔ Subgroup.zpowers a := by
    apply le_antisymm
    · intro g hg
      by_cases hgU : g ∈ stabSub U
      · exact Subgroup.mem_sup_left ((hmem g).mpr ⟨hg, hgU⟩)
      · rcases hP.perm g (hA2.1 hg) with ⟨h, -⟩ | ⟨hg1, hg2⟩
        · exact absurd h hgU
        · have hg1' : ∀ x, g x ∈ U' ↔ x ∈ U := fun x => by
            rw [← hg1]; exact apply_mem_map_iffQ1 g x
          have hainv : ∀ z, a⁻¹ z ∈ U ↔ z ∈ U' := fun z => by
            rw [← fa1 (a⁻¹ z)]; simp
          have hstab2 : a⁻¹ * g ∈ stabSub U := by
            intro x
            rw [MulAut.mul_apply, hainv, hg1']
          have hmem2 : a⁻¹ * g ∈ A ⊓ stabSub U :=
            (hmem _).mpr ⟨A.mul_mem (A.inv_mem haA) hg, hstab2⟩
          have : g = a * (a⁻¹ * g) := by group
          rw [this, sup_comm]
          exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers a) hmem2
    · exact sup_le hA₀le (Subgroup.zpowers_le.mpr haA)
  have hrkA : rk ↥A = rk ↥(A ⊓ stabSub U) + 1 := by
    have hidx : ((A ⊓ stabSub U).subgroupOf A).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨a, haA⟩, fun b => ?_⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmem, hmem]
      by_cases hbU : (b : MulAut Y) ∈ stabSub U
      · right
        refine ⟨⟨b.2, hbU⟩, fun hba => ?_⟩
        apply hUU'
        ext x
        have h1 := hba.2 x
        rw [MulAut.mul_apply] at h1
        have := (hbU (a x)).trans (fa2 x)
        exact (this.symm.trans h1).symm
      · left
        refine ⟨⟨A.mul_mem b.2 haA, ?_⟩, fun hb => hbU hb.2⟩
        rcases hP.perm (b : MulAut Y) (hA2.1 b.2) with ⟨h, -⟩ | ⟨hb1, hb2⟩
        · exact absurd h hbU
        · intro x
          rw [MulAut.mul_apply]
          have hb2' : ∀ z, (b : MulAut Y) z ∈ U ↔ z ∈ U' := fun z => by
            rw [← hb2]; exact apply_mem_map_iffQ1 (b : MulAut Y) z
          rw [hb2', fa1]
    have hc := Subgroup.card_mul_index ((A ⊓ stabSub U).subgroupOf A)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀le).toEquiv] at hc
    unfold rk
    rw [← hc, padicValNat.mul Nat.card_pos.ne' (by norm_num), padicValNat_self]
  exact ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩

private def commEndS (g : MulAut Y) : Y →* Y where
  toFun w := g w * w⁻¹
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul, mul_inv_rev]
    ac_rfl

private theorem mem_ker_commEndS {g : MulAut Y} {w : Y} : w ∈ (commEndS g).ker ↔ g w = w := by
  rw [MonoidHom.mem_ker]
  change g w * w⁻¹ = 1 ↔ g w = w
  rw [mul_inv_eq_one]

private theorem rk_eq_add_rk_map (ψ : Y →* Y) (K : Subgroup Y) :
    rk ↥K = rk ↥(K ⊓ ψ.ker) + rk ↥(K.map ψ) := by
  set φ : ↥K →* Y := ψ.comp K.subtype with hφ
  have hrange : φ.range = K.map ψ := by
    ext y
    simp [hφ, MonoidHom.mem_range, Subgroup.mem_map]
  have hker : φ.ker = (K ⊓ ψ.ker).subgroupOf K := by
    ext x
    simp [hφ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hcard : Nat.card ↥K = Nat.card ↥φ.ker * Nat.card ↥φ.range := by
    rw [← Subgroup.index_ker φ]
    exact (Subgroup.card_mul_index φ.ker).symm
  have hker' : Nat.card ↥φ.ker = Nat.card ↥(K ⊓ ψ.ker) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : K ⊓ ψ.ker ≤ K)).toEquiv
  unfold rk
  rw [hcard, hker', hrange, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne']

theorem glued_swap_shape {X A : Subgroup (MulAut Y)} {U U' : Subgroup Y}
    (hP : GluedPair X U U') (hUU' : U ≠ U') (h3 : rk ↥(U ⊓ U') + 2 < rk ↥U)
    (hA : A ∈ QhatStar X) (hAU : ¬ A ≤ stabSub U) :
    A ⊓ stabSub U ≠ ⊥ ∧
      2 * rk ↥U ≤ rk ↥(U ⊓ U' ⊓ fixV (A ⊓ stabSub U)) +
        rk ↥(commModSub U (A ⊓ stabSub U) (U ⊓ U')) + 2 * (rk ↥(A ⊓ stabSub U) + 1) ∧
      rk ↥(U ⊓ fixV (A ⊓ stabSub U)) ≤ rk ↥(U ⊓ U') + 1 := by
  obtain ⟨r, -, hr2, hAk, hmin⟩ := QhatStar_spec hA
  obtain ⟨a, haA, haU, ha1, haa, hcomm, hAeq, hrkA⟩ := glued_swap_decomp hP hUU' hA hAU
  have hA2 : IsA2 X A := hAk.1.1
  have hAr : rAV A = r := hAk.1.2
  have hAk3 : commSeries A 3 = ⊥ := hAk.2
  set B := A ⊓ stabSub U with hB
  have hBA : B ≤ A := inf_le_left
  have hstab : B ≤ stabSub U := inf_le_right
  have hsum' : U ⊔ U.map a.toMonoidHom = ⊤ := by rw [ha1]; exact hP.sup_eq
  have hDeq : U ⊓ U.map a.toMonoidHom = U ⊓ U' := by rw [ha1]
  have hFeq : fixV A = fixV B ⊓ fixV (Subgroup.zpowers a) := by
    rw [← fixV_sup_eq_inf_fixV, ← hAeq]
  have hrA : rkIdx (fixV A) ≤ 2 * rk ↥A := by
    have h1 := hA2.rAV_mul
    have h2 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
      rw [← h1, hAr]
      exact mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg _)
    exact_mod_cast h2
  have hY1 : rk Y ≤ rk ↥(fixV B ⊓ fixV (Subgroup.zpowers a)) + 2 * (rk ↥B + 1) := by
    have h := rk_add_rkIdx (fixV A)
    rw [hFeq] at h hrA
    rw [hrkA] at hrA
    omega
  have h1 := rk_fixV_swap_le haa hcomm hstab hsum'
  have h2 := rk_sup_swap_add_rk_inf hsum'
  rw [hDeq] at h1 h2
  have hb : 2 * rk ↥U ≤ rk ↥(U ⊓ U' ⊓ fixV B) + rk ↥(commModSub U B (U ⊓ U')) +
      2 * (rk ↥B + 1) := by omega
  have hBne : B ≠ ⊥ := by
    intro hbot
    have hh : commModSub U B (U ⊓ U') = U := by
      ext u
      constructor
      · exact fun h => h.1
      · intro hu
        refine ⟨hu, fun g hg => ?_⟩
        rw [hbot, Subgroup.mem_bot] at hg
        subst hg
        simp
    have hfix : fixV B = ⊤ := by
      ext v
      simp [hbot, mem_fixV]
    have hb0 : rk ↥B = 0 := by rw [hbot]; exact rk_bot
    rw [hh, hfix, hb0, inf_top_eq] at hb
    have hDU : rk ↥(U ⊓ U') ≤ rk ↥U := rk_mono inf_le_left
    omega
  refine ⟨hBne, hb, ?_⟩
  have hBlt : B < A := lt_of_le_of_ne hBA fun h => haU (hstab (h ▸ haA))
  have hBA2 : IsA2 X B := hA2.mono hBA hBne
  have hBk : commSeries B 3 = ⊥ := le_bot_iff.mp (hAk3 ▸ commSeries_mono hBA 3)
  have hrB : r < rAV B := by
    by_contra hle
    push Not at hle
    exact hBlt.ne (hmin B ⟨⟨hBA2, hle⟩, hBk⟩ hBA)
  have hBrk : 0 < rk ↥B := hBA2.rk_pos
  have hmulA : (rkIdx (fixV A) : ℚ) = r * ((rk ↥B : ℚ) + 1) := by
    have h := hA2.rAV_mul
    rw [hAr, hrkA] at h
    push_cast at h
    exact h.symm
  have hmulB : r * (rk ↥B : ℚ) < rkIdx (fixV B) := by
    unfold rAV at hrB
    rwa [lt_div_iff₀ (by exact_mod_cast hBrk)] at hrB
  have hAB : fixV A ≤ fixV B := hFeq ▸ inf_le_left
  have hlt : rkIdx (fixV A) < rkIdx (fixV B) + 2 := by
    have : (rkIdx (fixV A) : ℚ) < rkIdx (fixV B) + 2 := by
      rw [hmulA]
      nlinarith
    exact_mod_cast this
  have hψ : (commEndS a).ker = fixV (Subgroup.zpowers a) := by
    ext v
    rw [mem_ker_commEndS, mem_fixV_zpowers_iff_apply]
  have hC := rk_eq_add_rk_map (commEndS a) (fixV B)
  have hC1 := rk_eq_add_rk_map (commEndS a) (U ⊓ fixV B)
  rw [hψ, ← hFeq] at hC
  rw [hψ] at hC1
  have hmap : rk ↥((U ⊓ fixV B).map (commEndS a)) ≤ rk ↥((fixV B).map (commEndS a)) :=
    rk_mono (Subgroup.map_mono inf_le_right)
  have hDle : U ⊓ fixV B ⊓ fixV (Subgroup.zpowers a) ≤ U ⊓ U' := by
    rintro v ⟨⟨hvU, -⟩, hva⟩
    have hav : a v = v := mem_fixV_zpowers_iff_apply.mp hva
    refine ⟨hvU, ?_⟩
    have : a v ∈ U' := ha1 ▸ Subgroup.mem_map_of_mem a.toMonoidHom hvU
    rwa [hav] at this
  have hrD := rk_mono hDle
  have e1 := rk_add_rkIdx (fixV A)
  have e2 := rk_add_rkIdx (fixV B)
  omega

end Abstract

end CFSG.Quasithin
