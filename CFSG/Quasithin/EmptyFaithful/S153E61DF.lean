module

public import CFSG.Quasithin.EmptyFaithful.S153E61DE
public import CFSG.Quasithin.EmptyFaithful.S152N2Lin
public import CFSG.Quasithin.EmptyFaithful.S153E60
public import CFSG.Quasithin.EmptyFaithful.S153E61DD

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open CFSG.Quasithin.S153E
open scoped commutatorElement Pointwise MatrixGroups

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace S153E61D

section Tau

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N N' : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ}

theorem exists_tau_aux {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) :
    ∃ τ : Subgroup.normalizer (VZ T M : Set G), (τ : G) ∈ UH153 T M V₁ Mc ∧
      convI cx.c.hyp.elemAbelian τ ≠ 1 ∧ convI cx.c.hyp.elemAbelian τ ∈ N' ∧
      convI cx.c.hyp.elemAbelian τ * convI cx.c.hyp.elemAbelian τ = 1 ∧
      Even (rk (commV (Subgroup.zpowers (convI cx.c.hyp.elemAbelian τ)))) := by
  have hV := cx.c.hyp.elemAbelian
  have h53 := d.c54.h53one
  have hK4 : IsKleinFour153 (autI hV (UH153 T M V₁ Mc)) := by
    rcases d.c54.h51.two with h | ⟨hab, -, -, -⟩
    · exact h.2.1
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := d.c54.h52
      exact hne (B2F.isElemAbelian_comm hab ha hb)
  have hKle : autI hV (UH153 T M V₁ Mc) ≤ N ⊔ N' := by
    rw [← S153E55.autI_YU_eq cx h53]
    exact autI_mono hV le_sup_right
  obtain ⟨e₁⟩ := h53.iso₁
  obtain ⟨ū, hūK, hū1, hūN'⟩ := exists_mem_of_klein hK4 hKle h53.comm h53.inf e₁
  obtain ⟨τ', hτ'U, rfl⟩ := (mem_autI hV).1 hūK
  refine ⟨τ', hτ'U, hū1, hūN', ?_, ?_⟩
  · have := hK4.2.2 _ hūK
    simpa [pow_two] using this
  · exact isDicksonEven_of_mem_autOn_U cx d.c54.h51 d.c54.h52 hūK

theorem exists_tau {cx : Ctx15350 T Mc M V₁ V₂ t} (d : Dat61 cx N N' g s) {δ : G}
    (hδ : δ ∈ Ni153 T Mc M V₁ N') (hδ3 : δ ^ 3 = 1)
    (hδfix : ∀ v ∈ VZ T M, δ * v * δ⁻¹ = v → v = 1) :
    ∃ τ ∈ UH153 T M V₁ Mc, τ * δ * τ⁻¹ * δ ∈ Pgp153 T M V₁ Mc g ∧
      ∃ ℓ ∈ VZ T M, ℓ ∈ UH153 T M V₁ Mc ∧ τ * ℓ * τ⁻¹ ≠ ℓ := by
  have hV := cx.c.hyp.elemAbelian
  have h53 := d.c54.h53one
  have hI : Igp153 T M V₁ Mc g = Y153 Mc M ⊔ UH153 T M V₁ Mc := d.c54.h54.one
  obtain ⟨τ', hτ'U, hū1, hūN', hūsq, hdick⟩ := exists_tau_aux d
  refine ⟨(τ' : G), hτ'U, ?_, ?_⟩
  ·
    obtain ⟨hδYU, hδN, hdbar⟩ := mem_preAut153.1 hδ
    obtain ⟨hδN, hdbar⟩ : ∃ hg : δ ∈ Subgroup.normalizer (VZ T M : Set G),
        convI hV ⟨δ, hg⟩ ∈ N' := ⟨hδN, hdbar⟩
    obtain ⟨e₂⟩ := h53.iso₂
    have hd3 : (⟨convI hV ⟨δ, hδN⟩, hdbar⟩ : ↥N') ^ 3 = 1 := by
      apply Subtype.ext
      have h3 : (⟨δ, hδN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hδ3)
      have h4 := map_pow (convI hV) (⟨δ, hδN⟩ : Subgroup.normalizer (VZ T M : Set G)) 3
      rw [h3, map_one] at h4
      exact h4.symm
    have hd1 : (⟨convI hV ⟨δ, hδN⟩, hdbar⟩ : ↥N') ≠ 1 := by
      intro h1
      have h2 : convI hV ⟨δ, hδN⟩ = 1 := congrArg Subtype.val h1
      have hc := (convI_eq_one_iff hV _).1 h2
      have hall : ∀ v ∈ VZ T M, v = 1 := fun v hv => by
        apply hδfix v hv
        have := Subgroup.mem_centralizer_iff.1 hc v hv
        calc δ * v * δ⁻¹ = (v * δ) * δ⁻¹ := by rw [← this]
          _ = v := by group
      have h16 := cx.c.hyp.card_VZ
      have : Subsingleton ↥(VZ T M) := ⟨fun a b => Subtype.ext ((hall a a.2).trans (hall b b.2).symm)⟩
      have := Nat.card_unique (α := ↥(VZ T M))
      omega
    have hu2 : (⟨_, hūN'⟩ : ↥N') * ⟨_, hūN'⟩ = 1 := Subtype.ext hūsq
    have hu1 : (⟨_, hūN'⟩ : ↥N') ≠ 1 := fun h => hū1 (congrArg Subtype.val h)
    have hinv := perm3_invert (e₂ ⟨_, hūN'⟩) (e₂ ⟨convI hV ⟨δ, hδN⟩, hdbar⟩)
      (by rw [← map_mul, hu2, map_one]) (fun h => hu1 (e₂.injective (h.trans (map_one e₂).symm)))
      (by rw [← map_pow, hd3, map_one]) (fun h => hd1 (e₂.injective (h.trans (map_one e₂).symm)))
    have hinv' : (⟨_, hūN'⟩ : ↥N') * ⟨convI hV ⟨δ, hδN⟩, hdbar⟩ * (⟨_, hūN'⟩ : ↥N')⁻¹ *
        ⟨convI hV ⟨δ, hδN⟩, hdbar⟩ = 1 := by
      apply e₂.injective
      simp only [map_mul, map_inv, map_one]
      exact hinv
    have hinv'' : convI hV τ' * convI hV ⟨δ, hδN⟩ * (convI hV τ')⁻¹ * convI hV ⟨δ, hδN⟩ = 1 :=
      congrArg Subtype.val hinv'
    have hxN : (τ' : G) * δ * (τ' : G)⁻¹ * δ ∈ Subgroup.normalizer (VZ T M : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ τ'.2 hδN) (Subgroup.inv_mem _ τ'.2)) hδN
    have hconv : convI hV ⟨(τ' : G) * δ * (τ' : G)⁻¹ * δ, hxN⟩ = 1 := by
      have e : (⟨(τ' : G) * δ * (τ' : G)⁻¹ * δ, hxN⟩ : Subgroup.normalizer (VZ T M : Set G)) =
          τ' * ⟨δ, hδN⟩ * τ'⁻¹ * ⟨δ, hδN⟩ := Subtype.ext rfl
      rw [e, map_mul, map_mul, map_mul, map_inv]
      exact hinv''
    have hxYU : (τ' : G) * δ * (τ' : G)⁻¹ * δ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc :=
      (Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem
        ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem
          ((Y153 Mc M ⊔ UH153 T M V₁ Mc).mul_mem (S153E55.U_le_YU hτ'U) hδYU)
          ((Y153 Mc M ⊔ UH153 T M V₁ Mc).inv_mem (S153E55.U_le_YU hτ'U))) hδYU
    exact S153E55.centralizer_le_P hI cx ⟨hxYU, (convI_eq_one_iff hV _).1 hconv⟩
  ·
    by_contra hcon
    push Not at hcon
    have hcard : Nat.card ↥(VZ T M ⊓ UH153 T M V₁ Mc) ≤
        Nat.card ↥(fixV (Subgroup.zpowers (convI hV τ'))) := by
      let f : ↥(VZ T M ⊓ UH153 T M V₁ Mc) → ↥(fixV (Subgroup.zpowers (convI hV τ'))) := fun x =>
        ⟨IntMod.mk hV ⟨x.1, x.2.1⟩, by
          rw [mem_fixV_zpowers_iff]
          apply IntMod.val_injective
          rw [convI_apply_val]
          exact hcon x.1 x.2.1 x.2.2⟩
      refine Nat.card_le_card_of_injective f ?_
      intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z => z.1.val) hxy
    have hmul := S152N2.card_fixV_mul_card_commV (V := IntMod (VZ T M) hV) hūsq
    have h16 : Nat.card (IntMod (VZ T M) hV) = 16 := cx.c.hyp.card_VZ
    have h8 := card_VU d
    have hrk0 : rk (commV (Subgroup.zpowers (convI hV τ'))) ≠ 0 := by
      intro h0
      rw [rk_eq_zero_iff IntMod.sq_eq_one] at h0
      apply hū1
      ext w
      have hw : convI hV τ' w * w⁻¹ ∈ commV (Subgroup.zpowers (convI hV τ')) :=
        Subgroup.subset_closure ⟨convI hV τ', Subgroup.mem_zpowers _, w, rfl⟩
      rw [h0, Subgroup.mem_bot] at hw
      simpa [mul_inv_eq_one] using hw
    obtain ⟨j, hj⟩ := hdick
    have hrk2 : 2 ≤ rk (commV (Subgroup.zpowers (convI hV τ'))) := by omega
    have hdvd : 2 ^ 2 ∣ Nat.card (commV (Subgroup.zpowers (convI hV τ'))) := by
      have hpos : Nat.card (commV (Subgroup.zpowers (convI hV τ'))) ≠ 0 := Nat.card_pos.ne'
      exact (padicValNat_dvd_iff_le hpos).2 hrk2
    have h4 : 4 ≤ Nat.card (commV (Subgroup.zpowers (convI hV τ'))) :=
      Nat.le_of_dvd Nat.card_pos (by simpa using hdvd)
    have hf4 : Nat.card ↥(fixV (Subgroup.zpowers (convI hV τ'))) ≤ 4 := by
      rw [h16] at hmul
      nlinarith
    omega

end Tau

end S153E61D

end CFSG.Quasithin
