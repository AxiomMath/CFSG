module

public import CFSG.Quasithin.Vol2.Ch10SecCWE
public import CFSG.Quasithin.Background.B1MoreQuot
public import CFSG.Quasithin.Background.G2SixCore

public section

namespace CFSG.Quasithin.Vol2.Ch10.G16

open CFSG.Quasithin CFSG.Quasithin.SL2Model CFSG.QuasithinUnique
open scoped MatrixGroups

variable {U : Type} [CommGroup U] {F : Type} [Field F] {Gm R : Subgroup (MulAut U)}

theorem le_stabSub_fixV (Gm : Subgroup (MulAut U)) : Gm ≤ stabSub (fixV Gm) := fun g hg u => by
  constructor
  · intro h
    have h1 : g⁻¹ (g u) = g u := h _ (inv_mem hg)
    rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h1
    rw [h1]
    exact h
  · intro h
    rw [h g hg]
    exact h

@[expose] noncomputable def rho (e' : ↥Gm ≃* SL(2, F)) : SL(2, F) →* MulAut (U ⧸ fixV Gm) :=
  (quotHom (fixV Gm)).comp ((Subgroup.inclusion (le_stabSub_fixV Gm)).comp e'.symm.toMonoidHom)

theorem rho_mk (e' : ↥Gm ≃* SL(2, F)) (k : SL(2, F)) (u : U) :
    rho e' k (u : U ⧸ fixV Gm) = (((e'.symm k : ↥Gm) : MulAut U) u : U ⧸ fixV Gm) := rfl

theorem exists_equiv_rho [Finite U] [Finite F] [CharP F 2]
    (hG13 : G1.Theorem_G_1_3 F 2 (le_refl 2)) {e' : ↥Gm ≃* SL(2, F)} (hU : ∀ u : U, u ^ 2 = 1)
    (hRG : R ≤ Gm) (he' : ∀ x : ↥Gm, (x : MulAut U) ∈ R ↔ e' x ∈ Rg F)
    (hC : ∀ r ∈ R, r ≠ 1 → fixV (Subgroup.zpowers r) = fixV R)
    (hgen : (⨆ g ∈ Gm, (fixV R).map (g : MulAut U).toMonoidHom) = ⊤) :
    ∃ (s : ℕ) (Θ : (Fin s → Fin 2 → F) ≃+ Additive (U ⧸ fixV Gm)),
      ∀ (k : SL(2, F)) (x : Fin s → Fin 2 → F),
        Θ (fun j => k • x j) = Additive.ofMul (rho e' k (Additive.toMul (Θ x))) := by
  let _ : DistribMulAction SL(2, F) (Additive (U ⧸ fixV Gm)) := distribMulActionAdditive (rho e')
  let Y : AddSubgroup (Additive (U ⧸ fixV Gm)) :=
    Subgroup.toAddSubgroup ((fixV R).map (QuotientGroup.mk' (fixV Gm)))
  have hY : ∀ u : U, Additive.ofMul (u : U ⧸ fixV Gm) ∈ Y ↔
      ∃ a ∈ fixV R, (a : U ⧸ fixV Gm) = u := fun u =>
    (Iff.rfl : _ ↔ (u : U ⧸ fixV Gm) ∈ (fixV R).map (QuotientGroup.mk' (fixV Gm))).trans
      Subgroup.mem_map
  have hsurj : ∀ v : Additive (U ⧸ fixV Gm), ∃ u : U, Additive.ofMul (u : U ⧸ fixV Gm) = v :=
      fun v => by
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨u, by rw [hu]; rfl⟩
  have hsmul : ∀ (k : SL(2, F)) (u : U), k • Additive.ofMul (u : U ⧸ fixV Gm) =
      Additive.ofMul ((((e'.symm k : ↥Gm) : MulAut U) u : U) : U ⧸ fixV Gm) := fun _ _ => rfl
  have hsq : ∀ v : Additive (U ⧸ fixV Gm), v + v = 0 := fun v => by
    obtain ⟨u, rfl⟩ := hsurj v
    rw [← ofMul_mul, ← QuotientGroup.mk_mul, ← pow_two, hU, QuotientGroup.mk_one, ofMul_one]
  have hinv : ∀ k : SL(2, F), k.1 1 0 = 0 → ∀ y ∈ Y, k • y ∈ Y := by
    intro k hk y hy
    obtain ⟨u, rfl⟩ := hsurj y
    obtain ⟨a, ha, hau⟩ := (hY u).1 hy
    rw [← hau, hsmul]
    exact (hY _).2 ⟨_, apply_mem_fixV_of_lower_left_eq_zero hRG he' hk ha, rfl⟩
  have hcomm : ∀ t ∈ Rg F, ∀ v : Additive (U ⧸ fixV Gm), t • v - v ∈ Y := by
    intro t ht v
    obtain ⟨u, rfl⟩ := hsurj v
    rw [hsmul, ← ofMul_div, ← QuotientGroup.mk_div, div_eq_mul_inv]
    exact (hY _).2 ⟨_, mul_inv_mem_fixV hU hRG he' hC (symm_mem_R he' ht) u, rfl⟩
  have hfix : ∀ t ∈ Rg F, ∀ y ∈ Y, t • y = y := by
    intro t ht y hy
    obtain ⟨u, rfl⟩ := hsurj y
    obtain ⟨a, ha, hau⟩ := (hY u).1 hy
    rw [← hau, hsmul, ha _ (symm_mem_R he' ht)]
  set x : ↥Gm := e'.symm (e21 1) with hx
  have hdisj : Y ⊓ Y.map (G1.actU (e21 (1 : F))) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, y', hy', hyv⟩ := hv
    obtain ⟨u, rfl⟩ := hsurj v
    obtain ⟨a, ha, hau⟩ := (hY u).1 hv1
    obtain ⟨u', rfl⟩ := hsurj y'
    obtain ⟨a', ha', hau'⟩ := (hY u').1 hy'
    have h1 : ((a : U) : U ⧸ fixV Gm) = (((x : MulAut U) a' : U) : U ⧸ fixV Gm) := by
      have h2 : Additive.ofMul ((a : U) : U ⧸ fixV Gm) =
          Additive.ofMul ((((x : MulAut U) a' : U)) : U ⧸ fixV Gm) := by
        rw [hau, ← hyv, ← hau']
        rfl
      exact h2
    have hmem : a * ((x : MulAut U) a')⁻¹ ∈ fixV Gm := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1,
        mul_inv_cancel]
    have haZ := mem_fixV_of_mul_inv_mem hRG he' ha ha' hmem
    rw [← hau, (QuotientGroup.eq_one_iff a).2 haZ, ofMul_one]
    exact AddSubgroup.zero_mem _
  have hsup : Y ⊔ Y.map (G1.actU (e21 (1 : F))) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨u, rfl⟩ := hsurj v
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_eq_mul_apply hU hRG he' hC hgen u
    rw [QuotientGroup.mk_mul, ofMul_mul]
    refine AddSubgroup.add_mem_sup ((hY a).2 ⟨a, ha, rfl⟩) ⟨Additive.ofMul (b : U ⧸ fixV Gm),
      (hY b).2 ⟨b, hb, rfl⟩, ?_⟩
    rfl
  obtain ⟨s, Θ, hΘ, -, -⟩ := G1.exists_equiv_of_halves hG13 hsq Y (e21 (1 : F))
    e21_one_lower_left.1 hinv hcomm hfix hdisj hsup
  exact ⟨s, Θ, hΘ⟩

end CFSG.Quasithin.Vol2.Ch10.G16
