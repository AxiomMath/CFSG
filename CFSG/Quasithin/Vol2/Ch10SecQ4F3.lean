module

public import CFSG.Quasithin.Vol2.Ch10SecQ4F2
public import CFSG.Quasithin.Background.G64Linear
public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecG.C10E4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {V : Type} [CommGroup V]

theorem exists_proper_of_fix_three [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    {G : Subgroup (MulAut V)} {a : MulAut V} (h61 : G64.Hyp61 G a) {v₁ : V}
    (hc : commV (Subgroup.zpowers a) = Subgroup.zpowers v₁) {P : Subgroup (MulAut V)}
    (hPG : P ≤ G) (hP2 : IsPGroup 2 P) (h3 : ∀ u : V, ∃ x ∈ G, orderOf x = 3 ∧ x u = u) :
    ∃ X : Subgroup (MulAut V), P ≤ X ∧ X < G ∧ ∃ x ∈ X, orderOf x = 3 := by
  set K := conjClosure (Subgroup.zpowers a) G with hK
  set C := fixV K with hCdef
  have hGK : ∀ g ∈ G, ∀ k ∈ K, g⁻¹ * k * g ∈ K := fun g hg k hk =>
    (Subgroup.mem_normalizer_iff''.mp (le_normalizer_conjClosure _ G hg) k).mp hk
  have hC : ∀ g ∈ G, ∀ c ∈ C, g c ∈ C := fun g hg _ hc =>
    apply_mem_fixV_of_normalizes (hGK g hg) hc
  have haK : a ∈ K := le_conjClosure _ G (Subgroup.mem_zpowers a)
  have hCtop : C ≠ ⊤ := by
    intro h
    apply h61.ne_one
    ext w
    have hw : w ∈ C := h ▸ Subgroup.mem_top w
    exact hw a haK
  let _ : MulAction ↥P (V ⧸ C) :=
    { smul := fun p q => QuotientGroup.map C C (p : MulAut V).toMonoidHom
        (fun c hc => hC p (hPG p.2) c hc) q
      one_smul := fun q => by
        induction q using QuotientGroup.induction_on
        rfl
      mul_smul := fun p p' q => by
        induction q using QuotientGroup.induction_on
        rfl }
  have hsmul : ∀ (p : ↥P) (w : V), p • (QuotientGroup.mk w : V ⧸ C) =
      QuotientGroup.mk ((p : MulAut V) w) := fun _ _ => rfl
  obtain ⟨q, hq1, hqfix⟩ := G64.exists_fixed_ne_one (A := V ⧸ C) (Q := ↥P) hP2
    (fun q => by
      induction q using QuotientGroup.induction_on with
      | H w => rw [← QuotientGroup.mk_pow, hV2 w, QuotientGroup.mk_one])
    (fun p => by rw [← QuotientGroup.mk_one, hsmul, map_one])
    (by
      obtain ⟨w, hw⟩ : ∃ w : V, w ∉ C := by
        by_contra hall
        push Not at hall
        exact hCtop (eq_top_iff.mpr fun w _ => hall w)
      exact ⟨QuotientGroup.mk w, fun h => hw ((QuotientGroup.eq_one_iff w).mp h)⟩)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  have hu : u ∉ C := fun h => hq1 ((QuotientGroup.eq_one_iff u).mpr h)
  refine ⟨cosetStab G C hC u, fun p hp => ⟨hPG hp, ?_⟩, ?_, ?_⟩
  ·
    have h1 := hqfix ⟨p, hp⟩
    rw [hsmul, QuotientGroup.eq] at h1
    have h2 := C.inv_mem h1
    simpa [mul_comm] using h2
  ·
    refine lt_of_le_of_ne (fun g hg => hg.1) fun heq => hu ?_
    have hall : ∀ g ∈ G, g u * u⁻¹ ∈ C := fun g hg => by
      have hgS : g ∈ cosetStab G C hC u := by rw [heq]; exact hg
      exact hgS.2
    have hv₁2 : v₁ ^ 2 = 1 := hV2 v₁
    have hv₁C : v₁ ∉ C := by
      intro hv
      apply hCtop
      rw [eq_top_iff, ← h61.span]
      refine iSup_le fun g => iSup_le fun hg => ?_
      rw [hc]
      rintro _ ⟨w, hw, rfl⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      simp only [MulEquiv.coe_toMonoidHom, map_zpow]
      exact C.zpow_mem (hC g hg _ hv) k
    have hstab : K ≤ MulAction.stabilizer (MulAut V) u := by
      refine conjClosure_le fun h hh z hz => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      rcases zpow_eq_one_or_eq' h61.sq_eq_one k with hk | hk
      · rw [hk, mul_one, mul_inv_cancel, MulAut.one_apply]
      · rw [hk]
        have hmem := hall _ (G.mul_mem (G.mul_mem hh h61.mem) (G.inv_mem hh))
        rcases apply_eq_or_of_commV hc hv₁2 (h⁻¹ u) with h1 | h1
        · simp only [MulAut.mul_apply, MulAut.inv_apply] at h1 ⊢
          rw [h1, MulEquiv.apply_symm_apply]
        · exfalso
          have e : (h * a * h⁻¹) u * u⁻¹ = h v₁ := by
            simp only [MulAut.mul_apply, MulAut.inv_apply] at h1 ⊢
            rw [h1, map_mul, MulEquiv.apply_symm_apply, mul_inv_cancel_right]
          rw [e] at hmem
          apply hv₁C
          have := hC _ (G.inv_mem hh) _ hmem
          simpa using this
    intro k hk
    exact hstab hk
  ·
    obtain ⟨x, hxG, hx3, hxu⟩ := h3 u
    exact ⟨x, ⟨hxG, by rw [hxu, mul_inv_cancel]; exact C.one_mem⟩, hx3⟩

end CFSG.Quasithin.Vol2.Ch10.SecG.C10E4
