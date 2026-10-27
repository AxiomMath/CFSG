module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenLin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Seven_finprod_orbit_mem_fixV {W : Type*} [CommGroup W] [Finite W]
    (E : Subgroup (MulAut W)) (w : W) : (∏ᶠ u ∈ MulAction.orbit E w, u) ∈ fixV E := by
  rw [mem_fixV]
  intro e he
  have hfin : (MulAction.orbit E w).Finite := Set.toFinite _
  rw [MulEquiv.map_finprod_mem e (fun u : W => u) hfin]
  refine finprod_mem_eq_of_bijOn (fun u => e u) ⟨?_, ?_, ?_⟩ (fun x _ => rfl)
  · rintro _ ⟨g, rfl⟩
    exact ⟨⟨e, he⟩ * g, by simp [mul_smul]⟩
  · intro x _ y _ hxy
    exact e.injective hxy
  · rintro _ ⟨g, rfl⟩
    refine ⟨(⟨e, he⟩⁻¹ * g) • w, MulAction.mem_orbit _ _, ?_⟩
    simp [mul_smul, Subgroup.smul_def, MulAut.smul_def]

theorem s15_Seven_finprod_orbit_ne {W : Type*} [CommGroup W] [Finite W]
    {𝓤 : Set (Subgroup W)} (h𝓤 : sSupIndep 𝓤) {A E : Subgroup (MulAut W)} (hEA : E ≤ A)
    {U₀ : Subgroup W} (hU : ∀ e ∈ A, U₀.map e.toMonoidHom ∈ 𝓤) {w : W} (hw : w ∈ U₀)
    (hw1 : w ≠ 1) (hstab : ∀ e ∈ A, U₀.map e.toMonoidHom = U₀ → e ∈ E)
    (hwfix : ∀ e ∈ E, U₀.map e.toMonoidHom = U₀ → e w = w)
    {a : MulAut W} (haA : a ∈ A) (haE : a ∉ E) :
    a (∏ᶠ u ∈ MulAction.orbit E w, u) ≠ ∏ᶠ u ∈ MulAction.orbit E w, u := by
  intro hav
  have hfin : (MulAction.orbit E w).Finite := Set.toFinite _
  have hmapeq : ∀ x y : MulAut W, U₀.map x.toMonoidHom = U₀.map y.toMonoidHom →
      U₀.map (y⁻¹ * x).toMonoidHom = U₀ := by
    intro x y hxy
    ext u
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨u', hu', rfl⟩
      have h1 : x u' ∈ U₀.map y.toMonoidHom := hxy ▸ ⟨u', hu', rfl⟩
      obtain ⟨u'', hu'', hyx⟩ := h1
      have : (y⁻¹ * x) u' = u'' := by
        rw [MulAut.mul_apply, ← hyx]; simp
      rw [this]; exact hu''
    · intro hu
      have h1 : y u ∈ U₀.map x.toMonoidHom := hxy.symm ▸ ⟨u, hu, rfl⟩
      obtain ⟨u', hu', hxu⟩ := h1
      refine ⟨u', hu', ?_⟩
      rw [MulAut.mul_apply]
      simp only [MulEquiv.coe_toMonoidHom] at hxu
      rw [hxu]; simp
  set T : Subgroup W := U₀.map a.toMonoidHom with hT
  have hTU : T ∈ 𝓤 := hU a haA
  set R : Subgroup W := sSup (𝓤 \ {T}) with hR
  have hmemE : ∀ u ∈ MulAction.orbit E w, ∃ e ∈ E, u = e w := by
    rintro _ ⟨g, rfl⟩
    exact ⟨g, g.2, by simp [Subgroup.smul_def, MulAut.smul_def]⟩
  have hclaim1 : ∀ u ∈ MulAction.orbit E w, u ∈ R := by
    intro u hu
    obtain ⟨e, he, rfl⟩ := hmemE u hu
    have hne : U₀.map e.toMonoidHom ≠ T := by
      intro heq
      have h1 := hmapeq e a heq
      have h2 : a⁻¹ * e ∈ E := hstab _ (A.mul_mem (A.inv_mem haA) (hEA he)) h1
      apply haE
      have : a = e * (a⁻¹ * e)⁻¹ := by group
      rw [this]
      exact E.mul_mem he (E.inv_mem h2)
    exact (le_sSup (show U₀.map e.toMonoidHom ∈ 𝓤 \ {T} from ⟨hU e (hEA he), hne⟩))
      ⟨w, hw, rfl⟩
  have hclaim2 : ∀ u ∈ MulAction.orbit E w, u ≠ w → a u ∈ R := by
    intro u hu huw
    obtain ⟨e, he, rfl⟩ := hmemE u hu
    have hne : U₀.map (a * e).toMonoidHom ≠ T := by
      intro heq
      have h1 := hmapeq (a * e) a heq
      have h2 : U₀.map e.toMonoidHom = U₀ := by simpa using h1
      exact huw (hwfix e he h2)
    exact (le_sSup (show U₀.map (a * e).toMonoidHom ∈ 𝓤 \ {T} from
      ⟨hU (a * e) (A.mul_mem haA (hEA he)), hne⟩)) ⟨w, hw, rfl⟩
  have hv : (∏ᶠ u ∈ MulAction.orbit E w, u) ∈ R :=
    finprod_mem_induction (· ∈ R) R.one_mem (fun _ _ => R.mul_mem) hclaim1
  have hw_mem : w ∈ MulAction.orbit E w := MulAction.mem_orbit_self w
  have hsplit : a (∏ᶠ u ∈ MulAction.orbit E w, u) =
      a w * ∏ᶠ u ∈ MulAction.orbit E w \ {w}, a u := by
    rw [MulEquiv.map_finprod_mem a (fun u : W => u) hfin]
    have := finprod_mem_mul_sdiff (f := fun u : W => a u)
      (Set.singleton_subset_iff.2 hw_mem) hfin
    rw [finprod_mem_singleton] at this
    exact this.symm
  have hrest : (∏ᶠ u ∈ MulAction.orbit E w \ {w}, a u) ∈ R :=
    finprod_mem_induction (· ∈ R) R.one_mem (fun _ _ => R.mul_mem)
      (fun u hu => hclaim2 u hu.1 hu.2)
  have haw : a w ∈ R := by
    have : a w = (∏ᶠ u ∈ MulAction.orbit E w, u) *
        (∏ᶠ u ∈ MulAction.orbit E w \ {w}, a u)⁻¹ := by
      rw [← hav, hsplit]; group
    rw [this]
    exact R.mul_mem hv (R.inv_mem hrest)
  have hawT : a w ∈ T := ⟨w, hw, rfl⟩
  have h1 : a w = 1 := by
    have hdis : Disjoint T R := h𝓤 hTU
    exact (Subgroup.disjoint_def.1 hdis) hawT haw
  apply hw1
  apply a.injective
  rw [h1, map_one]

theorem s15_Seven_barSub_ne_bot_of_ne_one {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) {w : vStar D.M V₀ V hV L}
    (hw : w ∈ wStar D.M V₀ V hV L) (hw1 : w ≠ 1) : barSub V₀ V hV L ≠ ⊥ := by
  intro hL
  apply hw1
  have hW : wSub V₀ V hV L = V₀ := s15_Infra_wSub_eq_of_barSub_eq_bot h hV hL
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (wSub V₀ V hV L) w).1 hw
  rw [hW] at hx
  rw [← map_one (mkTil (v1Sub D.M V₀ V hV L) V hV), mkTil_eq_iff]
  show x.val * (1 : G)⁻¹ ∈ _
  simpa using s15_Infra_le_v1Sub D.M V₀ V hV L hx

theorem s15_Seven_preBarSub_mono {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {X Y : Subgroup (MulAut (Vtil V₀ V hV))} (h : X ≤ Y) :
    preBarSub M V₀ V hV X ≤ preBarSub M V₀ V hV Y := by
  intro g hg
  obtain ⟨hgM, hs, hX⟩ := (mem_preBarSub M V₀ V hV X).1 hg
  exact (mem_preBarSub M V₀ V hV Y).2 ⟨hgM, hs, h hX⟩

theorem fifteen_seven_prime (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    {A B E : Subgroup (MulAut (vStar D.M V₀ V hV L))}
    (hA : A ≤ Mbar D.M (v1Sub D.M V₀ V hV L) V hV)
    (hB : B = A ⊓ stabSub (wStar D.M V₀ V hV L)) (hBE : B ≤ E) (hEA : E < A)
    {w : vStar D.M V₀ V hV L} (hw : w ∈ wStar D.M V₀ V hV L) (hw1 : w ≠ 1)
    (hwB : w ∈ fixV B) :
    (∏ᶠ u ∈ MulAction.orbit E w, u) ∈ fixV E ∧ (∏ᶠ u ∈ MulAction.orbit E w, u) ∉ fixV A := by
  refine ⟨s15_Seven_finprod_orbit_mem_fixV E w, ?_⟩
  intro hvA
  have hL : barSub V₀ V hV L ≠ ⊥ := s15_Seven_barSub_ne_bot_of_ne_one h.hyp125 hV hw hw1
  have hind := sSupIndep_wStarConj D h hV hL
  obtain ⟨a, haA, haE⟩ := (SetLike.lt_iff_le_and_exists.1 hEA).2
  have hstabB : ∀ e ∈ A, (wStar D.M V₀ V hV L).map e.toMonoidHom = wStar D.M V₀ V hV L →
      e ∈ B := by
    intro e he hmap
    rw [hB]
    exact ⟨he, (s15_Lin_map_eq_iff_mem_stabSub _ e).1 hmap⟩
  exact s15_Seven_finprod_orbit_ne hind hEA.le
    (fun e he => s15_Infra_map_wStar_mem_wStarConj h.hyp125 hV (hA he)) hw hw1
    (fun e he hmap => hBE (hstabB e he hmap))
    (fun e he hmap => (mem_fixV.1 hwB) e (hstabB e (hEA.le he) hmap)) haA haE
    (mem_fixV.1 hvA a haA)

theorem fifteen_seven (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    {A : Subgroup (MulAut (vStar D.M V₀ V hV L))}
    (hA : A ∈ calABar 2 D.M (v1Sub D.M V₀ V hV L) V hV) :
    preBarSub D.M (v1Sub D.M V₀ V hV L) V hV A ≤ normalizer (wSub V₀ V hV L : Set G) := by
  obtain ⟨hAM, hA0, hAe, hAfix⟩ := hA
  have hnb : preBarSub D.M (v1Sub D.M V₀ V hV L) V hV (stabSub (wStar D.M V₀ V hV L)) ≤
      normalizer (wSub V₀ V hV L : Set G) := by
    rw [preBarSub_stabSub_wStar D h hV, ← inf_normalizer_wSub_eq_nBar D h hV]
    exact inf_le_right
  by_cases hBA : A ⊓ stabSub (wStar D.M V₀ V hV L) = A
  · exact (s15_Seven_preBarSub_mono hV (hBA ▸ inf_le_right)).trans hnb
  · exfalso
    have hBlt : A ⊓ stabSub (wStar D.M V₀ V hV L) < A := lt_of_le_of_ne inf_le_left hBA
    obtain ⟨E, hBE, hEA, hEq⟩ := s15_Lin_exists_hyperplane hAe hBlt
    have hW0 : wStar D.M V₀ V hV L ≠ ⊥ := by
      intro hbot
      apply hBA
      refine le_antisymm inf_le_left fun e he => Subgroup.mem_inf.2 ⟨he, ?_⟩
      exact (s15_Lin_map_eq_iff_mem_stabSub _ e).1 (by rw [hbot, Subgroup.map_bot])
    have hP : IsPGroup 2 (A ⊓ stabSub (wStar D.M V₀ V hV L) : Subgroup _) :=
      (IsElemAbelian2.isPGroup hAe).to_le inf_le_left
    have hinv : ∀ x ∈ A ⊓ stabSub (wStar D.M V₀ V hV L), ∀ u ∈ wStar D.M V₀ V hV L,
        x u ∈ wStar D.M V₀ V hV L :=
      fun x hx u hu => ((Subgroup.mem_inf.1 hx).2 u).2 hu
    obtain ⟨w, hw, hw1, hwB⟩ := s15_Lin_exists_ne_one_mem_fixV hP
      (s15_Infra_vtil_sq_eq_one _ V hV) hW0 hinv
    have key := fifteen_seven_prime D h hV hAM rfl hBE hEA hw hw1 hwB
    have hfix : fixV E = fixV A := hAfix E hEA.le (by rw [hEq]; exact Nat.one_lt_two)
    exact key.2 (hfix ▸ key.1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
