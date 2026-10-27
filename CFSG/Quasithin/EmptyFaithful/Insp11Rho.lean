module

public import CFSG.Quasithin.EmptyFaithful.Insp10Alpha
public import CFSG.Quasithin.Background.S1567W2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

namespace Insp11

section Alpha153NR

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem pCore_inf_ker_alpha_le_centralizer_V_NR (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) {q : G} (hq : q ∈ pCoreOf 2 (G0_153 T Mc M E s))
    (hqG : q ∈ G0_153 T Mc M E s)
    (h : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨q, hqG⟩ = 1) :
    q ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hqT : q ∈ TE153 T E := S1567.pCore_G0_le_TE c L r66 r67 gl r68.triple hq
  have hC : q ∈ Subgroup.centralizer (E : Set G) :=
    Insp10.mem_centralizer_E_of_alpha_eq_one_NR h113 c L r66 r67 hqG hqT h
  have hF : q ∈ Subgroup.centralizer (FE153 E s : Set G) :=
    S1567.pCore_G0_le_centralizer_F c L r66 r67 gl r68.triple hq
  exact S1567.TE_inf_centralizer_E_F_le c L r66 gl ⟨⟨hqT, hC⟩, hF⟩

theorem pCore_inf_ker_alpha_le_centralizer_V0_NR (h113 : StageLemma14113)
    (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) {q : G} (hq : q ∈ pCoreOf 2 (G0_153 T Mc M E s))
    (hqG : q ∈ G0_153 T Mc M E s)
    (hα1 : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨q, hqG⟩ = 1) :
    q ∈ Subgroup.centralizer (V0_153 T Mc M E s : Set G) := by
  have hle : V0_153 T Mc M E s ≤ Subgroup.centralizer ({q} : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hh' : h⁻¹ ∈ G0_153 T Mc M E s := (G0_153 T Mc M E s).inv_mem hh
    have hq' : h⁻¹ * y * h ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh') y).mp hq
      simpa using this
    have hq'G : h⁻¹ * y * h ∈ G0_153 T Mc M E s :=
      (G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).mul_mem hh' hqG) hh
    have hα : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨h⁻¹ * y * h, hq'G⟩ = 1 := by
      have e : (⟨h⁻¹ * y * h, hq'G⟩ : ↥(G0_153 T Mc M E s)) =
          ⟨h⁻¹, hh'⟩ * ⟨y, hqG⟩ * ⟨h, hh⟩ := rfl
      have e1 : (⟨h⁻¹, hh'⟩ : ↥(G0_153 T Mc M E s)) * ⟨h, hh⟩ = 1 := by
        ext
        simp
      rw [e, map_mul, map_mul, hα1, mul_one, ← map_mul, e1, map_one]
    have hC := pCore_inf_ker_alpha_le_centralizer_V_NR h113 c L r66 r67 gl r68 hq' hq'G hα
    have hz' : z * (h⁻¹ * y * h) = (h⁻¹ * y * h) * z := Subgroup.mem_centralizer_iff.mp hC z hz
    calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [hz']
      _ = (h * z * h⁻¹) * y := by group
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hle hx) q (Set.mem_singleton q)).symm

theorem exists_faithful_rho_NR (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) :
    ∃ ρ : (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) →*
        MulAut (IntMod (V0_153 T Mc M E s) (isElemAbelian_V0_NoTwo c r46 L r66 r67 gl r68)),
      Function.Injective ρ ∧ ∀ g : ↥(G0_153 T Mc M E s),
        S1567.alpha153 T Mc M E s r68.le_normalizer g = 1 →
          ρ (QuotientGroup.mk g) =
            convHom (isElemAbelian_V0_NoTwo c r46 L r66 r67 gl r68) (G0_153 T Mc M E s)
              V0_normal g := by
  classical
  set hV0 := isElemAbelian_V0_NoTwo c r46 L r66 r67 gl r68 with hV0def
  set Qb := CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) with hQb
  set α := S1567.alpha153 T Mc M E s r68.le_normalizer with hαdef
  set conv := convHom hV0 (G0_153 T Mc M E s) V0_normal with hconvdef
  have hmemQ : ∀ x : ↥(G0_153 T Mc M E s), x ∈ Qb ↔ (x : G) ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
    intro x
    rw [r68.pCore_eq]
    exact (Subgroup.mem_map_iff_mem (G0_153 T Mc M E s).subtype_injective).symm
  have hker : conv.ker ≤ Qb := by
    intro x hx
    rw [hconvdef, ker_convHom, Subgroup.mem_subgroupOf] at hx
    exact (hmemQ x).2 (inf_centralizer_V0_le_pCore c r67 hx)
  have hF1 : ∀ x ∈ Qb, α x = 1 → conv x = 1 := by
    intro x hx hαx
    have hC := pCore_inf_ker_alpha_le_centralizer_V0_NR h113 c L r66 r67 gl r68 ((hmemQ x).1 hx) x.2 hαx
    rw [hconvdef, ← MonoidHom.mem_ker, ker_convHom, Subgroup.mem_subgroupOf]
    exact ⟨x.2, hC⟩
  by_cases hA : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G)
  · have hQV : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) := fun q hq =>
      S1567.TE_inf_centralizer_E_F_le c L r66 gl
        ⟨⟨S1567.pCore_G0_le_TE c L r66 r67 gl r68.triple hq, hA hq⟩,
          S1567.pCore_G0_le_centralizer_F c L r66 r67 gl r68.triple hq⟩
    have hQ := pPrimeCore_G0_eq c r67 (r68.toRes15368 hQV)
    refine ⟨rhoOf hV0 V0_normal Qb hQ, rhoOf_injective hV0 V0_normal Qb hQ, fun g _ => ?_⟩
    exact DFunLike.congr_fun (rhoOf_comp hV0 V0_normal Qb hQ) g
  · have hcard := S1567.card_mulAut_quot_YE h113 c L r66
    obtain ⟨q₀, hq₀Q, hq₀E⟩ : ∃ q ∈ pCoreOf 2 (G0_153 T Mc M E s),
        q ∉ Subgroup.centralizer (E : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hA hcon
    have hq₀G : q₀ ∈ G0_153 T Mc M E s := pCoreOf_le 2 _ hq₀Q
    have hα₀ : α ⟨q₀, hq₀G⟩ ≠ 1 := fun h => hq₀E
      (Insp10.mem_centralizer_E_of_alpha_eq_one_NR h113 c L r66 r67 hq₀G
        (S1567.pCore_G0_le_TE c L r66 r67 gl r68.triple hq₀Q) h)
    have hq₀Qb : (⟨q₀, hq₀G⟩ : ↥(G0_153 T Mc M E s)) ∈ Qb := (hmemQ _).2 hq₀Q
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : MulAut
      (↥(YE153 Mc M E) ⧸ CFSG.Open.pCore 2 ↥(YE153 Mc M E)))).1 hcard
    let f : ↥α.ker →* (↥(G0_153 T Mc M E s) ⧸ Qb) := (QuotientGroup.mk' Qb).comp α.ker.subtype
    let g' : ↥α.ker →* MulAut (IntMod (V0_153 T Mc M E s) hV0) := conv.comp α.ker.subtype
    have hsurj : Function.Surjective f := by
      intro u
      induction u using QuotientGroup.induction_on with
      | H g =>
        by_cases hg : α g = 1
        · exact ⟨⟨g, hg⟩, rfl⟩
        · have heq : α g = α ⟨q₀, hq₀G⟩ := (huniq _ hg).trans (huniq _ hα₀).symm
          refine ⟨⟨g * ⟨q₀, hq₀G⟩⁻¹, ?_⟩, ?_⟩
          · rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
          · have hmk : QuotientGroup.mk' Qb (⟨q₀, hq₀G⟩ : ↥(G0_153 T Mc M E s)) = 1 :=
              (QuotientGroup.eq_one_iff _).2 hq₀Qb
            show QuotientGroup.mk' Qb (g * ⟨q₀, hq₀G⟩⁻¹) = QuotientGroup.mk g
            rw [map_mul, map_inv, hmk, inv_one, mul_one]
            rfl
    have hfg : f.ker ≤ g'.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      exact hF1 x ((QuotientGroup.eq_one_iff _).1 hx) x.2
    have hcomp : ∀ x : ↥α.ker,
        (MonoidHom.liftOfSurjective f hsurj ⟨g', hfg⟩) (f x) = conv (x : ↥(G0_153 T Mc M E s)) :=
      fun x => MonoidHom.liftOfRightInverse_comp_apply f _ _ ⟨g', hfg⟩ x
    refine ⟨MonoidHom.liftOfSurjective f hsurj ⟨g', hfg⟩, ?_, fun g hg => hcomp ⟨g, hg⟩⟩
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨x, rfl⟩ := hsurj u
    rw [hcomp] at hu
    exact (QuotientGroup.eq_one_iff _).2 (hker hu)


end Alpha153NR

end Insp11

end CFSG.Quasithin
