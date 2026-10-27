module

public import CFSG.Quasithin.Background.S1567W1
public import CFSG.Quasithin.EmptyFaithful.T1531InspTop
public import CFSG.Quasithin.Background.S1567Z1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

structure Res15368NoTwo {G : Type} [Group G] (T Mc M E : Subgroup G) (s : G) : Prop where
  le_normalizer : G0_153 T Mc M E s ≤ Subgroup.normalizer (YE153 Mc M E : Set G)
  V_le_pCore : VZ T M ≤ pCoreOf 2 (G0_153 T Mc M E s)
  sylow_of_inM : ∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀
  triple : F6.IsGoldschmidtTripleIn (G0_153 T Mc M E s) (G1_153 T Mc M E s) (G2_153 T E)
  pCore_eq : pCoreOf 2 (G0_153 T Mc M E s) =
    (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)).map (G0_153 T Mc M E s).subtype

theorem Res15368.toNoTwo {G : Type} [Group G] {T Mc M E : Subgroup G} {s : G}
    (r : Res15368 T Mc M E s) : Res15368NoTwo T Mc M E s :=
  ⟨r.le_normalizer, r.V_le_pCore, r.sylow_of_inM, r.triple, r.pCore_eq⟩

theorem Res15368NoTwo.toRes15368 {G : Type} [Group G] {T Mc M E : Subgroup G} {s : G}
    (r : Res15368NoTwo T Mc M E s)
    (h2 : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G)) :
    Res15368 T Mc M E s :=
  ⟨r.le_normalizer, r.V_le_pCore, h2, r.sylow_of_inM, r.triple, r.pCore_eq⟩

section Proved

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem res15368NoTwo_of_proved (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r45 : Res15345 T Mc M V₁ V₂) (r49 : Res15349 T Mc M V₁) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) :
    Res15368NoTwo T Mc M E s := by
  have h1 := G0_le_normalizer_YE c r49 L r67 gl
  have h2 := V_le_pCoreOf_G0 c r49 L r66 r67 gl
  have h3 : ∀ M₀ : Subgroup G, InM (G0_153 T Mc M E s) M₀ → IsSylowTwoOf (TE153 T E) M₀ :=
    fun M₀ hM₀ => sylow_of_inM_153 h113 c r45 L r66 r67 gl hM₀
  have h4 := triple_153 h113 c r45 r49 L r66 r67 gl
  exact ⟨h1, h2, h3, h4, C1Pack153.pCore_eq_of h113 c r49 L r66 r67 gl h2 h4⟩

end Proved

section CaseB

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem isElemAbelian_V0_NoTwo (c : Ctx153 G T Mc M V₁ V₂ t) (r46 : Res15346 T M V₁ V₂)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s) :
    IsElemAbelian 2 (V0_153 T Mc M E s) := by
  have hV := c.hyp.elemAbelian
  have hQT := S1567.pCore_G0_le_TE c L r66 r67 gl r68.triple
  have hconj : ∀ h ∈ G0_153 T Mc M E s, ∀ z ∈ VZ T M, ∀ v ∈ VZ T M,
      v * (h * z * h⁻¹) = (h * z * h⁻¹) * v := by
    intro h hh z hz v hv
    have hle : conjSubgroup (VZ T M) h⁻¹ ≤ M := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have hw : h⁻¹ * x * h ∈ VZ T M := by simpa using hx
      have hxQ : x ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh) _).mp
          (r68.V_le_pCore hw)
        have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
        rwa [e] at h1
      exact c.hyp.T_le (hQT hxQ).1
    have hx : h * z * h⁻¹ ∈ conjSubgroup (VZ T M) h⁻¹ := by
      rw [mem_conjSubgroup_iff]
      convert hz using 1
      group
    exact Subgroup.mem_centralizer_iff.mp (r46.conj_le_centralizer h⁻¹ hle hx) v hv
  refine B2F.isElemAbelian_closure
    (S := {x | ∃ h ∈ G0_153 T Mc M E s, ∃ z ∈ VZ T M, h * z * h⁻¹ = x}) ?_ ?_
  · rintro _ ⟨h₁, hh₁, z₁, hz₁, rfl⟩ _ ⟨h₂, hh₂, z₂, hz₂, rfl⟩
    have h12 : h₂⁻¹ * h₁ ∈ G0_153 T Mc M E s :=
      (G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).inv_mem hh₂) hh₁
    have h3 := hconj _ h12 z₁ hz₁ z₂ hz₂
    calc h₁ * z₁ * h₁⁻¹ * (h₂ * z₂ * h₂⁻¹)
        = h₂ * (((h₂⁻¹ * h₁) * z₁ * (h₂⁻¹ * h₁)⁻¹) * z₂) * h₂⁻¹ := by group
      _ = h₂ * (z₂ * ((h₂⁻¹ * h₁) * z₁ * (h₂⁻¹ * h₁)⁻¹)) * h₂⁻¹ := by rw [h3]
      _ = h₂ * z₂ * h₂⁻¹ * (h₁ * z₁ * h₁⁻¹) := by group
  · rintro _ ⟨h, hh, z, hz, rfl⟩
    rw [conj_pow, hV.2 z hz]
    simp

end CaseB

section Generic

private theorem le_normalizer_map_subtype {G : Type*} [Group G] {H : Subgroup G} (K : Subgroup ↥H) [K.Normal] :
    H ≤ Subgroup.normalizer ((K.map H.subtype : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ H, ∀ y ∈ K.map H.subtype, g' * y * g'⁻¹ ∈ K.map H.subtype := by
    intro g' hg' y hy
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨⟨g', hg'⟩ * y' * ⟨g', hg'⟩⁻¹, Subgroup.Normal.conj_mem inferInstance y' hy' _, by simp⟩
  intro g hg
  exact B6.mem_normalizer_of_forall_mem (key g hg) (fun y hy => by
    simpa using key g⁻¹ (H.inv_mem hg) y hy)

theorem map_barQ_eq_autI {G : Type} [Group G] {I V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hIN : I ≤ Subgroup.normalizer (V : Set G)) (Q : Subgroup ↥I) [Q.Normal]
    (ρ : (↥I ⧸ Q) →* MulAut (IntMod V hV)) (P : ↥I → Prop)
    (hρ : ∀ g : ↥I, P g → ρ (QuotientGroup.mk g) = convHom hV I hIN g)
    {A : Subgroup G} (hAI : A ≤ I) (hA : ∀ g : ↥I, (g : G) ∈ A → P g) :
    (barQ I Q A).map ρ = autI hV A := by
  rw [autI_eq_map_convHom hV hIN hAI]
  unfold barQ
  rw [Subgroup.map_map]
  ext φ
  simp only [Subgroup.mem_map, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, (hρ x (hA x (Subgroup.mem_subgroupOf.1 hx))).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hρ x (hA x (Subgroup.mem_subgroupOf.1 hx))⟩

theorem pCoreOf_autI_thompsonJ_eq_bot_of_faithful {G : Type} [Group G] [Finite G] {I V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hIN : I ≤ Subgroup.normalizer (V : Set G)) (Q : Subgroup ↥I)
    [Q.Normal] (ρ : (↥I ⧸ Q) →* MulAut (IntMod V hV)) (hρinj : Function.Injective ρ)
    (P : ↥I → Prop) (hρ : ∀ g : ↥I, P g → ρ (QuotientGroup.mk g) = convHom hV I hIN g)
    (hJ : ∀ g : ↥I, (g : G) ∈ thompsonJ I → P g) (hD : Open.pCore 2 (↥I ⧸ Q) = ⊥) :
    pCoreOf 2 (autI hV (thompsonJ I)) = ⊥ := by
  have h1 := map_barQ_eq_autI hV hIN Q ρ P hρ (B6.thompsonJ_le I) hJ
  have hN := barQ_thompsonJ_normal I Q
  rw [← h1]
  refine le_bot_iff.mp ((pCoreOf_map_le_of_injective _ hρinj _).trans ?_)
  have := pCoreOf_le_pCore_of_normal (barQ I Q (thompsonJ I))
  rw [hD] at this
  rw [le_bot_iff.mp this, Subgroup.map_bot]

theorem b53Hyp_autI_thompsonJ_of_faithful {G : Type} [Group G] [Finite G] {I V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hIN : I ≤ Subgroup.normalizer (V : Set G)) (hVI : V ≤ I)
    (Q : Subgroup ↥I) [Q.Normal] (ρ : (↥I ⧸ Q) →* MulAut (IntMod V hV))
    (hρinj : Function.Injective ρ) (P : ↥I → Prop)
    (hρ : ∀ g : ↥I, P g → ρ (QuotientGroup.mk g) = convHom hV I hIN g)
    (hJ : ∀ g : ↥I, (g : G) ∈ thompsonJ I → P g) (hD : Open.pCore 2 (↥I ⧸ Q) = ⊥)
    (hS : SQTKGroup ↥(thompsonJ I)) : B53Hyp (autI hV (thompsonJ I)) := by
  refine ⟨pCoreOf_autI_thompsonJ_eq_bot_of_faithful hV hIN Q ρ hρinj P hρ hJ hD,
    (autI_thompsonJ_eq_ffJ hV hIN hVI).symm, ?_⟩
  set ψ : ↥(thompsonJ I) →* MulAut (IntMod V hV) :=
    (convHom hV I hIN).comp (Subgroup.inclusion (B6.thompsonJ_le I)) with hψ
  have hrange : ψ.range = autI hV (thompsonJ I) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range,
      ← autI_eq_map_convHom hV hIN (B6.thompsonJ_le I)]
  exact ⟨↥(thompsonJ I), inferInstance, inferInstance, ψ.ker, inferInstance, hS,
    ⟨(MulEquiv.subgroupCongr hrange.symm).trans (QuotientGroup.quotientKerEquivRange ψ).symm⟩⟩

end Generic

section Alpha153

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem pCore_inf_ker_alpha_le_centralizer_V (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) {q : G} (hq : q ∈ pCoreOf 2 (G0_153 T Mc M E s))
    (hqG : q ∈ G0_153 T Mc M E s)
    (h : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨q, hqG⟩ = 1) :
    q ∈ Subgroup.centralizer (VZ T M : Set G) := by
  have hqT : q ∈ TE153 T E := S1567.pCore_G0_le_TE k.c k.L k.r66 r67 gl r68.triple hq
  have hC : q ∈ Subgroup.centralizer (E : Set G) :=
    S1567.mem_centralizer_E_of_alpha_eq_one h113 k hqG hqT h
  have hF : q ∈ Subgroup.centralizer (FE153 E s : Set G) :=
    S1567.pCore_G0_le_centralizer_F k.c k.L k.r66 r67 gl r68.triple hq
  exact S1567.TE_inf_centralizer_E_F_le k.c k.L k.r66 gl ⟨⟨hqT, hC⟩, hF⟩

theorem pCore_inf_ker_alpha_le_centralizer_V0 (h113 : StageLemma14113)
    (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
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
    have hC := pCore_inf_ker_alpha_le_centralizer_V h113 k r67 gl r68 hq' hq'G hα
    have hz' : z * (h⁻¹ * y * h) = (h⁻¹ * y * h) * z := Subgroup.mem_centralizer_iff.mp hC z hz
    calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [hz']
      _ = (h * z * h⁻¹) * y := by group
  exact Subgroup.mem_centralizer_iff.mpr fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hle hx) q (Set.mem_singleton q)).symm

theorem isSylowTwoOf_TE_G0_NT (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) : IsSylowTwoOf (TE153 T E) (G0_153 T Mc M E s) := by
  have h := r68.triple.2.2.2
  rwa [G1_inf_G2 c L r66 r67 gl] at h

theorem thompsonJ_G0_le_ker_alpha (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) :
    thompsonJ (G0_153 T Mc M E s) ≤
      (S1567.alpha153 T Mc M E s r68.le_normalizer).ker.map (G0_153 T Mc M E s).subtype := by
  have hT := isSylowTwoOf_TE_G0_NT c L r66 r67 gl r68
  have h1 : thompsonJ (TE153 T E) ≤
      (S1567.alpha153 T Mc M E s r68.le_normalizer).ker.map (G0_153 T Mc M E s).subtype := by
    intro x hx
    have hxT : x ∈ TE153 T E := B6.thompsonJ_le _ hx
    have hxG : x ∈ G0_153 T Mc M E s :=
      ((le_sup_right : TE153 T E ≤ G1_153 T Mc M E s).trans le_sup_left) hxT
    have hxC : x ∈ Subgroup.centralizer (E : Set G) :=
      Subgroup.centralizer_le L.le_V (thompsonJ_TE_le_R r67 hx).2
    exact ⟨⟨x, hxG⟩, S1567.alpha153_eq_one_of_mem_centralizer_E c r66 hxG hxC, rfl⟩
  have h2 := le_normalizer_map_subtype (S1567.alpha153 T Mc M E s r68.le_normalizer).ker
  exact B6.thompsonJ_le_of_sylow_of_le hT h1 h2

theorem exists_faithful_rho (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) :
    ∃ ρ : (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) →*
        MulAut (IntMod (V0_153 T Mc M E s) (isElemAbelian_V0_NoTwo k.c k.r46 k.L k.r66 r67 gl r68)),
      Function.Injective ρ ∧ ∀ g : ↥(G0_153 T Mc M E s),
        S1567.alpha153 T Mc M E s r68.le_normalizer g = 1 →
          ρ (QuotientGroup.mk g) =
            convHom (isElemAbelian_V0_NoTwo k.c k.r46 k.L k.r66 r67 gl r68) (G0_153 T Mc M E s)
              V0_normal g := by
  classical
  set hV0 := isElemAbelian_V0_NoTwo k.c k.r46 k.L k.r66 r67 gl r68 with hV0def
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
    exact (hmemQ x).2 (inf_centralizer_V0_le_pCore k.c r67 hx)
  have hF1 : ∀ x ∈ Qb, α x = 1 → conv x = 1 := by
    intro x hx hαx
    have hC := pCore_inf_ker_alpha_le_centralizer_V0 h113 k r67 gl r68 ((hmemQ x).1 hx) x.2 hαx
    rw [hconvdef, ← MonoidHom.mem_ker, ker_convHom, Subgroup.mem_subgroupOf]
    exact ⟨x.2, hC⟩
  by_cases hA : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G)
  · have hQV : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) := fun q hq =>
      S1567.TE_inf_centralizer_E_F_le k.c k.L k.r66 gl
        ⟨⟨S1567.pCore_G0_le_TE k.c k.L k.r66 r67 gl r68.triple hq, hA hq⟩,
          S1567.pCore_G0_le_centralizer_F k.c k.L k.r66 r67 gl r68.triple hq⟩
    have hQ := pPrimeCore_G0_eq k.c r67 (r68.toRes15368 hQV)
    refine ⟨rhoOf hV0 V0_normal Qb hQ, rhoOf_injective hV0 V0_normal Qb hQ, fun g _ => ?_⟩
    exact DFunLike.congr_fun (rhoOf_comp hV0 V0_normal Qb hQ) g
  · have hcard := S1567.card_mulAut_quot_YE h113 k.c k.L k.r66
    obtain ⟨q₀, hq₀Q, hq₀E⟩ : ∃ q ∈ pCoreOf 2 (G0_153 T Mc M E s),
        q ∉ Subgroup.centralizer (E : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hA hcon
    have hq₀G : q₀ ∈ G0_153 T Mc M E s := pCoreOf_le 2 _ hq₀Q
    have hα₀ : α ⟨q₀, hq₀G⟩ ≠ 1 := fun h => hq₀E
      (S1567.mem_centralizer_E_of_alpha_eq_one h113 k hq₀G
        (S1567.pCore_G0_le_TE k.c k.L k.r66 r67 gl r68.triple hq₀Q) h)
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

end Alpha153

section NTCopies

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem XE_le_thompsonJ_NT (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) : XE153 E ≤ thompsonJ (G0_153 T Mc M E s) := by
  have hT := isSylowTwoOf_TE_G0_NT c L r66 r67 gl r68
  have hJR : thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      thompsonJ (G0_153 T Mc M E s) :=
    (thompsonJ_R_eq r67 L).le.trans (B6.thompsonJ_le_of_sylow hT)
  have hXG : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hN := B6.le_normalizer_thompsonJ (G0_153 T Mc M E s)
  calc XE153 E = ⁅XE153 E, thompsonJ (T ⊓ Subgroup.centralizer (VZ T M : Set G))⁆ := r67.XE_comm
    _ ≤ thompsonJ (G0_153 T Mc M E s) := by
      rw [Subgroup.commutator_le]
      intro x hx j hj
      rw [commutatorElement_def]
      have h1 : x * j * x⁻¹ ∈ thompsonJ (G0_153 T Mc M E s) :=
        (Subgroup.mem_normalizer_iff.mp (hN (hXG hx)) j).mp (hJR hj)
      exact (thompsonJ (G0_153 T Mc M E s)).mul_mem h1 ((thompsonJ _).inv_mem (hJR hj))

theorem pCoreOf_G0_ne_bot_NT (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368NoTwo T Mc M E s) :
    pCoreOf 2 (G0_153 T Mc M E s) ≠ ⊥ := by
  intro hbot
  have h0 : VZ T M ≤ ⊥ := hbot ▸ r68.V_le_pCore
  have h16 := c.hyp.card_VZ
  rw [le_bot_iff.mp h0, Subgroup.card_bot] at h16
  omega

omit [Finite G] in
theorem V0_le_pCore_NT (r68 : Res15368NoTwo T Mc M E s) :
    V0_153 T Mc M E s ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
  refine conjClosure_le fun h hh z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hh) z).mp (r68.V_le_pCore hz)

omit [Finite G] in
theorem V0_le_G0_NT (r68 : Res15368NoTwo T Mc M E s) : V0_153 T Mc M E s ≤ G0_153 T Mc M E s :=
  (V0_le_pCore_NT r68).trans (pCoreOf_le 2 _)

theorem sqtkGroup_G0_NT (c : Ctx153 G T Mc M V₁ V₂ t) (r68 : Res15368NoTwo T Mc M E s) :
    SQTKGroup ↥(G0_153 T Mc M E s) :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot c.hyp.qtfe.qtke (pCoreOf_G0_ne_bot_NT c r68),
    kGroup_of_pCoreOf_ne_bot c.hyp.qtfe.qtke c.hyp.qtfe.simple c.hyp.qtfe.nonabelian
      (pCoreOf_G0_ne_bot_NT c r68)⟩

theorem barQ_XE_ne_bot_NT (r67 : Res15367 T Mc M V₁ V₂ E) (r68 : Res15368NoTwo T Mc M E s)
    (hXI : XE153 E ≤ G0_153 T Mc M E s) :
    barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E) ≠ ⊥ := by
  intro hbot
  apply not_isPGroup_XE r67
  have hle : XE153 E ≤ pCoreOf 2 (G0_153 T Mc M E s) := by
    intro x hx
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) ⟨x, hXI hx⟩ ∈
        barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E) :=
      Subgroup.mem_map.mpr ⟨⟨x, hXI hx⟩, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [r68.pCore_eq]
    exact ⟨⟨x, hXI hx⟩, h1, rfl⟩
  exact (pCoreOf_isPGroup 2 _).to_le hle

theorem XE_eq_oTwoUpper_of_S3_NT (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s)
    (hS3 : Nonempty (↥(Xdot153 T Mc M E s) ≃* Equiv.Perm (Fin 3))) :
    XE153 E = oTwoUpper (thompsonJ (G0_153 T Mc M E s)) := by
  obtain ⟨e⟩ := hS3
  have hT := isSylowTwoOf_TE_G0_NT c L r66 r67 gl r68
  have hXEJ := XE_le_thompsonJ_NT c L r66 r67 gl r68
  have hXI : XE153 E ≤ G0_153 T Mc M E s :=
    (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hXEidem : XE153 E = oTwoUpper (XE153 E) := (oTwoUpper_oTwoUpper _).symm
  have hKT : IsPGroup 2 ↥(pCoreOf 2 (G0_153 T Mc M E s)) := pCoreOf_isPGroup 2 _
  have hKN : pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.normalizer (XE153 E : Set G) :=
    (pCoreOf_le_of_isSylowTwoOf hT).trans (inf_le_right.trans r67.XE_normal)
  have hXbar := barQ_XE_ne_bot_NT r67 r68 hXI
  obtain ⟨w, hwX, hwodd, hw1⟩ : ∃ w ∈ barQ (G0_153 T Mc M E s)
      (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E), Odd (orderOf w) ∧ w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hXbar
    have h1 := barQ_oTwoUpper (I := G0_153 T Mc M E s) (Q := CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))
      hXI
    rw [← hXEidem] at h1
    rw [h1]
    refine le_bot_iff.mp ((Subgroup.closure_le _).mpr fun x hx => ?_)
    simpa using hcon x hx.1 hx.2
  have hwN : w ∈ Xdot153 T Mc M E s := barQ_mono hXEJ hwX
  have hodd : ∀ u ∈ Xdot153 T Mc M E s, Odd (orderOf u) →
      u ∈ barQ (G0_153 T Mc M E s) (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) (XE153 E) := by
    intro u hu huodd
    have hsu : Equiv.Perm.sign (e ⟨u, hu⟩) = 1 :=
      perm_fin3_sign_eq_one_of_odd (by rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk])
    have hsw : Equiv.Perm.sign (e ⟨w, hwN⟩) = 1 :=
      perm_fin3_sign_eq_one_of_odd (by rwa [MulEquiv.orderOf_eq, Subgroup.orderOf_mk])
    have hw1' : e ⟨w, hwN⟩ ≠ 1 := fun h => hw1 (by
      have := e.injective (h.trans (map_one e).symm)
      simpa using congrArg Subtype.val this)
    rcases perm_fin3_eq_pow_of_sign_eq_one _ _ hsu hsw hw1' with h | h | h
    · have : u = 1 := by
        have := e.injective (h.trans (map_one e).symm)
        simpa using congrArg Subtype.val this
      rw [this]
      exact Subgroup.one_mem _
    · have : u = w := by
        have := e.injective h
        simpa using congrArg Subtype.val this
      rw [this]
      exact hwX
    · have : u = w ^ 2 := by
        have := e.injective (h.trans (map_pow e _ 2).symm)
        simpa using congrArg Subtype.val this
      rw [this]
      exact Subgroup.pow_mem _ hwX 2
  have hy : ∀ y ∈ thompsonJ (G0_153 T Mc M E s), Odd (orderOf y) → y ∈ XE153 E := by
    intro y hyJ hyodd
    have hyI : y ∈ G0_153 T Mc M E s := (B6.thompsonJ_le _) hyJ
    have huN : (QuotientGroup.mk ⟨y, hyI⟩ : ↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)) ∈ Xdot153 T Mc M E s :=
      Subgroup.mem_map.mpr ⟨⟨y, hyI⟩, hyJ, rfl⟩
    have huodd : Odd (orderOf (QuotientGroup.mk ⟨y, hyI⟩ : ↥(G0_153 T Mc M E s) ⧸
        CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
      refine Odd.of_dvd_nat (n := orderOf y) hyodd ?_
      have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
        (⟨y, hyI⟩ : ↥(G0_153 T Mc M E s))
      rwa [Subgroup.orderOf_mk] at this
    obtain ⟨x, hxX, hxu⟩ := mem_barQ.mp (hodd _ huN huodd)
    have h1 : x⁻¹ * ⟨y, hyI⟩ ∈ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) :=
      QuotientGroup.eq.mp hxu
    have h2 : (x : G)⁻¹ * y ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
      rw [r68.pCore_eq]
      exact ⟨x⁻¹ * ⟨y, hyI⟩, h1, by simp⟩
    have hysup : y ∈ XE153 E ⊔ pCoreOf 2 (G0_153 T Mc M E s) := by
      have := Subgroup.mul_mem_sup hxX h2
      simpa using this
    exact mem_of_mem_sup_of_odd hKT hKN hysup hyodd
  refine le_antisymm ?_ ?_
  · calc XE153 E = oTwoUpper (XE153 E) := hXEidem
      _ ≤ oTwoUpper (thompsonJ (G0_153 T Mc M E s)) := oTwoUpper_mono hXEJ
  · refine oTwoUpper_le_of_pow_mem fun x hx => ?_
    obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, hy _ ((thompsonJ _).pow_mem hx _) ?_⟩
    have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
    rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
    exact hm

end NTCopies

end CFSG.Quasithin
