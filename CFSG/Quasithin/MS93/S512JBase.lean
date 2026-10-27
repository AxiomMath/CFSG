module

public import CFSG.Quasithin.MS93.S512RS51
public import CFSG.Quasithin.MS93.S512NOff

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512J

section Sp4

variable {F : Type} [Field F]

theorem inf_eq_bot_of_sup_eq_top {l l' : Submodule F (MSP.V4 F)} {E E' : Subgroup (MSP.Sp4 F)}
    (hE : E ≤ MSP.qLine l) (hE' : E' ≤ MSP.qLine l') (htop : E ⊔ E' = ⊤) : l ⊓ l' = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  by_contra hv0
  obtain ⟨y, hy⟩ := MSP.exists_form_eq_one hv0
  have hle : E ⊔ E' ≤ MSP.fixer (F ∙ v) :=
    sup_le (hE.trans (MSP.fixer_antitone ((Submodule.span_singleton_le_iff_mem _ _).2 hv.1)))
      (hE'.trans (MSP.fixer_antitone ((Submodule.span_singleton_le_iff_mem _ _).2 hv.2)))
  rw [htop] at hle
  have hfix := hle (Subgroup.mem_top (MSP.transv y 1)) v (Submodule.mem_span_singleton_self v)
  rw [MSP.transv_mulVec, one_mul, MSP.form_swap, hy, neg_smul, one_smul, add_neg_eq_iff_eq_add,
    left_eq_add] at hfix
  rw [hfix, map_zero] at hy
  exact zero_ne_one hy

end Sp4

section Grp

variable {Γ : Type*} [Group Γ]

theorem le_normalizer_sup_of_commutator_le {Y X E : Subgroup Γ}
    (hEX : E ≤ Subgroup.normalizer (X : Set Γ)) (hYE : ⁅Y, E⁆ ≤ X) :
    E ≤ Subgroup.normalizer ((Y ⊔ X : Subgroup Γ) : Set Γ) := by
  have key : ∀ e ∈ E, (Y ⊔ X).map (MulAut.conj e).toMonoidHom ≤ Y ⊔ X := by
    intro e he
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      have h1 : ⁅y, e⁆ ∈ X := hYE (Subgroup.commutator_mem_commutator hy he)
      have e1 : (MulAut.conj e).toMonoidHom y = ⁅y, e⁆⁻¹ * y := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e1]
      exact mul_mem (Subgroup.mem_sup_right (inv_mem h1)) (Subgroup.mem_sup_left hy)
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.1 (hEX he) x).1 hx)
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key e he ⟨x, hx, rfl⟩, fun hx => ?_⟩
  have h1 := key e⁻¹ (inv_mem he) ⟨_, hx, rfl⟩
  have e1 : (MulAut.conj e⁻¹).toMonoidHom (e * x * e⁻¹) = x := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rwa [e1] at h1

end Grp

section S33

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_zHat_le_xm (h32 : S32) (hX2 : S33.S33X52) (h : PUHyp M T L)
    (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') {Y : Subgroup (puAmalgam h.le).Universal}
    (hYT : Y ≤ Qv _ (geo _ α' (baseA (puAmalgam h.le)) 1))
    (hYR : Y ≤ Subgroup.centralizer (critR _ (baseA (puAmalgam h.le)) α' : Set _))
    (hYX : Y ≤ Subgroup.centralizer (XM _ (baseA (puAmalgam h.le)) : Set _))
    (hAY : ⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆ ≤ XM _ (baseA (puAmalgam h.le)))
    (hAYY : ⁅⁅critA _ (baseA (puAmalgam h.le)) α', Y⁆, Y⁆ = ⊥)
    (hno : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
      Xq M = Uq M T L ⊔ Zq M L →
      Nat.card ↥⁅Y, critA _ (baseA (puAmalgam h.le)) α'⁆ = 2 ^ k →
      ⁅Y, critA _ (baseA (puAmalgam h.le)) α'⁆ ≤ critR _ (baseA (puAmalgam h.le)) α' ⊔
        stabCenter _ α' → False) :
    ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤ XM _ (baseA (puAmalgam h.le)) := by
  by_contra hne
  obtain ⟨-, -, -, hRX, hXX, -⟩ := S5B.crit_facts h hc
  have hY3 : ¬ ⁅ZM (puAmalgam h.le) α', Y⁆ ≤
      ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ ⊔
        ⁅critA (puAmalgam h.le) (baseA _) α', Y⁆ := by
    intro hle
    apply hne
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans (hle.trans (sup_le hXX hAY))
  have hYZ : ¬ ⁅Y, S5.zHat _ (baseA (puAmalgam h.le)) α'⁆ ≤
      critR _ (baseA (puAmalgam h.le)) α' := fun hle => hne (hle.trans hRX)
  obtain ⟨hrel, hXU, hD⟩ := S5B.s33ii2_of' hX2 h hd (h32 G M T L h).2.1 hc hYT hYR hYX hY3 hYZ
  obtain ⟨hcard, hle⟩ := hD hAYY
  exact hno hrel hXU hcard hle

end S33

section Axis

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_mem_conj_eq_M (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup G} (hEM : E ≤ M) (hcard : Nat.card ((E.subgroupOf M).map a) = 2 ^ k)
    (hu : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) = 2 ^ k)
    {m : G} (hm : m ∈ M)
    (hmc : ∀ u ∈ Uq M T L ⊓ Subgroup.centralizer (E : Set G), m * u * m⁻¹ = u) :
    ∃ e ∈ E, ∀ u ∈ Uq M T L, m * u * m⁻¹ = e * u * e⁻¹ := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  obtain ⟨p, hp, -, hfix, hxP⟩ := S510.exists_point_of_relIndex h hd hEM hu
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hEX : (E.subgroupOf M).map a = MSP.xPoint p :=
    Subgroup.eq_of_le_of_card_ge hxP (by rw [MSP.card_xPoint hp, hcard, hFq])
  have hma : a ⟨m, hm⟩ ∈ MSP.xPoint p := by
    intro w hw
    rw [← hfix] at hw
    obtain ⟨u, rfl⟩ := c.exists_vec_eq w
    have huE := (S5B.mem_centralizer_iff_vec h hlift c hEM u).2 hw
    have h1 := hmc u ⟨u.2, huE⟩
    have hmu : m * (u : G) * m⁻¹ ∈ Uq M T L := by rw [h1]; exact u.2
    have h2 := c.vec_conj ⟨m, hm⟩ u hmu
    have h3 : (⟨m * (u : G) * m⁻¹, hmu⟩ : ↥(Uq M T L)) = u := Subtype.ext h1
    rw [h3] at h2
    exact h2.symm
  rw [← hEX] at hma
  obtain ⟨e, he, hea⟩ := hma
  refine ⟨e, Subgroup.mem_subgroupOf.1 he, fun u hu => ?_⟩
  have hs : a (e⁻¹ * ⟨m, hm⟩) = 1 := by rw [map_mul, map_inv, hea, inv_mul_cancel]
  have hsM : (e : G)⁻¹ * m ∈ M := mul_mem (inv_mem e.2) hm
  have hsu : (e : G)⁻¹ * m * u * ((e : G)⁻¹ * m)⁻¹ ∈ Uq M T L :=
    (Subgroup.mem_normalizer_iff.1 (hUn hsM) u).1 hu
  have hker : (e : G)⁻¹ * m * u * ((e : G)⁻¹ * m)⁻¹ * u⁻¹ ∈
      Subgroup.centralizer (L : Set G) := by
    have h1 := c.vec_commutator (e⁻¹ * ⟨m, hm⟩) ⟨u, hu⟩ hsu
    rw [hs, MSP.mat_one, Matrix.one_mulVec, sub_self, c.vec_eq_zero_iff] at h1
    exact h1.2
  have h2 := hlift _ hsM u hu hker
  calc m * u * m⁻¹ = e * ((e : G)⁻¹ * m * u * ((e : G)⁻¹ * m)⁻¹) * (e : G)⁻¹ := by group
    _ = e * u * e⁻¹ := by rw [h2]; rfl

theorem exists_mem_conj_eq_baseA (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E : Subgroup (puAmalgam h.le).Universal} (hEs : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hE2 : IsPGroup 2 E) (hc : (Qv _ (baseA (puAmalgam h.le))).relIndex E = 2 ^ k)
    (hu : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) = 2 ^ k)
    {t : (puAmalgam h.le).Universal} (ht : t ∈ stab _ (baseA (puAmalgam h.le)))
    (htc : ∀ u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal), t * u * t⁻¹ = u) :
    ∃ e ∈ E, ∀ u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)), t * u * t⁻¹ = e * u * e⁻¹ := by
  have hcard := S5.card_vIm h hd hEs hE2
  rw [puAmalgam.stab_baseA] at hEs ht
  obtain ⟨E₀, -, hE₀M, rfl⟩ := S5B.exists_eq_imM h.le hEs
  rw [imM] at ht
  obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.1 ht
  rw [S5B.vIm_imM h.le, hc] at hcard
  rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₀M] at hu
  have hmc : ∀ u ∈ Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G), (m : G) * u * (m : G)⁻¹ = u := by
    intro u hu'
    have huM : u ∈ M := Uq_le h.L_le hu'.1
    have h1 := htc ((puAmalgam h.le).ofA ⟨u, huM⟩) (by
      rw [S5B.uSub_baseA h, ← imM_inf_centralizer h.le _ hE₀M]
      exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.2 hu', rfl⟩)
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
  obtain ⟨e, he, hconj⟩ := exists_mem_conj_eq_M h hd hE₀M hcard hu m.2 hmc
  refine ⟨(puAmalgam h.le).ofA ⟨e, hE₀M he⟩, ⟨⟨e, hE₀M he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩,
    fun u hu' => ?_⟩
  rw [S5B.uSub_baseA h] at hu'
  obtain ⟨u₀, hu₀, rfl⟩ := hu'
  have h1 := hconj u₀ (Subgroup.mem_subgroupOf.1 hu₀)
  rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext h1

theorem exists_mem_conj_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {E : Subgroup (puAmalgam h.le).Universal} (hEs : E ≤ stab _ δ)
    (hE2 : IsPGroup 2 E) (hc : (Qv _ δ).relIndex E = 2 ^ k)
    (hu : (Subgroup.centralizer (E : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L δ) = 2 ^ k)
    {t : (puAmalgam h.le).Universal} (ht : t ∈ stab _ δ)
    (htc : ∀ u ∈ S5.uSub h.le L δ ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal),
      t * u * t⁻¹ = u) :
    ∃ e ∈ E, ∀ u ∈ S5.uSub h.le L δ, t * u * t⁻¹ = e * u * e⁻¹ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  set E' := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
  have hEE : E = E'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv E g).symm
  have hU := S5B.uSub_smul h.le hLn (L := L) g (baseA (puAmalgam h.le))
  rw [hEE, stab_smul, map_conj_le_map_conj_iff] at hEs
  rw [hEE, qv_smul, Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hc
  rw [hEE, hU, PU.centralizer_map_mulEquiv,
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hu
  have hE'2 : IsPGroup 2 E' := hE2.map _
  have ht' : g⁻¹ * t * g ∈ stab _ (baseA (puAmalgam h.le)) := by
    rw [stab_smul, PU.mem_map_conj] at ht
    exact ht
  have htc' : ∀ u ∈ S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
      Subgroup.centralizer (E' : Set (puAmalgam h.le).Universal),
      g⁻¹ * t * g * u * (g⁻¹ * t * g)⁻¹ = u := by
    intro u hu'
    have h1 := htc (g * u * g⁻¹) (by
      rw [hU, hEE, PU.centralizer_map_mulEquiv, ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
        PU.mem_map_conj]
      have e : g⁻¹ * (g * u * g⁻¹) * g = u := by group
      rw [e]
      exact hu')
    calc g⁻¹ * t * g * u * (g⁻¹ * t * g)⁻¹ = g⁻¹ * (t * (g * u * g⁻¹) * t⁻¹) * g := by group
      _ = u := by rw [h1]; group
  obtain ⟨e', he', hconj⟩ := exists_mem_conj_eq_baseA h hd hEs hE'2 hc hu ht' htc'
  refine ⟨g * e' * g⁻¹, ?_, fun u hu' => ?_⟩
  · rw [hEE, PU.mem_map_conj]
    have e : g⁻¹ * (g * e' * g⁻¹) * g = e' := by group
    rw [e]
    exact he'
  · rw [hU, PU.mem_map_conj] at hu'
    have h1 := hconj _ hu'
    calc t * u * t⁻¹ = g * (g⁻¹ * t * g * (g⁻¹ * u * g) * (g⁻¹ * t * g)⁻¹) * g⁻¹ := by group
      _ = g * e' * g⁻¹ * u * (g * e' * g⁻¹)⁻¹ := by rw [h1]; group

end Axis

section Offender

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

open S512N in
theorem relIndex_qv_le_of_offender (h14 : MS14AS)
    (hSQ : SQTKQuot) (hT : S32.TypeFacts) {h : PUHyp M T L} (hd : S5.IsSp4Data M T L k F a)
    {V : Subgroup (puAmalgam h.le).Universal} (hV : SecHyp h V)
    {E : Subgroup (puAmalgam h.le).Universal} (hEs : E ≤ stab _ (baseA (puAmalgam h.le)))
    (hE2 : IsPGroup 2 E)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y * x⁻¹ * y⁻¹ ∈ Qv _ (baseA (puAmalgam h.le)))
    (hEsq : ∀ x ∈ E, x ^ 2 ∈ Qv _ (baseA (puAmalgam h.le)))
    (hEW : (S36E.fixSec V (V ⊓ S5.bSub h.le L (baseA _)) E
      (hV.le_stab.trans hV.le_normalizer_inf)).relIndex V ≤ 2 ^ k) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex E ≤ 2 ^ k := by
  by_contra hlt
  push Not at hlt
  obtain ⟨S, _, p, ρ, hs⟩ := hV.exists_secMod
  have := hV.finite_S hs
  obtain ⟨S₀, hne, hS₀, hmin⟩ := exists_minimal_invariant ρ (hV.nontrivial_S hs)
  have hρ := hV.isIrrRep_restrict hs hS₀ hne hmin
  set ρM := (restrict ρ hS₀).comp (eM h.le) with hρM
  set A := (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map (restrict ρ hS₀) with hAdef
  have hAX : A ≤ ρM.range := by
    rintro _ ⟨g, -, rfl⟩
    obtain ⟨m, rfl⟩ := eM_surjective h.le g
    exact ⟨m, rfl⟩
  have hQ1 : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) →
      restrict ρ hS₀ g = 1 := fun g hg => hV.restrict_eq_one_of_mem_qv hs hS₀ hne hmin g hg
  have hA : IsElemAbelian2 A := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      have hq := hQ1 (g * g' * g⁻¹ * g'⁻¹) (hEc _ (Subgroup.mem_subgroupOf.1 hg) _
        (Subgroup.mem_subgroupOf.1 hg'))
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hq
      have e1 : restrict ρ hS₀ g * restrict ρ hS₀ g' =
          (restrict ρ hS₀ g * restrict ρ hS₀ g' * (restrict ρ hS₀ g)⁻¹ *
            (restrict ρ hS₀ g')⁻¹) * (restrict ρ hS₀ g' * restrict ρ hS₀ g) := by group
      rw [e1, hq, one_mul]
    · rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow]
      exact hQ1 _ (by simpa using hEsq _ (Subgroup.mem_subgroupOf.1 hg))
  have hcA : Nat.card A = (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
    have hker : (restrict ρ hS₀).ker ⊓ E.subgroupOf (stab (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA (puAmalgam h.le))).subgroupOf (stab (puAmalgam h.le) (baseA _)) ⊓
          E.subgroupOf (stab (puAmalgam h.le) (baseA _)) := by
      ext g
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨hg, hgE⟩
        obtain ⟨n, hn⟩ := hE2 ⟨g, hgE⟩
        refine ⟨hV.mem_qv_of_restrict_eq_one hs hS₀ hne hmin hg ⟨n, ?_⟩, hgE⟩
        simpa using congrArg Subtype.val hn
      · rintro ⟨hgQ, hgE⟩
        exact ⟨hQ1 g hgQ, hgE⟩
    rw [hAdef, ← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_right, hker,
      Subgroup.inf_relIndex_right, Subgroup.relIndex_subgroupOf hEs]
  have hidx : (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).index ≤ 2 ^ k := by
    rw [hs.index_fixV hEs (hV.le_stab.trans hV.le_normalizer_inf)]
    exact hEW
  have hAf := hV.card_le_fixV_restrict hs hS₀ hidx
  obtain ⟨F', iF, fF, φ, θ, hcard, -, hθ⟩ := exists_coord h14 hSQ hT h hd hρ hAX hA
    (by rw [hcA]; exact hlt.le) hAf (fun hk2 => hV.range_le_imL hs hd hk2 hS₀ hne hmin)
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcA
    have : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
    omega
  have hF' : Nat.card F' = 2 ^ k := by rw [Nat.card_eq_fintype_card, hcard]
  have hle := card_le_of_coord hθ hAX hA1 (by rw [hF']; exact hAf)
  rw [hcA, hF'] at hle
  omega

end Offender

section Line

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem jOff_eq_qv_of_le_qLine (h54 : S54) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l)) :
    S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) = Qv _ (baseB (puAmalgam h.le)) := by
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  have hF : 1 < Nat.card F := by
    rw [hFq]
    exact Nat.one_lt_two_pow (by have := hd.1; omega)
  have hTl' : (T.subgroupOf M).map a ≤ MSP.qLine l :=
    S512T.imSp_le_of_imM_le_vPre h.le (by rw [← puAmalgam.qv_baseB]; exact hTl)
  have hJT : S5.jOffM M T L (2 ^ k) ≤ T := iSup₂_le fun E hE => hE.1.1
  have hJM : S5.jOffM M T L (2 ^ k) ≤ M := hJT.trans h.le
  rcases h54 G M T L h hmin hb k F _ _ a hd with ⟨-, -, hJ2⟩ | ⟨-, -, p, hp, hTq⟩
  · rw [S5B.qv_baseA_eq h, S5.jOff_baseA h, S5B.relIndex_imM h.le hJM] at hJ2
    have hJ2' : (2 ^ k) ^ 2 ≤ Nat.card (((S5.jOffM M T L (2 ^ k)).subgroupOf M).map a) :=
      le_of_le_of_eq hJ2 (S5.IsSp4Data.card_imSp hd h hJT).symm
    rw [S5.jOff_baseA h, S512T.jOffM_eq_of_le_qLine_M h hd hl hTl' hJ2', puAmalgam.qv_baseB]
  · exfalso
    rw [puAmalgam.qv_baseB, S5.vIm_imM h] at hTq
    exact S512T.not_qPoint_le_qLine hF hp hl ((le_of_eq hTq.symm).trans hTl')

theorem sq_le_card_vIm_sup (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {E₁ E₂ : Subgroup (puAmalgam h.le).Universal}
    (hE₁ : E₁ ≤ Qv _ (baseB (puAmalgam h.le))) (hE₂ : E₂ ≤ Qv _ (baseB (puAmalgam h.le)))
    (hc₁ : (Qv _ (baseA (puAmalgam h.le))).relIndex E₁ = 2 ^ k)
    (hu₁ : (Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) = 2 ^ k)
    (hc₂ : (Qv _ (baseA (puAmalgam h.le))).relIndex E₂ = 2 ^ k)
    (hu₂ : (Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)).relIndex
      (S5.uSub h.le L (baseA (puAmalgam h.le))) = 2 ^ k)
    (hne : S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E₁ : Set (puAmalgam h.le).Universal) ≠
      S5.uSub h.le L (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (E₂ : Set (puAmalgam h.le).Universal)) :
    (2 ^ k) ^ 2 ≤ Nat.card (S5.vIm h.le a (E₁ ⊔ E₂)) := by
  have hFq : Nat.card F = 2 ^ k := by rw [Nat.card_eq_fintype_card, hd.2.1]
  rw [puAmalgam.qv_baseB] at hE₁ hE₂
  obtain ⟨E₁', hE₁T, hE₁M, rfl⟩ := S5B.exists_eq_imM h.le hE₁
  obtain ⟨E₂', hE₂T, hE₂M, rfl⟩ := S5B.exists_eq_imM h.le hE₂
  rw [S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hE₁M] at hc₁
  rw [S5B.qv_baseA_eq h, S5B.relIndex_imM h.le hE₂M] at hc₂
  rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₁M] at hu₁
  rw [S5B.uSub_baseA h, S5B.relIndex_centralizer_imM h.le (Uq_le h.L_le) hE₂M] at hu₂
  rw [S5B.uSub_baseA h, ← imM_inf_centralizer h.le _ hE₁M,
    ← imM_inf_centralizer h.le _ hE₂M] at hne
  have hne' : Uq M T L ⊓ Subgroup.centralizer (E₁' : Set G) ≠
      Uq M T L ⊓ Subgroup.centralizer (E₂' : Set G) := fun he => hne (by rw [he])
  obtain ⟨p₁, hp₁, hE₁a⟩ := S51.exists_imSp_eq_xPoint hd h hE₁T hc₁ hu₁
  obtain ⟨p₂, hp₂, hE₂a⟩ := S51.exists_imSp_eq_xPoint hd h hE₂T hc₂ hu₂
  have hp : p₁ ≠ p₂ := by
    rintro rfl
    apply hne'
    obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
    have hlift := (sp4Lift_holds G M T L h k F _ _ a hd).2.2
    have hfix : MSP.fixSp ((E₁'.subgroupOf M).map a) = MSP.fixSp ((E₂'.subgroupOf M).map a) := by
      have e1 : (E₁'.subgroupOf M).map a = MSP.xPoint p₁ := hE₁a
      have e2 : (E₂'.subgroupOf M).map a = MSP.xPoint p₁ := hE₂a
      rw [e1, e2]
    ext u
    constructor
    · rintro ⟨hu, huc⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c hE₂M ⟨u, hu⟩).2 ?_⟩
      rw [← hfix]
      exact (S5B.mem_centralizer_iff_vec h hlift c hE₁M ⟨u, hu⟩).1 huc
    · rintro ⟨hu, huc⟩
      refine ⟨hu, (S5B.mem_centralizer_iff_vec h hlift c hE₁M ⟨u, hu⟩).2 ?_⟩
      rw [hfix]
      exact (S5B.mem_centralizer_iff_vec h hlift c hE₂M ⟨u, hu⟩).1 huc
  have hsub : MSP.xPoint p₁ ⊔ MSP.xPoint p₂ ≤ S5.vIm h.le a (imM h.le E₁' ⊔ imM h.le E₂') := by
    have e1 : S5.vIm h.le a (imM h.le E₁') = MSP.xPoint p₁ := by
      rw [S5B.vIm_imM h.le]; exact hE₁a
    have e2 : S5.vIm h.le a (imM h.le E₂') = MSP.xPoint p₂ := by
      rw [S5B.vIm_imM h.le]; exact hE₂a
    rw [← e1, ← e2]
    exact sup_le (S5.vIm_mono' h le_sup_left) (S5.vIm_mono' h le_sup_right)
  have hcard := S512R.card_xPoint_sup_ge hp₁ hp₂ hp
  rw [hFq] at hcard
  exact hcard.trans (Subgroup.card_le_of_le hsub)

end Line

end S512J

end CFSG.Quasithin.MS93
