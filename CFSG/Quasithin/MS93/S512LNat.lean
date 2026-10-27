module

public import CFSG.Quasithin.MS93.S512LFF
public import CFSG.Quasithin.MS93.S512LMod

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S512L

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem rho_eq_one_of_mem_qv (h : PUHyp M T L)
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {V : Subgroup (puAmalgam h.le).Universal} (hVV : V ≤ Vv _ (baseA (puAmalgam h.le)))
    {S : Type} [CommGroup S] {p : ↥V →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (g : ↥(stab (puAmalgam h.le) (baseA _)))
    (hg : (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le))) : ρ g = 1 := by
  refine (hs.rho_eq_one_iff g).2 fun x hx => Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · exact mul_mem (S36E.conj_mem hs.hMA g.2 hx) (inv_mem hx)
  · have h1 : (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ * x⁻¹ ∈
        ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ := by
      rw [Subgroup.commutator_comm, ← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hg (hVV hx)
    refine vv_inf_dSub_le_bSub h (Subgroup.mem_inf.2 ⟨?_, hv h1⟩)
    exact mul_mem (S36E.conj_mem (stab_le_normalizer_vv h) g.2 (hVV hx)) (inv_mem (hVV hx))

theorem isIrrRep_of_irr (h : PUHyp M T L) {V : Subgroup (puAmalgam h.le).Universal}
    (hsec : S512N.SecHyp h V) {S : Type} [CommGroup S] {p : ↥V →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) V (V ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hQ : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      (g : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) → ρ g = 1)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤) :
    S38E.IsIrrRep L (ρ.comp (S512N.eM h.le)) where
  sq v := hsec.sq_eq_one hs v
  pCore m hm := by
    have hmQ : (S512N.eM h.le m : (puAmalgam h.le).Universal) ∈ Qv _ (baseA (puAmalgam h.le)) := by
      rw [S5B.qv_baseA_eq h, S512N.coe_eM]
      exact (S512N.ofA_mem_imM_iff h.le m).2 hm
    rw [MonoidHom.comp_apply]
    exact hQ _ hmQ
  irr W hW := by
    by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · right
      refine hirr W hW0 fun g s hs' => ?_
      obtain ⟨m, rfl⟩ := S512N.eM_surjective h.le g
      exact hW m s hs'
  ne := by
    by_contra hcon
    push Not at hcon
    have := hsec.nontrivial_S hs
    obtain ⟨s, hs1⟩ := exists_ne (1 : S)
    apply hs1
    refine hsec.eq_one_of_fixed hs s fun l hl => ?_
    rw [S5B.puTrans_L_baseA h] at hl
    obtain ⟨m, hm, hml⟩ := hl
    have h1 := hcon m (Subgroup.mem_subgroupOf.1 hm)
    have hl' : S512N.eM h.le m = l := Subtype.ext hml
    rw [← hl']
    rw [MonoidHom.comp_apply] at h1
    rw [h1]
    rfl

theorem range_le_imL (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk2 : 2 ≤ k)
    {S : Type} [CommGroup S] {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hρ : S38E.IsIrrRep L (ρ.comp (S512N.eM h.le))) :
    (ρ.comp (S512N.eM h.le)).range ≤ S38E.IsIrrRep.imL L (ρ.comp (S512N.eM h.le)) := by
  rintro _ ⟨m, rfl⟩
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hsup : L.subgroupOf M ⊔ (pCoreOf 2 M).subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le (pCoreOf_le' M), ← S5B.eq_sup_pCoreOf h hd hk2,
      Subgroup.subgroupOf_self]
  have hmem : m ∈ L.subgroupOf M ⊔ (pCoreOf 2 M).subgroupOf M := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨l, hl, ?_⟩
  rw [map_mul, hρ.pCore o (Subgroup.mem_subgroupOf.1 ho), mul_one]

theorem exists_natural (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk2 : 2 ≤ k)
    (hb : 2 < critDist (puAmalgam h.le))
    (hv : ⁅Vv _ (baseA (puAmalgam h.le)), Qv _ (baseA (puAmalgam h.le))⁆ ≤
      S5.dSub h.le L (baseA _))
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hTl : Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.qLine l))
    (hsec : S512N.SecHyp h (S5.voSub h.le L (baseA _)))
    {S : Type} [CommGroup S] {p : ↥(S5.voSub h.le L (baseA (puAmalgam h.le))) →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) (S5.voSub h.le L (baseA _))
      (S5.voSub h.le L (baseA _) ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤)
    {W E : Subgroup (puAmalgam h.le).Universal} {δ : Vtx (puAmalgam h.le)}
    (hWst : W ≤ stab _ (baseA (puAmalgam h.le)))
    (hVW : S5.voSub h.le L (baseA _) ≤ W ⊔ S5.bSub h.le L (baseA _))
    (hEβ : E ≤ Qv _ (baseB (puAmalgam h.le)))
    (hpair : ⁅W ⊓ Qv _ δ, E⁆ ≤ ZM _ (baseA (puAmalgam h.le)))
    (hidx : (Qv _ δ).relIndex W ≤ (Qv _ (baseA (puAmalgam h.le))).relIndex E)
    (hlt : 1 < (Qv _ (baseA (puAmalgam h.le))).relIndex E) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F')
      (θ : S ≃* Multiplicative (MSP.V4 F')), Fintype.card F' = 2 ^ k ∧
        Function.Surjective a' ∧
        ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : S),
          Multiplicative.toAdd (θ (ρ g s)) = MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s) := by
  have := hsec.finite_S hs
  have hQ := rho_eq_one_of_mem_qv h hv (voSub_le_vv h) hs
  have hρM := isIrrRep_of_irr h hsec hs hQ hirr
  have hβα := (adj_baseA_baseB (puAmalgam h.le)).symm
  have hEst : E ≤ stab _ (baseA (puAmalgam h.le)) := hEβ.trans (qv_le_stab_of_adj _ hβα)
  have hE2 : IsPGroup 2 E := (isPGroup_qv _ h.hyp20 (not_isMVtx_baseB _)).to_le hEβ
  have hAcard := card_map_eq h hv (voSub_le_vv h) hsec hs hirr hEst hE2
  have hAidx := index_fixV_le h hb (voSub_le_vv h) hs hWst hVW hEst hpair
  have hmemR : ∀ g : ↥(stab (puAmalgam h.le) (baseA _)),
      ρ g ∈ (ρ.comp (S512N.eM h.le)).range := fun g => by
    obtain ⟨m, rfl⟩ := S512N.eM_surjective h.le g
    exact ⟨m, rfl⟩
  have hAX : (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ ≤
      (ρ.comp (S512N.eM h.le)).range := by
    rintro _ ⟨g, -, rfl⟩
    exact hmemR g
  have hAel : IsElemAbelian2 ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      obtain ⟨hc, -⟩ := commutator_mem_qv_of_le_qLine h hd hl hTl
        (hEβ (Subgroup.mem_subgroupOf.1 hg)) (hEβ (Subgroup.mem_subgroupOf.1 hg'))
      have hcq : ρ ⁅g, g'⁆ = 1 := hQ ⁅g, g'⁆ (by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv] at hc ⊢
        exact hc)
      rw [← map_mul, ← map_mul]
      have e : g * g' = ⁅g, g'⁆ * (g' * g) := by
        rw [commutatorElement_def]
        group
      rw [e, map_mul, hcq, one_mul]
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨-, hsq⟩ := commutator_mem_qv_of_le_qLine h hd hl hTl
        (hEβ (Subgroup.mem_subgroupOf.1 hg)) (hEβ (Subgroup.mem_subgroupOf.1 hg))
      rw [← map_pow]
      exact hQ (g ^ 2) (by simpa using hsq)
  have hA1 : (E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  have hFF : IsFFModule (ρ.comp (S512N.eM h.le)).range := by
    refine ⟨_, hAX, hA1, hAel, ?_⟩
    have h1 := (fixV ((E.subgroupOf (stab (puAmalgam h.le) (baseA _))).map ρ)).card_mul_index
    rw [← h1, mul_comm, hAcard]
    exact Nat.mul_le_mul_right _ (hAidx.trans hidx)
  obtain ⟨F', iF, fF, φ, θ, hcard, hφs, hθ⟩ :=
    exists_coord_ff h14 hSQ hT h hd hk2 hρM hFF (range_le_imL h hd hk2 hρM)
  refine ⟨F', iF, fF, φ.comp (ρ.codRestrict _ hmemR), θ, hcard, ?_,
    fun g s => hθ (ρ.codRestrict _ hmemR g) s⟩
  intro x
  obtain ⟨⟨_, ⟨m, rfl⟩⟩, rfl⟩ := hφs x
  exact ⟨S512N.eM h.le m, rfl⟩

theorem exists_setup (h : PUHyp M T L)
    {S : Type} [CommGroup S] {p : ↥(S5.voSub h.le L (baseA (puAmalgam h.le))) →* S}
    {ρ : ↥(stab (puAmalgam h.le) (baseA _)) →* MulAut S}
    (hs : S36E.SecData (stab _ (baseA (puAmalgam h.le))) (S5.voSub h.le L (baseA _))
      (S5.voSub h.le L (baseA _) ⊓ S5.bSub h.le L (baseA _)) S p ρ)
    (hirr : ∀ S₁ : Subgroup S, S₁ ≠ ⊥ → S512N.IsInv ρ S₁ → S₁ = ⊤)
    {F' : Type} [Field F'] {a' : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F'}
    (ha' : Function.Surjective a') {θ : S ≃* Multiplicative (MSP.V4 F')}
    (hθ : ∀ (g : ↥(stab (puAmalgam h.le) (baseA _))) (s : S),
      Multiplicative.toAdd (θ (ρ g s)) = MSP.mat (a' g) *ᵥ Multiplicative.toAdd (θ s))
    {V₀ : Subgroup (puAmalgam h.le).Universal} (hV₀ : V₀ ≤ S5.voSub h.le L (baseA _))
    (hV₀n : stab _ (baseA (puAmalgam h.le)) ≤ Subgroup.normalizer (V₀ : Set _))
    (hV₀B : ¬ V₀ ≤ S5.bSub h.le L (baseA _)) :
    ∃ βv : (puAmalgam h.le).Universal → MSP.V4 F',
      S310.Setup (stab _ (baseA (puAmalgam h.le))) (puTrans h.le L (baseA _)) V₀
        (V₀ ⊓ S5.bSub h.le L (baseA _)) a' βv := by
  classical
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  let βv : (puAmalgam h.le).Universal → MSP.V4 F' := fun x =>
    if hx : x ∈ S5.voSub h.le L (baseA (puAmalgam h.le)) then
      Multiplicative.toAdd (θ (p ⟨x, hx⟩)) else 0
  have hβv : ∀ x (hx : x ∈ S5.voSub h.le L (baseA (puAmalgam h.le))),
      βv x = Multiplicative.toAdd (θ (p ⟨x, hx⟩)) := fun x hx => by simp [βv, hx]
  have hXinv : S512N.IsInv ρ ((V₀.subgroupOf (S5.voSub h.le L (baseA _))).map p) := by
    rintro g _ ⟨v, hv, rfl⟩
    have hvV₀ : (v : (puAmalgam h.le).Universal) ∈ V₀ := Subgroup.mem_subgroupOf.1 hv
    have hgv : (g : (puAmalgam h.le).Universal) * v * (g : (puAmalgam h.le).Universal)⁻¹ ∈
        S5.voSub h.le L (baseA (puAmalgam h.le)) := S36E.conj_mem hs.hMA g.2 v.2
    exact ⟨⟨_, hgv⟩, Subgroup.mem_subgroupOf.2 (S36E.conj_mem hV₀n g.2 hvV₀),
      (hs.conj g v hgv).symm⟩
  have hXne : (V₀.subgroupOf (S5.voSub h.le L (baseA _))).map p ≠ ⊥ := by
    intro hbot
    apply hV₀B
    intro v hv
    have : p ⟨v, hV₀ hv⟩ ∈ (V₀.subgroupOf (S5.voSub h.le L (baseA _))).map p :=
      ⟨⟨v, hV₀ hv⟩, Subgroup.mem_subgroupOf.2 hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, hs.ker] at this
    exact this.2
  have hXtop := hirr _ hXne hXinv
  refine ⟨βv, puTrans_le_stab h.le L _, stab_le_normalizer_puTrans h.le hLn _, hV₀n, inf_le_left,
    fun x hx y hy => ?_, fun w => ?_, fun x hx => ?_, fun g x hx => ?_,
    S310.exists_mem_puTrans_of_pow_three h ha'⟩
  · rw [hβv x (hV₀ hx), hβv y (hV₀ hy), hβv _ (mul_mem (hV₀ hx) (hV₀ hy))]
    rw [show (⟨x * y, mul_mem (hV₀ hx) (hV₀ hy)⟩ : ↥(S5.voSub h.le L (baseA _))) =
      ⟨x, hV₀ hx⟩ * ⟨y, hV₀ hy⟩ from rfl, map_mul, map_mul, toAdd_mul]
  · have hmem : θ.symm (Multiplicative.ofAdd w) ∈
        (V₀.subgroupOf (S5.voSub h.le L (baseA _))).map p := by
      rw [hXtop]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hpv⟩ := hmem
    refine ⟨v, Subgroup.mem_subgroupOf.1 hv, ?_⟩
    rw [hβv _ v.2, Subtype.coe_eta, hpv, MulEquiv.apply_symm_apply, toAdd_ofAdd]
  · rw [hβv x (hV₀ hx)]
    constructor
    · intro h0
      have h1 : θ (p ⟨x, hV₀ hx⟩) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]
        rfl
      have h2 : p ⟨x, hV₀ hx⟩ = 1 := by
        rw [← map_one θ] at h1
        exact θ.injective h1
      exact ⟨hx, ((hs.ker _).1 h2).2⟩
    · intro h1
      have h2 : p ⟨x, hV₀ hx⟩ = 1 := (hs.ker _).2 ⟨hV₀ hx, h1.2⟩
      rw [h2, map_one]
      rfl
  · have hgx : (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ ∈
        S5.voSub h.le L (baseA (puAmalgam h.le)) := S36E.conj_mem hs.hMA g.2 (hV₀ hx)
    rw [hβv x (hV₀ hx), hβv _ hgx, ← hθ g, hs.conj g ⟨x, hV₀ hx⟩ hgx]

end S512L

end CFSG.Quasithin.MS93
