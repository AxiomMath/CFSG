module

public import CFSG.Quasithin.EmptyFaithful.S153E51A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Two

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem inf_centralizer_ZS_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    T ⊓ Subgroup.centralizer (ZS153 T M V₁ : Set G) = Sgp153 T V₁ := by
  apply le_antisymm
  · rintro x ⟨hxT, hxC⟩
    by_contra hxS
    have hidx := Decomp153.relIndex_nS cx.c.hyp cx.c.decomp
    have hZS : ZS153 T M V₁ ≤ Subgroup.centralizer (T : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases coset_of_relIndex_two hidx hy hxT hxS with h | h
      · exact Subgroup.mem_centralizer_iff.mp hz.2 y h
      · have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ h
        have h2 := Subgroup.mem_centralizer_iff.mp hxC z hz
        calc y * z = (y * x⁻¹) * (x * z) := by group
          _ = (y * x⁻¹) * (z * x) := by rw [← h2]
          _ = ((y * x⁻¹) * z) * x := by group
          _ = (z * (y * x⁻¹)) * x := by rw [h1]
          _ = z * y := by group
    have hZle : ZS153 T M V₁ ≤ quasithinOmegaOneCenter T := by
      rw [cx.c.hyp.lemma_15_3_2_two.1]
      exact le_inf (ZS_le_V cx) hZS
    have h4 : Nat.card ↥(ZS153 T M V₁) = 4 := Decomp153.card_ZS cx.c.hyp cx.c.decomp
    have h2 : Nat.card ↥(quasithinOmegaOneCenter T) = 2 := cx.c.hyp.lemma_15_3_2_two.2
    have := Subgroup.card_le_of_le hZle
    omega
  · intro s hs
    refine ⟨hs.1, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hw.2 s hs).symm

theorem isElemAbelian_U_of_le_S (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hUS : UH153 T M V₁ Mc ≤ Sgp153 T V₁) : IsElemAbelian 2 (UH153 T M V₁ Mc) := by
  refine HypF91.isElemAbelian_conjClosure_of_forall cx.hF.elemAbelian_Vp fun k hk z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyU : y ∈ UH153 T M V₁ Mc := HypF91.conjSub_le_conjClosure hk hy
  exact Subgroup.mem_centralizer_iff.mp hz.2 y (hUS hyU)

theorem le_S_of_abelian (cx : Ctx15350 T Mc M V₁ V₂ t)
    (hab : ∀ a ∈ UH153 T M V₁ Mc, ∀ b ∈ UH153 T M V₁ Mc, a * b = b * a) :
    UH153 T M V₁ Mc ≤ Sgp153 T V₁ := by
  rw [← inf_centralizer_ZS_eq cx]
  intro u hu
  exact ⟨U_le_T cx hu, Subgroup.mem_centralizer_iff.mpr fun w hw => hab w (ZS_le_U cx hw) u hu⟩

end Two

section Bar

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem card_fixV_mul_s {W : Type*} [CommGroup W] [Finite W] {X L₁ L₂ : Subgroup (MulAut W)}
    {tb : MulAut W} (hexp : ∀ w : W, w ^ 2 = 1) (hS : OfourStruct X L₁ L₂ tb) {S' : Subgroup (MulAut W)}
    {s₁ s₂ : MulAut W} {a₁ a₂ : W} (hd : S1417.SylowData S' L₁ L₂ s₁ s₂ a₁ a₂) :
    Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂))) = 4 := by
  obtain ⟨-, -, h2, -⟩ := T1531O4.rk_fix_S hS hexp hd
  rw [card_eq_two_pow hexp, h2]
  norm_num

omit [Finite G] in
theorem autI_Sgp153 {V T M V₁ : Subgroup G} (hV : IsElemAbelian 2 V)
    {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} {tb : MulAut (IntMod V hV)}
    (hS : OfourStruct (autI hV M) L₁ L₂ tb) (hTM : T ≤ M)
    (hV₁ : (commV L₁).map (inclMod hV) = V₁) :
    autI hV (Sgp153 T V₁) = autI hV T ⊓ (L₁ ⊔ L₂) := by
  subst hV₁
  exact autI_nS hV hS hTM

theorem case_b (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc)
    (hUS : UH153 T M V₁ Mc ≤ Sgp153 T V₁) :
    IsElemAbelian 2 (UH153 T M V₁ Mc) ∧ UH153 T M V₁ Mc ≤ Sgp153 T V₁ ∧
      centerOf (autOn T (VZ T M)) ≤ autOn (UH153 T M V₁ Mc) (VZ T M) ∧
      ZS153 T M V₁ = VZ T M ⊓ UH153 T M V₁ Mc := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hV := cx.c.hyp.elemAbelian
  have hUab := isElemAbelian_U_of_le_S cx hUS
  refine ⟨hUab, hUS, centerOf_le_autI_U cx h1 hS hF, ?_⟩
  apply le_antisymm (le_inf (ZS_le_V cx) (ZS_le_U cx))
  have hr : s₁ * s₂ ∈ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) := mul_mem_autI_U cx h1 hS hF
  have hexp : ∀ w : IntMod (VZ T M) cx.c.hyp.elemAbelian, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hcard4 : Nat.card ↥(VZ T M ⊓ Subgroup.centralizer (UH153 T M V₁ Mc : Set G)) ≤ 4 := by
    rw [← card_fixV_autI cx.c.hyp.elemAbelian (U_le_N cx)]
    calc Nat.card ↥(fixV (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)))
        ≤ Nat.card ↥(fixV (Subgroup.zpowers (s₁ * s₂))) :=
          Subgroup.card_le_of_le (fixV_anti (Subgroup.zpowers_le.mpr hr))
      _ = 4 := card_fixV_mul_s hexp hS hF.sylow
  have hZS_le : ZS153 T M V₁ ≤ VZ T M ⊓ Subgroup.centralizer (UH153 T M V₁ Mc : Set G) :=
    le_inf (ZS_le_V cx) fun z hz => Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_iff.mp hz.2 u (hUS hu)
  have heq : ZS153 T M V₁ = VZ T M ⊓ Subgroup.centralizer (UH153 T M V₁ Mc : Set G) :=
    Subgroup.eq_of_le_of_card_ge hZS_le (by rw [Decomp153.card_ZS cx.c.hyp cx.c.decomp]; exact hcard4)
  intro v hv
  rw [heq]
  refine ⟨hv.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  exact B2F.isElemAbelian_comm hUab hu hv.2

theorem not_autI_U_le_sup (cx : Ctx15350 T Mc M V₁ V₂ t)
    {L₁ L₂ : Subgroup (MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian))}
    {tb : MulAut (IntMod (VZ T M) cx.c.hyp.elemAbelian)}
    (hS : OfourStruct (autI cx.c.hyp.elemAbelian M) L₁ L₂ tb)
    (hV₁ : (commV L₁).map (inclMod cx.c.hyp.elemAbelian) = V₁)
    (hUS : ¬ UH153 T M V₁ Mc ≤ Sgp153 T V₁) :
    ¬ autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) ≤ L₁ ⊔ L₂ := by
  have hSg := autI_Sgp153 cx.c.hyp.elemAbelian hS (T_le_M cx) hV₁
  intro hle
  apply hUS
  intro u hu
  have hN := U_le_N cx hu
  have hmem : convI cx.c.hyp.elemAbelian ⟨u, hN⟩ ∈ autI cx.c.hyp.elemAbelian (Sgp153 T V₁) := by
    rw [hSg]
    exact ⟨autI_U_le_T cx (convI_mem_autI cx.c.hyp.elemAbelian hu hN),
      hle (convI_mem_autI cx.c.hyp.elemAbelian hu hN)⟩
  obtain ⟨s, hsS, hs⟩ := (mem_autI cx.c.hyp.elemAbelian).1 hmem
  have hk : convI cx.c.hyp.elemAbelian (⟨u, hN⟩ * s⁻¹) = 1 := by
    rw [map_mul, map_inv, hs, mul_inv_cancel]
  have hk0 : (u : G) * (s : G)⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (convI_eq_one_iff cx.c.hyp.elemAbelian _).1 hk
  have hk1 : (u : G) * (s : G)⁻¹ ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) :=
    ⟨T.mul_mem (U_le_T cx hu) (T.inv_mem hsS.1), hk0⟩
  have hk2 : (u : G) * (s : G)⁻¹ ∈ Sgp153 T V₁ := by
    have hV₁V : V₁ ≤ VZ T M := cx.c.decomp.le₁
    exact inf_centralizer_le_nS T V₁ hV₁V hk1
  have e : u = ((u : G) * (s : G)⁻¹) * (s : G) := by group
  rw [e]
  exact (Sgp153 T V₁).mul_mem hk2 hsS

theorem case_a (cx : Ctx15350 T Mc M V₁ V₂ t) (hUS : ¬ UH153 T M V₁ Mc ≤ Sgp153 T V₁) :
    IsNonabelian153 (UH153 T M V₁ Mc) ∧
      IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
      autOn (UH153 T M V₁ Mc) (VZ T M) ≤ autOn T (VZ T M) ∧
      autOn (UH153 T M V₁ Mc) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
      ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
        IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, hV₁, -⟩ := exists_bar_model cx
  have hT := cx.c.hyp.isSylowTwoOf_autI
  have hexp : ∀ w : IntMod (VZ T M) cx.c.hyp.elemAbelian, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hSg := autI_Sgp153 cx.c.hyp.elemAbelian hS (T_le_M cx) hV₁
  have hNS := not_autI_U_le_sup cx hS hV₁ hUS
  obtain ⟨hchar, hcard⟩ := eq_even_of_normal_elemAbelian hS hexp hT hF (autI_U_le_T cx)
    (fun _ hh _ hn => autI_U_normal cx hh hn) (fun _ ha _ hb => autI_U_comm cx ha hb)
    (fun _ hn => autI_U_sq cx hn) hNS
  refine ⟨?_, ⟨hcard, fun a ha b hb => autI_U_comm cx ha hb, fun a ha => by
      rw [pow_two]; exact autI_U_sq cx ha⟩, autI_U_le_T cx, ?_, ?_⟩
  · by_contra hna
    unfold IsNonabelian153 at hna
    push Not at hna
    exact hUS (le_S_of_abelian cx fun a ha b hb => hna a ha b hb)
  · intro h
    apply hNS
    have h' : autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) =
        autI cx.c.hyp.elemAbelian (Sgp153 T V₁) := h
    rw [h', hSg]
    exact inf_le_right
  · obtain ⟨q, L₁', L₂', t', hq1, hq2, hq3, hX, -, -⟩ := cx.c.hyp.exists_ofourStruct
    have hcard16 : Nat.card (IntMod (VZ T M) cx.c.hyp.elemAbelian) = 16 := cx.c.hyp.card_VZ
    obtain ⟨Ω, hΩ36, hΩ⟩ := exists_omegaFourPlus hcard16 hq1 hq2 hq3
    have hOmega : IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω := by
      intro g
      refine (hΩ g).trans ?_
      have hXg : g ∈ autOn M (VZ T M) ↔ g ∈ orthogonalGroupOf q := by
        have : autOn M (VZ T M) = orthogonalGroupOf q := hX
        rw [this]
        exact Iff.rfl
      exact and_congr hXg.symm Iff.rfl
    have hle : autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc) ≤ Ω := by
      intro g hg
      have hgU := (hchar g).1 hg
      refine (hΩ g).2 ⟨?_, hgU.2⟩
      have : g ∈ autI cx.c.hyp.elemAbelian M := autI_mono _ (T_le_M cx) hgU.1
      rw [hX] at this
      exact this
    have hp : IsPGroup 2 ↥(autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) :=
      IsPGroup.of_card (p := 2) (n := 2) (by rw [hcard]; norm_num)
    have hU36 : Nat.card ↥((autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)).subgroupOf Ω) = 4 := by
      rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hidx : ¬ 2 ∣ ((autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)).subgroupOf Ω).index := by
      have hmul := Subgroup.card_mul_index
        ((autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)).subgroupOf Ω)
      rw [hU36, hΩ36] at hmul
      omega
    have hsyl : IsSylowTwoOf (autI cx.c.hyp.elemAbelian (UH153 T M V₁ Mc)) Ω := ⟨hle, hp, hidx⟩
    exact ⟨Ω, hOmega, hsyl⟩

theorem lemma_15_3_51_two (cx : Ctx15350 T Mc M V₁ V₂ t) (h1 : ¬ VZ T M ≤ pCoreOf 2 Mc) :
    (IsNonabelian153 (UH153 T M V₁ Mc) ∧
        IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
        autOn (UH153 T M V₁ Mc) (VZ T M) ≤ autOn T (VZ T M) ∧
        autOn (UH153 T M V₁ Mc) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
        ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
          IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω) ∨
      (IsElemAbelian 2 (UH153 T M V₁ Mc) ∧ UH153 T M V₁ Mc ≤ Sgp153 T V₁ ∧
        centerOf (autOn T (VZ T M)) ≤ autOn (UH153 T M V₁ Mc) (VZ T M) ∧
        ZS153 T M V₁ = VZ T M ⊓ UH153 T M V₁ Mc) := by
  by_cases hUS : UH153 T M V₁ Mc ≤ Sgp153 T V₁
  · exact Or.inr (case_b cx h1 hUS)
  · exact Or.inl (case_a cx hUS)

end Bar

end S153E

end CFSG.Quasithin
