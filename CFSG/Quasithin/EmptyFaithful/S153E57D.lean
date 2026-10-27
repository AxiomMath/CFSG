module

public import CFSG.Quasithin.EmptyFaithful.S153E51A
public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E57

section Setup

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

abbrev NZ (T : Subgroup G) : Subgroup G := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)

theorem Z_card (cx : Ctx15350 T Mc M V₁ V₂ t) : Nat.card (quasithinOmegaOneCenter T) = 2 :=
  cx.hF.card_V₁

theorem Mc_le_NZ (cx : Ctx15350 T Mc M V₁ V₂ t) : Mc ≤ NZ T := cx.hF.H_normalizes_V₁

theorem NZ_le_Mc (cx : Ctx15350 T Mc M V₁ V₂ t) : NZ T ≤ Mc := by
  have h := normalizer_eq_centralizer_of_card_eq_two (Z_card cx)
  intro g hg
  have : g ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := h ▸ hg
  exact cx.c.hyp.qtfe.centralizer_le_mc this

theorem Mc_le_centralizer_Z (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Mc ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := cx.hF.H_le_centralizer

theorem NZ_le_normalizer_U (cx : Ctx15350 T Mc M V₁ V₂ t) :
    NZ T ≤ Subgroup.normalizer (UH153 T M V₁ Mc : Set G) :=
  fun _ hn => le_normalizer_conjClosure _ _ (NZ_le_Mc cx hn)

@[expose] noncomputable def rho (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥(NZ T) →* MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  (conjAct (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))).comp
    (MonoidHom.codRestrict (secMk (NZ T) (quasithinOmegaOneCenter T))
      (Subgroup.normalizer (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) :
        Set (SecQuot (NZ T) (quasithinOmegaOneCenter T))))
      (fun n => secMk_mem_normalizer_secImg (NZ_le_normalizer_U cx n.2)))

theorem rho_apply_coe (cx : Ctx15350 T Mc M V₁ V₂ t) (n : NZ T)
    (x : tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :
    ((rho cx n x : tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :
      SecQuot (NZ T) (quasithinOmegaOneCenter T)) =
      secMk (NZ T) (quasithinOmegaOneCenter T) n * x *
        (secMk (NZ T) (quasithinOmegaOneCenter T) n)⁻¹ :=
  conjAct_apply_coe' _ _ x

theorem mem_XStar_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (B : Subgroup G)
    (a : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    a ∈ XStar153 T M V₁ Mc B ↔ ∃ n : NZ T, (n : G) ∈ B ∧ rho cx n = a := by
  show a ∈ autOn (tildeOf (quasithinOmegaOneCenter T) B)
    (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) ↔ _
  rw [mem_autOn_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨n, hnB, hn⟩ := mem_secImg.1 hs
    exact ⟨n, hnB, congrArg (conjAct _) (Subtype.ext hn)⟩
  · rintro ⟨n, hnB, rfl⟩
    exact ⟨⟨secMk _ _ n, secMk_mem_normalizer_secImg (NZ_le_normalizer_U cx n.2)⟩,
      mem_secImg.2 ⟨n, hnB, rfl⟩, rfl⟩

theorem rho_mem_XStar (cx : Ctx15350 T Mc M V₁ V₂ t) {B : Subgroup G} (n : NZ T) (hn : (n : G) ∈ B) :
    rho cx n ∈ XStar153 T M V₁ Mc B :=
  (mem_XStar_iff cx B _).2 ⟨n, hn, rfl⟩

theorem rho_eq_one_of_forall (cx : Ctx15350 T Mc M V₁ V₂ t) (n : NZ T)
    (h : ∀ u ∈ UH153 T M V₁ Mc, (n : G) * u * (n : G)⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T) :
    rho cx n = 1 := by
  ext x
  rw [MulAut.one_apply, rho_apply_coe]
  obtain ⟨u, hu, hux⟩ := mem_secImg.1 x.2
  rw [← hux]
  have h1 : secMk (NZ T) (quasithinOmegaOneCenter T) (n * u * n⁻¹ * u⁻¹) = 1 :=
    secMk_eq_one_iff.2 (by simpa using h u hu)
  simp only [map_mul, map_inv] at h1
  exact mul_inv_eq_one.1 h1

theorem rho_eq_one_of_mem_U (cx : Ctx15350 T Mc M V₁ V₂ t) (n : NZ T)
    (hn : (n : G) ∈ UH153 T M V₁ Mc) : rho cx n = 1 := by
  have h : (n : G) ∈ centralizerMod (quasithinOmegaOneCenter T) Mc (UH153 T M V₁ Mc) :=
    cx.hF.pCoreOf_eq_centralizerMod ▸ S153E.U_le_Q cx hn
  exact rho_eq_one_of_forall cx n h.2.2

theorem mem_XStar_conj_iff (cx : Ctx15350 T Mc M V₁ V₂ t) (B : Subgroup G) (g : NZ T)
    (a' : MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    a' ∈ XStar153 T M V₁ Mc (conjSubgroup B g) ↔
      ∃ a ∈ XStar153 T M V₁ Mc B, a' = (rho cx g)⁻¹ * a * rho cx g := by
  constructor
  · intro h
    obtain ⟨n, hnB, rfl⟩ := (mem_XStar_iff cx _ _).1 h
    have hn : (g : G) * n * (g : G)⁻¹ ∈ B := mem_conjSubgroup_iff.1 hnB
    refine ⟨rho cx (g * n * g⁻¹), rho_mem_XStar cx (g * n * g⁻¹) (by simpa using hn), ?_⟩
    simp [map_mul, map_inv, mul_assoc]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, hnB, rfl⟩ := (mem_XStar_iff cx _ _).1 ha
    refine (mem_XStar_iff cx _ _).2 ⟨g⁻¹ * n * g, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have e : (g : G) * ((g⁻¹ * n * g : NZ T) : G) * (g : G)⁻¹ = (n : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact hnB
    · simp [map_mul, map_inv, mul_assoc]

theorem XStar_mono (cx : Ctx15350 T Mc M V₁ V₂ t) {B B' : Subgroup G} (h : B ≤ B') :
    XStar153 T M V₁ Mc B ≤ XStar153 T M V₁ Mc B' := by
  intro a ha
  obtain ⟨n, hn, rfl⟩ := (mem_XStar_iff cx _ _).1 ha
  exact rho_mem_XStar cx n (h hn)

theorem XStar_le_HStar (cx : Ctx15350 T Mc M V₁ V₂ t) {B : Subgroup G} (h : B ≤ Mc) :
    XStar153 T M V₁ Mc B ≤ HStar153 T M V₁ Mc :=
  XStar_mono cx h

end Setup

section XFacts

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}
  {N₁ : Subgroup (MulAut ↥(VZ T M))} {y : G}

omit [Finite G] in
theorem Yi_le_Y (N : Subgroup (MulAut ↥(VZ T M))) : Yi153 T Mc M V₁ N ≤ Y153 Mc M :=
  (oTwoUpper_le _).trans inf_le_left

theorem X_le_Mc (cx : Ctx15350 T Mc M V₁ V₂ t) (hy : y ∈ Yi153 T Mc M V₁ N₁)
    (hV₀ : V0gp153 T Mc M V₁ N₁ =
      quasithinOmegaOneCenter T ⊔ conjSubgroup (quasithinOmegaOneCenter T) y) :
    Xgp153 T M V₁ Mc y ≤ Mc := by
  intro x hx
  have hf : y * x * y⁻¹ ∈ Fgp153 T M V₁ Mc y := mem_conjSubgroup_iff.1 hx
  obtain ⟨hfU, hfMc⟩ := hf
  have hfMc' : y * (y * x * y⁻¹) * y⁻¹ ∈ Mc := mem_conjSubgroup_iff.1 hfMc
  have hfC : y * x * y⁻¹ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Mc_le_centralizer_Z cx (S153E.U_le_Q cx hfU |> pCoreOf_le 2 Mc)
  have hZf : quasithinOmegaOneCenter T ≤ Subgroup.centralizer ({y * x * y⁻¹} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (Subgroup.mem_centralizer_iff.1 hfC z hz).symm
  have hZyf : conjSubgroup (quasithinOmegaOneCenter T) y ≤
      Subgroup.centralizer ({y * x * y⁻¹} : Set G) := by
    intro w hw
    have hw' : y * w * y⁻¹ ∈ quasithinOmegaOneCenter T := mem_conjSubgroup_iff.1 hw
    have h1 := Subgroup.mem_centralizer_iff.1 (Mc_le_centralizer_Z cx hfMc') _ hw'
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    have h2 : (y * x * y⁻¹) * w = w * (y * x * y⁻¹) := by
      calc (y * x * y⁻¹) * w = y⁻¹ * ((y * (y * x * y⁻¹) * y⁻¹) * (y * w * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * w * y⁻¹) * (y * (y * x * y⁻¹) * y⁻¹)) * y := by rw [h1]
        _ = w * (y * x * y⁻¹) := by group
    exact h2
  have hV₀le : V0gp153 T Mc M V₁ N₁ ≤ Subgroup.centralizer ({y * x * y⁻¹} : Set G) :=
    hV₀ ▸ sup_le hZf hZyf
  have hcomm : ∀ z ∈ quasithinOmegaOneCenter T,
      (y * x * y⁻¹) * (y * z * y⁻¹) = (y * z * y⁻¹) * (y * x * y⁻¹) := by
    intro z hz
    have hmem : y * z * y⁻¹ ∈ V0gp153 T Mc M V₁ N₁ := mem_conjClosure hy hz
    exact Subgroup.mem_centralizer_iff.1 (hV₀le hmem) _ (Set.mem_singleton _)
  refine cx.c.hyp.qtfe.centralizer_le_mc (Subgroup.mem_centralizer_iff.2 fun z hz => ?_)
  have h := hcomm z hz
  calc z * x = y⁻¹ * ((y * z * y⁻¹) * (y * x * y⁻¹)) * y := by group
    _ = y⁻¹ * ((y * x * y⁻¹) * (y * z * y⁻¹)) * y := by rw [h]
    _ = x * z := by group

theorem conj_normalizes_X (cx : Ctx15350 T Mc M V₁ V₂ t) (hy : y ∈ Yi153 T Mc M V₁ N₁) {c : G}
    (hc : c ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G)) :
    ∀ x ∈ Xgp153 T M V₁ Mc y, c * x * c⁻¹ ∈ Xgp153 T M V₁ Mc y := by
  intro x hx
  have hyY : y ∈ Y153 Mc M := Yi_le_Y N₁ hy
  have hyN : y ∈ Subgroup.normalizer (pCoreOf 2 (Y153 Mc M ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hyY)
  have hcQ : c ∈ pCoreOf 2 (Y153 Mc M ⊔ T) := by rw [← cx.hF.cT]; exact hc
  have hc'Q : y * c * y⁻¹ ∈ pCoreOf 2 (Y153 Mc M ⊔ T) :=
    (Subgroup.mem_normalizer_iff.1 hyN c).1 hcQ
  have hc' : y * c * y⁻¹ ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rw [cx.hF.cT]; exact hc'Q
  have hyV : y⁻¹ ∈ Subgroup.normalizer (VZ T M : Set G) :=
    (Subgroup.normalizer (VZ T M : Set G)).inv_mem
      (cx.c.hyp.le_normalizer (Y153_le Mc M hyY))
  have hc''C : y * (y * c * y⁻¹) * y⁻¹ ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hw : y⁻¹ * z * y ∈ VZ T M := by
      have := (Subgroup.mem_normalizer_iff.1 hyV z).1 (cx.c.hyp.Z_le_VZ hz)
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hc'.2 _ hw
    calc z * (y * (y * c * y⁻¹) * y⁻¹) = y * ((y⁻¹ * z * y) * (y * c * y⁻¹)) * y⁻¹ := by group
      _ = y * ((y * c * y⁻¹) * (y⁻¹ * z * y)) * y⁻¹ := by rw [h1]
      _ = (y * (y * c * y⁻¹) * y⁻¹) * z := by group
  have hc''Mc : y * (y * c * y⁻¹) * y⁻¹ ∈ Mc := cx.c.hyp.qtfe.centralizer_le_mc hc''C
  have hf : y * x * y⁻¹ ∈ Fgp153 T M V₁ Mc y := mem_conjSubgroup_iff.1 hx
  obtain ⟨hfU, hfMc⟩ := hf
  have hfMc' : y * (y * x * y⁻¹) * y⁻¹ ∈ Mc := mem_conjSubgroup_iff.1 hfMc
  have hc'Mc : y * c * y⁻¹ ∈ Mc := S153E.T_le_Mc cx hc'.1
  rw [Xgp153, mem_conjSubgroup_iff]
  refine ⟨?_, mem_conjSubgroup_iff.2 ?_⟩
  · have := S153E.U_conj_mem (T := T) (M := M) (V₁ := V₁) hc'Mc hfU
    have e : y * (c * x * c⁻¹) * y⁻¹ = (y * c * y⁻¹) * (y * x * y⁻¹) * (y * c * y⁻¹)⁻¹ := by group
    rw [e]
    exact this
  · have e : y * (y * (c * x * c⁻¹) * y⁻¹) * y⁻¹ =
        (y * (y * c * y⁻¹) * y⁻¹) * (y * (y * x * y⁻¹) * y⁻¹) * (y * (y * c * y⁻¹) * y⁻¹)⁻¹ := by
      group
    rw [e]
    exact Mc.mul_mem (Mc.mul_mem hc''Mc hfMc') (Mc.inv_mem hc''Mc)

theorem sq_mem_UCT (cx : Ctx15350 T Mc M V₁ V₂ t) (h51 : Concl15351 cx) (h52 : Concl15352 cx)
    {t₂ : G} (ht₂ : t₂ ∈ T) :
    ∃ u ∈ UH153 T M V₁ Mc, ∃ c ∈ T ⊓ Subgroup.centralizer (VZ T M : Set G), t₂ * t₂ = u * c := by
  have hV := cx.c.hyp.elemAbelian
  obtain ⟨L₁, L₂, tb, -, -, -, -, -, hS, -, -, -⟩ := S153E.exists_bar_model cx
  have hT8 : Nat.card ↥(autI hV T) = 8 := hS.card_T cx.c.hyp.isSylowTwoOf_autI
  obtain ⟨-, hK4, -⟩ : IsNonabelian153 (UH153 T M V₁ Mc) ∧
      IsKleinFour153 (autOn (UH153 T M V₁ Mc) (VZ T M)) ∧
      (autOn (UH153 T M V₁ Mc) (VZ T M) ≤ autOn T (VZ T M) ∧
        autOn (UH153 T M V₁ Mc) (VZ T M) ≠ autOn (Sgp153 T V₁) (VZ T M) ∧
        ∃ Ω : Subgroup (MulAut ↥(VZ T M)), IsOmega4PlusOfM153 T M cx.c.hyp.elemAbelian Ω ∧
          IsSylowTwoOf (autOn (UH153 T M V₁ Mc) (VZ T M)) Ω) := by
    rcases h51.two with h | ⟨hab, -, -, -⟩
    · exact ⟨h.1, h.2.1, h.2.2⟩
    · exfalso
      obtain ⟨a, ha, b, hb, hne⟩ := h52
      exact hne (B2F.isElemAbelian_comm hab ha hb)
  have hU4 : Nat.card ↥(autI hV (UH153 T M V₁ Mc)) = 4 := hK4.1
  have hle : autI hV (UH153 T M V₁ Mc) ≤ autI hV T := S153E.autI_U_le_T cx
  have hidx : ((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T)).index = 2 := by
    have hmul := Subgroup.card_mul_index ((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T))
    have hc : Nat.card ↥((autI hV (UH153 T M V₁ Mc)).subgroupOf (autI hV T)) = 4 := by
      rw [← hU4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [hc, hT8] at hmul
    omega
  have htN : t₂ ∈ Subgroup.normalizer (VZ T M : Set G) := S153E.T_le_N cx ht₂
  have hmem := Subgroup.mul_self_mem_of_index_two hidx
    (⟨convI hV ⟨t₂, htN⟩, convI_mem_autI hV ht₂ htN⟩ : ↥(autI hV T))
  rw [Subgroup.mem_subgroupOf] at hmem
  obtain ⟨u, huU, hu⟩ := (mem_autI hV).1 hmem
  have haa : convI hV (⟨t₂, htN⟩ * ⟨t₂, htN⟩) = convI hV ⟨t₂, htN⟩ * convI hV ⟨t₂, htN⟩ :=
    map_mul _ _ _
  have hu2 : convI hV u = convI hV ⟨t₂, htN⟩ * convI hV ⟨t₂, htN⟩ := by
    rw [hu]
    rfl
  have hu' : convI hV (u⁻¹ * (⟨t₂, htN⟩ * ⟨t₂, htN⟩)) = 1 := by
    rw [map_mul, map_inv, hu2, haa]
    exact inv_mul_cancel _
  have hcC : ((u⁻¹ * (⟨t₂, htN⟩ * ⟨t₂, htN⟩) : Subgroup.normalizer (VZ T M : Set G)) : G) ∈
      Subgroup.centralizer (VZ T M : Set G) := (convI_eq_one_iff hV _).1 hu'
  refine ⟨u, huU, (u : G)⁻¹ * (t₂ * t₂), ⟨?_, ?_⟩, by group⟩
  · exact T.mul_mem (T.inv_mem (S153E.U_le_T cx huU)) (T.mul_mem ht₂ ht₂)
  · simpa using hcC

end XFacts

end S153E57

end CFSG.Quasithin
