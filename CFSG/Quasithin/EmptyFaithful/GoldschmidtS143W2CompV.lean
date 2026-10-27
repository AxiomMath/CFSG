module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompT
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompG
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompM

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

section V

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {Z L : Subgroup G}

theorem card_le_four_of_pGroup_conj (h : Ctx T M g A t d x) (hf : Wp0 T d x) (hZ : Z ≤ Gw d x)
    (hZc : ∀ c ∈ Gw d x,
      (∀ u ∈ K0 T d x, ∀ k ∈ Z.map (MulAut.conj c).toMonoidHom,
        u * k * u⁻¹ ∈ Z.map (MulAut.conj c).toMonoidHom) ∧
      d * d ∉ Z.map (MulAut.conj c).toMonoidHom) {S : Subgroup G} (hSZ : S ≤ Z)
    (hS2 : IsPGroup 2 S) : Nat.card S ≤ 4 := by
  obtain ⟨c, hc, hcS⟩ := exists_conj_le_sylow h.hSyl hS2 (hSZ.trans hZ)
  have hle : S.map (MulAut.conj c).toMonoidHom ≤ Tw T d x ⊓ Z.map (MulAut.conj c).toMonoidHom := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hcS s hs, ⟨s, hSZ hs, rfl⟩⟩
  have hcard : Nat.card (S.map (MulAut.conj c).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [← hcard]
  exact card_le_four_of_le h hf (hZc c hc).1 (hZc c hc).2 hle

theorem not_component_le_conj (h : Ctx T M g A t d x) (hf : Wp0 T d x) (hZ : Z ≤ Gw d x)
    (hZc : ∀ c ∈ Gw d x,
      (∀ u ∈ K0 T d x, ∀ k ∈ Z.map (MulAut.conj c).toMonoidHom,
        u * k * u⁻¹ ∈ Z.map (MulAut.conj c).toMonoidHom) ∧
      d * d ∉ Z.map (MulAut.conj c).toMonoidHom)
    (hwZ : wOfX d x ∈ Z) (hL : IsComponentIn L (Gw d x)) : ¬ L ≤ Z := by
  intro hLZ
  have hq := isQuasisimple_of_isComponentIn hL
  obtain ⟨Sy⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  set S : Subgroup G := (Sy : Subgroup ↥L).map L.subtype with hS
  have hS2 : IsPGroup 2 S := Sy.isPGroup'.map L.subtype
  have hSL : S ≤ L := Subgroup.map_subtype_le _
  have hW2 := h.isPGroup_zpowers_w
  have hcommL : ∀ l ∈ L, l * wOfX d x = wOfX d x * l := fun l hl => mem_Gw_iff.mp (hL.1 hl)
  have hSN : S ≤ Subgroup.normalizer (Subgroup.zpowers (wOfX d x) : Set G) := fun s hs =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (Commute.zpow_left (show Commute (wOfX d x) s from (hcommL s (hSL hs)).symm) k).eq)
  have hS₂ : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers (wOfX d x)) :=
    hS2.to_sup_of_normal_right' hW2 hSN
  have hS₂Z : S ⊔ Subgroup.zpowers (wOfX d x) ≤ Z :=
    sup_le (hSL.trans hLZ) (Subgroup.zpowers_le.mpr hwZ)
  have hc := card_le_four_of_pGroup_conj h hf hZ hZc hS₂Z hS₂
  exact false_of_quasisimple_sylow_le_small hq hcommL h.w_sq h.w_ne Sy hc
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) le_sup_left

theorem Ctx.d_mem_Gw (h : Ctx T M g A t d x) : d ∈ Gw d x := by
  have hd : d ∈ dOf T M := h.hD ▸ Subgroup.mem_zpowers d
  have h0 : d ∈ Xgen T M := le_Wgen (dOf_mem_delta h.c) hd
  rw [mem_Gw_iff]
  exact Xgen_comm h.c h.hD h.hd4 _ h0 _ (wOfX_mem_Xgen h.c h.hD h.hx)

theorem Ctx.u0_mem_Tw (h : Ctx T M g A t d x) : u0Of d x ∈ Tw T d x := by
  have hd : d ∈ dOf T M := h.hD ▸ Subgroup.mem_zpowers d
  have hX : u0Of d x ∈ Xgen T M :=
    (Xgen T M).mul_mem (d1_mem_Xgen h.c h.hx hd) (d2_mem_Xgen h.c h.hx hd)
  exact ⟨Xgen_le_T hX, h.u0_mem_Gw⟩

theorem Gw_pData (h : Ctx T M g A t d x) (hf : LocalFacts T d x) :
    CFSG.pPrimeCore 2 ↥(Gw d x) = ⊥ ∧
      (∀ g' : ↥(Gw d x), g' * (⟨wOfX d x, h.w_mem_Gw⟩ : ↥(Gw d x)) = ⟨wOfX d x, h.w_mem_Gw⟩ * g') ∧
      (⟨wOfX d x, h.w_mem_Gw⟩ : ↥(Gw d x)) ≠ 1 ∧
      (⟨wOfX d x, h.w_mem_Gw⟩ : ↥(Gw d x)) ∈ CFSG.pCore 2 ↥(Gw d x) ∧
      Nat.card (CFSG.pCore 2 ↥(Gw d x)) ≤ 4 := by
  refine ⟨?_, fun g' => Subtype.ext (mem_Gw_iff.mp g'.2),
    fun h1 => h.w_ne (congrArg Subtype.val h1),
    ?_, ?_⟩
  · have := oddCore_Gw h
    rw [oddCoreIn_eq_map] at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Gw d x).subtype_injective).mp this
  · exact (mem_pCore_iff _).mpr (hf.wp1.w_mem_P (Subgroup.mem_zpowers (wOfX d x)))
  · have := hf.wp1.card_P
    rw [pCoreOf_eq_map_pCore, Subgroup.card_map_of_injective (Gw d x).subtype_injective] at this
    exact this

theorem three_components_Gw (h : Ctx T M g A t d x) (hf : LocalFacts T d x) {L₁ L₂ L₃ : Subgroup G}
    (h₁ : IsComponentIn L₁ (Gw d x)) (h₂ : IsComponentIn L₂ (Gw d x))
    (h₃ : IsComponentIn L₃ (Gw d x)) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) : False := by
  obtain ⟨hO, hwc, hw1, hwP, hP⟩ := Gw_pData h hf
  have hne : ∀ {A B : Subgroup G}, A ≤ Gw d x → B ≤ Gw d x → A ≠ B →
      A.subgroupOf (Gw d x) ≠ B.subgroupOf (Gw d x) := fun hA hB hAB e =>
    hAB (by
      have := Subgroup.subgroupOf_inj.mp e
      rwa [inf_eq_left.mpr hA, inf_eq_left.mpr hB] at this)
  have hSyl := h.hSyl
  have hT2 : IsPGroup 2 ((Tw T d x).subgroupOf (Gw d x)) :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSyl.1).symm
  refine false_of_three_components hO hwc hw1 hwP hP (T := (Tw T d x).subgroupOf (Gw d x)) hT2
    hSyl.2.2 ?_ (u := ⟨u0Of d x, h.u0_mem_Gw⟩) (Subgroup.mem_subgroupOf.mpr h.u0_mem_Tw) ?_
    h₁.2 h₂.2 h₃.2 (hne h₁.1 h₂.1 h12) (hne h₁.1 h₃.1 h13) (hne h₂.1 h₃.1 h23)
  · rw [card_subgroupOf_Gw inf_le_right, (hf.wp0).card_Tw]; norm_num
  · intro hmem
    have : (((⟨u0Of d x, h.u0_mem_Gw⟩ : ↥(Gw d x)) * ⟨u0Of d x, h.u0_mem_Gw⟩ : ↥(Gw d x)) : G) ∈
        pCoreOf 2 (Gw d x) := (mem_pCore_iff _).mp hmem
    exact hf.wp1.z_not_mem_P (by simpa [h.u0_sq] using this)

end V

end InspW2

end S143

end CFSG.Quasithin
