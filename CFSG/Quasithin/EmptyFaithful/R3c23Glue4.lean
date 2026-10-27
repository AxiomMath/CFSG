module

public import CFSG.Quasithin.EmptyFaithful.R3c23Glue3
public import CFSG.Quasithin.EmptyFaithful.R3c23Core
public import CFSG.Quasithin.EmptyFaithful.R3c23Fin
public import CFSG.Quasithin.EmptyFaithful.R3c23Glue1
public import CFSG.Quasithin.EmptyFaithful.R3c23Glue2
public import CFSG.Quasithin.EmptyFaithful.S153MTwoK

public section

namespace CFSG.Quasithin

namespace R3c23

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_map_conj (L : Subgroup G) (x t : G) :
    (L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      L.map (MulAut.conj (x * t)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem fixedVector_of_pairOutput (hPO : PairOutputOfAction) (h38 : A38ForSQTK) :
    ∀ (G : Type) [Group G] [Finite G], FixedVectorStatement (G := G) := by
  intro G _ _ H T L hH hL hT hSQ hLH hHeq hTN hn hq hJ hLV
  have hVred : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hH hT
  set V := VZ T H with hVdef
  have hVe : IsElemAbelian 2 V := hVred.2.2.1
  have hVH : V ≤ H := hVred.1
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hVred.2.1
  have hLX : L ≤ H := le_of_mem_cComp hLH
  have hTH : T ≤ H := hT.1
  have hVT : V ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVH hHN
      (B2F.isPGroup_of_isElemAbelian hVe)).trans (pCoreOf_le_of_isSylowTwoOf hT)
  have hTNV : T ≤ Subgroup.normalizer (V : Set G) := hTH.trans hHN
  have hV2 : ∀ v : IntMod V hVe, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have h38H : A38Part3 (↥H ⧸ CFSG.pCore 2 ↥H) :=
    h38 _ (SQTKHyp.of_sqtkGroup ↥H (C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ))
  obtain ⟨t, htT, htN, hLt, hcommL, hdich⟩ := pair_structure h38H hT hLH hHeq hTN
  have htH : t ∈ H := hTH htT
  have hLtX : L.map (MulAut.conj t).toMonoidHom ≤ H := le_of_mem_cComp hLt
  have hJn : ∀ x ∈ H, (L ⊔ L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x).toMonoidHom ≤
      L ⊔ L.map (MulAut.conj t).toMonoidHom := by
    intro x hx
    rw [Subgroup.map_sup, map_conj_map_conj]
    have h1 : L.map (MulAut.conj x).toMonoidHom ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom := by
      rcases hdich x hx with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    have h2 : L.map (MulAut.conj (x * t)).toMonoidHom ≤ L ⊔ L.map (MulAut.conj t).toMonoidHom := by
      rcases hdich (x * t) (H.mul_mem hx htH) with h | h
      · rw [h]; exact le_sup_left
      · rw [h]; exact le_sup_right
    exact sup_le h1 h2
  have hHNJ : H ≤ Subgroup.normalizer
      ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hJn x hx ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · intro hy
      have h1 : y ∈ (L ⊔ L.map (MulAut.conj t).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom :=
        ⟨x * y * x⁻¹, hy, by simp [mul_assoc]⟩
      exact hJn x⁻¹ (H.inv_mem hx) h1
  have hJH : L ⊔ L.map (MulAut.conj t).toMonoidHom ≤ H := sup_le hLX hLtX
  set ρ : ↥H →* MulAut (IntMod V hVe) := actV hVe hHN with hρ
  set K₁ : Subgroup ↥H := L.subgroupOf H with hK₁
  set t' : ↥H := ⟨t, htH⟩ with ht'
  have hmapt : K₁.map (MulAut.conj t').toMonoidHom =
      (L.map (MulAut.conj t).toMonoidHom).subgroupOf H := S153M.map_conj_subgroupOf hLX htH
  have hsup : K₁ ⊔ K₁.map (MulAut.conj t').toMonoidHom =
      (L ⊔ L.map (MulAut.conj t).toMonoidHom).subgroupOf H := by
    rw [hmapt, ← Subgroup.subgroupOf_sup hLX hLtX]
  have hO2V : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) :=
    pCoreOf_le_centralizer_of_isTwoReducedIn hVred
  have hSQ' : SQTKGroup ↥H := C1GN.isSQTKTC_iff_sqtkGroup.1 hSQ
  have hqK : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁) := by
    have h1 : CFSG.pCore 2 ↥L = (pCoreOf 2 L).subgroupOf L :=
      (A3.pCore_eq_openCore 2 ↥L).trans (map_subtype_subgroupOf' (CFSG.Open.pCore 2 L)).symm
    exact S153M.isQuasisimple_subgroupOf hLX
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq h1) hq)
  have hKn : (K₁ ⊔ K₁.map (MulAut.conj t').toMonoidHom).Normal := by
    rw [hsup]
    exact S153M.normal_subgroupOf_of_le hJH hHNJ
  have hcomm' : ⁅K₁, K₁.map (MulAut.conj t').toMonoidHom⁆ ≤ CFSG.pCore 2 ↥H := by
    rw [hmapt]
    refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    refine S153M.mem_pCore_of_mem_pCoreOf _ (hcommL ?_)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp ha)
      (Subgroup.mem_subgroupOf.mp hb)
  have hQ : CFSG.pCore 2 ↥H ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hρ, actV_eq_one_iff]
    exact hO2V (mem_pCoreOf_of_mem_pCore hx)
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hTJ : T ≤ Subgroup.normalizer
      ((L ⊔ L.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G) :=
    fun x hx => hHNJ (hTH hx)
  have hHJT : H = (L ⊔ L.map (MulAut.conj t).toMonoidHom) ⊔ T :=
    le_antisymm (hHeq ▸ sup_le_sup_right le_sup_left T) (sup_le hJH hTH)
  have h2' : ∀ y : ↥H, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t').toMonoidHom := by
    intro y
    rw [hsup]
    exact S153M.exists_two_pow_mem hHJT hT2 hTJ y
  have hperm' : ∀ x : ↥H, x ∈ Subgroup.normalizer (K₁ : Set ↥H) ∨
      t'⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set ↥H) := by
    have key : ∀ y : ↥H, (y : G) ∈ Subgroup.normalizer (L : Set G) →
        y ∈ Subgroup.normalizer (K₁ : Set ↥H) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro h
      exact Subgroup.mem_normalizer_iff.mp hy (h : G)
    intro x
    rcases hdich x x.2 with h | h
    · exact Or.inl (key x (A38.map_conj_eq_iff.mp h))
    · right
      apply key
      have h3 : L.map (MulAut.conj ((t : G)⁻¹ * (x : G))).toMonoidHom = L := by
        rw [← map_conj_map_conj L t⁻¹ x, h, map_conj_map_conj, inv_mul_cancel]
        ext y
        simp
      exact A38.map_conj_eq_iff.mp h3
  have hLn' : Lin2Cover ↥(K₁.map ρ) := by
    rw [hρ, hK₁, map_actV hVe hHN hLX]
    obtain ⟨n, hn1, hLn⟩ := hn
    exact lin2Cover_autI hVe hVred hLH hn1 hLn hq hLV
  have hnt' : ¬ K₁ ⊔ K₁.map (MulAut.conj t').toMonoidHom ≤ ρ.ker := by
    intro h
    apply hLV
    intro l hl
    have h1 : (⟨l, hLX hl⟩ : ↥H) ∈ ρ.ker :=
      h (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hl))
    rw [MonoidHom.mem_ker, hρ, actV_eq_one_iff] at h1
    exact h1
  have hJV : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G) :=
    not_thompsonJ_le_centralizer hHN hLX hJ hLV
  have hFF : IsFFModule ρ.range := by
    rw [hρ, range_actV hVe hHN]
    exact isFFModule_autI hVe hVH hHN hT hJV
  obtain ⟨G₁, G₂, W₁, W₂, C, P, N₁, N₂, hX, hL₁, hL₂, hne, hfree⟩ :=
    hPO hSQ' hV2 ρ K₁ t' hqK hKn hcomm' hQ h2' hperm' hnt' hFF hLn'
  have hA : ∀ A ∈ offenderImages hVe T, IsFFStarOffender ρ.range A := by
    intro A hA
    have h1 := offenderImages_isFFStarOffender hVe hVT hTNV hA
    refine ⟨?_, h1.2⟩
    rw [hρ, range_actV hVe hHN]
    exact h1.1.trans (autI_mono hVe hTH)
  have hQ2 : IsPGroup 2 (autI hVe (thompsonJ T)) := by
    have h1 : IsPGroup 2 ↥(T.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTNV).symm
    have h2 : IsPGroup 2 (autI hVe T) := h1.map (convI hVe)
    exact h2.to_le (autI_mono hVe (GammaExtra.thompsonJ_le_self T))
  have hAQ : ∀ A ∈ offenderImages hVe T, A ≤ autI hVe (thompsonJ T) := by
    rintro A ⟨A₀, hA₀, rfl⟩
    exact autI_mono hVe (GammaExtra.le_thompsonJ hA₀.1)
  have hQG : autI hVe (thompsonJ T) ≤ G₁ ⊔ G₂ := by
    rw [autI_thompsonJ hVe hTNV]
    exact (iSup_le fun A => iSup_le fun hAP => iSup_le fun _ => B6.le_ffJ (hA A hAP)).trans hX
  obtain ⟨w, hwW, hwL, hwL2, hwA⟩ := exists_fixed_vector hV2 P N₁ N₂ hX hL₂ hne hfree
    (offenderImages hVe T) hA hQ2 hAQ hQG
  have hQfix : ∀ q ∈ autI hVe (thompsonJ T), q w = w := by
    intro q hq
    have hle : autI hVe (thompsonJ T) ≤
        MulAction.stabilizer (MulAut (IntMod V hVe)) w := by
      rw [autI_thompsonJ hVe hTNV]
      refine iSup_le fun A => iSup_le fun hAP => iSup_le fun _ => ?_
      intro a ha
      exact (MulAction.mem_stabilizer_iff).2 (hwA A hAP a ha)
    exact (MulAction.mem_stabilizer_iff).1 (hle hq)
  refine ⟨w.val, w.val_mem, ?_, ?_, ?_⟩
  · by_contra hcon
    push Not at hcon
    apply hwL
    intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    apply IntMod.val_injective
    rw [hρ, actV_apply_val]
    have h1 := hcon (k : G) (Subgroup.mem_subgroupOf.mp hk)
    rw [h1]
    group
  · intro j hj
    have hjT : j ∈ T := GammaExtra.thompsonJ_le_self T hj
    have h1 := hQfix _ (convI_mem_autI hVe hj (hTNV hjT))
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    calc j * w.val = (j * w.val * j⁻¹) * j := by group
      _ = w.val * j := by rw [h2]
  · intro x hxT hxN l hl
    have hxH : x ∈ H := hTH hxT
    have hLx : x * l * x⁻¹ ∈ L.map (MulAut.conj t).toMonoidHom := by
      rcases hdich x hxH with h | h
      · exact absurd (A38.map_conj_eq_iff.mp h) hxN
      · rw [← h]
        exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have hgH : x * l * x⁻¹ ∈ H := hLtX hLx
    have hmem : (⟨x * l * x⁻¹, hgH⟩ : ↥H) ∈ K₁.map (MulAut.conj t').toMonoidHom := by
      rw [hmapt]
      exact Subgroup.mem_subgroupOf.mpr hLx
    have h1 := hwL2 (ρ ⟨x * l * x⁻¹, hgH⟩) ⟨_, hmem, rfl⟩
    have h2 := congrArg IntMod.val h1
    rw [hρ, actV_apply_val] at h2
    calc (x * l * x⁻¹) * w.val = ((x * l * x⁻¹) * w.val * (x * l * x⁻¹)⁻¹) * (x * l * x⁻¹) := by
          group
      _ = w.val * (x * l * x⁻¹) := by rw [h2]

end R3c23

end CFSG.Quasithin
