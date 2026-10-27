module

public import CFSG.Quasithin.MS93.S36SpTwo
public import CFSG.Quasithin.MS93.S36Inputs
public import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.S36SpRed
public import CFSG.Quasithin.MS93.S36SpSide

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem centralizer_conj {K : Type*} [Group K] (g t : K) :
    Subgroup.centralizer ({(MulAut.conj g).toMonoidHom t} : Set K) =
      (Subgroup.centralizer ({t} : Set K)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff, MulAut.conj_symm_apply]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  · intro hx
    calc x * (g * t * g⁻¹) = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by rw [hx]
      _ = g * t * g⁻¹ * x := by group

theorem S33iiW_smul (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {g : (puAmalgam h.le).Universal} (hg : g • baseA (puAmalgam h.le) = baseA _)
    (hW : S33iiW h α') : S33iiW h (g • α') := by
  obtain ⟨k, hk, hc⟩ := hW
  refine ⟨k, hk, ?_⟩
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hgeo : geo (puAmalgam h.le) (g • α') (baseA _) 1 =
      g • geo (puAmalgam h.le) α' (baseA _) 1 := by
    have := geo_smul (puAmalgam h.le) g α' (baseA _) 1
    rwa [hg] at this
  have hZA : ZM (puAmalgam h.le) (baseA _) =
      (ZM (puAmalgam h.le) (baseA _)).map (MulAut.conj g).toMonoidHom := by
    conv_lhs => rw [← hg]
    exact zm_smul (puAmalgam h.le) g _
  have hQ' : Qv (puAmalgam h.le) (g • α') =
      (Qv (puAmalgam h.le) α').map (MulAut.conj g).toMonoidHom := qv_smul _ g α'
  have hQβ : Qv (puAmalgam h.le) (geo (puAmalgam h.le) (g • α') (baseA _) 1) =
      (Qv (puAmalgam h.le) (geo (puAmalgam h.le) α' (baseA _) 1)).map
        (MulAut.conj g).toMonoidHom := by
    rw [hgeo, qv_smul]
  have hZ' : ZM (puAmalgam h.le) (g • α') =
      (ZM (puAmalgam h.le) α').map (MulAut.conj g).toMonoidHom := zm_smul _ g α'
  rcases hc with ⟨hk1, t₁, ht₁, t₂, ht₂, hrel, hne, hsup⟩ | h2
  · refine Or.inl ⟨hk1, (MulAut.conj g).toMonoidHom t₁, ?_, (MulAut.conj g).toMonoidHom t₂, ?_,
      fun t ht => ?_, ?_, ?_⟩
    · rw [hQβ]
      exact Subgroup.mem_map_of_mem _ ht₁
    · rw [hQβ]
      exact Subgroup.mem_map_of_mem _ ht₂
    · have hrel' : ∀ t ∈ ({t₁, t₂} : Set (puAmalgam h.le).Universal),
          (Subgroup.centralizer ({(MulAut.conj g).toMonoidHom t} :
            Set (puAmalgam h.le).Universal)).relIndex (ZM (puAmalgam h.le) (g • α')) = 2 := by
        intro t ht'
        rw [centralizer_conj, hZ', Subgroup.relIndex_map_map_of_injective _ _ hinj]
        exact hrel t ht'
      rcases ht with rfl | rfl
      · exact hrel' t₁ (Or.inl rfl)
      · exact hrel' t₂ (Or.inr rfl)
    · rw [hQ', ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hinj]
      exact hne
    · rw [hZA, hQ', ← Subgroup.map_sup, hsup, Subgroup.map_sup, MonoidHom.map_closure,
        Set.image_pair]
  · right
    rw [hQ', hZA, Subgroup.relIndex_map_map_of_injective _ _ hinj]
    exact h2

theorem relIndex_centralizer_imM (h : PUHyp M T L) (m : ↥M) {E : Subgroup G} (hE : E ≤ M) :
    (Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set (puAmalgam h.le).Universal)).relIndex
        (imM h.le E) = (Subgroup.centralizer ({(m : G)} : Set G)).relIndex E := by
  have e : Subgroup.centralizer ({(puAmalgam h.le).ofA m} : Set (puAmalgam h.le).Universal) ⊓
      imM h.le E = imM h.le (Subgroup.centralizer ({(m : G)} : Set G) ⊓ E) := by
    ext x
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨hx, hxE⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hxE
      refine Subgroup.mem_map.2 ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨?_, hy⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul] at hx
      exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective hx)
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hy
      refine ⟨?_, Subgroup.mem_map.2 ⟨y, hy.2, rfl⟩⟩
      have hy1 := Subgroup.mem_centralizer_singleton_iff.1 hy.1
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext hy1)
  rw [← Subgroup.inf_relIndex_right, e, S33.relIndex_imM h.le hE, Subgroup.inf_relIndex_right]

theorem s33iiW_inr (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 2) (ψ : MulAut ↥T)
    (hc : IsCritical (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _))
    (hW : S33iiW h ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _)) :
    ∃ k : ℕ, IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) k ∧
      ((k = 1 ∧ ∃ m₁ ∈ T, ∃ m₂ ∈ T,
        (Subgroup.centralizer ({m₁} : Set G)).relIndex (tImage ψ (Z0q M T)) = 2 ∧
        (Subgroup.centralizer ({m₂} : Set G)).relIndex (tImage ψ (Z0q M T)) = 2 ∧
        m₁ * m₂⁻¹ ∉ tImage ψ (pCoreOf 2 M) ∧
        Z0q M T ⊔ tImage ψ (pCoreOf 2 M) =
          Subgroup.closure ({m₁, m₂} : Set G) ⊔ tImage ψ (pCoreOf 2 M)) ∨
      (tImage ψ (pCoreOf 2 M)).relIndex (Z0q M T) = 2 ^ k) := by
  set X := puAmalgam h.le
  set α' := X.ofB (SemidirectProduct.inr ψ) • baseA X with hα'
  obtain ⟨k, hk, hcase⟩ := hW
  refine ⟨k, hk, ?_⟩
  have hZM : Z0q M T ≤ M := Z0q_le M T
  have hψZM : tImage ψ (Z0q M T) ≤ M := (tImage_le _ _).trans h.le
  have hψQM : tImage ψ (pCoreOf 2 M) ≤ M := (tImage_le _ _).trans h.le
  have hQα' : Qv X α' = imM h.le (tImage ψ (pCoreOf 2 M)) := qv_inr h ψ
  have hZα' : ZM X α' = imM h.le (tImage ψ (Z0q M T)) := zm_inr h ψ
  have hZα : ZM X (baseA X) = imM h.le (Z0q M T) := puAmalgam.zm_baseA h.le
  rcases hcase with ⟨hk1, t₁, ht₁, t₂, ht₂, hrel, hne, hsup⟩ | h2
  · left
    refine ⟨hk1, ?_⟩
    have hadj : X.treeGraph.Adj α' (baseB X) :=
      ((puAmalgam.adj_baseB_iff_mulAut h.le α').2 ⟨ψ, rfl⟩).symm
    have hd : X.treeGraph.dist α' (baseA X) = 2 := by
      rw [SimpleGraph.dist_comm, hc.2.1, hb]
    have hgeo : geo X α' (baseA X) 1 = baseB X := by
      refine (eq_geo_one X hadj ?_).symm
      rw [hd, dist_eq_one_of_adj X (adj_baseA_baseB X).symm]
    rw [hgeo, puAmalgam.qv_baseB] at ht₁ ht₂
    obtain ⟨m₁, hm₁, rfl⟩ := ht₁
    obtain ⟨m₂, hm₂, rfl⟩ := ht₂
    have hm₁T : (m₁ : G) ∈ T := hm₁
    have hm₂T : (m₂ : G) ∈ T := hm₂
    refine ⟨m₁, hm₁T, m₂, hm₂T, ?_, ?_, ?_, ?_⟩
    · have := hrel _ (Or.inl rfl)
      rwa [hZα', relIndex_centralizer_imM h m₁ hψZM] at this
    · have := hrel _ (Or.inr rfl)
      rwa [hZα', relIndex_centralizer_imM h m₂ hψZM] at this
    · intro hmem
      apply hne
      rw [hQα', ← map_inv, ← map_mul, S33.ofA_mem_imM_iff]
      simpa using hmem
    · have hcl : Subgroup.closure ({(m₁ : G), (m₂ : G)} : Set G) ≤ M := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact m₁.2
        · exact m₂.2
      rw [hZα, hQα', ← S33.imM_closure_pair h m₁ m₂, ← S33.imM_sup h.le hZM hψQM,
        ← S33.imM_sup h.le hcl hψQM] at hsup
      refine le_antisymm ((imM_le_imM_iff h.le (sup_le hZM hψQM)).1 hsup.le)
        ((imM_le_imM_iff h.le (sup_le hcl hψQM)).1 hsup.ge)
  · right
    rw [hQα', hZα, S33.relIndex_imM h.le hZM] at h2
    exact h2

end CFSG.Quasithin.MS93.S36SP

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36 CFSG.Quasithin.MS93.S36SP

theorem s36Sp4Excl_of_end (h32 : S32) (hEnd : S36SpEnd) :
    S36Sp4Excl := by
  intro G _ _ M T L h hb hV α' hc _ hW
  have hXL : ⁅Xq M, L⁆ ≤ Uq M T L := (h32 G M T L h).2.1
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 2 := hc.2.1.trans hb
  have hadj1 : (puAmalgam h.le).treeGraph.Adj (baseA _)
      (geo (puAmalgam h.le) (baseA _) α' 1) := adj_geo_one _ (by omega)
  obtain ⟨g, hg, hgβ⟩ := exists_mem_stab_smul _ hadj1 (adj_baseA_baseB (puAmalgam h.le))
  have hg' : g • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp hg
  have hc'' : IsCritical (puAmalgam h.le) (baseA _) (g • α') := by
    have := (isCritical_smul _ g (baseA _) α').mpr hc
    rwa [hg'] at this
  have hgeo'' : geo (puAmalgam h.le) (baseA _) (g • α') 1 = baseB _ := by
    have := geo_smul (puAmalgam h.le) g (baseA _) α' 1
    rwa [hg', hgβ] at this
  have hd'' : (puAmalgam h.le).treeGraph.dist (baseA _) (g • α') = 2 := hc''.2.1.trans hb
  have hadjB : (puAmalgam h.le).treeGraph.Adj (baseB _) (g • α') := by
    have := adj_geo (puAmalgam h.le) (u := baseA _) (w := g • α') (i := 1) (by omega)
    rwa [hgeo'', geo_of_le _ (by omega)] at this
  obtain ⟨ψ, hψ⟩ := (puAmalgam.adj_baseB_iff_mulAut h.le (g • α')).mp hadjB
  have hcψ : IsCritical (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) := hψ ▸ hc''
  have hWψ : S33iiW h ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) :=
    hψ ▸ S33iiW_smul h hg' hW
  obtain ⟨hZψ, hψZ⟩ := not_le_of_isCritical_inr h ψ hcψ
  obtain ⟨hZψ', hψZ'⟩ := not_le_of_isCritical_inr h ψ⁻¹ (isCritical_inr_inv h ψ hcψ)
  have hZT := S36.Z0q_le_T h
  obtain ⟨k, hsp4, hcase⟩ := s33iiW_inr h hb ψ hcψ hWψ
  obtain ⟨d, hdk⟩ : ∃ d : SpFrame h, d.k = k := by
    rcases hsp4 with ⟨hk1, N, hA⟩ | ⟨hk2, F, _, _, α, hF, hsurj, hnat⟩
    · subst hk1
      obtain ⟨s, hsT, hsQ, hs⟩ : ∃ s ∈ T, s ∉ pCoreOf 2 M ∧
          (Subgroup.centralizer ({s} : Set G)).relIndex (Uq M T L) ≤ 2 := by
        rcases hcase with ⟨-, m₁, hm₁, m₂, hm₂, hc₁, -, -, -⟩ | h2
        · refine ⟨((ψ⁻¹ ⟨m₁, hm₁⟩ : ↥T) : G), (ψ⁻¹ ⟨m₁, hm₁⟩).2, ?_, ?_⟩ <;>
            have hcs := relIndex_centralizer_tImage ψ⁻¹ hm₁ (tImage_le ψ (Z0q M T)) <;>
            rw [S36SP.tImage_inv_tImage ψ hZT, hc₁] at hcs
          · intro hsQ
            have : Z0q M T ≤ Subgroup.centralizer ({((ψ⁻¹ ⟨m₁, hm₁⟩ : ↥T) : G)} : Set G) :=
              fun z hz => Subgroup.mem_centralizer_singleton_iff.2
                (Subgroup.mem_centralizer_iff.1 (h.pCoreOf_le_centralizer_Z0q hsQ) z hz)
            rw [Subgroup.relIndex_eq_one.2 this] at hcs
            exact absurd hcs (by norm_num)
          · rw [← hcs]
            exact Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le)
              Subgroup.index_ne_zero_of_finite
        · obtain ⟨s, hsZ, hsQ⟩ := Set.not_subset.1 hψZ
          refine ⟨s, tImage_le _ _ hsZ, hsQ, ?_⟩
          calc (Subgroup.centralizer ({s} : Set G)).relIndex (Uq M T L)
              ≤ (Subgroup.centralizer (tImage ψ (Z0q M T) : Set G)).relIndex (Uq M T L) :=
                Subgroup.relIndex_le_of_le_left
                  (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hsZ))
                  Subgroup.index_ne_zero_of_finite
            _ ≤ (tImage ψ (pCoreOf 2 M)).relIndex (Uq M T L) :=
                Subgroup.relIndex_le_of_le_left (tImage_pCoreOf_le_centralizer h ψ)
                  Subgroup.index_ne_zero_of_finite
            _ ≤ (tImage ψ (pCoreOf 2 M)).relIndex (Z0q M T) :=
                Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le)
                  Subgroup.index_ne_zero_of_finite
            _ = 2 := by rw [h2, pow_one]
      exact exists_spFrame_of_alt h hA hsT hsQ hs
    · exact exists_spFrame_of_sp4 h hk2 hF hsurj hnat
  have hidx : (tImage ψ (pCoreOf 2 M)).relIndex (Z0q M T) = 2 ^ d.k := by
    rcases hcase with ⟨hk1, m₁, hm₁, m₂, hm₂, hc₁, hc₂, h12, hsup⟩ | h2
    · exact (false_of_case_one d (hdk.trans hk1) ψ hV hXL hZψ' hm₁ hm₂ hc₁ hc₂ h12 hsup).elim
    · rw [hdk]
      exact h2
  have hidx₂ : (pCoreOf 2 M).relIndex (tImage ψ (Z0q M T)) ≤ 2 ^ d.k :=
    relIndex_le_of_idx' d hψZ hidx.le
  have hp' : PairHyp d ψ⁻¹ := by
    refine ⟨hV, hXL, hψZ', hZψ', ?_, ?_⟩
    · have := PairHyp.relIndex_tImage_inv_eq (χ := ψ⁻¹) h hZT
      rw [inv_inv] at this
      rw [← this]
      exact hidx
    · rw [PairHyp.relIndex_tImage_inv_eq (χ := ψ) h hZT]
      exact hidx₂
  have hp : PairHyp d ψ := by
    refine ⟨hV, hXL, hψZ, hZψ, ?_, hidx.le⟩
    rw [← PairHyp.relIndex_tImage_inv_eq (χ := ψ) h hZT]
    exact hp'.idx'_eq
  obtain ⟨Ym, hm⟩ := hp.endSide hp'
  have hp'' : PairHyp d ψ⁻¹⁻¹ := by
    rw [inv_inv]
    exact hp
  obtain ⟨Yp, hpY⟩ := hp'.endSide hp''
  rw [inv_inv] at hpY
  have hsp4' : IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) d.k := by
    rw [hdk]
    exact hsp4
  exact hEnd G M T L h d.k ψ Yp Ym (hp.endCommon hsp4') hpY hm

end CFSG.Quasithin.MS93
