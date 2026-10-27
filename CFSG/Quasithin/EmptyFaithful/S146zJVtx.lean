module

public import CFSG.Quasithin.EmptyFaithful.S146zJRef

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C1Pack
  CFSG.Quasithin.CosetGeom
open scoped commutatorElement Pointwise

section Vtx

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.mIdx_eq_one_of_le (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (hpos : 0 < mIdx (F8.Uγ (VZ T M) H (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hle : mIdx (conjClosure (VZ T M) H)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤
      mIdx (F8.Uγ (VZ T M) H (k : G)) (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hU1 : F8.Uγ (VZ T M) H (k : G) ≤ H₁) :
    mIdx (F8.Uγ (VZ T M) H (k : G)) (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) = 1 ∧
      mIdx (conjClosure (VZ T M) H)
        (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) = 1 := by
  have hH : IsHTM T M H := hred.isHTM
  have hp : p.Prime := hred.prime
  have hp2 : p ≠ 2 := hred.odd
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have hUab := h98.isElemAbelian_Uγ (g := k)
  have h1 := h.relIndex_inf_pCore_le_two hp hp2 hU1 hUab
  rw [← h98.Dγ_eq_inf_pCoreOf sk] at h1
  have hm1 : mIdx (F8.Uγ (VZ T M) H (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤ 1 := by
    unfold mIdx
    exact padicValNat_two_le_one (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h1
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hpos2 : 0 < mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) :=
    mIdx_pos_of_lt_of_isPGroup hUp (h98.lemma_14_5_17 sk)
  constructor <;> omega

theorem Setting146.Z_le_DH (S : Setting146 G T M) (hH : IsHTM T M H)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sg : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g) :
    quasithinOmegaOneCenter T ≤ F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (g : G) := by
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have hHN : H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    (S.le_mcOf hH).trans S.normalizer_Z.ge
  have hHC : ∀ y ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, y * z = z * y := by
    intro y hy z hz
    have h1 := hHN hy
    rw [normalizer_eq_centralizer_of_card_eq_two S.card_Z] at h1
    exact (Subgroup.mem_centralizer_iff.mp h1 z hz).symm
  have hA₁H : F8.A₁ (quasithinOmegaOneCenter T) (g : G) ≤ H :=
    (h98.A₁_le_Uγ (g := g)).trans (h98.Uγ_le_H sg)
  intro z hz
  refine ⟨Z_le_conjClosure_VZ T M H hz, ?_, fun u hu => ?_⟩
  · rw [normalizer_eq_centralizer_of_card_eq_two (h98.card_A₁ (g := g))]
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hHC a (hA₁H ha) z hz
  · have h1 := hHC u (h98.Uγ_le_H sg hu) z hz
    have e : z * u * z⁻¹ * u⁻¹ = 1 := by
      rw [← h1]
      group
    rw [e]
    exact (F8.A₁ (quasithinOmegaOneCenter T) (g : G)).one_mem

theorem IsDecP.A₁_le_uHi (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t)
    (h8 : mIdx (uK T M H ⊔ quasithinOmegaOneCenter T) (quasithinOmegaOneCenter T) = 8)
    {δ δ' : F8.Geom T (yOfL22 T M) H} {k : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (sk : F8Setup T (VZ T M) (yOfL22 T M) H δ δ' k)
    (hpos : 0 < mIdx (F8.Uγ (VZ T M) H (k : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)))
    (hDH : mIdx (conjClosure (VZ T M) H)
      (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤ 1)
    (hU1 : F8.Uγ (VZ T M) H (k : G) ≤ H₁) :
    F8.A₁ (quasithinOmegaOneCenter T) (k : G) ≤ uHi T M H H₁ := by
  classical
  have hH : IsHTM T M H := hred.isHTM
  obtain ⟨-, h98⟩ := S.lemma_14_5_14 (S.isHz_iff.mpr hH)
  have h91 := h98.toHypF91
  have hcard : Nat.card (Wsub h91 (uHi T M H H₁)) = 16 :=
    h.card_Wsub_of_mIdx_eight S hred h91 h8
  obtain ⟨x, hx, hxQ⟩ : ∃ x ∈ F8.Uγ (VZ T M) H (k : G), x ∉ pCoreOf 2 H := by
    by_contra hall
    push Not at hall
    have hUD : F8.Uγ (VZ T M) H (k : G) ≤
        F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G) := by
      rw [h98.Dγ_eq_inf_pCoreOf sk]
      exact le_inf le_rfl hall
    have h1 : (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) H (k : G)).relIndex
        (F8.Uγ (VZ T M) H (k : G)) = 1 := Subgroup.relIndex_eq_one.mpr hUD
    unfold mIdx at hpos
    rw [h1] at hpos
    simp at hpos
  have hx₁ : x ∈ H₁ := hU1 hx
  have hx2 : x * x = 1 := by
    have := isElemAbelian_pow_eq_one (h98.isElemAbelian_Uγ (g := k)) hx
    simpa [pow_two] using this
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  have hidx : (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)).relIndex
      (conjClosure (VZ T M) H) ≤ 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp]
    calc 2 ^ mIdx (conjClosure (VZ T M) H)
          (F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G)) ≤ 2 ^ 1 :=
          Nat.pow_le_pow_right (by norm_num) hDH
      _ = 2 := by norm_num
  obtain ⟨d, ⟨hdD, hdU⟩, hne⟩ := h.exists_DH_inf_noncomm S hred h91 hcard hx₁ hxQ hx2
    (DH := F8.DH (VZ T M) (quasithinOmegaOneCenter T) H (k : G))
    (centralizerMod_le_left _ _ _) (S.Z_le_DH hH sk) hidx
  have hcA : x * d * x⁻¹ * d⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (k : G) := by
    have h1 := hdD.2.2 x hx
    have e : x * d * x⁻¹ * d⁻¹ = (d * x * d⁻¹ * x⁻¹)⁻¹ := by group
    rw [e]
    exact (F8.A₁ (quasithinOmegaOneCenter T) (k : G)).inv_mem h1
  have hcU : x * d * x⁻¹ * d⁻¹ ∈ uHi T M H H₁ := by
    have hxN := h.le_normalizer_uHi S hred hx₁
    have h1 := (Subgroup.mem_normalizer_iff.mp hxN d).mp hdU
    exact (uHi T M H H₁).mul_mem h1 ((uHi T M H H₁).inv_mem hdU)
  intro a ha
  rcases eq_one_or_eq_of_card_subgroup_two _ (h98.card_A₁ (g := k)) hcA hne ha with h1 | h1
  · rw [h1]
    exact (uHi T M H H₁).one_mem
  · rw [h1]
    exact hcU

end Vtx

section Trans

variable {G : Type} [Group G] [Finite G] {T V L V₁ H : Subgroup G}

theorem F8Setup.smul_T (h : HypF81 T V L V₁ H) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) {τ : ↥((L ⊔ T) ⊔ H)} (hτ : (τ : G) ∈ T) :
    F8Setup T V L H (τ • γ) (τ • γ') (τ * g) := by
  have hyp := h.amalgamHypV
  have hTT := hyp.T_le hτ
  have hτ0 : τ • F8.γ₀ T L H = F8.γ₀ T L H :=
    smul_eq_of_mem_stab (by rw [stab_γ₀ hyp.le₁]; exact hTT.1)
  have hτ1 : τ • F8.γ₁ T L H = F8.γ₁ T L H :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hyp.le₂]; exact hTT.2)
  have hVτ : conjSub (τ : G)⁻¹ V = V :=
    F7.conjSub_eq_of_mem_normalizer (hyp.normalizes ((L ⊔ T).inv_mem hTT.1))
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have h1 := dist_smul τ (F8.γ₀ T L H) γ
    rw [hτ0] at h1
    rw [h1]
    exact s.critical.dist_eq
  · intro hle
    apply s.critical.not_le
    rw [ballStab_smul, le_conjSub_iff, hVτ] at hle
    exact hle
  · have h1 := dist_smul τ (F8.γ₁ T L H) γ
    rw [hτ1] at h1
    rw [h1]
    exact s.critical.geodesic
  · exact (smul_adj τ).mpr s.nbr
  · have h1 := dist_smul τ (F8.γ₁ T L H) γ'
    rw [hτ1] at h1
    rw [h1]
    exact s.geodesic
  · rw [mul_smul, s.edge₀]
  · rw [mul_smul, s.edge₁]

end Trans

end CFSG.Quasithin
