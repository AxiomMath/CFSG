module

public import CFSG.Quasithin.EmptyFaithful.S146zUAMod
public import CFSG.Quasithin.EmptyFaithful.S146zHOfour
public import CFSG.Quasithin.Background.F918P3

public section

namespace CFSG.Quasithin.S146zU.UD3

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
  CFSG.Quasithin.C1Pack
open scoped commutatorElement

section Rot

variable {G : Type} [Group G] [Finite G] {T M H PQ H₀ H₁ H₂ : Subgroup G} {p : ℕ} {t : G}

theorem exists_comm_uHi (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ : ↥H₁ →* DihedralGroup p)
    (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a : ↥H₁}
    (ha : φ a = DihedralGroup.r 1) (haG : (a : G) ∈ mcOf T) {u : G} (hu : u ∈ uHi T M H H₁) :
    ∃ v ∈ uHi T M H H₁,
      u⁻¹ * ((a : G) * v * (a : G)⁻¹ * v⁻¹) ∈ quasithinOmegaOneCenter T := by
  classical
  have hG := UA.hypG S
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hU1 : uHi T M H H₁ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₁H).trans (conjClosure_mono le_rfl hHG)
  have hu' : u ∈ conjClosure (VZ T M) (mcOf T) := hU1 hu
  have hw : clsU hG hu' ∈ Wsub hG (uHi T M H H₁) := clsU_mem_Wsub hG hu' hu
  obtain ⟨w', hw', hww'⟩ := UA.exists_eq_mul_inv hG S hred h φ hker ha haG _ hw
  obtain ⟨v, hv', hvJ, rfl⟩ := exists_clsU_of_mem_Wsub hG hU1 hw'
  refine ⟨v, hvJ, ?_⟩
  have hconj : (a : G) * v * (a : G)⁻¹ ∈ conjClosure (VZ T M) (mcOf T) :=
    conj_mem_UH haG hv'
  have e : rhoH hG ⟨a, haG⟩ (clsU hG hv') * (clsU hG hv')⁻¹ =
      clsU hG ((conjClosure (VZ T M) (mcOf T)).mul_mem hconj
        ((conjClosure (VZ T M) (mcOf T)).inv_mem hv')) := by
    rw [rhoH_clsU, clsU_inv, clsU_mul]
  rw [e] at hww'
  exact (clsU_eq_iff hG hu' _).mp hww'

theorem tildeOf_uHi_le (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) (φ : ↥H₁ →* DihedralGroup p)
    (hker : ∀ y : ↥H₁, φ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a : ↥H₁}
    (ha : φ a = DihedralGroup.r 1) (haG : (a : G) ∈ mcOf T) {K : Subgroup G} (haK : (a : G) ∈ K) :
    tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₁) ≤
      tildeOf (quasithinOmegaOneCenter T) ⁅conjClosure (VZ T M) (mcOf T), K⁆ := by
  intro y hy
  obtain ⟨⟨u, huN⟩, huJ, rfl⟩ := mem_secImg.mp hy
  obtain ⟨v, hvJ, hv⟩ := exists_comm_uHi S hred h φ hker ha haG huJ
  have hHG : H ≤ mcOf T := S.le_mcOf hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hU1 : uHi T M H H₁ ≤ conjClosure (VZ T M) (mcOf T) :=
    (uHi_le_conjClosure hH₁H).trans (conjClosure_mono le_rfl hHG)
  have hvU : v ∈ conjClosure (VZ T M) (mcOf T) := hU1 hvJ
  have hNZ : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.normalizer_Z.ge
  have hUN : conjClosure (VZ T M) (mcOf T) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z S.isHTM_mcOf
  have hcN : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hNZ haG) (hUN hvU))
      (Subgroup.inv_mem _ (hNZ haG))) (Subgroup.inv_mem _ (hUN hvU))
  have hcmem : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈
      ⁅conjClosure (VZ T M) (mcOf T), K⁆ := by
    have h1 := Subgroup.commutator_mem_commutator hvU haK
    have e : (a : G) * v * (a : G)⁻¹ * v⁻¹ = (⁅v, (a : G)⁆)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hsec : secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
      (quasithinOmegaOneCenter T) ⟨u, huN⟩ =
      secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
        (quasithinOmegaOneCenter T) ⟨(a : G) * v * (a : G)⁻¹ * v⁻¹, hcN⟩ :=
    secMk_eq_secMk_iff.mpr hv
  rw [hsec]
  exact secMk_mem_secImg (A := Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
    (B := quasithinOmegaOneCenter T) (x := ⟨_, hcN⟩) hcmem

theorem card_tildeOf_uHi (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) {Hi : Subgroup G}
    (hHi : Hi ≤ H) {k : ℕ} (hk : mIdx (uHi T M H Hi) (quasithinOmegaOneCenter T) = k) :
    Nat.card ↥(tildeOf (quasithinOmegaOneCenter T) (uHi T M H Hi)) = 2 ^ k := by
  have hH : IsHTM T M H := hred.isHTM
  have hi₁ : uHi T M H Hi ≤ conjClosure (VZ T M) H := uHi_le_conjClosure hHi
  have hUZ : conjClosure (VZ T M) H ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    S.conjClosure_le_normalizer_Z hH
  have hUp : IsPGroup 2 (conjClosure (VZ T M) H) :=
    isPGroup_of_isElemAbelian (S.lemma_14_5_15_two hH)
  rw [card_tildeOf_eq_relIndex (Z_le_uHi T M H Hi) (hi₁.trans hUZ),
    HypF98.relIndex_eq_two_pow_mIdx (hUp.to_le hi₁), hk]

omit [Finite G] in
theorem tildeOf_uHi_inf_eq_bot (h : IsDecP T M H p H₀ H₁ H₂ t) :
    tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₁) ⊓
      tildeOf (quasithinOmegaOneCenter T) (uHi T M H H₂) = ⊥ := by
  rw [← tildeOf_inf (Z_le_uHi T M H H₁), h.dir_inf]
  exact tildeOf_eq_bot_of_le le_rfl

theorem comm_mem_of_mem_pCoreOf (S : Setting146 G T M) (hred : IsRedCE T M H PQ p)
    {Hi : Subgroup G} (hHi : Hi ≤ H) {x u : G} (hx : x ∈ pCoreOf 2 H) (hu : u ∈ uHi T M H Hi) :
    x * u * x⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
  have h91 := (S.lemma_14_5_14 (S.isHz_iff.mpr hred.isHTM)).2.toHypF91
  have h1 := h91.commutator_conjClosure_le u (uHi_le_conjClosure hHi hu) x hx
  have h2 := (quasithinOmegaOneCenter T).inv_mem h1
  rwa [show (u * x * u⁻¹ * x⁻¹)⁻¹ = x * u * x⁻¹ * u⁻¹ by group] at h2

end Rot

section Act

variable {G : Type} [Group G] {V₁ IH H' : Subgroup G}

theorem actH_fix_of_comm (hV₁ : H' ≤ Subgroup.normalizer (V₁ : Set G))
    (hIH : H' ≤ Subgroup.normalizer (IH : Set G)) (x : ↥H') {u : G}
    (hu : u ∈ Subgroup.normalizer (V₁ : Set G)) (hc : (x : G) * u * (x : G)⁻¹ * u⁻¹ ∈ V₁)
    (w : ↥(tildeOf V₁ IH))
    (hw : (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨u, hu⟩) :
    actH hV₁ hIH x w = w := by
  apply Subtype.ext
  rw [actH_apply_coe, hw, ← map_inv, ← map_mul, ← map_mul, secMk_eq_secMk_iff]
  have h1 := (Subgroup.mem_normalizer_iff''.mp hu ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹).mp
    (V₁.inv_mem hc)
  have e : (u : G)⁻¹ * ((x : G) * u * (x : G)⁻¹ * u⁻¹)⁻¹ * u =
      ((x : G) * u * (x : G)⁻¹)⁻¹ * u := by group
  rw [e] at h1
  exact h1

end Act

end CFSG.Quasithin.S146zU.UD3
