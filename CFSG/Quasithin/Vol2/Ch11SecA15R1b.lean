module

public import CFSG.Quasithin.Vol2.Ch11SecA15R1
public import CFSG.Quasithin.Vol2.Ch11SecA15Aut

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem radical_facts (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) :
    ∃ _ : IsMulCommutative ↥(fsuV T I),
      RadicalFixes (autOn L (fsuV T I)) ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
          (V₁.subgroupOf (fsuV T I)) ∧
        RadicalPoint (autOn L (fsuV T I))
          ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I))
          (V₁.subgroupOf (fsuV T I)) := by
  have hflag := isFlagW_of_isVi h hU
  obtain ⟨hc, -, -, -, hk⟩ := h1102 G T L I n h
  refine ⟨hc, ?_⟩
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hn : 2 ≤ n := h.one_lt
  rcases hk with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨-, -, -, -, -, hG2⟩
  · exact ⟨hF.radFixSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag,
      hF.radPointSL3 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag⟩
  · exact ⟨hF.radFixSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag,
      hF.radPointSp4 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag⟩
  · obtain ⟨K, _, _, hK, π, hπ⟩ := hG2
    exact ⟨hF.radFixG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag,
      hF.radPointG2 K n hn hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _ hflag⟩

theorem autOn_lOf_eq (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) :
    autOn (LOf L V₁) (fsuV T I) =
      perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I))) := by
  rw [autOn_perfectCore (inf_le_left.trans (L_le_normalizer_fsuV h)),
    autOn_inf_normalizer (IsVi.le_fsuV hU)]

theorem isPGroup_lOf_inf_centralizer (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) :
    IsPGroup 2 ↥(LOf L V₁ ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  refine (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le ?_
  rw [← centralizer_eq_pCoreOf h1102 h]
  exact inf_le_inf_right _ lOf_le_L

theorem mem_V1_of_fixed (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {w : G} (hw : w ∈ fsuV T I)
    (hfix : ∀ r ∈ ROf T L V₁, r * w * r⁻¹ = w) : w ∈ V₁ := by
  obtain ⟨_, hRF, -⟩ := radical_facts hF h1102 h hU
  unfold RadicalFixes at hRF
  rw [← autOn_lOf_eq h hU] at hRF
  have hX : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    lOf_le_L.trans (L_le_normalizer_fsuV h)
  refine hRF ⟨w, hw⟩ fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := exists_mem_pCoreOf_of_mem_pCore hX
    (isPGroup_lOf_inf_centralizer h1102 h) hx
  have h1 : ((autOnHom' (fsuV T I) (LOf L V₁) hX k : MulAut ↥(fsuV T I)) ⟨w, hw⟩) = ⟨w, hw⟩ := by
    apply Subtype.ext
    rw [autOnHom'_coe, conjV_apply_coe]
    exact hfix _ (pCoreOf_lOf_le_ROf h hU hk)
  rw [h1, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem ROf_act_V1 (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {r : G} (hr : r ∈ ROf T L V₁) {u : G} (hu : u ∈ V₁) :
    r * u * r⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨_, -, hRP⟩ := radical_facts hF h1102 h hU
  unfold RadicalPoint at hRP
  rw [← autOn_lOf_eq h hU] at hRP
  have hLV := L_le_normalizer_fsuV h
  have hUV := IsVi.le_fsuV hU
  have hX : LOf L V₁ ≤ Subgroup.normalizer (fsuV T I : Set G) := lOf_le_L.trans hLV
  have hrT : r ∈ T := ROf_le_T h hr
  have hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G) := T_le_normalizer_fsuV T I hrT
  have hrL : r ∈ Subgroup.normalizer (L : Set G) := h.normal hrT
  have hrL₁ : r ∈ Subgroup.normalizer (LOf L V₁ : Set G) := T_le_normalizer_L1 h hU hrT
  have hconj : ∀ {x : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G)),
      conjV (fsuV T I) r hrV * conjV (fsuV T I) x hx * (conjV (fsuV T I) r hrV)⁻¹ =
        conjV (fsuV T I) (r * x * r⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hrV hx)
          (Subgroup.inv_mem _ hrV)) := by
    intro x hx
    rw [← conjV_inv _ hrV, ← conjV_mul, ← conjV_mul]
  have h1 : ∃ k : ℕ, conjV (fsuV T I) r hrV ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_ROf (T := T) (L := L) (V₁ := V₁) ⟨r, hr⟩
    refine ⟨k, ?_⟩
    have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    ext v
    have : ((conjV (fsuV T I) r hrV ^ 2 ^ k) v : G) = r ^ 2 ^ k * v * (r ^ 2 ^ k)⁻¹ := by
      clear hk hrk
      induction (2 ^ k) with
      | zero => simp
      | succ m ih => rw [pow_succ', MulAut.mul_apply, conjV_apply_coe, ih]; group
    rw [this, hrk]
    simp
  have hceq : ∀ {x y : G} (hx : x ∈ Subgroup.normalizer (fsuV T I : Set G))
      (hy : y ∈ Subgroup.normalizer (fsuV T I : Set G)), x = y →
      conjV (fsuV T I) x hx = conjV (fsuV T I) y hy := by
    intro x y hx hy hxy
    subst hxy
    rfl
  have h2 : conjV (fsuV T I) r hrV ∈
      stabW ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) := by
    rw [← inf_centralizer_subgroupOf, conjV_mem_stabW_iff inf_le_left hrV]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hrV, mem_normalizer_centralizer hrL⟩
  have h3 : ∀ x ∈ autOn L (fsuV T I),
      conjV (fsuV T I) r hrV * x * (conjV (fsuV T I) r hrV)⁻¹ ∈ autOn L (fsuV T I) := by
    intro x hx
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hx
    rw [hconj hlV]
    exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hrL l).mp hl) _
  have h4 : ∀ x ∈ autOn (LOf L V₁) (fsuV T I),
      conjV (fsuV T I) r hrV * x * (conjV (fsuV T I) r hrV)⁻¹ ∈ autOn (LOf L V₁) (fsuV T I) := by
    intro x hx
    obtain ⟨l, hl, hlV, rfl⟩ := mem_autOn_iff.mp hx
    rw [hconj hlV]
    exact conjV_mem_autOn ((Subgroup.mem_normalizer_iff.mp hrL₁ l).mp hl) _
  have h5 : ∀ x : ↥(autOn (LOf L V₁) (fsuV T I)), ∃ y : ↥(autOn (LOf L V₁) (fsuV T I)),
      y ∈ CFSG.pCore 2 ↥(autOn (LOf L V₁) (fsuV T I)) ∧
        conjV (fsuV T I) r hrV * (x : MulAut ↥(fsuV T I)) * (conjV (fsuV T I) r hrV)⁻¹ =
          (y : MulAut ↥(fsuV T I)) * x := by
    intro x
    obtain ⟨l, rfl⟩ := autOnHom'_surjective _ _ hX x
    have hk := commutator_lOf_ROf_mem h hU l.2 hr
    have hkL₁ : r * (l : G) * r⁻¹ * (l : G)⁻¹ ∈ LOf L V₁ :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ hk
    refine ⟨autOnHom' _ _ hX ⟨_, hkL₁⟩, conjV_mem_pCore_of_mem_pCoreOf hX hk, ?_⟩
    rw [autOnHom'_coe, autOnHom'_coe, hconj, ← conjV_mul]
    exact hceq _ _ (by group)
  have h6 := hRP _ h1 h2 h3 h4 h5 ⟨u, hUV hu⟩ hu
  rw [Subgroup.mem_subgroupOf] at h6
  simpa [conjV_apply_coe] using h6

end CFSG.Quasithin.Vol2.Ch11.SecA
