module

public import CFSG.Quasithin.Vol2.Ch11SecA15Q
public import CFSG.Quasithin.Vol2.Ch11SecA15R1b
public import CFSG.Quasithin.Vol2.Ch11SecAKind

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem mem_V1_of_fixed_pCoreOf (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {w : G} (hw : w ∈ fsuV T I)
    (hfix : ∀ r ∈ pCoreOf 2 (LOf L V₁), r * w * r⁻¹ = w) : w ∈ V₁ := by
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
    exact hfix _ hk
  rw [h1, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem mem_V1_of_fixed_inf (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {w : G} (hw : w ∈ fsuV T I)
    (hfix : ∀ t ∈ T ⊓ L, t * w * t⁻¹ = w) : w ∈ V₁ :=
  mem_V1_of_fixed_pCoreOf hF h1102 h hU hw fun r hr =>
    hfix r ⟨ROf_le_T h (pCoreOf_lOf_le_ROf h hU hr),
      lOf_le_L (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr)⟩

theorem ROf_le_centralizer_V1 (hF : Facts15) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) (hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    ROf T L V₁ ≤ Subgroup.centralizer (V₁ : Set G) := by
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have huV := IsVi.le_fsuV hU hu
  have hrV : r ∈ Subgroup.normalizer (fsuV T I : Set G) := T_le_normalizer_fsuV T I (ROf_le_T h hr)
  have h1 : r * u * r⁻¹ * u⁻¹ ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hrV u).mp huV) (Subgroup.inv_mem _ huV),
      ROf_act_V1 hF h1102 h hU hr hu⟩
  rw [hCV, Subgroup.mem_bot] at h1
  calc u * r = (r * u * r⁻¹ * u⁻¹)⁻¹ * r * u := by group
    _ = r * u := by rw [h1, inv_one, one_mul]

theorem S_le_centralizer_V1 (hF : Facts15) (hF11 : Facts11) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    T ⊓ (L ⊔ ROf T L V₁) ≤ Subgroup.centralizer (V₁ : Set G) :=
  (inf_msG0_le h).trans (sup_le ((inf_L_le_lOf_sup_ROf hF h1102 h hU).trans
    (sup_le (lOf_one_le_centralizer hF11 h1102 h hU) (ROf_le_centralizer_V1 hF h1102 h hU hCV)))
    (ROf_le_centralizer_V1 hF h1102 h hU hCV))

theorem V1_le_omegaOneCenter (hF : Facts15) (hF11 : Facts11) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    V₁ ≤ omegaOneCenterOf (T ⊓ (L ⊔ ROf T L V₁)) := by
  intro u hu
  have huV := IsVi.le_fsuV hU hu
  refine Subgroup.subset_closure ⟨⟨⟨fsuV_le_T h huV, Subgroup.mem_sup_left (fsuV_le_L h1102 h huV)⟩,
    Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩, (isElemAbelian_fsuV h).2 u huV⟩
  exact (Subgroup.mem_centralizer_iff.mp (S_le_centralizer_V1 hF hF11 h1102 h hU hCV hs) u hu).symm

theorem sl3_realization (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hk : KindSL3 L (fsuV T I) n) :
    ∃ _ : IsMulCommutative ↥(fsuV T I),
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))),
      Nat.card K = 2 ^ n ∧
      (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
        ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π := by
  have hn : 2 ≤ n := h.one_lt
  obtain ⟨hc, -, -, -, hk'⟩ := h1102 G T L I n h
  refine ⟨hc, ?_⟩
  rcases hk' with ⟨K, _, _, hK, -, π, hπ, -⟩ | ⟨K, _, _, hK, he, -⟩ | ⟨K, _, _, hK, he, -⟩
  · exact ⟨K, inferInstance, inferInstance, π, hK, hπ⟩
  · exact (kind_not_SL3_Sp4 (by omega) hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim
  · exact (kind_not_SL3_G2 hG2 hn hk ⟨K, inferInstance, inferInstance, hK, he⟩).elim

theorem mem_lOf_sup_of_centralizes (hF : Facts15) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n) {l : G} (hl : l ∈ L) (hc : ∀ u ∈ V₁, l * u * l⁻¹ = u) :
    l ∈ LOf L V₁ ⊔ ROf T L V₁ := by
  obtain ⟨_, K, _, _, π, hK, hπ⟩ := sl3_realization hG2 h1102 h hk
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hlV : l ∈ Subgroup.normalizer (fsuV T I : Set G) := L_le_normalizer_fsuV h hl
  have hmem := hF.pointCentSL3 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _
    (isFlagW_of_isVi h hU) (conjV _ l hlV) (conjV_mem_autOn hl hlV) (fun u hu => by
      have : (conjV _ l hlV u : ↥(fsuV T I)) = u := by
        apply Subtype.ext
        rw [conjV_apply_coe]
        exact hc u hu
      rw [this, mul_inv_cancel]
      exact Subgroup.one_mem _)
  rw [← autOn_lOf_eq h hU, mem_autOn_iff] at hmem
  obtain ⟨l₁, hl₁, hl₁V, he⟩ := hmem
  have hk1 : l₁⁻¹ * l ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem (lOf_le_L hl₁)) hl, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) he
    simp only [conjV_apply_coe] at h1
    calc v * (l₁⁻¹ * l) = l₁⁻¹ * (l₁ * v * l₁⁻¹) * l := by group
      _ = l₁⁻¹ * (l * v * l⁻¹) * l := by rw [h1]
      _ = l₁⁻¹ * l * v := by group
  rw [centralizer_eq_pCoreOf h1102 h] at hk1
  have : l = l₁ * (l₁⁻¹ * l) := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl₁)
    (Subgroup.mem_sup_right (pCoreOf_le_ROf h hk1))

theorem msG0_inf_centralizer_le (hF : Facts15) (hG2 : FactG2DerivedOrder)
    (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n) (hCV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    (L ⊔ ROf T L V₁) ⊓ Subgroup.centralizer (V₁ : Set G) ≤ LOf L V₁ ⊔ ROf T L V₁ := by
  rintro g ⟨hg, hgc⟩
  have hg' : g ∈ ((L ⊔ ROf T L V₁ : Subgroup G) : Set G) := hg
  rw [coe_msG0 h] at hg'
  obtain ⟨l, hl, r, hr, rfl⟩ := hg'
  have hrc := ROf_le_centralizer_V1 hF h1102 h hU hCV hr
  have hlc : ∀ u ∈ V₁, l * u * l⁻¹ = u := by
    intro u hu
    have h1 := Subgroup.mem_centralizer_iff.mp hgc u hu
    have h2 := Subgroup.mem_centralizer_iff.mp hrc u hu
    calc l * u * l⁻¹ = (l * r) * (r⁻¹ * u * r) * (l * r)⁻¹ := by group
      _ = (l * r) * u * (l * r)⁻¹ := by
          rw [show r⁻¹ * u * r = u from by
            calc r⁻¹ * u * r = r⁻¹ * (u * r) := by group
              _ = r⁻¹ * (r * u) := by rw [h2]
              _ = u := by group]
      _ = u := by
          calc (l * r) * u * (l * r)⁻¹ = (u * (l * r)) * (l * r)⁻¹ := by rw [h1]
            _ = u := by group
  exact Subgroup.mul_mem _ (mem_lOf_sup_of_centralizes hF hG2 h1102 h hU hk hl hlc)
    (Subgroup.mem_sup_right hr)

end CFSG.Quasithin.Vol2.Ch11.SecA
