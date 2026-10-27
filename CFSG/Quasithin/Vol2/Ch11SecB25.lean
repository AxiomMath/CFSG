module

public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Background.F7
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.Quasithin.Vol2.Ch11StatementsD

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem le_normalizer_of_commutator_le {A B : Subgroup G} (h : ⁅A, B⁆ ≤ B) :
    A ≤ Subgroup.normalizer (B : Set G) := by
  have key : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ B := h (Subgroup.commutator_mem_commutator ha hb)
    have e : a * b * a⁻¹ = a * b * a⁻¹ * b⁻¹ * b := by group
    rw [e]
    exact B.mul_mem hc hb
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key a ha b, fun hb => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hb
  simpa [mul_assoc] using this

omit [Finite G] in
theorem weakClosureW0_le_wClos (T V : Subgroup G) : weakClosureW0 T V ≤ E3.wClos V 0 T := by
  refine iSup₂_le fun g hg => ?_
  have e : conjSub g V = conjSubgroup V g⁻¹ := by
    ext x
    rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
  refine E3.le_wClos ⟨hg, g⁻¹, by rw [e], ?_⟩
  rw [e]
  exact E3.mQuot_self _

theorem amalgamHypV_of (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hyp : Hyp11 G T L I n) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G)) :
    AmalgamHypV ((L ⊔ T) ⊔ H) (L ⊔ T) H T (fsuV T I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVLT, hred, hO⟩ := h3228 G T L I hyp.fsu
  rw [SecA.fsuL0_eq hyp] at hVLT hred hO
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le (SecA.L_le_normalizer_fsuV hyp) (SecA.T_le_normalizer_fsuV T I)
  have hVO : fsuV T I ≤ pCoreOf 2 (L ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVLT hLTV (SecA.isPGroup_fsuV hyp)
  have hO1 : pCoreOf 2 (L ⊔ T) ≠ ⊥ := fun h => SecA.fsuV_ne_bot hyp (le_bot_iff.1 (h ▸ hVO))
  refine ⟨⟨rfl, charTwo_of_inH hyp.fsu.qtke.2.1 (hyp.fsu.sylow.1.toSylow hyp.fsu.sylow.2)
      ⟨le_sup_right, hO1⟩, isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right,
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1, ?_⟩,
    isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨hVLT, hred⟩, ?_⟩
  · by_contra hne
    have hN : (L ⊔ T) ⊔ H ≤ Subgroup.normalizer (pCoreOf 2 ((L ⊔ T) ⊔ H) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
    exact hHM ((le_sup_right.trans hN).trans (SecA.normalizer_le_of_isPGroup h331 hyp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) hne (le_sup_left.trans hN)))
  · rw [← hO]
    have hCN : L ⊔ T ≤ Subgroup.normalizer
        (((L ⊔ T) ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) :=
      B2F.le_normalizer_inf Subgroup.le_normalizer (B2F.le_normalizer_centralizer hLTV)
    refine le_antisymm ?_ (F7.pCoreOf_mono_of_le_normalizer inf_le_left hCN)
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hO ▸ inf_le_right)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)

theorem exists_conj_commutator (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (hyp : Hyp11 G T L I n) {H : Subgroup G} (hH : InH T H)
    (hHM : ¬ H ≤ Subgroup.normalizer (L : Set G))
    (hW : E3.wClos (fsuV T I) 0 T ≤ pCoreOf 2 H) :
    ∃ g : G, conjSubgroup (fsuV T I) g ≤ T ∧ ⁅fsuV T I, conjSubgroup (fsuV T I) g⁆ ≠ ⊥ ∧
      fsuV T I ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
  have hamal := amalgamHypV_of h331 h3228 hyp hH hHM
  have hV1 := SecA.fsuV_ne_bot hyp
  have hb := even_critDist_of_weakClosureW0_le_G₂ hamal hV1
    ((weakClosureW0_le_wClos T (fsuV T I)).trans hW)
  obtain ⟨γ, hγ, hVγ⟩ := exists_dist_eq_critDist_not_le hamal hV1
  have hc := commutator_V_Vv_of_even hamal hV1 hb hγ hVγ
  obtain ⟨x, rfl⟩ := exists_smul_eq_γ₀ (vtype_eq_false_of_even hamal.gen (by rw [hγ]; exact hb))
  rw [Vv_smul_γ₀ hamal.normalizes] at hc
  obtain ⟨hne, hcl, hLT, -⟩ := hc
  have hVx2 : IsPGroup 2 (conjSub (x : G) (fsuV T I)) :=
    (SecA.isPGroup_fsuV hyp).map (MulAut.conj (x : G)).toMonoidHom
  obtain ⟨h, hh, hle⟩ := E3.exists_le_conj_of_isSylowIn
    (isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (le_sup_right : T ≤ L ⊔ T)) hLT hVx2
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le (SecA.L_le_normalizer_fsuV hyp) (SecA.T_le_normalizer_fsuV T I)
  have e1 : conjSub (x : G) (fsuV T I) = conjSubgroup (fsuV T I) (x : G)⁻¹ := by
    ext y
    rw [mem_conjSub, mem_conjSubgroup_iff, inv_inv]
  have e2 : conjSubgroup (fsuV T I) h⁻¹ = fsuV T I :=
    conjSubgroup_eq_iff_mem_normalizer.2 (hLTV (inv_mem hh))
  refine ⟨(x : G)⁻¹ * h⁻¹, ?_, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup, ← e1]
    intro y hy
    rw [mem_conjSubgroup_iff] at hy
    have := hle hy
    rw [mem_conjSubgroup_iff] at this
    simpa [mul_assoc] using this
  · rw [← conjSubgroup_conjSubgroup, ← e1]
    intro hbot
    apply hne
    have h1 := E3.conjSubgroup_commutator (fsuV T I) (conjSub (x : G) (fsuV T I)) h⁻¹
    rw [e2, hbot] at h1
    have h2 := congrArg (fun K => conjSubgroup K h) h1
    simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h2
    rw [h2]
    ext y
    simp [mem_conjSubgroup_iff]
  · rw [← conjSubgroup_conjSubgroup, ← e1]
    have hN : fsuV T I ≤ Subgroup.normalizer (conjSub (x : G) (fsuV T I) : Set G) :=
      le_normalizer_of_commutator_le (hcl.trans inf_le_right)
    intro v hv
    have hv' : h⁻¹ * v * h⁻¹⁻¹ ∈ fsuV T I :=
      ((Subgroup.mem_normalizer_iff.1 (hLTV (inv_mem hh))) v).1 hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have := (Subgroup.mem_normalizer_iff.1 (hN hv')) (h⁻¹ * y * h⁻¹⁻¹)
    rw [show h⁻¹ * (v * y * v⁻¹) * h⁻¹⁻¹ =
      (h⁻¹ * v * h⁻¹⁻¹) * (h⁻¹ * y * h⁻¹⁻¹) * (h⁻¹ * v * h⁻¹⁻¹)⁻¹ by group]
    exact this

theorem stmt11_2_5_of (h331 : Stmt3_3_1) (h3228 : Ch10.TmpL6_3_2_2_eight)
    (h1124 : Stmt11_2_4) : Stmt11_2_5 := by
  intro G _ _ T L I n V₁ V₂ H hyp hV₁ hV₂ hH hHM hsl3
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨hW, hab⟩ := hcon
  obtain ⟨g, hgT, hne, hN⟩ := exists_conj_commutator h331 h3228 hyp hH hHM hW
  have hgW : conjSubgroup (fsuV T I) g ≤ E3.wClos (fsuV T I) 0 T :=
    E3.le_wClos ⟨hgT, g, le_rfl, E3.mQuot_self _⟩
  have hVW : ⁅fsuV T I, E3.wClos (fsuV T I) 0 T⁆ ≠ ⊥ := fun hbot =>
    hne (le_bot_iff.1 (hbot ▸ Subgroup.commutator_mono le_rfl hgW))
  exact (h1124 G T L I n V₁ V₂ hyp hV₁ hV₂ hab hVW hsl3).2.1 g hgT hne hN

end CFSG.Quasithin.Vol2.Ch11.SecB
