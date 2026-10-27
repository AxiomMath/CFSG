module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFitting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.UC22Main1
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.GroupTheory.SylowNormalElements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TIFusion

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Data

theorem mem_centralizer_Z_of_two_element (D : Data G)
    (hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G)) {x : G} (hxM : x ∈ D.M)
    {k : ℕ} (hx : orderOf x = 2 ^ k) :
    x ∈ Subgroup.centralizer (D.Z : Set G) := by
  let K : Subgroup G := D.M ⊓ Subgroup.centralizer (D.Z : Set G)
  have hK_le_M : K ≤ D.M := inf_le_left
  have hM_le_normC : D.M ≤ Subgroup.normalizer
      (Subgroup.centralizer (D.Z : Set G) : Set G) :=
    hMZ.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer D.Z)
  have hM_le_normK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf Subgroup.le_normalizer hM_le_normC).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hK_normal : (K.subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_M).2 hM_le_normK
  have hT_le_K : D.T ≤ K :=
    le_inf D.sylowM.le (uc22main1_T_le_centralizer D)
  have hxK : x ∈ K :=
    CFSG.GroupTheory.mem_of_normal_of_isSylowOf hK_normal D.sylowM hT_le_K hxM hx
  exact hxK.2

end Data

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)

theorem V_le_pCoreOf_N (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    c.V ≤ CFSG.Open.pCoreOf 2 c.N := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hUe : IsElemAbelian 2 D.U :=
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2
  have hZe : IsElemAbelian 2 D.Z := hUZ ▸ hUe
  have hSylOfN : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N :=
    D.sylowG.of_le (Ctx23L.N_mem_calMOf_T c).2 le_top
  have hZdata := CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T
  have hZT : D.Z ≤ D.T := fun z hz => (Subgroup.mem_inf.mp (hZdata hz)).1
  have hZC : D.Z ≤ Subgroup.centralizer (D.T : Set G) :=
    fun z hz => (Subgroup.mem_inf.mp (hZdata hz)).2
  have hNmax : rankThreeIsMaxTwoLocal c.N := (Ctx23L.N_mem_calMOf_T c).1
  have h := CFSG.LocalAnalysis.RankThreeUC.iSup_conj_le_pCoreOf_inf_centralizer
    D.standing.charTwo hNmax.1 hSylOfN hZT hZC
  have hV : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Ctx23L.V]
    exact uc22br4_conjClosure_eq c.N D.Z
  rw [hV]
  exact fun x hx => (h hx).1

theorem isElemAbelian_V (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    IsElemAbelian 2 c.V := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hZe : IsElemAbelian 2 D.Z := hUZ ▸
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2
  have hSylOfN : CFSG.ABGLocalTools.IsSylowOf 2 D.T c.N :=
    D.sylowG.of_le (Ctx23L.N_mem_calMOf_T c).2 le_top
  have hZdata := CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T
  have hZT : D.Z ≤ D.T := fun z hz => (Subgroup.mem_inf.mp (hZdata hz)).1
  have hZC : D.Z ≤ Subgroup.centralizer (D.T : Set G) :=
    fun z hz => (Subgroup.mem_inf.mp (hZdata hz)).2
  have hNmax : rankThreeIsMaxTwoLocal c.N := (Ctx23L.N_mem_calMOf_T c).1
  have hV : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Ctx23L.V]
    exact uc22br4_conjClosure_eq c.N D.Z
  rw [hV]
  exact CFSG.LocalAnalysis.RankThreeUC.isElemAbelian_iSup_conj D.standing.charTwo
    hNmax.1 hSylOfN hZT hZC hZe

theorem V_le_T (h4 : S23_4 D Ch) (h1930 : H1930 D) : c.V ≤ D.T :=
  (c.V_le_pCoreOf_N h4 h1930).trans
    (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp
        (D.sylowG.of_le (Ctx23L.N_mem_calMOf_T c).2 le_top)))

theorem V_ne_bot (h4 : S23_4 D Ch) (h1930 : H1930 D) : c.V ≠ ⊥ := by
  intro hV
  have hZ : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  exact uc22main1_Z_ne_bot D (le_bot_iff.mp (hV ▸ hZ))

theorem normalizer_V_eq (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    Subgroup.normalizer (c.V : Set G) = c.N := by
  have hNmax : rankThreeIsMaxTwoLocal c.N := (Ctx23L.N_mem_calMOf_T c).1
  have hNnorm : c.N ≤ Subgroup.normalizer (c.V : Set G) :=
    uc22p22v_le_normalizer_conjClosure c.N D.Z
  exact CFSG.LocalAnalysis.RankThreeUC.normalizer_eq_of_isMaxTwoLocal hNmax
    (c.V_ne_bot h4 h1930)
    (CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_V h4 h1930)) hNnorm

theorem centralizer_V_le_N (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    Subgroup.centralizer (c.V : Set G) ≤ c.N :=
  (Subgroup.centralizer_le_normalizer (c.V : Set G)).trans
    (le_of_eq (c.normalizer_V_eq h4 h1930))

theorem E_le_pCoreOf_M (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    c.E ≤ CFSG.Open.pCoreOf 2 D.M :=
  ((h39 h1930 c).2).1

theorem isMulCommutative_E (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    IsMulCommutative c.E :=
  (h39 h1930 c).1

theorem E_le_T (h39 : S23_39 D Ch) (h1930 : H1930 D) : c.E ≤ D.T :=
  (c.E_le_pCoreOf_M h39 h1930).trans
    (CFSG.Quasithin.E1.pCoreOf_two_le_of_isSylowIn
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM))

theorem isElemAbelian_E (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    IsElemAbelian 2 c.E := by
  have hV2 : ∀ v ∈ c.V, v ^ 2 = 1 := (c.isElemAbelian_V h4 h1930).2
  have hcomm := c.isMulCommutative_E h39 h1930
  have hEeq : c.E = ⨆ m : ↥D.M, c.V.map (MulAut.conj (m : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  rw [hEeq, Subgroup.iSup_eq_closure]
  refine CFSG.Quasithin.B2F.isElemAbelian_closure ?_ ?_
  · intro a ha b hb
    obtain ⟨m, hma⟩ := Set.mem_iUnion.1 ha
    obtain ⟨n, hnb⟩ := Set.mem_iUnion.1 hb
    have haE : a ∈ c.E := by
      rw [hEeq]
      exact Subgroup.mem_iSup_of_mem m hma
    have hbE : b ∈ c.E := by
      rw [hEeq]
      exact Subgroup.mem_iSup_of_mem n hnb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, haE⟩ ⟨b, hbE⟩)
  · intro a ha
    obtain ⟨m, hma⟩ := Set.mem_iUnion.1 ha
    obtain ⟨v, hv, rfl⟩ := hma
    show ((MulAut.conj (m : G)) v) ^ 2 = 1
    have hv2 : (v : G) ^ 2 = 1 := hV2 v hv
    rw [← map_pow, hv2, map_one]

theorem E_ne_bot (h4 : S23_4 D Ch) (h1930 : H1930 D) : c.E ≠ ⊥ := by
  intro hE
  have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
  have hVE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  exact uc22main1_Z_ne_bot D (le_bot_iff.mp (hE ▸ (hZV.trans hVE)))

theorem normalizer_E_eq (h4 : S23_4 D Ch) (h39 : S23_39 D Ch) (h1930 : H1930 D) :
    Subgroup.normalizer (c.E : Set G) = D.M :=
  CFSG.LocalAnalysis.RankThreeUC.normalizer_eq_of_isMaxTwoLocal D.maxLocal
    (c.E_ne_bot h4 h1930)
    (CFSG.Open.IsElemAbelian.isPGroup (c.isElemAbelian_E h4 h39 h1930))
    (uc22p22v_le_normalizer_conjClosure D.M c.V)

include c in
theorem isElemAbelian_Z (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    IsElemAbelian 2 D.Z :=
  (h4 h1930 c).1 ▸
    (CFSG.LocalAnalysis.RankThreeUC.uCore_le_and_isElemAbelian D.standing.charTwo
      D.maxLocal.1 D.sylowM).2

include c in
theorem Z_le_pCoreOf_M (h4 : S23_4 D Ch) (h1930 : H1930 D) :
    D.Z ≤ CFSG.Open.pCoreOf 2 D.M := by
  obtain ⟨hUZ, hUM, hMN⟩ := h4 h1930 c
  have hMZN : D.M ≤ normalizer (D.Z : Set G) := by simpa [hUZ] using hMN
  refine uc22main1_le_pCoreOf (by simpa [hUZ] using hUM)
    (D.sylowM.isPGroup.to_le (uc22main1_Z_le_T D)) fun m hm z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hMZN hm) z).1 hz

include c in
theorem Z_right_TI (h4 : S23_4 D Ch) (h1930 : H1930 D) (g : G) :
    D.Z ⊓ CFSG.Quasithin.conjSubgroup D.Z g = ⊥ ∨
      CFSG.Quasithin.conjSubgroup D.Z g = D.Z := by
  have hUZ : D.U = D.Z := (h4 h1930 c).1
  have hTI : CFSG.CGT.Timmesfeld75.IsTI D.Z := hUZ ▸ c.hTI
  have h := hTI g⁻¹
  simp only [CFSG.CGT.Timmesfeld75.conjSubgroup, CFSG.Quasithin.conjSubgroup] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h)
      (le_of_eq (CFSG.Quasithin.E3.card_conjSubgroup D.Z g))).symm

include c in
theorem conjSubgroup_TI (h4 : S23_4 D Ch) (h1930 : H1930 D) (k g : G) :
    CFSG.Quasithin.conjSubgroup D.Z k ⊓
        CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) g ≠ ⊥ →
      CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) g =
        CFSG.Quasithin.conjSubgroup D.Z k := by
  intro hne
  have hTI := c.Z_right_TI h4 h1930 (k*g*k⁻¹)
  have hfac : CFSG.Quasithin.conjSubgroup D.Z k ⊓
      CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) g =
      CFSG.Quasithin.conjSubgroup
        (D.Z ⊓ CFSG.Quasithin.conjSubgroup D.Z (k*g*k⁻¹)) k := by
    rw [show CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) g =
        CFSG.Quasithin.conjSubgroup
          (CFSG.Quasithin.conjSubgroup D.Z (k*g*k⁻¹)) k from by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup,
        CFSG.Quasithin.conjSubgroup_conjSubgroup]
      congr 1
      group]
    rw [← CFSG.Quasithin.E3.conjSubgroup_inf]
  have hinner : D.Z ⊓ CFSG.Quasithin.conjSubgroup D.Z (k*g*k⁻¹) ≠ ⊥ := by
    intro h
    apply hne
    rw [hfac, h, CFSG.Quasithin.E3.conjSubgroup_bot]
  have hinner_eq : D.Z ⊓ CFSG.Quasithin.conjSubgroup D.Z (k*g*k⁻¹) = D.Z := by
    rcases hTI with h | h
    · exact absurd h hinner
    · exact inf_eq_left.mpr (le_of_eq h.symm)
  have hleft : CFSG.Quasithin.conjSubgroup D.Z k ⊓
      CFSG.Quasithin.conjSubgroup D.Z (k*g) =
      CFSG.Quasithin.conjSubgroup D.Z k := by
    rw [show CFSG.Quasithin.conjSubgroup D.Z (k*g) =
        CFSG.Quasithin.conjSubgroup
          (CFSG.Quasithin.conjSubgroup D.Z k) g from by
      rw [CFSG.Quasithin.conjSubgroup_conjSubgroup]]
    rw [hfac, hinner_eq]
  have hle : CFSG.Quasithin.conjSubgroup D.Z k ≤
      CFSG.Quasithin.conjSubgroup D.Z (k*g) := inf_eq_left.mp hleft
  have hcard : Nat.card (CFSG.Quasithin.conjSubgroup D.Z (k*g)) =
      Nat.card (CFSG.Quasithin.conjSubgroup D.Z k) := by
    rw [CFSG.Quasithin.E3.card_conjSubgroup, CFSG.Quasithin.E3.card_conjSubgroup]
  have heq : CFSG.Quasithin.conjSubgroup D.Z k =
      CFSG.Quasithin.conjSubgroup D.Z (k*g) :=
    Subgroup.eq_of_le_of_card_ge hle hcard.le
  rw [CFSG.Quasithin.conjSubgroup_conjSubgroup (A := D.Z) (g := k) (h := g)]
  exact heq.symm

include c in
theorem conjSubgroup_twoElement_centralizes (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (k : G) {x : G}
    (hxN : x ∈ Subgroup.normalizer (CFSG.Quasithin.conjSubgroup D.Z k : Set G))
    (hx2 : ∃ j : ℕ, orderOf x = 2 ^ j) :
    ∀ y ∈ CFSG.Quasithin.conjSubgroup D.Z k, x * y * x⁻¹ = y := by
  have h4c := h4 h1930 c
  have hNGZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← h4c.1]
    exact D.normalizer_U_eq
  have hxEq : CFSG.Quasithin.conjSubgroup (CFSG.Quasithin.conjSubgroup D.Z k) x =
      CFSG.Quasithin.conjSubgroup D.Z k :=
    CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr hxN
  have hconj : CFSG.Quasithin.conjSubgroup D.Z (k*x*k⁻¹) = D.Z := by
    have h3 := congrArg (fun A : Subgroup G => CFSG.Quasithin.conjSubgroup A k⁻¹) hxEq
    simp only [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_assoc] at h3
    simpa [CFSG.Quasithin.conjSubgroup_one, mul_assoc] using h3
  have hyM : k * x * k⁻¹ ∈ D.M := by
    rw [← hNGZ]
    exact (CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer).mp hconj
  have hy2 : ∃ j : ℕ, orderOf (k*x*k⁻¹) = 2 ^ j := by
    obtain ⟨j, hj⟩ := hx2
    refine ⟨j, ?_⟩
    have hord : orderOf (k*x*k⁻¹) = orderOf x := by
      simpa [MulAut.conj_apply] using (MulAut.conj k).orderOf_eq x
    rw [hord, hj]
  have hMZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := h4c.1 ▸ h4c.2.2
  obtain ⟨j, hj⟩ := hy2
  have hycent : k*x*k⁻¹ ∈ Subgroup.centralizer (D.Z : Set G) :=
    D.mem_centralizer_Z_of_two_element hMZ hyM hj
  intro y hy
  have hz : k * y * k⁻¹ ∈ D.Z := CFSG.Quasithin.mem_conjSubgroup_iff.mp hy
  have hcomm := (Subgroup.mem_centralizer_iff.mp hycent) (k*y*k⁻¹) hz
  calc x * y * x⁻¹ =
      k⁻¹ * ((k*x*k⁻¹) * (k*y*k⁻¹) * (k*x*k⁻¹)⁻¹) * k := by group
    _ = k⁻¹ * (k*y*k⁻¹) * k := by rw [← hcomm]; group
    _ = y := by group

theorem E_span : c.E = ⨆ p : ↥D.M × ↥c.N,
    CFSG.Quasithin.conjSubgroup D.Z ((p.1 : G) * (p.2 : G))⁻¹ := by
  have hE_decomp : c.E = ⨆ m : ↥D.M, c.V.map (MulAut.conj (m : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  have hV_decomp : c.V = ⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom := by
    rw [Ctx23L.V]
    exact uc22br4_conjClosure_eq c.N D.Z
  calc c.E = ⨆ m : ↥D.M, c.V.map (MulAut.conj (m : G)).toMonoidHom := hE_decomp
    _ = ⨆ m : ↥D.M,
          (⨆ n : ↥c.N, D.Z.map (MulAut.conj (n : G)).toMonoidHom).map
            (MulAut.conj (m : G)).toMonoidHom := by rw [hV_decomp]
    _ = ⨆ m : ↥D.M, ⨆ n : ↥c.N,
          (D.Z.map (MulAut.conj (n : G)).toMonoidHom).map
            (MulAut.conj (m : G)).toMonoidHom := by
          simp_rw [Subgroup.map_iSup]
    _ = ⨆ p : ↥D.M × ↥c.N,
          CFSG.Quasithin.conjSubgroup D.Z ((p.1 : G) * (p.2 : G))⁻¹ := by
          rw [iSup_prod]
          refine iSup_congr fun m => iSup_congr fun n => ?_
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc]

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
