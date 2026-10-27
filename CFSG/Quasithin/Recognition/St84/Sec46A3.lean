module

public import CFSG.Quasithin.Recognition.St84.Sec46A2
public import CFSG.Quasithin.MS93.Sec2Gen
public import CFSG.Quasithin.Recognition.St84.Gen.Sec6Cover
public import CFSG.Quasithin.Recognition.St84.Gen.Sec46W1
public import CFSG.GroupTheory.GroupAction.CoprimeFiniteSubgroups
public import CFSG.Quasithin.Recognition.St84.Sec4Nat16Quot

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

private theorem le_dsConjClosure (Y U : Subgroup G) : U ≤ dsConjClosure Y U := by
  unfold dsConjClosure
  refine le_iSup₂_of_le (f := fun y (_ : y ∈ Y) => U.map (MulAut.conj y).toMonoidHom)
    (1 : G) (Subgroup.one_mem _) ?_
  simpa [conjSub] using (le_of_eq (conjSub_one U).symm)

private theorem dsConjClosure_le_of_le {Y U K : Subgroup G} (hUK : U ≤ K)
    (hYK : Y ≤ Subgroup.normalizer (K : Set G)) : dsConjClosure Y U ≤ K := by
  unfold dsConjClosure
  refine iSup₂_le fun g hg => ?_
  calc U.map (MulAut.conj g).toMonoidHom = conjSub g U := rfl
    _ ≤ conjSub g K := conjSub_mono g hUK
    _ = K := mem_normalizer_iff_conjSub.mp (hYK hg)

private theorem dsConjClosure_le_dsCentMod {L A Z T : Subgroup G} (hTL : T ≤ L)
    (hLA : L ≤ Subgroup.normalizer (A : Set G)) (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hTA : ⁅T, A⁆ ≤ Z) : dsConjClosure L T ≤ dsCentMod L A Z := by
  have hTC : T ≤ dsCentMod L A Z := fun z hz =>
    ⟨hTL hz, hLZ (hTL hz), fun a ha => Subgroup.commutator_le.mp hTA z hz a ha⟩
  unfold dsConjClosure
  refine iSup₂_le fun g hg => ?_
  intro z hz
  obtain ⟨z₀, hz₀, hzz₀⟩ := Subgroup.mem_map.mp hz
  rw [← hzz₀]
  change g * z₀ * g⁻¹ ∈ dsCentMod L A Z
  have hzgL : g * z₀ * g⁻¹ ∈ L := L.mul_mem (L.mul_mem hg (hTL hz₀)) (L.inv_mem hg)
  refine ⟨hzgL, hLZ hzgL, ?_⟩
  intro a ha
  have hginv : g⁻¹ ∈ Subgroup.normalizer (A : Set G) := Subgroup.inv_mem _ (hLA hg)
  have hga : g⁻¹ * a * g ∈ A := by
    have := (Subgroup.mem_normalizer_iff.mp hginv a).mp ha
    simpa using this
  have hzcomm : ⁅z₀, g⁻¹ * a * g⁆ ∈ Z := (hTC hz₀).2.2 _ hga
  have e : ⁅g * z₀ * g⁻¹, a⁆ = g * ⁅z₀, g⁻¹ * a * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hLZ hg) _).mp hzcomm

private theorem oTwoRes_le_dsConjClosure {L Q T : Subgroup G} (hQ : IsPGroup 2 Q)
    (hL : L = T ⊔ Q) : oTwoRes L ≤ dsConjClosure L T := by
  set M : Subgroup G := dsConjClosure L T
  have hQL : Q ≤ L := by rw [hL]; exact le_sup_right
  have hLNM : L ≤ Subgroup.normalizer (M : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_iSup_conj L T
  have hMQ : M ⊔ Q = L := by
    have hTL : T ≤ L := by rw [hL]; exact le_sup_left
    refine le_antisymm (sup_le (dsConjClosure_le_of_le hTL Subgroup.le_normalizer) hQL) ?_
    calc L = T ⊔ Q := hL
      _ ≤ M ⊔ Q := sup_le_sup_right (le_dsConjClosure L T) _
  rw [oTwoRes_eq_oTwoUpper]
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  exact CFSG.Quasithin.E1.exists_pow_mem_of_mem_sup hQ (hQL.trans hLNM)
    (by rw [hMQ]; exact hx)

private theorem Z_three_eq_sup_of_Z_one_eq (X : Setup Γ G)
    (hZ1eq : X.Z 1 = X.Z 0 ⊔ X.Z 2) : X.Z 3 = X.Z 2 ⊔ X.Z 4 := by
  calc X.Z 3 = conjSub (X.τ ^ (1 : ℤ)) (X.Z 1) := X.Z_add 1 1
    _ = conjSub (X.τ ^ (1 : ℤ)) (X.Z 0 ⊔ X.Z 2) := by rw [hZ1eq]
    _ = conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) ⊔ conjSub (X.τ ^ (1 : ℤ)) (X.Z 2) :=
        conjSub_sup _ _ _
    _ = X.Z 2 ⊔ X.Z 4 := by
        have h1 : conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) = X.Z 2 := by
          simpa using (X.Z_add 1 0).symm
        have h2 : conjSub (X.τ ^ (1 : ℤ)) (X.Z 2) = X.Z 4 := by
          simpa using (X.Z_add 1 2).symm
        rw [h1, h2]

private theorem Z_neg_one_eq_sup_of_Z_one_eq (X : Setup Γ G)
    (hZ1eq : X.Z 1 = X.Z 0 ⊔ X.Z 2) : X.Z (-1) = X.Z (-2) ⊔ X.Z 0 := by
  calc X.Z (-1) = X.Z (1 + 2 * (-1 : ℤ)) := by congr 1
    _ = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 1) := X.Z_add (-1) 1
    _ = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 0 ⊔ X.Z 2) := by rw [hZ1eq]
    _ = conjSub (X.τ ^ (-1 : ℤ)) (X.Z 0) ⊔ conjSub (X.τ ^ (-1 : ℤ)) (X.Z 2) :=
        conjSub_sup _ _ _
    _ = X.Z (-2) ⊔ X.Z 0 := by
        have h1 : conjSub (X.τ ^ (-1 : ℤ)) (X.Z 0) = X.Z (-2) := by
          simpa using (X.Z_add (-1) 0).symm
        have h2 : conjSub (X.τ ^ (-1 : ℤ)) (X.Z 2) = X.Z 0 := by
          simpa using (X.Z_add (-1) 2).symm
        rw [h1, h2]

private theorem Z_neg_one_le_iSup_conjSub (X : Setup Γ G) :
    X.Z (-1) ≤ ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1) := by
  have hadj : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    simpa using (X.adj (-1)).symm
  obtain ⟨s, hsL, hsv⟩ :=
    (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans (X.vert 1) (X.vert (-1)) (X.adj 0) hadj
  have hZs : X.Z (-1) = conjSub s (X.Z 1) := X.Z_smul X hsv
  rw [hZs]
  exact le_iSup₂_of_le s (X.L_le_Gi 0 hsL) le_rfl

private theorem sq_mem_of_gen {H : Type*} [Group H] {T : Set H} {V Z : Subgroup H}
    (hV : Subgroup.closure T = V) (hZc : ∀ c ∈ Z, ∀ x ∈ V, c * x = x * c)
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ ∈ Z) (hT : ∀ a ∈ T, a ^ 2 ∈ Z) :
    ∀ a ∈ V, a ^ 2 ∈ Z := by
  intro a ha
  rw [← hV] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact hT x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxV : x ∈ V := hV ▸ hx
    have hyV : y ∈ V := hV ▸ hy
    have hc : ⁅y⁻¹, x⁻¹⁆ ∈ Z := hcomm y⁻¹ (V.inv_mem hyV) x⁻¹ (V.inv_mem hxV)
    have hcy : ⁅y⁻¹, x⁻¹⁆ * y = y * ⁅y⁻¹, x⁻¹⁆ := hZc _ hc y hyV
    have hyx : y * x = x * y * ⁅y⁻¹, x⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have e : (x * y) ^ 2 = x ^ 2 * (⁅y⁻¹, x⁻¹⁆ * y ^ 2) := by
      calc (x * y) ^ 2 = x * (y * x) * y := by simp only [pow_two, mul_assoc]
        _ = x * (x * y * ⁅y⁻¹, x⁻¹⁆) * y := by rw [hyx]
        _ = x ^ 2 * (y * ⁅y⁻¹, x⁻¹⁆ * y) := by simp only [pow_two, mul_assoc]
        _ = x ^ 2 * (⁅y⁻¹, x⁻¹⁆ * y ^ 2) := by rw [← hcy]; simp only [pow_two, mul_assoc]
    rw [e]
    exact Z.mul_mem ihx (Z.mul_mem hc ihy)
  | inv x hx ihx =>
    rw [inv_pow]
    exact Z.inv_mem ihx

private theorem Z_sup_Q_one_eq_edgeSylow
    (X : Setup Γ G) (A : X.CaseA) :
    X.Z 4 ⊔ X.Q 1 = X.edgeSylow 1 ∧ X.Z (-2) ⊔ X.Q 1 = X.S := by
  obtain ⟨h3, -, -, -, -, -, hZ1eq, -⟩ := X.caseA_3 A
  obtain ⟨hpos1, hpos2⟩ := X.caseA_pos A
  have h4 : X.HasB 4 3 :=
    (X.hasB_iff_of_even (i := 0) (j := 4) (by norm_num) 3).mp h3
  have hm2 : X.HasB (-2) 3 :=
    (X.hasB_iff_of_even (i := 0) (j := -2) (by norm_num) 3).mp h3
  have hZ3 := X.Z_three_eq_sup_of_Z_one_eq hZ1eq
  have hZm1 := X.Z_neg_one_eq_sup_of_Z_one_eq hZ1eq
  have hG1 : X.Gi 1 = conjSub X.τ (X.Gi (-1)) := by
    have h := X.Gi_add 1 (-1)
    simpa using h
  have hG2 : X.Gi 2 = conjSub X.τ (X.Gi 0) := by
    have h := X.Gi_add 1 0
    simpa using h
  have hG11 : X.Gi (1 + 1) = X.Gi 2 := by congr 1
  have hGm10 : X.Gi ((-1) + 1) = X.Gi 0 := by congr 1
  have hedge : X.edgeSylow 1 = conjSub X.τ (X.edgeSylow (-1)) := by
    unfold Setup.edgeSylow
    rw [hG11, hG1, hG2, hGm10, ← conjSub_inf, pCoreOf_conjSub]
  have hpos3 : X.Z 3 ⊔ X.Q 1 = X.edgeSylow 1 := by
    have h := congrArg (conjSub X.τ) hpos2
    rw [conjSub_sup] at h
    have hZ : conjSub X.τ (X.Z 1) = X.Z 3 := by
      simpa using (X.Z_add 1 1).symm
    have hQ : conjSub X.τ (X.Q (-1)) = X.Q 1 := by
      simpa using (X.Q_add 1 (-1)).symm
    rw [hZ, hQ, ← hedge] at h
    exact h
  have hZ3edge : X.Z 3 ≤ X.edgeSylow 1 := (le_sup_left : X.Z 3 ≤ _).trans hpos3.le
  have hZ4edge : X.Z 4 ≤ X.edgeSylow 1 := (by
    rw [hZ3]; exact le_sup_right : X.Z 4 ≤ X.Z 3).trans hZ3edge
  have hZm1S : X.Z (-1) ≤ X.S := (le_sup_left : X.Z (-1) ≤ _).trans hpos1.le
  have hZm2S : X.Z (-2) ≤ X.S := (by
    rw [hZm1]; exact le_sup_left : X.Z (-2) ≤ X.Z (-1)).trans hZm1S
  have hKZ4 : X.K ≤ Subgroup.normalizer (X.Z 4 : Set G) :=
    fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 4 g (X.K_le_Gi 4 hg))
  have hKZm2 : X.K ≤ Subgroup.normalizer (X.Z (-2) : Set G) :=
    fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal (-2) g (X.K_le_Gi (-2) hg))
  have hedge4 : X.Z 4 ⊔ X.Q 1 = X.edgeSylow 1 :=
    X.sup_Q_eq_edgeSylow_of_left_gen 1 (inf_le_left.trans hKZ4) hZ4edge
      (X.not_Z_le_Q_edge h4).2
  have hedge2 : X.Z (-2) ⊔ X.Q 1 = X.S := by
    have h := X.sup_Q_eq_edgeSylow_of_gen 0 (inf_le_left.trans hKZm2) hZm2S
      (X.not_Z_le_Q_edge hm2).1
    rwa [X.edgeSylow_zero] at h
  exact ⟨hedge4, hedge2⟩

private theorem commutator_Z_one_Q_zero_le_Z_zero
    (X : Setup Γ G) (A : X.CaseA) : ⁅X.Z 1, X.Q 0⁆ ≤ X.Z 0 := by
  obtain ⟨-, -, hZ0R, -, -, -, -, -⟩ := X.caseA_3 A
  obtain ⟨hpos1, -⟩ := X.caseA_pos A
  have hb1' : X.HasB (-1) 2 :=
    (X.hasB_iff_of_even (i := 1) (j := -1) (by norm_num) 2).mp A.b₁
  have hZm1Q0 : X.Z (-1) ≤ X.Q 0 := X.Z_le_Q_of_lt hb1' (j := 0) (by norm_num)
  have hQ1Z0 : X.Q 1 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g ((X.Q_le_Gi_adj 1) hg).1)
  have hZm1Z0 : X.Z (-1) ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun g hg => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 g (X.Q_le_Gi 0 (hZm1Q0 hg)))
  have hcommZ1Q1 : ⁅X.Z 1, X.Q 1⁆ ≤ X.Z 0 := by
    have h : ⁅X.Z 1, X.Q 1⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        ((X.Z_le_center 1).trans inf_le_right)
    rw [h]
    exact bot_le
  have hcommZ1Zm1 : ⁅X.Z 1, X.Z (-1)⁆ ≤ X.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact hZ0R.symm.le
  have hQ0le : X.Q 0 ≤ X.Z (-1) ⊔ X.Q 1 := by
    rw [hpos1]
    exact (X.Q_le_edgeSylow_left 0).trans (le_of_eq X.edgeSylow_zero)
  exact (Subgroup.commutator_mono le_rfl hQ0le).trans
    (CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := X.Z 1) hZm1Z0 hQ1Z0
      hcommZ1Zm1 hcommZ1Q1)

private theorem sq_mem_Z_zero_of_mem_iSup_conjSub (X : Setup Γ G)
    (hZ1elem : IsElemAbelian 2 (X.Z 1)) (hWQ : (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ X.Q 0)
    (hcommWW : ⁅(⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)), (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1))⁆ ≤
      X.Z 0) :
    ∀ a ∈ (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)), a ^ 2 ∈ X.Z 0 := by
  set W : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)
  have hZ0cent : ∀ c ∈ X.Z 0, ∀ x ∈ W, c * x = x * c := by
    intro c hc x hx
    have hccent : c ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 hc)).2
    exact (Subgroup.mem_centralizer_iff.mp hccent x (hWQ hx)).symm
  have hWgen : Subgroup.closure
      (⋃ (g : G) (_ : g ∈ X.Gi 0), (conjSub g (X.Z 1) : Set G)) = W := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro a ha
      rw [Set.mem_iUnion] at ha
      obtain ⟨g, ha⟩ := ha
      rw [Set.mem_iUnion] at ha
      obtain ⟨hg, ha⟩ := ha
      exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hg ha)
    · refine iSup₂_le fun g hg a ha => ?_
      exact Subgroup.subset_closure
        (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, ha⟩⟩)
  have hsqT : ∀ a ∈ ⋃ (g : G) (_ : g ∈ X.Gi 0),
      (conjSub g (X.Z 1) : Set G), a ^ 2 ∈ X.Z 0 := by
    intro a ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨g, ha⟩ := ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨hg, ha⟩ := ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    have hz2 : z ^ 2 = 1 := by
      have := hZ1elem.2 z hz
      simpa using this
    change (g * z * g⁻¹) ^ 2 ∈ X.Z 0
    have e : (g * z * g⁻¹) ^ 2 = g * z ^ 2 * g⁻¹ := by
      calc (g * z * g⁻¹) ^ 2 = (g * z * g⁻¹) * (g * z * g⁻¹) := pow_two _
        _ = g * (z * z) * g⁻¹ := by group
        _ = g * z ^ 2 * g⁻¹ := by rw [pow_two]
    rw [e, hz2]
    simp
  have hcommWV : ∀ a ∈ W, ∀ b ∈ W, ⁅a, b⁆ ∈ X.Z 0 :=
    fun a ha b hb => Subgroup.commutator_le.mp hcommWW a ha b hb
  exact sq_mem_of_gen hWgen hZ0cent hcommWV hsqT

theorem caseA_5a (X : Setup Γ G) (A : X.CaseA) :
    (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ≤ X.Q 0 ∧
      ⁅(⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)), X.Q 0⁆ ≤ X.Z 0 ∧
      X.Z 0 ≤
        ⁅(⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)), (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1))⁆ ∧
      IsElemSec (X.Z 0) (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ∧
      X.Z 4 ⊔ X.Q 1 = X.edgeSylow 1 ∧
      X.Z (-2) ⊔ X.Q 1 = X.S := by
  obtain ⟨-, -, hZ0R, -, -, -, hZ1eq, -⟩ := X.caseA_3 A
  have hRelem : IsElemAbelian 2 (X.Z 0) := hZ0R ▸ (X.caseA_R_elem A).1
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num)
  set W : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1) with hW
  have hWQ : W ≤ X.Q 0 := by
    refine iSup₂_le fun g hg => ?_
    calc conjSub g (X.Z 1) ≤ conjSub g (X.Q 0) := conjSub_mono g hZ1Q0
      _ = X.Q 0 := mem_normalizer_iff_conjSub.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hg)
  have hZ2elem : IsElemAbelian 2 (X.Z 2) := by
    have h : X.Z 2 = conjSub (X.τ ^ (1 : ℤ)) (X.Z 0) := by
      simpa using X.Z_add 1 0
    rw [h, conjSub]
    simpa using hRelem.map (MulAut.conj X.τ).toMonoidHom
  have hZ1elem : IsElemAbelian 2 (X.Z 1) := by
    rw [hZ1eq]
    refine IsElemAbelian.sup_of_commute hRelem hZ2elem ?_
    intro x hx y hy
    have hx1 : x ∈ X.Z 1 := hZ1eq ▸ Subgroup.mem_sup_left hx
    have hy1 : y ∈ X.Z 1 := hZ1eq ▸ Subgroup.mem_sup_right hy
    have hxcent : x ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hx1)).2
    exact (Subgroup.mem_centralizer_iff.mp hxcent y (X.Z_le_Q 1 hy1)).symm
  have hcommZ1Q0 : ⁅X.Z 1, X.Q 0⁆ ≤ X.Z 0 := X.commutator_Z_one_Q_zero_le_Z_zero A
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    fun q hq => mem_normalizer_iff_conjSub.mpr (X.Z_normal 0 q (X.Q_le_Gi 0 hq))
  have hcommWQ : ⁅W, X.Q 0⁆ ≤ X.Z 0 := by
    have hconjN : ∀ g ∈ X.Gi 0, conjSub g (X.Z 1) ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
      fun g hg => ((le_iSup₂_of_le (f := fun g (_ : g ∈ X.Gi 0) => conjSub g (X.Z 1))
        g hg le_rfl : conjSub g (X.Z 1) ≤ W).trans hWQ).trans hQ0N
    have hconjQ : ∀ g ∈ X.Gi 0, ⁅conjSub g (X.Z 1), X.Q 0⁆ ≤ X.Z 0 := by
      intro g hg
      have hconjQ0 : conjSub g (X.Q 0) = X.Q 0 := mem_normalizer_iff_conjSub.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0) hg)
      calc ⁅conjSub g (X.Z 1), X.Q 0⁆
          = ⁅conjSub g (X.Z 1), conjSub g (X.Q 0)⁆ := by rw [hconjQ0]
        _ = conjSub g ⁅X.Z 1, X.Q 0⁆ := conjSub_commutator g _ _
        _ ≤ conjSub g (X.Z 0) := conjSub_mono g hcommZ1Q0
        _ = X.Z 0 := X.Z_normal 0 g hg
    refine CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
      (A := fun g => ⨆ (_ : g ∈ X.Gi 0), conjSub g (X.Z 1)) (Y := X.Q 0) (N := X.Z 0)
      (fun g => iSup_le fun hg => hconjN g hg) (fun g => ?_)
    exact CFSG.GroupTheory.commutator_iSup_left_le_of_le_normalizer
      (fun hg => hconjN g hg) (fun hg => hconjQ g hg)
  have hcommWW : ⁅W, W⁆ ≤ X.Z 0 :=
    (Subgroup.commutator_mono le_rfl hWQ).trans hcommWQ
  have hZ1W : X.Z 1 ≤ W := le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [conjSub_one])
  have hZm1W : X.Z (-1) ≤ W := X.Z_neg_one_le_iSup_conjSub
  have hZ0WW : X.Z 0 ≤ ⁅W, W⁆ := by
    rw [hZ0R]
    exact Subgroup.commutator_mono hZm1W hZ1W
  have hWWW : ⁅W, W⁆ ≤ W :=
    (Subgroup.commutator_le_sup (H₁ := W) (H₂ := W)).trans (le_of_eq (sup_idem W))
  have hZ0W : X.Z 0 ≤ W := hZ0WW.trans hWWW
  have hsqW : ∀ a ∈ W, a ^ 2 ∈ X.Z 0 :=
    X.sq_mem_Z_zero_of_mem_iSup_conjSub hZ1elem hWQ hcommWW
  obtain ⟨hedge4, hedge2⟩ := X.Z_sup_Q_one_eq_edgeSylow A
  exact ⟨hWQ, hcommWQ, hZ0WW, ⟨hZ0W, hcommWW, hsqW⟩, hedge4, hedge2⟩

private theorem commutator_Z_four_Q_two_le_Z_two
    (X : Setup Γ G) (A : X.CaseA) : ⁅X.Z 4, X.Q 2⁆ ≤ X.Z 2 := by
  obtain ⟨-, -, -, -, -, -, hZ1eq, -⟩ := X.caseA_3 A
  have h5a2 := (X.caseA_5a A).2.1
  set W : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)
  have hZ1W : X.Z 1 ≤ W := le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [conjSub_one])
  have hZ4W : X.Z 4 ≤ conjSub X.τ W := by
    have hZ3conj : X.Z 3 = conjSub X.τ (X.Z 1) := by
      simpa using X.Z_add 1 1
    calc X.Z 4 ≤ X.Z 3 := by rw [X.Z_three_eq_sup_of_Z_one_eq hZ1eq]; exact le_sup_right
      _ = conjSub X.τ (X.Z 1) := hZ3conj
      _ ≤ conjSub X.τ W := conjSub_mono _ hZ1W
  have hQ0conj : conjSub X.τ (X.Q 0) = X.Q 2 := by
    simpa using (X.Q_add 1 0).symm
  have hZ0conj : conjSub X.τ (X.Z 0) = X.Z 2 := by
    simpa using (X.Z_add 1 0).symm
  calc ⁅X.Z 4, X.Q 2⁆ ≤ ⁅conjSub X.τ W, X.Q 2⁆ := Subgroup.commutator_mono hZ4W le_rfl
    _ = ⁅conjSub X.τ W, conjSub X.τ (X.Q 0)⁆ := by rw [hQ0conj]
    _ = conjSub X.τ ⁅W, X.Q 0⁆ := conjSub_commutator _ _ _
    _ ≤ conjSub X.τ (X.Z 0) := conjSub_mono _ h5a2
    _ = X.Z 2 := hZ0conj

private theorem T_le_L_one_and_commutator_le
    (X : Setup Γ G) (A : X.CaseA) :
    X.Z (-2) ⊔ X.Z 4 ≤ X.L 1 ∧ ⁅X.Z (-2) ⊔ X.Z 4, X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 1 := by
  obtain ⟨h3, -, -, -, -, hNatZ1, hZ1eq, -⟩ := X.caseA_3 A
  have h5a2 := (X.caseA_5a A).2.1
  have hZ0Z1 : X.Z 0 ≤ X.Z 1 := hZ1eq ▸ le_sup_left
  have hZ2Z1 : X.Z 2 ≤ X.Z 1 := hZ1eq ▸ le_sup_right
  have h4 : X.HasB 4 3 :=
    (X.hasB_iff_of_even (i := 0) (j := 4) (by norm_num) 3).mp h3
  have hm2 : X.HasB (-2) 3 :=
    (X.hasB_iff_of_even (i := 0) (j := -2) (by norm_num) 3).mp h3
  have hZm2W : X.Z (-2) ≤ ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1) :=
    (by rw [X.Z_neg_one_eq_sup_of_Z_one_eq hZ1eq]; exact le_sup_left :
      X.Z (-2) ≤ X.Z (-1)).trans X.Z_neg_one_le_iSup_conjSub
  have hcommZm2A1 : ⁅X.Z (-2), X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono hZm2W inf_le_left).trans (h5a2.trans hZ0Z1)
  have hcommZ4A1 : ⁅X.Z 4, X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 1 :=
    (Subgroup.commutator_mono le_rfl inf_le_right).trans
      ((X.commutator_Z_four_Q_two_le_Z_two A).trans hZ2Z1)
  have hZm2Gi1 : X.Z (-2) ≤ X.Gi 1 := hm2.Z_le_Gi (by norm_num)
  have hZ4Gi1 : X.Z 4 ≤ X.Gi 1 := h4.Z_le_Gi (by norm_num)
  have hZm2L1 : X.Z (-2) ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (-2)) |>.to_le (X.Z_le_Q (-2)))
      hZm2Gi1
  have hZ4L1 : X.Z 4 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 4) |>.to_le (X.Z_le_Q 4)) hZ4Gi1
  have hL1normZ1 : X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    exact (Subgroup.mem_inf.mp (hNatZ1.normal hx)).1
  exact ⟨sup_le hZm2L1 hZ4L1,
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _
      hcommZm2A1 hcommZ4A1 (hZm2L1.trans hL1normZ1) (hZ4L1.trans hL1normZ1)⟩

private theorem L_one_eq_sup_Q_one (X : Setup Γ G)
    (A : X.CaseA) : X.L 1 = (X.Z (-2) ⊔ X.Z 4) ⊔ X.Q 1 := by
  obtain ⟨-, -, -, -, h5a5, h5a6⟩ := X.caseA_5a A
  rw [← X.edgeSylow_sup_edgeSylow 1, show (1 : ℤ) - 1 = 0 by norm_num, X.edgeSylow_zero,
    ← h5a6, ← h5a5]
  simp only [sup_assoc, sup_comm, sup_left_comm, sup_idem]

theorem caseA_5b (X : Setup Γ G) (A : X.CaseA) :
    X.Gi 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) ∧
      ⁅X.Q 0 ⊓ X.Q 2, oTwoRes (X.L 1)⁆ ≤ X.Z 1 := by
  obtain ⟨-, -, -, -, -, hNatZ1, -, -⟩ := X.caseA_3 A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set T : Subgroup G := X.Z (-2) ⊔ X.Z 4 with hT
  have hZ1Q0 : X.Z 1 ≤ X.Q 0 := X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num)
  have hZ1Q2 : X.Z 1 ≤ X.Q 2 := X.Z_le_Q_of_lt A.b₁ (j := 2) (by norm_num)
  have hZ1A1 : X.Z 1 ≤ A1 := by rw [hA1]; exact le_inf hZ1Q0 hZ1Q2
  obtain ⟨hTL1, hTA1⟩ : T ≤ X.L 1 ∧ ⁅T, A1⁆ ≤ X.Z 1 := X.T_le_L_one_and_commutator_le A
  have hL1normZ1 : X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    exact (Subgroup.mem_inf.mp (hNatZ1.normal hx)).1
  have hTN : T ≤ Subgroup.normalizer (A1 : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_right.mpr (hTA1.trans hZ1A1)
  have hQ1N : X.Q 1 ≤ Subgroup.normalizer (A1 : Set G) := by
    intro q hq
    have hq0 : q ∈ X.Gi 0 := (X.Q_le_Gi_adj 1 hq).1
    have hq2 : q ∈ X.Gi 2 := (X.Q_le_Gi_adj 1 hq).2
    rw [hA1]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) hq0,
       (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) hq2⟩
  have hGi1eq : X.Gi 1 = X.L 1 ⊔ X.K := X.Gi_eq_L_sup_K 1
  have hL1eq : X.L 1 = T ⊔ X.Q 1 := X.L_one_eq_sup_Q_one A
  have hL1N : X.L 1 ≤ Subgroup.normalizer (A1 : Set G) := by
    rw [hL1eq]
    exact sup_le hTN hQ1N
  have hKN : X.K ≤ Subgroup.normalizer (A1 : Set G) := by
    intro k hk
    rw [hA1]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0)) (X.K_le_Gi 0 hk),
       (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) (X.K_le_Gi 2 hk)⟩
  have hGi1N : X.Gi 1 ≤ Subgroup.normalizer (A1 : Set G) := by
    rw [hGi1eq]
    exact sup_le hL1N hKN
  refine ⟨hGi1N, ?_⟩
  set C : Subgroup G := dsCentMod (X.L 1) A1 (X.Z 1) with hC
  have hO2C : oTwoRes (X.L 1) ≤ C :=
    (oTwoRes_le_dsConjClosure (pCoreOf_isPGroup' (X.Gi 1)) hL1eq).trans
      (dsConjClosure_le_dsCentMod hTL1 hL1N hL1normZ1 hTA1)
  have hcommA1O2 : ⁅A1, oTwoRes (X.L 1)⁆ ≤ X.Z 1 := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_le]
    intro x hx a ha
    have hxC := hO2C hx
    rw [hC] at hxC
    exact hxC.2.2 a ha
  rw [hA1]
  exact hcommA1O2

private theorem comm_edgeSylow_le_inf (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Q 1, X.edgeSylow 1⁆ ≤ X.Q 1 ⊓ X.Q 2 := by
  obtain ⟨h5b1, -⟩ := X.caseA_5b A
  obtain ⟨-, -, -, -, h5a5, -⟩ := X.caseA_5a A
  obtain ⟨hA1Q1, -, hQ1comm, -, -, -⟩ :=
    X.Q_quot A.hyp.char A.hyp.sing (by omega : 4 ≤ 7) 1
  set B : Subgroup G := X.Q 1 ⊓ X.Q 2 with hB
  have hA1B : X.Q 0 ⊓ X.Q 2 ≤ B := by rw [hB]; exact le_inf hA1Q1 inf_le_right
  obtain ⟨h3, -⟩ := X.caseA_3 A
  have h4 : X.HasB 4 3 :=
    (X.hasB_iff_of_even (i := 0) (j := 4) (by norm_num) 3).mp h3
  have hZ4Q2 : X.Z 4 ≤ X.Q 2 := X.Z_le_Q_of_lt h4 (j := 2) (by norm_num)
  have hZ4Gi1 : X.Z 4 ≤ X.Gi 1 := h4.Z_le_Gi (by norm_num)
  have hQ1Gi2 : X.Q 1 ≤ X.Gi 2 := fun q hq => (X.Q_le_Gi_adj 1 hq).2
  have hZ4NQ1 : X.Z 4 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    fun z hz => (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)) (hZ4Gi1 hz)
  have hQ1NQ2 : X.Q 1 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    fun q hq => (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2)) (hQ1Gi2 hq)
  have hZ4NQ2 : X.Z 4 ≤ Subgroup.normalizer (X.Q 2 : Set G) :=
    fun z hz => (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 2))
      ((X.Q_le_Gi 2) (hZ4Q2 hz))
  have hZ4NB : X.Z 4 ≤ Subgroup.normalizer (B : Set G) :=
    (le_inf hZ4NQ1 hZ4NQ2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQ1NB : X.Q 1 ≤ Subgroup.normalizer (B : Set G) :=
    (le_inf Subgroup.le_normalizer hQ1NQ2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQ1Z4Q1 : ⁅X.Q 1, X.Z 4⁆ ≤ X.Q 1 :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hZ4NQ1
  have hQ1Z4Q2 : ⁅X.Q 1, X.Z 4⁆ ≤ X.Q 2 :=
    (Subgroup.commutator_mono le_rfl hZ4Q2).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1NQ2)
  have hQ1Z4 : ⁅X.Q 1, X.Z 4⁆ ≤ B := by
    rw [hB]; exact le_inf hQ1Z4Q1 hQ1Z4Q2
  have hmain : ⁅X.Q 1, X.Z 4 ⊔ X.Q 1⁆ ≤ B :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := X.Q 1)
      (A := X.Z 4) (B := X.Q 1) (N := B) hZ4NB hQ1NB hQ1Z4
      (hQ1comm.trans hA1B)
  rw [← h5a5]
  exact hmain

private theorem comm_B_edgeSylow (X : Setup Γ G) (A : X.CaseA) :
    ⁅X.Q 1 ⊓ X.Q 2, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2 := by
  obtain ⟨h5b1, -⟩ := X.caseA_5b A
  obtain ⟨-, -, hQ1comm, -, -, -⟩ :=
    X.Q_quot A.hyp.char A.hyp.sing (by omega : 4 ≤ 7) 1
  obtain ⟨h3, -, -, -, -, -, hZ1eq, -⟩ := X.caseA_3 A
  obtain ⟨-, -, -, -, h5a5, -⟩ := X.caseA_5a A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set B : Subgroup G := X.Q 1 ⊓ X.Q 2 with hB
  have h4 : X.HasB 4 3 :=
    (X.hasB_iff_of_even (i := 0) (j := 4) (by norm_num) 3).mp h3
  have hZ4Gi1 : X.Z 4 ≤ X.Gi 1 := h4.Z_le_Gi (by norm_num)
  have hZ4Q2 : X.Z 4 ≤ X.Q 2 := X.Z_le_Q_of_lt h4 (j := 2) (by norm_num)
  have hZ1A1 : X.Z 1 ≤ A1 := by
    rw [hA1]
    exact le_inf (X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num))
      (X.Z_le_Q_of_lt A.b₁ (j := 2) (by norm_num))
  have hZ2A1 : X.Z 2 ≤ A1 := (hZ1eq ▸ le_sup_right : X.Z 2 ≤ X.Z 1).trans hZ1A1
  have hBQ2 : B ≤ X.Q 2 := by rw [hB]; exact inf_le_right
  have hBQ1 : ⁅B, X.Q 1⁆ ≤ A1 :=
    (Subgroup.commutator_mono (by simp [hB]) le_rfl).trans hQ1comm
  have hBZ4 : ⁅B, X.Z 4⁆ ≤ A1 := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl hBQ2).trans
      ((X.commutator_Z_four_Q_two_le_Z_two A).trans hZ2A1)
  have hZ4NA1 : X.Z 4 ≤ Subgroup.normalizer (A1 : Set G) := hZ4Gi1.trans h5b1
  have hQ1NA1 : X.Q 1 ≤ Subgroup.normalizer (A1 : Set G) := (X.Q_le_Gi 1).trans h5b1
  have hmain : ⁅B, X.Z 4 ⊔ X.Q 1⁆ ≤ A1 :=
    CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer (Y := B)
      (A := X.Z 4) (B := X.Q 1) (N := A1) hZ4NA1 hQ1NA1 hBZ4 hBQ1
  rw [← h5a5]
  exact hmain

theorem caseA_5c (X : Setup Γ G) (A : X.CaseA)
    (hn : ∀ i : ℤ, X.n i = 2) :
    NatQuot (X.L 1) (X.Q 1) (X.Q 0 ⊓ X.Q 2) 2 ∧
      X.Q 1 = (X.Q 1 ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q 2) := by
  obtain ⟨h5b1, -⟩ := X.caseA_5b A
  obtain ⟨-, -, -, -, -, hdec⟩ := X.Q_quot A.hyp.char A.hyp.sing (by omega : 4 ≤ 7) 1
  have hquad : ⁅⁅X.Q 1, X.edgeSylow 1⁆, X.edgeSylow 1⁆ ≤ X.Q 0 ⊓ X.Q 2 :=
    (Subgroup.commutator_mono (X.comm_edgeSylow_le_inf A) le_rfl).trans
      (X.comm_B_edgeSylow A)
  refine ⟨?_, ?_⟩
  · exact X.natQuot_Q_of_normal A.hyp.char A.hyp.sing (by omega : 4 ≤ 7) 1
      (hn 1) (hn 2) h5b1 hquad
  · simpa only [show (1 : ℤ) - 1 = 0 by norm_num,
      show (1 : ℤ) + 1 = 2 by norm_num, sup_comm] using hdec

theorem caseA_w1Hyp (X : Setup Γ G) (A : X.CaseA) : X.CaseAW1Hyp := by
  obtain ⟨hA1Q1, hsq, hcomm, hrel, -, hdec⟩ :=
    X.Q_quot A.hyp.char A.hyp.sing (by omega : 4 ≤ 7) 1
  have hrel' : (X.Q 0 ⊓ X.Q 2).relIndex (X.Q 1) = 2 ^ (2 * X.n 0) := by
    have hn2 : X.n 2 = X.n 0 := by
      simpa using (X.n_add (1 : ℤ) (0 : ℤ))
    simpa [show (1 : ℤ) - 1 = 0 by norm_num, show (1 : ℤ) + 1 = 2 by norm_num,
      hn2] using hrel
  refine
    { two_le_n0 := A.hyp.two_le_n 0
      two_le_n1 := A.hyp.two_le_n 1
      sec := ⟨by simpa using hA1Q1, by simpa using hcomm, by simpa using hsq⟩
      relIndex := hrel'
      dec := by
        simpa [show (1 : ℤ) - 1 = 0 by norm_num,
          show (1 : ℤ) + 1 = 2 by norm_num] using hdec
      normal := (X.caseA_5b A).1
      comm_S := X.comm_edgeSylow_le_inf A
      comm_B := X.comm_B_edgeSylow A }

theorem odd_orderOf_of_mem_Ki (X : Setup Γ G) {i : ℤ} {k : G} (hk : k ∈ X.Ki i) :
    Odd (orderOf k) := by
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 0)
  exact Odd.of_dvd_nat X.odd_card_K (Subgroup.orderOf_dvd_natCard X.K hk.1)

private theorem Q_inf_Q_le_D_sup_Z_one_of_solvable (X : Setup Γ G)
    (hKA1 : X.Ki 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G))
    (hA1Q1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1)
    (hA1solv : Group.IsSolvable ↥(X.Q 0 ⊓ X.Q 2))
    (hALKi : ⁅X.Q 0 ⊓ X.Q 2, X.Ki 1⁆ ≤ X.Z 1) :
    X.Q 0 ⊓ X.Q 2 ≤ (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1 := by
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  have hA1Gi : A1 ≤ X.Gi 1 := hA1Q1.trans (X.Q_le_Gi 1)
  have hA1p : IsPGroup 2 A1 := (pCoreOf_isPGroup' (X.Gi 1)).to_le hA1Q1
  haveI : Finite ↥A1 := finite_of_le_stabilizer X.hyp hA1Gi
  haveI : Finite ↥(X.Ki 1) :=
    finite_of_le_stabilizer X.hyp (inf_le_right.trans (X.L_le_Gi 1))
  have hn1 : 1 ≤ X.n 1 := (X.hyp.valency (X.vert 1)).1
  have hKiodd : Odd (Nat.card ↥(X.Ki 1)) := by
    rw [X.card_Ki 1]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  obtain ⟨t, ht⟩ := (IsPGroup.iff_card (p := 2)).mp hA1p
  have hcop : Nat.Coprime (Nat.card ↥(X.Ki 1)) (Nat.card ↥A1) := by
    rw [ht]
    exact hKiodd.coprime_two_right.pow_right t
  have hdec := CFSG.GroupTheory.le_commutator_sup_inf_centralizer_of_coprime_of_finite
    (R := A1) (A := X.Ki 1) hKA1 hcop hA1solv
  refine hdec.trans (sup_le ?_ ?_)
  · exact hALKi.trans le_sup_right
  · exact (le_inf (inf_le_left.trans hA1Q1) inf_le_right).trans le_sup_left

private theorem Q_inf_Q_le_D_sup_Z_one (X : Setup Γ G)
    (hKA1 : X.Ki 1 ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G))
    (hA1Q1 : X.Q 0 ⊓ X.Q 2 ≤ X.Q 1) (hA1elem : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2))
    (hALKi : ⁅X.Q 0 ⊓ X.Q 2, X.Ki 1⁆ ≤ X.Z 1) :
    X.Q 0 ⊓ X.Q 2 ≤ (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1 := by
  have hA1solv : Group.IsSolvable ↥(X.Q 0 ⊓ X.Q 2) :=
    Group.isSolvable_of_comm (fun a b => hA1elem.1.is_comm.comm a b)
  exact X.Q_inf_Q_le_D_sup_Z_one_of_solvable hKA1 hA1Q1 hA1solv hALKi

private theorem D_inf_Z_one_eq_bot (X : Setup Γ G) (A : X.CaseA) {k : G}
    (hkKi : k ∈ X.Ki 1) (hk1 : k ≠ 1) :
    (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥ := by
  obtain ⟨-, -, -, -, -, hNatZ1, -, -⟩ := X.caseA_3 A
  have hkQ1 : k ∉ X.Q 1 := by
    intro hkQ
    have hmem : k ∈ X.K ⊓ X.Q 1 := Subgroup.mem_inf.mpr ⟨hkKi.1, hkQ⟩
    rw [X.K_inf_Q_eq_bot 1] at hmem
    exact hk1 (Subgroup.mem_bot.mp hmem)
  have hkZ1 : k ∉ X.Z 1 := fun h => hkQ1 (X.Z_le_Q 1 h)
  have hodd : Odd (orderOf k) := X.odd_orderOf_of_mem_Ki hkKi
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzD, hzZ⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨-, hzC⟩ := Subgroup.mem_inf.mp hzD
  have hcomm : ⁅z, k⁆ ∈ (⊥ : Subgroup G) := by
    have h1 : ⁅z, k⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hzC k hkKi).symm
    rw [h1]
    exact Subgroup.one_mem _
  exact hNatZ1.fpf k hkKi.2 hodd hkZ1 z hzZ hcomm

theorem caseA_card_Q_zero_inf_Q_two (X : Setup Γ G) (A : X.CaseA) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 2) = 2 ^ (X.n 0 + 2 * X.n 1) := by
  have hW := X.caseA_w1Hyp A
  have hQ1card : Nat.card ↥(X.Q 1) = 2 ^ (2 * X.n 0) * 2 ^ (X.n 0 + 2 * X.n 1) := by
    have h := (X.caseA_card A).2 1
    rw [show (1 : ℤ) + 1 = 0 + 2 * 1 by norm_num, X.n_add 1 0] at h
    rw [h, ← pow_add]
    congr 1
    ring
  have h := Subgroup.relIndex_mul_card (H := X.Q 0 ⊓ X.Q 2) (K := X.Q 1)
  rw [inf_eq_left.mpr hW.sec.1, hW.relIndex, hQ1card] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) h

private theorem D_card_eq (X : Setup Γ G) (A : X.CaseA)
    (hA1eq : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1)
    (hDZ1 : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥) :
    Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 2 ^ X.n 0 := by
  obtain ⟨-, -, -, -, -, hNatZ1, -, -⟩ := X.caseA_3 A
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hD
  have hcardA1 : Nat.card ↥(X.Q 0 ⊓ X.Q 2) = 2 ^ (X.n 0 + 2 * X.n 1) :=
    X.caseA_card_Q_zero_inf_Q_two A
  have hcardZ1 : Nat.card ↥(X.Z 1) = 2 ^ (2 * X.n 1) := by
    have h := hNatZ1.index
    rwa [Subgroup.relIndex_bot_left] at h
  have hZnormD : X.Z 1 ≤ Subgroup.normalizer (D : Set G) := by
    intro z hz
    refine Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun d hd => ?_)
    exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2) d hd.1
  have hdisj : Disjoint D (X.Z 1) := by
    rw [disjoint_iff]
    exact hDZ1
  haveI : Finite ↥D :=
    finite_of_le_stabilizer X.hyp (inf_le_left.trans (X.Q_le_Gi 1))
  haveI : Finite ↥(X.Z 1) :=
    finite_of_le_stabilizer X.hyp ((X.Z_le_Q 1).trans (X.Q_le_Gi 1))
  have hsupcard : Nat.card ↥(D ⊔ X.Z 1) = Nat.card ↥D * Nat.card ↥(X.Z 1) :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      D (X.Z 1) hZnormD hdisj
  have hDp : IsPGroup 2 D := by
    rw [hD]
    exact (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_left
  obtain ⟨kd, hkd⟩ := (IsPGroup.iff_card (p := 2)).mp hDp
  have hcard_eq : Nat.card ↥(X.Q 0 ⊓ X.Q 2) = Nat.card ↥D * Nat.card ↥(X.Z 1) := by
    rw [hA1eq, hsupcard]
  have h1 : 2 ^ (X.n 0 + 2 * X.n 1) = 2 ^ (2 * X.n 1 + kd) := by
    calc 2 ^ (X.n 0 + 2 * X.n 1)
        = Nat.card ↥(X.Q 0 ⊓ X.Q 2) := hcardA1.symm
      _ = Nat.card ↥D * Nat.card ↥(X.Z 1) := hcard_eq
      _ = 2 ^ kd * 2 ^ (2 * X.n 1) := by rw [hkd, hcardZ1]
      _ = 2 ^ (2 * X.n 1 + kd) := by rw [pow_add, Nat.mul_comm]
  have hexp : X.n 0 + 2 * X.n 1 = 2 * X.n 1 + kd :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) h1
  have hkd' : kd = X.n 0 := by omega
  rw [hkd, hkd']

private theorem D_inf_Z_one_eq_bot_and_card
    (X : Setup Γ G) (A : X.CaseA) {k : G} (hkKi : k ∈ X.Ki 1) (hk1 : k ≠ 1)
    (hA1eq : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1) :
    (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥ ∧
      Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 2 ^ X.n 0 := by
  have hDZ1 := X.D_inf_Z_one_eq_bot A hkKi hk1
  exact ⟨hDZ1, X.D_card_eq A hA1eq hDZ1⟩

private theorem Q_one_le_conjClosure_sup {X : Setup Γ G} (A : X.CaseA)
    (W : X.CaseAW1Hyp) :
    X.Q 1 ≤ dsConjClosure (X.L 1) (X.Z (-2) ⊔ X.Z 4) ⊔ (X.Q 0 ⊓ X.Q 2) := by
  obtain ⟨-, -, -, -, h5a5, h5a6⟩ := X.caseA_5a A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2
  set M : Subgroup G := dsConjClosure (X.L 1) (X.Z (-2) ⊔ X.Z 4)
  have hTM : X.Z (-2) ⊔ X.Z 4 ≤ M := le_dsConjClosure (X.L 1) (X.Z (-2) ⊔ X.Z 4)
  have hL1NM : X.L 1 ≤ Subgroup.normalizer (M : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_iSup_conj (X.L 1) (X.Z (-2) ⊔ X.Z 4)
  have hQ1NM : X.Q 1 ≤ Subgroup.normalizer (M : Set G) := (X.Q_le_L 1).trans hL1NM
  have hS0syl : IsSylowTwoOf (X.edgeSylow 0) (X.L 1) := X.isSylowTwoOf_edgeSylow_L_succ 0
  have hS1syl : IsSylowTwoOf (X.edgeSylow 1) (X.L 1) := X.isSylowTwoOf_edgeSylow_L 1
  have hS0G1 : X.edgeSylow 0 ≤ X.Gi 1 := (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right
  have hS0L1 : X.edgeSylow 0 ≤ X.L 1 := hS0syl.1
  have hS1L1 : X.edgeSylow 1 ≤ X.L 1 := hS1syl.1
  have hS0NA : X.edgeSylow 0 ≤ Subgroup.normalizer ((M ⊔ A1 : Subgroup G) : Set G) := by
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_sup M A1
      ⟨hL1NM (hS0L1 ha), W.normal (hS0G1 ha)⟩
  have hS1NA : X.edgeSylow 1 ≤ Subgroup.normalizer ((M ⊔ A1 : Subgroup G) : Set G) := by
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_sup M A1
      ⟨hL1NM (hS1L1 ha), W.normal (((X.isSylowTwoOf_edgeSylow 1).1 ha).1)⟩
  have hQ1Z4M : ⁅X.Q 1, X.Z 4⁆ ≤ M :=
    (Subgroup.commutator_mono le_rfl (le_sup_right.trans hTM)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1NM)
  have hQ1Zm2M : ⁅X.Q 1, X.Z (-2)⁆ ≤ M :=
    (Subgroup.commutator_mono le_rfl (le_sup_left.trans hTM)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1NM)
  have hQ1S1 : ⁅X.Q 1, X.edgeSylow 1⁆ ≤ M ⊔ A1 := by
    rw [← h5a5]
    have hS1NA' : X.Z 4 ⊔ X.Q 1 ≤ Subgroup.normalizer ((M ⊔ A1 : Subgroup G) : Set G) := by
      rw [h5a5]; exact hS1NA
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (le_sup_left.trans hS1NA') (le_sup_right.trans hS1NA')
      (hQ1Z4M.trans le_sup_left) (W.sec.2.1.trans le_sup_right)
  have hQ1S0 : ⁅X.Q 1, X.edgeSylow 0⁆ ≤ M ⊔ A1 := by
    have hS0eq : X.edgeSylow 0 = X.Z (-2) ⊔ X.Q 1 := h5a6.symm
    rw [hS0eq]
    have hS0NA' : X.Z (-2) ⊔ X.Q 1 ≤ Subgroup.normalizer ((M ⊔ A1 : Subgroup G) : Set G) := by
      rw [h5a6]; exact hS0NA
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (le_sup_left.trans hS0NA') (le_sup_right.trans hS0NA')
      (hQ1Zm2M.trans le_sup_left) (W.sec.2.1.trans le_sup_right)
  have hB2le : X.Q 1 ⊓ X.Q 2 ≤ M ⊔ A1 := by
    rw [← W.comm_edgeSylow_sup]
    exact sup_le hQ1S1 le_sup_right
  have hB0le : X.Q 1 ⊓ X.Q 0 ≤ M ⊔ A1 := by
    rw [← W.comm_edgeSylow_zero_sup]
    exact sup_le hQ1S0 le_sup_right
  rw [W.dec]
  exact sup_le hB2le hB0le

private theorem commutator_L_one_Q_inf_Q_le_Z_one {X : Setup Γ G} (A : X.CaseA)
    (W : X.CaseAW1Hyp)
    (hA1elem : IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2)) :
    ⁅X.L 1, X.Q 0 ⊓ X.Q 2⁆ ≤ X.Z 1 := by
  obtain ⟨-, -, -, -, -, hNatZ1, -, -⟩ := X.caseA_3 A
  obtain ⟨hTL1, hTA1⟩ := X.T_le_L_one_and_commutator_le A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2
  set M : Subgroup G := dsConjClosure (X.L 1) (X.Z (-2) ⊔ X.Z 4)
  have hL1normZ1 : X.L 1 ≤ Subgroup.normalizer (X.Z 1 : Set G) := by
    intro x hx
    exact (Subgroup.mem_inf.mp (hNatZ1.normal hx)).1
  have hTM : X.Z (-2) ⊔ X.Z 4 ≤ M := le_dsConjClosure (X.L 1) (X.Z (-2) ⊔ X.Z 4)
  have hMle : M ≤ X.L 1 := dsConjClosure_le_of_le hTL1 Subgroup.le_normalizer
  have hA1Q1 : A1 ≤ X.Q 1 := W.sec.1
  have hQ1L1 : X.Q 1 ≤ X.L 1 := X.Q_le_L 1
  set Cc : Subgroup G := dsCentMod (X.L 1) A1 (X.Z 1) with hCc
  have hMCc : M ≤ Cc :=
    dsConjClosure_le_dsCentMod hTL1 ((X.L_le_Gi 1).trans W.normal) hL1normZ1 hTA1
  have hMAC : ⁅M, A1⁆ ≤ X.Z 1 := by
    rw [Subgroup.commutator_le]
    intro m hm a ha
    have hmC := hMCc hm
    rw [hCc] at hmC
    exact hmC.2.2 a ha
  have hA1comm : ⁅A1, A1⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hA1elem.comm hy hx
  have hMAsup : ⁅M ⊔ A1, A1⁆ ≤ X.Z 1 :=
    CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize _ _ _ _ hMAC
      (by rw [hA1comm]; exact bot_le) (hMle.trans hL1normZ1)
      ((hA1Q1.trans hQ1L1).trans hL1normZ1)
  have hL1MA : X.L 1 ≤ M ⊔ A1 :=
    (X.L_one_eq_sup_Q_one A).le.trans
      (sup_le (hTM.trans le_sup_left) (X.Q_one_le_conjClosure_sup A W))
  exact (Subgroup.commutator_mono hL1MA le_rfl).trans hMAsup

private theorem Q_zero_eq_V_sup_inf (X : Setup Γ G) (A : X.CaseA) :
    X.Q 0 = (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔ (X.Q 1 ⊓ X.Q 0) := by
  obtain ⟨h5a1, -, -, -, -, h5a6⟩ := X.caseA_5a A
  obtain ⟨-, -, -, -, -, -, hZ1eq, -⟩ := X.caseA_3 A
  set V : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)
  have hZm2V : X.Z (-2) ≤ V := by
    have hZm1V : X.Z (-1) ≤ V := X.Z_neg_one_le_iSup_conjSub
    refine (by rw [X.Z_neg_one_eq_sup_of_Z_one_eq hZ1eq]; exact le_sup_left :
      X.Z (-2) ≤ X.Z (-1)).trans hZm1V
  have hVN : X.Gi 0 ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_iSup_conj (X.Gi 0) (X.Z 1)
  have hQ1G0 : X.Q 1 ≤ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left
  have hQ1NV : X.Q 1 ≤ Subgroup.normalizer (V : Set G) := hQ1G0.trans hVN
  have hQ0le : X.Q 0 ≤ V ⊔ X.Q 1 := by
    have h1 : X.Q 0 ≤ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0
    have h2 : X.edgeSylow 0 ≤ V ⊔ X.Q 1 := by
      rw [X.edgeSylow_zero, ← h5a6]
      exact sup_le (hZm2V.trans le_sup_left) le_sup_right
    exact h1.trans h2
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (X.Q 1 ⊔ V : Subgroup G) := by
      rw [sup_comm]; exact hQ0le hx
    have hprod : (↑(X.Q 1 ⊔ V) : Set G) = (X.Q 1 : Set G) * (V : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right (X.Q 1) V hQ1NV
    have hxprod : x ∈ (X.Q 1 : Set G) * (V : Set G) := by
      rw [← hprod]; exact hx'
    obtain ⟨q, hq, w, hw, rfl⟩ := hxprod
    have hqQ0 : q ∈ X.Q 0 := by
      have : q = (q * w) * w⁻¹ := by group
      rw [this]
      exact (X.Q 0).mul_mem hx ((X.Q 0).inv_mem (h5a1 hw))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hq, hqQ0⟩))
      (Subgroup.mem_sup_left hw)
  · exact sup_le h5a1 inf_le_right

private theorem Q1_inf_Q0_le_V_sup_D {X : Setup Γ G} (A : X.CaseA) (W : X.CaseAW1Hyp)
    (hA1eq : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1) :
    X.Q 1 ⊓ X.Q 0 ≤ (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) := by
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)
  set V : Subgroup G := ⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)
  have hZ1V : X.Z 1 ≤ V := le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) (by rw [conjSub_one])
  have hZm1V : X.Z (-1) ≤ V := X.Z_neg_one_le_iSup_conjSub
  have hS0G0 : X.edgeSylow 0 ≤ X.Gi 0 := (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left
  have hS0G1 : X.edgeSylow 0 ≤ X.Gi 1 := (X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right
  have hVN : X.Gi 0 ≤ Subgroup.normalizer (V : Set G) :=
    CFSG.Quasithin.MS93.le_normalizer_iSup_conj (X.Gi 0) (X.Z 1)
  have hQ1G0 : X.Q 1 ≤ X.Gi 0 := (X.Q_le_Gi_adj 1).trans inf_le_left
  have hQ1NV : X.Q 1 ≤ Subgroup.normalizer (V : Set G) := hQ1G0.trans hVN
  have hS0eq : X.edgeSylow 0 = X.Z (-1) ⊔ X.Q 1 := by
    rw [X.edgeSylow_zero]
    exact (X.caseA_pos A).1.symm
  have hQ1Zm1V : ⁅X.Q 1, X.Z (-1)⁆ ≤ V :=
    (Subgroup.commutator_mono le_rfl hZm1V).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hQ1NV)
  have hS0NWA : X.edgeSylow 0 ≤ Subgroup.normalizer ((V ⊔ A1 : Subgroup G) : Set G) := by
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_sup V A1
      ⟨hVN (hS0G0 ha), W.normal (hS0G1 ha)⟩
  have hQ1S0V : ⁅X.Q 1, X.edgeSylow 0⁆ ≤ V ⊔ A1 := by
    rw [hS0eq]
    have hS0NWA' : X.Z (-1) ⊔ X.Q 1 ≤ Subgroup.normalizer ((V ⊔ A1 : Subgroup G) : Set G) := by
      rw [← hS0eq]; exact hS0NWA
    exact CFSG.GroupTheory.commutator_sup_right_le_of_le_normalizer
      (le_sup_left.trans hS0NWA') (le_sup_right.trans hS0NWA')
      (hQ1Zm1V.trans le_sup_left) (W.sec.2.1.trans le_sup_right)
  have hA1VD : A1 ≤ V ⊔ D := by
    rw [hA1eq]
    exact sup_le (le_sup_right) (hZ1V.trans le_sup_left)
  have hVAD : V ⊔ A1 ≤ V ⊔ D := sup_le le_sup_left hA1VD
  rw [← W.comm_edgeSylow_zero_sup]
  exact (sup_le hQ1S0V le_sup_right).trans hVAD

private theorem Q_zero_eq_iSup_conjSub_sup_D {X : Setup Γ G} (A : X.CaseA)
    (W : X.CaseAW1Hyp)
    (hA1eq : X.Q 0 ⊓ X.Q 2 =
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1) :
    X.Q 0 = (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) := by
  obtain ⟨h5a1, -⟩ := X.caseA_5a A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)
  have hQ0eq := X.Q_zero_eq_V_sup_inf A
  have hB0VD := X.Q1_inf_Q0_le_V_sup_D A W hA1eq
  have hDA1 : D ≤ A1 := le_sup_left.trans hA1eq.ge
  have hDQ0 : D ≤ X.Q 0 := hDA1.trans (by rw [hA1]; exact inf_le_left)
  refine le_antisymm ?_ (sup_le h5a1 hDQ0)
  rw [hQ0eq]
  exact sup_le le_sup_left hB0VD

private theorem commutator_le_of_central_elemAbelian {A Z D : Subgroup G}
    (hZA : Z ≤ A) (hDA : D ≤ A)
    (hcentZ : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z)
    (hdecomp : ∀ x ∈ A, ∃ z ∈ Z, ∃ d ∈ D, z * d = x) :
    ⁅A, A⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨za, hza, da, hda, rfl⟩ := hdecomp a ha
  obtain ⟨zb, hzb, db, hdb, rfl⟩ := hdecomp b hb
  have hdaA : da ∈ A := hDA hda
  have hdbA : db ∈ A := hDA hdb
  have h2 : za * zb = zb * za := hcentZ za hza zb (hZA hzb)
  have h3 : za * db = db * za := hcentZ za hza db hdbA
  have h4 : zb * da = da * zb := hcentZ zb hzb da hdaA
  have hcommD : ⁅da, db⁆ ∈ D :=
    D.mul_mem (D.mul_mem (D.mul_mem hda hdb) (D.inv_mem hda)) (D.inv_mem hdb)
  have h6 : za * ⁅da, db⁆ = ⁅da, db⁆ * za := hcentZ za hza _ (hDA hcommD)
  have h7 : zb * ⁅da, db⁆ = ⁅da, db⁆ * zb := hcentZ zb hzb _ (hDA hcommD)
  have hcomm_eq : ⁅za * da, zb * db⁆ = ⁅da, db⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_mul_right_eq_mul_conj]
    have hdazb : ⁅da, zb⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr h4.symm
    have hzazb : ⁅za, zb⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h2
    have hzadb : ⁅za, db⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h3
    rw [hdazb, hzazb, hzadb]
    simp [h2, h6, h7, mul_assoc]
  rw [hcomm_eq]
  exact hcommD

private theorem sq_mem_of_central_elemAbelian {A Z D : Subgroup G}
    (hDA : D ≤ A) (hZelem : IsElemAbelian 2 Z)
    (hcentZ : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z)
    (hdecomp : ∀ x ∈ A, ∃ z ∈ Z, ∃ d ∈ D, z * d = x) :
    ∀ x ∈ A, x ^ 2 ∈ D := by
  intro x hx
  obtain ⟨z, hz, d, hd, hzd⟩ := hdecomp x hx
  have hcent : z * d = d * z := hcentZ z hz d (hDA hd)
  have hz2 : z * z = 1 := by
    have := hZelem.2 z hz
    simpa [pow_two] using this
  have hsq : (z * d) ^ 2 = d ^ 2 := by
    rw [pow_two, pow_two]
    calc z * d * (z * d) = z * (d * z) * d := by group
      _ = z * (z * d) * d := by rw [hcent.symm]
      _ = z * z * (d * d) := by group
      _ = d * d := by rw [hz2, one_mul]
  have hsq' : x ^ 2 = d ^ 2 := by
    rw [← hzd]
    exact hsq
  rw [hsq']
  simpa [pow_two] using D.mul_mem hd hd

private theorem frattini_map_le_of_central_elemAbelian {A Z D : Subgroup G} [Finite ↥A]
    [Fact (IsPGroup 2 ↥A)] (hZA : Z ≤ A) (hDA : D ≤ A) (hZelem : IsElemAbelian 2 Z)
    (hcentZ : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z)
    (hdecomp : ∀ x ∈ A, ∃ z ∈ Z, ∃ d ∈ D, z * d = x) :
    (frattini ↥A).map A.subtype ≤ D := by
  have hcomm_le_D : ⁅A, A⁆ ≤ D :=
    commutator_le_of_central_elemAbelian hZA hDA hcentZ hdecomp
  have hsq_le_D : ∀ x ∈ A, x ^ 2 ∈ D :=
    sq_mem_of_central_elemAbelian hDA hZelem hcentZ hdecomp
  rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥A) (p := 2)]
  rw [MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro x ⟨y, hy, rfl⟩
  rcases hy with hy | ⟨z, rfl⟩
  · have hy' : (y : G) ∈ ⁅A, A⁆ := by
      have himg : Subgroup.map A.subtype (⁅(⊤ : Subgroup ↥A), ⊤⁆ : Subgroup ↥A) = ⁅A,A⁆ := by
        rw [Subgroup.map_commutator]
        congr 1
        · exact (show Subgroup.map A.subtype (⊤ : Subgroup ↥A) = A from by
            simpa using Subgroup.subgroupOf_map_subtype (H := (⊤ : Subgroup G)) (K := A))
        · exact (show Subgroup.map A.subtype (⊤ : Subgroup ↥A) = A from by
            simpa using Subgroup.subgroupOf_map_subtype (H := (⊤ : Subgroup G)) (K := A))
      exact himg ▸ Subgroup.mem_map_of_mem A.subtype hy
    exact hcomm_le_D hy'
  · exact hsq_le_D (z : G) z.2

private theorem inf_Z_one_ne_bot_of_le_Q (X : Setup Γ G) {N : Subgroup G} (hN : N ≠ ⊥)
    (hNQ : N ≤ X.Q 1) (hGN : X.Gi 1 ≤ Subgroup.normalizer (N : Set G)) :
    N ⊓ X.Z 1 ≠ ⊥ := by
  intro hNZ
  set S : Subgroup G := X.edgeSylow 1 with hS
  have hNS : N ≤ S := hNQ.trans (X.Q_le_edgeSylow_left 1)
  have hSGi : S ≤ X.Gi 1 := (X.isSylowTwoOf_edgeSylow 1).1.trans inf_le_left
  haveI : (N.subgroupOf S).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hSGi.trans hGN)
  haveI : Finite ↥S := finite_of_le_stabilizer X.hyp hSGi
  have hNne : N.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hN
    have hinf : N ⊓ S = ⊥ := (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot
    rwa [inf_of_le_left hNS] at hinf
  have hSnil : Group.IsNilpotent ↥S := (X.isPGroup_edgeSylow 1).isNilpotent
  have hcenter : N.subgroupOf S ⊓ Subgroup.center ↥S ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥S) (H := N.subgroupOf S) hNne
  obtain ⟨x, hx, hxne⟩ := Subgroup.exists_mem_ne_one_of_ne_bot hcenter
  have hxN : (x : G) ∈ N := Subgroup.mem_subgroupOf.mp hx.1
  have hxcentS : (x : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx.2 (⟨y, hy⟩ : ↥S))
  have hSylGi : IsSylowTwoOf S (X.Gi 1) := by
    have h := isSylowTwoOf_of_edgeStab X.hyp (X.adj 1) (X.isSylowTwoOf_edgeSylow 1)
    simpa [S] using h
  have hxZ : (x : G) ∈ X.Z 1 := by
    have hle : centerOf S ⊓ X.Q 1 ≤ X.Z 1 :=
      le_iSup₂_of_le S hSylGi le_rfl
    exact hle ⟨⟨x.2, hxcentS⟩, hNQ hxN⟩
  have hxbot : (x : G) ∈ N ⊓ X.Z 1 := ⟨hxN, hxZ⟩
  rw [hNZ] at hxbot
  exact hxne (Subtype.ext (Subgroup.mem_bot.mp hxbot))

private theorem A1_elem_of_decomp (X : Setup Γ G) (A : X.CaseA)
    (hA1eq : X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1)
    (hDZ1 : (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥) :
    IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) := by
  obtain ⟨-, -, -, -, -, hNatZ1, -, -⟩ := X.caseA_3 A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hD
  have hAGi : X.Gi 1 ≤ Subgroup.normalizer (A1 : Set G) := (X.caseA_5b A).1
  have hAQ1 : A1 ≤ X.Q 1 :=
    (X.Q_quot A.hyp.char A.hyp.sing (by omega : 4 ≤ 7) 1).1
  have hZelem : IsElemAbelian 2 (X.Z 1) := X.isElemAbelian_Z_of_natQuot 1 hNatZ1
  have hZiA : X.Z 1 ≤ A1 := by
    rw [hA1]
    exact le_inf (X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num))
      (X.Z_le_Q_of_lt A.b₁ (j := 2) (by norm_num))
  have hDle : D ≤ A1 := by rw [hA1eq]; exact le_sup_left
  have hA1p : IsPGroup 2 A1 := (pCoreOf_isPGroup' (X.Gi 1)).to_le hAQ1
  haveI : Finite ↥A1 :=
    finite_of_le_stabilizer X.hyp (hAQ1.trans (X.Q_le_Gi 1))
  haveI : Fact (IsPGroup 2 ↥A1) := ⟨hA1p⟩
  have hcentZ : ∀ z ∈ X.Z 1, ∀ a ∈ A1, z * a = a * z := by
    intro z hz a ha
    have hza : z ∈ Subgroup.centralizer (X.Q 1 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 1 hz)).2
    exact (Subgroup.mem_centralizer_iff.mp hza a (hAQ1 ha)).symm
  have hZnormD : X.Z 1 ≤ Subgroup.normalizer (D : Set G) := fun z hz =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun d hd => (hcentZ z hz d (hDle hd)).symm)
  have hdecomp : ∀ x ∈ A1, ∃ z ∈ X.Z 1, ∃ d ∈ D, z * d = x := by
    intro x hx
    have hx' : x ∈ X.Z 1 ⊔ D := by
      rw [sup_comm, ← hA1eq]
      exact hx
    have hx'' : x ∈ (X.Z 1 : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right (X.Z 1) D hZnormD]
      exact hx'
    obtain ⟨z, hz, d, hd, hzd⟩ := hx''
    exact ⟨z, hz, d, hd, hzd⟩
  have hP_le_D : (frattini ↥A1).map A1.subtype ≤ D :=
    frattini_map_le_of_central_elemAbelian hZiA hDle hZelem hcentZ hdecomp
  have hPZ : ((frattini ↥A1).map A1.subtype) ⊓ X.Z 1 = ⊥ := by
    rw [eq_bot_iff]
    exact (inf_le_inf hP_le_D le_rfl).trans (le_of_eq hDZ1)
  have hfr_bot : frattini ↥A1 = ⊥ := by
    by_contra hfr_ne
    have hPne : (frattini ↥A1).map A1.subtype ≠ ⊥ := by
      intro h
      exact hfr_ne (Subgroup.map_injective A1.subtype_injective
        (by rw [h, Subgroup.map_bot]))
    have hGN : X.Gi 1 ≤
        Subgroup.normalizer ((frattini ↥A1).map A1.subtype : Set G) :=
      hAGi.trans
        (CFSG.BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
          A1 (frattini ↥A1))
    exact X.inf_Z_one_ne_bot_of_le_Q hPne (hP_le_D.trans (hDle.trans hAQ1)) hGN hPZ
  haveI hEA : CFSG.IsElementaryAbelian 2 ↥A1 :=
    (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥A1) (p := 2)).mp hfr_bot
  exact ⟨inferInstance, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩

private theorem A1_eq_D_sup_Z1 (X : Setup Γ G) (A : X.CaseA) (W : X.CaseAW1Hyp)
    {k : G} (hkKi : k ∈ X.Ki 1) (hk1 : k ≠ 1) :
    (X.Q 0 ⊓ X.Q 2 = (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1) ∧
      X.Ki 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) ∧
      ⁅X.Q 0 ⊓ X.Q 2, X.Ki 1⁆ ≤ X.Z 1 := by
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hD
  have hA1Q1 : A1 ≤ X.Q 1 := by rw [hA1]; exact W.sec.1
  have hZ1A1 : X.Z 1 ≤ A1 := by
    rw [hA1]
    exact le_inf (X.Z_le_Q_of_lt A.b₁ (j := 0) (by norm_num))
      (X.Z_le_Q_of_lt A.b₁ (j := 2) (by norm_num))
  have hDA1 : D ≤ A1 := by
    intro x hx
    obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxk : ⁅x, k⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp hxC k hkKi).symm
    exact W.fpf k hkKi.2 (X.odd_orderOf_of_mem_Ki hkKi) hk1 x hxQ
      (by rw [hxk]; exact A1.one_mem)
  have hKA1 : X.Ki 1 ≤
      Subgroup.normalizer ((X.Q 0 ⊓ X.Q 2 : Subgroup G) : Set G) :=
    fun y hy => W.normal (X.K_le_Gi 1 hy.1)
  obtain ⟨-, h5b2⟩ := X.caseA_5b A
  have hn1 : 0 < X.n 1 := by
    have := A.hyp.two_le_n 1
    omega
  have hK1O2 : X.Ki 1 ≤ oTwoRes (X.L 1) :=
    le_oTwoRes_of_odd_card inf_le_right (by
      rw [X.card_Ki 1]
      exact Nat.Even.sub_odd Nat.one_le_two_pow
        (Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hn1⟩) odd_one)
  have hALKi : ⁅A1, X.Ki 1⁆ ≤ X.Z 1 := by
    rw [hA1]
    exact (Subgroup.commutator_mono le_rfl hK1O2).trans h5b2
  have hA1solv : Group.IsSolvable ↥A1 := by
    have hA1p : IsPGroup 2 A1 := (pCoreOf_isPGroup' (X.Gi 1)).to_le hA1Q1
    haveI : Finite ↥A1 := finite_of_le_stabilizer X.hyp (hA1Q1.trans (X.Q_le_Gi 1))
    haveI : Group.IsNilpotent ↥A1 := hA1p.isNilpotent
    infer_instance
  have hA1le : A1 ≤ D ⊔ X.Z 1 :=
    X.Q_inf_Q_le_D_sup_Z_one_of_solvable hKA1 hA1Q1 hA1solv
      (by simpa [hA1] using hALKi)
  refine ⟨le_antisymm hA1le (sup_le hDA1 hZ1A1), hKA1, ?_⟩
  simpa [hA1] using hALKi

theorem caseA_5d (X : Setup Γ G) (A : X.CaseA) :
    (X.Q 0 ⊓ X.Q 2) =
        (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊔ X.Z 1 ∧
      (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) ⊓ X.Z 1 = ⊥ ∧
      Nat.card ↥(X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) = 2 ^ X.n 0 ∧
      IsElemAbelian 2 (X.Q 0 ⊓ X.Q 2) ∧
      ⁅X.Q 0 ⊓ X.Q 2, X.L 1⁆ ≤ X.Z 1 ∧
      X.Q 0 = (⨆ g ∈ X.Gi 0, conjSub g (X.Z 1)) ⊔
        (X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G)) := by
  have W := X.caseA_w1Hyp A
  set A1 : Subgroup G := X.Q 0 ⊓ X.Q 2 with hA1
  set D : Subgroup G := X.Q 1 ⊓ Subgroup.centralizer (X.Ki 1 : Set G) with hD
  obtain ⟨k, hkKi, hk1, -, -⟩ := X.exists_generator_Ki 1 (A.hyp.two_le_n 1)
  obtain ⟨hA1eq, hKA1, hALKi⟩ := X.A1_eq_D_sup_Z1 A W hkKi hk1
  have hA1eqD : A1 = D ⊔ X.Z 1 := by simpa [hA1, hD] using hA1eq
  obtain ⟨hDZ1, hDcard⟩ := X.D_inf_Z_one_eq_bot_and_card A hkKi hk1 hA1eq
  have hA1elem : IsElemAbelian 2 A1 := by
    simpa [hA1] using X.A1_elem_of_decomp A hA1eq hDZ1
  have hA1le' : A1 ≤ D ⊔ X.Z 1 :=
    X.Q_inf_Q_le_D_sup_Z_one hKA1 W.sec.1 (by simpa [hA1] using hA1elem) hALKi
  have hDA1 : D ≤ A1 := hA1eqD.symm ▸ le_sup_left
  have hZ1A1 : X.Z 1 ≤ A1 := hA1eqD.symm ▸ le_sup_right
  have hA1eq' : A1 = D ⊔ X.Z 1 := le_antisymm hA1le' (sup_le hDA1 hZ1A1)
  have hL1A1 := X.commutator_L_one_Q_inf_Q_le_Z_one A W (by simpa [hA1] using hA1elem)
  have hQ0WD := X.Q_zero_eq_iSup_conjSub_sup_D A W (by simpa [hA1, hD] using hA1eq')
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hA1, hD] using hA1eq'
  · simpa [hD] using hDZ1
  · simpa [hD] using hDcard
  · simpa [hA1] using hA1elem
  · rw [Subgroup.commutator_comm]
    simpa [hA1] using hL1A1
  · exact hQ0WD

end Setup

end CFSG.Quasithin.St84
