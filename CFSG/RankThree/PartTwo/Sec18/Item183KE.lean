module

public import CFSG.RankThree.PartTwo.Sec18.Item183KDiag
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseI

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item183K

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M K S : Subgroup G} {c : G}

theorem diag183_of_mem (h : Hyp183 G A M c K) (hS : SylowS A K S)
    (hC : ∃ w : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers w : Set G))
    {a x : G} (ha : a ∈ A) (haC : a ∉ Subgroup.zpowers c) (haK : a ∉ K) (hx : x ∈ S ⊓ K)
    (hxa : x⁻¹ * a ∈ Sec4.thetaQuotCentralizer K) :
    Diag183 G A M c K
      (Subgroup.zpowers c ⊔ Subgroup.zpowers x ⊔ Subgroup.zpowers (x⁻¹ * a)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Sec4.thetaQuotCentralizer K with hCdef
  set s := x⁻¹ * a with hsdef
  set E₀ := Subgroup.zpowers c ⊔ Subgroup.zpowers x with hE₀
  set E := E₀ ⊔ Subgroup.zpowers s with hE
  have hcK : c ∈ K := c_mem_K h hS hC
  have hCA : A ⊓ C = Subgroup.zpowers c := inf_C_eq h hC
  have hcC : c ∈ C := h.c_mem_C
  have hc3 : c ^ 3 = 1 := h.pow_three h.mem_A
  have hco : orderOf c = 3 := orderOf_c h
  have hxS : x ∈ S := hx.1
  have hxK : x ∈ K := hx.2
  have hsS : s ∈ S := S.mul_mem (S.inv_mem hxS) (hS.le ha)
  have hxs_a : x * s = a := by rw [hsdef]; group
  have hcx : c * x = x * c :=
    (Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hxK)).symm
  have hca : c * a = a * c := h.commute h.mem_A ha
  have hcs : c * s = s * c :=
    ((Commute.inv_right (show Commute c x from hcx)).mul_right (show Commute c a from hca)).eq
  have hxs : x * s = s * x := (commute_of_mem_C h hS hsS hxa hx).symm
  have hx3 : x ^ 3 = 1 := pow_three_of_mem_inf h hS hx
  have hs3 : s ^ 3 = 1 := by
    have h1 : (x * s) ^ 3 = x ^ 3 * s ^ 3 := (show Commute x s from hxs).mul_pow 3
    rw [hxs_a, h.pow_three ha, hx3, one_mul] at h1
    exact h1.symm
  have hxC : x ∉ C := fun hxC => haC (by
    rw [← hCA]
    exact ⟨ha, hxs_a ▸ C.mul_mem hxC hxa⟩)
  have hsK : s ∉ K := fun hsK => haK (hxs_a ▸ K.mul_mem hxK hsK)
  have hzK : Subgroup.zpowers c ≤ K := Subgroup.zpowers_le.mpr hcK
  have hzC : Subgroup.zpowers c ≤ C := Subgroup.zpowers_le.mpr hcC
  have hzA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr h.mem_A
  have hxc : x ∉ Subgroup.zpowers c := fun h' => hxC (hzC h')
  have hsc : s ∉ Subgroup.zpowers c := fun h' => hsK (hzK h')
  have hsCA : s ∉ A := fun hsA => hsc (by rw [← hCA]; exact ⟨hsA, hxa⟩)
  have hE₀ab : CFSG.Assembly.IsElemAbelian 3 E₀ := Sec13.isElemAbelian_zpowers_sup hc3 hx3 hcx
  have hE₀9 : Nat.card E₀ = 9 := Sec4.card_zpowers_sup_zpowers hx3 hco hxc hcx.symm
  have hE₀K : E₀ ≤ K := sup_le hzK (Subgroup.zpowers_le.mpr hxK)
  have hsE₀ : s ∉ E₀ := fun hs => hsK (hE₀K hs)
  have hE₀s : ∀ e ∈ E₀, e * s = s * e := by
    have hle : E₀ ≤ Subgroup.centralizer ({s} : Set G) := sup_le
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcs))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxs))
    exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hle he)
  have hE27 : IsE27 E := isE27_sup_zpowers hE₀ab hE₀9 hsE₀ hs3 hE₀s
  have hcE : c ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hxE : x ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hsE : s ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have haE : a ∈ E := hxs_a ▸ E.mul_mem hxE hsE
  have hzE : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hcE
  have hcomm : ∀ b ∈ A, x * b * x⁻¹ * b⁻¹ ∈ Subgroup.zpowers c :=
    fun b hb => commutator_mem_zpowers h hS hC ha hx hxa hb
  have hxN : x ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have e : x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact A.mul_mem (hzA (hcomm b hb)) hb
  have hsN : s ∈ Subgroup.normalizer (A : Set G) :=
    mul_mem (inv_mem hxN) (Subgroup.le_normalizer ha)
  have hEN : E ≤ Subgroup.normalizer (A : Set G) :=
    sup_le (sup_le (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer h.mem_A))
      (Subgroup.zpowers_le.mpr hxN)) (Subgroup.zpowers_le.mpr hsN)
  have hAE : A ≤ Subgroup.normalizer (E : Set G) := by
    intro b hb
    have hle : E ≤ E.comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_))
        (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          h.commute hb h.mem_A, mul_inv_cancel_right]
        exact hcE
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have e : b * x * b⁻¹ = (x * b * x⁻¹ * b⁻¹)⁻¹ * x := by group
        rw [e]
        exact E.mul_mem (E.inv_mem (hzE (hcomm b hb))) hxE
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hba : b * a * b⁻¹ = a := by rw [h.commute hb ha, mul_inv_cancel_right]
        have e : b * s * b⁻¹ = x⁻¹ * (x * b * x⁻¹ * b⁻¹) * (b * a * b⁻¹) := by
          rw [hsdef]
          group
        rw [e, hba]
        exact E.mul_mem (E.mul_mem (E.inv_mem hxE) (hzE (hcomm b hb))) haE
    exact Subgroup.mem_normalizer_fintype fun n hn => hle hn
  have hEle : E ≤ (A ⊔ K) ⊓ Subgroup.normalizer (A : Set G) :=
    le_inf (sup_le (sup_le (hzA.trans le_sup_left)
      ((Subgroup.zpowers_le.mpr hxK).trans le_sup_right))
      ((Subgroup.zpowers_le.mpr hsS).trans hS.le_sup)) hEN
  have hENK : E ≤ Subgroup.normalizer (K : Set G) :=
    hEle.trans (inf_le_left.trans h.sup_le_normalizer)
  have hEK : ¬ ∃ y : G, ((E ⊓ K : Subgroup G) : Set G) ⊆ (Subgroup.zpowers y : Set G) :=
    not_subset_zpowers_of_le (D := E₀) (le_inf le_sup_left hE₀K) hE₀ab.2 hE₀9.ge
  have hE₁ab : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers s) :=
    Sec13.isElemAbelian_zpowers_sup hc3 hs3 hcs
  have hE₁9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers s : Subgroup G) = 9 :=
    Sec4.card_zpowers_sup_zpowers hs3 hco hsc hcs.symm
  have hE₁le : Subgroup.zpowers c ⊔ Subgroup.zpowers s ≤ E ⊓ C :=
    le_inf (sup_le hzE (Subgroup.zpowers_le.mpr hsE))
      (sup_le hzC (Subgroup.zpowers_le.mpr hxa))
  have hEC : ¬ ∃ y : G, sectionCentralizer E K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers y : Set G) := by
    rw [h.sectionCentralizer_eq hENK]
    exact not_subset_zpowers_of_le hE₁le hE₁ab.2 hE₁9.ge
  have hEE : E ∈ partTwoE G := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨hE27.1, hE27.2, CFSG.Open.pCoreOf 2 M,
      pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM.1,
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M, ?_⟩
    have hNM : Subgroup.normalizer (A : Set G) ≤ M :=
      (normalizer_le_gamma le_rfl (by rw [h.isE27.pRank_eq]; norm_num)).trans
        fun y hy => h.mem_scriptM.2 hy
    exact (hEN.trans hNM).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M)
  have hbar : Sec12.Sec12StdBar G E c K := by
    refine ⟨h.toPartTwoStanding, (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1,
      hE27, hcE, h.ne_one, h.mem_thetaComponentsAt, hcK, ?_, ?_, ?_⟩
    · refine card_eq_nine_of_le hE27 inf_le_left
        (hE₁9.ge.trans (Subgroup.card_le_of_le hE₁le)) fun heq => hxC ?_
      have hx' : x ∈ E ⊓ C := by rw [heq]; exact hxE
      exact hx'.2
    · refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
      refine sup_le (sup_le ?_ ?_) ?_
      · exact (le_inf hzE hzK).trans le_sup_right
      · exact (le_inf (Subgroup.zpowers_le.mpr hxE) (Subgroup.zpowers_le.mpr hxK)).trans
          le_sup_right
      · exact (le_inf (Subgroup.zpowers_le.mpr hsE) (Subgroup.zpowers_le.mpr hxa)).trans
          le_sup_left
    · set H := Subgroup.normalizer (E : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
      have hAH : A ≤ H := fun b hb =>
        ⟨hAE hb, Sec12.mem_normalizer_zpowers_of_commute (h.commute hb h.mem_A)⟩
      obtain ⟨Q, hQ⟩ := (h.isE27.isPGroup.comap_subtype (K := H)).exists_le_sylow
      refine ⟨(Q : Subgroup H).map H.subtype, ⟨Q, rfl⟩, fun hle => ?_⟩
      have hAP : ∀ b ∈ A, b ∈ (Q : Subgroup H).map H.subtype := fun b hb =>
        ⟨⟨b, hAH hb⟩, hQ (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
      obtain ⟨z, hz, hzs⟩ := hle ⟨hsE, hxa⟩
      refine hsCA (h.mem_of_commute hs3 fun b hb => ?_)
      have h1 := Subgroup.mem_center_iff.mp hz ⟨b, hAP b hb⟩
      rw [← hzs]
      exact congrArg Subtype.val h1
  have hinf : A ⊓ K = Subgroup.zpowers c := by
    refine le_antisymm (fun a' ha' => ?_) (le_inf hzA hzK)
    by_contra ha'c
    have ha'3 : a' ^ 3 = 1 := h.pow_three ha'.1
    have ha'S : a' ∈ S ⊓ K := ⟨hS.le ha'.1, ha'.2⟩
    have hDab : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers a') :=
      Sec13.isElemAbelian_zpowers_sup hc3 ha'3 (h.commute h.mem_A ha'.1)
    have hD9 : Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers a' : Subgroup G) = 9 :=
      Sec4.card_zpowers_sup_zpowers ha'3 hco ha'c (h.commute ha'.1 h.mem_A)
    have hDA : Subgroup.zpowers c ⊔ Subgroup.zpowers a' ≤ A :=
      sup_le hzA (Subgroup.zpowers_le.mpr ha'.1)
    have hxD : x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers a' := fun hxD => hsCA (by
      rw [hsdef]
      exact A.mul_mem (A.inv_mem (hDA hxD)) ha)
    have ha's : s * a' = a' * s := commute_of_mem_C h hS hsS hxa ha'S
    have hxa' : x = a * s⁻¹ := by rw [hsdef]; group
    have hDx : ∀ e ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers a', e * x = x * e := by
      have hcen : Subgroup.zpowers c ⊔ Subgroup.zpowers a' ≤
          Subgroup.centralizer ({x} : Set G) := by
        refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.mpr hcx
        · rw [Subgroup.mem_centralizer_singleton_iff, hxa']
          exact ((show Commute a' a from h.commute ha'.1 ha).mul_right
            (show Commute a' s from ha's.symm).inv_right).eq
      exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hcen he)
    have h27 := isE27_sup_zpowers hDab hD9 hxD hx3 hDx
    exact h.false_of_isE27_le h27 (sup_le (sup_le hzK (Subgroup.zpowers_le.mpr ha'.2))
      (Subgroup.zpowers_le.mpr hxK))
  have hsec : sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) = (Subgroup.zpowers c : Set G) := by
    rw [h.sectionCentralizer_eq h.le_normalizer, hCA]
  exact ⟨h, hcK, hsec, hinf, hEE, hEle, hAE, hEK, hEC, hbar⟩

theorem exists_E_of_cyclic (h : Hyp183 G A M c K)
    (hC : ∃ w : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers w : Set G)) :
    ∃ E : Subgroup G, Diag183 G A M c K E := by
  obtain ⟨S, hS⟩ := exists_sylowS h
  obtain ⟨a, ha, haC, haK⟩ := exists_a h
  obtain ⟨x, hx, hxa⟩ := exists_actsLike h hS ha
  exact ⟨_, diag183_of_mem h hS hC ha haC haK hx hxa⟩

theorem inf_noncyclic_of_not_cyclic (h : Hyp183 G A M c K)
    (hC : ¬ ∃ x : G, sectionCentralizer A K (CFSG.Open.pCoreOf 2 K) ⊆
      (Subgroup.zpowers x : Set G)) :
    ¬ ∃ x : G, ((A ⊓ K : Subgroup G) : Set G) ⊆ (Subgroup.zpowers x : Set G) := by
  obtain ⟨S, hS⟩ := exists_sylowS h
  exact inf_noncyclic_of_not_cyclic_aux h hS hC

end CFSG.RankThree.PartTwo.Sec18.Item183K
