module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.SplitExtAut

public section

open Subgroup
open scoped Pointwise

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {B : Type*} [Group B]

theorem IsCrossedHom.mul {K E : Subgroup B} [E.Normal] [IsMulCommutative E]
    {f g : ↥K → ↥E} (hf : IsCrossedHom K E f) (hg : IsCrossedHom K E g) :
    IsCrossedHom K E (fun k => f k * g k) := by
  intro k₁ k₂
  have hA : (k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹ ∈ E :=
    (inferInstance : E.Normal).conj_mem (f k₂ : B) (f k₂).2 (k₁ : B)
  have hD : (k₁ : B) * (g k₂ : B) * (k₁ : B)⁻¹ ∈ E :=
    (inferInstance : E.Normal).conj_mem (g k₂ : B) (g k₂).2 (k₁ : B)
  let Ae : ↥E := ⟨(k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹, hA⟩
  let De : ↥E := ⟨(k₁ : B) * (g k₂ : B) * (k₁ : B)⁻¹, hD⟩
  have hAe : (Ae : B) = (k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹ := rfl
  have hDe : (De : B) = (k₁ : B) * (g k₂ : B) * (k₁ : B)⁻¹ := rfl
  have hsplit : (k₁ : B) * (((f k₂ * g k₂ : ↥E) : B)) * (k₁ : B)⁻¹ =
      (Ae : B) * (De : B) := by
    rw [Subgroup.coe_mul, hAe, hDe]
    group
  rw [Subgroup.coe_mul, hf k₁ k₂, hg k₁ k₂, Subgroup.coe_mul, hsplit]
  have hcomm : (Ae : B) * (g k₁ : B) = (g k₁ : B) * (Ae : B) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, mul_comm' Ae (g k₁)]
  rw [← hAe, ← hDe]
  calc
    (f k₁ : B) * (Ae : B) * ((g k₁ : B) * (De : B))
        = (f k₁ : B) * ((Ae : B) * (g k₁ : B)) * (De : B) := by group
    _ = (f k₁ : B) * ((g k₁ : B) * (Ae : B)) * (De : B) := by rw [hcomm]
    _ = (f k₁ : B) * (g k₁ : B) * ((Ae : B) * (De : B)) := by group

theorem IsCrossedHom.inv {K E : Subgroup B} [E.Normal] [IsMulCommutative E]
    {f : ↥K → ↥E} (hf : IsCrossedHom K E f) :
    IsCrossedHom K E (fun k => (f k)⁻¹) := by
  intro k₁ k₂
  have hA : (k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹ ∈ E :=
    (inferInstance : E.Normal).conj_mem (f k₂ : B) (f k₂).2 (k₁ : B)
  let Ae : ↥E := ⟨(k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹, hA⟩
  have hAe : (Ae : B) = (k₁ : B) * (f k₂ : B) * (k₁ : B)⁻¹ := rfl
  have hinvA : (k₁ : B) * (f k₂ : B)⁻¹ * (k₁ : B)⁻¹ = (Ae : B)⁻¹ := by
    rw [hAe]
    group
  rw [Subgroup.coe_inv, hf k₁ k₂, Subgroup.coe_inv, Subgroup.coe_inv, hinvA]
  rw [mul_inv_rev, ← hAe]
  simpa using congrArg (fun e : ↥E => (e : B))
    (mul_comm' (M := ↥E) (Ae⁻¹) ((f k₁)⁻¹))

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

section CrossedHomSubgroup

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {B : Type*} [Group B]

noncomputable def crossedHomSubgroup (K E : Subgroup B) [E.Normal] [IsMulCommutative E]
    (D : Subgroup K) : Subgroup (↥K → ↥E) where
  carrier := {f | IsCrossedHom K E f ∧ ∀ d : D, f d = 1}
  mul_mem' := by
    rintro f g ⟨hf, hfv⟩ ⟨hg, hgv⟩
    refine ⟨hf.mul hg, ?_⟩
    intro d
    show f d * g d = 1
    rw [hfv d, hgv d, one_mul]
  one_mem' := ⟨by intro k₁ k₂; simp, by intro d; rfl⟩
  inv_mem' := by
    rintro f ⟨hf, hfv⟩
    refine ⟨hf.inv, ?_⟩
    intro d
    show (f d)⁻¹ = 1
    rw [hfv d, inv_one]

theorem odd_card_crossedHomSubgroup [Finite B] {K E : Subgroup B} [E.Normal]
    [IsMulCommutative E] (D : Subgroup K) (hEodd : Odd (Nat.card E)) :
    Odd (Nat.card (crossedHomSubgroup K E D)) := by
  have hamb : Odd (Nat.card (↥K → ↥E)) := by
    rw [Nat.card_fun]
    exact hEodd.pow
  exact Odd.of_dvd_nat hamb (Subgroup.card_subgroup_dvd_card _)

abbrev ComplementsContaining (E K : Subgroup B) (D : Subgroup K) : Type _ :=
  {K' : Subgroup B // E.IsComplement' K' ∧ D.map K.subtype ≤ K'}

noncomputable def complementEquivCrossedHom {K E : Subgroup B} [E.Normal]
    [IsMulCommutative E] (hK : E.IsComplement' K) (D : Subgroup K) :
    ComplementsContaining E K D ≃ crossedHomSubgroup K E D := by
  classical
  let phi : ComplementsContaining E K D → ↥K → ↥E :=
    fun K' => Classical.choose (existsUnique_isCrossedHom_of_isComplement' hK.sup_eq_top K'.2.1)
  have phi_spec (K' : ComplementsContaining E K D) :
      IsCrossedHom K E (phi K') ∧
        ∀ x : B, x ∈ K'.1 ↔ ∃ k : ↥K, x = (phi K' k : B) * (k : B) :=
    (Classical.choose_spec (existsUnique_isCrossedHom_of_isComplement' hK.sup_eq_top K'.2.1)).1
  let toFun : ComplementsContaining E K D → crossedHomSubgroup K E D := fun K' => by
    refine ⟨phi K', (phi_spec K').1, ?_⟩
    intro d
    have hdK' : ((d : K) : B) ∈ K'.1 := K'.2.2 ⟨(d : K), d.2, rfl⟩
    have hfdK' : (phi K' d : B) * ((d : K) : B) ∈ K'.1 :=
      ((phi_spec K').2 ((phi K' d : B) * ((d : K) : B))).mpr ⟨(d : K), rfl⟩
    have hmem : (phi K' d : B) ∈ E ⊓ K'.1 := by
      refine ⟨(phi K' d).2, ?_⟩
      have h : (phi K' d : B) = ((phi K' d : B) * ((d : K) : B)) * ((d : K) : B)⁻¹ := by
        group
      rw [h]
      exact K'.1.mul_mem hfdK' (K'.1.inv_mem hdK')
    have hbot : (phi K' d : B) ∈ (⊥ : Subgroup B) := by
      rw [← K'.2.1.disjoint.eq_bot]
      exact hmem
    exact Subtype.ext (by simpa using hbot)
  let fromFun : crossedHomSubgroup K E D → ComplementsContaining E K D := fun f => by
    refine ⟨f.2.1.graph, f.2.1.isComplement'_graph hK.disjoint.eq_bot hK.sup_eq_top, ?_⟩
    rintro x ⟨d, hd, rfl⟩
    have hfd : f.1 (d : K) = 1 := by
      simpa using f.2.2 ⟨d, hd⟩
    refine (f.2.1.mem_graph).mpr ⟨(d : K), ?_⟩
    show ((d : K) : B) = (f.1 (d : K) : B) * ((d : K) : B)
    rw [hfd, Subgroup.coe_one, one_mul]
  refine ⟨toFun, fromFun, ?_, ?_⟩
  · intro K'
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    exact (phi_spec K').2 x |>.symm
  · intro f
    apply Subtype.ext
    funext k
    have huniq := (Classical.choose_spec (existsUnique_isCrossedHom_of_isComplement' hK.sup_eq_top
      (fromFun f).2.1)).2
    have hP : IsCrossedHom K E f.1 ∧
        ∀ x : B, x ∈ f.2.1.graph ↔ ∃ k : ↥K, x = (f.1 k : B) * (k : B) :=
      ⟨f.2.1, fun x => f.2.1.mem_graph⟩
    have h := huniq f.1 hP
    exact (congrFun h k).symm

theorem odd_card_complements [Finite B] {K E : Subgroup B} [E.Normal] [IsMulCommutative E]
    (hK : E.IsComplement' K) (D : Subgroup K) (hEodd : Odd (Nat.card E)) :
    Odd (Nat.card (ComplementsContaining E K D)) := by
  rw [Nat.card_congr (complementEquivCrossedHom hK D)]
  exact odd_card_crossedHomSubgroup D hEodd



end CrossedHomSubgroup

section Main

open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

variable {Q : Type*} [Group Q] [Finite Q]

theorem exists_complement_normalized_of_odd {N M B X₀ S R : Subgroup Q} (hBM : B ≤ M)
    (hMN : M ≤ N) (hBn : N ≤ normalizer (B : Set Q)) (hMn : N ≤ normalizer (M : Set Q))
    (hMB : ⁅M, M⁆ ≤ B) (hodd : Odd (B.relIndex M)) (hBX : B ≤ X₀) (hX₀N : X₀ ≤ N)
    (hX₀M : X₀ ⊓ M = B) (hX₀sup : X₀ ⊔ M = N) (hSX : S ≤ X₀) (hR : IsPGroup 2 R)
    (hRN : R ≤ normalizer (N : Set Q)) (hRM : R ≤ normalizer (M : Set Q))
    (hRB : R ≤ normalizer (B : Set Q)) (hRS : R ≤ normalizer (S : Set Q)) :
    ∃ X : Subgroup Q, B ≤ X ∧ X ≤ N ∧ X ⊓ M = B ∧ X ⊔ M = N ∧ S ≤ X ∧
      R ≤ normalizer (X : Set Q) := by
  let build : {X : Subgroup Q // B ≤ X ∧ X ≤ N ∧ X ⊓ M = B ∧ X ⊔ M = N ∧ S ≤ X ∧
      R ≤ Subgroup.normalizer (X : Set Q)} := by
    let X0 : Subgroup Q := X₀
    have hX0N : X0 ≤ N := hX₀N
    have hX0M : X0 ⊓ M = B := hX₀M
    have hX0sup : X0 ⊔ M = N := hX₀sup
    have subgroupOf_inf_eq {H K L : Subgroup Q} (_hH : H ≤ L) (_hK : K ≤ L) :
        (H ⊓ K).subgroupOf L = H.subgroupOf L ⊓ K.subgroupOf L := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    let B' : Subgroup N := B.subgroupOf N
    have hBN : B ≤ N := le_trans hBM hMN
    have hB'normal : B'.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBN).mpr hBn
    letI : B'.Normal := hB'normal
    let q : N →* N ⧸ B' := QuotientGroup.mk' B'
    have map_inf_eq {A B : Subgroup N} (hB : q.ker ≤ B) :
        (A ⊓ B).map q = A.map q ⊓ B.map q := by
      refine le_antisymm (Subgroup.map_inf_le A B q) ?_
      intro z hz
      rw [Subgroup.mem_inf] at hz
      obtain ⟨hzA, hzB⟩ := hz
      obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.mp hzA
      obtain ⟨y, hyB, hy⟩ := Subgroup.mem_map.mp hzB
      have hker' : x⁻¹ * y ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
      have hxB : x ∈ B := by
        have hmem : (x⁻¹ * y)⁻¹ ∈ B := B.inv_mem (hB hker')
        have hx : x = y * (x⁻¹ * y)⁻¹ := by group
        rw [hx]
        exact B.mul_mem hyB hmem
      exact ⟨x, ⟨hxA, hxB⟩, rfl⟩
    let M' : Subgroup N := M.subgroupOf N
    let X0' : Subgroup N := X0.subgroupOf N
    let S' : Subgroup N := S.subgroupOf N
    let E : Subgroup (N ⧸ B') := M'.map q
    let K : Subgroup (N ⧸ B') := X0'.map q
    let D : Subgroup K := (S'.map q).subgroupOf K
    have hM'normal : M'.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mpr hMn
    have hE_normal : E.Normal := hM'normal.map q (QuotientGroup.mk'_surjective B')
    letI : E.Normal := hE_normal
    have hB'M' : B' ≤ M' := Subgroup.subgroupOf_mono N hBM
    have hB'X0' : B' ≤ X0' := Subgroup.subgroupOf_mono N hBX
    have hker : B'.map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      exact le_of_eq (QuotientGroup.ker_mk' B').symm
    have hcomm : ⁅M', M'⁆ ≤ B' := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      exact hMB (Subgroup.commutator_mem_commutator hx hy)
    have hE_comm : IsMulCommutative E := by
      have hbot : ⁅E, E⁆ = ⊥ := by
        rw [show E = M'.map q from rfl, ← Subgroup.map_commutator]
        exact le_bot_iff.mp ((Subgroup.map_mono hcomm).trans (le_of_eq hker))
      exact (Subgroup.le_centralizer_iff_isMulCommutative).mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot)
    letI : IsMulCommutative E := hE_comm
    have hM'X0' : M' ⊓ X0' = B' := by
      rw [← subgroupOf_inf_eq hMN hX0N, inf_comm, hX0M]
    have hM'X0'sup : M' ⊔ X0' = ⊤ := by
      apply (Subgroup.map_subtype_inj (H := N)).mp
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hMN,
        Subgroup.map_subgroupOf_eq_of_le hX0N, sup_comm, hX0sup, Subgroup.map_top,
        Subgroup.range_subtype]
    have hinf : E ⊓ K = ⊥ := by
      rw [show E = M'.map q from rfl, show K = X0'.map q from rfl,
        ← map_inf_eq (by rwa [QuotientGroup.ker_mk']), hM'X0']
      exact hker
    have hsup : E ⊔ K = ⊤ := by
      rw [show E = M'.map q from rfl, show K = X0'.map q from rfl,
        ← Subgroup.map_sup, hM'X0'sup,
        Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective B')]
    have hcomp : E.IsComplement' K :=
      isComplement'_iff_inf_eq_bot_and_sup_eq_top.2 ⟨hinf, hsup⟩
    have hDmap : D.map K.subtype = S'.map q := by
      rw [show D = (S'.map q).subgroupOf K from rfl,
        Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono (Subgroup.subgroupOf_mono N hSX))]
    have hcardE : Nat.card E = B.relIndex M := by
      have h1 : Nat.card E = Nat.card (M' ⧸ B'.subgroupOf M') := by
        change Nat.card (M'.map q) = Nat.card (M' ⧸ B'.subgroupOf M')
        exact Nat.card_congr (CFSG.quotientSubgroupRangeEquiv M' B').symm
      rw [h1]
      change B'.relIndex M' = B.relIndex M
      rw [Subgroup.relIndex_subgroupOf hMN]
    have hE_odd : Odd (Nat.card E) := hcardE ▸ hodd
    let QComp : Type _ :=
      {X : Subgroup Q // B ≤ X ∧ X ≤ N ∧ X ⊓ M = B ∧ X ⊔ M = N ∧ S ≤ X}
    have hmapM : M'.map N.subtype = M := Subgroup.map_subgroupOf_eq_of_le hMN
    have hmapB : B'.map N.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBN
    have hmapS : S'.map N.subtype = S := Subgroup.map_subgroupOf_eq_of_le (le_trans hSX hX0N)
    let toFun : QComp → ComplementsContaining E K D := fun X => by
      obtain ⟨hBX, hXN, hXM, hXsup, hSX⟩ := X.2
      have hB'X' : B' ≤ X.1.subgroupOf N := Subgroup.subgroupOf_mono N hBX
      have hM'X' : M' ⊓ X.1.subgroupOf N = B' := by
        rw [← subgroupOf_inf_eq hMN hXN, inf_comm, hXM]
      have hsup' : M' ⊔ X.1.subgroupOf N = ⊤ := by
        apply (Subgroup.map_subtype_inj (H := N)).mp
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hMN,
          Subgroup.map_subgroupOf_eq_of_le hXN, sup_comm, hXsup, Subgroup.map_top,
          Subgroup.range_subtype]
      have hinf' : E ⊓ (X.1.subgroupOf N).map q = ⊥ := by
        rw [show E = M'.map q from rfl, ← map_inf_eq (by rwa [QuotientGroup.ker_mk']), hM'X']
        exact hker
      have hsup'' : E ⊔ (X.1.subgroupOf N).map q = ⊤ := by
        rw [show E = M'.map q from rfl, ← Subgroup.map_sup, hsup',
          Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective B')]
      refine ⟨(X.1.subgroupOf N).map q, ?_, ?_⟩
      · exact isComplement'_iff_inf_eq_bot_and_sup_eq_top.2 ⟨hinf', hsup''⟩
      · rw [hDmap]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono N hSX)
    let invFun : ComplementsContaining E K D → QComp := fun K' => by
      obtain ⟨hK'comp, hK'cont⟩ := K'.2
      have hK'inf : E ⊓ K'.1 = ⊥ := hK'comp.disjoint.eq_bot
      have hK'sup : E ⊔ K'.1 = ⊤ := hK'comp.sup_eq_top
      have hcomapE : Subgroup.comap q E = M' := by
        change Subgroup.comap (QuotientGroup.mk' B') (M'.map (QuotientGroup.mk' B')) = M'
        exact Subgroup.comap_map_eq_self (by
          rw [QuotientGroup.ker_mk']
          exact hB'M')
      have hcomapBot : Subgroup.comap q (⊥ : Subgroup (N ⧸ B')) = B' := by
        rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
      have hB'L : B' ≤ K'.1.comap q := by
        intro b hb
        show q b ∈ K'.1
        have hbker : q b = 1 := by
          have hmem : b ∈ q.ker := by
            rw [QuotientGroup.ker_mk']
            exact hb
          exact MonoidHom.mem_ker.mp hmem
        rw [hbker]
        exact K'.1.one_mem
      have hLM : K'.1.comap q ⊓ M' = B' := by
        have h1 : (E ⊓ K'.1).comap q = (⊥ : Subgroup (N ⧸ B')).comap q := by
          rw [hK'inf]
        rw [Subgroup.comap_inf, hcomapE, hcomapBot] at h1
        rw [inf_comm]
        exact h1
      have hsupL : K'.1.comap q ⊔ M' = ⊤ := by
        have h1 : (E ⊔ K'.1).comap q = (⊤ : Subgroup (N ⧸ B')).comap q := by
          rw [hK'sup]
        rw [← Subgroup.comap_sup_eq (f := q) E K'.1 (QuotientGroup.mk'_surjective B')] at h1
        rw [hcomapE, Subgroup.comap_top] at h1
        simpa [sup_comm] using h1
      have hDqK : S'.map q ≤ K'.1 := hDmap ▸ hK'cont
      have hS'L : S' ≤ K'.1.comap q := by
        rw [← Subgroup.map_le_iff_le_comap]
        exact hDqK
      refine ⟨(K'.1.comap q).map N.subtype, ?_, ?_, ?_, ?_, ?_⟩
      · exact hmapB ▸ Subgroup.map_mono hB'L
      · exact Subgroup.map_subtype_le _
      · rw [← hmapM, ← Subgroup.map_inf (K'.1.comap q) M' N.subtype N.subtype_injective,
          hLM, hmapB]
      · have h1 : (K'.1.comap q ⊔ M').map N.subtype = (⊤ : Subgroup N).map N.subtype := by
          rw [hsupL]
        rw [Subgroup.map_sup, hmapM, Subgroup.map_top, Subgroup.range_subtype] at h1
        exact h1
      · rw [← hmapS]
        exact Subgroup.map_mono hS'L
    let e : QComp ≃ ComplementsContaining E K D :=
      { toFun := toFun, invFun := invFun
        left_inv := by
          intro X
          apply Subtype.ext
          change (((X.1.subgroupOf N).map q).comap q).map N.subtype = X.1
          rw [Subgroup.comap_map_eq_self (by
            show q.ker ≤ X.1.subgroupOf N
            rw [QuotientGroup.ker_mk']
            exact Subgroup.subgroupOf_mono N X.2.1),
            Subgroup.map_subgroupOf_eq_of_le X.2.2.1]
        right_inv := by
          intro K'
          apply Subtype.ext
          change ((((K'.1.comap q).map N.subtype).subgroupOf N)).map q = K'.1
          have hsub : ((K'.1.comap q).map N.subtype).subgroupOf N = K'.1.comap q := by
            apply (Subgroup.map_subtype_inj (H := N)).mp
            rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)]
          rw [hsub, Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective B') K'.1] }
    have hoddQ : Odd (Nat.card QComp) := by
      rw [Nat.card_congr e]
      exact odd_card_complements hcomp D hE_odd
    let R' : Subgroup (ConjAct Q) := R.map (ConjAct.toConjAct : Q ≃* ConjAct Q).toMonoidHom
    have hR' : IsPGroup 2 R' := hR.map _
    have smul_data (a : ConjAct Q) (haB : a • B = B) (haN : a • N = N)
        (haM : a • M = M) (haS : a • S = S) {Xs : Subgroup Q}
        (hBX : B ≤ Xs) (hXN : Xs ≤ N) (hXM : Xs ⊓ M = B) (hXS : Xs ⊔ M = N)
        (hSX : S ≤ Xs) :
        B ≤ a • Xs ∧ a • Xs ≤ N ∧ (a • Xs) ⊓ M = B ∧ (a • Xs) ⊔ M = N ∧ S ≤ a • Xs :=
      ⟨by
        rw [← haB]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hBX,
       by
        rw [← haN]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hXN,
       by
        rw [← haM, ← Subgroup.smul_inf, hXM, haB],
       by
        rw [← haM, ← haN, ← Subgroup.smul_sup, hXS, haN],
       by
        rw [← haS]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hSX⟩
    letI : MulAction R' QComp :=
      { smul := fun r X => ⟨(r : ConjAct Q) • X.1, by
          obtain ⟨hBX, hXN, hXM, hXS, hSX⟩ := X.2
          obtain ⟨r₀, hr₀, hr_eq⟩ := Subgroup.mem_map.mp r.2
          rw [← hr_eq]
          exact smul_data (ConjAct.toConjAct r₀)
            (Subgroup.conjAct_pointwise_smul_eq_self (hRB hr₀))
            (Subgroup.conjAct_pointwise_smul_eq_self (hRN hr₀))
            (Subgroup.conjAct_pointwise_smul_eq_self (hRM hr₀))
            (Subgroup.conjAct_pointwise_smul_eq_self (hRS hr₀))
            hBX hXN hXM hXS hSX⟩
        one_smul := fun X => by
          apply Subtype.ext
          change (1 : ConjAct Q) • X.1 = X.1
          simp
        mul_smul := fun r s X => by
          apply Subtype.ext
          change ((r * s : R') : ConjAct Q) • X.1 =
            (r : ConjAct Q) • ((s : ConjAct Q) • X.1)
          rw [Subgroup.coe_mul, mul_smul] }
    have hoddNotDvd : ¬ 2 ∣ Nat.card QComp := hoddQ.not_two_dvd_nat
    let hfp := hR'.nonempty_fixed_point_of_prime_not_dvd_card QComp hoddNotDvd
    let X : QComp := Classical.choose hfp
    have hXfix : X ∈ MulAction.fixedPoints R' QComp := Classical.choose_spec hfp
    have hXR : R ≤ Subgroup.normalizer (X.1 : Set Q) := by
      intro r hr
      have hfix := (MulAction.mem_fixedPoints.mp hXfix) ⟨ConjAct.toConjAct r,
        Subgroup.mem_map.mpr ⟨r, hr, rfl⟩⟩
      exact Subgroup.conjAct_pointwise_smul_iff.mp (congrArg Subtype.val hfix)
    exact ⟨X.1, X.2.1, X.2.2.1, X.2.2.2.1, X.2.2.2.2.1, X.2.2.2.2.2, hXR⟩
  obtain ⟨X, hX⟩ := build
  exact ⟨X, hX⟩



end Main

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
