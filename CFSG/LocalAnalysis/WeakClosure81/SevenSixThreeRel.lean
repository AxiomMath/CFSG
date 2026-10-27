module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_top_eq_subgroupOf (H : Subgroup G) :
    pCoreOf 2 (⊤ : Subgroup ↥H) = (pCoreOf 2 H).subgroupOf H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set P : Subgroup ↥H := pCoreOf 2 (⊤ : Subgroup ↥H) with hP
    have hPn : P.Normal := by
      have h1 : (⊤ : Subgroup ↥H) ≤ Subgroup.normalizer (P : Set ↥H) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 ⊤
      exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h1)
    have hK : IsPGroup 2 ↥(P.map H.subtype) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (⊤ : Subgroup ↥H)).map H.subtype
    have hKn : ((P.map H.subtype).subgroupOf H).Normal := by
      have h2 : (P.map H.subtype).subgroupOf H = P :=
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) P
      rw [h2]
      exact hPn
    have hle : P.map H.subtype ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 (Subgroup.map_subtype_le P) hKn hK
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hle ⟨x, hx, rfl⟩)
  · set N : Subgroup ↥H := (pCoreOf 2 H).subgroupOf H with hN
    have hNn : N.Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
    have hNp : IsPGroup 2 ↥N :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).of_equiv
        (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).symm
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 le_top inferInstance hNp

theorem isMulCommutative_subgroupOf {K H : Subgroup G} (hK : IsMulCommutative K) :
    IsMulCommutative (K.subgroupOf H) := by
  haveI := hK
  infer_instance

theorem isElemAbelian_subgroupOf {p : ℕ} {K H : Subgroup G} (hK : IsElemAbelian p K) :
    IsElemAbelian p (K.subgroupOf H) := by
  refine ⟨isMulCommutative_subgroupOf hK.1, fun x hx => ?_⟩
  have h := hK.2 ((x : ↥H) : G) (Subgroup.mem_subgroupOf.mp hx)
  exact Subtype.ext (by simpa using h)

private theorem subgroupOf_inf_eq (H₁ H₂ K : Subgroup G) :
    (H₁ ⊓ H₂).subgroupOf K = H₁.subgroupOf K ⊓ H₂.subgroupOf K :=
  Subgroup.comap_inf _ _ _

theorem isTI_subgroupOf {A H : Subgroup G} (hAH : A ≤ H) (hTI : IsTI A) :
    IsTI (A.subgroupOf H) := by
  intro g
  have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup g (A.subgroupOf H) =
      (CFSG.CGT.Timmesfeld75.conjSubgroup (g : G) A).subgroupOf H := by
    ext x
    simp only [CFSG.CGT.Timmesfeld75.mem_conjSubgroup, Subgroup.mem_subgroupOf]
    simp
  rw [hconj, ← subgroupOf_inf_eq]
  rcases hTI (g : G) with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]

private theorem commutator_le_of_le_of_le {X A H : Subgroup G} (hXH : X ≤ H) (hAH : A ≤ H) :
    ⁅X, A⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro x hx a ha
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hXH hx) (hAH ha)) (H.inv_mem (hXH hx)))
    (H.inv_mem (hAH ha))

theorem commutator_subgroupOf_of_le {X A H : Subgroup G} (hXH : X ≤ H) (hAH : A ≤ H) :
    ⁅X.subgroupOf H, A.subgroupOf H⁆ = ⁅X, A⁆.subgroupOf H := by
  have hXAH : ⁅X, A⁆ ≤ H := commutator_le_of_le_of_le hXH hAH
  apply Subgroup.map_injective (Subgroup.subtype_injective H)
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXH,
    Subgroup.map_subgroupOf_eq_of_le hAH, Subgroup.map_subgroupOf_eq_of_le hXAH]

theorem subgroupOf_mem_omegaSet {V H E A : Subgroup G} (hA : A ∈ omegaSet V H E) (hAH : A ≤ H) :
    A.subgroupOf H ∈ omegaSet (A.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) := by
  obtain ⟨g₀, -, hEA, hAnot⟩ := mem_omegaSet.mp hA
  refine ⟨1, (CFSG.Quasithin.conjSubgroup_one _).symm, ?_, ?_⟩
  · intro hbot
    apply hEA
    have h1 : (E ⊓ A).subgroupOf H = ⊥ := by
      rw [subgroupOf_inf_eq]
      exact hbot
    have h2 : Disjoint (E ⊓ A) H := Subgroup.subgroupOf_eq_bot.mp h1
    exact h2.eq_bot_of_le (inf_le_right.trans hAH)
  · rw [pCoreOf_top_eq_subgroupOf]
    intro hle
    apply hAnot
    intro x hx
    exact Subgroup.mem_subgroupOf.mp
      (hle (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hAH hx⟩ : ↥H) ∈ A.subgroupOf H))

theorem map_subtype_mem_omegaSet {V H E A : Subgroup G} {U' : Subgroup ↥H}
    (hA : A ∈ omegaSet V H E) (hAH : A ≤ H)
    (hU' : U' ∈ omegaSet (A.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H)) :
    U'.map H.subtype ∈ omegaSet V H E := by
  obtain ⟨g', hU'g, hEU', hnot⟩ := mem_omegaSet.mp hU'
  obtain ⟨g₀, hAg, -, -⟩ := mem_omegaSet.mp hA
  have hconj : conjSubgroup (A.subgroupOf H) g' = (conjSubgroup A (g' : G)).subgroupOf H := by
    ext x
    simp only [mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
    simp
  have hUH : conjSubgroup A (g' : G) ≤ H := by
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have h1 : (g' : G) * x * (g' : G)⁻¹ ∈ H := hAH hx
    have h2 : (g' : G)⁻¹ * ((g' : G) * x * (g' : G)⁻¹) * (g' : G) ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem g'.2) h1) g'.2
    simpa [mul_assoc] using h2
  have hmap : U'.map H.subtype = conjSubgroup A (g' : G) := by
    rw [hU'g, hconj, Subgroup.map_subgroupOf_eq_of_le hUH]
  rw [hmap]
  refine ⟨g₀ * (g' : G), ?_, ?_, ?_⟩
  · rw [hAg, CFSG.Quasithin.conjSubgroup_conjSubgroup]
  · intro hbot
    apply hEU'
    rw [hU'g, hconj, ← subgroupOf_inf_eq, hbot]
    simp
  · intro hle
    apply hnot
    rw [pCoreOf_top_eq_subgroupOf, hU'g, hconj]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_subgroupOf.mp hx))

theorem iSub_subgroupOf_le {V H E A : Subgroup G} (hA : A ∈ omegaSet V H E) (hAH : A ≤ H) :
    iSub (A.subgroupOf H) (⊤ : Subgroup ↥H) (E.subgroupOf H) ≤ (iSub V H E).subgroupOf H := by
  refine iSup₂_le fun U' hU' => ?_
  intro x hx
  obtain ⟨hxU, hxP⟩ := Subgroup.mem_inf.mp hx
  rw [pCoreOf_top_eq_subgroupOf] at hxP
  have hU := map_subtype_mem_omegaSet hA hAH hU'
  exact Subgroup.mem_subgroupOf.mpr
    (inf_pCoreOf_le_iSub hU ⟨⟨x, hxU, rfl⟩, Subgroup.mem_subgroupOf.mp hxP⟩)


theorem seven_six_three_rel {V H E J A X : Subgroup G} {p : ℕ}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hp : p.Prime) (hp2 : p ≠ 2)
    (hE : IsMulCommutative E) (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    (hA : A ∈ omegaSet V H E) (hAH : A ≤ H) (hJA : J.relIndex A = 2)
    (hJX : J ≤ X) (hXH : X ≤ H) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXA : X ≤ ⁅X, A⁆ ⊔ J) (hfaith : ∀ a ∈ A, (∀ x ∈ X, ⁅a, x⁆ ∈ J) → a ∈ J)
    (hexp : ∀ x ∈ X, x ^ p ∈ J) (hcl : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, ⁅⁅x, y⁆, z⁆ ∈ J) :
    J.relIndex X = p ∨ (J.relIndex X = p ^ 3 ∧ ∃ x ∈ X, ∃ y ∈ X, ⁅x, y⁆ ∉ J) := by
  have hAab : IsElemAbelian 2 A := isElemAbelian_of_mem_omegaSet hV hA
  have hTIA : IsTI A := isTI_of_mem_omegaSet hA hTI
  have hJleH : J ≤ H := hJX.trans hXH
  haveI : (E.subgroupOf H).Normal := hEnorm
  haveI : (J.subgroupOf H).Normal := hJnorm
  have key := seven_six_three_member (G := ↥H) (V := A.subgroupOf H) (H := ⊤)
    (E := E.subgroupOf H) (J := J.subgroupOf H) (A := A.subgroupOf H) (X := X.subgroupOf H)
    (p := p) (isElemAbelian_subgroupOf hAab) (isTI_subgroupOf hAH hTIA) hp hp2
    (isMulCommutative_subgroupOf hE) le_top inferInstance (fun _ _ => le_top)
    (by
      rw [pCoreOf_top_eq_subgroupOf]
      exact fun x hx => Subgroup.mem_subgroupOf.mpr (hJ (Subgroup.mem_subgroupOf.mp hx)))
    inferInstance
    ((iSub_subgroupOf_le hA hAH).trans
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hIJ (Subgroup.mem_subgroupOf.mp hx))))
    (subgroupOf_mem_omegaSet hA hAH)
    (by rw [Subgroup.relIndex_subgroupOf hAH]; exact hJA)
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hJX (Subgroup.mem_subgroupOf.mp hx)))
    le_top
    (by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (hAX (Subgroup.mem_subgroupOf.mp ha)) (x : G)
      simpa [Subgroup.mem_subgroupOf] using h1)
    (by
      rw [commutator_subgroupOf_of_le hXH hAH,
        ← Subgroup.subgroupOf_sup (commutator_le_of_le_of_le hXH hAH) hJleH]
      exact fun x hx => Subgroup.mem_subgroupOf.mpr (hXA (Subgroup.mem_subgroupOf.mp hx)))
    (by
      intro a ha hcomm
      rw [Subgroup.mem_subgroupOf]
      refine hfaith (a : G) (Subgroup.mem_subgroupOf.mp ha) fun x hx => ?_
      have h1 := hcomm ⟨x, hXH hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
      simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using h1)
    (by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        (by simpa using hexp (x : G) (Subgroup.mem_subgroupOf.mp hx)))
    (by
      intro x hx y hy z hz
      have h1 := hcl (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
        (Subgroup.mem_subgroupOf.mp hy) (z : G) (Subgroup.mem_subgroupOf.mp hz)
      exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using h1))
  rw [Subgroup.relIndex_subgroupOf hXH] at key
  rcases key with h | ⟨h, x, hx, y, hy, hxy⟩
  · exact Or.inl h
  · refine Or.inr ⟨h, (x : G), Subgroup.mem_subgroupOf.mp hx, (y : G),
      Subgroup.mem_subgroupOf.mp hy, fun hJmem => hxy ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hJmem

end CFSG.LocalAnalysis.WeakClosure81
