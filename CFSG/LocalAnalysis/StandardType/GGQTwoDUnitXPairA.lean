module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXTrans
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBlock
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoDSlFix
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSAPairAux2

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

lemma qtwoDB21_dBasis_apply (m : ℕ) (i : Fin m) :
    dBasis m i = Pi.single i (1 : ZMod 3) :=
  Pi.basisFun_apply (ZMod 3) (Fin m) i

lemma qtwoDB21_dTau_false (m : ℕ) (a b : Fin m) :
    dTau m false a b = dPerm m (Equiv.swap a b) := by
  simp [dTau]

lemma qtwoDB21_neg_one_smul_zmod (x : ZMod 3) : (-1 : ZMod 3) • x = -x := by
  revert x
  decide

lemma qtwoDB21_dSign_fixes_single {m : ℕ} {a b c : Fin m} (hca : c ≠ a)
    (hcb : c ≠ b) :
    dSign m a b (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
  rw [← qtwoDB21_dBasis_apply, dSign_apply, if_neg (by tauto), one_smul,
    qtwoDB21_dBasis_apply]

lemma qtwoDB21_dTau_fixes_single {m : ℕ} {i j c : Fin m} {sgn : Bool}
    (hij : i ≠ j) (h : dTau m sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3)) :
    c ≠ i ∧ c ≠ j := by
  constructor
  · intro hci
    subst hci
    rw [← qtwoDB21_dBasis_apply, dTau_apply_left m sgn hij] at h
    have h2 := congrFun h c
    simp [qtwoDB21_dBasis_apply, Pi.single_eq_of_ne' (Ne.symm hij), Pi.single_eq_same] at h2
  · intro hcj
    subst hcj
    rw [← qtwoDB21_dBasis_apply, dTau_apply_right m sgn hij] at h
    have h2 := congrFun h c
    simp [qtwoDB21_dBasis_apply, Pi.single_eq_of_ne' hij, Pi.single_eq_same] at h2

lemma qtwoDB21_dSign_mem_dEven (m : ℕ) {a b : Fin m} (hab : a ≠ b) :
    dSign m a b ∈ dEven m := by
  have h : dSign m a b = (dPerm m (Equiv.swap a b))⁻¹ * dTau m true a b := by
    rw [dTau, if_pos rfl, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h]
  exact (dEven m).mul_mem ((dEven m).inv_mem (dPerm_mem_dEven m _))
    (dTau_mem_dEven m true hab)

lemma qtwoDB21_dSign_comm_dPerm {m : ℕ} {c d : Fin m} {σ : Equiv.Perm (Fin m)}
    (hσc : σ c = c) (hσd : σ d = d) :
    dSign m c d * dPerm m σ = dPerm m σ * dSign m c d := by
  refine (dBasis m).ext' fun i => ?_
  simp only [LinearEquiv.mul_apply, dPerm_apply, dSign_apply, map_smul]
  congr 1
  have hiff : (σ i = c ∨ σ i = d) ↔ (i = c ∨ i = d) := by
    constructor
    · rintro (h | h)
      · left
        exact σ.injective (by rw [h, hσc])
      · right
        exact σ.injective (by rw [h, hσd])
    · rintro (h | h)
      · left; rw [h, hσc]
      · right; rw [h, hσd]
  by_cases h : i = c ∨ i = d
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]

theorem qtwoDB21_X_le_centralizer (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') :
    qtwoDelX ψ c g ≤ Subgroup.centralizer ({(b' : G)} : Set G) := by
  classical
  have hcoord : βL (Additive.ofMul b') = Pi.single c 1 := hdel.coord
  have hJ₁ : (coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ ≤
      Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    let cfun : Fin m → F0ˣ := fun i => ω ^ (βL (Additive.ofMul b') i).val
    have hcf : ∀ k ∈ Finset.univ.erase c, cfun k = 1 := by
      intro k hk
      rw [Finset.mem_erase] at hk
      simp only [cfun, hcoord]
      rw [Pi.single_eq_of_ne' (Ne.symm hk.1), ZMod.val_zero, pow_zero]
    have hconst : ∀ i ∈ Finset.univ.erase c, ∀ j ∈ Finset.univ.erase c,
        (cfun i : F0) = (cfun j : F0) := by
      intro i hi j hj
      rw [hcf i hi, hcf j hj]
    obtain ⟨u', hu'mat, hu'ψ⟩ := hcoords.induces b' u
    have hcomm : qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) =
        (u : GL (Fin m) F0) * qTwoChartTwoThree_diag cfun := by
      apply Units.ext
      change Matrix.diagonal (fun i => (cfun i : F0)) *
          ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          Matrix.diagonal (fun i => (cfun i : F0))
      exact diagonal_mul_comm_of_mem_coordBlockSU hu hconst
    have hu'u : u' = u := by
      have h1 : (u' : GL (Fin m) F0) = (u : GL (Fin m) F0) := by
        rw [hu'mat]
        calc qTwoChartTwoThree_diag cfun * (u : GL (Fin m) F0) *
              (qTwoChartTwoThree_diag cfun)⁻¹
            = ((u : GL (Fin m) F0) * qTwoChartTwoThree_diag cfun) *
                (qTwoChartTwoThree_diag cfun)⁻¹ := by rw [hcomm]
          _ = (u : GL (Fin m) F0) := by group
      exact Subtype.ext h1
    have h1 : (ψ u : G) = (b' : G) * ψ u * (b' : G)⁻¹ := by
      rw [← hu'ψ, hu'u]
    have hcommb : (b' : G) * ψ u = ψ u * (b' : G) := by
      conv_rhs => rw [h1]
      group
    exact hcommb
  have hαb' : α b' = b' := by
    have h2 : Additive.ofMul (α b') = Additive.ofMul b' := by
      apply βL.injective
      rw [hdel.sign b', hcoord]
      exact qtwoDB21_dSign_fixes_single hdel.hca hdel.hcb
    exact Additive.ofMul.injective h2
  have hgb' : g * (b' : G) * g⁻¹ = (b' : G) := by
    rw [← hdel.conj b', hαb']
  have hginv : g⁻¹ * (b' : G) = (b' : G) * g⁻¹ := by
    have h := congrArg (fun z => g⁻¹ * z) hgb'
    rw [show g⁻¹ * (g * (b' : G) * g⁻¹) = (b' : G) * g⁻¹ by group] at h
    exact h.symm
  have hJ₂ : ((coordBlockSU F0 2 1 (Finset.univ.erase c)).map ψ).map
      (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rintro z ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have hbu : (b' : G) * ψ u = ψ u * (b' : G) :=
      Subgroup.mem_centralizer_iff.mp (hJ₁ ⟨u, hu, rfl⟩) (b' : G) (Set.mem_singleton _)
    calc (b' : G) * ((MulAut.conj g) (ψ u))
        = (b' : G) * (g * ψ u * g⁻¹) := by rw [MulAut.conj_apply]
      _ = (g * (b' : G) * g⁻¹) * (g * ψ u * g⁻¹) := by conv_lhs => rw [← hgb']
      _ = g * (b' : G) * ψ u * g⁻¹ := by group
      _ = g * ((b' : G) * ψ u) * g⁻¹ := by group
      _ = g * (ψ u * (b' : G)) * g⁻¹ := by rw [hbu]
      _ = (g * ψ u * g⁻¹) * (g * (b' : G) * g⁻¹) := by group
      _ = (g * ψ u * g⁻¹) * (b' : G) := by rw [hgb']
      _ = ((MulAut.conj g) (ψ u)) * (b' : G) := by rw [MulAut.conj_apply]
  rw [qtwoDelX]
  exact sup_le hJ₁ hJ₂

lemma qtwoDB21_fixes_b'
    (hXc : qtwoDelX ψ c g ≤ Subgroup.centralizer ({(b' : G)} : Set G))
    {r : MulAut ↥Bs} (hr : r ∈ ggAutomizer (qtwoDelX ψ c g) Bs) :
    r b' = b' := by
  obtain ⟨n, hnX, hnN, hna⟩ := mem_ggAutomizer_iff.mp hr
  have hcomm : n * (b' : G) = (b' : G) * n :=
    (Subgroup.mem_centralizer_iff.mp (hXc hnX) (b' : G) (Set.mem_singleton _)).symm
  apply Subtype.ext
  rw [hna b']
  rw [hcomm]
  group

lemma qtwoDB21_normal_form_pair (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω)
    (hdel : QTwoUnitDel Bs βL a b c α g b') (hm : 7 ≤ m)
    {r r' : MulAut ↥Bs} (hrA : r ∈ ggAutomizer (qtwoDelX ψ c g) Bs)
    (hrC : r ∈ ggCoxRefl M e) (hr'A : r' ∈ ggAutomizer (qtwoDelX ψ c g) Bs)
    (hr'C : r' ∈ ggCoxRefl M e) (hnc : r * r' ≠ r' * r) :
    ∃ (p₀ p₁ p₂ : Fin m) (n : G) (a₀ : MulAut ↥Bs),
      p₁.val = p₀.val + 1 ∧ p₂.val = p₀.val + 2 ∧
      c ≠ p₀ ∧ c ≠ p₁ ∧ c ≠ p₂ ∧
      n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ s : ↥Bs, ((a₀ s : ↥Bs) : G) = n * (s : G) * n⁻¹) ∧
      a₀ * r * a₀⁻¹ = ((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) ∧
      a₀ * r' * a₀⁻¹ = ((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) := by
  classical
  have hXc := qtwoDB21_X_le_centralizer hbase hcoords hdel
  have hrb' : r b' = b' := qtwoDB21_fixes_b' hXc hrA
  have hr'b' : r' b' = b' := qtwoDB21_fixes_b' hXc hr'A
  obtain ⟨sgn, i, j, hij, hact⟩ := hcoords.coxRoot r hrC
  obtain ⟨sgn', i', j', hi'j', hact'⟩ := hcoords.coxRoot r' hr'C
  have hfix : dTau m sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r b')) = βL (Additive.ofMul b') := by rw [hrb']
    rw [hact b', hdel.coord] at h1
    exact h1
  obtain ⟨hci, hcj⟩ := qtwoDB21_dTau_fixes_single hij hfix
  have hfix' : dTau m sgn' i' j' (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    have h1 : βL (Additive.ofMul (r' b')) = βL (Additive.ofMul b') := by rw [hr'b']
    rw [hact' b', hdel.coord] at h1
    exact h1
  obtain ⟨hci', hcj'⟩ := qtwoDB21_dTau_fixes_single hi'j' hfix'
  have hnc' : dTau m sgn i j * dTau m sgn' i' j' ≠ dTau m sgn' i' j' * dTau m sgn i j := by
    intro h
    apply hnc
    refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    simp only [MulAut.mul_apply, hact, hact']
    simpa only [LinearEquiv.mul_apply] using
      congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m => T (βL (Additive.ofMul s))) h
  obtain ⟨p₀, p₁, p₂, hp1, hp2, -, hc0, hc1, hc2, U, hU, hUfix, hconj1, hconj2⟩ :=
    Sl.exists_conj_pair_of_noncomm_fix (m := m) (by omega) hij hi'j' sgn sgn' hnc' hci hcj
      hci' hcj'
  obtain ⟨κ, hκ, hUκ⟩ := hUfix
  have hVconj1 : U⁻¹ * dTau m sgn i j * U = dTau m false p₀ p₁ := by
    rw [← hconj1]
    group
  have hVconj2 : U⁻¹ * dTau m sgn' i' j' * U = dTau m false p₁ p₂ := by
    rw [← hconj2]
    group
  have hcard : ({c, p₀, p₁, p₂} : Finset (Fin m)).card <
      (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h4 : ({c, p₀, p₁, p₂} : Finset (Fin m)).card ≤ 4 := by
      calc ({c, p₀, p₁, p₂} : Finset (Fin m)).card
          ≤ ({p₀, p₁, p₂} : Finset (Fin m)).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({p₁, p₂} : Finset (Fin m)).card + 1 + 1 := by
              have := Finset.card_insert_le p₀ ({p₁, p₂} : Finset (Fin m))
              omega
        _ ≤ ({p₂} : Finset (Fin m)).card + 1 + 1 + 1 := by
              have := Finset.card_insert_le p₁ ({p₂} : Finset (Fin m))
              omega
        _ = 4 := by simp
    omega
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
  obtain ⟨hdc, hd0, hd1, hd2⟩ := hd
  have hcd : c ≠ d := fun h => hdc h.symm
  let D : DVec m ≃ₗ[ZMod 3] DVec m := dSign m c d
  have hDmem : D ∈ dEven m := qtwoDB21_dSign_mem_dEven m hcd
  have hDcomm1 : D * dTau m false p₀ p₁ * D⁻¹ = dTau m false p₀ p₁ := by
    have h1 : D * dPerm m (Equiv.swap p₀ p₁) = dPerm m (Equiv.swap p₀ p₁) * D :=
      qtwoDB21_dSign_comm_dPerm
        (Equiv.swap_apply_of_ne_of_ne hc0 hc1) (Equiv.swap_apply_of_ne_of_ne hd0 hd1)
    have h2 : dTau m false p₀ p₁ = dPerm m (Equiv.swap p₀ p₁) := by simp [dTau]
    rw [h2, h1]
    group
  have hDcomm2 : D * dTau m false p₁ p₂ * D⁻¹ = dTau m false p₁ p₂ := by
    have h1 : D * dPerm m (Equiv.swap p₁ p₂) = dPerm m (Equiv.swap p₁ p₂) * D :=
      qtwoDB21_dSign_comm_dPerm
        (Equiv.swap_apply_of_ne_of_ne hc1 hc2) (Equiv.swap_apply_of_ne_of_ne hd1 hd2)
    have h2 : dTau m false p₁ p₂ = dPerm m (Equiv.swap p₁ p₂) := by simp [dTau]
    rw [h2, h1]
    group
  have hDc : D (dBasis m c) = -dBasis m c := by
    rw [show D = dSign m c d from rfl, dSign_apply, if_pos (Or.inl rfl)]
    funext i
    exact qtwoDB21_neg_one_smul_zmod ((dBasis m) c i)
  let V' : DVec m ≃ₗ[ZMod 3] DVec m := if κ = 1 then U⁻¹ else D * U⁻¹
  have hV'mem : V' ∈ dEven m := by
    by_cases hκ1 : κ = 1
    · rw [show V' = U⁻¹ from if_pos hκ1]
      exact (dEven m).inv_mem hU
    · rw [show V' = D * U⁻¹ from if_neg hκ1]
      exact (dEven m).mul_mem hDmem ((dEven m).inv_mem hU)
  have hV'fix : V' (dBasis m c) = dBasis m c := by
    by_cases hκ1 : κ = 1
    · have hUc : U (dBasis m c) = dBasis m c := by
        rw [hκ1] at hUκ
        simpa only [one_smul] using hUκ
      rw [show V' = U⁻¹ from if_pos hκ1]
      calc U⁻¹ (dBasis m c) = U⁻¹ (U (dBasis m c)) := by rw [hUc]
        _ = dBasis m c := U.symm_apply_apply _
    · have hκm : κ = -1 := hκ.resolve_left hκ1
      have hUc : U (dBasis m c) = -dBasis m c := by
        rw [hκm] at hUκ
        rw [hUκ]
        funext i
        exact qtwoDB21_neg_one_smul_zmod ((dBasis m) c i)
      have hUinv : U⁻¹ (dBasis m c) = -dBasis m c := by
        change U.symm (dBasis m c) = -dBasis m c
        apply U.injective
        rw [U.apply_symm_apply]
        rw [show U (-(dBasis m c)) = -U (dBasis m c) from map_neg U (dBasis m c), hUc]
        abel
      rw [show V' = D * U⁻¹ from if_neg hκ1, LinearEquiv.mul_apply, hUinv]
      rw [show D (-(dBasis m c)) = -D (dBasis m c) from map_neg D (dBasis m c), hDc]
      abel
  have hV'conj1 : V' * dTau m sgn i j * V'⁻¹ = dTau m false p₀ p₁ := by
    by_cases hκ1 : κ = 1
    · rw [show V' = U⁻¹ from if_pos hκ1]
      exact hVconj1
    · rw [show V' = D * U⁻¹ from if_neg hκ1]
      calc D * U⁻¹ * dTau m sgn i j * (D * U⁻¹)⁻¹
          = D * (U⁻¹ * dTau m sgn i j * U) * D⁻¹ := by group
        _ = D * dTau m false p₀ p₁ * D⁻¹ := by rw [hVconj1]
        _ = dTau m false p₀ p₁ := hDcomm1
  have hV'conj2 : V' * dTau m sgn' i' j' * V'⁻¹ = dTau m false p₁ p₂ := by
    by_cases hκ1 : κ = 1
    · rw [show V' = U⁻¹ from if_pos hκ1]
      exact hVconj2
    · rw [show V' = D * U⁻¹ from if_neg hκ1]
      calc D * U⁻¹ * dTau m sgn' i' j' * (D * U⁻¹)⁻¹
          = D * (U⁻¹ * dTau m sgn' i' j' * U) * D⁻¹ := by group
        _ = D * dTau m false p₁ p₂ * D⁻¹ := by rw [hVconj2]
        _ = dTau m false p₁ p₂ := hDcomm2
  have hV'fix' : V' (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
    rw [← qtwoDB21_dBasis_apply]; exact hV'fix
  obtain ⟨a₀, ha₀J, ha₀V'⟩ := hcoords.join_onto V' hV'mem
  obtain ⟨n, -, hnN, hnact⟩ := exists_lift_of_mem_ggAutomizerJoin ha₀J
  have hainv : ∀ s : ↥Bs, βL (Additive.ofMul (a₀⁻¹ s)) = V'⁻¹ (βL (Additive.ofMul s)) := by
    intro s
    have h := ha₀V' (a₀⁻¹ s)
    rw [show a₀ (a₀⁻¹ s) = s from MulEquiv.apply_symm_apply a₀ s] at h
    change βL (Additive.ofMul (a₀⁻¹ s)) = V'.symm (βL (Additive.ofMul s))
    rw [h]
    exact (V'.symm_apply_apply _).symm
  refine ⟨p₀, p₁, p₂, n, a₀, hp1, hp2, hc0, hc1, hc2, hnN, hnact, ?_, ?_⟩
  · refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    have hcomp := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m =>
      T (βL (Additive.ofMul s))) hV'conj1
    have h1 : βL (Additive.ofMul ((a₀ * r * a₀⁻¹) s)) =
        V' (dTau m sgn i j (V'⁻¹ (βL (Additive.ofMul s)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀V', hact, hainv s]
    have h2 : βL (Additive.ofMul
        ((((ε (Equiv.swap p₀ p₁) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s))) =
        dPerm m (Equiv.swap p₀ p₁) (βL (Additive.ofMul s)) :=
      hcoords.perm (Equiv.swap p₀ p₁) s
    rw [h1, h2]
    simpa only [LinearEquiv.mul_apply, qtwoDB21_dTau_false] using hcomp
  · refine MulEquiv.ext fun s => ?_
    apply Additive.ofMul.injective
    apply βL.injective
    have hcomp := congrArg (fun T : DVec m ≃ₗ[ZMod 3] DVec m =>
      T (βL (Additive.ofMul s))) hV'conj2
    have h1 : βL (Additive.ofMul ((a₀ * r' * a₀⁻¹) s)) =
        V' (dTau m sgn' i' j' (V'⁻¹ (βL (Additive.ofMul s)))) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀V', hact', hainv s]
    have h2 : βL (Additive.ofMul
        ((((ε (Equiv.swap p₁ p₂) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) s))) =
        dPerm m (Equiv.swap p₁ p₂) (βL (Additive.ofMul s)) :=
      hcoords.perm (Equiv.swap p₁ p₂) s
    rw [h1, h2]
    simpa only [LinearEquiv.mul_apply, qtwoDB21_dTau_false] using hcomp

end CFSG.StandardType.QTwo

end
