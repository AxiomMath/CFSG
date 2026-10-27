module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbr
public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitRankTwo
import CFSG.LocalAnalysis.StandardType.GGQTwoDSlFix

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

@[expose] def qtwoDB20_sg (ε : Bool) : ZMod 3 := if ε then -1 else 1

theorem qtwoDB20_dBasis_apply (m : ℕ) (i : Fin m) :
    dBasis m i = Pi.single i (1 : ZMod 3) :=
  Pi.basisFun_apply (ZMod 3) (Fin m) i

theorem qtwoDB20_mul_dTau (m : ℕ) {U : DVec m ≃ₗ[ZMod 3] DVec m}
    {σ : Equiv.Perm (Fin m)} {cfun : Fin m → ZMod 3}
    (hc : ∀ i, cfun i = 1 ∨ cfun i = -1)
    (hU : ∀ i, U (dBasis m i) = cfun i • dBasis m (σ i))
    {a b : Fin m} (hab : a ≠ b) (ε ε' : Bool)
    (hε : qtwoDB20_sg ε' = cfun a * cfun b * qtwoDB20_sg ε) :
    U * dTau m ε a b * U⁻¹ = dTau m ε' (σ a) (σ b) := by
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  have hsq : ∀ i, cfun i * cfun i = 1 := by
    intro i
    rcases hc i with h | h <;> rw [h] <;> decide
  rw [mul_inv_eq_iff_eq_mul]
  refine (dBasis m).ext' fun k => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  by_cases hka : k = a
  · rw [hka, dTau_apply_left m ε hab, map_smul, hU b, hU a, map_smul,
      dTau_apply_left m ε' hσab, smul_smul, smul_smul]
    congr 1
    change qtwoDB20_sg ε * cfun b = cfun a * qtwoDB20_sg ε'
    rw [hε]
    have hsq2 : cfun a ^ 2 = 1 := by rw [pow_two]; exact hsq a
    ring_nf
    rw [hsq2]
    ring
  · by_cases hkb : k = b
    · rw [hkb, dTau_apply_right m ε hab, map_smul, hU a, hU b, map_smul,
        dTau_apply_right m ε' hσab, smul_smul, smul_smul]
      congr 1
      change qtwoDB20_sg ε * cfun a = cfun b * qtwoDB20_sg ε'
      rw [hε]
      have hsq2 : cfun b ^ 2 = 1 := by rw [pow_two]; exact hsq b
      ring_nf
      rw [hsq2]
      ring
    · rw [dTau_apply_of_ne m ε hka hkb, hU k, map_smul,
        dTau_apply_of_ne m ε' (fun h => hka (σ.injective h))
          (fun h => hkb (σ.injective h))]

theorem qtwoDB20_dSign_mem_dEven (m : ℕ) {a b : Fin m} (hab : a ≠ b) :
    dSign m a b ∈ dEven m := by
  have h : dSign m a b = (dPerm m (Equiv.swap a b))⁻¹ * dTau m true a b := by
    rw [dTau, if_pos rfl, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h]
  exact (dEven m).mul_mem ((dEven m).inv_mem (dPerm_mem_dEven m _))
    (dTau_mem_dEven m true hab)

theorem qtwoDB20_dSign_fixes_single {m : ℕ} {a b c : Fin m} (hca : c ≠ a) (hcb : c ≠ b) :
    dSign m a b (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3) := by
  rw [← qtwoDB20_dBasis_apply, dSign_apply, if_neg (by tauto), one_smul,
    qtwoDB20_dBasis_apply]

theorem qtwoDB20_dTau_fixes_single {m : ℕ} {i j c : Fin m} {sgn : Bool}
    (hij : i ≠ j) (h : dTau m sgn i j (Pi.single c (1 : ZMod 3)) = Pi.single c (1 : ZMod 3)) :
    c ≠ i ∧ c ≠ j := by
  constructor
  · intro hci
    subst hci
    rw [← qtwoDB20_dBasis_apply, dTau_apply_left m sgn hij] at h
    have h2 := congrFun h c
    simp [qtwoDB20_dBasis_apply, Pi.single_eq_of_ne' (Ne.symm hij),
      Pi.single_eq_same] at h2
  · intro hcj
    subst hcj
    rw [← qtwoDB20_dBasis_apply, dTau_apply_right m sgn hij] at h
    have h2 := congrFun h c
    simp [qtwoDB20_dBasis_apply, Pi.single_eq_of_ne' hij, Pi.single_eq_same] at h2

theorem qtwoDB20_oTwoPrime_le_inf {X : Type} [Group X] {C X' : Subgroup X}
    (h : ggOTwoPrime C ≤ X' ⊓ C) :
    ggOTwoPrime C ≤ ggOTwoPrime (X' ⊓ C) := by
  rw [ggOTwoPrime, ggOTwoPrime]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyC, k, hk⟩
  have hy : y ∈ ggOTwoPrime C := Subgroup.subset_closure ⟨hyC, k, hk⟩
  exact Subgroup.subset_closure ⟨h hy, k, hk⟩

theorem qtwoDB20_X_le_centralizer (hbase : QTwoUnitBase p B Bs x L ψ ε)
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
      exact qtwoDB20_dSign_fixes_single hdel.hca hdel.hcb
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

theorem qtwoDB20_fixes_b'
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

theorem qtwoDB20_normal_form_one (hm : 4 ≤ m) {i j : Fin m} {sgn : Bool}
    (hij : i ≠ j) (hci : c ≠ i) (hcj : c ≠ j) :
    ∃ w ∈ dEven m, w (Pi.single c 1) = Pi.single c 1 ∧
      ∃ u v : Fin m, u ∈ Finset.univ.erase c ∧ v ∈ Finset.univ.erase c ∧ u ≠ v ∧
        w * dTau m sgn i j * w⁻¹ = dTau m false u v := by
  classical
  have hiS : i ∈ Finset.univ.erase c := by
    rw [Finset.mem_erase]
    exact ⟨hci.symm, Finset.mem_univ i⟩
  have hjS : j ∈ Finset.univ.erase c := by
    rw [Finset.mem_erase]
    exact ⟨hcj.symm, Finset.mem_univ j⟩
  cases sgn
  · exact ⟨1, (dEven m).one_mem, by simp, i, j, hiS, hjS, hij, by simp⟩
  · have hcard : 0 < (Finset.univ.erase c \ {i, j}).card := by
      rw [Finset.card_sdiff]
      have hsub : ({i, j} : Finset (Fin m)) ⊆ Finset.univ.erase c := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rw [Finset.mem_erase]
        rcases hx with hxi | hxj
        · rw [hxi]
          exact ⟨hci.symm, Finset.mem_univ i⟩
        · rw [hxj]
          exact ⟨hcj.symm, Finset.mem_univ j⟩
      rw [Finset.inter_eq_left.mpr hsub, Finset.card_erase_of_mem (Finset.mem_univ c),
        Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
      omega
    obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
    rw [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hk
    obtain ⟨⟨hkc, -⟩, hki, hkj⟩ := hk
    have hjk : j ≠ k := Ne.symm hkj
    have hik : i ≠ k := Ne.symm hki
    have hck : c ≠ k := Ne.symm hkc
    refine ⟨dSign m j k, qtwoDB20_dSign_mem_dEven m hjk,
      qtwoDB20_dSign_fixes_single hcj hck, i, j, hiS, hjS, hij, ?_⟩
    have hε : qtwoDB20_sg false = (fun p => if p = j ∨ p = k then (-1 : ZMod 3) else 1) i *
        (fun p => if p = j ∨ p = k then (-1 : ZMod 3) else 1) j *
        qtwoDB20_sg true := by
      simp [qtwoDB20_sg, hij, hik, hkj]
    have hU : ∀ p : Fin m, dSign m j k (dBasis m p) =
        (fun q => if q = j ∨ q = k then (-1 : ZMod 3) else 1) p •
          dBasis m ((1 : Equiv.Perm (Fin m)) p) := by
      intro p
      rw [dSign_apply, Equiv.Perm.one_apply]
    have h := qtwoDB20_mul_dTau m (U := dSign m j k) (σ := 1)
      (cfun := fun p => if p = j ∨ p = k then (-1 : ZMod 3) else 1)
      (by intro p; by_cases h : p = j ∨ p = k <;> simp [h]) hU hij true false hε
    simpa using h

theorem qtwoDB20_dSign_comm_dPerm {m : ℕ} {c d : Fin m} {σ : Equiv.Perm (Fin m)}
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

theorem qtwoDB20_dTau_false (m : ℕ) (a b : Fin m) :
    dTau m false a b = dPerm m (Equiv.swap a b) := by
  simp [dTau]

theorem qtwoDB20_normal_form_pair_lin (hm : 6 ≤ m) {i j i' j' : Fin m} {sgn sgn' : Bool}
    (hij : i ≠ j) (hi'j' : i' ≠ j') (hci : c ≠ i) (hcj : c ≠ j) (hci' : c ≠ i')
    (hcj' : c ≠ j')
    (hnc : dTau m sgn i j * dTau m sgn' i' j' ≠ dTau m sgn' i' j' * dTau m sgn i j) :
    ∃ (p₀ p₁ p₂ : Fin m) (V : DVec m ≃ₗ[ZMod 3] DVec m),
      p₁.val = p₀.val + 1 ∧ p₂.val = p₀.val + 2 ∧ c ≠ p₀ ∧ c ≠ p₁ ∧ c ≠ p₂ ∧
      V ∈ dEven m ∧ V (Pi.single c 1) = Pi.single c 1 ∧
      V * dTau m sgn i j * V⁻¹ = dTau m false p₀ p₁ ∧
      V * dTau m sgn' i' j' * V⁻¹ = dTau m false p₁ p₂ := by
  classical
  obtain ⟨p₀, p₁, p₂, hp1, hp2, -, hc0, hc1, hc2, U, hU, hUfix, hconj1, hconj2⟩ :=
    Sl.exists_conj_pair_of_noncomm_fix (m := m) (by omega) hij hi'j' sgn sgn' hnc hci hcj
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
  have hDmem : D ∈ dEven m := qtwoDB20_dSign_mem_dEven m hcd
  have hDcomm1 : D * dTau m false p₀ p₁ * D⁻¹ = dTau m false p₀ p₁ := by
    have h1 : D * dPerm m (Equiv.swap p₀ p₁) = dPerm m (Equiv.swap p₀ p₁) * D :=
      qtwoDB20_dSign_comm_dPerm
        (Equiv.swap_apply_of_ne_of_ne hc0 hc1) (Equiv.swap_apply_of_ne_of_ne hd0 hd1)
    have h2 : dTau m false p₀ p₁ = dPerm m (Equiv.swap p₀ p₁) := qtwoDB20_dTau_false m p₀ p₁
    rw [h2, h1]
    group
  have hDcomm2 : D * dTau m false p₁ p₂ * D⁻¹ = dTau m false p₁ p₂ := by
    have h1 : D * dPerm m (Equiv.swap p₁ p₂) = dPerm m (Equiv.swap p₁ p₂) * D :=
      qtwoDB20_dSign_comm_dPerm
        (Equiv.swap_apply_of_ne_of_ne hc1 hc2) (Equiv.swap_apply_of_ne_of_ne hd1 hd2)
    have h2 : dTau m false p₁ p₂ = dPerm m (Equiv.swap p₁ p₂) := qtwoDB20_dTau_false m p₁ p₂
    rw [h2, h1]
    group
  have hDc : D (dBasis m c) = -dBasis m c := by
    rw [show D = dSign m c d from rfl, dSign_apply, if_pos (Or.inl rfl)]
    funext i
    simp
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
        funext i
        have h := congrFun hUκ i
        rw [h]
        rw [Pi.smul_apply, Pi.neg_apply]
        rw [smul_eq_mul]
        exact neg_one_mul ((dBasis m c) i)
      have hUinv : U⁻¹ (dBasis m c) = -dBasis m c := by
        apply U.injective
        have h1 : U (U⁻¹ (dBasis m c)) = dBasis m c := U.apply_symm_apply _
        rw [h1, show U (-(dBasis m c)) = -U (dBasis m c) from map_neg U (dBasis m c), hUc]
        exact (neg_neg (dBasis m c)).symm
      rw [show V' = D * U⁻¹ from if_neg hκ1, LinearEquiv.mul_apply, hUinv]
      rw [show D (-(dBasis m c)) = -D (dBasis m c) from map_neg D (dBasis m c), hDc]
      exact neg_neg (dBasis m c)
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
    rw [← qtwoDB20_dBasis_apply]; exact hV'fix
  exact ⟨p₀, p₁, p₂, V', hp1, hp2, hc0, hc1, hc2, hV'mem, hV'fix', hV'conj1, hV'conj2⟩

end CFSG.StandardType.QTwo

end
