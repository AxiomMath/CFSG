module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Defs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3
public import Certificates.Data.HuppertU38Fix.Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 CFSG.YGroups U38Fix U38Sylow

theorem fixes_pair_of_cube_comm {α : Type*} {X β : Equiv.Perm α} (hβ3 : β ^ 3 = 1)
    (hc : β * X = X * β) {p q : α} (hne : p ≠ q) (hp : X p = p) (hq : X q = q)
    (hall : ∀ r, X r = r → r = p ∨ r = q) : β p = p ∧ β q = q := by
  have hmap : ∀ r : α, X r = r → X (β r) = β r := by
    intro r hr
    have := congrArg (fun σ : Equiv.Perm α => σ r) hc
    simp only [Equiv.Perm.mul_apply, hr] at this
    exact this.symm
  have h3 : ∀ r : α, β (β (β r)) = r := by
    intro r
    have := congrArg (fun σ : Equiv.Perm α => σ r) hβ3
    simpa [pow_three] using this
  have h1 : β p = p := by
    rcases hall _ (hmap _ hp) with h | h
    · exact h
    · exfalso
      have hq' : β q = p := by
        rcases hall _ (hmap _ hq) with h' | h'
        · exact h'
        · exact absurd (β.injective (h.trans h'.symm)) hne
      have := h3 p
      rw [h, hq'] at this
      rw [h] at this
      exact hne this.symm
  refine ⟨h1, ?_⟩
  rcases hall _ (hmap _ hq) with h | h
  · exact absurd (β.injective (h.trans h1.symm)) (Ne.symm hne)
  · exact h

theorem perm_fix_of_rep {n : ℕ} {t : Array ℕ} {σ : Equiv.Perm (Fin n)} (hr : Rep n t σ)
    {p : Fin n} {k : ℕ} (hk : (p : ℕ) = k) (h : t[k]! = k) : σ p = p := by
  apply Fin.ext
  rw [← hr p, hk]
  exact h

section Spec


theorem X7_fix_points : X7 (109 : Fin 513) = 109 ∧ X7 (458 : Fin 513) = 458 →
    ∀ p : Fin 513, X7 p = p → p = 109 ∨ p = 458 := by
  rintro ⟨ha, hb⟩ p hp
  classical
  let T : Finset (Fin 513) := Finset.univ.filter fun q => X7 q = q
  have hT : T.card = 2 := by
    have h1 := X7_fixed
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    exact h1
  have hsub : ({109, 458} : Finset (Fin 513)) ⊆ T := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hq with rfl | rfl
    · exact ha
    · exact hb
  have hcard : ({109, 458} : Finset (Fin 513)).card = 2 := by decide
  have heq : ({109, 458} : Finset (Fin 513)) = T :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hT, hcard])
  have hpT : p ∈ T := by simp [T, hp]
  rw [← heq] at hpT
  simpa using hpT

theorem fixes_of_commute {β : Equiv.Perm (Fin 513)} (hβ3 : β ^ 3 = 1) (hc : β * X7 = X7 * β)
    (hfp : ∀ p : Fin 513, X7 p = p → p = 109 ∨ p = 458) (ha : X7 (109 : Fin 513) = 109)
    (hb : X7 (458 : Fin 513) = 458) : β 109 = 109 ∧ β 458 = 458 :=
  fixes_pair_of_cube_comm hβ3 hc (by decide) ha hb hfp

theorem fixCheck_spec (h : U38Fix.fixCheck () = true) :
    X7 ∈ X' ∧ (∀ β ∈ U38G, β ^ 3 = 1 → β * X7 = X7 * β → β ∈ X') ∧
      ∃ z ∈ X', orderOf z = 3 ∧ z * X7 = X7 * z := by
  classical
  simp only [U38Fix.fixCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨henum, hsize⟩, hsift⟩, hfix⟩, h109⟩, h458⟩, hx7X⟩, hOK⟩, hW⟩ := h
  have hps : ∀ p ∈ keyPts, p < 513 := by
    intro p hp
    simp [keyPts, base1, base1L] at hp
    omega
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hvx7 : validA 513 x7 = true := Certificates.certificate188001.2.2.2.2.2.1
  have hrx7 : Rep 513 x7 X7 := rep_of_validA hvx7
  have hX7X : X7 ∈ X' := sift3_mem hrx7 hx7X
  have ha : X7 (109 : Fin 513) = 109 := perm_fix_of_rep hrx7 rfl h109
  have hb : X7 (458 : Fin 513) = 458 := perm_fix_of_rep hrx7 rfl h458
  have hfp := X7_fix_points ⟨ha, hb⟩
  let H : Subgroup (Equiv.Perm (Fin 513)) := Subgroup.closure (permsA 513 hGens)
  let S₂ : Subgroup (Equiv.Perm (Fin 513)) :=
    U38G ⊓ (MulAction.stabilizer (Equiv.Perm (Fin 513)) (109 : Fin 513) ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 513)) (458 : Fin 513))
  have hHS₂ : H ≤ S₂ := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < hGens.size := hk
    have hvk := enumOK_gens_valid henum hk'
    have hrk := rep_of_validA hvk
    have hf := allLt_spec hfix hk'
    simp only [Bool.and_eq_true, beq_iff_eq] at hf
    refine Subgroup.mem_inf.2 ⟨mem_U38G_of_sift1 hvk (allLt_spec hsift hk'), Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
    · rw [MulAction.mem_stabilizer_iff]
      show permOfArr 513 hGens[k]! 109 = 109
      apply Fin.ext
      rw [← hrk (109 : Fin 513)]
      exact hf.1
    · rw [MulAction.mem_stabilizer_iff]
      show permOfArr 513 hGens[k]! 458 = 458
      apply Fin.ext
      rw [← hrk (458 : Fin 513)]
      exact hf.2
  have hS₂Γ : S₂ ≤ U38G := inf_le_left
  have hS₂card : Nat.card S₂ = 378 := by
    have h2 : ∀ a b a' b' : Fin 513, a ≠ b → a' ≠ b' →
        ∃ g : U38G, g • a = a' ∧ g • b = b' := by
      intro a b a' b' hab hab'
      obtain ⟨g, hg, h1, h2⟩ := U38G_twoTransitive a b a' b' hab hab'
      exact ⟨⟨g, hg⟩, h1, h2⟩
    have hpair := card_pairStabilizer (H := U38G) (Ω := Fin 513) h2
      (a := (109 : Fin 513)) (b := (458 : Fin 513)) (by decide)
    rw [card_U38G, Nat.card_fin] at hpair
    have hsub : S₂.subgroupOf U38G =
        (MulAction.stabilizer U38G (109 : Fin 513) ⊓ MulAction.stabilizer U38G (458 : Fin 513) :
          Subgroup U38G) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, S₂, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
      constructor
      · rintro ⟨-, h1, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨x.2, h1, h2⟩
    have hc1 : Nat.card (S₂.subgroupOf U38G) = Nat.card S₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS₂Γ).toEquiv
    rw [← hc1, hsub]
    generalize Nat.card (↥(MulAction.stabilizer U38G (109 : Fin 513) ⊓
      MulAction.stabilizer U38G (458 : Fin 513) : Subgroup U38G)) = X at hpair ⊢
    omega
  have hHcard : Nat.card H = 378 := by
    exact hcard.trans hsize
  have hHeq : H = S₂ := Subgroup.eq_of_le_of_card_ge hHS₂ (by rw [hHcard, hS₂card])
  refine ⟨hX7X, ?_, ?_⟩
  ·
    intro β hβ hβ3 hcomm
    obtain ⟨hβa, hβb⟩ := fixes_of_commute hβ3 hcomm hfp ha hb
    have hβS : β ∈ S₂ := by
      refine Subgroup.mem_inf.2 ⟨hβ, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
      · rw [MulAction.mem_stabilizer_iff]; exact hβa
      · rw [MulAction.mem_stabilizer_iff]; exact hβb
    rw [← hHeq] at hβS
    obtain ⟨i, hi, hβi⟩ := (hmem β).1 hβS
    have hvi := hval i hi
    have hri : Rep 513 hCert.pts[i]! β := hβi ▸ rep_of_validA hvi
    have hall := Array.all_eq_true.1 hOK i hi
    have hcube : cubeOne hCert.pts[i]! = true := by
      unfold cubeOne
      exact (eqA_iff (rep_compA hri (rep_compA hri hri)) rep_idA).2 (by simpa [pow_three] using hβ3)
    have hcomm' : commAt hCert.pts[i]! x7 = true := by
      unfold commAt
      exact (eqA_iff (rep_compA hri hrx7) (rep_compA hrx7 hri)).2 hcomm
    have hsc : cubeComm hCert.pts[i]! = true := by simp [cubeComm, hcube, hcomm']
    have hget : hCert.pts[i] = hCert.pts[i]! := (getElem!_pos hCert.pts i hi).symm
    rw [hget, hsc] at hall
    simp only [Bool.not_true, Bool.false_or] at hall
    exact sift3_mem hri hall
  ·
    obtain ⟨i, hi, hwit⟩ := Array.any_eq_true.1 hW
    have hget : hCert.pts[i] = hCert.pts[i]! := (getElem!_pos hCert.pts i hi).symm
    rw [hget] at hwit
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwit
    obtain ⟨⟨hcc, hnid⟩, hsx⟩ := hwit
    have hvi := hval i hi
    have hri : Rep 513 hCert.pts[i]! (permOfArr 513 hCert.pts[i]!) := rep_of_validA hvi
    simp only [cubeComm, Bool.and_eq_true] at hcc
    obtain ⟨hcube, hcomm'⟩ := hcc
    have hz3 : permOfArr 513 hCert.pts[i]! ^ 3 = 1 := by
      have := (eqA_iff (rep_compA hri (rep_compA hri hri)) rep_idA).1 (by unfold cubeOne at hcube; exact hcube)
      simpa [pow_three] using this
    have hz1 : permOfArr 513 hCert.pts[i]! ≠ 1 := by
      intro h1
      have : eqA 513 hCert.pts[i]! (idA 513) = true := (eqA_iff hri rep_idA).2 h1
      unfold isIdA at hnid
      rw [this] at hnid
      exact absurd hnid (by simp)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine ⟨permOfArr 513 hCert.pts[i]!, sift3_mem hri hsx, orderOf_eq_prime hz3 hz1, ?_⟩
    unfold commAt at hcomm'
    exact (eqA_iff (rep_compA hri hrx7) (rep_compA hrx7 hri)).1 hcomm'


theorem exists_conj_mem_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : ¬ p ^ 2 ∣ Nat.card G) {x s : G} (hx : orderOf x = p) (hs : orderOf s = p) :
    ∃ g : G, g * x * g⁻¹ ∈ Subgroup.zpowers s := by
  have hcard : ∀ y : G, orderOf y = p → Nat.card (Subgroup.zpowers y) = p := fun y hy => by
    rw [Nat.card_zpowers, hy]
  have hpg : ∀ y : G, orderOf y = p → IsPGroup p (Subgroup.zpowers y) := fun y hy =>
    IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcard y hy)
  have hindex : ∀ y : G, orderOf y = p → ¬ p ∣ (Subgroup.zpowers y).index := by
    intro y hy hdvd
    have h1 := Subgroup.card_mul_index (Subgroup.zpowers y)
    rw [hcard y hy] at h1
    obtain ⟨k, hk⟩ := hdvd
    apply hG
    rw [← h1, hk]
    exact ⟨k, by ring⟩
  let Px : Sylow p G := (hpg x hx).toSylow (hindex x hx)
  let Ps : Sylow p G := (hpg s hs).toSylow (hindex s hs)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Px Ps
  refine ⟨g, ?_⟩
  have hxP : x ∈ (Px : Subgroup G) := Subgroup.mem_zpowers x
  show g * x * g⁻¹ ∈ (Ps : Subgroup G)
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  exact ⟨x, hxP, by simp [MulAut.smul_def, MulAut.conj_apply]⟩

theorem orderOf_conj_group {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

theorem X'_le_U38G : X' ≤ U38G := by
  unfold X' U38G arrClosure
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk7 : k < 7 := by rw [gensX_size] at hk; exact hk
  apply Subgroup.subset_closure
  exact ⟨k, by rw [gensO_size]; omega, by rw [gensX_getElem k hk7]⟩

theorem exists_conj_X7 (hX7X : X7 ∈ X') (s : ↥X') (hs : orderOf s = 7) :
    ∃ g : ↥X', (g : Equiv.Perm (Fin 513)) * (s : Equiv.Perm (Fin 513)) * (g : Equiv.Perm (Fin 513))⁻¹
      ∈ Subgroup.zpowers X7 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hX7o : orderOf (⟨X7, hX7X⟩ : ↥X') = 7 := by
    rw [← Subgroup.orderOf_coe]
    exact X7_order
  have hG : ¬ 7 ^ 2 ∣ Nat.card ↥X' := by
    rw [card_X']
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_zpowers hG hs hX7o
  refine ⟨g, ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
  refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem commute_X7_of_conj {g s z : Equiv.Perm (Fin 513)} (hs : orderOf s = 7)
    (hg : g * s * g⁻¹ ∈ Subgroup.zpowers X7) (hz : Commute z (g * s * g⁻¹)) : Commute z X7 := by
  have h7 : orderOf (g * s * g⁻¹) = 7 := (orderOf_conj_group g s).trans hs
  have hle : Subgroup.zpowers (g * s * g⁻¹) ≤ Subgroup.zpowers X7 :=
    (Subgroup.zpowers_le).2 hg
  have hcard1 : Nat.card (Subgroup.zpowers (g * s * g⁻¹)) = 7 := by rw [Nat.card_zpowers, h7]
  have hcard2 : Nat.card (Subgroup.zpowers X7) = 7 := by rw [Nat.card_zpowers]; exact X7_order
  have heq : Subgroup.zpowers (g * s * g⁻¹) = Subgroup.zpowers X7 :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
  have hX7 : X7 ∈ Subgroup.zpowers (g * s * g⁻¹) := by rw [heq]; exact Subgroup.mem_zpowers X7
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hX7
  rw [← hk]
  exact hz.zpow_right k

theorem conj_commute_perm {g s z : Equiv.Perm (Fin 513)} (hc : z * (g * s * g⁻¹) = (g * s * g⁻¹) * z) :
    g⁻¹ * z * g * s = s * (g⁻¹ * z * g) := by
  calc g⁻¹ * z * g * s = g⁻¹ * (z * (g * s * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * s * g⁻¹) * z) * g := by rw [hc]
    _ = s * (g⁻¹ * z * g) := by group

theorem yFix3Wit_of_fixCheck (h : U38Fix.fixCheck () = true) : YFix3Wit ↥X' := by
  obtain ⟨hX7X, -, z₀, hz₀X, hz₀o, hz₀c⟩ := fixCheck_spec h
  intro s hs
  obtain ⟨g, hg⟩ := exists_conj_X7 hX7X s hs
  have hso : orderOf (s : Equiv.Perm (Fin 513)) = 7 := by rw [Subgroup.orderOf_coe]; exact hs
  have hcz : Commute z₀ X7 := hz₀c
  have hz₀g : Commute z₀ ((g : Equiv.Perm (Fin 513)) * (s : Equiv.Perm (Fin 513)) *
      (g : Equiv.Perm (Fin 513))⁻¹) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← hk]
    exact hcz.zpow_right k
  refine ⟨g⁻¹ * ⟨z₀, hz₀X⟩ * g, ?_, ?_⟩
  · have := orderOf_conj_group g⁻¹ (⟨z₀, hz₀X⟩ : ↥X')
    rw [inv_inv] at this
    rw [this, ← Subgroup.orderOf_coe]
    exact hz₀o
  · apply Subtype.ext
    exact conj_commute_perm (g := (g : Equiv.Perm (Fin 513))) (s := (s : Equiv.Perm (Fin 513)))
      (z := z₀) hz₀g.eq

open CFSG.Open CFSG.Open.StatedAPI CFSG.Blueprint.EvenSource in
theorem nonempty_X'_equiv_projSU : Nonempty (↥X' ≃* CFSG.PGLModel.projSU 3 2 3) := by
  have e1 : ↥X' ≃* P0 :=
    (MulEquiv.subgroupCongr X'_eq_range).trans (MonoidHom.ofInjective psiU38_injective).symm
  obtain ⟨e2⟩ : Nonempty (P0 ≃* CFSG.PGLModel.projSU 3 2 3) :=
    nonempty_mulEquiv_of_statedClassicalModel statedModel_P0
      (CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
        ⟨Nat.prime_two, by norm_num, le_rfl, by decide⟩ (MulEquiv.refl _))
  exact ⟨e1.trans e2⟩

theorem mem_X'_of_commute {γ x g : Equiv.Perm (Fin 513)} (hX7X : X7 ∈ X')
    (hkey : ∀ β ∈ U38G, β ^ 3 = 1 → β * X7 = X7 * β → β ∈ X')
    (hγΓ : γ ∈ U38G) (hgΓ : g ∈ U38G) (hgX : g ∈ X') (hγ3 : γ ^ 3 = 1) (hγx : γ * x = x * γ)
    (hxo : orderOf x = 7) (hg : g * x * g⁻¹ ∈ Subgroup.zpowers X7) : γ ∈ X' := by
  have hγ'3 : (g * γ * g⁻¹) ^ 3 = 1 := by rw [conj_pow, hγ3]; group
  have hcomm' : Commute (g * γ * g⁻¹) (g * x * g⁻¹) := by
    unfold Commute SemiconjBy
    calc g * γ * g⁻¹ * (g * x * g⁻¹) = g * (γ * x) * g⁻¹ := by group
      _ = g * (x * γ) * g⁻¹ := by rw [hγx]
      _ = g * x * g⁻¹ * (g * γ * g⁻¹) := by group
  have hX7comm : g * γ * g⁻¹ * X7 = X7 * (g * γ * g⁻¹) :=
    (commute_X7_of_conj hxo hg hcomm').eq
  have hγ'X : g * γ * g⁻¹ ∈ X' :=
    hkey _ (U38G.mul_mem (U38G.mul_mem hgΓ hγΓ) (U38G.inv_mem hgΓ)) hγ'3 hX7comm
  have h1 : g⁻¹ * (g * γ * g⁻¹) * g ∈ X' := X'.mul_mem (X'.mul_mem (X'.inv_mem hgX) hγ'X) hgX
  have h2 : g⁻¹ * (g * γ * g⁻¹) * g = γ := by group
  rwa [h2] at h1

theorem yFixClaim_of_fixCheck (h : U38Fix.fixCheck () = true) : YFixClaim ↥X' := by
  obtain ⟨hX7X, hkey, -⟩ := fixCheck_spec h
  have hbij := rhoU38_bijective (X := ↥X') nonempty_X'_equiv_projSU
  intro β hβ3 x hx hβx
  obtain ⟨γ, hγ⟩ := hbij.2 β
  have hγ3 : γ ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hγ, hβ3, map_one]
  have h1 : (x : Equiv.Perm (Fin 513)) =
      (γ : Equiv.Perm (Fin 513)) * (x : Equiv.Perm (Fin 513)) * (γ : Equiv.Perm (Fin 513))⁻¹ := by
    have := rhoU38_apply γ x
    rw [hγ, hβx] at this
    exact this
  have hγx : (γ : Equiv.Perm (Fin 513)) * (x : Equiv.Perm (Fin 513)) =
      (x : Equiv.Perm (Fin 513)) * (γ : Equiv.Perm (Fin 513)) := by
    have h2 : (x : Equiv.Perm (Fin 513)) * (γ : Equiv.Perm (Fin 513)) =
        (γ : Equiv.Perm (Fin 513)) * (x : Equiv.Perm (Fin 513)) := by
      calc (x : Equiv.Perm (Fin 513)) * (γ : Equiv.Perm (Fin 513))
          = (γ * x * (γ : Equiv.Perm (Fin 513))⁻¹) * (γ : Equiv.Perm (Fin 513)) := by rw [← h1]
        _ = (γ : Equiv.Perm (Fin 513)) * x := by group
    exact h2.symm
  have hxo : orderOf (x : Equiv.Perm (Fin 513)) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
  obtain ⟨g, hg⟩ := exists_conj_X7 hX7X x hx
  have h4 : (γ : Equiv.Perm (Fin 513)) ^ 3 = 1 := by
    have := congrArg Subtype.val hγ3
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  have hγX : (γ : Equiv.Perm (Fin 513)) ∈ X' :=
    mem_X'_of_commute hX7X hkey γ.2 (X'_le_U38G g.2) g.2 h4 hγx hxo hg
  refine ⟨⟨(γ : Equiv.Perm (Fin 513)), hγX⟩, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact h4
  · intro y
    apply Subtype.ext
    have h3 := rhoU38_apply γ y
    rw [hγ] at h3
    rw [h3]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]

end Spec

end CFSG.LocalAnalysis.UniquenessCase.UCK

