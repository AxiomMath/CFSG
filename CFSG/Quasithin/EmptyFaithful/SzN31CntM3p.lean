module

public import CFSG.Quasithin.Background.G8Dihedral
public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpA
public import CFSG.Quasithin.EmptyFaithful.SzN31CntGrpB
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11 CFSG.Open

section CaseA

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem counting_caseA {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hY : pCoreOf p Γ ≠ ⊥)
    (hfaith : A ⊓ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) = ⊥) :
    m = 1 ∧ p = 5 ∧ Module.finrank (ZMod 2) V = 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have := finite_linearEquiv_zmod2 V
  have hp2 : p ≠ 2 := by omega
  have hYp : IsPGroup p (pCoreOf p Γ) := isPGroup_pCoreOf p Γ
  have h81 : G81 (pCoreOf p Γ) A A :=
    { elemAbelian := hyp.A_elem
      le_pGroup := le_rfl
      pGroup := isPGroup_of_isElemAbelian hyp.A_elem
      le_normalizer := fun a ha => le_normalizer_pCoreOf p Γ (hyp.A_le ha)
      nilpotent := hYp.isNilpotent
      odd := odd_card_pCoreOf hp hp2 Γ
      ne_bot := hY }
  obtain ⟨Hs, q, hH, hAle, -, hx⟩ := g8_6 h81 hyp.A_ne hyp.A_card hfaith
  choose x hxY hxH hxo using hx
  obtain ⟨Fr, hFx, hFp, -⟩ :=
    exists_frame_of_dihedralFamily hH hyp.A_elem hAle hyp.A_card x hxH hxo
  have hq : ∀ i, q i = p := fun i =>
    G8.prime_orderOf_eq_of_mem_pGroup hYp (hxY i) (hxo i) (hH.prime i)
  have hxne : ∀ i, x i ≠ 1 := fun i h1 => by
    have h2 := hxo i
    rw [h1, orderOf_one, hq i] at h2
    exact hp.one_lt.ne h2
  have hadm : Adm Fr ⊤ Finset.univ :=
    adm_top Fr Finset.univ fun i _ => by rw [congrFun hFx i]; exact hxne i
  have hdim := dim_lemma Fr Finset.univ ⊤ hadm
  rw [finrank_top] at hdim
  have hsum : ∑ j ∈ Finset.univ, gFun (Fr.p j) = m * gFun p := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [hFp, hq j])]
    simp
  rw [hsum] at hdim
  have h4 := gFun_ge_four h5
  have hb := hyp.bound
  have hm1 := hyp.A_ne
  have hm_le : m ≤ 1 := by nlinarith
  have hm : m = 1 := le_antisymm hm_le hm1
  subst hm
  have hg4 : gFun p = 4 := by omega
  exact ⟨rfl, eq_five_of_gFun_eq_four hp hp2 hg4, by omega⟩

end CaseA

section CaseB

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem frame_counting_bound {k n : ℕ} (hk : 0 < k) (Fr : Frame V (Fin (k + n)))
    (hx1 : ∀ i, Fr.x i ≠ 1) {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hhigh : ∀ j : Fin n, Fr.p (Fin.natAdd k j) = p) {Y : Subgroup (GLV V)} (hYp : IsPGroup p Y)
    (hYfix : fixedSpace Y = ⊥)
    (hxY : ∀ y ∈ Y, y * Fr.x (Fin.castAdd n ⟨0, hk⟩) = Fr.x (Fin.castAdd n ⟨0, hk⟩) * y)
    (haY : ∀ y ∈ Y, y * Fr.a (Fin.castAdd n ⟨0, hk⟩) = Fr.a (Fin.castAdd n ⟨0, hk⟩) * y) :
    2 * k + 4 * n + 1 ≤ Module.finrank (ZMod 2) V := by
  set i0 : Fin (k + n) := Fin.castAdd n ⟨0, hk⟩ with hi0
  have hadm : Adm Fr ⊤ Finset.univ := adm_top Fr Finset.univ fun i _ => hx1 i
  have hpb := peel_bound Fr Finset.univ ⊤ hadm (Finset.mem_univ i0)
  rw [finrank_top] at hpb
  have hWne := peel_W_ne_bot Fr Finset.univ ⊤ hadm (Finset.mem_univ i0)
  have hWinv : ∀ y ∈ Y, ∀ w ∈ fixSp V (Fr.a i0) (commSp V (Fr.x i0) ⊤),
      y w ∈ fixSp V (Fr.a i0) (commSp V (Fr.x i0) ⊤) := fun y hy =>
    peel_W_invariant_of_comm (hxY y hy) (haY y hy) fun s _ => Submodule.mem_top
  have hW0 : ∀ v ∈ fixSp V (Fr.a i0) (commSp V (Fr.x i0) ⊤), (∀ y ∈ Y, y v = v) → v = 0 := by
    intro v _ hfix
    have hv : v ∈ fixedSpace Y := fun y hy => hfix y hy
    rw [hYfix] at hv
    exact (Submodule.mem_bot (ZMod 2)).1 hv
  have hd := pgroup_dvd_two_pow hp Y hYp _ hWinv hW0
  have hWpos : 0 < Module.finrank (ZMod 2) (fixSp V (Fr.a i0) (commSp V (Fr.x i0) ⊤)) := by
    have : Module.Finite (ZMod 2) (fixSp V (Fr.a i0) (commSp V (Fr.x i0) ⊤)) :=
      Module.Finite.of_finite
    exact Nat.pos_of_ne_zero fun h => hWne (Submodule.finrank_eq_zero.1 h)
  have h3 := three_le_of_dvd hp h5 hWpos hd
  have hlo : ∀ j : Fin (k + n), (if j.val < k then 2 else 4) ≤ gFun (Fr.p j) := by
    intro j
    by_cases hj : j.val < k
    · simp only [hj, ↓reduceIte]
      exact gFun_ge_two (Fr.prime j) (Fr.odd j)
    · simp only [hj, ↓reduceIte]
      have hjn : j.val - k < n := by omega
      have hjj : Fin.natAdd k ⟨j.val - k, hjn⟩ = j := Fin.ext (by simp; omega)
      have := hhigh ⟨j.val - k, hjn⟩
      rw [hjj] at this
      rw [this]
      exact gFun_ge_four h5
  have hsum1 : ∑ j ∈ Finset.univ.erase i0, (if j.val < k then 2 else 4) ≤
      ∑ j ∈ Finset.univ.erase i0, gFun (Fr.p j) := Finset.sum_le_sum fun j _ => hlo j
  have hsum2 := Finset.sum_erase_add Finset.univ (fun j : Fin (k + n) => if j.val < k then 2 else 4)
    (Finset.mem_univ i0)
  have hsum3 : ∑ j : Fin (k + n), (if j.val < k then 2 else 4) = 2 * k + 4 * n := by
    rw [Fin.sum_univ_add]
    simp [Fin.is_lt]
    ring
  have hi0k : i0.val < k := by simp [hi0, hk]
  simp only [hi0k, ↓reduceIte] at hsum2
  omega

theorem counting_caseB {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G94Hyp Γ A m) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) (hY : pCoreOf p Γ ≠ ⊥) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hm : m = k + n)
    (hB : Nat.card ↥(A ⊓ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V))) = 2 ^ k) : False := by
  subst hm
  have : Fact p.Prime := ⟨hp⟩
  have := finite_linearEquiv_zmod2 V
  have hp2 : p ≠ 2 := by omega
  have hYp : IsPGroup p (pCoreOf p Γ) := isPGroup_pCoreOf p Γ
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    G8.commute_of_isElemAbelian hyp.A_elem ha ha'
  have h81 : G81 ((genFittingFitting ↥Γ).map Γ.subtype) A A :=
    { elemAbelian := hyp.A_elem
      le_pGroup := le_rfl
      pGroup := isPGroup_of_isElemAbelian hyp.A_elem
      le_normalizer := fun a ha => le_normalizer_fitting Γ (hyp.A_le ha)
      nilpotent := isNilpotent_fitting_map Γ
      odd := g94_odd_card_fitting hyp
      ne_bot := g94_fitting_ne_bot hyp }
  obtain ⟨D, hDc, Hs, q, hH, hB1, hB2, hD1, -, hc1, hc2⟩ := g8_7 h81 hk hn
    (g94_inf_centralizer_fitting_eq_bot hyp) (pCoreOf_le_fitting hp Γ)
    (fun a ha => le_normalizer_pCoreOf p Γ (hyp.A_le ha)) hyp.A_card hB
  obtain ⟨hBA, hDA, hBD, hsup⟩ := hDc
  have hDcard : Nat.card D = 2 ^ n := by
    have h1 := G8.card_eq_mul_of_complement hAcomm ⟨hBA, hDA, hBD, hsup⟩
    rw [hyp.A_card, hB] at h1
    have hpos : 0 < 2 ^ k := by positivity
    have h2 : 2 ^ k * 2 ^ n = 2 ^ k * Nat.card D := by rw [← h1, ← pow_add]
    exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm
  have hxclaim : ∀ i : Fin (k + n), ∃ x : GLV V, x ∈ Hs i ∧ orderOf x = q i := by
    intro i
    induction i using Fin.addCases with
    | left j =>
      obtain ⟨x, -, hxH, hxo⟩ := hc1 j
      exact ⟨x, hxH, hxo⟩
    | right j =>
      obtain ⟨x, -, hxH, hxo⟩ := hc2 j
      exact ⟨x, hxH, hxo⟩
  choose x hxH hxo using hxclaim
  obtain ⟨Fr, hFx, hFp, hFaH, -, -⟩ := exists_frame_two_blocks hH
    (G8.isElemAbelian_mono hyp.A_elem hBA) (G8.isElemAbelian_mono hyp.A_elem hDA) hB1 hD1 hB
    hDcard x hxH hxo
  have hqn : ∀ j : Fin n, q (Fin.natAdd k j) = p := fun j => by
    obtain ⟨y, hyY, -, hyo⟩ := hc2 j
    exact G8.prime_orderOf_eq_of_mem_pGroup hYp hyY hyo (hH.prime _)
  have hHC : ∀ i : Fin k,
      Hs (Fin.castAdd n i) ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) := by
    intro i
    refine (le_iSup (fun i : Fin k => Hs (Fin.castAdd n i)) i).trans (hB2.trans ?_)
    exact sup_le inf_le_right
      (inf_le_right.trans (Subgroup.centralizer_le (by exact_mod_cast le_sup_right)))
  have hx1 : ∀ i, Fr.x i ≠ 1 := fun i h1 => by
    have h2 := hxo i
    rw [← congrFun hFx i, h1, orderOf_one] at h2
    exact (hH.prime i).one_lt.ne h2
  have hbound := frame_counting_bound hk Fr hx1 hp h5 (fun j => by rw [hFp, hqn]) hYp
    (g94_fixedSpace_pCoreOf_eq_bot hyp hY)
    (fun y hy => by
      rw [hFx]
      exact Subgroup.mem_centralizer_iff.mp (hHC ⟨0, hk⟩ (hxH _)) y hy)
    (fun y hy => Subgroup.mem_centralizer_iff.mp (hHC ⟨0, hk⟩ (hFaH _)) y hy)
  have hbd := hyp.bound
  omega

end CaseB

section Headline

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem counting_prime_ge_five {Γ A : Subgroup (GLV V)} {m : ℕ} (hyp : G11.G94Hyp Γ A m) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p)
    (hnot : ¬ A ≤ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V))) :
    m = 1 ∧ p = 5 ∧ Module.finrank (ZMod 2) V = 4 := by
  have := finite_linearEquiv_zmod2 V
  have hY : pCoreOf p Γ ≠ ⊥ := by
    intro h
    apply hnot
    rw [h]
    intro a _
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => by rw [Subgroup.mem_bot.mp hg]; simp
  have hBA : A ⊓ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) ≤ A := inf_le_left
  obtain ⟨k, hk⟩ := ((isPGroup_of_isElemAbelian hyp.A_elem).to_le hBA).exists_card_eq
  have hBne : A ⊓ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) ≠ A := by
    intro h
    apply hnot
    rw [← h]
    exact inf_le_right
  have hkm : k < m := by
    by_contra hge
    push Not at hge
    have : Nat.card A ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V))) := by
      rw [hyp.A_card, hk]
      exact Nat.pow_le_pow_right (by norm_num) hge
    exact hBne (Subgroup.eq_of_le_of_card_ge hBA this)
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · have hbot : A ⊓ Subgroup.centralizer (pCoreOf p Γ : Set (GLV V)) = ⊥ :=
      Subgroup.card_eq_one.mp (by rw [hk, hk0]; rfl)
    exact counting_caseA hyp hp h5 hY hbot
  · exact (counting_caseB hyp hp h5 hY hkpos (Nat.sub_pos_of_lt hkm) (by omega) hk).elim

end Headline

end CFSG.Quasithin.SzN31
