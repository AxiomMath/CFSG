module

public import CFSG.Sporadic.Th.Recog.MFactsB.Letters
public import CFSG.Sporadic.Th.Recog.MFactsB.Lift
public import CFSG.Sporadic.Th.Recog.MFactsB.DTransfer
public import CFSG.Sporadic.Th.Recog.AltNine
public import CFSG.GH74.Uniqueness.Section126Dihedral
public import CFSG.CGT.Foote82.T66.BranchAOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Sporadic.He.Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Recog.MFactsB
open CFSG.Sporadic.Recognition.PresentedWords
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.CosetTable

private theorem D8M_eq_closure : D8M = Subgroup.closure ({cM, e₀} : Set ↥Max3.M) := rfl

private theorem e₀_eq : e₀ = dM * cM * dM := rfl

private theorem cM_eq_incDP_one : cM = incDP (dPD 1) := by
  apply Subtype.ext
  rw [coe_incDP_dPD]
  rfl

private theorem dM_eq_incDP_two : dM = incDP (dPD 2) := by
  apply Subtype.ext
  rw [coe_incDP_dPD]
  rfl

private theorem orderOf_dP_eq_two {j : Fin 6} (hj : j = 1 ∨ j = 2) :
    orderOf (dP j) = 2 := by
  rcases hj with rfl | rfl
  · exact orderOf_eq_prime (by
      have hbeq : (comp 51 letArr[1]! letArr[1]! == idTab 51) = true := by decide +kernel
      exact ((tabRep_dP 1).comp (tabRep_dP 1)).beq_iff TabRep.idTab |>.1 hbeq) (by
      intro h
      have hne_tab : letArr[1]! ≠ idTab 51 := by decide +kernel
      exact hne_tab ((tabRep_dP 1).tab_eq (h.symm ▸ TabRep.idTab)))
  · exact orderOf_eq_prime (by
      have hbeq : (comp 51 letArr[2]! letArr[2]! == idTab 51) = true := by decide +kernel
      exact ((tabRep_dP 2).comp (tabRep_dP 2)).beq_iff TabRep.idTab |>.1 hbeq) (by
      intro h
      have hne_tab : letArr[2]! ≠ idTab 51 := by decide +kernel
      exact hne_tab ((tabRep_dP 2).tab_eq (h.symm ▸ TabRep.idTab)))

private theorem orderOf_dPD_eq_two {j : Fin 6} (hj : j = 1 ∨ j = 2) :
    orderOf (dPD j) = 2 := by
  change orderOf (⟨dP j, dP_mem j⟩ : ↥DP) = 2
  rw [Subgroup.orderOf_mk]
  exact orderOf_dP_eq_two hj

private theorem orderOf_cM : orderOf cM = 2 := by
  rw [cM_eq_incDP_one, orderOf_incDP, orderOf_dPD_eq_two (Or.inl rfl)]

private theorem orderOf_e₀ : orderOf e₀ = 2 := by
  rw [e₀_eq]
  have hd : dM⁻¹ = dM := inv_eq_of_mul_eq_one_right dM_mul_self
  have h : dM * cM * dM = MulAut.conj (G := ↥Max3.M) dM cM := by
    rw [MulAut.conj_apply, hd]
  rw [h, MulEquiv.orderOf_eq, orderOf_cM]

private def w4 : List (Fin 6 × Bool) := [(1, true), (2, true), (1, true), (2, true)]

private def t4 : Tab := wTab letArr (letInv ()) w4

private theorem orderOf_gP : orderOf (wprod dPD w4) = 4 := by
  have hrep : TabRep t4 (wprod dP w4) := tabRep_wTab tabRep_dP tabRep_letInv w4
  have h2 : (comp 51 t4 t4 == idTab 51) = false := by decide +kernel
  have h4 : (comp 51 (comp 51 t4 t4) (comp 51 t4 t4) == idTab 51) = true := by
    decide +kernel
  have hnot : ¬ (wprod dP w4) ^ 2 = 1 := by
    intro h
    have hbeq := ((hrep.comp hrep).beq_iff TabRep.idTab).2 (by
      rw [pow_two] at h
      exact h)
    rw [hbeq] at h2
    exact Bool.noConfusion h2
  have hfin : (wprod dP w4) ^ 4 = 1 := by
    have hbeq := ((hrep.comp hrep).comp (hrep.comp hrep)).beq_iff TabRep.idTab |>.1 h4
    rw [show (wprod dP w4) ^ 4 = ((wprod dP w4) * (wprod dP w4)) *
      ((wprod dP w4) * (wprod dP w4)) by simp [pow_succ, pow_two, mul_assoc]]
    exact hbeq
  have hordP : orderOf (wprod dP w4) = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := wprod dP w4) (by simpa using hnot)
      (by simpa using hfin)
    simpa using this
  have hcoe : ((wprod dPD w4 : ↥DP) : Equiv.Perm (Fin 51)) = wprod dP w4 :=
    map_wprod DP.subtype dPD w4
  have hordDP : orderOf ((wprod dPD w4 : ↥DP) : Equiv.Perm (Fin 51)) =
      orderOf (wprod dPD w4) :=
    orderOf_injective (Subgroup.subtype DP) DP.subtype_injective (wprod dPD w4)
  rw [← hordDP, hcoe]
  exact hordP

private theorem wprod_w4 : wprod dPD w4 = dPD 1 * (dPD 2 * (dPD 1 * dPD 2)) := by
  rw [w4, wprod_cons, wprod_cons, wprod_cons, wprod_cons, wprod_nil]
  simp only [Bool.true_eq_false, ↓reduceIte, mul_one]

private theorem cM_mul_e₀_eq : cM * e₀ = incDP (wprod dPD w4) := by
  rw [wprod_w4, map_mul, map_mul, map_mul, ← cM_eq_incDP_one, ← dM_eq_incDP_two, e₀_eq]
  group

private theorem orderOf_cM_mul_e₀ : orderOf (cM * e₀) = 4 := by
  rw [cM_mul_e₀_eq, orderOf_incDP, orderOf_gP]

theorem card_D8M : Nat.card ↥D8M = 8 := by
  rw [D8M_eq_closure, CFSG.GH74.Uniqueness.card_closure_pair_involutions]
  · rw [orderOf_cM_mul_e₀]
  · exact orderOf_cM
  · exact orderOf_e₀

theorem nonempty_D8M_mulEquiv : Nonempty (↥D8M ≃* DihedralGroup 4) := by
  rw [D8M_eq_closure]
  refine CFSG.CGT.Foote82.BranchAAux.nonempty_closure_mulEquiv_dihedral ?_ ?_ ?_ (by norm_num)
  · exact cM_mul_self
  · exact e₀_mul_self
  · exact orderOf_cM_mul_e₀

private theorem disjoint_D8M_zpowers_s :
    Disjoint D8M (Subgroup.zpowers sLetter) := by
  refine Subgroup.disjoint_of_coprime_natCard ?_
  rw [card_D8M, Nat.card_zpowers, orderOf_sLetter]
  norm_num

private theorem D8M_le_normalizer_zpowers_s :
    D8M ≤ Subgroup.normalizer (Subgroup.zpowers sLetter : Set ↥Max3.M) := by
  have hle : Subgroup.centralizer ({sLetter} : Set ↥Max3.M) ≤
      Subgroup.centralizer (Subgroup.zpowers sLetter : Set ↥Max3.M) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le]
    intro d hd
    exact (Subgroup.mem_centralizer_singleton_iff (g := sLetter) (k := d)).mp hd
  exact (D8M_le_centralizer_s.trans hle).trans (Subgroup.centralizer_le_normalizer _)

private theorem card_D8M_sup_zpowers_s :
    Nat.card ↥(D8M ⊔ Subgroup.zpowers sLetter) = 8 * 7 := by
  rw [sup_comm, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
    (Subgroup.zpowers sLetter) D8M D8M_le_normalizer_zpowers_s
    disjoint_D8M_zpowers_s.symm, Nat.card_zpowers, orderOf_sLetter, card_D8M]

private theorem card_centralizer_sLetter
    (h8 : Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓
      Subgroup.centralizer ({sLetter} : Set ↥Max3.M)) = 8) :
    Nat.card ↥(Subgroup.centralizer ({sLetter} : Set ↥Max3.M)) = 56 := by
  have hbound := card_centralizer_le_mul (g := sLetter)
  rw [h8] at hbound
  have hkaps : orderOf (Max3.InvRep.kap sLetter) = 7 :=
    orderOf_kap_of_orderOf_eq_prime (p := 7) (by norm_num) orderOf_sLetter
  have hcardA : Nat.card ↥(Subgroup.centralizer ({Max3.InvRep.kap sLetter} :
      Set (alternatingGroup (Fin 9)))) = 7 :=
    card_centralizer_of_orderOf_eq_seven hkaps
  rw [hcardA] at hbound
  let C : Subgroup ↥Max3.M := Subgroup.centralizer ({sLetter} : Set ↥Max3.M)
  have hjoin_le : D8M ⊔ Subgroup.zpowers sLetter ≤ C := by
    refine sup_le D8M_le_centralizer_s ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hjoin_card : Nat.card ↥(D8M ⊔ Subgroup.zpowers sLetter) = 8 * 7 :=
    card_D8M_sup_zpowers_s
  have hC_le : Nat.card ↥C ≤ 8 * 7 := by
    simpa [C] using hbound
  have hjoin_card_le : Nat.card ↥(D8M ⊔ Subgroup.zpowers sLetter) ≤ Nat.card ↥C :=
    Subgroup.card_le_of_le hjoin_le
  rw [hjoin_card] at hjoin_card_le
  have hCcard : Nat.card ↥C = 56 := by omega
  simpa [C] using hCcard

private theorem map_centralizer_conj (m a : ↥Max3.M) :
    (Subgroup.centralizer ({a} : Set ↥Max3.M)).map
        (MulAut.conj (G := ↥Max3.M) m : ↥Max3.M →* ↥Max3.M) =
      Subgroup.centralizer ({MulAut.conj (G := ↥Max3.M) m a} : Set ↥Max3.M) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    calc MulAut.conj (G := ↥Max3.M) m z * MulAut.conj (G := ↥Max3.M) m a
        = MulAut.conj (G := ↥Max3.M) m (z * a) := by rw [map_mul]
      _ = MulAut.conj (G := ↥Max3.M) m (a * z) := by rw [hz]
      _ = MulAut.conj (G := ↥Max3.M) m a * MulAut.conj (G := ↥Max3.M) m z := by
        rw [map_mul]
  · intro hy
    refine ⟨MulAut.conj (G := ↥Max3.M) m⁻¹ y, ?_, ?_⟩
    · have hy' : MulAut.conj (G := ↥Max3.M) m
          (MulAut.conj (G := ↥Max3.M) m⁻¹ y) = y := by
        simp only [MulAut.conj_apply]
        group
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply (MulAut.conj (G := ↥Max3.M) m).injective
      rw [map_mul, map_mul, hy']
      exact hy
    · change MulAut.conj (G := ↥Max3.M) m
          (MulAut.conj (G := ↥Max3.M) m⁻¹ y) = y
      simp only [MulAut.conj_apply]
      group

private theorem card_centralizer_of_orderOf_eq_seven_M
    (h8 : Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓
      Subgroup.centralizer ({sLetter} : Set ↥Max3.M)) = 8)
    {x : ↥Max3.M} (hx : orderOf x = 7) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥Max3.M)) = 56 := by
  have hx7 : orderOf (Max3.InvRep.kap x) = 7 :=
    orderOf_kap_of_orderOf_eq_prime (p := 7) (by norm_num) hx
  have hs7 : orderOf (Max3.InvRep.kap sLetter) = 7 :=
    orderOf_kap_of_orderOf_eq_prime (p := 7) (by norm_num) orderOf_sLetter
  have hconj : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap sLetter) :=
    isConj_of_orderOf_eq_seven hx7 hs7
  obtain ⟨m, hm⟩ := exists_conj_of_isConj_kap (p := 7) (by norm_num) hx orderOf_sLetter hconj
  let φ : ↥Max3.M ≃* ↥Max3.M := MulAut.conj (G := ↥Max3.M) m
  have hφx : φ x = sLetter := by
    change m * x * m⁻¹ = sLetter
    exact hm
  have hmap : (Subgroup.centralizer ({x} : Set ↥Max3.M)).map
      (φ : ↥Max3.M →* ↥Max3.M) =
      Subgroup.centralizer ({sLetter} : Set ↥Max3.M) := by
    simpa [φ, hφx] using map_centralizer_conj m x
  have hcard := Subgroup.card_map_of_injective
    (K := Subgroup.centralizer ({x} : Set ↥Max3.M))
    (f := (φ : ↥Max3.M →* ↥Max3.M)) φ.injective
  rw [hmap] at hcard
  exact hcard.symm.trans (card_centralizer_sLetter h8)

private theorem conj_D8M_le_centralizer {x : ↥Max3.M} {m : ↥Max3.M}
    (hm : m * x * m⁻¹ = sLetter) :
    D8M.map (MulAut.conj (G := ↥Max3.M) m⁻¹ : ↥Max3.M →* ↥Max3.M) ≤
      Subgroup.centralizer ({x} : Set ↥Max3.M) := by
  intro d hd
  obtain ⟨d0, hd0, rfl⟩ := Subgroup.mem_map.mp hd
  have hd0c : d0 * sLetter = sLetter * d0 :=
    (Subgroup.mem_centralizer_singleton_iff (g := sLetter) (k := d0)).mp
      (D8M_le_centralizer_s hd0)
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply (MulAut.conj (G := ↥Max3.M) m).injective
  rw [map_mul, map_mul]
  simp only [MulAut.conj_apply]
  rw [hm]
  change m * (m⁻¹ * d0 * m) * m⁻¹ * sLetter =
    sLetter * (m * (m⁻¹ * d0 * m) * m⁻¹)
  have hleft : m * (m⁻¹ * d0 * m) * m⁻¹ = d0 := by group
  rw [hleft]
  exact hd0c

private theorem exists_D_of_conj_s
    (h8 : Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓
      Subgroup.centralizer ({sLetter} : Set ↥Max3.M)) = 8)
    {x : ↥Max3.M} (hx : orderOf x = 7) {m : ↥Max3.M}
    (hm : m * x * m⁻¹ = sLetter) :
    ∃ D : Subgroup ↥Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
      D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧
        Nonempty (↥D ≃* DihedralGroup 4) := by
  let ψ : ↥Max3.M ≃* ↥Max3.M := MulAut.conj (G := ↥Max3.M) m⁻¹
  let D : Subgroup ↥Max3.M := D8M.map (ψ : ↥Max3.M →* ↥Max3.M)
  have hDcard : Nat.card ↥D = 8 := by
    dsimp only [D]
    rw [Subgroup.card_map_of_injective (K := D8M)
      (f := (ψ : ↥Max3.M →* ↥Max3.M)) ψ.injective, card_D8M]
  have hdisj : Disjoint D (Subgroup.zpowers x) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hDcard, Nat.card_zpowers, hx]
    norm_num
  have hD_le_cent : D ≤ Subgroup.centralizer ({x} : Set ↥Max3.M) :=
    conj_D8M_le_centralizer (x := x) (m := m) hm
  have hxcent : x ∈ Subgroup.centralizer (D : Set ↥Max3.M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_singleton_iff (g := x) (k := d)).mp (hD_le_cent hd)
  have hnormal : Subgroup.zpowers x ≤ Subgroup.normalizer (D : Set ↥Max3.M) :=
    (Subgroup.zpowers_le.mpr hxcent).trans (Subgroup.centralizer_le_normalizer _)
  have hjoin_card : Nat.card ↥(D ⊔ Subgroup.zpowers x) = 8 * 7 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer D
      (Subgroup.zpowers x) hnormal hdisj, hDcard, Nat.card_zpowers, hx]
  have hjoin_le : D ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set ↥Max3.M) := by
    refine sup_le hD_le_cent ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsup : D ⊔ Subgroup.zpowers x = Subgroup.centralizer ({x} : Set ↥Max3.M) := by
    refine Subgroup.eq_of_le_of_card_ge hjoin_le ?_
    rw [card_centralizer_of_orderOf_eq_seven_M h8 hx, hjoin_card]
  refine ⟨D, disjoint_iff.mp hdisj, hsup, ?_⟩
  obtain ⟨e⟩ := nonempty_D8M_mulEquiv
  have hmap := Subgroup.equivMapOfInjective D8M (ψ : ↥Max3.M →* ↥Max3.M) ψ.injective
  exact ⟨hmap.symm.trans e⟩

theorem seven_of_card_Q_inf_centralizer_s
    (h8 : Nat.card ↥(Max3.Q.subgroupOf Max3.M ⊓
      Subgroup.centralizer ({sLetter} : Set ↥Max3.M)) = 8) :
    ∀ x : ↥Max3.M, orderOf x = 7 →
      ∃ D : Subgroup ↥Max3.M, D ⊓ Subgroup.zpowers x = ⊥ ∧
        D ⊔ Subgroup.zpowers x = Subgroup.centralizer {x} ∧
          Nonempty (↥D ≃* DihedralGroup 4) := by
  intro x hx
  have hx7 : orderOf (Max3.InvRep.kap x) = 7 :=
    orderOf_kap_of_orderOf_eq_prime (p := 7) (by norm_num) hx
  have hs7 : orderOf (Max3.InvRep.kap sLetter) = 7 :=
    orderOf_kap_of_orderOf_eq_prime (p := 7) (by norm_num) orderOf_sLetter
  have hconj : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap sLetter) :=
    isConj_of_orderOf_eq_seven hx7 hs7
  obtain ⟨m, hm⟩ := exists_conj_of_isConj_kap (p := 7) (by norm_num) hx orderOf_sLetter hconj
  exact exists_D_of_conj_s h8 hx hm

end CFSG.Sporadic.Th.Recog
