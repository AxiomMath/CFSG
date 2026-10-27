module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrWeylA
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NormalFourGeometry
public import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open CFSG.ProperTwoGeneratedCore CFSG.LargeEvenClassification.Helpers

private lemma ct_rm8_zpowers_involution_eq_one_or {G : Type} [Group G] {a y : G}
    (ha2 : a * a = 1) (hy : y ∈ Subgroup.zpowers a) : y = 1 ∨ y = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  by_cases ha1 : a = 1
  · left; rw [ha1, one_zpow]
  · have horda : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha1
    have hmod : k % (2 : ℤ) = 0 ∨ k % (2 : ℤ) = 1 := by
      have h1 : 0 ≤ k % (2 : ℤ) := Int.emod_nonneg k (by norm_num)
      have h2 : k % (2 : ℤ) < 2 := Int.emod_lt_of_pos k (by norm_num)
      omega
    have hred : a ^ (k % (2 : ℤ)) = a ^ k := by
      have := zpow_mod_orderOf a k
      rwa [horda] at this
    rcases hmod with h | h
    · left; rw [← hred, h, zpow_zero]
    · right; rw [← hred, h, zpow_one]

private lemma ct_rm8_U4_mem {G : Type} [Group G] (sa sb : G)
    (hsa2 : sa * sa = 1) (hsb2 : sb * sb = 1) (hsab : sa * sb = sb * sa) :
    ∀ x ∈ (Subgroup.zpowers sa ⊔ Subgroup.zpowers sb : Subgroup G),
      x ∈ ({1, sa, sb, sa * sb} : Set G) := by
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      rcases hy with hy | hy
      · rcases ct_rm8_zpowers_involution_eq_one_or hsa2 hy with rfl | rfl <;> simp
      · rcases ct_rm8_zpowers_involution_eq_one_or hsb2 hy with rfl | rfl <;> simp
  | one => simp
  | mul y z hy hz ihy ihz =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ihy ihz ⊢
      rcases ihy with rfl | rfl | rfl | rfl <;> rcases ihz with rfl | rfl | rfl | rfl <;>
        grind
  | inv y hy ihy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ihy ⊢
      have hsa_inv : sa⁻¹ = sa := inv_eq_of_mul_eq_one_right hsa2
      have hsb_inv : sb⁻¹ = sb := inv_eq_of_mul_eq_one_right hsb2
      rcases ihy with rfl | rfl | rfl | rfl
      · simp
      · exact Or.inr (Or.inl hsa_inv)
      · exact Or.inr (Or.inr (Or.inl hsb_inv))
      · right; right; right
        rw [mul_inv_rev, hsa_inv, hsb_inv, hsab]

private lemma ct_rm8_commute_of_sq_mul_sq {G : Type} [Group G] {a b : G}
    (h : (a * b) * (a * b) = 1) (ha : a * a = 1) (hb : b * b = 1) : a * b = b * a := by
  have h1 : a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
  exact h1

private lemma ct_rm8_card_G2 : Nat.card (CoxeterMatrix.G₂).Group = 12 := by
  let cs := (CoxeterMatrix.G₂).toCoxeterSystem
  have hs : cs.simple 0 * cs.simple 0 = 1 := cs.simple_mul_simple_self 0
  have ht : cs.simple 1 * cs.simple 1 = 1 := cs.simple_mul_simple_self 1
  have hs1 : cs.simple 0 ≠ 1 := cs.simple_ne_one 0
  have ht1 : cs.simple 1 ≠ 1 := cs.simple_ne_one 1
  have hn : orderOf (cs.simple 0 * cs.simple 1) = 6 := by
    rw [cs.orderOf_simple_mul_simple]; decide
  have hgen : Subgroup.closure ({cs.simple 0, cs.simple 1} : Set (CoxeterMatrix.G₂).Group) = ⊤ := by
    rw [← cs.subgroup_closure_range_simple]
    congr 1
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · exact ⟨0, hx.symm⟩
      · exact ⟨1, hx.symm⟩
    · rintro ⟨i, hi⟩
      rw [← hi]
      have hi' : i = 0 ∨ i = 1 := by
        have h : i.val = 0 ∨ i.val = 1 := by omega
        rcases h with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi' with rfl | rfl <;> simp
  have e : DihedralGroup 6 ≃* (CoxeterMatrix.G₂).Group :=
    TauCeti.dihedralGroupMulEquiv (s := cs.simple 0) (t := cs.simple 1) (n := 6)
      hs ht hs1 ht1 hn hgen
  calc Nat.card (CoxeterMatrix.G₂).Group = Nat.card (DihedralGroup 6) :=
        (Nat.card_congr e.toEquiv).symm
    _ = 12 := by rw [DihedralGroup.nat_card]

private lemma ct_rm8_eight_dvd_coxeter {ι : Type} (M : CoxeterMatrix ι) [Finite M.Group]
    {a b c : ι} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hMab : M.M a b = 2) (hMac : M.M a c = 2) (hMbc : M.M b c = 2) :
    8 ∣ Nat.card M.Group := by
  let cs := M.toCoxeterSystem
  let sa : M.Group := cs.simple a
  let sb : M.Group := cs.simple b
  let sc : M.Group := cs.simple c
  have hsa2 : sa * sa = 1 := cs.simple_mul_simple_self a
  have hsb2 : sb * sb = 1 := cs.simple_mul_simple_self b
  have hsc2 : sc * sc = 1 := cs.simple_mul_simple_self c
  have hsa1 : sa ≠ 1 := cs.simple_ne_one a
  have hsb1 : sb ≠ 1 := cs.simple_ne_one b
  have hsc1 : sc ≠ 1 := cs.simple_ne_one c
  have hsab_ne : sa ≠ sb := fun h => hab (cs.simple_injective h)
  have hsac_ne : sa ≠ sc := fun h => hac (cs.simple_injective h)
  have hsbc_ne : sb ≠ sc := fun h => hbc (cs.simple_injective h)
  have horda : orderOf sa = 2 := orderOf_eq_prime (by rwa [pow_two]) hsa1
  have hordb : orderOf sb = 2 := orderOf_eq_prime (by rwa [pow_two]) hsb1
  have hordc : orderOf sc = 2 := orderOf_eq_prime (by rwa [pow_two]) hsc1
  have hsab : sa * sb = sb * sa := by
    have h := cs.simple_mul_simple_pow a b
    rw [hMab] at h
    exact ct_rm8_commute_of_sq_mul_sq h hsa2 hsb2
  have hsac : sa * sc = sc * sa := by
    have h := cs.simple_mul_simple_pow a c
    rw [hMac] at h
    exact ct_rm8_commute_of_sq_mul_sq h hsa2 hsc2
  have hsbc : sb * sc = sc * sb := by
    have h := cs.simple_mul_simple_pow b c
    rw [hMbc] at h
    exact ct_rm8_commute_of_sq_mul_sq h hsb2 hsc2
  have hb_not : sb ∉ Subgroup.zpowers sa := by
    intro h
    rcases ct_rm8_zpowers_involution_eq_one_or hsa2 h with h1 | h1
    · exact hsb1 h1
    · exact hsab_ne h1.symm
  have hcent_ab : Subgroup.zpowers sa ≤ Subgroup.centralizer (Subgroup.zpowers sb : Set M.Group) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hsab k).symm
  obtain ⟨E2, hV1E2, hV2E2, hE2elem, hE2card, hE2le⟩ :=
    commuting_disjoint_elementary_product (firstRank := 1) (secondRank := 1)
      (Subgroup.zpowers sa) (Subgroup.zpowers sb)
      (involution_zpowers_elementary sa horda) (involution_zpowers_elementary sb hordb)
      (by rw [Nat.card_zpowers, horda]; rfl) (by rw [Nat.card_zpowers, hordb]; rfl)
      hcent_ab (involution_zpowers_disjoint (Subgroup.zpowers sa) sb hordb hb_not)
  have hsup_sub : ∀ x ∈ (Subgroup.zpowers sa ⊔ Subgroup.zpowers sb : Subgroup M.Group),
      x ∈ ({1, sa, sb, sa * sb} : Set M.Group) := ct_rm8_U4_mem sa sb hsa2 hsb2 hsab
  have hc_not_sup : sc ∉ (Subgroup.zpowers sa ⊔ Subgroup.zpowers sb : Subgroup M.Group) := by
    intro h
    have h' := hsup_sub sc h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'
    rcases h' with h' | h' | h' | h'
    · exact hsc1 h'
    · exact hsac_ne h'.symm
    · exact hsbc_ne h'.symm
    · have hpar : cs.lengthParity sc = cs.lengthParity (sa * sb) := by rw [h']
      rw [map_mul] at hpar
      have hpa : cs.lengthParity sa = Multiplicative.ofAdd 1 := by
        change cs.lengthParity (cs.simple a) = Multiplicative.ofAdd 1
        exact cs.lengthParity_simple a
      have hpb : cs.lengthParity sb = Multiplicative.ofAdd 1 := by
        change cs.lengthParity (cs.simple b) = Multiplicative.ofAdd 1
        exact cs.lengthParity_simple b
      have hpc : cs.lengthParity sc = Multiplicative.ofAdd 1 := by
        change cs.lengthParity (cs.simple c) = Multiplicative.ofAdd 1
        exact cs.lengthParity_simple c
      rw [hpa, hpb, hpc] at hpar
      have hcoe := congrArg Multiplicative.toAdd hpar
      simp only [toAdd_mul, toAdd_ofAdd] at hcoe
      exact absurd hcoe (by decide)
  have hc_not_E2 : sc ∉ E2 := fun h => hc_not_sup (hE2le h)
  have hV1c : Subgroup.zpowers sa ≤ Subgroup.centralizer (Subgroup.zpowers sc : Set M.Group) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hsac k).symm
  have hV2c : Subgroup.zpowers sb ≤ Subgroup.centralizer (Subgroup.zpowers sc : Set M.Group) := by
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right hsbc k).symm
  have hcent_E2c : E2 ≤ Subgroup.centralizer (Subgroup.zpowers sc : Set M.Group) :=
    hE2le.trans (sup_le hV1c hV2c)
  obtain ⟨E3, hE2E3, hcE3, hE3elem, hE3card, -⟩ :=
    commuting_disjoint_elementary_product (firstRank := 2) (secondRank := 1)
      E2 (Subgroup.zpowers sc)
      hE2elem (involution_zpowers_elementary sc hordc) hE2card
      (by rw [Nat.card_zpowers, hordc]; rfl) hcent_E2c
      (involution_zpowers_disjoint E2 sc hordc hc_not_E2)
  have hdvd : Nat.card E3 ∣ Nat.card M.Group := Subgroup.card_subgroup_dvd_card E3
  rw [hE3card] at hdvd
  norm_num at hdvd
  exact hdvd

private lemma ct_rm8_cartanD_02 {n : ℕ} (hn : 4 ≤ n) :
    CartanMatrix.D n ⟨0, by omega⟩ ⟨n - 2, by omega⟩ = 0 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  dsimp only [Fin.val_mk, Fin.val_zero]
  rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp; omega))]
  rw [if_neg (by omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]

private lemma ct_rm8_cartanD_01 {n : ℕ} (hn : 4 ≤ n) :
    CartanMatrix.D n ⟨0, by omega⟩ ⟨n - 1, by omega⟩ = 0 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  dsimp only [Fin.val_mk, Fin.val_zero]
  rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp; omega))]
  rw [if_neg (by omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]

private lemma ct_rm8_cartanD_21 {n : ℕ} (hn : 4 ≤ n) :
    CartanMatrix.D n ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 0 := by
  rw [CartanMatrix.D, Matrix.of_apply]
  dsimp only [Fin.val_mk, Fin.val_zero]
  rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp; omega))]
  rw [if_neg (by omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]
  rw [if_neg (by rintro ⟨h1, h2⟩; omega)]

private lemma ct_rm8_D_M02 {n : ℕ} (hn : 4 ≤ n) :
    (ggCoxeterMatrixD n).M ⟨0, by omega⟩ ⟨n - 2, by omega⟩ = 2 := by
  rw [ggCoxeterMatrixD_apply]
  rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp; omega))]
  rw [if_pos (ct_rm8_cartanD_02 hn)]

private lemma ct_rm8_D_M01 {n : ℕ} (hn : 4 ≤ n) :
    (ggCoxeterMatrixD n).M ⟨0, by omega⟩ ⟨n - 1, by omega⟩ = 2 := by
  rw [ggCoxeterMatrixD_apply]
  rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp; omega))]
  rw [if_pos (ct_rm8_cartanD_01 hn)]

private lemma ct_rm8_D_M21 {n : ℕ} (hn : 4 ≤ n) :
    (ggCoxeterMatrixD n).M ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 2 := by
  rw [ggCoxeterMatrixD_apply]
  rw [if_neg (by intro h; exact absurd (congrArg Fin.val h) (by simp; omega))]
  rw [if_pos (ct_rm8_cartanD_21 hn)]

private lemma ct_rm8_A_not_dvd {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {n : ℕ} (h : GGWeylOfType p (CoxeterMatrix.A n) A)
    (hn : 3 ≤ n) : ¬ Nat.card ↥A ∣ 12 := by
  intro hdvd
  have hcard : Nat.card ↥A = (n + 1).factorial := ggWeylOfType_A_card h
  have h24 : 24 ≤ Nat.card ↥A := by
    rw [hcard]
    calc 24 = Nat.factorial 4 := by norm_num
      _ ≤ (n + 1).factorial := Nat.factorial_le (by omega)
  have hle12 : Nat.card ↥A ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem ggRM_not_G2_of_le {G : Type} [Group G] [Finite G] {p : ℕ} {Bs : Subgroup G} {ιA : Type}
    {M : CoxeterMatrix ιA} {ιL : Type} [Fintype ιL] {ML : CoxeterMatrix ιL}
    (hML : GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML) {A H : Subgroup (MulAut ↥Bs)}
    (hA : GGWeylOfType p ML A) (hle : A ≤ H) (f : M.Group ≃* ↥H) :
    ¬ ∃ e : Fin 2 ≃ ιA, M = CoxeterMatrix.G₂.reindex e := by
  rintro ⟨e2, hM⟩
  have hAkeep := hA
  obtain ⟨eML, -⟩ := hAkeep
  have hfinML : Finite ML.Group := Finite.of_equiv ↥A eML.symm.toEquiv
  have hcardH : Nat.card ↥H = 12 := by
    calc Nat.card ↥H = Nat.card M.Group :=
          (Nat.card_congr f.toEquiv).symm
      _ = Nat.card (CoxeterMatrix.G₂).Group := by
            rw [hM]
            exact Nat.card_congr ((CoxeterMatrix.G₂).reindexGroupEquiv e2).toEquiv
      _ = 12 := ct_rm8_card_G2
  have hdvdA : Nat.card ↥A ∣ 12 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [hcardH] at h
  rcases hML with (⟨n, e, hn, hMLa⟩ | ⟨n, e, hn, hMLd⟩) | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩
  ·
    have hA' : GGWeylOfType p ((CoxeterMatrix.A n).reindex e) (A) := by
      rwa [hMLa] at hA
    exact (ct_rm8_A_not_dvd (GGWeylOfType.of_reindex hA') hn) hdvdA
  ·
    have hn0 : 0 < n := by omega
    have hn2 : n - 2 < n := by omega
    have hn1 : n - 1 < n := by omega
    have h0ne2 : (⟨0, hn0⟩ : Fin n) ≠ ⟨n - 2, hn2⟩ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have h0ne1 : (⟨0, hn0⟩ : Fin n) ≠ ⟨n - 1, hn1⟩ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have h2ne1 : (⟨n - 2, hn2⟩ : Fin n) ≠ ⟨n - 1, hn1⟩ := by
      intro h; have := congrArg Fin.val h; simp at this; omega
    have hM01 : ML.M (e ⟨0, hn0⟩) (e ⟨n - 1, hn1⟩) = 2 := by
      rw [hMLd, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact ct_rm8_D_M01 hn
    have hM02 : ML.M (e ⟨0, hn0⟩) (e ⟨n - 2, hn2⟩) = 2 := by
      rw [hMLd, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact ct_rm8_D_M02 hn
    have hM21 : ML.M (e ⟨n - 2, hn2⟩) (e ⟨n - 1, hn1⟩) = 2 := by
      rw [hMLd, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact ct_rm8_D_M21 hn
    have h01 : e ⟨0, hn0⟩ ≠ e ⟨n - 1, hn1⟩ := e.injective.ne h0ne1
    have h02 : e ⟨0, hn0⟩ ≠ e ⟨n - 2, hn2⟩ := e.injective.ne h0ne2
    have h21 : e ⟨n - 2, hn2⟩ ≠ e ⟨n - 1, hn1⟩ := e.injective.ne h2ne1
    have h8 : 8 ∣ Nat.card ML.Group :=
      ct_rm8_eight_dvd_coxeter ML h02 h01 h21 hM02 hM01 hM21
    have h8' : 8 ∣ Nat.card ↥A := by
      rwa [Nat.card_congr eML.toEquiv] at h8
    exact absurd (h8'.trans hdvdA) (by norm_num)
  ·
    have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
    have h05 : e 0 ≠ e 5 := e.injective.ne (by decide)
    have h15 : e 1 ≠ e 5 := e.injective.ne (by decide)
    have hM01 : ML.M (e 0) (e 1) = 2 := by
      rw [hE6, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have hM05 : ML.M (e 0) (e 5) = 2 := by
      rw [hE6, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have hM15 : ML.M (e 1) (e 5) = 2 := by
      rw [hE6, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have h8 : 8 ∣ Nat.card ML.Group :=
      ct_rm8_eight_dvd_coxeter ML h01 h05 h15 hM01 hM05 hM15
    have h8' : 8 ∣ Nat.card ↥A := by
      rwa [Nat.card_congr eML.toEquiv] at h8
    exact absurd (h8'.trans hdvdA) (by norm_num)
  ·
    have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
    have h06 : e 0 ≠ e 6 := e.injective.ne (by decide)
    have h16 : e 1 ≠ e 6 := e.injective.ne (by decide)
    have hM01 : ML.M (e 0) (e 1) = 2 := by
      rw [hE7, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have hM06 : ML.M (e 0) (e 6) = 2 := by
      rw [hE7, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have hM16 : ML.M (e 1) (e 6) = 2 := by
      rw [hE7, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have h8 : 8 ∣ Nat.card ML.Group :=
      ct_rm8_eight_dvd_coxeter ML h01 h06 h16 hM01 hM06 hM16
    have h8' : 8 ∣ Nat.card ↥A := by
      rwa [Nat.card_congr eML.toEquiv] at h8
    exact absurd (h8'.trans hdvdA) (by norm_num)
  ·
    have h01 : e 0 ≠ e 1 := e.injective.ne (by decide)
    have h07 : e 0 ≠ e 7 := e.injective.ne (by decide)
    have h17 : e 1 ≠ e 7 := e.injective.ne (by decide)
    have hM01 : ML.M (e 0) (e 1) = 2 := by
      rw [hE8, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have hM07 : ML.M (e 0) (e 7) = 2 := by
      rw [hE8, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have hM17 : ML.M (e 1) (e 7) = 2 := by
      rw [hE8, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      decide
    have h8 : 8 ∣ Nat.card ML.Group :=
      ct_rm8_eight_dvd_coxeter ML h01 h07 h17 hM01 hM07 hM17
    have h8' : 8 ∣ Nat.card ↥A := by
      rwa [Nat.card_congr eML.toEquiv] at h8
    exact absurd (h8'.trans hdvdA) (by norm_num)

theorem ggRM_not_G2 {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {ιA : Type} {M : CoxeterMatrix ιA} {ιL : Type} [Fintype ιL] {ML : CoxeterMatrix ιL}
    (hML : GGIsWeylMatrixAD ML ∨ GGIsWeylMatrixE ML)
    (hAL : GGWeylOfType p ML (ggAutomizer L Bs)) (hle : ggAutomizer L Bs ≤ ggAInf p B Bs x L D J)
    (f : M.Group ≃* ↥(ggAInf p B Bs x L D J)) :
    ¬ ∃ e : Fin 2 ≃ ιA, M = CoxeterMatrix.G₂.reindex e :=
  ggRM_not_G2_of_le hML hAL hle f

end CFSG.StandardType

end
