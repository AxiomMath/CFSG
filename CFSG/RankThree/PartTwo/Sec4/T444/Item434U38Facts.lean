module

public import Certificates.Certificate188001
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Chain
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Abs
public import CFSG.YGroups.Model233F.RawChain

public section

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.YGroups

namespace CFSG.RankThree.PartTwo.Sec4.Item434U38

@[expose] def U38G : Subgroup (Equiv.Perm (Fin 513)) := arrClosure 513 gensO

theorem gensO_size : gensO.size = 9 := by simp [gensO]

theorem strong1_size : strong1.size = 14 := by simp [strong1, gensO]

theorem strong2_size : strong2.size = 16 := by simp [strong2, gensO]

theorem strong1_getElem (i : ℕ) (hi : i < 9) : strong1[i]! = gensO[i]! := by
  have hi' : i < gensO.size := by rw [gensO_size]; exact hi
  rw [getElem!_pos strong1 i (by rw [strong1_size]; omega), getElem!_pos gensO i hi']
  simp only [strong1]
  rw [Array.getElem_append_left hi']

theorem strong2_getElem (i : ℕ) (hi : i < 9) : strong2[i]! = gensO[i]! := by
  have hi' : i < gensO.size := by rw [gensO_size]; exact hi
  rw [getElem!_pos strong2 i (by rw [strong2_size]; omega), getElem!_pos gensO i hi']
  simp only [strong2]
  rw [Array.getElem_append_left hi']

theorem base1L_nodup : base1L.Nodup := by decide
theorem base2L_nodup : base2L.Nodup := by decide

theorem hk1 : 9 ≤ strong1.size := by rw [strong1_size]; omega
theorem hk2 : 9 ≤ strong2.size := by rw [strong2_size]; omega

@[expose] noncomputable def Q1 : RawSchreierDatum 513 :=
  RawSchreierDatum.ofArrays 513 (by norm_num) strong1 9 hk1 base1L base1L_nodup words1

@[expose] noncomputable def Q2 : RawSchreierDatum 513 :=
  RawSchreierDatum.ofArrays 513 (by norm_num) strong2 9 hk2 base2L base2L_nodup words2

theorem Q1_group : Q1.originalSubgroup = U38G :=
  originalSubgroup_ofArrays_eq_arrClosure gensO_size (fun i hi => strong1_getElem i hi)

theorem Q2_group : Q2.originalSubgroup = U38G :=
  originalSubgroup_ofArrays_eq_arrClosure gensO_size (fun i hi => strong2_getElem i hi)

section Cert

theorem chain1_ok :
    rawChainOK 513 (strong1.extract 0 9) strong1 (base1L.map Fin.val).toArray words1 1 = true :=
  Certificates.certificate188001.1.1

theorem chain1_sizes : rawOrbitSizes 513 strong1 (base1L.map Fin.val).toArray = [513, 512, 378] :=
  Certificates.certificate188001.1.2

theorem chain2_ok :
    rawChainOK 513 (strong2.extract 0 9) strong2 (base2L.map Fin.val).toArray words2 1 = true :=
  Certificates.certificate188001.2.1

theorem Q1_arrays : ChainArrays Q1 (strong1.extract 0 9) strong1 (base1L.map Fin.val).toArray words1 :=
  chainArrays_ofArrays (chainCheckFacts chain1_ok).strong_inv

theorem Q2_arrays : ChainArrays Q2 (strong2.extract 0 9) strong2 (base2L.map Fin.val).toArray words2 :=
  chainArrays_ofArrays (chainCheckFacts chain2_ok).strong_inv

theorem Q1_valid : ValidSchreier Q1 := (validSchreier_of_chainOK Q1_arrays (by norm_num) chain1_ok).1

theorem card_U38G : Nat.card U38G = 99283968 := by
  have h := card_arrClosure_of_rawChainOK (n := 513) (by norm_num) (O := gensO) (S := strong1)
    (W := words1) (base := base1L) base1L_nodup (chunks := 1) (by norm_num) (by rw [gensO_size]; exact hk1)
    (fun i hi => strong1_getElem i (by rw [gensO_size] at hi; exact hi))
    (by rw [gensO_size]; exact chain1_ok)
  rw [chain1_sizes] at h
  exact h

end Cert

section Cert2

theorem Q1_baseCount : Q1.baseCount = 3 := by
  change base1L.length = 3
  rfl

theorem U38G_twoTransitive :
    ∀ a b a' b' : Fin 513, a ≠ b → a' ≠ b' → ∃ g ∈ U38G, g a = a' ∧ g b = b' := by
  have hsz := (validSchreier_of_chainOK Q1_arrays (by norm_num) chain1_ok).2
  have hlev : ((rawLevels 513 strong1 (base1L.map Fin.val).toArray).toList.map fun L => L.pts.size) =
      [513, 512, 378] := chain1_sizes
  have h0 : Q1.orbitSize ⟨0, by rw [Q1_baseCount]; omega⟩ = 513 := by
    rw [hsz ⟨0, by rw [Q1_baseCount]; omega⟩]
    exact levels_size_get hlev (i := 0) (by simp)
  have h1 : Q1.orbitSize ⟨1, by rw [Q1_baseCount]; omega⟩ = 512 := by
    rw [hsz ⟨1, by rw [Q1_baseCount]; omega⟩]
    exact levels_size_get hlev (i := 1) (by simp)
  rw [← Q1_group]
  exact chain_twoTransitive Q1 Q1_valid (by rw [Q1_baseCount]; omega) h0 h1

end Cert2

theorem rep_apply_eq_self {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (x : Fin n) (h : t[(x : ℕ)]! = (x : ℕ)) : g x = x :=
  Fin.ext ((ht x).symm.trans h)

section Elements

theorem mem_U38G_of_sift1 {t : Array ℕ} (hv : validA 513 t = true)
    (hs : siftA 513 (rawLevels 513 strong1 base1) base1 0 t = true) :
    permOfArr 513 t ∈ U38G := by
  rw [← Q1_group]
  exact mem_of_siftA Q1_arrays chain1_ok (rep_of_validA hv) hs

theorem mem_U38G_of_sift2 {t : Array ℕ} (hv : validA 513 t = true)
    (hs : siftA 513 (rawLevels 513 strong2 base2) base2 0 t = true) :
    permOfArr 513 t ∈ U38G := by
  rw [← Q2_group]
  exact mem_of_siftA Q2_arrays chain2_ok (rep_of_validA hv) hs

@[expose] noncomputable def X19 : Equiv.Perm (Fin 513) := permOfArr 513 x19

theorem X19_mem : X19 ∈ U38G :=
  mem_U38G_of_sift1 Certificates.certificate188001.2.2.1.1 Certificates.certificate188001.2.2.1.2.1

theorem X19_order : orderOf X19 = 19 := by
  have h := Certificates.certificate188001.2.2.1
  have h2 : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 x19 (19 ^ (1 - 1))) (idA 513) = false := by
    simpa using h.2.2.2.1
  exact orderOf_eq_of_pow_checks h.1 h.2.2.1 (m := 19) (p := 19) (e := 1) (by norm_num) (by norm_num)
    (by norm_num) h2

theorem X19_centralizer_card : Nat.card (Subgroup.centralizer ({X19} : Set (Equiv.Perm (Fin 513))) ⊓ U38G :
    Subgroup (Equiv.Perm (Fin 513))) = 57 := by
  have h := Certificates.certificate188001.2.2.1
  have hx : Rep 513 x19 X19 := rep_of_validA h.1
  have hps : ∀ q ∈ ps1, q < 513 := by
    intro q hq
    have : ps1 = [0, 167, 270] := by decide
    rw [this] at hq
    simp at hq
    omega
  obtain ⟨hgrp, hcard⟩ := centralizer_card_of_centOKP (n := 513) (by norm_num) hk1 base1L_nodup
    (W := words1) chain1_ok hx (rels := rels1) (gs := gens1) (ps := ps1) (c := cert1) (N := 57) hps
    h.2.2.2.2
  rw [hgrp] at hcard
  change Nat.card ↥(Subgroup.centralizer ({X19} : Set (Equiv.Perm (Fin 513))) ⊓ Q1.originalSubgroup) = 57
    at hcard
  rw [Q1_group] at hcard
  exact hcard

end Elements

section Elements2

@[expose] noncomputable def Sigma0 : Equiv.Perm (Fin 513) := permOfArr 513 sigma0

theorem Sigma0_mem : Sigma0 ∈ U38G :=
  mem_U38G_of_sift2 Certificates.certificate188001.2.2.2.1.1 Certificates.certificate188001.2.2.2.1.2.1

theorem Sigma0_sq : Sigma0 ^ 2 = 1 :=
  (eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr (rep_of_validA Certificates.certificate188001.2.2.2.1.1) 2) rep_idA).1
    Certificates.certificate188001.2.2.2.1.2.2.1

theorem Sigma0_ne_one : Sigma0 ≠ 1 := by
  intro h
  have hrep : Rep 513 sigma0 Sigma0 := rep_of_validA Certificates.certificate188001.2.2.2.1.1
  have h1 : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 sigma0 1) (idA 513) = true := by
    rw [eqA_iff (CFSG.Monster.B.Mathieu.rep_powArr hrep 1) rep_idA, h]
    simp
  rw [Certificates.certificate188001.2.2.2.1.2.2.2.1] at h1
  exact absurd h1 (by simp)

theorem Sigma0_fix0 : Sigma0 (84 : Fin 513) = (84 : Fin 513) := by
  have hrep : Rep 513 sigma0 Sigma0 := rep_of_validA Certificates.certificate188001.2.2.2.1.1
  have h := Certificates.certificate188001.2.2.2.1.2.2.2.2.1
  have hb : base2[0]! = ((84 : Fin 513) : ℕ) := by decide
  rw [hb] at h
  exact rep_apply_eq_self hrep 84 h

theorem Sigma0_fix1 : Sigma0 (154 : Fin 513) = (154 : Fin 513) := by
  have hrep : Rep 513 sigma0 Sigma0 := rep_of_validA Certificates.certificate188001.2.2.2.1.1
  have h := Certificates.certificate188001.2.2.2.1.2.2.2.2.2.1
  have hb : base2[1]! = ((154 : Fin 513) : ℕ) := by decide
  rw [hb] at h
  exact rep_apply_eq_self hrep 154 h

theorem Sigma0_centralizer :
    Nat.card (Subgroup.centralizer ({Sigma0} : Set (Equiv.Perm (Fin 513))) ⊓ U38G :
      Subgroup (Equiv.Perm (Fin 513))) = 3024 ∧
    ∃ y ∈ (Subgroup.centralizer ({Sigma0} : Set (Equiv.Perm (Fin 513))) ⊓ U38G :
      Subgroup (Equiv.Perm (Fin 513))), orderOf y = 9 := by
  have h := Certificates.certificate188001.2.2.2.1
  have hx : Rep 513 sigma0 Sigma0 := rep_of_validA h.1
  have hps : ∀ q ∈ ps2, q < 513 := by
    intro q hq
    have : ps2 = [84, 154, 190, 0, 192] := by decide
    rw [this] at hq
    simp at hq
    omega
  have hcent : centOKP 2 513 strong2 base2 sigma0 rels2 gens2 ps2 cert2 3024 = true :=
    h.2.2.2.2.2.2.2.1
  obtain ⟨hgrp, hcard⟩ := centralizer_card_of_centOKP (n := 513) (by norm_num) hk2 base2L_nodup
    (W := words2) chain2_ok hx (rels := rels2) (gs := gens2) (ps := ps2) (c := cert2) (N := 3024) hps
    hcent
  rw [hgrp] at hcard
  change Nat.card ↥(Subgroup.centralizer ({Sigma0} : Set (Equiv.Perm (Fin 513))) ⊓ Q2.originalSubgroup) = 3024
    at hcard
  rw [Q2_group] at hcard
  refine ⟨hcard, permOfArr 513 gens2[0]!, ?_, ?_⟩
  · have hmem : permOfArr 513 gens2[0]! ∈ Subgroup.closure (permsA 513 gens2) :=
      Subgroup.subset_closure ⟨0, by simp [gens2], rfl⟩
    rw [hgrp] at hmem
    change permOfArr 513 gens2[0]! ∈ Subgroup.centralizer ({Sigma0} : Set (Equiv.Perm (Fin 513))) ⊓
      Q2.originalSubgroup at hmem
    rwa [Q2_group] at hmem
  · have hv : validA 513 gens2[0]! = true := enumOK_gens_valid (centOKP_enum hcent) (by simp [gens2])
    have h9 : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 gens2[0]! 9) (idA 513) = true := h.2.2.2.2.2.2.2.2.1
    have h3 : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 gens2[0]! (3 ^ (2 - 1))) (idA 513) = false := by
      simpa using h.2.2.2.2.2.2.2.2.2
    exact orderOf_eq_of_pow_checks hv h9 (m := 9) (p := 3) (e := 2) Nat.prime_three (by norm_num)
      (by norm_num) h3

end Elements2

section Elements3

@[expose] noncomputable def Y9 : Equiv.Perm (Fin 513) := permOfArr 513 y9

theorem Y9_mem : Y9 ∈ U38G :=
  mem_U38G_of_sift1 Certificates.certificate188001.2.2.2.2.1.1 Certificates.certificate188001.2.2.2.2.1.2.1

theorem Y9_order : orderOf Y9 = 9 := by
  have h := Certificates.certificate188001.2.2.2.2.1
  have h3 : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 y9 (3 ^ (2 - 1))) (idA 513) = false := by
    simpa using h.2.2.2.1
  exact orderOf_eq_of_pow_checks h.1 h.2.2.1 (m := 9) (p := 3) (e := 2) Nat.prime_three (by norm_num)
    (by norm_num) h3

theorem Y9_fix : Y9 (0 : Fin 513) = (0 : Fin 513) := by
  have hrep : Rep 513 y9 Y9 := rep_of_validA Certificates.certificate188001.2.2.2.2.1.1
  have h := Certificates.certificate188001.2.2.2.2.1.2.2.2.2
  have hb : base1[0]! = ((0 : Fin 513) : ℕ) := by decide
  rw [hb] at h
  exact rep_apply_eq_self hrep 0 h

@[expose] noncomputable def X7 : Equiv.Perm (Fin 513) := permOfArr 513 x7

theorem X7_mem : X7 ∈ U38G :=
  mem_U38G_of_sift1 Certificates.certificate188001.2.2.2.2.2.1 Certificates.certificate188001.2.2.2.2.2.2.1

theorem X7_order : orderOf X7 = 7 := by
  have h := Certificates.certificate188001.2.2.2.2.2
  have h2 : eqA 513 (CFSG.Monster.B.Mathieu.powArr 513 x7 (7 ^ (1 - 1))) (idA 513) = false := by
    simpa using h.2.2.2.1
  exact orderOf_eq_of_pow_checks h.1 h.2.2.1 (m := 7) (p := 7) (e := 1) (by norm_num) (by norm_num)
    (by norm_num) h2

theorem X7_fixed : Nat.card {p : Fin 513 // X7 p = p} = 2 := by
  have hrep : Rep 513 x7 X7 := rep_of_validA Certificates.certificate188001.2.2.2.2.2.1
  rw [card_fixedPoints_of_rep hrep]
  have hF := Certificates.certificate188001.2.2.2.2.2
  exact hF.2.2.2.2

end Elements3

theorem card_centralizer_subtype {G : Type*} [Group G] (K : Subgroup G) (g : K) :
    Nat.card (Subgroup.centralizer ({g} : Set K)) =
      Nat.card (Subgroup.centralizer ({(g : G)} : Set G) ⊓ K : Subgroup G) := by
  refine Nat.card_congr
    { toFun := fun c => ⟨(c.1 : G), Subgroup.mem_inf.2 ⟨?_, c.1.2⟩⟩
      invFun := fun d => ⟨⟨d.1, (Subgroup.mem_inf.1 d.2).2⟩, ?_⟩
      left_inv := fun c => rfl
      right_inv := fun d => rfl }
  · have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h
  · have h := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 d.2).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext h

theorem mem_centralizer_subtype {G : Type*} [Group G] (K : Subgroup G) (g c : K) :
    c ∈ Subgroup.centralizer ({g} : Set K) ↔
      (c : G) ∈ Subgroup.centralizer ({(g : G)} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

theorem U38G_smul_fix {g : Equiv.Perm (Fin 513)} (hg : g ∈ U38G) {a : Fin 513} (h : g a = a) :
    (⟨g, hg⟩ : U38G) • a = a := h

theorem U38G_card_smul_fix {g : Equiv.Perm (Fin 513)} (hg : g ∈ U38G) {m : ℕ}
    (h : Nat.card {p : Fin 513 // g p = p} = m) :
    Nat.card {p : Fin 513 // (⟨g, hg⟩ : U38G) • p = p} = m := h

section Transfer

theorem u38_K0_perm : ∀ E Y : Subgroup U38G, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 →
    ¬ 3 ∣ Nat.card Y → E ≤ Subgroup.normalizer (Y : Set U38G) → Y = ⊥ := by
  have h2 : ∀ a b a' b' : Fin 513, a ≠ b → a' ≠ b' →
      ∃ g : U38G, g • a = a' ∧ g • b = b' := by
    intro a b a' b' hab hab'
    obtain ⟨g, hg, h1, h2⟩ := U38G_twoTransitive a b a' b' hab hab'
    exact ⟨⟨g, hg⟩, h1, h2⟩
  obtain ⟨y, hy, hyo⟩ := Sigma0_centralizer.2
  have hyU : y ∈ U38G := (Subgroup.mem_inf.1 hy).2
  have hyC : (⟨y, hyU⟩ : U38G) ∈ Subgroup.centralizer ({⟨Sigma0, Sigma0_mem⟩} : Set U38G) :=
    (mem_centralizer_subtype U38G ⟨Sigma0, Sigma0_mem⟩ ⟨y, hyU⟩).2 (Subgroup.mem_inf.1 hy).1
  refine k0_abstract (Ω := Fin 513) (H := U38G) (by simp) card_U38G h2
    (ω0 := (0 : Fin 513)) (y9 := ⟨Y9, Y9_mem⟩) ?_ ?_ (x7 := ⟨X7, X7_mem⟩) ?_ ?_
    (ω1 := (84 : Fin 513)) (ω2 := (154 : Fin 513)) (by decide) (σ := ⟨Sigma0, Sigma0_mem⟩)
    ?_ ?_ ?_ ?_ ?_
    (y' := ⟨y, hyU⟩) hyC ?_ (x19 := ⟨X19, X19_mem⟩) ?_ ?_
  · exact (Subgroup.orderOf_coe (⟨Y9, Y9_mem⟩ : U38G)).symm.trans Y9_order
  · exact U38G_smul_fix Y9_mem Y9_fix
  · exact (Subgroup.orderOf_coe (⟨X7, X7_mem⟩ : U38G)).symm.trans X7_order
  · exact U38G_card_smul_fix X7_mem X7_fixed
  · exact Subtype.ext (by simpa using Sigma0_sq)
  · intro h
    exact Sigma0_ne_one (congrArg Subtype.val h)
  · exact U38G_smul_fix Sigma0_mem Sigma0_fix0
  · exact U38G_smul_fix Sigma0_mem Sigma0_fix1
  · exact (card_centralizer_subtype U38G ⟨Sigma0, Sigma0_mem⟩).trans Sigma0_centralizer.1
  · exact (Subgroup.orderOf_coe (⟨y, hyU⟩ : U38G)).symm.trans hyo
  · exact (Subgroup.orderOf_coe (⟨X19, X19_mem⟩ : U38G)).symm.trans X19_order
  · exact ((card_centralizer_subtype U38G ⟨X19, X19_mem⟩).trans X19_centralizer_card).le

end Transfer

end CFSG.RankThree.PartTwo.Sec4.Item434U38
