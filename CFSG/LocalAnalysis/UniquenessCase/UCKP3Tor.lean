module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP3Defs
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3
public import Certificates.Data.HuppertU38Fix.Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Item434U38 U38Sylow U38Fix

section Group

theorem toral_orderOf_conj {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have := (MulAut.conj g).orderOf_eq x
  simpa [MulAut.conj_apply] using this

theorem toral_not_mem_zpowers {G : Type*} [Group G] {e f : G} (he : orderOf e = 3)
    (h1 : f ≠ 1) (h2 : f ≠ e) (h3 : f ≠ e * e) : f ∉ Subgroup.zpowers e := by
  intro hmem
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hk : e ^ k = e ^ (k % 3) := by
    have := zpow_mod_orderOf e k
    rw [he] at this
    simpa using this.symm
  have hcase : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hcase with h | h | h
  · apply h1
    rw [hk, h]
    simp
  · apply h2
    rw [hk, h]
    simp
  · apply h3
    rw [hk, h]
    simp [pow_two]

theorem yCoverPlus_of_sylow_cover {G : Type} [Group G] [Finite G] (P : Sylow 3 G) {e0 f0 g0 : G}
    (he : orderOf e0 = 3) (hf : orderOf f0 = 3) (hef : e0 * f0 = f0 * e0)
    (hfe : f0 ∉ Subgroup.zpowers e0) (hge : g0 * e0 = e0 * g0) (hgf : g0 * f0 = f0⁻¹ * g0)
    (hcov : ∀ z ∈ P, orderOf z = 3 → ∃ u : G, ∃ a b : ℕ, u * z * u⁻¹ = e0 ^ a * f0 ^ b) :
    YCoverPlus G := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro t ht
  have hzp : IsPGroup 3 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq G P Q
  have htQ : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t)
  rw [← hg₁, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at htQ
  have hz : g₁⁻¹ * t * g₁ ∈ P := by
    have e : (MulAut.conj g₁)⁻¹ • t = g₁⁻¹ * t * g₁ := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
    rwa [e] at htQ
  have hzo : orderOf (g₁⁻¹ * t * g₁) = 3 := by
    have := toral_orderOf_conj g₁⁻¹ t
    rwa [inv_inv, ht] at this
  obtain ⟨u, a, b, hu⟩ := hcov _ hz hzo
  set v : G := g₁ * u⁻¹ with hv
  have hvt : v⁻¹ * t * v = e0 ^ a * f0 ^ b := by
    rw [← hu, hv]
    group
  have htv : t = v * (e0 ^ a * f0 ^ b) * v⁻¹ := by
    rw [← hvt]
    group
  let φ : G ≃* G := MulAut.conj v
  have hφ : ∀ x, φ x = v * x * v⁻¹ := fun x => MulAut.conj_apply v x
  refine ⟨φ e0, φ f0, φ g0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact he
  · rw [MulEquiv.orderOf_eq]
    exact hf
  · rw [← map_mul, ← map_mul, hef]
  · intro hmem
    apply hfe
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨k, φ.injective ?_⟩
    rw [map_zpow]
    exact hk
  · have : t = φ e0 ^ a * φ f0 ^ b := by
      rw [← map_pow, ← map_pow, ← map_mul, hφ, ← htv]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  · rw [← map_mul, ← map_mul, hge]
  · rw [← map_mul, ← map_inv, ← map_mul, hgf]

end Group

section Enum


theorem toral_exists_sylow {pts : Array (Array ℕ)} {Q : Subgroup (Equiv.Perm (Fin 513))}
    {nIdx : List ℕ}
    (hval : ∀ i < pts.size, validA 513 pts[i]! = true)
    (hmem : ∀ x, x ∈ Q ↔ ∃ i < pts.size, permOfArr 513 pts[i]! = x)
    (hQ : Nat.card Q = 729) (hsz : pts.size = 729)
    (hnIdx : ∀ i ∈ nIdx, i < pts.size ∧
      siftA 513 (rawLevels 513 strong3 base3) base3 0 pts[i]! = true)
    (hnd : nIdx.Nodup) (hlen : nIdx.length = 81) :
    ∃ P : Sylow 3 ↥X', ∀ x : ↥X', x ∈ P ↔
      ∃ i ∈ nIdx, permOfArr 513 pts[i]! = (x : Equiv.Perm (Fin 513)) := by
  classical
  let pt : ℕ → Equiv.Perm (Fin 513) := fun i => permOfArr 513 pts[i]!
  have hF : Function.Surjective
      (fun i : Fin pts.size => (⟨pt i, (hmem _).2 ⟨i, i.2, rfl⟩⟩ : Q)) := by
    rintro ⟨x, hx⟩
    obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
    exact ⟨⟨i, hi⟩, rfl⟩
  have hFb := hF.bijective_of_nat_card_le
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin, hQ, hsz])
  have hinj : ∀ i < pts.size, ∀ j < pts.size, pt i = pt j → i = j := by
    intro i hi j hj h
    exact congrArg Fin.val (hFb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h))
  let T : Finset (Equiv.Perm (Fin 513)) := nIdx.toFinset.image pt
  have hT : T.card = 81 := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnd, hlen]
    intro i hi j hj h
    exact hinj i (hnIdx i (by simpa using hi)).1 j (hnIdx j (by simpa using hj)).1 h
  have hTS : ∀ t ∈ T, t ∈ Q ∧ t ∈ X' := by
    intro t ht
    simp only [T, Finset.mem_image, List.mem_toFinset] at ht
    obtain ⟨i, hi, rfl⟩ := ht
    obtain ⟨hlt, hsift⟩ := hnIdx i hi
    exact ⟨(hmem _).2 ⟨i, hlt, rfl⟩, sift3_mem (rep_of_validA (hval i hlt)) hsift⟩
  set S : Subgroup (Equiv.Perm (Fin 513)) := Q ⊓ X' with hS
  have hSle : Nat.card S ≤ 81 := by
    have h1 : Nat.card S ∣ 729 := hQ ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card S ∣ 5515776 := card_X' ▸ Subgroup.card_dvd_of_le inf_le_right
    have h3 : Nat.card S ∣ Nat.gcd 729 5515776 := Nat.dvd_gcd h1 h2
    rw [show Nat.gcd 729 5515776 = 81 by norm_num] at h3
    exact Nat.le_of_dvd (by norm_num) h3
  let Sfin : Finset (Equiv.Perm (Fin 513)) := Finset.univ.filter (· ∈ S)
  have hSfin : Sfin.card = Nat.card S := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : T ⊆ Sfin := fun t ht => by
    simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(hTS t ht).1, (hTS t ht).2⟩
  have hS81 : Nat.card S = 81 := by
    have := Finset.card_le_card hsub
    omega
  have hTall : ∀ s ∈ S, s ∈ T := by
    have heq : T = Sfin := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro s hs
    rw [heq]
    simpa [Sfin] using hs
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSX : S ≤ X' := inf_le_right
  let P0 : Subgroup ↥X' := S.subgroupOf X'
  have hP0 : Nat.card P0 = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hS81]
    norm_num
  have hindex : ¬ 3 ∣ P0.index := by
    have h1 := Subgroup.card_mul_index P0
    rw [hP0, card_X'] at h1
    have h2 : P0.index = 68096 := by omega
    rw [h2]
    decide
  refine ⟨(IsPGroup.of_card hP0).toSylow hindex, fun x => ?_⟩
  rw [IsPGroup.mem_toSylow]
  change (x : Equiv.Perm (Fin 513)) ∈ S ↔ _
  constructor
  · intro hx
    have := hTall _ hx
    simp only [T, Finset.mem_image, List.mem_toFinset] at this
    obtain ⟨i, hi, hix⟩ := this
    exact ⟨i, hi, hix⟩
  · rintro ⟨i, hi, hix⟩
    have : (x : Equiv.Perm (Fin 513)) ∈ T := by
      simp only [T, Finset.mem_image, List.mem_toFinset]
      exact ⟨i, hi, hix⟩
    exact ⟨(hTS _ this).1, (hTS _ this).2⟩

end Enum

section Arrays

theorem toral_pow_three_of_cubeOne {x : Array ℕ} {X : Equiv.Perm (Fin 513)} (hx : Rep 513 x X)
    (hc : cubeOne x = true) : X ^ 3 = 1 := by
  rw [pow_three]
  exact (eqA_iff (rep_compA hx (rep_compA hx hx)) rep_idA).1 hc

theorem toral_cubeOne_of_pow_three {x : Array ℕ} {X : Equiv.Perm (Fin 513)} (hx : Rep 513 x X)
    (h : X ^ 3 = 1) : cubeOne x = true :=
  (eqA_iff (rep_compA hx (rep_compA hx hx)) rep_idA).2 ((pow_three X).symm.trans h)

theorem toral_isIdA_iff {x : Array ℕ} {X : Equiv.Perm (Fin 513)} (hx : Rep 513 x X) :
    isIdA x = true ↔ X = 1 :=
  eqA_iff hx rep_idA

theorem toral_rep_pw3 {x : Array ℕ} {X : Equiv.Perm (Fin 513)} (hx : Rep 513 x X) {a : ℕ}
    (ha : a < 3) : Rep 513 (pw3 x a) (X ^ a) := by
  interval_cases a
  · rw [pow_zero]
    exact rep_idA
  · rw [pow_one]
    exact hx
  · rw [pow_two]
    exact rep_compA hx hx

theorem toral_rep_e0List {X Y : Equiv.Perm (Fin 513)} (hx : Rep 513 eBar X) (hy : Rep 513 fBar Y)
    {w : Array ℕ} (hw : w ∈ e0List ()) : ∃ a b : ℕ, Rep 513 w (X ^ a * Y ^ b) := by
  simp only [e0List, List.mem_flatMap, List.mem_map, List.mem_range] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  exact ⟨a, b, rep_compA (toral_rep_pw3 hx ha) (toral_rep_pw3 hy hb)⟩

theorem toral_cover_spec {Pl hl E0 : List (Array ℕ)} (h : coverAll (uTab Pl E0 hl) Pl = true)
    {z : Array ℕ} (hz : z ∈ Pl) (hc : cubeOne z = true) (hid : isIdA z = false) :
    ∃ h ∈ hl, ∃ y ∈ Pl, ∃ w ∈ E0,
      eqA 513 (compA 513 (compA 513 h y) z) (compA 513 w (compA 513 h y)) = true := by
  unfold coverAll at h
  have h0 := List.all_eq_true.1 h z hz
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h0
  have h1 : coverOne (uTab Pl E0 hl) z = true := by
    rcases h0 with (h1 | h1) | h1
    · rw [hc] at h1
      exact absurd h1 (by simp)
    · rw [hid] at h1
      exact absurd h1 (by simp)
    · exact h1
  unfold coverOne at h1
  obtain ⟨p, hp, h2⟩ := List.any_eq_true.1 h1
  obtain ⟨wu, hwu, h3⟩ := List.any_eq_true.1 h2
  simp only [uTab, List.mem_map, List.mem_flatMap] at hp
  obtain ⟨u, ⟨hh, hhl, y, hy, rfl⟩, rfl⟩ := hp
  simp only [List.mem_map] at hwu
  obtain ⟨w, hw, rfl⟩ := hwu
  dsimp only at h3
  exact ⟨hh, hhl, y, hy, w, hw, h3⟩

theorem toral_orderOf_three {x : Array ℕ} {X : Equiv.Perm (Fin 513)} (hx : Rep 513 x X)
    (hX : X ∈ X') (hc : cubeOne x = true) (hid : isIdA x = false) :
    orderOf (⟨X, hX⟩ : ↥X') = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    exact toral_pow_three_of_cubeOne hx hc
  · intro h1
    have h2 : isIdA x = true := (toral_isIdA_iff hx).2 (congrArg Subtype.val h1)
    rw [hid] at h2
    exact Bool.false_ne_true h2

end Arrays

section Main


theorem yCoverPlus_of_toralCheck (h : U38Fix.toralCheck () = true) :
    YCoverPlus (↥CFSG.RankThree.PartTwo.Sec4.Item434U38.X') := by
  classical
  simp only [U38Fix.toralCheck, commAt, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    and_assoc] at h
  obtain ⟨henum, hsize, hN, hvE, hvF, hvG, hvT, hsE, hsF, hsG, hsT, hcE, hcF, hidE, hidF, hFE,
    hFE2, hcEF, hcGE, hGF, hcov⟩ := h
  have hps : ∀ p ∈ keyPts, p < 513 := by
    intro p hp
    simp [keyPts, base1, base1L] at hp
    omega
  generalize qCert () = c at henum hsize hN hcov
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps henum
  have hQ : Nat.card (Subgroup.closure (permsA 513 qGens)) = 729 := by rw [hcard, hsize]
  have hnIdx : ∀ i ∈ inX c.pts (rawLevels 513 strong3 base3), i < c.pts.size ∧
      siftA 513 (rawLevels 513 strong3 base3) base3 0 c.pts[i]! = true := by
    intro i hi
    simp only [inX, List.mem_filter, List.mem_range] at hi
    exact ⟨hi.1, hi.2⟩
  have hnd : (inX c.pts (rawLevels 513 strong3 base3)).Nodup := (List.nodup_range).filter _
  obtain ⟨P, hP⟩ := toral_exists_sylow hval hmem hQ hsize hnIdx hnd hN
  have hrE := rep_of_validA hvE
  have hrF := rep_of_validA hvF
  have hrG := rep_of_validA hvG
  let e0 : ↥X' := ⟨permOfArr 513 eBar, sift3_mem hrE hsE⟩
  let f0 : ↥X' := ⟨permOfArr 513 fBar, sift3_mem hrF hsF⟩
  let g0 : ↥X' := ⟨permOfArr 513 gRefl, sift3_mem hrG hsG⟩
  have he0 : orderOf e0 = 3 := toral_orderOf_three hrE _ hcE hidE
  have hf0 : orderOf f0 = 3 := toral_orderOf_three hrF _ hcF hidF
  have hef : e0 * f0 = f0 * e0 :=
    Subtype.ext ((eqA_iff (rep_compA hrE hrF) (rep_compA hrF hrE)).1 hcEF)
  have hfe : f0 ∉ Subgroup.zpowers e0 := by
    refine toral_not_mem_zpowers he0 ?_ ?_ ?_
    · intro h1
      have h2 := (toral_isIdA_iff hrF).2 (congrArg Subtype.val h1)
      rw [hidF] at h2
      exact Bool.false_ne_true h2
    · intro h1
      have h2 := (eqA_iff hrF hrE).2 (congrArg Subtype.val h1)
      rw [hFE] at h2
      exact Bool.false_ne_true h2
    · intro h1
      have h2 := (eqA_iff hrF (rep_compA hrE hrE)).2 (congrArg Subtype.val h1)
      rw [hFE2] at h2
      exact Bool.false_ne_true h2
  have hge : g0 * e0 = e0 * g0 :=
    Subtype.ext ((eqA_iff (rep_compA hrG hrE) (rep_compA hrE hrG)).1 hcGE)
  have hgf : g0 * f0 = f0⁻¹ * g0 := by
    have hf3 : f0 * (f0 * f0) = 1 :=
      Subtype.ext ((eqA_iff (rep_compA hrF (rep_compA hrF hrF)) rep_idA).1 hcF)
    rw [inv_eq_of_mul_eq_one_right hf3]
    exact Subtype.ext ((eqA_iff (rep_compA hrG hrF) (rep_compA (rep_compA hrF hrF) hrG)).1 hGF)
  refine yCoverPlus_of_sylow_cover P he0 hf0 hef hfe hge hgf ?_
  intro z hzP hzo
  obtain ⟨i, hi, hiz⟩ := (hP z).1 hzP
  have hlt : i < c.pts.size := (hnIdx i hi).1
  have hrz : Rep 513 c.pts[i]! (z : Equiv.Perm (Fin 513)) := by
    rw [← hiz]
    exact rep_of_validA (hval i hlt)
  have hz3 : (z : Equiv.Perm (Fin 513)) ^ 3 = 1 := by
    have : z ^ 3 = 1 := by
      rw [← hzo]
      exact pow_orderOf_eq_one z
    exact congrArg Subtype.val this
  have hcz : cubeOne c.pts[i]! = true := toral_cubeOne_of_pow_three hrz hz3
  have hidz : isIdA c.pts[i]! = false := by
    by_contra hne
    have h1 : isIdA c.pts[i]! = true := by simpa using hne
    have h2 : z = 1 := Subtype.ext ((toral_isIdA_iff hrz).1 h1)
    rw [h2, orderOf_one] at hzo
    omega
  have hzl : c.pts[i]! ∈ (inX c.pts (rawLevels 513 strong3 base3)).map fun i => c.pts[i]! :=
    List.mem_map.2 ⟨i, hi, rfl⟩
  obtain ⟨hh, hhl, y, hy, w, hw, heq⟩ := toral_cover_spec hcov hzl hcz hidz
  obtain ⟨H, hH⟩ : ∃ H : ↥X', Rep 513 hh (H : Equiv.Perm (Fin 513)) := by
    rcases List.mem_cons.1 hhl with hhe | hmemT
    · refine ⟨1, ?_⟩
      rw [hhe]
      exact rep_idA
    · obtain ⟨k, hk, hkk⟩ := List.getElem_of_mem hmemT
      have hk' : k < tHs.size := by simpa using hk
      have hhk : hh = tHs[k]! := by
        rw [← hkk, Array.getElem_toList]
        exact (getElem!_pos tHs k hk').symm
      have hvk := allLt_spec hvT hk'
      have hsk := allLt_spec hsT hk'
      refine ⟨⟨permOfArr 513 tHs[k]!, sift3_mem (rep_of_validA hvk) hsk⟩, ?_⟩
      rw [hhk]
      exact rep_of_validA hvk
  obtain ⟨Y, hY⟩ : ∃ Y : ↥X', Rep 513 y (Y : Equiv.Perm (Fin 513)) := by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    obtain ⟨hjlt, hjs⟩ := hnIdx j hj
    exact ⟨⟨permOfArr 513 c.pts[j]!, sift3_mem (rep_of_validA (hval j hjlt)) hjs⟩,
      rep_of_validA (hval j hjlt)⟩
  obtain ⟨a, b, hwr⟩ := toral_rep_e0List hrE hrF hw
  have hmain := (eqA_iff (rep_compA (rep_compA hH hY) hrz)
    (rep_compA hwr (rep_compA hH hY))).1 heq
  refine ⟨H * Y, a, b, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  exact Subtype.ext hmain

theorem exists_orderOf_three_of_toralCheck (h : U38Fix.toralCheck () = true) :
    ∃ t : ↥CFSG.RankThree.PartTwo.Sec4.Item434U38.X', orderOf t = 3 := by
  simp only [U38Fix.toralCheck, commAt, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    and_assoc] at h
  obtain ⟨-, -, -, hvE, -, -, -, hsE, -, -, -, hcE, -, hidE, -⟩ := h
  exact ⟨_, toral_orderOf_three (rep_of_validA hvE) (sift3_mem (rep_of_validA hvE) hsE) hcE hidE⟩

end Main

end CFSG.LocalAnalysis.UniquenessCase.UCK
