module

public import CFSG.GH74.GLS.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
open scoped commutatorElement

abbrev J2 : Type := CFSG.Blueprint.NativeSporadic.J2

theorem normal_le_or_eq_top {Y : Type*} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hS : IsPGroup 2 S) (hsimple : IsSimpleGroup (Y ⧸ S))
    (hY3 : oPrimeResidual 3 Y = ⊤) (K : Subgroup Y) [K.Normal] : K ≤ S ∨ K = ⊤ := by
  classical
  haveI := hsimple
  haveI hKn : (K.map (QuotientGroup.mk' S)).Normal :=
    Subgroup.Normal.map ‹K.Normal› (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S)
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.map (QuotientGroup.mk' S)) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hKS : ∀ y : Y, ∃ k ∈ K, k⁻¹ * y ∈ S := by
      intro y
      have hy : QuotientGroup.mk' S y ∈ K.map (QuotientGroup.mk' S) := by
        rw [h]; exact Subgroup.mem_top _
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      refine ⟨k, hk, ?_⟩
      have := (QuotientGroup.eq (s := S)).mp hky
      simpa using this
    rw [eq_top_iff, ← hY3]
    refine (Subgroup.closure_le K).mpr ?_
    rintro x ⟨n, hxn⟩
    obtain ⟨k, hk, hks⟩ := hKS x
    obtain ⟨m, hm⟩ := hS ⟨k⁻¹ * x, hks⟩
    have hm' : (k⁻¹ * x) ^ (2 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have h3 : (QuotientGroup.mk' K x) ^ (3 ^ n) = 1 := by
      rw [← map_pow, hxn, map_one]
    have h2 : (QuotientGroup.mk' K x) ^ (2 ^ m) = 1 := by
      have hk1 : QuotientGroup.mk' K k⁻¹ = 1 := by
        rw [QuotientGroup.mk'_apply]
        exact (QuotientGroup.eq_one_iff _).mpr (inv_mem hk)
      have hkx : QuotientGroup.mk' K (k⁻¹ * x) = QuotientGroup.mk' K x := by
        rw [map_mul, hk1, one_mul]
      rw [← hkx, ← map_pow, hm', map_one]
    have hg : (QuotientGroup.mk' K x) ^ (Nat.gcd (2 ^ m) (3 ^ n)) = 1 := pow_gcd_eq_one.mpr ⟨h2, h3⟩
    have hcop : Nat.gcd (2 ^ m) (3 ^ n) = 1 :=
      Nat.Coprime.pow m n (by norm_num : Nat.Coprime 2 3)
    rw [hcop, pow_one] at hg
    exact (QuotientGroup.eq_one_iff x).mp hg

theorem exists_perfect_sup_eq_top {Y : Type*} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hperf : Group.IsPerfect (Y ⧸ S)) : ∃ W : Subgroup Y, Group.IsPerfect ↥W ∧ W ⊔ S = ⊤ := by
  classical
  obtain ⟨W, -, hW⟩ := exists_minimal_le_of_wellFoundedLT (fun W : Subgroup Y => W ⊔ S = ⊤)
    ⊤ (by simp)
  refine ⟨W, ?_, hW.prop⟩
  rw [Subgroup.isPerfect_iff]
  have hle : ⁅W, W⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem ha hb) (W.inv_mem ha)) (W.inv_mem hb)
  have hmapW : W.map (QuotientGroup.mk' S) = ⊤ := by
    have h1 : (W ⊔ S).map (QuotientGroup.mk' S) = ⊤ := by
      rw [hW.prop, Subgroup.map_top, QuotientGroup.range_mk']
    rw [Subgroup.map_sup] at h1
    have h2 : S.map (QuotientGroup.mk' S) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, sup_bot_eq] at h1
  have hcomm : ⁅W, W⁆ ⊔ S = ⊤ := by
    have h3 : (⁅W, W⁆).map (QuotientGroup.mk' S) = ⊤ := by
      rw [Subgroup.map_commutator, hmapW]
      have := (Group.isPerfect_def.mp hperf)
      rwa [commutator_def] at this
    have h4 := Subgroup.comap_map_eq (QuotientGroup.mk' S) ⁅W, W⁆
    rw [h3, Subgroup.comap_top, QuotientGroup.ker_mk'] at h4
    exact h4.symm
  exact le_antisymm hle (hW.2 (y := ⁅W, W⁆) hcomm hle)

theorem center_of_order_seven {Y : Type*} [Group Y] [Finite Y] (S : Subgroup Y) [S.Normal]
    (hS : IsPGroup 2 S) (hF5 : ∀ K : Subgroup Y, K.Normal → K ≤ S ∨ K = ⊤)
    (h7 : 7 ∣ Nat.card Y) (hcent : ∀ y : Y, orderOf y = 7 → ∀ s ∈ S, y * s = s * y) :
    S ≤ Subgroup.center Y := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 7 h7
  haveI hC : (Subgroup.centralizer (S : Set Y)).Normal := inferInstance
  rcases hF5 _ hC with h | h
  · exfalso
    have hyC : y ∈ Subgroup.centralizer (S : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      exact (hcent y hy s hs).symm
    have hyS : y ∈ S := h hyC
    obtain ⟨n, hn⟩ := hS ⟨y, hyS⟩
    have hyn : y ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hdvd : 7 ∣ 2 ^ n := hy ▸ orderOf_dvd_of_pow_eq_one hyn
    have h7p : Nat.Prime 7 := by norm_num
    have := (Nat.Prime.dvd_of_dvd_pow h7p hdvd)
    omega
  · intro s hs
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (S : Set Y) := by rw [h]; trivial
    exact (Subgroup.mem_centralizer_iff.mp hg s hs).symm

theorem pu_map_commutatorSubgroup {Y : Type*} [Group Y] (S : Subgroup Y) [S.Normal] (y : Y)
    (H : Subgroup ↥S) :
    (commutatorSubgroup (A := ↥(Subgroup.zpowers y)) (G := ↥S) H).map S.subtype =
      ⁅H.map S.subtype, Subgroup.zpowers y⁆ := by
  unfold commutatorSubgroup
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨x, ⟨a, h, hh, rfl⟩, rfl⟩
    refine Subgroup.subset_closure
      ⟨((h⁻¹ : ↥S) : Y), Subgroup.mem_map.mpr ⟨h⁻¹, H.inv_mem hh, rfl⟩, (a : Y), a.2, ?_⟩
    simp [commutatorElement_def, mul_assoc]
  · rw [Subgroup.closure_le]
    rintro _ ⟨g₁, hg₁, g₂, hg₂, rfl⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg₁
    refine Subgroup.subset_closure ⟨(h⁻¹)⁻¹ * ((⟨g₂, hg₂⟩ : ↥(Subgroup.zpowers y)) • h⁻¹),
      ⟨⟨g₂, hg₂⟩, h⁻¹, H.inv_mem hh, rfl⟩, ?_⟩
    simp [commutatorElement_def, mul_assoc]

theorem commutator_commutator_zpowers_eq {Y : Type*} [Group Y] [Finite Y] (S : Subgroup Y)
    [S.Normal] (hS : IsPGroup 2 S) {y : Y} (hy : orderOf y = 7) :
    ⁅⁅S, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ = ⁅S, Subgroup.zpowers y⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSsolv : Group.IsSolvable ↥S := by
    haveI := hS.isNilpotent
    infer_instance
  have hcoprime : Nat.Coprime (Nat.card ↥(Subgroup.zpowers y)) (Nat.card ↥S) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hS
    rw [Nat.card_zpowers, hy, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hsubtop : (⊤ : Subgroup ↥S).map S.subtype = S := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hA : (commutatorAction (A := ↥(Subgroup.zpowers y)) (G := ↥S)).map S.subtype =
      ⁅S, Subgroup.zpowers y⁆ := by
    have h := pu_map_commutatorSubgroup S y ⊤
    rw [hsubtop] at h
    exact h
  have hB : (commutatorAction₂ (A := ↥(Subgroup.zpowers y)) (G := ↥S)).map S.subtype =
      ⁅⁅S, Subgroup.zpowers y⁆, Subgroup.zpowers y⁆ := by
    have h := pu_map_commutatorSubgroup S y
      (commutatorAction (A := ↥(Subgroup.zpowers y)) (G := ↥S))
    rw [hA] at h
    exact h
  have hC : commutatorAction₂ (A := ↥(Subgroup.zpowers y)) (G := ↥S) =
      commutatorAction (A := ↥(Subgroup.zpowers y)) (G := ↥S) :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime hSsolv hcoprime
  rw [← hB, hC, hA]

end CFSG.RankThree.PartTwo.Sec17.PropU
