module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps

public section

open scoped commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

section Thompson

variable {Y : Type*} [Group Y]

theorem b7c_normal_of_cos {P T : Subgroup Y} {u : Y} (hTP : T ≤ P) (huT : u ∉ T)
    (hcos : ∀ t ∈ P, t ∈ T ∨ u⁻¹ * t ∈ T) : ∀ t ∈ P, ∀ q ∈ T, t * q * t⁻¹ ∈ T := by
  intro t ht q hq
  rcases hcos t ht with h | h
  · exact T.mul_mem (T.mul_mem h hq) (T.inv_mem h)
  ·
    have hsq : (u⁻¹ * t) * q * (u⁻¹ * t)⁻¹ ∈ T :=
      T.mul_mem (T.mul_mem h hq) (T.inv_mem h)
    have hyP : t * q * t⁻¹ ∈ P := P.mul_mem (P.mul_mem ht (hTP hq)) (P.inv_mem ht)
    rcases hcos _ hyP with h1 | h2
    · exact h1
    · exfalso
      apply huT
      have h3 : ((u⁻¹ * t) * q * (u⁻¹ * t)⁻¹) * u⁻¹ ∈ T := by
        have e : u⁻¹ * (t * q * t⁻¹) = ((u⁻¹ * t) * q * (u⁻¹ * t)⁻¹) * u⁻¹ := by group
        rwa [e] at h2
      have h4 : u⁻¹ ∈ T := by
        simpa only [inv_mul_cancel_left] using T.mul_mem (T.inv_mem hsq) h3
      simpa only [inv_inv] using T.inv_mem h4

theorem b7c_inv_mul_mem {T U : Subgroup Y} (hUidx : U.relIndex T = 2) {a b : Y}
    (haT : a ∈ T) (hbT : b ∈ T) (haU : a ∉ U) (hbU : b ∉ U) : a⁻¹ * b ∈ U := by
  have key := (Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf T) hUidx
    (a := (⟨a, haT⟩ : T)⁻¹) (b := ⟨b, hbT⟩)).2 (by
      rw [inv_mem_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact iff_of_false haU hbU)
  exact Subgroup.mem_subgroupOf.1 key

theorem b7c_dich [Finite Y] {S L : Subgroup Y} {j : Y} (hjS : j ∈ S) (hjL : j ∉ L)
    (hidx : L.relIndex S ≤ 2) {s : Y} (hs : s ∈ S) : s ∈ L ∨ j⁻¹ * s ∈ L := by
  by_cases h : s ∈ L
  · exact Or.inl h
  · refine Or.inr (b7c_inv_mul_mem ?_ hjS hs hjL h)
    have h1 : L.relIndex S ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun hle => hjL (hle hjS)
    have h0 : (L.subgroupOf S).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h0' : L.relIndex S ≠ 0 := h0
    omega

theorem b7c_thompson [Finite Y] {P T : Subgroup Y} {u : Y} (hP : IsPGroup 2 P)
    (hPidx : ¬ 2 ∣ P.index) (hTP : T ≤ P) (hcos : ∀ t ∈ P, t ∈ T ∨ u⁻¹ * t ∈ T)
    (huP : u ∈ P) (huT : u ∉ T) (hu2 : u * u = 1) :
    (∃ (N : Subgroup Y) (_ : N.Normal), IsCyclic (Y ⧸ N) ∧ u ∉ N) ∨
      ∃ g : Y, g⁻¹ * u * g ∈ T := by
  have hTn := b7c_normal_of_cos hTP huT hcos
  have hcyc : ∃ b ∈ P, ∀ t ∈ P, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ T := by
    refine ⟨u, huP, fun t ht => ?_⟩
    rcases hcos t ht with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  have hb : ∀ (g : Y) (k : ℕ), g⁻¹ * u ^ (2 * k) * g ∈ P → g⁻¹ * u ^ (2 * k) * g ∈ T := by
    intro g k _
    have h1 : u ^ (2 * k) = 1 := by rw [pow_mul, pow_two, hu2, one_pow]
    rw [h1]
    simp
  have hc : ∀ g : Y, g⁻¹ * u * g ∈ P →
      CFSG.GH74.GLS.Bg.Thompson.IsExtremalIn 2 P (g⁻¹ * u * g) →
        g⁻¹ * u * g ∈ T ∨ u⁻¹ * (g⁻¹ * u * g) ∈ T :=
    fun g hg _ => hcos _ hg
  rcases CFSG.GH74.GLS.Bg.Thompson.thompson_transfer_1515 (p := 2) hP hPidx hTn hcyc huP huT
      hb hc with ⟨N, hN, hcycN, -, huN⟩ | ⟨g, hg, -⟩
  · exact Or.inl ⟨N, hN, hcycN, huN⟩
  · exact Or.inr ⟨g, hg⟩

theorem b7c_eq_top_of_cyclic [Group.IsPerfect Y] (N : Subgroup Y) [N.Normal]
    [IsCyclic (Y ⧸ N)] : N = ⊤ := by
  have hcomm : ∀ a b : Y, ⁅a, b⁆ ∈ N := by
    intro a b
    have h1 : ((⁅a, b⁆ : Y) : Y ⧸ N) = ⁅(a : Y ⧸ N), (b : Y ⧸ N)⁆ :=
      map_commutatorElement (QuotientGroup.mk' N) a b
    have h2 : ⁅(a : Y ⧸ N), (b : Y ⧸ N)⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Std.Commutative.comm _ _
    exact (QuotientGroup.eq_one_iff _).mp (h1.trans h2)
  have hle : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ ≤ N :=
    Subgroup.commutator_le.mpr fun a _ b _ => hcomm a b
  have htop : ⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top (G := Y)
  rw [htop] at hle
  exact eq_top_iff.mpr hle

end Thompson

theorem b7c_of : B7cStatement := by
  intro G _ _ M Q Z B t hH hperf S₁ hS hLS hidx hj
  obtain ⟨j, hjS, hjLB, hjj, hconj⟩ := hj
  obtain ⟨hQS, hS1L, ⟨hNS, hPS⟩, hdvd⟩ := hS
  have hPS' : IsPGroup 2 (↥S₁ ⧸ Q.subgroupOf S₁) := hPS
  have hQLB : Q ≤ LB M Q B := le_sup_left
  have hLBM : LB M Q B ≤ M := sup_le hH.ctx.hyp.Q_normal.1 inf_le_right
  have hLM : Lgen M (LB M Q B) ≤ M := by
    refine iSup₂_le fun m hm => ?_
    show conjSubgroup m (LB M Q B) ≤ M
    exact (Subgroup.map_mono (f := (MulAut.conj m).toMonoidHom) hLBM).trans
      (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hm)).le
  set L : Subgroup G := Lgen M (LB M Q B) with hLdef
  have hQL : Q ≤ L := hQS.trans hS1L
  have hQnorm : L ≤ Subgroup.normalizer (Q : Set G) :=
    fun s hs => hH.ctx.hyp.Q_normal.2 (hLM hs)
  haveI hQsN : (Q.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mpr hQnorm
  have hmapTop : Subgroup.map L.subtype (⊤ : Subgroup ↥L) = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hperfL : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ Q.subgroupOf L = ⊤ := by
    apply Subgroup.map_injective (f := L.subtype) (Subgroup.subtype_injective L)
    rw [Subgroup.map_sup, Subgroup.map_commutator, hmapTop, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hQL]
    exact hperf
  let p : ↥L →* ↥L ⧸ Q.subgroupOf L := QuotientGroup.mk' (Q.subgroupOf L)
  have hsurj : Function.Surjective p := QuotientGroup.mk'_surjective _
  haveI hXperf : Group.IsPerfect (↥L ⧸ Q.subgroupOf L) := by
    refine ⟨?_⟩
    have htop : Subgroup.map p (⊤ : Subgroup ↥L) = ⊤ := Subgroup.map_top_of_surjective p hsurj
    have hcomm : Subgroup.map p ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ =
        ⁅(⊤ : Subgroup (↥L ⧸ Q.subgroupOf L)), (⊤ : Subgroup (↥L ⧸ Q.subgroupOf L))⁆ := by
      rw [Subgroup.map_commutator, htop]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨l, rfl⟩ := hsurj x
    have hl : l ∈ ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ⊔ Q.subgroupOf L := by
      rw [hperfL]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hl
    have hq1 : p q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
    have hmem : p a ∈ Subgroup.map p ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ :=
      Subgroup.mem_map_of_mem p ha
    rw [hcomm] at hmem
    rw [map_mul, hq1, mul_one]
    exact hmem
  have hjL : j ∈ L := hS1L hjS
  obtain ⟨s0, hs0⟩ : ∃ s0 : ↥L, (s0 : G) = j := ⟨⟨j, hjL⟩, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ↥L ⧸ Q.subgroupOf L, u = p s0 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : Subgroup (↥L ⧸ Q.subgroupOf L),
      P = (S₁.subgroupOf L).map p := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup (↥L ⧸ Q.subgroupOf L),
      T = ((LB M Q B).subgroupOf L).map p := ⟨_, rfl⟩
  have hTP : T ≤ P := by
    rw [hTdef, hPdef]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono L hLS)
  have huP : u ∈ P := by
    rw [hu, hPdef]
    exact Subgroup.mem_map_of_mem p (Subgroup.mem_subgroupOf.mpr (by rw [hs0]; exact hjS))
  have huT : u ∉ T := by
    intro h
    rw [hTdef] at h
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.mp h
    rw [hu] at hxu
    have h1 : x⁻¹ * s0 ∈ Q.subgroupOf L := QuotientGroup.eq.mp hxu
    have h2 : ((x⁻¹ * s0 : ↥L) : G) ∈ Q := Subgroup.mem_subgroupOf.mp h1
    have h3 : (x : G) * ((x⁻¹ * s0 : ↥L) : G) = j := by
      simp [hs0]
    apply hjLB
    rw [← h3]
    exact (LB M Q B).mul_mem (Subgroup.mem_subgroupOf.mp hx) (hQLB h2)
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul]
    refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ?_)
    show ((s0 * s0 : ↥L) : G) ∈ Q
    rw [Subgroup.coe_mul, hs0]
    exact hjj
  have hcos : ∀ t ∈ P, t ∈ T ∨ u⁻¹ * t ∈ T := by
    intro t ht
    rw [hPdef] at ht
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    rw [hTdef, hu]
    rcases b7c_dich hjS hjLB hidx (Subgroup.mem_subgroupOf.mp hs) with h | h
    · exact Or.inl (Subgroup.mem_map_of_mem p (Subgroup.mem_subgroupOf.mpr h))
    · refine Or.inr ?_
      have e : (p s0)⁻¹ * p s = p (s0⁻¹ * s) := by rw [map_mul, map_inv]
      rw [e]
      refine Subgroup.mem_map_of_mem p (Subgroup.mem_subgroupOf.mpr ?_)
      have hcoe : ((s0⁻¹ * s : ↥L) : G) = j⁻¹ * (s : G) := by simp [hs0]
      rw [hcoe]
      exact h
  have hP2 : IsPGroup 2 P := by
    rw [hPdef]
    intro y
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp y.2
    have hxS : (x : G) ∈ S₁ := Subgroup.mem_subgroupOf.mp hx
    obtain ⟨k, hk⟩ := hPS' ((⟨x, hxS⟩ : ↥S₁) : ↥S₁ ⧸ Q.subgroupOf S₁)
    have hk' : QuotientGroup.mk' (Q.subgroupOf S₁) ((⟨x, hxS⟩ : ↥S₁) ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact hk
    have hmemN : ((⟨x, hxS⟩ : ↥S₁) ^ 2 ^ k) ∈ Q.subgroupOf S₁ :=
      (QuotientGroup.eq_one_iff _).mp hk'
    have hxQ : ((x ^ 2 ^ k : ↥L) : G) ∈ Q := by
      simpa using Subgroup.mem_subgroupOf.mp hmemN
    have hp : p (x ^ 2 ^ k) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxQ)
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hxy, ← map_pow, hp]
    rfl
  have hPidx : ¬ 2 ∣ P.index := by
    rw [hPdef]
    intro h
    exact hdvd (h.trans (Subgroup.index_map_dvd (f := p) (S₁.subgroupOf L) hsurj))
  rcases b7c_thompson hP2 hPidx hTP hcos huP huT hu2 with ⟨N, hN, hcycN, huN⟩ | ⟨g, hg⟩
  ·
    haveI := hN
    haveI := hcycN
    have hNtop : N = ⊤ := b7c_eq_top_of_cyclic N
    exact huN (by rw [hNtop]; exact Subgroup.mem_top u)
  ·
    obtain ⟨h, rfl⟩ := hsurj g
    rw [hTdef] at hg
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hg
    have hconjeq : p (h⁻¹ * s0 * h) = (p h)⁻¹ * u * (p h) := by
      rw [hu, map_mul, map_mul, map_inv]
    have h2 : p x = p (h⁻¹ * s0 * h) := hxeq.trans hconjeq.symm
    have h3 : x⁻¹ * (h⁻¹ * s0 * h) ∈ Q.subgroupOf L := QuotientGroup.eq.mp h2
    have h4 : ((h⁻¹ * s0 * h : ↥L) : G) ∈ LB M Q B := by
      have h5 : ((x⁻¹ * (h⁻¹ * s0 * h) : ↥L) : G) ∈ Q := Subgroup.mem_subgroupOf.mp h3
      have h6 : ((h⁻¹ * s0 * h : ↥L) : G) = (x : G) * ((x⁻¹ * (h⁻¹ * s0 * h) : ↥L) : G) := by
        simp
      rw [h6]
      exact (LB M Q B).mul_mem (Subgroup.mem_subgroupOf.mp hx) (hQLB h5)
    apply hconj ((h : G))⁻¹ (L.inv_mem h.2)
    simpa [hs0] using h4

end CFSG.RankThree.GF2n.Smith81.Smith23E1

end
