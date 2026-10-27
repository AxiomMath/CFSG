module

public import CFSG.Sporadic.Schreier.RuCheckBasic

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

theorem slotRun_mem {G : Type*} [Group G] {H : Subgroup G} (rows : List SlotRow) {g₁ g₂ : G}
    (h₁ : g₁ ∈ H) (h₂ : g₂ ∈ H) : (slotRun rows g₁ g₂).1 ∈ H ∧ (slotRun rows g₁ g₂).2 ∈ H := by
  have hread : ∀ (s : List (ℕ × G)), (∀ p ∈ s, p.2 ∈ H) → ∀ k, slotRead s k ∈ H := by
    intro s hs k
    induction s with
    | nil => exact H.one_mem
    | cons p s ih =>
      obtain ⟨a, g⟩ := p
      by_cases hk : k = a
      · subst hk
        simp only [slotRead, lookup_cons_self, Option.getD_some]
        exact hs _ List.mem_cons_self
      · have := ih fun q hq => hs q (List.mem_cons_of_mem _ hq)
        simpa only [slotRead, lookup_cons_ne hk] using this
  have hfold : ∀ (rows : List SlotRow) (s : List (ℕ × G)), (∀ p ∈ s, p.2 ∈ H) →
      ∀ p ∈ rows.foldl slotStep s, p.2 ∈ H := by
    intro rows
    induction rows with
    | nil => intro s hs; exact hs
    | cons r rows ih =>
      intro s hs
      rw [List.foldl_cons]
      apply ih
      intro p hp
      cases r with
      | mu i j k =>
        rcases List.mem_cons.1 hp with rfl | hp
        · exact H.mul_mem (hread s hs i) (hread s hs j)
        · exact hs p hp
      | iv i j =>
        rcases List.mem_cons.1 hp with rfl | hp
        · exact H.inv_mem (hread s hs i)
        · exact hs p hp
      | pwr e i j =>
        rcases List.mem_cons.1 hp with rfl | hp
        · exact H.pow_mem (hread s hs i) e
        · exact hs p hp
  have h0 : ∀ p ∈ ([(1, g₁), (2, g₂)] : List (ℕ × G)), p.2 ∈ H := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact h₁
    · exact h₂
  exact ⟨hread _ (hfold rows _ h0) 1, hread _ (hfold rows _ h0) 2⟩

theorem ruA0_mem : ruA0 ∈ ruP := Subgroup.subset_closure (Set.mem_insert _ _)

theorem ruA1_mem : ruA1 ∈ ruP := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ruC0_mem : ruC0 ∈ ruP := (slotRun_mem ruCProg ruA0_mem ruA1_mem).1

theorem ruC1_mem : ruC1 ∈ ruP := (slotRun_mem ruCProg ruA0_mem ruA1_mem).2

theorem ruN0_mem : ruN0 ∈ ruP := (slotRun_mem ruNProg ruA0_mem ruA1_mem).1

theorem ruN1_mem : ruN1 ∈ ruP := (slotRun_mem ruNProg ruA0_mem ruA1_mem).2

theorem ruZ_mem : ruZ ∈ ruP := ruP.pow_mem ruC0_mem 10

theorem pair_mem {G : Type*} [Group G] {H : Subgroup G} {g₀ g₁ : G} (h₀ : g₀ ∈ H) (h₁ : g₁ ∈ H) :
    ∀ g ∈ [g₀, g₁], g ∈ H := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact h₀
  · exact h₁

theorem ruH_mem : ruH ∈ ruP := by
  have hw : ruW ∈ ruP := evalSigned_mem (pair_mem ruA0_mem ruA1_mem) _
  have hz0 : ruZ0 ∈ ruP := evalSigned_mem (pair_mem ruN0_mem ruN1_mem) _
  exact ruP.mul_mem (ruP.pow_mem (ruP.mul_mem (ruP.mul_mem (ruP.mul_mem hw hz0)
    (ruP.inv_mem hw)) ruZ_mem) 3) hw

theorem ruNs0_mem : ruNs0 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN0_mem) (ruP.inv_mem ruH_mem)

theorem ruNs1_mem : ruNs1 ∈ ruP := ruP.mul_mem (ruP.mul_mem ruH_mem ruN1_mem) (ruP.inv_mem ruH_mem)

theorem closure_pair_le {G : Type*} [Group G] {H : Subgroup G} {g₀ g₁ : G} (h₀ : g₀ ∈ H)
    (h₁ : g₁ ∈ H) : Subgroup.closure {g₀, g₁} ≤ H := by
  rw [Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact h₀
  · exact h₁

theorem closure_list_le {G : Type*} [Group G] {H : Subgroup G} {l : List G}
    (h : ∀ g ∈ l, g ∈ H) : Subgroup.closure {g | g ∈ l} ≤ H := by
  rw [Subgroup.closure_le]
  exact fun g hg => h g hg

theorem ruC_le : ruC ≤ ruP := closure_pair_le ruC0_mem ruC1_mem

theorem ruN_le : ruN ≤ ruP := closure_pair_le ruNs0_mem ruNs1_mem

theorem ruSGens_mem : ∀ g ∈ ruSGens, g ∈ ruP := by
  intro g hg
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruNs0_mem ruNs1_mem) w

theorem ruS_le : ruS ≤ ruP := closure_list_le ruSGens_mem

theorem ruK_le : ruK ≤ ruP := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruNs0_mem ruNs1_mem) w

theorem ruJ_le : ruJ ≤ ruP := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem (pair_mem ruC0_mem ruC1_mem) w

theorem ruR_le : ruR ≤ ruP := closure_list_le fun g hg => by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalSigned_mem ruSGens_mem w

theorem ruE_subset : ruE ⊆ ruP := by
  rintro g (hg | ⟨m, hm, rfl⟩)
  · rw [Set.mem_singleton_iff.1 hg]
    exact ruP.one_mem
  · exact ruP.mul_mem (ruP.mul_mem (ruN_le hm) ruZ_mem) (ruP.inv_mem (ruN_le hm))

theorem ruChain_counts :
    ruChainC.originalCount = 2 ∧ ruChainC.strongCount = 7 ∧
    ruChainN.originalCount = 2 ∧ ruChainN.strongCount = 6 ∧
    ruChainJoin.originalCount = 4 ∧ ruChainJoin.strongCount = 18 ∧
    ruChainCFaithful.originalCount = 2 ∧ ruChainCFaithful.strongCount = 7 ∧
    ruChainCQuotient80.originalCount = 2 ∧ ruChainCQuotient80.strongCount = 8 ∧
    ruChainS.originalCount = 4 ∧ ruChainS.strongCount = 7 ∧
    ruChainK.originalCount = 8 ∧ ruChainK.strongCount = 10 ∧
    ruChainJ.originalCount = 6 ∧ ruChainJ.strongCount = 10 ∧
    ruChainR.originalCount = 5 ∧ ruChainR.strongCount = 7 := by
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_, rfl, ?_⟩ <;>
  simp [ruChainC, ruChainN, ruChainJoin, ruChainCFaithful, ruChainCQuotient80, ruChainS,
    ruChainK, ruChainJ, ruChainR, RawSchreierDatum.ofArrays_strongCount, ruField4060, ruField1920,
    ruField80, ruLines4060, ruLines1920]

theorem ruChain_bases :
    ruChainC.base.toList.map Fin.val = [0, 1, 2] ∧ ruChainN.base.toList.map Fin.val = [0, 1, 2] ∧
    ruChainJoin.base.toList.map Fin.val = [0, 1, 2, 3] ∧
    ruChainCFaithful.base.toList.map Fin.val = [0, 1] ∧
    ruChainCQuotient80.base.toList.map Fin.val = [0, 1, 2, 4] ∧
    ruChainS.base.toList.map Fin.val = [1, 0] ∧ ruChainK.base.toList.map Fin.val = [0, 1] ∧
    ruChainJ.base.toList.map Fin.val = [0, 1] ∧ ruChainR.base.toList.map Fin.val = [0, 1] := by
  simp only [ruChainC, ruChainN, ruChainJoin, ruChainCFaithful, ruChainCQuotient80, ruChainS,
    ruChainK, ruChainJ, ruChainR, RawSchreierDatum.ofArrays_base_toList]
  decide

theorem AT_Ru_local_certificate_data :
    (∀ L < 45, Rep 4060 (ruArr4060 L) (permOfArr 4060 (ruArr4060 L))) ∧
    (∀ L < 41, Rep 1920 (ruArr1920 L) (permOfArr 1920 (ruArr1920 L))) ∧
    (∀ L < 8, Rep 80 (ruArr80 L) (permOfArr 80 (ruArr80 L))) ∧
    ruChainC.originalCount = 2 ∧ ruChainC.strongCount = 7 ∧
    ruChainN.originalCount = 2 ∧ ruChainN.strongCount = 6 ∧
    ruChainJoin.originalCount = 4 ∧ ruChainJoin.strongCount = 18 ∧
    ruChainCFaithful.originalCount = 2 ∧ ruChainCFaithful.strongCount = 7 ∧
    ruChainCQuotient80.originalCount = 2 ∧ ruChainCQuotient80.strongCount = 8 ∧
    ruChainS.originalCount = 4 ∧ ruChainS.strongCount = 7 ∧
    ruChainK.originalCount = 8 ∧ ruChainK.strongCount = 10 ∧
    ruChainJ.originalCount = 6 ∧ ruChainJ.strongCount = 10 ∧
    ruChainR.originalCount = 5 ∧ ruChainR.strongCount = 7 ∧
    ruChainC.base.toList.map Fin.val = [0, 1, 2] ∧ ruChainN.base.toList.map Fin.val = [0, 1, 2] ∧
    ruChainJoin.base.toList.map Fin.val = [0, 1, 2, 3] ∧
    ruChainCFaithful.base.toList.map Fin.val = [0, 1] ∧
    ruChainCQuotient80.base.toList.map Fin.val = [0, 1, 2, 4] ∧
    ruChainS.base.toList.map Fin.val = [1, 0] ∧ ruChainK.base.toList.map Fin.val = [0, 1] ∧
    ruChainJ.base.toList.map Fin.val = [0, 1] ∧ ruChainR.base.toList.map Fin.val = [0, 1] ∧
    ruDerivOK ruCGenCount 7 ruCDerivations = true ∧ ruDerivOK ruNGenCount 6 ruNDerivations = true ∧
    ruDerivOK ruJoinGenCount 18 ruJoinDerivations = true ∧
    ruDerivOK ruCFaithfulGenCount 7 ruCFaithfulDerivations = true ∧
    ruDerivOK ruCQuotient80GenCount 8 ruCQuotient80Derivations = true ∧
    ruDerivOK ruSGenCount 7 ruSDerivations = true ∧ ruDerivOK ruKGenCount 10 ruKDerivations = true ∧
    ruDerivOK ruJGenCount 10 ruJDerivations = true ∧ ruDerivOK ruRGenCount 7 ruRDerivations = true ∧
    ((List.range 4).map fun i => (ruCOrbit i).size) = [1920, 2048, 80, 12] ∧
    ((List.range 3).map fun i => (ruNOrbit i).size) = [3584, 448, 28] ∧
    ruF.size = 1920 ∧ ruY.size = 80 ∧
    (∀ f < 9, ∀ i < (ruPtsOffsets.getD f (0, 0)).2, (ruPtList f)[i]! < 4060) ∧
    ruCSmallOrbit.length = 12 ∧ ruNSmallOrbit.length = 28 ∧
    (∀ k < 12, ruCSmallPartition.getD k 0 < 6) ∧ (∀ k < 28, ruNSmallPartition.getD k 0 < 7) ∧
    (∀ x ∈ ruCSmallOrbit, x < 4060) ∧ (∀ x ∈ ruNSmallOrbit, x < 4060) ∧
    ruDerivedProvenance.length = 5 ∧ ruQuotientBits.length = 4 ∧ (∀ b ∈ ruQuotientBits, b < 8) ∧
    ruBytesTree.size = 6 * (ruTreeCount - 1) ∧
    ruC0 ∈ ruP ∧ ruC1 ∈ ruP ∧ ruN0 ∈ ruP ∧ ruN1 ∈ ruP ∧ ruZ ∈ ruP ∧ ruH ∈ ruP ∧
    ruC ≤ ruP ∧ ruN ≤ ruP ∧ ruS ≤ ruP ∧ ruK ≤ ruP ∧ ruJ ≤ ruP ∧ ruR ≤ ruP ∧ ruE ⊆ ruP := by
  obtain ⟨-, -, -, h4060, h1920, h80, -, hpts, htree, d1, d2, d3, d4, d5, d6, d7, d8, d9, hcp,
    hnp, hco, -, hnl, -, hcx, hnx, hbits⟩ := ruEncoding_check
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18⟩ :=
    ruChain_counts
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := ruChain_bases
  refine ⟨fun L hL => (rep_permOfArr (h4060 L hL)).1, fun L hL => (rep_permOfArr (h1920 L hL)).1,
    fun L hL => (rep_permOfArr (h80 L hL)).1, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12,
    c13, c14, c15, c16, c17, c18, b1, b2, b3, b4, b5, b6, b7, b8, b9, d1, d2, d3, d4, d5, d6, d7,
    d8, d9, ?_, ?_, ?_, ?_, hpts, hco, hnl, hcp, hnp, hcx, hnx, rfl, rfl, hbits,
    by rw [htree]; rfl, ruC0_mem,
    ruC1_mem, ruN0_mem, ruN1_mem, ruZ_mem, ruH_mem, ruC_le, ruN_le, ruS_le, ruK_le, ruJ_le, ruR_le,
    ruE_subset⟩
  · simp only [ruCOrbit, ruPtList, Array.size_ofFn]
    decide
  · simp only [ruNOrbit, ruPtList, Array.size_ofFn]
    decide
  · simp only [ruF, ruPtList, Array.size_ofFn]
    decide
  · simp only [ruY, ruPtList, Array.size_ofFn]
    decide

end CFSG.Sporadic.RuSchreier
