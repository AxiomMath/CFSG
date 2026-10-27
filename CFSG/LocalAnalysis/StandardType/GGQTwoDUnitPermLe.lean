module

import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitPermLeA
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxMat

public section

namespace CFSG.StandardType.QTwo

theorem ggQTwoDUnit_perm_le {n m : ℕ} (hn : 5 ≤ n)
    (φ : Equiv.Perm (Fin n) →* (DVec m ≃ₗ[ZMod 3] DVec m)) (hinj : Function.Injective φ)
    (hφ : ∀ a b : Fin n, a ≠ b → ∃ (sgn : Bool) (a' b' : Fin m), a' ≠ b' ∧
      φ (Equiv.swap a b) = dTau m sgn a' b') : n ≤ m := by
  let S : Fin n → Fin n → Finset (Fin m) :=
    fun i j => qtwoDB33_supp m (φ (Equiv.swap i j))
  have hSdef : ∀ i j, S i j = qtwoDB33_supp m (φ (Equiv.swap i j)) := fun _ _ => rfl
  have hS_symm : ∀ i j, S i j = S j i := by
    intro i j
    rw [hSdef i j, hSdef j i, Equiv.swap_comm]
  have hS_card : ∀ i j, i ≠ j → (S i j).card = 2 := by
    intro i j hij
    obtain ⟨s, a, b, hab, hT⟩ := hφ i j hij
    rw [hSdef i j, hT, qtwoDB33_supp_dTau m s hab]
    exact Finset.card_pair hab
  have hS_inter : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → (S i j ∩ S i k).card = 1 := by
    intro i j k hij hik hjk
    obtain ⟨s, a, b, hab, hT1⟩ := hφ i j hij
    obtain ⟨s', a', b', hab', hT2⟩ := hφ i k hik
    have hS1 : S i j = {a, b} := by rw [hSdef i j, hT1, qtwoDB33_supp_dTau m s hab]
    have hS2 : S i k = {a', b'} := by rw [hSdef i k, hT2, qtwoDB33_supp_dTau m s' hab']
    have hle : (S i j ∩ S i k).card ≤ 2 := by
      calc (S i j ∩ S i k).card ≤ (S i j).card := Finset.card_le_card Finset.inter_subset_left
        _ = 2 := hS_card i j hij
    have hpos : 0 < (S i j ∩ S i k).card := by
      by_contra h
      have h0 : (S i j ∩ S i k).card = 0 := Nat.eq_zero_of_not_pos h
      have hdisj : Disjoint (S i j) (S i k) :=
        Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp h0)
      rw [hS1, hS2] at hdisj
      obtain ⟨haa, hab2, hba, hbb⟩ := qtwoDB33_cross_of_disjoint hdisj
      have hcomm := qtwoDB33_dTau_commute_disjoint s s' hab hab' haa hab2 hba hbb
      have hne := qtwoDB33_map_swap_mul_ne (φ := φ) hinj hij hik hjk
      exact hne (by rw [hT1, hT2]; exact hcomm)
    have hne2 : (S i j ∩ S i k).card ≠ 2 := by
      intro h2
      have hsub : S i j ⊆ S i k := by
        have heq : S i j ∩ S i k = S i j :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left
            (by rw [h2, hS_card i j hij])
        rw [← heq]; exact Finset.inter_subset_right
      have heqij : S i j = S i k :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hS_card i k hik, hS_card i j hij])
      have hp : ({a, b} : Finset (Fin m)) = {a', b'} := by
        rw [← hS1, heqij, hS2]
      have hcomm := qtwoDB33_dTau_commute_of_supp_eq s s' hab hab' hp
      have hne := qtwoDB33_map_swap_mul_ne (φ := φ) hinj hij hik hjk
      exact hne (by rw [hT1, hT2]; exact hcomm)
    omega
  have hπ_exists : ∀ i : Fin n, ∃ x : Fin m, ∀ j : Fin n, j ≠ i → x ∈ S i j := by
    intro i
    obtain ⟨j, hjinj, hji⟩ := qtwoDB33_four_index hn i
    have h01 : (S i (j 0) ∩ S i (j 1)).card = 1 :=
      hS_inter i (j 0) (j 1) (hji 0) (hji 1)
        (fun h => (by decide : (0 : Fin 4) ≠ 1) (hjinj h))
    obtain ⟨x, hx01⟩ := Finset.card_eq_one.mp h01
    have hx0 : x ∈ S i (j 0) := by
      have h : x ∈ S i (j 0) ∩ S i (j 1) := by rw [hx01]; exact Finset.mem_singleton_self x
      exact (Finset.mem_inter.mp h).1
    have hx1 : x ∈ S i (j 1) := by
      have h : x ∈ S i (j 0) ∩ S i (j 1) := by rw [hx01]; exact Finset.mem_singleton_self x
      exact (Finset.mem_inter.mp h).2
    refine ⟨x, fun k hk => ?_⟩
    by_cases hk0 : k = j 0
    · rwa [hk0]
    · by_cases hk1 : k = j 1
      · rwa [hk1]
      · have h0k : j 0 ≠ k := fun h => hk0 h.symm
        have h1k : j 1 ≠ k := fun h => hk1 h.symm
        by_cases hk2 : k = j 2
        · have hD : (S i (j 3)).card = 2 := hS_card i (j 3) (hji 3)
          have h03 : (S i (j 0) ∩ S i (j 3)).card = 1 :=
            hS_inter i (j 0) (j 3) (hji 0) (hji 3)
              (fun h => (by decide : (0 : Fin 4) ≠ 3) (hjinj h))
          have h13 : (S i (j 1) ∩ S i (j 3)).card = 1 :=
            hS_inter i (j 1) (j 3) (hji 1) (hji 3)
              (fun h => (by decide : (1 : Fin 4) ≠ 3) (hjinj h))
          have hk3 : (S i k ∩ S i (j 3)).card = 1 := by
            rw [hk2]
            exact hS_inter i (j 2) (j 3) (hji 2) (hji 3)
              (fun h => (by decide : (2 : Fin 4) ≠ 3) (hjinj h))
          exact qtwoDB33_three_common (hS_card i (j 0) (hji 0)) (hS_card i (j 1) (hji 1))
            (hS_card i k (Ne.symm hk)) hD h01 (hS_inter i (j 0) k (hji 0) (Ne.symm hk) h0k)
            (hS_inter i (j 1) k (hji 1) (Ne.symm hk) h1k) h03 h13 hk3 hx01
        · have hD : (S i (j 2)).card = 2 := hS_card i (j 2) (hji 2)
          have h02 : (S i (j 0) ∩ S i (j 2)).card = 1 :=
            hS_inter i (j 0) (j 2) (hji 0) (hji 2)
              (fun h => (by decide : (0 : Fin 4) ≠ 2) (hjinj h))
          have h12 : (S i (j 1) ∩ S i (j 2)).card = 1 :=
            hS_inter i (j 1) (j 2) (hji 1) (hji 2)
              (fun h => (by decide : (1 : Fin 4) ≠ 2) (hjinj h))
          have hk2' : (S i k ∩ S i (j 2)).card = 1 :=
            hS_inter i k (j 2) (Ne.symm hk) (hji 2) hk2
          exact qtwoDB33_three_common (hS_card i (j 0) (hji 0)) (hS_card i (j 1) (hji 1))
            (hS_card i k (Ne.symm hk)) hD h01 (hS_inter i (j 0) k (hji 0) (Ne.symm hk) h0k)
            (hS_inter i (j 1) k (hji 1) (Ne.symm hk) h1k) h02 h12 hk2' hx01
  choose π hπ using hπ_exists
  have hπ_inj : Function.Injective π := by
    intro i j hEq
    by_contra hij
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
      have hj : j ∈ Finset.univ.erase i :=
        Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
      have hcard : 0 < ((Finset.univ.erase i).erase j).card := by
        rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
        omega
      obtain ⟨k, hk⟩ := Finset.card_pos.mp hcard
      rw [Finset.mem_erase, Finset.mem_erase] at hk
      exact ⟨k, hk.2.1, hk.1⟩
    have hk_eq : π k = π i := by
      by_contra hkne
      obtain ⟨s, a, b, hab, hT1⟩ := hφ i k (Ne.symm hki)
      obtain ⟨s', a', b', hab', hT2⟩ := hφ j k (Ne.symm hkj)
      have hS1 : S i k = {a, b} := by rw [hSdef i k, hT1, qtwoDB33_supp_dTau m s hab]
      have hS2 : S j k = {a', b'} := by rw [hSdef j k, hT2, qtwoDB33_supp_dTau m s' hab']
      have heqik : S i k = S j k := by
        have hsub : ({π i, π k} : Finset (Fin m)) ⊆ S i k := by
          intro y hy
          rw [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hπ i k hki
          · rw [← hS_symm k i]; exact hπ k i hki.symm
        have hcardp : ({π i, π k} : Finset (Fin m)).card = 2 :=
          Finset.card_pair (fun h => hkne h.symm)
        have heq1 : ({π i, π k} : Finset (Fin m)) = S i k :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hS_card i k (Ne.symm hki), hcardp])
        have hpjk : π j ≠ π k := fun h => hkne (h.symm.trans hEq.symm)
        have hsub' : ({π j, π k} : Finset (Fin m)) ⊆ S j k := by
          intro y hy
          rw [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with rfl | rfl
          · exact hπ j k hkj
          · rw [← hS_symm k j]; exact hπ k j hkj.symm
        have hcardp' : ({π j, π k} : Finset (Fin m)).card = 2 := Finset.card_pair hpjk
        have heq2 : ({π j, π k} : Finset (Fin m)) = S j k :=
          Finset.eq_of_subset_of_card_le hsub' (by rw [hS_card j k (Ne.symm hkj), hcardp'])
        rw [← heq1, ← heq2, hEq]
      have hp : ({a, b} : Finset (Fin m)) = {a', b'} := by rw [← hS1, heqik, hS2]
      have hcomm := qtwoDB33_dTau_commute_of_supp_eq s s' hab hab' hp
      have hne := qtwoDB33_map_swap_mul_ne' (φ := φ) hinj hki.symm hkj.symm hij
      exact hne (by rw [hT1, hT2]; exact hcomm)
    have huij : π i ∈ S i j := hπ i j (Ne.symm hij)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by
      rw [Finset.card_erase_of_mem huij, hS_card i j hij])
    have ha' : a ∈ (S i j).erase (π i) := by rw [ha]; exact Finset.mem_singleton_self a
    have haSij : a ∈ S i j := (Finset.mem_erase.mp ha').2
    have hua : π i ≠ a := Ne.symm (Finset.mem_erase.mp ha').1
    have huik : π i ∈ S i k := hπ i k hki
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (by
      rw [Finset.card_erase_of_mem huik, hS_card i k (Ne.symm hki)])
    have hb' : b ∈ (S i k).erase (π i) := by rw [hb]; exact Finset.mem_singleton_self b
    have hub : π i ≠ b := Ne.symm (Finset.mem_erase.mp hb').1
    have hujk : π j ∈ S j k := hπ j k hkj
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp (by
      rw [Finset.card_erase_of_mem hujk, hS_card j k (Ne.symm hkj)])
    have hd' : d ∈ (S j k).erase (π j) := by rw [hd]; exact Finset.mem_singleton_self d
    have hdSjk : d ∈ S j k := (Finset.mem_erase.mp hd').2
    have hud : π i ≠ d := by
      have h1 : d ≠ π j := (Finset.mem_erase.mp hd').1
      rw [← hEq] at h1
      exact Ne.symm h1
    have hSij_eq : S i j = {π i, a} := by rw [← Finset.insert_erase huij, ha]
    have hSjk_eq : S j k = {π j, d} := by rw [← Finset.insert_erase hujk, hd]
    have hSik_eq : S i k = {π i, b} := by rw [← Finset.insert_erase huik, hb]
    have hinter : S i j ∩ S j k = {π i} := by
      have h1 : (S j i ∩ S j k).card = 1 :=
        hS_inter j i k (Ne.symm hij) (Ne.symm hkj) (Ne.symm hki)
      rw [hS_symm j i] at h1
      obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
      have hu : π i ∈ S i j ∩ S j k :=
        Finset.mem_inter.mpr ⟨hπ i j (Ne.symm hij), by rw [hEq]; exact hπ j k hkj⟩
      rw [hy, Finset.mem_singleton] at hu
      rw [hy, hu]
    have had : a ≠ d := by
      intro had_eq
      have hmem : a ∈ ({π i} : Finset (Fin m)) := by
        rw [← hinter]
        exact Finset.mem_inter.mpr ⟨haSij, had_eq ▸ hdSjk⟩
      exact hua (Finset.mem_singleton.mp hmem).symm
    obtain ⟨s1, a1, b1, hab1, hTij⟩ := hφ i j hij
    have hp1 : ({a1, b1} : Finset (Fin m)) = {π i, a} := by
      rw [← qtwoDB33_supp_dTau m s1 hab1, ← hTij, ← hSdef i j]
      rw [← Finset.insert_erase huij, ha]
    have hR : φ (Equiv.swap i j) = dTau m s1 (π i) a := by
      rcases qtwoDB33_pair_eq_cases hab1 hp1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hTij
      · rw [hTij, h1, h2, dTau_symm m s1 a (π i)]
    obtain ⟨s2, a2, b2, hab2, hTjk⟩ := hφ j k (Ne.symm hkj)
    have hp2 : ({a2, b2} : Finset (Fin m)) = {π j, d} := by
      rw [← qtwoDB33_supp_dTau m s2 hab2, ← hTjk, ← hSdef j k]
      rw [hSjk_eq]
    have hB : φ (Equiv.swap j k) = dTau m s2 (π j) d := by
      rcases qtwoDB33_pair_eq_cases hab2 hp2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hTjk
      · rw [hTjk, h1, h2, dTau_symm m s2 d (π j)]
    obtain ⟨s3, a3, b3, hab3, hTik⟩ := hφ i k (Ne.symm hki)
    have hp3 : ({a3, b3} : Finset (Fin m)) = {π i, b} := by
      rw [← qtwoDB33_supp_dTau m s3 hab3, ← hTik, ← hSdef i k]
      rw [hSik_eq]
    have hA : φ (Equiv.swap i k) = dTau m s3 (π i) b := by
      rcases qtwoDB33_pair_eq_cases hab3 hp3 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]; exact hTik
      · rw [hTik, h1, h2, dTau_symm m s3 b (π i)]
    have hB' : φ (Equiv.swap j k) = dTau m s2 (π i) d := by
      rw [hB, ← hEq]
    have hperm : Equiv.swap i j * Equiv.swap j k * (Equiv.swap i j)⁻¹ = Equiv.swap i k := by
      rw [← Equiv.swap_apply_apply (Equiv.swap i j) j k, Equiv.swap_apply_right,
        Equiv.swap_apply_of_ne_of_ne hki hkj]
    have hrel : φ (Equiv.swap i j) * φ (Equiv.swap j k) * (φ (Equiv.swap i j))⁻¹
        = φ (Equiv.swap i k) := by
      rw [← map_mul, ← map_inv, ← map_mul, hperm]
    exact (qtwoDB33_bad_ne' (u := π i) (a := a) (d := d) (b := b) (s := s1) (s' := s2)
      (s'' := s3) hua hud hub had hR hB' hA) hrel
  calc n = Fintype.card (Fin n) := (Fintype.card_fin n).symm
    _ ≤ Fintype.card (Fin m) := Fintype.card_le_of_injective π hπ_inj
    _ = m := Fintype.card_fin m

end CFSG.StandardType.QTwo

end
