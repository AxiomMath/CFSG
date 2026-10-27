
module

public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24Base

public import CFSG.Quasithin.Vol2.Ch12Sec5KG
public import CFSG.Quasithin.Vol2.Ch12Sec5KGM24Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicMathieu
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import Certificates.Certificate7249

public section

namespace CFSG.Quasithin.H13.S125KG.M24

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b m24_hyp)
open scoped commutatorElement

section KGFacts

theorem Y_le_of_incl {j jj : ℕ} (hj : j < 13) (hjj : jj < 13)
    (h : jj ∈ CFSG.Quasithin.S151S9T.m24Incl[j]!) : kgCtx.Y j ≤ kgCtx.Y jj :=
  (m24_Y_le_iff hj hjj).mpr h

theorem not_Y_le_of_incl {j jj : ℕ} (hj : j < 13) (hjj : jj < 13)
    (h : jj ∉ CFSG.Quasithin.S151S9T.m24Incl[j]!) : ¬ kgCtx.Y j ≤ kgCtx.Y jj :=
  fun hle => h ((m24_Y_le_iff hj hjj).mp hle)

theorem x_facts : elt xw ∈ kgCtx.Y 7 ∧ elt (xw ++ xw ++ xw) = 1 ∧ elt xw ≠ 1 :=
  Certificates.certificate7249.1

theorem alpha_facts :
    elt (invW y3w ++ xw ++ y3w) ∉ kgCtx.Y 2 ∧ elt ([0] ++ xw ++ [0]) ∉ kgCtx.Y 2 :=
  Certificates.certificate7249.2.1

theorem k_facts : elt k1w ∈ kgCtx.Y 2 ∧ elt k2w ∈ kgCtx.Y 2 ∧
    elt k1w = elt (commW (kWord c1v) (kWord c1u)) ∧
    elt k2w = elt (commW (kWord c2v) (kWord c2u)) ∧
    elt (w6w ++ invW (kWord kw6)) ∈ kgCtx.S :=
  Certificates.certificate7249.2.2.1

theorem q_facts : ∃ Q : Subgroup Γ, Nat.card Q = 64 ∧ Q ≤ kgCtx.Y 2 ∧
    kgCtx.Y 2 ≤ Subgroup.normalizer (Q : Set Γ) ∧
    ∀ g ∈ Q, g = 1 ∨ (elt vw * g ≠ g * elt vw ∧ elt ww * g ≠ g * elt ww) :=
  Certificates.certificate7249.2.2.2.1

theorem vw_facts : elt vw ∈ kgCtx.Y 2 ∧ elt ww ∈ kgCtx.Y 2 ∧
    elt (vw ++ vw ++ vw ++ vw ++ vw ++ vw ++ vw) = 1 ∧ elt vw ≠ 1 ∧
    elt (ww ++ ww ++ ww) = 1 ∧ elt ww ≠ 1 :=
  Certificates.certificate7249.2.2.2.2.1

theorem gens_facts : kgCtx.gens 3 = [elt y3w] ∧ kgCtx.gens 6 = [elt w6w] :=
  Certificates.certificate7249.2.2.2.2.2

end KGFacts

variable {X : Type} [Group X]

theorem Y_le_Y2
    {j : ℕ}
    (hj : j ∈ [2, 7, 10, 12]) : kgCtx.Y j ≤ kgCtx.Y 2 := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl
  · exact le_rfl
  · exact Y_le_of_incl (by norm_num) (by norm_num) (by decide)
  · exact Y_le_of_incl (by norm_num) (by norm_num) (by decide)
  · exact Y_le_of_incl (by norm_num) (by norm_num) (by decide)

theorem mem_of_Y7_le
    {j : ℕ} (hj : j ≤ 13)
    (h : kgCtx.Y 7 ≤ memberOrTop 13 kgCtx.Y j) :
    j = 2 ∨ j = 3 ∨ j = 7 ∨ j = 10 ∨ j = 12 ∨ j = 13 := by
  interval_cases j <;> first
    | omega
    | (exfalso; rw [member_lt (by norm_num)] at h
       exact not_Y_le_of_incl (by norm_num) (by norm_num) (by decide) h)

theorem not_Y9_le
    {j : ℕ}
    (hj : j ∈ [2, 7, 10, 12]) (h : kgCtx.Y 9 ≤ memberOrTop 13 kgCtx.Y j) : False := by
  have h9 : ∀ j ∈ [2, 7, 10, 12], j ∉ CFSG.Quasithin.S151S9T.m24Incl[9]! := by decide
  have hj' : j < 13 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hj
    omega
  rw [member_lt hj'] at h
  exact not_Y_le_of_incl (by norm_num) hj' (h9 j hj) h

theorem Y6_le
    (ψ : X ≃* Γ)
    {S N : Subgroup X} (hψ : S.map ψ.toMonoidHom = kgCtx.S)
    (hN2 : N.map ψ.toMonoidHom = kgCtx.Y 2) :
    kgCtx.Y 6 ≤ (CFSG.inSubgroup CFSG.perfectResidual N ⊔ S).map ψ.toMonoidHom := by
  obtain ⟨hk1, hk2, hc1, hc2, hw6⟩ := k_facts
  set K := Subgroup.closure ({elt k1w, elt k2w} : Set Γ) with hK
  have hk1K : elt k1w ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
  have hk2K : elt k2w ∈ K := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hgen : ∀ l, elt ([k1w, k2w, invW k1w, invW k2w].getD l []) ∈ K := by
    intro l
    rcases l with _ | _ | _ | _ | l
    · exact hk1K
    · exact hk2K
    · show elt (invW k1w) ∈ K
      rw [elt_invW]
      exact K.inv_mem hk1K
    · show elt (invW k2w) ∈ K
      rw [elt_invW]
      exact K.inv_mem hk2K
    · show elt [] ∈ K
      rw [elt_nil]
      exact K.one_mem
  have hKmem : ∀ u, elt (kWord u) ∈ K := by
    intro u
    induction u with
    | nil =>
      show elt [] ∈ K
      rw [elt_nil]
      exact K.one_mem
    | cons l u ih =>
      have e : kWord (l :: u) = [k1w, k2w, invW k1w, invW k2w].getD l [] ++ kWord u := by
        simp only [kWord, List.flatMap_cons]
      rw [e, elt_append]
      exact K.mul_mem (hgen l) ih
  have hKperf : K ≤ ⁅K, K⁆ := by
    refine (Subgroup.closure_le ⁅K, K⁆).mpr ?_
    rintro x (rfl | rfl)
    · rw [hc1, elt_commW]
      exact Subgroup.commutator_mem_commutator (hKmem _) (hKmem _)
    · rw [hc2, elt_commW]
      exact Subgroup.commutator_mem_commutator (hKmem _) (hKmem _)
  have hK2 : K ≤ kgCtx.Y 2 := by
    refine (Subgroup.closure_le (kgCtx.Y 2)).mpr ?_
    rintro x (rfl | rfl)
    · exact hk1
    · exact hk2
  have hK' : K.map ψ.symm.toMonoidHom ≤ CFSG.inSubgroup CFSG.perfectResidual N := by
    refine le_inSubgroup_perfectResidual_of_le ?_ ?_
    · intro y hy
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
      have h1 := hK2 hk
      rw [← hN2] at h1
      exact Subgroup.mem_map_equiv.mp h1
    · rw [← Subgroup.map_commutator]
      exact Subgroup.map_mono hKperf
  have hKY : K ≤ (CFSG.inSubgroup CFSG.perfectResidual N ⊔ S).map ψ.toMonoidHom := by
    intro k hk
    rw [Subgroup.mem_map_equiv]
    exact Subgroup.mem_sup_left (hK' ⟨k, hk, rfl⟩)
  have hSY : kgCtx.S ≤ (CFSG.inSubgroup CFSG.perfectResidual N ⊔ S).map ψ.toMonoidHom := by
    rw [← hψ]
    exact Subgroup.map_mono le_sup_right
  show Subgroup.closure {x | x ∈ kgCtx.sg ++ kgCtx.gens 6} ≤ _
  rw [Subgroup.closure_le]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hSY (kgCtx.sg_mem_S x hx)
  · rw [gens_facts.2, List.mem_singleton] at hx
    rw [hx]
    have e : elt w6w = elt (w6w ++ invW (kWord kw6)) * elt (kWord kw6) := by
      rw [elt_append, elt_invW, inv_mul_cancel_right]
    rw [e]
    exact Subgroup.mul_mem _ (hSY hw6) (hKY (hKmem kw6))

theorem map_D
    (ψ : X ≃* Γ)
    {S N D : Subgroup X} (hψ : S.map ψ.toMonoidHom = kgCtx.S) (hc : Config63 S N D) :
    D.map ψ.toMonoidHom = kgCtx.Y 7 := by
  have hN2 := map_N ψ hψ hc
  obtain ⟨hSD, hDN, -, hDc, hnot⟩ := hc
  obtain ⟨j, hj, h, hcard⟩ := exists_member_map ψ hψ hSD
  rw [hDc, card_S ψ hψ] at hcard
  have hDN' : memberOrTop 13 kgCtx.Y j ≤ kgCtx.Y 2 := by
    rw [← h, ← hN2]
    exact Subgroup.map_mono hDN
  have hnot' : ¬ memberOrTop 13 kgCtx.Y j ≤ kgCtx.Y 6 := by
    intro hle
    apply hnot
    rw [← Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective, h]
    exact hle.trans (Y6_le ψ hψ hN2)
  rw [h]
  interval_cases j
  · simp at hcard
  · simp at hcard
  · simp at hcard
  · simp at hcard
  · simp at hcard
  · simp at hcard
  · simp at hcard
  · exact member_lt (by norm_num)
  · exfalso
    rw [member_lt (by norm_num)] at hnot'
    exact hnot' (Y_le_of_incl (by norm_num) (by norm_num) (by decide))
  · exfalso
    rw [member_lt (by norm_num)] at hDN'
    exact not_Y_le_of_incl (by norm_num) (by norm_num) (by decide) hDN'
  · simp at hcard
  · exfalso
    rw [member_lt (by norm_num)] at hnot'
    exact hnot' (Y_le_of_incl (by norm_num) (by norm_num) (by decide))
  · simp at hcard
  · simp at hcard

theorem kg125AlphaM24 :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.M24) →
      ∀ S N D : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → Config63 S N D →
        Subgroup.normalizer (oTwoUpper D : Set X) ≤ N := by
  intro X _ _ hX S N D hS hc
  obtain ⟨ψ, hψ⟩ := exists_equiv hX hS
  have hN2 := map_N ψ hψ hc
  have hD7 := map_D ψ hψ hc
  obtain ⟨hSD, hDN, -, -, -⟩ := hc
  obtain ⟨hx7, hx3, hx1⟩ := x_facts
  obtain ⟨hα3, hαa⟩ := alpha_facts
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxD : ψ.symm (elt xw) ∈ D := by
    have h1 : elt xw ∈ D.map ψ.toMonoidHom := by
      rw [hD7]
      exact hx7
    exact Subgroup.mem_map_equiv.mp h1
  have hxo : orderOf (ψ.symm (elt xw)) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_elt' (elt_pow_three xw) hx3 hx1
  have hxO : ψ.symm (elt xw) ∈ oTwoUpper D :=
    mem_oTwoUpper_of_odd hxD (by rw [hxo]; exact ⟨1, rfl⟩)
  have hDM : D ≤ Subgroup.normalizer (oTwoUpper D : Set X) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_oTwoUpper D)
  obtain ⟨j, hj, hM, -⟩ := exists_member_map ψ hψ (hSD.trans hDM)
  have h7 : kgCtx.Y 7 ≤ memberOrTop 13 kgCtx.Y j := by
    rw [← hM, ← hD7]
    exact Subgroup.map_mono hDM
  have hconj : ∀ g : Γ, g ∈ memberOrTop 13 kgCtx.Y j → g⁻¹ * elt xw * g ∈ kgCtx.Y 2 := by
    intro g hg
    rw [← hM] at hg
    have h1 := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (Subgroup.mem_map_equiv.mp hg)) (ψ.symm (elt xw))).mp hxO
    rw [inv_inv] at h1
    rw [← hN2, Subgroup.mem_map_equiv, map_mul, map_mul, map_inv]
    exact hDN (oTwoUpper_le D h1)
  have hle : ∀ j', j' ∈ [2, 7, 10, 12] → memberOrTop 13 kgCtx.Y j = kgCtx.Y j' →
      Subgroup.normalizer (oTwoUpper D : Set X) ≤ N := by
    intro j' hj' he
    rw [← Subgroup.map_le_map_iff_of_injective (f := ψ.toMonoidHom) ψ.injective, hM, hN2, he]
    exact Y_le_Y2 hj'
  rcases mem_of_Y7_le hj h7 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact hle 2 (by simp) (member_lt (by norm_num))
  · exfalso
    have hy : elt y3w ∈ memberOrTop 13 kgCtx.Y 3 := by
      rw [member_lt (by norm_num)]
      exact kgCtx.gens_mem_Y _
        (by rw [gens_facts.1]; exact List.mem_singleton_self _)
    have h1 := hconj _ hy
    rw [← elt_invW, ← elt_append, ← elt_append] at h1
    exact hα3 h1
  · exact hle 7 (by simp) (member_lt (by norm_num))
  · exact hle 10 (by simp) (member_lt (by norm_num))
  · exact hle 12 (by simp) (member_lt (by norm_num))
  · exfalso
    have h1 := hconj m24a (by rw [member_top]; exact Subgroup.mem_top _)
    rw [inv_eq_of_mul_eq_one_left a_mul_a, ← elt_a, ← elt_append, ← elt_append] at h1
    exact hαa h1

theorem kg125BetaM24 :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.M24) →
      ∀ S N D E : Subgroup X, QuasithinUnique.IsSylowTwoOf S ⊤ → Config63 S N D →
        E ≤ pCoreOf 2 N → N ≤ Subgroup.normalizer (E : Set X) → E = ⊥ ∨ Nat.card E = 64 := by
  intro X _ _ hX S N D E hS hc hEO hNE
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨ψ, hψ⟩ := exists_equiv hX hS
  obtain ⟨Q, hQc, hQY, hQN, hfree⟩ := q_facts
  have hN2 := map_N ψ hψ hc
  have hEQ : E ≤ Q.comap ψ.toMonoidHom := by
    rw [← pCoreOf_eq ψ hS hψ hc hQc hQY hQN]
    exact hEO
  obtain ⟨hv2, hw2, hv7, hv1, hw3, hw1⟩ := vw_facts
  have hmemN : ∀ w, elt w ∈ kgCtx.Y 2 → ψ.symm (elt w) ∈ N := fun w hw => by
    have h1 : elt w ∈ N.map ψ.toMonoidHom := by
      rw [hN2]
      exact hw
    exact Subgroup.mem_map_equiv.mp h1
  have hfix : ∀ w, (∀ g ∈ Q, g = 1 ∨ elt w * g ≠ g * elt w) →
      ∀ e ∈ E, ψ.symm (elt w) * e = e * ψ.symm (elt w) → e = 1 := by
    intro w hw e he hce
    have h1 : ψ e ∈ Q := hEQ he
    have h2 : elt w * ψ e = ψ e * elt w := by
      have h3 := congrArg ψ hce
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    rcases hw _ h1 with h3 | h3
    · exact (MulEquiv.map_eq_one_iff ψ).mp h3
    · exact absurd h2 h3
  have h7 : Nat.card E ≡ 1 [MOD 7] := card_modEq_one_of_fixedPointFree
    (by rw [MulEquiv.orderOf_eq]; exact orderOf_elt' (elt_pow_seven vw) hv7 hv1)
    (hNE (hmemN vw hv2)) (hfix vw fun g hg => (hfree g hg).imp id And.left)
  have h3 : Nat.card E ≡ 1 [MOD 3] := card_modEq_one_of_fixedPointFree
    (by rw [MulEquiv.orderOf_eq]; exact orderOf_elt' (elt_pow_three ww) hw3 hw1)
    (hNE (hmemN ww hw2)) (hfix ww fun g hg => (hfree g hg).imp id And.right)
  have hdvd : Nat.card E ∣ 2 ^ 6 := by
    have h4 := Subgroup.card_dvd_of_le hEQ
    rwa [card_comap_mulEquiv, hQc] at h4
  obtain ⟨m, hm, hme⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rw [hme] at h7 h3
  interval_cases m
  · exact Or.inl (Subgroup.eq_bot_of_card_eq E (hme.trans (by norm_num)))
  · norm_num [Nat.ModEq] at h7
  · norm_num [Nat.ModEq] at h7
  · norm_num [Nat.ModEq] at h3
  · norm_num [Nat.ModEq] at h7
  · norm_num [Nat.ModEq] at h7
  · exact Or.inr (hme.trans (by norm_num))

theorem kg125GammaM24 :
    KG125GammaM24 := by
  intro X _ _ K₀ _ hK₀ hC _ S hS
  have hK := eq_top_of_m24 hK₀ hC
  obtain ⟨e⟩ := hK₀
  obtain ⟨ψ, hψ⟩ := exists_equiv
    ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hK.symm)).trans e⟩ hS
  have hSY : ∀ j, S ≤ (kgCtx.Y j).comap ψ.toMonoidHom := fun j => by
    rw [← Subgroup.map_le_iff_le_comap, hψ]
    exact kgCtx.S_le_Y j
  have hsolv : ∀ j < 13, [1, 315, 63, 135, 21, 9, 21, 3, 3, 3, 9, 3, 9, 239085].getD j 0 = 3 →
      Group.IsSolvable ↥((kgCtx.Y j).comap ψ.toMonoidHom) := by
    intro j hj h3
    refine isSolvable_of_card_eq ((card_comap_mulEquiv ψ _).trans ?_)
    rw [← member_lt hj, card_member hj.le, h3]
  have hAB : (kgCtx.Y 7).comap ψ.toMonoidHom ⊔ (kgCtx.Y 9).comap ψ.toMonoidHom ≤
      sSup {H : Subgroup X | S ≤ H ∧ Group.IsSolvable ↥H} :=
    sup_le (le_sSup ⟨hSY 7, hsolv 7 (by norm_num) rfl⟩)
      (le_sSup ⟨hSY 9, hsolv 9 (by norm_num) rfl⟩)
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hAB)
  obtain ⟨j, hj, h, hcard⟩ := exists_member_map ψ hψ ((hSY 7).trans le_sup_left)
  have hmap : ((kgCtx.Y 7).comap ψ.toMonoidHom ⊔ (kgCtx.Y 9).comap ψ.toMonoidHom).map
      ψ.toMonoidHom = kgCtx.Y 7 ⊔ kgCtx.Y 9 := by
    rw [Subgroup.map_sup,
      Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective,
      Subgroup.map_comap_eq_self_of_surjective (f := ψ.toMonoidHom) ψ.surjective]
  rw [hmap] at h
  have h7 : kgCtx.Y 7 ≤ memberOrTop 13 kgCtx.Y j := by
    rw [← h]
    exact le_sup_left
  have h9 : kgCtx.Y 9 ≤ memberOrTop 13 kgCtx.Y j := by
    rw [← h]
    exact le_sup_right
  rw [hcard]
  rcases mem_of_Y7_le hj h7 with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (not_Y9_le (by simp) h9).elim
  · norm_num
  · exact (not_Y9_le (by simp) h9).elim
  · exact (not_Y9_le (by simp) h9).elim
  · exact (not_Y9_le (by simp) h9).elim
  · norm_num

end CFSG.Quasithin.H13.S125KG.M24
