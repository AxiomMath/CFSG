module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylInduced
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf SpJoin

namespace GGHalfTorusFrame

private noncomputable def flip3 (T : Finset (Fin 3)) :
    Equiv.Perm (Fin 3 → Multiplicative (ZMod 3)) where
  toFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  invFun v := fun t => if t ∈ T then (v t)⁻¹ else v t
  left_inv v := by
    funext t
    by_cases h : t ∈ T
    · simp only [h, if_true]
      exact inv_inv (v t)
    · simp only [h, if_false]
  right_inv v := by
    funext t
    by_cases h : t ∈ T
    · simp only [h, if_true]
      exact inv_inv (v t)
    · simp only [h, if_false]

@[simp] private theorem flip3_apply (T : Finset (Fin 3))
    (v : Fin 3 → Multiplicative (ZMod 3)) (t : Fin 3) :
    flip3 T v t = if t ∈ T then (v t)⁻¹ else v t := rfl

private theorem inv_ne_self_three : ∀ x : Multiplicative (ZMod 3), x ≠ 1 → x⁻¹ ≠ x := by
  decide

private theorem inv_one_three : (1 : Multiplicative (ZMod 3))⁻¹ = 1 := inv_one

private theorem flip3_mem (T : Finset (Fin 3)) : flip3 T ∈ spSignedGroup 3 3 := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      rw [show flip3 (∅ : Finset (Fin 3)) = 1 by
        ext v t; simp [flip3_apply]]
      exact Subgroup.one_mem _
  | insert a T ha ih =>
      have hstep : flip3 (insert a T) = coordInv 3 3 a * flip3 T := by
        ext v t
        rw [flip3_apply, Equiv.Perm.mul_apply, coordInv_apply]
        by_cases ht : t = a
        · rw [ht]
          rw [if_pos (Finset.mem_insert_self a T), Function.update_self, flip3_apply,
            if_neg ha]
          rfl
        · rw [Function.update_apply, if_neg ht, flip3_apply]
          by_cases htT : t ∈ T
          · rw [if_pos (Finset.mem_insert_of_mem htT), if_pos htT]
          · rw [if_neg (fun h => by
              rcases Finset.mem_insert.mp h with h' | h'
              · exact ht h'
              · exact htT h'), if_neg htT]
      rw [hstep]
      exact Subgroup.mul_mem _ (coordInv_mem_spSignedGroup a) ih

private def supp3 (v : Fin 3 → Multiplicative (ZMod 3)) : Finset (Fin 3) :=
  Finset.univ.filter (fun t => v t ≠ 1)

private theorem flip3_inter_supp3 (v : Fin 3 → Multiplicative (ZMod 3)) (T : Finset (Fin 3)) :
    flip3 T v = flip3 (T ∩ supp3 v) v := by
  ext t
  rw [flip3_apply, flip3_apply]
  by_cases hvt : v t = 1
  · have ht : t ∉ supp3 v := by
      simp only [supp3, Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h hvt
    by_cases htT : t ∈ T
    · have hmem : t ∉ T ∩ supp3 v := fun h => ht (Finset.mem_inter.mp h).2
      rw [if_pos htT, if_neg hmem, hvt, inv_one_three]
    · have hmem : t ∉ T ∩ supp3 v := fun h => htT (Finset.mem_inter.mp h).1
      rw [if_neg htT, if_neg hmem]
  · have ht : t ∈ supp3 v := by
      simp only [supp3, Finset.mem_filter, Finset.mem_univ, true_and]; exact hvt
    by_cases htT : t ∈ T
    · have hmem : t ∈ T ∩ supp3 v := Finset.mem_inter.mpr ⟨htT, ht⟩
      rw [if_pos htT, if_pos hmem]
    · have hmem : t ∉ T ∩ supp3 v := fun h => htT (Finset.mem_inter.mp h).1
      rw [if_neg htT, if_neg hmem]

private theorem image_powerset_flip3_eq (v : Fin 3 → Multiplicative (ZMod 3)) :
    (Finset.univ.powerset.image (fun T => flip3 T v)) =
      ((supp3 v).powerset.image (fun T => flip3 T v)) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨T, -, hT⟩ := Finset.mem_image.mp hw
    refine Finset.mem_image.mpr ⟨T ∩ supp3 v,
      Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
    rw [← hT]
    exact (flip3_inter_supp3 v T).symm
  · intro w hw
    obtain ⟨T, -, hT⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image.mpr ⟨T, Finset.mem_powerset.mpr (Finset.subset_univ T), hT⟩

private theorem card_image_powerset_flip3 (v : Fin 3 → Multiplicative (ZMod 3)) :
    (Finset.univ.powerset.image (fun T => flip3 T v)).card = 2 ^ (supp3 v).card := by
  have hinj : Set.InjOn (fun T => flip3 T v) ↑((supp3 v).powerset) := by
    intro T hT T' hT' hEq
    have hTsub : T ⊆ supp3 v := Finset.mem_powerset.mp (Finset.mem_coe.mp hT)
    have hT'sub : T' ⊆ supp3 v := Finset.mem_powerset.mp (Finset.mem_coe.mp hT')
    apply Finset.ext
    intro t
    by_cases ht : t ∈ supp3 v
    · have hvt : v t ≠ 1 := (Finset.mem_filter.mp ht).2
      have hval : (if t ∈ T then (v t)⁻¹ else v t) =
          (if t ∈ T' then (v t)⁻¹ else v t) := by
        have hthis : (fun T => flip3 T v) T t = (fun T => flip3 T v) T' t :=
          congrFun hEq t
        change flip3 T v t = flip3 T' v t at hthis
        rwa [flip3_apply, flip3_apply] at hthis
      constructor
      · intro htT
        by_contra htT'
        rw [if_pos htT, if_neg htT'] at hval
        exact absurd hval (inv_ne_self_three (v t) hvt)
      · intro htT'
        by_contra htT
        rw [if_neg htT, if_pos htT'] at hval
        exact absurd hval.symm (inv_ne_self_three (v t) hvt)
    · have hvt : v t = 1 := by
        by_contra h; exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have htT : t ∉ T := fun h => ht (hTsub h)
      have htT' : t ∉ T' := fun h => ht (hT'sub h)
      simp [htT, htT']
  rw [image_powerset_flip3_eq v, Finset.card_image_of_injOn hinj, Finset.card_powerset]

private theorem eight_le_ncard_spSignedGroup_three {n : ℕ} (hn : n = 3)
    (a : Fin n → Multiplicative (ZMod 3))
    (h2 : ∃ i j : Fin n, i ≠ j ∧ a i ≠ 1 ∧ a j ≠ 1) :
    8 ≤ Set.ncard ((fun h : Equiv.Perm (Fin n → Multiplicative (ZMod 3)) => h a) ''
      (spSignedGroup n 3 : Set (Equiv.Perm (Fin n → Multiplicative (ZMod 3))))) := by
  subst hn
  classical
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  have hsub2 : ({i, j} : Finset (Fin 3)) ⊆ supp3 a := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hge2 : 2 ≤ (supp3 a).card := by
    have := Finset.card_le_card hsub2
    rwa [Finset.card_pair hij] at this
  have hle3 : (supp3 a).card ≤ 3 := by
    have := Finset.card_le_univ (supp3 a)
    simpa using this
  rcases (show (supp3 a).card = 2 ∨ (supp3 a).card = 3 by omega) with hc2 | hc3
  ·
    have hne : (supp3 a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty] at hc2
      simp at hc2
    obtain ⟨j₀, hj₀mem⟩ := hne
    have hj₀ : a j₀ ≠ 1 := (Finset.mem_filter.mp hj₀mem).2
    obtain ⟨l, -, hl⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := supp3 a) (t := Finset.univ) (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hal : a l = 1 := by
      by_contra h
      exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    have hlj₀ : j₀ ≠ l := fun h => hl (h ▸ hj₀mem)
    let σ : Equiv.Perm (Fin 3) := Equiv.swap j₀ l
    have hσl : σ.symm l = j₀ := by
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
    have hvl : (coordPerm 3 3 σ a) l ≠ 1 := by
      rw [coordPerm_apply, hσl]; exact hj₀
    have hA : (Finset.univ.powerset.image (fun T => flip3 T a)).card = 4 := by
      rw [card_image_powerset_flip3 a, hc2]; norm_num
    have hB : (Finset.univ.powerset.image (fun T => flip3 T (coordPerm 3 3 σ a))).card = 4 := by
      rw [card_image_powerset_flip3 (coordPerm 3 3 σ a)]
      have hcard : (supp3 (coordPerm 3 3 σ a)).card = (supp3 a).card := by
        have heq : supp3 (coordPerm 3 3 σ a) = (supp3 a).image σ := by
          ext t
          rw [supp3, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨-, ht⟩
            refine ⟨σ.symm t, ?_, Equiv.apply_symm_apply σ t⟩
            rw [supp3, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, by rwa [coordPerm_apply] at ht⟩
          · rintro ⟨s, hs, rfl⟩
            refine ⟨Finset.mem_univ _, ?_⟩
            rw [coordPerm_apply, Equiv.symm_apply_apply]
            exact (Finset.mem_filter.mp hs).2
        rw [heq, Finset.card_image_of_injective _ σ.injective]
      rw [hcard, hc2]; norm_num
    have hdisj : Disjoint (Finset.univ.powerset.image (fun T => flip3 T a))
        (Finset.univ.powerset.image (fun T => flip3 T (coordPerm 3 3 σ a))) := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      obtain ⟨T, -, hT⟩ := Finset.mem_image.mp hvA
      obtain ⟨T', -, hT'⟩ := Finset.mem_image.mp hvB
      have hEq : flip3 T' (coordPerm 3 3 σ a) l = flip3 T a l := by
        rw [hT', hT]
      have h1 : flip3 T a l = 1 := by
        rw [flip3_apply]
        by_cases h : l ∈ T
        · rw [if_pos h, hal, inv_one_three]
        · rw [if_neg h, hal]
      have h2 : flip3 T' (coordPerm 3 3 σ a) l ≠ 1 := by
        rw [flip3_apply]
        by_cases h : l ∈ T'
        · rw [if_pos h]
          exact fun hh => hvl (inv_eq_one.mp hh)
        · rw [if_neg h]; exact hvl
      exact h2 (hEq.trans h1)
    have hsub : (↑(Finset.univ.powerset.image (fun T => flip3 T a) ∪
        Finset.univ.powerset.image (fun T => flip3 T (coordPerm 3 3 σ a))) : Set _) ⊆
        (fun h : Equiv.Perm (Fin 3 → Multiplicative (ZMod 3)) => h a) ''
          (spSignedGroup 3 3 : Set _) := by
      intro v hv
      rw [Finset.mem_coe, Finset.mem_union] at hv
      rcases hv with hv | hv
      · obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨flip3 T, flip3_mem T, rfl⟩
      · obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp hv
        exact ⟨flip3 T * coordPerm 3 3 σ, Subgroup.mul_mem _ (flip3_mem T)
          (coordPerm_mem_spSignedGroup σ), rfl⟩
    have hcard : (Finset.univ.powerset.image (fun T => flip3 T a) ∪
        Finset.univ.powerset.image (fun T => flip3 T (coordPerm 3 3 σ a))).card = 8 := by
      rw [Finset.card_union_of_disjoint hdisj, hA, hB]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, hcard] at hle
  ·
    have hsupp_eq : supp3 a = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hc3, Fintype.card_fin]
    have hsub : (↑(Finset.univ.powerset.image (fun T => flip3 T a)) : Set _) ⊆
        (fun h : Equiv.Perm (Fin 3 → Multiplicative (ZMod 3)) => h a) ''
          (spSignedGroup 3 3 : Set _) := by
      intro v hv
      obtain ⟨T, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
      exact ⟨flip3 T, flip3_mem T, rfl⟩
    have hcard : (Finset.univ.powerset.image (fun T => flip3 T a)).card = 8 := by
      rw [card_image_powerset_flip3 a, hsupp_eq, Finset.card_univ, Fintype.card_fin]
      norm_num
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, hcard] at hle

theorem single_block_of_orbit {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} (hψ : GGHalfTorusFrame Bs X (halfTorus n) ψ)
    (hn : 5 ≤ n) {b : G} (hb : b ∈ Bs) {t : SpecialLinearGroup (Fin (n + 1)) F2}
    (ht : t ∈ halfTorus n) (hbt : GGHalfActsAs X ψ b t) :
    (∃ P : Fin n, P.val % 2 = 0 ∧ t ∈ Subgroup.zpowers (omegaBlock n P)) ∨
      2 * ((n + 1) / 2) + 2 ≤ Set.ncard (GGHalfOrbit (ggAutomizer X Bs) b hb) := by
  classical
  obtain ⟨Φ, hΦ⟩ := GGHalf.exists_torusCoord n
  have hk3 : 3 ≤ (n + 1) / 2 := by omega
  let a : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) := Φ.symm ⟨t, ht⟩
  have hΦa : (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = t := by
    have h' : Φ a = ⟨t, ht⟩ := by
      change Φ (Φ.symm ⟨t, ht⟩) = ⟨t, ht⟩
      exact MulEquiv.apply_symm_apply Φ ⟨t, ht⟩
    exact congrArg Subtype.val h'
  let c0 : G := (ψ t)⁻¹ * b
  have htBs : ψ t ∈ Bs := hψ.torus_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hc0Bs : c0 ∈ Bs := Subgroup.mul_mem _ (Subgroup.inv_mem _ htBs) hb
  have hc0c : c0 ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hconj : c0 * l * c0⁻¹ = l := by
      have h1 : c0 * l * c0⁻¹ = (ψ t)⁻¹ * (b * l * b⁻¹) * ψ t := by
        simp only [c0]; group
      rw [h1, hbt l hl]; group
    calc l * c0 = (c0 * l * c0⁻¹) * c0 := by rw [hconj]
      _ = c0 * l := by group
  have hb_eq : b = ψ (Φ a) * c0 := by
    rw [hΦa]; simp only [c0]; group
  have horb : ∀ h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)),
      h ∈ spSignedGroup ((n + 1) / 2) 3 →
      ψ (Φ (h a)) * c0 ∈ GGHalfOrbit (ggAutomizer X Bs) b hb := by
    intro h hh
    obtain ⟨σ, hσ, hσeq⟩ := GGHalfTorusFrame.exists_aut_signed hψ Φ hΦ h hh
    refine ⟨σ, hσ, ?_⟩
    have hmem : ψ (Φ a) * c0 ∈ Bs := hb_eq ▸ hb
    have hsub : (⟨b, hb⟩ : ↥Bs) = ⟨ψ (Φ a) * c0, hmem⟩ := Subtype.ext hb_eq
    rw [hsub]
    exact hσeq a c0 hmem hc0c
  have hf_inj : Function.Injective (fun v : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) =>
      ψ (Φ v) * c0) := by
    intro v v' hv
    have h1 : ψ (Φ v) = ψ (Φ v') := mul_right_cancel hv
    have h2 : Φ v = Φ v' := Subtype.coe_injective (hψ.inj h1)
    exact Φ.injective h2
  have hncard : Set.ncard ((fun h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) =>
        h a) '' (spSignedGroup ((n + 1) / 2) 3 : Set _)) ≤
      Set.ncard (GGHalfOrbit (ggAutomizer X Bs) b hb) := by
    have hsubset : (fun v : Fin ((n + 1) / 2) → Multiplicative (ZMod 3) =>
          ψ (Φ v) * c0) ''
        ((fun h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) => h a) ''
          (spSignedGroup ((n + 1) / 2) 3 : Set _)) ⊆
          GGHalfOrbit (ggAutomizer X Bs) b hb := by
      rintro z ⟨v, ⟨h, hh, rfl⟩, rfl⟩
      exact horb h hh
    have hinj := Set.ncard_image_of_injective
      ((fun h : Equiv.Perm (Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) => h a) ''
        (spSignedGroup ((n + 1) / 2) 3 : Set _)) hf_inj
    have hle := Set.ncard_le_ncard hsubset (Set.toFinite _)
    rwa [hinj] at hle
  by_cases htwo : ∃ i j : Fin ((n + 1) / 2), i ≠ j ∧ a i ≠ 1 ∧ a j ≠ 1
  · right
    rcases htwo with ⟨i, j, hij, hi, hj⟩
    by_cases hk4 : 4 ≤ (n + 1) / 2
    · have hbig := two_mul_add_two_lt_ncard_image (H := spSignedGroup ((n + 1) / 2) 3)
        Nat.prime_three (by norm_num) hk4
        (fun σ => coordPerm_mem_spSignedGroup σ)
        (fun i => coordInv_mem_spSignedGroup i) hij hi hj
      exact le_of_lt (lt_of_lt_of_le hbig hncard)
    · have hk3eq : (n + 1) / 2 = 3 := by omega
      have hbig := eight_le_ncard_spSignedGroup_three hk3eq a ⟨i, j, hij, hi, hj⟩
      have h8 : 2 * ((n + 1) / 2) + 2 = 8 := by omega
      rw [h8]
      exact le_trans hbig hncard
  · left
    have hatmost : ∀ i j : Fin ((n + 1) / 2), i ≠ j → a i = 1 ∨ a j = 1 := by
      intro i j hij
      by_contra h
      rw [not_or] at h
      exact htwo ⟨i, j, hij, h.1, h.2⟩
    by_cases ha1 : a = 1
    · refine ⟨⟨0, by omega⟩, by norm_num, ?_⟩
      have ht1 : t = 1 := by
        rw [← hΦa, ha1]; simp
      subst ht1
      exact Subgroup.one_mem _
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp ha1
      simp only [Pi.one_apply] at hj
      have ha_eq : a = Pi.mulSingle j (a j) := by
        funext i
        by_cases hij : i = j
        · subst hij; simp
        · rw [Pi.mulSingle_apply, if_neg hij]
          rcases hatmost i j hij with h | h
          · exact h
          · exact absurd h hj
      have hcases : ∀ x : Multiplicative (ZMod 3), x ≠ 1 →
          x = Multiplicative.ofAdd (1 : ZMod 3) ∨
          x = (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ := by decide
      let P : Fin n := ⟨2 * j.val, two_mul_lt_of_lt_half j.isLt⟩
      refine ⟨P, by show (2 * j.val) % 2 = 0; omega, ?_⟩
      rcases hcases (a j) hj with hv | hv
      · have ht_eq : t = omegaBlock n P := by
          rw [← hΦa, ha_eq, hv]
          exact hΦ j
        rw [ht_eq]
        exact Subgroup.mem_zpowers _
      · have ht_eq : t = (omegaBlock n P)⁻¹ := by
          have hsingle_inv :
              (Pi.mulSingle j ((Multiplicative.ofAdd (1 : ZMod 3))⁻¹) :
                  Fin ((n + 1) / 2) → Multiplicative (ZMod 3)) =
                ((Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3)) :
                  Fin ((n + 1) / 2) → Multiplicative (ZMod 3)))⁻¹ := by
            ext s
            by_cases hs : s = j
            · rw [Pi.mulSingle_apply, if_pos hs, Pi.inv_apply, Pi.mulSingle_apply, if_pos hs]
            · rw [Pi.mulSingle_apply, if_neg hs, Pi.inv_apply, Pi.mulSingle_apply, if_neg hs,
                inv_one_three]
          have hm : Φ ((Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3)))⁻¹) =
              (Φ (Pi.mulSingle j (Multiplicative.ofAdd (1 : ZMod 3))))⁻¹ :=
            MulEquiv.map_inv Φ _
          rw [← hΦa, ha_eq, hv, hsingle_inv]
          rw [hm, Subgroup.coe_inv, hΦ j]
        rw [ht_eq]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)

end GGHalfTorusFrame

end CFSG.StandardType

end
