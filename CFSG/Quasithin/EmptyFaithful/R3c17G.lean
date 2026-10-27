module

public import CFSG.Quasithin.EmptyFaithful.R3c17B
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6ResidualG2
public import CFSG.LieType.Chevalley.RankOneCentralImage

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.QuasithinUnique.K1
  CFSG.Quasithin.R3c16
open scoped commutatorElement Pointwise

theorem g2_height_le_five {α : Fin Tag.G2.rank → ℤ}
    (hα : IsRoot Tag.G2 α) : height α ≤ 5 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hα
  have h : (List.range Tag.G2.rootCertificate.roots.length).all fun k =>
      decide (height (Tag.G2.rootCertificate.root k) ≤ 5) := by decide
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

section G2

variable {K : Type} [Field K] [Finite K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem g2_center_xc
    (hK : 4 ≤ Nat.card K) {z : ModGL Tag.G2 K} (hz : z ∈ posUnipotent Tag.G2 K)
    (hzc : ∀ q ∈ posUnipotent Tag.G2 K, q * z = z * q) : ∃ F : K, z = X g2c F := by
  classical
  obtain ⟨A, B, C, D, E, F, hzN⟩ := exists_g2N_of_mem_posUnipotent hz
  have hconj : ∀ (α : Fin Tag.G2.rank → ℤ) (s : K), X α s ∈ posUnipotent Tag.G2 K →
      X α s * z * X α s = z := by
    intro α s hαU
    have h := hzc _ hαU
    calc X α s * z * X α s = z * X α s * X α s := by rw [h]
      _ = z := by rw [mul_assoc, pinnedX_mul_self, mul_one]
  have hr : ∀ s : K, X g2r s * g2N A B C D E F * X g2r s = g2N A B C D E F := fun s => by
    have := hconj g2r s (by rw [pinnedX_r_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _)
    rwa [← hzN] at this
  have ha : ∀ s : K, X g2a s * g2N A B C D E F * X g2a s = g2N A B C D E F := fun s => by
    have := hconj g2a s (by rw [pinnedX_a_eq_g2N]; exact g2N_mem_posUnipotent _ _ _ _ _ _)
    rwa [← hzN] at this
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := g2N_center hK hr ha
  exact ⟨F, by rw [← hzN, pinnedX_c_eq_g2N]⟩

theorem height_g2c : height g2c = 5 := by decide

omit [Finite K] [CharP K 2] in
theorem commute_pinnedX_g2c
    {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β) (hβp : 0 < height β) (a b : K) :
    Commute (X β a) (X g2c b) := by
  by_cases hβc : β = g2c
  · subst hβc
    rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]
  · refine CFSG.LieType.Ree.commute_pinnedX_of_not_isRoot K hβ isRoot_g2c hβp
      (by rw [height_g2c]; norm_num) hβc (fun a' b' ha' hb' hroot => ?_) a b
    have h1 := g2_height_le_five hroot
    rw [height_nsmul_add_nsmul, height_g2c] at h1
    have ha'' : (1 : ℤ) ≤ a' := by exact_mod_cast ha'
    have hb'' : (1 : ℤ) ≤ b' := by exact_mod_cast hb'
    nlinarith

omit [Finite K] [CharP K 2] in
theorem g2_xc_central
    {u : ModGL Tag.G2 K} (hu : u ∈ posUnipotent Tag.G2 K) (F : K) : u * X g2c F = X g2c F * u := by
  have hle : posUnipotent Tag.G2 K ≤ Subgroup.centralizer {X g2c F} := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_pinnedX_g2c hβ.1 hβ.2 a F).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)

omit [Finite K] in
theorem g2_xb_eq_xc
    {d : K} (h : X g2b d = X g2c d) : d = 0 := by
  have hUa : X g2a 1 ∈ posUnipotent Tag.G2 K := by
    rw [pinnedX_a_eq_g2N]
    exact g2N_mem_posUnipotent _ _ _ _ _ _
  have h1 : ⁅X g2a 1, X g2b d⁆ = X g2c (1 * d) := comm_a_b 1 d
  have h2 : X g2a 1 * X g2b d = X g2b d * X g2a 1 := by
    rw [h]
    exact g2_xc_central hUa d
  have h3 : ⁅X g2a 1, X g2b d⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h2
  rw [h3, one_mul] at h1
  have h4 : X g2c d = X g2c 0 := by rw [← h1, pinnedX_zero]
  exact pinnedX_injective Tag.G2 K g2c h4

omit [Finite K] in
theorem g2_n_short_conj
    (x : K) : weylElt Tag.G2 K g2ir 1 * X g2c x * (weylElt Tag.G2 K g2ir 1)⁻¹ = X g2c x := by
  rw [weylElt_conj g2ir isRoot_g2c x, reflect_r_c]

omit [Finite K] in
theorem g2_n_long_conj
    (x : K) : weylElt Tag.G2 K g2ia 1 * X g2c x * (weylElt Tag.G2 K g2ia 1)⁻¹ = X g2b x := by
  rw [weylElt_conj g2ia isRoot_g2c x, reflect_a_c]

omit [CharP K 2] in
theorem g2_overgroup_shape
    (hK : 4 ≤ Nat.card K) {M : Subgroup (ModGL Tag.G2 K)}
    (hMC : M ≤ adjointGroup Tag.G2 K) (hUM : posUnipotent Tag.G2 K ≤ M)
    (hMne : M ≠ adjointGroup Tag.G2 K) :
    M ≤ torusGroup Tag.G2 K ⊔ posUnipotent Tag.G2 K ∨
      ∃ (i : Fin Tag.G2.rank) (L : Subgroup (ModGL Tag.G2 K)), Group.IsPerfect ↥L ∧ L ≤ M ∧
        posWeylGroup Tag.G2 K i = posUnipotent Tag.G2 K ⊔ L ∧ posWeylGroup Tag.G2 K i ≤ M ∧
        M ≤ torusGroup Tag.G2 K ⊔ posWeylGroup Tag.G2 K i ∧ weylElt Tag.G2 K i 1 ∈ L := by
  classical
  obtain ⟨hle, hiff, -⟩ := chevalley_positive_root_overgroup_parabolic_containment hMC hUM
  set J : Set (Fin Tag.G2.rank) := {k | weylElt Tag.G2 K k 1 ∈ M} with hJ
  by_cases hJe : J = ∅
  · left
    rw [hJe, parabolicSubgroup_empty] at hle
    exact hle
  · right
    obtain ⟨i₀, hi₀⟩ := Set.nonempty_iff_ne_empty.2 hJe
    have hJsub : J ⊆ {i₀} := by
      intro k hk
      by_contra hne
      apply hMne
      apply hiff.1
      refine Set.eq_univ_of_forall fun i => ?_
      have h2 : ∀ x y z : Fin Tag.G2.rank, x ≠ y → z = x ∨ z = y := by decide
      rcases h2 k i₀ i (fun h => hne (by rw [h]; exact Set.mem_singleton _)) with rfl | rfl
      · exact hk
      · exact hi₀
    have hMP : M ≤ torusGroup Tag.G2 K ⊔ posWeylGroup Tag.G2 K i₀ := by
      rw [← parabolicSubgroup_singleton_eq_sup]
      exact hle.trans (parabolicSubgroup_le_parabolicSubgroup_iff.2 hJsub)
    obtain ⟨ρ, hρu, hρv, hρH, hρW, hrange, -, -, -⟩ :=
      exceptional_ordinary_rank_one_central_image Tag.G2 K i₀
    have hnL : weylElt Tag.G2 K i₀ 1 ∈ ρ.range := ⟨WSL, hρW⟩
    have hperf : Group.IsPerfect ↥ρ.range := by
      have := isPerfect_SL2_of_four_le hK
      exact Group.IsPerfect.range ρ
    have hNle : posWeylGroup Tag.G2 K i₀ ≤ posUnipotent Tag.G2 K ⊔ ρ.range :=
      sup_le_sup_left ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hnL)) _
    have hLN : ρ.range ≤ posWeylGroup Tag.G2 K i₀ := by
      rw [hrange]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact posUnipotent_le_posWeylGroup i₀ (xUnit_mem_posUnipotent i₀ c)
      · exact yUnit_mem_posWeylGroup i₀ c
    have hNM : posWeylGroup Tag.G2 K i₀ ≤ M :=
      sup_le hUM ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 hi₀))
    exact ⟨i₀, ρ.range, hperf, hLN.trans hNM,
      le_antisymm hNle (sup_le (posUnipotent_le_posWeylGroup i₀) hLN), hNM, hMP, hnL⟩

omit [Finite K] [CharP K 2] in
theorem g2_scalar_of_sup
    {W : Subgroup (ModGL Tag.G2 K)}
    (hHW : torusGroup Tag.G2 K ≤ Subgroup.normalizer (W : Set (ModGL Tag.G2 K)))
    (hWc : ∀ w ∈ W, ∀ c : K, w * X g2c c = X g2c c * w) {g : ModGL Tag.G2 K}
    (hg : g ∈ torusGroup Tag.G2 K ⊔ W) :
    ∃ l : K, ∀ c : K, g * X g2c c * g⁻¹ = X g2c (l * c) := by
  have hg' : g ∈ (torusGroup Tag.G2 K : Set (ModGL Tag.G2 K)) * (W : Set (ModGL Tag.G2 K)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hHW]
    exact hg
  obtain ⟨h, hh, w, hw, rfl⟩ := hg'
  obtain ⟨l, hl⟩ := torus_conj_scalar (τ := Tag.G2) (K := K) isRoot_g2c hh
  refine ⟨l, fun c => ?_⟩
  have hwc : w * X g2c c * w⁻¹ = X g2c c := by
    rw [hWc w hw c]
    group
  have e : h * w * X g2c c * (h * w)⁻¹ = h * (w * X g2c c * w⁻¹) * h⁻¹ := by group
  rw [e, hwc]
  exact hl c

theorem g2_core
    (hK : 4 ≤ Nat.card K) {V M : Subgroup (ModGL Tag.G2 K)}
    (hVU : V ≤ posUnipotent Tag.G2 K) (hV4 : Nat.card V = 4)
    (hMC : M ≤ adjointGroup Tag.G2 K) (hUM : posUnipotent Tag.G2 K ≤ M)
    (hMne : M ≠ adjointGroup Tag.G2 K) (hMV : M ≤ Subgroup.normalizer (V : Set (ModGL Tag.G2 K)))
    {y : ModGL Tag.G2 K} (hyM : y ∈ M) {k : ℕ} (hk : y ^ (3 ^ k) = 1)
    (hyn : ¬ ∀ v ∈ V, y * v = v * y) :
    (∀ u ∈ posUnipotent Tag.G2 K, ∀ v ∈ V, u * v = v * u) ∧
    ∀ g ∈ M, ∃ l : K, ∀ c : K, g * X g2c c * g⁻¹ = X g2c (l * c) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hU2 : IsPGroup 2 ↥(posUnipotent Tag.G2 K) :=
    (unique_Chevalley_positive_Sylow (τ := Tag.G2) (K := K) 2).1.isPGroup
  have hHU : torusGroup Tag.G2 K ≤
      Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
    torusGroup_le_normalizer_posUnipotent (τ := Tag.G2) (R := K)
  have hUc : ∀ u ∈ posUnipotent Tag.G2 K, ∀ c : K, u * X g2c c = X g2c c * u :=
    fun u hu c => g2_xc_central hu c
  rcases g2_overgroup_shape hK hMC hUM hMne with hB | ⟨i, L, hLperf, hLM, hNL, hNM, hMP, hnL⟩
  ·
    have hWn : ∀ m ∈ M, ∀ w ∈ posUnipotent Tag.G2 K, m * w * m⁻¹ ∈ posUnipotent Tag.G2 K := by
      intro m hm w hw
      have hm' : m ∈ Subgroup.normalizer (posUnipotent Tag.G2 K : Set (ModGL Tag.G2 K)) :=
        (sup_le hHU Subgroup.le_normalizer) (hB hm)
      exact (Subgroup.mem_normalizer_iff.1 hm' w).1 hw
    have ha := two_group_trivial_action hMV hV4 hU2 le_rfl hUM hWn
      (fun w hw => ⟨w, hw, fun v _ => rfl⟩) hyM hk hyn
    exact ⟨ha, fun g hg => g2_scalar_of_sup hHU hUc (hB hg)⟩
  ·
    have hHN : torusGroup Tag.G2 K ≤
        Subgroup.normalizer (posWeylGroup Tag.G2 K i : Set (ModGL Tag.G2 K)) :=
      torusGroup_le_normalizer_posWeylGroup i
    have hWn : ∀ m ∈ M, ∀ w ∈ posWeylGroup Tag.G2 K i, m * w * m⁻¹ ∈ posWeylGroup Tag.G2 K i := by
      intro m hm w hw
      have hm' : m ∈ Subgroup.normalizer (posWeylGroup Tag.G2 K i : Set (ModGL Tag.G2 K)) :=
        (sup_le hHN Subgroup.le_normalizer) (hMP hm)
      exact (Subgroup.mem_normalizer_iff.1 hm' w).1 hw
    have hW : ∀ w ∈ posWeylGroup Tag.G2 K i, ∃ u ∈ posUnipotent Tag.G2 K, ∀ v ∈ V,
        w * v * w⁻¹ = u * v * u⁻¹ := fun w hw =>
      act_eq_of_mem_sup_perfect hMV hV4 hUM hLM hLperf (hNL ▸ hw)
    have ha := two_group_trivial_action hMV hV4 hU2 (posUnipotent_le_posWeylGroup i) hNM hWn hW
      hyM hk hyn
    refine ⟨ha, ?_⟩
    have hcases : ∀ a : Fin Tag.G2.rank, a = g2ia ∨ a = g2ir := by decide
    rcases hcases i with rfl | rfl
    ·
      exfalso
      obtain ⟨v, hv, hv1⟩ : ∃ v ∈ V, v ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : V = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
        rw [this, Subgroup.card_bot] at hV4
        omega
      obtain ⟨d, hd⟩ := g2_center_xc hK (hVU hv) (fun q hq => ha q hq v hv)
      have hd0 : d ≠ 0 := by
        intro h0
        apply hv1
        rw [hd, h0]
        exact pinnedX_zero _ _ _
      have hnv : weylElt Tag.G2 K g2ia 1 * v * (weylElt Tag.G2 K g2ia 1)⁻¹ = v := by
        obtain ⟨u, hu, hu'⟩ := act_eq_of_mem_sup_perfect (U := ⊥) hMV hV4 bot_le hLM hLperf
          (w := weylElt Tag.G2 K g2ia 1) (by rw [bot_sup_eq]; exact hnL)
        rw [hu' v hv, Subgroup.mem_bot.1 hu]
        group
      rw [hd, g2_n_long_conj d] at hnv
      exact hd0 (g2_xb_eq_xc hnv)
    ·
      have hWc : ∀ w ∈ posWeylGroup Tag.G2 K g2ir, ∀ c : K,
          w * X g2c c = X g2c c * w := by
        intro w hw c
        have hle : posWeylGroup Tag.G2 K g2ir ≤ Subgroup.centralizer {X g2c c} := by
          refine sup_le (fun u hu => ?_) ((Subgroup.closure_le _).2 ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.2 (hUc u hu c)
          · rintro _ rfl
            refine Subgroup.mem_centralizer_singleton_iff.2 ?_
            have h1 := g2_n_short_conj (K := K) c
            calc weylElt Tag.G2 K g2ir 1 * X g2c c =
                (weylElt Tag.G2 K g2ir 1 * X g2c c * (weylElt Tag.G2 K g2ir 1)⁻¹) *
                  weylElt Tag.G2 K g2ir 1 := by group
              _ = X g2c c * weylElt Tag.G2 K g2ir 1 := by rw [h1]
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
      exact fun g hg => g2_scalar_of_sup hHN hWc (hMP hg)

end G2

end CFSG.Quasithin.R3c17
