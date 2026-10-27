module

public import CFSG.Milestones.ASVolI.F4K.F415
public import CFSG.Milestones.ASVolI.F4K.G2d
public import CFSG.Milestones.ASVolI.F4K.Grp
public import CFSG.Milestones.ASVolI.F4K.Poly
public import CFSG.Milestones.ASVolI.F4Native

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF
open scoped Pointwise

section Generic

theorem burnsideF4nA_exists_fixed {X : Type*} {Λ : Set X} (hΛ : Nat.card Λ = 5) (σ : X → X)
    (hσΛ : ∀ r ∈ Λ, σ r ∈ Λ) (hσσ : ∀ r ∈ Λ, σ (σ r) = r) : ∃ r ∈ Λ, σ r = r := by
  have hfin : Finite Λ := Nat.finite_of_card_ne_zero (by rw [hΛ]; norm_num)
  letI : Fintype Λ := Fintype.ofFinite Λ
  let e : Equiv.Perm Λ :=
    { toFun := fun r => ⟨σ r, hσΛ r r.2⟩
      invFun := fun r => ⟨σ r, hσΛ r r.2⟩
      left_inv := fun r => Subtype.ext (hσσ r r.2)
      right_inv := fun r => Subtype.ext (hσσ r r.2) }
  have he : e ^ 2 ^ 1 = 1 := by
    ext r
    show σ (σ r) = r
    exact hσσ r r.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : ¬ 2 ∣ Fintype.card Λ := by
    rw [← Nat.card_eq_fintype_card, hΛ]
    norm_num
  obtain ⟨r, hr⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard he
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

theorem burnsideF4nA_rot_pow {V H : Type*} [Group H] [MulAction H V] {n : ℕ} (f : ZMod n → V)
    {s₁ s₂ : H} {a b : ZMod n} (h₁ : ∀ t, s₁ • f t = f (a - t)) (h₂ : ∀ t, s₂ • f t = f (b - t))
    (k : ℕ) (t : ZMod n) : (s₁ * s₂) ^ k • f t = f (t + k * (a - b)) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_smul, mul_smul, h₂, h₁, ih]
    congr 1
    push_cast
    ring

theorem burnsideF4nA_orderOf_eq {V H : Type*} [Group H] [MulAction H V] {n N : ℕ} (hN : 0 < N)
    {f : ZMod n → V} (hf : Function.Injective f) {s₁ s₂ : H} {a b : ZMod n}
    (h₁ : ∀ t, s₁ • f t = f (a - t)) (h₂ : ∀ t, s₂ • f t = f (b - t))
    (hK : ∀ w : H, (∀ t, w • f t = f t) → w = 1) (hNz : (N : ZMod n) * (a - b) = 0)
    (hlt : ∀ k : ℕ, 0 < k → k < N → (k : ZMod n) * (a - b) ≠ 0) :
    orderOf (s₁ * s₂) = N := by
  rw [orderOf_eq_iff hN]
  refine ⟨hK _ fun t => ?_, fun k hk hk0 h => ?_⟩
  · rw [burnsideF4nA_rot_pow f h₁ h₂, hNz, add_zero]
  · have h' := burnsideF4nA_rot_pow f h₁ h₂ k 0
    rw [h, one_smul, zero_add] at h'
    exact hlt k hk0 hk (hf h').symm

end Generic

section Poly

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] {c : α.Completion Z}

theorem burnsideF4nA_swap_apply (z : ℕ → c.Γ) (hz : ∀ i, c.graph.Adj (z i) (z (i + 1))) {m : ℕ}
    (hm : 1 ≤ m) (hper : ∀ i, z (i + 2 * m) = z i) (i : ℕ) {g : c.G0}
    (h1 : g • GPath.arc₁ z hz m i = GPath.arc₂ z hz m i)
    (h2 : g • GPath.arc₂ z hz m i = GPath.arc₁ z hz m i) :
    g • z i = z i ∧ g • z (i + m) = z (i + m) ∧ g • z (i + 1) = z (i + 2 * m - 1) ∧
      g • z (i + 2 * m - 1) = z (i + 1) := by
  have e1 := GPath.smul_eq_iff.mp h1
  have e2 := GPath.smul_eq_iff.mp h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e1 0 (Nat.zero_le m)
    rwa [GPath.arc₁_zero, GPath.arc₂_zero z hz m hper] at this
  · have := e1 m le_rfl
    rwa [GPath.arc₁_last, GPath.arc₂_last] at this
  · have := e1 1 hm
    rwa [GPath.arc₁_one z hz m hm, GPath.arc₂_one z hz m hm] at this
  · have := e2 1 hm
    rwa [GPath.arc₁_one z hz m hm, GPath.arc₂_one z hz m hm] at this

theorem burnsideF4nA_eq_of_agree {m : ℕ} (hm : 2 ≤ m) {S : Set c.Γ} (hS : c.IsApartment m S)
    (hK : ∀ g : c.G0, (∀ v ∈ S, g • v = v) → g = 1) {s s' : c.G0} (hs : s ∈ setStab c S)
    (hs' : s' ∈ setStab c S) {u v : c.Γ} (hu : u ∈ S) (hv : v ∈ S) (huv : c.graph.Adj u v)
    (h1 : s • u = u) (h1' : s' • u = u) (h2 : s • v = s' • v) : s = s' := by
  obtain ⟨φ⟩ := hS
  have hg : s⁻¹ * s' ∈ setStab c S := mul_mem (inv_mem hs) hs'
  have hgu : (s⁻¹ * s') • u = u := by rw [mul_smul, h1', inv_smul_eq_iff, h1]
  have hgv : (s⁻¹ * s') • v = v := by rw [mul_smul, ← h2, inv_smul_smul]
  have hall := burnsideF4k_polygon_fix_adj (by omega : 3 ≤ 2 * m) φ (s⁻¹ * s')
    (fun w hw => burnsideF4k_setStab_mem c hg hw) hu hv huv hgu hgv
  exact inv_mul_eq_one.mp (hK _ hall)

theorem burnsideF4nA_orbit_eq (H : Subgroup c.G0) (u : c.Γ) :
    MulAction.orbit (↥H) u = {v | ∃ w ∈ H, w • u = v} := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, w.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩

theorem burnsideF4nA_smul_mem_SigmaST (κ : GLKind) (cc : c.Γ) {s t w : c.G0}
    (hw : w ∈ Subgroup.closure {s, t}) {u : c.Γ} (hu : u ∈ SigmaST c κ cc s t) :
    w • u ∈ SigmaST c κ cc s t := by
  rcases hu with (⟨w', hw', rfl⟩ | ⟨w', hw', rfl⟩) | hu
  · exact Or.inl (Or.inl ⟨w * w', mul_mem hw hw', mul_smul w w' _⟩)
  · exact Or.inl (Or.inr ⟨w * w', mul_mem hw hw', mul_smul w w' _⟩)
  · right
    by_cases h : κ = GLKind.G2d
    · rw [if_pos h] at hu ⊢
      obtain ⟨w', hw', rfl⟩ := hu
      exact ⟨w * w', mul_mem hw hw', mul_smul w w' _⟩
    · rw [if_neg h] at hu
      exact hu.elim

theorem burnsideF4nA_mem_setStab_SigmaST (κ : GLKind) (cc : c.Γ) {s t w : c.G0}
    (hw : w ∈ Subgroup.closure {s, t}) : w ∈ setStab c (SigmaST c κ cc s t) := by
  rw [setStab, MulAction.mem_stabilizer_iff]
  ext v
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact burnsideF4nA_smul_mem_SigmaST κ cc hw hu
  · intro hv
    exact ⟨w⁻¹ • v, burnsideF4nA_smul_mem_SigmaST κ cc (inv_mem hw) hv, smul_inv_smul w v⟩

theorem burnsideF4nA_mem_closure_left (s t : c.G0) : s ∈ Subgroup.closure {s, t} :=
  Subgroup.subset_closure (Set.mem_insert s {t})

theorem burnsideF4nA_mem_closure_right (s t : c.G0) : t ∈ Subgroup.closure {s, t} :=
  Subgroup.subset_closure (Set.mem_insert_of_mem s rfl)

end Poly

section MapsTo

variable {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] {c : α.Completion Z}

theorem burnsideF4nA_mem_G1 {g : c.G0} (h : g • c.xv = c.xv) : (g : Z) ∈ c.φ1.range := by
  have := CosetGeom.mem_stab_of_smul_eq h
  rwa [CosetGeom.stab_γ₀ (le_sup_left : c.φ1.range ≤ c.φ1.range ⊔ c.φ2.range)] at this

theorem burnsideF4nA_mem_G2 {g : c.G0} (h : g • c.lv = c.lv) : (g : Z) ∈ c.φ2.range := by
  have := CosetGeom.mem_stab_of_smul_eq h
  rwa [CosetGeom.stab_γ₁ (le_sup_right : c.φ2.range ≤ c.φ1.range ⊔ c.φ2.range)] at this

theorem burnsideF4nA_fix_xv {g : c.G0} (h : (g : Z) ∈ c.φ1.range) : g • c.xv = c.xv :=
  CosetGeom.smul_eq_of_mem_stab (by
    rw [CosetGeom.stab_γ₀ (le_sup_left : c.φ1.range ≤ c.φ1.range ⊔ c.φ2.range)]; exact h)

theorem burnsideF4nA_fix_lv {g : c.G0} (h : (g : Z) ∈ c.φ2.range) : g • c.lv = c.lv :=
  CosetGeom.smul_eq_of_mem_stab (by
    rw [CosetGeom.stab_γ₁ (le_sup_right : c.φ2.range ≤ c.φ1.range ⊔ c.φ2.range)]; exact h)

theorem burnsideF4nA_maps_tits (hU : UniqueGeod c.graph 8) {cc y y' : c.Γ} {s t : c.G0}
    (hs : s ∈ N1set c GLKind.Tits cc y) (ht : t ∈ N2set c GLKind.Tits cc y y')
    (hst : orderOf (s * t) = 8) :
    SigmaST c GLKind.Tits cc s t ∈ Bset c GLKind.Tits cc y y' := by
  rw [N1set, if_pos rfl] at hs
  rw [N2set, if_pos rfl] at ht
  obtain ⟨hsx, ⟨hss, hlc, hsl, -⟩, -⟩ := hs
  obtain ⟨htl, ⟨htt, hxy, htx, -⟩⟩ := ht
  have hsx' : s • c.xv = c.xv := MulAction.mem_stabilizer_iff.mp hsx
  have htl' : t • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp htl
  have hs12 : (s : Z) ∉ c.φ1.range ⊓ c.φ2.range := fun h =>
    hlc ((burnsideF4nA_fix_lv h.2).symm.trans hsl)
  have ht12 : (t : Z) ∉ c.φ1.range ⊓ c.φ2.range := fun h =>
    hxy ((burnsideF4nA_fix_xv h.1).symm.trans htx)
  have h8 : (((s * t) ^ 8 : c.G0) : Z) ∈ c.φ1.range ⊓ c.φ2.range := by
    rw [← hst, pow_orderOf_eq_one]
    exact Subgroup.one_mem _
  obtain ⟨-, hpoly, -, -⟩ := CosetGeom.lemma_F36 (m := 8) (by norm_num) hU hss htt
    (burnsideF4nA_mem_G1 hsx') hs12 (burnsideF4nA_mem_G2 htl') ht12 (n := 8) (by norm_num) le_rfl h8
  have heq : SigmaST c GLKind.Tits cc s t =
      MulAction.orbit (↥(Subgroup.closure {s, t})) c.xv ∪
        MulAction.orbit (↥(Subgroup.closure {s, t})) c.lv := by
    rw [SigmaST, if_neg (by decide), Set.union_empty, burnsideF4nA_orbit_eq, burnsideF4nA_orbit_eq]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hpoly
  · rw [if_pos rfl]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inr ⟨s, burnsideF4nA_mem_closure_left s t, hsl⟩)
    · exact Or.inl (Or.inl ⟨1, Subgroup.one_mem _, one_smul _ _⟩)
    · exact Or.inl (Or.inr ⟨1, Subgroup.one_mem _, one_smul _ _⟩)
    · exact Or.inl (Or.inl ⟨t, burnsideF4nA_mem_closure_right s t, htx⟩)

theorem burnsideF4nA_maps_g2d (hU : UniqueGeod c.graph 6) {cc y y' : c.Γ}
    (hcc : cc ∈ CosetGeom.nbrs c.xv) (hccl : cc ≠ c.lv) {s t : c.G0}
    (hs : s ∈ N1set c GLKind.G2d cc y) (ht : t ∈ N2set c GLKind.G2d cc y y')
    (hst : orderOf (s * t) = 3) :
    SigmaST c GLKind.G2d cc s t ∈ Bset c GLKind.G2d cc y y' := by
  rw [N1set, if_neg (by decide)] at hs
  rw [N2set, if_neg (by decide)] at ht
  obtain ⟨hsl, ⟨hss, hxy, hsx, -⟩⟩ := hs
  obtain ⟨htc, ⟨htt, hxy', htx, -⟩⟩ := ht
  have hsl' : s • c.lv = c.lv := MulAction.mem_stabilizer_iff.mp hsl
  have htc' : t • cc = cc := MulAction.mem_stabilizer_iff.mp htc
  have hs12 : (s : Z) ∉ c.φ1.range ⊓ c.φ2.range := fun h =>
    hxy ((burnsideF4nA_fix_xv h.1).symm.trans hsx)
  have htxc : (t : Z) ∉ c.φ1.range ⊓ CosetGeom.stab cc := fun h =>
    hxy' ((burnsideF4nA_fix_xv h.1).symm.trans htx)
  have h3 : (((t * s) ^ 3 : c.G0) : Z) ∈ c.φ1.range ⊓ c.φ2.range ⊓ CosetGeom.stab cc := by
    have e : t * s = (s * t)⁻¹ := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hss, inv_eq_of_mul_eq_one_left htt]
    rw [e, inv_pow, ← hst, pow_orderOf_eq_one, inv_one]
    exact Subgroup.one_mem _
  obtain ⟨-, hpoly, -, -⟩ := CosetGeom.lemma_F37 (m := 6) (by norm_num) (by decide) hU hcc hccl htt
    hss (CosetGeom.mem_stab_of_smul_eq htc') htxc (burnsideF4nA_mem_G2 hsl') hs12 (n := 3)
    (by norm_num) (by norm_num) h3
  have hcl : Subgroup.closure ({t, s} : Set c.G0) = Subgroup.closure {s, t} := by
    rw [Set.pair_comm]
  have heq : SigmaST c GLKind.G2d cc s t =
      MulAction.orbit (↥(Subgroup.closure {t, s})) c.xv ∪
        MulAction.orbit (↥(Subgroup.closure {t, s})) c.lv ∪
        MulAction.orbit (↥(Subgroup.closure {t, s})) cc := by
    rw [SigmaST, if_pos rfl, burnsideF4nA_orbit_eq, burnsideF4nA_orbit_eq, burnsideF4nA_orbit_eq,
      hcl]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact hpoly
  · rw [if_neg (by decide)]
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (Or.inl ⟨t, burnsideF4nA_mem_closure_right s t, htx⟩)
    · refine Or.inr ?_
      rw [if_pos rfl]
      exact ⟨1, Subgroup.one_mem _, one_smul _ _⟩
    · exact Or.inl (Or.inl ⟨1, Subgroup.one_mem _, one_smul _ _⟩)
    · exact Or.inl (Or.inr ⟨1, Subgroup.one_mem _, one_smul _ _⟩)
    · exact Or.inl (Or.inl ⟨s, burnsideF4nA_mem_closure_left s t, hsx⟩)

end MapsTo

section Kernel

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4nA_F415 (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal) :
    F_4_15 :=
  burnsideF4k_F415_of burnsideF4k_polyArcs burnsideF4k_polyRefl burnsideF4k_polyW
    burnsideF4k_polyOpp burnsideF4k_polyNbr burnsideF4k_polyG2d burnsideF4k_grpD10
    burnsideF4k_grpZ3 burnsideF4k_grpTwoTrans hF h5 hcompat

theorem burnsideF4nA_free_g2d (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hGp : Gp = ⊤) (hκ : κ = .G2d) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) {cc : β.Γ}
    (hcc : cc ∈ CosetGeom.nbrs β.xv) (hccl : cc ≠ β.lv) {S : Set β.Γ}
    (hS : β.IsApartment κ.m S) (hx : β.xv ∈ S) (hl : β.lv ∈ S) (hccS : cc ∈ S) {g : β.G0}
    (hg : g ∈ setStab β S) (hgx : g • β.xv = β.xv) : g = 1 := by
  obtain ⟨-, -, -, h4⟩ := burnsideF4nA_F415 hF h5 hcompat κ p f E Gp M₁ M₂ hyp Y β hβ hs
  obtain ⟨sl, sc, -, -, -, -, -, -, -, hreg, -⟩ := h4 ⟨hGp, hκ⟩ S hS hx hl cc hcc hccS hccl
  obtain ⟨w, -, hw⟩ := hreg β.xv hx rfl β.xv hx rfl
  have e1 := hw ⟨g, hg⟩ hgx
  have e2 := hw ⟨1, Subgroup.one_mem _⟩ (one_smul _ _)
  exact congrArg Subtype.val (e1.trans e2.symm)

theorem burnsideF4nA_K_tits (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hκ : κ = .Tits) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) {S : Set β.Γ} (hS : β.IsApartment κ.m S)
    (hx : β.xv ∈ S) (hl : β.lv ∈ S) {g : β.G0} (hg : ∀ v ∈ S, g • v = v) : g = 1 := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  obtain ⟨z, hz, hnb, hper, rfl, hz0, -⟩ :=
    burnsideF4k_asm_label F.hm F.uniqueGeod hS hx hl CosetGeom.adj_γ₀_γ₁
  exact burnsideF4k_asm_tits_K burnsideF4k_polyArcs burnsideF4k_grpD10 burnsideF4k_grpTwoTrans hF h5
    hcompat hyp hκ β hβ hs z hz hnb hper hz0 g hg

theorem burnsideF4nA_K (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hGp : Gp = ⊤) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type}
    [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall κ.m) {cc : β.Γ}
    (hcc : cc ∈ CosetGeom.nbrs β.xv) (hccl : cc ≠ β.lv) {S : Set β.Γ}
    (hS : β.IsApartment κ.m S) (hx : β.xv ∈ S) (hl : β.lv ∈ S) (hccS : cc ∈ S) {g : β.G0}
    (hg : ∀ v ∈ S, g • v = v) : g = 1 := by
  rcases hκ with hκ | hκ
  · exact burnsideF4nA_free_g2d hF h5 hcompat hyp hGp hκ β hβ hs hcc hccl hS hx hl hccS
      (burnsideF4k_pointwiseStab_le_setStab β S ((burnsideF4k_mem_pointwiseStab β).mpr hg))
      (hg _ hx)
  · exact burnsideF4nA_K_tits hF h5 hcompat hyp hκ β hβ hs hS hx hl hg

end Kernel

section InjOn

variable {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4nA_injOn_tits (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.Tits.m) (cc y y' : β.Γ) :
    Set.InjOn (fun st : β.G0 × β.G0 => SigmaST β GLKind.Tits cc st.1 st.2)
      (Pset β GLKind.Tits cc y y') := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  rintro ⟨s, t⟩ ⟨hs1, ht1, hst⟩ ⟨s', t'⟩ ⟨hs1', ht1', hst'⟩ heq
  have heq' : SigmaST β GLKind.Tits cc s t = SigmaST β GLKind.Tits cc s' t' := heq
  rw [m0Of, if_pos rfl] at hst
  obtain ⟨hSap, hsub⟩ := burnsideF4nA_maps_tits F.uniqueGeod hs1 ht1 hst
  rw [if_pos rfl] at hsub
  have hx : β.xv ∈ SigmaST β GLKind.Tits cc s t := hsub (by simp)
  have hl : β.lv ∈ SigmaST β GLKind.Tits cc s t := hsub (by simp)
  have hK : ∀ g : β.G0, (∀ v ∈ SigmaST β GLKind.Tits cc s t, g • v = v) → g = 1 := fun g hg =>
    burnsideF4nA_K_tits hF h5 hcompat hyp rfl β hβ hs hSap hx hl hg
  have hS1 := burnsideF4nA_mem_setStab_SigmaST GLKind.Tits cc (burnsideF4nA_mem_closure_left s t)
  have hT1 := burnsideF4nA_mem_setStab_SigmaST GLKind.Tits cc (burnsideF4nA_mem_closure_right s t)
  have hS1' : s' ∈ setStab β (SigmaST β GLKind.Tits cc s t) := by
    rw [heq']
    exact burnsideF4nA_mem_setStab_SigmaST GLKind.Tits cc (burnsideF4nA_mem_closure_left s' t')
  have hT1' : t' ∈ setStab β (SigmaST β GLKind.Tits cc s t) := by
    rw [heq']
    exact burnsideF4nA_mem_setStab_SigmaST GLKind.Tits cc (burnsideF4nA_mem_closure_right s' t')
  rw [N1set, if_pos rfl] at hs1 hs1'
  rw [N2set, if_pos rfl] at ht1 ht1'
  obtain ⟨hsx, ⟨-, -, hsl, -⟩, -⟩ := hs1
  obtain ⟨hsx', ⟨-, -, hsl', -⟩, -⟩ := hs1'
  obtain ⟨htl, ⟨-, -, htx, -⟩⟩ := ht1
  obtain ⟨htl', ⟨-, -, htx', -⟩⟩ := ht1'
  have e1 : s = s' := burnsideF4nA_eq_of_agree F.hm hSap hK hS1 hS1' hx hl CosetGeom.adj_γ₀_γ₁
    (MulAction.mem_stabilizer_iff.mp hsx) (MulAction.mem_stabilizer_iff.mp hsx')
    (hsl.trans hsl'.symm)
  have e2 : t = t' := burnsideF4nA_eq_of_agree F.hm hSap hK hT1 hT1' hl hx
    CosetGeom.adj_γ₀_γ₁.symm (MulAction.mem_stabilizer_iff.mp htl)
    (MulAction.mem_stabilizer_iff.mp htl') (htx.trans htx'.symm)
  rw [e1, e2]

theorem burnsideF4nA_injOn_g2d (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 GLKind.G2d p f Gp M₁ M₂) (hGp : Gp = ⊤) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.G2d.m) {cc : β.Γ}
    (hcc : cc ∈ CosetGeom.nbrs β.xv) (hccl : cc ≠ β.lv) (y y' : β.Γ) :
    Set.InjOn (fun st : β.G0 × β.G0 => SigmaST β GLKind.G2d cc st.1 st.2)
      (Pset β GLKind.G2d cc y y') := by
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  rintro ⟨s, t⟩ ⟨hs1, ht1, hst⟩ ⟨s', t'⟩ ⟨hs1', ht1', hst'⟩ heq
  have heq' : SigmaST β GLKind.G2d cc s t = SigmaST β GLKind.G2d cc s' t' := heq
  rw [m0Of, if_neg (by decide)] at hst
  obtain ⟨hSap, hsub⟩ := burnsideF4nA_maps_g2d F.uniqueGeod hcc hccl hs1 ht1 hst
  rw [if_neg (by decide)] at hsub
  have hccS : cc ∈ SigmaST β GLKind.G2d cc s t := hsub (by simp)
  have hx : β.xv ∈ SigmaST β GLKind.G2d cc s t := hsub (by simp)
  have hl : β.lv ∈ SigmaST β GLKind.G2d cc s t := hsub (by simp)
  have hK : ∀ g : β.G0, (∀ v ∈ SigmaST β GLKind.G2d cc s t, g • v = v) → g = 1 := fun g hg =>
    burnsideF4nA_K hF h5 hcompat hyp hGp (Or.inl rfl) β hβ hs hcc hccl hSap hx hl hccS hg
  have hS1 := burnsideF4nA_mem_setStab_SigmaST GLKind.G2d cc (burnsideF4nA_mem_closure_left s t)
  have hT1 := burnsideF4nA_mem_setStab_SigmaST GLKind.G2d cc (burnsideF4nA_mem_closure_right s t)
  have hS1' : s' ∈ setStab β (SigmaST β GLKind.G2d cc s t) := by
    rw [heq']
    exact burnsideF4nA_mem_setStab_SigmaST GLKind.G2d cc (burnsideF4nA_mem_closure_left s' t')
  have hT1' : t' ∈ setStab β (SigmaST β GLKind.G2d cc s t) := by
    rw [heq']
    exact burnsideF4nA_mem_setStab_SigmaST GLKind.G2d cc (burnsideF4nA_mem_closure_right s' t')
  rw [N1set, if_neg (by decide)] at hs1 hs1'
  rw [N2set, if_neg (by decide)] at ht1 ht1'
  obtain ⟨hsl, ⟨-, -, hsx, -⟩⟩ := hs1
  obtain ⟨hsl', ⟨-, -, hsx', -⟩⟩ := hs1'
  obtain ⟨htc, ⟨-, -, htx, -⟩⟩ := ht1
  obtain ⟨htc', ⟨-, -, htx', -⟩⟩ := ht1'
  have e1 : s = s' := burnsideF4nA_eq_of_agree F.hm hSap hK hS1 hS1' hl hx
    CosetGeom.adj_γ₀_γ₁.symm (MulAction.mem_stabilizer_iff.mp hsl)
    (MulAction.mem_stabilizer_iff.mp hsl') (hsx.trans hsx'.symm)
  have e2 : t = t' := burnsideF4nA_eq_of_agree F.hm hSap hK hT1 hT1' hccS hx
    (show β.graph.Adj cc β.xv from (hcc : β.graph.Adj β.xv cc).symm)
    (MulAction.mem_stabilizer_iff.mp htc) (MulAction.mem_stabilizer_iff.mp htc')
    (htx.trans htx'.symm)
  rw [e1, e2]

end InjOn

section SurjOn

theorem burnsideF4nA_faithful_zf {α : RankTwoAmalgam.{0}} {Z : Type} [Group Z] {c : α.Completion Z}
    {z : ℕ → c.Γ} {m : ℕ} (hper : ∀ i, z (i + 2 * m) = z i)
    (hK : ∀ w : c.G0, (∀ v ∈ Set.range z, w • v = v) → w = 1) (w : c.G0)
    (hw : ∀ t, w • burnsideF4k_pa_zf z m t = burnsideF4k_pa_zf z m t) : w = 1 := by
  refine hK w ?_
  rintro v ⟨k, rfl⟩
  rw [← burnsideF4k_pa_zf_natCast hper k]
  exact hw _

variable {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4nA_tits_geod (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.Tits.m) {r : GPath β.graph GLKind.Tits.m}
    (hr : r ∈ GPath.nbPaths β.graph β.xv GLKind.Tits.m) {sx : β.G0}
    (hsx : sx ∈ stv β β.xv ⊓ stv β (r GLKind.Tits.m)) (hsx2 : sx * sx = 1) (hsx1 : sx ≠ 1) :
    ∃ q : GPath β.graph GLKind.Tits.m, q 0 = β.xv ∧ q.IsGeodesic ∧
      (q.stabPath : Subgroup β.G0) = Subgroup.zpowers sx := by
  rcases burnsideF4k_asm_point_cases burnsideF4k_grpTwoTrans hF h5 hcompat hyp (Or.inl rfl) β hβ
      hs hr with ⟨-, ⟨e⟩, htr, hc⟩ | ⟨hκG, -⟩
  · obtain ⟨q, hq, hsq⟩ := burnsideF4nA_exists_fixed hc (fun r' => sx • r')
      (fun r' hr' => burnsideF4k_geods_smul hsx hr')
      (fun r' _ => by
        show sx • sx • r' = r'
        rw [← GPath.mul_smul', hsx2, GPath.one_smul'])
    have hqm : q GLKind.Tits.m = r GLKind.Tits.m := hq.2.1
    have hq' : q ∈ β.geods GLKind.Tits.m β.xv (q GLKind.Tits.m) := by rw [hqm]; exact hq
    have htr' : ∀ q₁ ∈ β.geods GLKind.Tits.m β.xv (q GLKind.Tits.m),
        ∀ q₂ ∈ β.geods GLKind.Tits.m β.xv (q GLKind.Tits.m),
          ∃ g ∈ stv β β.xv ⊓ stv β (q GLKind.Tits.m), g • q₁ = q₂ := by
      rw [hqm]; exact htr
    have hcard := burnsideF4k_asm_card_stab_geods hq' htr'
    rw [hqm, Nat.card_congr e.toEquiv, DihedralGroup.nat_card, hc] at hcard
    have h2 : Nat.card (q.stabPath : Subgroup β.G0) = 2 := by omega
    haveI : Finite (q.stabPath : Subgroup β.G0) :=
      Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
    have hle : Subgroup.zpowers sx ≤ q.stabPath := by
      rw [Subgroup.zpowers_le]
      exact GPath.smul_eq_iff.mp hsq
    have hord : orderOf sx = 2 := orderOf_eq_prime (by rw [sq]; exact hsx2) hsx1
    refine ⟨q, hq.1, hq.2.2, (Subgroup.eq_of_le_of_card_ge hle ?_).symm⟩
    rw [h2, Nat.card_zpowers, hord]
  · exact absurd hκG (by decide)

theorem burnsideF4nA_surj_tits (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 GLKind.Tits p f Gp M₁ M₂) {Y : Type} [Group Y] (β : Cpl M₁ M₂ Y)
    (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.Tits.m) {cc y : β.Γ}
    (hcc : cc ∈ CosetGeom.nbrs β.xv) (hccl : cc ≠ β.lv) (hy : y ∈ CosetGeom.nbrs β.lv)
    (hyx : y ≠ β.xv) (y' : β.Γ) :
    Set.SurjOn (fun st : β.G0 × β.G0 => SigmaST β GLKind.Tits cc st.1 st.2)
      (Pset β GLKind.Tits cc y y') (Bset β GLKind.Tits cc y y') := by
  intro S hS
  obtain ⟨hSap, hsub⟩ := hS
  rw [if_pos rfl] at hsub
  have hccS : cc ∈ S := hsub (by simp)
  have hx : β.xv ∈ S := hsub (by simp)
  have hl : β.lv ∈ S := hsub (by simp)
  have hyS : y ∈ S := hsub (by simp)
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  have hm : 2 ≤ GLKind.Tits.m := F.hm
  have hU := F.uniqueGeod
  have hnG : ¬ (Gp = ⊤ ∧ GLKind.Tits = GLKind.G2d) := fun h => absurd h.2 (by decide)
  obtain ⟨z, hz, hnb, hper, rfl, hz0, hz1, sx, sl, e1, e2, f1, f2⟩ :=
    burnsideF4k_asm_refl_data burnsideF4k_polyArcs burnsideF4k_grpD10 hF hcompat hyp hnG β hβ
      hSap hx hl
  have hK : ∀ w : β.G0, (∀ v ∈ Set.range z, w • v = v) → w = 1 := fun w hw =>
    burnsideF4k_asm_tits_K burnsideF4k_polyArcs burnsideF4k_grpD10 burnsideF4k_grpTwoTrans hF h5
      hcompat hyp rfl β hβ hs z hz hnb hper hz0 w hw
  obtain ⟨ax0, ax8, ax1, ax15⟩ := burnsideF4nA_swap_apply z hz (by decide) hper 0 e1 e2
  obtain ⟨al1, -, al2, al16⟩ := burnsideF4nA_swap_apply z hz (by decide) hper 1 f1 f2
  have hz16 : z 16 = z 0 := hper 0
  have ax1' : sx • z 1 = z 15 := ax1
  have ax15' : sx • z 15 = z 1 := ax15
  have al2' : sl • z 2 = z 0 := by rw [← hz16]; exact al2
  have al0 : sl • z 0 = z 2 := by rw [← hz16]; exact al16
  have hc15 : cc = z 15 := by
    rcases burnsideF4k_polyNbr β _ hm hU z hz hnb hper 0 cc hccS (by rw [hz0]; exact hcc) with
      h | h
    · exact absurd (h.trans hz1) hccl
    · exact h
  have hy2 : y = z 2 := by
    rcases burnsideF4k_polyNbr β _ hm hU z hz hnb hper 1 y hyS (by rw [hz1]; exact hy) with
      h | h
    · exact h
    · have h' : y = z 16 := h
      exact absurd (h'.trans (hz16.trans hz0)) hyx
  have hxx : sx * sx = 1 := hK _ (burnsideF4k_polyRefl β _ hm hU z hz hnb hper 0 sx e1 e2).1
  have hll : sl * sl = 1 := hK _ (burnsideF4k_polyRefl β _ hm hU z hz hnb hper 1 sl f1 f2).1
  have hsx1 : sx ≠ 1 := by
    rintro rfl
    exact GPath.arc_ne z hz hnb _ hper (by decide) 0 (by rw [← e1, GPath.one_smul'])
  have hN1 : sx ∈ N1set β GLKind.Tits cc y := by
    rw [N1set, if_pos rfl]
    have hr : GPath.arc₁ z hz GLKind.Tits.m 0 ∈ GPath.nbPaths β.graph β.xv GLKind.Tits.m :=
      ⟨by rw [GPath.arc₁_zero, hz0], GPath.arc₁_noBack z hz hnb _ 0⟩
    have hsxb : sx ∈ stv β β.xv ⊓ stv β (GPath.arc₁ z hz GLKind.Tits.m 0 GLKind.Tits.m) := by
      refine Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr (by rw [← hz0]; exact ax0),
        MulAction.mem_stabilizer_iff.mpr ?_⟩
      rw [GPath.arc₁_last]
      exact ax8
    refine ⟨MulAction.mem_stabilizer_iff.mpr (by rw [← hz0]; exact ax0),
      ⟨hxx, Ne.symm hccl, ?_, ?_⟩, burnsideF4nA_tits_geod hF h5 hcompat hyp β hβ hs hr hsxb hxx hsx1⟩
    · rw [hc15, ← hz1]; exact ax1'
    · rw [hc15, ← hz1]; exact ax15'
  have hN2 : sl ∈ N2set β GLKind.Tits cc y y' := by
    rw [N2set, if_pos rfl]
    refine ⟨MulAction.mem_stabilizer_iff.mpr (by rw [← hz1]; exact al1),
      ⟨hll, Ne.symm hyx, ?_, ?_⟩⟩
    · rw [hy2, ← hz0]; exact al0
    · rw [hy2, ← hz0]; exact al2'
  have hord : orderOf (sx * sl) = 8 := by
    have hconn := connected_graph β
    have hbip : ∀ a b : β.Γ, β.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
      fun _ _ h => CosetGeom.vtype_ne_of_adj h
    exact burnsideF4nA_orderOf_eq (n := 2 * GLKind.Tits.m) (by norm_num)
      (burnsideF4k_pa_zf_inj hconn hbip hm hU hz hnb hper)
      (burnsideF4k_pa_swap_act hz hm hper 0 e1 e2) (burnsideF4k_pa_swap_act hz hm hper 1 f1 f2)
      (burnsideF4nA_faithful_zf hper hK) (by decide)
      (by intro k hk0 hk; interval_cases k <;> decide)
  obtain ⟨-, -, hrx, hrl, -, htrans⟩ :=
    (burnsideF4k_polyW β _ hm hU z hz hnb hper hz0 hz1 sx sl e1 e2 f1 f2).1
  have hWle : Subgroup.closure {sx, sl} ≤ setStab β (Set.range z) := by
    rw [Subgroup.closure_le]
    rintro u (rfl | rfl)
    · exact hrx.2.1
    · exact hrl.2.1
  have hSig : SigmaST β GLKind.Tits cc sx sl = Set.range z := by
    ext u
    constructor
    · rintro ((⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) | hu)
      · exact burnsideF4k_setStab_mem β (hWle hw) hx
      · exact burnsideF4k_setStab_mem β (hWle hw) hl
      · rw [if_neg (by decide)] at hu
        exact hu.elim
    · intro hu
      cases hv : CosetGeom.vtype u
      · obtain ⟨w, hw, hwu⟩ := htrans β.xv hx u hu (by rw [hv]; rfl)
        exact Or.inl (Or.inl ⟨w, hw, hwu⟩)
      · obtain ⟨w, hw, hwu⟩ := htrans β.lv hl u hu (by rw [hv]; rfl)
        exact Or.inl (Or.inr ⟨w, hw, hwu⟩)
  refine ⟨(sx, sl), ⟨hN1, hN2, ?_⟩, hSig⟩
  show orderOf (sx * sl) = m0Of GLKind.Tits
  rw [m0Of, if_pos rfl]
  exact hord

theorem burnsideF4nA_surj_g2d (hF : F_4_6) (h5 : F_4_5) (hcompat : NativeChartCompatibilityGoal)
    (hyp : HypF_4_4 GLKind.G2d p f Gp M₁ M₂) (hGp : Gp = ⊤) {Y : Type} [Group Y]
    (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) (hs : β.IsSmall GLKind.G2d.m) {cc y y' : β.Γ}
    (hcc : cc ∈ CosetGeom.nbrs β.xv) (hccl : cc ≠ β.lv) (hy : y ∈ CosetGeom.nbrs β.lv)
    (hyx : y ≠ β.xv) (hy' : y' ∈ CosetGeom.nbrs cc) (hy'x : y' ≠ β.xv) :
    Set.SurjOn (fun st : β.G0 × β.G0 => SigmaST β GLKind.G2d cc st.1 st.2)
      (Pset β GLKind.G2d cc y y') (Bset β GLKind.G2d cc y y') := by
  intro S hS
  obtain ⟨hSap, hsub⟩ := hS
  rw [if_neg (by decide)] at hsub
  have hy'S : y' ∈ S := hsub (by simp)
  have hccS : cc ∈ S := hsub (by simp)
  have hx : β.xv ∈ S := hsub (by simp)
  have hl : β.lv ∈ S := hsub (by simp)
  have hyS : y ∈ S := hsub (by simp)
  have F := burnsideF4a_facts46_of_compat hF hcompat hyp β hβ
  have hm : 2 ≤ GLKind.G2d.m := F.hm
  have hU := F.uniqueGeod
  have hfree : ∀ g ∈ setStab β S, g • β.xv = β.xv → g = 1 := fun g hg hgx =>
    burnsideF4nA_free_g2d hF h5 hcompat hyp hGp rfl β hβ hs hcc hccl hSap hx hl hccS hg hgx
  obtain ⟨z, hz, hnb, hper, rfl, hz0, hz1⟩ :=
    burnsideF4k_asm_label hm hU hSap hx hl CosetGeom.adj_γ₀_γ₁
  have hK : ∀ w : β.G0, (∀ v ∈ Set.range z, w • v = v) → w = 1 := fun w hw =>
    hfree w (burnsideF4k_pointwiseStab_le_setStab β _ ((burnsideF4k_mem_pointwiseStab β).mpr hw))
      (hw _ hx)
  have hz12 : z 12 = z 0 := hper 0
  have hc11 : cc = z 11 := by
    rcases burnsideF4k_polyNbr β _ hm hU z hz hnb hper 0 cc hccS (by rw [hz0]; exact hcc) with
      h | h
    · exact absurd (h.trans hz1) hccl
    · exact h
  have hy2 : y = z 2 := by
    rcases burnsideF4k_polyNbr β _ hm hU z hz hnb hper 1 y hyS (by rw [hz1]; exact hy) with
      h | h
    · exact h
    · have h' : y = z 12 := h
      exact absurd (h'.trans (hz12.trans hz0)) hyx
  have hy'22 : y' = z 22 := by
    rcases burnsideF4k_polyNbr β _ hm hU z hz hnb hper 11 y' hy'S (by rw [← hc11]; exact hy') with
      h | h
    · have h' : y' = z 12 := h
      exact absurd (h'.trans (hz12.trans hz0)) hy'x
    · exact h
  subst hc11
  obtain ⟨b1, b2, b3, -⟩ := burnsideF4k_polyArcs β _ hm hU z hz hnb hper 1
  have hv1 : CosetGeom.vtype (z 1) = true := by rw [hz1]; rfl
  obtain ⟨sl, -, f1, f2⟩ := burnsideF4k_asm_twoTrans_line hF hyp β hβ hv1 b1 b2 b3 _ b1 _ b2 b3
    _ b2 _ b1 (Ne.symm b3)
  obtain ⟨c1, c2, c3, -⟩ := burnsideF4k_polyArcs β _ hm hU z hz hnb hper 11
  have hv11 : CosetGeom.vtype (z 11) = true := by
    have := CosetGeom.vtype_ne_of_adj (hcc : β.graph.Adj β.xv (z 11))
    revert this
    cases CosetGeom.vtype (z 11) <;> simp [show CosetGeom.vtype β.xv = false from rfl]
  obtain ⟨sc, -, g1, g2⟩ := burnsideF4k_asm_twoTrans_line hF hyp β hβ hv11 c1 c2 c3 _ c1 _ c2 c3
    _ c2 _ c1 (Ne.symm c3)
  obtain ⟨al1, -, al2, al12⟩ := burnsideF4nA_swap_apply z hz (by decide) hper 1 f1 f2
  obtain ⟨ac11, -, ac12, ac22⟩ := burnsideF4nA_swap_apply z hz (by decide) hper 11 g1 g2
  have al2' : sl • z 2 = z 0 := by rw [← hz12]; exact al2
  have al0 : sl • z 0 = z 2 := by rw [← hz12]; exact al12
  have ac0 : sc • z 0 = z 22 := by rw [← hz12]; exact ac12
  have ac22' : sc • z 22 = z 0 := by rw [← hz12]; exact ac22
  have hll : sl * sl = 1 := hK _ (burnsideF4k_polyRefl β _ hm hU z hz hnb hper 1 sl f1 f2).1
  have hcc2 : sc * sc = 1 := hK _ (burnsideF4k_polyRefl β _ hm hU z hz hnb hper 11 sc g1 g2).1
  have hN1 : sl ∈ N1set β GLKind.G2d (z 11) y := by
    rw [N1set, if_neg (by decide)]
    refine ⟨MulAction.mem_stabilizer_iff.mpr (by rw [← hz1]; exact al1), hll, Ne.symm hyx, ?_, ?_⟩
    · rw [hy2, ← hz0]; exact al0
    · rw [hy2, ← hz0]; exact al2'
  have hN2 : sc ∈ N2set β GLKind.G2d (z 11) y y' := by
    rw [N2set, if_neg (by decide)]
    refine ⟨MulAction.mem_stabilizer_iff.mpr ac11, hcc2, Ne.symm hy'x, ?_, ?_⟩
    · rw [hy'22, ← hz0]; exact ac0
    · rw [hy'22, ← hz0]; exact ac22'
  have hord : orderOf (sl * sc) = 3 := by
    have hconn := connected_graph β
    have hbip : ∀ a b : β.Γ, β.graph.Adj a b → CosetGeom.vtype a ≠ CosetGeom.vtype b :=
      fun _ _ h => CosetGeom.vtype_ne_of_adj h
    exact burnsideF4nA_orderOf_eq (n := 2 * GLKind.G2d.m) (by norm_num)
      (burnsideF4k_pa_zf_inj hconn hbip hm hU hz hnb hper)
      (burnsideF4k_pa_swap_act hz hm hper 1 f1 f2) (burnsideF4k_pa_swap_act hz hm hper 11 g1 g2)
      (burnsideF4nA_faithful_zf hper hK) (by decide)
      (by intro k hk0 hk; interval_cases k <;> decide)
  obtain ⟨hcl', -, -, hreg, hlines, -⟩ := burnsideF4k_polyG2d β hU z hz hnb hper hz0 hz1 sl sc
    f1 f2 g1 g2 (by rw [hz0]; exact hfree)
  have hSig : SigmaST β GLKind.G2d (z 11) sl sc = Set.range z := by
    rw [SigmaST, if_pos rfl, ← hcl']
    ext u
    constructor
    · rintro ((⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩) | ⟨w, hw, rfl⟩)
      · exact burnsideF4k_setStab_mem β hw hx
      · exact burnsideF4k_setStab_mem β hw hl
      · exact burnsideF4k_setStab_mem β hw hccS
    · intro hu
      cases hv : CosetGeom.vtype u
      · obtain ⟨w, hwu, -⟩ := hreg β.xv hx rfl u hu hv
        exact Or.inl (Or.inl ⟨w, w.2, hwu⟩)
      · have hu' : u ∈ {u : β.Γ | u ∈ Set.range z ∧ CosetGeom.vtype u = true} := ⟨hu, hv⟩
        rw [hlines] at hu'
        rcases hu' with ⟨w, hw, hwu⟩ | ⟨w, hw, hwu⟩
        · exact Or.inl (Or.inr ⟨w, hw, hwu⟩)
        · exact Or.inr ⟨w, hw, hwu⟩
  refine ⟨(sl, sc), ⟨hN1, hN2, ?_⟩, hSig⟩
  show orderOf (sl * sc) = m0Of GLKind.G2d
  rw [m0Of, if_neg (by decide)]
  exact hord

end SurjOn

theorem burnside_as_F_4_19_of
    (h45 : F_4_5) (h46 : F_4_6) : F_4_19 := by
  intro κ p f E _ Gp M₁ M₂ hyp hGp hκ Y _ β hβ hs cc hcc hccl y hy hyx y' hy' hy'x
  have F := burnsideF4a_facts46_of_compat h46 ChF.nativeChartCompatibility hyp β hβ
  rcases hκ with rfl | rfl
  · refine ⟨fun st hst => ?_,
      burnsideF4nA_injOn_g2d h46 h45 ChF.nativeChartCompatibility hyp hGp β hβ hs hcc hccl y y',
      burnsideF4nA_surj_g2d h46 h45 ChF.nativeChartCompatibility hyp hGp β hβ hs hcc hccl hy hyx
        hy' hy'x⟩
    obtain ⟨h1, h2, h3⟩ := hst
    rw [m0Of, if_neg (by decide)] at h3
    exact burnsideF4nA_maps_g2d F.uniqueGeod hcc hccl h1 h2 h3
  · refine ⟨fun st hst => ?_,
      burnsideF4nA_injOn_tits h46 h45 ChF.nativeChartCompatibility hyp β hβ hs cc y y',
      burnsideF4nA_surj_tits h46 h45 ChF.nativeChartCompatibility hyp β hβ hs hcc hccl hy hyx y'⟩
    obtain ⟨h1, h2, h3⟩ := hst
    rw [m0Of, if_pos rfl] at h3
    exact burnsideF4nA_maps_tits F.uniqueGeod h1 h2 h3

end CFSG.ASVolI
