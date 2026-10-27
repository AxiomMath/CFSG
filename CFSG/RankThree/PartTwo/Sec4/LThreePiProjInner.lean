module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

section Center

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem isPerfect_projImage_of_equiv [Group.IsPerfect L]
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) :
    Group.IsPerfect (projImage (slPi π 3 (p ^ f) K)) :=
  Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem center_eq_bot_proj (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) : Subgroup.center L = ⊥ := by
  rw [eq_bot_iff]
  intro l hl
  have hcen : e l ∈ Subgroup.center (projImage (slPi π 3 (p ^ f) K)) := by
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨l', rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hl l')]
  rw [center_projImage_eq_bot hK hq, Subgroup.mem_bot] at hcen
  exact Subgroup.mem_bot.mpr (e.injective (by rw [hcen, map_one]))

theorem inf_centralizer_eq_bot_proj (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))]
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) :
    L ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.mp hx
  have hZ : (⟨x, hxL⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC l l.2)
  rw [center_eq_bot_proj hK hq e, Subgroup.mem_bot] at hZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hZ)

theorem aschbacherSolvableCore_eq_bot_proj [Finite G] (hK : PiField π p f K)
    (hq : ModThree π (p ^ f)) (hLq : CFSG.IsQuasisimple L)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) : aschbacherSolvableCore 3 L = ⊥ := by
  have : Group.IsPerfect L := hLq.1
  have := isPerfect_projImage_of_equiv e
  have hchar := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hZ : aschbacherSolvableCore 3 L ≤ Subgroup.center L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq
      (inferInstance : (aschbacherSolvableCore 3 L).Normal) with h | h
    · exfalso
      have hsol := hchar.1
      rw [h] at hsol
      have hsolL : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := L)).symm.injective
      have := CFSG.LocalCores.isQuasisimple_nontrivial hLq
      exact Group.IsPerfect.not_isSolvable _ hsolL
    · exact h
  rw [center_eq_bot_proj hK hq e] at hZ
  exact le_bot_iff.mp hZ

end Center

section Inner

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K] {p f : ℕ}
  {π : Bool}

theorem coe_e_eq_mk_of_isPGLAtP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {l : G} (hl : l ∈ L) {z : GL (Fin 3) K} (hz : IsPGLAtP e l z) :
    ((e ⟨l, hl⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk z := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l, hl⟩).2
  have hls : IsPGLAtP e l s := isPGLAtP_of_mem e hπ hl hs hse.symm
  have h1 := mk_eq_one_iff_mem_statedScalars.mpr (isPGLAtP_inv_mul_mem hK hq hls hz)
  rw [map_mul, map_inv] at h1
  rw [← hse]
  exact inv_mul_eq_one.mp h1

theorem exists_inner_mem_of_innerP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {a : G} {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) {l : GL (Fin 3) K}
    (hl : l ∈ slPi π 3 (p ^ f) K)
    (hyl : ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹) :
    ∃ (v : G) (hv : v ∈ L),
      ((e ⟨v, hv⟩ : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
        ProjGenLinGroup.mk l ∧ a * v⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set w : L := e.symm (projOf _ ⟨l, hl⟩) with hw
  have hew : ((e w : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
      ProjGenLinGroup.mk l := by
    rw [hw, MulEquiv.apply_symm_apply, coe_projOf]
  refine ⟨w, w.2, hew, ?_⟩
  have hwinv : IsPGLAtP e ((w : G)⁻¹) l⁻¹ := by
    refine isPGLAtP_of_mem e hπ (inv_mem w.2) (inv_mem hl) ?_
    have : (⟨(w : G)⁻¹, inv_mem w.2⟩ : L) = w⁻¹ := rfl
    rw [this, map_inv, Subgroup.coe_inv, hew, map_inv]
  have hprod := isPGLAtP_mul e hy hwinv
  refine mem_centralizer_of_isPGLAtP_scalar hprod ?_
  refine mem_statedScalars_of_commute hπ hq' hτ hτ1 fun m hm => ?_
  have hm' : l⁻¹ * m * l ∈ slPi π 3 (p ^ f) K := by
    simpa using conj_mem_slPi hπ (inv_mem (slPi_le_glPi hπ hl)) hm
  have h1 := hyl _ hm'
  calc y * l⁻¹ * m = y * (l⁻¹ * m * l) * y⁻¹ * (y * l⁻¹) := by group
    _ = l * (l⁻¹ * m * l) * l⁻¹ * (y * l⁻¹) := by rw [h1]
    _ = m * (y * l⁻¹) := by group

theorem exists_inner_of_mem_supP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {a : G} (ha : a ∈ L ⊔ Subgroup.centralizer (L : Set G)) {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) :
    ∃ l ∈ slPi π 3 (p ^ f) K, ∀ m ∈ slPi π 3 (p ^ f) K, y * m * y⁻¹ = l * m * l⁻¹ := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  obtain ⟨l', hl', u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (e ⟨l', hl'⟩).2
  have hls : IsPGLAtP e l' s := isPGLAtP_of_mem e hπ hl' hs hse.symm
  have hlu : IsPGLAtP e (l' * u) (s * 1) :=
    isPGLAtP_mul e hls (isPGLAtP_of_mem_centralizer e hu)
  rw [mul_one] at hlu
  obtain ⟨c, hc⟩ := isPGLAtP_inv_mul_mem hK hq hlu hy
  have hys : y = s * GeneralLinearGroup.scalar (Fin 3) c := by rw [hc]; group
  refine ⟨s, hs, fun m _ => ?_⟩
  have hcm := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c m).eq
  rw [hys]
  calc s * GeneralLinearGroup.scalar (Fin 3) c * m * (s * GeneralLinearGroup.scalar (Fin 3) c)⁻¹ =
      s * (GeneralLinearGroup.scalar (Fin 3) c * m) *
        (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * s⁻¹ := by group
    _ = s * (m * GeneralLinearGroup.scalar (Fin 3) c) *
        (GeneralLinearGroup.scalar (Fin 3) c)⁻¹ * s⁻¹ := by rw [hcm]
    _ = s * m * s⁻¹ := by group

theorem mem_of_mul_inv_mem_centralizer {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {a l : G} (ha : a ∈ A) (hl : l ∈ L)
    (hal : a * l⁻¹ ∈ Subgroup.centralizer (L : Set G)) : l ∈ A := by
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCn : (Subgroup.centralizer (L : Set G)).Normal := inferInstance
  set u := a * l⁻¹ with hu
  have hlu : l * u = u * l := Subgroup.mem_centralizer_iff.mp hal l hl
  have hl' : l = u⁻¹ * a := by rw [hu]; group
  have hbot : ∀ x, x ∈ L → x ∈ Subgroup.centralizer (L : Set G) → x = 1 := fun x hxL hxC =>
    Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨hxL, hxC⟩)
  have hl3 : l ^ 3 = 1 := by
    have h1 : a ^ 3 = 1 := hA.1.2 a ha
    have ha' : a = u * l := by rw [hl']; group
    rw [ha', (show Commute u l from hlu.symm).mul_pow] at h1
    have h2 : l ^ 3 = (u ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1
    refine hbot _ (pow_mem hl 3) ?_
    rw [h2]
    exact inv_mem (pow_mem hal 3)
  refine mem_of_maximal_of_commute hA hl3 fun b hb => ?_
  have hab := hAcomm a ha b hb
  have hw : b * l * b⁻¹ * l⁻¹ = (b * u * b⁻¹)⁻¹ * u := by
    have e1 : a * b⁻¹ * a⁻¹ = b⁻¹ := by
      calc a * b⁻¹ * a⁻¹ = b⁻¹ * (b * a) * b⁻¹ * a⁻¹ := by group
        _ = b⁻¹ * (a * b) * b⁻¹ * a⁻¹ := by rw [hab]
        _ = b⁻¹ := by group
    calc b * l * b⁻¹ * l⁻¹ = b * (u⁻¹ * a) * b⁻¹ * (u⁻¹ * a)⁻¹ := by rw [hl']
      _ = b * u⁻¹ * (a * b⁻¹ * a⁻¹) * u := by group
      _ = b * u⁻¹ * b⁻¹ * u := by rw [e1]
      _ = (b * u * b⁻¹)⁻¹ * u := by group
  have hwL : b * l * b⁻¹ * l⁻¹ ∈ L := mul_mem (hLn.conj_mem l hl b) (inv_mem hl)
  have hwC : b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [hw]
    exact mul_mem (inv_mem (hCn.conj_mem u hal b)) hal
  have h1 := hbot _ hwL hwC
  calc b * l = b * l * b⁻¹ * l⁻¹ * (l * b) := by group
    _ = l * b := by rw [h1, one_mul]

theorem inf_sup_centralizer_eq {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c : G}
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) :
    A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) = (A ⊓ L) ⊔ Subgroup.zpowers c := by
  have hCn : (Subgroup.centralizer (L : Set G)).Normal := inferInstance
  apply le_antisymm
  · intro x hx
    obtain ⟨hxA, hxLC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxLC
    have hal : l * u * l⁻¹ ∈ Subgroup.centralizer (L : Set G) := hCn.conj_mem u hu l
    have hlA := mem_of_mul_inv_mem_centralizer hA hLC hxA hl hal
    have huA : u ∈ A := by
      have : u = l⁻¹ * (l * u) := by group
      rw [this]
      exact mul_mem (inv_mem hlA) hxA
    have huc : u ∈ Subgroup.zpowers c := hAc ▸ Subgroup.mem_inf.mpr ⟨huA, hu⟩
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hlA, hl⟩))
      (Subgroup.mem_sup_right huc)
  · refine sup_le (inf_le_inf_left _ le_sup_left) ?_
    rw [← hAc]
    exact inf_le_inf_left _ le_sup_right

variable [Finite G]

theorem card_inf_sup_centralizer {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c) :
    Nat.card (A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) : Subgroup G) =
      Nat.card (A ⊓ L : Subgroup G) * 3 := by
  rw [inf_sup_centralizer_eq hA hLC hAc]
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) := by
    rw [← hAc]
    exact inf_le_right
  have hcomm : ∀ x ∈ A ⊓ L, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hcC hy) x (Subgroup.mem_inf.mp hx).2
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  have hinf : A ⊓ L ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff, ← hLC]
    exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans hcC)
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3] at h
  exact h

end Inner

section Types

variable {G : Type} [Group G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K] {p f : ℕ}
  {π : Bool}

theorem pow_three_mem_zPiP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {g : G} (hg : g ^ 3 = 1) {y : GL (Fin 3) K} (hy : IsPGLAtP e g y) :
    y ^ 3 ∈ zPi π 3 (p ^ f) K := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h := isPGLAtP_pow hy 3
  rw [hg] at h
  have h1 := isPGLAtP_inv_mul_mem hK hq (isPGLAtP_of_mem_centralizer e (Subgroup.one_mem _)) h
  rw [inv_one, one_mul] at h1
  rw [zPi_eq hπ hq' hτ hτ1]
  exact ⟨h.1, h1⟩

theorem not_mem_zPi_of_isPGLAtP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {g : G}
    (hg : g ∉ Subgroup.centralizer (L : Set G)) {y : GL (Fin 3) K} (hy : IsPGLAtP e g y) :
    y ∉ zPi π 3 (p ^ f) K := by
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  exact fun hz => hg (mem_centralizer_of_isPGLAtP_scalar hy
    (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz))

theorem type13_of_heisP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {E : Subgroup (GL (Fin 3) K ⧸ StatedScalars (Fin 3) K)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    {y : GL (Fin 3) K} (hyH : y ∈ glPi π 3 (p ^ f) K) (hyZ : y ∉ zPi π 3 (p ^ f) K)
    (hy3 : y ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hyE : (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ E) :
    Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3 := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3 := hK.three_ne_zero hq
  rcases type123_exhaust hK hq hyH hyZ hy3 with h | h | h
  · exact Or.inl h
  · exfalso
    apply trace_ne_zero_of_type2 hK hq h
    by_cases hc1 : y * y₁ = y₁ * y
    · by_cases hc2 : y * y₂ = y₂ * y
      · apply absurd _ hyZ
        rw [zPi_eq hπ hq' hτ hτ1]
        exact ⟨hyH, mem_statedScalars_of_commute_heis h3 hζ1
          (pow_three_eq_one_of_conj_eq_scalar_mul hζ) hζ hc1 hc2⟩
      · obtain ⟨lam2, hlam2⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hy₂ _ hyE)
        refine trace_eq_zero_of_conj_eq_scalar_mul (fun h1 => hc2 ?_) hlam2
        rw [h1, map_one, one_mul] at hlam2
        calc y * y₂ = y₂ * y * y₂⁻¹ * y₂ := by rw [hlam2]
          _ = y₂ * y := by group
    · obtain ⟨lam1, hlam1⟩ := exists_scalar_of_mk_mul_comm (hcomm _ hy₁ _ hyE)
      refine trace_eq_zero_of_conj_eq_scalar_mul (fun h1 => hc1 ?_) hlam1
      rw [h1, map_one, one_mul] at hlam1
      calc y * y₁ = y₁ * y * y₁⁻¹ * y₁ := by rw [hlam1]
        _ = y₁ * y := by group
  · exact Or.inr h

end Types

section Bridges

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

omit hLn in
theorem thetaQuot_slAct (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (z : L ⧸ aschbacherSolvableCore 3 L) :
    (thetaBotEquiv hθ).trans e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hx⟩) z) =
      slAct e ⟨x, hx⟩ ((thetaBotEquiv hθ).trans e z) := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, thetaQuotMulAut_mk, thetaBotEquiv_mk,
      thetaBotEquiv_mk, slAct_apply, MulEquiv.symm_apply_apply]

theorem inducesTypeOn_of_isPGLAtP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    (hθ : aschbacherSolvableCore 3 L = ⊥) {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {a : G}
    {y : GL (Fin 3) K} (hy : IsPGLAtP e a y) {k : ℕ} (hk : Type123 π (p ^ f) K y k) :
    InducesTypeOn L a k := by
  refine ⟨mem_normalizer_of_normal a, π, p, f, K, inferInstance, hK, hq,
    (thetaBotEquiv hθ).trans e, y, hy.1, hk, fun z => ?_⟩
  rw [thetaQuot_slAct hθ e]
  exact hy.2 _

theorem isTypeCOn_of_frameP (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] (hθ : aschbacherSolvableCore 3 L = ⊥)
    {e : L ≃* projImage (slPi π 3 (p ^ f) K)} {E : Subgroup G}
    (hE : ∀ a ∈ E, ∃ y, IsPGLAtP e a y) (h3 : ∀ a ∈ E, a ^ 3 = 1)
    (h9 : Nat.card (pglHomP hK hq E hE).range = 9) {b : Fin 3 → (Fin 3 → K)}
    (hb : LinearIndependent K b)
    (hd : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
      (pglHomP hK hq E hE).range → ∀ i, ∃ c : K, (y : Matrix (Fin 3) (Fin 3) K) *ᵥ b i = c • b i) :
    IsTypeCOn E L := by
  set R := (pglHomP hK hq E hE).range with hR
  set D : Subgroup (GL (Fin 3) K) :=
    R.comap (QuotientGroup.mk' (StatedScalars (Fin 3) K)) ⊓ glPi π 3 (p ^ f) K with hD
  have hmemD : ∀ y, y ∈ D ↔ (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ R ∧
      y ∈ glPi π 3 (p ^ f) K := fun y => Iff.rfl
  have hRpow := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hE) h3
  have hmap : D.map (QuotientGroup.mk' (StatedScalars (Fin 3) K)) = R := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ((hmemD y).mp hy).1
    · rintro x ⟨a, rfl⟩
      obtain ⟨y, hy⟩ := hE a a.2
      refine ⟨y, (hmemD y).mpr ⟨?_, hy.1⟩, ?_⟩
      · exact mk_mem_range_pglHomP a.2 hy
      · exact (pglHomP_apply a hy).symm
  have hC : IsTypeC π (p ^ f) K D := by
    refine ⟨inf_le_right, fun a ha => ?_, by rw [hmap, h9], b, hb, fun a ha => hd a
      ((hmemD a).mp ha).1⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hRpow _ ((hmemD a).mp ha).1
  refine ⟨π, p, f, K, inferInstance, hK, hq, (thetaBotEquiv hθ).trans e, D, hC, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨h, hN, hhE, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    obtain ⟨y, hy⟩ := hE h hhE
    refine ⟨y, (hmemD y).mpr ⟨mk_mem_range_pglHomP hhE hy, hy.1⟩, fun z => ?_⟩
    rw [thetaQuot_slAct hθ e hN]
    exact hy.2 _
  · intro y hy
    obtain ⟨hyR, hyH⟩ := (hmemD y).mp hy
    obtain ⟨a, ha, hay⟩ := exists_isPGLAtP_of_mk_mem hyH hyR
    refine ⟨thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, mem_normalizer_of_normal a⟩),
      mem_autThetaQuot_iff.mpr ⟨a, _, ha, rfl⟩, fun z => ?_⟩
    rw [thetaQuot_slAct hθ e]
    exact hay.2 _

end Bridges

section Transitivity

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal] {K : Type} [Field K]
  {p f : ℕ} {π : Bool}

theorem heis_of_mul_scalar {y₁ y₂ z₁ z₂ : GL (Fin 3) K}
    (h₁ : y₁⁻¹ * z₁ ∈ StatedScalars (Fin 3) K) (h₂ : y₂⁻¹ * z₂ ∈ StatedScalars (Fin 3) K)
    {ζ : Kˣ} (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    z₁ * z₂ * z₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * z₂ := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  have hz₁ : z₁ = y₁ * GeneralLinearGroup.scalar (Fin 3) w₁ := by rw [hw₁]; group
  have hz₂ : z₂ = y₂ * GeneralLinearGroup.scalar (Fin 3) w₂ := by rw [hw₂]; group
  have hc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  calc z₁ * z₂ * z₁⁻¹ = y₁ * (GeneralLinearGroup.scalar (Fin 3) w₁ * z₂ *
        (GeneralLinearGroup.scalar (Fin 3) w₁)⁻¹) * y₁⁻¹ := by rw [hz₁]; group
    _ = y₁ * z₂ * y₁⁻¹ := by rw [← hc w₁ z₂]; group
    _ = (y₁ * y₂ * y₁⁻¹) * (y₁ * GeneralLinearGroup.scalar (Fin 3) w₂ * y₁⁻¹) := by
        rw [hz₂]; group
    _ = (y₁ * y₂ * y₁⁻¹) * GeneralLinearGroup.scalar (Fin 3) w₂ := by rw [hc w₂ y₁]; group
    _ = GeneralLinearGroup.scalar (Fin 3) ζ * z₂ := by rw [hζ, hz₂]; group

theorem eq_one_of_scalar_mul_eq {ζ : Kˣ} {z : GL (Fin 3) K}
    (h : GeneralLinearGroup.scalar (Fin 3) ζ * z = z) : ζ = 1 := by
  have h2 : GeneralLinearGroup.scalar (Fin 3) ζ = 1 := by
    calc GeneralLinearGroup.scalar (Fin 3) ζ = GeneralLinearGroup.scalar (Fin 3) ζ * z * z⁻¹ :=
          by group
      _ = 1 := by rw [h, mul_inv_cancel]
  have h3 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) h2
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    Units.val_one, Matrix.one_apply_eq] at h3
  exact Units.ext h3

theorem not_mem_statedScalars_of_heis {y₁ y₂ : GL (Fin 3) K} {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) :
    y₁ ∉ StatedScalars (Fin 3) K := by
  intro hs
  have h1 : y₁ * y₂ * y₁⁻¹ = y₂ := by
    rw [← commute_of_mem_statedScalars hs y₂]
    group
  rw [h1] at hζ
  exact hζ1 (eq_one_of_scalar_mul_eq hζ.symm)

theorem not_mk_eq_zpow_of_heis {y₁ y₂ : GL (Fin 3) K} {ζ : Kˣ} (hζ1 : ζ ≠ 1)
    (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂) (k : ℤ) :
    ProjGenLinGroup.mk y₂ ≠ ProjGenLinGroup.mk (y₁ ^ k) := by
  intro hmk
  have hsc : (y₁ ^ k)⁻¹ * y₂ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, hmk, inv_mul_cancel]
  obtain ⟨w, hw⟩ := hsc
  have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar w y₁⁻¹).eq
  have hy₂ : y₂ = y₁ ^ k * GeneralLinearGroup.scalar (Fin 3) w := by rw [hw]; group
  have h2 : y₁ * y₂ * y₁⁻¹ = y₂ := by
    rw [hy₂]
    calc y₁ * (y₁ ^ k * GeneralLinearGroup.scalar (Fin 3) w) * y₁⁻¹ =
        y₁ * y₁ ^ k * (GeneralLinearGroup.scalar (Fin 3) w * y₁⁻¹) := by group
      _ = y₁ * y₁ ^ k * (y₁⁻¹ * GeneralLinearGroup.scalar (Fin 3) w) := by rw [hc]
      _ = y₁ ^ k * GeneralLinearGroup.scalar (Fin 3) w := by group
  rw [h2] at hζ
  exact hζ1 (eq_one_of_scalar_mul_eq hζ.symm)

theorem transitive_of_range_heis (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {E : Subgroup G} (hEL : E ≤ L) (hE9 : Nat.card E = 9)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE3 : ∀ a ∈ E, a ^ 3 = 1)
    (hE : ∀ a ∈ E, ∃ y, IsPGLAtP e a y) {y₁ y₂ : GL (Fin 3) K}
    (hy₁ : (y₁ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq E hE).range)
    (hy₂ : (y₂ : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq E hE).range)
    {ζ : Kˣ} (hζ1 : ζ ≠ 1) (hζ : y₁ * y₂ * y₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * y₂)
    (h1 : ∀ x ∈ E, x ≠ 1 → ∀ y, IsPGLAtP e x y → Type123 π (p ^ f) K y 1) :
    ∀ x ∈ E, x ≠ 1 → ∀ y ∈ E, y ≠ 1 →
      ∃ n ∈ L ⊓ Subgroup.normalizer (E : Set G), n * x * n⁻¹ = y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨v₁, hv₁E⟩, hv₁⟩ := hy₁
  obtain ⟨⟨v₂, hv₂E⟩, hv₂⟩ := hy₂
  obtain ⟨z₁, hz₁⟩ := hE v₁ hv₁E
  obtain ⟨z₂, hz₂⟩ := hE v₂ hv₂E
  rw [pglHomP_apply ⟨v₁, hv₁E⟩ hz₁, QuotientGroup.eq] at hv₁
  rw [pglHomP_apply ⟨v₂, hv₂E⟩ hz₂, QuotientGroup.eq] at hv₂
  have hv₁' : y₁⁻¹ * z₁ ∈ StatedScalars (Fin 3) K := by
    have := inv_mem hv₁
    rwa [_root_.mul_inv_rev, inv_inv] at this
  have hv₂' : y₂⁻¹ * z₂ ∈ StatedScalars (Fin 3) K := by
    have := inv_mem hv₂
    rwa [_root_.mul_inv_rev, inv_inv] at this
  have hz : z₁ * z₂ * z₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * z₂ :=
    heis_of_mul_scalar hv₁' hv₂' hζ
  have hv₁L := hEL hv₁E
  have hv₂L := hEL hv₂E
  have he₁ := coe_e_eq_mk_of_isPGLAtP hK hq hv₁L hz₁
  have he₂ := coe_e_eq_mk_of_isPGLAtP hK hq hv₂L hz₂
  have hv₁1 : v₁ ≠ 1 := by
    intro h
    apply not_mem_statedScalars_of_heis hζ1 hz
    rw [← mk_eq_one_iff_mem_statedScalars, ← he₁]
    have : (⟨v₁, hv₁L⟩ : L) = 1 := Subtype.ext h
    rw [this, map_one]
    rfl
  have hz₁1 := h1 v₁ hv₁E hv₁1 z₁ hz₁
  obtain ⟨s₂, hs₂, hse₂⟩ := Subgroup.mem_map.mp (e ⟨v₂, hv₂L⟩).2
  have hzs : z₂⁻¹ * s₂ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, ← he₂, hse₂, inv_mul_cancel]
  have hs : z₁ * s₂ * z₁⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * s₂ :=
    heis_of_mul_scalar (by rw [inv_mul_cancel]; exact one_mem _) hzs hz
  have hv₂n : v₂ ∉ Subgroup.zpowers v₁ := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply not_mk_eq_zpow_of_heis hζ1 hz k
    rw [← he₂, map_zpow, ← he₁]
    have : (⟨v₂, hv₂L⟩ : L) = (⟨v₁, hv₁L⟩ : L) ^ k := Subtype.ext (by
      rw [Subgroup.coe_zpow]
      exact hk.symm)
    rw [this, map_zpow, Subgroup.coe_zpow]
  have hv₁o : orderOf v₁ = 3 := orderOf_eq_prime (hE3 v₁ hv₁E) hv₁1
  have hcard := card_zpowers_sup_zpowers (hE3 v₂ hv₂E) hv₁o hv₂n (hEcomm v₂ hv₂E v₁ hv₁E)
  have hEeq : Subgroup.zpowers v₁ ⊔ Subgroup.zpowers v₂ = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hv₁E)
      (Subgroup.zpowers_le.mpr hv₂E)) (by rw [hE9, hcard])
  have key := transitive_of_heis_pair hK hq e hv₁L hv₂L he₁ hse₂.symm hz₁1 hs₂ hζ1 hs
  rw [hEeq] at key
  exact key

end Transitivity

end CFSG.RankThree.PartTwo.Sec4
