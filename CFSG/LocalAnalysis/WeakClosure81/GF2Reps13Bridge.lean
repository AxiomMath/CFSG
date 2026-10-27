module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.FixedSpace
public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds
public import CFSG.RankThree.FFModules.BinaryTransport
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13BridgeA
public import CFSG.LocalAnalysis.RankThreeUC.ModuleHypotheses
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations
open CFSG.LocalAnalysis.RankThreeUC.WeakClosure

@[expose] noncomputable def dihedralDeg (p : ℕ) : ℕ :=
  if Even (dParam p) then dParam p else 2 * dParam p

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_stableUnder_zpowers {t : MulAut W} {U : Subgroup W} (htt : t * t = 1)
    (hUt : ∀ u ∈ U, t u ∈ U) : StableUnder (Subgroup.zpowers t) U := by
  have ht_stab : t ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    refine ⟨fun htu => ?_, hUt u⟩
    have h := hUt (t u) htu
    rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h
  intro s hs u hu
  exact (mem_stabSub.1 (Subgroup.zpowers_le.2 ht_stab hs) u).2 hu

private theorem w16g_mem_sup_zpowers_or {X : Subgroup (MulAut W)} {t : MulAut W}
    (hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (htt : t * t = 1)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) {g : MulAut W}
    (hg : g ∈ X ⊔ Subgroup.zpowers t) : g ∈ X ∨ ∃ a ∈ X, g = a * t := by
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htb : ∀ b ∈ X, t * b = b⁻¹ * t := fun b hb => by rw [← hinv b hb]; group
  have hclosure : X ⊔ Subgroup.zpowers t
      = Subgroup.closure ((X : Set (MulAut W)) ∪ {t}) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.zpowers_eq_closure]
  refine Subgroup.closure_induction (p := fun g _ => g ∈ X ∨ ∃ a ∈ X, g = a * t)
    ?_ ?_ ?_ ?_ (hclosure ▸ hg)
  · rintro s (hs | hs)
    · exact Or.inl hs
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact Or.inr ⟨1, X.one_mem, by rw [one_mul]⟩
  · exact Or.inl X.one_mem
  · rintro a b _ _ ha hb
    rcases ha with ha | ⟨a', ha', rfl⟩
    · rcases hb with hb | ⟨b', hb', rfl⟩
      · exact Or.inl (X.mul_mem ha hb)
      · exact Or.inr ⟨a * b', X.mul_mem ha hb', by rw [mul_assoc]⟩
    · rcases hb with hb | ⟨b', hb', rfl⟩
      · refine Or.inr ⟨a' * b⁻¹, X.mul_mem ha' (X.inv_mem hb), ?_⟩
        rw [mul_assoc, htb b hb, ← mul_assoc]
      · refine Or.inl ?_
        rw [mul_assoc, ← mul_assoc t b' t, htb b' hb', mul_assoc, htt, mul_one]
        exact X.mul_mem ha' (X.inv_mem hb')
  · rintro a _ ha
    rcases ha with ha | ⟨a', ha', rfl⟩
    · exact Or.inl (X.inv_mem ha)
    · refine Or.inr ⟨a', ha', ?_⟩
      rw [mul_inv_rev, ht_inv, htb a'⁻¹ (X.inv_mem ha'), inv_inv]

theorem inf_fixV_hyperplane_decomposition (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (A : Subgroup (MulAut W)) (hA : CFSG.Open.IsElemAbelian p A)
    {U : Subgroup W} (hU : StableUnder A U) (hAU : commSub U A = U) :
    iSupIndep (fun D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A =>
        U ⊓ fixV (D : Subgroup (MulAut W))) ∧
      (⨆ D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A,
        U ⊓ fixV (D : Subgroup (MulAut W))) = U := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite A := inferInstance
  set M : Submodule (ZMod 2) (Additive W) := w16g_toSub U with hMdef
  have hStab : ∀ s ∈ A, ∀ u ∈ U, s u ∈ U := hU
  have hM : ∀ s ∈ A, ∀ m ∈ M, CFSG.RankThree.FFModules.autRep W s m ∈ M := by
    intro s hs m hm
    rw [hMdef, w16g_mem_toSub] at hm ⊢
    rw [CFSG.RankThree.FFModules.autRep_apply]
    exact hStab s hs m hm
  let ρM :=
    ExtraspecialDimensionDivisibility.restrictRep
      (CFSG.RankThree.FFModules.autRep W) A M hM
  have hAtop : CFSG.Open.IsElemAbelian p (⊤ : Subgroup ↥A) := by
    refine ⟨IsMulCommutative.of_comm (fun a b => Subtype.ext (hA.1.is_comm.comm a.1 b.1)), ?_⟩
    intro x _
    exact Subtype.ext (hA.2 x.1 x.2)
  have htop : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM (⊤ : Subgroup ↥A)
      = ⊤ := by
    apply Submodule.map_injective_of_injective M.subtype_injective
    rw [CFSG.LocalAnalysis.WeakClosure81.w16g_map_commSpace_restrictRep]
    have hrange : (⊤ : Subgroup ↥A).map A.subtype = A := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hrange, hMdef, ← CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_commSub, hAU, ← hMdef,
      Submodule.map_subtype_top]
  have hInt :=
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.coprime_hyperplane_decomposition
      (q := 2) (p := p) hp2 ρM (⊤ : Subgroup ↥A) hAtop htop
  have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 hInt
  have hfix : ∀ D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
        (⊤ : Subgroup ↥A),
      (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.fixedSpace ρM D'.1).map M.subtype =
        CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (U ⊓ fixV (D'.1.map A.subtype)) := by
    intro D'
    rw [CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds.fixed_map
        (CFSG.RankThree.FFModules.autRep W) A M hM D'.1, hMdef,
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_inf,
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_fixV]
  have h1 : iSupIndep (fun D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
        (⊤ : Subgroup ↥A) =>
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (U ⊓ fixV (D'.1.map A.subtype))) := by
    simpa only [hfix] using CFSG.LocalAnalysis.WeakClosure81.w16g_iSupIndep_map_subtype h.1
  have h2 : (⨆ D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
        (⊤ : Subgroup ↥A),
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (U ⊓ fixV (D'.1.map A.subtype))) = M := by
    have hmap : (⨆ D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
          (⊤ : Subgroup ↥A),
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.fixedSpace ρM D'.1).map M.subtype)
        = M := by
      rw [← Submodule.map_iSup, h.2, Submodule.map_subtype_top]
    rwa [iSup_congr (fun D' => (hfix D'))] at hmap
  set Ψ := CFSG.LocalAnalysis.WeakClosure81.w16g_hyperplanesEquiv (W := W) A with hΨ
  refine ⟨?_, ?_⟩
  · have h3 : iSupIndep (fun D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
          (⊤ : Subgroup ↥A) => U ⊓ fixV (D'.1.map A.subtype)) :=
      (iSupIndep_map_orderIso_iff CFSG.LocalAnalysis.WeakClosure81.w16g_toSub).1 h1
    have h4 : iSupIndep (fun D : hyperplanes p A
        => U ⊓ fixV (D : Subgroup (MulAut W))) := h3.comp' (f := Ψ) Ψ.surjective
    simpa using h4
  · have hsup : (⨆ D' : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p
          (⊤ : Subgroup ↥A), U ⊓ fixV (D'.1.map A.subtype)) = U := by
      apply (CFSG.LocalAnalysis.WeakClosure81.w16g_toSub).injective
      rw [OrderIso.map_iSup, h2, hMdef]
    rw [← Equiv.iSup_comp (g := fun D :
        CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A =>
      U ⊓ fixV (D : Subgroup (MulAut W))) Ψ]
    rw [hΨ]
    exact hsup

theorem rk_commSub_eq_two_mul_of_inverted_on (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelianOfRank p n ↥X)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) {U : Subgroup W} (hUX : StableUnder X U)
    (hUt : ∀ u ∈ U, t u ∈ U) :
    rk ↥(commSub U X) = 2 * rk ↥(commSub (commSub U X) (Subgroup.zpowers t)) := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have htt : t * t = 1 := by
    rw [← pow_two]; exact pow_eq_one_iff_modEq.mpr (by simp [ht])
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((w16g_isElemAbelianOfRank_comm_pow hX).1 ⟨x, hx⟩ ⟨y, hy⟩)
  let G : Subgroup (MulAut W) := X ⊔ Subgroup.zpowers t
  have hXG : X ≤ G := le_sup_left
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hXstab : X ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro u
    exact ⟨fun hxu => by
      have h := hUX x⁻¹ (X.inv_mem hx) (x u) hxu
      rwa [show x⁻¹ (x u) = u by
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h, hUX x hx u⟩
  have htstab : t ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun htu => by
      have h := hUt (t u) htu
      rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h, hUt u⟩
  have hStabG : ∀ s ∈ G, ∀ u ∈ U, s u ∈ U := fun s hs u hu =>
    (mem_stabSub.1 (sup_le hXstab (Subgroup.zpowers_le.2 htstab) hs) u).2 hu
  set M : Submodule (ZMod 2) (Additive W) := w16g_toSub U with hMdef
  have hMG : ∀ s ∈ G, ∀ m ∈ M, CFSG.RankThree.FFModules.autRep W s m ∈ M := by
    intro s hs m hm
    rw [hMdef, w16g_mem_toSub] at hm ⊢
    rw [CFSG.RankThree.FFModules.autRep_apply]
    exact hStabG s hs m hm
  let ρM :=
    ExtraspecialDimensionDivisibility.restrictRep
      (CFSG.RankThree.FFModules.autRep W) G M hMG
  have hXpow : ∀ x ∈ X, x ^ p = 1 := fun x hx =>
    congrArg Subtype.val ((w16g_isElemAbelianOfRank_comm_pow hX).2 ⟨x, hx⟩)
  have hX'rank : IsElemAbelianOfRank p n (X.subgroupOf G) := by
    obtain ⟨e⟩ := hX
    exact ⟨(Subgroup.subgroupOfEquivOfLe hXG).trans e⟩
  have hX'pow : ∀ x ∈ X.subgroupOf G, x ^ p = 1 := fun x hx => Subtype.ext (hXpow x.1 hx)
  have hX'comm : ∀ x ∈ X.subgroupOf G, ∀ y ∈ X.subgroupOf G, x * y = y * x := fun x hx y hy =>
    Subtype.ext (hXcomm x.1 hx y.1 hy)
  haveI : Fintype (X.subgroupOf G) := Fintype.ofFinite _
  have hodd : Odd (Fintype.card (X.subgroupOf G)) := by
    rw [Fintype.card_eq_nat_card, w16g_card_of_isElemAbelianOfRank hX'rank]
    exact (hp.odd_of_ne_two hp2).pow
  have hX2 : ∀ x ∈ X.subgroupOf G, x ^ 2 = 1 → x = 1 := fun x hx hx2 =>
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds.sq_eq_one
      hp2 hp x (hX'pow x hx) hx2
  have hinvX' : ∀ x ∈ X.subgroupOf G, (⟨t, htG⟩ : ↥G) * x * (⟨t, htG⟩ : ↥G)⁻¹ = x⁻¹ :=
    fun x hx => Subtype.ext (hinv x.1 hx)
  have ht' : orderOf (⟨t, htG⟩ : ↥G) = 2 := by rw [orderOf_mk, ht]
  have h1 :=
    HyperplaneOrbitBounds.finrank_commSpace_eq_two_mul_iterated_commutator
      ρM (X.subgroupOf G) ⟨t, htG⟩ ht' hodd hX2 hinvX' hX'comm
  have hmapX : (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM
        (X.subgroupOf G)).map M.subtype
      = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (commSub U X) := by
    rw [w16g_map_commSpace_restrictRep, Subgroup.map_subgroupOf_eq_of_le hXG, hMdef,
      ← w16g_toSub_commSub]
  have hmapT : (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM
        (Subgroup.zpowers (⟨t, htG⟩ : ↥G))).map M.subtype
      = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (commSub U (Subgroup.zpowers t)) := by
    rw [w16g_map_commSpace_restrictRep, MonoidHom.map_zpowers, hMdef, ← w16g_toSub_commSub]
    rfl
  have hmapT2 : (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commOn ρM
        (Subgroup.zpowers (⟨t, htG⟩ : ↥G))
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM (X.subgroupOf G))).map
        M.subtype
      = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub
          (commSub (commSub U X) (Subgroup.zpowers t)) := by
    rw [w16g_map_commOn_restrictRep, hmapX, MonoidHom.map_zpowers, ← w16g_toSub_commSub]
    rfl
  have hLX : Module.finrank (ZMod 2)
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM (X.subgroupOf G))
      = rk ↥(commSub U X) := by
    rw [← Submodule.finrank_map_subtype_eq (p := M)
      (q := CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM (X.subgroupOf G)),
      hmapX]
    exact (w16g_rk_eq_finrank hW (commSub U X)).symm
  have hLT : Module.finrank (ZMod 2)
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commOn ρM
          (Subgroup.zpowers (⟨t, htG⟩ : ↥G))
          (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM (X.subgroupOf G)))
      = rk ↥(commSub (commSub U X) (Subgroup.zpowers t)) := by
    rw [← Submodule.finrank_map_subtype_eq (p := M)
      (q := CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commOn ρM
        (Subgroup.zpowers (⟨t, htG⟩ : ↥G))
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM (X.subgroupOf G))),
      hmapT2]
    exact (w16g_rk_eq_finrank hW (commSub (commSub U X) (Subgroup.zpowers t))).symm
  rw [hLX, hLT] at h1
  exact h1

theorem n_mul_dihedralDeg_le_two_mul_rk_on (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelianOfRank p n ↥X)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) {U : Subgroup W} (hUX : StableUnder X U)
    (hUt : ∀ u ∈ U, t u ∈ U) (hfaith : ∀ x ∈ X, (∀ u ∈ U, x u = u) → x = 1) :
    n * dihedralDeg p ≤ 2 * rk ↥(commSub U (Subgroup.zpowers t)) := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  have htt : t * t = 1 := by
    rw [← pow_two]; exact pow_eq_one_iff_modEq.mpr (by simp [ht])
  have hXcomm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((w16g_isElemAbelianOfRank_comm_pow hX).1 ⟨x, hx⟩ ⟨y, hy⟩)
  let G : Subgroup (MulAut W) := X ⊔ Subgroup.zpowers t
  have hXG : X ≤ G := le_sup_left
  have htG : t ∈ G := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hXstab : X ≤ stabSub U := by
    intro x hx
    rw [mem_stabSub]
    intro u
    exact ⟨fun hxu => by
      have h := hUX x⁻¹ (X.inv_mem hx) (x u) hxu
      rwa [show x⁻¹ (x u) = u by
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]] at h, hUX x hx u⟩
  have htstab : t ∈ stabSub U := by
    rw [mem_stabSub]
    intro u
    exact ⟨fun htu => by
      have h := hUt (t u) htu
      rwa [show t (t u) = u by rw [← MulAut.mul_apply, htt, MulAut.one_apply]] at h, hUt u⟩
  have hStabG : ∀ s ∈ G, ∀ u ∈ U, s u ∈ U := fun s hs u hu =>
    (mem_stabSub.1 (sup_le hXstab (Subgroup.zpowers_le.2 htstab) hs) u).2 hu
  set M : Submodule (ZMod 2) (Additive W) := w16g_toSub U with hMdef
  have hMG : ∀ s ∈ G, ∀ m ∈ M, CFSG.RankThree.FFModules.autRep W s m ∈ M := by
    intro s hs m hm
    rw [hMdef, w16g_mem_toSub] at hm ⊢
    rw [CFSG.RankThree.FFModules.autRep_apply]
    exact hStabG s hs m hm
  let ρM :=
    ExtraspecialDimensionDivisibility.restrictRep
      (CFSG.RankThree.FFModules.autRep W) G M hMG
  have hXpow : ∀ x ∈ X, x ^ p = 1 := fun x hx =>
    congrArg Subtype.val ((w16g_isElemAbelianOfRank_comm_pow hX).2 ⟨x, hx⟩)
  have hX'rank : IsElemAbelianOfRank p n (X.subgroupOf G) := by
    obtain ⟨e⟩ := hX
    exact ⟨(Subgroup.subgroupOfEquivOfLe hXG).trans e⟩
  have hXab' : CFSG.Assembly.IsElemAbelian p (X.subgroupOf G) :=
    w16g_isElemAbelian_of_isElemAbelianOfRank hX'rank
  have hXcard' : Nat.card (X.subgroupOf G) = p ^ n :=
    w16g_card_of_isElemAbelianOfRank hX'rank
  have hinvX' : ∀ x ∈ X.subgroupOf G, (⟨t, htG⟩ : ↥G) * x * (⟨t, htG⟩ : ↥G)⁻¹ = x⁻¹ :=
    fun x hx => Subtype.ext (hinv x.1 hx)
  have ht' : orderOf (⟨t, htG⟩ : ↥G) = 2 := by rw [orderOf_mk, ht]
  have hρM : Function.Injective ρM := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgU : ∀ u ∈ U, g.1 u = u := by
      intro u hu
      have hm : Additive.ofMul u ∈ M := by
        rw [hMdef, w16g_mem_toSub]; simpa using hu
      have h1 : ρM g ⟨Additive.ofMul u, hm⟩ = ⟨Additive.ofMul u, hm⟩ := by rw [hg]; rfl
      have h2 : (CFSG.RankThree.FFModules.autRep W g.1) (Additive.ofMul u)
          = Additive.ofMul u := by
        have h1' := congrArg Subtype.val h1
        change (CFSG.RankThree.FFModules.autRep W (g : MulAut W)) (Additive.ofMul u)
          = Additive.ofMul u at h1'
        rw [CFSG.RankThree.FFModules.autRep_apply] at h1'
        exact Additive.ofMul.injective h1'
      rw [CFSG.RankThree.FFModules.autRep_apply] at h2
      exact Additive.ofMul.injective h2
    obtain hdec | ⟨a, ha, hga⟩ := w16g_mem_sup_zpowers_or hXcomm htt hinv g.2
    · exact Subtype.ext (hfaith g.1 hdec hgU)
    · have hgs : g.1 = a * t := hga
      have hsU : ∀ u ∈ U, (a * t) u = u := fun u hu => by
        have := hgU u hu
        rwa [hgs] at this
      have hsG : a * t ∈ G := hgs ▸ g.2
      have hs_invU : ∀ u ∈ U, (a * t)⁻¹ u = u := fun u hu => by
        have h1 : (a * t) ((a * t)⁻¹ u) = (a * t)⁻¹ u :=
          hsU _ (hStabG ((a * t)⁻¹) (G.inv_mem hsG) u hu)
        rw [show (a * t) ((a * t)⁻¹ u) = u by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]] at h1
        exact h1.symm
      have hsx : ∀ x ∈ X, (a * t) * x * (a * t)⁻¹ = x⁻¹ := by
        intro x hx
        rw [show (a * t) * x * (a * t)⁻¹ = a * (t * x * t⁻¹) * a⁻¹ by group,
          hinv x hx, hXcomm a ha x⁻¹ (X.inv_mem hx), mul_assoc, mul_inv_cancel, mul_one]
      have hx1 : ∀ x ∈ X, x = 1 := by
        intro x hx
        have hx2U : ∀ u ∈ U, (x ^ 2) u = u := by
          intro u hu
          have hcu : ((a * t) * x * (a * t)⁻¹) u = x u := by
            show (a * t) (x ((a * t)⁻¹ u)) = x u
            rw [hs_invU u hu, hsU _ (hUX x hx u hu)]
          have h3 : x⁻¹ u = x u := by rw [← hcu, hsx x hx]
          have h4 := congrArg (fun v => x v) h3
          rw [show x (x⁻¹ u) = u by
            rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]] at h4
          rw [pow_two, MulAut.mul_apply]
          exact h4.symm
        exact CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.HyperplaneOrbitBounds.sq_eq_one
          hp2 hp x (hXpow x hx) (hfaith (x ^ 2) (X.pow_mem hx 2) hx2U)
      have hXbot : X = ⊥ := (Subgroup.eq_bot_iff_forall X).2 hx1
      exfalso
      have hXcard : Nat.card X = p ^ n := w16g_card_of_isElemAbelianOfRank hX
      rw [hXbot, Subgroup.card_bot] at hXcard
      have hgt : 1 < p ^ n := one_lt_pow' hp.one_lt (Nat.pos_iff_ne_zero.mp hn)
      omega
  have h :=
    finrank_commutator_eq_two_mul_and_involution_rank_bound
      (ρ := ρM) hρM ⟨t, htG⟩ ht' hp hp2 hn (X.subgroupOf G) hXab' hXcard' hinvX'
  have hmapT : (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM
        (Subgroup.zpowers (⟨t, htG⟩ : ↥G))).map M.subtype
      = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (commSub U (Subgroup.zpowers t)) := by
    rw [w16g_map_commSpace_restrictRep, MonoidHom.map_zpowers, hMdef, ← w16g_toSub_commSub]
    rfl
  have hLt : Module.finrank (ZMod 2)
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM
          (Subgroup.zpowers (⟨t, htG⟩ : ↥G)))
      = rk ↥(commSub U (Subgroup.zpowers t)) := by
    rw [← Submodule.finrank_map_subtype_eq (p := M)
      (q := CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace ρM
        (Subgroup.zpowers (⟨t, htG⟩ : ↥G))), hmapT]
    exact (w16g_rk_eq_finrank hW (commSub U (Subgroup.zpowers t))).symm
  have hbound := h.2
  rw [hLt] at hbound
  have hdp : dParam p = orderOf (2 : ZMod p) := rfl
  have he : eOfPrime p = dihedralDeg p := by
    simp only [eOfPrime, dihedralDeg, dOfPrime_eq_orderOf hp hp2, hdp]
  calc n * dihedralDeg p = n * eOfPrime p := by rw [he]
    _ ≤ max n (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.minHyperplaneOrbit p
          (X.subgroupOf G)) * eOfPrime p := Nat.mul_le_mul_right _ (le_max_left _ _)
    _ ≤ 2 * rk ↥(commSub U (Subgroup.zpowers t)) := hbound

theorem fixV_hyperplane_decomposition (hW : ∀ w : W, w ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (A : Subgroup (MulAut W)) (hA : CFSG.Open.IsElemAbelian p A)
    (hV : commSub ⊤ A = ⊤) :
    iSupIndep (fun D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A =>
        fixV (D : Subgroup (MulAut W))) ∧
      (⨆ D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A,
        fixV (D : Subgroup (MulAut W))) = ⊤ := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite A := inferInstance
  have hcomm : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace
      (CFSG.RankThree.FFModules.autRep W) A = ⊤ := by
    have h1 : CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (commSub ⊤ A)
        = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (⊤ : Subgroup W) := by rw [hV]
    rw [CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_commSub,
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_top,
      CFSG.LocalAnalysis.WeakClosure81.w16g_commOn_top] at h1
    exact h1
  have hInt :=
    CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.coprime_hyperplane_decomposition
      (q := 2) (p := p) hp2 (CFSG.RankThree.FFModules.autRep W) A hA hcomm
  have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 hInt
  have hfix : ∀ D : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.hyperplanes p A,
      CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.fixedSpace
          (CFSG.RankThree.FFModules.autRep W) D.1
        = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (fixV D.1) :=
    fun D => (CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_fixV D.1).symm
  refine ⟨?_, ?_⟩
  · have h1 : iSupIndep (fun D : hyperplanes p A
        => CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (fixV D.1)) := by
      simpa only [hfix] using h.1
    exact (iSupIndep_map_orderIso_iff CFSG.LocalAnalysis.WeakClosure81.w16g_toSub).1 h1
  · apply (CFSG.LocalAnalysis.WeakClosure81.w16g_toSub).injective
    rw [OrderIso.map_iSup, CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_top,
      iSup_congr (fun D => (hfix D).symm)]
    exact h.2

theorem rk_commSub_eq_two_mul_of_inverted (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelianOfRank p n ↥X)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    rk ↥(commSub ⊤ X) = 2 * rk ↥(commSub (commSub ⊤ X) (Subgroup.zpowers t)) := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut W) := inferInstance
  have hXab : CFSG.Assembly.IsElemAbelian p X :=
    w16g_isElemAbelian_of_isElemAbelianOfRank hX
  have hXcard : Nat.card X = p ^ n := w16g_card_of_isElemAbelianOfRank hX
  have hfaith : Function.Injective (CFSG.RankThree.FFModules.autRep W) :=
    CFSG.RankThree.FFModules.autRep_injective
  have h1 :=
    (finrank_commutator_eq_two_mul_and_involution_rank_bound
      (ρ := CFSG.RankThree.FFModules.autRep W) hfaith t ht hp hp2 hn X hXab hXcard hinv).1
  have hcsX : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace
      (CFSG.RankThree.FFModules.autRep W) X
        = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (commSub ⊤ X) := by
    rw [CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_commSub,
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_top,
      CFSG.LocalAnalysis.WeakClosure81.w16g_commOn_top]
  have hcsT : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commOn
      (CFSG.RankThree.FFModules.autRep W) (Subgroup.zpowers t)
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace
          (CFSG.RankThree.FFModules.autRep W) X)
        = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub
            (commSub (commSub ⊤ X) (Subgroup.zpowers t)) := by
    rw [hcsX, ← CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_commSub]
  rw [CFSG.LocalAnalysis.WeakClosure81.w16g_rk_eq_finrank hW (commSub ⊤ X),
    CFSG.LocalAnalysis.WeakClosure81.w16g_rk_eq_finrank hW
      (commSub (commSub ⊤ X) (Subgroup.zpowers t)),
    ← hcsX, ← hcsT]
  exact h1

theorem n_mul_dihedralDeg_le_two_mul_rk (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W}
    (ht : orderOf t = 2) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 0 < n)
    {X : Subgroup (MulAut W)} (hX : IsElemAbelianOfRank p n ↥X)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) :
    n * dihedralDeg p ≤ 2 * rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut W) := inferInstance
  have hXab : CFSG.Assembly.IsElemAbelian p X :=
    w16g_isElemAbelian_of_isElemAbelianOfRank hX
  have hXcard : Nat.card X = p ^ n := w16g_card_of_isElemAbelianOfRank hX
  have hfaith : Function.Injective (CFSG.RankThree.FFModules.autRep W) :=
    CFSG.RankThree.FFModules.autRep_injective
  have h :=
    finrank_commutator_eq_two_mul_and_involution_rank_bound
      (ρ := CFSG.RankThree.FFModules.autRep W) hfaith t ht hp hp2 hn X hXab hXcard hinv
  have hcsT : CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace
      (CFSG.RankThree.FFModules.autRep W) (Subgroup.zpowers t)
        = CFSG.LocalAnalysis.WeakClosure81.w16g_toSub (commSub ⊤ (Subgroup.zpowers t)) := by
    rw [CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_commSub,
      CFSG.LocalAnalysis.WeakClosure81.w16g_toSub_top,
      CFSG.LocalAnalysis.WeakClosure81.w16g_commOn_top]
  have hLt : Module.finrank (ZMod 2)
        (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.commSpace
          (CFSG.RankThree.FFModules.autRep W) (Subgroup.zpowers t))
      = rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    rw [hcsT]
    exact (w16g_rk_eq_finrank hW (commSub ⊤ (Subgroup.zpowers t))).symm
  have hbound := h.2
  rw [hLt] at hbound
  have hdp : dParam p = orderOf (2 : ZMod p) := rfl
  have he : eOfPrime p = dihedralDeg p := by
    simp only [eOfPrime, dihedralDeg, dOfPrime_eq_orderOf hp hp2, hdp]
  calc n * dihedralDeg p = n * eOfPrime p := by rw [he]
    _ ≤ max n (CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.minHyperplaneOrbit p X)
          * eOfPrime p := Nat.mul_le_mul_right _ (le_max_left _ _)
    _ ≤ 2 * rk ↥(commSub ⊤ (Subgroup.zpowers t)) := hbound

end CFSG.LocalAnalysis.WeakClosure81
