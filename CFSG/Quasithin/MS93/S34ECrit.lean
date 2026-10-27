module

public import CFSG.Quasithin.MS93.S33Trans
import CFSG.Quasithin.MS93.S33SpLin
public import CFSG.Quasithin.MS93.S32Cent
public import CFSG.Quasithin.MS93.S34DCrit
public import CFSG.Quasithin.MS93.S34RLin
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.MS93.S34E

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement
open Matrix

section LinAlg

variable {ι : Type} [Fintype ι] {F : Type} [Field F]

theorem ringHom_eq_of_fix_sub {f : (ι → F) → (ι → F)} {σ : F →+* F}
    (hσ : ∀ (c : F) (x : ι → F), f (c • x) = σ c • f x) {g₀ : Matrix ι ι F}
    (hg₀ : ∃ x, g₀ *ᵥ x ≠ x) (hfix : ∀ x, f (g₀ *ᵥ x - x) = g₀ *ᵥ x - x) (c : F) :
    σ c = c := by
  obtain ⟨x, hx⟩ := hg₀
  have hv : g₀ *ᵥ x - x ≠ 0 := sub_ne_zero.2 hx
  have h1 : f (c • (g₀ *ᵥ x - x)) = c • (g₀ *ᵥ x - x) := by
    have e : c • (g₀ *ᵥ x - x) = g₀ *ᵥ (c • x) - c • x := by
      rw [Matrix.mulVec_smul, smul_sub]
    rw [e, hfix]
  have h2 := hσ c (g₀ *ᵥ x - x)
  rw [h1, hfix] at h2
  have h3 : (σ c - c) • (g₀ *ᵥ x - x) = 0 := by rw [sub_smul, ← h2, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right hv)

end LinAlg

section Coord

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem fix_sub_of_mem_centralizer {ι : Type} {F : Type} [Field F] {V R : Subgroup G}
    {β : ↥V →* Multiplicative (Fin 1 → ι → F)} (hβ : Function.Surjective β) {e : G}
    (heV : e ∈ Subgroup.normalizer (V : Set G)) {g : (ι → F) → (ι → F)} (hg : IsCoordAct β e g)
    (heR : ∀ u ∈ V, ⁅e, u⁆ ∈ R) {y : G} (hy : y ∈ Subgroup.centralizer (R : Set G))
    {f : (ι → F) → (ι → F)} (hf : IsCoordAct β y f) (x : ι → F) : f (g x - x) = g x - x := by
  obtain ⟨u, rfl⟩ := exists_coord_eq hβ x
  have hc : ⁅e, (u : G)⁆ ∈ V := by
    rw [commutatorElement_def]
    exact V.mul_mem (conj_mem_of_mem_normalizer heV u) (V.inv_mem u.2)
  have hk := S33.crd_commutator_kernel heV hg u hc
  have hfix := S33.fix_of_mem_centralizer' hy hf (u := ⟨_, hc⟩) (heR u u.2)
  rw [← hk]
  exact hfix

theorem le_centralizer_of_imM (h : PUHyp M T L) {H K : Subgroup G} (hH : H ≤ M) (hK : K ≤ M)
    (hHK : imM h.le H ≤ Subgroup.centralizer (imM h.le K : Set (puAmalgam h.le).Universal)) :
    H ≤ Subgroup.centralizer (K : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hx' : (puAmalgam h.le).ofA ⟨x, hH hx⟩ ∈ imM h.le H := (S33.ofA_mem_imM_iff h.le _).2 hx
  have hk' : (puAmalgam h.le).ofA ⟨k, hK hk⟩ ∈ imM h.le K := (S33.ofA_mem_imM_iff h.le _).2 hk
  have h1 := Subgroup.mem_centralizer_iff.mp (hHK hx') _ hk'
  rw [← map_mul, ← map_mul] at h1
  exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)

theorem imM_le_centralizer (h : PUHyp M T L) {H K : Subgroup G}
    (hHK : H ≤ Subgroup.centralizer (K : Set G)) :
    imM h.le H ≤ Subgroup.centralizer (imM h.le K : Set (puAmalgam h.le).Universal) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (hHK (Subgroup.mem_subgroupOf.mp hx)) _
    (Subgroup.mem_subgroupOf.mp hk)

theorem le_centralizer_pre_iff (h : PUHyp M T L) {μ : Vtx (puAmalgam h.le)}
    (hcμ : IsCritical (puAmalgam h.le) μ (baseA _)) :
    Qv (puAmalgam h.le) (baseB _) ≤
        Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) : Set (puAmalgam h.le).Universal) ↔
      T ≤ Subgroup.centralizer ((⁅S33.pre h.le (ZM _ μ), Z0q M T⁆ : Subgroup G) : Set G) := by
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hcμ
  have hRM : ⁅S33.pre h.le (ZM _ μ), Z0q M T⁆ ≤ M :=
    S33.commutator_le_of_le (S33.pre_le h.le _) (Z0q_le M T)
  have himR : imM h.le ⁅S33.pre h.le (ZM _ μ), Z0q M T⁆ = critR (puAmalgam h.le) μ (baseA _) := by
    rw [S33.imM_commutator h.le (S33.pre_le h.le _) (Z0q_le M T), hEim, critR,
      puAmalgam.zm_baseA h.le]
  rw [← himR, puAmalgam.qv_baseB]
  exact ⟨le_centralizer_of_imM h h.le hRM, imM_le_centralizer h⟩

theorem pre_zm_le_not_le (h : PUHyp M T L) {μ : Vtx (puAmalgam h.le)}
    (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    S33.pre h.le (ZM _ μ) ≤ T ∧
      ¬ S33.pre h.le (ZM _ μ) ≤ Subgroup.centralizer (Uq M T L : Set G) := by
  have hb := h.critDist_pos
  have h20 := h.hyp20
  have hdμ : (puAmalgam h.le).treeGraph.dist μ (baseA _) = critDist (puAmalgam h.le) := hcμ.2.1
  have hZμT : ZM (puAmalgam h.le) μ ≤ Qv _ (baseB _) := by
    refine zm_le_qv_of_dist_lt _ hcμ.1 ?_
    rw [← hμβ, SimpleGraph.dist_comm,
      dist_geo_right _ (by rw [SimpleGraph.dist_comm, hdμ]; exact hb), SimpleGraph.dist_comm, hdμ]
    omega
  have hβT : Qv (puAmalgam h.le) (baseB _) = imM h.le T := puAmalgam.qv_baseB h.le
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hcμ
  have hET : S33.pre h.le (ZM _ μ) ≤ T := by
    rw [← imM_le_imM_iff h.le (S33.pre_le h.le _), hEim, ← hβT]
    exact hZμT
  refine ⟨hET, fun hEC => ms22_ii _ h20 hb h.centHyp hcμ ?_⟩
  have hbot : ⁅Uq M T L, S33.pre h.le (ZM _ μ)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu e he
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hEC he) u hu)
  have hRim : imM h.le ⁅S33.pre h.le (ZM _ μ), Z0q M T⁆ =
      ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [S33.imM_commutator h.le (S33.pre_le h.le _) (Z0q_le M T), hEim,
      (puAmalgam.zm_baseA h.le).symm]
  rw [← hRim, Subgroup.commutator_comm, S33.commutator_Z0q_eq h hET, hbot]
  simp [imM]

end Coord

section SL3

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSL 3 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 3 → F)}

omit [Fintype F] in
theorem mem_linPart_of_centralizer_sl (h : PUHyp M T L) (ha : Function.Surjective a)
    (hβ : Function.Surjective β) (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    {e : G} (heT : e ∈ T) {g₀ : Matrix (Fin 3) (Fin 3) F} (hg₀ : IsCoordAct β e g₀.mulVec)
    (hmv : ∃ x, g₀ *ᵥ x ≠ x) {R : Subgroup G} (heR : ∀ u ∈ Uq M T L, ⁅e, u⁆ ∈ R) {y : G}
    (hyT : y ∈ T) (hy : y ∈ Subgroup.centralizer (R : Set G)) : y ∈ S34R.linPart h β := by
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβ hβker (hTV hyT)
  obtain ⟨σ, hσ⟩ := S33.exists_semilinear_of_mem h ha hβ hβker hβα (h.le hyT) hf
  have hσid := ringHom_eq_of_fix_sub hσ hmv
    (fix_sub_of_mem_centralizer hβ (hTV heT) hg₀ heR hy hf)
  have hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := fun c x => by rw [hσ, hσid]
  have hbot : y ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker (hTV hyT) hbot hf hlin
  exact ⟨hyT, ⟨γ, Subgroup.mem_top γ⟩, hγ⟩

theorem exists_crit_mat_sl (h : PUHyp M T L) {n : ℕ} (hcard : Fintype.card F = 2 ^ n)
    (ha : Function.Surjective a) (hβ : Function.Surjective β)
    (hβker : β.ker = (⊥ : Subgroup G).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (β u) i))
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    ∃ e ∈ S33.pre h.le (ZM _ μ), ∃ g₀ : Matrix (Fin 3) (Fin 3) F,
      IsCoordAct β e g₀.mulVec ∧ ∃ x, g₀ *ᵥ x ≠ x := by
  obtain ⟨hEab, hE2, hUE, -, hEim⟩ := S33.pre_zm_props h hcμ
  obtain ⟨hET, hEU⟩ := pre_zm_le_not_le h hcμ hμβ
  obtain ⟨e, heE, heU⟩ := Set.not_subset.1 hEU
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have heV := hTV (hET heE)
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβ hβker heV
  have hlin : ∀ (c : F) (x : Fin 3 → F), f (c • x) = c • f x := by
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hF2 : Fintype.card F = 2 := S34R.card_eq_two_of_lt hcard hn2
      intro c x
      rcases S33.eq_zero_or_eq_one_of_card_eq_two hF2 c with rfl | rfl
      · rw [zero_smul, zero_smul, map_zero]
      · rw [one_smul, one_smul]
    · have hF4 : 4 ≤ Fintype.card F := by
        rw [hcard]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      by_contra hnl
      apply S33.relIndex_qv_zm_ne_two_gen h
        (fun _ hm hnt => S33.four_le_relIndex_centralizer h ha hβ hβker hβα hF4 hm hnt) hcμ
      rw [← hEim, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
        S33.relIndex_imM h.le (S33.pre_le h.le _)]
      exact S33.relIndex_eq_two_of_nonlinear h ha hβ hβker hβα hcard hET hEab hE2 hUE
        ⟨e, heE, f, hf, hnl⟩
  have hbot : e ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  obtain ⟨γ₀, hγ₀⟩ := S34R.exists_gl_of_linear hβ hβker heV hbot hf hlin
  refine ⟨e, heE, _, hγ₀, ?_⟩
  by_contra hall
  push Not at hall
  exact heU (S34D.mem_centralizer_of_coord_id hβker heV hγ₀ hall)

theorem sl3Full_of_critR_central (h : PUHyp M T L) (hU : IsSL3U M T L)
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _)
    (hR : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) : Set (puAmalgam h.le).Universal)) :
    IsSL3Full M T L := by
  obtain ⟨hX, hZU, n, F, _, _, a, hcard, ha, -, -, β, hβ, hβker, hβα⟩ := hU
  have hTR := (le_centralizer_pre_iff h hcμ).1 hR
  obtain ⟨e, heE, g₀, hg₀, hmv⟩ := exists_crit_mat_sl h hcard ha hβ hβker hβα hcμ hμβ
  have heT : e ∈ T := (pre_zm_le_not_le h hcμ hμβ).1 heE
  refine S34R.sl3Full_of_le_linPart h hcard ha hX hZU hβ hβker hβα fun y hy => ?_
  exact mem_linPart_of_centralizer_sl h ha hβ hβker hβα heT hg₀ hmv
    (fun u hu => Subgroup.commutator_mem_commutator heE (Uq_le_Z0q h.L_le hu)) hy (hTR hy)

end SL3

section Sp4

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSp 2 F)} {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)}

theorem mem_linPart_of_centralizer_sp (h : PUHyp M T L) (ha : Function.Surjective a)
    (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i))
    {e : G} (heT : e ∈ T) {g₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hg₀ : IsCoordAct β e g₀.mulVec) (hmv : ∃ x, g₀ *ᵥ x ≠ x) {R : Subgroup G}
    (heR : ∀ u ∈ Uq M T L, ⁅e, u⁆ ∈ R) {y : G} (hyT : y ∈ T)
    (hy : y ∈ Subgroup.centralizer (R : Set G)) : y ∈ S34R.linPart h β := by
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hTZ : T ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
  have hyV := hTV hyT
  obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker hyV (hTZ hyT)
  obtain ⟨f', hf'⟩ := exists_isCoordAct hβ hβker (inv_mem hyV) (hTZ (inv_mem hyT))
  obtain ⟨σ, hσ⟩ := S33.exists_semilinear_sp ha
    (h.L_le.trans (le_normalizer_Uq h.le_normalizer)) hβ (S33.isCoordAct_of_natSp hβα) hyV
    (h.le_normalizer (h.le hyT)) hf hf'
  have hσid := ringHom_eq_of_fix_sub hσ hmv
    (fix_sub_of_mem_centralizer hβ (hTV heT) hg₀ heR hy hf)
  have hlin : ∀ (c : F) (x : Fin 2 ⊕ Fin 2 → F), f (c • x) = c • f x := fun c x => by
    rw [hσ, hσid]
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker hyV (hTZ hyT) hf hlin
  exact ⟨hyT, ⟨γ, Subgroup.mem_top γ⟩, hγ⟩

theorem exists_crit_mat_sp (h : PUHyp M T L) {k : ℕ} (hk : 2 ≤ k)
    (hcard : Fintype.card F = 2 ^ k) (ha : Function.Surjective a) (hβ : Function.Surjective β)
    (hβker : β.ker = (Uq M T L ⊓ Subgroup.centralizer (L : Set G)).subgroupOf (Uq M T L))
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i))
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    ∃ e ∈ S33.pre h.le (ZM _ μ), ∃ g₀ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F,
      IsCoordAct β e g₀.mulVec ∧ ∃ x, g₀ *ᵥ x ≠ x := by
  obtain ⟨hET, hEU⟩ := pre_zm_le_not_le h hcμ hμβ
  obtain ⟨e, heE, heU⟩ := Set.not_subset.1 hEU
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hTZ : T ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
  have heT := hET heE
  obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker (hTV heT) (hTZ heT)
  have hF4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hβker' : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L) := by
    rw [h.Uq_inf_Zq]
    exact hβker
  have hlin := S33.linear_of_isCritical_sp h ha hβ hβker' (S33.isCoordAct_of_natSp hβα) hcard
    hF4 hcμ e heE f hf
  obtain ⟨γ₀, hγ₀⟩ := S34R.exists_gl_of_linear hβ hβker (hTV heT) (hTZ heT) hf hlin
  refine ⟨e, heE, _, hγ₀, ?_⟩
  by_contra hall
  push Not at hall
  exact heU (S34D.mem_centralizer_of_coord_id_sp h hβker (h.le heT) hγ₀ hall)

theorem sp4Full_of_critR_central (h : PUHyp M T L) (hU : IsSp4U M T L)
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _)
    (hR : Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) : Set (puAmalgam h.le).Universal)) :
    IsSp4Full M T L := by
  rcases hU with ⟨k, F, _, _, a, hk, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ | ⟨a, ha, hnat⟩
  · have hTR := (le_centralizer_pre_iff h hcμ).1 hR
    obtain ⟨e, heE, g₀, hg₀, hmv⟩ := exists_crit_mat_sp h hk hcard ha hβ hβker hβα hcμ hμβ
    have heT : e ∈ T := (pre_zm_le_not_le h hcμ hμβ).1 heE
    refine S34R.sp4Full_of_le_linPart h hk hcard ha hLV hZV hβ hβker hβα fun y hy => ?_
    exact mem_linPart_of_centralizer_sp h ha hβ hβker hβα heT hg₀ hmv
      (fun u hu => Subgroup.commutator_mem_commutator heE (Uq_le_Z0q h.L_le hu)) hy (hTR hy)
  · exact ⟨1, ZMod 2, inferInstance, inferInstance, a, le_rfl, by simp, ha, hnat⟩

end Sp4

end CFSG.Quasithin.MS93.S34E
