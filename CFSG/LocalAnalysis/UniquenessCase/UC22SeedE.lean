module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Main
public import CFSG.Adapters.Certificate43Check
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedG
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
open Matrix (SpecialLinearGroup)

section Gen

variable {G : Type} [Group G] {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)

theorem autI_eq_map_actHom (K : Subgroup G) : autI hV K = K.map (actHom hV) := by
  ext a
  rw [mem_autI, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, mem_normalizer_of_normal g⟩, hg, rfl⟩

theorem normal_subgroupOf_autI (N : Subgroup G) [N.Normal] :
    ((autI hV N).subgroupOf (autI hV (⊤ : Subgroup G))).Normal := by
  have h1 : (autI hV N).subgroupOf (autI hV (⊤ : Subgroup G)) = N.map (actA hV) := by
    ext a
    rw [Subgroup.mem_subgroupOf, autI_eq_map_actHom, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨g, hg, hga⟩
      exact ⟨g, hg, Subtype.ext hga⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩
  rw [h1]
  exact Subgroup.Normal.map inferInstance (actA hV) (actA_surjective hV)

end Gen

theorem exists_pow_mem_of_sup_eq_top {G : Type} [Group G] {N T : Subgroup G} [N.Normal] (hT : IsPGroup 2 T)
    (hNT : N ⊔ T = ⊤) (g : G) : ∃ a : ℕ, g ^ 2 ^ a ∈ N := by
  have hg : g ∈ N ⊔ T := by rw [hNT]; exact Subgroup.mem_top g
  obtain ⟨n, hn, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have key : ∀ m : ℕ, ∃ n' ∈ N, (n * t) ^ m = n' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨n', hn', e⟩ := ih
      refine ⟨n' * (t ^ m * n * (t ^ m)⁻¹), N.mul_mem hn' (Subgroup.Normal.conj_mem inferInstance n hn _), ?_⟩
      rw [pow_succ, e]
      group
  obtain ⟨n', hn', e⟩ := key (2 ^ a)
  exact ⟨a, by rw [e, ha', mul_one]; exact hn'⟩

section Bar

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]
  {T : Subgroup G} {π : G →* SpecialLinearGroup (Fin 2) k}

theorem exists_bar (h : SeedSetting T π) {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
    (hOC : CFSG.pCore 2 G ≤ Subgroup.centralizer (V : Set G))
    (hCK : Subgroup.centralizer (V : Set G) ≤ π.ker) :
    ∃ πb : ↥(autI hV (⊤ : Subgroup G)) →* SpecialLinearGroup (Fin 2) k,
      (∀ g, πb (actA hV g) = π g) ∧ Function.Surjective πb ∧ ¬ 2 ∣ Nat.card πb.ker := by
  classical
  haveI : Finite ↥(autI hV (⊤ : Subgroup G)) := Finite.of_surjective _ (actA_surjective hV)
  have hker : (actA hV).ker ≤ π.ker := by rw [ker_actA]; exact hCK
  have hcomp : ∀ g, ((actA hV).liftOfSurjective (actA_surjective hV) ⟨π, hker⟩) (actA hV g) = π g :=
    fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨π, hker⟩ g
  set πb := (actA hV).liftOfSurjective (actA_surjective hV) ⟨π, hker⟩ with hπb
  refine ⟨πb, hcomp, ?_, ?_⟩
  · intro s
    obtain ⟨g, rfl⟩ := h.surj s
    exact ⟨actA hV g, hcomp g⟩
  · intro hdvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    obtain ⟨g, hg⟩ := actA_surjective hV (y : ↥(autI hV (⊤ : Subgroup G)))
    have hgK : g ∈ π.ker := by
      have h1 : πb (y : ↥(autI hV (⊤ : Subgroup G))) = 1 := y.2
      rw [← hg, hcomp] at h1
      exact h1
    have hy2 : (y : ↥(autI hV (⊤ : Subgroup G))) ^ 2 = 1 := by
      have h2 : y ^ orderOf y = 1 := pow_orderOf_eq_one y
      rw [hy] at h2
      simpa using congrArg Subtype.val h2
    have hg2 : g ^ 2 ^ 1 ∈ Subgroup.centralizer (V : Set G) := by
      rw [← ker_actA hV, MonoidHom.mem_ker, pow_one, map_pow, hg]
      exact hy2
    have hgC : g ∈ Subgroup.centralizer (V : Set G) := h.mem_of_pow_mem hOC hCK hgK hg2
    have hy1 : (y : ↥(autI hV (⊤ : Subgroup G))) = 1 := by
      rw [← hg]
      have : g ∈ (actA hV).ker := by rw [ker_actA]; exact hgC
      exact this
    have hy1' : y = 1 := Subtype.ext hy1
    rw [hy1', orderOf_one] at hy
    exact absurd hy (by norm_num)

end Bar

section FromFamily

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]
  {T : Subgroup G} {π : G →* SpecialLinearGroup (Fin 2) k}

theorem isSeed_of_e23 (h : SeedSetting T π) {V : Subgroup G} [V.Normal] (hV : IsElemAbelian 2 V)
    {I : Finset (Subgroup (MulAut (IntMod V hV)))}
    (hfam : CFSG.AGLEmbeddingD2.GN.E23FamGen (⊤ : Subgroup G) T V hV I) (hVE : V ≤ Ecore G)
    (hOC : CFSG.pCore 2 G ≤ Subgroup.centralizer (V : Set G))
    (hCK : Subgroup.centralizer (V : Set G) ≤ π.ker)
    (hJG : thompsonJ (⊤ : Subgroup G) ⊔ Subgroup.centralizer (V : Set G) ⊔ T = ⊤)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) (hJP : ¬ thompsonJ T ≤ CFSG.pCore 2 G) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : G →* SpecialLinearGroup (Fin 2) F)
      (ψ : Ecore G →* Multiplicative (Fin 2 → F)), IsSeed P ρ (Ecore G) ψ := by
  classical
  obtain ⟨hne, hJeq, hcomm, -, hcases, -, -⟩ := hfam
  obtain ⟨πb, hcomp, hsurj, hodd⟩ := exists_bar h hV hOC hCK
  haveI : Finite ↥(autI hV (⊤ : Subgroup G)) := Finite.of_surjective _ (actA_surjective hV)
  have hQ : ∀ (y : SpecialLinearGroup (Fin 2) k) (a : ℕ), y ^ 2 ^ a = 1 → y ^ 2 = 1 :=
    fun y a hy => sl2_sq_eq_one_of_pow_two_pow (MulEquiv.refl _) hy
  have hJA : autI hV (thompsonJ (⊤ : Subgroup G)) ≤ autI hV (⊤ : Subgroup G) := autI_mono hV le_top
  have hIA : ∀ L ∈ I, L ≤ autI hV (⊤ : Subgroup G) := fun L hL =>
    le_trans (hJeq ▸ le_iSup₂ (f := fun (L : Subgroup (MulAut (IntMod V hV))) (_ : L ∈ I) => L) L hL) hJA
  have hall : ∀ L ∈ I, ∃ n : ℕ, E2.IsL2Natural L (fixV (autI hV (twoResidual (⊤ : Subgroup G)))) n := by
    intro L hL
    rcases hcases L hL with hn | ⟨m, hm2, θ, -, -⟩
    · exact hn
    · exfalso
      have h4 : 4 ≤ 2 ^ m + 1 := by
        have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
        omega
      obtain ⟨x, hxL, hx4, hx2⟩ := exists_pow_four_eq_one_of_perm h4 θ
      have := pow_two_pow_of_odd_kernel πb hodd hQ (⟨x, hIA L hL hxL⟩ : ↥(autI hV (⊤ : Subgroup G))) 2
        (Subtype.ext (by simpa using hx4))
      exact hx2 (by simpa using congrArg Subtype.val this)
  haveI hJGn : (thompsonJ (⊤ : Subgroup G)).Normal :=
    Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 (B6.le_normalizer_thompsonJ (⊤ : Subgroup G)))
  have hAJ : ∀ a ∈ autI hV (⊤ : Subgroup G), ∃ j : ℕ,
      a ^ 2 ^ j ∈ autI hV (thompsonJ (⊤ : Subgroup G)) := by
    intro a ha
    obtain ⟨g, rfl⟩ := exists_actHom_eq hV ha
    obtain ⟨j, hj⟩ := exists_pow_mem_of_sup_eq_top
      (N := thompsonJ (⊤ : Subgroup G) ⊔ Subgroup.centralizer (V : Set G)) h.sylow.2.1 hJG g
    refine ⟨j, ?_⟩
    obtain ⟨m, hm, c, hc, hmc⟩ := Subgroup.mem_sup_of_normal_right.1 hj
    rw [← map_pow, ← hmc, map_mul, (actHom_eq_one_iff hV c).2 hc, mul_one, autI_eq_map_actHom]
    exact Subgroup.mem_map_of_mem _ hm
  have hinv : ∀ L ∈ I, ∃ x ∈ L, x ≠ 1 ∧ x ^ 2 = 1 := by
    intro L hL
    obtain ⟨n, hn1, F, hF, hFin, hcard, e, β, -⟩ := hall L hL
    haveI : Finite F := Finite.of_fintype F
    haveI : CharP F 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two hn1 (by rw [Nat.card_eq_fintype_card]; exact hcard)
    obtain ⟨x, hx1, hx2⟩ := sl2_exists_involution e
    exact ⟨x, x.2, fun h' => hx1 (Subtype.ext h'), by simpa using congrArg Subtype.val hx2⟩
  have hQ1 : ∀ (N : Subgroup (SpecialLinearGroup (Fin 2) k)) [N.Normal] (x : SpecialLinearGroup (Fin 2) k),
      x ∈ N → x ≠ 1 → x ^ 2 = 1 → N = ⊤ :=
    fun N _ x hx hx1 hx2 => sl2_normal_eq_top_of_involution (MulEquiv.refl _) N hx hx1 hx2
  have hQnc : ∃ a b : SpecialLinearGroup (Fin 2) k, a * b ≠ b * a :=
    sl2_not_commutative (MulEquiv.refl _)
  obtain ⟨L, hIL, hJL, hJA'⟩ := single_factor πb hsurj hodd hQ1 hQnc
    (autI hV (thompsonJ (⊤ : Subgroup G))) hJA (normal_subgroupOf_autI hV (thompsonJ (⊤ : Subgroup G)))
    hAJ I hne hIA hJeq hcomm hinv
  have hL : L ∈ I := by rw [hIL]; exact Finset.mem_singleton_self L
  obtain ⟨n, hn⟩ := hall L hL
  have hLA : L = autI hV (⊤ : Subgroup G) := hJL.symm.trans hJA'
  rw [hLA] at hn
  have hfr : (Subgroup.centralizer (V : Set G)).map (QuotientGroup.mk' (CFSG.pCore 2 G)) ≤
      frattini (G ⧸ CFSG.pCore 2 G) := (Subgroup.map_mono hCK).trans h.ker_map_le_frattini
  exact exists_isSeed_of_natural hV P hVE hOC hfr hn (by rw [hP]; exact hJP)

theorem exists_isSeed_of_setting (h : SeedSetting T π)
    (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJ : omegaOneCenterOf (thompsonJ T) ≤ Subgroup.centralizer (T : Set G))
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (ρ : G →* SpecialLinearGroup (Fin 2) F)
      (ψ : Ecore G →* Multiplicative (Fin 2 → F)), IsSeed P ρ (Ecore G) ψ := by
  haveI := CFSG.Adapters.certificate43_holds
  haveI : (VZ T ⊤).Normal := normal_VZ_top T
  obtain ⟨M, hmin⟩ := h.exists_minParabolic
  have hfam := CFSG.AGLEmbeddingD2.Tits.E23.famI_e23FamGen h.isElemAbelian_VZ hmin
    (CFSG.AGLEmbeddingD2.Tits.E23.minPar_of_minParabolic hmin) h.charTwo h.isTwoReducedIn_VZ
    (h.not_thompsonJ_le_centralizer_VZ hnc hJ)
  have hVE : VZ T ⊤ ≤ Ecore G := by
    intro v hv
    have hc := h.VZ_le_center_pCore hv
    rw [pCoreOf_top_eq_pCore_two] at hc
    exact CFSG.Quasithin.BlueprintB2.mem_centerTorsion_iff.mpr
      ⟨hc.1, fun x hx => Subgroup.mem_centralizer_iff.mp hc.2 x hx, h.isElemAbelian_VZ.2 v hv⟩
  exact isSeed_of_e23 h h.isElemAbelian_VZ hfam hVE h.pCore_le_centralizer_VZ
    (h.centralizer_VZ_le_ker hnc) (h.thompsonJ_sup_centralizer_sup_eq_top hnc hJ) P hP
    (h.not_thompsonJ_le_pCore hnc hJ)

end FromFamily

end CFSG.LocalAnalysis.UniquenessCase.UC22
