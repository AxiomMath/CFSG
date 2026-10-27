module

public import CFSG.Quasithin.Vol2.Ch10SecA312AJ
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.Quasithin.Vol2.Ch10SecA312LB
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

theorem eq_perfectCore_of_leviData {S : Type} [Group S] [Finite S] (hq : CFSG.IsQuasisimple S)
    {U : Subgroup S} {P : Fin 2 → Subgroup S}
    (hP : CFSG.QuasithinUnique.Setup.X6.ResidualOvergroupsAt S U P)
    (hLevi : ∀ j, Vol2Native.A312L.LeviData (P j)) {B : Subgroup S} (hB : B ∈ lFamily U)
    (hBtop : B ≠ ⊤) : ∃ j, B = perfectCore (P j) ∧ perfectCore (P j) ≠ ⊥ := by
  have hB' : B ∈ cComp (B ⊔ U) := hB
  have hne : B ⊔ U ≠ ⊤ := by
    intro htop
    rw [htop] at hB'
    exact hBtop (A321.cComp_eq_top_of_quasisimple hq hB')
  have hns : ¬ Group.IsSolvable ↥(B ⊔ U) := fun hs =>
    not_isSolvable_of_mem_cComp hB'
      (Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (le_of_mem_cComp hB' : B ≤ B ⊔ U))
        (Subgroup.inclusion_injective _))
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 (B ⊔ U) le_sup_right hne hns
  have hN' : perfectCore (B ⊔ U) = perfectCore (P j) := by
    rw [← Vol2Native.A312L.dInf_eq_perfectCore, ← Vol2Native.A312L.dInf_eq_perfectCore, hd]
  have hnb : perfectCore (P j) ≠ ⊥ := fun h =>
    hns ((isSolvable_iff_perfectCore_eq_bot _).mpr (hN'.trans h))
  rcases hLevi j with h | ⟨F, _, _, _, n, hn, hn2, g, hg, hker⟩
  · exact absurd h hnb
  · have hK4 : ∃ s : Finset F, s.card = 4 := by
      refine Vol2Native.A312L.exists_finset_card_four ?_
      rw [hn]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    have := Vol2Native.A312L.sl2_isSimple hK4
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable g.ker := by
      have := hker.isNilpotent
      infer_instance
    exact ⟨j, Vol2Native.A312L.lFamily_eq_of_perfectCore_eq hB hN'
      (Vol2Native.A312L.sl2_nonabelian hK4) g hg hsolv, hnb⟩

section D4

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)

local notation "τ₀" => σ.toRingHom
local notation "GL" => ModGL TwistTag.D4.tag K

include hσ3 in
theorem d4_center_a0
    {z : GL} (hzQ : z ∈ Q0 σ) (hzC : z ∈ Subgroup.centralizer (Q0 σ : Set GL)) :
    ∃ f : trialityFixedField K τ₀, z = ox₆ σ f := by
  obtain ⟨b, c, d, e, f, rfl⟩ := (mem_radical_a0_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q0 σ,
      ⁅ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hb : b = 0 := by
    have h1 := hcent _ (ox₅_mem_Q0 σ hσ3 (1 : trialityFixedField K τ₀))
    have e1 : ox₂ σ b * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₂ σ b * (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₅ σ 1) :=
      (((comm35 σ hσ3 c 1).mul_left (comm45 σ hσ3 d 1)).mul_left
        (commute_of_add (ox₅ σ) (ox₅_add σ hσ3) e 1)).mul_left (comm56 σ hσ3 1 f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), rel25 σ hσ3] at h1
    have := ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
    exact (mul_one b).symm.trans this
  subst hb
  have hc : c = 0 := by
    apply trace_nondeg σ hσ3
    intro t
    have h1 := hcent _ (ox₄_mem_Q0 σ hσ3 t)
    have e1 : ox₂ σ 0 * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        ox₂ σ 0 * ox₃ σ c * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0) (ox₄ σ t) := comm24 σ hσ3 0 t
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    have hAy : Commute (ox₂ σ 0) ⁅ox₃ σ c, ox₄ σ t⁆ := by
      rw [rel34 σ hσ3]; exact comm26 σ hσ3 0 _
    rw [e1, comm_sandwich hA hB hAy, rel34 σ hσ3] at h1
    exact ox₆_inj σ hσ3 (h1.trans (ox₆_zero σ hσ3).symm)
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₃_mem_Q0 σ hσ3 s)
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0) * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0) (ox₃ σ s) :=
      (comm23 σ hσ3 0 s).mul_left (commute_of_add (ox₃ σ) (ox₃_add σ hσ3) 0 s)
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₃ σ s) :=
      (comm35 σ hσ3 s e).symm.mul_left (comm36 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₃ σ s⁆ = (ox₆ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel34 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0) ⁅ox₄ σ d, ox₃ σ s⁆ := by
      rw [hinv]
      exact ((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (trialityTrace K τ₀ hσ3 (s * d)) = 1 := inv_eq_one.1 h1
    exact ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
  subst hd
  have he : e = 0 := by
    have h1 := hcent _ (ox₂_mem_Q0 σ hσ3 (1 : trialityFixedField K τ₀))
    have e1 : ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0 * ox₅ σ e * ox₆ σ f =
        (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) * ox₅ σ e * ox₆ σ f := by group
    have hA : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) (ox₂ σ 1) :=
      (((commute_of_add (ox₂ σ) (ox₂_add σ hσ3) 0 1).mul_left (comm23 σ hσ3 1 0).symm).mul_left
        (comm24 σ hσ3 1 0).symm)
    have hB : Commute (ox₆ σ f) (ox₂ σ 1) := (comm26 σ hσ3 1 f).symm
    have hinv : ⁅ox₅ σ e, ox₂ σ 1⁆ = (ox₆ σ (1 * e))⁻¹ := by
      rw [← commutatorElement_inv, rel25 σ hσ3]
    have hAy : Commute (ox₂ σ 0 * ox₃ σ 0 * ox₄ σ 0) ⁅ox₅ σ e, ox₂ σ 1⁆ := by
      rw [hinv]
      exact (((comm26 σ hσ3 0 _).mul_left (comm36 σ hσ3 0 _)).mul_left
        (comm46 σ hσ3 0 _)).inv_right
    rw [e1, comm_sandwich hA hB hAy, hinv] at h1
    have h2 : ox₆ σ (1 * e) = 1 := inv_eq_one.1 h1
    have := ox₆_inj σ hσ3 (h2.trans (ox₆_zero σ hσ3).symm)
    exact (one_mul e).symm.trans this
  subst he
  exact ⟨f, by rw [ox₂_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3, ox₅_zero σ hσ3]; simp⟩

include hσ3 in
theorem d4_center_a1
    {z : GL} (hzQ : z ∈ Q1 σ) (hzC : z ∈ Subgroup.centralizer (Q1 σ : Set GL)) :
    ∃ e f : trialityFixedField K τ₀, z = ox₅ σ e * ox₆ σ f := by
  obtain ⟨a, c, d, e, f, rfl⟩ := (mem_radical_a1_iff σ hσ3).1 hzQ
  have hcent : ∀ g ∈ Q1 σ,
      ⁅ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f, g⁆ = 1 := fun g hg =>
    commutatorElement_eq_one_iff_mul_comm.2 (Subgroup.mem_centralizer_iff.1 hzC g hg).symm
  have hac : ∀ t : K, trialityTrace K τ₀ hσ3 (a * t) = 0 ∧
      trialityTrace K τ₀ hσ3 (c * t) = 0 := by
    intro t
    have h1 := hcent _ (ox₄_mem_Q1 σ hσ3 t)
    have e1 : ox₁ σ a * ox₃ σ c * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * (ox₁ σ a * ox₃ σ c) * (ox₄ σ d * ox₅ σ e * ox₆ σ f) := by group
    have hB : Commute (ox₄ σ d * ox₅ σ e * ox₆ σ f) (ox₄ σ t) :=
      ((commute_of_add (ox₄ σ) (ox₄_add σ hσ3) d t).mul_left (comm45 σ hσ3 t e).symm).mul_left
        (comm46 σ hσ3 t f).symm
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _)] at h1
    have e2 : ⁅ox₁ σ a * ox₃ σ c, ox₄ σ t⁆ =
        ox₁ σ a * ⁅ox₃ σ c, ox₄ σ t⁆ * (ox₁ σ a)⁻¹ * ⁅ox₁ σ a, ox₄ σ t⁆ := by
      simp only [commutatorElement_def]; group
    rw [e2, rel34 σ hσ3, rel14 σ hσ3, (comm16 σ hσ3 a _).eq, mul_inv_cancel_right] at h1
    have h2 : ox₅ σ (trialityTrace K τ₀ hσ3 (a * t)) * ox₆ σ (trialityTrace K τ₀ hσ3 (c * t)) =
        1 := by
      rw [(comm56 σ hσ3 _ _).eq]; exact h1
    exact five_six_eq_one σ hσ3 h2
  have ha : a = 0 := trace_nondeg σ hσ3 a (fun t => (hac t).1)
  have hc : c = 0 := trace_nondeg σ hσ3 c (fun t => (hac t).2)
  subst ha
  subst hc
  have hd : d = 0 := by
    apply trace_nondeg' σ hσ3
    intro s
    have h1 := hcent _ (ox₁_mem_Q1 σ hσ3 s)
    have e1 : ox₁ σ 0 * ox₃ σ 0 * ox₄ σ d * ox₅ σ e * ox₆ σ f =
        1 * ox₄ σ d * (ox₅ σ e * ox₆ σ f) := by
      rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3]; group
    have hB : Commute (ox₅ σ e * ox₆ σ f) (ox₁ σ s) :=
      (comm15 σ hσ3 s e).symm.mul_left (comm16 σ hσ3 s f).symm
    have hinv : ⁅ox₄ σ d, ox₁ σ s⁆ = (ox₅ σ (trialityTrace K τ₀ hσ3 (s * d)))⁻¹ := by
      rw [← commutatorElement_inv, rel14 σ hσ3]
    rw [e1, comm_sandwich (Commute.one_left _) hB (Commute.one_left _), hinv] at h1
    exact ox₅_inj σ hσ3 ((inv_eq_one.1 h1).trans (ox₅_zero σ hσ3).symm)
  subst hd
  exact ⟨e, f, by rw [ox₁_zero σ hσ3, ox₃_zero σ hσ3, ox₄_zero σ hσ3]; simp⟩

include hσ3 in
theorem d4_pos_comm_six
    (f : trialityFixedField K τ₀) {u : GL} (hu : u ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀) :
    Commute u (ox₆ σ f) := by
  obtain ⟨a, b, c, d, e, f', rfl⟩ := coord_exists σ hσ3 hu
  exact (((((comm16 σ hσ3 a f).mul_left (comm26 σ hσ3 b f)).mul_left (comm36 σ hσ3 c f)).mul_left
    (comm46 σ hσ3 d f)).mul_left (comm56 σ hσ3 e f)).mul_left
      (commute_of_add (ox₆ σ) (ox₆_add σ hσ3) f' f)

omit [Finite K] [CharP K 2] in
open Matrix in
theorem d4_orbitY_comm_six
    (c : orbitField TwistTag.D4 K τ₀ fa0) (f : trialityFixedField K τ₀) :
    Commute (orbitY TwistTag.D4 K τ₀ fa0 c : GL) (ox₆ σ f) := by
  have horth : ∀ j : Fin TwistTag.D4.tag.rank, j ≠ ⟨2, by decide⟩ →
      (-Pi.single j (1 : ℤ)) ⬝ᵥ (TwistTag.D4.tag.symmetrizedCartan *ᵥ trialityRoot 5) = 0 := by
    decide +kernel
  have hj : ∀ k ∈ List.range (TwistTag.D4.orbit fa0).card,
      (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin fa0) ≠ ⟨2, by decide⟩ := by
    rw [orbit_card_fa0, orbitMin_fa0]
    decide
  rw [coe_orbitY]
  refine Commute.list_prod_left _ _ fun x hx => ?_
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
  rw [← pinnedX_neg_single]
  exact commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.D4) K (isRoot_neg_single _ _)
    (isRoot_trialityRoot' 5) (horth _ (hj k hk)) _ (f : K)

include hσ3 in
theorem d4_perfectCore_le_centralizer
    (f : trialityFixedField K τ₀) :
    perfectCore (P0 σ) ≤ Subgroup.centralizer {ox₆ σ f} := by
  rw [P0, Vol2Native.A312L.fixed_perfectCore_eq σ fa0]
  refine (perfectCore_le _).trans (sup_le (fun u hu => ?_)
    ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ?_)))
  · exact Subgroup.mem_centralizer_singleton_iff.2 (d4_pos_comm_six σ hσ3 f hu).eq
  · obtain ⟨R, -, -, -, hRW, hRn, hrange, -⟩ :=
      exceptional_fixed_rank_one_central_image TwistTag.D4 K τ₀ fa0
    have hle : R.range ≤ Subgroup.centralizer {ox₆ σ f} := by
      rw [hrange]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · show (orbitX TwistTag.D4 K τ₀ fa0 c : GL) ∈ Subgroup.centralizer {ox₆ σ f}
        rw [orbitX_fa0_eq σ c]
        exact Subgroup.mem_centralizer_singleton_iff.2 (comm16 σ hσ3 _ f).eq
      · exact Subgroup.mem_centralizer_singleton_iff.2 (d4_orbitY_comm_six σ c f).eq
    rw [← hRn, ← hRW]
    exact hle ⟨WSL, rfl⟩

include hσ3 in
theorem d4_eq_one_a1
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K τ₀)) {z : GL}
    (hzU : z ∈ graphFixedPosUnipotent TwistTag.D4 K τ₀)
    (hzB : ∀ x ∈ perfectCore (P1 σ), z * x = x * z) : z = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ3' : σ ^ 3 = 1 := pow_three_equiv σ hσ3
  have hU := isPGroup_posUnipotent σ hσ3
  obtain ⟨hQP, -, -, hsc⟩ := library_facts σ fa1 singleton_ne_univ_fa1
  have hQB : Q1 σ ≤ perfectCore (P1 σ) :=
    (generation_a1 σ hσ3 hU hk4).trans (commutator_perfectCore_le_of_le hQP)
  have hzC : z ∈ Subgroup.centralizer (Q1 σ : Set GL) :=
    Subgroup.mem_centralizer_iff.2 fun q hq => (hzB q (hQB hq)).symm
  have hzP : z ∈ P1 σ := graphFixedRootBorel_le_graphFixedParabolic TwistTag.D4 K τ₀ {fa1}
    (graphFixedPosUnipotent_le_graphFixedRootBorel hzU)
  obtain ⟨e, f, rfl⟩ := d4_center_a1 σ hσ3 (hsc ⟨hzP, hzC⟩) hzC
  have hL4 : ∃ s : Finset ↥(orbitField TwistTag.D4 K τ₀ fa1), s.card = 4 := by
    have hc : 4 ≤ Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) := by
      have : Nat.card ↥(orbitField TwistTag.D4 K τ₀ fa1) =
          Nat.card ↥(trialityFixedField K τ₀) :=
        Nat.card_congr (Equiv.subtypeEquivRight fun c =>
          (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := τ₀)).symm)
      rw [this]; exact hk4
    exact Vol2Native.A312L.exists_finset_card_four hc
  obtain ⟨R, -, hRH, -, hMP, -, -⟩ := levi_package σ fa1 hU hL4
  have hH : ∀ b : (trialityFixedField K τ₀)ˣ,
      trialityTorusHom σ (1, b) ∈ perfectCore (P1 σ) := by
    intro b
    have e := trialityTorusHom_eq_orbitH hσ3' 1 b
    have h1 : trialityOuterParam hσ3' (1 : Kˣ) = 1 := Units.ext (Subtype.ext rfl)
    rw [h1, orbitH_one', one_mul] at e
    rw [e]
    exact hMP ⟨HSL _, hRH _⟩
  obtain ⟨b₀, hb₀⟩ := exists_units_ne_one' hk4
  have hd := hzB _ (hH b₀)
  have E0 : trialityTorusHom σ (1, b₀) * (ox₅ σ e * ox₆ σ f) * (trialityTorusHom σ (1, b₀))⁻¹ =
      ox₅ σ e * ox₆ σ f := by
    rw [← hd]
    group
  have E : ox₅ σ (((b₀⁻¹ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * e) *
      ox₆ σ (((b₀ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * f) =
        ox₅ σ e * ox₆ σ f := by
    rw [← torus_b_ox₅ σ hσ3 b₀ e, ← torus_b_ox₆ σ hσ3 b₀ f, ← E0]
    group
  have hinv : ∀ x : trialityFixedField K τ₀, x + x = 0 := fun x =>
    Subtype.ext (by push_cast; exact CharTwo.add_self_eq_zero _)
  have key : ox₅ σ (((b₀⁻¹ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * e + e) *
      ox₆ σ (((b₀ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * f + f) = 1 := by
    calc _ = ox₅ σ e * (ox₅ σ (((b₀⁻¹ : (trialityFixedField K τ₀)ˣ) :
          trialityFixedField K τ₀) * e) *
            ox₆ σ (((b₀ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) * f)) *
              ox₆ σ f := by
          rw [ox₅_add σ hσ3, ox₆_add σ hσ3,
            (commute_of_add (ox₅ σ) (ox₅_add σ hσ3) _ e).eq]
          group
      _ = ox₅ σ e * ox₅ σ e * (ox₆ σ f * ox₆ σ f) := by rw [E]; group
      _ = 1 := by
          rw [← ox₅_add σ hσ3, ← ox₆_add σ hσ3, hinv, hinv, ox₅_zero σ hσ3, ox₆_zero σ hσ3,
            one_mul]
  obtain ⟨h1, h2⟩ := five_six_eq_one σ hσ3 key
  have hw1 : ((((b₀ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) : K))⁻¹ ≠ 1 :=
    fun h' => hb₀ (Units.ext (Subtype.ext (inv_eq_one.1 h')))
  have hw2 : (((b₀ : (trialityFixedField K τ₀)ˣ) : trialityFixedField K τ₀) : K) ≠ 1 :=
    fun h' => hb₀ (Units.ext (Subtype.ext h'))
  have h1' := congrArg Subtype.val h1
  have h2' := congrArg Subtype.val h2
  push_cast at h1' h2'
  have he : e = 0 := Subtype.ext (eq_zero_of_mul_add_self hw1 h1')
  have hf : f = 0 := Subtype.ext (eq_zero_of_mul_add_self hw2 h2')
  rw [he, hf, ox₅_zero σ hσ3, ox₆_zero σ hσ3, one_mul]

end D4

section D4Main

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4

variable {K : Type} [Field K] [Finite K]

theorem zcentFor_D4
    {f : ℕ} (hf : 1 ≤ f) (σ : K ≃+* K) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq : CFSG.IsQuasisimple ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
    ZCentFor ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 := by
    refine RingHom.ext fun c => ?_
    have hc : c ^ ((2 ^ f) ^ 3) = c := by
      have : Fintype K := Fintype.ofFinite K
      rw [← hK, Nat.card_eq_fintype_card]
      exact FiniteField.pow_card c
    change σ (σ (σ c)) = c
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    convert hc using 2
    ring
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK3]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.D4.tag).length
  obtain ⟨PU, hPU⟩ := (exceptional_fixed_Sylow_opposition TwistTag.D4 K 2 σ w₀ hw₀).1
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  have hUsyl : IsSylowTwoOf (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    refine isSylowTwoOf_iff_isSylowOf.2 ⟨PU, ?_⟩
    rw [hPU, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hUC]
  have hU := isPGroup_posUnipotent σ hσ3
  refine ZCentFor.of_sylow _ (isSylowTwoOf_subgroupOf_top hUsyl) fun B hB hBtop z => ?_
  obtain ⟨j, rfl, hne⟩ := eq_perfectCore_of_leviData hq (triality_residualOvergroupsAt σ)
    (fun j => Vol2Native.A312L.fixed_leviData σ (d4Index j) hUsyl.2.1) hB hBtop
  have hPC : ∀ a, graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := fun a => graphFixedParabolic_le _ _ _ _
  have hup : ∀ a, ∀ x ∈ perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}),
      ∃ y ∈ perfectCore ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
          (y : ModGL TwistTag.D4.tag K) = x := fun a x hx => by
    rw [← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC a)] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  intro hzT hz1 _ hzB
  have hj : d4Index j = fa0 ∨ d4Index j = fa1 := by
    have h2 : ∀ x : Fin TwistTag.D4.foldedTag.rank, x = fa0 ∨ x = fa1 := by decide
    exact h2 _
  rcases hj with hj | hj <;> rw [hj] at hzB hne ⊢
  · intro v hv hvc _ b hb
    obtain ⟨hQP, hPN, hQ2, hsc⟩ := library_facts σ fa0 singleton_ne_univ_fa0
    have hQB : Q0 σ ≤ perfectCore (P0 σ) :=
      (generation_a0 σ hσ3 hU hK4).trans (commutator_perfectCore_le_of_le hQP)
    have hQO := subgroupOf_le_pCoreOf (C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (B := perfectCore ((P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
      hQ2 (fun q hq => hup fa0 q (hQB hq))
      (fun b hb => hPN (Subgroup.mem_subgroupOf.1 (perfectCore_le _ hb)))
    have hvC : (v : ModGL TwistTag.D4.tag K) ∈
        Subgroup.centralizer (Q0 σ : Set (ModGL TwistTag.D4.tag K)) :=
      Subgroup.mem_centralizer_iff.2 fun q hq =>
        congrArg Subtype.val (hvc ⟨q, hPC fa0 (hQP hq)⟩ (hQO hq))
    have hvB : v ∈ perfectCore ((P0 σ).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hv
    have hvQ := hsc ⟨Subgroup.mem_subgroupOf.1 (perfectCore_le _ hvB), hvC⟩
    obtain ⟨f', hf'⟩ := d4_center_a0 σ hσ3 hvQ hvC
    have hb' : (b : ModGL TwistTag.D4.tag K) ∈ perfectCore (P0 σ) := by
      rw [← Vol2Native.A312L.perfectCore_map_subgroupOf (hPC fa0)]
      exact ⟨b, hb, rfl⟩
    refine Subtype.ext ?_
    show (b : ModGL TwistTag.D4.tag K) * v = v * b
    rw [hf']
    exact Subgroup.mem_centralizer_singleton_iff.1 (d4_perfectCore_le_centralizer σ hσ3 f' hb')
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 ^ m := by
      have : Fintype ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) := Fintype.ofFinite _
      obtain ⟨n, -, hn⟩ := FiniteField.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) 2
      exact ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn⟩
    have hcard : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) =
        Nat.card ↥(trialityFixedField K σ.toRingHom) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (mem_orbitField_D4_one σ).trans (mem_trialityFixedField (K := K) (σ := σ.toRingHom)).symm)
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · have hpos : 1 < Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) := Finite.one_lt_card
      have h2 : Nat.card ↥(orbitField TwistTag.D4 K σ.toRingHom fa1) = 2 := by
        rcases m with _ | _ | m
        · rw [hm] at hpos; norm_num at hpos
        · rw [hm]; norm_num
        · omega
      apply hne
      apply Subgroup.map_injective (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective
      rw [Vol2Native.A312L.perfectCore_map_subgroupOf (hPC fa1),
        perfectCore_bot_of_card_two σ fa1 hU h2, Subgroup.map_bot]
    · have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := by
        rw [← hcard, hm]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
      refine hz1 (Subtype.ext (d4_eq_one_a1 σ hσ3 hk4 hzT fun x hx => ?_))
      obtain ⟨b, hb, rfl⟩ := hup fa1 x hx
      exact congrArg Subtype.val (hzB b hb)

end D4Main

theorem zcentFor_of_is3D4
    {X : Type} [Group X] [Finite X] (hq : CFSG.IsQuasisimple X) {f : ℕ} (h : Is3D4 2 f X) :
    ZCentFor X := by
  obtain ⟨hf, K, _, _, σ, hK, hσ, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_triality_model h
  exact ZCentFor.of_mulEquiv e
    (zcentFor_D4 hf σ hK hσ (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq))

end CFSG.Quasithin.Vol2.Ch10.A312A
