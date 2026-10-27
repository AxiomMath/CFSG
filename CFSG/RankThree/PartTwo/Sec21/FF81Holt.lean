module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.Holt.H78.Defs
import CFSG.Holt.H78.SectionsStar
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.Assembly.ComponentTypeDefs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open MulAction CFSG.Holt.H78 CFSG.Holt.General
open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedSp StatedProj)

theorem card_of_model_sp6 {H : Type} [Group H] (h : StatedClassicalModel H .PSp 3 2 1) :
    Nat.card H = 1451520 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK]; rfl)
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo, hK]
  decide

theorem factorial_ne_2903040 (m : ℕ) : Nat.factorial m ≠ 2903040 := by
  intro h
  rcases le_or_gt m 9 with hm | hm
  · have := Nat.factorial_le hm
    rw [h] at this
    exact absurd this (by decide)
  · have := Nat.factorial_le (show 10 ≤ m by omega)
    rw [h] at this
    exact absurd this (by decide)

section Core

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}

theorem not_isSolvable_of_card [IsSimpleGroup M] {z : M} (hz : orderOf z = 2)
    (hcard : Nat.card M = 1451520) : ¬ Group.IsSolvable M := by
  intro hsol
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable (G := M)).mpr hsol
  have hN : (Subgroup.zpowers z).Normal :=
    ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  rcases hN.eq_bot_or_eq_top with h | h
  · have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  · have h1 := Nat.card_zpowers z
    rw [h, Subgroup.card_top, hcard, hz] at h1
    exact absurd h1 (by norm_num)

theorem false_of_holtData [IsSimpleGroup M] (hcard : Nat.card M = 1451520) {z : X}
    (hz2 : orderOf z = 2) (hzM : z ∈ M)
    (hfix : ∀ ω : X ⧸ M, z • ω = ω ↔ ω = ((1 : X) : X ⧸ M))
    (h3 : 3 ≤ Nat.card (X ⧸ M)) (D : HoltData X (X ⧸ M)) : False := by
  set α : X ⧸ M := ((1 : X) : X ⧸ M) with hα
  have hz2' : orderOf (⟨z, hzM⟩ : M) = 2 := by rw [Subgroup.orderOf_mk]; exact hz2
  have hstab : stabilizer X α = M := MulAction.stabilizer_quotient M
  have hmα : ∀ m ∈ M, m • α = α := fun m hm => by
    rw [← mem_stabilizer_iff, hstab]
    exact hm
  have hzJ : z ∈ longInv X (X ⧸ M) :=
    ⟨hz2, ⟨α, (hfix α).mpr rfl, fun ω hω => (hfix ω).mp hω⟩⟩
  have hMH : M ≤ jHull X (X ⧸ M) := by
    have hN : ((jHull X (X ⧸ M)).subgroupOf M).Normal := (jHull_normal).subgroupOf M
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      have : (⟨z, hzM⟩ : M) ∈ (jHull X (X ⧸ M)).subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr (mem_jHull_of_mem_longInv hzJ)
      rw [h, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hz2'
      exact absurd hz2' (by norm_num)
    · exact Subgroup.subgroupOf_eq_top.mp h
  have hzO : z ∉ jOddCore X (X ⧸ M) := fun h => by
    have h1 : orderOf z ∣ Nat.card (jOddCore X (X ⧸ M)) := Subgroup.orderOf_dvd_natCard _ h
    rw [hz2] at h1
    exact (Nat.not_even_iff_odd.mpr odd_card_jOddCore) (even_iff_two_dvd.mpr h1)
  rcases isEmpty_or_nonempty D.ι with hι | ⟨⟨i⟩⟩
  ·
    have hall : ∀ ω : X ⧸ M, ω ∈ orbit (jOddCore X (X ⧸ M)) α := fun ω =>
      (D.coord_eq_iff α ω).mp (funext fun j => isEmptyElim j)
    by_cases hO : jOddCore X (X ⧸ M) = ⊥
    · have hsub : ∀ ω : X ⧸ M, ω = α := fun ω => by
        obtain ⟨o, ho⟩ := hall ω
        have : (o : X) = 1 := (Subgroup.eq_bot_iff_forall _).mp hO _ o.2
        rw [← ho]
        show o • α = α
        rw [Subgroup.smul_def, this, one_smul]
      have : Subsingleton (X ⧸ M) := ⟨fun a b => (hsub a).trans (hsub b).symm⟩
      have := Finite.card_le_one_iff_subsingleton.mpr this
      omega
    · have hK : jOrbitKernel X (X ⧸ M) = jHull X (X ⧸ M) := by
        refine le_antisymm (jOrbitKernel_le_jHull) fun g hg => mem_jOrbitKernel.mpr ⟨hg, ?_⟩
        intro ω
        have huniv : orbit (jOddCore X (X ⧸ M)) ω = Set.univ := by
          refine Set.eq_univ_of_forall fun ω' => ?_
          rw [orbit_eq_iff.mpr (hall ω)]
          exact hall ω'
        rw [huniv, Set.smul_set_univ]
      have h2 := (D.ker_inner fun j => isEmptyElim j).2 hO
      rw [hK] at h2
      have hle : (jOddCore X (X ⧸ M)).relIndex M ≤ 2 :=
        h2 ▸ Subgroup.relIndex_le_of_le_right hMH (by omega)
      have hN : ((jOddCore X (X ⧸ M)).subgroupOf M).Normal := (jOddCore_normal).subgroupOf M
      rcases hN.eq_bot_or_eq_top with h | h
      · rw [Subgroup.relIndex, h, Subgroup.index_bot, hcard] at hle
        omega
      · exact hzO (Subgroup.subgroupOf_eq_top.mp h hzM)
  ·
    set F := factorImage X (X ⧸ M) (D.L i) (D.ρ i) with hF
    set c := D.coord α i with hc
    set φ : M →* Equiv.Perm (D.Ψc i) := (D.ρ i).comp (Subgroup.inclusion hMH) with hφ
    have hφc : ∀ m : M, φ m c = c := fun m => by
      have h := D.coord_smul (Subgroup.inclusion hMH m) α i
      simp only [Subgroup.coe_inclusion, hmα m m.2] at h
      exact h.symm
    have hφF : ∀ m : M, ∀ x ∈ F, φ m * x * (φ m)⁻¹ ∈ F := by
      intro m x hx
      obtain ⟨h, hhL, rfl⟩ := mem_factorImage.mp hx
      refine mem_factorImage.mpr ⟨Subgroup.inclusion hMH m * h * (Subgroup.inclusion hMH m)⁻¹,
        ?_, by simp only [hφ, MonoidHom.comp_apply, map_mul, map_inv]⟩
      have hn := D.le_normalizer i (hMH m.2)
      simpa using (Subgroup.mem_normalizer_iff.mp hn h).mp hhL
    have hFc : ∀ x ∈ F, x c = c → x ∈ φ.range := by
      intro x hx hxc
      obtain ⟨h, hhL, rfl⟩ := mem_factorImage.mp hx
      have hco : D.coord α = D.coord ((h : X) • α) := by
        funext j
        rw [D.coord_smul]
        by_cases hj : j = i
        · subst hj
          exact hxc.symm
        · have hk : h ∈ (D.ρ j).ker :=
            D.le_ker i j (Ne.symm hj) (Subgroup.mem_subgroupOf.mpr hhL)
          rw [MonoidHom.mem_ker.mp hk]
          rfl
      obtain ⟨o, ho⟩ := (D.coord_eq_iff α _).mp hco
      have ho' : (o : X) • α = (h : X) • α := ho
      have hm : (o : X)⁻¹ * h ∈ M := hstab.le (mem_stabilizer_iff.mpr (by
        rw [mul_smul, ← ho', inv_smul_smul]))
      have hoH : (o : X) ∈ jHull X (X ⧸ M) := jOddCore_le_jHull o.2
      have hρo : D.ρ i ⟨o, hoH⟩ = 1 := by
        have h1 : (⟨o, hoH⟩ : jHull X (X ⧸ M)) ∈ (jOddCore X (X ⧸ M)).subgroupOf (jHull X _) :=
          Subgroup.mem_subgroupOf.mpr o.2
        rw [← D.inf_ker i] at h1
        exact h1.2
      refine ⟨⟨_, hm⟩, ?_⟩
      have he : Subgroup.inclusion hMH ⟨_, hm⟩ = (⟨o, hoH⟩ : jHull X (X ⧸ M))⁻¹ * h :=
        Subtype.ext (by simp)
      simp only [hφ, MonoidHom.comp_apply, he, map_mul, map_inv, hρo, inv_one, one_mul]
    set P : Subgroup (Equiv.Perm (D.Ψc i)) := (stabilizer F c).map F.subtype with hP
    have hmemP : ∀ x, x ∈ P ↔ x ∈ F ∧ x c = c := fun x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨hx, hxc⟩
        exact ⟨⟨x, hx⟩, hxc, rfl⟩
    have hcardP : Nat.card P = Nat.card (stabilizer F c) :=
      Subgroup.card_map_of_injective F.subtype_injective
    have htrans : IsPretransitive F (D.Ψc i) := by
      rcases D.factor i with ⟨hA, h7⟩ | ⟨q, e, hB⟩
      · have hA' : F = alternatingGroup (D.Ψc i) := hA
        have := alternatingGroup.isPretransitive_of_three_le_card (D.Ψc i)
          (by rw [Nat.card_eq_fintype_card]; omega)
        exact ⟨fun a b => by
          obtain ⟨g, hg⟩ := exists_smul_eq (alternatingGroup (D.Ψc i)) a b
          exact ⟨⟨g, by rw [hA']; exact g.2⟩, hg⟩⟩
      · have := hB.isPretransitive
        exact ⟨fun a b => by
          obtain ⟨g, hg⟩ := exists_smul_eq (⊤ : Subgroup F) a b
          exact ⟨g, hg⟩⟩
    have horbit : Nat.card (stabilizer F c) * Nat.card (D.Ψc i) = Nat.card F := by
      rw [← Subgroup.card_mul_index (stabilizer F c), index_stabilizer, orbit_eq_univ,
        Set.ncard_univ]
    have hPne : P ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card (stabilizer F c) = 1 := by rw [← hcardP, hbot, Subgroup.card_bot]
      rw [h1, one_mul] at horbit
      rcases D.factor i with ⟨hA, h7⟩ | ⟨q, e, hB⟩
      · have : Nontrivial (D.Ψc i) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        have h2 := two_mul_card_alternatingGroup (α := D.Ψc i)
        rw [Fintype.card_perm, ← Nat.card_eq_fintype_card (α := alternatingGroup (D.Ψc i)),
          ← hA, ← horbit, Nat.card_eq_fintype_card] at h2
        set n := Fintype.card (D.Ψc i)
        have h3' : 2 * n < Nat.factorial n := by
          obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
          rw [hk, Nat.factorial_succ]
          have : 2 < Nat.factorial k :=
            lt_of_lt_of_le (by decide) (Nat.factorial_le (show 3 ≤ k by omega))
          nlinarith
        omega
      · have hodd := hB.odd_card
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        obtain ⟨Q⟩ : Nonempty (Sylow 2 (⊤ : Subgroup F)) := inferInstance
        have hQ := ((hB.benderBorel Q).2.2.2.2)
        obtain ⟨-, h2, h1, -⟩ := hB.params
        have hdvd : 2 ∣ Nat.card F := by
          rw [← Subgroup.card_top (G := F)]
          exact (hQ ▸ dvd_pow h2 (by omega)).trans (Subgroup.card_subgroup_dvd_card _)
        rw [← horbit] at hdvd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    have hPle : P ≤ φ.range := fun x hx => hFc x ((hmemP x).mp hx).1 ((hmemP x).mp hx).2
    have hQ : (P.comap φ).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, hmemP] at *
      refine ⟨hφF g _ hn.1, ?_⟩
      have h1 : (φ g)⁻¹ c = c := Equiv.Perm.inv_eq_iff_eq.mpr (hφc g).symm
      simp only [Equiv.Perm.mul_apply]
      rw [h1, hn.2, hφc g]⟩
    rcases hQ.eq_bot_or_eq_top with h | h
    · apply hPne
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨m, rfl⟩ := hPle hx
      have : m ∈ P.comap φ := hx
      rw [h, Subgroup.mem_bot] at this
      rw [this, map_one]
      exact Subgroup.one_mem _
    · have hrange : φ.range = P := le_antisymm (fun x ⟨m, hm⟩ => hm ▸ (by
        have : m ∈ P.comap φ := h ▸ Subgroup.mem_top m
        exact this)) hPle
      have hinj : Function.Injective φ := by
        rcases (φ.normal_ker).eq_bot_or_eq_top with hk | hk
        · exact (MonoidHom.ker_eq_bot_iff φ).mp hk
        · exfalso
          apply hPne
          rw [← hrange, eq_bot_iff]
          rintro x ⟨m, rfl⟩
          have : m ∈ φ.ker := hk ▸ Subgroup.mem_top m
          exact (MonoidHom.mem_ker.mp this) ▸ Subgroup.one_mem _
      have hcardM : Nat.card M = Nat.card (stabilizer F c) := by
        rw [← hcardP, ← hrange]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv)
      rcases D.factor i with ⟨hA, h7⟩ | ⟨q, e, hB⟩
      · have : Nontrivial (D.Ψc i) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
        have h2 := two_mul_card_alternatingGroup (α := D.Ψc i)
        rw [Fintype.card_perm, ← Nat.card_eq_fintype_card (α := alternatingGroup (D.Ψc i)),
          ← hA, ← horbit, ← hcardM, hcard, Nat.card_eq_fintype_card] at h2
        set n := Fintype.card (D.Ψc i)
        obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [hk, Nat.factorial_succ] at h2
        exact factorial_ne_2903040 k (by nlinarith)
      · have hsol : Group.IsSolvable (stabilizer F c) := by
          have := hB.isSolvable_stabilizer_inf c
          rwa [inf_top_eq] at this
        apply not_isSolvable_of_card hz2' hcard
        have hmP : ∀ m : M, φ m ∈ P := fun m => hrange.le (MonoidHom.mem_range.mpr ⟨m, rfl⟩)
        let ψ : M →* stabilizer F c :=
          { toFun := fun m => ⟨⟨φ m, ((hmemP _).mp (hmP m)).1⟩, ((hmemP _).mp (hmP m)).2⟩
            map_one' := by ext; simp
            map_mul' := fun a b => by ext; simp }
        exact solvable_of_solvable_injective (f := ψ) fun a b hab =>
          hinj (congrArg (fun y : stabilizer F c => ((y : F) : Equiv.Perm (D.Ψc i))) hab)

end Core

theorem kf_holtThm1_of_holtTheorem1 (hH : HoltTheorem1) : KF_HoltThm1 := by
  intro X _ _ M hmod z hz2 hzM hS hfix
  have : IsSimpleGroup M :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp M 3 2 1 hmod
  have hcard := card_of_model_sp6 hmod
  have hzα : z • ((1 : X) : X ⧸ M) = ((1 : X) : X ⧸ M) := by
    have : z ∈ stabilizer X ((1 : X) : X ⧸ M) := by rw [MulAction.stabilizer_quotient]; exact hzM
    exact this
  have hfix' : ∀ ω : X ⧸ M, z • ω = ω ↔ ω = ((1 : X) : X ⧸ M) := fun ω =>
    ⟨fun h => hfix.unique h hzα, fun h => h ▸ hzα⟩
  by_contra hne
  have hsub : ¬ ∀ g : X, ((g : X) : X ⧸ M) = ((1 : X) : X ⧸ M) := fun h => hne <| by
    refine eq_top_iff.mpr fun g _ => ?_
    have := QuotientGroup.eq.mp (h g)
    simpa using this
  have hNc : (M.normalCore.subgroupOf M).Normal := (Subgroup.normalCore_normal M).subgroupOf M
  rcases hNc.eq_bot_or_eq_top with hb | ht
  · have hcore : M.normalCore = ⊥ := by
      refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : (⟨x, M.normalCore_le hx⟩ : M) ∈ M.normalCore.subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [hb, Subgroup.mem_bot] at hx'
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hx')
    have : FaithfulSMul X (X ⧸ M) := ⟨fun {a b} hab => by
      have hm : a⁻¹ * b ∈ M.normalCore := show ∀ g : X, g * (a⁻¹ * b) * g⁻¹ ∈ M from fun g => by
        have h1 := hab ((g⁻¹ : X) : X ⧸ M)
        rw [MulAction.Quotient.smul_coe, MulAction.Quotient.smul_coe, QuotientGroup.eq] at h1
        simpa [mul_assoc] using h1
      rw [hcore, Subgroup.mem_bot, inv_mul_eq_one] at hm
      exact hm⟩
    have hpre : IsPretransitive X (X ⧸ M) := ⟨fun a b => by
      induction a using QuotientGroup.induction_on with | H a => ?_
      induction b using QuotientGroup.induction_on with | H b => ?_
      exact ⟨b * a⁻¹, by rw [MulAction.Quotient.smul_coe, smul_eq_mul, inv_mul_cancel_right]⟩⟩
    have h3 : 3 ≤ Nat.card (X ⧸ M) := by
      have hodd := CFSG.Holt.odd_card hz2 hfix
      have h1 : Nat.card (X ⧸ M) ≠ 1 := fun h1 => hsub fun g =>
        (Finite.card_le_one_iff_subsingleton.mp h1.le).elim _ _
      obtain ⟨k, hk⟩ := hodd
      omega
    have hT : IsHoltTriple X (X ⧸ M) z ((1 : X) : X ⧸ M) := ⟨hpre, hz2, hfix', hS⟩
    obtain ⟨D⟩ := hH X (X ⧸ M) (IsHoltTriple.isStarGroup hT h3)
    exact false_of_holtData hcard hz2 hzM hfix' h3 D
  · have hMn : M.Normal := by
      have hle : M ≤ M.normalCore := fun x hx => by
        have : (⟨x, hx⟩ : M) ∈ M.normalCore.subgroupOf M := ht ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp this
      exact (le_antisymm M.normalCore_le hle) ▸ Subgroup.normalCore_normal M
    refine hsub fun g => ?_
    refine ((hfix' _).mp ?_)
    rw [MulAction.Quotient.smul_coe, QuotientGroup.eq]
    simpa [mul_assoc] using hMn.conj_mem _ (M.inv_mem hzM) g⁻¹


end CFSG.RankThree.PartTwo.Sec21.FF81
