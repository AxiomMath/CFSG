module

public import CFSG.Quasithin.Vol2.Ch4Sec4L443E7Le
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E2Comp
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E3Conj
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E4Inner
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E5Normal

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem not_isSolvable_of_isQuasisimple {K : Subgroup H} (hK : CFSG.IsQuasisimple ↥K) :
    ¬ Group.IsSolvable ↥K := by
  intro hs
  obtain ⟨hperf, -, a, b, hab⟩ := hK
  have htop : ∀ n : ℕ, derivedSeries ↥K n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf.commutator_eq_top]
  obtain ⟨n, hn⟩ := hs.solvable
  have h1 : ∀ x : ↥K, x = 1 := fun x => by
    have : x ∈ derivedSeries ↥K n := (htop n) ▸ Subgroup.mem_top x
    rw [hn] at this
    exact this
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [h1 a, h1 b]

omit [Finite H] in
theorem le_of_perfect_of_solvable {K L : Subgroup H} [hKn : K.Normal] (hL : ⁅L, L⁆ = L)
    (hLY : L ≤ K ⊔ Subgroup.centralizer (K : Set H))
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (K : Set H))) : L ≤ K :=
  (le_perfectCore_of_perfect hLY hL).trans
    (perfectCore_le_of_sup_solvable le_sup_left inferInstance rfl hC)

theorem centralizer_eq_oddCore {V L S M : Subgroup H} (hc : LocConf H V L S M) {K : Subgroup H}
    (hK : CFSG.IsComponent K) [hKn : K.Normal] (hKM : ¬ K ≤ M) (hVK : V ≤ K) :
    Subgroup.centralizer (K : Set H) = CFSG.oddCore H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (K : Set H) with hC
  have hKN : ∀ x : H, x ∈ Subgroup.normalizer (K : Set H) := fun x => by
    rw [Subgroup.normalizer_eq_top_iff.mpr hKn]
    trivial
  have hCN : ∀ x : H, x ∈ Subgroup.normalizer (C : Set H) := fun x =>
    CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer K (hKN x)
  have hCn : C.Normal := Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun x _ => hCN x)
  have hCM : C ≤ M := (Subgroup.centralizer_le hVK).trans hc.cent
  obtain ⟨S₀, hSS₀, hS₀⟩ := exists_isSylowTwoOf_of_le hc.s_le hc.s_two
  have hPsyl : IsSylowTwoOf (S₀ ⊓ C) C := A4.isSylowTwoOf_inf_normal hS₀ hCM fun x _ => hCN x
  set D := C ⊓ L with hD
  have hDL : L ≤ Subgroup.normalizer (D : Set H) := fun l hl =>
    (mem_normalizer_inf_sup (hCN l) (Subgroup.le_normalizer hl)).1
  have h1 := hc.cent_mod D inf_le_right hDL (inf_le_left.trans (Subgroup.centralizer_le hVK))
  have hO2C : pCoreOf 2 C = ⊥ := by
    refine le_bot_iff.mp ((LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top ?_
      (pCoreOf_isPGroup 2 C)).trans hc.o2.le)
    exact fun x _ => normalizer_le_normalizer_pCoreOf 2 C (hCN x)
  have h2 : D ⊓ pCoreOf 2 L ≤ pCoreOf 2 C := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans inf_le_left)
      (fun x hx => ?_) ((pCoreOf_isPGroup 2 L).to_le inf_le_right)
    have hxL : x ∈ Subgroup.normalizer (L : Set H) := hc.l_normal (hCM hx)
    exact (mem_normalizer_inf_sup (mem_normalizer_inf_sup (hCN x) hxL).1
      (normalizer_le_normalizer_pCoreOf 2 L hxL)).1
  have hDL1 : ⁅D, L⁆ = ⊥ := by
    rw [hO2C] at h2
    exact le_bot_iff.mp ((le_inf (commutator_le_left_of_le_normalizer hDL) h1).trans h2)
  have hPL : ⁅S₀ ⊓ C, L⁆ ≤ D := le_inf
    ((Subgroup.commutator_mono inf_le_right le_rfl).trans
      (commutator_le_left_of_le_normalizer fun l _ => hCN l))
    (commutator_le_right_of_le_normalizer (inf_le_left.trans (hS₀.1.trans hc.l_normal)))
  have h4 : ⁅⁅S₀ ⊓ C, L⁆, L⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hPL le_rfl).trans hDL1.le)
  have h5 : ⁅⁅L, L⁆, S₀ ⊓ C⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ h4
    rw [Subgroup.commutator_comm L]
    exact h4
  rw [hc.l_perfect] at h5
  have hPN : L ⊔ S ≤ Subgroup.normalizer ((S₀ ⊓ C : Subgroup H) : Set H) := by
    refine sup_le ?_ fun x hx => (mem_normalizer_inf_sup
      (Subgroup.le_normalizer (hSS₀ hx)) (hCN x)).1
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h5
    exact h5.trans (Subgroup.centralizer_le_normalizer _)
  have hP1 : S₀ ⊓ C = ⊥ := by
    by_contra hP
    have h6 := hc.uniq _ hP (hPsyl.2.1) hPN
    apply hKM
    have hKP : K ≤ Subgroup.centralizer ((S₀ ⊓ C : Subgroup H) : Set H) :=
      Subgroup.le_centralizer_iff.mp inf_le_right
    exact hKP.trans ((Subgroup.centralizer_le_normalizer _).trans h6)
  have hodd : Odd (Nat.card C) := by
    have h7 := hPsyl.2.2
    rw [hP1, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h7
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h7)
  refine le_antisymm (le_sSup ⟨hCn, hodd⟩) ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK (CFSG.oddCore_normal (G := H)) with h | h
  · exfalso
    have hKodd : Odd (Nat.card K) :=
      Odd.of_dvd_nat (CFSG.ABGLocalTools.odd_card_oddCore (H := H)) (Subgroup.card_dvd_of_le h)
    exact not_isSolvable_of_isQuasisimple hK.1 (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hKodd)
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact Subgroup.le_centralizer_iff.mp h

theorem exists_normal_component (hF : A38Facts) (hS : Vol2Native.SchreierFactCat)
    (h4411 : Fact4411) {V L S M : Subgroup H} (hc : LocConf H V L S M) :
    ∃ K : Subgroup H, CFSG.IsComponent K ∧ K.Normal ∧ ¬ K ≤ M ∧ V ≤ K ∧ L ≤ K ∧
      Subgroup.centralizer (K : Set H) = CFSG.oddCore H := by
  obtain ⟨K, hK, hKV⟩ := exists_isComponent_commutator_ne_bot hc.v_two hc.v_ne hc.o2 hc.v_odd
  have hO2K := pCore_eq_bot_of_isComponent hc.o2 hK
  have h2 : (conjSubgroups K).ncard ≤ 2 := by
    by_cases hn : K.Normal
    · exact ncard_conjSubgroups_of_normal hn
    · exact (A38.a38_part12 hF H hc.qt hc.kgroup K hK hO2K hn).1.1.le
  have hLN := le_normalizer_of_perfect h2 hc.l_perfect
  have hVN := le_normalizer_of_commutator_eq h2 hc.v_eq
  have hOut := hS ↥K hK.1 (hc.kgroup.subgroup K)
  have hLY := le_sup_centralizer_of_outSolvable hOut hLN hc.l_perfect
  have hVY := le_sup_centralizer_of_commutator_eq hLY hVN hc.v_eq
  have hKn := normal_of_fact4411 hF h4411 hc.qt hc.kgroup hK hO2K hLY hVY hc.l_perfect hc.v_two
    hc.v_eq hKV
  have hKM := not_le_of_commutator_ne_bot hc (pCoreOf_eq_bot_of_pCore hO2K) hVN hKV
  have hVK := le_of_normal hc hKM hVY
  have hC := centralizer_eq_oddCore hc hK hKM hVK
  have hCs : Group.IsSolvable ↥(Subgroup.centralizer (K : Set H)) := by
    rw [hC]
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ABGLocalTools.odd_card_oddCore (H := H))
  exact ⟨K, hK, hKn, hKM, hVK, le_of_perfect_of_solvable hc.l_perfect hLY hCs, hC⟩

end CFSG.Quasithin.H13.Ch4.E443
