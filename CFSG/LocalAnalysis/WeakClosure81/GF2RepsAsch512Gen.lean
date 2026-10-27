module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

theorem exists_mul_ne_of_isCalL1 {X : Type} [Group X] [Finite X] (h : IsCalL1 X) :
    ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨n, hn_odd, hn_gt1, hL2 | hSz | hL3⟩ := h
  ·
    have hm : StatedClassicalModel X .PSL 2 2 n := hL2.statedClassicalModel (by decide)
    obtain ⟨-, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hn2 : 2 ≤ n := by omega
    have hcard : 3 < Nat.card F := by
      rw [hF]
      calc 3 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    obtain ⟨x, y, hxy⟩ :=
      CFSG.ComponentClassification.CatalogueBSmallRee.projectiveSpecialLinear_two_nonabelian
        F (by omega) (by omega)
    let e' := eF.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
    exact ⟨e'.symm x, e'.symm y, fun hc => hxy (by simpa using congrArg e' hc)⟩
  ·
    exact CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 hSz
  ·
    have hm : StatedClassicalModel X .PSL 3 2 n := hL3.statedClassicalModel (by decide)
    haveI : IsSimpleGroup X := CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hm
    obtain ⟨⟨-, -, -⟩, F, _, _, hF, ⟨eF⟩⟩ := hm
    have hcard : Nat.card X = Nat.card (StatedProj (StatedSL 3 F)) := Nat.card_congr eF.toEquiv
    have hord :=
      CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := F)
    refine exists_noncomm_of_simple_of_pow_three_dvd (X := X)
      Nat.prime_two (g := Nat.gcd 3 (Nat.card F - 1))
      ((Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 _)) ?_
    rw [hcard, hord, hF]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right
      (pow_dvd_pow_of_dvd (dvd_pow_self 2 (by omega)) 3) _) _

private theorem isSimpleGroup_quotient_of_max' {X : Type} [Group X] {N : Subgroup X} [N.Normal]
    (hnt : N ≠ ⊤) (hmax : ∀ K : Subgroup X, K.Normal → N ≤ K → K = N ∨ K = ⊤) :
    IsSimpleGroup (X ⧸ N) :=
  { toNontrivial := QuotientGroup.nontrivial_iff.mpr hnt
    eq_bot_or_eq_top_of_normal := fun K hK' => by
      have hcomap : (K.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) = K :=
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K
      have hNK : N ≤ K.comap (QuotientGroup.mk' N) := by
        intro x hx
        rw [Subgroup.mem_comap,
          show QuotientGroup.mk' N x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
        exact K.one_mem
      rcases hmax (K.comap (QuotientGroup.mk' N)) (Subgroup.Normal.comap hK' _) hNK with h | h
      · left
        rw [← hcomap, h, QuotientGroup.map_mk'_self]
      · right
        rw [← hcomap, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] }

theorem isSolvable_of_forall_isCompositionFactor_comm (n : ℕ) :
    ∀ {X : Type} [Group X] [Finite X], Nat.card X ≤ n →
      (∀ (L : Type) [Group L], E1.IsCompositionFactor X L → ∀ a b : L, a * b = b * a) →
      Group.IsSolvable X := by
  induction n with
  | zero =>
    intro X _ _ h _
    have := Nat.card_pos (α := X)
    omega
  | succ n ih =>
    intro X _ _ hn hcf
    by_cases hX : Subsingleton X
    · exact Group.isSolvable_of_comm fun a b => Subsingleton.elim _ _
    · classical
      let S : Set (Subgroup X) := {K | K.Normal ∧ K ≠ ⊤}
      have hbot : (⊥ : Subgroup X) ∈ S := by
        refine ⟨inferInstance, fun h => hX ?_⟩
        refine ⟨fun a b => ?_⟩
        have ha : a ∈ (⊥ : Subgroup X) := by rw [h]; exact Subgroup.mem_top a
        have hb : b ∈ (⊥ : Subgroup X) := by rw [h]; exact Subgroup.mem_top b
        rw [Subgroup.mem_bot] at ha hb
        rw [ha, hb]
      obtain ⟨N, ⟨hNn, hNt⟩, hmax⟩ := Set.Finite.exists_maximalFor
        (fun K : Subgroup X => Nat.card K) S (Set.toFinite S) ⟨⊥, hbot⟩
      haveI := hNn
      have hmax' : ∀ K : Subgroup X, K.Normal → N ≤ K → K = N ∨ K = ⊤ := by
        intro K hK hNK
        by_cases hKt : K = ⊤
        · exact Or.inr hKt
        · left
          have hle : Nat.card K ≤ Nat.card N := hmax ⟨hK, hKt⟩ (Subgroup.card_le_of_le hNK)
          exact (Subgroup.eq_of_le_of_card_ge hNK hle).symm
      haveI hs : IsSimpleGroup (X ⧸ N) := isSimpleGroup_quotient_of_max' hNt hmax'
      have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp (⊤ : Subgroup X).subtype) := by
        intro y
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
        exact ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩
      have hcfq : E1.IsCompositionFactor X (X ⧸ N) :=
        CFSG.Quasithin.H13.L829N.isCompositionFactor_of_subnormal_surjection
          Subgroup.IsSubnormal.top hs _ hsurj
      haveI : Group.IsSolvable (X ⧸ N) := Group.isSolvable_of_comm (hcf _ hcfq)
      have hNlt : Nat.card N < Nat.card X := by
        have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNt)
        rwa [Subgroup.card_top] at this
      haveI : Group.IsSolvable N :=
        ih (by omega) fun L _ hL => hcf L (kbr_isCompositionFactor_of_normal_subgroup N hL)
      exact Group.isSolvable_of_subgroup_quotient N

variable {G : Type} [Group G] [Finite G]

theorem not_hasCompFactor_isCalL1_of_isSolvable {X : Subgroup G} [Group.IsSolvable ↥X] :
    ¬ HasCompFactor X IsCalL1 := by
  rintro ⟨L, hL, hcf, hP⟩
  letI := hL
  haveI : Finite L := isCompositionFactor_finite hcf
  obtain ⟨a, b, hab⟩ := exists_mul_ne_of_isCalL1 hP
  exact hab (uc22p20b_simpSec_comm (uc22p20b_simpSec_of_cf hcf) a b)

theorem lGen_le {P : ∀ (X : Type) [Group X], Prop} {H T : Subgroup G} : lGen P H T ≤ H :=
  iSup₂_le fun _ hX => hX.2.1.le

theorem calNIn_eq_lGen_of_forall {P : ∀ (X : Type) [Group X], Prop} {H T : Subgroup G}
    (hTH : T < H) (hne : H ≠ lGen P H T) (hall : ∀ M ∈ calNIn H T, ¬ HasCompFactor M P) :
    calNIn H T = {lGen P H T} := by
  have hlt : lGen P H T < H := lt_of_le_of_ne lGen_le (Ne.symm hne)
  have key : ∀ M ∈ calNIn H T, M = lGen P H T := by
    intro M hM
    have hMle : M ≤ lGen P H T := le_iSup₂_of_le M ⟨hM.1, hM.2.1, hall M hM⟩ le_rfl
    by_contra hneq
    exact hlt.ne (hM.2.2 _ (lt_of_le_of_ne hMle hneq) lGen_le)
  obtain ⟨X, hX, -⟩ := exists_mem_calNIn_of_lt le_rfl hTH
  ext M
  constructor
  · intro hM
    exact key M hM
  · intro hM
    rw [Set.mem_singleton_iff] at hM
    rw [hM, ← key X hX]
    exact hX

theorem calNIn_eq_lGen_of_isSolvable {H T : Subgroup G} (hTH : T < H) [Group.IsSolvable ↥H]
    (hne : H ≠ lGen IsCalL1 H T) : calNIn H T = {lGen IsCalL1 H T} := by
  refine calNIn_eq_lGen_of_forall hTH hne fun M hM => ?_
  haveI : Group.IsSolvable ↥M :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM.2.1.le)
  exact not_hasCompFactor_isCalL1_of_isSolvable

end CFSG.LocalAnalysis.WeakClosure81

end
