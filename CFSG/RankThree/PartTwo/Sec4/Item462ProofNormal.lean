module

public import CFSG.RankThree.PartTwo.Sec4.Item462ProofCent
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_list
    (hS4 : SectionFourHyp G) {A U L : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27) {a : G} (haA : a ∈ A) (haZ : a ∈ Subgroup.center G) (ha1 : a ≠ 1)
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUL : U ≤ L)
    (hU2 : IsPGroup 2 U) (hAU : A ≤ Subgroup.normalizer (U : Set G))
    (hUθ : ¬ U ≤ aschbacherSolvableCore 3 G)
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hlist : (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
          CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3)))
    (g : G) : g ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have ha3 : orderOf a = 3 := orderOf_eq_prime (hAe.2 a haA) ha1
  by_contra hg
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  obtain ⟨-, hK, ⟨η, -⟩, -, -, -, -, -, -, -, hAiff⟩ :=
    theta_component_quotient_structure Nat.prime_three hL
  have hZL : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
    rcases hlist with (he | he) | he
    · obtain ⟨e⟩ := he
      exact center_eq_bot_of_j2 e
    · obtain ⟨e⟩ := he
      exact (not_inducesOuterTheta_of_m12 (G := G) e).1
    · obtain ⟨e⟩ := he
      exact (center_eq_bot_and_isCyclic_of_l27 e).1
  have hZK : Subgroup.center (L.map ρ) = ⊥ := by
    have h := Subgroup.map_center_eq η
    rw [hZL, Subgroup.map_bot] at h
    exact h.symm
  set σ := MulAut.conj (ρ g) with hσ
  set K' := (L.map ρ).map σ.toMonoidHom with hK'
  have hK'c : IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv σ hK
  have hKK' : L.map ρ ≠ K' := by
    intro h
    apply hg
    rw [mem_normalizer_iff_mk_mem_normalizer Nat.prime_three hL,
      Subgroup.mem_normalizer_iff_map_conj_eq]
    exact h.symm
  have hcomm : ⁅L.map ρ, K'⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hK hK'c with h | h
    · exact absurd h hKK'
    · exact h
  have hK'C : K' ≤ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hKK'c : ∀ x ∈ L.map ρ, ∀ y ∈ K', x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hK'C hy) x hx)
  have hZK' : ∀ x ∈ L.map ρ, x ∈ K' → x = 1 := by
    intro x hxK hxK'
    have hmem : (⟨x, hxK⟩ : L.map ρ) ∈ Subgroup.center (L.map ρ) :=
      Subgroup.mem_center_iff.mpr fun k => Subtype.ext (hKK'c k k.2 x hxK')
    rw [hZK, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hU1 : U.map ρ ≠ ⊥ := by
    intro h
    apply hUθ
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  have hU2' : IsPGroup 2 (U.map ρ) := hU2.map ρ
  have hUK : U.map ρ ≤ L.map ρ := Subgroup.map_mono hUL
  have hK'N : K' ≤ Subgroup.normalizer ((U.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    hK'C.trans ((Subgroup.centralizer_le hUK).trans (Subgroup.centralizer_le_normalizer _))
  have hAUN : A.map ρ ≤ Subgroup.normalizer ((U.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    (Subgroup.map_mono hAU).trans (Subgroup.le_normalizer_map ρ)
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hAp
  have haZX : ρ a ∈ Subgroup.center (G ⧸ N) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N) (Subgroup.mem_map_of_mem ρ haZ)
  have hρa1 : ρ a ≠ 1 := fun h => ha1 (hinj haA A.one_mem (by rw [h, map_one]))
  have hρa3 : ρ a ^ 3 = 1 := by rw [← map_pow, hAe.2 a haA, map_one]
  have ha3X : orderOf (ρ a) = 3 := orderOf_eq_prime hρa3 hρa1
  have hZe : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers (ρ a)) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp y.2
      change (x : G ⧸ N) * y = y * x
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self (ρ a) i j).eq
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρa3, one_zpow]
  have hZN : Subgroup.zpowers (ρ a) ≤
      Subgroup.normalizer ((U.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    (Subgroup.zpowers_le.mpr haZX).trans
      ((Subgroup.center_le_centralizer _).trans (Subgroup.centralizer_le_normalizer _))
  rcases hlist with he | he
  ·
    have hinner : ∀ x ∈ A, ¬ InducesOuterTheta x L := by
      intro x hx
      rcases he with he | he
      · obtain ⟨e⟩ := he
        exact not_inducesOuterTheta_of_j2 e (hAe.2 x hx)
      · obtain ⟨e⟩ := he
        exact (not_inducesOuterTheta_of_m12 (G := G) e).2 x (hAe.2 x hx)
    have hZn : (Subgroup.zpowers a).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
    have hALa : A ≤ L ⊔ Subgroup.zpowers a := fun x hx =>
      mem_sup_zpowers_of_not_inducesOuterTheta hmax hL hAL hCA hZL hx (hinner x hx)
    set E := L.map ρ ⊓ A.map ρ with hE
    have hZnX : (Subgroup.zpowers (ρ a)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZX)
    have hAeX : CFSG.Assembly.IsElemAbelian 3 (A.map ρ) := isElemAbelian_map' ρ hAe
    have hEe : CFSG.Assembly.IsElemAbelian 3 E :=
      ⟨⟨⟨fun x y => Subtype.ext (show (x : G ⧸ N) * y = y * x from
        congrArg (Subtype.val : A.map ρ → G ⧸ N)
          (hAeX.1.1.comm (⟨x, x.2.2⟩ : A.map ρ) ⟨y, y.2.2⟩))⟩⟩, fun x hx => hAeX.2 x hx.2⟩
    have haE : ρ a ∉ E := fun h => hρa1 (by
      have hmem : (⟨ρ a, h.1⟩ : L.map ρ) ∈ Subgroup.center (L.map ρ) :=
        Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp haZX k)
      rw [hZK, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem)
    have hAEZ : A.map ρ = E ⊔ Subgroup.zpowers (ρ a) := by
      refine le_antisymm ?_ (sup_le inf_le_right
        (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem ρ haA)))
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨l, hl, z, hz, hlz⟩ := Subgroup.mem_sup_of_normal_right.mp (hALa hx)
      have hzA : z ∈ A := (Subgroup.zpowers_le.mpr haA) hz
      have hlA : l ∈ A := by
        have := A.mul_mem hx (A.inv_mem hzA)
        rwa [← hlz, mul_inv_cancel_right] at this
      rw [← hlz, map_mul]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨Subgroup.mem_map_of_mem ρ hl,
        Subgroup.mem_map_of_mem ρ hlA⟩) (Subgroup.mem_sup_right (by
          rw [← MonoidHom.map_zpowers]
          exact Subgroup.mem_map_of_mem ρ hz))
    have hAc : Nat.card (A.map ρ) = 27 := by
      rw [← h27]
      exact (Nat.card_congr (Equiv.ofBijective (ρ.subgroupMap A)
        ⟨fun x y h => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h)),
          ρ.subgroupMap_surjective A⟩)).symm
    have hEc : Nat.card E = 9 := by
      have h := card_sup_zpowers_of_not_mem haZX ha3X haE
      rw [← hAEZ, hAc] at h
      omega
    set E' := E.map σ.toMonoidHom with hE'
    have hE'e : CFSG.Assembly.IsElemAbelian 3 E' := isElemAbelian_map' _ hEe
    have hE'c : Nat.card E' = 9 := by
      rw [hE', Subgroup.card_map_of_injective σ.injective, hEc]
    have hEK : E ≤ L.map ρ := inf_le_left
    have hE'K' : E' ≤ K' := Subgroup.map_mono hEK
    have hEE' : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x := fun x hx y hy =>
      hKK'c x (hEK hx) y (hE'K' hy)
    have hFe := isElemAbelian_sup_of_commute hEe hE'e hEE'
    have hE'N : E' ≤ Subgroup.normalizer (E : Set (G ⧸ N)) := fun y hy =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        hEE' x hx y hy)
    have hdisj : Disjoint E E' := by
      rw [Subgroup.disjoint_def]
      intro x hx hx'
      exact hZK' x (hEK hx) (hE'K' hx')
    have hFc : Nat.card (E ⊔ E' : Subgroup (G ⧸ N)) = 3 ^ 4 := by
      rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E E' hE'N hdisj, hEc,
        hE'c]
      norm_num
    exact false_of_isElemAbelian_le_normalizer hS4 hU1 hU2' hFe hFc
      (sup_le (inf_le_right.trans hAUN) (hE'K'.trans hK'N))
  ·
    obtain ⟨e⟩ := he
    obtain ⟨E₀, hE₀, hE₀c⟩ := exists_isElemAbelian_card_of_l27 (η.symm.trans e)
    set E' := (E₀.map (L.map ρ).subtype).map σ.toMonoidHom with hE'
    have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
      isElemAbelian_map' _ (isElemAbelian_map' _ hE₀)
    have hE'c : Nat.card E' = 27 := by
      rw [hE', Subgroup.card_map_of_injective σ.injective,
        Subgroup.card_map_of_injective (L.map ρ).subtype_injective, hE₀c]
    have hE'K' : E' ≤ K' := Subgroup.map_mono (Subgroup.map_subtype_le _)
    have haE' : ρ a ∉ E' := by
      intro h
      have h1 : σ.symm (ρ a) = ρ a := by
        rw [hσ, MulAut.conj_symm_apply, (Subgroup.mem_center_iff.mp haZX (ρ g)⁻¹),
          inv_mul_cancel_right]
      have h2 : ρ a ∈ L.map ρ := by
        obtain ⟨y, hy, hya⟩ := hE'K' h
        have : y = ρ a := by
          rw [← h1, ← hya]
          exact (σ.symm_apply_apply y).symm
        exact this ▸ hy
      apply hρa1
      have hmem : (⟨ρ a, h2⟩ : L.map ρ) ∈ Subgroup.center (L.map ρ) :=
        Subgroup.mem_center_iff.mpr fun k => Subtype.ext (Subgroup.mem_center_iff.mp haZX k)
      rw [hZK, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
    have hFe := isElemAbelian_sup_of_commute hE'e hZe fun x _ y hy =>
      (Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZX) hy) x)
    have hFc : Nat.card (E' ⊔ Subgroup.zpowers (ρ a) : Subgroup (G ⧸ N)) = 3 ^ 4 := by
      rw [card_sup_zpowers_of_not_mem haZX ha3X haE', hE'c]
      norm_num
    exact false_of_isElemAbelian_le_normalizer hS4 hU1 hU2' hFe hFc
      (sup_le (hE'K'.trans hK'N) hZN)

end CFSG.RankThree.PartTwo.Sec4.Item462Proof
