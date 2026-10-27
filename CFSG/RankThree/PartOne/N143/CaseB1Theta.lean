module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartOne.N143.JFacts

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open scoped commutatorElement

theorem isKGroup_subgroup {X : Type} [Group X] (hX : CFSG.IsKGroup X) (K : Subgroup X) :
    CFSG.IsKGroup K :=
  hX.subgroup K

theorem isPerfect_of_simple_of_not_prime {K : Type*} [Group K] [IsSimpleGroup K]
    (h : ¬ (Nat.card K).Prime) : Group.IsPerfect K := by
  have hnab : ∃ a b : K, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := hc }
    exact h (IsSimpleGroup.prime_card (α := K))
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ commutator K := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h1, Subgroup.mem_bot] at h2
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · exact h1

section Share

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}

theorem isPerfect_Kof (hKt1 : JLemmaKt1) {c : G} {J : Subgroup G} (h : JGood p A c J)
    {t : MulAut A} (ht : t ∈ reflectionSet p A) (htJ : t ∈ torusImage A J) {f : ℕ}
    (hf : p ∣ 2 ^ f - 1) (hm : StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 3 2 f) :
    Group.IsPerfect ↥(Kof A J t) ∧ Kof A J t ≠ ⊥ := by
  obtain ⟨hs, hc, -⟩ := hKt1 G p A c J h t ht htJ f hf hm
  have hf1 : f ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := ↥(Kof A J t))
    rw [hc] at this
    simp at this
  have hnp : ¬ (Nat.card (Kof A J t)).Prime := by
    rw [hc]
    refine Nat.not_prime_mul ?_ ?_
    · have : 2 ≤ 2 ^ f := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 hf1)
      omega
    · have : 4 ≤ 2 ^ (2 * f) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * f) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  refine ⟨isPerfect_of_simple_of_not_prime hnp, ?_⟩
  intro hbot
  have : Nontrivial ↥(Kof A J t) := hs.toNontrivial
  exact (Subgroup.nontrivial_iff_ne_bot _).1 this hbot

theorem normal_solvable_le_center {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) (hNs : Group.IsSolvable N) : N ≤ Subgroup.center Q := by
  classical
  let Z : Subgroup Q := Subgroup.center Q
  let π : Q →* Q ⧸ Z := QuotientGroup.mk' Z
  let Nbar : Subgroup (Q ⧸ Z) := N.map π
  have hNbar : Nbar.Normal := hN.map π (QuotientGroup.mk'_surjective Z)
  have hsimple : IsSimpleGroup (Q ⧸ Z) := hQ.2.1
  rcases (haveI := hNbar; hsimple.eq_bot_or_eq_top_of_normal Nbar) with hbot | htop
  · intro x hx
    have hxmap : π x ∈ Nbar := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hbot] at hxmap
    exact (QuotientGroup.eq_one_iff (N := Z) x).mp (Subgroup.mem_bot.mp hxmap)
  · exfalso
    have hcom : Z ⊔ N = ⊤ := by
      calc Z ⊔ N = Subgroup.comap π Nbar := (QuotientGroup.comap_map_mk' Z N).symm
        _ = ⊤ := by rw [htop]; simp
    have hNZ : N ⊔ Z = ⊤ := by simpa [sup_comm] using hcom
    have hle : _root_.commutator Q ≤ N :=
      hN.commutator_le_of_self_sup_commutative_eq_top hNZ (by infer_instance)
    have hNtop : N = ⊤ := by
      rw [hQ.1.commutator_eq_top] at hle
      exact eq_top_iff.mpr hle
    have hQs : Group.IsSolvable Q := by
      have h1 : Group.IsSolvable ↥(⊤ : Subgroup Q) := by
        rw [← hNtop]
        exact hNs
      exact Group.isSolvable_of_surjective
        (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).toMonoidHom)
        Subgroup.topEquiv.surjective
    have : Nontrivial (Q ⧸ Z) := hsimple.toNontrivial
    have : Nontrivial Q := (QuotientGroup.mk'_surjective Z).nontrivial
    have : Group.IsPerfect Q := hQ.1
    exact Group.IsPerfect.not_isSolvable Q hQs

omit [Finite G] in
theorem Kof_le_self (J : Subgroup G) (t : MulAut A) : Kof A J t ≤ J := by
  have hK : Kof A J t ≤ Nt A J t := by
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  exact hK.trans inf_le_left

end Share

section Restrict

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem restrict_thetaComponentsAt (hp : p.Prime) {M : Subgroup G} {c : G} (hcM : c ∈ M)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt p c) (hJM : J ≤ M) :
    J.subgroupOf M ∈ thetaComponentsAt p (⟨c, hcM⟩ : ↥M) := by
  classical
  set x : ↥M := ⟨c, hcM⟩ with hx
  set Cx := Subgroup.centralizer ({x} : Set ↥M) with hCx
  have hJC : J ≤ Subgroup.centralizer ({c} : Set G) := (mem_thetaComponentsAt_iff.1 hJ).1
  have hle : J.subgroupOf M ≤ Cx := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (hJC (Subgroup.mem_subgroupOf.1 hg))
  refine mem_thetaComponentsAt_iff.2 ⟨hle, ?_⟩
  have hJc := (mem_thetaComponentsAt_iff.1 hJ).2
  have hsn := hJc.2.1
  set Z : Subgroup ↥Cx := (J.subgroupOf M).subgroupOf Cx with hZ
  let e : ↥Z ≃* ↥J :=
    (Subgroup.subgroupOfEquivOfLe hle).trans (Subgroup.subgroupOfEquivOfLe hJM)
  refine ⟨?_, ?_, ?_⟩
  · have := isPerfect_of_mem_thetaComponentsAt hJ
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · let ι' : ↥Cx →* ↥(Subgroup.centralizer ({c} : Set G)) :=
      ((M.subtype).comp Cx.subtype).codRestrict (Subgroup.centralizer ({c} : Set G)) (by
        intro g
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp g.2)))
    have hZ' : Z = (J.subgroupOf (Subgroup.centralizer ({c} : Set G))).comap ι' :=
      Subgroup.ext fun g => Iff.rfl
    rw [hZ']
    exact hsn.comap ι'
  · have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hJ
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e.symm (aschbacherSolvableCore_map_mulEquiv hp e.symm)) hq

end Restrict

section SubgroupOf

variable {H : Type*} [Group H]

theorem normalizer_subgroupOf_of_le {K E S : Subgroup H}
    (hE : E ≤ Subgroup.normalizer (S : Set H)) :
    E.subgroupOf K ≤ Subgroup.normalizer ((S.subgroupOf K : Subgroup K) : Set K) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxE : (x : H) ∈ E := hx
  exact Subgroup.mem_normalizer_iff.1 (hE hxE) (y : H)

theorem isPGroup_subgroupOf {p : ℕ} {K S : Subgroup H} (hSK : S ≤ K) (hS : IsPGroup p S) :
    IsPGroup p (S.subgroupOf K) :=
  hS.of_surjective (Subgroup.subgroupOfEquivOfLe hSK).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSK).symm.surjective

theorem subgroupOf_ne_bot {K S : Subgroup H} (hSK : S ≤ K) (hS : S ≠ ⊥) : S.subgroupOf K ≠ ⊥ := by
  intro h
  apply hS
  rw [← Subgroup.map_subgroupOf_eq_of_le hSK, h, Subgroup.map_bot]

theorem isPerfect_subgroupOf {K S : Subgroup H} (hSK : S ≤ K) (h : Group.IsPerfect S) :
    Group.IsPerfect (S.subgroupOf K) := by
  have := h
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hSK).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hSK).symm.surjective

theorem commutator_subgroupOf {K S E : Subgroup H} (hS : S ≤ K) (hE : E ≤ K) :
    ⁅S.subgroupOf K, E.subgroupOf K⁆ = (⁅S, E⁆).subgroupOf K := by
  have hSE : ⁅S, E⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hS hg₁) (hE hg₂))
      (Subgroup.inv_mem _ (hS hg₁))) (Subgroup.inv_mem _ (hE hg₂))
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hS,
    Subgroup.map_subgroupOf_eq_of_le hE, Subgroup.map_subgroupOf_eq_of_le hSE]

end SubgroupOf

end CFSG.RankThree.PartOne.N143
