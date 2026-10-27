module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofA6A6Cent
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.GroupTheory.SubnormalJoin

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Item148PtRes

variable {G : Type} [Group G] [Finite G]

theorem theta_le_pPrimeCoreOf_of_eq_sSup {b : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 b) {X : Subgroup G} (hX : X = sSup 𝒳) :
    inSubgroup (aschbacherSolvableCore 3) X ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  have hXCb : X ≤ Cb :=
    hX ▸ sSup_le fun L hL => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hL)
  set 𝒮 : Set (Subgroup ↥Cb) := {L' | L'.map Cb.subtype ∈ 𝒳} with h𝒮
  have h𝒮sn : ∀ L' ∈ 𝒮, L'.IsSubnormal := by
    intro L' hL'
    obtain ⟨L'', hL'', heq⟩ := h𝒳 hL'
    have : L'' = L' := Subgroup.map_injective Cb.subtype_injective heq
    exact this ▸ hL''.2.1
  have hcl : Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥Cb)) = X.subgroupOf Cb := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨A, hA, hxA⟩ := hx
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact (hX ▸ le_sSup hA : A.map Cb.subtype ≤ X) ⟨x, hxA, rfl⟩
    · intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hle : X ≤ (Subgroup.closure (⋃ A ∈ 𝒮, (A : Set ↥Cb))).map Cb.subtype := by
        rw [hX]
        refine sSup_le fun L hL => ?_
        have hLCb : L ≤ Cb := le_centralizer_of_mem_thetaComponentsAt (h𝒳 hL)
        have hL' : L.subgroupOf Cb ∈ 𝒮 := by
          show (L.subgroupOf Cb).map Cb.subtype ∈ 𝒳
          rw [Subgroup.map_subgroupOf_eq_of_le hLCb]
          exact hL
        rw [← Subgroup.map_subgroupOf_eq_of_le hLCb]
        exact Subgroup.map_mono fun y hy =>
          Subgroup.subset_closure (Set.mem_biUnion hL' hy)
      obtain ⟨y, hy, hyx⟩ := hle hx
      have : y = x := Subtype.ext hyx
      rwa [← this]
  have hsn : (X.subgroupOf Cb).IsSubnormal := by
    rw [← hcl]
    exact (CFSG.GroupTheory.subnormal_subgroups_generated_join 𝒮 h𝒮sn).1
  have h1 := CFSG.RankThree.solvable_prime_complement_core_subnormal_intersection
    Nat.prime_three hsn
  have h2 := congrArg (Subgroup.map Cb.subtype) h1
  have e1 := Sec6.map_inSubgroup_theta_of_injective Cb.subtype Cb.subtype_injective
    (X.subgroupOf Cb)
  rw [Subgroup.map_subgroupOf_eq_of_le hXCb] at e1
  rw [e1, Subgroup.map_inf_eq _ _ Cb.subtype Cb.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hXCb] at h2
  rw [h2]
  exact inf_le_right.trans (inSubgroup_theta_le_pPrimeCoreOf Cb)

omit [Finite G] in
theorem inf_le_theta_of_forall_normal {N X : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN3 : Nat.Coprime 3 (Nat.card N))
    (hP0 : ∀ P : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X), P.Normal →
      ¬ 3 ∣ Nat.card P → P = ⊥) :
    N ⊓ X ≤ inSubgroup (aschbacherSolvableCore 3) X := by
  set M : Subgroup ↥X := N.subgroupOf X with hMdef
  have hMn : M.Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [hMdef, Subgroup.mem_subgroupOf] at ha ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hXN g.2) a).mp ha
  set P := M.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) with hP
  have hPn : P.Normal := hMn.map _ (QuotientGroup.mk'_surjective _)
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3
    have h1 := h3.trans (Subgroup.card_map_dvd M _)
    have h2 : Nat.card M ∣ Nat.card N := by
      rw [hMdef, ← Subgroup.card_map_of_injective X.subtype_injective,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN3 (h1.trans h2)
  have hPb : P = ⊥ := hP0 P hPn hP3
  intro y hy
  obtain ⟨hyN, hyX⟩ := Subgroup.mem_inf.mp hy
  have hmem : (⟨y, hyX⟩ : ↥X) ∈ aschbacherSolvableCore 3 ↥X := by
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (⟨y, hyX⟩ : ↥X) ∈ P :=
      ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hyN, rfl⟩
    rw [hPb, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨⟨y, hyX⟩, hmem, rfl⟩

theorem mem_normalizer_of_eq_sSup {b g : G} {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 b) {X : Subgroup G} (hX : X = sSup 𝒳)
    (hNX : pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊓ X ≤
      inSubgroup (aschbacherSolvableCore 3) X)
    (hg : g ∈ Subgroup.centralizer ({b} : Set G))
    (hgN : g ∈ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer (X : Set G) := by
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hXCb : X ≤ Cb :=
    hX ▸ sSup_le fun L hL => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hL)
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := hXCb.trans hCbN
  have hθs : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) X) := by
    have h1 := (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).1
    exact Group.isSolvable_of_surjective (f := ((aschbacherSolvableCore 3 ↥X).equivMapOfInjective
      X.subtype X.subtype_injective).toMonoidHom) (MulEquiv.surjective _)
  have hLg : ∀ L ∈ 𝒳, L.map (MulAut.conj g).toMonoidHom ≤ X := by
    intro L hL
    set P := L.map (MulAut.conj g).toMonoidHom with hP
    by_cases hP𝒳 : P ∈ 𝒳
    · exact hX ▸ le_sSup hP𝒳
    exfalso
    have hPm : P ∈ thetaComponentsAt 3 b := Sec6.map_conj_mem_thetaComponentsAt hg (h𝒳 hL)
    have hPCb : P ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hPm
    have hXcomm : X ≤ commutatorInSubgroup P N := by
      rw [hX]
      refine sSup_le fun L' hL' => ?_
      intro x hx
      refine ⟨hCbN (hXCb (hX ▸ le_sSup hL' hx)), fun p hp => ?_⟩
      have hne : P ≠ L' := fun he => hP𝒳 (he ▸ hL')
      have h1 : ⁅p, x⁆ ∈ ⁅P, L'⁆ := Subgroup.commutator_mem_commutator hp hx
      exact (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hPm (h𝒳 hL') hne).trans
        (inSubgroup_theta_le_pPrimeCoreOf Cb) h1
    have hPle : P ≤ N ⊔ X := by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN x).mp
        (Subgroup.mem_sup_right (hX ▸ le_sSup hL hx))
    have hPN : P ≤ N := by
      have hPp : Group.IsPerfect ↥P := Sec6.isPerfect_of_mem_thetaComponentsAt hPm
      rw [← (Subgroup.isPerfect_iff).mp hPp, Subgroup.commutator_le]
      intro p₁ hp₁ p₂ hp₂
      obtain ⟨n, hn, x, hx, rfl⟩ := exists_mul_of_mem_sup hXN (hPle hp₂)
      have h1 : ⁅p₁, n * x⁆ = ⁅p₁, n⁆ * (n * ⁅p₁, x⁆ * n⁻¹) := by
        simp only [commutatorElement_def]
        group
      have h2 : ⁅p₁, n⁆ ∈ N := by
        rw [commutatorElement_def]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hCbN (hPCb hp₁)) n).mp hn) (inv_mem hn)
      rw [h1]
      exact mul_mem h2 (mul_mem (mul_mem hn ((hXcomm hx).2 p₁ hp₁)) (inv_mem hn))
    have hLN : L ≤ N := by
      intro l hl
      have h1 : g * l * g⁻¹ ∈ N := hPN ⟨l, hl, rfl⟩
      have h2 : l = g⁻¹ * (g * l * g⁻¹) * g := by group
      rw [h2]
      have := (Subgroup.mem_normalizer_iff.mp (hCbN (inv_mem hg)) _).mp h1
      simpa [mul_assoc] using this
    have hLθ : L ≤ inSubgroup (aschbacherSolvableCore 3) X :=
      hNX.trans' (le_inf hLN (hX ▸ le_sSup hL))
    have hLs : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLθ)
        (Subgroup.inclusion_injective hLθ)
    have hLp : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hL)
    have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt (h𝒳 hL)
    have hnt : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hLq
    have hLnt : Nontrivial ↥L := by
      rw [← not_subsingleton_iff_nontrivial] at hnt ⊢
      intro hsub
      exact hnt inferInstance
    exact Group.IsPerfect.not_isSolvable ↥L hLs
  have hle : X.map (MulAut.conj g).toMonoidHom ≤ X := by
    rw [Subgroup.map_le_iff_le_comap, hX]
    refine sSup_le fun L hL x hx => ?_
    rw [← hX]
    exact hLg L hL ⟨x, hx, rfl⟩
  have heq : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

omit [Finite G] in
theorem le_normalizer_sup_left {N X' : Subgroup G}
    (hX'N : X' ≤ Subgroup.normalizer (N : Set G)) :
    N ≤ Subgroup.normalizer ((N ⊔ X' : Subgroup G) : Set G) := by
  have key : ∀ m ∈ N, ∀ g ∈ N ⊔ X', m * g * m⁻¹ ∈ N ⊔ X' := by
    intro m hm g hg
    obtain ⟨n', hn', x, hx, rfl⟩ := exists_mul_of_mem_sup hX'N hg
    have h1 : m * (n' * x) * m⁻¹ = (m * n' * (x * m⁻¹ * x⁻¹)) * x := by group
    rw [h1]
    exact mul_mem (Subgroup.mem_sup_left (mul_mem (mul_mem hm hn')
      ((Subgroup.mem_normalizer_iff.mp (hX'N hx) _).mp (inv_mem hm)))) (Subgroup.mem_sup_right hx)
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key n hn g, fun h => ?_⟩
  have h1 := key n⁻¹ (inv_mem hn) _ h
  simpa [mul_assoc] using h1

theorem false_of_centralProduct_A6 {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B : Subgroup G} (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {X : Subgroup G}
    (hCX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    {𝒳 : Set (Subgroup G)} (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 b) (hX : X = sSup 𝒳)
    (hT : IsCentralProductA6Covers (↥X ⧸ aschbacherSolvableCore 3 ↥X))
    (hQX : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X) : False := by
  have hD := h.toSec13Data
  have hbA : b ∈ A := hB.1 hb
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  set θX := inSubgroup (aschbacherSolvableCore 3) X with hθX
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ Cb := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx b hbA)
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hXCb : X ≤ Cb :=
    hX ▸ sSup_le fun L hL => le_centralizer_of_mem_thetaComponentsAt (h𝒳 hL)
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := hXCb.trans hCbN
  have hθXN : θX ≤ N := theta_le_pPrimeCoreOf_of_eq_sSup h𝒳 hX
  have hXp : Group.IsPerfect ↥X := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le_self X) ?_
    rw [hX]
    refine sSup_le fun L hL => ?_
    have hLp : Group.IsPerfect ↥L := Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hL)
    rw [← (Subgroup.isPerfect_iff).mp hLp]
    exact Subgroup.commutator_mono (le_sSup hL) (le_sSup hL)
  obtain ⟨U, V, hUn, hVn, hUV', hUV, h3, hTU, hTV⟩ := hT
  have hXbp : Group.IsPerfect (↥X ⧸ aschbacherSolvableCore 3 ↥X) := inferInstance
  have hNX : N ⊓ X ≤ θX := inf_le_theta_of_forall_normal hXN hN3 fun P hP hP3 =>
    eq_bot_of_normal_of_coprime hUV' hUV h3 hTU hTV hP hP3
  have hTU' := hTU
  have hTV' := hTV
  obtain ⟨hZU, ⟨eU⟩⟩ := hTU'
  obtain ⟨hZV, ⟨eV⟩⟩ := hTV'
  have hUZ := inf_eq_centerIn_left hUV h3 hZU
  have hVZ := inf_eq_centerIn_right hUV h3 hZV
  obtain ⟨u, huB, hub⟩ := exists_mem_not_mem_zpowers hD.card_eq hD.isElemAbelian.2 hB hbA
  have huA : u ∈ A := hB.1 huB
  have hu3 : u ^ 3 = 1 := hD.isElemAbelian.2 u huA
  have hu1 : u ≠ 1 := fun h1 => hub (h1 ▸ one_mem _)
  have hne : Subgroup.zpowers b ≠ Subgroup.zpowers u := fun he =>
    hub (he ▸ Subgroup.mem_zpowers u)
  have huCb : u ∈ Cb := hAC huA
  have hCB : Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (B : Set G) :=
    Item148HJ.centralizer_inf_le_of_mem_hyperplane hD.isElemAbelian hD.card_eq hB hb huB hb1 hu1
      hne
  have hQYC : Q ≤ Y ⊓ Cb := le_inf (hQY.trans inf_le_left)
    (hQY.trans (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))))
  have hcontra : Q ≤ N → False := fun hQN =>
    hQb ((le_inf hQN hQYC).trans (inf_le_pPrimeCoreOf148 (inf_le_right.trans hCbN) hN3))
  have hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
    intro g hg
    obtain ⟨hgYC, hgu⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨hgY, hgb⟩ := Subgroup.mem_inf.mp hgYC
    exact le_normalizer_pPrimeCoreOf 3 _
      (Subgroup.mem_inf.mpr ⟨hgY, hCB (Subgroup.mem_inf.mpr ⟨hgb, hgu⟩)⟩)
  have hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) :=
    (le_sSup ⟨hQ, hQY⟩ : Q ≤ deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G))).trans
      (hYB B hB)
  have huX : u ∈ Subgroup.normalizer (X : Set G) :=
    mem_normalizer_of_eq_sSup h𝒳 hX hNX huCb (hCX huCb)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) with hπ
  set σ : MulAut (↥X ⧸ aschbacherSolvableCore 3 ↥X) :=
    Sec4.thetaQuotMulAut ↥X (X.normalizerMonoidHom ⟨u, huX⟩) with hσ
  have hσmk : ∀ (x : G) (hx : x ∈ X), σ (π ⟨x, hx⟩) =
      π ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huX x).mp hx⟩ := fun x hx => by
    rw [hσ, hπ, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    rfl
  have hmk : ∀ (x y : G) (hx : x ∈ X) (hy : y ∈ X),
      π (⟨x, hx⟩ : ↥X) = π ⟨y, hy⟩ ↔ x * y⁻¹ ∈ θX := by
    intro x y hx hy
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    constructor
    · intro h1
      exact ⟨_, h1, by simp [div_eq_mul_inv]⟩
    · rintro ⟨z, hz, hzeq⟩
      have : z = (⟨x, hx⟩ : ↥X) / ⟨y, hy⟩ := Subtype.ext (by
        simp only [Subgroup.coe_subtype] at hzeq
        rw [hzeq, Subgroup.coe_div, div_eq_mul_inv])
      rwa [← this]
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨u, huX⟩ : Subgroup.normalizer (X : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hu3)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨hσU, hσV⟩ := map_eq_of_pow_three hUV' hUV h3 hTU hTV hσ3
  have hQ3 : ¬ 3 ∣ Nat.card Q := (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQ.1.1.2.1
  have himg : ∀ q ∈ Q, ∃ n ∈ N, ∃ (y : G) (hy : y ∈ X), q = n * y ∧
      σ (π ⟨y, hy⟩) = π ⟨y, hy⟩ ∧ ∃ k : ℕ, Nat.Coprime k 3 ∧ π ⟨y, hy⟩ ^ k = 1 := by
    intro q hq
    obtain ⟨n, hn, y, hy, rfl⟩ := exists_mul_of_mem_sup hXN (hQX hq)
    refine ⟨n, hn, y, hy, rfl, ?_, ?_⟩
    · have hqu : u * (n * y) * u⁻¹ = n * y := by
        have h1 := Subgroup.mem_centralizer_iff.mp ((hQY hq).2) u huB
        calc u * (n * y) * u⁻¹ = n * y * u * u⁻¹ := by rw [h1]
          _ = n * y := by group
      have hyN : u * y * u⁻¹ * y⁻¹ ∈ N := by
        have h1 : u * y * u⁻¹ * y⁻¹ = (u * n * u⁻¹)⁻¹ * n := by
          have h2 : u * y * u⁻¹ = (u * n * u⁻¹)⁻¹ * (n * y) := by
            rw [← hqu]
            group
          rw [h2]
          group
        rw [h1]
        exact mul_mem (inv_mem ((Subgroup.mem_normalizer_iff.mp (hCbN huCb) n).mp hn)) hn
      have hyX : u * y * u⁻¹ * y⁻¹ ∈ X :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp huX y).mp hy) (inv_mem hy)
      rw [hσmk y hy]
      exact (hmk _ _ _ hy).mpr (hNX (Subgroup.mem_inf.mpr ⟨hyN, hyX⟩))
    · refine ⟨orderOf (n * y), ?_, ?_⟩
      · have h1 : orderOf (n * y) ∣ Nat.card Q := by
          rw [← Subgroup.orderOf_mk (n * y) hq]
          exact orderOf_dvd_natCard _
        exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
          fun h3' => hQ3 (h3'.trans h1))
      · obtain ⟨n', hn', hpow⟩ := exists_pow_eq_mul hXN hn hy (orderOf (n * y))
        rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have h1 : y ^ orderOf (n * y) = n'⁻¹ := by
          have h2 : n' * y ^ orderOf (n * y) = 1 := by rw [← hpow, pow_orderOf_eq_one]
          exact eq_inv_of_mul_eq_one_right h2
        have h2 : y ^ orderOf (n * y) ∈ θX :=
          hNX (Subgroup.mem_inf.mpr ⟨h1 ▸ inv_mem hn', pow_mem hy _⟩)
        obtain ⟨z, hz, hzeq⟩ := h2
        have : z = (⟨y, hy⟩ : ↥X) ^ orderOf (n * y) := Subtype.ext (by
          simp only [Subgroup.coe_subtype] at hzeq
          rw [hzeq, Subgroup.coe_pow])
        rwa [← this]
  have hM : ∀ W : Subgroup (↥X ⧸ aschbacherSolvableCore 3 ↥X), W.Normal →
      (∀ w ∈ W, σ w = w) → (∀ z : ↥X ⧸ aschbacherSolvableCore 3 ↥X, σ z = z →
        (∃ k : ℕ, Nat.Coprime k 3 ∧ z ^ k = 1) → z ∈ W) → False := by
    intro W hWn hWσ hQW
    set XW : Subgroup G := (W.comap π).map X.subtype with hXW
    have hXWX : XW ≤ X := Subgroup.map_subtype_le _
    have hmemXW : ∀ (y : G) (hy : y ∈ X), π ⟨y, hy⟩ ∈ W → y ∈ XW := fun y hy hyW =>
      ⟨⟨y, hy⟩, hyW, rfl⟩
    have hXWN : XW ≤ Subgroup.normalizer (N : Set G) := hXWX.trans hXN
    have hXnorm : X ≤ Subgroup.normalizer (XW : Set G) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        refine ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹, ?_, by simp⟩
        show π (⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹) ∈ W
        rw [map_mul, map_mul, map_inv]
        exact hWn.conj_mem _ hy' _
      · rintro ⟨y', hy', hy'eq⟩
        have hyX : y ∈ X := by
          have h1 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
          rw [h1]
          exact mul_mem (mul_mem (inv_mem hx) (hy'eq ▸ y'.2)) hx
        refine ⟨⟨y, hyX⟩, ?_, rfl⟩
        show π ⟨y, hyX⟩ ∈ W
        have h1 : (⟨y, hyX⟩ : ↥X) = ⟨x, hx⟩⁻¹ * y' * ⟨x, hx⟩ := Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [show (y' : G) = x * y * x⁻¹ from hy'eq]
          group)
        rw [h1, map_mul, map_mul, map_inv]
        have := hWn.conj_mem _ hy' (π ⟨x, hx⟩)⁻¹
        simpa using this
    have huXW : u ∈ Subgroup.normalizer (XW : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨y', hy', rfl⟩
        have hy'' : u * (y' : G) * u⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp huX _).mp y'.2
        refine ⟨⟨_, hy''⟩, ?_, rfl⟩
        show π ⟨_, hy''⟩ ∈ W
        have h1 : σ (π ⟨(y' : G), y'.2⟩) = π ⟨_, hy''⟩ := hσmk _ y'.2
        rw [← h1, hWσ _ hy']
        exact hy'
      · rintro ⟨y'', hy'', hy''eq⟩
        have hyX : y ∈ X := by
          have h1 : y = u⁻¹ * (u * y * u⁻¹) * u := by group
          have h2 : u * y * u⁻¹ ∈ X := by
            rw [← hy''eq]
            exact y''.2
          rw [h1]
          have := (Subgroup.mem_normalizer_iff.mp (inv_mem huX) _).mp h2
          simpa [mul_assoc] using this
        refine ⟨⟨y, hyX⟩, ?_, rfl⟩
        show π ⟨y, hyX⟩ ∈ W
        have h1 : σ (π ⟨y, hyX⟩) = π y'' := by
          rw [hσmk y hyX]
          congr 1
          exact Subtype.ext hy''eq.symm
        have h2 : σ (π y'') = π y'' := hWσ _ hy''
        have h3 : π ⟨y, hyX⟩ = π y'' := σ.injective (h1.trans h2.symm)
        rw [h3]
        exact hy''
    set M := N ⊔ XW with hMdef
    have hMu : ∀ m ∈ M, ⁅m, u⁆ ∈ N := fun m hm =>
      commutator_mem_of_mem_sup hXWN (hCbN huCb) (fun x hx => by
        obtain ⟨x', hx', rfl⟩ := hx
        have h1 : σ (π x') = π x' := hWσ _ hx'
        rw [show x' = ⟨(x' : G), x'.2⟩ from rfl, hσmk _ x'.2] at h1
        have h2 := (hmk _ _ _ _).mp h1
        have h3 : ⁅(x' : G), u⁆ = (u * x' * u⁻¹ * (x' : G)⁻¹)⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [Subgroup.coe_subtype, h3]
        exact hθXN (inv_mem h2)) hm
    have hQM : Q ≤ M := by
      intro q hq
      obtain ⟨n, hn, y, hy, rfl, hfix, hk⟩ := himg q hq
      exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right
        (hmemXW y hy (hQW _ hfix hk)))
    have hM₀M : N ⊔ X ≤ Subgroup.normalizer (M : Set G) :=
      sup_le (le_normalizer_sup_left hXWN)
        (le_normalizer_sup (A := X) hXN hXnorm)
    have huM : u ∈ Subgroup.normalizer (M : Set G) :=
      le_normalizer_sup (A := Subgroup.zpowers u) (Subgroup.zpowers_le.mpr (hCbN huCb))
        (Subgroup.zpowers_le.mpr huXW) (Subgroup.mem_zpowers u)
    exact hQb (le_pPrimeCoreOf_of_trivial_on hu3 le_sup_left (sup_le le_sup_left
      (hXWX.trans le_sup_right)) (sup_le (pPrimeCoreOf_le 3 Cb) hXCb) hM₀M hCX huM (hY.2 huA)
      huCb hMu hR (coprime_card_pPrimeCoreOf 3 _) hQR hQYC hQM)
  have hUcen : centerIn U ≤ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := fun x hx =>
    mem_center_of_mem_inf hUV' hUV (hUZ ▸ hx)
  have hVcen : centerIn V ≤ Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X) := fun x hx =>
    mem_center_of_mem_inf hUV' hUV (hVZ ▸ hx)
  have hfixU : (∃ y₀ ∈ U, σ y₀ * y₀⁻¹ ∉ centerIn U) → ∀ z : ↥X ⧸ aschbacherSolvableCore 3 ↥X,
      σ z = z → (∃ k : ℕ, Nat.Coprime k 3 ∧ z ^ k = 1) → z ∈ V := by
    rintro ⟨y₀, hy₀, hy₀σ⟩ z hz ⟨k, hk3, hzk⟩
    obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hUV' z
    obtain ⟨h1, -, h3', -⟩ := fixed_components hUV' hUV hσU hσV hy hv hz hzk
    have hyZ := mem_centerIn_of_fixed eU hσ3 hσU hy₀ hy₀σ hy (hUZ ▸ h1) (hUZ ▸ h3') hk3
    rw [← hUZ] at hyZ
    exact mul_mem hyZ.2 hv
  have hfixV : (∃ v₀ ∈ V, σ v₀ * v₀⁻¹ ∉ centerIn V) → ∀ z : ↥X ⧸ aschbacherSolvableCore 3 ↥X,
      σ z = z → (∃ k : ℕ, Nat.Coprime k 3 ∧ z ^ k = 1) → z ∈ U := by
    rintro ⟨v₀, hv₀, hv₀σ⟩ z hz ⟨k, hk3, hzk⟩
    obtain ⟨y, hy, v, hv, rfl⟩ := exists_mul_eq hUV' z
    obtain ⟨-, h2, -, h4⟩ := fixed_components hUV' hUV hσU hσV hy hv hz hzk
    have hvZ := mem_centerIn_of_fixed eV hσ3 hσV hv₀ hv₀σ hv (hVZ ▸ h2) (hVZ ▸ h4) hk3
    rw [← hVZ] at hvZ
    exact mul_mem hy hvZ.1
  by_cases hUt : ∀ y ∈ U, σ y * y⁻¹ ∈ centerIn U
  · by_cases hVt : ∀ v ∈ V, σ v * v⁻¹ ∈ centerIn V
    ·
      refine hM ⊤ inferInstance (fun w _ => ?_) (fun _ _ _ => Subgroup.mem_top _)
      have htop := top_eq_commutator_sup hUV' hUV
      have hw : w ∈ ⁅U, U⁆ ⊔ ⁅V, V⁆ := htop ▸ Subgroup.mem_top w
      have hle : ⁅U, U⁆ ⊔ ⁅V, V⁆ ≤ MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id _) :=
        sup_le (fun x hx => fixed_of_mem_commutator hUcen hUt hx)
          (fun x hx => fixed_of_mem_commutator hVcen hVt hx)
      exact hle hw
    ·
      push Not at hVt
      refine hM ⁅U, U⁆ (Subgroup.commutator_normal U U)
        (fun w hw => fixed_of_mem_commutator hUcen hUt hw) ?_
      intro z hfix hk
      obtain ⟨k, hk3, hzk⟩ := hk
      exact mem_commutator_of_mem (U := V) (V := U) (by rw [sup_comm]; exact hUV')
        (by rw [Subgroup.commutator_comm]; exact hUV) (by rw [inf_comm]; exact h3)
        (hfixV hVt _ hfix ⟨k, hk3, hzk⟩) hzk hk3
  · push Not at hUt
    by_cases hVt : ∀ v ∈ V, σ v * v⁻¹ ∈ centerIn V
    ·
      refine hM ⁅V, V⁆ (Subgroup.commutator_normal V V)
        (fun w hw => fixed_of_mem_commutator hVcen hVt hw) ?_
      intro z hfix hk
      obtain ⟨k, hk3, hzk⟩ := hk
      exact mem_commutator_of_mem hUV' hUV h3 (hfixU hUt _ hfix ⟨k, hk3, hzk⟩) hzk hk3
    ·
      push Not at hVt
      apply hcontra
      intro q hq
      obtain ⟨n, hn, y, hy, rfl, hfix, k, hk3, hzk⟩ := himg q hq
      have hzU := hfixV hVt _ hfix ⟨k, hk3, hzk⟩
      have hzV := hfixU hUt _ hfix ⟨k, hk3, hzk⟩
      have hz1 : π ⟨y, hy⟩ = 1 := by
        have h1 := Subgroup.orderOf_dvd_natCard (U ⊓ V) ⟨hzU, hzV⟩
        rw [h3] at h1
        have hd : orderOf (π ⟨y, hy⟩) ∣ Nat.gcd k 3 :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzk) h1
        rw [hk3, Nat.dvd_one] at hd
        exact orderOf_eq_one_iff.mp hd
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
      exact mul_mem hn (hθXN ⟨_, hz1, rfl⟩)

end Item148PtRes

theorem step148PointHJdA6A6_holds : Step148PointHJdA6A6 := by
  intro G _ _ A c L h Y hY _ hYB B hB Q hQ hQY b hb hb1 _ hQb _ _ _ _ _ _ _ _ _ _ _ X _ hCX h𝒳 hT
    hQX
  obtain ⟨𝒳, h𝒳b, -, hX𝒳⟩ := h𝒳
  exact (Item148PtRes.false_of_centralProduct_A6 h hY hYB hB hQ hQY hb hb1 hQb hCX h𝒳b hX𝒳 hT
    hQX).elim

end CFSG.RankThree.PartTwo.Sec14
