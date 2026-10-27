module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
import CFSG.RankThree.PartOne.S10.NontrivialPlaneTwoCommutatorAction
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.GroupTheory.SteinbergBMFaithfulRankThreeLineKernel
import CFSG.RankThree.GroupTheory.SteinbergBMFaithfulPlaneTwoGroupWitness
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank Subgroup
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory.SteinbergBY
  CFSG.RankThree.GroupTheory
open scoped commutatorElement Pointwise

namespace NormalPCoreWitness

section Phase3

variable {H : Type} [Group H] [Finite H] {p : ℕ}

theorem commute_of_commutators_mem_centralized (hp : p.Prime) {Q M : Subgroup H} {x : H}
    (hxp : x ^ p = 1) (hpM : ¬ p ∣ Nat.card M)
    (hxM : ∀ m ∈ M, x * m = m * x)
    (hcomm : ∀ a ∈ zpowers x, ∀ q ∈ Q, q⁻¹ * (a * q * a⁻¹) ∈ M)
    (hinvM : ∀ a ∈ zpowers x, ∀ m ∈ M, a * m * a⁻¹ ∈ M) {q : H} (hq : q ∈ Q) :
    x * q = q * x := by
  have : Fact p.Prime := ⟨hp⟩
  have hxpg : IsPGroup p (zpowers x) := by
    have := IsElementaryAbelian.zpowers_of_pow_eq_one hxp
    exact IsElementaryAbelian.isPGroup p _
  let α : zpowers x →* MulAut H := MulAut.conj.comp (zpowers x).subtype
  have hinv : ∀ (a : zpowers x) (y : H), q⁻¹ * y ∈ M → q⁻¹ * α a y ∈ M := by
    intro a y hy
    have h : q⁻¹ * α a y =
        (q⁻¹ * ((a : H) * q * (a : H)⁻¹)) * ((a : H) * (q⁻¹ * y) * (a : H)⁻¹) := by
      change q⁻¹ * ((a : H) * y * (a : H)⁻¹) = _
      group
    rw [h]
    exact M.mul_mem (hcomm a a.2 q hq) (hinvM a a.2 _ hy)
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed p hxpg α M
    hpM q).2 hinv
  have hxc : x * c = c * x := by
    have h := hfix ⟨x, mem_zpowers x⟩
    change x * c * x⁻¹ = c at h
    calc x * c = x * c * x⁻¹ * x := by group
      _ = c * x := by rw [h]
  have hq' : q = c * (q⁻¹ * c)⁻¹ := by group
  have hxm' : x * (q⁻¹ * c)⁻¹ = (q⁻¹ * c)⁻¹ * x := by
    have h := hxM _ hc
    calc x * (q⁻¹ * c)⁻¹ = (q⁻¹ * c)⁻¹ * ((q⁻¹ * c) * x) * (q⁻¹ * c)⁻¹ := by group
      _ = (q⁻¹ * c)⁻¹ * (x * (q⁻¹ * c)) * (q⁻¹ * c)⁻¹ := by rw [h]
      _ = (q⁻¹ * c)⁻¹ * x := by group
  calc x * q = x * (c * (q⁻¹ * c)⁻¹) := by rw [← hq']
    _ = (x * c) * (q⁻¹ * c)⁻¹ := by group
    _ = (c * x) * (q⁻¹ * c)⁻¹ := by rw [hxc]
    _ = c * (x * (q⁻¹ * c)⁻¹) := by group
    _ = c * ((q⁻¹ * c)⁻¹ * x) := by rw [hxm']
    _ = (c * (q⁻¹ * c)⁻¹) * x := by group
    _ = q * x := by rw [← hq']

theorem commutes_with_normal_p_subgroup
    {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hrank : localRank p Y ≤ 3) {D Q B : Subgroup Y} [D.Normal] (hD : IsPGroup p D)
    (hQ2 : IsPGroup 2 Q) (hB : IsElementaryAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hBQ : B ≤ normalizer (Q : Set Y))
    (hfaith : ∀ x ∈ B, (∀ q ∈ Q, x * q = q * x) → x = 1) (hQB : ⁅Q, B⁆ = Q) :
    ⁅Q, D⁆ = ⊥ := by
  have h311 := nontrivial_plane_two_commutator_action_on_prime_group_rank_obstruction
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (B ≤ normalizer (Q : Set Y)) := ⟨hBQ⟩
  have hBp : IsPGroup p B := IsElementaryAbelian.isPGroup p B
  have hDQ : Disjoint D Q := IsPGroup.disjoint_of_ne p 2 hp2 D Q hD hQ2
  have hQB' : Disjoint Q B := (IsPGroup.disjoint_of_ne 2 p hp2.symm Q B hQ2 hBp)
  let ψK : (Q ⋊[MulDistribMulAction.toMulAut B Q] B) →* Y :=
    SemidirectProduct.lift Q.subtype B.subtype (by
      intro g
      refine MonoidHom.ext fun s => ?_
      change ((g • s : Q) : Y) = (g : Y) * (s : Y) * (g : Y)⁻¹
      exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B Q g s)
  have hψK_inl : ∀ s : Q, ψK (SemidirectProduct.inl s) = (s : Y) := fun s => by simp [ψK]
  let β : (Q ⋊[MulDistribMulAction.toMulAut B Q] B) →* MulAut D :=
    (MulAut.conjNormal (H := D)).comp ψK
  have hβ : ∀ (k : Q ⋊[MulDistribMulAction.toMulAut B Q] B) (d : D),
      ((β k d : D) : Y) = ψK k * d * (ψK k)⁻¹ := fun k d => by
    change ((MulAut.conjNormal (ψK k) d : D) : Y) = _
    rw [MulAut.conjNormal_apply]
  have hfaith' : ∀ c : B, (∀ s : Q, c • s = s) → c = 1 := by
    intro c hc
    refine Subtype.ext (hfaith c c.2 fun q hq => ?_)
    have h := congrArg Subtype.val (hc ⟨q, hq⟩)
    change (c : Y) * q * (c : Y)⁻¹ = q at h
    calc (c : Y) * q = (c : Y) * q * (c : Y)⁻¹ * c := by group
      _ = q * c := by rw [h]
  have hsmulY : ∀ (c : B) (t : Q), ((c • t : Q) : Y) = (c : Y) * t * (c : Y)⁻¹ := fun c t =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe B Q c t
  have hDK : ∀ k : (Q ⋊[MulDistribMulAction.toMulAut B Q] B), ψK k ∈ D → k = 1 := by
    intro k hk
    obtain ⟨s, c⟩ := k
    have hx : (s : Y) * c ∈ D := hk
    have hcomm : ∀ t : Q, (s : Y) * ((c • t : Q) : Y) = t * s := by
      intro t
      have hu1 : (s : Y) * c * t * ((s : Y) * c)⁻¹ * (t : Y)⁻¹ ∈ D := by
        have h1 := (inferInstance : D.Normal).conj_mem _ (D.inv_mem hx) (t : Y)
        have h2 := D.mul_mem hx h1
        convert h2 using 1
        group
      have hu2 : (s : Y) * c * t * ((s : Y) * c)⁻¹ * (t : Y)⁻¹ ∈ Q := by
        have hct := (c • t : Q).2
        rw [hsmulY] at hct
        have h3 : (s : Y) * c * t * ((s : Y) * c)⁻¹ * (t : Y)⁻¹ =
            (s : Y) * ((c : Y) * t * (c : Y)⁻¹) * (s : Y)⁻¹ * (t : Y)⁻¹ := by group
        rw [h3]
        exact Q.mul_mem (Q.mul_mem (Q.mul_mem s.2 hct) (Q.inv_mem s.2)) (Q.inv_mem t.2)
      have hu : (s : Y) * c * t * ((s : Y) * c)⁻¹ * (t : Y)⁻¹ = 1 := by
        have := hDQ.le_bot ⟨hu1, hu2⟩
        rwa [Subgroup.mem_bot] at this
      rw [hsmulY]
      calc (s : Y) * ((c : Y) * t * (c : Y)⁻¹)
          = ((s : Y) * c * t * ((s : Y) * c)⁻¹ * (t : Y)⁻¹) * t * s := by group
        _ = t * s := by rw [hu, one_mul]
    have hinner : ∀ t : Q, c • t = s⁻¹ * t * s := by
      intro t
      refine Subtype.ext ?_
      change ((c • t : Q) : Y) = (s : Y)⁻¹ * t * s
      have h := hcomm t
      rw [hsmulY] at h ⊢
      calc (c : Y) * t * (c : Y)⁻¹ = (s : Y)⁻¹ * ((s : Y) * ((c : Y) * t * (c : Y)⁻¹)) := by
            group
        _ = (s : Y)⁻¹ * (t * s) := by rw [h]
        _ = _ := by group
    have hc1 : c = 1 := PlaneAux.eq_one_of_smul_eq_inner hp hp2 hBp hQ2 hfaith' hinner
    subst hc1
    have hsD : (s : Y) ∈ D := by simpa using hx
    have hs1 : (s : Y) = 1 := by
      have := hDQ.le_bot ⟨hsD, s.2⟩
      rwa [Subgroup.mem_bot] at this
    have : s = 1 := Subtype.ext hs1
    subst this
    rfl
  let ψ : (D ⋊[β] (Q ⋊[MulDistribMulAction.toMulAut B Q] B)) →* Y :=
    SemidirectProduct.lift D.subtype ψK (by
      intro k
      refine MonoidHom.ext fun d => ?_
      change ((β k d : D) : Y) = ψK k * (d : Y) * (ψK k)⁻¹
      exact hβ k d)
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨d, k⟩ := x
    have hx' : (d : Y) * ψK k = 1 := hx
    have hψk : ψK k = (d : Y)⁻¹ := eq_inv_of_mul_eq_one_right hx'
    have hk1 : k = 1 := hDK k (by rw [hψk]; exact D.inv_mem d.2)
    subst hk1
    have hd1 : d = 1 := Subtype.ext (by simpa using hx')
    subst hd1
    rfl
  have hlocal : localRank p (D ⋊[β] (Q ⋊[MulDistribMulAction.toMulAut B Q] B)) ≤ 3 :=
    (PlaneAux.localRank_le_of_injective hp ψ hψinj).trans hrank
  have hevenX : evenRank (D ⋊[β] (Q ⋊[MulDistribMulAction.toMulAut B Q] B)) ≤ 3 := by
    refine PlaneAux.evenRank_le_of_localRank_le_of_card hp ?_ hlocal
    intro r hr hrdvd
    rw [SemidirectProduct.card, SemidirectProduct.card] at hrdvd
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hD
    obtain ⟨b', hb'⟩ := IsPGroup.iff_card.mp hQ2
    rw [ha, hb', hBcard] at hrdvd
    rcases (Nat.Prime.dvd_mul hr).1 hrdvd with h | h
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))
  have hcommTop : actionCommutator B (⊤ : Subgroup Q) = ⊤ := by
    have hle : ⁅Q, B⁆ ≤ (actionCommutator B (⊤ : Subgroup Q)).map Q.subtype := by
      refine Subgroup.commutator_le.mpr fun q hq c hc => ?_
      set s : Q := ⟨q⁻¹, Q.inv_mem hq⟩ with hs
      set c' : B := ⟨c, hc⟩ with hc'
      refine ⟨s⁻¹ * (c' • s), gen_mem_actionCommutator (mem_top _) c', ?_⟩
      change ((s⁻¹ * (c' • s) : Q) : Y) = _
      rw [Subgroup.coe_mul, hsmulY]
      change (q⁻¹)⁻¹ * ((c : Y) * q⁻¹ * (c : Y)⁻¹) = _
      simp only [commutatorElement_def]
      group
    refine eq_top_iff.mpr fun s _ => ?_
    obtain ⟨w, hw, hws⟩ := hQB.symm.le.trans hle s.2
    have : w = s := Subtype.ext hws
    exact this ▸ hw
  by_contra hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hne
  obtain ⟨q, hq, hqc⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  rw [Subgroup.mem_centralizer_iff] at hqc
  push Not at hqc
  obtain ⟨d, hd, hdq⟩ := hqc
  have hnontriv : ∃ y ∈ actionCommutator B (⊤ : Subgroup Q), ∃ d : D,
      β (SemidirectProduct.inl y) d ≠ d := by
    refine ⟨⟨q, hq⟩, by rw [hcommTop]; exact mem_top _, ⟨d, hd⟩, fun h => hdq ?_⟩
    have h2 := congrArg Subtype.val h
    rw [hβ, hψK_inl] at h2
    change (q : Y) * d * (q : Y)⁻¹ = d at h2
    calc (d : Y) * q = (q : Y) * d * (q : Y)⁻¹ * q := by rw [h2]
      _ = q * d := by group
  have h3 := h311 p hp hp3 B Q hB hBcard hQ2 hfaith' D hD β hnontriv
  omega

theorem card_map_of_injOn {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (K : Subgroup X)
    (hf : ∀ x ∈ K, ∀ y ∈ K, f x = f y → x = y) : Nat.card (K.map f) = Nat.card K := by
  have hinj : Function.Injective (f.comp K.subtype) := fun x y hxy =>
    Subtype.ext (hf x x.2 y y.2 hxy)
  calc Nat.card (K.map f) = Nat.card (f.comp K.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
    _ = Nat.card K := Nat.card_range_of_injective hinj

omit [Finite H] in
theorem exists_plane_complement {p : ℕ} (hp : p.Prime) {A : Subgroup H}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) {b : H} (hbA : b ∈ A)
    (hb1 : b ≠ 1) :
    ∃ B' : Subgroup H, B' ≤ A ∧ Nat.card B' = p ^ 2 ∧ B' ⊓ zpowers b = ⊥ ∧
      B' ⊔ zpowers b = A := by
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hzA : zpowers b ≤ A := zpowers_le.mpr hbA
  have hzel : IsElementaryAbelian p (zpowers b) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := p) b hbA)
  obtain ⟨C, hC⟩ := IsElementaryAbelian.exists_isCompl p A ((zpowers b).subgroupOf A)
  have hZcard : Nat.card ((zpowers b).subgroupOf A) = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers,
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := p) b hbA) hb1]
  have hcomm : ∀ x y : A, x * y = y * x := fun x y => hA.is_comm.comm x y
  have hnormal : C.Normal := ⟨fun n hn g => by rwa [hcomm g n, mul_inv_cancel_right]⟩
  have hmul : ((zpowers b).subgroupOf A : Set A) * (C : Set A) = Set.univ := by
    rw [← Subgroup.mul_normal, hC.sup_eq_top]
    rfl
  have hcompl : ((zpowers b).subgroupOf A).IsComplement' C :=
    isComplement'_of_disjoint_and_mul_eq_univ hC.disjoint hmul
  have hCcard : Nat.card C = p ^ 2 := by
    have h := hcompl.card_mul_card
    rw [hZcard, hAcard] at h
    have hp0 : 0 < p := hp.pos
    exact Nat.eq_of_mul_eq_mul_left hp0 (by rw [h]; ring)
  refine ⟨C.map A.subtype, Subgroup.map_subtype_le C, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective A.subtype_injective, hCcard]
  · rw [eq_bot_iff]
    rintro x ⟨⟨c, hc, rfl⟩, hxz⟩
    have hcZ : c ∈ (zpowers b).subgroupOf A := hxz
    have h1 : c ∈ (zpowers b).subgroupOf A ⊓ C := ⟨hcZ, hc⟩
    rw [hC.inf_eq_bot, Subgroup.mem_bot] at h1
    simp [h1]
  · apply le_antisymm
    · exact sup_le (Subgroup.map_subtype_le C) hzA
    · intro a ha
      have hmem : (⟨a, ha⟩ : A) ∈ (zpowers b).subgroupOf A ⊔ C := hC.sup_eq_top ▸ mem_top _
      have h2 := Subgroup.mem_map_of_mem A.subtype hmem
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hzA, sup_comm] at h2
      exact h2

theorem mem_zpowers_of_centralizes_mod {p : ℕ} (hp : p.Prime) {A Q : Subgroup H} {b : H}
    (hA : IsElementaryAbelian p A) (hAQ : A ≤ normalizer (Q : Set H))
    (hker : ∀ x ∈ A, (∀ q ∈ Q, x * q = q * x) → x ∈ zpowers b) (N : Subgroup H) [N.Normal]
    (hpN : ¬ p ∣ Nat.card N) (hcent : ∀ x ∈ A, ∀ q ∈ Q ⊓ N, x * q = q * x) {x : H} (hxA : x ∈ A)
    (hxbar : ∀ q ∈ Q, QuotientGroup.mk' N x * QuotientGroup.mk' N q =
      QuotientGroup.mk' N q * QuotientGroup.mk' N x) : x ∈ zpowers b := by
  have := hA
  have hzA : zpowers x ≤ A := zpowers_le.mpr hxA
  have hQA : ∀ a ∈ zpowers x, ∀ q ∈ Q, a * q * a⁻¹ ∈ Q := fun a ha q hq =>
    (mem_normalizer_iff.mp (hAQ (hzA ha)) q).mp hq
  have hNA : ∀ a : H, ∀ n ∈ N, a * n * a⁻¹ ∈ N := fun a n hn => Normal.conj_mem inferInstance n hn a
  have hcommπ : ∀ a ∈ zpowers x, ∀ q ∈ Q, Commute (QuotientGroup.mk' N a)
      (QuotientGroup.mk' N q) := by
    intro a ha q hq
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    rw [map_zpow]
    exact Commute.zpow_left (hxbar q hq) k
  refine hker x hxA fun q hq => ?_
  refine commute_of_commutators_mem_centralized hp (elemPow_eq_one_of_isElementaryAbelian
    (p := p) x hxA) (fun h => hpN (h.trans (Subgroup.card_dvd_of_le inf_le_right))) (hcent x hxA)
    (fun a ha q hq => ⟨?_, ?_⟩) (fun a ha m hm => ⟨hQA a ha m hm.1, hNA a m hm.2⟩) hq
  · exact Q.mul_mem (Q.inv_mem hq) (hQA a ha q hq)
  · have h1 : QuotientGroup.mk' N (q⁻¹ * (a * q * a⁻¹)) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv]
      have h := (hcommπ a ha q hq).eq
      calc (QuotientGroup.mk' N q)⁻¹ * (QuotientGroup.mk' N a * QuotientGroup.mk' N q *
          (QuotientGroup.mk' N a)⁻¹) = (QuotientGroup.mk' N q)⁻¹ * (QuotientGroup.mk' N q *
            QuotientGroup.mk' N a * (QuotientGroup.mk' N a)⁻¹) := by rw [h]
        _ = 1 := by group
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem quotient_commutes_with_pcore
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hrank : localRank p H ≤ 3) {A Q : Subgroup H} {b : H}
    (hA : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3) (hbA : b ∈ A) (hb1 : b ≠ 1)
    (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ normalizer (Q : Set H)) (hQA : ⁅Q, A⁆ = Q)
    (hbQ : ∀ q ∈ Q, b * q = q * b)
    (hker : ∀ x ∈ A, (∀ q ∈ Q, x * q = q * x) → x ∈ zpowers b)
    (hcent : ∀ x ∈ A, ∀ q ∈ Q ⊓ aschbacherSolvableCore p H, x * q = q * x) :
    ⁅Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
      CFSG.pCore p (H ⧸ aschbacherSolvableCore p H)⁆ = ⊥ := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  set N := aschbacherSolvableCore p H with hNdef
  have hpN : ¬ p ∣ Nat.card N := (solvable_prime_complement_core_characterization (H := H) hp).2.2.1
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨B', hB'A, hB'card, hB'b, hB'sup⟩ := exists_plane_complement hp hA hAcard hbA hb1
  have hB'el : IsElementaryAbelian p B' :=
    CFSG.RankThree.GroupTheory.SteinbergBM.isElementaryAbelian_of_le hA hB'A
  have hB'p : IsPGroup p B' := IsElementaryAbelian.isPGroup p B'
  have hdisA : Disjoint A N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hAcard]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN))
  have hπA : ∀ x ∈ A, ∀ y ∈ A, π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ N := QuotientGroup.eq.mp hxy
    have h2 : x⁻¹ * y ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem hx) hy, h1⟩
    rw [hdisA.eq_bot, Subgroup.mem_bot] at h2
    exact eq_of_inv_mul_eq_one h2
  have hker' : ∀ y ∈ B', (∀ q ∈ Q, π y * π q = π q * π y) → y = 1 := by
    intro y hy hcomm
    have hyb : y ∈ zpowers b :=
      mem_zpowers_of_centralizes_mod hp hA hAQ hker N hpN hcent (hB'A hy) hcomm
    have h1 : y ∈ B' ⊓ zpowers b := ⟨hy, hyb⟩
    rw [hB'b, Subgroup.mem_bot] at h1
    exact h1
  have hzq : ∀ z ∈ zpowers b, ∀ q ∈ Q, z * q = q * z := by
    intro z hz q hq
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (hbQ q hq) k).eq
  have hzy : ∀ z ∈ zpowers b, ∀ y ∈ B', z * y = y * z := fun z hz y hy =>
    congrArg Subtype.val (hA.is_comm.comm ⟨z, zpowers_le.mpr hbA hz⟩ ⟨y, hB'A hy⟩)
  have hB'norm : B' ≤ normalizer (zpowers b : Set H) := by
    intro y hy
    rw [mem_normalizer_iff]
    intro g
    constructor
    · intro hg
      have h := hzy g hg y hy
      have h2 : y * g * y⁻¹ = g := by
        calc y * g * y⁻¹ = g * y * y⁻¹ := by rw [h]
          _ = g := by group
      rw [h2]
      exact hg
    · intro hg
      have h := hzy _ hg y⁻¹ (B'.inv_mem hy)
      have h2 : y * g * y⁻¹ = g := by
        calc y * g * y⁻¹ = (y * g * y⁻¹) * y⁻¹ * y := by group
          _ = y⁻¹ * (y * g * y⁻¹) * y := by rw [h]
          _ = g := by group
      exact h2 ▸ hg
  have hQB' : ⁅Q, B'⁆ = Q := by
    refine le_antisymm ((Subgroup.commutator_mono le_rfl hB'A).trans hQA.le) ?_
    refine hQA.symm.le.trans (Subgroup.commutator_le.mpr fun q hq a ha => ?_)
    have ha' : a ∈ (↑(B' ⊔ zpowers b) : Set H) := hB'sup ▸ ha
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B' (zpowers b) hB'norm] at ha'
    obtain ⟨y, hy, z, hz, rfl⟩ := ha'
    have hzq' := hzq z hz q hq
    have hcomm : ⁅q, y * z⁆ = ⁅q, y⁆ := by
      simp only [commutatorElement_def]
      calc q * (y * z) * q⁻¹ * (y * z)⁻¹ = q * y * (z * q⁻¹ * z⁻¹) * y⁻¹ := by group
        _ = q * y * q⁻¹ * y⁻¹ := by
          have h3 : z * q * z⁻¹ = q := by
            calc z * q * z⁻¹ = q * z * z⁻¹ := by rw [hzq']
              _ = q := by group
          have : z * q⁻¹ * z⁻¹ = q⁻¹ := by
            calc z * q⁻¹ * z⁻¹ = (z * q * z⁻¹)⁻¹ := by group
              _ = q⁻¹ := by rw [h3]
          rw [this]
    rw [hcomm]
    exact Subgroup.commutator_mem_commutator hq hy
  have hQ2' : IsPGroup 2 (Q.map π) := hQ2.map π
  have hBbEl : IsElementaryAbelian p (B'.map π) := by
    have := hB'el
    exact IsElementaryAbelian.map (A := B') π
  have hBbCard : Nat.card (B'.map π) = p ^ 2 := by
    rw [card_map_of_injOn π B' (fun x hx y hy h => hπA x (hB'A hx) y (hB'A hy) h), hB'card]
  have hBbQ : B'.map π ≤ normalizer ((Q.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) :=
    (Subgroup.map_mono (hB'A.trans hAQ)).trans (Subgroup.le_normalizer_map π)
  have hfaith : ∀ x ∈ B'.map π, (∀ q ∈ Q.map π, x * q = q * x) → x = 1 := by
    rintro _ ⟨y, hy, rfl⟩ hcomm
    rw [hker' y hy fun q hq => hcomm (π q) ⟨q, hq, rfl⟩, map_one]
  have hQB : ⁅Q.map π, B'.map π⁆ = Q.map π := by
    rw [← Subgroup.map_commutator, hQB']
  have hrank' : localRank p (H ⧸ N) ≤ 3 :=
    (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 N hpN).trans hrank
  exact commutes_with_normal_p_subgroup hp hp3 hrank' (D := CFSG.pCore p (H ⧸ N))
    CFSG.pCore_isPGroup hQ2' hBbEl hBbCard hBbQ hfaith hQB

end Phase3

section Transfer

variable {G : Type} [Group G]

theorem transfer_line_witness {A S : Subgroup G} [Fact (A ≤ normalizer (S : Set G))]
    {a : G} (haA : a ∈ A) {b : A} {Q' : Subgroup S}
    (hQ2 : IsPGroup 2 Q') (hinv : ∀ c : A, ∀ x ∈ Q', c • x ∈ Q')
    (hQc : actionCommutator A Q' = Q') (hbQ : ∀ x ∈ Q', b • x = x)
    (hker : ∀ c : A, (∀ x ∈ Q', c • x = x) ↔ c ∈ zpowers b)
    (hmoved : ∃ x ∈ Q', (⟨a, haA⟩ : A) • x ≠ x) (hbna : b ∉ zpowers (⟨a, haA⟩ : A)) :
    (b : G) ∈ A ∧ (b : G) ∉ zpowers a ∧ ∃ Q : Subgroup G, IsPGroup 2 Q ∧
      A ≤ normalizer (Q : Set G) ∧ Q ≤ centralizer ({(b : G)} : Set G) ∧ ⁅Q, A⁆ = Q ∧
      ⁅Q, zpowers a⁆ ≠ ⊥ ∧ ∀ x ∈ A, (∀ q ∈ Q, x * q = q * x) → x ∈ zpowers (b : G) := by
  have hsmul : ∀ (c : A) (s : S), ((c • s : S) : G) = (c : G) * s * (c : G)⁻¹ := fun c s =>
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe A S c s
  refine ⟨b.2, ?_, Q'.map S.subtype, hQ2.map _, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    exact hbna (mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)
  · refine CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_of_forall_conj_mem ?_
    rintro k hk _ ⟨s, hs, rfl⟩
    have := hinv ⟨k, hk⟩ s hs
    exact ⟨_, this, (hsmul ⟨k, hk⟩ s).symm⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (hbQ s hs)
    rw [hsmul] at h
    calc (s : G) * b = (b : G) * s * (b : G)⁻¹ * b := by rw [h]
      _ = b * s := by group
  · apply le_antisymm
    · refine Subgroup.commutator_le.mpr fun q hq a ha => ?_
      obtain ⟨s, hs, rfl⟩ := hq
      have h := hinv ⟨a, ha⟩ s⁻¹ (Q'.inv_mem hs)
      refine ⟨s * ((⟨a, ha⟩ : A) • s⁻¹), Q'.mul_mem hs h, ?_⟩
      show ((s * ((⟨a, ha⟩ : A) • s⁻¹) : S) : G) = ⁅(s : G), a⁆
      rw [Subgroup.coe_mul, hsmul]
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
    · refine Subgroup.map_le_iff_le_comap.mpr (hQc.symm.le.trans ((Subgroup.closure_le _).mpr ?_))
      rintro _ ⟨h, hh, a, rfl⟩
      change S.subtype (h⁻¹ * (a • h)) ∈ ⁅Q'.map S.subtype, A⁆
      have hmem : ((h⁻¹ : S) : G) ∈ Q'.map S.subtype := ⟨h⁻¹, Q'.inv_mem hh, rfl⟩
      have hc := Subgroup.commutator_mem_commutator hmem a.2
      convert hc using 1
      change ((h⁻¹ * (a • h) : S) : G) = _
      rw [Subgroup.coe_mul, hsmul]
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
  · intro hbot
    obtain ⟨x, hx, hxne⟩ := hmoved
    have hmem : ⁅(x : G), a⁆ ∈ ⁅Q'.map S.subtype, zpowers a⁆ :=
      Subgroup.commutator_mem_commutator ⟨x, hx, rfl⟩ (mem_zpowers a)
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hmem
    apply hxne
    refine Subtype.ext ?_
    rw [hsmul]
    have h1 : (x : G) * a = a * x := by
      calc (x : G) * a = ((x : G) * a * (x : G)⁻¹ * a⁻¹) * a * x := by group
        _ = a * x := by rw [hmem, one_mul]
    calc (⟨a, haA⟩ : A).1 * (x : G) * (⟨a, haA⟩ : A).1⁻¹ = x * a * a⁻¹ := by
          rw [← h1]
      _ = x := by group
  · intro x hxA hcomm
    have hc : (⟨x, hxA⟩ : A) ∈ zpowers b := by
      refine (hker _).mp fun s hs => ?_
      refine Subtype.ext ?_
      rw [hsmul]
      have h1 := hcomm s ⟨s, hs, rfl⟩
      calc x * (s : G) * x⁻¹ = (s : G) * x * x⁻¹ := by rw [h1]
        _ = s := by group
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hc
    exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

end Transfer


section Witness

variable {G : Type} [Group G] [Finite G]

theorem exists_line_witness {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchar : IsCharacteristicPType G 2) {A : Subgroup G} (hAe : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3)
    (hU : ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ normalizer (U : Set G))
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) :
    ∃ b ∈ A, b ∉ zpowers a ∧ ∃ Q : Subgroup G, IsPGroup 2 Q ∧ A ≤ normalizer (Q : Set G) ∧
      Q ≤ centralizer ({b} : Set G) ∧ ⁅Q, A⁆ = Q ∧ ⁅Q, zpowers a⁆ ≠ ⊥ ∧
      ∀ x ∈ A, (∀ q ∈ Q, x * q = q * x) → x ∈ zpowers b := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, hU1, hU2, hAU⟩ := hU
  obtain ⟨B', hB'⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) p (n := 2)
    (by rw [hAcard]; exact pow_dvd_pow p (by norm_num))
  have hB₀A : B'.map A.subtype ≤ A := Subgroup.map_subtype_le _
  have hB₀card : Nat.card (B'.map A.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective, hB']
  obtain ⟨⟨-, hS2, hAS⟩, hfaithS, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.characteristic_two_type_faithful_plane_two_group_witness
      hchar hp hp2 hAe hU2 hU1 hAU hB₀A hB₀card
  set S := inSubgroup (CFSG.pCore 2) (normalizer (U : Set G)) with hSdef
  have : Fact (A ≤ normalizer (S : Set G)) := ⟨hAS⟩
  have hfaith : ∀ c : A, (∀ s : S, c • s = s) → c = 1 := by
    intro c hc
    have hcS : (c : G) ∈ A ⊓ centralizer (S : Set G) := by
      refine ⟨c.2, mem_centralizer_iff.mpr fun s hs => ?_⟩
      have h := congrArg Subtype.val (hc ⟨s, hs⟩)
      change (c : G) * s * (c : G)⁻¹ = s at h
      calc s * (c : G) = (c : G) * s * (c : G)⁻¹ * c := by rw [h]
        _ = c * s := by group
    rw [hfaithS, Subgroup.mem_bot] at hcS
    exact Subtype.ext hcS
  obtain ⟨b, hbna, hQc, hker, hmoved, -, hQinv, hQle, hQ2⟩ :=
    SteinbergBM.faithful_rank_three_two_action_prescribed_actor_line_kernel_witness
      hp hp2 (A := A) (S := S) hAe hAcard hS2 hfaith (a := ⟨a, haA⟩)
      (fun h => ha1 (congrArg Subtype.val h))
  obtain ⟨hbA, hbna', Q, hQ2', hAQ, hQC, hQA, hQne, hQker⟩ := transfer_line_witness (A := A)
    (S := S) haA hQ2 hQinv hQc (fun x hx => (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b x).mp
      (hQle hx)) hker hmoved hbna
  exact ⟨b, hbA, hbna', Q, hQ2', hAQ, hQC, hQA, hQne, hQker⟩

theorem final_conjunct
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hvan : AschVanishing G p) (he : evenRank G ≤ 3)
    {A Q : Subgroup G} {b : G} (hAe : IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 3)
    (hbA : b ∈ A) (hb1 : b ≠ 1) (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hQC : Q ≤ centralizer ({b} : Set G)) (hQA : ⁅Q, A⁆ = Q)
    (hker : ∀ x ∈ A, (∀ q ∈ Q, x * q = q * x) → x ∈ zpowers b) :
    ⁅(Q.subgroupOf (centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore p ↥(centralizer ({b} : Set G)))),
      CFSG.pCore p (↥(centralizer ({b} : Set G)) ⧸
        aschbacherSolvableCore p ↥(centralizer ({b} : Set G)))⁆ = ⊥ := by
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have := hAe
  set C := centralizer ({b} : Set G) with hC
  have hbC : b ∈ C := mem_centralizer_singleton_iff.mpr rfl
  have hAC : A ≤ C := fun x hx => mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hAe.is_comm.comm ⟨x, hx⟩ ⟨b, hbA⟩))
  have hrank : localRank p ↥C ≤ 3 :=
    (CFSG.RankThree.OddKernel.localRank_le_evenRank hp hp2).trans
      ((CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le C).trans he)
  have hcoe : ∀ x : C, ∀ y : C, (x : G) * y = y * x → x * y = y * x := fun x y h => Subtype.ext h
  refine quotient_commutes_with_pcore hp hp3 hrank (A := A.subgroupOf C) (Q := Q.subgroupOf C)
    (b := ⟨b, hbC⟩) (IsElementaryAbelian.subgroupOf hAC) ?_ hbA ?_ hQ2.comap_subtype ?_ ?_ ?_ ?_ ?_
  · rw [Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv]
    exact hAcard
  · exact fun h => hb1 (congrArg Subtype.val h)
  · refine CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_of_forall_conj_mem ?_
    intro k hk x hx
    exact (mem_normalizer_iff.mp (hAQ hk) x).mp hx
  · apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQC,
      Subgroup.map_subgroupOf_eq_of_le hAC, hQA]
  · intro q hq
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hQC hq)).symm
  · intro x hx hxq
    have h1 := hker x hx fun q hq => congrArg Subtype.val (hxq ⟨q, hQC hq⟩ hq)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    exact mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  · intro x hx q hq
    set θ := inSubgroup (aschbacherSolvableCore p) C with hθ
    have hAθ : A ≤ normalizer (θ : Set G) :=
      le_normalizer_theta_of_le_normalizer hp (hAC.trans Subgroup.le_normalizer)
    have hU : A ≤ normalizer ((Q ⊓ θ : Subgroup G) : Set G) := by
      refine CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_of_forall_conj_mem ?_
      intro k hk y hy
      exact ⟨(mem_normalizer_iff.mp (hAQ hk) y).mp hy.1,
        (mem_normalizer_iff.mp (hAθ hk) y).mp hy.2⟩
    have hcomm := vanishing_centralizes_invariant_two_subgroups hp hvan hAe hAcard hbA hb1
      (U := Q ⊓ θ) inf_le_right (IsPGroup.to_le hQ2 inf_le_left) hU
    have hq' : (q : G) ∈ Q ⊓ θ := ⟨hq.1, ⟨q, hq.2, rfl⟩⟩
    have hq'' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hq'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hq'' (x : G) hx)

end Witness


end NormalPCoreWitness

theorem section_ten_five_normal_p_core_two_group_witness_frontier_of
    :
    SectionTenFiveNormalPCoreTwoGroupWitnessFrontier := by
  intro G _ _ p A hS a haA ha1
  have hp := sectionTenSetup_prime hS
  have hp3 := sectionTenSetup_three_lt hS
  obtain ⟨b, hbA, hbna, Q, hQ2, hAQ, hQC, hQA, hQne, hker⟩ :=
    NormalPCoreWitness.exists_line_witness hp (by omega) hS.2.2.2.1 hS.2.2.2.2.2.2.1
      hS.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.2.2.2.1 haA ha1
  refine ⟨b, hbA, hbna, Q, hQ2, hAQ, hQC, hQA, hQne, ?_⟩
  exact NormalPCoreWitness.final_conjunct hp hp3 (sectionTenSetup_vanishing hS)
    (sectionTenSetup_evenRank_eq hS).le hS.2.2.2.2.2.2.1 hS.2.2.2.2.2.2.2.1 hbA
    (fun h => hbna (h ▸ Subgroup.one_mem _)) hQ2 hAQ hQC hQA hker

theorem section_ten_five_normal_p_core_two_group_witness_frontier :
    SectionTenFiveNormalPCoreTwoGroupWitnessFrontier :=
  section_ten_five_normal_p_core_two_group_witness_frontier_of

end CFSG.RankThree.PartOne
