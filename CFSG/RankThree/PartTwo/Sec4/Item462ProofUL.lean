module

public import CFSG.RankThree.PartTwo.Sec4.Item462ProofTools
import CFSG.RankThree.PartTwo.Sec4.Item422Proof
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.Walter.W67.JR.OutPSL
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Inner

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_mul_of_commute (g u w : G) (hw : g * w = w * g) :
    ⁅g, u * w⁆ = ⁅g, u⁆ := by
  have h1 : g⁻¹ * w = w * g⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hw, mul_assoc, mul_inv_cancel, mul_one]
  rw [commutatorElement_def, commutatorElement_def]
  have h2 : g * (u * w) * g⁻¹ * (u * w)⁻¹ = g * u * (w * g⁻¹) * w⁻¹ * u⁻¹ := by group
  rw [h2, ← h1]
  group

omit [Finite G] in
theorem mem_of_mul_pow_three {L N : Subgroup G} (hN : N ≤ Subgroup.normalizer (L : Set G))
    (hN3 : ¬ 3 ∣ Nat.card N) {l t : G} (hl : l ∈ L) (ht : t ∈ N) (h3 : (l * t) ^ 3 = 1) :
    t ∈ L := by
  have htN := hN ht
  have ht2N := hN (N.pow_mem ht 2)
  have h1 : t * l * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htN l).mp hl
  have h2 : t ^ 2 * l * (t ^ 2)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht2N l).mp hl
  have h3' : l * t * (l * t) * (l * t) = 1 := by rw [← pow_three', h3]
  have key : t ^ 3 =
      (l * (t * l * t⁻¹) * (t ^ 2 * l * (t ^ 2)⁻¹))⁻¹ * (l * t * (l * t) * (l * t)) := by group
  have ht3 : t ^ 3 ∈ L := by
    rw [key, h3', mul_one]
    exact L.inv_mem (L.mul_mem (L.mul_mem hl h1) h2)
  have hcop : Nat.Coprime 3 (orderOf t) := by
    refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h => hN3 (h.trans ?_)
    rw [← Subgroup.orderOf_mk t ht]
    exact orderOf_dvd_natCard _
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact L.pow_mem ht3 m

theorem mem_sup_zpowers_of_not_inducesOuterTheta {A L : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (hL : L ∈ thetaComponents 3 G) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) {x : G} (hxA : x ∈ A)
    (hx : ¬ InducesOuterTheta x L) : x ∈ L ⊔ Subgroup.zpowers a := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hxN := hAL hxA
  have hσ : thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) ∈
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* MulAut _).range := by
    by_contra h
    exact hx ⟨hxN, h⟩
  obtain ⟨q₀, hq₀⟩ := hσ
  obtain ⟨l₀, rfl⟩ := QuotientGroup.mk_surjective q₀
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρdef
  obtain ⟨-, hK, ⟨η, hη⟩, -, -, -, hNL, -, -, -, hAiff⟩ :=
    theta_component_quotient_structure Nat.prime_three hL
  have hZK : Subgroup.center (L.map ρ) = ⊥ := by
    have h := Subgroup.map_center_eq η
    rw [hZ, Subgroup.map_bot] at h
    exact h.symm
  have hKC : ∀ w ∈ L.map ρ, w ∈ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set _) →
      w = 1 := by
    intro w hwK hwC
    have hmem : (⟨w, hwK⟩ : L.map ρ) ∈ Subgroup.center (L.map ρ) :=
      Subgroup.mem_center_iff.mpr fun k =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hwC k k.2)
    rw [hZK, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  set c := (ρ l₀)⁻¹ * ρ x with hc
  have hcK : c ∈ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := DFunLike.congr_fun hq₀ ((⟨l, hl⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)
    rw [MulAut.conj_apply, thetaQuotMulAut_mk] at h1
    have h2 := congrArg (fun q => ((η q : L.map ρ) : G ⧸ N)) h1
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hη, hη, hη, normalizerMonoidHom_apply_coe] at h2
    change ρ (l₀ : G) * ρ l * (ρ (l₀ : G))⁻¹ = ρ (x * l * x⁻¹) at h2
    rw [map_mul, map_mul, map_inv] at h2
    change ρ l * ((ρ l₀)⁻¹ * ρ x) = (ρ l₀)⁻¹ * ρ x * ρ l
    calc ρ l * ((ρ l₀)⁻¹ * ρ x) = (ρ l₀)⁻¹ * (ρ l₀ * ρ l * (ρ l₀)⁻¹) * ρ x := by group
      _ = (ρ l₀)⁻¹ * (ρ x * ρ l * (ρ x)⁻¹) * ρ x := by rw [h2]
      _ = (ρ l₀)⁻¹ * ρ x * ρ l := by group
  have hl₀K : ρ l₀ ∈ L.map ρ := Subgroup.mem_map_of_mem ρ l₀.2
  have hcomm : ρ l₀ * c = c * ρ l₀ := Subgroup.mem_centralizer_iff.mp hcK _ hl₀K
  have hxc : ρ x = ρ l₀ * c := by rw [hc, mul_inv_cancel_left]
  have hx3 : x ^ 3 = 1 := hAe.2 x hxA
  have hc3 : c ^ 3 = 1 := by
    have h := congrArg ρ hx3
    rw [map_pow, hxc, map_one, (Commute.mul_pow hcomm 3)] at h
    have hw : (ρ l₀ : G ⧸ N) ^ 3 = (c ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hwK : (ρ l₀) ^ 3 ∈ L.map ρ := (L.map ρ).pow_mem hl₀K 3
    have hwC : (ρ l₀) ^ 3 ∈ Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set _) := by
      rw [hw]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hcK 3)
    have h1 := hKC _ hwK hwC
    rw [h1, one_mul] at h
    exact h
  have hAK := (hAiff A).mp hAL
  have hcA : c ∈ Subgroup.centralizer ((A.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have hyK := hAK (Subgroup.mem_map_of_mem ρ hy)
    have hyx : ρ y * ρ x = ρ x * ρ y := by
      rw [← map_mul, ← map_mul]
      exact congrArg ρ (congrArg Subtype.val (hAe.1.is_comm.comm ⟨y, hy⟩ ⟨x, hxA⟩))
    have hk' : ρ y * ρ l₀ * (ρ y)⁻¹ ∈ L.map ρ := (Subgroup.mem_normalizer_iff.mp hyK _).mp hl₀K
    have hc' : ρ y * c * (ρ y)⁻¹ ∈
        Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk2 : (ρ y)⁻¹ * k * (ρ y)⁻¹⁻¹ ∈ L.map ρ :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyK) k).mp hk
      have h := Subgroup.mem_centralizer_iff.mp hcK _ hk2
      calc k * (ρ y * c * (ρ y)⁻¹) = ρ y * ((ρ y)⁻¹ * k * (ρ y)⁻¹⁻¹ * c) * (ρ y)⁻¹ := by group
        _ = ρ y * (c * ((ρ y)⁻¹ * k * (ρ y)⁻¹⁻¹)) * (ρ y)⁻¹ := by rw [h]
        _ = ρ y * c * (ρ y)⁻¹ * k := by group
    have hw : (ρ l₀)⁻¹ * (ρ y * ρ l₀ * (ρ y)⁻¹) = c * (ρ y * c * (ρ y)⁻¹)⁻¹ := by
      have h1 : ρ y * (ρ l₀ * c) * (ρ y)⁻¹ = ρ l₀ * c := by
        rw [← hxc, hyx, mul_inv_cancel_right]
      calc (ρ l₀)⁻¹ * (ρ y * ρ l₀ * (ρ y)⁻¹)
          = (ρ l₀)⁻¹ * (ρ y * (ρ l₀ * c) * (ρ y)⁻¹) * (ρ y * c * (ρ y)⁻¹)⁻¹ := by group
        _ = c * (ρ y * c * (ρ y)⁻¹)⁻¹ := by rw [h1]; group
    have hwK : (ρ l₀)⁻¹ * (ρ y * ρ l₀ * (ρ y)⁻¹) ∈ L.map ρ :=
      (L.map ρ).mul_mem ((L.map ρ).inv_mem hl₀K) hk'
    have hwC : (ρ l₀)⁻¹ * (ρ y * ρ l₀ * (ρ y)⁻¹) ∈
        Subgroup.centralizer ((L.map ρ : Subgroup (G ⧸ N)) : Set _) := by
      rw [hw]
      exact Subgroup.mul_mem _ hcK (Subgroup.inv_mem _ hc')
    have h1 := hKC _ hwK hwC
    rw [hw, mul_inv_eq_one] at h1
    calc ρ y * c = ρ y * c * (ρ y)⁻¹ * ρ y := by group
      _ = c * ρ y := by rw [← h1]
  obtain ⟨z, hzA, hzc⟩ := Item422Proof.mem_map_of_maximal hmax N
    three_not_dvd_card_aschbacherSolvableCore hc3 hcA
  have hzC : z ∈ thetaQuotCentralizer L := by
    rw [mem_thetaQuotCentralizer_iff_mk hL]
    change ρ z ∈ _
    rw [hzc]
    exact hcK
  have hzZ : z ∈ Subgroup.zpowers a := (hCA z hzA).mp hzC
  set t := (l₀ : G)⁻¹ * (x * z⁻¹) with ht
  have htN : t ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    change ρ t = 1
    rw [ht, map_mul, map_mul, map_inv, map_inv]
    change (ρ l₀)⁻¹ * (ρ x * (ρ z)⁻¹) = 1
    rw [hzc, hxc, hc]
    group
  have hxz3 : ((l₀ : G) * t) ^ 3 = 1 := by
    rw [ht, mul_inv_cancel_left]
    exact hAe.2 _ (A.mul_mem hxA (A.inv_mem hzA))
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := G)
    Nat.prime_three
  have htL : t ∈ L := mem_of_mul_pow_three hNL hN3 l₀.2 htN hxz3
  have hx' : x = ((l₀ : G) * t) * z := by rw [ht]; group
  rw [hx']
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.mul_mem l₀.2 htL))
    (Subgroup.mem_sup_right hzZ)

theorem le_of_forall_exists_not_inducesOuterTheta {A L U : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (haZ : a ∈ Subgroup.center G) (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUN : U ≤ Subgroup.normalizer (L : Set G))
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) (hUA : ⁅U, A⁆ = U)
    (hinner : ∀ x ∈ A, ∃ y ∈ A, ¬ InducesOuterTheta y L ∧ ∀ u ∈ U, ⁅u, x⁆ = ⁅u, y⁆) :
    U ≤ L := by
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  rw [← hUA, Subgroup.commutator_le]
  intro u hu x hx
  obtain ⟨y, hyA, hy, hyu⟩ := hinner x hx
  rw [hyu u hu]
  have hyLa := mem_sup_zpowers_of_not_inducesOuterTheta hmax hL hAL hCA hZ hyA hy
  obtain ⟨l, hl, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hyLa
  rw [commutatorElement_mul_of_commute u l w
    (Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr haZ) hw) u), commutatorElement_def]
  exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUN hu) l).mp hl) (L.inv_mem hl)

end Inner

theorem exists_zpow_mul_mem_inner {Q : Type*} [Group Q] [Finite Q] (hcyc : IsCyclic (Outer Q))
    {σ τ : MulAut Q} (hσ : σ ^ 3 = 1) (hτ : τ ^ 3 = 1) (hτo : τ ∉ inner Q) :
    ∃ k : ℤ, σ * (τ ^ k)⁻¹ ∈ inner Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut Q) := Finite.of_injective (fun σ : MulAut Q => (σ : Q → Q))
    (fun σ τ h => MulEquiv.ext (congrFun h))
  set s : Outer Q := (σ : Outer Q) with hs
  set t : Outer Q := (τ : Outer Q) with ht
  have ht1 : t ≠ 1 := fun h => hτo ((QuotientGroup.eq_one_iff τ).mp h)
  have ht3 : orderOf t = 3 :=
    orderOf_eq_prime (by rw [ht, ← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]) ht1
  have hs3 : s ^ 3 = 1 := by rw [hs, ← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one]
  have hsmem : s ∈ Subgroup.zpowers t := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hs3) with h1 | h3
    · rw [orderOf_eq_one_iff.mp h1]
      exact Subgroup.one_mem _
    · have heq : Subgroup.zpowers s = Subgroup.zpowers t :=
        IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, h3, ht3])
      rw [← heq]
      exact Subgroup.mem_zpowers s
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsmem
  refine ⟨k, ?_⟩
  have hk' : ((τ ^ k : MulAut Q) : Outer Q) = (σ : Outer Q) := by
    rw [QuotientGroup.mk_zpow]
    exact hk
  have := (QuotientGroup.eq_iff_div_mem).mp hk'.symm
  rwa [div_eq_mul_inv] at this

theorem center_eq_bot_of_isSimpleGroup {S : Type*} [Group S] (hS : IsSimpleGroup S)
    (hp : ¬ (Nat.card S).Prime) : Subgroup.center S = ⊥ := by
  obtain ⟨a, b, hab⟩ : ∃ a b : S, a * b ≠ b * a := by
    by_contra h
    push Not at h
    let _ : CommGroup S := { ‹Group S› with mul_comm := h }
    exact hp (CommGroup.is_simple_iff_prime_card.mp hS)
  rcases hS.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

section Groups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem thetaQuotMulAut_pow_three {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : x ^ 3 = 1) : thetaQuotMulAut L (compAction L ⟨x, hx⟩) ^ 3 = 1 := by
  rw [← map_pow, ← map_pow]
  have h : (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  rw [h, map_one, map_one]

theorem not_inducesOuterTheta_of_j2
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) {x : G}
    (hx3 : x ^ 3 = 1) : ¬ InducesOuterTheta x L := by
  rintro ⟨hx, hout⟩
  exact hout (KFacts.ks17J2AutThree_of_outer
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
    _ ⟨e⟩ _ (thetaQuotMulAut_pow_three hx hx3))

omit [Finite G] in
theorem center_eq_bot_of_j2
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ := by
  have hZ : Subgroup.center Blueprint.NativeSporadic.J2 = ⊥ :=
    center_eq_bot_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [CFSG.Sporadic.J2.card_J2]; norm_num)
  have h := Subgroup.map_center_eq e
  rw [hZ] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h

theorem not_inducesOuterTheta_of_m12
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
      ∀ x : G, x ^ 3 = 1 → ¬ InducesOuterTheta x L := by
  obtain ⟨-, hZ, hinn, -⟩ := KFacts.ks18M12 (L ⧸ aschbacherSolvableCore 3 L) ⟨e⟩
  refine ⟨hZ, fun x hx3 => ?_⟩
  rintro ⟨hx, hout⟩
  obtain ⟨y, hy⟩ := hinn _ ⟨1, by rw [pow_one]; exact thetaQuotMulAut_pow_three hx hx3⟩
  exact hout ⟨y, hy.symm⟩

omit [Finite G] in
theorem center_eq_bot_and_isCyclic_of_l27
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3)) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
      IsCyclic (Outer (L ⧸ aschbacherSolvableCore 3 L)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set e' := e.trans (projSLEquivPSL (GaloisField 3 3)) with he'
  refine ⟨?_, CFSG.Walter.W67.JROut.isCyclic_outer_of_equiv e' (by decide) (by decide)
    (by norm_num)⟩
  have h := Subgroup.map_center_eq e'
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot] at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ e'.injective).mp h

end Groups

theorem le_of_list
    {G : Type} [Group G] [Finite G] {A B U L : Subgroup G}
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) {a : G}
    (haZ : a ∈ Subgroup.center G) (hBA : B ≤ A) (hUB : U ≤ Subgroup.centralizer (B : Set G))
    (hUA : ⁅U, A⁆ = U) (hL : L ∈ thetaComponents 3 G)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hUN : U ≤ Subgroup.normalizer (L : Set G))
    (hCA : ∀ y ∈ A, y ∈ thetaQuotCentralizer L ↔ y ∈ Subgroup.zpowers a)
    (hlist : (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.J2) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.M12)) ∨
      (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃*
          CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 3 3)) ∧
        ∃ e ∈ B, InducesOuterTheta e L)) :
    U ≤ L := by
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  rcases hlist with (he | he) | ⟨he, f, hfB, hf⟩
  · obtain ⟨e⟩ := he
    exact le_of_forall_exists_not_inducesOuterTheta hmax haZ hL hAL hUN hCA
      (center_eq_bot_of_j2 e) hUA
      fun x hx => ⟨x, hx, not_inducesOuterTheta_of_j2 e (hAe.2 x hx), fun _ _ => rfl⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hZ, hinn⟩ := not_inducesOuterTheta_of_m12 (G := G) e
    exact le_of_forall_exists_not_inducesOuterTheta hmax haZ hL hAL hUN hCA hZ hUA
      fun x hx => ⟨x, hx, hinn x (hAe.2 x hx), fun _ _ => rfl⟩
  · obtain ⟨e⟩ := he
    obtain ⟨hZ, hcyc⟩ := center_eq_bot_and_isCyclic_of_l27 e
    refine le_of_forall_exists_not_inducesOuterTheta hmax haZ hL hAL hUN hCA hZ hUA
      fun x hx => ?_
    obtain ⟨hfN, hfo⟩ := hf
    have hfA := hBA hfB
    have hxN := hAL hx
    obtain ⟨k, hk⟩ := exists_zpow_mul_mem_inner hcyc
      (thetaQuotMulAut_pow_three hxN (hAe.2 x hx)) (thetaQuotMulAut_pow_three hfN (hAe.2 f hfA))
      hfo
    refine ⟨x * (f ^ k)⁻¹, A.mul_mem hx (A.inv_mem (A.zpow_mem hfA k)), ?_, fun u hu => ?_⟩
    · rintro ⟨hyN, hout⟩
      apply hout
      have heq : (⟨x * (f ^ k)⁻¹, hyN⟩ : Subgroup.normalizer (L : Set G)) =
          ⟨x, hxN⟩ * (⟨f, hfN⟩ ^ k)⁻¹ := Subtype.ext (by simp)
      rw [heq, map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow]
      exact hk
    · have hfu : u * f ^ k = f ^ k * u := by
        have h1 : u * f = f * u := (Subgroup.mem_centralizer_iff.mp (hUB hu) f hfB).symm
        exact (Commute.zpow_right h1 k).eq
      conv_lhs => rw [show x = x * (f ^ k)⁻¹ * f ^ k by group]
      exact commutatorElement_mul_of_commute u _ _ hfu

end CFSG.RankThree.PartTwo.Sec4.Item462Proof
