module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSCompA
public import CFSG.Permutation.FiveTransitive.CharacteristicAutomorphism
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.RankThree.PartTwo.Sec14.Item147

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14
open CFSG.FiveTransitive.CharacteristicAutomorphism (quotient quotient_apply_mk)
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y]

@[expose] noncomputable def thetaAct {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y)) :
    ↥B →* MulAut (↥W ⧸ aschbacherSolvableCore 3 ↥W) :=
  haveI := theta_characteristic ↥W
  (quotient (aschbacherSolvableCore 3 ↥W)).comp (conjAct hBW)

theorem thetaAct_mk {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y)) (b : ↥B)
    (w : ↥W) : thetaAct hBW b (w : ↥W ⧸ aschbacherSolvableCore 3 ↥W) =
      ((conjAct hBW b w : ↥W) : ↥W ⧸ aschbacherSolvableCore 3 ↥W) := by
  haveI := theta_characteristic ↥W
  exact quotient_apply_mk (aschbacherSolvableCore 3 ↥W) (conjAct hBW b) w

theorem three_dvd_card_of_isComponent {G : Type*} [Group G] [Finite G]
    (hcore : CFSG.pPrimeCore 3 G = ⊥) {J : Subgroup G} (hJ : IsComponent J) : 3 ∣ Nat.card J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra h3
  have hcop : Nat.Coprime 3 (Nat.card J) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hle := CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hJ.2 hcop
  rw [hcore, le_bot_iff] at hle
  have : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  subst hle
  obtain ⟨x, hx⟩ := exists_ne (1 : (⊥ : Subgroup G))
  exact hx (Subsingleton.elim _ _)

theorem open_isQuasisimple {K : Type*} [Group K] (hK : IsQuasisimple K) :
    CFSG.Open.IsQuasisimple K :=
  ⟨hK.1.commutator_eq_top, hK.2.1⟩

theorem exists_not_commute_of_not_mem_center {G : Type*} [Group G] {J : Subgroup G} {x : J}
    (hx : x ∉ Subgroup.center J) : ∃ j ∈ J, (j : G) * x ≠ x * j := by
  by_contra h
  push Not at h
  apply hx
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (h g g.2)

theorem exists_E27_of_ne {G : Type} [Group G] [Finite G] {J : Subgroup G} (hJ : IsComponent J)
    (h3 : 3 ∣ Nat.card J) {α : MulAut G} (hα : α ^ 3 = 1) (hne : J.map α.toMonoidHom ≠ J) :
    ∃ E : Subgroup G, CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J₂ := J.map α.toMonoidHom with hJ₂
  set J₃ := J₂.map α.toMonoidHom with hJ₃
  have hα3 : ∀ g, α (α (α g)) = g := fun g => by
    have := congrArg (fun β : MulAut G => β g) hα
    simpa [pow_succ, MulAut.mul_apply] using this
  have hJ₂c : IsComponent J₂ := CFSG.LocalCores.isComponent_map_mulEquiv α hJ
  have hJ₃c : IsComponent J₃ := CFSG.LocalCores.isComponent_map_mulEquiv α hJ₂c
  have hmap3 : J₃.map α.toMonoidHom = J := by
    ext g
    constructor
    · rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      change α (α (α j)) ∈ J
      rw [hα3]
      exact hj
    · intro hg
      refine ⟨α (α g), ⟨α g, ⟨g, hg, rfl⟩, rfl⟩, ?_⟩
      exact hα3 g
  have hne31 : J₃ ≠ J := by
    intro h
    apply hne
    rw [← hmap3, h]
  have hne32 : J₃ ≠ J₂ := by
    intro h
    have e : J₃ = J := by
      have := hmap3
      rw [h] at this
      exact this
    exact hne (h.symm.trans e)
  have hcomm : ∀ {K₁ K₂ : Subgroup G}, IsComponent K₁ → IsComponent K₂ → K₁ ≠ K₂ →
      ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a := by
    intro K₁ K₂ h₁ h₂ hne a ha b hb
    rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | h
    · exact absurd h hne
    · have := Subgroup.commutator_mem_commutator ha hb
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this
  obtain ⟨x, hx3, hxZ⟩ := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
    (open_isQuasisimple hJ.1) Nat.prime_three (by norm_num) h3
  obtain ⟨j₀, hj₀, hj₀x⟩ := exists_not_commute_of_not_mem_center hxZ
  set a : G := (x : G) with ha
  set b : G := α a with hb
  set c : G := α b with hc
  have haJ : a ∈ J := x.2
  have hbJ : b ∈ J₂ := ⟨a, haJ, rfl⟩
  have hcJ : c ∈ J₃ := ⟨b, hbJ, rfl⟩
  have ha3 : orderOf a = 3 := by rw [ha, Subgroup.orderOf_coe]; exact hx3
  have hb3 : orderOf b = 3 := by
    rw [hb, MulEquiv.orderOf_eq α a]; exact ha3
  have hc3 : orderOf c = 3 := by
    rw [hc, MulEquiv.orderOf_eq α b]; exact hb3
  have hbnc : ∃ j ∈ J₂, j * b ≠ b * j :=
    ⟨α j₀, ⟨j₀, hj₀, rfl⟩, fun h => hj₀x (α.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcnc : ∃ j ∈ J₃, j * c ≠ c * j := by
    obtain ⟨j, hj, hjb⟩ := hbnc
    exact ⟨α j, ⟨j, hj, rfl⟩, fun h => hjb (α.injective (by rw [map_mul, map_mul]; exact h))⟩
  have h12 := hcomm hJ hJ₂c (Ne.symm hne)
  have h13 := hcomm hJ hJ₃c (Ne.symm hne31)
  have h23 := hcomm hJ₂c hJ₃c (Ne.symm hne32)
  have hab : a * b = b * a := h12 a haJ b hbJ
  have hac : a * c = c * a := h13 a haJ c hcJ
  have hbc : b * c = c * b := h23 b hbJ c hcJ
  set A₁ := Subgroup.zpowers a
  set A₂ := Subgroup.zpowers b
  set A₃ := Subgroup.zpowers c
  have hcen : ∀ {g h : G}, g * h = h * g →
      Subgroup.zpowers g ≤ Subgroup.centralizer ((Subgroup.zpowers h : Subgroup G) : Set G) := by
    intro g h hgh
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left hgh.symm n)).eq.symm ▸ (Commute.zpow_left hgh.symm n).eq
  have h12n : A₁ ≤ Subgroup.normalizer (A₂ : Set G) :=
    (hcen hab).trans (Subgroup.centralizer_le_normalizer _)
  have h123n : A₁ ⊔ A₂ ≤ Subgroup.normalizer (A₃ : Set G) :=
    sup_le ((hcen hac).trans (Subgroup.centralizer_le_normalizer _))
      ((hcen hbc).trans (Subgroup.centralizer_le_normalizer _))
  have hk1 : Nat.card A₁ = 3 := by rw [Nat.card_zpowers, ha3]
  have hk2 : Nat.card A₂ = 3 := by rw [Nat.card_zpowers, hb3]
  have hk3 : Nat.card A₃ = 3 := by rw [Nat.card_zpowers, hc3]
  have hJJ₂ : J ≤ Subgroup.centralizer (J₂ : Set G) := fun g hg =>
    Subgroup.mem_centralizer_iff.mpr fun h hh => (h12 g hg h hh).symm
  have hbA₁ : b ∉ A₁ := by
    intro hb1
    obtain ⟨j, hj, hjb⟩ := hbnc
    have hbJ' : b ∈ J := (Subgroup.zpowers_le.mpr haJ) hb1
    exact hjb (Subgroup.mem_centralizer_iff.mp (hJJ₂ hbJ') j hj)
  have hJJ₃ : J ⊔ J₂ ≤ Subgroup.centralizer (J₃ : Set G) := by
    refine sup_le (fun g hg => Subgroup.mem_centralizer_iff.mpr fun h hh => (h13 g hg h hh).symm)
      (fun g hg => Subgroup.mem_centralizer_iff.mpr fun h hh => (h23 g hg h hh).symm)
  have hcA₁₂ : c ∉ A₁ ⊔ A₂ := by
    intro hc12
    obtain ⟨j, hj, hjc⟩ := hcnc
    have hcJ' : c ∈ J ⊔ J₂ :=
      (sup_le_sup (Subgroup.zpowers_le.mpr haJ) (Subgroup.zpowers_le.mpr hbJ)) hc12
    exact hjc (Subgroup.mem_centralizer_iff.mp (hJJ₃ hcJ') j hj)
  have hcard12 : Nat.card (A₁ ⊔ A₂ : Subgroup G) = 9 := by
    have hdvd := card_sup_dvd_card_mul h12n
    rw [hk1, hk2] at hdvd
    have hlt : Nat.card A₁ < Nat.card (A₁ ⊔ A₂ : Subgroup G) := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hbA₁ ?_)
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
    rw [hk1] at hlt
    have : Nat.card (A₁ ⊔ A₂ : Subgroup G) ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  set E : Subgroup G := A₁ ⊔ A₂ ⊔ A₃ with hE
  have hcardE : Nat.card E = 27 := by
    have hdvd := card_sup_dvd_card_mul h123n
    rw [hcard12, hk3] at hdvd
    have hlt : Nat.card (A₁ ⊔ A₂ : Subgroup G) < Nat.card E := by
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_left fun h => hcA₁₂ ?_)
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    rw [hcard12] at hlt
    have : Nat.card E ∈ Nat.divisors 27 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hd : Nat.divisors 27 = {1, 3, 9, 27} := by decide
    rw [hd] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  have hEc : E ≤ Subgroup.centralizer (E : Set G) := by
    have hA : ∀ {g : G}, g = a ∨ g = b ∨ g = c → E ≤ Subgroup.centralizer ({g} : Set G) := by
      intro g hg
      have hga : g * a = a * g := by rcases hg with rfl | rfl | rfl <;> simp [hab, hac, hbc]
      have hgb : g * b = b * g := by rcases hg with rfl | rfl | rfl <;> simp [hab, hac, hbc]
      have hgc : g * c = c * g := by rcases hg with rfl | rfl | rfl <;> simp [hab, hac, hbc]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hga.symm)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgb.symm)
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hgc.symm)
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hA (Or.inl rfl) hh))
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hA (Or.inr (Or.inl rfl)) hh))
    · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
      intro h hh
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hA (Or.inr (Or.inr rfl)) hh))
  have hEexp : ∀ g ∈ E, g ^ 3 = 1 := by
    have hpow3 : ∀ {g : G}, orderOf g = 3 → g ^ 3 = 1 := fun hg => hg ▸ pow_orderOf_eq_one _
    let S : Subgroup G :=
      { carrier := {g | g ∈ E ∧ g ^ 3 = 1}
        one_mem' := ⟨E.one_mem, one_pow 3⟩
        mul_mem' := by
          rintro u v ⟨huE, hu⟩ ⟨hvE, hv⟩
          refine ⟨E.mul_mem huE hvE, ?_⟩
          have hcomm : Commute u v := Subgroup.mem_centralizer_iff.mp (hEc hvE) u huE
          rw [hcomm.mul_pow, hu, hv, one_mul]
        inv_mem' := by
          rintro u ⟨huE, hu⟩
          exact ⟨E.inv_mem huE, by rw [inv_pow, hu, inv_one]⟩ }
    have hES : E ≤ S := by
      have haE : a ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
      have hbE : b ∈ E := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
      have hcE : c ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
      refine sup_le (sup_le ?_ ?_) ?_
      · exact Subgroup.zpowers_le.mpr ⟨haE, hpow3 ha3⟩
      · exact Subgroup.zpowers_le.mpr ⟨hbE, hpow3 hb3⟩
      · exact Subgroup.zpowers_le.mpr ⟨hcE, hpow3 hc3⟩
    intro g hg
    exact (hES hg).2
  refine ⟨E, ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun g hg => hEexp g hg⟩, hcardE⟩
  exact Subgroup.mem_centralizer_iff.mp (hEc v.2) u u.2

theorem exists_E27_of_quot {H : Type*} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
    (hN3 : ¬ 3 ∣ Nat.card N) {E : Subgroup (H ⧸ N)} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) :
    ∃ S : Subgroup H, CFSG.Assembly.IsElemAbelian 3 S ∧ Nat.card S = 27 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' N with hmk
  set Et : Subgroup H := E.comap mk with hEt
  have hker : mk.ker ≤ Et := MonoidHom.ker_le_comap mk E
  have hmap : Et.map mk = E :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) E
  have hcard : Nat.card Et = 27 * Nat.card N := by
    have h := card_map_mul_card_ker_of_le' mk hker
    rw [hmap, QuotientGroup.ker_mk', hE27] at h
    exact h.symm
  obtain ⟨S₀⟩ : Nonempty (Sylow 3 Et) := inferInstance
  have hS₀ : Nat.card S₀ = 27 := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_mul (by norm_num)
      (Nat.card_pos (α := N)).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN3, add_zero,
      show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_three]
    norm_num
  set S : Subgroup H := (S₀ : Subgroup Et).map Et.subtype with hS
  have hScard : Nat.card S = 27 := by
    rw [hS, Subgroup.card_map_of_injective Et.subtype_injective]
    exact hS₀
  have hSp : IsPGroup 3 S := (S₀.isPGroup').map Et.subtype
  have hSE : ∀ x ∈ S, mk x ∈ E := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hSN : ∀ x ∈ S, x ∈ N → x = 1 := fun x hxS hxN => by
    have hNc : Nat.Coprime 3 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN3
    exact eq_one_of_mem_pGroup_of_coprime hSp hNc hxS hxN
  refine ⟨S, ⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, hScard⟩
  · have hcomm : mk ((u : H) * v) = mk ((v : H) * u) := by
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨mk u, hSE u u.2⟩ ⟨mk v, hSE v v.2⟩)
    have h1 : ((u : H) * v) * ((v : H) * u)⁻¹ ∈ N := by
      have := (QuotientGroup.eq_iff_div_mem (N := N)).mp hcomm
      rwa [div_eq_mul_inv] at this
    have h2 : ((u : H) * v) * ((v : H) * u)⁻¹ = 1 := hSN _ (S.mul_mem (S.mul_mem u.2 v.2)
      (S.inv_mem (S.mul_mem v.2 u.2))) h1
    exact mul_inv_eq_one.mp h2
  · have h1 : mk (x ^ 3) = 1 := by rw [map_pow]; exact hE.2 _ (hSE x hx)
    rw [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hSN _ (S.pow_mem hx 3) h1

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {J : Subgroup G} {g : G}
    (h : ∀ j ∈ J, g * j * g⁻¹ ∈ J) : g ∈ Subgroup.normalizer (J : Set G) := by
  have hle : J.map (MulAut.conj g).toMonoidHom ≤ J := by
    rintro _ ⟨j, hj, rfl⟩
    exact h j hj
  have heq : J.map (MulAut.conj g).toMonoidHom = J :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨j, hj, hjx⟩ := hx
  have : j = x := by
    have hjx' : g * j * g⁻¹ = g * x * g⁻¹ := hjx
    simpa using hjx'
  exact this ▸ hj

section Invariance

variable {W P : Subgroup Y}

theorem map_eq_of_noE27 (hP : CFSG.Assembly.IsElemAbelian 3 P)
    (hPW : P ≤ Subgroup.normalizer (W : Set Y))
    (ha : CFSG.pPrimeCore 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) = ⊥)
    (hb : ∀ E : Subgroup Y, E ≤ W → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E ≠ 27)
    {J : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W)} (hJ : IsComponent J) (p : ↥P) :
    J.map (thetaAct hPW p).toMonoidHom = J := by
  by_contra hne
  have h3 := three_dvd_card_of_isComponent ha hJ
  have hα : thetaAct hPW p ^ 3 = 1 := by
    rw [← map_pow]
    have : p ^ 3 = 1 := Subtype.ext (hP.2 p p.2)
    rw [this, map_one]
  obtain ⟨E, hE, hE27⟩ := exists_E27_of_ne hJ h3 hα hne
  haveI := theta_characteristic ↥W
  obtain ⟨S, hS, hS27⟩ := exists_E27_of_quot (aschbacherSolvableCore 3 ↥W) (theta_not_dvd _) hE hE27
  apply hb (S.map W.subtype) (Subgroup.map_subtype_le S)
    (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 W.subtype S hS)
  rw [Subgroup.card_map_of_injective W.subtype_injective]
  exact hS27

theorem le_normalizer_of_commutator {Q : Subgroup Y} (hPW : P ≤ Subgroup.normalizer (W : Set Y))
    (hQW : Q ≤ W) (hQP : Q = ⁅Q, P⁆)
    (hinv : ∀ J : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W), IsComponent J →
      ∀ p : ↥P, J.map (thetaAct hPW p).toMonoidHom = J)
    {J : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W)} (hJ : IsComponent J) :
    (Q.subgroupOf W).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W)) ≤
      Subgroup.normalizer (J : Set (↥W ⧸ aschbacherSolvableCore 3 ↥W)) := by
  classical
  set Ws := ↥W ⧸ aschbacherSolvableCore 3 ↥W
  set mk := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W) with hmk
  set M : Subgroup ↥W := (Subgroup.normalizer (J : Set Ws)).comap mk with hM
  have hgen : ∀ q ∈ Q, ∀ p ∈ P, ∃ hw : ⁅q, p⁆ ∈ W, (⟨⁅q, p⁆, hw⟩ : ↥W) ∈ M := by
    intro q hq p hp
    have hqW := hQW hq
    have hw : ⁅q, p⁆ ∈ W := by
      rw [commutatorElement_def]
      have : p * q⁻¹ * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hPW hp) q⁻¹).mp (W.inv_mem hqW)
      have e : q * p * q⁻¹ * p⁻¹ = q * (p * q⁻¹ * p⁻¹) := by group
      rw [e]
      exact W.mul_mem hqW this
    refine ⟨hw, ?_⟩
    set σ := thetaAct hPW ⟨p, hp⟩ with hσ
    set qs : Ws := ((⟨q, hqW⟩ : ↥W) : Ws) with hqs
    have hmkw : ((⟨⁅q, p⁆, hw⟩ : ↥W) : Ws) = qs * (σ qs)⁻¹ := by
      have e : (⟨⁅q, p⁆, hw⟩ : ↥W) = ⟨q, hqW⟩ * (conjAct hPW ⟨p, hp⟩ ⟨q, hqW⟩)⁻¹ := by
        apply Subtype.ext
        change ⁅q, p⁆ = q * ((p : Y) * q * (p : Y)⁻¹)⁻¹
        rw [commutatorElement_def]
        group
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← thetaAct_mk]
    show ((⟨⁅q, p⁆, hw⟩ : ↥W) : Ws) ∈ Subgroup.normalizer (J : Set Ws)
    rw [hmkw]
    refine mem_normalizer_of_conj_le fun j hj => ?_
    set J' := J.map (MulAut.conj qs⁻¹).toMonoidHom with hJ'
    have hJ'c : IsComponent J' := CFSG.LocalCores.isComponent_map_mulEquiv _ hJ
    have hσJ := hinv J hJ ⟨p, hp⟩
    have hσJ' := hinv J' hJ'c ⟨p, hp⟩
    have hj' : j ∈ J.map σ.toMonoidHom := by rw [hσJ]; exact hj
    obtain ⟨j₀, hj₀, rfl⟩ := hj'
    have hmem : qs⁻¹ * j₀ * qs ∈ J' := ⟨j₀, hj₀, by simp [MulAut.conj_apply]⟩
    have hmem' : σ (qs⁻¹ * j₀ * qs) ∈ J' := by rw [← hσJ']; exact ⟨_, hmem, rfl⟩
    obtain ⟨j₁, hj₁, hj₁e⟩ := hmem'
    have e1 : σ (qs⁻¹ * j₀ * qs) = qs⁻¹ * j₁ * qs := by
      rw [← hj₁e]
      simp [MulAut.conj_apply]
    have e2 : qs * (σ qs)⁻¹ * σ j₀ * (qs * (σ qs)⁻¹)⁻¹ = j₁ := by
      have : σ (qs⁻¹ * j₀ * qs) = (σ qs)⁻¹ * σ j₀ * σ qs := by
        rw [map_mul, map_mul, map_inv]
      rw [this] at e1
      calc qs * (σ qs)⁻¹ * σ j₀ * (qs * (σ qs)⁻¹)⁻¹ = qs * ((σ qs)⁻¹ * σ j₀ * σ qs) * qs⁻¹ := by
            group
        _ = qs * (qs⁻¹ * j₁ * qs) * qs⁻¹ := by rw [e1]
        _ = j₁ := by group
    change qs * (σ qs)⁻¹ * σ j₀ * (qs * (σ qs)⁻¹)⁻¹ ∈ J
    rw [e2]
    exact hj₁
  have hQM : Q ≤ M.map W.subtype := by
    rw [hQP, Subgroup.commutator_def, Subgroup.closure_le]
    rintro _ ⟨q, hq, p, hp, rfl⟩
    obtain ⟨hw, hm⟩ := hgen q hq p hp
    exact ⟨_, hm, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hQM (Subgroup.mem_subgroupOf.mp hx)
  have : y = x := Subtype.ext hyx
  rw [← this]
  exact hy

end Invariance

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
