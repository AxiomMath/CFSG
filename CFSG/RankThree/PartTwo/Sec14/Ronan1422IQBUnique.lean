module

public import CFSG.RankThree.PartTwo.Sec14.Ronan1422IQBTools
public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec15.HypR
import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
import CFSG.RankThree.PartTwo.KFacts.K71Coprime
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_inSubgroup_theta {H : Subgroup G} {g t : G} (hg : g ∈ H)
    (ht : t ∈ inSubgroup (aschbacherSolvableCore 3) H) :
    g * t * g⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) H := by
  have hθc := (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).2.1
  have : (aschbacherSolvableCore 3 ↥H).Normal := @Subgroup.normal_of_characteristic _ _ _ hθc
  obtain ⟨t', ht', rfl⟩ := ht
  exact ⟨⟨g, hg⟩ * t' * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance t' ht' _, rfl⟩

theorem commutator_mem_theta_of_ne_in {H K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ thetaComponentsIn H)
    (h₂ : K₂ ∈ thetaComponentsIn H) (hne : K₁ ≠ K₂) {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₂) :
    x * y * x⁻¹ * y⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) H := by
  obtain ⟨K₁', hK₁', rfl⟩ := h₁
  obtain ⟨K₂', hK₂', rfl⟩ := h₂
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hne' : K₁' ≠ K₂' := fun h => hne (h ▸ rfl)
  have hJne : K₁'.map π ≠ K₂'.map π := fun h => hne' (hbij.injOn hK₁' hK₂' h)
  have hcomm := (LocalCores.distinct_components_commute
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁')
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hK₂')).resolve_left hJne
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have h1 : π y' * π x' = π x' * π y' :=
    Subgroup.mem_centralizer_iff.mp (hcent (Subgroup.mem_map_of_mem π hx')) _
      (Subgroup.mem_map_of_mem π hy')
  have h2 : π (x' * y' * x'⁻¹ * y'⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
    group
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  exact ⟨_, h2, rfl⟩

theorem le_normalizer_of_ne_in {H K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ thetaComponentsIn H)
    (h₂ : K₂ ∈ thetaComponentsIn H) (hne : K₁ ≠ K₂) :
    K₂ ≤ Subgroup.normalizer (K₁ : Set G) := by
  obtain ⟨K₁', hK₁', rfl⟩ := h₁
  obtain ⟨K₂', hK₂', rfl⟩ := h₂
  have hne' : K₁' ≠ K₂' := fun h => hne (h ▸ rfl)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 H) with hπ
  have hle : K₂' ≤ Subgroup.normalizer (K₁' : Set H) := by
    intro y hy
    have hyc : π y ∈ Subgroup.centralizer
        ((K₁'.map π : Subgroup (H ⧸ aschbacherSolvableCore 3 H)) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have h1 : π (x * y * x⁻¹ * y⁻¹) = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have h := commutator_mem_theta_of_ne_in ⟨K₁', hK₁', rfl⟩ ⟨K₂', hK₂', rfl⟩ hne
          (Subgroup.mem_map_of_mem H.subtype hx) (Subgroup.mem_map_of_mem H.subtype hy)
        obtain ⟨z, hz, hzeq⟩ := h
        have : z = x * y * x⁻¹ * y⁻¹ := Subtype.ext (by simpa using hzeq)
        rwa [← this]
      simp only [map_mul, map_inv] at h1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hyN : y ∈ Subgroup.normalizer (((K₁'.map π).comap π : Subgroup H) : Set H) :=
      Subgroup.le_normalizer_comap π (Subgroup.centralizer_le_normalizer _ hyc)
    have h :=
      CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _ hyN
    rwa [hπ, perfectResidual_comap_map_of_mem_thetaComponents Nat.prime_three hK₁'] at h
  exact (Subgroup.map_mono hle).trans (Subgroup.le_normalizer_map _)

theorem exists_noncentral_three {M J : Subgroup G} (hJ : J ∈ thetaComponentsIn M)
    (h3 : 3 ∣ Nat.card J) :
    ∃ x : ↥J ⧸ aschbacherSolvableCore 3 ↥J, orderOf x = 3 ∧
      x ∉ Subgroup.center (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
  have hq := Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 hJ
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥J) :=
    (solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three).2.2.1
  have hcard : Nat.card J = Nat.card (aschbacherSolvableCore 3 ↥J) *
      Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
    rw [mul_comm]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3' : 3 ∣ Nat.card (↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
    rw [hcard] at h3
    exact Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3) h3
  exact HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
    (open_isQuasisimple_of hq) Nat.prime_three (by norm_num) h3'

theorem exists_invariant_sylow_of_three {A Q : Subgroup G} (hA : IsPGroup 3 A)
    (hQ : ¬ 3 ∣ Nat.card Q) (hAQ : A ≤ Subgroup.normalizer (Q : Set G)) {r : ℕ} (hr : r.Prime) :
    ∃ R : Subgroup G, R ≤ Q ∧ IsPGroup r R ∧ A ≤ Subgroup.normalizer (R : Set G) ∧
      Nat.card R = r ^ (Nat.card Q).factorization r := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, hS⟩ := CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime 3 r
    hA hQ (Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ))
  refine ⟨(S : Subgroup Q).map Q.subtype, Subgroup.map_subtype_le _, S.isPGroup'.map _,
    fun a ha => ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    conv_rhs => rw [← hS ⟨a, ha⟩]
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, Sylow.card_eq_multiplicity]

theorem mk_eq_of_mem_inSubgroup_theta {J : Subgroup G} {a b : G} (ha : a ∈ J) (hb : b ∈ J)
    (h : a⁻¹ * b ∈ inSubgroup (aschbacherSolvableCore 3) J) :
    ((⟨a, ha⟩ : ↥J) : ↥J ⧸ aschbacherSolvableCore 3 ↥J) =
      ((⟨b, hb⟩ : ↥J) : ↥J ⧸ aschbacherSolvableCore 3 ↥J) := by
  rw [QuotientGroup.eq]
  obtain ⟨t, ht, hteq⟩ := h
  have : t = (⟨a, ha⟩ : ↥J)⁻¹ * ⟨b, hb⟩ := Subtype.ext (by simpa using hteq)
  rwa [← this]

theorem eq_of_mem_thetaComponentsIn_of_three_dvd {B : Subgroup G}
    (hBe : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hEF : ∀ E ∈ partTwoE G, E ∈ partTwoF G) {J₁ J₂ : Subgroup G}
    (h₁ : J₁ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (h₂ : J₂ ∈ thetaComponentsIn (Subgroup.centralizer (B : Set G)))
    (h3₁ : 3 ∣ Nat.card J₁) (h3₂ : 3 ∣ Nat.card J₂) : J₁ = J₂ := by
  by_contra hne
  have h3 : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨h3⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer (B : Set G) with hCdef
  have hJ₁C : J₁ ≤ C := le_of_mem_thetaComponentsIn h₁
  have hJ₂C : J₂ ≤ C := le_of_mem_thetaComponentsIn h₂
  have hBc : ∀ b ∈ B, ∀ g ∈ C, b * g = g * b := fun b hb g hg =>
    Subgroup.mem_centralizer_iff.mp hg b hb
  have hN : J₁ ≤ Subgroup.normalizer (J₂ : Set G) := le_normalizer_of_ne_in h₂ h₁ (Ne.symm hne)
  obtain ⟨xb, hxb3, hxbZ⟩ := exists_noncentral_three h₁ h3₁
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective xb
  have hθ₁ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥J₁) :=
    (solvable_prime_complement_core_characterization (H := ↥J₁) h3).2.2.1
  obtain ⟨k, hk3, hkx⟩ := pow_orderOf_three_of_quotient hθ₁ hxb3
  set x : G := ((x₀ ^ k : ↥J₁) : G) with hxdef
  have hxJ₁ : x ∈ J₁ := (x₀ ^ k).2
  have hx3 : x ^ 3 = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, ← hk3, pow_orderOf_eq_one, Subgroup.coe_one]
  have hxB : x ∉ B := by
    intro hxB
    apply hxbZ
    rw [← hkx, Subgroup.mem_center_iff]
    intro z
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hBc x hxB l (hJ₁C l.2)).symm
  have hxC : ∀ b ∈ B, b * x = x * b := fun b hb => hBc b hb x (hJ₁C hxJ₁)
  set E := B ⊔ Subgroup.zpowers x with hEdef
  obtain ⟨-, hEcard⟩ := CFSG.RankThree.PartTwo.sup_zpowers_card (p := 3) hBe.1 hxB hx3 hxC
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := Sec15.isElemAbelian_sup_zpowers hBe hx3 hxC
  have hE27 : Nat.card E = 27 := by rw [hEcard, hB9]
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  have hBθ : B ≤ Sec4.thetaQuotCentralizer J₂ := by
    intro b hb
    have hbC : b ∈ Subgroup.centralizer (J₂ : Set G) := Subgroup.mem_centralizer_iff.mpr
      fun l hl => (hBc b hb l (hJ₂C hl)).symm
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr
      ⟨Subgroup.centralizer_le_normalizer _ hbC, fun l hl => ?_⟩
    have : b * l * b⁻¹ = l := by rw [hBc b hb l (hJ₂C hl), mul_inv_cancel_right]
    rw [this, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hxθ : x ∈ Sec4.thetaQuotCentralizer J₂ := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hN hxJ₁, fun l hl => ?_⟩
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsIn h₂]
    refine ⟨J₂.mul_mem (J₂.inv_mem hl)
      ((Subgroup.mem_normalizer_iff.mp (hN hxJ₁) l).mp hl), ?_⟩
    have hc := commutator_mem_theta_of_ne_in h₁ h₂ hne hxJ₁ hl
    have h' := conj_mem_inSubgroup_theta (H := C) (C.inv_mem (hJ₂C hl)) hc
    have heq : l⁻¹ * (x * l * x⁻¹ * l⁻¹) * l⁻¹⁻¹ = l⁻¹ * (x * l * x⁻¹) := by group
    rwa [heq] at h'
  have hEθ : E ≤ Sec4.thetaQuotCentralizer J₂ := sup_le hBθ (Subgroup.zpowers_le.mpr hxθ)
  have hEN : E ≤ Subgroup.normalizer (J₂ : Set G) := fun e he =>
    (Sec6.mem_thetaQuotCentralizer_iff.mp (hEθ he)).1
  have hEtriv : ∀ e ∈ E, ∀ l ∈ J₂, l⁻¹ * (e * l * e⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) J₂ :=
    fun e he => (Sec6.mem_thetaQuotCentralizer_iff.mp (hEθ he)).2
  set θ₂ := aschbacherSolvableCore 3 ↥J₂ with hθ₂
  have hθ₂3 : ¬ 3 ∣ Nat.card θ₂ :=
    (solvable_prime_complement_core_characterization (H := ↥J₂) h3).2.2.1
  have hq₂ := Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423 h₂
  have h2 : 2 ∣ Nat.card (↥J₂ ⧸ θ₂) := by
    by_contra hodd
    have hodd' : Odd (Nat.card (↥J₂ ⧸ θ₂)) := Nat.odd_iff.mpr (by omega)
    have hsol := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have : Nontrivial (↥J₂ ⧸ θ₂) := CFSG.LocalCores.isQuasisimple_nontrivial hq₂
    have : Group.IsPerfect (↥J₂ ⧸ θ₂) := hq₂.1
    exact Group.IsPerfect.not_isSolvable _ hsol
  obtain ⟨T⟩ : Nonempty (Sylow 2 (↥J₂ ⧸ θ₂)) := inferInstance
  have hT2 : 2 ∣ Nat.card (T : Subgroup (↥J₂ ⧸ θ₂)) := by
    rw [Sylow.card_eq_multiplicity]
    exact dvd_pow_self 2 (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2
      |>.ne')
  set Y' := (T : Subgroup (↥J₂ ⧸ θ₂)).comap (QuotientGroup.mk' θ₂) with hY'
  set Y := Y'.map J₂.subtype with hYdef
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro hd
    rw [hYdef, Subgroup.card_map_of_injective J₂.subtype_injective] at hd
    obtain ⟨⟨y, hy⟩, hyo⟩ := exists_prime_orderOf_dvd_card' 3 hd
    rw [Subgroup.orderOf_mk] at hyo
    have himg : orderOf (QuotientGroup.mk' θ₂ y) = 1 := by
      have hd3 : orderOf (QuotientGroup.mk' θ₂ y) ∣ 3 := by
        have := orderOf_map_dvd (QuotientGroup.mk' θ₂) y
        rwa [hyo] at this
      have hdT : ∃ n : ℕ, orderOf (QuotientGroup.mk' θ₂ y) ∣ 2 ^ n := by
        obtain ⟨n, hn⟩ := T.isPGroup' ⟨QuotientGroup.mk' θ₂ y, hy⟩
        refine ⟨n, orderOf_dvd_of_pow_eq_one ?_⟩
        have := congrArg Subtype.val hn
        simpa using this
      obtain ⟨n, hdT⟩ := hdT
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdT
      rcases (Nat.dvd_prime h3).mp hd3 with h1 | h1
      · exact h1
      · rw [h1] at hi
        rcases i with _ | i
        · simp at hi
        · have : 2 ∣ 3 := hi ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)
          norm_num at this
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at himg
    have : orderOf (⟨y, himg⟩ : θ₂) = 3 := by rw [Subgroup.orderOf_mk, hyo]
    exact hθ₂3 (this ▸ orderOf_dvd_natCard _)
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    have key : ∀ e ∈ E, ∀ h ∈ Y, e * h * e⁻¹ ∈ Y := by
      rintro e he _ ⟨j, hj, rfl⟩
      have hjJ := j.2
      have he' : e * (j : G) * e⁻¹ ∈ J₂ :=
        (Subgroup.mem_normalizer_iff.mp (hEN he) j).mp hjJ
      refine ⟨⟨_, he'⟩, ?_, rfl⟩
      have hmk := mk_eq_of_mem_inSubgroup_theta hjJ he' (hEtriv e he j hjJ)
      change QuotientGroup.mk' θ₂ ⟨_, he'⟩ ∈ (T : Subgroup _)
      rw [QuotientGroup.mk'_apply, ← hmk]
      exact hj
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨key e he h, fun hh => ?_⟩
    have := key e⁻¹ (E.inv_mem he) _ hh
    rwa [show e⁻¹ * (e * h * e⁻¹) * e⁻¹⁻¹ = h by group] at this
  obtain ⟨R, hRY, hR2, hER, hRcard⟩ := exists_invariant_sylow_of_three hE3 hY3 hEY Nat.prime_two
  have hY2 : 2 ∣ Nat.card Y := by
    rw [hYdef, Subgroup.card_map_of_injective J₂.subtype_injective]
    refine hT2.trans (Subgroup.card_dvd_of_surjective
      (f := ((QuotientGroup.mk' θ₂).comp Y'.subtype).codRestrict (T : Subgroup _)
        fun y => y.2) ?_)
    rintro ⟨t, ht⟩
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective θ₂ t
    exact ⟨⟨j, ht⟩, rfl⟩
  have hR1 : R ≠ ⊥ := by
    intro hR
    rw [hR, Subgroup.card_bot] at hRcard
    have hpos : 0 < (Nat.card Y).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' hY2
    have : 2 ≤ 2 ^ (Nat.card Y).factorization 2 :=
      le_self_pow₀ (by norm_num) hpos.ne'
    omega
  have hEmem : E ∈ partTwoE G := ⟨hEe, hE27, R, hR1, hR2, hER⟩
  have hEF' := hEF E hEmem
  obtain ⟨yb, hyb3, hybZ⟩ := exists_noncentral_three h₂ h3₂
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective yb
  set ρ : ↥E →* MulAut ↥J₂ := J₂.normalizerMonoidHom.comp (Subgroup.inclusion hEN) with hρ
  have hρapp : ∀ (g : ↥E) (j : ↥J₂), ((ρ g j : ↥J₂) : G) = (g : G) * j * (g : G)⁻¹ :=
    fun g j => rfl
  obtain ⟨y₁, hy₁, hy₁fix⟩ := KFacts.exists_fixed_of_coprime hE3 ρ θ₂ hθ₂3
    (fun g n hn => by
      have h := Sec4.map_aschbacherSolvableCore (ρ g)
      have : ρ g n ∈ (aschbacherSolvableCore 3 ↥J₂).map (ρ g : ↥J₂ →* ↥J₂) :=
        Subgroup.mem_map_of_mem _ hn
      rw [h] at this
      exact this)
    y₀ (fun g => by
      have := mk_eq_of_mem_inSubgroup_theta y₀.2 (ρ g y₀).2 (hEtriv g g.2 y₀ y₀.2)
      exact this.symm)
  have hy₁3 : orderOf ((y₁ : ↥J₂) : ↥J₂ ⧸ θ₂) = 3 := by rw [hy₁, hyb3]
  obtain ⟨k', hk'3, hk'y⟩ := pow_orderOf_three_of_quotient hθ₂3 hy₁3
  set y : G := ((y₁ ^ k' : ↥J₂) : G) with hydef
  have hy3 : y ^ 3 = 1 := by
    rw [hydef, ← Subgroup.coe_pow, ← hk'3, pow_orderOf_eq_one, Subgroup.coe_one]
  have hyE : E ≤ Subgroup.centralizer ({y} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix : ρ ⟨g, hg⟩ (y₁ ^ k') = y₁ ^ k' := by rw [map_pow, hy₁fix]
    have h' : g * y * g⁻¹ = y := congrArg Subtype.val hfix
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h']
  have hyEmem : y ∈ E := Sec15.mem_of_mem_partTwoF hEF' hy3 hyE
  apply hybZ
  rw [← hy₁, ← hk'y, Subgroup.mem_center_iff]
  intro z
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  have hyl := hEtriv y hyEmem l l.2
  have hyJ : y * (l : G) * y⁻¹ ∈ J₂ :=
    (Subgroup.mem_normalizer_iff.mp (hEN hyEmem) l).mp l.2
  have hmk := mk_eq_of_mem_inSubgroup_theta l.2 hyJ hyl
  have hyl' : (⟨y * (l : G) * y⁻¹, hyJ⟩ : ↥J₂) = (y₁ ^ k') * l * (y₁ ^ k')⁻¹ :=
    Subtype.ext rfl
  rw [hyl'] at hmk
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  have : ((l * (y₁ ^ k') : ↥J₂) : ↥J₂ ⧸ θ₂) = ((y₁ ^ k' * l : ↥J₂) : ↥J₂ ⧸ θ₂) := by
    have h1 : ((y₁ ^ k' * l : ↥J₂) : ↥J₂ ⧸ θ₂) =
        ((y₁ ^ k' * l * (y₁ ^ k')⁻¹ : ↥J₂) : ↥J₂ ⧸ θ₂) * ((y₁ ^ k' : ↥J₂) : ↥J₂ ⧸ θ₂) := by
      rw [← QuotientGroup.mk_mul, inv_mul_cancel_right]
    rw [h1, ← hmk, ← QuotientGroup.mk_mul]
  exact this

end CFSG.RankThree.PartTwo.Sec14.Ronan1422IQB
