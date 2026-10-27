module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestNorm
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallSpLift
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperElt
import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGStdSubNormEltData (p : ℕ) {R : Type} [Group R] (A : Subgroup R) (a : R) : Prop :=
  ∃ D : Subgroup R, D ≤ Subgroup.centralizer ({a} : Set R) ∧
    (∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D) ∧ CFSG.IsQuasisimple D ∧
    ∃ U : Subgroup R, U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
      ((∀ b ∈ A, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers a) →
        ∃ t ∈ D, t ^ p = 1 ∧ (∀ s ∈ A, s * t = t * s) ∧ t ∈ Subgroup.normalizer (U : Set R) ∧
          ∃ j ∈ D, t * j ≠ j * t)

@[expose] def GGStdSubTwoTorusEltNorm (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∀ a ∈ A, a ≠ 1 → GGStdSubNormEltData p A a

namespace StdSubRest

section Lift

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem exists_lift_pow_eq_one_of_noTorsion [Finite L'] {p : ℕ} (hp : p.Prime)
    (hnp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) {e : R} (he : e ^ p = 1) {x : L'} (hx : ψ x = e) :
    ∃ k : ℕ, ψ (x ^ k) = e ∧ (x ^ k) ^ p = 1 := by
  have hxp : x ^ p ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hx, he]
  set m := orderOf (x ^ p) with hm
  have hmp : ¬ p ∣ m := by
    rintro ⟨c, hc⟩
    have hz : (x ^ p) ^ c ∈ ψ.ker := Subgroup.pow_mem _ hxp c
    have hzp : ((x ^ p) ^ c) ^ p = 1 := by
      rw [← pow_mul, mul_comm, ← hc, hm, pow_orderOf_eq_one]
    have h1 := hnp _ hz hzp
    have hm0 : 0 < m := orderOf_pos (x ^ p)
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h, mul_zero] at hc
        omega
      · exact h
    have hlt : c < m := by
      rw [hc]
      exact lt_mul_left hc0 hp.one_lt
    exact absurd (orderOf_le_of_pow_eq_one hc0 h1) (by omega)
  have hcop : Nat.Coprime m p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hmp))
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  refine ⟨m * u, ?_, ?_⟩
  · rw [map_pow, hx, ← Nat.mod_add_div (m * u) p, hu, pow_add, pow_mul, he, one_pow, mul_one,
      pow_one]
  · rw [← pow_mul, mul_comm, ← mul_assoc, pow_mul, pow_mul, hm, pow_orderOf_eq_one, one_pow]

theorem commute_of_noTorsion (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ}
    (hnp : ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1) {t s : L'} (htp : t ^ p = 1)
    (hts : ψ t * ψ s = ψ s * ψ t) : s * t = t * s := by
  set z := s * t * s⁻¹ * t⁻¹ with hz
  have hzk : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, hz, map_mul, map_mul, map_mul, map_inv, map_inv, ← hts]
    group
  have hzc := Subgroup.mem_center_iff.mp (hker hzk)
  have hst : s * t * s⁻¹ = z * t := by rw [hz]; group
  have hzp : z ^ p = 1 := by
    have h1 : (s * t * s⁻¹) ^ p = 1 := by
      rw [show s * t * s⁻¹ = MulAut.conj s t from rfl, ← map_pow, htp, map_one]
    rw [hst, (Commute.mul_pow (hzc t).symm), htp, mul_one] at h1
    exact h1
  have h1 := hnp z hzk hzp
  rw [h1, one_mul] at hst
  calc s * t = s * t * s⁻¹ * s := by group
    _ = t * s := by rw [hst]

theorem noTorsion_of_centerPrime [Finite L'] {p : ℕ} (hp : p.Prime) (hZ : GGCenterPrime p R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    ∀ z ∈ ψ.ker, z ^ p = 1 → z = 1 := by
  have := Fact.mk hp
  intro z hz hzp
  by_contra hz1
  apply hZ L' ψ hψ hker hperf
  have h1 : orderOf z = p := orderOf_eq_prime hzp hz1
  have h2 : orderOf (⟨z, hker hz⟩ : Subgroup.center L') = p := by
    rw [Subgroup.orderOf_mk]
    exact h1
  rw [← h2]
  exact orderOf_dvd_natCard _

end Lift

end StdSubRest

open TableBSymp StdSubSp StdSubRest in
theorem ggStdSubTwoTorusNorm_of_elt {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : GGOutdiagPrime p R I) (hZ : Subgroup.center R = ⊥)
    (hZp : GGCenterPrime p R) (h : GGStdSubTwoTorusEltNorm p r R) :
    GGStdSubTwoTorusNorm p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a haA ha1 hEcomp hcentA
  have hAI' : ∀ a ∈ A, ∃ φ ∈ {φ : MulAut R | φ ∈ I ∧ φ ^ p = 1}, ∀ l : L',
      φ (ψ l) = ψ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    refine ⟨φ, ⟨hφI, ?_⟩, hφ⟩
    ext x
    obtain ⟨l, rfl⟩ := hψ x
    rw [pow_apply_comp_eq hφ p l, hA.2 a ha, MulAut.one_apply, MulAut.one_apply]
  obtain ⟨χ, hχinj, hinner⟩ := exists_inducedHom (I := {φ : MulAut R | φ ∈ I ∧ φ ^ p = 1})
    (fun φ hφ => hI φ hφ.1 hφ.2) hZ hψ hker hperf hAI'
  set Ab := χ.range with hAb
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hlift : ∀ a' : A, ∃ s : L', ψ s = χ a' ∧ ∀ l, (a' : MulAut L') l = s * l * s⁻¹ := by
    intro a'
    obtain ⟨s, hs⟩ := hψ (χ a')
    exact ⟨s, hs, hinner a' s hs⟩
  have hUAb : ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ Ab ≤ Subgroup.normalizer (U : Set R) := by
    obtain ⟨U, hU1, hU2, hAU⟩ := hα
    refine ⟨U, hU1, hU2, ?_⟩
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨b, rfl⟩ u hu
    obtain ⟨l, rfl⟩ := hψ u
    obtain ⟨s, hs, hsb⟩ := hlift b
    have h1 := hAU b b.2 l hu
    rw [hsb, map_mul, map_mul, map_inv, hs] at h1
    exact h1
  set a₀ : A := ⟨a, haA⟩ with ha₀def
  obtain ⟨t', ht'⟩ := hψ (χ a₀)
  have ha₀ := hinner a₀ t' ht'
  have hfix : ggFix a = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix, show a = (a₀ : MulAut L') from rfl, ha₀,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  set C := Subgroup.centralizer ({t'} : Set L') with hC
  set E := LargeEvenLayer (ggFix a) with hE
  have hψC : ∀ y ∈ C, ψ y ∈ Subgroup.centralizer ({χ a₀} : Set R) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← ht', ← map_mul, ← map_mul, hy]
  have hχa₁ : χ a₀ ≠ 1 := by
    intro h1
    apply ha1
    have h2 : a₀ = 1 := hχinj (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  obtain ⟨D, hDC, hDn, hDq, Ub, hUbD, hUb1, hUb2, hAUb, hrest⟩ :=
    h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) hUAb (χ a₀) ⟨a₀, rfl⟩ hχa₁
  set Y := D.comap ψ with hY
  set K := ⁅Y, Y⁆ with hK
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hDq.1
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hψ hker hDq
  have hKmap : K.map ψ = D := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hDperf
  have hKC : K ≤ C := by
    intro k hk
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    refine (commute_of_mem_commutator (x := t') (fun y hy => hker ?_) hk).symm
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hDC hy)
    rw [ht', ← h1]
    group
  have hnormK : ∀ g : L', (∀ d ∈ D, ψ g * d * (ψ g)⁻¹ ∈ D) → ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
      rw [hK, Subgroup.map_commutator]
      have hYc : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
        rintro _ ⟨y, hy, rfl⟩
        show ψ (g * y * g⁻¹) ∈ D
        rw [map_mul, map_mul, map_inv]
        exact hg _ hy
      exact Subgroup.commutator_mono hYc hYc
    exact hle ⟨k, hk, rfl⟩
  have hKcomp : IsComponentOf K C := by
    refine ⟨hKC, IsSubnormal.step hKC ?_ (IsSubnormal.refl C), (isQuasisimple_iff _).mpr hKq⟩
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro k c hk hc
    exact hnormK c (fun d hd => hDn _ (hψC c hc) d hd) k hk
  have hEcomp' : IsComponentOf E C := by
    rw [← hfix]
    exact hEcomp
  have hKE : K ≤ E := by
    rw [hE, hfix]
    exact le_sSup hKcomp
  have hKEeq : K = E :=
    CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hKcomp hEcomp' hKE
  have hAbC : ∀ a' : A, χ a' ∈ Subgroup.centralizer ({χ a₀} : Set R) := by
    intro a'
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (TableB.IsElemAbelian.comm hA a'.2 a₀.2)
  have hmemK : ∀ d ∈ D, ∃ k ∈ K, ψ k = d := by
    intro d hd
    obtain ⟨k, hk, hk'⟩ := hKmap.ge hd
    exact ⟨k, hk, hk'⟩
  have hprov : ∀ b ∈ Ab, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers (χ a₀) := by
    rintro _ ⟨b₀, rfl⟩ hb
    obtain ⟨s, hs, hsb⟩ := hlift b₀
    have hfixE : ∀ j ∈ E, (b₀ : MulAut L') j = j := by
      intro j hj
      rw [hsb]
      have hjK : j ∈ K := hKEeq ▸ hj
      have hcomm := commute_of_mem_commutator (x := s) (Y := Y) (fun y hy => hker (by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs, hb _ hy]
        group)) hjK
      rw [hcomm]
      group
    have hmem := (hcentA b₀ b₀.2).mp hfixE
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have h2 : a₀ ^ n = b₀ := Subtype.ext (by simpa using hn)
    rw [← map_zpow, h2]
  obtain ⟨tb, htbD, htbp, htbA, htbU, jb, hjbD, hjb⟩ := hrest hprov
  obtain ⟨U, hUK, hU1, hU2, hUn⟩ := exists_twoSubgroup_lift_le hker hUb1 hUb2 (hUbD.trans hKmap.ge)
  obtain ⟨x, hxK, hx⟩ := hmemK tb htbD
  have hnp := noTorsion_of_centerPrime hp hZp hψ hker hperf
  obtain ⟨k, hψt, htp⟩ := exists_lift_pow_eq_one_of_noTorsion hp hnp htbp hx
  have htK : x ^ k ∈ K := Subgroup.pow_mem _ hxK k
  have htcomm : ∀ a' : A, ∀ s : L', ψ s = χ a' → s * x ^ k = x ^ k * s := by
    intro a' s hs
    refine commute_of_noTorsion hker hnp htp ?_
    rw [hψt, hs]
    exact (htbA _ ⟨a', rfl⟩).symm
  have hUA : ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U := by
    intro a' ha' u hu
    obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa]
    refine hUn s (hnormK s (fun d hd => ?_)) (fun v hv => ?_) u hu
    · rw [hs]
      exact hDn _ (hAbC _) d hd
    · rw [hs]
      exact hAUb _ ⟨_, rfl⟩ v hv
  have hN : ∀ g : L', g ∈ K → ψ g ∈ Subgroup.normalizer (Ub : Set R) →
      ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hgK hgN u hu
    refine hUn g (fun k hk => K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK)) (fun v hv => ?_) u hu
    exact (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  obtain ⟨j, hjK, hj⟩ := hmemK jb hjbD
  refine ⟨U, hU1, hU2, hUK.trans hKE, hUA, x ^ k, hKE htK, htp, fun a' ha' => ?_, ?_,
    j, hKE hjK, fun hcomm => hjb ?_⟩
  · obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa, htcomm _ s hs]
    group
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hN (x ^ k) htK (hψt ▸ htbU) u
    · intro hu
      have := hN (x ^ k)⁻¹ (K.inv_mem htK)
        (by rw [map_inv, hψt]; exact Subgroup.inv_mem _ htbU) _ hu
      simpa [mul_assoc] using this
  · have := congrArg ψ hcomm
    rwa [map_mul, map_mul, hψt, hj] at this

end CFSG.StandardType
