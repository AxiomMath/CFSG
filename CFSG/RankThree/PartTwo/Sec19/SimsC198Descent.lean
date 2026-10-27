module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaSolvableQuotient

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThreeEvenClassification.Helpers
  (solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel)
open scoped commutatorElement

section CenterQuotAut

variable {X : Type} [Group X] [Finite X]

@[expose] noncomputable def centerQuotAut (X : Type) [Group X] :
    MulAut X →* MulAut (X ⧸ Subgroup.center X) where
  toFun φ := QuotientGroup.congr (Subgroup.center X) (Subgroup.center X) φ
    (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

omit [Finite X] in
theorem centerQuotAut_mk (φ : MulAut X) (x : X) :
    centerQuotAut X φ (x : X ⧸ Subgroup.center X) = ((φ x : X) : X ⧸ Subgroup.center X) :=
  rfl

omit [Finite X] in
theorem centerQuotAut_conj (x : X) :
    centerQuotAut X (MulAut.conj x) = MulAut.conj (x : X ⧸ Subgroup.center X) := by
  ext y
  induction y using QuotientGroup.induction_on
  rfl

omit [Finite X] in
theorem centerQuotAut_injective (hX : Group.IsPerfect X) :
    Function.Injective (centerQuotAut X) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  have hz : ∀ x : X, x⁻¹ * φ x ∈ Subgroup.center X := fun x => by
    have h : (x : X ⧸ Subgroup.center X) = ((φ x : X) : X ⧸ Subgroup.center X) := by
      rw [← centerQuotAut_mk, hφ]
      rfl
    exact QuotientGroup.eq.mp h
  let f : X →* Subgroup.center X :=
    { toFun := fun x => ⟨x⁻¹ * φ x, hz x⟩
      map_one' := by
        ext
        simp
      map_mul' := fun x y => by
        ext
        have h := Subgroup.mem_center_iff.mp (hz x) y⁻¹
        change (x * y)⁻¹ * φ (x * y) = (x⁻¹ * φ x) * (y⁻¹ * φ y)
        calc (x * y)⁻¹ * φ (x * y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by rw [map_mul]; group
          _ = (x⁻¹ * φ x) * y⁻¹ * φ y := by rw [h]
          _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by group }
  have hker : commutator X ≤ f.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (f b).2 (f a : X)))
  rw [Group.isPerfect_def.mp hX] at hker
  ext x
  have hx := congrArg Subtype.val (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top x)))
  change x⁻¹ * φ x = 1 at hx
  simpa using (inv_mul_eq_one.mp hx).symm

omit [Finite X] in
theorem mem_inner_of_centerQuotAut (hX : Group.IsPerfect X) {φ : MulAut X}
    (h : centerQuotAut X φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (X ⧸ Subgroup.center X)) :
    φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X := by
  obtain ⟨y, hy⟩ : ∃ y : X ⧸ Subgroup.center X,
      MulAut.conj y = centerQuotAut X φ := h
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x, ?_⟩
  apply centerQuotAut_injective hX
  rw [centerQuotAut_conj]
  exact hy

end CenterQuotAut

section TypeFacts

private theorem card_center_eq_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (Subgroup.center A) = Nat.card (Subgroup.center B) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

private theorem isSLThreePi_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : Sec4.IsSLThreePi A) : Sec4.IsSLThreePi B := by
  obtain ⟨q, K, hF, hfin, hcase⟩ := h
  refine ⟨q, K, hF, hfin, ?_⟩
  rcases hcase with ⟨hK, hq, ⟨e'⟩⟩ | ⟨hK, hq, ⟨e'⟩⟩
  · exact Or.inl ⟨hK, hq, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr ⟨hK, hq, ⟨e.symm.trans e'⟩⟩

private theorem isTripleCover_of_mulEquiv {A B Y : Type*} [Group A] [Group B] [Group Y]
    (e : A ≃* B) (h : Sec4.IsTripleCover A Y) : Sec4.IsTripleCover B Y := by
  obtain ⟨hc, ⟨f⟩⟩ := h
  refine ⟨?_, ⟨(QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e
    (Subgroup.map_center_eq e)).symm.trans f⟩⟩
  rw [← card_center_eq_of_mulEquiv' e]
  exact hc

private theorem isType198_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsType198 A) : IsType198 B := by
  rcases h with h | h | h
  · exact Or.inl (isSLThreePi_of_mulEquiv e h)
  · exact Or.inr (Or.inl (isTripleCover_of_mulEquiv e h))
  · exact Or.inr (Or.inr (isTripleCover_of_mulEquiv e h))

private theorem card_center_eq_three_of_isSLThreePi {X : Type} [Group X]
    (hX : Sec4.IsSLThreePi X) : Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
  · have hpf : Sec4.PiField true (ringChar K) n K := ⟨hp, n.2, hnc⟩
    have hq' : Sec4.ModThree true (ringChar K ^ (n : ℕ)) := by
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    rw [card_center_eq_of_mulEquiv' e]
    exact KFacts.card_center_slPi hpf hq'
  · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, pow_zero] at hm
        rw [hm] at hq
        norm_num at hq
      · exact h0
    have hpf : Sec4.PiField false (ringChar K) m K := ⟨hp, hm1, by
      rw [hK, hm]
      rfl⟩
    have hq' : Sec4.ModThree false (ringChar K ^ m) := by
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
    rw [card_center_eq_of_mulEquiv' e]
    have h := KFacts.card_center_slPi hpf hq'
    rw [← hm] at h
    exact h

private theorem card_center_eq_three_of_isType198 {Y : Type} [Group Y] (h : IsType198 Y) :
    Nat.card (Subgroup.center Y) = 3 := by
  rcases h with h | h | h
  · exact card_center_eq_three_of_isSLThreePi h
  · exact h.1
  · exact h.1

end TypeFacts

section ThetaKernel

variable {X : Type} [Group X] [Finite X]

private theorem center_subgroupOf_comm {L : Subgroup X} (n : L)
    (hn : n ∈ (Subgroup.center X).subgroupOf L) (l : L) : l * n = n * l :=
  Subtype.ext (Subgroup.mem_center_iff.mp hn (l : X))

private theorem center_subgroupOf_le_theta {c : X} {L : Subgroup X}
    (hc3 : orderOf c = 3) (hcL : c ∈ L) (hLc : L ≤ Subgroup.centralizer ({c} : Set X))
    (hZ : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3)
    (hcZ : c ∉ Subgroup.center X) :
    (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L := by
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨-, -, hθ3, hmax, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  set θ := aschbacherSolvableCore 3 L with hθdef
  set N := (Subgroup.center X).subgroupOf L with hNdef
  have hNsolv : Group.IsSolvable N :=
    isSolvable_of_comm fun a b => Subtype.ext (center_subgroupOf_comm (b : L) b.2 (a : L))
  apply hmax N inferInstance hNsolv
  intro h3
  have hnot : ¬ N ≤ θ := fun hle => hθ3 (h3.trans (Subgroup.card_dvd_of_le hle))
  obtain ⟨n, hnN, hnθ⟩ := SetLike.not_le_iff_exists.mp hnot
  let ρ : L →* L ⧸ θ := QuotientGroup.mk' θ
  have hρn : ρ n ≠ 1 := fun h => hnθ ((QuotientGroup.eq_one_iff n).mp h)
  have hρcentral : ∀ x : L, (∀ l : L, l * x = x * l) → ρ x ∈ Subgroup.center (L ⧸ θ) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    change ρ l * ρ x = ρ x * ρ l
    rw [← map_mul, ← map_mul, hx l]
  let cL : L := ⟨c, hcL⟩
  have hcLcentral : ∀ l : L, l * cL = cL * l := fun l =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp (hLc l.2) c (Set.mem_singleton c)).symm
  let g1 : Subgroup.center (L ⧸ θ) := ⟨ρ n, hρcentral n (center_subgroupOf_comm n hnN)⟩
  have hg1 : g1 ≠ 1 := fun h => hρn (congrArg Subtype.val h)
  have hmem : (⟨ρ cL, hρcentral cL hcLcentral⟩ : Subgroup.center (L ⧸ θ)) ∈
      Subgroup.zpowers g1 := mem_zpowers_of_prime_card hZ hg1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : (ρ n) ^ k = ρ cL := by simpa [g1] using congrArg Subtype.val hk
  have hmk : ((n ^ k : L) : L ⧸ θ) = (cL : L ⧸ θ) := (map_zpow ρ n k).trans hk'
  have ht : (n ^ k)⁻¹ * cL ∈ θ := QuotientGroup.eq.mp hmk
  set t : L := (n ^ k)⁻¹ * cL with htdef
  have hm3 : ¬ 3 ∣ orderOf t := fun h => hθ3 (h.trans (θ.orderOf_dvd_natCard ht))
  have hnk : n ^ k ∈ N := Subgroup.zpow_mem N hnN k
  have hcomm : Commute (n ^ k) t := (center_subgroupOf_comm (n ^ k) hnk t).symm
  have hcLt : cL = n ^ k * t := by rw [htdef, mul_inv_cancel_left]
  have hpow : cL ^ orderOf t = (n ^ k) ^ orderOf t := by
    rw [hcLt, hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  have hcm : c ^ orderOf t ∈ Subgroup.center X := by
    have h1 := congrArg Subtype.val hpow
    have h2 : (((n ^ k) ^ orderOf t : L) : X) ∈ Subgroup.center X := by
      rw [Subgroup.coe_pow, Subgroup.coe_zpow]
      exact Subgroup.pow_mem _ (Subgroup.zpow_mem _ hnN k) _
    rw [← h1] at h2
    exact h2
  have hcop : (orderOf c).Coprime (orderOf t) := by
    rw [hc3]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hm3
  have hord : orderOf (c ^ orderOf t) = orderOf c := Nat.Coprime.orderOf_pow hcop
  have hle : Subgroup.zpowers (c ^ orderOf t) ≤ Subgroup.zpowers c :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _)
  have heq : Subgroup.zpowers (c ^ orderOf t) = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  apply hcZ
  have hcz : c ∈ Subgroup.zpowers (c ^ orderOf t) := by
    rw [heq]
    exact Subgroup.mem_zpowers c
  exact Subgroup.zpowers_le.mpr hcm hcz

end ThetaKernel

section ThetaCompat

variable {X : Type} [Group X] [Finite X]

private abbrev cq (X : Type) [Group X] : X →* X ⧸ Subgroup.center X :=
  QuotientGroup.mk' (Subgroup.center X)

private abbrev psi (L : Subgroup X) : L →* L.map (cq X) := (cq X).subgroupMap L

private theorem psi_surjective (L : Subgroup X) : Function.Surjective (psi L) :=
  MonoidHom.subgroupMap_surjective _ L

private theorem psi_ker (L : Subgroup X) :
    (psi L).ker = (Subgroup.center X).subgroupOf L := by
  ext l
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

private theorem theta_psi_map (L : Subgroup X)
    (hN : (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L) :
    (aschbacherSolvableCore 3 L).map (psi L) = aschbacherSolvableCore 3 (L.map (cq X)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨hθs, -, hθ3, -, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  have hker : (psi L).ker ≤ aschbacherSolvableCore 3 L := by
    rw [psi_ker]
    exact hN
  have hkersolv : Group.IsSolvable (psi L).ker :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hker)
      (Subgroup.inclusion_injective hker)
  have hker3 : ¬ 3 ∣ Nat.card (psi L).ker := fun h =>
    hθ3 (h.trans (Subgroup.card_dvd_of_le hker))
  rw [aschbacherSolvableCore_eq_solvablePrimeComplementCore hp,
    aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]
  exact solvablePrimeComplementCore_map_eq_of_solvable_prime_complement_kernel
    3 hp (psi L) (psi_surjective L) hkersolv hker3

private theorem psi_mem_theta_iff (L : Subgroup X)
    (hN : (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L) (l : L) :
    psi L l ∈ aschbacherSolvableCore 3 (L.map (cq X)) ↔ l ∈ aschbacherSolvableCore 3 L := by
  rw [← theta_psi_map L hN]
  constructor
  · rintro ⟨t, ht, hte⟩
    have hker : t⁻¹ * l ∈ (psi L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hte, inv_mul_cancel]
    rw [psi_ker] at hker
    have := (aschbacherSolvableCore 3 L).mul_mem ht (hN hker)
    simpa using this
  · intro hl
    exact Subgroup.mem_map_of_mem _ hl

private noncomputable def thetaQuotMap (L : Subgroup X)
    (hN : (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L) :
    L ⧸ aschbacherSolvableCore 3 L →*
      L.map (cq X) ⧸ aschbacherSolvableCore 3 (L.map (cq X)) :=
  QuotientGroup.map (aschbacherSolvableCore 3 L) (aschbacherSolvableCore 3 (L.map (cq X)))
    (psi L) (by
      intro l hl
      exact (psi_mem_theta_iff L hN l).mpr hl)

private theorem thetaQuotMap_mk (L : Subgroup X)
    (hN : (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L) (l : L) :
    thetaQuotMap L hN (l : L ⧸ aschbacherSolvableCore 3 L) =
      ((psi L l : L.map (cq X)) : L.map (cq X) ⧸ aschbacherSolvableCore 3 (L.map (cq X))) :=
  rfl

private theorem thetaQuotMap_bijective (L : Subgroup X)
    (hN : (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L) :
    Function.Bijective (thetaQuotMap L hN) := by
  refine ⟨?_, ?_⟩
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    rw [thetaQuotMap_mk, thetaQuotMap_mk, QuotientGroup.eq] at hxy
    apply QuotientGroup.eq.mpr
    rw [← map_inv, ← map_mul] at hxy
    exact (psi_mem_theta_iff L hN _).mp hxy
  · intro y
    induction y using QuotientGroup.induction_on with | H y =>
    obtain ⟨a, rfl⟩ := psi_surjective L y
    exact ⟨a, rfl⟩

private noncomputable def thetaQuotEquiv (L : Subgroup X)
    (hN : (Subgroup.center X).subgroupOf L ≤ aschbacherSolvableCore 3 L) :
    L ⧸ aschbacherSolvableCore 3 L ≃*
      L.map (cq X) ⧸ aschbacherSolvableCore 3 (L.map (cq X)) :=
  MulEquiv.ofBijective (thetaQuotMap L hN) (thetaQuotMap_bijective L hN)

end ThetaCompat

section Subnormal

variable {X : Type} [Group X] [Finite X]

private abbrev cenQ (c : X) : Subgroup (X ⧸ Subgroup.center X) :=
  Subgroup.centralizer ({(c : X ⧸ Subgroup.center X)} : Set (X ⧸ Subgroup.center X))

private abbrev cenT (c : X) : Subgroup X := (cenQ c).comap (cq X)

private theorem comm_mem_center_of_mem_cenT {c y : X} (hy : y ∈ cenT c) :
    ⁅y, c⁆ ∈ Subgroup.center X := by
  have h : (cq X) y ∈ cenQ c := hy
  have hc : Commute ((cq X) y) ((cq X) c) :=
    (Subgroup.mem_centralizer_iff.mp h (cq X c) (Set.mem_singleton _)).symm
  refine (QuotientGroup.eq_one_iff _).mp ?_
  change (cq X) ⁅y, c⁆ = 1
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr hc

private noncomputable def commHom (c : X) : cenT c →* Subgroup.center X where
  toFun y := ⟨⁅(y : X), c⁆, comm_mem_center_of_mem_cenT y.2⟩
  map_one' := by
    ext
    simp
  map_mul' a b := by
    ext
    have hb := comm_mem_center_of_mem_cenT b.2
    have h1 : (a : X) * ⁅(b : X), c⁆ * (a : X)⁻¹ = ⁅(b : X), c⁆ := by
      rw [Subgroup.mem_center_iff.mp hb a, mul_inv_cancel_right]
    change ⁅(a : X) * b, c⁆ = ⁅(a : X), c⁆ * ⁅(b : X), c⁆
    rw [commutatorElement_mul_left_eq_conj_mul, h1]
    exact (Subgroup.mem_center_iff.mp hb ⁅(a : X), c⁆).symm

private theorem centralizer_subgroupOf_cenT_normal (c : X) :
    ((Subgroup.centralizer ({c} : Set X)).subgroupOf (cenT c)).Normal := by
  have h : (Subgroup.centralizer ({c} : Set X)).subgroupOf (cenT c) = (commHom c).ker := by
    ext y
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy
      refine Subtype.ext ?_
      change ⁅(y : X), c⁆ = 1
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hy c (Set.mem_singleton c)).symm
    · intro hy
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have := congrArg Subtype.val hy
      change ⁅(y : X), g⁆ = 1 at this
      exact (commutatorElement_eq_one_iff_mul_comm.mp this).symm
  rw [h]
  exact MonoidHom.normal_ker _

private theorem centralizer_le_cenT (c : X) : Subgroup.centralizer ({c} : Set X) ≤ cenT c := by
  intro y hy
  change (cq X) y ∈ cenQ c
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  exact congrArg (cq X) (Subgroup.mem_centralizer_iff.mp hy c (Set.mem_singleton c))

private theorem isSubnormal_subgroupOf_cenT {c : X} {L : Subgroup X}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set X))
    (h : (L.subgroupOf (Subgroup.centralizer ({c} : Set X))).IsSubnormal) :
    (L.subgroupOf (cenT c)).IsSubnormal := by
  have hnorm := centralizer_subgroupOf_cenT_normal c
  refine Subgroup.IsSubnormal.trans (K := (Subgroup.centralizer ({c} : Set X)).subgroupOf (cenT c))
    (fun x hx => hLc hx) ?_ hnorm.isSubnormal
  have h2 := h.comap (Subgroup.subgroupOfEquivOfLe (centralizer_le_cenT c)).toMonoidHom
  convert h2 using 1
  ext k
  rfl

private theorem isSubnormal_map_cq {c : X} {L : Subgroup X}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set X))
    (h : (L.subgroupOf (Subgroup.centralizer ({c} : Set X))).IsSubnormal) :
    ((L.map (cq X)).subgroupOf (cenQ c)).IsSubnormal := by
  have h1 := (isSubnormal_subgroupOf_cenT hLc h).map (f := (cq X).subgroupComap (cenQ c))
    ((cq X).subgroupComap_surjective _ (QuotientGroup.mk'_surjective _))
  convert h1 using 1
  ext y
  constructor
  · rintro ⟨l, hl, hly⟩
    exact ⟨⟨l, centralizer_le_cenT c (hLc hl)⟩, hl, Subtype.ext hly⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end Subnormal

section Descent

variable {X : Type} [Group X] [Finite X]

theorem LocalDatum.descent {c : X} {L : Subgroup X} (h : LocalDatum X c L)
    (hc : c ∉ Subgroup.center X) :
    LocalDatum (X ⧸ Subgroup.center X) (c : X ⧸ Subgroup.center X)
      (L.map (QuotientGroup.mk' (Subgroup.center X))) := by
  have hN := center_subgroupOf_le_theta h.orderOf_eq h.mem h.le_centralizer
    (card_center_eq_three_of_isType198 h.type) hc
  haveI := h.perfect
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h3 : (cq X c) ^ 3 = 1 := by
      rw [← map_pow, ← h.orderOf_eq, pow_orderOf_eq_one, map_one]
    have h1 : (cq X c) ≠ 1 := fun h1 => hc ((QuotientGroup.eq_one_iff c).mp h1)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 h1
  · rintro _ ⟨l, hl, rfl⟩
    exact centralizer_le_cenT c (h.le_centralizer hl)
  · exact Subgroup.mem_map_of_mem _ h.mem
  · exact isSubnormal_map_cq h.le_centralizer h.subnormal
  · exact Group.IsPerfect.map (cq X)
  · exact (CFSG.IsQuasisimple.congr (thetaQuotEquiv L hN)).mp h.quasisimple
  · exact isType198_of_mulEquiv (thetaQuotEquiv L hN) h.type

theorem AutDatum.descent (hq : IsQuasisimple X) {c : X} {L : Subgroup X}
    {𝒟 : Subgroup (MulAut X)} (h : AutDatum X c L 𝒟) (hc : c ∉ Subgroup.center X) :
    AutDatum (X ⧸ Subgroup.center X) (c : X ⧸ Subgroup.center X)
      (L.map (QuotientGroup.mk' (Subgroup.center X))) (𝒟.map (centerQuotAut X)) := by
  have hN := center_subgroupOf_le_theta h.orderOf_eq h.mem h.le_centralizer
    (card_center_eq_three_of_isType198 h.type) hc
  have hinj := centerQuotAut_injective hq.1
  have hmapL : ∀ φ ∈ 𝒟, ∀ l ∈ L.map (cq X), centerQuotAut X φ l ∈ L.map (cq X) := by
    intro φ hφ l hl
    obtain ⟨l, hl, rfl⟩ := hl
    exact ⟨φ l, (h.map_eq φ hφ l).mpr hl, rfl⟩
  refine ⟨h.toLocalDatum.descent hc, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    rw [← map_pow, h.pow_three φ hφ, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact h.card
  · exact ⟨MulAut.conj c, h.conj_mem, centerQuotAut_conj c⟩
  · rintro _ ⟨φ, hφ, rfl⟩ l
    refine ⟨fun hl => ?_, hmapL φ hφ l⟩
    have := hmapL φ⁻¹ (𝒟.inv_mem hφ) _ hl
    rwa [map_inv, MulAut.inv_apply_self] at this
  · rintro _ ⟨φ, hφ, rfl⟩ _ ⟨l, hl, rfl⟩
    obtain ⟨t, ht, hte⟩ := h.trivial φ hφ l hl
    refine Subgroup.mem_map.mpr ⟨psi L t, ?_, ?_⟩
    · rw [← theta_psi_map L hN]
      exact Subgroup.mem_map_of_mem _ ht
    · have hte' : (t : X) = φ l * l⁻¹ := hte
      change cq X (t : X) = _
      rw [hte', map_mul, map_inv]
      rfl

end Descent

end CFSG.RankThree.PartTwo.Sec19.SimsC198
