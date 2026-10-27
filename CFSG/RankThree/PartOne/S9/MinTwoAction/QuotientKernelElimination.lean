module

public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientBridge
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientKernelCore

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY SemidirectProduct
  CFSG.RankThree.PartOne.Quotient36
open scoped IsMulCommutative commutatorElement

namespace Quotient36

section Irred

variable {G : Type*} [Group G]

theorem irredFrattini_ofSubgroups {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hLX : R ⊔ A ≤ Subgroup.normalizer (X : Set G))
    (hirr : IsFrattiniIrreducibleFor (R ⊔ A) X) :
    letI C := Compat.ofSubgroups hAR (le_trans le_sup_left hLX) (le_trans le_sup_right hLX)
    letI := C.actE
    IrredFrattini (C.Q ⋊[C.φ] ↥A) ↥X := by
  let C := Compat.ofSubgroups hAR (le_trans le_sup_left hLX) (le_trans le_sup_right hLX)
  let _ := C.actE
  obtain ⟨-, hlt, hmin⟩ := hirr
  refine ⟨?_, ?_⟩
  · by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hbt : (⊥ : Subgroup (↥X ⧸ frattini ↥X)) = ⊤ := Subsingleton.elim _ _
    have h1 := (liftSub_eq_frattini_iff (X := X) ⊥).mpr rfl
    have h2 := (liftSub_eq_top_iff (X := X) ⊤).mpr rfl
    rw [hbt] at h1
    exact hlt.ne (h1.symm.trans h2)
  · intro T hT
    have hRX := le_trans le_sup_left hLX
    have hAX := le_trans le_sup_right hLX
    have hnorm : R ⊔ A ≤ Subgroup.normalizer (liftSub X T : Set G) := by
      refine sup_le ?_ ?_
      · refine le_normalizer_liftSub hRX T fun h x hx => ?_
        have h1 := hT (SemidirectProduct.inl (h : C.Q)) _ hx
        change ((((SemidirectProduct.inl (h : C.Q) : C.Q ⋊[C.φ] ↥A)) • x : ↥X) :
          ↥X ⧸ frattini ↥X) ∈ T at h1
        rw [C.actE_inl] at h1
        exact h1
      · refine le_normalizer_liftSub hAX T fun a x hx => ?_
        have h1 := hT (SemidirectProduct.inr a) _ hx
        change ((((SemidirectProduct.inr a : C.Q ⋊[C.φ] ↥A)) • x : ↥X) :
          ↥X ⧸ frattini ↥X) ∈ T at h1
        rw [C.actE_inr] at h1
        exact h1
    rcases hmin _ (frattini_le_liftSub T) (liftSub_le T) hnorm with h0 | h1
    · exact Or.inl ((liftSub_eq_frattini_iff T).mp h0)
    · exact Or.inr ((liftSub_eq_top_iff T).mp h1)

theorem irreducible_phi_ofSubgroups {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hirr : ∀ Y : Subgroup G, R ⊓ Subgroup.centralizer (X : Set G) ≤ Y → Y ≤ R →
      A ≤ Subgroup.normalizer (Y : Set G) →
      Y = R ⊓ Subgroup.centralizer (X : Set G) ∨ Y = R) :
    let C := Compat.ofSubgroups hAR hRX hAX
    ∀ U : Subgroup C.Q, (∀ a : ↥A, ∀ x ∈ U, C.φ a x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro C U hU
  let Y : Subgroup G := (U.comap (QuotientGroup.mk' C.fR.ker)).map R.subtype
  have hmem : ∀ g : G, g ∈ Y ↔ ∃ h : g ∈ R, ((⟨g, h⟩ : ↥R) : C.Q) ∈ U := by
    intro g
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r.2, hr⟩
    · rintro ⟨h, hg⟩
      exact ⟨⟨g, h⟩, hg, rfl⟩
  have hker : ∀ r : ↥R, r ∈ C.fR.ker ↔ (r : G) ∈ Subgroup.centralizer (X : Set G) :=
    fun r => mem_ker_conjHom hRX r
  have h1 : R ⊓ Subgroup.centralizer (X : Set G) ≤ Y := by
    intro g hg
    refine (hmem g).mpr ⟨hg.1, ?_⟩
    have : (⟨g, hg.1⟩ : ↥R) ∈ C.fR.ker := (hker _).mpr hg.2
    have h2 : ((⟨g, hg.1⟩ : ↥R) : C.Q) = 1 := (QuotientGroup.eq_one_iff _).mpr this
    rw [h2]
    exact U.one_mem
  have h2 : Y ≤ R := Subgroup.map_subtype_le _
  have h3 : A ≤ Subgroup.normalizer (Y : Set G) := by
    refine le_normalizer_of_conj_mem fun a ha g hg => ?_
    obtain ⟨hgR, hgU⟩ := (hmem g).mp hg
    have hagR : a * g * a⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hAR ha) g).mp hgR
    refine (hmem _).mpr ⟨hagR, ?_⟩
    have := hU ⟨a, ha⟩ _ hgU
    exact this
  rcases hirr Y h1 h2 h3 with hY | hY
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective u
    have hrY : (r : G) ∈ Y := (hmem _).mpr ⟨r.2, hu⟩
    rw [hY] at hrY
    exact (QuotientGroup.eq_one_iff r).mpr ((hker r).mpr hrY.2)
  · right
    rw [Subgroup.eq_top_iff']
    intro u
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective u
    have hrY : (r : G) ∈ Y := by rw [hY]; exact r.2
    exact (hmem _).mp hrY |>.2

theorem phi_eq_of_mem_centralizer {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (b : ↥A)
    (hb : (b : G) ∈ Subgroup.centralizer (R : Set G)) (s : (Compat.ofSubgroups hAR hRX hAX).Q) :
    (Compat.ofSubgroups hAR hRX hAX).φ b s = s := by
  let C := Compat.ofSubgroups hAR hRX hAX
  obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
  rw [Compat.φ_mk]
  have : C.ψ b r = r := by
    apply Subtype.ext
    change (b : G) * r * (b : G)⁻¹ = r
    have h1 := Subgroup.mem_centralizer_iff.mp hb (r : G) r.2
    calc (b : G) * r * (b : G)⁻¹ = (r * b) * (b : G)⁻¹ := by rw [← h1]
      _ = r := by group
  rw [this]

theorem card_range_phi_ofSubgroups {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) [Finite A] {p d : ℕ} (hp : p.Prime)
    (hAcard : Nat.card A = p ^ 2)
    (hB : Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) = p)
    (hSd : Nat.card (Compat.ofSubgroups hAR hRX hAX).Q = 2 ^ d) (hd : 2 ≤ d)
    (hirr : ∀ U : Subgroup (Compat.ofSubgroups hAR hRX hAX).Q,
      (∀ a : ↥A, ∀ x ∈ U, (Compat.ofSubgroups hAR hRX hAX).φ a x ∈ U) → U = ⊥ ∨ U = ⊤) :
    Nat.card (Compat.ofSubgroups hAR hRX hAX).φ.range = p := by
  let C := Compat.ofSubgroups hAR hRX hAX
  have : Fact p.Prime := ⟨hp⟩
  have : Finite C.Q := Nat.finite_of_card_ne_zero (by rw [hSd]; positivity)
  have hBle : A ⊓ Subgroup.centralizer (R : Set G) ≤ A := inf_le_left
  let B' : Subgroup ↥A := (A ⊓ Subgroup.centralizer (R : Set G)).subgroupOf A
  have hB'card : Nat.card B' = p := by
    rw [← hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv
  have hB'le : B' ≤ C.φ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro s
    exact phi_eq_of_mem_centralizer hAR hRX hAX b (Subgroup.mem_subgroupOf.mp hb).2 s
  have hdvd1 : p ∣ Nat.card C.φ.ker := hB'card ▸ Subgroup.card_dvd_of_le hB'le
  have hdvd2 : Nat.card C.φ.ker ∣ p ^ 2 := hAcard ▸ Subgroup.card_subgroup_dvd_card _
  obtain ⟨j, hj2, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd2
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hj
    rw [hj] at hdvd1
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd1)
  have hj1 : j = 1 := by
    by_contra hne
    have hj2' : j = 2 := by omega
    subst hj2'
    have htop : C.φ.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hj, hAcard])
    have hφ1 : ∀ (a : ↥A) (s : C.Q), C.φ a s = s := by
      intro a s
      have : a ∈ C.φ.ker := by rw [htop]; exact Subgroup.mem_top _
      rw [MonoidHom.mem_ker] at this
      rw [this]
      rfl
    have hdv : 2 ∣ Nat.card C.Q := by
      rw [hSd]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C.Q) 2 hdv
    rcases hirr (Subgroup.zpowers t) (fun a x hx => by rw [hφ1]; exact hx) with h0 | h1
    · have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      rw [h0, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at ht
      omega
    · have h2 := Nat.card_zpowers t
      rw [h1, Subgroup.card_top, hSd, ht] at h2
      have : 2 ^ 2 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
      omega
  subst hj1
  have h3 := Subgroup.card_ker_mul_card_range C.φ
  rw [hj, hAcard, pow_one] at h3
  have : p * Nat.card C.φ.range = p * p := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_left hp.pos this

theorem fixed_map_eq {R A X : Subgroup G}
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hRX : R ≤ Subgroup.normalizer (X : Set G))
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (r : ↥R) :
    letI C := Compat.ofSubgroups hAR hRX hAX
    letI := C.actE
    (fixedPointSubgroup (Subgroup.zpowers (SemidirectProduct.inl (r : C.Q) : C.Q ⋊[C.φ] ↥A))
      ↥X).map X.subtype = X ⊓ Subgroup.centralizer ({(r : G)} : Set G) := by
  let C := Compat.ofSubgroups hAR hRX hAX
  let _ := C.actE
  have hfix : ∀ x : ↥X, x ∈ fixedPointSubgroup (Subgroup.zpowers
      (SemidirectProduct.inl (r : C.Q) : C.Q ⋊[C.φ] ↥A)) ↥X ↔ (r : G) * x = x * (r : G) := by
    intro x
    rw [mem_fixedPointSubgroup_zpowers_iff, C.actE_inl]
    constructor
    · intro h
      have h1 := congrArg (fun y : ↥X => (y : G)) h
      change (r : G) * x * (r : G)⁻¹ = x at h1
      calc (r : G) * x = ((r : G) * x * (r : G)⁻¹) * r := by group
        _ = x * r := by rw [h1]
    · intro h
      apply Subtype.ext
      change (r : G) * x * (r : G)⁻¹ = x
      calc (r : G) * x * (r : G)⁻¹ = (x * r) * (r : G)⁻¹ := by rw [h]
        _ = x := by group
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({(r : G)} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hfix x).mp hx).symm
  · rintro ⟨hgX, hgC⟩
    refine ⟨⟨g, hgX⟩, (hfix ⟨g, hgX⟩).mpr ?_, rfl⟩
    have hgC' : g ∈ Subgroup.centralizer ({(r : G)} : Set G) := hgC
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC'
    exact hgC'.symm

end Irred

end Quotient36

theorem elementaryFaithfulQuotientKernelElimination :
    ElementaryFaithfulQuotientKernelElimination := by
  intro G _ _ p q d A D R X hp hq hp3 hq2 hpq hpd hAel hAcard hR2 hAR hLD hDq hDexp hDcl hrk hXD
    hXirr hcomm hsq hidx hAirr hB
  classical
  have hLX : R ⊔ A ≤ Subgroup.normalizer (X : Set G) := hXirr.1
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_left hLX
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_trans le_sup_right hLX
  let C := Compat.ofSubgroups hAR hRX hAX
  have hker : ∀ r : ↥R, r ∈ C.fR.ker ↔ (r : G) ∈ Subgroup.centralizer (X : Set G) :=
    fun r => mem_ker_conjHom hRX r
  have hKsub : (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R = C.fR.ker := by
    ext r
    rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨r.2, h⟩⟩
  have hq1 : 1 < q := hq.one_lt
  have hXq : IsPGroup q ↥X := hDq.of_injective (Subgroup.inclusion hXD)
    (Subgroup.inclusion_injective hXD)
  have hXexp : ∀ x : ↥X, x ^ q = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow]
    exact hDexp x (hXD x.2))
  have hXcl : commutator ↥X ≤ Subgroup.center ↥X := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ = 1 := by
      have : ⁅⁅(a : G), (b : G)⁆, (z : G)⁆ ∈ ⁅⁅D, D⁆, D⁆ :=
        Subgroup.commutator_mem_commutator
          (Subgroup.commutator_mem_commutator (hXD a.2) (hXD b.2)) (hXD z.2)
      rw [hDcl, Subgroup.mem_bot] at this
      exact this
    apply Subtype.ext
    have h2 := commutatorElement_eq_one_iff_mul_comm.mp h1
    have e : ((⁅a, b⁆ : ↥X) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, e]
    exact h2.symm
  have hcomm' : commutator ↥R ≤ C.fR.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [hker]
    have e : ((⁅a, b⁆ : ↥R) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
    rw [e]
    exact (hcomm (Subgroup.commutator_mem_commutator a.2 b.2)).2
  have hsq' : ∀ r : ↥R, r ^ 2 ∈ C.fR.ker := fun r => by
    rw [hker, Subgroup.coe_pow]
    exact (hsq r r.2).2
  have hSel : IsElementaryAbelian 2 C.Q := isElementaryAbelian_two_quotient C.fR.ker hcomm' hsq'
  have hSd : Nat.card C.Q = 2 ^ d := by
    rw [← hidx]
    have : Nat.card C.Q = C.fR.ker.index := rfl
    rw [this, ← hKsub]
    rfl
  have hd2 : 2 ≤ d := by rcases hpd with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hirrφ := irreducible_phi_ofSubgroups hAR hRX hAX hAirr
  have hφ := card_range_phi_ofSubgroups hAR hRX hAX hp hAcard hB hSd hd2 hirrφ
  have hIrr := irredFrattini_ofSubgroups hAR hLX hXirr
  let _ := C.actE
  have hfaith : ∀ s : C.Q, (∀ x : ↥X, (SemidirectProduct.inl s : C.Q ⋊[C.φ] ↥A) • x = x) →
      s = 1 := by
    intro s hs
    refine (injective_iff_map_eq_one C.fS).mp C.fS_injective s ?_
    apply MulEquiv.ext
    intro x
    rw [← C.actE_inl]
    exact hs x
  have hfixrank : ∀ r : ↥R,
      CFSG.pRank q ↥(fixedPointSubgroup (Subgroup.zpowers
        (SemidirectProduct.inl (r : C.Q) : C.Q ⋊[C.φ] ↥A)) ↥X) =
      CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({(r : G)} : Set G)) := by
    intro r
    rw [← pRank_map_subtype hq1, fixed_map_eq hAR hRX hAX r]
  have hmono : ∀ r : ↥R, CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({(r : G)} : Set G)) ≤
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({(r : G)} : Set G)) := fun r =>
    pRank_mono_subgroup hq1 (inf_le_inf_right _ hXD)
  have hne1 : ∀ r : ↥R, (r : C.Q) ≠ 1 → (r : G) ≠ 1 := by
    intro r hr h1
    apply hr
    have : r = 1 := Subtype.ext h1
    rw [this]
    rfl
  have hrank : ∀ s : C.Q, s ≠ 1 → CFSG.pRank q ↥(fixedPointSubgroup (Subgroup.zpowers
      (SemidirectProduct.inl s : C.Q ⋊[C.φ] ↥A)) ↥X) ≤ 3 := by
    intro s hs
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    rw [hfixrank r]
    exact (hmono r).trans (hrk r r.2 (hne1 r hs))
  have hAfin : Finite ↥A := inferInstance
  have : IsElementaryAbelian p ↥A := hAel
  have : IsElementaryAbelian 2 C.Q := hSel
  obtain ⟨hcard, h4, hex, h7, h5, hAc⟩ := kernel_elimination_core hp hq hp3 hq2 hpq hpd hXq
    hXexp hXcl hSd C.φ hφ hirrφ hfaith hIrr hrank
  have htr : ∀ r : ↥R, (r : G) ≠ 1 → CFSG.pRank q ↥(fixedPointSubgroup (Subgroup.zpowers
      (SemidirectProduct.inl (r : C.Q) : C.Q ⋊[C.φ] ↥A)) ↥X) = 3 →
      CFSG.pRank q ↥(X ⊓ Subgroup.centralizer ({(r : G)} : Set G)) = 3 ∧
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({(r : G)} : Set G)) = 3 := by
    intro r hr1 h3
    rw [hfixrank r] at h3
    refine ⟨h3, le_antisymm (hrk r r.2 hr1) ?_⟩
    rw [← h3]
    exact hmono r
  have hK0 : R ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    by_contra hne
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
    have hX : X ≤ D ⊓ Subgroup.centralizer ({g} : Set G) := by
      intro x hx
      refine ⟨hXD hx, ?_⟩
      show x ∈ Subgroup.centralizer ({g} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hg.2 x hx
    have h1 := pRank_mono_subgroup hq1 hX
    have h2 := hrk g hg.1 hg1'
    omega
  have hne1' : ∀ g : G, ∀ hgR : g ∈ R, g ≠ 1 → ((⟨g, hgR⟩ : ↥R) : C.Q) ≠ 1 := by
    intro g hgR hg1 h
    have h' : (⟨g, hgR⟩ : ↥R) ∈ C.fR.ker := (QuotientGroup.eq_one_iff _).mp h
    have : g ∈ R ⊓ Subgroup.centralizer (X : Set G) := ⟨hgR, (hker _).mp h'⟩
    rw [hK0, Subgroup.mem_bot] at this
    exact hg1 this
  refine ⟨hK0, ?_, ?_, ?_, h4, ?_, ?_, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · apply Subtype.ext
      have h1 : ⁅(a : G), (b : G)⁆ ∈ R ⊓ Subgroup.centralizer (X : Set G) :=
        hcomm (Subgroup.commutator_mem_commutator a.2 b.2)
      rw [hK0, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun r => Subtype.ext ?_
      have h1 := hsq r r.2
      rw [hK0, Subgroup.mem_bot] at h1
      simpa using h1
  · rw [hK0, Subgroup.relIndex_bot_left] at hidx
    exact hidx
  · have h1 : (inSubgroup frattini X).relIndex X = Nat.card (↥X ⧸ frattini ↥X) := by
      rw [Subgroup.relIndex]
      have : (inSubgroup frattini X).subgroupOf X = frattini ↥X :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
      rw [this]
      rfl
    rw [h1, hcard]
  · obtain ⟨s, hs1, hs3⟩ := hex
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective s
    have hr1 := hne1 r hs1
    obtain ⟨h31, h32⟩ := htr r hr1 hs3
    exact ⟨r, r.2, hr1, h31, h32⟩
  · intro hp7 g hgR hg1
    exact htr ⟨g, hgR⟩ hg1 (h7 hp7 _ (hne1' g hgR hg1))
  · intro hp5
    let ι : C.Q → G := fun s => ((Function.surjInv (QuotientGroup.mk_surjective
      (s := C.fR.ker)) s : ↥R) : G)
    have hι : Function.Injective ι := fun s t h =>
      Function.injective_surjInv (QuotientGroup.mk_surjective (s := C.fR.ker))
        (Subtype.ext h)
    refine (h5 hp5).trans ?_
    rw [← Set.ncard_image_of_injective _ hι]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨s, ⟨hs1, hs3⟩, rfl⟩
    have hsr := Function.surjInv_eq (QuotientGroup.mk_surjective (s := C.fR.ker)) s
    set r : ↥R := Function.surjInv (QuotientGroup.mk_surjective (s := C.fR.ker)) s
    have hr1 : (r : G) ≠ 1 := hne1 r (by rw [hsr]; exact hs1)
    rw [← hsr] at hs3
    obtain ⟨h31, h32⟩ := htr r hr1 hs3
    exact ⟨r.2, hr1, h31, h32⟩
  · rcases hAc with hAc | hqp
    · left
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro b hb
      have hx := hAc ⟨b, hb.1⟩ (fun s => phi_eq_of_mem_centralizer hAR hRX hAX ⟨b, hb.1⟩ hb.2 s)
      rw [Subgroup.mem_centralizer_iff]
      intro x hxX
      have hx' := hx ⟨x, hxX⟩
      rw [C.actE_inr] at hx'
      have h1 := congrArg (fun y : ↥X => (y : G)) hx'
      change (b : G) * x * (b : G)⁻¹ = x at h1
      calc x * b = ((b : G) * x * (b : G)⁻¹) * b := by rw [h1]
        _ = b * x := by group
    · exact Or.inr hqp

end CFSG.RankThree.PartOne
