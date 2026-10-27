module

public import CFSG.RankThree.GF2n.Smith81.LinOddDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualInv
import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVICoord
public import CFSG.RankThree.GF2n.Stroth80.SectionActRank

public section

namespace CFSG.RankThree.GF2n.Stroth80.NatDualCoord

variable {Γ : Type} [Group Γ] {K F E : Type} [Field K] [Field F] [AddCommGroup E] [Module K E]
  {n : ℕ} {ρ : Γ →* (E ≃ₗ[K] E)} {ρ' : Γ →* GL (Fin n) F} (C : NatDualCoord ρ ρ')

theorem preserves_iff_forall_mem (T : E ≃ₗ[K] E) :
    C.Preserves T ↔ (∀ e ∈ C.W₁, T e ∈ C.W₁) ∧ (∀ e ∈ C.W₂, T e ∈ C.W₂) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · have := h1 (C.Ψ e).1
      rwa [← C.eq_inl_of_mem_W₁ he] at this
    · have := h2 (C.Ψ e).2
      rwa [← C.eq_inr_of_mem_W₂ he] at this
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 _ (C.inl_mem_W₁ x), fun y => h2 _ (C.inr_mem_W₂ y)⟩

theorem swaps_iff_forall_mem (T : E ≃ₗ[K] E) :
    C.Swaps T ↔ (∀ e ∈ C.W₁, T e ∈ C.W₂) ∧ (∀ e ∈ C.W₂, T e ∈ C.W₁) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · have := h1 (C.Ψ e).1
      rwa [← C.eq_inl_of_mem_W₁ he] at this
    · have := h2 (C.Ψ e).2
      rwa [← C.eq_inr_of_mem_W₂ he] at this
  · rintro ⟨h1, h2⟩
    exact ⟨fun x => h1 _ (C.inl_mem_W₁ x), fun y => h2 _ (C.inr_mem_W₂ y)⟩

end CFSG.RankThree.GF2n.Stroth80.NatDualCoord

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem SectionAct.exists_comm_not_mem {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {S V Z : Subgroup G} {φ : ↥S →* GL ι K} {act : GL ι K → Matrix ι ι K}
    (h : SectionAct K S V Z φ act) (a : ↥S) (ha : act (φ a) ≠ 1) :
    ∃ v ∈ V, ⁅(a : G), v⁆ ∉ Z := by
  obtain ⟨hS, hN, ψ, hψ⟩ := h
  haveI := hN
  obtain ⟨w, hw⟩ : ∃ w : ι → K, act (φ a) *ᵥ w ≠ w := by
    by_contra hcon
    push Not at hcon
    exact ha (Matrix.ext_iff_mulVec.mpr fun v => by rw [hcon v, Matrix.one_mulVec])
  obtain ⟨c, hc⟩ := ψ.surjective (Multiplicative.ofAdd w)
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective c
  have hav : (a : G) * v * (a : G)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hS a.2) v).mp v.2
  refine ⟨v, v.2, fun hmem => hw ?_⟩
  have hq : (QuotientGroup.mk (⟨(a : G) * v * (a : G)⁻¹, hav⟩ : ↥V) :
      ↥V ⧸ Z.subgroupOf V) = QuotientGroup.mk v := by
    have h1 : (⟨(a : G) * v * (a : G)⁻¹, hav⟩ : ↥V) * v⁻¹ ∈ Z.subgroupOf V := by
      rw [Subgroup.mem_subgroupOf]
      simpa [commutatorElement_def] using hmem
    have := (QuotientGroup.eq_one_iff _).mpr h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at this
    exact mul_inv_eq_one.mp this
  have e1 := hψ a v ⟨_, hav⟩ rfl
  rw [hq, hc] at e1
  simpa using e1.symm

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem map_le_iff_conjSubgroup_le {Q Z V V' : Subgroup G} {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {t : G} (T : M₀.E ≃ₗ[K] M₀.E) {S S' : AddSubgroup M₀.E}
    (hS : ∀ e, e ∈ S ↔ e ∈ M₀.img V) (hS' : ∀ e, e ∈ S' ↔ e ∈ M₀.img V')
    (hQ : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q) (hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x))
    (hZV' : Z ≤ V') (hVQ : V ≤ Q) :
    (∀ e ∈ S, T e ∈ S') ↔ conjSubgroup t V ≤ V' := by
  constructor
  · intro h x hx
    rw [mem_conjSubgroup] at hx
    have hvQ : t⁻¹ * x * t ∈ Q := hVQ hx
    have hxQ : x ∈ Q := by
      have := hQ _ hvQ
      rwa [show t * (t⁻¹ * x * t) * t⁻¹ = x by group] at this
    have hv := (hS' _).mp (h (M₀.π (t⁻¹ * x * t)) ((hS _).mpr (M₀.pi_mem_img hx hvQ)))
    rw [← hT _ hvQ, show t * (t⁻¹ * x * t) * t⁻¹ = x by group] at hv
    exact (M₀.mem_img_iff hZV' hxQ).mp hv
  · intro h e he
    obtain ⟨x, hxV, hxQ, rfl⟩ := (hS e).mp he
    rw [hS', ← hT x hxQ]
    refine M₀.pi_mem_img (h ?_) (hQ x hxQ)
    rw [mem_conjSubgroup, show t⁻¹ * (t * x * t⁻¹) * t = x by group]
    exact hxV

private theorem exists_inclusion_conj [Finite G] {M L Z : Subgroup G}
    (hSH : Lgen M L ≤ H0 M Z) {A : Type*} [Group A] (φ : ↥(H0 M Z) →* A) (t : ↥(H0 M Z))
    (g : ↥(Lgen M L)) :
    ∃ g' : ↥(Lgen M L),
      φ (Subgroup.inclusion hSH g) * φ t = φ t * φ (Subgroup.inclusion hSH g') := by
  have htM : (t : G) ∈ M := (t.2 : (t : G) ∈ M ⊓ _).1
  have hg' : (t : G)⁻¹ * (g : G) * (t : G) ∈ Lgen M L := by
    have := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M L (M.inv_mem htM)) g).mp g.2
    simpa using this
  refine ⟨⟨_, hg'⟩, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (g : G) * (t : G) = (t : G) * ((t : G)⁻¹ * (g : G) * (t : G))
  group

private theorem LinSetup.sections_bounds {M Q Z B : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}
    (h : LinSetup M Q Z B n V₁ V₂) :
    Z ≤ V₁ ∧ V₁ ≤ Q ∧ Z ≤ V₂ ∧ V₂ ≤ Q ∧ Nat.card V₁ = Nat.card V₂ := by
  obtain ⟨K, _, _, -, φ, -, -, hZV₁, hV₁Q, hZV₂, hV₂Q, -, -, -, -, ⟨x, -, hxV⟩, -⟩ := h
  exact ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, by rw [← hxV, card_conjSubgroup]⟩

private theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {k : ℕ}
    (h : Nat.card K = 2 ^ k) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  have hd : ringChar K ∣ 2 ^ k := by
    rw [← h, Nat.card_eq_fintype_card, hm]
    exact dvd_pow_self _ m.ne_zero
  have hp2 : ringChar K = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
  rw [← hp2]
  exact ringChar.charP K

theorem exists_linCoord [Finite G] {M Q Z B : Subgroup G} {n : ℕ}
    {V₁ V₂ : Subgroup G} (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂) (hn : 3 ≤ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
      (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (ρ' : ↥(Lgen M (LB M Q B)) →* GL (Fin n) F)
      (C : NatDualCoord (φ.comp (Subgroup.inclusion (Lgen_le_H0 hc))) ρ'),
      Nat.card K = Nat.card Z ∧ 2 < Nat.card K ∧
      (∀ (m : ↥(H0 M Z)) (x : G), x ∈ Q →
        M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) ∧
      (∀ m : ↥(H0 M Z), φ m = 1 ↔ (m : G) ∈ Q) ∧
      (∀ (m : ↥(H0 M Z)) e, M₀.Qf (φ m e) = M₀.Qf e) ∧
      ρ'.range = StatedSL n F ∧
      (∀ e, e ∈ M₀.img V₁ ↔ (C.Ψ e).2 = 0) ∧ (∀ e, e ∈ M₀.img V₂ ↔ (C.Ψ e).1 = 0) ∧
      ∀ t : ↥(H0 M Z), C.Preserves (φ t) ∨ C.Swaps (φ t) := by
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  obtain ⟨F, hFfield, hFfin, hFcard, φ', hrange, -, hZV₁, hV₁Q, hZV₂, hV₂Q, hinf, hsup,
    hact₁, hact₂, -, -⟩ := hS
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  obtain ⟨Φ, hΦ, hΦ₁, hΦ₂⟩ := exists_equivariant_coord M₀ (φ.comp (Subgroup.inclusion hSH))
    (fun s x hx => hφπ ⟨s, hSH s.2⟩ x hx) hZV₁ hV₁Q hZV₂ hV₂Q hinf hsup φ' hact₁ hact₂
  obtain ⟨C, hCΦ⟩ := exists_natDualCoord_of_equivariant (φ.comp (Subgroup.inclusion hSH)) φ' hn
    hrange (by rw [h.card, hFcard]) Φ hΦ
  have hq4 := hc.hyp.q4
  haveI : CharP F 2 := charP_of_injective_ringHom (f := C.θ₁.toRingHom) C.θ₁.injective 2
  have hps : ∀ t : ↥(H0 M Z), C.Preserves (φ t) ∨ C.Swaps (φ t) := by
    intro t
    refine C.preserves_or_swaps hn hrange (φ t) fun g => ?_
    obtain ⟨g', hg'⟩ := exists_inclusion_conj hSH φ t g
    refine ⟨g', fun e => ?_⟩
    have := LinearEquiv.congr_fun hg' e
    simpa using this
  refine ⟨GaloisField 2 m, inferInstance, inferInstance, inferInstance, γ, M₀, φ, F, hFfield,
    hFfin, inferInstance, φ', C, h.card, ?_, hφπ, hφQ, hφiso, hrange, fun e => ?_, fun e => ?_,
    hps⟩
  · rw [h.card]
    omega
  · rw [hCΦ]
    exact hΦ₁ e
  · rw [hCΦ]
    exact hΦ₂ e

theorem linSwapStatement_holds : LinSwapStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS hn t ht
  obtain ⟨hZV₁, hV₁Q, hZV₂, hV₂Q, hcard⟩ := hS.sections_bounds
  obtain ⟨K, _, _, _, γ, M₀, φ, F, _, _, _, ρ', C, -, -, hφπ, -, -, -, hV₁, hV₂, hps⟩ :=
    exists_linCoord hc hS hn
  have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = φ ⟨t, ht⟩ (M₀.π x) := hφπ ⟨t, ht⟩
  have hQt : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ht.1) x).mp hx
  have hW₁ : ∀ e, e ∈ C.W₁ ↔ e ∈ M₀.img V₁ := fun e => C.mem_W₁.trans (hV₁ e).symm
  have hW₂ : ∀ e, e ∈ C.W₂ ↔ e ∈ M₀.img V₂ := fun e => C.mem_W₂.trans (hV₂ e).symm
  rcases hps ⟨t, ht⟩ with hP | hSw
  · left
    obtain ⟨h1, h2⟩ := (C.preserves_iff_forall_mem _).mp hP
    have e1 := (map_le_iff_conjSubgroup_le _ hW₁ hW₁ hQt hTπ hZV₁ hV₁Q).mp h1
    have e2 := (map_le_iff_conjSubgroup_le _ hW₂ hW₂ hQt hTπ hZV₂ hV₂Q).mp h2
    exact ⟨Subgroup.eq_of_le_of_card_ge e1 (by rw [card_conjSubgroup]),
      Subgroup.eq_of_le_of_card_ge e2 (by rw [card_conjSubgroup])⟩
  · right
    obtain ⟨h1, h2⟩ := (C.swaps_iff_forall_mem _).mp hSw
    have e1 := (map_le_iff_conjSubgroup_le _ hW₁ hW₂ hQt hTπ hZV₂ hV₁Q).mp h1
    have e2 := (map_le_iff_conjSubgroup_le _ hW₂ hW₁ hQt hTπ hZV₁ hV₂Q).mp h2
    exact ⟨Subgroup.eq_of_le_of_card_ge e1 (by rw [card_conjSubgroup, hcard]),
      Subgroup.eq_of_le_of_card_ge e2 (by rw [card_conjSubgroup, hcard.symm])⟩

theorem linNonswapStatement_holds : LinNonswapStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS hn t ht htt hconj
  obtain ⟨hZV₁, hV₁Q, -, -, -⟩ := hS.sections_bounds
  obtain ⟨K, _, _, _, γ, M₀, φ, F, _, _, _, ρ', C, -, hK, hφπ, hφker, hφQ, hrange, hV₁, -, hps⟩ :=
    exists_linCoord hc hS hn
  have hSH : Lgen M (LB M Q B) ≤ H0 M Z := Lgen_le_H0 hc
  have hTπ : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = φ ⟨t, ht⟩ (M₀.π x) := hφπ ⟨t, ht⟩
  have hQt : ∀ x ∈ Q, t * x * t⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 ht.1) x).mp hx
  have hW₁ : ∀ e, e ∈ C.W₁ ↔ e ∈ M₀.img V₁ := fun e => C.mem_W₁.trans (hV₁ e).symm
  have hT2 : ∀ e, φ ⟨t, ht⟩ (φ ⟨t, ht⟩ e) = e := by
    have h1 : φ (⟨t, ht⟩ * ⟨t, ht⟩) = 1 := (hφker _).mpr htt
    intro e
    have := LinearEquiv.congr_fun h1 e
    rwa [map_mul, LinearEquiv.mul_apply] at this
  have hP : C.Preserves (φ ⟨t, ht⟩) := by
    rcases hps ⟨t, ht⟩ with hP | hSw
    · exact hP
    · exfalso
      obtain ⟨h1, -⟩ := (C.swaps_iff_forall_mem _).mp hSw
      have hW₁T := (map_le_iff_conjSubgroup_le _ hW₁ hW₁ hQt hTπ hZV₁ hV₁Q).mpr hconj.le
      obtain ⟨x₀, hx₀⟩ := NatDualCoord.exists_ne_zero (F := F) (by omega : 1 ≤ n)
      have hzero : φ ⟨t, ht⟩ (C.inl x₀) = 0 := by
        apply C.Ψ.injective
        rw [map_zero]
        exact Prod.ext (C.mem_W₂.mp (h1 _ (C.inl_mem_W₁ x₀)))
          (C.mem_W₁.mp (hW₁T _ (C.inl_mem_W₁ x₀)))
      have h0 : C.inl x₀ = 0 := (φ ⟨t, ht⟩).injective (by rw [hzero, map_zero])
      exact hx₀ (C.inl_injective (by rw [h0, map_zero]))
  obtain ⟨g, hg⟩ := C.exists_eq_of_preserves (quadDatumOfModel M₀) hn hrange
    (fun g e => hφQ _ e) (exists_ne_zero_sq_ne_one_of_two_lt_card K hK) (φ ⟨t, ht⟩) hT2
    (fun e => hφQ _ e) hP
  have h1 : φ (⟨t, ht⟩ * (Subgroup.inclusion hSH g)⁻¹) = 1 := by
    have h2 : φ (Subgroup.inclusion hSH g) = φ ⟨t, ht⟩ := hg
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h2 : t * (g : G)⁻¹ ∈ Q := (hφker _).mp h1
  have hQL : Q ≤ Lgen M (LB M Q B) := le_sup_left.trans (le_Lgen_self M (LB M Q B))
  have h3 : t = (t * (g : G)⁻¹) * g := by group
  rw [h3]
  exact (Lgen M (LB M Q B)).mul_mem (hQL h2) g.2

theorem linFaithfulStatement_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → ∀ a ∈ Lgen M (LB M Q B), a ∉ Q →
        (∃ v ∈ V₁, ⁅a, v⁆ ∉ Z) ∧ (∃ v ∈ V₂, ⁅a, v⁆ ∉ Z) := by
  intro G _ _ M Q Z B n V₁ V₂ _ hS a haL haQ
  obtain ⟨K, _, _, -, φ, -, hker, -, -, -, -, -, -, hs₁, hs₂, -, -⟩ := hS
  have hφ : φ ⟨a, haL⟩ ≠ 1 := by
    intro h
    apply haQ
    have h1 : (⟨a, haL⟩ : ↥(Lgen M (LB M Q B))) ∈ φ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  refine ⟨SectionAct.exists_comm_not_mem hs₁ ⟨a, haL⟩ fun h => hφ (Units.ext h),
    SectionAct.exists_comm_not_mem hs₂ ⟨a, haL⟩ fun h => hφ ?_⟩
  have h1 : (((φ ⟨a, haL⟩)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
    Matrix.transpose_eq_one.mp h
  exact inv_eq_one.mp (Units.ext h1)

theorem linRankBoundStatement_holds : LinRankBoundStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS a haL haQ haaQ
  obtain ⟨K, _, _, hcard, φ, -, hker, hZV₁, -, hZV₂, -, -, -, hs₁, hs₂, -, -⟩ := hS
  obtain ⟨_, _, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hcard.trans hZ2)
  set a' : ↥(Lgen M (LB M Q B)) := ⟨a, haL⟩
  have hφ1 : φ a' ≠ 1 := by
    intro h
    apply haQ
    have h1 : a' ∈ φ.ker := h
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hφ2 : φ a' * φ a' = 1 := by
    rw [← map_mul]
    have h1 : a' * a' ∈ φ.ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact haaQ
    exact h1
  set A : Matrix (Fin n) (Fin n) K := ((φ a' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hAA : A * A = 1 := by
    have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) hφ2
    simpa using this
  have hA1 : A ≠ 1 := fun h => hφ1 (Units.ext h)
  have hsq : (A - 1) * (A - 1) = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    calc (A - 1) * (A - 1) = A * A - A - A + 1 := by noncomm_ring
      _ = (1 + 1) - (A + A) := by rw [hAA]; abel
      _ = 0 := by
        rw [← two_smul K (1 : Matrix (Fin n) (Fin n) K), ← two_smul K A, h2, zero_smul,
          zero_smul, sub_zero]
  have hrk_le : 2 * (A - 1).rank ≤ n := by
    have h1 : LinearMap.range (Matrix.mulVecLin (A - 1)) ≤
        LinearMap.ker (Matrix.mulVecLin (A - 1)) := by
      rw [LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, hsq, Matrix.mulVecLin_zero]
    have h2 := Submodule.finrank_mono h1
    have h3 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (A - 1))
    rw [Module.finrank_fin_fun] at h3
    show 2 * Module.finrank K (LinearMap.range (Matrix.mulVecLin (A - 1))) ≤ n
    omega
  have hrk_pos : 1 ≤ (A - 1).rank := by
    by_contra hlt
    have h0 : (A - 1).rank = 0 := by omega
    apply hA1
    have h1 : LinearMap.range (Matrix.mulVecLin (A - 1)) = ⊥ :=
      Submodule.finrank_eq_zero.mp h0
    have h2 : ∀ v, (A - 1) *ᵥ v = 0 := by
      intro v
      have h3 : (Matrix.mulVecLin (A - 1)) v ∈ LinearMap.range (Matrix.mulVecLin (A - 1)) :=
        LinearMap.mem_range_self _ v
      rw [h1, Submodule.mem_bot] at h3
      exact h3
    have h3 : A - 1 = 0 := Matrix.ext_iff_mulVec.mpr fun v => by rw [h2 v, Matrix.zero_mulVec]
    exact sub_eq_zero.mp h3
  refine ⟨(A - 1).rank, hrk_pos, by omega, ?_, ?_⟩
  · have h1 : Nat.card ↥(⁅V₁, Subgroup.zpowers (a' : G)⁆ ⊔ Z) =
        Nat.card Z * Nat.card K ^ (A - 1).rank :=
      card_comm_zpowers_sup_of_sectionAct hs₁ hZV₁ a'
    show Nat.card ↥(⁅V₁, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z ^ ((A - 1).rank + 1)
    rw [h1, hcard]
    ring
  · have h2 : Nat.card ↥(⁅V₂, Subgroup.zpowers (a' : G)⁆ ⊔ Z) =
        Nat.card Z * Nat.card K ^
          ((((φ a')⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ - 1).rank :=
      card_comm_zpowers_sup_of_sectionAct hs₂ hZV₂ a'
    rw [rank_inv_transpose_sub_one] at h2
    show Nat.card ↥(⁅V₂, Subgroup.zpowers a⁆ ⊔ Z) = Nat.card Z ^ ((A - 1).rank + 1)
    rw [h2, hcard]
    ring

end CFSG.RankThree.GF2n.Smith81
