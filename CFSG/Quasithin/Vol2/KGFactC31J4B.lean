module

public import CFSG.Quasithin.Vol2.KGFactC31J4A
public import CFSG.Quasithin.Vol2.KGFactC31NatSec
public import CFSG.Quasithin.Vol2.KGFactC31E8

public section

namespace CFSG.Quasithin.KGC31.J4

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31
open scoped Pointwise

variable {A : Type} [Group A]

theorem sup_inf_centralizer_eq' {M₀ R V : Subgroup A}
    (hRN : R ≤ Subgroup.normalizer (M₀ : Set A)) (hRC : R ≤ Subgroup.centralizer (V : Set A))
    (hM₀C : M₀ ⊓ Subgroup.centralizer (V : Set A) ≤ R) :
    (M₀ ⊔ R) ⊓ Subgroup.centralizer (V : Set A) = R := by
  refine le_antisymm (fun x ⟨hx, hxC⟩ => ?_) (le_inf le_sup_right hRC)
  have hx' : x ∈ ((M₀ : Set A) * (R : Set A)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left M₀ R hRN]
    exact hx
  obtain ⟨m, hm, r, hr, rfl⟩ := hx'
  have hmC : m ∈ Subgroup.centralizer (V : Set A) := by
    have : m = m * r * r⁻¹ := by group
    rw [this]
    exact (Subgroup.centralizer (V : Set A)).mul_mem hxC
      ((Subgroup.centralizer (V : Set A)).inv_mem (hRC hr))
  exact R.mul_mem (hM₀C ⟨hm, hmC⟩) hr

theorem isSpecial2Group_of_equiv {a b : ℕ} {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsSpecial2Group a b X) : IsSpecial2Group a b Y := by
  obtain ⟨hc, hcomm, hq⟩ := h
  have hZ : (Subgroup.center X).map e.toMonoidHom = Subgroup.center Y := Subgroup.map_center_eq e
  refine ⟨?_, ?_, isE2_of_mulEquiv b _ _ (QuotientGroup.congr _ _ e hZ) hq⟩
  · rw [← hZ, Subgroup.card_map_of_injective e.injective, hc]
  · rw [← hZ, ← hcomm, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]

theorem isSpecial2Group_map {a b : ℕ} {G : Type} [Group G] {κ : G →* A}
    (hκ : Function.Injective κ) {Q : Subgroup G} {K : Subgroup A} (hQK : Q.map κ ≤ K)
    (h : IsSpecial2Group a b ↥Q) : IsSpecial2Group a b ↥((Q.map κ).subgroupOf K) :=
  isSpecial2Group_of_equiv ((Q.equivMapOfInjective κ hκ).trans
    (Subgroup.subgroupOfEquivOfLe hQK).symm) h

theorem cComp_cases_map {G : Type} [Group G] (κ : G →* A) (hinj : Function.Injective κ)
    (hsurj : Function.Surjective κ) {X K W : Subgroup G}
    (h : ∀ L ∈ cComp X, conjClosure L X = K ∨ L ≤ Subgroup.centralizer (W : Set G))
    {L : Subgroup A} (hL : L ∈ cComp (X.map κ)) :
    conjClosure L (X.map κ) = K.map κ ∨
      L ≤ Subgroup.centralizer ((W.map κ : Subgroup A) : Set A) := by
  let e : G ≃* A := MulEquiv.ofBijective κ ⟨hinj, hsurj⟩
  have h1 : e.symm.toMonoidHom.comp κ = MonoidHom.id G :=
    MonoidHom.ext fun x => e.symm_apply_apply x
  have h2 : κ.comp e.symm.toMonoidHom = MonoidHom.id A :=
    MonoidHom.ext fun x => e.apply_symm_apply x
  have hL' := cComp_map_mulEquiv e.symm hL
  rw [Subgroup.map_map, h1, Subgroup.map_id] at hL'
  have hLL : (L.map e.symm.toMonoidHom).map κ = L := by rw [Subgroup.map_map, h2, Subgroup.map_id]
  rcases h _ hL' with h3 | h3
  · left
    rw [← hLL, ← map_conjClosure_eq, h3]
  · right
    rw [← hLL]
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (h3 hy) w hw]

theorem map_pCoreOf_le [Finite A] {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V)
    {κ : G₀ →* A} (hκ : Iso κ) {X : Subgroup G₀}
    (hNR : Subgroup.normalizer (R : Set A) ≤ X.map κ) : (pCoreOf 2 X).map κ ≤ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_of_normalizer_le h.hR2 h.hrad hNR
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).map κ) ?_
  rw [← hκ.map_normalizer]
  exact Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)

theorem le_centralizer_map [Finite A] {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V)
    {κ : G₀ →* A} (hκ : Iso κ) {X : Subgroup G₀}
    (hNR : Subgroup.normalizer (R : Set A) ≤ X.map κ) :
    CFSG.Quasithin.centerOf R ≤
      (Subgroup.centralizer ((pCoreOf 2 X : Subgroup G₀) : Set G₀)).map κ := by
  rw [hκ.map_centralizer]
  exact inf_le_right.trans (Subgroup.centralizer_le (map_pCoreOf_le h hκ hNR))

theorem branch_H [Finite A]
    {S M₀ R M V : Subgroup A}
    (h : Setup S M₀ R M V) {κ : G₀ →* A} (hκ : Iso κ)
    (hNR : Subgroup.normalizer (R : Set A) ≤ CFSG.Sporadic.J4.Hj.map κ) :
    ∃ B : Subgroup A, B ≤ R ∧ IsElemAbelian 2 B ∧ 2 ^ 11 ≤ Nat.card B := by
  have F := hFacts hκ
  exact ⟨_, le_of_normalizer_le h.hR2 h.hrad hNR F.pGroup F.NE.ge, F.elemAb, F.card.ge⟩

theorem branch_M2 [Finite A]
    {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V) {κ : G₀ →* A} (hκ : Iso κ)
    (hNR : Subgroup.normalizer (R : Set A) ≤
      (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set G₀)).map κ)
    (hD3 : Subgroup.centralizer ((pCoreOf 2 (Subgroup.centralizer
      ({CFSG.Quasithin.J4Loc.z0} : Set G₀)) : Subgroup G₀) : Set G₀) ≤
      Subgroup.zpowers CFSG.Quasithin.J4Loc.z0) : False := by
  have hz : CFSG.Quasithin.J4Loc.z0 ^ 2 = 1 := by
    rw [pow_two]
    exact CFSG.Sporadic.J4.QT.eta_sq
      (CFSG.Sporadic.J4.QT.elem_uJ CFSG.Sporadic.J4.j4Facts.mat) 1131
  refine h.not_card_le_four ((h.V_le_center.trans (le_centralizer_map h hκ hNR)).trans
    (Subgroup.map_mono hD3)) ?_
  rw [hκ.card_map, Nat.card_zpowers]
  exact (orderOf_le_of_pow_eq_one (by norm_num) hz).trans (by norm_num)

noncomputable abbrev M3J : Subgroup G₀ := Subgroup.normalizer (CFSG.Quasithin.J4Loc.V0 : Set G₀)

structure M3Facts (KL : Subgroup G₀) {v0 : Fin 3 → G₀} (hv0 : EBasis v0) : Prop where
  cent : Subgroup.centralizer ((pCoreOf 2 M3J : Subgroup G₀) : Set G₀) ≤ CFSG.Quasithin.J4Loc.V0
  max : ∀ X : Subgroup G₀, M3J ≤ X → X = M3J ∨ X = ⊤
  le : KL ≤ M3J
  norm : M3J ≤ Subgroup.normalizer (KL : Set G₀)
  comp : ∀ L ∈ cComp M3J, conjClosure L M3J = KL ∨
    L ≤ Subgroup.centralizer (CFSG.Quasithin.J4Loc.V0 : Set G₀)
  core_le : pCoreOf 2 M3J ≤ KL
  inf_cent : KL ⊓ Subgroup.centralizer (CFSG.Quasithin.J4Loc.V0 : Set G₀) = pCoreOf 2 M3J
  special : IsSpecial2Group 3 12 ↥(pCoreOf 2 M3J)
  basis : eSub hv0 = CFSG.Quasithin.J4Loc.V0
  enorm : KL ≤ eNorm hv0
  surj : Function.Surjective (E16.eNHom hv0 enorm)

theorem concl_M3 [Finite A] {S R : Subgroup A} (hSs : IsSporadic .J4 ↥S) {κ : G₀ →* A}
    (hκ : Iso κ) {KL : Subgroup G₀} {v0 : Fin 3 → G₀} {hv0 : EBasis v0} (F : M3Facts KL hv0)
    (hRX : R ≤ M3J.map κ) (hQR : (pCoreOf 2 M3J).map κ ≤ R)
    (hRC : R ≤ Subgroup.centralizer ((CFSG.Quasithin.J4Loc.V0.map κ : Subgroup A) : Set A)) :
    Concl S (KL.map κ) R (M3J.map κ) (CFSG.Quasithin.J4Loc.V0.map κ) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvA : EBasis fun i => κ (v0 i) := hv0.map hκ.inj
  have hV0A : CFSG.Quasithin.J4Loc.V0.map κ = eSub hvA := by
    rw [← F.basis, eSub_map hv0 hκ.inj]
  rw [hV0A] at hRC ⊢
  have hKLX : M3J.map κ ≤ Subgroup.normalizer ((KL.map κ : Subgroup A) : Set A) := by
    rw [← hκ.map_normalizer]
    exact Subgroup.map_mono F.norm
  have hXQ : M3J.map κ ≤ Subgroup.normalizer (((pCoreOf 2 M3J).map κ : Subgroup A) : Set A) := by
    rw [← hκ.map_normalizer]
    exact Subgroup.map_mono (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M3J)
  have hKLe : KL.map κ ≤ eNorm hvA := by
    show KL.map κ ≤ Subgroup.normalizer (eSub hvA : Set A)
    rw [← eSub_map hv0 hκ.inj, ← hκ.map_normalizer]
    exact Subgroup.map_mono F.enorm
  have hinf : KL.map κ ⊓ Subgroup.centralizer (eSub hvA : Set A) = (pCoreOf 2 M3J).map κ := by
    rw [← eSub_map hv0 hκ.inj, F.basis, ← hκ.map_centralizer, ← Subgroup.map_inf_eq _ _ κ hκ.inj,
      F.inf_cent]
  have hQKL : (pCoreOf 2 M3J).map κ ≤ KL.map κ := Subgroup.map_mono F.core_le
  have hker₀ := ker_eNHom hvA hKLe hinf
  have hcJ : Nat.card ↥(E16.eNHom hv0 F.enorm).range * Nat.card ↥(pCoreOf 2 M3J) =
      Nat.card ↥KL :=
    card_range_eq F.core_le _ (ker_eNHom hv0 F.enorm (by rw [F.basis]; exact F.inf_cent))
  rw [MonoidHom.range_eq_top.mpr F.surj, Subgroup.card_top, E8.card_statedSL3] at hcJ
  have hsurj₀ : Function.Surjective (E16.eNHom hvA hKLe) := by
    have h1 := card_range_eq hQKL _ hker₀
    rw [hκ.card_map, hκ.card_map, ← hcJ] at h1
    have h2 : Nat.card ↥(E16.eNHom hvA hKLe).range =
        Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := by
      rw [E8.card_statedSL3]
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ h2
  have hQ2 : IsPGroup 2 ↥((pCoreOf 2 M3J).map κ) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M3J).map κ
  have : IsSimpleGroup ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hKL2 : ¬ IsPGroup 2 ↥(KL.map κ) := fun h2 => by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (h2.of_surjective _ hsurj₀)
    rw [E8.card_statedSL3] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
    have h4 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h4
  have hO : pCoreOf 2 (KL.map κ) = (pCoreOf 2 M3J).map κ :=
    pCoreOf_eq_of_max hQKL ((Subgroup.map_mono F.le).trans hXQ) hQ2
      (simple_of_surj _ hsurj₀ hker₀) hKL2
  have hpk : CFSG.pCore 2 ↥(KL.map κ) = (E16.eNHom hvA hKLe).ker := by
    rw [← Hex.pCoreOf_subgroupOf', hO, hker₀]
  have hpsl : IsPSL 3 2 1 (ModO2 (KL.map κ)) := E8.isPSL_of_equiv3
    ((QuotientGroup.quotientMulEquivOfEq hpk).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hsurj₀))
  have hL3 : C31Case6L3 (M3J.map κ) (KL.map κ) := by
    show IsExt ↥(conjClosure (KL.map κ) (M3J.map κ)) _ _
    rw [conjClosure_eq_self' hKLX]
    refine ⟨(E16.eNHom hvA hKLe).ker, inferInstance, ?_,
      E8.isPSL_of_equiv3 (QuotientGroup.quotientKerEquivOfSurjective _ hsurj₀)⟩
    rw [hker₀]
    exact isSpecial2Group_map hκ.inj hQKL F.special
  have hXC : (KL.map κ ⊔ R) ⊓ Subgroup.centralizer (eSub hvA : Set A) = R :=
    sup_inf_centralizer_eq' (hRX.trans hKLX) hRC (hinf.le.trans hQR)
  have hsum := sum_natural_of_surj hvA hKLe hRC hsurj₀ hXC
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨hSs, Or.inr (Or.inl hL3)⟩))),
    Or.inr (Or.inl ⟨3, Or.inl rfl, hpsl, Or.inl ⟨1, le_rfl, hsum⟩⟩), summand_of_card ?_⟩
  rw [card_eSub]
  norm_num

theorem branch_M3 [Finite A] {S M₀ R M V : Subgroup A} (h : Setup S M₀ R M V) (hS : S = ⊤)
    {κ : G₀ →* A} (hκ : Iso κ) (hNR : Subgroup.normalizer (R : Set A) ≤ M3J.map κ)
    {KL : Subgroup G₀} {v0 : Fin 3 → G₀} {hv0 : EBasis v0} (F : M3Facts KL hv0) :
    Concl S M₀ R M V := by
  have hZV0 : CFSG.Quasithin.centerOf R ≤ CFSG.Quasithin.J4Loc.V0.map κ :=
    (le_centralizer_map h hκ hNR).trans (Subgroup.map_mono F.cent)
  have hVV0 : V ≤ CFSG.Quasithin.J4Loc.V0.map κ := h.V_le_center.trans hZV0
  have hcV0 : Nat.card ↥(CFSG.Quasithin.J4Loc.V0.map κ) = 2 ^ 3 := by
    rw [hκ.card_map, ← F.basis, card_eSub]
  have hVeq : V = CFSG.Quasithin.J4Loc.V0.map κ := by
    have hdvd : Nat.card V ∣ 2 ^ 3 := hcV0 ▸ Subgroup.card_dvd_of_le hVV0
    obtain ⟨i, hi, hVi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have h4 : ¬ Nat.card V ≤ 4 := fun h4 => h.not_card_le_four le_rfl h4
    have h8 : Nat.card V = 2 ^ 3 := by
      rw [hVi] at h4 ⊢
      interval_cases i <;> simp at h4 ⊢
    exact Subgroup.eq_of_le_of_card_ge hVV0 (le_of_eq (by rw [h8, hcV0]))
  have hZ : CFSG.Quasithin.centerOf R = CFSG.Quasithin.J4Loc.V0.map κ :=
    le_antisymm hZV0 (by rw [← hVeq]; exact h.V_le_center)
  have hXM : M3J.map κ ≤ M := by
    have h1 := h.hZ
    rwa [hZ, ← hκ.map_normalizer] at h1
  have hMeq : M = M3J.map κ := by
    rcases F.max _ (Subgroup.map_le_iff_le_comap.mp hXM) with h2 | h2
    · rw [← hκ.map_comap M, h2]
    · exfalso
      apply h.hSM
      rw [hS, ← hκ.map_comap M, h2, Subgroup.map_top_of_surjective _ hκ.surj]
  subst hMeq
  obtain ⟨L, hL, hM₀L⟩ := h.hcomp
  have hM₀ : M₀ = KL.map κ := by
    rcases cComp_cases_map κ hκ.inj hκ.surj F.comp hL with h1 | h1
    · rw [hM₀L, h1]
    · exfalso
      apply h.hVne
      rw [← h.hcomm, Subgroup.commutator_eq_bot_iff_le_centralizer, hVeq,
        Subgroup.le_centralizer_iff, hM₀L]
      refine conjClosure_le fun x hx l hl => ?_
      have hx' : x ∈ Subgroup.normalizer
          ((CFSG.Quasithin.J4Loc.V0.map κ : Subgroup A) : Set A) := by
        rw [← hκ.map_normalizer]
        exact hx
      exact (Subgroup.mem_normalizer_iff.mp
        (normalizer_le_normalizer_centralizer _ hx') l).mp (h1 hl)
  subst hM₀ hVeq
  exact concl_M3 h.hSs hκ F h.hRM (map_pCoreOf_le h hκ hNR) h.hRC

end CFSG.Quasithin.KGC31.J4

end
