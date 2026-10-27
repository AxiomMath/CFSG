module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inspection15418Facts
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2PerfectOfCard
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace Insp15418

theorem isQuasisimple_of_open {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  have hp : Group.IsPerfect Q := ⟨hQ.1⟩
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  refine ⟨hp, hQ.2, ?_⟩
  have h := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using h

theorem isQuasisimple_of_isSimpleGroup {Q : Type*} [Group Q] [hs : IsSimpleGroup Q]
    (hp : Group.IsPerfect Q) : CFSG.IsQuasisimple Q := by
  have hZ : Subgroup.center Q = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
    · exact h
    · exfalso
      have hc : commutator Q = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top x) y)
      have htop : commutator Q = ⊤ := Group.IsPerfect.commutator_eq_top
      rw [hc] at htop
      obtain ⟨a, b, hab⟩ := exists_pair_ne Q
      exact hab ((Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top a)).trans
        (Subgroup.mem_bot.mp (htop ▸ Subgroup.mem_top b)).symm)
  have e : Q ⧸ Subgroup.center Q ≃* Q :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hsq : IsSimpleGroup (Q ⧸ Subgroup.center Q) := e.isSimpleGroup
  refine ⟨hp, hsq, ?_⟩
  have : Group.IsPerfect (Q ⧸ Subgroup.center Q) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (Subgroup.center Q))
  have h := Group.IsPerfect.not_isMulCommutative (Q ⧸ Subgroup.center Q)
  simpa only [isMulCommutative_iff, not_forall] using h

theorem le_ker_of_isPerfect {X A : Type*} [Group X] [Group A] (hA : ∀ a b : A, a * b = b * a)
    (f : X →* A) {M : Subgroup X} (hM : Group.IsPerfect ↥M) : M ≤ f.ker := by
  have hMM : ⁅M, M⁆ = M := Subgroup.isPerfect_iff.mp hM
  have hbot : M.map f = ⊥ := by
    rw [← hMM, Subgroup.map_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hA y x
  exact (Subgroup.map_eq_bot_iff _).mp hbot

theorem eq_of_isComponent_of_le {X : Type*} [Group X] [Finite X] {N M : Subgroup X}
    (hN : CFSG.IsQuasisimple ↥N) (hM : CFSG.IsComponent M) (hMN : M ≤ N) : M = N := by
  have hM' := CFSG.LocalCores.component_overgroup hM hMN
  have htop : CFSG.IsComponent (⊤ : Subgroup ↥N) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hN,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.distinct_components_commute hM' htop with h | h
  · refine le_antisymm hMN fun x hx => ?_
    have : (⟨x, hx⟩ : ↥N) ∈ M.subgroupOf N := h ▸ Subgroup.mem_top _
    exact this
  · exfalso
    have hc : ⁅M.subgroupOf N, M.subgroupOf N⁆ = ⊥ :=
      le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl le_top)
    rw [Subgroup.isPerfect_iff.mp hM'.1.1] at hc
    exact (Subgroup.nontrivial_iff_ne_bot _).mp
      (CFSG.LocalCores.isQuasisimple_nontrivial hM'.1) hc

theorem eq_of_isComponent_of_ker {X A : Type*} [Group X] [Finite X] [Group A]
    (hA : ∀ a b : A, a * b = b * a) (f : X →* A) (hN : CFSG.IsQuasisimple ↥f.ker)
    {M : Subgroup X} (hM : CFSG.IsComponent M) : M = f.ker :=
  eq_of_isComponent_of_le hN hM (le_ker_of_isPerfect hA f hM.1.1)

theorem units_int_comm : ∀ a b : ℤˣ, a * b = b * a := fun a b => mul_comm a b

theorem isPerfect_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (hn : ∃ a b : Q, a * b ≠ b * a) : Group.IsPerfect Q := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hn
    have : ⁅a, b⁆ ∈ commutator Q :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact hab this
  · exact ⟨h⟩

theorem index_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (M : Subgroup X) :
    (M.map e.toMonoidHom).index = M.index := by
  have h : (M.map e.toMonoidHom).comap e.toMonoidHom = M :=
    Subgroup.comap_map_eq_self_of_injective e.injective M
  rw [← Subgroup.index_comap_of_surjective (f := e.toMonoidHom) (M.map e.toMonoidHom)
    e.surjective, h]

theorem alternating_seven_not_comm : ∃ a b : ↥(alternatingGroup (Fin 7)), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩, ?_⟩
  intro h
  have := congrArg Subtype.val h
  revert this
  decide

theorem isQuasisimple_alternating_seven : CFSG.IsQuasisimple ↥(alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  exact isQuasisimple_of_isSimpleGroup (isPerfect_of_isSimpleGroup alternating_seven_not_comm)

theorem eq_alternating_of_isComponent {M : Subgroup (Equiv.Perm (Fin 7))}
    (hM : CFSG.IsComponent M) : M = alternatingGroup (Fin 7) :=
  eq_of_isComponent_of_ker units_int_comm Equiv.Perm.sign isQuasisimple_alternating_seven hM

theorem index_of_perm_seven {D : Type} [Group D] [Finite D] (e : D ≃* Equiv.Perm (Fin 7))
    {M : Subgroup D} (hM : CFSG.IsComponent M) : M.index = 2 := by
  rw [← index_map_mulEquiv e M,
    eq_alternating_of_isComponent (CFSG.LocalCores.isComponent_map_mulEquiv e hM)]
  exact alternatingGroup.index_eq_two

theorem index_of_isHatSym {n : ℕ} (hn : 2 ≤ n) {D : Type} [Group D] [Finite D]
    (h : F6.IsHatSym n D) {M : Subgroup D} (hM : CFSG.IsComponent M) : M.index = 2 := by
  obtain ⟨φ, hφ, -, hhat⟩ := h
  have hker : (Equiv.Perm.sign.comp φ).ker = (alternatingGroup (Fin n)).comap φ := by
    rw [← MonoidHom.comap_ker]
    rfl
  have hq : CFSG.IsQuasisimple ↥(Equiv.Perm.sign.comp φ).ker := by
    rw [hker]
    exact isQuasisimple_of_open hhat.1
  rw [eq_of_isComponent_of_ker units_int_comm _ hq hM, hker,
    Subgroup.index_comap_of_surjective _ hφ]
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  exact alternatingGroup.index_eq_two

theorem le_normalizer_of_forall {X : Type*} [Group X] {R H : Subgroup X}
    (h : ∀ g ∈ R, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : R ≤ Subgroup.normalizer (H : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (R.inv_mem hg) _ hx
  simpa [mul_assoc] using this

open CFSG.GorensteinWalter in
theorem range_inr_le_normalizer_psl (K : Type) [Field K] :
    (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range ≤
      Subgroup.normalizer (pGammaL2PSLRange K : Set (PGammaL2 K)) := by
  refine le_normalizer_of_forall ?_
  rintro _ ⟨σ, rfl⟩ x hx
  obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K x).mp hx
  refine (mem_pGammaL2PSLRange_iff K _).mpr ⟨psl2FieldAut K σ y, ?_⟩
  rw [psl2FieldAut_toPGL, SemidirectProduct.inl_aut, map_inv]

open CFSG.GorensteinWalter in
theorem mem_psl_of_rightHom_eq_one (K : Type) [Field K] {x : PGammaL2 K}
    (hx : x ∈ F6.PSigmaL2 K) (h1 : SemidirectProduct.rightHom x = 1) :
    x ∈ pGammaL2PSLRange K := by
  have hx' : x ∈ ((SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range ⊔
      pGammaL2PSLRange K : Subgroup (PGammaL2 K)) := by
    rw [sup_comm]
    exact hx
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (range_inr_le_normalizer_psl K)
  have hx'' : x ∈ ((((SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range ⊔
      pGammaL2PSLRange K : Subgroup (PGammaL2 K))) : Set (PGammaL2 K)) := hx'
  rw [hset] at hx''
  obtain ⟨_, ⟨σ, rfl⟩, l, hl, rfl⟩ := Set.mem_mul.mp hx''
  obtain ⟨y, rfl⟩ := (mem_pGammaL2PSLRange_iff K l).mp hl
  rw [map_mul, SemidirectProduct.rightHom_inr, SemidirectProduct.rightHom_inl, mul_one] at h1
  rw [h1, map_one, one_mul]
  exact (mem_pGammaL2PSLRange_iff K _).mpr ⟨y, rfl⟩

open CFSG.GorensteinWalter in
theorem ker_pSigmaL2_rightHom (K : Type) [Field K] :
    ((SemidirectProduct.rightHom).comp (F6.PSigmaL2 K).subtype).ker =
      (pGammaL2PSLRange K).subgroupOf (F6.PSigmaL2 K) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · exact fun h => mem_psl_of_rightHom_eq_one K x.2 h
  · intro h
    obtain ⟨y, hy⟩ := (mem_pGammaL2PSLRange_iff K _).mp h
    change SemidirectProduct.rightHom (x : PGammaL2 K) = 1
    rw [← hy, SemidirectProduct.rightHom_inl]

open CFSG.GorensteinWalter in
@[expose] noncomputable def pslEquivPSigma (K : Type) [Field K] :
    PSL2 K ≃* ↥((pGammaL2PSLRange K).subgroupOf (F6.PSigmaL2 K)) :=
  (pGammaL2PSLRangeEquiv K).trans (Subgroup.subgroupOfEquivOfLe le_sup_left).symm

open CFSG.GorensteinWalter in
theorem eq_psl_of_isComponent {p : ℕ} (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) [Finite ↥(F6.PSigmaL2 K)] {M : Subgroup ↥(F6.PSigmaL2 K)}
    (hM : CFSG.IsComponent M) : M = (pGammaL2PSLRange K).subgroupOf (F6.PSigmaL2 K) := by
  obtain ⟨-, hcyc⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK
  have hcomm : ∀ a b : K ≃+* K, a * b = b * a := by
    have : IsCyclic (K ≃+* K) := hcyc
    exact fun a b => (IsCyclic.isMulCommutative (α := K ≃+* K)).is_comm.comm a b
  have hcard4 : 4 ≤ Nat.card K := by
    rw [hK]
    have := hp.two_le
    nlinarith
  have hq : CFSG.IsQuasisimple
      ↥((SemidirectProduct.rightHom).comp (F6.PSigmaL2 K).subtype).ker := by
    have : IsSimpleGroup (PSL2 K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard4
    have hpsl : CFSG.IsQuasisimple (PSL2 K) :=
      isQuasisimple_of_isSimpleGroup (psl2_isPerfect_of_card_gt_three K (by omega))
    rw [ker_pSigmaL2_rightHom]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (pslEquivPSigma K) hpsl
  rw [eq_of_isComponent_of_ker hcomm _ hq hM, ker_pSigmaL2_rightHom]

open CFSG.GorensteinWalter in
theorem index_of_pSigmaL2 {p : ℕ} (hp : p.Prime) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = p ^ 2) [Finite ↥(F6.PSigmaL2 K)] {M : Subgroup ↥(F6.PSigmaL2 K)}
    (hM : CFSG.IsComponent M) : M.index = 2 := by
  obtain ⟨hAut, -⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK
  have hsurj : Function.Surjective
      ((SemidirectProduct.rightHom).comp (F6.PSigmaL2 K).subtype) := by
    intro σ
    refine ⟨⟨SemidirectProduct.inr σ, le_sup_right (a := pGammaL2PSLRange K) ⟨σ, rfl⟩⟩, ?_⟩
    change SemidirectProduct.rightHom (SemidirectProduct.inr σ : PGammaL2 K) = σ
    exact SemidirectProduct.rightHom_inr σ
  rw [eq_psl_of_isComponent hp K hK hM, ← ker_pSigmaL2_rightHom, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
  exact hAut

end Insp15418

open Insp15418

theorem componentIndexTwo15418_holds : ComponentIndexTwo15418 := by
  intro D _ _ hD M hM
  rcases hD with h | he | h | ⟨p, hp, K, _, _, hK, he⟩
  · exact index_of_isHatSym (by norm_num) h hM
  · obtain ⟨e⟩ := he
    exact index_of_perm_seven e hM
  · exact index_of_isHatSym (by norm_num) h hM
  · obtain ⟨e⟩ := he
    have : Finite ↥(F6.PSigmaL2 K) := Finite.of_equiv D e.toEquiv
    rw [← index_map_mulEquiv e M]
    exact index_of_pSigmaL2 hp K hK (CFSG.LocalCores.isComponent_map_mulEquiv e hM)

end CFSG.Quasithin.EmptyFaithfulMultiple
