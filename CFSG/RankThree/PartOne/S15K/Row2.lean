module

public import CFSG.RankThree.PartOne.S15K.AutTorus
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagData
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartOne.KC.SymplecticTorusSetting
import CFSG.RankThree.PartOne.KC.SymplecticFullCentralizerLift
import CFSG.RankThree.PartOne.KC.SymplecticInnerPlaneCore
import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.RankThree.PartOne
  CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {G : Type} [Group G] [Finite G]

noncomputable def statedProjEquivProjSp (n : ℕ) (K : Type) [Field K] :
    StatedProj (StatedSp n K) ≃* CFSG.Assembly.RankThreeEven.projSp n K :=
  (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk (StatedSp n K)).trans
    (MulEquiv.subgroupCongr (projImage_statedSp_eq_projSp n K))

theorem row2_lifts_of_field {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E) (hEA : E = A)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hq : 3 < 2 ^ f) (hpq : p ∣ 2 ^ f - 1)
    (φ : ↥(lieGenerated p E) ≃* StatedProj (StatedSp 3 K)) :
    ∃ x : ↥E → StatedSp 3 K, (∀ e, x e ^ p = 1) ∧
      (∀ e : ↥E, MulAut.conj (proj 3 K (x e)) =
        actP φ ⟨(e : G), E_le_normalizer_lieGenerated h.prime e.2⟩) ∧
      (∀ e e' : ↥E, x e * x e' = x e' * x e) ∧ (∀ e : ↥E, e ≠ 1 → orderOf (x e) = p) ∧
      (∀ e : ↥E, e ≠ 1 →
        orderOf (actP φ ⟨(e : G), E_le_normalizer_lieGenerated h.prime e.2⟩) = p) := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hp3 : 3 < p := by omega
  have hEI : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    E_le_normalizer_lieGenerated hp
  have hWI : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    torusNormalizer_le_lieNormalizer hp E
  have hE : IsElementaryAbelian p E := h.E_elem
  have hEcard : p < Nat.card E := by
    have h3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
    rw [h3]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; omega
  obtain ⟨-, hTcenter, hTinj⟩ := spProj_facts (ℓ := 2) (f := f) Nat.prime_two hf hK
    (by norm_num : 2 ≤ 3) (by omega)
  have hZ : lieGenerated p E ⊓ Subgroup.centralizer (lieGenerated p E : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxI : x ∈ lieGenerated p E := hx.1
    have hxc := hx.2
    have h1 : φ ⟨x, hxI⟩ ∈ Subgroup.center (StatedProj (StatedSp 3 K)) := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := φ.surjective z
      have := Subgroup.mem_centralizer_iff.1 hxc (y : G) y.2
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subtype.ext this)
    rw [hTcenter, Subgroup.mem_bot] at h1
    exact congrArg Subtype.val (φ.injective (h1.trans (map_one φ).symm))
  have hpI : p ∣ Nat.card (lieGenerated p E) := by
    rw [Nat.card_congr φ.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo,
      hK]
    refine Dvd.dvd.mul_left ?_ _
    have h2f : 2 ^ f - 1 ∣ (2 ^ f) ^ (2 * 1) - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 (2 * 1)
      simpa using this
    exact (hpq.trans h2f).trans
      (Finset.dvd_prod_of_mem (fun j => (2 ^ f) ^ (2 * j) - 1) (show 1 ∈ Finset.Icc 1 3 by simp))
  have hfaith : E ⊓ Subgroup.centralizer (lieGenerated p E : Set G) = ⊥ :=
    centralizer_inf_eq_bot hp h.E_max_global hWI h13.irreducible hZ hpI
  have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hEexp' : ∀ e : ↥E, e ^ p = 1 := fun e => Subtype.ext (hEexp e e.2)
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic Nat.prime_two K hK).2
  have hN : (OuterAutomorphisms.inner (StatedProj (StatedSp 3 K))).Normal :=
    OuterAutomorphisms.inner_normal _
  have hQ : ∀ γ : MulAut (StatedProj (StatedSp 3 K)), γ ^ p ∈ OuterAutomorphisms.inner (StatedProj (StatedSp 3 K)) →
      ∃ σ : K ≃+* K, γ * (fieldAut 3 K σ)⁻¹ ∈ OuterAutomorphisms.inner (StatedProj (StatedSp 3 K)) := by
    intro γ _
    obtain ⟨A', σ, rfl⟩ := (automorphism_generation (K := K) (r := 3) (by norm_num)).2 γ
    refine ⟨σ, ?_⟩
    rw [mul_inv_cancel_right, ← UnitaryHigher.spLinearAutGroup_eq_inner_of_charTwo]
    exact conjAut_mem_spLinearAutGroup A'
  have hbound : ∀ ρ : ↥E →* MulAut (StatedProj (StatedSp 3 K)),
      (∀ e : ↥E, ρ e ∈ OuterAutomorphisms.inner (StatedProj (StatedSp 3 K)) → e = 1) → Nat.card ↥E ≤ p :=
    fun ρ hρ => card_le_of_injective_mod_normal (OuterAutomorphisms.inner (StatedProj (StatedSp 3 K))) hcyc
      (fieldAut 3 K) hp hQ hEexp' ρ hρ
  have hinn := actP_mem_normal_of_bound φ hEI hWI hEcard h13.irreducible
    (OuterAutomorphisms.inner (StatedProj (StatedSp 3 K))) hN hbound
  have hpow : ∀ e : ↥E, (actP φ ⟨(e : G), hEI e.2⟩) ^ p = 1 := by
    intro e
    rw [← map_pow]
    have : (⟨(e : G), hEI e.2⟩ : ↥(Subgroup.normalizer (lieGenerated p E : Set G))) ^ p = 1 :=
      Subtype.ext (hEexp e e.2)
    rw [this, map_one]
  have hne : ∀ e : ↥E, e ≠ 1 → actP φ ⟨(e : G), hEI e.2⟩ ≠ 1 := by
    intro e he h1
    have hc := mem_centralizer_of_actP_eq_one φ h1
    have hmem : (e : G) ∈ E ⊓ Subgroup.centralizer (lieGenerated p E : Set G) := ⟨e.2, hc⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact he (Subtype.ext hmem)
  have hordall : ∀ e : ↥E, e ≠ 1 →
      orderOf (actP φ ⟨(e : G), hEI e.2⟩) = p := fun e he =>
    haveI : Fact p.Prime := ⟨hp⟩
    orderOf_eq_prime (hpow e) (hne e he)
  have hlift : ∀ e : ↥E, ∃ y : StatedSp 3 K, y ^ p = 1 ∧
      MulAut.conj (proj 3 K y) = actP φ ⟨(e : G), hEI e.2⟩ ∧ (e ≠ 1 → orderOf y = p) := by
    intro e
    by_cases he : e = 1
    · subst he
      refine ⟨1, one_pow _, ?_, fun h' => absurd rfl h'⟩
      have : (⟨((1 : ↥E) : G), hEI (1 : ↥E).2⟩ :
          ↥(Subgroup.normalizer (lieGenerated p E : Set G))) = 1 := Subtype.ext rfl
      rw [this, map_one, map_one, map_one]
    · have : Fact p.Prime := ⟨hp⟩
      have hord : orderOf (actP φ ⟨(e : G), hEI e.2⟩) = p := orderOf_eq_prime (hpow e) (hne e he)
      obtain ⟨⟨x, ⟨hxo, hxt⟩, -⟩, -⟩ := KCSpComm.exists_unique_lift (ℓ := 2) (f := f)
        Nat.prime_two hf (by norm_num : 2 ≤ 3) hK hq hp hp3 hp2
        (actP φ ⟨(e : G), hEI e.2⟩) (hinn e) hord
      refine ⟨x, ?_, hxt, fun _ => hxo⟩
      rw [← hxo]
      exact pow_orderOf_eq_one x
  choose x hxp hxc hxo using hlift
  refine ⟨x, hxp, hxc, fun e e' => ?_, hxo, hordall⟩
  have hcomm_act : actP φ ⟨(e : G), hEI e.2⟩ * actP φ ⟨(e' : G), hEI e'.2⟩ =
      actP φ ⟨(e' : G), hEI e'.2⟩ * actP φ ⟨(e : G), hEI e.2⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    have hcomm : (e : G) * e' = e' * e := congrArg Subtype.val (hE.is_comm.comm e e')
    exact Subtype.ext hcomm
  have h1 : proj 3 K (x e * x e' * (x e)⁻¹) = proj 3 K (x e') := by
    apply hTinj
    simp only [map_mul, map_inv, hxc]
    rw [hcomm_act, mul_inv_cancel_right]
  have h2 : x e * x e' * (x e)⁻¹ = x e' := by
    refine CFSG.RankThree.Classical.eq_of_map_eq_of_pow_eq_one_of_coprime (proj 3 K)
      KCSpFull.ker_proj_le_center (KCSpFull.coprime_card_ker_proj (by norm_num) hp hp2)
      (a := 1) (b := 1) ?_ ?_ h1
    · rw [pow_one, conj_pow, hxp e', mul_one, mul_inv_cancel]
    · rw [pow_one, hxp e']
  exact (mul_inv_eq_iff_eq_mul.1 h2)

end CFSG.RankThree.PartOne.S15K
