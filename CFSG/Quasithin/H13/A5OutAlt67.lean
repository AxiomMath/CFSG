module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.Background.Sp4InfAut6
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.QuasithinUnique.Ch1 Equiv

@[expose] noncomputable def autQuotCenter (K : Type*) [Group K] :
    MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun β := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) β
    (Subgroup.characteristic_iff_map_eq.mp inferInstance β)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' β γ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl

theorem mem_of_index_two_of_odd_pow {X : Type*} [Group X] {H : Subgroup X} (h : H.index = 2)
    {g : X} {m : ℕ} (hm : Odd m) (hg : g ^ m = 1) : g ∈ H := by
  obtain ⟨k, rfl⟩ := hm
  have hsq : g ^ 2 ∈ H := by
    rw [pow_two]
    exact Subgroup.mul_self_mem_of_index_two h g
  have hk : (g ^ 2) ^ k ∈ H := H.pow_mem hsq k
  have e : g ^ (2 * k + 1) = (g ^ 2) ^ k * g := by rw [pow_succ, pow_mul]
  rw [e] at hg
  exact ((Subgroup.mul_mem_iff_of_index_two h).mp (hg ▸ H.one_mem)).mp hk

theorem sign_eq_one_of_pow_odd {n : ℕ} {σ : Perm (Fin n)} {m : ℕ} (hm : Odd m)
    (hσ : σ ^ m = 1) : Perm.sign σ = 1 := by
  have h1 : Perm.sign σ ^ m = 1 := by rw [← map_pow, hσ, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h | h
  · exact h
  · rw [h, hm.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem exists_perm_of_odd {n : ℕ} (hn : n = 6 ∨ n = 7) (α : MulAut (alternatingGroup (Fin n)))
    {m : ℕ} (hm : Odd m) (hαm : α ^ m = 1) :
    ∃ σ : Perm (Fin n), Perm.sign σ = 1 ∧
      ∀ a : alternatingGroup (Fin n), ((α a : alternatingGroup (Fin n)) : Perm (Fin n)) =
        σ * a * σ⁻¹ := by
  rcases hn with rfl | rfl
  · have hα : α ∈ Sp4Inf.conjAlt6.range :=
      mem_of_index_two_of_odd_pow Sp4Inf.index_range_conjAlt6 hm hαm
    obtain ⟨σ, rfl⟩ := hα
    have hσm : σ ^ m = 1 := Sp4Inf.conjAlt6_injective (by rw [map_pow, hαm, map_one])
    exact ⟨σ, sign_eq_one_of_pow_odd hm hσm, fun a => Sp4Inf.coe_conjAlt6 σ a⟩
  · have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by norm_num) (by norm_num)
    obtain ⟨σ, rfl⟩ := hbij.2 α
    have hσm : σ ^ m = 1 := hbij.1 (by rw [map_pow, hαm, map_one])
    exact ⟨σ, sign_eq_one_of_pow_odd hm hσm, fun a => MulAut.conjNormal_apply σ a⟩

variable {G : Type} [Group G]

theorem exists_conj_of_odd {K : Subgroup G} (hK : Group.IsPerfect K) {n : ℕ}
    (hn : n = 6 ∨ n = 7) (φ : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hodd : Odd (orderOf g)) :
    ∃ l ∈ K, ∀ x ∈ K, g * x * g⁻¹ = l * x * l⁻¹ := by
  set N := Subgroup.normalizer (K : Set G) with hN
  let Φ : ↥N →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr φ).toMonoidHom.comp ((autQuotCenter ↥K).comp K.normalizerMonoidHom)
  have hΦ : ∀ (h : ↥N) (x : ↥K), φ (QuotientGroup.mk (K.normalizerMonoidHom h x)) =
      Φ h (φ (QuotientGroup.mk x)) := by
    intro h x
    simp only [Φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  have hΦm : Φ ⟨g, hg⟩ ^ orderOf g = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥N) ^ orderOf g = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  obtain ⟨σ, hσs, hσ⟩ := exists_perm_of_odd hn (Φ ⟨g, hg⟩) hodd hΦm
  obtain ⟨q, hq⟩ := φ.surjective ⟨σ, Perm.mem_alternatingGroup.mpr hσs⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  have key : (QuotientGroup.mk' (Subgroup.center ↥K)).comp
        (K.normalizerMonoidHom ⟨g, hg⟩).toMonoidHom =
      (QuotientGroup.mk' (Subgroup.center ↥K)).comp (MulAut.conj l).toMonoidHom := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply]
    apply φ.injective
    apply Subtype.ext
    rw [hΦ, hσ, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, map_mul, map_mul, map_inv, hq]
    rfl
  have : Group.IsPerfect ↥K := hK
  have hlift := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
    (π := QuotientGroup.mk' (Subgroup.center ↥K)) (by rw [QuotientGroup.ker_mk']) key
  refine ⟨l, l.2, fun x hx => ?_⟩
  have h1 := congrArg (fun f : ↥K →* ↥K => ((f ⟨x, hx⟩ : ↥K) : G)) hlift
  simpa using h1

theorem inducesInner_of_odd {K : Subgroup G} (hK : Group.IsPerfect K) {n : ℕ}
    (hn : n = 6 ∨ n = 7) (φ : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) (hodd : Odd (orderOf g)) : InducesInner g K := by
  obtain ⟨l, hl, h⟩ := exists_conj_of_odd hK hn φ (Subgroup.inv_mem _ hg)
    (by rwa [orderOf_inv])
  refine ⟨l⁻¹, K.inv_mem hl, fun x hx => ?_⟩
  rw [inv_inv]
  simpa using h x hx

end CFSG.Quasithin.H13.A5
