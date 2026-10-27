module

public import CFSG.Quasithin.Background.RonanH44SigNfs
public import CFSG.Quasithin.Background.RonanH44SigConj
public import CFSG.Quasithin.Background.RonanH44SigCent
public import CFSG.Quasithin.Background.RonanH44Orth
public import CFSG.Quasithin.Background.RonanH44NfsTr

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3
  CFSG.Quasithin.SteinbergCB Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

private theorem six_exists_y (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {i : MulAut (HMod n K)} (hi : i ∈ norm hK) (hi2 : orderOf i = 2) (hiL : i ∉ img hK) :
    ∃ y : MulAut (HMod n K), y ∈ norm hK ∧ i = y * sig n K * y⁻¹ ∧
      ∀ (c : K) (v w : HMod n K), mat w = c • mat v → mat (y w) = c • mat (y v) := by
  have hii : i * i = 1 := by
    have h := pow_orderOf_eq_one i
    rwa [hi2, pow_two] at h
  obtain ⟨B, hB⟩ := exists_conj_sig hn hK hi hii hiL
  exact ⟨rhoT hK B, rhoT_mem_norm hK B, hB, fun c v w hvw => by
    rw [mat_rhoT, mat_rhoT, hvw, tw_smul]⟩

private theorem six_rk_fixV (y : MulAut (HMod n K)) :
    rk ↥(fixV (Subgroup.zpowers (y * sig n K * y⁻¹))) =
      rk ↥(fixV (Subgroup.zpowers (sig n K))) := by
  unfold rk
  rw [card_fixV_zpowers_conj]

private theorem six_rkIdx_fixV (y : MulAut (HMod n K)) :
    rkIdx (fixV (Subgroup.zpowers (y * sig n K * y⁻¹))) =
      rkIdx (fixV (Subgroup.zpowers (sig n K))) := by
  rw [fixV_zpowers_conj, E3.rkIdx_map_equiv]

private theorem six_rk_commV (y : MulAut (HMod n K)) :
    rk ↥(commV (Subgroup.zpowers (y * sig n K * y⁻¹))) =
      rk ↥(commV (Subgroup.zpowers (sig n K))) := by
  unfold rk
  rw [commV_zpowers_conj_eq, Subgroup.card_map_of_injective (f := y.toMonoidHom) y.injective]

private theorem six_b (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hMN : M ≤ norm hK) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) (hiM : y * sig n K * y⁻¹ ∈ M) :
    M ⊓ centSub (fixV (Subgroup.zpowers (y * sig n K * y⁻¹))) =
      Subgroup.zpowers (y * sig n K * y⁻¹) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM, hxC⟩ := hx
    have hxC' : ∀ v ∈ fixV (Subgroup.zpowers (y * sig n K * y⁻¹)), x v = v :=
      mem_centSub.1 hxC
    have hx' : y⁻¹ * x * y ∈ norm hK := mul_mem (mul_mem (inv_mem hy) (hMN hxM)) hy
    have hfix : ∀ v ∈ fixV (Subgroup.zpowers (sig n K)), (y⁻¹ * x * y) v = v := by
      intro v hv
      have hyv : y v ∈ fixV (Subgroup.zpowers (y * sig n K * y⁻¹)) := by
        rw [fixV_zpowers_conj, nfsTr_mem_map_iff, MulAut.inv_apply_self]
        exact hv
      rw [MulAut.mul_apply, MulAut.mul_apply, hxC' _ hyv, MulAut.inv_apply_self]
    have hxe : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
    rcases eq_one_or_eq_sig_of_fix hn hK hx' hfix with h1 | h1
    · rw [hxe, h1, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [hxe, h1]
      exact Subgroup.mem_zpowers _
  · exact Subgroup.zpowers_le.2 (Subgroup.mem_inf.2
      ⟨hiM, mem_centSub.2 fun v hv => mem_fixV_zpowers_iff_apply.1 hv⟩)

private theorem six_mem_CL (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) (g : MulAut (HMod n K)) :
    g ∈ img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))) ↔
      y⁻¹ * g * y ∈ img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))) := by
  have hL : g ∈ img hK ↔ y⁻¹ * g * y ∈ img hK := by
    have h := Subgroup.mem_normalizer_iff.1 hy (y⁻¹ * g * y)
    have e : y * (y⁻¹ * g * y) * y⁻¹ = g := by group
    rw [e] at h
    exact h.symm
  have hC : g ∈ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))) ↔
      y⁻¹ * g * y ∈ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))) := by
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    have e1 : sig n K * (y⁻¹ * g * y) = y⁻¹ * (y * sig n K * y⁻¹ * g) * y := by group
    have e2 : y⁻¹ * g * y * sig n K = y⁻¹ * (g * (y * sig n K * y⁻¹)) * y := by group
    rw [e1, e2, mul_left_inj, mul_right_inj]
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr hL hC

private theorem six_CL_eq (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) :
    img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))) =
      (img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K)))).map
        (MulAut.conj y).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨y⁻¹ * g * y, (six_mem_CL hK hy g).1 h, ?_⟩
    show MulAut.conj y (y⁻¹ * g * y) = g
    rw [MulAut.conj_apply]
    group
  · rintro ⟨z, hz, hzg⟩
    rw [← hzg]
    refine (six_mem_CL hK hy _).2 ?_
    have e : y⁻¹ * MulAut.conj y z * y = z := by
      rw [MulAut.conj_apply]
      group
    show y⁻¹ * MulAut.conj y z * y ∈ _
    rw [e]
    exact hz

private theorem six_iso (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) :
    Nonempty (↥(img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K)))) ≃*
      SL(3, Fq n K)) := by
  have hR : (rhoF hK).range =
      img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K))) := by
    ext r
    rw [Subgroup.mem_inf]
    exact mem_range_rhoF_iff hn hK r
  have e₁ : SL(3, Fq n K) ≃*
      ↥(img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K)))) :=
    (MonoidHom.ofInjective (rhoF_injective hn hK)).trans (MulEquiv.subgroupCongr hR)
  have e₂ : ↥(img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K)))) ≃*
      ↥((img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K)))).map
        (MulAut.conj y).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ (MulAut.conj y).toMonoidHom (MulAut.conj y).injective
  have e₃ : ↥((img hK ⊓ Subgroup.centralizer ({sig n K} : Set (MulAut (HMod n K)))).map
        (MulAut.conj y).toMonoidHom) ≃*
      ↥(img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K)))) :=
    MulEquiv.subgroupCongr (six_CL_eq hK hy).symm
  exact ⟨(e₁.trans (e₂.trans e₃)).symm⟩

private theorem six_isFixed (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    IsFixedFieldEmb (n := n) (scalF n K) := by
  refine ⟨card_Fq hn hK, fun c => ⟨fun hc => ⟨⟨c, mem_frobFixed.2 hc⟩, rfl⟩, ?_⟩⟩
  rintro ⟨f, rfl⟩
  exact bar_scalF f

private theorem six_nfs_comm (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK)
    (hyl : ∀ (c : Fq n K) (v w : HMod n K), mat w = scalF n K c • mat v →
      mat (y w) = scalF n K c • mat (y v)) :
    NineFaithSec (scalF n K)
      (img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))))
      (commV (Subgroup.zpowers (y * sig n K * y⁻¹))) ⊥ 3 := by
  have h := nfs_transport (scalF n K) bar_scalF y hyl (nfs_sig_comm hn hK)
  rw [← six_CL_eq hK hy, ← commV_zpowers_conj_eq (sig n K) y, Subgroup.map_bot] at h
  exact h

private theorem six_nfs_fix (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK)
    (hyl : ∀ (c : Fq n K) (v w : HMod n K), mat w = scalF n K c • mat v →
      mat (y w) = scalF n K c • mat (y v)) :
    NineFaithSec (scalF n K)
      (img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))))
      (fixV (Subgroup.zpowers (y * sig n K * y⁻¹)))
      (commV (Subgroup.zpowers (y * sig n K * y⁻¹))) 3 := by
  have h := nfs_transport (scalF n K) bar_scalF y hyl (nfs_sig_fix hn hK)
  rw [← six_CL_eq hK hy, ← fixV_zpowers_conj y (sig n K),
    ← commV_zpowers_conj_eq (sig n K) y] at h
  exact h

private theorem six_nfs_top (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK)
    (hyl : ∀ (c : Fq n K) (v w : HMod n K), mat w = scalF n K c • mat v →
      mat (y w) = scalF n K c • mat (y v)) :
    NineFaithSec (scalF n K)
      (img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))))
      ⊤ (fixV (Subgroup.zpowers (y * sig n K * y⁻¹))) 3 := by
  have h := nfs_transport (scalF n K) bar_scalF y hyl (nfs_sig_top hn hK)
  rw [← six_CL_eq hK hy, ← fixV_zpowers_conj y (sig n K),
    Subgroup.map_top_of_surjective y.toMonoidHom y.surjective] at h
  exact h

private theorem six_e1 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) :
    ∀ g ∈ img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))),
      (∀ u ∈ commV (Subgroup.zpowers (y * sig n K * y⁻¹)), g u = u) → g = 1 := by
  intro g hg hfix
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.1
    ((mem_range_rhoF_iff hn hK _).2 ((six_mem_CL hK hy g).1 hg))
  have hcomm : ∀ u ∈ commV (Subgroup.zpowers (sig n K)), rhoF hK h u = u := by
    intro u hu
    have hyu : y u ∈ commV (Subgroup.zpowers (y * sig n K * y⁻¹)) := by
      rw [commV_zpowers_conj_eq, nfsTr_mem_map_iff, MulAut.inv_apply_self]
      exact hu
    rw [hh, MulAut.mul_apply, MulAut.mul_apply, hfix _ hyu, MulAut.inv_apply_self]
  have hg1 : y⁻¹ * g * y = 1 := by
    rw [← hh, faith_comm hn hK hcomm, map_one]
  have e : g = y * (y⁻¹ * g * y) * y⁻¹ := by group
  rw [e, hg1, mul_one, mul_inv_cancel]

private theorem six_e2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) :
    ∀ g ∈ img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))),
      (∀ u ∈ fixV (Subgroup.zpowers (y * sig n K * y⁻¹)),
        g u * u⁻¹ ∈ commV (Subgroup.zpowers (y * sig n K * y⁻¹))) → g = 1 := by
  intro g hg hfix
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.1
    ((mem_range_rhoF_iff hn hK _).2 ((six_mem_CL hK hy g).1 hg))
  have hcomm : ∀ u ∈ fixV (Subgroup.zpowers (sig n K)),
      rhoF hK h u * u⁻¹ ∈ commV (Subgroup.zpowers (sig n K)) := by
    intro u hu
    have hyu : y u ∈ fixV (Subgroup.zpowers (y * sig n K * y⁻¹)) := by
      rw [fixV_zpowers_conj, nfsTr_mem_map_iff, MulAut.inv_apply_self]
      exact hu
    have hw := hfix _ hyu
    rw [commV_zpowers_conj_eq, nfsTr_mem_map_iff] at hw
    have e : rhoF hK h u * u⁻¹ = y⁻¹ (g (y u) * (y u)⁻¹) := by
      rw [hh, MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [e]
    exact hw
  have hg1 : y⁻¹ * g * y = 1 := by
    rw [← hh, faith_fix hn hK hcomm, map_one]
  have e : g = y * (y⁻¹ * g * y) * y⁻¹ := by group
  rw [e, hg1, mul_one, mul_inv_cancel]

private theorem six_e3 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {y : MulAut (HMod n K)}
    (hy : y ∈ norm hK) :
    ∀ g ∈ img hK ⊓ Subgroup.centralizer ({y * sig n K * y⁻¹} : Set (MulAut (HMod n K))),
      (∀ u : HMod n K, g u * u⁻¹ ∈ fixV (Subgroup.zpowers (y * sig n K * y⁻¹))) → g = 1 := by
  intro g hg hfix
  obtain ⟨h, hh⟩ := MonoidHom.mem_range.1
    ((mem_range_rhoF_iff hn hK _).2 ((six_mem_CL hK hy g).1 hg))
  have hcomm : ∀ u : HMod n K, rhoF hK h u * u⁻¹ ∈ fixV (Subgroup.zpowers (sig n K)) := by
    intro u
    have hw := hfix (y u)
    rw [fixV_zpowers_conj, nfsTr_mem_map_iff] at hw
    have e : rhoF hK h u * u⁻¹ = y⁻¹ (g (y u) * (y u)⁻¹) := by
      rw [hh, MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [e]
    exact hw
  have hg1 : y⁻¹ * g * y = 1 := by
    rw [← hh, faith_top hn hK hcomm, map_one]
  have e : g = y * (y⁻¹ * g * y) * y⁻¹ := by group
  rw [e, hg1, mul_one, mul_inv_cancel]

theorem part6 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {M : Subgroup (MulAut (HMod n K))} (hLM : img hK ≤ M) (hMN : M ≤ norm hK) :
    ∀ i ∈ M, i ∉ img hK → orderOf i = 2 →
      rk ↥(fixV (Subgroup.zpowers i)) = 6 * n ∧
      M ⊓ centSub (fixV (Subgroup.zpowers i)) = Subgroup.zpowers i ∧
      (∃ (F : Type) (_ : Field F), Nat.card F = 2 ^ n ∧
        Nonempty (↥(img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K)))) ≃*
          SL(3, F))) ∧
      rk ↥(commV (Subgroup.zpowers i)) = 3 * n ∧ rkIdx (fixV (Subgroup.zpowers i)) = 3 * n ∧
      (∀ g ∈ img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))),
        (∀ u ∈ commV (Subgroup.zpowers i), g u = u) → g = 1) ∧
      (∀ g ∈ img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))),
        (∀ u ∈ fixV (Subgroup.zpowers i), g u * u⁻¹ ∈ commV (Subgroup.zpowers i)) → g = 1) ∧
      (∀ g ∈ img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))),
        (∀ u : HMod n K, g u * u⁻¹ ∈ fixV (Subgroup.zpowers i)) → g = 1) ∧
      ∃ (F : Type) (_ : Field F) (scalar : F →+* K),
        IsFixedFieldEmb (n := n) scalar ∧
        Nonempty (↥(img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K)))) ≃*
          SL(3, F)) ∧
        NineFaithSec scalar
          (img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))))
          (commV (Subgroup.zpowers i)) ⊥ 3 ∧
        NineFaithSec scalar
          (img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K))))
          (fixV (Subgroup.zpowers i)) (commV (Subgroup.zpowers i)) 3 ∧
        NineFaithSec scalar
          (img hK ⊓ Subgroup.centralizer ({i} : Set (MulAut (HMod n K)))) ⊤
          (fixV (Subgroup.zpowers i)) 3 := by
  intro i hiM hiL hi2
  obtain ⟨y, hy, rfl, hylin⟩ := six_exists_y hn hK (hMN hiM) hi2 hiL
  have hyl : ∀ (c : Fq n K) (v w : HMod n K), mat w = scalF n K c • mat v →
      mat (y w) = scalF n K c • mat (y v) :=
    fun c v w h => hylin (scalF n K c) v w h
  refine ⟨?_, six_b hn hK hMN hy hiM, ⟨Fq n K, inferInstance, card_Fq hn hK, six_iso hn hK hy⟩,
    ?_, ?_, six_e1 hn hK hy, six_e2 hn hK hy, six_e3 hn hK hy,
    Fq n K, inferInstance, scalF n K, six_isFixed hn hK, six_iso hn hK hy,
    six_nfs_comm hn hK hy hyl, six_nfs_fix hn hK hy hyl, six_nfs_top hn hK hy hyl⟩
  · rw [six_rk_fixV]
    exact rk_fixV_sig hn hK
  · rw [six_rk_commV]
    exact rk_commV_sig hn hK
  · rw [six_rkIdx_fixV]
    exact rkIdx_fixV_sig hn hK

end CFSG.Quasithin.RonanH44
