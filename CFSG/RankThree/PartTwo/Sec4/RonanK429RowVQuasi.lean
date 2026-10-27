module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowVTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429CfgTypes
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof429

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

namespace RowV

@[expose] def CentQuasi {S : Type} [Group S] (s : S) (N₁ N₂ : ℕ) : Prop :=
  Nat.card (Subgroup.centralizer ({s} : Set S)) ∣ N₁ ∨
    ∃ H : Subgroup S, H ≤ Subgroup.centralizer ({s} : Set S) ∧
      (∀ a ∈ Subgroup.centralizer ({s} : Set S), ∀ b ∈ Subgroup.centralizer ({s} : Set S),
        ⁅a, b⁆ ∈ H) ∧
      IsQuasisimple H ∧ (∃ z ∈ H, z ≠ 1 ∧ z ^ 3 = 1 ∧ ∀ h ∈ H, h * z = z * h) ∧
      Nat.card H ∣ N₂

theorem mem_centralizer_map_iff {S T : Type} [Group S] [Group T] (φ : S ≃* T) {s x : S} :
    φ x ∈ Subgroup.centralizer ({φ s} : Set T) ↔ x ∈ Subgroup.centralizer ({s} : Set S) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    ← map_mul, ← map_mul]
  exact φ.injective.eq_iff

theorem CentQuasi.of_mulEquiv {S T : Type} [Group S] [Group T] (φ : S ≃* T) {s : S}
    {N₁ N₂ : ℕ} (h : CentQuasi (φ s) N₁ N₂) : CentQuasi s N₁ N₂ := by
  rcases h with h | ⟨H, hH, hcomm, hq, ⟨z, hz, hz1, hz3, hzc⟩, hcard⟩
  · left
    rwa [card_centralizer_congr φ s]
  · right
    have hmap : H.comap φ.toMonoidHom = H.map φ.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm φ H
    let e : H ≃* H.comap φ.toMonoidHom :=
      (MulEquiv.subgroupMap φ.symm H).trans (MulEquiv.subgroupCongr hmap.symm)
    refine ⟨H.comap φ.toMonoidHom, ?_, ?_, ?_, ⟨φ.symm z, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro x hx
      exact (mem_centralizer_map_iff φ).mp (hH hx)
    · intro a ha b hb
      show φ ⁅a, b⁆ ∈ H
      rw [map_commutatorElement]
      exact hcomm _ ((mem_centralizer_map_iff φ).mpr ha) _ ((mem_centralizer_map_iff φ).mpr hb)
    · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq
    · show φ (φ.symm z) ∈ H
      rwa [MulEquiv.apply_symm_apply]
    · intro h1
      exact hz1 (by rw [← MulEquiv.apply_symm_apply φ z, h1, map_one])
    · rw [← map_pow, hz3, map_one]
    · intro h hh
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hzc _ hh
    · rwa [Nat.card_congr e.toEquiv.symm]

theorem noCfgS429_of_inner_quasi {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hin : ∀ τ : MulAut S, τ ^ 3 = 1 → τ ∈ (MulAut.conj : S →* MulAut S).range)
    {N₁ N₂ B : ℕ}
    (hC : ∀ E : Subgroup S, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ∀ s ∈ E, s ≠ 1 → CentQuasi s N₁ N₂)
    (hN : 0 < N₁) (hB : 3 * N₁ < B ^ 3 * ((B ^ 2 - 1) * (B ^ 3 - 1)))
    (hL : ∀ q < B, q % 3 = 1 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) ∣ 3 * N₁)
    (hU : ∀ q < B, q % 3 = 2 → q ≠ 2 → ¬ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) ∣ 3 * N₁)
    (h7 : ¬ 2520 ∣ N₁) (h12 : ¬ 95040 ∣ N₁) (h22 : ¬ 443520 ∣ N₁) (hJ : ¬ 604800 ∣ N₁)
    (h12' : ¬ 95040 ∣ N₂) (h22' : ¬ 443520 ∣ N₂) (hJ' : ¬ 604800 ∣ N₂) :
    NoCfgS429 S := by
  intro A σ K hc
  have hconj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun τ : MulAut S => τ g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * x = x * g * x⁻¹ * x := by rw [h]
        _ = x * g := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have h3 : σ ^ 3 = 1 := hc.isE27.1.2 σ hc.mem
  obtain ⟨s, rfl⟩ := hin σ h3
  have hs1 : s ≠ 1 := fun h => hc.ne_one (by rw [h, map_one])
  set E := A.comap (MulAut.conj : S →* MulAut S) with hEdef
  have hAle : A ≤ (MulAut.conj : S →* MulAut S).range := fun a ha =>
    hin a (hc.isE27.1.2 a ha)
  have hEA : E.map (MulAut.conj : S →* MulAut S) = A := Subgroup.map_comap_eq_self hAle
  have hE27 : Nat.card E = 27 := by
    rw [← hc.isE27.2, ← hEA, Subgroup.card_map_of_injective hconj]
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hconj ?_)⟩⟩, fun x hx => hconj ?_⟩
    · have := hc.isE27.1.1.is_comm.comm ⟨MulAut.conj (x : S), x.2⟩ ⟨MulAut.conj (y : S), y.2⟩
      have h := congrArg Subtype.val this
      simpa only [Subgroup.coe_mul, map_mul] using h
    · rw [map_pow, map_one]
      exact hc.isE27.1.2 _ hx
  have hsE : s ∈ E := hc.mem
  haveI : Group.IsPerfect K := hc.isPerfect
  have hle : K ≤ Subgroup.centralizer ({s} : Set S) := by
    rw [← autFix_conj_eq_centralizer]
    exact hc.le_autFix
  rcases hC E hEab hE27 s hsE hs1 with hcard | ⟨H, hH, hcomm, hq, ⟨z, hz, hz1, hz3, hzc⟩, hcard⟩
  · have hK : Nat.card K ∣ N₁ := (Subgroup.card_dvd_of_le hle).trans hcard
    exact not_isType429_of_dvd hN ((Subgroup.card_quotient_dvd_card _).trans hK) hB hL hU h7 h12
      h22 hJ hc.isType
  ·
    have hKH : K ≤ H := by
      rw [← Subgroup.commutator_eq_self (H := K)]
      exact Subgroup.commutator_le.mpr fun a ha b hb => hcomm a (hle ha) b (hle hb)
    by_cases hK1 : Nontrivial K
    swap
    · rw [not_nontrivial_iff_subsingleton] at hK1
      exact not_isType429_of_dvd hN ((Subgroup.card_quotient_dvd_card _).trans
        (by rw [Nat.card_unique]; exact one_dvd _)) hB hL hU h7 h12 h22 hJ hc.isType
    have hHfix : H ≤ autFix (MulAut.conj s) := by
      rw [autFix_conj_eq_centralizer]
      exact hH
    have hsn : (K.subgroupOf H).IsSubnormal := by
      have h := hc.isSubnormal.comap (Subgroup.inclusion hHfix)
      have heq : (K.subgroupOf (autFix (MulAut.conj s))).comap (Subgroup.inclusion hHfix) =
          K.subgroupOf H := by
        ext x
        simp [Subgroup.mem_subgroupOf]
      rwa [heq] at h
    have hKeq : K = H := Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hKH hq hc.isPerfect hK1 hsn
    have hzK : z ∈ K := hKeq ▸ hz
    set X := K ⧸ CFSG.pCore 2 K with hX
    have hXdvd : Nat.card X ∣ N₂ :=
      (Subgroup.card_quotient_dvd_card _).trans (hKeq ▸ hcard)
    have hXc : Subgroup.center X = ⊥ := by
      have hnt : Nontrivial X := by
        by_contra hnt
        rw [not_nontrivial_iff_subsingleton] at hnt
        exact not_isType429_of_dvd hN (by rw [Nat.card_unique]; exact one_dvd _) hB hL hU h7 h12
          h22 hJ hc.isType
      rcases hc.isType with ⟨p, e, hp, he, h⟩ | h | h | h | h
      · exact center_eq_bot_of_isoLThreePi he h
      · obtain ⟨φ⟩ := h
        exact center_eq_bot_of_mulEquiv φ Sec13.isPerfect_center_alt7.2
      · obtain ⟨φ⟩ := h
        exact absurd (((Nat.card_congr φ.toEquiv).trans KS14.card_nativeM12) ▸ hXdvd) h12'
      · obtain ⟨φ⟩ := h
        exact absurd (((Nat.card_congr φ.toEquiv).trans KS14.card_nativeM22) ▸ hXdvd) h22'
      · obtain ⟨φ⟩ := h
        exact absurd (((Nat.card_congr φ.toEquiv).trans KS14.card_nativeJ2) ▸ hXdvd) hJ'
    have hzc' : (QuotientGroup.mk (⟨z, hzK⟩ : K) : X) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact hzc y (hKeq ▸ y.2)
    rw [hXc, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzc'
    have h2 : IsPGroup 2 (CFSG.pCore 2 K) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := h2 ⟨⟨z, hzK⟩, hzc'⟩
    have hz2 : z ^ 2 ^ k = 1 := by
      have := congrArg (fun x : CFSG.pCore 2 K => ((x : K) : S)) hk
      simpa using this
    have hd : orderOf z ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hz2) (orderOf_dvd_of_pow_eq_one hz3)
    have hg : Nat.gcd (2 ^ k) 3 = 1 :=
      Nat.Coprime.pow_left k (by norm_num)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hz1 hd

end RowV

end CFSG.RankThree.PartTwo.Sec4.RonanK429
