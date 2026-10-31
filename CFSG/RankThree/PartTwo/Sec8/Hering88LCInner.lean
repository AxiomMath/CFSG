module

public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem perfectResidual_normal (M : Type*) [Group M] : (perfectResidual M).Normal := by
  refine ⟨fun x hx g => ?_⟩
  unfold perfectResidual at hx ⊢
  rw [Subgroup.mem_iInf] at hx ⊢
  exact fun n => (derivedSeries_normal M n).conj_mem x (hx n) g

theorem inSubgroup_perfectResidual_le' (M : Subgroup G) : inSubgroup perfectResidual M ≤ M := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem theta_inf_le_theta' {H K : Subgroup G} (hKH : K ≤ H) :
    inSubgroup (aschbacherSolvableCore 3) H ⊓ K ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨hs, h3⟩ := Sec6.theta_solvable_and_not_dvd H
  set N := inSubgroup (aschbacherSolvableCore 3) H ⊓ K with hN
  have hKN : K ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Sec6.le_normalizer_theta H (hKH hx), Subgroup.le_normalizer hx⟩
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : N ≤ inSubgroup (aschbacherSolvableCore 3) H))
      (Subgroup.inclusion_injective _)
  have hN3 : ¬ 3 ∣ Nat.card N := fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact Sec6.le_theta_of_normal inf_le_right hKN hNsol hN3

noncomputable abbrev barAut (Y : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) : MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
  Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨x, hx⟩)

theorem barAut_mk {Y : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (Y : Set G)) {y : G}
    (hy : y ∈ Y) (hxy : x * y * x⁻¹ ∈ Y) :
    barAut Y x hx (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨y, hy⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨x * y * x⁻¹, hxy⟩ :=
  rfl

theorem conj_mem_of_mem_normalizer {Y : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (Y : Set G)) (hy : y ∈ Y) : x * y * x⁻¹ ∈ Y :=
  (Subgroup.mem_normalizer_iff.mp hx y).mp hy

theorem barAut_commute {Y : Subgroup G} {x y : G} (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (hy : y ∈ Subgroup.normalizer (Y : Set G)) (hxy : x * y = y * x) :
    barAut Y x hx * barAut Y y hy = barAut Y y hy * barAut Y x hx := by
  have h : (⟨x, hx⟩ : Subgroup.normalizer (Y : Set G)) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    Subtype.ext hxy
  change ((Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)) ⟨x, hx⟩ *
      ((Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)) ⟨y, hy⟩ =
    ((Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)) ⟨y, hy⟩ *
      ((Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)) ⟨x, hx⟩
  rw [← map_mul, ← map_mul, h]

theorem barAut_pow_three {Y : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (Y : Set G))
    (hx3 : x ^ 3 = 1) : barAut Y x hx ^ 3 = 1 := by
  have h : (⟨x, hx⟩ : Subgroup.normalizer (Y : Set G)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  change ((Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)) ⟨x, hx⟩ ^ 3 = 1
  rw [← map_pow, h, map_one]

theorem barAut_mk_of_commute {Y : Subgroup G} {d y : G} (hd : d ∈ Subgroup.normalizer (Y : Set G))
    (hy : y ∈ Y) (hyd : y ∈ Subgroup.centralizer ({d} : Set G)) :
    barAut Y d hd (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨y, hy⟩) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨y, hy⟩ := by
  rw [barAut_mk hd hy (conj_mem_of_mem_normalizer hd hy)]
  congr 1
  apply Subtype.ext
  change d * y * d⁻¹ = y
  rw [(Subgroup.mem_centralizer_singleton_iff.mp hyd).symm, mul_inv_cancel_right]

theorem eq_of_conj_eq {Q : Type*} [Group Q] (hZ : ∀ z : Q, (∀ y : Q, z * y = y * z) → z = 1)
    {g g' : Q} (h : MulAut.conj g = MulAut.conj g') : g = g' := by
  have hz : g'⁻¹ * g = 1 := hZ _ fun y => by
    have e := congrArg (fun φ : MulAut Q => φ y) h
    simp only [MulAut.conj_apply] at e
    calc g'⁻¹ * g * y = g'⁻¹ * (g * y * g⁻¹) * g := by group
      _ = g'⁻¹ * (g' * y * g'⁻¹) * g := by rw [e]
      _ = y * (g'⁻¹ * g) := by group
  calc g = g' * (g'⁻¹ * g) := by group
    _ = g' := by rw [hz, mul_one]

theorem barCentralizer_eq_centralizer {Y : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (Y : Set G)) {g : Y ⧸ aschbacherSolvableCore 3 Y}
    (hg : barAut Y d hd = MulAut.conj g) :
    barCentralizer (Subgroup.zpowers d) Y = Subgroup.centralizer ({g} : Set _) := by
  ext z
  rw [KFacts.mem_barCentralizer_zpowers_iff hd, Subgroup.mem_centralizer_singleton_iff]
  change barAut Y d hd z = z ↔ _
  rw [hg, MulAut.conj_apply]
  constructor
  · intro h
    calc z * g = g * z * g⁻¹ * g := by rw [h]
      _ = g * z := by group
  · intro h
    rw [← h]
    group

theorem mem_residual_of_mem_imageModTheta {Y : Subgroup G} {d w : G} (hwY : w ∈ Y)
    (hwd : w ∈ Subgroup.centralizer ({d} : Set G))
    (himg : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨w, hwY⟩ ∈
      imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))))
    {e : ℕ} (hwe : w ^ 3 ^ e = 1) :
    w ∈ inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) := by
  classical
  set M := Y ⊓ Subgroup.centralizer ({d} : Set G) with hM
  obtain ⟨u', hu', hu'w⟩ := himg
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_subgroupOf.mp hu'
  have hθ : u'⁻¹ * ⟨w, hwY⟩ ∈ aschbacherSolvableCore 3 Y := QuotientGroup.eq.mp hu'w
  have hwM : w ∈ M := ⟨hwY, hwd⟩
  haveI : (perfectResidual M).Normal := perfectResidual_normal M
  set π := QuotientGroup.mk' (perfectResidual M) with hπ
  set θM : M := v⁻¹ * ⟨w, hwM⟩ with hθM
  have hπv : π v = 1 := (QuotientGroup.eq_one_iff _).mpr hv
  have hπw : π ⟨w, hwM⟩ = π θM := by rw [hθM, map_mul, map_inv, hπv, inv_one, one_mul]
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
  have hθval : ((θM : M) : G) = ((u'⁻¹ * ⟨w, hwY⟩ : Y) : G) := by
    rw [hθM, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    congr 2
  have hord : orderOf θM = orderOf (⟨u'⁻¹ * ⟨w, hwY⟩, hθ⟩ : aschbacherSolvableCore 3 Y) := by
    rw [← Subgroup.orderOf_coe θM, hθval]
    exact (Subgroup.orderOf_coe (u'⁻¹ * ⟨w, hwY⟩ : Y)).trans
      (Subgroup.orderOf_coe (⟨u'⁻¹ * ⟨w, hwY⟩, hθ⟩ : aschbacherSolvableCore 3 Y))
  have hθ3' : ¬ 3 ∣ orderOf θM := fun h => hθ3 (h.trans (hord ▸ orderOf_dvd_natCard _))
  have h1 : orderOf (π ⟨w, hwM⟩) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one (by
    rw [← map_pow]
    have : (⟨w, hwM⟩ : M) ^ 3 ^ e = 1 := Subtype.ext (by simpa using hwe)
    rw [this, map_one])
  have h2 : orderOf (π ⟨w, hwM⟩) ∣ orderOf θM := by
    rw [hπw]
    exact orderOf_map_dvd π θM
  have hcop : Nat.Coprime (3 ^ e) (orderOf θM) :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3')
  have h3 : orderOf (π ⟨w, hwM⟩) = 1 := by
    have h := Nat.dvd_gcd h1 h2
    rwa [hcop.gcd_eq_one, Nat.dvd_one] at h
  have hw1 : π ⟨w, hwM⟩ = 1 := orderOf_eq_one_iff.mp h3
  exact ⟨⟨w, hwM⟩, (QuotientGroup.eq_one_iff _).mp hw1, rfl⟩

theorem commutator_mem_imageModTheta {Y : Subgroup G} {d t u₀ : G}
    (hZ : ∀ z : Y ⧸ aschbacherSolvableCore 3 Y, (∀ y, z * y = y * z) → z = 1)
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hd3 : d ^ 3 = 1)
    (htN : t ∈ Subgroup.normalizer (Y : Set G)) (htd : t * d = d * t)
    {g s : Y ⧸ aschbacherSolvableCore 3 Y}
    (hg : barAut Y d hdN = MulAut.conj g) (hs : barAut Y t htN = MulAut.conj s)
    (hLC2 : ∀ p ∈ Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)),
      ∀ q ∈ Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)),
      p * q * p⁻¹ * q⁻¹ ∈ inSubgroup perfectResidual
        (Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y))))
    (hu₀Y : u₀ ∈ Y) (hu₀d : u₀ ∈ Subgroup.centralizer ({d} : Set G)) :
    ∃ hwY : t * u₀ * t⁻¹ * u₀⁻¹ ∈ Y,
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨t * u₀ * t⁻¹ * u₀⁻¹, hwY⟩ ∈
        imageModTheta Y (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G))) := by
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hq
  have hc : t * u₀ * t⁻¹ ∈ Y := conj_mem_of_mem_normalizer htN hu₀Y
  have hwY : t * u₀ * t⁻¹ * u₀⁻¹ ∈ Y := mul_mem hc (inv_mem hu₀Y)
  refine ⟨hwY, ?_⟩
  set ū := q ⟨u₀, hu₀Y⟩ with hū
  have himg : q ⟨t * u₀ * t⁻¹ * u₀⁻¹, hwY⟩ = s * ū * s⁻¹ * ū⁻¹ := by
    have e1 : (⟨t * u₀ * t⁻¹ * u₀⁻¹, hwY⟩ : Y) = ⟨t * u₀ * t⁻¹, hc⟩ * ⟨u₀, hu₀Y⟩⁻¹ := rfl
    rw [e1, map_mul, map_inv, ← barAut_mk htN hu₀Y hc, hs, MulAut.conj_apply]
  have hūg : ū ∈ Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    rw [← barCentralizer_eq_centralizer hdN hg, KFacts.mem_barCentralizer_zpowers_iff hdN]
    exact barAut_mk_of_commute hdN hu₀Y hu₀d
  have hsg : s ∈ Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    have hcomm := barAut_commute htN hdN htd
    rw [hs, hg] at hcomm
    have e : MulAut.conj (s * g * s⁻¹) = MulAut.conj g := by
      rw [map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right]
    have e' := eq_of_conj_eq hZ e
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * g = s * g * s⁻¹ * s := by group
      _ = g * s := by rw [e']
  have h := hLC2 s hsg ū hūg
  rw [himg]
  rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hdN ⟨1, by rwa [pow_one]⟩,
    barCentralizer_eq_centralizer hdN hg]
  exact h

theorem false_of_outer {Y : Subgroup G} {d x : G}
    (hZ : ∀ z : Y ⧸ aschbacherSolvableCore 3 Y, (∀ y, z * y = y * z) → z = 1)
    (hcyc : KFacts.OutThreeCyclic (Y ⧸ aschbacherSolvableCore 3 Y))
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hd3 : d ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hx3 : x ^ 3 = 1) (hdx : d * x = x * d)
    (hdout : ¬ KFacts.IsInnerAut (barAut Y d hdN)) (hxout : ¬ KFacts.IsInnerAut (barAut Y x hxN))
    (h3 : ∀ y : barCentralizer (Subgroup.zpowers d) Y, y ^ 3 = 1 →
      y ∈ perfectResidual (barCentralizer (Subgroup.zpowers d) Y))
    (hxU : Sec4.InducesOuterTheta x
      (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) : False := by
  classical
  set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hq
  set δ := barAut Y d hdN with hδ
  set ξ := barAut Y x hxN with hξ
  obtain ⟨k, hk3, hkin⟩ := hcyc δ ξ (barAut_commute hdN hxN hdx) (barAut_pow_three hdN hd3)
    (barAut_pow_three hxN hx3) hdout
  obtain ⟨g, hg⟩ := hkin
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hxout
    rw [pow_zero, one_mul] at hg
    exact ⟨g, hg⟩
  have hcomm : δ * ξ = ξ * δ := barAut_commute hdN hxN hdx
  have hgfix : δ g = g := by
    have e : δ * MulAut.conj g * δ⁻¹ = MulAut.conj g := by
      rw [hg]
      have : δ * (δ ^ k * ξ) = δ ^ k * ξ * δ := by
        rw [← mul_assoc, ← pow_succ', pow_succ, mul_assoc, mul_assoc, hcomm]
      rw [this, mul_inv_cancel_right]
    rw [KFacts.mul_mulAutConj_mul_inv] at e
    exact eq_of_conj_eq hZ e
  have hgC : g ∈ barCentralizer (Subgroup.zpowers d) Y :=
    (KFacts.mem_barCentralizer_zpowers_iff hdN g).mpr hgfix
  have hg3 : g ^ 3 = 1 := by
    have hc : Commute (δ ^ k) ξ := Commute.pow_left (hcomm : Commute δ ξ) k
    have e : MulAut.conj (g ^ 3) = MulAut.conj 1 := by
      rw [map_pow, hg, map_one, hc.mul_pow, ← pow_mul, mul_comm, pow_mul,
        barAut_pow_three hdN hd3, one_pow, one_mul, barAut_pow_three hxN hx3]
    exact eq_of_conj_eq hZ e
  have hgR : g ∈ imageModTheta Y U := by
    rw [hU, KFacts.imageModTheta_perfectResidual_centralizer_eq hdN ⟨1, by rwa [pow_one]⟩]
    exact ⟨⟨g, hgC⟩, h3 ⟨g, hgC⟩ (Subtype.ext (by simpa using hg3)), rfl⟩
  obtain ⟨ug, hugU, hugq⟩ := hgR
  have hugU' : (ug : G) ∈ U := Subgroup.mem_subgroupOf.mp hugU
  have hξ' : ξ = (δ ^ k)⁻¹ * MulAut.conj g := by rw [hg, inv_mul_cancel_left]
  have hξC : ∀ z, δ z = z → ξ z = g * z * g⁻¹ := by
    intro z hz
    have hz' : δ (g * z * g⁻¹) = g * z * g⁻¹ := by rw [map_mul, map_mul, map_inv, hz, hgfix]
    have hzk : ∀ j : ℕ, (δ ^ j) (g * z * g⁻¹) = g * z * g⁻¹ := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih => rw [pow_succ', MulAut.mul_apply, ih, hz']
    rw [hξ', MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulEquiv.symm_apply_eq,
      hzk k]
  obtain ⟨hxNU, hnot⟩ := hxU
  apply hnot
  refine ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 U) ⟨ug, hugU'⟩, ?_⟩
  ext v
  induction v using QuotientGroup.induction_on with
  | H v =>
  obtain ⟨v, hvU⟩ := v
  have hvM : v ∈ Y ⊓ Subgroup.centralizer ({d} : Set G) := inSubgroup_perfectResidual_le' _ hvU
  have hvY : v ∈ Y := hvM.1
  have hxvU : x * v * x⁻¹ ∈ U := conj_mem_of_mem_normalizer hxNU hvU
  have hugvU : ug * v * ug⁻¹ ∈ U := mul_mem (mul_mem hugU' hvU) (inv_mem hugU')
  have hY1 : q ⟨x * v * x⁻¹, conj_mem_of_mem_normalizer hxN hvY⟩ =
      q ⟨ug * v * ug⁻¹, mul_mem (mul_mem ug.2 hvY) (inv_mem ug.2)⟩ := by
    rw [← barAut_mk hxN hvY, hξC _ (barAut_mk_of_commute hdN hvY hvM.2), ← hugq]
    rfl
  have hθY : (ug * v * ug⁻¹)⁻¹ * (x * v * x⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) Y :=
    ⟨_, QuotientGroup.eq.mp hY1.symm, rfl⟩
  have hθU : (ug * v * ug⁻¹)⁻¹ * (x * v * x⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) U :=
    theta_inf_le_theta' ((inSubgroup_perfectResidual_le' _).trans inf_le_left)
      (Subgroup.mem_inf.mpr ⟨hθY, U.mul_mem (U.inv_mem hugvU) hxvU⟩)
  obtain ⟨θ', hθ', hθ'v⟩ := hθU
  change QuotientGroup.mk' (aschbacherSolvableCore 3 U) ⟨ug, hugU'⟩ *
      QuotientGroup.mk' (aschbacherSolvableCore 3 U) ⟨v, hvU⟩ *
      (QuotientGroup.mk' (aschbacherSolvableCore 3 U) ⟨ug, hugU'⟩)⁻¹ =
    QuotientGroup.mk' (aschbacherSolvableCore 3 U) (Sec4.compAction U ⟨x, hxNU⟩ ⟨v, hvU⟩)
  rw [← map_mul, ← map_inv, ← map_mul]
  apply QuotientGroup.eq.mpr
  have e : (⟨ug, hugU'⟩ * ⟨v, hvU⟩ * ⟨ug, hugU'⟩⁻¹)⁻¹ * Sec4.compAction U ⟨x, hxNU⟩ ⟨v, hvU⟩ =
      θ' := Subtype.ext (by rw [show ((θ' : U) : G) = _ from hθ'v]; rfl)
  rw [e]
  exact hθ'

theorem not_isQuasisimple_of_residual_eq_bot {Y : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (Y : Set G)) (hd3 : d ^ 3 = 1)
    (hbot : inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers d) Y) = ⊥) :
    ¬ IsQuasisimple (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
      aschbacherSolvableCore 3
        (inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)))) := by
  set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hU
  intro hq
  have himg : imageModTheta Y U = ⊥ := by
    rw [hU, KFacts.imageModTheta_perfectResidual_centralizer_eq hdN ⟨1, by rwa [pow_one]⟩, hbot]
  have hUY : U ≤ Y := (inSubgroup_perfectResidual_le' _).trans inf_le_left
  have hUθ : U ≤ inSubgroup (aschbacherSolvableCore 3) Y := by
    intro u hu
    have h : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨u, hUY hu⟩ ∈ imageModTheta Y U :=
      ⟨⟨u, hUY hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
    rw [himg, Subgroup.mem_bot] at h
    exact ⟨_, (QuotientGroup.eq_one_iff _).mp h, rfl⟩
  obtain ⟨hθs, -⟩ := Sec6.theta_solvable_and_not_dvd Y
  have hUs : Group.IsSolvable U := by
    have : Group.IsSolvable (inSubgroup (aschbacherSolvableCore 3) Y) := hθs
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hUθ)
      (Subgroup.inclusion_injective hUθ)
  have hQs : Group.IsSolvable (U ⧸ aschbacherSolvableCore 3 U) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective _)
  obtain ⟨hP, -, a, b, hab⟩ := hq
  have : Nontrivial (U ⧸ aschbacherSolvableCore 3 U) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hab
    have : Subsingleton ((U ⧸ aschbacherSolvableCore 3 U) ⧸
        Subgroup.center (U ⧸ aschbacherSolvableCore 3 U)) := by
      refine ⟨fun y z => ?_⟩
      induction y using QuotientGroup.induction_on with
      | H y => induction z using QuotientGroup.induction_on with
        | H z => rw [Subsingleton.elim y z]
    exact Subsingleton.elim _ _
  haveI : Group.IsPerfect (U ⧸ aschbacherSolvableCore 3 U) := hP
  exact Group.IsPerfect.not_isSolvable _ hQs

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
