module

import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartOne.CTP.SeitzToral
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace Res611Res7

variable {G : Type} [Group G] [Finite G]

theorem mk_commute_of_ne {d : G} {K K' : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hK' : K' ∈ thetaComponentsAt 3 d) (hne : K ≠ K')
    {k y : Subgroup.centralizer ({d} : Set G)} (hk : (k : G) ∈ K) (hy : (y : G) ∈ K') :
    QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({d} : Set G))) k *
        QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({d} : Set G))) y =
      QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({d} : Set G))) y *
        QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({d} : Set G))) k := by
  obtain ⟨z, hz, hzk⟩ := commutator_le_theta_of_ne_mem_thetaComponentsAt hK hK' hne
    (Subgroup.commutator_mem_commutator hk hy)
  have hz' : z = k * y * k⁻¹ * y⁻¹ := Subtype.ext (by
    rw [show ((k * y * k⁻¹ * y⁻¹ : Subgroup.centralizer ({d} : Set G)) : G) =
      (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ from rfl, ← commutatorElement_def]
    exact hzk)
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({d} : Set G)))
    with hπ
  have h1 : π z = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hz
  rw [hz', map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc π k * π y = (π k * π y * (π k)⁻¹ * (π y)⁻¹) * (π y * π k) := by group
    _ = π y * π k := by rw [h1, one_mul]

theorem false_of_not_mem_normalizer (he : CFSG.Assembly.evenRank G = 3) {d x : G}
    {K B : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hx : x ∈ Subgroup.centralizer ({d} : Set G)) (hx2 : x ^ 2 = 1)
    (hxK : x ∉ Subgroup.normalizer (K : Set G))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBK : B ≤ K)
    (hcard : 81 * Nat.card (B ⊓ thetaQuotCentralizer K : Subgroup G) ≤ Nat.card B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.centralizer ({d} : Set G) with hH
  set Θ := aschbacherSolvableCore 3 H with hΘ
  set π := QuotientGroup.mk' Θ with hπ
  set Kx := K.map (MulAut.conj x).toMonoidHom with hKx
  have hKxd : Kx ∈ thetaComponentsAt 3 d := map_conj_mem_thetaComponentsAt hx hK
  have hne : K ≠ Kx := ne_map_conj_of_not_mem_normalizer hxK
  have hKH : K ≤ H := le_centralizer_of_mem_thetaComponentsAt hK
  have hBH : B ≤ H := hBK.trans hKH
  set xH : H := ⟨x, hx⟩ with hxH
  set ι : B →* H := Subgroup.inclusion hBH with hι
  have hcomm : ∀ k y : H, (k : G) ∈ K → (y : G) ∈ Kx → π k * π y = π y * π k :=
    fun k y hk hy => mk_commute_of_ne hK hKxd hne hk hy
  have hbx : ∀ b : H, (b : G) ∈ K → ((xH * b * xH⁻¹ : H) : G) ∈ Kx :=
    fun b hb => ⟨b, hb, rfl⟩
  set f : B → H ⧸ Θ := fun b => π (ι b) * π (xH * ι b * xH⁻¹) with hf
  have hfmul : ∀ b₁ b₂ : B, f (b₁ * b₂) = f b₁ * f b₂ := by
    intro b₁ b₂
    have h := hcomm (ι b₂) (xH * ι b₁ * xH⁻¹) (hBK b₂.2) (hbx _ (hBK b₁.2))
    have hconj : xH * ι (b₁ * b₂) * xH⁻¹ = (xH * ι b₁ * xH⁻¹) * (xH * ι b₂ * xH⁻¹) := by
      rw [map_mul]
      group
    simp only [hf]
    rw [hconj, map_mul ι, map_mul π, map_mul π (xH * ι b₁ * xH⁻¹)]
    calc π (ι b₁) * π (ι b₂) * (π (xH * ι b₁ * xH⁻¹) * π (xH * ι b₂ * xH⁻¹)) =
        π (ι b₁) * (π (ι b₂) * π (xH * ι b₁ * xH⁻¹)) * π (xH * ι b₂ * xH⁻¹) := by group
      _ = π (ι b₁) * (π (xH * ι b₁ * xH⁻¹) * π (ι b₂)) * π (xH * ι b₂ * xH⁻¹) := by rw [h]
      _ = π (ι b₁) * π (xH * ι b₁ * xH⁻¹) * (π (ι b₂) * π (xH * ι b₂ * xH⁻¹)) := by group
  set φ : B →* H ⧸ Θ := MonoidHom.mk' f hfmul with hφ
  have hφapp : ∀ b : B, φ b = π (ι b) * π (xH * ι b * xH⁻¹) := fun b => rfl
  have hker : ∀ b : B, φ b = 1 → (b : G) ∈ thetaQuotCentralizer K := by
    intro b hb1
    rw [hφapp] at hb1
    have hb1' : π (ι b) = (π (xH * ι b * xH⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left hb1
    refine mem_thetaQuotCentralizer_iff.mpr ⟨Subgroup.le_normalizer (hBK b.2), fun l hl => ?_⟩
    rw [theta_eq_inf_of_mem_thetaComponentsAt hK]
    refine ⟨K.mul_mem (K.inv_mem hl) (K.mul_mem (K.mul_mem (hBK b.2) hl) (K.inv_mem (hBK b.2))),
      ?_⟩
    set lH : H := ⟨l, hKH hl⟩ with hlH
    refine ⟨lH⁻¹ * (ι b * lH * (ι b)⁻¹), ?_, rfl⟩
    have hc := hcomm lH (xH * ι b * xH⁻¹) hl (hbx _ (hBK b.2))
    set q := π lH
    set c := π (xH * ι b * xH⁻¹)
    have hcq : c⁻¹ * q = q * c⁻¹ := by
      calc c⁻¹ * q = c⁻¹ * (q * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * q) * c⁻¹ := by rw [hc]
        _ = q * c⁻¹ := by group
    have h1 : π (lH⁻¹ * (ι b * lH * (ι b)⁻¹)) = 1 := by
      calc π (lH⁻¹ * (ι b * lH * (ι b)⁻¹)) = q⁻¹ * (π (ι b) * q * (π (ι b))⁻¹) := by
            simp only [map_mul, map_inv]; rfl
        _ = q⁻¹ * (c⁻¹ * q * c⁻¹⁻¹) := by rw [hb1']
        _ = q⁻¹ * (q * c⁻¹ * c⁻¹⁻¹) := by rw [hcq]
        _ = 1 := by group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hkercard : Nat.card φ.ker ≤ Nat.card (B ⊓ thetaQuotCentralizer K : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun k : φ.ker =>
      (⟨((k : B) : G), (k : B).2, hker k k.2⟩ : (B ⊓ thetaQuotCentralizer K : Subgroup G))) ?_
    intro k k' h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
  have hBcard : Nat.card B = Nat.card φ.range * Nat.card φ.ker := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have hpos : 0 < Nat.card (B ⊓ thetaQuotCentralizer K : Subgroup G) := Nat.card_pos
  have h81 : 81 ≤ Nat.card φ.range := by
    have h1 : 81 * Nat.card (B ⊓ thetaQuotCentralizer K : Subgroup G) ≤
        Nat.card φ.range * Nat.card (B ⊓ thetaQuotCentralizer K : Subgroup G) :=
      hcard.trans (hBcard.le.trans (Nat.mul_le_mul_left _ hkercard))
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hRc : ∀ u ∈ φ.range, ∀ v ∈ φ.range, u * v = v * u := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hB.1.is_comm.comm a b]
  have hR3 : ∀ u ∈ φ.range, u ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 3 = 1 := Subtype.ext (by simpa using hB.2 _ a.2)
    rw [this, map_one]
  have hRp : IsPGroup 3 φ.range := fun u => ⟨1, Subtype.ext (by simpa using hR3 u u.2)⟩
  have hxx : xH * xH = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, hxH, ← pow_two, hx2, Subgroup.coe_one])
  have hRx : ∀ u ∈ φ.range, π xH * u = u * π xH := by
    rintro _ ⟨b, rfl⟩
    have h := hcomm (ι b) (xH * ι b * xH⁻¹) (hBK b.2) (hbx _ (hBK b.2))
    have hX : π xH * π xH = 1 := by rw [← map_mul, hxx, map_one]
    rw [hφapp]
    rw [map_mul π (xH * ι b) xH⁻¹, map_mul π xH (ι b), map_inv] at h ⊢
    have hXi : (π xH)⁻¹ = π xH := (eq_inv_of_mul_eq_one_left hX).symm
    rw [hXi] at h ⊢
    calc π xH * (π (ι b) * (π xH * π (ι b) * π xH)) =
        π xH * ((π xH * π (ι b) * π xH) * π (ι b)) := by rw [h]
      _ = (π xH * π xH) * π (ι b) * π xH * π (ι b) := by group
      _ = π (ι b) * π xH * π (ι b) := by rw [hX, one_mul]
      _ = π (ι b) * (π xH * π (ι b) * (π xH * π xH)) := by rw [hX, mul_one]; group
      _ = π (ι b) * (π xH * π (ι b) * π xH) * π xH := by group
  have hΘ3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1
  obtain ⟨E', hE'map, hE'dis⟩ :=
    CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker π
      (QuotientGroup.mk'_surjective Θ) hΘ3 φ.range hRp
  have hE'mem : ∀ y ∈ E', π y ∈ φ.range := fun y hy => hE'map ▸ ⟨y, hy, rfl⟩
  have hinj : ∀ y ∈ E', π y = 1 → y = 1 := fun y hy h1 =>
    Subgroup.disjoint_def.mp hE'dis hy (MonoidHom.mem_ker.mpr h1)
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ = 1 := by
      refine hinj _ (E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
        (E'.inv_mem hb)) ?_
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hRc _ (hE'mem a ha) _ (hE'mem b hb)]
      group
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [hc, one_mul]
  have hE'exp : ∀ a ∈ E', a ^ 3 = 1 := fun a ha =>
    hinj _ (E'.pow_mem ha 3) (by rw [map_pow]; exact hR3 _ (hE'mem a ha))
  have hE'card : Nat.card E' = Nat.card φ.range := by
    let g : E' →* φ.range := (π.comp E'.subtype).codRestrict φ.range (fun y => hE'mem y y.2)
    have hginj : Function.Injective g := by
      intro a b hab
      have h1 : π a = π b := congrArg Subtype.val hab
      have h2 : (a : H)⁻¹ * b = 1 := hinj _ (E'.mul_mem (E'.inv_mem a.2) b.2)
        (by rw [map_mul, map_inv, h1, inv_mul_cancel])
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    have hgsurj : Function.Surjective g := by
      intro u
      have hu : (u : H ⧸ Θ) ∈ E'.map π := by rw [hE'map]; exact u.2
      obtain ⟨y, hy, hyu⟩ := hu
      exact ⟨⟨y, hy⟩, Subtype.ext hyu⟩
    exact Nat.card_congr (Equiv.ofBijective g ⟨hginj, hgsurj⟩)
  set P := E'.map H.subtype with hPdef
  have hPe : CFSG.Assembly.IsElemAbelian 3 P := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
      obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
      change (a' : G) * b' = b' * a'
      exact congrArg Subtype.val (hE'comm a' ha' b' hb')
    · rintro _ ⟨a', ha', rfl⟩
      change (a' : G) ^ 3 = 1
      rw [← Subgroup.coe_pow, hE'exp a' ha', Subgroup.coe_one]
  have hPcard : 81 ≤ Nat.card P := by
    rw [hPdef, Subgroup.card_map_of_injective H.subtype_injective, hE'card]
    exact h81
  set θG := inSubgroup (aschbacherSolvableCore 3) H with hθG
  set N := Subgroup.zpowers x ⊔ θG with hN
  have hx1 : x ≠ 1 := fun h => hxK (h ▸ Subgroup.one_mem _)
  have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  have hT2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hxθ : Subgroup.zpowers x ≤ Subgroup.normalizer (θG : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_theta H hx)
  have hN3 : ¬ 3 ∣ Nat.card N :=
    not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hT2 hxθ
      (theta_solvable_and_not_dvd H).2
  have hPx : ∀ p ∈ P, p * x * p⁻¹ * x⁻¹ ∈ θG := by
    rintro _ ⟨p', hp', rfl⟩
    refine ⟨p' * xH * p'⁻¹ * xH⁻¹, ?_, rfl⟩
    have hc := hRx _ (hE'mem p' hp')
    have h1 : π (p' * xH * p'⁻¹ * xH⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      calc π p' * π xH * (π p')⁻¹ * (π xH)⁻¹ = (π p' * π xH) * (π p')⁻¹ * (π xH)⁻¹ := rfl
        _ = (π xH * π p') * (π p')⁻¹ * (π xH)⁻¹ := by rw [hc]
        _ = 1 := by group
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro a ha y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : a * x * a⁻¹ ∈ N := by
        rw [show a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x by group]
        exact N.mul_mem (Subgroup.mem_sup_right (hPx a ha))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
      rw [← conj_zpow]
      exact N.zpow_mem h1 k
    · intro a ha y hy
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta H (hPH ha)) y).mp hy)
  have hP3 : IsPGroup 3 P := Sec5.isPGroup_of_isElemAbelian hPe
  obtain ⟨R, hPR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three P N hP3 hN3 hPN 2 Nat.prime_two
  set RG := (R : Subgroup N).map N.subtype with hRG
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map N.subtype
  have hRG1 : RG ≠ ⊥ := by
    intro hbot
    obtain ⟨y, -, hle⟩ := exists_le_conj_sylow R (le_sup_left : Subgroup.zpowers x ≤ N) hT2
    rw [← hRG, hbot, Subgroup.map_bot] at hle
    exact hx1 (Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers x)))
  have := Sec5.card_le_of_le_normalizer he hRG1 hRG2 hPe hPR
  omega

theorem zpowers_inf_eq_bot {d : G} {K : Subgroup G} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1)
    (hdK : d ∉ K) : Subgroup.zpowers d ⊓ K = ⊥ := by
  have hord : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdvd : Nat.card (Subgroup.zpowers d ⊓ K : Subgroup G) ∣ 3 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers d ⊓ K ≤ Subgroup.zpowers d)
    rwa [Nat.card_zpowers, hord] at this
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    apply hdK
    have heq : Subgroup.zpowers d ⊓ K = Subgroup.zpowers d :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, Nat.card_zpowers, hord])
    have hmem : d ∈ Subgroup.zpowers d ⊓ K := by
      rw [heq]
      exact Subgroup.mem_zpowers d
    exact hmem.2

theorem inf_thetaQuotCentralizer_eq_bot_of_center {K B : Subgroup G} (hBK : B ≤ K)
    (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥) :
    B ⊓ thetaQuotCentralizer K = ⊥ := by
  rw [eq_bot_iff]
  rintro b ⟨hbB, hbC⟩
  have hbK := hBK hbB
  replace hbC : b ∈ thetaQuotCentralizer K := hbC
  rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (Subgroup.le_normalizer hbK),
    Sec12.thetaBarAct_of_mem hbK] at hbC
  have hbZ := Sec12.mem_center_of_conj_eq_one hbC
  rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hbZ
  exact Subgroup.mem_bot.mpr
    (Sec13.eq_one_of_mem_inSubgroup_theta_of_pow_three ⟨_, hbZ, rfl⟩ (hB.2 b hbB))

end Res611Res7

open Res611Res7

end CFSG.RankThree.PartTwo.Sec6
