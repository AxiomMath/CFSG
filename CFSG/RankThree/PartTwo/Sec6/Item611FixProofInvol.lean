module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofTools
public import CFSG.RankThree.PartTwo.Sec6.Item611Res7ProofInvol
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofE81

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open Res611Res7

namespace Res611Fix

variable {G : Type} [Group G] [Finite G]

theorem false_of_not_mem_normalizer (he : CFSG.Assembly.evenRank G = 3) {d x : G}
    {K B : Subgroup G} (hK : K ∈ thetaComponentsAt 3 d)
    (hx : x ∈ Subgroup.centralizer ({d} : Set G)) (hx2 : x ^ 2 = 1)
    (hxK : x ∉ Subgroup.normalizer (K : Set G))
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hBK : B ≤ K) (hcard : 81 ≤ Nat.card B)
    (hBC : B ⊓ thetaQuotCentralizer K ≤ Subgroup.zpowers d) : False := by
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
  have hker1 : ∀ b : B, φ b = 1 → b = 1 := by
    intro b hb
    have hbd : (b : G) ∈ Subgroup.zpowers d := hBC ⟨b.2, hker b hb⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbd
    have hxd : Commute x d := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hxb : xH * ι b * xH⁻¹ = ι b := by
      apply Subtype.ext
      change x * (b : G) * x⁻¹ = b
      rw [← hk, (hxd.zpow_right k).eq, mul_inv_cancel_right]
    rw [hφapp, hxb, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hb
    have hb2 : (b : G) ^ 2 ∈ inSubgroup (aschbacherSolvableCore 3) H :=
      ⟨ι b * ι b, hb, by rw [pow_two]; rfl⟩
    have hb3 : (b : G) ^ 3 = 1 := hB.2 _ b.2
    have hb23 : ((b : G) ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hb3, one_pow]
    have h1 := Sec13.eq_one_of_mem_inSubgroup_theta_of_pow_three hb2 hb23
    apply Subtype.ext
    calc (b : G) = (b : G) ^ 3 * ((b : G) ^ 2)⁻¹ := by group
      _ = 1 := by rw [hb3, h1, inv_one, one_mul]
  have h81 : 81 ≤ Nat.card φ.range := by
    have hinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hker1
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hcard
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

end Res611Fix

section Certs


theorem item611InvolNormal_holdsFix (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) : Item611InvolNormal := by
  intro G _ _ hst A hA hrank d hdA hd1 K hK hCAK x hx hx2
  by_contra hxK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d hK
  obtain ⟨m, hm5, hAcard⟩ := Sec4.exists_card_eq_of_four_lt_pRank hAe hrank
  have h243 : 243 ≤ Nat.card A := by
    rw [hAcard]
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
  have hd3 : orderOf d = 3 := orderOf_eq_prime (hAe.2 d hdA) hd1
  have hd3' : d ^ 3 = 1 := hAe.2 d hdA
  rcases Res611Fix.cases413 h45 h41 h413 hst hA hrank hdA hd1 hK hCAK with
    ⟨-, -, m', -, ⟨φ⟩, -⟩ | ⟨hAK, -⟩ | ⟨hdec, hdK, -⟩ | hcase
  ·
    obtain ⟨B, hBK, hB, hB81⟩ :=
      Res611Fix.exists_elemAbelian_le h45 h41 h413 hst hA hrank hdA hd1 hK hCAK
    have hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
      CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv
        (φ.trans (Sec4.projSLEquivPSL (GaloisField 3 (3 * m'))))
        (CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 3 (3 * m')))
    have hbot := inf_thetaQuotCentralizer_eq_bot_of_center hBK hB hZ
    exact false_of_not_mem_normalizer hst.evenRank_eq hKd hx hx2 hxK hB hBK
      (by rw [hbot, Subgroup.card_bot]; omega)
  ·
    refine false_of_not_mem_normalizer hst.evenRank_eq hKd hx hx2 hxK hAe hAK ?_
    rw [hCAK, Nat.card_zpowers, hd3]
    omega
  ·
    have hbot : (A ⊓ K) ⊓ thetaQuotCentralizer K = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨⟨hyA, hyK⟩, hyC⟩
      have hyd : y ∈ Subgroup.zpowers d := hCAK ▸ (⟨hyA, hyC⟩ : y ∈ A ⊓ thetaQuotCentralizer K)
      have hmem : y ∈ Subgroup.zpowers d ⊓ K := ⟨hyd, hyK⟩
      rwa [zpowers_inf_eq_bot (hAe.2 d hdA) hd1 hdK] at hmem
    have hle := Res611Res3.card_le_three_mul_card_inf hAe hdA hd1 hdec
    exact false_of_not_mem_normalizer hst.evenRank_eq hKd hx hx2 hxK
      (Sec5.isElemAbelian_of_le hAe inf_le_left) inf_le_right
      (by rw [hbot, Subgroup.card_bot]; omega)
  ·
    obtain ⟨hdK, hZ, hZ3, hM, -⟩ := hcase
    obtain ⟨P, hP, hP81⟩ := ks611G2CoverE81_holds _ hZ3 hM
    obtain ⟨B, hBK, hB, hBcard⟩ := Res611Fix.exists_elemAbelian_le_of_quot hP
    refine Res611Fix.false_of_not_mem_normalizer hst.evenRank_eq hKd hx hx2 hxK hB hBK
      (by omega) ?_
    rintro b ⟨hbB, hbC⟩
    have hbK := hBK hbB
    replace hbC : b ∈ thetaQuotCentralizer K := hbC
    rw [Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (Subgroup.le_normalizer hbK),
      Sec12.thetaBarAct_of_mem hbK] at hbC
    have hbZ := Sec12.mem_center_of_conj_eq_one hbC
    rw [hZ] at hbZ
    obtain ⟨y, hy, hyb⟩ := hbZ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hy)
    have hθ : (y : G)⁻¹ * b ∈ inSubgroup (aschbacherSolvableCore 3) K := by
      refine ⟨y⁻¹ * ⟨b, hbK⟩, ?_, rfl⟩
      have h2 : (QuotientGroup.mk y : K ⧸ aschbacherSolvableCore 3 K) =
          QuotientGroup.mk ⟨b, hbK⟩ := hyb
      exact QuotientGroup.eq.mp h2
    have hKd' : K ≤ Subgroup.centralizer ({d} : Set G) :=
      le_centralizer_of_mem_thetaComponentsAt hKd
    have hbd : Commute b d := Subgroup.mem_centralizer_singleton_iff.mp (hKd' hbK)
    have hθ3 : ((y : G)⁻¹ * b) ^ 3 = 1 := by
      rw [← hk, ((hbd.zpow_right k).inv_right).symm.mul_pow, hB.2 b hbB, mul_one, inv_pow,
        ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3', one_zpow, inv_one]
    have h1 := Sec13.eq_one_of_mem_inSubgroup_theta_of_pow_three hθ hθ3
    have hby : b = (y : G) := by
      calc b = (y : G) * ((y : G)⁻¹ * b) := by group
        _ = (y : G) := by rw [h1, mul_one]
    rw [hby, ← hk]
    exact Subgroup.zpow_mem_zpowers d k

end Certs

end CFSG.RankThree.PartTwo.Sec6
