module

public import CFSG.Quasithin.Background.C1PackS15205I
public import CFSG.Quasithin.Background.C1PackS15205H

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section Index

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_centralizer_le_of_card_three {X V V' : Subgroup G}
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hXV' : X ≤ Subgroup.normalizer (V' : Set G))
    (hle : X ⊓ Subgroup.centralizer (V : Set G) ≤ X ⊓ Subgroup.centralizer (V' : Set G))
    (h1 : Nat.card (autOn X V) = 3) (h2 : Nat.card (autOn X V') = 3) :
    X ⊓ Subgroup.centralizer (V' : Set G) ≤ X ⊓ Subgroup.centralizer (V : Set G) := by
  have e1 := card_autOn_eq_relIndex hXV
  have e2 := card_autOn_eq_relIndex hXV'
  rw [h1] at e1
  rw [h2] at e2
  have e3 := Subgroup.relIndex_mul_relIndex (X ⊓ Subgroup.centralizer (V : Set G))
    (X ⊓ Subgroup.centralizer (V' : Set G)) X hle inf_le_left
  rw [← e1, ← e2] at e3
  have e4 : (X ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (X ⊓ Subgroup.centralizer (V' : Set G)) = 1 := by omega
  exact Subgroup.relIndex_eq_one.mp e4

end Index

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

theorem Ctr5.relIndex_H_eq_three (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁)
    {Q : Subgroup (MulAut (V154 T Mc M))} (hQ : QD5 T Mc M M₁ Q)
    (hCH : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M₁ ⊓ M) :
    (M₁ ⊓ M).relIndex M = 3 := by
  have hd := c.std.data
  have h3 := c.case_three
  obtain ⟨-, hA, -⟩ := id h3
  have sh : OmShape (mBar0 T Mc M) := S152Y.omShape_mBar0 hOm h3
  have hMb36 : Nat.card (autOn M (V154 T Mc M)) = 36 := by rw [hA]; exact sh.card_X
  have hsyl : IsSylowTwoOf (autOn T (V154 T Mc M)) (mBar0 T Mc M) := by
    rw [← hA]; exact S152Y.isSylowTwoOf_Tb hd
  have hT4 : Nat.card (autOn T (V154 T Mc M)) = 4 := card_eq_four_of_isSylowTwoOf sh.card_X hsyl
  have hHb : Nat.card (autOn (M₁ ⊓ M) (V154 T Mc M)) = 12 := by
    have hle : autOn (M₁ ⊓ M) (V154 T Mc M) ≤ mBar0 T Mc M := by
      rw [← hA]; exact A4.autOn_mono inf_le_right
    have hd36 : Nat.card (autOn (M₁ ⊓ M) (V154 T Mc M)) ∣ 36 :=
      sh.card_X ▸ Subgroup.card_dvd_of_le hle
    have hd3 : 3 ∣ Nat.card (autOn (M₁ ⊓ M) (V154 T Mc M)) :=
      hQ.card ▸ Subgroup.card_dvd_of_le hQ.le_Hb
    have hd4 : 4 ∣ Nat.card (autOn (M₁ ⊓ M) (V154 T Mc M)) :=
      hT4 ▸ Subgroup.card_dvd_of_le (A4.autOn_mono c.T_le_H)
    have hd12 : 12 ∣ Nat.card (autOn (M₁ ⊓ M) (V154 T Mc M)) :=
      Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 4) hd3 hd4
    have hne : Nat.card (autOn (M₁ ⊓ M) (V154 T Mc M)) ≠ 36 := by
      intro h36
      apply c.not_mBar0_le
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h36, sh.card_X])).symm.le
    obtain ⟨k, hk⟩ := hd12
    have hk3 : k ∣ 3 := by
      rw [hk, show (36 : ℕ) = 12 * 3 by norm_num] at hd36
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hd36
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h1 | h1
    · rw [hk, h1]
    · exact absurd (by rw [hk, h1]) hne
  have hHV : M₁ ⊓ M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := inf_le_right.trans hd.hMV
  have hHC : (M₁ ⊓ M) ⊓ Subgroup.centralizer (V154 T Mc M : Set G) =
      M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_antisymm (fun x hx => ⟨hx.1.2, hx.2⟩) (fun x hx => ⟨hCH hx, hx.2⟩)
  have e1 := card_autOn_eq_relIndex hd.hMV
  have e2 := card_autOn_eq_relIndex hHV
  rw [hMb36] at e1
  rw [hHb, hHC] at e2
  have e3 := Subgroup.relIndex_mul_relIndex (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
    (M₁ ⊓ M) M hCH inf_le_right
  rw [← e1, ← e2] at e3
  omega

theorem Ctr5.false_of_VZ (h113 : StageLemma14113) (hOm : Om4IsoStatement) (c : Ctr5 T Mc M M₁)
    (hV : V154 T Mc M = VZ T M) : False := by
  classical
  have hd := c.std.data
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := c.exists_QD5 hOm
  have hY := yd5_of_VZ c hV hQ
  have hCV : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
      M₁ ⊓ Subgroup.centralizer (VZ T M₁ : Set G) := by
    rw [hV]; exact c.centralizer_V_le
  have hCH : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ M₁ ⊓ M :=
    fun x hx => ⟨(hCV hx).1, hx.1⟩
  have hCn : M ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, A4.mem_normalizer_centralizer (hd.hMV hg)⟩
  have hCY2 : M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
      Subgroup.normalizer (Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) : Set G) :=
    fun g hg => c.Y2_normal hY (hCV hg).1
  have hY2Y0 : Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) ≤ preOn M (V154 T Mc M) Q :=
    c.Y2_le_Yh hY
  have hY0M : preOn M (V154 T Mc M) Q ≤ M := preOn_le _ _ _
  have hDC : Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) ⊓ Subgroup.centralizer (VZ T M₁ : Set G) ≤
      M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := by
    have hY0N : preOn M (V154 T Mc M) Q ≤ Subgroup.normalizer (V154 T Mc M : Set G) :=
      hY0M.trans hd.hMV
    have hY0N₁ : preOn M (V154 T Mc M) Q ≤ Subgroup.normalizer (VZ T M₁ : Set G) :=
      hY.le_H.trans (inf_le_left.trans (le_normalizer_VZ T M₁))
    have hle : preOn M (V154 T Mc M) Q ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤
        preOn M (V154 T Mc M) Q ⊓ Subgroup.centralizer (VZ T M₁ : Set G) := fun y hy =>
      ⟨hy.1, (hCV ⟨hY0M hy.1, hy.2⟩).2⟩
    have h1 : Nat.card (autOn (preOn M (V154 T Mc M) Q) (V154 T Mc M)) = 3 := by
      rw [hQ.autOn_Y0 c]; exact hQ.card
    have h2 := inf_centralizer_le_of_card_three hY0N hY0N₁ hle h1 hY.card
    intro d hdd
    have h3 := h2 ⟨hY2Y0 hdd.1, hdd.2⟩
    exact ⟨hY0M (hY2Y0 hdd.1), h3.2⟩
  have hS := c.Y2_inf_centralizer_le h113 hY
  obtain ⟨x, hxY, ⟨a₃, hxo⟩, hxC, hxdec⟩ := c.exists_gen_Y2 h113 hY
  have hxM : x ∈ M := hY0M (hY2Y0 hxY)
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := a₃) (by rw [Nat.card_zpowers, hxo])
  obtain ⟨P, hP, hzP⟩ := exists_isSylowIn_ge 3 (Subgroup.zpowers_le.mpr hxM) hx3
  have hab := c.sylow_abelian h113 hOm hV hQ hP
  have hidx := c.relIndex_H_eq_three hOm hQ hCH
  have hPH : ¬ P ≤ M₁ ⊓ M := by
    intro hPH
    apply hP.2.2
    rw [← Subgroup.relIndex_mul_relIndex P (M₁ ⊓ M) M hPH inf_le_right, hidx]
    exact dvd_mul_left 3 _
  set W₃ : Subgroup G := conjClosure (Subgroup.zpowers x)
    (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) with hW₃
  have hW₃Y : W₃ ≤ Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) :=
    conjClosure_le fun g hg z hz => by
      have hzY : z ∈ Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) :=
        (Subgroup.zpowers_le.mpr hxY) hz
      exact (Subgroup.mem_normalizer_iff.mp (hCY2 hg) z).mp hzY
  have hCW₃ : ∀ g ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G), ∀ w ∈ W₃,
      g * w * g⁻¹ ∈ W₃ := by
    intro g hg w hw
    have hle : W₃ ≤ W₃.comap (MulAut.conj g).toMonoidHom := by
      refine conjClosure_le fun c' hc' z hz => ?_
      show g * (c' * z * c'⁻¹) * g⁻¹ ∈ W₃
      have e : g * (c' * z * c'⁻¹) * g⁻¹ = (g * c') * z * (g * c')⁻¹ := by group
      rw [e]
      exact mem_conjClosure ((M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)).mul_mem hg hc') hz
    exact hle hw
  have hY₂W₃ : Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) ≤ W₃ := by
    refine (Y2of_idem T Mc M₁ (preOn M (V154 T Mc M) Q)).symm.le.trans
      (oTwoUpper_le_of_pow_mem fun y hy => ?_)
    obtain ⟨j, hj⟩ := hxdec y hy
    have hdY : (x ^ j)⁻¹ * y ∈ Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) :=
      (Y2of T Mc M₁ (preOn M (V154 T Mc M) Q)).mul_mem
        ((Y2of T Mc M₁ (preOn M (V154 T Mc M) Q)).inv_mem
          ((Y2of T Mc M₁ (preOn M (V154 T Mc M) Q)).pow_mem hxY j)) hy
    have hdC : (x ^ j)⁻¹ * y ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
      hDC ⟨hdY, hj⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 M₁) ⟨_, hS ⟨hdY, hj⟩⟩
    have hk' : ((x ^ j)⁻¹ * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hxjW : x ^ j ∈ W₃ :=
      le_conjClosure _ _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) j)
    have hdN : (x ^ j)⁻¹ * y ∈ Subgroup.normalizer (W₃ : Set G) :=
      (le_normalizer_of_conj' hCW₃) hdC
    obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hxjW hdN (2 ^ k)
    refine ⟨k, ?_⟩
    have e : y = x ^ j * ((x ^ j)⁻¹ * y) := by group
    rw [e, hpow, hk', mul_one]
    exact hx'
  have hPW₃ : ∀ g ∈ P, ∀ w ∈ W₃, g * w * g⁻¹ ∈ W₃ := by
    intro g hg w hw
    have hle : W₃ ≤ W₃.comap (MulAut.conj g).toMonoidHom := by
      refine conjClosure_le fun c' hc' z hz => ?_
      show g * (c' * z * c'⁻¹) * g⁻¹ ∈ W₃
      have hgM : g ∈ M := hP.1 hg
      have hc'' : g * c' * g⁻¹ ∈ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
        (Subgroup.mem_normalizer_iff.mp (hCn hgM) c').mp hc'
      have hgz : g * z * g⁻¹ ∈ Subgroup.zpowers x := by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hgx : Commute g x := hab g hg x (hzP (Subgroup.mem_zpowers x))
        have h1 : g * x ^ i = x ^ i * g := (hgx.zpow_right i).eq
        have h2 : g * x ^ i * g⁻¹ = x ^ i := by rw [h1]; group
        rw [h2]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) i
      have e : g * (c' * z * c'⁻¹) * g⁻¹ = (g * c' * g⁻¹) * (g * z * g⁻¹) * (g * c' * g⁻¹)⁻¹ := by
        group
      rw [e]
      exact mem_conjClosure hc'' hgz
    exact hle hw
  have hPnorm : P ≤ Subgroup.normalizer (Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) : Set G) := by
    rw [le_antisymm hY₂W₃ hW₃Y]
    exact le_normalizer_of_conj' hPW₃
  have hN : M ≤ Subgroup.normalizer (Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) : Set G) := by
    set K : Subgroup G := M ⊓ Subgroup.normalizer
      (Y2of T Mc M₁ (preOn M (V154 T Mc M) Q) : Set G) with hK
    have hHK : M₁ ⊓ M ≤ K := fun h hh => ⟨hh.2, c.Y2_normal hY hh.1⟩
    obtain ⟨g, hgP, hgH⟩ : ∃ g ∈ P, g ∉ M₁ ⊓ M := by
      by_contra hcon
      push Not at hcon
      exact hPH hcon
    have hgK : g ∈ K := ⟨hP.1 hgP, hPnorm hgP⟩
    have h1 : (M₁ ⊓ M).relIndex K * K.relIndex M = (M₁ ⊓ M).relIndex M :=
      Subgroup.relIndex_mul_relIndex _ _ _ hHK inf_le_left
    rw [hidx] at h1
    have hdvd : (M₁ ⊓ M).relIndex K ∣ 3 := ⟨K.relIndex M, h1.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h3 | h3
    · exact absurd ((Subgroup.relIndex_eq_one.mp h3) hgK) hgH
    · rw [h3] at h1
      have h4 : K.relIndex M = 1 := by omega
      exact fun m hm => (Subgroup.relIndex_eq_one.mp h4 hm).2
  exact c.false_of_Y2_normal h113 hY hN

end Main

end C1Pack5

end CFSG.Quasithin
