module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Frame
public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79NF

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

variable {H : Type} [Group H] [Finite H]
variable {b t b₁ b₂ : H} {J : Subgroup H}

namespace Std

structure KData (S : Std b t b₁ b₂ J) (A₁ : Subgroup J6.S6) (x e : J6.S6) : Prop where
  sqA : ∀ s ∈ A₁, s * s = 1
  commA : ∀ a ∈ A₁, ∀ c ∈ A₁, a * c = c * a
  normA : ∀ s ∈ A₁, x * s * x⁻¹ ∈ A₁
  x3 : x ^ 3 = 1
  x1 : x ≠ 1
  cen : ∀ s ∈ A₁, s * x = x * s → s = 1 ∨ s = e
  e_mem : e ∈ A₁
  e_sq : e * e = 1
  e_ne : e ≠ 1
  e_comm : e * x = x * e
  Na : ¬ HC t (S.ι e)
  Nb : ¬ HC t (t * S.ι e)
  Nc : ¬ HC (S.ι e) (t * S.ι e)
  Nd : ∀ r : H, (∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H), y * r = r * y) → ¬ HC r (S.ι e)

variable {S : Std b t b₁ b₂ J} {A₁ : Subgroup J6.S6} {x e : J6.S6}

theorem KData.ιx_pow (hK : S.KData A₁ x e) : S.ι x ^ 3 = 1 := by
  rw [← map_pow, hK.x3, map_one]

theorem KData.ιx_ne (hK : S.KData A₁ x e) : S.ι x ≠ 1 := fun h1 =>
  hK.x1 (S.ι_injective (h1.trans (map_one S.ι).symm))

theorem KData.ιx_orderOf (hK : S.KData A₁ x e) : orderOf (S.ι x) = 3 :=
  orderOf_eq_prime hK.ιx_pow hK.ιx_ne

theorem KData.cen_frame (hK : S.KData A₁ x e) {y : H} (hy : y ∈ S.frame A₁)
    (hyx : y * S.ι x = S.ι x * y) : y = 1 ∨ y = S.ι e ∨ y = t ∨ y = t * S.ι e := by
  obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ y).mp hy
  · have : s * x = x * s := by
      apply S.ι_injective
      rw [map_mul, map_mul]
      exact hyx
    rcases hK.cen s hs this with rfl | rfl
    · left
      exact map_one S.ι
    · right; left; rfl
  · have : s * x = x * s := by
      apply S.ι_injective
      rw [map_mul, map_mul]
      have h1 : t * S.ι s * S.ι x = S.ι x * (t * S.ι s) := hyx
      calc S.ι s * S.ι x = t⁻¹ * (t * S.ι s * S.ι x) := by group
        _ = t⁻¹ * (S.ι x * (t * S.ι s)) := by rw [h1]
        _ = t⁻¹ * ((S.ι x * t) * S.ι s) := by group
        _ = t⁻¹ * ((t * S.ι x) * S.ι s) := by rw [S.ι_comm_t x]
        _ = S.ι x * S.ι s := by group
    rcases hK.cen s hs this with rfl | rfl
    · right; right; left
      simpa using (map_one S.ι)
    · right; right; right; rfl


theorem KData.cen_mem (hK : S.KData A₁ x e) {w : H} (hwN : w ∈ Nor (S.frame A₁))
    (hwx : w * S.ι x = S.ι x * w) (hw3 : ∃ k : ℕ, w ^ (3 ^ k) = 1) :
    w ∈ Subgroup.zpowers (S.ι x) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := S.hyp
  by_contra hnot
  have hwx' : w⁻¹ * S.ι x = S.ι x * w⁻¹ := by
    calc w⁻¹ * S.ι x = w⁻¹ * (S.ι x * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * S.ι x) * w⁻¹ := by rw [hwx]
      _ = S.ι x * w⁻¹ := by group
  have hconj : ∀ y ∈ S.frame A₁, y * S.ι x = S.ι x * y →
      w * y * w⁻¹ ∈ S.frame A₁ ∧ (w * y * w⁻¹) * S.ι x = S.ι x * (w * y * w⁻¹) := by
    intro y hy hyx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hwN y).mp hy, ?_⟩
    calc w * y * w⁻¹ * S.ι x = w * y * (w⁻¹ * S.ι x) := by group
      _ = w * y * (S.ι x * w⁻¹) := by rw [hwx']
      _ = w * (y * S.ι x) * w⁻¹ := by group
      _ = w * (S.ι x * y) * w⁻¹ := by rw [hyx]
      _ = (w * S.ι x) * y * w⁻¹ := by group
      _ = (S.ι x * w) * y * w⁻¹ := by rw [hwx]
      _ = S.ι x * (w * y * w⁻¹) := by group
  obtain ⟨hwtA, hwtx⟩ := hconj t (S.t_mem_frame A₁) (S.ι_comm_t x).symm
  have hwt : w * t * w⁻¹ = t := by
    rcases hK.cen_frame hwtA hwtx with h1 | h1 | h1 | h1
    · exfalso
      apply h.t_ne_one
      calc t = w⁻¹ * (w * t * w⁻¹) * w := by group
        _ = 1 := by rw [h1]; group
    · exact absurd ⟨w, h1⟩ hK.Na
    · exact h1
    · exact absurd ⟨w, h1⟩ hK.Nb
  have hιex : S.ι e * S.ι x = S.ι x * S.ι e := by rw [← map_mul, ← map_mul, hK.e_comm]
  obtain ⟨hweA, hwex⟩ := hconj _ (S.ι_mem_frame hK.e_mem) hιex
  have hιe_ne : S.ι e ≠ 1 := fun h1 => hK.e_ne (S.ι_injective (h1.trans (map_one S.ι).symm))
  have hwe : w * S.ι e * w⁻¹ = S.ι e := by
    rcases hK.cen_frame hweA hwex with h1 | h1 | h1 | h1
    · exfalso
      apply hιe_ne
      calc S.ι e = w⁻¹ * (w * S.ι e * w⁻¹) * w := by group
        _ = 1 := by rw [h1]; group
    · exact h1
    · exact absurd (HC.symm ⟨w, h1⟩) hK.Na
    · exact absurd ⟨w, h1⟩ hK.Nc
  have hwe' : w * S.ι e = S.ι e * w := by
    calc w * S.ι e = (w * S.ι e * w⁻¹) * w := by group
      _ = S.ι e * w := by rw [hwe]
  have hwt' : w * t = t * w := by
    calc w * t = (w * t * w⁻¹) * w := by group
      _ = t * w := by rw [hwt]
  obtain ⟨k, hk⟩ := hw3
  have hwp : IsPGroup 3 (Subgroup.zpowers w) := by
    have hord : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hxp : IsPGroup 3 (Subgroup.zpowers (S.ι x)) := isPGroup_zpowers_of_pow_three hK.ιx_pow
  have hxN : Subgroup.zpowers (S.ι x) ≤ Subgroup.normalizer (Subgroup.zpowers w : Set H) := by
    rw [Subgroup.zpowers_le]
    refine mem_Nor_zpowers_of_comm ?_
    exact hwx.symm
  have hWp : IsPGroup 3 (Subgroup.zpowers w ⊔ Subgroup.zpowers (S.ι x) : Subgroup H) :=
    IsPGroup.to_sup_of_normal_left' hwp hxp hxN
  set W : Subgroup H := Subgroup.zpowers w ⊔ Subgroup.zpowers (S.ι x) with hW
  have hWt : W ≤ Cen t := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hwt'
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (S.ι_comm_t x)
  have hW9 : Nat.card W ≤ 9 := h.card_le_nine_of_cen h.t_sq h.t_ne_one hWp hWt
  obtain ⟨m, hm⟩ := hWp.exists_card_eq
  have hxle : Subgroup.zpowers (S.ι x) ≤ W := le_sup_right
  have hwW : w ∈ W := Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  have hxcard : Nat.card (Subgroup.zpowers (S.ι x)) = 3 := by
    rw [Nat.card_zpowers, hK.ιx_orderOf]
  have hWne : Nat.card W ≠ 3 := by
    intro h3
    apply hnot
    have : Subgroup.zpowers (S.ι x) = W :=
      Subgroup.eq_of_le_of_card_ge hxle (by rw [h3, hxcard])
    rw [this]
    exact hwW
  have hdvd : 3 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le hxle
    rwa [hxcard] at this
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with hlt | hge
    · interval_cases m
      · rw [hm] at hdvd
        norm_num at hdvd
      · exact absurd (by rw [hm]; norm_num) hWne
    · exact hge
  have hW9' : Nat.card W = 9 := by
    have h9 : 9 ≤ 3 ^ m :=
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    rw [hm] at hW9 ⊢
    omega
  have hB₁3 : IsPGroup 3 (Subgroup.closure ({b₁, b₂} : Set H)) := by
    have hE := h.isElemAb_B
    haveI := hE.1
    exact (IsElementaryAbelian.isPGroup 3 _).to_le (FS79Hyp.B₁_le_B b b₁ b₂)
  have hB₁t : Subgroup.closure ({b₁, b₂} : Set H) ≤ Cen t := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (S.J_comm_t (h.B₁_le_J hy))
  have hB₁card : Nat.card (Subgroup.closure ({b₁, b₂} : Set H)) = 9 := by simpa using h.E9.2
  have hSylB := h.isSylowOf_cen h.t_sq h.t_ne_one hB₁3 hB₁t hB₁card
  obtain ⟨c, hc, hcW⟩ := L14.exists_conj_le_sylowOf hSylB hWt hWp
  set W' : Subgroup H := W.map (MulAut.conj c).toMonoidHom with hW'
  have hW'le : W' ≤ Subgroup.closure ({b₁, b₂} : Set H) := by
    rintro _ ⟨y, hy, rfl⟩
    have hce : (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := by simp [MulAut.conj_apply]
    rw [hce]
    exact hcW y hy
  have hW'card : Nat.card W' = 9 := by
    rw [hW', Subgroup.card_map_of_injective (MulAut.conj c).injective, hW9']
  have hW'eq : W' = Subgroup.closure ({b₁, b₂} : Set H) :=
    Subgroup.eq_of_le_of_card_ge hW'le (by rw [hW'card, hB₁card])
  have hWe : ∀ y ∈ W, y * S.ι e = S.ι e * y := by
    intro y hy
    have hcomm : ∀ a ∈ Subgroup.zpowers w, ∀ c' ∈ Subgroup.zpowers (S.ι x), Commute a c' := by
      intro a ha c' hc'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
      exact Commute.zpow_zpow (show Commute w (S.ι x) from hwx) i j
    obtain ⟨a, ha, c', hc', rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc'
    have h1 : Commute (w ^ i) (S.ι e) :=
      Commute.zpow_left (show Commute w (S.ι e) from hwe') i
    have h2 : Commute (S.ι x ^ j) (S.ι e) :=
      Commute.zpow_left (show Commute (S.ι x) (S.ι e) from hιex.symm) j
    exact (h1.mul_left h2).eq
  set r : H := c * S.ι e * c⁻¹ with hr
  have hrB : ∀ y ∈ Subgroup.closure ({b₁, b₂} : Set H), y * r = r * y := by
    intro y hy
    rw [← hW'eq] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    have hce : (MulAut.conj c).toMonoidHom y₀ = c * y₀ * c⁻¹ := by simp [MulAut.conj_apply]
    rw [hce, hr]
    calc c * y₀ * c⁻¹ * (c * S.ι e * c⁻¹) = c * (y₀ * S.ι e) * c⁻¹ := by group
      _ = c * (S.ι e * y₀) * c⁻¹ := by rw [hWe y₀ hy₀]
      _ = c * S.ι e * c⁻¹ * (c * y₀ * c⁻¹) := by group
  exact hK.Nd r hrB ⟨c⁻¹, by rw [hr]; group⟩


theorem KData.ιx_mem_Nor (hK : S.KData A₁ x e) : S.ι x ∈ Nor (S.frame A₁) := by
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  obtain ⟨s, hs, rfl | rfl⟩ := (S.mem_frame_iff A₁ y).mp hy
  · have : S.ι x * S.ι s * (S.ι x)⁻¹ = S.ι (x * s * x⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [this]
    exact S.ι_mem_frame (hK.normA s hs)
  · have : S.ι x * (t * S.ι s) * (S.ι x)⁻¹ = t * S.ι (x * s * x⁻¹) := by
      calc S.ι x * (t * S.ι s) * (S.ι x)⁻¹ = (S.ι x * t) * S.ι s * (S.ι x)⁻¹ := by group
        _ = (t * S.ι x) * S.ι s * (S.ι x)⁻¹ := by rw [S.ι_comm_t x]
        _ = t * (S.ι x * S.ι s * (S.ι x)⁻¹) := by group
        _ = t * S.ι (x * s * x⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [this]
    exact S.t_ι_mem_frame (hK.normA s hs)

theorem KData.isSylowOf (hK : S.KData A₁ x e) :
    CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers (S.ι x)) (Nor (S.frame A₁)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup H := Subgroup.zpowers (S.ι x) with hT
  set M : Subgroup H := Nor (S.frame A₁) with hM
  have hTM : T ≤ M := Subgroup.zpowers_le.mpr hK.ιx_mem_Nor
  have hTN : T ≤ Nor T := Subgroup.le_normalizer
  have hTK : T ≤ Nor T ⊓ M := le_inf hTN hTM
  have hTp : IsPGroup 3 T := isPGroup_zpowers_of_pow_three hK.ιx_pow
  refine CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le (H := Nor T) (M := M) ?_ inf_le_left
  have hTsub : IsPGroup 3 (T.subgroupOf (Nor T ⊓ M)) := hTp.comap_subtype
  obtain ⟨Q, hTQ⟩ := hTsub.exists_le_sylow
  have hQ' : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup ↥(Nor T ⊓ M)).map (Nor T ⊓ M).subtype)
      (Nor T ⊓ M) := ⟨Q, rfl⟩
  have hQT : (Q : Subgroup ↥(Nor T ⊓ M)).map (Nor T ⊓ M).subtype ≤ T := by
    rintro _ ⟨q, hq, rfl⟩
    set q' : H := ((q : ↥(Nor T ⊓ M)) : H) with hq'
    have hq'N : q' ∈ Nor T := q.2.1
    have hq'M : q' ∈ M := q.2.2
    obtain ⟨j, hj⟩ := (CFSG.ABGLocalTools.IsSylowOf.isPGroup hQ').exists_orderOf_eq_pow
      ⟨q', ⟨q, hq, rfl⟩⟩
    have hodd : Odd (orderOf q') := by
      have h1 := Subgroup.orderOf_coe (⟨q', ⟨q, hq, rfl⟩⟩ :
          ↥((Q : Subgroup ↥(Nor T ⊓ M)).map (Nor T ⊓ M).subtype))
      have h2 : orderOf q' = 3 ^ j := by
        rw [← hj]
        exact h1
      rw [h2]
      exact Odd.pow (by decide)
    have hmem : q' * S.ι x * q'⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hq'N (S.ι x)).mp
      (Subgroup.mem_zpowers _)
    have hcomm : q' * S.ι x * q'⁻¹ = S.ι x :=
      conj_eq_self_of_odd_of_mem_zpowers hK.ιx_orderOf hodd hmem
    have hcomm' : q' * S.ι x = S.ι x * q' := by
      calc q' * S.ι x = (q' * S.ι x * q'⁻¹) * q' := by group
        _ = S.ι x * q' := by rw [hcomm]
    have hpow : ∃ k : ℕ, q' ^ (3 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := (CFSG.ABGLocalTools.IsSylowOf.isPGroup hQ').exists_pow_pow_eq_one
        ⟨q', ⟨q, hq, rfl⟩⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    exact hK.cen_mem hq'M hcomm' hpow
  have hTle : T ≤ (Q : Subgroup ↥(Nor T ⊓ M)).map (Nor T ⊓ M).subtype :=
    calc T = (T.subgroupOf (Nor T ⊓ M)).map (Nor T ⊓ M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hTK).symm
      _ ≤ (Q : Subgroup ↥(Nor T ⊓ M)).map (Nor T ⊓ M).subtype := Subgroup.map_mono hTQ
  have heq : (Q : Subgroup ↥(Nor T ⊓ M)).map (Nor T ⊓ M).subtype = T := le_antisymm hQT hTle
  rw [heq] at hQ'
  exact hQ'

end Std

end CFSG.RankThree.PartTwo.Sec21.FF81
