module

public import CFSG.Quasithin.H13.L32A753g
public import CFSG.Quasithin.H13.L32A753h

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] {X K : Subgroup (MulAut V)}

omit [Finite V] in
theorem autSec_zpowers {b : MulAut V} {J C : Subgroup V} (hbJ : b ∈ stabSub J)
    (hbC : b ∈ stabSub C) :
    autSec (Subgroup.zpowers b) J C = Subgroup.zpowers (secHom (Subgroup.zpowers_le.2 hbJ)
      (Subgroup.zpowers_le.2 hbC) ⟨b, Subgroup.mem_zpowers b⟩) := by
  rw [← range_secHom (Subgroup.zpowers_le.2 hbJ) (Subgroup.zpowers_le.2 hbC)]
  ext φ
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨n, ?_⟩
    rw [← map_zpow]
    congr 1
  · rintro ⟨n, rfl⟩
    exact Subgroup.zpow_mem _ (MonoidHom.mem_range.2 ⟨_, rfl⟩) n

omit [Finite V] in
theorem index_fixV_sec_ge
    {J C : Subgroup V}
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hXJ : X ≤ stabSub J)
    (hXC : X ≤ stabSub C) (hP : B42TypeU33 ↥K) (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C)
    (hnat : G2NaturalDerived (autSec K J C) ⊤ ⊥ 1) (h64 : Nat.card (Sec J C) = 2 ^ 6)
    {b : MulAut V} (hbX : b ∈ X) (hbK : b ∉ K) (hb2 : b ^ 2 = 1) :
    2 ^ 3 ≤ (fixV (autSec (Subgroup.zpowers b) J C)).index := by
  have hs := isSimpleGroup_of_b42 hP
  obtain ⟨e, hKe, he⟩ := exists_equiv_sec hKX hXN hXJ hXC hnat
  set β := secHom hXJ hXC ⟨b, hbX⟩ with hβ
  have hβX : β ∈ autSec X J C := by
    rw [← range_secHom hXJ hXC]
    exact ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ := he β hβX
  have hγD : γ ∉ g2Derived (ZMod 2) := by
    intro hγ'
    have h1 : MulAut.congr e β ∈ (autSec K J C).map (MulAut.congr e).toMonoidHom := by
      rw [hKe, ← hγ]
      exact ⟨γ, hγ', rfl⟩
    obtain ⟨κ, hκ, hκe⟩ := h1
    have hκβ : κ = β := (MulAut.congr e).injective hκe
    rw [← range_secHom (hKX.trans hXJ) (hKX.trans hXC)] at hκ
    obtain ⟨k, hk⟩ := hκ
    have h2 : secHom hXJ hXC ⟨k, hKX k.2⟩ = secHom hXJ hXC ⟨b, hbX⟩ := by
      rw [← secHom_mono hKX hXJ hXC, hk, hκβ]
    have h3 := secHom_injective_X hKX hXN hCK hXJ hXC hs hnt h2
    have h4 : (k : MulAut V) = b := congrArg Subtype.val h3
    exact hbK (h4 ▸ k.2)
  have hb2' : (⟨b, hbX⟩ : ↥X) ^ 2 = 1 := Subtype.ext hb2
  have hβ2 : β ^ 2 = 1 := by rw [hβ, ← map_pow, hb2', map_one]
  have hγ2 : γ ^ 2 = 1 :=
    g2QAct_injective (by rw [map_pow, hγ, ← map_pow, hβ2, map_one, map_one])
  have hcard := card_fixV_le_eight hγD hγ2
  have hzp : (Subgroup.zpowers γ).map (g2QAct (ZMod 2)) =
      (autSec (Subgroup.zpowers b) J C).map (MulAut.congr e).toMonoidHom := by
    rw [autSec_zpowers (hXJ hbX) (hXC hbX), MonoidHom.map_zpowers, MonoidHom.map_zpowers, hγ]
    rfl
  rw [hzp, B1Red.fixV_map_congr',
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective] at hcard
  have h := (fixV (autSec (Subgroup.zpowers b) J C)).card_mul_index
  rw [h64] at h
  by_contra hlt
  push Not at hlt
  have h7 : (fixV (autSec (Subgroup.zpowers b) J C)).index ≤ 7 := by
    norm_num at hlt
    omega
  have := Nat.mul_le_mul hcard h7
  rw [h] at this
  norm_num at this

theorem index_fixV_zpowers_le {b : MulAut V} {D A₁ : Subgroup V}
    (h : ∀ d ∈ D, b d * d⁻¹ ∈ A₁) :
    (fixV (Subgroup.zpowers b)).index ≤ D.index * Nat.card A₁ := by
  set F := fixV (Subgroup.zpowers b) with hF
  let φ : ↥D →* V :=
    { toFun := fun d => b d * (d : V)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        change b ((x : V) * y) * ((x : V) * y)⁻¹ = b x * (x : V)⁻¹ * (b y * (y : V)⁻¹)
        rw [map_mul, mul_inv, mul_mul_mul_comm] }
  have hker : φ.ker = F.subgroupOf D := by
    ext d
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change b d * (d : V)⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    constructor
    · exact fun hd => mem_fixV_zpowers_of hd
    · exact fun hd => hd b (Subgroup.mem_zpowers b)
  have hrange : Nat.card φ.range ≤ Nat.card A₁ := by
    have hle : φ.range ≤ A₁ := by
      rintro _ ⟨d, rfl⟩
      exact h d d.2
    exact Subgroup.card_le_of_le hle
  have h1 : F.relIndex D ≤ Nat.card A₁ := by
    have := Subgroup.index_ker φ
    rw [hker] at this
    exact (show F.relIndex D = Nat.card φ.range from this).trans_le hrange
  have h2 : F.index ≤ (F ⊓ D).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le inf_le_left)
  have h3 : (F ⊓ D).index = F.relIndex D * D.index := by
    rw [← Subgroup.relIndex_mul_index (inf_le_right : F ⊓ D ≤ D), Subgroup.inf_relIndex_right]
  rw [h3] at h2
  calc F.index ≤ F.relIndex D * D.index := h2
    _ ≤ Nat.card A₁ * D.index := Nat.mul_le_mul_right _ h1
    _ = D.index * Nat.card A₁ := mul_comm _ _

theorem two_factor
    (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hP : B42TypeU33 ↥K)
    {J : Subgroup V} (hKJ : K ≤ stabSub J) (hC₀J : fixV K ≤ J) (hirr : IrrBetween K (fixV K) J)
    (hnt₁ : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ fixV K)
    (hnt₂ : ∃ k ∈ K, ∃ v ∈ (⊤ : Subgroup V), k v * v⁻¹ ∉ J)
    (h64₁ : Nat.card (Sec J (fixV K)) = 2 ^ 6)
    (hnat₁ : G2NaturalDerived (autSec K J (fixV K)) ⊤ ⊥ 1)
    (h64₂ : Nat.card (Sec ⊤ J) = 2 ^ 6) (hnat₂ : G2NaturalDerived (autSec K ⊤ J) ⊤ ⊥ 1)
    {B : Subgroup (MulAut V)} (hBX : B ≤ X) (hB1 : B ≠ ⊥) (hBe : IsElemAbelian2 B)
    (hidx : (fixV B).index ≤ Nat.card B ^ 2) :
    (fixV B).index = Nat.card B ^ 2 ∧ Nat.card B = 8 ∧
      ∃ b ∈ B, b ∉ K ∧ 2 ^ 6 ≤ (fixV (Subgroup.zpowers b)).index := by
  have hBJ : B ≤ stabSub J :=
    stab_of_offender hKX hXN hCK hP hBX hB1 hBe hidx hKJ hC₀J hirr hnt₁ h64₁
  set X' := K ⊔ B with hX'
  have hX'X : X' ≤ X := sup_le hKX hBX
  have hKX' : K ≤ X' := le_sup_left
  have hBX' : B ≤ X' := le_sup_right
  have hX'N : X' ≤ Subgroup.normalizer (K : Set (MulAut V)) := hX'X.trans hXN
  have hX'C : X' ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K :=
    (inf_le_inf_right _ hX'X).trans hCK
  have hX'J : X' ≤ stabSub J := sup_le hKJ hBJ
  have hX'C₀ : X' ≤ stabSub (fixV K) := hX'X.trans (le_stabSub_fixV hXN)
  have hX'T : X' ≤ stabSub (⊤ : Subgroup V) := fun x _ v => by simp
  obtain ⟨h1a, h1b⟩ := sec_offender hKX' hX'N hX'C hX'J hX'C₀ hP hnt₁ hnat₁ hBX' hB1 hBe
  obtain ⟨h2a, -⟩ := sec_offender hKX' hX'N hX'C hX'T hX'J hP hnt₂ hnat₂ hBX' hB1 hBe
  have hmul := index_mul_index_le hC₀J hBJ
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hi₁ : (fixV (autSec B J (fixV K))).index = Nat.card B := by
    by_contra hne
    have hlt := lt_of_le_of_ne h1a (Ne.symm hne)
    have h3 := (Nat.mul_le_mul (Nat.succ_le_of_lt hlt) h2a).trans (hmul.trans hidx)
    rw [Nat.succ_mul, pow_two] at h3
    omega
  have hi₂ : (fixV (autSec B ⊤ J)).index = Nat.card B := by
    by_contra hne
    have hlt := lt_of_le_of_ne h2a (Ne.symm hne)
    have h3 := (Nat.mul_le_mul h1a (Nat.succ_le_of_lt hlt)).trans (hmul.trans hidx)
    rw [Nat.mul_succ, pow_two] at h3
    omega
  obtain ⟨h8, hBK⟩ := h1b hi₁
  refine ⟨le_antisymm hidx ?_, h8, ?_⟩
  · calc Nat.card B ^ 2 =
        (fixV (autSec B J (fixV K))).index * (fixV (autSec B ⊤ J)).index := by
          rw [hi₁, hi₂, pow_two]
      _ ≤ _ := hmul
  obtain ⟨b, hbB, hbK⟩ : ∃ b ∈ B, b ∉ K := by
    by_contra h
    push Not at h
    exact hBK h
  refine ⟨b, hbB, hbK, ?_⟩
  have hb2 : b ^ 2 = 1 := hBe.2 b hbB
  have hbX' : b ∈ X' := hBX' hbB
  have hzJ : Subgroup.zpowers b ≤ stabSub J := Subgroup.zpowers_le.2 (hX'J hbX')
  have e1 := index_fixV_sec_ge hKX' hX'N hX'C hX'J hX'C₀ hP hnt₁ hnat₁ h64₁ hbX' hbK hb2
  have e2 := index_fixV_sec_ge hKX' hX'N hX'C hX'T hX'J hP hnt₂ hnat₂ h64₂ hbX' hbK hb2
  have e3 := index_mul_index_le hC₀J hzJ
  calc 2 ^ 6 = 2 ^ 3 * 2 ^ 3 := by norm_num
    _ ≤ _ := Nat.mul_le_mul e1 e2
    _ ≤ _ := e3

end CFSG.Quasithin.H13.L32A.M753
