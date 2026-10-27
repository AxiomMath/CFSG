module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
public import CFSG.RankThree.PartTwo.Sec21.FF81HL32Recognition
public import CFSG.RankThree.PartTwo.Sec21.FF81S59Sp6
public import CFSG.RankThree.PartTwo.Sec21.FF81S59R
public import CFSG.RankThree.PartTwo.Sec21.FF81S59T
public import CFSG.RankThree.PartTwo.Sec21.FF81S59Inv
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81Sec32A
import CFSG.RankThree.PartTwo.Sec21.FF81J

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def FF81_5_9Act : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (b : G) (L B : Subgroup G) (b₁ b₂ b₃ t₀ s₀ : G),
    FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀ → FF81Conc5_2_6 b b₁ b₂ b₃ s₀ →
    ∀ M : Subgroup G, FF81Conc5_7 b b₁ b₂ b₃ s₀ M → FF81Conc5_8 L t₀ →
      L ⊓ CenS (Op 2 (Cen t₀) ⊓ CenS (Op 2 (Cen t₀))) = ⊥ ∧
      ∀ l ∈ L, (∀ u ∈ Op 2 (Cen t₀),
        l * u * l⁻¹ * u⁻¹ ∈ Op 2 (Cen t₀) ⊓ CenS (Op 2 (Cen t₀))) → l = 1

section TL

variable {G : Type} [Group G] [Finite G]

theorem op_two_isPGroup' (t₀ : G) : IsPGroup 2 (Op 2 (Cen t₀)) :=
  CFSG.pCore_isPGroup.map (Cen t₀).subtype

theorem op_two_le' (t₀ : G) : Op 2 (Cen t₀) ≤ Cen t₀ := Subgroup.map_subtype_le _

theorem op_two_conj' {t₀ g u : G} (hg : g ∈ Cen t₀) (hu : u ∈ Op 2 (Cen t₀)) :
    g * u * g⁻¹ ∈ Op 2 (Cen t₀) := by
  obtain ⟨o', ho', rfl⟩ := hu
  exact ⟨⟨g, hg⟩ * o' * ⟨g, hg⟩⁻¹,
    (CFSG.pCore_normal (p := 2) (G := ↥(Cen t₀))).conj_mem o' ho' ⟨g, hg⟩, by simp⟩

theorem le_cen_of_mem_cenS {L : Subgroup G} {t₀ : G} (ht₀L : t₀ ∈ CenS L) : L ≤ Cen t₀ :=
  fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp ht₀L x hx)

theorem cen_inf_cenS_eq_of_decomp {L T R : Subgroup G} {t₀ : G}
    (hcent : setMul T L = Cen t₀) (hTL : T ⊓ L = ⊥) (hLN : L ≤ Nor T) (hTle : T ≤ Cen t₀)
    (hRL : R ≤ L) (hCLR : L ⊓ CenS R = ⊥) : Cen t₀ ⊓ CenS R = T ⊓ CenS R := by
  refine le_antisymm ?_ (inf_le_inf_right _ hTle)
  rintro x ⟨hx, hxR⟩
  have hx' : x ∈ setMul T L := by rw [hcent]; exact hx
  obtain ⟨u, hu, l, hl, rfl⟩ := hx'
  have hlR : l ∈ CenS R := by
    refine Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
    have hy : l * r * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl (hRL hr)) (L.inv_mem hl)
    have hcomm := Subgroup.mem_centralizer_iff.mp hxR r hr
    have h1 : u * (l * r * l⁻¹) * u⁻¹ = r := by
      calc u * (l * r * l⁻¹) * u⁻¹ = (u * l) * r * (u * l)⁻¹ := by group
        _ = r := by rw [mul_inv_eq_iff_eq_mul]; exact hcomm.symm
    have hT : u * (l * r * l⁻¹) * u⁻¹ * (l * r * l⁻¹)⁻¹ ∈ T := by
      have h2 : (l * r * l⁻¹) * u⁻¹ * (l * r * l⁻¹)⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hLN hy) u⁻¹).mp (T.inv_mem hu)
      have := T.mul_mem hu h2
      rwa [show u * ((l * r * l⁻¹) * u⁻¹ * (l * r * l⁻¹)⁻¹) =
        u * (l * r * l⁻¹) * u⁻¹ * (l * r * l⁻¹)⁻¹ by group] at this
    rw [h1] at hT
    have hL : r * (l * r * l⁻¹)⁻¹ ∈ L := L.mul_mem (hRL hr) (L.inv_mem hy)
    have : r * (l * r * l⁻¹)⁻¹ ∈ T ⊓ L := ⟨hT, hL⟩
    rw [hTL, Subgroup.mem_bot, mul_inv_eq_one] at this
    calc r * l = l * r * l⁻¹ * l := by rw [← this]
      _ = l * r := by group
  have hl1 : l = 1 := by
    have : l ∈ L ⊓ CenS R := ⟨hl, hlR⟩
    rw [hCLR, Subgroup.mem_bot] at this
    exact this
  subst hl1
  rw [mul_one] at hxR ⊢
  exact ⟨hu, hxR⟩

end TL

section CenB

variable {G : Type} [Group G] [Finite G] {b : G} {L B R : Subgroup G} {b₁ b₂ b₃ : G}

theorem cen_inf_cenS_eq_zpowers (hB : FF81Basis b L B b₁ b₂ b₃) (h0 : Opp 3 (Cen b) = ⊥)
    (hRL : R ≤ L) (hCLR : L ⊓ CenS R = ⊥) : Cen b ⊓ CenS R = Subgroup.zpowers b := by
  have hbR : b ∈ CenS R := Subgroup.mem_centralizer_iff.mpr fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC (hRL hr))
  have hzR : Subgroup.zpowers b ≤ CenS R := Subgroup.zpowers_le.mpr hbR
  refine le_antisymm ?_ fun x hx =>
    ⟨(Subgroup.zpowers_le.mpr (b_mem_cen b)) hx, hzR hx⟩
  rintro x ⟨hxb, hxR⟩
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L hB.hyp.model x (hB.hyp.hLN hxb)
  have hdL : l⁻¹ * x ∈ CenS L := Subgroup.mem_centralizer_iff.mpr fun y hy => by
    have h1 := hl y hy
    calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
      _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = l⁻¹ * x * y := by group
  have hdb : l⁻¹ * x ∈ Cen b := (Cen b).mul_mem ((Cen b).inv_mem (hB.hyp.hLC hlL)) hxb
  have hd1 : l⁻¹ * x ∈ Subgroup.zpowers b := by
    have h1 : l⁻¹ * x ∈ Cen b ⊓ CenS L := ⟨hdb, hdL⟩
    rwa [hB.cen_inf_cenS_eq h0] at h1
  have hlR : l ∈ CenS R := by
    have : l = x * (l⁻¹ * x)⁻¹ := by group
    rw [this]
    exact (CenS R).mul_mem hxR ((CenS R).inv_mem (hzR hd1))
  have hl1 : l = 1 := by
    have : l ∈ L ⊓ CenS R := ⟨hlL, hlR⟩
    rw [hCLR, Subgroup.mem_bot] at this
    exact this
  rw [hl1, inv_one, one_mul] at hd1
  exact hd1

end CenB

section VM

variable {G : Type} [Group G] [Finite G]

theorem le_of_two_group {β : G} {M V : Subgroup G} (hβ : orderOf β = 3) (hMβ : M ≤ Cen β)
    (hMC : Subgroup.zpowers β ⊔ M = Cen β) (hinf : Subgroup.zpowers β ⊓ M = ⊥)
    (hV : IsPGroup 2 V) (hVβ : V ≤ Cen β) : V ≤ M := by
  intro v hv
  have hnorm : Subgroup.zpowers β ≤ Subgroup.normalizer (M : Set G) := fun y hy => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_normalizer_fintype fun m hm => ?_
    have hc : m * β = β * m := Subgroup.mem_centralizer_singleton_iff.mp (hMβ hm)
    rw [(Commute.zpow_left (show Commute β m from hc.symm) k).eq]
    rwa [mul_inv_cancel_right]
  have h1 := Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers β) M hnorm
  have hv' : v ∈ (↑(Subgroup.zpowers β ⊔ M) : Set G) := by rw [hMC]; exact hVβ hv
  rw [h1] at hv'
  obtain ⟨y, hy, m, hm, rfl⟩ := hv'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm : Commute (β ^ k) m := by
    have hc : m * β = β * m := Subgroup.mem_centralizer_singleton_iff.mp (hMβ hm)
    exact (Commute.zpow_left (show Commute β m from hc.symm) k)
  obtain ⟨n, hn⟩ := hV ⟨β ^ k * m, hv⟩
  have hn' : (β ^ k * m) ^ 2 ^ n = 1 := congrArg Subtype.val hn
  rw [hcomm.mul_pow] at hn'
  have hy1 : (β ^ k) ^ 2 ^ n = 1 := by
    have h2 : (β ^ k) ^ 2 ^ n = (m ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hn'
    have h3 : (β ^ k) ^ 2 ^ n ∈ Subgroup.zpowers β ⊓ M :=
      ⟨Subgroup.pow_mem _ (Subgroup.zpow_mem_zpowers β k) _, by
        rw [h2]; exact M.inv_mem (M.pow_mem hm _)⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact h3
  have hy3 : (β ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    have : β ^ ((3 : ℕ) : ℤ) = 1 := by
      rw [zpow_natCast, ← hβ]
      exact pow_orderOf_eq_one β
    rw [this, one_zpow]
  have hord : orderOf (β ^ k) = 1 := by
    have d1 : orderOf (β ^ k) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hy1
    have d2 : orderOf (β ^ k) ∣ 3 := orderOf_dvd_of_pow_eq_one hy3
    have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
    exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd d2 d1)
  have hy1' : β ^ k = 1 := orderOf_eq_one_iff.mp hord
  show β ^ k * m ∈ M
  rw [hy1', one_mul]
  exact hm

end VM

section VD8

variable {G : Type} [Group G] [Finite G]

theorem mem_nor_inf_cen {T : Subgroup G} {β γ : G} (hβT : β ∈ Nor T)
    (hβγ : β * γ * β⁻¹ ∈ Subgroup.zpowers γ) : β ∈ Nor (T ⊓ Cen γ) := by
  have hβz : β ∈ Subgroup.normalizer ((Subgroup.zpowers γ : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype fun y hy => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← conj_zpow]
      exact Subgroup.zpow_mem _ hβγ k
  have hβi : β⁻¹ * γ * β ∈ Subgroup.zpowers γ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hβz) γ).mp
      (Subgroup.mem_zpowers γ)
    simpa using this
  refine Subgroup.mem_normalizer_fintype fun v hv => ⟨(Subgroup.mem_normalizer_iff.mp hβT v).mp
    hv.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have hvγ : v * γ = γ * v := Subgroup.mem_centralizer_singleton_iff.mp hv.2
  have hvc : v * (β⁻¹ * γ * β) = (β⁻¹ * γ * β) * v := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hβi
    rw [← hk]
    exact (Commute.zpow_right (show Commute v γ from hvγ) k).eq
  calc β * v * β⁻¹ * γ = β * (v * (β⁻¹ * γ * β)) * β⁻¹ := by group
    _ = β * ((β⁻¹ * γ * β) * v) * β⁻¹ := by rw [hvc]
    _ = γ * (β * v * β⁻¹) := by group

theorem centralizes_of_D8 {V : Subgroup G} (e : ↥V ≃* DihedralGroup 4) {β : G}
    (hβ : β ∈ Nor V) (hβ3 : β ^ 3 = 1) : ∀ v ∈ V, β * v * β⁻¹ = v := by
  have hmap : V.map (MulAut.conj β).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hβ
  let φ : ↥V ≃* ↥V :=
    (V.equivMapOfInjective (MulAut.conj β).toMonoidHom (MulAut.conj β).injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hφ : ∀ v : ↥V, ((φ v : ↥V) : G) = β * (v : G) * β⁻¹ := fun v => rfl
  let ψ : DihedralGroup 4 ≃* DihedralGroup 4 := e.symm.trans (φ.trans e)
  have hφ3 : ∀ v : ↥V, φ (φ (φ v)) = v := fun v => by
    apply Subtype.ext
    simp only [hφ]
    have hβ3' : β * (β * β) = 1 := by rw [← pow_three]; exact hβ3
    calc β * (β * (β * (v : G) * β⁻¹) * β⁻¹) * β⁻¹
        = (β * (β * β)) * (v : G) * (β * (β * β))⁻¹ := by group
      _ = v := by rw [hβ3']; group
  have h3 : ∀ x, ψ (ψ (ψ x)) = x := by
    intro x
    show e (φ (e.symm (e (φ (e.symm (e (φ (e.symm x)))))))) = x
    simp only [MulEquiv.symm_apply_apply]
    rw [hφ3]
    simp
  intro v hv
  have h4 := FF81.S59.dihedral4_aut_cube ψ h3 (e ⟨v, hv⟩)
  have h5 : e (φ ⟨v, hv⟩) = e ⟨v, hv⟩ := by simpa [ψ] using h4
  exact congrArg Subtype.val (e.injective h5)

end VD8

section Beta

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem orderOf_β (hB : FF81Basis b L B b₁ b₂ b₃) : orderOf (β' b₂ b₃) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨h1, h2, h3⟩, ⟨h12, h13, h23⟩⟩ := triple_facts hB.elem
  have hE : IsElemAb 3 3 (Subgroup.closure ({b₂, b₃, b₁} : Set G)) :=
    (isElemAb_perm (isElemAb_perm hB.elem).2.2).2.2
  have hne := ne_of_basis hE
  have hb3inv : b₃ ^ 2 = b₃⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h3])
  refine orderOf_eq_prime ?_ ?_
  · show (b₂ * b₃ ^ 2) ^ 3 = 1
    rw [(Commute.mul_pow (show Commute b₂ (b₃ ^ 2) from (Commute.pow_right h23 2)) 3), h2,
      ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, h3, one_pow, one_mul]
  · intro h
    apply hne
    left
    show b₂ = b₃
    have : b₂ * b₃⁻¹ = 1 := by rw [← hb3inv]; exact h
    exact mul_inv_eq_one.mp this

end Beta

section TLFacts

variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem le_nor_op_two {t₀ : G} (ht₀L : t₀ ∈ CenS L) : L ≤ Nor (Op 2 (Cen t₀)) := fun l hl =>
  Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => op_two_conj' (le_cen_of_mem_cenS ht₀L hl) hs,
    fun hs => by
      have := op_two_conj' ((Cen t₀).inv_mem (le_cen_of_mem_cenS ht₀L hl)) hs
      rwa [show l⁻¹ * (l * s * l⁻¹) * l⁻¹⁻¹ = s by group] at this⟩

theorem op_two_inf_eq_bot (hB : FF81Basis b L B b₁ b₂ b₃) {t₀ : G} (ht₀L : t₀ ∈ CenS L) :
    Op 2 (Cen t₀) ⊓ L = ⊥ := by
  have hLt : L ≤ Cen t₀ := le_cen_of_mem_cenS ht₀L
  have hTp : IsPGroup 2 (Op 2 (Cen t₀)) := op_two_isPGroup' t₀
  haveI : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1
      hB.hyp.model
  haveI hn : ((Op 2 (Cen t₀) ⊓ L).subgroupOf L).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨op_two_conj' (hLt g.2) hn.1, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Op 2 (Cen t₀) ⊓ L).subgroupOf L) with h | h
  · refine eq_bot_iff.mpr fun x hx => ?_
    have : (⟨x, hx.2⟩ : L) ∈ (Op 2 (Cen t₀) ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  · exfalso
    have hLT : L ≤ Op 2 (Cen t₀) := fun x hx => by
      have : (⟨x, hx⟩ : L) ∈ (Op 2 (Cen t₀) ⊓ L).subgroupOf L := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).1
    obtain ⟨n, hn⟩ := (hTp.to_le hLT).exists_card_eq
    rw [hB.hyp.card_L] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; norm_num
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

end TLFacts

section Assemble

variable {G : Type} [Group G] [Finite G]

theorem inv_conj_eq_pow_five {γ h : G} (hγ7 : γ ^ 7 = 1) (hh : h * γ * h⁻¹ = γ ^ 3) :
    h⁻¹ * γ * h⁻¹⁻¹ = γ ^ 5 := by
  have h1 : (h⁻¹ * γ * h⁻¹⁻¹) ^ 3 = γ := by
    rw [conj_pow]
    calc h⁻¹ * γ ^ 3 * h⁻¹⁻¹ = h⁻¹ * (h * γ * h⁻¹) * h⁻¹⁻¹ := by rw [hh]
      _ = γ := by group
  have h7 : (h⁻¹ * γ * h⁻¹⁻¹) ^ 7 = 1 := by
    rw [conj_pow, hγ7]
    group
  calc h⁻¹ * γ * h⁻¹⁻¹ = (h⁻¹ * γ * h⁻¹⁻¹) ^ 15 := by
        rw [show 15 = 7 * 2 + 1 by norm_num, pow_succ, pow_mul, h7, one_pow, one_mul]
    _ = ((h⁻¹ * γ * h⁻¹⁻¹) ^ 3) ^ 5 := by rw [← pow_mul]
    _ = γ ^ 5 := by rw [h1]

theorem tSetup_of {T₀ T₁ T : Subgroup G} (hT0 : IsElemAb 2 6 T₀)
    (hT1 : IsExtraspecialPlus 4 T₁) (hinf : T₀ ⊓ T₁ = ⊥) (hcen : T₀ ≤ CenS T₁)
    (hTeq : T₀ ⊔ T₁ = T) {γ h : G} (hγT : γ ∈ Nor T) (hhT : h ∈ Nor T) (hγ7 : γ ^ 7 = 1)
    (hh : h * γ * h⁻¹ = γ ^ 3) (nt1 : ∃ z ∈ T ⊓ CenS T, γ * z ≠ z * γ)
    (nt2 : ∃ u ∈ T, γ * u * γ⁻¹ * u⁻¹ ∉ T ⊓ CenS T) : TSetup T γ h h⁻¹ := by
  subst hTeq
  exact ⟨card_sup hT0 hT1 hinf hcen, card_center hT0 hT1 hinf hcen, sq_center hT0 hT1 hinf hcen,
    sq_mem_center hT0 hT1 hinf hcen, comm_mem_center hT0 hT1 hinf hcen, hγT, hhT,
    Subgroup.inv_mem _ hhT, hγ7, hh, inv_conj_eq_pow_five hγ7 hh, nt1, nt2⟩

theorem nt_of_act {L T : Subgroup G} {γ : G} (hγL : γ ∈ L) (hγ1 : γ ≠ 1)
    (hf1 : L ⊓ CenS (T ⊓ CenS T) = ⊥)
    (hf2 : ∀ l ∈ L, (∀ u ∈ T, l * u * l⁻¹ * u⁻¹ ∈ T ⊓ CenS T) → l = 1) :
    (∃ z ∈ T ⊓ CenS T, γ * z ≠ z * γ) ∧ ∃ u ∈ T, γ * u * γ⁻¹ * u⁻¹ ∉ T ⊓ CenS T := by
  constructor
  · by_contra hcon
    push Not at hcon
    apply hγ1
    have : γ ∈ L ⊓ CenS (T ⊓ CenS T) :=
      ⟨hγL, Subgroup.mem_centralizer_iff.mpr fun z hz => (hcon z hz).symm⟩
    rw [hf1, Subgroup.mem_bot] at this
    exact this
  · by_contra hcon
    push Not at hcon
    exact hγ1 (hf2 γ hγL hcon)

theorem le_cenS_of_orders {R V : Subgroup G} (hR : IsLnq 3 2 1 R) {γ β s : G} (hγ : γ ∈ R)
    (hβ : β ∈ R) (hs : s ∈ R) (hγ7 : orderOf γ = 7) (hβ3 : orderOf β = 3)
    (hs2 : orderOf s = 2) (hVγ : V ≤ Cen γ) (hVβ : V ≤ Cen β) (hVs : V ≤ Cen s) :
    V ≤ CenS R := by
  have hmem : ∀ x : G, x ∈ R → V ≤ Cen x → x ∈ R ⊓ CenS V := fun x hx hVx =>
    ⟨hx, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      Subgroup.mem_centralizer_singleton_iff.mp (hVx hv)⟩
  have hK : R ⊓ CenS V = R :=
    eq_of_orders_in hR inf_le_left ⟨γ, hmem γ hγ hVγ, hγ7⟩ ⟨β, hmem β hβ hVβ, hβ3⟩
      ⟨s, hmem s hs hVs, hs2⟩
  refine le_cenS_of_le (fun r hr => ?_)
  have : r ∈ R ⊓ CenS V := by rw [hK]; exact hr
  exact this.2

end Assemble

section Main

theorem ff81_5_9_core (hL : KF_L32Recognition) {G : Type} [Group G] [Finite G] {b : G}
    {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G} (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
    (h526 : FF81Conc5_2_6 b b₁ b₂ b₃ s₀) {M : Subgroup G} (hM7 : FF81Conc5_7 b b₁ b₂ b₃ s₀ M)
    (h58 : FF81Conc5_8 L t₀) (hf1 : L ⊓ CenS (Op 2 (Cen t₀) ⊓ CenS (Op 2 (Cen t₀))) = ⊥)
    (hf2 : ∀ l ∈ L, (∀ u ∈ Op 2 (Cen t₀),
      l * u * l⁻¹ * u⁻¹ ∈ Op 2 (Cen t₀) ⊓ CenS (Op 2 (Cen t₀))) → l = 1)
    {R : Subgroup G} (hRL : R ≤ L) (hR : IsLnq 3 2 1 R)
    (hRs : Subgroup.closure {β' b₂ b₃, s₀} ≤ R) : IsLnq 3 2 1 (CenS R) := by
  have hB := h5.basis
  obtain ⟨h0, -⟩ := h526
  obtain ⟨hcent, T₀, T₁, hT0, hT1, hTeq, hinf, hcen⟩ := h58
  obtain ⟨hMs, -, -, hMC, hMinf, -⟩ := hM7
  have hβ3 : orderOf (β' b₂ b₃) = 3 := orderOf_β hB
  have hβR : β' b₂ b₃ ∈ R := hRs (Subgroup.subset_closure (Set.mem_insert _ _))
  have hs₀R : s₀ ∈ R :=
    hRs (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hβL : β' b₂ b₃ ∈ L := hRL hβR
  obtain ⟨γ, hγR, hγ7, hβγ⟩ := exists_seven_in hR hβR hβ3
  have hγL : γ ∈ L := hRL hγR
  have hγ7' : γ ^ 7 = 1 := by rw [← hγ7]; exact pow_orderOf_eq_one γ
  have hγ1 : γ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hγ7
    omega
  obtain ⟨hcγ, h, hhL, hhγ⟩ := sp6_seven hB.hyp.model hγL hγ7
  have hCLR : L ⊓ CenS R = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxγ : x * γ = γ * x := (Subgroup.mem_centralizer_iff.mp hx.2 γ hγR).symm
    have hxR : x ∈ R := Subgroup.zpowers_le.mpr hγR (hcγ x hx.1 hxγ)
    exact Subgroup.mem_bot.mpr (eq_one_of_central_in hR hxR fun r hr =>
      (Subgroup.mem_centralizer_iff.mp hx.2 r hr).symm)
  have hLN : L ≤ Nor (Op 2 (Cen t₀)) := le_nor_op_two h5.ht₀L
  have hTL : Op 2 (Cen t₀) ⊓ L = ⊥ := op_two_inf_eq_bot hB h5.ht₀L
  have hTle : Op 2 (Cen t₀) ≤ Cen t₀ := op_two_le' t₀
  obtain ⟨nt1, nt2⟩ := nt_of_act hγL hγ1 hf1 hf2
  have hTS : TSetup (Op 2 (Cen t₀)) γ h h⁻¹ :=
    tSetup_of hT0 hT1 hinf hcen hTeq (hLN hγL) (hLN hhL) hγ7' hhγ nt1 nt2
  have hV8 : Nat.card ↥(Op 2 (Cen t₀) ⊓ Cen γ) = 8 := card_T_cen hTS
  have hN : Nat.card {u : G // u ∈ Op 2 (Cen t₀) ∧ u ^ 2 = 1} = 17408 := by
    have := card_sq_T hT0 hT1 hinf hcen
    rwa [hTeq] at this
  obtain ⟨eV⟩ := nonempty_mulEquiv_D8 hγ7' (hLN hγL) hN hV8
  have hβ3' : β' b₂ b₃ ^ 3 = 1 := by rw [← hβ3]; exact pow_orderOf_eq_one _
  have hβV : β' b₂ b₃ ∈ Nor (Op 2 (Cen t₀) ⊓ Cen γ) := mem_nor_inf_cen (hLN hβL) hβγ
  have hβcomm := centralizes_of_D8 eV hβV hβ3'
  have hVβ : Op 2 (Cen t₀) ⊓ Cen γ ≤ Cen (β' b₂ b₃) := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hβcomm v hv)).symm
  have hMβ : M ≤ Cen (β' b₂ b₃) := hMC ▸ le_sup_right
  have hV2 : IsPGroup 2 ↥(Op 2 (Cen t₀) ⊓ Cen γ) :=
    IsPGroup.of_card (n := 3) (by rw [hV8]; norm_num)
  have hVM : Op 2 (Cen t₀) ⊓ Cen γ ≤ M := le_of_two_group hβ3 hMβ hMC hMinf hV2 hVβ
  have hVs : Op 2 (Cen t₀) ⊓ Cen γ ≤ Cen s₀ := fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hMs (hVM hv)) s₀
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))).symm
  have hVR : Op 2 (Cen t₀) ⊓ Cen γ ≤ CenS R :=
    le_cenS_of_orders hR hγR hβR hs₀R hγ7 hβ3 h5.hs₀ inf_le_right hVβ hVs
  have hXt : Cen t₀ ⊓ CenS R = Op 2 (Cen t₀) ⊓ CenS R :=
    cen_inf_cenS_eq_of_decomp hcent hTL hLN hTle hRL hCLR
  have hTCR : Op 2 (Cen t₀) ⊓ CenS R = Op 2 (Cen t₀) ⊓ Cen γ := by
    refine le_antisymm (fun x hx => ⟨hx.1, ?_⟩) (fun x hx => ⟨hx.1, hVR hx⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hx.2 γ hγR).symm
  have hD8 : Nonempty (↥(Cen t₀ ⊓ CenS R) ≃* DihedralGroup 4) :=
    ⟨(MulEquiv.subgroupCongr (hXt.trans hTCR)).trans eV⟩
  have hbR : b ∈ CenS R := Subgroup.mem_centralizer_iff.mpr fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC (hRL hr))
  have htR : t₀ ∈ CenS R := Subgroup.centralizer_le hRL h5.ht₀L
  have hCb : Cen b ⊓ CenS R = Subgroup.zpowers b := cen_inf_cenS_eq_zpowers hB h0 hRL hCLR
  exact isLnq_of_l32_data hL (CenS R) hbR htR hB.hyp.ord hCb h5.ht₀ h5.ht₀b hD8

theorem ff81_5_9_of_l32 (hL : KF_L32Recognition) (hres : FF81_5_9Act) : FF81_5_9 := by
  intro G _ _ b L B b₁ b₂ b₃ t₀ s₀ h5 h526 M hM7 h58 R hRL hR hRs
  obtain ⟨hf1, hf2⟩ := hres G b L B b₁ b₂ b₃ t₀ s₀ h5 h526 M hM7 h58
  exact ff81_5_9_core hL h5 h526 hM7 h58 hf1 hf2 hRL hR hRs

section Certificates


theorem ff81_5_9_of (hres : FF81_5_9Act) : FF81_5_9 :=
  ff81_5_9_of_l32 kf_l32Recognition hres

end Certificates

end Main

end CFSG.RankThree.PartTwo.Sec21.FF81.S59
