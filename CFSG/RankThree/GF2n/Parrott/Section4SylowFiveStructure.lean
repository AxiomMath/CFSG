module

public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.RankThree.GF2n.Parrott.Section4SylowFiveFusion
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.RankThree.GF2n.Parrott.Section4FixDimBridge
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

section Certified


theorem card_inf_J_of_isSylowOf_five (h : Tim79a.ParrottHyp z)
    {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z)) : Nat.card ↥(B ⊓ J z) = 1 := by
  have hB5c : Nat.card B = 5 := card_eq_five_of_isSylowOf_five h hB5
  have h1 : Nat.card ↥(B ⊓ J z) ∣ 5 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : B ⊓ J z ≤ B)
    rwa [hB5c] at this
  have h2 : Nat.card ↥(B ⊓ J z) ∣ 2 ^ 10 := by
    have := Subgroup.card_dvd_of_le (inf_le_right : B ⊓ J z ≤ J z)
    rwa [card_J h] at this
  have h3 := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 5 (2 ^ 10) = 1 by norm_num] at h3
  exact Nat.dvd_one.mp h3

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

theorem card_imageQA45_of_isSylowOf_five (h : Tim79a.ParrottHyp z) {B : Subgroup G}
    (hB5 : IsSylowOf 5 B (H z)) : Nat.card (imageQA45 D hB5.le) = 5 := by
  have h1 := card_eq_card_inf_J_mul_card_imageQA45 D hB5.le
  rw [card_eq_five_of_isSylowOf_five h hB5, card_inf_J_of_isSylowOf_five h hB5, one_mul] at h1
  exact h1.symm

theorem exists_sylowTwo_inf_centralizer_five (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hV5 : ∀ y : ↥(H z), orderOf (qH D y) = 5 → fixDimV h y = 0)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → Nat.card (centralizer (B : Set A45)) = 10)
    {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z)) {x₀ : G} (hx₀H : x₀ ∈ H z)
    (hx₀x₀ : x₀ * x₀ = 1) (hx₀N : x₀ ∉ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hx₀B : ∀ b ∈ B, x₀ * b = b * x₀) :
    ∃ Y₀ : Subgroup G, IsSylowOf 2 Y₀ (H z ⊓ centralizer (B : Set G)) ∧ Nat.card Y₀ = 8 ∧
      centerIn (J z) ≤ Y₀ ∧ x₀ ∈ Y₀ ∧
      ∀ w ∈ Y₀, w ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) → w ∈ centerIn (J z) := by
  have hBH : B ≤ H z := hB5.le
  have hB5c : Nat.card B = 5 := card_eq_five_of_isSylowOf_five h hB5
  have hZJ : centerIn (J z) ≤ J z := inf_le_left
  have hZcen : ∀ e ∈ centerIn (J z), ∀ g ∈ H z, g * e = e * g := by
    intro e he g hg
    have heH : e ∈ centerIn (H z) := hZ ▸ he
    exact mem_centralizer_iff.mp heH.2 g hg
  have hBJ : Nat.card ↥(B ⊓ J z) = 1 := card_inf_J_of_isSylowOf_five h hB5
  have hBbar : Nat.card (imageQA45 D hBH) = 5 := card_imageQA45_of_isSylowOf_five D h hB5
  have hBne : B ≠ ⊥ := fun hbot => by
    have : Nat.card B = 1 := by rw [hbot]; simp
    omega
  obtain ⟨b', hb'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hbB : (b' : G) ∈ B := b'.2
  have hb1 : (b' : G) ≠ 1 := fun h1 => hb'1 (Subtype.ext h1)
  have hb5 : (b' : G) ^ 5 = 1 := by
    have := pow_card_eq_one' (G := B) (x := b')
    rw [hB5c] at this
    exact congrArg Subtype.val this
  have hbH : (b' : G) ∈ H z := hBH hbB
  have hbnJ : (⟨(b' : G), hbH⟩ : ↥(H z)) ∉ (J z).subgroupOf (H z) := by
    intro hmem
    have hbJ : (b' : G) ∈ J z := hmem
    have hbot : B ⊓ J z = ⊥ := Subgroup.card_eq_one.mp hBJ
    have : (b' : G) ∈ B ⊓ J z := mem_inf.mpr ⟨hbB, hbJ⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hb1 this
  have hord : orderOf (qH D ⟨(b' : G), hbH⟩) = 5 := by
    apply orderOf_eq_prime
    · rw [← map_pow]
      have : (⟨(b' : G), hbH⟩ : ↥(H z)) ^ 5 = 1 := Subtype.ext hb5
      rw [this, map_one]
    · intro h1
      exact hbnJ ((J_mem_iff D _).mpr h1)
  have hfix0 := hV5 _ hord
  have hfixbot : autFixedSubgroup (conjV h ⟨(b' : G), hbH⟩) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [card_fix h ⟨(b' : G), hbH⟩, hfix0]
    rfl
  set C : Subgroup G := H z ⊓ centralizer (B : Set G) with hC
  have hCH : C ≤ H z := inf_le_left
  have hCJ : C ⊓ J z = centerIn (J z) := by
    apply le_antisymm
    · intro j hj
      obtain ⟨hjC, hjJ⟩ := mem_inf.mp hj
      have hbj : (b' : G) * j = j * (b' : G) := mem_centralizer_iff.mp (mem_inf.mp hjC).2 _ hbB
      have hfx := pi_mem_autFixedSubgroup_conjV h hjJ (x := ⟨(b' : G), hbH⟩) hbj
      rw [hfixbot, Subgroup.mem_bot] at hfx
      have hker : (⟨j, hjJ⟩ : ↥(J z)) ∈ (QuotientV.pi z).ker := hfx
      rw [QuotientV.pi_ker, Subgroup.mem_subgroupOf] at hker
      exact hker
    · intro e he
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨J_le_H (hZJ he), ?_⟩, hZJ he⟩
      rw [mem_centralizer_iff]
      intro g hg
      exact hZcen e he g (hBH hg)
  have hZC : centerIn (J z) ≤ C := by
    rw [← hCJ]
    exact inf_le_left
  have himg : imageQA45 D hCH ≤ centralizer ((imageQA45 D hBH : Subgroup A45) : Set A45) := by
    intro a ha
    obtain ⟨k, hk, rfl⟩ := (mem_imageQA45_iff D hCH a).mp ha
    rw [mem_centralizer_iff]
    intro c' hc'
    obtain ⟨b'', hb'', rfl⟩ := (mem_imageQA45_iff D hBH c').mp hc'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact mem_centralizer_iff.mp (mem_inf.mp hk).2 b'' hb''
  have himgdvd : Nat.card (imageQA45 D hCH) ∣ 10 := by
    have := Subgroup.card_dvd_of_le himg
    rwa [hC5 _ hBbar] at this
  have hCcard := card_eq_card_inf_J_mul_card_imageQA45 D hCH
  rw [hCJ, card_centerIn_J h] at hCcard
  have hCdvd : Nat.card C ∣ 40 := by
    rw [hCcard]
    exact Nat.mul_dvd_mul_left 4 himgdvd
  have hx₀C : x₀ ∈ C :=
    mem_inf.mpr ⟨hx₀H, mem_centralizer_iff.mpr fun b'' hb'' => (hx₀B b'' hb'').symm⟩
  have hx₀2 : orderOf x₀ = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hx₀x₀) (fun h1 => hx₀N (by rw [h1]; exact one_mem _))
  have hx₀p : IsPGroup 2 (zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx₀2, pow_one])
  obtain ⟨Q, hQ⟩ := (hx₀p.comap_subtype (K := C)).exists_le_sylow
  have hY₀ : IsSylowOf 2 ((Q : Subgroup C).map C.subtype) C := ⟨Q, rfl⟩
  have hx₀Y : x₀ ∈ (Q : Subgroup C).map C.subtype :=
    ⟨⟨x₀, hx₀C⟩, hQ (show (⟨x₀, hx₀C⟩ : C) ∈ (zpowers x₀).subgroupOf C from mem_zpowers x₀), rfl⟩
  set Y₀ : Subgroup G := (Q : Subgroup C).map C.subtype with hY₀def
  have hZY : centerIn (J z) ≤ Y₀ := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hY₀ (N := centerIn (J z)) hZC ?_
      (IsPGroup.of_card (n := 2) (by rw [card_centerIn_J h]; norm_num))
    intro c hc
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro e he
    exact (hZcen e he c (hCH hc)).symm
  have hZN : centerIn (J z) ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) := le_sup_right
  have hx₀Z : x₀ ∉ centerIn (J z) := fun hx => hx₀N (hZN hx)
  have hY₀dvd : Nat.card Y₀ ∣ 40 := (Subgroup.card_dvd_of_le hY₀.le).trans hCdvd
  obtain ⟨k, hk⟩ : ∃ k, Nat.card Y₀ = 2 ^ k := by
    have := hY₀.card_eq
    exact ⟨_, this⟩
  have hk3 : k ≤ 3 := by
    by_contra hcon
    have h16 : 2 ^ 4 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    rw [← hk] at h16
    have := h16.trans hY₀dvd
    omega
  have hZlt : Nat.card (centerIn (J z)) < Nat.card Y₀ := by
    have hle := Subgroup.card_le_of_le hZY
    refine lt_of_le_of_ne hle (fun heq => hx₀Z ?_)
    have := Subgroup.eq_of_le_of_card_ge hZY (le_of_eq heq.symm)
    rw [this]
    exact hx₀Y
  have hk3' : k = 3 := by
    rw [card_centerIn_J h, hk] at hZlt
    interval_cases k <;> first | rfl | (exfalso; norm_num at hZlt)
  have hY₀c : Nat.card Y₀ = 8 := by
    rw [hk, hk3']
    norm_num
  refine ⟨Y₀, hY₀, hY₀c, hZY, hx₀Y, ?_⟩
  intro w hw hwN
  have hZS : centerIn (J z) ≤ Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z)) := le_inf hZY hZN
  have h4 : 4 ∣ Nat.card ↥(Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z))) := by
    rw [← card_centerIn_J h]
    exact Subgroup.card_dvd_of_le hZS
  have h8 : Nat.card ↥(Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z))) ∣ 8 := by
    rw [← hY₀c]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hpos : 0 < Nat.card ↥(Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z))) := Nat.card_pos
  have hne : Nat.card ↥(Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z))) ≠ 8 := by
    intro h8'
    have heq : Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z)) = Y₀ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8', hY₀c])
    apply hx₀N
    have hx : x₀ ∈ Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z)) := by
      rw [heq]
      exact hx₀Y
    exact (mem_inf.mp hx).2
  have hS4 : Nat.card ↥(Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z))) = 4 := by
    obtain ⟨m, hm⟩ := h4
    have hle := Nat.le_of_dvd (by norm_num) h8
    omega
  have hSeq : centerIn (J z) = Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z)) :=
    Subgroup.eq_of_le_of_card_ge hZS (by rw [hS4, card_centerIn_J h])
  have hwS : w ∈ Y₀ ⊓ (⁅H z, H z⁆ ⊔ centerIn (J z)) := mem_inf.mpr ⟨hw, hwN⟩
  rw [← hSeq] at hwS
  exact hwS

theorem isConj_qH_of_involution_mem_centralizer_five (h : Tim79a.ParrottHyp z)
    (hC5 : ∀ B : Subgroup A45, Nat.card B = 5 → ∃ w : A45, orderOf w = 2 ∧ IsConj w (uA * vA) ∧
      centralizer (B : Set A45) = B ⊔ zpowers w)
    {B : Subgroup G} (hB5 : IsSylowOf 5 B (H z)) {x₀ : G} (hx₀H : x₀ ∈ H z)
    (hx₀x₀ : x₀ * x₀ = 1) (hx₀J : x₀ ∉ J z) (hx₀B : ∀ b ∈ B, x₀ * b = b * x₀) :
    IsConj (qH D ⟨x₀, hx₀H⟩) (uA * vA) := by
  have hBH : B ≤ H z := hB5.le
  have hBbar : Nat.card (imageQA45 D hBH) = 5 := card_imageQA45_of_isSylowOf_five D h hB5
  obtain ⟨w, hw2, hwc, hCeq⟩ := hC5 _ hBbar
  have hxcen : qH D ⟨x₀, hx₀H⟩ ∈ centralizer ((imageQA45 D hBH : Subgroup A45) : Set A45) := by
    rw [mem_centralizer_iff]
    intro c' hc'
    obtain ⟨b'', hb'', rfl⟩ := (mem_imageQA45_iff D hBH c').mp hc'
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (hx₀B b'' hb'').symm
  rw [hCeq] at hxcen
  have hwcen : ∀ a ∈ imageQA45 D hBH, a * w = w * a := by
    intro a ha
    have hw : w ∈ centralizer ((imageQA45 D hBH : Subgroup A45) : Set A45) := by
      rw [hCeq]
      exact Subgroup.mem_sup_right (mem_zpowers w)
    exact mem_centralizer_iff.mp hw a ha
  have hcomm : ∀ a ∈ imageQA45 D hBH, ∀ c ∈ zpowers w, Commute a c := by
    intro a ha c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    exact (show Commute a w from hwcen a ha).zpow_right k
  obtain ⟨a, ha, c, hc, hac⟩ := (CFSG.mem_sup_of_commute hcomm).mp hxcen
  have hxx : qH D ⟨x₀, hx₀H⟩ * qH D ⟨x₀, hx₀H⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x₀, hx₀H⟩ : ↥(H z)) * ⟨x₀, hx₀H⟩ = 1 := Subtype.ext hx₀x₀
    rw [this, map_one]
  have hc2 : c * c = 1 := by
    rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hw2 hc with rfl | rfl
    · exact one_mul 1
    · have := pow_orderOf_eq_one c
      rwa [hw2, pow_two] at this
  have ha2 : a * a = 1 := by
    have h1 : (a * c) * (a * c) = a * a * (c * c) := by
      calc (a * c) * (a * c) = a * (c * a) * c := by group
        _ = a * (a * c) * c := by rw [(hcomm a ha c hc).eq.symm]
        _ = a * a * (c * c) := by group
    rw [hac, hxx, hc2, mul_one] at h1
    exact h1.symm
  have ha5 : a ^ 5 = 1 := by
    have := pow_card_eq_one' (G := imageQA45 D hBH) (x := ⟨a, ha⟩)
    rw [hBbar] at this
    exact congrArg Subtype.val this
  have ha1 : a = 1 := by
    have h2 : a ^ 2 = 1 := by rwa [pow_two]
    calc a = a ^ 5 * ((a ^ 2)⁻¹) ^ 2 := by group
      _ = 1 := by rw [ha5, h2]; simp
  have hx1 : qH D ⟨x₀, hx₀H⟩ ≠ 1 := fun h1 => hx₀J ((J_mem_iff D _).mpr h1)
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hw2 hc with hc1 | hcw
  · exact absurd (by rw [← hac, ha1, hc1, one_mul]) hx1
  · have : qH D ⟨x₀, hx₀H⟩ = w := by rw [← hac, ha1, hcw, one_mul]
    rw [this]
    exact hwc

theorem fixDimV_eq_of_conj_rep (h : Tim79a.ParrottHyp z)
    (ρ : QA45.originalSubgroup →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (P : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2))
    (hP : ∀ a, actionQA45 (z := z) h D a = P * ρ a * P⁻¹) (S : A45 → Prop) (c : ℕ)
    (hρ : ∀ a : A45, S a →
      fixCard (((ρ a : Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) = 2 ^ c) :
    ∀ x : ↥(H z), S (qH D x) → fixDimV h x = c := by
  intro x hx
  have h1 := two_pow_fixDimV_eq_of_conj_rep D h ρ P hP x
  rw [hρ _ hx] at h1
  exact Nat.pow_right_injective (le_refl 2) h1

end Certified

end CFSG.RankThree.GF2n.Parrott
