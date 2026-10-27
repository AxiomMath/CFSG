module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeWeights
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3CorrL3aFix
import CFSG.GH74.GLS.Bg.TwoGroups.Lemma218a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private theorem s1614_ce_card_sup_mul_card_inf_of_normal {X : Type*} [Group X]
    (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) =
      Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

private theorem s1614_ce_card_sup_mul_card_inf {X : Type*} [Group X] {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) =
      Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set X)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := s1614_ce_card_sup_mul_card_inf_of_normal (A.subgroupOf N) (B.subgroupOf N)
  have hc : ∀ Y : Subgroup X, Y ≤ N → Nat.card (Y.subgroupOf N) = Nat.card Y := fun Y hY =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY).toEquiv
  have hsup : A.subgroupOf N ⊔ B.subgroupOf N = (A ⊔ B).subgroupOf N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAN, inf_eq_left.mpr hB,
      inf_eq_left.mpr (sup_le hAN hB)]
  have hinf : A.subgroupOf N ⊓ B.subgroupOf N = (A ⊓ B).subgroupOf N :=
    Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  exact h

private theorem s1614_ce_comm_of_le {G : Type*} [Group G] {A X Y : Subgroup G}
    (hA : IsMulCommutative ↥A) (hX : X ≤ A) (hY : Y ≤ A) :
    ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hX hx⟩ ⟨y, hY hy⟩)

private theorem s1614_ce_comm_of_eq_sup {G : Type*} [Group G] {P Z L : Subgroup G}
    (hLeq : L = P ⊔ Z) (hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    (hZcent : ∀ z ∈ Z, ∀ y ∈ L, z * y = y * z)
    (hZnorm : Z ≤ Subgroup.normalizer (P : Set G))
    (hPL : P ≤ L) (hZL : Z ≤ L) :
    ∀ a ∈ L, ∀ b ∈ L, a * b = b * a := by
  intro a ha b hb
  have ha' : a ∈ (↑(P ⊔ Z) : Set G) := by rw [← hLeq]; exact ha
  have hb' : b ∈ (↑(P ⊔ Z) : Set G) := by rw [← hLeq]; exact hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left P Z hZnorm] at ha' hb'
  obtain ⟨p1, hp1, z1, hz1, hpz1⟩ := Set.mem_mul.mp ha'
  obtain ⟨p2, hp2, z2, hz2, hpz2⟩ := Set.mem_mul.mp hb'
  have hz1p2 : z1 * p2 = p2 * z1 := hZcent z1 hz1 p2 (hPL hp2)
  have hz2p1 : z2 * p1 = p1 * z2 := hZcent z2 hz2 p1 (hPL hp1)
  have hp12 : p1 * p2 = p2 * p1 := hPcomm p1 hp1 p2 hp2
  have hz12 : z1 * z2 = z2 * z1 := hZcent z1 hz1 z2 (hZL hz2)
  rw [← hpz1, ← hpz2]
  calc
    (p1 * z1) * (p2 * z2) = p1 * (z1 * p2) * z2 := by group
    _ = p1 * (p2 * z1) * z2 := by rw [hz1p2]
    _ = (p1 * p2) * (z1 * z2) := by group
    _ = (p2 * p1) * (z1 * z2) := by rw [hp12]
    _ = p2 * p1 * (z1 * z2) := by group
    _ = p2 * p1 * (z2 * z1) := by rw [hz12]
    _ = p2 * (p1 * (z2 * z1)) := by group
    _ = p2 * ((p1 * z2) * z1) := by group
    _ = p2 * ((z2 * p1) * z1) := by rw [hz2p1]
    _ = (p2 * z2) * (p1 * z1) := by group

theorem s1614_central_eq {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {L : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L) {ℓ : ↥L}
    (hℓ : ℓ ∈ Subgroup.center ↥L) (hℓ1 : ℓ ≠ 1) {v : MulAut W} (hv3 : v * v * v = 1)
    (hvL : ∀ y ∈ L, v * y = y * v) : v ∈ Subgroup.zpowers (ℓ : MulAut W) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  let z : MulAut W := (ℓ : MulAut W)
  have hz3 : z * z * z = 1 := by
    have h := congrArg (fun y : ↥L => (y : MulAut W)) (hL.2.2 ℓ)
    simpa [z, Subgroup.coe_pow, pow_three'] using h
  have hzfix : ∀ x : W, z x = x → x = 1 := fun x hx =>
    s16c167_central_fixed_point_free hW hcard hL hℓ hℓ1 hx
  have hvz : v * z = z * v := hvL (ℓ : MulAut W) ℓ.2
  have hmain := s1614_weights hW hz3 hv3 hvz hzfix
  let U : Fin 3 → Subgroup W := fun j => fixV (Subgroup.zpowers (v * z ^ (j : ℕ)))
  have hsup : ⨆ j : Fin 3, U j = ⊤ := hmain.2
  have hinv : ∀ j : Fin 3, ∀ y ∈ L, ∀ u ∈ U j, y u ∈ U j := by
    intro j y hy u hu
    rw [mem_fixV_zpowers_iff_apply] at hu ⊢
    have hyz_eq : y * z = z * y := by
      have h := congrArg (fun a : ↥L => (a : MulAut W))
        (Subgroup.mem_center_iff.1 hℓ ⟨y, hy⟩)
      simpa [z, Subgroup.coe_mul] using h
    have hyz : Commute y z := hyz_eq
    have hyv : Commute y v := (hvL y hy).symm
    have hyw : Commute y (v * z ^ (j : ℕ)) :=
      hyv.mul_right (hyz.pow_right (j : ℕ))
    have happ := congrArg (fun f : MulAut W => f u) hyw
    simp only [MulAut.mul_apply] at happ
    have hu' : v ((z ^ (j : ℕ)) u) = u := hu
    rw [hu'] at happ
    exact happ.symm
  have hpartition : ∀ j : Fin 3, U j = ⊥ ∨ U j = ⊤ := by
    intro j
    rcases s16c167_invariant_eq_bot_or_card hW hcard hL (U j) (hinv j)
        (fun ℓ' hℓ' hℓ'1 u _ hu =>
          s16c167_central_fixed_point_free hW hcard hL hℓ' hℓ'1 hu) with h | h
    · exact Or.inl h
    · exact Or.inr (Subgroup.eq_top_of_card_eq (U j) (by rw [h, hcard]))
  have hex : ∃ j : Fin 3, U j = ⊤ := by
    by_contra h
    have hall : ∀ j : Fin 3, U j = ⊥ := by
      intro j
      rcases hpartition j with hbot | htop
      · exact hbot
      · exact absurd htop (by intro hh; exact h ⟨j, hh⟩)
    have hbot : (⊤ : Subgroup W) = ⊥ := by
      rw [← hsup]
      exact iSup_eq_bot.mpr hall
    have hcard1 : Nat.card W = 1 := by
      have hc := congrArg (fun H : Subgroup W => Nat.card ↥H) hbot
      simpa using hc
    rw [hcard] at hcard1
    norm_num at hcard1
  obtain ⟨j, hj⟩ := hex
  have hfixall : ∀ w : W, (v * z ^ (j : ℕ)) w = w := by
    intro w
    have hw : w ∈ U j := by rw [hj]; exact Subgroup.mem_top w
    rwa [mem_fixV_zpowers_iff_apply] at hw
  have heq : v * z ^ (j : ℕ) = 1 := by
    apply MulEquiv.ext
    intro w
    simpa using hfixall w
  have hv : v = (z ^ (j : ℕ))⁻¹ := eq_inv_of_mul_eq_one_left heq
  have hmem : (z ^ (j : ℕ))⁻¹ ∈ Subgroup.zpowers (ℓ : MulAut W) :=
    Subgroup.inv_mem (Subgroup.zpowers (ℓ : MulAut W))
      (Subgroup.pow_mem (Subgroup.zpowers (ℓ : MulAut W)) (Subgroup.mem_zpowers z) (j : ℕ))
  rw [hv]
  exact hmem

theorem s1614_inf_card {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {L M A : Subgroup (MulAut W)} (hL : IsPOnePlusTwo 3 ↥L)
    (hMN : M ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAM : A ≤ M) (hA : IsElemAbelian 3 A)
    (hA27 : Nat.card ↥A = 27) :
    Nat.card ↥(A ⊓ L) = 9 ∧ ∀ ℓ : ↥L, ℓ ∈ Subgroup.center ↥L → (ℓ : MulAut W) ∈ A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 27 := by
    rw [hL.2.1]
    norm_num
  have hZcard : Nat.card (Subgroup.center ↥L) = 3 :=
    CFSG.IsExtraspecial.center_order_p 3 ↥L
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    by_contra h
    have hcomm : ∀ a b : ↥L, a * b = b * a := fun a b => by
      by_contra hne
      exact h ⟨a, b, hne⟩
    have htop : Subgroup.center ↥L = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hcomm y x
    rw [htop, Subgroup.card_top, hLcard] at hZcard
    norm_num at hZcard
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut W)) := hAM.trans hMN
  have hprod := s1614_ce_card_sup_mul_card_inf (A := L) (B := A) hAN
  rw [hLcard, hA27] at hprod
  have hmdvd_nat : Nat.card ↥(L ⊓ A) ∣ 27 := by
    have h := Subgroup.card_dvd_of_le (H := L ⊓ A) (K := L) inf_le_left
    simpa [hLcard] using h
  set m := Nat.card ↥(L ⊓ A) with hm
  obtain ⟨k, hk, hmk⟩ :=
    (Nat.dvd_prime_pow (p := 3) (m := 3) (i := m) Nat.prime_three).1
      (by rw [show (3 : ℕ) ^ 3 = 27 by norm_num]; exact hmdvd_nat)
  have hm_cases : m = 1 ∨ m = 3 ∨ m = 9 ∨ m = 27 := by
    interval_cases k
    · exact Or.inl (by simpa using hmk)
    · exact Or.inr (Or.inl (by simpa using hmk))
    · exact Or.inr (Or.inr (Or.inl (by simpa using hmk)))
    · exact Or.inr (Or.inr (Or.inr (by simpa using hmk)))
  have hAut : Nat.card (MulAut W) = 20158709760 := by
    rw [CFSG.GH74.GLS.Bg.TwoGroups.L218.card_mulAut_two hW 6 hcard]
    norm_num [Fin.prod_univ_succ]
  have hAutdvd : Nat.card ↥(L ⊔ A) ∣ 20158709760 := by
    rw [← hAut]
    exact Subgroup.card_subgroup_dvd_card (L ⊔ A)
  have hm1 : m ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hprod
    rw [hprod] at hAutdvd
    norm_num at hAutdvd
  have hm3 : m ≠ 3 := by
    intro h3
    rw [h3] at hprod
    have hval : Nat.card ↥(L ⊔ A) = 243 := by omega
    rw [hval] at hAutdvd
    norm_num at hAutdvd
  have hm27 : m ≠ 27 := by
    intro h27
    have hcard_inf : Nat.card ↥(L ⊓ A) = Nat.card ↥L := by
      rw [← hm, h27, hLcard]
    have hEqL : L ⊓ A = L :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard_inf.symm)
    have hLA : L ≤ A := hEqL ▸ inf_le_right
    have hcommL : ∀ a b : ↥L, a * b = b * a := by
      intro a b
      exact Subtype.ext (s1614_ce_comm_of_le hA.1 hLA hLA a a.2 b b.2)
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (hcommL a b)
  have hm9 : m = 9 := by
    rcases hm_cases with h | h | h | h
    · exact absurd h hm1
    · exact absurd h hm3
    · exact h
    · exact absurd h hm27
  have hfirst : Nat.card ↥(A ⊓ L) = 9 := by
    rw [inf_comm, ← hm]
    exact hm9
  refine ⟨hfirst, ?_⟩
  intro ℓ hℓ
  by_contra hℓA
  let P : Subgroup (MulAut W) := A ⊓ L
  let Z : Subgroup (MulAut W) := (Subgroup.center ↥L).map L.subtype
  have hPcard : Nat.card P = 9 := hfirst
  have hZcard' : Nat.card Z = 3 := by
    show Nat.card ((Subgroup.center ↥L).map L.subtype) = 3
    rw [Subgroup.card_map_of_injective L.subtype_injective, hZcard]
  have hℓmem : (ℓ : MulAut W) ∈ Z :=
    Subgroup.mem_map.mpr ⟨ℓ, hℓ, rfl⟩
  have hPL : P ≤ L := inf_le_right
  have hZL : Z ≤ L := by
    intro z hz
    obtain ⟨c, _, rfl⟩ := Subgroup.mem_map.mp hz
    exact c.2
  have hPcomm : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p :=
    s1614_ce_comm_of_le hA.1 (show P ≤ A from inf_le_left) (show P ≤ A from inf_le_left)
  have hZcent : ∀ z ∈ Z, ∀ y ∈ L, z * y = y * z := by
    intro z hz y hy
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hz
    have hcz' : (c : MulAut W) = z := hcz
    have hcomm := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
    have hcoe := congrArg (fun a : ↥L => (a : MulAut W)) hcomm
    simp only [Subgroup.coe_mul] at hcoe
    rw [hcz'] at hcoe
    exact hcoe.symm
  have hZP : Z ⊓ P = ⊥ := by
    have hdvd : Nat.card ↥(Z ⊓ P) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (H := Z ⊓ P) (K := Z) inf_le_left
      simpa [hZcard'] using h
    have hcases : Nat.card ↥(Z ⊓ P) = 1 ∨ Nat.card ↥(Z ⊓ P) = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hdvd
    rcases hcases with h1 | h3
    · exact Subgroup.eq_bot_of_card_eq (Z ⊓ P) h1
    · have hEqZ : Z ⊓ P = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      have hZA : Z ≤ A := (hEqZ ▸ inf_le_right : Z ≤ P).trans (show P ≤ A from inf_le_left)
      exact absurd (hZA hℓmem) hℓA
  have hZnorm : Z ≤ Subgroup.normalizer (P : Set (MulAut W)) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      have hcomm := hZcent z hz p (hPL hp)
      have heq : z * p * z⁻¹ = p := by rw [hcomm]; group
      rwa [heq]
    · intro hp
      have hzL : z ∈ L := hZL hz
      have hpL : p ∈ L := by
        have h1 : z * p * z⁻¹ ∈ L := hPL hp
        have heq : p = z⁻¹ * (z * p * z⁻¹) * z := by group
        rw [heq]
        exact L.mul_mem (L.mul_mem (L.inv_mem hzL) h1) hzL
      have hcomm := hZcent z hz p hpL
      have heq : z * p * z⁻¹ = p := by rw [hcomm]; group
      rwa [heq] at hp
  have hprodPZ := s1614_ce_card_sup_mul_card_inf (A := P) (B := Z) hZnorm
  rw [inf_comm, hZP, Subgroup.card_bot, mul_one, hPcard, hZcard'] at hprodPZ
  have hPZcard : Nat.card ↥(P ⊔ Z) = 27 := by
    rw [hprodPZ]
  have hPZle : P ⊔ Z ≤ L := sup_le hPL hZL
  have hPZeq : P ⊔ Z = L :=
    Subgroup.eq_of_le_of_card_ge hPZle (by omega)
  have hcommL : ∀ a ∈ L, ∀ b ∈ L, a * b = b * a :=
    s1614_ce_comm_of_eq_sup hPZeq.symm hPcomm hZcent hZnorm hPL hZL
  obtain ⟨a, b, hab⟩ := hnc
  exact hab (Subtype.ext (hcommL a a.2 b b.2))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
