module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
import CFSG.Quasithin.EmptyFaithful.SBdK36Abs

public section

namespace CFSG.StandardType.QTwo

variable {G : Type} [Group G] [Finite G]

theorem qtwoDL1_le_ggOTwoPrime_ggOTwoPrime (Y : Subgroup G) :
    ggOTwoPrime Y ≤ ggOTwoPrime (ggOTwoPrime Y) := by
  rw [ggOTwoPrime, Subgroup.closure_le]
  intro y hy
  exact Subgroup.subset_closure ⟨Subgroup.subset_closure hy, hy.2⟩

private theorem p9uL6_center_eq_bot_of_card_six_of_not_comm {S : Subgroup G}
    (h6 : Nat.card ↥S = 6) (hnc : ¬ ∀ a b : ↥S, a * b = b * a) :
    Subgroup.center ↥S = ⊥ := by
  have hnc' : ∃ x y : ↥S, x * y ≠ y * x := by
    rw [not_forall] at hnc
    obtain ⟨x, hx⟩ := hnc
    rw [not_forall] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨x, y, hy⟩
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 hnc'
  have hcenter3 : ∀ w : Equiv.Perm (Fin 3), (∀ x, w * x = x * w) → w = 1 := by decide
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hz' : e z = 1 := by
    apply hcenter3
    intro w
    have h := congrArg e (Subgroup.mem_center_iff.mp hz (e.symm w))
    simp only [map_mul, MulEquiv.apply_symm_apply] at h
    exact h.symm
  apply e.injective
  rw [map_one, hz']

theorem qtwoDL1_not_comm_of_card_six {S : Subgroup G} (h6 : Nat.card ↥S = 6)
    (hS2 : S ≤ ggOTwoPrime S) : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let T : Subgroup G :=
    { carrier := {x : G | x ∈ S ∧ x ^ 2 = 1}
      one_mem' := ⟨S.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxS, hx2⟩ ⟨hyS, hy2⟩
        refine ⟨S.mul_mem hxS hyS, ?_⟩
        have hxy : x * y = y * x := h x hxS y hyS
        calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
          _ = x * (x * y) * y := by rw [hxy]
          _ = (x * x) * (y * y) := by group
          _ = 1 := by rw [← pow_two, hx2, ← pow_two, hy2, mul_one]
      inv_mem' := by
        rintro x ⟨hxS, hx2⟩
        exact ⟨S.inv_mem hxS, by rw [inv_pow, hx2, inv_one]⟩ }
  have hgen : ggOTwoPrime S ≤ T := by
    rw [ggOTwoPrime, Subgroup.closure_le]
    rintro y ⟨hyS, k, hk⟩
    refine ⟨hyS, ?_⟩
    have hordS : orderOf y ∣ 6 := by
      rw [← h6]
      exact Subgroup.orderOf_dvd_natCard S hyS
    have hord2 : orderOf y ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord2
    have hj6 : 2 ^ j ∣ 6 := hj ▸ hordS
    have hj1 : j ≤ 1 := by
      by_contra hj
      have h2 : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      have h46 : 4 ∣ 6 := by simpa using h2.trans hj6
      norm_num at h46
    rw [← orderOf_dvd_iff_pow_eq_one, hj]
    simpa using pow_dvd_pow 2 hj1
  have hST : S ≤ T := hS2.trans hgen
  have hT2 : T ≤ S := fun _ hx => hx.1
  have hdvdT : Nat.card ↥T ∣ 6 := h6 ▸ Subgroup.card_dvd_of_le hT2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 ↥T := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using x.2.2
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hTp
  have hnle : n ≤ 1 := by
    by_contra hn1
    have h2 : 2 ^ 2 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have h46 : 4 ∣ 6 := by
      have := h2.trans (hn ▸ hdvdT)
      simpa using this
    norm_num at h46
  have hTle2 : Nat.card ↥T ≤ 2 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
      _ = 2 := by norm_num
  have hcardST : Nat.card ↥S ∣ Nat.card ↥T := Subgroup.card_dvd_of_le hST
  rw [h6] at hcardST
  have h6le : 6 ≤ Nat.card ↥T := Nat.le_of_dvd Nat.card_pos hcardST
  omega

theorem qtwoDL1_exists_mem_inv_mul_mem_centralizer {S : Subgroup G} (h6 : Nat.card ↥S = 6)
    (hnc : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) {c : G}
    (hc : c ∈ Subgroup.normalizer (S : Set G)) :
    ∃ s ∈ S, s⁻¹ * c ∈ Subgroup.centralizer (S : Set G) := by
  have hnc' : ∃ x y : ↥S, x * y ≠ y * x := by
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (by simpa using congrArg Subtype.val h)⟩
  obtain ⟨e⟩ := CFSG.Quasithin.SBd.nonempty_mulEquiv_perm_three_of_card_six h6 hnc'
  have hmap : S.map (MulAut.conj c) = S :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hc
  let γ : MulAut ↥S := ((MulAut.conj c).subgroupMap S).trans (MulEquiv.subgroupCongr hmap)
  let α : MulAut (Equiv.Perm (Fin 3)) := (e.symm.trans γ).trans e
  obtain ⟨g, hg⟩ := CFSG.Quasithin.SBd.perm_three_aut_inner α
  refine ⟨(e.symm g : ↥S), (e.symm g).2, ?_⟩
  have hγ : ∀ x : ↥S, γ x = (e.symm g) * x * (e.symm g)⁻¹ := by
    intro x
    apply e.injective
    calc e (γ x) = α (e x) := by simp [α, MulEquiv.trans_apply]
      _ = g * e x * g⁻¹ := hg (e x)
      _ = e ((e.symm g) * x * (e.symm g)⁻¹) := by
            rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hcoe : ∀ x ∈ S, c * x * c⁻¹ = (e.symm g : G) * x * (e.symm g : G)⁻¹ := by
    intro x hx
    have h := congrArg (fun y : ↥S => (y : G)) (hγ ⟨x, hx⟩)
    have hγcoe : (γ ⟨x, hx⟩ : G) = c * x * c⁻¹ := by
      dsimp only [γ]
      simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
        MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
    rw [hγcoe] at h
    exact h
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hs0x := hcoe x hx
  have hgoal : (e.symm g : G)⁻¹ * c * x = x * ((e.symm g : G)⁻¹ * c) := by
    calc (e.symm g : G)⁻¹ * c * x
        = (e.symm g : G)⁻¹ * (c * x * c⁻¹) * c := by group
      _ = (e.symm g : G)⁻¹ * ((e.symm g : G) * x * (e.symm g : G)⁻¹) * c := by rw [hs0x]
      _ = x * ((e.symm g : G)⁻¹ * c) := by group
  exact hgoal.symm

theorem qtwoDL1_ggOTwoPrime_eq_of_card_six {C S : Subgroup G} (hSC : S ≤ C)
    (hCN : C ≤ Subgroup.normalizer (S : Set G)) (h6 : Nat.card ↥S = 6)
    (hS2 : S ≤ ggOTwoPrime S)
    (hodd : Odd (Nat.card ↥(C ⊓ Subgroup.centralizer (S : Set G)))) :
    ggOTwoPrime C = S := by
  have hnc : ∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a :=
    qtwoDL1_not_comm_of_card_six h6 hS2
  have hnc' : ¬ ∀ a b : ↥S, a * b = b * a := by
    intro h
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    exact hab (by simpa using congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩))
  have hcenter : Subgroup.center ↥S = ⊥ :=
    p9uL6_center_eq_bot_of_card_six_of_not_comm h6 hnc'
  apply le_antisymm
  · rw [ggOTwoPrime, Subgroup.closure_le]
    rintro c ⟨hcC, a, hca⟩
    obtain ⟨s, hsS, hk⟩ :=
      qtwoDL1_exists_mem_inv_mul_mem_centralizer h6 hnc (hCN hcC)
    set k : G := s⁻¹ * c with hkdef
    have hkc : k ∈ C := C.mul_mem (C.inv_mem (hSC hsS)) hcC
    have hkH : k ∈ C ⊓ Subgroup.centralizer (S : Set G) := ⟨hkc, hk⟩
    have hks : k * s = s * k :=
      ((Subgroup.mem_centralizer_iff.mp hk) s hsS).symm
    have hck : c = s * k := by rw [hkdef]; group
    have hkpow : k ^ (2 ^ a) = (s ^ (2 ^ a))⁻¹ := by
      have h1 : k ^ (2 ^ a) * s ^ (2 ^ a) = 1 := by
        have h2 : (s * k) ^ (2 ^ a) = 1 := by rw [← hck]; exact hca
        rw [← hks, Commute.mul_pow hks] at h2
        exact h2
      exact mul_eq_one_iff_eq_inv.mp h1
    have hkpowS : k ^ (2 ^ a) ∈ S := by
      rw [hkpow]
      exact S.inv_mem (pow_mem hsS _)
    have hkpowC : k ^ (2 ^ a) ∈ Subgroup.centralizer (S : Set G) :=
      pow_mem hk _
    have hzmem : (⟨k ^ (2 ^ a), hkpowS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hkpowC) y y.2
    have hk2a1 : k ^ (2 ^ a) = 1 := by
      have hz1 : (⟨k ^ (2 ^ a), hkpowS⟩ : ↥S) = 1 := by
        rw [hcenter] at hzmem
        exact Subgroup.mem_bot.mp hzmem
      simpa using congrArg Subtype.val hz1
    have hord2 : orderOf k ∣ 2 ^ a := orderOf_dvd_iff_pow_eq_one.mpr hk2a1
    have hordH : orderOf k ∣ Nat.card ↥(C ⊓ Subgroup.centralizer (S : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hkH
    have hcop : Nat.Coprime (2 ^ a)
        (Nat.card ↥(C ⊓ Subgroup.centralizer (S : Set G))) :=
      Nat.Coprime.pow_left a hodd.coprime_two_left
    have hk1 : k = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord2 hordH)
    rw [hck, hk1, mul_one]
    exact hsS
  · have hmono : ggOTwoPrime S ≤ ggOTwoPrime C := by
      rw [ggOTwoPrime, ggOTwoPrime, Subgroup.closure_le]
      rintro y ⟨hyS, k, hk⟩
      exact Subgroup.subset_closure ⟨hSC hyS, k, hk⟩
    exact hS2.trans hmono

end CFSG.StandardType.QTwo

end
