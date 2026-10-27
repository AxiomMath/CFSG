module

public import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

theorem pCore_le_solvableRadical {H : Type*} [Group H] [Finite H] :
    CFSG.pCore 2 H ≤ CFSG.solvableRadical H := by
  have : Group.IsNilpotent (CFSG.pCore 2 H) :=
    (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 H)).isNilpotent
  exact le_solvableRadical' CFSG.pCore_normal inferInstance

@[expose] def qcore {G : Type} [Group G] (D : Set G) (x : G) (P : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 (lsub D x P)).map (lsub D x P).subtype

namespace ConnCex

variable {G : Type} [Group G] {D : Set G} (hC : ConnCex D)
include hC

theorem reach_of_commute_mul {e f y : G} (he : e ∈ D) (hf : f ∈ D) (hy : y ∈ D) (hef : e ≠ f)
    (hc : Commute e f) (hyc : Commute y (e * f)) : Reach D y e := by
  have hD := hC.setting.root
  by_contra hnr
  obtain ⟨-, hodd_ye⟩ := opposite_of_not_reach hD hy he hnr
  have hnyf : ¬ Reach D y f := fun h' =>
    hnr (reach_trans h' (reach_symm (reach_of_commute he hf hc)))
  obtain ⟨-, hodd_yf⟩ := opposite_of_not_reach hD hy hf hnyf
  have hu2 : e * f * (e * f) = 1 := hC.mul_mul_self_of_commute he hf hc
  have hu1 : e * f ≠ 1 := hC.mul_ne_one_of_ne hf hef
  have hou : orderOf (e * f) = 2 := orderOf_eq_prime (by rw [pow_two, hu2]) hu1
  have hec : Commute e (e * f) := (Commute.refl e).mul_right hc
  have h2 := orderOf_mul_eq_two_mul_of_odd (hyc.mul_left hec) hodd_ye hou
  rw [show y * e * (e * f) = y * f by rw [← mul_assoc, mul_assoc y e e,
    hD.mul_self_eq_one he, mul_one]] at h2
  rw [h2] at hodd_yf
  exact (Nat.not_even_iff_odd.2 hodd_yf) (even_two_mul _)

end ConnCex

namespace Step6

variable {G : Type} [Group G] {D : Set G} {a b c x z : G} {P : Subgroup G}

theorem mem_classIn_of_mem_lsub (hC : ConnCex D) (h : Step6 D a b c x z P) {y : G}
    (hy : y ∈ D) (hyX : y ∈ lsub D x P) : y ∈ classIn (lsub D x P) x := by
  have hD := hC.setting.root
  by_cases hay : Reach D a y
  · have hyx : ¬ Reach D y x := fun hr => h.hax (reach_trans hay hr)
    obtain ⟨-, hodd⟩ := opposite_of_not_reach hD hy h.hx hyx
    have h1 := mem_classIn_of_odd hD hy h.hx hyX mem_lsub_x hodd
    rw [classIn_eq_of_mem h1]
    exact mem_classIn_self _ _
  · obtain ⟨-, hodd⟩ := opposite_of_not_reach hD h.ha hy hay
    have h1 := mem_classIn_of_odd hD h.ha hy (mem_lsub_of_mem h.ha h.haP) hyX hodd
    rwa [classIn_eq_of_mem (h.mem_classIn hC h.ha h.haP)] at h1

theorem not_mem_qcore (hC : ConnCex D) (h : Step6 D a b c x z P) {y : G} (hy : y ∈ D) :
    y ∉ qcore D x P := by
  have := hC.setting.finite
  rintro ⟨w, hw, rfl⟩
  have hwE : w ∈ lclass D x P := h.mem_classIn_of_mem_lsub hC hy w.2
  exact h.not_mem_solvableRadical hC w hwE (pCore_le_solvableRadical hw)

theorem mem_of_isPGroup (hC : ConnCex D) (h : Step6 D a b c x z P) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hPS : ∀ l ∈ D, l ∈ P → l ∈ S) {y : G} (hy : y ∈ D)
    (hyz : Commute y z) (hyS : y ∈ S) : y ∈ P :=
  h.hcent y hy fun l hl hlP => (h.isOddTransp hC).commute_of_isPGroup hS
    ⟨hy, Subgroup.mem_centralizer_singleton_iff.2 hyz.eq⟩ ⟨hl, h.hPz hlP⟩ hyS (hPS l hl hlP)

theorem false_of_commute_mul (hC : ConnCex D) (h : Step6 D a b c x z P) {e f : G} (he : e ∈ D)
    (hf : f ∈ D) (hef : e ≠ f) (hc : Commute e f) (ha : Commute a (e * f))
    (hx : Commute x (e * f)) : False :=
  h.hax (reach_trans (hC.reach_of_commute_mul he hf h.ha hef hc ha)
    (reach_symm (hC.reach_of_commute_mul he hf h.hx hef hc hx)))

theorem isPGroup_sup_zpowers (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G} (hf : f ∈ D)
    (hfN : f ∈ Subgroup.normalizer (P : Set G)) :
    IsPGroup 2 (P ⊔ Subgroup.zpowers f : Subgroup G) := by
  have hD := hC.setting.root
  have hf2 : IsPGroup 2 (Subgroup.zpowers f) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hD.orderOf_eq_two hf, pow_one]
  exact h.hP2.to_sup_of_normal_left' hf2 ((Subgroup.zpowers_le).2 hfN)

theorem eq_one_of_commute_center (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G}
    (hf : f ∈ D) (hfN : f ∈ Subgroup.normalizer (P : Set G)) (hfP : f ∉ P) {w : lsub D x P}
    (hwc : w ∈ Subgroup.center (lsub D x P)) (hfw : Commute f (w : G)) : w = 1 := by
  by_contra hw1
  have hcen : ∀ g ∈ lsub D x P, Commute g (w : G) := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hwc ⟨g, hg⟩)
  have hK : Subgroup.centralizer ({(w : G)} : Set G) ≠ ⊤ := by
    intro htop
    have hwG : (w : G) ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have : g ∈ Subgroup.centralizer ({(w : G)} : Set G) := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have := hC.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
    · rw [hb, Subgroup.mem_bot] at hwG
      exact hw1 (Subtype.ext hwG)
    · have hax : x ∈ Subgroup.center G := ht ▸ Subgroup.mem_top x
      rw [Subgroup.mem_center_iff] at hax
      exact (opposite_of_not_reach hC.setting.root h.ha h.hx h.hax).1 (hax a)
  have hOT := hC.isOddTransp_of_le hK h.ha h.hx
    (Subgroup.mem_centralizer_singleton_iff.2 (hcen a (mem_lsub_of_mem h.ha h.haP)).eq)
    (Subgroup.mem_centralizer_singleton_iff.2 (hcen x mem_lsub_x).eq) h.hax
  apply hfP
  refine h.hcent f hf fun l hl hlP => ?_
  exact hOT.commute_of_isPGroup (h.isPGroup_sup_zpowers hC hf hfN)
    ⟨hf, Subgroup.mem_centralizer_singleton_iff.2 hfw.eq⟩
    ⟨hl, Subgroup.mem_centralizer_singleton_iff.2 (hcen l (mem_lsub_of_mem hl hlP)).eq⟩
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers f)) (Subgroup.mem_sup_left hlP)

theorem commute_of_mul_conj_mem_qcore (hC : ConnCex D) (h : Step6 D a b c x z P) {f : G}
    (hf : f ∈ D) (hfN : f ∈ Subgroup.normalizer (P : Set G)) {ℓ : G} (hℓ : ℓ ∈ D)
    (hℓP : ℓ ∈ P) (hq : ℓ * (f * ℓ * f⁻¹) ∈ qcore D x P) : Commute f ℓ := by
  have hD := hC.setting.root
  by_contra hnc
  have hS := h.isPGroup_sup_zpowers hC hf hfN
  have hfS : f ∈ (P ⊔ Subgroup.zpowers f : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers f)
  have hℓS : ℓ ∈ (P ⊔ Subgroup.zpowers f : Subgroup G) := Subgroup.mem_sup_left hℓP
  have h4 : orderOf (ℓ * f) = 4 := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hℓ hf with h' | h' | ⟨hodd, -⟩
    · exact absurd h'.symm hnc
    · exact h'
    · exfalso
      obtain ⟨k, hk⟩ := hS ⟨ℓ * f, (P ⊔ Subgroup.zpowers f).mul_mem hℓS hfS⟩
      have hk' : (ℓ * f) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h1 : orderOf (ℓ * f) = 1 := by
        have hdvd := orderOf_dvd_of_pow_eq_one hk'
        rcases (Nat.dvd_prime_pow Nat.prime_two).1 hdvd with ⟨j, -, hj⟩
        rcases j with _ | j
        · simpa using hj
        · rw [hj] at hodd
          exact absurd hodd
            (Nat.not_odd_iff_even.2 (Nat.even_pow.2 ⟨even_two, Nat.succ_ne_zero j⟩))
      rw [orderOf_eq_one_iff, mul_eq_one_iff_eq_inv, hD.inv_eq hf] at h1
      exact hnc (by rw [h1])
  have hsq := hD.sq_mem hℓ hf h4
  rw [show (ℓ * f) ^ 2 = ℓ * (f * ℓ * f⁻¹) by rw [pow_two, hD.inv_eq hf]; group] at hsq
  exact h.not_mem_qcore hC hsq hq

end Step6

end CFSG.Timmesfeld.Bridge
