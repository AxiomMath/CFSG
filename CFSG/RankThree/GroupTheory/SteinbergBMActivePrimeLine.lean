module

public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup

variable {G : Type*} [Group G]

theorem centralizer_zpowers_eq (y : G) :
    centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem small_odd_group_active_prime_line [Finite G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {F K : Subgroup G} (hK2 : IsPGroup 2 K) (hFK : F ≤ normalizer (K : Set G))
    (hCF : F ⊓ centralizer (K : Set G) = ⊥)
    (hF : (CFSG.IsElementaryAbelian q F ∧ Nat.card F = q ^ 2) ∨
      (Monoid.exponent F = q ∧ Nat.card F = q ^ 3 ∧ center F = commutator F ∧
        commutator F = frattini F ∧ Nat.card (center F) = q)) :
    ∃ Y : Subgroup G, Y ≤ F ∧ Nat.card Y = q ∧ ¬ Y ≤ CFSG.inSubgroup frattini F ∧
      ⁅K ⊓ centralizer (Y : Set G), F ⊓ centralizer (Y : Set G)⁆ ≠ ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  have hqK : ¬ q ∣ Nat.card K := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hK2
    rw [hk]
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
  have hline : ∀ y : G, y ≠ 1 → y ^ q = 1 → Nat.card (zpowers y) = q := fun y hy1 hyq => by
    rw [Nat.card_zpowers, orderOf_eq_prime hyq hy1]
  rcases hF with ⟨hFe, hFcard⟩ | ⟨hFexp, hFcard, hZF', hF'Φ, hZcard⟩
  ·
    obtain ⟨y, hy, hy1, hne⟩ :
        ∃ y ∈ F, y ≠ 1 ∧ ⁅K ⊓ centralizer ({y} : Set G), F⁆ ≠ ⊥ := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hKF : K ≤ centralizer (F : Set G) :=
        le_of_forall_inf_centralizer_le hFe hFcard.ge hqK hFK fun y hy hy1 =>
          commutator_eq_bot_iff_le_centralizer.mp (hcon y hy hy1)
      have hFb : F = ⊥ := by
        rw [← hCF]
        refine le_antisymm (le_inf le_rfl fun f hf => ?_) inf_le_left
        rw [mem_centralizer_iff]
        intro k hk
        exact (mem_centralizer_iff.mp (hKF hk) f hf).symm
      rw [hFb, card_bot] at hFcard
      have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq.one_lt
      omega
    have hyq : y ^ q = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := q) (A := F) y hy
    refine ⟨zpowers y, zpowers_le.mpr hy, hline y hy1 hyq, ?_, ?_⟩
    · have : Fact (IsPGroup q F) := ⟨CFSG.IsElementaryAbelian.isPGroup q F⟩
      rw [CFSG.inSubgroup, CFSG.frattini_eq_bot_of_isElementaryAbelian (p := q),
        Subgroup.map_bot, le_bot_iff]
      exact fun h => hy1 (zpowers_eq_bot.mp h)
    · have hFC : F ⊓ centralizer ((zpowers y : Subgroup G) : Set G) = F := by
        refine inf_eq_left.mpr fun f hf => ?_
        rw [centralizer_zpowers_eq]
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hFe.is_comm.comm ⟨f, hf⟩ ⟨y, hy⟩))
      rw [hFC, centralizer_zpowers_eq]
      exact hne
  ·
    have hpow : ∀ x ∈ F, x ^ q = 1 := fun x hx => by
      have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : F)
      rw [hFexp] at this
      simpa using congrArg Subtype.val this
    set Z := (center F).map F.subtype with hZdef
    have hZF : Z ≤ F := map_subtype_le _
    have hZc : Nat.card Z = q := by rw [hZdef, card_map_of_injective F.subtype_injective, hZcard]
    have hZΦ : Z = CFSG.inSubgroup frattini F := by rw [CFSG.inSubgroup, ← hF'Φ, ← hZF']
    have hZcomm : ∀ z ∈ Z, ∀ f ∈ F, z * f = f * z := by
      rintro _ ⟨w, hw, rfl⟩ f hf
      exact (congrArg Subtype.val ((mem_center_iff.mp hw) ⟨f, hf⟩)).symm
    have hZlt : Z < F := lt_of_le_of_ne hZF fun h => by
      rw [h, hFcard] at hZc
      have : q ^ 1 < q ^ 3 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
      rw [pow_one] at this
      omega
    obtain ⟨x, hx, hxZ⟩ := IsConcreteLE.exists_of_lt hZlt
    have hx1 : x ≠ 1 := fun h => hxZ (h ▸ Z.one_mem)
    set E := zpowers x ⊔ Z with hEdef
    have hEF : E ≤ F := sup_le (zpowers_le.mpr hx) hZF
    have hZx : Z ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
      intro z hz
      rw [centralizer_zpowers_eq]
      exact mem_centralizer_singleton_iff.mpr (hZcomm z hz x hx)
    have hZe : CFSG.IsElementaryAbelian q Z :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hZcomm a a.2 b (hZF b.2))⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => Subtype.ext (by
          rw [coe_pow, hpow z (hZF z.2), coe_one]) }
    have hxe : CFSG.IsElementaryAbelian q (zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (hpow x hx)
    have hEe : CFSG.IsElementaryAbelian q E := CFSG.IsElementaryAbelian.sup_of_le_centralizer hZx
    have hxZb : zpowers x ⊓ Z = ⊥ := by
      have hdvd : Nat.card (zpowers x ⊓ Z : Subgroup G) ∣ q := by
        rw [← hline x hx1 (hpow x hx)]
        exact card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hq).mp hdvd with h | h
      · exact card_eq_one.mp h
      · exfalso
        have heq : zpowers x ⊓ Z = zpowers x :=
          eq_of_le_of_card_ge inf_le_left (by rw [h, hline x hx1 (hpow x hx)])
        exact hxZ ((heq ▸ inf_le_right : zpowers x ≤ Z) (mem_zpowers x))
    have hEcard : Nat.card E = q ^ 2 := by
      rw [hEdef, CFSG.Quasithin.SteinbergBM.card_sup_of_commute hZx hxZb, hline x hx1 (hpow x hx),
        hZc, sq]
    obtain ⟨y, hy, hy1, hyZ, hne⟩ : ∃ y ∈ E, y ≠ 1 ∧ zpowers y ≠ Z ∧
        ⁅K ⊓ centralizer ({y} : Set G), E⁆ ≠ ⊥ := by
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hKZ : K ≤ centralizer (Z : Set G) := by
        refine le_of_forall_inf_centralizer_le hEe hEcard.ge hqK (hEF.trans hFK) fun y hy hy1 => ?_
        by_cases hyZ : zpowers y = Z
        · rw [← hyZ, centralizer_zpowers_eq]
          exact inf_le_right
        · exact (commutator_eq_bot_iff_le_centralizer.mp (hcon y hy hy1 hyZ)).trans
            (centralizer_le (SetLike.coe_subset_coe.mpr (le_sup_right : Z ≤ E)))
      have hZb : Z ≤ F ⊓ centralizer (K : Set G) := fun z hz =>
        ⟨hZF hz, mem_centralizer_iff.mpr fun k hk => (mem_centralizer_iff.mp (hKZ hk) z hz).symm⟩
      rw [hCF, le_bot_iff] at hZb
      rw [hZb, card_bot] at hZc
      exact hq.one_lt.ne hZc
    have hyF : y ∈ F := hEF hy
    have hyq : y ^ q = 1 := hpow y hyF
    have hYc := hline y hy1 hyq
    have hFC : F ⊓ centralizer ((zpowers y : Subgroup G) : Set G) = E := by
      have hEC : E ≤ F ⊓ centralizer ((zpowers y : Subgroup G) : Set G) := by
        intro e he
        refine mem_inf.mpr ⟨hEF he, ?_⟩
        rw [centralizer_zpowers_eq]
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (hEe.is_comm.comm ⟨e, he⟩ ⟨y, hy⟩))
      have hproper : F ⊓ centralizer ((zpowers y : Subgroup G) : Set G) ≠ F := by
        intro h
        apply hyZ
        have hyZ' : y ∈ Z := by
          refine ⟨⟨y, hyF⟩, mem_center_iff.mpr fun f => Subtype.ext ?_, rfl⟩
          have hf : (f : G) ∈ F ⊓ centralizer ((zpowers y : Subgroup G) : Set G) := by
            rw [h]
            exact f.2
          have hfc : (f : G) ∈ centralizer ((zpowers y : Subgroup G) : Set G) := (mem_inf.mp hf).2
          rw [centralizer_zpowers_eq] at hfc
          exact mem_centralizer_singleton_iff.mp hfc
        exact eq_of_le_of_card_ge (zpowers_le.mpr hyZ') (by rw [hYc, hZc])
      have hdvd1 : Nat.card (F ⊓ centralizer ((zpowers y : Subgroup G) : Set G) : Subgroup G) ∣
          q ^ 3 := hFcard ▸ card_dvd_of_le inf_le_left
      obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hq).mp hdvd1
      have hdvd2 : q ^ 2 ∣ q ^ k := hEcard ▸ hkc ▸ card_dvd_of_le hEC
      have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp hdvd2
      have hk3 : k ≠ 3 := fun h => hproper (eq_of_le_of_card_ge inf_le_left (by
        rw [hFcard, hkc, h]))
      have hk' : k = 2 := by omega
      exact (eq_of_le_of_card_ge hEC (by rw [hEcard, hkc, hk'])).symm
    refine ⟨zpowers y, zpowers_le.mpr hyF, hYc, ?_, ?_⟩
    · rw [← hZΦ]
      intro hle
      exact hyZ (eq_of_le_of_card_ge hle (by rw [hYc, hZc]))
    · rw [hFC, centralizer_zpowers_eq]
      exact hne

end CFSG.RankThree.GroupTheory.SteinbergBM
