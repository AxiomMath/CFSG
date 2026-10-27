module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartOne.K1214

open Subgroup

variable {G : Type*} [Group G]

omit [Group G] in
theorem card_sup_mul_card_inf_of_normal {G : Type*} [Group G] (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem card_sup_mul_card_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := Subgroup.normalizer (A : Set G)
  have hAN : A ≤ N := Subgroup.le_normalizer
  have : (A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (Subgroup.subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem mem_sup_centralizer_iff (J : Subgroup G) {g : G} :
    g ∈ J ⊔ centralizer (J : Set G) ↔ ∃ j ∈ J, ∃ z ∈ centralizer (J : Set G), g = j * z := by
  constructor
  · intro hg
    let S : Subgroup G :=
      { carrier := {g | ∃ j ∈ J, ∃ z ∈ centralizer (J : Set G), g = j * z}
        one_mem' := ⟨1, J.one_mem, 1, Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨j, hj, z, hz, rfl⟩ ⟨j', hj', z', hz', rfl⟩
          refine ⟨j * j', J.mul_mem hj hj', z * z', Subgroup.mul_mem _ hz hz', ?_⟩
          have hc : z * j' = j' * z := (mem_centralizer_iff.mp hz) j' hj' |>.symm
          calc j * z * (j' * z') = j * (z * j') * z' := by group
            _ = j * (j' * z) * z' := by rw [hc]
            _ = j * j' * (z * z') := by group
        inv_mem' := by
          rintro _ ⟨j, hj, z, hz, rfl⟩
          refine ⟨j⁻¹, J.inv_mem hj, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
          have hc : z * j = j * z := (mem_centralizer_iff.mp hz) j hj |>.symm
          have hc' : z⁻¹ * j⁻¹ = j⁻¹ * z⁻¹ := by
            have := congrArg (·⁻¹) hc
            simpa [mul_inv_rev] using this.symm
          calc (j * z)⁻¹ = z⁻¹ * j⁻¹ := by group
            _ = j⁻¹ * z⁻¹ := hc' }
    have hle : J ⊔ centralizer (J : Set G) ≤ S :=
      sup_le (fun j hj => ⟨j, hj, 1, Subgroup.one_mem _, by simp⟩)
        (fun z hz => ⟨1, J.one_mem, z, hz, by simp⟩)
    exact hle hg
  · rintro ⟨j, hj, z, hz, rfl⟩
    exact Subgroup.mul_mem _ (mem_sup_left hj) (mem_sup_right hz)

theorem inf_centralizer_eq_map_center (I : Subgroup G) :
    I ⊓ centralizer (I : Set G) = (center I).map I.subtype := by
  ext x
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun w => ?_, rfl⟩
    apply Subtype.ext
    exact mem_centralizer_iff.mp hxc (w : G) w.2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨w, hw⟩
    exact congrArg Subtype.val this

theorem card_inf_centralizer (I : Subgroup G) :
    Nat.card (I ⊓ centralizer (I : Set G) : Subgroup G) = Nat.card (center I) := by
  rw [inf_centralizer_eq_map_center, Subgroup.card_map_of_injective I.subtype_injective]

theorem conj_mem_centralizer_inf {C I : Subgroup G} {n z : G} (hnC : n ∈ C)
    (hn : n ∈ normalizer (I : Set G)) (hz : z ∈ centralizer (I : Set G) ⊓ C) :
    n * z * n⁻¹ ∈ centralizer (I : Set G) ⊓ C := by
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun i hi => ?_, C.mul_mem (C.mul_mem hnC hz.2) (C.inv_mem hnC)⟩
  have hi' : n⁻¹ * i * n ∈ I := (Subgroup.mem_normalizer_iff''.1 hn i).1 hi
  have h := mem_centralizer_iff.1 hz.1 _ hi'
  calc i * (n * z * n⁻¹) = n * ((n⁻¹ * i * n) * z) * n⁻¹ := by group
    _ = n * (z * (n⁻¹ * i * n)) * n⁻¹ := by rw [h]
    _ = n * z * n⁻¹ * i := by group

theorem le_normalizer_centralizer_inf (C I : Subgroup G) :
    C ⊓ normalizer (I : Set G) ≤ normalizer ((centralizer (I : Set G) ⊓ C : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    exact conj_mem_centralizer_inf hn.1 hn.2 hz
  · intro hz
    have hn' : n⁻¹ ∈ C ⊓ normalizer (I : Set G) := (C ⊓ normalizer (I : Set G)).inv_mem hn
    have := conj_mem_centralizer_inf hn'.1 hn'.2 hz
    simpa [mul_assoc] using this

theorem inf_isSylowOf_of_le_normalizer [Finite G] {p : ℕ} [Fact p.Prime] {C P I : Subgroup G}
    (hP : ABGLocalTools.IsSylowOf p P C) (hIC : I ≤ C) (hPI : P ≤ normalizer (I : Set G)) :
    ABGLocalTools.IsSylowOf p (P ⊓ I) I :=
  (hP.of_le (le_inf hP.le hPI) inf_le_left).inf_of_le_normalizer (le_inf hIC Subgroup.le_normalizer)
    inf_le_right

theorem inf_sup_centralizer_eq [Finite G] {p : ℕ} [Fact p.Prime] {C P I : Subgroup G}
    (hP : ABGLocalTools.IsSylowOf p P C) (hIC : I ≤ C) (hPI : P ≤ normalizer (I : Set G))
    (hZ : ¬ p ∣ Nat.card (center I)) :
    P ⊓ (I ⊔ centralizer (I : Set G)) = (centralizer (I : Set G) ⊓ P) ⊔ (P ⊓ I) := by
  have hPC : P ≤ C := hP.le
  set N : Subgroup G := C ⊓ normalizer (I : Set G) with hN
  set Cz : Subgroup G := centralizer (I : Set G) ⊓ C with hCz
  set Y : Subgroup G := I ⊔ Cz with hY
  have hPN : P ≤ N := le_inf hPC hPI
  have hIN : I ≤ N := le_inf hIC Subgroup.le_normalizer
  have hCzN : Cz ≤ N :=
    le_inf inf_le_right (le_trans inf_le_left (Subgroup.centralizer_le_normalizer _))
  have hYN : Y ≤ N := sup_le hIN hCzN
  have hNI : N ≤ normalizer (I : Set G) := inf_le_right
  have hNCz : N ≤ normalizer (Cz : Set G) := le_normalizer_centralizer_inf C I
  have hNY : N ≤ normalizer (Y : Set G) := by
    have hI' : (I.subgroupOf N).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hIN).mpr hNI
    have hC' : (Cz.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hCzN).mpr hNCz
    have hY' : (Y.subgroupOf N).Normal := by
      rw [hY, Subgroup.subgroupOf_sup hIN hCzN]
      exact Subgroup.sup_normal _ _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hYN).mp hY'
  have hPsylN : ABGLocalTools.IsSylowOf p P N := hP.of_le hPN inf_le_left
  have hsylY : ABGLocalTools.IsSylowOf p (P ⊓ Y) Y := hPsylN.inf_of_le_normalizer hYN hNY
  have hsylI : ABGLocalTools.IsSylowOf p (P ⊓ I) I := hPsylN.inf_of_le_normalizer hIN hNI
  have hsylC : ABGLocalTools.IsSylowOf p (P ⊓ Cz) Cz := hPsylN.inf_of_le_normalizer hCzN hNCz
  have hIcz : Nat.card (I ⊓ Cz : Subgroup G) ∣ Nat.card (center I) := by
    have hle : I ⊓ Cz ≤ I ⊓ centralizer (I : Set G) := inf_le_inf_left _ inf_le_left
    rw [← card_inf_centralizer]
    exact Subgroup.card_dvd_of_le hle
  have hIcz' : ¬ p ∣ Nat.card (I ⊓ Cz : Subgroup G) := fun h => hZ (h.trans hIcz)
  have hcop : (Nat.card (I ⊓ Cz : Subgroup G)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hIcz'
  have hnormI : Cz ≤ normalizer (I : Set G) := hCzN.trans hNI
  have hprod := card_sup_mul_card_inf_of_le_normalizer hnormI
  have hpos : ∀ X : Subgroup G, Nat.card X ≠ 0 := fun X => Nat.card_pos.ne'
  have hvY : (Nat.card Y).factorization p =
      (Nat.card I).factorization p + (Nat.card Cz).factorization p := by
    have h := congrArg (fun n => n.factorization p) hprod
    simp only [Nat.factorization_mul (hpos _) (hpos _), Finsupp.add_apply] at h
    rw [hcop] at h
    simpa using h
  have hcardY : Nat.card (P ⊓ Y : Subgroup G) =
      Nat.card (P ⊓ I : Subgroup G) * Nat.card (P ⊓ Cz : Subgroup G) := by
    rw [hsylY.card_eq, hsylI.card_eq, hsylC.card_eq, hvY, pow_add]
  have hcent : centralizer (I : Set G) ⊓ P = P ⊓ Cz := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, hx1, hPC hx2⟩
    · rintro ⟨hx1, hx2, -⟩
      exact ⟨hx2, hx1⟩
  rw [hcent]
  have hcomm : ∀ r ∈ P ⊓ I, ∀ w ∈ P ⊓ Cz, r * w * r⁻¹ = w := fun r hr w hw => by
    have := mem_centralizer_iff.1 hw.2.1 r hr.2
    calc r * w * r⁻¹ = w * r * r⁻¹ := by rw [this]
      _ = w := by group
  have hcommQ : P ⊓ I ≤ normalizer ((P ⊓ Cz : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [hcomm r hr z hz]
      exact hz
    · intro hz
      have hr' : r⁻¹ ∈ P ⊓ I := (P ⊓ I).inv_mem hr
      have h1 := hcomm r⁻¹ hr' _ hz
      rw [inv_inv] at h1
      have h2 : r⁻¹ * (r * z * r⁻¹) * r = z := by group
      rw [h2] at h1
      rw [h1]
      exact hz
  have hprodQ := card_sup_mul_card_inf_of_le_normalizer hcommQ
  have hdisj : Nat.card ((P ⊓ Cz) ⊓ (P ⊓ I) : Subgroup G) = 1 := by
    have h1 : Nat.card ((P ⊓ Cz) ⊓ (P ⊓ I) : Subgroup G) ∣ Nat.card (P ⊓ I : Subgroup G) :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hsylI.card_eq] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
    have h2 : Nat.card ((P ⊓ Cz) ⊓ (P ⊓ I) : Subgroup G) ∣ Nat.card (I ⊓ Cz : Subgroup G) := by
      refine Subgroup.card_dvd_of_le fun x hx => ⟨hx.2.2, hx.1.2⟩
    rw [hj] at h2 ⊢
    by_cases hj0 : j = 0
    · simp [hj0]
    · exact absurd (((dvd_pow_self p hj0).trans h2)) hIcz'
  rw [hdisj, mul_one] at hprodQ
  have hPY : P ⊓ (I ⊔ centralizer (I : Set G)) = P ⊓ Y := by
    ext x
    constructor
    · rintro ⟨hxP, hx⟩
      obtain ⟨j, hj, z, hz, rfl⟩ := (mem_sup_centralizer_iff I).1 hx
      have hzC : z ∈ C := by
        have : z = j⁻¹ * (j * z) := by group
        rw [this]
        exact C.mul_mem (C.inv_mem (hIC hj)) (hPC hxP)
      exact ⟨hxP, Subgroup.mul_mem _ (mem_sup_left hj) (mem_sup_right ⟨hz, hzC⟩)⟩
    · rintro ⟨hxP, hx⟩
      exact ⟨hxP, (sup_le_sup_left (inf_le_left : Cz ≤ centralizer (I : Set G)) I) hx⟩
  rw [hPY]
  symm
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · exact sup_le (inf_le_inf_left P (le_sup_right : Cz ≤ I ⊔ Cz))
      (inf_le_inf_left P (le_sup_left : I ≤ I ⊔ Cz))
  · rw [hcardY, hprodQ, mul_comm]

theorem exists_sup_zpowers_eq_of_comparable [Finite G] {P Q : Subgroup G} (hQP : Q ≤ P)
    (h : ∀ u ∈ P, ∀ v ∈ P, u ∈ zpowers v ⊔ Q ∨ v ∈ zpowers u ⊔ Q) :
    ∃ f ∈ P, P = Q ⊔ zpowers f := by
  classical
  obtain ⟨f, hfP, hmax⟩ : ∃ f ∈ P, ∀ u ∈ P,
      Nat.card (zpowers u ⊔ Q : Subgroup G) ≤ Nat.card (zpowers f ⊔ Q : Subgroup G) := by
    have : Fintype P := Fintype.ofFinite P
    obtain ⟨f, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset P)
      (fun u : P => Nat.card (zpowers (u : G) ⊔ Q : Subgroup G)) Finset.univ_nonempty
    exact ⟨f, f.2, fun u hu => hmax ⟨u, hu⟩ (Finset.mem_univ _)⟩
  refine ⟨f, hfP, le_antisymm ?_ (sup_le hQP (zpowers_le.2 hfP))⟩
  intro u hu
  rcases h u hu f hfP with h1 | h2
  · rw [sup_comm]
    exact h1
  · have hle : zpowers f ⊔ Q ≤ zpowers u ⊔ Q := sup_le (zpowers_le.2 h2) le_sup_right
    have heq : zpowers f ⊔ Q = zpowers u ⊔ Q := Subgroup.eq_of_le_of_card_ge hle (hmax u hu)
    have hu' : u ∈ zpowers f ⊔ Q := heq ▸ mem_sup_left (mem_zpowers u)
    rw [sup_comm]
    exact hu'

end CFSG.RankThree.PartOne.K1214
