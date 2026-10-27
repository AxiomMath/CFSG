module

public import CFSG.Quasithin.Recognition.M12AmalAutIso
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.C31SporJ

open CFSG.Open CFSG.Quasithin.AmalTransport

section Exists

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_bot : IsElemAbelian 2 (⊥ : Subgroup G) :=
  CFSG.Open.isElemAbelian_bot _

theorem exists_isMaxElemAbelian (H : Subgroup G) : ∃ A : Subgroup G, IsMaxElemAbelian H A := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  set s := (Finset.univ : Finset (Subgroup G)).filter (fun A => A ≤ H ∧ IsElemAbelian 2 A)
    with hs
  have hbot : (⊥ : Subgroup G) ∈ s := by
    rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, bot_le, isElemAbelian_bot⟩
  obtain ⟨A, hAs, hmax⟩ := s.exists_max_image (fun A => Nat.card A) ⟨⊥, hbot⟩
  rw [hs, Finset.mem_filter] at hAs
  refine ⟨A, hAs.2.1, hAs.2.2, fun B hB hBe => hmax B ?_⟩
  rw [hs, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hB, hBe⟩

end Exists

section Prod

variable {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q]

omit [Finite P] [Finite Q] in
theorem card_prod' (A : Subgroup P) (B : Subgroup Q) :
    Nat.card (A.prod B) = Nat.card A * Nat.card B := by
  rw [Nat.card_congr (Subgroup.prodEquiv A B).toEquiv, Nat.card_prod]

omit [Finite P] [Finite Q] in
theorem isElemAbelian_prod {A : Subgroup P} {B : Subgroup Q} (hA : IsElemAbelian 2 A)
    (hB : IsElemAbelian 2 B) : IsElemAbelian 2 (A.prod B) := by
  obtain ⟨hAc, hAp⟩ := hA
  obtain ⟨hBc, hBp⟩ := hB
  refine ⟨⟨⟨fun x y => Subtype.ext (Prod.ext ?_ ?_)⟩⟩, fun x hx => Prod.ext ?_ ?_⟩
  · exact congrArg Subtype.val (hAc.is_comm.comm ⟨x.1.1, x.2.1⟩ ⟨y.1.1, y.2.1⟩)
  · exact congrArg Subtype.val (hBc.is_comm.comm ⟨x.1.2, x.2.2⟩ ⟨y.1.2, y.2.2⟩)
  · exact hAp x.1 hx.1
  · exact hBp x.2 hx.2

omit [Finite P] [Finite Q] in
theorem le_prod_map_fst_snd (A : Subgroup (P × Q)) :
    A ≤ (A.map (MonoidHom.fst P Q)).prod (A.map (MonoidHom.snd P Q)) :=
  fun x hx => ⟨⟨x, hx, rfl⟩, ⟨x, hx, rfl⟩⟩

theorem card_le_card_mul_of_elemAbelian (A : Subgroup (P × Q)) :
    Nat.card A ≤ Nat.card (A.map (MonoidHom.fst P Q)) * Nat.card (A.map (MonoidHom.snd P Q)) := by
  rw [← card_prod']
  exact Subgroup.card_le_of_le (le_prod_map_fst_snd A)

theorem isMaxElemAbelian_map_of_prod {A : Subgroup (P × Q)} {AP' : Subgroup P}
    {AQ' : Subgroup Q} (hP : IsMaxElemAbelian ⊤ AP') (hQ : IsMaxElemAbelian ⊤ AQ')
    (hA : IsMaxElemAbelian ⊤ A) :
    IsMaxElemAbelian ⊤ (A.map (MonoidHom.fst P Q)) ∧
      IsMaxElemAbelian ⊤ (A.map (MonoidHom.snd P Q)) := by
  have h1 := hA.2.2 (AP'.prod AQ') le_top (isElemAbelian_prod hP.2.1 hQ.2.1)
  rw [card_prod'] at h1
  have h2 := card_le_card_mul_of_elemAbelian A
  have hfe : IsElemAbelian 2 (A.map (MonoidHom.fst P Q)) := isElemAbelian_map _ hA.2.1
  have hse : IsElemAbelian 2 (A.map (MonoidHom.snd P Q)) := isElemAbelian_map _ hA.2.1
  have h3 := hP.2.2 _ le_top hfe
  have h4 := hQ.2.2 _ le_top hse
  have hp1 : 0 < Nat.card (A.map (MonoidHom.fst P Q)) := Nat.card_pos
  have hp2 : 0 < Nat.card (A.map (MonoidHom.snd P Q)) := Nat.card_pos
  have hq1 : 0 < Nat.card AP' := Nat.card_pos
  have hq2 : 0 < Nat.card AQ' := Nat.card_pos
  have e1 : Nat.card (A.map (MonoidHom.fst P Q)) = Nat.card AP' := by
    by_contra hne
    have hlt : Nat.card (A.map (MonoidHom.fst P Q)) < Nat.card AP' := lt_of_le_of_ne h3 hne
    have := Nat.mul_lt_mul_of_lt_of_le hlt h4 hq2
    omega
  have e2 : Nat.card (A.map (MonoidHom.snd P Q)) = Nat.card AQ' := by
    by_contra hne
    have hlt : Nat.card (A.map (MonoidHom.snd P Q)) < Nat.card AQ' := lt_of_le_of_ne h4 hne
    have := Nat.mul_lt_mul_of_le_of_lt h3 hlt hq1
    omega
  refine ⟨⟨le_top, hfe, fun B hB hBe => e1 ▸ hP.2.2 B hB hBe⟩,
    ⟨le_top, hse, fun B hB hBe => e2 ▸ hQ.2.2 B hB hBe⟩⟩

theorem le_thompsonJ_of_isMaxElemAbelian {G : Type*} [Group G] {H A : Subgroup G}
    (hA : IsMaxElemAbelian H A) : A ≤ thompsonJ H :=
  le_iSup₂_of_le A hA le_rfl

theorem thompsonJ_top_prod :
    thompsonJ (⊤ : Subgroup (P × Q)) =
      (thompsonJ (⊤ : Subgroup P)).prod (thompsonJ (⊤ : Subgroup Q)) := by
  obtain ⟨AP, hAP⟩ := exists_isMaxElemAbelian (⊤ : Subgroup P)
  obtain ⟨AQ, hAQ⟩ := exists_isMaxElemAbelian (⊤ : Subgroup Q)
  have hbound : ∀ B : Subgroup (P × Q), IsElemAbelian 2 B →
      Nat.card B ≤ Nat.card (AP.prod AQ) := by
    intro B hB
    rw [card_prod']
    exact (card_le_card_mul_of_elemAbelian B).trans (Nat.mul_le_mul
      (hAP.2.2 _ le_top (isElemAbelian_map _ hB)) (hAQ.2.2 _ le_top (isElemAbelian_map _ hB)))
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    obtain ⟨h1, h2⟩ := isMaxElemAbelian_map_of_prod hAP hAQ hA
    exact (le_prod_map_fst_snd A).trans (Subgroup.prod_mono
      (le_thompsonJ_of_isMaxElemAbelian h1) (le_thompsonJ_of_isMaxElemAbelian h2))
  · have hmaxP : ∀ A : Subgroup P, IsMaxElemAbelian ⊤ A → IsMaxElemAbelian ⊤ (A.prod AQ) :=
      fun A hA => ⟨le_top, isElemAbelian_prod hA.2.1 hAQ.2.1, fun B _ hB => by
        have := hbound B hB
        rwa [card_prod', ← le_antisymm (hAP.2.2 A le_top hA.2.1)
          (hA.2.2 AP le_top hAP.2.1), ← card_prod'] at this⟩
    have hmaxQ : ∀ A : Subgroup Q, IsMaxElemAbelian ⊤ A → IsMaxElemAbelian ⊤ (AP.prod A) :=
      fun A hA => ⟨le_top, isElemAbelian_prod hAP.2.1 hA.2.1, fun B _ hB => by
        have := hbound B hB
        rwa [card_prod', ← le_antisymm (hAQ.2.2 A le_top hA.2.1)
          (hA.2.2 AQ le_top hAQ.2.1), ← card_prod'] at this⟩
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : (x, (1 : Q)) ∈ thompsonJ (⊤ : Subgroup (P × Q)) := by
      have hle : (thompsonJ (⊤ : Subgroup P)).map (MonoidHom.inl P Q) ≤
          thompsonJ (⊤ : Subgroup (P × Q)) := by
        rw [thompsonJ, Subgroup.map_iSup]
        refine iSup_le fun A => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun hA => ?_
        rintro _ ⟨a, ha, rfl⟩
        exact le_thompsonJ_of_isMaxElemAbelian (hmaxP A hA) ⟨ha, Subgroup.one_mem _⟩
      exact hle ⟨x, hx, rfl⟩
    have hy' : ((1 : P), y) ∈ thompsonJ (⊤ : Subgroup (P × Q)) := by
      have hle : (thompsonJ (⊤ : Subgroup Q)).map (MonoidHom.inr P Q) ≤
          thompsonJ (⊤ : Subgroup (P × Q)) := by
        rw [thompsonJ, Subgroup.map_iSup]
        refine iSup_le fun A => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun hA => ?_
        rintro _ ⟨a, ha, rfl⟩
        exact le_thompsonJ_of_isMaxElemAbelian (hmaxQ A hA) ⟨Subgroup.one_mem _, ha⟩
      exact hle ⟨y, hy, rfl⟩
    have := Subgroup.mul_mem _ hx' hy'
    simpa using this

end Prod

section Internal

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem thompsonJ_eq_map_subtype (R : Subgroup G) :
    thompsonJ R = (thompsonJ (⊤ : Subgroup ↥R)).map R.subtype := by
  rw [← thompsonJ_map_of_injective _ R.subtype_injective, Subgroup.map_top, Subgroup.range_subtype]

theorem thompsonJ_sup_of_commute {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXY : X ⊓ Y = ⊥) : thompsonJ (X ⊔ Y) = thompsonJ X ⊔ thompsonJ Y := by
  have hcomm : ∀ (x : ↥X) (y : ↥Y), Commute (X.subtype x) (Y.subtype y) := fun x y => by
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact hc x x.2 y y.2
  set φ : ↥X × ↥Y →* G := MonoidHom.noncommCoprod X.subtype Y.subtype hcomm with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hφ, MonoidHom.noncommCoprod_apply] at hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hxm : (x : G) ∈ X ⊓ Y := ⟨x.2, hx ▸ Y.inv_mem y.2⟩
    rw [hXY, Subgroup.mem_bot] at hxm
    have hxy' : (x : G) * (y : G) = 1 := hxy
    have hy1 : (y : G) = 1 := by rw [hxm, one_mul] at hxy'; exact hxy'
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext hxm) (Subtype.ext hy1)
  have hrange : (⊤ : Subgroup (↥X × ↥Y)).map φ = X ⊔ Y := by
    rw [Subgroup.map_top]
    apply le_antisymm
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right y.2)
    · refine sup_le ?_ ?_
      · intro x hx
        exact ⟨(⟨x, hx⟩, 1), by simp [hφ]⟩
      · intro y hy
        exact ⟨(1, ⟨y, hy⟩), by simp [hφ]⟩
  rw [← hrange, thompsonJ_map_of_injective φ hφinj, thompsonJ_top_prod,
    thompsonJ_eq_map_subtype X, thompsonJ_eq_map_subtype Y]
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have e : φ (a, b) = (a : G) * (b : G) := rfl
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, ha, rfl⟩)
      (Subgroup.mem_sup_right ⟨b, hb, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact ⟨(a, 1), ⟨ha, Subgroup.one_mem _⟩, by simp [hφ]⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact ⟨(1, b), ⟨Subgroup.one_mem _, hb⟩, by simp [hφ]⟩

theorem thompsonJ_ne_bot {R : Subgroup G} (hR : IsPGroup 2 ↥R) (hne : R ≠ ⊥) :
    thompsonJ R ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian R
  have h2 : 2 ∣ Nat.card R := by
    obtain ⟨n, hn⟩ := hR.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq R (by rw [hn, pow_zero]))
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 2 h2
  have hZ : IsElemAbelian 2 (Subgroup.zpowers (t : G)) := by
    refine ⟨inferInstance, fun x hx => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have ht2 : (t : G) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht2, one_zpow]
  have hcard : Nat.card (Subgroup.zpowers (t : G)) = 2 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ht]
  have hle : Subgroup.zpowers (t : G) ≤ R := (Subgroup.zpowers_le).mpr t.2
  have h3 := hA.2.2 _ hle hZ
  intro hJ
  have hAbot : A = ⊥ := le_bot_iff.mp (hJ ▸ le_thompsonJ_of_isMaxElemAbelian hA)
  rw [hAbot, Subgroup.card_bot, hcard] at h3
  omega

omit [Finite G] in
theorem exists_mul_of_mem_sup {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    {g : G} (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, g = x * y := by
  have hcomm : ∀ (x : ↥X) (y : ↥Y), Commute (X.subtype x) (Y.subtype y) := fun x y => by
    show (x : G) * (y : G) = (y : G) * (x : G)
    exact hc x x.2 y y.2
  set φ : ↥X × ↥Y →* G := MonoidHom.noncommCoprod X.subtype Y.subtype hcomm with hφ
  have hle : X ⊔ Y ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨(⟨x, hx⟩, 1), by simp [hφ]⟩
    · intro y hy
      exact ⟨(1, ⟨y, hy⟩), by simp [hφ]⟩
  obtain ⟨⟨x, y⟩, rfl⟩ := hle hg
  exact ⟨x, x.2, y, y.2, rfl⟩

omit [Finite G] in
theorem centerOf_sup_of_commute {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    centerOf (X ⊔ Y) = centerOf X ⊔ centerOf Y := by
  apply le_antisymm
  · rintro g ⟨hg, hgc⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc hg
    have hxc : x ∈ centerOf X := ⟨hx, Subgroup.mem_centralizer_iff.mpr fun x' hx' => by
      have h1 := Subgroup.mem_centralizer_iff.mp hgc x' (Subgroup.mem_sup_left hx')
      have h2 := hc x' hx' y hy
      calc x' * x = (x' * x * y) * y⁻¹ := by group
        _ = (x * y * x') * y⁻¹ := by rw [mul_assoc x' x y, h1]
        _ = x * (y * x') * y⁻¹ := by group
        _ = x * (x' * y) * y⁻¹ := by rw [h2]
        _ = x * x' := by group⟩
    have hyc : y ∈ centerOf Y := ⟨hy, Subgroup.mem_centralizer_iff.mpr fun y' hy' => by
      have h1 := Subgroup.mem_centralizer_iff.mp hgc y' (Subgroup.mem_sup_right hy')
      have h2 := hc x hx y' hy'
      calc y' * y = x⁻¹ * (y' * (x * y)) := by rw [← mul_assoc y', ← h2]; group
        _ = x⁻¹ * (x * y * y') := by rw [h1]
        _ = y * y' := by group⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hxc) (Subgroup.mem_sup_right hyc)
  · refine sup_le ?_ ?_
    · rintro z ⟨hz, hzc⟩
      refine ⟨Subgroup.mem_sup_left hz, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc hg
      have h1 := Subgroup.mem_centralizer_iff.mp hzc x hx
      have h2 := hc z hz y hy
      calc x * y * z = x * (z * y) := by rw [mul_assoc, ← h2]
        _ = z * x * y := by rw [← mul_assoc, h1]
        _ = z * (x * y) := mul_assoc _ _ _
    · rintro z ⟨hz, hzc⟩
      refine ⟨Subgroup.mem_sup_right hz, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc hg
      have h1 := Subgroup.mem_centralizer_iff.mp hzc y hy
      have h2 := hc x hx z hz
      calc x * y * z = x * (z * y) := by rw [mul_assoc, h1]
        _ = z * x * y := by rw [← mul_assoc, h2]
        _ = z * (x * y) := mul_assoc _ _ _

omit [Finite G] in
theorem omegaOneOf_sup_of_commute {X Y : Subgroup G} (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x)
    (hXY : X ⊓ Y = ⊥) : omegaOneOf (X ⊔ Y) = omegaOneOf X ⊔ omegaOneOf Y := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨hg, hg2⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_mul_of_mem_sup hc hg
    have hxy2 : x ^ 2 * y ^ 2 = 1 := by
      rw [← hg2, pow_two, pow_two, pow_two]
      calc x * x * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hc x hx y hy]
        _ = x * y * (x * y) := by group
    have hx2m : x ^ 2 ∈ X ⊓ Y := ⟨X.pow_mem hx 2, by
      rw [eq_inv_of_mul_eq_one_left hxy2]
      exact Y.inv_mem (Y.pow_mem hy 2)⟩
    rw [hXY, Subgroup.mem_bot] at hx2m
    have hy2 : y ^ 2 = 1 := by rw [hx2m, one_mul] at hxy2; exact hxy2
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hx, hx2m⟩))
      (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hy, hy2⟩))
  · refine sup_le ?_ ?_
    · exact (Subgroup.closure_le _).mpr fun g hg =>
        Subgroup.subset_closure ⟨Subgroup.mem_sup_left hg.1, hg.2⟩
    · exact (Subgroup.closure_le _).mpr fun g hg =>
        Subgroup.subset_closure ⟨Subgroup.mem_sup_right hg.1, hg.2⟩

end Internal

end CFSG.Quasithin.C31SporJ
