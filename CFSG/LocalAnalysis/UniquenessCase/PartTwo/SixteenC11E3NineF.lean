module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10PerfL3
public import CFSG.GroupTheory.SupCommute

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem s1611e3_card_prod {M N : Type*} [Group M] [Group N]
    (H : Subgroup M) (K : Subgroup N) : Nat.card ↥(H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

private theorem s1611e3_center_inf_commutator_prod {M Q : Type*} [Group M] [Group Q]
    [IsMulCommutative M] (hQc : Subgroup.center Q = ⊥) (hQp : _root_.commutator Q = ⊤) :
    Subgroup.center (M × Q × Q) ⊓ _root_.commutator (M × Q × Q) = ⊥ := by
  have hQc' : Subgroup.center (Q × Q) = ⊥ := by
    rw [Subgroup.center_prod, hQc, Subgroup.bot_prod_bot]
  have hcenter : Subgroup.center (M × Q × Q) =
      (⊤ : Subgroup M).prod (⊥ : Subgroup (Q × Q)) := by
    rw [Subgroup.center_prod, Subgroup.center_eq_top, hQc']
  have hcomm : _root_.commutator (M × Q × Q) =
      (⊥ : Subgroup M).prod (⊤ : Subgroup (Q × Q)) := by
    rw [_root_.commutator, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod]
    congr 1
    · exact commutator_eq_bot (G := M)
    · rw [← Subgroup.top_prod_top (G := Q) (N := Q), Subgroup.commutator_prod_prod,
        show ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ from hQp, Subgroup.top_prod_top]
  rw [hcenter, hcomm]
  ext x
  simp [Subgroup.mem_prod, Prod.ext_iff, and_comm]

theorem s1611e3_nine_center_card {F : Type} [Group F] [Finite F] {Q : Type} [Group Q]
    [Finite Q] (hQ : IsL3 Q 1) (e : F ≃* Multiplicative (ZMod 7) × Q × Q) :
    Nat.card ↥(Subgroup.center F) = 7 := by
  have hQc : Subgroup.center Q = ⊥ := center_eq_bot_of_isL3 hQ
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
  rw [Subgroup.center_prod, Subgroup.center_prod, Subgroup.center_eq_top, hQc,
    Subgroup.bot_prod_bot, s1611e3_card_prod, Subgroup.card_bot, mul_one, Subgroup.card_top]
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem s1611e3_nine_abstract_faith {A : Type} [Group A] [Finite A]
    {X F L L' : Subgroup A} {Q : Type} [Group Q] [Finite Q]
    (hQ : IsL3 Q 1) (e : ↥F ≃* Multiplicative (ZMod 7) × Q × Q)
    (hself : ∀ x ∈ X, (∀ f ∈ F, x * f = f * x) → x ∈ F)
    (hLF : L ≤ F) (hL'F : L' ≤ F) (hL3 : IsL3 ↥L 1) (hL'3 : IsL3 ↥L' 1)
    (hcomm : ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) (hne : L ≠ L')
    {x : A} (hxX : x ∈ X) (hx2 : x * x = 1)
    (hxL : ∀ a ∈ L, x * a = a * x) (hxL' : ∀ b ∈ L', x * b = b * x)
    (hxZ : ∀ z : ↥F, z ∈ Subgroup.center ↥F → x * (z : A) = (z : A) * x) :
    x = 1 := by
  have hQc : Subgroup.center Q = ⊥ := center_eq_bot_of_isL3 hQ
  have hQp : _root_.commutator Q = ⊤ := s16c1610_commutator_of_isL3 hQ
  have hQcard : Nat.card Q = 168 := card_eq_of_isL3 hQ
  have hLcard : Nat.card ↥L = 168 := card_eq_of_isL3 hL3
  have hL'card : Nat.card ↥L' = 168 := card_eq_of_isL3 hL'3
  have hLinf : L ⊓ L' = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hcent : (⟨w, hw.1⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      simpa using hcomm g g.2 w hw.2
    rw [center_eq_bot_of_isL3 hL3, Subgroup.mem_bot] at hcent
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcent
  have hmapL : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapL' : (⊤ : Subgroup ↥L').map L'.subtype = L' := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmapF : (⊤ : Subgroup ↥F).map F.subtype = F := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hLcomm_eq : ⁅L, L⁆ = L := by
    have h1 : ⁅L, L⁆ = (_root_.commutator ↥L).map L.subtype := by
      rw [_root_.commutator, Subgroup.map_commutator]
      congr 1 <;> exact hmapL.symm
    rw [h1, show _root_.commutator ↥L = ⊤ from s16c1610_commutator_of_isL3 hL3, hmapL]
  have hL'comm_eq : ⁅L', L'⁆ = L' := by
    have h1 : ⁅L', L'⁆ = (_root_.commutator ↥L').map L'.subtype := by
      rw [_root_.commutator, Subgroup.map_commutator]
      congr 1 <;> exact hmapL'.symm
    rw [h1, show _root_.commutator ↥L' = ⊤ from s16c1610_commutator_of_isL3 hL'3, hmapL']
  have hLperf : L ≤ ⁅F, F⁆ := hLcomm_eq ▸ Subgroup.commutator_mono hLF hLF
  have hL'perf : L' ≤ ⁅F, F⁆ := hL'comm_eq ▸ Subgroup.commutator_mono hL'F hL'F
  set Zc : Subgroup A := (Subgroup.center ↥F).map F.subtype with hZcdef
  have hZc_le_F : Zc ≤ F := Subgroup.map_subtype_le _
  have hZc_card : Nat.card ↥Zc = 7 := by
    rw [hZcdef, Subgroup.card_map_of_injective (f := F.subtype) F.subtype_injective,
      Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [Subgroup.center_prod, Subgroup.center_prod, Subgroup.center_eq_top, hQc,
      Subgroup.bot_prod_bot, s1611e3_card_prod, Subgroup.card_bot, mul_one,
      Subgroup.card_top]
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hFcard : Nat.card ↥F = 7 * (168 * 168) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, ZMod.card, hQcard]
  have hLsup_card : Nat.card ↥(L ⊔ L') = 168 * 168 := by
    rw [CFSG.card_sup_eq_mul_of_commute L L' (fun a ha b hb => hcomm a ha b hb) hLinf,
      hLcard, hL'card]
  have hmapFcomm : (_root_.commutator ↥F).map F.subtype = ⁅F, F⁆ := by
    rw [_root_.commutator, Subgroup.map_commutator]
    congr 1 <;> exact hmapF.symm
  have hcenterinf : Subgroup.center ↥F ⊓ _root_.commutator ↥F = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective
      (Subgroup.center ↥F ⊓ _root_.commutator ↥F) (f := e.toMonoidHom) e.injective).1 ?_
    rw [Subgroup.map_inf _ _ _ e.injective]
    rw [show (Subgroup.center ↥F).map e.toMonoidHom =
        Subgroup.center (Multiplicative (ZMod 7) × Q × Q) from Subgroup.map_center_eq e]
    have h3 : (_root_.commutator ↥F).map e.toMonoidHom =
        _root_.commutator (Multiplicative (ZMod 7) × Q × Q) := by
      rw [_root_.commutator, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]
      rfl
    rw [h3]
    exact s1611e3_center_inf_commutator_prod hQc hQp
  have hZD : Zc ⊓ ⁅F, F⁆ = ⊥ := by
    rw [hZcdef, ← hmapFcomm, ← Subgroup.map_inf _ _ _ F.subtype_injective, hcenterinf,
      Subgroup.map_bot]
  have hZinf : Zc ⊓ (L ⊔ L') = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have hw' : w ∈ Zc ⊓ ⁅F, F⁆ := ⟨hw.1, sup_le hLperf hL'perf hw.2⟩
    rwa [hZD, Subgroup.mem_bot] at hw'
  have hZs_comm : ∀ a ∈ Zc, ∀ b ∈ L ⊔ L', a * b = b * a := by
    intro a ha b hb
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
    simpa [Subgroup.coe_mul] using congrArg (fun w : ↥F => (w : A))
      (Subgroup.mem_center_iff.mp hz ⟨b, (sup_le hLF hL'F) hb⟩).symm
  have hZs_card : Nat.card ↥(Zc ⊔ L ⊔ L') = 7 * (168 * 168) := by
    rw [sup_assoc, CFSG.card_sup_eq_mul_of_commute Zc (L ⊔ L') hZs_comm hZinf,
      hZc_card, hLsup_card]
  have hZs_le : Zc ⊔ L ⊔ L' ≤ F := sup_le (sup_le hZc_le_F hLF) hL'F
  have hZsup : Zc ⊔ L ⊔ L' = F := by
    refine Subgroup.eq_of_le_of_card_ge hZs_le ?_
    rw [hFcard, hZs_card]
  have hxF_comm : ∀ f ∈ F, x * f = f * x := by
    rw [← hZsup]
    have hle : Zc ⊔ L ⊔ L' ≤ Subgroup.centralizer ({x} : Set A) := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro a ha
        rw [hZcdef] at ha
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hxZ z hz
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hxL a ha
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        rw [Set.mem_singleton_iff] at hb
        subst hb
        exact hxL' a ha
    intro f hf
    have h := hle hf
    rw [Subgroup.mem_centralizer_iff] at h
    exact h x (Set.mem_singleton x)
  have hxF : x ∈ F := hself x hxX hxF_comm
  have hxZc : x ∈ Zc := by
    rw [hZcdef]
    refine Subgroup.mem_map.2 ⟨⟨x, hxF⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    simpa using (hxF_comm g g.2).symm
  have hxord : orderOf x ∣ 7 := by
    have h := orderOf_dvd_natCard (⟨x, hxZc⟩ : Zc)
    rw [hZc_card, ← Subgroup.orderOf_coe (⟨x, hxZc⟩ : Zc)] at h
    exact h
  have hd2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hx2)
  have hd1 : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd hd2 hxord
    simpa using this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
