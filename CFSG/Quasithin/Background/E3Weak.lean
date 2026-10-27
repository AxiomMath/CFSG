module

public import CFSG.Quasithin.Background.E3Basic
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.A1bGroups

public section

namespace CFSG.Quasithin

namespace E3

open CFSG.Open
open scoped commutatorElement

universe u

section Weak

variable {G : Type u} [Group G] {V : Subgroup G}

theorem mem_gammaSet_iff {i : ℕ} {X A : Subgroup G} :
    A ∈ gammaSet V i X ↔
      A ≤ X ∧ ∃ g : G, A ≤ conjSubgroup V g ∧ mQuot (conjSubgroup V g) A = i := Iff.rfl

theorem le_wClos {i : ℕ} {X A : Subgroup G} (hA : A ∈ gammaSet V i X) : A ≤ wClos V i X :=
  le_iSup₂ (f := fun A (_ : A ∈ gammaSet V i X) => A) A hA

theorem wClos_le_of_forall {i : ℕ} {X Z : Subgroup G} (h : ∀ A ∈ gammaSet V i X, A ≤ Z) :
    wClos V i X ≤ Z :=
  iSup₂_le h

theorem wClos_le (i : ℕ) (X : Subgroup G) : wClos V i X ≤ X :=
  wClos_le_of_forall fun _ hA => hA.1

theorem gammaSet_mono {i : ℕ} {X X' : Subgroup G} (h : X ≤ X') :
    gammaSet V i X ⊆ gammaSet V i X' := fun _ hA => ⟨hA.1.trans h, hA.2⟩

theorem wClos_mono {i : ℕ} {X X' : Subgroup G} (h : X ≤ X') : wClos V i X ≤ wClos V i X' :=
  wClos_le_of_forall fun _ hA => le_wClos (gammaSet_mono h hA)

theorem conjSubgroup_le_iff_le_inv {A B : Subgroup G} (h : G) :
    conjSubgroup A h ≤ B ↔ A ≤ conjSubgroup B h⁻¹ := by
  have := conjSubgroup_le_conjSubgroup_iff (A := conjSubgroup A h) (B := B) h⁻¹
  rw [conjSubgroup_conj_inv] at this
  exact this.symm

theorem le_conjSubgroup_iff_inv_le {A B : Subgroup G} (h : G) :
    A ≤ conjSubgroup B h ↔ conjSubgroup A h⁻¹ ≤ B := by
  rw [conjSubgroup_le_iff_le_inv, inv_inv]

theorem gammaMember_conj {i : ℕ} {A : Subgroup G} (h : G)
    (hA : ∃ g : G, A ≤ conjSubgroup V g ∧ mQuot (conjSubgroup V g) A = i) :
    ∃ g : G, conjSubgroup A h ≤ conjSubgroup V g ∧
      mQuot (conjSubgroup V g) (conjSubgroup A h) = i := by
  obtain ⟨g, hAg, hm⟩ := hA
  refine ⟨g * h, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup]
    exact conjSubgroup_mono_left h hAg
  · rw [← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
    exact hm

theorem conj_mem_gammaSet {i : ℕ} {X A : Subgroup G} (h : G) (hA : A ∈ gammaSet V i X) :
    conjSubgroup A h ∈ gammaSet V i (conjSubgroup X h) :=
  ⟨conjSubgroup_mono_left h hA.1, gammaMember_conj h hA.2⟩

theorem gammaSet_conjV {i : ℕ} (g : G) (X : Subgroup G) :
    gammaSet (conjSubgroup V g) i X = gammaSet V i X := by
  ext A
  constructor
  · rintro ⟨hAX, g', hAg', hm⟩
    refine ⟨hAX, g * g', ?_, ?_⟩
    · rwa [← conjSubgroup_conjSubgroup]
    · rwa [← conjSubgroup_conjSubgroup]
  · rintro ⟨hAX, g', hAg', hm⟩
    refine ⟨hAX, g⁻¹ * g', ?_, ?_⟩
    · rwa [conjSubgroup_conjSubgroup, mul_inv_cancel_left]
    · rwa [conjSubgroup_conjSubgroup, mul_inv_cancel_left]

theorem wClos_conjV {i : ℕ} (g : G) (X : Subgroup G) :
    wClos (conjSubgroup V g) i X = wClos V i X := by
  unfold wClos
  rw [gammaSet_conjV]

theorem cClos_conjV {i : ℕ} (g : G) (X : Subgroup G) :
    cClos (conjSubgroup V g) i X = cClos V i X := by
  unfold cClos
  rw [wClos_conjV]

theorem conjSubgroup_wClos_le {i : ℕ} (X : Subgroup G) (h : G) :
    conjSubgroup (wClos V i X) h ≤ wClos V i (conjSubgroup X h) := by
  rw [conjSubgroup_le_iff_le_inv]
  refine wClos_le_of_forall fun A hA => ?_
  rw [le_conjSubgroup_iff_inv_le, inv_inv]
  exact le_wClos (conj_mem_gammaSet h hA)

theorem wClos_conj {i : ℕ} (X : Subgroup G) (h : G) :
    wClos V i (conjSubgroup X h) = conjSubgroup (wClos V i X) h := by
  refine le_antisymm ?_ (conjSubgroup_wClos_le X h)
  have := conjSubgroup_wClos_le (V := V) (i := i) (conjSubgroup X h) h⁻¹
  rw [conjSubgroup_conj_inv] at this
  have h2 := (conjSubgroup_le_iff_le_inv h⁻¹).1 this
  rwa [inv_inv] at h2

theorem cClos_conj {i : ℕ} (X : Subgroup G) (h : G) :
    cClos V i (conjSubgroup X h) = conjSubgroup (cClos V i X) h := by
  unfold cClos
  rw [conjSubgroup_inf, conjSubgroup_centralizer, wClos_conj]

theorem normalizer_le_normalizer_wClos {i : ℕ} (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (wClos V i X : Set G) := by
  intro h hh
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hh ⊢
  rw [← wClos_conj, hh]

theorem normalizer_le_normalizer_cClos {i : ℕ} (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (cClos V i X : Set G) := by
  intro h hh
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hh ⊢
  rw [← cClos_conj, hh]

section Sylow

variable [Finite G]

theorem exists_le_conj_of_isSylowIn {H S Y : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) : ∃ h ∈ H, Y ≤ conjSubgroup S h := by
  obtain ⟨h, hh, hle⟩ := exists_conj_le_of_isSylowTwoOf hS hYH hY
  refine ⟨h, hh, fun y hy => ?_⟩
  rw [mem_conjSubgroup_iff]
  apply hle
  rw [mem_cjSub]
  have e : h⁻¹ * (h * y * h⁻¹) * h = y := by group
  rw [e]
  exact hy

theorem e3_15 {i : ℕ} {H S Y : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) (hW : wClos V i S ≤ Y) : wClos V i S = wClos V i Y := by
  have h1 : wClos V i S ≤ wClos V i Y :=
    wClos_le_of_forall fun A hA => le_wClos ⟨(le_wClos hA).trans hW, hA.2⟩
  obtain ⟨h, -, hYS⟩ := exists_le_conj_of_isSylowIn hS hYH hY
  have h2 : wClos V i Y ≤ conjSubgroup (wClos V i S) h :=
    calc wClos V i Y ≤ wClos V i (conjSubgroup S h) := wClos_mono hYS
      _ = conjSubgroup (wClos V i S) h := wClos_conj S h
  refine Subgroup.eq_of_le_of_card_ge h1 ?_
  calc Nat.card (wClos V i Y) ≤ Nat.card (conjSubgroup (wClos V i S) h) :=
        Subgroup.card_le_of_le h2
    _ = Nat.card (wClos V i S) := card_conjSubgroup _ _

theorem e3_15_weaklyClosed {i : ℕ} {H S Y : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) (hW : wClos V i S ≤ Y) : IsWeaklyClosedIn (wClos V i S) Y := by
  have heq := e3_15 hS hYH hY hW
  intro g hg
  have hle : conjSubgroup (wClos V i S) g ≤ wClos V i S := by
    rw [conjSubgroup_le_iff_le_inv]
    calc wClos V i S = wClos V i Y := heq
      _ ≤ conjSubgroup (wClos V i S) g⁻¹ := by
        refine wClos_le_of_forall fun A hA => ?_
        rw [le_conjSubgroup_iff_inv_le, inv_inv]
        rw [heq]
        exact le_wClos ⟨(conjSubgroup_mono_left g ((le_wClos hA))).trans (heq ▸ hg),
          gammaMember_conj g hA.2⟩
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem e3_15_normalizer {i : ℕ} {H S Y : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) (hW : wClos V i S ≤ Y) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (wClos V i S : Set G) := by
  rw [e3_15 hS hYH hY hW]
  exact normalizer_le_normalizer_wClos Y

end Sylow

theorem wClos_eq_weakClosure {i : ℕ} (X : Subgroup G) :
    wClos V i X = E1.weakClosure X (gammaSet V i ⊤) := by
  unfold wClos E1.weakClosure
  refine le_antisymm ?_ ?_
  · exact iSup₂_le fun A hA => le_iSup₂_of_le A ⟨le_top, hA.2⟩ (le_iSup_of_le hA.1 le_rfl)
  · refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
    exact le_iSup₂_of_le A ⟨hAX, hA.2⟩ le_rfl

theorem weakClosure_gammaSet {i : ℕ} {S H : Subgroup G} (hSH : S ≤ H) :
    E1.weakClosure S (gammaSet V i H) = wClos V i S := by
  unfold wClos E1.weakClosure
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => iSup_le fun hAS => ?_
    exact le_iSup₂_of_le A ⟨hAS, hA.2⟩ le_rfl
  · exact iSup₂_le fun A hA => le_iSup₂_of_le A ⟨hA.1.trans hSH, hA.2⟩
      (le_iSup_of_le hA.1 le_rfl)

theorem isInvColl_gammaSet (hV : IsElemAbelian 2 V) (i : ℕ) (H : Subgroup G) :
    E1.IsInvColl H (gammaSet V i H) where
  le A hA := hA.1
  isElemAbelian A hA := by
    obtain ⟨-, g, hAg, -⟩ := hA
    exact B2F.isElemAbelian_mono hAg (isElemAbelian_conjSubgroup hV g)
  conj A hA h hh := by
    have h1 := conj_mem_gammaSet h⁻¹ hA
    have h2 : conjSubgroup H h⁻¹ = H :=
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer (H.inv_mem hh))
    rw [h2] at h1
    have h3 := conjSubgroup_eq_conjSub A h⁻¹
    rw [inv_inv] at h3
    rw [← h3]
    exact h1

theorem wClos_ne_bot [Finite G] (hV : IsElemAbelian 2 V) {X : Subgroup G} (hVX : V ≤ X) {i : ℕ}
    (hi : i < rk ↥V) : wClos V i X ≠ ⊥ := by
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hcard : Nat.card V = 2 ^ rk ↥V := card_eq_two_pow_of_isPGroup hV2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥V) 2 (n := rk ↥V - i)
    (by rw [hcard]; exact pow_dvd_pow 2 (Nat.sub_le _ _))
  have hAV : K.map V.subtype ≤ V := Subgroup.map_subtype_le K
  have hAcard : Nat.card (K.map V.subtype) = 2 ^ (rk ↥V - i) := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hK]
  have hm : mQuot V (K.map V.subtype) = i := by
    have h := card_eq_two_pow_mul hV2 hAV
    rw [hcard, hAcard, ← pow_add] at h
    have h' := Nat.pow_right_injective (le_refl 2) h
    omega
  have hmem : K.map V.subtype ∈ gammaSet V i X :=
    ⟨hAV.trans hVX, 1, by rw [conjSubgroup_one]; exact hAV, by rw [conjSubgroup_one]; exact hm⟩
  intro hbot
  have h1 : K.map V.subtype = ⊥ := le_bot_iff.1 (hbot ▸ le_wClos hmem)
  rw [h1] at hAcard
  have : (1 : ℕ) = 2 ^ (rk ↥V - i) := by simpa using hAcard
  have h2 : rk ↥V - i = 0 := by
    have := Nat.pow_right_injective (le_refl 2) (this.symm.trans (pow_zero 2).symm)
    exact this
  omega

end Weak

section Unique

variable {G : Type u} [Group G] [Finite G] {V : Subgroup G}

theorem centerOf_ne_bot_of_isPGroup {W : Subgroup G} (hW : IsPGroup 2 W) (h1 : W ≠ ⊥) :
    centerOf W ≠ ⊥ := by
  have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr h1
  have hc : Nontrivial (Subgroup.center W) := hW.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center W)
  intro h
  apply hz
  have hzW : (z : W) ∈ Subgroup.center W := z.2
  have hz' : ((z : W) : G) ∈ centerOf W := by
    refine ⟨(z : W).2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    have := Subgroup.mem_center_iff.1 hzW ⟨w, hw⟩
    exact congrArg Subtype.val this
  rw [h, Subgroup.mem_bot] at hz'
  exact Subtype.ext (Subtype.ext hz')

omit [Finite G] in
theorem normalizer_le_normalizer_centerOf (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (centerOf W : Set G) := by
  intro n hn
  rw [← conjSubgroup_eq_iff_mem_normalizer] at hn ⊢
  unfold centerOf
  rw [conjSubgroup_inf, conjSubgroup_centralizer, hn]

theorem e3_16_one {i : ℕ} {H S Y N : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) (hW : wClos V i S ≤ Y) (hW1 : wClos V i S ≠ ⊥)
    (hN : IsUniqueM (Subgroup.normalizer (Y : Set G)) N) :
    Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (wClos V i S : Set G) ∧
      Subgroup.normalizer (wClos V i S : Set G) ≤ N := by
  have h1 := e3_15_normalizer hS hYH hY hW
  refine ⟨h1, ?_⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (wClos V i S : Set G)) :=
    ⟨_, hW1, hY.to_le hW, rfl⟩
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge hloc
  have hMN : M = N := hN.2 M ⟨hM, h1.trans hle⟩
  rw [← hMN]
  exact hle

theorem e3_16_two {i : ℕ} {H S Y N : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) (hW : wClos V i S ≤ Y) (hW1 : wClos V i S ≠ ⊥)
    (hN : IsUniqueM (Subgroup.normalizer (Y : Set G)) N) :
    IsUniqueM (Subgroup.normalizer (wClos V i S : Set G)) N := by
  obtain ⟨h1, h2⟩ := e3_16_one hS hYH hY hW hW1 hN
  exact ⟨⟨hN.1.1, h2⟩, fun M' hM' => hN.2 M' ⟨hM'.1, h1.trans hM'.2⟩⟩

theorem e3_16_three {i : ℕ} {H S Y N : Subgroup G} (hS : IsSylowIn 2 S H) (hYH : Y ≤ H)
    (hY : IsPGroup 2 Y) (hW : wClos V i S ≤ Y) (hW1 : wClos V i S ≠ ⊥)
    (hN : IsUniqueM (Subgroup.normalizer (Y : Set G)) N) :
    Subgroup.centralizer (cClos V i S : Set G) ≤ N := by
  have h1 := e3_15_normalizer hS hYH hY hW
  have hW2 : IsPGroup 2 (wClos V i S) := hY.to_le hW
  have hZ1 : centerOf (wClos V i S) ≠ ⊥ := centerOf_ne_bot_of_isPGroup hW2 hW1
  have hZ2 : IsPGroup 2 (centerOf (wClos V i S)) := hW2.to_le inf_le_left
  have hloc : IsTwoLocal (Subgroup.normalizer (centerOf (wClos V i S) : Set G)) :=
    ⟨_, hZ1, hZ2, rfl⟩
  obtain ⟨M, hM, hle⟩ := exists_maxTwoLocal_ge hloc
  have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer
      (centerOf (wClos V i S) : Set G) :=
    h1.trans (normalizer_le_normalizer_centerOf _)
  have hMN : M = N := hN.2 M ⟨hM, hNY.trans hle⟩
  have hZC : centerOf (wClos V i S) ≤ cClos V i S :=
    le_inf (inf_le_left.trans (wClos_le i S)) inf_le_right
  refine (Subgroup.centralizer_le hZC).trans ?_
  refine (Subgroup.centralizer_le_normalizer _).trans ?_
  rw [← hMN]
  exact hle

end Unique

end E3

end CFSG.Quasithin
