module

public import CFSG.Quasithin.Background.RonanE114Good
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuL32
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312RuSimple
public import CFSG.Quasithin.EmptyFaithful.ModHHe2

public section

namespace CFSG.Quasithin.RonanE114.HeOver

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He1
  CFSG.Quasithin.ModH.He2
open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.E2P.SporB

section Lattice

variable {J : Type} [Group J] [Finite J]

theorem hall_7168_of_21504 {h k : ℕ} (hr : h * k = 21504)
    (hh : ∀ q : ℕ, q.Prime → q ∣ h → q = 2 ∨ q = 7) (hk2 : ¬ 2 ∣ k) (hk7 : ¬ 7 ∣ k) :
    h = 7168 := by
  have hk : k ∣ 7168 * 3 := ⟨h, by rw [show 7168 * 3 = 21504 by norm_num, ← hr]; ring⟩
  have hc2 : Nat.Coprime (2 ^ 10) k :=
    Nat.Coprime.pow_left 10 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hk2)
  have hc7 : Nat.Coprime 7 k := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hk7
  have hc : Nat.Coprime 7168 k := by
    have := Nat.Coprime.mul_left hc2 hc7
    simpa using this
  have hk3 : k ∣ 3 := Nat.Coprime.dvd_of_dvd_mul_left hc.symm hk
  have hkle : k ≤ 3 := Nat.le_of_dvd (by norm_num) hk3
  interval_cases k <;>
    first
    | omega
    | (exfalso; have := hh 3 (by norm_num) (by omega); omega)

omit [Finite J] in
theorem card_Y7 (hl : HeLat J) : Nat.card ↥(hl.Y 7) = 21504 := by
  rw [hl.card_Y 7 (by norm_num)]
  rfl

theorem heY7_not_solvable (hl : HeLat J) : ¬ Group.IsSolvable ↥(hl.Y 7) := by
  intro hZs
  have hU : IsPGroup 2 ↥(hl.S.subgroupOf (hl.Y 7)) :=
    hl.S_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe (hl.S_le_Y 7)).symm
  obtain ⟨H, hUH, hHq, hk2, hk7⟩ :=
    M24a.exists_hall_two_p hZs (hl.S.subgroupOf (hl.Y 7)) hU 7 (by norm_num)
  have hSH : hl.S ≤ H.map (hl.Y 7).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (hl.S_le_Y 7)]
    exact Subgroup.map_mono hUH
  have hcardH : Nat.card ↥(H.map (hl.Y 7).subtype) = Nat.card ↥H :=
    (Nat.card_congr (H.equivMapOfInjective (hl.Y 7).subtype Subtype.val_injective).toEquiv).symm
  have h7168 : Nat.card ↥H = 7168 :=
    hall_7168_of_21504 (h := Nat.card ↥H) (k := H.index)
      (by rw [Subgroup.card_mul_index H]; exact card_Y7 hl) hHq hk2 hk7
  rcases member_of_complete hl hSH with ⟨j, hj, hjeq⟩ | htop
  · have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) hjeq
    rw [hcardH, h7168, hl.card_Y j hj] at h1
    interval_cases j <;> revert h1 <;> decide
  · have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) htop
    rw [hcardH, h7168, card_top hl] at h1
    omega

theorem heY7_levi (hl : HeLat J) (h128 : Nat.card (CFSG.pCore 2 ↥(hl.Y 7)) = 128) :
    ∃ f : ↥(hl.Y 7) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  classical
  have hns := heY7_not_solvable hl
  have hle87 : hl.Y 8 ≤ hl.Y 7 := (hl.le_iff (by norm_num) (by norm_num)).mpr (by decide)
  have hcard : Nat.card ↥(hl.Y 7) = 2 ^ 10 * 3 * 7 := by rw [card_Y7 hl]; norm_num
  have hcard' : Nat.card ↥((hl.Y 8).subgroupOf (hl.Y 7)) = 2 ^ 10 * 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle87).toEquiv, hl.card_Y 8 (by norm_num)]
    rfl
  obtain ⟨ρ, hker, htr⟩ := A312Ru.exists_hom_perm hns (Y' := (hl.Y 8).subgroupOf (hl.Y 7))
    (e := 10) (p := 7) (by norm_num) (by norm_num) hcard hcard'
  have hcardR : Nat.card ρ.range = 168 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hker, h128,
      card_Y7 hl] at h1
    omega
  have hnsR : ¬ Group.IsSolvable ρ.range := fun hGs => by
    apply hns
    have h2 : IsPGroup 2 ρ.ker := by rw [hker]; exact CFSG.pCore_isPGroup
    have : Group.IsNilpotent ρ.ker := h2.isNilpotent
    exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ.rangeRestrict
      (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])
  have hsimple : IsSimpleGroup ρ.range := A312Ru.isSimpleGroup_of_card_168 hcardR hnsR
  have hpsl : IsPSL 3 2 1 ρ.range :=
    A312Ru.isPSL_three_two_of_perm_seven hcardR ρ.range.subtype (Subgroup.subtype_injective _)
      (fun i j => by
        obtain ⟨y, hy⟩ := htr i j
        exact ⟨⟨ρ y, y, rfl⟩, hy⟩)
  obtain ⟨φ⟩ := P7.exists_mulEquiv_sl3_of_isPSL hpsl
  refine ⟨φ.toMonoidHom.comp ρ.rangeRestrict,
    φ.surjective.comp (MonoidHom.rangeRestrict_surjective ρ), ?_⟩
  have hk : (φ.toMonoidHom.comp ρ.rangeRestrict).ker = ρ.ker := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [map_eq_one_iff φ φ.injective, ← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]
    rfl
  rw [hk, hker]
  exact CFSG.pCore_isPGroup

@[expose] def heIdx (j : ℕ) : ℕ := #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]!

omit [Finite J] in
theorem card_Y_idx (hl : HeLat J) {j : ℕ} (hj : j < 11) :
    Nat.card ↥(hl.Y j) = heIdx j * 1024 := hl.card_Y j hj

omit [Finite J] in
theorem card_Y_lt (hl : HeLat J) {j : ℕ} (hj : j < 11) : Nat.card ↥(hl.Y j) < Nat.card J := by
  rw [card_Y_idx hl hj, hl.card_J]
  have : ∀ j < 11, heIdx j * 1024 < 2 ^ 10 * 3935925 := by decide
  exact this j hj

omit [Finite J] in
theorem map_member (hl : HeLat J) {α : MulAut J} (hα : hl.S.map α.toMonoidHom = hl.S) {a : ℕ}
    (ha : a < 11) : ∃ j < 11, (hl.Y a).map α.toMonoidHom = hl.Y j ∧ heIdx j = heIdx a := by
  have hS := S_le_map hl (hl.S_le_Y a) hα
  have hc : Nat.card ↥((hl.Y a).map α.toMonoidHom) = Nat.card ↥(hl.Y a) := card_map_aut α _
  rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
  · refine ⟨j, hj, hjeq, ?_⟩
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) hjeq
    rw [hc, card_Y_idx hl ha, card_Y_idx hl hj] at h1
    omega
  · exfalso
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) htop
    rw [hc, card_top hl] at h1
    have := card_Y_lt hl ha
    rw [hl.card_J] at this
    omega

omit [Finite J] in
theorem map_of_below (hl : HeLat J) {α : MulAut J} (hα : hl.S.map α.toMonoidHom = hl.S)
    {a b c a' b' c' : ℕ} (ha : a < 11) (hb' : b' < 11) (hc' : c' < 11) (ha' : a' < 11)
    (hab : hl.Y a ≤ hl.Y b) (hac : hl.Y a ≤ hl.Y c)
    (hbα : (hl.Y b).map α.toMonoidHom = hl.Y b') (hcα : (hl.Y c).map α.toMonoidHom = hl.Y c')
    (htab : ∀ j < 11, heIdx j = heIdx a → b' ∈ heIncl[j]! → c' ∈ heIncl[j]! → j = a') :
    (hl.Y a).map α.toMonoidHom = hl.Y a' := by
  obtain ⟨j, hj, hjeq, hidx⟩ := map_member hl hα ha
  have h1 : (hl.Y a).map α.toMonoidHom ≤ hl.Y b' := hbα ▸ Subgroup.map_mono hab
  have h2 : (hl.Y a).map α.toMonoidHom ≤ hl.Y c' := hcα ▸ Subgroup.map_mono hac
  rw [hjeq] at h1 h2 ⊢
  rw [htab j hj hidx ((hl.le_iff hj hb').mp h1) ((hl.le_iff hj hc').mp h2)]

omit [Finite J] in
theorem he_Y3_inf_Y4 (hl : HeLat J) : hl.Y 3 ⊓ hl.Y 4 = hl.Y 2 := by
  refine le_antisymm ?_ (le_inf (Y_le hl (by norm_num) (by norm_num) (by decide))
    (Y_le hl (by norm_num) (by norm_num) (by decide)))
  have hS : hl.S ≤ hl.Y 3 ⊓ hl.Y 4 := le_inf (hl.S_le_Y 3) (hl.S_le_Y 4)
  rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
  · rw [hjeq]
    have h3 : hl.Y j ≤ hl.Y 3 := hjeq ▸ inf_le_left
    have h4 : hl.Y j ≤ hl.Y 4 := hjeq ▸ inf_le_right
    have key : ∀ j < 11, 3 ∈ heIncl[j]! → 4 ∈ heIncl[j]! → 2 ∈ heIncl[j]! := by decide
    exact (hl.le_iff hj (by norm_num)).mpr
      (key j hj ((hl.le_iff hj (by norm_num)).mp h3) ((hl.le_iff hj (by norm_num)).mp h4))
  · exfalso
    have : hl.Y 3 = ⊤ := top_le_iff.mp (htop ▸ inf_le_left)
    have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
    rw [card_top hl, card_Y3 hl] at h1
    omega

omit [Finite J] in
theorem Y0_eq_S (hl : HeLat J) : hl.Y 0 = hl.S := by
  obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hl.S_sylow
  have hle : hl.S ≤ hl.Y 0 := hl.S_le_Y 0
  have h1 : (hl.S.subgroupOf (hl.Y 0)).index * (hl.Y 0).index = hl.S.index :=
    Subgroup.relIndex_mul_index hle
  have hodd : ¬ 2 ∣ (hl.S.subgroupOf (hl.Y 0)).index := fun h =>
    hi (h1 ▸ Dvd.dvd.mul_right h _)
  have hdvd : (hl.S.subgroupOf (hl.Y 0)).index ∣ Nat.card ↥(hl.Y 0) := Subgroup.index_dvd_card _
  rw [card_Y_idx hl (by norm_num)] at hdvd
  have hcop : Nat.Coprime (hl.S.subgroupOf (hl.Y 0)).index (2 ^ 10) :=
    Nat.Coprime.pow_right 10 ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr hodd)))
  have h2 : (hl.S.subgroupOf (hl.Y 0)).index = 1 :=
    Nat.Coprime.eq_one_of_dvd hcop (by simpa [heIdx] using hdvd)
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h2) hle

theorem he_goodPair_abstract (hl : HeLat J)
    (hlev : ∃ f : ↥(hl.Y 7) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Function.Surjective f ∧ IsPGroup 2 f.ker)
    (𝒜 : Set (MulAut J)) (h𝒜 : ∀ α ∈ 𝒜, hl.S.map α.toMonoidHom = hl.S) :
    Good.GoodPair J hl.S 𝒜 := by
  have h7 : ∀ α ∈ 𝒜, (hl.Y 7).map α.toMonoidHom = hl.Y 7 := by
    intro α hα
    refine map_eq_of_unique_card (hl.S_le_Y 7) (fun Z hZ hc => ?_) α (h𝒜 α hα)
    rcases hl.complete Z hZ with ⟨j, hj, rfl⟩ | rfl
    · rw [card_Y_idx hl hj, card_Y_idx hl (by norm_num)] at hc
      have hidx : heIdx j = heIdx 7 := by omega
      have key : ∀ j < 11, heIdx j = heIdx 7 → j = 7 := by decide
      rw [key j hj hidx]
    · exfalso
      rw [card_top hl, card_Y7 hl] at hc
      omega
  have h2 : ∀ α ∈ 𝒜, (hl.Y 2).map α.toMonoidHom = hl.Y 2 := by
    intro α hα
    rw [← he_Y3_inf_Y4 hl, Subgroup.map_inf_eq _ _ _ α.injective]
    rcases aut_Y34 hl (h𝒜 α hα) with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rw [h3, h4]
    · rw [h3, h4, inf_comm]
  have hjoin : hl.Y 2 ⊔ hl.Y 7 = ⊤ := by
    have hS : hl.S ≤ hl.Y 2 ⊔ hl.Y 7 := le_sup_of_le_left (hl.S_le_Y 2)
    rcases hl.complete _ hS with ⟨j, hj, hjeq⟩ | htop
    · exfalso
      have h2j : hl.Y 2 ≤ hl.Y j := hjeq ▸ le_sup_left
      have h7j : hl.Y 7 ≤ hl.Y j := hjeq ▸ le_sup_right
      have key : ∀ j < 11, j ∈ heIncl[2]! → j ∈ heIncl[7]! → False := by decide
      exact key j hj ((hl.le_iff (by norm_num) hj).mp h2j) ((hl.le_iff (by norm_num) hj).mp h7j)
    · exact htop
  have hY2s : Group.IsSolvable ↥(hl.Y 2) :=
    A312L.isSolvable_of_card_two_three (a := 10) (b := 2) (by
      rw [card_Y_idx hl (by norm_num)]
      norm_num [heIdx])
  refine ⟨hl.Y 2, hl.Y 7, hl.S_le_Y 2, hl.S_le_Y 7, hY2s, hjoin,
    fun α hα => ⟨h2 α hα, h7 α hα⟩, ?_⟩
  by_cases hfix : ∀ α ∈ 𝒜, (hl.Y 3).map α.toMonoidHom = hl.Y 3
  ·
    left
    have h87 : hl.Y 8 ≤ hl.Y 7 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h107 : hl.Y 10 ≤ hl.Y 7 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h83 : hl.Y 8 ≤ hl.Y 3 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h104 : hl.Y 10 ≤ hl.Y 4 := Y_le hl (by norm_num) (by norm_num) (by decide)
    refine ⟨hl.Y 8, hl.Y 10, h87, h107, ?_, ?_, ?_, fun α hα => ?_⟩
    · exact A312L.isSolvable_of_card_two_three (a := 10) (b := 1) (by
        rw [card_Y_idx hl (by norm_num)]
        norm_num [heIdx])
    · exact A312L.isSolvable_of_card_two_three (a := 10) (b := 1) (by
        rw [card_Y_idx hl (by norm_num)]
        norm_num [heIdx])
    · have hS : hl.S ≤ hl.Y 8 ⊔ hl.Y 10 := le_sup_of_le_left (hl.S_le_Y 8)
      have hle : hl.Y 8 ⊔ hl.Y 10 ≤ hl.Y 7 := sup_le h87 h107
      have hne : hl.Y 8 ⊔ hl.Y 10 ≠ ⊤ := fun h => by
        have : hl.Y 7 = ⊤ := top_le_iff.mp (h ▸ hle)
        have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
        rw [card_top hl, card_Y7 hl] at h1
        omega
      obtain ⟨j, hj, hjeq⟩ := (hl.complete _ hS).resolve_right hne
      have h8j : hl.Y 8 ≤ hl.Y j := hjeq ▸ le_sup_left
      have h10j : hl.Y 10 ≤ hl.Y j := hjeq ▸ le_sup_right
      have hj7 : hl.Y j ≤ hl.Y 7 := hjeq ▸ hle
      have key : ∀ j < 11, j ∈ heIncl[8]! → j ∈ heIncl[10]! → 7 ∈ heIncl[j]! → j = 7 := by decide
      rw [hjeq, key j hj ((hl.le_iff (by norm_num) hj).mp h8j)
        ((hl.le_iff (by norm_num) hj).mp h10j) ((hl.le_iff hj (by norm_num)).mp hj7)]
    · have h4 : (hl.Y 4).map α.toMonoidHom = hl.Y 4 := by
        rcases aut_Y34 hl (h𝒜 α hα) with ⟨-, h4⟩ | ⟨h3, -⟩
        · exact h4
        · exact absurd (h3.symm.trans (hfix α hα)).symm (Y3_ne_Y4 hl)
      exact ⟨map_of_below hl (h𝒜 α hα) (a := 8) (b := 3) (c := 7) (a' := 8) (b' := 3) (c' := 7)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) h83 h87 (hfix α hα) (h7 α hα)
          (by decide),
        map_of_below hl (h𝒜 α hα) (a := 10) (b := 4) (c := 7) (a' := 10) (b' := 4) (c' := 7)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num) h104 h107 h4 (h7 α hα)
          (by decide)⟩
  ·
    right
    push Not at hfix
    obtain ⟨α₀, hα₀, hne⟩ := hfix
    obtain ⟨h3, h4⟩ : (hl.Y 3).map α₀.toMonoidHom = hl.Y 4 ∧
        (hl.Y 4).map α₀.toMonoidHom = hl.Y 3 :=
      (aut_Y34 hl (h𝒜 α₀ hα₀)).resolve_left fun h => hne h.1
    have h87 : hl.Y 8 ≤ hl.Y 7 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h107 : hl.Y 10 ≤ hl.Y 7 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h83 : hl.Y 8 ≤ hl.Y 3 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h104 : hl.Y 10 ≤ hl.Y 4 := Y_le hl (by norm_num) (by norm_num) (by decide)
    have h8 : (hl.Y 8).map α₀.toMonoidHom = hl.Y 10 :=
      map_of_below hl (h𝒜 α₀ hα₀) (a := 8) (b := 3) (c := 7) (a' := 10) (b' := 4) (c' := 7)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) h83 h87 h3 (h7 α₀ hα₀)
        (by decide)
    have h10 : (hl.Y 10).map α₀.toMonoidHom = hl.Y 8 :=
      map_of_below hl (h𝒜 α₀ hα₀) (a := 10) (b := 4) (c := 7) (a' := 8) (b' := 3) (c' := 7)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) h104 h107 h4 (h7 α₀ hα₀)
        (by decide)
    refine ⟨fun X hSX hXP hinv => ?_, hlev⟩
    have hXne : X ≠ ⊤ := fun h => by
      have : hl.Y 7 = ⊤ := top_le_iff.mp (h ▸ hXP)
      have h1 := congrArg (fun K : Subgroup J => Nat.card ↥K) this
      rw [card_top hl, card_Y7 hl] at h1
      omega
    obtain ⟨j, hj, rfl⟩ := (hl.complete X hSX).resolve_right hXne
    have h7j : 7 ∈ heIncl[j]! := (hl.le_iff hj (by norm_num)).mp hXP
    have key : ∀ j < 11, 7 ∈ heIncl[j]! → j = 0 ∨ j = 7 ∨ j = 8 ∨ j = 10 := by decide
    rcases key j hj h7j with rfl | rfl | rfl | rfl
    · exact Or.inl (Y0_eq_S hl)
    · exact Or.inr rfl
    · exfalso
      have := hinv α₀ hα₀
      rw [h8] at this
      exact Y_not_le hl (j := 10) (jj := 8) (by norm_num) (by norm_num) (by decide)
        this.le
    · exfalso
      have := hinv α₀ hα₀
      rw [h10] at this
      exact Y_not_le hl (j := 8) (jj := 10) (by norm_num) (by norm_num) (by decide)
        this.le

end Lattice

end CFSG.Quasithin.RonanE114.HeOver
