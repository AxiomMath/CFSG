module

public import CFSG.Quasithin.Vol2.Ch11SecHSL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

theorem card_fixed_le {F : Type*} [Field F] [Finite F] (g : Matrix (Fin 3) (Fin 3) F)
    (hg : ∃ x, g.mulVec x ≠ x) : Nat.card {x : Fin 3 → F // g.mulVec x = x} ≤ Nat.card F ^ 2 := by
  classical
  have := Fintype.ofFinite F
  let S : Submodule F (Fin 3 → F) := LinearMap.ker (Matrix.toLin' g - LinearMap.id)
  have hmem : ∀ x, x ∈ S ↔ g.mulVec x = x := fun x => by
    simp [S, sub_eq_zero]
  have hS : S ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hg
    exact hx ((hmem x).mp (h ▸ Submodule.mem_top))
  have hr : Module.finrank F S ≤ 2 := by
    have := Submodule.finrank_lt hS
    simp only [Module.finrank_fin_fun] at this
    omega
  have hcard : Nat.card {x : Fin 3 → F // g.mulVec x = x} = Nat.card S :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => (hmem x).symm)
  rw [hcard, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
    ← Nat.card_eq_fintype_card]
  exact Nat.pow_le_pow_right Nat.card_pos hr

theorem zpow_apply_eq_of_apply_eq' {X : Type*} [Group X] {b : MulAut X} {v : X} (h : b v = v)
    (k : ℤ) : (b ^ k) v = v := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih => rw [zpow_add_one, MulAut.mul_apply, h, ih]
  | pred n ih =>
    have h' : b.symm v = v := (MulEquiv.symm_apply_eq b).mpr h.symm
    rw [zpow_sub_one, MulAut.mul_apply, MulAut.inv_apply, h', ih]

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem card_B_sl3 [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    Nat.card (bOf T I H) = (2 ^ n) ^ 2 := by
  have h3 := card_of_realizesVia hπ
  rw [d.card_fsuV, hF, Fintype.card_fin] at h3
  have h5 : 2 ^ n * Nat.card (bOf T I H) = 2 ^ n * (2 ^ n) ^ 2 := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h5

theorem B_ne_bot_sl3 [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π) :
    bOf T I H ≠ ⊥ := by
  intro hb
  have := d.card_B_sl3 hF hπ
  rw [hb, Subgroup.card_bot] at this
  have hn := d.c.two_le
  have h1 : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow (by omega))
  omega

theorem mem_B_of_fix (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π)
    {b' : G} (hb' : b' ∈ conjSubgroup (bOf T I H) h) (hb'1 : b' ≠ 1) {v : G}
    (hv : v ∈ fsuV T I) (hfix : b' * v * b'⁻¹ = v) : v ∈ bOf T I H := by
  obtain ⟨φ, -, hφbij, hφeq⟩ := exists_coords hπ
  have hb'N := d.Bh_le_normalizer_V i hb'
  have hσL := d.conjAct_P_mem i hF π hπ (Subgroup.mem_sup_right hb') hb'N
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL 3 F), π γ = ⟨_, hσL⟩ := hπ.1 ⟨_, hσL⟩
  have hγσ : ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) =
      conjAct (fsuV T I) ⟨b', hb'N⟩ := congrArg Subtype.val hγ
  have hfixiff : ∀ w : ↥(fsuV T I), conjAct (fsuV T I) ⟨b', hb'N⟩ w = w ↔
      ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (φ w) = φ w := by
    intro w
    rw [← hφeq γ w, hγσ]
    exact ⟨fun h1 => by rw [h1], fun h1 => hφbij.1 h1⟩
  have hmove : ∃ x, ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x ≠ x := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hb'1
    have hσ1 : conjAct (fsuV T I) ⟨b', hb'N⟩ = 1 := by
      ext w
      rw [MulAut.one_apply]
      exact congrArg Subtype.val ((hfixiff w).mpr (hall _))
    have : b' ∈ conjSubgroup (bOf T I H) h ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
      ⟨hb', (conjAct_eq_one_iff _ _).mp hσ1⟩
    rw [d.Bh_inf_centralizer_V i, Subgroup.mem_bot] at this
    exact this
  have hle := card_fixed_le _ hmove
  have hσB : conjAct (fsuV T I) ⟨b', hb'N⟩ ∈ autOn (conjSubgroup (bOf T I H) h) (fsuV T I) :=
    ⟨⟨b', hb'N⟩, Subgroup.mem_subgroupOf.mpr hb', rfl⟩
  have hzp : ∀ w : ↥(fsuV T I), w ∈ fixV (Subgroup.zpowers (conjAct (fsuV T I) ⟨b', hb'N⟩)) ↔
      conjAct (fsuV T I) ⟨b', hb'N⟩ w = w := fun w =>
    ⟨fun h1 => h1 _ (Subgroup.mem_zpowers _), fun h1 x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact zpow_apply_eq_of_apply_eq' h1 k⟩
  have hBFx : (bOf T I H).subgroupOf (fsuV T I) ≤
      fixV (Subgroup.zpowers (conjAct (fsuV T I) ⟨b', hb'N⟩)) := fun w hw =>
    (hzp w).mpr (d.autOn_Bh_fix i _ hσB w hw)
  have hcardFx : Nat.card (fixV (Subgroup.zpowers (conjAct (fsuV T I) ⟨b', hb'N⟩))) ≤
      (2 ^ n) ^ 2 := by
    rw [← hF]
    calc Nat.card (fixV (Subgroup.zpowers (conjAct (fsuV T I) ⟨b', hb'N⟩))) =
          Nat.card {w : ↥(fsuV T I) // conjAct (fsuV T I) ⟨b', hb'N⟩ w = w} :=
          Nat.card_congr (Equiv.subtypeEquivRight hzp)
      _ = Nat.card {x : Fin 3 → F //
          ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x} := by
          refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨φ w.1, (hfixiff w.1).mp w.2⟩)
            ⟨fun w₁ w₂ hw => Subtype.ext (hφbij.1 (congrArg Subtype.val hw)), fun x => ?_⟩)
          obtain ⟨w, hw⟩ := hφbij.2 x.1
          exact ⟨⟨w, (hfixiff w).mpr (hw ▸ x.2)⟩, Subtype.ext hw⟩
      _ ≤ Nat.card F ^ 2 := hle
  have heq : (bOf T I H).subgroupOf (fsuV T I) =
      fixV (Subgroup.zpowers (conjAct (fsuV T I) ⟨b', hb'N⟩)) :=
    Subgroup.eq_of_le_of_card_ge hBFx (by rw [card_B_subgroupOf, d.card_B_sl3 hF hπ]; exact hcardFx)
  have hvFx : (⟨v, hv⟩ : ↥(fsuV T I)) ∈
      fixV (Subgroup.zpowers (conjAct (fsuV T I) ⟨b', hb'N⟩)) := by
    rw [hzp]
    apply Subtype.ext
    rw [conjAct_apply_coe]
    exact hfix
  rw [← heq] at hvFx
  exact Subgroup.mem_subgroupOf.mp hvFx

theorem mem_B_of_comm (i : Inp32) [IsMulCommutative ↥(fsuV T I)] {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ n) {π : ↥(StatedSL 3 F) →* ↥(autOn L (fsuV T I))}
    (hπ : (FFModel.nat (StatedSL 3 F)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ π)
    {v : G} (hv : v ∈ fsuV T I) (hvB : v ∉ bOf T I H) {p : G} (hp : p ∈ pOf T I H h)
    (hcomm : v * p = p * v) : p ∈ bOf T I H := by
  obtain ⟨b, hb, b', hb', rfl⟩ := (d.mem_P_iff i).mp hp
  have hvb : v * b = b * v := comm_of_isElemAbelian (SecA.isElemAbelian_fsuV d.c.s.hyp) hv
    ((inf_le_left : bOf T I H ≤ fsuV T I) hb)
  have hvb' : v * b' = b' * v := by
    have : b * (v * b') = b * (b' * v) := by
      calc b * (v * b') = (b * v) * b' := by group
        _ = (v * b) * b' := by rw [hvb]
        _ = v * (b * b') := by group
        _ = (b * b') * v := hcomm
        _ = b * (b' * v) := by group
    exact mul_left_cancel this
  by_cases hb'1 : b' = 1
  · rw [hb'1, mul_one]
    exact hb
  · exfalso
    apply hvB
    exact d.mem_B_of_fix i hF hπ hb' hb'1 hv (by rw [← hvb', mul_inv_cancel_right])

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
