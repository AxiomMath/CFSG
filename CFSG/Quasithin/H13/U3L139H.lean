module

public import CFSG.Quasithin.H13.U3L13x8
public import CFSG.Quasithin.H13.U3G2Blk
public import CFSG.Quasithin.H13.U3L15A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

theorem oTwoRes_le_of_le_sup [Finite G] {X C Q : Subgroup G} (hX : X ≤ C ⊔ Q)
    (hQ : IsPGroup 2 Q) (hQC : Q ≤ normalizer (C : Set G)) : oTwoRes X ≤ C := by
  rw [oTwoRes_eq_oTwoUpper]
  exact (oTwoUpper_mono hX).trans (oTwoUpper_le_of_sup hQ hQC)

theorem oTwoRes_le_oTwoRes (X : Subgroup G) : oTwoRes X ≤ oTwoRes (oTwoRes X) :=
  (closure_le _).2 fun _ hy => subset_closure ⟨subset_closure hy, hy.2⟩

theorem le_normalizer_orderThreeSubgroup (Y : Subgroup G) :
    normalizer (Y : Set G) ≤ normalizer (orderThreeSubgroup Y : Set G) := by
  have key : ∀ g ∈ normalizer (Y : Set G), ∀ x ∈ orderThreeSubgroup Y,
      g * x * g⁻¹ ∈ orderThreeSubgroup Y := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      refine subset_closure ⟨(mem_normalizer_iff.1 hg y).1 hy.1, ?_⟩
      have := MulEquiv.orderOf_eq (MulAut.conj g) y
      rw [MulAut.conj_apply] at this
      rw [this]
      exact hy.2
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem mem_orderThreeSubgroup {Y : Subgroup G} {x : G} (hx : x ∈ Y) (h3 : orderOf x = 3) :
    x ∈ orderThreeSubgroup Y :=
  subset_closure ⟨hx, h3⟩

theorem orderThreeSubgroup_le (Y : Subgroup G) : orderThreeSubgroup Y ≤ Y :=
  (closure_le _).2 fun _ hx => hx.1

theorem orderThreeSubgroup_le_oTwoRes (Y : Subgroup G) :
    orderThreeSubgroup Y ≤ oTwoRes (orderThreeSubgroup Y) :=
  (closure_le _).2 fun x hx => subset_closure ⟨subset_closure hx, 3, by decide, by
    rw [← hx.2, pow_orderOf_eq_one]⟩

theorem isPGroup_two_of_no_three [Finite G] {Y : Subgroup G} (h23 : IsTwoThreeGroup Y)
    (h3 : ∀ x ∈ Y, orderOf x ≠ 3) : IsPGroup 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {p} hp hpd => ?_⟩
  rcases h23 p hp hpd with rfl | rfl
  · rfl
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 hpd
    exact h3 y y.2 (by rw [Subgroup.orderOf_coe]; exact hy)

theorem o2Z_le_pCoreOf_of_a6 {L : Subgroup G}
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) : o2Z L ≤ pCoreOf 2 L := by
  obtain ⟨e6⟩ := he
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsQ : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e6).2 hs
  have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := alt6_nonabelian
    exact ⟨e6.symm a, e6.symm b, fun h => hab (by simpa using congrArg e6 h)⟩
  have hcen : center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
    rcases (inferInstance : (center (↥L ⧸ CFSG.pCore 2 ↥L)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      exact hab (mem_center_iff.1 (h ▸ mem_top b) a)
  rintro _ ⟨y, hy, rfl⟩
  have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) y ∈ center (↥L ⧸ CFSG.pCore 2 ↥L) := hy
  rw [hcen, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  exact coe_mem_pCoreOf_iff.2 this

theorem l0_le_of_mem [Finite G] {L W : Subgroup G} (hhat : IsHatA6 L)
    (hW : pCoreOf 2 (l0 L) ≤ normalizer (W : Set G)) {x : G} (hxW : x ∈ W) (hxL0 : x ∈ l0 L)
    (hx3 : orderOf x = 3) : l0 L ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcL0, hc3, hcO, hdec⟩ := l0_decomp hhat
  set O := pCoreOf 2 (l0 L) with hO
  have hO2 : IsPGroup 2 O := LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hxO : x ∉ O := fun h => by
    obtain ⟨k, hk⟩ := hO2 ⟨x, h⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hx3] at h2
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  have hcW : c ∈ W ⊔ O := by
    rcases hdec x hxL0 with h | h | h
    · exact absurd h hxO
    ·
      have e : c = x * (c * c * x)⁻¹ := by
        have h3 : c * c * c = 1 := by rw [← pow_three', hc3]
        calc c = (c * c * c)⁻¹ * c := by rw [h3, inv_one, one_mul]
          _ = x * (c * c * x)⁻¹ := by group
      rw [e]
      exact mul_mem (mem_sup_left hxW) (inv_mem (mem_sup_right h))
    · have e : c = (c * x) * x⁻¹ * (x * x * x) := by
        have h3 : x * x * x = 1 := by rw [← pow_three', ← hx3, pow_orderOf_eq_one]
        rw [h3]
        group
      rw [e]
      have h3 : x * x * x = 1 := by rw [← pow_three', ← hx3, pow_orderOf_eq_one]
      rw [h3, mul_one]
      exact mul_mem (mem_sup_right h) (inv_mem (mem_sup_left hxW))
  have hL0 : l0 L ≤ W ⊔ O := by
    intro y hy
    rcases hdec y hy with h | h | h
    · exact mem_sup_right h
    · have e : y = (c * c)⁻¹ * (c * c * y) := by group
      rw [e]
      exact mul_mem (inv_mem (mul_mem hcW hcW)) (mem_sup_right h)
    · have e : y = c⁻¹ * (c * y) := by group
      rw [e]
      exact mul_mem (inv_mem hcW) (mem_sup_right h)
  calc l0 L ≤ oTwoRes (l0 L) := oTwoRes_le_oTwoRes _
    _ ≤ W := oTwoRes_le_of_le_sup hL0 hO2 hW

theorem normalizer_l0_le [Finite G] {T L : Subgroup G} (hhat : IsHatA6 L) (hL : CharTwo L)
    (hTL : T ≤ normalizer (L : Set G)) (hU : IsUniqueM (L ⊔ T) (normalizer (L : Set G))) :
    normalizer (l0 L : Set G) ≤ normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : pCoreOf 2 (l0 L) ≠ ⊥ := by
    obtain ⟨c, hc, -, hcO, -⟩ := exists_l0_c hhat.2.1
    intro h
    apply hcO
    have hcL : c ∈ L := l0_le_L hc
    refine hL (mem_inf.2 ⟨hcL, mem_centralizer_iff.2 fun x hx => ?_⟩)
    have hxL : x ∈ L := LieType.BorelTits.pCoreOf_le 2 L hx
    have hk0 : x * c * x⁻¹ * c⁻¹ ∈ l0 L :=
      (l0 L).mul_mem ((mem_normalizer_iff.mp (L_le_normalizer_l0 hxL) c).mp hc)
        ((l0 L).inv_mem hc)
    have hk2 : x * c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 L := by
      have h1 : c * x⁻¹ * c⁻¹ ∈ pCoreOf 2 L :=
        (mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 L hcL) _).mp
          ((pCoreOf 2 L).inv_mem hx)
      have := (pCoreOf 2 L).mul_mem hx h1
      simpa [mul_assoc] using this
    have hk := mem_pCoreOf_l0 hk0 hk2
    rw [h, mem_bot] at hk
    calc x * c = x * c * x⁻¹ * c⁻¹ * (c * x) := by group
      _ = c * x := by rw [hk, one_mul]
  have hN : normalizer (l0 L : Set G) ≤ normalizer (pCoreOf 2 (l0 L) : Set G) :=
    LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
  have hLT : L ⊔ T ≤ normalizer (l0 L : Set G) :=
    sup_le L_le_normalizer_l0
      (A5.le_normalizer_oTwoRes_of_le_normalizer (hTL.trans normalizer_L_le_o2Z))
  exact hN.trans (normalizer_le_of_isUniqueM hU (LieType.BorelTits.pCoreOf_isPGroup 2 _) hne
    (hLT.trans hN))

theorem autOn_le_of_forall {X Y V : Subgroup G}
    (h : ∀ x ∈ X, x ∈ normalizer (V : Set G) →
      ∃ y ∈ Y, y ∈ normalizer (V : Set G) ∧ y⁻¹ * x ∈ centralizer (V : Set G)) :
    autOn X V ≤ autOn Y V := by
  rintro φ ⟨⟨x, hxN⟩, hxX, rfl⟩
  obtain ⟨y, hyY, hyN, hyx⟩ := h x (mem_subgroupOf.1 hxX) hxN
  refine ⟨⟨y, hyN⟩, mem_subgroupOf.2 hyY, ?_⟩
  have h1 : conjAct V (⟨y, hyN⟩⁻¹ * ⟨x, hxN⟩ : ↥(normalizer (V : Set G))) = 1 :=
    A1b.conjAct_eq_one_iff.2 hyx
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1

end CFSG.Quasithin.H13.U3
