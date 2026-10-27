module

public import CFSG.GroupTheory.SolvableHallNodes
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

theorem commute_of_conj_comm [Finite G] {N : Subgroup G} {y d : G}
    (hyN : y ∈ Subgroup.normalizer (N : Set G)) (hd : d ∈ N) {r : ℕ} (hr : r.Prime)
    (hyr : y ^ r = 1) (hrN : ¬ r ∣ Nat.card N)
    (hc : y * (y * d * y⁻¹ * d⁻¹) = (y * d * y⁻¹ * d⁻¹) * y) : y * d = d * y := by
  set c := y * d * y⁻¹ * d⁻¹ with hcdef
  have hcN : c ∈ N := N.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN d).mp hd) (N.inv_mem hd)
  have hyc : y * c * y⁻¹ = c := by rw [hc, mul_inv_cancel_right]
  have hyck : ∀ k : ℕ, y * c ^ k * y⁻¹ = c ^ k := fun k => by rw [← conj_pow, hyc]
  have hpow : ∀ k : ℕ, y ^ k * d * (y ^ k)⁻¹ = c ^ k * d := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc y ^ (k + 1) * d * (y ^ (k + 1))⁻¹ = y * (y ^ k * d * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = (y * c ^ k * y⁻¹) * (y * d * y⁻¹) := by rw [ih]; group
        _ = c ^ (k + 1) * d := by rw [hyck k, pow_succ, mul_assoc, hcdef]; group
  have h1 := hpow r
  rw [hyr, one_mul, inv_one, mul_one] at h1
  have hcr : c ^ r = 1 := by
    have h2 := congrArg (· * d⁻¹) h1
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
    exact h2.symm
  rcases (Nat.dvd_prime hr).mp (orderOf_dvd_of_pow_eq_one hcr) with h | h
  · rw [orderOf_eq_one_iff] at h
    calc y * d = c * (d * y) := by rw [hcdef]; group
      _ = d * y := by rw [h, one_mul]
  · exact absurd (h ▸ Subgroup.orderOf_dvd_natCard N hcN) hrN

theorem le_normalizer_of_hall [Finite G] {B R D : Subgroup G} (hBR : B ≤ R) {k : ℕ}
    (hk : B.relIndex R = 2 ^ k) (hB : Odd (Nat.card B)) (hD : Odd (Nat.card D))
    (hBD : B ≤ Subgroup.normalizer (D : Set G)) (hDR : D ≤ Subgroup.normalizer (R : Set G)) :
    D ≤ Subgroup.normalizer (B : Set G) := by
  have hS : Odd (Nat.card ↥(B ⊔ D)) :=
    (hB.mul hD).of_dvd_nat (Dvd.intro _ (C5.card_sup_mul_card_inf_of_le_normalizer hBD))
  have hle : B ≤ (B ⊔ D) ⊓ R := le_inf le_sup_left hBR
  have h1 : B.relIndex ((B ⊔ D) ⊓ R) ∣ 2 ^ k := by
    rw [← hk, ← Subgroup.relIndex_mul_relIndex B _ R hle inf_le_right]
    exact Dvd.intro _ rfl
  have h2 : Odd (B.relIndex ((B ⊔ D) ⊓ R)) := by
    refine hS.of_dvd_nat ((Dvd.intro_left _ (C5.card_eq_card_mul_relIndex hle).symm).trans ?_)
    exact Subgroup.card_dvd_of_le inf_le_left
  have h3 : B.relIndex ((B ⊔ D) ⊓ R) = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h2).pow_right k) h1
  have hSR : (B ⊔ D) ⊓ R = B := le_antisymm (Subgroup.relIndex_eq_one.mp h3) hle
  intro d hd
  rw [← hSR]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer (Subgroup.mem_sup_right hd), hDR hd⟩

theorem inf_eq_bot_of_odd [Finite G] {P B : Subgroup G} (hP : IsPGroup 2 P)
    (hB : Odd (Nat.card B)) : P ⊓ B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP
  have h1 : Nat.card ↥(P ⊓ B) ∣ 2 ^ j := hj ▸ Subgroup.card_dvd_of_le inf_le_left
  have h2 : Odd (Nat.card ↥(P ⊓ B)) := hB.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  exact Subgroup.eq_bot_of_card_eq _
    (Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr h2).pow_right j) h1)

theorem exists_complement_of_odd [Finite G] {P Y : Subgroup G} (hPY : P ≤ Y)
    (hYP : Y ≤ Subgroup.normalizer (P : Set G)) (hP : IsPGroup 2 P)
    (hodd : Odd (P.relIndex Y)) : ∃ E : Subgroup G, E ≤ Y ∧ P ⊔ E = Y ∧ P ⊓ E = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPY).mpr hYP
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP
  have hNcard : Nat.card (P.subgroupOf Y) = 2 ^ j := by
    rw [← hj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPY).toEquiv
  obtain ⟨E', hE'⟩ := Subgroup.exists_right_complement'_of_coprime (N := P.subgroupOf Y)
    (by rw [hNcard]; exact (Nat.coprime_two_left.mpr hodd).pow_left j)
  refine ⟨E'.map Y.subtype, Subgroup.map_subtype_le E', ?_, ?_⟩
  · have h := congrArg (Subgroup.map Y.subtype) hE'.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPY, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  · have h := congrArg (Subgroup.map Y.subtype) (disjoint_iff.mp hE'.disjoint)
    rwa [Subgroup.map_inf_eq _ _ _ Y.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hPY,
      Subgroup.map_bot] at h

theorem exists_conj_of_complement [Finite G] {P H K : Subgroup G} (hP : IsPGroup 2 P)
    (hH : Odd (Nat.card H)) (hHP : H ≤ Subgroup.normalizer (P : Set G))
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hPH : P ⊓ H = ⊥) (hPK : P ⊓ K = ⊥)
    (hsup : P ⊔ H = P ⊔ K) : ∃ n ∈ P, K = H.map (MulAut.conj n⁻¹).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := P ⊔ H with hC
  have hCP : C ≤ Subgroup.normalizer (P : Set G) := sup_le Subgroup.le_normalizer hHP
  have hPC : P ≤ C := le_sup_left
  have hHC : H ≤ C := le_sup_right
  have hKC : K ≤ C := hsup ▸ le_sup_right
  have hN : (P.subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPC).mpr hCP
  have hNs : Group.IsSolvable (P.subgroupOf C) := by
    have h2 : IsPGroup 2 (P.subgroupOf C) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
    have := h2.isNilpotent
    infer_instance
  have hidx : (P.subgroupOf C).index = Nat.card H := by
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hHP
    rw [inf_comm, hPH, Subgroup.card_bot, mul_one, sup_comm, ← hC,
      C5.card_eq_card_mul_relIndex hPC, mul_comm (Nat.card H)] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP
  have hcop : Nat.Coprime (Nat.card (P.subgroupOf C)) (P.subgroupOf C).index := by
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv, hj]
    exact (Nat.coprime_two_left.mpr hH).pow_left j
  have hmul : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (P : Set G) → P ⊔ X = C →
      ((P.subgroupOf C : Set ↥C) * (X.subgroupOf C : Set ↥C)) = Set.univ := by
    intro X hXP hXC
    ext x
    simp only [Set.mem_univ, iff_true]
    have hx : (x : G) ∈ ((P ⊔ X : Subgroup G) : Set G) := by rw [hXC]; exact x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P X hXP] at hx
    obtain ⟨p, hp, y, hy, hpy⟩ := Set.mem_mul.mp hx
    exact Set.mem_mul.mpr ⟨⟨p, hPC hp⟩, hp, ⟨y, hXC ▸ (le_sup_right : X ≤ P ⊔ X) hy⟩, hy,
      Subtype.ext hpy⟩
  have hbot : ∀ X : Subgroup G, P ⊓ X = ⊥ → P.subgroupOf C ⊓ X.subgroupOf C = ⊥ := by
    intro X hX
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : G) ∈ P ⊓ X := ⟨hx.1, hx.2⟩
    rw [hX, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  obtain ⟨n, hn, hK⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy
    (P.subgroupOf C) hNs hcop (hmul H hHP rfl) (hmul K hKP hsup.symm) (hbot H hPH)
    (hbot K hPK)
  refine ⟨(n : G), hn, ?_⟩
  ext x
  constructor
  · intro hx
    have h1 : (⟨x, hKC hx⟩ : ↥C) ∈ K.subgroupOf C := hx
    rw [hK] at h1
    obtain ⟨h, hh, hhx⟩ := h1
    refine ⟨(h : G), hh, ?_⟩
    have h2 := congrArg Subtype.val hhx
    simpa [MulAut.conj_apply] using h2
  · rintro ⟨h, hh, rfl⟩
    have hh' : (⟨h, hHC hh⟩ : ↥C) ∈ H.subgroupOf C := hh
    have h1 : (MulAut.conj n⁻¹).toMonoidHom ⟨h, hHC hh⟩ ∈ K.subgroupOf C := by
      rw [hK]
      exact ⟨_, hh', rfl⟩
    simpa [Subgroup.mem_subgroupOf, MulAut.conj_apply] using h1

theorem exists_hall_le_normalizer [Finite G] {B₀ P B : Subgroup G} (hPB₀ : P ≤ B₀)
    (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.relIndex B₀)
    (hPn : B₀ ≤ Subgroup.normalizer (P : Set G)) (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hBB : B ≤ Subgroup.normalizer (B₀ : Set G)) (hB : Odd (Nat.card B)) :
    ∃ D : Subgroup G, Lin2.IsHallTwoPrimeOf D B₀ ∧ ∃ n ∈ P,
      B.map (MulAut.conj n⁻¹).toMonoidHom ≤ Subgroup.normalizer (D : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := B ⊔ B₀ with hY
  have hPY : P ≤ Y := hPB₀.trans le_sup_right
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := sup_le hBP hPn
  have hodd0 : Odd (P.relIndex B₀) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hPi)
  have hYodd : Odd (P.relIndex Y) := by
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hBB
    rw [← hY, C5.card_eq_card_mul_relIndex hPY, C5.card_eq_card_mul_relIndex hPB₀] at h1
    have h2 : P.relIndex Y * Nat.card ↥(B ⊓ B₀) = Nat.card B * P.relIndex B₀ := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥P))
      calc Nat.card ↥P * (P.relIndex Y * Nat.card ↥(B ⊓ B₀))
          = Nat.card ↥P * P.relIndex Y * Nat.card ↥(B ⊓ B₀) := by ring
        _ = Nat.card ↥B * (Nat.card ↥P * P.relIndex B₀) := h1
        _ = Nat.card ↥P * (Nat.card ↥B * P.relIndex B₀) := by ring
    exact (hB.mul hodd0).of_dvd_nat (Dvd.intro _ h2)
  obtain ⟨E, hEY, hPE, hPE'⟩ := exists_complement_of_odd hPY hYP hP hYodd
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := hEY.trans hYP
  have hEodd : Odd (Nat.card E) := by
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hEP
    rw [inf_comm, hPE', Subgroup.card_bot, mul_one, sup_comm, hPE,
      C5.card_eq_card_mul_relIndex hPY, mul_comm (Nat.card E)] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1 ▸ hYodd
  set C := P ⊔ B with hC
  have hCY : C ≤ Y := sup_le hPY le_sup_left
  have hCB : C ≤ Subgroup.normalizer (B₀ : Set G) :=
    sup_le (hPB₀.trans Subgroup.le_normalizer) hBB
  have hsup : P ⊔ B = P ⊔ (E ⊓ C) := by
    refine le_antisymm (fun x hx => ?_) (sup_le le_sup_left inf_le_right)
    have hxY : x ∈ ((P ⊔ E : Subgroup G) : Set G) := by rw [hPE]; exact hCY hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P E hEP] at hxY
    obtain ⟨p, hp, e, he, rfl⟩ := Set.mem_mul.mp hxY
    have heC : e ∈ C := by
      have h1 := C.mul_mem (C.inv_mem ((le_sup_left : P ≤ C) hp)) hx
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ⟨he, heC⟩)
  have hPEC : P ⊓ (E ⊓ C) = ⊥ :=
    le_bot_iff.mp (hPE' ▸ (inf_le_inf_left P inf_le_left : P ⊓ (E ⊓ C) ≤ P ⊓ E))
  obtain ⟨n, hn, hn'⟩ := exists_conj_of_complement hP hB hBP (inf_le_left.trans hEP)
    (inf_eq_bot_of_odd hP hB) hPEC hsup
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hP
  refine ⟨E ⊓ B₀, ⟨inf_le_right, hEodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left), j,
    ?_⟩, n, hn, ?_⟩
  · have hB₀eq : (E ⊓ B₀) ⊔ P = B₀ := by
      refine le_antisymm (sup_le inf_le_right hPB₀) (fun b hb => ?_)
      have hbY : b ∈ ((P ⊔ E : Subgroup G) : Set G) := by
        rw [hPE]
        exact (le_sup_right : B₀ ≤ Y) hb
      rw [Subgroup.coe_mul_of_right_le_normalizer_left P E hEP] at hbY
      obtain ⟨p, hp, e, he, rfl⟩ := Set.mem_mul.mp hbY
      have heB : e ∈ B₀ := by
        have h1 := B₀.mul_mem (B₀.inv_mem (hPB₀ hp)) hb
        rwa [inv_mul_cancel_left] at h1
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hp) (Subgroup.mem_sup_left ⟨he, heB⟩)
    have hD0 : (E ⊓ B₀) ⊓ P = ⊥ :=
      le_bot_iff.mp (hPE' ▸ (fun x hx => ⟨hx.2, hx.1.1⟩ : (E ⊓ B₀) ⊓ P ≤ P ⊓ E))
    have h1 := C5.card_sup_mul_card_inf_of_le_normalizer
      ((inf_le_left : E ⊓ B₀ ≤ E).trans hEP)
    rw [hB₀eq, hD0, Subgroup.card_bot, mul_one,
      C5.card_eq_card_mul_relIndex (inf_le_right : E ⊓ B₀ ≤ B₀), hj] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  · rw [← hn']
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx.1, hCB hx.2⟩

theorem isHallTwoPrimeOf_map_conj [Finite G] {D X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hD : Lin2.IsHallTwoPrimeOf D X) :
    Lin2.IsHallTwoPrimeOf (D.map (MulAut.conj g).toMonoidHom) X := by
  obtain ⟨hDX, hDo, k, hk⟩ := hD
  have hcard : Nat.card ↥(D.map (MulAut.conj g).toMonoidHom) = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle : D.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨d, hd, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg d).mp (hDX hd)
  refine ⟨hle, hcard ▸ hDo, k, ?_⟩
  have h1 := C5.card_eq_card_mul_relIndex hle
  have h2 := C5.card_eq_card_mul_relIndex hDX
  rw [hcard] at h1
  rw [← hk]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.symm.trans h2)

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
