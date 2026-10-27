module

public import CFSG.Monster.Existence.TwoPoint.OrbitEquation
public import CFSG.Monster.Existence.TwoPoint.Fi23
public import CFSG.Monster.Existence.TwoPoint.Th
public import CFSG.Monster.Existence.TwoPoint.ThreeReps
public import CFSG.Monster.Existence.AssemblyHS
public import CFSG.Sporadic.HN

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section Conj

variable {G : Type} [Group G]

theorem conj_mem_inf_centralizer {x y w : G} (g : G)
    (hw : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) :
    g * w * g⁻¹ ∈ Subgroup.centralizer ({g * x * g⁻¹} : Set G) ⊓
      Subgroup.centralizer {g * y * g⁻¹} := by
  obtain ⟨hx, hy⟩ := Subgroup.mem_inf.1 hw
  rw [Subgroup.mem_centralizer_singleton_iff] at hx hy
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩ <;> rw [Subgroup.mem_centralizer_singleton_iff]
  · calc g * w * g⁻¹ * (g * x * g⁻¹) = g * (w * x) * g⁻¹ := by group
      _ = g * (x * w) * g⁻¹ := by rw [hx]
      _ = g * x * g⁻¹ * (g * w * g⁻¹) := by group
  · calc g * w * g⁻¹ * (g * y * g⁻¹) = g * (w * y) * g⁻¹ := by group
      _ = g * (y * w) * g⁻¹ := by rw [hy]
      _ = g * y * g⁻¹ * (g * w * g⁻¹) := by group

theorem oddNbr_conj {a z₀ x y : G} (g : G) (hy : y ∈ oddNbr a z₀ x) :
    g * y * g⁻¹ ∈ oddNbr a z₀ (g * x * g⁻¹) := by
  obtain ⟨hyA, hyx, hodd, w, hw, hwB⟩ := hy
  refine ⟨hyA.trans (isConj_iff.2 ⟨g, rfl⟩), fun e => hyx ?_, ?_, g * w * g⁻¹,
    conj_mem_inf_centralizer g hw, hwB.trans (isConj_iff.2 ⟨g, rfl⟩)⟩
  · calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [e]
      _ = x := by group
  · have e : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
    rw [e, ← orderOf_eq_of_isConj (isConj_iff.2 ⟨g, rfl⟩)]
    exact hodd

theorem oddNbrType_conj {z₀ x y : G} (g : G) {k : Fin 3} (h : OddNbrType z₀ x y k) :
    OddNbrType z₀ (g * x * g⁻¹) (g * y * g⁻¹) k := by
  intro w hw hwB
  have e1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  have e2 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
  have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} := by
    have := conj_mem_inf_centralizer g⁻¹ hw
    rwa [e1, e2] at this
  have hB : IsConj z₀ (g⁻¹ * w * g⁻¹⁻¹) := hwB.trans (isConj_iff.2 ⟨g⁻¹, rfl⟩)
  have := (LeechOddType.conj_iff g _ x y k).2 (h _ hw' hB)
  have e3 : g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ = w := by group
  rwa [e3] at this

end Conj

section Types

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ x y : G}

theorem oddNbrType_two_of_five
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hx : IsConj a x) (hy : y ∈ oddNbr a z₀ x) (h5 : orderOf (x * y) = 5) :
    OddNbrType z₀ x y 2 := by
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy
  obtain ⟨w, hwB, hw⟩ := oddNbr.exists_isOddPair hx hy
  have ho := (s348_card hk hw.mem_inf hwB).1
  rw [h5] at ho
  fin_cases k
  · simp [oddTypeOrder] at ho
  · simp [oddTypeOrder] at ho
  · exact hk

theorem oddNbrType_zero_of_dvd
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hx : IsConj a x) (hy : y ∈ oddNbr a z₀ x) (h3 : orderOf (x * y) = 3)
    (h2 : 2 ^ 18 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y})) :
    OddNbrType z₀ x y 0 := by
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy
  obtain ⟨w, hwB, hw⟩ := oddNbr.exists_isOddPair hx hy
  have ho := (s348_card hk hw.mem_inf hwB).1
  rw [h3] at ho
  fin_cases k
  · exact hk
  · exfalso
    have hf := s347_factorization_three_C I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hwB
      hw (hk w hw.mem_inf hwB)
    have hpos : Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) ≠ 0 :=
      Nat.card_pos.ne'
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos).1 h2
    omega
  · simp [oddTypeOrder] at ho

theorem oddNbrType_one_of_seven
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hx : IsConj a x) (hy : y ∈ oddNbr a z₀ x) (h3 : orderOf (x * y) = 3) {w e : G}
    (hw : w ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) (hwB : IsConj z₀ w)
    (he : e ∈ Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer {x} ⊓
      Subgroup.centralizer {y}) (he7 : orderOf e = 7) :
    OddNbrType z₀ x y 1 := by
  obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG hx hy
  have hc := s348_card hk hw hwB
  rw [h3] at hc
  fin_cases k
  · exfalso
    have h7 : 7 ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer {x} ⊓
        Subgroup.centralizer {y}) := by
      rw [← he7, ← Subgroup.orderOf_mk e he]
      exact orderOf_dvd_natCard _
    rw [hc.2] at h7
    norm_num [oddTypeCard] at h7
  · exact hk
  · simp [oddTypeOrder] at hc

end Types


section Base

variable {G : Type} [Group G] {a α β : G} {g : G}

theorem isConj_conj_inv (g x : G) : IsConj x (g⁻¹ * x * g) :=
  isConj_iff.2 ⟨g⁻¹, by group⟩

theorem conj_base_eq (hg : g * a * g⁻¹ = α) : g⁻¹ * α * g = a := by
  rw [← hg]
  group

theorem mul_conj_base (hg : g * a * g⁻¹ = α) :
    a * (g⁻¹ * β * g) = g⁻¹ * (α * β) * g := by
  rw [← conj_base_eq hg]
  group

theorem mem_oddNbr_base {z₀ w : G} (hg : g * a * g⁻¹ = α) (hβ : IsConj a β) (hne : β ≠ α)
    (hodd : Odd (orderOf (α * β))) (hw : w ∈ cent2 α β) (hwB : IsConj z₀ w) :
    g⁻¹ * β * g ∈ oddNbr a z₀ a := by
  have h : β ∈ oddNbr a z₀ α := ⟨hβ, hne, hodd, w, hw, hwB⟩
  have := oddNbr_conj g⁻¹ h
  rwa [inv_inv, conj_base_eq hg] at this

theorem map_conj_le_cent2 (hg : g * a * g⁻¹ = α) {K : Subgroup G} (hK : K ≤ cent2 α β) :
    K.map (MulAut.conj g⁻¹).toMonoidHom ≤ cent2 a (g⁻¹ * β * g) := by
  rintro _ ⟨k, hk, rfl⟩
  have := conj_mem_inf_centralizer g⁻¹ (hK hk)
  rw [inv_inv, conj_base_eq hg] at this
  simpa using this

theorem conj_mem_inf3 (hg : g * a * g⁻¹ = α) {w e : G}
    (he : e ∈ Subgroup.centralizer ({w} : Set G) ⊓ Subgroup.centralizer {α} ⊓
      Subgroup.centralizer {β}) :
    g⁻¹ * e * g ∈ Subgroup.centralizer ({g⁻¹ * w * g} : Set G) ⊓ Subgroup.centralizer {a} ⊓
      Subgroup.centralizer {g⁻¹ * β * g} := by
  obtain ⟨⟨hw, hα⟩, hβ⟩ := Subgroup.mem_inf.1 he |>.imp_left Subgroup.mem_inf.1
  have h1 := conj_mem_inf_centralizer g⁻¹ (Subgroup.mem_inf.2 ⟨hw, hα⟩)
  have h2 := conj_mem_inf_centralizer g⁻¹ (Subgroup.mem_inf.2 ⟨hα, hβ⟩)
  rw [inv_inv] at h1 h2
  rw [conj_base_eq hg] at h1 h2
  exact Subgroup.mem_inf.2 ⟨h1, (Subgroup.mem_inf.1 h2).2⟩

end Base

section MGriess

open CFSG.Monster.Griess

theorem oddShapes_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess)
    (hex : OddExhaustive tGriess xGriess) (hcard : Nat.card MGriess = CFSG.Open.monsterOrder)
    (hCa : Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess)) = twoBabyOrder)
    (hTh : Finite TauCeti.SporadicName.Th.Group ∧
      Nat.card TauCeti.SporadicName.Th.Group ≤ 90745943887872000)
    (hThCard : Nat.card Th = CFSG.Open.monsterThOrder)
    (hHN : ∃ α β w : MGriess, IsConj tGriess α ∧ IsConj tGriess β ∧ orderOf (α * β) = 5 ∧
      IsConj xGriess w ∧ w ∈ cent2 α β ∧ ∃ K : Subgroup MGriess, K ≤ cent2 α β ∧
        Nonempty (K ≃* HN)) :
    ∃ y : Fin 3 → MGriess,
      (∀ k, y k ∈ oddNbr tGriess xGriess tGriess ∧ OddNbrType xGriess tGriess (y k) k) ∧
      TwoPointShape (cent2 tGriess (y 0)) 3 ∧ TwoPointShape (cent2 tGriess (y 1)) 4 ∧
      TwoPointShape (cent2 tGriess (y 2)) 7 ∧
      IsConj (tGriess * y 0) threeARep ∧ IsConj (tGriess * y 1) threeCRep := by
  have hG := gmsF1Type_MGriess_uncond
  have htt : IsConj tGriess tGriess := IsConj.refl _
  obtain ⟨α₀, β₀, w₀, hα₀, hβ₀, ho₀, h3A, hw₀B, hw₀, K₀, hK₀, ⟨e₀⟩⟩ := exists_fi23_two_point
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hα₀
  have hne₀ : β₀ ≠ α₀ := fun h => by
    rw [h, mul_self_of_isConj orderOf_tGriess hα₀, orderOf_one] at ho₀
    norm_num at ho₀
  have hy₀ := mem_oddNbr_base hg₀ hβ₀ hne₀ (by rw [ho₀]; decide) hw₀ hw₀B
  have hm₀ := mul_conj_base (β := β₀) hg₀
  have hK₀' := map_conj_le_cent2 hg₀ hK₀
  have hK₀c : Nat.card ↥(K₀.map (MulAut.conj g₀⁻¹).toMonoidHom) = CFSG.Open.monsterFi23Order := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₀⁻¹).injective,
      Nat.card_congr e₀.toEquiv, CFSG.Sporadic.Fi23.card_Fi23]
    norm_num [CFSG.Open.monsterFi23Order]
  have ho₀' : orderOf (tGriess * (g₀⁻¹ * β₀ * g₀)) = 3 := by
    rw [hm₀, ← orderOf_eq_of_isConj (isConj_conj_inv g₀ _), ho₀]
  have hty₀ : OddNbrType xGriess tGriess (g₀⁻¹ * β₀ * g₀) 0 := by
    refine oddNbrType_zero_of_dvd I hG htt hy₀ ho₀' ?_
    have h1 := Subgroup.card_dvd_of_le hK₀'
    rw [hK₀c] at h1
    exact (show 2 ^ 18 ∣ CFSG.Open.monsterFi23Order from
      ⟨3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23, by norm_num [CFSG.Open.monsterFi23Order]⟩).trans h1
  obtain ⟨α₁, β₁, w₁, hα₁, hβ₁, ho₁, h3C, hw₁B, hw₁, ⟨e, he7, he⟩, K₁, hK₁, ⟨e₁⟩⟩ :=
    exists_th_two_point hTh
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hα₁
  have hne₁ : β₁ ≠ α₁ := fun h => by
    rw [h, mul_self_of_isConj orderOf_tGriess hα₁, orderOf_one] at ho₁
    norm_num at ho₁
  have hy₁ := mem_oddNbr_base hg₁ hβ₁ hne₁ (by rw [ho₁]; decide) hw₁ hw₁B
  have hm₁ := mul_conj_base (β := β₁) hg₁
  have hK₁' := map_conj_le_cent2 hg₁ hK₁
  have hK₁c : Nat.card ↥(K₁.map (MulAut.conj g₁⁻¹).toMonoidHom) = CFSG.Open.monsterThOrder := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₁⁻¹).injective,
      Nat.card_congr e₁.toEquiv, hThCard]
  have ho₁' : orderOf (tGriess * (g₁⁻¹ * β₁ * g₁)) = 3 := by
    rw [hm₁, ← orderOf_eq_of_isConj (isConj_conj_inv g₁ _), ho₁]
  have hty₁ : OddNbrType xGriess tGriess (g₁⁻¹ * β₁ * g₁) 1 := by
    have hw₁' : g₁⁻¹ * w₁ * g₁ ∈ Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
        Subgroup.centralizer {g₁⁻¹ * β₁ * g₁} := by
      have := conj_mem_inf_centralizer g₁⁻¹ hw₁
      rwa [inv_inv, conj_base_eq hg₁] at this
    have he' : e ∈ Subgroup.centralizer ({w₁} : Set MGriess) ⊓ Subgroup.centralizer {α₁} ⊓
        Subgroup.centralizer {β₁} := by
      obtain ⟨he1, he2⟩ := Subgroup.mem_inf.1 he
      obtain ⟨he3, he4⟩ := Subgroup.mem_inf.1 he1
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨he2, he3⟩, he4⟩
    refine oddNbrType_one_of_seven I hG htt hy₁ ho₁' hw₁'
      (hw₁B.trans (isConj_conj_inv g₁ w₁)) (conj_mem_inf3 hg₁ he') ?_
    rw [← orderOf_eq_of_isConj (isConj_conj_inv g₁ e), he7]
  obtain ⟨α₂, β₂, w₂, hα₂, hβ₂, ho₂, hw₂B, hw₂, K₂, hK₂, ⟨e₂⟩⟩ := hHN
  obtain ⟨g₂, hg₂⟩ := isConj_iff.1 hα₂
  have hne₂ : β₂ ≠ α₂ := fun h => by
    rw [h, mul_self_of_isConj orderOf_tGriess hα₂, orderOf_one] at ho₂
    norm_num at ho₂
  have hy₂ := mem_oddNbr_base hg₂ hβ₂ hne₂ (by rw [ho₂]; decide) hw₂ hw₂B
  have hm₂ := mul_conj_base (β := β₂) hg₂
  have hK₂' := map_conj_le_cent2 hg₂ hK₂
  have hK₂c : Nat.card ↥(K₂.map (MulAut.conj g₂⁻¹).toMonoidHom) = CFSG.Open.monsterHNOrder := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g₂⁻¹).injective,
      Nat.card_congr e₂.toEquiv, CFSG.Sporadic.HN.card_HN]
    norm_num [CFSG.Open.monsterHNOrder]
  have ho₂' : orderOf (tGriess * (g₂⁻¹ * β₂ * g₂)) = 5 := by
    rw [hm₂, ← orderOf_eq_of_isConj (isConj_conj_inv g₂ _), ho₂]
  have hty₂ := oddNbrType_two_of_five I hG htt hy₂ ho₂'
  set y : Fin 3 → MGriess := ![g₀⁻¹ * β₀ * g₀, g₁⁻¹ * β₁ * g₁, g₂⁻¹ * β₂ * g₂] with hydef
  set K : Fin 3 → Subgroup MGriess := ![K₀.map (MulAut.conj g₀⁻¹).toMonoidHom,
    K₁.map (MulAut.conj g₁⁻¹).toMonoidHom, K₂.map (MulAut.conj g₂⁻¹).toMonoidHom] with hKdef
  have hy : ∀ k, y k ∈ oddNbr tGriess xGriess tGriess ∧
      OddNbrType xGriess tGriess (y k) ((Equiv.refl (Fin 3)) k) := by
    intro k
    fin_cases k
    · exact ⟨hy₀, hty₀⟩
    · exact ⟨hy₁, hty₁⟩
    · exact ⟨hy₂, hty₂⟩
  have hK : ∀ k, K k ≤ cent2 tGriess (y k) := by
    intro k
    fin_cases k
    · exact hK₀'
    · exact hK₁'
    · exact hK₂'
  have hKc : ∀ k, Nat.card ↥(K k) = oddStabOrder k := by
    intro k
    fin_cases k
    · exact hK₀c
    · exact hK₁c
    · exact hK₂c
  have heq := odd_twoPoint_eq I hG hex hcard hCa y (Equiv.refl _) hy K hK hKc
  refine ⟨y, fun k => hy k, ?_, ?_, ?_, ?_, ?_⟩
  · have h := heq 0
    exact ⟨((MulEquiv.subgroupCongr h).symm.trans
      ((Subgroup.equivMapOfInjective K₀ _ (MulAut.conj g₀⁻¹).injective).symm.trans e₀))⟩
  · have h := heq 1
    exact ⟨((MulEquiv.subgroupCongr h).symm.trans
      ((Subgroup.equivMapOfInjective K₁ _ (MulAut.conj g₁⁻¹).injective).symm.trans e₁))⟩
  · have h := heq 2
    exact ⟨((MulEquiv.subgroupCongr h).symm.trans
      ((Subgroup.equivMapOfInjective K₂ _ (MulAut.conj g₂⁻¹).injective).symm.trans e₂))⟩
  · show IsConj (tGriess * (g₀⁻¹ * β₀ * g₀)) threeARep
    rw [hm₀]
    exact (isConj_iff.2 ⟨g₀, by group⟩).trans h3A
  · show IsConj (tGriess * (g₁⁻¹ * β₁ * g₁)) threeCRep
    rw [hm₁]
    exact (isConj_iff.2 ⟨g₁, by group⟩).trans h3C


theorem isConj_mul_of_oddNbrType
    (I : GMSInterfaces (phiB uBar) MGriess) {k : Fin 3}
    {y₀ : MGriess} (hy₀ : y₀ ∈ oddNbr tGriess xGriess tGriess)
    (hk₀ : OddNbrType xGriess tGriess y₀ k) {x y : MGriess} (hx : IsConj tGriess x)
    (hy : y ∈ oddNbr tGriess xGriess x) (hk : OddNbrType xGriess x y k) :
    IsConj (x * y) (tGriess * y₀) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 hx
  have hb := conj_base_eq hg
  have hu : g⁻¹ * y * g ∈ oddNbr tGriess xGriess tGriess := by
    have := oddNbr_conj g⁻¹ hy
    rwa [inv_inv, hb] at this
  have hku : OddNbrType xGriess tGriess (g⁻¹ * y * g) k := by
    have := oddNbrType_conj g⁻¹ hk
    rwa [inv_inv, hb] at this
  obtain ⟨c, hc, hcu⟩ := s348_orbit I.sls I.tableV I.leech I.leechOddPair I.tableIV
    gmsF1Type_MGriess_uncond (IsConj.refl _) hu hy₀ hku hk₀
  have hct : c * tGriess * c⁻¹ = tGriess := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  have e1 : x * y = g * (tGriess * (g⁻¹ * y * g)) * g⁻¹ := by
    rw [← hg]
    group
  have e2 : c * (tGriess * (g⁻¹ * y * g)) * c⁻¹ = tGriess * y₀ := by
    calc c * (tGriess * (g⁻¹ * y * g)) * c⁻¹ =
        (c * tGriess * c⁻¹) * (c * (g⁻¹ * y * g) * c⁻¹) := by group
      _ = tGriess * y₀ := by rw [hct, hcu]
  rw [e1]
  exact (isConj_iff.2 ⟨g⁻¹, by group⟩).trans (isConj_iff.2 ⟨c, e2⟩)

theorem oddTypesSeparated_MGriess
    (I : GMSInterfaces (phiB uBar) MGriess) {y₀ y₁ : MGriess}
    (hy₀ : y₀ ∈ oddNbr tGriess xGriess tGriess) (hk₀ : OddNbrType xGriess tGriess y₀ 0)
    (hy₁ : y₁ ∈ oddNbr tGriess xGriess tGriess) (hk₁ : OddNbrType xGriess tGriess y₁ 1)
    (h₀ : IsConj (tGriess * y₀) threeARep) (h₁ : IsConj (tGriess * y₁) threeCRep) :
    OddTypesSeparated tGriess xGriess := by
  intro x y y' hx hy hy' hk hk' hc
  have c₀ := (isConj_mul_of_oddNbrType I hy₀ hk₀ hx hy hk).trans h₀
  have c₁ := (isConj_mul_of_oddNbrType I hy₁ hk₁ hx hy' hk').trans h₁
  have h := trace_eq_of_isConj_MGriess ((c₀.symm.trans hc).trans c₁)
  rw [trace_threeARep, trace_threeCRep] at h
  norm_num at h

end MGriess

end CFSG.Monster.Existence
