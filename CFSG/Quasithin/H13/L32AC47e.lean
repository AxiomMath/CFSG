module

public import CFSG.Quasithin.H13.L32AC47d
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt6

open Equiv Equiv.Perm

abbrev A6 : Type := alternatingGroup (Fin 6)

abbrev toA6 (σ : Perm (Fin 6)) (h : sign σ = 1) : A6 := ⟨σ, mem_alternatingGroup.mpr h⟩

@[expose] def listSubgroup (l : List (Perm (Fin 6))) (h1 : (1 : Perm (Fin 6)) ∈ l)
    (hmul : ∀ g ∈ l, ∀ h ∈ l, g * h ∈ l) (hinv : ∀ g ∈ l, g⁻¹ ∈ l) : Subgroup A6 where
  carrier := {g | (g : Perm (Fin 6)) ∈ l}
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun ha => hinv _ ha

@[expose] def D0 : Subgroup A6 := listSubgroup d0List one_mem_lists.1 d0_mul d0_inv

@[expose] def E1 : Subgroup A6 := listSubgroup e1List one_mem_lists.2.1 e1_mul e1_inv

@[expose] def E2 : Subgroup A6 := listSubgroup e2List one_mem_lists.2.2 e2_mul e2_inv

@[expose] def N1 : Subgroup A6 := Subgroup.normalizer (E1 : Set A6)

@[expose] def N2 : Subgroup A6 := Subgroup.normalizer (E2 : Set A6)

theorem mem_D0 {g : A6} : g ∈ D0 ↔ (g : Perm (Fin 6)) ∈ d0List := Iff.rfl

theorem mem_E1 {g : A6} : g ∈ E1 ↔ (g : Perm (Fin 6)) ∈ e1List := Iff.rfl

theorem mem_E2 {g : A6} : g ∈ E2 ↔ (g : Perm (Fin 6)) ∈ e2List := Iff.rfl

theorem mem_N1_of {g : A6}
    (h : ∀ e ∈ e1List, (g : Perm (Fin 6)) * e * (g : Perm (Fin 6))⁻¹ ∈ e1List) : g ∈ N1 :=
  Subgroup.mem_normalizer_fintype fun _ hn => h _ hn

theorem mem_N2_of {g : A6}
    (h : ∀ e ∈ e2List, (g : Perm (Fin 6)) * e * (g : Perm (Fin 6))⁻¹ ∈ e2List) : g ∈ N2 :=
  Subgroup.mem_normalizer_fintype fun _ hn => h _ hn

theorem card_listSubgroup (l : List (Perm (Fin 6))) (h1 : (1 : Perm (Fin 6)) ∈ l)
    (hmul : ∀ g ∈ l, ∀ h ∈ l, g * h ∈ l) (hinv : ∀ g ∈ l, g⁻¹ ∈ l) (hs : ∀ g ∈ l, sign g = 1)
    (hl : l.Nodup) : Nat.card (listSubgroup l h1 hmul hinv) = l.length := by
  have e : ↥(listSubgroup l h1 hmul hinv) ≃ {σ : Perm (Fin 6) // σ ∈ l.toFinset} :=
    { toFun := fun g => ⟨(g : A6), List.mem_toFinset.mpr g.2⟩
      invFun := fun σ => ⟨⟨σ.1, mem_alternatingGroup.mpr (hs _ (List.mem_toFinset.mp σ.2))⟩,
        List.mem_toFinset.mp σ.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup hl]

theorem card_D0 : Nat.card D0 = 8 :=
  card_listSubgroup _ _ _ _ d0_sign d0_nodup

theorem card_E1 : Nat.card E1 = 4 :=
  card_listSubgroup _ _ _ _ (fun _ hg => d0_sign _ (e1_sub _ hg)) e_nodup.1

theorem card_E2 : Nat.card E2 = 4 :=
  card_listSubgroup _ _ _ _ (fun _ hg => d0_sign _ (e2_sub _ hg)) e_nodup.2

theorem mem_N1_iff {g : A6} :
    g ∈ N1 ↔ ∀ e ∈ e1List, (g : Perm (Fin 6)) * e * (g : Perm (Fin 6))⁻¹ ∈ e1List :=
  ⟨fun hg e he => (Subgroup.mem_normalizer_iff.mp hg (toA6 e (d0_sign _ (e1_sub _ he)))).mp he,
    mem_N1_of⟩

theorem mem_N2_iff {g : A6} :
    g ∈ N2 ↔ ∀ e ∈ e2List, (g : Perm (Fin 6)) * e * (g : Perm (Fin 6))⁻¹ ∈ e2List :=
  ⟨fun hg e he => (Subgroup.mem_normalizer_iff.mp hg (toA6 e (d0_sign _ (e2_sub _ he)))).mp he,
    mem_N2_of⟩

theorem card_N1 : Nat.card N1 = 24 := by
  have e : ↥N1 ≃ {σ : Perm (Fin 6) // σ ∈ (Finset.univ.filter fun g : Perm (Fin 6) =>
      sign g = 1 ∧ ∀ e ∈ e1List, g * e * g⁻¹ ∈ e1List)} :=
    { toFun := fun g => ⟨((g : A6) : Perm (Fin 6)), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, mem_alternatingGroup.mp (g : A6).2, mem_N1_iff.mp g.2⟩⟩
      invFun := fun σ => ⟨⟨σ.1, mem_alternatingGroup.mpr (Finset.mem_filter.mp σ.2).2.1⟩,
        mem_N1_iff.mpr (Finset.mem_filter.mp σ.2).2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, n1_count]

theorem card_N2 : Nat.card N2 = 24 := by
  have e : ↥N2 ≃ {σ : Perm (Fin 6) // σ ∈ (Finset.univ.filter fun g : Perm (Fin 6) =>
      sign g = 1 ∧ ∀ e ∈ e2List, g * e * g⁻¹ ∈ e2List)} :=
    { toFun := fun g => ⟨((g : A6) : Perm (Fin 6)), Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, mem_alternatingGroup.mp (g : A6).2, mem_N2_iff.mp g.2⟩⟩
      invFun := fun σ => ⟨⟨σ.1, mem_alternatingGroup.mpr (Finset.mem_filter.mp σ.2).2.1⟩,
        mem_N2_iff.mpr (Finset.mem_filter.mp σ.2).2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, n2_count]

theorem D0_le_N1 : D0 ≤ N1 := fun _ hd => mem_N1_of fun _ he => d0_normalizes_e1 _ hd _ he

theorem D0_le_N2 : D0 ≤ N2 := fun _ hd => mem_N2_of fun _ he => d0_normalizes_e2 _ hd _ he

theorem x0_mem_N1 : toA6 x0 x0_y0_facts.1 ∈ N1 := mem_N1_of x0_y0_facts.2.2.2.2.1

theorem y0_mem_N2 : toA6 y0 x0_y0_facts.2.2.2.2.2.1 ∈ N2 :=
  mem_N2_of x0_y0_facts.2.2.2.2.2.2.2.2.2.1

theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem sup_N_eq_top : N1 ⊔ N2 = ⊤ := by
  set Y := N1 ⊔ N2 with hY
  have h8 : 8 ∣ Nat.card Y := card_D0 ▸ Subgroup.card_dvd_of_le (D0_le_N1.trans le_sup_left)
  have hx : toA6 x0 x0_y0_facts.1 ∈ Y := Subgroup.mem_sup_left x0_mem_N1
  have hy : toA6 y0 x0_y0_facts.2.2.2.2.2.1 ∈ Y := Subgroup.mem_sup_right y0_mem_N2
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h3 : 3 ∣ Nat.card Y := by
    have ho : orderOf (⟨_, hx⟩ : Y) = 3 := by
      rw [Subgroup.orderOf_mk, orderOf_eq_prime_iff]
      refine ⟨Subtype.ext x0_y0_facts.2.1, fun h => x0_y0_facts.2.2.1 (congrArg Subtype.val h)⟩
    exact ho ▸ orderOf_dvd_natCard _
  have h5 : 5 ∣ Nat.card Y := by
    have ho : orderOf (⟨_, Y.mul_mem hx hy⟩ : Y) = 5 := by
      rw [Subgroup.orderOf_mk, orderOf_eq_prime_iff]
      refine ⟨Subtype.ext x0y0_order_five.1, fun h => x0y0_order_five.2 (congrArg Subtype.val h)⟩
    exact ho ▸ orderOf_dvd_natCard _
  have h120 : 120 ∣ Nat.card Y :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num) h8 h3) h5
  have hdvd : Nat.card Y ∣ 360 := card_A6 ▸ Subgroup.card_subgroup_dvd_card Y
  have hcases : Nat.card Y = 120 ∨ Nat.card Y = 360 := by
    obtain ⟨k, hk⟩ := h120
    have hk3 : k ∣ 3 := by
      obtain ⟨m, hm⟩ := hdvd
      have h1 : 120 * (k * m) = 120 * 3 := by rw [← mul_assoc, ← hk, ← hm]
      exact ⟨m, (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h | h <;> subst h <;> omega
  rcases hcases with h | h
  · exfalso
    have hidx : Y.index = 3 := by
      have := Y.card_mul_index
      rw [h, card_A6] at this
      omega
    have : Y.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
    have hd := Y.index_normalCore_dvd_factorial_index
    have hsimple : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y.normalCore with hb | ht
    · rw [hb, Subgroup.index_bot, card_A6, hidx] at hd
      exact absurd hd (by decide)
    · have : Y = ⊤ := eq_top_iff.mpr (ht ▸ Y.normalCore_le)
      rw [this, Subgroup.card_top, card_A6] at h
      omega
  · exact Subgroup.eq_top_of_card_eq Y (h.trans card_A6.symm)

section Endo

variable (β : A6 →* A6)

abbrev zA : A6 := toA6 z6 (d0_sign _ (by simp [d0List]))

abbrev aA : A6 := toA6 a6 (d0_sign _ (by simp [d0List]))

abbrev bA : A6 := toA6 b6 (d0_sign _ (by simp [d0List]))

abbrev xA : A6 := toA6 x0 x0_y0_facts.1

abbrev yA : A6 := toA6 y0 x0_y0_facts.2.2.2.2.2.1

theorem map_mem_invList (hinj : Function.Injective β) (hD : ∀ d ∈ D0, β d ∈ D0) {u : A6}
    (hu : u ∈ D0) (hu1 : u ≠ 1) (hu2 : u * u = 1) : ((β u : A6) : Perm (Fin 6)) ∈ invList := by
  refine inv_D0 _ (hD u hu) (fun h => hu1 (hinj ?_)) ?_
  · rw [map_one]
    exact Subtype.ext h
  · have : β u * β u = 1 := by rw [← map_mul, hu2, map_one]
    exact congrArg Subtype.val this

theorem map_le_of_gens {E E' : Subgroup A6} {l : List (Perm (Fin 6))} {g : A6}
    (hl : ∀ e : A6, e ∈ E → (e : Perm (Fin 6)) ∈ l)
    (hl' : l = [1, z6, (g : Perm (Fin 6)), z6 * (g : Perm (Fin 6))])
    (hz : β zA ∈ E') (hg : β g ∈ E') : E.map β ≤ E' := by
  rintro _ ⟨e, he, rfl⟩
  have h := hl e he
  rw [hl'] at h
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h
  · rw [show e = 1 from Subtype.ext h, map_one]
    exact E'.one_mem
  · rw [show e = zA from Subtype.ext h]
    exact hz
  · rw [show e = g from Subtype.ext h]
    exact hg
  · rw [show e = zA * g from Subtype.ext h, map_mul]
    exact E'.mul_mem hz hg

theorem map_eq_of_le {E E' : Subgroup A6} (hinj : Function.Injective β) (hle : E.map β ≤ E')
    (hc : Nat.card E' ≤ Nat.card E) : E.map β = E' :=
  Subgroup.eq_of_le_of_card_ge hle (by rwa [Subgroup.card_map_of_injective hinj])

theorem map_normalizes {E E' : Subgroup A6} (heq : E.map β = E') {x : A6}
    (hx : x ∈ Subgroup.normalizer (E : Set A6)) {e : A6} (he : e ∈ E') :
    β x * e * (β x)⁻¹ ∈ E' := by
  rw [← heq] at he ⊢
  obtain ⟨e', he', rfl⟩ := he
  refine ⟨x * e' * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx e').mp he', ?_⟩
  rw [map_mul, map_mul, map_inv]

theorem map_E1_eq (hinj : Function.Injective β) (hD : ∀ d ∈ D0, β d ∈ D0)
    (hx : ∃ g : A6, β xA = g * xA * g⁻¹) : E1.map β = E1 := by
  obtain ⟨hz2, ha2, -, hz1, ha1, -, hza, -, hcza, -⟩ := zab_facts
  have hzD : zA ∈ D0 := e1_sub _ (by simp [e1List])
  have haD : aA ∈ D0 := e1_sub _ (by simp [e1List])
  have hz := map_mem_invList β hinj hD hzD (fun h => hz1 (congrArg Subtype.val h))
    (Subtype.ext hz2)
  have ha := map_mem_invList β hinj hD haD (fun h => ha1 (congrArg Subtype.val h))
    (Subtype.ext ha2)
  have hne : ((β zA : A6) : Perm (Fin 6)) ≠ ((β aA : A6) : Perm (Fin 6)) := fun h =>
    hza (congrArg Subtype.val (hinj (Subtype.ext h)))
  have hcomm : ((β zA : A6) : Perm (Fin 6)) * ((β aA : A6) : Perm (Fin 6)) =
      ((β aA : A6) : Perm (Fin 6)) * ((β zA : A6) : Perm (Fin 6)) := by
    have : β zA * β aA = β aA * β zA := by
      rw [← map_mul, ← map_mul, show zA * aA = aA * zA from Subtype.ext hcza]
    exact congrArg Subtype.val this
  have hl : ∀ e : A6, e ∈ E1 → (e : Perm (Fin 6)) ∈ e1List := fun _ he => he
  rcases klein_D0 _ hz _ ha hne hcomm with ⟨hz', ha'⟩ | ⟨hz', ha'⟩
  · exact map_eq_of_le β hinj (map_le_of_gens β (g := aA) hl rfl hz' ha') le_rfl
  · exfalso
    have heq := map_eq_of_le β hinj (map_le_of_gens β (E' := E2) (g := aA) hl rfl hz' ha')
      (card_E2.trans card_E1.symm).le
    have h3 : ((β xA : A6) : Perm (Fin 6)) ^ 3 = 1 := by
      have : β xA ^ 3 = 1 := by
        rw [← map_pow, show xA ^ 3 = 1 from Subtype.ext x0_y0_facts.2.1, map_one]
      exact congrArg Subtype.val this
    have h1 : ((β xA : A6) : Perm (Fin 6)) ≠ 1 := by
      intro h
      have : β xA = β 1 := by rw [map_one]; exact Subtype.ext h
      exact x0_y0_facts.2.2.1 (congrArg Subtype.val (hinj this))
    have hfpf := fpf_of_normalizes_E2 ((β xA : A6) : Perm (Fin 6)) h3 h1
      (fun e he => map_normalizes β heq x0_mem_N1
        (e := toA6 e (d0_sign _ (e2_sub _ he))) he)
    obtain ⟨g, hg⟩ := hx
    apply hfpf ((g : Perm (Fin 6)) 3)
    rw [hg]
    show (g : Perm (Fin 6)) (x0 ((g : Perm (Fin 6))⁻¹ ((g : Perm (Fin 6)) 3))) =
      (g : Perm (Fin 6)) 3
    have h3' : (g : Perm (Fin 6))⁻¹ ((g : Perm (Fin 6)) 3) = 3 := by simp
    rw [h3', x0_y0_facts.2.2.2.1]

theorem map_E2_eq (hinj : Function.Injective β) (hD : ∀ d ∈ D0, β d ∈ D0)
    (hy : ∃ g : A6, β yA = g * yA * g⁻¹) : E2.map β = E2 := by
  obtain ⟨hz2, -, hb2, hz1, -, hb1, -, hzb, -, hczb⟩ := zab_facts
  have hzD : zA ∈ D0 := e2_sub _ (by simp [e2List])
  have hbD : bA ∈ D0 := e2_sub _ (by simp [e2List])
  have hz := map_mem_invList β hinj hD hzD (fun h => hz1 (congrArg Subtype.val h))
    (Subtype.ext hz2)
  have hb := map_mem_invList β hinj hD hbD (fun h => hb1 (congrArg Subtype.val h))
    (Subtype.ext hb2)
  have hne : ((β zA : A6) : Perm (Fin 6)) ≠ ((β bA : A6) : Perm (Fin 6)) := fun h =>
    hzb (congrArg Subtype.val (hinj (Subtype.ext h)))
  have hcomm : ((β zA : A6) : Perm (Fin 6)) * ((β bA : A6) : Perm (Fin 6)) =
      ((β bA : A6) : Perm (Fin 6)) * ((β zA : A6) : Perm (Fin 6)) := by
    have : β zA * β bA = β bA * β zA := by
      rw [← map_mul, ← map_mul, show zA * bA = bA * zA from Subtype.ext hczb]
    exact congrArg Subtype.val this
  have hl : ∀ e : A6, e ∈ E2 → (e : Perm (Fin 6)) ∈ e2List := fun _ he => he
  rcases klein_D0 _ hz _ hb hne hcomm with ⟨hz', hb'⟩ | ⟨hz', hb'⟩
  · exfalso
    have heq := map_eq_of_le β hinj (map_le_of_gens β (E' := E1) (g := bA) hl rfl hz' hb')
      (card_E1.trans card_E2.symm).le
    have h3 : ((β yA : A6) : Perm (Fin 6)) ^ 3 = 1 := by
      have : β yA ^ 3 = 1 := by
        rw [← map_pow, show yA ^ 3 = 1 from Subtype.ext x0_y0_facts.2.2.2.2.2.2.1, map_one]
      exact congrArg Subtype.val this
    have h1 : ((β yA : A6) : Perm (Fin 6)) ≠ 1 := by
      intro h
      have : β yA = β 1 := by rw [map_one]; exact Subtype.ext h
      exact x0_y0_facts.2.2.2.2.2.2.2.1 (congrArg Subtype.val (hinj this))
    obtain ⟨i, hi⟩ := fixed_of_normalizes_E1 ((β yA : A6) : Perm (Fin 6)) h3 h1
      (fun e he => map_normalizes β heq y0_mem_N2
        (e := toA6 e (d0_sign _ (e1_sub _ he))) he)
    obtain ⟨g, hg⟩ := hy
    rw [hg] at hi
    apply x0_y0_facts.2.2.2.2.2.2.2.2.1 ((g : Perm (Fin 6))⁻¹ i)
    have hi' : (g : Perm (Fin 6)) (y0 ((g : Perm (Fin 6))⁻¹ i)) = i := hi
    have := congrArg (fun j => ((g : Perm (Fin 6))⁻¹) j) hi'
    simpa using this
  · exact map_eq_of_le β hinj (map_le_of_gens β (g := bA) hl rfl hz' hb') le_rfl

theorem map_N_of_endo (hinj : Function.Injective β) (hD : ∀ d ∈ D0, β d ∈ D0)
    (hx : ∃ g : A6, β xA = g * xA * g⁻¹) (hy : ∃ g : A6, β yA = g * yA * g⁻¹) :
    (∀ n ∈ N1, β n ∈ N1) ∧ ∀ n ∈ N2, β n ∈ N2 :=
  ⟨fun _ hn => Subgroup.mem_normalizer_fintype fun _ he =>
      map_normalizes β (map_E1_eq β hinj hD hx) hn he,
    fun _ hn => Subgroup.mem_normalizer_fintype fun _ he =>
      map_normalizes β (map_E2_eq β hinj hD hy) hn he⟩

end Endo

end CFSG.Quasithin.H13.L32A.C.Alt6
