module

public import CFSG.Quasithin.EmptyFaithful.E111L2B
public import CFSG.Quasithin.EmptyFaithful.E111RMain
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R DihedralGroup

variable {G : Type} [Group G]

theorem le_normalizer_iSup {ι : Type*} {K : Subgroup G} (F : ι → Subgroup G) (s : Finset ι)
    (h : ∀ i ∈ s, K ≤ Subgroup.normalizer (F i : Set G)) :
    K ≤ Subgroup.normalizer ((⨆ i ∈ s, F i : Subgroup G) : Set G) := by
  intro k hk
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_iSup₂]
  exact iSup_congr fun i => iSup_congr fun hi => conjSub_eq_of_mem_normalizer (h i hi hk)

theorem isSolvable_iSup {ι : Type*} [DecidableEq ι] (F : ι → Subgroup G)
    (hF : ∀ i j, F i = F j ∨ ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x)
    (hs : ∀ i, Group.IsSolvable ↥(F i)) (s : Finset ι) :
    Group.IsSolvable ↥(⨆ i ∈ s, F i) := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : (⨆ i ∈ (∅ : Finset ι), F i) = ⊥ := by simp
    rw [h0]
    infer_instance
  | insert a s _ ih =>
    rw [Finset.iSup_insert, sup_comm]
    refine CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer ?_ ih (hs a)
    refine le_normalizer_iSup F s fun i _ => ?_
    rcases hF a i with h | h
    · rw [← h]
      exact Subgroup.le_normalizer
    · exact le_normalizer_of_comm h

theorem top_of_comp_le {X T S H : Subgroup G} (hR : E111Reduced G X T) (hS : IsComp X S)
    (hTH : T ≤ H) (hSH : S ≤ H) : H = ⊤ := by
  have hXH : X ≤ H := by
    rw [← iSup_conj_eq hR hS]
    refine iSup₂_le fun t ht => ?_
    rintro _ ⟨s, hs, rfl⟩
    exact H.mul_mem (H.mul_mem (hTH ht) (hSH hs)) (H.inv_mem (hTH ht))
  refine le_antisymm le_top ?_
  rw [← hR.2.2.2.2.2.2]
  exact sup_le hXH hTH

theorem normalizer_le_normalizer_centralizer (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  intro y hy
  have key : ∀ y ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      y * c * y⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro y hy c hc
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : y⁻¹ * s * y ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hy) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc _ hs'
    calc s * (y * c * y⁻¹) = y * ((y⁻¹ * s * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * s * y)) * y⁻¹ := by rw [h1]
      _ = y * c * y⁻¹ * s := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key y hy c, fun hc => ?_⟩
  have := key y⁻¹ (Subgroup.inv_mem _ hy) _ hc
  simpa [mul_assoc] using this

private def d4A : Subgroup (DihedralGroup 4) where
  carrier := ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4))
  mul_mem' {a b} ha hb := by
    have key : ∀ a ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)),
        ∀ b ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)),
          a * b ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)) := by decide
    exact key a ha b hb
  one_mem' := by decide
  inv_mem' {a} ha := by
    have key : ∀ a ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)),
        a⁻¹ ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)) := by decide
    exact key a ha

private def d4B : Subgroup (DihedralGroup 4) where
  carrier := ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4))
  mul_mem' {a b} ha hb := by
    have key : ∀ a ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)),
        ∀ b ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)),
          a * b ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)) := by decide
    exact key a ha b hb
  one_mem' := by decide
  inv_mem' {a} ha := by
    have key : ∀ a ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)),
        a⁻¹ ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)) := by decide
    exact key a ha

private theorem d4A_isKleinFour : IsKleinFour ↥d4A := by
  refine isKleinFour_of_sq ?_ fun x => Subtype.ext ?_
  · have e : ↥d4A ≃ {x // x ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4))} := Equiv.refl _
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  · have key : ∀ a ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4)), a * a = 1 := by decide
    exact key x.1 x.2

private theorem d4B_isKleinFour : IsKleinFour ↥d4B := by
  refine isKleinFour_of_sq ?_ fun x => Subtype.ext ?_
  · have e : ↥d4B ≃ {x // x ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4))} := Equiv.refl _
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    decide
  · have key : ∀ a ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)), a * a = 1 := by decide
    exact key x.1 x.2

theorem exists_two_kleinFour {R : Subgroup G} (f : ↥R ≃* DihedralGroup 4) :
    ∃ W₀ W₂ : Subgroup G, W₀ ≤ R ∧ W₂ ≤ R ∧ IsKleinFour ↥W₀ ∧ IsKleinFour ↥W₂ ∧ W₀ ≠ W₂ := by
  set W₀ : Subgroup G := (d4A.map f.symm.toMonoidHom).map R.subtype
  set W₂ : Subgroup G := (d4B.map f.symm.toMonoidHom).map R.subtype
  have hle : ∀ K : Subgroup ↥R, K.map R.subtype ≤ R := fun K => Subgroup.map_subtype_le K
  have hK : ∀ K : Subgroup (DihedralGroup 4), IsKleinFour ↥K →
      IsKleinFour ↥((K.map f.symm.toMonoidHom).map R.subtype) := fun K hK =>
    isKleinFour_of_equiv ((K.equivMapOfInjective _ f.symm.injective).trans
      ((K.map f.symm.toMonoidHom).equivMapOfInjective _ R.subtype_injective)).symm hK
  refine ⟨W₀, W₂, hle _, hle _, hK _ d4A_isKleinFour, hK _ d4B_isKleinFour, fun h => ?_⟩
  have h0 : ((f.symm (sr 0) : ↥R) : G) ∈ W₀ :=
    ⟨f.symm (sr 0), ⟨sr 0, Finset.mem_coe.mpr
      (by decide : sr 0 ∈ ({1, r 2, sr 0, sr 2} : Finset (DihedralGroup 4))), rfl⟩, rfl⟩
  rw [h] at h0
  obtain ⟨y, ⟨d, hd, rfl⟩, hy⟩ := h0
  have : d = sr 0 := f.symm.injective (Subtype.ext hy)
  subst this
  have hd' : sr 0 ∈ ({1, r 2, sr 1, sr 3} : Finset (DihedralGroup 4)) := Finset.mem_coe.mp hd
  exact absurd hd' (by decide)

theorem sup_eq_of_ne [Finite G] {P U V : Subgroup G} (hP : Nat.card P = 8) (hUP : U ≤ P)
    (hVP : V ≤ P) (hU : IsKleinFour ↥U) (hV : IsKleinFour ↥V) (hne : U ≠ V) : U ⊔ V = P := by
  have hle : U ⊔ V ≤ P := sup_le hUP hVP
  have h1 : Nat.card ↥(U ⊔ V) ∣ 8 := hP ▸ Subgroup.card_dvd_of_le hle
  have h2 : 4 ∣ Nat.card ↥(U ⊔ V) := hU.card_four ▸ Subgroup.card_dvd_of_le le_sup_left
  have h3 : Nat.card ↥(U ⊔ V) ≠ 4 := by
    intro h4
    have hUe : U = U ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [h4, hU.card_four])
    have hVe : V = U ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [h4, hV.card_four])
    exact hne (hUe.trans hVe.symm)
  have h8 : Nat.card ↥(U ⊔ V) = 8 := by
    have hpos : 0 < Nat.card ↥(U ⊔ V) := Nat.card_pos
    have hle8 : Nat.card ↥(U ⊔ V) ≤ 8 := Nat.le_of_dvd (by norm_num) h1
    interval_cases h : Nat.card ↥(U ⊔ V) <;> simp_all
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h8, hP])

theorem conj_eq_of_mem_normalizer {P : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (eP : ↥P ≃* DihedralGroup (2 ^ m)) {z : G} (hz : z ∈ P) (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ P, z * x = x * z) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    g * z * g⁻¹ = z := by
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  refine central_unique hm eP ((Subgroup.mem_normalizer_iff.mp hg z).mp hz) hz ?_ hz1 ?_ hzc
  · intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  · intro x hx
    have hx' : g⁻¹ * x * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) x).mp hx
      simpa using this
    have h1 := hzc _ hx'
    calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [h1]
      _ = x * (g * z * g⁻¹) := by group

theorem eq_of_comm_sylow [Finite G] {D T : Subgroup G} (hTD : IsSylowIn 2 (T ⊓ D) D) {m : ℕ}
    (hm : 2 ≤ m) (eP : ↥(T ⊓ D) ≃* DihedralGroup (2 ^ m)) {z z' : G} (hz : z ∈ T ⊓ D)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ T ⊓ D, z * x = x * z) (hz'D : z' ∈ D)
    (hz'2 : orderOf z' = 2) (hz'c : ∀ x ∈ T ⊓ D, z' * x = x * z') : z' = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 ↥(T ⊓ D ⊔ Subgroup.zpowers z') := by
    refine IsPGroup.to_sup_of_normal_right' hTD.isPGroup ?_ ?_
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2, pow_one])
    · refine le_normalizer_of_comm fun x hx y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_right (hz'c x hx).symm k))
  have hle : T ⊓ D ⊔ Subgroup.zpowers z' ≤ D :=
    sup_le inf_le_right (Subgroup.zpowers_le.mpr hz'D)
  have heq := eq_of_le_of_isPGroup hTD le_sup_left hle hQ
  have hz'P : z' ∈ T ⊓ D := heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z')
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  have hz'1 : z' ≠ 1 := fun h => by rw [h, orderOf_one] at hz'2; omega
  exact central_unique hm eP hz'P hz hz'1 hz1 hz'c hzc

theorem conjSub_inf (g : G) (H K : Subgroup G) :
    A1b.conjSub g (H ⊓ K) = A1b.conjSub g H ⊓ A1b.conjSub g K :=
  Subgroup.map_inf H K _ (MulAut.conj g).injective

theorem conjSub_sup (g : G) (H K : Subgroup G) :
    A1b.conjSub g (H ⊔ K) = A1b.conjSub g H ⊔ A1b.conjSub g K :=
  Subgroup.map_sup H K _

theorem mem_normalizer_sup {g : G} {H K : Subgroup G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_sup, conjSub_eq_of_mem_normalizer hH, conjSub_eq_of_mem_normalizer hK]

theorem isKleinFour_conjSub (g : G) {V : Subgroup G} (hV : IsKleinFour ↥V) :
    IsKleinFour ↥(A1b.conjSub g V) :=
  isKleinFour_of_equiv (V.equivMapOfInjective _ (MulAut.conj g).injective).symm hV

theorem orderOf_conj' (g z : G) : orderOf (g * z * g⁻¹) = orderOf z := by
  have : g * z * g⁻¹ = MulAut.conj g z := rfl
  rw [this, MulEquiv.orderOf_eq]

theorem le_gOne {T : Subgroup G} {Ω : Set (Subgroup G)} [Finite G] (hΩ : E1.IsInvColl ⊤ Ω) :
    T ≤ E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) :=
  fun t ht => Subgroup.mem_sup_right ⟨Subgroup.mem_top t, E1.le_normalizer_weakClosure hΩ ht⟩

section Main

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem normalizer_inf_le (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {X T S W : Subgroup G}
    (hR : E111Reduced G X T) (hS : IsComp X S) (hSp : IsPSL 2 p 1 ↥S) (hWS : W ≤ S)
    (hW : IsKleinFour ↥W)
    (hfix : ∀ t ∈ T ⊓ Subgroup.normalizer (S : Set G), A1b.conjSub t W = W)
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω) :
    Subgroup.normalizer (W : Set G) ⊓ S ≤
      E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype ↥T := Fintype.ofFinite _
  set L₀ := Subgroup.normalizer (W : Set G) ⊓ S with hL₀
  set F : ↥T → Subgroup G := fun t => A1b.conjSub (t : G) L₀ with hF
  have hconj : ∀ u : G, A1b.conjSub u S = S → A1b.conjSub u W = W →
      A1b.conjSub u L₀ = L₀ := by
    intro u hu hw
    rw [hL₀, conjSub_inf, A1b.conjSub_normalizer, hw, hu]
  have hF2 : ∀ i j, F i = F j ∨ ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x := by
    intro i j
    rcases (hS.conj hR.1 i).eq_or_commute (hS.conj hR.1 j) with h | h
    · left
      set u : G := (i : G)⁻¹ * j with hu
      have hu1 : A1b.conjSub u S = S := by
        rw [hu, A1b.conjSub_mul, ← h, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
      have huT : u ∈ T := T.mul_mem (T.inv_mem i.2) j.2
      have hu2 := hconj u hu1 (hfix u ⟨huT, mem_normalizer_of_conjSub_eq hu1⟩)
      show A1b.conjSub (i : G) L₀ = A1b.conjSub (j : G) L₀
      have hj : (j : G) = i * u := by rw [hu]; group
      rw [hj, A1b.conjSub_mul, hu2]
    · right
      intro x hx y hy
      exact h x (A1b.conjSub_mono _ inf_le_right hx) y (A1b.conjSub_mono _ inf_le_right hy)
  have hs : ∀ i, Group.IsSolvable ↥(F i) := by
    intro i
    have h24 : Nat.card ↥(F i) = 2 ^ 3 * 3 ^ 1 := by
      rw [hF, card_conjSub, sub_card_normalizer hp7 hp8 hSp hWS hW]
      norm_num
    exact CFSG.QuasithinUnique.Vol2Native.A312L.isSolvable_of_card_two_three h24
  have hM := isSolvable_iSup F hF2 hs Finset.univ
  have hMeq : (⨆ i ∈ (Finset.univ : Finset ↥T), F i) = ⨆ i, F i := by simp
  rw [hMeq] at hM
  have hTM : T ≤ Subgroup.normalizer ((⨆ i, F i : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_conjSub_eq
    rw [E111R.conjSub_iSup]
    have h1 : ∀ i : ↥T, A1b.conjSub t (F i) = F (⟨t, ht⟩ * i) := fun i => by
      simp only [hF, Subgroup.coe_mul]
      rw [A1b.conjSub_mul]
    simp only [h1]
    exact Equiv.iSup_comp (g := F) (Equiv.mulLeft ⟨t, ht⟩)
  have hT2 : IsPGroup 2 T := hR.2.2.2.2.2.1.isPGroup
  have hTs : Group.IsSolvable ↥T := by
    have := hT2.isNilpotent
    infer_instance
  have hH := CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer hTM hM hTs
  have hHG := E1.le_eGen_sup_normalizer_of_isSolvable hR.2.2.2.2.2.1 le_sup_right hH hΩ
  have hL₀M : L₀ ≤ ⨆ i, F i := by
    have h1 : F 1 ≤ ⨆ i, F i := le_iSup F 1
    simpa [hF, A1b.conjSub_one] using h1
  exact hL₀M.trans (le_sup_left.trans hHG)

end Main

section Cases

variable [Finite G] {p : ℕ} [Fact p.Prime]

theorem caseNU (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {X T S : Subgroup G}
    (hR : E111Reduced G X T) (hS : IsComp X S) (hSp : IsPSL 2 p 1 ↥S)
    (h8 : Nat.card ↥(T ⊓ S) = 8)
    (hfix : ∀ t ∈ T ⊓ Subgroup.normalizer (S : Set G), ∀ W : Subgroup G, W ≤ T ⊓ S →
      IsKleinFour ↥W → A1b.conjSub t W = W)
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω) :
    E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G)) = ⊤ := by
  have hTS := isSylowIn_inf hR hS
  obtain ⟨m, hm, ⟨eP⟩⟩ := sub_dihedral hp7 hp8 hSp hTS
  have hm2 : m = 2 := by
    have h := Nat.card_congr eP.toEquiv
    rw [DihedralGroup.nat_card, h8] at h
    have h4 : 2 ^ m = 2 ^ 2 := by omega
    exact Nat.pow_right_injective le_rfl h4
  subst hm2
  obtain ⟨z, hzP, hz2, hzc, hzV, -⟩ := CFSG.Quasithin.E22L2.dihedral_sylow_data hm eP
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  obtain ⟨W₀, W₂, hW₀, hW₂, hK₀, hK₂, hne⟩ := exists_two_kleinFour (R := T ⊓ S) eP
  set G₁ := E1.eGen 1 ⊤ T Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T Ω : Set G))
  have hTG : T ≤ G₁ := le_gOne hΩ
  have hN₀ := normalizer_inf_le hp7 hp8 hR hS hSp (hW₀.trans inf_le_right) hK₀
    (fun t ht => hfix t ht W₀ hW₀ hK₀) hΩ
  have hN₂ := normalizer_inf_le hp7 hp8 hR hS hSp (hW₂.trans inf_le_right) hK₂
    (fun t ht => hfix t ht W₂ hW₂ hK₂) hΩ
  obtain ⟨g, hg, hgz⟩ := sub_moves hp7 hp8 hSp (hW₀.trans inf_le_right) hK₀ (hzV W₀ hW₀ hK₀) hz1
  rcases sub_og hp7 hp8 hSp hTS hm eP hzP hz2 hzc (le_inf (inf_le_left.trans hTG) inf_le_right)
      (inf_le_right : G₁ ⊓ S ≤ S) with h | h | ⟨W, hWT, hWK, hLW⟩
  · exact top_of_comp_le hR hS hTG (h ▸ inf_le_left)
  · exfalso
    have := h (le_inf hN₀ inf_le_right hg)
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact hgz this
  · exfalso
    have hc := sub_card_normalizer hp7 hp8 hSp (hWT.trans inf_le_right) hWK
    have e₀ : Subgroup.normalizer (W₀ : Set G) ⊓ S = Subgroup.normalizer (W : Set G) ⊓ S :=
      Subgroup.eq_of_le_of_card_ge (hLW ▸ le_inf hN₀ inf_le_right)
        (by rw [hc, sub_card_normalizer hp7 hp8 hSp (hW₀.trans inf_le_right) hK₀])
    have e₂ : Subgroup.normalizer (W₂ : Set G) ⊓ S = Subgroup.normalizer (W : Set G) ⊓ S :=
      Subgroup.eq_of_le_of_card_ge (hLW ▸ le_inf hN₂ inf_le_right)
        (by rw [hc, sub_card_normalizer hp7 hp8 hSp (hW₂.trans inf_le_right) hK₂])
    have hsup := sup_eq_of_ne h8 hW₀ hW₂ hK₀ hK₂ hne
    have hg2 : g ∈ Subgroup.normalizer (W₂ : Set G) ⊓ S := e₂ ▸ e₀ ▸ hg
    have hgP : g ∈ Subgroup.normalizer ((T ⊓ S : Subgroup G) : Set G) :=
      hsup ▸ mem_normalizer_sup hg.1 hg2.1
    have hfz := conj_eq_of_mem_normalizer hm eP hzP hz2 hzc hgP
    apply hgz
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hfz]

theorem le_of_moves (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7) {X T S H : Subgroup G}
    (hR : E111Reduced G X T) (hS : IsComp X S) (hSp : IsPSL 2 p 1 ↥S)
    (hU : ¬ (Nat.card ↥(T ⊓ S) = 8 ∧ ∀ t ∈ T ⊓ Subgroup.normalizer (S : Set G),
      ∀ W : Subgroup G, W ≤ T ⊓ S → IsKleinFour ↥W → A1b.conjSub t W = W))
    (hTH : T ≤ H) {z : G} (hz : z ∈ T ⊓ S) (hz2 : orderOf z = 2)
    (hzc : ∀ x ∈ T ⊓ S, z * x = x * z) {g : G} (hgH : g ∈ H)
    (hgS : g ∈ Subgroup.normalizer (S : Set G)) (hgz : g * z ≠ z * g) : S ≤ H := by
  have hTS := isSylowIn_inf hR hS
  obtain ⟨m, hm, ⟨eP⟩⟩ := sub_dihedral hp7 hp8 hSp hTS
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; omega
  set M := (H ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.centralizer (S : Set G) with hM
  set L := S ⊓ M with hL
  have hMN : H ⊓ Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
    inf_le_right.trans (normalizer_le_normalizer_centralizer S)
  have hLn : ∀ y ∈ H ⊓ Subgroup.normalizer (S : Set G), A1b.conjSub y L = L := by
    intro y hy
    rw [hL, hM, conjSub_inf, conjSub_sup, conjSub_eq_of_mem_normalizer hy.2,
      conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hy),
      conjSub_eq_of_mem_normalizer (hMN hy)]
  have hTL : T ⊓ S ≤ L := fun x hx =>
    ⟨hx.2, Subgroup.mem_sup_left ⟨hTH hx.1, Subgroup.le_normalizer hx.2⟩⟩
  have hgN : g ∈ H ⊓ Subgroup.normalizer (S : Set G) := ⟨hgH, hgS⟩
  have hkey : ¬ L ≤ Subgroup.centralizer ({z} : Set G) := by
    intro hLz
    apply hgz
    have hginv : g⁻¹ ∈ H ⊓ Subgroup.normalizer (S : Set G) := inv_mem hgN
    have hz'c : ∀ x ∈ L, (g * z * g⁻¹) * x = x * (g * z * g⁻¹) := by
      intro x hx
      have hx' : g⁻¹ * x * g ∈ L := by
        have h1 := A1b.mem_conjSub_of_mem (g := g⁻¹) hx
        rw [hLn g⁻¹ hginv, inv_inv] at h1
        exact h1
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hLz hx')
      calc g * z * g⁻¹ * x = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by rw [h1]
        _ = x * (g * z * g⁻¹) := by group
    have hz'S : g * z * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hgS z).mp hz.2
    have hfz := eq_of_comm_sylow hTS hm eP hz hz2 hzc hz'S (by rw [orderOf_conj']; exact hz2)
      fun x hx => hz'c x (hTL hx)
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hfz]
  rcases sub_og hp7 hp8 hSp hTS hm eP hz hz2 hzc hTL inf_le_left with h | h | ⟨W, hWT, hWK, hLW⟩
  ·
    refine le_of_diag hS.simple (fun h0 => hz1 (by rw [h0] at hz; exact hz)) hTH fun x hx => ?_
    have hxM : x ∈ Subgroup.centralizer (S : Set G) ⊔ (H ⊓ Subgroup.normalizer (S : Set G)) := by
      rw [sup_comm]
      exact (h.symm ▸ hx : x ∈ L).2
    obtain ⟨c, hc, y, hy, rfl⟩ := exists_mul_of_mem_sup hMN hxM
    refine ⟨y, hy.1, ?_⟩
    have hc' : y⁻¹ * c⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
      have := (Subgroup.mem_normalizer_iff.mp (hMN (inv_mem hy)) c⁻¹).mp (inv_mem hc)
      simpa using this
    have : (c * y)⁻¹ * y = y⁻¹ * c⁻¹ * y := by group
    rw [this]
    exact hc'
  · exact absurd h hkey
  · exfalso
    have hcard24 := sub_card_normalizer hp7 hp8 hSp (hWT.trans inf_le_right) hWK
    have hcardP : Nat.card ↥(T ⊓ S) = 2 * 2 ^ m := by
      rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
    have hm2 : m = 2 := by
      have hdvd : Nat.card ↥(T ⊓ S) ∣ 24 := hcard24 ▸ hLW ▸ Subgroup.card_dvd_of_le hTL
      rw [hcardP] at hdvd
      have h3 : 2 ^ m ∣ 12 :=
        Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) (by simpa using hdvd)
      have h4 : 2 ^ m ≤ 12 := Nat.le_of_dvd (by norm_num) h3
      have h5 : m < 4 := by
        by_contra hc
        push Not at hc
        have : 2 ^ 4 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hc
        omega
      interval_cases m <;> simp_all
    subst hm2
    have h8 : Nat.card ↥(T ⊓ S) = 8 := by rw [hcardP]; norm_num
    obtain ⟨t, ht, V, hVT, hVK, htV⟩ : ∃ t ∈ T ⊓ Subgroup.normalizer (S : Set G),
        ∃ V : Subgroup G, V ≤ T ⊓ S ∧ IsKleinFour ↥V ∧ A1b.conjSub t V ≠ V := by
      by_contra hc
      push Not at hc
      exact hU ⟨h8, fun t ht W hW hWK => hc t ht W hW hWK⟩
    have htN : t ∈ H ⊓ Subgroup.normalizer (S : Set G) := ⟨hTH ht.1, ht.2⟩
    have htP : A1b.conjSub t (T ⊓ S) = T ⊓ S := by
      rw [conjSub_inf, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer ht.1),
        conjSub_eq_of_mem_normalizer ht.2]
    have hconjle : ∀ U : Subgroup G, U ≤ T ⊓ S → A1b.conjSub t U ≤ T ⊓ S := fun U hU =>
      htP ▸ A1b.conjSub_mono t hU
    have htW : A1b.conjSub t W = W := by
      by_contra hne
      apply hkey
      have hLW' : L = Subgroup.normalizer (A1b.conjSub t W : Set G) ⊓ S := by
        rw [← hLn t htN, hLW, conjSub_inf, A1b.conjSub_normalizer,
          conjSub_eq_of_mem_normalizer ht.2]
      have hsup := sup_eq_of_ne h8 hWT (hconjle W hWT) hWK (isKleinFour_conjSub t hWK)
        (Ne.symm hne)
      intro x hx
      have hx1 : x ∈ Subgroup.normalizer (W : Set G) := (hLW ▸ hx : x ∈ _ ⊓ S).1
      have hx2 : x ∈ Subgroup.normalizer (A1b.conjSub t W : Set G) := (hLW' ▸ hx : x ∈ _ ⊓ S).1
      have hxP : x ∈ Subgroup.normalizer ((T ⊓ S : Subgroup G) : Set G) :=
        hsup ▸ mem_normalizer_sup hx1 hx2
      have hfz := conj_eq_of_mem_normalizer hm eP hz hz2 hzc hxP
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x * z = x * z * x⁻¹ * x := by group
        _ = z * x := by rw [hfz]
    have htW' : A1b.conjSub t⁻¹ W = W := by
      conv_lhs => rw [← htW]
      rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
    rcases klein_three (R := T ⊓ S) eP hWT hVT (hconjle V hVT) hWK hVK
        (isKleinFour_conjSub t hVK) with h1 | h1 | h1
    · exact htV (by rw [← h1, htW])
    · apply htV
      have h2 := htW'
      rw [h1, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h2
      exact h2.symm
    · exact htV h1.symm

end Cases

end CFSG.Quasithin.E2.E22N.E111L
