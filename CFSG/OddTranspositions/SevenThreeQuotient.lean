module

public import CFSG.OddTranspositions.SevenThreeRadical
public import CFSG.Timmesfeld.Bridge.Asc72Theorem

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {X : Type} [Group X]

theorem image_isClass_quotient {Θ : Set X} {d₀ : X} (hΘ : Θ = {g | IsConj d₀ g})
    (N : Subgroup X) [N.Normal] :
    ∃ c : X ⧸ N, (QuotientGroup.mk' N) '' Θ = {g | IsConj c g} := by
  refine ⟨QuotientGroup.mk' N d₀, ?_⟩
  rw [hΘ]
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [isConj_iff] at hx ⊢
    obtain ⟨c, hc⟩ := hx
    exact ⟨QuotientGroup.mk' N c, by rw [← hc]; simp [map_mul]⟩
  · simp only [Set.mem_setOf_eq]
    rw [isConj_iff]
    rintro ⟨y, hy⟩
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective N y
    refine ⟨z * d₀ * z⁻¹, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [isConj_iff]
      exact ⟨z, rfl⟩
    · rw [← hy]
      simp only [map_mul, map_inv]

theorem image_isOddTransp_quotient [Finite X] {Θ : Set X} (N : Subgroup X) [N.Normal]
    (hodd : IsOddTransp Θ) (hne : ∀ x ∈ Θ, QuotientGroup.mk' N x ≠ 1) :
    IsOddTransp ((QuotientGroup.mk' N) '' Θ) := by
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    have hdvd : orderOf (QuotientGroup.mk' N x) ∣ orderOf x := orderOf_map_dvd _ x
    rw [hodd.1 x hx] at hdvd
    have hne1 : orderOf (QuotientGroup.mk' N x) ≠ 1 := fun h =>
      hne x hx (orderOf_eq_one_iff.mp h)
    have hpos : 0 < orderOf (QuotientGroup.mk' N x) := orderOf_pos _
    have : orderOf (QuotientGroup.mk' N x) ∣ 2 := hdvd
    have := Nat.dvd_prime (by norm_num : Nat.Prime 2) |>.mp this
    rcases this with h | h
    · exact absurd h hne1
    · exact h
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have hdvd : orderOf (QuotientGroup.mk' N x * QuotientGroup.mk' N y) ∣ orderOf (x * y) := by
      rw [← map_mul]
      exact orderOf_map_dvd _ _
    rcases hodd.2 x hx y hy with h | h
    · left
      exact hdvd.trans h
    · right
      exact Odd.of_dvd_nat h hdvd

theorem image_closure_eq_top_quotient {Θ : Set X} (N : Subgroup X) [N.Normal]
    (hgen : Subgroup.closure Θ = ⊤) :
    Subgroup.closure ((QuotientGroup.mk' N) '' Θ) = ⊤ := by
  rw [← MonoidHom.map_closure (QuotientGroup.mk' N) Θ, hgen, Subgroup.map_top,
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)]

variable {G : Type} [Group G] [Finite G] {D : Set G}

@[expose] def DeltaK (D : Set G) (z : G) : Set (thirdK D z) :=
  {x | (x : G) ∈ Delta D z}

@[expose] def DeltaBar (D : Set G) (z : G) :
    Set (thirdK D z ⧸ CFSG.solvableRadical (thirdK D z)) :=
  (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D z))) '' DeltaK D z

theorem DeltaK_isOddTransp (hS : Setup G D) (z : G) : IsOddTransp (DeltaK D z) := by
  constructor
  · intro x hx
    rw [← Subgroup.orderOf_coe]
    exact hS.oddT.1 _ (mem_Delta_iff.mp hx).1
  · intro x hx y hy
    have h := hS.oddT.2 (x : G) (mem_Delta_iff.mp hx).1 (y : G) (mem_Delta_iff.mp hy).1
    have hcoe : orderOf (x * y : thirdK D z) = orderOf ((x : G) * (y : G)) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rwa [hcoe]

theorem DeltaK_closure_eq_top (z : G) : Subgroup.closure (DeltaK D z) = ⊤ := by
  have h := Subgroup.closure_preimage_eq_top (Delta D z)
  have hK : DeltaK D z = (thirdK D z).subtype ⁻¹' Delta D z := rfl
  rw [hK]
  change Subgroup.closure ((Subgroup.closure (Delta D z)).subtype ⁻¹' Delta D z) = ⊤
  exact h

theorem DeltaK_class (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n)
    (hord : orderOf (u * v * w) = 2 * n) :
    ∃ d₀ : thirdK D ((u * v * w) ^ n),
      DeltaK D ((u * v * w) ^ n) = {x | IsConj d₀ x} := by
  let z : G := (u * v * w) ^ n
  let K : Subgroup G := thirdK D z
  have hthird := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  obtain ⟨-, -, hzu, -, -, -⟩ := hthird
  have huΔ : u ∈ Delta D z := mem_Delta_iff.mpr ⟨htri.1, hzu.symm⟩
  refine ⟨⟨u, Delta_subset_thirdK huΔ⟩, ?_⟩
  ext x
  constructor
  · intro hx
    have hxΔ : (x : G) ∈ Delta D z := hx
    obtain ⟨k, hkK, hku⟩ := thirdK_transitive hS hL htri hn hord x hxΔ
    simp only [Set.mem_setOf_eq]
    rw [isConj_iff]
    exact ⟨⟨k, hkK⟩, Subtype.ext hku⟩
  · intro hx
    simp only [Set.mem_setOf_eq] at hx
    rw [isConj_iff] at hx
    obtain ⟨c, hc⟩ := hx
    have hcG : (c : G) * u * (c : G)⁻¹ = (x : G) := by
      have := congrArg Subtype.val hc
      simpa using this
    change (x : G) ∈ Delta D z
    rw [← hcG]
    exact Delta_conj_mem hS.normal c.2 huΔ

theorem DeltaK_mk_ne_one (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    ∀ x ∈ DeltaK D ((u * v * w) ^ n),
      QuotientGroup.mk' (CFSG.solvableRadical (thirdK D ((u * v * w) ^ n))) x ≠ 1 := by
  intro x hx hx1
  have hxR : x ∈ CFSG.solvableRadical (thirdK D ((u * v * w) ^ n)) :=
    (QuotientGroup.eq_one_iff x).mp hx1
  have hxmap : (x : G) ∈ ((CFSG.solvableRadical (thirdK D ((u * v * w) ^ n))).map
      (thirdK D ((u * v * w) ^ n)).subtype : Subgroup G) := ⟨x, hxR, rfl⟩
  have hempty := Delta_inter_solvableRadical_eq_empty hS hL htri hn hn1 hord
  rw [Set.eq_empty_iff_forall_notMem] at hempty
  exact hempty (x : G) ⟨hx, hxmap⟩

theorem thirdK_quotient_setup (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    Setup (thirdK D ((u * v * w) ^ n) ⧸
        CFSG.solvableRadical (thirdK D ((u * v * w) ^ n)))
      (DeltaBar D ((u * v * w) ^ n)) := by
  obtain ⟨d₀, hclass⟩ := DeltaK_class hS hL htri hn hord
  exact
    { isClass := image_isClass_quotient hclass _
      oddT := image_isOddTransp_quotient _
        (DeltaK_isOddTransp hS _)
        (DeltaK_mk_ne_one hS hL htri hn hn1 hord)
      gen := image_closure_eq_top_quotient _ (DeltaK_closure_eq_top _) }

theorem thirdK_quotient_radical_eq_bot
    (z : G) :
    CFSG.solvableRadical (thirdK D z ⧸ CFSG.solvableRadical (thirdK D z)) = ⊥ := by
  exact OddTransp.eq_bot_of_quotient_solvableRadical (CFSG.solvableRadical _)
    inferInstance OddTransp.isSolvable_solvableRadical

theorem commute_of_commute_mk_of_ne (hS : Setup G D) {z : G} {a b : thirdK D z}
    (ha : a ∈ DeltaK D z) (hb : b ∈ DeltaK D z)
    (hcomm : Commute (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D z)) a)
      (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D z)) b))
    (hne : QuotientGroup.mk' (CFSG.solvableRadical (thirdK D z)) a ≠
      QuotientGroup.mk' (CFSG.solvableRadical (thirdK D z)) b) : Commute a b := by
  by_contra hnc
  have hodd : Odd (orderOf (a * b)) :=
    (DeltaK_isOddTransp hS z).odd_of_not_commute ha hb hnc
  exact hne (eq_of_commute_of_odd (DeltaK_isOddTransp hS z) ha hb hcomm hodd)

theorem localSecond_quotient_class (hS : Setup G D) (hL : LocalSecond D) {e : G}
    (hclass : ∃ d₀ : thirdK D e, DeltaK D e = {x | IsConj d₀ x})
    (hne : ∀ x ∈ DeltaK D e,
      QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) x ≠ 1) :
    LocalSecond (DeltaBar D e) := by
  classical
  let K : Subgroup G := thirdK D e
  let R : Subgroup K := CFSG.solvableRadical K
  let mk := QuotientGroup.mk' R
  obtain ⟨d₀, hclass'⟩ := hclass
  have hsetup : Setup (K ⧸ R) (DeltaBar D e) :=
    { isClass := image_isClass_quotient hclass' R
      oddT := image_isOddTransp_quotient R (DeltaK_isOddTransp hS e) hne
      gen := image_closure_eq_top_quotient R (DeltaK_closure_eq_top e) }
  intro d hd x y t hxd hyd htd htri'
  obtain ⟨d0, hd0K, rfl⟩ := hd
  obtain ⟨x0, hx0K, rfl⟩ := htri'.1
  obtain ⟨t0, ht0K, rfl⟩ := htri'.2.1
  obtain ⟨y0, hy0K, rfl⟩ := htri'.2.2.1
  have hx0D : (x0 : G) ∈ D := (mem_Delta_iff.mp hx0K).1
  have ht0D : (t0 : G) ∈ D := (mem_Delta_iff.mp ht0K).1
  have hy0D : (y0 : G) ∈ D := (mem_Delta_iff.mp hy0K).1
  have hd0D : (d0 : G) ∈ D := (mem_Delta_iff.mp hd0K).1
  have hxne : mk x0 ≠ mk d0 := by
    intro hEq
    apply htri'.2.2.2.2.2.1
    have h := hyd
    rw [← hEq] at h
    exact h.symm
  have hyne : mk y0 ≠ mk d0 := by
    intro hEq
    apply htri'.2.2.2.2.2.1
    have h := hxd
    rw [← hEq] at h
    exact h
  have htne : mk t0 ≠ mk d0 := by
    intro hEq
    apply htri'.2.2.2.2.2.2
    have h := hyd
    rw [← hEq] at h
    exact h.symm
  have hxtne : mk x0 ≠ mk t0 := by
    intro hEq
    exact htri'.2.2.2.1 hEq
  have hxd' : Commute x0 d0 := commute_of_commute_mk_of_ne hS hx0K hd0K hxd hxne
  have hyd' : Commute y0 d0 := commute_of_commute_mk_of_ne hS hy0K hd0K hyd hyne
  have htd' : Commute t0 d0 := commute_of_commute_mk_of_ne hS ht0K hd0K htd htne
  have hxt' : Commute x0 t0 :=
    commute_of_commute_mk_of_ne hS hx0K ht0K htri'.2.2.2.2.1 hxtne
  have htri0 : IsTriangle D (x0 : G) (y0 : G) (t0 : G) := by
    have hcommK : ∀ {a b : K}, Commute (a : G) (b : G) → Commute a b :=
      fun hc => (commute_iff_eq _ _).mpr (Subtype.ext hc.eq)
    refine ⟨hx0D, ht0D, hy0D, ?_, hxt'.map K.subtype, ?_, ?_⟩
    · intro h
      exact htri'.2.2.2.1 (congrArg mk (Subtype.ext h))
    · intro hc
      exact htri'.2.2.2.2.2.1 ((hcommK hc).map mk)
    · intro hc
      exact htri'.2.2.2.2.2.2 ((hcommK hc).map mk)
  have h4G : orderOf ((x0 : G) * (t0 : G) * (y0 : G)) = 4 :=
    hL d0 hd0D (x0 : G) (y0 : G) (t0 : G)
      (hxd'.map K.subtype) (hyd'.map K.subtype) (htd'.map K.subtype) htri0
  have h4 : orderOf (x0 * t0 * y0 : K) = 4 := by
    rw [← Subgroup.orderOf_coe]
    simpa only [Subgroup.coe_mul] using h4G
  have hdvd : orderOf (mk x0 * mk t0 * mk y0) ∣ 4 := by
    have h := orderOf_map_dvd mk (x0 * t0 * y0)
    rw [show mk (x0 * t0 * y0) = mk x0 * mk t0 * mk y0 by simp only [map_mul]] at h
    rwa [h4] at h
  have hcases := IsTriangle.orderOf_cases hsetup.oddT hsetup.normal htri'
  rcases hcases with ⟨hodd, hgt⟩ | h4' | ⟨m, hmodd, hm1, hm⟩
  · exfalso
    set o : ℕ := orderOf (mk x0 * mk t0 * mk y0) with ho
    have ho4 : o ≤ 4 := by rw [ho]; exact Nat.le_of_dvd (by norm_num) hdvd
    have ho0 : 0 < o := by rw [ho]; exact orderOf_pos _
    have hodd' : Odd o := by rw [ho]; exact hodd
    have hdvd' : o ∣ 4 := by rw [ho]; exact hdvd
    interval_cases o
    · rcases hodd' with ⟨k, hk⟩; omega
    · rcases hdvd' with ⟨c, hc⟩; omega
    · rcases hodd' with ⟨k, hk⟩; omega
  · exact h4'
  · exfalso
    have hm2 : m ∣ 2 := by
      have h := hdvd
      rw [hm] at h
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h
    have hmle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
    interval_cases m
    · rcases hmodd with ⟨k, hk⟩; omega

theorem localSecond_DeltaBar (hS : Setup G D) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n) :
    LocalSecond (DeltaBar D ((u * v * w) ^ n)) :=
  localSecond_quotient_class hS hL (DeltaK_class hS hL htri hn hord)
    (DeltaK_mk_ne_one hS hL htri hn hn1 hord)

theorem thirdK_le_thirdK_of_le_centralizer {z e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G)) :
    thirdK D z ≤ thirdK D e := by
  rw [thirdK, Subgroup.closure_le]
  intro x hx
  exact Delta_subset_thirdK (mem_Delta_iff.mpr
    ⟨(mem_Delta_iff.mp hx).1,
      Subgroup.mem_centralizer_singleton_iff.mp (hzK (Delta_subset_thirdK hx))⟩)

theorem thirdK_map_quotient_injective {z e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (h9 : (thirdK D z).subgroupOf (thirdK D e) ⊓
      CFSG.solvableRadical (thirdK D e) = ⊥) :
    Function.Injective (fun x : thirdK D z =>
      (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
        ⟨x, thirdK_le_thirdK_of_le_centralizer hzK x.2⟩) := by
  intro a b hab
  have hKY := thirdK_le_thirdK_of_le_centralizer (D := D) (z := z) (e := e) hzK
  have hR : ((⟨a, hKY a.2⟩ : thirdK D e)⁻¹ * ⟨b, hKY b.2⟩) ∈
      CFSG.solvableRadical (thirdK D e) :=
    (QuotientGroup.eq_one_iff _).mp (by
      change (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
        ((⟨a, hKY a.2⟩ : thirdK D e)⁻¹ * ⟨b, hKY b.2⟩) = 1
      rw [map_mul, map_inv]
      exact (congrArg (fun z => z⁻¹ *
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e))) ⟨b, hKY b.2⟩) hab).trans
        (inv_mul_cancel _))
  have hmem' : ((⟨a, hKY a.2⟩ : thirdK D e)⁻¹ * ⟨b, hKY b.2⟩) ∈
      (thirdK D z).subgroupOf (thirdK D e) ⊓ CFSG.solvableRadical (thirdK D e) :=
    ⟨Subgroup.mem_subgroupOf.mpr (by
      simpa using (thirdK D z).mul_mem ((thirdK D z).inv_mem a.2) b.2), hR⟩
  rw [h9, Subgroup.mem_bot] at hmem'
  have h1 : (a : G)⁻¹ * (b : G) = 1 := by
    have := congrArg Subtype.val hmem'
    simpa using this
  exact Subtype.ext (inv_mul_eq_one.mp h1)

theorem orderOf_thirdK_map_quotient {z e : G}
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (h9 : (thirdK D z).subgroupOf (thirdK D e) ⊓
      CFSG.solvableRadical (thirdK D e) = ⊥) (x : thirdK D z) :
    orderOf ((QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
        ⟨x, thirdK_le_thirdK_of_le_centralizer hzK x.2⟩) = orderOf x := by
  let f : thirdK D z →* (thirdK D e ⧸ CFSG.solvableRadical (thirdK D e)) :=
    { toFun := fun x => (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
        ⟨x, thirdK_le_thirdK_of_le_centralizer hzK x.2⟩
      map_one' := map_one (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
      map_mul' := fun x y => by
        simpa using map_mul (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)))
          ⟨x, thirdK_le_thirdK_of_le_centralizer hzK x.2⟩
          ⟨y, thirdK_le_thirdK_of_le_centralizer hzK y.2⟩ }
  have hf : Function.Injective f := thirdK_map_quotient_injective hzK h9
  simpa [f] using orderOf_injective f hf x

end CFSG.OddTranspositions

