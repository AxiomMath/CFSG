module

public import CFSG.OddTranspositions.FourEightBase
public import CFSG.OddTranspositions.DeltaCentSet
public import CFSG.OddTranspositions.TheoremTwo.ConfigSylow
public import CFSG.OddTranspositions.TheoremTwo.ConfigAltFive
public import CFSG.OddTranspositions.TheoremTwo.DerivedLocal

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem conj_mem_localGroup_of_commute (hS : Setup G D) {z g x : G} (hgz : Commute g z)
    (hx : x ∈ localGroup D z) : g * x * g⁻¹ ∈ localGroup D z := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    exact mem_localGroup_of_mem ⟨hS.normal g y hy.1, (hgz.mul_left hy.2).mul_left hgz.inv_left⟩
  | one => simp
  | mul x y _ _ hx hy =>
    rw [show g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ hx

omit [Finite G] in
theorem map_conj_localGroup (hS : Setup G D) {z g : G} (hgz : Commute g z) :
    (localGroup D z).map (MulAut.conj g).toMonoidHom = localGroup D z := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact conj_mem_localGroup_of_commute hS hgz hx
  · intro x hx
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, conj_mem_localGroup_of_commute hS hgz.inv_left hx, ?_⟩
    change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
    group

omit [Finite G] in
theorem mem_normalizer_derivedLocal (hS : Setup G D) {z g : G} (hgz : Commute g z) :
    g ∈ Subgroup.normalizer (derivedLocal D z : Set G) := by
  have hd : derivedLocal D z = ⁅localGroup D z, localGroup D z⁆ :=
    Subgroup.map_subtype_commutator _
  have hconj : ∀ {g : G}, Commute g z → ∀ x ∈ derivedLocal D z,
      g * x * g⁻¹ ∈ derivedLocal D z := by
    intro g hgz x hx
    rw [hd] at hx ⊢
    have h := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx
    rw [Subgroup.map_commutator, map_conj_localGroup hS hgz] at h
    exact h
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨hconj hgz x, fun hx => ?_⟩
  have h := hconj hgz.inv_left _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h

theorem localGroup_transitive (hS : Setup G D) (hL : LocalSecond D) {u w v : G}
    (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (hord : orderOf (u * v * w) = 2 * n) :
    ∀ x ∈ centSet D ((u * v * w) ^ n), ∀ y ∈ centSet D ((u * v * w) ^ n),
      ∃ h ∈ localGroup D ((u * v * w) ^ n), h * x * h⁻¹ = y := by
  intro x hx y hy
  rw [← Delta_eq_centSet] at hx hy
  obtain ⟨k₁, hk₁, rfl⟩ := thirdK_transitive hS hL htri hn hord x hx
  obtain ⟨k₂, hk₂, rfl⟩ := thirdK_transitive hS hL htri hn hord y hy
  rw [thirdK_eq_localGroup] at hk₁ hk₂
  exact ⟨k₂ * k₁⁻¹, Subgroup.mul_mem _ hk₂ (Subgroup.inv_mem _ hk₁), by group⟩

omit [Finite G] in
theorem not_isConj_mul_of_transitive (hS : Setup G D) {z u v : G} (hu : u ∈ centSet D z)
    (hv : v ∈ centSet D z) (huv : u ≠ v)
    (htrans : ∀ x ∈ centSet D z, ∀ y ∈ centSet D z, ∃ h ∈ localGroup D z, h * x * h⁻¹ = y)
    {r s : G} (hr : r ∈ D) (hs : s ∈ D) (hrs : r ≠ s) (hcrs : Commute r s) :
    ¬ IsConj z (r * s) := by
  intro h
  obtain ⟨y, hy⟩ := isConj_iff.mp h
  have hr' : y⁻¹ * r * y ∈ D := by simpa using hS.normal y⁻¹ r hr
  have hs' : y⁻¹ * s * y ∈ D := by simpa using hS.normal y⁻¹ s hs
  have hc' := hcrs.conj y⁻¹
  rw [inv_inv] at hc'
  refine ne_mul_of_transitive hS hu hv huv htrans hr' hs' (fun h' => hrs ?_) hc' ?_
  · exact mul_left_cancel (mul_right_cancel h')
  · calc z = y⁻¹ * (y * z * y⁻¹) * y := by group
      _ = y⁻¹ * r * y * (y⁻¹ * s * y) := by rw [hy]; group

theorem exists_config_of_alt5 (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hL : LocalSecond D)
    {u w v : G} (htri : IsTriangle D u w v) {n : ℕ} (hn : Odd n) (h1n : 1 < n)
    (hord : orderOf (u * v * w) = 2 * n)
    (hB : CFSG.BenderSuzuki.IsBenderGroup (thirdK D ((u * v * w) ^ n) ⧸
      CFSG.solvableRadical (thirdK D ((u * v * w) ^ n))))
    (hQ : CFSG.pCore 2 (thirdK D ((u * v * w) ^ n)) ≤
      Subgroup.center (thirdK D ((u * v * w) ^ n)))
    (hA5 : ∀ K₁ S' : Subgroup G, commutator K₁ = ⊤ → Odd (Nat.card (Subgroup.center K₁)) →
      CFSG.BenderSuzuki.IsBenderGroup (K₁ ⧸ Subgroup.center K₁) →
      (IsPGroup 2 S' ∧ ∀ P : Subgroup G, IsPGroup 2 P → S' ≤ P → P = S') →
      S' ≤ Subgroup.normalizer (K₁ : Set G) → ∀ a : G, a * a = 1 → a ∈ S' →
      (∀ t ∈ S' ⊓ K₁, ∀ t' ∈ S' ⊓ K₁, (∀ s ∈ S' ⊓ K₁, Commute t s) →
        (∀ s ∈ S' ⊓ K₁, Commute t' s) → t * t = 1 → t' * t' = 1 → Commute a t →
        Commute a t' → t ≠ 1 → t' ≠ 1 → t = t') →
      Nonempty (K₁ ≃* alternatingGroup (Fin 5)) ∧
        ¬ ∃ k ∈ K₁, ∀ x ∈ K₁, a * x * a⁻¹ = k * x * k⁻¹) :
    ∃ (a : G) (K₁ S' : Subgroup G), Config D u w v ((u * v * w) ^ n) a K₁ S' := by
  classical
  obtain ⟨hz2, hz1, hzu, hzv, hzw, huvz⟩ := IsTriangle.third_kind hS.oddT hS.normal htri hn hord
  have hzD := thirdInv_not_mem hS hL htri hn hord
  have htrans := localGroup_transitive hS hL htri hn hord
  set z := (u * v * w) ^ n with hzdef
  rw [thirdK_eq_localGroup] at hB hQ
  have hu2 : u * u = 1 := hS.oddT.mul_self_eq_one htri.1
  have hv2 : v * v = 1 := hS.oddT.mul_self_eq_one htri.2.1
  have hu : u ∈ centSet D z := ⟨htri.1, hzu.symm⟩
  have hv : v ∈ centSet D z := ⟨htri.2.1, hzv.symm⟩
  have huv : u ≠ v := htri.2.2.2.1
  have hc : Commute u v := htri.2.2.2.2.1
  obtain ⟨hKeq, hzK, hdelta, hperf, hodd, hB₁⟩ :=
    derivedLocal_structure hS hz1 hu hv huv hc huvz htrans hQ hB
  have hinv := mul_mem_centSet_of_mem_derivedLocal hS hz1 hu hv huv hc huvz htrans hQ hB
  obtain ⟨S, a, hzS, hSz, haS, -, haconj, haa, hau, hfixD⟩ :=
    exists_sylow_conj_data hS hrad hz1 hzD hu hv huv hc huvz htrans hQ hB
  set K₁ := derivedLocal D z with hK₁def
  have haz : Commute a z := hSz a haS
  have hK₁H : K₁ ≤ localGroup D z := by rw [hKeq]; exact le_sup_left
  have hK₁z : ∀ x ∈ K₁, Commute x z := fun x hx => commute_of_mem_localGroup (hK₁H hx)
  have hnorm : ∀ g : G, Commute g z → g ∈ Subgroup.normalizer (K₁ : Set G) :=
    fun g hg => mem_normalizer_derivedLocal hS hg
  have hSyl : IsPGroup 2 (S : Subgroup G) ∧
      ∀ P : Subgroup G, IsPGroup 2 P → (S : Subgroup G) ≤ P → P = S :=
    ⟨S.isPGroup', fun P hP hle => S.is_maximal' hP hle⟩
  have hfixT : ∀ t ∈ (S : Subgroup G) ⊓ K₁, ∀ t' ∈ (S : Subgroup G) ⊓ K₁,
      (∀ s ∈ (S : Subgroup G) ⊓ K₁, Commute t s) →
      (∀ s ∈ (S : Subgroup G) ⊓ K₁, Commute t' s) → t * t = 1 → t' * t' = 1 →
      Commute a t → Commute a t' → t ≠ 1 → t' ≠ 1 → t = t' := by
    intro t ht t' ht' _ _ htt ht't hat hat' ht1 ht'1
    rw [Subgroup.mem_inf] at ht ht'
    by_contra hne
    exact hfixD ⟨z * t, ⟨(hinv t ht.2 htt ht1).1, S.mul_mem hzS ht.1⟩, z * t',
      ⟨(hinv t' ht'.2 ht't ht'1).1, S.mul_mem hzS ht'.1⟩, fun h => hne (mul_left_cancel h),
      haz.mul_right hat, haz.mul_right hat'⟩
  obtain ⟨⟨e⟩, hout⟩ := hA5 K₁ S hperf hodd hB₁ hSyl (fun s hs => hnorm s (hSz s hs)) a haa
    haS hfixT
  have haN := hnorm a haz
  have hkK : z * u ∈ K₁ := hdelta u hu
  have hkk : z * u * (z * u) = 1 := by
    rw [show z * u * (z * u) = z * (u * z) * u by group, ← hzu.eq,
      show z * (z * u) * u = z * z * (u * u) by group, hz2, hu2, one_mul]
  have hk1 : z * u ≠ 1 := fun h => hzD (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hu2]
    exact htri.1)
  obtain ⟨⟨k', hk'K, hk'k, hak', hord3⟩, h, hhK, hh⟩ :=
    exists_pair_and_twist_of_outer e haa haN hout hkK hkk hk1 (haz.mul_right hau)
  have hk'1 : k' ≠ 1 := by
    rintro rfl
    rw [mul_one] at hord3
    have h2 : orderOf (z * u) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hkk])
    rw [hord3] at h2
    omega
  have hhz : Commute h z := hK₁z h hhK
  have hconj1 : h * (a * u) * h⁻¹ = a * z := by
    have hau' : z * (a * (z * u)) = a * u := by
      calc z * (a * (z * u)) = z * (a * z) * u := by group
        _ = z * (z * a) * u := by rw [haz.eq]
        _ = z * z * (a * u) := by group
        _ = a * u := by rw [hz2, one_mul]
    calc h * (a * u) * h⁻¹ = h * (z * (a * (z * u))) * h⁻¹ := by rw [hau']
      _ = h * z * h⁻¹ * (h * (a * (z * u)) * h⁻¹) := by group
      _ = z * a := by rw [hh, hhz.eq, mul_inv_cancel_right]
      _ = a * z := haz.eq.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp haconj
  have hxC : g⁻¹ * u * g ∈ centSet D z := by
    refine ⟨by simpa using hS.normal g⁻¹ u htri.1, ?_⟩
    have h1 := hau.symm.conj g⁻¹
    rw [inv_inv, ← hg, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h1
    exact h1
  obtain ⟨c, hcK, hcu⟩ := htrans u hu _ hxC
  have hcz : Commute c z := commute_of_mem_localGroup hcK
  have hvb : v * (u * v * z) = z * u := by
    calc v * (u * v * z) = v * u * v * z := by group
      _ = u * v * v * z := by rw [← hc.eq]
      _ = u * (v * v) * z := by group
      _ = z * u := by rw [hv2, mul_one, hzu.eq]
  have hau_eq : a * u = g * c * v * (g * c)⁻¹ * (g * c * (u * v * z) * (g * c)⁻¹) := by
    calc a * u = g * z * g⁻¹ * u := by rw [hg]
      _ = g * (z * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * (z * c * u * c⁻¹) * g⁻¹ := by rw [← hcu]; group
      _ = g * (c * z * u * c⁻¹) * g⁻¹ := by rw [hcz.eq]
      _ = g * c * (v * (u * v * z)) * (g * c)⁻¹ := by rw [hvb]; group
      _ = g * c * v * (g * c)⁻¹ * (g * c * (u * v * z) * (g * c)⁻¹) := by group
  have hvne : v ≠ u * v * z := fun h' => hzD (by
    have h1 : u * z = 1 := by
      have h2 : v * (u * z) = v * 1 := by
        rw [mul_one, ← mul_assoc, ← hc.eq]; exact h'.symm
      exact mul_left_cancel h2
    rw [eq_inv_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right hu2]
    exact htri.1)
  have hcv : Commute v (u * v * z) := (hc.symm.mul_right (Commute.refl v)).mul_right hzv.symm
  refine ⟨a, K₁, S, ⟨hS, hrad, hL, ?_, htri, ⟨n, hn, h1n, hord, rfl⟩, ?_, ⟨e⟩, ?_, hSyl,
    ⟨hzS, fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hSz s hs).eq⟩, haconj,
    haS, haN, hout, hau, ?_, fun d hd => hdelta d (mem_Delta_iff.mp hd), ?_⟩⟩
  · exact hrad (Subgroup.center G) inferInstance
      (Group.isSolvable_of_comm fun x y => Subtype.ext (Subgroup.mem_center_iff.mp y.2 x))
  · rw [thirdK_eq_localGroup, hKeq]
  · exact fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hK₁z x hx).eq
  ·
    intro hconj2
    have hz' : IsConj z (a * u) := haconj.trans (hconj2.trans (isConj_iff.mpr ⟨h, hconj1⟩).symm)
    rw [hau_eq] at hz'
    exact not_isConj_mul_of_transitive hS hu hv huv htrans (hS.normal _ v htri.2.1)
      (hS.normal _ _ huvz) (fun h' => hvne (mul_left_cancel (mul_right_cancel h')))
      (hcv.conj (g * c)) hz'
  ·
    refine ⟨z * k', mem_Delta_iff.mpr (hinv k' hk'K hk'k hk'1), (haz.mul_right hak').symm, ?_⟩
    rw [show u * (z * k') = z * u * k' by rw [← mul_assoc, ← hzu.eq]]
    exact hord3

end CFSG.OddTranspositions

end
