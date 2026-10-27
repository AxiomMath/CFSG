module

public import CFSG.Quasithin.Vol2.Ch10SecB3Comm

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13
open scoped IsMulCommutative

theorem eq_two_of_dvd {m n : ℕ} (hm : 2 ≤ m) (h : 2 ^ m - 1 ∣ 2 ^ n + 1) : m = 2 := by
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hmod : 2 ^ m ≡ 1 [MOD 2 ^ m - 1] := ((Nat.modEq_iff_dvd' h1).mpr dvd_rfl).symm
  have hn : 2 ^ n = (2 ^ m) ^ (n / m) * 2 ^ (n % m) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : 2 ^ n ≡ 2 ^ (n % m) [MOD 2 ^ m - 1] := by
    rw [hn]
    have := (hmod.pow (n / m)).mul_right (2 ^ (n % m))
    simpa using this
  have h3 : 2 ^ m - 1 ∣ 2 ^ (n % m) + 1 :=
    (Nat.modEq_zero_iff_dvd.mp ((h2.add_right 1).symm.trans (Nat.modEq_zero_iff_dvd.mpr h)))
  have h4 : 2 ^ m - 1 ≤ 2 ^ (n % m) + 1 := Nat.le_of_dvd (by positivity) h3
  have h5 : 2 ^ (n % m) ≤ 2 ^ (m - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := Nat.mod_lt n (by omega : 0 < m); omega)
  have h6 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h7 : 2 ^ (m - 1) ≤ 2 := by omega
  have h8 : m - 1 ≤ 1 := by
    by_contra h9
    have : 2 ^ 2 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  omega

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuCVM_eq_bot_of_comm (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) :
    fsuCVM T L I = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hVT := SecA.fsuVM_le_T hyp
  have hCT : fsuCVM T L I ≤ T := inf_le_left.trans hVT
  have hTN : T ≤ Subgroup.normalizer (fsuCVM T L I : Set G) := by
    intro s hs
    have hsM := SecA.le_fsuM T L hs
    have h1 := SecA.fsuM_le_normalizer_fsuVM T L I hsM
    have h2 := SecA.le_normalizer_centralizer (le_refl (fsuM T L)) hsM
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have hn : ((fsuCVM T L I).subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCT).mpr hTN
  have hnil : Group.IsNilpotent ↥T := hyp.fsu.sylow.1.isNilpotent
  have hne' : (fsuCVM T L I).subgroupOf T ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro v hv
    have : (⟨v, hCT hv⟩ : ↥T) ∈ (fsuCVM T L I).subgroupOf T := hv
    rw [h, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  obtain ⟨⟨x, hxC, hxZ⟩, hx1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  set c : G := (x : G) with hc
  have hc1 : c ≠ 1 := fun h => hx1 (Subtype.ext (Subtype.ext h))
  have hcV : c ∈ fsuVM T L I := hxC.1
  have hcL0 : c ∈ Subgroup.centralizer (fsuL0 T L : Set G) := hxC.2
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hxZ) ⟨s, hs⟩)
  have hc2 : c ^ 2 = 1 := (SecA.isElemAbelian_fsuVM hyp).2 c hcV
  have hcp : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hc2 hc1, pow_one])
  obtain ⟨M', hM'⟩ := exists_inM_centralizer hcp hc1
  have hcZ : c ∈ quasithinOmegaOneCenter T := Subgroup.subset_closure ⟨⟨hVT hcV, hcT⟩, hc2⟩
  have hcH := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH) hcZ
  have hmem : ∀ {X : Subgroup G}, c ∈ Subgroup.centralizer (X : Set G) →
      X ≤ Subgroup.centralizer ({c} : Set G) := by
    intro X hX y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.mp hX y hy).symm
  have hM : M' = fsuM T L := (isUniqueM_L0T h331 hyp).2 M'
    ⟨hM'.1, (sup_le (hmem hcL0) (hmem hcT)).trans hM'.2⟩
  exact hH.2.1 ((hmem hcH).trans (hM ▸ hM'.2))

theorem fix_of_comm (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1011 : Stmt10_1_1) (hyp : Hyp10 G T L I) (hCV : fsuCVM T L I = ⊥) {H : Subgroup G}
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥) {g : G} (hgH : g ∈ H)
    (hgL : g ∈ Subgroup.normalizer (L : Set G))
    (hgV : g ∈ Subgroup.normalizer (fsuVM T L I : Set G)) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G))
    (hgLt : g ∈ Subgroup.normalizer (CFSG.conjugate L t : Set G)) {u : G}
    (hu : u ∈ fsuUL T L I) (huT : ∀ s ∈ T1 T L, s * u * s⁻¹ = u) : g * u * g⁻¹ = u := by
  set V := fsuVM T L I with hVdef
  set U' := ⁅V, CFSG.conjugate L t⁆ with hU'def
  have hel := SecA.isElemAbelian_fsuVM hyp
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUV : fsuUL T L I ≤ V := fsuUL_le' T L I
  have htM := SecA.le_fsuM T L ht
  have htV : t ∈ Subgroup.normalizer (V : Set G) := SecA.le_normalizer_fsuVM T L I ht
  have htn' : t⁻¹ ∉ Subgroup.normalizer (L : Set G) := fun h =>
    htn (by simpa using (Subgroup.normalizer _).inv_mem h)
  have hLt' : CFSG.conjugate L t⁻¹ = CFSG.conjugate L t :=
    SecA.conjugate_eq_of_not_mem h37 h38 hyp ht htn (T.inv_mem ht) htn'
  have htu : t * u * t⁻¹ ∈ U' := by
    have h := SecA.conjugate_commutator_fsuVM (I := I) ((fsuM T L).inv_mem htM)
    rw [hLt'] at h
    rw [hU'def, ← h, SecA.mem_conjugate_iff]
    simpa [mul_assoc] using hu
  have huV := hUV hu
  have htuV : t * u * t⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp htV u).mp huV
  have hT1 : ∀ s ∈ T1 T L, s * (u * (t * u * t⁻¹)) * s⁻¹ = u * (t * u * t⁻¹) := by
    intro s hs
    have hs' : t⁻¹ * s * t⁻¹⁻¹ ∈ T1 T L :=
      (Subgroup.mem_normalizer_iff.mp (T1_normal h37 h38 hyp (T.inv_mem ht)) s).mp hs
    have h1 := huT s hs
    have h2 := huT _ hs'
    calc s * (u * (t * u * t⁻¹)) * s⁻¹
        = (s * u * s⁻¹) * (t * ((t⁻¹ * s * t⁻¹⁻¹) * u * (t⁻¹ * s * t⁻¹⁻¹)⁻¹) * t⁻¹) := by group
      _ = u * (t * u * t⁻¹) := by rw [h1, h2]
  have hvT : ∀ s ∈ T, s * (u * (t * u * t⁻¹)) * s⁻¹ = u * (t * u * t⁻¹) := by
    intro s hs
    by_cases hsL : s ∈ Subgroup.normalizer (L : Set G)
    · exact hT1 s ⟨hs, hsL⟩
    · have hst : s * t⁻¹ ∈ T1 T L := ⟨T.mul_mem hs (T.inv_mem ht),
        SecA.mul_inv_mem_normalizer_of_conjugate_eq
          (SecA.conjugate_eq_of_not_mem h37 h38 hyp ht htn hs hsL)⟩
      have ht2 : t * t ∈ T1 T L :=
        ⟨T.mul_mem ht ht, SecA.mul_self_mem_normalizer h37 h38 hyp ht htn⟩
      have h1 := huT _ ht2
      have htv : t * (u * (t * u * t⁻¹)) * t⁻¹ = u * (t * u * t⁻¹) := by
        calc t * (u * (t * u * t⁻¹)) * t⁻¹ = (t * u * t⁻¹) * ((t * t) * u * (t * t)⁻¹) := by
              group
          _ = (t * u * t⁻¹) * u := by rw [h1]
          _ = u * (t * u * t⁻¹) := hcomm _ htuV _ huV
      calc s * (u * (t * u * t⁻¹)) * s⁻¹
          = (s * t⁻¹) * (t * (u * (t * u * t⁻¹)) * t⁻¹) * (s * t⁻¹)⁻¹ := by group
        _ = u * (t * u * t⁻¹) := by rw [htv, hT1 _ hst]
  have hvV : u * (t * u * t⁻¹) ∈ V := V.mul_mem huV htuV
  have hvZ : u * (t * u * t⁻¹) ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨SecA.fsuVM_le_T hyp hvV,
      Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩, hel.2 _ hvV⟩
    have := hvT s hs
    calc s * (u * (t * u * t⁻¹)) = s * (u * (t * u * t⁻¹)) * s⁻¹ * s := by group
      _ = u * (t * u * t⁻¹) * s := by rw [this]
  have hgv : g * (u * (t * u * t⁻¹)) * g⁻¹ = u * (t * u * t⁻¹) := by
    have h := Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hZH) hvZ) g hgH
    rw [h, mul_inv_cancel_right]
  have hgU : g * u * g⁻¹ ∈ fsuUL T L I :=
    (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator
      (Subgroup.zpowers_le.mpr hgV) (Subgroup.zpowers_le.mpr hgL) (Subgroup.mem_zpowers g)) u).mp hu
  have hgU' : g * (t * u * t⁻¹) * g⁻¹ ∈ U' :=
    (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator
      (Subgroup.zpowers_le.mpr hgV) (Subgroup.zpowers_le.mpr hgLt) (Subgroup.mem_zpowers g)) _).mp
      htu
  obtain ⟨-, -, -, hinf⟩ := (h1011 G T L I hyp).2.2.1 t ht htn
  rw [hCV, sup_bot_eq, sup_bot_eq] at hinf
  have hgUV := hUV hgU
  have hgU'V : g * (t * u * t⁻¹) * g⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp hgV _).mp htuV
  have key : g * u * g⁻¹ * u⁻¹ = t * u * t⁻¹ * (g * (t * u * t⁻¹) * g⁻¹)⁻¹ := by
    have e : g * (u * (t * u * t⁻¹)) * g⁻¹ = (g * u * g⁻¹) * (g * (t * u * t⁻¹) * g⁻¹) := by group
    rw [e] at hgv
    calc g * u * g⁻¹ * u⁻¹
        = (g * u * g⁻¹) * (g * (t * u * t⁻¹) * g⁻¹) * (g * (t * u * t⁻¹) * g⁻¹)⁻¹ * u⁻¹ := by
          group
      _ = u * (t * u * t⁻¹) * (g * (t * u * t⁻¹) * g⁻¹)⁻¹ * u⁻¹ := by rw [hgv]
      _ = u⁻¹ * (u * (t * u * t⁻¹) * (g * (t * u * t⁻¹) * g⁻¹)⁻¹) := by
          rw [hcomm _ (V.mul_mem (V.mul_mem huV htuV) (V.inv_mem hgU'V)) _ (V.inv_mem huV)]
      _ = t * u * t⁻¹ * (g * (t * u * t⁻¹) * g⁻¹)⁻¹ := by group
  have hmem : g * u * g⁻¹ * u⁻¹ ∈ fsuUL T L I ⊓ U' :=
    ⟨(fsuUL T L I).mul_mem hgU ((fsuUL T L I).inv_mem hu),
      key ▸ U'.mul_mem htu (U'.inv_mem hgU')⟩
  rw [hinf, Subgroup.mem_bot] at hmem
  calc g * u * g⁻¹ = g * u * g⁻¹ * u⁻¹ * u := by group
    _ = u := by rw [hmem, one_mul]

end CFSG.Quasithin.Vol2.Ch10.SecB
