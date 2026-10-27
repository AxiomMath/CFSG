module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65InversionG2General

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley CFSG.AGLEmbedding.KFactProofs.G2Q

theorem g2_exists_sylow_weakClosure_data
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    ∃ (Q0 : Subgroup (adjointGroup .G2 K)) (z0 : ↥Q0),
      (∃ P : Sylow 3 (adjointGroup .G2 K), (P : Subgroup (adjointGroup .G2 K)) = Q0) ∧
      Subgroup.center ↥Q0 = Subgroup.zpowers z0 ∧
      orderOf (z0 : adjointGroup .G2 K) = 3 ∧
      ∃ (L : Type) (_ : Field L) (φ : adjointGroup .G2 K →* ModGL .G2 L) (g : ModGL .G2 L)
        (ω : Lˣ) (m : ℕ) (hω1 : ω ≠ 1),
        Function.Injective φ ∧ (3 : L) ≠ 0 ∧ ω ^ 3 = 1 ∧
        Q0.map φ = (extSub (ext3_tzPart (L := L) (m := m) hω1)).map (MulAut.conj g).toMonoidHom ∧
        φ z0 = g * tz 1 ω⁻¹ * g⁻¹ :=
  open CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups Subgroup in by
  classical
  let q := Nat.card K
  let b := padicValNat 3 (q ^ 2 - 1)
  have hq2 : 2 ≤ q := by omega
  have hb1 : 1 ≤ b := one_le_padicValNat_three_sq_sub_one (q := q) h3 hq2
  have hb0 : 3 ^ b ≠ 0 := pow_ne_zero b (by norm_num)
  have hbpos : 0 < b := by omega
  have h3b1 : 1 < 3 ^ b := one_lt_pow' (by norm_num) (by omega)
  have h3bdvd : 3 ∣ 3 ^ b := by
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ b = 3 * c := by
      refine ⟨3 ^ (b - 1), ?_⟩
      have hb : b = (b - 1) + 1 := by omega
      calc 3 ^ b = 3 ^ ((b - 1) + 1) := congrArg (fun n => 3 ^ n) hb
        _ = 3 ^ (b - 1) * 3 := pow_succ _ _
        _ = 3 * 3 ^ (b - 1) := by ring
    exact ⟨c, hc⟩
  let L := AlgebraicClosure K
  have h3K : (3 : K) ≠ 0 := by
    intro h
    apply h3
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have hp3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by exact_mod_cast h))
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hqe, hp3]
    exact dvd_pow_self 3 e.ne_zero
  have h3L : (3 : L) ≠ 0 := by
    intro h
    apply h3K
    have h' : (algebraMap K L) (3 : K) = 0 := by
      rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, map_natCast]
      exact h
    exact (algebraMap K L).injective (h'.trans (map_zero _).symm)
  have : NeZero ((3 : ℕ) : L) := ⟨h3L⟩
  have : NeZero ((3 ^ b : ℕ) : L) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero b h3L⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3 ^ b)
  let ζu : Lˣ := (hζ.isUnit hb0).unit
  have hζu : IsPrimitiveRoot (ζu : L) (3 ^ b) := by simpa [ζu] using hζ
  have hζu_ne1 : ζu ≠ 1 := fun h => hζu.ne_one h3b1 (congrArg Units.val h)
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  let ωu : Lˣ := (hω.isUnit (by norm_num)).unit
  have hωu : IsPrimitiveRoot (ωu : L) 3 := by simpa [ωu] using hω
  have hωu3 : ωu ^ 3 = 1 := Units.ext (by simpa [ωu] using hω.pow_eq_one)
  have hωu1 : ωu ≠ 1 := fun h => hωu.ne_one (by norm_num) (congrArg Units.val h)
  obtain ⟨F, hF, hTW⟩ := exists_rational_conj_fixed K
  let n : ModGL .G2 L := if q % 3 = 1 then 1 else nw0
  have hn_mem : n ∈ adjointGroup .G2 L := by
    by_cases hmod : q % 3 = 1
    · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; exact one_mem _
    · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; exact nw0_mem_adjointGroup
  have hn_y : n * Units.map (entrywiseHom F) (yq : ModGL .G2 L) * n⁻¹ = yq := by
    rw [frob_yq]
    by_cases hmod : q % 3 = 1
    · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; simp
    · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]
      calc nw0 * yq * nw0⁻¹ = yq * nw0 * nw0⁻¹ := by rw [nw0_comm_yq]
        _ = yq := by group
  have hn_twist : ∀ s u : Lˣ, s ^ (3 ^ b) = 1 → u ^ (3 ^ b) = 1 →
      n * Units.map (entrywiseHom F) (tz s u : ModGL .G2 L) * n⁻¹ = tz s u := by
    intro s u hs hu
    have hFs : Units.map (F : L →* L) s = s ^ q := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      simp [hF, q])
    have hFu : Units.map (F : L →* L) u = u ^ q := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      simp [hF, q])
    rw [frob_tz, hFs, hFu]
    by_cases hmod : q % 3 = 1
    · have hdvd : 3 ^ b ∣ q - 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_one (q := q) hq3 hmod
      obtain ⟨c, hc⟩ := hdvd
      have hsfix : s ^ q = s := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hs, one_pow, one_mul, pow_one]
      have hufix : u ^ q = u := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hu, one_pow, one_mul, pow_one]
      have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn, hsfix, hufix]
      simp
    · have hmod2 : q % 3 = 2 := by
        have := Nat.mod_lt q (by norm_num : 0 < 3)
        omega
      have hdvd : 3 ^ b ∣ q + 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_two (q := q) hq3 hmod2
      obtain ⟨c, hc⟩ := hdvd
      have hsfix : s ^ q = s⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have hsq1 : s ^ (q + 1) = 1 := by rw [hc, pow_mul, hs, one_pow]
        rwa [pow_succ] at hsq1
      have hufix : u ^ q = u⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have huq1 : u ^ (q + 1) = 1 := by rw [hc, pow_mul, hu, one_pow]
        rwa [pow_succ] at huq1
      have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn, hsfix, hufix, nw0_tz]
      simp
  obtain ⟨g, hg, hFg, hrat⟩ := hTW n hn_mem
  let T : Subgroup (ModGL .G2 L) := tzPart (3 ^ b)
  let hExt : Ext3 T (yq : ModGL .G2 L) := ext3_tzPart (L := L) (m := 3 ^ b) hζu_ne1
  let H : Subgroup (ModGL .G2 L) := extSub hExt
  let S : Subgroup (ModGL .G2 L) := H.map (MulAut.conj g).toMonoidHom
  have hcardT : Nat.card T = 3 ^ (2 * b) := by
    calc Nat.card T = Nat.card (tzPart (3 ^ b) : Subgroup (ModGL .G2 L)) := rfl
      _ = (3 ^ b) ^ 2 := card_tzPart (L := L) (3 ^ b) hb0 hζu
      _ = 3 ^ (2 * b) := by rw [← pow_mul]; congr 1; omega
  have hcardH : Nat.card H = 3 ^ (2 * b + 1) := by
    calc Nat.card H = 3 * Nat.card T := card_extSub hExt
      _ = 3 * 3 ^ (2 * b) := by rw [hcardT]
      _ = 3 ^ (2 * b + 1) := by rw [mul_comm, pow_succ]
  have hHle : S ≤ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    have hH : H = Subgroup.closure (T ∪ ({yq} : Set (ModGL .G2 L))) := extSub_eq_closure hExt
    rw [show S = H.map (MulAut.conj g).toMonoidHom from rfl, hH, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_union] at hy
    rcases hy with hy | hy
    · obtain ⟨s, u, hs, hu, rfl⟩ := hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hrat (tz s u) (tz_mem_adjointGroup s u) (hn_twist s u hs hu)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hrat yq yq_mem_adjointGroup hn_y
  let φ : adjointGroup .G2 K →* ModGL .G2 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  have hrange : φ.range = (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [show φ = (baseChangeGL (algebraMap K L)).comp
      (adjointGroup .G2 K).subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hSle : S ≤ φ.range := by rw [hrange]; exact hHle
  let Q0 : Subgroup (adjointGroup .G2 K) := S.comap φ
  have hmapQ : Q0.map φ = S := Subgroup.map_comap_eq_self hSle
  have hcardS : Nat.card S = 3 ^ (2 * b + 1) := by
    calc Nat.card S = Nat.card (H.map (MulAut.conj g).toMonoidHom) := rfl
      _ = Nat.card H := Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 3 ^ (2 * b + 1) := hcardH
  have hcardQ : Nat.card Q0 = 3 ^ (2 * b + 1) := by
    rw [← Subgroup.card_map_of_injective (K := Q0) hφinj, hmapQ, hcardS]
  have hind : ¬ 3 ∣ Q0.index := by
    intro hdvd
    have hmul : Q0.index * Nat.card Q0 = Nat.card (adjointGroup .G2 K) :=
      Subgroup.index_mul_card Q0
    rw [hcardQ, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2] at hmul
    have hidx0 : Q0.index ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      have hpos : 0 < CFSG.Open.ordG2 (Nat.card K) := by
        rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
        exact Nat.card_pos
      omega
    have hv3 : padicValNat 3 (CFSG.Open.ordG2 q) = 2 * b + 1 := by
      simpa [b, q] using CFSG.RankThree.PartTwo.Sec12.OrdG2D4.v3_ordG2_of_not_dvd (a := q) hq3 h3
    have hmul' : Q0.index * 3 ^ (2 * b + 1) = CFSG.Open.ordG2 q := by
      simpa [q] using hmul
    have hv : padicValNat 3 (Q0.index * 3 ^ (2 * b + 1)) = 2 * b + 1 := by rw [hmul', hv3]
    rw [padicValNat.mul hidx0 (pow_ne_zero (2 * b + 1) (by norm_num)),
      padicValNat.prime_pow] at hv
    have hle : 1 ≤ padicValNat 3 Q0.index := one_le_padicValNat_of_dvd hidx0 hdvd
    omega
  have hQ0syl : ∃ P : Sylow 3 (adjointGroup .G2 K),
      (P : Subgroup (adjointGroup .G2 K)) = Q0 :=
    ⟨(IsPGroup.of_card (n := 2 * b + 1) hcardQ).toSylow hind, rfl⟩
  let z0val : ModGL .G2 L := tz 1 ωu⁻¹
  have hωu_inv_pow : (ωu⁻¹ : Lˣ) ^ (3 ^ b) = 1 := by
    have h3inv : (ωu⁻¹) ^ 3 = 1 := by rw [inv_pow, hωu3, inv_one]
    obtain ⟨c, hc⟩ := h3bdvd
    rw [hc, pow_mul, h3inv, one_pow]
  have hzHmem : z0val ∈ H :=
    le_extSub hExt (tz_mem_tzPart (m := 3 ^ b) (by simp) hωu_inv_pow)
  let zH : ↥H := ⟨z0val, hzHmem⟩
  have hzHval : (zH : ModGL .G2 L) = z0val := rfl
  have hzH_order_val : orderOf z0val = 3 := by
    have h := orderOf_tz_one (L := L) (ω := ωu⁻¹)
      (by rw [inv_pow, hωu3, inv_one]) (by simpa using hωu1)
    simpa [z0val] using h
  have hzH_order : orderOf zH = 3 := by
    rw [← Subgroup.orderOf_coe zH, hzHval, hzH_order_val]
  have hcenterH : Subgroup.center ↥H = Subgroup.zpowers zH := by
    apply le_antisymm
    · intro x hx
      have hxv :=
        (mem_center_extSub_tzPart_iff (L := L) (m := 3 ^ b) h3bdvd hωu3 hωu1 hωu x).mp hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxv
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hzHc : zH ∈ Subgroup.center ↥H :=
        (mem_center_extSub_tzPart_iff (L := L) (m := 3 ^ b) h3bdvd hωu3 hωu1 hωu zH).mpr
          (Subgroup.mem_zpowers z0val)
      rw [← hk]
      exact Subgroup.zpow_mem (K := Subgroup.center ↥H) hzHc k
  let eH : ↥H ≃* ↥S := (MulAut.conj g).subgroupMap H
  have hcardCenterH : Nat.card (Subgroup.center ↥H) = 3 := by
    rw [hcenterH, Nat.card_zpowers, hzH_order]
  have hzSval : ((eH zH : ↥S) : ModGL .G2 L) = g * z0val * g⁻¹ := by
    rw [show ((eH zH : ↥S) : ModGL .G2 L) =
      (MulAut.conj g) ((zH : ↥H) : ModGL .G2 L) from
        MulEquiv.coe_subgroupMap_apply (MulAut.conj g) H zH]
    rw [MulAut.conj_apply, hzHval]
  have hzS_center : eH zH ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hzHc : zH ∈ Subgroup.center ↥H := by
      rw [hcenterH]
      exact Subgroup.mem_zpowers _
    have h := Subgroup.mem_center_iff.mp hzHc (eH.symm s)
    calc s * eH zH = eH (eH.symm s) * eH zH := by rw [eH.apply_symm_apply]
      _ = eH (eH.symm s * zH) := by rw [map_mul]
      _ = eH (zH * eH.symm s) := by rw [h]
      _ = eH zH * eH (eH.symm s) := by rw [map_mul]
      _ = eH zH * s := by rw [eH.apply_symm_apply]
  have hcardCenterS : Nat.card (Subgroup.center ↥S) = 3 := by
    have h : Nat.card ((Subgroup.center ↥H).map (eH : ↥H →* ↥S)) =
        Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective (K := Subgroup.center ↥H) (f := (eH : ↥H →* ↥S))
        eH.injective
    rw [Subgroup.map_center_eq eH] at h
    rw [h, hcardCenterH]
  have hzSval_mem : ((eH zH : ↥S) : ModGL .G2 L) ∈ S := (eH zH).2
  have hzSval_mem' : ((eH zH : ↥S) : ModGL .G2 L) ∈ Q0.map φ := by
    rw [hmapQ]; exact hzSval_mem
  obtain ⟨z0, hz0Q, hφz0⟩ := Subgroup.mem_map.mp hzSval_mem'
  have hz0_order : orderOf z0 = 3 := by
    have hφinjQ : Function.Injective (φ.comp Q0.subtype) := hφinj.comp Subtype.val_injective
    show orderOf ((⟨z0, hz0Q⟩ : ↥Q0) : ↥(adjointGroup .G2 K)) = 3
    rw [Subgroup.orderOf_coe (⟨z0, hz0Q⟩ : ↥Q0),
      ← orderOf_injective (φ.comp Q0.subtype) hφinjQ ⟨z0, hz0Q⟩]
    change orderOf (φ z0) = 3
    rw [hφz0, Subgroup.orderOf_coe, eH.orderOf_eq zH, hzH_order]
  have hcenterQ : Subgroup.center ↥Q0 = Subgroup.zpowers ⟨z0, hz0Q⟩ := by
    have hz0c : (⟨z0, hz0Q⟩ : ↥Q0) ∈ Subgroup.center ↥Q0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      apply hφinj
      rw [show ((y * ⟨z0, hz0Q⟩ : ↥Q0) : ↥(adjointGroup .G2 K)) =
            (y : ↥(adjointGroup .G2 K)) * z0 from map_mul Q0.subtype y ⟨z0, hz0Q⟩,
          show ((⟨z0, hz0Q⟩ * y : ↥Q0) : ↥(adjointGroup .G2 K)) =
            z0 * (y : ↥(adjointGroup .G2 K)) from map_mul Q0.subtype ⟨z0, hz0Q⟩ y,
          map_mul, map_mul, hφz0]
      have hyS : φ (y : ↥(adjointGroup .G2 K)) ∈ S := Subgroup.mem_comap.mp y.2
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzS_center ⟨φ y, hyS⟩)
    let eQ : ↥Q0 ≃* ↥S :=
      (Subgroup.equivMapOfInjective Q0 φ hφinj).trans (MulEquiv.subgroupCongr hmapQ)
    have heQz : eQ ⟨z0, hz0Q⟩ = eH zH := by
      apply Subtype.ext
      change φ z0 = ((eH zH : ↥S) : ModGL .G2 L)
      exact hφz0
    have hcardCenterQ : Nat.card (Subgroup.center ↥Q0) = 3 := by
      have h : Nat.card ((Subgroup.center ↥Q0).map (eQ : ↥Q0 →* ↥S)) =
          Nat.card (Subgroup.center ↥Q0) :=
        Subgroup.card_map_of_injective (K := Subgroup.center ↥Q0)
          (f := (eQ : ↥Q0 →* ↥S)) eQ.injective
      rw [Subgroup.map_center_eq eQ] at h
      rw [← h, hcardCenterS]
    have hzord : orderOf (⟨z0, hz0Q⟩ : ↥Q0) = 3 := by
      rw [← eQ.orderOf_eq ⟨z0, hz0Q⟩, heQz, eH.orderOf_eq zH, hzH_order]
    have hle : Subgroup.zpowers (⟨z0, hz0Q⟩ : ↥Q0) ≤ Subgroup.center ↥Q0 :=
      Subgroup.zpowers_le.mpr hz0c
    have heq : Nat.card (Subgroup.center ↥Q0) =
        Nat.card (Subgroup.zpowers (⟨z0, hz0Q⟩ : ↥Q0)) := by
      rw [hcardCenterQ, Nat.card_zpowers, hzord]
    exact (Subgroup.eq_of_le_of_card_ge hle heq.le).symm
  refine ⟨Q0, ⟨z0, hz0Q⟩, hQ0syl, hcenterQ, hz0_order, L, inferInstance, φ, g, ωu, 3 ^ b,
    hωu1, hφinj, h3L, hωu3, ?_, ?_⟩
  · have hext : ext3_tzPart (L := L) (m := 3 ^ b) hωu1 = hExt := Subsingleton.elim _ _
    rw [hext]
    exact hmapQ
  · simpa [z0val] using hφz0.trans hzSval

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
