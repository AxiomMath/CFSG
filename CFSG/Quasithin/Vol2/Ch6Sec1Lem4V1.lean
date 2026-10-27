module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F4

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

variable {F : Type*} [Field F] [Finite F]

theorem exists_two_involutions614 (hK : IsOddPrimePower (Nat.card F))
    {D : Subgroup (PGammaL2 F)} (hDs : IsSylowTwoOf D (pGammaL2PSLRange F)) :
    ∃ a ∈ D, ∃ b ∈ D, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PSL2 F) := Finite.of_injective _
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := F))
  set ι := iotaPSL614 F
  have hinj : Function.Injective ι := iotaPSL614_injective
  have hDN : D ≤ ι.range := hDs.1
  set D₁ := D.comap ι with hD₁
  have hD₁2 : IsPGroup 2 D₁ := by
    intro x
    obtain ⟨k, hk⟩ := hDs.2.1 ⟨ι x, x.2⟩
    refine ⟨k, Subtype.ext (hinj ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hD₁i : ¬ 2 ∣ D₁.index := by
    have h1 : (D₁.map ι).relIndex ((⊤ : Subgroup (PSL2 F)).map ι) = D₁.index := by
      rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr hinj, sup_bot_eq,
        sup_bot_eq, Subgroup.relIndex_top_right]
    rw [Subgroup.map_comap_eq_self hDN, ← MonoidHom.range_eq_map] at h1
    rw [← h1]
    exact hDs.2.2
  set S : Sylow 2 (PSL2 F) := hD₁2.toSylow hD₁i
  obtain ⟨m, hm, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hK S
  obtain ⟨a, b, ha1, hb1, hab, ha2, hb2, hcomm⟩ := dihedral_commuting_involutions614 hm
  have hmem : ∀ c : DihedralGroup (2 ^ m), ι ((e.symm c : S) : PSL2 F) ∈ D :=
    fun c => (e.symm c).2
  have hsq : ∀ c : DihedralGroup (2 ^ m), c ^ 2 = 1 → ι ((e.symm c : S) : PSL2 F) ^ 2 = 1 := by
    intro c hc
    rw [← map_pow, ← Subgroup.coe_pow, ← map_pow, hc, map_one, Subgroup.coe_one, map_one]
  have hinj' : ∀ c d : DihedralGroup (2 ^ m),
      ι ((e.symm c : S) : PSL2 F) = ι ((e.symm d : S) : PSL2 F) → c = d := by
    intro c d h
    have h1 : e.symm c = e.symm d := Subtype.ext (hinj h)
    simpa using congrArg e h1
  have hne : ∀ c : DihedralGroup (2 ^ m), c ≠ 1 → ι ((e.symm c : S) : PSL2 F) ≠ 1 := by
    intro c hc h
    apply hc
    apply hinj' c 1
    rw [h, map_one, Subgroup.coe_one, map_one]
  refine ⟨_, hmem a, _, hmem b, hne a ha1, hne b hb1, fun h => hab (hinj' a b h), hsq a ha2,
    hsq b hb2, ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  have := congrArg (fun c => ((e.symm c : S) : PSL2 F)) hcomm
  simpa using this

theorem pGammaL2EquivMulAut614_symm_conj (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {p f : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ f) (s : PSL2 F) :
    (pGammaL2EquivMulAut614 F hK hcard hF).symm (MulAut.conj s) = iotaPSL614 F s := by
  rw [MulEquiv.symm_apply_eq]
  symm
  show pGammaL2ToMulAutPSL2 F hK hcard
    (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL s)) = _
  rw [pGammaL2ToMulAutPSL2_inl, pgl2InnerAutPSL2_toPGL]

theorem exists_inv_of_isSylowTwoOf614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) {D : Subgroup (PGammaL2 F)} {y : PGammaL2 F}
    (hDs : IsSylowTwoOf D (pGammaL2PSLRange F)) (hyN : y ∈ pGammaL2PSLRange F)
    (hy5 : orderOf y = 5)
    (hDy : D ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F))) :
    ∃ r ∈ D, r * y * r⁻¹ = y⁻¹ := by
  classical
  obtain ⟨a, haD, b, hbD, ha1, hb1, hab, ha2, hb2, -⟩ := exists_two_involutions614 hK hDs
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  rcases conj_eq_or_eq_inv_of_sq614 hy5' ha2 (hDy haD) with hA | hA
  swap
  · exact ⟨a, haD, hA⟩
  rcases conj_eq_or_eq_inv_of_sq614 hy5' hb2 (hDy hbD) with hB | hB
  swap
  · exact ⟨b, hbD, hB⟩
  exfalso
  set ι₂ := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hinj₂ : Function.Injective ι₂ := SemidirectProduct.inl_injective
  set ι₁ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  obtain ⟨y₁, rfl⟩ := hyN
  obtain ⟨a₁, rfl⟩ := hDs.1 haD
  obtain ⟨b₁, rfl⟩ := hDs.1 hbD
  have hcomm : ∀ c : PSL2 F, ι₂ (ι₁ c) * ι₂ (ι₁ y₁) * (ι₂ (ι₁ c))⁻¹ = ι₂ (ι₁ y₁) →
      Commute (ι₁ c) (ι₁ y₁) := by
    intro c h
    apply hinj₂
    rw [map_mul, map_mul]
    calc ι₂ (ι₁ c) * ι₂ (ι₁ y₁)
        = ι₂ (ι₁ c) * ι₂ (ι₁ y₁) * (ι₂ (ι₁ c))⁻¹ * ι₂ (ι₁ c) := by group
      _ = ι₂ (ι₁ y₁) * ι₂ (ι₁ c) := by rw [h]
  have hsq : ∀ c : PSL2 F, ι₂ (ι₁ c) ^ 2 = 1 → ι₁ c ^ 2 = 1 := fun c h =>
    hinj₂ (by rw [map_pow, map_one]; exact h)
  have hy₀5 : orderOf (ι₁ y₁) = 5 := by
    rw [← orderOf_injective _ hinj₂ (ι₁ y₁)]
    exact hy5
  have ha₀I : BenderSuzuki.PFAppendixIII.IsInvolution (ι₁ a₁) :=
    ⟨fun h => ha1 (by show ι₂ (ι₁ a₁) = 1; rw [h, map_one]), hsq a₁ ha2⟩
  obtain ⟨hinv, -⟩ := pgl2_inner_order_five614 hK hcard hy₀5 ⟨y₁, rfl⟩ ⟨a₁, rfl⟩ ha₀I
    (hcomm a₁ hA).symm
  rcases hinv (ι₁ b₁) (hsq b₁ hb2) (hcomm b₁ hB) with h | h
  · exact hb1 (by show ι₂ (ι₁ b₁) = 1; rw [h, map_one])
  · exact hab (by show ι₂ (ι₁ a₁) = ι₂ (ι₁ b₁); rw [h])

theorem five_dvd_of_commute_inner614 (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    {y z : PGL2 F} (hy : orderOf y = 5)
    (hzJ : z ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hz : BenderSuzuki.PFAppendixIII.IsInvolution z) (hyz : Commute y z) :
    (Even ((Nat.card F - 1) / 2) ∧ 5 ∣ Nat.card F - 1) ∨
      (¬ Even ((Nat.card F - 1) / 2) ∧ 5 ∣ Nat.card F + 1) := by
  classical
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three F hK hcard
  have hJidx : (commutator (PGL2 F)).index = 2 := hJ ▸ pgl2_psl2Range_index_eq_two F hK
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, -, hpo, -, hq⟩ := hK
    rw [hq]
    exact hpo.pow
  have key : ∀ (U : Subgroup (PGL2 F)) (s w : PGL2 F), s * s = 1 → s ≠ 1 → w * w = 1 →
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) →
      Subgroup.centralizer ({s} : Set (PGL2 F)) = U ⊔ Subgroup.zpowers w →
      s ∈ commutator (PGL2 F) → 5 ∣ Nat.card U := by
    intro U s w hss hs1 hww hwinv hC hsJ
    have hsI : BenderSuzuki.PFAppendixIII.IsInvolution s := ⟨hs1, by rw [pow_two]; exact hss⟩
    obtain ⟨g, -, hg⟩ := pgl2_inner_involutions_conjugate hK hcard hsJ hsI (hJ ▸ hzJ) hz
    have hy'C : g⁻¹ * y * g ∈ U ⊔ Subgroup.zpowers w := by
      rw [← hC, Subgroup.mem_centralizer_singleton_iff]
      have e : y * z = z * y := hyz.eq
      rw [← hg] at e
      calc g⁻¹ * y * g * s = g⁻¹ * (y * (g * s * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * s * g⁻¹) * y) * g := by rw [e]
        _ = s * (g⁻¹ * y * g) := by group
    have hy'5 : orderOf (g⁻¹ * y * g) = 5 := by
      have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) y
      rw [MulAut.conj_apply, inv_inv] at this
      rw [this, hy]
    rcases mem_or_mem_mul_of_mem_sup_zpowers614 hww hwinv hy'C with h | ⟨u, hu, he⟩
    · have := Subgroup.orderOf_dvd_natCard U h
      rwa [hy'5] at this
    · exfalso
      have h2 : (u * w) ^ 2 = 1 := by
        rw [pow_two]
        calc u * w * (u * w) = u * (w * u * w⁻¹) * (w * w) := by group
          _ = u * u⁻¹ * (w * w) := by rw [hwinv u hu]
          _ = 1 := by rw [hww]; group
      rw [← he] at h2
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hy'5] at this
      norm_num at this
  rcases Nat.even_or_odd ((Nat.card F - 1) / 2) with hev | hev
  · obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, -, hww, hwinv, hC, hUJ⟩ :=
      pgl2_split_torus_centralizer_data F hodd
    have hsJ : s ∈ commutator (PGL2 F) := by
      refine pgl2_torus_involution_mem_commutator hJidx U hUc hsU hss hs1
        (m := (Nat.card F - 1) / 2) ?_ hev (hJ ▸ hUJ hodd)
      rw [hUcard]
      obtain ⟨k, hk⟩ := hodd
      omega
    left
    exact ⟨hev, hUcard ▸ key U s w hss hs1 hww hwinv hC hsJ⟩
  · obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, -, hww, hwinv, hC, hUJ⟩ :=
      pgl2_nonsplit_torus_centralizer_data F hodd
    have hsJ : s ∈ commutator (PGL2 F) := by
      refine pgl2_torus_involution_mem_commutator hJidx U hUc hsU hss hs1
        (m := (Nat.card F + 1) / 2) ?_ ?_ (hJ ▸ hUJ hodd)
      · rw [hUcard]
        obtain ⟨k, hk⟩ := hodd
        omega
      · obtain ⟨k, hk⟩ := hodd
        obtain ⟨j, hj⟩ := hev
        refine ⟨(k + 1) / 2, ?_⟩
        omega
    right
    exact ⟨Nat.not_even_iff_odd.mpr hev, hUcard ▸ key U s w hss hs1 hww hwinv hC hsJ⟩

theorem false_of_le_normalizer_five614 (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) (hq : Nat.card F = 5 ∨ Nat.card F = 9 ∨ Nat.card F = 25)
    {D : Subgroup (PGammaL2 F)} {y : PGammaL2 F} (hDs : IsSylowTwoOf D (pGammaL2PSLRange F))
    (hyN : y ∈ pGammaL2PSLRange F) (hy5 : orderOf y = 5)
    (hDy : D ≤ Subgroup.normalizer (Subgroup.zpowers y : Set (PGammaL2 F))) : False := by
  classical
  have hDs' : IsSylowTwoOf D (pGammaL2PSLRange F ⊔ D) := by rwa [sup_eq_left.mpr hDs.1]
  obtain ⟨z, hzN, hzI, hyz⟩ := exists_involution_commute614 hK hcard hDs' hy5 hDy
  set ι₂ := (SemidirectProduct.inl : PGL2 F →* PGammaL2 F)
  have hinj₂ : Function.Injective ι₂ := SemidirectProduct.inl_injective
  set ι₁ := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)
  obtain ⟨y₁, rfl⟩ := hyN
  obtain ⟨z₁, rfl⟩ := hzN
  have hy₀5 : orderOf (ι₁ y₁) = 5 := by
    rw [← orderOf_injective _ hinj₂ (ι₁ y₁)]
    exact hy5
  have hz₀I : BenderSuzuki.PFAppendixIII.IsInvolution (ι₁ z₁) :=
    ⟨fun h => hzI.1 (by show ι₂ (ι₁ z₁) = 1; rw [h, map_one]),
      hinj₂ (by rw [map_pow, map_one]; exact hzI.2)⟩
  have hyz₀ : Commute (ι₁ y₁) (ι₁ z₁) := hinj₂ (by rw [map_mul, map_mul]; exact hyz.eq)
  rcases five_dvd_of_commute_inner614 hK hcard hy₀5 ⟨z₁, rfl⟩ hz₀I hyz₀ with
    ⟨hev, h⟩ | ⟨hev, h⟩ <;> rcases hq with hq | hq | hq <;> rw [hq] at h hev <;> revert h hev <;>
    norm_num [Nat.even_iff]

end

end CFSG.Quasithin.H13
