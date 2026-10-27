module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3Odd
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3Sp6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace Co3K

open Subgroup CFSG.Sporadic.Schreier.Co3

private theorem index_cases {m : ℕ} (hdvd : m ∣ 484147125) (h3 : ¬ 3 ∣ m) (h1 : m ≠ 1)
    (h23 : m ≤ 23) : m = 5 ∨ m = 7 ∨ m = 11 ∨ m = 23 := by
  have h0 : m ≠ 0 := by
    rintro rfl
    norm_num at hdvd
  interval_cases m <;> omega

theorem eq_co3T_of_solvable
    {Z : Subgroup (Equiv.Perm (Fin 276))} (hZP : Z ≤ co3P)
    (hTZ : co3T ≤ Z) (hZs : Group.IsSolvable ↥Z) (h3 : ¬ 3 ∣ Nat.card Z) : Z = co3T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmdef⟩ : ∃ m, (co3T.subgroupOf Z).index = m := ⟨_, rfl⟩
  have hcardTz : Nat.card (co3T.subgroupOf Z) = 1024 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTZ).toEquiv, card_co3T]
  have hZm : Nat.card Z = 1024 * m := by
    have h := (co3T.subgroupOf Z).card_mul_index
    rw [hcardTz, hmdef] at h
    exact h.symm
  have hmdvd : m ∣ 484147125 := by
    have h := card_dvd_of_le hZP
    rw [card_co3P, hZm, show (495766656000 : ℕ) = 1024 * 484147125 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hm3 : ¬ 3 ∣ m := fun h => h3 (by rw [hZm]; exact h.mul_left 1024)
  have hm2 : ¬ 2 ∣ m := fun h => absurd (h.trans hmdvd) (by norm_num)
  by_cases hm1 : m = 1
  · rw [hm1, index_eq_one, subgroupOf_eq_top] at hmdef
    exact le_antisymm hmdef hTZ
  exfalso
  have hzZ : co3Z ∈ Z := hTZ co3Z_mem_T
  haveI : Nontrivial ↥Z :=
    nontrivial_of_ne (⟨co3Z, hzZ⟩ : Z) 1 fun h => co3Z_ne_one (congrArg Subtype.val h)
  obtain ⟨p, hp, A, hAn, hA1, hAp, hAc⟩ := exists_normal_comm_exponent_prime hZs
  have : Fact p.Prime := ⟨hp⟩
  have hNZ : A.map Z.subtype ≤ Z := map_subtype_le A
  have hN1 : A.map Z.subtype ≠ ⊥ := by
    rwa [Ne, map_eq_bot_iff_of_injective A Z.subtype_injective]
  have hNp : ∀ x ∈ A.map Z.subtype, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAp a ha, map_one]
  have hNc : ∀ x ∈ A.map Z.subtype, ∀ y ∈ A.map Z.subtype, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hNnorm : ∀ g ∈ Z, ∀ x ∈ A.map Z.subtype, g * x * g⁻¹ ∈ A.map Z.subtype := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact mem_map.2 ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, hAn.conj_mem a ha ⟨g, hg⟩, rfl⟩
  have hZN : Z ≤ normalizer ((A.map Z.subtype : Subgroup (Equiv.Perm (Fin 276))) :
      Set (Equiv.Perm (Fin 276))) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hNnorm g hg x, fun hx => ?_⟩
    have h := hNnorm g⁻¹ (Z.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h
  obtain ⟨⟨a, haA⟩, ha1⟩ := ne_bot_iff_exists_ne_one.1 hA1
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hpZ : p ∣ Nat.card Z := by
    rw [← orderOf_eq_prime (hAp a haA) ha1']
    exact orderOf_dvd_natCard a
  rcases eq_or_ne p 2 with rfl | hp2
  swap
  ·
    have hcop : Nat.Coprime p 1024 := by
      have := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right 10
      simpa using this
    rw [hZm] at hpZ
    have hpm : p ∣ m := hcop.dvd_of_dvd_mul_left hpZ
    have hp3 : p ≠ 3 := fun h => hm3 (h ▸ hpm)
    exact false_of_normal_odd (hNZ.trans hZP) hN1 hNc hp hp2 hp3 hNp (hTZ.trans hZN)
  set N : Subgroup (Equiv.Perm (Fin 276)) := A.map Z.subtype
  have hTzP : IsPGroup 2 (co3T.subgroupOf Z) :=
    IsPGroup.of_card (n := 10) (by rw [hcardTz]; norm_num)
  have hTzi : ¬ 2 ∣ (co3T.subgroupOf Z).index := by
    rw [hmdef]
    exact hm2
  have hApg : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAp x x.2)⟩
  haveI := hAn
  have hATz : A ≤ co3T.subgroupOf Z := hApg.le_sylow_of_normal (hTzP.toSylow hTzi)
  have hNT : N ≤ co3T := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_subgroupOf.1 (hATz ha)
  have hNTn : (N.subgroupOf co3T).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hNnorm g (hTZ g.2) n hn
  have hNT1 : N.subgroupOf co3T ≠ ⊥ := by
    intro h
    apply hN1
    have := subgroupOf_map_subtype N co3T
    rw [h, Subgroup.map_bot, inf_of_le_left hNT] at this
    exact this.symm
  have hTpg : IsPGroup 2 ↥co3T := IsPGroup.of_card (n := 10) (by rw [card_co3T]; norm_num)
  haveI : Group.IsNilpotent ↥co3T := hTpg.isNilpotent
  haveI := hNTn
  have hzN : co3Z ∈ N := by
    obtain ⟨⟨x, hx⟩, hx1⟩ :=
      ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hNT1)
    obtain ⟨hxN, hxC⟩ := mem_inf.1 hx
    have hxc : (x : Equiv.Perm (Fin 276)) ∈ co3T ∧
        ∀ y ∈ co3T, (x : Equiv.Perm (Fin 276)) * y = y * x :=
      ⟨x.2, fun y hy => (congrArg Subtype.val (Subgroup.mem_center_iff.1 hxC ⟨y, hy⟩)).symm⟩
    rcases (co3T_center_iff _).1 hxc with h | h
    · exact (hx1 (Subtype.ext (Subtype.ext h))).elim
    · rw [← h]
      exact mem_subgroupOf.1 hxN
  have hNd : ∀ x ∈ N, x ≠ 1 → ∃ i < 23, x = co3Kd i := by
    intro x hx hx1
    refine co3K_inv_cases (hNT hx) (by rw [← sq]; exact hNp x hx) hx1 (fun k hk => ?_)
    exact hNc x hx _ (hNnorm _ (hTZ (co3TGen_mem hk)) x hx)
  have hZM : Z ⊓ co3M = co3T :=
    eq_co3T_of_le_co3M (le_inf hTZ co3T_le_co3M) inf_le_right
      (fun h => h3 (h.trans (card_dvd_of_le inf_le_left)))
  set zZ : ↥Z := ⟨co3Z, hzZ⟩
  have hCz : centralizer {zZ} = co3T.subgroupOf Z := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, ← hZM, mem_inf, co3M_eq_centralizer,
      mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨g.2, hZP g.2, congrArg Subtype.val h⟩
    · rintro ⟨-, -, h⟩
      exact Subtype.ext h
  have hΩ : (conjugatesOf zZ).ncard = m := by
    rw [← index_centralizer_eq_ncard, hCz]
    exact hmdef
  have hΩ' : ∀ c ∈ conjugatesOf zZ, ∃ g : ↥Z,
      (c : Equiv.Perm (Fin 276)) = g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹ := by
    intro c hc
    obtain ⟨g, rfl⟩ := isConj_iff.1 (show IsConj zZ c from hc)
    exact ⟨g, rfl⟩
  have hΩN : ∀ g : ↥Z, (g : Equiv.Perm (Fin 276)) * co3Z * (g : Equiv.Perm (Fin 276))⁻¹ ∈ N :=
    fun g => hNnorm g g.2 co3Z hzN
  have hΩ1 : ∀ g : ↥Z, (g : Equiv.Perm (Fin 276)) * co3Z * (g : Equiv.Perm (Fin 276))⁻¹ ≠ 1 :=
    fun g h => co3Z_ne_one (by simpa using h)
  have hm23 : m ≤ 23 := by
    rw [← hΩ]
    calc (conjugatesOf zZ).ncard
        ≤ (Set.range fun i : Fin 23 => co3Kd i).ncard := by
          refine Set.ncard_le_ncard_of_injOn Subtype.val (fun c hc => ?_)
            Subtype.val_injective.injOn
          obtain ⟨g, hg⟩ := hΩ' c hc
          have hcN : (c : Equiv.Perm (Fin 276)) ∈ N := by
            rw [hg]
            exact hΩN g
          have hc1 : (c : Equiv.Perm (Fin 276)) ≠ 1 := by
            rw [hg]
            exact hΩ1 g
          obtain ⟨i, hi, he⟩ := hNd _ hcN hc1
          exact ⟨⟨i, hi⟩, he.symm⟩
      _ ≤ 23 := by
        rw [← Set.image_univ]
        exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp [Set.ncard_univ])
  have hmc := index_cases hmdvd hm3 hm1 hm23
  have hmp : m.Prime := by rcases hmc with rfl | rfl | rfl | rfl <;> norm_num
  have hG2 := card_dvd_pred_mul_card_normalCore hZs hmp hmdef
  have hK₀T : (co3T.subgroupOf Z).normalCore ≤ co3T.subgroupOf Z := normalCore_le _
  obtain ⟨d, hd⟩ : ∃ d,
      (((co3T.subgroupOf Z).normalCore).subgroupOf (co3T.subgroupOf Z)).index = d := ⟨_, rfl⟩
  have hkd : Nat.card ((co3T.subgroupOf Z).normalCore) * d = 1024 := by
    rw [← hd, ← Nat.card_congr (subgroupOfEquivOfLe hK₀T).toEquiv, card_mul_index, hcardTz]
  have hd4 : d ∣ 4 := by
    rw [hcardTz, ← hkd, mul_comm (m - 1)] at hG2
    have h1 : d ∣ m - 1 := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hG2
    have h2 : d ∣ 1024 := Dvd.intro_left _ hkd
    have h4 : Nat.gcd (m - 1) 1024 ∣ 4 := by
      rcases hmc with rfl | rfl | rfl | rfl <;> norm_num
    exact (Nat.dvd_gcd h1 h2).trans h4
  have hidx4 :
      (((co3T.subgroupOf Z).normalCore).subgroupOf (co3T.subgroupOf Z)).index ∣ 4 := by
    rw [hd]
    exact hd4
  have hcent : ∀ k ∈ (co3T.subgroupOf Z).normalCore, ∀ g : ↥Z,
      (k : Equiv.Perm (Fin 276)) * (g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹) =
        g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹ * k := by
    intro k hk g
    have h1 : g⁻¹ * k * g ∈ (co3T.subgroupOf Z).normalCore := by
      have := (normalCore_normal (co3T.subgroupOf Z)).conj_mem k hk g⁻¹
      rwa [inv_inv] at this
    have h2 : ((g⁻¹ * k * g : ↥Z) : Equiv.Perm (Fin 276)) ∈ co3T := mem_subgroupOf.1 (hK₀T h1)
    have h3 : (g : Equiv.Perm (Fin 276))⁻¹ * k * g * co3Z =
        co3Z * ((g : Equiv.Perm (Fin 276))⁻¹ * k * g) :=
      mem_centralizer_singleton_iff.1 (co3T_le_centralizer_Z h2)
    calc (k : Equiv.Perm (Fin 276)) * (g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹)
        = g * ((g : Equiv.Perm (Fin 276))⁻¹ * k * g * co3Z) * (g : Equiv.Perm (Fin 276))⁻¹ := by
          group
      _ = g * (co3Z * ((g : Equiv.Perm (Fin 276))⁻¹ * k * g)) * (g : Equiv.Perm (Fin 276))⁻¹ := by
          rw [h3]
      _ = g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹ * k := by group
  have hgenZ : ∀ k < 8, co3TGen k ∈ Z := fun k hk => hTZ (co3TGen_mem hk)
  have hwc : ∀ w : Equiv.Perm (Fin 276),
      ((∃ a < 8, ∃ b < 8, w = co3TGen a * co3TGen b * (co3TGen a)⁻¹ * (co3TGen b)⁻¹) ∨
        ∃ a < 8, w = co3TGen a ^ 4) → ∀ g : ↥Z,
      w * (g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹) =
        g * co3Z * (g : Equiv.Perm (Fin 276))⁻¹ * w := by
    rintro w (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩) g
    · exact hcent _ (commutator_mem_of_index_dvd_four hidx4 (x := ⟨co3TGen a, hgenZ a ha⟩)
        (y := ⟨co3TGen b, hgenZ b hb⟩) (mem_subgroupOf.2 (co3TGen_mem ha))
        (mem_subgroupOf.2 (co3TGen_mem hb))) g
    · exact hcent _ (pow_four_mem_of_index_dvd_four hidx4 (x := ⟨co3TGen a, hgenZ a ha⟩)
        (mem_subgroupOf.2 (co3TGen_mem ha))) g
  have hm5 : 5 ≤ m := by rcases hmc with rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨u, huΩ, huz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {zZ})
    (t := conjugatesOf zZ) (by rw [Set.ncard_singleton, hΩ]; omega)
  obtain ⟨v, hvΩ, hvs⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {zZ, u, u * zZ})
    (t := conjugatesOf zZ) (by
      rw [hΩ]
      have h1 := Set.ncard_insert_le zZ ({u, u * zZ} : Set ↥Z)
      have h2 := Set.ncard_insert_le u ({u * zZ} : Set ↥Z)
      have h3 := Set.ncard_singleton (u * zZ)
      omega)
  obtain ⟨gu, hgu⟩ := hΩ' u huΩ
  obtain ⟨gv, hgv⟩ := hΩ' v hvΩ
  have huN : (u : Equiv.Perm (Fin 276)) ∈ N := by
    rw [hgu]
    exact hΩN gu
  have hvN : (v : Equiv.Perm (Fin 276)) ∈ N := by
    rw [hgv]
    exact hΩN gv
  have hu1 : (u : Equiv.Perm (Fin 276)) ≠ 1 := by
    rw [hgu]
    exact hΩ1 gu
  have hv1 : (v : Equiv.Perm (Fin 276)) ≠ 1 := by
    rw [hgv]
    exact hΩ1 gv
  obtain ⟨i, hi, hui⟩ := hNd _ huN hu1
  obtain ⟨j, hj, hvj⟩ := hNd _ hvN hv1
  have hc : co3Kd i * co3Kd j = co3Kd j * co3Kd i := by
    rw [← hui, ← hvj]
    exact hNc _ huN _ hvN
  have hiz : co3Kd i ≠ co3Z := by
    rw [← hui]
    intro h
    exact huz (Set.mem_singleton_iff.2 (Subtype.ext h))
  have hjz : co3Kd j ≠ co3Z := by
    rw [← hvj]
    intro h
    exact hvs (Set.mem_insert_iff.2 (Or.inl (Subtype.ext h)))
  have hji : co3Kd j ≠ co3Kd i := by
    rw [← hui, ← hvj]
    intro h
    exact hvs (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl (Subtype.ext h)))))
  have hjiz : co3Kd j ≠ co3Kd i * co3Z := by
    rw [← hui, ← hvj]
    intro h
    exact hvs (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2
      (Or.inr (Set.mem_singleton_iff.2 (Subtype.ext h))))))
  obtain ⟨w, hw, hwn⟩ := co3K_witness hi hj hc hiz hjz hji hjiz
  apply hwn
  constructor
  · rw [← hui, hgu]
    exact hwc w hw gu
  · rw [← hvj, hgv]
    exact hwc w hw gv

end Co3K

open CFSG.Sporadic.Schreier.Co3 in
theorem k105SporAt_Co3 :
    K105SporAt .Co3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf (co3T.subgroupOf co3P) ⊤ := by
    refine ⟨le_top, co3T_isPGroup, ?_⟩
    rw [show ((co3T.subgroupOf co3P).subgroupOf ⊤).index = (co3T.subgroupOf co3P).index from
      Subgroup.relIndex_top_right _]
    exact co3T_not_dvd_index
  refine k105SporAt_of_index (s := .Co3) hS₀ (fun Z hZ hZs m hm => ?_) co3PermEquiv
  by_cases h3 : 3 ∣ m
  · exact Or.inr h3
  left
  have hZ' : Z.map co3P.subtype = co3T := by
    refine Co3K.eq_co3T_of_solvable (Subgroup.map_subtype_le Z)
      (fun x hx => Subgroup.mem_map.2 ⟨⟨x, co3T_le_P hx⟩, hZ (Subgroup.mem_subgroupOf.2 hx), rfl⟩)
      (Group.isSolvable_of_surjective (co3P.subtype.subgroupMap_surjective Z)) ?_
    rw [Subgroup.card_map_of_injective co3P.subtype_injective, hm, card_co3T_subgroupOf]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact h3 h
    · norm_num at h
  have hc : Nat.card Z = 1024 := by
    rw [← Subgroup.card_map_of_injective (K := Z) co3P.subtype_injective, hZ', card_co3T]
  rw [hc, card_co3T_subgroupOf] at hm
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
