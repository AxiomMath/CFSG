module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporAt
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

namespace ONK

open Subgroup CFSG.ONSchreier

private theorem index_cases {m : ℕ} (hdvd : m ∣ 900030285) (h3 : ¬ 3 ∣ m) (h1 : m ≠ 1)
    (h7 : m ≤ 7) : m = 5 ∨ m = 7 := by
  have h0 : m ≠ 0 := by
    rintro rfl
    norm_num at hdvd
  interval_cases m <;> omega

theorem eq_onT_of_solvable
    {Z : Subgroup (Equiv.Perm (Fin N))} (hZP : Z ≤ Pv)
    (hTZ : onT ≤ Z) (hZs : Group.IsSolvable ↥Z) (h3 : ¬ 3 ∣ Nat.card Z) : Z = onT := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hmdef⟩ : ∃ m, (onT.subgroupOf Z).index = m := ⟨_, rfl⟩
  have hcardTz : Nat.card (onT.subgroupOf Z) = 512 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTZ).toEquiv, card_onT]
  have hZm : Nat.card Z = 512 * m := by
    have h := (onT.subgroupOf Z).card_mul_index
    rw [hcardTz, hmdef] at h
    exact h.symm
  have hmdvd : m ∣ 900030285 := by
    have h := card_dvd_of_le hZP
    rw [card_Pv, hZm, show (460815505920 : ℕ) = 512 * 900030285 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hm3 : ¬ 3 ∣ m := fun h => h3 (by rw [hZm]; exact h.mul_left 512)
  have hm2 : ¬ 2 ∣ m := fun h => absurd (h.trans hmdvd) (by norm_num)
  by_cases hm1 : m = 1
  · rw [hm1, index_eq_one, subgroupOf_eq_top] at hmdef
    exact le_antisymm hmdef hTZ
  exfalso
  have hzZ : onz ∈ Z := hTZ onz_mem_T
  have : Nontrivial ↥Z :=
    nontrivial_of_ne (⟨onz, hzZ⟩ : Z) 1 fun h => onz_ne_one (congrArg Subtype.val h)
  obtain ⟨p, hp, A, hAn, hA1, hAp, hAc⟩ := Co3K.exists_normal_comm_exponent_prime hZs
  have : Fact p.Prime := ⟨hp⟩
  have hVZ : A.map Z.subtype ≤ Z := map_subtype_le A
  have hV1 : A.map Z.subtype ≠ ⊥ := by
    rwa [Ne, map_eq_bot_iff_of_injective A Z.subtype_injective]
  have hVp : ∀ x ∈ A.map Z.subtype, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hAp a ha, map_one]
  have hVc : ∀ x ∈ A.map Z.subtype, ∀ y ∈ A.map Z.subtype, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hVnorm : ∀ g ∈ Z, ∀ x ∈ A.map Z.subtype, g * x * g⁻¹ ∈ A.map Z.subtype := by
    rintro g hg _ ⟨a, ha, rfl⟩
    exact mem_map.2 ⟨⟨g, hg⟩ * a * ⟨g, hg⟩⁻¹, hAn.conj_mem a ha ⟨g, hg⟩, rfl⟩
  have hZV : Z ≤ normalizer ((A.map Z.subtype : Subgroup (Equiv.Perm (Fin N))) :
      Set (Equiv.Perm (Fin N))) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hVnorm g hg x, fun hx => ?_⟩
    have h := hVnorm g⁻¹ (Z.inv_mem hg) _ hx
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
    have hcop : Nat.Coprime p 512 := by
      have := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right 9
      simpa using this
    rw [hZm] at hpZ
    have hpm : p ∣ m := hcop.dvd_of_dvd_mul_left hpZ
    have hp3 : p ≠ 3 := fun h => hm3 (h ▸ hpm)
    exact false_of_normal_odd (hVZ.trans hZP) hV1 hVc hp hp2 hp3 hVp (hTZ.trans hZV)
  set V : Subgroup (Equiv.Perm (Fin N)) := A.map Z.subtype
  have hTzP : IsPGroup 2 (onT.subgroupOf Z) :=
    IsPGroup.of_card (n := 9) (by rw [hcardTz]; norm_num)
  have hTzi : ¬ 2 ∣ (onT.subgroupOf Z).index := by
    rw [hmdef]
    exact hm2
  have hApg : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hAp x x.2)⟩
  have := hAn
  have hATz : A ≤ onT.subgroupOf Z := hApg.le_sylow_of_normal (hTzP.toSylow hTzi)
  have hVT : V ≤ onT := by
    rintro _ ⟨a, ha, rfl⟩
    exact mem_subgroupOf.1 (hATz ha)
  have hVTn : (V.subgroupOf onT).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hVnorm g (hTZ g.2) n hn
  have hVT1 : V.subgroupOf onT ≠ ⊥ := by
    intro h
    apply hV1
    have := subgroupOf_map_subtype V onT
    rw [h, Subgroup.map_bot, inf_of_le_left hVT] at this
    exact this.symm
  have hTpg : IsPGroup 2 ↥onT := IsPGroup.of_card (n := 9) (by rw [card_onT]; norm_num)
  have : Group.IsNilpotent ↥onT := hTpg.isNilpotent
  have := hVTn
  have hzV : onz ∈ V := by
    obtain ⟨⟨x, hx⟩, hx1⟩ :=
      ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hVT1)
    obtain ⟨hxV, hxC⟩ := mem_inf.1 hx
    have hxc : ∀ y ∈ onT, y * (x : Equiv.Perm (Fin N)) = x * y :=
      fun y hy => congrArg Subtype.val (Subgroup.mem_center_iff.1 hxC ⟨y, hy⟩)
    rcases onT_central_cases x.2 hxc with h | h
    · exact (hx1 (Subtype.ext (Subtype.ext h))).elim
    · rw [← h]
      exact mem_subgroupOf.1 hxV
  have hVd : ∀ x (hxT : x ∈ onT), x ∈ V → x ≠ 1 → ∃ i < 7, rhoT ⟨x, hxT⟩ = onKd i := by
    intro x hxT hx hx1
    have hinj := rhoT_injective
    refine onK_inv_cases (by rw [← rhoT_range]; exact ⟨_, rfl⟩) ?_ ?_ (fun j hj => ?_)
    · have h2 : (⟨x, hxT⟩ : onT) * ⟨x, hxT⟩ = 1 := Subtype.ext (by
        change x * x = 1
        rw [← sq]
        exact hVp x hx)
      rw [← map_mul, h2, map_one]
    · intro h
      exact hx1 (congrArg Subtype.val (hinj (h.trans (map_one rhoT).symm)))
    · obtain ⟨s, hs⟩ := gen_mem_range hj
      have hs' : rhoT s = onKs j := hs
      have hcomm : x * (s * x * (s : Equiv.Perm (Fin N))⁻¹) =
          s * x * (s : Equiv.Perm (Fin N))⁻¹ * x :=
        hVc x hx _ (hVnorm _ (hTZ s.2) x hx)
      have h' : (⟨x, hxT⟩ : onT) * (s * ⟨x, hxT⟩ * s⁻¹) = s * ⟨x, hxT⟩ * s⁻¹ * ⟨x, hxT⟩ :=
        Subtype.ext hcomm
      rw [← hs']
      simpa only [map_mul, map_inv] using congrArg rhoT h'
  have hZM : Z ⊓ onM = onT :=
    eq_onT_of_le_onM (le_inf hTZ onT_le_onM) inf_le_right
      (fun h => h3 (h.trans (card_dvd_of_le inf_le_left)))
  set zZ : ↥Z := ⟨onz, hzZ⟩
  have hCz : centralizer {zZ} = onT.subgroupOf Z := by
    ext g
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, ← hZM, mem_inf, onM_eq_centralizer_z,
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
      (c : Equiv.Perm (Fin N)) = g * onz * (g : Equiv.Perm (Fin N))⁻¹ := by
    intro c hc
    obtain ⟨g, rfl⟩ := isConj_iff.1 (show IsConj zZ c from hc)
    exact ⟨g, rfl⟩
  have hΩV : ∀ c ∈ conjugatesOf zZ, (c : Equiv.Perm (Fin N)) ∈ V := fun c hc => by
    obtain ⟨g, hg⟩ := hΩ' c hc
    rw [hg]
    exact hVnorm g g.2 onz hzV
  have hΩ1 : ∀ c ∈ conjugatesOf zZ, (c : Equiv.Perm (Fin N)) ≠ 1 := fun c hc h => by
    obtain ⟨g, hg⟩ := hΩ' c hc
    rw [hg] at h
    exact onz_ne_one (by simpa using h)
  have hm7 : m ≤ 7 := by
    rw [← hΩ]
    let f : ↥Z → Equiv.Perm (Fin 32) := fun c =>
      if h : (c : Equiv.Perm (Fin N)) ∈ onT then rhoT ⟨c, h⟩ else 1
    calc (conjugatesOf zZ).ncard
        ≤ (Set.range fun i : Fin 7 => onKd i).ncard := by
          refine Set.ncard_le_ncard_of_injOn f (fun c hc => ?_) (fun c hc c' hc' hcc => ?_)
          · have hcT := hVT (hΩV c hc)
            obtain ⟨i, hi, he⟩ := hVd _ hcT (hΩV c hc) (hΩ1 c hc)
            refine ⟨⟨i, hi⟩, ?_⟩
            change onKd i = f c
            simp only [f, dif_pos hcT]
            exact he.symm
          · have hcT := hVT (hΩV c hc)
            have hcT' := hVT (hΩV c' hc')
            simp only [f, dif_pos hcT, dif_pos hcT'] at hcc
            have h := congrArg Subtype.val (rhoT_injective hcc)
            exact Subtype.ext h
      _ ≤ 7 := by
        rw [← Set.image_univ]
        exact (Set.ncard_image_le (Set.toFinite _)).trans (by simp [Set.ncard_univ])
  have hmc := index_cases hmdvd hm3 hm1 hm7
  have hmp : m.Prime := by rcases hmc with rfl | rfl <;> norm_num
  have hG2 := Co3K.card_dvd_pred_mul_card_normalCore hZs hmp hmdef
  have hK₀T : (onT.subgroupOf Z).normalCore ≤ onT.subgroupOf Z := normalCore_le _
  obtain ⟨d, hd⟩ : ∃ d,
      (((onT.subgroupOf Z).normalCore).subgroupOf (onT.subgroupOf Z)).index = d := ⟨_, rfl⟩
  have hkd : Nat.card ((onT.subgroupOf Z).normalCore) * d = 512 := by
    rw [← hd, ← Nat.card_congr (subgroupOfEquivOfLe hK₀T).toEquiv, card_mul_index, hcardTz]
  have hd4 : d ∣ 4 := by
    rw [hcardTz, ← hkd, mul_comm (m - 1)] at hG2
    have h1 : d ∣ m - 1 := Nat.dvd_of_mul_dvd_mul_left Nat.card_pos hG2
    have h2 : d ∣ 512 := Dvd.intro_left _ hkd
    have h4 : Nat.gcd (m - 1) 512 ∣ 4 := by
      rcases hmc with rfl | rfl <;> norm_num
    exact (Nat.dvd_gcd h1 h2).trans h4
  have hidx4 :
      (((onT.subgroupOf Z).normalCore).subgroupOf (onT.subgroupOf Z)).index ∣ 4 := by
    rw [hd]
    exact hd4
  have hcent : ∀ k ∈ (onT.subgroupOf Z).normalCore, ∀ g : ↥Z,
      (k : Equiv.Perm (Fin N)) * (g * onz * (g : Equiv.Perm (Fin N))⁻¹) =
        g * onz * (g : Equiv.Perm (Fin N))⁻¹ * k := by
    intro k hk g
    have h1 : g⁻¹ * k * g ∈ (onT.subgroupOf Z).normalCore := by
      have := (normalCore_normal (onT.subgroupOf Z)).conj_mem k hk g⁻¹
      rwa [inv_inv] at this
    have h2 : ((g⁻¹ * k * g : ↥Z) : Equiv.Perm (Fin N)) ∈ onT := mem_subgroupOf.1 (hK₀T h1)
    have h3 : (g : Equiv.Perm (Fin N))⁻¹ * k * g * onz =
        onz * ((g : Equiv.Perm (Fin N))⁻¹ * k * g) :=
      onT_mul_onz h2
    calc (k : Equiv.Perm (Fin N)) * (g * onz * (g : Equiv.Perm (Fin N))⁻¹)
        = g * ((g : Equiv.Perm (Fin N))⁻¹ * k * g * onz) * (g : Equiv.Perm (Fin N))⁻¹ := by
          group
      _ = g * (onz * ((g : Equiv.Perm (Fin N))⁻¹ * k * g)) * (g : Equiv.Perm (Fin N))⁻¹ := by
          rw [h3]
      _ = g * onz * (g : Equiv.Perm (Fin N))⁻¹ * k := by group
  have hwc : ∀ w : Equiv.Perm (Fin 32),
      ((∃ a < 6, ∃ b < 6, w = onKs a * onKs b * (onKs a)⁻¹ * (onKs b)⁻¹) ∨
        ∃ a < 6, w = onKs a ^ 4) →
      ∃ w' : onT, rhoT w' = w ∧ ∃ hw' : (w' : Equiv.Perm (Fin N)) ∈ Z,
        (⟨w', hw'⟩ : ↥Z) ∈ (onT.subgroupOf Z).normalCore := by
    rintro w (⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩)
    · obtain ⟨sa, hsa⟩ := gen_mem_range ha
      obtain ⟨sb, hsb⟩ := gen_mem_range hb
      refine ⟨sa * sb * sa⁻¹ * sb⁻¹, ?_, hTZ (sa * sb * sa⁻¹ * sb⁻¹).2, ?_⟩
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hsa, hsb]
      · exact Co3K.commutator_mem_of_index_dvd_four hidx4 (x := ⟨sa, hTZ sa.2⟩)
          (y := ⟨sb, hTZ sb.2⟩) (mem_subgroupOf.2 sa.2) (mem_subgroupOf.2 sb.2)
    · obtain ⟨sa, hsa⟩ := gen_mem_range ha
      refine ⟨sa ^ 4, ?_, hTZ (sa ^ 4).2, ?_⟩
      · rw [map_pow, hsa]
      · exact Co3K.pow_four_mem_of_index_dvd_four hidx4 (x := ⟨sa, hTZ sa.2⟩)
          (mem_subgroupOf.2 sa.2)
  have hcomm32 : ∀ w : Equiv.Perm (Fin 32),
      ((∃ a < 6, ∃ b < 6, w = onKs a * onKs b * (onKs a)⁻¹ * (onKs b)⁻¹) ∨
        ∃ a < 6, w = onKs a ^ 4) →
      ∀ c ∈ conjugatesOf zZ, ∀ hcT : (c : Equiv.Perm (Fin N)) ∈ onT,
        w * rhoT ⟨c, hcT⟩ = rhoT ⟨c, hcT⟩ * w := by
    intro w hw c hc hcT
    obtain ⟨g, hg⟩ := hΩ' c hc
    obtain ⟨w', rfl, hw'Z, hw'K⟩ := hwc w hw
    have h := hcent _ hw'K g
    rw [← hg] at h
    have h' : w' * ⟨c, hcT⟩ = ⟨c, hcT⟩ * w' := Subtype.ext h
    rw [← map_mul, ← map_mul, h']
  have hm5 : 5 ≤ m := by rcases hmc with rfl | rfl <;> norm_num
  obtain ⟨u, huΩ, huz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {zZ})
    (t := conjugatesOf zZ) (by rw [Set.ncard_singleton, hΩ]; omega)
  obtain ⟨v, hvΩ, hvs⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := {zZ, u, u * zZ})
    (t := conjugatesOf zZ) (by
      rw [hΩ]
      have h1 := Set.ncard_insert_le zZ ({u, u * zZ} : Set ↥Z)
      have h2 := Set.ncard_insert_le u ({u * zZ} : Set ↥Z)
      have h3 := Set.ncard_singleton (u * zZ)
      omega)
  have huT := hVT (hΩV u huΩ)
  have hvT := hVT (hΩV v hvΩ)
  obtain ⟨i, hi, hui⟩ := hVd _ huT (hΩV u huΩ) (hΩ1 u huΩ)
  obtain ⟨j, hj, hvj⟩ := hVd _ hvT (hΩV v hvΩ) (hΩ1 v hvΩ)
  have hinj := rhoT_injective
  have hc : onKd i * onKd j = onKd j * onKd i := by
    rw [← hui, ← hvj, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hVc _ (hΩV u huΩ) _ (hΩV v hvΩ))
  have hiz : onKd i ≠ onz32 := by
    rw [← hui, ← rhoT_z]
    intro h
    have h' := congrArg Subtype.val (hinj h)
    exact huz (Set.mem_singleton_iff.2 (Subtype.ext h'))
  have hjz : onKd j ≠ onz32 := by
    rw [← hvj, ← rhoT_z]
    intro h
    have h' := congrArg Subtype.val (hinj h)
    exact hvs (Set.mem_insert_iff.2 (Or.inl (Subtype.ext h')))
  have hji : onKd j ≠ onKd i := by
    rw [← hui, ← hvj]
    intro h
    have h' := congrArg Subtype.val (hinj h)
    exact hvs (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2 (Or.inl (Subtype.ext h')))))
  have hjiz : onKd j ≠ onKd i * onz32 := by
    rw [← hui, ← hvj, ← rhoT_z, ← map_mul]
    intro h
    have h' := congrArg Subtype.val (hinj h)
    exact hvs (Set.mem_insert_iff.2 (Or.inr (Set.mem_insert_iff.2
      (Or.inr (Set.mem_singleton_iff.2 (Subtype.ext h'))))))
  obtain ⟨w, hw, hwn⟩ := onK_witness hi hj hc hiz hjz hji hjiz
  apply hwn
  constructor
  · rw [← hui]
    exact hcomm32 w hw u huΩ huT
  · rw [← hvj]
    exact hcomm32 w hw v hvΩ hvT

end ONK

open CFSG.ONSchreier in
theorem k105SporAt_ONan :
    K105SporAt .ONan := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₀ : CFSG.QuasithinUnique.IsSylowTwoOf (onT.subgroupOf Pv) ⊤ := by
    refine ⟨le_top, onT_isPGroup, ?_⟩
    rw [show ((onT.subgroupOf Pv).subgroupOf ⊤).index = (onT.subgroupOf Pv).index from
      Subgroup.relIndex_top_right _]
    exact onT_not_dvd_index
  have e : CFSG.Blueprint.NativeSporadic.Carrier .ONan ≃* ↥Pv := onEquivPv
  refine k105SporAt_of_index (s := .ONan) hS₀ (fun Z hZ hZs m hm => ?_) e
  by_cases h3 : 3 ∣ m
  · exact Or.inr h3
  left
  have hZ' : Z.map Pv.subtype = onT := by
    refine ONK.eq_onT_of_solvable (Subgroup.map_subtype_le Z)
      (fun x hx => Subgroup.mem_map.2 ⟨⟨x, onT_le hx⟩, hZ (Subgroup.mem_subgroupOf.2 hx), rfl⟩)
      (Group.isSolvable_of_surjective (Pv.subtype.subgroupMap_surjective Z)) ?_
    rw [Subgroup.card_map_of_injective Pv.subtype_injective, hm, card_onT_subgroupOf]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact h3 h
    · norm_num at h
  have hc : Nat.card Z = 512 := by
    rw [← Subgroup.card_map_of_injective (K := Z) Pv.subtype_injective, hZ', card_onT]
  rw [hc, card_onT_subgroupOf] at hm
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
