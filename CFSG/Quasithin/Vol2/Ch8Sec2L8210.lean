module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFacts
public import CFSG.Quasithin.Vol2.Ch8Sec3InputZ
public import CFSG.Quasithin.Vol2.Ch7Lem761End
public import CFSG.Quasithin.Vol2.Ch8Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3
open scoped IsMulCommutative

section L8210

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem le_normalizer_of_case82 (h711n : Stmt7_1_1_normal) (hyp : Hyp7_0_2 G T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) :
    T ≤ Subgroup.normalizer (L : Set G) := by
  refine h711n G T L I hyp hc ?_
  rcases hrow with h | h | h | h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl h))))))))))

theorem inf_center_ne_bot_of_82 {N : Subgroup G} (hT : IsPGroup 2 T) (hNT : N ≤ T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) :
    N ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) ≠ ⊥ := by
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnormal : (N.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTN
  have hne : N.subgroupOf T ≠ ⊥ := by
    intro h
    apply hN
    rw [← Subgroup.map_subgroupOf_eq_of_le hNT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h
  have hmem : (y : G) ∈ N ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) := ⟨hy.1, y.2, hyC⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

theorem inf_centralizer_eq_bot_of_82 (h3109 : Stmt3_2_10_nine) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hyp : Hyp7_0_2 G T L I)
    (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hJ := thompsonJ_le_centralizer_fsuV h37 h38 h39 hyp hV hN
  have hVp : IsVplus T L I (fsuV T I) := Or.inr ⟨fun h => h.1 hL0.symm, rfl⟩
  obtain ⟨h1, -⟩ := h3109 G T L I (fsuV T I) hyp.fsu hVp hJ
  have hcl : conjClosure L T = L := hL0
  rw [hcl] at h1
  by_contra hne
  have hT : IsPGroup 2 ↥T := hyp.fsu.sylow.1
  have hTN : T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hLt := Subgroup.mem_normalizer_iff.mp (hTL ht)
    constructor
    · rintro ⟨hxT, hxC⟩
      refine ⟨T.mul_mem (T.mul_mem ht hxT) (T.inv_mem ht), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have hl' : t⁻¹ * l * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTL ht)) l).mp hl
        simpa using this
      have h2 := Subgroup.mem_centralizer_iff.mp hxC _ hl'
      calc l * (t * x * t⁻¹) = t * ((t⁻¹ * l * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * l * t)) * t⁻¹ := by rw [h2]
        _ = t * x * t⁻¹ * l := by group
    · rintro ⟨hxT, hxC⟩
      have hx' : x = t⁻¹ * (t * x * t⁻¹) * t := by group
      refine ⟨?_, ?_⟩
      · rw [hx']
        exact T.mul_mem (T.mul_mem (T.inv_mem ht) hxT) ht
      · refine Subgroup.mem_centralizer_iff.mpr ?_
        intro l hl
        have hl' : t * l * t⁻¹ ∈ L := (hLt l).mp hl
        have h2 := Subgroup.mem_centralizer_iff.mp hxC _ hl'
        calc l * x = t⁻¹ * ((t * l * t⁻¹) * (t * x * t⁻¹)) * t := by group
          _ = t⁻¹ * ((t * x * t⁻¹) * (t * l * t⁻¹)) * t := by rw [h2]
          _ = x * l := by group
  have h2 := inf_center_ne_bot_of_82 hT inf_le_left hTN hne
  set N := T ⊓ Subgroup.centralizer (L : Set G) ⊓ (T ⊓ Subgroup.centralizer (T : Set G)) with hNdef
  have hNp : IsPGroup 2 ↥N := hT.to_le (inf_le_left.trans inf_le_left)
  have hNc : 2 ∣ Nat.card ↥N := by
    rcases hNp.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) h2
    · exact h
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2 hNc
  have hyN : (y : G) ∈ N := y.2
  have hy2 : (y : G) ^ 2 = 1 := by
    have := pow_orderOf_eq_one y
    rw [hy] at this
    exact congrArg Subtype.val this
  have hmem : (y : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) :=
    ⟨Subgroup.subset_closure ⟨hyN.2, hy2⟩, hyN.1.2⟩
  rw [h1, Subgroup.mem_bot] at hmem
  have hy1 : y = 1 := Subtype.ext hmem
  rw [hy1, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem exists_fixT_eq_zpowers_of_82 (hfix : HFixSylow82) (hyp : Hyp7_0_2 G T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hV : IsElemAbelian 2 (fsuV T I)) (hrow : Case8_2 T L I)
    (hn1 : ∀ n : ℕ, Row711L3Nine T L I n → n = 1) :
    ∃ z : G, orderOf z = 2 ∧
      fsuV T I ⊓ Subgroup.centralizer (T : Set G) = Subgroup.zpowers z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := hyp.fsu
  have hT := isSylowIn_top_of_fsu hfsu
  have hTL₀ : T ≤ Subgroup.normalizer (fsuL0 T L : Set G) := le_normalizer_conjClosure L T
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_normalizer_conjClosure I T
  have hmono : ∀ {H K : Subgroup G}, H ≤ K → autOn H (fsuV T I) ≤ autOn K (fsuV T I) :=
    fun hHK => Subgroup.map_mono fun x hx => hHK hx
  have hS := card_autOn_inf_of_sylow hT hTL₀ hTV
  have hmod : BinaryNineTensor (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ 1 ∨
      MathieuCode22 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ ∨
      MathieuCode24 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ ∨
      MathieuCocode24 (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I)) ⊤ ⊥ := by
    rcases hrow with ⟨n, hn⟩ | h | h | h
    · have h1 := hn1 n hn
      subst h1
      exact Or.inl hn.2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  have hle0 := hfix ↥(fsuV T I) (autOn (fsuL0 T L) (fsuV T I))
    (autOn (T ⊓ fsuL0 T L) (fsuV T I)) hmod (hmono inf_le_right) hS
  have hle : Nat.card ↥(fixV (autOn T (fsuV T I))) ≤ 2 := by
    have hsub : fixV (autOn T (fsuV T I)) ≤ fixV (autOn (T ⊓ fsuL0 T L) (fsuV T I)) :=
      fun v hv x hx => hv x (hmono inf_le_left hx)
    exact (Subgroup.card_le_of_le hsub).trans hle0
  have hA2 : IsPGroup 2 ↥(autOn T (fsuV T I)) :=
    (hfsu.sylow.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTV).symm).map _
  have hcong := hA2.card_modEq_card_fixedPoints ↥(fsuV T I)
  have hVeven : 2 ∣ Nat.card ↥(fsuV T I) := by
    rcases (isPGroup_of_isElemAbelian_two hV).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) (fsuV_ne_bot hfsu)
    · exact h
  have hfixeq : Nat.card ↑(MulAction.fixedPoints ↥(autOn T (fsuV T I)) ↥(fsuV T I)) =
      Nat.card ↥(fixV (autOn T (fsuV T I))) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h x hx => h ⟨x, hx⟩, fun h a => h a.1 a.2⟩)
  rw [hfixeq] at hcong
  have hpos : 0 < Nat.card ↥(fixV (autOn T (fsuV T I))) := Nat.card_pos
  have hfix2 : Nat.card ↥(fixV (autOn T (fsuV T I))) = 2 := by
    have h1 := Nat.ModEq.symm hcong
    unfold Nat.ModEq at h1
    obtain ⟨c, hc'⟩ := hVeven
    rw [hc'] at h1
    omega
  have hCeq : fsuV T I ⊓ Subgroup.centralizer (T : Set G) =
      (fixV (autOn T (fsuV T I))).map (fsuV T I).subtype := by
    ext x
    constructor
    · rintro ⟨hxV, hxC⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      rintro _ ⟨⟨t, htN⟩, htT, rfl⟩
      apply Subtype.ext
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
      change t * x * t⁻¹ = x
      rw [Subgroup.mem_centralizer_iff.mp hxC t htT, mul_inv_cancel_right]
    · rintro ⟨⟨x, hxV⟩, hfx, rfl⟩
      refine ⟨hxV, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
      have h1 := hfx (conjAct (fsuV T I) ⟨t, hTV ht⟩) ⟨⟨t, hTV ht⟩, ht, rfl⟩
      have h2 := congrArg Subtype.val h1
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h2
      change t * x * t⁻¹ = x at h2
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x * t := by rw [h2]
  have hCcard : Nat.card ↥(fsuV T I ⊓ Subgroup.centralizer (T : Set G)) = 2 := by
    rw [hCeq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hfix2]
  obtain ⟨z, hzC, hz1⟩ : ∃ z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : fsuV T I ⊓ Subgroup.centralizer (T : Set G) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hCcard
    omega
  have hz2 : orderOf z = 2 := by
    have h1 := Subgroup.orderOf_dvd_natCard _ hzC
    rw [hCcard] at h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  refine ⟨z, hz2, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzC)
  rw [hCcard, Nat.card_zpowers, hz2]

end L8210

end CFSG.Quasithin.H13
