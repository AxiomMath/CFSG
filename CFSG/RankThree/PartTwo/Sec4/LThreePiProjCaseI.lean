module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} [hLn : L.Normal]
  {K : Type} [Field K] {p f : ℕ} {π : Bool}

omit [Finite G] in
theorem mem_range_inf_of_mem_sup (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hE : ∀ a ∈ A ⊓ L, ∃ y, IsPGLAtP e a y)
    {a : G} (ha : a ∈ A) (haLC : a ∈ L ⊔ Subgroup.centralizer (L : Set G)) {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) :
    (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq (A ⊓ L) hE).range := by
  have hCn : (Subgroup.centralizer (L : Set G)).Normal := inferInstance
  obtain ⟨l, hl, u, hu, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp haLC
  have hlA := mem_of_mul_inv_mem_centralizer hA hLC ha hl (hCn.conj_mem u hu l)
  have hly : IsPGLAtP e l (y * 1) := by
    have h := isPGLAtP_mul e hy (isPGLAtP_of_mem_centralizer e (inv_mem hu))
    rwa [mul_inv_cancel_right] at h
  rw [mul_one] at hly
  exact mk_mem_range_pglHomP (Subgroup.mem_inf.mpr ⟨hlA, hl⟩) hly

theorem exists_mem_inf_of_type3 (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] {e : L ≃* projImage (slPi π 3 (p ^ f) K)}
    {A : Subgroup G} (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : Nat.card A = 27) (hLC : L ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c : G}
    (hc3 : orderOf c = 3) (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) {a : G} (ha : a ∈ A) {y : GL (Fin 3) K}
    (hy : IsPGLAtP e a y) (hy3 : Type123 π (p ^ f) K y 3) :
    ∃ v ∈ A ⊓ L, v ≠ 1 := by
  classical
  have : NeZero (qSubPi π (p ^ f)) := ⟨qSubPi_ne_zero hK hq⟩
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have ha3 : a ^ 3 = 1 := hA.1.2 a ha
  have haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set G) := fun h =>
    not_inner_of_type3 hK hq hy.1 hy3 (exists_inner_of_mem_supP hK hq h hy)
  have hac : a ∉ Subgroup.zpowers c := by
    intro h
    have : a ∈ A ⊓ Subgroup.centralizer (L : Set G) := by rw [hAc]; exact h
    exact haLC (Subgroup.mem_sup_right this.2)
  have hca9 := card_zpowers_sup_zpowers ha3 hc3 hac (hAcomm a ha c hcAC.1)
  obtain ⟨x, hxA, hxca⟩ : ∃ x ∈ A, x ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers a := by
    by_contra hne
    push Not at hne
    have := Subgroup.card_le_of_le (show A ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers a from
      fun x hx => hne x hx)
    omega
  obtain ⟨z, hz⟩ := hpgl x hxA
  have hdz := det_mem_rootsOfUnity hK hz.1
  have hdy := det_mem_rootsOfUnity hK hy.1
  have hnc : ∀ μ : rootsOfUnity (qSubPi π (p ^ f)) K,
      μ ^ 3 ≠ ⟨GeneralLinearGroup.det y, hdy⟩ := by
    intro μ hμ
    apply not_inner_of_type3 hK hq hy.1 hy3
    have h1 : ((μ : Kˣ) : K) ^ 3 = (y : Matrix (Fin 3) (Fin 3) K).det := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hμ]
      rfl
    obtain ⟨l, hl, -, hyl⟩ := exists_inner_of_det_eq_cube hK hy.1
      ((scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) h1.symm
    exact ⟨l, hl, fun m _ => hyl m⟩
  obtain ⟨k, μ, hkμ⟩ := exists_mul_pow_eq_cube (⟨GeneralLinearGroup.det z, hdz⟩ :
    rootsOfUnity (qSubPi π (p ^ f)) K) hnc
  have hwH : z * y ^ k ∈ glPi π 3 (p ^ f) K := mul_mem hz.1 (pow_mem hy.1 k)
  have hwdet : ((z * y ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det =
      ((μ : Kˣ) : K) ^ 3 := by
    have h1 := congrArg (fun t : rootsOfUnity (qSubPi π (p ^ f)) K => ((t : Kˣ) : K)) hkμ
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val,
      GeneralLinearGroup.val_det_apply] at h1
    rw [Units.val_mul, Matrix.det_mul, Units.val_pow_eq_pow_val, Matrix.det_pow]
    exact h1
  obtain ⟨l, hl, -, hwl⟩ := exists_inner_of_det_eq_cube hK hwH
    ((scalar_mem_glPi_iff hK (μ : Kˣ)).mpr μ.2) hwdet
  have hw : IsPGLAtP e (x * a ^ k) (z * y ^ k) := isPGLAtP_mul e hz (isPGLAtP_pow hy k)
  obtain ⟨v, hv, -, hwv⟩ := exists_inner_mem_of_innerP hK hq hw hl (fun m _ => hwl m)
  have hbA : x * a ^ k ∈ A := mul_mem hxA (pow_mem ha k)
  have hvA := mem_of_mul_inv_mem_centralizer hA hLC hbA hv hwv
  refine ⟨v, Subgroup.mem_inf.mpr ⟨hvA, hv⟩, fun hv1 => hxca ?_⟩
  rw [hv1, inv_one, mul_one] at hwv
  have hbc : x * a ^ k ∈ Subgroup.zpowers c := hAc ▸ Subgroup.mem_inf.mpr ⟨hbA, hwv⟩
  have : x = x * a ^ k * (a ^ k)⁻¹ := by group
  rw [this]
  exact mul_mem (Subgroup.mem_sup_left hbc) (inv_mem (pow_mem (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers a)) k))

theorem alt412_of_pgl (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    [Group.IsPerfect (projImage (slPi π 3 (p ^ f) K))] (hθ : aschbacherSolvableCore 3 L = ⊥)
    (e : L ≃* projImage (slPi π 3 (p ^ f) K)) {A : Subgroup G}
    (hA : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (hA27 : 27 ≤ Nat.card A) {c : G} (hc3 : orderOf c = 3)
    (hAc : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers c)
    (hpgl : ∀ a ∈ A, ∃ y, IsPGLAtP e a y) : Alt412 L A c := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have h3K := hK.three_ne_zero hq
  have hLC := inf_centralizer_eq_bot_proj hK hq e
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hRcomm := range_pglHomP_comm (hK := hK) (hq := hq) (hA' := hpgl) hAcomm
  have hRexp := range_pglHomP_pow (hK := hK) (hq := hq) (hA' := hpgl) hA3
  have hcardA := card_eq_card_inf_mul_card_rangeP (hK := hK) (hq := hq) (hA' := hpgl)
  rw [hAc, Nat.card_zpowers, hc3] at hcardA
  have hR9 := card_le_nine_of_comm h3K hτ hτ1 _ hRcomm hRexp
  have hA27' : Nat.card A = 27 := by omega
  have hR9' : Nat.card (pglHomP hK hq A hpgl).range = 9 := by omega
  have hbot : ∀ x ∈ A ⊓ L, x ≠ 1 → x ∉ Subgroup.centralizer (L : Set G) := fun x hx hx1 hxC =>
    hx1 (Subgroup.mem_bot.mp (hLC ▸ Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hxC⟩))
  rcases frame_or_heis h3K hτ hτ1 _ hRcomm hRexp (by omega) with ⟨b, hb, hd, -⟩ |
    ⟨y₁, y₂, hy₁, hy₂, ζ, hζ1, hζ⟩
  ·
    exact Or.inr (Or.inl ⟨hA27', isTypeCOn_of_frameP hK hq hθ hpgl hA3 hR9' hb hd⟩)
  have htype : ∀ a ∈ A, a ∉ Subgroup.centralizer (L : Set G) → ∀ y, IsPGLAtP e a y →
      Type123 π (p ^ f) K y 1 ∨ Type123 π (p ^ f) K y 3 := fun a ha haC y hy =>
    type13_of_heisP hK hq hRcomm hy₁ hy₂ hζ1 hζ hy.1 (not_mem_zPi_of_isPGLAtP hK hq haC hy)
      (pow_three_mem_zPiP hK hq (hA3 a ha) hy) (mk_mem_range_pglHomP ha hy)
  have hcardALC := card_inf_sup_centralizer hA hLC hc3 hAc
  by_cases h3 : ∃ a ∈ A, ∃ y, IsPGLAtP e a y ∧ Type123 π (p ^ f) K y 3
  ·
    obtain ⟨a, ha, ya, hya, hya3⟩ := h3
    refine Or.inr (Or.inr (Or.inl ⟨hA27', ⟨a, ha, inducesTypeOn_of_isPGLAtP hK hq hθ hya hya3⟩,
      ?_⟩))
    have haLC : a ∉ L ⊔ Subgroup.centralizer (L : Set G) := fun h =>
      not_inner_of_type3 hK hq hya.1 hya3 (exists_inner_of_mem_supP hK hq h hya)
    obtain ⟨v, hv, hv1⟩ := exists_mem_inf_of_type3 hK hq hA hA27' hLC hc3 hAc hpgl ha hya hya3
    have hdvd : Nat.card (A ⊓ L : Subgroup G) * 3 ∣ 27 := by
      rw [← hcardALC, ← hA27']
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne9 : Nat.card (A ⊓ L : Subgroup G) ≠ 9 := by
      intro h9
      apply haLC
      have hle : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcardALC, h9, hA27'])
      rw [← hle] at ha
      exact (Subgroup.mem_inf.mp ha).2
    have hne1 : Nat.card (A ⊓ L : Subgroup G) ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      rw [h1] at hv
      exact hv1 (Subgroup.mem_bot.mp hv)
    have hAL3 : Nat.card (A ⊓ L : Subgroup G) = 3 := by
      have h9 : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 2 :=
        Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 3) (by norm_num; exact hdvd)
      obtain ⟨m, hm, hmeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9
      interval_cases m
      · exact absurd hmeq hne1
      · exact hmeq
      · exact absurd hmeq hne9
    have hvo : orderOf v = 3 := orderOf_eq_prime (hA3 v (Subgroup.mem_inf.mp hv).1) hv1
    have hALv : A ⊓ L = Subgroup.zpowers v := by
      symm
      exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hv)
        (by rw [hAL3, Nat.card_zpowers, hvo])
    refine ⟨v, hALv, hvo, ?_⟩
    obtain ⟨y, hy⟩ := hpgl v (Subgroup.mem_inf.mp hv).1
    have hvC := hbot v hv hv1
    refine inducesTypeOn_of_isPGLAtP hK hq hθ hy ((htype v (Subgroup.mem_inf.mp hv).1 hvC y
      hy).resolve_right fun h3 => ?_)
    exact not_inner_of_type3 hK hq hy.1 h3 (exists_inner_of_mem_supP hK hq
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mp hv).2) hy)
  ·
    have h1 : ∀ a ∈ A, a ∉ Subgroup.centralizer (L : Set G) → ∀ y, IsPGLAtP e a y →
        Type123 π (p ^ f) K y 1 := fun a ha haC y hy =>
      (htype a ha haC y hy).resolve_right fun h => h3 ⟨a, ha, y, hy, h⟩
    have hALC : A ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
      intro a ha
      by_cases haC : a ∈ Subgroup.centralizer (L : Set G)
      · exact Subgroup.mem_sup_right haC
      · obtain ⟨y, hy⟩ := hpgl a ha
        obtain ⟨l, hl, hyl⟩ := exists_inner_of_type1 hK hq hy.1 (h1 a ha haC y hy)
        obtain ⟨v, hv, -, hav⟩ := exists_inner_mem_of_innerP hK hq hy hl hyl
        have : a = a * v⁻¹ * v := by group
        rw [this]
        exact mul_mem (Subgroup.mem_sup_right hav) (Subgroup.mem_sup_left hv)
    have hAeq : A ⊓ (L ⊔ Subgroup.centralizer (L : Set G)) = A := inf_eq_left.mpr hALC
    rw [hAeq, hA27'] at hcardALC
    have hAL9 : Nat.card (A ⊓ L : Subgroup G) = 9 := by omega
    have hsup := inf_sup_centralizer_eq hA hLC hAc
    rw [hAeq] at hsup
    refine Or.inl ⟨hA27', ?_, ?_, ?_⟩
    · apply le_antisymm
      · rw [hsup]
        exact sup_le (sup_le (inf_le_right.trans le_sup_right) le_sup_left) le_sup_right
      · refine sup_le ?_ le_sup_right
        rw [← hAc]
        exact inf_le_left.trans le_sup_left
    · intro x hx hx1
      obtain ⟨y, hy⟩ := hpgl x (Subgroup.mem_inf.mp hx).1
      exact inducesTypeOn_of_isPGLAtP hK hq hθ hy (h1 x (Subgroup.mem_inf.mp hx).1
        (hbot x hx hx1) y hy)
    · have hE : ∀ a ∈ A ⊓ L, ∃ y, IsPGLAtP e a y := fun a ha => hpgl a (Subgroup.mem_inf.mp ha).1
      have hrange : ∀ y : GL (Fin 3) K, (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈
          (pglHomP hK hq A hpgl).range →
            (y : GL (Fin 3) K ⧸ StatedScalars (Fin 3) K) ∈ (pglHomP hK hq (A ⊓ L) hE).range := by
        intro y hy
        obtain ⟨⟨a, ha⟩, hay⟩ := hy
        obtain ⟨z, hz⟩ := hpgl a ha
        rw [pglHomP_apply ⟨a, ha⟩ hz] at hay
        rw [← hay]
        exact mem_range_inf_of_mem_sup hK hq hA hLC hE ha (hALC ha) hz
      exact transitive_of_range_heis hK hq inf_le_right hAL9
        (fun a ha b hb => hAcomm a (Subgroup.mem_inf.mp ha).1 b (Subgroup.mem_inf.mp hb).1)
        (fun a ha => hA3 a (Subgroup.mem_inf.mp ha).1) hE (hrange _ hy₁) (hrange _ hy₂) hζ1 hζ
        (fun x hx hx1 y hy => h1 x (Subgroup.mem_inf.mp hx).1 (hbot x hx hx1) y hy)

end CFSG.RankThree.PartTwo.Sec4
