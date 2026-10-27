module

public import CFSG.RankThree.PartTwo.Sec13.K135SFDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossFamLinear
public import CFSG.GroupTheory.WeirSylow.CrossRankLinear

public section

namespace CFSG.RankThree.PartTwo.Sec13.K135GL12

open CFSG CFSG.RankThree.PartTwo.Sec13.K135SF Subgroup

@[expose] def gl12Order : ℕ := 284280375831090647160439487256465538461866018719326087728634789888000

private theorem gl12kt1_card_GL_dvd {N : ℕ} (hN : N ≤ 12) :
    Nat.card (Matrix.GeneralLinearGroup (Fin N) (ZMod 3)) ∣
      gl12Order := by
  rw [Matrix.card_GL_field, ZMod.card]
  unfold gl12Order
  interval_cases N <;> decide +kernel

theorem gl12Data_card_dvd {S : Type} [Group S] [Finite S] (h : GL12Data S) :
    Nat.card S ∣ gl12Order := by
  obtain ⟨n, X, hXg, _, ρ, K, hK, hn, -, -, hker, -, ⟨e⟩, -⟩ := h
  have h1 : Nat.card S = K.index := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv]
  have h2 : K.index ∣ ρ.ker.index := Subgroup.index_dvd_of_le hker
  have h3 : ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
  have h4 : Nat.card ρ.range ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  rw [h3] at h2
  rw [h1]
  exact h2.trans (h4.trans (gl12kt1_card_GL_dvd hn))

theorem gl12_card_le_card_pTorsion_of_surjective {T E : Type*} [CommGroup T] [Finite T] [Group E]
    (π : T →* E) (hπ : Function.Surjective π) {p : ℕ} (hE : ∀ e : E, e ^ p = 1) :
    Nat.card E ≤ Nat.card {t : T // t ^ p = 1} := by
  have hle : (powMonoidHom p : T →* T).range ≤ π.ker := by
    intro x hx
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hE]
  have hdvd : π.ker.index ∣ (powMonoidHom p : T →* T).range.index :=
    Subgroup.index_dvd_of_le hle
  have hpos : 0 < (powMonoidHom p : T →* T).range.index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle2 : π.ker.index ≤ (powMonoidHom p : T →* T).range.index :=
    Nat.le_of_dvd hpos hdvd
  have hE_eq : Nat.card E = π.ker.index := by
    rw [Subgroup.index_ker, π.range_eq_top_of_surjective hπ, Subgroup.card_top]
  have hR : (powMonoidHom p : T →* T).range.index = Nat.card (powMonoidHom p : T →* T).ker := by
    have h1 : Nat.card (powMonoidHom p : T →* T).range * (powMonoidHom p : T →* T).range.index
        = Nat.card (powMonoidHom p : T →* T).ker * Nat.card (powMonoidHom p : T →* T).range := by
      rw [Subgroup.card_mul_index, Subgroup.card_ker_mul_card_range]
    have hpos' : 0 < Nat.card (powMonoidHom p : T →* T).range := Nat.card_pos
    rw [mul_comm (Nat.card (powMonoidHom p : T →* T).ker)] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos' h1
  have hK : Nat.card (powMonoidHom p : T →* T).ker = Nat.card {t : T // t ^ p = 1} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun t => by simp [MonoidHom.mem_ker])
  rw [hE_eq]
  calc π.ker.index ≤ (powMonoidHom p : T →* T).range.index := hle2
    _ = Nat.card (powMonoidHom p : T →* T).ker := hR
    _ = Nat.card {t : T // t ^ p = 1} := hK

theorem gl12_exists_pSubgroup_map_eq {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    {p : ℕ} [Fact p.Prime] (Q : Subgroup (X ⧸ K)) (hQ : IsPGroup p Q) :
    ∃ T : Subgroup X, IsPGroup p T ∧ T.map (QuotientGroup.mk' K) = Q := by
  let W : Subgroup X := Q.comap (QuotientGroup.mk' K)
  let f : W →* Q :=
    { toFun := fun w => ⟨QuotientGroup.mk' K (w : X), w.2⟩
      map_one' := Subtype.ext (map_one (QuotientGroup.mk' K))
      map_mul' := fun a b => Subtype.ext (map_mul (QuotientGroup.mk' K) (a : X) (b : X)) }
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (q : X ⧸ K)
    have hxW : x ∈ W := by
      show QuotientGroup.mk' K x ∈ Q
      rw [QuotientGroup.mk'_apply, hx]
      exact q.2
    exact ⟨⟨x, hxW⟩, Subtype.ext (by
      show QuotientGroup.mk' K x = (q : X ⧸ K)
      rw [QuotientGroup.mk'_apply, hx])⟩
  obtain ⟨P0⟩ : Nonempty (Sylow p W) := Sylow.nonempty
  have hPf : ((P0.mapSurjective hf : Sylow p Q) : Subgroup Q) = Subgroup.map f (P0 : Subgroup W) :=
    Sylow.coe_mapSurjective hf P0
  have htop : ((P0.mapSurjective hf : Sylow p Q) : Subgroup Q) = ⊤ :=
    ((P0.mapSurjective hf).is_maximal' (hQ.of_equiv Subgroup.topEquiv.symm) le_top).symm
  refine ⟨(P0 : Subgroup W).map W.subtype, P0.isPGroup'.map W.subtype, ?_⟩
  ext q
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨w, _, rfl⟩ := Subgroup.mem_map.mp ht
    exact w.2
  · intro hq
    have hmem : (⟨q, hq⟩ : Q) ∈ Subgroup.map f (P0 : Subgroup W) := by
      rw [← hPf, htop]
      exact Subgroup.mem_top _
    obtain ⟨w, hwP0, hfw⟩ := Subgroup.mem_map.mp hmem
    have hwq : QuotientGroup.mk' K (w : X) = q := congrArg Subtype.val hfw
    exact Subgroup.mem_map.mpr ⟨(w : X), Subgroup.mem_map.mpr ⟨w, hwP0, rfl⟩, hwq⟩

private theorem gl12kt4_three_pow_eq_one_iff (p j : ℕ) [Fact p.Prime] :
    (3 : ZMod p) ^ j = 1 ↔ p ∣ 3 ^ j - 1 := by
  have h1 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
  have h2 : ((3 ^ j - 1 : ℕ) : ZMod p) = (3 : ZMod p) ^ j - 1 := by
    rw [Nat.cast_sub h1]
    simp
  rw [← ZMod.natCast_eq_zero_iff, h2, sub_eq_zero]

private theorem gl12kt4_three_ne_zero (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    (3 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 3 p).1 h'
  have hle := Nat.le_of_dvd (by norm_num) hd
  omega

private theorem gl12kt4_orderOf_pos (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) :
    0 < orderOf (3 : ZMod p) := by
  rw [orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
  exact ⟨p - 1, by omega, ZMod.pow_card_sub_one_eq_one (gl12kt4_three_ne_zero p hp7)⟩

private theorem gl12kt4_not_dvd {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hp13 : p ≠ 13) :
    ¬ p ∣ 2 ∧ ¬ p ∣ 8 ∧ ¬ p ∣ 26 ∧ ¬ p ∣ 80 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  all_goals
    have hle := Nat.le_of_dvd (by norm_num) h
    first
    | omega
    | (interval_cases p <;> first | omega | norm_num at hp)

theorem gl12_three_orderOf_facts {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) :
    (p ≠ 13 → 5 ≤ orderOf (3 : ZMod p)) ∧ (p = 13 → orderOf (3 : ZMod p) = 3) := by
  have hp : p.Prime := Fact.out
  have hpos := gl12kt4_orderOf_pos p hp7
  have hpow : (3 : ZMod p) ^ orderOf (3 : ZMod p) = 1 := pow_orderOf_eq_one _
  refine ⟨fun hp13 => ?_, fun hp13 => ?_⟩
  · by_contra hlt
    have hdvd := (gl12kt4_three_pow_eq_one_iff p _).1 hpow
    obtain ⟨hn1, hn2, hn3, hn4⟩ := gl12kt4_not_dvd hp hp7 hp13
    have hk : orderOf (3 : ZMod p) = 1 ∨ orderOf (3 : ZMod p) = 2 ∨
        orderOf (3 : ZMod p) = 3 ∨ orderOf (3 : ZMod p) = 4 := by omega
    rcases hk with hk | hk | hk | hk <;> rw [hk] at hdvd
    · exact hn1 (by simpa using hdvd)
    · exact hn2 (by simpa using hdvd)
    · exact hn3 (by simpa using hdvd)
    · exact hn4 (by simpa using hdvd)
  · subst hp13
    apply orderOf_eq_prime
    · exact (gl12kt4_three_pow_eq_one_iff 13 3).2 (by norm_num)
    · intro h
      have h1 : (3 : ZMod 13) ^ 1 = 1 := by rw [pow_one]; exact h
      have h2 := (gl12kt4_three_pow_eq_one_iff 13 1).1 h1
      norm_num at h2

private def gl12kt4_torsion {G : Type*} [Group G] (Q : Subgroup G) (hQ : IsMulCommutative Q)
    (p : ℕ) : Subgroup G where
  carrier := {x | x ∈ Q ∧ x ^ p = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    have h2 : (⟨a, ha⟩ : Q) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := isMulCommutative_iff.1 hQ _ _
    have hab : a * b = b * a := congrArg Subtype.val h2
    have hc : Commute a b := hab
    refine ⟨Q.mul_mem ha hb, ?_⟩
    rw [hc.mul_pow, ha', hb', one_mul]
  one_mem' := ⟨Q.one_mem, one_pow p⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Q.inv_mem ha, ?_⟩
    rw [inv_pow, ha', inv_one]

theorem gl12_pSubgroup_comm_and_torsion {p n : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p) (hn : n ≤ 12)
    (Q : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 3))) (hQ : IsPGroup p Q) :
    IsMulCommutative Q ∧ Nat.card {x : Q // x ^ p = 1} ≤ p ^ (n / orderOf (3 : ZMod p)) := by
  have hp : p.Prime := Fact.out
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have h3 : ¬ p ∣ Nat.card (ZMod 3) := by
    rw [Nat.card_zmod]
    intro hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    omega
  have hpos := gl12kt4_orderOf_pos p hp7
  have he3 : 3 ≤ orderOf (3 : ZMod p) := by
    by_cases h13 : p = 13
    · have := (gl12_three_orderOf_facts hp7).2 h13
      omega
    · have := (gl12_three_orderOf_facts hp7).1 h13
      omega
  have hpeq : ∀ j : ℕ, p ∣ Nat.card (ZMod 3) ^ j - 1 ↔ orderOf (3 : ZMod p) ∣ j := by
    intro j
    rw [Nat.card_zmod, orderOf_dvd_iff_pow_eq_one, gl12kt4_three_pow_eq_one_iff p j]
  have hne : n / orderOf (3 : ZMod p) < p := by
    have h1 : n / orderOf (3 : ZMod p) ≤ n / 3 := Nat.div_le_div_left he3 (by norm_num)
    omega
  have hcomm : IsMulCommutative Q :=
    CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_of_isPGroup_GL_matrix hp2 h3 hpos hpeq
      hne hQ
  refine ⟨hcomm, ?_⟩
  obtain ⟨E, hEmem⟩ : ∃ E : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 3)),
      ∀ x : Matrix.GeneralLinearGroup (Fin n) (ZMod 3), x ∈ E ↔ x ∈ Q ∧ x ^ p = 1 :=
    ⟨gl12kt4_torsion Q hcomm p, fun x => Iff.rfl⟩
  have hEc : IsMulCommutative E := by
    refine isMulCommutative_iff.2 ?_
    intro a b
    apply Subtype.ext
    have h2 : (⟨a.1, ((hEmem a.1).1 a.2).1⟩ : Q) * ⟨b.1, ((hEmem b.1).1 b.2).1⟩ =
        ⟨b.1, ((hEmem b.1).1 b.2).1⟩ * ⟨a.1, ((hEmem a.1).1 a.2).1⟩ :=
      isMulCommutative_iff.1 hcomm _ _
    have h3 := congrArg Subtype.val h2
    exact h3
  have hEp : ∀ x ∈ E, x ^ p = 1 := fun x hx => ((hEmem x).1 hx).2
  have hEelem : CFSG.Open.IsElemAbelian p E := ⟨hEc, hEp⟩
  have hEpg : IsPGroup p E := by
    refine isPGroup_iff_pow_pow_eq_one.2 (fun g => ⟨1, ?_⟩)
    rw [pow_one]
    apply Subtype.ext
    have h := hEp g.1 g.2
    simpa using h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hEpg
  have hkle : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 3))) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hEelem hk
  have hrank : CFSG.Open.pRank p (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 3))) =
      n / orderOf (3 : ZMod p) := by
    rw [CFSG.GroupTheory.WeirSylow.pRank_top_gl_eq (ι := Fin n) hp2 h3]
    simp only [Fintype.card_fin, Nat.card_zmod, Nat.cast_ofNat]
  have hfin : k ≤ n / orderOf (3 : ZMod p) := hkle.trans_eq hrank
  have hsub : ∀ y : {x : Q // x ^ p = 1}, y.1.1 ^ p = 1 := fun y => by
    have h := congrArg Subtype.val y.2
    simpa using h
  have hcardE : Nat.card {x : Q // x ^ p = 1} = Nat.card E := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun y => ⟨y.1.1, (hEmem y.1.1).2 ⟨y.1.2, hsub y⟩⟩
        invFun := fun x => ⟨⟨x.1, ((hEmem x.1).1 x.2).1⟩,
          Subtype.ext (by simpa using ((hEmem x.1).1 x.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcardE, hk]
  exact Nat.pow_le_pow_right hp.pos hfin

theorem gl12_exists_surj_from_gl {S X : Type} [Group S] [Group X] [Finite X] {n : ℕ}
    (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) (K : Subgroup X) [K.Normal]
    (hker : ρ.ker ≤ K) (e : X ⧸ K ≃* S) {p : ℕ} [Fact p.Prime]
    (E : Subgroup S) (hE : IsPGroup p E) :
    ∃ (C : Subgroup (Matrix.GeneralLinearGroup (Fin n) (ZMod 3))) (π : C →* S),
      IsPGroup p C ∧ π.range = E := by
  let Q : Subgroup (X ⧸ K) := E.map e.symm.toMonoidHom
  have hQ : IsPGroup p Q := hE.map e.symm.toMonoidHom
  obtain ⟨T, hT, hTQ⟩ := gl12_exists_pSubgroup_map_eq K Q hQ
  let φ : T →* S := e.toMonoidHom.comp ((QuotientGroup.mk' K).comp T.subtype)
  let ρT : T →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3) := ρ.comp T.subtype
  have hsurj : Function.Surjective ρT.rangeRestrict := ρT.rangeRestrict_surjective
  have hkerle : ρT.rangeRestrict.ker ≤ φ.ker := by
    intro t ht
    have h1 : ρT t = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
    have h2 : (t : X) ∈ ρ.ker := h1
    have h3 : (t : X) ∈ K := hker h2
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff (t : X)).mpr h3, map_one]
  let π : ρT.range →* S := (MonoidHom.liftOfSurjective ρT.rangeRestrict hsurj) ⟨φ, hkerle⟩
  have hπ : ∀ t : T, π (ρT.rangeRestrict t) = φ t := fun t => by
    exact MonoidHom.liftOfRightInverse_comp_apply ρT.rangeRestrict (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨φ, hkerle⟩ t
  refine ⟨ρT.range, π, ?_, ?_⟩
  · have : IsPGroup p (T.map ρ) := hT.map ρ
    have hr : ρT.range = T.map ρ := by
      ext g
      simp [ρT, MonoidHom.mem_range, Subgroup.mem_map]
    rw [hr]
    exact this
  · ext s
    constructor
    · rintro ⟨c, rfl⟩
      obtain ⟨t, rfl⟩ := hsurj c
      rw [hπ]
      have : (QuotientGroup.mk' K (t : X)) ∈ Q := by
        rw [← hTQ]
        exact Subgroup.mem_map.mpr ⟨t, t.2, rfl⟩
      obtain ⟨s', hs', hs'e⟩ := Subgroup.mem_map.mp this
      have : φ t = s' := by
        simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype]
        rw [← hs'e]
        simp
      rw [this]
      exact hs'
    · intro hs
      have : e.symm s ∈ Q := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
      rw [← hTQ] at this
      obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp this
      refine ⟨ρT.rangeRestrict ⟨t, ht⟩, ?_⟩
      rw [hπ]
      simp only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [show (QuotientGroup.mk' K) t = e.symm s from hte]
      simp

theorem gl12Sec_comm {S X : Type} [Group S] [Group X] [Finite X] {n : ℕ} (hn : n ≤ 12)
    (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) (K : Subgroup X) [K.Normal]
    (hker : ρ.ker ≤ K) (e : X ⧸ K ≃* S) {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (E : Subgroup S) (hE : IsPGroup p E) : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
  obtain ⟨C, π, hC, hπ⟩ := gl12_exists_surj_from_gl ρ K hker e E hE
  have hcomm := (gl12_pSubgroup_comm_and_torsion hp7 hn C hC).1
  intro a ha b hb
  rw [← hπ] at ha hb
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  rw [← map_mul, ← map_mul, hcomm.is_comm.comm c d]

theorem gl12Sec_card_le {S X : Type} [Group S] [Group X] [Finite X] {n : ℕ} (hn : n ≤ 12)
    (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) (K : Subgroup X) [K.Normal]
    (hker : ρ.ker ≤ K) (e : X ⧸ K ≃* S) {p : ℕ} [Fact p.Prime] (hp7 : 7 ≤ p)
    (E : Subgroup S) (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ (n / orderOf (3 : ZMod p)) := by
  have hEp : IsPGroup p E := fun x => ⟨1, by
    have := hE x.1 x.2
    exact Subtype.ext (by simpa using this)⟩
  obtain ⟨C, π, hC, hπ⟩ := gl12_exists_surj_from_gl ρ K hker e E hEp
  obtain ⟨hcomm, htors⟩ := gl12_pSubgroup_comm_and_torsion hp7 hn C hC
  letI : CommGroup C := { (inferInstance : Group C) with mul_comm := fun a b => hcomm.is_comm.comm a b }
  let π' : C →* E := π.codRestrict E (fun c => by rw [← hπ]; exact ⟨c, rfl⟩)
  have hπ' : Function.Surjective π' := by
    intro x
    have : (x : S) ∈ π.range := by rw [hπ]; exact x.2
    obtain ⟨c, hc⟩ := this
    exact ⟨c, Subtype.ext hc⟩
  have h := gl12_card_le_card_pTorsion_of_surjective π' hπ' (p := p) (fun x => Subtype.ext (hE x.1 x.2))
  exact h.trans htors

end CFSG.RankThree.PartTwo.Sec13.K135GL12
