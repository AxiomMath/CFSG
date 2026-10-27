module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

private abbrev projFst : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
    alternatingGroup (Fin 5) :=
  MonoidHom.fst _ _

private abbrev projSnd : alternatingGroup (Fin 5) × alternatingGroup (Fin 5) →*
    alternatingGroup (Fin 5) :=
  MonoidHom.snd _ _

private theorem isElemAbelian_bot_aux {G : Type*} [Group G] (p : ℕ) :
    CFSG.Open.IsElemAbelian p (⊥ : Subgroup G) :=
  ⟨⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])⟩⟩,
    fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩

private theorem exists_isPGroup_card_dvd_of_le_pRank {G : Type*} [Group G] [Finite G]
    {p k : ℕ} (hp : p.Prime) (H : Subgroup G) (hk : k ≤ CFSG.Open.pRank p H) :
    ∃ E : Subgroup G, E ≤ H ∧ IsPGroup p E ∧ p ^ k ∣ Nat.card E := by
  have hne : ({m | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ m} : Set ℕ).Nonempty :=
    ⟨0, ⊥, bot_le, isElemAbelian_bot_aux p, by simp⟩
  have hbdd : BddAbove ({m | ∃ E : Subgroup G, E ≤ H ∧ CFSG.Open.IsElemAbelian p E ∧
      Nat.card E = p ^ m} : Set ℕ) := by
    refine ⟨Nat.card G, ?_⟩
    rintro m ⟨E, -, -, hEcard⟩
    have h1 : m < p ^ m := Nat.lt_pow_self hp.one_lt
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  obtain ⟨E, hEH, hEea, hEcard⟩ := Nat.sSup_mem hne hbdd
  exact ⟨E, hEH, IsPGroup.of_card hEcard, by rw [hEcard]; exact pow_dvd_pow p hk⟩

private theorem isSolvable_of_card_eq_five_or_ten {X : Type*} [Group X] [Finite X]
    (h : Nat.card X = 5 ∨ Nat.card X = 10) : Group.IsSolvable X := by
  have hFact5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hFact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h with h5 | h10
  · have hcycX : IsCyclic X := isCyclic_of_prime_card (p := 5) h5
    infer_instance
  · have hdvd : 5 ^ 1 ∣ Nat.card X := by rw [h10]; norm_num
    obtain ⟨P, hPcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := X) 5 (n := 1) hdvd
    have hpindex : P.index = 2 := by
      have hmul := P.index_mul_card
      rw [hPcard, h10] at hmul
      omega
    have hPnorm : P.Normal := Subgroup.normal_of_index_eq_two hpindex
    have hPsolv : Group.IsSolvable P := by
      have hcycP : IsCyclic P := isCyclic_of_prime_card (p := 5) hPcard
      infer_instance
    have hQsolv : Group.IsSolvable (X ⧸ P) := by
      have hqcard : Nat.card (X ⧸ P) = 2 := by
        rw [← Subgroup.index_eq_card, hpindex]
      have hcycQ : IsCyclic (X ⧸ P) := isCyclic_of_prime_card (p := 2) hqcard
      infer_instance
    exact Group.isSolvable_of_subgroup_quotient P

private theorem eq_top_of_isPerfect_of_dvd_card_five
    {V : Subgroup (alternatingGroup (Fin 5))}
    (hV : Group.IsPerfect V) (h5 : 5 ∣ Nat.card V) : V = ⊤ := by
  by_contra hne
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hGcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcore : V.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal V.normalCore with hbot | htop
    · exact hbot
    · exfalso
      have hle : (⊤ : Subgroup (alternatingGroup (Fin 5))) ≤ V := by
        simpa only [htop] using V.normalCore_le
      exact hne (top_le_iff.mp hle)
  have hdvd : V.normalCore.index ∣ V.index.factorial :=
    Subgroup.index_normalCore_dvd_factorial_index V
  have hindex : V.normalCore.index = 60 := by rw [hcore, Subgroup.index_bot, hGcard]
  have hfact : 60 ≤ V.index.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (hindex ▸ hdvd)
  have hmul : V.index * Nat.card V = 60 := by
    have h := V.index_mul_card
    rwa [hGcard] at h
  have hge5 : 5 ≤ V.index := by
    by_contra hlt
    have hle4 : V.index ≤ 4 := by omega
    have hfle : V.index.factorial ≤ Nat.factorial 4 := Nat.factorial_le hle4
    norm_num at hfle
    omega
  have hcard_le : Nat.card V ≤ 12 := by
    have h : 5 * Nat.card V ≤ V.index * Nat.card V := Nat.mul_le_mul_right _ hge5
    rw [hmul] at h
    omega
  have hcard_cases : Nat.card V = 5 ∨ Nat.card V = 10 := by
    obtain ⟨m, hm⟩ := h5
    have hmpos : 1 ≤ m := by
      have hpos : 0 < Nat.card V := Nat.card_pos
      rw [hm] at hpos
      omega
    have hmle : m ≤ 2 := by
      rw [hm] at hcard_le
      omega
    interval_cases m
    · left; omega
    · right; omega
  have hVnt : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rcases hcard_cases with h | h <;> omega
  have hVperf : Group.IsPerfect V := hV
  exact Group.IsPerfect.not_isSolvable V (isSolvable_of_card_eq_five_or_ten hcard_cases)

theorem eq_top_of_perfect_of_two_le_pRank_five
    (U : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) (hU : ⁅U, U⁆ = U)
    (h5 : 2 ≤ CFSG.Open.pRank 5 U) : U = ⊤ := by
  have hFact5V : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hSimpleV : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have hA5card : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hUperf : Group.IsPerfect U := Subgroup.isPerfect_iff.mpr hU
  obtain ⟨E, hEU, hEp, h25E⟩ := exists_isPGroup_card_dvd_of_le_pRank Nat.prime_five U h5
  have hU1perf : Group.IsPerfect (U.map projFst) := Group.IsPerfect.map (H := U) projFst
  have hU2perf : Group.IsPerfect (U.map projSnd) := Group.IsPerfect.map (H := U) projSnd
  have h5U1 : 5 ∣ Nat.card (U.map projFst) := by
    by_contra hnot
    have hE1p : IsPGroup 5 (E.map projFst) := hEp.map projFst
    have hdvd : Nat.card (E.map projFst) ∣ Nat.card (U.map projFst) :=
      Subgroup.card_dvd_of_le (Subgroup.map_mono hEU)
    obtain ⟨n, hn⟩ := hE1p.exists_card_eq
    have hdiv : 5 ^ n ∣ Nat.card (U.map projFst) := hn ▸ hdvd
    have hn0 : n = 0 := by
      by_contra hnne
      exact hnot (dvd_trans (dvd_pow_self 5 hnne) hdiv)
    have hE1bot : E.map projFst = ⊥ := by
      rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]
    have hEker : E ≤ MonoidHom.ker projFst := by
      intro x hx
      refine MonoidHom.mem_ker.mpr ?_
      have hx1 : projFst x ∈ E.map projFst := ⟨x, hx, rfl⟩
      rw [hE1bot] at hx1
      exact Subgroup.mem_bot.mp hx1
    have hinj : Function.Injective (projSnd.comp E.subtype) := by
      intro x y hxy
      apply Subtype.ext
      have hx1 : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1 = 1 :=
        MonoidHom.mem_ker.mp (hEker x.2)
      have hy1 : (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1 = 1 :=
        MonoidHom.mem_ker.mp (hEker y.2)
      exact Prod.ext (by rw [hx1, hy1]) hxy
    have hEdiv : Nat.card E ∣ 60 := by
      have h := Subgroup.card_dvd_of_injective (projSnd.comp E.subtype) hinj
      rwa [hA5card] at h
    exact absurd (dvd_trans h25E hEdiv) (by norm_num)
  have h5U2 : 5 ∣ Nat.card (U.map projSnd) := by
    by_contra hnot
    have hE2p : IsPGroup 5 (E.map projSnd) := hEp.map projSnd
    have hdvd : Nat.card (E.map projSnd) ∣ Nat.card (U.map projSnd) :=
      Subgroup.card_dvd_of_le (Subgroup.map_mono hEU)
    obtain ⟨n, hn⟩ := hE2p.exists_card_eq
    have hdiv : 5 ^ n ∣ Nat.card (U.map projSnd) := hn ▸ hdvd
    have hn0 : n = 0 := by
      by_contra hnne
      exact hnot (dvd_trans (dvd_pow_self 5 hnne) hdiv)
    have hE2bot : E.map projSnd = ⊥ := by
      rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]
    have hEker : E ≤ MonoidHom.ker projSnd := by
      intro x hx
      refine MonoidHom.mem_ker.mpr ?_
      have hx1 : projSnd x ∈ E.map projSnd := ⟨x, hx, rfl⟩
      rw [hE2bot] at hx1
      exact Subgroup.mem_bot.mp hx1
    have hinj : Function.Injective (projFst.comp E.subtype) := by
      intro x y hxy
      apply Subtype.ext
      have hx1 : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).2 = 1 :=
        MonoidHom.mem_ker.mp (hEker x.2)
      have hy1 : (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).2 = 1 :=
        MonoidHom.mem_ker.mp (hEker y.2)
      exact Prod.ext hxy (by rw [hx1, hy1])
    have hEdiv : Nat.card E ∣ 60 := by
      have h := Subgroup.card_dvd_of_injective (projFst.comp E.subtype) hinj
      rwa [hA5card] at h
    exact absurd (dvd_trans h25E hEdiv) (by norm_num)
  have hU1top : U.map projFst = ⊤ := eq_top_of_isPerfect_of_dvd_card_five hU1perf h5U1
  have hU2top : U.map projSnd = ⊤ := eq_top_of_isPerfect_of_dvd_card_five hU2perf h5U2
  let N : Subgroup (alternatingGroup (Fin 5)) :=
    U.comap (MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5)))
  have hNmem : ∀ g : alternatingGroup (Fin 5), g ∈ N ↔ (g, 1) ∈ U := fun _ => Iff.rfl
  have hNnormal : N.Normal := by
    refine ⟨fun g hg a => ?_⟩
    have hgU : (g, 1) ∈ U := (hNmem g).mp hg
    have ha : a ∈ U.map projFst := by rw [hU1top]; exact Subgroup.mem_top a
    obtain ⟨u, huU, hu1⟩ := Subgroup.mem_map.mp ha
    have hu_eq : u = (a, u.2) := Prod.ext hu1 rfl
    have hub : (a, u.2) ∈ U := hu_eq ▸ huU
    have hconj : (a, u.2) * (g, 1) * (a, u.2)⁻¹ ∈ U :=
      U.mul_mem (U.mul_mem hub hgU) (U.inv_mem hub)
    have heq : (a, u.2) * (g, 1) * (a, u.2)⁻¹ = (a * g * a⁻¹, 1) := by
      ext <;> simp [mul_assoc]
    exact (hNmem (a * g * a⁻¹)).mpr (heq ▸ hconj)
  have hNnormalI : N.Normal := hNnormal
  rcases hSimpleV.eq_bot_or_eq_top_of_normal N with hNbot | hNtop
  ·
    exfalso
    have hinj : Function.Injective (projSnd.comp E.subtype) := by
      intro x y hxy
      apply Subtype.ext
      have hxU : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈ U := hEU x.2
      have hyU : (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∈ U := hEU y.2
      have hxyU : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) *
          (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5))⁻¹ ∈ U :=
        U.mul_mem hxU (U.inv_mem hyU)
      have hxy' : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).2 =
          (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).2 := hxy
      have hpair : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) *
          (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5))⁻¹ =
          ((x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1 *
            (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1⁻¹, 1) := by
        ext <;> simp [hxy']
      have hmemN : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1 *
          (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1⁻¹ ∈ N :=
        (hNmem _).mpr (hpair ▸ hxyU)
      rw [hNbot] at hmemN
      have hfst : (x : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1 =
          (y : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)).1 :=
        mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmemN)
      exact Prod.ext hfst hxy
    have hEdiv : Nat.card E ∣ 60 := by
      have h := Subgroup.card_dvd_of_injective (projSnd.comp E.subtype) hinj
      rwa [hA5card] at h
    exact absurd (dvd_trans h25E hEdiv) (by norm_num)
  ·
    rw [Subgroup.eq_top_iff']
    intro x
    have hb : x.2 ∈ U.map projSnd := by rw [hU2top]; exact Subgroup.mem_top x.2
    obtain ⟨u, huU, hu2⟩ := Subgroup.mem_map.mp hb
    have hmemN : x.1 * u.1⁻¹ ∈ N := by rw [hNtop]; exact Subgroup.mem_top _
    have hua : (x.1 * u.1⁻¹, 1) ∈ U := (hNmem _).mp hmemN
    have hu2' : u.2 = x.2 := hu2
    have heq : (x.1 * u.1⁻¹, 1) * u = x := by
      ext <;> simp [hu2', mul_assoc]
    rw [← heq]
    exact U.mul_mem hua huU

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
