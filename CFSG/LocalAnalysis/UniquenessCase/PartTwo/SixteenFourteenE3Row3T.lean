module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenE3Tools
public import CFSG.RankThree.PartOne.K133H.SylowTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

private lemma s1614e3_hsum {W : Type} [CommGroup W] {z : MulAut W}
    (hz3 : z * z * z = 1) (hzfix : ∀ x : W, z x = x → x = 1) (x : W) :
    x * z x * z (z x) = 1 := by
  apply hzfix
  have hzzz : z (z (z x)) = x := by
    have h := congrArg (fun f : MulAut W => f x) hz3
    simpa using h
  rw [map_mul, map_mul, hzzz]
  ac_rfl

private lemma s1614e3_elemAbelianRank_comm_pow {q n : ℕ} {P : Type*} [Group P]
    (h : IsElemAbelianOfRank q n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ q = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

private lemma s1614e3_card_elemAbelianOfRank {X : Type*} [Group X]
    (h : IsElemAbelianOfRank 3 2 X) : Nat.card X = 3 ^ 2 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.ofAdd.symm,
    Nat.card_fun, Nat.card_fin, Nat.card_zmod]

private lemma s1614e3_mem_of_card_sq_of_central {G : Type*} [Group G] [Finite G]
    {p : ℕ} [hp : Fact p.Prime] (hG : Nat.card G = p ^ 3) {z : G}
    (hz : z ∈ Subgroup.center G) (hnc : ¬ ∀ a b : G, a * b = b * a)
    {R : Subgroup G} (hR : Nat.card R = p ^ 2) : z ∈ R := by
  by_contra hzR
  have hRc : ∀ a b : R, a * b = b * a := IsPGroup.commutative_of_card_eq_prime_sq hR
  set H : Subgroup G := Subgroup.closure ((R : Set G) ∪ {z}) with hH
  have hRH : R ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hzH : z ∈ H := Subgroup.subset_closure (Or.inr rfl)
  have hHc : IsMulCommutative ↥H := by
    refine Subgroup.isMulCommutative_closure ?_
    intro u hu v hv _
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact congrArg Subtype.val (hRc ⟨u, hu⟩ ⟨v, hv⟩)
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Subgroup.mem_center_iff.1 hz u
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (Subgroup.mem_center_iff.1 hz v).symm
    · rw [Set.mem_singleton_iff] at hu hv
      subst hu
      subst hv
      exact absurd rfl ‹_›
  have hdvd1 : p ^ 2 ∣ Nat.card H := hR ▸ Subgroup.card_dvd_of_le hRH
  have hdvd2 : Nat.card H ∣ p ^ 3 := hG ▸ Subgroup.card_subgroup_dvd_card H
  have hne : Nat.card H ≠ p ^ 2 := by
    intro h
    have : R = H := Subgroup.eq_of_le_of_card_ge hRH (by rw [h, hR])
    exact hzR (this ▸ hzH)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp.out).1 hdvd2
  have hp2 : 2 ≤ k := by
    have h1 : p ^ 2 ∣ p ^ k := hk' ▸ hdvd1
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h1
  have hk3 : k = 3 := by
    interval_cases k
    · exact absurd hk' hne
    · rfl
  have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H (by rw [hk', hk3, hG])
  apply hnc
  intro a b
  have ha : a ∈ H := hHtop ▸ Subgroup.mem_top a
  have hb : b ∈ H := hHtop ▸ Subgroup.mem_top b
  exact congrArg Subtype.val (hHc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem s1614e3_row3_lin {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {z t : MulAut W} (hz3 : z * z * z = 1)
    (hzfix : ∀ x : W, z x = x → x = 1) (ht2 : t * t = 1) (hzt : t * z = z * t)
    (hk : 1 < rkIdx (fixV (Subgroup.zpowers t))) {Wd : Subgroup W}
    (hWd : Wd ≤ fixV (Subgroup.zpowers t)) (hrk : rkIdx Wd ≤ 3) :
    ∃ Z : Subgroup W, Z ≠ ⊥ ∧ Z ≤ Wd ∧ Z.map z.toMonoidHom = Z := by

  classical
  have hT : ∀ x : W, x ^ 2 = 1 := fun x => by rw [pow_two]; exact hW x
  have hrkW : rk W = 6 := by
    unfold rk
    rw [hcard, padicValNat.prime_pow]
  let C : Subgroup W := fixV (Subgroup.zpowers t)
  have hC4 : rk C ≤ 4 := by
    have hkC : 1 < rkIdx C := hk
    have h := rk_add_rkIdx (G := W) C
    omega
  have hWd3 : 3 ≤ rk Wd := by
    have h := rk_add_rkIdx (G := W) Wd
    omega
  have hCinv : Wd.comap z.toMonoidHom ≤ C := by
    intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [mem_fixV_zpowers_iff_apply]
    have hx' : t (z x) = z x := mem_fixV_zpowers_iff_apply.mp (hWd hx)
    have hzx : z (t x) = z x := by
      calc z (t x) = (z * t) x := rfl
        _ = (t * z) x := by rw [hzt]
        _ = t (z x) := rfl
        _ = z x := hx'
    exact z.injective hzx
  have hcomap_rk : rk (Wd.comap z.toMonoidHom) = rk Wd := by
    unfold rk
    rw [Subgroup.comap_equiv_eq_map_symm' z Wd,
      Subgroup.card_map_of_injective z.symm.injective]
  have hsup_le : rk ↥(Wd ⊔ Wd.comap z.toMonoidHom) ≤ 4 :=
    le_trans (rk_mono (sup_le hWd hCinv)) hC4
  have hZ2 : 2 ≤ rk ↥(Wd ⊓ Wd.comap z.toMonoidHom) := by
    have h := rk_sup_add_rk_inf (V := W) Wd (Wd.comap z.toMonoidHom)
    omega
  have hZne : Wd ⊓ Wd.comap z.toMonoidHom ≠ ⊥ := by
    intro hbot
    have : rk ↥(Wd ⊓ Wd.comap z.toMonoidHom) = 0 := by rw [hbot, rk_bot]
    omega
  have hZmap_le : (Wd ⊓ Wd.comap z.toMonoidHom).map z.toMonoidHom ≤
      Wd ⊓ Wd.comap z.toMonoidHom := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap]
    refine ⟨hx.2, Subgroup.mem_comap.mpr ?_⟩
    have hsum := s1614e3_hsum hz3 hzfix x
    have hz2 : z (z x) = (x * z x)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)
    change z (z x) ∈ Wd
    rw [hz2]
    exact Wd.inv_mem (Wd.mul_mem hx.1 hx.2)
  have hZmap : (Wd ⊓ Wd.comap z.toMonoidHom).map z.toMonoidHom =
      Wd ⊓ Wd.comap z.toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hZmap_le ?_
    rw [Subgroup.card_map_of_injective z.injective]
  exact ⟨Wd ⊓ Wd.comap z.toMonoidHom, hZne, inf_le_left, hZmap⟩

theorem s1614e3_row3_inv {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {z t : MulAut W} (hz3 : z * z * z = 1)
    (hzfix : ∀ x : W, z x = x → x = 1) (ht2 : t * t = 1) (htz : t * z = z * z * t) :
    rkIdx (fixV (Subgroup.zpowers t)) = 3 ∧
      ∀ m : MulAut W, (m * z = z * m ∨ m * z = z * z * m) →
        (∀ x ∈ fixV (Subgroup.zpowers t), m x = x) → m = 1 ∨ m = t := by

  classical
  have hT : ∀ x : W, x ^ 2 = 1 := fun x => by rw [pow_two]; exact hW x
  have hrkW : rk W = 6 := by
    unfold rk
    rw [hcard, padicValNat.prime_pow]
  let C : Subgroup W := fixV (Subgroup.zpowers t)
  have hinf : C ⊓ C.map z.toMonoidHom = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxC, hxC'⟩ := hx
    obtain ⟨y, hyC, hyx⟩ := Subgroup.mem_map.mp hxC'
    have htx : t x = z x := by
      rw [← hyx]
      calc t (z y) = (t * z) y := rfl
        _ = (z * z * t) y := by rw [htz]
        _ = z (z (t y)) := rfl
        _ = z (z y) := by rw [mem_fixV_zpowers_iff_apply.mp hyC]
    have hzx : z x = x := htx ▸ mem_fixV_zpowers_iff_apply.mp hxC
    exact hzfix x hzx
  have hCmap_rk : rk (C.map z.toMonoidHom) = rk C := by
    unfold rk
    rw [Subgroup.card_map_of_injective z.injective]
  have hsup_eq : rk ↥(C ⊔ C.map z.toMonoidHom) = 2 * rk C := by
    have h := rk_sup_add_rk_inf (V := W) C (C.map z.toMonoidHom)
    rw [hinf] at h
    rw [rk_bot (G := W)] at h
    rw [hCmap_rk] at h
    omega
  have hsup_le6 : rk ↥(C ⊔ C.map z.toMonoidHom) ≤ 6 := by
    have h := rk_mono (le_top : C ⊔ C.map z.toMonoidHom ≤ (⊤ : Subgroup W))
    rwa [rk_top, hrkW] at h
  have hC3 : rk C ≤ 3 := by omega
  have hIdx3 : rkIdx C = 3 := by
    have hge : 3 ≤ rkIdx C := by
      have h := rk_add_rkIdx (G := W) C
      omega
    have hle : rkIdx C ≤ 3 := by
      have h := s1614e3_two_mul_rkIdx_le (T := W) hT ht2
      change 2 * rkIdx C ≤ rk W at h
      omega
    omega
  have hC : rk C = 3 := by
    have h := rk_add_rkIdx (G := W) C
    omega
  have htop : C ⊔ C.map z.toMonoidHom = ⊤ := by
    refine eq_of_le_of_rk_le hT le_top ?_
    rw [rk_top, hrkW, hsup_eq, hC]
  have key_agree : ∀ m₁ m₂ : MulAut W, (∀ x ∈ C, m₁ x = m₂ x) →
      (∀ x ∈ C.map z.toMonoidHom, m₁ x = m₂ x) → m₁ = m₂ := by
    intro m₁ m₂ h1 h2
    ext x
    have hx : x ∈ (⊤ : Subgroup W) := Subgroup.mem_top x
    rw [← htop] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
    rw [map_mul, map_mul, h1 a ha, h2 b hb]
  refine ⟨hIdx3, ?_⟩
  intro m hm hfix
  rcases hm with hlin | hinv
  · left
    refine key_agree m 1 (fun x hx => by simpa using hfix x hx) ?_
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    have : m (z c) = z c := by
      calc m (z c) = (m * z) c := rfl
        _ = (z * m) c := by rw [hlin]
        _ = z (m c) := rfl
        _ = z c := by rw [hfix c hc]
    simpa using this
  · right
    refine key_agree m t (fun x hx => ?_) ?_
    · rw [hfix x hx]
      exact (mem_fixV_zpowers_iff_apply.mp hx).symm
    · intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      have hmzc : m (z c) = z (z c) := by
        calc m (z c) = (m * z) c := rfl
          _ = (z * z * m) c := by rw [hinv]
          _ = z (z (m c)) := rfl
          _ = z (z c) := by rw [hfix c hc]
      have htzc : t (z c) = z (z c) := by
        calc t (z c) = (t * z) c := rfl
          _ = (z * z * t) c := by rw [htz]
          _ = z (z (t c)) := rfl
          _ = z (z c) := by rw [mem_fixV_zpowers_iff_apply.mp hc]
      exact hmzc.trans htzc.symm

theorem s1614e3_row3_sylow {W : Type} [CommGroup W] [Finite W] {L X : Subgroup (MulAut W)}
    (hL : IsPOnePlusTwo 3 ↥L) (hLX : L ≤ X)
    (hXN : X ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (h27 : (Nat.card X).factorization 3 = 3) :
    CFSG.Open.pRank 3 X ≤ 2 ∧
      ∀ E : Subgroup (MulAut W), E ≤ X → IsElemAbelianOfRank 3 2 ↥E →
        ∀ ℓ : ↥L, ℓ ∈ Subgroup.center ↥L → (ℓ : MulAut W) ∈ E := by

  classical
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CFSG.IsExtraspecial 3 ↥L := hL.1
  have hLcard : Nat.card ↥L = 3 ^ 3 := hL.2.1
  have hLfac : (Nat.card ↥L).factorization 3 = 3 := by
    rw [hLcard, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  have hnc : ¬ ∀ a b : ↥L, a * b = b * a := by
    intro hcomm
    have hcenter : Subgroup.center ↥L = ⊤ :=
      Subgroup.center_eq_top_iff.mpr (IsMulCommutative.of_comm hcomm)
    have h3 := CFSG.IsExtraspecial.center_order_p 3 ↥L
    rw [hcenter, Subgroup.card_top] at h3
    omega
  have hEL : ∀ E : Subgroup (MulAut W), E ≤ X → (∀ x ∈ E, x ^ 3 = 1) → E ≤ L := by
    intro E hEX hEpow
    have hord : (Nat.card X).factorization 3 = (Nat.card ↥L).factorization 3 := by
      rw [h27, hLfac]
    obtain ⟨g, hgX, hgE⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow
      (p := 3) hLX hEX hEpow hord
    intro e he
    have hge : g * e * g⁻¹ ∈ L :=
      hgE (Subgroup.mem_map.mpr ⟨e, he, MulAut.conj_apply g e⟩)
    have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut W)) := hXN hgX
    have hginvN : g⁻¹ ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
      (Subgroup.normalizer (L : Set (MulAut W))).inv_mem hgN
    have hback := (Subgroup.mem_normalizer_iff.mp hginvN (g * e * g⁻¹)).mp hge
    have heq : g⁻¹ * (g * e * g⁻¹) * (g⁻¹)⁻¹ = e := by group
    rwa [heq] at hback
  have hpRank : CFSG.Open.pRank 3 X ≤ 2 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) ?_
    intro E hEX hEel
    have hEpow : ∀ x ∈ E, x ^ 3 = 1 := hEel.2
    have hEL' : E ≤ L := hEL E hEX hEpow
    have hdvd : Nat.card ↥E ∣ 3 ^ 3 := by
      rw [← hLcard]
      exact Subgroup.card_dvd_of_le hEL'
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have hk_ne : k ≠ 3 := by
      intro hk3eq
      have hcardE : Nat.card ↥E = 3 ^ 3 := by rw [hk, hk3eq]
      have hEeqL : E = L := Subgroup.eq_of_le_of_card_ge hEL' (by rw [hcardE, hLcard])
      apply hnc
      intro a b
      have ha : a.1 ∈ E := by rw [hEeqL]; exact a.2
      have hb : b.1 ∈ E := by rw [hEeqL]; exact b.2
      apply Subtype.ext
      have hcomm := hEel.1.is_comm.comm ⟨a.1, ha⟩ ⟨b.1, hb⟩
      simpa using congrArg Subtype.val hcomm
    have hk2 : k ≤ 2 := by omega
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk2
  refine ⟨hpRank, ?_⟩
  intro E hEX hErank ℓ hℓ
  have hEcard : Nat.card ↥E = 3 ^ 2 := s1614e3_card_elemAbelianOfRank hErank
  have hEpow : ∀ x ∈ E, x ^ 3 = 1 := fun x hx => by
    have := (s1614e3_elemAbelianRank_comm_pow hErank).2 ⟨x, hx⟩
    simpa using this
  have hEL' : E ≤ L := hEL E hEX hEpow
  have hRcard : Nat.card ↥(E.subgroupOf L) = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL').toEquiv, hEcard]
  have hzmem : ℓ ∈ E.subgroupOf L :=
    s1614e3_mem_of_card_sq_of_central (p := 3) hLcard hℓ hnc hRcard
  exact Subgroup.mem_subgroupOf.mp hzmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
