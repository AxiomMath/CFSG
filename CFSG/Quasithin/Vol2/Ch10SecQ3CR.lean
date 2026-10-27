module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CQ
public import CFSG.Quasithin.Vol2.Ch10SecB3CHall
public import CFSG.Quasithin.Vol2.Ch10SecQ34B0
public import CFSG.Quasithin.Vol2.Ch11SecB35
public import CFSG.Quasithin.Vol2.Ch10SecQ4FS9

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_fsuM_le_normalizer_T0
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) (hK : BenderHyp (↥L ⧸ CFSG.pCore 2 ↥L))
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    H ⊓ fsuM T L ≤ Subgroup.normalizer (T0 T L : Set G) := by
  have hN := inf_le_normalizer_T0 hF6 h37 h38 h331 hyp hK hH
  set K₀ := (H ⊓ fsuM T L) ⊓ fsuL0 T L with hK₀
  have hT0L := SecF.C10P4F.isSylowTwoOf_T0 hyp
  have hT0K : T0 T L ≤ K₀ :=
    le_inf (le_inf (inf_le_left.trans hH.1.1) (inf_le_left.trans (SecA.le_fsuM T L)))
      inf_le_right
  have hsyl : IsSylowTwoOf (T0 T L) K₀ := by
    refine ⟨hT0K, hT0L.2.1, fun h2 => hT0L.2.2 ?_⟩
    change 2 ∣ (T0 T L).relIndex (fsuL0 T L)
    rw [← Subgroup.relIndex_mul_relIndex _ K₀ _ hT0K inf_le_right]
    exact Dvd.dvd.mul_right h2 _
  intro x hx
  have hxK : x ∈ Subgroup.normalizer (K₀ : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hx.2⟩
  set T₀' := (T0 T L).map (MulAut.conj x).toMonoidHom with hT₀'
  have hcard : Nat.card T₀' = Nat.card (T0 T L) :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hle' : T₀' ≤ K₀ := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxK s).mp (hT0K hs)
  have hsyl' : IsSylowTwoOf T₀' K₀ :=
    isSylowTwoOf_of_card_eq hle' (hT0L.2.1.map _) (hcard.trans hsyl.card_eq)
  have hsub : T0 T L ≤ T₀' := hsyl'.le_of_normalizes hT0K hN hT0L.2.1
  have heq : T₀' = T0 T L := (Subgroup.eq_of_le_of_card_ge hsub hcard.le).symm
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    rw [← heq]
    exact ⟨s, hs, rfl⟩
  · intro hs
    rw [← heq] at hs
    obtain ⟨s', hs', hss'⟩ := hs
    have h1 : s' = s := by simpa [MulAut.conj_apply] using hss'
    exact h1 ▸ hs'

theorem inf_fsuM_le_normalizer_B0
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) (hK : BenderHyp (↥L ⧸ CFSG.pCore 2 ↥L))
    {H : Subgroup G} (hH : IsHStar T (fsuM T L) H) :
    H ⊓ fsuM T L ≤ Subgroup.normalizer (B0 T L : Set G) := fun _ hx =>
  normalizer_le_normalizer_oTwoUpper _ (Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hx.2, Subgroup.le_normalizer (inf_fsuM_le_normalizer_T0 hF6 h37 h38 h331 hyp hK hH hx)⟩)

omit [Finite G] in
theorem conjClosure_eq_of_sup {H K T : Subgroup G} (hHK : H = K ⊔ T) :
    conjClosure K H = conjClosure K T := by
  refine le_antisymm (conjClosure_le fun h hh k hk => ?_)
    (conjClosure_mono le_rfl (hHK ▸ le_sup_right))
  have hN : H ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
    rw [hHK]
    exact sup_le (fun k hk => Subgroup.le_normalizer (le_conjClosure K T hk))
      (le_normalizer_conjClosure K T)
  exact (Subgroup.mem_normalizer_iff.mp (hN hh) k).mp (le_conjClosure K T hk)

theorem oTwoUpper_eq_conjClosure_T {H K T : Subgroup G} (hKc : K ∈ cComp H)
    (hT : IsPGroup 2 T) (hHK : H = K ⊔ T) : oTwoUpper H = conjClosure K T := by
  rw [Ch11.SecB.oTwoUpper_eq_conjClosure (perfect_of_mem_cComp hKc) hT hHK,
    conjClosure_eq_of_sup hHK]

omit [Finite G] in
theorem le_normalizer_conjClosure_of {A K T : Subgroup G}
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ Subgroup.normalizer (conjClosure K T : Set G) := by
  have key : ∀ a ∈ A, ∀ y ∈ conjClosure K T, a * y * a⁻¹ ∈ conjClosure K T := by
    intro a ha
    have hle : conjClosure K T ≤ (conjClosure K T).comap (MulAut.conj a).toMonoidHom := by
      refine conjClosure_le fun t ht k hk => ?_
      show a * (t * k * t⁻¹) * a⁻¹ ∈ conjClosure K T
      have ha' : t⁻¹ * a * t ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (hTA (T.inv_mem ht)) a).mp ha
        simpa using this
      have h2 : (t⁻¹ * a * t) * k * (t⁻¹ * a * t)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hAK ha') k).mp hk
      have h3 := mem_conjClosure ht h2
      have e : t * ((t⁻¹ * a * t) * k * (t⁻¹ * a * t)⁻¹) * t⁻¹ = a * (t * k * t⁻¹) * a⁻¹ := by
        group
      rwa [e] at h3
    intro y hy
    exact hle hy
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have := key a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

theorem B0_le_normalizer_oTwoUpper (hB0K : Obl10_2_3B0K) (hyp : Hyp10 G T L I) {n : ℕ}
    (h1 : Case10_1_1One T L I n) {H : Subgroup G} (hH : IsHStar T (fsuM T L) H)
    (hn1 : 1 < E1.nParam H) (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) {K : Subgroup G}
    {m : ℕ} (hKc : K ∈ cComp H) (hHK : H = K ⊔ T)
    (hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    B0 T L ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  have hO := oTwoUpper_eq_conjClosure_T hKc hyp.fsu.sylow.1 hHK
  rw [hO]
  exact le_normalizer_conjClosure_of (hB0K G T L I hyp n h1 H hH hn1 hZH K m hKc hO hKF)
    (SecA.le_normalizer_B0 T L)

theorem exists_hall_pair
    (hF6 : FactBenderOver) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h331 : Stmt3_3_1) (hDHB : Ch11.SecB.DerivedHallBorel) (hB0K : Obl10_2_3B0K)
    (hyp : Hyp10 G T L I) {n : ℕ} (h1 : Case10_1_1One T L I n) {H : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hn1 : 1 < E1.nParam H)
    (hZH : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥) {K : Subgroup G} {m : ℕ} (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T)
    (hKF : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ m ∧
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)) :
    ∃ B D : Subgroup G, Lin2.IsHallTwoPrimeOf B (H ⊓ fsuM T L) ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ Lin2.IsHallTwoPrimeOf D (B0 T L) ∧
      B ≤ Subgroup.normalizer (D : Set G) ∧ D ≤ Subgroup.normalizer (B : Set G) := by
  have hK := (bender_of_cases (Or.inl ⟨n, h1⟩)).1
  have hInM : InM T (fsuM T L) := ⟨fsuM_isMaxTwoLocal h331 hyp, SecA.le_fsuM T L⟩
  obtain ⟨B, hB, hBc, -⟩ := hDHB G T (fsuM T L) H hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.sylow hInM (normalizer_T_le h331 hyp) hH hn1
  have hXT0 := inf_fsuM_le_normalizer_T0 hF6 h37 h38 h331 hyp hK hH
  have hXB0 := inf_fsuM_le_normalizer_B0 hF6 h37 h38 h331 hyp hK hH
  obtain ⟨hPB, hP2, hPi⟩ := SecA.isSylowTwoOf_T0_inf_B0 hyp
  have hB0P : B0 T L ≤ Subgroup.normalizer ((T0 T L ⊓ B0 T L : Subgroup G) : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(oTwoUpper_le _ hb).2, Subgroup.le_normalizer hb⟩
  have hXP : H ⊓ fsuM T L ≤ Subgroup.normalizer ((T0 T L ⊓ B0 T L : Subgroup G) : Set G) :=
    fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hXT0 hx, hXB0 hx⟩
  obtain ⟨D, hD, c, hc, hcD⟩ := exists_hall_le_normalizer hPB hP2 hPi hB0P
    (hB.1.trans hXP) (hB.1.trans hXB0) hB.2.1
  have hcX : c⁻¹ ∈ H ⊓ fsuM T L :=
    (H ⊓ fsuM T L).inv_mem ⟨hH.1.1 hc.1.1, SecA.le_fsuM T L hc.1.1⟩
  have hB'h : Lin2.IsHallTwoPrimeOf (B.map (MulAut.conj c⁻¹).toMonoidHom) (H ⊓ fsuM T L) :=
    isHallTwoPrimeOf_conjSub hcX hB
  refine ⟨_, D, hB'h, ?_, hD, hcD, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c⁻¹ * a * c⁻¹⁻¹ * (c⁻¹ * b * c⁻¹⁻¹) = c⁻¹ * (a * b) * c⁻¹⁻¹ by group,
      hBc a ha b hb]
    group
  · have hR : B.map (MulAut.conj c⁻¹).toMonoidHom ≤ oTwoUpper H ⊓ fsuM T L := fun b hb =>
      ⟨mem_oTwoUpper_of_odd (hB'h.1 hb).1
        (hB'h.2.1.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hb)), (hB'h.1 hb).2⟩
    obtain ⟨k, hk⟩ := hB'h.2.2
    have h2 := Subgroup.relIndex_mul_relIndex _ _ _ hR
      (inf_le_inf_right (fsuM T L) (oTwoUpper_le H))
    rw [hk] at h2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro _ h2)
    have hDR : D ≤ Subgroup.normalizer ((oTwoUpper H ⊓ fsuM T L : Subgroup G) : Set G) := by
      intro d hd
      have hdB0 := hD.1 hd
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨B0_le_normalizer_oTwoUpper hB0K hyp h1 hH hn1 hZH hKc hHK hKF hdB0,
          Subgroup.le_normalizer (SecA.fsuL0_le_fsuM T L (oTwoUpper_le _ hdB0).1)⟩
    exact le_normalizer_of_hall hR hi hB'h.2.1 hD.2.1 hcD hDR

theorem commute_of_mem_hall_pair {B D B₀ : Subgroup G} (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBN : B ≤ Subgroup.normalizer (B₀ : Set G)) (hDB₀ : D ≤ B₀)
    (hDB : D ≤ Subgroup.normalizer (B : Set G)) {y : G} (hy : y ∈ B) {r : ℕ} (hr : r.Prime)
    (hyr : y ^ r = 1) (hrB : ¬ r ∣ Nat.card B₀) {d : G} (hd : d ∈ D) : y * d = d * y := by
  refine commute_of_conj_comm (hBN hy) (hDB₀ hd) hr hyr hrB ?_
  have hc : y * d * y⁻¹ * d⁻¹ ∈ B := by
    have h1 : d * y⁻¹ * d⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hDB hd) _).mp (B.inv_mem hy)
    have := B.mul_mem hy h1
    simpa [mul_assoc] using this
  exact hBc y hy _ hc

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
