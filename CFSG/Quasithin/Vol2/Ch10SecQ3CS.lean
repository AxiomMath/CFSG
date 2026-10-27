module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CP
public import CFSG.Quasithin.Vol2.Ch10SecQ3CG
public import CFSG.Quasithin.Vol2.Ch10SecATorusA
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5B0
public import CFSG.Quasithin.Vol2.Ch10SecAT1Torus
public import CFSG.Quasithin.Vol2.Ch10SecQ3CQ

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem le_normalizer_fsuUL (T L I : Subgroup G) :
    L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
  SecA.le_normalizer_commutator
    ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)) Subgroup.le_normalizer

theorem exists_preimage_normalizer_T0
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    [IsMulCommutative ↥(fsuUL T L I)] {F : Type} [Field F] (c : SecA.NatCoord T L I F)
    {δ : Matrix.SpecialLinearGroup (Fin 2) F}
    (hδ : ∀ X, (∃ b, X = SecA.unipSL b) ↔ ∃ b, δ * X * δ⁻¹ = SecA.unipSL b) :
    ∃ l ∈ L, ∃ hlN : l ∈ Subgroup.normalizer (fsuUL T L I : Set G),
      l ∈ Subgroup.normalizer (T0 T L : Set G) ∧
      conjAct (fsuUL T L I) ⟨l, hlN⟩ =
        ((c.eρ (c.g⁻¹ * δ * c.g) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  have hloc := hyp.fsu.maximal.1
  have hLU := le_normalizer_fsuUL T L I
  set γ := c.g⁻¹ * δ * c.g with hγ
  have hφN := c.mem_normalizer hδ
  obtain ⟨g', hg'L, hg'⟩ := SecA.mem_autOn_iff'.mp (c.eρ γ).2
  have hchar : ∀ s (hs : s ∈ L), s ∈ T ⊓ L ↔
      conjAct (fsuUL T L I) ⟨s, hLU hs⟩ ∈ autOn (T ⊓ L) (fsuUL T L I) := by
    intro s hs
    refine ⟨fun h => SecA.mem_autOn_iff'.mpr ⟨_, h, rfl⟩, fun h => ?_⟩
    obtain ⟨s', hs'K, hs'⟩ := SecA.mem_autOn_iff'.mp h
    have h2 : conjAct (fsuUL T L I) (⟨s, hLU hs⟩ * s'⁻¹) = 1 := by
      rw [map_mul, map_inv, hs', mul_inv_cancel]
    have hy : ∀ u ∈ fsuUL T L I, s * (s' : G)⁻¹ * u * (s * (s' : G)⁻¹)⁻¹ = u := by
      intro u hu
      have e := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨u, hu⟩ : ↥(fsuUL T L I)) : G)) h2
      simp only [SecA.coe_conjAct_apply', MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at e
      exact e
    have hyT := SecA.mem_T_of_forall_conj_eq h37 h38 hyp ht htn
      (L.mul_mem hs (L.inv_mem hs'K.2)) hy
    refine ⟨?_, hs⟩
    have e : s = s * (s' : G)⁻¹ * s' := by group
    rw [e]
    exact T.mul_mem hyT hs'K.1
  have hlN : (g' : G) ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    by_cases hs : s ∈ L
    · have hls : (g' : G) * s * (g' : G)⁻¹ ∈ L := L.mul_mem (L.mul_mem hg'L hs) (L.inv_mem hg'L)
      rw [hchar s hs, hchar _ hls]
      have he : conjAct (fsuUL T L I) ⟨(g' : G) * s * (g' : G)⁻¹, hLU hls⟩ =
          ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) *
            conjAct (fsuUL T L I) ⟨s, hLU hs⟩ *
              ((c.eρ γ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))⁻¹ := by
        rw [← hg', ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [he]
      exact Subgroup.mem_normalizer_iff.mp hφN _
    · constructor
      · intro h
        exact absurd h.2 hs
      · intro h
        apply absurd _ hs
        have := L.mul_mem (L.mul_mem (L.inv_mem hg'L) h.2) hg'L
        simpa [mul_assoc] using this
  have hlLt := SecA.mem_normalizer_inf_conjugate h37 hyp ht htn hg'L
  have hlO : (g' : G) ∈ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (SecA.le_fsuL0 T L hg'L)
  have hT0eq : T0 T L = T ⊓ L ⊔ T ⊓ CFSG.conjugate L t ⊔ pCoreOf 2 (fsuL0 T L) :=
    le_antisymm (SecA.T0_le_sup h37 h38 hyp ht htn) (sup_le (sup_le
      (inf_le_inf_left T (SecA.le_fsuL0 T L)) (inf_le_inf_left T (SecA.conjugate_le_fsuL0 ht)))
      (SecA.pCoreOf_fsuL0_le_T0 hyp.fsu.sylow))
  have hlT0 : (g' : G) ∈ Subgroup.normalizer (T0 T L : Set G) := by
    rw [hT0eq]
    exact SecA.le_normalizer_sup (SecA.le_normalizer_sup ((Subgroup.zpowers_le).mpr hlN)
      ((Subgroup.zpowers_le).mpr hlLt)) ((Subgroup.zpowers_le).mpr hlO)
      (Subgroup.mem_zpowers _)
  exact ⟨g', hg'L, g'.2, hlT0, hg'⟩

theorem forall_mem_zpowers_pow {F : Type} [Field F] [Finite F] {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hn : 1 ≤ n) {μ : Fˣ} (hμ : ∀ x : Fˣ, x ∈ Subgroup.zpowers μ) (k : ℕ) :
    ∀ x : Fˣ, x ∈ Subgroup.zpowers (μ ^ 2 ^ k) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcu : Nat.card Fˣ = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  have hodd : Odd (orderOf μ) := by
    refine Odd.of_dvd_nat ?_ (hcu ▸ orderOf_dvd_natCard μ)
    exact Nat.Even.sub_odd (Nat.one_le_two_pow) (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one
  have hord : orderOf (μ ^ 2 ^ k) = orderOf μ :=
    Nat.Coprime.orderOf_pow ((Nat.coprime_two_right.mpr hodd).pow_right k)
  have hle : Subgroup.zpowers (μ ^ 2 ^ k) ≤ Subgroup.zpowers μ :=
    Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers μ) _)
  have heq : Subgroup.zpowers (μ ^ 2 ^ k) = Subgroup.zpowers μ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  intro x
  rw [heq]
  exact hμ x

theorem exists_torus_gen
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    [IsMulCommutative ↥(fsuUL T L I)] {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (c : SecA.NatCoord T L I F) :
    ∃ l ∈ L, ∃ hlN : l ∈ Subgroup.normalizer (fsuUL T L I : Set G),
      l ∈ Subgroup.normalizer (T0 T L : Set G) ∧ Odd (orderOf l) ∧ ∃ μ : Fˣ,
        (∀ x : Fˣ, x ∈ Subgroup.zpowers μ) ∧
        conjAct (fsuUL T L I) ⟨l, hlN⟩ =
          ((c.eρ (c.g⁻¹ * dU μ * c.g) : ↥(autOn L (fsuUL T L I))) :
            MulAut ↥(fsuUL T L I)) := by
  obtain ⟨μ₀, hμ₀⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hd : dU μ₀ = SecA.diagSL μ₀.ne_zero := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_dU, SecA.coe_diagSL]
  obtain ⟨g', hg'L, hg'N, hg'T, hg'⟩ := exists_preimage_normalizer_T0 h37 h38 hyp c
    (δ := dU μ₀) (hd ▸ SecA.diagSL_conj_iff μ₀.ne_zero)
  obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g').ne'
  refine ⟨g' ^ 2 ^ k, L.pow_mem hg'L _, Subgroup.pow_mem _ hg'N _, Subgroup.pow_mem _ hg'T _,
    ?_, μ₀ ^ 2 ^ k, forall_mem_zpowers_pow hF hn hμ₀ k, ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hord⟩, hord,
      Nat.mul_div_cancel_left _ (pow_pos two_pos k)]
    exact hm
  · have hpow : (c.g⁻¹ * dU μ₀ * c.g) ^ 2 ^ k = c.g⁻¹ * dU (μ₀ ^ 2 ^ k) * c.g := by
      have h := map_pow (MulAut.conj c.g⁻¹) (dU μ₀) (2 ^ k)
      simp only [MulAut.conj_apply, inv_inv] at h
      rw [← dU_pow]
      exact h.symm
    have h1 : conjAct (fsuUL T L I) ⟨g' ^ 2 ^ k, Subgroup.pow_mem _ hg'N _⟩ =
        (conjAct (fsuUL T L I) ⟨g', hg'N⟩) ^ 2 ^ k := by
      rw [← map_pow]
      rfl
    rw [h1, hg', ← hpow, map_pow, SubgroupClass.coe_pow]

theorem exists_conj_le_of_odd {B₀ P D Y : Subgroup G} (hPB₀ : P ≤ B₀)
    (hP : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.relIndex B₀)
    (hPn : B₀ ≤ Subgroup.normalizer (P : Set G)) (hD : Lin2.IsHallTwoPrimeOf D B₀)
    (hYB : Y ≤ B₀) (hY : Odd (Nat.card Y)) :
    ∃ m ∈ P, Y.map (MulAut.conj m⁻¹).toMonoidHom ≤ D := by
  set Q := P ⊔ Y with hQ
  have hQB : Q ≤ B₀ := sup_le hPB₀ hYB
  have hDQodd : Odd (Nat.card ↥(D ⊓ Q)) :=
    hD.2.1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := hD.1.trans hPn
  have hsup : P ⊔ Y = P ⊔ (D ⊓ Q) := by
    refine le_antisymm (fun y hy => ?_) (sup_le le_sup_left inf_le_right)
    have hyPD : y ∈ ((P ⊔ D : Subgroup G) : Set G) :=
      le_sup_of_hall ⟨hPB₀, hP, hPi⟩ hD (hQB hy)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P D hDP] at hyPD
    obtain ⟨p, hp, e, he, rfl⟩ := Set.mem_mul.mp hyPD
    have heQ : e ∈ Q := by
      have h1 := Q.mul_mem (Q.inv_mem ((le_sup_left : P ≤ Q) hp)) hy
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ⟨he, heQ⟩)
  obtain ⟨m, hm, hmD⟩ := exists_conj_of_complement hP hY (hYB.trans hPn)
    (inf_le_left.trans hDP) (inf_eq_bot_of_odd hP hY) (inf_eq_bot_of_odd hP hDQodd) hsup
  exact ⟨m, hm, hmD ▸ inf_le_left⟩

theorem exists_mem_hall_torus
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I)
    [IsMulCommutative ↥(fsuUL T L I)] {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (c : SecA.NatCoord T L I F)
    {D : Subgroup G} (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) :
    ∃ d ∈ D, ∃ hdN : d ∈ Subgroup.normalizer (fsuUL T L I : Set G), ∃ (μ : Fˣ)
      (x : Matrix.SpecialLinearGroup (Fin 2) F), (∀ y : Fˣ, y ∈ Subgroup.zpowers μ) ∧
      conjAct (fsuUL T L I) ⟨d, hdN⟩ =
        ((c.eρ (x * dU μ * x⁻¹) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) := by
  obtain ⟨l, hlL, hlN, hlT0, hlo, μ, hμ, hl⟩ := exists_torus_gen h37 h38 hyp hF hn c
  have hlB : l ∈ B0 T L := mem_oTwoUpper_of_odd ⟨SecA.le_fsuL0 T L hlL, hlT0⟩ hlo
  obtain ⟨hPB, hP2, hPi⟩ := SecA.isSylowTwoOf_T0_inf_B0 hyp
  set P := T0 T L ⊓ B0 T L with hP
  have hB0P : B0 T L ≤ Subgroup.normalizer (P : Set G) :=
    fun b hb => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨(oTwoUpper_le _ hb).2, Subgroup.le_normalizer hb⟩
  set Q := P ⊔ Subgroup.zpowers l with hQ
  have hQB : Q ≤ B0 T L := sup_le hPB (Subgroup.zpowers_le.mpr hlB)
  have hlodd : Odd (Nat.card (Subgroup.zpowers l)) := by rw [Nat.card_zpowers]; exact hlo
  have hDQodd : Odd (Nat.card ↥(D ⊓ Q)) :=
    hD.2.1.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hsup : P ⊔ Subgroup.zpowers l = P ⊔ (D ⊓ Q) := by
    refine le_antisymm (fun y hy => ?_) (sup_le le_sup_left inf_le_right)
    have hyPD : y ∈ ((P ⊔ D : Subgroup G) : Set G) :=
      le_sup_of_hall ⟨hPB, hP2, hPi⟩ hD (hQB hy)
    rw [Subgroup.coe_mul_of_right_le_normalizer_left P D (hD.1.trans hB0P)] at hyPD
    obtain ⟨p, hp, e, he, rfl⟩ := Set.mem_mul.mp hyPD
    have heQ : e ∈ Q := by
      have h1 := Q.mul_mem (Q.inv_mem ((le_sup_left : P ≤ Q) hp)) hy
      rwa [inv_mul_cancel_left] at h1
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right ⟨he, heQ⟩)
  obtain ⟨m, hm, hmD⟩ := exists_conj_of_complement hP2 hlodd
    (Subgroup.zpowers_le.mpr (hB0P hlB)) ((inf_le_left.trans hD.1).trans hB0P)
    (inf_eq_bot_of_odd hP2 hlodd) (inf_eq_bot_of_odd hP2 hDQodd) hsup
  have hdD : m⁻¹ * l * m ∈ D := by
    have h1 : (MulAut.conj m⁻¹).toMonoidHom l ∈ D ⊓ Q := by
      rw [hmD]
      exact ⟨l, Subgroup.mem_zpowers l, rfl⟩
    simpa [MulAut.conj_apply] using h1.1
  have hmL0 : m ∈ fsuL0 T L := (oTwoUpper_le _ (hPB hm)).1
  have hL0U : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (SecA.fsuL0_le_normalizer_fsuVM T L I)
      (SecA.fsuL0_le_normalizer hyp.fsu.maximal.1)
  have hmN := hL0U hmL0
  obtain ⟨l', hl'L, hl'⟩ := SecA.exists_mem_autOn_of_mem_fsuL0 h37 h38 hyp hmL0
  have hAm : conjAct (fsuUL T L I) ⟨m, hmN⟩ ∈ autOn L (fsuUL T L I) := by
    refine SecA.mem_autOn_iff'.mpr ⟨⟨l', le_normalizer_fsuUL T L I hl'L⟩, hl'L, ?_⟩
    refine MulEquiv.ext fun w => Subtype.ext ?_
    simp only [SecA.coe_conjAct_apply']
    exact (hl' w w.2).symm
  set ξ := c.eρ.symm ⟨_, hAm⟩ with hξ
  have hξ' : ((c.eρ ξ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) =
      conjAct (fsuUL T L I) ⟨m, hmN⟩ := by
    rw [hξ, MulEquiv.apply_symm_apply]
  have hdN : m⁻¹ * l * m ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hmN) hlN) hmN
  refine ⟨m⁻¹ * l * m, hdD, hdN, μ, ξ⁻¹ * c.g⁻¹, hμ, ?_⟩
  have he : conjAct (fsuUL T L I) ⟨m⁻¹ * l * m, hdN⟩ =
      (conjAct (fsuUL T L I) ⟨m, hmN⟩)⁻¹ * conjAct (fsuUL T L I) ⟨l, hlN⟩ *
        conjAct (fsuUL T L I) ⟨m, hmN⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have h2 : ((c.eρ (ξ⁻¹ * c.g⁻¹ * dU μ * (ξ⁻¹ * c.g⁻¹)⁻¹) : ↥(autOn L (fsuUL T L I))) :
        MulAut ↥(fsuUL T L I)) =
      ((c.eρ ξ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I))⁻¹ *
        ((c.eρ (c.g⁻¹ * dU μ * c.g) : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) *
          ((c.eρ ξ : ↥(autOn L (fsuUL T L I))) : MulAut ↥(fsuUL T L I)) := by
    have e : ξ⁻¹ * c.g⁻¹ * dU μ * (ξ⁻¹ * c.g⁻¹)⁻¹ = ξ⁻¹ * (c.g⁻¹ * dU μ * c.g) * ξ := by group
    rw [e, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [he, hl, ← hξ', h2]

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
