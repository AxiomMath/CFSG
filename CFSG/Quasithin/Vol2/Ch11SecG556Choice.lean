module

public import CFSG.Quasithin.Vol2.Ch11SecG556Odd1
public import CFSG.Quasithin.Vol2.Ch11SecGTShape
public import CFSG.Quasithin.Vol2.Ch11SecE42A36
public import CFSG.Quasithin.Vol2.Ch11SecD551D
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecG

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.CosetGeom
open scoped MatrixGroups

variable {G : Type} [Group G]

@[expose] def H1Choice (T L V₁ H₁ : Subgroup G) : Prop :=
  H₁ = KOf L V₁ V₁ ⊔ T ∨
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ Case11_1_2One (KOf L V₁ V₁) ∧
      ¬ oTwoPrime (KOf L V₁ V₁) p ≤ Subgroup.normalizer (L : Set G) ∧
      H₁ = oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁ ⊔ T

namespace H1Choice

variable {T L I V₁ H₁ : Subgroup G} {n : ℕ}

theorem lT_le (hc : H1Choice T L V₁ H₁) : LOf L V₁ ⊔ T ≤ H₁ := by
  rcases hc with rfl | ⟨p, -, -, -, -, rfl⟩
  · exact sup_le_sup_right (le_conjClosure _ _) T
  · exact sup_le_sup_right le_sup_right T

theorem le_kt (hc : H1Choice T L V₁ H₁) : H₁ ≤ KOf L V₁ V₁ ⊔ T := by
  rcases hc with rfl | ⟨p, -, -, -, -, rfl⟩
  · exact le_rfl
  · exact sup_le_sup_right (kOne_le L V₁ p) T

theorem le_normalizer (hV₁ : IsVi T L I n 1 V₁) (hc : H1Choice T L V₁ H₁) :
    H₁ ≤ Subgroup.normalizer (V₁ : Set G) :=
  hc.le_kt.trans (kt_le_normalizer hV₁)

variable [Finite G]

theorem inH (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hc : H1Choice T L V₁ H₁) :
    InH (LOf L V₁ ⊔ T) H₁ :=
  inH_of_le_kt h hV₁ hc.lT_le hc.le_kt

theorem not_le_M (h1110 : Stmt11_1_0) (h1112 : Stmt11_1_2) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hne : KOf L V₁ V₁ ≠ LOf L V₁) (hc : H1Choice T L V₁ H₁) :
    ¬ H₁ ≤ Subgroup.normalizer (L : Set G) := by
  rcases hc with rfl | ⟨p, -, -, -, hPM, rfl⟩
  · exact not_kt_le_M h1110 h1112 h hV₁ hne
  · exact fun hle => hPM (le_sup_left.trans (le_sup_left.trans hle))

theorem oTwoUpper_le (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hc : H1Choice T L V₁ H₁) : oTwoUpper H₁ ≤ KOf L V₁ V₁ := by
  rcases hc with rfl | ⟨p, -, -, -, -, rfl⟩
  · exact oTwoUpper_kt_le h hV₁
  · exact (oTwoUpper_sup_le h (T_le_normalizer_kOne h hV₁ p)).trans (kOne_le L V₁ p)

end H1Choice

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem pCoreOf_kOf_le_T (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    pCoreOf 2 (KOf L V₁ V₁) ≤ T :=
  le_of_normal_of_sylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow le_sup_right)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    (fun _ hr x hx => (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _
        (sup_le Subgroup.le_normalizer
          ((SecA.IsVi.le_normalizer hV₁).trans (SecD.normalizer_le_normalizer_kOf L V₁ V₁))
          hr)) x).mp hx)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem le_normalizer_of_oTwoPrime_le (h1110 : Stmt11_1_0)
    (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁)
    (hA : A36Case4 (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁)))
    (hall : ∀ p : ℕ, p.Prime → oTwoPrime (KOf L V₁ V₁) p ≤ Subgroup.normalizer (L : Set G)) :
    KOf L V₁ V₁ ≤ Subgroup.normalizer (L : Set G) := by
  set K := KOf L V₁ V₁ with hKdef
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπdef
  set F := CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) with hFdef
  have hLK : LOf L V₁ ≤ K := le_conjClosure _ _
  have hL₁M : LOf L V₁ ≤ M := ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  set S := (M.subgroupOf K).map π with hSdef
  have hFS : F ≤ S := by
    rw [hFdef, CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun q => ?_
    intro z hz
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) z
    have hkq : (k : G) ∈ oTwoPrime K q.1.1 := (SecD.mem_oTwoPrime_iff k).mpr hz
    exact ⟨k, hall _ (Nat.prime_of_mem_primeFactors q.1.2) hkq, rfl⟩
  have hFO : F ≤ CFSG.oddCore (↥K ⧸ CFSG.pCore 2 ↥K) :=
    le_sSup ⟨inferInstance, SecE.odd_card_fitting_of_a36 hA⟩
  obtain ⟨-, -, ⟨e⟩, -⟩ := hA
  set φ : ↥K →* SL(2, ZMod 5) := e.toMonoidHom.comp ((QuotientGroup.mk' F).comp π) with hφ
  have hker : ∀ k : ↥K, φ k = 1 → π k ∈ F := by
    intro k hk
    have h1 : QuotientGroup.mk' F (π k) = 1 := by
      apply e.injective
      rw [map_one]
      exact hk
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set ψ : ↥(LOf L V₁) →* SL(2, ZMod 5) := φ.comp (Subgroup.inclusion hLK) with hψ
  have hLperf : commutator ↥(LOf L V₁) = ⊤ := by
    apply Subgroup.map_injective (LOf L V₁).subtype_injective
    rw [Subgroup.map_subtype_commutator, perfectCore_perfect, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hLperf]
  have hne : ψ.range ≠ ⊥ := by
    intro h0
    apply SecE.lOf_not_le_oTwoTwoPrime h1110 h hV₁ (K := K)
    intro l hl
    have h1 : ψ ⟨l, hl⟩ = 1 := by
      have : ψ ⟨l, hl⟩ ∈ ψ.range := ⟨_, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    exact (SecD.mem_oTwoTwoPrime_iff (Subgroup.inclusion hLK ⟨l, hl⟩)).mpr (hFO (hker _ h1))
  have htop := SecE.eq_top_of_perfect_sl2_five hperf hne
  intro k hk
  obtain ⟨l, hl⟩ : ∃ l : ↥(LOf L V₁), ψ l = φ ⟨k, hk⟩ := by
    have : φ ⟨k, hk⟩ ∈ ψ.range := htop ▸ Subgroup.mem_top _
    exact this
  have hkl : φ (⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← hl]
    exact mul_inv_cancel _
  obtain ⟨m, hmM, hmk⟩ := hFS (hker _ hkl)
  have hQ : (m⁻¹ * (⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹) : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq]
    exact hmk
  have hQM : pCoreOf 2 K ≤ M :=
    (SecD.pCoreOf_le_oTwoPrime K 2).trans (hall 2 Nat.prime_two)
  have h1 : ((m⁻¹ * (⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹) : ↥K) : G) ∈ M :=
    hQM ((mem_pCoreOf_iff_mem_pCore _).mpr hQ)
  have h2 : (m : G) ∈ M := hmM
  have h3 : ((l : ↥(LOf L V₁)) : G) ∈ M := hL₁M l.2
  have e : k = (m : G) * ((m⁻¹ * (⟨k, hk⟩ * (Subgroup.inclusion hLK l)⁻¹) : ↥K) : G) *
      ((l : ↥(LOf L V₁)) : G) := by
    simp [Subgroup.coe_inclusion]
  rw [e]
  exact M.mul_mem (M.mul_mem h2 h1) h3

theorem exists_h1Choice (hShape : FactCase1Shape)
    (hTI : SecD.PointsTIFact) (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1111 : Stmt11_1_1)
    (h1112 : Stmt11_1_2) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n)
    {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) (hne : KOf L V₁ V₁ ≠ LOf L V₁) :
    ∃ H₁ : Subgroup G, H1Choice T L V₁ H₁ ∧ ¬ H₁ ≤ Subgroup.normalizer (L : Set G) ∧
      (Case11_1_2Two L (KOf L V₁ V₁) ∨
        (∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(CFSG.fittingSubgroup
          (↥(KOf L V₁ V₁) ⧸ CFSG.pCore 2 ↥(KOf L V₁ V₁)))) ∨
        ∃ p : ℕ, p.Prime ∧ oTwoUpper H₁ ≤ oTwoPrime (KOf L V₁ V₁) p ⊔ LOf L V₁) := by
  set K := KOf L V₁ V₁ with hKdef
  have hlt : LOf L V₁ < K := lt_of_le_of_ne (le_conjClosure _ _) (Ne.symm hne)
  have hKT : H1Choice T L V₁ (K ⊔ T) := Or.inl rfl
  have hKTM := hKT.not_le_M h1110 h1112 h hV₁ hne
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  rcases (h1141 G T L I n V₁ X h hV₁ hX).2.1 K
      (SecD.kOf_cComp_centralizer hTI h1102 h1110 h1112 h1141 h1143 h hV₁) hlt with hK1 | hK2
  · by_cases hp : ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K))
    · exact ⟨K ⊔ T, hKT, hKTM, Or.inr (Or.inl hp)⟩
    obtain ⟨V₂, hV₂, -⟩ := (h1110 G T L I n h).1 2 (by norm_num) (by norm_num)
    have hn2 : n = 2 := by
      obtain ⟨K'', hLK'', hK'', hNK'', -, hor⟩ :=
        h1112 G T L I n 1 V₁ V₁ V₂ X h (Or.inl rfl) hV₁ hV₁ hV₂ hX
      have hKK'' := SecD.kOf_eq_of_cComp hLK'' hK'' hNK'' (SecD.lOf_ne_bot h1110 h hV₁)
      rcases hor with heq | ⟨-, hn2, -⟩
      · exact absurd (hKK''.trans heq.symm) hne
      · exact hn2
    have hTN := SecA.IsVi.le_normalizer hV₁
    have hsylN : QuasithinUnique.IsSylowTwoOf (T ⊓ Subgroup.normalizer (V₁ : Set G))
        (Subgroup.normalizer (V₁ : Set G)) := by
      rw [inf_eq_left.mpr hTN]
      exact isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
    obtain ⟨K', hLK', hK', hNK', hcase'⟩ := h1111 G T L I n 1 V₁ V₁ h hV₁
      (Or.inl ⟨rfl, SecA.IsVi.ne_bot h hV₁ le_rfl, le_rfl, hsylN⟩)
    have hKK' : K = K' := SecD.kOf_eq_of_cComp hLK' hK' hNK' (SecD.lOf_ne_bot h1110 h hV₁)
    rw [← hKK'] at hcase'
    have hlist : List11_1_1Two (↥K ⧸ CFSG.pCore 2 ↥K) 2 ∨
        List11_1_1Three (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rcases hcase' with heq | h2 | h3
      · exact absurd heq.symm hne
      · exact Or.inl (hn2 ▸ h2)
      · exact Or.inr h3.2
    rcases hShape _ hlist (exists_oddCore_of_case11_1_2One hK1) with hA | ⟨p, hpp, -, -, -, hE, -⟩
    ·
      obtain ⟨p, hpp, hPM⟩ : ∃ p : ℕ, p.Prime ∧
          ¬ oTwoPrime K p ≤ Subgroup.normalizer (L : Set G) := by
        by_contra hall
        push Not at hall
        exact hKTM (sup_le (le_normalizer_of_oTwoPrime_le h1110 h hV₁ hA hall) h.normal)
      have : Fact p.Prime := ⟨hpp⟩
      have hQT := pCoreOf_kOf_le_T h hV₁
      have hne1 : CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ≠ ⊥ := by
        intro hbot
        apply hPM
        rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap, hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff] at hy
        exact h.normal (hQT ((mem_pCoreOf_iff_mem_pCore y).mpr hy))
      have hdvd : p ∣ Nat.card ↥(CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K)) := by
        have hle : CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) ≤
            CFSG.fittingSubgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
          CFSG.LocalCores.fitting_characteristic.2.2 _ CFSG.pCore_normal CFSG.pCore_isNilpotent
        refine dvd_trans ?_ (Subgroup.card_dvd_of_le hle)
        rcases (CFSG.pCore_isPGroup (p := p) (G := ↥K ⧸ CFSG.pCore 2 ↥K)).card_eq_or_dvd with
          h1 | h1
        · exact absurd (Subgroup.card_eq_one.mp h1) hne1
        · exact h1
      have hp5 : 5 ≤ p := five_le_of_mod_five hpp (hA.2.2.2 p hpp hdvd).1
      exact ⟨oTwoPrime K p ⊔ LOf L V₁ ⊔ T, Or.inr ⟨p, hpp, hp5, hK1, hPM, rfl⟩,
        fun hle => hPM (le_sup_left.trans (le_sup_left.trans hle)),
        Or.inr (Or.inr ⟨p, hpp, oTwoUpper_sup_le h (T_le_normalizer_kOne h hV₁ p)⟩)⟩
    ·
      exfalso
      apply hp
      obtain ⟨eF⟩ := hE
      refine ⟨p, hpp, IsPGroup.of_card (n := 2) ?_⟩
      have : Fact p.Prime := ⟨hpp⟩
      rw [Nat.card_congr eF.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
  · exact ⟨K ⊔ T, hKT, hKTM, Or.inl hK2⟩

end CFSG.Quasithin.Vol2.Ch11.SecG
