module

public import CFSG.Quasithin.EmptyFaithful.S153QPE3
public import CFSG.Quasithin.H13.L32AKG1468l

public section

namespace CFSG.Quasithin.H13.KGBlk

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom)

section Generic

variable {Γ : Type} [Group Γ]

theorem exists_theta_subgroupOf {L X : Subgroup Γ} (hXL : X ≤ L) {N : Type*} [Group N]
    (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) :
    ∃ θ' : ↥(X.subgroupOf L) →* N, Function.Surjective θ' ∧ IsPGroup 2 θ'.ker := by
  let ε := Subgroup.subgroupOfEquivOfLe hXL
  refine ⟨θ.comp ε.toMonoidHom, hθ.comp ε.surjective, fun z => ?_⟩
  obtain ⟨k, hk'⟩ := hk ⟨ε z, z.2⟩
  refine ⟨k, Subtype.ext ?_⟩
  show ((z : ↥(X.subgroupOf L)) ^ 2 ^ k) = 1
  apply ε.injective
  rw [map_pow, map_one]
  exact congrArg Subtype.val hk'

theorem exists_sylow_le_normalizer {L P : Subgroup Γ} (hpar : IsParabolic2 L P) :
    ∃ S : Subgroup ↥L, IsSylowTwoOf S ⊤ ∧
      S ≤ Subgroup.normalizer (((oTwoUpper P).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  obtain ⟨-, S, hS, hSN⟩ := hpar
  refine ⟨S.subgroupOf L, ⟨le_top, hS.2.1.comap_of_injective L.subtype L.subtype_injective, ?_⟩,
    fun s hs => ?_⟩
  · rw [show ((S.subgroupOf L).subgroupOf ⊤).index = (S.subgroupOf L).index from
      Subgroup.relIndex_top_right _]
    exact hS.2.2
  · have hsP : (s : Γ) ∈ P := hSN ⟨s.2, Subgroup.le_normalizer hs⟩
    exact Subgroup.le_normalizer_comap L.subtype (le_normalizer_oTwoUpper P hsP)

theorem false_of_two_threes_hom {A : Type*} [CommGroup A] {P X : Subgroup Γ}
    (hPX : oTwoUpper P ≤ X) (θ : ↥X →* alternatingGroup (Fin 5)) (hk : IsPGroup 2 θ.ker)
    (κ : A →* Γ) (hκ : Function.Injective κ) {s₁ s₂ : A} (h₁ : κ s₁ ∈ P) (h₂ : κ s₂ ∈ P)
    (h₁3 : s₁ ^ 3 = 1) (h₂3 : s₂ ^ 3 = 1) (n₁ : s₁ ≠ 1) (n₂ : s₂ ≠ 1) (n₃ : s₁ * s₂ ≠ 1)
    (n₄ : s₁ * s₂⁻¹ ≠ 1) : False := by
  have hne : ∀ s : A, s ≠ 1 → κ s ≠ 1 := fun s hs h => hs (hκ (h.trans (map_one κ).symm))
  refine false_of_two_threes hPX θ hk h₁ h₂ ?_ ?_ ?_ (hne _ n₁) (hne _ n₂) ?_ ?_
  · rw [← map_mul, ← map_mul, mul_comm]
  · rw [← map_pow, h₁3, map_one]
  · rw [← map_pow, h₂3, map_one]
  · rw [← map_mul]
    exact hne _ n₃
  · rw [← map_inv, ← map_mul]
    exact hne _ n₄

end Generic

section Diag

variable (F : Type) [Field F]

noncomputable def diag3 : Fˣ × Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun p := ⟨Matrix.diagonal ![(p.1 : F), (p.2 : F), ((p.1 * p.2)⁻¹ : Fˣ)], by
    rw [Matrix.det_diagonal, Fin.prod_univ_three]
    show (p.1 : F) * p.2 * (((p.1 * p.2)⁻¹ : Fˣ) : F) = 1
    rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    show Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' p q := by
    apply Subtype.ext
    show Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp
    ring

variable {F}

theorem diag3_apply (p : Fˣ × Fˣ) (i : Fin 3) :
    ((diag3 F p : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i i =
      ![(p.1 : F), (p.2 : F), ((p.1 * p.2)⁻¹ : Fˣ)] i := Matrix.diagonal_apply_eq _ i

theorem diag3_injective : Function.Injective (diag3 F) := by
  intro p q h
  have h0 := congrArg (fun A : SpecialLinearGroup (Fin 3) F =>
    (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  have h1 := congrArg (fun A : SpecialLinearGroup (Fin 3) F =>
    (A : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp only [diag3_apply] at h0 h1
  exact Prod.ext (Units.ext h0) (Units.ext h1)

theorem diag3_mem_upperTriangular (p : Fˣ × Fˣ) : diag3 F p ∈ LinearFlag.upperTriangular 3 F := by
  rw [LinearFlag.mem_upperTriangular]
  intro i j hij
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

end Diag

variable {G : Type} [Group G] [Finite G] {Y R M I : Subgroup G}

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem false_of_a6Block {V : Subgroup G} (hIY : I ≤ Y) (hsub : IsSubnormal I Y) (hRY : R ≤ Y)
    (hR : R ≤ Subgroup.normalizer (I : Set G))
    (h11 : pCoreOf 2 (I ⊔ R) ≤ (I ⊔ R) ⊓ Subgroup.centralizer (V : Set G))
    (h12 : (I ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (I ⊔ R) ⊔ oTwoZIn I)
    (hIV : I ≤ Subgroup.normalizer (V : Set G)) {α : ↥I →* alternatingGroup (Fin 6)}
    (hα : IsAltBlockTypeWith I 6 α) (hmax : IsMaxParabolic2 (autOn I V) (autOn (M ⊓ I) V))
    (θ : ↥(autOn (oTwoUpper (I ⊓ M)) V) →* alternatingGroup (Fin 5))
    (hθ : Function.Surjective θ) : False := by
  obtain ⟨hker, hOC, hα1⟩ := He17.alt_kernel_facts hIY hsub hRY hR h11 h12 (by norm_num) hα
  obtain ⟨-, e, -⟩ := He17.exists_autOn_equiv hIV hα.1
    (fun x => ⟨fun h => hOC ((hker x).mp h), hα1 x⟩)
  obtain ⟨⟨hPL, S, hS, hSN⟩, hne, -⟩ := hmax
  have hLc : Nat.card ↥(autOn I V) = 360 := by rw [Nat.card_congr e.toEquiv, card_alt_six]
  have hS8 : Nat.card S = 8 := by
    have h1 := Subgroup.card_mul_index (S.subgroupOf (autOn I V))
    have h2 : Nat.card (S.subgroupOf (autOn I V)) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
    rw [h2, hLc] at h1
    have hSi := hS.2.2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS.2.1
    rw [hk] at h1
    have hk3 : k = 3 := by
      rcases Nat.lt_or_ge k 4 with hk4 | hk4
      · interval_cases k <;> first | rfl | (norm_num at h1; omega)
      · exfalso
        obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
        have : 2 ^ (m + 4) * (S.subgroupOf (autOn I V)).index =
            16 * (2 ^ m * (S.subgroupOf (autOn I V)).index) := by ring
        omega
    rw [hk, hk3]
    norm_num
  have hSP : S ≤ autOn (M ⊓ I) V := fun s hs => hSN ⟨hS.1 hs, Subgroup.le_normalizer hs⟩
  have hXP : autOn (oTwoUpper (I ⊓ M)) V ≤ autOn (M ⊓ I) V := autOn_mono oTwoUpper_le_inf
  have h60 : 60 ∣ Nat.card ↥(autOn (M ⊓ I) V) :=
    (card_alt_five ▸ Subgroup.card_dvd_of_surjective hθ).trans (Subgroup.card_dvd_of_le hXP)
  have h8 : 8 ∣ Nat.card ↥(autOn (M ⊓ I) V) := hS8 ▸ Subgroup.card_dvd_of_le hSP
  have h120 : 120 ∣ Nat.card ↥(autOn (M ⊓ I) V) := by
    have := Nat.lcm_dvd h60 h8
    rwa [show Nat.lcm 60 8 = 120 by norm_num] at this
  have hidx : ((autOn (M ⊓ I) V).subgroupOf (autOn I V)).index ≤ 3 := by
    have h1 := Subgroup.card_mul_index ((autOn (M ⊓ I) V).subgroupOf (autOn I V))
    have h2 : Nat.card ((autOn (M ⊓ I) V).subgroupOf (autOn I V)) = Nat.card (autOn (M ⊓ I) V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
    rw [h2, hLc] at h1
    obtain ⟨j, hj⟩ := h120
    rw [hj, mul_assoc] at h1
    have h3 : j * ((autOn (M ⊓ I) V).subgroupOf (autOn I V)).index = 3 :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 120) (h1.trans (by norm_num))
    exact Nat.le_of_dvd (by norm_num) (Dvd.intro_left j h3)
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥(autOn I V) := e.isSimpleGroup
  have htop := eq_top_of_factorial_index_lt ((autOn (M ⊓ I) V).subgroupOf (autOn I V)) (by
    calc ((autOn (M ⊓ I) V).subgroupOf (autOn I V)).index.factorial ≤ (3 : ℕ).factorial :=
          Nat.factorial_le hidx
      _ < Nat.card ↥(autOn I V) := by rw [hLc]; decide)
  apply hne
  refine le_antisymm hPL fun x hx => ?_
  have : (⟨x, hx⟩ : ↥(autOn I V)) ∈ (autOn (M ⊓ I) V).subgroupOf (autOn I V) :=
    htop ▸ Subgroup.mem_top _
  exact this

theorem exists_omega {F : Type} [Field F] [Fintype F] (hcard : Fintype.card F = 4) :
    ∃ ω : Fˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have hcardU : Nat.card Fˣ = 3 := by rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hcardU])
  refine ⟨ω, hω ▸ pow_orderOf_eq_one ω, fun h => ?_⟩
  rw [h, orderOf_one] at hω
  omega

theorem false_of_sp4Block {V : Subgroup G} (hIV : I ≤ Subgroup.normalizer (V : Set G))
    (hD : I ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn I)
    (hOC : pCoreOf 2 I ≤ Subgroup.centralizer (V : Set G)) (hsp : IsSp4Block I)
    (hmax : IsMaxParabolic2 (autOn I V) (autOn (M ⊓ I) V))
    (θ : ↥(autOn (oTwoUpper (I ⊓ M)) V) →* alternatingGroup (Fin 5)) (hk : IsPGroup 2 θ.ker) :
    False := by
  classical
  obtain ⟨F, hF, hFin, hcard, e, -⟩ := He17.exists_equiv_of_isSp4Block hIV hD hOC hsp
  have : CharP F 2 := SBc17.charP_two_of_card_eq_pow (n := 2) (by rw [hcard]; norm_num)
  have : Finite F := Finite.of_fintype F
  have hP := QP.isMaxParabolic2_top_of_mulEquiv hmax e
  obtain ⟨-, S, hSyl, hSN⟩ := hP.1
  obtain ⟨g, hg⟩ := QP.exists_conj_isSylowTwoOf (SzN2.isSylowTwoOf_unipotent (K := F)) hSyl
  obtain ⟨ω, hω3, hω1⟩ := exists_omega hcard
  have hT : ∀ s : Fin 2 → Fˣ, MulAut.conj g (torusHom s) ∈
      ((autOn (M ⊓ I) V).subgroupOf (autOn I V)).map e.toMonoidHom := by
    intro s
    apply hSN
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
    have h1 : torusHom s ∈ Subgroup.normalizer
        (SymplecticFlag.unipotent 2 F : Set ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) := by
      rw [SymplecticHigher.normalizer_unipotent]
      exact SymplecticFlag.torus_le_borelSubgroup ⟨s, rfl⟩
    rw [hg, ← Subgroup.map_equiv_normalizer_eq (SymplecticFlag.unipotent 2 F) (MulAut.conj g)]
    exact ⟨_, h1, rfl⟩
  let κ : (Fin 2 → Fˣ) →* MulAut ↥V := (autOn I V).subtype.comp
    (e.symm.toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp torusHom))
  have hκ : Function.Injective κ := (autOn I V).subtype_injective.comp
    (e.symm.injective.comp ((MulAut.conj g).injective.comp SymplecticTorusWeyl.torusHom_injective))
  have hκP : ∀ s, κ s ∈ autOn (M ⊓ I) V := by
    intro s
    have := hT s
    rw [Subgroup.mem_map_equiv] at this
    exact this
  have hne1 : (![ω, 1] : Fin 2 → Fˣ) ≠ 1 := fun h => hω1 (congrFun h 0)
  refine false_of_two_threes_hom (autOn_oTwoUpper_inf hIV).symm.le θ hk κ hκ (hκP ![ω, 1])
    (hκP ![1, ω]) ?_ ?_ hne1 (fun h => hω1 (congrFun h 1)) ?_ ?_
  · funext i
    fin_cases i <;> simp [hω3]
  · funext i
    fin_cases i <;> simp [hω3]
  · intro h
    have := congrFun h 0
    simp at this
    exact hω1 this
  · intro h
    have := congrFun h 0
    simp at this
    exact hω1 this

theorem false_of_sl3 {V : Subgroup G} (hIV : I ≤ Subgroup.normalizer (V : Set G))
    (hg : (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
        Nonempty (↥(autOn I V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
      IsMaxParabolic2 (autOn I V) (autOn (M ⊓ I) V))
    (θ : ↥(autOn (oTwoUpper (I ⊓ M)) V) →* alternatingGroup (Fin 5))
    (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) : False := by
  classical
  obtain ⟨⟨n, F, _, _, hn1, hcard, ⟨e₀⟩⟩, hmax⟩ := hg
  have : CharP F 2 := SBc17.charP_two_of_card_eq_pow hcard
  have : Finite F := Finite.of_fintype F
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  let e : ↥(autOn I V) ≃* SpecialLinearGroup (Fin 3) F :=
    e₀.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm
  have hXeq : autOn (oTwoUpper (I ⊓ M)) V = oTwoUpper (autOn (M ⊓ I) V) := autOn_oTwoUpper_inf hIV
  have hXL : autOn (oTwoUpper (I ⊓ M)) V ≤ autOn I V :=
    (autOn_mono oTwoUpper_le_inf).trans hmax.1.1
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl | rfl : n = 1 ∨ n = 2 := by omega
    ·
      obtain ⟨x, hx⟩ := exists_orderOf_five card_alt_five θ hθ
      have h5 := orderOf_dvd_natCard (⟨(x : MulAut ↥V), hXL x.2⟩ : ↥(autOn I V))
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx, Nat.card_congr e.toEquiv,
        Matrix.card_SL_field, hcard, Fin.prod_univ_three] at h5
      norm_num at h5
    ·
      have hP := QP.isMaxParabolic2_top_of_mulEquiv hmax e
      obtain ⟨-, S, hSyl, hSN⟩ := hP.1
      obtain ⟨U, hU⟩ := LinearFlag.exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
      have hUs : IsSylowTwoOf (LinearFlag.unitriangular 3 F) ⊤ := hU ▸ isSylowTwoOf_top_of_sylow U
      obtain ⟨g, hg⟩ := QP.exists_conj_isSylowTwoOf hUs hSyl
      obtain ⟨ω, hω3, hω1⟩ := exists_omega (by rw [hcard]; norm_num)
      have hT : ∀ p : Fˣ × Fˣ, MulAut.conj g (diag3 F p) ∈
          ((autOn (M ⊓ I) V).subgroupOf (autOn I V)).map e.toMonoidHom := by
        intro p
        apply hSN
        refine Subgroup.mem_inf.2 ⟨Subgroup.mem_top _, ?_⟩
        have h1 : diag3 F p ∈ Subgroup.normalizer
            (LinearFlag.unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F)) := by
          rw [LinearFlag.normalizer_unitriangular]
          exact diag3_mem_upperTriangular p
        rw [hg, ← Subgroup.map_equiv_normalizer_eq (LinearFlag.unitriangular 3 F) (MulAut.conj g)]
        exact ⟨_, h1, rfl⟩
      let κ : Fˣ × Fˣ →* MulAut ↥V := (autOn I V).subtype.comp
        (e.symm.toMonoidHom.comp ((MulAut.conj g).toMonoidHom.comp (diag3 F)))
      have hκ : Function.Injective κ := (autOn I V).subtype_injective.comp
        (e.symm.injective.comp ((MulAut.conj g).injective.comp diag3_injective))
      have hκP : ∀ p, κ p ∈ autOn (M ⊓ I) V := by
        intro p
        have := hT p
        rw [Subgroup.mem_map_equiv] at this
        exact this
      refine false_of_two_threes_hom hXeq.symm.le θ hk κ hκ (hκP (ω, ω⁻¹)) (hκP (1, ω)) ?_ ?_
        (fun h => hω1 (congrArg Prod.fst h)) (fun h => hω1 (congrArg Prod.snd h)) ?_ ?_
      · rw [Prod.pow_mk, hω3, inv_pow, hω3, inv_one]
        rfl
      · rw [Prod.pow_mk, one_pow, hω3]
        rfl
      · intro h
        have := congrArg Prod.fst h
        simp at this
        exact hω1 this
      · intro h
        have := congrArg Prod.fst h
        simp at this
        exact hω1 this
  · obtain ⟨Ŝ, hŜ, hŜN⟩ := exists_sylow_le_normalizer hmax.1
    rw [← hXeq] at hŜN
    obtain ⟨θ', hθ's, hθ'k⟩ := exists_theta_subgroupOf hXL θ hθ hk
    exact QP.false_of_sylow_normalizes_sl3 hn3 hFn e hŜ hŜN card_alt_five θ' hθ's hθ'k

theorem false_of_l45 {V : Subgroup G} (hIV : I ≤ Subgroup.normalizer (V : Set G))
    (he : Nonempty (↥(autOn I V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2))) ∨
      Nonempty (↥(autOn I V) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2))))
    (hpar : IsParabolic2 (autOn I V) (autOn (M ⊓ I) V))
    (θ : ↥(autOn (oTwoUpper (I ⊓ M)) V) →* alternatingGroup (Fin 5))
    (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) : False := by
  have hXeq : autOn (oTwoUpper (I ⊓ M)) V = oTwoUpper (autOn (M ⊓ I) V) := autOn_oTwoUpper_inf hIV
  have hXL : autOn (oTwoUpper (I ⊓ M)) V ≤ autOn I V := (autOn_mono oTwoUpper_le_inf).trans hpar.1
  obtain ⟨Ŝ, hŜ, hŜN⟩ := exists_sylow_le_normalizer hpar
  rw [← hXeq] at hŜN
  obtain ⟨θ', hθ's, hθ'k⟩ := exists_theta_subgroupOf hXL θ hθ hk
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases he with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact QP.false_of_sylow_normalizes_sl4 hF
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm) hŜ hŜN
      card_alt_five θ' hθ's hθ'k
  · exact QP.false_of_sylow_normalizes_sl5 hF
      (e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm) hŜ hŜN
      card_alt_five θ' hθ's hθ'k

end CFSG.Quasithin.H13.KGBlk
