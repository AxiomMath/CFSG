module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNine3CKer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6PGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6M10
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Aut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNRedKer

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NF3C

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup
open scoped commutatorElement

structure CoverModel (G₁₀ : Subgroup (Equiv.Perm (Fin 10))) (G TM : Subgroup Y) (a : ℕ) :
    Prop where
  ML_le : ML ≤ G
  ker : G ⊓ π10.ker = zpowers gZeta
  TM_le : TM ≤ G
  card_TM : Nat.card TM = 2 ^ a
  sup : ML ⊔ TM = G
  map : G.map π10 = G₁₀

theorem coverModel_P : CoverModel A6Models.pgl29 GP TP 4 :=
  ⟨ML_le_GP, inf_ker_GP, TP_le, card_TP, sup_TP, map_GP_π10⟩

theorem coverModel_M : CoverModel A6Models.m10 GM TM 4 :=
  ⟨ML_le_GM, inf_ker_GM, TM_le, card_TM, sup_TM, map_GM_π10⟩

theorem coverModel_A : CoverModel A6Models.autA6 GA TA 5 :=
  ⟨ML_le_GA, inf_ker_GA, TA_le, card_TA, sup_TA, map_GA_π10⟩

theorem factorization_two_pow_mul_three (a : ℕ) : (2 ^ a * 3).factorization 2 = a := by
  rw [Nat.factorization_mul (pow_ne_zero a two_ne_zero) three_ne_zero, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem inf_eq_bot_of_two_three {G : Type*} [Group G] {P Z : Subgroup G} (hP : IsPGroup 2 P)
    (hZ : Nat.card Z = 3) : P ⊓ Z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro x hx
  rw [mem_bot]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx.1⟩
  rw [Subgroup.orderOf_mk] at hk
  have h3 : orderOf x ∣ 3 := by
    have := orderOf_dvd_natCard (⟨x, hx.2⟩ : Z)
    rwa [Subgroup.orderOf_mk, hZ] at this
  rw [hk] at h3
  have hk0 : k = 0 := by
    rcases k with _ | k
    · rfl
    · exfalso
      have h2 : 2 ∣ 3 := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans h3
      omega
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
  exact hk

theorem card_map_of_inf_ker {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G}
    (hK : K ⊓ f.ker = ⊥) : Nat.card (K.map f) = Nat.card K := by
  rw [card_eq_card_range_mul_card_ker (f.comp K.subtype), MonoidHom.range_comp, range_subtype]
  have h1 : (f.comp K.subtype).ker = f.ker.subgroupOf K := by ext x; exact Iff.rfl
  rw [h1, ← card_map_of_injective K.subtype_injective, subgroupOf_map_subtype, inf_comm, hK,
    card_bot, mul_one]

variable {B : Type} [Group B] [Finite B]

theorem exists_embedding_of_cover {L D : Subgroup B} [hLn : L.Normal]
    (hq : CFSG.IsQuasisimple L) (hZ3 : Nat.card (center L) = 3)
    (hC : centralizer (L : Set B) ≤ L) {G₁₀ T₁₀ : Subgroup (Equiv.Perm (Fin 10))}
    (hM : NFA6.ModelFacts G₁₀ A6Models.psl29 T₁₀) (ψ : B →* Equiv.Perm (Fin 10))
    (hψr : ψ.range = G₁₀) (hψk : ψ.ker = centralizer (L : Set B)) {G TM : Subgroup Y} {a : ℕ}
    (hG : CoverModel G₁₀ G TM a) (hT₁₀ : Nat.card T₁₀ = 2 ^ a) (hD : IsSylowIn 2 D ⊤) :
    ∃ ι : B →* Y, Function.Injective ι ∧ ι.range = G ∧ L.map ι = ML ∧ D.map ι = TM := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect L := hq.1
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp inferInstance
  have hkL : ψ.ker ≤ L := hψk ▸ hC
  have hk3 : Nat.card ψ.ker = 3 := by
    rw [hψk, CFSG.LocalAnalysis.UniquenessCase.PartTwo.NF914.centralizer_eq_map_center hC,
      card_map_of_injective L.subtype_injective, hZ3]
  have hkLc : ∀ z ∈ ψ.ker, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    rw [hψk] at hz
    exact (mem_centralizer_iff.mp hz l hl).symm
  have hmapG : L.map ψ ≤ G₁₀ := hψr ▸ map_le_range ψ L
  have hL1 : L.map ψ ≠ ⊥ := by
    intro hbot
    have hLc : L ≤ centralizer (L : Set B) := by
      rw [← hψk]
      intro l hl
      have h1 : ψ l ∈ L.map ψ := mem_map_of_mem ψ hl
      rw [hbot, mem_bot] at h1
      exact h1
    have hL1' : L = ⊥ := by
      rw [← hLperf, eq_bot_iff, commutator_le]
      intro x hx y hy
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact mem_centralizer_iff.mp (hLc hy) x hx
    have h1 : Nat.card (center L) ≤ Nat.card L := card_le_of_le le_top |>.trans_eq card_top
    have h2 : Nat.card L = 1 := by rw [hL1', card_bot]
    omega
  have hψL : L.map ψ = A6Models.psl29 := by
    refine le_antisymm ?_ (hM.le_of_normal _ hmapG ?_ hL1)
    · rw [← hLperf, map_commutator, commutator_le]
      intro x hx y hy
      rw [commutatorElement_def]
      exact hM.commutator_mem (hmapG hx) (hmapG hy)
    · intro g' hg' y hy
      rw [← hψr] at hg'
      obtain ⟨h, rfl⟩ := hg'
      obtain ⟨l, hl, rfl⟩ := hy
      exact ⟨h * l * h⁻¹, hLn.conj_mem l hl h, by simp⟩
  have hcardB : Nat.card B = Nat.card G₁₀ * 3 := by
    rw [card_eq_card_range_mul_card_ker ψ, hψr, hk3]
  have hfac : (Nat.card G₁₀).factorization 2 = a := by
    have h1 := hM.sylow.card_eq
    rw [hT₁₀] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hTM2 : IsPGroup 2 TM := IsPGroup.of_card hG.card_TM
  have hzG : Nat.card (G ⊓ π10.ker : Subgroup Y) = 3 := by rw [hG.ker, card_zpowers_gZeta]
  have hTMk : TM ⊓ π10.ker = ⊥ := by
    have h1 : TM ⊓ π10.ker ≤ TM ⊓ (G ⊓ π10.ker) :=
      le_inf inf_le_left (le_inf (inf_le_left.trans hG.TM_le) inf_le_right)
    exact eq_bot_iff.mpr (h1.trans (inf_eq_bot_of_two_three hTM2 hzG).le)
  have hcTM : Nat.card (TM.map π10) = 2 ^ a := by rw [card_map_of_inf_ker π10 hTMk, hG.card_TM]
  have hS0 : TM.map π10 ≤ ψ.range := by
    rw [hψr, ← hG.map]
    exact map_mono hG.TM_le
  set K := (TM.map π10).comap ψ with hK
  have hkK : ψ.ker ≤ K := fun z hz => by
    rw [hK, mem_comap, (MonoidHom.mem_ker).mp hz]
    exact one_mem _
  have hcardK : Nat.card K = 2 ^ a * 3 := by
    rw [card_eq_card_range_mul_card_ker (ψ.comp K.subtype), MonoidHom.range_comp, range_subtype,
      hK, map_comap_eq, inf_eq_right.mpr hS0, hcTM, ← hk3]
    congr 1
    have h1 : (ψ.comp K.subtype).ker = ψ.ker.subgroupOf K := by ext x; exact Iff.rfl
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkK).toEquiv
  obtain ⟨S⟩ : Nonempty (Sylow 2 K) := Sylow.nonempty
  set P := (S : Subgroup K).map K.subtype with hPdef
  have hcardP : Nat.card P = 2 ^ a := by
    rw [hPdef, card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity S, hcardK,
      factorization_two_pow_mul_three]
  have hP2 : IsPGroup 2 P := IsPGroup.of_card hcardP
  have hPK : P ≤ K := map_subtype_le _
  have hPsyl : IsSylowIn 2 P ⊤ := by
    refine isSylowIn_of_card_eq le_top ?_
    rw [hcardP, card_top, hcardB]
    congr 1
    rw [Nat.factorization_mul (Nat.card_pos.ne') three_ne_zero, Finsupp.add_apply, hfac,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hψP : P.map ψ = TM.map π10 := by
    have hPk : P ⊓ ψ.ker = ⊥ := inf_eq_bot_of_two_three hP2 hk3
    refine eq_of_le_of_card_ge ?_ ?_
    · rw [map_le_iff_le_comap]
      exact hPK
    · rw [card_map_of_inf_ker ψ hPk, hcardP, hcTM]
  have hLP : L ⊔ P = ⊤ := by
    rw [eq_top_iff]
    intro b _
    have h1 : ψ b ∈ (L ⊔ P).map ψ := by
      rw [Subgroup.map_sup, hψP, hψL, ← map_ML_π10, ← Subgroup.map_sup, hG.sup, hG.map, ← hψr]
      exact ⟨b, rfl⟩
    obtain ⟨c, hc, hcb⟩ := h1
    have h2 : b * c⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcb, mul_inv_cancel]
    have h3 := mul_mem (mem_sup_left (hkL h2)) hc
    rwa [inv_mul_cancel_right] at h3
  obtain ⟨φ, hφπ, hφL, hφT⟩ := exists_mulEquiv_of_fibre ψ π10 (L := L) (T := P) (ML := ML)
    (G := G) (TM := TM) (u := uP) (v := vP) hLn hLperf commutator_ML
    (by rw [hψL, map_ML_π10]) hkL hkLc hk3 hG.ML_le (by rw [hG.ker]; exact zpowers_gZeta_le_ML)
    (by
      intro z hz m hm
      rw [hG.ker] at hz
      exact zpowers_gZeta_comm hz hm)
    hzG (by rw [hψL]; exact uv_le (Subgroup.subset_closure (by simp)))
    (by rw [hψL]; exact uv_le (Subgroup.subset_closure (by simp))) uv_comm
    (by rw [hψL, relIndex_uv]; norm_num) hP2 hTM2 hG.TM_le hψP hLP hG.sup
  obtain ⟨g, hg⟩ := NFA6.exists_eq_map_conj hPsyl hD
  refine ⟨G.subtype.comp (φ.toMonoidHom.comp (MulAut.conj g).toMonoidHom), ?_, ?_, ?_, ?_⟩
  · exact G.subtype_injective.comp (φ.injective.comp (MulAut.conj g).injective)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (φ _).2
    · intro hy
      obtain ⟨x, hx⟩ := φ.surjective ⟨y, hy⟩
      refine ⟨g⁻¹ * x * g, ?_⟩
      simp [MulAut.conj_apply, mul_assoc, hx]
  · rw [← map_map, ← map_map]
    have hLg : L.map (MulAut.conj g).toMonoidHom = L := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact hLn.conj_mem l hl g
      · intro hx
        refine ⟨g⁻¹ * x * g, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := hLn.conj_mem x hx g⁻¹
        simpa using this
    rw [hLg, map_map]
    exact hφL
  · rw [show G.subtype.comp (φ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) =
        (G.subtype.comp φ.toMonoidHom).comp (MulAut.conj g).toMonoidHom from rfl, ← map_map,
      ← hg]
    exact hφT


omit [Finite B] in
theorem range_ker_comp {A : Type} [Group A] {ρ : B →* A} (hρ : Function.Surjective ρ)
    {G₁₀ : Subgroup (Equiv.Perm (Fin 10))} (e : A ≃* G₁₀) :
    (G₁₀.subtype.comp (e.toMonoidHom.comp ρ)).range = G₁₀ ∧
      (G₁₀.subtype.comp (e.toMonoidHom.comp ρ)).ker = ρ.ker := by
  refine ⟨?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e (ρ x)).2
    · intro hy
      obtain ⟨x, hx⟩ := hρ (e.symm ⟨y, hy⟩)
      exact ⟨x, by simp [hx]⟩
  · ext x
    simp [MonoidHom.mem_ker]

theorem exists_embedding {L D : Subgroup B} (hLn : L.Normal) (hq : CFSG.IsQuasisimple L)
    (hZ3 : Nat.card (center L) = 3) (hC : centralizer (L : Set B) ≤ L)
    (hρ : ∃ (A : Type) (_ : Group A) (ρ : B →* A), Function.Surjective ρ ∧
      ρ.ker = centralizer (L : Set B) ∧
      (CFSG.Quasithin.F6.IsPGL2 9 A ∨
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsAutOf A
          (alternatingGroup (Fin 6)) ∨
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.IsM10 A))
    (hD : IsSylowIn 2 D ⊤) :
    (∃ ι : B →* Y, Function.Injective ι ∧ ι.range = GP ∧ L.map ι = ML ∧ D.map ι = TP) ∨
      (∃ ι : B →* Y, Function.Injective ι ∧ ι.range = GA ∧ L.map ι = ML ∧ D.map ι = TA) ∨
      (∃ ι : B →* Y, Function.Injective ι ∧ ι.range = GM ∧ L.map ι = ML ∧ D.map ι = TM) := by
  obtain ⟨A, _, ρ, hρs, hρk, hA⟩ := hρ
  rcases hA with h | h | h
  · obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_pgl29_of_isPGL2 h
    obtain ⟨hr, hk⟩ := range_ker_comp hρs e
    exact Or.inl (exists_embedding_of_cover hq hZ3 hC NFA6.PGLModel.modelFacts _ hr
      (hk.trans hρk) coverModel_P Out21.A6.card_Qp hD)
  · obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_autA6_of_isAutOf h
    obtain ⟨hr, hk⟩ := range_ker_comp hρs e
    exact Or.inr (Or.inl (exists_embedding_of_cover hq hZ3 hC NFA6.AutModel.modelFacts _ hr
      (hk.trans hρk) coverModel_A card_P0 hD))
  · obtain ⟨e⟩ := NFA6.nonempty_mulEquiv_m10_of_isM10 h
    obtain ⟨hr, hk⟩ := range_ker_comp hρs e
    exact Or.inr (Or.inr (exists_embedding_of_cover hq hZ3 hC NFA6.M10Model.modelFacts _ hr
      (hk.trans hρk) coverModel_M Out21.A6.card_Qm hD))

end CFSG.LocalAnalysis.WeakClosure81.NF3C
