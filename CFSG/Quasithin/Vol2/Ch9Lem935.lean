module

public import CFSG.Quasithin.Vol2.Ch9Sec3LSide
public import CFSG.Quasithin.Vol2.Ch9Sec3Red

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

namespace IsCoord

variable {S : Setup T L I n} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {e : ↥(fsuV T I) ≃* Om4.VM K}
  {ψ : ↥(fsuL0 T L) →* SpecialLinearGroup (Fin 2) K × SpecialLinearGroup (Fin 2) K}
  (hc : S.IsCoord e ψ)
include hc

theorem e_conj (k : ↥(fsuL0 T L)) (v : ↥(fsuV T I))
    (h : (k : G) * v * (k : G)⁻¹ ∈ fsuV T I) :
    e ⟨(k : G) * v * (k : G)⁻¹, h⟩ = Om4.rho (ψ k) (e v) := by
  rw [← hc.bar_L0, bar_apply]
  rfl

variable {D : Subgroup G}

theorem exists_moved (h2 : n = 2)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K))
    (hL : (L.subgroupOf (fsuL0 T L)).map ψ = (MonoidHom.snd _ _).ker ∨
      (L.subgroupOf (fsuL0 T L)).map ψ = (MonoidHom.fst _ _).ker) :
    ∃ l ∈ L, ∃ b ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G),
      ∃ v ∈ fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G),
        b * (l * v * l⁻¹) * b⁻¹ ≠ l * v * l⁻¹ := by
  have hK4 : Fintype.card K = 4 := by rw [hc.card, h2]; norm_num
  have : Nontrivial Kˣ := by
    classical
    exact Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_units, hK4]; norm_num)
  obtain ⟨ω, hω⟩ := exists_ne (1 : Kˣ)
  have hω3 := pow_three_eq_one_of_card_four hK4 ω
  obtain ⟨b, hbD, hbL, hψb⟩ := exists_mem_of_diag hdiag ω ω⁻¹
  have hbB : b ∈ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) :=
    ⟨hbD, (hc.mem_centralizer_V1_iff_diag ⟨b, hbL⟩ ω ω⁻¹ hψb).mpr (mul_inv_cancel ω)⟩
  let w : SpecialLinearGroup (Fin 2) K := ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp only [mul_zero, mul_one, zero_sub]
    exact CharTwo.neg_eq 1⟩
  set v := e.symm (Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0])) with hvdef
  have hv := hc.symm_mem (e := e) 1
  have hev : e v = Multiplicative.ofAdd ((1 : K) • !![(1 : K), 0; 0, 0]) := by
    rw [hvdef, MulEquiv.apply_symm_apply]
  have key : ∀ l ∈ L, ∀ hlL : l ∈ fsuL0 T L,
      (Multiplicative.toAdd (Om4.rho (ψ ⟨b, hbL⟩) (Om4.rho (ψ ⟨l, hlL⟩) (e v))) ≠
        Multiplicative.toAdd (Om4.rho (ψ ⟨l, hlL⟩) (e v))) →
      b * (l * v * l⁻¹) * b⁻¹ ≠ l * v * l⁻¹ := by
    intro l hl hlL hne heq
    apply hne
    have hlv : l * (v : G) * l⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V hlL) v).mp v.2
    have h1 := hc.e_conj ⟨l, hlL⟩ v hlv
    have hblv : b * (l * (v : G) * l⁻¹) * b⁻¹ ∈ fsuV T I :=
      (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V hbL) _).mp hlv
    have h3 := hc.e_conj ⟨b, hbL⟩ ⟨_, hlv⟩ hblv
    rw [← h1, ← h3]
    congr 2
    exact Subtype.ext heq
  rcases hL with hL | hL
  · obtain ⟨⟨l, hlL⟩, hl, hψl⟩ := (show ((w, 1) : SpecialLinearGroup (Fin 2) K × _) ∈
        (L.subgroupOf (fsuL0 T L)).map ψ by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
    refine ⟨l, Subgroup.mem_subgroupOf.mp hl, b, hbB, v, hv, key l (Subgroup.mem_subgroupOf.mp hl)
      hlL fun h => ?_⟩
    rw [hψl, hψb, hev] at h
    have h1 := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 1 0) h
    simp only [toAdd_rho, toAdd_ofAdd, mul_mul_transpose_apply, coe_diagOf] at h1
    simp [w] at h1
    have h4 : (ω⁻¹ * ω⁻¹ : Kˣ) = 1 := Units.ext (by simpa using h1)
    apply hω
    calc ω = ω ^ 3 * (ω⁻¹ * ω⁻¹) := by group
      _ = 1 := by rw [hω3, h4, one_mul]
  · obtain ⟨⟨l, hlL⟩, hl, hψl⟩ := (show ((1, w) : SpecialLinearGroup (Fin 2) K × _) ∈
        (L.subgroupOf (fsuL0 T L)).map ψ by rw [hL]; exact MonoidHom.mem_ker.mpr rfl)
    refine ⟨l, Subgroup.mem_subgroupOf.mp hl, b, hbB, v, hv, key l (Subgroup.mem_subgroupOf.mp hl)
      hlL fun h => ?_⟩
    rw [hψl, hψb, hev] at h
    have h1 := congrArg (fun X : Matrix (Fin 2) (Fin 2) K => X 0 1) h
    simp only [toAdd_rho, toAdd_ofAdd, mul_mul_transpose_apply, coe_diagOf] at h1
    simp [w] at h1
    have h4 : (ω * ω : Kˣ) = 1 := Units.ext (by simpa using h1)
    apply hω
    calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
      _ = 1 := by rw [hω3, h4, inv_one, one_mul]

theorem not_le_centralizer_conjClosure
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) :
    ¬ D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤
        Subgroup.centralizer ((conjClosure (fsuV T I ⊓ Subgroup.centralizer
          ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) L : Subgroup G) : Set G) := by
  intro hle
  obtain ⟨l, hl, b, hb, v, hv, hne⟩ := hc.exists_moved h2 hdiag (hc.map_L h37c h38c)
  have hmem : l * v * l⁻¹ ∈ conjClosure (fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G)) L :=
    Subgroup.subset_closure ⟨l, hl, v, hv, rfl⟩
  apply hne
  rw [(Subgroup.mem_centralizer_iff.mp (hle hb) _ hmem).symm, mul_inv_cancel_right]

theorem not_commutator_le_pCoreOf
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h2 : n = 2)
    (hdiag : (D.subgroupOf (fsuL0 T L)).map ψ = (diagT K).prod (diagT K)) :
    ¬ ⁅L, D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G)⁆ ≤ pCoreOf 2 L := by
  intro hle
  obtain ⟨l, hl, b, hb, v, hv, hne⟩ := hc.exists_moved h2 hdiag (hc.map_L h37c h38c)
  apply hne
  have ho : b * l * b⁻¹ * l⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have h1 : l * b * l⁻¹ * b⁻¹ ∈ pCoreOf 2 L := hle (Subgroup.commutator_mem_commutator hl hb)
    have e : b * l * b⁻¹ * l⁻¹ = (l * b * l⁻¹ * b⁻¹)⁻¹ := by group
    rw [e]
    exact S.pCoreOf_L_le_centralizer (inv_mem h1)
  have hlv : l * v * l⁻¹ ∈ fsuV T I :=
    (Subgroup.mem_normalizer_iff.mp (S.L0_le_normalizer_V (S.L_le_L0 hl)) v).mp hv.1
  have hbv : b * v * b⁻¹ = v := by
    rw [(Subgroup.mem_centralizer_iff.mp hb.2 v hv).symm, mul_inv_cancel_right]
  have e : b * (l * v * l⁻¹) * b⁻¹ =
      (b * l * b⁻¹ * l⁻¹) * (l * v * l⁻¹) * (b * l * b⁻¹ * l⁻¹)⁻¹ := by
    calc b * (l * v * l⁻¹) * b⁻¹ = (b * l * b⁻¹) * (b * v * b⁻¹) * (b * l * b⁻¹)⁻¹ := by group
      _ = (b * l * b⁻¹) * v * (b * l * b⁻¹)⁻¹ := by rw [hbv]
      _ = _ := by group
  rw [e, (Subgroup.mem_centralizer_iff.mp ho _ hlv).symm, mul_inv_cancel_right]

end IsCoord

variable (S : Setup T L I n)
include S

theorem exists_K0' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h2 : n = 2) {K D : Subgroup G} (hKl₁ : K ∈ lFamily (T ⊓ Subgroup.normalizer (L : Set G)))
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) :
    ∃ K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K), L ≤ K₀ ∧ K ≤ K₀ ∧
      L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤ Subgroup.normalizer (K₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  set B := D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) with hB
  have hLM₀ : L ≤ M₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hKM₀ : K ≤ M₀ := le_sup_right
  have hT₁M₀ : T₁ ≤ M₀ := le_sup_right.trans le_sup_left
  have hLl : L ∈ lFamily T₁ :=
    cComp_mem_of_le (X := L ⊔ T) hfsu.maximal.1.2.1 le_sup_left (sup_le_sup_left inf_le_left L)
  obtain ⟨KL, hKLc, hLKL⟩ := CFSG.Quasithin.lemma_1_2_4_exists hfsu.qtke hfsu.simple
    hfsu.nonabelian h37 h39 hM₀O hsyl hLM₀ hLl
  obtain ⟨KK, hKKc, hKKK⟩ := CFSG.Quasithin.lemma_1_2_4_exists hfsu.qtke hfsu.simple
    hfsu.nonabelian h37 h39 hM₀O hsyl hKM₀ hKl₁
  have hKLn := CFSG.Quasithin.lemma_1_2_4_normal hfsu.qtke hfsu.simple hfsu.nonabelian h37 h38
    hM₀O hsyl hLl hLKL hKLc inf_le_right
  have hKLM₀ : KL ≤ M₀ := le_of_mem_cComp hKLc
  refine ⟨KL, hKLc, hLKL, ?_, (Subgroup.normal_subgroupOf_iff_le_normalizer hKLM₀).mp hKLn⟩
  by_contra hKKL
  have hne : KL ≠ KK := fun h => hKKL (h ▸ hKKK)
  obtain ⟨hcomm, -⟩ := CFSG.Quasithin.lemma_1_2_1_two hfsu.qtke hfsu.simple hfsu.nonabelian h37
    hM₀O hKLc hKKc hne
  apply hc.not_commutator_le_pCoreOf h37c h38c h2 hdiag
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    inf_le_left.trans ((hD.1.trans inf_le_left).trans (hc.L0_le_normalizer_L h37 h38 h37c h38c))
  have h1 : ⁅L, B⁆ ≤ pCoreOf 2 KL ⊓ L := by
    refine le_inf ((Subgroup.commutator_mono hLKL (hBK.trans hKKK)).trans
      (hcomm.trans inf_le_left)) ?_
    rw [Subgroup.commutator_le]
    intro l hl b hb
    rw [commutatorElement_def]
    have e' : l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) := by group
    rw [e']
    exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.mp (hBL hb) _).mp (L.inv_mem hl))
  refine h1.trans (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 KL).to_le inf_le_left))
  intro l hl
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 KL (hLKL hl), Subgroup.le_normalizer hl⟩

theorem exists_K0 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (h2 : n = 2) {K D : Subgroup G} (hKl : K ∈ lFamily T)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) :
    ∃ K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K), L ≤ K₀ ∧ K ≤ K₀ ∧
      L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤ Subgroup.normalizer (K₀ : Set G) :=
  S.exists_K0' h37 h38 h39 h37c h38c h2
    (cComp_mem_of_le (X := K ⊔ T) hKl le_sup_left (sup_le_sup_left inf_le_left K)) hD hBK hM₀O
    hsyl

end Setup

end CFSG.Quasithin.H13.Ch9
