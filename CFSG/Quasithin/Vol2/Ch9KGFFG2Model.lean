module

public import CFSG.Quasithin.Vol2.Ch9KGFFG2Act
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.G2M

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2Id Matrix
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev
  CFSG.Quasithin.B42G2Cur CFSG.QuasithinUnique.Setup.X6 CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Timmesfeld.RankTwo (hexRoot)
open scoped commutatorElement

variable {F : Type} [Field F]

theorem exists_psiEquiv
    [Finite F] [CharP F 2] {f : ℕ} (hK : Nat.card F = 2 ^ f) (hf : 2 ≤ f) :
    ∃ ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F),
      ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c := by
  obtain ⟨ψ, hψ, hsurj, hker⟩ := exists_adjointGroup_hom_cayleyGroup hK hf
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, center_adjointGroup_eq_bot]
  exact ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩, hψ⟩

section Defs

@[expose] noncomputable def par
    (i : Fin Tag.G2.rank) : Subgroup ↥(adjointGroup .G2 F) :=
  (parabolicSubgroup .G2 F {i}).subgroupOf (adjointGroup .G2 F)

@[expose] noncomputable def core
    (i : Fin Tag.G2.rank) : Subgroup ↥(adjointGroup .G2 F) := perfectCore (par (F := F) i)

@[expose] noncomputable def rad
    (i : Fin Tag.G2.rank) : Subgroup ↥(adjointGroup .G2 F) := pCoreOf 2 (core (F := F) i)

@[expose] noncomputable def radical
    (i : Fin Tag.G2.rank) : Subgroup ↥(adjointGroup .G2 F) :=
  (parabolicRadical .G2 F {i}).subgroupOf (adjointGroup .G2 F)

@[expose] noncomputable def lev
    (i : Fin Tag.G2.rank) : Subgroup ↥(adjointGroup .G2 F) :=
  (Subgroup.closure (Set.range (xUnit .G2 F i) ∪
    Set.range (yUnit .G2 F i))).subgroupOf (adjointGroup .G2 F)

theorem radical_le_par
    (i : Fin Tag.G2.rank) :
    radical (F := F) i ≤ par i := fun _ hx =>
  ((parabolicRadical_le_posUnipotent _).trans (posUnipotent_le_parabolicSubgroup _)) hx

theorem core_le_par
    (i : Fin Tag.G2.rank) :
    core (F := F) i ≤ par i := perfectCore_le _

theorem rad_le_core
    (i : Fin Tag.G2.rank) :
    rad (F := F) i ≤ core i :=
  CFSG.LieType.BorelTits.pCoreOf_le 2 _

end Defs

section Basic

theorem mem_par_iff
    {i : Fin Tag.G2.rank}
    {g : ↥(adjointGroup .G2 F)} :
    g ∈ par i ↔ (g : ModGL .G2 F) ∈ parabolicSubgroup .G2 F {i} := Iff.rfl

theorem mem_radical_iff
    {i : Fin Tag.G2.rank}
    {g : ↥(adjointGroup .G2 F)} :
    g ∈ radical i ↔ (g : ModGL .G2 F) ∈ parabolicRadical .G2 F {i} := Iff.rfl

theorem xC_mem_lev
    (i : Fin Tag.G2.rank) (c : F) :
    xC .G2 F i c ∈ lev i :=
  Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)

theorem yC_mem_lev
    (i : Fin Tag.G2.rank) (c : F) :
    yC .G2 F i c ∈ lev i :=
  Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

theorem dC_mem_lev (i : Fin Tag.G2.rank)
    (t : Fˣ) : dC .G2 F i t ∈ lev i := by
  rw [dC_eq]
  refine (lev i).mul_mem ((lev i).mul_mem ((lev i).mul_mem (xC_mem_lev i _) (yC_mem_lev i _))
    (xC_mem_lev i _)) ((lev i).mul_mem ((lev i).mul_mem (xC_mem_lev i _) (yC_mem_lev i _))
    (xC_mem_lev i _))

theorem conj_mem_radical
    {i : Fin Tag.G2.rank} {g x : ↥(adjointGroup .G2 F)} (hg : g ∈ par i)
    (hx : x ∈ radical i) : g * x * g⁻¹ ∈ radical i :=
  (Subgroup.mem_normalizer_iff.mp (parabolicSubgroup_le_normalizer_parabolicRadical _ hg) _).mp hx

theorem conj_mem_core
    {i : Fin Tag.G2.rank}
    {g x : ↥(adjointGroup .G2 F)} (hg : g ∈ par i)
    (hx : x ∈ core i) : g * x * g⁻¹ ∈ core i :=
  (Subgroup.mem_normalizer_iff.mp ((Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_perfectCore _)) hg) x).mp hx

theorem xPar_mem_radical
    {i : Fin Tag.G2.rank} {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ parabolicRadicalRoots .G2 {i}) (c : F) :
    xPar (rootOperatorFamily .G2) γ c ∈ radical i :=
  (le_iSup₂_of_le γ hγ le_rfl : rootSubgroup .G2 F γ ≤ parabolicRadical .G2 F {i})
    (coe_xPar_mem hγ.1.1 c)

theorem radical_isPGroup
    [Finite F] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) (i : Fin Tag.G2.rank) :
    IsPGroup 2 ↥(radical (F := F) i) := by
  obtain ⟨k, hk⟩ := hF
  have hQ : IsPGroup 2 ↥(parabolicRadical .G2 F {i}) :=
    IsPGroup.of_card (n := k * (parabolicRadicalRoots .G2 {i}).ncard)
      (by rw [card_parabolicRadical, hk, ← pow_mul])
  exact hQ.comap_of_injective (adjointGroup .G2 F).subtype (Subgroup.subtype_injective _)

theorem radical_inf_core_le_rad
    [Finite F] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) (i : Fin Tag.G2.rank) :
    radical (F := F) i ⊓ core i ≤ rad i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ?_
    ((radical_isPGroup hF i).to_le inf_le_left)
  rw [Subgroup.normal_subgroupOf_iff inf_le_right]
  intro x n hx hn
  exact ⟨conj_mem_radical (core_le_par i hn) hx.1, (core i).mul_mem
    ((core i).mul_mem hn hx.2) ((core i).inv_mem hn)⟩

theorem comm_mem_rad
    [Finite F] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) {i : Fin Tag.G2.rank}
    {t : ↥(adjointGroup .G2 F)} (ht : t ∈ core i) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ parabolicRadicalRoots .G2 {i}) (c : F) :
    t * xPar (rootOperatorFamily .G2) γ c * t⁻¹ * (xPar (rootOperatorFamily .G2) γ c)⁻¹ ∈
      rad i := by
  have hx := xPar_mem_radical (F := F) hγ c
  refine radical_inf_core_le_rad hF i ⟨(radical i).mul_mem
    (conj_mem_radical (core_le_par i ht) hx) ((radical i).inv_mem hx), ?_⟩
  have h1 : xPar (rootOperatorFamily .G2) γ c * t⁻¹ * (xPar (rootOperatorFamily .G2) γ c)⁻¹ ∈
      core i := conj_mem_core (radical_le_par i hx) ((core i).inv_mem ht)
  have e : t * xPar (rootOperatorFamily .G2) γ c * t⁻¹ * (xPar (rootOperatorFamily .G2) γ c)⁻¹ =
      t * (xPar (rootOperatorFamily .G2) γ c * t⁻¹ * (xPar (rootOperatorFamily .G2) γ c)⁻¹) := by
    group
  rw [e]
  exact (core i).mul_mem ht h1

end Basic

section LeviCore

theorem perfectCore_subgroupOf_eq [Finite F]
    {H M : Subgroup (ModGL .G2 F)} (hHM : H ≤ M) :
    perfectCore (H.subgroupOf M) = (perfectCore H).subgroupOf M := by
  have : Finite (ModGL .G2 F) := finite_modGL
  apply Subgroup.map_injective M.subtype_injective
  rw [map_perfectCore, Subgroup.map_subgroupOf_eq_of_le hHM,
    Subgroup.map_subgroupOf_eq_of_le ((perfectCore_le H).trans hHM)]

theorem lev_le_core
    [Finite F] [CharP F 2] (hK4 : ∃ s : Finset F, s.card = 4) (i : Fin Tag.G2.rank) :
    lev (F := F) i ≤ core i := by
  obtain ⟨ρ, -, hrange⟩ := exists_rankOne_injective (τ := .G2) (K := F) (i)
  have hLperf : ⁅ρ.range, ρ.range⁆ = ρ.range := by
    have := CFSG.LinearGroups.special_linear_dimension_two_perfect (K := F) hK4
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.range ρ)
  rw [hrange] at hLperf
  have hLP : Subgroup.closure (Set.range (xUnit .G2 F i) ∪
      Set.range (yUnit .G2 F i)) ≤ parabolicSubgroup .G2 F {i} := by
    refine ((Subgroup.closure_le _).2 ?_).trans (parabolicLevi_le_parabolicSubgroup _)
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_parabolicLevi (Set.mem_singleton _) c
    · exact yUnit_mem_parabolicLevi (Set.mem_singleton _) c
  have hLC := le_perfectCore_of_perfect hLP hLperf
  intro x hx
  show x ∈ perfectCore ((parabolicSubgroup .G2 F {i}).subgroupOf (adjointGroup .G2 F))
  rw [perfectCore_subgroupOf_eq (parabolicSubgroup_le_adjointGroup _ _ _)]
  exact hLC hx

end LeviCore

section HEl

theorem i_cases (i : Fin Tag.G2.rank) : i = iA ∨ i = iR := by
  rcases i with ⟨_ | _ | k, hk⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have h2 : Tag.G2.rank = 2 := rfl
    omega

@[expose] noncomputable def hEl
    (ω : Fˣ) (i : Fin Tag.G2.rank) : ↥(adjointGroup .G2 F) :=
  if i = iA then 1 else dC .G2 F iA (ω ^ 2) * dC .G2 F iR ω

theorem hEl_iA (ω : Fˣ) :
    hEl (F := F) ω iA = 1 := by
  simp [hEl]

theorem hEl_iR (ω : Fˣ) :
    hEl (F := F) ω iR = dC .G2 F iA (ω ^ 2) * dC .G2 F iR ω := by
  simp [hEl]

theorem dA_mul_dR [CharP F 2] (ω : Fˣ) : dA (ω ^ 2) * dR ω = dH (F := F) ω := by
  rw [dA, dR, dH, diag3_mul _ _ (by
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have := ω.ne_zero
    field_simp)]
  apply diag3_congr <;>
    simp only [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, one_mul] <;>
    have := ω.ne_zero <;> field_simp

theorem psi_hEl_iR
    [CharP F 2] (ψ : adjointGroup .G2 F →* cayleyGroup F)
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (ω : Fˣ) : ψ (hEl ω iR) = g2A (dH ω) := by
  rw [hEl_iR, map_mul, psi_dC_zero ψ hψ, psi_dC_one ψ hψ, ← map_mul, dA_mul_dR]

theorem dC_mem_torusGroup
    (i : Fin Tag.G2.rank) (t : Fˣ) : (dC .G2 F i t : ModGL .G2 F) ∈ torusGroup .G2 F :=
  Subgroup.subset_closure ⟨(i, t), rfl⟩

theorem hEl_iR_mem_torusGroup
    (ω : Fˣ) : (hEl ω iR : ModGL .G2 F) ∈ torusGroup .G2 F := by
  rw [hEl_iR]
  exact (torusGroup .G2 F).mul_mem (dC_mem_torusGroup _ _) (dC_mem_torusGroup _ _)

theorem hEl_mem_par (ω : Fˣ)
    (i : Fin Tag.G2.rank) : hEl ω i ∈ par (F := F) i := by
  rcases i_cases i with rfl | rfl
  · rw [hEl_iA]
    exact (par iA).one_mem
  · exact torusGroup_le_parabolicSubgroup _ (hEl_iR_mem_torusGroup ω)

omit [Field F] in
theorem dH_mat [Field F] (ω : Fˣ) : ((dH ω : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![1, 0, 0; 0, (ω : F), 0; 0, 0, ((ω⁻¹ : Fˣ) : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dH_mulVec_e0 (ω : Fˣ) (c : F) :
    ((dH ω : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![c, 0, 0] = ![c, 0, 0] := by
  rw [dH_mat]
  funext k
  fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem dH_adj_mulVec_e0 (ω : Fˣ) (c : F) :
    (adjugate ((dH ω : SL3 F) : Matrix (Fin 3) (Fin 3) F))ᵀ *ᵥ ![c, 0, 0] = ![c, 0, 0] := by
  rw [dH_mat, adjugate_fin_three]
  funext k
  fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem hEl_iR_comm_xC
    [CharP F 2] (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (ω : Fˣ) (c : F) : hEl ω iR * xC .G2 F iR c = xC .G2 F iR c * hEl ω iR := by
  apply ψ.injective
  have h1 := psi_hEl_iR ψ.toMonoidHom hψ ω
  have h2 := psi_xC ψ.toMonoidHom hψ iR c
  simp only [MulEquiv.coe_toMonoidHom] at h1 h2
  rw [map_mul, map_mul, h1, h2, zPsi_r, g2A_mul_g2X, dH_mulVec_e0]

theorem hEl_iR_comm_yC
    [CharP F 2] (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (ω : Fˣ) (c : F) : hEl ω iR * yC .G2 F iR c = yC .G2 F iR c * hEl ω iR := by
  apply ψ.injective
  have h1 := psi_hEl_iR ψ.toMonoidHom hψ ω
  have h2 := psi_yC ψ.toMonoidHom hψ iR c
  simp only [MulEquiv.coe_toMonoidHom] at h1 h2
  rw [map_mul, map_mul, h1, h2, zPsi_negr, g2A_mul_g2Y, dH_adj_mulVec_e0]

theorem parabolicLevi_le_centralizer_hEl
    [CharP F 2] (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (ω : Fˣ) : parabolicLevi .G2 F {iR} ≤
      Subgroup.centralizer ({(hEl ω iR : ModGL .G2 F)} : Set (ModGL .G2 F)) := by
  refine sup_le ?_ ((Subgroup.closure_le _).2 ?_)
  · intro t ht
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (hEl_iR_mem_torusGroup ω))
      (torusGroup_le_diagonalGroup ht)
  · rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [Set.mem_singleton_iff] at hi
      subst hi
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact congrArg Subtype.val (hEl_iR_comm_xC ψ hψ ω c)
    · rw [Set.mem_singleton_iff] at hi
      subst hi
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact congrArg Subtype.val (hEl_iR_comm_yC ψ hψ ω c)

theorem comm_hEl_iR_mem_radical
    [CharP F 2] (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (ω : Fˣ) {n : ↥(adjointGroup .G2 F)} (hn : n ∈ par iR) :
    hEl ω iR * n * (hEl ω iR)⁻¹ * n⁻¹ ∈ radical iR := by
  have hnP : (n : ModGL .G2 F) ∈ parabolicSubgroup .G2 F {iR} := hn
  rw [← parabolicRadical_sup_parabolicLevi, sup_comm] at hnP
  have hLN : parabolicLevi .G2 F {iR} ≤
      Subgroup.normalizer (parabolicRadical .G2 F {iR} : Set (ModGL .G2 F)) :=
    (parabolicLevi_le_parabolicSubgroup _).trans
      (parabolicSubgroup_le_normalizer_parabolicRadical _)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hnP
  obtain ⟨m, hm, q, hq, hmq⟩ := hnP
  have hc : (hEl ω iR : ModGL .G2 F) * m = m * hEl ω iR :=
    Subgroup.mem_centralizer_iff.mp (parabolicLevi_le_centralizer_hEl ψ hψ ω hm) _ rfl
  have hhP : (hEl ω iR : ModGL .G2 F) ∈ parabolicSubgroup .G2 F {iR} := hEl_mem_par ω iR
  show ((hEl ω iR * n * (hEl ω iR)⁻¹ * n⁻¹ : ↥(adjointGroup .G2 F)) : ModGL .G2 F) ∈
    parabolicRadical .G2 F {iR}
  have e : ((hEl ω iR * n * (hEl ω iR)⁻¹ * n⁻¹ : ↥(adjointGroup .G2 F)) : ModGL .G2 F) =
      m * ((hEl ω iR : ModGL .G2 F) * q * (hEl ω iR : ModGL .G2 F)⁻¹ * q⁻¹) * m⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hmq]
    have hc' : (hEl ω iR : ModGL .G2 F) * m * (hEl ω iR : ModGL .G2 F)⁻¹ = m := by
      rw [hc, mul_inv_cancel_right]
    calc (hEl ω iR : ModGL .G2 F) * (m * q) * (hEl ω iR : ModGL .G2 F)⁻¹ * (m * q)⁻¹
        = ((hEl ω iR : ModGL .G2 F) * m * (hEl ω iR : ModGL .G2 F)⁻¹) *
            ((hEl ω iR : ModGL .G2 F) * q * (hEl ω iR : ModGL .G2 F)⁻¹ * q⁻¹) * m⁻¹ := by
          group
      _ = _ := by rw [hc']
  rw [e]
  have hq' : (hEl ω iR : ModGL .G2 F) * q * (hEl ω iR : ModGL .G2 F)⁻¹ * q⁻¹ ∈
      parabolicRadical .G2 F {iR} :=
    (parabolicRadical .G2 F {iR}).mul_mem
      ((Subgroup.mem_normalizer_iff.mp
        (parabolicSubgroup_le_normalizer_parabolicRadical _ hhP) q).mp hq)
      ((parabolicRadical .G2 F {iR}).inv_mem hq)
  exact (Subgroup.mem_normalizer_iff.mp (hLN hm) _).mp hq'

theorem comm_hEl_mem_rad
    [Finite F] [CharP F 2] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k)
    (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (ω : Fˣ) (i : Fin Tag.G2.rank) {n : ↥(adjointGroup .G2 F)} (hn : n ∈ core i) :
    hEl ω i * n * (hEl ω i)⁻¹ * n⁻¹ ∈ rad i := by
  rcases i_cases i with rfl | rfl
  · rw [hEl_iA, one_mul, inv_one, mul_one, mul_inv_cancel]
    exact (rad iA).one_mem
  · refine radical_inf_core_le_rad hF iR
      ⟨comm_hEl_iR_mem_radical ψ hψ ω (core_le_par iR hn), ?_⟩
    exact (core iR).mul_mem (conj_mem_core (hEl_mem_par ω iR) hn) ((core iR).inv_mem hn)

theorem hEl_pow_three
    [CharP F 2] (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    {ω : Fˣ} (hω3 : ω ^ 3 = 1) (i : Fin Tag.G2.rank) : hEl ω i ^ 3 = 1 := by
  rcases i_cases i with rfl | rfl
  · rw [hEl_iA, one_pow]
  · apply ψ.injective
    have h1 := psi_hEl_iR ψ.toMonoidHom hψ ω
    simp only [MulEquiv.coe_toMonoidHom] at h1
    rw [map_pow, h1, map_one, ← map_pow]
    have hω : (ω : F) ^ 3 = 1 := by
      have := congrArg Units.val hω3
      simpa using this
    have e : dH (F := F) ω ^ 3 = 1 := by
      apply Subtype.ext
      rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, dH_mat]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, ← pow_three, hω]
    rw [e, map_one]

end HEl

section Fixed

omit [Field F] in
theorem g2Act_smul' [Field F] [CharP F 2] (g : ↥(cayleyGroup F)) (c : F) (w : Ix3 → F) :
    g2Act g (c • w) = c • g2Act g w := by
  have hzI : zI (c • w) = c • zI w := by
    rw [q6_eta w, q6_smul, zI_q6, zI_q6, zmk_smul]
    simp
  rw [g2Act_apply, g2Act_apply, hzI, map_smul, zP_smul]

theorem fixed_of_line [CharP F 2] {G' : Type*} [Group G'] (φ : G' →* ↥(cayleyGroup F))
    {N R : Subgroup G'} (hN : ⁅N, N⁆ = N) (hRN : ∀ n ∈ N, ∀ r ∈ R, n * r * n⁻¹ ∈ R)
    {e : Ix3 → F} (hline : ∀ w, (∀ r ∈ R, g2Act (φ r) w = w) → ∃ s : F, w = s • e)
    {w : Ix3 → F} (hw : ∀ r ∈ R, g2Act (φ r) w = w) {n : G'} (hn : n ∈ N) :
    g2Act (φ n) w = w := by
  obtain ⟨s, rfl⟩ := hline w hw
  by_cases hs : s = 0
  · rw [hs, zero_smul, map_zero]
  by_cases he : e = 0
  · rw [he, smul_zero, map_zero]
  have heR : ∀ r ∈ R, g2Act (φ r) e = e := fun r hr => by
    have h := hw r hr
    rw [g2Act_smul'] at h
    exact smul_right_injective _ hs h
  have hinv : ∀ x ∈ N, ∀ r ∈ R, g2Act (φ r) (g2Act (φ x) e) = g2Act (φ x) e := by
    intro x hx r hr
    have h1 := heR _ (hRN x⁻¹ (N.inv_mem hx) r hr)
    have e1 : φ r = φ x * φ (x⁻¹ * r * x⁻¹⁻¹) * (φ x)⁻¹ := by
      simp only [map_mul, map_inv, inv_inv]
      group
    rw [e1, g2Act_mul_apply', g2Act_mul_apply', ← g2Act_mul_apply' (φ x)⁻¹, inv_mul_cancel,
      map_one, AddMonoid.End.coe_one, id_eq, h1]
  have hsc : ∀ x ∈ N, ∃ α : F, g2Act (φ x) e = α • e := fun x hx => hline _ (hinv x hx)
  have hinvsc : ∀ x ∈ N, ∀ α : F, g2Act (φ x) e = α • e → ∀ β : F,
      g2Act (φ x⁻¹) e = β • e → β * α = 1 := by
    intro x hx α hα β hβ
    have h1 : g2Act (φ (x⁻¹ * x)) e = e := by
      rw [inv_mul_cancel, map_one, map_one]
      rfl
    rw [map_mul, g2Act_mul_apply', hα, g2Act_smul', hβ, smul_smul] at h1
    have h2 : (α * β) • e = (1 : F) • e := by rw [h1, one_smul]
    rw [mul_comm]
    exact smul_left_injective F he h2
  have key : ∀ x ∈ ⁅N, N⁆, g2Act (φ x) e = e := by
    intro x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hg
      obtain ⟨α, hα⟩ := hsc a ha
      obtain ⟨β, hβ⟩ := hsc b hb
      obtain ⟨α', hα'⟩ := hsc a⁻¹ (N.inv_mem ha)
      obtain ⟨β', hβ'⟩ := hsc b⁻¹ (N.inv_mem hb)
      have h1 := hinvsc a ha α hα α' hα'
      have h2 := hinvsc b hb β hβ β' hβ'
      have eφ : φ ⁅a, b⁆ = φ a * φ b * φ a⁻¹ * φ b⁻¹ := by
        rw [commutatorElement_def]
        simp only [map_mul]
      rw [eφ, g2Act_mul_apply', g2Act_mul_apply', g2Act_mul_apply']
      simp only [hβ', hα', hβ, hα, g2Act_smul', smul_smul]
      convert one_smul F e using 2
      linear_combination (β' * β) * h1 + h2
    | one => rw [map_one, map_one]; rfl
    | mul x y _ _ hx hy => rw [map_mul, g2Act_mul_apply', hy, hx]
    | inv x _ hx =>
      have h1 : g2Act (φ (x⁻¹ * x)) e = e := by
        rw [inv_mul_cancel, map_one, map_one]
        rfl
      rw [map_mul, g2Act_mul_apply', hx] at h1
      exact h1
  rw [← hN] at hn
  rw [g2Act_smul', key n hn]

theorem radRoot_iA_r :
    (Pi.single iR 1 : Fin Tag.G2.rank → ℤ) ∈ parabolicRadicalRoots .G2 {iA} :=
  ⟨⟨isRoot_single .G2 iR, by decide⟩, fun h => absurd (h.1.2 iR (by decide)) (by decide)⟩

theorem radRoot_iA_u :
    (hexRoot 4 : Fin Tag.G2.rank → ℤ) ∈ parabolicRadicalRoots .G2 {iA} :=
  ⟨⟨CFSG.Timmesfeld.RankTwo.isRoot_hexRoot 4, by decide⟩,
    fun h => absurd (h.1.2 iR (by decide)) (by decide)⟩

theorem radRoot_iR_u :
    (hexRoot 4 : Fin Tag.G2.rank → ℤ) ∈ parabolicRadicalRoots .G2 {iR} :=
  ⟨⟨CFSG.Timmesfeld.RankTwo.isRoot_hexRoot 4, by decide⟩,
    fun h => absurd (h.1.2 iA (by decide)) (by decide)⟩

theorem radRoot_iR_v :
    (hexRoot 2 : Fin Tag.G2.rank → ℤ) ∈ parabolicRadicalRoots .G2 {iR} :=
  ⟨⟨CFSG.Timmesfeld.RankTwo.isRoot_hexRoot 2, by decide⟩,
    fun h => absurd (h.1.2 iA (by decide)) (by decide)⟩

theorem add_one_ne_zero_of_ne_one [CharP F 2] {δ : F} (hδ : δ ≠ 1) : δ + 1 ≠ 0 := by
  intro h
  apply hδ
  rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq]

theorem inv_add_one_ne_zero [CharP F 2] {δ : Fˣ} (hδ : (δ : F) ≠ 1) :
    ((δ⁻¹ : Fˣ) : F) + 1 ≠ 0 := by
  refine add_one_ne_zero_of_ne_one fun h => hδ ?_
  have h1 : (δ : F) * ((δ⁻¹ : Fˣ) : F) = 1 := Units.mul_inv δ
  rw [h, mul_one] at h1
  exact h1

theorem line_iA
    [Finite F] [CharP F 2] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) (hK4 : ∃ s : Finset F, s.card = 4)
    (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    {δ : Fˣ} (hδ : (δ : F) ≠ 1) {w : Ix3 → F} (hR : ∀ r ∈ rad iA, g2Act (ψ r) w = w) :
    ∃ s : F, w = s • q6 0 0 0 0 0 1 := by
  have ht : dC .G2 F iA δ ∈ core iA := lev_le_core hK4 iA (dC_mem_lev iA δ)
  have hpsi_t : ψ (dC .G2 F iA δ) = g2A (dA δ) := by
    have := psi_dC_zero ψ.toMonoidHom hψ δ
    simpa using this
  have hδ1 := inv_add_one_ne_zero hδ
  have hδ2 := add_one_ne_zero_of_ne_one (δ := (δ : F)) hδ
  have hr : g2Act (g2X ![1, 0, 0]) w = w := by
    set c := (((δ⁻¹ : Fˣ) : F) + 1)⁻¹ with hc
    have hx : ψ (xPar (rootOperatorFamily .G2) (Pi.single iR 1) c) = g2X ![c, 0, 0] := by
      rw [hψ _ (isRoot_single .G2 iR)]
      exact zPsi_r c
    have hk : ψ (dC .G2 F iA δ * xPar (rootOperatorFamily .G2) (Pi.single iR 1) c *
        (dC .G2 F iA δ)⁻¹ * (xPar (rootOperatorFamily .G2) (Pi.single iR 1) c)⁻¹) =
        g2X ![((δ⁻¹ : Fˣ) : F) * c + c, 0, 0] := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpsi_t, hx]
      exact comm_dA_r δ c
    have h := hR _ (comm_mem_rad hF ht radRoot_iA_r c)
    rw [hk] at h
    have e : ((δ⁻¹ : Fˣ) : F) * c + c = 1 := by
      rw [← add_one_mul, hc, mul_inv_cancel₀ hδ1]
    rwa [e] at h
  have hu : g2Act (g2X ![0, 1, 0]) w = w := by
    set c := ((δ : F) + 1)⁻¹ with hc
    have hx : ψ (xPar (rootOperatorFamily .G2) (hexRoot 4) c) = g2X ![0, c, 0] := by
      rw [hψ _ (CFSG.Timmesfeld.RankTwo.isRoot_hexRoot 4)]
      exact zPsi_u c
    have hk : ψ (dC .G2 F iA δ * xPar (rootOperatorFamily .G2) (hexRoot 4) c *
        (dC .G2 F iA δ)⁻¹ * (xPar (rootOperatorFamily .G2) (hexRoot 4) c)⁻¹) =
        g2X ![0, (δ : F) * c + c, 0] := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpsi_t, hx]
      exact comm_dA_u δ c
    have h := hR _ (comm_mem_rad hF ht radRoot_iA_u c)
    rw [hk] at h
    have e : (δ : F) * c + c = 1 := by
      rw [← add_one_mul, hc, mul_inv_cancel₀ hδ2]
    rwa [e] at h
  refine ⟨w (.inr 2), ?_⟩
  rw [q6_smul]
  simpa using eq_of_fixed_r_u hr hu

theorem eq_zero_iR
    [Finite F] [CharP F 2] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) (hK4 : ∃ s : Finset F, s.card = 4)
    (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    {ω : Fˣ} (hω : (ω : F) ≠ 1) {w : Ix3 → F} (hR : ∀ r ∈ rad iR, g2Act (ψ r) w = w)
    (hh : g2Act (ψ (hEl ω iR)) w = w) : w = 0 := by
  have ht : dC .G2 F iR ω ∈ core iR := lev_le_core hK4 iR (dC_mem_lev iR ω)
  have hpsi_t : ψ (dC .G2 F iR ω) = g2A (dR ω) := by
    have := psi_dC_one ψ.toMonoidHom hψ ω
    simpa using this
  have hω1 := inv_add_one_ne_zero hω
  have hω2 := add_one_ne_zero_of_ne_one (δ := (ω : F)) hω
  have hu : g2Act (g2X ![0, 1, 0]) w = w := by
    set c := (((ω⁻¹ : Fˣ) : F) + 1)⁻¹ with hc
    have hx : ψ (xPar (rootOperatorFamily .G2) (hexRoot 4) c) = g2X ![0, c, 0] := by
      rw [hψ _ (CFSG.Timmesfeld.RankTwo.isRoot_hexRoot 4)]
      exact zPsi_u c
    have hk : ψ (dC .G2 F iR ω * xPar (rootOperatorFamily .G2) (hexRoot 4) c *
        (dC .G2 F iR ω)⁻¹ * (xPar (rootOperatorFamily .G2) (hexRoot 4) c)⁻¹) =
        g2X ![0, ((ω⁻¹ : Fˣ) : F) * c + c, 0] := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpsi_t, hx]
      exact comm_dR_u ω c
    have h := hR _ (comm_mem_rad hF ht radRoot_iR_u c)
    rw [hk] at h
    have e : ((ω⁻¹ : Fˣ) : F) * c + c = 1 := by
      rw [← add_one_mul, hc, mul_inv_cancel₀ hω1]
    rwa [e] at h
  have hv : g2Act (g2Y ![0, 0, 1]) w = w := by
    set c := ((ω : F) + 1)⁻¹ with hc
    have hx : ψ (xPar (rootOperatorFamily .G2) (hexRoot 2) c) = g2Y ![0, 0, c] := by
      rw [hψ _ (CFSG.Timmesfeld.RankTwo.isRoot_hexRoot 2)]
      exact zPsi_v c
    have hk : ψ (dC .G2 F iR ω * xPar (rootOperatorFamily .G2) (hexRoot 2) c *
        (dC .G2 F iR ω)⁻¹ * (xPar (rootOperatorFamily .G2) (hexRoot 2) c)⁻¹) =
        g2Y ![0, 0, (ω : F) * c + c] := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hpsi_t, hx]
      exact comm_dR_v ω c
    have h := hR _ (comm_mem_rad hF ht radRoot_iR_v c)
    rw [hk] at h
    have e : (ω : F) * c + c = 1 := by
      rw [← add_one_mul, hc, mul_inv_cancel₀ hω2]
    rwa [e] at h
  have hw := eq_of_fixed_u_v hu hv
  have h1 := psi_hEl_iR ψ.toMonoidHom hψ ω
  simp only [MulEquiv.coe_toMonoidHom] at h1
  rw [h1, hw, g2Act_dH] at hh
  obtain ⟨-, hb, -, -, -, hf⟩ := q6_inj hh
  have hb0 : w (.inl 1) = 0 := by
    have : ((ω : F) - 1) * w (.inl 1) = 0 := by rw [sub_mul, one_mul, hb, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω)
  have hf0 : w (.inr 2) = 0 := by
    have : ((ω : F) - 1) * w (.inr 2) = 0 := by rw [sub_mul, one_mul, hf, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω)
  rw [hw, hb0, hf0, q6_zero]

theorem fixed_of_rad
    [Finite F] [CharP F 2] (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) (hK4 : ∃ s : Finset F, s.card = 4)
    (ψ : ↥(adjointGroup .G2 F) ≃* ↥(cayleyGroup F))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    {ω : Fˣ} (hω : (ω : F) ≠ 1) (i : Fin Tag.G2.rank) {w : Ix3 → F}
    (hR : ∀ r ∈ rad i, g2Act (ψ r) w = w) (hh : g2Act (ψ (hEl ω i)) w = w)
    {n : ↥(adjointGroup .G2 F)} (hn : n ∈ core i) : g2Act (ψ n) w = w := by
  rcases i_cases i with rfl | rfl
  · refine fixed_of_line ψ.toMonoidHom (perfectCore_perfect _)
      (fun n hn r hr => ?_) (fun w' hw' => line_iA hF hK4 ψ hψ hω hw') hR hn
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hn) r).mp hr
  · rw [eq_zero_iR hF hK4 ψ hψ hω hR hh, map_zero]

end Fixed

end CFSG.Quasithin.H13.Ch9.KGFF.G2M
