module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5o
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.Quasithin.Vol2.Ch12Sec7L5f

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Matrix

namespace S127.L5.Sp4

variable {F : Type} [Field F]

@[expose] def mulVecEquiv (g : ↥(StatedSp 2 F)) :
    (Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 → F) where
  toFun v := mat g *ᵥ v
  invFun v := mat g⁻¹ *ᵥ v
  map_add' v w := Matrix.mulVec_add _ _ _
  map_smul' c v := by simp [Matrix.mulVec_smul]
  left_inv v := mat_inv_mulVec g v
  right_inv v := by
    have h := mat_inv_mulVec g⁻¹ v
    rwa [inv_inv] at h

theorem mulVecEquiv_symm_apply (g : ↥(StatedSp 2 F)) (v : Fin 2 ⊕ Fin 2 → F) :
    (mulVecEquiv g).symm v = mat g⁻¹ *ᵥ v := rfl

theorem exists_map_eq_ell0 [Fintype F] (hF : Fintype.card F = 4)
    {S : Subgroup ↥(StatedSp 2 F)} (hS : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index)
    {W₀ : Submodule F (Fin 2 ⊕ Fin 2 → F)} (hW₀ : Module.finrank F ↥W₀ = 2)
    (hinv : ∀ s ∈ S, ∀ w ∈ W₀, mat s *ᵥ w ∈ W₀) :
    ∃ g : ↥(StatedSp 2 F), W₀.map (mulVecEquiv g : (Fin 2 ⊕ Fin 2 → F) →ₗ[F] _) = ell0 := by
  classical
  have hX : IsPGroup 2 ↥(upperHom (F := F)).range := by
    have hc : Nat.card (Multiplicative (F × F × F)) = 2 ^ 6 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod,
        Nat.card_eq_fintype_card, hF]
      norm_num
    exact (IsPGroup.of_card hc).of_surjective _ (upperHom (F := F)).rangeRestrict_surjective
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ :=
    ⟨le_top, hS, by
      show ¬ 2 ∣ S.relIndex ⊤
      rwa [Subgroup.relIndex_top_right]⟩
  obtain ⟨h, -, hh⟩ := exists_conj_le_of_isSylowTwoOf hSyl le_top hX
  refine ⟨h⁻¹, eq_ell0_of_invariant _ (by rw [LinearEquiv.finrank_map_eq, hW₀]) ?_⟩
  intro a b c w hw
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  set x := upperHom (Multiplicative.ofAdd (a, b, c)) with hx
  have hxS : h * x * h⁻¹ ∈ S := hh ⟨x, ⟨_, rfl⟩, rfl⟩
  refine ⟨mat (h * x * h⁻¹) *ᵥ w₀, hinv _ hxS w₀ hw₀, ?_⟩
  show mat h⁻¹ *ᵥ (mat (h * x * h⁻¹) *ᵥ w₀) = upperMat (symMat a b c) *ᵥ (mat h⁻¹ *ᵥ w₀)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mat_upperHom, ← hx]
  congr 1
  show ((h⁻¹ * (h * x * h⁻¹) : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F).val =
    ((x * h⁻¹ : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F).val
  congr 2
  group

end S127.L5.Sp4

open S127.L5 S127.L5.Sp4 in
theorem sp4BlockLineSplit_holds : Sp4BlockLineSplit := by
  intro G _ _ K V F _ _ α β hK hF hblk hFL hpar
  classical
  obtain ⟨hαs, hαk, hβs, hβk, hβeq⟩ := hblk
  obtain ⟨hVU, W₀, hW₀, hmem⟩ := hFL
  obtain ⟨⟨-, S, hS, hSP⟩, -, -⟩ := hpar
  obtain ⟨hUQ, hU2⟩ := hK.1.2.2.1
  have hNU := CFSG.QuasithinUnique.C1.le_normalizer_blockU K
  have hSV : ∀ s ∈ S, s ∈ Subgroup.normalizer (V : Set G) := fun s hs =>
    (hSP ⟨hS.1 hs, Subgroup.le_normalizer hs⟩).2
  have hSbar2 : IsPGroup 2 ↥((S.subgroupOf K).map α) :=
    (hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).map α
  have hSbari : ¬ 2 ∣ ((S.subgroupOf K).map α).index := fun h =>
    hS.2.2 (h.trans (Subgroup.index_map_dvd _ hαs))
  have hinv : ∀ s ∈ (S.subgroupOf K).map α, ∀ w ∈ W₀, mat s *ᵥ w ∈ W₀ := by
    rintro _ ⟨s, hs, rfl⟩ w hw
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
    have hu' : Multiplicative.toAdd (β u) = w := by rw [hu]; rfl
    have huV : (u : G) ∈ V := (hmem u).mpr (by rw [hu']; exact hw)
    have hsu : (s : G) * u * (s : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hSV s (Subgroup.mem_subgroupOf.mp hs)) u).mp huV
    have hsuU : (s : G) * u * (s : G)⁻¹ ∈ blockU K :=
      (Subgroup.mem_normalizer_iff.mp (hNU s.2) u).mp u.2
    have := (hmem ⟨_, hsuU⟩).mp hsu
    rwa [hβeq s u ⟨_, hsuU⟩ rfl, hu'] at this
  obtain ⟨g, hg⟩ := exists_map_eq_ell0 hF hSbar2 hSbari hW₀ hinv
  let α' : ↥K →* ↥(StatedSp 2 F) := (MulAut.conj g).toMonoidHom.comp α
  let β' : ↥(blockU K) →* Multiplicative (Fin 2 ⊕ Fin 2 → F) :=
    { toFun := fun u => Multiplicative.ofAdd (mat g *ᵥ Multiplicative.toAdd (β u))
      map_one' := by simp
      map_mul' := fun a b => by simp [Matrix.mulVec_add, ofAdd_add] }
  have hβ' : ∀ u, Multiplicative.toAdd (β' u) = mat g *ᵥ Multiplicative.toAdd (β u) :=
    fun u => rfl
  have hβ'1 : ∀ u, β' u = 1 ↔ β u = 1 := by
    intro u
    constructor
    · intro h1
      have h0 : mat g *ᵥ Multiplicative.toAdd (β u) = 0 := by
        rw [← hβ', h1]
        rfl
      have h2 := congrArg (fun v => mat g⁻¹ *ᵥ v) h0
      simp only [mat_inv_mulVec, Matrix.mulVec_zero] at h2
      exact h2
    · intro h1
      apply Multiplicative.toAdd.injective
      rw [hβ', h1]
      exact Matrix.mulVec_zero _
  have hstd : StdSplit K (blockU K) (blockZ K) V α' β' :=
    { comm := fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hUQ hb).2 a (hUQ ha).1
      sq := hU2
      normU := hNU
      kerc := by
        intro k hk u hu
        have hk1 : α k = 1 := by
          have : (MulAut.conj g) (α k) = 1 := hk
          simpa using this
        have hkO : k ∈ CFSG.Open.pCore 2 ↥K := by
          rw [← hαk]
          exact hk1
        have hkQ : (k : G) ∈ blockQ K := Subgroup.mem_map_of_mem K.subtype hkO
        exact Subgroup.mem_centralizer_iff.mp (hUQ hu).2 k hkQ
      surjα := (MulAut.conj g).surjective.comp hαs
      surjβ := by
        intro y
        obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (mat g⁻¹ *ᵥ Multiplicative.toAdd y))
        refine ⟨u, Multiplicative.toAdd.injective ?_⟩
        rw [hβ', hu, toAdd_ofAdd]
        have h := mat_inv_mulVec g⁻¹ (Multiplicative.toAdd y)
        rwa [inv_inv] at h
      kerβ := by
        rw [← hβk]
        ext u
        exact hβ'1 u
      ZU := inf_le_left
      Zc := fun z hz k hk => Subgroup.mem_centralizer_iff.mp hz.2 k hk
      equiv := by
        intro k u v huv
        rw [hβ', hβeq k u v huv, hβ', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        show mat g * mat (α k) = (mat g * mat (α k) * mat g⁻¹) * mat g
        rw [mul_assoc _ (mat g⁻¹), show mat g⁻¹ * mat g = 1 from by
          show ((g⁻¹ * g : ↥(StatedSp 2 F)) : GL (Fin 2 ⊕ Fin 2) F).val = 1
          rw [inv_mul_cancel]
          rfl, mul_one]
      VU := hVU
      memV := by
        intro u
        rw [hmem u, ← hg, Submodule.mem_map_equiv, hβ', mulVecEquiv_symm_apply,
          mat_inv_mulVec] }
  exact hstd.exists_complement hF

end CFSG.Quasithin.H13
