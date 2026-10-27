module

public import CFSG.Quasithin.Vol2.Ch11SecFFacts3
public import CFSG.Quasithin.Vol2.Ch11SecO2A

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (qSp nSp)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq)
open scoped IsMulCommutative commutatorElement

namespace O2

variable {K : Type} [Field K]

noncomputable def eltE (t : Fin 2 ⊕ Fin 2 → K) : StatedSp 2 K :=
  qSp (t (.inl 0) - t (.inl 1) * t (.inr 1)) (t (.inl 1)) 0 * nSp (-t (.inr 1))

theorem mulVec_E_f0 (t : Fin 2 ⊕ Fin 2 → K) :
    mat 2 K (eltE t) *ᵥ vec4 0 0 1 0 = vec4 (t (.inl 0)) (t (.inl 1)) 1 (t (.inr 1)) := by
  rw [eltE, map_mul, ← Matrix.mulVec_mulVec, nSp_mulVec, qSp_mulVec]
  refine vec4_eq ?_ ?_ ?_ ?_ <;> simp [vec4]

theorem eltE_mem [Finite K] [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    (t : Fin 2 ⊕ Fin 2 → K) : eltE t ∈ pCoreOf 2 (perfectCore (Q2 K 0)) :=
  mul_mem (KA.qSp_mem_pCoreOf hK4 _ _) (KA.nSp_mem_pCoreOf hK4 _)

variable {G : Type} [Group G] {L V : Subgroup G} [IsMulCommutative ↥V]
  {π : ↥(StatedSp 2 K) →* ↥(autOn L V)} {f : ↥V → (Fin 2 ⊕ Fin 2 → K)}

theorem mem_conj_v1_iff {hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L V) ⊥ π f}
    {g : StatedSp 2 K} {V₁ : Subgroup G}
    (hV₁ : V₁.subgroupOf V = hf.pre (gmapSp g (spLine K)).toAddSubgroup) {z : G}
    (hz : z ∈ Subgroup.normalizer (V : Set G)) {γ : StatedSp 2 K}
    (hγ : SecA.conjV V z hz = ((π γ : ↥(autOn L V)) : MulAut ↥V)) (x : ↥V) :
    (x : G) ∈ conjSubgroup V₁ z ↔
      ∃ c : K, f x = c • (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) := by
  rw [CFSG.Quasithin.mem_conjSubgroup_iff]
  have e1 : z * (x : G) * z⁻¹ = ((SecA.conjV V z hz x : ↥V) : G) := by
    rw [SecA.conjV_apply_coe]
  rw [e1, ← Subgroup.mem_subgroupOf, hV₁, hf.mem_pre, Submodule.mem_toAddSubgroup, mem_gS1_iff,
    hγ, hf.act4]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h1 := congrArg (fun v => mat 2 K γ⁻¹ *ᵥ v) hc
    simpa only [mat_inv_mulVec, Matrix.mulVec_smul] using h1
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, Matrix.mulVec_smul, mat_mulVec_inv]⟩

omit [IsMulCommutative ↥V] in
theorem conj_le {V₁ : Subgroup G} (hV₁ : V₁ ≤ V) {z : G}
    (hz : z ∈ Subgroup.normalizer (V : Set G)) : conjSubgroup V₁ z ≤ V := by
  intro x hx
  have h1 := CFSG.Quasithin.mem_conjSubgroup_iff.mp hx
  have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hz) _).mp (hV₁ h1)
  simpa [mul_assoc] using h3

end O2

open O2 in
theorem factSp4Trans_holds : FactSp4Trans := by
  intro G _ _ T L I n V₁ V₃ hS hk hV₁ hV₃ y hy hyopp m hmL hmV hmV₁ hmV₃
  have := SecO1.isMulCommutative hS
  have hn : 2 ≤ n := hS.one_lt
  obtain ⟨K, _, _, _, hK, π, f, hf, g, hπ, -, hV₁g, -, hV₃g⟩ := exists_coord hS hk
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hinj := SecO1.IsCoord.injective_of_bot hf
  have hV₁V := SecA.IsVi.le_fsuV hV₁
  have hy' : m⁻¹ * y * m ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmL) y).mp hy
    simpa only [inv_inv] using this
  have hconj : conjSubgroup V₁ (y * m) = conjSubgroup V₁ (m⁻¹ * y * m) := by
    ext x
    rw [CFSG.Quasithin.mem_conjSubgroup_iff, CFSG.Quasithin.mem_conjSubgroup_iff]
    have e1 : m⁻¹ * y * m * x * (m⁻¹ * y * m)⁻¹ = m⁻¹ * (y * m * x * (y * m)⁻¹) * m⁻¹⁻¹ := by
      group
    rw [e1]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmV₁) _)
  have hy'opp : conjSubgroup V₁ (m⁻¹ * y * m) ⊓ V₃ = ⊥ := by
    rw [← hconj, eq_bot_iff]
    rintro x ⟨hx1, hx3⟩
    have hx1' : x ∈ conjSubgroup V₁ (y * m) := hx1
    have h1 : m * x * m⁻¹ ∈ conjSubgroup V₁ y := by
      rw [CFSG.Quasithin.mem_conjSubgroup_iff] at hx1' ⊢
      simpa only [mul_assoc, _root_.mul_inv_rev] using hx1'
    have h3 : m * x * m⁻¹ ∈ V₃ := (Subgroup.mem_normalizer_iff.mp hmV₃ x).mp hx3
    have h4 : m * x * m⁻¹ ∈ conjSubgroup V₁ y ⊓ V₃ := ⟨h1, h3⟩
    rw [hyopp, Subgroup.mem_bot] at h4
    rw [Subgroup.mem_bot]
    calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
      _ = 1 := by rw [h4]; group
  have hlin : ∀ z (hz : z ∈ L), ∃ γ : StatedSp 2 K, SecA.conjV (fsuV T I) z (hS.le_normalizer hz) =
      ((π γ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
    intro z hz
    obtain ⟨γ, hγ⟩ : ∃ γ : StatedSp 2 K, π γ = ⟨_, SecA.conjV_mem_autOn hz (hS.le_normalizer hz)⟩ :=
      hf.onto _
    exact ⟨γ, by rw [hγ]⟩
  obtain ⟨γ, hγ⟩ := hlin y hy
  obtain ⟨γ', hγ'⟩ := hlin _ hy'
  set u := mat 2 K g⁻¹ *ᵥ (mat 2 K γ⁻¹ *ᵥ (mat 2 K g *ᵥ (vec4 1 0 0 0))) with hu
  set u' := mat 2 K g⁻¹ *ᵥ (mat 2 K γ'⁻¹ *ᵥ (mat 2 K g *ᵥ (vec4 1 0 0 0))) with hu'
  have hopp : ∀ (z : G) (hz : z ∈ L) (δ : StatedSp 2 K),
      SecA.conjV (fsuV T I) z (hS.le_normalizer hz) =
        ((π δ : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) →
      conjSubgroup V₁ z ⊓ V₃ = ⊥ →
      (mat 2 K g⁻¹ *ᵥ (mat 2 K δ⁻¹ *ᵥ (mat 2 K g *ᵥ (vec4 1 0 0 0)))) (.inr 0) ≠ 0 := by
    intro z hz δ hδ hzopp h0
    obtain ⟨v, hv⟩ := hf.surj (mat 2 K δ⁻¹ *ᵥ (mat 2 K g *ᵥ (vec4 1 0 0 0)))
    have hv1 : (v : G) ∈ conjSubgroup V₁ z :=
      (mem_conj_v1_iff (hV₁g V₁ hV₁) _ hδ v).mpr ⟨1, by rw [hv, one_smul]⟩
    have hv3 : (v : G) ∈ V₃ := by
      rw [mem_iff_of_eq (hV₃g V₃ hV₃), hv]
      exact h0
    have h4 : (v : G) ∈ conjSubgroup V₁ z ⊓ V₃ := ⟨hv1, hv3⟩
    rw [hzopp, Subgroup.mem_bot] at h4
    have h5 : v = 1 := Subtype.ext h4
    rw [h5, hf.map_one] at hv
    have h6 := congrArg (fun x => mat 2 K g⁻¹ *ᵥ (mat 2 K δ *ᵥ x)) hv
    simp only [Matrix.mulVec_zero, mat_mulVec_inv, mat_inv_mulVec] at h6
    exact one_ne_zero (congrFun h6 (.inl 0)).symm
  have hu0 := hopp y hy γ hγ hyopp
  have hu'0 := hopp _ hy' γ' hγ' hy'opp
  set û := (u (.inr 0))⁻¹ • u with hû
  set û' := (u' (.inr 0))⁻¹ • u' with hû'
  set N₁ := eltE û * (eltE û')⁻¹ with hN₁
  have hN₁mem : N₁ ∈ pCoreOf 2 (perfectCore (Q2 K 0)) :=
    mul_mem (eltE_mem hK4 û) (inv_mem (eltE_mem hK4 û'))
  have hEû : mat 2 K (eltE û) *ᵥ vec4 0 0 1 0 = û := by
    rw [mulVec_E_f0]
    refine vec4_eq rfl rfl ?_ rfl
    simp only [vec4, Sum.elim_inr, Matrix.cons_val_zero, hû, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel₀ hu0]
  have hEû' : mat 2 K (eltE û') *ᵥ vec4 0 0 1 0 = û' := by
    rw [mulVec_E_f0]
    refine vec4_eq rfl rfl ?_ rfl
    simp only [vec4, Sum.elim_inr, Matrix.cons_val_zero, hû', Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel₀ hu'0]
  have hN₁u : mat 2 K N₁⁻¹ *ᵥ u = (u (.inr 0) / u' (.inr 0)) • u' := by
    have h0 : vec4 0 0 1 0 = mat 2 K (eltE û)⁻¹ *ᵥ û := by
      have h := congrArg (fun x => mat 2 K (eltE û)⁻¹ *ᵥ x) hEû
      simpa only [mat_inv_mulVec] using h
    have h1 : mat 2 K N₁⁻¹ *ᵥ û = û' := by
      rw [hN₁, _root_.mul_inv_rev, inv_inv, map_mul, ← Matrix.mulVec_mulVec, ← h0, hEû']
    have h2 : mat 2 K N₁⁻¹ *ᵥ u = u (.inr 0) • û' := by
      conv_lhs => rw [show u = u (.inr 0) • û by rw [hû, smul_smul, mul_inv_cancel₀ hu0, one_smul]]
      rw [Matrix.mulVec_smul, h1]
    rw [h2, hû', smul_smul, div_eq_mul_inv]
  have hmemL : psiSp π g N₁ ∈ autOn (LOf L V₁) (fsuV T I) := by
    rw [SecA.autOn_lOf hS.le_normalizer hV₁V, hV₁g V₁ hV₁]
    change _ ∈ SecS.gammaW _ _
    rw [gammaW_pre_eq hf g 0 _ flag_one_eq]
    exact ⟨_, Subgroup.map_subtype_le _ hN₁mem, rfl⟩
  obtain ⟨l, hl, hlV, hleq⟩ := SecA.mem_autOn_iff.mp hmemL
  have hlL : l ∈ L := ((perfectCore_le _).trans inf_le_left) hl
  have hr : u (.inr 0) / u' (.inr 0) ≠ 0 := div_ne_zero hu0 hu'0
  have hgu' : mat 2 K g *ᵥ u' = mat 2 K γ'⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) := by
    rw [hu', mat_mulVec_inv]
  have hkey : mat 2 K (γ * (g * N₁ * g⁻¹))⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0) =
      (u (.inr 0) / u' (.inr 0)) • (mat 2 K γ'⁻¹ *ᵥ (mat 2 K g *ᵥ vec4 1 0 0 0)) := by
    rw [show (γ * (g * N₁ * g⁻¹))⁻¹ = g * N₁⁻¹ * g⁻¹ * γ⁻¹ by group, map_mul, map_mul, map_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hu, hN₁u,
      Matrix.mulVec_smul, hgu']
  refine ⟨l, hl, ?_⟩
  rw [hconj]
  have hyl : SecA.conjV (fsuV T I) (y * l) (hS.le_normalizer (L.mul_mem hy hlL)) =
      ((π (γ * (g * N₁ * g⁻¹)) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)) := by
    rw [SecA.conjV_mul _ (hS.le_normalizer hy) hlV, hγ, ← hleq, psiSp_apply, ← Subgroup.coe_mul,
      ← map_mul]
  ext x
  constructor
  · intro hx
    have hxV := conj_le hV₁V (hS.le_normalizer hy') hx
    obtain ⟨c, hc⟩ := (mem_conj_v1_iff (hV₁g V₁ hV₁) _ hγ' ⟨x, hxV⟩).mp hx
    refine (mem_conj_v1_iff (hV₁g V₁ hV₁) _ hyl ⟨x, hxV⟩).mpr
      ⟨c * (u (.inr 0) / u' (.inr 0))⁻¹, ?_⟩
    rw [hc, hkey, smul_smul, mul_assoc, inv_mul_cancel₀ hr, mul_one]
  · intro hx
    have hxV := conj_le hV₁V (hS.le_normalizer (L.mul_mem hy hlL)) hx
    obtain ⟨c, hc⟩ := (mem_conj_v1_iff (hV₁g V₁ hV₁) _ hyl ⟨x, hxV⟩).mp hx
    exact (mem_conj_v1_iff (hV₁g V₁ hV₁) _ hγ' ⟨x, hxV⟩).mpr
      ⟨c * (u (.inr 0) / u' (.inr 0)), by rw [hc, hkey, smul_smul]⟩

end CFSG.Quasithin.Vol2.Ch11.SecF
