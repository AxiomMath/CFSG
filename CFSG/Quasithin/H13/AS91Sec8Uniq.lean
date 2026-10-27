module

public import CFSG.Quasithin.H13.AS91Sec8Pt
public import CFSG.Quasithin.Recognition.UniquenessSystemOrbit
public import CFSG.Quasithin.Recognition.UniquenessSystemCoset

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

variable {G : Type*} [Group G]

structure CosetGeomLocal (G₁ G₂ G₃ : Subgroup G) : Prop where
  exists_pt : ∃ y : G ⧸ G₁, CInc G₁ G₂ y (basePt G₂) ∧ y ≠ basePt G₁
  twoTrans : ∀ a b a' b' : G ⧸ G₁, CInc G₁ G₂ a (basePt G₂) → CInc G₁ G₂ b (basePt G₂) →
    CInc G₁ G₂ a' (basePt G₂) → CInc G₁ G₂ b' (basePt G₂) → a ≠ b → a' ≠ b' →
    ∃ s ∈ G₂ ⊓ G₃, s • a = a' ∧ s • b = b'
  sup_top : G₁ ⊔ G₃ = ⊤
  gen₁ : G₁ ≤ G₁ ⊓ G₂ ⊔ G₁ ⊓ G₃
  gen₃ : G₃ ≤ G₃ ⊓ G₁ ⊔ G₃ ⊓ G₂
  gamma5 : ∀ y : G ⧸ G₁, CInc G₁ G₂ y (basePt G₂) → y ≠ basePt G₁ →
    G₁ ⊓ G₂ ≤ G₁ ⊓ G₂ ⊓ stabilizer G y ⊔ G₁ ⊓ G₂ ⊓ G₃

variable {G₁ G₂ G₃ : Subgroup G}

theorem CosetGeomLocal.adj {y : G ⧸ G₁} (hyl : CInc G₁ G₂ y (basePt G₂))
    (hyx : y ≠ basePt G₁) : (colGraph G₁ G₂).Adj (basePt G₁) y := by
  rw [colGraph_adj]
  exact ⟨hyx.symm, basePt G₂, cInc_mk G₁ G₂ 1, hyl⟩

theorem CosetGeomLocal.swap (h : CosetGeomLocal G₁ G₂ G₃) {y : G ⧸ G₁}
    (hyl : CInc G₁ G₂ y (basePt G₂)) (hyx : y ≠ basePt G₁) :
    ∃ t ∈ G₃, t • basePt G₁ = y ∧ t • y = basePt G₁ := by
  obtain ⟨c, hc, hcx, hcy⟩ := h.twoTrans (basePt G₁) y y (basePt G₁)
    (cInc_mk G₁ G₂ 1) hyl hyl (cInc_mk G₁ G₂ 1) hyx.symm hyx
  exact ⟨c, (Subgroup.mem_inf.mp hc).2, hcx, hcy⟩

private theorem smul_basePt_surj (w : G ⧸ G₁) : ∃ g : G, g • basePt G₁ = w := by
  induction w using QuotientGroup.induction_on with
  | H g => exact ⟨g, by rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]⟩

private theorem mem_of_smul_basePt {g : G} (hg : g • basePt G₁ = basePt G₁) : g ∈ G₁ := by
  have h' : g ∈ MulAction.stabilizer G (basePt G₁) := mem_stabilizer_iff.mpr hg
  rwa [stabilizer_mk_one] at h'

private theorem sup_top_stab (h : CosetGeomLocal G₁ G₂ G₃) :
    MulAction.stabilizer G (basePt G₁) ⊔ G₃ = ⊤ := by
  rw [stabilizer_mk_one]
  exact h.sup_top

private theorem stab_eq_of (h : CosetGeomLocal G₁ G₂ G₃) {y : G ⧸ G₁}
    (hyl : CInc G₁ G₂ y (basePt G₂)) (hyx : y ≠ basePt G₁) :
    MulAction.stabilizer G (basePt G₁) = MulAction.stabilizer G (basePt G₁) ⊓
      MulAction.stabilizer G y ⊔ G₃ ⊓ MulAction.stabilizer G (basePt G₁) := by
  rw [stabilizer_mk_one]
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_right)
  have h1 : G₁ ⊓ G₂ ≤ G₁ ⊓ MulAction.stabilizer G y ⊔ G₃ ⊓ G₁ := by
    refine (h.gamma5 y hyl hyx).trans (sup_le ?_ ?_)
    · exact le_sup_of_le_left (inf_le_inf_right _ inf_le_left)
    · exact le_sup_of_le_right (le_inf inf_le_right (inf_le_left.trans inf_le_left))
  exact h.gen₁.trans (sup_le h1 (le_sup_of_le_right (inf_comm G₁ G₃).le))

private theorem I_eq_of (h : CosetGeomLocal G₁ G₂ G₃) {y : G ⧸ G₁}
    (hyl : CInc G₁ G₂ y (basePt G₂)) (hyx : y ≠ basePt G₁) :
    G₃ = G₃ ⊓ MulAction.stabilizer G (basePt G₁) ⊔
      G₃ ⊓ MulAction.stabilizer G ({basePt G₁, y} : Set (G ⧸ G₁)) := by
  rw [stabilizer_mk_one]
  refine le_antisymm (h.gen₃.trans (sup_le le_sup_left ?_)) (sup_le inf_le_left inf_le_left)
  intro c hc
  obtain ⟨hc3, hc2⟩ := Subgroup.mem_inf.mp hc
  by_cases hcx : c • basePt G₁ = basePt G₁
  · exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hc3, mem_of_smul_basePt hcx⟩)
  · have hcx' : CInc G₁ G₂ (c • basePt G₁) (basePt G₂) :=
      ⟨c, by rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one],
        QuotientGroup.eq.mpr (by rw [mul_one]; exact inv_mem hc2)⟩
    obtain ⟨u, hu, hux, huy⟩ := h.twoTrans (basePt G₁) y (basePt G₁) (c • basePt G₁)
      (cInc_mk G₁ G₂ 1) hyl (cInc_mk G₁ G₂ 1) hcx' hyx.symm (Ne.symm hcx)
    obtain ⟨t, ht, htx, hty⟩ := h.swap hyl hyx
    have hu3 : u ∈ G₃ := (Subgroup.mem_inf.mp hu).2
    have hw : ((u * t)⁻¹ * c) • basePt G₁ = basePt G₁ := by
      rw [mul_smul, ← huy, mul_inv_rev, mul_smul, inv_smul_smul, ← htx, inv_smul_smul]
    have hwG3 : (u * t)⁻¹ * c ∈ G₃ := mul_mem (inv_mem (mul_mem hu3 ht)) hc3
    have htS : t ∈ MulAction.stabilizer G ({basePt G₁, y} : Set (G ⧸ G₁)) := by
      rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, htx, hty,
        Set.pair_comm]
    have huM : u ∈ G₃ ⊓ G₁ ⊔ G₃ ⊓ MulAction.stabilizer G ({basePt G₁, y} : Set (G ⧸ G₁)) :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hu3, mem_of_smul_basePt hux⟩)
    have htM : t ∈ G₃ ⊓ G₁ ⊔ G₃ ⊓ MulAction.stabilizer G ({basePt G₁, y} : Set (G ⧸ G₁)) :=
      Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨ht, htS⟩)
    have hwM : (u * t)⁻¹ * c ∈
        G₃ ⊓ G₁ ⊔ G₃ ⊓ MulAction.stabilizer G ({basePt G₁, y} : Set (G ⧸ G₁)) :=
      Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hwG3, mem_of_smul_basePt hw⟩)
    have hM := mul_mem (mul_mem huM htM) hwM
    rwa [mul_inv_cancel_left] at hM

private theorem exists_smul_of_adj (h : CosetGeomLocal G₁ G₂ G₃) {y : G ⧸ G₁}
    (hyl : CInc G₁ G₂ y (basePt G₂)) (hyx : y ≠ basePt G₁) {u v : G ⧸ G₁}
    (huv : (colGraph G₁ G₂).Adj u v) : ∃ k : G, k • basePt G₁ = u ∧ k • y = v := by
  obtain ⟨hne, m, hum, hvm⟩ := colGraph_adj.mp huv
  obtain ⟨g₀, rfl⟩ := smul_basePt_surj u
  have hA : CInc G₁ G₂ (basePt G₁) (g₀⁻¹ • m) := by
    have := (cInc_smul G₁ G₂ g₀⁻¹ _ m).mpr hum
    rwa [inv_smul_smul] at this
  have hB : CInc G₁ G₂ (g₀⁻¹ • v) (g₀⁻¹ • m) := (cInc_smul G₁ G₂ g₀⁻¹ v m).mpr hvm
  obtain ⟨g, hgx, hgm⟩ := hA
  have hgx' : g • basePt G₁ = basePt G₁ := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    exact hgx
  have hgl : ((g : G) : G ⧸ G₂) = g • basePt G₂ := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  rw [← hgm, hgl] at hB
  have hC : CInc G₁ G₂ (g⁻¹ • g₀⁻¹ • v) (basePt G₂) := by
    have := (cInc_smul G₁ G₂ g⁻¹ _ _).mpr hB
    rwa [inv_smul_smul] at this
  have hne' : basePt G₁ ≠ g⁻¹ • g₀⁻¹ • v := by
    intro e
    apply hne
    have h1 : g₀⁻¹ • v = basePt G₁ := by
      calc g₀⁻¹ • v = g • (g⁻¹ • g₀⁻¹ • v) := (smul_inv_smul g _).symm
        _ = g • basePt G₁ := by rw [← e]
        _ = basePt G₁ := hgx'
    calc g₀ • basePt G₁ = g₀ • g₀⁻¹ • v := by rw [h1]
      _ = v := smul_inv_smul g₀ v
  obtain ⟨c, -, hcx, hcy⟩ := h.twoTrans (basePt G₁) y (basePt G₁) (g⁻¹ • g₀⁻¹ • v)
    (cInc_mk G₁ G₂ 1) hyl (cInc_mk G₁ G₂ 1) hC hyx.symm hne'
  refine ⟨g₀ * g * c, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hcx, hgx']
  · rw [mul_smul, mul_smul, hcy, smul_inv_smul, smul_inv_smul]

private theorem edgeSet_eq_of (h : CosetGeomLocal G₁ G₂ G₃) {y : G ⧸ G₁}
    (hyl : CInc G₁ G₂ y (basePt G₂)) (hyx : y ≠ basePt G₁) :
    (colGraph G₁ G₂).edgeSet = Set.range fun g : G => s(g • basePt G₁, g • y) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro hadj
      obtain ⟨k, hk1, hk2⟩ := exists_smul_of_adj h hyl hyx hadj
      exact ⟨k, by simp only [hk1, hk2]⟩
    · rintro ⟨k, hk⟩
      have hadj : (colGraph G₁ G₂).Adj (basePt G₁) y := CosetGeomLocal.adj hyl hyx
      rcases Sym2.eq_iff.mp hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
        exact (CFSG.Quasithin.GraphAction.adj_smul k _ _).mpr hadj
      · rw [← h1, ← h2]
        exact ((CFSG.Quasithin.GraphAction.adj_smul k _ _).mpr hadj).symm

theorem CosetGeomLocal.isUniquenessSystem (h : CosetGeomLocal G₁ G₂ G₃) {y : G ⧸ G₁}
    (hyl : CInc G₁ G₂ y (basePt G₂)) (hyx : y ≠ basePt G₁) :
    IsUniquenessSystem (colGraph G₁ G₂) G₃
      (orbitSubgraph (colGraph G₁ G₂) G₃ (basePt G₁) y (CosetGeomLocal.adj hyl hyx)
        (by obtain ⟨t, ht, h1, -⟩ := h.swap hyl hyx; exact ⟨t, ht, h1⟩))
      (basePt G₁) y :=
  isUniquenessSystem_of (colGraph G₁ G₂) G₃ (basePt G₁) y (CosetGeomLocal.adj hyl hyx)
    smul_basePt_surj (edgeSet_eq_of h hyl hyx) (h.swap hyl hyx) (sup_top_stab h)
    (stab_eq_of h hyl hyx) (I_eq_of h hyl hyx)

end CFSG.Quasithin.H13.AS91
