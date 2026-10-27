module

public import CFSG.Milestones.ASVolI.F4N.L23b
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_mem_stabPath_smul {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {n : ℕ} (q : GPath c.graph n) (g x : c.G0) :
    x ∈ ((g • q).stabPath : Subgroup c.G0) ↔ g⁻¹ * x * g ∈ (q.stabPath : Subgroup c.G0) := by
  show (∀ i, i ≤ n → x • (g • q) i = (g • q) i) ↔ (∀ i, i ≤ n → (g⁻¹ * x * g) • q i = q i)
  refine forall_congr' fun i => imp_congr_right fun _ => ?_
  rw [GPath.smul_apply, mul_smul, mul_smul, inv_smul_eq_iff]

theorem burnsideF4n_mem_zpowers_conj {G : Type*} [Group G] (g s x : G) :
    x ∈ Subgroup.zpowers (g * s * g⁻¹) ↔ g⁻¹ * x * g ∈ Subgroup.zpowers s := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [conj_zpow]; group⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [conj_zpow, hk]; group⟩

theorem burnsideF4n_orderOf_conj_mul {G : Type*} [Group G] (g a b : G) :
    orderOf (g * a * g⁻¹ * (g * b * g⁻¹)) = orderOf (a * b) := by
  rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group]
  exact (SemiconjBy.orderOf_eq g (by simp [SemiconjBy, mul_assoc])).symm

theorem burnsideF4n_N1set_tits_conj {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {cc y : c.Γ} {g s : c.G0} (hgx : g • c.xv = c.xv)
    (hgl : g • c.lv = c.lv) (hgc : g • cc = cc) (hs : s ∈ N1set c GLKind.Tits cc y) :
    g * s * g⁻¹ ∈ N1set c GLKind.Tits cc y := by
  unfold N1set at hs ⊢
  rw [if_pos rfl] at hs ⊢
  obtain ⟨hsx, hcy, q, hq0, hqg, hqs⟩ := hs
  refine ⟨?_, ?_, g • q, ?_, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
      show g⁻¹ • c.xv = c.xv by rw [inv_smul_eq_iff, hgx], MulAction.mem_stabilizer_iff.mp hsx, hgx]
  · have := (burnsideF4n_hasCycle_conj c g s c.lv cc).mpr hcy
    rwa [hgl, hgc] at this
  · rw [GPath.smul_apply, hq0, hgx]
  · show c.graph.dist ((g • q) 0) ((g • q) GLKind.Tits.m) = GLKind.Tits.m
    rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul (connected_graph c)]
    exact hqg
  · ext x
    rw [burnsideF4n_mem_stabPath_smul, hqs, burnsideF4n_mem_zpowers_conj]

theorem burnsideF4n_cyc2_conj {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {y : c.Γ} {g t : c.G0} (hgx : g • c.xv = c.xv)
    (hgl : g • c.lv = c.lv) (hgy : g • y = y)
    (ht : t ∈ stv c c.lv ∧ HasCycle c t c.xv y) :
    g * t * g⁻¹ ∈ stv c c.lv ∧ HasCycle c (g * t * g⁻¹) c.xv y := by
  refine ⟨?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
      show g⁻¹ • c.lv = c.lv by rw [inv_smul_eq_iff, hgl], MulAction.mem_stabilizer_iff.mp ht.1, hgl]
  · have := (burnsideF4n_hasCycle_conj c g t c.xv y).mpr ht.2
    rwa [hgx, hgy] at this

theorem burnsideF4n_N2set_g2d_conj {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) {cc y y' : c.Γ} {g t : c.G0} (hgx : g • c.xv = c.xv)
    (hgc : g • cc = cc) (hgy : g • y' = y') (ht : t ∈ N2set c GLKind.G2d cc y y') :
    g * t * g⁻¹ ∈ N2set c GLKind.G2d cc y y' := by
  unfold N2set at ht ⊢
  rw [if_neg (by decide)] at ht ⊢
  refine ⟨?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
      show g⁻¹ • cc = cc by rw [inv_smul_eq_iff, hgc], MulAction.mem_stabilizer_iff.mp ht.1, hgc]
  · have := (burnsideF4n_hasCycle_conj c g t c.xv y').mpr ht.2
    rwa [hgx, hgy] at this

theorem burnsideF4n_ncard_eq_mul_fiber {G : Type*} [Group G] [Finite G] (N₁ : Set G)
    (P : Set (G × G)) (K : Set G) (hP1 : ∀ st ∈ P, st.1 ∈ N₁)
    (hconj : ∀ g ∈ K, ∀ st ∈ P, (g * st.1 * g⁻¹, g * st.2 * g⁻¹) ∈ P)
    (hKinv : ∀ g ∈ K, g⁻¹ ∈ K) (htrans : ∀ s ∈ N₁, ∀ s' ∈ N₁, ∃ g ∈ K, g * s * g⁻¹ = s')
    {s₀ : G} (hs₀ : s₀ ∈ N₁) : P.ncard = N₁.ncard * {t | (s₀, t) ∈ P}.ncard := by
  classical
  have hfib : ∀ s : N₁, Nat.card {t | ((s : G), t) ∈ P} = Nat.card {t | (s₀, t) ∈ P} := by
    rintro ⟨s, hs⟩
    obtain ⟨g, hg, rfl⟩ := htrans s₀ hs₀ s hs
    refine Nat.card_congr
      { toFun := fun t => ⟨g⁻¹ * t.1 * g, ?_⟩
        invFun := fun t => ⟨g * t.1 * g⁻¹, ?_⟩
        left_inv := fun t => Subtype.ext (by simp only; group)
        right_inv := fun t => Subtype.ext (by simp only; group) }
    · have := hconj g⁻¹ (hKinv g hg) _ t.2
      simp only [inv_inv] at this
      rwa [show g⁻¹ * (g * s₀ * g⁻¹) * g = s₀ by group] at this
    · exact hconj g hg _ t.2
  let e : P ≃ Σ s : N₁, {t | ((s : G), t) ∈ P} :=
    { toFun := fun st => ⟨⟨st.1.1, hP1 _ st.2⟩, ⟨st.1.2, st.2⟩⟩
      invFun := fun st => ⟨((st.1 : G), (st.2 : G)), st.2.2⟩
      left_inv := fun st => rfl
      right_inv := fun st => rfl }
  haveI : Fintype N₁ := Fintype.ofFinite N₁
  have h1 : P.ncard = Nat.card P := (Nat.card_coe_set_eq P).symm
  have h2 : N₁.ncard = Nat.card N₁ := (Nat.card_coe_set_eq N₁).symm
  have h3 : {t | (s₀, t) ∈ P}.ncard = Nat.card {t | (s₀, t) ∈ P} := (Nat.card_coe_set_eq _).symm
  rw [h1, h2, h3, Nat.card_congr e, Nat.card_sigma, Finset.sum_congr rfl (fun s _ => hfib s),
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card (α := N₁)]

theorem burnsideF4n_Qx_fix {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p (⊤ : Subgroup E) (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) {Y : Type}
    [Group Y] (c : Cpl M₁ M₂ Y) {g : c.G0} (hg : g ∈ Qu p ⊤ c c.xv) :
    g • c.xv = c.xv ∧ ∀ w ∈ CosetGeom.nbrs c.xv, g • w = w := by
  have hQ := burnsideF4b_QNormalized p (inferInstance : (⊤ : Subgroup E).Normal) c
  have hQx : Qu p ⊤ c c.xv = Qx p ⊤ c := Qvert_baseVert hQ false
  rw [hQx] at hg
  refine ⟨?_, fun w hw => ?_⟩
  · have hle : Qx p ⊤ c ≤ stv c c.xv := by
      rw [stv_xv_eq_range]
      exact Subgroup.map_le_range _ _
    exact MulAction.mem_stabilizer_iff.mp (hle hg)
  · exact MulAction.mem_stabilizer_iff.mp
      (burnsideF4b_Qx_le_stv p inferInstance (burnsideF4b_pCoreOf_le hp hP).1 c hw hg)

theorem burnsideF4n_Ql_fix {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p (⊤ : Subgroup E) (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) {Y : Type}
    [Group Y] (c : Cpl M₁ M₂ Y) {g : c.G0} (hg : g ∈ Qu p ⊤ c c.lv) :
    g • c.lv = c.lv ∧ ∀ w ∈ CosetGeom.nbrs c.lv, g • w = w := by
  have hQ := burnsideF4b_QNormalized p (inferInstance : (⊤ : Subgroup E).Normal) c
  have hQl : Qu p ⊤ c c.lv = Ql p ⊤ c := Qvert_baseVert hQ true
  rw [hQl] at hg
  refine ⟨?_, fun w hw => ?_⟩
  · have hle : Ql p ⊤ c ≤ stv c c.lv := by
      rw [burnsideF4n_stv_lv_eq_range]
      exact Subgroup.map_le_range _ _
    exact MulAction.mem_stabilizer_iff.mp (hle hg)
  · exact MulAction.mem_stabilizer_iff.mp
      (burnsideF4b_Ql_le_stv p inferInstance (burnsideF4b_pCoreOf_le hp hP).2 c hw hg)

theorem burnsideF4n_Qc_fix {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p (⊤ : Subgroup E) (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) {Y : Type}
    [Group Y] (c : Cpl M₁ M₂ Y) (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) {g : c.G0}
    (hg : g ∈ Qu p ⊤ c (f1 (c := c) a₀ • c.lv)) :
    g • (f1 (c := c) a₀ • c.lv) = f1 (c := c) a₀ • c.lv ∧
      ∀ w ∈ CosetGeom.nbrs (f1 (c := c) a₀ • c.lv), g • w = w := by
  have hQ := burnsideF4b_QNormalized p (inferInstance : (⊤ : Subgroup E).Normal) c
  have h1 : Qu p ⊤ c (f1 (c := c) a₀ • c.lv) = conjSub (f1 (c := c) a₀) (Qu p ⊤ c c.lv) :=
    Qvert_smul hQ _ _
  rw [h1, mem_conjSub] at hg
  obtain ⟨hl, hw⟩ := burnsideF4n_Ql_fix hp hP c hg
  have key : ∀ v : c.Γ, ((f1 (c := c) a₀)⁻¹ * g * f1 (c := c) a₀) • v = v →
      g • (f1 (c := c) a₀ • v) = f1 (c := c) a₀ • v := by
    intro v hv
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at hv
    exact hv
  refine ⟨key _ hl, fun w hw' => ?_⟩
  have hw'' : (f1 (c := c) a₀)⁻¹ • w ∈ CosetGeom.nbrs c.lv := by
    have := (CosetGeom.smul_adj (f1 (c := c) a₀)⁻¹).mpr
      (show c.graph.Adj (f1 (c := c) a₀ • c.lv) w from hw')
    rwa [inv_smul_smul] at this
  have := key _ (hw _ hw'')
  rwa [smul_inv_smul] at this

theorem burnsideF4n_fiber_tits {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p (⊤ : Subgroup E) (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) {Y : Type}
    [Group Y] [Finite Y] (ρ : Cpl M₁ M₂ Y) {cc y y' : ρ.Γ} (hcc : cc ∈ CosetGeom.nbrs ρ.xv)
    (hy : y ∈ CosetGeom.nbrs ρ.lv)
    (h20 : Set.ncard (N1set ρ GLKind.Tits cc y) = 2 ^ 4 ∧
      Set.ncard (N2set ρ GLKind.Tits cc y y') = 2 ^ 6 ∧
      Set.ncard (Pset ρ GLKind.Tits cc y y') = 2 ^ 9 ∧
      ∀ s ∈ N1set ρ GLKind.Tits cc y, ∀ s' ∈ N1set ρ GLKind.Tits cc y,
        ∃ g ∈ Qu p ⊤ ρ ρ.xv ⊓ Qu p ⊤ ρ ρ.lv, g * s * g⁻¹ = s')
    {s₀ : ρ.G0} (hs₀ : s₀ ∈ N1set ρ GLKind.Tits cc y) :
    {t | (s₀, t) ∈ Pset ρ GLKind.Tits cc y y'}.ncard = 2 ^ 5 := by
  obtain ⟨h1, -, h3, htr⟩ := h20
  have key := burnsideF4n_ncard_eq_mul_fiber (N1set ρ GLKind.Tits cc y) (Pset ρ GLKind.Tits cc y y')
    ((Qu p ⊤ ρ ρ.xv ⊓ Qu p ⊤ ρ ρ.lv : Subgroup ρ.G0) : Set ρ.G0) (fun st hst => hst.1)
    (fun g hg st hst => by
      obtain ⟨hgx, hgΓx⟩ := burnsideF4n_Qx_fix hp hP ρ hg.1
      obtain ⟨hgl, hgΓl⟩ := burnsideF4n_Ql_fix hp hP ρ hg.2
      refine ⟨burnsideF4n_N1set_tits_conj ρ hgx hgl (hgΓx cc hcc) hst.1, ?_, ?_⟩
      · have h2 := hst.2.1
        unfold N2set at h2 ⊢
        rw [if_pos rfl] at h2 ⊢
        exact burnsideF4n_cyc2_conj ρ hgx hgl (hgΓl y hy) h2
      · show orderOf (g * st.1 * g⁻¹ * (g * st.2 * g⁻¹)) = _
        rw [burnsideF4n_orderOf_conj_mul]
        exact hst.2.2)
    (fun g hg => Subgroup.inv_mem _ hg) (fun s hs s' hs' => htr s hs s' hs') hs₀
  rw [h3, h1] at key
  omega

theorem burnsideF4n_fiber_g2d {E : Type} [Group E] [Finite E] {p : ℕ} (hp : p.Prime)
    {M₁ M₂ : Subgroup E}
    (hP : IsLieParabolics p (⊤ : Subgroup E) (⊤ ⊓ (M₁ ⊓ M₂)) (⊤ ⊓ M₁) (⊤ ⊓ M₂)) {Y : Type}
    [Group Y] [Finite Y] (ρ : Cpl M₁ M₂ Y) (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1)
    {y y' : ρ.Γ} (hcc : f1 (c := ρ) a₀ • ρ.lv ∈ CosetGeom.nbrs ρ.xv)
    (hy : y ∈ CosetGeom.nbrs ρ.lv) (hy' : y' ∈ CosetGeom.nbrs (f1 (c := ρ) a₀ • ρ.lv))
    (h20 : Set.ncard (N1set ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y) = 4 ∧
      Set.ncard (N2set ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y y') = 4 ∧
      Set.ncard (Pset ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y y') = 8 ∧
      ∀ s ∈ N1set ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y,
        ∀ s' ∈ N1set ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y,
        ∃ g ∈ Qu p ⊤ ρ ρ.lv ⊓ Qu p ⊤ ρ (f1 (c := ρ) a₀ • ρ.lv), g * s * g⁻¹ = s')
    {s₀ : ρ.G0} (hs₀ : s₀ ∈ N1set ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y) :
    {t | (s₀, t) ∈ Pset ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y y'}.ncard = 2 := by
  obtain ⟨h1, -, h3, htr⟩ := h20
  have hxc : ρ.xv ∈ CosetGeom.nbrs (f1 (c := ρ) a₀ • ρ.lv) :=
    (show ρ.graph.Adj ρ.xv (f1 (c := ρ) a₀ • ρ.lv) from hcc).symm
  have hxl : ρ.xv ∈ CosetGeom.nbrs ρ.lv := (CosetGeom.adj_γ₀_γ₁ : ρ.graph.Adj ρ.xv ρ.lv).symm
  have key := burnsideF4n_ncard_eq_mul_fiber
    (N1set ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y) (Pset ρ GLKind.G2d (f1 (c := ρ) a₀ • ρ.lv) y y')
    ((Qu p ⊤ ρ ρ.lv ⊓ Qu p ⊤ ρ (f1 (c := ρ) a₀ • ρ.lv) : Subgroup ρ.G0) : Set ρ.G0)
    (fun st hst => hst.1)
    (fun g hg st hst => by
      obtain ⟨hgl, hgΓl⟩ := burnsideF4n_Ql_fix hp hP ρ hg.1
      obtain ⟨hgc, hgΓc⟩ := burnsideF4n_Qc_fix hp hP ρ a₀ hg.2
      have hgx : g • ρ.xv = ρ.xv := hgΓl _ hxl
      refine ⟨?_, burnsideF4n_N2set_g2d_conj ρ hgx hgc (hgΓc y' hy') hst.2.1, ?_⟩
      · have h2 := hst.1
        unfold N1set at h2 ⊢
        rw [if_neg (by decide)] at h2 ⊢
        exact burnsideF4n_cyc2_conj ρ hgx hgl (hgΓl y hy) h2
      · show orderOf (g * st.1 * g⁻¹ * (g * st.2 * g⁻¹)) = _
        rw [burnsideF4n_orderOf_conj_mul]
        exact hst.2.2)
    (fun g hg => Subgroup.inv_mem _ hg) (fun s hs s' hs' => htr s hs s' hs') hs₀
  rw [h3, h1] at key
  omega

theorem burnsideF4n_three_disjoint {X : Type*} [Finite X] {N Q₁ Q₂ Q₃ : Set X} {k n : ℕ}
    (h1 : Q₁ ⊆ N) (h2 : Q₂ ⊆ N) (h3 : Q₃ ⊆ N) (d12 : Disjoint Q₁ Q₂) (d13 : Disjoint Q₁ Q₃)
    (d23 : Disjoint Q₂ Q₃) (k1 : k ≤ Q₁.ncard) (k2 : k ≤ Q₂.ncard) (k3 : k ≤ Q₃.ncard)
    (hN : N.ncard ≤ n) (hkn : n < 3 * k) : False := by
  have e1 := Set.ncard_union_eq d12 (Set.toFinite _) (Set.toFinite _)
  have e2 := Set.ncard_union_eq (Disjoint.union_left d13 d23) (Set.toFinite _) (Set.toFinite _)
  have hle := Set.ncard_le_ncard (Set.union_subset (Set.union_subset h1 h2) h3) (Set.toFinite N)
  omega

theorem burnsideF4n_no_three
    (h45 : F_4_5) (h46 : F_4_6)
    (h420 : F_4_20) {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hGp : Gp = ⊤) (hκ : κ = .G2d ∨ κ = .Tits)
    (Y₁ Y₂ Y₃ : Type) [Group Y₁] [Group Y₂] [Group Y₃] (ρ₁ : Cpl M₁ M₂ Y₁) (ρ₂ : Cpl M₁ M₂ Y₂)
    (ρ₃ : Cpl M₁ M₂ Y₃) (hρ₁ : ρ₁.IsFaithful) (hρ₂ : ρ₂.IsFaithful) (hρ₃ : ρ₃.IsFaithful)
    (hs₁ : ρ₁.IsSmall κ.m) (hs₂ : ρ₂.IsSmall κ.m) (hs₃ : ρ₃.IsSmall κ.m)
    (n12 : ¬ Amalgam.Completion.IsEquivalent ρ₁.toCompletion ρ₂.toCompletion)
    (n13 : ¬ Amalgam.Completion.IsEquivalent ρ₁.toCompletion ρ₃.toCompletion)
    (n23 : ¬ Amalgam.Completion.IsEquivalent ρ₂.toCompletion ρ₃.toCompletion) : False := by
  haveI : Finite E := hyp.finite
  haveI := burnsideF4b_finite_G1 M₁ M₂
  haveI := burnsideF4b_finite_G2 M₁ M₂
  have hp : p.Prime := burnsideF4a_prime_of_isGenLie hyp.model
  have hP := burnsideF4n_parabolics_at hyp
  subst hGp
  have hι := hρ₁
  have hιs := hs₁
  have Fι := burnsideF4n_facts46_at h46 hyp ρ₁ hι
  haveI : Finite Y₁ := burnsideF4b_finite_of_small Fι hιs
  obtain ⟨cc₁, hcc₁, hcc₁l, -⟩ := Fι.hval ρ₁.xv ρ₁.lv ρ₁.lv
  obtain ⟨y₁, hy₁, hy₁x, -⟩ := Fι.hval ρ₁.lv ρ₁.xv ρ₁.xv
  obtain ⟨y'₁, hy'₁, hy'₁x, -⟩ := Fι.hval cc₁ ρ₁.xv ρ₁.xv
  obtain ⟨a₀, rfl⟩ := burnsideF4n_exists_a0 _ hcc₁
  obtain ⟨b₀, rfl⟩ := burnsideF4n_exists_b0 _ hy₁
  obtain ⟨b₁, rfl⟩ := burnsideF4n_exists_b1 _ a₀ hy'₁
  obtain ⟨-, -, -, ha₀ι, hb₀ι, hb₁ι⟩ := burnsideF4n_corr_props _ hι a₀ b₀ b₁
  have h20ι := h420 κ p f E ⊤ M₁ M₂ hyp rfl hκ _ ρ₁ hι hιs _ hcc₁ hcc₁l _ hy₁ hy₁x _
    hy'₁ hy'₁x
  have hdata : ∀ (Z : Type) [Group Z] (ρ : Cpl M₁ M₂ Z), ρ.IsFaithful → ρ.IsSmall κ.m →
      Finite Z ∧ ρ.Facts46 κ.m ∧ (f1 (c := ρ) a₀ • ρ.lv ∈ CosetGeom.nbrs ρ.xv) ∧
        (f2 (c := ρ) b₀ • ρ.xv ∈ CosetGeom.nbrs ρ.lv) ∧
        (f1 (c := ρ) a₀ • f2 (c := ρ) b₁ • ρ.xv ∈ CosetGeom.nbrs (f1 (c := ρ) a₀ • ρ.lv)) ∧
        ((κ = .Tits → Set.ncard (N1set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv)) = 2 ^ 4 ∧
          Set.ncard (N2set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv)
            (f1 (c := ρ) a₀ • f2 (c := ρ) b₁ • ρ.xv)) = 2 ^ 6 ∧
          Set.ncard (Pset ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv)
            (f1 (c := ρ) a₀ • f2 (c := ρ) b₁ • ρ.xv)) = 2 ^ 9 ∧
          ∀ s ∈ N1set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv),
            ∀ s' ∈ N1set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv),
            ∃ g ∈ Qu p ⊤ ρ ρ.xv ⊓ Qu p ⊤ ρ ρ.lv, g * s * g⁻¹ = s') ∧
         (κ = .G2d → Set.ncard (N1set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv)) = 4 ∧
          Set.ncard (N2set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv)
            (f1 (c := ρ) a₀ • f2 (c := ρ) b₁ • ρ.xv)) = 4 ∧
          Set.ncard (Pset ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv)
            (f1 (c := ρ) a₀ • f2 (c := ρ) b₁ • ρ.xv)) = 8 ∧
          ∀ s ∈ N1set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv),
            ∀ s' ∈ N1set ρ κ (f1 (c := ρ) a₀ • ρ.lv) (f2 (c := ρ) b₀ • ρ.xv),
            ∃ g ∈ Qu p ⊤ ρ ρ.lv ⊓ Qu p ⊤ ρ (f1 (c := ρ) a₀ • ρ.lv), g * s * g⁻¹ = s')) := by
    intro Z _ ρ hρ hsρ
    have Fρ := burnsideF4n_facts46_at h46 hyp ρ hρ
    obtain ⟨hcρ, hyρ, hy'ρ, ha₀ρ, hb₀ρ, hb₁ρ⟩ := burnsideF4n_corr_props ρ hρ a₀ b₀ b₁
    exact ⟨burnsideF4b_finite_of_small Fρ hsρ, Fρ, hcρ, hyρ, hy'ρ,
      h420 κ p f E ⊤ M₁ M₂ hyp rfl hκ Z ρ hρ hsρ _ hcρ (ha₀ρ.mpr (ha₀ι.mp hcc₁l)) _ hyρ
        (hb₀ρ.mpr (hb₀ι.mp hy₁x)) _ hy'ρ (hb₁ρ.mpr (hb₁ι.mp hy'₁x))⟩
  rcases hκ with rfl | rfl
  ·
    obtain ⟨h1ι, h2ι, -, -⟩ := h20ι.2 rfl
    obtain ⟨s, hs⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h1ι]; norm_num :
      (N1set ρ₁ GLKind.G2d (f1 (c := ρ₁) a₀ • ρ₁.lv)
        (f2 (c := ρ₁) b₀ • ρ₁.xv)).ncard ≠ 0)
    have hsl : s ∈ stv ρ₁ ρ₁.lv := by
      have := hs
      unfold N1set at this
      rw [if_neg (by decide)] at this
      exact this.1
    obtain ⟨b₂, rfl⟩ := stv_lv_le_range_f2 _ hsl
    obtain ⟨N₂', hN₂'⟩ : ∃ N : Set (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, N = {b | f1 (c := ρ₁) a₀ *
      f2 (c := ρ₁) b * (f1 (c := ρ₁) a₀)⁻¹ ∈ N2set ρ₁ GLKind.G2d
        (f1 (c := ρ₁) a₀ • ρ₁.lv) (f2 (c := ρ₁) b₀ • ρ₁.xv)
        (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv)} := ⟨_, rfl⟩
    have hN₂card : N₂'.ncard ≤ 4 := by
      have hinj : Function.Injective (fun b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 =>
          f1 (c := ρ₁) a₀ * f2 (c := ρ₁) b * (f1 (c := ρ₁) a₀)⁻¹) :=
        fun b b' h => f2_injective _ hι (by simpa using h)
      rw [← Set.ncard_image_of_injective N₂' hinj, ← h2ι]
      refine Set.ncard_le_ncard (fun _ ⟨b, hb, e⟩ => ?_) (Set.toFinite _)
      rw [hN₂'] at hb
      exact e ▸ hb
    have hQsub : ∀ (Z : Type) [Group Z] (ρ : Cpl M₁ M₂ Z),
        {b | (xi2 M₁ M₂ b₂, xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹) ∈
          PhatFor GLKind.G2d ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ} ⊆ N₂' := by
      intro Z _ ρ b hb
      obtain ⟨h, b', -, hw, hmem⟩ := burnsideF4n_N2hat_g2d _ hb.2.1
      have e : f1 (c := ρ₁) a₀ * f2 (c := ρ₁) b * (f1 (c := ρ₁) a₀)⁻¹ =
          f1 (c := ρ₁) h * f2 (c := ρ₁) b' * (f1 (c := ρ₁) h)⁻¹ := by
        apply Subtype.ext
        have := congrArg ρ₁.theta hw
        rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv] at this
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
          Subgroup.coe_mul, Subgroup.coe_inv]
        exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) (theta_ξ1 ρ₁ a₀)
          (theta_ξ2 ρ₁ b)) (congrArg (·⁻¹) (theta_ξ1 ρ₁ a₀))).symm.trans
          (this.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (theta_ξ1 ρ₁ h)
            (theta_ξ2 ρ₁ b')) (congrArg (·⁻¹) (theta_ξ1 ρ₁ h))))
      have hmem' := hmem
      rw [← e] at hmem'
      rw [hN₂']
      exact hmem'
    have hQlow : ∀ (Z : Type) [Group Z] (ρ : Cpl M₁ M₂ Z), ρ.IsFaithful → ρ.IsSmall GLKind.G2d.m →
        2 ≤ {b | (xi2 M₁ M₂ b₂, xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹) ∈
          PhatFor GLKind.G2d ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ}.ncard := by
      intro Z _ ρ hρ hsρ
      obtain ⟨hfin, Fρ, hcρ, hyρ, hy'ρ, h20ρ⟩ := hdata Z ρ hρ hsρ
      haveI := hfin
      have hs₀ := (burnsideF4n_N1set_g2d_iff ρ₁ ρ hι hρ b₀ b₂ _
        (f1 (c := ρ) a₀ • ρ.lv)).mp hs
      have hfib := burnsideF4n_fiber_g2d hp hP ρ a₀ hcρ hyρ hy'ρ (h20ρ.2 rfl) hs₀
      rw [← hfib]
      refine le_trans (Set.ncard_le_ncard (t := (fun b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2 =>
        f1 (c := ρ) a₀ * f2 (c := ρ) b * (f1 (c := ρ) a₀)⁻¹) '' _) ?_ (Set.toFinite _))
        (Set.ncard_image_le (Set.toFinite _))
      intro t ht
      have htN := ht.2.1
      have htc : t ∈ stv ρ (f1 (c := ρ) a₀ • ρ.lv) := by
        have := htN
        unfold N2set at this
        rw [if_neg (by decide)] at this
        exact this.1
      have ht' : (f1 (c := ρ) a₀)⁻¹ * t * f1 (c := ρ) a₀ ∈ stv ρ ρ.lv := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul,
          MulAction.mem_stabilizer_iff.mp htc, inv_smul_smul]
      obtain ⟨b, hb⟩ := stv_lv_le_range_f2 ρ ht'
      have htb : t = f1 (c := ρ) a₀ * f2 (c := ρ) b * (f1 (c := ρ) a₀)⁻¹ := by
        rw [hb]; group
      subst htb
      refine ⟨b, ⟨⟨?_, f2 (c := ρ₁) b₂, hs, (theta_ξ2 _ b₂).symm⟩,
        ⟨?_, f1 (c := ρ₁) a₀ * f2 (c := ρ₁) b * (f1 (c := ρ₁) a₀)⁻¹,
          (burnsideF4n_N2set_g2d_iff ρ₁ ρ hι hρ a₀ b₁ b _ _).mpr htN, ?_⟩, ?_⟩, rfl⟩
      · rw [liftDom1, if_neg (by decide)]
        exact ⟨b₂, rfl⟩
      · rw [liftDom2, if_neg (by decide)]
        exact ⟨a₀, rfl, b, rfl⟩
      · show _ = ρ₁.theta (xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹)
        rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) (theta_ξ1 _ a₀) (theta_ξ2 _ b))
          (congrArg (·⁻¹) (theta_ξ1 _ a₀))).symm
      · have e : ρ.toCompletion.hat (xi2 M₁ M₂ b₂) * ρ.toCompletion.hat
            (xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹) =
            ((f2 (c := ρ) b₂ * (f1 (c := ρ) a₀ * f2 (c := ρ) b * (f1 (c := ρ) a₀)⁻¹) : ρ.G0) :
              Z) := by
          show ρ.theta _ * ρ.theta _ = _
          rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
            Subgroup.coe_inv]
          exact congrArg₂ (· * ·) (theta_ξ2 ρ b₂)
            (congrArg₂ (· * ·) (congrArg₂ (· * ·) (theta_ξ1 ρ a₀) (theta_ξ2 ρ b))
              (congrArg (·⁻¹) (theta_ξ1 ρ a₀)))
        show orderOf (ρ.toCompletion.hat (xi2 M₁ M₂ b₂) * ρ.toCompletion.hat
          (xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹)) = _
        rw [e, Subgroup.orderOf_coe]
        exact ht.2.2
    have hdisj : ∀ (Z Z' : Type) [Group Z] [Group Z'] (ρ : Cpl M₁ M₂ Z) (ρ' : Cpl M₁ M₂ Z'),
        ρ.IsFaithful → ρ'.IsFaithful →
        ¬ Amalgam.Completion.IsEquivalent ρ.toCompletion ρ'.toCompletion →
        Disjoint {b | (xi2 M₁ M₂ b₂, xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹) ∈
          PhatFor GLKind.G2d ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ}
          {b | (xi2 M₁ M₂ b₂, xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b * (xi1 M₁ M₂ a₀)⁻¹) ∈
          PhatFor GLKind.G2d ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ'} := by
      intro Z Z' _ _ ρ ρ' hρ hρ' hne
      refine Set.disjoint_left.mpr fun b h1 h2 => hne ?_
      exact burnsideF4n_isEquivalent_of_phat h45 h46 hyp (Or.inl rfl) ρ₁ hι hcc₁l ρ hρ
        ρ' hρ' ⟨_, h1, h2⟩
    exact burnsideF4n_three_disjoint (hQsub _ ρ₁) (hQsub _ ρ₂) (hQsub _ ρ₃)
      (hdisj _ _ ρ₁ ρ₂ hρ₁ hρ₂ n12) (hdisj _ _ ρ₁ ρ₃ hρ₁ hρ₃ n13) (hdisj _ _ ρ₂ ρ₃ hρ₂ hρ₃ n23)
      (hQlow _ ρ₁ hρ₁ hs₁) (hQlow _ ρ₂ hρ₂ hs₂) (hQlow _ ρ₃ hρ₃ hs₃) hN₂card (by norm_num)
  ·
    obtain ⟨h1ι, h2ι, -, -⟩ := h20ι.1 rfl
    obtain ⟨s, hs⟩ := Set.nonempty_of_ncard_ne_zero (by rw [h1ι]; norm_num :
      (N1set ρ₁ GLKind.Tits (f1 (c := ρ₁) a₀ • ρ₁.lv)
        (f2 (c := ρ₁) b₀ • ρ₁.xv)).ncard ≠ 0)
    have hsx : s ∈ stv ρ₁ ρ₁.xv := by
      have := hs
      unfold N1set at this
      rw [if_pos rfl] at this
      exact this.1
    obtain ⟨a₁, rfl⟩ := stv_xv_le_range_f1 _ hsx
    obtain ⟨N₂', hN₂'⟩ : ∃ N : Set (RankTwoAmalgam.ofSubgroups M₁ M₂).G2, N = {b | f2 (c := ρ₁) b ∈
      N2set ρ₁ GLKind.Tits (f1 (c := ρ₁) a₀ • ρ₁.lv)
        (f2 (c := ρ₁) b₀ • ρ₁.xv)
        (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv)} := ⟨_, rfl⟩
    have hN₂card : N₂'.ncard ≤ 2 ^ 6 := by
      rw [← Set.ncard_image_of_injective N₂' (f2_injective _ hι), ← h2ι]
      refine Set.ncard_le_ncard (fun _ ⟨b, hb, e⟩ => ?_) (Set.toFinite _)
      rw [hN₂'] at hb
      exact e ▸ hb
    have hQsub : ∀ (Z : Type) [Group Z] (ρ : Cpl M₁ M₂ Z),
        {b | (xi1 M₁ M₂ a₁, xi2 M₁ M₂ b) ∈
          PhatFor GLKind.Tits ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ} ⊆ N₂' := by
      intro Z _ ρ b hb
      obtain ⟨b', hw, hmem⟩ := burnsideF4n_N2hat_tits _ hb.2.1
      have hbb : b = b' := by
        apply hι.2.2
        have := congrArg ρ₁.theta hw
        exact (theta_ξ2 ρ₁ b).symm.trans (this.trans (theta_ξ2 ρ₁ b'))
      have hmem' := hmem
      rw [← hbb] at hmem'
      rw [hN₂']
      exact hmem'
    have hQlow : ∀ (Z : Type) [Group Z] (ρ : Cpl M₁ M₂ Z), ρ.IsFaithful → ρ.IsSmall GLKind.Tits.m →
        2 ^ 5 ≤ {b | (xi1 M₁ M₂ a₁, xi2 M₁ M₂ b) ∈
          PhatFor GLKind.Tits ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ}.ncard := by
      intro Z _ ρ hρ hsρ
      obtain ⟨hfin, Fρ, hcρ, hyρ, hy'ρ, h20ρ⟩ := hdata Z ρ hρ hsρ
      haveI := hfin
      have hs₀ := (burnsideF4n_N1set_tits_iff ρ₁ ρ hι hρ Fι Fρ a₀ a₁ _
        (f2 (c := ρ) b₀ • ρ.xv)).mp hs
      have hfib := burnsideF4n_fiber_tits hp hP ρ hcρ hyρ (h20ρ.1 rfl) hs₀
      rw [← hfib]
      refine le_trans (Set.ncard_le_ncard (t := (f2 (c := ρ)) '' _) ?_ (Set.toFinite _))
        (Set.ncard_image_le (Set.toFinite _))
      intro t ht
      have htN := ht.2.1
      have htl : t ∈ stv ρ ρ.lv := by
        have := htN
        unfold N2set at this
        rw [if_pos rfl] at this
        exact this.1
      obtain ⟨b, rfl⟩ := stv_lv_le_range_f2 ρ htl
      refine ⟨b, ⟨⟨?_, f1 (c := ρ₁) a₁, hs, (theta_ξ1 _ a₁).symm⟩,
        ⟨?_, f2 (c := ρ₁) b,
          (burnsideF4n_N2set_tits_iff ρ₁ ρ hι hρ b₀ b _ _ _ _).mpr htN,
          (theta_ξ2 _ b).symm⟩, ?_⟩, rfl⟩
      · rw [liftDom1, if_pos rfl]
        exact ⟨a₁, rfl⟩
      · rw [liftDom2, if_pos rfl]
        exact ⟨b, rfl⟩
      · have e : ρ.toCompletion.hat (xi1 M₁ M₂ a₁) * ρ.toCompletion.hat (xi2 M₁ M₂ b) =
            ((f1 (c := ρ) a₁ * f2 (c := ρ) b : ρ.G0) : Z) := by
          show ρ.theta _ * ρ.theta _ = _
          rw [Subgroup.coe_mul]
          exact congrArg₂ (· * ·) (theta_ξ1 ρ a₁) (theta_ξ2 ρ b)
        show orderOf (ρ.toCompletion.hat (xi1 M₁ M₂ a₁) * ρ.toCompletion.hat (xi2 M₁ M₂ b)) = _
        rw [e, Subgroup.orderOf_coe]
        exact ht.2.2
    have hdisj : ∀ (Z Z' : Type) [Group Z] [Group Z'] (ρ : Cpl M₁ M₂ Z) (ρ' : Cpl M₁ M₂ Z'),
        ρ.IsFaithful → ρ'.IsFaithful →
        ¬ Amalgam.Completion.IsEquivalent ρ.toCompletion ρ'.toCompletion →
        Disjoint {b | (xi1 M₁ M₂ a₁, xi2 M₁ M₂ b) ∈
          PhatFor GLKind.Tits ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ}
          {b | (xi1 M₁ M₂ a₁, xi2 M₁ M₂ b) ∈
          PhatFor GLKind.Tits ρ₁ (f1 (c := ρ₁) a₀ • ρ₁.lv)
            (f2 (c := ρ₁) b₀ • ρ₁.xv)
            (f1 (c := ρ₁) a₀ • f2 (c := ρ₁) b₁ • ρ₁.xv) ρ'} := by
      intro Z Z' _ _ ρ ρ' hρ hρ' hne
      refine Set.disjoint_left.mpr fun b h1 h2 => hne ?_
      exact burnsideF4n_isEquivalent_of_phat h45 h46 hyp (Or.inr rfl) ρ₁ hι hcc₁l ρ hρ
        ρ' hρ' ⟨_, h1, h2⟩
    exact burnsideF4n_three_disjoint (hQsub _ ρ₁) (hQsub _ ρ₂) (hQsub _ ρ₃)
      (hdisj _ _ ρ₁ ρ₂ hρ₁ hρ₂ n12) (hdisj _ _ ρ₁ ρ₃ hρ₁ hρ₃ n13) (hdisj _ _ ρ₂ ρ₃ hρ₂ hρ₃ n23)
      (hQlow _ ρ₁ hρ₁ hs₁) (hQlow _ ρ₂ hρ₂ hs₂) (hQlow _ ρ₃ hρ₃ hs₃) hN₂card (by norm_num)

theorem burnsideF4n_F423_four
    (h45 : F_4_5) (h46 : F_4_6)
    (h420 : F_4_20) {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hGp : Gp = ⊤) (hκ : κ = .G2d ∨ κ = .Tits) :
    ∃ (Y₁ Y₂ : Type) (_ : Group Y₁) (_ : Group Y₂) (β₁ : Cpl M₁ M₂ Y₁) (β₂ : Cpl M₁ M₂ Y₂),
      β₁.IsFaithful ∧ β₂.IsFaithful ∧ β₁.IsSmall κ.m ∧ β₂.IsSmall κ.m ∧
      ∀ (Y : Type) [Group Y] (β : Cpl M₁ M₂ Y), β.IsFaithful → β.IsSmall κ.m →
        Amalgam.Completion.IsEquivalent β.toCompletion β₁.toCompletion ∨
          Amalgam.Completion.IsEquivalent β.toCompletion β₂.toCompletion := by
  have hι := incl_faithful M₁ M₂
  have hF := burnsideF4n_facts46All h46
  have hιs : (incl M₁ M₂).IsSmall κ.m := burnsideF4b_IotaSmall_of hF h45 κ p f E Gp M₁ M₂ hyp
  by_cases hex : ∃ (Y₂ : Type) (_ : Group Y₂) (ρ₂ : Cpl M₁ M₂ Y₂), ρ₂.IsFaithful ∧
      ρ₂.IsSmall κ.m ∧
      ¬ Amalgam.Completion.IsEquivalent (incl M₁ M₂).toCompletion ρ₂.toCompletion
  · obtain ⟨Y₂, _, ρ₂, hρ₂, hs₂, hne⟩ := hex
    refine ⟨_, Y₂, inferInstance, inferInstance, incl M₁ M₂, ρ₂, hι, hρ₂, hιs, hs₂,
      fun Y _ β hβ hs => ?_⟩
    by_contra hc
    exact burnsideF4n_no_three h45 h46 h420 hyp hGp hκ _ _ _ (incl M₁ M₂) ρ₂ β hι hρ₂ hβ hιs hs₂ hs
      hne (fun e => hc (Or.inl e.symm)) (fun e => hc (Or.inr e.symm))
  · refine ⟨_, _, inferInstance, inferInstance, incl M₁ M₂, incl M₁ M₂, hι, hι, hιs, hιs,
      fun Y _ β hβ hs => Or.inl ?_⟩
    by_contra hc
    exact hex ⟨Y, inferInstance, β, hβ, hs, fun e => hc e.symm⟩

end CFSG.ASVolI
