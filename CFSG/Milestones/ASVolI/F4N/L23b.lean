module

public import CFSG.Milestones.ASVolI.F4N.L23
import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_hasCycle1_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) (a₀ a : α.G1) :
    HasCycle c (f1 (c := c) a) c.lv (f1 (c := c) a₀ • c.lv) ↔
      (a * a = 1 ∧ a₀ ∉ α.α1.range ∧ a₀⁻¹ * a ∈ α.α1.range ∧ a * a₀ ∈ α.α1.range) := by
  have k : ∀ b, f1 (c := c) b • c.lv = c.lv ↔ b ∈ α.α1.range := burnsideF4n_f1_smul_lv_iff c hc
  unfold HasCycle
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [← map_mul, ← map_one (f1 (c := c))]
    exact (f1_injective c hc).eq_iff
  · rw [ne_comm, Ne, k]
  · rw [← k (a₀⁻¹ * a), map_mul, map_inv, mul_smul, inv_smul_eq_iff]
  · rw [← k (a * a₀), map_mul, mul_smul]

theorem burnsideF4n_hasCycle2_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) (b₀ b : α.G2) :
    HasCycle c (f2 (c := c) b) c.xv (f2 (c := c) b₀ • c.xv) ↔
      (b * b = 1 ∧ b₀ ∉ α.α2.range ∧ b₀⁻¹ * b ∈ α.α2.range ∧ b * b₀ ∈ α.α2.range) := by
  have k : ∀ b, f2 (c := c) b • c.xv = c.xv ↔ b ∈ α.α2.range := burnsideF4n_f2_smul_xv_iff c hc
  unfold HasCycle
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · rw [← map_mul, ← map_one (f2 (c := c))]
    exact (f2_injective c hc).eq_iff
  · rw [ne_comm, Ne, k]
  · rw [← k (b₀⁻¹ * b), map_mul, map_inv, mul_smul, inv_smul_eq_iff]
  · rw [← k (b * b₀), map_mul, mul_smul]

theorem burnsideF4n_hasCycle_conj {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (g k : c.G0) (u v : c.Γ) :
    HasCycle c (g * k * g⁻¹) (g • u) (g • v) ↔ HasCycle c k u v := by
  unfold HasCycle
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro h
      have h2 := congrArg (fun z => g⁻¹ * z * g) h
      rw [show g⁻¹ * (g * k * g⁻¹ * (g * k * g⁻¹)) * g = k * k by group,
        show g⁻¹ * 1 * g = 1 by group] at h2
      exact h2
    · intro h
      rw [show g * k * g⁻¹ * (g * k * g⁻¹) = g * (k * k) * g⁻¹ by group, h]
      group
  · exact not_congr (smul_left_cancel_iff g)
  · rw [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff]
  · rw [mul_smul, mul_smul, inv_smul_smul, smul_left_cancel_iff]

theorem burnsideF4n_geodStab_transfer {α : RankTwoAmalgam.{0}} {Y Y' : Type} [Group Y] [Group Y']
    (c : α.Completion Y) (d : α.Completion Y') (hc : c.IsFaithful) (hd : d.IsFaithful) {m : ℕ}
    (Fd : d.Facts46 m) (a : α.G1)
    (h : ∃ q : GPath c.graph m, q 0 = c.xv ∧ q.IsGeodesic ∧
      (q.stabPath : Subgroup c.G0) = Subgroup.zpowers (f1 (c := c) a)) :
    ∃ q : GPath d.graph m, q 0 = d.xv ∧ q.IsGeodesic ∧
      (q.stabPath : Subgroup d.G0) = Subgroup.zpowers (f1 (c := d) a) := by
  obtain ⟨r, h1, h2, h3⟩ := lemma_F46_3_x c d hc hd
  obtain ⟨q, hq0, hqg, hqs⟩ := h
  let pp : PathSet c.graph c.xv := ⟨m, q, hq0⟩
  have hnb : pp.NoBack := GPath.noBack_of_dist_eq (connected_graph c) q hqg
  rcases hpp : r.set pp with ⟨n', q', hq'0⟩
  have hlen : n' = m := by
    have := h2 pp
    rw [hpp] at this
    exact this
  subst hlen
  have hnb' : q'.NoBack := by
    have := (h3 pp).mpr hnb
    rw [hpp] at this
    exact this
  have hmemc : f1 (c := c) a ∈ stv c c.xv := MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a)
  have hmemd : f1 (c := d) a ∈ stv d d.xv := MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a)
  have hra : r.grp ⟨f1 (c := c) a, hmemc⟩ = ⟨f1 (c := d) a, hmemd⟩ := h1 a _ _ rfl rfl
  have fixc : ∀ g : stv c c.xv, g • pp = pp ↔ (g : c.G0) ∈ (q.stabPath : Subgroup c.G0) := by
    intro g
    constructor
    · intro hg i _
      have := congrArg (fun z : PathSet c.graph c.xv => z.2.1 i) hg
      exact this
    · intro hg
      refine PathSet.ext rfl fun i => ?_
      show (g : c.G0) • q i = q i
      by_cases hi : i ≤ n'
      · exact hg i hi
      · rw [q.tail i (by omega)]
        exact hg n' le_rfl
  have fixd : ∀ g : stv d d.xv, g • (⟨n', q', hq'0⟩ : PathSet d.graph d.xv) = ⟨n', q', hq'0⟩ ↔
      (g : d.G0) ∈ (q'.stabPath : Subgroup d.G0) := by
    intro g
    constructor
    · intro hg i _
      have := congrArg (fun z : PathSet d.graph d.xv => z.2.1 i) hg
      exact this
    · intro hg
      refine PathSet.ext rfl fun i => ?_
      show (g : d.G0) • q' i = q' i
      by_cases hi : i ≤ n'
      · exact hg i hi
      · rw [q'.tail i (by omega)]
        exact hg n' le_rfl
  refine ⟨q', hq'0, ?_, ?_⟩
  · show d.graph.dist (q' 0) (q' n') = n'
    rw [hq'0]
    exact Fd.dist_m d.xv q' ⟨hq'0, hnb'⟩
  · ext g'
    constructor
    · intro hg'
      have hgx : g' ∈ stv d d.xv := by
        have := hg' 0 (Nat.zero_le _)
        rw [hq'0] at this
        exact MulAction.mem_stabilizer_iff.mpr this
      set G' : stv d d.xv := ⟨g', hgx⟩
      set G := r.grp.symm G'
      have hG : r.grp G = G' := r.grp.apply_symm_apply G'
      have hfix : G • pp = pp := by
        apply r.set.injective
        rw [r.map_smul, hG, hpp]
        exact (fixd G').mpr hg'
      have hGm := (fixc G).mp hfix
      rw [hqs] at hGm
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hGm
      have hGk : G = (⟨f1 (c := c) a, hmemc⟩ : stv c c.xv) ^ k := Subtype.ext (by
        rw [← hk]
        rfl)
      have : G' = (⟨f1 (c := d) a, hmemd⟩ : stv d d.xv) ^ k := by
        rw [← hG, hGk, map_zpow, hra]
      have hg'eq : g' = f1 (c := d) a ^ k := by
        have := congrArg Subtype.val this
        simpa using this
      rw [hg'eq]
      exact Subgroup.zpow_mem_zpowers _ k
    · intro hg'
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg'
      set G : stv c c.xv := (⟨f1 (c := c) a, hmemc⟩ : stv c c.xv) ^ k
      have hGm : (G : c.G0) ∈ (q.stabPath : Subgroup c.G0) := by
        rw [hqs]
        have : (G : c.G0) = f1 (c := c) a ^ k := by simp [G]
        rw [this]
        exact Subgroup.zpow_mem_zpowers _ k
      have hfix := (fixc G).mpr hGm
      have hG : r.grp G = (⟨f1 (c := d) a, hmemd⟩ : stv d d.xv) ^ k := by
        rw [map_zpow, hra]
      have h4 : r.grp G • (⟨n', q', hq'0⟩ : PathSet d.graph d.xv) = ⟨n', q', hq'0⟩ := by
        rw [← hpp, ← r.map_smul, hfix]
      have h5 := (fixd (r.grp G)).mp h4
      have h6 : ((r.grp G : stv d d.xv) : d.G0) = g' := by
        rw [hG, ← hk]
        simp
      rwa [h6] at h5

theorem burnsideF4n_N1set_tits_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y Y' : Type}
    [Group Y] [Group Y'] (c : Cpl M₁ M₂ Y) (d : Cpl M₁ M₂ Y') (hc : c.IsFaithful)
    (hd : d.IsFaithful) (Fc : c.Facts46 GLKind.Tits.m) (Fd : d.Facts46 GLKind.Tits.m)
    (a₀ a : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) (yc : c.Γ) (yd : d.Γ) :
    f1 (c := c) a ∈ N1set c GLKind.Tits (f1 (c := c) a₀ • c.lv) yc ↔
      f1 (c := d) a ∈ N1set d GLKind.Tits (f1 (c := d) a₀ • d.lv) yd := by
  unfold N1set
  rw [if_pos rfl, if_pos rfl]
  show (_ ∧ HasCycle c _ _ _ ∧ _) ↔ (_ ∧ HasCycle d _ _ _ ∧ _)
  rw [burnsideF4n_hasCycle1_iff c hc, burnsideF4n_hasCycle1_iff d hd]
  constructor
  · rintro ⟨-, hcy, hq⟩
    exact ⟨MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a), hcy,
      burnsideF4n_geodStab_transfer c d hc hd Fd a hq⟩
  · rintro ⟨-, hcy, hq⟩
    exact ⟨MulAction.mem_stabilizer_iff.mpr (f1_smul_xv a), hcy,
      burnsideF4n_geodStab_transfer d c hd hc Fc a hq⟩

theorem burnsideF4n_cyc2_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y Y' : Type}
    [Group Y] [Group Y'] (c : Cpl M₁ M₂ Y) (d : Cpl M₁ M₂ Y') (hc : c.IsFaithful)
    (hd : d.IsFaithful) (b₀ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) :
    (f2 (c := c) b ∈ stv c c.lv ∧ HasCycle c (f2 (c := c) b) c.xv (f2 (c := c) b₀ • c.xv)) ↔
      (f2 (c := d) b ∈ stv d d.lv ∧ HasCycle d (f2 (c := d) b) d.xv (f2 (c := d) b₀ • d.xv)) := by
  rw [burnsideF4n_hasCycle2_iff c hc, burnsideF4n_hasCycle2_iff d hd]
  exact ⟨fun h => ⟨MulAction.mem_stabilizer_iff.mpr (f2_smul_lv b), h.2⟩,
    fun h => ⟨MulAction.mem_stabilizer_iff.mpr (f2_smul_lv b), h.2⟩⟩

theorem burnsideF4n_N2set_tits_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y Y' : Type}
    [Group Y] [Group Y'] (c : Cpl M₁ M₂ Y) (d : Cpl M₁ M₂ Y') (hc : c.IsFaithful)
    (hd : d.IsFaithful) (b₀ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) (ccc y'c : c.Γ)
    (ccd y'd : d.Γ) :
    f2 (c := c) b ∈ N2set c GLKind.Tits ccc (f2 (c := c) b₀ • c.xv) y'c ↔
      f2 (c := d) b ∈ N2set d GLKind.Tits ccd (f2 (c := d) b₀ • d.xv) y'd := by
  unfold N2set
  rw [if_pos rfl, if_pos rfl]
  exact burnsideF4n_cyc2_iff c d hc hd b₀ b

theorem burnsideF4n_N1set_g2d_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y Y' : Type}
    [Group Y] [Group Y'] (c : Cpl M₁ M₂ Y) (d : Cpl M₁ M₂ Y') (hc : c.IsFaithful)
    (hd : d.IsFaithful) (b₀ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) (ccc : c.Γ) (ccd : d.Γ) :
    f2 (c := c) b ∈ N1set c GLKind.G2d ccc (f2 (c := c) b₀ • c.xv) ↔
      f2 (c := d) b ∈ N1set d GLKind.G2d ccd (f2 (c := d) b₀ • d.xv) := by
  unfold N1set
  rw [if_neg (by decide), if_neg (by decide)]
  exact burnsideF4n_cyc2_iff c d hc hd b₀ b

theorem burnsideF4n_N2set_g2d_mem_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y : Type}
    [Group Y] (c : Cpl M₁ M₂ Y) (hc : c.IsFaithful)
    (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1) (b₁ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2)
    (yc : c.Γ) :
    f1 (c := c) a₀ * f2 (c := c) b * (f1 (c := c) a₀)⁻¹ ∈
        N2set c GLKind.G2d (f1 (c := c) a₀ • c.lv) yc (f1 (c := c) a₀ • f2 (c := c) b₁ • c.xv) ↔
      (b * b = 1 ∧ b₁ ∉ (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range ∧
        b₁⁻¹ * b ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range ∧
        b * b₁ ∈ (RankTwoAmalgam.ofSubgroups M₁ M₂).α2.range) := by
  unfold N2set
  rw [if_neg (by decide)]
  show (_ ∈ stv c _ ∧ HasCycle c _ _ _) ↔ _
  have hx : f1 (c := c) a₀ • c.xv = c.xv := f1_smul_xv a₀
  have hconj := burnsideF4n_hasCycle_conj c (f1 (c := c) a₀) (f2 (c := c) b) c.xv
    (f2 (c := c) b₁ • c.xv)
  rw [hx] at hconj
  rw [hconj, burnsideF4n_hasCycle2_iff c hc]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, f2_smul_lv]

theorem burnsideF4n_N2set_g2d_iff {E : Type} [Group E] {M₁ M₂ : Subgroup E} {Y Y' : Type}
    [Group Y] [Group Y'] (c : Cpl M₁ M₂ Y) (d : Cpl M₁ M₂ Y') (hc : c.IsFaithful)
    (hd : d.IsFaithful) (a₀ : (RankTwoAmalgam.ofSubgroups M₁ M₂).G1)
    (b₁ b : (RankTwoAmalgam.ofSubgroups M₁ M₂).G2) (yc : c.Γ) (yd : d.Γ) :
    f1 (c := c) a₀ * f2 (c := c) b * (f1 (c := c) a₀)⁻¹ ∈
        N2set c GLKind.G2d (f1 (c := c) a₀ • c.lv) yc (f1 (c := c) a₀ • f2 (c := c) b₁ • c.xv) ↔
      f1 (c := d) a₀ * f2 (c := d) b * (f1 (c := d) a₀)⁻¹ ∈
        N2set d GLKind.G2d (f1 (c := d) a₀ • d.lv) yd (f1 (c := d) a₀ • f2 (c := d) b₁ • d.xv) := by
  rw [burnsideF4n_N2set_g2d_mem_iff c hc, burnsideF4n_N2set_g2d_mem_iff d hd]

theorem burnsideF4n_exists_a0 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    {cc : c.Γ} (hcc : cc ∈ CosetGeom.nbrs c.xv) : ∃ a₀ : α.G1, f1 (c := c) a₀ • c.lv = cc := by
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq
    (CosetGeom.adj_γ₀_γ₁ : c.graph.Adj c.xv c.lv) (hcc : c.graph.Adj c.xv cc)
  obtain ⟨a₀, rfl⟩ := stv_xv_le_range_f1 c (MulAction.mem_stabilizer_iff.mpr hg1)
  exact ⟨a₀, hg2⟩

theorem burnsideF4n_exists_b0 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    {y : c.Γ} (hy : y ∈ CosetGeom.nbrs c.lv) : ∃ b₀ : α.G2, f2 (c := c) b₀ • c.xv = y := by
  obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq
    (CosetGeom.adj_γ₀_γ₁.symm : c.graph.Adj c.lv c.xv) (hy : c.graph.Adj c.lv y)
  obtain ⟨b₀, rfl⟩ := stv_lv_le_range_f2 c (MulAction.mem_stabilizer_iff.mpr hg1)
  exact ⟨b₀, hg2⟩

theorem burnsideF4n_exists_b1 {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] (c : α.Completion Y)
    (a₀ : α.G1) {y' : c.Γ} (hy' : y' ∈ CosetGeom.nbrs (f1 (c := c) a₀ • c.lv)) :
    ∃ b₁ : α.G2, f1 (c := c) a₀ • f2 (c := c) b₁ • c.xv = y' := by
  have h1 : (f1 (c := c) a₀)⁻¹ • y' ∈ CosetGeom.nbrs c.lv := by
    have := (CosetGeom.smul_adj (f1 (c := c) a₀)⁻¹).mpr (hy' : c.graph.Adj _ y')
    rwa [inv_smul_smul] at this
  obtain ⟨b₁, hb₁⟩ := burnsideF4n_exists_b0 c h1
  exact ⟨b₁, by rw [hb₁, smul_inv_smul]⟩

theorem burnsideF4n_corr_props {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (hc : c.IsFaithful) (a₀ : α.G1) (b₀ b₁ : α.G2) :
    f1 (c := c) a₀ • c.lv ∈ CosetGeom.nbrs c.xv ∧ f2 (c := c) b₀ • c.xv ∈ CosetGeom.nbrs c.lv ∧
      f1 (c := c) a₀ • f2 (c := c) b₁ • c.xv ∈ CosetGeom.nbrs (f1 (c := c) a₀ • c.lv) ∧
      (f1 (c := c) a₀ • c.lv ≠ c.lv ↔ a₀ ∉ α.α1.range) ∧
      (f2 (c := c) b₀ • c.xv ≠ c.xv ↔ b₀ ∉ α.α2.range) ∧
      (f1 (c := c) a₀ • f2 (c := c) b₁ • c.xv ≠ c.xv ↔ b₁ ∉ α.α2.range) := by
  have hl : ∀ b : α.G2, c.graph.Adj c.lv (f2 (c := c) b • c.xv) := fun b => by
    have := (CosetGeom.smul_adj (f2 (c := c) b)).mpr
      (CosetGeom.adj_γ₀_γ₁.symm : c.graph.Adj c.lv c.xv)
    rwa [f2_smul_lv] at this
  refine ⟨?_, hl b₀, ?_, not_congr (burnsideF4n_f1_smul_lv_iff c hc a₀),
    not_congr (burnsideF4n_f2_smul_xv_iff c hc b₀), ?_⟩
  · have := (CosetGeom.smul_adj (f1 (c := c) a₀)).mpr
      (CosetGeom.adj_γ₀_γ₁ : c.graph.Adj c.xv c.lv)
    rwa [f1_smul_xv] at this
  · exact (CosetGeom.smul_adj (f1 (c := c) a₀)).mpr (hl b₁)
  · refine not_congr ?_
    rw [← burnsideF4n_f2_smul_xv_iff c hc b₁]
    constructor
    · intro h
      have := congrArg (fun v => (f1 (c := c) a₀)⁻¹ • v) h
      simp only [inv_smul_smul] at this
      rwa [show (f1 (c := c) a₀)⁻¹ • c.xv = c.xv by rw [inv_smul_eq_iff, f1_smul_xv]] at this
    · intro h
      rw [h, f1_smul_xv]

theorem burnsideF4n_phat_of_small
    (h46 : F_4_6) (h420 : F_4_20)
    {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hGp : Gp = ⊤) (hκ : κ = .G2d ∨ κ = .Tits) {Y : Type}
    [Group Y] (β : Cpl M₁ M₂ Y) (hβ : β.IsFaithful) {cc : β.Γ} (hcc : cc ∈ CosetGeom.nbrs β.xv)
    (hccl : cc ≠ β.lv) {y : β.Γ} (hy : y ∈ CosetGeom.nbrs β.lv) (hyx : y ≠ β.xv) {y' : β.Γ}
    (hy' : y' ∈ CosetGeom.nbrs cc) (hy'x : y' ≠ β.xv) {Y' : Type} [Group Y'] (ρ : Cpl M₁ M₂ Y')
    (hρ : ρ.IsFaithful) (hs : ρ.IsSmall κ.m) : (PhatFor κ β cc y y' ρ).Nonempty := by
  obtain ⟨a₀, rfl⟩ := burnsideF4n_exists_a0 β hcc
  obtain ⟨b₀, rfl⟩ := burnsideF4n_exists_b0 β hy
  obtain ⟨b₁, rfl⟩ := burnsideF4n_exists_b1 β a₀ hy'
  obtain ⟨-, -, -, ha₀β, hb₀β, hb₁β⟩ := burnsideF4n_corr_props β hβ a₀ b₀ b₁
  obtain ⟨hcρ, hyρ, hy'ρ, ha₀ρ, hb₀ρ, hb₁ρ⟩ := burnsideF4n_corr_props ρ hρ a₀ b₀ b₁
  have Fβ := burnsideF4n_facts46_at h46 hyp β hβ
  have Fρ := burnsideF4n_facts46_at h46 hyp ρ hρ
  have h20 := h420 κ p f E Gp M₁ M₂ hyp hGp hκ Y' ρ hρ hs _ hcρ (ha₀ρ.mpr (ha₀β.mp hccl)) _ hyρ
    (hb₀ρ.mpr (hb₀β.mp hyx)) _ hy'ρ (hb₁ρ.mpr (hb₁β.mp hy'x))
  rcases hκ with rfl | rfl
  ·
    obtain ⟨-, -, hP, -⟩ := h20.2 rfl
    obtain ⟨⟨s, t⟩, hsN, htN, hord⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hP]; norm_num)
    have hsl : s ∈ stv ρ ρ.lv := by
      have := hsN
      unfold N1set at this
      rw [if_neg (by decide)] at this
      exact this.1
    obtain ⟨b, rfl⟩ := stv_lv_le_range_f2 ρ hsl
    have htc : t ∈ stv ρ (f1 (c := ρ) a₀ • ρ.lv) := by
      have := htN
      unfold N2set at this
      rw [if_neg (by decide)] at this
      exact this.1
    have ht' : (f1 (c := ρ) a₀)⁻¹ * t * f1 (c := ρ) a₀ ∈ stv ρ ρ.lv := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, MulAction.mem_stabilizer_iff.mp htc,
        inv_smul_smul]
    obtain ⟨b', hb'⟩ := stv_lv_le_range_f2 ρ ht'
    have htb : t = f1 (c := ρ) a₀ * f2 (c := ρ) b' * (f1 (c := ρ) a₀)⁻¹ := by
      rw [hb']; group
    subst htb
    have hsβ := (burnsideF4n_N1set_g2d_iff β ρ hβ hρ b₀ b (f1 (c := β) a₀ • β.lv)
      (f1 (c := ρ) a₀ • ρ.lv)).mpr hsN
    have htβ := (burnsideF4n_N2set_g2d_iff β ρ hβ hρ a₀ b₁ b' (f2 (c := β) b₀ • β.xv)
      (f2 (c := ρ) b₀ • ρ.xv)).mpr htN
    refine ⟨(xi2 M₁ M₂ b, xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b' * (xi1 M₁ M₂ a₀)⁻¹), ?_, ?_, ?_⟩
    · refine ⟨?_, f2 (c := β) b, hsβ, (theta_ξ2 β b).symm⟩
      rw [liftDom1, if_neg (by decide)]
      exact ⟨b, rfl⟩
    · refine ⟨?_, f1 (c := β) a₀ * f2 (c := β) b' * (f1 (c := β) a₀)⁻¹, htβ, ?_⟩
      · rw [liftDom2, if_neg (by decide)]
        exact ⟨a₀, rfl, b', rfl⟩
      · show _ = β.theta (xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b' * (xi1 M₁ M₂ a₀)⁻¹)
        rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        exact (congrArg₂ (· * ·) (congrArg₂ (· * ·) (theta_ξ1 β a₀) (theta_ξ2 β b'))
          (congrArg (·⁻¹) (theta_ξ1 β a₀))).symm
    · have e : ρ.toCompletion.hat (xi2 M₁ M₂ b) * ρ.toCompletion.hat
          (xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b' * (xi1 M₁ M₂ a₀)⁻¹) =
          ((f2 (c := ρ) b * (f1 (c := ρ) a₀ * f2 (c := ρ) b' * (f1 (c := ρ) a₀)⁻¹) : ρ.G0) : Y') := by
        show ρ.theta _ * ρ.theta _ = _
        rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv]
        exact congrArg₂ (· * ·) (theta_ξ2 ρ b)
          (congrArg₂ (· * ·) (congrArg₂ (· * ·) (theta_ξ1 ρ a₀) (theta_ξ2 ρ b'))
            (congrArg (·⁻¹) (theta_ξ1 ρ a₀)))
      show orderOf (ρ.toCompletion.hat (xi2 M₁ M₂ b) * ρ.toCompletion.hat
          (xi1 M₁ M₂ a₀ * xi2 M₁ M₂ b' * (xi1 M₁ M₂ a₀)⁻¹)) = _
      rw [e, Subgroup.orderOf_coe]
      exact hord
  ·
    obtain ⟨-, -, hP, -⟩ := h20.1 rfl
    obtain ⟨⟨s, t⟩, hsN, htN, hord⟩ := Set.nonempty_of_ncard_ne_zero (by rw [hP]; norm_num)
    have hsx : s ∈ stv ρ ρ.xv := by
      have := hsN
      unfold N1set at this
      rw [if_pos rfl] at this
      exact this.1
    obtain ⟨a, rfl⟩ := stv_xv_le_range_f1 ρ hsx
    have htl : t ∈ stv ρ ρ.lv := by
      have := htN
      unfold N2set at this
      rw [if_pos rfl] at this
      exact this.1
    obtain ⟨b, rfl⟩ := stv_lv_le_range_f2 ρ htl
    have hsβ := (burnsideF4n_N1set_tits_iff β ρ hβ hρ Fβ Fρ a₀ a (f2 (c := β) b₀ • β.xv)
      (f2 (c := ρ) b₀ • ρ.xv)).mpr hsN
    have htβ := (burnsideF4n_N2set_tits_iff β ρ hβ hρ b₀ b (f1 (c := β) a₀ • β.lv)
      (f1 (c := β) a₀ • f2 (c := β) b₁ • β.xv) (f1 (c := ρ) a₀ • ρ.lv)
      (f1 (c := ρ) a₀ • f2 (c := ρ) b₁ • ρ.xv)).mpr htN
    refine ⟨(xi1 M₁ M₂ a, xi2 M₁ M₂ b), ?_, ?_, ?_⟩
    · refine ⟨?_, f1 (c := β) a, hsβ, (theta_ξ1 β a).symm⟩
      rw [liftDom1, if_pos rfl]
      exact ⟨a, rfl⟩
    · refine ⟨?_, f2 (c := β) b, htβ, (theta_ξ2 β b).symm⟩
      rw [liftDom2, if_pos rfl]
      exact ⟨b, rfl⟩
    · have e : ρ.toCompletion.hat (xi1 M₁ M₂ a) * ρ.toCompletion.hat (xi2 M₁ M₂ b) =
          ((f1 (c := ρ) a * f2 (c := ρ) b : ρ.G0) : Y') := by
        show ρ.theta _ * ρ.theta _ = _
        rw [Subgroup.coe_mul]
        exact congrArg₂ (· * ·) (theta_ξ1 ρ a) (theta_ξ2 ρ b)
      show orderOf (ρ.toCompletion.hat (xi1 M₁ M₂ a) * ρ.toCompletion.hat (xi2 M₁ M₂ b)) = _
      rw [e, Subgroup.orderOf_coe]
      exact hord

end CFSG.ASVolI
