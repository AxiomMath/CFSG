module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec111Order
public import CFSG.RankThree.GF2n.Stroth80.Sec114Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec34Trans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.OrthogonalInvolutions (commSpace)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

private theorem Ctx.pi_B_le_commSpace [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {a : G} (ha : a ∈ LB M Q B) (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z) :
    ∀ u ∈ B, M₀.π u ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩) := by
  intro u hu
  have haH : a ∈ H0 M Z := hc.LB_le_H0 ha
  have haM : a ∈ M := haH.1
  have hQn : ∀ x ∈ Q, a * x * a⁻¹ ∈ Q := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haM) x).mp hx
  have hQn' : ∀ x ∈ Q, a⁻¹ * x * a ∈ Q := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem haM)) x).mp hx
    simpa using this
  have hTπ : ∀ x ∈ Q, M₀.π (a * x * a⁻¹) = φ ⟨a, haH⟩ (M₀.π x) := fun x hx =>
    hφπ ⟨a, haH⟩ x hx
  have hcomQ : ⁅Q, Subgroup.zpowers a⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hyM : a ^ k ∈ M := M.zpow_mem haM k
    have e : ⁅x, a ^ k⁆ = x * ((a ^ k) * x⁻¹ * (a ^ k)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hyM) x⁻¹).mp
      (Q.inv_mem hx))
  have h2 := stroth_sup_le_lift h hcomQ (hline hu)
  exact (Tim79.QuadModel.mem_img_commutator_zpowers (φ ⟨a, haH⟩) hQn hQn' hTπ).mp h2.2

private theorem Ctx.comm_mem_Z_of_fix_commSpace [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {a : G} (ha : a ∈ LB M Q B) (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z)
    {g : ↥(H0 M Z)}
    (hgfix : ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), φ g w = w) :
    ∀ u ∈ B, ⁅(g : G), u⁆ ∈ Z := by
  intro u hu
  have huQ : u ∈ Q := hc.le hu
  have hgu : (g : G) * u * (g : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 g.2.1) u).mp huQ
  refine (M₀.comm_mem_iff huQ hgu).mpr ?_
  rw [hφπ g u huQ]
  exact hgfix _ (hc.pi_B_le_commSpace h hφπ ha hline u hu)

private theorem Ctx.mem_normalizer_sup_Z_of_comm {g : ↥(H0 M Z)}
    (hB' : ∀ u ∈ B, ⁅(g : G), u⁆ ∈ Z) :
    (g : G) ∈ Subgroup.normalizer ((B ⊔ Z : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : (B ⊔ Z : Subgroup G) ≤
      (B ⊔ Z : Subgroup G).comap (MulAut.conj (g : G)).toMonoidHom := by
    refine sup_le (fun u hu => ?_) (fun z hz => ?_)
    · show (MulAut.conj (g : G)) u ∈ (B ⊔ Z : Subgroup G)
      rw [MulAut.conj_apply]
      have e : (g : G) * u * (g : G)⁻¹ = ⁅(g : G), u⁆ * u := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hB' u hu)) (Subgroup.mem_sup_left hu)
    · show (MulAut.conj (g : G)) z ∈ (B ⊔ Z : Subgroup G)
      rw [MulAut.conj_apply]
      have e : (g : G) * z * (g : G)⁻¹ = z := by
        have := Subgroup.mem_centralizer_iff.mp g.2.2 z hz
        rw [mul_inv_eq_iff_eq_mul]
        exact this.symm
      rw [e]
      exact Subgroup.mem_sup_right hz
  exact hle hx

private theorem Ctx.normalizes_LB_of_fix_commSpace [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    {a : G} (ha : a ∈ LB M Q B) (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z)
    {g : ↥(H0 M Z)}
    (hgfix : ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), φ g w = w) :
    ∀ t ∈ LB M Q B, (g : G) * t * (g : G)⁻¹ ∈ LB M Q B := by
  intro t ht
  have hgBZ := Ctx.mem_normalizer_sup_Z_of_comm
    (hc.comm_mem_Z_of_fix_commSpace h hφπ ha hline hgfix)
  exact (Subgroup.mem_normalizer_iff.mp ((stroth_11_1a hc hw hn g.2.1).mp hgBZ) t).mp ht

private theorem Ctx.fixes_commSpace_of_mem_Kb [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {a : G} (ha : a ∈ LB M Q B)
    {Kb : Subgroup (Mbar M Q)} (hKH : Kb ≤ bar M Q (H0 M Z))
    (hfix : ∀ z ∈ Kb, ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), liftF φ z w = w)
    {z : Mbar M Q} (hz : z ∈ Kb) :
    ∃ g : ↥(H0 M Z), mkH M Q Z g = z ∧
      ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), φ g w = w := by
  obtain ⟨g, hg⟩ := mem_bar_H0_iff.mp (hKH hz)
  refine ⟨g, hg, fun w hw => ?_⟩
  have := hfix z hz w hw
  rwa [← hg, liftF_mkH hφker] at this

private theorem Ctx.normalizes_bar_LB_of_mem_Kb [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {a : G} (ha : a ∈ LB M Q B) (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z)
    {Kb : Subgroup (Mbar M Q)} (hKH : Kb ≤ bar M Q (H0 M Z))
    (hfix : ∀ z ∈ Kb, ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), liftF φ z w = w) :
    ∀ z ∈ Kb, ∀ l ∈ bar M Q (LB M Q B), z * l * z⁻¹ ∈ bar M Q (LB M Q B) := by
  intro z hz l hl
  obtain ⟨g, hg, hgfix⟩ := hc.fixes_commSpace_of_mem_Kb hφker ha hKH hfix hz
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hl
  have hx' : (x : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hx
  refine Subgroup.mem_map.mpr ⟨⟨(g : G), g.2.1⟩ * x * ⟨(g : G), g.2.1⟩⁻¹,
    Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
  · simpa using hc.normalizes_LB_of_fix_commSpace hw hn h hφπ ha hline hgfix _ hx'
  · rw [map_mul, map_mul, map_inv, ← hg]
    rfl

private theorem Ctx.commute_Kb_bar_LB [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {a : G} (ha : a ∈ LB M Q B) (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z)
    {Kb X : Subgroup (Mbar M Q)} (hKX : Kb ≤ X)
    (hXK : X ≤ Subgroup.normalizer (Kb : Set (Mbar M Q))) (hX : X.Normal)
    (hKH : Kb ≤ bar M Q (H0 M Z))
    (hfix : ∀ z ∈ Kb, ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), liftF φ z w = w)
    (hLK : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Kb : Set (Mbar M Q))) :
    ∀ k ∈ Kb, ∀ l ∈ bar M Q (LB M Q B), k * l = l * k := by
  have : Finite (Mbar M Q) := inferInstanceAs (Finite (↥M ⧸ Q.subgroupOf M))
  have hKL : Kb ≤ Subgroup.normalizer
      ((bar M Q (LB M Q B) : Subgroup (Mbar M Q)) : Set (Mbar M Q)) := fun z hz =>
    Subgroup.mem_normalizer_fintype fun l hl =>
      hc.normalizes_bar_LB_of_mem_Kb hw hn h hφπ hφker ha hline hKH hfix z hz l hl
  have hL2 : IsPGroup 2 ↥(bar M Q (LB M Q B)) := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hc.isElemAbelian_bar_LB.2 x x.2⟩
  exact commute_of_pCore_trivial hKX hXK hX hc.pCore_two_Mbar hL2 hLK hKL

private theorem Ctx.isPGroup_Kb_of_commute [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    {n : ℕ} (hw : Width Q Z n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q →
      M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q)
    {a : G} (ha : a ∈ LB M Q B) (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z)
    {Kb : Subgroup (Mbar M Q)} (hKH : Kb ≤ bar M Q (H0 M Z))
    (hfix : ∀ z ∈ Kb, ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), liftF φ z w = w)
    (hcommKL : ∀ k ∈ Kb, ∀ l ∈ bar M Q (LB M Q B), k * l = l * k) :
    IsPGroup 2 ↥Kb := by
  intro z
  obtain ⟨g, hg, hgfix⟩ := hc.fixes_commSpace_of_mem_Kb hφker ha hKH hfix z.2
  have hL : ∀ t ∈ LB M Q B, ⁅(g : G), t⁆ ∈ Q := by
    intro t ht
    have htM : t ∈ M := hc.LB_le_M ht
    have hmem : (QuotientGroup.mk' (Q.subgroupOf M) (⟨t, htM⟩ : ↥M)) ∈ bar M Q (LB M Q B) :=
      Subgroup.mem_map.mpr ⟨⟨t, htM⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
    have h1 := hcommKL z.1 z.2 _ hmem
    rw [← hg] at h1
    exact (mk_commute_iff ⟨(g : G), g.2.1⟩ ⟨t, htM⟩).mp h1
  obtain ⟨k, hk⟩ := stroth_11_1b_ii hc hw g.2 hL
    (hc.comm_mem_Z_of_fix_commSpace h hφπ ha hline hgfix)
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : mkH M Q Z (g ^ 2 ^ k) = 1 :=
    (mkH_eq_one_iff (g ^ 2 ^ k)).mpr (by simpa [Subgroup.coe_pow] using hk)
  rw [map_pow, hg] at h1
  simpa using h1

theorem Ctx.eq_bot_of_fix_commSpace [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ}
    (hw : Width Q Z n) (hn : 2 < n) (h : GlobalModelData M Q Z γ M₀)
    {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (g : ↥(H0 M Z)) (x : G), x ∈ Q → M₀.π ((g : G) * x * (g : G)⁻¹) = φ g (M₀.π x))
    (hφker : ∀ g : ↥(H0 M Z), φ g = 1 ↔ (g : G) ∈ Q) {a : G} (ha : a ∈ LB M Q B)
    (hline : B ≤ ⁅Q, Subgroup.zpowers a⁆ ⊔ Z) {Kb X : Subgroup (Mbar M Q)} (hKX : Kb ≤ X)
    (hXK : X ≤ Subgroup.normalizer (Kb : Set (Mbar M Q))) (hX : X.Normal)
    (hKH : Kb ≤ bar M Q (H0 M Z))
    (hfix : ∀ z ∈ Kb, ∀ w ∈ commSpace (φ ⟨a, hc.LB_le_H0 ha⟩), liftF φ z w = w)
    (hLK : bar M Q (LB M Q B) ≤ Subgroup.normalizer (Kb : Set (Mbar M Q))) : Kb = ⊥ := by
  have hKb2 : IsPGroup 2 ↥Kb :=
    hc.isPGroup_Kb_of_commute hw h hφπ hφker ha hline hKH hfix
      (hc.commute_Kb_bar_LB hw hn h hφπ hφker ha hline hKX hXK hX hKH hfix hLK)
  exact eq_bot_of_isPGroup_of_subnormal hKX hXK hX hc.pCore_two_Mbar hKb2

end CFSG.RankThree.GF2n.Stroth80
