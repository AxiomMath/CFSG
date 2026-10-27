module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalPath
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFixed
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalT2

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem t2_contra (F : Frame L1 L2 S D X)
    (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
    {α α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = false) (hbad : ¬ Zv α ≤ Qv α')
    (hd : dist α α' = bAt α) (hα'v : vtype α' = true) {t : G} (htα : t ∈ stab α)
    (htα' : t ∈ stab α') (ht1 : t ≠ 1) (ht3 : t ^ 3 = 1) : False := by
  have hA := Amal.of_frame F
  have hZα : ∀ μ ∈ nbrs α, Zv μ ≤ centerOf (stab μ) := fun μ hμ => hZ μ (by
    have := vtype_ne_of_adj (show (graph _ _ _).Adj α μ from hμ)
    cases hv : vtype μ <;> simp_all)
  have hcen := three_centralizes_Zv F hα hZα htα ht3
  have hZle : Zv α ≤ stab α' := hA.Zv_le_stab_of_dist_le hd.le
  apply hbad
  intro z hz
  refine le_Qv_of_commute_three F hα'v (k := 1) (hZle hz) htα' ?_ ht3 ht1 ?_
  · have := (hA.isElemAbelian_Zv α).2 z hz
    simpa using this
  · exact (hcen z hz).symm

omit [Finite G] in
theorem conj_mem_stab_of_fix {H M : Subgroup G} (y : ↥(H ⊔ M)) {x : Geo H M} {t : G}
    (hyx : y • x = x) (ht : t ∈ stab x) : (y : G) * t * (y : G)⁻¹ ∈ stab x := by
  have h1 : (y : G) * t * (y : G)⁻¹ ∈ stab (y • x) := by
    rw [stab_smul]; exact mem_conjSub_of_mem' ht
  rwa [hyx] at h1

theorem t2_dist_ne_five (F : Frame L1 L2 S D X)
    (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
    (hPU : ¬ P1 L1 L2 S ≤ Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G))
    {α α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = false) (hbad : ¬ Zv α ≤ Qv α')
    (hd : dist α α' = bAt α) (h5 : bAt α = 5) : False := by
  have hA := Amal.of_frame F
  have hd5 : dist α α' = 4 + 1 := hd.trans h5
  obtain ⟨v4, h4, h4d⟩ := exists_adj_dist_eq rfl (α := α) (δ := α') (d := 4) hd5
  obtain ⟨v3, h3, h3d⟩ := exists_adj_dist_eq rfl (α := α) (δ := v4) (d := 3) h4d
  obtain ⟨v2, h2, h2d⟩ := exists_adj_dist_eq rfl (α := α) (δ := v3) (d := 2) h3d
  obtain ⟨v1, h1, h1d⟩ := exists_adj_dist_eq rfl (α := α) (δ := v2) (d := 1) h2d
  have h0 : (graph _ _ _).Adj α v1 := dist_eq_one_iff_adj.mp h1d
  have ty : ∀ {a b : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, (graph _ _ _).Adj a b →
      vtype a = false → vtype b = true := by
    intro a b hab ha
    have := vtype_ne_of_adj hab
    cases hv : vtype b <;> simp_all
  have ty' : ∀ {a b : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, (graph _ _ _).Adj a b →
      vtype a = true → vtype b = false := by
    intro a b hab ha
    have := vtype_ne_of_adj hab
    cases hv : vtype b <;> simp_all
  have hv1 : vtype v1 = true := ty h0 hα
  have hv2 : vtype v2 = false := ty' h1.symm hv1
  have hv3 : vtype v3 = true := ty h2.symm hv2
  have hv4 : vtype v4 = false := ty' h3.symm hv3
  have hα'v : vtype α' = true := ty h4.symm hv4
  have n02 : α ≠ v2 := by
    intro h; rw [← h, CosetGeom.dist_self] at h2d; omega
  have n13 : v1 ≠ v3 := by
    intro h
    have : dist α v1 = dist α v3 := by rw [h]
    omega
  have n24 : v2 ≠ v4 := by
    intro h
    have : dist α v2 = dist α v4 := by rw [h]
    omega
  obtain ⟨t, ht1, ht1', ht3, htα, htv2⟩ :=
    exists_three_stab_two_nbrs F hv1 (show α ∈ nbrs v1 from h0.symm)
      (show v2 ∈ nbrs v1 from h1.symm) n02
  have htv3 : t ∈ stab v3 := three_mem_stab_nbr F hv2 (show v3 ∈ nbrs v2 from h2.symm) htv2 ht3
  have hcard := card_fixed_nbrs_three F hv3 htv3 ht3 ht1'
  obtain ⟨w, hwn, hwt, hwv2⟩ : ∃ w : Geo (P1 L1 L2 S) (P2 L1 L2 S), w ∈ nbrs v3 ∧ t ∈ stab w ∧
      w ≠ v2 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S) // μ ∈ nbrs v3 ∧ t ∈ stab μ} :=
      ⟨fun a b => Subtype.ext ((hcon a.1 a.2.1 a.2.2).trans (hcon b.1 b.2.1 b.2.2).symm)⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨q, hqQ, hqw⟩ := exists_Qv_smul_nbr F hv3 (show v2 ∈ nbrs v3 from h2) hwn
    (show v4 ∈ nbrs v3 from h3.symm) hwv2 n24.symm
  have hsup := Qv_le_sup_of_not_normal F hPU hv2 (show v1 ∈ nbrs v2 from h1)
    (show v3 ∈ nbrs v2 from h2.symm) n13
  have hQN : ∀ {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, μ ∈ nbrs δ →
      Qv δ ≤ Subgroup.normalizer ((Qv μ : Subgroup G) : Set G) := fun {δ μ} hμ =>
    (hA.Qv_le_stab_of_mem_nbrs hμ).trans (le_normalizer_pCoreOf 2 (stab μ))
  have hQs : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), Qv δ ≤ stab δ := fun δ => pCoreOf_le 2 (stab δ)
  have hNy : (Qv v2 ⊓ Qv v3) ≤ Subgroup.normalizer ((Qv v2 ⊓ Qv v1 : Subgroup G) : Set G) := by
    refine le_normalizer_inf (inf_le_left.trans ?_) (inf_le_left.trans ?_)
    · exact (hQs v2).trans (le_normalizer_pCoreOf 2 (stab v2))
    · exact hQN (show v1 ∈ nbrs v2 from h1)
  obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hNy).mp (hsup hqQ)
  have haG : (a : G) ∈ stab v2 := hQs v2 ha.1
  have hbG : (b : G) ∈ stab v3 := hQs v3 hb.2
  obtain ⟨haG0, -⟩ := mem_stab.mp haG
  obtain ⟨hbG0, -⟩ := mem_stab.mp hbG
  set ya : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨a, haG0⟩ with hya
  set yb : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨b, hbG0⟩ with hyb
  have hq_eq : q = ya * yb := Subtype.ext hab
  have hybw : yb • w = w :=
    smul_eq_of_mem_stab (hA.Qv_le_stab_of_mem_nbrs hwn hb.2 |> fun h => h)
  have hyaw : ya • w = v4 := by
    rw [← hqw, hq_eq, mul_smul, hybw]
  have hyaα : ya • α = α :=
    smul_eq_of_mem_stab (hA.Qv_le_stab_of_mem_nbrs (show α ∈ nbrs v1 from h0.symm) ha.2)
  have ht'α : (a : G) * t * (a : G)⁻¹ ∈ stab α := conj_mem_stab_of_fix ya hyaα htα
  have ht'w : (a : G) * t * (a : G)⁻¹ ∈ stab v4 := by
    have h1' : (a : G) * t * (a : G)⁻¹ ∈ stab (ya • w) := by
      rw [stab_smul]; exact mem_conjSub_of_mem' hwt
    rwa [hyaw] at h1'
  have ht'3 : ((a : G) * t * (a : G)⁻¹) ^ 3 = 1 := by rw [conj_pow, ht3]; group
  have ht'1 : (a : G) * t * (a : G)⁻¹ ≠ 1 := by
    intro h
    apply ht1'
    have : t = (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * a := by group
    rw [this, h]; group
  have ht'α' : (a : G) * t * (a : G)⁻¹ ∈ stab α' :=
    three_mem_stab_nbr F hv4 (show α' ∈ nbrs v4 from h4.symm) ht'w ht'3
  exact t2_contra F hZ hα hbad hd hα'v ht'α ht'α' ht'1 ht'3

end CFSG.Quasithin.Kleidman.F204
