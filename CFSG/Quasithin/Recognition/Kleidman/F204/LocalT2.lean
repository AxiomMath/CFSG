module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalGeo
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalComm
public import CFSG.Quasithin.Recognition.Kleidman.F204.GeoBase2
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Offender

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

theorem three_centralizes_Zv (F : Frame L1 L2 S D X) {δ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hδ : vtype δ = false) (hZ : ∀ μ ∈ nbrs δ, Zv μ ≤ centerOf (stab μ)) {t : G}
    (ht : t ∈ stab δ) (ht3 : t ^ 3 = 1) : ∀ z ∈ Zv δ, t * z = z * t := by
  have hA := Amal.of_frame F
  obtain ⟨T, hT, μ, hμ, hTμ⟩ := hA.exists_sylow_stab δ
  have hle : Zv δ ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [Zv_eq_conjClosure hT]
    refine conjClosure_le fun c hc y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have ht' : c⁻¹ * s * c ∈ stab δ :=
      (stab δ).mul_mem ((stab δ).mul_mem ((stab δ).inv_mem hc) ht) hc
    have ht'3 : (c⁻¹ * s * c) ^ 3 = 1 := by
      have hcp := conj_pow (a := c⁻¹) (b := s) (i := 3)
      simp only [inv_inv] at hcp
      rw [hcp, ht3]; group
    have hμt : c⁻¹ * s * c ∈ stab μ := three_mem_stab_nbr F hδ hμ ht' ht'3
    have hy' : y ∈ Zv μ := (hA.omegaOneCenter_le_Zv hT hTμ).2.2 hy
    have hyc : y ∈ Subgroup.centralizer ((stab μ : Subgroup G) : Set G) := (hZ μ hμ hy').2
    have h1 := Subgroup.mem_centralizer_iff.mp hyc _ hμt
    calc s * (c * y * c⁻¹) = c * ((c⁻¹ * s * c) * y) * c⁻¹ := by group
      _ = c * (y * (c⁻¹ * s * c)) * c⁻¹ := by rw [h1]
      _ = c * y * c⁻¹ * s := by group
  intro z hz
  exact Subgroup.mem_centralizer_iff.mp (hle hz) t (Set.mem_singleton t)

theorem le_Qv_of_commute_three (F : Frame L1 L2 S D X) {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : vtype μ = true) {z t : G} {k : ℕ} (hz : z ∈ stab μ) (ht : t ∈ stab μ)
    (hz2 : z ^ 2 ^ k = 1) (ht3 : t ^ 3 = 1) (ht1 : t ≠ 1) (hc : z * t = t * z) : z ∈ Qv μ := by
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  obtain ⟨g, rfl⟩ := exists_smul_eq_γ₁ hμ
  rw [mem_stab_smul_γ₁ h₂] at hz ht
  rw [Qv_smul, mem_conjSub]
  have hQ : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  rw [hQ]
  refine Q2_of_commute_three F (k := k) hz ht ?_ ?_ ?_ ?_
  · have hcp := conj_pow (a := (g : G)⁻¹) (b := z) (i := 2 ^ k)
    simp only [inv_inv] at hcp
    rw [hcp, hz2]; group
  · have hcp := conj_pow (a := (g : G)⁻¹) (b := t) (i := 3)
    simp only [inv_inv] at hcp
    rw [hcp, ht3]; group
  · intro h
    apply ht1
    have : t = (g : G) * ((g : G)⁻¹ * t * g) * (g : G)⁻¹ := by group
    rw [this, h]; group
  · calc (g : G)⁻¹ * z * g * ((g : G)⁻¹ * t * g) = (g : G)⁻¹ * (z * t) * g := by group
      _ = (g : G)⁻¹ * (t * z) * g := by rw [hc]
      _ = (g : G)⁻¹ * t * g * ((g : G)⁻¹ * z * g) := by group

theorem exists_three_edge (F : Frame L1 L2 S D X) {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (h : μ ∈ nbrs δ) : ∃ t ∈ stab δ ⊓ stab μ, t ≠ 1 ∧ t ^ 3 = 1 := by
  have hA := Amal.of_frame F
  obtain ⟨g, -, he⟩ := hA.edge_conj h
  obtain ⟨d, hd, hd1⟩ := F.exists_ne_one_D
  have hd3 : d ^ 3 = 1 := by
    have := pow_card_eq_one' (G := ↥D) (x := ⟨d, hd⟩)
    rw [F.D_card] at this
    simpa using congrArg Subtype.val this
  refine ⟨(g : G) * d * (g : G)⁻¹, ?_, ?_, ?_⟩
  · rw [he, mem_conjSub]
    have : ((g : G))⁻¹ * ((g : G) * d * (g : G)⁻¹) * g = d := by group
    rw [this]
    exact F.D_le_B hd
  · intro h1
    apply hd1
    have : d = (g : G)⁻¹ * ((g : G) * d * (g : G)⁻¹) * g := by group
    rw [this, h1]; group
  · rw [conj_pow, hd3]; group

theorem t2_dist_ne (F : Frame L1 L2 S D X)
    (hZ : ∀ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype μ = true → Zv μ ≤ centerOf (stab μ))
    {α α' : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hα : vtype α = false) (hbad : ¬ Zv α ≤ Qv α')
    (hd : dist α α' = bAt α) (hodd : bAt α = 1 ∨ bAt α = 3) : False := by
  have hA := Amal.of_frame F
  have key : vtype α' = true ∧ ∃ t ∈ stab α ⊓ stab α', t ≠ 1 ∧ t ^ 3 = 1 := by
    rcases hodd with h1 | h3
    · have hadj : α' ∈ nbrs α := dist_eq_one_iff_adj.mp (hd.trans h1)
      refine ⟨?_, exists_three_edge F hadj⟩
      have := vtype_ne_of_adj hadj
      cases hv : vtype α' <;> simp_all
    · have hd3 : dist α α' = 3 := hd.trans h3
      obtain ⟨v2, h2, h2d⟩ := exists_adj_dist_eq rfl (α := α) (δ := α') (d := 2) hd3
      obtain ⟨v1, h1', h1d⟩ := exists_adj_dist_eq rfl (α := α) (δ := v2) (d := 1) h2d
      have hα1 : (graph _ _ _).Adj α v1 := dist_eq_one_iff_adj.mp h1d
      have hv1 : vtype v1 = true := by
        have := vtype_ne_of_adj hα1
        cases hv : vtype v1 <;> simp_all
      have hv2 : vtype v2 = false := by
        have := vtype_ne_of_adj h1'
        cases hv : vtype v2 <;> simp_all
      have hα'v : vtype α' = true := by
        have := vtype_ne_of_adj h2
        cases hv : vtype α' <;> simp_all
      refine ⟨hα'v, ?_⟩
      have hne : α ≠ v2 := by
        intro h
        rw [← h, CosetGeom.dist_self] at h2d
        omega
      obtain ⟨t, ht1, ht1', ht3, htα, htv2⟩ :=
        exists_three_stab_two_nbrs F hv1 (show α ∈ nbrs v1 from hα1.symm)
          (show v2 ∈ nbrs v1 from h1'.symm) hne
      exact ⟨t, ⟨htα, three_mem_stab_nbr F hv2 (show α' ∈ nbrs v2 from h2.symm) htv2 ht3⟩,
        ht1', ht3⟩
  obtain ⟨hα'v, t, ⟨htα, htα'⟩, ht1, ht3⟩ := key
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

end CFSG.Quasithin.Kleidman.F204
