module

public import CFSG.RankThree.GF2n.Stroth80.MaxAbCentralizer
public import CFSG.RankThree.GF2n.Stroth80.Sec34Fibre
public import CFSG.RankThree.GF2n.Stroth80.Sec39

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def PerpB (M Q B : Subgroup G) : Subgroup G :=
  Q ⊓ Subgroup.centralizer (Lgen M B : Set G)

theorem Ctx.Lgen_le_Q (hc : Ctx M Q Z B) : Lgen M B ≤ Q := by
  refine iSup₂_le fun m hm => ?_
  exact (Subgroup.map_mono hc.le : conjSubgroup m B ≤ conjSubgroup m Q).trans
    (hc.conj_Q_eq hm).le

theorem PerpB_le_Q : PerpB M Q B ≤ Q := inf_le_left

theorem Ctx.PerpB_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ PerpB M Q B) :
    m * x * m⁻¹ ∈ PerpB M Q B := by
  refine ⟨(hc.conj_mem_Q_of_mem_M hm).1 x hx.1, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
  have hn' : m⁻¹ * n * m ∈ Lgen M B := by
    have := (Subgroup.mem_normalizer_iff.mp (Lgen_normalizes M B (M.inv_mem hm)) n).mp hn
    simpa using this
  have hc' := Subgroup.mem_centralizer_iff.mp hx.2 _ hn'
  calc n * (m * x * m⁻¹) = m * ((m⁻¹ * n * m) * x) * m⁻¹ := by group
    _ = m * (x * (m⁻¹ * n * m)) * m⁻¹ := by rw [hc']
    _ = m * x * m⁻¹ * n := by group

theorem Ctx.Z_le_PerpB (hc : Ctx M Q Z B) : Z ≤ PerpB M Q B := fun z hz =>
  ⟨hc.Z_le_Q hz, Subgroup.mem_centralizer_iff.mpr fun n hn =>
    (hc.hyp.toHyp79.V_central hz (hc.Lgen_le_Q hn)).symm⟩

theorem Ctx.PerpB_le_centralizer_B (hc : Ctx M Q Z B) :
    PerpB M Q B ≤ Subgroup.centralizer (B : Set G) := fun x hx =>
  Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mem_centralizer_iff.mp hx.2 b (le_Lgen_self M B hb)

theorem Ctx.PerpB_inf_sup_le (hc : Ctx M Q Z B) {x : G} (hx : x ∈ PerpB M Q B)
    (hxs : x ∈ Lgen M B ⊔ Z) : x ∈ Z := by
  have h := hc.hyp.sup_inf_centralizer_eq hc.Lgen_le_Q (Lgen_normalizes M B)
  have hx' : x ∈ (Lgen M B ⊔ Z) ⊓ Subgroup.centralizer (Lgen M B : Set G) := ⟨hxs, hx.2⟩
  rwa [h] at hx'

theorem Ctx.PerpB_inf_B_le (hc : Ctx M Q Z B) {x : G} (hx : x ∈ PerpB M Q B) (hxB : x ∈ B) :
    x = 1 := by
  have h1 : x ∈ Z := hc.PerpB_inf_sup_le hx (Subgroup.mem_sup_left (le_Lgen_self M B hxB))
  have h2 : x ∈ Z ⊓ B := ⟨h1, hxB⟩
  rw [hc.inf_eq_bot, Subgroup.mem_bot] at h2
  exact h2

theorem Ctx.comm_mem_PerpB (hc : Ctx M Q Z B) {r c : G} (hr : r ∈ M) (hcc : c ∈ PerpB M Q B) :
    ⁅r, c⁆ ∈ PerpB M Q B := by
  rw [commutatorElement_def, show r * c * r⁻¹ * c⁻¹ = (r * c * r⁻¹) * c⁻¹ from rfl]
  exact (PerpB M Q B).mul_mem (hc.PerpB_conj hr hcc) ((PerpB M Q B).inv_mem hcc)

theorem StrothHyp.exists_ne_one_mem_Z (H : StrothHyp M Q Z) : ∃ z ∈ Z, z ≠ 1 := by
  by_contra h
  push Not at h
  have h1 : Z = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
  have h2 := H.q4
  rw [h1, Subgroup.card_bot] at h2
  omega

theorem Ctx.exists_ne_one_B (hc : Ctx M Q Z B) : ∃ c ∈ B, c ≠ 1 := by
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨z, hz, hz1⟩ := hc.hyp.exists_ne_one_mem_Z
  refine ⟨g * z * g⁻¹, ?_, ?_⟩
  · rw [hg, mem_conjSubgroup]
    simpa [mul_assoc] using hz
  · intro h
    apply hz1
    have := congrArg (fun y => g⁻¹ * y * g) h
    simpa [mul_assoc] using this

theorem Ctx.PerpB_inf_QB_le (hc : Ctx M Q Z B) : PerpB M Q B ⊓ QB B ≤ Z := by
  intro d hd
  obtain ⟨hdP, hdQB⟩ := hd
  have hcomm1 : ∀ s ∈ QB B ⊓ M, ⁅s, d⁆ = 1 := by
    intro s hs
    have h1 : ⁅s, d⁆ ∈ B := hc.comm_QB_le_B hs.1 hdQB
    have h2 : ⁅s, d⁆ ∈ PerpB M Q B := hc.comm_mem_PerpB hs.2 hdP
    exact hc.PerpB_inf_B_le h2 h1
  have hdZB : d ∈ B ⊔ Z := by
    by_contra hnot
    rw [sup_comm] at hnot
    obtain ⟨c₀, hc₀B, hc₀1⟩ := hc.exists_ne_one_B
    obtain ⟨s, hs, hsd⟩ := hc.exists_mem_QB_M_comm_eq hdQB hnot hc₀B
    exact hc₀1 (hsd ▸ hcomm1 s hs)
  have hBN : B ≤ Subgroup.normalizer (Z : Set G) := fun u hu =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hu))
  obtain ⟨u, hu, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hBN hdZB
  have huP : u ∈ PerpB M Q B := by
    have := (PerpB M Q B).mul_mem hdP ((PerpB M Q B).inv_mem (hc.Z_le_PerpB hz))
    simpa using this
  have hu1 : u = 1 := hc.PerpB_inf_B_le huP hu
  rw [hu1, one_mul]
  exact hz

theorem Ctx.comm_LB_PerpB_mem_Z (hc : Ctx M Q Z B) {r c : G} (hr : r ∈ LB M Q B)
    (hcc : c ∈ PerpB M Q B) : ⁅r, c⁆ ∈ Z := by
  have h1 : ⁅r, c⁆ ∈ Q ⊓ QB B :=
    hc.comm_mem_inf_of_mem_LB hr ⟨hcc.1, hc.PerpB_le_centralizer_B hcc⟩
  exact hc.PerpB_inf_QB_le ⟨hc.comm_mem_PerpB (hc.LB_le_M hr) hcc, h1.2⟩

theorem Ctx.conj_PerpB_le_Spure (hc : Ctx M Q Z B) {ω : G} (h1 : conjSubgroup ω Q = QB B)
    (h2 : conjSubgroup ω (QB B) = Q) (h3 : conjSubgroup ω Z = B)
    (h4 : conjSubgroup ω B = Z) : conjSubgroup ω (PerpB M Q B) ≤ hc.Spure := by
  intro t ht
  have htc : ω⁻¹ * t * ω ∈ PerpB M Q B := mem_conjSubgroup.mp ht
  set c := ω⁻¹ * t * ω with hcdef
  have ht' : t = ω * c * ω⁻¹ := by rw [hcdef]; group
  have htQB : t ∈ QB B := by
    rw [← h1, mem_conjSubgroup]
    exact htc.1
  have htZ : t ∈ Subgroup.centralizer (Z : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
    have hzB : ω⁻¹ * z * ω ∈ B := by
      have : z ∈ conjSubgroup ω B := h4 ▸ hz
      exact mem_conjSubgroup.mp this
    have hcomm : (ω⁻¹ * z * ω) * c = c * (ω⁻¹ * z * ω) :=
      Subgroup.mem_centralizer_iff.mp htc.2 _ (le_Lgen_self M B hzB)
    calc z * t = ω * ((ω⁻¹ * z * ω) * c) * ω⁻¹ := by rw [ht']; group
      _ = ω * (c * (ω⁻¹ * z * ω)) * ω⁻¹ := by rw [hcomm]
      _ = t * z := by rw [ht']; group
  have htM : t ∈ QB B ⊓ M := by
    rw [hc.QB_inf_M_eq]
    exact ⟨htQB, htZ⟩
  refine ⟨Subgroup.mem_sup_right htM, fun y hy => ?_⟩
  have hC : conjSubgroup ω (QB B ⊓ Subgroup.centralizer (Z : Set G)) =
      Q ⊓ Subgroup.centralizer (B : Set G) := by
    rw [conjSubgroup_inf, conjSubgroup_centralizer, h2, h3]
  have hy' : ω⁻¹ * y * ω ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := by
    rw [← hC] at hy
    exact mem_conjSubgroup.mp hy
  have hy'L : ω⁻¹ * y * ω ∈ LB M Q B :=
    Subgroup.mem_sup_right (by rw [hc.QB_inf_M_eq]; exact hy')
  have hZ : ⁅ω⁻¹ * y * ω, c⁆ ∈ Z := hc.comm_LB_PerpB_mem_Z hy'L htc
  have hZ' : ⁅c, ω⁻¹ * y * ω⁆ ∈ Z := by
    rw [← commutatorElement_inv]
    exact Z.inv_mem hZ
  have e : ⁅t, y⁆ = ω * ⁅c, ω⁻¹ * y * ω⁆ * ω⁻¹ := by
    rw [ht']
    simp only [commutatorElement_def]
    group
  rw [e]
  have hmem : ω * ⁅c, ω⁻¹ * y * ω⁆ * ω⁻¹ ∈ conjSubgroup ω Z :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using hZ')
  rw [h3] at hmem
  exact Subgroup.mem_sup_left hmem

theorem Ctx.conj_PerpB_inf_Q_le (hc : Ctx M Q Z B) {ω : G}
    (h2 : conjSubgroup ω (QB B) = Q) (h3 : conjSubgroup ω Z = B) :
    conjSubgroup ω (PerpB M Q B) ⊓ Q ≤ B := by
  rintro x ⟨hx1, hx2⟩
  have hx1' : ω⁻¹ * x * ω ∈ PerpB M Q B := mem_conjSubgroup.mp hx1
  have hx2' : ω⁻¹ * x * ω ∈ QB B := by
    rw [← h2] at hx2
    exact mem_conjSubgroup.mp hx2
  have hZ : ω⁻¹ * x * ω ∈ Z := hc.PerpB_inf_QB_le ⟨hx1', hx2'⟩
  rw [← h3]
  exact mem_conjSubgroup.mpr hZ

end CFSG.RankThree.GF2n.Stroth80
