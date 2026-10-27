module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddF81

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem ε_eq_of_mem_Z₁ (hI : L2OddInnerFact) (c : OddCoord T L V n) {z : ↥V}
    (hz : (z : G) ∈ quasithinOmegaOneCenter T) : c.ε z = c.ε z 0 • ![1, 0] := by
  have h1 : c.ε z 1 = 0 := (s.mem_Z_iff hI c z).mp hz
  funext i
  fin_cases i <;> simp [h1]

theorem isTISetUnder_M (hI : L2OddInnerFact) :
    IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) M := by
  obtain ⟨c⟩ := s.nonempty_coord
  have hh := s.hyp.hyp.toHyp5_0_1
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁
  intro g hgM hgN
  by_contra hne
  have hne' : Z₁ ⊓ conjSub g⁻¹ Z₁ ≠ ⊥ := hne
  have hgV : g ∈ Subgroup.normalizer (V : Set G) := by
    by_contra hgV
    have hbot := s.ti g hgM hgV
    apply hne'
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ V ⊓ CFSG.conjugate V g :=
      ⟨hx.1.2, show x ∈ conjSub g⁻¹ V from conjSub_mono _ inf_le_right hx.2⟩
    rw [hbot] at hx'
    exact hx'
  set x : Subgroup.normalizer (V : Set G) := ⟨g⁻¹, inv_mem hgV⟩ with hxdef
  have hxL : (x : G) ∈ Subgroup.normalizer (L : Set G) := inv_mem (hh.normal hgM)
  obtain ⟨σ, hσ⟩ := c.semi x hxL
  obtain ⟨v, hv, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne' |> fun ⟨w, hw⟩ =>
    (⟨w, w.2, fun h => hw (Subtype.ext h)⟩ : ∃ v ∈ Z₁ ⊓ conjSub g⁻¹ Z₁, v ≠ 1)
  have hz : g * v * g⁻¹ ∈ Z₁ := by
    have := mem_conjSub.mp hv.2
    simpa using this
  set z : ↥V := ⟨g * v * g⁻¹, hz.2⟩ with hzdef
  have hzv : conjAct V x z = ⟨v, hv.1.2⟩ := by
    apply Subtype.ext
    rw [conjAct_apply_coe]
    show g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v
    group
  have hε : c.act x (c.ε z) = c.ε ⟨v, hv.1.2⟩ := by rw [c.act_ε, hzv]
  have hz0 : c.ε z 0 ≠ 0 := by
    intro h0
    apply hv1
    have hzε : c.ε z = 0 := by
      rw [s.ε_eq_of_mem_Z₁ hI c (z := z) hz.1, h0, zero_smul]
    have hz1 : z = 1 := c.ε_bij.1 (by
      rw [hzε]
      have := c.ε_mul 1 1
      rw [mul_one] at this
      have h2 : c.ε 1 + c.ε 1 - c.ε 1 = c.ε 1 - c.ε 1 := by rw [← this]
      simpa using h2.symm)
    have : g * v * g⁻¹ = 1 := congrArg Subtype.val hz1
    have e : v = g⁻¹ * (g * v * g⁻¹) * g := by group
    rw [e, this]
    group
  have hxe : (c.act x ![1, 0]) 1 = 0 := by
    have h1 : c.ε ⟨v, hv.1.2⟩ 1 = 0 := (s.mem_Z_iff hI c _).mp hv.1.1
    rw [← hε, s.ε_eq_of_mem_Z₁ hI c (z := z) hz.1, hσ] at h1
    simp only [Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (by simpa using hz0)
  apply hgN
  have hxN : (x : G) ∈ Subgroup.normalizer (Z₁ : Set G) := by
    apply mem_normalizer_of_forall_conj_mem'
    intro w hw
    have hwV : (x : G) * w * (x : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp x.2 w).mp hw.2
    refine ⟨?_, hwV⟩
    have h1 : c.act x (c.ε ⟨w, hw.2⟩) = c.ε ⟨(x : G) * w * (x : G)⁻¹, hwV⟩ := by
      rw [c.act_ε]
      exact congrArg c.ε (Subtype.ext (by rw [conjAct_apply_coe]))
    refine (s.mem_Z_iff hI c ⟨_, hwV⟩).mpr ?_
    rw [← h1, s.ε_eq_of_mem_Z₁ hI c (z := ⟨w, hw.2⟩) hw.1, hσ]
    simp [hxe]
  simpa [hxdef] using inv_mem hxN

theorem exists_conj_eq_of_mem_Z₁ (hI : L2OddInnerFact) (hF : L2TorusFact) {z₀ z : G}
    (hz₀ : z₀ ∈ quasithinOmegaOneCenter T ⊓ V) (hz₀1 : z₀ ≠ 1)
    (hz : z ∈ quasithinOmegaOneCenter T ⊓ V) (hz1 : z ≠ 1) :
    ∃ d ∈ D, d * z₀ * d⁻¹ = z := by
  obtain ⟨c⟩ := s.nonempty_coord
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  set a₀ := c.ε ⟨z₀, hz₀.2⟩ 0 with ha₀
  set a := c.ε ⟨z, hz.2⟩ 0 with ha
  have hne : ∀ {y : G} (hy : y ∈ quasithinOmegaOneCenter T ⊓ V), y ≠ 1 → c.ε ⟨y, hy.2⟩ 0 ≠ 0 := by
    intro y hy hy1 h0
    apply hy1
    have hyε : c.ε ⟨y, hy.2⟩ = c.ε 1 := by
      rw [s.ε_eq_of_mem_Z₁ hI c (z := ⟨y, hy.2⟩) hy.1, h0, zero_smul]
      have := c.ε_mul 1 1
      rw [mul_one] at this
      have h2 : c.ε 1 + c.ε 1 - c.ε 1 = c.ε 1 - c.ε 1 := by rw [← this]
      simpa using h2.symm
    exact congrArg Subtype.val (c.ε_bij.1 hyε)
  have ha₀0 : a₀ ≠ 0 := hne hz₀ hz₀1
  have ha0 : a ≠ 0 := hne hz hz1
  obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c (div_ne_zero ha₀0 ha0)
  obtain ⟨A, hA0, hA⟩ := s.exists_mat_of_normalizer hI c d (hDL hdD) (s.D_le_normalizer_Z₁ hI hdD)
  have hA11 : (A : Matrix (Fin 2) (Fin 2) c.K) 1 1 = a₀ / a := by
    have h1 := hd ![0, 1]
    rw [hA, mulVec_one_of_lower _ hA0] at h1
    simpa using h1
  have hA00 : (A : Matrix (Fin 2) (Fin 2) c.K) 0 0 = a / a₀ := by
    have h1 := mul_eq_one_of_lower A hA0
    rw [hA11] at h1
    field_simp at h1 ⊢
    linear_combination h1
  refine ⟨d, hdD, ?_⟩
  have hdz₀ : (d : G) * z₀ * (d : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp d.2 z₀).mp hz₀.2
  have h1 : c.ε ⟨(d : G) * z₀ * (d : G)⁻¹, hdz₀⟩ = c.ε ⟨z, hz.2⟩ := by
    have h2 : c.ε ⟨(d : G) * z₀ * (d : G)⁻¹, hdz₀⟩ = c.act d (c.ε ⟨z₀, hz₀.2⟩) := by
      rw [c.act_ε]
      exact congrArg c.ε (Subtype.ext (by rw [conjAct_apply_coe]))
    rw [h2, s.ε_eq_of_mem_Z₁ hI c (z := ⟨z₀, hz₀.2⟩) hz₀.1,
      s.ε_eq_of_mem_Z₁ hI c (z := ⟨z, hz.2⟩) hz.1, hA]
    funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA00, ← ha₀, ← ha]
      field_simp
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hA0]
  exact congrArg Subtype.val (c.ε_bij.1 h1)

theorem isTISetUnder_top_of_Mp (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first)
    (hMp : IsTISetUnder (quasithinOmegaOneCenter T ⊓ V)
      (Subgroup.normalizer (oTwoUpper H : Set G))) :
    IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤ := by
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁
  have hCz := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.1.2
  intro g _ hgN
  by_contra hne
  have hne' : Z₁ ⊓ conjSub g⁻¹ Z₁ ≠ ⊥ := hne
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz₀ : g * z * g⁻¹ ∈ Z₁ := by
    have := mem_conjSub.mp hz.2
    simpa using this
  have hz₀1 : g * z * g⁻¹ ≠ 1 := fun h => hz1' (by
    have e : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [e, h]
    group)
  obtain ⟨d, hdD, hd⟩ := s.exists_conj_eq_of_mem_Z₁ hI hF hz₀ hz₀1 hz.1 hz1'
  have hdg : d * g ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc d * g * z = (d * (g * z * g⁻¹) * d⁻¹) * (d * g) := by group
      _ = z * (d * g) := by rw [hd]
  have hdgM := hCz z hz.1.1 hz1' hdg
  have hdgN : d * g ∈ Subgroup.normalizer (Z₁ : Set G) := by
    by_contra hn
    have hbot := hMp (d * g) hdgM hn
    have hmem : z ∈ Z₁ ⊓ CFSG.conjugate Z₁ (d * g) := by
      refine ⟨hz.1, ?_⟩
      show z ∈ conjSub (d * g)⁻¹ Z₁
      rw [mem_conjSub, inv_inv]
      have hc : d * g * z * (d * g)⁻¹ = z := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hdg, mul_inv_cancel_right]
      rw [hc]
      exact hz.1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hz1' hmem
  apply hgN
  have hdN : d ∈ Subgroup.normalizer (Z₁ : Set G) := s.D_le_normalizer_Z₁ hI hdD
  have e : g = d⁻¹ * (d * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ (inv_mem hdN) hdgN

end Setup5_1_17Odd

end CFSG.Quasithin.H13
