module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabThirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_rconj_of_conj_mem {X : Subgroup G} {g c : G}
    (hc : g * c * g⁻¹ ∈ Subgroup.normalizer (X : Set G)) :
    c ∈ Subgroup.normalizer (rconj X g : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_rconj, mem_rconj]
  have e : g * (c * y * c⁻¹) * g⁻¹ = (g * c * g⁻¹) * (g * y * g⁻¹) * (g * c * g⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hc _

namespace Hyp1281Two

@[expose] def centralizerHat (T M : Subgroup G) : Subgroup G :=
  centralizerMod (centerOf (uOfL22 T M)) (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (uOfL22 T M)

theorem uOfL22_le_centralizerHat (h : Hyp1281Two G T M L) :
    uOfL22 T M ≤ centralizerHat T M := by
  intro u hu
  refine ⟨h.uOfL22_le_g1 hu, ?_, fun u' hu' => ?_⟩
  · exact normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer hu)
  · exact h.omegaOneCenter_le_centerOf_uOfL22 (h.commutator_mem_omegaOneCenter hu hu')

theorem centralizer_le_normalizer_centralizerHat (h : Hyp1281Two G T M L) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (centralizerHat T M : Set G) :=
  le_normalizer_centralizerMod
    (fun _ hx => normalizer_le_normalizer_centerOf _ (h.g1_le_normalizer_uOfL22 hx))
    Subgroup.le_normalizer
    (fun _ hx => h.g1_le_normalizer_uOfL22 hx)

theorem exists_mul_mem_centralizer_of_mem_inf (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {y : G}
    (hyH : y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hyN : y ∈ Subgroup.normalizer (VZ T M : Set G)) :
    ∃ u ∈ uOfL22 T M, u⁻¹ * y ∈ Subgroup.centralizer (VZ T M : Set G) := by
  by_cases hyC : y ∈ Subgroup.centralizer (VZ T M : Set G)
  · exact ⟨1, Subgroup.one_mem _, by simpa using hyC⟩
  · obtain ⟨u₀, hu₀U, hu₀W⟩ : ∃ u₀ ∈ uOfL22 T M, u₀ ∉ wOfU T M := by
      by_contra hall
      push Not at hall
      exact h.not_le_centralizer_VZ_of_nonabelian hU fun u hu => (hall u hu).2
    have hu₀C : u₀ ∉ Subgroup.centralizer (VZ T M : Set G) := fun hc => hu₀W ⟨hu₀U, hc⟩
    have hu₀T : u₀ ∈ T := h.uOfL22_le_T hu₀U
    exact ⟨u₀, hu₀U, h.inv_mul_mem_centralizer_VZ (h.isTwoReducedIn.1.2.1 (h.inM.2 hu₀T)) hyN
      (h.almostSpecialHyp_g1.T_le_H hu₀T) hyH hu₀C hyC⟩

section

variable (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T L g)

include h hU hg

omit hU in
theorem centralizer_VZ_le_normalizer_rconj_uOfL22 :
    Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.normalizer (rconj (uOfL22 T M) g : Set G) := by
  intro c hc
  refine mem_normalizer_rconj_of_conj_mem ?_
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans h.LT_le_normalizer_VZ) hg.mem
  have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hgN) c).mp hc
  exact h.g1_le_normalizer_uOfL22 (Subgroup.centralizer_le (omegaOneCenter_le_VZ T M) hc')

omit hU in
theorem centralizer_VZ_le_normalizer_rconj_wOfU :
    Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.normalizer (rconj (wOfU T M) g : Set G) := by
  intro c hc
  refine mem_normalizer_rconj_of_conj_mem ?_
  have hgN : g ∈ Subgroup.normalizer (VZ T M : Set G) :=
    ((le_sup_left : L ≤ L ⊔ T).trans h.LT_le_normalizer_VZ) hg.mem
  have hc' : g * c * g⁻¹ ∈ Subgroup.centralizer (VZ T M : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer'' _ hgN) c).mp hc
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨h.g1_le_normalizer_uOfL22 (Subgroup.centralizer_le (omegaOneCenter_le_VZ T M) hc'),
      Subgroup.le_normalizer hc'⟩

omit hU in
theorem centralizer_VZ_le_normalizer_rconj_centerOf :
    Subgroup.centralizer (VZ T M : Set G) ≤
      Subgroup.normalizer (rconj (centerOf (uOfL22 T M)) g : Set G) := by
  intro c hc
  rw [← centerOf_rconj]
  exact normalizer_le_normalizer_centerOf _
    (h.centralizer_VZ_le_normalizer_rconj_uOfL22 hg hc)

omit hU hg in
theorem inf_normalizer_le_normalizer_sup_centralizerHat {K : Subgroup G}
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    (hK : Subgroup.centralizer (VZ T M : Set G) ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
        Subgroup.normalizer (VZ T M : Set G) ≤
      Subgroup.normalizer ((K ⊔ centralizerHat T M : Subgroup G) : Set G) := by
  rintro y ⟨hyH, hyN⟩
  obtain ⟨u, hu, huc⟩ := h.exists_mul_mem_centralizer_of_mem_inf hU hyH hyN
  have hyeq : y = u * (u⁻¹ * y) := by group
  rw [hyeq]
  refine Subgroup.mul_mem _ (Subgroup.le_normalizer
    (le_sup_right (a := K) (b := centralizerHat T M) (h.uOfL22_le_centralizerHat hu))) ?_
  have hcH : u⁻¹ * y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le (omegaOneCenter_le_VZ T M) huc
  exact Subgroup.inf_normalizer_le_normalizer_sup K (centralizerHat T M)
    ⟨hK huc, h.centralizer_le_normalizer_centralizerHat hcH⟩

theorem lemma_12_8_12_two :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
          Subgroup.normalizer (VZ T M : Set G) ≤
        Subgroup.normalizer ((rconj (wOfU T M) g ⊔ centralizerHat T M : Subgroup G) : Set G) ∧
      Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊓
          Subgroup.normalizer (VZ T M : Set G) ≤
        Subgroup.normalizer
          ((rconj (centerOf (uOfL22 T M)) g ⊔ centralizerHat T M : Subgroup G) : Set G) ∧
      T ≤ Subgroup.normalizer ((rconj (wOfU T M) g ⊔ centralizerHat T M : Subgroup G) : Set G) := by
  have h1 := h.inf_normalizer_le_normalizer_sup_centralizerHat hU
    (h.centralizer_VZ_le_normalizer_rconj_wOfU hg)
  refine ⟨h1, h.inf_normalizer_le_normalizer_sup_centralizerHat hU
    (h.centralizer_VZ_le_normalizer_rconj_centerOf hg), fun t ht => h1 ⟨?_, ?_⟩⟩
  · exact h.almostSpecialHyp_g1.T_le_H ht
  · exact h.isTwoReducedIn.1.2.1 (h.inM.2 ht)

theorem lemma_12_8_11_one :
    ⁅wOfU T M, rconj (wOfU T M) g⁆ ≤ wOfU T M ⊓ rconj (wOfU T M) g :=
  h.commutator_wOfU_rconj_le hU hg

theorem lemma_12_8_11_two :
    IsElemAbelian 2 (wOfU T M ⊓ rconj (wOfU T M) g) ∧
      frattiniOf (wOfU T M ⊓ rconj (wOfU T M) g) = ⊥ := by
  have hE : IsElemAbelian 2 (wOfU T M ⊓ rconj (wOfU T M) g) := by
    rw [h.wOfU_inf_rconj_eq hU hg]
    exact h.isElemAbelian_inf_rconj hU hg
  refine ⟨hE, ?_⟩
  rw [eq_bot_iff]
  refine frattiniOf_le_of_forall (fun x hx y hy => ?_) (fun x hx => ?_)
  · have hxy : x * y = y * x := congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [Subgroup.mem_bot]
    calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [hxy]
      _ = 1 := by group
  · rw [Subgroup.mem_bot]
    exact hE.2 x hx

theorem lemma_12_8_11_four :
    centralizerMod (centerOf (uOfL22 T M)) (wOfU T M ⊓ rconj (wOfU T M) g)
        (rconj (wOfU T M) g) = VZ T M := by
  have hE : wOfU T M ⊓ rconj (wOfU T M) g = uOfL22 T M ⊓ rconj (uOfL22 T M) g :=
    h.wOfU_inf_rconj_eq hU hg
  have hVE : VZ T M ≤ wOfU T M ⊓ rconj (wOfU T M) g := by
    rw [hE]
    exact h.VZ_le_inf_rconj hU hg
  have hV1gV : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M :=
    (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
  have hCX : ∀ v ∈ VZ T M, v ∈ centerOf (rconj (wOfU T M) g) := by
    intro v hv
    rw [h.centerOf_rconj_wOfU_eq hU hg]
    exact Subgroup.mem_sup_left hv
  apply le_antisymm
  · rintro e ⟨heE, -, hecomm⟩
    have heX : e ∈ rconj (wOfU T M) g := heE.2
    have heUg : e ∈ rconj (uOfL22 T M) g := by
      rw [hE] at heE
      exact heE.2
    have hcX : ∀ x ∈ rconj (wOfU T M) g, x * e = e * x := by
      intro x hx
      have hxUg : x ∈ rconj (uOfL22 T M) g := rconj_le_rconj (wOfU_le_uOfL22 T M) g hx
      have h1 : e * x * e⁻¹ * x⁻¹ ∈ rconj (quasithinOmegaOneCenter T) g := by
        rw [mem_rconj]
        have he' : g * e * g⁻¹ ∈ uOfL22 T M := mem_rconj.mp heUg
        have hx' : g * x * g⁻¹ ∈ uOfL22 T M := mem_rconj.mp hxUg
        have := h.commutator_mem_omegaOneCenter he' hx'
        have e1 : g * (e * x * e⁻¹ * x⁻¹) * g⁻¹ =
            (g * e * g⁻¹) * (g * x * g⁻¹) * (g * e * g⁻¹)⁻¹ * (g * x * g⁻¹)⁻¹ := by group
        rw [e1]
        exact this
      have h2 : e * x * e⁻¹ * x⁻¹ ∈ centerOf (uOfL22 T M) := hecomm x hx
      have h3 : e * x * e⁻¹ * x⁻¹ ∈ rconj (quasithinOmegaOneCenter T) g ⊓ centerOf (uOfL22 T M) :=
        ⟨h1, h2⟩
      rw [h.lemma_12_8_9_seven hU hg] at h3
      have h4 : e * x * e⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.mp h3
      have h5 : e * x = x * e := by
        calc e * x = (e * x * e⁻¹ * x⁻¹) * x * e := by group
          _ = x * e := by rw [h4]; group
      exact h5.symm
    have heC : e ∈ centerOf (rconj (wOfU T M) g) :=
      ⟨heX, Subgroup.mem_centralizer_iff.mpr hcX⟩
    rw [h.centerOf_rconj_wOfU_eq hU hg] at heC
    have hVc : ∀ v ∈ VZ T M, ∀ z ∈ rconj (centerOf (uOfL22 T M)) g, v * z = z * v := by
      intro v hv z hz
      exact (Subgroup.mem_centralizer_iff.mp (hCX v hv).2 z
        (rconj_centerOf_le_rconj_wOfU T M g hz)).symm
    obtain ⟨v, hv, z, hz, rfl⟩ := exists_eq_mul_of_mem_sup_of_forall_commute hVc heC
    have hzU : z ∈ uOfL22 T M := by
      have h1 : v⁻¹ * (v * z) ∈ uOfL22 T M :=
        (uOfL22 T M).mul_mem ((uOfL22 T M).inv_mem (VZ_le_uOfL22 T M hv))
          (by rw [hE] at heE; exact heE.1)
      simpa using h1
    have hz' : z ∈ rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M := ⟨hz, hzU⟩
    rw [h.lemma_12_8_10_one_symm hU hg, h.centerOf_inf_rconj_centerOf_eq_bot hU hg,
      bot_sup_eq] at hz'
    exact (VZ T M).mul_mem hv (hV1gV hz')
  · intro v hv
    refine ⟨hVE hv, normalizer_le_normalizer_centerOf _ (Subgroup.le_normalizer
      (VZ_le_uOfL22 T M hv)), fun x hx => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp (hCX v hv).2 x hx
    have e3 : v * x * v⁻¹ * x⁻¹ = 1 := by
      calc v * x * v⁻¹ * x⁻¹ = (x * v) * v⁻¹ * x⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e3]
    exact Subgroup.one_mem _

end

end Hyp1281Two

end CFSG.Quasithin
