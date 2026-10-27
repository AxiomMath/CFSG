module

public import CFSG.Quasithin.EmptyFaithful.S143WVt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement

namespace S143W

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

section PG

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T (yOfL22 T M) g)

@[expose] def pOf (T M : Subgroup G) (g : G) : Subgroup G :=
  conjClosure (rconj (centerOf (uOfL22 T M)) g) (mcOf T)

include h hU hg in
theorem rconj_centerOf_le_T : rconj (centerOf (uOfL22 T M)) g ≤ T :=
  (Hyp1281Two.rconj_centerOf_le_rconj_wOfU T M g).trans (h.rconj_wOfU_le_T hU hg)

include h hU hg in
theorem pOf_le_H : pOf T M g ≤ mcOf T :=
  conjClosure_le fun _ hx _ hy =>
    (mcOf T).mul_mem ((mcOf T).mul_mem hx (h.almostSpecialHyp_g1.T_le_H
      (rconj_centerOf_le_T h hU hg hy))) ((mcOf T).inv_mem hx)

omit [Finite G] in
theorem pOf_normalized (x : G) (hx : x ∈ mcOf T) {p : G} (hp : p ∈ pOf T M g) :
    x * p * x⁻¹ ∈ pOf T M g :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hx) p).mp hp

include h hU hg in
theorem pOf_centralizes {p : G} (hp : p ∈ pOf T M g) {z : G} (hz : z ∈ centerOf (uOfL22 T M)) :
    p * z = z * p := by
  have hle : pOf T M g ≤ Subgroup.centralizer (centerOf (uOfL22 T M) : Set G) := by
    refine conjClosure_le fun x hx y hy => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hxN : x ∈ Subgroup.normalizer (centerOf (uOfL22 T M) : Set G) :=
      normalizer_le_normalizer_centerOf _ (h.g1_le_normalizer_uOfL22 hx)
    have hz' : x⁻¹ * z * x ∈ centerOf (uOfL22 T M) := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (centerOf (uOfL22 T M) : Set G)).inv_mem hxN) z).mp hz
      simpa using this
    have hcomm : ⁅x⁻¹ * z * x, y⁆ = 1 := by
      have : ⁅x⁻¹ * z * x, y⁆ ∈ ⁅centerOf (uOfL22 T M), rconj (centerOf (uOfL22 T M)) g⁆ :=
        Subgroup.commutator_mem_commutator hz' hy
      rw [(h.lemma_12_8_13_three hU hg).2.2] at this
      exact Subgroup.mem_bot.mp this
    have hc2 : (x⁻¹ * z * x) * y = y * (x⁻¹ * z * x) := by
      calc (x⁻¹ * z * x) * y = ⁅x⁻¹ * z * x, y⁆ * (y * (x⁻¹ * z * x)) := by
            simp only [commutatorElement_def]; group
        _ = y * (x⁻¹ * z * x) := by rw [hcomm, one_mul]
    calc z * (x * y * x⁻¹) = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by rw [hc2]
      _ = (x * y * x⁻¹) * z := by group
  have := Subgroup.mem_centralizer_iff.mp (hle hp) z hz
  exact this.symm

end PG

section Module

variable (h : Hyp1281Two G T M L) (Tm : TildeModel T M) (D : HatModel T M)

theorem card_map_tilde_eq {K : Subgroup ↥(mcOf T)}
    (hker : ∀ k ∈ K, S143V.rhoH h D k = 1 → Tm.ρ k = 1) :
    Nat.card (K.map Tm.ρ) = Nat.card (K.map (S143V.rhoH h D)) := by
  have hker' : (Tm.ρ.comp K.subtype).ker = ((S143V.rhoH h D).comp K.subtype).ker := by
    ext k
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · intro hk1
      ext w
      obtain ⟨v, rfl⟩ := Tm.phi_surjective h D w
      rw [← Tm.phi_ρ h D, hk1]
      simp
    · exact fun hk1 => hker k k.2 hk1
  have e1 : (Tm.ρ.comp K.subtype).range = K.map Tm.ρ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have e2 : ((S143V.rhoH h D).comp K.subtype).range = K.map (S143V.rhoH h D) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← e1, ← e2, ← Subgroup.index_ker, ← Subgroup.index_ker, hker']

include h in
theorem span_orbit_eq_top (vv : Tm.V)
    (hV : ∀ w ∈ VZ T M, ∃ hw : w ∈ uOfL22 T M, Tm.c ⟨w, hw⟩ = 0 ∨ Tm.c ⟨w, hw⟩ = vv) :
    Submodule.span (ZMod 2) (Set.range fun x : ↥(mcOf T) => Tm.ρ x vv) = ⊤ := by
  set S := Submodule.span (ZMod 2) (Set.range fun x : ↥(mcOf T) => Tm.ρ x vv) with hS
  have key : ∀ x (hx : x ∈ Subgroup.closure {y | ∃ k ∈ mcOf T, ∃ z ∈ VZ T M, k * z * k⁻¹ = y}),
      ∃ hxU : x ∈ uOfL22 T M, Tm.c ⟨x, hxU⟩ ∈ S := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, hk, z, hz, rfl⟩ := hx
      obtain ⟨hzU, hz0⟩ := hV z hz
      have hxU : k * z * k⁻¹ ∈ uOfL22 T M :=
        HatModel.conj_mem_uOfL22 (h.g1_le_normalizer_uOfL22 hk) hzU
      refine ⟨hxU, ?_⟩
      have := Tm.ρ_c ⟨k, hk⟩ ⟨z, hzU⟩ hxU
      rw [← this]
      rcases hz0 with h0 | h0
      · rw [h0, map_zero]
        exact S.zero_mem
      · rw [h0]
        exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
    | one =>
      refine ⟨(uOfL22 T M).one_mem, ?_⟩
      have : (⟨1, (uOfL22 T M).one_mem⟩ : ↥(uOfL22 T M)) = 1 := rfl
      rw [this, Tm.c_one]
      exact S.zero_mem
    | mul x y hx hy ihx ihy =>
      obtain ⟨hxU, hxS⟩ := ihx
      obtain ⟨hyU, hyS⟩ := ihy
      refine ⟨(uOfL22 T M).mul_mem hxU hyU, ?_⟩
      have := Tm.c_mul ⟨x, hxU⟩ ⟨y, hyU⟩
      have e : (⟨x * y, (uOfL22 T M).mul_mem hxU hyU⟩ : ↥(uOfL22 T M)) =
          ⟨x, hxU⟩ * ⟨y, hyU⟩ := rfl
      rw [e, this]
      exact S.add_mem hxS hyS
    | inv x hx ih =>
      obtain ⟨hxU, hxS⟩ := ih
      refine ⟨(uOfL22 T M).inv_mem hxU, ?_⟩
      have h1 := Tm.c_mul ⟨x, hxU⟩ ⟨x, hxU⟩⁻¹
      rw [mul_inv_cancel, Tm.c_one] at h1
      have e : (⟨x⁻¹, (uOfL22 T M).inv_mem hxU⟩ : ↥(uOfL22 T M)) = ⟨x, hxU⟩⁻¹ := rfl
      rw [e]
      have h2 : Tm.c (⟨x, hxU⟩⁻¹) = - Tm.c ⟨x, hxU⟩ := eq_neg_of_add_eq_zero_right h1.symm
      rw [h2]
      exact S.neg_mem hxS
  rw [eq_top_iff]
  intro v _
  obtain ⟨u, rfl⟩ := Tm.c_surj v
  exact (key (u : G) u.2).2

end Module

end S143W

end CFSG.Quasithin
