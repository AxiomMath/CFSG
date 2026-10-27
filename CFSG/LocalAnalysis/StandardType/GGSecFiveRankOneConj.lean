module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs

public section

namespace CFSG.StandardType

section

variable {G : Type} [Group G] [Finite G]

theorem ggMap_conj_centralizer (g : G) (H : Subgroup G) :
    (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext z
  constructor
  · intro hz
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hz
    rw [← hcz]
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro y hy
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp hy
    rw [← hhy]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * h * g⁻¹ * (g * c * g⁻¹) = g * (h * c) * g⁻¹ := by group
      _ = g * (c * h) * g⁻¹ := by rw [hc h hh]
      _ = g * c * g⁻¹ * (g * h * g⁻¹) := by group
  · intro hz
    rw [Subgroup.mem_centralizer_iff] at hz
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * z * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have h2 : (MulAut.conj g).toMonoidHom h * z = z * (MulAut.conj g).toMonoidHom h :=
        hz ((MulAut.conj g).toMonoidHom h) (Subgroup.mem_map.mpr ⟨h, hh, rfl⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h2
      calc h * (g⁻¹ * z * g) = g⁻¹ * (g * h * g⁻¹ * z) * g := by group
        _ = g⁻¹ * (z * (g * h * g⁻¹)) * g := by rw [h2]
        _ = (g⁻¹ * z * g) * h := by group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

theorem ggOTwoPrime_map_conj (g : G) (Y : Subgroup G) :
    (ggOTwoPrime Y).map (MulAut.conj g).toMonoidHom =
      ggOTwoPrime (Y.map (MulAut.conj g).toMonoidHom) := by
  rw [ggOTwoPrime, ggOTwoPrime, MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    exact ⟨⟨y, hyY, rfl⟩, k, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [conj_pow, hk, mul_one, mul_inv_cancel]⟩
  · rintro ⟨hyY, k, hk⟩
    obtain ⟨w, hwY, hwy⟩ := Subgroup.mem_map.mp hyY
    refine ⟨w, ⟨hwY, k, ?_⟩, hwy⟩
    have h1 : (g * w * g⁻¹) ^ (2 ^ k) = 1 := by
      have h2 : ((MulAut.conj g).toMonoidHom w) ^ (2 ^ k) = 1 := by
        rw [hwy]; exact hk
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h2
    rw [conj_pow] at h1
    calc w ^ (2 ^ k) = g⁻¹ * (g * w ^ (2 ^ k) * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem ggHyperplane_map_conj {Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r : MulAut ↥Bs) :
    (ggHyperplane Bs r).map (MulAut.conj g).toMonoidHom = ggHyperplane Bs (a * r * a⁻¹) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := Subgroup.mem_map.mp hz
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hy
    have hrb : r b = b := hb
    refine Subgroup.mem_map.mpr ⟨a b, ?_, ?_⟩
    · change (a * r * a⁻¹) (a b) = a b
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, hrb]
    · rw [Subgroup.coe_subtype, ha b, ← hzy, ← hby]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_subtype]
  · intro hz
    obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.mp hz
    have hrc : (a * r * a⁻¹) c = c := hc
    refine Subgroup.mem_map.mpr ⟨((a⁻¹ c : ↥Bs) : G), ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨a⁻¹ c, ?_, rfl⟩
      change r (a⁻¹ c) = a⁻¹ c
      have hconj := congrArg (fun x : ↥Bs => a⁻¹ x) hrc
      simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using hconj
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← ha (a⁻¹ c), MulAut.apply_inv_self]
      exact hcz

theorem ggRankOne_map_conj {Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r : MulAut ↥Bs) :
    (ggRankOne Bs r).map (MulAut.conj g).toMonoidHom = ggRankOne Bs (a * r * a⁻¹) := by
  rw [ggRankOne, ggRankOne, ggOTwoPrime_map_conj, ggMap_conj_centralizer,
    ggHyperplane_map_conj ha r]

theorem ggRankOneIn_map_conj {X Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r : MulAut ↥Bs) :
    (ggRankOneIn X Bs r).map (MulAut.conj g).toMonoidHom =
      ggRankOneIn (X.map (MulAut.conj g).toMonoidHom) Bs (a * r * a⁻¹) := by
  rw [ggRankOneIn, ggRankOneIn, ggOTwoPrime_map_conj,
    Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ggMap_conj_centralizer,
    ggHyperplane_map_conj ha r]

theorem ggRankOnePerf_map_conj {Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r : MulAut ↥Bs) :
    (ggRankOnePerf Bs r).map (MulAut.conj g).toMonoidHom = ggRankOnePerf Bs (a * r * a⁻¹) := by
  rw [ggRankOnePerf, ggRankOnePerf, CFSG.Quasithin.map_perfectCore, ggMap_conj_centralizer,
    ggHyperplane_map_conj ha r]

theorem mem_ggRankOnePerf_conj_iff {Bs : Subgroup G} {g : G} {a : MulAut ↥Bs}
    (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) (r : MulAut ↥Bs) (s : G) :
    g * s * g⁻¹ ∈ ggRankOnePerf Bs (a * r * a⁻¹) ↔ s ∈ ggRankOnePerf Bs r := by
  rw [← ggRankOnePerf_map_conj ha r]
  rw [show g * s * g⁻¹ = (MulAut.conj g).toMonoidHom s by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]]
  exact Subgroup.mem_map_iff_mem (MulAut.conj g).injective

theorem exists_ggRankOnePerf_conj_of_mem_ggAutomizer {X Bs : Subgroup G} {a : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer X Bs) (r : MulAut ↥Bs) :
    ∃ g ∈ X, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (ggRankOnePerf Bs r).map (MulAut.conj g).toMonoidHom = ggRankOnePerf Bs (a * r * a⁻¹) := by
  obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  exact ⟨g, hgX, hgN, ggRankOnePerf_map_conj hg r⟩

theorem exists_ggRankOneIn_conj_of_mem_ggAutomizer {X Bs : Subgroup G} {a : MulAut ↥Bs}
    (ha : a ∈ ggAutomizer X Bs) (r : MulAut ↥Bs) :
    ∃ g ∈ X, g ∈ Subgroup.normalizer (Bs : Set G) ∧
      (ggRankOneIn X Bs r).map (MulAut.conj g).toMonoidHom = ggRankOneIn X Bs (a * r * a⁻¹) := by
  obtain ⟨g, hgX, hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  refine ⟨g, hgX, hgN, ?_⟩
  rw [ggRankOneIn_map_conj hg r]
  have hX : X.map (MulAut.conj g).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
  rw [hX]

end

end CFSG.StandardType
