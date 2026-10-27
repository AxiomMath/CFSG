module

public import CFSG.Quasithin.Recognition.SzR1Fam
public import CFSG.Quasithin.Recognition.SzR1Center

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace SzR1

namespace FamCtx

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω)

@[expose] noncomputable def zU (i₀ j₀ : Ω) : ↥(vBeta K1 L2 S Zs) :=
  ⟨C.cm i₀ j₀, F112J2.Zs_le_vBeta K1 L2 S Zs (C.cm_mem i₀ j₀)⟩

@[expose] noncomputable def wU (j : Ω) : ↥(vBeta K1 L2 S Zs) := ⟨C.zf j, C.zf_mem_U j⟩

theorem gramRel {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) : GramRel (C.zU i₀ j₀) C.wU where
  z_sq := Subtype.ext (C.Zs_sq (C.cm_mem i₀ j₀))
  z_comm := fun g => Subtype.ext (C.Zs_central g.2 (C.cm_mem i₀ j₀))
  w_sq := fun i => Subtype.ext (C.Vf_sq (C.zf_mem i))
  w_comm := fun i j hij' => by
    have hcm : C.cm i j = C.cm i₀ j₀ := C.cm_const hij hij'
    apply Subtype.ext
    show C.zf i * C.zf j = C.cm i₀ j₀ * (C.zf j * C.zf i)
    have h2 : C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹ = C.cm i₀ j₀ := hcm
    calc C.zf i * C.zf j
        = (C.zf i * C.zf j * (C.zf i)⁻¹ * (C.zf j)⁻¹) * (C.zf j * C.zf i) := by group
      _ = C.cm i₀ j₀ * (C.zf j * C.zf i) := by rw [h2]

theorem closure_wU {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) :
    Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have h1 : (u : G) ∈ Subgroup.closure (insert (C.cm i₀ j₀) (Set.range C.zf)) := by
    have := C.U_eq_closure (C.cm_mem i₀ j₀) (C.cm_ne_one hij)
    rw [← this]
    exact u.2
  have h2 : Subgroup.closure (insert (C.cm i₀ j₀) (Set.range C.zf)) =
      (Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU))).map
        (vBeta K1 L2 S Zs).subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_image, Set.mem_range]
    constructor
    · rintro (rfl | ⟨j, rfl⟩)
      · exact ⟨C.zU i₀ j₀, Or.inl rfl, rfl⟩
      · exact ⟨C.wU j, Or.inr ⟨j, rfl⟩, rfl⟩
    · rintro ⟨y, (rfl | ⟨j, rfl⟩), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨j, rfl⟩
  rw [h2] at h1
  obtain ⟨x, hx, hxu⟩ := h1
  have : x = u := Subtype.ext hxu
  rw [← this]
  exact hx

section Odd

variable [Fintype Ω] [DecidableEq Ω]

include C

omit [Fintype Ω] in
theorem center_dichotomy {i₀ j₀ : Ω} (hij : i₀ ≠ j₀) (l₀ : List Ω) (hl₀ : l₀.Nodup)
    (hall : ∀ i, i ∈ l₀) {x : G} (hxW : x ∈ vBeta K1 L2 S Zs)
    (hxc : ∀ u ∈ vBeta K1 L2 S Zs, x * u = u * x) :
    (∃ b : ℕ, x = (C.cm i₀ j₀) ^ b) ∨
      ∃ b : ℕ, x = (C.cm i₀ j₀) ^ b * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) := by
  have hG := C.gramRel hij
  have hz : C.zU i₀ j₀ ≠ 1 := fun h => C.cm_ne_one hij (congrArg Subtype.val h)
  have hclos : ∀ g : ↥(vBeta K1 L2 S Zs),
      g ∈ Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    intro g
    rw [C.closure_wU hij]
    exact Subgroup.mem_top g
  have hxi : ∀ i, (⟨x, hxW⟩ : ↥(vBeta K1 L2 S Zs)) * C.wU i = C.wU i * ⟨x, hxW⟩ :=
    fun i => Subtype.ext (hxc _ (C.zf_mem_U i))
  have hzU : (C.zU i₀ j₀ : G) = C.cm i₀ j₀ := rfl
  rcases hG.central_mem_closure hz l₀ hl₀ hall (hclos _) hxi with ⟨b, hb⟩ | ⟨b, hb⟩
  · left
    exact ⟨b, by simpa [hzU] using congrArg Subtype.val hb⟩
  · right
    exact ⟨b, by simpa [hzU] using congrArg Subtype.val hb⟩

theorem centralizes_y {i₀ j₀ : Ω} (hodd : Odd (Fintype.card Ω)) (hij : i₀ ≠ j₀) (l₀ : List Ω)
    (hl₀ : l₀.Nodup) (hall : ∀ i, i ∈ l₀)
    (hyZ : ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) ∉ Zs) :
    ∀ k ∈ K1, k * ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) =
      ((gprod C.wU l₀ : ↥(vBeta K1 L2 S Zs)) : G) * k := by
  have hG := C.gramRel hij
  have hclos : ∀ g : ↥(vBeta K1 L2 S Zs),
      g ∈ Subgroup.closure (insert (C.zU i₀ j₀) (Set.range C.wU)) := by
    intro g
    rw [C.closure_wU hij]
    exact Subgroup.mem_top g
  obtain ⟨yU, hyU⟩ : ∃ yU : ↥(vBeta K1 L2 S Zs), yU = gprod C.wU l₀ := ⟨_, rfl⟩
  rw [← hyU] at hyZ ⊢
  have hyUc : ∀ g : ↥(vBeta K1 L2 S Zs), g * yU = yU * g := fun g => by
    rw [hyU]
    exact hG.commute_gprod_univ_closure hodd l₀ hl₀ hall (hclos g)
  have hzU : (C.zU i₀ j₀ : G) = C.cm i₀ j₀ := rfl
  have hz0 : C.cm i₀ j₀ ∈ Zs := C.cm_mem i₀ j₀
  have hzpow : ∀ b : ℕ, (C.cm i₀ j₀) ^ b ∈ Zs := fun b => Zs.pow_mem hz0 b
  have hKZ : ∀ k ∈ K1, ∀ s ∈ Zs, k * s = s * k := fun k hk s hs =>
    (Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) s hs).symm
  refine centralizes_of_perfect (K := K1) (Zs := Zs) (y := (yU : G))
    (perfect_of_mem_cComp C.h.cComp_mem) hKZ ?_ ?_
  · intro s hs t ht
    exact C.Zs_central (F112J2.Zs_le_vBeta K1 L2 S Zs hs) ht
  · intro k hk
    have hkN : k ∈ Subgroup.normalizer (vBeta K1 L2 S Zs : Set G) :=
      le_normalizer_conjClosure (conjClosure Zs L2) (K1 ⊔ S) (Subgroup.mem_sup_left hk)
    have huW : k * (yU : G) * k⁻¹ ∈ vBeta K1 L2 S Zs :=
      (Subgroup.mem_normalizer_iff.mp hkN (yU : G)).mp yU.2
    have hucen : ∀ v ∈ vBeta K1 L2 S Zs,
        (k * (yU : G) * k⁻¹) * v = v * (k * (yU : G) * k⁻¹) := by
      intro v hv
      have hv' : k⁻¹ * v * k ∈ vBeta K1 L2 S Zs :=
        (Subgroup.mem_normalizer_iff''.mp hkN v).mp hv
      have h1 : k⁻¹ * v * k * (yU : G) = (yU : G) * (k⁻¹ * v * k) :=
        congrArg Subtype.val (hyUc ⟨k⁻¹ * v * k, hv'⟩)
      calc (k * (yU : G) * k⁻¹) * v
          = k * ((yU : G) * (k⁻¹ * v * k)) * k⁻¹ := by group
        _ = k * (k⁻¹ * v * k * (yU : G)) * k⁻¹ := by rw [h1]
        _ = v * (k * (yU : G) * k⁻¹) := by group
    rcases C.center_dichotomy hij l₀ hl₀ hall huW hucen with ⟨c, hc⟩ | ⟨c, hc⟩
    · exfalso
      apply hyZ
      have h2 : (yU : G) = (C.cm i₀ j₀) ^ c := by
        calc (yU : G) = k⁻¹ * (k * (yU : G) * k⁻¹) * k := by group
          _ = k⁻¹ * (C.cm i₀ j₀) ^ c * k := by rw [hc]
          _ = (C.cm i₀ j₀) ^ c := by
              rw [hKZ k⁻¹ (K1.inv_mem hk) _ (hzpow c)]
              group
      rw [h2]
      exact hzpow c
    · rw [← hyU] at hc
      exact ⟨(C.cm i₀ j₀) ^ c, hzpow c, hc⟩

end Odd

end FamCtx

end SzR1

end CFSG.Quasithin
