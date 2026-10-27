module

public import CFSG.Quasithin.Vol2.Ch10SecD12S
public import CFSG.Quasithin.Vol2.Ch10SecD12R

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem data_five (hF : Fact12WW) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h : Hyp10 G T L I) (h5 : Case10_1_1Five T L I)
    (hc : fsuCVM T L I = ⊥) : Data10212 T L I 6 3 3 := by
  obtain ⟨hL32, s, hsT, hsL, W, hWV1, hLW, hsup, hinf, ⟨hWc, hnat⟩, -⟩ := h5
  have hV := SecA.isElemAbelian_fsuVM h
  have : IsMulCommutative ↥(fsuUL T L I) := ⟨⟨fun x y => Subtype.ext
    (show (x : G) * y = y * x from B2F.isElemAbelian_comm hV (V1_le_V x.2) (V1_le_V y.2))⟩⟩
  have hWsV1 : CFSG.conjugate W s ≤ fsuUL T L I := hsup ▸ le_sup_right
  have hW8 : Nat.card W = 8 := by
    obtain ⟨K, _, _, hK, hreal⟩ := hnat
    have := card_of_realizes_nat hreal
    rw [Subgroup.card_top, hK, Fintype.card_fin, Subgroup.card_bot] at this
    simpa using this
  have hWs8 : Nat.card ↥(CFSG.conjugate W s) = 8 := (card_conjSubgroup W s).trans hW8
  have hV64 : Nat.card ↥(fsuUL T L I) = 64 := by
    rw [← hsup, card_sup_of_comm (fun x hx y hy => B2F.isElemAbelian_comm hV (V1_le_V (hWV1 hx))
      (V1_le_V (hWsV1 hy))) hinf, hW8, hWs8]
  have hsV1 : s ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    SecA.le_normalizer_commutator (X := T1 T L)
      (inf_le_left.trans (SecA.le_normalizer_fsuVM T L I)) inf_le_right ⟨hsT, hsL⟩
  have hsiV1 : s⁻¹ ∈ Subgroup.normalizer (fsuUL T L I : Set G) :=
    (Subgroup.normalizer _).inv_mem hsV1
  have hsiL : s⁻¹ ∈ Subgroup.normalizer (L : Set G) := (Subgroup.normalizer _).inv_mem hsL
  set ι : ↥W →* ↥(fsuUL T L I) := Subgroup.inclusion hWV1 with hι
  set s' : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) ⟨s⁻¹, hsiV1⟩ with hs'
  have hcoe : ∀ (l : G) (hlN : l ∈ Subgroup.normalizer (fsuUL T L I : Set G))
      (hlW : l ∈ Subgroup.normalizer (W : Set G)) (w : ↥W),
      conjAct (fsuUL T L I) ⟨l, hlN⟩ (ι w) = ι (conjAct W ⟨l, hlW⟩ w) := by
    intro l hlN hlW w
    apply Subtype.ext
    rw [A1b.conjAct_coe]
    show l * (w : G) * l⁻¹ = ((conjAct W ⟨l, hlW⟩ w : ↥W) : G)
    rw [A1b.conjAct_coe]
  have hrel1 : ∀ x ∈ autOn L (fsuUL T L I), ∃ y ∈ autOn L W, ∀ w, x (ι w) = ι (y w) := by
    rintro _ ⟨⟨l, hlN⟩, hl, rfl⟩
    have hlL := Subgroup.mem_subgroupOf.mp hl
    exact ⟨conjAct W ⟨l, hLW hlL⟩, ⟨⟨l, hLW hlL⟩, Subgroup.mem_subgroupOf.mpr hlL, rfl⟩,
      hcoe l hlN (hLW hlL)⟩
  have hrel2 : ∀ y ∈ autOn L W, ∃ x ∈ autOn L (fsuUL T L I), ∀ w, x (ι w) = ι (y w) := by
    rintro _ ⟨⟨l, hlN⟩, hl, rfl⟩
    have hlL := Subgroup.mem_subgroupOf.mp hl
    exact ⟨conjAct (fsuUL T L I) ⟨l, L_le_normalizer_V1 hlL⟩,
      ⟨⟨l, L_le_normalizer_V1 hlL⟩, Subgroup.mem_subgroupOf.mpr hlL, rfl⟩,
      hcoe l (L_le_normalizer_V1 hlL) hlN⟩
  have hfaith : ∀ x ∈ autOn L (fsuUL T L I), (∀ w, x (ι w) = ι w) → x = 1 := by
    rintro _ ⟨⟨l, hlN⟩, hl, rfl⟩ hx
    apply A1b.conjAct_eq_one_iff.mpr
    refine faithful_five h hL32 hsL hLW hsup hnat ⟨Subgroup.mem_subgroupOf.mp hl,
      Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h1 : l * w * l⁻¹ = w := by
      have := congrArg Subtype.val (hx ⟨w, hw⟩)
      rwa [A1b.conjAct_coe] at this
    calc w * l = l * w * l⁻¹ * l := by rw [h1]
      _ = l * w := by group
  have hs'N : s' ∈ Subgroup.normalizer (autOn L (fsuUL T L I) : Set (MulAut ↥(fsuUL T L I))) :=
    Subgroup.mem_normalizer_iff.mpr (conj_mem_autOn_iff hsiL hsiV1)
  have hrange : ι.range = W.subgroupOf (fsuUL T L I) := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
  have hrange' : ι.range.map s'.toMonoidHom = (CFSG.conjugate W s).subgroupOf (fsuUL T L I) := by
    rw [hrange]
    ext v
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, SecA.mem_conjugate_iff]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [Subgroup.mem_subgroupOf] at hu
      show s * ((s' u : ↥(fsuUL T L I)) : G) * s⁻¹ ∈ W
      rw [hs', A1b.conjAct_coe]
      simpa [mul_assoc] using hu
    · intro hv
      refine ⟨⟨s * v * s⁻¹, (Subgroup.mem_normalizer_iff.mp hsV1 v).mp v.2⟩,
        Subgroup.mem_subgroupOf.mpr hv, Subtype.ext ?_⟩
      show ((s' ⟨s * v * s⁻¹, _⟩ : ↥(fsuUL T L I)) : G) = v
      rw [hs', A1b.conjAct_coe]
      group
  have hsup' : ι.range ⊔ ι.range.map s'.toMonoidHom = ⊤ := by
    rw [hrange', hrange, ← Subgroup.subgroupOf_sup hWV1 hWsV1, hsup, Subgroup.subgroupOf_self]
  have hinf' : ι.range ⊓ ι.range.map s'.toMonoidHom = ⊥ := by
    rw [hrange', hrange, eq_bot_iff]
    intro v hv
    have h1 : (v : G) ∈ W ⊓ CFSG.conjugate W s :=
      ⟨Subgroup.mem_subgroupOf.mp hv.1, Subgroup.mem_subgroupOf.mp hv.2⟩
    rw [hinf, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  have hb := hF _ _ (SecC.sq_eq_one_fsuUL h) ι (Subgroup.inclusion_injective hWV1) _ _ hnat hrel1
    hrel2 hfaith s' hs'N hsup' hinf'
  have hr := rank_le_of_bound h37 h38 h hb
  exact data_of_bound h (by rw [hV64, card_inf_eq_one hc]; norm_num)
    (by rw [card_inf_eq_one hc]; norm_num)
    hr (by norm_num) (a_le_of_rank_le hr)

end CFSG.Quasithin.Vol2.Ch10.SecD
