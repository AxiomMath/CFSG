module

public import CFSG.Quasithin.Vol2.Ch11SecC37V2
public import CFSG.Quasithin.Vol2.Ch11SecC37B4
public import CFSG.Quasithin.Vol2.Ch11SecC37V1
public import CFSG.Quasithin.Vol2.Ch11SecCFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem exists_point (i : Inp37) (hTVS : FactTransvPointSL3) (hTVP : FactTransvPointSp4)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {u : G} (hu : u ∈ VZ T H)
    (huA : u ∉ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G)) :
    ∃ l ∈ L, ∀ w ∈ fsuV T I, (∃ w' ∈ fsuV T I,
      w = g * u * g⁻¹ * w' * (g * u * g⁻¹)⁻¹ * w'⁻¹) ↔
        l⁻¹ * w * l ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  have hG2 := i.hKF.2.2.2
  have huN := s.VZ_le_normalizer_A i.hAS i.hF i.h1102 hG2 i.h1122 i.h1134 i.h1135 i.h1136 hu
  have hN := conj_mem_normalizer huN
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV s.hyp
  have hNL : g * u * g⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    SecA.normalizer_fsuV_le i.h331 s.hyp hN
  have hyN := conjAct_mem_normalizer_autOn (P := L) (x := ⟨g * u * g⁻¹, hN⟩) hNL
  have hu2 : u * u = 1 := by
    have := s.isElemAbelian_VZ.2 u hu
    rwa [pow_two] at this
  have hyy : conjAct (fsuV T I) ⟨g * u * g⁻¹, hN⟩ * conjAct (fsuV T I) ⟨g * u * g⁻¹, hN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨g * u * g⁻¹, hN⟩ * ⟨g * u * g⁻¹, hN⟩ :
        ↥(Subgroup.normalizer (fsuV T I : Set G))) = 1 := by
      apply Subtype.ext
      show g * u * g⁻¹ * (g * u * g⁻¹) = 1
      calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
        _ = 1 := by rw [hu2]; group
    rw [this, map_one]
  have hy1 : conjAct (fsuV T I) ⟨g * u * g⁻¹, hN⟩ ≠ 1 := by
    intro h1
    apply huA
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hga : g * a * g⁻¹ ∈ fsuV T I := mem_conjSubgroup_iff.mp ha
    have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨g * a * g⁻¹, hga⟩)
    rw [conjAct_apply_coe] at h2
    have h2' : g * u * g⁻¹ * (g * a * g⁻¹) * (g * u * g⁻¹)⁻¹ = g * a * g⁻¹ := h2
    have h3 : u * a * u⁻¹ = a := by
      calc u * a * u⁻¹ = g⁻¹ * (g * u * g⁻¹ * (g * a * g⁻¹) * (g * u * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * a * g⁻¹) * g := by rw [h2']
        _ = a := by group
    calc a * u = (u * a * u⁻¹) * u := by rw [h3]
      _ = u * a := by group
  have hcard := s.card_le_fix i.hAS i.hF i.h1102 hG2 i.h1122 i.h1134 i.h1135 i.h1136 hu hN
  obtain ⟨hc, -, -, -, hk⟩ := i.h1102 G T L I n s.hyp
  have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn s.sylow_TL hLV
  have hV2 : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV s.hyp).2 w w.2)
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ fsuV T I ⊓ Subgroup.centralizer (L : Set G) :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [hVL, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hpt : ∃ h ∈ autOn L (fsuV T I), ∀ w : ↥(fsuV T I),
      (∃ w' : ↥(fsuV T I), w = conjAct (fsuV T I) ⟨g * u * g⁻¹, hN⟩ w' * w'⁻¹) ↔
        ∀ σ ∈ autOn (T ⊓ L) (fsuV T I), σ (h⁻¹ w) = h⁻¹ w := by
    rcases hk with ⟨F, _, _, hF, -, π, hπ, -⟩ | ⟨F, _, _, hF, -, π, hπ, -⟩ |
      ⟨F, _, _, hF, ⟨e⟩, -⟩
    · rw [hZ] at hπ
      exact hTVS F n s.two_le hF ↥(fsuV T I) hV2 _ π hπ _ hS _ hyN hyy hy1 hcard
    · rw [hZ] at hπ
      exact hTVP F n s.two_le hF ↥(fsuV T I) hV2 _ π hπ _ hS _ hyN hyy hy1 hcard
    · exfalso
      have hk2 : KindG2 L (fsuV T I) n := ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩
      rcases s.kind i.h1134 with h1 | h1
      · exact SecA.kind_not_SL3_G2 hG2 s.two_le h1 hk2
      · exact SecA.kind_not_Sp4_G2 hG2 s.two_le h1 hk2
  obtain ⟨_, ⟨z, hz, rfl⟩, hpt⟩ := hpt
  have hzL : (z : G) ∈ L := Subgroup.mem_subgroupOf.mp hz
  have hinv : ∀ w : ↥(fsuV T I), (((conjAct (fsuV T I) z)⁻¹ w : ↥(fsuV T I)) : G) =
      (z : G)⁻¹ * w * z := fun w => by
    rw [← map_inv, conjAct_apply_coe, Subgroup.coe_inv, inv_inv]
  have hTLV : T ⊓ L ≤ Subgroup.normalizer (fsuV T I : Set G) := inf_le_right.trans hLV
  refine ⟨z, hzL, fun w hw => ?_⟩
  have hiff := hpt ⟨w, hw⟩
  rw [fix_autOn_iff hTLV, hinv] at hiff
  rw [← hiff]
  constructor
  · rintro ⟨w', hw', hww⟩
    refine ⟨⟨w', hw'⟩, Subtype.ext ?_⟩
    rw [Subgroup.coe_mul, conjAct_apply_coe, Subgroup.coe_inv]
    exact hww
  · rintro ⟨w', hww⟩
    refine ⟨w', w'.2, ?_⟩
    have := congrArg Subtype.val hww
    rw [Subgroup.coe_mul, conjAct_apply_coe, Subgroup.coe_inv] at this
    exact this

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
