module

public import CFSG.Quasithin.Vol2.Ch10SecKRKb
public import CFSG.Quasithin.Vol2.Ch10SecCFacts

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRK

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {Γ : Type} [Group Γ] [Finite Γ]

namespace K1Hyp

variable {H R J L V₁ : Subgroup Γ} (h : K1Hyp H R J L V₁)
include h

theorem vB : imJ J V₁ ≤ imJ J L := Subgroup.map_mono (Subgroup.comap_mono h.vle)

theorem vel_V : IsElemAbelian 2 (imJ J V₁) := by
  obtain ⟨hc, hsq⟩ := h.vel
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    have hxy : x * y = y * x := Subtype.ext (by
      have := hc.is_comm.comm (⟨x, hx⟩ : ↥V₁) ⟨y, hy⟩
      have h' := congrArg Subtype.val this
      simpa using h')
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hsq x hx)
    rw [this, map_one]

theorem B_le_normalizer_V : imJ J L ≤ Subgroup.normalizer (imJ J V₁ : Set (QJ J)) := by
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map (piJ J))
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact Subgroup.mem_normalizer_iff.mp
    (h.vn (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hs))) (x : Γ)

theorem comm_subgroupOf : ⁅V₁.subgroupOf J, L.subgroupOf J⁆ = V₁.subgroupOf J := by
  apply Subgroup.map_injective J.subtype_injective
  rw [SecB.KRP.map_commutator_subgroupOf (h.vle.trans h.le) h.le, h.vc,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (h.vle.trans h.le)]

theorem comm_V : ⁅imJ J V₁, imJ J L⁆ = imJ J V₁ := by
  rw [← Subgroup.map_commutator, h.comm_subgroupOf]

theorem V_ne_bot : imJ J V₁ ≠ ⊥ := by
  intro hV
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hV
  have hc : V₁.subgroupOf J ≤ Subgroup.center ↥J := hV.trans h.pCore_le_center
  have hb : ⁅V₁.subgroupOf J, L.subgroupOf J⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp (hc hx) y)
  rw [h.comm_subgroupOf] at hb
  exact h.v_ne_bot (SecB.KRP.eq_bot_of_subgroupOf_eq_bot (h.vle.trans h.le) hb)

theorem pCoreOf_B_le :
    pCoreOf 2 (imJ J L) ≤ Subgroup.centralizer (imJ J V₁ : Set (QJ J)) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [← map_pCore_eq_of_surjective (MonoidHom.subgroupMap_surjective _ _) isPGroup_ker_restr] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxL : ((x : ↥J) : Γ) ∈ pCoreOf 2 L := by
    rw [← SecB.KRP.map_pCoreOf_subgroupOf h.le]
    refine ⟨x, ?_, rfl⟩
    unfold pCoreOf
    exact ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨w, hw, rfl⟩
  have hc := (Subgroup.mem_centralizer_iff.mp (h.vcent hxL)) (w : Γ) hw
  show piJ J w * piJ J x = piJ J x * piJ J w
  rw [← map_mul, ← map_mul, show w * (x : ↥J) = (x : ↥J) * w from Subtype.ext hc]

theorem type_B (hM : ModCase L V₁) :
    (∃ n : ℕ, 1 < n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (ModO2 (imJ J L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)) ∨
      Nonempty (ModO2 (imJ J L) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (ModO2 (imJ J L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (ModO2 (imJ J L)) 2 n := by
  obtain ⟨_, hM⟩ := hM
  have e := h.modO2B
  rcases hM with ⟨n, hn, ⟨F, _, _, hF, ⟨f⟩⟩, -⟩ | ⟨⟨f⟩, -⟩ | ⟨⟨f⟩, -⟩ |
      ⟨n, hn, ⟨F, _, _, hF, ⟨f⟩⟩, -⟩ | ⟨⟨f⟩, -⟩ | ⟨n, hsz, -⟩
  · exact Or.inl ⟨n, hn, F, inferInstance, inferInstance, hF, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨e.trans f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f⟩))
  · exact Or.inl ⟨2 * n, by omega, F, inferInstance, inferInstance, hF, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans f⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨n, CFSG.SectionRank.suzukiModel_of_mulEquiv e hsz⟩))

end K1Hyp

end CFSG.Quasithin.Vol2.Ch10.SecC.KRK
