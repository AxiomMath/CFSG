module

public import CFSG.Quasithin.Vol2.Ch11SecC37V5

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem g_mem_M (i : Inp37) (hTVS : FactTransvPointSL3) (hTVP : FactTransvPointSp4)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  have hTN := s.T_le_normalizer_A i hTVS hTVP hVL
  have hTM : QuasithinUnique.IsSylowTwoOf T (Subgroup.normalizer (L : Set G)) :=
    SecA.isSylowTwoOf_M s.hyp
  have hT'M : T.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (L : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    exact SecA.normalizer_fsuV_le i.h331 s.hyp (conj_mem_normalizer (hTN ht))
  have hcard : Nat.card ↥(T.map (MulAut.conj g).toMonoidHom) = Nat.card ↥T :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hT'S : QuasithinUnique.IsSylowTwoOf (T.map (MulAut.conj g).toMonoidHom)
      (Subgroup.normalizer (L : Set G)) := by
    refine ⟨hT'M, s.hyp.fsu.sylow.1.map _, ?_⟩
    have h1 := Subgroup.relIndex_mul_card (T.map (MulAut.conj g).toMonoidHom)
      (Subgroup.normalizer (L : Set G))
    have h2 := Subgroup.relIndex_mul_card T (Subgroup.normalizer (L : Set G))
    rw [inf_eq_left.mpr hT'M, hcard] at h1
    rw [inf_eq_left.mpr hTM.1] at h2
    change ¬ 2 ∣ (T.map (MulAut.conj g).toMonoidHom).relIndex (Subgroup.normalizer (L : Set G))
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)]
    exact hTM.2.2
  obtain ⟨m, hm, hmT⟩ := A4.exists_conj_of_isSylowTwoOf hTM hT'S
  have e : ∀ x : G, m⁻¹ * g * x * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * x * g⁻¹) * m := fun x => by group
  have hc : m⁻¹ * g ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [e]
    constructor
    · intro hx
      exact (hmT _).mp ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := (hmT _).mpr hx
      have h4 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      rw [← mul_left_cancel (mul_right_cancel h4)]
      exact hy
  have hcM := SecA.normalizer_T_le i.h331 s.hyp hc
  have : g = m * (m⁻¹ * g) := by group
  rw [this]
  exact Subgroup.mul_mem _ hm hcM

theorem pCore_le_centralizer_A (i : Inp37) (hTVS : FactTransvPointSL3)
    (hTVP : FactTransvPointSp4) (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (conjSubgroup (fsuV T I) g : Set G) := by
  have hgM := s.g_mem_M i hTVS hTVP hVL
  have hTN := s.T_le_normalizer_A i hTVS hTVP hVL
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := SecA.L_le_normalizer_fsuV s.hyp
  have hRT : pCoreOf 2 (L ⊔ T) ≤ T := F7.isSylowTwoOf_pCoreOf_le s.sylow_LT
  have hLR : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T))
  have hLA : L ≤ Subgroup.normalizer (conjSubgroup (fsuV T I) g : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff]
    have hgl : g * l * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hgM l).mp hl
    have e : g * (l * x * l⁻¹) * g⁻¹ = (g * l * g⁻¹) * (g * x * g⁻¹) * (g * l * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp (hLV hgl) _
  have hA1 : conjSubgroup (fsuV T I) g ≠ ⊥ := by
    intro h
    apply SecA.fsuV_ne_bot s.hyp
    rw [eq_bot_iff]
    intro v hv
    have : g⁻¹ * v * g ∈ conjSubgroup (fsuV T I) g := by
      rw [mem_conjSubgroup_iff]
      have e : g * (g⁻¹ * v * g) * g⁻¹ = v := by group
      rw [e]
      exact hv
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    calc v = g * (g⁻¹ * v * g) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hAT := SecB.inf_centralizer_ne_bot s.hyp.fsu.sylow.1 s.hAT hTN hA1
  have hAR : conjSubgroup (fsuV T I) g ⊓ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ≠ ⊥ := by
    intro h
    apply hAT
    rw [eq_bot_iff, ← h]
    exact inf_le_inf_left _ (Subgroup.centralizer_le hRT)
  set J : Subgroup G := (conjSubgroup (fsuV T I) g ⊓
    Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G)).comap (MulAut.conj g⁻¹).toMonoidHom
  have hJ : ∀ x, x ∈ J ↔ g⁻¹ * x * g ∈ conjSubgroup (fsuV T I) g ⊓
      Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) := fun x => by
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hJV : J ≤ fsuV T I := fun x hx => by
    have h1 := (Subgroup.mem_inf.mp ((hJ x).mp hx)).1
    rw [mem_conjSubgroup_iff] at h1
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [e] at h1
  have hLJ : L ≤ Subgroup.normalizer (J : Set G) := by
    intro l hl
    have hgl : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgM) l).mp hl
      simpa using this
    have hN : g⁻¹ * l * g ∈ Subgroup.normalizer ((conjSubgroup (fsuV T I) g ⊓
        Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) : Subgroup G) : Set G) :=
      F7.mem_normalizer_inf (hLA hgl) (le_normalizer_centralizer hLR hgl)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hJ, hJ]
    have e : g⁻¹ * (l * x * l⁻¹) * g =
        (g⁻¹ * l * g) * (g⁻¹ * x * g) * (g⁻¹ * l * g)⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hN _
  obtain ⟨_, hirr, -⟩ := i.h1102 G T L I n s.hyp
  rcases hirr.2.2.2.2.2 J (by rw [hVL]; exact bot_le) hJV hLJ with h | h
  · exfalso
    apply hAR
    rw [eq_bot_iff]
    intro x hx
    have h1 : g * x * g⁻¹ ∈ J := by
      rw [hJ]
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]
      exact hx
    rw [h, hVL, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [Subgroup.le_centralizer_iff]
    intro a ha
    have h1 : g * a * g⁻¹ ∈ J := h ▸ mem_conjSubgroup_iff.mp ha
    have h2 := (Subgroup.mem_inf.mp ((hJ _).mp h1)).2
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rwa [e] at h2

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
