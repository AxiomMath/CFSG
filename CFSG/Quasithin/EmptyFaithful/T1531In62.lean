module

public import CFSG.Quasithin.EmptyFaithful.T1531Geom
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem Z_eq_zpowers (h : Hyp153 G T Mc M) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz1 : z ≠ 1) : quasithinOmegaOneCenter T = Subgroup.zpowers z := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [h.lemma_15_3_2_two.2]
  by_contra hlt
  push Not at hlt
  have h1 : Nat.card (Subgroup.zpowers z) ≤ 1 := by omega
  have h2 : Subgroup.zpowers z = ⊥ :=
    Subgroup.card_eq_one.mp (le_antisymm h1 Nat.card_pos)
  apply hz1
  have hz' : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
  rw [h2] at hz'
  exact Subgroup.mem_bot.mp hz'

theorem mem_Mc_of_conj_eq (h11 : StageLemma14111) (h : Hyp153 G T Mc M) {z a : G}
    (hz : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (ha : a * z * a⁻¹ = z) : a ∈ Mc := by
  rw [Hyp153.lemma_15_3_4 h11 h, Z_eq_zpowers h hz hz1, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  rw [Set.mem_singleton_iff.mp hy]
  exact (mul_inv_eq_iff_eq_mul.mp ha).symm

theorem conjSubgroup_VZ_mul (h : Hyp153 G T Mc M) {m : G} (hm : m ∈ M) (a : G) :
    conjSubgroup (VZ T M) (m * a) = conjSubgroup (VZ T M) a := by
  rw [← conjSubgroup_conjSubgroup, conjSubgroup_eq_iff_mem_normalizer.2 (h.le_normalizer hm)]

theorem transitive_153 (h11 : StageLemma14111) (h : Hyp153 G T Mc M) (r46 : Res15346 T M V₁ V₂)
    {g₁ g₂ : G} (h₁ : quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) g₁)
    (h₂ : quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) g₂) :
    ∃ c ∈ Mc, conjSubgroup (conjSubgroup (VZ T M) g₁) c = conjSubgroup (VZ T M) g₂ := by
  obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_Z h
  have key : ∀ g : G, quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) g →
      ∃ m ∈ M, m⁻¹ * g ∈ Mc := fun g hg => by
    have hzg : g * z * g⁻¹ ∈ VZ T M := mem_conjSubgroup_iff.mp (hg hz)
    obtain ⟨m, hm, e⟩ := r46.fusion z (h.Z_le_VZ hz) g hzg
    refine ⟨m, hm, mem_Mc_of_conj_eq h11 h hz hz1 ?_⟩
    calc m⁻¹ * g * z * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * z * g⁻¹) * m := by group
      _ = m⁻¹ * (m * z * m⁻¹) * m := by rw [e]
      _ = z := by group
  obtain ⟨m₁, hm₁, ha₁⟩ := key g₁ h₁
  obtain ⟨m₂, hm₂, ha₂⟩ := key g₂ h₂
  refine ⟨(m₁⁻¹ * g₁)⁻¹ * (m₂⁻¹ * g₂), Mc.mul_mem (Mc.inv_mem ha₁) ha₂, ?_⟩
  rw [conjSubgroup_conjSubgroup]
  have e1 : g₁ * ((m₁⁻¹ * g₁)⁻¹ * (m₂⁻¹ * g₂)) = m₁ * (m₂⁻¹ * g₂) := by group
  rw [e1, conjSubgroup_VZ_mul h hm₁]
  have e2 : g₂ = m₂ * (m₂⁻¹ * g₂) := by group
  conv_rhs => rw [e2]
  rw [conjSubgroup_VZ_mul h hm₂]

theorem commutes_153 (h11 : StageLemma14111) (c : Ctx153 G T Mc M V₁ V₂ t)
    (r46 : Res15346 T M V₁ V₂) (r50 : Res15350 T M) {g : G}
    (hg : VZ T M ⊓ conjSubgroup (VZ T M) g ≠ ⊥) : ⁅VZ T M, conjSubgroup (VZ T M) g⁆ = ⊥ := by
  have hMN := c.hyp.le_normalizer
  have hab : ∀ a ∈ VZ T M, ∀ b ∈ VZ T M, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm c.hyp.elemAbelian ha hb
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
  by_cases hgM : g ∈ M
  · have hVg : conjSubgroup (VZ T M) g = VZ T M :=
      conjSubgroup_eq_iff_mem_normalizer.2 (hMN hgM)
    rw [hVg] at hb
    exact (hab a ha b hb).symm
  · have hts := r46.totSingular_inter g hgM
    obtain ⟨w, hwA, hw1⟩ : ∃ w ∈ VZ T M ⊓ conjSubgroup (VZ T M) g, w ≠ 1 := by
      obtain ⟨w, hw⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hg
      exact ⟨w.1, w.2, fun e => hw (Subtype.ext e)⟩
    have hw₁ : w ∉ V₁ := fun h1 => hw1 (by
      have : w ∈ (VZ T M ⊓ conjSubgroup (VZ T M) g) ⊓ V₁ := ⟨hwA, h1⟩
      rw [hts.2.1, Subgroup.mem_bot] at this
      exact this)
    have hw₂ : w ∉ V₂ := fun h1 => hw1 (by
      have : w ∈ (VZ T M ⊓ conjSubgroup (VZ T M) g) ⊓ V₂ := ⟨hwA, h1⟩
      rw [hts.2.2, Subgroup.mem_bot] at this
      exact this)
    obtain ⟨z, hz, hz1⟩ := exists_ne_one_mem_Z c.hyp
    have hzs := not_mem_V₁_V₂_of_mem_Z c.hyp c.decomp hz hz1
    obtain ⟨m, hm, hmw⟩ := exists_conj_singular c.hyp c.decomp ⟨hwA.1, hw₁, hw₂⟩
      ⟨c.hyp.Z_le_VZ hz, hzs.1, hzs.2⟩
    have hZg : quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) (g * m⁻¹) := by
      rw [Z_eq_zpowers c.hyp hz hz1, Subgroup.zpowers_le, mem_conjSubgroup_iff]
      have e : g * m⁻¹ * z * (g * m⁻¹)⁻¹ = g * w * g⁻¹ := by rw [← hmw]; group
      rw [e]
      exact mem_conjSubgroup_iff.mp hwA.2
    have hZ1 : quasithinOmegaOneCenter T ≤ conjSubgroup (VZ T M) 1 := by
      rw [conjSubgroup_one]
      exact c.hyp.Z_le_VZ
    obtain ⟨c', hc', hcc⟩ := transitive_153 h11 c.hyp r46 hZg hZ1
    rw [conjSubgroup_one] at hcc
    have ha' : m * a * m⁻¹ ∈ VZ T M := (Subgroup.mem_normalizer_iff.mp (hMN hm) a).mp ha
    have hb' : m * b * m⁻¹ ∈ conjClosure (VZ T M) Mc := by
      have hbg : g * m⁻¹ * (m * b * m⁻¹) * (g * m⁻¹)⁻¹ ∈ VZ T M := by
        have e : g * m⁻¹ * (m * b * m⁻¹) * (g * m⁻¹)⁻¹ = g * b * g⁻¹ := by group
        rw [e]
        exact mem_conjSubgroup_iff.mp hb
      have e : c' * (c'⁻¹ * (m * b * m⁻¹) * c') * c'⁻¹ = m * b * m⁻¹ := by group
      have hx : c'⁻¹ * (m * b * m⁻¹) * c' ∈ VZ T M := by
        rw [← hcc, mem_conjSubgroup_iff, e]
        exact mem_conjSubgroup_iff.mpr hbg
      have := mem_conjClosure hc' hx
      rwa [e] at this
    have hcomm := r50 Mc (isHTM153_mc c) (m * a * m⁻¹) (le_conjClosure (VZ T M) Mc ha')
      (m * b * m⁻¹) hb'
    calc b * a = m⁻¹ * (m * b * m⁻¹ * (m * a * m⁻¹)) * m := by group
      _ = m⁻¹ * (m * a * m⁻¹ * (m * b * m⁻¹)) * m := by rw [hcomm]
      _ = a * b := by group

theorem stage15362 (h11 : StageLemma14111) : Stage15362 :=
  fun _ _ _ _ _ _ _ _ _ c _ r46 r50 =>
    ⟨fun _ _ h₁ h₂ => transitive_153 h11 c.hyp r46 h₁ h₂,
      fun _ hg => commutes_153 h11 c r46 r50 hg⟩

end CFSG.Quasithin
