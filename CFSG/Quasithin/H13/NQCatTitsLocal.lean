module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLattice
public import CFSG.Walter.AStar.Subnormal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Quasithin CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat

theorem eq_top_or_isSolvable_of_sylow_le
    {Y : Type} [Group Y] [Finite Y] (e : Y ≃* titsD)
    (P : Sylow 2 Y) {M : Subgroup Y} (hPM : (P : Subgroup Y) ≤ M) :
    M = ⊤ ∨ Group.IsSolvable M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS2, hSi⟩ : IsPGroup 2 titsFlagStab ∧ ¬ 2 ∣ titsFlagStab.index := by
    refine ⟨isSylowTwoOf_flagStab.2.1, ?_⟩
    have := isSylowTwoOf_flagStab.2.2
    rwa [show (titsFlagStab.subgroupOf ⊤).index = titsFlagStab.index from
      Subgroup.relIndex_top_right titsFlagStab] at this
  have hU' : IsPGroup 2 ((P : Subgroup Y).map e.toMonoidHom) := P.isPGroup'.map _
  have hU'i : ¬ 2 ∣ ((P : Subgroup Y).map e.toMonoidHom).index := by
    have h3 : ((P : Subgroup Y).map e.toMonoidHom).index = (P : Subgroup Y).index :=
      Subgroup.index_map_equiv _ e
    rw [h3]
    exact P.not_dvd_index
  obtain ⟨m, hm⟩ := exists_conj_sylow hS2 hSi hU' hU'i
  let ψ : Y ≃* titsD := e.trans (MulAut.conj m⁻¹)
  have hUψ : titsFlagStab.comap ψ.toMonoidHom = P := by
    ext x
    have hx : x ∈ (P : Subgroup Y) ↔ e x ∈ (P : Subgroup Y).map e.toMonoidHom :=
      ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, hyx⟩ => by rwa [← e.injective hyx]⟩
    rw [hx, hm]
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, ψ, MulEquiv.trans_apply,
      MulAut.conj_apply, inv_inv]
  rcases lattice_comap ψ tits_overgroups M (hUψ ▸ hPM) with h | h | h | h
  · right
    rw [h, hUψ]
    have := P.isPGroup'.isNilpotent
    infer_instance
  · exact Or.inr (h ▸ solvable_comap_equiv ψ _ solvable_titsPointStab)
  · exact Or.inr (h ▸ solvable_comap_equiv ψ _ solvable_titsLineStab)
  · exact Or.inl h

theorem Tits_actual_Sylow_local_component_equality
    {X : Type} [Group X] [Finite X]
    (T : Sylow 2 X) {K : Subgroup X} (hKs : IsSimpleGroup ↥K)
    (_hKna : ∃ a b : ↥K, a * b ≠ b * a) (hKsub : K.IsSubnormal) (e : ↥K ≃* titsD)
    {B : Subgroup X} (hBK : B ≤ K) (hB : B ∈ cComp (B ⊔ (T : Subgroup X))) :
    B = K ∧ (T : Subgroup X) ⊓ normalizer (K : Set X) ≤
      (T : Subgroup X) ⊓ normalizer (B : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal T hKsub
  have hBL : B ≤ (B ⊔ (T : Subgroup X)) ⊓ K := le_inf le_sup_left hBK
  have hBcL : B ∈ cComp ((B ⊔ (T : Subgroup X)) ⊓ K) := cComp_mem_of_le hB hBL inf_le_left
  have hPL : (P : Subgroup ↥K) ≤ ((B ⊔ (T : Subgroup X)) ⊓ K).subgroupOf K := by
    intro x hx
    rw [mem_subgroupOf]
    have h1 : (x : X) ∈ (P : Subgroup ↥K).map K.subtype := ⟨x, hx, rfl⟩
    rw [hP] at h1
    exact ⟨mem_sup_right h1.1, h1.2⟩
  have hBeq : B = K := by
    rcases eq_top_or_isSolvable_of_sylow_le e P hPL with htop | hsolv
    ·
      have hLK : (B ⊔ (T : Subgroup X)) ⊓ K = K :=
        le_antisymm inf_le_right (Subgroup.subgroupOf_eq_top.mp htop)
      rw [hLK] at hBcL
      have hc := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hBcL)
      rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hKs hc.2.2.1 with hbot | htop'
      · exact absurd hbot hc.1
      · exact le_antisymm hBK (Subgroup.subgroupOf_eq_top.mp htop')
    · exfalso
      apply not_isSolvable_of_mem_cComp hBcL
      have hle : (B ⊔ (T : Subgroup X)) ⊓ K ≤ K := inf_le_right
      exact Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom.comp (Subgroup.inclusion hBL))
        ((Subgroup.subgroupOfEquivOfLe hle).symm.injective.comp (Subgroup.inclusion_injective hBL))
  refine ⟨hBeq, ?_⟩
  rw [hBeq]

end CFSG.Quasithin.H13.NQCat
