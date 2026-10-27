module

public import CFSG.Quasithin.Vol2.Ch4Sec2T425G
public import CFSG.Quasithin.Vol2.Ch4Sec2T425C27Z
public import CFSG.Quasithin.Vol2.Ch4Sec2T425D

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem not_isSolvable_of_quasisimple {L : Subgroup G}
    (hL : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) : ¬ Group.IsSolvable L := by
  intro hs
  set Q := ↥L ⧸ CFSG.pCore 2 ↥L
  have hQs : Group.IsSolvable Q := inferInstance
  have hnt : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    obtain ⟨a, b, hab⟩ := hL.2.2
    have : Subsingleton (Q ⧸ Subgroup.center Q) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (Subgroup.center Q))
    exact hab (Subsingleton.elim _ _)
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne (Group.isPerfect_def.mp hL.1)

namespace Set425

variable {T M L Mm I H : Subgroup G} (s : Set425 G T M L Mm I H)
include s

theorem inf_le_normalizer_conj (c : Inp425 G) {h : G} (hh : h ∈ H) :
    H ⊓ M ≤ Subgroup.normalizer ((L.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
  intro x hx
  have hy : h⁻¹ * x * h ∈ H ⊓ M := by
    have := (Subgroup.mem_normalizer_iff.mp (s.le_normalizer_inf c (H.inv_mem hh)) x).mp hx
    simpa using this
  rw [s.inf_eq c] at hy
  rw [← Subgroup.map_equiv_normalizer_eq L (MulAut.conj h)]
  refine ⟨h⁻¹ * x * h, hy.2, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

theorem false (c : Inp425 G) (hC27 : ASC27Statement G) : False := by
  obtain ⟨K, hK, hc, hq, hKH⟩ := s.exists_K c
  obtain ⟨h, hh, hhM⟩ := s.exists_h
  obtain ⟨hJK, hMK, hrank⟩ := s.lemma_4_2_10 c hK hKH hh hhM
  have hLJ : Nat.card ↥(L.map (MulAut.conj h).toMonoidHom) = Nat.card L :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  refine T425C27.false_of_c27_normal_nonsolvable hC27 s.hypC23 hK hq hc
    (fun hle => hKH (hle.trans inf_le_left)) (((pCoreOf_le 2 _).trans inf_le_right).trans hMK)
    (le_inf ((s.conj_h c hh hhM).2.2.trans (s.H0_le c)) hJK)
    (inf_le_left.trans (s.inf_le_normalizer_conj c hh)) (fun hs => ?_)
    (fun p hp hp2 hpJ => hrank p hp hp2 (hLJ ▸ hpJ))
  apply not_isSolvable_of_quasisimple s.hyp.quasisimple
  exact Group.isSolvable_of_isSolvable_injective
    (f := (L.equivMapOfInjective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective).toMonoidHom)
    (MulEquiv.injective _)

end Set425

theorem thm4_2_5_of (hin : ∀ (G : Type) [Group G] [Finite G], Inp425 G)
    (hC27 : ∀ (G : Type) [Group G] [Finite G], ASC27Statement G) : Thm4_2_5 := by
  intro G _ _ T M L Mm I H hyp hIn hne hle
  exact Set425.false ⟨hyp, hIn, hne, hle⟩ (hin G) (hC27 G)

end CFSG.Quasithin.H13.Ch4
