module

public import CFSG.Quasithin.EmptyFaithful.ModGRed2
public import CFSG.Quasithin.EmptyFaithful.S146F4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.ModG CFSG.QuasithinUnique.Vol2Native.L239

theorem input14620M22_proved :
    Input14620M22 := by
  intro G _ _ K T hT hTN hK
  obtain ⟨ε⟩ := hK
  obtain ⟨E, L⟩ := m22Lat
  let ε' : KBar K ≃* Mg := ε
  let ψ₀ : ↥K →* Mg := ε'.toMonoidHom.comp (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))
  have hψ₀s : Function.Surjective ψ₀ :=
    ε'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψ₀k : ψ₀.ker = (pCoreOf 2 K).subgroupOf K := by
    ext k
    show ε' (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) k) = 1 ↔ _
    rw [map_eq_one_iff _ ε'.injective]
    exact QuotientGroup.eq_one_iff _
  have hKn : (K.subgroupOf (K ⊔ T)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff le_sup_left]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.1 ((sup_le Subgroup.le_normalizer hTN) hk) h).1 hh
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hT le_sup_left hKn.isSubnormal
  have hS2 : IsPGroup 2 ↥(((T ⊓ K).subgroupOf K).map ψ₀) := by
    refine IsPGroup.map ?_ ψ₀
    exact hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm
  have hSi : ¬ 2 ∣ (((T ⊓ K).subgroupOf K).map ψ₀).index := by
    rw [Subgroup.index_map, MonoidHom.range_eq_top_of_surjective ψ₀ hψ₀s, Subgroup.index_top,
      mul_one]
    intro h2
    exact hsyl.2.2 (h2.trans (Subgroup.index_dvd_of_le le_sup_left))
  obtain ⟨c, hc⟩ := exists_conj_of_sylow_two hS2 hSi L.sylow.1 L.sylow.2
  let ψ : ↥K →* Mg := (MulAut.conj c).toMonoidHom.comp ψ₀
  have hψs : Function.Surjective ψ := (MulAut.conj c).surjective.comp hψ₀s
  have hψk : ψ.ker = (pCoreOf 2 K).subgroupOf K := by
    rw [← hψ₀k]
    ext k
    show (MulAut.conj c) (ψ₀ k) = 1 ↔ ψ₀ k = 1
    exact map_eq_one_iff _ (MulAut.conj c).injective
  have hψS : ((T ⊓ K).subgroupOf K).map ψ = Sg := by
    rw [← hc, Subgroup.map_map]
  exact (Red.mk L hT hTN hψs hψk hψS).secExt

end CFSG.Quasithin
