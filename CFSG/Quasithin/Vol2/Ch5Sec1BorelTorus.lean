module

public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.Vol2.Ch5Sec1Facts
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section General

variable {G : Type*} [Group G]

theorem nonempty_mulEquiv_quotient_of_compl {U C N : Subgroup G} (hCN : C ⊔ U = N)
    (hCU : C ≤ Subgroup.normalizer (U : Set G)) (hinf : C ⊓ U = ⊥) :
    ∃ _ : (U.subgroupOf N).Normal, Nonempty (↥C ≃* ↥N ⧸ U.subgroupOf N) := by
  have hUN : U ≤ N := hCN ▸ le_sup_right
  have hCleN : C ≤ N := hCN ▸ le_sup_left
  have hNU : N ≤ Subgroup.normalizer (U : Set G) := hCN ▸ sup_le hCU Subgroup.le_normalizer
  have hnorm : (U.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUN).mpr hNU
  refine ⟨hnorm, ?_⟩
  let φ : ↥C →* ↥N ⧸ U.subgroupOf N :=
    (QuotientGroup.mk' (U.subgroupOf N)).comp (Subgroup.inclusion hCleN)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hc
    have hc' : (c : G) ∈ C ⊓ U := Subgroup.mem_inf.mpr ⟨c.2, hc⟩
    rw [hinf, Subgroup.mem_bot] at hc'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hc')
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hn : (n : G) ∈ U ⊔ C := by
      rw [sup_comm, hCN]
      exact n.2
    obtain ⟨u, hu, c, hc, hnuc⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hCU).mp hn
    refine ⟨⟨c, hc⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hCleN ⟨c, hc⟩) : ↥N ⧸ U.subgroupOf N) =
      QuotientGroup.mk n
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inclusion, hnuc]
    have hcN : c⁻¹ ∈ Subgroup.normalizer (U : Set G) := inv_mem (hCU hc)
    have := (Subgroup.mem_normalizer_iff.mp hcN u).mp hu
    simpa [mul_assoc] using this
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

end General

theorem l2TorusFact : L2TorusFact := by
  intro X _ _ n hn hL S C hS hCN hinf hsup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_equiv_psl_of_lieModel (by omega) hL
  have hS'p : IsPGroup 2 ↥(S.map e.toMonoidHom) := hS.2.1.map e.toMonoidHom
  have hS'i : ¬ 2 ∣ (S.map e.toMonoidHom).index := by
    have h1 : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv S e
    rw [h1, ← Subgroup.relIndex_top_right]
    exact hS.2.2
  obtain ⟨D, hDcyc, hDcard, hUD, hUDN, -⟩ :=
    CFSG.Walter.psl2_even_normalizer_sylow_two hn (hS'p.toSylow hS'i)
  have hNS : (Subgroup.normalizer (S : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) :=
    Subgroup.map_equiv_normalizer_eq S e
  have hC'N : C.map e.toMonoidHom ⊔ S.map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [← Subgroup.map_sup, hsup, hNS]
  have hC'S : C.map e.toMonoidHom ≤
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) :=
    le_sup_left.trans hC'N.le
  have hC'inf : C.map e.toMonoidHom ⊓ S.map e.toMonoidHom = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ _ e.injective, hinf, Subgroup.map_bot]
  have hDN : D ⊔ S.map e.toMonoidHom =
      Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) := by
    rw [sup_comm]
    exact hUDN
  have hDS : D ≤ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup _) : Set _) :=
    le_sup_left.trans hDN.le
  have hDinf : D ⊓ S.map e.toMonoidHom = ⊥ := by
    rw [inf_comm]
    exact hUD
  obtain ⟨_, ⟨eC⟩⟩ := nonempty_mulEquiv_quotient_of_compl hC'N hC'S hC'inf
  obtain ⟨_, ⟨eD⟩⟩ := nonempty_mulEquiv_quotient_of_compl hDN hDS hDinf
  have eCD : ↥C ≃* ↥D :=
    (C.equivMapOfInjective e.toMonoidHom e.injective).trans (eC.trans eD.symm)
  refine ⟨?_, ?_⟩
  · exact isCyclic_of_surjective eCD.symm.toMonoidHom eCD.symm.surjective
  · rw [Nat.card_congr eCD.toEquiv, hDcard]

end CFSG.Quasithin.H13
