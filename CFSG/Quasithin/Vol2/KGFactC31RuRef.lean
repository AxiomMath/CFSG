
module


public import Certificates.Certificate7233
public import CFSG.Sporadic.Schreier.RuCenters

public section

namespace CFSG.Quasithin.KGC31.Ru

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31

section Reps

end Reps

section Facts

theorem refFacts : RefFacts := Certificates.certificate7233.1

theorem hvE : EBasis vE := refFacts.ebasis.1
theorem hv64 : EBasis v64 := refFacts.ebasis.2.1
theorem hv3 : EBasis v3 := refFacts.ebasis.2.2.1
theorem hv16 : EBasis v16 := refFacts.ebasis.2.2.2.1
theorem hv32 : EBasis v32 := refFacts.ebasis.2.2.2.2.1
theorem hvV32E : EBasis vV32E := refFacts.ebasis.2.2.2.2.2.1
theorem hvV32p : EBasis vV32p := refFacts.ebasis.2.2.2.2.2.2

theorem ruZ_mem_uE : ruZ ∈ uE := refFacts.ruZ_mem.1
theorem ruZ_mem_u64 : ruZ ∈ u64 := refFacts.ruZ_mem.2.1
theorem ruZ_mem_u3 : ruZ ∈ u3 := refFacts.ruZ_mem.2.2.1
theorem ruZ_mem_u16 : ruZ ∈ u16 := refFacts.ruZ_mem.2.2.2.1
theorem ruZ_mem_u32 : ruZ ∈ u32 := refFacts.ruZ_mem.2.2.2.2

theorem uE_le_uV32E : uE ≤ uV32E := refFacts.uE_le_uV32E

theorem uE_le_ruESub :
    uE ≤ ruESub := by
  refine refSub_le_of_forall fun i => ?_
  obtain ⟨m, hm, e⟩ := refFacts.vE_conj i
  change vE i ∈ ruE
  exact Or.inr ⟨m, hm, e.symm⟩

theorem uE_eq : uE = ruESub :=
  Subgroup.eq_of_le_of_card_ge uE_le_ruESub (by rw [card_ruESub, card_refSub hvE]; norm_num)

theorem ncard_fixSet_of_mem_uE {g : Equiv.Perm (Fin 4060)} (hg : g ∈ uE) (h1 : g ≠ 1) :
    (fixSet g).ncard = 92 :=
  refFacts.ncard_fix_uE g hg h1

theorem ncard_fixSet_of_mem_uV32E {g : Equiv.Perm (Fin 4060)} (hg : g ∈ uV32E) (hE : g ∉ uE) :
    (fixSet g).ncard = 0 :=
  refFacts.ncard_fix_uV32E g hg hE

theorem x16_mem_normalizer : x16 ∈ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) :=
  refFacts.x16_mem_normalizer

theorem ruC_le_normalizer32 : ruC ≤ Subgroup.normalizer (u32 : Set (Equiv.Perm (Fin 4060))) :=
  refFacts.ruC_le_normalizer32

theorem orderOf_xE : orderOf xE = 7 := refFacts.orderOf_eq.1

theorem orderOf_x16 : orderOf x16 = 5 := refFacts.orderOf_eq.2.1

theorem orderOf_x32 : orderOf x32 = 5 := refFacts.orderOf_eq.2.2

theorem conj_x16_not_mem_normalizer :
    g16 * x16 * g16⁻¹ ∉ Subgroup.normalizer (u16 : Set (Equiv.Perm (Fin 4060))) :=
  refFacts.conj_x16_not_mem_normalizer

theorem map_k16_u32 : u32.map (MulAut.conj k16).toMonoidHom = uV32p := by
  have hle : u32.map (MulAut.conj k16).toMonoidHom ≤ uV32p := by
    rw [show u32 = Subgroup.closure (Set.range v32) from rfl, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact refFacts.conj_k16_u32 i
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj k16).injective, card_refSub hv32,
    card_refSub hvV32p]

theorem conj64_distinct {i j : ℕ} (hi : i < 20) (hj : j < 20) (hij : i ≠ j) :
    u64.map (MulAut.conj (wG (conj64W.getD i []))).toMonoidHom ≠
      u64.map (MulAut.conj (wG (conj64W.getD j []))).toMonoidHom :=
  refFacts.conj64_distinct i hi j hj hij

end Facts

end CFSG.Quasithin.KGC31.Ru

end
