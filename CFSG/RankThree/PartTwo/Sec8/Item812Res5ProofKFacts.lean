module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res4ProofTools
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofA9
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofSp62
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.RankThree.PartTwo.Sec8.Item812Res5ProofWreath

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG.RankThree.PartTwo.Sec4.Item434Kit Subgroup

namespace Item812Res5

structure WreathSylow (H : Type*) [Group H] [Finite H] : Prop where
  out : ∃ (z : Fin 3 → H) (t : H), WreathFacts z t ∧
    Nat.card (wreathW z t) = 3 ^ (Nat.card H).factorization 3 ∧
    Nat.card (wreathW z t) = 81 ∧ ∃ k : H, k * t * k⁻¹ ∈ baseA z

theorem wreathSylow_A9 : WreathSylow (alternatingGroup (Fin 9)) :=
  ⟨⟨zA9, tA9, wreathFacts_A9, card_wreathW_A9_eq_pow, card_wreathW_A9, kA9,
    kA9_conj_mem_baseA⟩⟩

theorem wreathSylow_H6 :
    WreathSylow CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two.H6 :=
  ⟨⟨Sec4.Item434SmallTwoIII.zH, Sec4.Item434SmallTwoIII.tH,
    Sec4.Item434SmallTwoIII.wreathFacts_zH, card_wreathW_zH_eq_pow,
    Sec4.Item434SmallTwoIII.card_wreathW_zH, kH6, kH6_conj_mem_baseA⟩⟩

variable {H : Type*} [Group H] [Finite H]

theorem WreathSylow.card_inf_centralizer_le (hH : WreathSylow H) {M : Type*} [Group M]
    (e : M ≃* H) {S E : Subgroup M} (hS : IsPGroup 3 S) (hES : E ≤ S)
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {y : M} (hyS : y ∈ S)
    (hyE : y ∉ E) : Nat.card (E ⊓ Subgroup.centralizer {y} : Subgroup M) ≤ 3 := by
  obtain ⟨z, t, hf, hW, h81, -⟩ := hH.out
  set f : M →* H := e.toMonoidHom with hfdef
  have hfinj : Function.Injective f := e.injective
  have hyE' : f y ∉ E.map f := by
    rintro ⟨x, hx, hxy⟩
    exact hyE (hfinj hxy ▸ hx)
  have h3 := card_inf_centralizer_le_three hf hW h81 (hS.map f) (Subgroup.map_mono hES)
    (isElemAbelian_map_hom f hE) (by rw [Subgroup.card_map_of_injective hfinj, hE27])
    ⟨y, hyS, rfl⟩ hyE'
  have hle : (E ⊓ Subgroup.centralizer {y} : Subgroup M).map f ≤
      E.map f ⊓ Subgroup.centralizer {f y} := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE, hxy⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨⟨x, hxE, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hxy ⊢
    rw [← map_mul, ← map_mul, hxy]
  calc Nat.card (E ⊓ Subgroup.centralizer {y} : Subgroup M)
      = Nat.card ((E ⊓ Subgroup.centralizer {y} : Subgroup M).map f) :=
        (Subgroup.card_map_of_injective hfinj).symm
    _ ≤ Nat.card (E.map f ⊓ Subgroup.centralizer {f y} : Subgroup H) :=
        Subgroup.card_le_of_le hle
    _ ≤ 3 := h3

theorem WreathSylow.exists_conj_mem (hH : WreathSylow H) {M : Type*} [Group M] (e : M ≃* H)
    {E : Subgroup M} (hE : CFSG.Assembly.IsElemAbelian 3 E) (hE27 : Nat.card E = 27) {y : M}
    (hy : y ^ 3 = 1) : ∃ g : M, g * y * g⁻¹ ∈ E := by
  obtain ⟨z, t, hf, hW, h81, k, hk⟩ := hH.out
  set f : M →* H := e.toMonoidHom with hfdef
  have hfinj : Function.Injective f := e.injective
  obtain ⟨g', hg'⟩ := exists_conj_mem_of_conj_t hf hW h81 hk (isElemAbelian_map_hom f hE)
    (by rw [Subgroup.card_map_of_injective hfinj, hE27]) (y := f y)
    (by rw [← map_pow, hy, map_one])
  refine ⟨e.symm g', ?_⟩
  obtain ⟨x, hx, hxe⟩ := hg'
  have hfx : f (e.symm g' * y * (e.symm g')⁻¹) = g' * f y * g'⁻¹ := by
    simp [hfdef]
  rw [← hfx] at hxe
  exact hfinj hxe ▸ hx

end Item812Res5

open Item812Res5

theorem kF812WreathCent_holds : KF812WreathCent := by
  intro M _ hM S hS E hES hE hE27 y hyS hyE
  rcases hM with h9 | h6
  · obtain ⟨e⟩ := h9
    exact wreathSylow_A9.card_inf_centralizer_le e hS hES hE hE27 hyS hyE
  · obtain ⟨e⟩ := h6
    exact wreathSylow_H6.card_inf_centralizer_le (e.trans Sec4.Item434SmallTwoIII.sp62Equiv) hS
      hES hE hE27 hyS hyE

theorem kF812E27Fuse_holds : KF812E27Fuse := by
  intro M _ hM E hE hE27 y hy
  rcases hM with h9 | h6
  · obtain ⟨e⟩ := h9
    exact wreathSylow_A9.exists_conj_mem e hE hE27 hy
  · obtain ⟨e⟩ := h6
    exact wreathSylow_H6.exists_conj_mem (e.trans Sec4.Item434SmallTwoIII.sp62Equiv) hE hE27 hy

end CFSG.RankThree.PartTwo.Sec8
