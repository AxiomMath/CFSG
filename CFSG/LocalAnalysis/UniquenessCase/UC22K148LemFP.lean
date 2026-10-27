module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Sub
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.RGroupExclusionGL
import CFSG.RankThree.FFModules.FixSubConj
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Red

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem cenOn_commOn_sup_fixSub_eq_bot (hρ : Function.Injective ρ) (hO : CFSG.pCore 2 G = ⊥)
    {M K : Subgroup G} (hM : M.Normal) (hK : K.Normal) (hc : ∀ m ∈ M, ∀ k ∈ K, m * k = k * m) :
    cenOn ρ K (commOn ρ M ⊤ ⊔ fixSub ρ M) = ⊥ := by
  have hMN : (⊤ : Subgroup G) ≤ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hM]
  have hXinv : ∀ g : G, ∀ x ∈ commOn ρ M ⊤ ⊔ fixSub ρ M, ρ g x ∈ commOn ρ M ⊤ ⊔ fixSub ρ M :=
    fun g x hx => by
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup ((invariant_commOn_top hMN).2 g (Subgroup.mem_top g) y hy)
        (rep_apply_mem_fixSub_of_normal ρ hM g hz)
  have hnorm : (cenOn ρ K (commOn ρ M ⊤ ⊔ fixSub ρ M)).Normal :=
    ⟨fun k hk g => ⟨hK.conj_mem k hk.1 g, fun x hx => by
      rw [glRep_mul_apply, glRep_mul_apply, hk.2 _ (hXinv g⁻¹ x hx), glRep_apply_inv]⟩⟩
  have hfix : ∀ k ∈ cenOn ρ K (commOn ρ M ⊤ ⊔ fixSub ρ M), ∀ v : V, ρ k v - v ∈ fixSub ρ M :=
    fun k hk v => mem_fixSub.2 fun m hm => by
      have h1 : ρ k (ρ m v - v) = ρ m v - v :=
        hk.2 _ (Submodule.mem_sup_left (sub_mem_commOn hm Submodule.mem_top))
      have h2 : ρ m (ρ k v) = ρ k (ρ m v) := by
        rw [← glRep_mul_apply, ← glRep_mul_apply, hc m hm k hk.1]
      rw [map_sub, sub_eq_iff_eq_add] at h1
      rw [map_sub, h2, h1]
      abel
  have hp : IsPGroup 2 ↥(cenOn ρ K (commOn ρ M ⊤ ⊔ fixSub ρ M)) := fun k => by
    refine ⟨1, Subtype.ext (hρ (LinearMap.ext fun v => ?_))⟩
    have h1 : ρ k (ρ k v - v) = ρ k v - v := k.2.2 _ (Submodule.mem_sup_right (hfix k k.2 v))
    rw [map_sub, sub_eq_iff_eq_add] at h1
    rw [pow_one, Subgroup.coe_pow, pow_two, glRep_mul_apply, h1, Subgroup.coe_one, map_one,
      Module.End.one_apply, ZModModule.sub_eq_add, add_right_comm, ZModModule.add_self, zero_add]
  have hle : cenOn ρ K (commOn ρ M ⊤ ⊔ fixSub ρ M) ≤ CFSG.pCore 2 G :=
    le_sSup (s := {N : Subgroup G | N.Normal ∧ IsPGroup 2 N}) ⟨hnorm, hp⟩
  rw [hO] at hle
  exact le_bot_iff.1 hle

theorem exists_retraction {N K₀ : Subgroup G} (hN : N.Normal) (hNK : N ⊓ K₀ = ⊥)
    (hsup : N ⊔ K₀ = ⊤) :
    ∃ π : G →* ↥K₀, (∀ k : ↥K₀, π k = k) ∧ ∀ g : G, ((π g : ↥K₀) : G)⁻¹ * g ∈ N := by
  have hc : K₀.IsComplement' N := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff, inf_comm, hNK]
    · rw [← Subgroup.mul_normal, sup_comm, hsup, Subgroup.coe_top]
  let π : G →* ↥K₀ := hc.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπN : ∀ g : G, ((π g : ↥K₀) : G)⁻¹ * g ∈ N := fun g =>
    Subgroup.IsComplement.inv_toLeftFun_mul_mem hc g
  refine ⟨π, fun k => Subtype.ext ?_, hπN⟩
  have h1 : ((π k : ↥K₀) : G)⁻¹ * k ∈ N ⊓ K₀ :=
    ⟨hπN k, K₀.mul_mem (K₀.inv_mem (π k).2) k.2⟩
  rw [hNK, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.1 h1

private theorem card_eq_card_map_mul_card_inf_ker {G' : Type*} [Group G'] (f : G →* G')
    (S : Subgroup G) : Nat.card S = Nat.card (S.map f) * Nat.card ↥(S ⊓ f.ker) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (f.subgroupMap_surjective S)
  rw [Subgroup.ker_subgroupMap] at h
  have h2 : Nat.card ↥(f.ker.subgroupOf S) = Nat.card ↥(S ⊓ f.ker) := by
    rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
    exact Nat.card_congr ((f.ker.subgroupOf S).equivMapOfInjective _ S.subtype_injective).toEquiv
  rw [← h, h2, mul_comm]

theorem hP_subRep_comp_subtype_eq_top [Finite G] [Finite V] (hρ : Function.Injective ρ)
    (hH : hP ρ = ⊤) {N K₀ : Subgroup G} (hN : N.Normal) (hNK : N ⊓ K₀ = ⊥) (hsup : N ⊔ K₀ = ⊤)
    {W : Submodule (ZMod 2) V} (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W)
    (hNW : ∀ n ∈ N, ∀ w ∈ W, ρ n w = w) :
    hP (subRep (ρ.comp K₀.subtype) W fun g w hw => hW g w hw) = ⊤ := by
  obtain ⟨π, hπK, hπN⟩ := exists_retraction hN hNK hsup
  have hact : ∀ g : G, ∀ w ∈ W, ρ g w = ρ (π g : G) w := fun g w hw => by
    calc ρ g w = ρ (π g : G) (ρ ((π g : G)⁻¹ * g) w) := by rw [glRep_mul_apply, glRep_apply_inv]
      _ = ρ (π g : G) w := by rw [hNW _ (hπN g) w hw]
  have hfixW : ∀ S : Subgroup G, W ⊓ fixSub ρ S = W ⊓ fixSub ρ ((S.map π).map K₀.subtype) :=
    fun S => by
      ext w
      simp only [Submodule.mem_inf, mem_fixSub]
      constructor
      · rintro ⟨hw, h⟩
        refine ⟨hw, ?_⟩
        rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
        exact (hact s w hw).symm.trans (h s hs)
      · rintro ⟨hw, h⟩
        exact ⟨hw, fun s hs => (hact s w hw).trans (h _ ⟨π s, ⟨s, hs, rfl⟩, rfl⟩)⟩
  have hmem : ∀ A ∈ calP ρ,
      A.map π ≤ hP (subRep (ρ.comp K₀.subtype) W fun g w hw => hW g w hw) := by
    intro A hA
    by_cases hbot : A.map π = ⊥
    · rw [hbot]
      exact bot_le
    have hel : CFSG.Open.IsElemAbelian 2 (A.map π) := by
      obtain ⟨hcomm, hpow⟩ := hA.2.1
      refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
        obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.1 y.2
        have hab : a * b = b * a := congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hax, ← hby, ← map_mul, ← map_mul, hab]
      · obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
        rw [← map_pow, hpow a ha, map_one]
    have hbest := (isBestOffenderOn_of_mem_calP hρ hA).restrict (le_top : W ≤ ⊤)
    refine le_iSup₂_of_le (A.map π) ((mem_calP_subRep_iff _ _).2 ⟨hbot, hel,
      SubAux.isElemAbelianOn_of_isElemAbelian hel W, fun B hB => ?_⟩) le_rfl
    have hSB : (A ⊓ B.comap π).map π = B := by
      refine le_antisymm (Subgroup.map_le_iff_le_comap.2 inf_le_right) fun b hb => ?_
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 (hB hb)
      exact Subgroup.mem_map_of_mem _ ⟨ha, hb⟩
    have hSk : A ⊓ B.comap π ⊓ π.ker = A ⊓ π.ker := by
      refine le_antisymm (inf_le_inf_right _ inf_le_left)
        (le_inf (le_inf inf_le_left ?_) inf_le_right)
      intro x hx
      rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hx.2]
      exact B.one_mem
    have hcS := card_eq_card_map_mul_card_inf_ker π (A ⊓ B.comap π)
    have hcA := card_eq_card_map_mul_card_inf_ker π A
    rw [hSB, hSk] at hcS
    have h := hbest.2 (A ⊓ B.comap π) inf_le_left
    rw [fixOn, fixOn, hfixW, hfixW A, hSB, hcS, hcA, mul_right_comm (Nat.card ↥B),
      mul_right_comm (Nat.card ↥(A.map π))] at h
    rw [fixOn, fixOn, fixSub_comp_subtype, fixSub_comp_subtype]
    exact Nat.le_of_mul_le_mul_right h Nat.card_pos
  refine eq_top_iff.2 fun x _ => ?_
  have hle : hP ρ ≤ (hP (subRep (ρ.comp K₀.subtype) W fun g w hw => hW g w hw)).comap π :=
    iSup₂_le fun A hA => Subgroup.map_le_iff_le_comap.1 (hmem A hA)
  have hx := hle (show (x : G) ∈ hP ρ by rw [hH]; exact Subgroup.mem_top _)
  rwa [Subgroup.mem_comap, hπK] at hx

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
