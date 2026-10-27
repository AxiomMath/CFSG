module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixNbrB
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrB
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2]
variable {G : Type} [Group G] [Finite G]

theorem ggQTwoDUnitSix_dSign_sub_single {a c k : Fin 6} (hac : a ≠ c) (hka : k ≠ a)
    (hkc : k ≠ c) :
    dSign 6 a c (Pi.single k 1 + -Pi.single a 1) = Pi.single k 1 + Pi.single a 1 := by
  funext l
  rw [dSign_apply_vec]
  by_cases hla : l = a
  · rw [hla]
    simp [Ne.symm hka]
  · by_cases hlc : l = c
    · rw [hlc]
      simp [Ne.symm hkc, Ne.symm hac]
    · simp [Pi.single_apply, hla, hlc]

theorem ggQTwoDUnitSix_single_eq_add : ∀ k a : Fin 6,
    (Pi.single k 1 : DVec 6) =
      ((Pi.single k 1 + Pi.single a 1) + (Pi.single k 1 + -Pi.single a 1)) +
        ((Pi.single k 1 + Pi.single a 1) + (Pi.single k 1 + -Pi.single a 1)) := by
  decide

theorem ggQTwoDUnitSix_torus (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) :
    ∀ t : ↥Bs, βL (Additive.ofMul t) c = 0 →
      (t : G) ∈ J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom := by
  classical
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  let A : AddSubgroup (DVec 6) :=
    { carrier := {v | ((Additive.toMul (βL.symm v) : ↥Bs) : G) ∈
        J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom}
      add_mem' := fun {u v} hu hv => by
        simp only [Set.mem_setOf_eq, map_add, toMul_add, Subgroup.coe_mul] at hu hv ⊢
        exact Subgroup.mul_mem _ hu hv
      zero_mem' := by
        simp only [Set.mem_setOf_eq, map_zero, toMul_zero, Subgroup.coe_one]
        exact Subgroup.one_mem _
      neg_mem' := fun {v} hv => by
        simp only [Set.mem_setOf_eq, map_neg, toMul_neg, Subgroup.coe_inv] at hv ⊢
        exact Subgroup.inv_mem _ hv }
  have hmemA : ∀ s : ↥Bs, (s : G) ∈ J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom →
      βL (Additive.ofMul s) ∈ A := fun s hs => by
    show ((Additive.toMul (βL.symm (βL (Additive.ofMul s))) : ↥Bs) : G) ∈
      J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom
    simpa using hs
  have hS : ∀ i ∈ Finset.univ.erase c, ∀ k ∈ Finset.univ.erase c, i ≠ k →
      Pi.single i 1 + -Pi.single k 1 ∈ A := by
    intro i hi k hk hik
    obtain ⟨t, htJ, hβt⟩ := ggQTwoDUnitSix_sub_single_mem hK hD hψk hε hind hpermβ
      (T := Finset.univ.erase c) (by omega) hJ₁L hJ₁Z hJ₁ hi hk hik
    have h := hmemA t (Subgroup.mem_sup_left htJ)
    rwa [hβt] at h
  obtain ⟨k, hk⟩ : ∃ k, k ∈ (Finset.univ.erase c).erase a :=
    Finset.card_pos.mp (by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩), h5]
      norm_num)
  have hka : k ≠ a := (Finset.mem_erase.mp hk).1
  have hkS : k ∈ Finset.univ.erase c := (Finset.mem_erase.mp hk).2
  have hkc : k ≠ c := (Finset.mem_erase.mp hkS).1
  have haS : a ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩
  have hJ₂ : Pi.single k 1 + Pi.single a 1 ∈ A := by
    obtain ⟨t, htJ, hβt⟩ := ggQTwoDUnitSix_sub_single_mem hK hD hψk hε hind hpermβ
      (T := Finset.univ.erase c) (by omega) hJ₁L hJ₁Z hJ₁ hkS haS hka
    have hαt : βL (Additive.ofMul (α t)) = Pi.single k 1 + Pi.single a 1 := by
      rw [hα, hβt]
      exact ggQTwoDUnitSix_dSign_sub_single hac hka hkc
    rw [← hαt]
    refine hmemA (α t) (Subgroup.mem_sup_right ?_)
    rw [hg]
    exact Subgroup.mem_map.mpr ⟨t, htJ, rfl⟩
  have hk1 : Pi.single k 1 ∈ A := by
    have h := A.add_mem (A.add_mem hJ₂ (hS k hkS a haS hka))
      (A.add_mem hJ₂ (hS k hkS a haS hka))
    rw [ggQTwoDUnitSix_single_eq_add k a]
    exact h
  have hi1 : ∀ i ∈ Finset.univ.erase c, Pi.single i 1 ∈ A := by
    intro i hi
    by_cases hik : i = k
    · rw [hik]
      exact hk1
    · have h := A.add_mem (hS i hi k hkS hik) hk1
      rwa [neg_add_cancel_right] at h
  intro t ht
  have hv : βL (Additive.ofMul t) ∈ A := by
    rw [← Finset.univ_sum_single (βL (Additive.ofMul t))]
    refine A.sum_mem fun i _ => ?_
    by_cases hic : i = c
    · rw [hic, ht, Pi.single_zero]
      exact A.zero_mem
    · have hi : i ∈ Finset.univ.erase c := Finset.mem_erase.mpr ⟨hic, Finset.mem_univ i⟩
      rcases (by decide : ∀ r : ZMod 3, r = 0 ∨ r = 1 ∨ r = 2) (βL (Additive.ofMul t) i) with
        h0 | h1 | h2
      · rw [h0, Pi.single_zero]
        exact A.zero_mem
      · rw [h1]
        exact hi1 i hi
      · rw [h2, show (2 : ZMod 3) = 1 + 1 by decide, Pi.single_add]
        exact A.add_mem (hi1 i hi) (hi1 i hi)
  have hv' : ((Additive.toMul (βL.symm (βL (Additive.ofMul t))) : ↥Bs) : G) ∈
      J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom := hv
  simpa using hv'

theorem ggQTwoDUnitSix_normalizer_N (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type}
    [Group Q] {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) (hBsE : CFSG.Open.IsElemAbelian 3 Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    {c : Fin 6} {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {y : G} (hy : y ∈ Bs) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) N) (hJ₁N : J₁ ≤ N) :
    Bs ≤ Subgroup.normalizer (N : Set G) := by
  have h5 : (Finset.univ.erase c).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hBsJ := ggQTwoDUnitSix_Bs_le_normalizer hK hD hψk hind (T := Finset.univ.erase c)
    (by omega) hJ₁L hJ₁Z hJ₁
  obtain ⟨θ, hθ, hθr, -⟩ := ggQTwoDUnitSix_chart hK hD hψk (Finset.univ.erase c) (by omega)
    hJ₁L hJ₁Z hJ₁
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥J₁) 3
    (ggQTwoDUnitSix_three_dvd_card hK (by omega) hθ hθr)
  have hu1 : (u : G) ≠ 1 := by
    intro h
    have h1 : u = 1 := Subtype.ext h
    rw [h1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hu3 : (u : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hu, pow_orderOf_eq_one, Subgroup.coe_one]
  exact qtwoDB17_normalizer_of_block hBsE
    (fun s hs => Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBsJ hs)) hy hN hJ₁N
    Subgroup.commutator_eq_self.ge u.2 hu1 hu3

theorem ggQTwoDUnitSix_inner_N (hK : Nat.card K = 4) {L Bs : Subgroup G} {Q : Type} [Group Q]
    {f : ↥(Subgroup.normalizer (L : Set G)) →* Q} {ψ : Su K 2 1 6 →* Q}
    (hD : NsQuot.Datum 3 (Subgroup.normalizer (L : Set G)) f L Bs (twoCentral L))
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    (hε : ∀ (σ : Equiv.Perm (Fin 6)), ∀ q ∈ NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs,
      ψ (ggPermSU σ⁻¹) * q * (ψ (ggPermSU σ⁻¹))⁻¹ ∈
        NsQuot.img (Subgroup.normalizer (L : Set G)) f Bs)
    {βL : Additive ↥Bs ≃+ DVec 6} {ω : Kˣ}
    (hind : ∀ (s : ↥Bs) (hs : (s : G) ∈ Subgroup.normalizer (L : Set G)),
      qTwoChartTwoThree_induces ψ (f ⟨s, hs⟩) (fun i => ω ^ (βL (Additive.ofMul s) i).val))
    (hpermβ : ∀ (σ : Equiv.Perm (Fin 6)) (s t : ↥Bs)
      (hs : (s : G) ∈ Subgroup.normalizer (L : Set G))
      (ht : (t : G) ∈ Subgroup.normalizer (L : Set G)),
      f ⟨t, ht⟩ = ψ (ggPermSU σ⁻¹) * f ⟨s, hs⟩ * (ψ (ggPermSU σ⁻¹))⁻¹ →
        βL (Additive.ofMul t) = dPerm 6 σ (βL (Additive.ofMul s)))
    {a c : Fin 6} (hac : a ≠ c) {J₁ : Subgroup G} (hJ₁L : J₁ ≤ L) [Group.IsPerfect ↥J₁]
    (hJ₁Z : ∀ j ∈ J₁, j ∈ twoCentral L → j = 1)
    (hJ₁ : NsQuot.img (Subgroup.normalizer (L : Set G)) f J₁ =
      (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    {α : MulAut ↥Bs}
    (hα : ∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s)))
    {g : G} (hg : ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹) {b' : ↥Bs}
    (hb' : βL (Additive.ofMul b') = Pi.single c 1) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁N : J₁ ≤ N) (hJ₂N : J₁.map (MulAut.conj g).toMonoidHom ≤ N) :
    ∀ s : ↥Bs, ∃ t ∈ N, ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ = t * n * t⁻¹ :=
  qtwoDB17_inner_of_torus hb'
    (ggQTwoDUnitSix_torus hK hD hψk hε hind hpermβ hac hJ₁L hJ₁Z hJ₁ hα hg)
    (sup_le hJ₁N hJ₂N) hN.1

theorem ggQTwoDUnitSix_innerDiag_N
    {B L Bs D J N : Subgroup G}
    {x b' : G} (hThmI : GGThmIHyp 3 B x L) (hDJ : LargeEvenStdSub 3 B x L D J)
    (hnbr : GGNbr 3 B x D J b' N) (hBsN : Bs ≤ Subgroup.normalizer (N : Set G))
    (hinner : ∀ s : ↥Bs, ∃ t ∈ N, ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ = t * n * t⁻¹) :
    GGInnerDiagOn Bs N :=
  qtwoDB17_innerDiag_of_inner (ggRawInnSubgroupInput_of_rawInnField ggRawInnFieldInput_holds)
    hThmI hDJ hnbr hBsN hinner

end CFSG.StandardType.QTwo

end
