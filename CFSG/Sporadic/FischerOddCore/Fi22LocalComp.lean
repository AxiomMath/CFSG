module

public import CFSG.Sporadic.FischerOddCore.Fi22CTI
public import CFSG.Sporadic.FischerOddCore.Fi22AllInv
public import CFSG.Sporadic.FischerOddCore.CentralExt
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores CFSG.Monster.B.Co2 CFSG.Monster.B.Fischer
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Sporadic.Fi22 (Ca caQuotEquiv)

section Generic

theorem card_quotient_center_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (G ⧸ Subgroup.center G) = Nat.card (H ⧸ Subgroup.center H) :=
  Nat.card_congr (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).toEquiv

theorem component_quotient_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    {B : Subgroup G} (hB : IsComponent B) :
    IsComponent (B.map e.toMonoidHom) ∧
      Nat.card (B ⧸ Subgroup.center B) =
        Nat.card (B.map e.toMonoidHom ⧸ Subgroup.center (B.map e.toMonoidHom)) :=
  ⟨isComponent_map_mulEquiv e hB,
    card_quotient_center_mulEquiv (B.equivMapOfInjective e.toMonoidHom e.injective)⟩

theorem exists_noncomm_of_isSimpleGroup {Q : Type*} [Group Q] (hQ : IsSimpleGroup Q)
    (hp : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : Q, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  have : IsMulCommutative Q := ⟨⟨hc⟩⟩
  exact hp ((Group.is_simple_iff_prime_card (α := Q)).1 hQ)

theorem not_isComponent_of_isSolvable {G : Type*} [Group G] (hG : Group.IsSolvable G)
    {B : Subgroup G} : ¬ IsComponent B := by
  rintro ⟨hq, -⟩
  have : Nontrivial B := isQuasisimple_nontrivial hq
  have : Group.IsPerfect B := hq.1
  have : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective B.subtype_injective
  exact Group.IsPerfect.not_isSolvable B this

theorem card_quotient_center_of_component_simple {E K : Type*} [Group E] [Group K] [Finite E]
    (ρ : E →* K) (hρ : Function.Surjective ρ) (hker : Group.IsSolvable ρ.ker)
    (hKs : IsSimpleGroup K) (hKnc : ∃ a b : K, a * b ≠ b * a) {B : Subgroup E}
    (hB : IsComponent B) : Nat.card (B ⧸ Subgroup.center B) = Nat.card K := by
  obtain ⟨hq, hsub⟩ := hB
  have hperf : Group.IsPerfect B := hq.1
  have hnt : Nontrivial B := isQuasisimple_nontrivial hq
  rcases (hsub.map hρ).eq_bot_or_top_of_isSimpleGroup hKs with h | h
  · exfalso
    have hBk : B ≤ ρ.ker := by
      intro b hb
      rw [MonoidHom.mem_ker]
      have : ρ b ∈ B.map ρ := ⟨b, hb, rfl⟩
      rwa [h, Subgroup.mem_bot] at this
    have : Group.IsSolvable B :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hBk)
    exact Group.IsPerfect.not_isSolvable B this
  · set ρB : B →* K := ρ.comp B.subtype
    have hrange : ρB.range = ⊤ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, h]
    have hkerB : ρB.ker = Subgroup.center B := by
      apply le_antisymm
      · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq ρB.normal_ker with h1 | h1
        · exfalso
          obtain ⟨a, b, hab⟩ := hKnc
          obtain ⟨x, hx⟩ := (hrange ▸ Subgroup.mem_top a : a ∈ ρB.range)
          have hx1 : x ∈ ρB.ker := h1 ▸ Subgroup.mem_top x
          rw [MonoidHom.mem_ker, hx] at hx1
          apply hab
          rw [hx1, one_mul, mul_one]
        · exact h1
      · intro z hz
        rw [MonoidHom.mem_ker]
        have hc : ρB z ∈ Subgroup.center K := by
          rw [Subgroup.mem_center_iff]
          intro g
          obtain ⟨y, rfl⟩ := (hrange ▸ Subgroup.mem_top g : g ∈ ρB.range)
          rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y)]
        have hZ : Subgroup.center K = ⊥ := by
          rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h2 | h2
          · exact h2
          · exfalso
            obtain ⟨a, b, hab⟩ := hKnc
            have hb : b ∈ Subgroup.center K := h2 ▸ Subgroup.mem_top b
            exact hab (Subgroup.mem_center_iff.1 hb a)
        rwa [hZ, Subgroup.mem_bot] at hc
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρB.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ρB).toEquiv, hrange,
      Subgroup.card_top, hkerB] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center B)
    have hpos : 0 < Nat.card (Subgroup.center B) := Nat.card_pos
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem card_quotient_center_of_component_of_equiv {C E K : Type*} [Group C] [Group E]
    [Group K] [Finite E] (g : C ≃* E) (ρ : E →* K) (hρ : Function.Surjective ρ)
    (hker : Group.IsSolvable ρ.ker) (hKs : IsSimpleGroup K) (hKnc : ∃ a b : K, a * b ≠ b * a)
    {B : Subgroup C} (hB : IsComponent B) : Nat.card (B ⧸ Subgroup.center B) = Nat.card K := by
  have : Finite C := Finite.of_equiv _ g.symm.toEquiv
  obtain ⟨hB', hcard⟩ := component_quotient_mulEquiv g hB
  rw [hcard]
  exact card_quotient_center_of_component_simple ρ hρ hker hKs hKnc hB'

end Generic

@[expose] def fi22Kappa :
    Ca →* CFSG.Fischer.T46 :=
  { toFun := fun c => caQuotEquiv (c : Ca ⧸ Subgroup.center Ca)
    map_one' := by simp
    map_mul' := fun x y => by simp }

theorem fi22Kappa_apply
    (c : Ca) : fi22Kappa c = caQuotEquiv (c : Ca ⧸ Subgroup.center Ca) :=
  rfl

theorem fi22Kappa_surjective :
    Function.Surjective fi22Kappa := by
  intro y
  obtain ⟨q, rfl⟩ := caQuotEquiv.surjective y
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨c, rfl⟩

theorem ker_fi22Kappa :
    fi22Kappa.ker = Subgroup.center Ca := by
  ext x
  rw [MonoidHom.mem_ker, fi22Kappa_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

theorem isSolvable_ker_fi22Kappa :
    Group.IsSolvable fi22Kappa.ker := by
  rw [ker_fi22Kappa]
  infer_instance

theorem exists_noncomm_T46 :
    ∃ a b : CFSG.Fischer.T46, a * b ≠ b * a :=
  exists_noncomm_of_isSimpleGroup CFSG.Fischer.isSimpleGroup_T46
    (by rw [CFSG.Fischer.card_T46]; norm_num)

theorem card_quotient_center_of_component_CPz
    {B : Subgroup ↥(fi22P ⊓ Subgroup.centralizer {fi22OuterZ})} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 isConj_fi22OuterZP_fi22Ya
  have e1 := fi22CPzEquiv
  have e2 := centralizerMulEquiv (MulAut.conj c) fi22OuterZP
  have e3 : ↥(Subgroup.centralizer ({MulAut.conj c fi22OuterZP} : Set fi22P)) ≃*
      ↥(Subgroup.centralizer ({fi22Ya} : Set fi22P)) :=
    MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc])
  have e4 := @centralizerMulEquiv fi22P CFSG.Sporadic.Fi22.J inferInstance inferInstance fi22PJ
    fi22Ya
  have e5 : ↥(Subgroup.centralizer ({fi22PJ fi22Ya} : Set CFSG.Sporadic.Fi22.J)) ≃* Ca :=
    MulEquiv.subgroupCongr (by rw [fi22Ya, MulEquiv.apply_symm_apply])
  rw [@card_quotient_center_of_component_of_equiv ↥(fi22P ⊓ Subgroup.centralizer {fi22OuterZ}) Ca
    CFSG.Fischer.T46 inferInstance inferInstance inferInstance inferInstance
    ((((e1.trans e2).trans e3).trans e4).trans e5) fi22Kappa fi22Kappa_surjective
    isSolvable_ker_fi22Kappa CFSG.Fischer.isSimpleGroup_T46 exists_noncomm_T46 B hB,
    CFSG.Fischer.card_T46]

theorem primeFactors_card_fi22H_zero : (Nat.primeFactors 1769472).card ≤ 2 := by
  rw [show (1769472 : ℕ) = 2 ^ 16 * 3 ^ 3 by norm_num,
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
    Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
  decide

theorem card_fi22H_zero :
    Nat.card (fi22H 0) = 1769472 := by
  rw [card_fi22H (c := 0) (by norm_num), CTUC_Fi22_centralizer_certificate_data.2.2.2.2.2.2.1]
  rfl

theorem card_quotient_center_of_component_rep
    {k : ℕ} (hk : k < 3)
    {B : Subgroup ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k})} (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨h0, h1, -⟩ := CTUC_Fi22_five_exact_involution_fixed_subgroups
  interval_cases k
  · exfalso
    have e := MulEquiv.subgroupCongr h0
    have hs : Group.IsSolvable (fi22H 0) :=
      isSolvable_of_card_primeFactors_le_two (by rw [card_fi22H_zero]; exact
        primeFactors_card_fi22H_zero)
    exact not_isComponent_of_isSolvable hs (component_quotient_mulEquiv e hB).1
  · exfalso
    have e := MulEquiv.subgroupCongr h1
    exact CTI_Fi22_second_involution_centralizer_normal_two_subgroup.2.1 _
      (component_quotient_mulEquiv e hB).1
  · have e := MulEquiv.subgroupCongr (show fi22P ⊓ Subgroup.centralizer {fi22ExtRep 2} =
        fi22P ⊓ Subgroup.centralizer {fi22OuterZ} by rw [fi22ExtRep_two])
    obtain ⟨hB', hcard⟩ := component_quotient_mulEquiv e hB
    rw [hcard]
    exact card_quotient_center_of_component_CPz hB'

theorem CTI_Fi22_involution_local_components_unitary_quotient_order
    {T : Type*} [Group T]
    (e : T ≃* Blueprint.NativeSporadic.Fi22) (t : T) (ht : orderOf t = 2)
    (B : Subgroup (Subgroup.centralizer ({t} : Set T))) (hB : IsComponent B) :
    Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  set f : T ≃* fi22P := e.trans fi22PermEquiv
  have hτP : ((f t : fi22P) : Equiv.Perm (Fin 3510)) ∈ fi22P := (f t).2
  have hτ : orderOf ((f t : fi22P) : Equiv.Perm (Fin 3510)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have g1 : ↥(Subgroup.centralizer ({t} : Set T)) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {((f t : fi22P) : Equiv.Perm (Fin 3510))}) :=
    (centralizerMulEquiv f t).trans (infCentralizerEquiv fi22P hτP).symm
  obtain ⟨k, hk, r, hr, hrτ⟩ := fi22R_involution_conj (fi22P_le_R hτP) hτ
  have hrn := fi22R_le_normalizer hr
  have hkP : fi22ExtRep k ∈ fi22P := by
    rw [← hrτ]
    exact (Subgroup.mem_normalizer_iff.1 hrn _).1 hτP
  have hk3 : k < 3 := by
    by_contra h
    obtain ⟨j, rfl⟩ : ∃ j, k = 3 + j := ⟨k - 3, by omega⟩
    exact (CTUC_Fi22_all_extension_involutions_covered.2.1 j (by omega)).2 hkP
  have g2 : ↥(fi22P ⊓ Subgroup.centralizer {((f t : fi22P) : Equiv.Perm (Fin 3510))}) ≃*
      ↥(fi22P ⊓ Subgroup.centralizer {fi22ExtRep k}) :=
    (fi22CP_conj_equiv hrn _).trans (MulEquiv.subgroupCongr (by rw [hrτ]))
  obtain ⟨hB', hcard⟩ := component_quotient_mulEquiv (g1.trans g2) hB
  rw [hcard]
  exact card_quotient_center_of_component_rep hk3 hB'

end CFSG.Sporadic.FischerOddCore
