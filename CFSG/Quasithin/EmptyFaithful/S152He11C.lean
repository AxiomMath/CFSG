module

public import CFSG.Quasithin.EmptyFaithful.S152He11B
public import CFSG.Quasithin.EmptyFaithful.S152He10E
public import CFSG.Quasithin.Background.C1PackBasic

public section

namespace CFSG.Quasithin.He11

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.He9 CFSG.Quasithin.He10
open scoped commutatorElement

theorem eq_of_isSubnormal_of_le_sup {G : Type} [Group G] [Finite G] {K L T : Subgroup G}
    (hsub : IsSubnormal K L) (hL : L = oTwoUpper L) (hT2 : IsPGroup 2 T) (hTL : T ≤ L)
    (hgen : L ≤ K ⊔ T) : K = L := by
  induction hsub with
  | refl => rfl
  | @step H M K' hle hN hMK ih =>
    have hML : M = K' := ih hL hTL (hgen.trans (sup_le_sup_right hle T))
    subst hML
    have hHN : M ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN
    have h1 : oTwoUpper M ≤ H :=
      (oTwoUpper_mono hgen).trans (oTwoUpper_sup_le hT2 (hTL.trans hHN))
    exact le_antisymm hle (hL ▸ h1)

section Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sup_eq_of_map_sup_eq_top {K T L : Subgroup G} {Y : Type} [Group Y]
    (hKL : K ≤ L) (hTL : T ≤ L) (ρ : ↥L →* Y) (hker : ρ.ker ≤ T.subgroupOf L)
    (htop : (K.subgroupOf L).map ρ ⊔ (T.subgroupOf L).map ρ = ⊤) : K ⊔ T = L := by
  have h1 : ((K.subgroupOf L) ⊔ (T.subgroupOf L)).map ρ = ⊤ := by
    rw [Subgroup.map_sup]
    exact htop
  have h2 : (K.subgroupOf L) ⊔ (T.subgroupOf L) ⊔ ρ.ker = ⊤ := by
    have := Subgroup.comap_map_eq ρ ((K.subgroupOf L) ⊔ (T.subgroupOf L))
    rw [h1, Subgroup.comap_top] at this
    exact this.symm
  have h3 : (K.subgroupOf L) ⊔ (T.subgroupOf L) = ⊤ := by
    rwa [sup_eq_left.mpr (hker.trans le_sup_right)] at h2
  have h4 : (K ⊔ T).subgroupOf L = ⊤ := by
    rw [Subgroup.subgroupOf_sup hKL hTL, h3]
  exact le_antisymm (sup_le hKL hTL) (Subgroup.subgroupOf_eq_top.mp h4)

theorem map_eq_top_of_alt5 {K L : Subgroup G} (hKL : K ≤ L)
    (ρ : ↥L →* ↥(alternatingGroup (Fin 5))) (hker : ρ.ker = CFSG.pCore 2 ↥L)
    (hA5 : Nonempty (OTwoQuot K ≃* ↥(alternatingGroup (Fin 5)))) :
    (K.subgroupOf L).map ρ = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hA5
  let ψ : ↥K →* ↥(alternatingGroup (Fin 5)) := ρ.comp (Subgroup.inclusion hKL)
  have hψker : ψ.ker ≤ (pCoreOf 2 K).subgroupOf K := by
    intro x hx
    have h1 : Subgroup.inclusion hKL x ∈ ρ.ker := hx
    rw [hker] at h1
    have h2 : ((Subgroup.inclusion hKL x : ↥L) : G) ∈ pCoreOf 2 L := C2Six.mem_pCore_two_iff.mp h1
    have h3 : (x : G) ∈ pCoreOf 2 K := by
      have : K ⊓ pCoreOf 2 L ≤ pCoreOf 2 K := by
        refine le_pCoreOf_of_le_normalizer inf_le_left ?_ ((pCoreOf_isPGroup 2 L).to_le inf_le_right)
        intro y hy
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hy, le_normalizer_pCoreOf 2 L (hKL hy)⟩
      exact this ⟨x.2, h2⟩
    exact h3
  have hsub : (pCoreOf 2 K).subgroupOf K = CFSG.Open.pCore 2 ↥K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have hdvd : (CFSG.Open.pCore 2 ↥K).index ∣ ψ.ker.index :=
    Subgroup.index_dvd_of_le (hsub ▸ hψker)
  have h60 : (CFSG.Open.pCore 2 ↥K).index = 60 := by
    have : (CFSG.Open.pCore 2 ↥K).index = Nat.card (OTwoQuot K) := rfl
    rw [this, Nat.card_congr e.toEquiv, card_alternatingGroup_five]
  have hrange : Nat.card ψ.range = ψ.ker.index := by
    rw [← Subgroup.index_ker]
  have hle : 60 ≤ Nat.card ψ.range := by
    rw [hrange]
    exact h60 ▸ Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hdvd
  have hrt : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [card_alternatingGroup_five]
    exact le_antisymm (card_alternatingGroup_five ▸ Nat.card_le_card_of_injective _ Subtype.val_injective) hle
  rw [eq_top_iff, ← hrt]
  rintro _ ⟨x, rfl⟩
  exact ⟨Subgroup.inclusion hKL x, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩

end Gen

section Lin2

variable {G : Type} [Group G] [Finite G]

theorem sup_eq_of_lin2 {K T L : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hKL : K ≤ L) (hTL : T ≤ L) (hT2 : IsPGroup 2 T) (hTi : ¬ 2 ∣ (T.subgroupOf L).index)
    (hKperf : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (ρ : ↥L →* SL2 F) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ T.subgroupOf L) (hkerp : IsPGroup 2 ρ.ker) : K ⊔ T = L := by
  refine sup_eq_of_map_sup_eq_top hKL hTL ρ hker ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hKperf
  have hKn : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
  have hK'perf : Group.IsPerfect ↥(K.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.surjective
  have hK'n : Nontrivial ↥(K.subgroupOf L) :=
    Function.Injective.nontrivial (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKL).symm.injective
  have hKbne : (K.subgroupOf L).map ρ ≠ ⊥ := by
    intro hbot
    have hle : K.subgroupOf L ≤ ρ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    have h2 : IsPGroup 2 ↥(K.subgroupOf L) := hkerp.to_le hle
    have : Group.IsSolvable ↥(K.subgroupOf L) := by
      have : Group.IsNilpotent ↥(K.subgroupOf L) := h2.isNilpotent
      infer_instance
    exact Group.IsPerfect.not_isSolvable ↥(K.subgroupOf L) this
  have hKb : ¬ Group.IsSolvable ↥((K.subgroupOf L).map ρ) := by
    have : Group.IsPerfect ↥((K.subgroupOf L).map ρ) := Group.IsPerfect.map (H := K.subgroupOf L) ρ
    have : Nontrivial ↥((K.subgroupOf L).map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hKbne
    exact Group.IsPerfect.not_isSolvable _
  have hTb2 : IsPGroup 2 ((T.subgroupOf L).map ρ) :=
    (A4.isPGroup_subgroupOf_of_le hTL hT2).map ρ
  have hTbi : ¬ 2 ∣ ((T.subgroupOf L).map ρ).index := by
    rw [Subgroup.index_map_eq _ hρ hker]
    exact hTi
  exact sup_eq_top_of_not_solvable hKb hTb2 hTbi

end Lin2

theorem input15204A314_holds : Input15204A314 := by
  intro G _ _ X S K L hX hS hLc hχ hK hKL hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLX : L ≤ X := le_of_mem_cComp hLc
  have hsubLX : IsSubnormal L X := subnormal_of_mem_cComp hLc
  have hKc : K ∈ cComp (K ⊔ S) := hK
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hKc
  have hKne : K ≠ ⊥ := ne_bot_of_mem_cComp hKc
  have hTsyl : IsSylowTwoOf (S ⊓ L) L := A312.isSylowTwoOf_inf_of_subnormal hsubLX hS
  have hTL : S ⊓ L ≤ L := inf_le_right
  have hT2 : IsPGroup 2 (S ⊓ L : Subgroup G) := hTsyl.2.1
  have hQS : pCoreOf 2 X ≤ S :=
    A4.le_of_normal_of_isSylowTwoOf hS (pCoreOf_le 2 X)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 X)).2
        (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  have hQT : pCoreOf 2 L ≤ S ⊓ L :=
    le_inf ((A4.pCoreOf_le_of_subnormal 2 hsubLX).trans hQS) (pCoreOf_le 2 L)
  have hkerT : ∀ {Y : Type} [Group Y] (ρ : ↥L →* Y), ρ.ker = CFSG.pCore 2 ↥L →
      ρ.ker ≤ (S ⊓ L).subgroupOf L := by
    intro Y _ ρ hρ x hx
    rw [hρ] at hx
    exact hQT (C2Six.mem_pCore_two_iff.mp hx)
  have hL2 : L = oTwoUpper L := C1Pack.isShort2_eq_oTwoUpper hχ.1.1
  have hgen : K ⊔ (S ⊓ L) = L := by
    rcases hχ.2 with ⟨n, hn, F, hF, hFin, hcard, α, hα, hαker, -⟩ | ⟨α, hα, hαker, -⟩ | ⟨α, hα, hαker, -⟩
    · have : Finite F := Finite.of_fintype F
      have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hcard
      exact sup_eq_of_lin2 hKL hTL hT2 hTsyl.2.2 hKperf hKne α hα (hkerT α hαker)
        (hαker ▸ CFSG.pCore_isPGroup)
    · exfalso
      have h3 : Group.IsSolvable ↥(alternatingGroup (Fin 3)) :=
        alternatingGroup.isSolvable (by simp)
      have hp : Group.IsNilpotent ↥(CFSG.pCore 2 ↥L) := (CFSG.pCore_isPGroup (p := 2)).isNilpotent
      have : Group.IsSolvable ↥L := by
        refine Group.isSolvable_of_ker_le_range (CFSG.pCore 2 ↥L).subtype α ?_
        rw [hαker, Subgroup.range_subtype]
      exact not_isSolvable_of_mem_cComp hLc this
    · exact sup_eq_of_map_sup_eq_top hKL hTL α (hkerT α hαker) (by
        rw [map_eq_top_of_alt5 hKL α hαker hA5, top_sup_eq])
  have hsubKL : IsSubnormal K L :=
    A3.subnormal_of_le_of_le (subnormal_of_mem_cComp hKc) hKL
      (hgen ▸ sup_le_sup_left inf_le_left K)
  exact eq_of_isSubnormal_of_le_sup hsubKL hL2 hT2 hTL (le_of_eq hgen.symm)

end CFSG.Quasithin.He11
