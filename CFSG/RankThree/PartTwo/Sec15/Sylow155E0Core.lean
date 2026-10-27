module

public import CFSG.Foundations.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113Rank2
public import CFSG.RankThree.S4Free.StellmacherHosts
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentLift
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113CentBender
import CFSG.GH74.GLS.Balance.CompNormalizes
import CFSG.GroupTheory.OddOrderClosurePerfect

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace Sylow155E0

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.RankThree.S4Free

variable {Q : Type} [Group Q] [Finite Q]

private theorem odd_orderOf_of_coprime {K : Subgroup Q} (hK : Nat.Coprime 2 (Nat.card K)) {k : Q}
    (hk : k ∈ K) : Odd (orderOf k) := by
  have h1 : orderOf k ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : K)
    rwa [Subgroup.orderOf_mk] at this
  exact Nat.coprime_two_left.mp (hK.coprime_dvd_right h1)

private theorem eq_one_of_odd_of_isPGroup {T : Subgroup Q} (hT : IsPGroup 2 T) {t : Q}
    (ht : t ∈ T) (hto : Odd (orderOf t)) : t = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hT ⟨t, ht⟩
  rw [Subgroup.orderOf_mk] at hn
  have hcop : Nat.Coprime (orderOf t) (2 ^ n) := (Nat.coprime_two_right.mpr hto).pow_right n
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (hn ▸ dvd_refl _))

private theorem mem_centralizer_sup {H K : Subgroup Q} {x : Q}
    (hH : x ∈ Subgroup.centralizer (H : Set Q)) (hK : x ∈ Subgroup.centralizer (K : Set Q)) :
    x ∈ Subgroup.centralizer ((H ⊔ K : Subgroup Q) : Set Q) := by
  have hle : H ⊔ K ≤ Subgroup.centralizer ({x} : Set Q) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hH y hy)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hK y hy)
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

private theorem coe_mem_centralizer {N T : Subgroup Q} (hTN : T ≤ N) {n : ↥N}
    (hn : n ∈ Subgroup.centralizer ((T.subgroupOf N : Subgroup ↥N) : Set ↥N)) :
    (n : Q) ∈ Subgroup.centralizer (T : Set Q) := by
  rw [Subgroup.mem_centralizer_iff] at hn ⊢
  intro t ht
  exact congrArg Subtype.val (hn ⟨t, hTN ht⟩ ht)

private theorem mem_centralizer_of_coprime {N : Subgroup Q} {K : Subgroup ↥N} (hKn : K.Normal)
    (hK : Nat.Coprime 2 (Nat.card K)) {T : Subgroup Q} (hT : IsPGroup 2 T) (hTN : T ≤ N)
    (hTn : (T.subgroupOf N).Normal) {k : ↥N} (hk : k ∈ K) :
    (k : Q) ∈ Subgroup.centralizer (T : Set Q) := by
  have hdis : Disjoint K (T.subgroupOf N) := by
    rw [Subgroup.disjoint_def]
    intro z hzK hzT
    refine Subtype.ext (eq_one_of_odd_of_isPGroup hT hzT ?_)
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_coprime hK hzK
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have hc := Subgroup.commute_of_normal_of_disjoint K (T.subgroupOf N) hKn hTn hdis k
    ⟨t, hTN ht⟩ hk ht
  exact (congrArg Subtype.val hc.eq).symm

theorem card_le_card_inf_sylow (S : Sylow 2 Q) {H : Subgroup Q} [H.Normal] {T : Subgroup Q}
    (hTH : T ≤ H) (hT : IsPGroup 2 T) :
    Nat.card T ≤ Nat.card ((S : Subgroup Q) ⊓ H : Subgroup Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_eq_subgroupOf_of_normal S H
  have hT' : IsPGroup 2 (T.subgroupOf H) := hT.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨S', hS'⟩ := hT'.exists_le_sylow
  have e1 : Nat.card T = Nat.card (T.subgroupOf H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv.symm
  have e2 : Nat.card ((S : Subgroup Q) ⊓ H : Subgroup Q) = Nat.card (P : Subgroup H) := by
    rw [hP, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective H.subtype_injective]
  calc Nat.card T = Nat.card (T.subgroupOf H) := e1
    _ ≤ Nat.card S' := Subgroup.card_le_of_le hS'
    _ = Nat.card P := (Sylow.card_eq_multiplicity S').trans (Sylow.card_eq_multiplicity P).symm
    _ = Nat.card ((S : Subgroup Q) ⊓ H : Subgroup Q) := e2.symm

private theorem layer_normal : (layer Q).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := Q)
  infer_instance

theorem sylow_le_normalizer_inf (S : Sylow 2 Q) :
    (S : Subgroup Q) ≤ Subgroup.normalizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q) := by
  have : (layer Q).Normal := layer_normal
  intro s hs
  have hsS : s ∈ Subgroup.normalizer ((S : Subgroup Q) : Set Q) := Subgroup.le_normalizer hs
  have hsE : s ∈ Subgroup.normalizer ((layer Q : Subgroup Q) : Set Q) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top s
  exact Subgroup.mem_normalizer_iff.mpr fun h =>
    and_congr (Subgroup.mem_normalizer_iff.mp hsS h) (Subgroup.mem_normalizer_iff.mp hsE h)

theorem mem_centralizer_layer
    (hSA : ∀ J : Subgroup Q, IsComponent J → SylowAutTrivial (↥J ⧸ Subgroup.center ↥J))
    (S : Sylow 2 Q) {x : Q}
    (hx : x ∈ Subgroup.centralizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q))
    (hxo : Odd (orderOf x)) : x ∈ Subgroup.centralizer (layer Q : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (layer Q).Normal := layer_normal
  set P : Subgroup Q := (S : Subgroup Q) ⊓ layer Q with hPdef
  have hPE : P ≤ layer Q := inf_le_right
  have hP2 : IsPGroup 2 P := S.isPGroup'.to_le inf_le_left
  have hPs : ∀ T : Subgroup Q, T ≤ layer Q → IsPGroup 2 T → Nat.card T ≤ Nat.card P :=
    fun T hT hT2 => card_le_card_inf_sylow S hT hT2
  have hJ : ∀ J : Subgroup Q, IsComponent J → J ≤ Subgroup.centralizer ({x} : Set Q) := by
    intro J hJ
    have hxN := CFSG.GH74.GLS.Balance.mem_normalizer_of_centralizes_sylow hJ P hPE hP2 hPs hx
    have hJE := CFSG.LocalCores.components_normal_in_layer hJ
    obtain ⟨SJ, hSJ⟩ :=
      CFSG.GH74.GLS.Balance.Comp.exists_sylow_map_eq_inf hJE.1 hJE.2 hPE hP2 hPs
    have hT : IsSylowTwoOf (P ⊓ J) J := by
      refine ⟨inf_le_right, hP2.to_le inf_le_left, ?_⟩
      have heq : (P ⊓ J).subgroupOf J = (SJ : Subgroup J) := by
        rw [← hSJ]
        exact Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
      rw [heq]
      exact SJ.not_dvd_index
    have hxJ := centralizes_of_sylowAutTrivial hJ.1 hT (hSA J hJ) hxN
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) hx) hxo
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxJ y hy)
  have hle : layer Q ≤ Subgroup.centralizer ({x} : Set Q) := by
    rw [layer.eq_sSup]
    exact sSup_le fun J hJ' => hJ J hJ'
  exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem centralizer_generalizedFitting_le_pCore (hO : pPrimeCore 2 Q = ⊥) :
    Subgroup.centralizer (generalizedFitting Q : Set Q) ≤ pCore 2 Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (layer Q).Normal := layer_normal
  have : (generalizedFitting Q).Normal := by
    rw [generalizedFitting.eq_sup]
    infer_instance
  have hCF := centralizer_generalizedFitting_le Q
  have : IsMulCommutative ↥(Subgroup.centralizer (generalizedFitting Q : Set Q)) :=
    isMulCommutative_iff.mpr fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp a.2 b (hCF b.2)).symm
  rw [← Fitting_eq_pcore Q 2 hO]
  exact le_sSup (s := {N : Subgroup Q | N.Normal ∧ Group.IsNilpotent N})
    ⟨inferInstance, inferInstance⟩

private theorem centralizer_generalizedFitting_comm {a b : Q}
    (ha : a ∈ Subgroup.centralizer (generalizedFitting Q : Set Q))
    (hb : b ∈ Subgroup.centralizer (generalizedFitting Q : Set Q)) : a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp ha b (centralizer_generalizedFitting_le Q hb)).symm

private theorem mem_centralizer_generalizedFitting (hO : pPrimeCore 2 Q = ⊥) {x : Q}
    (hx2 : x ∈ Subgroup.centralizer (pCore 2 Q : Set Q))
    (hxE : x ∈ Subgroup.centralizer (layer Q : Set Q)) :
    x ∈ Subgroup.centralizer (generalizedFitting Q : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [generalizedFitting.eq_sup, Fitting_eq_pcore Q 2 hO]
  exact mem_centralizer_sup hx2 hxE

private theorem pCore_le_normalizer (S : Sylow 2 Q) :
    pCore 2 Q ≤ Subgroup.normalizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (pCore_isPGroup.le_sylow_of_normal S).trans (sylow_le_normalizer_inf S)

theorem pPrimeCore_normalizer_eq_bot (hO : pPrimeCore 2 Q = ⊥)
    (hSA : ∀ J : Subgroup Q, IsComponent J → SylowAutTrivial (↥J ⧸ Subgroup.center ↥J))
    (S : Sylow 2 Q) :
    pPrimeCore 2
      ↥(Subgroup.normalizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup Q := (S : Subgroup Q) ⊓ layer Q with hPdef
  set N : Subgroup Q := Subgroup.normalizer (P : Set Q) with hNdef
  have hKn : (pPrimeCore 2 ↥N).Normal := pPrimeCore_normal
  have hKc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥N)) := pPrimeCore_coprime_card
  have hP2 : IsPGroup 2 P := S.isPGroup'.to_le inf_le_left
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  have hko : Odd (orderOf (k : Q)) := by
    rw [Subgroup.orderOf_coe]
    exact odd_orderOf_of_coprime hKc hk
  have hkP : (k : Q) ∈ Subgroup.centralizer (P : Set Q) :=
    mem_centralizer_of_coprime hKn hKc hP2 Subgroup.le_normalizer inferInstance hk
  have hkO : (k : Q) ∈ Subgroup.centralizer (pCore 2 Q : Set Q) :=
    mem_centralizer_of_coprime hKn hKc pCore_isPGroup (pCore_le_normalizer S)
      (pCore_normal.subgroupOf N) hk
  have hkF := mem_centralizer_generalizedFitting hO hkO (mem_centralizer_layer hSA S hkP hko)
  exact Subtype.ext (eq_one_of_odd_of_isPGroup pCore_isPGroup
    (centralizer_generalizedFitting_le_pCore hO hkF) hko)

theorem layer_normalizer_eq_bot (hO : pPrimeCore 2 Q = ⊥)
    (hSA : ∀ J : Subgroup Q, IsComponent J → SylowAutTrivial (↥J ⧸ Subgroup.center ↥J))
    (S : Sylow 2 Q) :
    layer ↥(Subgroup.normalizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup Q := (S : Subgroup Q) ⊓ layer Q with hPdef
  set N : Subgroup Q := Subgroup.normalizer (P : Set Q) with hNdef
  have hP2 : IsPGroup 2 P := S.isPGroup'.to_le inf_le_left
  have hPN : P ≤ N := Subgroup.le_normalizer
  have hON : pCore 2 Q ≤ N := pCore_le_normalizer S
  have hP2' : IsPGroup 2 (P.subgroupOf N) := hP2.comap_of_injective N.subtype N.subtype_injective
  have hO2' : IsPGroup 2 ((pCore 2 Q).subgroupOf N) :=
    pCore_isPGroup.comap_of_injective N.subtype N.subtype_injective
  have hPn : (P.subgroupOf N).Normal := inferInstance
  have hOn : ((pCore 2 Q).subgroupOf N).Normal := pCore_normal.subgroupOf N
  have : Group.IsNilpotent ↥(P.subgroupOf N) := hP2'.isNilpotent
  have : Group.IsNilpotent ↥((pCore 2 Q).subgroupOf N) := hO2'.isNilpotent
  apply CFSG.LocalCores.layer_eq_bot_of_forall
  intro J hJ
  have hJP := (CFSG.LocalCores.component_solvable_centralizer inferInstance
    hPn.isSubnormal).1 J hJ
  have hJO := (CFSG.LocalCores.component_solvable_centralizer inferInstance
    hOn.isSubnormal).1 J hJ
  set C : Subgroup Q := Subgroup.centralizer (generalizedFitting Q : Set Q) with hCdef
  let f : ↥J →* Q := N.subtype.comp J.subtype
  have hf : Function.Injective f := N.subtype_injective.comp J.subtype_injective
  have hodd : ∀ j : ↥J, Odd (orderOf j) → f j ∈ C := by
    intro j hj
    have hjo : Odd (orderOf (f j)) := by
      rw [orderOf_injective f hf]
      exact hj
    have hjP : f j ∈ Subgroup.centralizer (P : Set Q) :=
      coe_mem_centralizer hPN (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJP j.2)
    have hjO : f j ∈ Subgroup.centralizer (pCore 2 Q : Set Q) :=
      coe_mem_centralizer hON (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hJO j.2)
    exact mem_centralizer_generalizedFitting hO hjO (mem_centralizer_layer hSA S hjP hjo)
  have : Group.IsPerfect ↥J := hJ.1.1
  have hJC : ∀ j : ↥J, f j ∈ C := by
    have hle : (⊤ : Subgroup ↥J) ≤ C.comap f := by
      rw [← CFSG.GroupTheory.oddOrderClosure_eq_top_of_isPerfect,
        CFSG.GroupTheory.oddOrderClosure_eq_closure, Subgroup.closure_le]
      rintro j ⟨-, hj⟩
      exact hodd j hj
    exact fun j => hle (Subgroup.mem_top j)
  have hJab : ∀ a b : ↥J, a * b = b * a := fun a b => hf (by
    rw [map_mul, map_mul]
    exact centralizer_generalizedFitting_comm (hJC a) (hJC b))
  obtain ⟨-, -, a, b, hab⟩ := hJ.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hJab a b])

theorem isCharacteristicP_normalizer_inf_layer (hO : pPrimeCore 2 Q = ⊥)
    (hSA : ∀ J : Subgroup Q, IsComponent J → SylowAutTrivial (↥J ⧸ Subgroup.center ↥J))
    (S : Sylow 2 Q) :
    IsCharacteristicP 2
      ↥(Subgroup.normalizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot _ 2
    (pPrimeCore_normalizer_eq_bot hO hSA S) (layer_normalizer_eq_bot hO hSA S)

theorem sylowAutTrivial_of_szSections (hSz : SzSections Q) {J : Subgroup Q} (hJ : IsComponent J) :
    SylowAutTrivial (↥J ⧸ Subgroup.center ↥J) := by
  obtain ⟨a, ha, K, _, _, hK, ⟨e⟩⟩ := hSz J (Subgroup.center ↥J) hJ.1.2.1 hJ.1.2.2
  exact sylowAutTrivial_isSz (f := 2 * a + 1) ⟨rfl, a, ha, K, inferInstance, inferInstance, rfl,
    hK, ⟨e⟩⟩

theorem isCharacteristicP_normalizer_inf_layer_of_szSections (hO : pPrimeCore 2 Q = ⊥)
    (hSz : SzSections Q) (S : Sylow 2 Q) :
    IsCharacteristicP 2
      ↥(Subgroup.normalizer (((S : Subgroup Q) ⊓ layer Q : Subgroup Q) : Set Q)) :=
  isCharacteristicP_normalizer_inf_layer hO (fun _ hJ => sylowAutTrivial_of_szSections hSz hJ) S

end Sylow155E0

end CFSG.RankThree.PartTwo.Sec15
