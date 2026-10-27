module

public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS14

open CFSG CFSG.Blueprint

theorem isTripleCover_congr {X X' Y : Type*} [Group X] [Group X'] [Group Y] (e : X ≃* X')
    (h : Sec4.IsTripleCover X Y) : Sec4.IsTripleCover X' Y := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩⟩
  rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]

section Centralizer

variable {X : Type} [Group X] [Finite X]

theorem j2_centralizer_quotient (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X)) ≤
        Subgroup.center ↥(Subgroup.centralizer ({z} : Set X)) ∧
      Nat.card ↥((Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X))) = 3 ∧
      ∃ _ : ((Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X))).Normal,
        Nonempty (↥(Subgroup.centralizer ({z} : Set X)) ⧸
          (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X)) ≃*
            alternatingGroup (Fin 6)) := by
  obtain ⟨P', hzP', hP'z⟩ := hz
  have hZ := Sec14.j2_zpowers_eq h415 hX P' hz1 hzP' ⟨P', hzP', hP'z⟩
  obtain ⟨hZ3, -, hext⟩ := Sec14.j2_sylow_facts h415 hX P'
  rw [← hZ] at hext hZ3
  have hCz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup X) : Set X) =
      Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hCz] at hext
  set C := Subgroup.centralizer ({z} : Set X) with hC
  obtain ⟨K, hK, ⟨eK⟩, ⟨eQ⟩⟩ := hext
  have hZC : Subgroup.zpowers z ≤ C := Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  set N := (Subgroup.zpowers z).subgroupOf C with hN
  have hNc : N ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    change (y : X) * (x : X) = (x : X) * y
    rw [← hk]
    exact (Commute.zpow_right hy k).eq
  have hN3 : Nat.card N = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv]
    exact hZ3
  have hK3 : Nat.card K = 3 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hNK : N = K := by
    by_contra hne
    have hinf : K ⊓ N = ⊥ := by
      have hdvd : Nat.card ↥(K ⊓ N) ∣ 3 := hK3 ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hne
        have h1 : K ⊓ N = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hK3])
        have h2 : K ⊓ N = N := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hN3])
        rw [← h2, h1]
    obtain ⟨⟨x, hxN⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (fun h : N = ⊥ => by rw [h, Subgroup.card_bot] at hN3; exact absurd hN3 (by norm_num))
    have hxK : x ∉ K := fun hxK => hx1 (Subtype.ext (by
      have : x ∈ K ⊓ N := ⟨hxK, hxN⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact this))
    exact hxK (mem_of_mem_center_of_isExtOf eQ (hNc hxN))
  subst hNK
  exact ⟨hNc, hN3, hK, ⟨eQ⟩⟩

theorem j2_centralizer_isPerfect (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Group.IsPerfect ↥(Subgroup.centralizer ({z} : Set X)) := by
  obtain ⟨-, -, hN, ⟨eQ⟩⟩ := j2_centralizer_quotient h415 hX hz1 hz
  obtain ⟨P', hzP', hP'z⟩ := hz
  have hZ := Sec14.j2_zpowers_eq h415 hX P' hz1 hzP' ⟨P', hzP', hP'z⟩
  obtain ⟨⟨hHeis, -⟩, -⟩ := h415 X hX P' _ rfl _ rfl
  obtain ⟨⟨-, hcomm, -, -⟩, -, -⟩ := hHeis
  set C := Subgroup.centralizer ({z} : Set X) with hC
  set N := (Subgroup.zpowers z).subgroupOf C with hNdef
  have hzc : (⟨z, hzP'⟩ : ↥(P' : Subgroup X)) ∈ Subgroup.center ↥(P' : Subgroup X) := by
    have hz' : z ∈ (P' : Subgroup X) ⊓ Subgroup.centralizer ((P' : Subgroup X) : Set X) :=
      hZ ▸ Subgroup.mem_zpowers z
    rw [← Sec14.map_subtype_center_eq] at hz'
    obtain ⟨w, hw, hwz⟩ := hz'
    have : w = ⟨z, hzP'⟩ := Subtype.ext hwz
    rw [← this]
    exact hw
  rw [← hcomm] at hzc
  have hzC : (⟨z, hP'z hzP'⟩ : ↥C) ∈ commutator ↥C := by
    have hmap := Subgroup.map_commutator (⊤ : Subgroup ↥(P' : Subgroup X)) ⊤
      (Subgroup.inclusion hP'z)
    have hle : (commutator ↥(P' : Subgroup X)).map (Subgroup.inclusion hP'z) ≤ commutator ↥C := by
      rw [commutator_def, hmap, commutator_def]
      exact Subgroup.commutator_mono le_top le_top
    exact hle ⟨_, hzc, rfl⟩
  have hNle : N ≤ commutator ↥C := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    have : x = (⟨z, hP'z hzP'⟩ : ↥C) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, ← hk])
    rw [this]
    exact zpow_mem hzC k
  have hA6 := Sec14.alternatingGroup_six_isPerfect
  have hQperf : Group.IsPerfect (↥C ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := eQ.symm.toMonoidHom) eQ.symm.surjective
  have hmapc : (commutator ↥C).map (QuotientGroup.mk' N) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective N), ← commutator_def]
    exact hQperf.commutator_eq_top
  refine ⟨eq_top_iff.mpr fun c _ => ?_⟩
  have hc : QuotientGroup.mk' N c ∈ (commutator ↥C).map (QuotientGroup.mk' N) :=
    hmapc ▸ Subgroup.mem_top _
  obtain ⟨d, hd, hdc⟩ := hc
  have hdN : d⁻¹ * c ∈ N := by
    rw [← QuotientGroup.eq]
    exact hdc
  have : c = d * (d⁻¹ * c) := by group
  rw [this]
  exact mul_mem hd (hNle hdN)

theorem j2_center_centralizer (h415 : Sec4.Item4_15) (hX : Nonempty (X ≃* NativeSporadic.J2))
    {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Subgroup.center ↥(Subgroup.centralizer ({z} : Set X)) =
      (Subgroup.zpowers z).subgroupOf (Subgroup.centralizer ({z} : Set X)) := by
  obtain ⟨hNc, -, hN, ⟨eQ⟩⟩ := j2_centralizer_quotient h415 hX hz1 hz
  exact le_antisymm (fun x hx => mem_of_mem_center_of_isExtOf eQ hx) hNc

theorem j2_centralizer_isTripleCover (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Sec4.IsTripleCover ↥(Subgroup.centralizer ({z} : Set X)) (alternatingGroup (Fin 6)) := by
  obtain ⟨-, hN3, hN, ⟨eQ⟩⟩ := j2_centralizer_quotient h415 hX hz1 hz
  have hc := j2_center_centralizer h415 hX hz1 hz
  exact ⟨hc ▸ hN3, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans eQ⟩⟩

theorem j2_perfectResidual_centralizer_eq_top (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    perfectResidual ↥(Subgroup.centralizer ({z} : Set X)) = ⊤ := by
  have hperf := j2_centralizer_isPerfect h415 hX hz1 hz
  exact top_le_iff.mp ((perfect_residual_transport
    (MonoidHom.id ↥(Subgroup.centralizer ({z} : Set X)))).2.2 ⊤
      (Group.IsPerfect.top_iff.mpr hperf))

theorem j2_perfectResidual_centralizer_isTripleCover (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Sec4.IsTripleCover ↥(perfectResidual ↥(Subgroup.centralizer ({z} : Set X)))
      (alternatingGroup (Fin 6)) := by
  have htop := j2_perfectResidual_centralizer_eq_top h415 hX hz1 hz
  exact isTripleCover_congr
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).symm
    (j2_centralizer_isTripleCover h415 hX hz1 hz)

theorem j2_pCore_two_centralizer_eq_bot (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    CFSG.pCore 2 ↥(Subgroup.centralizer ({z} : Set X)) = ⊥ := by
  obtain ⟨-, hN3, hN, ⟨eQ⟩⟩ := j2_centralizer_quotient h415 hX hz1 hz
  set C := Subgroup.centralizer ({z} : Set X) with hC
  set N := (Subgroup.zpowers z).subgroupOf C with hNdef
  set V := CFSG.pCore 2 ↥C with hV
  have hV2 : IsPGroup 2 V := CFSG.pCore_isPGroup
  have hVn : V.Normal := CFSG.pCore_normal
  set W := (V.map (QuotientGroup.mk' N)).map eQ.toMonoidHom with hW
  have hWn : W.Normal := (Subgroup.Normal.map hVn _ (QuotientGroup.mk'_surjective N)).map _
    eQ.surjective
  have hW2 : IsPGroup 2 W := (hV2.map _).map _
  have hWbot : W = ⊥ := by
    have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by norm_num)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact h
    · exfalso
      rw [h] at hW2
      have h3 : 3 ∣ Nat.card (⊤ : Subgroup (alternatingGroup (Fin 6))) := by
        rw [Subgroup.card_top, card_alternatingGroup_six]
        norm_num
      obtain ⟨k, hk⟩ := hW2.exists_card_eq
      rw [hk] at h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
      norm_num at this
  have hVN : V ≤ N := by
    intro v hv
    have hv' : eQ (QuotientGroup.mk' N v) ∈ W := ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    rw [hWbot, Subgroup.mem_bot, map_eq_one_iff _ eQ.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hv'
    exact hv'
  have hN3' : IsPGroup 3 N := IsPGroup.of_card (n := 1) (by rw [hN3, pow_one])
  refine eq_bot_iff.mpr fun v hv => ?_
  have hbot : V ⊓ N = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact (IsPGroup.disjoint_of_ne 2 3 (by norm_num) V N hV2 hN3').eq_bot
  have : v ∈ V ⊓ N := ⟨hv, hVN hv⟩
  rw [hbot] at this
  exact this

end Centralizer

end CFSG.RankThree.PartTwo.KFacts.KS14
