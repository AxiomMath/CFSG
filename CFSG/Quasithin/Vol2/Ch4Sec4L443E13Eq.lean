module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E7Le
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E9Mp

public section

namespace CFSG.Quasithin.H13.Ch4.E443

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.A4
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}

theorem conjClosure_eq_of_quasisimple (s : Setting443 G T M L B Tp VB) (h37 : A37ForSQTK)
    (h39 : A39ForSQTK)
    (hq : CFSG.IsQuasisimple
      (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))))) :
    conjClosure L T = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Mp := conjClosure L T with hMp
  set Q := pCoreOf 2 Mp with hQ
  set LB := perfectCore (Mp ⊓ Subgroup.centralizer (B : Set G)) with hLB
  have h := s.hyp421
  have hMpN : Mp ≤ Subgroup.normalizer (L : Set G) :=
    conjClosure_le_normalizer_of_hyp421 h h37 h39
  have hLMp : L ≤ Mp := le_conjClosure L T
  have hLBMp : LB ≤ Mp := LB_le L T B
  have hQN : Mp ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 Mp
  have h445 : Mp = LB ⊔ Q := lemma_4_4_5_orbit s.hyp.toHyp4_4_1TwoOrbit
  have hO2 : pCoreOf 2 LB ≤ Q := pCoreOf_LB_le s
  have hXN : Mp ≤ Subgroup.normalizer ((L ⊔ Q : Subgroup G) : Set G) := fun x hx =>
    (mem_normalizer_inf_sup (hMpN hx) (hQN hx)).2
  have : Group.IsPerfect ↥LB := Subgroup.isPerfect_iff.mpr (perfectCore_perfect _)
  have : ((L ⊔ Q).subgroupOf LB).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hLBMp.trans hXN)
  rcases le_center_or_eq_top_of_isQuasisimple hq
      (((L ⊔ Q).subgroupOf LB).map (QuotientGroup.mk' (CFSG.pCore 2 ↥LB))) with hc | ht
  · exfalso
    have hcomm : ∀ a ∈ LB, a ∈ L ⊔ Q → ∀ b ∈ LB, ⁅a, b⁆ ∈ Q := by
      intro a ha haX b hb
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥LB) ⟨a, ha⟩ ∈ Subgroup.center _ :=
        hc ⟨_, haX, rfl⟩
      have h1 : ⁅(⟨a, ha⟩ : ↥LB), ⟨b, hb⟩⁆ ∈ CFSG.pCore 2 ↥LB := by
        rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥LB), MonoidHom.mem_ker, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hmem _).symm
      exact hO2 ((coe_mem_pCoreOf_two_iff _).mpr h1)
    have hLBN : LB ≤ Subgroup.normalizer (Q : Set G) := hLBMp.trans hQN
    have hLBZ : LB ≤ centralizerSection ⊤ L Q := by
      refine fun b hb => ⟨Subgroup.mem_top b, hMpN (hLBMp hb), hLBN hb, fun l hl => ?_⟩
      have hl' : l ∈ (LB : Set G) * (Q : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right LB Q hLBN, ← h445]
        exact hLMp hl
      obtain ⟨a, ha, q, hq, rfl⟩ := hl'
      have haX : a ∈ L ⊔ Q := by
        have e : a = a * q * q⁻¹ := by group
        rw [e]
        exact (L ⊔ Q).mul_mem (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right (Q.inv_mem hq))
      have hqb : q * (b * q⁻¹ * b⁻¹) ∈ Q :=
        Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hLBN hb) q⁻¹).mp (Q.inv_mem hq))
      have h1 : a * (q * (b * q⁻¹ * b⁻¹)) * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hLBN ha) _).mp hqb
      have e : a * q * b * (a * q)⁻¹ * b⁻¹ = a * (q * (b * q⁻¹ * b⁻¹)) * a⁻¹ * ⁅a, b⁆ := by
        rw [commutatorElement_def]
        group
      change a * q * b * (a * q)⁻¹ * b⁻¹ ∈ Q
      rw [e]
      exact Q.mul_mem h1 (hcomm a ha haX b hb)
    have hQZ : Q ≤ centralizerSection ⊤ L Q := by
      refine fun q hq => ⟨Subgroup.mem_top q, hMpN (pCoreOf_le 2 Mp hq), hQN (pCoreOf_le 2 Mp hq),
        fun l hl => ?_⟩
      exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQN (hLMp hl)) q).mp hq) (Q.inv_mem hq)
    have hLQ : L ≤ Q := by
      have hLZ : L ≤ centralizerSection ⊤ L Q := hLMp.trans (h445.le.trans (sup_le hLBZ hQZ))
      calc L = ⁅L, L⁆ := h.perfect.symm
        _ ≤ Q := Subgroup.commutator_le.mpr fun l hl l' hl' => (hLZ hl').2.2.2 l hl
    have hLO : L ≤ pCoreOf 2 L :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl (fun x hx => Subgroup.le_normalizer hx)
        ((pCoreOf_isPGroup 2 Mp).to_le hLQ)
    obtain ⟨x, y, hxy⟩ :=
      (CFSG.LocalCores.isQuasisimple_nontrivial s.hyp.quasisimple).exists_pair_ne
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    refine hxy (QuotientGroup.eq.mpr ((coe_mem_pCoreOf_two_iff _).mp (hLO ?_)))
    exact (x⁻¹ * y).2
  ·
    have hsup : (L ⊔ Q).subgroupOf LB ⊔ CFSG.pCore 2 ↥LB = ⊤ := by
      have hcomap :=
        Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 ↥LB)) ((L ⊔ Q).subgroupOf LB)
      rw [ht, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have htop := eq_top_of_sup_isPGroup_eq_top CFSG.pCore_isPGroup hsup
    have hLBX : LB ≤ L ⊔ Q := fun a ha => by
      have : (⟨a, ha⟩ : ↥LB) ∈ (L ⊔ Q).subgroupOf LB := htop ▸ Subgroup.mem_top _
      exact this
    have hMpX : Mp ≤ L ⊔ Q := h445.le.trans (sup_le hLBX le_sup_right)
    have hXL : (L.subgroupOf (L ⊔ Q)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer ((sup_le hLMp (pCoreOf_le 2 Mp)).trans hMpN)
    have : Group.IsNilpotent ↥Q := (pCoreOf_isPGroup 2 Mp).isNilpotent
    have hperf : ∀ P : Subgroup G, P ≤ Mp → ⁅P, P⁆ = P → P ≤ L := fun P hP hPP =>
      (le_perfectCore_of_perfect (hP.trans hMpX) hPP).trans
        (perfectCore_le_of_sup_solvable le_sup_left hXL rfl inferInstance)
    refine le_antisymm (conjClosure_le fun t ht l hl => ?_) hLMp
    have hP : L.map (MulAut.conj t).toMonoidHom ≤ Mp := by
      rintro _ ⟨l', hl', rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L T ht) l').mp (hLMp hl')
    have hPP : ⁅L.map (MulAut.conj t).toMonoidHom, L.map (MulAut.conj t).toMonoidHom⁆ =
        L.map (MulAut.conj t).toMonoidHom := by
      rw [← Subgroup.map_commutator, h.perfect]
    exact hperf _ hP hPP ⟨l, hl, rfl⟩

theorem le_normalizer_of_quasisimple (s : Setting443 G T M L B Tp VB) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hq : CFSG.IsQuasisimple
      (↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))) ⧸
        CFSG.pCore 2 ↥(perfectCore (conjClosure L T ⊓ Subgroup.centralizer (B : Set G))))) :
    M ≤ Subgroup.normalizer (L : Set G) := by
  have h := s.hyp421.le_normalizer_conjClosure h37 h38 h39
  rwa [conjClosure_eq_of_quasisimple s h37 h39 hq] at h

end CFSG.Quasithin.H13.Ch4.E443
