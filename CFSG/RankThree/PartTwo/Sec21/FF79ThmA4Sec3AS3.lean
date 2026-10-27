module

public import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3AStarDefs

import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41Base
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3AS1
import CFSG.RankThree.PartTwo.Sec21.FF79ThmA4Sec3AS2
import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterInversion
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
open CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
open CFSG.RankThree.PartTwo.Sec21.FF79.AS
open CFSG CFSG.RankThree.PartTwo.Sec21
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]
variable {b : G} {J B A P D S : Subgroup G}

theorem mem_nor_zpowers_of_comm {g : G} (hg : g * b = b * g) : g ∈ Nor (Subgroup.zpowers b) :=
  L41.mem_nor_of_forall fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [((Commute.zpow_right hg k).eq)]; group
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k

theorem mem_nor_sup_of {g : G} {H K : Subgroup G}
    (hH : H ≤ (H ⊔ K).comap (MulAut.conj g).toMonoidHom)
    (hK : K ≤ (H ⊔ K).comap (MulAut.conj g).toMonoidHom) : g ∈ Nor (H ⊔ K) :=
  L41.mem_nor_of_forall fun y hy => by simpa using (sup_le hH hK) hy

theorem comm_b_of_mem_J (h : FF79Sec34Pre4 b J B A P D) {d : G} (hd : d ∈ J) : d * b = b * d :=
  (Subgroup.mem_centralizer_iff.mp ((J_le h) hd) b rfl).symm

theorem exists_S (h : FF79Sec34Pre4 b J B A P D) (hodd : Odd (Nat.card (CenS A))) :
    ∃ S : Subgroup G, IsSylowOf 3 S (CenS A ⊔ Subgroup.zpowers b) ∧ P ≤ S ∧ D ≤ Nor S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : Nat.card ↥(CenS A ⊔ Subgroup.zpowers b) = Nat.card (CenS A) * 3 :=
    card_sup_zpowers (ord_b h) (mem_nor_cenS h.bA) (b_not_cenS h)
  have hM2 : ¬ 2 ∣ Nat.card ↥(CenS A ⊔ Subgroup.zpowers b) := by
    rw [hM, ← even_iff_two_dvd, Nat.not_even_iff_odd]
    exact hodd.mul (by decide)
  have hDM : D ≤ Subgroup.normalizer ((CenS A ⊔ Subgroup.zpowers b : Subgroup G) : Set G) :=
    fun d hd => mem_nor_sup (mem_nor_cenS (h.DA hd))
      (mem_nor_zpowers_of_comm (comm_b_of_mem_J h (h.DJ hd)))
  have hPM : P ≤ CenS A ⊔ Subgroup.zpowers b := by
    rw [h.hP]
    exact sup_le le_sup_right ((A_le_cenS h).trans le_sup_left)
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := fun d hd => by
    rw [h.hP]
    exact mem_nor_sup (mem_nor_zpowers_of_comm (comm_b_of_mem_J h (h.DJ hd))) (h.DA hd)
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [h.D8.1]; norm_num)
  obtain ⟨S, hS, hPS, hDS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_two Nat.prime_three hD2 hM2 hDM hPM h.sylP.2.1 hDP
  exact ⟨S, isSylowOf_of_fusion hS, hPS, hDS⟩

structure AStarCtx (b : G) (J B A P D S : Subgroup G) : Prop where
  pre : FF79Sec34Pre4 b J B A P D
  odd : Odd (Nat.card (CenS A))
  sylS : IsSylowOf 3 S (CenS A ⊔ Subgroup.zpowers b)
  PS : P ≤ S
  DS : D ≤ Nor S

abbrev AStarCtx.As (_ : AStarCtx b J B A P D S) : Subgroup G := S ⊓ CenS A

namespace AStarCtx

variable (c : AStarCtx b J B A P D S)
include c

theorem b_mem_P : b ∈ P := c.pre.hP ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers b)

theorem A_le_P : A ≤ P := c.pre.hP ▸ le_sup_right

theorem b_mem_S : b ∈ S := c.PS c.b_mem_P

theorem S_isPGroup : IsPGroup 3 S := c.sylS.2.1

theorem As_le_S : c.As ≤ S := inf_le_left

theorem As_le_cenS : c.As ≤ CenS A := inf_le_right

theorem A_le_As : A ≤ c.As := le_inf (c.A_le_P.trans c.PS) (A_le_cenS c.pre)

theorem As_isPGroup : IsPGroup 3 c.As := c.S_isPGroup.to_le c.As_le_S

theorem b_nor_As : b ∈ Nor c.As :=
  mem_nor_inf (Subgroup.le_normalizer c.b_mem_S) (mem_nor_cenS c.pre.bA)

theorem D_nor_As : D ≤ Nor c.As := fun _ hd =>
  mem_nor_inf (c.DS hd) (mem_nor_cenS (c.pre.DA hd))

theorem b_not_As : b ∉ c.As := fun hb => b_not_cenS c.pre hb.2

theorem card_facts : Nat.card S = 3 ^ ((Nat.card (CenS A)).factorization 3 + 1) ∧
    Nat.card c.As = 3 ^ (Nat.card (CenS A)).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hM : Nat.card ↥(CenS A ⊔ Subgroup.zpowers b) = Nat.card (CenS A) * 3 :=
    card_sup_zpowers (ord_b c.pre) (mem_nor_cenS c.pre.bA) (b_not_cenS c.pre)
  have hS : Nat.card S = 3 ^ ((Nat.card (CenS A)).factorization 3 + 1) := by
    rw [L41.isSylowOf_card_p c.sylS, hM, Nat.factorization_mul Nat.card_pos.ne' (by norm_num),
      Finsupp.add_apply]
    simp [Nat.Prime.factorization Nat.prime_three]
  refine ⟨hS, ?_⟩
  set v := (Nat.card (CenS A)).factorization 3 with hv
  have hrM : (CenS A).relIndex (CenS A ⊔ Subgroup.zpowers b) = 3 := by
    have h1 := Subgroup.relIndex_mul_card (CenS A) (CenS A ⊔ Subgroup.zpowers b)
    rw [inf_of_le_left le_sup_left, hM] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans (mul_comm _ _))
  have hrS : (CenS A).relIndex S ≤ 3 := by
    rw [← hrM]
    exact Subgroup.relIndex_le_of_le_right c.sylS.1 (by rw [hrM]; norm_num)
  have h2 := Subgroup.relIndex_mul_card (CenS A) S
  rw [inf_comm] at h2
  obtain ⟨j, hj⟩ := c.As_isPGroup.exists_card_eq
  have hjle : j ≤ v := by
    have : 3 ^ j ∣ Nat.card (CenS A) := hj ▸ Subgroup.card_dvd_of_le c.As_le_cenS
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp this
  have hge : 3 ^ (v + 1) ≤ 3 * 3 ^ j := by
    rw [← hS, ← h2, ← hj]
    exact Nat.mul_le_mul_right _ hrS
  have : v ≤ j := by
    rw [pow_succ, mul_comm] at hge
    have := Nat.pow_le_pow_iff_right (show 1 < 3 by norm_num) |>.mp
      (Nat.le_of_mul_le_mul_left hge (by norm_num))
    exact this
  rw [hj, le_antisymm hjle this]

theorem As_sylow : IsSylowOf 3 c.As (CenS A) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact L41.isSylowOf_of_card_p c.As_le_cenS c.card_facts.2

theorem card_S : Nat.card S = 3 * Nat.card c.As := by
  rw [c.card_facts.1, c.card_facts.2, pow_succ, mul_comm]

theorem S_eq : S = c.As ⊔ Subgroup.zpowers b := by
  refine (Subgroup.eq_of_le_of_card_ge (sup_le c.As_le_S ((Subgroup.zpowers_le).mpr c.b_mem_S))
    ?_).symm
  rw [card_sup_zpowers (ord_b c.pre) c.b_nor_As c.b_not_As, c.card_S, mul_comm]

theorem S_le_nor : S ≤ Nor A := by
  rw [c.S_eq]
  exact sup_le (c.As_le_cenS.trans (cenS_le_nor A)) ((Subgroup.zpowers_le).mpr c.pre.bA)

section Z

variable {z : D} (hz : z ∈ Subgroup.center D) (hz1 : z ≠ 1)
include hz hz1

theorem fix_trivial : c.As ⊓ Cen (z : G) = ⊥ := by
  set F := c.As ⊓ Cen (z : G) with hF
  have hbF : b ∈ Nor F := mem_nor_inf c.b_nor_As (mem_nor_cen (z_comm_b c.pre).symm)
  have hbnF : b ∉ F := fun hb => c.b_not_As hb.1
  have hF3 : IsPGroup 3 ↥(F ⊔ Subgroup.zpowers b) :=
    (c.As_isPGroup.to_le inf_le_left).to_sup_of_normal_left'
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ord_b c.pre, pow_one]))
      ((Subgroup.zpowers_le).mpr hbF)
  have hFY : F ⊔ Subgroup.zpowers b ≤ Nor A ⊓ Cen (z : G) := by
    refine sup_le (le_inf (inf_le_left.trans (c.As_le_cenS.trans (cenS_le_nor A)))
      inf_le_right) ((Subgroup.zpowers_le).mpr ⟨c.pre.bA, ?_⟩)
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy; subst hy; exact z_comm_b c.pre
  have h1 := card_le_three_of_Y c.pre hz hz1 hF3 hFY
  rw [card_sup_zpowers (ord_b c.pre) hbF hbnF] at h1
  exact Subgroup.eq_bot_of_card_le _ (by omega)

theorem z_inv_As {s : G} (hs : s ∈ c.As) : (z : G) * s * (z : G)⁻¹ = s⁻¹ := by
  refine CFSG.HardMathSupport.Timmesfeld.SporadicBalance.inv_of_fixedPointFree_involution
    (z_sq c.pre c.odd hz hz1) (fun q hq => ?_) (fun q hq hfix => ?_) s hs
  · exact (Subgroup.mem_normalizer_iff.mp (c.D_nor_As z.2) q).mp hq
  · have hq' : q ∈ c.As ⊓ Cen (z : G) := ⟨hq, Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff] at hy; subst hy; exact (comm_of_conj hfix).symm⟩
    rw [c.fix_trivial hz hz1] at hq'
    exact (Subgroup.mem_bot).mp hq'

theorem As_comm {s t : G} (hs : s ∈ c.As) (ht : t ∈ c.As) : s * t = t * s := by
  have e1 := c.z_inv_As hz hz1 (c.As.mul_mem hs ht)
  have e2 : (z : G) * (s * t) * (z : G)⁻¹ = s⁻¹ * t⁻¹ := by
    rw [← c.z_inv_As hz hz1 hs, ← c.z_inv_As hz hz1 ht]; group
  rw [e1, mul_inv_rev] at e2
  have := congrArg (·⁻¹) e2
  simpa [mul_inv_rev] using this

end Z

theorem exists_z : ∃ z : D, z ∈ Subgroup.center D ∧ z ≠ 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 3) (by rw [c.pre.D8.1]; norm_num)
  haveI : Nontrivial D := by
    rw [← Finite.one_lt_card_iff_nontrivial, c.pre.D8.1]; norm_num
  haveI := hD2.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center D)
  exact ⟨z, z.2, fun e => hz (Subtype.ext e)⟩

theorem As_comm' {s t : G} (hs : s ∈ c.As) (ht : t ∈ c.As) : s * t = t * s := by
  obtain ⟨z, hz, hz1⟩ := c.exists_z
  exact c.As_comm hz hz1 hs ht

theorem P_inf_cenS : P ⊓ CenS A = A := by
  have hcP : Nat.card P = 3 * Nat.card A := by
    rw [c.pre.hP, sup_comm, card_sup_zpowers (ord_b c.pre) c.pre.bA (b_not_A c.pre), mul_comm]
  rcases eq_or_eq_of_card_three_mul (le_inf c.A_le_P (A_le_cenS c.pre)) inf_le_left hcP with
    e | e
  · exact e
  · exfalso
    have : b ∈ P ⊓ CenS A := by rw [e]; exact c.b_mem_P
    exact b_not_cenS c.pre this.2

theorem charA {s : G} (hs : s ∈ c.As) : ⁅⁅s, b⁆, b⁆ = 1 ↔ s ∈ A := by
  constructor
  · intro h1
    set w := ⁅s, b⁆ with hw
    have hwAs : w ∈ c.As := by
      rw [hw, commutatorElement_def]
      have : b * s⁻¹ * b⁻¹ ∈ c.As :=
        (Subgroup.mem_normalizer_iff.mp c.b_nor_As _).mp (c.As.inv_mem hs)
      have e : s * b * s⁻¹ * b⁻¹ = s * (b * s⁻¹ * b⁻¹) := by group
      rw [e]; exact c.As.mul_mem hs this
    have hwb : w * b = b * w := commutatorElement_eq_one_iff_mul_comm.mp h1
    have hwB0 : w ∈ B ⊓ J := mem_B0_of_cen c.pre (c.As_le_cenS hwAs) hwb
      (zpowers_isPGroup_of_mem c.As_isPGroup hwAs)
    have hsC : s ∈ CenS A := c.As_le_cenS hs
    have hsb : s * b * s⁻¹ = w * b := by rw [hw, commutatorElement_def]; group
    have hsfix : ∀ a ∈ A, s * a * s⁻¹ = a := fun a ha => by
      rw [← Subgroup.mem_centralizer_iff.mp hsC a ha]; group
    have hsNB : s ∈ Nor B := by
      rw [← c.pre.supB]
      refine mem_nor_sup_of ((Subgroup.zpowers_le).mpr ?_) fun x hx => ?_
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hsb, c.pre.supB]
        exact B.mul_mem hwB0.1 (b_mem_B c.pre)
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hsfix x (B0_le_A c.pre hx)]
        exact Subgroup.mem_sup_right hx
    have hsNP : s ∈ Nor P := by
      rw [c.pre.hP]
      refine mem_nor_sup_of ((Subgroup.zpowers_le).mpr ?_) fun x hx => ?_
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hsb]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (B0_le_A c.pre hwB0))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
      · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hsfix x hx]
        exact Subgroup.mem_sup_right hx
    have hsP := mem_of_sylowOf_of_mem_nor c.pre.sylP hsNB hsNP
      (zpowers_isPGroup_of_mem c.As_isPGroup hs)
    rw [← c.P_inf_cenS]
    exact ⟨hsP, hsC⟩
  · intro hsA
    have h1 : ⁅b, s⁆ ∈ B ⊓ J := c.pre.commbA ▸
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hsA
    have h2 : ⁅s, b⁆ ∈ B ⊓ J := by rw [← commutatorElement_inv]; exact (B ⊓ J).inv_mem h1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact comm_B c.pre h2.1 (b_mem_B c.pre)

end AStarCtx

end CFSG.RankThree.PartTwo.Sec21.FF79.H4.AS
