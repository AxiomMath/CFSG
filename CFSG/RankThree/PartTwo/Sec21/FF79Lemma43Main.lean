module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43Final
import CFSG.RankThree.PartTwo.Sec21.FF79KAutL5
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43A5
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43L3
import CFSG.GF2Type.Smith1979.CaseIIExclL52
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.PartTwo.Sec21.FF79Sec4Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem opp_cenS_le {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂)
    (hX : Odd (Nat.card (Opp 3 (Cen b)))) (e : J ≃* GL (Fin 5) (ZMod 2))
    (hset : setMul3 (Subgroup.zpowers b) (Opp 3 (Cen b)) J = Cen b)
    (hXY : Opp 3 (Cen b) ≤ Opp 3 (CenS B)) : Opp 3 (CenS B) ≤ Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have S := setup_of_sec4 h4 e
  obtain ⟨ho1, ho2, hb₁b₂, hK1⟩ := s43_orders h4
  have hbB : b ∈ B := s43_hbB h4
  have hb₁B : b₁ ∈ B := (Subgroup.mem_inf.mp h4.hb₁).1
  have hb₂B : b₂ ∈ B := (Subgroup.mem_inf.mp h4.hb₂).1
  have hb₁J : b₁ ∈ J := (Subgroup.mem_inf.mp h4.hb₁).2
  have hb₂J : b₂ ∈ J := (Subgroup.mem_inf.mp h4.hb₂).2
  intro y hy
  have hyC : y ∈ CenS B := Subgroup.map_subtype_le _ hy
  have hCb : CenS B ≤ Cen b := Subgroup.centralizer_le (by simpa using hbB)
  have hy' : y ∈ setMul3 (Subgroup.zpowers b) (Opp 3 (Cen b)) J := by
    rw [hset]; exact hCb hyC
  obtain ⟨a, ha, u, hu, j, hj, rfl⟩ := hy'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have huC : u ∈ Cen b := Subgroup.map_subtype_le _ hu
  have hub : b ^ i * u = u * b ^ i := ((show Commute b u from s43_cen_comm huC).zpow_left i).eq
  have huj : u * j = j * u :=
    (Subgroup.mem_centralizer_iff.mp (S.X_le_cenS hX hu) j hj).symm
  have hz : b ^ i * j ∈ Opp 3 (CenS B) := by
    have : b ^ i * j = u⁻¹ * (b ^ i * u * j) := by rw [hub]; group
    rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hXY hu)) hy
  have hzC : b ^ i * j ∈ CenS B := Subgroup.map_subtype_le _ hz
  have hbc : ∀ x ∈ B, Commute (b ^ i) x := fun x hx =>
    ((show Commute b x from s43_Bcomm h4 b hbB x hx).zpow_left i)
  have hjc : ∀ x ∈ B, j * x = x * j := by
    intro x hx
    have h1 : Commute (b ^ i * j) x := (Subgroup.mem_centralizer_iff.mp hzC x hx).symm
    have h2 : Commute ((b ^ i)⁻¹ * (b ^ i * j)) x := (hbc x hx).inv_left.mul_left h1
    have h3 : (b ^ i)⁻¹ * (b ^ i * j) = j := by group
    rw [h3] at h2
    exact h2.eq
  have hy1 : orderOf (e ⟨b₁, hb₁J⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ho1
  have hy2 : orderOf (e ⟨b₂, hb₂J⟩) = 3 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact ho2
  have hyc : e ⟨b₁, hb₁J⟩ * e ⟨b₂, hb₂J⟩ = e ⟨b₂, hb₂J⟩ * e ⟨b₁, hb₁J⟩ := by
    rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext hb₁b₂)
  have hyn : e ⟨b₂, hb₂J⟩ ∉ Subgroup.zpowers (e ⟨b₁, hb₁J⟩) := by
    rintro ⟨k, hk⟩
    apply hK1
    have h' : (⟨b₁, hb₁J⟩ : J) ^ k = ⟨b₂, hb₂J⟩ := by
      apply e.injective
      rw [map_zpow]; exact hk
    exact ⟨k, congrArg Subtype.val h'⟩
  obtain ⟨Q, hQ⟩ := CFSG.RankThree.PartTwo.Sec21.FF79.exists_sylow_zpowers_sup hy1 hy2 hyc hyn
  obtain ⟨-, -, hcent, -⟩ := CFSG.GroupTheory.GL52.syl3_structure Q
  have hwy : ∀ x (hx : x ∈ B) (hxJ : x ∈ J),
      e ⟨j, hj⟩ * e ⟨x, hxJ⟩ = e ⟨x, hxJ⟩ * e ⟨j, hj⟩ := by
    intro x hx hxJ
    rw [← map_mul, ← map_mul]; exact congrArg e (Subtype.ext (hjc x hx))
  have hwQ : e ⟨j, hj⟩ ∈ Subgroup.centralizer (Q : Set (GL (Fin 5) (ZMod 2))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ Subgroup.zpowers (e ⟨b₁, hb₁J⟩) ⊔ Subgroup.zpowers (e ⟨b₂, hb₂J⟩) := by
      rw [← hQ]; exact hh
    have hle : Subgroup.zpowers (e ⟨b₁, hb₁J⟩) ⊔ Subgroup.zpowers (e ⟨b₂, hb₂J⟩) ≤
        Subgroup.centralizer {e ⟨j, hj⟩} := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hwy b₁ hb₁B hb₁J).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]; exact (hwy b₂ hb₂B hb₂J).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh')
  rw [hcent, hQ] at hwQ
  obtain ⟨u₁, hu₁, u₂, hu₂, hw⟩ := s43_mem_sup_of_comm
    (A := Subgroup.zpowers (e ⟨b₁, hb₁J⟩)) (H := Subgroup.zpowers (e ⟨b₂, hb₂J⟩))
    (fun a ha h hh => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (Commute.zpow_right
        (show Commute (e ⟨b₁, hb₁J⟩) (e ⟨b₂, hb₂J⟩) from hyc) l) k)).eq) hwQ
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₁
  obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu₂
  have hjB : j ∈ B := by
    have h1 : (⟨j, hj⟩ : J) = (⟨b₁, hb₁J⟩ : J) ^ k * (⟨b₂, hb₂J⟩ : J) ^ l := by
      apply e.injective
      rw [map_mul, map_zpow, map_zpow]; exact hw
    have h2 : j = b₁ ^ k * b₂ ^ l := congrArg Subtype.val h1
    rw [h2]
    exact B.mul_mem (B.zpow_mem hb₁B k) (B.zpow_mem hb₂B l)
  have hzB : b ^ i * j ∈ B := B.mul_mem (B.zpow_mem hbB i) hjB
  have hz3 : (b ^ i * j) ^ 3 = 1 := by
    haveI := h4.mono.1.1
    exact elemPow_eq_one_of_isElementaryAbelian (A := B) _ hzB
  have hz1 : b ^ i * j = 1 := by
    have h1 : orderOf (⟨b ^ i * j, hz⟩ : Opp 3 (CenS B)) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext hz3)
    have h2 := Subgroup.orderOf_dvd_natCard (Opp 3 (CenS B))
      (show b ^ i * j ∈ Opp 3 (CenS B) from hz)
    rw [Subgroup.orderOf_mk] at h1
    have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (L14.Opp_coprime 3 _)) h2
    have : orderOf (b ^ i * j) = 1 := h3
    exact orderOf_eq_one_iff.mp this
  have : b ^ i * u * j = u := by rw [hub, mul_assoc, hz1, mul_one]
  rw [this]; exact hu

theorem ff79_4_3_of_K (hO5 : FF79KO2L5) (hF5 : FF79KAut5Fix) (hJ5 : FF79_JL5)
    (h14 : FF79_1_4) (h41 : FF79_4_1) (h42 : FF79_4_2Pre) : FF79_4_3 := by
  intro G _ _ b J B b₁ b₂ h4
  have hX := h41 G b J B b₁ b₂ h4
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two (hJ5 G b J h4.hyp)
  have hodd : Odd (Nat.card (CenS B)) := by
    rcases Nat.even_or_odd (Nat.card (CenS B)) with hev | hodd
    · exfalso
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CenS B)) 2
        (even_iff_two_dvd.mp hev)
      have hto : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
      exact no_involution h4 (fun τ hτ hτo => ⟨good_b h4 hX e hO5 hτ hτo,
        good_beta h4 hX e hF5 ff79KO2A5_holds ff79KO2L3_holds h42 hτ hτo⟩) t.2 hto
    · exact hodd
  refine ⟨hodd, ?_⟩
  have h := h14 G 5 (Or.inr rfl) b J h4.hyp B h4.sylB hX (Or.inl hodd)
  dsimp only at h
  obtain ⟨-, -, -, -, -, hdec | hev⟩ := h
  · obtain ⟨hset, hcard⟩ := hdec
    have S := setup_of_sec4 h4 e
    have hXJ := S.X_le_cenS hX
    refine ⟨?_, by rw [hcard]; ring⟩
    ext g
    constructor
    · rintro ⟨a, ha, u, hu, j, hj, rfl⟩
      have : a * u * j ∈ setMul3 (Subgroup.zpowers b) J (Opp 3 (Cen b)) := by
        refine ⟨a, ha, j, hj, u, hu, ?_⟩
        rw [mul_assoc, (Subgroup.mem_centralizer_iff.mp (hXJ hu) j hj).symm, ← mul_assoc]
      rw [hset] at this; exact this
    · intro hg
      rw [← hset] at hg
      obtain ⟨a, ha, j, hj, u, hu, rfl⟩ := hg
      refine ⟨a, ha, u, hu, j, hj, ?_⟩
      rw [mul_assoc, (Subgroup.mem_centralizer_iff.mp (hXJ hu) j hj), ← mul_assoc]
  · exact absurd hev (Nat.not_even_iff_odd.mpr hodd)

theorem ff79_4_2_of_K (hJ5 : FF79_JL5) (_h14 : FF79_1_4) (h41 : FF79_4_1) (h42 : FF79_4_2Pre)
    (h43 : FF79_4_3) : FF79_4_2 := by
  intro G _ _ b J B b₁ b₂ h4
  have hX := h41 G b J B b₁ b₂ h4
  obtain ⟨e⟩ := CFSG.GF2Type.Smith1979.Case2.nonempty_mulEquiv_gl_of_psl_two (hJ5 G b J h4.hyp)
  have h := h42 G b J B b₁ b₂ h4
  dsimp only at h ⊢
  obtain ⟨h1, h2, h3, h4', h5, h6, h7, h8, h9, h10, hO1, hO2⟩ := h
  have hle := opp_cenS_le h4 hX e (h43 G b J B b₁ b₂ h4).2.1 hO2
  exact ⟨h1, h2, h3, h4', h5, h6, h7, h8, h9, h10, (hle.trans hO1.symm.le).antisymm
    (hO1.le.trans hO2), hO1⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
