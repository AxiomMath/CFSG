module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwenty
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

@[expose] def ggFixingJ {G : Type} [Group G] (L J : Subgroup G) (A : Subgroup (MulAut ↥L)) :
    Subgroup (MulAut ↥L) :=
  A ⊓ ⨅ l : {l : ↥L // (l : G) ∈ J}, MulAction.stabilizer (MulAut ↥L) l.1

theorem ggTBJ_card_fixingJ_mul_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    p ^ 2 * Nat.card ↥(ggFixingJ L J (ggGamma L hN).range) ≤ Nat.card ↥(ggGamma L hN).range := by
  obtain ⟨hp, hBs_ea, hxBs, hLx, hBs4⟩ := GGConfig.tableB_facts hcfg
  have hJ_comp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJ_le_L : J ≤ L := hJ_comp.1.trans inf_le_left
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hB_le_Bs : B ≤ Bs := hcfg.2.1.1
  have hD_le_B : D ≤ B := hcfg.2.2.1.1
  have hD_ea : CFSG.Open.IsElemAbelian p D := hcfg.2.2.1.2.1
  have hcardD : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDBJ : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S :=
    hS.2.2.2.2
  have hNB : B ≤ Subgroup.normalizer (L : Set G) := hB_le_Bs.trans hN
  have hND : D ≤ Subgroup.normalizer (L : Set G) := hD_le_B.trans hNB
  have hB_ea : CFSG.Open.IsElemAbelian p B := CFSG.Open.IsElemAbelian.mono hBs_ea hB_le_Bs
  have hcardB : Nat.card (ggGamma L hNB).range * p = Nat.card B :=
    card_range_ggGamma_mul_of hp hB_ea hxB hx1 hLx hcyc hNB
  have hcardDg : Nat.card (ggGamma L hND).range * p = Nat.card D :=
    card_range_ggGamma_mul_of hp hD_ea hxD hx1 hLx hcyc hND
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcardDg_le : Nat.card (ggGamma L hND).range ≤ p := by
    have h := hcardDg
    rw [hcardD, pow_two] at h
    exact Nat.le_of_mul_le_mul_right h.le hp.pos
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hp4B : p ^ 4 ≤ Nat.card B := by
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
      _ = Nat.card B := hBc.symm
  let A : Subgroup (MulAut ↥L) := (ggGamma L hN).range
  let U : Subgroup (MulAut ↥L) := (ggGamma L hNB).range
  let C : Subgroup (MulAut ↥L) := ggFixingJ L J A
  have hU_eq : U = (ggGamma L hNB).range := rfl
  have hA_eq : A = (ggGamma L hN).range := rfl
  have hC_eq : C = ggFixingJ L J A := rfl
  have hUA : U ≤ A := by
    rw [hU_eq, hA_eq]
    intro u hu
    rw [MonoidHom.mem_range] at hu ⊢
    obtain ⟨b, rfl⟩ := hu
    refine ⟨⟨b, hB_le_Bs b.2⟩, ?_⟩
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [ggGamma_coe, ggGamma_coe]
  have hinf_le : U ⊓ C ≤ (ggGamma L hND).range := by
    intro φ hφ
    obtain ⟨hφU, hφC⟩ := hφ
    have hφU' : φ ∈ (ggGamma L hNB).range := hU_eq ▸ hφU
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hφU'
    have hbD : (b : G) ∈ D := by
      rw [hDBJ]
      refine ⟨b.property, ?_⟩
      change (b : G) ∈ Subgroup.centralizer (J : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hjL : j ∈ L := hJ_le_L hj
      have hφC' : φ ∈ A ⊓ ⨅ l : {l : ↥L // (l : G) ∈ J},
          MulAction.stabilizer (MulAut ↥L) l.1 := hφC
      have hstab := Subgroup.mem_iInf.mp hφC'.2 ⟨⟨j, hjL⟩, by simpa using hj⟩
      rw [MulAction.mem_stabilizer_iff] at hstab
      have hfix' : ggGamma L hNB b ⟨j, hjL⟩ = ⟨j, hjL⟩ := by
        rw [hb]
        simpa using hstab
      have hcoe : b * j * b⁻¹ = j := by
        have h := congrArg (fun z : ↥L => (z : G)) hfix'
        rw [ggGamma_coe] at h
        simpa using h
      rw [eq_comm]
      calc
        b * j = (b * j * b⁻¹) * b := by
          rw [Subgroup.coe_inv]
          group
        _ = j * b := by rw [hcoe]
    refine ⟨⟨(b : G), hbD⟩, ?_⟩
    change (ggGamma L hNB) b = φ
    exact hb
  have hcard_inf_le : Nat.card ↥(U ⊓ C) ≤ p :=
    (Subgroup.card_le_of_le hinf_le).trans hcardDg_le
  have hA_comm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rw [hA_eq]
    intro a ha b hb
    rw [MonoidHom.mem_range] at ha hb
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    calc ggGamma L hN a' * ggGamma L hN b' = ggGamma L hN (a' * b') := by rw [map_mul]
      _ = ggGamma L hN (b' * a') := by rw [hBs_ea.1.is_comm.comm a' b']
      _ = ggGamma L hN b' * ggGamma L hN a' := by rw [map_mul]
  have hcomm : ∀ u ∈ U, ∀ c ∈ C, u * c = c * u := by
    intro u hu c hc
    exact hA_comm u (hUA hu) c hc.1
  have hprod := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U C hcomm
  have hprod1 : Nat.card ↥(U ⊔ C) * Nat.card ↥(U ⊓ C) = Nat.card ↥U * Nat.card ↥C := hprod.1
  have hU_ge : p ^ 3 ≤ Nat.card ↥U := by
    have hcube : p ^ 3 * p = p ^ 4 := by ring
    have h : p ^ 3 * p ≤ Nat.card ↥U * p := by
      rw [hU_eq, hcube, hcardB]
      exact hp4B
    exact Nat.le_of_mul_le_mul_right h hp.pos
  have hUC_le_A : U ⊔ C ≤ A := sup_le hUA inf_le_left
  have hcardUC_le : Nat.card ↥(U ⊔ C) ≤ Nat.card ↥A := Subgroup.card_le_of_le hUC_le_A
  have hkey : p ^ 2 * Nat.card ↥C ≤ Nat.card ↥(U ⊔ C) := by
    have h1 : p ^ 3 * Nat.card ↥C ≤ Nat.card ↥U * Nat.card ↥C :=
      Nat.mul_le_mul_right _ hU_ge
    have h2 : Nat.card ↥U * Nat.card ↥C = Nat.card ↥(U ⊔ C) * Nat.card ↥(U ⊓ C) := hprod1.symm
    have h3 : Nat.card ↥(U ⊔ C) * Nat.card ↥(U ⊓ C) ≤ Nat.card ↥(U ⊔ C) * p :=
      Nat.mul_le_mul_left _ hcard_inf_le
    have h4 : p ^ 3 * Nat.card ↥C ≤ Nat.card ↥(U ⊔ C) * p := by
      calc p ^ 3 * Nat.card ↥C ≤ Nat.card ↥U * Nat.card ↥C := h1
        _ = Nat.card ↥(U ⊔ C) * Nat.card ↥(U ⊓ C) := h2
        _ ≤ Nat.card ↥(U ⊔ C) * p := h3
    have h5 : p ^ 3 * Nat.card ↥C = p ^ 2 * Nat.card ↥C * p := by ring
    rw [h5] at h4
    exact Nat.le_of_mul_le_mul_right h4 hp.pos
  change p ^ 2 * Nat.card ↥C ≤ Nat.card ↥A
  calc p ^ 2 * Nat.card ↥C ≤ Nat.card ↥(U ⊔ C) := hkey
    _ ≤ Nat.card ↥A := hcardUC_le

end CFSG.StandardType

end
