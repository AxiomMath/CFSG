module

public import CFSG.Quasithin.Vol2.Ch11SecHSchur
public import CFSG.Quasithin.Vol2.Ch11SecHV

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecH

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

namespace Data

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g h y : G}
  (d : Data T L I n V₁ H g h y)
include d

theorem not_fsuV_le_B : ¬ fsuV T I ≤ bOf T I H := by
  intro hle
  have h1 := Subgroup.card_le_of_le hle
  rw [d.card_fsuV] at h1
  have hpos : 0 < Nat.card (bOf T I H) := Nat.card_pos
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by have := d.c.two_le; omega)
  nlinarith

theorem pCoreOf_K_le_P (i : Inp32) : pCoreOf 2 (oTwoUpper H) ≤ pOf T I H h := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kQuot
  have hKP := d.K_le_normalizer_P i
  have hNn : ((pOf T I H h).subgroupOf (oTwoUpper H)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKP
  have hMeq : (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H) = CFSG.pCore 2 ↥(oTwoUpper H) :=
    (SecC.pCore_eq_subgroupOf _).symm
  have hMn : ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)).Normal := by
    rw [hMeq]
    infer_instance
  have hNM : (pOf T I H h).subgroupOf (oTwoUpper H) ≤
      (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (d.inf_P_le i ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩)
  have hperf : Group.IsPerfect ↥(oTwoUpper H) := Subgroup.isPerfect_iff.mpr d.comp.2.1
  have hZc : ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)).map
      (QuotientGroup.mk' ((pOf T I H h).subgroupOf (oTwoUpper H))) ≤
      Subgroup.center (↥(oTwoUpper H) ⧸ (pOf T I H h).subgroupOf (oTwoUpper H)) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    induction z using QuotientGroup.induction_on with
    | H k =>
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hq' := Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mp hq)
      have hk' : ((k : G))⁻¹ ∈ fsuV T I ⊔ conjSubgroup (fsuV T I) h :=
        d.K_le_I i (Subgroup.inv_mem _ k.2)
      have := d.comm_Q_mem_P i hq' hk'
      simpa [mul_assoc] using this
  have hiso : Nonempty ((↥(oTwoUpper H) ⧸ (pOf T I H h).subgroupOf (oTwoUpper H)) ⧸
      ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)).map
        (QuotientGroup.mk' ((pOf T I H h).subgroupOf (oTwoUpper H))) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) :=
    ⟨(QuotientGroup.quotientQuotientEquivQuotient _ _ hNM).trans
      ((QuotientGroup.quotientMulEquivOfEq hMeq).trans e)⟩
  rcases i.hI13 n d.c.two_le F hF _ inferInstance _ hZc hiso with hZ | ⟨-, -, hinv⟩
  · intro x hx
    have hxK : x ∈ oTwoUpper H := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
    have hmem : QuotientGroup.mk' ((pOf T I H h).subgroupOf (oTwoUpper H)) ⟨x, hxK⟩ ∈
        ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)).map
          (QuotientGroup.mk' ((pOf T I H h).subgroupOf (oTwoUpper H))) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · exfalso
    obtain ⟨v, hv, hvB⟩ := Set.not_subset.mp d.not_fsuV_le_B
    obtain ⟨k, hk, b, hb, rfl⟩ := d.exists_decomp i hv
    have hkB : k ∉ bOf T I H := by
      intro hkB
      apply hvB
      rw [d.bOf_eq i] at hkB ⊢
      exact Subgroup.mul_mem _ hkB hb
    have hk2 : (QuotientGroup.mk' ((pOf T I H h).subgroupOf (oTwoUpper H))
        ⟨k, hk.2⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨k, hk.2⟩ : ↥(oTwoUpper H)) ^ 2 = 1 :=
        Subtype.ext (by simpa using (SecA.isElemAbelian_fsuV d.c.s.hyp).2 k hk.1)
      rw [this, map_one]
    obtain ⟨q, hq, hqk⟩ := hinv _ hk2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hqk
    have h1 := Subgroup.mem_subgroupOf.mp (hNM hqk)
    have h2 := Subgroup.mem_subgroupOf.mp hq
    have hkM : k ∈ pCoreOf 2 (oTwoUpper H) := by
      have := (pCoreOf 2 (oTwoUpper H)).mul_mem h2 h1
      simpa using this
    apply hkB
    rw [d.bOf_eq i]
    exact ⟨hk.1, pCoreOf_K_le_pCoreOf_H H hkM⟩

theorem inf_centralizer_P (i : Inp32) (hB : bOf T I H ≠ ⊥) :
    oTwoUpper H ⊓ Subgroup.centralizer (pOf T I H h : Set G) = pCoreOf 2 (oTwoUpper H) := by
  have hPab := d.isElemAbelian_P i
  have hQP := d.pCoreOf_K_le_P i
  have hQC : pCoreOf 2 (oTwoUpper H) ≤ Subgroup.centralizer (pOf T I H h : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact comm_of_isElemAbelian hPab hp (hQP hx)
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hQC)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kQuot
  have hMeq := (SecC.pCore_eq_subgroupOf (oTwoUpper H)).symm
  have hMn : ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)).Normal := by
    rw [hMeq]
    infer_instance
  have : IsSimpleGroup (↥(oTwoUpper H) ⧸ (pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)) := by
    have := SecC.isSimpleGroup_SL2 d.c.two_le hF
    exact ((QuotientGroup.quotientMulEquivOfEq hMeq).trans e).isSimpleGroup
  have hN'n : ((Subgroup.centralizer (pOf T I H h : Set G)).subgroupOf (oTwoUpper H)).Normal := by
    refine ⟨fun a ha k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact conj_mem_centralizer (d.K_le_normalizer_P i k.2) ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (((Subgroup.centralizer (pOf T I H h : Set G)).subgroupOf (oTwoUpper H)).map
        (QuotientGroup.mk' ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)))) with hb | ht
  · rintro x ⟨hxK, hxC⟩
    have hmem : QuotientGroup.mk' ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H)) ⟨x, hxK⟩ ∈
        ((Subgroup.centralizer (pOf T I H h : Set G)).subgroupOf (oTwoUpper H)).map
          (QuotientGroup.mk' ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H))) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hxC)
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · exfalso
    have hKC : oTwoUpper H ≤ Subgroup.centralizer (pOf T I H h : Set G) := by
      intro k hk
      have hmem : QuotientGroup.mk' ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H))
          ⟨k, hk⟩ ∈ ((Subgroup.centralizer (pOf T I H h : Set G)).subgroupOf (oTwoUpper H)).map
            (QuotientGroup.mk' ((pCoreOf 2 (oTwoUpper H)).subgroupOf (oTwoUpper H))) :=
        ht ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hck⟩ := hmem
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hck
      have h1 := hQC (Subgroup.mem_subgroupOf.mp hck)
      have h2 := Subgroup.mem_subgroupOf.mp hc
      have := (Subgroup.centralizer _).mul_mem h2 h1
      simpa using this
    have hBh : conjSubgroup (bOf T I H) h = ⊥ := by
      rw [eq_bot_iff, ← d.Bh_inf_centralizer_V i]
      intro b' hb'
      refine Subgroup.mem_inf.mpr ⟨hb', ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨k, hk, b, hb, rfl⟩ := d.exists_decomp i hv
      have hb'P : b' ∈ pOf T I H h := Subgroup.mem_sup_right hb'
      have h1 : k * b' = b' * k := (Subgroup.mem_centralizer_iff.mp (hKC hk.2) b' hb'P).symm
      have hbP : b ∈ pOf T I H h := Subgroup.mem_sup_left (by rw [d.bOf_eq i]; exact hb)
      have h2 : b * b' = b' * b := comm_of_isElemAbelian hPab hbP hb'P
      calc k * b * b' = k * (b * b') := by group
        _ = k * (b' * b) := by rw [h2]
        _ = k * b' * b := by group
        _ = b' * k * b := by rw [h1]
        _ = b' * (k * b) := by group
    apply hB
    have hc := card_conjSubgroup (bOf T I H) h
    rw [hBh, Subgroup.card_bot] at hc
    exact Subgroup.eq_bot_of_card_eq _ hc.symm

theorem gm_equiv (i : Inp32) (hB : bOf T I H ≠ ⊥) : ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧ Nonempty (↥(autOn (oTwoUpper H) (pOf T I H h)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := d.kQuot
  have hKP := d.K_le_normalizer_P i
  have hker : (SecC.autOnHom (oTwoUpper H) (pOf T I H h) hKP).ker =
      CFSG.pCore 2 ↥(oTwoUpper H) := by
    rw [SecC.ker_autOnHom, ← Subgroup.inf_subgroupOf_left, d.inf_centralizer_P i hB,
      ← SecC.pCore_eq_subgroupOf]
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨(SecC.autOnEquiv _ _ hKP).trans ((QuotientGroup.quotientMulEquivOfEq hker).trans e)⟩⟩

end Data

end CFSG.Quasithin.Vol2.Ch11.SecH
