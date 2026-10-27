module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Sp6Core
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixModelTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem sylowOf_ge {p : ℕ} [Fact p.Prime] {K Q : Subgroup G} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P K ∧ Q ≤ P := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩,
    fun x hx => ⟨⟨x, hQK hx⟩, hS hx, rfl⟩⟩

private theorem sylowOf_exists_mem_conj {p : ℕ} [Fact p.Prime] {P P' K : Subgroup G}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (h' : CFSG.ABGLocalTools.IsSylowOf p P' K) :
    ∃ k ∈ K, ∀ x : G, x ∈ P' ↔ k⁻¹ * x * k ∈ P := by
  obtain ⟨Q, rfl⟩ := h
  obtain ⟨Q', rfl⟩ := h'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q Q'
  have key : ∀ y : K, y ∈ (Q' : Subgroup K) ↔ g⁻¹ * y * g ∈ (Q : Subgroup K) := by
    intro y
    rw [← hg]
    change y ∈ MulAut.conj g • (Q : Subgroup K) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (key y).mp hy, by simp⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : (z : G) = (g : G)⁻¹ * x * g := hzx
    have hx : x = (g : G) * z * (g : G)⁻¹ := by rw [hzx']; group
    have hxK : x ∈ K := by
      rw [hx]
      exact K.mul_mem (K.mul_mem g.2 z.2) (K.inv_mem g.2)
    refine ⟨⟨x, hxK⟩, (key _).mpr ?_, rfl⟩
    have : g⁻¹ * ⟨x, hxK⟩ * g = z := Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hzx'.symm)
    rw [this]
    exact hz

private theorem pullSub_conj_mem_of_mem_normalizer {G₀ X : Type*} [Group G₀] [Group X]
    {Lsub : Subgroup G₀} (φ : Lsub ≃* X) {R : Subgroup X} {a b : G₀}
    (ha : a ∈ pullSub φ (Subgroup.normalizer (R : Set X)))
    (hb : b ∈ pullSub φ R) : a * b * a⁻¹ ∈ pullSub φ R := by
  obtain ⟨haL, haN⟩ := mem_pullSub.1 ha
  obtain ⟨hbL, hbR⟩ := mem_pullSub.1 hb
  refine mem_pullSub.2 ⟨mul_mem (mul_mem haL hbL) (inv_mem haL), ?_⟩
  have hsub : (⟨a * b * a⁻¹, mul_mem (mul_mem haL hbL) (inv_mem haL)⟩ : Lsub) =
      ⟨a, haL⟩ * ⟨b, hbL⟩ * ⟨a, haL⟩⁻¹ := Subtype.ext rfl
  rw [hsub, map_mul, map_mul, map_inv]
  exact (Subgroup.mem_normalizer_iff.1 haN _).1 hbR

theorem c8_mem_pullSub_range_of_sq_eq_one (D : Data G) {V₀ V L T' : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil V₀ V)
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' D.M)
    (ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)))
    (hTP : barSub V₀ V hV T' ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (hTR : ∀ t ∈ T', t ^ 2 = 1 → ∀ ht : t ∈ stabTil V₀ V,
      actTil V₀ V hV ⟨t, ht⟩ ∈ pullSub ψ (tauSym 3).range)
    {x : G} (hxM : x ∈ D.M) (hx2 : x ^ 2 = 1)
    (hxP : actTil V₀ V hV ⟨x, hMs hxM⟩ ∈
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3))) :
    actTil V₀ V hV ⟨x, hMs hxM⟩ ∈ pullSub ψ (tauSym 3).range := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G :=
    D.M ⊓ ((pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3))).comap
      (actTil V₀ V hV)).map (stabTil V₀ V).subtype with hH
  have hTH : T' ≤ H := by
    rw [hH]
    intro t htT'
    have htM : t ∈ D.M := CFSG.ABGLocalTools.IsSylowOf.le hT' htT'
    have hts : t ∈ stabTil V₀ V := hMs htM
    have htbar : actTil V₀ V hV ⟨t, hts⟩ ∈
        pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) :=
      hTP (actTil_mem_barSub V₀ V hV htT' hts)
    exact ⟨htM, Subgroup.mem_map.2 ⟨⟨t, hts⟩, Subgroup.mem_comap.2 htbar, rfl⟩⟩
  have hHM : H ≤ D.M := by rw [hH]; exact inf_le_left
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 2 T' H :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hT' hTH hHM
  have hxH : x ∈ H := by
    rw [hH]
    exact ⟨hxM, Subgroup.mem_map.2 ⟨⟨x, hMs hxM⟩, Subgroup.mem_comap.2 hxP, rfl⟩⟩
  have hQ : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]
      simpa using (orderOf_dvd_iff_pow_eq_one (x := x) (n := 2)).2 hx2)
  obtain ⟨S, hSylS, hQS⟩ :=
    sylowOf_ge (K := H) (Q := Subgroup.zpowers x) (Subgroup.zpowers_le.2 hxH) hQ
  obtain ⟨k, hkH, hconj⟩ := sylowOf_exists_mem_conj (K := H) hSylH hSylS
  have hxS : x ∈ S := hQS (Subgroup.mem_zpowers x)
  have hkxT : k⁻¹ * x * k ∈ T' := (hconj x).1 hxS
  have hkM : k ∈ D.M := hHM hkH
  have hks : k ∈ stabTil V₀ V := hMs hkM
  have hkP : actTil V₀ V hV ⟨k, hks⟩ ∈
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
    have hkH' := hkH
    rw [hH] at hkH'
    obtain ⟨-, hksub⟩ := Subgroup.mem_inf.1 hkH'
    obtain ⟨ks, hksP, hksk⟩ := Subgroup.mem_map.1 hksub
    have hkeq : (⟨k, hks⟩ : ↥(stabTil V₀ V)) = ks := Subtype.ext hksk.symm
    rw [hkeq]
    exact hksP
  set t : G := k⁻¹ * x * k with ht
  have htT : t ∈ T' := by rw [ht]; exact hkxT
  have htM : t ∈ D.M := CFSG.ABGLocalTools.IsSylowOf.le hT' htT
  have hts : t ∈ stabTil V₀ V := hMs htM
  have hkx2 : (k⁻¹ * x * k) ^ 2 = 1 := by
    rw [pow_two]
    calc (k⁻¹ * x * k) * (k⁻¹ * x * k) = k⁻¹ * (x * x) * k := by group
      _ = k⁻¹ * 1 * k := by rw [← pow_two, hx2]
      _ = 1 := by group
  have ht2 : t ^ 2 = 1 := by rw [ht]; exact hkx2
  have hx_eq : (⟨x, hMs hxM⟩ : ↥(stabTil V₀ V)) =
      ⟨k, hks⟩ * ⟨t, hts⟩ * ⟨k, hks⟩⁻¹ := by
    apply Subtype.ext
    show x = k * t * k⁻¹
    rw [ht]
    group
  have heq : actTil V₀ V hV ⟨x, hMs hxM⟩ =
      actTil V₀ V hV ⟨k, hks⟩ * actTil V₀ V hV ⟨t, hts⟩ *
        (actTil V₀ V hV ⟨k, hks⟩)⁻¹ := by
    rw [hx_eq, map_mul, map_mul, map_inv]
  have hconjmem : actTil V₀ V hV ⟨k, hks⟩ * actTil V₀ V hV ⟨t, hts⟩ *
      (actTil V₀ V hV ⟨k, hks⟩)⁻¹ ∈ pullSub ψ (tauSym 3).range :=
    pullSub_conj_mem_of_mem_normalizer ψ
      (by rw [normalizer_range_tauSym]; exact hkP) (hTR t htT ht2 hts)
  rw [heq]
  exact hconjmem

theorem c8_rank_eq_one_of_sq_eq_one (D : Data G) {V₀ V L T' : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil V₀ V)
    (hM : Mbar D.M V₀ V hV = lBar V₀ V hV L) (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' D.M)
    (ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)))
    (hTP : barSub V₀ V hV T' ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (hTR : ∀ t ∈ T', t ^ 2 = 1 → ∀ ht : t ∈ stabTil V₀ V,
      actTil V₀ V hV ⟨t, ht⟩ ∈ pullSub ψ (tauSym 3).range)
    {x : G} (hxM : x ∈ D.M) (hx2 : x ^ 2 = 1) (y : ↥(lBar V₀ V hV L))
    (hxy : actTil V₀ V hV ⟨x, hMs hxM⟩ = y) (hyR : ψ y ∈ (tauSym 3).range) (hy1 : y ≠ 1) :
    (spMatrixOf (ψ y) - 1).rank = 1 := by
  obtain ⟨B, hB⟩ := hyR
  rw [← hB, c8_rank_tauSym_sub_one B]
  by_contra hrank
  have hB1 : B ≠ 1 := by
    intro h
    apply hy1
    have : ψ y = 1 := by rw [← hB, h, map_one]
    exact ψ.injective (by rw [this, map_one])
  obtain ⟨k, hkmem, hknot⟩ := c8_exists_conj_mem_stabilizer_not_mem_range B hB1 hrank
  have hM' : barSub V₀ V hV D.M = lBar V₀ V hV L := hM
  set k' : ↥(lBar V₀ V hV L) := ψ.symm k with hk'
  have hk'ψ : ψ k' = k := by rw [hk']; exact MulEquiv.apply_symm_apply ψ k
  have hk'bar : (k' : MulAut (Vtil V₀ V hV)) ∈ barSub V₀ V hV D.M :=
    le_of_eq hM'.symm k'.2
  obtain ⟨g, hgM, hgact⟩ := (mem_barSub V₀ V hV D.M (k' : MulAut (Vtil V₀ V hV))).1 hk'bar
  set x' : G := (g : G) * x * (g : G)⁻¹ with hx'def
  have hx'M : x' ∈ D.M := by
    rw [hx'def]
    exact D.M.mul_mem (D.M.mul_mem hgM hxM) (D.M.inv_mem hgM)
  have hx'2 : x' ^ 2 = 1 := by
    rw [hx'def, pow_two]
    calc (g : G) * x * (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹)
        = (g : G) * (x * x) * (g : G)⁻¹ := by group
      _ = (g : G) * 1 * (g : G)⁻¹ := by rw [← pow_two, hx2]
      _ = 1 := by group
  have hx'sub : (⟨x', hMs hx'M⟩ : ↥(stabTil V₀ V)) = g * ⟨x, hMs hxM⟩ * g⁻¹ :=
    Subtype.ext rfl
  have hact : actTil V₀ V hV ⟨x', hMs hx'M⟩ =
      (k' : MulAut (Vtil V₀ V hV)) * y * (k' : MulAut (Vtil V₀ V hV))⁻¹ := by
    rw [hx'sub, map_mul, map_mul, map_inv, hgact, hxy]
  have hx'lbar : actTil V₀ V hV ⟨x', hMs hx'M⟩ ∈ lBar V₀ V hV L := by
    have hb : actTil V₀ V hV ⟨x', hMs hx'M⟩ ∈ barSub V₀ V hV D.M :=
      actTil_mem_barSub V₀ V hV hx'M (hMs hx'M)
    rw [hM'] at hb
    exact hb
  have hψval : ψ ⟨actTil V₀ V hV ⟨x', hMs hx'M⟩, hx'lbar⟩ = k * tauSym 3 B * k⁻¹ := by
    have hsub : (⟨actTil V₀ V hV ⟨x', hMs hx'M⟩, hx'lbar⟩ : ↥(lBar V₀ V hV L)) =
        k' * y * k'⁻¹ := Subtype.ext hact
    rw [hsub, map_mul, map_mul, map_inv, hk'ψ, ← hB]
  have hx'P : actTil V₀ V hV ⟨x', hMs hx'M⟩ ∈
      pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)) := by
    refine mem_pullSub.2 ⟨hx'lbar, ?_⟩
    rw [hψval]
    exact hkmem
  have hx'R : actTil V₀ V hV ⟨x', hMs hx'M⟩ ∈ pullSub ψ (tauSym 3).range :=
    c8_mem_pullSub_range_of_sq_eq_one D hMs hT' ψ hTP hTR hx'M hx'2 hx'P
  obtain ⟨hmem, hRm⟩ := mem_pullSub.1 hx'R
  have hψsame : ψ ⟨actTil V₀ V hV ⟨x', hMs hx'M⟩, hx'lbar⟩ =
      ψ ⟨actTil V₀ V hV ⟨x', hMs hx'M⟩, hmem⟩ :=
    congrArg ψ (Subtype.ext rfl)
  have hkR : k * tauSym 3 B * k⁻¹ ∈ (tauSym 3).range := by
    rw [← hψval, hψsame]
    exact hRm
  exact hknot hkR

private theorem exists_actTil_of_mem_barSub (D : Data G) {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil V₀ V) {A T' : Subgroup G}
    (hAT : A ≤ T') (hT'M : T' ≤ D.M) (hA : IsElemAbelian 2 A)
    {z : MulAut (Vtil V₀ V hV)} (hz : z ∈ barSub V₀ V hV A) :
    ∃ (x : G) (hxM : x ∈ D.M), x ∈ A ∧ x ^ 2 = 1 ∧
      actTil V₀ V hV ⟨x, hMs hxM⟩ = z := by
  obtain ⟨g, hgA, hgz⟩ := (mem_barSub V₀ V hV A z).1 hz
  have hxM : (g : G) ∈ D.M := hT'M (hAT hgA)
  refine ⟨(g : G), hxM, hgA, hA.2 _ hgA, ?_⟩
  have hge : (⟨(g : G), hMs hxM⟩ : ↥(stabTil V₀ V)) = g := Subtype.ext rfl
  rw [hge, hgz]

theorem c8_barSub_eq_bot_or_zpowers (D : Data G) {V₀ V L T' : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil V₀ V)
    (hM : Mbar D.M V₀ V hV = lBar V₀ V hV L) (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' D.M)
    (ψ : ↥(lBar V₀ V hV L) ≃* ↥(StatedSp 3 (ZMod 2)))
    (hTP : barSub V₀ V hV T' ≤ pullSub ψ (stabilizer 3 (ZMod 2) (lagrangianZero 3)))
    (hTR : ∀ t ∈ T', t ^ 2 = 1 → ∀ ht : t ∈ stabTil V₀ V,
      actTil V₀ V hV ⟨t, ht⟩ ∈ pullSub ψ (tauSym 3).range)
    {A : Subgroup G} (hAT : A ≤ T') (hA : IsElemAbelian 2 A) :
    barSub V₀ V hV A = ⊥ ∨
      ∃ a : ↥(lBar V₀ V hV L), (spMatrixOf (ψ a) - 1).rank = 1 ∧
        barSub V₀ V hV A = Subgroup.zpowers (a : MulAut (Vtil V₀ V hV)) := by
  have hT'M : T' ≤ D.M := CFSG.ABGLocalTools.IsSylowOf.le hT'
  have hbar_le : barSub V₀ V hV A ≤ pullSub ψ (tauSym 3).range := by
    intro z hz
    obtain ⟨x, hxM, hxA, hx2, hxz⟩ := exists_actTil_of_mem_barSub D hMs hAT hT'M hA hz
    rw [← hxz]
    exact hTR x (hAT hxA) hx2 (hMs hxM)
  have hbar_le_lBar : barSub V₀ V hV A ≤ lBar V₀ V hV L :=
    hbar_le.trans (pullSub_le ψ _)
  rcases Subgroup.bot_or_exists_ne_one (barSub V₀ V hV A) with hbot | ⟨a₀, ha₀, ha₀1⟩
  · exact Or.inl hbot
  · set a : ↥(lBar V₀ V hV L) := ⟨a₀, hbar_le_lBar ha₀⟩ with ha
    have haR : ψ a ∈ (tauSym 3).range := by
      obtain ⟨hmem, hR⟩ := mem_pullSub.1 (hbar_le ha₀)
      have haeq : a = ⟨a₀, hmem⟩ := Subtype.ext rfl
      rwa [haeq]
    have ha1 : a ≠ 1 := by
      intro h
      apply ha₀1
      have := congrArg (fun z : ↥(lBar V₀ V hV L) => (z : MulAut (Vtil V₀ V hV))) h
      simpa [ha] using this
    obtain ⟨xa, hxaM, hxaA, hxa2, hxaz⟩ := exists_actTil_of_mem_barSub D hMs hAT hT'M hA ha₀
    have hranka : (spMatrixOf (ψ a) - 1).rank = 1 :=
      c8_rank_eq_one_of_sq_eq_one D hMs hM hT' ψ hTP hTR hxaM hxa2 a hxaz haR ha1
    refine Or.inr ⟨a, hranka, ?_⟩
    have hzp_le : Subgroup.zpowers (a : MulAut (Vtil V₀ V hV)) ≤ barSub V₀ V hV A := by
      refine Subgroup.zpowers_le.2 ?_
      simpa [ha] using ha₀
    refine le_antisymm ?_ hzp_le
    intro b₀ hb₀
    by_cases hb1 : b₀ = 1
    · rw [hb1]; exact Subgroup.one_mem _
    · by_cases hba : b₀ = a₀
      · rw [hba]
        exact Subgroup.mem_zpowers (a : MulAut (Vtil V₀ V hV))
      · exfalso
        have hinv : a₀⁻¹ = a₀ := by
          have ha₀sq : a₀ ^ 2 = 1 := by
            obtain ⟨x, hxM, hxA, hx2, hxz⟩ :=
              exists_actTil_of_mem_barSub D hMs hAT hT'M hA ha₀
            have hg2 : (⟨x, hMs hxM⟩ : ↥(stabTil V₀ V)) ^ 2 = 1 := Subtype.ext (by
              simp only [Subgroup.coe_pow, Subgroup.coe_one]
              exact hx2)
            rw [← hxz, ← map_pow, hg2, map_one]
          exact mul_eq_one_iff_inv_eq.1 (by rwa [pow_two] at ha₀sq)
        have hc01 : a₀ * b₀ ≠ 1 := by
          intro h
          apply hba
          have : b₀ = a₀⁻¹ := (mul_eq_one_iff_eq_inv').1 h
          rw [this, hinv]
        set b : ↥(lBar V₀ V hV L) := ⟨b₀, hbar_le_lBar hb₀⟩ with hb
        have hbR : ψ b ∈ (tauSym 3).range := by
          obtain ⟨hmem, hR⟩ := mem_pullSub.1 (hbar_le hb₀)
          have hbeq : b = ⟨b₀, hmem⟩ := Subtype.ext rfl
          rwa [hbeq]
        have hb1' : b ≠ 1 := by
          intro h
          apply hb1
          have := congrArg (fun z : ↥(lBar V₀ V hV L) => (z : MulAut (Vtil V₀ V hV))) h
          simpa [hb] using this
        obtain ⟨xb, hxbM, hxbA, hxb2, hxbz⟩ :=
          exists_actTil_of_mem_barSub D hMs hAT hT'M hA hb₀
        have hrankb : (spMatrixOf (ψ b) - 1).rank = 1 :=
          c8_rank_eq_one_of_sq_eq_one D hMs hM hT' ψ hTP hTR hxbM hxb2 b hxbz hbR hb1'
        have hc0mem : a₀ * b₀ ∈ barSub V₀ V hV A := mul_mem ha₀ hb₀
        set c : ↥(lBar V₀ V hV L) := ⟨a₀ * b₀, hbar_le_lBar hc0mem⟩ with hc
        have hcR : ψ c ∈ (tauSym 3).range := by
          obtain ⟨hmem, hR⟩ := mem_pullSub.1 (hbar_le hc0mem)
          have hceq : c = ⟨a₀ * b₀, hmem⟩ := Subtype.ext rfl
          rwa [hceq]
        have hc1' : c ≠ 1 := by
          intro h
          apply hc01
          have := congrArg (fun z : ↥(lBar V₀ V hV L) => (z : MulAut (Vtil V₀ V hV))) h
          simpa [hc] using this
        obtain ⟨xc, hxcM, hxcA, hxc2, hxcz⟩ :=
          exists_actTil_of_mem_barSub D hMs hAT hT'M hA hc0mem
        have hrankc : (spMatrixOf (ψ c) - 1).rank = 1 :=
          c8_rank_eq_one_of_sq_eq_one D hMs hM hT' ψ hTP hTR hxcM hxc2 c hxcz hcR hc1'
        obtain ⟨B₁, hB₁⟩ := haR
        obtain ⟨B₂, hB₂⟩ := hbR
        have hB₁rank : ((B₁.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))).rank = 1 := by
          rw [← c8_rank_tauSym_sub_one B₁, hB₁]
          exact hranka
        have hB₂rank : ((B₂.toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2))).rank = 1 := by
          rw [← c8_rank_tauSym_sub_one B₂, hB₂]
          exact hrankb
        have hBne : B₁ ≠ B₂ := by
          intro hBB
          have hab : a = b := ψ.injective (by rw [← hB₁, ← hB₂, hBB])
          apply hba
          simpa [ha, hb] using congrArg
            (fun z : ↥(lBar V₀ V hV L) => (z : MulAut (Vtil V₀ V hV))) hab.symm
        have hc_eq : ψ c = tauSym 3 (B₁ * B₂) := by
          have hcab : c = a * b := Subtype.ext rfl
          rw [hcab, map_mul, ← hB₁, ← hB₂, ← map_mul]
        have hcrank : ((B₁ * B₂).toAdd : Matrix (Fin 3) (Fin 3) (ZMod 2)).rank = 1 := by
          rw [← c8_rank_tauSym_sub_one (B₁ * B₂), ← hc_eq]
          exact hrankc
        exact (c8_rank_mul_ne_one hB₁rank hB₂rank hBne) hcrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
