module

public import CFSG.Quasithin.Vol2.Ch11SecOE7L

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def centQuot (H X R : Subgroup G) (hXH : H ≤ Subgroup.normalizer (X : Set G))
    (hRH : H ≤ Subgroup.normalizer (R : Set G)) : Subgroup G where
  carrier := {g | g ∈ H ∧ ∀ y ∈ X, ⁅g, y⁆ ∈ R}
  one_mem' := ⟨H.one_mem, fun y _ => by simp [R.one_mem]⟩
  mul_mem' := by
    rintro g g' ⟨hg, hgR⟩ ⟨hg', hg'R⟩
    refine ⟨H.mul_mem hg hg', fun y hy => ?_⟩
    have h1 : ⁅g * g', y⁆ = g * ⁅g', y⁆ * g⁻¹ * ⁅g, y⁆ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact R.mul_mem ((Subgroup.mem_normalizer_iff.mp (hRH hg) _).mp (hg'R y hy)) (hgR y hy)
  inv_mem' := by
    rintro g ⟨hg, hgR⟩
    refine ⟨H.inv_mem hg, fun y hy => ?_⟩
    have hz : g⁻¹ * y * g⁻¹⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hXH (H.inv_mem hg)) y).mp hy
    have h1 : ⁅g⁻¹, y⁆ = (⁅g, g⁻¹ * y * g⁻¹⁻¹⁆)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    exact R.inv_mem (hgR _ hz)

theorem inEFor_top_of_quot_sl2_family {n : ℕ} {ι : Type*} {T : Subgroup G} (X : ι → Subgroup G)
    (hT : IsSylowIn 2 T ⊤) (hn : 2 ≤ n) (hTX : ∀ i, T ≤ Subgroup.normalizer (X i : Set G))
    (hφ : ∀ i, ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (φ : ↥(X i) →* SL(2, F)), Function.Surjective φ ∧ IsPGroup 2 φ.ker ∧ Nat.card F = 2 ^ n)
    (hgen : (⨆ i, X i) ⊔ T = ⊤) : E1.InEFor n ⊤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro Ω hΩ
  refine eq_top_iff.mpr (hgen.symm.trans_le ?_)
  refine sup_le (iSup_le fun i => ?_) fun x hx =>
    Subgroup.mem_sup_right ⟨Subgroup.mem_top x, E1.le_normalizer_weakClosure hΩ hx⟩
  obtain ⟨F, _, _, _, φ, hφs, hker, hF⟩ := hφ i
  have hF4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  set R : Subgroup G := φ.ker.map (X i).subtype with hRdef
  set H := (X i) ⊔ T with hHdef
  have hTH : IsSylowIn 2 T H := B6.isSylowTwoOf_mono hT le_sup_right le_top
  have hHN : H ≤ Subgroup.normalizer ((X i) : Set G) := sup_le Subgroup.le_normalizer (hTX i)
  have hXsyl : IsSylowIn 2 (T ⊓ (X i)) (X i) := by
    have h1 := B6.isSylowTwoOf_inf_normal (⟨hTH.1, hTH.2.1, hTH.2.2⟩ :
      QuasithinUnique.IsSylowTwoOf T H) le_sup_left hHN
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  have hRc : R = (CFSG.Open.pCore 2 ↥(X i)).map (X i).subtype := by
    rw [hRdef, ker_eq_pCore φ hφs hker hF4]
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := by
    have : (CFSG.Open.pCore 2 ↥(X i)).Characteristic :=
      CFSG.LieType.BorelTits.pCore_characteristic 2
    rw [hRc]
    exact hHN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  by_cases hc : ∃ A ∈ Ω, A ≤ T ∧ ¬ ∀ a ∈ A, ∀ x ∈ (X i), ⁅a, x⁆ ∈ R
  · obtain ⟨A, hA, hAT, hAC⟩ := hc
    have hmem := isE_sup_tauOf_of_quot_sl2 hT hAT (hΩ.isElemAbelian A hA) φ hφs hker hF hF4
      ((E1.tauOf_le _ _ _).trans (hTX i)) hXsyl hAC
    exact le_sup_left.trans ((E1.le_eGen hA hAT hmem).trans le_sup_left)
  · push Not at hc
    set C := centQuot H (X i) R hHN hHR with hCdef
    have hZ := SecE3.center_eq_bot_of_simple (SecE3.sl2_nonabelian (K := F))
    have hCX : ∀ y ∈ C, y ∈ (X i) → y ∈ R := by
      intro y hy hyX
      have hc : φ ⟨y, hyX⟩ ∈ Subgroup.center SL(2, F) := by
        rw [Subgroup.mem_center_iff]
        intro s
        obtain ⟨z, rfl⟩ := hφs s
        have h1 := hy.2 z z.2
        rw [hRdef] at h1
        obtain ⟨w, hw, hwz⟩ := h1
        have hw' : w = ⁅(⟨y, hyX⟩ : ↥(X i)), z⁆ := Subtype.ext hwz
        have hw2 : φ ⁅(⟨y, hyX⟩ : ↥(X i)), z⁆ = 1 := by rw [← hw']; exact hw
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv] at hw2
        calc φ z * φ ⟨y, hyX⟩ = (φ ⟨y, hyX⟩ * φ z * (φ ⟨y, hyX⟩)⁻¹ * (φ z)⁻¹)⁻¹ *
              (φ ⟨y, hyX⟩ * φ z) := by group
          _ = φ ⟨y, hyX⟩ * φ z := by rw [hw2, inv_one, one_mul]
      rw [hZ, Subgroup.mem_bot] at hc
      exact ⟨⟨y, hyX⟩, hc, rfl⟩
    have hCH : C ≤ H := fun y hy => hy.1
    have hCn : (C.subgroupOf H).Normal := by
      refine ⟨fun c hc h => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      refine ⟨H.mul_mem (H.mul_mem h.2 hc.1) (H.inv_mem h.2), fun y hy => ?_⟩
      have hz : (h : G)⁻¹ * y * (h : G)⁻¹⁻¹ ∈ (X i) :=
        (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem h.2)) y).mp hy
      have h1 : ⁅(h : G) * c * (h : G)⁻¹, y⁆ =
          (h : G) * ⁅(c : G), (h : G)⁻¹ * y * (h : G)⁻¹⁻¹⁆ * (h : G)⁻¹ := by
        simp only [commutatorElement_def]
        group
      push_cast
      rw [h1]
      exact (Subgroup.mem_normalizer_iff.mp (hHR h.2) _).mp (hc.2 _ hz)
    have hτ' : IsPGroup 2 ↥(T.subgroupOf H) :=
      hT.2.1.comap_of_injective H.subtype H.subtype_injective
    have hC2 : IsPGroup 2 ↥C := by
      intro c
      have hcH : (c : G) ∈ (X i) ⊔ T := hCH c.2
      have hXHn : ((X i).subgroupOf H).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hHN
      have hsup : (X i).subgroupOf H ⊔ T.subgroupOf H = ⊤ :=
        (Subgroup.codisjoint_subgroupOf_sup (X i) T).eq_top
      have hq : (⟨c, hcH⟩ : ↥H) ∈ (X i).subgroupOf H ⊔ T.subgroupOf H := hsup ▸ Subgroup.mem_top _
      obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp hq
      obtain ⟨k, hk⟩ := hτ' ⟨z, hz⟩
      have hck : ((⟨c, hcH⟩ : ↥H)) ^ 2 ^ k ∈ (X i).subgroupOf H := by
        rw [← hyz, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
          (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
          show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk,
          QuotientGroup.mk_one]
      have hckX : (c : G) ^ 2 ^ k ∈ (X i) := by simpa [Subgroup.mem_subgroupOf] using hck
      have hckR : (c : G) ^ 2 ^ k ∈ R := hCX _ (C.pow_mem c.2 _) hckX
      obtain ⟨b, hb⟩ := (hker.map (X i).subtype) ⟨_, hckR⟩
      refine ⟨k + b, Subtype.ext ?_⟩
      have hb' : ((c : G) ^ 2 ^ k) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      rw [← pow_mul, ← pow_add] at hb'
      simpa using hb'
    have hCT : C ≤ T := hTH.le_of_normal hCH hCn hC2
    have hWC : E1.weakClosure T Ω ≤ C := by
      refine iSup₂_le fun A hA => iSup_le fun hAT a ha => ?_
      exact ⟨(le_sup_right : T ≤ H) (hAT ha), hc A hA hAT a ha⟩
    intro x hx
    refine Subgroup.mem_sup_right ⟨Subgroup.mem_top x, ?_⟩
    refine E1.mem_normalizer_weakClosure hΩ fun w hw => hCT ?_
    have h1 := hCn.conj_mem ⟨w, hCH (hWC hw)⟩ (by rw [Subgroup.mem_subgroupOf]; exact hWC hw)
      ⟨x, (le_sup_left : X i ≤ H) hx⟩
    rwa [Subgroup.mem_subgroupOf] at h1

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
