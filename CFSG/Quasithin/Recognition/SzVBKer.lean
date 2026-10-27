module

public import CFSG.Quasithin.Recognition.SzVBFam
public import CFSG.Quasithin.Recognition.SzVBBenderData
public import CFSG.Quasithin.Recognition.SzVBKerAux
public import CFSG.Quasithin.Background.Harris.R1.Fam
public import CFSG.Quasithin.Recognition.SzVBOdd

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

omit [Finite G] in
theorem kerAct_normal (P V : Subgroup G) : (kerAct P V).Normal := by
  unfold kerAct
  infer_instance

omit [Finite G] in
theorem normalizer_of_mem_kerAct {P V : Subgroup G} {y : ↥P} (hy : y ∈ kerAct P V) :
    (y : G) ∈ Subgroup.normalizer (V : Set G) := by
  have h2 : (y • ConjSet.base P V : ConjSet P V).1 = (ConjSet.base P V).1 :=
    congrArg Subtype.val ((OddAux.mem_kerAct.mp hy) (ConjSet.base P V))
  rw [ConjSet.smul_val] at h2
  have h1 : conjSub (y : G) V = V := h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have e : (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * (y : G) = x := by group
  have h3 : ∀ z : G, z ∈ conjSub (y : G) V ↔ z ∈ V := fun z => by rw [h1]
  rw [← h3 ((y : G) * x * (y : G)⁻¹), mem_conjSub, e]

theorem comm_mem_pCoreOf_of_mem_kerAct (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1)) {P : Subgroup G} (hK1P : K1 ≤ P)
    (hPN : P ≤ Subgroup.normalizer (K1 : Set G)) {y k : G}
    (hy : y ∈ (kerAct P (conjClosure Zs L2)).map P.subtype) (hk : k ∈ K1) :
    y * k * y⁻¹ * k⁻¹ ∈ pCoreOf 2 K1 := by
  obtain ⟨K, _, ψ, e, i, hψ, hker, hB, -⟩ := exists_benderData hn hX
  have : Finite K := Finite.of_surjective (ψ.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1)))
    (hψ.comp (QuotientGroup.mk'_surjective _))
  have : IsSimpleGroup K := hB.isSimple
  have hR : Hyp111R K1 L2 S := F112J2.hyp111R_of_setting hRO h
  have hSyl : IsSylowTwoOf (S ⊓ K1) K1 := h.hyp.h1.sylow
  have : (kerAct P (conjClosure Zs L2)).Normal := kerAct_normal _ _
  have : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp h.cComp_mem)
  set Y₀ : Subgroup G := (kerAct P (conjClosure Zs L2)).map P.subtype with hY₀
  have hYconj : ∀ p ∈ P, ∀ z ∈ Y₀, p * z * p⁻¹ ∈ Y₀ := fun p hp z hz =>
    KerAux.conj_mem_map_subtype (kerAct P (conjClosure Zs L2)) hp hz
  have hYB : ∀ z ∈ Y₀, z ∈ K1 → z ∈ borelOf K1 S := by
    rintro z ⟨z', hz', rfl⟩ hzK
    rw [← inf_normalizer_eq_borelOf hRO h]
    exact ⟨hzK, normalizer_of_mem_kerAct hz'⟩
  have hO2 : CFSG.Open.pCore 2 ↥K1 ≤ (S ⊓ K1).subgroupOf K1 := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    exact F7.isSylowTwoOf_pCoreOf_le hSyl ⟨z, hz, rfl⟩
  have hT : Subgroup.normalizer (((S ⊓ K1).subgroupOf K1 : Subgroup ↥K1) : Set ↥K1) ≠ ⊤ := by
    intro htop
    apply hR.r1.borel_ne
    refine inf_eq_left.mpr fun z hz => ?_
    have hz' : (⟨z, hz⟩ : ↥K1) ∈
        Subgroup.normalizer (((S ⊓ K1).subgroupOf K1 : Subgroup ↥K1) : Set ↥K1) := by
      rw [htop]
      exact Subgroup.mem_top _
    have hb := (Background.Harris.R1.mem_borelOf_iff_mem_normalizer (S := S) ⟨z, hz⟩).mpr hz'
    rw [borelOf, Subgroup.mem_inf] at hb
    exact hb.2
  have hRn : ((Y₀ ⊓ K1).subgroupOf K1).Normal :=
    ⟨fun r hr a => by
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      exact ⟨hYconj (a : G) (hK1P a.2) r hr.1, (a * r * a⁻¹).2⟩⟩
  have hRT : (Y₀ ⊓ K1).subgroupOf K1 ≤
      Subgroup.normalizer (((S ⊓ K1).subgroupOf K1 : Subgroup ↥K1) : Set ↥K1) := by
    intro r hr
    rw [Subgroup.mem_subgroupOf] at hr
    exact (Background.Harris.R1.mem_borelOf_iff_mem_normalizer (S := S) r).mp
      (hYB r hr.1 hr.2)
  have hyP : y ∈ P := Subgroup.map_subtype_le _ hy
  have hyK : ∀ z : ↥K1, y * z * y⁻¹ ∈ K1 := fun z =>
    (Subgroup.mem_normalizer_iff.mp (hPN hyP) z).mp z.2
  let φ : ↥K1 →* ↥K1 := MonoidHom.mk' (fun z => (⟨y * z * y⁻¹, hyK z⟩ : ↥K1)) (fun a b => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group)
  have hφ : ∀ z : ↥K1, φ z * z⁻¹ ∈ (Y₀ ⊓ K1).subgroupOf K1 := by
    intro z
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, (φ z * z⁻¹).2⟩
    have e : y * (z : G) * y⁻¹ * (z : G)⁻¹ = y * ((z : G) * y * (z : G)⁻¹)⁻¹ := by group
    show y * (z : G) * y⁻¹ * (z : G)⁻¹ ∈ Y₀
    rw [e]
    exact Y₀.mul_mem hy (Y₀.inv_mem (hYconj (z : G) (hK1P z.2) y hy))
  have key := KerAux.comm_mem_of_perfect (N := CFSG.Open.pCore 2 ↥K1) hO2 ψ hψ hker hT hRT φ hφ
    ⟨k, hk⟩
  exact ⟨_, key, rfl⟩

theorem ker_inv_le_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1)) :
    ∀ x : ↥(K1 ⊔ S), x * x = 1 → x ∈ kerAct (K1 ⊔ S) (conjClosure Zs L2) →
      (x : G) ∈ pCoreOf 2 (K1 ⊔ S) := by
  intro x hx2 hxY
  have hSK : S ≤ Subgroup.normalizer (K1 : Set G) := h.hyp.h1.normalizes
  have hSyl : IsSylowTwoOf (S ⊓ K1) K1 := h.hyp.h1.sylow
  have hK1P : K1 ≤ K1 ⊔ S := le_sup_left
  have hPN : K1 ⊔ S ≤ Subgroup.normalizer (K1 : Set G) := sup_le Subgroup.le_normalizer hSK
  have : (kerAct (K1 ⊔ S) (conjClosure Zs L2)).Normal := kerAct_normal _ _
  have hOT : pCoreOf 2 K1 ≤ S ⊓ K1 := F7.isSylowTwoOf_pCoreOf_le hSyl
  have hstar : ∀ z ∈ (kerAct (K1 ⊔ S) (conjClosure Zs L2)).map (K1 ⊔ S).subtype,
      z * z = 1 → z ∈ S := fun z hz hz2 =>
    KerAux.mem_of_sq_eq_one hSK hSyl.2.2 hOT (Subgroup.map_subtype_le _)
      (fun y hy k hk => comm_mem_pCoreOf_of_mem_kerAct hRO h hn hX hK1P hPN hy hk) hz hz2
  have hcore : x ∈ (S.subgroupOf (K1 ⊔ S)).normalCore := by
    intro b
    rw [Subgroup.mem_subgroupOf]
    have hmem : ((b * x * b⁻¹ : ↥(K1 ⊔ S)) : G) ∈
        (kerAct (K1 ⊔ S) (conjClosure Zs L2)).map (K1 ⊔ S).subtype :=
      ⟨b * x * b⁻¹, Subgroup.Normal.conj_mem inferInstance x hxY b, rfl⟩
    have e : (b * x * b⁻¹) * (b * x * b⁻¹) = (1 : ↥(K1 ⊔ S)) := by
      calc (b * x * b⁻¹) * (b * x * b⁻¹) = b * (x * x) * b⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    exact hstar _ hmem (congrArg Subtype.val e)
  have hpg : IsPGroup 2 (S.subgroupOf (K1 ⊔ S)) := h.hyp.h1.pgroup.comap_subtype
  have hpc : x ∈ CFSG.Open.pCore 2 ↥(K1 ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCore 2 (Subgroup.normalCore_normal _)
      (hpg.to_le (Subgroup.normalCore_le _)) hcore
  exact ⟨x, hpc, rfl⟩

end CFSG.Quasithin.SzVB
