module

public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.Quasithin.Vol2.F134LieL3
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.H13.NQCore.X27L3

open CFSG.Quasithin CFSG.Quasithin.P134 CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.F134 CFSG.Quasithin.F134.LieL3
open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.SteinbergBS
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {K : Type} [Field K]

theorem projPerm_fix_basePt27 [Finite K] {Q : Subgroup (projectiveSL 3 K)}
    (hQ : Nat.card Q ∣ 27) (hK6 : 6 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8) (hK26 : Nat.card K ≠ 26)
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {x : projectiveSL 3 K} (hx : x ∈ Q) :
    projPerm 3 K x (basePt K) = basePt K := by
  classical
  set O : Set (ℙ K (Fin 3 → K)) := {p | ∃ y ∈ Q, projPerm 3 K y (basePt K) = p} with hOdef
  have hOdvd : O.ncard ∣ 27 := by
    let _ : MulAction Q (ℙ K (Fin 3 → K)) :=
      MulAction.compHom _ ((projPerm 3 K).comp Q.subtype)
    have h1 : O = MulAction.orbit Q (basePt K) := by
      ext p
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact ⟨y, y.2, rfl⟩
    rw [h1, ← MulAction.index_stabilizer]
    exact (Subgroup.index_dvd_card _).trans hQ
  have hOle : O.ncard ≤ 27 := Nat.le_of_dvd (by norm_num) hOdvd
  have hbase : basePt K ∈ O := ⟨1, Q.one_mem, by rw [map_one, Equiv.Perm.one_apply]⟩
  have hinv : ∀ u ∈ projUnitriangular 3 K, ∀ p ∈ O, projPerm 3 K u p ∈ O := by
    rintro u hu _ ⟨y, hy, rfl⟩
    obtain ⟨y', hy', s, hs, hus⟩ := hQU u hu y hy
    refine ⟨y', hy', ?_⟩
    rw [← Equiv.Perm.mul_apply, ← map_mul, hus, map_mul, Equiv.Perm.mul_apply,
      projPerm_basePt_of_mem hs]
  have hoff : ∀ a b, offPt a b ∉ O := by
    intro a b hab
    have hall : ∀ a' b', offPt a' b' ∈ O := by
      intro a' b'
      have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular (b' - b) (a' - a) 0)) _ hab
      rwa [projPerm_proj, up3_smul_offPt, add_sub_cancel, add_sub_cancel] at this
    have hsub : insert (basePt K) (Set.range fun p : K × K => offPt p.1 p.2) ⊆ O := by
      rintro _ (rfl | ⟨⟨a', b'⟩, rfl⟩)
      · exact hbase
      · exact hall a' b'
    have hcard := Set.ncard_le_ncard hsub (Set.toFinite O)
    rw [Set.ncard_insert_of_notMem (by rintro ⟨⟨a', b'⟩, h⟩; exact basePt_ne_offPt a' b' h.symm)
      (Set.toFinite _), Set.ncard_range_of_injective offPt_injective, Nat.card_prod] at hcard
    have : 36 ≤ Nat.card K * Nat.card K := Nat.mul_le_mul hK6 hK6
    omega
  have hline : ∀ a, linePt a ∉ O := by
    intro a ha
    have hall : ∀ a', linePt a' ∈ O := by
      intro a'
      have := hinv _ (Subgroup.mem_map_of_mem _ (up3_mem_unitriangular 0 0 (a' - a))) _ ha
      rwa [projPerm_proj, up3_smul_linePt, add_sub_cancel] at this
    have hO : O = insert (basePt K) (Set.range linePt) := by
      apply le_antisymm
      · intro p hp
        rcases point_cases p with rfl | ⟨a', rfl⟩ | ⟨a', b', rfl⟩
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ ⟨a', rfl⟩
        · exact absurd hp (hoff a' b')
      · rintro _ (rfl | ⟨a', rfl⟩)
        · exact hbase
        · exact hall a'
    rw [hO, Set.ncard_insert_of_notMem (by rintro ⟨a', h⟩; exact basePt_ne_linePt a' h.symm)
      (Set.toFinite _), Set.ncard_range_of_injective linePt_injective] at hOdvd
    have hle : Nat.card K ≤ 26 := by
      have := Nat.le_of_dvd (by norm_num) hOdvd
      omega
    obtain ⟨q, hq⟩ : ∃ q, Nat.card K = q := ⟨_, rfl⟩
    rw [hq] at hOdvd hle hK6 hK8 hK26
    interval_cases q <;> omega
  have hxO : projPerm 3 K x (basePt K) ∈ O := ⟨x, hx, rfl⟩
  rcases point_cases (projPerm 3 K x (basePt K)) with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · exact h
  · exact absurd (h ▸ hxO) (hline a)
  · exact absurd (h ▸ hxO) (hoff a b)

theorem mem_upperTriangular_of_le27 [Finite K] [CharP K 2] {Q : Subgroup (projectiveSL 3 K)}
    (hQ : Nat.card Q ∣ 27) (hK6 : 6 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8)
    (hK26 : Nat.card K ≠ 26)
    (hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q, ∃ y ∈ Q, ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s) {g : SL(3, K)} (hg : proj 3 K g ∈ Q) : g ∈ upperTriangular 3 K := by
  obtain ⟨h10, h20⟩ :=
    entries_of_smul_basePt (projPerm_fix_basePt27 hQ hK6 hK8 hK26 hQU hg)
  set Q' := Q.map (gammaZero K).toMonoidHom with hQ'def
  have hγU := map_projUnitriangular_gammaZero (F := K)
  have hQ'card : Nat.card Q' ∣ 27 := by
    rw [hQ'def, Subgroup.card_map_of_injective (gammaZero K).injective]
    exact hQ
  have hQ'U : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ Q', ∃ y ∈ Q', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    rintro u hu _ ⟨x, hx, rfl⟩
    rw [← hγU] at hu
    obtain ⟨u₀, hu₀, rfl⟩ := hu
    obtain ⟨y, hy, s, hs, hus⟩ := hQU u₀ hu₀ x hx
    refine ⟨gammaZero K y, ⟨y, hy, rfl⟩, gammaZero K s, ?_, ?_⟩
    · rw [← hγU]
      exact ⟨s, hs, rfl⟩
    · change gammaZero K u₀ * gammaZero K x = gammaZero K y * gammaZero K s
      rw [← map_mul, hus, map_mul]
  obtain ⟨h, hh, h1, h2⟩ := gammaZero_proj_inv g
  have hhQ' : proj 3 K h ∈ Q' := by
    rw [← hh, map_inv]
    exact ⟨_, Q.inv_mem hg, rfl⟩
  obtain ⟨h10', h20'⟩ :=
    entries_of_smul_basePt (projPerm_fix_basePt27 hQ'card hK6 hK8 hK26 hQ'U hhQ')
  rw [h1] at h10'
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

theorem proj_commutator_mem {g h : SL(3, K)} (hg : g ∈ upperTriangular 3 K)
    (hh : h ∈ upperTriangular 3 K) :
    proj 3 K (g * h * g⁻¹ * h⁻¹) ∈ projUnitriangular 3 K := by
  have hm : g * h * g⁻¹ * h⁻¹ ∈ upperTriangular 3 K :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hd : ∀ i : Fin 3, ((g * h * g⁻¹ * h⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i i = 1 := by
    intro i
    have he : (⟨g * h * g⁻¹ * h⁻¹, hm⟩ : upperTriangular 3 K) =
        ⟨g, hg⟩ * ⟨h, hh⟩ * (⟨g, hg⟩)⁻¹ * (⟨h, hh⟩)⁻¹ := rfl
    have h1 : diagUnit i (⟨g * h * g⁻¹ * h⁻¹, hm⟩ : upperTriangular 3 K) = 1 := by
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (diagUnit i ⟨g, hg⟩),
        mul_assoc, mul_assoc, mul_inv_cancel_left, mul_inv_cancel]
    have h2 := congrArg (fun u : Kˣ => (u : K)) h1
    simpa [coe_diagUnit] using h2
  exact proj_mem_projUnitriangular hm ((hd 0).trans (hd 1).symm) ((hd 1).trans (hd 2).symm)

theorem false_of_x27Config {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    [Finite K] [CharP K 2] (hK6 : 6 ≤ Nat.card K) (hK8 : Nat.card K ≠ 8)
    (hK26 : Nat.card K ≠ 26) (e₁ : ↥L ≃* projectiveSL 3 K) (hcfg : OddConfig 3 L P T)
    (h27 : Nat.card P = 27) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := OddConfig.isSylowTwoOf_inf hcfg
  set UL : Subgroup L := (T ⊓ L).subgroupOf L with hULdef
  have hUL2 : IsPGroup 2 UL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hU1 : IsPGroup 2 (UL.map e₁.toMonoidHom) := hUL2.map _
  have hU1i : ¬ 2 ∣ (UL.map e₁.toMonoidHom).index := by
    rw [show UL.map e₁.toMonoidHom = UL.map (e₁ : ↥L →* projectiveSL 3 K) from rfl,
      Subgroup.index_map_equiv]
    exact hS.2.2
  obtain ⟨S₀, hS₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) S₀ (hU1.toSylow hU1i)
  have hmem : ∀ z, z ∈ UL.map e₁.toMonoidHom ↔ g⁻¹ * z * g ∈ projUnitriangular 3 K := by
    intro z
    have h1 : UL.map e₁.toMonoidHom = ((g • S₀ : Sylow 2 (projectiveSL 3 K)) :
        Subgroup (projectiveSL 3 K)) := by
      rw [hg]
      rfl
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hS₀]
  set e : ↥L ≃* projectiveSL 3 K := e₁.trans (MulAut.conj g⁻¹) with hedef
  have he : ∀ y : L, e y = g⁻¹ * e₁ y * g := fun y => by
    rw [hedef, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hUe : UL.map e.toMonoidHom = projUnitriangular 3 K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e y ∈ _
      rw [he]
      exact (hmem _).mp ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, hye⟩ := (hmem (g * x * g⁻¹)).mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x
        by group])
      refine ⟨y, hy, ?_⟩
      change e y = x
      rw [he]
      change e₁ y = g * x * g⁻¹ at hye
      rw [hye]
      group
  set P' : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e.toMonoidHom with hP'def
  have hP'card : Nat.card P' = 27 := by
    rw [hP'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, h27]
  have hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ P', ∃ y ∈ P', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    intro u hu x hx
    rw [← hUe] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y, hy, s, hs, hys⟩ := OddConfig.mul_inf hcfg u' (Subgroup.mem_subgroupOf.mp hu') x'
      (Subgroup.mem_subgroupOf.mp hx')
    refine ⟨e ⟨y, hcfg.le hy⟩, ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩,
      e ⟨s, hs.2⟩, ?_, ?_⟩
    · rw [← hUe]
      exact ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    · change e u' * e x' = e ⟨y, hcfg.le hy⟩ * e ⟨s, hs.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hys
  have hPB : ∀ g : SL(3, K), proj 3 K g ∈ P' → g ∈ upperTriangular 3 K :=
    fun g hg => mem_upperTriangular_of_le27 (by rw [hP'card]) hK6 hK8 hK26 hQU hg
  have hPU : P' ⊓ projUnitriangular 3 K = ⊥ := by
    have := Fintype.ofFinite K
    obtain ⟨k, -, hk⟩ := FiniteField.card K 2
    rw [← Nat.card_eq_fintype_card] at hk
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hP'card, card_projUnitriangular, hk, ← pow_mul]
    exact Nat.Coprime.pow_right _ (by norm_num)
  have hP'ab : ∀ x ∈ P', ∀ y ∈ P', x * y = y * x := by
    intro x hx y hy
    obtain ⟨g₁, rfl⟩ := proj_surjective 3 K x
    obtain ⟨g₂, rfl⟩ := proj_surjective 3 K y
    have hc : proj 3 K (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) ∈ P' ⊓ projUnitriangular 3 K := by
      refine ⟨?_, proj_commutator_mem (hPB g₁ hx) (hPB g₂ hy)⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact P'.mul_mem (P'.mul_mem (P'.mul_mem hx hy) (P'.inv_mem hx)) (P'.inv_mem hy)
    rw [hPU, Subgroup.mem_bot, map_mul, map_mul, map_mul, map_inv, map_inv] at hc
    calc proj 3 K g₁ * proj 3 K g₂
        = proj 3 K g₁ * proj 3 K g₂ * (proj 3 K g₁)⁻¹ * (proj 3 K g₂)⁻¹ *
            (proj 3 K g₂ * proj 3 K g₁) := by group
      _ = proj 3 K g₂ * proj 3 K g₁ := by rw [hc, one_mul]
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    have hea : e ⟨a, hcfg.le ha⟩ ∈ P' := ⟨⟨a, hcfg.le ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    have heb : e ⟨b, hcfg.le hb⟩ ∈ P' := ⟨⟨b, hcfg.le hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
    have h1 := hP'ab _ hea _ heb
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (e.injective h1)
  have hrank : Open.pRank 3 (⊤ : Subgroup A) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hcfg.hyp.sqt) 3 Nat.prime_three (by norm_num)
  obtain ⟨E, hEP, hE, hE9⟩ := exists_elemAbelian_sq hcfg.exp (by rw [h27]; norm_num)
  obtain ⟨x, hxP, hxE⟩ : ∃ x ∈ P, x ∉ E := by
    by_contra hall
    push Not at hall
    have hle : Nat.card P ≤ Nat.card E := Subgroup.card_le_of_le hall
    rw [h27, hE9] at hle
    norm_num at hle
  exact false_of_commute' hrank hE hE9 hxE (hcfg.exp x hxP)
    fun a ha => hPab a (hEP ha) x hxP

theorem false_of_e9Cfg {A : Type} [Group A] [Finite A] {L P T : Subgroup A}
    [Finite K] [CharP K 2] (hK2 : Nat.card K ≠ 2) (hK8 : Nat.card K ≠ 8)
    (e₁ : ↥L ≃* projectiveSL 3 K) (hcfg : E9Cfg L P T) : False := by
  classical
  have hLn : L.Normal := hcfg.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := E9Cfg.isSylowTwoOf_inf hcfg
  set UL : Subgroup L := (T ⊓ L).subgroupOf L with hULdef
  have hUL2 : IsPGroup 2 UL := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hU1 : IsPGroup 2 (UL.map e₁.toMonoidHom) := hUL2.map _
  have hU1i : ¬ 2 ∣ (UL.map e₁.toMonoidHom).index := by
    rw [show UL.map e₁.toMonoidHom = UL.map (e₁ : ↥L →* projectiveSL 3 K) from rfl,
      Subgroup.index_map_equiv]
    exact hS.2.2
  obtain ⟨S₀, hS₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) S₀ (hU1.toSylow hU1i)
  have hmem : ∀ z, z ∈ UL.map e₁.toMonoidHom ↔ g⁻¹ * z * g ∈ projUnitriangular 3 K := by
    intro z
    have h1 : UL.map e₁.toMonoidHom = ((g • S₀ : Sylow 2 (projectiveSL 3 K)) :
        Subgroup (projectiveSL 3 K)) := by
      rw [hg]
      rfl
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply, hS₀]
  set e : ↥L ≃* projectiveSL 3 K := e₁.trans (MulAut.conj g⁻¹) with hedef
  have he : ∀ y : L, e y = g⁻¹ * e₁ y * g := fun y => by
    rw [hedef, MulEquiv.trans_apply, MulAut.conj_apply, inv_inv]
  have hUe : UL.map e.toMonoidHom = projUnitriangular 3 K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e y ∈ _
      rw [he]
      exact (hmem _).mp ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, hye⟩ := (hmem (g * x * g⁻¹)).mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x
        by group])
      refine ⟨y, hy, ?_⟩
      change e y = x
      rw [he]
      change e₁ y = g * x * g⁻¹ at hye
      rw [hye]
      group
  set P' : Subgroup (projectiveSL 3 K) := (P.subgroupOf L).map e.toMonoidHom with hP'def
  have hP'card : Nat.card P' = 9 := by
    rw [hP'def, Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcfg.le).toEquiv, hcfg.card]
  have hP'exp : ∀ x ∈ P', x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hcfg.exp y (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy3, map_one]
  have hQU : ∀ u ∈ projUnitriangular 3 K, ∀ x ∈ P', ∃ y ∈ P', ∃ s ∈ projUnitriangular 3 K,
      u * x = y * s := by
    intro u hu x hx
    rw [← hUe] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y, hy, s, hs, hys⟩ := E9Cfg.mul_inf hcfg u' (Subgroup.mem_subgroupOf.mp hu') x'
      (Subgroup.mem_subgroupOf.mp hx')
    refine ⟨e ⟨y, hcfg.le hy⟩, ⟨⟨y, hcfg.le hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩,
      e ⟨s, hs.2⟩, ?_, ?_⟩
    · rw [← hUe]
      exact ⟨⟨s, hs.2⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    · change e u' * e x' = e ⟨y, hcfg.le hy⟩ * e ⟨s, hs.2⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hys
  have hPB : ∀ g : SL(3, K), proj 3 K g ∈ P' → g ∈ upperTriangular 3 K :=
    fun g hg => mem_upperTriangular_of_le (by rw [hP'card]) hK2 hK8 hQU hg
  have hD1 := inf_ratioGroup_ne_bot hPB hP'card hP'exp
  have hD2 := not_le_ratioGroup hPB hP'card hP'exp
  set α : A → MulAut (projectiveSL 3 K) := fun t => (e.symm.trans (MulAut.conjNormal t)).trans e
    with hαdef
  have hα : ∀ t (y : L), α t (e y) = e (MulAut.conjNormal t y) := fun t y => by
    rw [hαdef]
    simp
  have hαU : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A),
      (projUnitriangular 3 K).map (α t).toMonoidHom = projUnitriangular 3 K := by
    intro t ht
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hUe] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨MulAut.conjNormal t y, ?_, (hα t y).symm⟩
      have hy' := Subgroup.mem_subgroupOf.mp hy
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
      exact ⟨T.mul_mem (T.mul_mem ht.1 hy'.1) (T.inv_mem ht.1), hLn.conj_mem _ hy'.2 t⟩
    · rw [Subgroup.card_map_of_injective (α t).injective]
  have hαP : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ P', α t x ∈ P' := by
    rintro t ht _ ⟨y, hy, rfl⟩
    refine ⟨MulAut.conjNormal t y, ?_, (hα t y).symm⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, MulAut.conjNormal_apply]
    exact (Subgroup.mem_normalizer_iff.mp ht.2 _).mp (Subgroup.mem_subgroupOf.mp hy)
  set Q : Subgroup (projectiveSL 3 K) := P' ⊓ ratioGroup K with hQdef
  have hαQ : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ x ∈ Q, α t x ∈ Q :=
    fun t ht x hx => ⟨hαP t ht x hx.1, map_mem_ratioGroup (hαU t ht) hx.2⟩
  set QA : Subgroup A := (Q.map e.symm.toMonoidHom).map L.subtype with hQAdef
  have hQAP : QA ≤ P := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    obtain ⟨p, hp, rfl⟩ := hq.1
    have hp' : e.symm (e p) = p := e.symm_apply_apply p
    change ((e.symm (e p) : L) : A) ∈ P
    rw [hp']
    exact Subgroup.mem_subgroupOf.mp hp
  have hfwd : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ z ∈ QA, t * z * t⁻¹ ∈ QA := by
    rintro t ht _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨_, ⟨α t q, hαQ t ht q hq, rfl⟩, ?_⟩
    have h1 : e.symm (α t q) = MulAut.conjNormal t (e.symm q) := by
      have h2 := hα t (e.symm q)
      rw [e.apply_symm_apply] at h2
      rw [h2, e.symm_apply_apply]
    change ((e.symm (α t q) : L) : A) = t * ((e.symm q : L) : A) * t⁻¹
    rw [h1, MulAut.conjNormal_apply]
  have hnorm : T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (QA : Set A) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hfwd t ht z, fun hz => ?_⟩
    have h1 := hfwd t⁻¹ (inv_mem ht) _ hz
    rwa [show t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z by group] at h1
  rcases hcfg.irred QA hQAP hnorm with h | h
  · apply hD1
    rw [hQAdef, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective,
      Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective] at h
    exact h
  · apply hD2
    have hP : P = (P.subgroupOf L).map L.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hcfg.le]
    rw [hQAdef, hP] at h
    have h2 := Subgroup.map_injective L.subtype_injective h
    have h3 : Q = P' := by
      rw [hP'def, ← h2, Subgroup.map_map]
      ext x
      simp
    intro x hx
    rw [← h3] at hx
    exact hx.2

theorem not_dvd_card_psl3_four {X : Type} [Group X]
    (h : StatedClassicalModel X .PSL 3 2 2) : ¬ 27 ∣ Nat.card X := by
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := h
  rw [Nat.card_congr e₀.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num : 1 ≤ 3), hK]
  decide

theorem noX27Simple_psl3Even (n : ℕ) :
    NoX27Simple fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n := by
  rcases Nat.even_or_odd n with hn | hn
  · intro A _ _ L P T hcfg h27 hL
    by_cases hn2 : n = 2
    · subst hn2
      exact not_dvd_card_psl3_four hL (OddConfig.twentyseven_dvd_card hcfg h27)
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hL
    have := LieL3.charP_two_of_card_eq_two_pow hK
    have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
    have hn4 : 4 ≤ n := by
      obtain ⟨k, rfl⟩ := hn
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · rw [hK] at hq2
          norm_num at hq2
        · exact absurd rfl hn2
      · omega
    have h16 : 16 ≤ Nat.card K := by
      rw [hK]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn4
    refine false_of_x27Config (K := K) (by omega) ?_ ?_
      (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))) hcfg h27
    · rw [hK]
      intro h
      have h3 : n = 3 := Nat.pow_right_injective le_rfl (h.trans (by norm_num))
      omega
    · rw [hK]
      intro h
      rcases Nat.lt_or_ge n 5 with h5 | h5
      · have h4 : n = 4 := by omega
        subst h4
        norm_num at h
      · have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5
        omega
  · exact noX27Simple_of_noElemNine fun _ _ h => LieL3.noElemNine_of_odd hn h

theorem noE9Cfg_psl3Even (n : ℕ) :
    NoE9Cfg fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n := by
  rcases Nat.even_or_odd n with hn | hn
  · intro A _ _ L P T hL hcfg
    obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := hL
    have := LieL3.charP_two_of_card_eq_two_pow hK
    refine false_of_e9Cfg (K := K) ?_ ?_
      (e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))) hcfg
    · rw [hK]
      intro h
      have h1 : n = 1 := Nat.pow_right_injective le_rfl (h.trans (pow_one 2).symm)
      rw [h1] at hn
      exact Nat.not_even_one hn
    · rw [hK]
      intro h
      have h3 : n = 3 := Nat.pow_right_injective le_rfl (h.trans (by norm_num))
      rw [h3, Nat.even_iff] at hn
      omega
  · exact noE9Cfg_of_noElemNine fun _ _ h => LieL3.noElemNine_of_odd hn h

theorem facts134X27_psl3Even : ∀ f : ℕ, 1 ≤ f →
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 f := fun f _ =>
  noX27ConfigQ_of_noE9Cfg (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv
    e.symm h) (noX27Simple_psl3Even f) (noE9Cfg_psl3Even f)

end CFSG.Quasithin.H13.NQCore.X27L3
