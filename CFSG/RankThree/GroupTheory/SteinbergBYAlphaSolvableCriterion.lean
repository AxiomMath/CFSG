module

public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.GroupTheory.SteinbergCDCentralizerCoreIntersection

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBY

open CFSG CFSG.RankThree.GroupTheory

theorem alpha_solvable_normal_subgroup_criterion {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {B K : Subgroup H} (hB : IsElementaryAbelian p B)
    (hBcard : p ^ 2 ≤ Nat.card B) (hK : K.Normal) (hKs : Group.IsSolvable K)
    (hKp : ¬ p ∣ Nat.card K) (hXK : twoCoreX B ≤ K)
    (hJ : ∀ b ∈ B, b ≠ 1 →
      ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({b} : Set H)), B⁆ ≤ pCore 2 H) :
    twoCoreX B = inSubgroup (pCore 2) K ⊓ Subgroup.centralizer (B : Set H) ∧
      twoCoreX B ≤ pCore 2 H ∧ twoCoreAlpha B ≤ pCore 2 H := by
  have : Fact p.Prime := ⟨hp⟩
  have := hB
  let _ : MulDistribMulAction B K :=
    MulDistribMulAction.compHom K ((MulAut.conjNormal (H := K)).comp B.subtype)
  have hsmul : ∀ (b : B) (k : K), ((b • k : K) : H) = (b : H) * k * (b : H)⁻¹ := fun _ _ => rfl
  have hfix : ∀ b : B, (fixedPointSubgroup (Subgroup.zpowers b) K).map K.subtype =
      K ⊓ Subgroup.centralizer ({(b : H)} : Set H) := by
    intro b
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have h := congrArg Subtype.val
        ((SolvableHall.mem_fixedPointSubgroup_zpowers_iff b k).mp hk)
      rw [hsmul] at h
      exact ⟨k.2, (mul_inv_eq_iff_eq_mul.mp h).symm⟩
    · rintro ⟨hxK, hx⟩
      refine ⟨⟨x, hxK⟩, (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b _).mpr
        (Subtype.ext ?_), rfl⟩
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr hx.symm
  have hfixB : (fixedPointSubgroup B K).map K.subtype = K ⊓ Subgroup.centralizer (B : Set H) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Subgroup.coe_subtype, SetLike.mem_coe]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨k.2, fun b hb => ?_⟩
      have h := congrArg Subtype.val (hk ⟨b, hb⟩)
      rw [hsmul] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · rintro ⟨hxK, hx⟩
      refine ⟨⟨x, hxK⟩, fun b => Subtype.ext ?_, rfl⟩
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr (hx b b.2)
  have hcore : ∀ b : B,
      ((pCore 2 (fixedPointSubgroup (Subgroup.zpowers b) K)).map
        (fixedPointSubgroup (Subgroup.zpowers b) K).subtype).map K.subtype =
        inSubgroup (pCore 2) (K ⊓ Subgroup.centralizer ({(b : H)} : Set H)) := by
    intro b
    rw [← hfix b, ← map_inSubgroup_pCore_of_injective 2 K.subtype K.subtype_injective]
    rfl
  have hnormK : ∀ b : H, Subgroup.centralizer ({b} : Set H) ≤
      Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({b} : Set H) : Subgroup H) : Set H) :=
    fun b _ hg => mem_normalizer_inf ((Subgroup.normalizer_eq_top (H := K)).ge (Subgroup.mem_top _))
      (Subgroup.le_normalizer hg)
  have hCD := coprime_solvable_centralizer_core_intersection (B := B) (K := K) Nat.prime_two
    hBcard hKs hKp
  have hX : twoCoreX B = (pCore 2 K ⊓ fixedPointSubgroup B K).map K.subtype := by
    rw [← hCD]
    ext x
    constructor
    · intro hx
      have hxK : x ∈ K := hXK hx
      refine ⟨⟨x, hxK⟩, ?_, rfl⟩
      simp only [SetLike.mem_coe, Subgroup.mem_iInf]
      intro b hb
      have hb' : (b : H) ≠ 1 := fun h => hb (Subtype.ext h)
      have hxO2 := (mem_twoCoreX_iff.mp hx) b b.2 hb'
      have hxO : x ∈ inSubgroup (pCore 2) (K ⊓ Subgroup.centralizer ({(b : H)} : Set H)) :=
        inf_inSubgroup_pCore_le inf_le_right ⟨⟨hxK, inSubgroup_pCore_le 2 _ hxO2⟩, hxO2⟩
      rw [← hcore b] at hxO
      obtain ⟨z, hz, hzx⟩ := hxO
      have hz' : z = ⟨x, hxK⟩ := Subtype.ext hzx
      rwa [← hz']
    · rintro ⟨k, hk, rfl⟩
      rw [mem_twoCoreX_iff]
      intro b hb hb1
      have hb1' : (⟨b, hb⟩ : B) ≠ 1 := fun h => hb1 (by simpa using congrArg Subtype.val h)
      have hkO := Subgroup.mem_map_of_mem K.subtype
        ((Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hk ⟨b, hb⟩)) hb1')
      rw [hcore] at hkO
      exact inSubgroup_pCore_mono inf_le_right (hnormK b) hkO
  have hOK : inSubgroup (pCore 2) K ≤ pCore 2 H := by
    rw [inSubgroup_pCore_eq_inf le_top (Subgroup.normalizer_eq_top (H := K)).ge,
      inSubgroup_pCore_top]
    exact inf_le_right
  have hXeq : twoCoreX B = inSubgroup (pCore 2) K ⊓ Subgroup.centralizer (B : Set H) := by
    rw [hX, Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hfixB, ← inf_assoc]
    change inSubgroup (pCore 2) K ⊓ K ⊓ _ = _
    rw [inf_eq_left.mpr (inSubgroup_pCore_le 2 K)]
  have hXO : twoCoreX B ≤ pCore 2 H := hXeq ▸ inf_le_left.trans hOK
  refine ⟨hXeq, hXO, sup_le ?_ hXO⟩
  exact iSup₂_le fun b hb => iSup_le fun hb1 => hJ b hb hb1

end CFSG.RankThree.GroupTheory.SteinbergBY
