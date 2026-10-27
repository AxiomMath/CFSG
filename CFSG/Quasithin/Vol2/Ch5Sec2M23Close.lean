module

public import CFSG.Quasithin.Recognition.UniquenessSystemCoset
public import CFSG.Quasithin.Recognition.M23Facts
public import CFSG.Quasithin.Recognition.UniquenessSystemCriterion

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Blueprint CFSG.Quasithin.Asc94
open scoped Pointwise

variable {G : Type} [Group G]

theorem map_subgroupOf_eq_of_iff {Gb : Type*} [Group Gb] {A P : Subgroup G} {B Q : Subgroup Gb}
    (e : A ≃* B) (h : ∀ a : A, (a : G) ∈ P ↔ (e a : Gb) ∈ Q) :
    (P.subgroupOf A).map e.toMonoidHom = Q.subgroupOf B := by
  ext b
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact (h a).mp ha
  · intro hb
    refine ⟨e.symm b, (h _).mpr (by simpa using hb), by simp⟩

theorem nonempty_mulEquiv_m23_of_closeData
    {Gx I : Subgroup G} {t : G} {a b c d : Fin 23}
    (habcd : [a, b, c, d].Nodup) (htI : t ∈ I) (htGx : t ∉ Gx) (htt : t * t ∈ Gx)
    (hgen : Gx ⊔ I = ⊤)
    (hGx : Gx ≤ Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx) ⊔ I ⊓ Gx)
    (hI : I ≤ I ⊓ Gx ⊔ Subgroup.zpowers t)
    (β : Gx ≃* stabilizer ↥NativeSporadic.M23 (xbar habcd))
    (ζ : I ≃* quadStab ↥NativeSporadic.M23 a b c d)
    (hζx : ∀ i : I, (i : G) ∈ Gx ↔
      (ζ i : ↥NativeSporadic.M23) ∈ stabilizer ↥NativeSporadic.M23 (xbar habcd))
    (hβζ : ∀ (i : I) (hi : (i : G) ∈ Gx), (β ⟨i, hi⟩ : ↥NativeSporadic.M23) = ζ i)
    (hβy : ∀ g : Gx, (g : G) ∈ stabilizer G ((t : G) : G ⧸ Gx) ↔
      (β g : ↥NativeSporadic.M23) ∈ stabilizer ↥NativeSporadic.M23 (ybar habcd))
    (hζy : ∀ i : I, (i : G) ∈
        stabilizer G ({((1 : G) : G ⧸ Gx), ((t : G) : G ⧸ Gx)} : Set (G ⧸ Gx)) ↔
      (ζ i : ↥NativeSporadic.M23) ∈
        stabilizer ↥NativeSporadic.M23 ({xbar habcd, ybar habcd} : Set (Pair (Fin 23))))
    (haut : ∀ α : ↥(Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx)) ≃*
        ↥(Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx)),
      (∀ k : ↥(Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx)), (k : G) ∈ I → α k = k) →
        α = MulEquiv.refl _) :
    Nonempty (G ≃* ↥NativeSporadic.M23) := by
  set x : G ⧸ Gx := ((1 : G) : G ⧸ Gx)
  set y : G ⧸ Gx := ((t : G) : G ⧸ Gx)
  have hU := cosetSystem_isUniquenessSystem htI htGx htt hgen hGx hI
  have hUb := m23_isUniquenessSystem habcd
  have hstab : stabilizer G x = Gx := stabilizer_mk_one Gx
  have mem : ∀ {g : G}, g ∈ stabilizer G x → g ∈ Gx := fun hg => by rwa [hstab] at hg
  have htx : t • x = y := by
    simp only [x, y, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  have hty : t • y = x := by
    simp only [x, y, MulAction.Quotient.smul_mk, smul_eq_mul]
    rw [QuotientGroup.eq]
    simpa using Gx.inv_mem htt
  set β' : stabilizer G x ≃* stabilizer ↥NativeSporadic.M23 (xbar habcd) :=
    (MulEquiv.subgroupCongr hstab).trans β
  have hβ' : ∀ g : stabilizer G x, β' g = β ⟨g, mem g.2⟩ := fun g => rfl
  have hs : IsSimilarity I x y (quadStab ↥NativeSporadic.M23 a b c d) (xbar habcd)
      (ybar habcd) β' ζ := by
    refine ⟨map_subgroupOf_eq_of_iff ζ fun i => ?_, fun i hi => ?_,
      map_subgroupOf_eq_of_iff β' fun g => ?_, map_subgroupOf_eq_of_iff ζ hζy⟩
    · rw [hstab]; exact hζx i
    · rw [hβ']; exact hβζ i _
    · rw [hβ']; exact hβy ⟨g, mem g.2⟩
  have hzt := zeta_swap (t := ⟨t, htI⟩) hs hU.adj.ne hUb.adj.ne htx hty
  set K := stabilizer G x ⊓ stabilizer G y with hK
  have e : t⁻¹ • x = y := by rw [← hty, inv_smul_smul]
  have e' : t⁻¹ • y = x := by rw [← htx, inv_smul_smul]
  have hKt : ∀ g : G, g ∈ K ↔ t * g * t⁻¹ ∈ K := by
    intro g
    simp only [hK, Subgroup.mem_inf, mem_stabilizer_iff]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨by rw [mul_smul, mul_smul, e, hy, hty], by rw [mul_smul, mul_smul, e', hx, htx]⟩
    · rintro ⟨h1, h2⟩
      rw [mul_smul, mul_smul, e] at h1
      rw [mul_smul, mul_smul, e'] at h2
      exact ⟨smul_left_cancel t (h2.trans htx.symm), smul_left_cancel t (h1.trans hty.symm)⟩
  have hKeq : K = Gx ⊓ stabilizer G ((t : G) : G ⧸ Gx) := by rw [hK, hstab]
  have h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) → α = MulEquiv.refl K := by
    rw [hKeq]; exact haut
  have htK : t ∈ Subgroup.normalizer (K : Set G) := Subgroup.mem_normalizer_iff.mpr hKt
  have hhK : t⁻¹ ∈ Subgroup.normalizer (K : Set G) := inv_mem htK
  have himg : stabImage β' K = stabilizer ↥NativeSporadic.M23 (xbar habcd) ⊓
      stabilizer ↥NativeSporadic.M23 (ybar habcd) := by
    ext g
    rw [mem_stabImage, Subgroup.mem_inf]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨(β' k).2, ?_⟩
      rw [hβ']
      exact (hβy ⟨k, mem k.2⟩).mp (Subgroup.mem_inf.mp hk).2
    · rintro ⟨hgx, hgy⟩
      refine ⟨β'.symm ⟨g, hgx⟩, Subgroup.mem_inf.mpr ⟨(β'.symm ⟨g, hgx⟩).2, ?_⟩, by simp⟩
      have h0 : (β ⟨_, mem (β'.symm ⟨g, hgx⟩).2⟩ : ↥NativeSporadic.M23) = g := by
        rw [← hβ', MulEquiv.apply_symm_apply]
      exact (hβy ⟨_, mem (β'.symm ⟨g, hgx⟩).2⟩).mpr (by rw [h0]; exact hgy)
  have hzK : ∀ g : ↥NativeSporadic.M23, g ∈ stabilizer _ (xbar habcd) ⊓
      stabilizer _ (ybar habcd) ↔ (ζ ⟨t, htI⟩ : ↥NativeSporadic.M23) * g *
        (ζ ⟨t, htI⟩ : ↥NativeSporadic.M23)⁻¹ ∈ stabilizer _ (xbar habcd) ⊓
          stabilizer _ (ybar habcd) := by
    set z : ↥NativeSporadic.M23 := (ζ ⟨t, htI⟩ : ↥NativeSporadic.M23)
    have ez : z⁻¹ • xbar habcd = ybar habcd := by rw [← hzt.2, inv_smul_smul]
    have ez' : z⁻¹ • ybar habcd = xbar habcd := by rw [← hzt.1, inv_smul_smul]
    intro g
    simp only [Subgroup.mem_inf, mem_stabilizer_iff]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨by rw [mul_smul, mul_smul, ez, hy, hzt.2],
        by rw [mul_smul, mul_smul, ez', hx, hzt.1]⟩
    · rintro ⟨h1, h2⟩
      rw [mul_smul, mul_smul, ez] at h1
      rw [mul_smul, mul_smul, ez'] at h2
      exact ⟨smul_left_cancel z (h2.trans hzt.1.symm), smul_left_cancel z (h1.trans hzt.2.symm)⟩
  have hhβ : (ζ ⟨t⁻¹, I.inv_mem htI⟩ : ↥NativeSporadic.M23) ∈
      Subgroup.normalizer (stabImage β' K : Set ↥NativeSporadic.M23) := by
    rw [himg, show (⟨t⁻¹, I.inv_mem htI⟩ : I) = (⟨t, htI⟩ : I)⁻¹ from rfl, map_inv,
      Subgroup.coe_inv]
    exact inv_mem (Subgroup.mem_normalizer_iff.mpr hzK)
  have h3 : stabilizer G x ⊓ stabilizer G y =
      K ⊓ stabilizer G y ⊔ I ⊓ stabilizer G x ⊓ stabilizer G y := by
    refine le_antisymm (le_sup_of_le_left (le_inf le_rfl inf_le_right)) (sup_le inf_le_left ?_)
    exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hth : ((⟨t, htI⟩ : I) : G) * ((⟨t⁻¹, I.inv_mem htI⟩ : I) : G) ∈ stabilizer G x := by
    simp only [mul_inv_cancel]; exact one_mem _
  obtain ⟨-, he⟩ := equivalence_criterion hs K ⟨t, htI⟩ ⟨t⁻¹, I.inv_mem htI⟩ inf_le_left h1
    htx hty hth htK hhK hhβ h3
  obtain ⟨φ, -, -⟩ := m23_recognition hU habcd he
  exact ⟨φ⟩

end CFSG.Quasithin.H13
