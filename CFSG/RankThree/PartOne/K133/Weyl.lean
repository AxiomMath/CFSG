module

public import CFSG.RankThree.PartOne.K133.Complement
public import CFSG.RankThree.PartOne.K133.Lift
public import CFSG.RankThree.PartOne.S13K.Pair134Basic

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem torusImage_le_of_sectionTenRel {p : ℕ} (hp : p.Prime) {E I J : Subgroup G} {e : G}
    (hE : IsElementaryAbelian p E) (heE : e ∈ E) (hI : I ∈ thetaComponentsAt p e)
    (hEI : E ≤ Subgroup.normalizer (I : Set G)) (hEJ : E ≤ Subgroup.normalizer (J : Set G))
    (hIJ : sectionTenRel p I J) : torusImage E I ≤ torusImage E J := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set T := inSubgroup (aschbacherSolvableCore p) I with hT
  have hTp : ¬ p ∣ Nat.card T := (theta_solvable_and_not_dvd hp I).2
  have hθe : T ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) := by
    rw [hT, theta_eq_inf_of_mem_thetaComponentsAt hp hI]
    exact inf_le_right
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => theta_conj_mem_of_normalizer p I (hEI ha) hn
    · intro hn
      have := theta_conj_mem_of_normalizer p I (hEI (E.inv_mem ha)) hn
      simpa [mul_assoc] using this
  set P := I ⊓ J with hP
  have hEP : E ≤ Subgroup.normalizer (P : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => ⟨(Subgroup.mem_normalizer_iff.1 (hEI ha) x).1 hx.1,
        (Subgroup.mem_normalizer_iff.1 (hEJ ha) x).1 hx.2⟩
    · exact fun hx => ⟨(Subgroup.mem_normalizer_iff.1 (hEI ha) x).2 hx.1,
        (Subgroup.mem_normalizer_iff.1 (hEJ ha) x).2 hx.2⟩
  have hEPE : E ≤ Subgroup.normalizer ((P ⊔ E : Subgroup G) : Set G) :=
    fun a ha => Subgroup.le_normalizer (le_sup_right (a := P) ha)
  set T₁ := T ⊓ (P ⊔ E) with hT₁
  have hET₁ : E ≤ Subgroup.normalizer (T₁ : Set G) := fun a ha => by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => ⟨(Subgroup.mem_normalizer_iff.1 (hET ha) x).1 hx.1,
        (Subgroup.mem_normalizer_iff.1 (hEPE ha) x).1 hx.2⟩
    · exact fun hx => ⟨(Subgroup.mem_normalizer_iff.1 (hET ha) x).2 hx.1,
        (Subgroup.mem_normalizer_iff.1 (hEPE ha) x).2 hx.2⟩
  have hT₁p : ¬ p ∣ Nat.card T₁ := fun h =>
    hTp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
  intro xs hxs
  obtain ⟨⟨x, hxN⟩, hxI', rfl⟩ := Subgroup.mem_map.1 hxs
  have hxI : x ∈ I := Subgroup.mem_subgroupOf.1 hxI'
  have hxset : x ∈ ((I ⊓ J : Subgroup G) : Set G) * (T : Set G) := by
    rw [← sectionTenRel_iff.1 hIJ]
    exact hxI
  obtain ⟨j, hjP, n, hnT, rfl⟩ := hxset
  set E' : Subgroup G := E.map (MulAut.conj j⁻¹).toMonoidHom with hE'
  have hE'TE : E' ≤ T ⊔ E := by
    rintro u ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have ha' : (j * n)⁻¹ * a * (j * n) ∈ E := by
      have := (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (E : Set G)).inv_mem hxN) a).1 ha
      simpa using this
    have h1 : j⁻¹ * a * j = n * ((j * n)⁻¹ * a * (j * n)) * n⁻¹ := by group
    rw [h1]
    have hτ : n * (((j * n)⁻¹ * a * (j * n)) * n⁻¹ * ((j * n)⁻¹ * a * (j * n))⁻¹) ∈ T :=
      T.mul_mem hnT ((Subgroup.mem_normalizer_iff.1 (hET ha') n⁻¹).1 (T.inv_mem hnT))
    have h2 : n * ((j * n)⁻¹ * a * (j * n)) * n⁻¹ =
        (n * (((j * n)⁻¹ * a * (j * n)) * n⁻¹ * ((j * n)⁻¹ * a * (j * n))⁻¹)) *
          ((j * n)⁻¹ * a * (j * n)) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup hτ ha'
  have hE'PE : E' ≤ P ⊔ E := by
    rintro u ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h1 : a * j * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 (hEP ha) j).1 hjP
    have h2 : j⁻¹ * a * j = (j⁻¹ * (a * j * a⁻¹)) * a := by group
    rw [h2]
    exact Subgroup.mul_mem_sup (P.mul_mem (P.inv_mem hjP) h1) ha
  have hE'T₁E : E' ≤ T₁ ⊔ E := by
    intro u hu
    obtain ⟨τ', hτ', a', ha', rfl⟩ := exists_mul_of_mem_sup hET (hE'TE hu)
    have hτ'PE : τ' ∈ P ⊔ E := by
      have h1 : τ' * a' * a'⁻¹ ∈ P ⊔ E := (P ⊔ E).mul_mem (hE'PE hu)
        ((P ⊔ E).inv_mem (le_sup_right (a := P) ha'))
      simpa using h1
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.2 ⟨hτ', hτ'PE⟩) ha'
  have hcard : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj j⁻¹).injective
  obtain ⟨τ₁, hτ₁, hEτ⟩ := exists_conj_of_complement hp hET₁ hEp hT₁p hE'T₁E hcard
  have hy₁N : j * τ₁ ∈ Subgroup.normalizer (E : Set G) := by
    have hcomp : (MulAut.conj (j * τ₁)).toMonoidHom =
        (MulAut.conj j).toMonoidHom.comp (MulAut.conj τ₁).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hcomp' : (MulAut.conj j).toMonoidHom.comp (MulAut.conj j⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have key : E.map (MulAut.conj (j * τ₁)).toMonoidHom = E := by
      rw [hcomp, ← Subgroup.map_map, ← hEτ, hE', Subgroup.map_map, hcomp', Subgroup.map_id]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 key
  have hzN : n⁻¹ * τ₁ ∈ Subgroup.normalizer (E : Set G) := by
    have := (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).inv_mem hxN) hy₁N
    simpa [mul_assoc] using this
  have hzθ : n⁻¹ * τ₁ ∈ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({e} : Set G)) :=
    hθe (T.mul_mem (T.inv_mem hnT) (Subgroup.mem_inf.1 hτ₁).1)
  have hzc : ∀ a ∈ E, (n⁻¹ * τ₁) * a * (n⁻¹ * τ₁)⁻¹ = a :=
    S13K.centralizes_of_mem_theta_of_mem_normalizer hp hE heE hzN hzθ
  obtain ⟨π₁, hπ₁, a₁, ha₁, hτπ⟩ := exists_mul_of_mem_sup hEP (Subgroup.mem_inf.1 hτ₁).2
  have hy₂N : j * π₁ ∈ Subgroup.normalizer (E : Set G) := by
    have h1 : j * π₁ = (j * τ₁) * a₁⁻¹ := by rw [hτπ]; group
    rw [h1]
    exact (Subgroup.normalizer (E : Set G)).mul_mem hy₁N
      ((Subgroup.normalizer (E : Set G)).inv_mem (Subgroup.le_normalizer ha₁))
  have hy₂J : j * π₁ ∈ J := J.mul_mem (Subgroup.mem_inf.1 hjP).2 (Subgroup.mem_inf.1 hπ₁).2
  refine Subgroup.mem_map.2 ⟨⟨j * π₁, hy₂N⟩, Subgroup.mem_subgroupOf.2 hy₂J, ?_⟩
  refine MulEquiv.ext fun a => Subtype.ext ?_
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hc : (a₁ : G) * a = a * a₁ := congrArg Subtype.val (hE.is_comm.comm ⟨a₁, ha₁⟩ a)
  have hcomm1 : a₁⁻¹ * (a : G) * a₁ = a := by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hz := hzc (a : G) a.2
  calc j * π₁ * (a : G) * (j * π₁)⁻¹
      = (j * τ₁) * (a₁⁻¹ * a * a₁) * (j * τ₁)⁻¹ := by rw [hτπ]; group
    _ = (j * τ₁) * a * (j * τ₁)⁻¹ := by rw [hcomm1]
    _ = (j * n) * ((n⁻¹ * τ₁) * a * (n⁻¹ * τ₁)⁻¹) * (j * n)⁻¹ := by group
    _ = (j * n) * a * (j * n)⁻¹ := by rw [hz]

end CFSG.RankThree.PartOne.K133
