module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveF4SmallDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLang
import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4
import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType.FrameRoute

theorem ggF4Small_a4_abstract {ι : Type} {M : CoxeterMatrix ι} (i₀ i₁ : ι)
    (hconj : ∀ i, ∃ w : M.Group, w * M.simple i₀ = M.simple i * w ∨
      w * M.simple i₁ = M.simple i * w)
    (hnc : ∀ j, (j = i₀ ∨ j = i₁) → ∃ a b c d : M.Group, (∃ w, w * M.simple j = a * w) ∧
      (∃ w, w * M.simple j = b * w) ∧ (∃ w, w * M.simple j = c * w) ∧
      (∃ w, w * M.simple j = d * w) ∧ a * b * (c * d) ≠ c * d * (a * b))
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} (hBsE : IsElemAbelian 3 Bs)
    {A₀ : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥A₀)
    (he : ∀ i : ι, GGIsReflection 3 ((e (M.simple i) : ↥A₀) : MulAut ↥Bs))
    (hA₀ : A₀ ≤ ggAutomizer ⊤ Bs) (hfix : ∀ b : ↥Bs, (∀ φ ∈ A₀, φ b = b) → b = 1)
    {z : G} (hzBs : z ∈ Bs) (hz1 : z ≠ 1) :
    ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧
      g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  letI : CommGroup ↥Bs :=
    { (inferInstance : Group ↥Bs) with mul_comm := fun a b => hBsE.1.is_comm.comm a b }
  let z' : ↥Bs := ⟨z, hzBs⟩
  have hz'3 : z' ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hBsE.2 z hzBs)
  have hz'1 : z' ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  let S : Subgroup (MulAut ↥Bs) :=
    { carrier := {φ | φ z' ∈ Subgroup.zpowers z' ∧ φ⁻¹ z' ∈ Subgroup.zpowers z'}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨?_, ?_⟩
        · rw [MulAut.mul_apply]; exact map_mem_zpowers ha hb
        · rw [mul_inv_rev, MulAut.mul_apply]; exact map_mem_zpowers hb' ha'
      one_mem' := ⟨Subgroup.mem_zpowers z', Subgroup.mem_zpowers z'⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨ha', by rw [inv_inv]; exact ha⟩ }
  have key : ∀ h : G, ∀ ψ : MulAut ↥Bs, (∀ b : ↥Bs, ((ψ b : ↥Bs) : G) = h * b * h⁻¹) →
      ψ z' ∈ Subgroup.zpowers z' := by
    intro h ψ hψ
    have e1 : ((ψ z' : ↥Bs) : G) = h * z * h⁻¹ := hψ z'
    have hmem : h * z * h⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      rw [Set.mem_singleton_iff.mp hw, ← e1]
      exact congrArg Subtype.val (mul_comm z' (ψ z'))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hcon h hmem)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow, e1]; exact hk)⟩
  have hgen : ∀ H : Subgroup G, ggInduced H Bs ⊆ S := by
    rintro H φ ⟨g, -, -, hφ⟩
    refine ⟨key g φ hφ, key g⁻¹ φ⁻¹ fun b => ?_⟩
    have h1 := hφ (φ⁻¹ b)
    rw [MulAut.apply_inv_self] at h1
    rw [inv_inv, h1]
    group
  have hAleS : A₀ ≤ S := hA₀.trans ((Subgroup.closure_le _).mpr (hgen ⊤))
  set E : M.Group → MulAut ↥Bs :=
    fun w => ((e w : ↥(A₀)) : MulAut ↥Bs) with hEdef
  have hEmul : ∀ a b, E (a * b) = E a * E b := fun a b => by simp [hEdef]
  have hEinv : ∀ a, E a⁻¹ = (E a)⁻¹ := fun a => by simp [hEdef]
  have hAS : ∀ w : M.Group, E w ∈ S := fun w => hAleS (e w).2
  have hconjact : ∀ (w : M.Group) (j : ι), E (w * M.simple j * w⁻¹) z' = E (M.simple j) z' := by
    intro w j
    refine apply_eq_of_conj (ψ := E w) ?_ (hAS w).2 (hAS _).1
    rw [← hEmul, ← hEmul]
    congr 1
    group
  have hrefl : ∀ (w : M.Group) (j : ι), GGIsReflection 3 (E (w * M.simple j * w⁻¹)) := by
    intro w j
    rw [hEmul, hEmul, hEinv]
    exact ggIsReflection_mul_inv (he j) (E w)
  have hsame : ∀ i, E (M.simple i) z' = E (M.simple i₀) z' ∨
      E (M.simple i) z' = E (M.simple i₁) z' := by
    intro i
    obtain ⟨w, hw | hw⟩ := hconj i
    · left
      have : M.simple i = w * M.simple i₀ * w⁻¹ := by rw [hw]; group
      rw [this]
      exact hconjact w i₀
    · right
      have : M.simple i = w * M.simple i₁ * w⁻¹ := by rw [hw]; group
      rw [this]
      exact hconjact w i₁
  by_cases h0 : E (M.simple i₀) z' = z' ∧ E (M.simple i₁) z' = z'
  ·
    have hfixall : ∀ ψ ∈ A₀, ψ z' = z' := by
      intro ψ hψ
      obtain ⟨w, rfl⟩ : ∃ w, ((e w : ↥(A₀)) : MulAut ↥Bs) = ψ :=
        ⟨e.symm ⟨ψ, hψ⟩, by simp⟩
      let T : Subgroup M.Group :=
        (MulAction.stabilizer (MulAut ↥Bs) z').comap
          ((A₀).subtype.comp e.toMonoidHom)
      have hT : (⊤ : Subgroup M.Group) ≤ T := by
        rw [← M.toCoxeterSystem.subgroup_closure_range_simple, Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        simp only [CoxeterMatrix.toCoxeterSystem_simple]
        rw [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
        rcases hsame i with h | h
        · exact h.trans h0.1
        · exact h.trans h0.2
      exact hT (Subgroup.mem_top w)
    exact hz'1 (hfix z' hfixall)
  ·
    obtain ⟨j, hj, hjz⟩ : ∃ j, (j = i₀ ∨ j = i₁) ∧ E (M.simple j) z' ≠ z' := by
      by_cases ha : E (M.simple i₀) z' = z'
      · exact ⟨i₁, Or.inr rfl, fun hb => h0 ⟨ha, hb⟩⟩
      · exact ⟨i₀, Or.inl rfl, ha⟩
    have hφ1 : E (M.simple j) z' ≠ 1 :=
      fun h => hz'1 ((map_eq_one_iff _ (MulEquiv.injective _)).mp h)
    have hinv : E (M.simple j) z' = z'⁻¹ := eq_inv_of_mem_zpowers hz'3 (hAS _).1 hφ1 hjz
    have hinvw : ∀ w : M.Group, E (w * M.simple j * w⁻¹) z' = z'⁻¹ :=
      fun w => (hconjact w j).trans hinv
    obtain ⟨a, b, c, d, ⟨w₁, ha⟩, ⟨w₂, hb⟩, ⟨w₃, hc⟩, ⟨w₄, hd⟩, hne⟩ := hnc j hj
    obtain rfl := eq_mul_inv_of_mul_eq ha.symm
    obtain rfl := eq_mul_inv_of_mul_eq hb.symm
    obtain rfl := eq_mul_inv_of_mul_eq hc.symm
    obtain rfl := eq_mul_inv_of_mul_eq hd.symm
    have hu := unip_of_refl hz'3 hz'1 (hrefl w₁ j).2 (hinvw w₁) (hrefl w₂ j).2 (hinvw w₂)
    have hu' := unip_of_refl hz'3 hz'1 (hrefl w₃ j).2 (hinvw w₃) (hrefl w₄ j).2 (hinvw w₄)
    have hcomm := commute_of_unip hu hu'
    apply hne
    apply e.injective
    apply Subtype.ext
    set a := w₁ * M.simple j * w₁⁻¹
    set b := w₂ * M.simple j * w₂⁻¹
    set c := w₃ * M.simple j * w₃⁻¹
    set d := w₄ * M.simple j * w₄⁻¹
    show E (a * b * (c * d)) = E (c * d * (a * b))
    calc E (a * b * (c * d)) = E a * E b * (E c * E d) := by
          rw [hEmul (a * b) (c * d), hEmul a b, hEmul c d]
      _ = E c * E d * (E a * E b) := hcomm
      _ = E (c * d * (a * b)) := by rw [hEmul (c * d) (a * b), hEmul c d, hEmul a b]

theorem ggF4Small_a4
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {ks : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J ks)
    (hW4 : GGWeylOfType 3 CoxeterMatrix.F₄ (ggAutomizerJoin L Bs ks)) (hne : ks.Nonempty)
    {z : G} (hzB : z ∈ B) (hz1 : z ≠ 1) :
    ∃ g : G, g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) ∧
      g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  have hW : GGSecFiveWeylCase 3 B Bs x D J := ggSecFiveWeylCase_of_prime_three hR.1.1 hR.2.1
  have hfix := FrameRoute.eq_one_of_fix_ggAutomizerJoin hTBF hWI hR.1 hW hR.2.2.2.1 hne
  have hA₀ : ggAutomizerJoin L Bs ks ≤ ggAutomizer ⊤ Bs :=
    (FrameRoute.ggAutomizerJoin_le_ggG0 hR.2.2.2.1).trans (ggAutomizer_mono Bs le_top)
  have hBsE : IsElemAbelian 3 Bs := hR.1.1.2.1.2.1
  have hzBs : z ∈ Bs := hR.1.1.2.1.1 hzB
  have hW4' : GGWeylOfType 3
      (CFSG.LieType.RootSystem.coxeterMatrix (CFSG.LieType.Chevalley.isFiniteType_cartan .F4))
      (ggAutomizerJoin L Bs ks) := by
    rw [← coxeterF4_eq]
    exact hW4
  obtain ⟨e, he⟩ := hW4'
  refine ggF4Small_a4_abstract (iF4 0) (iF4 3) conj_simple_F4 ?_ hBsE e he hA₀ hfix hzBs hz1
  rintro j (rfl | rfl)
  · exact noncomm_F4 0
  · exact noncomm_F4 1

end CFSG.StandardType

end
