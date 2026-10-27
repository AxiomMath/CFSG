module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorComp
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}

private theorem plh_img_mono (Φ : OrthFrameCore p Bs X)
    {S S' : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)} (h : S ≤ S') : Φ.img S ≤ Φ.img S' := by
  rw [OrthFrameCore.img, OrthFrameCore.img]
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono (orthDerived Φ.Q) h)

private noncomputable def plh_imgEquiv (Φ : OrthFrameCore p Bs X)
    (S : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V)) (hS : S ≤ orthDerived Φ.Q) : ↥S ≃* ↥(Φ.img S) :=
  (Subgroup.subgroupOfEquivOfLe hS).symm.trans
    (Subgroup.equivMapOfInjective (S.subgroupOf (orthDerived Φ.Q)) Φ.ψ Φ.hinj)

private theorem plh_isQuasisimple_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : CFSG.Assembly.IsQuasisimple A) : CFSG.Assembly.IsQuasisimple B := by
  refine ⟨?_, ?_⟩
  · haveI : Group.IsPerfect A := ⟨h.1⟩
    haveI : Group.IsPerfect B :=
      Group.IsPerfect.ofSurjective (f := (e : A →* B)) e.surjective
    exact (inferInstance : Group.IsPerfect B).commutator_eq_top
  · haveI : IsSimpleGroup (A ⧸ Subgroup.center A) := h.2
    have e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
      QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)
    exact e'.symm.isSimpleGroup

private theorem plh_assembly_isQuasisimple_of_isQuasisimple {Q : Type*} [Group Q]
    (h : CFSG.IsQuasisimple Q) : CFSG.Assembly.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem plh_not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q]
    (h : CFSG.Assembly.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  haveI : Group.IsPerfect Q := ⟨h.1⟩
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := h.2
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  exact Group.IsPerfect.not_isSolvable Q

private theorem plh_not_isSolvable_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ¬ Group.IsSolvable B) : ¬ Group.IsSolvable A := fun hA => by
  haveI : Group.IsSolvable A := hA
  exact h (Group.isSolvable_of_isSolvable_injective
    (f := e.symm.toMonoidHom) e.symm.injective)

private theorem plh_ggHasLabel_quotCenter_of_mulEquiv {A B : Type} [Group A] [Group B]
    (e : A ≃* B) {lab : LargeEvenLabel} (h : GGHasLabel lab (A ⧸ Subgroup.center A)) :
    GGHasLabel lab (B ⧸ Subgroup.center B) :=
  ggHasLabel_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e (Subgroup.map_center_eq e)) h

private noncomputable def plh_pullback (Φ : OrthFrameCore p Bs X) (K : Subgroup G) :
    Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  (K.comap Φ.ψ).map (orthDerived Φ.Q).subtype

private theorem plh_img_pullback_eq (Φ : OrthFrameCore p Bs X) {K : Subgroup G}
    (hK : K ≤ Φ.ψ.range) : Φ.img (plh_pullback Φ K) = K := by
  unfold plh_pullback
  rw [OrthFrameCore.img]
  have hsub : ((K.comap Φ.ψ).map (orthDerived Φ.Q).subtype).subgroupOf (orthDerived Φ.Q) =
      K.comap Φ.ψ := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := Subtype.ext hyx
      rw [Subgroup.mem_comap] at hy ⊢
      rw [hyx'] at hy
      exact hy
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
  rw [hsub, Subgroup.map_comap_eq_self hK]

private theorem plh_pullback_perfect (Φ : OrthFrameCore p Bs X) {K : Subgroup G}
    (hK : K ≤ Φ.ψ.range) (hperf : ⁅K, K⁆ = K) :
    ⁅plh_pullback Φ K, plh_pullback Φ K⁆ = plh_pullback Φ K := by
  unfold plh_pullback
  set K' : Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
    (K.comap Φ.ψ).map (orthDerived Φ.Q).subtype with hK'def
  have hle : K' ≤ orthDerived Φ.Q := by
    intro x hx
    rw [hK'def, Subgroup.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hsub : K'.subgroupOf (orthDerived Φ.Q) = K.comap Φ.ψ := by
    rw [hK'def]
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : y = x := Subtype.ext hyx
      rw [Subgroup.mem_comap] at hy ⊢
      rw [hyx'] at hy
      exact hy
    · intro hx
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      exact ⟨x, hx, rfl⟩
  have himg : (K'.subgroupOf (orthDerived Φ.Q)).map Φ.ψ = K := by
    rw [hsub]
    exact Subgroup.map_comap_eq_self hK
  have h1 : (⁅K'.subgroupOf (orthDerived Φ.Q),
      K'.subgroupOf (orthDerived Φ.Q)⁆).map Φ.ψ = K := by
    rw [Subgroup.map_commutator, himg, hperf]
  have h2 : (⁅K'.subgroupOf (orthDerived Φ.Q),
      K'.subgroupOf (orthDerived Φ.Q)⁆).map Φ.ψ =
      (K'.subgroupOf (orthDerived Φ.Q)).map Φ.ψ := by
    rw [h1, himg]
  have h3 : ⁅K'.subgroupOf (orthDerived Φ.Q),
      K'.subgroupOf (orthDerived Φ.Q)⁆ = K'.subgroupOf (orthDerived Φ.Q) :=
    Subgroup.map_injective Φ.hinj h2
  have h4 : (⁅K'.subgroupOf (orthDerived Φ.Q),
      K'.subgroupOf (orthDerived Φ.Q)⁆).map (orthDerived Φ.Q).subtype = K' := by
    rw [h3, Subgroup.map_subgroupOf_eq_of_le hle]
  have h5 : (⁅K'.subgroupOf (orthDerived Φ.Q),
      K'.subgroupOf (orthDerived Φ.Q)⁆).map (orthDerived Φ.Q).subtype = ⁅K', K'⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle]
  exact h5.symm.trans h4

theorem OrthFrameCore.torStruct_component (Φ : OrthFrameCore p Bs X)
    {t : Φ.V ≃ₗ[Φ.F] Φ.V} (h : Φ.TorStruct t) {J : Subgroup G}
    (hJ : IsComponentOf J (Φ.img (Φ.torC t))) :
    (∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥J ⧸ Subgroup.center ↥J) ∧ lab.n = 1 ∧ lab.tag ≠ .A ∧
          (lab.tag = .twD → lab.rank ≠ 2)) ∧
      ∃ x y : OmPlusIdx Φ.r,
        omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x ∧
          Φ.img (Φ.rank2 x y) ≤ J := by
  obtain ⟨P₀, P₁, hP₀C, hP₁C, hn₀, hn₁, hcomm, hperf, htf₀, htf₁⟩ := h
  have hCΩ : Φ.torC t ≤ orthDerived Φ.Q := by
    unfold OrthFrameCore.torC
    exact inf_le_left
  have hP₀Ω : P₀ ≤ orthDerived Φ.Q := le_trans hP₀C hCΩ
  have hP₁Ω : P₁ ≤ orthDerived Φ.Q := le_trans hP₁C hCΩ
  have hQ₀H : Φ.img P₀ ≤ Φ.img (Φ.torC t) := plh_img_mono Φ hP₀C
  have hQ₁H : Φ.img P₁ ≤ Φ.img (Φ.torC t) := plh_img_mono Φ hP₁C
  have hn₀' : ((Φ.img P₀).subgroupOf (Φ.img (Φ.torC t))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ₀H]
    intro g k hg hk
    rw [OrthFrameCore.img, Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [OrthFrameCore.img, Subgroup.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have haP : (a : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ P₀ := Subgroup.mem_subgroupOf.mp ha
    have hcC : (c : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.torC t := Subgroup.mem_subgroupOf.mp hc
    let aC : ↥(Φ.torC t) := ⟨(a : Φ.V ≃ₗ[Φ.F] Φ.V), hP₀C haP⟩
    let cC : ↥(Φ.torC t) := ⟨(c : Φ.V ≃ₗ[Φ.F] Φ.V), hcC⟩
    have haP' : aC ∈ P₀.subgroupOf (Φ.torC t) := haP
    have hconj : cC * aC * cC⁻¹ ∈ P₀.subgroupOf (Φ.torC t) := hn₀.conj_mem aC haP' cC
    refine Subgroup.mem_map.mpr ⟨c * a * c⁻¹, ?_, ?_⟩
    · show ((c * a * c⁻¹ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ P₀
      simpa using (Subgroup.mem_subgroupOf.mp hconj)
    · rw [map_mul, map_mul, map_inv]
  have hn₁' : ((Φ.img P₁).subgroupOf (Φ.img (Φ.torC t))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hQ₁H]
    intro g k hg hk
    rw [OrthFrameCore.img, Subgroup.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    rw [OrthFrameCore.img, Subgroup.mem_map] at hk
    obtain ⟨c, hc, rfl⟩ := hk
    have haP : (a : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ P₁ := Subgroup.mem_subgroupOf.mp ha
    have hcC : (c : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.torC t := Subgroup.mem_subgroupOf.mp hc
    let aC : ↥(Φ.torC t) := ⟨(a : Φ.V ≃ₗ[Φ.F] Φ.V), hP₁C haP⟩
    let cC : ↥(Φ.torC t) := ⟨(c : Φ.V ≃ₗ[Φ.F] Φ.V), hcC⟩
    have haP' : aC ∈ P₁.subgroupOf (Φ.torC t) := haP
    have hconj : cC * aC * cC⁻¹ ∈ P₁.subgroupOf (Φ.torC t) := hn₁.conj_mem aC haP' cC
    refine Subgroup.mem_map.mpr ⟨c * a * c⁻¹, ?_, ?_⟩
    · show ((c * a * c⁻¹ : ↥(orthDerived Φ.Q)) : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ P₁
      simpa using (Subgroup.mem_subgroupOf.mp hconj)
    · rw [map_mul, map_mul, map_inv]
  have hcomm' : ∀ a ∈ Φ.img P₀, ∀ b ∈ Φ.img P₁, a * b = b * a := by
    intro a ha b hb
    rw [OrthFrameCore.img, Subgroup.mem_map] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    rw [OrthFrameCore.img, Subgroup.mem_map] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    have haP : (a' : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ P₀ := Subgroup.mem_subgroupOf.mp ha'
    have hbP : (b' : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ P₁ := Subgroup.mem_subgroupOf.mp hb'
    have h_ab : (a' : Φ.V ≃ₗ[Φ.F] Φ.V) * (b' : Φ.V ≃ₗ[Φ.F] Φ.V) =
        (b' : Φ.V ≃ₗ[Φ.F] Φ.V) * (a' : Φ.V ≃ₗ[Φ.F] Φ.V) := hcomm _ haP _ hbP
    have hab : a' * b' = b' * a' := Subtype.ext h_ab
    calc Φ.ψ a' * Φ.ψ b' = Φ.ψ (a' * b') := (map_mul Φ.ψ a' b').symm
      _ = Φ.ψ (b' * a') := by rw [hab]
      _ = Φ.ψ b' * Φ.ψ a' := map_mul Φ.ψ b' a'
  have hperf' : ∀ K : Subgroup G, K ≤ Φ.img (Φ.torC t) → ⁅K, K⁆ = K →
      K ≤ Φ.img P₀ ⊔ Φ.img P₁ := by
    intro K hKH hKperf
    have hHrange : Φ.img (Φ.torC t) ≤ Φ.ψ.range := by
      rw [OrthFrameCore.img]
      exact Subgroup.map_le_range Φ.ψ _
    have hKrange : K ≤ Φ.ψ.range := le_trans hKH hHrange
    have hK'leC : plh_pullback Φ K ≤ Φ.torC t := by
      intro x hx
      unfold plh_pullback at hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Subgroup.mem_comap] at hy
      have hyH : Φ.ψ y ∈ Φ.img (Φ.torC t) := hKH hy
      rw [OrthFrameCore.img, Subgroup.mem_map] at hyH
      obtain ⟨c, hc, hcy⟩ := hyH
      have hcy' : c = y := Φ.hinj hcy
      rw [hcy'] at hc
      exact Subgroup.mem_subgroupOf.mp hc
    have hK'perf : ⁅plh_pullback Φ K, plh_pullback Φ K⁆ = plh_pullback Φ K :=
      plh_pullback_perfect Φ hKrange hKperf
    have hK'le : plh_pullback Φ K ≤ P₀ ⊔ P₁ := hperf _ hK'leC hK'perf
    calc K = Φ.img (plh_pullback Φ K) := (plh_img_pullback_eq Φ hKrange).symm
      _ ≤ Φ.img (P₀ ⊔ P₁) := plh_img_mono Φ hK'le
      _ = Φ.img P₀ ⊔ Φ.img P₁ := Φ.img_sup hP₀Ω hP₁Ω
  have hs₀ : Group.IsSolvable ↥(Φ.img P₀) ∨ CFSG.Assembly.IsQuasisimple ↥(Φ.img P₀) := by
    rcases htf₀ with hsol | hq
    · haveI : Group.IsSolvable ↥P₀ := hsol
      exact Or.inl (Group.isSolvable_of_isSolvable_injective
        (f := (plh_imgEquiv Φ P₀ hP₀Ω).symm.toMonoidHom)
        (plh_imgEquiv Φ P₀ hP₀Ω).symm.injective)
    · exact Or.inr (plh_isQuasisimple_of_mulEquiv (plh_imgEquiv Φ P₀ hP₀Ω)
        (plh_assembly_isQuasisimple_of_isQuasisimple hq.1))
  have hs₁ : Group.IsSolvable ↥(Φ.img P₁) ∨ CFSG.Assembly.IsQuasisimple ↥(Φ.img P₁) := by
    rcases htf₁ with hsol | hq
    · haveI : Group.IsSolvable ↥P₁ := hsol
      exact Or.inl (Group.isSolvable_of_isSolvable_injective
        (f := (plh_imgEquiv Φ P₁ hP₁Ω).symm.toMonoidHom)
        (plh_imgEquiv Φ P₁ hP₁Ω).symm.injective)
    · exact Or.inr (plh_isQuasisimple_of_mulEquiv (plh_imgEquiv Φ P₁ hP₁Ω)
        (plh_assembly_isQuasisimple_of_isQuasisimple hq.1))
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hJ.2.2
  have hcase := CFSG.StandardType.QTwo.torComp_eq_of_isComponentOf hQ₀H hQ₁H hn₀' hn₁'
    hcomm' hperf' hs₀ hs₁ hJ
  rcases hcase with hJ₀ | hJ₁
  · have hQ₀qs : CFSG.Assembly.IsQuasisimple ↥(Φ.img P₀) := hJ₀ ▸ hJq
    have hns : ¬ Group.IsSolvable ↥P₀ := plh_not_isSolvable_of_mulEquiv
      (plh_imgEquiv Φ P₀ hP₀Ω) (plh_not_isSolvable_of_isQuasisimple hQ₀qs)
    obtain ⟨hqs, hrest⟩ := htf₀.resolve_left hns
    obtain ⟨hLabel, hPair⟩ := hrest
    obtain ⟨lab, hΛ2, hlab, hn, htag, htwD⟩ := hLabel
    obtain ⟨x, y, hne, hle⟩ := hPair
    refine ⟨⟨lab, hΛ2, ?_, hn, htag, htwD⟩, ⟨x, y, hne, ?_⟩⟩
    · have htrans : GGHasLabel lab (↥(Φ.img P₀) ⧸
          Subgroup.center ↥(Φ.img P₀)) :=
        plh_ggHasLabel_quotCenter_of_mulEquiv (plh_imgEquiv Φ P₀ hP₀Ω) hlab
      rw [hJ₀]
      exact htrans
    · rw [hJ₀]
      exact plh_img_mono Φ hle
  · have hQ₁qs : CFSG.Assembly.IsQuasisimple ↥(Φ.img P₁) := hJ₁ ▸ hJq
    have hns : ¬ Group.IsSolvable ↥P₁ := plh_not_isSolvable_of_mulEquiv
      (plh_imgEquiv Φ P₁ hP₁Ω) (plh_not_isSolvable_of_isQuasisimple hQ₁qs)
    obtain ⟨hqs, hrest⟩ := htf₁.resolve_left hns
    obtain ⟨hLabel, hPair⟩ := hrest
    obtain ⟨lab, hΛ2, hlab, hn, htag, htwD⟩ := hLabel
    obtain ⟨x, y, hne, hle⟩ := hPair
    refine ⟨⟨lab, hΛ2, ?_, hn, htag, htwD⟩, ⟨x, y, hne, ?_⟩⟩
    · have htrans : GGHasLabel lab (↥(Φ.img P₁) ⧸
          Subgroup.center ↥(Φ.img P₁)) :=
        plh_ggHasLabel_quotCenter_of_mulEquiv (plh_imgEquiv Φ P₁ hP₁Ω) hlab
      rw [hJ₁]
      exact htrans
    · rw [hJ₁]
      exact plh_img_mono Φ hle

end OrthTorus

end CFSG.StandardType

end
