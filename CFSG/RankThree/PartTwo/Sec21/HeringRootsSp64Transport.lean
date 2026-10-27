module

public import CFSG.RankThree.PartTwo.Sec21.Item233RootsL44

public section

namespace CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def RootModel {K : Type} [Group K] (A0 : Subgroup K) : Prop :=
  ∀ D : Set (MulAut A0), (∀ φ ∈ D, IsReflectionOn φ) →
    (∀ g ∈ starOf A0 (⊤ : Subgroup K), ∀ φ ∈ D, g * φ * g⁻¹ ∈ D) →
    Subgroup.closure D = starOf A0 (⊤ : Subgroup K) →
    ∀ b ∈ A0, b ≠ 1 → ∀ Y : Subgroup (Subgroup.centralizer ({b} : Set K)),
      CFSG.IsComponent Y → ∃ φ ∈ D, ∀ P : Subgroup K,
        P ≤ Subgroup.centralizer (fixedInG A0 φ : Set K) → Group.IsPerfect P →
          P ≤ Y.map (Subgroup.centralizer ({b} : Set K)).subtype

section Transport

variable {G K : Type} [Group G] [Group K]

@[expose] noncomputable def restrA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K)
    {A0 : Subgroup K} (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) : A ≃* A0 :=
  (Subgroup.subgroupOfEquivOfLe hAI).symm.trans
    ((MulEquiv.subgroupMap Φ (A.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦA))

theorem coe_restrA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K) {A0 : Subgroup K}
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (c : A) :
    ((restrA hAI Φ hΦA c : A0) : K) = Φ ⟨(c : G), hAI c.2⟩ := rfl

theorem mem_A_iff_Phi {I A : Subgroup G} (Φ : I ≃* K) {A0 : Subgroup K}
    (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (h : I) :
    (h : G) ∈ A ↔ Φ h ∈ A0 :=
  Subgroup.mem_subgroupOf.symm.trans
    ((Subgroup.mem_map_iff_mem (f := Φ.toMonoidHom) Φ.injective).symm.trans
      (by rw [hΦA]; exact Iff.rfl))

theorem mem_normalizer_iff_Phi {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K)
    {A0 : Subgroup K} (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (y : I) :
    (y : G) ∈ Subgroup.normalizer (A : Set G) ↔ Φ y ∈ Subgroup.normalizer (A0 : Set K) := by
  have key := mem_A_iff_Phi Φ hΦA
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hy m
    obtain ⟨h, rfl⟩ := Φ.surjective m
    have e1 : Φ y * Φ h * (Φ y)⁻¹ = Φ (y * h * y⁻¹) := by simp only [map_mul, map_inv]
    rw [e1]
    exact (key h).symm.trans ((hy (h : G)).trans (key (y * h * y⁻¹)))
  · intro hm g
    by_cases hg : g ∈ I
    · obtain ⟨h, rfl⟩ : ∃ h : I, (h : G) = g := ⟨⟨g, hg⟩, rfl⟩
      have e1 : Φ y * Φ h * (Φ y)⁻¹ = Φ (y * h * y⁻¹) := by simp only [map_mul, map_inv]
      have k2 : Φ h ∈ A0 ↔ Φ (y * h * y⁻¹) ∈ A0 := by
        rw [← e1]
        exact hm (Φ h)
      exact (key h).trans (k2.trans (key (y * h * y⁻¹)).symm)
    · have hgA : g ∉ A := fun hgA => hg (hAI hgA)
      have hyg : (y : G) * g * (y : G)⁻¹ ∉ I := by
        intro hI
        apply hg
        have e : (y : G)⁻¹ * ((y : G) * g * (y : G)⁻¹) * (y : G) = g := by group
        rw [← e]
        exact I.mul_mem (I.mul_mem (I.inv_mem y.2) hI) y.2
      exact ⟨fun h => absurd h hgA, fun h => absurd (hAI h) hyg⟩

theorem congr_normalizer_aux {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K)
    {A0 : Subgroup K} (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0)
    (n : Subgroup.normalizer (A : Set G)) (hn : (n : G) ∈ I) :
    MulAut.congr (restrA hAI Φ hΦA) (A.normalizerMonoidHom n) =
      A0.normalizerMonoidHom ⟨Φ ⟨(n : G), hn⟩,
        (mem_normalizer_iff_Phi hAI Φ hΦA ⟨(n : G), hn⟩).mp n.2⟩ := by
  apply MulEquiv.ext
  intro a'
  apply Subtype.ext
  obtain ⟨c, rfl⟩ := (restrA hAI Φ hΦA).surjective a'
  have hxy : (⟨((A.normalizerMonoidHom n c : A) : G), hAI (A.normalizerMonoidHom n c).2⟩ : I) =
      (⟨(n : G), hn⟩ : I) * ⟨(c : G), hAI c.2⟩ * (⟨(n : G), hn⟩ : I)⁻¹ :=
    Subtype.ext (normalizerMonoidHom_coe_apply_G n c)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    normalizerMonoidHom_coe_apply_G, coe_restrA hAI Φ hΦA, coe_restrA hAI Φ hΦA, hxy, map_mul,
    map_mul, map_inv]

theorem starOf_map_restrA {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K)
    {A0 : Subgroup K} (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) :
    (starOf A I).map (MulAut.congr (restrA hAI Φ hΦA)).toMonoidHom =
      starOf A0 (⊤ : Subgroup K) := by
  ext φ
  constructor
  · intro hφ
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hψ
    rw [MulEquiv.coe_toMonoidHom,
      congr_normalizer_aux hAI Φ hΦA x (Subgroup.mem_subgroupOf.mp hx)]
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_top _), rfl⟩
  · intro hφ
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨y, hy⟩ : ∃ y : I, Φ y = (m : K) := ⟨Φ.symm (m : K), Φ.apply_symm_apply _⟩
    have hyN : (y : G) ∈ Subgroup.normalizer (A : Set G) :=
      (mem_normalizer_iff_Phi hAI Φ hΦA y).mpr (by rw [hy]; exact m.2)
    refine Subgroup.mem_map.mpr ⟨A.normalizerMonoidHom ⟨(y : G), hyN⟩, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨⟨(y : G), hyN⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, congr_normalizer_aux hAI Φ hΦA ⟨(y : G), hyN⟩ y.2]
      congr 1
      apply Subtype.ext
      exact hy

theorem congr_restrA_apply {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K)
    {A0 : Subgroup K} (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (φ : MulAut A) (a : A) :
    MulAut.congr (restrA hAI Φ hΦA) φ (restrA hAI Φ hΦA a) = restrA hAI Φ hΦA (φ a) := by
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

@[expose] noncomputable def restrC {I H : Subgroup G} (hHI : H ≤ I) (Φ : I ≃* K)
    {C : Subgroup K} (hΦH : (H.subgroupOf I).map Φ.toMonoidHom = C) : H ≃* C :=
  (Subgroup.subgroupOfEquivOfLe hHI).symm.trans
    ((MulEquiv.subgroupMap Φ (H.subgroupOf I)).trans (MulEquiv.subgroupCongr hΦH))

theorem isPerfect_map_subgroupOf_aux {I P : Subgroup G} (hPI : P ≤ I) (Φ : I ≃* K)
    (hP : Group.IsPerfect P) : Group.IsPerfect ((P.subgroupOf I).map Φ.toMonoidHom) := by
  haveI : Group.IsPerfect (P.subgroupOf I) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hPI).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hPI).symm.surjective
  exact Group.IsPerfect.map Φ.toMonoidHom

theorem root_of_model [Finite G] {I A : Subgroup G} (hAI : A ≤ I) (Φ : I ≃* K)
    {A0 : Subgroup K} (hΦA : (A.subgroupOf I).map Φ.toMonoidHom = A0) (hM : RootModel A0)
    (D : Set (MulAut A)) (hrefl : ∀ φ ∈ D, IsReflectionOn φ)
    (hconj : ∀ g ∈ starOf A I, ∀ φ ∈ D, g * φ * g⁻¹ ∈ D) (hcl : Subgroup.closure D = starOf A I)
    (B : Subgroup G) (hBA : B ≤ A) (hB3 : Nat.card B = 3)
    (X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G)) (hX : CFSG.IsComponent X) :
    ∃ φ ∈ D, ∀ P : Subgroup G, P ≤ I →
      P ≤ Subgroup.centralizer (fixedInG A φ : Set G) → Group.IsPerfect P →
        P ≤ X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype := by
  obtain ⟨b, -, hb1, rfl⟩ := exists_gen_of_card_three hB3
  have hbA : b ∈ A := hBA (Subgroup.mem_zpowers b)
  have hbI : b ∈ I := hAI hbA
  have ha1 : (⟨b, hbA⟩ : A) ≠ 1 := fun h => hb1 (congrArg Subtype.val h)
  set θ := restrA hAI Φ hΦA with hθ
  have hrefl' : ∀ φ ∈ (MulAut.congr θ) '' D, IsReflectionOn φ := by
    rintro _ ⟨φ, hφ, rfl⟩
    exact isReflectionOn_congr θ φ (hrefl φ hφ)
  have hconj' : ∀ g ∈ starOf A0 (⊤ : Subgroup K), ∀ φ ∈ (MulAut.congr θ) '' D,
      g * φ * g⁻¹ ∈ (MulAut.congr θ) '' D := by
    intro g hg φ hφ
    obtain ⟨φ0, hφ0, rfl⟩ := hφ
    have hg' : g ∈ (starOf A I).map (MulAut.congr θ).toMonoidHom := by
      rw [hθ, starOf_map_restrA hAI Φ hΦA]
      exact hg
    obtain ⟨g', hg'I, rfl⟩ := Subgroup.mem_map.mp hg'
    refine ⟨g' * φ0 * g'⁻¹, hconj g' hg'I φ0 hφ0, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  have hcl' : Subgroup.closure ((MulAut.congr θ) '' D) = starOf A0 (⊤ : Subgroup K) := by
    have h1 : Subgroup.closure ((MulAut.congr θ) '' D) =
        (Subgroup.closure D).map (MulAut.congr θ).toMonoidHom := by
      rw [MonoidHom.map_closure, MulEquiv.coe_toMonoidHom]
    rw [h1, hcl, hθ, starOf_map_restrA hAI Φ hΦA]
  have hb'A : Φ ⟨b, hbI⟩ ∈ A0 := (restrA hAI Φ hΦA ⟨b, hbA⟩).2
  have hb'1 : Φ ⟨b, hbI⟩ ≠ 1 := by
    intro h
    apply ha1
    apply θ.injective
    rw [map_one]
    apply Subtype.ext
    exact h
  have hHI : I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ I :=
    inf_le_left
  have hΦH : ((I ⊓ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G)).subgroupOf
      I).map Φ.toMonoidHom = Subgroup.centralizer ({Φ ⟨b, hbI⟩} : Set K) :=
    map_inf_centralizer_zpowers Φ hbI
  have hY := CFSG.LocalCores.isComponent_map_mulEquiv (restrC hHI Φ hΦH) hX
  obtain ⟨ψ', hψ'D, hψ'⟩ := hM _ hrefl' hconj' hcl' (Φ ⟨b, hbI⟩) hb'A hb'1 _ hY
  obtain ⟨ψ, hψD, rfl⟩ := hψ'D
  refine ⟨ψ, hψD, fun P hPI hPC hPperf => ?_⟩
  have hQ := isPerfect_map_subgroupOf_aux hPI Φ hPperf
  have hcomm : (P.subgroupOf I).map Φ.toMonoidHom ≤
      Subgroup.centralizer (fixedInG A0 (MulAut.congr θ ψ) : Set K) := by
    rintro _ ⟨x, hx, rfl⟩ z hz
    obtain ⟨a0, ha0fix, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨a, rfl⟩ := θ.surjective a0
    have hfix : ψ a = a := by
      apply θ.injective
      rw [← congr_restrA_apply hAI Φ hΦA ψ a]
      exact ha0fix
    have hcomm0 : (a : G) * (x : G) = (x : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp (hPC (Subgroup.mem_subgroupOf.mp hx)) (a : G)
        (mem_fixedInG_of hfix)
    have hcomm1 : (⟨(a : G), hAI a.2⟩ : I) * x = x * ⟨(a : G), hAI a.2⟩ := Subtype.ext hcomm0
    exact (Phi_comm_iff Φ _ x).mpr hcomm1
  have hmain := hψ' _ hcomm hQ
  intro x hx
  have hxI : x ∈ I := hPI hx
  have hmem : Φ ⟨x, hxI⟩ ∈ (P.subgroupOf I).map Φ.toMonoidHom :=
    Subgroup.mem_map.mpr ⟨⟨x, hxI⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hmain hmem)
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hzx : Φ ⟨(z : G), hHI z.2⟩ = Φ ⟨x, hxI⟩ := hyx
  have hzx' := congrArg Subtype.val (Φ.injective hzx)
  exact Subgroup.mem_map.mpr ⟨z, hz, hzx'⟩

end Transport

end CFSG.RankThree.PartTwo.Sec21.HeringRootsSp64

end
