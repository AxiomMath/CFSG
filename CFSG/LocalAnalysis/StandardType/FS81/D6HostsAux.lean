module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Weyl
public import CFSG.LocalAnalysis.StandardType.FS81.D6Transport
public import CFSG.LocalAnalysis.StandardType.FS81.RootHostPair

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT

variable {G : Type} [Group G] {K : Subgroup G}

@[expose] def IsFrameModel (B : Basis3 G 7) (e : ↥K ≃* ↥Om12) : Prop :=
  ∀ (i : Fin 6) (hi : B.b i.succ ∈ K),
    ((e ⟨B.b i.succ, hi⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) = frameRot i

private theorem mem_normalizer_of_conj {H : Subgroup G} {g : G}
    (h₁ : ∀ z ∈ H, g * z * g⁻¹ ∈ H) (h₂ : ∀ z ∈ H, g⁻¹ * z * g ∈ H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨h₁ z, fun hz => ?_⟩
  have h := h₂ _ hz
  rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h

private theorem conj_inv_eq {M : Type} [Group M] {r : M} (hr : r ^ 3 = 1) (y : M) :
    r⁻¹ * y * r = r * (r * y * r⁻¹) * r⁻¹ := by
  have h : r⁻¹ = r * r := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact hr
  have h' : r⁻¹ * r⁻¹ = r := by
    rw [← mul_inv_rev, ← h, inv_inv]
  calc r⁻¹ * y * r = (r * r) * y * (r⁻¹ * r⁻¹) := by rw [← h, h']
    _ = r * (r * y * r⁻¹) * r⁻¹ := by group

theorem span_le_normalizer_tr {b₀ : G} {E : Subgroup G} {B : Basis3 G 7}
    (hB : Adapted B b₀ K E) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e) (hrot : ∀ i, frameRot i ^ 3 = 1)
    {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hX : ∀ i, ∀ z ∈ X, frameRot i * z * (frameRot i)⁻¹ ∈ X) :
    E ≤ Subgroup.normalizer (tr e X : Set G) := by
  rw [← hB.1, Basis3.span, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  induction j using Fin.cases with
  | zero =>
    have hc : ∀ z ∈ tr e X, B.b 0 * z = z * B.b 0 := by
      intro z hz
      have := Subgroup.mem_centralizer_iff.mp (hKC (tr_le_K e X hz)) b₀ rfl
      rw [hB.2.1]
      exact this
    refine mem_normalizer_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · rw [hc z hz, mul_inv_cancel_right]
      exact hz
    · rw [mul_assoc, ← hc z hz, inv_mul_cancel_left]
      exact hz
  | succ i =>
    have hbK : B.b i.succ ∈ K := hB.2.2 _ (Fin.succ_ne_zero i)
    have hconj : ∀ z ∈ tr e X, ∀ g : ↥K, (g : G) = B.b i.succ ∨ (g : G) = (B.b i.succ)⁻¹ →
        (g : G) * z * (g : G)⁻¹ ∈ tr e X := by
      intro z hz g hg
      have hzK := tr_le_K e X hz
      have hmem := (mem_tr_iff e X ⟨z, hzK⟩).mp hz
      have h := (mem_tr_iff e X (g * ⟨z, hzK⟩ * g⁻¹)).mpr ?_
      · simpa using h
      have hb : ((e ⟨B.b i.succ, hbK⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) = frameRot i := he i hbK
      rcases hg with hg | hg
      · have hg' : g = ⟨B.b i.succ, hbK⟩ := Subtype.ext hg
        subst hg'
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hb]
        exact hX i _ hmem
      · have hg' : g = (⟨B.b i.succ, hbK⟩ : ↥K)⁻¹ := Subtype.ext hg
        subst hg'
        simp only [map_mul, map_inv, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, hb]
        rw [conj_inv_eq (hrot i)]
        exact hX i _ (hX i _ hmem)
    refine mem_normalizer_of_conj (fun z hz => ?_) (fun z hz => ?_)
    · exact hconj z hz ⟨B.b i.succ, hbK⟩ (Or.inl rfl)
    · have h := hconj z hz (⟨B.b i.succ, hbK⟩ : ↥K)⁻¹ (Or.inr rfl)
      simpa using h

theorem tr_eq_closure (e : ↥K ≃* ↥Om12) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {a b : ↥K}
    (hX : X = Subgroup.closure {((e a : ↥Om12) : V12 ≃ₗ[ZMod 2] V12),
      ((e b : ↥Om12) : V12 ≃ₗ[ZMod 2] V12)}) :
    tr e X = Subgroup.closure {(a : G), (b : G)} := by
  have hH : Subgroup.closure {(a : G), (b : G)} ≤ K := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [a.2, b.2]
  apply le_antisymm
  · calc tr e X ≤ tr e (pull e (Subgroup.closure {(a : G), (b : G)})) := tr_mono e ?_
      _ = _ := tr_pull e hH
    rw [hX, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · refine Subgroup.mem_map.mpr ⟨e a, Subgroup.mem_comap.mpr ?_, rfl⟩
      show (((e.symm (e a)) : ↥K) : G) ∈ _
      rw [MulEquiv.symm_apply_apply]
      exact Subgroup.subset_closure (Set.mem_insert _ _)
    · refine Subgroup.mem_map.mpr ⟨e b, Subgroup.mem_comap.mpr ?_, rfl⟩
      show (((e.symm (e b)) : ↥K) : G) ∈ _
      rw [MulEquiv.symm_apply_apply]
      exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact (mem_tr_iff e X a).mpr (hX ▸ Subgroup.subset_closure (Set.mem_insert _ _))
    · exact (mem_tr_iff e X b).mpr (hX ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem exists_closure_tr (e : ↥K ≃* ↥Om12) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hXO : X ≤ Om12)
    (hpres : ∀ h ∈ X, h ≠ 1 → h ^ 3 = 1 →
      ∃ s ∈ X, s * s = 1 ∧ s * h * s⁻¹ = h⁻¹ ∧ X = Subgroup.closure {h, s})
    {x : G} (hx : x ∈ tr e X) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    ∃ s ∈ tr e X, s * s = 1 ∧ s * x * s⁻¹ = x⁻¹ ∧ tr e X = Subgroup.closure {x, s} := by
  have hxK := tr_le_K e X hx
  obtain ⟨k, rfl⟩ : ∃ k : ↥K, (k : G) = x := ⟨⟨x, hxK⟩, rfl⟩
  have hkX := (mem_tr_iff e X k).mp hx
  have hk1 : ((e k : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ≠ 1 := by
    intro h
    apply hx1
    have h' : e k = 1 := Subtype.ext h
    rw [MulEquiv.map_eq_one_iff] at h'
    exact congrArg Subtype.val h'
  have hk3 : ((e k : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ^ 3 = 1 := by
    have : k ^ 3 = 1 := Subtype.ext hx3
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  obtain ⟨s₀, hs₀X, hs₀2, hs₀h, hXcl⟩ := hpres _ hkX hk1 hk3
  set ks : ↥K := e.symm ⟨s₀, hXO hs₀X⟩ with hks
  have heks : ((e ks : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) = s₀ := by
    rw [hks, MulEquiv.apply_symm_apply]
  have hinj : ∀ y z : ↥K, ((e y : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) =
      ((e z : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) → (y : G) = z := fun y z h =>
    congrArg Subtype.val (e.injective (Subtype.ext h))
  refine ⟨ks, (mem_tr_iff e X ks).mpr (heks ▸ hs₀X), ?_, ?_, ?_⟩
  · have := hinj (ks * ks) 1 (by
      simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one, heks, hs₀2])
    simpa using this
  · have := hinj (ks * k * ks⁻¹) k⁻¹ (by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, heks, hs₀h])
    simpa using this
  · have hXcl' : X = Subgroup.closure {((e k : ↥Om12) : V12 ≃ₗ[ZMod 2] V12),
        ((e ks : ↥Om12) : V12 ≃ₗ[ZMod 2] V12)} := by
      rw [heks]
      exact hXcl
    exact tr_eq_closure e hXcl'

theorem pull_pair (e : ↥K ≃* ↥Om12) {W H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ K) (h₂ : H₂ ≤ K)
    (h : LinearBlockStandardPair (ZMod 2) W H₁ H₂) :
    ∃ W', LinearBlockStandardPair (ZMod 2) W' (pull e H₁) (pull e H₂) := by
  have hW : W ≤ K := (CFSG.StandardType.linearBlockStandardPair_eq_sup h) ▸ sup_le h₁ h₂
  have hpull : ∀ H : Subgroup G, pull e H = (H.subgroupOf K).map (Om12.subtype.comp e.toMonoidHom) := by
    intro H
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨e.symm z, hz, by simp⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e k, by simpa [Subgroup.mem_subgroupOf] using hk, rfl⟩
  rw [hpull, hpull]
  exact ⟨_, CFSG.ClassicalInvolution.Models.linearBlockStandardPair_map
    (CFSG.StandardType.linearBlockStandardPair_subgroupOf K hW h)
    (Om12.subtype.comp e.toMonoidHom) (Subtype.val_injective.comp e.injective)⟩

theorem tr_le_of_rootHost (e : ↥K ≃* ↥Om12) {x : G} (hxK : x ∈ K) {L : Subgroup G}
    (hL : CFSG.StandardType.FrameRoute.FS81.RootHost x L) {W X Y : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hXO : X ≤ Om12) (hYO : Y ≤ Om12) (hp : LinearBlockStandardPair (ZMod 2) W X Y)
    (hX : ∀ a ∈ X, a * (e ⟨x, hxK⟩ : V12 ≃ₗ[ZMod 2] V12) = (e ⟨x, hxK⟩ : V12 ≃ₗ[ZMod 2] V12) * a)
    (hY : ∀ a ∈ Y, a * (e ⟨x, hxK⟩ : V12 ≃ₗ[ZMod 2] V12) = (e ⟨x, hxK⟩ : V12 ≃ₗ[ZMod 2] V12) * a) :
    tr e X ≤ L ∧ tr e Y ≤ L := by
  obtain ⟨W', hW'⟩ := tr_pair e hXO hYO hp
  have hC : ∀ Z : Subgroup (V12 ≃ₗ[ZMod 2] V12), (∀ a ∈ Z, a * (e ⟨x, hxK⟩ : V12 ≃ₗ[ZMod 2] V12) =
      (e ⟨x, hxK⟩ : V12 ≃ₗ[ZMod 2] V12) * a) → tr e Z ≤ Subgroup.centralizer ({x} : Set G) := by
    intro Z hZ z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzK := tr_le_K e Z hz
    have hzZ := (mem_tr_iff e Z ⟨z, hzK⟩).mp hz
    have h : e (⟨z, hzK⟩ * ⟨x, hxK⟩) = e (⟨x, hxK⟩ * ⟨z, hzK⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext (hZ _ hzZ)
    exact congrArg Subtype.val (e.injective h)
  exact CFSG.StandardType.FrameRoute.FS81.le_of_rootHost_of_pair hL hW' (hC X hX) (hC Y hY)

variable {b₀ : G} {E : Subgroup G} {B : Basis3 G 7}

theorem e_vec_pair (hB : Adapted B b₀ K E) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e)
    (i i' : Fin 6) {x : G} (hx : x = B.b i.succ * B.b i'.succ) (h : x ∈ K) :
    ((e ⟨x, h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) = frameRot i * frameRot i' := by
  subst hx
  have h₁ : B.b i.succ ∈ K := hB.2.2 _ (Fin.succ_ne_zero i)
  have h₂ : B.b i'.succ ∈ K := hB.2.2 _ (Fin.succ_ne_zero i')
  rw [show (⟨B.b i.succ * B.b i'.succ, h⟩ : ↥K) = ⟨B.b i.succ, h₁⟩ * ⟨B.b i'.succ, h₂⟩ from rfl,
    map_mul, Subgroup.coe_mul, he i h₁, he i' h₂]

theorem e_vec_pair_inv (hB : Adapted B b₀ K E) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e)
    (i i' : Fin 6) {x : G} (hx : x = B.b i.succ * (B.b i'.succ)⁻¹) (h : x ∈ K) :
    ((e ⟨x, h⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) = frameRot i * (frameRot i')⁻¹ := by
  subst hx
  have h₁ : B.b i.succ ∈ K := hB.2.2 _ (Fin.succ_ne_zero i)
  have h₂ : B.b i'.succ ∈ K := hB.2.2 _ (Fin.succ_ne_zero i')
  rw [show (⟨B.b i.succ * (B.b i'.succ)⁻¹, h⟩ : ↥K) = ⟨B.b i.succ, h₁⟩ * (⟨B.b i'.succ, h₂⟩)⁻¹
      from rfl, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, he i h₁, he i' h₂]

end CFSG.StandardType.FrameRoute.FS81.D6M
