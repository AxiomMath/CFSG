module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.LocalAnalysis.StandardType.FS81.D6HostsAux
public import CFSG.LocalAnalysis.StandardType.FS81.D6Unique

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.ClassicalInvolution.WeakCT

variable {G : Type} [Group G]

theorem mem_map_conj {X : Subgroup G} {w y : G} :
    y ∈ X.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * y * w ∈ X := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [mul_assoc] using hx
  · intro h
    exact ⟨_, h, by simp [mul_assoc]⟩

theorem map_conj_map_conj_inv (X : Subgroup G) (w : G) :
    (X.map (MulAut.conj w⁻¹).toMonoidHom).map (MulAut.conj w).toMonoidHom = X := by
  ext y
  rw [mem_map_conj, mem_map_conj]
  simp [mul_assoc]

theorem le_normalizer_map_conj {E X : Subgroup G} (hEX : E ≤ Subgroup.normalizer (X : Set G))
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) :
    E ≤ Subgroup.normalizer ((X.map (MulAut.conj w).toMonoidHom : Subgroup G) : Set G) := by
  intro t ht
  have ht' : w⁻¹ * t * w ∈ E := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hw)) t
    rw [inv_inv] at h
    exact h.mp ht
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have key := (Subgroup.mem_normalizer_iff.mp (hEX ht')) (w⁻¹ * y * w)
  rw [show w⁻¹ * t * w * (w⁻¹ * y * w) * (w⁻¹ * t * w)⁻¹ = w⁻¹ * (t * y * t⁻¹) * w by group]
    at key
  have e1 : y ∈ X.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * y * w ∈ X := mem_map_conj
  have e2 : t * y * t⁻¹ ∈ X.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * (t * y * t⁻¹) * w ∈ X :=
    mem_map_conj
  exact e1.trans (key.trans e2.symm)

@[expose] def IsRootAt (E : Subgroup G) (B : Basis3 G 7) (X : Subgroup G) (v : Coords 7) : Prop :=
  E ≤ Subgroup.normalizer (X : Set G) ∧ ∃ s ∈ X, s * s = 1 ∧ s * B.vec v * s⁻¹ = (B.vec v)⁻¹ ∧
    X = Subgroup.closure {B.vec v, s}

theorem IsRootAt.map_conj {E X : Subgroup G} {B : Basis3 G 7} {v u : Coords 7}
    (h : IsRootAt E B X v) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hwv : w * B.vec v * w⁻¹ = B.vec u) :
    IsRootAt E B (X.map (MulAut.conj w).toMonoidHom) u := by
  obtain ⟨hEX, s, hsX, hs2, hsv, hXc⟩ := h
  refine ⟨le_normalizer_map_conj hEX hw, w * s * w⁻¹,
    mem_map_conj.mpr (by simpa [mul_assoc] using hsX), ?_, ?_, ?_⟩
  · calc w * s * w⁻¹ * (w * s * w⁻¹) = w * (s * s) * w⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  · rw [← hwv]
    calc w * s * w⁻¹ * (w * B.vec v * w⁻¹) * (w * s * w⁻¹)⁻¹ = w * (s * B.vec v * s⁻¹) * w⁻¹ := by
          group
      _ = (w * B.vec v * w⁻¹)⁻¹ := by rw [hsv]; group
  · rw [hXc, MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hwv]

theorem IsRootAt.eq [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdLoc b₀ K E Row.D6)
    {B : Basis3 G 7} (hB : Adapted B b₀ K E) (hrec : RecOutD6 B b₀) {v : Coords 7}
    (hv0 : v 0 = 0) (hv : wt v = 2) {X Y : Subgroup G} (hX : IsRootAt E B X v)
    (hY : IsRootAt E B Y v) (hXK : X ≤ K) (hYK : Y ≤ K) : X = Y := by
  obtain ⟨hEX, s, hsX, hs2, hsv, hXc⟩ := hX
  obtain ⟨hEY, s', hs'Y, hs'2, hs'v, hYc⟩ := hY
  have hNX : ∀ t ∈ E ⊓ K, ∀ x ∈ Subgroup.closure {B.vec v, s},
      t * x * t⁻¹ ∈ Subgroup.closure {B.vec v, s} := by
    intro t ht x hx
    rw [← hXc] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hEX (Subgroup.mem_inf.mp ht).1) x).mp hx
  have hNY : ∀ t ∈ E ⊓ K, ∀ x ∈ Subgroup.closure {B.vec v, s'},
      t * x * t⁻¹ ∈ Subgroup.closure {B.vec v, s'} := by
    intro t ht x hx
    rw [← hYc] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hEY (Subgroup.mem_inf.mp ht).1) x).mp hx
  rw [hXc, hYc]
  exact eq_of_rootS3_D6 hstd hB hrec hv0 hv (hXK hsX) (hYK hs'Y) hs2 hs'2 hsv hs'v hNX hNY

theorem map_conj_eq_of_isRootAt [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {u v : Coords 7} (hu0 : u 0 = 0) (hu : wt u = 2) {X Y : Subgroup G}
    (hX : IsRootAt E B X u) (hXK : X ≤ K) (hY : IsRootAt E B Y v) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (hwv : w * B.vec u * w⁻¹ = B.vec v)
    (hYL : Y ≤ K.map (MulAut.conj w).toMonoidHom) :
    X.map (MulAut.conj w).toMonoidHom = Y := by
  have hw' : w⁻¹ ∈ Subgroup.normalizer (E : Set G) := Subgroup.inv_mem _ hw
  have hwv' : w⁻¹ * B.vec v * w⁻¹⁻¹ = B.vec u := by rw [← hwv]; group
  have hYK : Y.map (MulAut.conj w⁻¹).toMonoidHom ≤ K := by
    intro y hy
    rw [mem_map_conj, inv_inv] at hy
    have h := hYL hy
    rw [mem_map_conj] at h
    simpa [mul_assoc] using h
  rw [IsRootAt.eq hstd hB hrec hu0 hu hX (hY.map_conj hw' hwv') hXK hYK,
    map_conj_map_conj_inv]

private theorem vec_pow_three (B : Basis3 G 7) (v : Coords 7) : B.vec v ^ 3 = 1 := by
  have h3 : v + v + v = 0 := by
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    generalize v i = x
    revert x
    decide
  rw [pow_succ, pow_two, ← B.vec_add, ← B.vec_add, h3, B.vec_zero]

theorem isRootAt_tr {b₀ : G} {K E : Subgroup G} {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) {e : ↥K ≃* ↥Om12} (he : IsFrameModel B e)
    (hrot : ∀ i, frameRot i ^ 3 = 1) {X : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hXO : X ≤ Om12)
    (hXT : ∀ i, ∀ z ∈ X, frameRot i * z * (frameRot i)⁻¹ ∈ X)
    (hpres : ∀ h ∈ X, h ≠ 1 → h ^ 3 = 1 →
      ∃ s ∈ X, s * s = 1 ∧ s * h * s⁻¹ = h⁻¹ ∧ X = Subgroup.closure {h, s})
    {v : Coords 7} (hv : v ≠ 0) (hvK : B.vec v ∈ K)
    (hvX : ((e ⟨B.vec v, hvK⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ X) :
    IsRootAt E B (tr e X) v := by
  refine ⟨span_le_normalizer_tr hB hKC he hrot hXT, ?_⟩
  have hx : B.vec v ∈ tr e X := (mem_tr_iff e X ⟨B.vec v, hvK⟩).mpr hvX
  have hx1 : B.vec v ≠ 1 := fun h => hv (B.vec_injective (h.trans B.vec_zero.symm))
  obtain ⟨s, hs, hs2, hsv, hc⟩ := exists_closure_tr e hXO hpres hx hx1 (vec_pow_three B v)
  exact ⟨s, hs, hs2, hsv, hc⟩

theorem rootHost_map_conj [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G 7} (hB : Adapted B b₀ K E)
    (hrec : RecOutD6 B b₀) {w x : G} (hw : w * b₀ * w⁻¹ = x) :
    CFSG.StandardType.FrameRoute.FS81.RootHost x (K.map (MulAut.conj w).toMonoidHom) := by
  rw [← hw]
  exact (CFSG.StandardType.FrameRoute.FS81.rootHost_D6 hstd hB hrec).conj w

theorem tr_le_host {K L : Subgroup G} (e : ↥K ≃* ↥Om12) {x : G} (hxK : x ∈ K)
    (hL : CFSG.StandardType.FrameRoute.FS81.RootHost x L)
    {W X Y Z : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hXO : X ≤ Om12) (hYO : Y ≤ Om12)
    (hp : LinearBlockStandardPair (ZMod 2) W X Y)
    (hxZ : ((e ⟨x, hxK⟩ : ↥Om12) : V12 ≃ₗ[ZMod 2] V12) ∈ Z)
    (hXZ : ∀ a ∈ X, ∀ c ∈ Z, a * c = c * a) (hYZ : ∀ a ∈ Y, ∀ c ∈ Z, a * c = c * a) :
    tr e X ≤ L ∧ tr e Y ≤ L :=
  tr_le_of_rootHost e hxK hL hXO hYO hp (fun a ha => hXZ a ha _ hxZ) (fun a ha => hYZ a ha _ hxZ)

theorem conjModel_apply_mk {K : Subgroup G} (e : ↥K ≃* ↥Om12) (w : G) {y : G}
    (hy : y ∈ K.map (MulAut.conj w).toMonoidHom) (hy' : w⁻¹ * y * w ∈ K) :
    conjModel e w ⟨y, hy⟩ = e ⟨w⁻¹ * y * w, hy'⟩ := by
  have hmem : w * ((⟨w⁻¹ * y * w, hy'⟩ : ↥K) : G) * w⁻¹ ∈ K.map (MulAut.conj w).toMonoidHom := by
    rw [show w * ((⟨w⁻¹ * y * w, hy'⟩ : ↥K) : G) * w⁻¹ = y by
      show w * (w⁻¹ * y * w) * w⁻¹ = y
      group]
    exact hy
  rw [← conjModel_apply e w ⟨w⁻¹ * y * w, hy'⟩ hmem]
  congr 1
  apply Subtype.ext
  show y = w * (w⁻¹ * y * w) * w⁻¹
  group

theorem conjModel_vec {K : Subgroup G} (e : ↥K ≃* ↥Om12) {B : Basis3 G 7} {w : G}
    {v u : Coords 7} (hwv : w⁻¹ * B.vec v * w = B.vec u)
    (hv : B.vec v ∈ K.map (MulAut.conj w).toMonoidHom) (hu : B.vec u ∈ K) :
    conjModel e w ⟨B.vec v, hv⟩ = e ⟨B.vec u, hu⟩ := by
  rw [conjModel_apply_mk e w hv (by rw [hwv]; exact hu)]
  congr 1
  exact Subtype.ext hwv

end CFSG.StandardType.FrameRoute.FS81.D6M
