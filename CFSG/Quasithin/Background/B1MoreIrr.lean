module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.D2Basic
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem fixed_eq_inf_fixV (H : Subgroup (MulAut V)) (I : Subgroup V) :
    XMod.fixed ↥H I = I ⊓ fixV H := by
  ext v
  simp only [XMod.mem_fixed, Subgroup.mem_inf, mem_fixV]
  constructor
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun x hx => h ⟨x, hx⟩⟩
  · rintro ⟨hv, h⟩
    exact ⟨hv, fun a => h a a.2⟩

theorem commOf_eq_commSub (H : Subgroup (MulAut V)) (I : Subgroup V) :
    XMod.commOf ↥H I = commSub I H := by
  unfold XMod.commOf commSub
  congr 1
  ext c
  constructor
  · rintro ⟨a, l, hl, rfl⟩
    exact ⟨a, a.2, l, hl, rfl⟩
  · rintro ⟨x, hx, w, hw, rfl⟩
    exact ⟨⟨x, hx⟩, w, hw, rfl⟩

theorem isInv_iff (H : Subgroup (MulAut V)) (J : Subgroup V) :
    XMod.IsInv ↥H J ↔ ∀ x ∈ H, ∀ w ∈ J, x w ∈ J :=
  ⟨fun h x hx w hw => h ⟨x, hx⟩ w hw, fun h a w hw => h a a.2 w hw⟩

theorem mem_irrPlus_top_iff {H : Subgroup (MulAut V)} {I : Subgroup V} :
    I ∈ IrrPlus H (⊤ : Subgroup V) ↔
      (∀ x ∈ H, ∀ w ∈ I, x w ∈ I) ∧ commSub I H = I ∧ I ⊓ fixV H < I ∧
        ∀ J : Subgroup V, (∀ x ∈ H, ∀ w ∈ J, x w ∈ J) → I ⊓ fixV H ≤ J → J ≤ I →
          J = I ⊓ fixV H ∨ J = I := by
  unfold IrrPlus
  simp only [Set.mem_ofPred_eq, le_top, true_and]
  unfold XMod.IsIrrPlus XMod.IsIrrSec
  rw [fixed_eq_inf_fixV, commOf_eq_commSub, isInv_iff]
  simp only [isInv_iff]

theorem isInv_sup {H : Subgroup (MulAut V)} {X Y : Subgroup V}
    (hX : ∀ x ∈ H, ∀ w ∈ X, x w ∈ X) (hY : ∀ x ∈ H, ∀ w ∈ Y, x w ∈ Y) :
    ∀ x ∈ H, ∀ w ∈ X ⊔ Y, x w ∈ X ⊔ Y := by
  intro x hx w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hX x hx a ha) (hY x hx b hb)

theorem isInv_inf {H : Subgroup (MulAut V)} {X Y : Subgroup V}
    (hX : ∀ x ∈ H, ∀ w ∈ X, x w ∈ X) (hY : ∀ x ∈ H, ∀ w ∈ Y, x w ∈ Y) :
    ∀ x ∈ H, ∀ w ∈ X ⊓ Y, x w ∈ X ⊓ Y :=
  fun x hx w hw => ⟨hX x hx w hw.1, hY x hx w hw.2⟩

theorem isInv_fixV (H : Subgroup (MulAut V)) : ∀ x ∈ H, ∀ w ∈ fixV H, x w ∈ fixV H := by
  intro x hx w hw
  rw [hw x hx]
  exact hw

theorem commSub_sup_fixV {H : Subgroup (MulAut V)} {J Z : Subgroup V} (hZ : Z ≤ fixV H) :
    commSub (J ⊔ Z) H = commSub J H := by
  refine le_antisymm ?_ (commSub_mono le_sup_left le_rfl)
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨j, hj, z, hz, rfl⟩ := Subgroup.mem_sup.1 hw
  have h1 : x (j * z) * (j * z)⁻¹ = x j * j⁻¹ := by
    rw [map_mul, hZ hz x hx]
    group
  rw [h1]
  exact Subgroup.subset_closure ⟨x, hx, j, hj, rfl⟩

theorem irrPlus_sup_inf {H : Subgroup (MulAut V)} {I J : Subgroup V}
    (hI : I ∈ IrrPlus H (⊤ : Subgroup V)) (hJ : J ∈ IrrPlus H (⊤ : Subgroup V)) :
    I = J ∨ (I ⊔ fixV H) ⊓ (J ⊔ fixV H) = fixV H := by
  rw [mem_irrPlus_top_iff] at hI hJ
  obtain ⟨invI, commI, ltI, irrI⟩ := hI
  obtain ⟨invJ, commJ, ltJ, irrJ⟩ := hJ
  set Z := fixV H with hZ
  have invZ : ∀ x ∈ H, ∀ w ∈ Z, x w ∈ Z := isInv_fixV H
  have hIZ' : ¬ I ≤ Z := by
    intro h
    have := inf_eq_left.2 h
    rw [this] at ltI
    exact lt_irrefl _ ltI
  set T := (I ⊔ Z) ⊓ (J ⊔ Z) with hT
  have invT : ∀ x ∈ H, ∀ w ∈ T, x w ∈ T :=
    isInv_inf (isInv_sup invI invZ) (isInv_sup invJ invZ)
  have hZT : Z ≤ T := le_inf le_sup_right le_sup_right
  have hIZle : I ⊓ Z ≤ T ⊓ I := le_inf (le_inf (inf_le_left.trans le_sup_left)
    (inf_le_right.trans le_sup_right)) inf_le_left
  rcases irrI (T ⊓ I) (isInv_inf invT invI) hIZle inf_le_right with h | h
  ·
    right
    have h1 : T ⊓ I ⊔ Z = T ⊓ (I ⊔ Z) := inf_sup_assoc_of_le I hZT
    rw [inf_eq_left.2 (inf_le_left : T ≤ I ⊔ Z), h] at h1
    rw [sup_eq_right.2 inf_le_right] at h1
    exact h1.symm
  ·
    left
    have hIT : I ≤ T := by
      calc I = T ⊓ I := h.symm
        _ ≤ T := inf_le_left
    have hIJZ : I ≤ J ⊔ Z := hIT.trans inf_le_right
    have hIJ : I ≤ J := by
      calc I = commSub I H := commI.symm
        _ ≤ commSub (J ⊔ Z) H := commSub_mono hIJZ le_rfl
        _ = commSub J H := commSub_sup_fixV le_rfl
        _ ≤ J := commSub_le_of_invariant invJ
    set K := I ⊔ J ⊓ Z with hK
    have hKJ : K ≤ J := sup_le hIJ inf_le_left
    rcases irrJ K (isInv_sup invI (isInv_inf invJ invZ)) le_sup_right hKJ with h2 | h2
    · exfalso
      apply hIZ'
      calc I ≤ K := le_sup_left
        _ = J ⊓ Z := h2
        _ ≤ Z := inf_le_right
    · have hJI : J ≤ I := by
        have h3 : J ≤ I ⊔ Z := by
          calc J = K := h2.symm
            _ ≤ I ⊔ Z := sup_le_sup_left inf_le_right I
        calc J = commSub J H := commJ.symm
          _ ≤ commSub (I ⊔ Z) H := commSub_mono h3 le_rfl
          _ = commSub I H := commSub_sup_fixV le_rfl
          _ ≤ I := commSub_le_of_invariant invI
      exact le_antisymm hIJ hJI

theorem mem_map_aut_iff {g : MulAut V} {I : Subgroup V} {w : V} :
    w ∈ I.map g.toMonoidHom ↔ g⁻¹ w ∈ I := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using hi
  · intro h
    exact ⟨g⁻¹ w, h, by simp⟩

theorem irrPlus_map {H : Subgroup (MulAut V)} {g : MulAut V} (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (hg' : ∀ x ∈ H, g⁻¹ * x * g ∈ H) {I : Subgroup V}
    (hI : I ∈ IrrPlus H (⊤ : Subgroup V)) : I.map g.toMonoidHom ∈ IrrPlus H (⊤ : Subgroup V) := by
  rw [mem_irrPlus_top_iff] at hI ⊢
  obtain ⟨invI, commI, ltI, irrI⟩ := hI
  set I' := I.map g.toMonoidHom with hI'
  have hZg : ∀ w, w ∈ fixV H ↔ g w ∈ fixV H := by
    intro w
    constructor
    · intro hw x hx
      have := hw (g⁻¹ * x * g) (hg' x hx)
      have h2 : g (g⁻¹ (x (g w))) = x (g w) := by simp
      calc x (g w) = g ((g⁻¹ * x * g) w) := by simp [MulAut.mul_apply]
        _ = g w := by rw [this]
    · intro hw x hx
      have := hw (g * x * g⁻¹) (hg x hx)
      have h3 : g (x w) = g w := by
        calc g (x w) = (g * x * g⁻¹) (g w) := by simp [MulAut.mul_apply]
          _ = g w := this
      exact g.injective h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx w hw
    rw [hI', mem_map_aut_iff] at hw ⊢
    have h1 : g⁻¹ (x w) = (g⁻¹ * x * g) (g⁻¹ w) := by simp [MulAut.mul_apply]
    rw [h1]
    exact invI _ (hg' x hx) _ hw
  · apply le_antisymm
    · rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      rw [hI', mem_map_aut_iff] at hw
      show x w * w⁻¹ ∈ I'
      rw [hI', mem_map_aut_iff]
      have h1 : g⁻¹ (x w * w⁻¹) = (g⁻¹ * x * g) (g⁻¹ w) * (g⁻¹ w)⁻¹ := by
        simp [MulAut.mul_apply]
      rw [h1, ← commI]
      exact Subgroup.subset_closure ⟨_, hg' x hx, _, hw, rfl⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [← commI] at hi
      refine Subgroup.closure_induction (p := fun i _ => g i ∈ commSub I' H) ?_ ?_ ?_ ?_ hi
      · rintro _ ⟨y, hy, w, hw, rfl⟩
        have h1 : g (y w * w⁻¹) = (g * y * g⁻¹) (g w) * (g w)⁻¹ := by
          simp [MulAut.mul_apply]
        show g (y w * w⁻¹) ∈ commSub I' H
        rw [h1]
        exact Subgroup.subset_closure ⟨_, hg y hy, _, ⟨w, hw, rfl⟩, rfl⟩
      · simp
      · intro a b _ _ ha hb
        simpa using (commSub I' H).mul_mem ha hb
      · intro a _ ha
        simpa using (commSub I' H).inv_mem ha
  · refine lt_of_le_of_ne inf_le_left fun h => ?_
    have h1 : I' ≤ fixV H := by
      rw [← h]
      exact inf_le_right
    have h2 : I ≤ fixV H := by
      intro i hi
      exact (hZg i).2 (h1 ⟨i, hi, rfl⟩)
    have : I ⊓ fixV H = I := inf_eq_left.2 h2
    rw [this] at ltI
    exact lt_irrefl _ ltI
  · intro J invJ hJ1 hJ2
    set J' := J.map (g⁻¹).toMonoidHom with hJ'
    have hmem : ∀ w, w ∈ J' ↔ g w ∈ J := by
      intro w
      rw [hJ', mem_map_aut_iff]
      simp
    have invJ' : ∀ x ∈ H, ∀ w ∈ J', x w ∈ J' := by
      intro x hx w hw
      rw [hmem] at hw ⊢
      have h1 : g (x w) = (g * x * g⁻¹) (g w) := by simp [MulAut.mul_apply]
      rw [h1]
      exact invJ _ (hg x hx) _ hw
    have hJ'1 : I ⊓ fixV H ≤ J' := by
      intro i hi
      rw [hmem]
      apply hJ1
      refine ⟨⟨i, hi.1, rfl⟩, (hZg i).1 hi.2⟩
    have hJ'2 : J' ≤ I := by
      intro w hw
      rw [hmem] at hw
      have := hJ2 hw
      rw [hI', mem_map_aut_iff] at this
      simpa using this
    have hJJ : J = J'.map g.toMonoidHom := by
      ext w
      rw [mem_map_aut_iff, hmem]
      simp
    rcases irrI J' invJ' hJ'1 hJ'2 with h | h
    · left
      rw [hJJ, h]
      ext w
      rw [mem_map_aut_iff]
      simp only [Subgroup.mem_inf, hI', mem_map_aut_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by simpa using (hZg _).1 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (hZg _).2 (by simpa using h2)⟩
    · right
      rw [hJJ, h]

end CFSG.Quasithin
