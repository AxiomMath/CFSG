module

public import CFSG.Quasithin.Background.SmithB51LnReal
public import CFSG.Quasithin.Background.SmithB51LnAut

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B5.Ln

open CFSG.Assembly.LowTwoRank Matrix Module
open scoped Matrix

variable {V : Type} [CommGroup V] {n : ℕ} {L : Subgroup (MulAut V)} {W Y : Subgroup V}
  {π : ↥(StatedSL n (ZMod 2)) →* ↥L} {M : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)}

@[expose] def mulM (Q : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Multiplicative (Fin n → ZMod 2) →* Multiplicative (Fin n → ZMod 2) :=
  AddMonoidHom.toMultiplicative (Matrix.mulVecLin Q).toAddMonoidHom

theorem toAdd_mulM (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (x : Multiplicative (Fin n → ZMod 2)) :
    Multiplicative.toAdd (mulM Q x) = Q *ᵥ Multiplicative.toAdd x := rfl

theorem RealM.twist (h : RealM L W Y π M) {π₀ : ↥(StatedSL n (ZMod 2)) →* ↥L}
    (σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))) (hσ : ∀ γ, π γ = π₀ (σ γ))
    {M' : ↥(StatedSL n (ZMod 2)) → Matrix (Fin n) (Fin n) (ZMod 2)} (Q : GL (Fin n) (ZMod 2))
    (hQ : ∀ γ, (Q : Matrix (Fin n) (Fin n) (ZMod 2)) * M γ = M' (σ γ) * Q) :
    RealM L W Y π₀ M' := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  set q := mulM (Q : Matrix (Fin n) (Fin n) (ZMod 2)) with hqdef
  have hQinv : ∀ x : Fin n → ZMod 2,
      ((Q⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hQinv' : ∀ x : Fin n → ZMod 2, (Q : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((Q⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine ⟨fun l => ?_, hYW, hLW, hLY, q.comp β, fun y => ?_, fun w => ?_, fun δ w hw => ?_⟩
  · obtain ⟨γ, hγ⟩ := hπ l
    exact ⟨σ γ, by rw [← hσ, hγ]⟩
  · obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd
      (((Q⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ Multiplicative.toAdd y))
    refine ⟨w, Multiplicative.toAdd.injective ?_⟩
    rw [MonoidHom.comp_apply, hqdef, toAdd_mulM, hw, toAdd_ofAdd, hQinv']
  · rw [MonoidHom.comp_apply, ← hβk w]
    constructor
    · intro h1
      apply Multiplicative.toAdd.injective
      have h2 := congrArg
        (fun x => ((Q⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
          Multiplicative.toAdd x) h1
      simp only [hqdef, toAdd_mulM, hQinv, toAdd_one, mulVec_zero] at h2
      rw [h2, toAdd_one]
    · intro h1
      rw [h1, map_one]
  · obtain ⟨γ, rfl⟩ := σ.surjective δ
    have hw' : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := by rw [hσ]; exact hw
    have h2 : (⟨((π₀ (σ γ) : ↥L) : MulAut V) (w : V), hw⟩ : ↥W) =
        ⟨((π γ : ↥L) : MulAut V) (w : V), hw'⟩ := by
      apply Subtype.ext
      show ((π₀ (σ γ) : ↥L) : MulAut V) (w : V) = ((π γ : ↥L) : MulAut V) (w : V)
      rw [hσ]
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hqdef, toAdd_mulM, toAdd_mulM, h2, hβe γ w hw',
      mulVec_mulVec, hQ, ← mulVec_mulVec]

theorem dmat_of_mat_conj {σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))}
    {P : GL (Fin n) (ZMod 2)}
    (hP : ∀ g, mat (σ g) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * mat g *
      ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))
    (γ : ↥(StatedSL n (ZMod 2))) :
    dmat (σ γ) = ((invT P : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat γ *
      ((invT P)⁻¹ : GL (Fin n) (ZMod 2)) := by
  rw [dmat, ← map_inv, hP, dmat, transpose_mul, transpose_mul, ← Matrix.mul_assoc]
  rfl

theorem dmat_of_dmat_conj {σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2))}
    {P : GL (Fin n) (ZMod 2)}
    (hP : ∀ g, mat (σ g) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * dmat g *
      ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)))
    (γ : ↥(StatedSL n (ZMod 2))) :
    dmat (σ γ) = ((invT P : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) * mat γ *
      ((invT P)⁻¹ : GL (Fin n) (ZMod 2)) := by
  rw [dmat, ← map_inv, hP, dmat, inv_inv, transpose_mul, transpose_mul, transpose_transpose,
    ← Matrix.mul_assoc]
  rfl

theorem twist_of_conj {A B : Matrix (Fin n) (Fin n) (ZMod 2)} {P : GL (Fin n) (ZMod 2)}
    (h : B = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * A *
      ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) :
    (P : Matrix (Fin n) (Fin n) (ZMod 2)) * A = B * P := by
  rw [h, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.mul_one]

theorem RealM.align (hn : 3 ≤ n) (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat)
    {π₀ : ↥(StatedSL n (ZMod 2)) →* ↥L} (hπ₀ : Function.Bijective π₀) :
    RealM L W Y π₀ mat ∨ RealM L W Y π₀ dmat := by
  have hπ : Function.Bijective π := ⟨h.injective hM, h.1⟩
  set e := MulEquiv.ofBijective π hπ
  set e₀ := MulEquiv.ofBijective π₀ hπ₀
  set σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2)) := e.trans e₀.symm with hσdef
  have hσ : ∀ γ, π γ = π₀ (σ γ) := by
    intro γ
    show π γ = e₀ (e₀.symm (e γ))
    rw [MulEquiv.apply_symm_apply]
    rfl
  obtain ⟨P, hP | hP⟩ := aut_cases hn σ
  · rcases hM with rfl | rfl
    · exact Or.inl (h.twist σ hσ P fun γ => twist_of_conj (hP γ))
    · exact Or.inr (h.twist σ hσ (invT P) fun γ => twist_of_conj (dmat_of_mat_conj hP γ))
  · rcases hM with rfl | rfl
    · exact Or.inr (h.twist σ hσ (invT P) fun γ => twist_of_conj (dmat_of_dmat_conj hP γ))
    · exact Or.inl (h.twist σ hσ P fun γ => twist_of_conj (hP γ))

theorem dmat_injective : Function.Injective (dmat (n := n)) := by
  intro g h hgh
  have h1 : mat g⁻¹ = mat h⁻¹ := by
    have := congrArg Matrix.transpose hgh
    rwa [dmat, dmat, transpose_transpose, transpose_transpose] at this
  exact inv_injective (mat_injective h1)

theorem dmat_inv_eq {q : ↥(StatedSL n (ZMod 2))} {P : GL (Fin n) (ZMod 2)}
    (hq : dmat q = (P : Matrix (Fin n) (Fin n) (ZMod 2))) :
    dmat q⁻¹ = ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
  have h1 : dmat q⁻¹ * (P : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    rw [← hq, dmat_inv_mul]
  have h2 : dmat q⁻¹ = dmat q⁻¹ * ((P : Matrix (Fin n) (Fin n) (ZMod 2)) *
      ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  rw [h2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem RealM.exists_inner (h : RealM L W Y π M) (hM : M = mat ∨ M = dmat) (hn : 1 ≤ n)
    {g : MulAut V} (hgL : ∀ x ∈ L, g * x * g⁻¹ ∈ L) (hgL' : ∀ x ∈ L, g⁻¹ * x * g ∈ L)
    (hgW : g ∈ stabSub W) (hgY : g ∈ stabSub Y) :
    ∃ l ∈ L, ∀ x ∈ L, g * x * g⁻¹ = l * x * l⁻¹ := by
  have hinj := h.injective hM
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  let c : ↥L ≃* ↥L :=
    { toFun := fun x => ⟨g * x * g⁻¹, hgL x x.2⟩
      invFun := fun x => ⟨g⁻¹ * x * g, hgL' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  set e := MulEquiv.ofBijective π ⟨hinj, hπ⟩ with he
  set σ : ↥(StatedSL n (ZMod 2)) ≃* ↥(StatedSL n (ZMod 2)) := e.trans (c.trans e.symm) with hσdef
  have hσ : ∀ γ, ((π (σ γ) : ↥L) : MulAut V) = g * ((π γ : ↥L) : MulAut V) * g⁻¹ := by
    intro γ
    show ((e (e.symm (c (e γ))) : ↥L) : MulAut V) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  set gW : ↥W →* Multiplicative (Fin n → ZMod 2) := β.comp (resHom W ⟨g, hgW⟩).toMonoidHom
    with hgWdef
  have hgWapp : ∀ w : ↥W, gW w = β ⟨g w, (hgW w).2 w.2⟩ := fun w => rfl
  have hle : β.ker ≤ gW.ker := by
    intro w hw
    rw [MonoidHom.mem_ker] at hw ⊢
    rw [hgWapp]
    exact (hβk _).2 ((hgY w).2 ((hβk w).1 hw))
  set eβ := QuotientGroup.quotientKerEquivOfSurjective β hβs with heβ
  set φm : Multiplicative (Fin n → ZMod 2) →* Multiplicative (Fin n → ZMod 2) :=
    (QuotientGroup.lift β.ker gW hle).comp eβ.symm.toMonoidHom with hφm
  have hφmβ : ∀ w : ↥W, φm (β w) = gW w := by
    intro w
    have : eβ.symm (β w) = (QuotientGroup.mk w : ↥W ⧸ β.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [hφm, MonoidHom.comp_apply]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [this, QuotientGroup.lift_mk]
  set φ : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) := AddMonoidHom.toMultiplicative.symm φm with hφ
  have hφapp : ∀ w : ↥W, φ (Multiplicative.toAdd (β w)) = Multiplicative.toAdd (gW w) := by
    intro w
    rw [← hφmβ w]
    rfl
  have hint : ∀ γ x, φ (M γ *ᵥ x) = M (σ γ) *ᵥ φ x := by
    intro γ x
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd x)
    have hx : x = Multiplicative.toAdd (β w) := by rw [hw]; rfl
    have hW1 : ((π γ : ↥L) : MulAut V) (w : V) ∈ W := hLW (π γ) w w.2
    have hW2 : ((π (σ γ) : ↥L) : MulAut V) (g (w : V)) ∈ W :=
      hLW (π (σ γ)) _ ((hgW w).2 w.2)
    rw [hx, ← hβe γ w hW1, hφapp, hφapp, hgWapp, hgWapp]
    have h1 := hβe (σ γ) ⟨g w, (hgW w).2 w.2⟩ hW2
    rw [← h1]
    congr 2
    apply Subtype.ext
    show g (((π γ : ↥L) : MulAut V) (w : V)) = ((π (σ γ) : ↥L) : MulAut V) (g (w : V))
    rw [hσ]
    simp
  have hφ0 : φ ≠ 0 := by
    intro h0
    set v : Fin n → ZMod 2 := Pi.single ⟨0, by omega⟩ 1 with hv
    have hv0 : v ≠ 0 := by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp [hv] at this
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd v)
    have hgw : (g⁻¹ (w : V)) ∈ W := ((stabSub W).inv_mem hgW w).2 w.2
    have h1 := hφapp ⟨g⁻¹ w, hgw⟩
    rw [h0, AddMonoidHom.zero_apply, hgWapp] at h1
    have h2 : (⟨g (g⁻¹ (w : V)), (hgW _).2 hgw⟩ : ↥W) = w := Subtype.ext (by simp)
    rw [h2, hw] at h1
    exact hv0 h1.symm
  have hB : ∀ g' : ↥(StatedSL n (ZMod 2)), ∃ γ, M (σ γ) = mat g' := by
    intro g'
    rcases hM with rfl | rfl
    · exact ⟨σ.symm g', by rw [MulEquiv.apply_symm_apply]⟩
    · obtain ⟨δ, hδ⟩ := exists_dmat_eq (g' : GL (Fin n) (ZMod 2))
      exact ⟨σ.symm δ, by rw [MulEquiv.apply_symm_apply, hδ]; rfl⟩
  obtain ⟨P, -, hP⟩ := exists_conj_of_intertwine hφ0 hB hint
  have hconj : ∃ p : ↥(StatedSL n (ZMod 2)), ∀ γ, σ γ = p * γ * p⁻¹ := by
    have hP' : ∀ γ, M (σ γ) = (P : Matrix (Fin n) (Fin n) (ZMod 2)) * M γ *
        ((P⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) := by
      intro γ
      rw [hP γ, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    rcases hM with rfl | rfl
    · refine ⟨ofGL P, fun γ => mat_injective ?_⟩
      rw [hP' γ, mat_mul, mat_mul, mat_ofGL]
      rfl
    · obtain ⟨q, hq⟩ := exists_dmat_eq P
      refine ⟨q, fun γ => dmat_injective ?_⟩
      rw [hP' γ, dmat_mul, dmat_mul, hq, dmat_inv_eq hq]
  obtain ⟨p, hp⟩ := hconj
  refine ⟨((π p : ↥L) : MulAut V), (π p).2, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hx⟩
  have h1 := hσ γ
  rw [hp, map_mul, map_mul, hγ] at h1
  rw [← h1]
  simp

theorem RealM.complement (h : RealM L W Y π M) {X : Subgroup V} (hXW : X ≤ W) (hYX : Y ⊔ X = W)
    (hYX' : Y ⊓ X = ⊥) (hX : ∀ l : ↥L, ∀ x ∈ X, (l : MulAut V) x ∈ X) : RealM L X ⊥ π M := by
  obtain ⟨hπ, hYW, hLW, hLY, β, hβs, hβk, hβe⟩ := h
  refine ⟨hπ, bot_le, hX, fun l y hy => ?_, β.comp (Subgroup.inclusion hXW), fun y => ?_,
    fun x => ?_, fun γ x hx => ?_⟩
  · rw [Subgroup.mem_bot] at hy ⊢
    rw [hy, map_one]
  · obtain ⟨w, rfl⟩ := hβs y
    have hw : (w : V) ∈ Y ⊔ X := by rw [hYX]; exact w.2
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hw
    refine ⟨⟨b, hb⟩, ?_⟩
    have h1 : β ⟨a, hYW ha⟩ = 1 := (hβk _).2 ha
    have h2 : w = ⟨a, hYW ha⟩ * Subgroup.inclusion hXW ⟨b, hb⟩ := Subtype.ext hab.symm
    rw [MonoidHom.comp_apply, h2, map_mul, h1, one_mul]
  · rw [MonoidHom.comp_apply, hβk, Subgroup.mem_bot]
    constructor
    · intro h1
      have : (x : V) ∈ Y ⊓ X := ⟨h1, x.2⟩
      rw [hYX', Subgroup.mem_bot] at this
      exact this
    · intro h1
      show (x : V) ∈ Y
      rw [h1]
      exact Y.one_mem
  · have := hβe γ (Subgroup.inclusion hXW x) (hLW (π γ) _ (hXW x.2))
    exact this

@[expose] def secPre (W Y : Subgroup V) (X : Subgroup (Sec W Y)) : Subgroup V :=
  (X.comap (QuotientGroup.mk' (Y.subgroupOf W))).map W.subtype

theorem mem_secPre {X : Subgroup (Sec W Y)} {u : V} :
    u ∈ secPre W Y X ↔ ∃ hu : u ∈ W, (QuotientGroup.mk ⟨u, hu⟩ : Sec W Y) ∈ X := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  · rintro ⟨hu, hX⟩
    exact ⟨⟨u, hu⟩, hX, rfl⟩

theorem secPre_le (X : Subgroup (Sec W Y)) : secPre W Y X ≤ W :=
  Subgroup.map_subtype_le _

theorem le_secPre (hYW : Y ≤ W) (X : Subgroup (Sec W Y)) : Y ≤ secPre W Y X := by
  intro y hy
  refine mem_secPre.2 ⟨hYW hy, ?_⟩
  have : (QuotientGroup.mk ⟨y, hYW hy⟩ : Sec W Y) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy
  rw [this]
  exact X.one_mem

theorem secPre_mono {X X' : Subgroup (Sec W Y)} (h : X ≤ X') : secPre W Y X ≤ secPre W Y X' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem secPre_bot (hYW : Y ≤ W) : secPre W Y ⊥ = Y := by
  refine le_antisymm (fun u hu => ?_) (le_secPre hYW ⊥)
  obtain ⟨hu, hX⟩ := mem_secPre.1 hu
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hX
  exact hX

theorem secPre_top : secPre W Y ⊤ = W :=
  le_antisymm (secPre_le ⊤) fun _ hw => mem_secPre.2 ⟨hw, trivial⟩

theorem secPre_inf (X X' : Subgroup (Sec W Y)) :
    secPre W Y (X ⊓ X') = secPre W Y X ⊓ secPre W Y X' := by
  rw [secPre, secPre, secPre, Subgroup.comap_inf, Subgroup.map_inf _ _ _ W.subtype_injective]

theorem secPre_sup (X X' : Subgroup (Sec W Y)) :
    secPre W Y (X ⊔ X') = secPre W Y X ⊔ secPre W Y X' := by
  refine le_antisymm (fun u hu => ?_) (sup_le (secPre_mono le_sup_left) (secPre_mono le_sup_right))
  obtain ⟨huW, hs⟩ := mem_secPre.1 hu
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 hs
  obtain ⟨w₂, rfl⟩ := QuotientGroup.mk_surjective b
  have hw₂ : (w₂ : V) ∈ secPre W Y X' := mem_secPre.2 ⟨w₂.2, hb⟩
  have h1 : (QuotientGroup.mk (⟨u, huW⟩ * w₂⁻¹) : Sec W Y) = a := by
    rw [QuotientGroup.mk_mul, ← hab, QuotientGroup.mk_inv, mul_inv_cancel_right]
  have hw₁ : u * (w₂ : V)⁻¹ ∈ secPre W Y X := mem_secPre.2 ⟨(⟨u, huW⟩ * w₂⁻¹ : ↥W).2, by
    rw [show (⟨u * (w₂ : V)⁻¹, _⟩ : ↥W) = ⟨u, huW⟩ * w₂⁻¹ from rfl, h1]
    exact ha⟩
  have := Subgroup.mul_mem_sup hw₁ hw₂
  simpa using this

theorem RealM.ofSec (hLW : L ≤ stabSub W) (hLY : L ≤ stabSub Y)
    (hfaith : L ⊓ centSec W Y = ⊥) {X Z : Subgroup (Sec W Y)}
    {π' : ↥(StatedSL n (ZMod 2)) →* ↥(autSec L W Y)} (h : RealM (autSec L W Y) X Z π' M) :
    RealM L (secPre W Y X) (secPre W Y Z)
      ((B5.secEquiv L hLW hLY hfaith).symm.toMonoidHom.comp π') M := by
  obtain ⟨hπ, hZX, hLX, hLZ, β, hβs, hβk, hβe⟩ := h
  set ε := B5.secEquiv L hLW hLY hfaith with hε
  have hsec : ∀ (x : ↥(autSec L W Y)) (w : ↥W),
      ((x : MulAut (Sec W Y))) (QuotientGroup.mk w) =
        QuotientGroup.mk ⟨((ε.symm x : ↥L) : MulAut V) (w : V), (hLW (ε.symm x).2 w).2 w.2⟩ := by
    intro x w
    rw [B5.secHom_symm hLW hLY hfaith x, B5.secHom_mk]
  have hinv : ∀ (x : ↥(autSec L W Y)), ∀ (X₀ : Subgroup (Sec W Y)),
      (∀ l : ↥(autSec L W Y), ∀ s ∈ X₀, (l : MulAut (Sec W Y)) s ∈ X₀) →
      ∀ u ∈ secPre W Y X₀, ((ε.symm x : ↥L) : MulAut V) u ∈ secPre W Y X₀ := by
    intro x X₀ hX₀ u hu
    obtain ⟨hu, hs⟩ := mem_secPre.1 hu
    refine mem_secPre.2 ⟨(hLW (ε.symm x).2 u).2 hu, ?_⟩
    have := hX₀ x _ hs
    rw [hsec x ⟨u, hu⟩] at this
    exact this
  let q : ↥(secPre W Y X) →* ↥X :=
    { toFun := fun u => ⟨QuotientGroup.mk ⟨(u : V), secPre_le X u.2⟩,
        (mem_secPre.1 u.2).2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hq : ∀ u : ↥(secPre W Y X), ((q u : ↥X) : Sec W Y) =
      QuotientGroup.mk ⟨(u : V), secPre_le X u.2⟩ := fun _ => rfl
  refine ⟨ε.symm.surjective.comp hπ, secPre_mono hZX, ?_, ?_, β.comp q, ?_, fun u => ?_,
    fun γ u hu => ?_⟩
  · intro l u hu
    have := hinv (ε l) X (fun l s hs => hLX l s hs) u hu
    rwa [MulEquiv.symm_apply_apply] at this
  · intro l u hu
    have := hinv (ε l) Z (fun l s hs => hLZ l s hs) u hu
    rwa [MulEquiv.symm_apply_apply] at this
  · intro y
    obtain ⟨s, rfl⟩ := hβs y
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (s : Sec W Y)
    have hwX : (w : V) ∈ secPre W Y X := mem_secPre.2 ⟨w.2, by rw [hw]; exact s.2⟩
    refine ⟨⟨w, hwX⟩, ?_⟩
    rw [MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    rw [hq, ← hw]
  · rw [MonoidHom.comp_apply, hβk, hq]
    constructor
    · intro h1
      exact mem_secPre.2 ⟨secPre_le X u.2, h1⟩
    · intro h1
      obtain ⟨_, h2⟩ := mem_secPre.1 h1
      exact h2
  · have hu' : ((π' γ : ↥(autSec L W Y)) : MulAut (Sec W Y)) ((q u : ↥X) : Sec W Y) ∈ X :=
      hLX (π' γ) _ (q u).2
    have h1 := hβe γ (q u) hu'
    have h2 : q ⟨_, hu⟩ = ⟨((π' γ : ↥(autSec L W Y)) : MulAut (Sec W Y)) ((q u : ↥X) : Sec W Y),
        hu'⟩ := by
      apply Subtype.ext
      show (QuotientGroup.mk ⟨_, _⟩ : Sec W Y) = ((π' γ : ↥(autSec L W Y)) : MulAut (Sec W Y))
        (QuotientGroup.mk ⟨(u : V), secPre_le X u.2⟩)
      rw [hsec]
      rfl
    show Multiplicative.toAdd (β (q ⟨_, hu⟩)) = M γ *ᵥ Multiplicative.toAdd (β (q u))
    rw [h2, h1]

theorem realM_of_binaryNaturalSL {H : Subgroup (MulAut V)} {U Z : Subgroup V} {d : ℕ}
    (h : BinaryNaturalSL H U Z d 1) : ∃ π : ↥(StatedSL d (ZMod 2)) →* ↥H, RealM H U Z π mat := by
  classical
  obtain ⟨K, hKf, hKfin, hK, π₁, hπ₁⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card (ZMod 2) = Fintype.card K := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one]
  set φ : ZMod 2 ≃+* K := FiniteField.ringEquivOfCardEq hcard with hφ
  have hφφ : ∀ x : K, φ (φ.symm x) = x := φ.apply_symm_apply
  have hφφ' : ∀ x : ZMod 2, φ.symm (φ x) = x := φ.symm_apply_apply
  let ιGL : GL (Fin d) (ZMod 2) →* GL (Fin d) K := Units.map
    (φ.toRingHom.mapMatrix : Matrix (Fin d) (Fin d) (ZMod 2) →+* Matrix (Fin d) (Fin d) K)
  have hιGL : ∀ A : GL (Fin d) (ZMod 2), ((ιGL A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      (A : Matrix (Fin d) (Fin d) (ZMod 2)).map φ := fun A => rfl
  have hmem : ∀ γ : ↥(StatedSL d (ZMod 2)), ιGL (γ : GL (Fin d) (ZMod 2)) ∈ StatedSL d K := by
    intro γ
    apply Subgroup.subset_closure
    show ((ιGL (γ : GL (Fin d) (ZMod 2)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).det = 1
    rw [hιGL]
    have h1 : ((γ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2)).det = 1 := by
      have hu : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1 := by decide
      rw [← Matrix.GeneralLinearGroup.val_det_apply]
      exact hu _
    have h2 := RingHom.map_det φ.toRingHom
      ((γ : GL (Fin d) (ZMod 2)) : Matrix (Fin d) (Fin d) (ZMod 2))
    rw [h1, map_one] at h2
    exact h2.symm
  let ι : ↥(StatedSL d (ZMod 2)) →* ↥(StatedSL d K) :=
    (ιGL.comp (StatedSL d (ZMod 2)).subtype).codRestrict _ hmem
  have hι : ∀ γ : ↥(StatedSL d (ZMod 2)),
      (((ι γ : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = (mat γ).map φ :=
    fun γ => rfl
  have hιs : Function.Surjective ι := by
    intro γ'
    let A : GL (Fin d) (ZMod 2) := Units.map
      (φ.symm.toRingHom.mapMatrix : Matrix (Fin d) (Fin d) K →+* Matrix (Fin d) (Fin d) (ZMod 2))
      (γ' : GL (Fin d) K)
    refine ⟨ofGL A, Subtype.ext (Units.ext ?_)⟩
    show ((A : Matrix (Fin d) (Fin d) (ZMod 2))).map φ = _
    ext i j
    show φ (φ.symm _) = _
    rw [hφφ]
  obtain ⟨β₀, hβ₀s, hβ₀k, hβ₀e⟩ :=
    FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL d K)) rfl rfl hπ₁
  let β₁ : ↥U →* Multiplicative (Fin d → K) := β₀
  have hβ₁s : Function.Surjective β₁ := hβ₀s
  have hβ₁k : ∀ u : ↥U, β₁ u = 1 ↔ (u : V) ∈ Z := hβ₀k
  have hβ₁e : ∀ (γ : ↥(StatedSL d K)) (u : ↥U) (hu : ((π₁ γ : ↥H) : MulAut V) (u : V) ∈ U),
      Multiplicative.toAdd (β₁ ⟨((π₁ γ : ↥H) : MulAut V) (u : V), hu⟩) =
        ((γ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ Multiplicative.toAdd (β₁ u) :=
    fun γ u hu => congrArg Multiplicative.toAdd (hβ₀e γ u hu)
  obtain ⟨hπs, hZU, -, hHU, hHZ, -⟩ := hπ₁
  let c : Multiplicative (Fin d → K) →* Multiplicative (Fin d → ZMod 2) :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft φ.symm.toAddEquiv.toAddMonoidHom (Fin d))
  have hc : ∀ x, Multiplicative.toAdd (c x) = φ.symm ∘ Multiplicative.toAdd x := fun _ => rfl
  refine ⟨π₁.comp ι, hπs.comp hιs, hZU, hHU, hHZ, c.comp β₁, fun y => ?_, fun u => ?_,
    fun γ u hu => ?_⟩
  · obtain ⟨u, hu⟩ := hβ₁s (Multiplicative.ofAdd (φ ∘ Multiplicative.toAdd y))
    refine ⟨u, Multiplicative.toAdd.injective ?_⟩
    show Multiplicative.toAdd (c (β₁ u)) = _
    rw [hc, hu, toAdd_ofAdd]
    funext i
    exact hφφ' _
  · show c (β₁ u) = 1 ↔ _
    rw [← hβ₁k u]
    constructor
    · intro h1
      apply Multiplicative.toAdd.injective
      funext i
      have := congrFun (congrArg Multiplicative.toAdd h1) i
      rw [hc, Function.comp_apply] at this
      have h2 := congrArg φ this
      rw [hφφ] at h2
      rw [h2]
      exact map_zero φ
    · intro h1
      rw [h1, map_one]
  · have h1 := hβ₁e (ι γ) u hu
    show Multiplicative.toAdd (c (β₁ ⟨((π₁ (ι γ) : ↥H) : MulAut V) (u : V), hu⟩)) =
      mat γ *ᵥ Multiplicative.toAdd (c (β₁ u))
    rw [hc, hc, h1]
    funext i
    show φ.symm (((((ι γ : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
      Multiplicative.toAdd (β₁ u)) i) = _
    have h2 := RingHom.map_mulVec φ.symm.toRingHom
      (((ι γ : ↥(StatedSL d K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      (Multiplicative.toAdd (β₁ u)) i
    rw [show φ.symm.toRingHom = (φ.symm : K →+* ZMod 2) from rfl] at h2
    simp only [RingEquiv.coe_toRingHom] at h2
    rw [h2, hι]
    congr 2
    ext a b
    exact hφφ' _

end CFSG.Quasithin.B5.Ln
