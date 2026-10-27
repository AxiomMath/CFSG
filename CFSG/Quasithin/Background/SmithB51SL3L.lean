module

public import CFSG.Quasithin.Background.SmithB51SL3K

public section

namespace CFSG.Quasithin

namespace B5

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section Irr

variable {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {K : Type} [Field K]

theorem NatSec.eq_bot_or_eq {W : Subgroup V} (c : NatSec L W ⊥ K) (hLW : L ≤ stabSub W)
    {S : Subgroup V} (hSW : S ≤ W) (hLS : ∀ l ∈ L, ∀ x ∈ S, l x ∈ S) : S = ⊥ ∨ S = W := by
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  obtain ⟨⟨x, hxS⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hS
  set M := (S.subgroupOf W).map c.f with hM
  set T : AddSubgroup (Fin 3 → K) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ M}
      add_mem' := fun {a b} (ha : Multiplicative.ofAdd a ∈ M)
        (hb : Multiplicative.ofAdd b ∈ M) => M.mul_mem ha hb
      zero_mem' := (show Multiplicative.ofAdd (0 : Fin 3 → K) ∈ M from M.one_mem)
      neg_mem' := fun {a} (ha : Multiplicative.ofAdd a ∈ M) => M.inv_mem ha } with hT
  have hTinv : ∀ g : ↥(StatedSL 3 K), ∀ v ∈ T, slAct g v ∈ T := by
    rintro g v ⟨y, hy, hyv⟩
    have hyS : (y : V) ∈ S := Subgroup.mem_subgroupOf.1 hy
    have hgy : ((c.π g : ↥L) : MulAut V) y ∈ W := ((hLW (c.π g).2) y).2 y.2
    refine ⟨⟨_, hgy⟩, Subgroup.mem_subgroupOf.2 (hLS _ (c.π g).2 _ hyS), ?_⟩
    rw [c.hfe g y hgy, hyv]
    rfl
  have hxW : x ∈ W := hSW hxS
  have hxT : Multiplicative.toAdd (c.f ⟨x, hxW⟩) ∈ T :=
    ⟨⟨x, hxW⟩, Subgroup.mem_subgroupOf.2 hxS, rfl⟩
  have hxne : Multiplicative.toAdd (c.f ⟨x, hxW⟩) ≠ 0 := by
    intro h0
    apply hx1
    have h1 : c.f ⟨x, hxW⟩ = 1 := Multiplicative.toAdd.injective h0
    exact Subtype.ext ((c.hfk _).1 h1)
  have htop := eq_top_of_slAct_mem hTinv hxT hxne
  refine le_antisymm hSW fun w hw => ?_
  have hwT : Multiplicative.toAdd (c.f ⟨w, hw⟩) ∈ T := by rw [htop]; trivial
  obtain ⟨y, hy, hyw⟩ := hwT
  have h1 := c.f_injective hyw
  have h2 : (y : V) = w := congrArg Subtype.val h1
  rw [← h2]
  exact Subgroup.mem_subgroupOf.1 hy

theorem NatSec.card_eq [Finite K] {W : Subgroup V} (c : NatSec L W ⊥ K) :
    Nat.card W = Nat.card K ^ 3 := by
  rw [Nat.card_congr (MulEquiv.ofBijective c.f ⟨c.f_injective, c.hfs⟩).toEquiv]
  rw [show Nat.card (Multiplicative (Fin 3 → K)) = Nat.card (Fin 3 → K) from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

end Irr

section Graphs

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)} (s : SL3Split G L)

@[expose] def smulMul {K : Type} [Field K] (μ : K) :
    Multiplicative (Fin 3 → K) →* Multiplicative (Fin 3 → K) where
  toFun x := Multiplicative.ofAdd (μ • Multiplicative.toAdd x)
  map_one' := by simp
  map_mul' x y := by simp [smul_add]

theorem toAdd_smulMul {K : Type} [Field K] (μ : K) (x : Multiplicative (Fin 3 → K)) :
    Multiplicative.toAdd (smulMul μ x) = μ • Multiplicative.toAdd x := rfl

@[expose] noncomputable def SL3Split.ι₁ : Multiplicative (Fin 3 → s.K) ≃* ↥s.I :=
  (MulEquiv.ofBijective s.e₁.f ⟨s.e₁.f_injective, s.e₁.hfs⟩).symm

theorem SL3Split.f_ι₁ (x : Multiplicative (Fin 3 → s.K)) : s.e₁.f (s.ι₁ x) = x :=
  (MulEquiv.ofBijective s.e₁.f ⟨s.e₁.f_injective, s.e₁.hfs⟩).apply_symm_apply x

theorem SL3Split.act_ι₁ (γ : ↥(StatedSL 3 s.K)) (x : Multiplicative (Fin 3 → s.K)) :
    ((s.e₁.π γ : ↥L) : MulAut V) (s.ι₁ x) = s.ι₁ (natAct (StatedSL 3 s.K) γ x) := by
  have hmem : ((s.e₁.π γ : ↥L) : MulAut V) (s.ι₁ x) ∈ s.I :=
    ((s.hLI (s.e₁.π γ).2) _).2 (s.ι₁ x).2
  have h1 := s.e₁.hfe γ (s.ι₁ x) hmem
  rw [s.f_ι₁, ← s.f_ι₁ (natAct _ γ x)] at h1
  exact congrArg Subtype.val (s.e₁.f_injective h1)

@[expose] noncomputable def SL3Split.graphHom (μ : s.K) : Multiplicative (Fin 3 → s.K) →* V :=
  (commV L).subtype.comp s.σ * s.I.subtype.comp (s.ι₁.toMonoidHom.comp (smulMul μ))

theorem SL3Split.graphHom_apply (μ : s.K) (x : Multiplicative (Fin 3 → s.K)) :
    s.graphHom μ x = (s.σ x : V) * (s.ι₁ (smulMul μ x) : V) := rfl

theorem SL3Split.graphHom_mem (μ : s.K) (x : Multiplicative (Fin 3 → s.K)) :
    s.graphHom μ x ∈ commV L :=
  (commV L).mul_mem (s.σ x).2 (s.hIU (s.ι₁ _).2)

theorem SL3Split.f_graphHom (μ : s.K) (x : Multiplicative (Fin 3 → s.K)) :
    s.e₂.f ⟨s.graphHom μ x, s.graphHom_mem μ x⟩ = x := by
  have h1 : s.e₂.f ⟨_, s.hIU (s.ι₁ (smulMul μ x)).2⟩ = 1 := (s.e₂.hfk _).2 (s.ι₁ _).2
  have e1 : (⟨s.graphHom μ x, s.graphHom_mem μ x⟩ : ↥(commV L)) =
      s.σ x * ⟨_, s.hIU (s.ι₁ (smulMul μ x)).2⟩ := rfl
  rw [e1, map_mul, h1, mul_one, s.hσf]

@[expose] noncomputable def SL3Split.D (μ : s.K) : Subgroup V := (s.graphHom μ).range

theorem SL3Split.D_le (μ : s.K) : s.D μ ≤ commV L := by
  rintro _ ⟨x, rfl⟩
  exact s.graphHom_mem μ x

theorem SL3Split.graphHom_injective (μ : s.K) : Function.Injective (s.graphHom μ) := by
  intro x y hxy
  have e : (⟨s.graphHom μ x, s.graphHom_mem μ x⟩ : ↥(commV L)) =
      ⟨s.graphHom μ y, s.graphHom_mem μ y⟩ := Subtype.ext hxy
  have h1 := congrArg s.e₂.f e
  rwa [s.f_graphHom, s.f_graphHom] at h1

theorem SL3Split.card_D (μ : s.K) : Nat.card (s.D μ) = Nat.card s.K ^ 3 := by
  rw [SL3Split.D, ← Nat.card_congr (MonoidHom.ofInjective (s.graphHom_injective μ)).toEquiv,
    show Nat.card (Multiplicative (Fin 3 → s.K)) = Nat.card (Fin 3 → s.K) from rfl, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]

theorem SL3Split.act_graphHom (μ : s.K) (γ : ↥(StatedSL 3 s.K))
    (x : Multiplicative (Fin 3 → s.K)) :
    ((s.e₁.π γ : ↥L) : MulAut V) (s.graphHom μ x) =
      s.graphHom μ (natAct (StatedSL 3 s.K) γ x) := by
  rw [s.graphHom_apply, s.graphHom_apply, map_mul, s.hσe, s.act_ι₁]
  congr 3
  apply Multiplicative.toAdd.injective
  show slAct γ (μ • Multiplicative.toAdd x) = μ • slAct γ (Multiplicative.toAdd x)
  exact slAct_smul γ μ _

theorem SL3Split.hLD (μ : s.K) : L ≤ stabSub (s.D μ) := by
  have key : ∀ l ∈ L, ∀ v ∈ s.D μ, l v ∈ s.D μ := by
    rintro l hl _ ⟨x, rfl⟩
    obtain ⟨γ, hγ⟩ := s.e₁.hπ.2 ⟨l, hl⟩
    have := s.act_graphHom μ γ x
    rw [hγ] at this
    exact ⟨_, this.symm⟩
  intro l hl
  exact mem_stabSub_of_inv (key l hl) (key l⁻¹ (L.inv_mem hl))

theorem SL3Split.D_ne_I (μ : s.K) : s.D μ ≠ s.I := by
  intro h
  have hmem : s.graphHom μ (Multiplicative.ofAdd (Pi.single 0 1)) ∈ s.I := by
    rw [← h]
    exact ⟨_, rfl⟩
  have h1 := (s.e₂.hfk ⟨_, s.graphHom_mem μ (Multiplicative.ofAdd (Pi.single 0 1))⟩).2 hmem
  rw [s.f_graphHom] at h1
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) 0
  simp at h2

theorem SL3Split.D_injective : Function.Injective s.D := by
  intro μ μ' h
  have hmem : s.graphHom μ (Multiplicative.ofAdd (Pi.single 0 1)) ∈ s.D μ' := by
    rw [← h]
    exact ⟨_, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  have e : (⟨s.graphHom μ' y, s.graphHom_mem μ' y⟩ : ↥(commV L)) =
      ⟨_, s.graphHom_mem μ (Multiplicative.ofAdd (Pi.single 0 1))⟩ := Subtype.ext hy
  have h1 := congrArg s.e₂.f e
  rw [s.f_graphHom, s.f_graphHom] at h1
  subst h1
  rw [s.graphHom_apply, s.graphHom_apply] at hy
  have h2 := mul_left_cancel hy
  have h3 := congrArg s.e₁.f (Subtype.ext h2 : s.ι₁ _ = s.ι₁ _)
  rw [s.f_ι₁, s.f_ι₁] at h3
  have h4 := congrFun (congrArg Multiplicative.toAdd h3) 0
  have h5 : μ' = μ := by simpa [toAdd_smulMul] using h4
  exact h5.symm

end Graphs

section Classify

variable {V : Type} [CommGroup V] {G L : Subgroup (MulAut V)} (s : SL3Split G L)

theorem SL3Split.card_I : Nat.card s.I = Nat.card s.K ^ 3 := s.e₁.card_eq

theorem SL3Split.card_U : Nat.card (commV L) = Nat.card s.K ^ 6 := by
  have h := card_sup_mul_card_inf s.I' s.I
  rw [s.sup_eq, s.inf_eq_bot, Subgroup.card_bot, mul_one, s.e₁'.card_eq, s.card_I] at h
  rw [h]
  ring

theorem SL3Split.eq_I_or_inf [Finite V] {J : Subgroup V} (hLJ : L ≤ stabSub J)
    (hJ : Nat.card J = Nat.card s.K ^ 3) : J = s.I ∨ J ⊓ s.I = ⊥ := by
  rcases s.e₁.eq_bot_or_eq s.hLI (inf_le_right : J ⊓ s.I ≤ s.I)
      (fun l hl x hx => ⟨((hLJ hl) x).2 hx.1, ((s.hLI hl) x).2 hx.2⟩) with hbot | htop
  · exact Or.inr hbot
  · left
    exact (Subgroup.eq_of_le_of_card_ge (inf_eq_right.1 htop) (by rw [hJ, s.card_I])).symm

theorem SL3Split.sup_eq_of_inf [Finite V] {J : Subgroup V} (hJU : J ≤ commV L)
    (hJ : Nat.card J = Nat.card s.K ^ 3) (hbot : J ⊓ s.I = ⊥) : J ⊔ s.I = commV L := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le hJU s.hIU) ?_
  have h := card_sup_mul_card_inf J s.I
  rw [hbot, Subgroup.card_bot, mul_one, hJ, s.card_I] at h
  rw [s.card_U, h]
  ring_nf
  exact le_rfl

theorem SL3Split.exists_natSec [Finite V] {J : Subgroup V} (hJU : J ≤ commV L) (hLJ : L ≤ stabSub J)
    (hJ : Nat.card J = Nat.card s.K ^ 3) : ∃ c : NatSec L J ⊥ s.K, c.π = s.e₁.π := by
  rcases s.eq_I_or_inf hLJ hJ with rfl | hbot
  · exact ⟨s.e₁, rfl⟩
  · refine ⟨(s.e₂.restrict hJU (s.sup_eq_of_inf hJU hJ hbot)).ofEq hbot, ?_⟩
    rw [← s.hπ]
    exact MonoidHom.ext fun γ => NatSec.ofEq_π _ _ γ

theorem SL3Split.eq_D [Finite V] {J : Subgroup V} (hJU : J ≤ commV L) (hLJ : L ≤ stabSub J)
    (hJ : Nat.card J = Nat.card s.K ^ 3) (hbot : J ⊓ s.I = ⊥) : ∃ μ, J = s.D μ := by
  classical
  set cJ := (s.e₂.restrict hJU (s.sup_eq_of_inf hJU hJ hbot)).ofEq hbot with hcJ
  have hcJπ : cJ.π = s.e₁.π := by
    rw [← s.hπ]
    exact MonoidHom.ext fun γ => NatSec.ofEq_π _ _ γ
  have hcJf : ∀ j : ↥J, cJ.f j = s.e₂.f ⟨j, hJU j.2⟩ := fun j => NatSec.ofEq_f _ _ j
  set j := (MulEquiv.ofBijective cJ.f ⟨cJ.f_injective, cJ.hfs⟩).symm with hj
  have hjf : ∀ x, cJ.f (j x) = x := fun x =>
    (MulEquiv.ofBijective cJ.f ⟨cJ.f_injective, cJ.hfs⟩).apply_symm_apply x
  have hτI : ∀ x, ((s.σ x : ↥(commV L)) : V)⁻¹ * (j x : V) ∈ s.I := by
    intro x
    have hmem : ((s.σ x : ↥(commV L)) : V)⁻¹ * (j x : V) ∈ commV L :=
      (commV L).mul_mem ((commV L).inv_mem (s.σ x).2) (hJU (j x).2)
    rw [← s.e₂.hfk ⟨_, hmem⟩]
    have e1 : (⟨_, hmem⟩ : ↥(commV L)) = (s.σ x)⁻¹ * ⟨(j x : V), hJU (j x).2⟩ := rfl
    rw [e1, map_mul, map_inv, s.hσf, ← hcJf, hjf, inv_mul_cancel]
  set τ : (Fin 3 → s.K) →+ (Fin 3 → s.K) :=
    { toFun := fun v => Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd v)⟩)
      map_zero' := by
        show Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd 0)⟩) = 0
        have e1 : (⟨_, hτI (Multiplicative.ofAdd 0)⟩ : ↥s.I) = 1 := by
          apply Subtype.ext
          show ((s.σ 1 : ↥(commV L)) : V)⁻¹ * (j 1 : V) = ((1 : ↥s.I) : V)
          rw [map_one, map_one, Subgroup.coe_one, Subgroup.coe_one, Subgroup.coe_one, inv_one,
            mul_one]
        rw [e1, map_one, toAdd_one]
      map_add' := fun v w => by
        show Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd (v + w))⟩) =
          Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd v)⟩) +
            Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd w)⟩)
        have e1 : (⟨_, hτI (Multiplicative.ofAdd (v + w))⟩ : ↥s.I) =
            ⟨_, hτI (Multiplicative.ofAdd v)⟩ * ⟨_, hτI (Multiplicative.ofAdd w)⟩ := by
          apply Subtype.ext
          rw [Subgroup.coe_mul]
          show ((s.σ (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : ↥(commV L)) : V)⁻¹ *
              (j (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : V) = _
          rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, mul_inv, mul_mul_mul_comm]
        rw [e1, map_mul, toAdd_mul] } with hτ
  have hτcomm : ∀ γ ∈ StatedSL 3 s.K, ∀ v, τ ((γ : Matrix (Fin 3) (Fin 3) s.K) *ᵥ v) =
      (γ : Matrix (Fin 3) (Fin 3) s.K) *ᵥ τ v := by
    intro γ hγ v
    set g : ↥(StatedSL 3 s.K) := ⟨γ, hγ⟩ with hg
    have hj_e : ∀ x, ((s.e₁.π g : ↥L) : MulAut V) (j x) = j (natAct (StatedSL 3 s.K) g x) := by
      intro x
      have hmem : ((cJ.π g : ↥L) : MulAut V) (j x) ∈ J := ((hLJ (cJ.π g).2) _).2 (j x).2
      have h1 := cJ.hfe g (j x) hmem
      rw [hjf, ← hjf (natAct _ g x)] at h1
      have h2 := congrArg Subtype.val (cJ.f_injective h1)
      rw [← hcJπ]
      exact h2
    have hmemI : ((s.e₁.π g : ↥L) : MulAut V)
        (((s.σ (Multiplicative.ofAdd v) : ↥(commV L)) : V)⁻¹ * (j (Multiplicative.ofAdd v) : V))
        ∈ s.I := ((s.hLI (s.e₁.π g).2) _).2 (hτI _)
    have h1 := s.e₁.hfe g ⟨_, hτI (Multiplicative.ofAdd v)⟩ hmemI
    have e1 : (⟨_, hmemI⟩ : ↥s.I) = ⟨_, hτI (Multiplicative.ofAdd (slAct g v))⟩ := by
      apply Subtype.ext
      show ((s.e₁.π g : ↥L) : MulAut V)
          (((s.σ (Multiplicative.ofAdd v) : ↥(commV L)) : V)⁻¹ *
            (j (Multiplicative.ofAdd v) : V)) = _
      rw [map_mul, map_inv, s.hσe, hj_e]
      rfl
    rw [e1] at h1
    show Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd (slAct g v))⟩) =
      slAct g (Multiplicative.toAdd (s.e₁.f ⟨_, hτI (Multiplicative.ofAdd v)⟩))
    rw [h1]
    rfl
  obtain ⟨μ, hμ⟩ := H.hasScalarCommutant_statedSL (d := 3) (K := s.K) (by norm_num) τ hτcomm
  refine ⟨μ, Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [s.card_D, hJ])⟩
  set y := cJ.f ⟨x, hx⟩ with hy
  have hjy : j y = ⟨x, hx⟩ :=
    (MulEquiv.ofBijective cJ.f ⟨cJ.f_injective, cJ.hfs⟩).symm_apply_apply _
  have h1 : (⟨_, hτI y⟩ : ↥s.I) = s.ι₁ (smulMul μ y) := by
    apply s.e₁.f_injective
    rw [s.f_ι₁]
    apply Multiplicative.toAdd.injective
    have := hμ (Multiplicative.toAdd y)
    exact this
  refine ⟨y, ?_⟩
  rw [s.graphHom_apply, ← h1]
  show ((s.σ y : ↥(commV L)) : V) * (((s.σ y : ↥(commV L)) : V)⁻¹ * (j y : V)) = x
  rw [hjy]
  group

end Classify

section Fixed

variable {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)} (s : SL3Split G L)

theorem SL3Split.exists_fixed_natural {B : Subgroup (MulAut V)} (hB2 : IsPGroup 2 B)
    (hBL : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L) :
    ∃ J : Subgroup V, J ≤ commV L ∧ L ≤ stabSub J ∧ B ≤ stabSub J ∧
      ∃ c : NatSec L J ⊥ s.K, c.π = s.e₁.π := by
  classical
  have hq : 2 ∣ Nat.card s.K := by
    rw [s.hK]
    rcases Nat.eq_zero_or_pos s.n with h0 | h0
    · have : (1 : ℕ) < Nat.card s.K := Finite.one_lt_card
      rw [s.hK, h0] at this
      norm_num at this
    · exact dvd_pow_self 2 h0.ne'
  set S : Set (Subgroup V) :=
    {J | J ≤ commV L ∧ L ≤ stabSub J ∧ Nat.card J = Nat.card s.K ^ 3} with hS
  have hBU : B ≤ stabSub (commV L) := le_stabSub_commV hBL (fun _ hb => B.inv_mem hb)
  have hmap : ∀ b ∈ B, ∀ J ∈ S, J.map (b : MulAut V).toMonoidHom ∈ S := by
    rintro b hb J ⟨hJU, hLJ, hJ⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ((hBU hb) x).2 (hJU hx)
    · have key : ∀ l ∈ L, ∀ y ∈ J.map (b : MulAut V).toMonoidHom,
          l y ∈ J.map (b : MulAut V).toMonoidHom := by
        rintro l hl _ ⟨x, hx, rfl⟩
        have hl' : b⁻¹ * l * b⁻¹⁻¹ ∈ L := hBL _ (B.inv_mem hb) l hl
        rw [inv_inv] at hl'
        refine ⟨(b⁻¹ * l * b) x, ((hLJ hl') x).2 hx, ?_⟩
        show b ((b⁻¹ * l * b) x) = l (b x)
        rw [← MulAut.mul_apply, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul,
          MulAut.mul_apply]
      intro l hl
      exact mem_stabSub_of_inv (key l hl) (key l⁻¹ (L.inv_mem hl))
    · rw [Subgroup.card_map_of_injective (b : MulAut V).injective, hJ]
  have hSeq : S = insert s.I (Set.range s.D) := by
    ext J
    constructor
    · rintro ⟨hJU, hLJ, hJ⟩
      rcases s.eq_I_or_inf hLJ hJ with rfl | hbot
      · exact Or.inl rfl
      · obtain ⟨μ, rfl⟩ := s.eq_D hJU hLJ hJ hbot
        exact Or.inr ⟨μ, rfl⟩
    · rintro (rfl | ⟨μ, rfl⟩)
      · exact ⟨s.hIU, s.hLI, s.card_I⟩
      · exact ⟨s.D_le μ, s.hLD μ, s.card_D μ⟩
  have hnot : s.I ∉ Set.range s.D := by
    rintro ⟨μ, hμ⟩
    exact s.D_ne_I μ hμ
  have hcard : Nat.card ↥S = Nat.card s.K + 1 := by
    rw [Nat.card_coe_set_eq, hSeq, Set.ncard_insert_of_notMem hnot,
      Set.ncard_range_of_injective s.D_injective]
  have hodd : ¬ 2 ∣ Nat.card ↥S := by
    rw [hcard]
    omega
  let _ : MulAction ↥B ↥S :=
    { smul := fun b J => ⟨J.1.map (b : MulAut V).toMonoidHom, hmap b b.2 J.1 J.2⟩
      one_smul := fun J => Subtype.ext (by
        show J.1.map ((1 : MulAut V)).toMonoidHom = J.1
        exact Subgroup.map_id J.1)
      mul_smul := fun b b' J => Subtype.ext (by
        show J.1.map (((b : MulAut V) * b')).toMonoidHom =
          (J.1.map (b' : MulAut V).toMonoidHom).map (b : MulAut V).toMonoidHom
        rw [Subgroup.map_map]
        rfl) }
  obtain ⟨⟨J, hJ⟩, hfix⟩ := hB2.nonempty_fixed_point_of_prime_not_dvd_card ↥S hodd
  have hBJ : ∀ b ∈ B, J.map (b : MulAut V).toMonoidHom = J := by
    intro b hb
    have := congrArg Subtype.val (hfix ⟨b, hb⟩)
    exact this
  refine ⟨J, hJ.1, hJ.2.1, fun b hb => ?_, s.exists_natSec hJ.1 hJ.2.1 hJ.2.2⟩
  have h1 := hBJ b hb
  have h2 := hBJ b⁻¹ (B.inv_mem hb)
  refine mem_stabSub_of_inv (fun x hx => ?_) (fun x hx => ?_)
  · rw [← h1]
    exact ⟨x, hx, rfl⟩
  · rw [← h2]
    exact ⟨x, hx, rfl⟩

end Fixed

end B5

end CFSG.Quasithin
