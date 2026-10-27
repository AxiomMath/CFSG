module

public import CFSG.Quasithin.Background.RonanG25Odd
public import CFSG.Quasithin.Background.RonanG25Small
public import CFSG.Quasithin.Background.RonanG25Calc
public import CFSG.Quasithin.Background.G2SL2
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.RonanG25

section TailHelpers

variable {G : Type} [Group G] {F : Type} [Field F] {X Q : Subgroup G}

@[expose] noncomputable def detSub (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) :
    Subgroup ↥X :=
  MonoidHom.ker ((Matrix.GeneralLinearGroup.det :
    Matrix.GeneralLinearGroup (Fin 2) F →* Fˣ).comp π)

@[expose] noncomputable def tailK (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) :
    Subgroup G :=
  (detSub π).map X.subtype

theorem mem_tailK_iff (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) (g : G) :
    g ∈ tailK π ↔ ∃ h : g ∈ X, Matrix.GeneralLinearGroup.det (π ⟨g, h⟩) = 1 := by
  constructor
  · intro hg
    unfold tailK at hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨x.2, MonoidHom.mem_ker.mp hx⟩
  · rintro ⟨h, hd⟩
    unfold tailK
    exact Subgroup.mem_map.mpr ⟨⟨g, h⟩, MonoidHom.mem_ker.mpr hd, rfl⟩

theorem tailK_le (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) : tailK π ≤ X := by
  intro g hg
  obtain ⟨h, -⟩ := (mem_tailK_iff π g).mp hg
  exact h

@[expose] noncomputable def tailX (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (k : ↥(tailK π)) : ↥X :=
  ⟨k.1, tailK_le π k.2⟩

theorem det_tailX (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) (k : ↥(tailK π)) :
    Matrix.GeneralLinearGroup.det (π (tailX π k)) = 1 := by
  obtain ⟨_, hd⟩ := (mem_tailK_iff π k.1).mp k.2
  exact hd

@[expose] noncomputable def tailMat (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (k : ↥(tailK π)) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨((π (tailX π k) : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F), by
    have h := congrArg Units.val (det_tailX π k)
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at h
    exact h⟩

@[expose] noncomputable def tailPsi (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) :
    ↥(tailK π) →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := tailMat π
  map_one' := by
    apply Subtype.ext
    have h1 : tailX π 1 = 1 := Subtype.ext rfl
    simp only [tailMat, h1, map_one, Units.val_one, Matrix.SpecialLinearGroup.coe_one]
  map_mul' k l := by
    apply Subtype.ext
    have h1 : tailX π (k * l) = tailX π k * tailX π l := Subtype.ext rfl
    rw [Matrix.SpecialLinearGroup.coe_mul]
    show ((π (tailX π (k * l)) : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((π (tailX π k) : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((π (tailX π l) : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    rw [h1, map_mul, Units.val_mul]

theorem tailPsi_apply (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) (k : ↥(tailK π)) :
    ((tailPsi π k : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((π (tailX π k) : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
  rfl

theorem tailPsi_eq_one_iff (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ Q) (k : ↥(tailK π)) :
    tailPsi π k = 1 ↔ (k : G) ∈ Q := by
  have key : tailPsi π k = 1 ↔ π (tailX π k) = 1 := by
    constructor
    · intro h
      apply Units.ext
      have h' : ((tailPsi π k : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [h, Matrix.SpecialLinearGroup.coe_one]
      rw [tailPsi_apply] at h'
      rw [h', Units.val_one]
    · intro h
      apply Subtype.ext
      rw [tailPsi_apply, h, Units.val_one, Matrix.SpecialLinearGroup.coe_one]
  rw [key]
  exact hker (tailX π k)

theorem tailPsi_surjective (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F)) :
    Function.Surjective (tailPsi π) := by
  intro M
  obtain ⟨x, hx⟩ := hsurj M
  have hxK : (x : G) ∈ tailK π := by
    refine (mem_tailK_iff π x).mpr ⟨x.2, ?_⟩
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    show Matrix.det ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [hx]
    exact M.2
  refine ⟨⟨x.1, hxK⟩, ?_⟩
  apply Subtype.ext
  rw [tailPsi_apply]
  exact hx

theorem sl2_normal_bot_or_top [CharP F 2] (hF : 4 ≤ Nat.card F)
    (N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [N.Normal] : N = ⊥ ∨ N = ⊤ := by
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨r, hr, hzr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have hr1 : r = 1 := by
      rcases sq_eq_one_iff.mp hr2 with h | h
      · exact h
      · rw [h, CharTwo.neg_eq]
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hzr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
  have hsurjp := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
  haveI : (N.map (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))).Normal :=
    Subgroup.Normal.map inferInstance _ hsurjp
  haveI := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk'
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)))) with h | h
  · left
    apply Subgroup.map_injective hinj
    rw [h, Subgroup.map_bot]
  · right
    apply Subgroup.map_injective hinj
    rw [h, Subgroup.map_top_of_surjective _ hsurjp]

theorem tail_chiefStep [CharP F 2] (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hF : 4 ≤ Nat.card F) (hQn : Inv X Q) (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ Q)
    (hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F))
    (hQK : Q ≤ tailK π) (hQlt : Q < tailK π) (hKinv : Inv X (tailK π)) :
    ChiefStep X Q (tailK π) := by
  refine ⟨hQlt, hQn, hKinv, ?_, ?_⟩
  · intro y hy z hz
    exact hQn y (tailK_le π hy) z hz
  · intro Q' hQQ' hQ'K _ hQ'norm
    classical
    have hnorm' : (Q'.subgroupOf (tailK π)).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hQ'norm (g : G) g.2 (n : G) hn
      simpa using this⟩
    have hSn : ((Q'.subgroupOf (tailK π)).map (tailPsi π)).Normal :=
      Subgroup.Normal.map hnorm' _ (tailPsi_surjective π hsurj)
    rcases sl2_normal_bot_or_top hF ((Q'.subgroupOf (tailK π)).map (tailPsi π)) with
      hbot | htop
    · left
      refine le_antisymm ?_ hQQ'
      intro q hq
      have hqK : q ∈ tailK π := hQ'K hq
      have hmem : (⟨q, hqK⟩ : ↥(tailK π)) ∈ Q'.subgroupOf (tailK π) :=
        Subgroup.mem_subgroupOf.mpr hq
      have him : tailPsi π ⟨q, hqK⟩ ∈ (Q'.subgroupOf (tailK π)).map (tailPsi π) :=
        Subgroup.mem_map_of_mem _ hmem
      rw [hbot, Subgroup.mem_bot] at him
      exact (tailPsi_eq_one_iff π hker ⟨q, hqK⟩).mp him
    · right
      refine le_antisymm hQ'K ?_
      intro k hk
      have him : tailPsi π ⟨k, hk⟩ ∈ (Q'.subgroupOf (tailK π)).map (tailPsi π) := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.mp him
      have hprod : tailPsi π (n⁻¹ * ⟨k, hk⟩) = 1 := by
        rw [map_mul, map_inv, hnk, inv_mul_cancel]
      have hq : ((n⁻¹ * ⟨k, hk⟩ : ↥(tailK π)) : G) ∈ Q :=
        (tailPsi_eq_one_iff π hker _).mp hprod
      have hnQ' : (n : G) ∈ Q' := Subgroup.mem_subgroupOf.mp hn
      have hq' : ((n⁻¹ * ⟨k, hk⟩ : ↥(tailK π)) : G) ∈ Q' := hQQ' hq
      have hmul := Q'.mul_mem hnQ' hq'
      simpa using hmul

theorem tail_inv (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F) : Inv X (tailK π) := by
  intro x hx y hy
  obtain ⟨hyX, hdy⟩ := (mem_tailK_iff π y).mp hy
  have hnormD : (detSub π).Normal := by
    unfold detSub
    infer_instance
  have hmem : (⟨x, hx⟩ : ↥X) * ⟨y, hyX⟩ * (⟨x, hx⟩ : ↥X)⁻¹ ∈ detSub π :=
    hnormD.conj_mem ⟨y, hyX⟩ (MonoidHom.mem_ker.mpr hdy) ⟨x, hx⟩
  unfold tailK
  exact Subgroup.mem_map_of_mem X.subtype hmem

theorem exists_tail_not_mem (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ Q)
    (hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F)) :
    ∃ g ∈ tailK π, g ∉ Q := by
  obtain ⟨x, hx⟩ := hsurj ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨x, (mem_tailK_iff π x).mpr ⟨x.2, ?_⟩, fun hxQ => ?_⟩
  · apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    show Matrix.det ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [hx]
    simp [Matrix.det_fin_two]
  · have h1 : π x = 1 := (hker x).mpr hxQ
    have h2 : ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
      rw [h1, Units.val_one]
    rw [hx] at h2
    have h3 := congrFun (congrFun h2 0) 1
    simp at h3

theorem tail_not_factorTwo [Finite G] [Finite F] [CharP F 2]
    (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hF : 4 ≤ Nat.card F) (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ Q)
    (hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F))
    (hQK : Q ≤ tailK π) : ¬ FactorTwo Q (tailK π) := by
  rintro ⟨d, -, hcard⟩
  have hk : (tailPsi π).ker = Q.subgroupOf (tailK π) := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact tailPsi_eq_one_iff π hker k
  have hrel : Q.relIndex (tailK π) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
    unfold Subgroup.relIndex
    rw [← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (tailPsi_surjective π hsurj),
      Subgroup.card_top]
  have hmul := Subgroup.relIndex_mul_card (H := Q) (K := tailK π)
  rw [inf_eq_left.mpr hQK, hcard, hrel] at hmul
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 2 ^ d :=
    Nat.eq_of_mul_eq_mul_right hQpos hmul
  rw [CFSG.Quasithin.SL2Model.card_SL2] at hcardSL
  obtain ⟨m, hm⟩ := CFSG.Quasithin.SL2Model.card_F_even (F := F)
  have hdvd : Nat.card F ^ 2 - 1 ∣ 2 ^ d := Dvd.intro_left _ hcardSL
  have hodd : Odd (Nat.card F ^ 2 - 1) := by
    have hm2 : 2 ≤ m := by omega
    have hsq : Nat.card F ^ 2 = 4 * (m * m) := by
      rw [hm]
      ring
    have hm1 : 1 ≤ m * m := by nlinarith
    exact ⟨2 * (m * m) - 1, by omega⟩
  have hcop : Nat.Coprime (Nat.card F ^ 2 - 1) (2 ^ d) :=
    Nat.Coprime.pow_right d (Odd.coprime_two_right hodd)
  have h1 : Nat.card F ^ 2 - 1 = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
  have h16 : 16 ≤ Nat.card F ^ 2 := by nlinarith
  omega

theorem tail_odd [Finite F] [CharP F 2] (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hF : 4 ≤ Nat.card F) : Odd ((tailK π).relIndex X) := by
  have hsub : (tailK π).subgroupOf X = detSub π := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_tailK_iff]
    constructor
    · rintro ⟨_, hd⟩
      exact MonoidHom.mem_ker.mpr hd
    · intro hx
      exact ⟨x.2, MonoidHom.mem_ker.mp hx⟩
  have hrel : (tailK π).relIndex X = (detSub π).index := by
    unfold Subgroup.relIndex
    rw [hsub]
  rw [hrel]
  unfold detSub
  rw [Subgroup.index_ker]
  obtain ⟨m, hm⟩ := CFSG.Quasithin.SL2Model.card_F_even (F := F)
  have hunits := Nat.card_eq_card_units_add_one (α := F)
  have hdvd := Subgroup.card_subgroup_dvd_card
    ((Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) F →* Fˣ).comp π).range
  apply Odd.of_dvd_nat _ hdvd
  exact ⟨m - 1, by omega⟩

end TailHelpers

section Tail

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {X Q : Subgroup G}

theorem tail_big (hF : 2 < Nat.card F) (hQX : Q ≤ X) (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ Q)
    (hsurj : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, ∃ x : ↥X,
      ((π x : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        (M : Matrix (Fin 2) (Fin 2) F)) :
    ChainCounts F X true Q X 0 0 := by
  obtain ⟨m, hm⟩ := CFSG.Quasithin.SL2Model.card_F_even (F := F)
  have hF4 : 4 ≤ Nat.card F := by omega
  have hKX : tailK π ≤ X := tailK_le π
  have hKinv : Inv X (tailK π) := tail_inv π
  have hQK : Q ≤ tailK π := by
    intro q hq
    refine (mem_tailK_iff π q).mpr ⟨hQX hq, ?_⟩
    have h1 : π ⟨q, hQX hq⟩ = 1 := (hker ⟨q, hQX hq⟩).mpr hq
    rw [h1, map_one]
  have hQlt : Q < tailK π := by
    obtain ⟨g, hg, hgQ⟩ := exists_tail_not_mem π hker hsurj
    exact lt_of_le_of_ne hQK (fun h => hgQ (by rw [h]; exact hg))
  have hstep := tail_chiefStep π hF4 hQn hker hsurj hQK hQlt hKinv
  have hnot := tail_not_factorTwo π hF4 hker hsurj hQK
  have hodd := tail_odd π hF4
  have hXinv : Inv X X := fun x hx y hy => X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  have h1 : ChainCounts F X true Q (tailK π) 0 0 :=
    ChainCounts.other rfl hstep hnot (ChainCounts.refl (tailK π) hKinv)
  have h2 : ChainCounts F X true (tailK π) X 0 0 :=
    exists_chain_odd hKX hKinv hXinv hKinv hodd
  exact ChainCounts.trans h1 h2

theorem tail_small (hF : Nat.card F = 2) (hQX : Q ≤ X)
    (hQn : ∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q)
    (π : ↥X →* Matrix.GeneralLinearGroup (Fin 2) F)
    (hker : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ Q) :
    ChainCounts F X true Q X 0 0 := by
  have hsub : Q.subgroupOf X = π.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact (hker x).symm
  have hrel : Q.relIndex X = Nat.card π.range := by
    unfold Subgroup.relIndex
    rw [hsub, Subgroup.index_ker]
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) = 6 := by
    haveI : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hF
    rw [Matrix.card_GL_field, Fin.prod_univ_two, hc]
    norm_num
  have hdvd : Q.relIndex X ∣ 6 := by
    rw [hrel, ← hGL]
    exact Subgroup.card_subgroup_dvd_card _
  have hXinv : Inv X X := fun x hx y hy => X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)
  exact exists_chain_small hQX hQn hXinv hQn hdvd

end Tail

end CFSG.Quasithin.RonanG25
