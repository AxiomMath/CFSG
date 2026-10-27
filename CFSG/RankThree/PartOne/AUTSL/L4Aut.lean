module

public import CFSG.RankThree.PartOne.AUTSL.L4Push
public import CFSG.RankThree.PartOne.AUTSL.L4Act
public import CFSG.RankThree.PartOne.AUTSL.L4Torus
public import CFSG.RankThree.PartOne.AUTSL.L4Out
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.RankThree.PartOne.AUTSL.L4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K]

theorem conj_injective [CharP K 2] :
    Function.Injective (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
      MulAut (SpecialLinearGroup (Fin 4) K)) := by
  intro x y h
  have h1 : (MulAut.conj (y⁻¹ * x) : MulAut (SpecialLinearGroup (Fin 4) K)) = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hc : y⁻¹ * x ∈ Subgroup.center (SpecialLinearGroup (Fin 4) K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun φ : MulAut (SpecialLinearGroup (Fin 4) K) => φ z) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * (y⁻¹ * x) = ((y⁻¹ * x) * z * (y⁻¹ * x)⁻¹) * (y⁻¹ * x) := by rw [this]
      _ = (y⁻¹ * x) * z := by group
  rw [← scalars_eq_center, LinearCover.scalars_four_eq_bot, Subgroup.mem_bot, inv_mul_eq_one]
    at hc
  exact hc.symm

theorem mul_conj_mul_inv {L : Type*} [Group L] (t : MulAut L) (g : L) :
    t * MulAut.conj g * t⁻¹ = MulAut.conj (t g) := by
  ext z
  simp [MulAut.conj_apply]

@[expose] def Uhat (K : Type) [Field K] : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K)) :=
  (Uge K).map MulAut.conj

@[expose] def Vhat (K : Type) [Field K] : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K)) :=
  (Vge K).map MulAut.conj

theorem Vhat_le_Uhat : Vhat K ≤ Uhat K := Subgroup.map_mono Vge_le_Uge

theorem Uhat_le_inn : Uhat K ≤ InnL (SpecialLinearGroup (Fin 4) K) := by
  rintro _ ⟨u, -, rfl⟩
  exact ⟨u, rfl⟩

theorem card_Vhat [Finite K] [CharP K 2] : Nat.card (Vhat K) = Nat.card K ^ 4 :=
  (Subgroup.card_map_of_injective conj_injective).trans card_Vge

theorem Vhat_comm {x y : MulAut (SpecialLinearGroup (Fin 4) K)} (hx : x ∈ Vhat K)
    (hy : y ∈ Vhat K) : x * y = y * x := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [← map_mul, ← map_mul, Vge_comm hu hv]

theorem Vhat_sq [CharP K 2] {x : MulAut (SpecialLinearGroup (Fin 4) K)} (hx : x ∈ Vhat K) :
    x ^ 2 = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  rw [← map_pow, Vge_sq hu, map_one]

theorem isSylow_Uhat [Finite K] [CharP K 2] :
    IsSylowOf 2 (Uhat K) (InnL (SpecialLinearGroup (Fin 4) K)) := by
  obtain ⟨Sy, hSy⟩ := LinearFlag.exists_sylow_unitriangular (K := K) 2 (n := 4) (by norm_num)
  have hp : IsPGroup 2 (Uge K) := by
    have := Sy.isPGroup'
    rwa [hSy] at this
  refine ⟨Uhat_le_inn, hp.map _, ?_⟩
  have h1 : (InnL (SpecialLinearGroup (Fin 4) K)) =
      (⊤ : Subgroup (SpecialLinearGroup (Fin 4) K)).map MulAut.conj := MonoidHom.range_eq_map _
  rw [Uhat, h1, Subgroup.relIndex_map_map_of_injective _ _ conj_injective,
    Subgroup.relIndex_top_right]
  have := Sy.not_dvd_index
  rwa [hSy] at this

theorem pushingUpS_Uhat [Finite K] [CharP K 2] {f : ℕ} (hq : Nat.card K = 2 ^ f) :
    pushingUpS (Uhat K) = Vhat K := by
  have h := U5K.map_pushingUpS (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
    MulAut (SpecialLinearGroup (Fin 4) K))
    (T := Uge K) (conj_injective.comp (Uge K).subtype_injective)
  rw [pushingUpS_Uge hq] at h
  exact h.symm

section TLemmas

variable [Finite K] [CharP K 2] {T : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K))}

omit [Finite K] [CharP K 2] in
theorem map_conj_Uhat (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K)
    {t : MulAut (SpecialLinearGroup (Fin 4) K)} (ht : t ∈ T) :
    (Uhat K).map (MulAut.conj t).toMonoidHom = Uhat K := by
  rw [← hTU, Subgroup.map_inf _ _ _ (MulAut.conj t).injective, map_conj_self_of_mem ht,
    map_conj_eq_of_mem (InnL_normalizer T) ht]

theorem map_conj_Vhat (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K) {f : ℕ}
    (hq : Nat.card K = 2 ^ f) {t : MulAut (SpecialLinearGroup (Fin 4) K)} (ht : t ∈ T) :
    (Vhat K).map (MulAut.conj t).toMonoidHom = Vhat K := by
  have h := U5K.map_pushingUpS (MulAut.conj t).toMonoidHom (T := Uhat K)
    ((MulAut.conj t).injective.comp (Uhat K).subtype_injective)
  rw [pushingUpS_Uhat hq, map_conj_Uhat hTU ht, pushingUpS_Uhat hq] at h
  exact h

theorem normalizes_corner (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K) {f : ℕ}
    (hq : Nat.card K = 2 ^ f) {t : MulAut (SpecialLinearGroup (Fin 4) K)} (ht : t ∈ T)
    (X : Matrix (Fin 2) (Fin 2) K) : ∃ Y, t (corner X) = corner Y := by
  have hmem : t * MulAut.conj (corner X) * t⁻¹ ∈ Vhat K := by
    rw [← map_conj_Vhat hTU hq ht]
    exact ⟨_, ⟨corner X, corner_mem_Vge X, rfl⟩, rfl⟩
  rw [mul_conj_mul_inv] at hmem
  obtain ⟨w, hw, hw'⟩ := hmem
  have := conj_injective hw'
  rw [this] at hw
  obtain ⟨Y, hY⟩ := mem_Vge.1 hw
  exact ⟨Y, hY⟩

omit [Finite K] in
theorem exists_fix_of_mem {t : MulAut (SpecialLinearGroup (Fin 4) K)}
    (h : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ Y, t (corner X) = corner Y)
    {x : MulAut (SpecialLinearGroup (Fin 4) K)} (hx : x ∈ Vhat K)
    (hxc : x ∈ Subgroup.centralizer ({t} : Set (MulAut (SpecialLinearGroup (Fin 4) K)))) :
    ∃ X, x = MulAut.conj (corner X) ∧ act t h X = X := by
  obtain ⟨v, hv, rfl⟩ := hx
  obtain ⟨X, rfl⟩ := mem_Vge.1 hv
  refine ⟨X, rfl, ?_⟩
  have h1 : t * MulAut.conj (corner X) = MulAut.conj (corner X) * t :=
    Subgroup.mem_centralizer_iff.1 hxc t rfl
  have h2 : MulAut.conj (t (corner X)) = MulAut.conj (corner X) := by
    rw [← mul_conj_mul_inv, h1]
    group
  have h3 := conj_injective h2
  rw [act_spec t h X] at h3
  exact corner_injective h3

theorem centralizer_card_le (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K) {f : ℕ}
    (hq : Nat.card K = 2 ^ f) {t : MulAut (SpecialLinearGroup (Fin 4) K)} (ht : t ∈ T)
    (htU : t ∉ Uhat K) :
    Nat.card ↥(Vhat K ⊓ Subgroup.centralizer ({t} : Set (MulAut (SpecialLinearGroup (Fin 4) K)))) ≤
      Nat.card K ^ 3 := by
  have h := normalizes_corner hTU hq ht
  have hnot : t ∉ (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
      MulAut (SpecialLinearGroup (Fin 4) K)).range := fun hr => htU (by
    have : t ∈ T ⊓ InnL (SpecialLinearGroup (Fin 4) K) := ⟨ht, hr⟩
    rwa [hTU] at this)
  have hfix := card_fix_le t h hnot
  have hinj : Nat.card ↥(Vhat K ⊓ Subgroup.centralizer
      ({t} : Set (MulAut (SpecialLinearGroup (Fin 4) K)))) ≤
      Nat.card {X : Matrix (Fin 2) (Fin 2) K // act t h X = X} := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨Classical.choose (exists_fix_of_mem h x.2.1 x.2.2),
        (Classical.choose_spec (exists_fix_of_mem h x.2.1 x.2.2)).2⟩) ?_
    intro x x' hxx
    apply Subtype.ext
    have h1 := (Classical.choose_spec (exists_fix_of_mem h x.2.1 x.2.2)).1
    have h2 := (Classical.choose_spec (exists_fix_of_mem h x'.2.1 x'.2.2)).1
    have h3 : Classical.choose (exists_fix_of_mem h x.2.1 x.2.2) =
        Classical.choose (exists_fix_of_mem h x'.2.1 x'.2.2) := congrArg Subtype.val hxx
    rw [h1, h2, h3]
  have hq0 : 0 < Nat.card K := Nat.card_pos
  have : Nat.card {X : Matrix (Fin 2) (Fin 2) K // act t h X = X} * Nat.card K ≤
      Nat.card K ^ 3 * Nat.card K := by
    calc _ ≤ Nat.card K ^ 4 := hfix
      _ = _ := by ring
  exact hinj.trans (Nat.le_of_mul_le_mul_right this hq0)

theorem relIndex_Uhat_le (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K)
    {F : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K))} (hFT : F ≤ T)
    (hF : ∀ x ∈ F, x ^ 2 = 1) : (F ⊓ Uhat K).relIndex F ≤ 4 := by
  have : F ⊓ Uhat K = F ⊓ InnL (SpecialLinearGroup (Fin 4) K) := by
    rw [← hTU, ← inf_assoc, inf_eq_left.2 hFT]
  rw [this]
  exact outer_bound_of_equiv (LinearCover.projectiveSLFourEquivSL K).symm F hF

theorem inner_bound_hat {F : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K))} (hF : F ≤ Uhat K)
    (hFV : ¬ F ≤ Vhat K) :
    (F ⊓ Vhat K).relIndex F * Nat.card ↥(Vhat K ⊓ Subgroup.centralizer
      (F : Set (MulAut (SpecialLinearGroup (Fin 4) K)))) ≤ Nat.card K ^ 3 := by
  set F₀ : Subgroup (SpecialLinearGroup (Fin 4) K) := F.comap MulAut.conj with hF₀
  have hFrange : F ≤ (MulAut.conj : SpecialLinearGroup (Fin 4) K →*
      MulAut (SpecialLinearGroup (Fin 4) K)).range := hF.trans Uhat_le_inn
  have hFmap : F₀.map MulAut.conj = F := Subgroup.map_comap_eq_self hFrange
  have hF₀U : F₀ ≤ Uge K := by
    intro x hx
    obtain ⟨u, hu, hux⟩ := hF hx
    rwa [← conj_injective hux]
  have hF₀V : ¬ F₀ ≤ Vge K := fun h => hFV (by
    rw [← hFmap]
    exact Subgroup.map_mono h)
  have hb := inner_bound hF₀U hF₀V
  have e1 : F ⊓ Vhat K = (F₀ ⊓ Vge K).map MulAut.conj := by
    rw [Subgroup.map_inf _ _ _ conj_injective, hFmap]
    rfl
  have e2 : (F ⊓ Vhat K).relIndex F = (F₀ ⊓ Vge K).relIndex F₀ := by
    rw [e1]
    conv_lhs => rw [← hFmap]
    exact Subgroup.relIndex_map_map_of_injective _ _ conj_injective
  have e3 : Vhat K ⊓ Subgroup.centralizer (F : Set (MulAut (SpecialLinearGroup (Fin 4) K))) =
      (Vge K ⊓ Subgroup.centralizer (F₀ : Set (SpecialLinearGroup (Fin 4) K))).map
        MulAut.conj := by
    ext x
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hxc⟩
      refine ⟨v, ⟨hv, Subgroup.mem_centralizer_iff.2 fun f hf => ?_⟩, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hxc (MulAut.conj f) (by
        rw [← hFmap]
        exact ⟨f, hf, rfl⟩)
      rw [← map_mul, ← map_mul] at this
      exact conj_injective this
    · rintro ⟨v, ⟨hv, hvc⟩, rfl⟩
      refine ⟨⟨v, hv, rfl⟩, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [← hFmap] at hy
      obtain ⟨f, hf, rfl⟩ := hy
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hvc f hf]
  rw [e2, e3, Subgroup.card_map_of_injective conj_injective]
  exact hb

theorem centralizer_Vhat (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K) {f : ℕ}
    (hq : Nat.card K = 2 ^ f) {t : MulAut (SpecialLinearGroup (Fin 4) K)} (ht : t ∈ T)
    (hc : ∀ v ∈ Vhat K, v * t = t * v) : t ∈ Vhat K := by
  by_cases htU : t ∈ Uhat K
  · obtain ⟨u, hu, rfl⟩ := htU
    refine ⟨u, centralizer_Uge_Vge hu fun v hv => ?_, rfl⟩
    have := hc (MulAut.conj v) ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact conj_injective this
  · exfalso
    have h1 := centralizer_card_le hTU hq ht htU
    have h2 : Vhat K ≤ Vhat K ⊓ Subgroup.centralizer
        ({t} : Set (MulAut (SpecialLinearGroup (Fin 4) K))) := fun v hv =>
      ⟨hv, Subgroup.mem_centralizer_iff.2 fun h' hh' => by
        rw [Set.mem_singleton_iff] at hh'
        rw [hh']
        exact (hc v hv).symm⟩
    have h3 := Subgroup.card_le_of_le h2
    rw [card_Vhat] at h3
    have hq1 : 1 < Nat.card K := Finite.one_lt_card
    have : Nat.card K ^ 3 < Nat.card K ^ 4 := Nat.pow_lt_pow_right hq1 (by norm_num)
    omega

theorem pushingUpS_eq_Vhat (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K) {f : ℕ}
    (hq : Nat.card K = 2 ^ f) (h5 : 5 ≤ Nat.card K) : pushingUpS T = Vhat K := by
  have hVT : Vhat K ≤ T := Vhat_le_Uhat.trans (by rw [← hTU]; exact inf_le_left)
  have hq0 : 0 < Nat.card K ^ 3 := by positivity
  refine pushingUpS_eq_of_bounds (n := 4 * f) (m := 4) (B₁ := Nat.card K ^ 3)
    (B₂ := Nat.card K ^ 3) Vhat_le_Uhat hVT (fun x hx y hy => Vhat_comm hx hy)
    (fun x hx => Vhat_sq hx) ?_ (fun t ht hc => centralizer_Vhat hTU hq ht hc) (by norm_num)
    (fun F hFT _ hFs => relIndex_Uhat_le hTU hFT hFs)
    (fun F hFU _ _ hFV => inner_bound_hat hFU hFV)
    (fun t ht htU => centralizer_card_le hTU hq ht htU) ?_ ?_
  · rw [card_Vhat, hq, ← pow_mul, mul_comm]
  · rw [card_Vhat]
    calc 4 * Nat.card K ^ 3 < 5 * Nat.card K ^ 3 := by omega
      _ ≤ Nat.card K * Nat.card K ^ 3 := Nat.mul_le_mul_right _ h5
      _ = Nat.card K ^ 4 := by ring
  · rw [card_Vhat]
    calc 4 * Nat.card K ^ 3 < 5 * Nat.card K ^ 3 := by omega
      _ ≤ Nat.card K * Nat.card K ^ 3 := Nat.mul_le_mul_right _ h5
      _ = Nat.card K ^ 4 := by ring

end TLemmas

@[expose] def Zhat (K : Type) [Field K] : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K)) :=
  Uhat K ⊓ Subgroup.centralizer (Uhat K : Set (MulAut (SpecialLinearGroup (Fin 4) K)))

theorem Zhat_le_Uhat : Zhat K ≤ Uhat K := inf_le_left

section Centre

theorem Zhat_ne_bot [Finite K] [CharP K 2] : Zhat K ≠ ⊥ := by
  have hU : IsPGroup 2 (Uhat K) := isSylow_Uhat.2.1
  have hne : Uhat K ≠ ⊥ := by
    intro h
    have h1 : Vhat K ≤ ⊥ := h ▸ Vhat_le_Uhat
    have h2 := Subgroup.card_le_of_le h1
    rw [card_Vhat, Subgroup.card_bot] at h2
    have hq1 : 1 < Nat.card K := Finite.one_lt_card
    have : 1 < Nat.card K ^ 4 := Nat.one_lt_pow (by norm_num) hq1
    omega
  obtain ⟨x, hxU, hx1, hxc⟩ := exists_ne_one_mem_center_of_normal hU le_rfl
    (fun t ht x hx => mul_mem (mul_mem ht hx) (inv_mem ht)) hne
  intro hZ
  apply hx1
  have : x ∈ Zhat K := ⟨hxU, Subgroup.mem_centralizer_iff.2 fun h hh => hxc h hh⟩
  rw [hZ, Subgroup.mem_bot] at this
  exact this

theorem exists_corner_of_mem_Zhat [CharP K 2] {x : MulAut (SpecialLinearGroup (Fin 4) K)}
    (hx : x ∈ Zhat K) :
    ∃ c : K, x = MulAut.conj (corner !![0, c; 0, 0]) := by
  obtain ⟨⟨u, hu, rfl⟩, hxc⟩ := hx
  obtain ⟨c, hc⟩ := center_Uge hu fun v hv => by
    have := Subgroup.mem_centralizer_iff.1 hxc (MulAut.conj v) ⟨v, hv, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact conj_injective this
  exact ⟨c, by rw [hc]⟩

theorem Zhat_sq [CharP K 2] {x : MulAut (SpecialLinearGroup (Fin 4) K)} (hx : x ∈ Zhat K) :
    x ^ 2 = 1 := by
  obtain ⟨c, rfl⟩ := exists_corner_of_mem_Zhat hx
  rw [← map_pow, Vge_sq (corner_mem_Vge _), map_one]

theorem Zhat_normalized {T : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K))}
    (hTU : T ⊓ InnL (SpecialLinearGroup (Fin 4) K) = Uhat K)
    {t : MulAut (SpecialLinearGroup (Fin 4) K)} (ht : t ∈ T)
    {x : MulAut (SpecialLinearGroup (Fin 4) K)} (hx : x ∈ Zhat K) : t * x * t⁻¹ ∈ Zhat K := by
  have hU1 : ∀ s ∈ T, ∀ y ∈ Uhat K, s * y * s⁻¹ ∈ Uhat K := fun s hs y hy => by
    rw [← map_conj_Uhat hTU hs]
    exact ⟨y, hy, rfl⟩
  refine ⟨hU1 t ht x (Zhat_le_Uhat hx), Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
  have h1 : t⁻¹ * y * t ∈ Uhat K := by
    have := hU1 t⁻¹ (inv_mem ht) y hy
    simpa using this
  have h2 : (t⁻¹ * y * t) * x = x * (t⁻¹ * y * t) :=
    Subgroup.mem_centralizer_iff.1 hx.2 _ h1
  calc y * (t * x * t⁻¹) = t * ((t⁻¹ * y * t) * x) * t⁻¹ := by group
    _ = t * (x * (t⁻¹ * y * t)) * t⁻¹ := by rw [h2]
    _ = (t * x * t⁻¹) * y := by group

end Centre

section Torus

variable [Finite K] [CharP K 2]

theorem torus_row {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1)
    {A₀ : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K))}
    (hA₀ : A₀ ≤ InnL (SpecialLinearGroup (Fin 4) K)) (hel : IsElementaryAbelian p ↥A₀) :
    ∃ g ∈ InnL (SpecialLinearGroup (Fin 4) K),
      (∃ B : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K)), B ≤ A₀ ∧
        Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.normalizer (Vhat K : Set (MulAut (SpecialLinearGroup (Fin 4) K)))) ∧
      (∃ B : Subgroup (MulAut (SpecialLinearGroup (Fin 4) K)), B ≤ A₀ ∧
        Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧ ∀ x ∈ Zhat K, x ≠ 1 →
          B.map (MulAut.conj g).toMonoidHom ≤
            Subgroup.centralizer ({x} : Set (MulAut (SpecialLinearGroup (Fin 4) K)))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ p := by
    have h1 : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hpq
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h1
    exact ⟨(x : K), IsPrimitiveRoot.coe_units_iff.2 (by simpa [hx] using IsPrimitiveRoot.orderOf x)⟩
  set E₀ : Subgroup (SpecialLinearGroup (Fin 4) K) := A₀.comap MulAut.conj with hE₀
  have hmapE : E₀.map MulAut.conj = A₀ := Subgroup.map_comap_eq_self hA₀
  have hcomm : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := fun x hx y hy => by
    have h1 := congrArg Subtype.val (IsMulCommutative.is_comm.comm
      (⟨MulAut.conj x, hx⟩ : ↥A₀) ⟨MulAut.conj y, hy⟩)
    apply conj_injective
    rw [map_mul, map_mul]
    exact h1
  have hpow : ∀ x ∈ E₀, x ^ p = 1 := fun x hx => by
    have : (MulAut.conj x : MulAut (SpecialLinearGroup (Fin 4) K)) ^ p = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (MulAut.conj x) hx
    apply conj_injective
    rw [map_pow, this, map_one]
  obtain ⟨g, hdiag, B₀, hB₀E, hB₀card, hB₀diag⟩ := torus_data hp hζ E₀ hcomm hpow
  have hcard : Nat.card ↥A₀ = Nat.card ↥E₀ := by
    rw [← hmapE, Subgroup.card_map_of_injective conj_injective]
  refine ⟨MulAut.conj g, ⟨g, rfl⟩, ⟨A₀, le_rfl, Nat.le_mul_of_pos_left _ hp.pos, ?_⟩,
    ⟨B₀.map MulAut.conj, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [← hmapE] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have h1 : (MulAut.conj (MulAut.conj g : MulAut (SpecialLinearGroup (Fin 4) K))).toMonoidHom
        (MulAut.conj x) = MulAut.conj (g * x * g⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rw [h1]
    exact Subgroup.le_normalizer_map (H := Vge K) MulAut.conj
      ⟨g * x * g⁻¹, (hdiag x hx).mem_normalizer, rfl⟩
  · rw [← hmapE]
    exact Subgroup.map_mono hB₀E
  · rw [Subgroup.card_map_of_injective conj_injective, hcard]
    exact hB₀card
  · intro x hx hx1
    obtain ⟨c, rfl⟩ := exists_corner_of_mem_Zhat hx
    rintro _ ⟨b, ⟨y, hy, rfl⟩, rfl⟩
    have h1 : (MulAut.conj (MulAut.conj g : MulAut (SpecialLinearGroup (Fin 4) K))).toMonoidHom
        (MulAut.conj y) = MulAut.conj (g * y * g⁻¹) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rw [h1, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact ((hdiag y (hB₀E hy)).mul_root (hB₀diag y hy) c).symm

end Torus

theorem kf1514PAutGen_SL4 [Finite K] [CharP K 2] {p f : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hq : Nat.card K = 2 ^ f) (hpq : p ∣ Nat.card K - 1) :
    KF1514PAutGen (SpecialLinearGroup (Fin 4) K) p := by
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hq5 : 5 ≤ Nat.card K := by
    have := Nat.le_of_dvd (by omega) hpq
    omega
  exact kf1514PAutGen_of_data (Uhat K) (Vhat K) (Zhat K) isSylow_Uhat
    (fun T _ hTU => pushingUpS_eq_Vhat hTU hq hq5) Zhat_ne_bot Zhat_le_Uhat
    (fun x hx => Zhat_sq hx) (fun T _ hTU t ht x hx => Zhat_normalized hTU ht hx)
    (fun A₀ hA₀ hel _ => torus_row hp hpq hA₀ hel)

end CFSG.RankThree.PartOne.AUTSL.L4
