module

public import CFSG.RankThree.PartOne.KF.Z2S4Mod
public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

section Normalizer

variable {p : ℕ} {K : Type} [Field K]

theorem perm_four_pow_eq_one' (hp : p.Prime) (h5 : 5 ≤ p) (π : Equiv.Perm (Fin 4))
    (h : π ^ p = 1) : π = 1 := by
  have h1 : orderOf π ∣ p := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
  · exact orderOf_eq_one_iff.mp h2
  · exfalso
    have h3 : orderOf π ∣ Nat.card (Equiv.Perm (Fin 4)) := orderOf_dvd_natCard π
    have hc : Nat.card (Equiv.Perm (Fin 4)) = 2 ^ 3 * 3 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [h2, hc] at h3
    rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h4
      omega

theorem perm_four_center : ∀ σ : Equiv.Perm (Fin 4),
    (∀ τ : Equiv.Perm (Fin 4), τ * σ = σ * τ) → σ = 1 := by
  decide

theorem mul_self_zmod_two (e : Multiplicative (ZMod 2)) : e * e = 1 := by
  revert e
  decide

theorem pow_odd_zmod_two (e : Multiplicative (ZMod 2)) {n : ℕ} (hn : Odd n) : e ^ n = e := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, sq, mul_self_zmod_two, one_pow, one_mul]

omit [Field K] in
theorem act10_one_eq (σ : Equiv.Perm (Fin 4)) [Field K] :
    (act10 (p := p) (K := K)) ((1 : Multiplicative (ZMod 2)), σ) = symAut p K σ := by
  rw [act10_apply, invHom_apply_one, one_mul]

theorem eq_one_of_normalizes_w10 [Finite K] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4), Function.Injective α →
      ∃ π : Equiv.Perm (Fin 4), ∀ σ, α σ = π * σ * π⁻¹)
    (φ : MulAut (torusVec p 4 K)) (hφ : φ ^ p = 1)
    (hnorm : ∀ γ : W10, ∃ γ' : W10, φ * act10 γ * φ⁻¹ = act10 γ') : φ = 1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hinj := act10_injective hp hp2 hζ
  choose α hα using hnorm
  have hαmul : ∀ γ δ, α (γ * δ) = α γ * α δ := fun γ δ => hinj (by
    rw [map_mul, ← hα γ, ← hα δ, ← hα (γ * δ), map_mul]
    group)
  have hα1 : α 1 = 1 := hinj (by
    rw [← hα 1, map_one]
    group)
  have hαinj : Function.Injective α := fun γ δ h => hinj (by
    have h1 := hα γ
    have h2 := hα δ
    rw [h] at h1
    rw [← h2] at h1
    exact mul_right_cancel (mul_left_cancel h1))
  let αh : W10 →* W10 := { toFun := α, map_one' := hα1, map_mul' := hαmul }
  have hiter : ∀ (k : ℕ) (γ : W10), act10 (α^[k] γ) = φ ^ k * act10 γ * (φ ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro γ; simp
    | succ k ih =>
      intro γ
      rw [Function.iterate_succ_apply', ← hα, ih, pow_succ', mul_inv_rev]
      group
  have hfix : ∀ γ, α^[p] γ = γ := fun γ => hinj (by
    rw [hiter, hφ]
    simp)
  let ι : Equiv.Perm (Fin 4) →* W10 := MonoidHom.inr _ _
  let ᾱ : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4) := (MonoidHom.snd _ _).comp (αh.comp ι)
  let η : Equiv.Perm (Fin 4) →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp (αh.comp ι)
  have hαι : ∀ σ, α (1, σ) = (η σ, ᾱ σ) := fun σ => rfl
  have hcentral : ∀ (e : Multiplicative (ZMod 2)) (w : W10), (e, (1 : Equiv.Perm (Fin 4))) * w =
      w * (e, 1) := fun e w => by
    obtain ⟨e', σ'⟩ := w
    simp [Prod.mk_mul_mk, mul_comm]
  have hᾱinj : Function.Injective ᾱ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hc : α (1, σ) = (η σ, 1) := by rw [hαι]; exact Prod.ext rfl hσ
    apply perm_four_center
    intro τ
    have h1 : α ((1, σ) * (1, τ)) = α ((1, τ) * (1, σ)) := by
      rw [hαmul, hαmul, hc]
      exact hcentral _ _
    have := hαinj h1
    simpa [Prod.mk_mul_mk] using (congrArg Prod.snd this).symm
  obtain ⟨π, hπ⟩ := hinner ᾱ hᾱinj
  have hαz : α ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Equiv.Perm (Fin 4))) =
      (Multiplicative.ofAdd 1, 1) := by
    obtain ⟨e, s, hes⟩ : ∃ (e : Multiplicative (ZMod 2)) (s : Equiv.Perm (Fin 4)),
        α ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Equiv.Perm (Fin 4))) = (e, s) :=
      ⟨_, _, rfl⟩
    have hs : s = 1 := by
      apply perm_four_center
      intro τ'
      have hτ : ᾱ (π⁻¹ * τ' * π) = τ' := by
        rw [hπ]
        group
      have h1 : α ((Multiplicative.ofAdd (1 : ZMod 2), (1 : Equiv.Perm (Fin 4))) *
          (1, π⁻¹ * τ' * π)) =
          α ((1, π⁻¹ * τ' * π) *
            (Multiplicative.ofAdd (1 : ZMod 2), (1 : Equiv.Perm (Fin 4)))) := by
        rw [hcentral]
      rw [hαmul, hαmul, hes, hαι, hτ] at h1
      simpa [Prod.mk_mul_mk] using (congrArg Prod.snd h1).symm
    subst hs
    rcases cases_zmod_two e with rfl | rfl
    · exfalso
      have h1 : α ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Equiv.Perm (Fin 4))) = α 1 := by
        rw [hes, hα1]
        rfl
      have h2 := hαinj h1
      have hne : ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Equiv.Perm (Fin 4))) ≠ (1 : W10) := by
        decide
      exact hne h2
    · exact hes
  have hαe : ∀ e : Multiplicative (ZMod 2), α (e, (1 : Equiv.Perm (Fin 4))) = (e, 1) := by
    intro e
    rcases cases_zmod_two e with rfl | rfl
    · exact hα1
    · exact hαz
  have hηconj : ∀ σ τ, η (τ * σ * τ⁻¹) = η σ := fun σ τ => by
    rw [map_mul, map_mul, mul_comm (η τ) (η σ), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  have hiter2 : ∀ (k : ℕ) (σ : Equiv.Perm (Fin 4)),
      α^[k] (1, σ) = (η σ ^ k, π ^ k * σ * (π ^ k)⁻¹) := by
    intro k
    induction k with
    | zero => intro σ; simp
    | succ k ih =>
      intro σ
      rw [Function.iterate_succ_apply', ih]
      have h1 : ((η σ ^ k, π ^ k * σ * (π ^ k)⁻¹) : W10) =
          (η σ ^ k, 1) * (1, π ^ k * σ * (π ^ k)⁻¹) := by
        simp [Prod.mk_mul_mk]
      rw [h1, hαmul, hαe, hαι, hηconj, hπ]
      simp only [Prod.mk_mul_mk, pow_succ]
      refine Prod.ext rfl ?_
      show (π * (π ^ k * σ * (π ^ k)⁻¹) * π⁻¹) = π ^ k * π * σ * (π ^ k * π)⁻¹
      group
  have hη1 : ∀ σ, η σ = 1 := by
    intro σ
    have h1 := hfix (1, σ)
    rw [hiter2] at h1
    have h2 : η σ ^ p = 1 := congrArg Prod.fst h1
    rw [pow_odd_zmod_two _ (hp.odd_of_ne_two hp2)] at h2
    exact h2
  have hnormS : ∀ σ : Equiv.Perm (Fin 4), ∃ τ : Equiv.Perm (Fin 4),
      φ * symAut p K σ * φ⁻¹ = symAut p K τ := fun σ => by
    refine ⟨π * σ * π⁻¹, ?_⟩
    rw [← act10_one_eq, hα (1, σ), hαι, hη1, act10_one_eq, hπ]
  exact eq_one_of_symNormalizer hp hp2 (by norm_num)
    (fun π hπp => perm_four_pow_eq_one' hp hp5 π hπp) hζ (fun α hα _ => hinner α hα) φ hφ hnormS

end Normalizer

section Reflections

variable {p : ℕ} {K : Type} [Field K]

@[expose] def refl10 : Set W10 :=
  {w | (∃ a b : Fin 4, a ≠ b ∧ w = ((1 : Multiplicative (ZMod 2)), Equiv.swap a b)) ∨
    (∃ σ : Equiv.Perm (Fin 4), IsDt σ ∧ w = (Multiplicative.ofAdd (1 : ZMod 2), σ))}

omit [Field K] in
theorem closure_refl10 : Subgroup.closure refl10 = ⊤ := by
  set H := Subgroup.closure refl10 with hH
  have hinv1 : (1 : Multiplicative (ZMod 2))⁻¹ = 1 := by decide
  have hswap : ∀ a b : Fin 4, a ≠ b → ((1 : Multiplicative (ZMod 2)), Equiv.swap a b) ∈ H :=
    fun a b hab => Subgroup.subset_closure (Or.inl ⟨a, b, hab, rfl⟩)
  have hS : ∀ σ : Equiv.Perm (Fin 4), ((1 : Multiplicative (ZMod 2)), σ) ∈ H := by
    intro σ
    have hσ : σ ∈ Subgroup.closure {σ : Equiv.Perm (Fin 4) | σ.IsSwap} := by
      rw [Equiv.Perm.closure_isSwap]
      trivial
    induction hσ using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, b, hab, rfl⟩ := hx
      exact hswap a b hab
    | one => exact H.one_mem
    | mul x y _ _ hx hy =>
      have := H.mul_mem hx hy
      simpa [Prod.mk_mul_mk] using this
    | inv x _ hx =>
      convert H.inv_mem hx using 1
      exact Prod.ext hinv1.symm rfl
  have hz : ((Multiplicative.ofAdd (1 : ZMod 2)), (1 : Equiv.Perm (Fin 4))) ∈ H := by
    have h1 : (Multiplicative.ofAdd (1 : ZMod 2), dt1) ∈ H :=
      Subgroup.subset_closure (Or.inr ⟨dt1, Or.inl rfl, rfl⟩)
    have h2 := H.mul_mem h1 (H.inv_mem (hS dt1))
    have h3 : (Multiplicative.ofAdd (1 : ZMod 2), dt1) * ((1 : Multiplicative (ZMod 2)), dt1)⁻¹ =
        (Multiplicative.ofAdd (1 : ZMod 2), (1 : Equiv.Perm (Fin 4))) :=
      Prod.ext (by show Multiplicative.ofAdd (1 : ZMod 2) * (1 : Multiplicative (ZMod 2))⁻¹ = _
                   rw [hinv1, mul_one]) (by show dt1 * dt1⁻¹ = 1; exact mul_inv_cancel _)
    convert h2 using 1
    exact h3.symm
  rw [eq_top_iff]
  rintro ⟨e, σ⟩ -
  rcases cases_zmod_two e with rfl | rfl
  · exact hS σ
  · have := H.mul_mem hz (hS σ)
    simpa [Prod.mk_mul_mk] using this

end Reflections

abbrev W10Ctx {G : Type} [Group G] (p : ℕ) (K : Type) [Field K] (L F : Subgroup G) : Type :=
  WCtx (act10 : W10 →* MulAut (torusVec p 4 K)) L F

namespace W10Ctx

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {L F : Subgroup G}
  (S : W10Ctx p K L F)

include S in
theorem card_F [Finite K] (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Nat.card F = p ^ 3 := by
  rw [← Nat.card_congr S.tor.toEquiv]
  exact card_torusVec_eq hp hζ 3

include S in
theorem actF_injective (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Function.Injective S.actF := fun _ _ h =>
  act10_injective hp hp2 hζ ((MulAut.congr S.tor).injective h)

@[expose] noncomputable def weylEquiv (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : ↥(torusImage F L) ≃* W10 :=
  (MulEquiv.subgroupCongr S.torusImage_eq_range).trans
    (MonoidHom.ofInjective (S.actF_injective hp hp2 hζ)).symm

theorem autMoved_actF (w : W10) :
    autMoved F (S.actF w) = (movedV (act10 (p := p) (K := K) w)).map S.tor.toMonoidHom := by
  unfold autMoved movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨act10 w d * d⁻¹, ⟨d, rfl⟩, by simp [S.actF_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.actF_apply, map_mul, map_inv]⟩

include S in
theorem isAutReflection_one_swap [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {a b : Fin 4} (hab : a ≠ b) :
    IsAutReflection p F (S.actF ((1 : Multiplicative (ZMod 2)), Equiv.swap a b)) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ (S.actF_injective hp hp2 hζ) _]
    have h2 : (act10 (p := p) (K := K)) ((1 : Multiplicative (ZMod 2)), Equiv.swap a b) =
        act10 (p := p) (K := K) ((1 : Multiplicative (ZMod 2)), Equiv.swap a b) := rfl
    rw [← orderOf_injective _ (act10_injective hp hp2 hζ) _]
    exact orderOf_act10_one_swap hp hp2 hζ hab
  · rw [autMoved_actF, Subgroup.card_map_of_injective S.tor.injective, movedV_one_swap]
    exact card_movedSub_swap hp hp2 hζ hab

include S in
theorem isAutReflection_dt [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) {σ : Equiv.Perm (Fin 4)} (h : IsDt σ) :
    IsAutReflection p F (S.actF (Multiplicative.ofAdd (1 : ZMod 2), σ)) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ (S.actF_injective hp hp2 hζ) _]
    rw [← orderOf_injective _ (act10_injective hp hp2 hζ) _]
    exact orderOf_act10_inv_dt hp hp2 hζ h
  · rw [autMoved_actF, Subgroup.card_map_of_injective S.tor.injective]
    exact card_movedV_inv_dt hp hp2 hζ h

include S in
theorem torusImage_eq_closure [Finite K] (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
  apply le_antisymm
  · have h : torusImage F L = Subgroup.closure (S.actF '' refl10) := by
      rw [S.torusImage_eq_range, MonoidHom.range_eq_map, ← closure_refl10, MonoidHom.map_closure]
    calc torusImage F L = Subgroup.closure (S.actF '' refl10) := h
      _ ≤ Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨w, hw | hw, rfl⟩
        · obtain ⟨a, b, hab, rfl⟩ := hw
          exact ⟨by rw [S.torusImage_eq_range]; exact ⟨_, rfl⟩,
            S.isAutReflection_one_swap hp hp2 hζ hab⟩
        · obtain ⟨σ, hσ, rfl⟩ := hw
          exact ⟨by rw [S.torusImage_eq_range]; exact ⟨_, rfl⟩,
            S.isAutReflection_dt hp hp2 hζ hσ⟩
  · exact (Subgroup.closure_le _).mpr fun t ht => ht.1

include S in
theorem torusIrreducible [Finite K] (hp : p.Prime) (h5 : 5 ≤ p) (B : Subgroup G) (hBF : B ≤ F)
    (hB : torusInvariant F L B) : B = ⊥ ∨ B = F := by
  refine S.torusIrreducible_of (fun B' hB' => ?_) B hBF hB
  refine eq_bot_or_eq_top_of_symInvariant hp (by norm_num) ?_ B' (fun σ d hd => ?_)
  · intro h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  · have := hB' (1, σ) d hd
    rwa [act10_one] at this

include S in
theorem not_isAutTransvection [Finite K] (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hinner : ∀ α : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 4), Function.Injective α →
      ∃ π : Equiv.Perm (Fin 4), ∀ σ, α σ = π * σ * π⁻¹)
    (hpow : ∀ a : F, a ^ p = 1) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  intro hT
  have hφp := hT.pow_eq_one hpow
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  have hφV : ((MulAut.congr S.tor).symm φ) ^ p = 1 := by rw [← map_pow, hφp, map_one]
  have h1 : (MulAut.congr S.tor).symm φ = 1 :=
    eq_one_of_normalizes_w10 hp h5 hζ hinner _ hφV (S.normalizes_act hyL hyF)
  apply hT.1
  have := congrArg (MulAut.congr S.tor) h1
  rwa [MulEquiv.apply_symm_apply, map_one] at this

include S in
theorem rowData [Finite K] (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hmodel : RowModel p L 10) : RowData p L F 10 := by
  have hp2 : p ≠ 2 := by omega
  exact ⟨hmodel, S.card_F hp.pos hζ, ⟨S.weylEquiv hp hp2 hζ⟩, S.torusImage_eq_closure hp hp2 hζ,
    fun _ B hBF hB => S.torusIrreducible hp h5 B hBF hB, fun h11 => absurd h11 (by norm_num)⟩

end W10Ctx

end CFSG.RankThree.PartOne.KFU
