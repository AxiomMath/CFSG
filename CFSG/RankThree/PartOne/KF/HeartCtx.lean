module

public import CFSG.RankThree.PartOne.KF.HeartMod
public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

abbrev HeartCtx {G : Type} [Group G] (K : Type) [Field K] (L F : Subgroup G) : Type :=
  WCtx (heartAct K) L F

namespace HeartCtx

variable {G : Type} [Group G] {K : Type} [Field K] {L F : Subgroup G} (S : HeartCtx K L F)

include S in
theorem card_F [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) : Nat.card F = 5 ^ 3 := by
  rw [← Nat.card_congr S.tor.toEquiv]
  exact card_heart hζ

include S in
theorem actF_injective (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) : Function.Injective S.actF :=
  fun _ _ h => heartAct_injective hζ ((MulAut.congr S.tor).injective h)

@[expose] noncomputable def weylEquiv (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    ↥(torusImage F L) ≃* Equiv.Perm (Fin 5) :=
  (MulEquiv.subgroupCongr S.torusImage_eq_range).trans
    (MonoidHom.ofInjective (S.actF_injective hζ)).symm

theorem autMoved_actF (σ : Equiv.Perm (Fin 5)) :
    autMoved F (S.actF σ) = (movedV (heartAct K σ)).map S.tor.toMonoidHom := by
  unfold autMoved movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨heartAct K σ d * d⁻¹, ⟨d, rfl⟩, by simp [S.actF_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.actF_apply, map_mul, map_inv]⟩

include S in
theorem isAutReflection_swap [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) {a b : Fin 5}
    (hab : a ≠ b) : IsAutReflection 5 F (S.actF (Equiv.swap a b)) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ (S.actF_injective hζ) _]
    exact Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr hab)
  · rw [autMoved_actF, Subgroup.card_map_of_injective S.tor.injective]
    exact card_movedV_heartAct_swap hζ hab

include S in
theorem torusImage_eq_closure [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection 5 F t} := by
  apply le_antisymm
  · have h : torusImage F L = Subgroup.closure (S.actF '' {σ | σ.IsSwap}) := by
      rw [S.torusImage_eq_range, MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap,
        MonoidHom.map_closure]
    calc torusImage F L = Subgroup.closure (S.actF '' {σ | σ.IsSwap}) := h
      _ ≤ Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection 5 F t} := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨σ, ⟨a, b, hab, rfl⟩, rfl⟩
        exact ⟨by rw [S.torusImage_eq_range]; exact ⟨_, rfl⟩,
          S.isAutReflection_swap hζ hab⟩
  · exact (Subgroup.closure_le _).mpr fun t ht => ht.1

include S in
theorem torusIrreducible [Finite K] (B : Subgroup G) (hBF : B ≤ F) (hB : torusInvariant F L B) :
    B = ⊥ ∨ B = F :=
  S.torusIrreducible_of (fun _ hB' => heart_irreducible _ hB') B hBF hB

include S in
theorem not_isAutTransvection [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5)
    (hinner : ∀ α : Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 5), Function.Injective α →
      (∀ a b : Fin 5, a ≠ b → ∃ c d : Fin 5, c ≠ d ∧ α (Equiv.swap a b) = Equiv.swap c d) →
      ∃ π : Equiv.Perm (Fin 5), ∀ σ, α σ = π * σ * π⁻¹)
    (hpow : ∀ a : F, a ^ 5 = 1) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ¬ IsAutTransvection 5 F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  intro hT
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  have hφV : ((MulAut.congr S.tor).symm φ) ^ 5 = 1 := by
    rw [← map_pow, hT.pow_eq_one hpow, map_one]
  obtain ⟨π, hπ5, hπφ⟩ := exists_heartAct_of_normalizes hζ hinner _ hφV
    (fun σ => S.normalizes_act hyL hyF σ)
  have hφπ : φ = S.actF π := by
    have := congrArg (MulAut.congr S.tor) hπφ
    rwa [MulEquiv.apply_symm_apply] at this
  by_cases hπ : π = 1
  · apply hT.1
    rw [hφπ, hπ, map_one]
  · have hc := hT.2.1
    rw [hφπ, autMoved_actF, Subgroup.card_map_of_injective S.tor.injective] at hc
    exact card_movedV_heartAct_ne_five_of_pow_five hζ π hπ hπ5 hc

include S in
theorem rowData [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) (hmodel : RowModel 5 L 12) :
    RowData 5 L F 12 :=
  ⟨hmodel, S.card_F hζ, ⟨S.weylEquiv hζ⟩, S.torusImage_eq_closure hζ,
    fun _ B hBF hB => S.torusIrreducible B hBF hB, fun h11 => absurd h11 (by norm_num)⟩

end HeartCtx

end CFSG.RankThree.PartOne.KFU
