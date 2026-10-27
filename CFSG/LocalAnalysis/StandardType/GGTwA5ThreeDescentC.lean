module

import all CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescentB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def twd_T {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) : Subgroup (MulAut L') :=
  (w₁.T.comap (U63TB.redHom (U63TB.twoSub ψ.ker hker))).map
    (U63TB.presZ (U63TB.twoSub ψ.ker hker)).subtype

private theorem twd_mem_T {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) {x : MulAut L'} :
    x ∈ twd_T hker hAle w₁ ↔ ∃ (hx : x ∈ U63TB.presZ (U63TB.twoSub ψ.ker hker)),
      U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hx⟩ ∈ w₁.T := by
  constructor
  · intro hx
    obtain ⟨p, hp, hp1⟩ := Subgroup.mem_map.mp hx
    cases hp1
    exact ⟨p.2, by simpa using hp⟩
  · rintro ⟨hx, hhx⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hhx, rfl⟩

private theorem twd_T_le_pres {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) :
    twd_T hker hAle w₁ ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker) :=
  fun _ hx => ((twd_mem_T hker hAle w₁).mp hx).1

private theorem twd_T_comm {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    ∀ x ∈ twd_T hker hAle w₁, ∀ y ∈ twd_T hker hAle w₁, x * y = y * x := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hw₁
  intro x hx y hy
  obtain ⟨hxP, hxT⟩ := (twd_mem_T hker hAle w₁).mp hx
  obtain ⟨hyP, hyT⟩ := (twd_mem_T hker hAle w₁).mp hy
  have hinj := U63TB.redHom_injective (U63TB.twoSub ψ.ker hker) (U63TB.twoSub_le_center hker) hperf
  have h1' : U63TB.redHom (U63TB.twoSub ψ.ker hker) (⟨x, hxP⟩ * ⟨y, hyP⟩) =
      U63TB.redHom (U63TB.twoSub ψ.ker hker) (⟨y, hyP⟩ * ⟨x, hxP⟩) := by
    rw [map_mul, map_mul, h1 _ hxT _ hyT]
  exact congrArg Subtype.val (hinj h1')

private theorem twd_T_cube {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M)
    {x : MulAut L'} (hx : x ∈ twd_T hker hAle w₁) : x ^ 3 = 1 := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, h11, -, -, -, ⟨-,-,-⟩, -, -⟩ := hw₁
  obtain ⟨hxP, hxT⟩ := (twd_mem_T hker hAle w₁).mp hx
  have hαpow : ∀ k n, w₁.α k ((U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩) ^ n) =
      (w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩)) ^ n := by
    intro k n
    induction n with
    | zero =>
      have h1 : w₁.α k 1 = w₁.α k 1 * w₁.α k 1 := by
        simpa using h4 k 1 w₁.T.one_mem 1 w₁.T.one_mem
      have h2 : w₁.α k 1 * (w₁.α k 1)⁻¹ = (w₁.α k 1 * w₁.α k 1) * (w₁.α k 1)⁻¹ :=
        congrArg (fun z => z * (w₁.α k 1)⁻¹) h1
      simpa using h2.symm
    | succ n ih =>
      rw [pow_succ, h4 k _ (w₁.T.pow_mem hxT n) _ hxT, ih, pow_succ]
  have ht3 : (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨x, hxP⟩) ^ 3 = 1 := by
    apply h11 _ (w₁.T.pow_mem hxT 3)
    intro k
    rw [hαpow k 3, twd_mu3_cube]
  have hinj := U63TB.redHom_injective (U63TB.twoSub ψ.ker hker) (U63TB.twoSub_le_center hker) hperf
  have h3 : U63TB.redHom (U63TB.twoSub ψ.ker hker)
      ⟨x ^ 3, (U63TB.presZ (U63TB.twoSub ψ.ker hker)).pow_mem hxP 3⟩ = 1 := by
    rw [show (⟨x ^ 3, (U63TB.presZ (U63TB.twoSub ψ.ker hker)).pow_mem hxP 3⟩ :
        U63TB.presZ (U63TB.twoSub ψ.ker hker)) = ⟨x, hxP⟩ ^ 3 from Subtype.ext rfl,
      map_pow, ht3]
  have h4' := congrArg Subtype.val (hinj (h3.trans (map_one _).symm))
  simpa using h4'

private theorem twd_T_isPGroup3 {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) :
    IsPGroup 3 (twd_T hker hAle w₁) :=
  fun g => ⟨1, Subtype.ext (by rw [pow_one]; exact twd_T_cube hker hperf hAle w₁ hw₁ g.2)⟩

private noncomputable def twd_alpha {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) (φ : MulAut L') :
    Multiplicative (ZMod 3) := by
  classical
  exact if h : φ ∈ U63TB.presZ (U63TB.twoSub ψ.ker hker) then
    w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨φ, h⟩) else 1

private theorem twd_alpha_of_mem {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) (k : Fin N) {φ : MulAut L'}
    (h : φ ∈ U63TB.presZ (U63TB.twoSub ψ.ker hker)) :
    twd_alpha hker hAle w₁ k φ =
      w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨φ, h⟩) := by
  rw [twd_alpha, dif_pos h]

private theorem twd_n_exists {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) (k : Fin N) :
    ∃ n : L', (n : L' ⧸ U63TB.twoSub ψ.ker hker) = w₁.n k ∧
      ∀ τ ∈ twd_T hker hAle w₁,
        (n * (τ n)⁻¹) ^ 3 = 1 ∧ ∀ τ' ∈ twd_T hker hAle w₁, τ' (n * (τ n)⁻¹) = n * (τ n)⁻¹ := by
  classical
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, h7, -, -, h10, -, -, -, -, ⟨-,-,-⟩, -, -⟩ := hw₁'
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective (w₁.n k)
  have hcube : ∀ θ : Multiplicative (ZMod 3), (w₁.cor k θ) ^ 3 = 1 := by
    intro θ
    rw [← map_pow, twd_mu3_cube θ, map_one]
  have h3 : ∀ τ ∈ twd_T hker hAle w₁,
      (n₀ * (τ n₀)⁻¹) ^ 3 ∈ U63TB.twoSub ψ.ker hker := by
    intro τ hτ
    obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
    have hred : ((n₀ * (τ n₀)⁻¹ : L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
        (w₁.cor k (w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩)))⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ n₀, hn₀, h10 k _ hτT]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hred, inv_pow, hcube, inv_one]
  have hfix : ∀ τ ∈ twd_T hker hAle w₁, ∀ τ' ∈ twd_T hker hAle w₁,
      (n₀ * (τ n₀)⁻¹)⁻¹ * τ' (n₀ * (τ n₀)⁻¹) ∈ U63TB.twoSub ψ.ker hker := by
    intro τ hτ τ' hτ'
    obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
    obtain ⟨hτ'P, hτ'T⟩ := (twd_mem_T hker hAle w₁).mp hτ'
    have hred : ((n₀ * (τ n₀)⁻¹ : L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
        (w₁.cor k (w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩)))⁻¹ := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ n₀, hn₀, h10 k _ hτT]
    have hred' : ((τ' (n₀ * (τ n₀)⁻¹) : L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
        (w₁.cor k (w₁.α k (U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩)))⁻¹ := by
      rw [← U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ', hτ'P⟩ (n₀ * (τ n₀)⁻¹), hred,
        map_inv, h7 _ hτ'T k]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hred, hred']
    group
  obtain ⟨z, hz, hzW⟩ := Line63.exists_lift_fixed (U63TB.twoSub_le_center hker)
    (U63TB.isPGroup_twoSub hker) (twd_T_isPGroup3 hker hperf hAle w₁ hw₁)
    (twd_T_comm hker hperf hAle w₁ hw₁)
    (fun a ha z hz => twd_T_le_pres hker hAle w₁ ha z hz) n₀ h3 hfix
  refine ⟨n₀ * z, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one, hn₀]
  · exact hzW

private noncomputable def twd_n {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) (k : Fin N) : L' :=
  Classical.choose (twd_n_exists hker hperf hAle w₁ hw₁ k)

private theorem twd_n_mk {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) (k : Fin N) :
    (twd_n (L' := L') hker hperf hAle w₁ hw₁ k : L' ⧸ U63TB.twoSub ψ.ker hker) = w₁.n k :=
  (Classical.choose_spec (twd_n_exists hker hperf hAle w₁ hw₁ k)).1

private theorem twd_n_cube {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) (k : Fin N)
    {τ : MulAut L'} (hτ : τ ∈ twd_T hker hAle w₁) :
    (twd_n (L' := L') hker hperf hAle w₁ hw₁ k * (τ (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹)
        ^ 3 = 1 :=
  ((Classical.choose_spec (twd_n_exists hker hperf hAle w₁ hw₁ k)).2 τ hτ).1

private noncomputable def twd_Tsc {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) : Subgroup L' where
  carrier := {t | (t : L' ⧸ U63TB.twoSub ψ.ker hker) ∈ w₁.Tsc ∧
    ∀ τ ∈ twd_T hker hAle w₁, τ t = t}
  one_mem' := ⟨w₁.Tsc.one_mem, fun τ _ => map_one τ⟩
  mul_mem' := fun {s t} hs ht =>
    ⟨by rw [QuotientGroup.mk_mul]; exact w₁.Tsc.mul_mem hs.1 ht.1,
      fun τ hτ => by rw [map_mul, hs.2 τ hτ, ht.2 τ hτ]⟩
  inv_mem' := fun {s} hs =>
    ⟨by rw [QuotientGroup.mk_inv]; exact w₁.Tsc.inv_mem hs.1,
      fun τ hτ => by rw [map_inv, hs.2 τ hτ]⟩

private theorem twd_mem_Tsc {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range) {t : L'} :
    t ∈ twd_Tsc hker hAle w₁ ↔ (t : L' ⧸ U63TB.twoSub ψ.ker hker) ∈ w₁.Tsc ∧
      ∀ τ ∈ twd_T hker hAle w₁, τ t = t := Iff.rfl

private theorem twd_lift_Tsc {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) {t₁ : L' ⧸ U63TB.twoSub ψ.ker hker}
    (ht₁ : t₁ ∈ w₁.Tsc) :
    ∃ t ∈ twd_Tsc hker hAle w₁, (t : L' ⧸ U63TB.twoSub ψ.ker hker) = t₁ := by
  classical
  have hw₁' := hw₁
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨-, h15b, -⟩, -, -⟩ := hw₁'
  obtain ⟨t₀, ht₀⟩ := QuotientGroup.mk_surjective t₁
  have hu : ∀ τ ∈ twd_T hker hAle w₁, t₀ * (τ t₀)⁻¹ ∈ U63TB.twoSub ψ.ker hker := by
    intro τ hτ
    obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ht₀,
      show ((τ t₀ : L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
        U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ t₁ from
        (U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ t₀).symm.trans (by rw [ht₀]),
      h15b _ hτT t₁ ht₁, mul_inv_cancel]
  have h3 : ∀ τ ∈ twd_T hker hAle w₁, (t₀ * (τ t₀)⁻¹) ^ 3 ∈ U63TB.twoSub ψ.ker hker :=
    fun τ hτ => (U63TB.twoSub ψ.ker hker).pow_mem (hu τ hτ) 3
  have hfix : ∀ τ ∈ twd_T hker hAle w₁, ∀ τ' ∈ twd_T hker hAle w₁,
      (t₀ * (τ t₀)⁻¹)⁻¹ * τ' (t₀ * (τ t₀)⁻¹) ∈ U63TB.twoSub ψ.ker hker :=
    fun τ hτ τ' hτ' => (U63TB.twoSub ψ.ker hker).mul_mem
      ((U63TB.twoSub ψ.ker hker).inv_mem (hu τ hτ))
      (twd_T_le_pres hker hAle w₁ hτ' _ (hu τ hτ))
  obtain ⟨z, hz, hzW⟩ := Line63.exists_lift_fixed (U63TB.twoSub_le_center hker)
    (U63TB.isPGroup_twoSub hker) (twd_T_isPGroup3 hker hperf hAle w₁ hw₁)
    (twd_T_comm hker hperf hAle w₁ hw₁)
    (fun a ha z hz => twd_T_le_pres hker hAle w₁ ha z hz) t₀ h3 hfix
  have hfixall : ∀ τ ∈ twd_T hker hAle w₁, τ (t₀ * z) = t₀ * z := by
    intro τ hτ
    obtain ⟨hτP, hτT⟩ := (twd_mem_T hker hAle w₁).mp hτ
    have hz1 : (z : L' ⧸ U63TB.twoSub ψ.ker hker) = 1 :=
      (QuotientGroup.eq_one_iff z).mpr hz
    have hmem : (t₀ * z) * (τ (t₀ * z))⁻¹ ∈ U63TB.twoSub ψ.ker hker := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_mul]
      rw [hz1, mul_one, ht₀]
      rw [show ((τ (t₀ * z) : L') : L' ⧸ U63TB.twoSub ψ.ker hker) =
          U63TB.redHom (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩
            ((t₀ * z : L') : L' ⧸ U63TB.twoSub ψ.ker hker) from
          (U63TB.redHom_mk (U63TB.twoSub ψ.ker hker) ⟨τ, hτP⟩ (t₀ * z)).symm]
      rw [show ((t₀ * z : L') : L' ⧸ U63TB.twoSub ψ.ker hker) = t₁ from by
        rw [QuotientGroup.mk_mul, hz1, mul_one, ht₀]]
      rw [h15b _ hτT t₁ ht₁]
      group
    have h1 := eq_one_of_isPGroup_two_of_pow_odd (U63TB.isPGroup_twoSub hker) (m := 3)
      (by norm_num) hmem (hzW τ hτ).1
    exact (mul_inv_eq_one.mp h1).symm
  refine ⟨t₀ * z, (twd_mem_Tsc hker hAle w₁).mpr ⟨?_, hfixall⟩, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one, ht₀]; exact ht₁
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, mul_one, ht₀]

private noncomputable def twd_w {L' R : Type} [Group L'] [Finite L'] [Group R]
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    {ψ : L' →* R} (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker)
      (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M) : GGTorusTorWit 3 N L' A where
  T := twd_T hker hAle w₁
  α := twd_alpha hker hAle w₁
  cor := twd_cor hker hAle w₁
  n := twd_n (L' := L') hker hperf hAle w₁ hw₁
  hn := fun k => by
    refine Subgroup.mem_normalizer_fintype (fun a ha => ?_)
    have hmem : MulAut.conj (w₁.n k) * U63TB.redSub hker hAle ⟨a, ha⟩ *
        (MulAut.conj (w₁.n k))⁻¹ ∈ (U63TB.redSub hker hAle).range :=
      (Subgroup.mem_normalizer_iff.mp (w₁.hn k) (U63TB.redSub hker hAle ⟨a, ha⟩)).mp
        ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨a'', ha''⟩ := hmem
    have hpres : MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) * a * (MulAut.conj
        (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹ ∈
        U63TB.presZ (U63TB.twoSub ψ.ker hker) :=
      (U63TB.presZ (U63TB.twoSub ψ.ker hker)).mul_mem
        ((U63TB.presZ (U63TB.twoSub ψ.ker hker)).mul_mem
          (U63TB.conjP (U63TB.twoSub ψ.ker hker) _).2 (hAle ha))
        ((U63TB.presZ (U63TB.twoSub ψ.ker hker)).inv_mem
          (U63TB.conjP (U63TB.twoSub ψ.ker hker) _).2)
    have heq : (⟨MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) * a *
        (MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹, hpres⟩ :
        U63TB.presZ (U63TB.twoSub ψ.ker hker)) = ⟨a''.1, hAle a''.2⟩ := by
      apply U63TB.redHom_injective (U63TB.twoSub ψ.ker hker)
        (U63TB.twoSub_le_center hker) hperf
      rw [show U63TB.redHom (U63TB.twoSub ψ.ker hker)
          ⟨MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) * a *
            (MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹, hpres⟩ =
          U63TB.redHom (U63TB.twoSub ψ.ker hker) (U63TB.conjP (U63TB.twoSub ψ.ker hker)
            (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) * ⟨a, hAle ha⟩ *
            (U63TB.conjP (U63TB.twoSub ψ.ker hker)
              (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹) from
        congrArg (U63TB.redHom (U63TB.twoSub ψ.ker hker)) (Subtype.ext rfl),
        map_mul, map_mul, map_inv, U63TB.redHom_conjP,
        twd_n_mk (L' := L') hker hperf hAle w₁ hw₁ k]
      rw [← U63TB.redSub_eq]
      exact ha''.symm
    have hval : MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k) * a *
        (MulAut.conj (twd_n (L' := L') hker hperf hAle w₁ hw₁ k))⁻¹ = a''.1 :=
      congrArg Subtype.val heq
    rw [hval]
    exact a''.2
  Tsc := twd_Tsc hker hAle w₁

end CFSG.StandardType

end
