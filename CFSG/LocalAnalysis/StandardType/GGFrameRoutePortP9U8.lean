module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U8Semilin

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU

variable {L : Type} [Group L] {F : Type} [Field F] {m : ℕ}

section AutomizerBound

variable {A : Subgroup (MulAut L)}

private def Gives (ι : ↥A →* UTorus.Proj F m) (γ : Equiv.Perm (Fin m) × ℤˣ)
    (φ : MulAut ↥A) : Prop :=
  ∀ (a : ↥A) (t : Fin m → Fˣ), ι a = QuotientGroup.mk t →
    ι (φ a) = QuotientGroup.mk (fun i => t (γ.1.symm i) ^ (γ.2 : ℤ))

private theorem gives_one (ι : ↥A →* UTorus.Proj F m) :
    Gives ι (1 : Equiv.Perm (Fin m) × ℤˣ) (1 : MulAut ↥A) := by
  intro a t ha
  change ι ((1 : MulAut ↥A) a) =
    QuotientGroup.mk (fun i => t ((1 : Equiv.Perm (Fin m)).symm i) ^ ((1 : ℤˣ) : ℤ))
  have h1 : (1 : Equiv.Perm (Fin m)).symm = 1 := rfl
  rw [show (fun i => t ((1 : Equiv.Perm (Fin m)).symm i) ^ ((1 : ℤˣ) : ℤ)) = t from by
    funext i
    rw [h1]
    simp]
  simpa using ha

private theorem gives_mul {ι : ↥A →* UTorus.Proj F m} {γ δ : Equiv.Perm (Fin m) × ℤˣ}
    {φ ψ : MulAut ↥A} (hγ : Gives ι γ φ) (hδ : Gives ι δ ψ) :
    Gives ι (γ * δ) (φ * ψ) := by
  intro a t ha
  obtain ⟨σ, e⟩ := γ
  obtain ⟨τ, f⟩ := δ
  have h1 : ι (ψ a) = QuotientGroup.mk (fun i => t (τ.symm i) ^ (f : ℤ)) := hδ a t ha
  have h2 : ι (φ (ψ a)) =
      QuotientGroup.mk (fun i => (t (τ.symm (σ.symm i)) ^ (f : ℤ)) ^ (e : ℤ)) :=
    hγ (ψ a) (fun i => t (τ.symm i) ^ (f : ℤ)) h1
  rw [MulAut.mul_apply, h2]
  congr 1
  funext i
  change (t (τ.symm (σ.symm i)) ^ (f : ℤ)) ^ (e : ℤ) =
    t ((σ * τ).symm i) ^ ((e * f : ℤˣ) : ℤ)
  have hidx : (σ * τ).symm i = τ.symm (σ.symm i) := by
    have h : (σ * τ).symm = τ.symm * σ.symm := by
      rw [← Equiv.Perm.inv_def, _root_.mul_inv_rev, Equiv.Perm.inv_def, Equiv.Perm.inv_def]
    rw [h, Equiv.Perm.mul_apply]
  rw [hidx, show ((e * f : ℤˣ) : ℤ) = (f : ℤ) * (e : ℤ) from by
    rw [mul_comm e f, Units.val_mul], _root_.zpow_mul]

private theorem gives_pow {ι : ↥A →* UTorus.Proj F m} {γ : Equiv.Perm (Fin m) × ℤˣ}
    {φ : MulAut ↥A} (h : Gives ι γ φ) (n : ℕ) : Gives ι (γ ^ n) (φ ^ n) := by
  induction n with
  | zero => simpa using gives_one ι
  | succ n ih => rw [pow_succ, pow_succ]; exact gives_mul ih h

private theorem gives_unique {ι : ↥A →* UTorus.Proj F m} (hιinj : Function.Injective ι)
    {γ : Equiv.Perm (Fin m) × ℤˣ} {φ ψ : MulAut ↥A} (hφ : Gives ι γ φ)
    (hψ : Gives ι γ ψ) : φ = ψ := by
  refine MulEquiv.ext fun a => hιinj ?_
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective (ι a)
  exact (hφ a t ht.symm).trans (hψ a t ht.symm).symm

private noncomputable def GammaA (ι : ↥A →* UTorus.Proj F m) :
    Subgroup (Equiv.Perm (Fin m) × ℤˣ) where
  carrier := {γ | ∃ φ ∈ ggAutomizer (⊤ : Subgroup (MulAut L)) A, Gives ι γ φ}
  one_mem' := ⟨1, Subgroup.one_mem _, gives_one ι⟩
  mul_mem' := by
    rintro γ δ ⟨φ, hφ, hγ⟩ ⟨ψ, hψ, hδ⟩
    exact ⟨φ * ψ, Subgroup.mul_mem _ hφ hψ, gives_mul hγ hδ⟩
  inv_mem' := by
    rintro γ ⟨φ, hφ, hγ⟩
    have hz : γ ^ (-1 : ℤ) ∈ Subgroup.zpowers γ := Subgroup.zpow_mem_zpowers γ (-1)
    rw [_root_.zpow_neg_one] at hz
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff γ⁻¹ γ).mp
      (mem_powers_iff_mem_zpowers.mpr hz)
    have hp : Gives ι (γ ^ n) (φ ^ n) := gives_pow hγ n
    rw [hn] at hp
    exact ⟨φ ^ n, Subgroup.pow_mem (ggAutomizer (⊤ : Subgroup (MulAut L)) A) hφ n, hp⟩

private noncomputable def gammaAHom (ι : ↥A →* UTorus.Proj F m)
    (hιinj : Function.Injective ι) :
    ↥(GammaA ι) →* ggAutomizer (⊤ : Subgroup (MulAut L)) A where
  toFun γ := ⟨Classical.choose γ.2, (Classical.choose_spec γ.2).1⟩
  map_one' := Subtype.ext (gives_unique hιinj
    (Classical.choose_spec (1 : ↥(GammaA ι)).2).2 (gives_one ι))
  map_mul' γ δ := Subtype.ext (gives_unique hιinj
    (Classical.choose_spec (γ * δ).2).2
    (gives_mul (Classical.choose_spec γ.2).2 (Classical.choose_spec δ.2).2))

end AutomizerBound

theorem P9_U8a_card_dvd (h : UnitaryFieldData 2 1 F) (hm : 4 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥A →* UTorus.Proj F m) (hιinj : Function.Injective ι)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t)
    (hinner : UTorus.inner F m ≤ ι.range) :
    Nat.card (ggAutomizer (⊤ : Subgroup (MulAut L)) A) ∣ 2 * m.factorial := by
  have hsurj : Function.Surjective (gammaAHom (A := A) ι hιinj) := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨β, -, hβN, hβeq⟩ := (mem_ggAutomizer_iff (H := ⊤) (Bs := A)).mp hψ
    have hβ : ψ = ggConjAut A hβN := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [hβeq b, ggConjAut_apply]
    obtain ⟨σ, e, hσe⟩ := P9_U8a_exists_perm_zpow h hm hφs hφker hdiag ι hι hinner hβN
    have hmem : ((σ, e) : Equiv.Perm (Fin m) × ℤˣ) ∈ GammaA (A := A) ι :=
      ⟨ggConjAut A hβN, ggConjAut_mem_ggAutomizer (Subgroup.mem_top β) hβN, hσe⟩
    refine ⟨⟨(σ, e), hmem⟩, ?_⟩
    refine Subtype.ext ?_
    show Classical.choose hmem = ψ
    exact (gives_unique hιinj (Classical.choose_spec hmem).2 hσe).trans hβ.symm
  have h1 : Nat.card (ggAutomizer (⊤ : Subgroup (MulAut L)) A) ∣
      Nat.card ↥(GammaA (A := A) ι) :=
    Subgroup.card_dvd_of_surjective hsurj
  have h2 : Nat.card ↥(GammaA (A := A) ι) ∣
      Nat.card (Equiv.Perm (Fin m) × ℤˣ) :=
    Subgroup.card_subgroup_dvd_card _
  have hΓ : Nat.card (Equiv.Perm (Fin m) × ℤˣ) = m.factorial * 2 := by
    rw [Nat.card_prod, Nat.card_perm, Nat.card_fin, Nat.card_eq_fintype_card,
      Fintype.card_units_int]
  have h3 := dvd_trans h1 h2
  rw [hΓ] at h3
  rw [Nat.mul_comm m.factorial 2] at h3
  exact h3

theorem P9_U_dim_and_card_dvd
    [Finite L] [Finite F] (hF : Nat.card F = 4) {r : ℕ}
    (hm : 5 ≤ m) (hm6 : m ≠ 6) (hmr : m ≤ r + 3)
    {ψ : L →* LargeEvenProj (unitarySU 2 1 F m)} {A : Subgroup (MulAut L)}
    (hTB : GGTorusTBGroup 3 r (LargeEvenProj (unitarySU 2 1 F m))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 F m))
        (LargeEvenGUSet (Fin m) F (2 ^ 1))) L ψ A)
    (hAr : Nat.card A = 3 ^ r) :
    (m = r + 1 ∨ (3 ∣ m ∧ m = r + 2)) ∧
      Nat.card (ggAutomizer (⊤ : Subgroup (MulAut L)) A) ∣ 2 * m.factorial := by
  obtain ⟨hψ, hker, hperf, hA, hAI, hrA, -, hSC⟩ := hTB
  obtain ⟨φ, hφs, hφker, hdiag⟩ :=
    P9_U3a_exists_diagModel_of_card hF hm hm6 hmr hψ hker hperf hA hAI hrA
  have h : UnitaryFieldData 2 1 F := ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
  obtain ⟨ι, hιinj, hι⟩ := P9_U6a_exists_coord h (by omega) hφs hφker hdiag
  have hinner : UTorus.inner F m ≤ ι.range := P9_U6a_inner_le_range h hdiag hSC ι hι
  exact ⟨P9_U6a_dim_eq h (by omega) ι hιinj hinner hAr,
    P9_U8a_card_dvd h (by omega) hφs hφker hdiag ι hιinj hι hinner⟩

end CFSG.StandardType.FrameRoute

end
