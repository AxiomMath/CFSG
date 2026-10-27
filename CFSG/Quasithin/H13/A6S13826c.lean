module

public import CFSG.Quasithin.H13.A6S13826a
public import CFSG.Quasithin.H13.A6S13826b

public section

namespace CFSG.Quasithin.H13.A6

open Equiv Equiv.Perm CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B42Alt6
open CFSG.Quasithin.H13.A6Coc
open scoped Pointwise

namespace A6Hm

variable {Y : Type} [CommGroup Y]

theorem isIrr_smul {A T : Type*} [Group A] [Group T] [MulDistribMulAction A Y]
    [MulDistribMulAction T Y] (h : XMod.Normalizes A T Y) (t : T) {L : Subgroup Y}
    (hL : XMod.IsIrr A L) : XMod.IsIrr A (t • L) := by
  refine ⟨XMod.isInv_smul_of_normalizes h t hL.1, ?_, fun J hJ _ hJL => ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h0
    apply hL.2.1.ne'
    have : t⁻¹ • t • L = t⁻¹ • (⊥ : Subgroup Y) := by rw [h0]
    rwa [inv_smul_smul, Subgroup.smul_bot] at this
  · have hJ' := XMod.isInv_smul_of_normalizes h t⁻¹ hJ
    have hJL' : t⁻¹ • J ≤ L := by
      have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := t⁻¹) |>.2 hJL
      rwa [inv_smul_smul] at this
    rcases hL.2.2 _ hJ' bot_le hJL' with h0 | h1
    · left
      have : t • t⁻¹ • J = t • (⊥ : Subgroup Y) := by rw [h0]
      rwa [smul_inv_smul, Subgroup.smul_bot] at this
    · right
      rw [← h1, smul_inv_smul]

theorem exists_isIrr_le [Finite Y] {A : Type*} [Group A] [MulDistribMulAction A Y]
    {B : Subgroup Y} (hB : XMod.IsInv A B) (hne : B ≠ ⊥) : ∃ S ≤ B, XMod.IsIrr A S := by
  classical
  obtain ⟨S, ⟨hSB, hSinv, hSne⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup Y))
    {J : Subgroup Y | J ≤ B ∧ XMod.IsInv A J ∧ J ≠ ⊥} ⟨B, le_rfl, hB, hne⟩
  refine ⟨S, hSB, hSinv, bot_lt_iff_ne_bot.2 hSne, fun J hJ _ hJS => ?_⟩
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  · right
    by_contra hne'
    exact hmin J ⟨hJS.trans hSB, hJ, hJ0⟩ (lt_of_le_of_ne hJS hne')

theorem isIrr_top_of_homog [Finite Y] (hY : ∀ y : Y, y ^ 2 = 1) {K T : Subgroup (MulAut Y)}
    (hT2 : IsPGroup 2 T) (hTK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hirr : ∀ J : Subgroup Y, (∀ k ∈ K, ∀ y ∈ J, k y ∈ J) → (∀ t ∈ T, ∀ y ∈ J, t y ∈ J) →
      J = ⊥ ∨ J = ⊤)
    (hne : (⊤ : Subgroup Y) ≠ ⊥)
    (hom : ∀ M : Subgroup Y, XMod.IsIrr ↥K M → ∀ t : ↥T, XMod.Iso ↥K (t • M) M) :
    XMod.IsIrr ↥K (⊤ : Subgroup Y) := by
  have hN : XMod.Normalizes ↥K ↥T Y := by
    intro t a
    refine ⟨⟨t * a * t⁻¹, hTK t t.2 a a.2⟩, fun q => ?_⟩
    show (t : MulAut Y) ((a : MulAut Y) q) = (t * a * t⁻¹ : MulAut Y) ((t : MulAut Y) q)
    simp
  obtain ⟨L₀, -, hL₀⟩ := exists_isIrr_le (A := ↥K) (XMod.isInv_top (A := ↥K) (Q := Y)) hne
  obtain ⟨L', -, hL', -, hhom⟩ := XMod.exists_isHomComp_of_isIrr hY hN hT2 hL₀
  have hsmul : ∀ t : ↥T, t • L' ≤ L' := fun t =>
    hhom.2.2 _ (le_iSup (fun t : ↥T => t • L') t) (isIrr_smul hN t hL') (hom L' hL' t)
  have hT : ∀ t ∈ T, ∀ y ∈ L', t y ∈ L' := fun t ht y hy =>
    hsmul ⟨t, ht⟩ (Subgroup.smul_mem_pointwise_smul y (⟨t, ht⟩ : ↥T) L' hy)
  rcases hirr L' (fun k hk y hy => hL'.1 ⟨k, hk⟩ y hy) hT with h0 | h1
  · exact absurd h0 hL'.2.1.ne'
  · rwa [h1] at hL'

theorem iso_smul_of_class [Finite Y] (hY : ∀ y : Y, y * y = 1)
    {K : Subgroup (MulAut Y)} (ιK : ↥K ≃* alternatingGroup (Fin 6)) {M : Subgroup Y}
    (hM : XMod.IsIrr ↥K M) (hMfix : ∀ m ∈ M, (∀ k ∈ K, k m = m) → m = 1)
    (hcard : Nat.card M < 2 ^ 16) {t : MulAut Y} (htK : ∀ k ∈ K, t⁻¹ * k * t ∈ K)
    {c : MulAut Y} (hcK : c ∈ K) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {k₀ : MulAut Y}
    (hk₀ : k₀ ∈ K) (hcc : t⁻¹ * c * t = k₀ * c * k₀⁻¹ ∨ t⁻¹ * c * t = k₀ * c⁻¹ * k₀⁻¹) :
    XMod.Iso ↥K (t • M) M := by
  classical
  have hinv : ∀ k ∈ K, ∀ m ∈ M, k m ∈ M := fun k hk m hm => hM.1 ⟨k, hk⟩ m hm
  have hKs : K ≤ stabSub M := fun k hk u => ⟨fun h => by
      have := hinv k⁻¹ (K.inv_mem hk) _ h
      simpa using this, fun h => hinv k hk u h⟩
  set r : ↥K →* MulAut ↥M := (resHom M).comp (Subgroup.inclusion hKs) with hr
  have hrapp : ∀ (k : ↥K) (m : ↥M), ((r k m : ↥M) : Y) = (k : MulAut Y) m := fun _ _ => rfl
  have hsimp : IsSimpleGroup ↥K := by
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact ιK.isSimpleGroup
  have hMne : M ≠ ⊥ := hM.2.1.ne'
  have hrinj : Function.Injective r := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal r.ker with h | h
    · exact h
    · exfalso
      apply hMne
      rw [eq_bot_iff]
      intro m hm
      refine hMfix m hm fun k hk => ?_
      have h1 : r ⟨k, hk⟩ = 1 := (MonoidHom.mem_ker).1 (h ▸ Subgroup.mem_top _)
      have h2 := congrArg (fun φ : MulAut ↥M => ((φ ⟨m, hm⟩ : ↥M) : Y)) h1
      exact h2
  set LM : Subgroup (MulAut ↥M) := r.range with hLM
  let eK : ↥K ≃* ↥LM := MonoidHom.ofInjective hrinj
  have heK : ∀ k : ↥K, ((eK k : ↥LM) : MulAut ↥M) = r k := fun _ => rfl
  let ιM : ↥LM ≃* alternatingGroup (Fin 6) := eK.symm.trans ιK
  have hS : ∀ s : ↥M, s * s = 1 := fun s => Subtype.ext (hY s)
  have hirrM : XMod.IsIrrSec ↥LM (⊥ : Subgroup ↥M) ⊤ := by
    refine ⟨?_, fun J hJ _ _ => ?_⟩
    · rw [bot_lt_iff_ne_bot]
      intro h
      apply hMne
      rw [eq_bot_iff]
      intro m hm
      have : (⟨m, hm⟩ : ↥M) ∈ (⊤ : Subgroup ↥M) := trivial
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
    · have hJ' : XMod.IsInv ↥K (J.map M.subtype) := by
        rintro ⟨k, hk⟩ _ ⟨j, hj, rfl⟩
        refine ⟨r ⟨k, hk⟩ j, hJ ⟨r ⟨k, hk⟩, ⟨⟨k, hk⟩, rfl⟩⟩ j hj, ?_⟩
        rfl
      rcases hM.2.2 _ hJ' bot_le (Subgroup.map_subtype_le J) with h | h
      · left
        rw [eq_bot_iff]
        intro j hj
        have : (j : Y) ∈ J.map M.subtype := ⟨j, hj, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.2 (Subtype.ext this)
      · right
        rw [eq_top_iff]
        intro j _
        have : (j : Y) ∈ J.map M.subtype := by rw [h]; exact j.2
        obtain ⟨j', hj', hjj⟩ := this
        rwa [Subtype.ext hjj] at hj'
  obtain ⟨N⟩ := A6Md.exists_n6Model hS ιM hirrM hcard
  let e₀ : alternatingGroup (Fin 6) ≃* ↥LM :=
    ((alternatingGroup (Fin 6)).equivMapOfInjective N.ρ N.ρ_inj).trans
      (MulEquiv.subgroupCongr N.ρ_alt)
  have he₀ : ∀ γ : alternatingGroup (Fin 6), ((e₀ γ : ↥LM) : MulAut ↥M) = N.ρ γ := fun _ => rfl
  let α : ↥K ≃* alternatingGroup (Fin 6) := eK.trans e₀.symm
  have hα : ∀ k : ↥K, N.ρ (α k) = r k := by
    intro k
    rw [← he₀, ← heK]
    show ((e₀ (e₀.symm (eK k)) : ↥LM) : MulAut ↥M) = _
    rw [MulEquiv.apply_symm_apply]
  let cj : ↥K →* ↥K :=
    { toFun := fun k => ⟨t⁻¹ * k * t, htK k k.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hcj : ∀ k : ↥K, ((cj k : ↥K) : MulAut Y) = t⁻¹ * k * t := fun _ => rfl
  have hcjinj : Function.Injective cj := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    rw [hcj, hcj] at this
    simpa using this
  let ψ : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
    α.toMonoidHom.comp (cj.comp α.symm.toMonoidHom)
  have hψ : ∀ k : ↥K, ψ (α k) = α (cj k) := by
    intro k
    show α (cj (α.symm (α k))) = _
    rw [MulEquiv.symm_apply_apply]
  have hψinj : Function.Injective ψ := by
    intro a b hab
    have h1 : α (cj (α.symm a)) = α (cj (α.symm b)) := hab
    exact α.symm.injective (hcjinj (α.injective h1))
  set c' : ↥K := ⟨c, hcK⟩ with hc'
  set k' : ↥K := ⟨k₀, hk₀⟩ with hk'
  have hx3 : (α c') ^ 3 = 1 := by
    rw [← map_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have hx1 : α c' ≠ 1 := by
    intro h
    apply hc1
    have : c' = 1 := α.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hψx : ∃ g : alternatingGroup (Fin 6),
      ψ (α c') = g * α c' * g⁻¹ ∨ ψ (α c') = g * (α c')⁻¹ * g⁻¹ := by
    refine ⟨α k', ?_⟩
    rw [hψ]
    rcases hcc with h | h
    · left
      have : cj c' = k' * c' * k'⁻¹ := Subtype.ext (by rw [hcj]; exact h)
      rw [this, map_mul, map_mul, map_inv]
    · right
      have : cj c' = k' * c'⁻¹ * k'⁻¹ := Subtype.ext (by rw [hcj]; exact h)
      rw [this, map_mul, map_mul, map_inv, map_inv]
  obtain ⟨σ, hσ⟩ := exists_perm_of_conj hψinj hx3 hx1 hψx
  refine ⟨(XMod.smulEquiv t M).symm.trans (N.ρ σ⁻¹), fun a l l' hll' => ?_⟩
  set m := (XMod.smulEquiv t M).symm l with hm
  set m' := (XMod.smulEquiv t M).symm l' with hm'
  have hl : (l : Y) = t (m : Y) := by
    rw [hm]
    exact (smul_inv_smul t (l : Y)).symm
  have hl' : (l' : Y) = t (m' : Y) := by
    rw [hm']
    exact (smul_inv_smul t (l' : Y)).symm
  have hmm : m' = r (cj a) m := by
    apply Subtype.ext
    rw [hrapp, hcj]
    have h1 : (a : MulAut Y) (t (m : Y)) = t (m' : Y) := by
      rw [← hl, ← hl']
      exact hll'
    show (m' : Y) = t⁻¹ ((a : MulAut Y) (t (m : Y)))
    rw [h1]
    simp
  have hρψ : N.ρ (α (cj a)) = N.ρ σ * N.ρ (α a) * (N.ρ σ)⁻¹ := by
    rw [← hψ, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact hσ (α a)
  show (a : MulAut Y) (((N.ρ σ⁻¹ m : ↥M)) : Y) = ((N.ρ σ⁻¹ m' : ↥M) : Y)
  have hL : (a : MulAut Y) ((N.ρ σ⁻¹ m : ↥M) : Y) = ((N.ρ (α a) (N.ρ σ⁻¹ m) : ↥M) : Y) := by
    rw [hα, hrapp]
  have hR : N.ρ σ⁻¹ m' = N.ρ (α a) (N.ρ σ⁻¹ m) := by
    rw [hmm, ← hα, hρψ, map_inv]
    show ((N.ρ σ)⁻¹ * (N.ρ σ * N.ρ (α a) * (N.ρ σ)⁻¹)) m = (N.ρ (α a) * (N.ρ σ)⁻¹) m
    congr 1
    group
  rw [hL, hR]
