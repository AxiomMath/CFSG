module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflSp

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp SpCoord

theorem ggTBJ_sp_stdModel {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {K : Type} [Field K]
    [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1) {L' : Type} [Group L'] [Finite L']
    (ψ₀ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) L' ψ₀ A) :
    ∃ (ζ : Kˣ) (hζ : ζ ^ p = 1) (x : LargeEvenProj (LargeEvenSpGroup K m))
      (σ : (Fin m → Multiplicative (ZMod p)) →* L')
      (Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A),
      orderOf ζ = p ∧ (∀ f, ψ₀ (σ f) = x * spTorus hζ f * x⁻¹) ∧
      (∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f)) ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) := by
  classical
  obtain ⟨hψ0, hker0, hperf0, hAe0, hAI0, hr0, h3_0, -⟩ := hA
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo⟩ := ReflSp.exists_orderOf_eq (K := K) hp hpq
  have hζ : ζ ^ p = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥ :=
    TableBSymp.center_spProj_eq_bot (K := K) (m := m)
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : LargeEvenProj (LargeEvenSpGroup K m) →* MulAut L',
      (∀ {e : LargeEvenProj (LargeEvenSpGroup K m)} {x : L'}, ψ₀ x = e → Λ e = MulAut.conj x) ∧
      Function.Injective Λ ∧
      (∀ e l, ψ₀ (Λ e l) = e * ψ₀ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ₀ hψ0 hker0, fun hx => ReflInner.liftConj_eq hψ0 hker0 hx,
      ReflInner.liftConj_injective hψ0 hker0 hZ, ReflInner.map_liftConj_apply hψ0 hker0⟩
  have hΛn : ∀ n : L', Λ (ψ₀ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI0 a ha
    obtain ⟨e, rfl⟩ := hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ₀ hker0 hperf0 fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hAe0 e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hAe0.2 _ he
  obtain ⟨x, hτE, hEτ⟩ := ReflSp.exists_conj_spTorus hp hp2 hζo hζ hEab (hcardE ▸ hr0)
  set τ : (Fin m → Multiplicative (ZMod p)) →* LargeEvenProj (LargeEvenSpGroup K m) :=
    (MulAut.conj x).toMonoidHom.comp (spTorus hζ) with hτ
  have hτapp : ∀ f, τ f = x * spTorus hζ f * x⁻¹ := fun f => rfl
  have hτinj : Function.Injective τ :=
    (MulAut.conj x).injective.comp (spTorus_injective hζ hζo (hp.odd_of_ne_two hp2))
  have hτrange : τ.range = E := by
    ext e
    constructor
    · rintro ⟨f, rfl⟩
      exact hτE f
    · intro he
      obtain ⟨f, hf⟩ := hEτ e he
      exact ⟨f, hf⟩
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτrange ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : (Fin m → Multiplicative (ZMod p)) →* ↥A := (Λ.comp τ).codRestrict A hτmem with hΘ₀
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτrange] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : (Fin m → Multiplicative (ZMod p)) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij with hΘ
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  have hconjτ : ∀ (s : LargeEvenProj (LargeEvenSpGroup K m))
      (α : (Fin m → Multiplicative (ZMod p)) → (Fin m → Multiplicative (ZMod p))),
      (∀ f, s * spTorus hζ f * s⁻¹ = spTorus hζ (α f)) →
      ∀ f, (x * s * x⁻¹) * τ f * (x * s * x⁻¹)⁻¹ = τ (α f) := by
    intro s α hs f
    rw [hτapp, hτapp, ← hs f]
    group
  have hsgn : ∀ i : Fin m, ∃ w : LargeEvenProj (LargeEvenSpGroup K m),
      ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f) := fun i =>
    ⟨x * LargeEvenProjMk _ (spSwapSp i) * x⁻¹,
      hconjτ _ (sgnAut i) fun f => spSwap_conj_spTorus hζ i f⟩
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ0 hker0 (hp.odd_of_ne_two hp2) τ
    fun i j => by
      obtain ⟨w, hw⟩ := hsgn i
      refine ⟨w, ?_, fun hji => ?_⟩
      · rw [TableBSymp.torusBasis, hw, sgnAut_mulSingle_self, map_inv]
      · rw [TableBSymp.torusBasis, hw, sgnAut_mulSingle_of_ne hji]
  have hψσ : ∀ f, ψ₀ (σ f) = τ f := fun f => by rw [← MonoidHom.comp_apply, hσ]
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hNE : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ f, ∃ f', ψ₀ n * τ f * (ψ₀ n)⁻¹ = τ f' := by
    intro n hn f
    have h1 : Λ (ψ₀ n * τ f * (ψ₀ n)⁻¹) ∈ A := by
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hτmem f)
    have h2 : ψ₀ n * τ f * (ψ₀ n)⁻¹ ∈ τ.range := hτrange ▸ h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f', hf'.symm⟩
  refine ⟨ζ, hζ, x, σ, Θ, hζo, fun f => (hψσ f).trans (hτapp f), hΘσ, fun n hn => ?_⟩
  have hform : ∀ f, ∃ g, ∃ z ∈ ψ₀.ker, z ^ p = 1 ∧
      n * (MulAut.conj (σ f) n)⁻¹ = σ g * z := by
    intro f
    obtain ⟨f', hf'⟩ := hNE n hn f
    set z := (σ f')⁻¹ * (n * σ f * n⁻¹) with hz
    have hzk : z ∈ ψ₀.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, hψσ, hψσ, hf',
        inv_mul_cancel]
    have hzc := Subgroup.mem_center_iff.mp (hker0 hzk)
    have hzp : z ^ p = 1 := by
      have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
        rw [conj_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel]
      have h2 : n * σ f * n⁻¹ = σ f' * z := by rw [hz, mul_inv_cancel_left]
      rw [h2, (show Commute (σ f') z from hzc (σ f')).mul_pow, ← map_pow,
        ReflInner.pow_eq_one_of_zmod, map_one, one_mul] at h1
      exact h1
    refine ⟨f' * f⁻¹, z, hzk, hzp, ?_⟩
    rw [MulAut.conj_apply, map_mul, map_inv, mul_assoc (σ f'), hzc (σ f)⁻¹, hz]
    group
  intro a ha
  obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
  have haσ : a = MulAut.conj (σ f) := by
    rw [← hΘσ, hf]
  obtain ⟨g, z, hzk, hzp, he⟩ := hform f
  have hzc := Subgroup.mem_center_iff.mp (hker0 hzk)
  rw [haσ, he]
  refine ⟨?_, fun a' ha' => ?_⟩
  · rw [(show Commute (σ g) z from hzc (σ g)).mul_pow, ← map_pow,
      ReflInner.pow_eq_one_of_zmod, map_one, one_mul, hzp]
  · obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
    have ha'σ : a' = MulAut.conj (σ f'') := by
      rw [← hΘσ, hf'']
    rw [ha'σ, MulAut.conj_apply]
    calc σ f'' * (σ g * z) * (σ f'')⁻¹ = σ g * (σ f'' * z) * (σ f'')⁻¹ := by
          rw [← mul_assoc, hσc]; group
      _ = σ g * (z * σ f'') * (σ f'')⁻¹ := by rw [hzc]
      _ = σ g * z := by group

end CFSG.StandardType

end
