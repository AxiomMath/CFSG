module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoFusionCount

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExcTwoFusion

namespace TableBExcTwoTB

section WeylImage

variable
  {τ : Tag}

@[expose] noncomputable def weylImageHom {K : Type} [Field K] {S : Subgroup (WeylGroup τ)}
    (E : Subgroup (adjointGroup τ K)) (hEX : E ≤ weylX τ K S) : E →* WeylGroup τ :=
  (weylQuotientHom τ K).comp
    (((adjointGroup τ K).subtype.comp E.subtype).codRestrict _
      (fun e => (mem_weylX.mp (hEX e.2)).1))

theorem weylImage_spec {K : Type} [Field K] [Finite K] {p : ℕ} [NeZero p] (hp : p.Prime)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod p))
    (hV : Nat.card (torusPow τ K p) = p ^ τ.rank) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1)
    {S : Subgroup (WeylGroup τ)} {E : Subgroup (adjointGroup τ K)} (hE : IsElemAbelian p E)
    (hEX : E ≤ weylX τ K S) :
    (weylImageHom E hEX).range ≤ S ∧ IsElemAbelian p (weylImageHom E hEX).range ∧
      Nat.card E = Nat.card (weylImageHom E hEX).range * Nat.card (torusSet hζ E) ∧
      (∀ x ∈ torusSet hζ E, ∀ a ∈ (weylImageHom E hEX).range, torusAct τ p a x = x) ∧
      (∀ e : E, weylImageHom E hEX e = 1 → (e : adjointGroup τ K) ∈ torusPow τ K p) := by
  have := Fact.mk hp
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  have hφinj := chevTorus_injective hζo hζ hdet
  have hφrange := range_chevTorus_eq_torusPow hζo hζ hdet hV
  obtain ⟨-, hker⟩ := weylQuotientHom_surjective_ker (τ := τ) (K := K)
  have hEM : ∀ e : E, ((e : adjointGroup τ K) : ModGL τ K) ∈ monomialSubgroup τ K :=
    fun e => (mem_weylX.mp (hEX e.2)).1
  let ι : E →* monomialSubgroup τ K :=
    ((adjointGroup τ K).subtype.comp E.subtype).codRestrict _ hEM
  have hψS : ∀ e : E, weylImageHom E hEX e ∈ S := fun e => (mem_weylX.mp (hEX e.2)).2
  have hkerH : ∀ e : E, weylImageHom E hEX e = 1 →
      ((e : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K := by
    intro e he
    have h1 : ι e ∈ (weylQuotientHom τ K).ker := he
    rw [hker, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hkerV : ∀ e : E, weylImageHom E hEX e = 1 → (e : adjointGroup τ K) ∈ torusPow τ K p :=
    fun e he => ⟨hkerH e he, hE.2 _ e.2⟩
  have hψ1 : ∀ e : E, ((e : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K →
      weylImageHom E hEX e = 1 := by
    intro e he
    have h1 : ι e ∈ (weylQuotientHom τ K).ker := by
      rw [hker, Subgroup.mem_subgroupOf]
      exact he
    exact h1
  have hfix : ∀ (e₀ : E) (ω : List (Fin τ.rank)),
      weylImageHom E hEX e₀ = (coxeterSystem τ).wordProd ω →
      ∀ e : E, weylImageHom E hEX e = 1 → ∃ x : Fin τ.rank → ZMod p,
        chevTorus τ ζ hζ (.ofAdd x) = (e : adjointGroup τ K) ∧ torusWord τ p ω x = x := by
    intro e₀ ω hω e he
    obtain ⟨x, hx⟩ : (e : adjointGroup τ K) ∈ (chevTorus τ ζ hζ).range := hφrange ▸ hkerV e he
    refine ⟨Multiplicative.toAdd x, by rw [ofAdd_toAdd]; exact hx, ?_⟩
    set n := nWord τ K ω with hn
    have hm := coe_nWord_mem_monomialSubgroup (K := K) ω
    have hρ : weylQuotientHom τ K (ι e₀ * (⟨_, hm⟩ : monomialSubgroup τ K)⁻¹) = 1 := by
      rw [map_mul, map_inv, weylQuotientHom_nWord]
      change weylImageHom E hEX e₀ * _ = 1
      rw [hω, mul_inv_cancel]
    have hh : (((e₀ : adjointGroup τ K) * n⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
        torusGroup τ K := by
      have h1 : ι e₀ * (⟨_, hm⟩ : monomialSubgroup τ K)⁻¹ ∈ (weylQuotientHom τ K).ker := hρ
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hc0 : (e₀ : adjointGroup τ K) * e = e * e₀ := TableB.IsElemAbelian.comm hE e₀.2 e.2
    have hch : ((e₀ : adjointGroup τ K) * n⁻¹) * e = e * ((e₀ : adjointGroup τ K) * n⁻¹) :=
      Subtype.ext (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
        (torusGroup_le_diagonalGroup (hkerH e he)))
    have hne : n * (e : adjointGroup τ K) * n⁻¹ = e := by
      set h := (e₀ : adjointGroup τ K) * n⁻¹ with hhdef
      have hn' : n = h⁻¹ * e₀ := by
        rw [hhdef]
        group
      have hc0' : (e₀ : adjointGroup τ K) * e * (e₀ : adjointGroup τ K)⁻¹ = e := by
        rw [hc0]
        group
      have hch' : h⁻¹ * (e : adjointGroup τ K) * h = e := by
        rw [mul_assoc, ← hch]
        group
      rw [hn', mul_inv_rev, inv_inv]
      calc h⁻¹ * (e₀ : adjointGroup τ K) * e * ((e₀ : adjointGroup τ K)⁻¹ * h) =
          h⁻¹ * ((e₀ : adjointGroup τ K) * e * (e₀ : adjointGroup τ K)⁻¹) * h := by group
        _ = h⁻¹ * e * h := by rw [hc0']
        _ = e := hch'
    have hconj := nWord_conj_chevTorus hζ ω (Multiplicative.toAdd x)
    rw [ofAdd_toAdd, hx, hne] at hconj
    exact congrArg Multiplicative.toAdd (hφinj (hconj.symm.trans hx.symm))
  refine ⟨?_, ?_, ?_, ?_, hkerV⟩
  · rintro _ ⟨e, rfl⟩
    exact hψS e
  · have hcommE : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
    have hpowE : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (by simpa using hE.2 _ a.2)
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show weylImageHom E hEX a * weylImageHom E hEX b =
        weylImageHom E hEX b * weylImageHom E hEX a
      rw [← map_mul, ← map_mul, hcommE]
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow, hpowE, map_one]
  ·
    have hcardE := TableB.card_range_mul_card_ker (weylImageHom E hEX)
    let f : torusSet hζ E → (weylImageHom E hEX).ker := fun x =>
      ⟨⟨chevTorus τ ζ hζ (.ofAdd x.1), x.2⟩, hψ1 _ (coe_chevTorus_mem_torusGroup hζ _)⟩
    have hf : Function.Bijective f := by
      refine ⟨fun x y hxy => ?_, fun e => ?_⟩
      · have h1 := congrArg (fun z : (weylImageHom E hEX).ker => ((z : E) : adjointGroup τ K)) hxy
        exact Subtype.ext (Multiplicative.ofAdd.injective (hφinj h1))
      · obtain ⟨x, hx⟩ : ((e : E) : adjointGroup τ K) ∈ (chevTorus τ ζ hζ).range :=
          hφrange ▸ hkerV e e.2
        have hxE : Multiplicative.toAdd x ∈ torusSet hζ E := by
          rw [mem_torusSet, ofAdd_toAdd, hx]
          exact (e : E).2
        refine ⟨⟨_, hxE⟩, Subtype.ext (Subtype.ext ?_)⟩
        show chevTorus τ ζ hζ (.ofAdd (Multiplicative.toAdd x)) = _
        rw [ofAdd_toAdd, hx]
    rw [← hcardE, Nat.card_congr (Equiv.ofBijective f hf)]
  · rintro x hx _ ⟨e₀, rfl⟩
    obtain ⟨ω, hω⟩ := (coxeterSystem τ).wordProd_surjective (weylImageHom E hEX e₀)
    have he : weylImageHom E hEX ⟨chevTorus τ ζ hζ (.ofAdd x), hx⟩ = 1 :=
      hψ1 _ (coe_chevTorus_mem_torusGroup hζ _)
    obtain ⟨y, hy, hy'⟩ := hfix e₀ ω hω.symm ⟨_, hx⟩ he
    have hxy : y = x := Multiplicative.ofAdd.injective (hφinj hy)
    rw [← hω, ← torusWord_eq_torusAct hsymm, ← hxy]
    exact hy'

end WeylImage

end TableBExcTwoTB

end CFSG.StandardType

end
