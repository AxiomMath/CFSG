module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBToralAux
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBWeylImage
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  TableBExc TableBExcTwoFusion CFSG.HardMathSupport.Timmesfeld.CrossChar

namespace TableBExcTwoTB

section Generic

private theorem conj_mul_zpow_eq_of_comm {G : Type*} [Group G] (g a n : G) (h : g * a = a * g)
    (k : ℤ) : g * (a * n ^ k) * g⁻¹ = a * (g * n * g⁻¹) ^ k := by
  have hgag : g * a * g⁻¹ = a := by rw [h]; group
  calc g * (a * n ^ k) * g⁻¹ = (g * a * g⁻¹) * (g * n ^ k * g⁻¹) := by group
    _ = a * (g * n ^ k * g⁻¹) := by rw [hgag]
    _ = a * (g * n * g⁻¹) ^ k := by rw [conj_zpow]

end Generic

section Heart

variable
  {τ : Tag}

theorem exists_conj_toral_of_le_weylX {K₂ L : Type} [Field K₂] [Finite K₂] [Field L] [IsAlgClosed L]
    (hmon : MonomialToralAt τ 3) (hL : ringChar L ≠ 3) (ψ₂ : K₂ →+* L)
    (hdet : IsUnit ((τ.cartan.det : ℤ) : ZMod 3)) (hsymm : ∀ i j, τ.cartan i j = τ.cartan j i)
    (hV : Nat.card (torusPow τ K₂ 3) = 3 ^ τ.rank) (h3 : 3 ∣ Nat.card K₂ - 1)
    {S : Subgroup (WeylGroup τ)} (hhalf : HalfOffender τ S)
    {E : Subgroup (adjointGroup τ K₂)} (hE : IsElemAbelian 3 E) (hEX : E ≤ weylX τ K₂ S)
    (hcard : 3 ^ (τ.rank - 1) ≤ Nat.card E) :
    ∃ h ∈ adjointGroup τ L, ∀ e ∈ E,
      h * baseChangeGL ψ₂ ((e : adjointGroup τ K₂) : ModGL τ K₂) * h⁻¹ ∈ torusGroup τ L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K₂) (p := 3) h3
  have hζ : ζ ^ 3 = 1 := by rw [← hζo]; exact pow_orderOf_eq_one ζ
  have hrange : (chevTorus τ ζ hζ).range = torusPow τ K₂ 3 :=
    range_chevTorus_eq_torusPow hζo hζ hdet hV
  obtain ⟨hAS, hA, hcardE, hfixV, hkerV⟩ :=
    weylImage_spec (K := K₂) (p := 3) (ζ := ζ) (S := S) (E := E)
      Nat.prime_three hdet hV hsymm hζo hζ hE hEX
  let ψ : E →* WeylGroup τ := weylImageHom E hEX
  let A : Subgroup (WeylGroup τ) := ψ.range
  have hAS' : A ≤ S := hAS
  have hA' : IsElemAbelian 3 A := hA
  have hcardE' : Nat.card E = Nat.card A * Nat.card (torusSet hζ E) := hcardE
  by_cases hAbot : A = ⊥
  · refine ⟨1, one_mem _, ?_⟩
    intro e he
    have hψe : ψ ⟨e, he⟩ = 1 := by
      have hmem : ψ ⟨e, he⟩ ∈ A := ⟨⟨e, he⟩, rfl⟩
      rw [hAbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hpow : (e : adjointGroup τ K₂) ∈ torusPow τ K₂ 3 := hkerV ⟨e, he⟩ hψe
    have htorus : ((e : adjointGroup τ K₂) : ModGL τ K₂) ∈ torusGroup τ K₂ :=
      (mem_torusPow.mp hpow).1
    have := CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup (τ := τ) ψ₂ htorus
    simpa using this
  · set C : Set (Fin τ.rank → ZMod 3) :=
      {x | ∀ a ∈ A, torusAct τ 3 a x = x} with hC
    set X : Set (Fin τ.rank → ZMod 3) :=
      (torusSet hζ E : Set (Fin τ.rank → ZMod 3)) with hX
    have hXC : X ⊆ C := fun x hx a ha => hfixV x hx a ha
    have hle_card : Nat.card (torusSet hζ E) ≤
        Nat.card {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} := by
      let ι : torusSet hζ E →
          {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} :=
        fun x => ⟨x.1, fun a ha => hfixV x.1 x.2 a ha⟩
      exact Nat.card_le_card_of_injective ι
        (fun x y hxy => Subtype.ext (congrArg (fun z => z.1) hxy))
    have hcount : 3 ^ (τ.rank - 1) ≤ Nat.card A *
        Nat.card {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} :=
      calc 3 ^ (τ.rank - 1) ≤ Nat.card E := hcard
        _ = Nat.card A * Nat.card (torusSet hζ E) := hcardE'
        _ ≤ Nat.card A * Nat.card
              {x : Fin τ.rank → ZMod 3 // ∀ a ∈ A, torusAct τ 3 a x = x} :=
            Nat.mul_le_mul_left _ hle_card
    obtain ⟨w, hAw, hwcl⟩ := hhalf A hAS' hA' hAbot hcount
    have hwA : w ∈ A := by rw [hAw]; exact Subgroup.mem_zpowers w
    have hw3 : w ^ 3 = 1 := hA'.2 w hwA
    have hwr : w ∈ ψ.range := hwA
    obtain ⟨n₀, hn₀⟩ := hwr
    have hwK : w ∈ kernelWeylGroup (pairChar τ X) :=
      mem_kernelWeylGroup_pairChar (X := X) (C := C) hXC hwcl
    let m : ModGL τ K₂ := ((n₀ : adjointGroup τ K₂) : ModGL τ K₂)
    have hm : m ∈ monomialSubgroup τ K₂ := (mem_weylX.mp (hEX n₀.2)).1
    let n : ModGL τ L := baseChangeGL ψ₂ m
    have hn : n ∈ monomialSubgroup τ L := baseChangeGL_mem_monomialSubgroup ψ₂ hm
    have hq : weylQuotientHom τ L ⟨n, hn⟩ = w := by
      have h1 := weylQuotientHom_baseChangeGL (τ := τ) (K₂ := K₂) (L := L) ψ₂ hm
      have h2 : weylQuotientHom τ K₂ ⟨m, hm⟩ = w := hn₀
      exact h1.trans h2
    obtain ⟨g, hgroot, hgn⟩ := hmon L hL (Multiplicative (X → ZMod 3)) (pairChar τ X) n hn
      (by rw [hq]; exact hwK) (by rw [hq]; exact hw3)
    refine ⟨g, rootSpan_le_adjointGroup L _ hgroot, ?_⟩
    intro e he
    have hψe_mem : ψ ⟨e, he⟩ ∈ A := ⟨⟨e, he⟩, rfl⟩
    have hz : ψ ⟨e, he⟩ ∈ Subgroup.zpowers w := by
      rw [← hAw]; exact hψe_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    let t : E := ⟨e, he⟩ * (n₀ ^ k)⁻¹
    have hψt : ψ t = 1 := by
      change ψ (⟨e, he⟩ * (n₀ ^ k)⁻¹) = 1
      rw [map_mul, map_inv, map_zpow, ← hk, hn₀]
      group
    have htV : (t : adjointGroup τ K₂) ∈ torusPow τ K₂ 3 := hkerV t hψt
    have htR : (t : adjointGroup τ K₂) ∈ (chevTorus τ ζ hζ).range := by
      rw [hrange]; exact htV
    have htG : baseChangeGL ψ₂ ((t : adjointGroup τ K₂) : ModGL τ K₂) ∈ torusGroup τ L :=
      CFSG.RankThree.Classical2.baseChangeGL_mem_torusGroup ψ₂ (mem_torusPow.mp htV).1
    have hcomm := mul_comm_baseChangeGL_of_mem_rootSpan (τ := τ) (K₂ := K₂) (L := L)
      ψ₂ (ζ := ζ) hζ (E := E) (g := g) hgroot t.2 htR
    have het : (⟨e, he⟩ : E) = t * n₀ ^ k := by
      rw [show t = ⟨e, he⟩ * (n₀ ^ k)⁻¹ from rfl]
      group
    have het' : ((e : adjointGroup τ K₂) : ModGL τ K₂) =
        ((t : adjointGroup τ K₂) : ModGL τ K₂) *
          (((n₀ : E) : adjointGroup τ K₂) : ModGL τ K₂) ^ k := by
      have h := congrArg (fun x : E => ((x : adjointGroup τ K₂) : ModGL τ K₂)) het
      simpa using h
    have hbase : baseChangeGL ψ₂ ((e : adjointGroup τ K₂) : ModGL τ K₂) =
        baseChangeGL ψ₂ ((t : adjointGroup τ K₂) : ModGL τ K₂) * n ^ k := by
      have h := congrArg (baseChangeGL ψ₂) het'
      simpa [n] using h
    have hconj : g * (baseChangeGL ψ₂ ((t : adjointGroup τ K₂) : ModGL τ K₂) * n ^ k) * g⁻¹ =
        baseChangeGL ψ₂ ((t : adjointGroup τ K₂) : ModGL τ K₂) * (g * n * g⁻¹) ^ k :=
      conj_mul_zpow_eq_of_comm g _ n hcomm k
    rw [hbase, hconj]
    exact mul_mem htG (zpow_mem hgn k)

end Heart

end TableBExcTwoTB

end CFSG.StandardType

end
