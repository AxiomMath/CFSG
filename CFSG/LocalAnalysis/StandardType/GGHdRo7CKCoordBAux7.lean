module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBAux6

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
open Polynomial Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_zeta_ne_one {G : Type} [Group G] {Bs K : Subgroup G}
    (n : ℕ) (hn : 0 < n) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    (hmem : ∀ f : Fin (n + 1) → Multiplicative (ZMod 3), (τ f : G) ∈ K ↔ f 0 = 1)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L]
    {ζ : L} {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hE : E = (Bs ⊓ K).comap φ) :
    ζ ≠ 1 := by
  intro hz1
  let i1 : Fin n := ⟨0, hn⟩
  let f1 : Fin (n + 1) → Multiplicative (ZMod 3) :=
    Pi.mulSingle (Fin.succ i1) (Multiplicative.ofAdd 1)
  have hf1_0 : f1 0 = 1 := by
    simp [f1, Pi.mulSingle_apply, Fin.succ_ne_zero]
  have hf1_ne : f1 ≠ 1 := by
    intro h
    have := congrFun h (Fin.succ i1)
    simp [f1, Pi.mulSingle_eq_same] at this
  have hb1K : (τ f1 : G) ∈ K := (hmem f1).mpr hf1_0
  have hb1 : (τ f1 : G) ∈ Bs ⊓ K := ⟨(τ f1).2, hb1K⟩
  have hb1_ne : (τ f1 : ↥Bs) ≠ 1 := fun h => hf1_ne (τ.injective (by rw [h, map_one]))
  obtain ⟨x, hxφ⟩ : ∃ x, φ x = (τ f1 : G) := by
    have : (τ f1 : G) ∈ φ.range := by rw [hrange]; exact hb1K
    exact MonoidHom.mem_range.mp this
  have hxE : x ∈ E := by
    rw [hE, Subgroup.mem_comap, hxφ]; exact hb1
  obtain ⟨c', hc'⟩ := F.mem_tor x hxE
  have hx1 : x = 1 := by
    rw [← hc']
    apply ChoiceTwo.eq_of_spEnd_eq'
    intro v
    rw [← F.Φ.apply_symm_apply v, F.tor_acts c']
    have hid : ChoiceTwo.torE ζ c' (F.Φ.symm v) = F.Φ.symm v := by
      funext j; simp [ChoiceTwo.torE_apply, hz1]
    rw [hid, F.Φ.apply_symm_apply, ChoiceTwo.spEnd_one_apply]
  have hτ1 : (τ f1 : G) = 1 := by rw [← hxφ, hx1, map_one]
  exact hb1_ne (Subtype.ext hτ1)

def hdRo7CKCoordAux_hyperEquiv (p n : ℕ) :
    (Fin n → Multiplicative (ZMod p)) ≃
      {f : Fin (n + 1) → Multiplicative (ZMod p) // f 0 = 1} where
  toFun u := ⟨Fin.cases 1 u, by simp [Fin.cases_zero]⟩
  invFun f := fun k => f.1 (Fin.succ k)
  left_inv u := by funext k; simp [Fin.cases_succ]
  right_inv f := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => simp [Fin.cases_zero, f.2]
    | succ k => simp [Fin.cases_succ]

theorem hdRo7CKCoordAux_card_E {G : Type} [Group G] {Bs K : Subgroup G}
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    (hmem : ∀ f : Fin (n + 1) → Multiplicative (ZMod 3), (τ f : G) ∈ K ↔ f 0 = 1)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K)
    {E : Subgroup (StatedSp m (GaloisField 2 1))} (hE : E = (Bs ⊓ K).comap φ) :
    Nat.card E = 3 ^ n := by
  have hle : Bs ⊓ K ≤ φ.range := by rw [hrange]; exact inf_le_right
  have hmap : E.map φ = Bs ⊓ K := by
    rw [hE, Subgroup.map_comap_eq_self hle]
  have hcardE : Nat.card E = Nat.card ↥(Bs ⊓ K) := by
    rw [← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective E φ hinj).toEquiv
  have hcardH : Nat.card ↥(Bs ⊓ K) =
      Nat.card {f : Fin (n + 1) → Multiplicative (ZMod 3) // f 0 = 1} := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun b => ⟨τ.symm ⟨b.1, b.2.1⟩, (hmem (τ.symm ⟨b.1, b.2.1⟩)).mp (by rw [MulEquiv.apply_symm_apply]; exact b.2.2)⟩
        invFun := fun f => ⟨(τ f.1 : G), (τ f.1).2, (hmem f.1).mpr f.2⟩
        left_inv := fun b => by apply Subtype.ext; simp
        right_inv := fun f => by apply Subtype.ext; simp }
  rw [hcardE, hcardH, ← Nat.card_congr (hdRo7CKCoordAux_hyperEquiv 3 n)]
  simp [Nat.card_pi, ZMod.card, Finset.prod_const, Fintype.card_fin]

theorem hdRo7CKCoordAux_s_eq {G : Type} [Group G] {Bs K : Subgroup G}
    (n : ℕ) (hn : 0 < n) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    (hmem : ∀ f : Fin (n + 1) → Multiplicative (ZMod 3), (τ f : G) ∈ K ↔ f 0 = 1)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    (hrange : φ.range = K)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L]
    {ζ : L} {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hE : E = (Bs ⊓ K).comap φ) (hsupp : (F.suppSet c).card = 2) :
    F.s = n := by
  have hζ3 : ζ ^ 3 = 1 := hdRo7CKCoordAux_zeta_cube n τ φ hinj F c hE hsupp
  have hζne : ζ ≠ 1 := hdRo7CKCoordAux_zeta_ne_one n hn τ hmem φ hinj hrange F c hE
  have hζ : IsPrimitiveRoot ζ 3 := by
    rw [IsPrimitiveRoot.iff_orderOf]
    exact orderOf_eq_prime hζ3 hζne
  have htormem : ∀ f : Fin F.s → ZMod 3, F.tor f ∈ E := F.tor_mem
  have hcardE : Nat.card E = 3 ^ F.s := by
    have hbij : Function.Bijective
        (fun f : Fin F.s → ZMod 3 => (⟨F.tor f, F.tor_mem f⟩ : ↥E)) :=
      ⟨fun a b h => hdRo7CKCoordAux_tor_injective F hζ (Subtype.ext_iff.mp h),
        fun x => by
          obtain ⟨f, hf⟩ := F.mem_tor x.1 x.2
          exact ⟨f, Subtype.ext hf⟩⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
    simp [Nat.card_pi, ZMod.card, Finset.prod_const, Fintype.card_fin]
  have h3n : Nat.card E = 3 ^ n := hdRo7CKCoordAux_card_E n τ hmem φ hinj hrange hE
  have hpow : 3 ^ F.s = 3 ^ n := by rw [← hcardE, h3n]
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3)) hpow

end CFSG.StandardType.HdRo7C

end
