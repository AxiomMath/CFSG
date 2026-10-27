module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeNamed
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeWeylCoordsLin
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeWeylCoordsChain

public section

namespace CFSG.GGQ2Prime

open CFSG.StandardType CFSG.StandardType.TypeAReflOver CFSG.Assembly CFSG.Open

theorem exists_weylCoords_core {G : Type} [Group G] {Bs : Subgroup G} [Finite Bs]
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 6)
    {A AL : Subgroup (MulAut Bs)} (hle : AL ≤ A)
    (hW6 : GGWeylOfType 3 (CoxeterMatrix.A 6) A) (hW5 : GGWeylOfType 3 (CoxeterMatrix.A 5) AL)
    {x : G} (hx : x ∈ Bs) (hx1 : x ≠ 1) (hfixx : ∀ φ ∈ AL, φ ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ (κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))) (m : Fin 7),
      WeylCoords Bs A x κ m := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨V, hVadd, hVmod, ⟨ι⟩⟩ := exists_ggLinData (p := 3) hBs
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod 3) V := hVmod
  haveI : Finite V := Finite.of_equiv _ ι.toEquiv
  have hcardV : Nat.card V = 3 ^ (5 + 1) := by
    rw [← Nat.card_congr ι.toEquiv]
    exact hcard
  obtain ⟨Ehat, hEhat⟩ := exists_permEquiv_of_ggWeylOfType_A hW6
  let E : Equiv.Perm (Fin (5 + 1 + 1)) →* MulAut Bs := A.subtype.comp Ehat.toMonoidHom
  have hEapp : ∀ π, E π = (Ehat π : MulAut Bs) := fun π => rfl
  have hEinj : Function.Injective E := Subtype.val_injective.comp Ehat.injective
  have hEmem : ∀ π, E π ∈ A := fun π => (Ehat π).2
  have hErange : AL ≤ E.range := fun φ hφ => by
    refine ⟨Ehat.symm ⟨φ, hle hφ⟩, ?_⟩
    rw [hEapp, MulEquiv.apply_symm_apply]
  have hsw : ∀ a b, a ≠ b → GGIsReflection 3 (E (Equiv.swap a b)) := fun a b hab =>
    ggIsReflection_swap_of_swap E (Fin.castSucc_lt_succ (i := (0 : Fin 6))).ne (hEhat 0) hab
  obtain ⟨w, hwinj, hwAL⟩ := exists_chain_of_weylA5 hBs E hEinj hsw hErange hW5
  obtain ⟨lab, hlab0⟩ := Equiv.Perm.exists_extending_pair (Fin.castSucc : Fin (5 + 1) → _)
    (fun c => w c.val) (Fin.castSucc_injective _)
    (fun c d h => Fin.ext (hwinj c d (by omega) (by omega) h))
  have hlab : ∀ c : Fin (5 + 1 + 1), c.val ≤ 5 → lab c = w c.val := fun c hc => by
    have := hlab0 ⟨c.val, by omega⟩
    rwa [show (Fin.castSucc ⟨c.val, by omega⟩ : Fin (5 + 1 + 1)) = c from Fin.ext rfl] at this
  let S : Equiv.Perm (Fin (5 + 1 + 1)) →* (V ≃ₗ[ZMod 3] V) :=
    (ggLin (p := 3) ι).comp (E.comp (MulAut.conj lab).toMonoidHom)
  have hSinj : Function.Injective S :=
    (ggLin_injective ι).comp (hEinj.comp (MulAut.conj lab).injective)
  let s : Fin (5 + 1) → (V ≃ₗ[ZMod 3] V) := fun i => S (adjSwap7 i)
  have hs_apply : ∀ i (b : Bs), s i (ι (Additive.ofMul b)) =
      ι (Additive.ofMul (E (Equiv.swap (lab i.castSucc) (lab i.succ)) b)) := fun i b => by
    rw [← conj_adjSwap7]
    exact ggLin_apply_ofMul ι _ b
  have hrefl : ∀ i, IsLinRefl (s i) := fun i => by
    have h := isLinRefl_ggLin ι (hsw _ _ (lab.injective.ne (Fin.castSucc_lt_succ (i := i)).ne))
    have e : s i = ggLin (p := 3) ι (E (Equiv.swap (lab i.castSucc) (lab i.succ))) := by
      simp only [s, S, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_adjSwap7]
    rw [e]
    exact h
  have hdistinct : ∀ i j, i ≠ j → s i ≠ s j := fun i j hij h => adjSwap7_ne i j hij (hSinj h)
  have hcomm : ∀ i j : Fin (5 + 1), i.val + 2 ≤ j.val → s i * s j = s j * s i := fun i j h => by
    simp only [s, ← map_mul, adjSwap7_comm i j h]
  have hbraid : ∀ i j : Fin (5 + 1), i.val + 1 = j.val → s i * s j * s i = s j * s i * s j :=
    fun i j h => by simp only [s, ← map_mul, adjSwap7_braid i j h]
  have hfix := typeA_fix_eq_zero (p := 3) (by norm_num) (n := 5) (by norm_num) hcardV
    ⟨cartanA6InvF3, cartanA6_mul_inv⟩ s hrefl hdistinct hcomm hbraid
  set v₀ : V := ι (Additive.ofMul ⟨x, hx⟩) with hv₀
  have hv0 : v₀ ≠ 0 := by
    intro h
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by rw [← hv₀, h, map_zero])
    exact congrArg Subtype.val (Additive.ofMul.injective (h1.trans ofMul_one.symm))
  have hxfix : ∀ i : Fin (5 + 1), i ≠ Fin.last 5 → s i v₀ = v₀ := fun i hi => by
    have hi5 : i.val < 5 := by
      have := i.isLt
      have : i.val ≠ 5 := fun h => hi (Fin.ext h)
      omega
    rw [hv₀, hs_apply, hlab _ (by simp; omega), hlab _ (by simp; omega)]
    simp only [Fin.coe_castSucc, Fin.val_succ]
    rw [hfixx _ (hwAL i.val hi5)]
  have hxn : s (Fin.last 5) v₀ ≠ v₀ := fun h => hv0 (hfix v₀ fun i => by
    by_cases hi : i = Fin.last 5
    · rw [hi]; exact h
    · exact hxfix i hi)
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_linearEquiv_of_typeA_refl (p := 3) (by norm_num) (n := 5)
    (by norm_num) s hrefl hdistinct hcomm hbraid hfix v₀ hxfix hxn
  let crd : Bs → (Fin (5 + 1 + 1) → ZMod 3) := fun b => sumZeroCoords (κ (ι (Additive.ofMul b)))
  have hgen : ∀ (i : Fin (5 + 1)) (b : Bs),
      crd (E ((MulAut.conj lab) (adjSwap7 i)) b) = fun j => crd b (adjSwap7 i j) := fun i b => by
    have h1 : κ (ι (Additive.ofMul (E ((MulAut.conj lab) (adjSwap7 i)) b))) =
        κ (s i (ι (Additive.ofMul b))) := by rw [hs_apply, conj_adjSwap7]
    simp only [crd]
    rw [h1]
    induction i using Fin.lastCases with
    | last =>
        have h2 := congrFun hκ2 (ι (Additive.ofMul b))
        simp only [Function.comp_apply] at h2
        rw [h2, sumZeroCoords_kRefl zmod3_three]
        funext j
        simp only [adjSwap7, Fin.succ_last]
    | cast k =>
        have h2 := congrFun (hκ1 k) (ι (Additive.ofMul b))
        simp only [Function.comp_apply] at h2
        rw [h2, sumZeroCoords_coordPerm]
        funext j
        simp only [adjSwap7, Fin.succ_castSucc]
  have hall : ∀ ρ : Equiv.Perm (Fin (5 + 1 + 1)), ∀ b : Bs,
      crd (E ((MulAut.conj lab) ρ) b) = fun j => crd b (ρ.symm j) := by
    intro ρ
    have hρ : ρ ∈ (⊤ : Submonoid (Equiv.Perm (Fin (5 + 1 + 1)))) := Submonoid.mem_top ρ
    rw [← Equiv.Perm.mclosure_swap_castSucc_succ (5 + 1)] at hρ
    induction hρ using Submonoid.closure_induction with
    | mem ρ hmem =>
        obtain ⟨i, rfl⟩ := hmem
        intro b
        have := hgen i b
        simp only [adjSwap7] at this
        rw [this, Equiv.symm_swap]
    | one =>
        intro b
        simp only [map_one, MulAut.one_apply, Equiv.Perm.one_symm, Equiv.Perm.coe_one, id]
    | mul ρ σ _ _ hρ hσ =>
        intro b
        rw [map_mul, map_mul, MulAut.mul_apply, hρ, hσ]
        rfl
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hκ3
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ha
    exact hv0 (κ.injective (by rw [← ha, map_zero]))
  have hcrdx : crd ⟨x, hx⟩ = fun j => if j = Fin.last (5 + 1) then 0 else a := by
    simp only [crd]
    rw [← hv₀, ← ha]
    have h1 : (a • (1 : Fin (5 + 1) → ZMod 3)) = fun _ => a := by
      funext k
      simp
    rw [h1, sumZeroCoords_const zmod3_three]
  let addHom : Fin (5 + 1 + 1) → (Additive Bs →+ ZMod 3) := fun j =>
    ((LinearMap.proj j).comp ((a⁻¹ • sumZeroCoords).comp κ.toLinearMap)).toAddMonoidHom.comp
      ι.toAddMonoidHom
  let κW : Fin 7 → (Bs →* Multiplicative (ZMod 3)) := fun j =>
    AddMonoidHom.toMultiplicativeRight (addHom j)
  have hκW : ∀ j b, κW j b = Multiplicative.ofAdd (a⁻¹ * crd b j) := fun j b => rfl
  refine ⟨κW, Fin.last 6, ⟨?_, ?_, ?_, ?_, hx, ?_⟩⟩
  ·
    intro b hb
    have hz : crd b = 0 := by
      funext j
      have h1 := hb j
      rw [hκW, ← ofAdd_zero] at h1
      have h2 := Multiplicative.ofAdd.injective h1
      exact (mul_eq_zero.mp h2).resolve_left (inv_ne_zero ha0)
    have h3 : κ (ι (Additive.ofMul b)) = 0 :=
      sumZeroCoords_injective (p := 3) (by rw [map_zero]; exact hz)
    have h4 : Additive.ofMul b = 0 := ι.injective (by rw [map_zero]; exact κ.injective (by
      rw [h3, map_zero]))
    exact Additive.ofMul.injective (h4.trans ofMul_one.symm)
  ·
    intro b
    simp only [hκW]
    rw [← ofAdd_sum, ← Finset.mul_sum]
    have h0 : ∑ j : Fin 7, crd b j = 0 :=
      sumZeroCoords_sum (p := 3) zmod3_three (κ (ι (Additive.ofMul b)))
    rw [h0, mul_zero, ofAdd_zero]
  ·
    intro φ hφ
    obtain ⟨π, rfl⟩ : ∃ π, E π = φ :=
      ⟨Ehat.symm ⟨φ, hφ⟩, by rw [hEapp, MulEquiv.apply_symm_apply]⟩
    refine ⟨lab⁻¹ * π * lab, fun j b => ?_⟩
    have hc : (MulAut.conj lab) (lab⁻¹ * π * lab) = π := by
      rw [MulAut.conj_apply]
      group
    have hE : E π = E ((MulAut.conj lab) (lab⁻¹ * π * lab)) := by rw [hc]
    rw [hκW, hκW, hE, hall]
  ·
    intro σ
    refine ⟨E ((MulAut.conj lab) σ), hEmem _, fun j b => ?_⟩
    rw [hκW, hκW, hall]
  ·
    intro j
    rw [hκW, hcrdx]
    by_cases hj : j = Fin.last 6
    · subst hj
      simp
    · have hj' : ¬ ((j : Fin (5 + 1 + 1)) = Fin.last (5 + 1)) := hj
      simp only [hj', if_false, hj, inv_mul_cancel₀ ha0]

theorem weylCoordInput_holds : WeylCoordInput := by
  intro G _ _ B Bs x L D J 𝒦 y K hcfg hcard _ hW6 hW5
  have hconfig : GGConfig 3 B Bs x L D J := hcfg.1.1
  obtain ⟨-, hxB, hx1, hcomp, -⟩ := ggThmIHyp_unpack hconfig.1
  have hbstar := hconfig.2.1
  have hxBs : x ∈ Bs := hbstar.1 hxB
  exact exists_weylCoords_core hbstar.2.1 hcard le_sup_left hW6 hW5 hxBs hx1
    (fun φ hφ => ggAutomizer_apply_eq_of_le_centralizer (x := ⟨x, hxBs⟩) hcomp.1 hφ)

end CFSG.GGQ2Prime
