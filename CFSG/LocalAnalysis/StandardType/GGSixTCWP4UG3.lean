module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TwistedE6Base
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnGenUni
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSuNHom
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeE6FourCore
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.RankThree.PartOne.KE (twistedTorusOf)

section Algebra

theorem exists_of_mem_map_conj {G : Type*} [Group G] {D : Subgroup G} {g0 y : G}
    (hy : y ∈ D.map (MulAut.conj g0).toMonoidHom) : ∃ x ∈ D, y = g0 * x * g0⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, hx, rfl⟩

theorem conj_elt_mem_map_conj {G : Type*} [Group G] {D : Subgroup G} {g0 x : G} (hx : x ∈ D) :
    g0 * x * g0⁻¹ ∈ D.map (MulAut.conj g0).toMonoidHom :=
  ⟨x, hx, rfl⟩

theorem mem_of_mem_map_conj {G : Type*} [Group G] {D T : Subgroup G} {g0 g0' : G}
    (h : ∀ y ∈ D.map (MulAut.conj g0).toMonoidHom, y ∈ T.map (MulAut.conj g0').toMonoidHom) :
    ∀ x ∈ D, (g0⁻¹ * g0')⁻¹ * x * (g0⁻¹ * g0') ∈ T := by
  intro x hx
  obtain ⟨t, ht, hte⟩ := h _ (conj_elt_mem_map_conj hx)
  have hte' : g0' * t * g0'⁻¹ = g0 * x * g0⁻¹ := hte
  have : (g0⁻¹ * g0')⁻¹ * x * (g0⁻¹ * g0') = t := by
    calc (g0⁻¹ * g0')⁻¹ * x * (g0⁻¹ * g0') = g0'⁻¹ * (g0 * x * g0⁻¹) * g0' := by group
      _ = g0'⁻¹ * (g0' * t * g0'⁻¹) * g0' := by rw [hte']
      _ = t := by group
  rw [this]
  exact ht

theorem prod_zpow_eq_zpow_finset_sum {G : Type*} [CommGroup G] {ι : Type*} (s : Finset ι) (ζ : G)
    (f : ι → ℤ) : ∏ j ∈ s, ζ ^ f j = ζ ^ ∑ j ∈ s, f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem rootChar_eq_one_iff_dvd_pairing {τ : Tag} {L : Type} [Field L] {p : ℕ} {ζ : Lˣ}
    (hζ : IsPrimitiveRoot ζ p) (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ)
    (ha : ∀ j, a j = ζ ^ v j) (γ : Fin τ.rank → ℤ) :
    rootChar a γ = 1 ↔ (p : ℤ) ∣ ∑ j, γ j * v j := by
  have h : rootChar a γ = ζ ^ (∑ j, γ j * v j) := by
    rw [rootChar, ← prod_zpow_eq_zpow_finset_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [ha j, ← zpow_mul, mul_comm]
  rw [h]
  exact hζ.zpow_eq_one_iff_dvd _

end Algebra

section Lang

theorem rootChar_step_eq
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {a a' : Fin τ.rank → Lˣ}
    (h : S.D.step (rootDiagUnit τ a) = rootDiagUnit τ a') {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootChar a' (S.ρ γ) = rootChar a γ ^ S.D.q := by
  obtain ⟨μ, hμ, h'⟩ := step_pinnedX S hγ
  have hργ : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have h1 : S.D.step (rootDiagUnit τ a * pinnedX τ L γ 1 * (rootDiagUnit τ a)⁻¹) =
      S.D.step (pinnedX τ L γ ((rootChar a γ : L) * 1)) := by
    rw [rootDiagUnit_conj_pinnedX a hγ]
  rw [map_mul, map_mul, map_inv, h, h', h', rootDiagUnit_conj_pinnedX a' hργ] at h1
  have h2 := pinnedX_injective (τ := τ) (R := L) (S.ρ γ) h1
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val]
  have h3 : (rootChar a' (S.ρ γ) : L) * μ = μ * (rootChar a γ : L) ^ S.D.q := by
    simpa using h2
  exact mul_right_cancel₀ hμ (by rw [h3]; ring)

theorem rootDiagUnit_mem_langTorus_iff
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) (a : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a ∈ S.D.torus ↔
      ∀ γ, IsRoot τ γ → rootChar a (S.ρ γ) = rootChar a γ ^ S.D.q := by
  refine ⟨fun h γ hγ => S.frob.rootChar_eq a h γ hγ, fun h => ?_⟩
  obtain ⟨r, e, hr, hrL, -, hqe⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨a', ha'⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
    (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSGen.step_mem_torusGroup S hqe
      (rootDiagUnit_mem_torusGroup a))
  have haa' : a' = a := by
    funext i
    obtain ⟨γ, hγ⟩ := S.ρ.surjective (Pi.single i 1)
    have hγr : IsRoot τ γ := by
      rw [← S.frob.isRoot_iff γ, hγ]
      exact IsRoot.basis i
    have h1 := rootChar_step_eq S ha' hγr
    have h2 := h γ hγr
    rw [hγ, CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h1 h2
    exact h1.trans h2.symm
  refine ⟨rootDiagUnit_mem_torusGroup a, ?_⟩
  have hfix : S.D.step (rootDiagUnit τ a) = rootDiagUnit τ a := by rw [ha', haa']
  simpa [LangDatum.step, MulAut.conj_apply] using hfix

theorem g3_core
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [hL2 : CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {D : Subgroup (ModGL τ L)}
    (hDS : D ≤ S.D.model) (hDexp : ∀ x ∈ D, x ^ p = 1) {g : ModGL τ L}
    (hg : g ∈ adjointGroup τ L) (hgD : ∀ x ∈ D, g⁻¹ * x * g ∈ torusGroup τ L) :
    ∃ (w : WeylGroup τ) (g0' : ModGL τ L), g0' ∈ adjointGroup τ L ∧
      S.D.Φ g0' = g0' * canonicalRep (coxeterSystem τ) L w ∧
      ∀ x ∈ D, (S.D.g0⁻¹ * g0')⁻¹ * x * (S.D.g0⁻¹ * g0') ∈
        twistedTorusOf (canonicalRep (coxeterSystem τ) L w) S.D.Φ := by
  classical
  obtain ⟨r, e, hr, hrL, he0, hqe⟩ := exists_char_pow S
  have hr2 : r = 2 := CharP.eq L hrL hL2
  subst hr2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime p (2 ^ e) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hl := S.D.lang
  obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
  have hFrE : Fr = iterateFrobenius L 2 e :=
    RingHom.ext fun c => by rw [hFr, iterateFrobenius_def, hqe]
  have hfix : ∀ y ∈ D.map (MulAut.conj S.D.g0).toMonoidHom, S.D.Φ y = y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_map_conj hy
    have hx' := (S.D.mem_model.1 (hDS hx)).2
    calc S.D.Φ (S.D.g0 * x * S.D.g0⁻¹)
        = S.D.g0 * (S.D.n * S.D.Φ x * S.D.n⁻¹) * S.D.g0⁻¹ := by
          rw [map_mul, map_mul, map_inv, hl]
          group
      _ = S.D.g0 * x * S.D.g0⁻¹ := by rw [hx']
  have hexp : ∀ y ∈ D.map (MulAut.conj S.D.g0).toMonoidHom, y ^ p = 1 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_map_conj hy
    rw [conj_pow, hDexp x hx]
    group
  have hT : ∀ y ∈ D.map (MulAut.conj S.D.g0).toMonoidHom,
      (S.D.g0 * g)⁻¹ * y * (S.D.g0 * g) ∈ torusGroup τ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_map_conj hy
    have : (S.D.g0 * g)⁻¹ * (S.D.g0 * x * S.D.g0⁻¹) * (S.D.g0 * g) = g⁻¹ * x * g := by group
    rw [this]
    exact hgD x hx
  have hg0g : S.D.g0 * g ∈ adjointGroup τ L := mul_mem S.D.g0_mem hg
  rcases hP with rfl | ⟨t, h, rfl⟩
  · have hΦ' : S.D.Φ = entrywiseFrobGL τ L 2 e :=
      MonoidHom.ext fun x => by rw [hΦ x, hFrE]; simp
    obtain ⟨w, g0', hg0', hl', hmem⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus (ℓ := 2) e he0
        hcop hexp (by rw [← hΦ']; exact hfix) hg0g hT
    exact ⟨w, g0', hg0', by rw [hΦ']; exact hl',
      mem_of_mem_map_conj (by rw [hΦ']; exact hmem)⟩
  · subst h
    have hΦ' : S.D.Φ = twistHom t L (iterateFrobenius L 2 e) :=
      MonoidHom.ext fun x => by rw [hΦ x, hFrE]; rfl
    obtain ⟨w, g0', hg0', hl', hmem⟩ :=
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_lang_torus_of_conj_torus_twisted 2 t e he0
        (A := D.map (MulAut.conj S.D.g0).toMonoidHom) (by rw [← hΦ']; exact hfix) hg0g hT
    exact ⟨w, g0', hg0', by rw [hΦ']; exact hl',
      mem_of_mem_map_conj (by rw [hΦ']; exact hmem)⟩

theorem ggTCInputG3Toral_holds
    :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ D : Subgroup (ModGL τ L), D ≤ S.D.model → IsElemAbelian p D →
        (∃ g ∈ adjointGroup τ L, ∀ x ∈ D, g⁻¹ * x * g ∈ torusGroup τ L) →
        ∃ g₁ ∈ adjointGroup τ L, ∃ S₁ : LangSetup τ L p₀,
          S₁.D.Φ = S.D.Φ ∧ S₁.D.q = S.D.q ∧
          S₁.D.step = (MulAut.conj g₁⁻¹).toMonoidHom.comp
            (S.D.step.comp (MulAut.conj g₁).toMonoidHom) ∧
          (∃ w : WeylGroup τ, S₁.D.n = canonicalRep (coxeterSystem τ) L w) ∧
          (∀ x ∈ D, g₁⁻¹ * x * g₁ ∈ S₁.D.torus) ∧
          (∀ a : Fin τ.rank → Lˣ, (∀ j, a j ^ p = 1) →
            (rootDiagUnit τ a ∈ S₁.D.torus ↔
              ∀ γ, IsRoot τ γ → rootChar a (S₁.ρ γ) = rootChar a γ ^ S₁.D.q)) ∧
          (∀ ζ : Lˣ, IsPrimitiveRoot ζ p → ∀ x ∈ D, ∀ (a : Fin τ.rank → Lˣ) (v : Fin τ.rank → ℤ),
            g₁⁻¹ * x * g₁ = rootDiagUnit τ a → (∀ j, a j = ζ ^ v j) →
            ∀ γ, IsRoot τ γ → (rootChar a γ = 1 ↔ (p : ℤ) ∣ ∑ j, γ j * v j)) := by
  intro τ L _ _ _ p₀ S _ p hp hp2 D hDS hD hconj
  obtain ⟨g, hg, hgD⟩ := hconj
  obtain ⟨w, g0', hg0', hl', hT⟩ := g3_core S hp hp2 hDS hD.2 hg hgD
  obtain ⟨D₁, hΦ, hq, hn, -⟩ : ∃ D₁ : LangDatum τ L, D₁.Φ = S.D.Φ ∧ D₁.q = S.D.q ∧
      D₁.n = canonicalRep (coxeterSystem τ) L w ∧ D₁.g0 = g0' :=
    ⟨⟨S.D.Φ, S.D.q, canonicalRep (coxeterSystem τ) L w, g0', S.D.steinberg, ⟨w, rfl⟩, hg0', hl'⟩,
      rfl, rfl, rfl, rfl⟩
  set g₁ := S.D.g0⁻¹ * g0' with hg₁def
  have hg₁ : g₁ ∈ adjointGroup τ L := mul_mem (inv_mem S.D.g0_mem) hg0'
  have hn₁ : canonicalRep (coxeterSystem τ) L w = g₁⁻¹ * S.D.n * S.D.Φ g₁ := by
    rw [hg₁def, map_mul, map_inv, S.D.lang, hl']
    group
  clear_value g₁
  have hstep : ∀ x, D₁.n * D₁.Φ x * D₁.n⁻¹ =
      g₁⁻¹ * (S.D.n * S.D.Φ (g₁ * x * g₁⁻¹) * S.D.n⁻¹) * g₁ := by
    intro x
    rw [hn, hΦ, hn₁, map_mul, map_mul, map_inv]
    group
  have hfin : Finite D₁.model := by
    have := S.finite
    refine Finite.of_injective (fun x : D₁.model => (⟨g₁ * x * g₁⁻¹, ?_⟩ : S.D.model)) ?_
    · obtain ⟨hxa, hxf⟩ := D₁.mem_model.1 x.2
      refine S.D.mem_model.2 ⟨mul_mem (mul_mem hg₁ hxa) (inv_mem hg₁), ?_⟩
      have h1 := hstep x
      rw [hxf] at h1
      calc S.D.n * S.D.Φ (g₁ * x * g₁⁻¹) * S.D.n⁻¹
          = g₁ * (g₁⁻¹ * (S.D.n * S.D.Φ (g₁ * x * g₁⁻¹) * S.D.n⁻¹) * g₁) * g₁⁻¹ := by group
        _ = g₁ * x * g₁⁻¹ := by rw [← h1]
    · intro x y hxy
      exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
  obtain ⟨S₁, hS₁⟩ : ∃ S₁ : LangSetup τ L p₀, S₁.D = D₁ := by
    obtain ⟨ρ₁, hρ₁⟩ := frobeniusOnRoots_proved τ L D₁
    exact ⟨D₁.toSetup p₀ ρ₁ hρ₁ S.hp (by rw [hq]; exact S.hq) (by rw [hq]; exact S.hqpow)
      (by rw [hq]; exact S.hpq) hfin, rfl⟩
  refine ⟨g₁, hg₁, S₁, ?_, ?_, ?_, ⟨w, ?_⟩, ?_, fun a _ => rootDiagUnit_mem_langTorus_iff S₁ a,
    fun ζ hζ x _ a v _ hav γ _ => rootChar_eq_one_iff_dvd_pairing hζ a v hav γ⟩
  · rw [hS₁]
    exact hΦ
  · rw [hS₁]
    exact hq
  · rw [hS₁]
    refine MonoidHom.ext fun x => ?_
    have h1 := hstep x
    simp only [LangDatum.step, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
    exact h1
  · rw [hS₁]
    exact hn
  · intro x hx
    rw [hS₁]
    show g₁⁻¹ * x * g₁ ∈ twistedTorusOf D₁.n D₁.Φ
    rw [hn, hΦ]
    exact hT x hx

end Lang

end CFSG.StandardType.TableCRes
