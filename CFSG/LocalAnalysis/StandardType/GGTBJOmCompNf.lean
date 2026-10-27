module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmCompTwisted
public import CFSG.LocalAnalysis.StandardType.GGTorusDWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBJOmDTwoCount

public section

open Module Multiplicative QuadraticMap Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord NbrOrth TypeBDatum TypeDDatum CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

private theorem tbjN_evenSignedAut_eq_evenSignedGroup [Fact p.Prime] (hp2 : p ≠ 2) :
    evenSignedAut r p = DScalarTorus.evenSignedGroup (p := p) (N := r) := by
  apply le_antisymm
  · unfold evenSignedAut evenSignedSupportedAut
    rw [Subgroup.closure_le]
    rintro σ (h | h)
    · obtain ⟨a, -, b, -, hab, rfl⟩ := h
      exact DScalarTorus.permAut_mem_evenSignedGroup _
    · obtain ⟨a, -, b, -, hab, rfl⟩ := h
      exact DScalarTorus.sgnAut_pair_mem_evenSignedGroup hab
  · refine DScalarTorus.evenSignedGroup_le (p := p) (N := r) hp2
      (fun i j hij => ?_) (fun σ => ?_)
    · exact Subgroup.subset_closure
        (Or.inr ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, hij, rfl⟩)
    · exact tbjA_permSupportedAut_le_evenSignedSupportedAut Finset.univ
        (tbjA_permAut_mem_permSupportedAut_of_fixes Finset.univ σ
          (fun i hi => absurd (Finset.mem_univ i) hi))

private theorem tbjN_support_of_fix [Fact p.Prime] {σ : MulAut (Fin r → Multiplicative (ZMod p))}
    {S : Finset (Fin r)} {π : Equiv.Perm (Fin r)} {c : Fin r → ZMod p}
    (hc : ∀ i, c i = 1 ∨ c i = -1)
    (hu : ∀ f i, toAdd (σ f (π i)) = c i * toAdd (f i))
    (hfix : ∀ j ∉ S, σ (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1)) :
    (∀ j ∉ S, π j = j) ∧ (∀ j ∉ S, c j = 1) := by
  classical
  have hone : ∀ j ∉ S, π j = j ∧ c j = 1 := by
    intro j hj
    have h := hu (Pi.mulSingle j (ofAdd 1)) j
    rw [hfix j hj] at h
    by_cases hpj : π j = j
    · refine ⟨hpj, ?_⟩
      rw [hpj] at h
      simpa using h.symm
    · exfalso
      rw [Pi.mulSingle_eq_of_ne hpj] at h
      simp only [toAdd_one, Pi.mulSingle_eq_same, toAdd_ofAdd, mul_one] at h
      rcases hc j with h1 | h1
      · rw [h1] at h
        exact one_ne_zero h.symm
      · rw [h1] at h
        exact one_ne_zero (neg_eq_zero.mp h.symm)
  exact ⟨fun j hj => (hone j hj).1, fun j hj => (hone j hj).2⟩

theorem TBJOmData.torusAut_component_nf [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (hA : A ≤ orthDerived Q)
    (hnf : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    {f₀ : Fin r → Multiplicative (ZMod p)} (hf₀ : f₀ ≠ 1) {J : Subgroup ↥(orthDerived Q)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({Δ.τΩ hA f₀} : Set ↥(orthDerived Q))))
    (hcount : p ^ 2 * Nat.card {f : Fin r → Multiplicative (ZMod p) //
      ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f} ≤ p ^ r) :
    ∃ S : Finset (Fin r),
      (∀ f : Fin r → Multiplicative (ZMod p), (∀ σ ∈ Δ.torusAut hA J, σ f = f) →
        ∀ j ∈ J, Δ.τΩ hA f * j = j * Δ.τΩ hA f) ∧
      ((3 ≤ S.card ∧ S ≠ Finset.univ ∧ Δ.torusAut hA J = evenSignedSupportedAut r p S) ∨
        ∃ (s : Fin r → ZMod p) (hs : ∀ i, s i * s i = 1), 2 ≤ S.card ∧
          Δ.torusAut hA J = twistedPermAut r p S s hs) := by
  classical
  have hx := Δ.oddOrderIsometry hp2 hQ hA f₀
  rcases component_cases hQ Fact.out hp2 (x := Δ.τΩ hA f₀) hx hJ with
    ⟨h, hh, hhX, rfl⟩ | ⟨F, hFq, hFle, hFn, hF4, rfl⟩
  ·
    obtain ⟨a, P, ha, hP, hswap, hmixed, hcent⟩ := Δ.blockG_orthDerived hp2 hQ hA f₀ hh hhX
    obtain ⟨S, s, hs, h3, htor, hfix⟩ := Δ.torusAut_twisted_of_blockData hp2 hA hJ.1 ha hP hswap
      hmixed hcent hcount
    exact ⟨S, hfix, Or.inr ⟨s, hs, by omega, htor⟩⟩
  ·
    have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
    have hFc : CFSG.Assembly.IsComponentOf F (supportedFixedDerived Q (Δ.τ f₀)) :=
      ⟨hFle, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hFle).2 hFn.isSubnormal,
        (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2 hFq⟩
    have hcard : Nat.card {f : Fin r → Multiplicative (ZMod p) //
        ∀ j ∈ F.subgroupOf (orthDerived Q), Δ.τΩ hA f * j = j * Δ.τΩ hA f} =
        Nat.card {f : Fin r → Multiplicative (ZMod p) // ∀ j ∈ F, Δ.τ f * j = j * Δ.τ f} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun f =>
        ⟨fun h j hj => congrArg Subtype.val (h ⟨j, hFΩ hj⟩ (Subgroup.mem_subgroupOf.mpr hj)),
          fun h j hj => Subtype.ext (h (j : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hj))⟩)
    have h3 := Δ.three_le_card_zero_of_isComponentOf hp2 hQ hA hnf f₀ hFc
      (by rw [← hcard]; exact hcount)
    obtain ⟨hswapZ, hcentZ, hdim⟩ := Δ.blockZ_nf hp2 hQ hA f₀ h3
    have hFeq : F = supportedFixedDerived Q (Δ.τ f₀) := hF4.resolve_left fun h4 => by
      have h4' : finrank K (fixedSpace (Δ.τ f₀)) ≤ 4 := h4
      omega
    have h5 : 5 ≤ finrank K (fixedSpace (Δ.τ f₀)) := hdim
    let S : Finset (Fin r) := Finset.univ.filter (fun i => toAdd (f₀ i) = 0)
    have hSmem : ∀ i, i ∈ S ↔ toAdd (f₀ i) = 0 := by intro i; simp [S]
    have hScard : S.card = Nat.card {i : Fin r // toAdd (f₀ i) = 0} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hmemJ : ∀ (n : V ≃ₗ[K] V) (hn : n ∈ orthDerived Q),
        n ∈ supportedFixedDerived Q (Δ.τ f₀) →
          (⟨n, hn⟩ : ↥(orthDerived Q)) ∈ F.subgroupOf (orthDerived Q) := by
      intro n hn hnF
      rw [Subgroup.mem_subgroupOf, hFeq]
      exact hnF
    have hswapJ : ∀ a b, a ∈ S → b ∈ S → a ≠ b →
        permAut (p := p) (Equiv.swap a b) ∈ Δ.torusAut hA (F.subgroupOf (orthDerived Q)) := by
      intro a b ha hb hab
      obtain ⟨n, hn, hconj⟩ := hswapZ a b hab ((hSmem a).1 ha) ((hSmem b).1 hb)
      exact ⟨⟨n, hx.supportedFixedDerived_le_orthDerived hn⟩,
        hmemJ n (hx.supportedFixedDerived_le_orthDerived hn) hn,
        fun f => Subtype.ext (hconj f)⟩
    have hdinvJ : ∀ a b, a ∈ S → b ∈ S → a ≠ b →
        (sgnAut (p := p) a * sgnAut b : MulAut (Fin r → Multiplicative (ZMod p))) ∈
          Δ.torusAut hA (F.subgroupOf (orthDerived Q)) := by
      intro a b ha hb hab
      obtain ⟨n, hn, hconj⟩ := Δ.blockZ_dinv hp2 hQ hA f₀ h5 hab ((hSmem a).1 ha) ((hSmem b).1 hb)
      exact ⟨⟨n, hx.supportedFixedDerived_le_orthDerived hn⟩,
        hmemJ n (hx.supportedFixedDerived_le_orthDerived hn) hn,
        fun f => Subtype.ext (hconj f)⟩
    have hlower : evenSignedSupportedAut r p S ≤ Δ.torusAut hA (F.subgroupOf (orthDerived Q)) := by
      unfold evenSignedSupportedAut
      rw [Subgroup.closure_le]
      rintro σ (⟨a, ha, b, hb, hab, rfl⟩ | ⟨a, ha, b, hb, hab, rfl⟩)
      · exact hswapJ a b ha hb hab
      · exact hdinvJ a b ha hb hab
    have hupper : Δ.torusAut hA (F.subgroupOf (orthDerived Q)) ≤ evenSignedSupportedAut r p S := by
      intro σ hσ
      have hσtop : σ ∈ Δ.torusAut hA ⊤ := by
        obtain ⟨n, -, hn⟩ := hσ
        exact ⟨n, Subgroup.mem_top _, hn⟩
      rw [Δ.torusAut_top_nf hp2 hQ hT hA hnf,
        tbjN_evenSignedAut_eq_evenSignedGroup hp2] at hσtop
      obtain ⟨π, c, hc, hprod, hu⟩ := hσtop
      obtain ⟨n, hnJ, hn⟩ := hσ
      have hfixS : ∀ j ∉ S, σ (Pi.mulSingle j (ofAdd 1)) = Pi.mulSingle j (ofAdd 1) := by
        intro j hj
        have hfj : ∀ i, toAdd (f₀ i) = 0 →
            (Pi.mulSingle j (ofAdd 1) : Fin r → Multiplicative (ZMod p)) i = 1 := by
          intro i hi
          have hij : i ≠ j := fun h => hj (h ▸ (hSmem i).2 hi)
          exact Pi.mulSingle_eq_of_ne hij _
        have hcomm := hcentZ _ hfj (n : V ≃ₗ[K] V) (hFle (Subgroup.mem_subgroupOf.mp hnJ))
        have h1 : n * Δ.τΩ hA (Pi.mulSingle j (ofAdd 1)) * n⁻¹ =
            Δ.τΩ hA (Pi.mulSingle j (ofAdd 1)) :=
          mul_inv_eq_iff_eq_mul.mpr (Subtype.ext hcomm.symm)
        apply tbjA_tauOmega_injective Δ hA
        rw [← hn, h1]
      obtain ⟨hπ, hεS⟩ := tbjN_support_of_fix hc hu hfixS
      exact tbjA_mem_evenSignedSupportedAut_of hp2 S hc hπ hεS hprod hu
    refine ⟨S, ?_, Or.inl ⟨by rw [hScard]; exact h3, ?_, le_antisymm hupper hlower⟩⟩
    · intro f hf j hj
      have hfS : ∀ i ∈ S, f i = 1 :=
        tbjA_fixed_of_mem_evenSignedSupportedAut hp2 (by rw [hScard]; omega)
          (fun σ hσ => hf σ (hlower hσ))
      exact Subtype.ext (hcentZ f (fun i hi => hfS i ((hSmem i).2 hi)) (j : V ≃ₗ[K] V)
        (hFle (Subgroup.mem_subgroupOf.mp hj)))
    · intro hSu
      apply hf₀
      funext i
      have hi : i ∈ S := hSu ▸ Finset.mem_univ i
      exact toAdd.injective ((hSmem i).1 hi)

end OrthTorus

end CFSG.StandardType

end
