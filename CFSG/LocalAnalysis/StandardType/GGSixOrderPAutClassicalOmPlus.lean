module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutClassicalOmWeights
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSpin
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusFour
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace OrdPOm

section Torus

variable {K : Type} [Field K] {p : ℕ} {ζ : Kˣ} {m : ℕ}

theorem isElemAbelian_range_spTorusGL (hζ : ζ ^ p = 1) :
    IsElemAbelian p (TableBSymp.spTorusGL (K := K) (m := m) hζ).range := by
  rw [MonoidHom.range_eq_map]
  refine isElemAbelian_map _ ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun a _ => ?_⟩
  exact TableBSymp.pow_card_eq_one_zmod a

theorem spTorusGL_injective [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (hp : Odd p) :
    Function.Injective (TableBSymp.spTorusGL (K := K) (m := m) hζ) := fun a b hab =>
  TableBSymp.spTorus_injective hζ hζo hp
    (congrArg (LargeEvenProjMk _) (Subtype.ext hab : TableBSymp.spTorusSp hζ a =
      TableBSymp.spTorusSp hζ b))

theorem card_range_spTorusGL [NeZero p] (hζ : ζ ^ p = 1) (hζo : orderOf ζ = p) (hp : Odd p) :
    Nat.card (TableBSymp.spTorusGL (K := K) (m := m) hζ).range = p ^ m := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (spTorusGL_injective hζ hζo hp)).toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin m), Fintype.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

theorem diagGL_pairedUnits_commute (t : Fin m → Kˣ) (hζ : ζ ^ p = 1)
    (a : Fin m → Multiplicative (ZMod p)) :
    TauCeti.diagGL (TableBSymp.pairedUnits t) * TableBSymp.spTorusGL hζ a =
      TableBSymp.spTorusGL hζ a * TauCeti.diagGL (TableBSymp.pairedUnits t) := by
  rw [TableBSymp.spTorusGL_apply, ← map_mul, ← map_mul, mul_comm]

end Torus

section Split

open TableBOrth

variable {n f : ℕ}

theorem isElemAbelian_zpowers {H : Type*} [Group H] {p : ℕ} {x : H} (hx : x ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem exists_conj_mem_centralizer_split_plus {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs G₀ : Subgroup G} (hn : 3 ≤ n) {ψ : spinGroup (quadPlus n (GaloisField 2 f)) →* G}
    (hS : GGSixFusionSetting p Bs G₀ (plusDatum n (GaloisField 2 f) hn) .POmegaPlus n f ψ)
    (hp : p ∣ 2 ^ f - 1) {y : G} (hyp : y ^ p = 1)
    (hy : GGPsiInnerDiag (plusDatum n (GaloisField 2 f) hn) ψ y) :
    ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hS.prime⟩
  have hp2 := hS.ne_two
  have hodd : Odd p := hS.prime.odd_of_ne_two hp2
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hS.presents
  have hf : 1 ≤ f := hadm.2.1
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact hS.centralizer_eq_bot
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  set j := spinMatrix (quadPlus n (GaloisField 2 f)) with hjdef
  have hj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff _).mp (ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero)
  have hjr : j.range = LargeEvenOmega (LargeEvenQPlus (GaloisField 2 f) n) :=
    range_spinMatrix_quadPlus hn
  have hin : ∀ c, GGPsiInnerDiag (plusDatum n (GaloisField 2 f) hn) ψ c → c ∈ ψ.range := by
    intro c hc
    obtain ⟨g, hg, hcg⟩ := PsiDiag.SpinP.exists_mem_centralizer hn ψ hker hc
    rw [hC, Subgroup.mem_bot] at hcg
    rw [eq_inv_of_mul_eq_one_left hcg]
    exact ψ.range.inv_mem hg
  obtain ⟨u, rfl⟩ := hin y hy
  have hup : u ^ p = 1 := hψ (by rw [map_pow, hyp, map_one])
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := GaloisField 2 f) (p := p)
    (by rw [GaloisField.card 2 f (by omega)]; exact hp)
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hBsψ : Bs ≤ ψ.range := fun b hb => hin b (hS.innerDiag b hb)
  obtain ⟨hA, hAj, hAc⟩ := transfer_range ψ hψ j hj hS.elem hBsψ
  have hBs : Nat.card Bs ≤ p ^ n := by
    rw [← hAc]
    exact card_le_plus hp2 hζ (hAj.trans (hjr.le.trans (omega_le_orth _))) hA
  have hxO : j u ∈ LargeEvenOrthGroup (LargeEvenQPlus (GaloisField 2 f) n) :=
    omega_le_orth _ (hjr ▸ ⟨u, rfl⟩)
  have hxp : j u ^ p = 1 := by rw [← map_pow, hup, map_one]
  obtain ⟨g, hgO, χ, hχ⟩ := exists_orth_conj_plus_le hp2 hζ (Subgroup.zpowers_le.mpr hxO)
    (isElemAbelian_zpowers hxp)
  have hgx := hχ ⟨j u, Subgroup.mem_zpowers _⟩
  set T := (TableBSymp.spTorusGL (K := GaloisField 2 f) (m := n) hζp).range with hT
  set E := T.map (MulAut.conj g⁻¹).toMonoidHom with hE
  have hEel : IsElemAbelian p E := isElemAbelian_map _ (isElemAbelian_range_spTorusGL hζp)
  have hEcard : Nat.card E = p ^ n := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      card_range_spTorusGL hζp hζ hodd]
  have hEj : E ≤ j.range := by
    rw [hjr, hE, ← map_conj_omega (inv_mem hgO)]
    refine Subgroup.map_mono ?_
    rintro _ ⟨a, rfl⟩
    exact TableBSymp.spTorusGL_mem_omegaPlus hζp hodd a
  set D := TauCeti.diagGL (TableBSymp.pairedUnits fun k =>
    χ k ⟨j u, Subgroup.mem_zpowers _⟩) with hD
  have hu' : j u = g⁻¹ * D * g := by
    rw [← hgx]
    group
  have hxE : ∀ z ∈ E, j u * z = z * j u := by
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hu']
    calc g⁻¹ * D * g * (g⁻¹ * TableBSymp.spTorusGL hζp a * g) =
        g⁻¹ * (D * TableBSymp.spTorusGL hζp a) * g := by group
      _ = g⁻¹ * (TableBSymp.spTorusGL hζp a * D) * g := by
        rw [hD, diagGL_pairedUnits_commute]
      _ = g⁻¹ * TableBSymp.spTorusGL hζp a * g * (g⁻¹ * D * g) := by group
  obtain ⟨hE', hEG, hEc, hcomm⟩ := transfer_mat ψ hψ j hj hEel hEj hxE
  exact OrdPNS.exists_conj_mem_centralizer_of_card hS
    (hEG.trans (hrange.le.trans Subgroup.le_normalizer)) hE' (by rw [hEc, hEcard]; exact hBs)
    hcomm

end Split

end OrdPOm

section Family

theorem ggOrdPInnerConj_POmegaPlus_split : ∀ (G : Type) [Group G] [Finite G] (p : ℕ)
    (Bs G₀ : Subgroup G) (n f : ℕ) (ψ : (ggU .POmegaPlus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ → p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G) := by
  intro G _ _ p Bs G₀ n f
  by_cases hn : 3 ≤ n
  · rw [ggU_POmegaPlus_eq hn]
    intro ψ hS hp y _ hyo hy
    exact OrdPOm.exists_conj_mem_centralizer_split_plus hn hS hp (hyo ▸ pow_orderOf_eq_one y) hy
  · rw [show ggU .POmegaPlus n f = trivialUniversal from dite_eq_right hn]
    intro ψ hS
    exact absurd hS.presents.1.2 (by decide)

@[expose] def GGOrdPInnerConjPOmegaPlusNonsplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU .POmegaPlus n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU .POmegaPlus n f).D .POmegaPlus n f ψ →
    GGTwoLocalRankFour p (Subgroup.normalizer (G₀ : Set G)) → ¬ p ∣ 2 ^ f - 1 →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiInnerDiag (ggU .POmegaPlus n f).D ψ y →
      ∃ m ∈ Subgroup.normalizer (G₀ : Set G), m⁻¹ * y * m ∈ Subgroup.centralizer (Bs : Set G)

theorem ggOrdPInnerConjAt_POmegaPlus_of_nonsplit (h : GGOrdPInnerConjPOmegaPlusNonsplit) :
    GGOrdPInnerConjAt .POmegaPlus := by
  intro G _ _ p Bs G₀ n f ψ hS h24 _ y hyM hyo hy
  by_cases hpq : p ∣ 2 ^ f - 1
  · exact ggOrdPInnerConj_POmegaPlus_split G p Bs G₀ n f ψ hS hpq y hyM hyo hy
  · exact h G p Bs G₀ n f ψ hS h24 hpq y hyM hyo hy

end Family

end CFSG.StandardType
