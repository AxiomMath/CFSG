module

public import CFSG.LocalAnalysis.StandardType.GGKGTwTheta
public import CFSG.LocalAnalysis.StandardType.GGKGTwMultBridge

public section

namespace CFSG.StandardType.KGL

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.NoOffRest CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def comap_equiv {R S : Type} [Group R] [Group S] (Θ : R ≃* S)
    (E : Subgroup S) : ↥(E.comap Θ.toMonoidHom) ≃* ↥E :=
  (Subgroup.equivMapOfInjective (E.comap Θ.toMonoidHom) Θ.toMonoidHom Θ.injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective Θ.surjective E))


theorem kgA3_clause_tw (hA3 : GGTwE6A3LayerInput) {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (h3 : 3 ∣ 2 ^ n + 1) {R : Type} [Group R] {Θ : R ≃* ↥(twistedE6RootGroup K σ)}
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} {ζ : (AlgebraicClosure K)ˣ}
    {hζ : ζ ^ 3 = 1} (hζo : orderOf ζ = 3) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} {v : WeylGroup TwistTag.E6.tag}
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure K)} {κ : A →* Multiplicative (Fin 6 → ZMod 3)}
    {t : (Fin 6 → ZMod 3) → ModGL TwistTag.E6.tag K}
    (hF : KGTwFrame n σ Θ Fr ζ hζ ψ A v g κ t) {a b : ↥A}
    (hab : GGCorootOrth 3 (ggTorusAut A) a b) :
    ∃ Eab : Subgroup R, GGLayerOf (ggRFix ψ {(a : MulAut L'), (b : MulAut L')}) Eab ∧
      (∀ u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b},
        ∃ l : L', ψ l ∈ Eab ∧ MulAut.conj l = (u : MulAut L')) ∧
      ∀ (N : Type) [Group N] [Finite N] (π : N →* ↥Eab), Function.Surjective π →
        π.ker ≤ Subgroup.center N → commutator N = ⊤ → IsCyclic (Subgroup.center N) := by
  obtain ⟨α, β, hα, hβ, hαβ, haα, hbβ⟩ := hF.aut.corootOrth hab
  let ta : ModGL TwistTag.E6.tag K := t (Multiplicative.toAdd (κ a))
  let tb : ModGL TwistTag.E6.tag K := t (Multiplicative.toAdd (κ b))
  have hta : ta ∈ twistedE6InndiagGL K σ := (hF.ht (Multiplicative.toAdd (κ a))).1
  have htb : tb ∈ twistedE6InndiagGL K σ := (hF.ht (Multiplicative.toAdd (κ b))).1
  have hconjA : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) ta * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ) := by
    show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (t (Multiplicative.toAdd (κ a))) * g =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple α ζ)
    rw [haα, corootTuple_eq_zetaVec_kg ζ hζ α]
    exact hF.t_coroot (kgExpVec α)
  have hconjB : g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) tb * g =
      rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple β ζ) := by
    show g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (t (Multiplicative.toAdd (κ b))) * g =
        rootDiagUnit TwistTag.E6.tag (TwE6RootAs.corootTuple β ζ)
    rw [hbβ, corootTuple_eq_zetaVec_kg ζ hζ β]
    exact hF.t_coroot (kgExpVec β)
  have hζne : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    norm_num at hζo
  obtain ⟨E, hE, ⟨e⟩, hγ⟩ := hA3 n hn h3 K σ hK hσ Fr hF.hFr v hF.hv g hF.hg hF.hgF
    α β hα hβ hαβ ζ hζ hζne ta hta tb htb hconjA hconjB
  let Eab : Subgroup R := E.comap Θ.toMonoidHom
  have hEab_layer : GGLayerOf (ggRFix ψ {(a : MulAut L'), (b : MulAut L')}) Eab := by
    refine layer_of_centralizer_tw Θ ψ hψ {(a : MulAut L'), (b : MulAut L')}
      ({ta, tb} : Set (ModGL TwistTag.E6.tag K)) ?_ ?_ hE
    · rintro f hf
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · exact ⟨ta, by rw [Set.mem_insert_iff]; left; rfl, fun l => hF.conj a l⟩
      · exact ⟨tb, by rw [Set.mem_insert_iff]; right; rfl, fun l => hF.conj b l⟩
    · rintro d hd
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl
      · exact ⟨(a : MulAut L'), by rw [Set.mem_insert_iff]; left; rfl, fun l => hF.conj a l⟩
      · exact ⟨(b : MulAut L'), by rw [Set.mem_insert_iff]; right; rfl, fun l => hF.conj b l⟩
  have hlifts : ∀ u ∈ ggFixedByCentres 3 (ggTorusAut A) {a, b},
      ∃ l : L', ψ l ∈ Eab ∧ MulAut.conj l = (u : MulAut L') := by
    intro u hu
    have hku := hF.aut.fixedByCentres hα hβ hαβ haα hbβ hu
    have hS : ∀ x ∈ {y : Fin Tag.E6.rank → ZMod 3 |
        ∃ γ, IsRoot Tag.E6 γ ∧ iform γ α = 0 ∧ iform γ β = 0 ∧ y = kgExpVec γ},
        t x ∈ E.map (twistedE6RootGroup K σ).subtype := by
      rintro x ⟨γ, hγroot, hγα, hγβ, rfl⟩
      have hx : t (kgExpVec γ) ∈ twistedE6InndiagGL K σ := (hF.ht (kgExpVec γ)).1
      refine hγ γ hγroot hγα hγβ (t (kgExpVec γ)) hx ?_
      rw [corootTuple_eq_zetaVec_kg ζ hζ γ]
      exact hF.t_coroot (kgExpVec γ)
    have htu : t (Multiplicative.toAdd (κ u)) ∈ E.map (twistedE6RootGroup K σ).subtype :=
      hF.t_mem_of_closure (E.map (twistedE6RootGroup K σ).subtype) hS hku
    obtain ⟨e', he'E, he'eq⟩ := Subgroup.mem_map.mp htu
    have he'val : ((e' : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) =
        t (Multiplicative.toAdd (κ u)) := he'eq
    obtain ⟨l, hl⟩ := hψ (Θ.symm (e' : ↥(twistedE6RootGroup K σ)))
    have hΘl : Θ (ψ l) = (e' : ↥(twistedE6RootGroup K σ)) := by
      rw [hl, MulEquiv.apply_symm_apply]
    refine ⟨l, ?_, ?_⟩
    · rw [Subgroup.mem_comap]
      show Θ (ψ l) ∈ E
      rw [hΘl]
      exact he'E
    · refine mulAut_eq_of_comp_eq ψ hker hperf (fun z => ?_)
      apply Θ.injective
      apply Subtype.ext
      rw [MulAut.conj_apply]
      calc ((Θ (ψ (l * z * l⁻¹)) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K)
          = ((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
              ((Θ (ψ z) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
              (((Θ (ψ l) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K))⁻¹ := by
            rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv]
            rfl
        _ = t (Multiplicative.toAdd (κ u)) *
              ((Θ (ψ z) : ↥(twistedE6RootGroup K σ)) : ModGL TwistTag.E6.tag K) *
              (t (Multiplicative.toAdd (κ u)))⁻¹ := by
            rw [hΘl, he'val]
        _ = ((Θ (ψ ((u : MulAut L') z)) : ↥(twistedE6RootGroup K σ)) :
              ModGL TwistTag.E6.tag K) := (hF.conj u z).symm
  refine ⟨Eab, hEab_layer, hlifts, ?_⟩
  intro N _ _ π hπ hkerπ hperfN
  exact kgMult_of_mulEquiv_statedSU_four hn hK ⟨(comap_equiv Θ E).trans e⟩ N π hπ hkerπ hperfN

end CFSG.StandardType.KGL

end
