module

public import CFSG.LocalAnalysis.StandardType.GGCompatNbrSomeDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylB
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerSp

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CoxeterSystem CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras TauCeti.GLSymplecticFin

namespace CompatSp

variable {n : ℕ} {F : Type} [Field F]

theorem diag_conj_elt (t : Fin n → Fˣ) (r : RootSubgroupIndex n) (c : F) :
    equivStatedSp n F (diagonal t) * elt r c * (equivStatedSp n F (diagonal t))⁻¹ =
      elt r ((r.character t : F) * c) := by
  simp only [elt]
  rw [← map_inv, ← map_mul, ← map_mul, diagonal_mul_rootSubgroup_mul_inv]
  rfl

theorem diagonal_mem_ggTorus (t : Fin n → Fˣ) :
    equivStatedSp n F (diagonal t) ∈ ggTorus (Symplectic.rootDatum n F) := by
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hγ
  change _ ∈ Subgroup.normalizer (rootGroup n F γ : Set (StatedSp n F))
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hD : (equivStatedSp n F (diagonal t))⁻¹ = equivStatedSp n F (diagonal t⁻¹) := by
    simp only [map_inv]
  constructor
  · intro hz
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).mp hz
    rw [diag_conj_elt]
    exact elt_mem_rootGroup hr _
  · intro hz
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff hr).mp hz
    have e : z = (equivStatedSp n F (diagonal t))⁻¹ * elt r c *
        ((equivStatedSp n F (diagonal t))⁻¹)⁻¹ := by
      rw [← hc]
      group
    rw [e, hD, diag_conj_elt]
    exact elt_mem_rootGroup hr _

theorem stdVec_difference_eq {k : Fin n} (hk : k.val + 1 < n) :
    stdVec (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (ne_succ' hk)) =
      toStd n (Pi.single k 1) := by
  rw [toStd_single_of_lt' hk]
  rfl

theorem spLeviBlock_torus_match {k : Fin n} (hk : k.val + 1 < n) {h' : StatedSp n F}
    (hh' : h' ∈ ggTorus (Symplectic.rootDatum n F)) :
    ∃ h ∈ ggTorus (Symplectic.rootDatum (n + 1) F),
      ∀ z ∈ (Symplectic.rootDatum (n + 1) F).rootGroup
          (Fin.cons 0 (Pi.single k 1) : Fin (n + 1) → ℤ),
        h * z * h⁻¹ = spLeviBlock n F h' * z * (spLeviBlock n F h')⁻¹ := by
  have hr₀ := stdVec_difference_eq hk
  have hδ : (Pi.single k 1 : Fin n → ℤ) ∈ roots (isFiniteType_cartanC n) ∅ :=
    mem_roots_of_stdVec hr₀
  have hN : h' ∈ Subgroup.normalizer (rootGroup n F (Pi.single k 1) : Set (StatedSp n F)) := by
    simp only [ggTorus, Subgroup.mem_iInf] at hh'
    exact hh' _ hδ
  obtain ⟨χ, hχ⟩ := PsiDiag.Symp.conj_elt_eq_of_mem_normalizer hr₀ hN
  have hχ0 : χ ≠ 0 := by
    intro h0
    have h1 := hχ 1
    rw [h0, zero_mul, elt_zero, mul_inv_eq_one, mul_eq_left] at h1
    exact one_ne_zero (elt_injective _ (h1.trans (elt_zero _).symm))
  refine ⟨equivStatedSp (n + 1) F (diagonal (Pi.mulSingle k.succ (Units.mk0 χ hχ0))),
    diagonal_mem_ggTorus _, fun z hz => ?_⟩
  change z ∈ rootGroup (n + 1) F _ at hz
  rw [rootGroup_cons hδ] at hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr₀).mp hz'
  have hR : spLeviBlock n F h' * spLeviBlock n F (elt (RootSubgroupIndex.difference k
      ⟨k.val + 1, hk⟩ (ne_succ' hk)) c) * (spLeviBlock n F h')⁻¹ =
      elt (spShift (RootSubgroupIndex.difference k ⟨k.val + 1, hk⟩ (ne_succ' hk))) (χ * c) := by
    rw [← map_inv, ← map_mul, ← map_mul, hχ, spLeviBlock_elt]
  rw [hR, spLeviBlock_elt, diag_conj_elt]
  simp [spShift, Fin.ext_iff]

end CompatSp

section Compat

theorem ggCompatPresented_spBlock {G : Type*} [Group G] {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    {ψ : StatedSp (n + 1) (GaloisField 2 f) →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp (n + 1) (GaloisField 2 f))) :
    GGCompatPresented (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) ψ
      (ψ.comp (spLeviBlock n (GaloisField 2 f))).range := by
  have hk : (⟨0, by omega⟩ : Fin n).val + 1 < n := by simp only; omega
  have hδ : (Pi.single (⟨0, by omega⟩ : Fin n) 1 : Fin n → ℤ) ∈ roots (isFiniteType_cartanC n) ∅ :=
    mem_roots_of_stdVec (CompatSp.stdVec_difference_eq hk)
  refine ggCompatPresented_comp_of_conj (t' := .PSp) (n' := n) (f' := f) hker
    ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega⟩ (by change 2 ≤ n; omega)
    (ι := spLeviBlock n (GaloisField 2 f)) spLeviBlock_injective hδ (cons_mem_roots hδ)
    (fun z hz => ?_) (fun _ hh' => CompatSp.spLeviBlock_torus_match hk hh')
  change z ∈ rootGroup (n + 1) _ _ at hz
  rw [rootGroup_cons hδ] at hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  exact ⟨z', hz', rfl⟩

end Compat

section Presentation

variable {G : Type} [Group G] [Finite G]

theorem exists_presents_local_ext {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hrank : 3 ≤ bnRank t n)
    (hrk : 2 ≤ (ggU t n f).D.rank) {ν : GGWeyl (ggU t n f).D →* (ggU t n f).K} {ι : Type}
    {S : ι → Set (Fin (ggU t n f).D.rank → ℤ)} (φ : ∀ k, ggSub (ggU t n f).D (S k) →* G)
    {ρ : GGWeyl (ggU t n f).D →* G} (Wk : ι → Subgroup (GGWeyl (ggU t n f).D))
    (hν : GGStandardCopy (ggU t n f).D ν) (hS : ∀ k, S k ⊆ (ggU t n f).D.roots)
    (hρ : Function.Injective ρ)
    (hagree : ∀ k l, ∀ α ∈ S k, α ∈ S l → ∀ z ∈ (ggU t n f).D.rootGroup α,
      ggExt (φ k) z = ggExt (φ l) z)
    (hWk : ∀ k, ∀ v ∈ Wk k, ν v ∈ ggSub (ggU t n f).D (S k))
    (hρk : ∀ k, ∀ v ∈ Wk k, ggExt (φ k) (ν v) = ρ v)
    (hrefl : ∀ (k : ι) (w : GGWeyl (ggU t n f).D) (j : Fin (ggU t n f).D.rank),
      weylAction (ggU t n f).D.isFiniteType w (Pi.single j 1) ∈ S k →
        w * (coxeterMatrix (ggU t n f).D.isFiniteType).toCoxeterSystem.simple j * w⁻¹ ∈ Wk k)
    (htrans : ∀ (w : GGWeyl (ggU t n f).D) (k l : ι), ∀ α ∈ S k,
      weylAction (ggU t n f).D.isFiniteType w α ∈ S l →
        ∃ α' ∈ S k, α' ∈ S l ∧ ∃ v₁ ∈ Wk k, ∃ v₂ ∈ Wk l,
          weylAction (ggU t n f).D.isFiniteType v₁ α = α' ∧
          weylAction (ggU t n f).D.isFiniteType v₂ α' =
            weylAction (ggU t n f).D.isFiniteType w α)
    (hcent : ∀ (w : GGWeyl (ggU t n f).D) (k : ι), ∀ α ∈ S k,
      weylAction (ggU t n f).D.isFiniteType w α = α → ∀ z ∈ (ggU t n f).D.rootGroup α,
        ρ w * ggExt (φ k) z * (ρ w)⁻¹ = ggExt (φ k) z)
    (horb : GGOrbit (ggU t n f).D S)
    (hnt : ∃ k, ∃ γ ∈ S k, ∃ z ∈ (ggU t n f).D.rootGroup γ, ggExt (φ k) z ≠ 1)
    (hφG : ∀ k, (φ k).range ≤ ggG0 p B x L D J) (hρG : ρ.range ≤ ggG0 p B x L D J)
    (hL : L ≤ ggClosure (ggU t n f).D S φ ρ.range)
    (hK : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ ggClosure (ggU t n f).D S φ ρ.range) :
    ∃ ψ₀ : (ggU t n f).K →* G, GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ₀ ∧
      ∀ k (u : ggSub (ggU t n f).D (S k)), ψ₀ u = φ k u :=
  ggPresentsG0_of_presentation t n f hadm hrank hrk hν.1 hS φ
    (MonoidHom.ofInjective hρ).symm.surjective
    (ggActsLike_ofInjective hρ (ggActsLikeHom_of_local hν hρ hS hagree Wk hWk hρk htrans hcent))
    (ggWeylInR_ofInjective hρ (ggWeylInRHom_of_local Wk hρk hrefl)) horb hnt
    (ggClosure_eq_ggG0 hφG hρG hL hK)

theorem ggSecFiveCompat_of_spEndNode {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) (φ₁ : StatedSp n (GaloisField 2 f) →* G)
    (hφ : Function.Injective φ₁) (hφL : φ₁.range = L) {T : G} (hT : GGSpEndNode φ₁ T)
    (hTG : T ∈ ggG0 p B x L D J)
    (hnbr : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      K ≤ L ⊔ L.map (MulAut.conj T).toMonoidHom) :
    ∃ ψ₀ : (ggU .PSp (n + 1) f).K →* G,
      GGPresentsG0 (ggG0 p B x L D J) (ggU .PSp (n + 1) f).D .PSp (n + 1) f ψ₀ ∧
        GGCompatPresented (ggU .PSp (n + 1) f).D ψ₀ L := by
  have h2 : (2 : GaloisField 2 f) = 0 := by
    exact_mod_cast CharP.cast_eq_zero (GaloisField 2 f) 2
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hadm : StatedLieAdmissible .PSp (n + 1) 2 f :=
    ⟨Nat.prime_two, hf, by omega, fun h => by simp at h; omega⟩
  have hLG := le_ggG0_left p B x L D J
  have hTR : T ∈ (spFrameLift h2 hn2 hT).range := ⟨_, by rw [spFrameLift_simple, spSpecial_zero]⟩
  have hLcl : L ≤ ggClosure (Symplectic.rootDatum (n + 1) (GaloisField 2 f))
      (fun _ : Unit => ggSupp (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) (spLeviJ n))
      (fun _ => spLeviHom φ₁) (spFrameLift h2 hn2 hT).range := by
    rw [← hφL, ← range_spLeviHom φ₁]
    exact range_le_ggClosure (Δ := Symplectic.rootDatum (n + 1) (GaloisField 2 f))
      (S := fun _ : Unit =>
        ggSupp (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) (spLeviJ n))
      (φ := fun _ => spLeviHom φ₁) (R := (spFrameLift h2 hn2 hT).range) ()
  obtain ⟨ψ₀, hpres, hext⟩ := exists_presents_local_ext (t := .PSp) (n := n + 1) (f := f)
    (S := fun _ : Unit => ggSupp (Symplectic.rootDatum (n + 1) (GaloisField 2 f)) (spLeviJ n))
    hadm (by simp only [bnRank]; omega) (by change 2 ≤ n + 1; omega)
    (fun _ => spLeviHom φ₁) (fun _ => spLeviWeyl n)
    (spWeylLift_standardCopy h2) (fun _ γ hγ => hγ.1) (spFrameLift_injective h2 hn2 hT hφ hn3)
    (fun _ _ _ _ _ _ _ => rfl) (fun _ v hv => spWeylLift_mem_levi h2 hv)
    (fun _ v hv => spFrame_eq_ggExt h2 hn2 hT hv)
    (fun _ w j hj => spLevi_refl_mem (by omega) w j hj)
    (by
      intro w _ _ α hα hwα
      obtain ⟨v, hv, hvα⟩ := spLevi_transitive (by omega) w hα hwα
      exact ⟨α, hα, hα, 1, one_mem _, v, hv, by rw [map_one, Module.End.one_apply], hvα⟩)
    (fun w _ α hα hfix z hz => spFrame_hcent h2 hn2 hT hn3 w α hα hfix z hz)
    (spLevi_orbit _ hn) ⟨(), spLevi_hnt hφ (by omega)⟩
    (fun _ => ((range_spLeviHom φ₁).trans hφL).le.trans hLG)
    (spFrameLift_range_le h2 hn2 hT (hφL ▸ hLG) hTG) hLcl
    (by
      intro y K hK
      refine (hnbr y K hK).trans (sup_le hLcl ?_)
      rw [← hφL, ← range_spLeviHom φ₁]
      exact le_iSup_of_le ⟨T, hTR⟩ (le_iSup_of_le () le_rfl))
  refine ⟨ψ₀, hpres, ?_⟩
  have hcomp : ψ₀.comp (spLeviBlock n (GaloisField 2 f)) = φ₁ := by
    ext g
    exact (hext () ⟨spLeviBlock n (GaloisField 2 f) g, spLeviBlock_mem g⟩).trans
      (spLeviHom_apply φ₁ g)
  rw [← hφL, ← hcomp]
  exact ggCompatPresented_spBlock hn3 hf hpres.2.1.2

theorem ggSecFiveCompat_of_typeC (hL : GGSpLiftInput) (hE : GGSpJoinEndNodeInput)
    (hJ : GGSpJoinInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {y : G} {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) (hNoTr : GGNoTransvection p Bs)
    (hN : GGTypeCNbr p B Bs x L D J n f y K) : GGSecFiveCompat p B x L D J := by
  have hperf : commutator L = ⊤ := hcfg.1.2.2.2.2.2.2.2.1.1
  have hf : 1 ≤ f := hN.1.1.2.1
  obtain ⟨φ₁, hφ, hφL⟩ := hL G L n f hN.2.1 hperf hN.1
  obtain ⟨T, hTLK, hT, hKle⟩ := hE G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN φ₁ hφ hφL
  have hTG : T ∈ ggG0 p B x L D J :=
    (sup_le (le_ggG0_left p B x L D J) (le_ggG0_of_ggNbr hN.2.2.2.1)) hTLK
  obtain ⟨ψ₀, hpres, hcomp⟩ := ggSecFiveCompat_of_spEndNode hN.2.1 hf φ₁ hφ hφL hT hTG
    fun y' K' hK' => (hJ G p B Bs x L D J n f y K hcfg hOp hInn hNoTr hN y' K' hK').trans
      (sup_le le_sup_left hKle)
  exact ⟨.PSp, n + 1, f, ψ₀, hpres, L, Or.inl rfl, hcomp⟩

end Presentation

end CFSG.StandardType
