module

public import CFSG.LocalAnalysis.StandardType.GGFrameRouteNbrDefs
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly TableB

theorem fix_mem_centralizer_of_noFix {G : Type} [Group G] [Finite G]
    {p r : ℕ} (hp : p.Prime) {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hX : commutator X = ⊤) {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R)
    {I : Set (MulAut R)} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hr : p ^ r ≤ Nat.card (ggGamma X hBsN).range)
    (h3 : p ^ 3 ≤ Nat.card (ggGamma X hBsN).range)
    (hT : GGTorusNoFix p r R I) (b : Bs) (hb : ∀ φ ∈ ggAutomizer X Bs, φ b = b) :
    (b : G) ∈ Subgroup.centralizer (X : Set G) := by
  classical
  have := Fact.mk hp
  set γ := ggGamma X hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : X, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta X θ hBsN b, ggBeta_mem X θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom X hBsN θ b l⟩
  rw [← ggGamma_eq_one_iff X hBsN]
  refine hT X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hX γ.range hA hAI
    hr h3 (γ b) ⟨b, rfl⟩ ?_
  intro n hn
  have hWB : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨htp, htA⟩ := hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : X) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hnN : (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB w hw)
    simpa using Subgroup.inv_mem _ h
  have hφ : Bs.normalizerMonoidHom ⟨n, hnN⟩ ∈ ggAutomizer X Bs :=
    Subgroup.subset_closure ⟨(n : G), n.2, hnN, fun _ => rfl⟩
  have hnb : (n : G) * b * (n : G)⁻¹ = b := congrArg Subtype.val (hb _ hφ)
  have hc := ggGamma_conj X hBsN n b (hWB b b.2)
  rw [← hγ] at hc
  rw [← hc]
  congr 1
  exact Subtype.ext hnb

end CFSG.StandardType.FrameRoute
