module

public import CFSG.RankThree.PartOne.KE.E6FourData
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE6FourPerX
public import CFSG.RankThree.PartOne.KE6.Phi3Solvable
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitE6Gen
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitComponentEmbed

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne
open CFSG.RankThree.E6 (chainRoot weylMatrix e6Index)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Assembly (IsComponentOf)
open scoped Matrix MatrixGroups

namespace NonsplitLayers


theorem e6_four_components_dvd (K : Type) [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    (n : ModGL .E6 L) (hnm : n ∈ monomialSubgroup .E6 L)
    (hnW : ∀ u, weylQuotientHom .E6 L ⟨n, hnm⟩ • u = (weylMatrix e6F4U) *ᵥ u) :
    ∀ x : adjointGroup .E6 K, orderOf x = p →
      ∀ X : Subgroup (adjointGroup .E6 K),
        IsComponentOf X (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) →
          p ∣ Nat.card X := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_four_frame K hf hK hp hp3 hpq L n hnm hnW
  intro x hx X hX
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, -, hψ⟩ := CFSG.RankThree.PartOne.KE.e6_four_perx_odd K hf hK hp hp3 hordq hΦ L n
    hnm hnW g0 hg0C hg0 hperf hT hx c hh
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
  obtain ⟨hreg, hnonreg⟩ := hψ b hb.symm
  rcases (rootCharKernel b).eq_empty_or_nonempty with hA | hne
  ·
    exfalso
    have hcomm : ∀ a a' : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))),
        a * a' = a' * a := by
      intro a a'
      apply hψinj
      rw [map_mul, map_mul]
      exact CFSG.RankThree.PartOne.KE6.phi3_torusGroup_comm _ (hreg hA a) _ (hreg hA a')
    haveI : Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) :=
      Group.isSolvable_of_comm hcomm
    exact CFSG.StandardType.ExcNonsplit.not_isComponentOf_of_isSolvable hX
  ·
    obtain ⟨Pt, hPtq, hPtc, hcent, Y₀, hY₀, hY₀o⟩ := hnonreg hne
    have hPle : Pt ≤ ψ.range := by
      rw [← hPtc]
      exact Subgroup.commutator_le.2 fun a ha b hb => by
        rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    have hnorm : ∀ d : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), ∀ u ∈ Pt,
        ψ d * u * (ψ d)⁻¹ ∈ Pt := by
      intro d u hu
      have h1 : ψ.range.map (MulAut.conj (ψ d)).toMonoidHom ≤ ψ.range := by
        rintro _ ⟨v, hv, rfl⟩
        exact mul_mem (mul_mem ⟨d, rfl⟩ hv) (inv_mem ⟨d, rfl⟩)
      have h2 : Pt.map (MulAut.conj (ψ d)).toMonoidHom ≤ Pt := by
        rw [← hPtc, Subgroup.map_commutator]
        exact Subgroup.commutator_mono h1 h1
      exact h2 ⟨u, hu, rfl⟩
    refine CFSG.StandardType.E6Nonsplit.dvd_card_of_isComponentOf_of_layers ψ hψinj
      (fun _ : Unit => Pt) (fun _ => hPle) (fun _ => hPtq) (fun _ d u hu => hnorm d u hu)
      (Z := (torusGroup .E6 L : Set (ModGL .E6 L)))
      (fun a ha b' hb' => CFSG.RankThree.PartOne.KE6.phi3_torusGroup_comm a ha b' hb')
      (fun d hd => hcent (ψ d) ⟨d, rfl⟩ (fun u hu => hd () u hu)) (fun _ => ?_) hX
    rw [← hY₀o, ← Subgroup.orderOf_mk Y₀ hY₀]
    exact orderOf_dvd_natCard _

end NonsplitLayers

end CFSG.RankThree.PartOne.KE
