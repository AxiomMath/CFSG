module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthD4KStruct
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructFrame
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructRank
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructKer
import CFSG.LocalAnalysis.StandardType.GGOrthKStructCompAux
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructTransfer
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructNormalizer
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructAutomizer
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructWeylB
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructFixed
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructClass4
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylInduced
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf CFSG.StandardType.SpJoin
  CFSG.LieType.Universal.SpecialLinear Matrix

theorem ggSecFiveOrthD4KStructInput_holds :
    GGSecFiveOrthD4KStructInput := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit hC1 hp3 V _ _ Q hQnd hFact ι hdim hQ hAL y K hnb hK hJ hJf
  subst hp3
  have hB : GGBstar 3 B Bs := hcfg.1.1.2.1
  have hinn : GGInnerDiagOn Bs K := hcfg.1.2.2.1.2 y K hnb
  have hcard : Nat.card Bs = 3 ^ 5 := by
    haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
    haveI : Fintype V := Fintype.ofFinite V
    haveI : Fact (Nat.Prime 3) := hFact
    calc Nat.card Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card V := Nat.card_congr ι.toEquiv
      _ = Fintype.card V := Nat.card_eq_fintype_card
      _ = Fintype.card (ZMod 3) ^ Module.finrank (ZMod 3) V :=
            Module.card_eq_pow_finrank (K := ZMod 3) (V := V)
      _ = 3 ^ 5 := by rw [ZMod.card, hdim]
  have hyf : y ∈ Bs ∧ y ≠ 1 ∧ ∀ k ∈ K, y * k = k * y := by
    refine ⟨hB.1 hnb.1.2.1, hnb.1.2.2.1, ?_⟩
    intro k hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hnb.1.2.2.2.1 hk)).symm
  obtain ⟨m, hm8, ⟨e⟩⟩ := hK
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  obtain ⟨ψ, hψ⟩ := ggOrthKStruct_frame hB hinn (by omega) e
  obtain ⟨hk4, hprod, hCb⟩ := ggOrthKStruct_rank hψ (by omega) hB.2.1 hcard hyf.1 hyf.2.1 hyf.2.2
  obtain ⟨Φ, hΦ⟩ := exists_torusCoord n
  have hup := ggOrthKStruct_automizer hψ (by omega) hprod Φ hΦ
  have hlow : ∀ h ∈ spSignedGroup ((n + 1) / 2) 3, ∃ σ ∈ ggAutomizer K Bs, InducesSigned K ψ Φ σ h :=
    fun h hh => hψ.exists_aut_signed Φ hΦ h hh
  refine ⟨?_, ggOrthKStruct_fixed hψ hprod hCb Φ hΦ hlow, ?_⟩
  · have hw := ggOrthKStruct_weylB hψ (by omega) hprod Φ hΦ hup hlow
    rwa [hk4] at hw
  · intro φ hφ hcl hx
    obtain ⟨t, htT, hxt⟩ := hψ.act x hx
    obtain ⟨a, ha⟩ := Φ.surjective ⟨t, htT⟩
    have hta : (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) = t := congrArg Subtype.val ha
    have hcK : (ψ t)⁻¹ * x ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h := hxt l hl
      calc l * ((ψ t)⁻¹ * x) = (ψ t)⁻¹ * (ψ t * l * (ψ t)⁻¹) * x := by group
        _ = (ψ t)⁻¹ * (x * l * x⁻¹) * x := by rw [← h]
        _ = ((ψ t)⁻¹ * x) * l := by group
    have hxac : x = ψ (Φ a : SpecialLinearGroup (Fin (n + 1)) F2) * ((ψ t)⁻¹ * x) := by
      rw [hta]; group
    obtain ⟨J', hJ', hJf'⟩ := ggOrthKStruct_transfer hψ.range hψ.inj hxt hJ hJf
    have hker := okComp_main hRig t (halfTorus_pow_three htT) hJ' hJf'
    have hcount := ggOrthKStruct_ker Φ hΦ a
    have hall : ∀ j, a j ≠ 1 := by
      rw [hta] at hcount
      have hcard4 : (Finset.univ.filter fun j => a j ≠ 1).card = 4 := by
        have h2 : 2 * (Finset.univ.filter fun j => a j ≠ 1).card = 8 := by
          rw [← hcount]
          exact hker
        omega
      have huniv : (Finset.univ.filter fun j => a j ≠ 1) = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hcard4, Fintype.card_fin, hk4]
      intro j
      have hj : j ∈ Finset.univ.filter (fun j => a j ≠ 1) := by
        rw [huniv]
        exact Finset.mem_univ j
      exact (Finset.mem_filter.mp hj).2
    exact ggOrthKStruct_class4 hψ hk4 hprod Φ hΦ hup hlow hx a _ hcK hxac hall φ hφ hcl

end CFSG.StandardType

end
