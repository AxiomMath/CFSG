module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompSmall
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlock
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitNsKG

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix Multiplicative
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.RankThree.PartTwo.Sec21
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary mem_primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

section Inputs

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggSixSeventeenWitnessDvdOn_PSUNonsplit : GGSixSeventeenWitnessDvdOn GGPSUNonsplit := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx s1 b L₁ hpair hpL
  obtain ⟨rfl, hns⟩ := hP
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  classical
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hβ := hctx.1.2.2.2.2.2.1
  have hp : p.Prime := hβ.1
  have hp2 : p ≠ 2 := hβ.2.1
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set ψ₁ := SURep.ggFrameU hF ψ P₀ hP₀ with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hFk₁ : SURep.GGFrameKer ψ₁ := SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁
  have hC : Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by
    rw [hr₁, hrange]
    exact s1.1
  have hG₀ : ψ₁.range = ggG0 p B x L D J := hr₁.trans hrange
  have hBsel : IsElemAbelian p Bs := hctx.2.1.2.1
  have hEB : ∀ b ∈ Bs, ∃ B', B' ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) ∧
      (b, B') ∈ SUTorus.suPairs ψ₁ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
    refine ⟨P₀ * A * P₀⁻¹,
      SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA),
      SUTorus.mem_suPairs_transfer P₀ hP₀ (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
        hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hlift : ∀ b ∈ Bs, ∃ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      X ^ p = 1 ∧ ψ₁ X = b := fun b hb => by
    obtain ⟨B', hB'U, hB'⟩ := hEB b hb
    exact SUTB.exists_lift h (by omega) hnq hp hns hker₁ hC (hBsel.2 b hb) hB'U hB'
  have hcomm : ∀ X Y : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n), X ^ p = 1 →
      ψ₁ X ∈ Bs → ψ₁ Y ∈ Bs → X * Y = Y * X := fun X Y hXp hX hY =>
    SUNS.commute_of_frame_commute h hFk₁ hp hns hXp (TableB.IsElemAbelian.comm hBsel hX hY)
  let A : Subgroup ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    { carrier := {X | X ^ p = 1 ∧ ψ₁ X ∈ Bs}
      mul_mem' := fun {X Y} hX hY => ⟨by
        rw [(show Commute X Y from hcomm X Y hX.1 hX.2 hY.2).mul_pow, hX.1, hY.1, one_mul], by
          rw [map_mul]; exact Bs.mul_mem hX.2 hY.2⟩
      one_mem' := ⟨one_pow p, by rw [map_one]; exact Bs.one_mem⟩
      inv_mem' := fun {X} hX => ⟨by rw [inv_pow, hX.1, inv_one], by
        rw [map_inv]; exact Bs.inv_mem hX.2⟩ }
  have hmemA : ∀ X, X ∈ A ↔ X ^ p = 1 ∧ ψ₁ X ∈ Bs := fun X => Iff.rfl
  have hA : SUTB.MaxElemAb p A :=
    { prime := hp
      ne_two := hp2
      not_dvd := hns
      pow := fun a ha => ((hmemA a).mp ha).1
      comm := fun a ha b hb => hcomm a b ((hmemA a).mp ha).1 ((hmemA a).mp ha).2
        ((hmemA b).mp hb).2
      max := fun g hgp hga => by
        refine (hmemA g).mpr ⟨hgp, hctx.2.1.2.2.2 (ψ₁ g) ?_ (by rw [← map_pow, hgp, map_one])⟩
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        obtain ⟨X, hXp, rfl⟩ := hlift b hb
        rw [← map_mul, ← map_mul, hga X ((hmemA X).mpr ⟨hXp, hb⟩)] }
  have hcard : p ^ 4 ≤ Nat.card A := by
    have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hβ.2.2.2
    have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hctx.1.2.2.2.2.2.2.1.1.2.1
    have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hctx.2.1.1
    have hsurj : Function.Surjective (fun X : A => (⟨ψ₁ X, ((hmemA X).mp X.2).2⟩ : Bs)) := by
      intro b
      obtain ⟨X, hXp, hXb⟩ := hlift b b.2
      exact ⟨⟨X, (hmemA X).mpr ⟨hXp, hXb ▸ b.2⟩⟩, Subtype.ext hXb⟩
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos hm4
      _ = Nat.card B := hBcard.symm
      _ ≤ Nat.card Bs := hBle
      _ ≤ Nat.card A := Nat.card_le_card_of_surjective _ hsurj
  have huniq : ∀ X ∈ A, ∀ X' ∈ A, ψ₁ X = ψ₁ X' → X = X' := by
    intro X hX X' hX' hXX'
    have hz : ψ₁ (X⁻¹ * X') = 1 := by rw [map_mul, map_inv, hXX', inv_mul_cancel]
    obtain ⟨c, hc⟩ := hFk₁ _ hz
    have hzp : (X⁻¹ * X') ^ p = 1 := hA.pow _ (A.mul_mem (A.inv_mem hX) hX')
    exact inv_mul_eq_one.mp (SUNS.eq_one_of_scalar_mem h hp hns ⟨0, by omega⟩ hc hzp)
  obtain ⟨F⟩ := NsFrameComp.exists_pieceFrame' h hA
  have hιA : ∀ s, F.ι s ∈ A := fun s => by
    have h1 : F.ι s ∈ F.ι.range := ⟨s, rfl⟩
    rwa [F.ι_range] at h1
  have hr : 4 ≤ F.r := by
    have e : Multiplicative (Fin F.r → ZMod p) ≃ A :=
      Equiv.ofBijective (fun s => ⟨F.ι s, hιA s⟩)
        ⟨fun s s' hss => F.ι_injective (congrArg Subtype.val hss), fun a => by
          have ha : (a : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n)) ∈ F.ι.range := by
            rw [F.ι_range]
            exact a.2
          obtain ⟨s, hs⟩ := ha
          exact ⟨s, Subtype.ext hs⟩⟩
    have hcardA : Nat.card A = p ^ F.r := by
      rw [← Nat.card_congr e, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hcardA] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  have hBsι : (ψ₁.comp F.ι).range = Bs := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ((hmemA _).mp (hιA s)).2
    · intro hz
      obtain ⟨X, hXp, hXz⟩ := hlift z hz
      have hX : X ∈ F.ι.range := by
        rw [F.ι_range]
        exact (hmemA X).mpr ⟨hXp, hXz ▸ hz⟩
      obtain ⟨s, hs⟩ := hX
      exact ⟨s, by rw [MonoidHom.comp_apply, hs, hXz]⟩
  obtain ⟨hb, -, hcomp, -⟩ := hpair
  obtain ⟨y₀, hy₀p, hy₀b⟩ := hlift b hb
  have hy₀A : y₀ ∈ A := (hmemA y₀).mpr ⟨hy₀p, hy₀b ▸ hb⟩
  rw [← hG₀, ← hy₀b] at hcomp
  obtain ⟨a, ha, hL₁⟩ :=
    NsFrameComp.exists_eq_map_sb_of_isComponentOf hFk₁ hp hp2 hns hy₀p hcomp hpL
  have hwit : ∀ t' : Fin F.r → ZMod p, t' ≠ 0 → (NsFrameComp.supp t').card ≤ 2 →
      F.ι (ofAdd t') ∈ NsFrameComp.sb h y₀ a →
        ∃ e ∈ L₁, GGSixSeventeenDirect p Bs D (ggG0 p B x L D J) e := by
    intro t' ht0 ht2 htsb
    refine ⟨ψ₁ (F.ι (ofAdd t')), ?_, ?_, ?_, Or.inr ?_⟩
    · rw [hL₁]
      exact Subgroup.mem_map_of_mem _ htsb
    · rw [← hBsι]
      exact ⟨_, rfl⟩
    · intro h1
      have h2 := huniq _ (hιA _) 1 A.one_mem (h1.trans (map_one ψ₁).symm)
      apply ht0
      exact ofAdd_eq_one.mp (F.ι_injective (h2.trans (map_one F.ι).symm))
    · obtain ⟨L₂, hL₂, hL₂c⟩ := NsFrameComp.exists_comp_card_le hA F hFk₁ hr ht2
      refine ⟨L₂, ?_, ?_⟩
      · rw [← hG₀]
        exact hL₂
      · rw [← hBsι]
        exact hL₂c
  refine Or.inr ?_
  by_cases ha1 : (a : Polynomial (GaloisField 2 (2 * (f + 1)))) = Polynomial.X - Polynomial.C 1
  · by_cases hz : ∃ i₀, ∀ u ∈ SUTB.rng (F.y i₀), SUTB.lin y₀ u = u
    ·
      obtain ⟨i₀, hi₀⟩ := hz
      obtain ⟨e, he, hd⟩ := hwit (Pi.single i₀ 1) (fun h0 => by
          have := congrFun h0 i₀
          simp at this) (by
          refine (Finset.card_le_card (s := NsFrameComp.supp (Pi.single i₀ (1 : ZMod p)))
            (t := {i₀}) fun i hi => ?_).trans (by simp)
          rw [NsFrameComp.mem_supp] at hi
          rw [Finset.mem_singleton]
          by_contra hne
          exact hi (by simp [Pi.single_eq_of_ne hne])) (by
          rw [F.ι_single, ha1]
          exact NsFrameComp.mem_sb_zero_of_fix hA F hy₀A i₀ hi₀)
      exact ⟨e, he, Or.inl hd⟩
    ·
      exfalso
      push Not at hz
      have h1 := NsFrameComp.not_dvd_card_sb_zero hA F hy₀A hz
      rw [← ha1] at h1
      apply h1
      have h2 := Subgroup.card_map_dvd (NsFrameComp.sb h y₀ a) ψ₁
      rw [← hL₁] at h2
      exact hpL.trans h2
  ·
    obtain ⟨t', ht0, ht2, htsb⟩ := NsFrameComp.exists_mem_sb_class hA F hy₀A a ha ha1
    obtain ⟨e, he, hd⟩ := hwit t' ht0 ht2 htsb
    exact ⟨e, he, Or.inl hd⟩

end Inputs

end CFSG.StandardType
