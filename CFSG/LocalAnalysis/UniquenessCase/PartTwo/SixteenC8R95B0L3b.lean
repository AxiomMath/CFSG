module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0E1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0L3a
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.FamilyL3TwoElem

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_false_of_embed_P1 {F : Type} [Field F] [Finite F]
    (hq : Nat.card F % 3 = 2) {E : Subgroup (SL3 F)}
    (ι : ↥E →* ↥(P1 : Subgroup (SL3 F))) (hι : Function.Injective ι) (hE : HasL32Quot E) :
    False := by
  obtain ⟨Qm, hQm, π, hπ, hm⟩ := hE
  letI : Group Qm := hQm
  haveI : Finite Qm := Finite.of_surjective π hπ
  obtain ⟨hsimple, hcard⟩ :=
    CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hm
  haveI : IsSimpleGroup Qm := hsimple
  let φ : ↥E →* GL (Fin 2) F := rho1.comp ι
  have hpow : ∀ g ∈ φ.ker, g ^ (Nat.card F ^ 2) = 1 := by
    intro g hg
    have hQ : ((ι g : ↥(P1 : Subgroup (SL3 F))) : SL3 F) ∈ (Q1 : Subgroup (SL3 F)) :=
      mem_ker_rho1.mp hg
    have hx : (⟨((ι g : ↥(P1 : Subgroup (SL3 F))) : SL3 F), hQ⟩ :
        (Q1 : Subgroup (SL3 F))) ^ Nat.card (Q1 : Subgroup (SL3 F)) = 1 := pow_card_eq_one'
    rw [card_Q1] at hx
    have hx' : ((ι g : ↥(P1 : Subgroup (SL3 F))) : SL3 F) ^ (Nat.card F ^ 2) = 1 :=
      congrArg Subtype.val hx
    apply hι
    apply Subtype.ext
    simpa [map_pow] using hx'
  have hker : φ.ker ≤ π.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    haveI hKn : ((φ.ker).map π).Normal :=
      Subgroup.Normal.map (inferInstance : φ.ker.Normal) π hπ
    have hK := IsSimpleGroup.eq_bot_or_eq_top_of_normal ((φ.ker).map π)
    rcases hK with hK | hK
    · have hπg : π g ∈ (φ.ker).map π := Subgroup.mem_map_of_mem π hg
      rw [hK] at hπg
      exact Subgroup.mem_bot.mp hπg
    · exfalso
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hdvd3 : 3 ∣ Nat.card Qm := by rw [hcard]; norm_num
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := Qm) 3 hdvd3
      have hyK : y ∈ (φ.ker).map π := by rw [hK]; exact Subgroup.mem_top y
      obtain ⟨g', hg'ker, hg'y⟩ := Subgroup.mem_map.mp hyK
      have hy3 : y ^ (Nat.card F ^ 2) = 1 := by
        rw [← hg'y, ← map_pow, hpow g' hg'ker, map_one]
      have hdvd : orderOf y ∣ Nat.card F ^ 2 := orderOf_dvd_of_pow_eq_one hy3
      rw [hy] at hdvd
      have h3F : 3 ∣ Nat.card F := Nat.prime_three.dvd_of_dvd_pow hdvd
      have hmod : Nat.card F % 3 = 0 := Nat.mod_eq_zero_of_dvd h3F
      omega
  let ψ : ↥φ.range →* Qm :=
    MonoidHom.liftOfSurjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)
      ⟨π, by rw [MonoidHom.ker_rangeRestrict]; exact hker⟩
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨φ.rangeRestrict x, by simp [ψ]⟩
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨p, f, hp, -, hcard'⟩ := (isPrimePow_nat_iff _).1 (FiniteField.isPrimePow_card F)
  have hFc : Nat.card F = p ^ f := by
    rw [Nat.card_eq_fintype_card]
    exact hcard'.symm
  have h7 : p = 7 := r95_gl2_char_seven hp hFc ψ hψ hm
  rw [h7] at hFc
  have hmod7 : 7 ^ f % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  rw [hFc] at hq
  omega

theorem r95_false_of_transitive_even {F : Type} [Field F] [Finite F] (hF : 2 ∣ Nat.card F)
    {W E : Subgroup (SL3 F)} (hEW : E ≤ W)
    (htr : ∀ v : Fin 3 → F, v ≠ 0 → InOrbit W v) (hb : W ⊓ P1 ⊓ Q1 = ⊥)
    (hE : HasL32Quot E) : False := by
  obtain ⟨R, hRE, hR, a, ha, b, hb', hab⟩ := r95_exists_noncomm_two_subgroup hE
  let T : Subgroup ↥W := (P1 : Subgroup (SL3 F)).subgroupOf W
  have hTidx : ¬ 2 ∣ T.index := by
    have h1 : T.index = Nat.card F ^ 2 + Nat.card F + 1 := by
      change (P1 : Subgroup (SL3 F)).relIndex W = _
      rw [relIndex_P1_of_transitive htr, index_P1]
    rw [h1]
    intro hd
    have hev : 2 ∣ Nat.card F ^ 2 + Nat.card F :=
      dvd_add (dvd_pow hF two_ne_zero) hF
    exact absurd ((Nat.dvd_add_right hev).mp hd) (by norm_num)
  let ι : ↥T →* ↥(P1 : Subgroup (SL3 F)) :=
    ((W.subtype).comp T.subtype).codRestrict _ (fun x => x.2)
  let ρ : ↥T →* GL (Fin 2) F := rho1.comp ι
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hQ : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ (Q1 : Subgroup (SL3 F)) :=
      mem_ker_rho1.mp hx
    have hxW : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ W := (x : ↥W).2
    have hxP : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ (P1 : Subgroup (SL3 F)) :=
      (ι x).2
    have : (((ι x : ↥(P1 : Subgroup (SL3 F))) : SL3 F)) ∈ (⊥ : Subgroup (SL3 F)) :=
      hb ▸ ⟨⟨hxW, hxP⟩, hQ⟩
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp this))
  have hRsub : IsPGroup 2 (R.subgroupOf W) :=
    hR.comap_of_injective W.subtype Subtype.val_injective
  have hcomm : (⟨a, hEW (hRE ha)⟩ : ↥W) * ⟨b, hEW (hRE hb')⟩ =
      ⟨b, hEW (hRE hb')⟩ * ⟨a, hEW (hRE ha)⟩ :=
    CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.two_subgroup_comm_of_odd_index hTidx ρ hρ
      (fun Q hQ => CFSG.AGLEmbeddingD2.McLaughlin.OddIndex.gl2_two_group_comm hF hQ)
      (R := R.subgroupOf W) hRsub
      ⟨a, hEW (hRE ha)⟩ (Subgroup.mem_subgroupOf.mpr ha)
      ⟨b, hEW (hRE hb')⟩ (Subgroup.mem_subgroupOf.mpr hb')
  exact hab (congrArg Subtype.val hcomm)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
