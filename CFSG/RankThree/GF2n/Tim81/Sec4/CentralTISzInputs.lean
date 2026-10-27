module

public import CFSG.RankThree.GF2n.Tim81.Sec4.SzWeaklyClosed
public import CFSG.Blueprint.SourceSuzukiTransport
public import CFSG.Blueprint.SourceGeckCorrespondence
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.GF2n.Tim81.CentralTI

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin.B45Sz
open CFSG.CGT.Timmesfeld75
open CFSG.RankThree.GF2n.Tim81.Sec2
open CFSG.RankThree.GF2n.Tim81.Sec4

variable {a : ℕ} {F : Type} [Field F] [Fintype F] [CharP F 2]

private theorem nonempty_ringEquiv_of_card_eq (hF : Fintype.card F = 2 ^ (2 * a + 1)) :
    Nonempty (F ≃+* GaloisField 2 (2 * a + 1)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite F := Finite.of_fintype F
  haveI : Finite (GaloisField 2 (2 * a + 1)) := inferInstance
  refine CFSG.Blueprint.EvenSource.nonempty_ringEquiv_of_card_eq F _ ?_
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  have hG : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  rw [hF', hG]

noncomputable def szModelEquivOfMulEquiv {X : Type} [Group X]
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a F) :
    X ≃* CFSG.Theory.Comparator.SzModel a :=
  let φ := Classical.choice (nonempty_ringEquiv_of_card_eq (a := a) hF)
  let e₁ : suzukiGroup a F ≃* suzukiGroup a (GaloisField 2 (2 * a + 1)) :=
    CFSG.Blueprint.EvenSource.suzukiGroupMapEquiv a φ
  let hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  let e₂ : suzukiGroup a (GaloisField 2 (2 * a + 1)) ≃*
      CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK
  let e₃ : CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a ≃*
      CFSG.Theory.Comparator.SzModel a :=
    MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a).symm
  e.trans (e₁.trans (e₂.trans e₃))

noncomputable def openSzEquivOfMulEquiv {X : Type} [Group X]
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) (e : X ≃* suzukiGroup a F) :
    X ≃* CFSG.Open.Sz a :=
  (szModelEquivOfMulEquiv hF e).trans
    (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a))

private theorem mem_szZ_iff_mem_szUp_mul_self
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) {s : suzukiGroup a F} :
    s ∈ szZ a F ↔ s ∈ szUp a F ∧ s * s = 1 := by
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  constructor
  · intro hs
    exact ⟨szZ_le_szUp hs, szZ_mul_self hK hs⟩
  · rintro ⟨hs, hsq⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hs
    change (suzukiWElt a F * u * (suzukiWElt a F)⁻¹) *
      (suzukiWElt a F * u * (suzukiWElt a F)⁻¹) = 1 at hsq
    have hu2 : u * u = 1 := by
      calc u * u = (suzukiWElt a F)⁻¹ *
            ((suzukiWElt a F * u * (suzukiWElt a F)⁻¹) *
              (suzukiWElt a F * u * (suzukiWElt a F)⁻¹)) * suzukiWElt a F := by group
        _ = 1 := by rw [hsq]; group
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1
      (CFSG.Quasithin.H13.suzukiU_involution_e34 hK u hu (by simpa [pow_two] using hu2))
    exact (mem_szZ_iff hK).2 ⟨v, rfl⟩

theorem exists_conjSubgroup_szZ_of_involution
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) {x : suzukiGroup a F}
    (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ g : suzukiGroup a F, x ∈ conjSubgroup g (szZ a F) := by
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  let y : suzukiGroup a F :=
    suzukiWElt a F * suzukiSElt a F 0 1 * (suzukiWElt a F)⁻¹
  have hyZ : y ∈ szZ a F := by
    show suzukiWElt a F * suzukiSElt a F 0 1 * (suzukiWElt a F)⁻¹ ∈ szZ a F
    exact (mem_szZ_iff hK).2 ⟨1, rfl⟩
  have hy1 : y ≠ 1 := by
    intro h
    have h1 : suzukiSElt a F 0 1 = 1 := by
      have := congrArg (fun t : suzukiGroup a F =>
        (suzukiWElt a F)⁻¹ * t * suzukiWElt a F) h
      simpa [y, mul_assoc] using this
    rw [← suzukiSElt_zero_zero hK] at h1
    exact one_ne_zero (suzukiSElt_inj.1 h1).2
  have hy2 : y * y = 1 := by
    have h : suzukiSElt a F 0 1 * suzukiSElt a F 0 1 = 1 := by
      rw [suzukiSElt_mul hK, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
        zero_pow (pow_ne_zero _ two_ne_zero), zero_mul, add_zero, suzukiSElt_zero_zero hK]
    calc y * y = (MulAut.conj (suzukiWElt a F))
          (suzukiSElt a F 0 1 * suzukiSElt a F 0 1) := by
          rw [show y = (MulAut.conj (suzukiWElt a F)) (suzukiSElt a F 0 1) from rfl,
            map_mul]
      _ = 1 := by rw [h, map_one]
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rwa [pow_two]) hy1
  obtain ⟨g, hg⟩ := isConj_iff.1
    (CFSG.QuasithinUnique.Setup.Family.suzuki_involutions_conjugate (a := a) (K := F) hK
      x y hxo hyo)
  have hg' : g * x * g⁻¹ = y := by simpa [mul_assoc] using hg
  refine ⟨g⁻¹, ?_⟩
  rw [mem_conjSubgroup]
  show g * x * g⁻¹ ∈ szZ a F
  rw [hg']
  exact hyZ

private theorem inf_conjSubgroup_szZ_eq_bot_of_ne
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) {x y : suzukiGroup a F}
    (hne : conjSubgroup x (szZ a F) ≠ conjSubgroup y (szZ a F)) :
    conjSubgroup x (szZ a F) ⊓ conjSubgroup y (szZ a F) = ⊥ := by
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by
    rw [Nat.card_eq_fintype_card]; exact hF
  have hgoodU : CFSG.Quasithin.H13.E3Good_e34 (suzukiGroup a F) (2 ^ (2 * a + 1))
      (suzukiU a F) := CFSG.Quasithin.H13.good_suzukiU_e34 hK
  have hgoodUp : CFSG.Quasithin.H13.E3Good_e34 (suzukiGroup a F) (2 ^ (2 * a + 1))
      (szUp a F) := by
    simpa [szUp] using CFSG.Quasithin.H13.good_map_e34
      (MulAut.conj (suzukiWElt a F)) _ _ hgoodU
  have hgood (g : suzukiGroup a F) : CFSG.Quasithin.H13.E3Good_e34 (suzukiGroup a F)
      (2 ^ (2 * a + 1)) (conjSubgroup g (szUp a F)) := by
    simpa [conjSubgroup] using CFSG.Quasithin.H13.good_map_e34
      (MulAut.conj g) _ _ hgoodUp
  have hmem (g : suzukiGroup a F) {s : suzukiGroup a F} :
      s ∈ conjSubgroup g (szZ a F) ↔ s ∈ conjSubgroup g (szUp a F) ∧ s * s = 1 := by
    rw [mem_conjSubgroup, mem_conjSubgroup, mem_szZ_iff_mem_szUp_mul_self hF]
    constructor
    · rintro ⟨hs, hsq⟩
      refine ⟨hs, ?_⟩
      have h := congrArg (fun t : suzukiGroup a F => g * t * g⁻¹) hsq
      simpa [mul_assoc] using h
    · rintro ⟨hs, hsq⟩
      refine ⟨hs, ?_⟩
      have h := congrArg (fun t : suzukiGroup a F => g⁻¹ * t * g) hsq
      simpa [mul_assoc] using h
  by_contra hbot
  obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  have hu' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  have huUx : u ∈ conjSubgroup x (szUp a F) := ((hmem x).1 hu.1).1
  have huUy : u ∈ conjSubgroup y (szUp a F) := ((hmem y).1 hu.2).1
  have hUeq : conjSubgroup x (szUp a F) = conjSubgroup y (szUp a F) := by
    by_contra hUne
    have hgN : y * x⁻¹ ∉ Subgroup.normalizer (conjSubgroup x (szUp a F) :
        Set (suzukiGroup a F)) := by
      intro hgN
      have h1 : conjSubgroup (y * x⁻¹) (conjSubgroup x (szUp a F)) =
          conjSubgroup x (szUp a F) := mem_normalizer_iff_conjSubgroup_eq.1 hgN
      have h2 : conjSubgroup (y * x⁻¹) (conjSubgroup x (szUp a F)) =
          conjSubgroup y (szUp a F) := by
        rw [conjSubgroup_conjSubgroup]
        congr 1
        group
      rw [h1] at h2
      exact hUne h2
    have hdisj := (hgood x).2.1 (y * x⁻¹) hgN
    have hdisj' : conjSubgroup x (szUp a F) ⊓
        conjSubgroup (y * x⁻¹) (conjSubgroup x (szUp a F)) = ⊥ := by
      simpa [conjSubgroup] using hdisj
    have h2 : conjSubgroup (y * x⁻¹) (conjSubgroup x (szUp a F)) =
        conjSubgroup y (szUp a F) := by
      rw [conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [h2] at hdisj'
    have hmemu : u ∈ conjSubgroup x (szUp a F) ⊓ conjSubgroup y (szUp a F) :=
      ⟨huUx, huUy⟩
    rw [hdisj', Subgroup.mem_bot] at hmemu
    exact hu' hmemu
  apply hne
  ext s
  rw [hmem x, hmem y, hUeq]

theorem mem_normalizer_conjSubgroup_szZ_of_inf_ne_bot
    (hF : Fintype.card F = 2 ^ (2 * a + 1)) {c g u : suzukiGroup a F} (hu : u ≠ 1)
    (hu1 : u ∈ conjSubgroup c (szZ a F))
    (hu2 : u ∈ conjSubgroup g (conjSubgroup c (szZ a F))) :
    g ∈ Subgroup.normalizer (conjSubgroup c (szZ a F) : Set (suzukiGroup a F)) := by
  rw [mem_normalizer_iff_conjSubgroup_eq]
  by_contra hne
  have hne' : conjSubgroup c (szZ a F) ≠ conjSubgroup (g * c) (szZ a F) := by
    intro h
    exact hne (by rw [conjSubgroup_conjSubgroup]; exact h.symm)
  have hbot := inf_conjSubgroup_szZ_eq_bot_of_ne hF hne'
  have hmem : u ∈ conjSubgroup c (szZ a F) ⊓ conjSubgroup (g * c) (szZ a F) := by
    refine ⟨hu1, ?_⟩
    rwa [conjSubgroup_conjSubgroup] at hu2
  rw [hbot] at hmem
  exact hu (Subgroup.mem_bot.1 hmem)

end CFSG.RankThree.GF2n.Tim81.CentralTI
