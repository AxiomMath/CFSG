module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34ModelL34
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34B
public import CFSG.Quasithin.EmptyFaithful.S153MAR
public import CFSG.Quasithin.EmptyFaithful.T1515dB
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.Quasithin.H13.E54

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank

section L34

variable {L : Type} [Group L]

theorem card_of_lieModel (h : LieModel L .PSL 3 2 2) : Nat.card L = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four (h.statedClassicalModel (by decide))

theorem isSimpleGroup_of_lieModel (h : LieModel L .PSL 3 2 2) : IsSimpleGroup L :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem injective_of_isSimpleGroup {Γ : Type} [Group Γ] (h : LieModel L .PSL 3 2 2)
    (hΓ : IsSimpleGroup Γ) (π : Γ →* L) (hπ : Function.Surjective π) : Function.Injective π := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with hbot | htop
  · exact (MonoidHom.ker_eq_bot_iff π).1 hbot
  · exfalso
    have hL := card_of_lieModel h
    have hsub : Subsingleton L := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      have hx : x ∈ π.ker := by rw [htop]; trivial
      have hy : y ∈ π.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.1 hx, MonoidHom.mem_ker.1 hy]⟩
    rw [Nat.card_of_subsingleton (1 : L)] at hL
    omega

theorem false_of_surjective_sl4 (h : LieModel L .PSL 3 2 2) (π : ↥(StatedSL 4 (ZMod 2)) →* L)
    (hπ : Function.Surjective π) : False := by
  have hs : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) :=
    CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) (by norm_num)
  let e : ↥(StatedSL 4 (ZMod 2)) ≃* L :=
    MulEquiv.ofBijective π ⟨injective_of_isSimpleGroup h hs π hπ, hπ⟩
  obtain ⟨k, _, _, hk, ⟨φ⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel h
  let f : Matrix.SpecialLinearGroup (Fin 3) k →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.toMonoidHom.comp
      (e.symm.toMonoidHom.comp φ.symm.toMonoidHom)).comp
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 k)
  refine CFSG.Quasithin.Vol2.Ch11.SecS.factL34_holds k hk f ?_
  exact (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.surjective.comp
    (e.symm.surjective.comp (φ.symm.surjective.comp
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 k)))

theorem false_of_surjective_sl5 (h : LieModel L .PSL 3 2 2) (π : ↥(StatedSL 5 (ZMod 2)) →* L)
    (hπ : Function.Surjective π) : False := by
  have hs : IsSimpleGroup ↥(StatedSL 5 (ZMod 2)) :=
    CFSG.Quasithin.B69.isSimpleGroup_statedSL_two (by simp) (by norm_num)
  have h1 := Nat.card_congr (Equiv.ofBijective π ⟨injective_of_isSimpleGroup h hs π hπ, hπ⟩)
  rw [card_statedSL_five_zmod1527d, card_of_lieModel h] at h1
  omega

theorem false_of_surjective_sl_zmod (h : LieModel L .PSL 3 2 2) {n : ℕ} (hn : n = 4 ∨ n = 5)
    (π : ↥(StatedSL n (ZMod 2)) →* L) (hπ : Function.Surjective π) : False := by
  rcases hn with rfl | rfl
  · exact false_of_surjective_sl4 h π hπ
  · exact false_of_surjective_sl5 h π hπ

end L34

section Part1

variable {V : Type} [CommGroup V] [Finite V] {J L : Subgroup (MulAut V)}

omit [Finite V] in
theorem false_of_b42ModulePair (h : LieModel ↥L .PSL 3 2 2) {U Z : Subgroup V}
    (hB : B42ModulePair L U Z) : False := by
  have hN : Nat.card ↥L = 20160 ∨ Nat.card ↥L = 9999360 := Or.inl (card_of_lieModel h)
  have hL := card_of_lieModel h
  rcases hB with ⟨n, hB⟩ | ⟨n, hB⟩ | ⟨n, hB⟩ | ⟨n, hB⟩ | hB | hB | hB | hB | hB | hB | hB | hB |
    hB | hB
  · exact not_binaryNaturalSL_two1527d hN hB
  · exact not_binaryNaturalSL_three1527d hN hB
  · exact not_binaryNaturalSp4_1527d hN hB
  · exact not_g2Natural1527d hN hB
  · exact not_g2NaturalDerived_one1527d hN hB
  · exact not_alternatingNatural1527d (n := 5) (by norm_num)
      (by rw [hL]; norm_num [Nat.factorial]) hB
  · exact not_alternatingNatural1527d (n := 6) (by norm_num)
      (by rw [hL]; norm_num [Nat.factorial]) hB
  · exact not_alternatingNatural1527d (n := 7) (by norm_num)
      (by rw [hL]; norm_num [Nat.factorial]) hB
  · exact not_a7Four1527d hN hB
  · exact not_tripleA6Six1527d hN hB
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hB
    exact false_of_surjective_sl4 h π hπ.1
  · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod hB
    exact false_of_surjective_sl5 h π hπ.1
  · obtain ⟨π, hπ⟩ := hB
    exact false_of_surjective_sl4 h π hπ.1
  · obtain ⟨π, hπ⟩ := hB
    exact false_of_surjective_sl5 h π hπ.1

theorem false_of_b51Part1 (h : LieModel ↥L .PSL 3 2 2) (h1 : B51Part1 J L) : False := by
  obtain ⟨-, hc⟩ := h1
  have hN : Nat.card ↥L = 20160 ∨ Nat.card ↥L = 9999360 := Or.inl (card_of_lieModel h)
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · exact false_of_b42ModulePair h hi.2.1
  · obtain ⟨-, n, K, _, _, hK, I, π, -, -, hreal, -⟩ := hii
    exact ne_card_sl3_1527d hK hN (card_eq_of_nat_realizes1527d (hreal 0)).symm
  · obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
    exact false_of_surjective_sl_zmod h hn π hr1.1
  · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact false_of_surjective_sl_zmod h hn π (hreal ⟨0, hk1⟩).1

end Part1

theorem map_pCore_le_pCore {H : Type} [Group H] [Finite H] (N : Subgroup H) [N.Normal] :
    (CFSG.pCore 2 ↥N).map N.subtype ≤ CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCore 2 ?_ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N
  rw [Subgroup.normalizer_eq_top, top_le_iff] at h1
  exact Subgroup.normalizer_eq_top_iff.mp h1

theorem not_isFFModule (h51 : AsB51) {Hg : Type} [Group Hg] [Finite Hg] (hS : SQTKGroup Hg)
    (Kg : Subgroup Hg) [Kg.Normal] (hK : LieModel (↥Kg ⧸ CFSG.pCore 2 ↥Kg) .PSL 3 2 2)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ Kg) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) (ρ : Hg →* MulAut V) (hker : ρ.ker = CFSG.pCore 2 Hg)
    (hnt : ¬ Kg ≤ ρ.ker) : ¬ IsFFModule ρ.range := by
  intro hFF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (↥Kg ⧸ CFSG.pCore 2 ↥Kg) := isSimpleGroup_of_lieModel hK
  have hnc : ∃ a b : ↥Kg ⧸ CFSG.pCore 2 ↥Kg, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup (↥Kg ⧸ CFSG.pCore 2 ↥Kg) :=
      { (inferInstance : Group (↥Kg ⧸ CFSG.pCore 2 ↥Kg)) with mul_comm := hc }
    have hp : (Nat.card (↥Kg ⧸ CFSG.pCore 2 ↥Kg)).Prime := IsSimpleGroup.prime_card
    rw [card_of_lieModel hK] at hp
    norm_num at hp
  have hq : CFSG.IsQuasisimple (↥Kg ⧸ CFSG.pCore 2 ↥Kg) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnc).1
  obtain ⟨hqL, hLX, hn, h2', hO2⟩ := S153M.ar_facts ρ Kg hq hker.ge h2 hnt
  let f : ↥Kg →* ↥(Kg.map ρ) :=
    (ρ.comp Kg.subtype).codRestrict (Kg.map ρ) fun k => ⟨k, k.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hfk : ∀ k : ↥Kg, f k = 1 ↔ (k : Hg) ∈ CFSG.pCore 2 Hg := by
    intro k
    rw [← hker, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hStop : SQTKGroup ↥(⊤ : Subgroup Hg) := by
    refine InternalSec.sqtkGroup_of_surjective (Subgroup.topEquiv (G := Hg)).symm.toMonoidHom
      (Subgroup.topEquiv (G := Hg)).symm.surjective ?_ hS
    intro x
    refine ⟨0, ?_⟩
    have hx : (Subgroup.topEquiv (G := Hg)).symm (x : Hg) = 1 := MonoidHom.mem_ker.mp x.2
    have hx1 : (x : Hg) = 1 :=
      (Subgroup.topEquiv (G := Hg)).symm.injective (hx.trans (map_one _).symm)
    rw [pow_zero, pow_one]
    exact Subtype.ext hx1
  have hSK : SQTKGroup ↥Kg := InternalSec.sqtkGroup_mono hStop le_top
  have hSL : SQTKGroup ↥(Kg.map ρ) := by
    refine InternalSec.sqtkGroup_of_surjective f hf ?_ hSK
    intro x
    have hx : ((x : ↥Kg) : Hg) ∈ CFSG.pCore 2 Hg := (hfk x).mp (MonoidHom.mem_ker.mp x.2)
    have hP : IsPGroup 2 (CFSG.pCore 2 Hg) := by
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨e, he⟩ := hP ⟨_, hx⟩
    refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
    have he' := congrArg Subtype.val he
    simpa using he'
  have hle : CFSG.pCore 2 ↥Kg ≤ f.ker := by
    intro k hk
    rw [MonoidHom.mem_ker, hfk]
    exact map_pCore_le_pCore Kg ⟨k, hk, rfl⟩
  let θ : (↥Kg ⧸ CFSG.pCore 2 ↥Kg) →* ↥(Kg.map ρ) := QuotientGroup.lift _ f hle
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨k, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk k, rfl⟩
  have hθi : Function.Injective θ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff θ).1 hbot
    · exfalso
      apply hnt
      intro k hk
      have h1 : θ (QuotientGroup.mk ⟨k, hk⟩) = 1 := by
        rw [← MonoidHom.mem_ker, htop]
        trivial
      have h2 : f ⟨k, hk⟩ = 1 := h1
      rw [hker]
      exact (hfk ⟨k, hk⟩).mp h2
  have hLie : LieModel ↥(Kg.map ρ) .PSL 3 2 2 :=
    CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (MulEquiv.ofBijective θ ⟨hθi, hθs⟩) hK
  obtain ⟨-, hB51⟩ := S153M.le_ffJ_of_ffModule hV hLX hn h2' hqL hSL hO2 hFF
  exact false_of_b51Part1 hLie (h51 V hV _ _ hB51).1

end CFSG.Quasithin.H13.E54
