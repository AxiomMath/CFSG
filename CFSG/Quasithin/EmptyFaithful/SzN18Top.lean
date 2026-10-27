module

public import CFSG.Quasithin.EmptyFaithful.SzN18Cen
public import CFSG.Quasithin.EmptyFaithful.SzN18Case
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Quot
public import CFSG.Quasithin.EmptyFaithful.SzN17Ctx
public import CFSG.Quasithin.EmptyFaithful.SzN8Decomp
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.Quasithin.Vol2.Ch1Chief

public section

namespace CFSG.Quasithin.SzN18

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

section Yp

variable {G : Type} [Group G] [Finite G]

theorem card_Yp_two_three {Yp : Subgroup G}
    (hs : IsElemAbelianOfRank 3 2 (OTwoQuot Yp) ∨ IsPOnePlusTwo 3 (OTwoQuot Yp)) :
    ∃ a b : ℕ, Nat.card ↥Yp = 2 ^ a * 3 ^ b := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥Yp)).exists_card_eq
  have hQ : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 9 ∨
      Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 27 := (szN8_Q_facts hs).2
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
  rcases hQ with h | h
  · exact ⟨a, 2, by rw [hsplit, h, ha]; ring⟩
  · exact ⟨a, 3, by rw [hsplit, h, ha]; ring⟩

omit [Finite G] in
theorem isPGroup_ker_toBar {I L : Subgroup G} (hLI : L ≤ I) : IsPGroup 2 (toBar hLI).ker := by
  have h := CFSG.QuasithinUnique.Unc25G2.A312Sub.isPGroup_ker_phiOf hLI
  have hk : (toBar hLI).ker = (CFSG.QuasithinUnique.Unc25G2.A312Sub.phiOf hLI).ker :=
    MonoidHom.ker_codRestrict _ _ _
  rwa [hk]

end Yp

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem isQuasisimple_pCoreQuot_of_list
    (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (c : Ctx15313 T Mc M V₁ V₂ Yp I t) (hF : Facts15311 T M V₁ Yp I)
    (hLc : L ∈ cComp (thompsonJ I)) (hLn : ¬ L ≤ M ⊓ I)
    (hLq : CFSG.IsQuasisimple ↥(autOn L (UI153 T I)))
    (hLl : B56QuasisimpleList ↥(autOn L (UI153 T I))) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) :=
    S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hLI
  have hcomm : ⁅L, Yp⁆ = L := S153D.comm_eq_of_quasisimple h37 h38 c hF hLc hLn hLq
  have hY23 := card_Yp_two_three hF.struct_Yp
  have hUN : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLU : L ≤ Subgroup.normalizer (UI153 T I : Set G) := hLle.trans hUN
  obtain ⟨hconc, hcommon, -⟩ := lemma_1_2_1_four_strong c.hyp.hyp.qtfe.qtke
    c.hyp.hyp.qtfe.simple c.hyp.hyp.qtfe.nonabelian h36 c.inH.1.2 hLI
  obtain ⟨e⟩ := modO2_mulEquiv hLI
  have h34 : ¬ (A36Case3 ↥(modO2Image I L) ∨ A36Case4 ↥(modO2Image I L)) := by
    intro h34
    obtain ⟨hgf, hF6⟩ := fitting_primes_of_case34 h34
    refine false_of_fitting_comm hLle hYI hcomm hYL hY23 hF6 ?_ hgf hcommon.2.1
    intro l hl
    set π := InternalSec.autOnHom hLU with hπ
    have hπs : Function.Surjective π := InternalSec.autOnHom_surjective hLU
    set Q : Subgroup ↥L :=
      (CFSG.fittingSubgroup ↥(modO2Image I L)).comap (toBar hLle) with hQdef
    have hQn : Q.Normal := Subgroup.Normal.comap inferInstance _
    have hcop3 : ∀ q ∈ Q, Nat.Coprime (orderOf q) 3 := by
      intro q hq
      have hqF : toBar hLle q ∈ CFSG.fittingSubgroup ↥(modO2Image I L) := hq
      set k := Nat.card ↥(CFSG.fittingSubgroup ↥(modO2Image I L)) with hk
      have h3k : ¬ 3 ∣ k := fun h => (hF6 3 Nat.prime_three h).2 rfl
      have hpow : toBar hLle (q ^ k) = 1 := by
        rw [map_pow]
        have := pow_card_eq_one'
          (G := ↥(CFSG.fittingSubgroup ↥(modO2Image I L))) (x := ⟨toBar hLle q, hqF⟩)
        exact congrArg Subtype.val this
      obtain ⟨j, hj⟩ := isPGroup_ker_toBar hLle (⟨q ^ k, hpow⟩ : ↥(toBar hLle).ker)
      have hqj : q ^ (k * 2 ^ j) = 1 := by
        have := congrArg (fun z : ↥(toBar hLle).ker => (z : ↥L)) hj
        simpa [pow_mul] using this
      have hc : Nat.Coprime (k * 2 ^ j) 3 :=
        Nat.Coprime.mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3k).symm
          (Nat.Coprime.pow_left j (by decide))
      exact hc.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hqj)
    have hN : Q.map π = ⊥ := by
      have : (Q.map π).Normal := hQn.map π hπs
      exact normal_eq_bot_of_coprime_three hLl hLq (Q.map π) fun n hn => by
        obtain ⟨q, hq, rfl⟩ := hn
        exact (hcop3 q hq).coprime_dvd_left (orderOf_map_dvd π q)
    have h1 : π l = 1 := by
      have : π l ∈ Q.map π := ⟨l, hl, rfl⟩
      rw [hN, Subgroup.mem_bot] at this
      exact this
    have hlc : (l : G) ∈ Subgroup.centralizer (UI153 T I : Set G) :=
      (InternalSec.mem_ker_autOnHom hLU l).1 h1
    have hmem : (l : G) ∈ M ⊓ I := hF.cent_le ⟨hLle l.2, hlc⟩
    rw [← hF.norm_eq] at hmem
    exact hmem.2
  rcases hconc with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hcomp.1
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hcomp.1
  · exact absurd (Or.inl h3) h34
  · exact absurd (Or.inr h4) h34

end Main

end CFSG.Quasithin.SzN18

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input15315Two_of_a3
    (h56 : AsB56) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Input15315Two := by
  intro G _ _ T Mc M V₁ V₂ Yp I t c hF
  have hF153 : Facts153 T M V₁ Yp I :=
    { sylow := hF.sylow, cent_le := hF.cent_le, norm_eq := hF.norm_eq, theta := hF.theta,
      star_norm := hF.star_norm, star_lt := hF.star_lt, star_ne := hF.star_ne,
      J_not_le := hF.J_not_le }
  obtain ⟨L, hLc, hLn, hL3, hLq, hLl⟩ :=
    SzN17.exists_cComp_not_le h56 h39 c.hyp c.inH c.charTwo hF153
  exact ⟨L, hLc, hLn, hL3, hLq, SzN18.isQuasisimple_pCoreQuot_of_list h36 h37 h38 c hF hLc hLn hLq hLl⟩

end CFSG.Quasithin
