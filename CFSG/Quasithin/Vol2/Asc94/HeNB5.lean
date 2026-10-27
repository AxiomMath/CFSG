module

public import CFSG.Quasithin.Vol2.Asc94.HeNB2
public import CFSG.Quasithin.Vol2.Asc94.HeNB4
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeCaseProof
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeRCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.LargeExtraspecial Hexa
open Matrix
open scoped MatrixGroups

@[expose] def Sec4HeCaseNB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G) (E F S₁ Q : Subgroup G) (z : G),
    Sec4QNB G A R g E F S₁ Q z → IsSimpleGroup G →
    pCoreOf 2 (centralizer ({z} : Set G)) = Q →
    (∀ X ∈ ({E, F} : Set (Subgroup G)),
        X ≤ iX z X ∧
        (∃ φ : ↥(iX z X) →* Equiv.Perm (Fin 4) × Multiplicative (ZMod 2),
          Function.Surjective φ ∧ φ.ker = X.subgroupOf (iX z X)) ∧
        ¬ iX z X ≤ normalizer (R : Set G) ∧
        Nat.card (Q ⊓ X : Subgroup G) = 16) →
    (∀ X ∈ ({E, F} : Set (Subgroup G)),
      ∃ (ι : ↥X ≃* ↥hexaT) (ψ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G))) →* ↥hexaM),
        Function.Surjective ψ ∧
        ψ.ker = X.subgroupOf (AS76b.oUpperTwoPrime (normalizer (X : Set G))) ∧
        (∀ (ℓ : ↥(AS76b.oUpperTwoPrime (normalizer (X : Set G)))) (x y : ↥X),
          (y : G) = ℓ * x * (ℓ : G)⁻¹ →
            (ι y : Equiv.Perm (Fin 64)) = ψ ℓ * ι x * (ψ ℓ : Equiv.Perm (Fin 64))⁻¹) ∧
        ∀ x : ↥X, (x : G) ∈ R ↔ (ι x : Equiv.Perm (Fin 64)) ∈ hexaR0) →
    (∃ P : Sylow 2 (Carrier .He), Nonempty (S₁ ≃* P)) →
    Nonempty (centralizer ({z} : Set G) ≃*
      centralizer ({DW.cornerTransvection (N := 5) (by norm_num)} : Set (SL(5, ZMod 2)))) →
    IsSporadic G .He

namespace HeTriNB

open CFSG.ComponentClassification.AS81.HeTri
open CFSG.Monster.B.Co2 CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa CFSG.ComponentClassification.AS81.HePres.Native
open CFSG.ComponentClassification.AS81.HePres CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem isSporadic_of_hePiHom_NB
    (hQ : Sec4QNB G A R g E F S₁ Q z) (hs : IsSimpleGroup G)
    (hO2 : pCoreOf 2 (centralizer ({z} : Set G)) = Q) (hRA : R ≤ A)
    (hS₁E : S₁ ≤ normalizer (E : Set G)) (hCE : centralizer (E : Set G) ≤ E)
    (hCz : Nat.card (centralizer ({z} : Set G)) = 21504) (Φ : HePi →* G) (hΦz : Φ hePiZ = z)
    (hCΦ : centralizer ({z} : Set G) ≤ Φ.range)
    (hLΦ : AS76b.oUpperTwoPrime (normalizer (E : Set G)) ≤ Φ.range) {W : Set HePi} {π : HePi}
    (hRΦ : R.comap Φ = (closure W).map (MulAut.conj π).toMonoidHom)
    {M : Subgroup (Equiv.Perm (Fin 8330))}
    (hM : M = (closure ((fun w => (hePiEquivP w : Equiv.Perm (Fin 8330))) '' W)).map
      (MulAut.conj (hePiEquivP π : Equiv.Perm (Fin 8330))).toMonoidHom)
    (hMc : ∀ x ∈ M, x ≠ 1 → x ∈ conjClass heP (heGenPerm 0))
    (hMp : ⁅heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))),
      heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))⁆ =
        heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))))
    (hMn : Nat.card ↥(heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))) = 80640) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .He := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hePi_simple
  have hF := hQ.setting.frame
  have hinj : Function.Injective Φ :=
    HeTri.injective_of_ne_one Φ (x := hePiZ) (by rw [hΦz]; exact hQ.z_ne_one)
  set H := Φ.range with hH
  set e : ↥H ≃* ↥heP := (MonoidHom.ofInjective hinj).symm.trans hePiEquivP
    with he
  set ψP : HePi →* Equiv.Perm (Fin 8330) :=
    heP.subtype.comp hePiEquivP.toMonoidHom with hψP
  have hT : HeEnd.transportHom e = ψP.comp (MonoidHom.ofInjective hinj).symm.toMonoidHom := rfl
  have heΦ : ∀ (a : HePi) (h : Φ a ∈ H), (e ⟨Φ a, h⟩ : Equiv.Perm (Fin 8330)) = ψP a := by
    intro a h
    have : (MonoidHom.ofInjective hinj).symm ⟨Φ a, h⟩ = a := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (MonoidHom.ofInjective_apply hinj).symm
    simp [he, hψP, this]
  have hRM : (R.subgroupOf H).map (HeEnd.transportHom e) = M := by
    rw [hT, HeTri.map_subgroupOf_range_eq, hRΦ, HeTri.map_map_conj, MonoidHom.map_closure, hM]
    rfl
  have hzH : z ∈ H := hCΦ (mem_centralizer_singleton_iff.mpr rfl)
  have hEL : E ≤ AS76b.oUpperTwoPrime (normalizer (E : Set G)) :=
    le_oUpper_of_card le_normalizer (n := 6) (by rw [hF.cardE]; norm_num)
  have hRH : R ≤ H := (hF.R_le_E.trans hEL).trans hLΦ
  have hR1 : R ≠ ⊥ := by
    intro h
    have := hF.cardR
    rw [h, card_bot] at this
    omega
  have hz : ((e ⟨z, hzH⟩ : heP) : Equiv.Perm (Fin 8330)) ∈
      conjClass heP heT1P := by
    have h1 : (e ⟨z, hzH⟩ : Equiv.Perm (Fin 8330)) = heT1P := by
      have := heΦ hePiZ (hΦz ▸ hzH)
      simp only [hΦz] at this
      rw [this, hψP]
      exact hePiEquivP_z
    rw [h1]
    exact ⟨1, heP.one_mem, by group⟩
  have hR : ∀ (r : G) (hr : r ∈ R), r ≠ 1 →
      ((e ⟨r, hRH hr⟩ : heP) : Equiv.Perm (Fin 8330)) ∈
        conjClass heP
          (heGenPerm 0) := by
    intro r hr hr1
    refine hMc _ ?_ ?_
    · rw [← hRM]
      exact ⟨⟨r, hRH hr⟩, mem_subgroupOf.mpr hr, rfl⟩
    · intro h1
      have : e ⟨r, hRH hr⟩ = 1 := Subtype.ext h1
      rw [← map_one e] at this
      exact hr1 (congrArg Subtype.val (e.injective this))
  obtain ⟨hinv, hCr, hAp, hAc⟩ := HeEnd.he_facts e hzH hz hRH hR1 hR (by rw [hRM]; exact hMp)
    (by rw [hRM]; exact hMn)
  have htop := HeEndNB.eq_top hQ hs hO2 hRA hS₁E hCE hCz hCΦ hLΦ hinv hCr hAp hAc
  exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm).trans
    ((MonoidHom.ofInjective hinj).symm.trans hePiEquivHe)⟩

theorem sec4HeCaseNB_of_cent
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11)
    (hRc : ∀ d ∈ heP, ∀ x ∈ (closure {(hePiEquivP (HeTri.heRWordPi 0) : Equiv.Perm (Fin 8330)),
        (hePiEquivP (HeTri.heRWordPi 1) : Equiv.Perm (Fin 8330))}).map (MulAut.conj d).toMonoidHom,
      x ≠ 1 → x ∈ conjClass heP (heGenPerm 0))
    (hRp : ∀ d ∈ heP,
      let M := (closure {(hePiEquivP (HeTri.heRWordPi 0) : Equiv.Perm (Fin 8330)),
        (hePiEquivP (HeTri.heRWordPi 1) : Equiv.Perm (Fin 8330))}).map (MulAut.conj d).toMonoidHom
      ⁅heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))),
        heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))⁆ =
        heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330))))
    (hRn : ∀ d ∈ heP,
      let M := (closure {(hePiEquivP (HeTri.heRWordPi 0) : Equiv.Perm (Fin 8330)),
        (hePiEquivP (HeTri.heRWordPi 1) : Equiv.Perm (Fin 8330))}).map (MulAut.conj d).toMonoidHom
      Nat.card ↥(heP ⊓ centralizer (M : Set (Equiv.Perm (Fin 8330)))) = 80640) :
    Sec4HeCaseNB := by
  intro G _ _ A R g E F S₁ Q z hQ hs hO2 h46a hNX hS₁ hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : HexaFacts := hexaFacts
  have hm : heModelCheck = true := he_modelCheck
  have hg : heGlueCheck = true := he_glueCheck
  have hM : HeModelFacts := heModelFacts_of hm hF
  have hset := hQ.setting
  have hFr := hset.frame
  obtain ⟨hS₁c, hN, hEFS, hS₁I, hIE, hIF⟩ := HeTriNB.sec4He_inputs hE16 h11 hM hQ
    (fun X hX => ⟨(h46a X hX).1, (h46a X hX).2.1⟩) hC
  have hCz := card_centralizer_eq hM hC
  have hz1 := hQ.z_ne_one
  have hzE : z ∈ E := Step46NBAux.z_mem_of_card_NB hQ hQ.normE (h46a E (by simp)).2.2.2
  have hzF : z ∈ F := Step46NBAux.z_mem_of_card_NB hQ hQ.normF (h46a F (by simp)).2.2.2
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hFr.elemE.2 x hx
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => by rw [← sq]; exact hFr.elemF.2 x hx
  obtain ⟨s, fC, hCz', hCB, hCE, hCF, hCEE, -⟩ := exists_normC hM hC hz1 hQ.le_centralizer hS₁c
    hN hEFS hFr.ne hIE hIF hE2 hFr.cardE hF2 hFr.cardF
  obtain ⟨ιE, ψE, hψEs, hψEk, hEeq, hER⟩ := hNX E (by simp)
  obtain ⟨ιF, ψF, hψFs, hψFk, hFeq, -⟩ := hNX F (by simp)
  obtain ⟨fE, -, -, hEP, hEB, -, hE23, cE, hcE⟩ := exists_normX_R hF hM ιE ψE hψEs hψEk hEeq
    hE2 hFr.cardE hzE hz1 hCz (hS₁I.trans inf_le_left) hS₁c (le_sup_right.trans hEFS)
    (hN.trans inf_le_right) hF2 hFr.cardF hFr.ne.symm hFr.R_le_E hER
  obtain ⟨fF, -, -, hFP, hFB, -, hF23, -⟩ := exists_normX hF hM ιF ψF hψFs hψFk hFeq hF2
    hFr.cardF hzF hz1 hCz (hS₁I.trans inf_le_right) hS₁c (le_sup_left.trans hEFS)
    (hN.trans inf_le_left) hE2 hFr.cardE hFr.ne
  obtain ⟨Φ, pN, hΦC, hΦE, hΦz, -, hΦw⟩ := exists_hePiHom hm hg hF s fC fE fF hCz' hCB hCE hCF
    hEP hEB hE23 hFP hFB hF23
  have := hePi_simple
  have hinj : Function.Injective Φ :=
    HeTri.injective_of_ne_one Φ (x := hePiZ) (by rw [hΦz]; exact hz1)
  have hEL : E ≤ AS76b.oUpperTwoPrime (normalizer (E : Set G)) :=
    le_oUpper_of_card le_normalizer (n := 6) (by rw [hFr.cardE]; norm_num)
  have hw : ∀ k < 2, ∃ h : permOfArr 64 (hexaR0Gens.getD k #[]) ∈ heN0,
      Φ (HeTri.heRWordPi k) = (fE (pN * ⟨_, h⟩ * pN⁻¹) : G) := by
    intro k hk
    obtain ⟨hw', he⟩ := hΦw _ (HeTri.heGenWordsR_letters k hk)
    have heq := heGenWordsR_eval hg hk
    refine ⟨heq ▸ hw', ?_⟩
    have h1 : (⟨_, hw'⟩ : ↥heN0) = ⟨_, heq ▸ hw'⟩ := Subtype.ext heq
    rw [HeTri.heRWordPi, he, h1]
  obtain ⟨π, hπ⟩ := HeTri.comap_eq_conj Φ hinj fE hΦE hcE (hFr.R_le_E.trans hEL) (hw 0 (by norm_num))
    (hw 1 (by norm_num))
  have hCE' : centralizer (E : Set G) ≤ E :=
    HeTri.centralizer_le_of_mulEquiv hzE ((hM.EC_le s).trans (hM.P12C_le s).2) fC hCEE (hM.cent_EC s)
  have hd := (hePiEquivP π).2
  exact isSporadic_of_hePiHom_NB hQ hs hO2 (step16 hE16 h11 G A R g E F hFr hset.even).1
    (hN.trans inf_le_left) hCE' hCz Φ hΦz hΦC hΦE hπ (by rw [Set.image_pair]) (hRc _ hd)
    (hRp _ hd) (hRn _ hd)

end HeTriNB

theorem sec4HeCaseNB_of
    {d : L34E16Cert} (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (h11 : Step11) :
    Sec4HeCaseNB :=
  HeTriNB.sec4HeCaseNB_of_cent hE16 h11 (fun _ hd => HePres.heRP_class_conj hd)
    (fun _ hd => HePres.heRP_perfect_conj hd) (fun _ hd => HePres.heRP_card_conj hd)

end CFSG.ComponentClassification.AS81
