module

public import CFSG.Quasithin.Recognition.Stroth.SliceSzUReduction
public import CFSG.Quasithin.Recognition.Stroth.Y9Transport
public import CFSG.Quasithin.Recognition.GoldschmidtF112RG24
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Local
public import CFSG.Quasithin.Vol2.E2NinePullback
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced
public import CFSG.Quasithin.H13.A7Nat1238Setup
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Orient3
public import CFSG.Quasithin.Background.C35InspF4A
public import CFSG.Quasithin.H13.L32NLem14331g
public import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.Sec53F CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.BorelTits CFSG.AGLEmbedding
open scoped commutatorElement

private theorem sz_factorization_two (a : ℕ) :
    (Nat.card (Sz a)).factorization 2 = 2 * (2 * a + 1) := by
  rw [CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_sz a]
  set q := 2 ^ (2 * a + 1) with hq
  have hq2 : q ^ 2 = 2 ^ (2 * (2 * a + 1)) := by rw [hq, ← pow_mul, mul_comm]
  have hqpos : 0 < q := by positivity
  have hodd1 : Odd (q ^ 2 + 1) := by
    have he : Even (q ^ 2) := by
      rw [hq2]
      exact Even.pow_of_ne_zero (by norm_num) (by omega)
    exact he.add_one
  have hodd2 : Odd (q - 1) := by
    have he : Even q := by
      rw [hq]
      exact Even.pow_of_ne_zero (by norm_num) (by omega)
    exact Nat.Even.sub_odd hqpos he odd_one
  have hprod1 : (q ^ 2 * (q ^ 2 + 1)) ≠ 0 := by positivity
  have hprod2 : (q ^ 2 * (q ^ 2 + 1) * (q - 1)) ≠ 0 :=
    mul_ne_zero hprod1 (by omega)
  have h1 : (q ^ 2 + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      simpa [Nat.two_dvd_ne_zero] using hodd1.not_two_dvd_nat)
  have h2 : (q - 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      simpa [Nat.two_dvd_ne_zero] using hodd2.not_two_dvd_nat)
  rw [Nat.factorization_mul hprod1 (by omega)]
  rw [Nat.factorization_mul (by positivity) (by omega)]
  show (q ^ 2).factorization 2 + (q ^ 2 + 1).factorization 2 + (q - 1).factorization 2 =
    2 * (2 * a + 1)
  rw [h1, h2, hq2, Nat.Prime.factorization_pow Nat.prime_two]
  simp

private theorem card_sylow_sz {a : ℕ} (ha : 1 ≤ a)
    (P : Sylow 2 (Sz a)) :
    Nat.card (P : Subgroup (Sz a)) = (2 ^ (2 * a + 1)) ^ 2 := by
  rw [Sylow.card_eq_multiplicity P, sz_factorization_two a, ← pow_mul]
  ring_nf

private theorem index_normalizer_sz {a : ℕ} (ha : 1 ≤ a)
    {T : Subgroup (Sz a)} (hp : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.index) :
    (Subgroup.normalizer (T : Set (Sz a))).index = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  let P := hp.toSylow hodd
  have hP : (P : Subgroup (Sz a)) = T := rfl
  have h := P.card_eq_index_normalizer
  rw [CFSG.ComponentClassification.Asc76X.card_sylow_of_mulEquiv_sz ha
    (MulEquiv.refl (Sz a)) P, card_sylow_sz ha P] at h
  rw [← hP]
  exact h.symm

private theorem isPerfect_sz {a : ℕ} (ha : 1 ≤ a) :
    Group.IsPerfect ↥(Sz a) := by
  obtain ⟨e⟩ :=
    CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hperf := (CFSG.LieType.Ree.suzuki_perfect (a := a)
    (K := GaloisField 2 (2 * a + 1)) ha hK).2
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem index_borelOf_of_sz {G : Type} [Group G] [Finite G]
    {L S : Subgroup G} {a : ℕ} (ha : 1 ≤ a) (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (e : oTwoQuot ↥L ≃* Sz a) :
    ((borelOf L S).subgroupOf L).index = (2 ^ (2 * a + 1)) ^ 2 + 1 := by
  obtain ⟨hp, hodd, hmap⟩ := CFSG.Quasithin.F1.map_borelOf_eq_normalizer hsyl
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ (borelOf L S).subgroupOf L := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (CFSG.Quasithin.F1.mem_pCore_iff_coe x).mp hx
    exact CFSG.Quasithin.F1.sylow_le_borelOf L S (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hsyl h1)
  rw [← Subgroup.index_map_eq _ hsurj hker, hmap]
  set Tb : Subgroup (oTwoQuot ↥L) := Subgroup.map π ((S ⊓ L).subgroupOf L) with hTb
  have hT' : IsPGroup 2 (Tb.map e.toMonoidHom) := hp.map e.toMonoidHom
  have hodd' : ¬ 2 ∣ (Tb.map e.toMonoidHom).index := by
    rw [show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv]
    exact hodd
  have h5 := index_normalizer_sz ha hT' hodd'
  rw [← Subgroup.map_normalizer_eq_of_bijective Tb e.bijective,
    show e.toMonoidHom = (e : oTwoQuot ↥L →* _) from rfl, Subgroup.index_map_equiv] at h5
  exact h5

private theorem map_pCore_perfectCore_Pg
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount) :
    (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a j))).map
        (F4.reeGamma K a).subtype =
      F4.reeFixedOrbitComplementUnipotent K a j := by
  have hpc : perfectCore (H13.F431.TwoF4.Pg K a j) =
      (perfectCore (F4.reeLocalParabolic K a j)).subgroupOf (F4.reeGamma K a) := by
    ext x
    change x ∈ perfectCore ((F4.reeLocalParabolic K a j).subgroupOf (F4.reeGamma K a)) ↔
      x ∈ (perfectCore (F4.reeLocalParabolic K a j)).subgroupOf (F4.reeGamma K a)
    exact CFSG.Quasithin.H13.Sec53F.ReeF4.mem_perfectCore_subgroupOf
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma j) x
  rw [hpc]
  have hle : perfectCore (F4.reeLocalParabolic K a j) ≤ F4.reeGamma K a :=
    (perfectCore_le _).trans (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma j)
  rw [CFSG.Quasithin.H13.L14331.map_pCoreOf_subgroupOf' (I := F4.reeGamma K a)
    (X := perfectCore (F4.reeLocalParabolic K a j)) hle]
  exact CFSG.Quasithin.C35Pf.pCoreOf_perfectCore_f4 ha hK j

private theorem card_pCore_perfectCore_Pg_one
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))) =
      (2 ^ (2 * a + 1)) ^ 10 := by
  rw [← Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective,
    map_pCore_perfectCore_Pg ha hK ⟨1, by decide⟩]
  exact (CFSG.LieType.Ree.LargeReeInvolution.card_complement_two_and_centralizerZ
    (K := K) (a := a) ha hK
    (CFSG.LieType.Ree.LargeReeInvolution.card_reeFixedPosUnipotent hK)).1

private theorem card_pCore_perfectCore_Pg_zero
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))) =
      (2 ^ (2 * a + 1)) ^ 11 := by
  rw [← Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective,
    map_pCore_perfectCore_Pg ha hK ⟨0, by decide⟩]
  have h := CFSG.LieType.Ree.LargeReeInvolution.card_reeFixedPosUnipotent_eq_mul
    (K := K) (a := a) (j := ⟨0, by decide⟩)
  let j0 : Fin F4.fixedOrbitCount := ⟨0, by decide⟩
  have h0 : Nat.card (F4.reeFixedOrbitUnipotent K a j0) = 2 ^ (2 * a + 1) := by
    change Nat.card (F4.reeFixedOrbitUnipotent K a ⟨0, by decide⟩) = 2 ^ (2 * a + 1)
    rw [CFSG.LieType.Ree.ReeTag.card_reeFixedOrbitUnipotent_zero (K := K) (a := a) hK, hK]
  rw [CFSG.LieType.Ree.LargeReeInvolution.card_reeFixedPosUnipotent hK, h0] at h
  have hq : 0 < 2 ^ (2 * a + 1) := by positivity
  rw [show (2 ^ (2 * a + 1)) ^ 12 = (2 ^ (2 * a + 1)) ^ 11 * (2 ^ (2 * a + 1)) by ring] at h
  exact Nat.eq_of_mul_eq_mul_right hq h.symm

private theorem centerOf_Ug_le_centralizer_perfectCore_one
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    centerOf (H13.F431.TwoF4.Ug K a) ≤
      Subgroup.centralizer (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) :
        Set (H13.F431.TwoF4.Gm K a)) := by
  intro z hz
  obtain ⟨c, hc⟩ : ∃ c : K, centralZ K a c = (z : ModGL F4.tag K) := by
    have hzU : (z : ModGL F4.tag K) ∈ F4.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hz.1
    have hzc : (⟨(z : ModGL F4.tag K), hzU⟩ : ↥(F4.reeFixedPosUnipotent K a)) ∈
        Subgroup.center ↥(F4.reeFixedPosUnipotent K a) := by
      rw [Subgroup.mem_center_iff]
      intro u
      apply Subtype.ext
      have huΓ : (u : ModGL F4.tag K) ∈ F4.reeGamma K a :=
        CFSG.LieType.Ree.ReeTag.reeFixedPosUnipotent_le_reeGamma u.2
      have huUg : (⟨(u : ModGL F4.tag K), huΓ⟩ : H13.F431.TwoF4.Gm K a) ∈
          H13.F431.TwoF4.Ug K a := Subgroup.mem_subgroupOf.2 u.2
      simpa using congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hz.2 _ huUg)
    have hzc' : (z : ModGL F4.tag K) ∈
        ((Subgroup.center (F4.reeFixedPosUnipotent K a)).map
          (F4.reeFixedPosUnipotent K a).subtype : Set (ModGL F4.tag K)) :=
      ⟨⟨(z : ModGL F4.tag K), hzU⟩, hzc, rfl⟩
    rw [coe_center_eq_range_centralZ ha hK] at hzc'
    exact hzc'
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : (g : ModGL F4.tag K) ∈ perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) :=
    (CFSG.Quasithin.H13.Sec53F.ReeF4.mem_perfectCore_subgroupOf
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma _) g).1 hg
  have hcomm := H13.F431.TwoF4.perfectCore_one_commute_centralZ ha hK hg' c
  apply Subtype.ext
  simpa [← hc] using hcomm

private lemma y9_standard_position
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    (hA : IsAmalgamOfGroup (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S) (IsTwistedF4Over (2 * a + 1)))
    (ha : 1 ≤ a) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime)
      (_ : Nat.card K = 2 ^ (2 * a + 1))
      (Y : Type) (_ : Group Y) (M1 M2 : Subgroup Y)
      (ε : Y ≃* H13.F431.TwoF4.Gm K a)
      (_ : (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S).Iso (RankTwoAmalgam.ofSubgroups M1 M2)),
      (M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ∧
        M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) ∨
      (M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ∧
        M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
  obtain ⟨Y, hGroupY, hY, _, M1, M2, hpair, ⟨iso0⟩⟩ := hA
  letI := hGroupY
  have hD : CFSG.Blueprint.LieModel Y .twistedF4 0 2 (2 * a + 1) := by
    rcases hY with ⟨h1, -⟩ | h
    · exact absurd h1 (by omega)
    · exact h.2.2
  obtain ⟨a0, K, hFieldK, hFinK, hCharK, _, hfa, hK0, ⟨e⟩⟩ :=
    H13.F431.TwoF4.f4_model_data hD
  have haa : a0 = a := by omega
  subst a0
  letI := hFieldK
  letI := hFinK
  letI := hCharK
  haveI : Finite (H13.F431.TwoF4.Gm K a) := H13.F431.TwoF4.finite_gm K a
  obtain ⟨c, _, hP⟩ := (CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK0).pair e hpair
  let ε : Y ≃* H13.F431.TwoF4.Gm K a := e.trans (MulAut.conj c⁻¹)
  have hε : ∀ S : Subgroup Y, S.map ε.toMonoidHom =
      (S.map e.toMonoidHom).map (MulAut.conj c⁻¹).toMonoidHom := fun S => by
    rw [Subgroup.map_map]
    rfl
  have hPε :
      (M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ∧
        M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) ∨
      (M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ∧
        M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [hε, hε, h1, h2, H13.F431.TwoF4.map_conj_inv_map_aux,
        H13.F431.TwoF4.map_conj_inv_map_aux]
      exact ⟨rfl, rfl⟩
    · right
      rw [hε, hε, h1, h2, H13.F431.TwoF4.map_conj_inv_map_aux,
        H13.F431.TwoF4.map_conj_inv_map_aux]
      exact ⟨rfl, rfl⟩
  exact ⟨K, hFieldK, hFinK, hCharK, hK0, Y, hGroupY, M1, M2, ε, iso0, hPε⟩

private lemma y9_index_orientation
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {Y : Type} [Group Y] {M1 M2 : Subgroup Y}
    {ε : Y ≃* H13.F431.TwoF4.Gm K a}
    (hF : F112Hyp L1 L2 S) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (iso0 : (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S).Iso (RankTwoAmalgam.ofSubgroups M1 M2))
    (hM : (M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ∧
            M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) ∨
           (M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ∧
            M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)) :
    Hyp111R L1 L2 S ∧
      bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) ∧
      bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) ∧
      M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ∧
      M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ∧
      (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S ∧
      H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓ H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ =
        Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := by
  classical
  set q : ℕ := 2 ^ (2 * a + 1) with hq
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    (CFSG.Quasithin.F112R.bigB_le_normalizer hF.1).1
  have hB2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    (CFSG.Quasithin.F112R.bigB_le_normalizer hF.1).2
  have hLB1 : L1 ⊓ bigB L1 L2 S = borelOf L1 S := F1.inf_bigB_eq_borelOf hR
  have hLB2 : L2 ⊓ bigB L1 L2 S = borelOf L2 S := by
    have := F1.inf_bigB_eq_borelOf hR.symm
    rwa [bigB_comm] at this
  have hP1P2 : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S :=
    (CFSG.Quasithin.prop_F19_of_hyp111 (G := G) (L1 := L1) (L2 := L2) (S := S)
      hF.1).1
  have hIdx1 : (borelOf L1 S).relIndex L1 = q ^ 2 + 1 := by
    have := index_borelOf_of_sz ha hF.1.h1.sylow (Classical.choice hSz)
    simpa [hq, Subgroup.relIndex] using this
  have hrel1 : (bigB L1 L2 S).relIndex (L1 ⊔ bigB L1 L2 S) = q ^ 2 + 1 := by
    rw [F112W.relIndex_sup_eq_relIndex_inf hB1]
    simpa [hLB1] using hIdx1
  obtain ⟨_, _, _, _, _, hi0, _⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK
  have hi0' : (Subgroup.normalizer (H13.F431.TwoF4.Ug K a)).relIndex
      (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) = q + 1 := by
    simpa [H13.F431.TwoF4.Ug, H13.F431.TwoF4.Pg, hq, hK] using hi0
  have hYam := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  have hinf : H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
      H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ = Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := by
    have hLie := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_lieFactsOf ha hK
    exact le_antisymm hLie.2.1 (le_inf hYam.le₀ hYam.le₁)
  have hPε' : M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ∧
      M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ := by
    rcases hM with ⟨h1, h2⟩ | h
    · exfalso
      have hεinj : Function.Injective ε.toMonoidHom := ε.injective
      let e1 : (RankTwoAmalgam.ofSubgroups M1 M2).G1 ≃*
          ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) :=
        (M1.equivMapOfInjective ε.toMonoidHom hεinj).trans (MulEquiv.subgroupCongr h1)
      have he1 : ∀ x : (RankTwoAmalgam.ofSubgroups M1 M2).G1,
          (e1 x : H13.F431.TwoF4.Gm K a) = ε x.1 := fun x => rfl
      have hQ : (M1 ⊓ M2).map ε.toMonoidHom =
          H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
            H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ := by
        rw [Subgroup.map_inf_eq _ _ _ hεinj, h1, h2]
      have hBimg := iso_map_inter_of_equiv iso0 ε e1 hQ he1
      rw [show (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S from hP1P2]
        at hBimg
      have h1idx := Subgroup.index_map_equiv
        ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)) (iso0.φ1.trans e1)
      change ((Subgroup.map (iso0.φ1.trans e1).toMonoidHom
        ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S))).index =
          ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).index) at h1idx
      rw [hBimg] at h1idx
      have h2idx : ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).index = q ^ 2 + 1 :=
        hrel1
      have h3idx : ((H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
          H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subgroupOf
            (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)).index = q + 1 := by
        change (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
          H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).relIndex
            (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) = q + 1
        rw [hinf]
        exact hi0'
      rw [h2idx] at h1idx
      rw [h3idx] at h1idx
      have hq8 : 8 ≤ q := by
        rw [hq]
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith [hq8]
    · exact h
  exact ⟨hR, hB1, hB2, hPε'.1, hPε'.2, hP1P2, hinf⟩

private lemma y9_vertex_one_iso
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    {Y : Type} [Group Y] {M1 M2 : Subgroup Y}
    {ε : Y ≃* H13.F431.TwoF4.Gm K a}
    (hP1P2 : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S)
    (hM1ε : M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)
    (hM2ε : M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)
    (iso0 : (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S).Iso (RankTwoAmalgam.ofSubgroups M1 M2)) :
    ∃ ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩),
      ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ⊓
          H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subgroupOf
            (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
  have hεinj : Function.Injective ε.toMonoidHom := ε.injective
  let e1 : (RankTwoAmalgam.ofSubgroups M1 M2).G1 ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) :=
    (M1.equivMapOfInjective ε.toMonoidHom hεinj).trans (MulEquiv.subgroupCongr hM1ε)
  let ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := iso0.φ1.trans e1
  have hQ1 : (M1 ⊓ M2).map ε.toMonoidHom =
      H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ⊓
        H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ := by
    rw [Subgroup.map_inf_eq _ _ _ hεinj, hM1ε, hM2ε]
  have hBimg1 : ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ⊓
        H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subgroupOf
          (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
    have h := iso_map_inter_of_equiv iso0 ε e1 hQ1 (fun x => rfl)
    rwa [show (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S from hP1P2]
      at h
  exact ⟨ψ1, hBimg1⟩

private lemma y9_vertex_one_sylow
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (hR : Hyp111R L1 L2 S)
    (hinf : H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
      H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ = Subgroup.normalizer (H13.F431.TwoF4.Ug K a))
    {ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)}
    (hBimg1 : ((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ⊓
        H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subgroupOf
          (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)) :
    IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) ∧
      (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
        (H13.F431.TwoF4.Ug K a).subgroupOf (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
  have hSyl := CFSG.GH74.QTGen4.DSGen4.leafSylowS (G := G) hR
  have hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S) := hSyl.2.1
  have hYam := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  obtain ⟨hsylU, _, _, _, _, _, _⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK
  have hUglePg1 : H13.F431.TwoF4.Ug K a ≤ H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ :=
    Subgroup.le_normalizer.trans hYam.le₁
  have hUgSylP1 : IsSylowTwoOf (H13.F431.TwoF4.Ug K a)
      (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) :=
    F7.isSylowTwoOf_mono_right hsylU hUglePg1 le_top
  have hUgleN : H13.F431.TwoF4.Ug K a ≤
      Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := Subgroup.le_normalizer
  have hUgSylN : IsSylowTwoOf (H13.F431.TwoF4.Ug K a)
      (Subgroup.normalizer (H13.F431.TwoF4.Ug K a)) :=
    F7.isSylowTwoOf_mono_right hsylU hUgleN le_top
  have hUn : ((H13.F431.TwoF4.Ug K a).subgroupOf
      (Subgroup.normalizer (H13.F431.TwoF4.Ug K a))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUgleN).2 le_rfl
  have hSimgTop : IsSylowTwoOf
      ((S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom) ⊤ := by
    have hSsub : IsSylowTwoOf (S.subgroupOf (L1 ⊔ bigB L1 L2 S)) ⊤ := by
      refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
      · exact hSylP1.2.1.of_equiv
          (Subgroup.subgroupOfEquivOfLe hSylP1.1).symm
      · simpa using hSylP1.2.2
    exact CFSG.Quasithin.E2.isSylowTwoOf_map_mulEquiv ψ1 hSsub
  have hUgSubTop : IsSylowTwoOf
      ((H13.F431.TwoF4.Ug K a).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)) ⊤ := by
    refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hUgSylP1.2.1.of_equiv
        (Subgroup.subgroupOfEquivOfLe hUgSylP1.1).symm
    · simpa using hUgSylP1.2.2
  have hSimg_le : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom ≤
      (H13.F431.TwoF4.Ug K a).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
    intro x hx
    have hxT : (x : H13.F431.TwoF4.Gm K a) ∈
        (((S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom).map
          (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype) := ⟨x, hx, rfl⟩
    have hleT : (((S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom).map
          (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype) ≤
        Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := by
      have hSleB : S.subgroupOf (L1 ⊔ bigB L1 L2 S) ≤
          (bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S) :=
        Subgroup.subgroupOf_mono _ (le_sup_right : S ≤ bigB L1 L2 S)
      calc (((S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom).map
            (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype)
          ≤ ((((bigB L1 L2 S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map
              ψ1.toMonoidHom).map (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype) :=
            Subgroup.map_mono (Subgroup.map_mono hSleB)
        _ = (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ⊓
              H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
            rw [hBimg1, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        _ = Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := by rw [inf_comm, hinf]
    have hSsub2 : IsPGroup 2 (S.subgroupOf (L1 ⊔ bigB L1 L2 S)) :=
      hSylP1.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSylP1.1).symm
    have hTp : IsPGroup 2 ((((S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map
        ψ1.toMonoidHom).map (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype)) :=
      (hSsub2.map ψ1.toMonoidHom).map
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype
    exact le_of_isSylowTwoOf_normal hUgSylN hUn hleT hTp hxT
  have hSUg : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (H13.F431.TwoF4.Ug K a).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
    refine Subgroup.eq_of_le_of_card_ge hSimg_le ?_
    rw [hSimgTop.card_eq, hUgSubTop.card_eq]
  exact ⟨hSylP1, hSUg⟩

private lemma y9_vertex_two_iso
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    {Y : Type} [Group Y] {M1 M2 : Subgroup Y}
    {ε : Y ≃* H13.F431.TwoF4.Gm K a}
    (hP1P2 : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S)
    (hM1ε : M1.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)
    (hM2ε : M2.map ε.toMonoidHom = H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)
    (iso0 : (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S).Iso (RankTwoAmalgam.ofSubgroups M1 M2)) :
    ∃ ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩),
      ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
          H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subgroupOf
            (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
  have hεinj : Function.Injective ε.toMonoidHom := ε.injective
  let e2 : (RankTwoAmalgam.ofSubgroups M1 M2).G2 ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) :=
    (M2.equivMapOfInjective ε.toMonoidHom hεinj).trans (MulEquiv.subgroupCongr hM2ε)
  let ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := iso0.φ2.trans e2
  have hQ1 : (M1 ⊓ M2).map ε.toMonoidHom =
      H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ ⊓
        H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ := by
    rw [Subgroup.map_inf_eq _ _ _ hεinj, hM1ε, hM2ε]
  have hBimg2 : ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
      (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
        H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subgroupOf
          (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    have h := iso_map_inter_of_equiv_right iso0 ε e2 hQ1 (fun x => rfl)
    rw [show (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S from hP1P2]
      at h
    rwa [inf_comm] at h
  exact ⟨ψ2, hBimg2⟩

private lemma y9_vertex_two_sylow
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (hR : Hyp111R L1 L2 S)
    (hinf : H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
      H13.F431.TwoF4.Pg K a ⟨1, by decide⟩ = Subgroup.normalizer (H13.F431.TwoF4.Ug K a))
    {ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)}
    (hBimg2 : ((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
      (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
        H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subgroupOf
          (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)) :
    IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) ∧
      (S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
        (H13.F431.TwoF4.Ug K a).subgroupOf (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
  have hSyl2 := CFSG.GH74.QTGen4.DSGen4.leafSylowS (G := G) hR.symm
  have hSylP2 : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S) := by
    have := hSyl2.2.1
    rwa [bigB_comm] at this
  have hYam := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  obtain ⟨hsylU, _, _, _, _, _, _⟩ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.F4.largeRee_named_covers a K hK
  have hUglePg0 : H13.F431.TwoF4.Ug K a ≤ H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ :=
    Subgroup.le_normalizer.trans hYam.le₀
  have hUgSylP0 : IsSylowTwoOf (H13.F431.TwoF4.Ug K a)
      (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) :=
    F7.isSylowTwoOf_mono_right hsylU hUglePg0 le_top
  have hUgleN : H13.F431.TwoF4.Ug K a ≤
      Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := Subgroup.le_normalizer
  have hUgSylN0 : IsSylowTwoOf (H13.F431.TwoF4.Ug K a)
      (Subgroup.normalizer (H13.F431.TwoF4.Ug K a)) :=
    F7.isSylowTwoOf_mono_right hsylU hUgleN le_top
  have hUn0 : ((H13.F431.TwoF4.Ug K a).subgroupOf
      (Subgroup.normalizer (H13.F431.TwoF4.Ug K a))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUgleN).2 le_rfl
  have hSimgTop2 : IsSylowTwoOf
      ((S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom) ⊤ := by
    have hSsub : IsSylowTwoOf (S.subgroupOf (L2 ⊔ bigB L1 L2 S)) ⊤ := by
      refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
      · exact hSylP2.2.1.of_equiv
          (Subgroup.subgroupOfEquivOfLe hSylP2.1).symm
      · simpa using hSylP2.2.2
    exact CFSG.Quasithin.E2.isSylowTwoOf_map_mulEquiv ψ2 hSsub
  have hUgSubTop0 : IsSylowTwoOf
      ((H13.F431.TwoF4.Ug K a).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)) ⊤ := by
    refine F7.isSylowTwoOf_of_relIndex le_top ?_ ?_
    · exact hUgSylP0.2.1.of_equiv
        (Subgroup.subgroupOfEquivOfLe hUgSylP0.1).symm
    · simpa using hUgSylP0.2.2
  have hSimg_le2 : (S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom ≤
      (H13.F431.TwoF4.Ug K a).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    intro x hx
    have hxT : (x : H13.F431.TwoF4.Gm K a) ∈
        (((S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom).map
          (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype) := ⟨x, hx, rfl⟩
    have hleT : (((S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom).map
          (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype) ≤
        Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := by
      have hSleB : S.subgroupOf (L2 ⊔ bigB L1 L2 S) ≤
          (bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S) :=
        Subgroup.subgroupOf_mono _ (le_sup_right : S ≤ bigB L1 L2 S)
      calc (((S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom).map
            (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype)
          ≤ ((((bigB L1 L2 S).subgroupOf (L2 ⊔ bigB L1 L2 S)).map
              ψ2.toMonoidHom).map (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype) :=
            Subgroup.map_mono (Subgroup.map_mono hSleB)
        _ = (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩ ⊓
              H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
            rw [hBimg2, Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        _ = Subgroup.normalizer (H13.F431.TwoF4.Ug K a) := hinf
    have hSsub2 : IsPGroup 2 (S.subgroupOf (L2 ⊔ bigB L1 L2 S)) :=
      hSylP2.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSylP2.1).symm
    have hTp : IsPGroup 2 ((((S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map
        ψ2.toMonoidHom).map (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype)) :=
      (hSsub2.map ψ2.toMonoidHom).map
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype
    exact le_of_isSylowTwoOf_normal hUgSylN0 hUn0 hleT hTp hxT
  have hSUg2 : (S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
      (H13.F431.TwoF4.Ug K a).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    refine Subgroup.eq_of_le_of_card_ge hSimg_le2 ?_
    rw [hSimgTop2.card_eq, hUgSubTop0.card_eq]
  exact ⟨hSylP2, hSUg2⟩

private lemma y9_perfectCore_one
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (hR : Hyp111R L1 L2 S)
    (hB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G))
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    {ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)}
    (hSUg : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (H13.F431.TwoF4.Ug K a).subgroupOf (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))
    (hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S)) :
    ((perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) =
      ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom) ∧
      S ≤ perfectCore (L1 ⊔ bigB L1 L2 S) ∧
      perfectCore (L1 ⊔ bigB L1 L2 S) = L1 ∧
      perfectCore L1 = L1 := by
  classical
  have hperfPg1 : (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) =
      ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom := by
    have h := CFSG.Quasithin.F112R.perfectCore_map_inj ψ1.toMonoidHom ψ1.injective
      (⊤ : Subgroup ↥(L1 ⊔ bigB L1 L2 S))
    rw [Subgroup.map_top_of_surjective ψ1.toMonoidHom ψ1.surjective] at h
    rw [← Subgroup.subgroupOf_self (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)] at h
    rw [← Subgroup.subgroupOf_self (L1 ⊔ bigB L1 L2 S)] at h
    rw [← CFSG.Quasithin.H13.A7.perfectCore_subgroupOf_of_le
      (le_refl (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))] at h
    rw [← CFSG.Quasithin.H13.A7.perfectCore_subgroupOf_of_le
      (le_refl (L1 ⊔ bigB L1 L2 S))] at h
    exact h
  have hUgleCore : (H13.F431.TwoF4.Ug K a).subgroupOf
      (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) ≤
      (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
    intro x hx
    have hxU : (x : H13.F431.TwoF4.Gm K a) ∈ H13.F431.TwoF4.Ug K a :=
      Subgroup.mem_subgroupOf.1 hx
    have hxU' : (x : H13.F431.TwoF4.Gm K a).1 ∈ F4.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hxU
    exact (CFSG.Quasithin.H13.Sec53F.ReeF4.mem_perfectCore_subgroupOf
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma _) x).2
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeFixedPosUnipotent_le_perfectCore_one ha hK hxU')
  have hSleCore1 : S ≤ perfectCore (L1 ⊔ bigB L1 L2 S) := by
    have h1 : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom ≤
        ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
          (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom := by
      rw [hSUg, ← hperfPg1]
      exact hUgleCore
    have h2 : S.subgroupOf (L1 ⊔ bigB L1 L2 S) ≤
        (perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf (L1 ⊔ bigB L1 L2 S) :=
      (Subgroup.map_le_map_iff_of_injective ψ1.injective).1 h1
    intro s hs
    let sP : ↥(L1 ⊔ bigB L1 L2 S) := ⟨s, hSylP1.1 hs⟩
    exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_subgroupOf.2 (show (sP : G) ∈ S from hs)))
  have hBsolv : Group.IsSolvable ↥(bigB L1 L2 S) := F1.isSolvable_bigB hR
  have hcoreP1leL1 : perfectCore (L1 ⊔ bigB L1 L2 S) ≤ L1 := by
    have hn : (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hB1)
    exact CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left hn rfl hBsolv
  have hperfL1quot : Group.IsPerfect (oTwoQuot ↥L1) := by
    obtain ⟨eSz⟩ := hSz
    haveI : Group.IsPerfect ↥(Sz a) := isPerfect_sz ha
    exact Group.IsPerfect.ofSurjective (f := eSz.symm.toMonoidHom) eSz.symm.surjective
  have hO1 : pCoreOf 2 L1 ≤ ⁅L1, L1⁆ := by
    calc pCoreOf 2 L1 ≤ S ⊓ L1 :=
          CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hR.hyp.h1.sylow
      _ ≤ S := inf_le_left
      _ ≤ perfectCore (L1 ⊔ bigB L1 L2 S) := hSleCore1
      _ = ⁅perfectCore (L1 ⊔ bigB L1 L2 S), perfectCore (L1 ⊔ bigB L1 L2 S)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅L1, L1⁆ := Subgroup.commutator_mono hcoreP1leL1 hcoreP1leL1
  have hL1perf : ⁅L1, L1⁆ = L1 := perfect_of_isPerfect_oTwoQuot hperfL1quot hO1
  have hL1leCore1 : L1 ≤ perfectCore (L1 ⊔ bigB L1 L2 S) :=
    CFSG.Quasithin.le_perfectCore_of_perfect le_sup_left hL1perf
  have hcoreP1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1 :=
    le_antisymm hcoreP1leL1 hL1leCore1
  exact ⟨hperfPg1, hSleCore1, hcoreP1,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hL1perf⟩

private lemma y9_perfectCore_two
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a) (hR : Hyp111R L1 L2 S)
    (hB2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G))
    (hL2 : IsL2Quot (2 * a + 1) (oTwoQuot ↥L2))
    {ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)}
    (hSUg : (S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
      (H13.F431.TwoF4.Ug K a).subgroupOf (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))
    (hSylP2 : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S)) :
    ((perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) =
      ((perfectCore (L2 ⊔ bigB L1 L2 S)).subgroupOf
        (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom) ∧
      S ≤ perfectCore (L2 ⊔ bigB L1 L2 S) ∧
      perfectCore (L2 ⊔ bigB L1 L2 S) = L2 ∧
      perfectCore L2 = L2 := by
  classical
  have hperfPg0 : (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) =
      ((perfectCore (L2 ⊔ bigB L1 L2 S)).subgroupOf
        (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom := by
    have h := CFSG.Quasithin.F112R.perfectCore_map_inj ψ2.toMonoidHom ψ2.injective
      (⊤ : Subgroup ↥(L2 ⊔ bigB L1 L2 S))
    rw [Subgroup.map_top_of_surjective ψ2.toMonoidHom ψ2.surjective] at h
    rw [← Subgroup.subgroupOf_self (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)] at h
    rw [← Subgroup.subgroupOf_self (L2 ⊔ bigB L1 L2 S)] at h
    rw [← CFSG.Quasithin.H13.A7.perfectCore_subgroupOf_of_le
      (le_refl (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))] at h
    rw [← CFSG.Quasithin.H13.A7.perfectCore_subgroupOf_of_le
      (le_refl (L2 ⊔ bigB L1 L2 S))] at h
    exact h
  have hUgleCore0 : (H13.F431.TwoF4.Ug K a).subgroupOf
      (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) ≤
      (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    intro x hx
    have hxU : (x : H13.F431.TwoF4.Gm K a) ∈ H13.F431.TwoF4.Ug K a :=
      Subgroup.mem_subgroupOf.1 hx
    have hxU' : (x : H13.F431.TwoF4.Gm K a).1 ∈ F4.reeFixedPosUnipotent K a :=
      Subgroup.mem_subgroupOf.1 hxU
    exact (CFSG.Quasithin.H13.Sec53F.ReeF4.mem_perfectCore_subgroupOf
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeLocalParabolic_le_reeGamma _) x).2
      (CFSG.Quasithin.H13.Sec53F.ReeF4.reeFixedPosUnipotent_le_perfectCore_zero ha hK hxU')
  have hSleCore2 : S ≤ perfectCore (L2 ⊔ bigB L1 L2 S) := by
    have h1 : (S.subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom ≤
        ((perfectCore (L2 ⊔ bigB L1 L2 S)).subgroupOf
          (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom := by
      rw [hSUg, ← hperfPg0]
      exact hUgleCore0
    have h2 : S.subgroupOf (L2 ⊔ bigB L1 L2 S) ≤
        (perfectCore (L2 ⊔ bigB L1 L2 S)).subgroupOf (L2 ⊔ bigB L1 L2 S) :=
      (Subgroup.map_le_map_iff_of_injective ψ2.injective).1 h1
    intro s hs
    let sP : ↥(L2 ⊔ bigB L1 L2 S) := ⟨s, hSylP2.1 hs⟩
    exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_subgroupOf.2 (show (sP : G) ∈ S from hs)))
  have hBsolv : Group.IsSolvable ↥(bigB L1 L2 S) := F1.isSolvable_bigB hR
  have hcoreP2leL2 : perfectCore (L2 ⊔ bigB L1 L2 S) ≤ L2 := by
    have hn : (L2.subgroupOf (L2 ⊔ bigB L1 L2 S)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
        (sup_le Subgroup.le_normalizer hB2)
    exact CFSG.Quasithin.perfectCore_le_of_sup_solvable le_sup_left hn rfl hBsolv
  have hperfL2quot : Group.IsPerfect (oTwoQuot ↥L2) := by
    obtain ⟨eL2⟩ := hL2
    have h4 : ∃ s : Finset (GaloisField 2 (2 * a + 1)), s.card = 4 := by
      have h4c : 4 ≤ Nat.card (GaloisField 2 (2 * a + 1)) := by
        rw [GaloisField.card 2 (2 * a + 1) (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : Fintype (GaloisField 2 (2 * a + 1)) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (GaloisField 2 (2 * a + 1)))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4c)
      exact ⟨s, hs⟩
    have hPSL : Group.IsPerfect
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (2 * a + 1))) :=
      CFSG.LinearGroups.linear_projective_perfect (K := GaloisField 2 (2 * a + 1))
        (by norm_num) (Or.inr h4)
    exact Group.IsPerfect.ofSurjective (f := eL2.symm.toMonoidHom) eL2.symm.surjective
  have hO2 : pCoreOf 2 L2 ≤ ⁅L2, L2⁆ := by
    calc pCoreOf 2 L2 ≤ S ⊓ L2 :=
          CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hR.hyp.h2.sylow
      _ ≤ S := inf_le_left
      _ ≤ perfectCore (L2 ⊔ bigB L1 L2 S) := hSleCore2
      _ = ⁅perfectCore (L2 ⊔ bigB L1 L2 S), perfectCore (L2 ⊔ bigB L1 L2 S)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅L2, L2⁆ := Subgroup.commutator_mono hcoreP2leL2 hcoreP2leL2
  have hL2perf : ⁅L2, L2⁆ = L2 := perfect_of_isPerfect_oTwoQuot hperfL2quot hO2
  have hL2leCore2 : L2 ≤ perfectCore (L2 ⊔ bigB L1 L2 S) :=
    CFSG.Quasithin.le_perfectCore_of_perfect le_sup_left hL2perf
  have hcoreP2 : perfectCore (L2 ⊔ bigB L1 L2 S) = L2 :=
    le_antisymm hcoreP2leL2 hL2leCore2
  exact ⟨hperfPg0, hSleCore2, hcoreP2,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hL2perf⟩

private lemma y9_card_radical_one
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (hB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G))
    (hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S))
    (hSleL1 : S ≤ L1)
    (hcore1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1)
    {ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)}
    (hperfPg1 : (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) =
      ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom) :
    Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 10 := by
  have hPC1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 :=
    pCoreOf_sup_eq_of_sylow_le hB1 hSylP1 hSleL1
  have hpCoreSub1 : pCoreOf 2 (L1.subgroupOf (L1 ⊔ bigB L1 L2 S)) =
      (pCoreOf 2 L1).subgroupOf (L1 ⊔ bigB L1 L2 S) := by
    apply Subgroup.map_injective (f := (L1 ⊔ bigB L1 L2 S).subtype)
      (L1 ⊔ bigB L1 L2 S).subtype_injective
    rw [CFSG.Quasithin.H13.L14331.map_pCoreOf_subgroupOf' (I := L1 ⊔ bigB L1 L2 S)
      (X := L1) le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le ((pCoreOf_le 2 L1).trans le_sup_left)]
  have hpCoreSub1' : pCoreOf 2 ((perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)) =
      (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
    apply Subgroup.map_injective (f := (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype)
      (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩).subtype_injective
    rw [CFSG.Quasithin.H13.L14331.map_pCoreOf_subgroupOf'
      (I := H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)
      (X := perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)) (perfectCore_le _),
      Subgroup.map_subgroupOf_eq_of_le ((pCoreOf_le 2 _).trans (perfectCore_le _))]
  have hpc1map : ((pCoreOf 2 L1).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) := by
    rw [← hpCoreSub1, ← hpCoreSub1',
      ← CFSG.Quasithin.F112R.pCoreOf_map_inj ψ1.toMonoidHom ψ1.injective
        (L1.subgroupOf (L1 ⊔ bigB L1 L2 S))]
    congr 1
    simpa [hcore1] using hperfPg1.symm
  calc Nat.card (pCoreOf 2 (L1 ⊔ bigB L1 L2 S))
      = Nat.card (pCoreOf 2 L1) := by rw [hPC1]
    _ = Nat.card (((pCoreOf 2 L1).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom) := by
          rw [Subgroup.card_map_of_injective (f := ψ1.toMonoidHom) ψ1.injective,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe
              ((pCoreOf_le 2 L1).trans le_sup_left)).toEquiv]
    _ = Nat.card ((pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))).subgroupOf
          (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)) := by rw [hpc1map]
    _ = Nat.card (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            ((pCoreOf_le 2 _).trans (perfectCore_le _))).toEquiv]
    _ = (2 ^ (2 * a + 1)) ^ 10 := card_pCore_perfectCore_Pg_one ha hK

private lemma y9_card_radical_two
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (hB2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G))
    (hSylP2 : IsSylowTwoOf S (L2 ⊔ bigB L1 L2 S))
    (hSleL2 : S ≤ L2)
    (hcore2 : perfectCore (L2 ⊔ bigB L1 L2 S) = L2)
    {ψ2 : ↥(L2 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)}
    (hperfPg0 : (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) =
      ((perfectCore (L2 ⊔ bigB L1 L2 S)).subgroupOf
        (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom) :
    Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ (2 * a + 1)) ^ 11 := by
  have hPC2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 :=
    pCoreOf_sup_eq_of_sylow_le hB2 hSylP2 hSleL2
  have hpCoreSub2 : pCoreOf 2 (L2.subgroupOf (L2 ⊔ bigB L1 L2 S)) =
      (pCoreOf 2 L2).subgroupOf (L2 ⊔ bigB L1 L2 S) := by
    apply Subgroup.map_injective (f := (L2 ⊔ bigB L1 L2 S).subtype)
      (L2 ⊔ bigB L1 L2 S).subtype_injective
    rw [CFSG.Quasithin.H13.L14331.map_pCoreOf_subgroupOf' (I := L2 ⊔ bigB L1 L2 S)
      (X := L2) le_sup_left,
      Subgroup.map_subgroupOf_eq_of_le ((pCoreOf_le 2 L2).trans le_sup_left)]
  have hpCoreSub2' : pCoreOf 2 ((perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)) =
      (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    apply Subgroup.map_injective (f := (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype)
      (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩).subtype_injective
    rw [CFSG.Quasithin.H13.L14331.map_pCoreOf_subgroupOf'
      (I := H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)
      (X := perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)) (perfectCore_le _),
      Subgroup.map_subgroupOf_eq_of_le ((pCoreOf_le 2 _).trans (perfectCore_le _))]
  have hpc2map : ((pCoreOf 2 L2).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom =
      (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩) := by
    rw [← hpCoreSub2, ← hpCoreSub2',
      ← CFSG.Quasithin.F112R.pCoreOf_map_inj ψ2.toMonoidHom ψ2.injective
        (L2.subgroupOf (L2 ⊔ bigB L1 L2 S))]
    congr 1
    simpa [hcore2] using hperfPg0.symm
  calc Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S))
      = Nat.card (pCoreOf 2 L2) := by rw [hPC2]
    _ = Nat.card (((pCoreOf 2 L2).subgroupOf (L2 ⊔ bigB L1 L2 S)).map ψ2.toMonoidHom) := by
          rw [Subgroup.card_map_of_injective (f := ψ2.toMonoidHom) ψ2.injective,
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe
              ((pCoreOf_le 2 L2).trans le_sup_left)).toEquiv]
    _ = Nat.card ((pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))).subgroupOf
          (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩)) := by rw [hpc2map]
    _ = Nat.card (pCoreOf 2 (perfectCore (H13.F431.TwoF4.Pg K a ⟨0, by decide⟩))) := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            ((pCoreOf_le 2 _).trans (perfectCore_le _))).toEquiv]
    _ = (2 ^ (2 * a + 1)) ^ 11 := card_pCore_perfectCore_Pg_zero ha hK

private lemma y9_center_le
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}
    {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (ha : 1 ≤ a)
    (hSylP1 : IsSylowTwoOf S (L1 ⊔ bigB L1 L2 S))
    {ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃*
      ↥(H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)}
    (hSUg : (S.subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (H13.F431.TwoF4.Ug K a).subgroupOf (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩))
    (hperfPg1 : (perfectCore (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩)).subgroupOf
        (H13.F431.TwoF4.Pg K a ⟨1, by decide⟩) =
      ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom)
    (hcore1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1) :
    centerOf S ≤ Subgroup.centralizer (L1 : Set G) := by
  let j1 : Fin F4.fixedOrbitCount := ⟨1, by decide⟩
  have hcenterS : centerOf (S.subgroupOf (L1 ⊔ bigB L1 L2 S)) =
      (centerOf S).subgroupOf (L1 ⊔ bigB L1 L2 S) := by
    apply Subgroup.map_injective (f := (L1 ⊔ bigB L1 L2 S).subtype)
      (L1 ⊔ bigB L1 L2 S).subtype_injective
    rw [map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hSylP1.1]
    exact (Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hSylP1.1)).symm
  have hYam := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  have hUglePg1 : H13.F431.TwoF4.Ug K a ≤ H13.F431.TwoF4.Pg K a j1 :=
    Subgroup.le_normalizer.trans hYam.le₁
  have hcenterU : centerOf ((H13.F431.TwoF4.Ug K a).subgroupOf
      (H13.F431.TwoF4.Pg K a j1)) =
      (centerOf (H13.F431.TwoF4.Ug K a)).subgroupOf
        (H13.F431.TwoF4.Pg K a j1) := by
    apply Subgroup.map_injective (f := (H13.F431.TwoF4.Pg K a j1).subtype)
      (H13.F431.TwoF4.Pg K a j1).subtype_injective
    rw [map_subtype_centerOf, Subgroup.map_subgroupOf_eq_of_le hUglePg1]
    exact (Subgroup.map_subgroupOf_eq_of_le (inf_le_left.trans hUglePg1)).symm
  have hcenterMap : ((centerOf S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom =
      (centerOf (H13.F431.TwoF4.Ug K a)).subgroupOf
        (H13.F431.TwoF4.Pg K a j1) := by
    have h := CFSG.Quasithin.H13.Sec53F.Yam.centerOf_map_equiv ψ1
      (S.subgroupOf (L1 ⊔ bigB L1 L2 S))
    rw [hSUg, hcenterS, hcenterU] at h
    exact h.symm
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hzP1 : z ∈ L1 ⊔ bigB L1 L2 S := hSylP1.1 hz.1
  have hlP1 : l ∈ L1 ⊔ bigB L1 L2 S := Subgroup.mem_sup_left hl
  let z' : ↥(L1 ⊔ bigB L1 L2 S) := ⟨z, hzP1⟩
  let l' : ↥(L1 ⊔ bigB L1 L2 S) := ⟨l, hlP1⟩
  have hzCenter : ψ1 z' ∈ (centerOf (H13.F431.TwoF4.Ug K a)).subgroupOf
      (H13.F431.TwoF4.Pg K a j1) := by
    have hmem : ψ1 z' ∈ ((centerOf S).subgroupOf (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom :=
      (Subgroup.mem_map (f := ψ1.toMonoidHom)).2
        ⟨z', (Subgroup.mem_subgroupOf (h := z')).2 (by simpa using hz), rfl⟩
    rwa [hcenterMap] at hmem
  have hlPerf : ψ1 l' ∈ (perfectCore (H13.F431.TwoF4.Pg K a j1)).subgroupOf
      (H13.F431.TwoF4.Pg K a j1) := by
    have hlPerf1 : l ∈ perfectCore (L1 ⊔ bigB L1 L2 S) := by rw [hcore1]; exact hl
    have hmem : ψ1 l' ∈ ((perfectCore (L1 ⊔ bigB L1 L2 S)).subgroupOf
        (L1 ⊔ bigB L1 L2 S)).map ψ1.toMonoidHom :=
      (Subgroup.mem_map (f := ψ1.toMonoidHom)).2
        ⟨l', (Subgroup.mem_subgroupOf (h := l')).2 (by simpa using hlPerf1), rfl⟩
    rwa [← hperfPg1] at hmem
  have hcomm := Subgroup.mem_centralizer_iff.1
    (centerOf_Ug_le_centralizer_perfectCore_one ha hK
      (Subgroup.mem_subgroupOf.1 hzCenter)) _ (Subgroup.mem_subgroupOf.1 hlPerf)
  have hpsi : ψ1 (l' * z') = ψ1 (z' * l') := by
    apply Subtype.ext
    rw [map_mul, map_mul]
    exact hcomm
  have hcomm' : l' * z' = z' * l' := ψ1.injective hpsi
  simpa using congrArg Subtype.val hcomm'


theorem y9TwistedF4 : Y9TwistedF4 := by
  intro G _ _ L1 L2 S a hF ha hSz hL2 hA
  classical
  obtain ⟨K, hFieldK, hFinK, hCharK, hK, _, hGroupY, M1, M2, ε, iso0, hM⟩ :=
    y9_standard_position hA ha
  letI := hFieldK
  letI := hFinK
  letI := hCharK
  letI := hGroupY
  obtain ⟨hR, hB1, hB2, hM1ε, hM2ε, hP1P2, hinf⟩ :=
    y9_index_orientation hK hF ha hSz iso0 hM
  obtain ⟨ψ1, hBimg1⟩ := y9_vertex_one_iso hP1P2 hM1ε hM2ε iso0
  obtain ⟨hSylP1, hSUg1⟩ := y9_vertex_one_sylow hK ha hR hinf hBimg1
  obtain ⟨ψ2, hBimg2⟩ := y9_vertex_two_iso hP1P2 hM1ε hM2ε iso0
  obtain ⟨hSylP2, hSUg2⟩ := y9_vertex_two_sylow hK ha hR hinf hBimg2
  obtain ⟨hperfPg1, hSleCore1, hcore1, hperfL1⟩ :=
    y9_perfectCore_one hK ha hR hB1 hSz hSUg1 hSylP1
  obtain ⟨hperfPg0, hSleCore2, hcore2, hperfL2⟩ :=
    y9_perfectCore_two hK ha hR hB2 hL2 hSUg2 hSylP2
  have hSleL1 : S ≤ L1 := by rw [← hcore1]; exact hSleCore1
  have hSleL2 : S ≤ L2 := by rw [← hcore2]; exact hSleCore2
  have hPO : CFSG.Quasithin.F112R.PerfectOver L1 L2 S := ⟨hperfL1, hperfL2, hSleL1, hSleL2⟩
  refine ⟨?_, ?_, ?_, hPO⟩
  · exact y9_center_le hK ha hSylP1 hSUg1 hperfPg1 hcore1
  · exact y9_card_radical_one hK ha hB1 hSylP1 hSleL1 hcore1 hperfPg1
  · exact y9_card_radical_two hK ha hB2 hSylP2 hSleL2 hcore2 hperfPg0

end CFSG.Quasithin.Stroth
