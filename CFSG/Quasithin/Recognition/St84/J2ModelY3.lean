module

public import CFSG.Quasithin.Recognition.St84.J2YPair
public import CFSG.Quasithin.Recognition.J2RecCzIso
public import CFSG.Quasithin.Recognition.L34AmalgamIsoA5
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
public import CFSG.Quasithin.EmptyFaithful.S1421QA17Embed
public import Certificates.Certificate733001
public import CFSG.GroupTheory.PCore.CharacteristicPPerfect

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.A312J2 CFSG.Quasithin.F112R.J2L CFSG.Quasithin.J2Cz
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore

variable {G : Type} [Group G]

theorem j2_C2_concrete :
    genOf 315 j2C2Gens ≤ j2P ∧ Nat.card ↥(genOf 315 j2C2Gens) = 1920 := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ :=
    CFSG.Sporadic.SmallOddCore.ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  have hmem : _ ∈ j2Rows := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hr := hrows _ hmem
  have hC2 : genOf 315 j2C2Gens =
      j2P ⊓ Subgroup.centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
    have h := hr.2.2.2.1
    dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C2Gens]
    exact h
  have hcard : Nat.card ↥(j2P ⊓ Subgroup.centralizer ({tp 315 (j2CentTbl 31)} : Set _)) = 1920 := by
    have h := hr.2.2.2.2.1
    dsimp only at h
    exact h
  exact ⟨by rw [hC2]; exact inf_le_left, by rw [hC2]; exact hcard⟩

end CFSG.Quasithin.F112R.St84

namespace CFSG.Quasithin.F112R.St84.J2Model

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.A312J2 CFSG.Quasithin.F112R.J2L CFSG.Quasithin.J2Cz
open CFSG.Quasithin.L34Amalgam
open CFSG.CosetTable CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Th Subgroup

@[expose] noncomputable def Km : Subgroup (Equiv.Perm (Fin 315)) := genOf 315 [c2aT, c2bT]

theorem Km_eq_closure :
    Km = Subgroup.closure ({tp 315 (c2aT ()), tp 315 (c2bT ())} : Set (Equiv.Perm (Fin 315))) := by
  rw [Km, genOf]
  congr 1
  ext x
  simp only [Set.mem_image, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl | rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨c2aT (), Or.inl rfl, rfl⟩
    · exact ⟨c2bT (), Or.inr rfl, rfl⟩

theorem Km_le_C2 :
    Km ≤ genOf 315 j2C2Gens := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have hA1 : a1OK = true := (Certificates.certificate733001).1
  have hC2p : ∀ g ∈ j2C2Gens, permOK 315 g = true := by
    have h := j2_QOK
    simp only [j2QOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨-, hC2enum⟩, hC2p⟩, -⟩, -⟩, -⟩ := h
    rwa [List.all_eq_true] at hC2p
  rw [Km_eq_closure, Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | rfl
  · exact tp_wordTbl_mem hn hC2p (by decide) (c2aT_permOK hA1)
  · exact tp_wordTbl_mem hn hC2p (by decide) (c2bT_permOK hA1)

theorem Km_card : Nat.card Km = 60 := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have hA1 : a1OK = true := (Certificates.certificate733001).1
  have hA3 : a3OK = true := (Certificates.certificate733001).2.2.1
  have hgs : ∀ g ∈ [c2aT, c2bT], permOK 315 g = true := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact c2aT_permOK hA1
    · exact c2bT_permOK hA1
  have h := (enumOK_spec hn hgs (c2_enumOK hA3)).1
  simpa only [Km] using h

theorem Km_isSimple :
    IsSimpleGroup ↥Km := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have hA1 : a1OK = true := (Certificates.certificate733001).1
  have hA2 : a2OK = true := (Certificates.certificate733001).2.1
  have hpa : permOK 315 (c2aT ()) = true := c2aT_permOK hA1
  have hpb : permOK 315 (c2bT ()) = true := c2bT_permOK hA1
  have hpb3 : pb ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
    exact pb_cube
  have harep : Rep 315 (c2aT ()) (tp 315 (c2aT ())) := rep_tp hpa
  have hbrep : Rep 315 (c2bT ()) (tp 315 (c2bT ())) := rep_tp hpb
  have ha : tp 315 (c2aT ()) * tp 315 (c2aT ()) = 1 := by
    have h := c2aT_sq hA2
    exact (tblEq_iff_eq (Rep.compT harep harep) (Rep.idT hn)).mp h
  have hb : tp 315 (c2bT ()) ^ 3 = 1 := by
    have h := c2bT_cube hA2
    exact (tblEq_iff_eq (Rep.powT hn hbrep 3) (Rep.idT hn)).mp h
  have hab : (tp 315 (c2aT ()) * tp 315 (c2bT ())) ^ 5 = 1 := by
    have h := c2abT_pow_five hA2
    exact (tblEq_iff_eq (Rep.powT hn (Rep.compT harep hbrep) 5) (Rep.idT hn)).mp h
  have hclosure : Subgroup.closure
      ({tp 315 (c2aT ()), tp 315 (c2bT ())} : Set (Equiv.Perm (Fin 315))) = Km :=
    Km_eq_closure.symm
  have hcard : Nat.card Km = 60 := Km_card
  let eKm : PG 2 a5Rels ≃* Km :=
    a5Equiv (C := Km) (a := tp 315 (c2aT ())) (b := tp 315 (c2bT ()))
      ha hb hab hclosure hcard
  let eA5 : PG 2 a5Rels ≃* alternatingGroup (Fin 5) :=
    a5Equiv (C := alternatingGroup (Fin 5)) (a := (pa : Equiv.Perm (Fin 5)))
      (b := (pb : Equiv.Perm (Fin 5))) (by simpa using pa_sq)
      hpb3 papb_pow_five closure_pa_pb
      (by rw [nat_card_alternatingGroup, Nat.card_fin]; norm_num)
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  exact MulEquiv.isSimpleGroup (eKm.symm.trans eA5)

theorem nonempty_C2_equiv_Y3 :
    Nonempty (↥(genOf 315 j2C2Gens) ≃* ↥(j2CtxA.Y 3)) := by
  obtain ⟨hC2le, hC2card⟩ := j2_C2_concrete
  let Z : Subgroup ↥j2P := (genOf 315 j2C2Gens).subgroupOf j2P
  have hZcard : Nat.card Z = 1920 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC2le).toEquiv, hC2card]
  obtain ⟨R, hRcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥Z) 2 (n := 7)
    (by rw [hZcard]; norm_num)
  let T₀ : Subgroup ↥j2P := R.map Z.subtype
  have hT₀card : Nat.card T₀ = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective Z.subtype_injective, hRcard]
  have hT₀le : T₀ ≤ Z := Subgroup.map_subtype_le R
  have hT₀p : IsPGroup 2 T₀ := IsPGroup.of_card hT₀card
  have hAcard : Nat.card ↥j2P = 604800 := by
    have h1 : Nat.card ↥j2P = Nat.card CFSG.Blueprint.NativeSporadic.J2 :=
      (Nat.card_congr CFSG.Sporadic.Schreier.j2PermEquiv.toEquiv).symm
    have h2 : Nat.card CFSG.Blueprint.NativeSporadic.J2 = Nat.card ↥CFSG.Sporadic.J2.J :=
      Nat.card_congr CFSG.Sporadic.Bridge.J2.nativeEquiv.toEquiv
    rw [h1, h2]
    exact CFSG.Sporadic.J2.card_J
  have hT₀sylow : IsSylowTwoOf T₀ ⊤ := by
    refine ⟨le_top, hT₀p, ?_⟩
    have hindex_top : (T₀.subgroupOf ⊤).index = T₀.index := Subgroup.relIndex_top_right T₀
    rw [hindex_top]
    have h := T₀.card_mul_index
    rw [hT₀card, hAcard] at h
    have hidx : T₀.index = 4725 := by omega
    rw [hidx]
    norm_num
  let ψ : ↥j2P ≃* ↥CFSG.Sporadic.J2.J :=
    (CFSG.Sporadic.Bridge.J2.nativeEquiv.symm.trans CFSG.Sporadic.Schreier.j2PermEquiv).symm
  obtain ⟨e⟩ := @CFSG.Quasithin.F112R.nonempty_equiv_of_overgroup ↥j2P
    ↥CFSG.Sporadic.J2.J inferInstance inferInstance inferInstance inferInstance ψ T₀
    hT₀sylow j2CtxA.S j2A_sylow Z hT₀le (j2CtxA.Y 3) (fun W hSW hc =>
      J2Y.eq_of_card (j := 3) (Or.inr rfl) hSW (by
        rw [hc, hZcard]
        exact (j2A_card (j := 3) (by norm_num)).symm))
  exact ⟨(Subgroup.subgroupOfEquivOfLe hC2le).symm.trans e⟩

theorem exists_complement_Y3 :
    ∃ K : Subgroup ↥CFSG.Sporadic.J2.J,
      K ≤ j2CtxA.Y 3 ∧ K ⊓ pCoreOf 2 (j2CtxA.Y 3) = ⊥ ∧ Nat.card K = 60 := by
  obtain ⟨e⟩ := nonempty_C2_equiv_Y3
  have hKmC2 : Km ≤ genOf 315 j2C2Gens := Km_le_C2
  let Ksub : Subgroup ↥(j2CtxA.Y 3) :=
    Subgroup.map (e : ↥(genOf 315 j2C2Gens) →* ↥(j2CtxA.Y 3))
      (Km.subgroupOf (genOf 315 j2C2Gens))
  let K : Subgroup ↥CFSG.Sporadic.J2.J := Subgroup.map (j2CtxA.Y 3).subtype Ksub
  have hKle : K ≤ j2CtxA.Y 3 := Subgroup.map_subtype_le Ksub
  let eqKmK : ↥Km ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hKmC2).symm.trans
      ((Subgroup.equivMapOfInjective (Km.subgroupOf (genOf 315 j2C2Gens))
        (e : ↥(genOf 315 j2C2Gens) →* ↥(j2CtxA.Y 3)) (EquivLike.injective e)).trans
        (Subgroup.equivMapOfInjective Ksub (j2CtxA.Y 3).subtype
          (j2CtxA.Y 3).subtype_injective))
  have hKcard : Nat.card K = 60 := by
    rw [← Nat.card_congr eqKmK.toEquiv]
    exact Km_card
  have hKsimple : IsSimpleGroup ↥K := by
    haveI : IsSimpleGroup ↥Km := Km_isSimple
    exact MulEquiv.isSimpleGroup eqKmK.symm
  have hKQ : K ⊓ pCoreOf 2 (j2CtxA.Y 3) = ⊥ := by
    haveI : IsSimpleGroup ↥K := hKsimple
    have hnorm : ((K ⊓ pCoreOf 2 (j2CtxA.Y 3)).subgroupOf K).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
      refine (le_inf Subgroup.le_normalizer
        (hKle.trans (le_normalizer_pCoreOf (r := 2) (j2CtxA.Y 3)))).trans ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((K ⊓ pCoreOf 2 (j2CtxA.Y 3)).subgroupOf K) with hbot | htop
    · exact (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le inf_le_left
    · exfalso
      have hKleQ : K ≤ pCoreOf 2 (j2CtxA.Y 3) :=
        (Subgroup.subgroupOf_eq_top.mp htop).trans inf_le_right
      have hdvd : Nat.card K ∣ Nat.card (pCoreOf 2 (j2CtxA.Y 3)) :=
        Subgroup.card_dvd_of_le hKleQ
      rw [hKcard, J2L.card_pCoreOf_Y3] at hdvd
      norm_num at hdvd
  exact ⟨K, hKle, hKQ, hKcard⟩

theorem eq_pCoreOf_or_eq_of_normal_Y3
    {N : Subgroup ↥CFSG.Sporadic.J2.J}
    (hQN : pCoreOf 2 (j2CtxA.Y 3) ≤ N) (hNP : N ≤ j2CtxA.Y 3)
    (hN : (N.subgroupOf (j2CtxA.Y 3)).Normal) :
    N = pCoreOf 2 (j2CtxA.Y 3) ∨ N = j2CtxA.Y 3 := by
  obtain ⟨V, hVnormal, hVext, hValt⟩ := j2_Y3_ext.1
  haveI : V.Normal := hVnormal
  have hVp : IsPGroup 2 ↥V := by
    haveI : CFSG.IsExtraspecial 2 ↥V := hVext.1
    exact CFSG.IsExtraspecial.isPGroup 2 ↥V
  have hVcard : Nat.card ↥V = 32 := by
    simpa using hVext.2
  have hVcore : V.map (j2CtxA.Y 3).subtype ≤ pCoreOf 2 (j2CtxA.Y 3) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf (r := 2) (H := j2CtxA.Y 3)
      (Subgroup.map_subtype_le V) ?_ (hVp.map (j2CtxA.Y 3).subtype)
    have hmap : (V.map (j2CtxA.Y 3).subtype).subgroupOf (j2CtxA.Y 3) = V :=
      Subgroup.comap_map_eq_self_of_injective (j2CtxA.Y 3).subtype_injective V
    rw [hmap]
    exact hVnormal
  have hVcorecard : Nat.card (pCoreOf 2 (j2CtxA.Y 3)) = 32 := by
    rw [J2L.card_pCoreOf_Y3]
    norm_num
  have hVeq : V.map (j2CtxA.Y 3).subtype = pCoreOf 2 (j2CtxA.Y 3) := by
    refine Subgroup.eq_of_le_of_card_ge hVcore ?_
    rw [hVcorecard, Subgroup.card_map_of_injective (j2CtxA.Y 3).subtype_injective, hVcard]
  haveI : IsSimpleGroup (↥(j2CtxA.Y 3) ⧸ V) := by
    obtain ⟨e⟩ := hValt
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact MulEquiv.isSimpleGroup e
  let N' : Subgroup ↥(j2CtxA.Y 3) := N.subgroupOf (j2CtxA.Y 3)
  have hN'norm : N'.Normal := hN
  have hVN' : V ≤ N' := by
    intro v hv
    have hv' : ((v : ↥(j2CtxA.Y 3)) : ↥CFSG.Sporadic.J2.J) ∈
        V.map (j2CtxA.Y 3).subtype := ⟨v, hv, rfl⟩
    rw [hVeq] at hv'
    exact hQN hv'
  have hMnorm : (N'.map (QuotientGroup.mk' V)).Normal :=
    hN'norm.map (QuotientGroup.mk' V) (QuotientGroup.mk'_surjective V)
  haveI := hMnorm
  have hNkeq : N = N'.map (j2CtxA.Y 3).subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hNP).symm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map (QuotientGroup.mk' V)) with
    hbot | htop
  · left
    have hle : N' ≤ V := by
      have h := (Subgroup.map_eq_bot_iff N').mp hbot
      rwa [QuotientGroup.ker_mk'] at h
    have hN'eq : N' = V := le_antisymm hle hVN'
    calc N = N'.map (j2CtxA.Y 3).subtype := hNkeq
      _ = V.map (j2CtxA.Y 3).subtype := by rw [hN'eq]
      _ = pCoreOf 2 (j2CtxA.Y 3) := hVeq
  · right
    have hker : (QuotientGroup.mk' V).ker ≤ N' := by
      rw [QuotientGroup.ker_mk']
      exact hVN'
    have hN'top : N' = ⊤ := by
      have h := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' V) (H := N') hker
      rw [htop] at h
      simpa using h.symm
    calc N = N'.map (j2CtxA.Y 3).subtype := hNkeq
      _ = j2CtxA.Y 3 := by rw [hN'top, Subgroup.map_top, Subgroup.range_subtype]

theorem not_commutative_pCoreOf_Y3 :
    ¬ ∀ x y : ↥(pCoreOf 2 (j2CtxA.Y 3)), x * y = y * x := by
  rintro hcomm
  obtain ⟨-, A, B, -, ⟨eA⟩, -⟩ := isQ8D8_pCoreOf_Y3
  have hAcomm : ∀ a b : ↥A, a * b = b * a := by
    intro a b
    exact Subtype.ext (hcomm (a : ↥(pCoreOf 2 (j2CtxA.Y 3)))
      (b : ↥(pCoreOf 2 (j2CtxA.Y 3))))
  have hq8comm : ∀ x y : QuaternionGroup 2, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := eA.surjective x
    obtain ⟨b, rfl⟩ := eA.surjective y
    calc eA a * eA b = eA (a * b) := (map_mul eA a b).symm
      _ = eA (b * a) := by rw [hAcomm a b]
      _ = eA b * eA a := map_mul eA b a
  have hnc : (QuaternionGroup.a 1 * QuaternionGroup.xa 0 : QuaternionGroup 2) ≠
      QuaternionGroup.xa 0 * QuaternionGroup.a 1 := by decide
  exact hnc (hq8comm _ _)

theorem charTwo_Y3 :
    CharTwo (j2CtxA.Y 3) :=
  CFSG.GroupTheory.le_pCoreOf_of_perfect_of_not_commutative
    not_commutative_pCoreOf_Y3 j2_Y3_ext.2
    (fun _ hQN hNP hN => eq_pCoreOf_or_eq_of_normal_Y3 hQN hNP hN)

theorem nonempty_mulEquiv_Y3 :
    Nonempty (↥(j2CtxA.Y 3) ≃* J2Cz.Model) := by
  obtain ⟨K, hKP, hKQ, hKcard⟩ := exists_complement_Y3
  have hQ : Nonempty (↥(pCoreOf 2 (j2CtxA.Y 3)) ≃* J2Cz.QM) :=
    @CFSG.Quasithin.IsQ8D8.nonempty_mulEquiv_QM ↥(pCoreOf 2 (j2CtxA.Y 3)) inferInstance
      isQ8D8_pCoreOf_Y3
  exact @CFSG.Quasithin.nonempty_mulEquiv_model_of_complement ↥CFSG.Sporadic.J2.J
    inferInstance inferInstance (j2CtxA.Y 3) K hQ charTwo_Y3 J2L.card_Y3 hKP hKQ hKcard

end CFSG.Quasithin.F112R.St84.J2Model
