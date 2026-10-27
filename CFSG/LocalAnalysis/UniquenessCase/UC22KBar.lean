module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22xk

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.Open.StatedAPI
open P22x

variable {G : Type} [Group G] [Finite G]

@[expose] def S22_5_2Bar (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ p ∈ D.sig, p ∣ Nat.card ↥(mbarImage D.M D.U (proofN D))

@[expose] def NatPFactBar (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ p ∈ D.sig, ¬ p ∣ Nat.card ↥(mbarImage D.M D.U (proofN D)) →
    ∀ x ∈ D.M, IsPGroup p (Subgroup.zpowers x) →
      (∀ y ∈ jOf D.T, x * y * x⁻¹ ∈ jOf D.T) → (∀ z ∈ proofE D, x * z * x⁻¹ = z) →
      ∀ y ∈ jOf D.T, x * y * x⁻¹ * y⁻¹ ∈ centralizer (D.U : Set G)

theorem uc22k_natPFactBar_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch)
    (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) : NatPFactBar D Ch := by
  classical
  intro hH c p hp hpN x hxM hxp _hxJ hxE y hy
  obtain ⟨hpP, -⟩ := D.sig_prime p hp
  obtain ⟨m, Nb, hNb⟩ := h2 hH c
  obtain ⟨Umod, _, _, _, e, ρ, hc⟩ :=
    uc22br4_exists_conjModule D.M D.U (uc22p22xf_hV D) (uc22p22xf_hel D)
  have d := natDec_of_data D Ch h3 h51 hH c hNb e ρ hc
  have hV := uc22p22xf_hV D
  have hJM : jOf D.T ≤ D.M := (uc22p22e_jOf_le_self D.T).trans D.sylowM.le
  set Nbar : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (proofN D) with hNbar
  set Q : Subgroup (MBar D.M D.U) := mbarImage D.M D.U (jOf D.T) with hQdef
  have hQN : Q ≤ Nbar := mbarImage_mono D.M D.U (uc22p22e_jOf_le D.sylowM)
  have hQ2 : IsPGroup 2 Q :=
    ((D.sylowM.isPGroup.to_le (uc22p22e_jOf_le_self D.T)).comap_subtype (K := D.M)).map _
  have himg : ∀ w ∈ natI ρ Nbar, (∀ a ∈ Q, ρ a w - w ∈ natC ρ Nbar) → ∀ a ∈ Q, ρ a w = w :=
    fun w hw hwC a ha => uc22p22xf_imgEI_of D Ch h2 h3 h51 hH c Umod e ρ hc w hw hwC a ha
  set xb : MBar D.M D.U := QuotientGroup.mk ⟨x, hxM⟩ with hxb
  have ht := mem_normalizer_mbarImage D hxM
  have hfix : ∀ v ∈ natI ρ Nbar ⊓ fixSub ρ Q, ρ xb v = v := by
    intro v hv
    have hvfix : v ∈ fixSub ρ Q := hv.2
    rw [hQdef, fixSub_mbarImage hV e ρ hc hJM] at hvfix
    have hz : iota e v ∈ centralizer ((jOf D.T : Subgroup G) : Set G) := mem_bsub.1 hvfix
    have hzE : iota e v ∈ proofE D :=
      uc22p22e_mem_omegaZJ'.2 ⟨uc22p22xf_UleT D (iota_mem e v),
        fun j hj => Subgroup.mem_centralizer_iff.1 hz j hj,
        (uc22p22xf_hel D).2 _ (iota_mem e v)⟩
    apply iota_injective e
    rw [hxb, iota_rho hV e ρ hc ⟨x, hxM⟩ v]
    exact hxE _ hzE
  obtain ⟨k, hk⟩ : ∃ k : ℕ, xb ^ (p ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hxp ⟨x, Subgroup.mem_zpowers x⟩
    refine ⟨k, ?_⟩
    have h1 : x ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have h2 : (⟨x, hxM⟩ : ↥D.M) ^ (p ^ k) = 1 := Subtype.ext (by simpa using h1)
    rw [hxb, ← QuotientGroup.mk_pow, h2]
    rfl
  have hpF : ∀ i, ¬ p ∣ Nat.card ↥(Nb i) := fun i hdvd =>
    hpN (hdvd.trans (Subgroup.card_dvd_of_le (d.le i)))
  have hcomm := d.commute_of_fixed hQN hQ2 himg ht hfix hpP hpF hk
  have hyM : y ∈ D.M := hJM hy
  have hyb : (QuotientGroup.mk ⟨y, hyM⟩ : MBar D.M D.U) ∈ Nbar :=
    hQN (Subgroup.mem_map_of_mem _ (show (⟨y, hyM⟩ : ↥D.M) ∈ (jOf D.T).subgroupOf D.M from hy))
  have h4 := hcomm _ hyb
  rw [← hxb] at h4
  have hw : (QuotientGroup.mk (⟨x, hxM⟩ * ⟨y, hyM⟩ * ⟨x, hxM⟩⁻¹ * ⟨y, hyM⟩⁻¹ : ↥D.M) :
      MBar D.M D.U) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv]
    change xb * QuotientGroup.mk ⟨y, hyM⟩ * xb⁻¹ * (QuotientGroup.mk ⟨y, hyM⟩)⁻¹ = 1
    rw [h4]
    group
  have hker := (QuotientGroup.eq_one_iff _).1 hw
  have hker' : (⟨x, hxM⟩ * ⟨y, hyM⟩ * ⟨x, hxM⟩⁻¹ * ⟨y, hyM⟩⁻¹ : ↥D.M) ∈ kerAct D.M D.U :=
    Subgroup.normalCore_le _ hker
  exact hker'

namespace P22k

omit [Finite G] in
theorem card_map_sylow {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ} [Fact p.Prime]
    (f : A →* B) (Q : Sylow p A) :
    Nat.card ((Q : Subgroup A).map f) = p ^ (Nat.card f.range).factorization p := by
  have hs : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have h1 := (Q.mapSurjective hs).card_eq_multiplicity
  have h2 : ((Q : Subgroup A).map f) = ((Q : Subgroup A).map f.rangeRestrict).map f.range.subtype := by
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  rw [h2, Subgroup.card_map_of_injective f.range.subtype_injective, ← h1, Sylow.coe_mapSurjective]

end P22k

theorem uc22k_exists_p_normalizing_jOf_bar (D : Data G) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ Nat.card ↥(mbarImage D.M D.U (proofN D))) :
    ∃ P : Subgroup G, P ≤ D.M ∧ IsPGroup p P ∧
      CFSG.ABGLocalTools.IsSylowOf p (mbarImage D.M D.U P) ⊤ ∧
      ∀ y ∈ P, ∀ x ∈ jOf D.T, y * x * y⁻¹ ∈ jOf D.T := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNM : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  have hMN := uc22p22t_M_le_normalizer_jOf D
  have hTN : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ proofN D) (proofN D) :=
    D.sylowM.inf_of_le_normalizer hNM hMN
  have hFr := uc22p22t_frattini_sup hNM hMN hTN
  set Hn : Subgroup G := D.M ⊓ normalizer ((D.T ⊓ proofN D : Subgroup G) : Set G) with hHn
  have hHnM : Hn ≤ D.M := inf_le_left
  have hMeq : proofN D ⊔ Hn = D.M := le_antisymm (sup_le hNM hHnM) hFr
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p Hn))
  set P : Subgroup G := (Q : Subgroup Hn).map Hn.subtype with hPdef
  have hPHn : P ≤ Hn := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  set π := QuotientGroup.mk' (kerAct D.M D.U).normalCore with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Nb := mbarImage D.M D.U (proofN D) with hNbdef
  set Hb := mbarImage D.M D.U Hn with hHbdef
  have hsup : Nb ⊔ Hb = ⊤ := by
    rw [hNbdef, hHbdef, mbarImage, mbarImage, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hNM hHnM, hMeq,
      Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ hπ
  have hNbn : Nb.Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hMN).map π hπ
  have hHbN : Hb ≤ normalizer (Nb : Set (MBar D.M D.U)) := fun g _ =>
    Subgroup.mem_normalizer_iff.2 fun n =>
      ⟨fun h => hNbn.conj_mem n h g, fun h => by simpa [mul_assoc] using hNbn.conj_mem _ h g⁻¹⟩
  have hcard := CFSG.LocalAnalysis.EvenBN.Tits.N.card_sup_mul_card_inf' hHbN
  rw [sup_comm, hsup] at hcard
  have hN0 : (Nat.card Nb).factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpN
  have hI0 : (Nat.card ↥(Hb ⊓ Nb)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd fun hd => hpN (hd.trans (Subgroup.card_dvd_of_le inf_le_right))
  have hfac := congrArg (fun n => n.factorization p) hcard
  rw [Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne'] at hfac
  simp only [Finsupp.add_apply, hN0, hI0, add_zero, zero_add] at hfac
  set f : ↥Hn →* MBar D.M D.U := π.comp (Subgroup.inclusion hHnM) with hfdef
  have hfr : f.range = Hb := by
    rw [hfdef, MonoidHom.range_comp, Subgroup.inclusion_range, hHbdef, mbarImage]
  have hQP : (Q : Subgroup Hn).map (Subgroup.inclusion hHnM) = P.subgroupOf D.M := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, hPdef]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, hqx⟩
      exact ⟨q, hq, Subtype.ext hqx⟩
  have hPb : (Q : Subgroup Hn).map f = mbarImage D.M D.U P := by
    rw [hfdef, ← Subgroup.map_map, hQP, mbarImage]
  have hcP := P22k.card_map_sylow f Q
  rw [hPb, hfr] at hcP
  refine ⟨P, hPHn.trans hHnM, Q.isPGroup'.map Hn.subtype, ?_, ?_⟩
  · refine CFSG.ABGLocalTools.isSylowOf_of_card le_top ?_
    rw [hcP, hfac]
  · intro y hy x hx
    have hyN : y ∈ normalizer ((D.T ⊓ proofN D : Subgroup G) : Set G) := (hPHn hy).2
    refine uc22p22e_conj_jOf (T := D.T) (fun x hx => ?_) x hx
    have hxTN : x ∈ D.T ⊓ proofN D :=
      ⟨uc22p22e_jOf_le_self D.T hx, uc22p22e_jOf_le D.sylowM hx⟩
    exact ((Subgroup.mem_normalizer_iff.1 hyN x).1 hxTN).1

theorem uc22k_s22_5_2Bar_of (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h31 : S22_3_1 D Ch) (hB : NatPFactBar D Ch) : S22_5_2Bar D Ch := by
  classical
  intro h1930 c p hp
  by_contra hpN
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPM, hPp, hPbar, hnJ⟩ := uc22k_exists_p_normalizing_jOf_bar D hpP hpN
  have hPE : ∀ y ∈ P, ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D := fun y hy =>
    uc22p22e_conj_omegaZJ (hnJ y hy) (fun x hx => by simpa using hnJ y⁻¹ (P.inv_mem hy) x hx)
  have hTE : ∀ y ∈ D.T, ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D := fun y hy =>
    uc22p22e_conj_omegaZJ (uc22p22e_normalizes_jOf_T D y hy)
      (fun x hx => by simpa using uc22p22e_normalizes_jOf_T D y⁻¹ (D.T.inv_mem hy) x hx)
  have hnormE : ∀ {Y : Subgroup G}, (∀ y ∈ Y, ∀ z ∈ proofE D, y * z * y⁻¹ ∈ proofE D) →
      Y ≤ normalizer (proofE D : Set G) := by
    intro Y hY y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact hY y hy z hz
    · intro hz
      have := hY y⁻¹ (Y.inv_mem hy) _ hz
      simpa [mul_assoc] using this
  set H₀ : Subgroup G := D.M ⊓ normalizer (proofE D : Set G) with hH₀
  set K : Subgroup G := D.M ⊓ centralizer (proofE D : Set G) with hK
  have hKH : K ≤ H₀ := inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hconj : ∀ h ∈ H₀, ∀ k ∈ K, h * k * h⁻¹ ∈ K := by
    intro h hh k hk
    obtain ⟨hhM, hhN⟩ := Subgroup.mem_inf.1 hh
    obtain ⟨hkM, hkC⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨D.M.mul_mem (D.M.mul_mem hhM hkM) (D.M.inv_mem hhM), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hN' := (Subgroup.mem_normalizer_iff.1 (inv_mem hhN)) e
    have he' : h⁻¹ * e * h ∈ proofE D := by
      have := hN'.1 he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.1 hkC _ he'
    calc e * (h * k * h⁻¹) = h * ((h⁻¹ * e * h) * k) * h⁻¹ := by group
      _ = h * (k * (h⁻¹ * e * h)) * h⁻¹ := by rw [h1]
      _ = h * k * h⁻¹ * e := by group
  have hHK : H₀ ≤ normalizer (K : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hconj h hh k hk
    · intro hk
      have := hconj h⁻¹ (H₀.inv_mem hh) _ hk
      simpa [mul_assoc] using this
  have hTH : D.T ≤ H₀ := fun y hy => ⟨D.sylowM.le hy, hnormE hTE hy⟩
  have hSylH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H₀ := D.sylowM.of_le hTH inf_le_left
  have hSK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K := hSylH.inf_of_le_normalizer hKH hHK
  have hSeq : D.T ⊓ K = proofS D := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT, hxK⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxT, (Subgroup.mem_inf.1 hxK).2⟩
    · intro hx
      obtain ⟨hxT, hxC⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨hxT, Subgroup.mem_inf.2 ⟨D.sylowM.le hxT, hxC⟩⟩
  have hPH : P ≤ H₀ := fun y hy => ⟨hPM hy, hnormE hPE hy⟩
  have hPK : P ⊓ K ≤ centralizer (D.U : Set G) := by
    intro x hx
    obtain ⟨hxP, hxK⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨_, hxC⟩ := Subgroup.mem_inf.1 hxK
    have hxM : x ∈ D.M := hPM hxP
    have hxp : IsPGroup p (Subgroup.zpowers x) := hPp.to_le (Subgroup.zpowers_le.2 hxP)
    have hxE : ∀ z ∈ proofE D, x * z * x⁻¹ = z := fun z hz => by
      have h1 := Subgroup.mem_centralizer_iff.1 hxC z hz
      calc x * z * x⁻¹ = z * x * x⁻¹ := by rw [h1]
        _ = z := by group
    have hcomm := hB h1930 c p hp hpN x hxM hxp (hnJ x hxP) hxE
    refine uc22p22t_faithful_bar D hpP hp2 hxM hxp (fun y hy => ?_)
      (fun z hz _ => (Subgroup.mem_centralizer_iff.1 hxC z hz).symm)
    have h2 := (centralizer (D.U : Set G)).inv_mem (hcomm y hy)
    have e : (x * y * x⁻¹ * y⁻¹)⁻¹ = y * x * y⁻¹ * x⁻¹ := by group
    rwa [e] at h2
  have hrk : 1 < CFSG.pRank p (MBar D.M D.U) :=
    uc22p22n_one_lt_pRank_mbar D hx h61 (uc22p22e_inCalV_U D) c.hU p hp
  have hnc : ¬ IsCyclic ↥(mbarImage D.M D.U P) := by
    refine uc22p22e_not_isCyclic_sylow hpP hPbar ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    omega
  obtain ⟨X, hXH, hXp, hXnc, hXN⟩ :=
    uc22p22t_frattini_bar D hKH hHK inf_le_left (hSeq ▸ hSK) hPp hPH hPK hnc
  exact (h31 h1930 c).2 (uc22p22e_calCGS_le D h61 hp (hXH.trans inf_le_left) hXp hXnc hXN
    (inf_le_left : proofS D ≤ D.T))

theorem uc22k_s22_5_2Bar_holds (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h31 : S22_3_1 D Ch) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch) (h51 : S22_5_1 D Ch) : S22_5_2Bar D Ch :=
  uc22k_s22_5_2Bar_of D Ch hx h61 h31 (uc22k_natPFactBar_of D Ch h2 h3 h51)

theorem uc22k_exists_index_bar (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)}
    (hNb : NbarSplit D Nb) {p : ℕ} (hp : p.Prime)
    (hpN : p ∣ Nat.card ↥(mbarImage D.M D.U (proofN D))) : ∃ i, p ∣ Nat.card ↥(Nb i) := by
  classical
  by_contra hex
  have hcon : ∀ i, ¬ p ∣ Nat.card ↥(Nb i) := fun i hi => hex ⟨i, hi⟩
  have hnorm : ∀ i, (⨆ j, Nb j) ≤ normalizer (Nb i : Set (MBar D.M D.U)) := by
    intro i g hg
    rw [hNb.1.1] at hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => uc22p22v_internalDirect_conj hNb.1 i g hg x hx, fun hx => ?_⟩
    have := uc22p22v_internalDirect_conj hNb.1 i g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have hnot := uc22p22v_not_dvd_iSup Nb hnorm hp hcon Finset.univ
  have heq : (⨆ i ∈ (Finset.univ : Finset (Fin m)), Nb i) = mbarImage D.M D.U (proofN D) := by
    rw [← hNb.1.1]
    simp
  exact hnot (heq ▸ hpN)

end CFSG.LocalAnalysis.UniquenessCase.UC22
