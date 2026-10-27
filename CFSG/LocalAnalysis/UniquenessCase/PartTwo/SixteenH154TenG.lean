module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC34Ten
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s16h_ten_exists_E (D : Data G) {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V)
    (h116 : C116 D V₀ V) (h118 : C118 D V₀ V)
    [hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M))
    {Xbar : Subgroup (F11.MBar11 D.M V₀ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆)
    {v : G} (hvV : v ∈ V)
    (hrank : 1 < CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v))) :
    ∃ E : Subgroup G,
      E ≤ F11.Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ∧
      E ≤ F11.CElt D.M V₀ v ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ 2 := by
  set T : Subgroup G := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar with hT
  set Z : Subgroup G := T ⊓ F11.CTilde D.M V₀ V with hZ
  obtain ⟨hTp, hZc, hZT, hcomm, hcent, hpow, hTM, hbar⟩ :=
    s16c34_ten_tdata D hV h116 h118 hp hp2 hP hXe hXle (T := T) (Z := Z) hT hZ
  have hCS : F11.CTilde D.M V₀ V ≤ F11.CElt D.M V₀ v := by
    rw [F11.CTilde]
    exact iInf₂_le v hvV
  set S : Subgroup G := T ⊓ F11.CElt D.M V₀ v with hS
  have hST : S ≤ T := inf_le_left
  have hZS : Z ≤ S := le_inf hZT (inf_le_right.trans hCS)
  have hSp : IsPGroup p ↥S := hTp.to_le hST
  have hScomm : ⁅S, S⁆ ≤ Z := (Subgroup.commutator_mono hST hST).trans hcomm
  have hScent : ⁅S, Z⁆ = ⊥ := le_bot_iff.1 ((Subgroup.commutator_mono hST le_rfl).trans hcent.le)
  have hSpow : ∀ t ∈ S, t ^ p ∈ Z := fun t ht => hpow t ht.1
  have hSZ : S ⊓ F11.CTilde D.M V₀ V = Z := by
    ext x
    constructor
    · rintro ⟨⟨hxT, -⟩, hx⟩
      exact ⟨hxT, hx⟩
    · rintro ⟨hxT, hx⟩
      exact ⟨⟨hxT, hCS hx⟩, hx⟩
  have hSW : F11.barImage11 D.M V₀ V S =
      Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 hq
      exact ⟨hbar ▸ uc22p22u_mem_barImage11.2 ⟨m, hm.1, rfl⟩,
        uc22p22u_mem_barImage11.2 ⟨m, hm.2, rfl⟩⟩
    · rintro q ⟨hqX, hqC⟩
      obtain ⟨m, hm, rfl⟩ := uc22p22u_mem_barImage11.1 (hbar ▸ hqX)
      obtain ⟨m', hm', hmm'⟩ := uc22p22u_mem_barImage11.1 hqC
      have h1 : ((m'⁻¹ * m : ↥D.M) : G) ∈ F11.CTilde D.M V₀ V :=
        uc22p22u_mk_eq_iff.1 hmm'
      refine uc22p22u_mem_barImage11.2 ⟨m, ⟨hm, ?_⟩, rfl⟩
      have h3 : (m : G) = (m' : G) * ((m'⁻¹ * m : ↥D.M) : G) := by simp
      rw [h3]
      exact (F11.CElt D.M V₀ v).mul_mem hm' (hCS h1)
  have hcardS := uc22p22u_card_eq_barImage11_mul (M := D.M) (V₀ := V₀) (V := V)
    (hST.trans hTM)
  rw [hSW, hSZ] at hcardS
  have hS2 : p ^ 2 * Nat.card ↥Z ≤ Nat.card ↥S := by
    obtain ⟨E₀, hE₀W, hE₀e, hE₀c⟩ := CFSG.SectionRank.exists_pRank hp.one_lt
      (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v))
    have h1 : p ^ 2 ≤ Nat.card ↥(Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) := by
      calc p ^ 2 ≤ p ^ CFSG.Open.pRank p
              (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v)) :=
            Nat.pow_le_pow_right hp.pos hrank
        _ = Nat.card ↥E₀ := hE₀c.symm
        _ ≤ _ := Subgroup.card_le_of_le hE₀W
    rw [hcardS]
    exact Nat.mul_le_mul_right _ h1
  obtain ⟨E, hEΩ, hEe, hEc⟩ := uc22p22u_exists_elemAbelian_omega1 hp hp2 hSp hZc hZS hScomm
    hScent hSpow hS2
  have hΩS : F11.Omega1p p S ≤ S := (Subgroup.closure_le S).2 fun x hx => hx.1
  have hΩT : F11.Omega1p p S ≤ F11.Omega1p p T :=
    Subgroup.closure_mono fun x hx => ⟨hST hx.1, hx.2⟩
  exact ⟨E, hEΩ.trans hΩT, hEΩ.trans (hΩS.trans inf_le_right), hEe, hEc⟩

theorem s16h_ten_normalizer_le {M V₀ V P : Subgroup G}
    [((F11.CTilde M V₀ V).subgroupOf M).Normal] {Xbar : Subgroup (F11.MBar11 M V₀ V)}
    [Xbar.Normal] :
    M ⊓ normalizer (P : Set G) ≤
      normalizer ((P ⊓ ⁅M, M⁆ ⊓ F11.barPreimage11 M V₀ V Xbar : Subgroup G) : Set G) := by
  intro g hg
  have hgP : g ∈ normalizer (P : Set G) := hg.2
  have hgM : g ∈ M := hg.1
  have h1 := uc22p22u_mem_normalizer_commutator hgM
  have h2 := uc22p22u_mem_normalizer_barPreimage11 (Xbar := Xbar) hgM
  refine mem_normalizer_iff.2 fun x => ?_
  constructor
  · rintro ⟨⟨hxP, hxc⟩, hxX⟩
    exact ⟨⟨(mem_normalizer_iff.1 hgP x).1 hxP, (mem_normalizer_iff.1 h1 x).1 hxc⟩,
      (mem_normalizer_iff.1 h2 x).1 hxX⟩
  · rintro ⟨⟨hxP, hxc⟩, hxX⟩
    exact ⟨⟨(mem_normalizer_iff.1 hgP x).2 hxP, (mem_normalizer_iff.1 h1 x).2 hxc⟩,
      (mem_normalizer_iff.1 h2 x).2 hxX⟩

theorem s16h_ten_gamma (D : Data G) (hSig : UC6S846.SigmaStd D) (h77 : F07.R77Eq D)
    (hσ : D.sig = D.sig1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P T E : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M)) (hTP : T ≤ P) (hTM : T ≤ D.M)
    (hclT : ⁅⁅T, T⁆, T⁆ = ⊥) (hN : D.M ⊓ normalizer (P : Set G) ≤ normalizer (T : Set G))
    (hE : E ≤ F11.Omega1p p T) (hEe : IsElemAbelian p E) (hEc : Nat.card ↥E = p ^ 2) :
    rankThreeGamma 1 p E ≤ D.M ∨ p ∈ D.sig := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hTp : IsPGroup p ↥T := ((CFSG.ABGLocalTools.isSylowOf_iff.1 hP).2.1).to_le hTP
  by_cases hpσ : p ∈ D.sig
  · exact Or.inr hpσ
  refine Or.inl ?_
  obtain ⟨p₁, hp₁⟩ := hSig.nonempty
  have hp₁1 : p₁ ∈ D.sig1 := hσ ▸ hp₁
  have hsp := hSig.sig1_sp p₁ hp₁1
  obtain ⟨hp₁pr, hp₁2⟩ := D.sig_prime p₁ hp₁
  have hp₁p : p₁ ≠ p := fun h => hpσ (h ▸ hp₁)
  set Y : Subgroup G := F11.Omega1p p T with hY
  have hYT : Y ≤ T := (Subgroup.closure_le T).2 fun x hx => hx.1
  have hYM : Y ≤ D.M := hYT.trans hTM
  have hYp : IsPGroup p ↥Y := hTp.to_le hYT
  have hEY : E ≤ Y := hE
  have hEnc : ¬ IsCyclic ↥E := uc22p22u_not_isCyclic_of_card_sq hp hEe hEc
  have hYnc : ¬ IsCyclic ↥Y := by
    intro hc
    haveI := hc
    exact hEnc (isCyclic_of_injective (Subgroup.inclusion hEY) (Subgroup.inclusion_injective hEY))
  have hYexp : ∀ x ∈ Y, x ^ p = 1 := uc22p22u_omega1p_exponent hp hp2 hTp hclT
  have hYcl : ⁅⁅Y, Y⁆, Y⁆ = ⊥ :=
    le_bot_iff.1 ((Subgroup.commutator_mono (Subgroup.commutator_mono hYT hYT) hYT).trans hclT.le)
  have hNY : D.M ⊓ normalizer (P : Set G) ≤ D.M ⊓ normalizer (Y : Set G) :=
    le_inf inf_le_left fun g hg => uc22p22u_mem_normalizer_Omega1p (hN hg)
  haveI : (CFSG.pCore p (Bar2 D.M)).Normal := CFSG.pCore_normal
  have hOn : D.M ≤ normalizer ((F11.O2p p D.M : Subgroup G) : Set G) :=
    uc22p22u_barPreimage_normalizes (D := CFSG.pCore p (Bar2 D.M))
  have hp₁O : ¬ p₁ ∣ Nat.card ↥(F11.O2p p D.M) := by
    have hcard : Nat.card ↥(F11.O2p p D.M) =
        Nat.card ↥(pCoreOf 2 D.M) * Nat.card ↥(CFSG.pCore p (Bar2 D.M)) :=
      uc22p22u_card_barPreimage D.M (CFSG.pCore p (Bar2 D.M))
    rw [hcard]
    intro hd
    rcases (Nat.Prime.dvd_mul hp₁pr).1 hd with h | h
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (uc22p21c_isPGroup_pCoreOf D.M)
      rw [hk] at h
      exact hp₁2 ((Nat.prime_dvd_prime_iff_eq hp₁pr Nat.prime_two).1 (hp₁pr.dvd_of_dvd_pow h))
    · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M))
      rw [hk] at h
      exact hp₁p ((Nat.prime_dvd_prime_iff_eq hp₁pr hp).1 (hp₁pr.dvd_of_dvd_pow h))
  have hrk := uc22p22u_pRank_le_normalizer_sylow hp₁pr hp (uc22p21c_barPreimage_le D.M _) hOn hP
    hp₁O
  have hrk' : CFSG.Open.pRank p₁ (D.M ⊓ normalizer (Y : Set G)) ≤ CFSG.Open.pRank p₁ D.M :=
    CFSG.SectionRank.pRank_mono hp₁pr.one_lt inf_le_left
  have hrk'' : CFSG.Open.pRank p₁ (D.M ⊓ normalizer (P : Set G)) ≤
      CFSG.Open.pRank p₁ (D.M ⊓ normalizer (Y : Set G)) :=
    CFSG.SectionRank.pRank_mono hp₁pr.one_lt hNY
  have hthree : 3 ≤ CFSG.Open.pRank p₁ D.M := hSig.three_le p₁ hp₁
  have hΓY := h77 hσ.subset p₁ hp₁ hp₁2 hsp p hp hp2 hpσ Y hYM hYp hYnc hYexp hYcl (by omega)
    (le_antisymm (hrk.trans hrk'') hrk')
  exact (uc22p22u_gamma_mono hEY).trans hΓY

theorem s16h_exists_conj_le_of_not_dvd_relIndex {p : ℕ} (hp : p.Prime) {K H B : Subgroup G}
    (hBK : B ≤ K) (hindex : ¬ p ∣ H.relIndex K) (hB : IsPGroup p B) :
    ∃ k ∈ K, conjSubgroup B k ≤ H := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Hk : Subgroup ↥K := H.subgroupOf K
  have hBk : IsPGroup p (B.subgroupOf K) :=
    hB.of_equiv (Subgroup.subgroupOfEquivOfLe hBK).symm
  have hindexK : ¬ p ∣ Nat.card (↥K ⧸ Hk) := by
    rw [← Subgroup.index_eq_card (H := Hk)]
    exact hindex
  obtain ⟨q, hq⟩ := hBk.nonempty_fixed_point_of_prime_not_dvd_card (↥K ⧸ Hk) hindexK
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hfix : ∀ x : B.subgroupOf K, k⁻¹ * (x : ↥K) * k ∈ Hk := by
    intro x
    have hb : ((x⁻¹ : B.subgroupOf K) : ↥K) • (QuotientGroup.mk k : ↥K ⧸ Hk) =
        QuotientGroup.mk k := by
      have := (MulAction.mem_fixedPoints.mp hq) x⁻¹
      simpa only [Subgroup.smul_def] using this
    have hb' : (QuotientGroup.mk (((x⁻¹ : B.subgroupOf K) : ↥K) * k) : ↥K ⧸ Hk) =
        QuotientGroup.mk k := by
      change ((x⁻¹ : B.subgroupOf K) : ↥K) • (QuotientGroup.mk k : ↥K ⧸ Hk) =
        QuotientGroup.mk k
      exact hb
    have h := QuotientGroup.eq.mp hb'
    have heq : ((((x⁻¹ : B.subgroupOf K) : ↥K)) * k)⁻¹ * k = k⁻¹ * (x : ↥K) * k := by
      rw [Subgroup.coe_inv (x := x)]
      group
    rwa [heq] at h
  refine ⟨(k : G), k.2, ?_⟩
  intro x hx
  rw [mem_conjSubgroup_iff] at hx
  have hxK : (k : G) * x * (k : G)⁻¹ ∈ K := hBK hx
  have h4 := hfix ⟨⟨(k : G) * x * (k : G)⁻¹, hxK⟩, hx⟩
  have h4' : ((k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G)) ∈ H := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_subgroupOf).1 h4
  have h5 : (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (k : G) = x := by group
  rwa [h5] at h4'

private theorem s16h_conjSubgroup_eq_self_of_mem {M : Subgroup G} {y : G} (hy : y ∈ M) :
    conjSubgroup M y = M := by
  ext x
  rw [mem_conjSubgroup_iff]
  constructor
  · intro h
    have := M.mul_mem (M.mul_mem (M.inv_mem hy) h) hy
    simpa [mul_assoc] using this
  · intro hx
    exact M.mul_mem (M.mul_mem hy hx) (M.inv_mem hy)

theorem s16h_uniqueMax_cent_of_pRank (D : Data G) (hSig : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h869 : F08.R869 D)
    (h111 : F11.R111 D) (h112 : F11.R112 D) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    {V₀ V : Subgroup G} (hV : F11.Hyp11 D V₀ V) (h4 : Nat.card V₀ ≤ 4)
    [hNorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal] (hσ : D.sig = D.sig1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf p P (F11.O2p p D.M))
    {Xbar : Subgroup (F11.MBar11 D.M V₀ V)} [hXn : Xbar.Normal] (hXe : IsElemAbelian p Xbar)
    (hXle : Xbar ≤ ⁅(⊤ : Subgroup (F11.MBar11 D.M V₀ V)), (⊤ : Subgroup (F11.MBar11 D.M V₀ V))⁆)
    {v : G} (hvV : v ∈ V) (hvV₀ : v ∉ V₀)
    (hrank : 1 < CFSG.Open.pRank p (Xbar ⊓ F11.barImage11 D.M V₀ V (F11.CElt D.M V₀ v))) :
    UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)) := by
  have h116 := ElevenNine.c116_of_hyp11 D hSig h61 h63 h77 h111 h112 hV
  have h117 := ElevenNine.c117_of_hyp11 D h869 hV
  have h118 := ElevenNine.c118_of_hyp11 hThin hCyc D hV h116 h117
  obtain ⟨E, hEΩ, hEK, hEe, hEc⟩ := s16h_ten_exists_E D hV h116 h118 hp hp2 hP hXe hXle hvV hrank
  have hEnc : ¬ IsCyclic ↥E := uc22p22u_not_isCyclic_of_card_sq hp hEe hEc
  have hEp : IsPGroup p ↥E := CFSG.Open.IsElemAbelian.isPGroup hEe
  obtain ⟨hTp, hZc, hZT, hcomm, hcent, hpow, hTM, hbar⟩ :=
    s16c34_ten_tdata D hV h116 h118 hp hp2 hP hXe hXle
      (T := P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar)
      (Z := (P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar) ⊓ F11.CTilde D.M V₀ V) rfl rfl
  have hclT : ⁅⁅P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar,
      P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar⁆,
      P ⊓ ⁅D.M, D.M⁆ ⊓ F11.barPreimage11 D.M V₀ V Xbar⁆ = ⊥ := by
    rw [eq_bot_iff, ← hcent]
    exact (Subgroup.commutator_mono hcomm le_rfl).trans (by rw [Subgroup.commutator_comm])
  have hΓ := s16h_ten_gamma D hSig h77 hσ hp hp2 hP
    (inf_le_left.trans inf_le_left) hTM hclT s16h_ten_normalizer_le hEΩ hEe hEc
  have hEM : E ≤ D.M := hEK.trans (fun x hx => hx.1)
  have hU : UniqueMax D.M E := uc22p22u_uniqueMax_of_noncyclic D h61 h63 hp hp2 hEM hEp hEnc hΓ
  obtain ⟨n, -, hn⟩ := r113_holds D V₀ V hV h4 v hvV hvV₀
  have hindex : ¬ p ∣ (D.M ⊓ centralizer ({v} : Set G)).relIndex (F11.CElt D.M V₀ v) := by
    rw [hn]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  obtain ⟨k, hk, hEk⟩ := s16h_exists_conj_le_of_not_dvd_relIndex hp hEK hindex hEp
  have h1 := uniqueMax_conjSubgroup hU k
  rw [s16h_conjSubgroup_eq_self_of_mem hk.1] at h1
  exact uc22p22u_uniqueMax_mono D hEk inf_le_left h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
