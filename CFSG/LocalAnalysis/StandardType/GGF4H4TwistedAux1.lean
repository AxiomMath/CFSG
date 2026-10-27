module

public import CFSG.LocalAnalysis.StandardType.GGF4LabelH4Pieces
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrLabelJOfTcjK
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggF4TW_iso_twA2 {f : ℕ} {jj : LargeEvenLabel} (hiso : GGLabelIso ⟨.twA, 2, f⟩ jj) :
    jj = ⟨.twA, 2, f⟩ := by
  obtain ⟨t, r, n⟩ := jj
  simp [GGLabelIso] at hiso
  simp only [LargeEvenLabel.mk.injEq]
  rcases hiso with ⟨h1, h2, h3⟩ <;> subst_vars <;> simp_all

private theorem ggF4TW_zmod_eq_one_of_dvd {p a : ℕ} (h : p ∣ a - 1) (ha : 1 ≤ a) :
    ((a : ZMod p)) = 1 := by
  have h0 : ((a - 1 : ℕ) : ZMod p) = 0 :=
    (CharP.cast_eq_zero_iff (ZMod p) p (a - 1)).2 h
  rw [Nat.cast_sub ha, Nat.cast_one] at h0
  exact sub_eq_zero.mp h0

private theorem ggF4TW_dvd_pow_sub_one {p a m : ℕ} (h : p ∣ a - 1) (ha : 1 ≤ a) :
    p ∣ a ^ m - 1 := by
  have h1 : (a : ZMod p) = 1 := ggF4TW_zmod_eq_one_of_dvd h ha
  have h0 : ((a ^ m : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_pow, h1, one_pow]
  have hsub : ((a ^ m - 1 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub (one_le_pow₀ ha), Nat.cast_one, h0, sub_self]
  exact (CharP.cast_eq_zero_iff (ZMod p) p (a ^ m - 1)).1 hsub

private theorem ggF4TW_field_eq_of_dvd_bound {p f f₁ : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpf : p ∣ 2 ^ f + 1) (hf₁ : 1 ≤ f₁) (hdiv : f₁ ∣ f)
    (hsplit : p ∣ 2 ^ f₁ - 1 ∨ p ∣ 2 ^ f₁ + 1)
    (hbound : f ≤ 4 * f₁) (h3 : f = 3 * f₁ → False) : f₁ = f := by
  obtain ⟨m, rfl⟩ := hdiv
  have hf₁pos : 0 < f₁ := hf₁
  have hm4 : m ≤ 4 := by
    have h : f₁ * m ≤ 4 * f₁ := hbound
    rw [mul_comm 4 f₁] at h
    exact Nat.le_of_mul_le_mul_left h hf₁pos
  have hsplit' : p ∣ 2 ^ f₁ + 1 := by
    rcases hsplit with h | h
    · exfalso
      have hd : p ∣ 2 ^ (f₁ * m) - 1 := by
        have h' := ggF4TW_dvd_pow_sub_one (p := p) (a := 2 ^ f₁) (m := m) h
          (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
        simpa [pow_mul] using h'
      have h2 : p ∣ 2 := by
        have h' := Nat.dvd_sub hpf hd
        have ha : 1 ≤ 2 ^ (f₁ * m) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
        have hsub : (2 ^ (f₁ * m) + 1) - (2 ^ (f₁ * m) - 1) = 2 := by omega
        rwa [hsub] at h'
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact h
  have hneg : (2 : ZMod p) ^ f₁ = -1 := by
    have h0 : ((2 ^ f₁ + 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ f₁ + 1)).2 hsplit'
    push_cast at h0
    exact (add_eq_zero_iff_eq_neg).1 h0
  have hnegm : (2 : ZMod p) ^ (f₁ * m) = -1 := by
    have h0 : ((2 ^ (f₁ * m) + 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ (f₁ * m) + 1)).2 hpf
    push_cast at h0
    exact (add_eq_zero_iff_eq_neg).1 h0
  have hpoweq : (-1 : ZMod p) ^ m = -1 := by
    rw [pow_mul, hneg] at hnegm
    exact hnegm
  have hodd : Odd m := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    have h1 : (-1 : ZMod p) ^ m = 1 := h.neg_one_pow
    rw [h1] at hpoweq
    have h2 : (2 : ZMod p) = 0 := by
      have h' := congrArg (fun x : ZMod p => x + 1) hpoweq
      simpa only [one_add_one_eq_two, neg_add_cancel] using h'
    have hdvd2 : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).1 (by simpa using h2)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd2)
  obtain ⟨k, hk⟩ := hodd
  have hm13 : m = 1 ∨ m = 3 := by omega
  rcases hm13 with rfl | rfl
  · simp
  · exact (h3 (by ring)).elim

private theorem ggF4TW_nbrK_div {G : Type} [Group G] [Finite G] (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hI3 : GGNbrSubcomponentInput) (hK : GGInnerDiagOn Bs K) {labK : LargeEvenLabel}
    (hlabK : LargeEvenInLambda2 labK) (hhasK : GGHasLabel labK (K ⧸ Subgroup.center K)) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ labK.n ∣ labJ.n ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS : LargeEvenSStar p B x L := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hx : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hx
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hJK : J ≤ K := hI3 G p B x L D J hT hDJ y K hnb
  have hKrel := ggInnerDiagOn_relabel hRig hK hlabK hhasK
  have hKperf : commutator ↥K = ⊤ := hKrel.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hTCJ p hp hp2 lab hlab) hKrel
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, ⟨⟨hlabel, hBN, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hBN hxBs
  have hx1 : x ^ p = 1 := hBel.2 x hx
  have hxp : K.normalizerMonoidHom ⟨x, hxN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  let ψ : ↥K →* R := (θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥K := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (K.normalizerMonoidHom ⟨x, hxN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (K.normalizerMonoidHom ⟨x, hxN⟩ l) ?_⟩
    show ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hTC ↥K ψ hψsurj hψker hKperf _ hxp hφe (J.subgroupOf K) hJcomp
  refine ⟨labJ, hlabJ, ?_, ?_⟩
  · rwa [hlabel] at hdvd
  · exact ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)) hhasJ

def ggF4TW_OrderInput : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {J K : Subgroup G} {f f₁ : ℕ},
    J ≤ K → 2 ≤ f →
    GGHasLabel (⟨.twA, 2, f⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J) →
    (GGHasLabel (⟨.C, 3, f₁⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) →
        f ≤ 4 * f₁ ∧ (f = 3 * f₁ → False)) ∧
      ((GGHasLabel (⟨.twD, 4, f₁⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) →
          f ≤ 4 * f₁ ∧ (f = 3 * f₁ → False)) ∧
        (3 ∣ 2 ^ f + 1 →
          ((GGHasLabel (⟨.A, 5, 1⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K) ∨
              GGHasLabel (⟨.A, 6, 1⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K)) → False)))

@[expose] def GGF4H4Psl64Twisted
    : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (ks : Finset (Subgroup G)), GGF4SmallRes p B Bs x L D J ks →
    (∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) → ∀ f : ℕ, 2 ≤ f → p ∣ 2 ^ f + 1 →
      GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L) → GGF4JBlock p f L J → ∀ K ∈ ks, p = 5 →
        GGHasLabel ⟨.A, 5, 2⟩ (K ⧸ Subgroup.center K) → Subgroup.center K = ⊥ → False

private theorem ggF4TW_order_C3 (hOrd : ggF4TW_OrderInput) {G : Type} [Group G] [Finite G]
    {J K : Subgroup G} {f f₁ : ℕ}
    (hJK : J ≤ K) (hf : 2 ≤ f)
    (hK : GGHasLabel (⟨.C, 3, f₁⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K))
    (hJ : GGHasLabel (⟨.twA, 2, f⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J)) :
    f ≤ 4 * f₁ ∧ (f = 3 * f₁ → False) :=
  (hOrd (f := f) (f₁ := f₁) hJK hf hJ).1 hK

private theorem ggF4TW_order_twD4 (hOrd : ggF4TW_OrderInput) {G : Type} [Group G] [Finite G]
    {J K : Subgroup G} {f f₁ : ℕ}
    (hJK : J ≤ K) (hf : 2 ≤ f)
    (hK : GGHasLabel (⟨.twD, 4, f₁⟩ : LargeEvenLabel) (K ⧸ Subgroup.center K))
    (hJ : GGHasLabel (⟨.twA, 2, f⟩ : LargeEvenLabel) (J ⧸ Subgroup.center J)) :
    f ≤ 4 * f₁ ∧ (f = 3 * f₁ → False) :=
  (hOrd (f := f) (f₁ := f₁) hJK hf hJ).2.1 hK

private theorem ggF4TW_entryC
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} {f f₁ : ℕ} {K : Subgroup G}
    (hL : GGLBalanceInput) (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hP : GGStdSubPrimeInput)
    (hOrd : ggF4TW_OrderInput)
    (hres : GGF4SmallRes p B Bs x L D J ks) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) (hJB : GGF4JBlock p f L J)
    (hK : K ∈ ks) (hf₁ : 1 ≤ f₁) (hsplit : p ∣ 2 ^ f₁ - 1 ∨ p ∣ 2 ^ f₁ + 1)
    (hlab : GGHasLabel ⟨.C, 3, f₁⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.twD, 4, f₁⟩ (K ⧸ Subgroup.center K)) : f₁ = f := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hInnAll : GGInnerDiagAll p B Bs x L D J := hres.1.1.2.2.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hInnAll.2 y K hnb
  have hI3 : GGNbrSubcomponentInput := ggNbrSubcomponentInput_of_lBalance hL hP
  have hJK : J ≤ K := hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb
  have hJlab : GGHasLabel ⟨.twA, 2, f⟩ (J ⧸ Subgroup.center J) := (hJB.2 hpf hLlab).1
  have hΛJ : LargeEvenInLambda2 (⟨.twA, 2, f⟩ : LargeEvenLabel) := by
    refine ⟨by show 1 ≤ f; omega, ?_⟩
    show 2 ≤ 2 ∧ (2 = 2 → 2 ≤ f)
    exact ⟨by norm_num, fun _ => by omega⟩
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  rcases hlab with hC | hD
  · have hΛK : LargeEvenInLambda2 (⟨.C, 3, f₁⟩ : LargeEvenLabel) := by
      refine ⟨hf₁, ?_⟩
      show 2 ≤ 3 ∧ (3 = 2 → 2 ≤ f₁)
      exact ⟨by norm_num, fun _ => by omega⟩
    obtain ⟨labJ, hΛlabJ, hdvd, hhasJ⟩ := ggF4TW_nbrK_div hTCJ hRig hcfg hnb hI3 hInnK hΛK hC
    have hiso : GGLabelIso (⟨.twA, 2, f⟩ : LargeEvenLabel) labJ :=
      hRig _ _ _ hΛJ hΛlabJ hJlab hhasJ
    have hlabJ : labJ = ⟨.twA, 2, f⟩ := ggF4TW_iso_twA2 hiso
    subst hlabJ
    have horder := ggF4TW_order_C3 hOrd hJK hf hC hJlab
    exact ggF4TW_field_eq_of_dvd_bound hp hp2 hpf hf₁ hdvd hsplit horder.1 horder.2
  · have hΛK : LargeEvenInLambda2 (⟨.twD, 4, f₁⟩ : LargeEvenLabel) := by
      refine ⟨hf₁, ?_⟩
      show 2 ≤ 4
      norm_num
    obtain ⟨labJ, hΛlabJ, hdvd, hhasJ⟩ := ggF4TW_nbrK_div hTCJ hRig hcfg hnb hI3 hInnK hΛK hD
    have hiso : GGLabelIso (⟨.twA, 2, f⟩ : LargeEvenLabel) labJ :=
      hRig _ _ _ hΛJ hΛlabJ hJlab hhasJ
    have hlabJ : labJ = ⟨.twA, 2, f⟩ := ggF4TW_iso_twA2 hiso
    subst hlabJ
    have horder := ggF4TW_order_twD4 hOrd hJK hf hD hJlab
    exact ggF4TW_field_eq_of_dvd_bound hp hp2 hpf hf₁ hdvd hsplit horder.1 horder.2

private theorem ggF4TW_entrySU
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} {f f₁ : ℕ} {K : Subgroup G}
    (hL : GGLBalanceInput) (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hP : GGStdSubPrimeInput)
    (hres : GGF4SmallRes p B Bs x L D J ks) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) (hJB : GGF4JBlock p f L J)
    (hK : K ∈ ks) (hf₁ : 2 ≤ f₁) (hsplit : p ∣ 2 ^ f₁ - 1)
    (hlab : GGHasLabel ⟨.twA, 5, f₁⟩ (K ⧸ Subgroup.center K)) : False := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hInnAll : GGInnerDiagAll p B Bs x L D J := hres.1.1.2.2.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hInnK : GGInnerDiagOn Bs K := hInnAll.2 y K hnb
  have hI3 : GGNbrSubcomponentInput := ggNbrSubcomponentInput_of_lBalance hL hP
  have hJlab : GGHasLabel ⟨.twA, 2, f⟩ (J ⧸ Subgroup.center J) := (hJB.2 hpf hLlab).1
  have hΛJ : LargeEvenInLambda2 (⟨.twA, 2, f⟩ : LargeEvenLabel) := by
    refine ⟨by show 1 ≤ f; omega, ?_⟩
    show 2 ≤ 2 ∧ (2 = 2 → 2 ≤ f)
    exact ⟨by norm_num, fun _ => by omega⟩
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hΛK : LargeEvenInLambda2 (⟨.twA, 5, f₁⟩ : LargeEvenLabel) := by
    refine ⟨by show 1 ≤ f₁; omega, ?_⟩
    show 2 ≤ 5 ∧ (5 = 2 → 2 ≤ f₁)
    exact ⟨by norm_num, fun _ => by omega⟩
  obtain ⟨labJ, hΛlabJ, hdvd, hhasJ⟩ := ggF4TW_nbrK_div hTCJ hRig hcfg hnb hI3 hInnK hΛK hlab
  have hiso : GGLabelIso (⟨.twA, 2, f⟩ : LargeEvenLabel) labJ :=
    hRig _ _ _ hΛJ hΛlabJ hJlab hhasJ
  have hlabJ : labJ = ⟨.twA, 2, f⟩ := ggF4TW_iso_twA2 hiso
  subst hlabJ
  obtain ⟨m, hm⟩ := hdvd
  have hm' : f = f₁ * m := hm
  have hd : p ∣ 2 ^ f - 1 := by
    rw [hm']
    simpa [pow_mul] using
      ggF4TW_dvd_pow_sub_one hsplit (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
  have h2 : p ∣ 2 := by
    have h' := Nat.dvd_sub hpf hd
    have ha : 1 ≤ 2 ^ f := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    have hsub : (2 ^ f + 1) - (2 ^ f - 1) = 2 := by omega
    rwa [hsub] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

private theorem ggF4TW_entryLin
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} {f : ℕ} {K : Subgroup G}
    (hL : GGLBalanceInput) (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hP : GGStdSubPrimeInput)
    (hOrd : ggF4TW_OrderInput)
    (hres : GGF4SmallRes p B Bs x L D J ks) (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) (hJB : GGF4JBlock p f L J)
    (hK : K ∈ ks) (hp3 : p = 3)
    (hlab : GGHasLabel ⟨.A, 5, 1⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.A, 6, 1⟩ (K ⧸ Subgroup.center K)) : False := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hI3 : GGNbrSubcomponentInput := ggNbrSubcomponentInput_of_lBalance hL hP
  have hJK : J ≤ K := hI3 G p B x L D J hcfg.1 hcfg.2.2 y K hnb
  have hJlab : GGHasLabel ⟨.twA, 2, f⟩ (J ⧸ Subgroup.center J) := (hJB.2 hpf hLlab).1
  exact (hOrd (f := f) (f₁ := 0) hJK hf hJlab).2.2 (hp3 ▸ hpf) hlab

private theorem ggF4TW_entryPsl64
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} {f : ℕ} {K : Subgroup G}
    (hPsl : GGF4H4Psl64Twisted)
    (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs))
    (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L)) (hJB : GGF4JBlock p f L J)
    (hK : K ∈ ks) (hp5 : p = 5) (hlab : GGHasLabel ⟨.A, 5, 2⟩ (K ⧸ Subgroup.center K))
    (hZ : Subgroup.center K = ⊥) : False :=
  hPsl G p B Bs x L D J ks hres hB f hf hpf hLlab hJB K hK hp5 hlab hZ

theorem ggF4TW_twistedNbrLabel
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {ks : Finset (Subgroup G)} {f : ℕ} {K : Subgroup G}
    (hL : GGLBalanceInput) (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hP : GGStdSubPrimeInput)
    (hOrd : ggF4TW_OrderInput) (hPslTw : GGF4H4Psl64Twisted)
    (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs))
    (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (hLlab : GGHasLabel ⟨.twA, 3, f⟩ (L ⧸ Subgroup.center L))
    (hJB : GGF4JBlock p f L J)
    (hK : K ∈ ks) (hlist : GGF4NbrList p K) :
    GGHasLabel ⟨.C, 3, f⟩ (K ⧸ Subgroup.center K) ∨
      GGHasLabel ⟨.twD, 4, f⟩ (K ⧸ Subgroup.center K) := by
  rcases hlist with ⟨f₁, hf₁, hsplit, hC | hD⟩ | ⟨hp3, hA5 | hA6⟩ | ⟨hp5, hA52, hZ⟩ |
    ⟨f₁, hf₁, hsplit, hSU⟩
  · have heq := ggF4TW_entryC hL hRig hTCJ hP hOrd hres hf hpf hLlab hJB hK hf₁ hsplit
      (Or.inl hC)
    subst heq
    exact Or.inl hC
  · have heq := ggF4TW_entryC hL hRig hTCJ hP hOrd hres hf hpf hLlab hJB hK hf₁ hsplit
      (Or.inr hD)
    subst heq
    exact Or.inr hD
  · exact (ggF4TW_entryLin hL hRig hTCJ hP hOrd hres hf hpf hLlab hJB hK hp3 (Or.inl hA5)).elim
  · exact (ggF4TW_entryLin hL hRig hTCJ hP hOrd hres hf hpf hLlab hJB hK hp3 (Or.inr hA6)).elim
  · exact (ggF4TW_entryPsl64 hPslTw hres hB hf hpf hLlab hJB hK hp5 hA52 hZ).elim
  · exact (ggF4TW_entrySU hL hRig hTCJ hP hres hf hpf hLlab hJB hK hf₁ hsplit hSU).elim

end CFSG.StandardType

end
