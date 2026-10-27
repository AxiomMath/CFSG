module

public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

theorem le_centralizer_sup {D V₁ V₂ : Subgroup G} (h₁ : D ≤ Subgroup.centralizer (V₁ : Set G))
    (h₂ : D ≤ Subgroup.centralizer (V₂ : Set G)) :
    D ≤ Subgroup.centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) := by
  intro x hx
  have hle : V₁ ⊔ V₂ ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun v hv => ?_) (fun v hv => ?_)
    · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 (h₁ hx) v hv).symm
    · refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 (h₂ hx) v hv).symm
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) x rfl).symm

end B2F

section TwoReduced

variable [Finite G] {H V : Subgroup G}

theorem pCoreOf_le_centralizer_of_isTwoReducedIn (h : IsTwoReducedIn H V) :
    pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G) := by
  refine h.2.2.2 (pCoreOf 2 H) (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H) fun d hd => ?_
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

omit [Finite G] in
theorem le_pCoreOf_of_isTwoReducedIn (h : IsTwoReducedIn H V) : V ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 h.1 h.2.1 (B2F.isPGroup_of_isElemAbelian h.2.2.1)

theorem commute_of_isTwoReducedIn (h : IsTwoReducedIn H V) {v w : G} (hv : v ∈ V)
    (hw : w ∈ pCoreOf 2 H) : v * w = w * v :=
  Subgroup.mem_centralizer_iff.1 (pCoreOf_le_centralizer_of_isTwoReducedIn h hw) v hv

omit [Finite G] in
theorem isTwoReducedIn_bot (H : Subgroup G) : IsTwoReducedIn H (⊥ : Subgroup G) := by
  refine ⟨bot_le, ?_, ⟨inferInstance, fun x hx => ?_⟩, fun D _ _ _ => ?_⟩
  · intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have : x = 1 := hx
      simp [this]
    · intro hx
      have : g * x * g⁻¹ = 1 := hx
      have hx1 : x = 1 := by simpa using this
      simp [hx1]
  · have : x = 1 := hx
    simp [this]
  · intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have : h = 1 := hh
    simp [this]

theorem isTwoReducedIn_sup {V₁ V₂ : Subgroup G} (h₁ : IsTwoReducedIn H V₁)
    (h₂ : IsTwoReducedIn H V₂) : IsTwoReducedIn H (V₁ ⊔ V₂) := by
  refine ⟨sup_le h₁.1 h₂.1, B2F.le_normalizer_sup h₁.2.1 h₂.2.1, ?_, ?_⟩
  · exact B2F.isElemAbelian_sup_of_commute h₁.2.2.1 h₂.2.2.1 fun a ha b hb =>
      commute_of_isTwoReducedIn h₁ ha (le_pCoreOf_of_isTwoReducedIn h₂ hb)
  · intro D hDH hDN hD
    have hD₁ : D ≤ Subgroup.centralizer (V₁ : Set G) :=
      h₁.2.2.2 D hDH hDN fun d hd =>
        (hD d hd).imp fun _ hk => Subgroup.centralizer_le (le_sup_left : V₁ ≤ V₁ ⊔ V₂) hk
    have hD₂ : D ≤ Subgroup.centralizer (V₂ : Set G) :=
      h₂.2.2.2 D hDH hDN fun d hd =>
        (hD d hd).imp fun _ hk => Subgroup.centralizer_le (le_sup_right : V₂ ≤ V₁ ⊔ V₂) hk
    exact B2F.le_centralizer_sup hD₁ hD₂

theorem exists_isTwoReducedIn_max (H : Subgroup G) :
    ∃ M : Subgroup G, IsTwoReducedIn H M ∧ ∀ V : Subgroup G, IsTwoReducedIn H V → V ≤ M := by
  obtain ⟨M, hM, hmax⟩ := Set.exists_max_image {V : Subgroup G | IsTwoReducedIn H V}
    (fun V => Nat.card V) (Set.toFinite _) ⟨⊥, isTwoReducedIn_bot H⟩
  refine ⟨M, hM, fun V hV => ?_⟩
  have h := isTwoReducedIn_sup hM hV
  have : M = M ⊔ V := Subgroup.eq_of_le_of_card_ge le_sup_left (hmax _ h)
  rw [this]
  exact le_sup_right

@[expose] def twoReducedMax (H : Subgroup G) : Subgroup G :=
  ⨆ (V : Subgroup G) (_ : IsTwoReducedIn H V), V

omit [Finite G] in
theorem le_twoReducedMax (h : IsTwoReducedIn H V) : V ≤ twoReducedMax H :=
  le_iSup₂_of_le V h le_rfl

theorem isTwoReducedIn_twoReducedMax (H : Subgroup G) :
    IsTwoReducedIn H (twoReducedMax H) := by
  obtain ⟨M, hM, hmax⟩ := exists_isTwoReducedIn_max H
  have : twoReducedMax H = M :=
    le_antisymm (iSup_le fun V => iSup_le fun hV => hmax V hV) (le_twoReducedMax hM)
  rw [this]
  exact hM

end TwoReduced

namespace B2F

theorem omegaOneCenter_le_inf_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) := by
  unfold quasithinOmegaOneCenter
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1

end B2F

section Thompson

variable [Finite G] {H T : Subgroup G}

theorem pCoreOf_le_of_isSylowTwoOf (hT : IsSylowTwoOf T H) : pCoreOf 2 H ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 H :=
    (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).toSylow hT.2.2
  have hn : (pCore 2 H).Normal := pCore_normal 2
  have hle : pCore 2 H ≤ (T' : Subgroup H) := (pCore_isPGroup 2).le_sylow_of_normal T'
  rintro _ ⟨y, hy, rfl⟩
  have := hle hy
  simp only [T', IsPGroup.toSylow_coe] at this
  exact Subgroup.mem_subgroupOf.1 this

theorem conjClosure_le_of_isSylowTwoOf (hT : IsSylowTwoOf T H) {Z : Subgroup G}
    (hZT : Z ≤ quasithinOmegaOneCenter T) (hZO : Z ≤ pCoreOf 2 H) :
    conjClosure Z H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (conjClosure Z H) := by
  have hOT := pCoreOf_le_of_isSylowTwoOf hT
  have hZC : Z ≤ Subgroup.centralizer (pCoreOf 2 H : Set G) := fun z hz =>
    Subgroup.centralizer_le hOT (B2F.omegaOneCenter_le_inf_centralizer T (hZT hz)).2
  have hle : conjClosure Z H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    refine conjClosure_le fun h hh z hz => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 H hh) z).1 (hZO hz)
    · refine Subgroup.mem_centralizer_iff.2 fun o ho => ?_
      have hho : h⁻¹ * o * h ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff''.1 (le_normalizer_pCoreOf 2 H hh) o).1 ho
      have hc := Subgroup.mem_centralizer_iff.1 (hZC hz) _ hho
      calc o * (h * z * h⁻¹) = h * ((h⁻¹ * o * h) * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * o * h)) * h⁻¹ := by rw [hc]
        _ = h * z * h⁻¹ * o := by group
  refine ⟨hle, ?_⟩
  have hS : ∀ a ∈ {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x},
      ∀ b ∈ {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x}, a * b = b * a := by
    intro a ha b hb
    have ha' := hle (Subgroup.subset_closure ha)
    have hb' := hle (Subgroup.subset_closure hb)
    exact (Subgroup.mem_centralizer_iff.1 ha'.2 b hb'.1).symm
  have h2 : ∀ a ∈ {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x}, a ^ 2 = 1 := by
    rintro _ ⟨h, -, z, hz, rfl⟩
    rw [conj_pow, sq_eq_one_of_mem_omegaOneCenter T (hZT hz), mul_one, mul_inv_cancel]
  exact B2F.isElemAbelian_closure hS h2

theorem le_sup_inf_of_two_power (hT : IsSylowTwoOf T H) {K D : Subgroup G} (hDH : D ≤ H)
    (hTD : T ≤ Subgroup.normalizer (D : Set G)) (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) : D ≤ (K ⊓ D) ⊔ (T ⊓ D) := by
  have hpow : ∃ n : ℕ, K.relIndex D = 2 ^ n := by
    have := Subgroup.normal_subgroupOf_of_le_normalizer hDK
    have hp : IsPGroup 2 (D ⧸ K.subgroupOf D) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H d =>
        obtain ⟨k, hk⟩ := hD d d.2
        refine ⟨k, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using hk
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hpow
  have hodd := not_two_dvd_relIndex_inf_of_normalizer (S := T) (D := D) (K := H) hT.1 hDH hT.2.2 hTD
  rw [← Subgroup.relIndex_eq_one]
  have h1 : ((K ⊓ D) ⊔ (T ⊓ D)).relIndex D ∣ 2 ^ n :=
    ((Subgroup.inf_relIndex_right K D).trans hn) ▸ Subgroup.relIndex_dvd_of_le_left D le_sup_left
  have h2 : ((K ⊓ D) ⊔ (T ⊓ D)).relIndex D ∣ (T ⊓ D).relIndex D :=
    Subgroup.relIndex_dvd_of_le_left D le_sup_right
  have hcop : Nat.Coprime (2 ^ n) ((T ⊓ D).relIndex D) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem B2_13_conjClosure (hT : IsSylowTwoOf T H) {Z : Subgroup G}
    (hZT : Z ≤ quasithinOmegaOneCenter T) (hZO : Z ≤ pCoreOf 2 H) :
    IsTwoReducedIn H (conjClosure Z H) := by
  obtain ⟨hle, hel⟩ := conjClosure_le_of_isSylowTwoOf hT hZT hZO
  refine ⟨hle.trans (inf_le_left.trans (pCoreOf_le 2 H)), le_normalizer_conjClosure Z H, hel, ?_⟩
  intro D hDH hDN hD
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp
      ((hZT.trans (B2F.omegaOneCenter_le_inf_centralizer T)).trans inf_le_right)
  have hDle := le_sup_inf_of_two_power hT hDH (hT.1.trans hDN)
    (hDH.trans ((le_normalizer_conjClosure Z H).trans
      (B2F.normalizer_le_normalizer_centralizer _))) hD
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) :=
    hDle.trans (sup_le (inf_le_left.trans (Subgroup.centralizer_le (le_conjClosure Z H)))
      (inf_le_left.trans hTZ))
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hDN (H.inv_mem hh)) d).mp hd
  have hcomm : z * (h⁻¹ * d * h) = (h⁻¹ * d * h) * z := hDZ hd' z hz
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [hcomm]
    _ = h * z * h⁻¹ * d := by group

theorem omegaOneCenter_le_pCoreOf_of_charTwo (hT : IsSylowTwoOf T H) (hF : CharTwo H) :
    quasithinOmegaOneCenter T ≤ pCoreOf 2 H := by
  intro z hz
  have hz' := B2F.omegaOneCenter_le_inf_centralizer T hz
  exact hF ⟨hT.1 hz'.1, Subgroup.centralizer_le (pCoreOf_le_of_isSylowTwoOf hT) hz'.2⟩

theorem conjClosure_isTwoReducedIn_of_charTwo (hT : IsSylowTwoOf T H) (hF : CharTwo H)
    {Z : Subgroup G} (hZ : Z ≤ quasithinOmegaOneCenter T) :
    conjClosure Z H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (conjClosure Z H) ∧ IsTwoReducedIn H (conjClosure Z H) := by
  have hZO : Z ≤ pCoreOf 2 H := hZ.trans (omegaOneCenter_le_pCoreOf_of_charTwo hT hF)
  obtain ⟨hle, hel⟩ := conjClosure_le_of_isSylowTwoOf hT hZ hZO
  exact ⟨hle, hel, B2_13_conjClosure hT hZ hZO⟩

theorem B2_15 (hF : CharTwo H) (hT : IsSylowTwoOf T H) :
    ∃ hU : IsElemAbelian 2 (conjClosure (quasithinOmegaOneCenter T) H),
      (¬ thompsonJ T ≤ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) H : Set G) ∧
        IsFFModule (autI hU H) ∧
        IsTwoReducedIn H (conjClosure (quasithinOmegaOneCenter T) H)) ∨
      (thompsonJ T ≤ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) H : Set G) ∧
        ∀ h ∈ H, ∃ c ∈ H ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G),
          ∃ n ∈ H ⊓ Subgroup.normalizer (thompsonJ T : Set G), h = c * n) := by
  obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  refine ⟨hel, ?_⟩
  by_cases h : thompsonJ T ≤ Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) H : Set G)
  · refine Or.inr ⟨h, fun x hx => ?_⟩
    obtain ⟨-, hfac⟩ := B2_7_of_le_factor hred.2.1 hT h
    obtain ⟨n, hn, c, hc, hxinv⟩ := hfac x⁻¹ (H.inv_mem hx)
    refine ⟨c⁻¹, ⟨(H.inv_mem hc.1), ?_⟩, n⁻¹, ⟨H.inv_mem hn.1, ?_⟩, ?_⟩
    · exact Subgroup.centralizer_le (le_conjClosure _ _) ((Subgroup.centralizer _).inv_mem hc.2)
    · exact (Subgroup.normalizer _).inv_mem hn.2
    · rw [← mul_inv_rev, ← hxinv, inv_inv]
  · refine Or.inl ⟨h, ?_, hred⟩
    have hJH : ¬ thompsonJ H ≤ Subgroup.centralizer
        (conjClosure (quasithinOmegaOneCenter T) H : Set G) := fun h' =>
      h ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h')
    exact (B2_7_of_not_le hel hred.1 hred.2.1 hJH).1

end Thompson

end CFSG.Quasithin
