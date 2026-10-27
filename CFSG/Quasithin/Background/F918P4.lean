module

public import CFSG.Quasithin.Background.F918P3
public import CFSG.Quasithin.Background.A1cModuleHomog
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure312Transport
public import CFSG.Quasithin.Background.F918P1
public import CFSG.Quasithin.Background.F9Eighteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section CCompImage

variable {G : Type*} [Group G] [Finite G]

theorem map_mem_cComp_top_of_ne_bot {Q : Type*} [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) {L : Subgroup G} (hL : L ∈ cComp (⊤ : Subgroup G))
    (hne : L.map f ≠ ⊥) : L.map f ∈ cComp (⊤ : Subgroup Q) := by
  have : Finite Q := Finite.of_surjective f hf
  refine ⟨hne, ?_, A3.subnormal_top_map hf (subnormal_of_mem_cComp hL), ?_⟩
  · rw [← Subgroup.map_commutator, perfect_of_mem_cComp hL]
  · intro K' hK'lt hK'ne hK'perf hK'sub
    have hKsub : IsSubnormal (K'.comap f) ⊤ := A3.subnormal_top_comap f hK'sub
    set Y : Subgroup G := L ⊓ K'.comap f with hY
    have hYsub : IsSubnormal Y ⊤ :=
      A3.subnormal_trans (A3.subnormal_inf_right (subnormal_of_mem_cComp hL)
        (le_top : K'.comap f ≤ ⊤)) hKsub
    have hZsub : IsSubnormal (perfectCore Y) ⊤ := A3.subnormal_perfectCore hYsub
    have hZL : perfectCore Y ≤ L := (perfectCore_le Y).trans inf_le_left
    have hmapY : Y.map f = K' := by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        exact hy.2
      · intro k hk
        obtain ⟨l, hl, rfl⟩ := hK'lt.le hk
        exact ⟨l, ⟨hl, hk⟩, rfl⟩
    by_cases hZ : perfectCore Y = ⊥
    · apply hK'ne
      have := map_perfectCore f Y
      rw [hZ, Subgroup.map_bot, hmapY, perfectCore_eq_self_of_perfect hK'perf] at this
      exact this.symm
    · by_cases hZL' : perfectCore Y = L
      · have : L.map f ≤ K' := by
          rw [← hZL']
          rintro _ ⟨y, hy, rfl⟩
          exact ((perfectCore_le Y) hy).2
        exact (lt_irrefl _) (lt_of_lt_of_le hK'lt this)
      · exact not_subnormal_of_mem_cComp hL (lt_of_le_of_ne hZL hZL') hZ (perfectCore_perfect Y)
          hZsub

end CCompImage

section CentralQuot

variable {X : Type} [Group X] [Finite X]

theorem coprime_natCard_two_of_le_center (Z : Subgroup X) (hZ : Z ≤ Subgroup.center X)
    (hX : CFSG.Open.pCore 2 X = ⊥) : Nat.Coprime (Nat.card Z) 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcop
  have h2 : 2 ∣ Nat.card Z := by
    by_contra hnd
    exact hcop (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hxo : orderOf (x : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hzc : (x : X) ∈ Subgroup.center X := hZ x.2
  have hle : Subgroup.zpowers (x : X) ≤ Subgroup.center X := (Subgroup.zpowers_le).mpr hzc
  have hnormal : (Subgroup.zpowers (x : X)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : n ∈ Subgroup.center X := hle hn
    have := Subgroup.mem_center_iff.mp hn' g
    rw [show g * n * g⁻¹ = n by rw [this]; group]
    exact hn
  have hp : IsPGroup 2 (Subgroup.zpowers (x : X)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hxo]
    norm_num
  have hz : Subgroup.zpowers (x : X) ≤ CFSG.Open.pCore 2 X := CFSG.LieType.BorelTits.le_pCore 2 hnormal hp
  rw [hX] at hz
  have : (x : X) ∈ (⊥ : Subgroup X) := hz (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hxo
  omega

theorem pCore_quotient_eq_bot (Z : Subgroup X) [Z.Normal] (hZ : Z ≤ Subgroup.center X)
    (hX : CFSG.Open.pCore 2 X = ⊥) : CFSG.Open.pCore 2 (X ⧸ Z) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZr := coprime_natCard_two_of_le_center Z hZ hX
  obtain ⟨V₀, hV₀, hV₀V⟩ := exists_isPGroup_map_eq Z (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := X ⧸ Z))
  have hnorm := normalizer_eq_comap_normalizer_map Z hZ hZr hV₀
  rw [hV₀V] at hnorm
  have hN : V₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hg : g ∈ Subgroup.normalizer (V₀ : Set X) := by
      rw [hnorm, Subgroup.mem_comap]
      have := Subgroup.normalizer_eq_top_iff.mpr (CFSG.LieType.BorelTits.pCore_normal (G := X ⧸ Z) 2)
      rw [this]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have hle : V₀ ≤ CFSG.Open.pCore 2 X := CFSG.LieType.BorelTits.le_pCore 2 hN hV₀
  rw [hX, le_bot_iff] at hle
  rw [← hV₀V, hle, Subgroup.map_bot]

theorem pCore_eq_bot_of_surjective_of_ker_le_center {Y : Type} [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center X) (hX : CFSG.Open.pCore 2 X = ⊥) :
    CFSG.Open.pCore 2 Y = ⊥ := by
  have h1 := pCore_quotient_eq_bot f.ker hker hX
  have e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have h2 := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
  rw [← h2, h1, Subgroup.map_bot]

end CentralQuot

section O2Inv

theorem iso_tilde_smul_of_commute {G : Type*} [Group G] {V : Type*} [CommGroup V]
    [MulDistribMulAction G V] {X T : Subgroup G} {W : Subgroup V}
    (hTX : T ≤ Subgroup.normalizer (X : Set G)) (hW : ∀ t ∈ T, ∀ w ∈ W, t • w ∈ W) {g : G}
    (hg : g ∈ T) (hc : ∀ x ∈ X, g * x = x * g) (I : Subgroup V) :
    XMod.Iso ↥X (tilde X W (g • I)) (tilde X W I) := by
  let := quotAct hTX hW
  have e : tilde X W (g • I) = (⟨g, hg⟩ : ↥T) • tilde X W I := (tilde_smul hTX hW ⟨g, hg⟩ I).symm
  rw [e]
  refine ⟨(XMod.smulEquiv (⟨g, hg⟩ : ↥T) (tilde X W I)).symm, fun a y y' hy => ?_⟩
  have hcomm : ∀ q : V ⧸ modFix X W, (a : ↥X) • (⟨g, hg⟩ : ↥T)⁻¹ • q =
      (⟨g, hg⟩ : ↥T)⁻¹ • (a : ↥X) • q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H w =>
      have h1 : (a : G) * g⁻¹ = g⁻¹ * (a : G) := by
        have := hc (a : G) a.2
        calc (a : G) * g⁻¹ = g⁻¹ * (g * (a : G)) * g⁻¹ := by group
          _ = g⁻¹ * ((a : G) * g) * g⁻¹ := by rw [this]
          _ = g⁻¹ * (a : G) := by group
      show QuotientGroup.mk ((a : G) • (g⁻¹ • w)) = QuotientGroup.mk (g⁻¹ • ((a : G) • w))
      rw [smul_smul, smul_smul, h1]
  show (a : ↥X) • ((⟨g, hg⟩ : ↥T)⁻¹ • (y : V ⧸ modFix X W)) = (⟨g, hg⟩ : ↥T)⁻¹ • (y' : V ⧸ modFix X W)
  rw [hcomm, hy]

section O2InvMod

variable {W : Type} [CommGroup W] [Finite W]

theorem commute_of_mem_pCoreOf_sup {Mp T : Subgroup (MulAut W)}
    (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (hO2 : pCoreOf 2 Mp = ⊥)
    {g : MulAut W} (hg : g ∈ pCoreOf 2 (Mp ⊔ T)) : ∀ m ∈ Mp, g * m = m * g := by
  intro m hm
  have hnormR : Mp ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (Mp ⊔ T) : Set (MulAut W)) :=
    le_normalizer_pCoreOf 2 (Mp ⊔ T)
  have hnormMp : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hTn
  have hmM : m ∈ Mp ⊔ T := Subgroup.mem_sup_left hm
  have hgM : g ∈ Mp ⊔ T := pCoreOf_le 2 _ hg
  have hc1 : g * m * g⁻¹ * m⁻¹ ∈ pCoreOf 2 (Mp ⊔ T) := by
    have h1 : m * g⁻¹ * m⁻¹ ∈ pCoreOf 2 (Mp ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hnormR hmM) g⁻¹).mp (inv_mem hg)
    have : g * m * g⁻¹ * m⁻¹ = g * (m * g⁻¹ * m⁻¹) := by group
    rw [this]
    exact mul_mem hg h1
  have hc2 : g * m * g⁻¹ * m⁻¹ ∈ Mp := by
    have h1 : g * m * g⁻¹ ∈ Mp := (Subgroup.mem_normalizer_iff.mp (hnormMp hgM) m).mp hm
    exact mul_mem h1 (inv_mem hm)
  have hNle : pCoreOf 2 (Mp ⊔ T) ⊓ Mp ≤ pCoreOf 2 Mp := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hnormR (Subgroup.mem_sup_left hx)) y
    have h2 := Subgroup.mem_normalizer_iff.mp (hnormMp (Subgroup.mem_sup_left hx)) y
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  have hc : g * m * g⁻¹ * m⁻¹ ∈ pCoreOf 2 Mp := hNle ⟨hc1, hc2⟩
  rw [hO2, Subgroup.mem_bot] at hc
  calc g * m = g * m * g⁻¹ * m⁻¹ * m * g := by group
    _ = m * g := by rw [hc]; group

theorem o2inv_of_irrPlusOn {Mp T : Subgroup (MulAut W)} {V : Subgroup W}
    (hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W))) (hT : IsSylowTwoOf T (Mp ⊔ T))
    (hO2 : pCoreOf 2 Mp = ⊥) (hV : V ∈ IrrPlusOn Mp (orbSup T V) T) :
    ∀ g ∈ pCoreOf 2 (Mp ⊔ T), ∀ v ∈ V, g v ∈ V := by
  intro g hg v hv
  have hgT : g ∈ T := isSylowTwoOf_pCoreOf_le hT hg
  have hc := commute_of_mem_pCoreOf_sup hTn hO2 hg
  have hW : ∀ t ∈ T, ∀ w ∈ orbSup T V, t • w ∈ orbSup T V := fun t ht w hw =>
    mem_orbSup_of_mem_map ht hw
  have hiso := iso_tilde_smul_of_commute hTn hW hgT hc V
  have hstab := (forall_smul_eq_iff_mem_irrPlusOn hTn hW hV.1).mpr hV g ⟨hgT, hiso⟩
  have h2 : g • v ∈ g • V := Subgroup.smul_mem_pointwise_smul v g V hv
  rw [hstab] at h2
  exact h2

end O2InvMod

end O2Inv

section Bridge

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

namespace HypF918

omit [Finite G] in
theorem H_le_normalizer_V₁ (h : HypF918 T V L V₁ Vp H K) :
    H ≤ Subgroup.normalizer (V₁ : Set G) := h.H_normalizes_V₁

theorem conjClosure_le_normalizer_V₁ (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    conjClosure I H ≤ Subgroup.normalizer (V₁ : Set G) :=
  (conjClosure_le_conjClosure_U hIU le_rfl).trans
    (h.toHypF98.toHypF91.conjClosure_Vp_le_pCoreOf.trans
      ((pCoreOf_le 2 H).trans h.H_normalizes_V₁))

theorem actH_eq_one_of_mem_pCoreOf [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {x : ↥H}
    (hx : (x : G) ∈ pCoreOf 2 H) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x = 1 := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  refine MulEquiv.ext fun w => ?_
  rw [MulAut.one_apply]
  obtain ⟨a, haIH, hau⟩ := exists_mk_of_mem_tilde w
  have hw : w = modMk hIHN (a : G) haIH := Subtype.ext hau.symm
  rw [hw, actH_modMk h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) x haIH]
  apply Subtype.ext
  show secMk _ _ ⟨(x : G) * a * (x : G)⁻¹, _⟩ = secMk _ _ ⟨(a : G), _⟩
  symm
  rw [secMk_eq_secMk_iff]
  have := h.toHypF98.toHypF91.commutator_conjClosure_le (a : G)⁻¹ (inv_mem (hIHU haIH)) x hx
  have e : (a : G)⁻¹ * (x : G) * ((a : G)⁻¹)⁻¹ * (x : G)⁻¹ = (a : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) := by
    group
  rw [e] at this
  exact this

theorem commutator_mem_of_actH_fix [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {x : ↥H} {a : G}
    (haIH : a ∈ conjClosure I H)
    (hx : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x
      (modMk (h.conjClosure_le_normalizer_V₁ hIU) a haIH) =
      modMk (h.conjClosure_le_normalizer_V₁ hIU) a haIH) :
    (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ V₁ := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have key := actH_modMk h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) x haIH
  rw [hx] at key
  have h1 : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨a, hIHN haIH⟩ =
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨(x : G) * a * (x : G)⁻¹, hIHN
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I H x.2) a).mp haIH)⟩ :=
    congrArg Subtype.val key
  have h2 := secMk_eq_secMk_iff.mp h1
  have e : (x : G) * a * (x : G)⁻¹ * a⁻¹ = a * (a⁻¹ * ((x : G) * a * (x : G)⁻¹)) * a⁻¹ := by
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hIHN haIH) _).mp h2

theorem commutator_mem_of_actH_eq_one [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {x : ↥H}
    (hx : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x = 1) :
    ∀ a ∈ conjClosure I H, (x : G) * a * (x : G)⁻¹ * a⁻¹ ∈ V₁ := fun a haIH =>
  commutator_mem_of_actH_fix h hIU haIH (by rw [hx, MulAut.one_apply])

theorem central_of_actH_eq_one [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) {x : ↥H}
    (hxK : (x : G) ∈ conjClosure K T)
    (hx : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x = 1) :
    ∀ k' ∈ conjClosure K T, (x : G) * k' * (x : G)⁻¹ * k'⁻¹ ∈ pCoreOf 2 H := by
  have hnt' : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure I H, k * e * k⁻¹ * e⁻¹ ∈ V₁ :=
    fun hall => hnt fun k hk i hi => hall k hk i (le_conjClosure I H hi)
  have hE : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I H : Set G) :=
    h.K₀T_le_H.trans (le_normalizer_conjClosure I H)
  exact (h.central_kernel_and_faithful (B := ⊥) bot_le
    (fun b hb _ => by rw [Subgroup.mem_bot.mp hb]; exact (pCoreOf 2 H).one_mem)
    h.K₀T_le_normalizer_V₁ hE hnt').1 x hxK (commutator_mem_of_actH_eq_one h hIU hx)

theorem pCore_quotient_K₀_eq_bot (h : HypF918 T V L V₁ Vp H K)
    (Qk : Subgroup ↥(conjClosure K T)) [hQkN : Qk.Normal]
    (hQk : Qk = (pCoreOf 2 H).subgroupOf (conjClosure K T)) :
    CFSG.Open.pCore 2 (↥(conjClosure K T) ⧸ Qk) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀H : conjClosure K T ≤ H := h.K₀_le_H
  subst hQk
  set Qk : Subgroup ↥(conjClosure K T) := (pCoreOf 2 H).subgroupOf (conjClosure K T) with hQk
  set D := CFSG.Open.pCore 2 (↥(conjClosure K T) ⧸ Qk) with hD
  have hDn : D.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCore_isPGroup 2
  set Et : Subgroup ↥(conjClosure K T) := D.comap (QuotientGroup.mk' Qk) with hEt
  have hEtn : Et.Normal := hDn.comap _
  set E : Subgroup G := Et.map (conjClosure K T).subtype with hE
  have hEK : E ≤ conjClosure K T := Subgroup.map_subtype_le _
  have hEsub : E.subgroupOf (conjClosure K T) = Et := map_subtype_subgroupOf' Et
  have hKE : conjClosure K T ≤ Subgroup.normalizer (E : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hEK).mp ?_
    rw [hEsub]
    exact hEtn
  have hall : ∀ e ∈ E, ∃ k : ℕ, e ^ 2 ^ k ∈ pCoreOf 2 H := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := he
    have hxD : QuotientGroup.mk' Qk x ∈ D := hx
    obtain ⟨k, hk⟩ := hD2 ⟨_, hxD⟩
    refine ⟨k, ?_⟩
    have h1 : (QuotientGroup.mk' Qk x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h2 := Subgroup.mem_subgroupOf.mp (show x ^ 2 ^ k ∈ Qk from h1)
    simpa using h2
  have hEQ : E ≤ pCoreOf 2 H := h.F918_1.2.2.2 E hEK hKE hall
  have hEtQ : Et ≤ Qk := fun x hx => by
    rw [hQk, Subgroup.mem_subgroupOf]
    exact hEQ ⟨x, hx, rfl⟩
  rw [eq_bot_iff]
  intro d hd
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Qk d
  have hxEt : x ∈ Et := hd
  have := hEtQ hxEt
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact this

theorem pCoreOf_map_actH_eq_bot [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    pCoreOf 2 (((conjClosure K T).subgroupOf H).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H))) = ⊥ := by
  have hK₀H : conjClosure K T ≤ H := h.K₀_le_H
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  let ψ : ↥(conjClosure K T) →* MulAut ↥(tildeOf V₁ (conjClosure I H)) :=
    φ.comp (Subgroup.inclusion hK₀H)
  have hrange : ψ.range = ((conjClosure K T).subgroupOf H).map φ := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  set Qk : Subgroup ↥(conjClosure K T) := (pCoreOf 2 H).subgroupOf (conjClosure K T) with hQk
  have hQkN : Qk.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hQk, Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (hK₀H g.2)) n).mp hn
  have hQψ : Qk ≤ ψ.rangeRestrict.ker := fun n hn => by
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact actH_eq_one_of_mem_pCoreOf h hIU (x := Subgroup.inclusion hK₀H n)
      (Subgroup.mem_subgroupOf.mp hn)
  let f : (↥(conjClosure K T) ⧸ Qk) →* ↥ψ.range := QuotientGroup.lift Qk ψ.rangeRestrict hQψ
  have hf : Function.Surjective f := by
    have : f.comp (QuotientGroup.mk' Qk) = ψ.rangeRestrict := rfl
    intro y
    obtain ⟨x, hx⟩ := ψ.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' Qk x, hx⟩
  have hker : f.ker ≤ Subgroup.center (↥(conjClosure K T) ⧸ Qk) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Qk y
    rw [MonoidHom.mem_ker] at hy
    have hx1 : ψ x = 1 := congrArg Subtype.val hy
    have hxK : (x : G) ∈ conjClosure K T := x.2
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective Qk g
    show QuotientGroup.mk' Qk k' * QuotientGroup.mk' Qk x = QuotientGroup.mk' Qk x * QuotientGroup.mk' Qk k'
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [hQk, Subgroup.mem_subgroupOf]
    have hx1' : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        (Subgroup.inclusion hK₀H x⁻¹) = 1 := by
      have : Subgroup.inclusion hK₀H x⁻¹ = (Subgroup.inclusion hK₀H x)⁻¹ := by simp
      rw [this, map_inv]
      have h2 : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) (Subgroup.inclusion hK₀H x) = 1 := hx1
      rw [h2, inv_one]
    have := central_of_actH_eq_one h hIU hnt (x := Subgroup.inclusion hK₀H x⁻¹) (inv_mem hxK) hx1'
      ((k' : G)⁻¹) (inv_mem k'.2)
    simpa [mul_assoc] using this
  have hXq := pCore_quotient_K₀_eq_bot h Qk hQk
  have := pCore_eq_bot_of_surjective_of_ker_le_center f hf hker hXq
  rw [← hrange]
  unfold pCoreOf
  rw [this, Subgroup.map_bot]

theorem F918_3_weak (h : HypF918 T V L V₁ Vp H K) {I B X : Subgroup G}
    (hIU : I ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hnt_I : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hB : IsF918B T L V₁ Vp H (conjClosure K T) B) (hX : X = T ∨ X = H) :
    (∀ k ∈ conjClosure K T, (∀ i ∈ conjClosure I X, k * i * k⁻¹ * i⁻¹ ∈ V₁) →
        ∀ k' ∈ conjClosure K T, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 H) ∧
      (∀ b ∈ B, (∀ i ∈ conjClosure I X, b * i * b⁻¹ * i⁻¹ ∈ V₁) → b ∈ pCoreOf 2 H) ∧
      autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure I X)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure I X))
          (commGroupOfElemAbelian (h.isElemAbelian_tilde_conjClosure hIU hX))
          (autOn (tildeOf V₁ (conjClosure K T ⊔ T)) (tildeOf V₁ (conjClosure I X))) := by
  obtain ⟨hBL, hq, hfaith⟩ := hB
  have h1 := h.toHypF98.toHypF91
  obtain ⟨hTX, hXH, hXK₀⟩ := h.T_le_of_cases hX
  have hBT : B ≤ T := hBL.trans h.pCoreOf_L₁T_le_T
  have hIX_U : conjClosure I X ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU hXH
  have hIXN : conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure I X : Set G) :=
    sup_le (le_normalizer_conjClosure_of_le hKI hXK₀)
      (hTX.trans (le_normalizer_conjClosure I X))
  have hnt_IX : ¬ ∀ k ∈ conjClosure K T, ∀ e ∈ conjClosure I X, k * e * k⁻¹ * e⁻¹ ∈ V₁ :=
    fun hall => hnt_I fun k hk i hi => hall k hk i (le_conjClosure I X hi)
  obtain ⟨hcentral, hfaithIX⟩ :=
    h.central_kernel_and_faithful hBT hfaith h.K₀T_le_normalizer_V₁ hIXN hnt_IX
  have hhC : centralizerMod V₁ B (conjClosure I X) = B ⊓ pCoreOf 2 H :=
    h.centralizerMod_eq_inf_pCoreOf le_rfl (hBT.trans (h.T_le_H.trans h1.H_normalizes_V₁))
      hIX_U hfaithIX
  have hIX_N : conjClosure I X ≤ Subgroup.normalizer (V₁ : Set G) :=
    hIX_U.trans (h1.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans h1.H_normalizes_V₁))
  have hr1 : (centralizerMod V₁ (conjClosure I X) B).relIndex (conjClosure I X) ≤
      ((B ⊓ pCoreOf 2 H).relIndex B) ^ 2 :=
    (relIndex_centralizerMod_le V₁ (conjClosure Vp H) (conjClosure I X) B hIX_U).trans
      hq.2.2.2.2
  refine ⟨hcentral, hfaithIX, ?_⟩
  refine mem_Qset_autOn_secImg (K := V₁) (E := conjClosure I X) (X' := conjClosure K T ⊔ T)
    (B := B) (h.isElemAbelian_tilde_conjClosure hIU hX) hIX_N h.K₀T_le_normalizer_V₁ hIXN
    (hBT.trans le_sup_right) hq.2.1 ?_ ?_ ?_
  · intro hall
    exact hq.2.2.1 fun b hb => hfaithIX b hb fun e he => hall b hb e he
  · exact fun b₁ hb₁ b₂ hb₂ e he => hq.2.2.2.1 b₁ hb₁ b₂ hb₂ e (hIX_U he)
  · rw [hhC]; exact hr1

end HypF918

section Images

variable {Γ : Type} [Group Γ] [Finite Γ] (φ : ↥H →* Γ)

omit [Finite G] [Finite Γ] in
theorem map_subgroupOf_self_eq_range : (H.subgroupOf H).map φ = φ.range := by
  rw [Subgroup.subgroupOf_self, MonoidHom.range_eq_map]

omit [Finite Γ] in
theorem isQuotientOfSQTK_range (hH : SQTKGroup ↥H) : IsQuotientOfSQTKTC ↥φ.range :=
  ⟨↥H, inferInstance, inferInstance,
    fun p hp hp2 => hH.1 p hp hp2, hH.2,
    φ.rangeRestrict, φ.rangeRestrict_surjective⟩

omit [Finite Γ] in
theorem isSylowTwoOf_map_subgroupOf {T : Subgroup G} (hT : IsSylowTwoOf T H) :
    IsSylowTwoOf ((T.subgroupOf H).map φ) ((H.subgroupOf H).map φ) := by
  have h1 : IsSylowTwoOf (T.subgroupOf H) (⊤ : Subgroup ↥H) :=
    (A312.isSylowTwoOf_top_iff_map H (T.subgroupOf H)).mpr
      (by rwa [Subgroup.map_subgroupOf_eq_of_le hT.1])
  have h2 := A312.isSylowTwoOf_top_map φ.rangeRestrict φ.rangeRestrict_surjective h1
  have h3 := (A312.isSylowTwoOf_top_iff_map φ.range _).mp h2
  rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h3
  rwa [map_subgroupOf_self_eq_range]

theorem map_subgroupOf_mem_cComp {K : Subgroup G} (hK : K ∈ cComp H)
    (hne : (K.subgroupOf H).map φ ≠ ⊥) :
    (K.subgroupOf H).map φ ∈ cComp ((H.subgroupOf H).map φ) := by
  have h1 : K.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hK
  have hne' : (K.subgroupOf H).map φ.rangeRestrict ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← MonoidHom.subtype_comp_rangeRestrict φ, ← Subgroup.map_map, hbot, Subgroup.map_bot]
  have h2 := map_mem_cComp_top_of_ne_bot φ.rangeRestrict φ.rangeRestrict_surjective h1 hne'
  have h3 := map_subtype_mem_cComp h2
  rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict] at h3
  rwa [map_subgroupOf_self_eq_range]

omit [Finite G] [Finite Γ] in
theorem subgroupOf_conjClosure_of_le {K T : Subgroup G} (hK : K ≤ H) (hT : T ≤ H) :
    (conjClosure K T).subgroupOf H = conjClosure (K.subgroupOf H) (T.subgroupOf H) := by
  have hle : conjClosure K T ≤ H :=
    conjClosure_le fun t ht k hk => H.mul_mem (H.mul_mem (hT ht) (hK hk)) (H.inv_mem (hT ht))
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hle, A3.map_conjClosure,
    Subgroup.map_subgroupOf_eq_of_le hK, Subgroup.map_subgroupOf_eq_of_le hT]

omit [Finite G] [Finite Γ] in
theorem map_subgroupOf_conjClosure {K T : Subgroup G} (hK : K ≤ H) (hT : T ≤ H) :
    ((conjClosure K T).subgroupOf H).map φ =
      conjClosure ((K.subgroupOf H).map φ) ((T.subgroupOf H).map φ) := by
  rw [subgroupOf_conjClosure_of_le hK hT, A3.map_conjClosure]

omit [Finite G] [Finite Γ] in
theorem map_le_normalizer_map_of_le_normalizer {N : Subgroup G} (hNH : N ≤ H)
    (hN : H ≤ Subgroup.normalizer (N : Set G)) :
    (H.subgroupOf H).map φ ≤ Subgroup.normalizer (((N.subgroupOf H).map φ : Subgroup Γ) : Set Γ) := by
  have hnorm : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hN
  have h1 := Subgroup.le_normalizer_map φ (H := N.subgroupOf H)
  rw [Subgroup.normalizer_eq_top_iff.mpr hnorm, Subgroup.map_top] at h1
  rwa [map_subgroupOf_self_eq_range]

end Images

section Data

variable {Γ : Type} [Group Γ]

noncomputable abbrev autIH (V₁ I H X : Subgroup G) :
    Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H))) :=
  autOn (tildeOf V₁ X) (tildeOf V₁ (conjClosure I H))

omit [Finite G] in
theorem autIH_eq_map (h : HypF918 T V L V₁ Vp H K) {X : Subgroup G} (hXH : X ≤ H) :
    autIH V₁ I H X =
      (X.subgroupOf H).map (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) :=
  autOn_tilde_eq_map_actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) hXH

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem K₀_le_normalizer_of_isInv (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I)
    (hinv : XMod.IsInv ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) :
    conjClosure K T ≤ Subgroup.normalizer (I : Set G) := by
  intro k hk
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  have hkH : k ∈ H := h.K₀_le_H hk
  let φ := actH h.H_le_normalizer_V₁ hIH
  have hmem : ∀ x (hx : x ∈ conjClosure K T),
      φ ⟨x, h.K₀_le_H hx⟩ ∈ autIH V₁ I H (conjClosure K T) := by
    intro x hx
    rw [autIH_eq_map h h.K₀_le_H]
    exact ⟨⟨x, h.K₀_le_H hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hstab : φ ⟨k, hkH⟩ ∈ stabSub (subM V₁ (conjClosure I H) I) := by
    intro u
    constructor
    · intro hu
      have := hinv ⟨(φ ⟨k, hkH⟩)⁻¹, inv_mem (hmem k hk)⟩ _ hu
      simpa using this
    · intro hu
      exact hinv ⟨φ ⟨k, hkH⟩, hmem k hk⟩ u hu
  exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ hIHN hIH hV₁I (le_conjClosure I H)
    ⟨k, hkH⟩).mp hstab

theorem hnt_of_irrSec (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hsec : (XMod.fixed ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I)) <
      subM V₁ (conjClosure I H) I) :
    ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁ := by
  intro hall
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  obtain ⟨w, hwV, hwf⟩ := IsConcreteLE.not_le_iff_exists.mp (not_le_of_gt hsec)
  apply hwf
  refine ⟨hwV, fun a => ?_⟩
  obtain ⟨x, hx, hxa⟩ : ∃ x : ↥H, x ∈ (conjClosure K T).subgroupOf H ∧
      actH h.H_le_normalizer_V₁ hIH x = (a : MulAut _) := by
    have ha : (a : MulAut _) ∈ ((conjClosure K T).subgroupOf H).map
        (actH h.H_le_normalizer_V₁ hIH) := by
      rw [← autIH_eq_map h h.K₀_le_H]
      exact a.2
    exact ha
  obtain ⟨i, hi, hiw⟩ := mem_secImg.mp (show (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) ∈
    tildeOf V₁ I from hwV)
  have hiIH : (i : G) ∈ conjClosure I H := le_conjClosure I H hi
  have hw : w = modMk hIHN (i : G) hiIH := Subtype.ext hiw.symm
  have hxK : (x : G) ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hx
  show (a : MulAut _) w = w
  rw [← hxa, hw, actH_modMk h.H_le_normalizer_V₁ hIHN hIH x hiIH]
  apply Subtype.ext
  show secMk _ _ ⟨(x : G) * i * (x : G)⁻¹, _⟩ = secMk _ _ ⟨(i : G), _⟩
  symm
  rw [secMk_eq_secMk_iff]
  have hc := hall x hxK i hi
  have e : (i : G)⁻¹ * ((x : G) * i * (x : G)⁻¹) = (i : G)⁻¹ * ((x : G) * i * (x : G)⁻¹ * (i : G)⁻¹) * i := by
    group
  rw [e]
  have := (Subgroup.mem_normalizer_iff''.mp (hIHN hiIH) _).mp hc
  simpa [mul_assoc] using this

theorem map_K_ne_bot (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    (K.subgroupOf H).map (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) ≠ ⊥ := by
  intro hbot
  apply hnt
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hK : K.subgroupOf H ≤ φ.ker := Subgroup.map_eq_bot_iff _ |>.mp hbot
  have hK₀ : conjClosure K T ≤ φ.ker.map H.subtype := by
    refine conjClosure_le fun t ht z hz => ?_
    have htH : t ∈ H := h.T_le_H ht
    have hzK : (⟨z, hKH hz⟩ : ↥H) ∈ K.subgroupOf H := hz
    have hz1 : φ ⟨z, hKH hz⟩ = 1 := hK hzK
    refine ⟨⟨t * z * t⁻¹, H.mul_mem (H.mul_mem htH (hKH hz)) (H.inv_mem htH)⟩, ?_, rfl⟩
    show φ (⟨t, htH⟩ * ⟨z, hKH hz⟩ * ⟨t, htH⟩⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hz1]
    simp
  intro k hk i hi
  obtain ⟨y, hy, hyk⟩ := hK₀ hk
  have hy1 : φ y = 1 := hy
  have := h.commutator_mem_of_actH_eq_one hIU hy1 i (le_conjClosure I H hi)
  have hyk' : (y : G) = k := hyk
  rw [hyk'] at this
  exact this

theorem qOff_of_hyp (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) (hV₁I : V₁ ≤ I)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁) :
    ∃ B : Subgroup G, QOff (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H B)
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) := by
  obtain ⟨B, hB, -⟩ := h.F918_2
  have hBT : B ≤ T := hB.1.trans h.pCoreOf_L₁T_le_T
  have hBH : B ≤ H := hBT.trans h.T_le_H
  obtain ⟨-, -, hmemH⟩ := h.F918_3_weak (X := H) hIU hKI hnt hB (Or.inr rfl)
  obtain ⟨-, hfaithT, -⟩ := h.F918_3_weak (X := T) hIU hKI hnt hB (Or.inl rfl)
  obtain ⟨⟨hA2, hr⟩, hcs⟩ := hmemH
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  have hK₀H : conjClosure K T ≤ H := h.K₀_le_H
  have hQ : ∀ x : ↥H, (x : G) ∈ pCoreOf 2 H → φ x = 1 := fun x hx =>
    h.actH_eq_one_of_mem_pCoreOf hIU hx
  refine ⟨B, ⟨?_, hA2.2.1, hA2.2.2, hcs, hr, ?_, ?_⟩⟩
  · exact autOn_le_autOn (tildeOf V₁ (conjClosure I H)) (secImg_mono hBT)
  ·
    intro a ha hcomm
    have ha' : a ∈ (B.subgroupOf H).map φ := by
      rw [← autIH_eq_map h hBH]
      exact ha
    obtain ⟨b', hb', rfl⟩ := ha'
    have hbB : (b' : G) ∈ B := Subgroup.mem_subgroupOf.mp hb'
    have hcomm' : ∀ n : ℤ, ∀ k (hk : k ∈ conjClosure K T),
        φ (b' ^ n) * φ ⟨k, hK₀H hk⟩ = φ ⟨k, hK₀H hk⟩ * φ (b' ^ n) := by
      intro n k hk
      have hmem : φ ⟨k, hK₀H hk⟩ ∈ autIH V₁ I H (conjClosure K T) := by
        rw [autIH_eq_map h hK₀H]
        exact ⟨⟨k, hK₀H hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
      have := hcomm _ hmem
      rw [map_zpow]
      exact ((Commute.zpow_left (show Commute (φ b') (φ ⟨k, hK₀H hk⟩) from this) n))
    have hbQ : (b' : G) ∈ pCoreOf 2 H := by
      set b : G := (b' : G) with hb
      let A₁ : Subgroup G := Subgroup.zpowers b
      have hA₁B : A₁ ≤ B := (Subgroup.zpowers_le).mpr hbB
      have hA₁T : A₁ ≤ T := hA₁B.trans hBT
      have hA₁H : A₁ ≤ H := hA₁T.trans h.T_le_H
      have hkerK : ⁅conjClosure K T, A₁⁆ ≤ conjClosure K T ⊓ φ.ker.map H.subtype := by
        rw [Subgroup.commutator_le]
        intro k hk c hc
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        have hcT : b ^ n ∈ T := hA₁T hc
        refine ⟨?_, ?_⟩
        · have h1 : b ^ n * k⁻¹ * (b ^ n)⁻¹ ∈ conjClosure K T :=
            (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K T hcT) k⁻¹).mp
              (inv_mem hk)
          have e : k * b ^ n * k⁻¹ * (b ^ n)⁻¹ = k * (b ^ n * k⁻¹ * (b ^ n)⁻¹) := by group
          show k * b ^ n * k⁻¹ * (b ^ n)⁻¹ ∈ _
          rw [e]
          exact mul_mem hk h1
        · have hkH : k ∈ H := hK₀H hk
          refine ⟨⟨k, hkH⟩ * b' ^ n * ⟨k, hkH⟩⁻¹ * (b' ^ n)⁻¹, ?_, rfl⟩
          show φ (⟨k, hkH⟩ * b' ^ n * ⟨k, hkH⟩⁻¹ * (b' ^ n)⁻¹) = 1
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          have e := (hcomm' n k hk).symm
          rw [e]
          group
      have hcc : ⁅⁅conjClosure K T, A₁⁆, conjClosure K T⁆ ≤ pCoreOf 2 H := by
        rw [Subgroup.commutator_le]
        intro g₁ hg₁ k' hk'
        obtain ⟨hg1K, y, hy, hyg⟩ := hkerK hg₁
        have hy1 : φ y = 1 := hy
        have hyg' : (y : G) = g₁ := hyg
        have := h.central_of_actH_eq_one hIU hnt (x := y) (by rw [hyg']; exact hg1K) hy1 k' hk'
        rw [hyg'] at this
        exact this
      have hcomm3 : ⁅A₁, conjClosure K T⁆ ≤ pCoreOf 2 H :=
        commutator_le_of_commutator_commutator_le
          (hA₁H.trans (le_normalizer_pCoreOf 2 H)) (hK₀H.trans (le_normalizer_pCoreOf 2 H))
          h.K₀_perfect hcc
      exact hB.2.2 b hbB fun k hk =>
        hcomm3 (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hk)
    exact hQ b' hbQ
  ·
    have hIHN := h.conjClosure_le_normalizer_V₁ hIU
    rw [eq_bot_iff]
    rintro a ⟨ha, hcent⟩
    have ha' : a ∈ (B.subgroupOf H).map φ := by
      rw [← autIH_eq_map h hBH]
      exact ha
    obtain ⟨b', hb', rfl⟩ := ha'
    have hbB : (b' : G) ∈ B := Subgroup.mem_subgroupOf.mp hb'
    have hfix : ∀ i ∈ conjClosure I T, (b' : G) * i * (b' : G)⁻¹ * i⁻¹ ∈ V₁ := by
      intro i hi
      have hiIH : i ∈ conjClosure I H := conjClosure_mono le_rfl h.T_le_H hi
      have hsub : modMk hIHN i hiIH ∈ subM V₁ (conjClosure I H) (conjClosure I T) :=
        (modMk_mem_subM_iff hIHN (hV₁I.trans (le_conjClosure I T)) hiIH).mpr hi
      have hle := subM_conjClosure_le_orbSup h.H_le_normalizer_V₁ hIHN
        (le_normalizer_conjClosure I H) h.T_le_H hV₁I
      rw [← autIH_eq_map h h.T_le_H] at hle
      exact h.commutator_mem_of_actH_fix hIU hiIH (hcent _ (hle hsub))
    exact hQ b' (hfaithT (b' : G) hbB hfix)

theorem d31_of_hyp (h : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hIU : I ≤ conjClosure Vp H)
    (hV₁I : V₁ ≤ I)
    (hirr : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T)) :
    D31 (autIH V₁ I H H) (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H T) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I) := by
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G) :=
    K₀_le_normalizer_of_isInv h hIU hV₁I hirr.1.2.1
  have hnt := hnt_of_irrSec h hIU hirr.1.2.2.2.1
  have hO2 := h.pCoreOf_map_actH_eq_bot hIU hnt
  set φ := actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  rw [autIH_eq_map h h.T_le_H, autIH_eq_map h h.K₀_le_H] at hirr
  rw [autIH_eq_map h (le_refl H), autIH_eq_map h h.T_le_H, autIH_eq_map h h.K₀_le_H,
    autIH_eq_map h hKH]
  have hTM : (T.subgroupOf H).map φ ≤ (H.subgroupOf H).map φ :=
    Subgroup.map_mono (by rw [Subgroup.subgroupOf_self]; exact le_top)
  have hMpM : ((conjClosure K T).subgroupOf H).map φ ≤ (H.subgroupOf H).map φ :=
    Subgroup.map_mono (by rw [Subgroup.subgroupOf_self]; exact le_top)
  have hnormMp := map_le_normalizer_map_of_le_normalizer φ h.K₀_le_H h.K₀_normal
  have hsyl := isSylowTwoOf_map_subgroupOf φ h.sylow_H
  have hquasi : CFSG.IsQuasisimple ↥((K.subgroupOf H).map φ) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hO2K : pCoreOf 2 K ≤ pCoreOf 2 H :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp h.K_cComp)
    let ψ : ↥K →* ↥((K.subgroupOf H).map φ) :=
      (φ.comp (Subgroup.inclusion hKH)).codRestrict _
        (fun k => ⟨⟨(k : G), hKH k.2⟩, Subgroup.mem_subgroupOf.mpr k.2, rfl⟩)
    have hker : (pCoreOf 2 K).subgroupOf K ≤ ψ.ker := by
      intro k hk
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact h.actH_eq_one_of_mem_pCoreOf hIU (x := ⟨k, hKH k.2⟩)
        (hO2K (Subgroup.mem_subgroupOf.mp hk))
    let ψq : ↥K ⧸ (pCoreOf 2 K).subgroupOf K →* ↥((K.subgroupOf H).map φ) :=
      QuotientGroup.lift _ ψ hker
    have hsurj : Function.Surjective ψq := by
      intro y
      obtain ⟨x, hx, hxy⟩ := y.2
      exact ⟨QuotientGroup.mk ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxy⟩
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (map_K_ne_bot h hIU hnt)
    obtain ⟨q, rfl⟩ := hsurj y
    exact CFSG.LieType.CurtisTits.isQuasisimple_of_surjective h.K_quasisimple hsurj ⟨q, hy⟩
  refine ⟨?_, ?_, hsyl, map_subgroupOf_mem_cComp φ h.K_cComp (map_K_ne_bot h hIU hnt), hquasi,
    map_subgroupOf_conjClosure φ hKH h.T_le_H, hnormMp, ⟨le_top, hirr.1.2⟩, ?_,
    iSup_actH_subM_eq_top h.H_le_normalizer_V₁ hIHN (le_normalizer_conjClosure I H) hV₁I⟩
  · intro w
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).2
      (w : SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) w.2
    simpa using this
  · rw [map_subgroupOf_self_eq_range]
    exact isQuotientOfSQTK_range φ hH
  · exact o2inv_of_irrPlusOn (hTM.trans hnormMp)
      (isSylowTwoOf_mono_right hsyl le_sup_right (sup_le hMpM hTM)) hO2 hirr

end Data

end Bridge


end CFSG.Quasithin
