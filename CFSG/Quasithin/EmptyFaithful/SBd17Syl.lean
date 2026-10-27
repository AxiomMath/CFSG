module

public import CFSG.Quasithin.EmptyFaithful.SBd14Mid
public import CFSG.Quasithin.EmptyFaithful.SBd16Gen

public section

namespace CFSG.Quasithin.SBd14

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem false_of_centralizer_component_quotient
    (hAbs : ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H) [N.Normal],
      N ≤ Subgroup.center H → Nat.card ↥N = 2 →
      Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H →
      ∀ {t : H ⧸ N}, t ≠ 1 → t * t = 1 → ∀ {K : Subgroup (H ⧸ N)},
        K ≤ Subgroup.centralizer ({t} : Set (H ⧸ N)) →
        CFSG.ComponentClassification.TwoComponents.IsTwoComponent
          (K.subgroupOf (Subgroup.centralizer ({t} : Set (H ⧸ N)))) → False)
    (hComp : ∀ (Γ : Type) [Group Γ] [Finite Γ] (K : Subgroup Γ) [K.Normal],
      CFSG.IsQuasisimple ↥K → IsPGroup 2 ↥(Subgroup.center ↥K) → 2 ∣ Nat.card ↥K →
      CFSG.ComponentClassification.TwoComponents.IsTwoComponent K)
    {X : Type} [Group X] [Finite X]
    (hX : Subgroup.centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    (N : Subgroup X) [N.Normal] (hNc : N ≤ Subgroup.center X) (hN2 : Nat.card ↥N = 2)
    (Lx : Subgroup X) (hLq : CFSG.IsQuasisimple ↥Lx)
    (hZ : ∀ y ∈ Lx, (∀ x ∈ Lx, y * x = x * y) → y * y = 1)
    {u : X} (huL : u ∈ Lx) (huN : u ∉ N) (hu2 : u * u = 1) (hLu : ∀ l ∈ Lx, l * u = u * l)
    (hnorm : ∀ g : X, (QuotientGroup.mk g : X ⧸ N) * QuotientGroup.mk u =
      QuotientGroup.mk u * QuotientGroup.mk g → g ∈ Subgroup.normalizer (Lx : Set X)) :
    False := by
  classical
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup (X ⧸ N) :=
    Subgroup.centralizer ({(QuotientGroup.mk u : X ⧸ N)} : Set (X ⧸ N)) with hC
  set K : Subgroup (X ⧸ N) := Lx.map (QuotientGroup.mk' N) with hK
  have hut : (QuotientGroup.mk u : X ⧸ N) ≠ 1 := fun h => huN ((QuotientGroup.eq_one_iff u).mp h)
  have hut2 : (QuotientGroup.mk u : X ⧸ N) * QuotientGroup.mk u = 1 := by
    rw [← QuotientGroup.mk_mul, hu2, QuotientGroup.mk_one]
  have hKmem : ∀ l ∈ Lx, (QuotientGroup.mk l : X ⧸ N) ∈ K := fun l hl => ⟨l, hl, rfl⟩
  have hLC : ∀ l ∈ Lx, (QuotientGroup.mk l : X ⧸ N) ∈ C := by
    intro l hl
    rw [hC, Subgroup.mem_centralizer_singleton_iff, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      hLu l hl]
  have hKC : K ≤ C := by
    rintro _ ⟨l, hl, rfl⟩
    exact hLC l hl
  have hKnorm : (K.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨l, hl, hln⟩ := (hn : (n : X ⧸ N) ∈ K)
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk_surjective (g : X ⧸ N)
    have hgC : (QuotientGroup.mk g₀ : X ⧸ N) ∈ C := hg₀ ▸ g.2
    have hg₀N : g₀ ∈ Subgroup.normalizer (Lx : Set X) :=
      hnorm g₀ (Subgroup.mem_centralizer_singleton_iff.mp hgC)
    have hl' : g₀ * l * g₀⁻¹ ∈ Lx := (Subgroup.mem_normalizer_iff.mp hg₀N l).mp hl
    have hln' : (n : X ⧸ N) = QuotientGroup.mk l := hln.symm
    show ((g : X ⧸ N) * (n : X ⧸ N) * (g : X ⧸ N)⁻¹) ∈ K
    rw [← hg₀, hln']
    exact ⟨g₀ * l * g₀⁻¹, hl', rfl⟩
  let Φ : ↥Lx →* ↥(K.subgroupOf C) :=
    { toFun := fun l => ⟨⟨QuotientGroup.mk (l : X), hLC l l.2⟩, hKmem l l.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  have hΦs : Function.Surjective Φ := by
    rintro ⟨⟨c, hcC⟩, hcK⟩
    obtain ⟨l, hl, hlc⟩ := hcK
    exact ⟨⟨l, hl⟩, Subtype.ext (Subtype.ext hlc)⟩
  have hΦk : Φ.ker ≤ Subgroup.center ↥Lx := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : (QuotientGroup.mk (y : X) : X ⧸ N) = 1 :=
      congrArg (fun w : ↥(K.subgroupOf C) => ((w : ↥C) : X ⧸ N)) hy
    have hyN : (y : X) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    refine Subgroup.mem_center_iff.mpr fun z => Subtype.ext ?_
    exact Subgroup.mem_center_iff.mp (hNc hyN) (z : X)
  have hq : CFSG.IsQuasisimple ↥(K.subgroupOf C) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hLq Φ hΦs hΦk
  have hcen := CFSG.LocalCores.comap_center_eq_of_perfect hLq.1 Φ hΦs hΦk
  have hZ2 : IsPGroup 2 ↥(Subgroup.center ↥(K.subgroupOf C)) := by
    intro w
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := hΦs (w : ↥(K.subgroupOf C))
    have hyc : y ∈ Subgroup.center ↥Lx := by
      rw [← hcen, Subgroup.mem_comap, hy]
      exact w.2
    have hy2 : (y : X) * (y : X) = 1 :=
      hZ y y.2 fun x hx => (congrArg Subtype.val (Subgroup.mem_center_iff.mp hyc ⟨x, hx⟩)).symm
    have h1 : (w : ↥(K.subgroupOf C)) * (w : ↥(K.subgroupOf C)) = 1 := by
      rw [← hy, ← map_mul]
      have : y * y = 1 := Subtype.ext hy2
      rw [this, map_one]
    apply Subtype.ext
    simpa [pow_two] using h1
  have hdvd : 2 ∣ Nat.card ↥(K.subgroupOf C) := by
    have hΦu2 : (Φ ⟨u, huL⟩) ^ 2 = 1 := by
      rw [pow_two, ← map_mul]
      have : (⟨u, huL⟩ : ↥Lx) * ⟨u, huL⟩ = 1 := Subtype.ext hu2
      rw [this, map_one]
    have hΦu1 : Φ ⟨u, huL⟩ ≠ 1 := by
      intro h
      exact hut (congrArg (fun w : ↥(K.subgroupOf C) => ((w : ↥C) : X ⧸ N)) h)
    have := orderOf_eq_prime hΦu2 hΦu1
    rw [← this]
    exact orderOf_dvd_natCard _
  have hTC : CFSG.ComponentClassification.TwoComponents.IsTwoComponent (K.subgroupOf C) :=
    hComp ↥C (K.subgroupOf C) hq hZ2 hdvd
  exact hAbs X N hNc hN2 hX hut hut2 hKC hTC

theorem exists_sylow_le_of_not_isSylowTwoOf {T S Hv : Subgroup G}
    (hT : IsPGroup 2 ↥T ∧ ¬ 2 ∣ T.index) (hSH : S ≤ Hv) (hS2 : IsPGroup 2 ↥S)
    (hcard : Nat.card ↥T = 2 * Nat.card ↥S) (hnot : ¬ IsSylowTwoOf S Hv) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ Hv := by
  classical
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTtop : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT.1, ?_⟩
    show ¬ 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact hT.2
  have hTc : Nat.card ↥T = twoPart (⊤ : Subgroup G) := (isSylowTwoOf_iff.mp hTtop).2.2
  by_contra hne
  apply hnot
  rw [isSylowTwoOf_iff]
  refine ⟨hSH, hS2, ?_⟩
  by_contra hcne
  have hdvd : Nat.card ↥S ∣ twoPart Hv := card_dvd_twoPart hSH hS2
  have hlt : Nat.card ↥S < twoPart Hv :=
    lt_of_le_of_ne (Nat.le_of_dvd (twoPart_pos Hv) hdvd) hcne
  obtain ⟨b, hb⟩ := hS2.exists_card_eq
  have hHv : twoPart Hv = 2 ^ (Nat.card ↥Hv).factorization 2 := rfl
  have hba : b < (Nat.card ↥Hv).factorization 2 := by
    rw [hb, hHv] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  have h2S : 2 * Nat.card ↥S ≤ twoPart Hv := by
    rw [hb, hHv, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) hba
  have hup : twoPart Hv ≤ twoPart (⊤ : Subgroup G) := twoPart_mono le_top
  have heq : twoPart Hv = twoPart (⊤ : Subgroup G) := by omega
  obtain ⟨P, hP⟩ := exists_isSylowTwoOf Hv
  have hPtop : IsSylowTwoOf P ⊤ := by
    refine isSylowTwoOf_iff.mpr ⟨le_top, hP.2.1, ?_⟩
    rw [← heq]
    exact (isSylowTwoOf_iff.mp hP).2.2
  have hPidx : ¬ 2 ∣ P.index := by
    have h := hPtop.2.2
    change ¬ 2 ∣ P.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  exact hne ⟨hP.2.1.toSylow hPidx, by rw [IsPGroup.toSylow_coe]; exact hP.1⟩

omit [Finite G] in
theorem orderOf_eq_two_of_involution {v : G} (hv1 : v ≠ 1) (hv2 : v * v = 1) : orderOf v = 2 := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact hv2) hv1

omit [Finite G] in
theorem eq_one_or_self_of_mem_zpowers_involution {v : G} (hv1 : v ≠ 1) (hv2 : v * v = 1) {x : G}
    (hx : x ∈ Subgroup.zpowers v) : x = 1 ∨ x = v := by
  have ho := orderOf_eq_two_of_involution hv1 hv2
  obtain ⟨n, rfl⟩ := hx
  have h : v ^ (n % 2) = v ^ n := by
    have := zpow_mod_orderOf v n
    rw [ho] at this
    exact_mod_cast this
  show v ^ n = 1 ∨ v ^ n = v
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [← h, h0, zpow_zero]
  · right
    rw [← h, h1, zpow_one]

omit [Finite G] in
theorem centralizer_involution_eq_normalizer_zpowers {v : G} (hv1 : v ≠ 1) (hv2 : v * v = 1) :
    Subgroup.centralizer ({v} : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have hc : ∀ n : ℤ, g * v ^ n * g⁻¹ = v ^ n := fun n => by
      have := (Commute.zpow_right (show Commute g v from h) n).eq
      calc g * v ^ n * g⁻¹ = v ^ n * g * g⁻¹ := by rw [this]
        _ = v ^ n := by group
    constructor
    · rintro ⟨n, rfl⟩
      rw [hc n]
      exact ⟨n, rfl⟩
    · rintro ⟨n, hn⟩
      have hx : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      have hc' : g⁻¹ * v ^ n * g = v ^ n := by
        have := (Commute.zpow_right (show Commute g⁻¹ v from (show Commute g v from h).inv_left) n).eq
        calc g⁻¹ * v ^ n * g = v ^ n * g⁻¹ * g := by rw [this]
          _ = v ^ n := by group
      rw [hx, ← hn, hc']
      exact ⟨n, rfl⟩
  · intro h
    have h1 : g * v * g⁻¹ ∈ Subgroup.zpowers v := (h v).mp (Subgroup.mem_zpowers v)
    have h2 : g * v * g⁻¹ ≠ 1 := by
      intro h3
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h3]; group
    rcases eq_one_or_self_of_mem_zpowers_involution hv1 hv2 h1 with h3 | h3
    · exact absurd h3 h2
    · calc g * v = (g * v * g⁻¹) * g := by group
        _ = v * g := by rw [h3]

omit [Finite G] in
theorem isTwoLocal_centralizer_involution {v : G} (hv1 : v ≠ 1) (hv2 : v * v = 1) :
    IsTwoLocal (Subgroup.centralizer ({v} : Set G)) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ho := orderOf_eq_two_of_involution hv1 hv2
  refine ⟨Subgroup.zpowers v, ?_, ?_, centralizer_involution_eq_normalizer_zpowers hv1 hv2⟩
  · intro hbot
    apply hv1
    have : v ∈ Subgroup.zpowers v := Subgroup.mem_zpowers v
    rw [hbot] at this
    exact this
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho]; norm_num)

omit [Finite G] in
theorem centralizer_pCore_le_of_inf_le {Hv : Subgroup G}
    (h : Hv ⊓ Subgroup.centralizer (pCoreOf 2 Hv : Set G) ≤ pCoreOf 2 Hv) :
    Subgroup.centralizer (CFSG.pCore 2 ↥Hv : Set ↥Hv) ≤ CFSG.pCore 2 ↥Hv := by
  intro x hx
  rw [S153D.mem_pCore_iff]
  refine h (Subgroup.mem_inf.mpr ⟨x.2, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨y', hy'⟩ : ∃ y' : ↥Hv, (y' : G) = y :=
    ⟨⟨y, CFSG.LieType.BorelTits.pCoreOf_le 2 Hv hy⟩, rfl⟩
  subst hy'
  have hy'' : y' ∈ CFSG.pCore 2 ↥Hv := (S153D.mem_pCore_iff y').mpr hy
  have := Subgroup.mem_centralizer_iff.mp hx y' hy''
  exact congrArg Subtype.val this

omit [Finite G] in
theorem conj_mem_of_commutator_mem_zpowers {V : Subgroup G} {v u g : G} (hV4 : Nat.card ↥V = 4)
    (hsq : ∀ a ∈ V, a * a = 1) (hv : v ∈ V) (hu : u ∈ V) (hv1 : v ≠ 1)
    (huv : u ∉ Subgroup.zpowers v) (hgv : g * v = v * g)
    (hg : u⁻¹ * g⁻¹ * u * g ∈ Subgroup.zpowers v) : ∀ x ∈ V, g⁻¹ * x * g ∈ V := by
  have hu1 : u ≠ 1 := fun h => huv (h ▸ Subgroup.one_mem _)
  have hvu : v ≠ u := fun h => huv (h ▸ Subgroup.mem_zpowers v)
  have hguV : g⁻¹ * u * g ∈ V := by
    have hw : u⁻¹ * g⁻¹ * u * g ∈ V := (Subgroup.zpowers_le.mpr hv) hg
    have : g⁻¹ * u * g = u * (u⁻¹ * g⁻¹ * u * g) := by group
    rw [this]
    exact V.mul_mem hu hw
  have hgvg : g⁻¹ * v * g = v := by
    calc g⁻¹ * v * g = g⁻¹ * (v * g) := by group
      _ = g⁻¹ * (g * v) := by rw [hgv]
      _ = v := by group
  intro x hx
  rcases SBd16.mem_klein_four hV4 hsq hv hu hv1 hu1 hvu x hx with h | h | h | h
  · rw [h]
    simp
  · rw [h, hgvg]
    exact hv
  · rw [h]
    exact hguV
  · rw [h]
    have : g⁻¹ * (v * u) * g = (g⁻¹ * v * g) * (g⁻¹ * u * g) := by group
    rw [this, hgvg]
    exact V.mul_mem hv hguV

theorem RestHyp.isSylowTwoOf_centralizer_v (r : RestHyp T Mc M V₁ V₂ Yp I L t)
    (h113 : StageLemma14113) (hI : I = Subgroup.normalizer (V₁ : Set G)) {v : G} (hv : v ∈ V₁)
    (hv1 : v ≠ 1) (hS : ∀ s ∈ Sgp153 T V₁, s * v = v * s)
    (hCI : I ⊓ Subgroup.centralizer ({v} : Set G) = L ⊔ Sgp153 T V₁)
    (hAbs : ∀ (H : Type) [Group H] [Finite H] (N : Subgroup H) [N.Normal],
      N ≤ Subgroup.center H → Nat.card ↥N = 2 →
      Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H →
      ∀ {t : H ⧸ N}, t ≠ 1 → t * t = 1 → ∀ {K : Subgroup (H ⧸ N)},
        K ≤ Subgroup.centralizer ({t} : Set (H ⧸ N)) →
        CFSG.ComponentClassification.TwoComponents.IsTwoComponent
          (K.subgroupOf (Subgroup.centralizer ({t} : Set (H ⧸ N)))) → False)
    (hComp : ∀ (Γ : Type) [Group Γ] [Finite Γ] (K : Subgroup Γ) [K.Normal],
      CFSG.IsQuasisimple ↥K → IsPGroup 2 ↥(Subgroup.center ↥K) → 2 ∣ Nat.card ↥K →
      CFSG.ComponentClassification.TwoComponents.IsTwoComponent K) :
    IsSylowTwoOf (Sgp153 T V₁) (Subgroup.centralizer ({v} : Set G)) := by
  classical
  by_contra hnot
  have hyp : Hyp153 G T Mc M := r.ctx.hyp.hyp
  have D0 := r.ctx.hyp.decomp
  have hq := hyp.qtfe
  set S : Subgroup G := Sgp153 T V₁ with hSdef
  set Hv : Subgroup G := Subgroup.centralizer ({v} : Set G) with hHv
  have hvV : v ∈ VZ T M := D0.le₁ hv
  have hv2 : v * v = 1 := r.V_sq v hvV
  have hSHv : S ≤ Hv := fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hS s hs)
  have hS2 : IsPGroup 2 ↥S := hq.sylow.1.to_le inf_le_left
  have hcard : Nat.card ↥T = 2 * Nat.card ↥S := by
    have hidx : (S.subgroupOf T).index = 2 := D0.relIndex_nS hyp
    have hmul := Subgroup.index_mul_card (S.subgroupOf T)
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : S ≤ T)).toEquiv] at hmul
    exact hmul.symm
  obtain ⟨P, hP⟩ := exists_sylow_le_of_not_isSylowTwoOf hq.sylow hSHv hS2 hcard hnot
  have hchar := hq.qtke.2.1 Hv (isTwoLocal_centralizer_involution hv1 hv2) ⟨P, hP⟩
  have hX := centralizer_pCore_le_of_inf_le hchar
  have hzp : Nat.card ↥(Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_two_of_involution hv1 hv2]
  obtain ⟨u, huV, huv⟩ : ∃ u ∈ V₁, u ∉ Subgroup.zpowers v := by
    by_contra hcon
    push Not at hcon
    have hle : V₁ ≤ Subgroup.zpowers v := hcon
    have := Subgroup.card_le_of_le hle
    rw [D0.card₁, hzp] at this
    omega
  have hVc : V₁ = centerOf L := r.V₁_eq_center h113
  have hVL : V₁ ≤ L := fun a ha => ((hVc ▸ ha : a ∈ centerOf L)).1
  have hsqV : ∀ a ∈ V₁, a * a = 1 := fun a ha => r.V_sq a (D0.le₁ ha)
  have hcommV : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := by
    intro a ha b hb
    have := hyp.elemAbelian.1
    exact setLike_mul_comm (D0.le₁ ha) (D0.le₁ hb)
  have hLH : L ≤ Hv := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (r.h1 hv) l hl)
  have hzH : Subgroup.zpowers v ≤ Hv := Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have huH : u ∈ Hv := Subgroup.mem_centralizer_singleton_iff.mpr (hcommV u huV v hv)
  set N : Subgroup ↥Hv := (Subgroup.zpowers v).subgroupOf Hv with hN
  have hNc : N ≤ Subgroup.center ↥Hv := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    obtain ⟨k, hk⟩ := (hn : (n : G) ∈ Subgroup.zpowers v)
    have hk' : v ^ k = (n : G) := hk
    have hxv : Commute (x : G) v := Subgroup.mem_centralizer_singleton_iff.mp x.2
    have := (Commute.zpow_right hxv k).eq
    show (x : G) * (n : G) = (n : G) * (x : G)
    rw [← hk']
    exact this
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have := Subgroup.mem_center_iff.mp (hNc hn) g
    rw [this, mul_inv_cancel_right]
    exact hn
  have hN2 : Nat.card ↥N = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzH).toEquiv, hzp]
  have hLq : CFSG.IsQuasisimple ↥(L.subgroupOf Hv) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm
      r.ctx.c33.quasisimple
  have hZ : ∀ y ∈ L.subgroupOf Hv, (∀ x ∈ L.subgroupOf Hv, y * x = x * y) → y * y = 1 := by
    intro y hy hc
    have hyL : (y : G) ∈ L := hy
    have hyc : (y : G) ∈ Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (congrArg Subtype.val (hc ⟨l, hLH hl⟩ hl)).symm
    have hyV : (y : G) ∈ V₁ := by
      rw [hVc]
      exact ⟨hyL, hyc⟩
    exact Subtype.ext (hsqV _ hyV)
  have hnorm : ∀ g : ↥Hv, (QuotientGroup.mk g : ↥Hv ⧸ N) * QuotientGroup.mk (⟨u, huH⟩ : ↥Hv) =
      QuotientGroup.mk (⟨u, huH⟩ : ↥Hv) * QuotientGroup.mk g →
      g ∈ Subgroup.normalizer ((L.subgroupOf Hv : Subgroup ↥Hv) : Set ↥Hv) := by
    have key : ∀ g : ↥Hv, (QuotientGroup.mk g : ↥Hv ⧸ N) * QuotientGroup.mk (⟨u, huH⟩ : ↥Hv) =
        QuotientGroup.mk (⟨u, huH⟩ : ↥Hv) * QuotientGroup.mk g →
        ∀ x ∈ V₁, (g : G)⁻¹ * x * (g : G) ∈ V₁ := by
      intro g h
      have h1 : (QuotientGroup.mk (g * ⟨u, huH⟩) : ↥Hv ⧸ N) =
          QuotientGroup.mk (⟨u, huH⟩ * g) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact h
      have h2 : ((g * ⟨u, huH⟩)⁻¹ * (⟨u, huH⟩ * g) : ↥Hv) ∈ N := QuotientGroup.eq.mp h1
      have h3 : u⁻¹ * (g : G)⁻¹ * u * (g : G) ∈ Subgroup.zpowers v := by
        have h4 : (((g * ⟨u, huH⟩)⁻¹ * (⟨u, huH⟩ * g) : ↥Hv) : G) ∈ Subgroup.zpowers v := h2
        have h5 : (((g * ⟨u, huH⟩)⁻¹ * (⟨u, huH⟩ * g) : ↥Hv) : G) =
            u⁻¹ * (g : G)⁻¹ * u * (g : G) := by
          simp [mul_assoc]
        rwa [h5] at h4
      exact conj_mem_of_commutator_mem_zpowers D0.card₁ hsqV hv huV hv1 huv
        (Subgroup.mem_centralizer_singleton_iff.mp g.2) h3
    intro g h
    have h' : (QuotientGroup.mk g⁻¹ : ↥Hv ⧸ N) * QuotientGroup.mk (⟨u, huH⟩ : ↥Hv) =
        QuotientGroup.mk (⟨u, huH⟩ : ↥Hv) * QuotientGroup.mk g⁻¹ := by
      rw [QuotientGroup.mk_inv]
      exact (show Commute (QuotientGroup.mk g : ↥Hv ⧸ N) (QuotientGroup.mk ⟨u, huH⟩) from h).inv_left.eq
    have hgN : (g : G) ∈ Subgroup.normalizer (V₁ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have := key g⁻¹ h' x hx
        simpa using this
      · intro hx
        have := key g h _ hx
        simpa [mul_assoc] using this
    have hgI : (g : G) ∈ I ⊓ Hv := ⟨hI ▸ hgN, g.2⟩
    rw [hCI] at hgI
    have hgL : (g : G) ∈ Subgroup.normalizer (L : Set G) :=
      (sup_le Subgroup.le_normalizer r.S_le_L) hgI
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact Subgroup.mem_normalizer_iff.mp hgL (x : G)
  exact false_of_centralizer_component_quotient hAbs hComp hX N hNc hN2 (L.subgroupOf Hv) hLq hZ
    (u := ⟨u, huH⟩) (hVL huV) huv (Subtype.ext (hsqV u huV))
    (fun l hl => Subtype.ext (Subgroup.mem_centralizer_iff.mp (r.h1 huV) l hl)) hnorm

end CFSG.Quasithin.SBd14
