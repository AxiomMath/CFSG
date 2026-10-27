module

public import CFSG.Quasithin.Background.B6Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace B6

open scoped Pointwise

variable {Y : Type*} [Group Y]

open scoped Classical in
@[expose] noncomputable def indAut (L : Subgroup Y) (n : Y) : MulAut L :=
  if h : n ∈ Subgroup.normalizer (L : Set Y) then conjAct L ⟨n, h⟩ else 1

theorem indAut_of_mem {L : Subgroup Y} {n : Y} (hn : n ∈ Subgroup.normalizer (L : Set Y)) :
    indAut L n = conjAct L ⟨n, hn⟩ := by
  simp only [indAut, hn, ↓reduceDIte]

theorem coe_indAut_apply {L : Subgroup Y} {n : Y} (hn : n ∈ Subgroup.normalizer (L : Set Y))
    (x : L) : ((indAut L n x : L) : Y) = n * x * n⁻¹ := by
  rw [indAut_of_mem hn]
  exact Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion le_rfl ⟨n, hn⟩) x

theorem indAut_one (L : Subgroup Y) : indAut L 1 = 1 := by
  rw [indAut_of_mem (one_mem _)]
  exact map_one (conjAct L)

theorem indAut_mul {L : Subgroup Y} {x y : Y} (hx : x ∈ Subgroup.normalizer (L : Set Y))
    (hy : y ∈ Subgroup.normalizer (L : Set Y)) : indAut L (x * y) = indAut L x * indAut L y := by
  rw [indAut_of_mem (mul_mem hx hy), indAut_of_mem hx, indAut_of_mem hy]
  exact map_mul (conjAct L) ⟨x, hx⟩ ⟨y, hy⟩

theorem indAut_inv {L : Subgroup Y} {x : Y} (hx : x ∈ Subgroup.normalizer (L : Set Y)) :
    indAut L x⁻¹ = (indAut L x)⁻¹ := by
  rw [indAut_of_mem (inv_mem hx), indAut_of_mem hx]
  exact map_inv (conjAct L) ⟨x, hx⟩

theorem indAut_pow {L : Subgroup Y} {x : Y} (hx : x ∈ Subgroup.normalizer (L : Set Y)) (m : ℕ) :
    indAut L (x ^ m) = indAut L x ^ m := by
  rw [indAut_of_mem (pow_mem hx m), indAut_of_mem hx]
  exact map_pow (conjAct L) ⟨x, hx⟩ m

theorem indAut_eq_one_iff {L : Subgroup Y} {n : Y} (hn : n ∈ Subgroup.normalizer (L : Set Y)) :
    indAut L n = 1 ↔ n ∈ Subgroup.centralizer (L : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    have := congrArg (fun φ : MulAut L => ((φ ⟨x, hx⟩ : L) : Y)) h
    simp only [coe_indAut_apply hn, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  · intro h
    ext x
    rw [coe_indAut_apply hn, MulAut.one_apply]
    exact mul_inv_eq_iff_eq_mul.mpr (h x x.2).symm

theorem indAut_eq_one_of_mem_centralizer {L : Subgroup Y} {n : Y}
    (hn : n ∈ Subgroup.normalizer (L : Set Y)) (hc : n ∈ Subgroup.centralizer (L : Set Y)) :
    indAut L n = 1 := (indAut_eq_one_iff hn).mpr hc

theorem mem_autOn_iff_indAut {H L : Subgroup Y} {φ : MulAut L} :
    φ ∈ autOn H L ↔ ∃ n ∈ H, n ∈ Subgroup.normalizer (L : Set Y) ∧ indAut L n = φ := by
  unfold autOn
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, Subgroup.mem_subgroupOf.mp hg, g.2, by rw [indAut_of_mem g.2]⟩
  · rintro ⟨n, hnH, hnN, rfl⟩
    exact ⟨⟨n, hnN⟩, Subgroup.mem_subgroupOf.mpr hnH, (indAut_of_mem hnN).symm⟩

theorem indAut_mem_autOn {H L : Subgroup Y} {n : Y} (hnH : n ∈ H)
    (hn : n ∈ Subgroup.normalizer (L : Set Y)) : indAut L n ∈ autOn H L :=
  mem_autOn_iff_indAut.mpr ⟨n, hnH, hn, rfl⟩

theorem autOn_le_autOn_of_le {H H' L : Subgroup Y} (h : H ≤ H') : autOn H L ≤ autOn H' L :=
  CFSG.Quasithin.AutOn.autOn_mono h

@[expose] def preAut (L : Subgroup Y) (V : Subgroup (MulAut L)) : Subgroup Y where
  carrier := {y | y ∈ Subgroup.normalizer (L : Set Y) ∧ indAut L y ∈ V}
  one_mem' := ⟨one_mem _, by rw [indAut_one]; exact one_mem V⟩
  mul_mem' := fun {x y} hx hy =>
    ⟨mul_mem hx.1 hy.1, by rw [indAut_mul hx.1 hy.1]; exact mul_mem hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [indAut_inv hx.1]; exact inv_mem hx.2⟩

theorem mem_preAut {L : Subgroup Y} {V : Subgroup (MulAut L)} {y : Y} :
    y ∈ preAut L V ↔ y ∈ Subgroup.normalizer (L : Set Y) ∧ indAut L y ∈ V := Iff.rfl

@[expose] noncomputable def innAut (L : Subgroup Y) : L →* MulAut L :=
  (conjAct L).comp (Subgroup.inclusion Subgroup.le_normalizer)

theorem indAut_eq_innAut (L : Subgroup Y) (x : L) : indAut L (x : Y) = innAut L x :=
  indAut_of_mem (Subgroup.le_normalizer x.2)

theorem innAut_injective {L : Subgroup Y} (hL : IsSimpleGroup L) (hLn : ¬ IsMulCommutative L) :
    Function.Injective (innAut L) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hnorm : (innAut L).ker.Normal := MonoidHom.normal_ker _
  rcases Subgroup.Normal.eq_bot_or_eq_top (innAut L).ker with h | h
  · exact h
  · exfalso
    apply hLn
    rw [isMulCommutative_iff]
    intro a b
    have h1 : innAut L a = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top a)
    have h2 := congrArg (fun φ : MulAut L => ((φ b : L) : Y)) h1
    simp only [← indAut_eq_innAut, coe_indAut_apply (Subgroup.le_normalizer a.2),
      MulAut.one_apply] at h2
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp h2)

theorem not_isPGroup_two_of_simple [Finite Y] {L : Subgroup Y} (hL : IsSimpleGroup L)
    (hLn : ¬ IsMulCommutative L) : ¬ IsPGroup 2 L := by
  intro hp
  apply hLn
  have hbot : ⊥ < Subgroup.center L := hp.bot_lt_center
  exact Subgroup.center_eq_top_iff.mp
    ((Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center L)).resolve_left hbot.ne')

theorem isPGroup_autOn {T : Subgroup Y} (hT : IsPGroup 2 T) (L : Subgroup Y) :
    IsPGroup 2 (autOn T L) :=
  CFSG.Quasithin.AutOn.isPGroup_autOn hT

theorem eq_top_of_forall_mul_of_odd_index {G : Type*} [Group G] [Finite G] {P Λ : Subgroup G}
    (hΛ : IsPGroup 2 Λ) (hodd : ¬ 2 ∣ P.index) (hdec : ∀ x : G, ∃ l ∈ Λ, ∃ p ∈ P, x = l * p) :
    P = ⊤ := by
  obtain ⟨q, hq⟩ := hΛ.nonempty_fixed_point_of_prime_not_dvd_card (G ⧸ P) hodd
  have hfix : ∀ l ∈ Λ, ((l : G) • q : G ⧸ P) = q := fun l hl =>
    MulAction.mem_fixedPoints.mp hq ⟨l, hl⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨l₀, hl₀, p₀, hp₀, rfl⟩ := hdec g₀
  have hΛP : Λ ≤ P := by
    intro l hl
    have hl' : l₀ * l⁻¹ * l₀⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hl₀ (Λ.inv_mem hl)) (Λ.inv_mem hl₀)
    have h1 := hfix _ hl'
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul] at h1
    have h2 : ((l₀ * l⁻¹ * l₀⁻¹) * (l₀ * p₀))⁻¹ * (l₀ * p₀) = p₀⁻¹ * l * p₀ := by group
    rw [h2] at h1
    have h3 := P.mul_mem (P.mul_mem hp₀ h1) (P.inv_mem hp₀)
    simpa [mul_assoc] using h3
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨l, hl, p, hp, rfl⟩ := hdec x
  exact P.mul_mem (hΛP hl) hp

@[expose] noncomputable def innPre (T L : Subgroup Y) : Subgroup L := (autOn T L).comap (innAut L)

theorem mem_innPre {T L : Subgroup Y} {x : L} : x ∈ innPre T L ↔ innAut L x ∈ autOn T L := Iff.rfl

structure AutData (T L K C : Subgroup Y) : Prop where
  normal : K.Normal
  fac : ∀ y : Y, ∃ t ∈ T, ∃ k ∈ K, y = t * k
  L_le : L ≤ K
  C_le : C ≤ K
  K_le_normalizer_L : K ≤ Subgroup.normalizer (L : Set Y)
  K_le_normalizer_C : K ≤ Subgroup.normalizer (C : Set Y)
  decomp : ∀ k ∈ K, ∃ l ∈ L, ∃ c ∈ C, k = l * c
  disj : L ⊓ C = ⊥
  C_le_centralizer : C ≤ Subgroup.centralizer (L : Set Y)
  conj_le_C : ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set Y) → conjSub t L ≤ C
  gen : K = ⨆ t ∈ T, conjSub t L
  simple : IsSimpleGroup L
  nonabelian : ¬ IsMulCommutative L
  isPGroup_T : IsPGroup 2 T
  sylow_TL : IsSylowTwoOf (T ⊓ L) L
  TL_ne_bot : T ⊓ L ≠ ⊥

namespace AutData

variable {T L K C : Subgroup Y}

theorem isPGroup_innPre (d : AutData T L K C) : IsPGroup 2 (innPre T L) :=
  (isPGroup_autOn d.isPGroup_T L).comap_of_injective (innAut L)
    (innAut_injective d.simple d.nonabelian)

theorem innPre_ne_top [Finite Y] (d : AutData T L K C) : innPre T L ≠ ⊤ := by
  intro htop
  have hp := d.isPGroup_innPre
  rw [htop] at hp
  exact not_isPGroup_two_of_simple d.simple d.nonabelian (hp.of_equiv Subgroup.topEquiv)

theorem innPre_ne_bot (d : AutData T L K C) : innPre T L ≠ ⊥ := by
  intro hbot
  apply d.TL_ne_bot
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxL : x ∈ L := hx.2
  have hxT : x ∈ T := hx.1
  have : (⟨x, hxL⟩ : L) ∈ innPre T L := by
    rw [mem_innPre, ← indAut_eq_innAut]
    exact indAut_mem_autOn hxT (Subgroup.le_normalizer hxL)
  rw [hbot, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem autOn_lt [Finite Y] (d : AutData T L K C) : autOn T L < autOn ⊤ L := by
  refine lt_of_le_of_ne (autOn_le_autOn_of_le le_top) fun heq => d.innPre_ne_top ?_
  rw [eq_top_iff]
  intro x _
  rw [mem_innPre, ← indAut_eq_innAut, heq]
  exact indAut_mem_autOn (Subgroup.mem_top _) (Subgroup.le_normalizer x.2)

theorem not_le_normalizer [Finite Y] (d : AutData T L K C) :
    ¬ autOn ⊤ L ≤ Subgroup.normalizer (autOn T L : Set (MulAut L)) := by
  intro hn
  have : (innPre T L).Normal := ⟨fun x hx g => by
    rw [mem_innPre, map_mul, map_mul, map_inv]
    have hg : innAut L g ∈ Subgroup.normalizer (autOn T L : Set (MulAut L)) :=
      hn (by
        rw [← indAut_eq_innAut]
        exact indAut_mem_autOn (Subgroup.mem_top _) (Subgroup.le_normalizer g.2))
    exact (Subgroup.mem_normalizer_iff.mp hg _).mp hx⟩
  have := d.simple
  rcases Subgroup.Normal.eq_bot_or_eq_top (innPre T L) with h | h
  · exact d.innPre_ne_bot h
  · exact d.innPre_ne_top h

theorem mem_normalizer_K (d : AutData T L K C) (g : Y) :
    g ∈ Subgroup.normalizer (K : Set Y) := by
  have := Subgroup.normalizer_eq_top_iff.mpr d.normal
  rw [this]
  exact Subgroup.mem_top g

theorem conjSub_K (d : AutData T L K C) (g : Y) : conjSub g K = K :=
  conjSub_eq_self (d.mem_normalizer_K g)

theorem decomp_of_mem_normalizer (d : AutData T L K C) {y : Y}
    (hy : y ∈ Subgroup.normalizer (L : Set Y)) :
    ∃ t ∈ T, t ∈ Subgroup.normalizer (L : Set Y) ∧ ∃ l ∈ L, ∃ c ∈ C, y = t * l * c := by
  obtain ⟨t, ht, k, hk, rfl⟩ := d.fac y
  obtain ⟨l, hl, c, hc, rfl⟩ := d.decomp k hk
  refine ⟨t, ht, ?_, l, hl, c, hc, by rw [mul_assoc]⟩
  have h2 : t * (l * c) * (l * c)⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
    mul_mem hy (inv_mem (d.K_le_normalizer_L hk))
  rwa [mul_inv_cancel_right] at h2

theorem indAut_decomp (d : AutData T L K C) {t l c : Y}
    (htN : t ∈ Subgroup.normalizer (L : Set Y)) (hl : l ∈ L) (hc : c ∈ C) :
    indAut L (t * l * c) = indAut L t * innAut L ⟨l, hl⟩ := by
  have hlN : l ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer hl
  have hcN : c ∈ Subgroup.normalizer (L : Set Y) := d.K_le_normalizer_L (d.C_le hc)
  rw [indAut_mul (mul_mem htN hlN) hcN, indAut_mul htN hlN,
    indAut_eq_one_of_mem_centralizer hcN (d.C_le_centralizer hc), mul_one]
  exact congrArg (indAut L t * ·) (indAut_eq_innAut L ⟨l, hl⟩)

theorem autOn_top_le (d : AutData T L K C) {V : Subgroup (MulAut L)} (hTV : autOn T L ≤ V)
    (hLV : ∀ x : L, innAut L x ∈ V) : autOn ⊤ L ≤ V := by
  intro φ hφ
  obtain ⟨y, -, hyN, rfl⟩ := mem_autOn_iff_indAut.mp hφ
  obtain ⟨t, ht, htN, l, hl, c, hc, rfl⟩ := d.decomp_of_mem_normalizer hyN
  rw [d.indAut_decomp htN hl hc]
  exact mul_mem (hTV (indAut_mem_autOn ht htN)) (hLV ⟨l, hl⟩)

theorem le_autOn_M [Finite Y] {M : Subgroup Y} (h : MinParabolic (⊤ : Subgroup Y) T M)
    (d : AutData T L K C) {V : Subgroup (MulAut L)} (hTV : autOn T L ≤ V)
    (hVA : V < autOn ⊤ L) : V ≤ autOn M L := by
  have hCN : ∀ {c : Y}, c ∈ C → c ∈ Subgroup.normalizer (L : Set Y) := fun hc =>
    d.K_le_normalizer_L (d.C_le hc)
  have hTV' : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set Y) → t ∈ preAut L V :=
    fun t ht htN => ⟨htN, hTV (indAut_mem_autOn ht htN)⟩
  have hCV : ∀ c ∈ C, c ∈ preAut L V := fun c hc =>
    ⟨hCN hc, by
      rw [indAut_eq_one_of_mem_centralizer (hCN hc) (d.C_le_centralizer hc)]
      exact one_mem V⟩
  obtain ⟨Y₀, hY₀⟩ : ∃ Y₀ : Subgroup Y, Y₀ = preAut L V ⊓ L := ⟨_, rfl⟩
  have hY₀L : Y₀ ≤ L := by rw [hY₀]; exact inf_le_right
  have hY₀V : Y₀ ≤ preAut L V := by rw [hY₀]; exact inf_le_left
  have hY₀of : ∀ y, y ∈ preAut L V → y ∈ L → y ∈ Y₀ := fun y h1 h2 => by
    rw [hY₀]; exact ⟨h1, h2⟩
  have hY₀lt : Y₀ < L := by
    refine lt_of_le_of_ne hY₀L fun heq => ?_
    have hLV : ∀ x : L, innAut L x ∈ V := fun x => by
      rw [← indAut_eq_innAut]
      refine (hY₀V ?_).2
      rw [heq]
      exact x.2
    exact absurd (d.autOn_top_le hTV hLV) (not_le_of_gt hVA)
  have hY₀n : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set Y) →
      t ∈ Subgroup.normalizer (Y₀ : Set Y) := by
    intro t ht htN
    rw [hY₀]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hTV' t ht htN), htN⟩
  obtain ⟨W, hW⟩ : ∃ W : Subgroup Y, W = ⨆ t ∈ T, conjSub t Y₀ := ⟨_, rfl⟩
  have hW1 : Y₀ ≤ W := by
    rw [hW]
    exact le_iSup₂_of_le 1 T.one_mem (by rw [conjSub_one])
  have hW2 : ∀ s ∈ T, conjSub s W ≤ W := by
    intro s hs
    rw [hW]
    simp only [OrderIso.map_iSup]
    refine iSup₂_le fun t ht => ?_
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (s * t) (T.mul_mem hs ht) le_rfl
  have hWn : T ≤ Subgroup.normalizer (W : Set Y) := fun s hs =>
    mem_normalizer_of_conjSub_le (hW2 s hs) (hW2 s⁻¹ (T.inv_mem hs))
  have hWK : W ≤ K := by
    rw [hW]
    refine iSup₂_le fun t ht => ?_
    have h1 : conjSub t Y₀ ≤ conjSub t K := (conjSub t).monotone (hY₀L.trans d.L_le)
    rwa [d.conjSub_K] at h1
  have hWC : W ≤ Y₀ ⊔ C := by
    rw [hW]
    refine iSup₂_le fun t ht => ?_
    by_cases htN : t ∈ Subgroup.normalizer (L : Set Y)
    · rw [conjSub_eq_self (hY₀n t ht htN)]
      exact le_sup_left
    · exact ((conjSub t).monotone hY₀L).trans ((d.conj_le_C t ht htN).trans le_sup_right)
  have hTK : ∀ x ∈ T, x ∈ K → x ∈ Y₀ ⊔ C := by
    intro x hxT hxK
    have hxN := d.K_le_normalizer_L hxK
    obtain ⟨l, hl, c, hc, rfl⟩ := d.decomp x hxK
    have hxV : l * c ∈ preAut L V := hTV' _ hxT hxN
    have hlV : l ∈ preAut L V := by
      have := mul_mem hxV (inv_mem (hCV c hc))
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem_sup (hY₀of l hlV hl) hc
  have hne : Y₀ ⊔ T ≠ ⊤ := by
    intro htop
    have hLWT : L ≤ W ⊔ T := by
      intro l _
      have : l ∈ Y₀ ⊔ T := by rw [htop]; exact Subgroup.mem_top l
      exact sup_le_sup_right hW1 T this
    have hset : ((W ⊔ T : Subgroup Y) : Set Y) = (W : Set Y) * (T : Set Y) :=
      Subgroup.coe_mul_of_right_le_normalizer_left W T hWn
    have hLY : L ≤ Y₀ ⊔ C := by
      intro l hl
      have hmem : l ∈ ((W ⊔ T : Subgroup Y) : Set Y) := hLWT hl
      rw [hset] at hmem
      obtain ⟨w, hw, t, ht, hwt⟩ := hmem
      have hwt : w * t = l := hwt
      subst hwt
      have htK : t ∈ K := by
        have := mul_mem (inv_mem (hWK hw)) (d.L_le hl)
        rwa [inv_mul_cancel_left] at this
      exact mul_mem (hWC hw) (hTK t ht htK)
    have hLY0 : L ≤ Y₀ := by
      intro l hl
      have hmem : l ∈ ((Y₀ ⊔ C : Subgroup Y) : Set Y) := hLY hl
      rw [Subgroup.coe_mul_of_left_le_normalizer_right Y₀ C
        (fun y hy => d.K_le_normalizer_C (d.L_le (hY₀L hy)))] at hmem
      obtain ⟨y, hy, c, hc, hyc⟩ := hmem
      have hyc : y * c = l := hyc
      subst hyc
      have hcL : c ∈ L := by
        have := mul_mem (inv_mem (hY₀L hy)) hl
        rwa [inv_mul_cancel_left] at this
      have hc1 : c = 1 := by
        have : c ∈ L ⊓ C := ⟨hcL, hc⟩
        rw [d.disj] at this
        exact Subgroup.mem_bot.mp this
      rw [hc1, mul_one]
      exact hy
    exact absurd hLY0 (not_le_of_gt hY₀lt)
  have hY₀M : Y₀ ≤ M :=
    le_sup_left.trans (h.le_of_lt le_sup_right (lt_top_iff_ne_top.mpr hne))
  intro φ hφ
  obtain ⟨y, -, hyN, rfl⟩ := mem_autOn_iff_indAut.mp (hVA.le hφ)
  obtain ⟨t, ht, htN, l, hl, c, hc, rfl⟩ := d.decomp_of_mem_normalizer hyN
  have hlN : l ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer hl
  have hlV : l ∈ preAut L V := by
    refine ⟨hlN, ?_⟩
    have h1 : indAut L t * innAut L ⟨l, hl⟩ ∈ V := by
      rw [← d.indAut_decomp htN hl hc]
      exact hφ
    have h2 : indAut L t ∈ V := hTV (indAut_mem_autOn ht htN)
    have h3 := mul_mem (inv_mem h2) h1
    rw [inv_mul_cancel_left] at h3
    rw [indAut_eq_innAut L ⟨l, hl⟩]
    exact h3
  have hlM : l ∈ M := hY₀M (hY₀of l hlV hl)
  refine mem_autOn_iff_indAut.mpr ⟨t * l, M.mul_mem (h.le ht) hlM, mul_mem htN hlN, ?_⟩
  rw [d.indAut_decomp htN hl hc, indAut_mul htN hlN]
  exact congrArg (indAut L t * ·) (indAut_eq_innAut L ⟨l, hl⟩)

theorem autOn_M_ne [Finite Y] {M : Subgroup Y} (h : MinParabolic (⊤ : Subgroup Y) T M)
    (d : AutData T L K C) (hKM : ¬ K ≤ M) : autOn M L ≠ autOn ⊤ L := by
  intro hMA
  have hCN : ∀ {c : Y}, c ∈ C → c ∈ Subgroup.normalizer (L : Set Y) := fun hc =>
    d.K_le_normalizer_L (d.C_le hc)
  have hdec : ∀ x : L, ∃ l ∈ innPre T L, ∃ p ∈ (((M ⊓ K) ⊔ C).subgroupOf L), x = l * p := by
    intro x
    have hx : innAut L x ∈ autOn M L := by
      rw [hMA, ← indAut_eq_innAut]
      exact indAut_mem_autOn (Subgroup.mem_top _) (Subgroup.le_normalizer x.2)
    obtain ⟨m, hmM, hmN, hm⟩ := mem_autOn_iff_indAut.mp hx
    obtain ⟨t, ht, k, hk, rfl⟩ := d.fac m
    obtain ⟨l, hl, c, hc, rfl⟩ := d.decomp k hk
    have htN : t ∈ Subgroup.normalizer (L : Set Y) := by
      have h2 : t * (l * c) * (l * c)⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
        mul_mem hmN (inv_mem (d.K_le_normalizer_L hk))
      rwa [mul_inv_cancel_right] at h2
    have hkM : l * c ∈ M := by
      have := M.mul_mem (M.inv_mem (h.le ht)) hmM
      rwa [inv_mul_cancel_left] at this
    have hlP : l ∈ (M ⊓ K) ⊔ C := by
      have := Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hkM, hk⟩ : l * c ∈ M ⊓ K) (inv_mem hc)
      rwa [mul_inv_cancel_right] at this
    refine ⟨x * (⟨l, hl⟩ : L)⁻¹, ?_, ⟨l, hl⟩, hlP, by group⟩
    rw [mem_innPre, map_mul, map_inv]
    rw [← mul_assoc, d.indAut_decomp htN hl hc] at hm
    rw [← hm, mul_inv_cancel_right]
    exact indAut_mem_autOn ht htN
  have hodd : ¬ 2 ∣ (((M ⊓ K) ⊔ C).subgroupOf L).index := by
    have hle : ((T ⊓ L).subgroupOf L) ≤ (((M ⊓ K) ⊔ C).subgroupOf L) := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact Subgroup.mem_sup_left (⟨h.le hx.1, d.L_le hx.2⟩ : (x : Y) ∈ M ⊓ K)
    exact fun hdvd => d.sylow_TL.2.2 (hdvd.trans (Subgroup.index_dvd_of_le hle))
  have hP : ((M ⊓ K) ⊔ C).subgroupOf L = ⊤ :=
    eq_top_of_forall_mul_of_odd_index d.isPGroup_innPre hodd hdec
  have hLP : L ≤ (M ⊓ K) ⊔ C := by
    intro l hl
    have : (⟨l, hl⟩ : L) ∈ ((M ⊓ K) ⊔ C).subgroupOf L := by rw [hP]; exact Subgroup.mem_top _
    exact this
  have hnormD : (M.subgroupOf L).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : (g : Y) ∈ (((M ⊓ K) ⊔ C : Subgroup Y) : Set Y) := hLP g.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (M ⊓ K) C
      (fun y hy => d.K_le_normalizer_C hy.2)] at hg
    obtain ⟨m, hm, c, hc, hgmc⟩ := hg
    have hcx : c * (x : Y) = (x : Y) * c :=
      (Subgroup.mem_centralizer_iff.mp (d.C_le_centralizer hc) x x.2).symm
    have e : (m * c) * (x : Y) * (m * c)⁻¹ = m * x * m⁻¹ := by
      have : c * (x : Y) * c⁻¹ = x := by rw [hcx, mul_inv_cancel_right]
      calc (m * c) * (x : Y) * (m * c)⁻¹ = m * (c * (x : Y) * c⁻¹) * m⁻¹ := by group
        _ = m * x * m⁻¹ := by rw [this]
    show (g : Y) * x * (g : Y)⁻¹ ∈ M
    rw [← hgmc, e]
    exact M.mul_mem (M.mul_mem hm.1 hx) (M.inv_mem hm.1)⟩
  have hD : M.subgroupOf L = ⊤ := by
    have := d.simple
    rcases Subgroup.Normal.eq_bot_or_eq_top (M.subgroupOf L) with hbot | htop
    · exfalso
      apply d.TL_ne_bot
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have : (⟨x, hx.2⟩ : L) ∈ M.subgroupOf L := h.le hx.1
      rw [hbot, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exact htop
  have hLM : L ≤ M := fun l hl => by
    have : (⟨l, hl⟩ : L) ∈ M.subgroupOf L := by rw [hD]; exact Subgroup.mem_top _
    exact this
  apply hKM
  rw [d.gen]
  refine iSup₂_le fun t ht x hx => ?_
  rw [mem_conjSub] at hx
  have := M.mul_mem (M.mul_mem (h.le ht) (hLM hx)) (M.inv_mem (h.le ht))
  simpa [mul_assoc] using this

end AutData

theorem exists_autData [Finite Y] {T L K : Subgroup Y} (hT : IsPGroup 2 T)
    (hKnormal : K.Normal) (hTK : T ⊔ K = ⊤) (hK1 : IsSylowTwoOf (T ⊓ K) K)
    (hL : IsSimpleGroup L) (hLn : ¬ IsMulCommutative L) (hL2 : Even (Nat.card L))
    (hLK : L ≤ K) (hgen : K = ⨆ t ∈ T, conjSub t L)
    (hind : sSupIndep {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L})
    (hnorm : ∀ t ∈ T, ((conjSub t L).subgroupOf K).Normal) :
    ∃ C : Subgroup Y, AutData T L K C := by
  obtain ⟨𝒞, h𝒞⟩ : ∃ 𝒞 : Set (Subgroup Y), 𝒞 = {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L} :=
    ⟨_, rfl⟩
  rw [← h𝒞] at hind
  have hmem𝒞 : ∀ S, S ∈ 𝒞 ↔ ∃ t ∈ T, S = conjSub t L := fun S => by rw [h𝒞]; rfl
  have hLmem : L ∈ 𝒞 := (hmem𝒞 L).mpr ⟨1, T.one_mem, (conjSub_one L).symm⟩
  have hConj_mem : ∀ t ∈ T, conjSub t L ∈ 𝒞 := fun t ht => (hmem𝒞 _).mpr ⟨t, ht, rfl⟩
  have hSK : ∀ S ∈ 𝒞, S ≤ K := by
    intro S hS
    obtain ⟨t, ht, rfl⟩ := (hmem𝒞 S).mp hS
    rw [hgen]
    exact le_iSup₂_of_le t ht le_rfl
  have hKS : ∀ S ∈ 𝒞, K ≤ Subgroup.normalizer (S : Set Y) := by
    intro S hS
    obtain ⟨t, ht, rfl⟩ := (hmem𝒞 S).mp hS
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hSK _ hS)).mp (hnorm t ht)
  obtain ⟨C, hC⟩ : ∃ C : Subgroup Y, C = sSup (𝒞 \ {L}) := ⟨_, rfl⟩
  have hSC : ∀ S ∈ 𝒞, S ≠ L → S ≤ C := fun S hS hne => by
    rw [hC]
    exact le_sSup ⟨hS, hne⟩
  have hCK : C ≤ K := by
    rw [hC]
    exact sSup_le fun S hS => hSK S hS.1
  have hconjC : ∀ k ∈ K, conjSub k C ≤ C := by
    intro k hk
    rw [hC, OrderIso.map_sSup]
    refine iSup₂_le fun S hS => ?_
    rw [conjSub_eq_self (hKS S hS.1 hk)]
    exact le_sSup hS
  have hKC : K ≤ Subgroup.normalizer (C : Set Y) := fun k hk =>
    mem_normalizer_of_conjSub_le (hconjC k hk) (hconjC k⁻¹ (K.inv_mem hk))
  have hKLC : K ≤ L ⊔ C := by
    rw [hgen]
    refine iSup₂_le fun t ht => ?_
    by_cases heq : conjSub t L = L
    · rw [heq]
      exact le_sup_left
    · exact (hSC _ (hConj_mem t ht) heq).trans le_sup_right
  have hCnL : C ≤ Subgroup.normalizer (L : Set Y) := hCK.trans (hKS L hLmem)
  have hdecomp : ∀ k ∈ K, ∃ l ∈ L, ∃ c ∈ C, k = l * c := by
    intro k hk
    have hk' : k ∈ ((L ⊔ C : Subgroup Y) : Set Y) := hKLC hk
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L C hCnL] at hk'
    obtain ⟨l, hl, c, hc, hlc⟩ := hk'
    exact ⟨l, hl, c, hc, hlc.symm⟩
  have hdisj : L ⊓ C = ⊥ := by
    have := hind hLmem
    rw [← hC] at this
    exact disjoint_iff.mp this
  have hCcent : C ≤ Subgroup.centralizer (L : Set Y) := by
    rw [hC]
    refine sSup_le fun S hS => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hdis : Disjoint L S := by
      have := (hind hLmem).mono_right (le_sSup hS)
      exact this
    have hxK : x ∈ K := hSK S hS.1 hx
    have hyK : y ∈ K := hLK hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ L := by
      refine mul_mem ?_ (inv_mem hy)
      exact (Subgroup.mem_normalizer_iff.mp (hKS L hLmem hxK) y).mp hy
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ S := by
      have h3 : y * x⁻¹ * y⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hKS S hS.1 hyK) x⁻¹).mp (inv_mem hx)
      have := mul_mem hx h3
      simpa [mul_assoc] using this
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ L ⊓ S := ⟨h1, h2⟩
    rw [disjoint_iff.mp hdis, Subgroup.mem_bot] at h3
    have h4 : x * y * x⁻¹ = y := mul_inv_eq_one.mp h3
    have h5 : x * y = y * x := by
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [h4]
    exact h5.symm
  have hconjL : ∀ t ∈ T, t ∉ Subgroup.normalizer (L : Set Y) → conjSub t L ≤ C := by
    intro t ht htN
    refine hSC _ (hConj_mem t ht) fun heq => htN ?_
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  have hfac : ∀ y : Y, ∃ t ∈ T, ∃ k ∈ K, y = t * k := by
    intro y
    have hy : y ∈ T ⊔ K := by rw [hTK]; exact Subgroup.mem_top y
    have hy' : y ∈ ((T ⊔ K : Subgroup Y) : Set Y) := hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T K
      (fun t _ => Subgroup.le_normalizer_of_normal (K := ⊤) (Subgroup.mem_top t))] at hy'
    obtain ⟨t, ht, k, hk, htk⟩ := hy'
    exact ⟨t, ht, k, hk, htk.symm⟩
  have hsyl : IsSylowTwoOf (T ⊓ L) L := by
    have := isSylowTwoOf_inf_normal hK1 hLK (hKS L hLmem)
    rwa [inf_assoc, inf_eq_right.mpr hLK] at this
  have hTL : T ⊓ L ≠ ⊥ := by
    intro hbot
    have h1 := hsyl.2.2
    rw [hbot, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h1
    exact h1 (even_iff_two_dvd.mp hL2)
  exact ⟨C, ⟨hKnormal, hfac, hLK, hCK, hKS L hLmem, hKC, hdecomp, hdisj, hCcent, hconjL, hgen, hL,
    hLn, hT, hsyl, hTL⟩⟩

end B6

theorem aut_clause {Y : Type*} [Group Y] [Finite Y] {T M L : Subgroup Y}
    (h : MinParabolic (⊤ : Subgroup Y) T M)
    (hL : IsSimpleGroup L) (hLn : ¬ IsMulCommutative L) (hL2 : Even (Nat.card L))
    (hLK : L ≤ twoResidual (⊤ : Subgroup Y))
    (hgen : twoResidual (⊤ : Subgroup Y) = ⨆ t ∈ T, conjSub t L)
    (hind : sSupIndep {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L})
    (hnorm : ∀ t ∈ T, ((conjSub t L).subgroupOf (twoResidual (⊤ : Subgroup Y))).Normal) :
    autOn ⊤ L ∈ uFamHat (autOn ⊤ L) (autOn T L) ∧
      IsUniqueMaxOver (autOn ⊤ L) (autOn T L) (autOn M L) := by
  have hKn : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (twoResidual (⊤ : Subgroup Y) : Set Y) :=
    le_normalizer_twoResidual ⊤
  have hKnormal : (twoResidual (⊤ : Subgroup Y)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hKn)
  obtain ⟨C, d⟩ := exists_autData h.isSylow.2.1 hKnormal (sup_twoResidual_eq h.isSylow)
    (isSylowTwoOf_inf_normal h.isSylow le_top hKn) hL hLn hL2 hLK hgen hind hnorm
  have hKM : ¬ twoResidual (⊤ : Subgroup Y) ≤ M := fun hle =>
    h.not_twoResidual_le_kerIn (le_kerIn_of_le_normalizer hle hKn)
  have hne := d.autOn_M_ne h hKM
  have hMA : autOn M L < autOn ⊤ L := lt_of_le_of_ne (autOn_le_autOn_of_le le_top) hne
  have hTM : autOn T L ≤ autOn M L := autOn_le_autOn_of_le h.le
  have hU : IsUniqueMaxOver (autOn ⊤ L) (autOn T L) (autOn M L) := by
    rw [isUniqueMaxOver_iff]
    refine ⟨⟨hMA, fun V hMV hVA => ?_⟩, hTM, fun V hV hTV => ?_⟩
    · by_contra hne'
      have := d.le_autOn_M h (hTM.trans hMV.le) (lt_of_le_of_ne hVA hne')
      exact absurd hMV (not_lt_of_ge this)
    · have hVM : V ≤ autOn M L := d.le_autOn_M h hTV hV.1
      by_contra hne'
      exact hne (hV.2 _ (lt_of_le_of_ne hVM hne') hMA.le)
  exact ⟨⟨⟨le_rfl, d.autOn_lt, maxOver_ncard_eq_one_iff.mpr ⟨_, hU⟩⟩, d.not_le_normalizer⟩, hU⟩

end CFSG.Quasithin
