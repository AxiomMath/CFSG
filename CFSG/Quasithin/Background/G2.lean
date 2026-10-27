module

public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type*} [Group G]

abbrev SecQuot (A B : Subgroup G) : Type _ := ↥A ⧸ B.subgroupOf A

theorem map_subtype_subgroupOf' {X : Subgroup G} (K : Subgroup X) :
    (K.map X.subtype).subgroupOf X = K := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

instance normal_pCoreOf_subgroupOf (X : Subgroup G) : ((pCoreOf 2 X).subgroupOf X).Normal := by
  have h : (pCoreOf 2 X).subgroupOf X = pCore 2 X := map_subtype_subgroupOf' (pCore 2 X)
  rw [h]
  exact pCore_normal 2

section Sections

variable (A B : Subgroup G) [(B.subgroupOf A).Normal]

@[expose] def secMk : A →* SecQuot A B := QuotientGroup.mk' (B.subgroupOf A)

@[expose] def secImg (X : Subgroup G) : Subgroup (SecQuot A B) :=
  (X.subgroupOf A).map (secMk A B)

variable {A B}

theorem secMk_eq_one_iff {x : A} : secMk A B x = 1 ↔ (x : G) ∈ B := by
  simp [secMk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem secMk_eq_secMk_iff {x y : A} : secMk A B x = secMk A B y ↔ (x : G)⁻¹ * y ∈ B := by
  simp [secMk, QuotientGroup.eq, Subgroup.mem_subgroupOf]

theorem secMk_surjective : Function.Surjective (secMk A B) := QuotientGroup.mk'_surjective _

theorem mem_secImg {X : Subgroup G} {y : SecQuot A B} :
    y ∈ secImg A B X ↔ ∃ x : A, (x : G) ∈ X ∧ secMk A B x = y := by
  simp only [secImg, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem secMk_mem_secImg {X : Subgroup G} {x : A} (hx : (x : G) ∈ X) :
    secMk A B x ∈ secImg A B X :=
  mem_secImg.2 ⟨x, hx, rfl⟩

theorem secImg_mono {X Y : Subgroup G} (h : X ≤ Y) : secImg A B X ≤ secImg A B Y := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
  exact secMk_mem_secImg (h hx)

theorem secMk_mem_secImg_iff {X : Subgroup G} (hBX : B ≤ X) {x : A} :
    secMk A B x ∈ secImg A B X ↔ (x : G) ∈ X := by
  constructor
  · intro h
    obtain ⟨x', hx', hxx'⟩ := mem_secImg.1 h
    have h1 := secMk_eq_secMk_iff.1 hxx'
    have h2 : (x : G) = (x' : G) * ((x' : G)⁻¹ * x) := by group
    rw [h2]
    exact X.mul_mem hx' (hBX h1)
  · exact secMk_mem_secImg

theorem secMk_conj_mem_secImg {X : Subgroup G} {a : A}
    (ha : (a : G) ∈ Subgroup.normalizer (X : Set G)) {y : SecQuot A B}
    (hy : y ∈ secImg A B X) : secMk A B a * y * (secMk A B a)⁻¹ ∈ secImg A B X := by
  obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
  have h1 : (a : G) * x * (a : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.1 ha x).1 hx
  have h2 := secMk_mem_secImg (A := A) (B := B) (x := a * x * a⁻¹) (by simpa using h1)
  simpa [map_mul, map_inv] using h2

theorem secMk_mem_normalizer_secImg {X : Subgroup G} {a : A}
    (ha : (a : G) ∈ Subgroup.normalizer (X : Set G)) :
    secMk A B a ∈ Subgroup.normalizer (secImg A B X : Set (SecQuot A B)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => secMk_conj_mem_secImg ha hy, fun hy => ?_⟩
  have ha' : ((a⁻¹ : A) : G) ∈ Subgroup.normalizer (X : Set G) := by
    simpa using inv_mem ha
  have := secMk_conj_mem_secImg (B := B) ha' hy
  simpa [map_mul, map_inv, mul_assoc] using this

theorem secImg_le_iff {X : Subgroup G} {Y : Subgroup (SecQuot A B)} :
    secImg A B X ≤ Y ↔ ∀ x : A, (x : G) ∈ X → secMk A B x ∈ Y := by
  constructor
  · intro h x hx
    exact h (secMk_mem_secImg hx)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
    exact h x hx

end Sections

section Omega

variable {Γ : Type*} [Group Γ]

theorem conj_mem_omegaOneOf {Y : Subgroup Γ} {g : Γ} (hg : g ∈ Subgroup.normalizer (Y : Set Γ))
    {x : Γ} (hx : x ∈ omegaOneOf Y) : g * x * g⁻¹ ∈ omegaOneOf Y := by
  unfold omegaOneOf at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hx.1, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  | one => simp
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using (omegaOneOf Y).mul_mem ihx ihy
  | inv x _ ih => simpa [mul_assoc] using (omegaOneOf Y).inv_mem ih

theorem normalizer_le_normalizer_omegaOneOf (Y : Subgroup Γ) :
    Subgroup.normalizer (Y : Set Γ) ≤ Subgroup.normalizer (omegaOneOf Y : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_omegaOneOf hg hx, fun hx => ?_⟩
  have := conj_mem_omegaOneOf (inv_mem hg) hx
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_centerOf (Y : Subgroup Γ) :
    Subgroup.normalizer (Y : Set Γ) ≤ Subgroup.normalizer (centerOf Y : Set Γ) := by
  have key : ∀ g ∈ Subgroup.normalizer (Y : Set Γ), ∀ c ∈ centerOf Y,
      g * c * g⁻¹ ∈ centerOf Y := by
    intro g hg c hc
    refine ⟨(Subgroup.mem_normalizer_iff.1 hg c).1 hc.1, ?_⟩
    show g * c * g⁻¹ ∈ Subgroup.centralizer (Y : Set Γ)
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : g⁻¹ * s * g ∈ Y := (Subgroup.mem_normalizer_iff''.1 hg s).1 hs
    have h1 := Subgroup.mem_centralizer_iff.1 hc.2 _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => key g hg c hc, fun hc => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc⟩

theorem normalizer_le_normalizer_omegaOneCenterOf (Y : Subgroup Γ) :
    Subgroup.normalizer (Y : Set Γ) ≤ Subgroup.normalizer (omegaOneCenterOf Y : Set Γ) :=
  (normalizer_le_normalizer_centerOf Y).trans (normalizer_le_normalizer_omegaOneOf _)

theorem mem_omegaOneCenterOf {Y : Subgroup Γ} {x : Γ} (hxY : x ∈ Y)
    (hxC : ∀ y ∈ Y, y * x = x * y) (hx2 : x ^ 2 = 1) : x ∈ omegaOneCenterOf Y :=
  Subgroup.subset_closure ⟨⟨hxY, Subgroup.mem_centralizer_iff.2 hxC⟩, hx2⟩

theorem omegaOneCenterOf_le (Y : Subgroup Γ) : omegaOneCenterOf Y ≤ Y := by
  unfold omegaOneCenterOf omegaOneOf
  rw [Subgroup.closure_le]
  exact fun x hx => hx.1.1

theorem mem_centralizer_of_mem_omegaOneCenterOf {Y : Subgroup Γ} {x : Γ}
    (hx : x ∈ omegaOneCenterOf Y) {y : Γ} (hy : y ∈ Y) : y * x = x * y := by
  have hle : omegaOneCenterOf Y ≤ centerOf Y := by
    unfold omegaOneCenterOf omegaOneOf
    rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  exact Subgroup.mem_centralizer_iff.1 (hle hx).2 y hy

theorem sq_eq_one_of_mem_omegaOneCenterOf {Y : Subgroup Γ} {x : Γ}
    (hx : x ∈ omegaOneCenterOf Y) : x ^ 2 = 1 :=
  sq_eq_one_of_mem_omegaOneCenter Y hx

end Omega

@[expose] def frattiniOf (P : Subgroup G) : Subgroup G := (frattini P).map P.subtype

theorem frattiniOf_le_of_forall [Finite G] {P N : Subgroup G}
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N) (hsq : ∀ x ∈ P, x ^ 2 ∈ N) :
    frattiniOf P ≤ N := by
  rintro _ ⟨x, hx, rfl⟩
  by_contra hxN
  set N' : Subgroup P := N.subgroupOf P with hN'
  have hxN' : x ∉ N' := hxN
  have hN'le : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ N' := fun a b => hcomm a a.2 b b.2
  have hN'sq : ∀ a : P, a ^ 2 ∈ N' := fun a => hsq a a.2
  let S : Set (Subgroup P) := {M | N' ≤ M ∧ x ∉ M}
  obtain ⟨M, hMS, hMmax⟩ := Set.Finite.exists_maximal (Set.toFinite S) ⟨N', le_rfl, hxN'⟩
  have hMn : M.Normal := by
    refine ⟨fun m hm g => ?_⟩
    have h1 : g * m * g⁻¹ * m⁻¹ ∈ M := hMS.1 (hN'le g m)
    have h2 : g * m * g⁻¹ = (g * m * g⁻¹ * m⁻¹) * m := by group
    rw [h2]
    exact M.mul_mem h1 hm
  have hcoatom : IsCoatom M := by
    refine ⟨fun h => hMS.2 (h ▸ Subgroup.mem_top x), fun K hMK => ?_⟩
    have hxK : x ∈ K := by
      by_contra hxK
      have : K ≤ M := hMmax ⟨hMS.1.trans hMK.le, hxK⟩ hMK.le
      exact absurd hMK (not_lt_of_ge this)
    rw [eq_top_iff]
    intro y _
    by_contra hyK
    have hyM : y ∉ M := fun h => hyK (hMK.le h)
    have hxsup : x ∈ M ⊔ Subgroup.zpowers y := by
      by_contra hxsup
      have hle : M ⊔ Subgroup.zpowers y ≤ M :=
        hMmax ⟨hMS.1.trans le_sup_left, hxsup⟩ le_sup_left
      exact hyM (hle (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
    have hyyM : y * y ∈ M := by simpa [sq] using hMS.1 (hN'sq y)
    obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hxsup
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
    · have h1 : y ^ k ∈ M := by
        rw [hj, zpow_mul, zpow_two]
        exact M.zpow_mem hyyM j
      exact hMS.2 (M.mul_mem hm h1)
    · apply hyK
      have h1 : y ^ k = (y * y) ^ j * y := by
        rw [hj, zpow_add_one, zpow_mul, zpow_two]
      have h2 : y = ((y * y) ^ j)⁻¹ * (m⁻¹ * (m * y ^ k)) := by
        rw [h1]
        group
      rw [h2]
      refine K.mul_mem (K.inv_mem (K.zpow_mem (hMK.le hyyM) j))
        (K.mul_mem (K.inv_mem (hMK.le hm)) hxK)
  exact hMS.2 (frattini_le_coatom hcoatom hx)


@[expose] def lOne (L V₁ : Subgroup G) : Subgroup G :=
  oTwoUpper (L ⊓ Subgroup.normalizer (V₁ : Set G))

@[expose] def tildeOf (V₁ X : Subgroup G) :
    Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁) :=
  secImg (Subgroup.normalizer (V₁ : Set G)) V₁ X

@[expose] def IsIrredOnSection (X V V₁ : Subgroup G) : Prop :=
  V₁ < V ∧ X ≤ Subgroup.normalizer (V : Set G) ∧ X ≤ Subgroup.normalizer (V₁ : Set G) ∧
    ∀ W : Subgroup G, V₁ ≤ W → W ≤ V → X ≤ Subgroup.normalizer (W : Set G) → W = V₁ ∨ W = V

structure AlmostSpecialHyp (V V₁ L T H : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 V
  ne_bot : V₁ ≠ ⊥
  le_V : V₁ ≤ V
  oTwo_eq : L = oTwoUpper L
  V_le_T : V ≤ T
  T_le_normV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  T_le_normV : T ≤ Subgroup.normalizer (V : Set G)
  T_le_normL : T ≤ Subgroup.normalizer (L : Set G)
  sylow_LT : IsSylowTwoOf T (L ⊔ T)
  H_le : H ≤ Subgroup.normalizer (V₁ : Set G)
  lOne_sup_le : lOne L V₁ ⊔ T ≤ H
  sylow_H : IsSylowTwoOf T H
  charTwo : CharTwo H
  irred : IsIrredOnSection (lOne L V₁ ⊔ T) V V₁

theorem exists_pow_two_pow_eq_one_of_mem {K : Subgroup G} (hK : IsPGroup 2 K) {c : G}
    (hc : c ∈ K) : ∃ k : ℕ, c ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hK ⟨c, hc⟩
  refine ⟨k, ?_⟩
  have := congrArg Subtype.val hk
  simpa using this

theorem isPGroup_two_of_forall {K : Subgroup G} (h : ∀ c ∈ K, ∃ k : ℕ, c ^ 2 ^ k = 1) :
    IsPGroup 2 K := by
  intro c
  obtain ⟨k, hk⟩ := h c c.2
  refine ⟨k, ?_⟩
  apply Subtype.ext
  simpa using hk

theorem pCoreOf_two_le_of_isSylowTwoOf [Finite G] {T H : Subgroup G} (h : IsSylowTwoOf T H) :
    pCoreOf 2 H ≤ T := by
  have hT : IsPGroup 2 (T.subgroupOf H) :=
    h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe h.1).symm
  let S : Sylow 2 H := hT.toSylow h.2.2
  have hn : (pCore 2 H).Normal := pCore_normal 2
  have hle : pCore 2 H ≤ (S : Subgroup H) := (pCore_isPGroup 2).le_sylow_of_normal S
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hle hy
  change y ∈ T.subgroupOf H at hy'
  exact hy'

theorem eq_one_of_odd_orderOf_of_mem {K : Subgroup G} (hK : IsPGroup 2 K) {y : G}
    (hy : y ∈ K) (ho : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem hK hy
  have h1 : orderOf y ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 ho)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 dvd_rfl)

theorem isPGroup_two_of_odd_orderOf_eq_one [Finite G] {K : Subgroup G}
    (h : ∀ y ∈ K, Odd (orderOf y) → y = 1) : IsPGroup 2 K := by
  refine isPGroup_two_of_forall fun c hc => ?_
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  refine ⟨k, h _ (K.pow_mem hc _) ?_⟩
  have h2k : (2 ^ k : ℕ) ≠ 0 := by positivity
  rw [orderOf_pow' _ h2k, hkm, Nat.gcd_mul_right_left, Nat.mul_div_cancel_left _ (by positivity)]
  exact hm


theorem le_normalizer_of_conj_mem {X W : Subgroup G}
    (h : ∀ x ∈ X, ∀ w ∈ W, x * w * x⁻¹ ∈ W) : X ≤ Subgroup.normalizer (W : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => h x hx w hw, fun hw => ?_⟩
  simpa [mul_assoc] using h x⁻¹ (X.inv_mem hx) _ hw

theorem mem_pCoreOf_of_commutator_le [Finite G] {H V₁ : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁ : IsPGroup 2 V₁) (hchar : CharTwo H)
    {x : G} (hxH : x ∈ H) (hxV₁ : ∀ v ∈ V₁, x * v = v * x)
    (hxQ : ∀ q ∈ pCoreOf 2 H, x * q * x⁻¹ * q⁻¹ ∈ V₁) : x ∈ pCoreOf 2 H := by
  set Q := pCoreOf 2 H with hQdef
  have hQp : IsPGroup 2 Q := pCoreOf_isPGroup 2 H
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf 2 H
  have hconjQ : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q :=
    fun h hh q hq => (Subgroup.mem_normalizer_iff.1 (hHQ hh) q).1 hq
  have hconjV : ∀ h ∈ H, ∀ v ∈ V₁, h * v * h⁻¹ ∈ V₁ :=
    fun h hh v hv => (Subgroup.mem_normalizer_iff.1 (hHN hh) v).1 hv
  let K : Subgroup G :=
    { carrier := {y | y ∈ H ∧ (∀ v ∈ V₁, y * v = v * y) ∧ ∀ q ∈ Q, y * q * y⁻¹ * q⁻¹ ∈ V₁}
      one_mem' := ⟨H.one_mem, fun v _ => by simp, fun q _ => by simp⟩
      mul_mem' := by
        rintro y y' ⟨hyH, hyv, hyQ⟩ ⟨hy'H, hy'v, hy'Q⟩
        refine ⟨H.mul_mem hyH hy'H, fun v hv => ?_, fun q hq => ?_⟩
        · calc y * y' * v = y * (y' * v) := by group
            _ = y * (v * y') := by rw [hy'v v hv]
            _ = (y * v) * y' := by group
            _ = (v * y) * y' := by rw [hyv v hv]
            _ = v * (y * y') := by group
        · have hc := hy'Q q hq
          have hc' := hyQ q hq
          have hyc : y * (y' * q * y'⁻¹ * q⁻¹) * y⁻¹ = y' * q * y'⁻¹ * q⁻¹ := by
            have := hyv _ hc
            calc y * (y' * q * y'⁻¹ * q⁻¹) * y⁻¹
                = (y * (y' * q * y'⁻¹ * q⁻¹)) * y⁻¹ := by group
              _ = ((y' * q * y'⁻¹ * q⁻¹) * y) * y⁻¹ := by rw [this]
              _ = y' * q * y'⁻¹ * q⁻¹ := by group
          have : y * y' * q * (y * y')⁻¹ * q⁻¹ =
              (y * (y' * q * y'⁻¹ * q⁻¹) * y⁻¹) * (y * q * y⁻¹ * q⁻¹) := by group
          rw [this, hyc]
          exact V₁.mul_mem hc hc'
      inv_mem' := by
        rintro y ⟨hyH, hyv, hyQ⟩
        refine ⟨H.inv_mem hyH, fun v hv => ?_, fun q hq => ?_⟩
        · calc y⁻¹ * v = y⁻¹ * (v * y) * y⁻¹ := by group
            _ = y⁻¹ * (y * v) * y⁻¹ := by rw [hyv v hv]
            _ = v * y⁻¹ := by group
        · have hq' : y⁻¹ * q * y ∈ Q := by
            simpa using hconjQ y⁻¹ (H.inv_mem hyH) q hq
          have hc := hyQ _ hq'
          have : y⁻¹ * q * y⁻¹⁻¹ * q⁻¹ = (y * (y⁻¹ * q * y) * y⁻¹ * (y⁻¹ * q * y)⁻¹)⁻¹ := by
            group
          rw [this]
          exact V₁.inv_mem hc }
  have hKH : K ≤ H := fun y hy => hy.1
  have hconjK : ∀ h ∈ H, ∀ y ∈ K, h * y * h⁻¹ ∈ K := by
    rintro h hh y ⟨hyH, hyv, hyQ⟩
    refine ⟨H.mul_mem (H.mul_mem hh hyH) (H.inv_mem hh), fun v hv => ?_, fun q hq => ?_⟩
    · have hv' : h⁻¹ * v * h ∈ V₁ := by simpa using hconjV h⁻¹ (H.inv_mem hh) v hv
      have := hyv _ hv'
      calc h * y * h⁻¹ * v = h * (y * (h⁻¹ * v * h)) * h⁻¹ := by group
        _ = h * ((h⁻¹ * v * h) * y) * h⁻¹ := by rw [this]
        _ = v * (h * y * h⁻¹) := by group
    · have hq' : h⁻¹ * q * h ∈ Q := by simpa using hconjQ h⁻¹ (H.inv_mem hh) q hq
      have hc := hconjV h hh _ (hyQ _ hq')
      have : h * y * h⁻¹ * q * (h * y * h⁻¹)⁻¹ * q⁻¹ =
          h * (y * (h⁻¹ * q * h) * y⁻¹ * (h⁻¹ * q * h)⁻¹) * h⁻¹ := by group
      rw [this]
      exact hc
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_conj_mem hconjK
  have hA : ∀ y ∈ K, Odd (orderOf y) → y = 1 := by
    rintro y ⟨hyH, hyv, hyQ⟩ ho
    have hcentQ : ∀ q ∈ Q, q * y = y * q := by
      intro q hq
      set c := y * q * y⁻¹ * q⁻¹ with hc
      have hcV : c ∈ V₁ := hyQ q hq
      have hyc : y * c = c * y := hyv c hcV
      have hbc : ∀ k : ℕ, y * c ^ k = c ^ k * y := fun k => (Commute.pow_right hyc k)
      have hcc : ∀ k : ℕ, c ^ k * c = c * c ^ k := fun k => (Commute.pow_self c k).eq
      have hyq : y * q * y⁻¹ = c * q := by rw [hc]; group
      have hpow : ∀ k : ℕ, y ^ k * q * (y ^ k)⁻¹ = c ^ k * q := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have h1 : y ^ (k + 1) * q * (y ^ (k + 1))⁻¹ = y * (y ^ k * q * (y ^ k)⁻¹) * y⁻¹ := by
            rw [pow_succ']
            group
          have h2 : y * c ^ k * y⁻¹ = c ^ k := by
            rw [hbc k, mul_assoc, mul_inv_cancel, mul_one]
          calc y ^ (k + 1) * q * (y ^ (k + 1))⁻¹
              = y * (y ^ k * q * (y ^ k)⁻¹) * y⁻¹ := h1
            _ = y * (c ^ k * q) * y⁻¹ := by rw [ih]
            _ = (y * c ^ k * y⁻¹) * (y * q * y⁻¹) := by group
            _ = c ^ k * (c * q) := by rw [h2, hyq]
            _ = c ^ (k + 1) * q := by rw [pow_succ, hcc k]; group
      have hm := hpow (orderOf y)
      rw [pow_orderOf_eq_one] at hm
      simp only [one_mul, inv_one, mul_one] at hm
      have hcm : c ^ orderOf y = 1 := by
        have : c ^ orderOf y * q = 1 * q := by rw [← hm, one_mul]
        simpa using this
      obtain ⟨a, ha⟩ := exists_pow_two_pow_eq_one_of_mem hV₁ hcV
      have hcop : Nat.Coprime (2 ^ a) (orderOf y) :=
        Nat.Coprime.pow_left a (Nat.coprime_two_left.2 ho)
      have hc1 : c = 1 := orderOf_eq_one_iff.1
        (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one ha)
          (orderOf_dvd_of_pow_eq_one hcm))
      have h1 : y * q * y⁻¹ * q⁻¹ = 1 := hc1
      have h4 : y * q * y⁻¹ = q := mul_inv_eq_one.1 h1
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    have hyQ' : y ∈ Q := hchar ⟨hyH, Subgroup.mem_centralizer_iff.2 hcentQ⟩
    exact eq_one_of_odd_orderOf_of_mem hQp hyQ' ho
  have hKp : IsPGroup 2 K := isPGroup_two_of_odd_orderOf_eq_one hA
  have hKQ : K ≤ Q := le_pCoreOf_of_le_normalizer 2 hKH hHK hKp
  exact hKQ ⟨hxH, hxV₁, hxQ⟩


private theorem sq_eq_one_of_mem_closure_of_comm {S : Set G}
    (hS : ∀ x ∈ S, x ^ 2 = 1)
    (hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x)
    {x : G} (hx : x ∈ Subgroup.closure S) : x ^ 2 = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [Commute.mul_pow (hc x hx y hy) 2, ihx, ihy, mul_one]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem normalizer_le_normalizer_centralizer' (S : Subgroup G) :
    Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (S : Set G), ∀ c ∈ Subgroup.centralizer (S : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := (Subgroup.mem_normalizer_iff''.1 hg s).1 hs
    have h1 := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * s := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  exact ⟨fun hc => key g hg c hc, fun hc => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc⟩

private theorem relIndex_sup_eq_of_le_normalizer' {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

private theorem not_two_dvd_relIndex_inf' [Finite G] {S H D : Subgroup G}
    (hS : IsSylowTwoOf S H) (hDH : D ≤ H) (hSN : S ≤ Subgroup.normalizer (D : Set G)) :
    ¬ 2 ∣ (S ⊓ D).relIndex D := by
  have h1 : (S ⊓ D).relIndex S * S.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (S ⊓ D).relIndex D * D.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (S ⊔ D) = (S ⊓ D).relIndex S :=
    (relIndex_sup_eq_of_le_normalizer' hSN).trans (Subgroup.inf_relIndex_left S D).symm
  have h4 : 0 < (S ⊓ D).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((S ⊓ D).subgroupOf S)))
  have h5 : (S ⊓ D).relIndex D = S.relIndex (S ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((S ⊓ D).relIndex S) ((S ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  have h6 := Subgroup.relIndex_mul_relIndex S (S ⊔ D) H le_sup_left (sup_le hS.1 hDH)
  exact fun h => hS.2.2 (h.trans ⟨_, h6.symm⟩)

private theorem exists_relIndex_eq_two_pow' [Finite G] {K D : Subgroup G}
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    ∃ n : ℕ, K.relIndex D = 2 ^ n := by
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

private theorem le_sup_inf_of_two_power' [Finite G] {K D S H : Subgroup G}
    (hS : IsSylowTwoOf S H) (hDH : D ≤ H) (hSD : S ≤ Subgroup.normalizer (D : Set G))
    (hDK : D ≤ Subgroup.normalizer (K : Set G)) (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ (2 ^ k) ∈ K) :
    D ≤ (K ⊓ D) ⊔ (S ⊓ D) := by
  obtain ⟨n, hn⟩ := exists_relIndex_eq_two_pow' hDK hD
  have hodd := not_two_dvd_relIndex_inf' hS hDH hSD
  rw [← Subgroup.relIndex_eq_one]
  have h1 : ((K ⊓ D) ⊔ (S ⊓ D)).relIndex D ∣ 2 ^ n :=
    ((Subgroup.inf_relIndex_right K D).trans hn) ▸ Subgroup.relIndex_dvd_of_le_left D le_sup_left
  have h2 : ((K ⊓ D) ⊔ (S ⊓ D)).relIndex D ∣ (S ⊓ D).relIndex D :=
    Subgroup.relIndex_dvd_of_le_left D le_sup_right
  have hcop : Nat.Coprime (2 ^ n) ((S ⊓ D).relIndex D) :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact Nat.eq_one_of_dvd_coprimes hcop h1 h2

theorem isTwoReducedIn_conjClosure_of_isSylowTwoOf [Finite G] {H T Z : Subgroup G}
    (hT : IsSylowTwoOf T H) (hZO : Z ≤ pCoreOf 2 H) (hZT : Z ≤ quasithinOmegaOneCenter T) :
    conjClosure Z H ≤ centerOf (pCoreOf 2 H) ∧ IsTwoReducedIn H (conjClosure Z H) := by
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf hT
  have hZcT : ∀ z ∈ Z, ∀ t ∈ T, t * z = z * t := fun z hz t ht =>
    mem_centralizer_of_mem_omegaOneCenterOf (Y := T) (hZT hz) ht
  have hZc : Z ≤ centerOf (pCoreOf 2 H) := fun z hz =>
    ⟨hZO hz, Subgroup.mem_centralizer_iff.2 fun q hq => hZcT z hz q (hOT hq)⟩
  have hle : conjClosure Z H ≤ centerOf (pCoreOf 2 H) := by
    refine conjClosure_le fun h hh z hz => ?_
    exact (Subgroup.mem_normalizer_iff.1
      (normalizer_le_normalizer_centerOf (pCoreOf 2 H) (le_normalizer_pCoreOf 2 H hh)) z).1
      (hZc hz)
  have hcomm : ∀ x ∈ conjClosure Z H, ∀ y ∈ conjClosure Z H, x * y = y * x :=
    fun x hx y hy => (hle hy).2 x (hle hx).1
  have hsq : ∀ x ∈ conjClosure Z H, x ^ 2 = 1 := by
    intro x hx
    refine sq_eq_one_of_mem_closure_of_comm
      (S := {x | ∃ h ∈ H, ∃ z ∈ Z, h * z * h⁻¹ = x}) ?_ hcomm hx
    rintro _ ⟨h, -, z, hz, rfl⟩
    rw [conj_pow, sq_eq_one_of_mem_omegaOneCenter T (hZT hz), mul_one, mul_inv_cancel]
  refine ⟨hle, ?_⟩
  refine ⟨hle.trans (inf_le_left.trans (pCoreOf_le 2 H)), le_normalizer_conjClosure Z H,
    ⟨⟨⟨fun x y => Subtype.ext (hcomm x x.2 y y.2)⟩⟩, hsq⟩, ?_⟩
  intro D hDH hDN hD
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) :=
    Subgroup.le_centralizer_iff.mp fun z hz =>
      Subgroup.mem_centralizer_iff.2 fun t ht => hZcT z hz t ht
  have hDle := le_sup_inf_of_two_power' hT hDH (hT.1.trans hDN)
    (hDH.trans ((le_normalizer_conjClosure Z H).trans
      (normalizer_le_normalizer_centralizer' _))) hD
  have hDZ : D ≤ Subgroup.centralizer (Z : Set G) :=
    hDle.trans (sup_le (inf_le_left.trans (Subgroup.centralizer_le (le_conjClosure Z H)))
      (inf_le_left.trans hTZ))
  rw [Subgroup.le_centralizer_iff]
  refine conjClosure_le fun h hh z hz => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : h⁻¹ * d * h ∈ D := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hDN (H.inv_mem hh)) d).mp hd
  have hcomm' : z * (h⁻¹ * d * h) = (h⁻¹ * d * h) * z := hDZ hd' z hz
  calc d * (h * z * h⁻¹) = h * ((h⁻¹ * d * h) * z) * h⁻¹ := by group
    _ = h * (z * (h⁻¹ * d * h)) * h⁻¹ := by rw [hcomm']
    _ = h * z * h⁻¹ * d := by group


section Sections2

variable {A B : Subgroup G} [(B.subgroupOf A).Normal]

theorem commutator_mem_of_secMk_commute {x y : A}
    (hxy : secMk A B x * secMk A B y = secMk A B y * secMk A B x) :
    (x : G) * y * (x : G)⁻¹ * (y : G)⁻¹ ∈ B := by
  have h : secMk A B (x * y * x⁻¹ * y⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hxy]
    group
  simpa using secMk_eq_one_iff.1 h

theorem isPGroup_secImg {p : ℕ} {X : Subgroup G} (hXA : X ≤ A) (hX : IsPGroup p X) :
    IsPGroup p (secImg A B X) := by
  have : IsPGroup p (X.subgroupOf A) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXA).symm
  exact this.map (secMk A B)

theorem relIndex_secImg {T H : Subgroup G} (hBT : B ≤ T) (hTH : T ≤ H) (hHA : H ≤ A) :
    (secImg A B T).relIndex (secImg A B H) = T.relIndex H := by
  unfold secImg
  rw [Subgroup.relIndex_map_map]
  have hker : (secMk A B).ker = B.subgroupOf A := QuotientGroup.ker_mk' _
  have h1 : B.subgroupOf A ≤ T.subgroupOf A := fun x hx => hBT hx
  have h2 : B.subgroupOf A ≤ H.subgroupOf A := fun x hx => hTH (hBT hx)
  rw [hker, sup_eq_left.2 h1, sup_eq_left.2 h2, Subgroup.relIndex_subgroupOf hHA]

theorem isSylowTwoOf_secImg {T H : Subgroup G} (hT : IsSylowTwoOf T H) (hHA : H ≤ A)
    (hBT : B ≤ T) : IsSylowTwoOf (secImg A B T) (secImg A B H) := by
  refine ⟨secImg_mono hT.1, isPGroup_secImg (hT.1.trans hHA) hT.2.1, ?_⟩
  change ¬ 2 ∣ (secImg A B T).relIndex (secImg A B H)
  rw [relIndex_secImg hBT hT.1 hHA]
  exact hT.2.2

theorem secImg_conjClosure_le {V H : Subgroup G} {Y : Subgroup (SecQuot A B)} (hHA : H ≤ A)
    (hVA : V ≤ A)
    (hY : ∀ x : A, (x : G) ∈ H → secMk A B x ∈ Subgroup.normalizer (Y : Set (SecQuot A B)))
    (hV : secImg A B V ≤ Y) : secImg A B (conjClosure V H) ≤ Y := by
  let K : Subgroup G := (Y.comap (secMk A B)).map A.subtype
  have hK : conjClosure V H ≤ K := by
    refine conjClosure_le fun h hh v hv => ?_
    have hAh : h ∈ A := hHA hh
    have hAv : v ∈ A := hVA hv
    refine ⟨⟨h, hAh⟩ * ⟨v, hAv⟩ * ⟨h, hAh⟩⁻¹, ?_, by simp⟩
    show secMk A B (⟨h, hAh⟩ * ⟨v, hAv⟩ * ⟨h, hAh⟩⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hY ⟨h, hAh⟩ hh) _).1 (hV (secMk_mem_secImg hv))
  rw [secImg_le_iff]
  intro x hx
  obtain ⟨x', hx', hxx'⟩ := hK hx
  have : x' = x := Subtype.ext hxx'
  have hx'' : secMk A B x' ∈ Y := hx'
  rwa [← this]

end Sections2


abbrev tmk (V₁ : Subgroup G) :
    Subgroup.normalizer (V₁ : Set G) →* SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁ :=
  secMk (Subgroup.normalizer (V₁ : Set G)) V₁

namespace AlmostSpecialHyp

section NoFinite

variable {V V₁ L T H : Subgroup G} (h : AlmostSpecialHyp V V₁ L T H)

include h

theorem T_le_H : T ≤ H := le_sup_right.trans h.lOne_sup_le

theorem V_le_H : V ≤ H := h.V_le_T.trans h.T_le_H

theorem V_le_N : V ≤ Subgroup.normalizer (V₁ : Set G) := h.V_le_T.trans h.T_le_normV₁

theorem isPGroup_T : IsPGroup 2 T := h.sylow_H.2.1

theorem isPGroup_V₁ : IsPGroup 2 V₁ := h.isPGroup_T.to_le (h.le_V.trans h.V_le_T)

theorem V₁_le_pCoreOf : V₁ ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 (h.le_V.trans h.V_le_H) h.H_le h.isPGroup_V₁

theorem commV {x y : G} (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x :=
  congrArg Subtype.val (h.elemAbelian.1.is_comm.comm (⟨x, hx⟩ : V) ⟨y, hy⟩)

theorem sq_eq_one_of_mem_V {x : G} (hx : x ∈ V) : x ^ 2 = 1 := h.elemAbelian.2 x hx

end NoFinite

section WithFinite

variable [Finite G] {V V₁ L T H : Subgroup G} (h : AlmostSpecialHyp V V₁ L T H)

include h

theorem pCoreOf_le_T : pCoreOf 2 H ≤ T := pCoreOf_two_le_of_isSylowTwoOf h.sylow_H

theorem exists_fixed_element :
    ∃ z : Subgroup.normalizer (V₁ : Set G), (z : G) ∈ V ∧ (z : G) ∉ V₁ ∧
      ∀ t : Subgroup.normalizer (V₁ : Set G), (t : G) ∈ T →
        tmk V₁ z * tmk V₁ t = tmk V₁ t * tmk V₁ z := by
  set N := Subgroup.normalizer (V₁ : Set G) with hN
  have hT2 : IsPGroup 2 (secImg N V₁ T) := isPGroup_secImg h.T_le_normV₁ h.isPGroup_T
  have : Group.IsNilpotent (secImg N V₁ T) := hT2.isNilpotent
  have hVT : secImg N V₁ V ≤ secImg N V₁ T := secImg_mono h.V_le_T
  have hnorm : secImg N V₁ T ≤ Subgroup.normalizer (secImg N V₁ V : Set _) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_secImg.1 hy
    exact secMk_mem_normalizer_secImg (h.T_le_normV ht)
  have : ((secImg N V₁ V).subgroupOf (secImg N V₁ T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  obtain ⟨v, hvV, hvV₁⟩ : ∃ v ∈ V, v ∉ V₁ := by
    by_contra hcon
    exact not_le_of_gt h.irred.1 fun v hv => by_contra fun hv1 => hcon ⟨v, hv, hv1⟩
  have hvN : v ∈ N := h.V_le_N hvV
  have hv_ne : secMk N V₁ ⟨v, hvN⟩ ≠ 1 := fun h1 => hvV₁ (secMk_eq_one_iff.1 h1)
  have hne : (secImg N V₁ V).subgroupOf (secImg N V₁ T) ≠ ⊥ := by
    intro hbot
    have hmem : (⟨secMk N V₁ ⟨v, hvN⟩, hVT (secMk_mem_secImg hvV)⟩ : ↥(secImg N V₁ T)) ∈
        (secImg N V₁ V).subgroupOf (secImg N V₁ T) :=
      Subgroup.mem_subgroupOf.2 (secMk_mem_secImg hvV)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hv_ne (congrArg Subtype.val hmem)
  obtain ⟨w, hw⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨z, hzV, hz⟩ := mem_secImg.1 (Subgroup.mem_subgroupOf.1 w.2.1)
  refine ⟨z, hzV, ?_, ?_⟩
  · intro hzV₁
    apply hw
    have h1 : (w.1 : SecQuot N V₁) = 1 := by rw [← hz]; exact secMk_eq_one_iff.2 hzV₁
    exact Subtype.ext (Subtype.ext h1)
  · intro t ht
    have hc := Subgroup.mem_center_iff.1 w.2.2 ⟨secMk N V₁ t, secMk_mem_secImg ht⟩
    have := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at this
    rw [← hz] at this
    exact this.symm

theorem mem_pCoreOf_of_fixed {z : Subgroup.normalizer (V₁ : Set G)} (hzV : (z : G) ∈ V)
    (hz : ∀ t : Subgroup.normalizer (V₁ : Set G), (t : G) ∈ T →
      tmk V₁ z * tmk V₁ t = tmk V₁ t * tmk V₁ z) : (z : G) ∈ pCoreOf 2 H := by
  refine mem_pCoreOf_of_commutator_le h.H_le h.isPGroup_V₁ h.charTwo (h.V_le_H hzV)
    (fun v hv => h.commV hzV (h.le_V hv)) (fun q hq => ?_)
  have hqN : q ∈ Subgroup.normalizer (V₁ : Set G) := h.H_le (pCoreOf_le 2 H hq)
  have := hz ⟨q, hqN⟩ (h.pCoreOf_le_T hq)
  exact commutator_mem_of_secMk_commute (x := z) (y := ⟨q, hqN⟩) this

omit [Finite G] in
theorem tildeOf_V_le {Y : Subgroup (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)}
    (hY : ∀ x : Subgroup.normalizer (V₁ : Set G), (x : G) ∈ H →
      tmk V₁ x ∈ Subgroup.normalizer (Y : Set _))
    (hex : ∃ z : Subgroup.normalizer (V₁ : Set G), (z : G) ∈ V ∧ (z : G) ∉ V₁ ∧
      tmk V₁ z ∈ Y) : tildeOf V₁ V ≤ Y := by
  set N := Subgroup.normalizer (V₁ : Set G) with hN
  let W : Subgroup G := V ⊓ (Y.comap (secMk N V₁)).map N.subtype
  have hWmem : ∀ x : N, (x : G) ∈ W ↔ (x : G) ∈ V ∧ secMk N V₁ x ∈ Y := by
    intro x
    constructor
    · rintro ⟨hxV, x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      have hx'' : secMk N V₁ x' ∈ Y := hx'
      exact ⟨hxV, by rw [← this]; exact hx''⟩
    · rintro ⟨hxV, hx⟩
      exact ⟨hxV, x, hx, rfl⟩
  have hV₁W : V₁ ≤ W := by
    intro v hv
    have hvN : v ∈ N := Subgroup.le_normalizer hv
    refine (hWmem ⟨v, hvN⟩).2 ⟨h.le_V hv, ?_⟩
    rw [secMk_eq_one_iff.2 hv]
    exact Y.one_mem
  have hWV : W ≤ V := inf_le_left
  have hnormW : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_mem fun x hx w hw => ?_
    have hxH : x ∈ H := h.lOne_sup_le hx
    have hxN : x ∈ N := h.H_le hxH
    have hwN : w ∈ N := h.V_le_N (hWV hw)
    have hxV : x * w * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (h.irred.2.1 hx) w).1 (hWV hw)
    have hxwN : x * w * x⁻¹ ∈ N := N.mul_mem (N.mul_mem hxN hwN) (N.inv_mem hxN)
    have hwY := ((hWmem ⟨w, hwN⟩).1 hw).2
    refine (hWmem ⟨x * w * x⁻¹, hxwN⟩).2 ⟨hxV, ?_⟩
    have h1 : secMk N V₁ (⟨x * w * x⁻¹, hxwN⟩ : N) =
        secMk N V₁ ⟨x, hxN⟩ * secMk N V₁ ⟨w, hwN⟩ * (secMk N V₁ ⟨x, hxN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    exact (Subgroup.mem_normalizer_iff.1 (hY ⟨x, hxN⟩ hxH) _).1 hwY
  obtain ⟨z, hzV, hzV₁, hzY⟩ := hex
  have hW : W = V₁ ∨ W = V := h.irred.2.2.2 W hV₁W hWV hnormW
  have hWeq : W = V := by
    rcases hW with hW | hW
    · exfalso
      have hzW := (hWmem z).2 ⟨hzV, hzY⟩
      rw [hW] at hzW
      exact hzV₁ hzW
    · exact hW
  unfold tildeOf
  rw [secImg_le_iff]
  intro x hx
  have hxW : (x : G) ∈ W := by rw [hWeq]; exact hx
  exact ((hWmem x).1 hxW).2

omit [Finite G] in
theorem conjClosure_le_N : conjClosure V H ≤ Subgroup.normalizer (V₁ : Set G) :=
  conjClosure_le fun _ hh _ hv =>
    (Subgroup.normalizer (V₁ : Set G)).mul_mem
      ((Subgroup.normalizer (V₁ : Set G)).mul_mem (h.H_le hh) (h.V_le_N hv))
      ((Subgroup.normalizer (V₁ : Set G)).inv_mem (h.H_le hh))

theorem G22_one :
    tildeOf V₁ V ≤ tildeOf V₁ (conjClosure V H) ∧
      tildeOf V₁ (conjClosure V H) ≤ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) := by
  refine ⟨secImg_mono (le_conjClosure V H), ?_⟩
  set N := Subgroup.normalizer (V₁ : Set G) with hN
  set Y := omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) with hYdef
  have hY : ∀ x : N, (x : G) ∈ H → tmk V₁ x ∈ Subgroup.normalizer (Y : Set _) := by
    intro x hx
    exact normalizer_le_normalizer_omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H))
      (secMk_mem_normalizer_secImg (le_normalizer_pCoreOf 2 H hx))
  obtain ⟨z, hzV, hzV₁, hz⟩ := h.exists_fixed_element
  have hzQ : (z : G) ∈ pCoreOf 2 H := h.mem_pCoreOf_of_fixed hzV hz
  have hzY : tmk V₁ z ∈ Y := by
    refine mem_omegaOneCenterOf (secMk_mem_secImg hzQ) ?_ ?_
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := mem_secImg.1 hy
      exact (hz q (h.pCoreOf_le_T hq)).symm
    · have hz2 : z ^ 2 = 1 := Subtype.ext (by simpa using h.sq_eq_one_of_mem_V hzV)
      rw [← map_pow, hz2, map_one]
  have hVY : tildeOf V₁ V ≤ Y := h.tildeOf_V_le hY ⟨z, hzV, hzV₁, hzY⟩
  exact secImg_conjClosure_le h.H_le h.V_le_N hY hVY

theorem G22_two : frattiniOf (conjClosure V H) ≤ V₁ := by
  have hU := h.G22_one.2
  have hcc := h.conjClosure_le_N
  have hmemY : ∀ u (hu : u ∈ conjClosure V H),
      tmk V₁ ⟨u, hcc hu⟩ ∈ omegaOneCenterOf (tildeOf V₁ (pCoreOf 2 H)) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  refine frattiniOf_le_of_forall (fun x hx y hy => ?_) (fun x hx => ?_)
  · have hyQ : tmk V₁ ⟨y, hcc hy⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
      omegaOneCenterOf_le _ (hmemY y hy)
    have hxy : tmk V₁ ⟨x, hcc hx⟩ * tmk V₁ ⟨y, hcc hy⟩ =
        tmk V₁ ⟨y, hcc hy⟩ * tmk V₁ ⟨x, hcc hx⟩ :=
      (mem_centralizer_of_mem_omegaOneCenterOf (hmemY x hx) hyQ).symm
    exact commutator_mem_of_secMk_commute hxy
  · have h1 := sq_eq_one_of_mem_omegaOneCenterOf (hmemY x hx)
    rw [← map_pow] at h1
    simpa using secMk_eq_one_iff.1 h1

theorem G22_three :
    conjClosure V H ≤ T ∧ T ≤ Subgroup.normalizer (conjClosure V H : Set G) := by
  refine ⟨fun u hu => ?_, h.T_le_H.trans (le_normalizer_conjClosure V H)⟩
  have hcc := h.conjClosure_le_N
  have hU := h.G22_one.2
  have hQ : tmk V₁ ⟨u, hcc hu⟩ ∈ tildeOf V₁ (pCoreOf 2 H) :=
    omegaOneCenterOf_le _ ((secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu)
  exact h.pCoreOf_le_T ((secMk_mem_secImg_iff h.V₁_le_pCoreOf).1 hQ)

theorem G22_four : IsTwoReducedIn (tildeOf V₁ H) (tildeOf V₁ (conjClosure V H)) := by
  set N := Subgroup.normalizer (V₁ : Set G) with hN
  set Ht := tildeOf V₁ H with hHt
  set Tt := tildeOf V₁ T with hTt
  set Z : Subgroup (SecQuot N V₁) :=
    tildeOf V₁ V ⊓ Subgroup.centralizer (Tt : Set (SecQuot N V₁)) with hZ
  have hTtsyl : IsSylowTwoOf Tt Ht :=
    isSylowTwoOf_secImg h.sylow_H h.H_le (h.le_V.trans h.V_le_T)
  have hZfix : ∀ y ∈ Z, ∃ z : N, (z : G) ∈ V ∧ tmk V₁ z = y ∧
      ∀ t : N, (t : G) ∈ T → tmk V₁ z * tmk V₁ t = tmk V₁ t * tmk V₁ z := by
    intro y hy
    obtain ⟨z, hzV, rfl⟩ := mem_secImg.1 hy.1
    exact ⟨z, hzV, rfl, fun t ht =>
      (Subgroup.mem_centralizer_iff.1 hy.2 _ (secMk_mem_secImg ht)).symm⟩
  have hQt : tildeOf V₁ (pCoreOf 2 H) ≤ pCoreOf 2 Ht := by
    refine le_pCoreOf_of_le_normalizer 2 (secImg_mono (pCoreOf_le 2 H)) ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
      exact secMk_mem_normalizer_secImg (le_normalizer_pCoreOf 2 H hx)
    · exact isPGroup_secImg ((pCoreOf_le 2 H).trans h.H_le) (pCoreOf_isPGroup 2 H)
  have hZO : Z ≤ pCoreOf 2 Ht := by
    intro y hy
    obtain ⟨z, hzV, rfl, hz⟩ := hZfix y hy
    exact hQt (secMk_mem_secImg (h.mem_pCoreOf_of_fixed hzV hz))
  have hZT : Z ≤ quasithinOmegaOneCenter Tt := by
    intro y hy
    obtain ⟨z, hzV, rfl, hz⟩ := hZfix y hy
    refine mem_omegaOneCenterOf (Y := Tt) (secMk_mem_secImg (h.V_le_T hzV)) ?_ ?_
    · intro t ht
      obtain ⟨t', ht', rfl⟩ := mem_secImg.1 ht
      exact (hz t' ht').symm
    · have hz2 : z ^ 2 = 1 := Subtype.ext (by simpa using h.sq_eq_one_of_mem_V hzV)
      rw [← map_pow, hz2, map_one]
  obtain ⟨-, hR2⟩ := isTwoReducedIn_conjClosure_of_isSylowTwoOf hTtsyl hZO hZT
  have hEq : conjClosure Z Ht = tildeOf V₁ (conjClosure V H) := by
    apply le_antisymm
    · refine conjClosure_le fun ĥ hĥ y hy => ?_
      obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hĥ
      obtain ⟨z, hzV, rfl, -⟩ := hZfix y hy
      have hxzx : (x : G) * z * (x : G)⁻¹ ∈ conjClosure V H := mem_conjClosure hx hzV
      have := secMk_mem_secImg (A := N) (B := V₁) (X := conjClosure V H) (x := x * z * x⁻¹)
        (by simpa using hxzx)
      simpa [map_mul, map_inv, tildeOf] using this
    · have hnorm : ∀ x : N, (x : G) ∈ H →
          tmk V₁ x ∈ Subgroup.normalizer (conjClosure Z Ht : Set (SecQuot N V₁)) :=
        fun x hx => le_normalizer_conjClosure Z Ht (secMk_mem_secImg hx)
      refine secImg_conjClosure_le h.H_le h.V_le_N hnorm ?_
      refine h.tildeOf_V_le hnorm ?_
      obtain ⟨z, hzV, hzV₁, hz⟩ := h.exists_fixed_element
      refine ⟨z, hzV, hzV₁, le_conjClosure Z Ht ?_⟩
      refine ⟨secMk_mem_secImg hzV, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      obtain ⟨t, ht, rfl⟩ := mem_secImg.1 hy
      exact (hz t ht).symm
  rw [← hEq]
  exact hR2

end WithFinite

end AlmostSpecialHyp

end CFSG.Quasithin
