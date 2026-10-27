module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C45
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323Sec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.CZL32 CFSG.Quasithin.H13.Par32
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement Pointwise

namespace One3323

theorem isPlane_P12 : L3.IsPlane P12 := by
  unfold L3.IsPlane P12 e1 e2
  decide +kernel

theorem bsSub_le_stabSub (S : Finset L3.Vec) : L3.bsSub S ≤ L3.stabSub S := by
  intro g hg v
  rw [L3.mem_bsSub] at hg
  constructor
  · intro hv
    rw [hg v hv]
    exact hv
  · intro hv
    have h1 : L3.act g (L3.act g v) = L3.act g v := hg _ hv
    have h2 := congrArg (L3.act g⁻¹) h1
    rw [L3.act_inv_act, L3.act_inv_act] at h2
    rw [← h2]
    exact hv

theorem stabSub_le_normalizer (S : Finset L3.Vec) :
    L3.stabSub S ≤ Subgroup.normalizer (L3.bsSub S : Set L3.Γ) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ x ∈ L3.stabSub S, ∀ g ∈ L3.bsSub S, x * g * x⁻¹ ∈ L3.bsSub S := by
    intro x hx g hg v hv
    have hxv : L3.act x⁻¹ v ∈ S := ((L3.stabSub S).inv_mem hx v).mp hv
    rw [L3.act_mul, L3.act_mul, hg _ hxv, L3.act_act_inv]
  intro g
  refine ⟨key h hh g, fun hg => ?_⟩
  have := key h⁻¹ ((L3.stabSub S).inv_mem hh) _ hg
  simpa [mul_assoc] using this

theorem sq_bsSub : ∀ g : L3.Γ, (∀ v ∈ P12, L3.act g v = v) → g * g = 1 := by
  unfold P12 e1 e2
  decide +kernel

@[expose] def aW₂ : L3.Γ := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def bW₂ : L3.Γ := ⟨!![0, 1, 0; 1, 1, 0; 0, 0, 1], by decide⟩

theorem aW₂_mem : aW₂ ∈ L3.stabSub P12 := by
  rw [L3.mem_stabSub]
  unfold aW₂ P12 e1 e2
  decide +kernel

theorem bW₂_mem : bW₂ ∈ L3.stabSub P12 := by
  rw [L3.mem_stabSub]
  unfold bW₂ P12 e1 e2
  decide +kernel

theorem comm_not_mem₂ : (bW₂ * aW₂)⁻¹ * (aW₂ * bW₂) ∉ L3.bsSub P12 := by
  rw [L3.mem_bsSub]
  unfold aW₂ bW₂ P12 e1 e2
  decide +kernel

theorem center_check₁ : ∀ g : L3.Γ, (∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec)) →
    (∀ v ∈ P12, L3.act g v = v) → ∀ h : L3.Γ,
      (L3.act h e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act h v ∈ P12) → g * h = h * g := by
  unfold P12 e1 e2
  decide +kernel

@[expose] def bSet : Finset L3.Γ :=
  Finset.univ.filter fun g : L3.Γ => L3.act g e1 = e1 ∧ ∀ v, v ∈ P12 ↔ L3.act g v ∈ P12

theorem mem_bSet {g : L3.Γ} : g ∈ bSet ↔ g ∈ bSub := by
  rw [bSet, Finset.mem_filter, mem_bSub]
  simp

theorem center_check₂ : ∀ g ∈ bSet, (∀ h ∈ bSet, g * h = h * g) →
    (∀ v, L3.act g v - v ∈ ({0, e1} : Finset L3.Vec)) ∧ ∀ v ∈ P12, L3.act g v = v := by
  unfold bSet P12 e1 e2
  decide +kernel

theorem card_invol : 9 ≤ (Finset.univ.filter L3.IsInvol).card := by
  decide +kernel

theorem normal_eq_bot {N : Subgroup L3.Γ} (hN : N.Normal) (h2 : IsPGroup 2 N) : N = ⊥ := by
  classical
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq N (by rw [hm, pow_zero]))
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 2
    (by rw [hm]; exact dvd_pow_self 2 hm0)
  have hzi : L3.IsInvol (z : L3.Γ) := by
    refine ⟨?_, fun h1 => ?_⟩
    · have := pow_orderOf_eq_one z
      rw [hz, pow_two] at this
      exact congrArg Subtype.val this
    · have : z = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hz
      omega
  have hall : ∀ w : L3.Γ, L3.IsInvol w → w ∈ N := by
    intro w hw
    obtain ⟨x, hx⟩ := L3.conj_invol hzi hw
    rw [← hx]
    exact hN.conj_mem _ z.2 x
  have hle : (Finset.univ.filter L3.IsInvol).card ≤ Nat.card N := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun w => ⟨w.1, hall w.1 (Finset.mem_filter.mp w.2).2⟩)
      fun a b hab => by
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext h1
  have hdvd : 2 ^ m ∣ 168 := by
    rw [← hm, ← card_L3Γ]
    exact Subgroup.card_subgroup_dvd_card N
  have hm3 : m ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 4 ∣ 168 := (pow_dvd_pow 2 hcon).trans hdvd
    omega
  have h8 : 2 ^ m ≤ 8 := by
    calc 2 ^ m ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hm3
      _ = 8 := by norm_num
  have := card_invol
  omega

variable {G : Type} [Group G]

theorem ncAtMost_zero_top_of_three {K N P : Subgroup G} {H : Type} [Group H] (ψ : ↥P →* H)
    (hKP : K ≤ P) (hψ3 : ∀ x (hx : x ∈ K), ψ ⟨x, hKP hx⟩ ^ 3 = 1)
    (hker : ∀ x (hx : x ∈ K), ψ ⟨x, hKP hx⟩ = 1 → x ∈ N) : NCAtMost K N K 0 := by
  rintro ⟨A, B, hAB, -⟩
  obtain ⟨⟨hBA, hAK, -, -, -, h2⟩, -, hNB, -⟩ := hAB 0
  obtain ⟨a, haA, haB⟩ := Set.exists_of_ssubset hBA
  obtain ⟨k, hk⟩ := h2 a haA
  have haK : a ∈ K := hAK haA
  set b := (a ^ 2 ^ k) ^ 2 ^ k with hb
  have hbB : b ∈ B 0 := (B 0).pow_mem hk _
  have hbK : b ∈ K := K.pow_mem (K.pow_mem haK _) _
  have h4 : ∀ n : ℕ, ∃ j, 4 ^ n = 3 * j + 1 := by
    intro n
    induction n with
    | zero => exact ⟨0, by norm_num⟩
    | succ n ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨4 * j + 1, by rw [pow_succ, hj]; ring⟩
  obtain ⟨j, hj⟩ := h4 k
  have hψb : ψ ⟨b, hKP hbK⟩ = ψ ⟨a, hKP haK⟩ := by
    have e : (⟨b, hKP hbK⟩ : ↥P) = ⟨a, hKP haK⟩ ^ (4 ^ k) := by
      apply Subtype.ext
      simp only [hb, Subgroup.coe_pow]
      rw [← pow_mul, ← mul_pow]
      norm_num
    rw [e, map_pow, hj, pow_succ, pow_mul, hψ3 a haK, one_pow, one_mul]
  have hab : a * b⁻¹ ∈ N := by
    refine hker _ (K.mul_mem haK (K.inv_mem hbK)) ?_
    have e : (⟨a * b⁻¹, hKP (K.mul_mem haK (K.inv_mem hbK))⟩ : ↥P) =
        ⟨a, hKP haK⟩ * (⟨b, hKP hbK⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, hψb, mul_inv_cancel]
  apply haB
  have := (B 0).mul_mem (hNB hab) hbB
  simpa using this

theorem sign_eq_one_of_odd {σ : Equiv.Perm (Fin 3)} (h : Odd (orderOf σ)) :
    Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ orderOf σ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem pow_three_of_sign : ∀ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ = 1 → σ ^ 3 = 1 := by
  decide

theorem isLnBlock_of_isSL3Block {L : Subgroup G} (hB : IsSL3Block L)
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂) :
    IsLnBlock L 3 := by
  obtain ⟨hshort, n, F, _, _, hFc, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hB
  have hF := Mod3323.card_eq_two hFc (C45.card_sl_eq hα₂ ⟨hαs, hαk⟩)
  refine ⟨hshort, ?_⟩
  let e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let e₂ := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)
  let α' : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    e₂.toMonoidHom.comp ((Mod3323.toL3 hF).comp (e.symm.toMonoidHom.comp α))
  let ε := Mod3323.toZ2 hF
  let β' : ↥(blockU L) →* Multiplicative (Fin 3 → ZMod 2) :=
    (AddMonoidHom.toMultiplicative (AddMonoidHom.compLeft ε.toAddMonoidHom (Fin 3))).comp β
  have hα' : ∀ l, α' l = 1 ↔ α l = 1 := by
    intro l
    simp only [α', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    rw [(map_eq_one_iff _ (Mod3323.toL3_injective hF))]
    simp
  have hβ' : ∀ u, Multiplicative.toAdd (β' u) = ε ∘ Multiplicative.toAdd (β u) := fun _ => rfl
  refine ⟨α', ?_, ?_, β', ?_, ?_, ?_⟩
  · intro y
    obtain ⟨g, hg⟩ := Mod3323.toL3_surjective hF (e₂.symm y)
    obtain ⟨l, hl⟩ := hαs (e g)
    refine ⟨l, ?_⟩
    simp only [α', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hl,
      MulEquiv.symm_apply_apply, hg, MulEquiv.apply_symm_apply]
  · rw [← hαk]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hα']
  · intro y
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd (ε.symm ∘ Multiplicative.toAdd y))
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hβ', hu]
    funext i
    simp
  · rw [← hβk]
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro h1
      apply Multiplicative.toAdd.injective
      funext i
      have := congrFun (congrArg Multiplicative.toAdd h1) i
      rw [hβ'] at this
      exact ε.injective (by simpa using this)
    · intro h1
      apply Multiplicative.toAdd.injective
      rw [hβ', h1]
      funext i
      simp
  · intro ℓ u v huv
    rw [hβ', hβ', hβe ℓ u v huv]
    have hm : ((α' ℓ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        ((Mod3323.toL3 hF (e.symm (α ℓ)) : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
      CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 (ZMod 2) _
    have hm' : (((e.symm (α ℓ)) : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = ((α ℓ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F (e.symm (α ℓ))
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    rw [hm, ← hm']
    exact (Mod3323.act_toL3 hF _ _).symm

variable [Finite G] {T M L D : Subgroup G}

omit [Finite G] in
theorem mem_of_odd (hT2 : IsPGroup 2 T) (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ L ⊔ T) (hodd : Odd (orderOf x)) : x ∈ L := by
  obtain ⟨l, hl, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTL).mp hx
  obtain ⟨a, ha⟩ := hT2 ⟨t, ht⟩
  have ha' : t ^ 2 ^ a = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hstep : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', e⟩ := ih
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), L.mul_mem hl' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht m)) l).mp hl
      · rw [pow_succ, e]
        group
  obtain ⟨l', hl', e⟩ := hstep (2 ^ a)
  rw [ha', mul_one] at e
  exact Lem3328.mem_of_pow_odd hodd (by rw [pow_orderOf_eq_one]; exact L.one_mem) (e ▸ hl')

theorem inf_qL_le : L ⊓ qL L T ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _ hx => ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hx)))
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)

theorem parabolic3 (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hLn : IsLnBlock L 3) (ρ : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ bSub)
    (hρL : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = γ)
    (hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ qL L T)
    (hρQ : ∀ g, g ∈ qL L T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1)
    {p r : Subgroup L3.Γ} (hBp : bSub ≤ p) (hrp : r ≤ p)
    (hpr : p ≤ Subgroup.normalizer (r : Set L3.Γ)) (hr2 : ∀ x ∈ r, x * x = 1)
    (hp24 : Nat.card p = 24) (hr4 : Nat.card r = 4) {a b : L3.Γ} (ha : a ∈ p) (hb : b ∈ p)
    (hab : (b * a)⁻¹ * (a * b) ∉ r) :
    oTwoUpper (oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p)) =
        oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p) ∧
      T ≤ Subgroup.normalizer (oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p) :
        Set G) ∧
      Nonempty (↥(oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p) ⊔ T) ⧸
        CFSG.pCore 2 ↥(oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p) ⊔ T) ≃*
          Equiv.Perm (Fin 3)) ∧
      ¬ HasNoncentralTwoChief (oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p)) 3 ∧
      pCoreOf 2 (oTwoUpper (pre ρ (sup_le Subgroup.le_normalizer hTL) p) ⊔ T) =
        pre ρ (sup_le Subgroup.le_normalizer hTL) r ∧
      pre ρ (sup_le Subgroup.le_normalizer hTL) r ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hT2 : IsPGroup 2 T := h.toSetup331.isSylowTwoOf.2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have htop : (ρ.comp (Subgroup.inclusion hLTN)).range = ⊤ := by
    rw [eq_top_iff]
    intro γ _
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have h6 : Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ p) =
      6 * Nat.card ↥((ρ.comp (Subgroup.inclusion hLTN)).range ⊓ r) := by
    rw [htop, top_inf_eq, top_inf_eq, hp24, hr4]
  obtain ⟨ℓa, hℓa, ea⟩ := hρL a
  obtain ⟨ℓb, hℓb, eb⟩ := hρL b
  obtain ⟨hXX, hTX, hXT, ⟨e⟩, hO2, hRT⟩ := parabolic_gen ρ hLTN hT2 hTidx
    (fun g hg h1 => hK g hg (hLTN hg) h1) (fun t ht => hBp (hρT t ht)) hrp hpr hr2 h6 hℓa hℓb
    (by rw [ea]; exact ha) (by rw [eb]; exact hb) (by rw [ea, eb]; exact hab)
  refine ⟨hXX, hTX, nonempty_quot_pCore_congr hXT ⟨e⟩, ?_, by rw [hXT]; exact hO2, hRT⟩
  set P := pre ρ hLTN p with hP
  set R := pre ρ hLTN r with hR
  set X := oTwoUpper P with hX
  have hXP : X ≤ P := oTwoUpper_le P
  have hXL : X ≤ L := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxP, hxo⟩
    exact mem_of_odd hT2 hTL (pre_le_sup ρ hLTN p hxP) hxo
  have hshort := hLn.1
  have hZU : blockZ L ≤ blockU L := inf_le_left
  have hUO : blockU L ≤ pCoreOf 2 L := hshort.2.2.1.1.trans inf_le_left
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hLTN)
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hOR : pCoreOf 2 L ≤ R := fun x hx =>
    (mem_pre ρ hLTN).mpr ⟨hQLT (hOQ hx), by
      rw [hρQ x (hOQ hx)]
      exact r.one_mem⟩
  have hXN : ∀ x ∈ X, x ∈ Subgroup.normalizer (L : Set G) := fun x hx =>
    Subgroup.le_normalizer (hXL hx)
  have hXZ : X ≤ Subgroup.normalizer ((X ⊓ blockZ L : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (C1.mem_normalizer_blockZ (hXN x hx))
  have hXU : X ≤ Subgroup.normalizer ((X ⊓ blockU L : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx) (C1.mem_normalizer_blockU (hXN x hx))
  have hXO : X ≤ Subgroup.normalizer ((X ⊓ pCoreOf 2 L : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hXL hx))
  have hXR : X ≤ Subgroup.normalizer ((X ⊓ R : Subgroup G) : Set G) := fun x hx =>
    ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hx)
      (pre_le_normalizer ρ hLTN hpr (hXP hx))
  have hUZ : (blockZ L).relIndex (blockU L) = 8 := by
    obtain ⟨-, -, -, β, hβs, hβk, -⟩ := hLn.2
    rw [Subgroup.relIndex, ← hβk]
    exact Sec3323.index_ker_eq (by rw [ZMod.card]) β hβs
  have s1 : NCAtMost X ⊥ (X ⊓ blockZ L) 0 := by
    refine ncAtMost_zero_of_commutator_le (le_of_eq ?_)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact inf_le_right.trans (inf_le_right.trans (Subgroup.centralizer_le hXL))
  have s2 : NCAtMost X (X ⊓ blockZ L) (X ⊓ blockU L) 1 := by
    refine ncAtMost_of_relIndex_lt (lt_of_le_of_lt ?_ (by norm_num : (8 : ℕ) < 4 ^ (1 + 1)))
    have e1 : X ⊓ blockZ L = blockZ L ⊓ (X ⊓ blockU L) := by
      ext y
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1, hZU h.2⟩, fun h => ⟨h.2.1, h.1⟩⟩
    rw [e1, Subgroup.inf_relIndex_right, ← hUZ]
    exact Subgroup.relIndex_le_of_le_right inf_le_right (by rw [hUZ]; norm_num)
  have s3 : NCAtMost X (X ⊓ blockU L) (X ⊓ pCoreOf 2 L) 0 := by
    refine ncAtMost_zero_of_commutator_le (le_inf ?_ ?_)
    · exact (commutator_le_left_of_le_normalizer hXO).trans inf_le_left
    · exact Subgroup.commutator_mono inf_le_right hXL
  have s4 : NCAtMost X (X ⊓ pCoreOf 2 L) (X ⊓ R) 1 := by
    refine ncAtMost_of_relIndex_lt (lt_of_le_of_lt ?_ (by norm_num : (4 : ℕ) < 4 ^ (1 + 1)))
    have hN : X ⊓ R ≤ Subgroup.normalizer (L : Set G) := fun x hx => hXN x hx.1
    let f : ↥(X ⊓ R) →* L3.Γ := ρ.comp (Subgroup.inclusion hN)
    have hfr : f.range ≤ r := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨hx', hxr⟩ := (mem_pre ρ hLTN).mp x.2.2
      exact hxr
    have hfk : f.ker ≤ (X ⊓ pCoreOf 2 L).subgroupOf (X ⊓ R) := by
      intro x hx
      have hxLT : (x : G) ∈ L ⊔ T := pre_le_sup ρ hLTN r x.2.2
      have h1 := hK x hxLT (hN x.2) hx
      exact ⟨x.2.1, inf_qL_le ⟨hXL x.2.1, h1⟩⟩
    calc (X ⊓ pCoreOf 2 L).relIndex (X ⊓ R)
        ≤ f.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
          (Subgroup.index_dvd_of_le hfk)
      _ = Nat.card f.range := Subgroup.index_ker f
      _ ≤ Nat.card r := Subgroup.card_le_of_le hfr
      _ = 4 := hr4
  have s5 : NCAtMost X (X ⊓ R) X 0 := by
    let ψ : ↥P →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
    have hsign : ∀ x (hx : x ∈ X), Equiv.Perm.sign (ψ ⟨x, hXP hx⟩) = 1 := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        apply sign_eq_one_of_odd
        refine Odd.of_dvd_nat ?_ (orderOf_map_dvd ψ _)
        rw [Subgroup.orderOf_mk]
        exact hy.2
      | one =>
        show Equiv.Perm.sign (ψ 1) = 1
        rw [map_one, map_one]
      | mul y z hy hz ihy ihz =>
        have e1 : (⟨y * z, hXP (Subgroup.mul_mem _ hy hz)⟩ : ↥P) = ⟨y, hXP hy⟩ * ⟨z, hXP hz⟩ :=
          rfl
        rw [e1, map_mul, map_mul, ihy, ihz, mul_one]
      | inv y hy ihy =>
        have e1 : (⟨y⁻¹, hXP (Subgroup.inv_mem _ hy)⟩ : ↥P) = (⟨y, hXP hy⟩ : ↥P)⁻¹ := rfl
        rw [e1, map_inv, map_inv, ihy, inv_one]
    refine ncAtMost_zero_top_of_three ψ hXP (fun x hx => pow_three_of_sign _ (hsign x hx))
      fun x hx h1 => ⟨hx, ?_⟩
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨x, hXP hx⟩ = 1 :=
      (map_eq_one_iff e.toMonoidHom e.injective).mp h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    rw [← hO2]
    exact (Lem3328.mem_pCore_iff _).mp h2
  rw [Chief3323.hasNoncentralTwoChief_iff]
  have h12 := s1.add s2 bot_le (inf_le_inf_left X hZU) inf_le_left hXZ
  have h123 := h12.add s3 bot_le (inf_le_inf_left X hUO) inf_le_left hXU
  have h1234 := h123.add s4 bot_le (inf_le_inf_left X hOR) inf_le_left hXO
  exact h1234.add s5 bot_le inf_le_left le_rfl hXR

theorem rho_qL (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (ρ : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ)
    (hρL : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = γ) :
    ∀ g, g ∈ qL L T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hQLT : qL L T ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  let f : ↥(L ⊔ T) →* L3.Γ := ρ.comp (Subgroup.inclusion hLTN)
  have hf : Function.Surjective f := by
    intro γ
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have hQn : ((qL L T).subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQLT).mpr
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hN := normal_eq_bot (hQn.map f hf)
    (((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).comap_of_injective
      (L ⊔ T).subtype (L ⊔ T).subtype_injective).map f)
  intro g hg hgN
  have h1 : f ⟨g, hQLT hg⟩ ∈ ((qL L T).subgroupOf (L ⊔ T)).map f := ⟨⟨g, hQLT hg⟩, hg, rfl⟩
  rw [hN, Subgroup.mem_bot] at h1
  exact h1

omit [Finite G] in
theorem comm_iff {H : Type} [Group H] (a b : H) : a * b * a⁻¹ * b⁻¹ = 1 ↔ a * b = b * a := by
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem inf_eq_preCenterAut
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (ρ : ↥(Subgroup.normalizer (L : Set G)) →* L3.Γ)
    (hρT : ∀ t (ht : t ∈ T), ρ ⟨t, hTL ht⟩ ∈ bSub)
    (hρL : ∀ γ : L3.Γ, ∃ ℓ, ∃ hℓ : ℓ ∈ L, ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ = γ)
    (hK : ∀ g, g ∈ L ⊔ T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1 →
      g ∈ qL L T)
    (hρQ : ∀ g, g ∈ qL L T → ∀ hgN : g ∈ Subgroup.normalizer (L : Set G), ρ ⟨g, hgN⟩ = 1)
    (hR₁T : pre ρ (sup_le Subgroup.le_normalizer hTL) rSub ≤ T) :
    pre ρ (sup_le Subgroup.le_normalizer hTL) rSub ⊓
        pre ρ (sup_le Subgroup.le_normalizer hTL) (L3.bsSub P12) =
      preCenterAut T (vPlus L T) := by
  set hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hCQ : T ⊓ Subgroup.centralizer (vPlus L T : Set G) = qL L T :=
    (h.centralizer_vPlus h38 h39).2.1
  have hTidx : ¬ 2 ∣ T.index := h.sylow.2
  have hH : Function.Surjective (ρ.comp (Subgroup.inclusion hLTN)) := by
    intro γ
    obtain ⟨ℓ, hℓ, e⟩ := hρL γ
    exact ⟨⟨ℓ, Subgroup.mem_sup_left hℓ⟩, e⟩
  have hcommρ : ∀ x (hx : x ∈ T) s (hs : s ∈ T),
      conjAct (vPlus L T) ⟨x, hTV hx⟩ * conjAct (vPlus L T) ⟨s, hTV hs⟩ =
        conjAct (vPlus L T) ⟨s, hTV hs⟩ * conjAct (vPlus L T) ⟨x, hTV hx⟩ ↔
      ρ ⟨x, hTL hx⟩ * ρ ⟨s, hTL hs⟩ = ρ ⟨s, hTL hs⟩ * ρ ⟨x, hTL hx⟩ := by
    intro x hx s hs
    have hc : x * s * x⁻¹ * s⁻¹ ∈ T := T.mul_mem (T.mul_mem (T.mul_mem hx hs) (T.inv_mem hx))
      (T.inv_mem hs)
    have eV : (⟨x * s * x⁻¹ * s⁻¹, hTV hc⟩ : ↥(Subgroup.normalizer (vPlus L T : Set G))) =
        ⟨x, hTV hx⟩ * ⟨s, hTV hs⟩ * (⟨x, hTV hx⟩)⁻¹ * (⟨s, hTV hs⟩)⁻¹ := rfl
    have eL : (⟨x * s * x⁻¹ * s⁻¹, hTL hc⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨x, hTL hx⟩ * ⟨s, hTL hs⟩ * (⟨x, hTL hx⟩)⁻¹ * (⟨s, hTL hs⟩)⁻¹ := rfl
    have key : x * s * x⁻¹ * s⁻¹ ∈ Subgroup.centralizer (vPlus L T : Set G) ↔
        ρ ⟨x * s * x⁻¹ * s⁻¹, hTL hc⟩ = 1 := by
      constructor
      · intro hC
        exact hρQ _ (hCQ ▸ ⟨hc, hC⟩) _
      · intro h1
        exact hQC (hK _ (Subgroup.mem_sup_right hc) _ h1)
    have hV : x * s * x⁻¹ * s⁻¹ ∈ Subgroup.centralizer (vPlus L T : Set G) ↔
        conjAct (vPlus L T) ⟨x * s * x⁻¹ * s⁻¹, hTV hc⟩ = 1 := by
      constructor
      · exact InternalSec.conjAct_eq_one_of_mem_centralizer ⟨_, hTV hc⟩
      · exact Lem3328.mem_centralizer_of_conjAct_eq_one ⟨_, hTV hc⟩
    rw [eL, map_mul, map_mul, map_mul, map_inv, map_inv, comm_iff] at key
    rw [eV, map_mul, map_mul, map_mul, map_inv, map_inv, comm_iff] at hV
    exact hV.symm.trans key
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨hxLT, hρ1⟩ := (mem_pre ρ hLTN).mp hx1
    obtain ⟨hxLT', hρ2⟩ := (mem_pre ρ hLTN).mp hx2
    have hxT : x ∈ T := hR₁T hx1
    rw [Lem3328.mem_preCenterAut]
    refine ⟨hxT, hTV hxT, ⟨conjAct (vPlus L T) ⟨x, hTV hxT⟩, ⟨x, hTV hxT⟩, hxT, rfl⟩, ?_, rfl⟩
    show _ ∈ Subgroup.center ↥(autOn T (vPlus L T))
    rw [Subgroup.mem_center_iff]
    rintro ⟨y, s, hs, rfl⟩
    apply Subtype.ext
    have hsT : (s : G) ∈ T := hs
    have h1 := (hcommρ x hxT s hsT).mpr (center_check₁ _ hρ1 hρ2 _
      (mem_bSub.mp (hρT s hsT)))
    exact h1.symm
  · intro hx
    obtain ⟨hxT, hxN, z, hz, hzx⟩ := Lem3328.mem_preCenterAut.mp hx
    have hxB : ρ ⟨x, hTL hxT⟩ ∈ bSub := hρT x hxT
    have hcen : ∀ g ∈ bSet, ρ ⟨x, hTL hxT⟩ * g = g * ρ ⟨x, hTL hxT⟩ := by
      intro g hg
      obtain ⟨s, hs, rfl⟩ := mem_image_bSub ρ hLTN hTidx hρT hH (mem_bSet.mp hg)
      refine (hcommρ x hxT s hs).mp ?_
      have h1 := Subgroup.mem_center_iff.mp hz ⟨conjAct (vPlus L T) ⟨s, hTV hs⟩,
        ⟨s, hTV hs⟩, hs, rfl⟩
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at h2
      have hzx' : (z : MulAut ↥(vPlus L T)) = conjAct (vPlus L T) ⟨x, hTV hxT⟩ := hzx
      rw [hzx'] at h2
      exact h2.symm
    obtain ⟨hr1, hr2⟩ := center_check₂ _ (mem_bSet.mpr hxB) hcen
    exact ⟨(mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_right hxT, hr1⟩,
      (mem_pre ρ hLTN).mpr ⟨Subgroup.mem_sup_right hxT, hr2⟩⟩

theorem case1
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    {α₂ : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2))} (hα₂ : IsModO2Surj L α₂)
    (hi : IsC134Case1 (L ⊔ T) T L) :
    IsLnBlock L 3 ∧ ∃ X₁ X₂ : Subgroup G,
      (oTwoUpper X₁ = X₁ ∧ T ≤ Subgroup.normalizer (X₁ : Set G) ∧
        Nonempty (↥(X₁ ⊔ T) ⧸ CFSG.pCore 2 ↥(X₁ ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ HasNoncentralTwoChief X₁ 3) ∧
      (oTwoUpper X₂ = X₂ ∧ T ≤ Subgroup.normalizer (X₂ : Set G) ∧
        Nonempty (↥(X₂ ⊔ T) ⧸ CFSG.pCore 2 ↥(X₂ ⊔ T) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ HasNoncentralTwoChief X₂ 3) ∧
      pCoreOf 2 (X₁ ⊔ T) ⊓ pCoreOf 2 (X₂ ⊔ T) = preCenterAut T (vPlus L T) := by
  have hLn := isLnBlock_of_isSL3Block hi.1 hα₂
  obtain ⟨ρ, hρT, hρL, hK, -⟩ := exists_rho_cZ h38 h39 h hLn hTL
  have hρQ := rho_qL hTL ρ hρL
  obtain ⟨hX₁, hTX₁, hS₁, hN₁, hO₁, hR₁⟩ := parabolic3 h hTL hLn ρ hρT hρL hK hρQ bSub_le_ptSub
    rSub_le_ptSub ptSub_le_normalizer (fun x hx => sq_eq_one_of_mem_rSub hx) card_ptSub card_rSub
    aW_mem bW_mem comm_not_mem
  obtain ⟨hX₂, hTX₂, hS₂, hN₂, hO₂, -⟩ := parabolic3 h hTL hLn ρ hρT hρL hK hρQ
    (inf_le_right : bSub ≤ L3.stabSub P12) (bsSub_le_stabSub P12) (stabSub_le_normalizer P12)
    (fun x hx => sq_bsSub x hx) (L3.card_stabSub isPlane_P12) (L3.card_bsSub isPlane_P12)
    aW₂_mem bW₂_mem comm_not_mem₂
  refine ⟨hLn, _, _, ⟨hX₁, hTX₁, hS₁, hN₁⟩, ⟨hX₂, hTX₂, hS₂, hN₂⟩, ?_⟩
  rw [hO₁, hO₂]
  exact inf_eq_preCenterAut h h38 h39 hTL ρ hρT hρL hK hρQ hR₁

end One3323

end CFSG.Quasithin.H13
