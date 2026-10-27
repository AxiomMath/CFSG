module

public import CFSG.Quasithin.H13.A6S4L1
public import CFSG.Quasithin.Background.C2Six
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.H13.A6S4L0

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.C2Six
open scoped commutatorElement

namespace A6O2F

variable {G : Type} [Group G] [Finite G]

theorem mem_pCoreOf_of_mem_oTwoFIn {H : Subgroup G} {y : G} (hy : y ∈ oTwoFIn H) {n : ℕ}
    (hyn : y ^ 2 ^ n = 1) : y ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hyH, hF⟩ := mem_oTwoFIn.mp hy
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hFdef
  set yF : ↥F := ⟨QuotientGroup.mk (⟨y, hyH⟩ : ↥H), hF⟩ with hyF
  have hyF2 : yF ^ 2 ^ n = 1 := by
    apply Subtype.ext
    show (QuotientGroup.mk (⟨y, hyH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 2 ^ n = 1
    rw [← QuotientGroup.mk_pow]
    have : (⟨y, hyH⟩ : ↥H) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hyn)
    rw [this, QuotientGroup.mk_one]
  have hP : IsPGroup 2 (Subgroup.zpowers yF) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨n, Subtype.ext ?_⟩
    show (yF ^ m) ^ 2 ^ n = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyF2, one_zpow]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have hmem : (yF : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ (Q : Subgroup ↥F).map F.subtype :=
    ⟨yF, hQ (Subgroup.mem_zpowers yF), rfl⟩
  have h1 := Sylow.map_le_pCore (inferInstance : F.Normal) inferInstance 2 Q hmem
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot, Subgroup.mem_bot] at h1
  have h2 : (⟨y, hyH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
  exact mem_pCore_two_iff.mp h2

theorem mem_sup_of_decomp {X Q Y : Subgroup G} {y : G} (hy : y ∈ Y)
    (hodd : ∀ x ∈ Y, ∀ m : ℕ, Odd m → x ^ m = 1 → x ∈ X)
    (h2 : ∀ x ∈ Y, ∀ n : ℕ, x ^ 2 ^ n = 1 → x ∈ Q) : y ∈ X ⊔ Q := by
  obtain ⟨a, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hcop : Nat.Coprime (2 ^ a) m :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ a) m
  rw [hcop] at hb
  set u := Nat.gcdA (2 ^ a) m
  set v := Nat.gcdB (2 ^ a) m
  have hord : y ^ ((2 ^ a * m : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast, ← hnm, pow_orderOf_eq_one]
  have hy1 : y = y ^ (((2 ^ a : ℕ) : ℤ) * u) * y ^ ((m : ℤ) * v) := by
    rw [← zpow_add, ← hb]
    simp
  have hx1 : (y ^ (((2 ^ a : ℕ) : ℤ) * u)) ^ m = 1 := by
    rw [← zpow_natCast, ← zpow_mul, show ((2 ^ a : ℕ) : ℤ) * u * m = ((2 ^ a * m : ℕ) : ℤ) * u by
      push_cast; ring, zpow_mul, hord, one_zpow]
  have hx2 : (y ^ ((m : ℤ) * v)) ^ 2 ^ a = 1 := by
    rw [← zpow_natCast, ← zpow_mul, show (m : ℤ) * v * ((2 ^ a : ℕ) : ℤ) =
      ((2 ^ a * m : ℕ) : ℤ) * v by push_cast; ring, zpow_mul, hord, one_zpow]
  rw [hy1]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (hodd _ (Subgroup.zpow_mem _ hy _) m hm hx1))
    (Subgroup.mem_sup_right (h2 _ (Subgroup.zpow_mem _ hy _) a hx2))

omit [Finite G] in
theorem mem_of_mk_mem {H A : Subgroup G} (hQA : pCoreOf 2 H ≤ A) {x : ↥H}
    (hx : (QuotientGroup.mk x : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
      (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) : (x : G) ∈ A := by
  obtain ⟨a, ha, hax⟩ := hx
  have h1 : a⁻¹ * x ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [QuotientGroup.mk'_apply] at hax
    rw [hax, inv_mul_cancel]
  have h2 : ((a⁻¹ * x : ↥H) : G) ∈ A := hQA (mem_pCore_two_iff.mp h1)
  have e : (x : G) = (a : G) * ((a⁻¹ * x : ↥H) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact A.mul_mem ha h2

theorem exists_mem_normalizer {H A : Subgroup G} (hQA : pCoreOf 2 H ≤ A)
    (hAE : A < oTwoFIn H) :
    ∃ y ∈ oTwoFIn H, y ∉ A ∧ y ∈ Subgroup.normalizer (A : Set G) := by
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hFdef
  set Ab : Subgroup ↥F := ((A.subgroupOf H).map π).subgroupOf F with hAb
  have hAH : A ≤ H := hAE.le.trans oTwoFIn_le
  have hAbtop : Ab ≠ ⊤ := by
    intro htop
    apply (lt_iff_le_not_ge.mp hAE).2
    intro e he
    obtain ⟨heH, heF⟩ := mem_oTwoFIn.mp he
    have h1 : (⟨π ⟨e, heH⟩, heF⟩ : ↥F) ∈ Ab := by rw [htop]; exact Subgroup.mem_top _
    exact mem_of_mk_mem hQA (x := ⟨e, heH⟩) h1
  obtain ⟨f, hfN, hfA⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent Ab (lt_top_iff_ne_top.mpr hAbtop))
  obtain ⟨⟨y, hyH⟩, hyf⟩ := QuotientGroup.mk_surjective (f : ↥H ⧸ CFSG.pCore 2 ↥H)
  have hyF : π ⟨y, hyH⟩ ∈ F := by rw [hπ, QuotientGroup.mk'_apply, hyf]; exact f.2
  have hfe : f = ⟨π ⟨y, hyH⟩, hyF⟩ := by
    apply Subtype.ext
    show (f : ↥H ⧸ CFSG.pCore 2 ↥H) = π ⟨y, hyH⟩
    rw [hπ, QuotientGroup.mk'_apply, hyf]
  have haF : ∀ a (ha : a ∈ A), π ⟨a, hAH ha⟩ ∈ F := fun a ha =>
    (mem_oTwoFIn.mp (hAE.le ha)).2
  have haAb : ∀ a (ha : a ∈ A), (⟨π ⟨a, hAH ha⟩, haF a ha⟩ : ↥F) ∈ Ab := fun a ha =>
    ⟨⟨a, hAH ha⟩, ha, rfl⟩
  have hconj : ∀ g : ↥F, g ∈ Subgroup.normalizer (Ab : Set ↥F) → ∀ x : ↥H, π x = g → ∀ a ∈ A,
      (x : G) * a * (x : G)⁻¹ ∈ A := by
    intro g hg x hxg a ha
    have h1 := (Subgroup.mem_normalizer_iff.mp hg _).mp (haAb a ha)
    have e : (g * ⟨π ⟨a, hAH ha⟩, haF a ha⟩ * g⁻¹ : ↥F) =
        ⟨π (x * ⟨a, hAH ha⟩ * x⁻¹), by
          rw [map_mul, map_mul, map_inv, hxg]
          exact F.mul_mem (F.mul_mem g.2 (haF a ha)) (F.inv_mem g.2)⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hxg]
    rw [e] at h1
    have h2 : (QuotientGroup.mk (x * (⟨a, hAH ha⟩ : ↥H) * x⁻¹) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈
        (A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) :=
      Subgroup.mem_subgroupOf.mp h1
    exact mem_of_mk_mem hQA h2
  have hfN' : f⁻¹ ∈ Subgroup.normalizer (Ab : Set ↥F) := Subgroup.inv_mem _ hfN
  have hy1 := hconj f hfN ⟨y, hyH⟩ (by rw [hfe])
  have hy2 := hconj f⁻¹ hfN' ⟨y, hyH⟩⁻¹ (by rw [map_inv, hfe]; rfl)
  refine ⟨y, mem_oTwoFIn.mpr ⟨hyH, hyF⟩, fun hyA => hfA ?_, ?_⟩
  · rw [hfe]
    exact ⟨⟨y, hyH⟩, hyA, rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hy1 a
    · intro ha
      have := hy2 _ ha
      simp only [Subgroup.coe_inv, inv_inv] at this
      have e : y⁻¹ * (y * a * y⁻¹) * y = a := by group
      rwa [e] at this

omit [Finite G] in
theorem perfect_conjClosure {K X : Subgroup G} (hK : ⁅K, K⁆ = K) :
    ⁅conjClosure K X, conjClosure K X⁆ = conjClosure K X := by
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
    (conjClosure_le fun h hh k hk => ?_)
  · rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
      (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)
  · set Kh := K.map (MulAut.conj h).toMonoidHom with hKh_def
    have hKh : Kh ≤ conjClosure K X := by
      rintro _ ⟨k', hk', rfl⟩
      exact mem_conjClosure hh hk'
    have hperf : ⁅Kh, Kh⁆ = Kh := by rw [hKh_def, ← Subgroup.map_commutator, hK]
    have hmem : h * k * h⁻¹ ∈ Kh := ⟨k, hk, rfl⟩
    rw [← hperf] at hmem
    exact Subgroup.commutator_mono hKh hKh hmem

@[expose] def A4L : List (Perm (Fin 6)) :=
  K4L ++ K4L.map (fun σ => swap 0 1 * swap 1 2 * σ) ++
    K4L.map (fun σ => swap 0 1 * swap 1 2 * (swap 0 1 * swap 1 2) * σ)

theorem mem_A4L : ∀ σ : Perm (Fin 6), σ 4 = 4 → σ 5 = 5 → Perm.sign σ = 1 → σ ∈ A4L := by
  decide +kernel

theorem A4L_comm : ∀ σ ∈ A4L, ∀ τ ∈ A4L, σ * τ * σ⁻¹ * τ⁻¹ ∈ K4L := by
  decide +kernel

theorem K4L_comm : ∀ σ ∈ K4L, ∀ τ ∈ K4L, σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
  decide +kernel

omit [Finite G] in
theorem perfect_le_ker_of_A4 {N Y : Subgroup G} (hY : ⁅Y, Y⁆ = Y) (hYN : Y ≤ N)
    (f : ↥N →* Perm (Fin 6))
    (hf : ∀ y (hy : y ∈ Y), f ⟨y, hYN hy⟩ 4 = 4 ∧ f ⟨y, hYN hy⟩ 5 = 5 ∧
      Perm.sign (f ⟨y, hYN hy⟩) = 1) :
    ∀ y (hy : y ∈ Y), f ⟨y, hYN hy⟩ = 1 := by
  have hfA : ∀ y (hy : y ∈ Y), f ⟨y, hYN hy⟩ ∈ A4L := fun y hy =>
    mem_A4L _ (hf y hy).1 (hf y hy).2.1 (hf y hy).2.2
  have hmemY : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ∈ Y := fun a ha b hb => by
    rw [← hY]
    exact Subgroup.commutator_mem_commutator ha hb
  have hcY : ∀ a (ha : a ∈ Y) b (hb : b ∈ Y),
      f ⟨⁅a, b⁆, hYN (hmemY a ha b hb)⟩ =
        f ⟨a, hYN ha⟩ * f ⟨b, hYN hb⟩ * (f ⟨a, hYN ha⟩)⁻¹ * (f ⟨b, hYN hb⟩)⁻¹ := by
    intro a ha b hb
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  let Y1 : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ N, f ⟨x, hx⟩ ∈ K4L}
      mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨N.mul_mem ha hb, by
        have e : f ⟨a * b, N.mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := by
          rw [← map_mul]; rfl
        rw [e]
        exact K4L_mul _ ha' _ hb'⟩
      one_mem' := ⟨N.one_mem, by
        have e : f ⟨1, N.one_mem⟩ = 1 := by rw [← map_one f]; rfl
        rw [e]
        exact List.mem_cons_self⟩
      inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨N.inv_mem ha, by
        have e : f ⟨a⁻¹, N.inv_mem ha⟩ = (f ⟨a, ha⟩)⁻¹ := by rw [← map_inv]; rfl
        rw [e]
        exact K4L_inv _ ha'⟩ }
  have h1 : Y ≤ Y1 := by
    rw [← hY, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨hYN (hmemY a ha b hb), ?_⟩
    rw [hcY a ha b hb]
    exact A4L_comm _ (hfA a ha) _ (hfA b hb)
  let Y2 : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ N, f ⟨x, hx⟩ = 1}
      mul_mem' := fun {a b} ⟨ha, ha'⟩ ⟨hb, hb'⟩ => ⟨N.mul_mem ha hb, by
        have e : f ⟨a * b, N.mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := by
          rw [← map_mul]; rfl
        rw [e, ha', hb', mul_one]⟩
      one_mem' := ⟨N.one_mem, by rw [← map_one f]; rfl⟩
      inv_mem' := fun {a} ⟨ha, ha'⟩ => ⟨N.inv_mem ha, by
        have e : f ⟨a⁻¹, N.inv_mem ha⟩ = (f ⟨a, ha⟩)⁻¹ := by rw [← map_inv]; rfl
        rw [e, ha', inv_one]⟩ }
  have h2 : Y ≤ Y2 := by
    rw [← hY, Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨hYN (hmemY a ha b hb), ?_⟩
    rw [hcY a ha b hb]
    obtain ⟨_, ha1⟩ := h1 ha
    obtain ⟨_, hb1⟩ := h1 hb
    exact K4L_comm _ ha1 _ hb1
  intro y hy
  obtain ⟨_, hy2⟩ := h2 hy
  exact hy2

theorem eq_bot_of_perfect_le {A P : Subgroup G} (hA : Group.IsSolvable ↥A) (hP : ⁅P, P⁆ = P)
    (hPA : P ≤ A) : P = ⊥ := by
  have : Group.IsSolvable ↥P :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hPA)
      (Subgroup.inclusion_injective hPA)
  rw [← perfectCore_eq_self_of_perfect hP]
  exact (isSolvable_iff_perfectCore_eq_bot P).mp this

end A6O2F

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem nonempty_alt6_of_not_hat (hhat : ¬ IsHatA6 L) :
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e⟩ := S.centralQuot
  have hc := S.center_Q_eq_bot hhat
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc.symm).trans e)⟩

theorem pCoreOf_ne_bot_of_le_G1 {H' : Subgroup G} (hV1 : fsuV1 T V ≤ H') (hH' : H' ≤ S.G1) :
    pCoreOf 2 H' ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h0
  have hV1Q : fsuV1 T V ≤ pCoreOf 2 H' :=
    le_pCoreOf_of_le_normalizer 2 hV1
      (hH'.trans (S.G1_le_centralizer_V1.trans (Subgroup.centralizer_le_normalizer _)))
      (IsPGroup.of_card (n := 1) (by rw [S.card_V1]; norm_num))
  rw [h0, le_bot_iff] at hV1Q
  have := S.card_V1
  rw [hV1Q] at this
  simp at this

theorem lem13812_two (h139 : Stmt13_3_9) {H : Subgroup G}
    (hH : H ∈ S.Hz) :
    oTwoRes (oTwoFIn H ⊓ Subgroup.normalizer (L : Set G)) = ⊥ ∨
      (¬ IsHatA6 L ∧ oTwoRes (oTwoFIn H ⊓ Subgroup.normalizer (L : Set G)) = S.L1) ∨
      (IsHatA6 L ∧ oTwoRes (oTwoFIn H ⊓ Subgroup.normalizer (L : Set G)) = l1plus T L V) := by
  set M := Subgroup.normalizer (L : Set G) with hM
  set E := oTwoFIn H with hE
  set X := oTwoRes (E ⊓ M) with hX
  set Q := pCoreOf 2 H with hQ
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHG : H ≤ S.G1 := hH.2.1
  have hHM : ¬ H ≤ M := hH.2.2
  have hQT : Q ≤ T := pCoreOf_le_of_sylow S.h13.sylow hTH
  have hTM : T ≤ M := S.T_le_NL
  have hQE : Q ≤ E := pCoreOf_le_oTwoFIn
  have hEH : E ≤ H := oTwoFIn_le
  have hHE : H ≤ Subgroup.normalizer (E : Set G) := le_normalizer_oTwoFIn
  have hV1T : fsuV1 T V ≤ T := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V).trans S.V_le_T
  have hEMeq : E ⊓ M = X ⊔ Q := by
    apply le_antisymm
    · intro y hy
      exact A6O2F.mem_sup_of_decomp hy
        (fun x hx m hm hxm => Subgroup.subset_closure ⟨hx, m, hm, hxm⟩)
        (fun x hx n hxn => A6O2F.mem_pCoreOf_of_mem_oTwoFIn hx.1 hxn)
    · exact sup_le (oTwoRes_le _) (le_inf hQE (hQT.trans hTM))
  have hXN : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((X ⊔ Q : Subgroup G) : Set G) →
      K ≤ Subgroup.normalizer (X : Set G) := by
    intro K hK
    have := A5.le_normalizer_oTwoRes_of_le_normalizer hK
    rwa [← hEMeq] at this
  have hNX : ∀ g ∈ Subgroup.normalizer (E : Set G), g ∈ M →
      g ∈ Subgroup.normalizer (X : Set G) := by
    intro g hgE hgM
    refine hXN (Subgroup.zpowers g) ?_ (Subgroup.mem_zpowers g)
    rw [Subgroup.zpowers_le, ← hEMeq, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyE, hyM⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgE y).mp hyE,
        M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM)⟩
    · rintro ⟨hyE, hyM⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp hgE y).mpr hyE, ?_⟩
      have := M.mul_mem (M.mul_mem (M.inv_mem hgM) hyM) hgM
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rwa [e] at this
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht => hNX t (hHE (hTH ht)) (hTM ht)
  have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
  have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
    intro h
    have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
    rw [S.zv, Subgroup.mem_bot] at h1
    exact S.z_ne_one h1
  have hXz : X ≤ M ⊓ Subgroup.centralizer ({S.z} : Set G) :=
    le_inf ((oTwoRes_le _).trans inf_le_right)
      ((oTwoRes_le _).trans (inf_le_left.trans (hEH.trans hHG)))
  have hXX : oTwoRes X = X := by
    refine le_antisymm (oTwoRes_le _) ?_
    rw [hX, oTwoRes, Subgroup.closure_le]
    rintro y ⟨hy, m, hm, hym⟩
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨hy, m, hm, hym⟩, m, hm, hym⟩
  have key : ∀ H' : Subgroup G, T ≤ H' → H' ≤ S.G1 → ¬ H' ≤ M → X ≤ H' →
      H' ≤ Subgroup.normalizer (X : Set G) →
      X = ⊥ ∨ (¬ IsHatA6 L ∧ X = S.L1) ∨ (IsHatA6 L ∧ X = l1plus T L V) := by
    intro H' hTH' hH'G hH'M hXH' hH'X
    have hInH : InH T H' := ⟨hTH', S.pCoreOf_ne_bot_of_le_G1 (hV1T.trans hTH') hH'G⟩
    rcases h139 G T L V H' X S.z S.h13 S.irr S.a6 hInH hH'M hXX hXH' hH'X hz hzL hXz with
      h | ⟨-, hA6, hhat⟩
    · exact Or.inl h
    · by_cases hh : IsHatA6 L
      · exact Or.inr (Or.inr ⟨hh, hhat hh⟩)
      · exact Or.inr (Or.inl ⟨hh, hA6 (S.nonempty_alt6_of_not_hat hh)⟩)
  by_cases hEM : E ≤ M
  ·
    have hXE : X = oTwoRes E := by rw [hX, inf_eq_left.mpr hEM]
    refine key H hTH hHG hHM ((oTwoRes_le _).trans (inf_le_left.trans hEH)) ?_
    rw [hXE]
    exact A5.le_normalizer_oTwoRes_of_le_normalizer hHE
  ·
    have hXQE : X ⊔ Q ≤ E := by rw [← hEMeq]; exact inf_le_left
    have hXQM : X ⊔ Q ≤ M := by rw [← hEMeq]; exact inf_le_right
    have hlt : X ⊔ Q < E := lt_of_le_of_ne hXQE fun h => hEM (h ▸ hXQM)
    obtain ⟨y, hyE, hyXQ, hyN⟩ := A6O2F.exists_mem_normalizer le_sup_right hlt
    have hyM : y ∉ M := fun h => hyXQ (by rw [← hEMeq]; exact ⟨hyE, h⟩)
    have hyX : y ∈ Subgroup.normalizer (X : Set G) :=
      hXN (Subgroup.zpowers y) (Subgroup.zpowers_le.mpr hyN) (Subgroup.mem_zpowers y)
    have hXG : X ≤ S.G1 := (oTwoRes_le _).trans (inf_le_left.trans (hEH.trans hHG))
    refine key ((Subgroup.zpowers y ⊔ X) ⊔ T) le_sup_right
      (sup_le (sup_le (Subgroup.zpowers_le.mpr (hHG (hEH hyE))) hXG) (hTH.trans hHG))
      (fun h => hyM (h (Subgroup.mem_sup_left (Subgroup.mem_sup_left
        (Subgroup.mem_zpowers y))))) (le_sup_right.trans le_sup_left)
      (sup_le (sup_le (Subgroup.zpowers_le.mpr hyX) Subgroup.le_normalizer) hTX)

theorem lem13812_one (h139 : Stmt13_3_9) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G} (hK : K ∈ cComp H) :
    ¬ K ≤ Subgroup.normalizer (L : Set G) ∧ (K ⊔ T) ⊔ S.L1 ∈ S.Hz := by
  set M := Subgroup.normalizer (L : Set G) with hM
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hHG : H ≤ S.G1 := hH.2.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTM : T ≤ M := S.T_le_NL
  have hV1T : fsuV1 T V ≤ T := ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V).trans S.V_le_T
  have hKM : ¬ K ≤ M := by
    intro hKM
    set Y := conjClosure K T with hY
    have hYH : H ≤ Subgroup.normalizer (Y : Set G) :=
      normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
        hH.1.2 (isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH) hK
    have hYle : Y ≤ H := conjClosure_le fun t ht k hk =>
      H.mul_mem (H.mul_mem (hTH ht) (hKH hk)) (H.inv_mem (hTH ht))
    have hYM : Y ≤ M := conjClosure_le fun t ht k hk =>
      M.mul_mem (M.mul_mem (hTM ht) (hKM hk)) (M.inv_mem (hTM ht))
    have hYperf : ⁅Y, Y⁆ = Y := A6O2F.perfect_conjClosure (perfect_of_mem_cComp hK)
    have hYres : oTwoRes Y = Y := by
      rw [oTwoRes_eq_oTwoUpper]
      exact (eq_oTwoUpper_of_perfect hYperf).symm
    have hz : S.z ∈ fsuV1 T V := S.mem_V1_iff.2 (Or.inr rfl)
    have hzL : S.z ∉ Subgroup.centralizer (L : Set G) := by
      intro h
      have h1 : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h⟩
      rw [S.zv, Subgroup.mem_bot] at h1
      exact S.z_ne_one h1
    have hInH : InH T H := ⟨hTH, hH.1.2⟩
    have hKne : K ≠ ⊥ := ne_bot_of_mem_cComp hK
    have hKY : K ≤ Y := le_conjClosure K T
    rcases h139 G T L V H Y S.z S.h13 S.irr S.a6 hInH hH.2.2 hYres hYle hYH hz hzL
      (le_inf hYM (hYle.trans hHG)) with hY0 | ⟨-, hA6, hhat⟩
    · exact hKne (le_bot_iff.mp (hY0 ▸ hKY))
    have hYL1 : Y ≤ S.L1 := by
      by_cases hh : IsHatA6 L
      · rw [hhat hh]
        refine (oTwoRes_le _).trans (Subgroup.commutator_le.mpr fun a ha b hb => ?_)
        rw [commutatorElement_def]
        have h1 := (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hb.1) _).mp
          (S.L1.inv_mem ha)
        have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
        rw [e]
        exact S.L1.mul_mem ha h1
      · rw [hA6 (S.nonempty_alt6_of_not_hat hh)]
        exact le_rfl
    have hYN : Y ≤ Subgroup.normalizer (V : Set G) := hYL1.trans (S.L1_le_L.trans S.frame.L_le)
    have hYC := A6O2F.perfect_le_ker_of_A4 hYperf hYN S.frame.ρ fun y hy =>
      S.rho_L1 (g := ⟨y, hYN hy⟩) (hYL1 hy)
    have hYZ : Y ≤ o2Z L := fun y hy =>
      S.centralizer_le_o2Z ⟨S.L1_le_L (hYL1 hy), (S.rho_eq_one_iff _).1 (hYC y hy)⟩
    have hYO : Y ≤ pCoreOf 2 L := by
      rw [← hYperf, Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨-, hab⟩ := mem_o2Z_iff.1 (hYZ ha)
      rw [commutatorElement_def]
      exact hab b (S.L1_le_L (hYL1 hb))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable ↥(pCoreOf 2 L) := by
      have := (pCoreOf_isPGroup 2 L).isNilpotent
      infer_instance
    exact hKne (le_bot_iff.mp ((A6O2F.eq_bot_of_perfect_le hsolv hYperf hYO) ▸ hKY))
  have hXG : (K ⊔ T) ⊔ S.L1 ≤ S.G1 :=
    sup_le (sup_le (hKH.trans hHG) (hTH.trans hHG)) (le_sup_left.trans (hH.1.1.trans hHG))
  refine ⟨hKM, ⟨sup_le le_sup_right (le_sup_right.trans le_sup_left),
    S.pCoreOf_ne_bot_of_le_G1 (hV1T.trans (le_sup_right.trans le_sup_left)) hXG⟩, hXG,
    fun h => hKM ((le_sup_left.trans le_sup_left).trans h)⟩

end Setting4

end CFSG.Quasithin.H13.A6
