module

public import CFSG.Quasithin.EmptyFaithful.FLc4ZDiag
public import CFSG.Quasithin.Background.FLc5Restrict
public import CFSG.Quasithin.Background.C2PushThree
public import CFSG.Quasithin.Background.FLcP0Ker

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_conjClosure_of_le5 {Z H X : Subgroup G}
    (hZ : X ≤ Subgroup.normalizer (Z : Set G)) (hH : X ≤ Subgroup.normalizer (H : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ conjClosure Z H, x * y * x⁻¹ ∈ conjClosure Z H := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨h, hh, z, hz, rfl⟩ := hy
      have h1 : x * h * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hH hx) h).mp hh
      have h2 : x * z * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ hx) z).mp hz
      have := mem_conjClosure h1 h2
      simpa [mul_assoc] using this
    | one => simp
    | mul y y' _ _ ihy ihy' => simpa [mul_assoc] using (conjClosure Z H).mul_mem ihy ihy'
    | inv y _ ih => simpa [mul_assoc] using (conjClosure Z H).inv_mem ih
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this

omit [Finite G] in
theorem isPGroup_two_of_sq {X : Subgroup G} (h : ∀ x ∈ X, x ^ 2 = 1) : IsPGroup 2 ↥X := fun x =>
  ⟨1, by simpa using Subtype.ext (h x x.2)⟩

theorem z2_le_q1 {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (hc : Ctx15128 T Mc M Z₁ Z₂ V₁ V₂ L) :
    Z₂ ≤ q1_1516 Mc Z₁ := by
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hM := hc.ctx.mf
  have hsmall : Ce15Small T Mc M := ce15Small_of_four_or_six hc.h24.one
  have hn7 : ¬ Ce15Seven T Mc M := not_seven_of_four_or_six hc.h24.one
  have hTM : T ≤ M := hM.1.1.2
  have hidx := hS.index_two hsmall hn7
  have hswap := hS.swap_small hsmall hn7
  obtain ⟨-, hZ₁V₁, -, hV₁₂inf⟩ := hS.decomp_other hn7
  have hZ₂V₂ := hS.z2_le_v2 hn7
  have hVab := hS.V_isElemAbelian hq hM
  have hcomm : ∀ a ∈ Z₁, ∀ b ∈ Z₂, a * b = b * a := by
    intro a ha b hb
    have := hVab.1
    exact setLike_mul_comm (hS.z1_le_V ha) (hS.z2_le_V hb)
  have hZ₁M : Z₁ ≤ mZ1516 Mc Z₁ :=
    le_inf (hS.z1_le_g1 hq hM) ((hS.z1_le_T hq hM).trans hq.t_le_mc)
  have hZ₁N : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (Z₁ : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ hx.1
  have hZ₁Q : Z₁ ≤ q1_1516 Mc Z₁ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZ₁M hZ₁N
      (isPGroup_two_of_sq (hS.z1_isElemAbelian hq hM).2)
  obtain ⟨t, htT, htS⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hcon
    push Not at hcon
    have h1 : (s1516 T Z₁).relIndex T = 1 := Subgroup.relIndex_eq_one.2 hcon
    omega
  have hsw := hswap t htT htS
  intro y hy
  have hyV₂ : y ∈ V₂ := hZ₂V₂ hy
  have h1 : t * y * t⁻¹ ∈ V₁ := by
    have : t * y * t⁻¹ ∈ conjByElt t V₂ := by
      rw [mem_conjByElt]
      have e : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      rw [e]
      exact hyV₂
    rwa [hsw] at this
  have h2 : t * y * t⁻¹ ∈ Z₁ ⊔ Z₂ := by
    rw [hS.vE_sup_small hsmall]
    exact conj_mem_vE1516 hTM htT (hS.z2_le hy)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_comm4 hcomm h2
  have hbV₂ : b ∈ V₂ := hZ₂V₂ hb
  have hbV₁ : b ∈ V₁ := by
    have h3 : b = a⁻¹ * (t * y * t⁻¹) := by rw [hab]; group
    rw [h3]
    exact V₁.mul_mem (V₁.inv_mem (hZ₁V₁ ha)) h1
  have hb1 : b = 1 := by
    have : b ∈ V₁ ⊓ V₂ := ⟨hbV₁, hbV₂⟩
    rw [hV₁₂inf] at this
    exact Subgroup.mem_bot.1 this
  have hyZ₁ : t * y * t⁻¹ ∈ Z₁ := by
    rw [hab, hb1, mul_one]
    exact ha
  have hTQ := hc.h18.three
  have h4 := (Subgroup.mem_normalizer_iff.1 (hTQ (T.inv_mem htT)) (t * y * t⁻¹)).1 (hZ₁Q hyZ₁)
  simpa [mul_assoc] using h4

theorem rho_of_alt {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ w : V, w ^ 2 = 1)
    {Ls : Subgroup (MulAut V)} {UL' : Subgroup V} (h : Alt15127 Ls UL') :
    ∃ (n : ℕ) (ρ : FLc.SLt n →* MulAut V), 3 ≤ n ∧ (∀ g, ρ g ∈ Ls) ∧ (∀ k ∈ Ls, ∃ g, ρ g = k) ∧
      UL' ≠ ⊥ := by
  rcases h with ⟨Z, hZ1, -, h⟩ | h | ⟨n, h⟩ | ⟨n, hn, k, hk1, -, h⟩
  · obtain ⟨n, -, ρ, hn3, -, h1, h2, h3, -⟩ := FLc.ml_case_ext4 hV2 (fun z hz => (hZ1 hz).1) h
    exact ⟨n, ρ, hn3, h1, h2, h3⟩
  · obtain ⟨n, -, ρ, hn3, -, h1, h2, h3, -⟩ := FLc.ml_case_ext5 hV2 h
    exact ⟨n, ρ, hn3, h1, h2, h3⟩
  · obtain ⟨hn, π, U₁, U₂, hdirect, hreal1, hreal2⟩ := h
    obtain ⟨D₁⟩ := FLc.vmodelNat hreal1
      (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
    obtain ⟨a, ha⟩ := FLc.exists_ne_one_nat (by omega : 1 ≤ n)
    have hU₁ne : U₁ ≠ ⊥ := FLc.ne_bot_of_surj D₁.β D₁.surj a ha
    exact ⟨n, FLc.rhoOf π, by omega, FLc.rhoOf_mem π, FLc.rhoOf_surj hreal1.1, fun h0 =>
      hU₁ne (eq_bot_iff.2 (le_sup_left.trans (hdirect.1.le.trans h0.le)))⟩
  · obtain ⟨n', -, ρ, hn3, -, h1, h2, h3, -⟩ := FLc.ml_case_nat hV2 (by omega) hk1 h
    exact ⟨n', ρ, hn3, h1, h2, h3⟩

theorem centralizerU_isPGroup {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L)
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {n : ℕ} (hn : 3 ≤ n)
    (ρ : FLc.SLt n →* MulAut ↥(uOf1527 Z₂ L)) (hρinj : Function.Injective ρ)
    (hrange : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ g, ρ g = k)
    (hrange' : ∀ g, ρ g ∈ autOn L (uOf1527 Z₂ L)) :
    IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (uOf1527 Z₂ L : Set G)) := by
  let θ : ↥L →* MulAut ↥(uOf1527 Z₂ L) :=
    (conjAct (uOf1527 Z₂ L)).comp (Subgroup.inclusion hF.LU)
  have hθ : ∀ (l : ↥L) (v : ↥(uOf1527 Z₂ L)),
      ((θ l v : ↥(uOf1527 Z₂ L)) : G) = (l : G) * v * (l : G)⁻¹ := fun l v =>
    FLc.conjAct_coe (hF.LU l.2) v
  have hθmem : ∀ l : ↥L, θ l ∈ ρ.range := fun l => by
    obtain ⟨g, hg⟩ := hrange (θ l) (FLc.mem_autOn_iff.2 ⟨l, hF.LU l.2, l.2, rfl⟩)
    exact ⟨g, hg⟩
  let e : FLc.SLt n ≃* ↥ρ.range := MonoidHom.ofInjective hρinj
  let α₀ : ↥L →* FLc.SLt n := e.symm.toMonoidHom.comp (θ.codRestrict ρ.range hθmem)
  have hα₀ : ∀ l : ↥L, ρ (α₀ l) = θ l := fun l => by
    have h1 : e (α₀ l) = θ.codRestrict ρ.range hθmem l := e.apply_symm_apply _
    exact congrArg Subtype.val h1
  have hα₀s : Function.Surjective α₀ := fun g => by
    obtain ⟨x, hx, hxL, hxg⟩ := FLc.mem_autOn_iff.1 (hrange' g)
    exact ⟨⟨x, hxL⟩, hρinj (by rw [hα₀]; exact hxg)⟩
  have hker : ∀ a : ↥L, α₀ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (uOf1527 Z₂ L : Set G) := by
    intro a
    constructor
    · intro h1
      have h2 : θ a = 1 := by rw [← hα₀, h1, map_one]
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h3 := hθ a ⟨u, hu⟩
      rw [h2] at h3
      have h4 : u = (a : G) * u * (a : G)⁻¹ := h3
      calc u * (a : G) = ((a : G) * u * (a : G)⁻¹) * (a : G) := by rw [← h4]
        _ = (a : G) * u := by group
    · intro h1
      apply hρinj
      rw [hα₀, map_one]
      ext v
      rw [hθ]
      have := Subgroup.mem_centralizer_iff.1 h1 (v : G) v.2
      show (a : G) * (v : G) * (a : G)⁻¹ = (v : G)
      calc (a : G) * (v : G) * (a : G)⁻¹ = ((v : G) * a) * (a : G)⁻¹ := by rw [this]
        _ = v := by group
  exact FLc.kernel_isPGroup (by omega) α₀ hα₀s hker hsimple

omit [Finite G] in
theorem mul_pow_mem_of_normalizing {L Q : Subgroup G} (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    {l q : G} (hl : l ∈ L) (hq : q ∈ Q) (m : ℕ) : ∃ l' ∈ L, (l * q) ^ m = l' * q ^ m := by
  induction m with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hqm : q ^ m ∈ Q := Q.pow_mem hq m
    have h1 : q ^ m * l * (q ^ m)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hQL hqm) l).1 hl
    refine ⟨l' * (q ^ m * l * (q ^ m)⁻¹), L.mul_mem hl' h1, ?_⟩
    rw [pow_succ, h]
    group

theorem centralizer_le_pCore_of_kernel {L Q U : Subgroup G}
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) (hLQU : L ⊔ Q ≤ Subgroup.normalizer (U : Set G))
    (hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (U : Set G))) (hQ : IsPGroup 2 ↥Q) :
    (L ⊔ Q) ⊓ Subgroup.centralizer (U : Set G) ≤ pCoreOf 2 (L ⊔ Q) := by
  have hXN : L ⊔ Q ≤ Subgroup.normalizer (((L ⊔ Q) ⊓ Subgroup.centralizer (U : Set G) : Subgroup G) :
      Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx,
      normalizer_le_normalizer_centralizer U (hLQU hx)⟩
  have hX2 : IsPGroup 2 ↥((L ⊔ Q) ⊓ Subgroup.centralizer (U : Set G)) := by
    rintro ⟨x, hxLQ, hxC⟩
    have hxLQ' : x ∈ ((L ⊔ Q : Subgroup G) : Set G) := hxLQ
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L Q hQL] at hxLQ'
    obtain ⟨l, hl, q, hq, hlq⟩ := hxLQ'
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ
    obtain ⟨l', hl', hpow⟩ := mul_pow_mem_of_normalizing hQL hl hq (Nat.card ↥Q)
    have hq1 : q ^ Nat.card ↥Q = 1 := by
      have : (⟨q, hq⟩ : ↥Q) ^ Nat.card ↥Q = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    have hlq' : l * q = x := hlq
    rw [hq1, mul_one, hlq'] at hpow
    have hmem : x ^ Nat.card ↥Q ∈ L ⊓ Subgroup.centralizer (U : Set G) :=
      ⟨by rw [hpow]; exact hl', Subgroup.pow_mem _ hxC _⟩
    obtain ⟨k, hk⟩ := hker ⟨_, hmem⟩
    have h1 : (x ^ Nat.card ↥Q) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨a + k, Subtype.ext ?_⟩
    have h2 : x ^ 2 ^ (a + k) = 1 := by
      rw [← h1, ← pow_mul, ha, pow_add]
    simpa using h2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hXN hX2

theorem offender_transfer_group {U V₀ Q : Subgroup G} (hUe : IsElemAbelian 2 U)
    (hVe : IsElemAbelian 2 V₀) (hUV : U ≤ V₀) (hQU : Q ≤ Subgroup.normalizer (U : Set G))
    (hfaith : ∀ q ∈ Q, (∀ u ∈ U, q * u = u * q) → ∀ v ∈ V₀, q * v = v * q)
    {X₀ A : Subgroup (MulAut ↥V₀)} (hAQ : A ≤ autOn Q V₀)
    (hA : @IsFFStarOffender ↥V₀ (commGroupOfElemAbelian hVe) X₀ A)
    (X' : Subgroup (MulAut ↥U)) (hX' : autOn Q U ≤ X') :
    ∃ B : Subgroup (MulAut ↥U), B ≤ autOn Q U ∧
      @IsFFStarOffender ↥U (commGroupOfElemAbelian hUe) X' B := by
  let _ : CommGroup ↥V₀ := commGroupOfElemAbelian hVe
  let _ : CommGroup ↥U := commGroupOfElemAbelian hUe
  let ι : ↥U →* ↥V₀ := Subgroup.inclusion hUV
  have hι : Function.Injective ι := Subgroup.inclusion_injective hUV
  have hstab : ∀ σ ∈ A, ∀ w : ↥U, ∃ w' : ↥U, ι w' = σ (ι w) := by
    intro σ hσ w
    obtain ⟨q, hqN, hqQ, hqσ⟩ := FLc.mem_autOn_iff.1 (hAQ hσ)
    refine ⟨⟨q * (w : G) * q⁻¹, (Subgroup.mem_normalizer_iff.1 (hQU hqQ) w).1 w.2⟩, ?_⟩
    apply Subtype.ext
    rw [← hqσ, FLc.conjAct_coe hqN]
    rfl
  have hfaith' : ∀ σ ∈ A, (∀ w : ↥U, σ (ι w) = ι w) → σ = 1 := by
    intro σ hσ h1
    obtain ⟨q, hqN, hqQ, hqσ⟩ := FLc.mem_autOn_iff.1 (hAQ hσ)
    have hqU : ∀ u ∈ U, q * u = u * q := by
      intro u hu
      have h2 := congrArg (fun x : ↥V₀ => (x : G)) (h1 ⟨u, hu⟩)
      rw [← hqσ] at h2
      simp only [FLc.conjAct_coe hqN] at h2
      have h3 : q * u * q⁻¹ = u := h2
      calc q * u = (q * u * q⁻¹) * q := by group
        _ = u * q := by rw [h3]
    ext v
    rw [← hqσ]
    show ((conjAct V₀ ⟨q, hqN⟩ v : ↥V₀) : G) = ((1 : MulAut ↥V₀) v : ↥V₀)
    rw [FLc.conjAct_coe hqN, MulAut.one_apply]
    have h4 := hfaith q hqQ hqU v v.2
    calc q * (v : G) * q⁻¹ = ((v : G) * q) * q⁻¹ := by rw [h4]
      _ = v := by group
  obtain ⟨B, hBA, hBne, hBab, hBmax⟩ := FLc.offender_restrict ι hι hA hstab hfaith'
  have hBQ : B ≤ autOn Q U := by
    intro b hb
    obtain ⟨σ, hσA, hσ⟩ := hBA b hb
    obtain ⟨q, hqN, hqQ, hqσ⟩ := FLc.mem_autOn_iff.1 (hAQ hσA)
    have hqU : q ∈ Subgroup.normalizer (U : Set G) := hQU hqQ
    refine FLc.mem_autOn_iff.2 ⟨q, hqU, hqQ, ?_⟩
    ext w
    rw [FLc.conjAct_coe hqU]
    have h1 := hσ w
    rw [← hqσ] at h1
    have h2 := congrArg (fun x : ↥V₀ => (x : G)) h1
    simp only [FLc.conjAct_coe hqN] at h2
    exact h2.symm
  exact ⟨B, hBQ, hBQ.trans hX' |> fun h => h, hBne, hBab, hBmax⟩

theorem input15128OffenderTransfer_holds : Input15128OffenderTransfer := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hoff
  obtain ⟨hV, A, hAQ, hAoff⟩ := hoff
  have hF := facts_of_ctx hc
  have hU := hF.hU
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rcases hc.h26.2 with h | h
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 4 2 1 h).2
    · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 5 2 1 h).2
  have hQS : q1_1516 Mc Z₁ ≤ s1516 T Z₁ := hF.QS
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs =>
    Subgroup.mem_normalizer_iff.2 fun l => ⟨fun hl => hF.SL s hs l hl, fun hl => by
      have := hF.SL s⁻¹ ((s1516 T Z₁).inv_mem hs) _ hl
      simpa [mul_assoc] using this⟩
  have hQN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) := hQS.trans hSN
  have hZ₂Q : Z₂ ≤ q1_1516 Mc Z₁ := z2_le_q1 hc
  have hULQ : uOf1527 Z₂ L ≤ L ⊔ q1_1516 Mc Z₁ := by
    refine conjClosure_le fun l hl z hz => ?_
    have hzS : z ∈ s1516 T Z₁ := hQS (hZ₂Q hz)
    have h1 : z * l⁻¹ * z⁻¹ ∈ L := hF.SL z hzS l⁻¹ (L.inv_mem hl)
    have e : l * z * l⁻¹ = (l * (z * l⁻¹ * z⁻¹)) * z := by group
    rw [e]
    exact (L ⊔ q1_1516 Mc Z₁).mul_mem (Subgroup.mem_sup_left (L.mul_mem hl h1))
      (Subgroup.mem_sup_right (hZ₂Q hz))
  have hSZ2 : s1516 T Z₁ ≤ Subgroup.normalizer (Z₂ : Set G) := fun s hs =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun z hz => by
      have := hF.SZ s hs z hz
      calc z * s = (s * z * s⁻¹) * s := by rw [this]
        _ = s * z := by group)
  have hSU : s1516 T Z₁ ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G) :=
    le_normalizer_conjClosure_of_le5 hSZ2 hSN
  have hLQU : L ⊔ q1_1516 Mc Z₁ ≤ Subgroup.normalizer (uOf1527 Z₂ L : Set G) :=
    sup_le hF.LU (hQS.trans hSU)
  have hU2 : IsPGroup 2 ↥(uOf1527 Z₂ L) := isPGroup_two_of_sq hU.2
  have hUP : uOf1527 Z₂ L ≤ pCoreOf 2 (L ⊔ q1_1516 Mc Z₁) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hULQ hLQU hU2
  have hPQ : pCoreOf 2 (L ⊔ q1_1516 Mc Z₁) ≤ q1_1516 Mc Z₁ :=
    c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hc.h18.five.2.2.radical hc.hL.comp
      hc.hL.quasi hQN)
  have hPU : ∀ x ∈ pCoreOf 2 (L ⊔ q1_1516 Mc Z₁), ∀ u ∈ uOf1527 Z₂ L, x * u = u * x := by
    intro x hx
    have hle : uOf1527 Z₂ L ≤ Subgroup.centralizer ({x} : Set G) := by
      refine conjClosure_le fun l hl z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx' : l⁻¹ * x * l ∈ pCoreOf 2 (L ⊔ q1_1516 Mc Z₁) := by
        have := (Subgroup.mem_normalizer_iff.1
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
            (Subgroup.mem_sup_left (L.inv_mem hl) : l⁻¹ ∈ L ⊔ q1_1516 Mc Z₁)) x).1 hx
        simpa using this
      have hx'S : l⁻¹ * x * l ∈ s1516 T Z₁ := hQS (hPQ hx')
      have h1 := hF.SZ _ hx'S z hz
      have h2 : (l⁻¹ * x * l) * z = z * (l⁻¹ * x * l) := by
        calc (l⁻¹ * x * l) * z = ((l⁻¹ * x * l) * z * (l⁻¹ * x * l)⁻¹) * (l⁻¹ * x * l) := by group
          _ = z * (l⁻¹ * x * l) := by rw [h1]
      calc l * z * l⁻¹ * x = l * (z * (l⁻¹ * x * l)) * l⁻¹ := by group
        _ = l * ((l⁻¹ * x * l) * z) * l⁻¹ := by rw [h2]
        _ = x * (l * z * l⁻¹) := by group
    intro u hu
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hu)).symm
  have hUV : uOf1527 Z₂ L ≤ vC27Of15128 Mc Z₁ L := by
    intro u hu
    exact Subgroup.subset_closure ⟨⟨hUP hu, Subgroup.mem_centralizer_iff.2 fun x hx => hPU x hx u hu⟩,
      hU.2 u hu⟩
  have hV₀C : vC27Of15128 Mc Z₁ L ≤
      Subgroup.centralizer (pCoreOf 2 (L ⊔ q1_1516 Mc Z₁) : Set G) :=
    (Subgroup.closure_le _).2 fun g hg => hg.1.2
  have hker : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (uOf1527 Z₂ L : Set G)) := by
    obtain ⟨hU', halt⟩ := hc.h27
    let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hU'
    have hV2 : ∀ w : ↥(uOf1527 Z₂ L), w ^ 2 = 1 := fun w =>
      Subtype.ext (by simpa using hU'.2 w w.2)
    obtain ⟨n, ρ₀, hn3, hr', hr, hne⟩ := rho_of_alt hV2 halt
    have hne' : uLOf1527 Z₂ L ≠ ⊥ := fun h => hne (by rw [h, Subgroup.bot_subgroupOf])
    exact centralizerU_isPGroup hF hsimple hn3 ρ₀ (rho_inj_of_ne_bot hF hn3 ρ₀ hr hne') hr hr'
  have hQ2 : IsPGroup 2 ↥(q1_1516 Mc Z₁) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hfaith : ∀ q ∈ q1_1516 Mc Z₁, (∀ u ∈ uOf1527 Z₂ L, q * u = u * q) →
      ∀ v ∈ vC27Of15128 Mc Z₁ L, q * v = v * q := by
    intro q hq hqU v hv
    have hqX : q ∈ (L ⊔ q1_1516 Mc Z₁) ⊓ Subgroup.centralizer (uOf1527 Z₂ L : Set G) :=
      ⟨Subgroup.mem_sup_right hq, Subgroup.mem_centralizer_iff.2 fun u hu => (hqU u hu).symm⟩
    have hqP : q ∈ pCoreOf 2 (L ⊔ q1_1516 Mc Z₁) :=
      centralizer_le_pCore_of_kernel hQN hLQU hker hQ2 hqX
    exact Subgroup.mem_centralizer_iff.1 (hV₀C hv) q hqP
  obtain ⟨B, hBQ, hBoff⟩ := offender_transfer_group hU hV hUV (hQS.trans hSU) hfaith hAQ hAoff
    (autOn (L ⊔ s1516 T Z₁) (uOf1527 Z₂ L))
    (FLc.autOn_mono' (hQS.trans le_sup_right)) |> fun h => h
  exact ⟨hU, B, hBQ, hBoff⟩

end CFSG.Quasithin
