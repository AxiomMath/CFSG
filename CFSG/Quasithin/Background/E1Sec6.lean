module

public import CFSG.Quasithin.Background.E1Sec7
import CFSG.GroupTheory.HyperplaneGeneration
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Quasithin

namespace E1

open CFSG.Open CFSG.Quasithin.A1b
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_isPGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P N : Subgroup G}
    (hP : IsPGroup p P) (hN : IsPGroup 2 N) : P ⊓ N = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  obtain ⟨a, ha⟩ := hP ⟨x, hx.1⟩
  obtain ⟨b, hb⟩ := hN ⟨x, hx.2⟩
  have h1 : x ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
  have h2 : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have := mem_of_pow_mem_two_p (N := (⊥ : Subgroup G)) hp hp2
    (by rw [h1]; exact Subgroup.one_mem _) (by rw [h2]; exact Subgroup.one_mem _)
  simpa using this

omit [Finite G] in
theorem isSylowIn_two_of_le {P₁ P₂ K : Subgroup G} (h : IsSylowIn 2 P₁ K) (h12 : P₁ ≤ P₂)
    (h2K : P₂ ≤ K) (hP₂ : IsPGroup 2 P₂) : IsSylowIn 2 P₂ K :=
  ⟨h2K, hP₂, fun hd => h.not_dvd_relIndex (hd.trans (Subgroup.relIndex_dvd_of_le_left K h12))⟩

theorem eOneAmb_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P₀ τ A B : Subgroup G}
    (hP₀ : IsPGroup p P₀) (hτ : IsPGroup 2 τ) (hτP : τ ≤ Subgroup.normalizer (P₀ : Set G))
    (hne : P₀ ≠ ⊥) (hAτ : A ≤ τ) (hcomm : ⁅P₀, A⁆ = P₀) (hBA : B ≤ A)
    (hBc : B ≤ Subgroup.centralizer (P₀ : Set G)) (hBidx : B.relIndex A ≤ 2) :
    EOneAmb (P₀ ⊔ τ) A := by
  set S := P₀ ⊔ τ with hS
  set N := pCoreOf 2 S with hN
  have hPS : P₀ ≤ S := le_sup_left
  have hτS : τ ≤ S := le_sup_right
  have hSP : S ≤ Subgroup.normalizer (P₀ : Set G) := sup_le Subgroup.le_normalizer hτP
  have hN2 : IsPGroup 2 N := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 S
  have hNS : N ≤ S := CFSG.LieType.BorelTits.pCoreOf_le 2 S
  have hSN : S ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 S
  have hPN : P₀ ⊓ N = ⊥ := inf_eq_bot_of_isPGroup hp hp2 hP₀ hN2
  have hNc : N ≤ Subgroup.centralizer (P₀ : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ P₀ :=
      P₀.mul_mem ((Subgroup.mem_normalizer_iff.mp (hSP (hNS hx)) y).mp hy) (P₀.inv_mem hy)
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact N.mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hSN (hPS hy)) x⁻¹).mp (N.inv_mem hx))
    have h3 : x * y * x⁻¹ * y⁻¹ ∈ P₀ ⊓ N := ⟨h1, h2⟩
    rw [hPN, Subgroup.mem_bot] at h3
    have : x * y = y * x := by
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h3, one_mul]
    exact this.symm
  set D : Subgroup G := τ ⊓ Subgroup.centralizer (P₀ : Set G) with hD
  have hDτ : D ≤ τ := inf_le_left
  have hDc : ∀ d ∈ D, ∀ y ∈ P₀, y * d = d * y := fun d hd y hy =>
    Subgroup.mem_centralizer_iff.mp hd.2 y hy
  have hPD : P₀ ≤ Subgroup.normalizer (D : Set G) := by
    intro y hy
    apply mem_normalizer_of_conj_mem
    intro d hd
    have : y * d * y⁻¹ = d := by
      have := hDc d hd y hy
      calc y * d * y⁻¹ = (d * y) * y⁻¹ := by rw [this]
        _ = d := by group
    rw [this]
    exact hd
  have hτD : τ ≤ Subgroup.normalizer (D : Set G) := by
    intro t ht
    apply mem_normalizer_of_conj_mem
    intro d hd
    refine Subgroup.mem_inf.mpr ⟨τ.mul_mem (τ.mul_mem ht (hDτ hd)) (τ.inv_mem ht), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : t⁻¹ * u * t ∈ P₀ := by
      have := (Subgroup.mem_normalizer_iff.mp (hτP (τ.inv_mem ht)) u).mp hu
      simpa using this
    have h1 := hDc d hd _ hu'
    calc u * (t * d * t⁻¹) = t * ((t⁻¹ * u * t) * d) * t⁻¹ := by group
      _ = t * (d * (t⁻¹ * u * t)) * t⁻¹ := by rw [h1]
      _ = (t * d * t⁻¹) * u := by group
  have hSD : S ≤ Subgroup.normalizer (D : Set G) := sup_le hPD hτD
  have hDS : D ≤ S := hDτ.trans hτS
  have hD2 : IsPGroup 2 D := hτ.to_le hDτ
  have hDN : D ≤ N := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hDS hSD hD2
  have hBD : B ≤ D := le_inf (hBA.trans hAτ) hBc
  have hBN : B ≤ N := hBD.trans hDN
  have hAN : ¬ A ≤ N := by
    intro hAN
    apply hne
    have h1 : A ≤ Subgroup.centralizer (P₀ : Set G) := hAN.trans hNc
    have h2 : ⁅A, P₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    calc P₀ = ⁅P₀, A⁆ := hcomm.symm
      _ = ⁅A, P₀⁆ := Subgroup.commutator_comm _ _
      _ = ⊥ := h2
  have hrel : N.relIndex A = 2 := by
    have h1 : N.relIndex A ∣ B.relIndex A := Subgroup.relIndex_dvd_of_le_left A hBN
    have hpos : B.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle : N.relIndex A ≤ 2 := (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) h1).trans hBidx
    have hne1 : N.relIndex A ≠ 1 := fun h => hAN (Subgroup.relIndex_eq_one.mp h)
    have hne0 : N.relIndex A ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  refine ⟨p, hp, hp2, P₀ ⊔ N, sup_le hPS hNS, ?_, le_sup_right, ?_, ?_, ?_, ?_, hrel⟩
  · intro s hs
    exact mem_normalizer_sup (hSP hs) (hSN hs)
  · intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left P₀ N (hNS.trans hSP)] at hx
    obtain ⟨v, hv, n, hn, rfl⟩ := hx
    obtain ⟨k, hk⟩ := hP₀ ⟨v, hv⟩
    have hvk : v ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨n', hn', hvn⟩ := mul_pow_eq_of_mem_normalizer (O := N) (hSN (hPS hv)) hn (p ^ k)
    exact ⟨k, by rw [hvn, hvk, one_mul]; exact hn'⟩
  · intro s hs
    have hs' : s ∈ P₀ ⊔ τ := hs
    obtain ⟨j, hj⟩ := exists_pow_mem_of_mem_sup hτ hτP hs'
    exact ⟨j, Subgroup.mem_sup_left hj⟩
  · intro h
    apply hne
    have h' : P₀ ⊔ N = N := h
    have : P₀ ≤ N := h' ▸ le_sup_left
    rw [← hPN]
    exact (inf_eq_left.mpr this).symm
  · refine sup_le ?_ le_sup_right
    have h1 : P₀ ≤ ⁅P₀ ⊔ N, A⁆ :=
      calc P₀ = ⁅P₀, A⁆ := hcomm.symm
        _ ≤ ⁅P₀ ⊔ N, A⁆ := Subgroup.commutator_mono le_sup_left le_rfl
    exact h1.trans le_sup_left

theorem isE_one_sup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T A P₀ B : Subgroup G}
    (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hAab : IsElemAbelian 2 A) (hP₀ : IsPGroup p P₀)
    (hne : P₀ ≠ ⊥) (hτP : tauOf ⊤ T A ≤ Subgroup.normalizer (P₀ : Set G))
    (hcomm : ⁅P₀, A⁆ = P₀) (hBA : B ≤ A) (hBc : B ≤ Subgroup.centralizer (P₀ : Set G))
    (hBidx : B.relIndex A ≤ 2) :
    IsE 1 ⊤ T A (P₀ ⊔ tauOf ⊤ T A) ∧
      EOne ↥(P₀ ⊔ tauOf ⊤ T A) (A.subgroupOf (P₀ ⊔ tauOf ⊤ T A)) ∧
      Nat.card (barO2 ↥(P₀ ⊔ tauOf ⊤ T A) (A.subgroupOf (P₀ ⊔ tauOf ⊤ T A))) ≤ 2 ^ 1 := by
  set τ := tauOf ⊤ T A with hτdef
  have hτT : τ ≤ T := tauOf_le _ _ _
  have hτ2 : IsPGroup 2 τ := hT.isPGroup.to_le hτT
  have hAτ : A ≤ τ := le_sup_left.trans (le_tauOf hT hAT hAab)
  have hamb : EOneAmb (P₀ ⊔ τ) A := eOneAmb_sup hp hp2 hP₀ hτ2 hτP hne hAτ hcomm hBA hBc hBidx
  have hAS : A ≤ P₀ ⊔ τ := hAτ.trans le_sup_right
  have hE : EOne ↥(P₀ ⊔ τ) (A.subgroupOf (P₀ ⊔ τ)) := (eOne_iff_amb hAS).mpr hamb
  have hcard : Nat.card (barO2 ↥(P₀ ⊔ τ) (A.subgroupOf (P₀ ⊔ τ))) ≤ 2 ^ 1 := by
    obtain ⟨-, -, -, -, -, -, h⟩ := hE
    rw [h]
    norm_num
  have hSyl : IsSylowIn 2 τ (P₀ ⊔ τ) := by
    have h0 : IsSylowIn 2 (τ ⊓ P₀) P₀ := by
      have hbot : τ ⊓ P₀ = ⊥ := by
        rw [inf_comm]
        exact inf_eq_bot_of_isPGroup hp hp2 hP₀ hτ2
      rw [hbot]
      refine ⟨bot_le, ?_, ?_⟩
      · intro g
        refine ⟨0, ?_⟩
        have hg : (g : G) = 1 := Subgroup.mem_bot.mp g.2
        exact Subtype.ext (by simpa using hg)
      · rw [Subgroup.relIndex_bot_left]
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨n, hn⟩ := hP₀.exists_card_eq
        rw [hn]
        intro h2
        have h3 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h3).symm
    exact isSylowIn_two_of_sup_inf hτP hτ2 h0
  have hSyl' : IsSylowIn 2 (T ⊓ (P₀ ⊔ τ)) (P₀ ⊔ τ) :=
    isSylowIn_two_of_le hSyl (le_inf hτT le_sup_right) inf_le_right
      (hT.isPGroup.to_le inf_le_left)
  exact ⟨⟨le_top, le_inf hτT le_sup_right, hSyl', Or.inl ⟨hE, hcard⟩⟩, hE, hcard⟩

theorem tauOf_le_normalizer_commutator {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T A B X : Subgroup G} [X.Normal] (hXp : IsPGroup p X) (hBA : B ≤ A) :
    tauOf ⊤ T A ≤ Subgroup.normalizer
      ((⁅X ⊓ Subgroup.centralizer (B : Set G), A⁆ : Subgroup G) : Set G) := by
  intro t ht
  apply mem_normalizer_of_conj_mem
  have hO2 : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup G)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hOn : ∀ o ∈ pCoreOf 2 (⊤ : Subgroup G), ∀ g : G,
      g * o * g⁻¹ ∈ pCoreOf 2 (⊤ : Subgroup G) := fun o ho g =>
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (⊤ : Subgroup G) (Subgroup.mem_top g)) o).mp ho
  have hOX : ∀ o ∈ pCoreOf 2 (⊤ : Subgroup G), ∀ x ∈ X, o * x = x * o := by
    intro o ho x hx
    have h1 : o * x * o⁻¹ * x⁻¹ ∈ X :=
      X.mul_mem (Subgroup.Normal.conj_mem inferInstance x hx o) (X.inv_mem hx)
    have h2 : o * x * o⁻¹ * x⁻¹ ∈ pCoreOf 2 (⊤ : Subgroup G) := by
      have : o * x * o⁻¹ * x⁻¹ = o * (x * o⁻¹ * x⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ho (hOn o⁻¹ (Subgroup.inv_mem _ ho) x)
    have h3 : o * x * o⁻¹ * x⁻¹ ∈ X ⊓ pCoreOf 2 (⊤ : Subgroup G) := ⟨h1, h2⟩
    rw [inf_eq_bot_of_isPGroup hp hp2 hXp hO2, Subgroup.mem_bot] at h3
    calc o * x = (o * x * o⁻¹ * x⁻¹) * (x * o) := by group
      _ = x * o := by rw [h3, one_mul]
  have htinv : t⁻¹ ∈ tauOf ⊤ T A := (tauOf ⊤ T A).inv_mem ht
  have key : ∀ c ∈ X ⊓ Subgroup.centralizer (B : Set G), ∀ a ∈ A,
      t * ⁅c, a⁆ * t⁻¹ ∈ ⁅X ⊓ Subgroup.centralizer (B : Set G), A⁆ := by
    intro c hc a ha
    have hcX : c ∈ X := hc.1
    set c' := t * c * t⁻¹ with hc'
    have hc'X : c' ∈ X := Subgroup.Normal.conj_mem inferInstance c hcX t
    have hc'B : c' ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have ho₁ : ⁅t⁻¹, b⁆ ∈ pCoreOf 2 (⊤ : Subgroup G) := htinv.2.2 b (hBA hb)
      have hbc : b * c = c * b := Subgroup.mem_centralizer_iff.mp hc.2 b hb
      have hoc : ⁅t⁻¹, b⁆ * c = c * ⁅t⁻¹, b⁆ := hOX _ ho₁ c hcX
      have e1 : t⁻¹ * b * t = ⁅t⁻¹, b⁆ * b := by
        simp only [commutatorElement_def]; group
      calc b * c' = t * (t⁻¹ * b * t) * c * t⁻¹ := by rw [hc']; group
        _ = t * (⁅t⁻¹, b⁆ * (b * c)) * t⁻¹ := by rw [e1]; group
        _ = t * (⁅t⁻¹, b⁆ * (c * b)) * t⁻¹ := by rw [hbc]
        _ = t * ((⁅t⁻¹, b⁆ * c) * b) * t⁻¹ := by group
        _ = t * ((c * ⁅t⁻¹, b⁆) * b) * t⁻¹ := by rw [hoc]
        _ = t * c * (⁅t⁻¹, b⁆ * b) * t⁻¹ := by group
        _ = t * c * (t⁻¹ * b * t) * t⁻¹ := by rw [e1]
        _ = c' * b := by rw [hc']; group
    have ho : ⁅t, a⁆ ∈ pCoreOf 2 (⊤ : Subgroup G) := ht.2.2 a ha
    have e2 : t * a * t⁻¹ = ⁅t, a⁆ * a := by
      simp only [commutatorElement_def]; group
    have hcomm1 : ⁅t, a⁆ * c' = c' * ⁅t, a⁆ := hOX _ ho c' hc'X
    have hz : ⁅c', a⁆ ∈ X := by
      have : ⁅c', a⁆ = c' * (a * c'⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact X.mul_mem hc'X (Subgroup.Normal.conj_mem inferInstance c'⁻¹ (X.inv_mem hc'X) a)
    have hcomm2 : ⁅t, a⁆ * ⁅c', a⁆ = ⁅c', a⁆ * ⁅t, a⁆ := hOX _ ho _ hz
    have e3 : t * ⁅c, a⁆ * t⁻¹ = ⁅c', ⁅t, a⁆ * a⁆ := by
      rw [← e2, hc']
      simp only [commutatorElement_def]
      group
    have e4 : ⁅c', ⁅t, a⁆ * a⁆ = ⁅c', a⁆ := by
      rw [comm_mul_right]
      have h5 : ⁅c', ⁅t, a⁆⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hcomm1.symm
      rw [h5, one_mul]
      calc ⁅t, a⁆ * ⁅c', a⁆ * ⁅t, a⁆⁻¹ = ⁅c', a⁆ * ⁅t, a⁆ * ⁅t, a⁆⁻¹ := by rw [hcomm2]
        _ = ⁅c', a⁆ := by group
    rw [e3, e4]
    exact Subgroup.commutator_mem_commutator ⟨hc'X, hc'B⟩ ha
  intro g hg
  have hle : ⁅X ⊓ Subgroup.centralizer (B : Set G), A⁆ ≤
      (⁅X ⊓ Subgroup.centralizer (B : Set G), A⁆).comap (MulAut.conj t).toMonoidHom := by
    refine Subgroup.commutator_le.mpr fun c hc a ha => ?_
    rw [Subgroup.mem_comap]
    exact key c hc a ha
  have := hle hg
  simpa [MulAut.conj_apply] using this

theorem le_normalizer_commutator_left {X A : Subgroup G} :
    X ≤ Subgroup.normalizer ((⁅X, A⁆ : Subgroup G) : Set G) := by
  intro y hy
  apply mem_normalizer_of_conj_mem
  intro g hg
  have hle : ⁅X, A⁆ ≤ (⁅X, A⁆).comap (MulAut.conj y).toMonoidHom := by
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    rw [Subgroup.mem_comap]
    have e : (MulAut.conj y).toMonoidHom ⁅x, a⁆ = ⁅y * x, a⁆ * ⁅y, a⁆⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (X.mul_mem hy hx) ha)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy ha))
  exact hle hg

omit [Finite G] in
theorem le_normalizer_commutator_right {X A : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    A ≤ Subgroup.normalizer ((⁅X, A⁆ : Subgroup G) : Set G) := fun _ ha =>
  mem_normalizer_commutator (hAX ha) (Subgroup.le_normalizer ha)

theorem comm_sup_inf_centralizer_eq {X A : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hA : IsPGroup 2 A)
    (hcop : Nat.Coprime 2 (Nat.card X)) (hX : Group.IsSolvable X) :
    ⁅X, A⁆ ⊔ (X ⊓ Subgroup.centralizer (A : Set G)) = X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction ↥A ↥X := Subgroup.conjMulDistribMulActionOfLeNormalizer A X hAX
  have hX₀X : ⁅X, A⁆ ≤ X := commutator_le_of_le_normalizer hAX
  have hAX₀ := le_normalizer_commutator_right hAX
  have hN₀n : ((⁅X, A⁆).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hX₀X).mpr le_normalizer_commutator_left
  have hN₀inv : ∀ a : ↥A, ∀ x ∈ (⁅X, A⁆).subgroupOf X, a • x ∈ (⁅X, A⁆).subgroupOf X := by
    intro a x hx
    exact (Subgroup.mem_normalizer_iff.mp (hAX₀ a.2) (x : G)).mp hx
  have hinv : CFSG.IsInvariant ↥A ↥X ((⁅X, A⁆).subgroupOf X) :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem hN₀inv
  have hNsolv : Group.IsSolvable ((⁅X, A⁆).subgroupOf X) := inferInstance
  have hcopN : Nat.Coprime (Nat.card ↥A) (Nat.card ((⁅X, A⁆).subgroupOf X)) := by
    obtain ⟨k, hk⟩ := hA.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _) hcop)
  refine le_antisymm (sup_le hX₀X inf_le_left) fun g hg => ?_
  have hg' : ∀ b : ↥A, (⟨g, hg⟩ : ↥X)⁻¹ * (b • (⟨g, hg⟩ : ↥X)) ∈ (⁅X, A⁆).subgroupOf X := by
    intro b
    show (g⁻¹ * ((b : G) * g * (b : G)⁻¹) : G) ∈ ⁅X, A⁆
    have h1 := Subgroup.commutator_mem_commutator (X.inv_mem hg) b.2
    have e : ⁅g⁻¹, (b : G)⁆ = g⁻¹ * ((b : G) * g * (b : G)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h1
  obtain ⟨c, hc, hcg⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    ((⁅X, A⁆).subgroupOf X) hinv hNsolv hcopN ⟨g, hg⟩ hg'
  have hcg' : (c : G)⁻¹ * g ∈ ⁅X, A⁆ := hcg
  have hcC : (c : G) ∈ X ⊓ Subgroup.centralizer (A : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : ((⟨a, ha⟩ : ↥A) • c : ↥X) = c := hc ⟨a, ha⟩
    have h2 : (a * (c : G) * a⁻¹) = (c : G) := congrArg Subtype.val h1
    calc a * (c : G) = (a * (c : G) * a⁻¹) * a := by group
      _ = (c : G) * a := by rw [h2]
  have e : g = (c : G) * ((c : G)⁻¹ * g) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcC) (Subgroup.mem_sup_left hcg')

theorem comm_comm_eq {X A : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hA : IsPGroup 2 A) (hcop : Nat.Coprime 2 (Nat.card X)) (hX : Group.IsSolvable X) :
    ⁅⁅X, A⁆, A⁆ = ⁅X, A⁆ := by
  have hX₀X : ⁅X, A⁆ ≤ X := commutator_le_of_le_normalizer hAX
  have hAX₀ := le_normalizer_commutator_right hAX
  have hXX₀ : X ≤ Subgroup.normalizer ((⁅X, A⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_left
  have hX₀solv : Group.IsSolvable (⁅X, A⁆ : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hX₀X)
      (Subgroup.inclusion_injective hX₀X)
  have hcop₀ : Nat.Coprime 2 (Nat.card (⁅X, A⁆ : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hX₀X) hcop
  have hfacX := comm_sup_inf_centralizer_eq hAX hA hcop hX
  have hfacX₀ := comm_sup_inf_centralizer_eq hAX₀ hA hcop₀ hX₀solv
  have hZX₀ : ⁅⁅X, A⁆, A⁆ ≤ ⁅X, A⁆ := commutator_le_of_le_normalizer hAX₀
  have hX₀Z : ⁅X, A⁆ ≤ Subgroup.normalizer ((⁅⁅X, A⁆, A⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_left
  have hCZ : X ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.normalizer ((⁅⁅X, A⁆, A⁆ : Subgroup G) : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    intro g hg
    have hle : ⁅⁅X, A⁆, A⁆ ≤ (⁅⁅X, A⁆, A⁆).comap (MulAut.conj c).toMonoidHom := by
      refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
      rw [Subgroup.mem_comap]
      have hca : (MulAut.conj c) a = a := by
        have h1 : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a ha
        simp only [MulAut.conj_apply]
        calc c * a * c⁻¹ = (a * c) * c⁻¹ := by rw [h1]
          _ = a := by group
      have e : (MulAut.conj c).toMonoidHom ⁅x, a⁆ = ⁅(MulAut.conj c) x, a⁆ := by
        have h2 := map_commutatorElement (MulAut.conj c).toMonoidHom x a
        rw [show (MulAut.conj c).toMonoidHom a = a from hca] at h2
        exact h2
      rw [e]
      have hcx : (MulAut.conj c) x ∈ ⁅X, A⁆ := by
        have := (Subgroup.mem_normalizer_iff.mp (hXX₀ hc.1) x).mp hx
        simpa [MulAut.conj_apply] using this
      exact Subgroup.commutator_mem_commutator hcx ha
    exact hle hg
  have hXZ : X ≤ Subgroup.normalizer ((⁅⁅X, A⁆, A⁆ : Subgroup G) : Set G) :=
    hfacX.ge.trans (sup_le hX₀Z hCZ)
  let U : Subgroup G :=
    { carrier := {g | g ∈ X ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ ⁅⁅X, A⁆, A⁆}
      one_mem' := ⟨X.one_mem, fun a _ => by simp⟩
      mul_mem' := by
        rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
        refine ⟨X.mul_mem hgX hhX, fun a ha => ?_⟩
        rw [comm_mul_left]
        refine Subgroup.mul_mem _ ?_ (hg a ha)
        exact (Subgroup.mem_normalizer_iff.mp (hXZ hgX) _).mp (hh a ha)
      inv_mem' := by
        rintro g ⟨hgX, hg⟩
        refine ⟨X.inv_mem hgX, fun a ha => ?_⟩
        have e : ⁅g⁻¹, a⁆ = g⁻¹ * (⁅g, a⁆)⁻¹ * g := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.mp (hXZ (X.inv_mem hgX)) _).mp
          (Subgroup.inv_mem _ (hg a ha))
        simpa using this }
  have hZU : ⁅⁅X, A⁆, A⁆ ≤ U := fun z hz =>
    ⟨hX₀X (hZX₀ hz), fun a ha => Subgroup.commutator_mem_commutator (hZX₀ hz) ha⟩
  have hCU : X ⊓ Subgroup.centralizer (A : Set G) ≤ U := fun c hc =>
    ⟨hc.1, fun a ha => by
      have h1 : a * c = c * a := Subgroup.mem_centralizer_iff.mp hc.2 a ha
      have : ⁅c, a⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact h1.symm
      rw [this]
      exact Subgroup.one_mem _⟩
  have hX₀U : ⁅X, A⁆ ≤ U :=
    hfacX₀.ge.trans (sup_le hZU ((inf_le_inf_right _ hX₀X).trans hCU))
  have hXU : X ≤ U := hfacX.ge.trans (sup_le hX₀U hCU)
  exact le_antisymm hZX₀ (Subgroup.commutator_le.mpr fun x hx a ha => (hXU hx).2 a ha)

theorem exists_normal_le_ne_top {Y : Type*} [Group Y] [Finite Y] [Group.IsNilpotent Y]
    {V : Subgroup Y} (hV : V ≠ ⊤) : ∃ M : Subgroup Y, M.Normal ∧ V ≤ M ∧ M ≠ ⊤ := by
  obtain ⟨M, hM, hVM⟩ := (eq_top_or_exists_le_coatom V).resolve_left hV
  refine ⟨M, ?_, hVM, hM.1⟩
  have hlt : M < Subgroup.normalizer (M : Set Y) :=
    (Group.normalizerCondition_of_isNilpotent) M (lt_top_iff_ne_top.mpr hM.1)
  have : Subgroup.normalizer (M : Set Y) = ⊤ := hM.2 _ hlt
  exact Subgroup.normalizer_eq_top_iff.mp this

theorem comm_le_iSup_hyperplane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X A : Subgroup G}
    (hXp : IsPGroup p X) (hAab : IsElemAbelian 2 A)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    ⁅X, A⁆ ≤ ⨆ S ∈ {S : Subgroup G | S ≤ A ∧ Nat.card A = 2 * Nat.card S},
      ⁅X ⊓ Subgroup.centralizer (S : Set G), A⁆ := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hA0 : A = ⊥
  · rw [hA0]
    simp
  have hA2 : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hAab.2 g g.2)⟩
  have hXodd : Nat.Coprime 2 (Nat.card X) := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  have hXsolv : Group.IsSolvable X := by
    have := hXp.isNilpotent
    infer_instance
  have hX₀X : ⁅X, A⁆ ≤ X := commutator_le_of_le_normalizer hAX
  have hAX₀ := le_normalizer_commutator_right hAX
  have hX₀p : IsPGroup p (⁅X, A⁆ : Subgroup G) := hXp.to_le hX₀X
  have hX₀nil : Group.IsNilpotent (⁅X, A⁆ : Subgroup G) := hX₀p.isNilpotent
  have hcop₀ : Nat.Coprime 2 (Nat.card (⁅X, A⁆ : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hX₀X) hXodd
  have hB := comm_comm_eq hAX hA2 hXodd hXsolv
  set X₀ : Subgroup G := ⁅X, A⁆ with hX₀def
  set F : Set (Subgroup G) := {S | S ≤ A ∧ Nat.card A = 2 * Nat.card S} with hF
  have hgen : X₀ ≤ ⨆ S ∈ F, X₀ ⊓ Subgroup.centralizer (S : Set G) := by
    let : MulDistribMulAction ↥A ↥X₀ := Subgroup.conjMulDistribMulActionOfLeNormalizer A X₀ hAX₀
    have : CFSG.IsElementaryAbelian 2 ↥A :=
      { toIsMulCommutative := hAab.1
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
          Subtype.ext (hAab.2 x x.2) }
    have : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA0
    have hodd : ¬ 2 ∣ Nat.card ↥X₀ := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop₀
    have h := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := ↥A) (H := ↥X₀) hodd
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥X₀) ∈ ⨆ (B : Subgroup ↥A) (_ : B.index = 2),
        CFSG.fixedPointSubgroup B ↥X₀ := by
      rw [h]
      exact Subgroup.mem_top _
    have hle : (⨆ (B : Subgroup ↥A) (_ : B.index = 2), CFSG.fixedPointSubgroup B ↥X₀) ≤
        (⨆ S ∈ F, X₀ ⊓ Subgroup.centralizer (S : Set G)).comap X₀.subtype := by
      refine iSup₂_le fun B hB y hy => ?_
      have hBF : B.map A.subtype ∈ F := by
        refine ⟨Subgroup.map_subtype_le B, ?_⟩
        rw [Subgroup.card_map_of_injective A.subtype_injective]
        have := B.card_mul_index
        rw [hB] at this
        omega
      have hmem : (y : G) ∈ X₀ ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) := by
        refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨b, hb, rfl⟩
        have h1 : (b : G) * (y : G) * (b : G)⁻¹ = (y : G) :=
          congrArg Subtype.val (hy ⟨b, hb⟩)
        show (b : G) * (y : G) = (y : G) * (b : G)
        calc (b : G) * (y : G) = ((b : G) * (y : G) * (b : G)⁻¹) * (b : G) := by group
          _ = (y : G) * (b : G) := by rw [h1]
      exact (le_iSup₂_of_le (f := fun S (_ : S ∈ F) => X₀ ⊓ Subgroup.centralizer (S : Set G))
        (B.map A.subtype) hBF le_rfl) hmem
    exact hle hx'
  set U₀ : Subgroup G := ⨆ S ∈ F, ⁅X₀ ⊓ Subgroup.centralizer (S : Set G), A⁆ with hU₀
  have hU₀X₀ : U₀ ≤ X₀ := by
    refine iSup₂_le fun S _ => ?_
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans (le_of_eq hB)
  have hX₀U₀ : X₀ ≤ U₀ := by
    by_contra hne
    have hV : U₀.subgroupOf X₀ ≠ ⊤ := by
      intro h
      apply hne
      intro x hx
      have : (⟨x, hx⟩ : ↥X₀) ∈ U₀.subgroupOf X₀ := by
        rw [h]
        exact Subgroup.mem_top _
      exact this
    obtain ⟨M, hMn, hVM, hMtop⟩ := exists_normal_le_ne_top hV
    set M₀ : Subgroup G := M.map X₀.subtype with hM₀
    have hM₀norm : ∀ x ∈ X₀, x ∈ Subgroup.normalizer (M₀ : Set G) := by
      intro x hx
      apply mem_normalizer_of_conj_mem
      rintro _ ⟨m, hm, rfl⟩
      exact ⟨⟨x, hx⟩ * m * ⟨x, hx⟩⁻¹, hMn.conj_mem m hm ⟨x, hx⟩, rfl⟩
    let U' : Subgroup G :=
      { carrier := {g | g ∈ X₀ ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ M₀}
        one_mem' := ⟨X₀.one_mem, fun a _ => by simp⟩
        mul_mem' := by
          rintro g h ⟨hgX, hg⟩ ⟨hhX, hh⟩
          refine ⟨X₀.mul_mem hgX hhX, fun a ha => ?_⟩
          rw [comm_mul_left]
          refine M₀.mul_mem ?_ (hg a ha)
          exact (Subgroup.mem_normalizer_iff.mp (hM₀norm g hgX) _).mp (hh a ha)
        inv_mem' := by
          rintro g ⟨hgX, hg⟩
          refine ⟨X₀.inv_mem hgX, fun a ha => ?_⟩
          have e : ⁅g⁻¹, a⁆ = g⁻¹ * (⁅g, a⁆)⁻¹ * g := by
            simp only [commutatorElement_def]
            group
          rw [e]
          have := (Subgroup.mem_normalizer_iff.mp (hM₀norm g⁻¹ (X₀.inv_mem hgX)) _).mp
            (M₀.inv_mem (hg a ha))
          simpa using this }
    have hSU' : ∀ S ∈ F, X₀ ⊓ Subgroup.centralizer (S : Set G) ≤ U' := by
      intro S hS g hg
      refine ⟨hg.1, fun a ha => ?_⟩
      have h1 : ⁅g, a⁆ ∈ U₀ :=
        (le_iSup₂_of_le (f := fun S (_ : S ∈ F) => ⁅X₀ ⊓ Subgroup.centralizer (S : Set G), A⁆)
          S hS le_rfl) (Subgroup.commutator_mem_commutator hg ha)
      have h2 : ⁅g, a⁆ ∈ X₀ := hU₀X₀ h1
      have h3 : (⟨⁅g, a⁆, h2⟩ : ↥X₀) ∈ M := hVM h1
      exact ⟨_, h3, rfl⟩
    have hX₀U' : X₀ ≤ U' := hgen.trans (iSup₂_le fun S hS => hSU' S hS)
    have hX₀M₀ : X₀ ≤ M₀ :=
      hB.ge.trans (Subgroup.commutator_le.mpr fun g hg a ha => (hX₀U' hg).2 a ha)
    apply hMtop
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨m, hm, hmx⟩ := hX₀M₀ x.2
    have : m = x := Subtype.ext hmx
    exact this ▸ hm
  refine hX₀U₀.trans (iSup₂_le fun S hS => ?_)
  exact le_iSup₂_of_le (f := fun S (_ : S ∈ F) => ⁅X ⊓ Subgroup.centralizer (S : Set G), A⁆) S hS
    (Subgroup.commutator_mono (inf_le_inf_right _ hX₀X) le_rfl)

theorem comm_le_iSup_twoResidual {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T A X : Subgroup G}
    [X.Normal] (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hXp : IsPGroup p X) :
    ⁅X, A⁆ ≤ ⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K ∧ EOne ↥K (A.subgroupOf K) ∧
      Nat.card (barO2 ↥K (A.subgroupOf K)) ≤ 2 ^ 1}, twoResidual K := by
  have : Fact p.Prime := ⟨hp⟩
  have hA2 : IsPGroup 2 A := hT.isPGroup.to_le hAT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXodd : Nat.Coprime 2 (Nat.card X) := by
    obtain ⟨n, hn⟩ := hXp.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  have hXsolv : Group.IsSolvable X := by
    have := hXp.isNilpotent
    infer_instance
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := fun a _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top a
  refine (comm_le_iSup_hyperplane hp hp2 hXp hAab hAX).trans (iSup₂_le fun S hS => ?_)
  obtain ⟨hSA, hScard⟩ := hS
  set P₀ : Subgroup G := ⁅X ⊓ Subgroup.centralizer (S : Set G), A⁆ with hP₀
  by_cases hP : P₀ = ⊥
  · rw [hP]
    exact bot_le
  have hP₀X : P₀ ≤ X := by
    refine Subgroup.commutator_le.mpr fun c hc a ha => ?_
    have : ⁅c, a⁆ = c * (a * c⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact X.mul_mem hc.1 (Subgroup.Normal.conj_mem inferInstance c⁻¹ (X.inv_mem hc.1) a)
  have hP₀p : IsPGroup p P₀ := hXp.to_le hP₀X
  have hAC : A ≤ Subgroup.normalizer ((X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) : Set G) := by
    intro a ha
    refine mem_normalizer_inf (hAX ha) ?_
    refine Subgroup.le_normalizer ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact commute_of_isElemAbelian hAab (hSA hb) ha
  have hCodd : Nat.Coprime 2 (Nat.card (X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hXodd
  have hCsolv : Group.IsSolvable (X ⊓ Subgroup.centralizer (S : Set G) : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_left : X ⊓ Subgroup.centralizer (S : Set G) ≤ X))
      (Subgroup.inclusion_injective _)
  have hcomm : ⁅P₀, A⁆ = P₀ := comm_comm_eq hAC hA2 hCodd hCsolv
  have hSc : S ≤ Subgroup.centralizer (P₀ : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hle : P₀ ≤ Subgroup.centralizer ({b} : Set G) := by
      refine Subgroup.commutator_le.mpr fun c hc a ha => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcb : Commute c b := (Subgroup.mem_centralizer_iff.mp hc.2 b hb).symm
      have hab : Commute a b := commute_of_isElemAbelian hAab ha (hSA hb)
      exact (((hcb.mul_left hab).mul_left hcb.inv_left).mul_left hab.inv_left).eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  have hSidx : S.relIndex A ≤ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := S) (K := A)
    rw [inf_eq_left.mpr hSA] at h1
    have hpos : 0 < Nat.card S := Nat.card_pos
    have : S.relIndex A = 2 := Nat.eq_of_mul_eq_mul_right hpos (h1.trans hScard)
    exact this.le
  obtain ⟨hK, hKE, hKc⟩ := isE_one_sup hp hp2 hT hAT hAab hP₀p hP
    (tauOf_le_normalizer_commutator hp hp2 hXp hSA) hcomm hSA hSc hSidx
  refine le_trans ?_ (le_iSup₂_of_le (P₀ ⊔ tauOf ⊤ T A) ⟨hK, hKE, hKc⟩ le_rfl)
  intro x hx
  obtain ⟨k, hk⟩ := hP₀p ⟨x, hx⟩
  have hxp : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj⟩ := twoResidual_isTwoQuotient (P₀ ⊔ tauOf ⊤ T A) x (Subgroup.mem_sup_left hx)
  exact mem_of_pow_mem_two_p hp hp2 (by rw [hxp]; exact Subgroup.one_mem _) hj

theorem ten_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T A X Y : Subgroup G} [X.Normal]
    [Y.Normal] (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T) (hAab : IsElemAbelian 2 A)
    (hXp : IsPGroup p (X.map (QuotientGroup.mk' Y)))
    (hXA : ⁅X.map (QuotientGroup.mk' Y), A.map (QuotientGroup.mk' Y)⁆ =
      X.map (QuotientGroup.mk' Y)) :
    X ≤ (⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K) ⊔ Y := by
  set π := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  set Xb : Subgroup (G ⧸ Y) := X.map π with hXb
  set Ab : Subgroup (G ⧸ Y) := A.map π with hAb
  have hXbn : Xb.Normal := Subgroup.Normal.map inferInstance π hπs
  have hTb : IsSylowIn 2 (T.map π) ⊤ := isSylowIn_two_map_top hπs hT
  have hAbT : Ab ≤ T.map π := Subgroup.map_mono hA
  have hAbab : IsElemAbelian 2 Ab := isElemAbelian_map' π hAab
  have key : Xb ≤ (⨆ K ∈ {K : Subgroup G | IsE 1 ⊤ T A K}, K).map π := by
    calc Xb = ⁅Xb, Ab⁆ := hXA.symm
      _ ≤ ⨆ K ∈ {K : Subgroup (G ⧸ Y) | IsE 1 ⊤ (T.map π) Ab K ∧ EOne ↥K (Ab.subgroupOf K) ∧
          Nat.card (barO2 ↥K (Ab.subgroupOf K)) ≤ 2 ^ 1}, twoResidual K :=
        comm_le_iSup_twoResidual hp hp2 hTb hAbT hAbab hXp
      _ ≤ _ := by
        refine iSup₂_le fun K hK => ?_
        obtain ⟨J, hJ, hJK⟩ := ten_seven_eOne hT hA hAab hK.1 ⟨hK.2.1, hK.2.2⟩
        rw [hJK]
        exact (Subgroup.map_mono (twoResidual_le J)).trans
          (Subgroup.map_mono (le_iSup₂_of_le J hJ le_rfl))
  intro x hx
  obtain ⟨e, he, hex⟩ := key (Subgroup.mem_map_of_mem π hx)
  have hy : e⁻¹ * x ∈ Y := by
    rw [← QuotientGroup.ker_mk' Y, MonoidHom.mem_ker, map_mul, map_inv]
    change (π e)⁻¹ * π x = 1
    rw [hex]
    exact inv_mul_cancel _
  have h2 : x = e * (e⁻¹ * x) := by group
  rw [h2]
  exact Subgroup.mul_mem_sup he hy

end E1

end CFSG.Quasithin
