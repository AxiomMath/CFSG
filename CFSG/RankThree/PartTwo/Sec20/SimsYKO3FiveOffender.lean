module

public import CFSG.RankThree.PartTwo.Sec20.SimsYKO3FiveFac
public import CFSG.RankThree.PartTwo.Sec20.SimsYKO3FiveAut
import CFSG.RankThree.PartTwo.Sec20.SimsYKO3FiveCount

public section

namespace CFSG.RankThree.PartTwo.Sec20.SimsYKO3

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_normalizer_sup' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
private theorem conj_mem_centralizer {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) {c : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) v).mp hv
    rwa [inv_inv] at this
  have key := hc _ hv'
  calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [key]
    _ = g * c * g⁻¹ * v := by group

private def trivOn (R W Q : Subgroup G) (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) :
    Subgroup G where
  carrier := {r | r ∈ R ∧ ∀ w ∈ W, r * w * r⁻¹ * w⁻¹ ∈ Q}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨R.mul_mem ha hb, fun w hw => ?_⟩
    have h1 : a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hRQ ha) _).mp (hb' w hw)
    have h2 := Q.mul_mem h1 (ha' w hw)
    rwa [show a * (b * w * b⁻¹ * w⁻¹) * a⁻¹ * (a * w * a⁻¹ * w⁻¹) =
      a * b * w * (a * b)⁻¹ * w⁻¹ by group] at h2
  one_mem' := ⟨R.one_mem, fun w _ => by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨R.inv_mem ha, fun w hw => ?_⟩
    have h1 : a⁻¹ * (a * w * a⁻¹ * w⁻¹) * a⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hRQ (R.inv_mem ha)) _).mp (ha' w hw)
    have h2 := Q.inv_mem h1
    rwa [show (a⁻¹ * (a * w * a⁻¹ * w⁻¹) * a⁻¹⁻¹)⁻¹ = a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ by group] at h2

omit [Finite G] in
private theorem mem_trivOn {R W Q : Subgroup G} {hRQ : R ≤ Subgroup.normalizer (Q : Set G)}
    {r : G} : r ∈ trivOn R W Q hRQ ↔ r ∈ R ∧ ∀ w ∈ W, r * w * r⁻¹ * w⁻¹ ∈ Q :=
  Iff.rfl

omit [Finite G] in
private theorem le_normalizer_trivOn {R W Q : Subgroup G}
    (hRQ : R ≤ Subgroup.normalizer (Q : Set G)) (hWQ : W ≤ Subgroup.normalizer (Q : Set G))
    (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hQR : Q ≤ R) :
    W ⊔ R ≤ Subgroup.normalizer (trivOn R W Q hRQ : Set G) := by
  have hW : ∀ g ∈ W, ∀ n ∈ trivOn R W Q hRQ, g * n * g⁻¹ ∈ trivOn R W Q hRQ := by
    intro g hg n hn
    obtain ⟨hnR, hn'⟩ := mem_trivOn.mp hn
    have hq : g * n * g⁻¹ * n⁻¹ ∈ Q := by
      have := Q.inv_mem (hn' g hg)
      rwa [show (n * g * n⁻¹ * g⁻¹)⁻¹ = g * n * g⁻¹ * n⁻¹ by group] at this
    refine mem_trivOn.mpr ⟨?_, fun w hw => ?_⟩
    · have := R.mul_mem (hQR hq) hnR
      rwa [show g * n * g⁻¹ * n⁻¹ * n = g * n * g⁻¹ by group] at this
    · have h3 : w * (g * n * g⁻¹ * n⁻¹)⁻¹ * w⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hWQ hw) _).mp (Q.inv_mem hq)
      have := Q.mul_mem (Q.mul_mem hq (hn' w hw)) h3
      rwa [show g * n * g⁻¹ * n⁻¹ * (n * w * n⁻¹ * w⁻¹) * (w * (g * n * g⁻¹ * n⁻¹)⁻¹ * w⁻¹) =
        g * n * g⁻¹ * w * (g * n * g⁻¹)⁻¹ * w⁻¹ by group] at this
  have hR : ∀ g ∈ R, ∀ n ∈ trivOn R W Q hRQ, g * n * g⁻¹ ∈ trivOn R W Q hRQ := by
    intro g hg n hn
    obtain ⟨hnR, hn'⟩ := mem_trivOn.mp hn
    refine mem_trivOn.mpr ⟨R.mul_mem (R.mul_mem hg hnR) (R.inv_mem hg), fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g⁻¹⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hRW (R.inv_mem hg)) w).mp hw
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRQ hg) _).mp (hn' _ hw')
    rwa [show g * (n * (g⁻¹ * w * g⁻¹⁻¹) * n⁻¹ * (g⁻¹ * w * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * n * g⁻¹ * w * (g * n * g⁻¹)⁻¹ * w⁻¹ by group] at h1
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · exact Sec7.mem_normalizer_of_conj_mem (fun n hn => hW g hg n hn)
      (fun n hn => by simpa using hW g⁻¹ (W.inv_mem hg) n hn)
  · exact Sec7.mem_normalizer_of_conj_mem (fun n hn => hR g hg n hn)
      (fun n hn => by simpa using hR g⁻¹ (R.inv_mem hg) n hn)

omit [Finite G] in
private theorem exists_pow_mem_of_mem_sup {W R : Subgroup G}
    (hRW : R ≤ Subgroup.normalizer (W : Set G)) (hR2 : IsPGroup 2 R) {h : G}
    (hh : h ∈ W ⊔ R) : ∃ n : ℕ, h ^ (2 ^ n) ∈ W := by
  have hh' : h ∈ ((W ⊔ R : Subgroup G) : Set G) := hh
  rw [Subgroup.coe_mul_of_right_le_normalizer_left W R hRW] at hh'
  obtain ⟨w, hw, r, hr, rfl⟩ := hh'
  obtain ⟨n, hn⟩ := hR2 ⟨r, hr⟩
  have hrn : r ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have key : ∀ m : ℕ, (w * r) ^ m * (r ^ m)⁻¹ ∈ W := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hc : r ^ m * w * (r ^ m)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hRW (pow_mem hr m)) w).mp hw
      have := W.mul_mem ih hc
      rwa [show (w * r) ^ m * (r ^ m)⁻¹ * (r ^ m * w * (r ^ m)⁻¹) =
        (w * r) ^ (m + 1) * (r ^ (m + 1))⁻¹ by rw [pow_succ, pow_succ]; group] at this
  refine ⟨n, ?_⟩
  have := key (2 ^ n)
  rwa [hrn, inv_one, mul_one] at this

private theorem exists_closure_pair_eq_top {E : Type*} [Group E] [Finite E]
    (hE5 : ∀ a : E, a ^ 5 = 1) (hE25 : Nat.card E = 25) :
    ∃ v₁ v₂ : E, Subgroup.closure ({v₁, v₂} : Set E) = ⊤ := by
  classical
  have hnt : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE25]; norm_num
  obtain ⟨v₁, hv₁⟩ := exists_ne (1 : E)
  have hord : orderOf v₁ = 5 := by
    have h := orderOf_dvd_of_pow_eq_one (hE5 v₁)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv₁
    · exact h
  have hlt : Nat.card (Subgroup.zpowers v₁) < Nat.card E := by
    rw [Nat.card_zpowers, hord, hE25]; norm_num
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : E, v₂ ∉ Subgroup.zpowers v₁ := by
    by_contra h
    push Not at h
    have : Subgroup.zpowers v₁ = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [this, Subgroup.card_top] at hlt
    exact lt_irrefl _ hlt
  refine ⟨v₁, v₂, ?_⟩
  set C := Subgroup.closure ({v₁, v₂} : Set E) with hC
  have hle : Subgroup.zpowers v₁ ≤ C :=
    (Subgroup.zpowers_le).mpr (Subgroup.subset_closure (by simp))
  have hv₂C : v₂ ∈ C := Subgroup.subset_closure (by simp)
  have hlt' : Subgroup.zpowers v₁ < C := lt_of_le_of_ne hle (fun h => hv₂ (h ▸ hv₂C))
  have hcard_lt : Nat.card (Subgroup.zpowers v₁) < Nat.card C := Subgroup.card_lt_of_lt hlt'
  rw [Nat.card_zpowers, hord] at hcard_lt
  have hdvd : Nat.card C ∣ 25 := hE25 ▸ Subgroup.card_subgroup_dvd_card C
  have hC25 : Nat.card C = 25 := by
    have hpos : 0 < Nat.card C := Nat.card_pos
    have : Nat.card C ≤ 25 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card C <;> first | omega | (exfalso; revert hdvd; norm_num)
  exact Subgroup.eq_top_of_card_eq C (hC25.trans hE25.symm)

theorem jOneOf_le_centralizer_of_E25 {E : Type*} [Group E] [Finite E]
    (hEc : ∀ a b : E, a * b = b * a) (hE5 : ∀ a : E, a ^ 5 = 1) (hE25 : Nat.card E = 25)
    {N K R W Q : Subgroup G} (θ : ↥N →* MulAut E) (π : ↥W →* E) (hπ : Function.Surjective π)
    (hWN : N ≤ Subgroup.normalizer (W : Set G)) (hQN : N ≤ Subgroup.normalizer (Q : Set G))
    (hWN' : W ≤ N) (hRN : R ≤ N) (hKN : K ≤ N)
    (hπθ : ∀ (g : N) (w : W) (h : (g : G) * w * (g : G)⁻¹ ∈ W), θ g (π w) = π ⟨_, h⟩)
    (hQW : Q ≤ W) (hQπ : ∀ w : W, (w : G) ∈ Q → π w = 1)
    (hBB : ∀ X : Subgroup G, Q ≤ X → X ≤ W → (∀ v : E, ∃ x : W, (x : G) ∈ X ∧ π x = v) →
      W ≤ X)
    (hW5 : ∀ w ∈ W, ∃ a : ℕ, w ^ (5 ^ a) ∈ Q)
    (hRθ : ∀ r (hr : r ∈ R), θ ⟨r, hRN hr⟩ = 1 → ∀ w ∈ W, r * w * r⁻¹ * w⁻¹ ∈ Q)
    (hQR : Q ≤ R) (hHyp : HypThree (W ⊔ R) R)
    [Group.IsPerfect K] (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* projSL 2 (GaloisField 2 2)))
    (hKR : K ≤ Subgroup.normalizer (R : Set G)) (hRK : R ≤ Subgroup.normalizer (K : Set G))
    (hθK : θ.comp (Subgroup.inclusion hKN) ≠ 1) :
    jOneOf R ≤ Subgroup.centralizer (reducedClosure (W ⊔ R) R : Set G) := by
  classical
  set H := W ⊔ R with hHdef
  set V := reducedClosure H R with hVdef
  set κ : ↥K →* MulAut E := θ.comp (Subgroup.inclusion hKN) with hκdef
  have hR2 : IsPGroup 2 R := hHyp.two
  have hRH : R ≤ H := le_sup_right
  have hWH : W ≤ H := le_sup_left
  have hRW : R ≤ Subgroup.normalizer (W : Set G) := hRN.trans hWN
  have hRQ : R ≤ Subgroup.normalizer (Q : Set G) := hRN.trans hQN
  have hWQ : W ≤ Subgroup.normalizer (Q : Set G) := hWN'.trans hQN
  have hKW : K ≤ Subgroup.normalizer (W : Set G) := hKN.trans hWN
  obtain ⟨U, hUR, hU2, hUn, -, hUc⟩ := hHyp.exists_O2
  obtain ⟨hVH, hVn, hVab, hZV, hVU, hUV, hVred⟩ :=
    reducedClosure_spec (R := H) (S := R) (H := U) hHyp.le hR2 hHyp.syl hUR hUn hUc
  have hVR : V ≤ R := hVU.trans hUR
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := fun k hk =>
    mem_normalizer_reducedClosure (mem_normalizer_sup' (hKW hk) (hKR hk)) (hKR hk)
  have hCRD : trivOn R W Q hRQ ≤ Subgroup.centralizer (V : Set G) := by
    refine hVred _ (fun x hx => hRH (mem_trivOn.mp hx).1)
      (le_normalizer_trivOn hRQ hWQ hRW hQR) (fun x hx => ?_)
    obtain ⟨n, hn⟩ := hR2 ⟨x, (mem_trivOn.mp hx).1⟩
    refine ⟨n, ?_⟩
    have : x ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    rw [this]
    exact Subgroup.one_mem _
  have hQV : Q ≤ Subgroup.centralizer (V : Set G) := by
    intro q hq
    refine hCRD (mem_trivOn.mpr ⟨hQR hq, fun w hw => ?_⟩)
    have h1 : w * q⁻¹ * w⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hWQ hw) _).mp (Q.inv_mem hq)
    have := Q.mul_mem hq h1
    rwa [show q * (w * q⁻¹ * w⁻¹) = q * w * q⁻¹ * w⁻¹ by group] at this
  have hθCV : ∀ r (hr : r ∈ R), θ ⟨r, hRN hr⟩ = 1 → r ∈ Subgroup.centralizer (V : Set G) :=
    fun r hr h1 => hCRD (mem_trivOn.mpr ⟨hr, hRθ r hr h1⟩)
  have hθW : ∀ w (hw : w ∈ W), θ ⟨w, hWN' hw⟩ = 1 := by
    intro w hw
    refine MulEquiv.ext fun v => ?_
    obtain ⟨x, rfl⟩ := hπ v
    have hx : w * (x : G) * w⁻¹ ∈ W := W.mul_mem (W.mul_mem hw x.2) (W.inv_mem hw)
    rw [hπθ ⟨w, hWN' hw⟩ x hx, MulAut.one_apply]
    have : (⟨w * (x : G) * w⁻¹, hx⟩ : W) = ⟨w, hw⟩ * x * ⟨w, hw⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hEc (π ⟨w, hw⟩) (π x), mul_inv_cancel_right]
  have h60 : 60 ∣ Nat.card κ.range := sixty_dvd_card_range hK κ hθK
  set N₀ : Subgroup (MulAut E) := ((R ⊓ K).subgroupOf N).map θ with hN₀def
  have hN₀2 : IsPGroup 2 N₀ := by
    have h1 : IsPGroup 2 ((R ⊓ K).subgroupOf N) :=
      (hR2.to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hRN)).symm
    exact h1.map θ
  have hN₀K : N₀ ≤ κ.range := by
    rintro _ ⟨y, hy, rfl⟩
    have hyK : (y : G) ∈ K := (Subgroup.mem_subgroupOf.mp hy).2
    exact ⟨⟨y, hyK⟩, rfl⟩
  have hN₀n : ∀ k : K, ∀ n ∈ N₀, κ k * n * (κ k)⁻¹ ∈ N₀ := by
    rintro k _ ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_subgroupOf.mp hy
    refine ⟨Subgroup.inclusion hKN k * y * (Subgroup.inclusion hKN k)⁻¹,
      Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hKR k.2) _).mp hy'.1
    · exact K.mul_mem (K.mul_mem k.2 hy'.2) (K.inv_mem k.2)
    · simp [κ, map_mul, map_inv]
  have hscal : ∀ a (ha : a ∈ R), a * a = 1 →
      θ ⟨a, hRN ha⟩ = 1 ∨ ∀ v, θ ⟨a, hRN ha⟩ v = v⁻¹ := by
    intro a ha ha2
    refine eq_one_or_eq_inv_of_comm hK hEc hE5 hE25 κ hθK N₀ hN₀2 hN₀K hN₀n _ ?_ ?_
    · rw [← map_mul]
      have : (⟨a, hRN ha⟩ : N) * ⟨a, hRN ha⟩ = 1 := Subtype.ext ha2
      rw [this, map_one]
    · intro k
      refine ⟨⟨a, hRN ha⟩ * Subgroup.inclusion hKN k * ⟨a, hRN ha⟩⁻¹ *
        (Subgroup.inclusion hKN k)⁻¹, Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩, ?_⟩
      · have h1 : (k : G) * a⁻¹ * (k : G)⁻¹ ∈ R :=
          (Subgroup.mem_normalizer_iff.mp (hKR k.2) _).mp (R.inv_mem ha)
        have := R.mul_mem ha h1
        simpa [mul_assoc] using this
      · have h1 : a * (k : G) * a⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hRK ha) _).mp k.2
        exact K.mul_mem h1 (K.inv_mem k.2)
      · simp [κ, map_mul, map_inv]
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAR, hAab, hAcard⟩ := hA
  by_contra hAC
  obtain ⟨e, heA, heC⟩ := SetLike.not_le_iff_exists.mp hAC
  have heR : e ∈ R := hAR heA
  have he2 : e * e = 1 := hAab.mul_self_eq_one heA
  have hθe : ∀ v, θ ⟨e, hRN heR⟩ v = v⁻¹ := by
    rcases hscal e heR he2 with h | h
    · exact absurd (hθCV e heR h) heC
    · exact h
  have hA2 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 2 := by
    set φ : ↥A →* MulAut E := θ.comp (Subgroup.inclusion (hAR.trans hRN)) with hφ
    have hker : φ.ker ≤ (A ⊓ Subgroup.centralizer (V : Set G)).subgroupOf A := by
      intro a ha
      refine Subgroup.mem_subgroupOf.mpr ⟨a.2, hθCV a (hAR a.2) ?_⟩
      exact MonoidHom.mem_ker.mp ha
    have hrange : φ.range ≤ Subgroup.zpowers (θ ⟨e, hRN heR⟩) := by
      rintro _ ⟨a, rfl⟩
      rcases hscal a (hAR a.2) (hAab.mul_self_eq_one a.2) with h | h
      · change θ (Subgroup.inclusion _ a) ∈ _
        have : θ (Subgroup.inclusion (hAR.trans hRN) a) = 1 := h
        rw [this]
        exact Subgroup.one_mem _
      · have : θ (Subgroup.inclusion (hAR.trans hRN) a) = θ ⟨e, hRN heR⟩ :=
          MulEquiv.ext fun v => (h v).trans (hθe v).symm
        change θ (Subgroup.inclusion _ a) ∈ _
        rw [this]
        exact Subgroup.mem_zpowers _
    have horder : orderOf (θ ⟨e, hRN heR⟩) ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [pow_two, ← map_mul]
      have : (⟨e, hRN heR⟩ : N) * ⟨e, hRN heR⟩ = 1 := Subtype.ext he2
      rw [this, map_one]
    have hcard : Nat.card φ.range ≤ 2 := by
      refine (Subgroup.card_le_of_le hrange).trans ?_
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd (by norm_num) horder
    calc (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A
        ≤ φ.ker.index := by
          refine Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_
          exact Subgroup.index_dvd_of_le hker
      _ = Nat.card φ.range := Subgroup.index_ker φ
      _ ≤ 2 := hcard
  have hm : ∀ B : Subgroup G, B ≤ R → IsElemAbelian 2 B → Nat.card B ≤ 2 * Nat.card A := by
    intro B hBR hB
    obtain ⟨k, hk⟩ := hB.isPGroup.exists_card_eq
    have hkR : k ≤ CFSG.Open.pRank 2 R := CFSG.SectionRank.le_pRank Nat.one_lt_two hBR hB hk
    rw [hk]
    calc 2 ^ k ≤ 2 ^ CFSG.Open.pRank 2 R := Nat.pow_le_pow_right (by norm_num) hkR
      _ ≤ 2 * 2 ^ (CFSG.Open.pRank 2 R - 1) := by
          rcases Nat.eq_zero_or_pos (CFSG.Open.pRank 2 R) with h | h
          · rw [h]; norm_num
          · obtain ⟨j, hj⟩ : ∃ j, CFSG.Open.pRank 2 R = j + 1 :=
              ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
            rw [hj, pow_succ, Nat.add_sub_cancel, mul_comm]
      _ ≤ 2 * Nat.card A := Nat.mul_le_mul_left 2 hAcard
  have hVA : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ 4 := by
    have h := relIndex_centralizer_le_two_mul (V := V) hVab hVR hAab hAR hm
    have h2 : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤ 2 := hA2
    omega
  have hVe : (V ⊓ Subgroup.centralizer ({e} : Set G)).relIndex V ≤ 4 := by
    refine (Subgroup.relIndex_le_of_le_left ?_ Subgroup.index_ne_zero_of_finite).trans hVA
    exact inf_le_inf_left V (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr heA))
  have hCWπ : ∀ x : W, (x : G) ∈ Subgroup.centralizer (V : Set G) → π x = 1 := by
    set X : Subgroup E := ((W ⊓ Subgroup.centralizer (V : Set G)).subgroupOf W).map π with hX
    have hXinv : ∀ k : K, ∀ x ∈ X, κ k x ∈ X := by
      rintro k _ ⟨y, hy, rfl⟩
      have hy' := Subgroup.mem_subgroupOf.mp hy
      have hky : (k : G) * y * (k : G)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hKW k.2) _).mp y.2
      refine ⟨⟨_, hky⟩, Subgroup.mem_subgroupOf.mpr ⟨hky, conj_mem_centralizer (hKV k.2) hy'.2⟩,
        ?_⟩
      exact (hπθ (Subgroup.inclusion hKN k) y hky).symm
    rcases eq_bot_or_eq_top_of_invariant hEc hE5 hE25 κ hθK X hXinv with hXb | hXt
    · intro x hx
      have : π x ∈ X := ⟨x, Subgroup.mem_subgroupOf.mpr ⟨x.2, hx⟩, rfl⟩
      rw [hXb] at this
      exact Subgroup.mem_bot.mp this
    · exfalso
      have hWC : W ≤ W ⊓ Subgroup.centralizer (V : Set G) := by
        refine hBB _ (le_inf hQW hQV) inf_le_left fun v => ?_
        have hv : v ∈ X := hXt ▸ Subgroup.mem_top v
        obtain ⟨y, hy, rfl⟩ := hv
        exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
      have hHC : H ≤ Subgroup.centralizer (V : Set G) := by
        refine hVred H le_rfl Subgroup.le_normalizer fun h hh => ?_
        obtain ⟨n, hn⟩ := exists_pow_mem_of_mem_sup hRW hR2 hh
        exact ⟨n, (hWC hn).2⟩
      exact heC (hHC (hRH heR))
  obtain ⟨v₁, v₂, hv⟩ := exists_closure_pair_eq_top hE5 hE25
  obtain ⟨x₁, hx₁⟩ := hπ v₁
  obtain ⟨x₂, hx₂⟩ := hπ v₂
  have heW : ∀ x : W, e * (x : G) * e⁻¹ ∈ W := fun x =>
    (Subgroup.mem_normalizer_iff.mp (hRW heR) _).mp x.2
  have hyW : ∀ x : W, (x : G)⁻¹ * e * x * e⁻¹ ∈ W := fun x => by
    have := W.mul_mem (W.inv_mem x.2) (heW x)
    rwa [show (x : G)⁻¹ * (e * x * e⁻¹) = (x : G)⁻¹ * e * x * e⁻¹ by group] at this
  have hπy : ∀ x : W, π ⟨_, hyW x⟩ = (π x)⁻¹ * (π x)⁻¹ := by
    intro x
    have h1 : (⟨(x : G)⁻¹ * e * x * e⁻¹, hyW x⟩ : W) = x⁻¹ * ⟨e * x * e⁻¹, heW x⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [h1, map_mul, map_inv, ← hπθ ⟨e, hRN heR⟩ x (heW x), hθe]
  have hsq : ∀ v : E, (v⁻¹ * v⁻¹) ^ 2 = v := by
    intro v
    calc (v⁻¹ * v⁻¹) ^ 2 = v⁻¹ ^ 4 := by group
      _ = v⁻¹ ^ 4 * v ^ 5 := by rw [hE5, mul_one]
      _ = v := by group
  set Y : Subgroup G := Subgroup.closure ({(x₁ : G)⁻¹ * e * x₁ * e⁻¹,
    (x₂ : G)⁻¹ * e * x₂ * e⁻¹} : Set G) ⊔ Q with hYdef
  have hy₁Y : (x₁ : G)⁻¹ * e * x₁ * e⁻¹ ∈ Y :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert _ _))
  have hy₂Y : (x₂ : G)⁻¹ * e * x₂ * e⁻¹ ∈ Y :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hWY : W ≤ Y := by
    refine hBB Y le_sup_right (sup_le ((Subgroup.closure_le _).mpr ?_) hQW) fun v => ?_
    · intro g hg
      rcases Set.mem_insert_iff.mp hg with h | h
      · rw [h]; exact hyW x₁
      · rw [Set.mem_singleton_iff.mp h]; exact hyW x₂
    · set Z : Subgroup E := (Y.subgroupOf W).map π with hZ
      have hmem : ∀ x : W, (x : G)⁻¹ * e * x * e⁻¹ ∈ Y → π x ∈ Z := by
        intro x hx
        refine ⟨⟨_, hyW x⟩ ^ 2, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
        · exact Y.pow_mem hx 2
        · rw [map_pow, hπy, hsq]
      have hZt : Z = ⊤ := by
        rw [eq_top_iff, ← hv, Subgroup.closure_le]
        intro g hg
        rcases Set.mem_insert_iff.mp hg with h | h
        · rw [h, ← hx₁]; exact hmem x₁ hy₁Y
        · rw [Set.mem_singleton_iff.mp h, ← hx₂]; exact hmem x₂ hy₂Y
      have : v ∈ Z := hZt ▸ Subgroup.mem_top v
      obtain ⟨y, hy, rfl⟩ := this
      exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hey : ∀ x : W, e * ((x : G)⁻¹ * e * x * e⁻¹) * e⁻¹ = ((x : G)⁻¹ * e * x * e⁻¹)⁻¹ := by
    intro x
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
    rw [hei]
    calc e * ((x : G)⁻¹ * e * x * e) * e = e * (x : G)⁻¹ * e * x * (e * e) := by group
      _ = e * (x : G)⁻¹ * e * x := by rw [he2, mul_one]
      _ = ((x : G)⁻¹ * e * x * e)⁻¹ := by simp only [mul_inv_rev, inv_inv, hei, mul_assoc]
  have hVy : ∀ x : W, (V ⊓ Subgroup.centralizer ({(x : G)⁻¹ * e * x * e⁻¹} : Set G)).relIndex V ≤
      16 := by
    intro x
    obtain ⟨a, ha⟩ := hW5 _ (hyW x)
    have h := relIndex_centralizer_le_sq (V := V) (hVn (hWH (hyW x))) he2 (hey x)
      (Odd.pow (by decide : Odd 5) : Odd (5 ^ a)) (hQV ha)
    calc _ ≤ ((V ⊓ Subgroup.centralizer ({e} : Set G)).relIndex V) ^ 2 := h
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left hVe 2
      _ = 16 := by norm_num
  have hidx : (V ⊓ Subgroup.centralizer (W : Set G)).relIndex V ≤ 2 ^ 8 := by
    have hle : (V ⊓ Subgroup.centralizer ({(x₁ : G)⁻¹ * e * x₁ * e⁻¹} : Set G)) ⊓
        (V ⊓ Subgroup.centralizer ({(x₂ : G)⁻¹ * e * x₂ * e⁻¹} : Set G)) ≤
        V ⊓ Subgroup.centralizer (W : Set G) := by
      intro v hv
      have h1 := Subgroup.mem_inf.mp hv
      have hvV : v ∈ V := (Subgroup.mem_inf.mp h1.1).1
      have hv1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1.1).2
      have hv2 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp h1.2).2
      refine Subgroup.mem_inf.mpr ⟨hvV, ?_⟩
      have hYc : Y ≤ Subgroup.centralizer ({v} : Set G) := by
        refine sup_le ((Subgroup.closure_le _).mpr ?_) fun q hq => ?_
        · intro g hg
          have hgv : v * g = g * v := by
            rcases Set.mem_insert_iff.mp hg with h | h
            · rw [h]; exact (hv1 _ (Set.mem_singleton _)).symm
            · rw [Set.mem_singleton_iff.mp h]; exact (hv2 _ (Set.mem_singleton _)).symm
          exact Subgroup.mem_centralizer_iff.mpr fun g' hg' => by
            rw [Set.mem_singleton_iff.mp hg']; exact hgv
        · exact Subgroup.mem_centralizer_iff.mpr fun g' hg' => by
            rw [Set.mem_singleton_iff.mp hg']
            exact Subgroup.mem_centralizer_iff.mp (hQV hq) _ hvV
      exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
        (Subgroup.mem_centralizer_iff.mp (hYc (hWY hw)) v (Set.mem_singleton _)).symm
    calc (V ⊓ Subgroup.centralizer (W : Set G)).relIndex V
        ≤ ((V ⊓ Subgroup.centralizer ({(x₁ : G)⁻¹ * e * x₁ * e⁻¹} : Set G)) ⊓
            (V ⊓ Subgroup.centralizer ({(x₂ : G)⁻¹ * e * x₂ * e⁻¹} : Set G))).relIndex V :=
          Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
      _ ≤ (V ⊓ Subgroup.centralizer ({(x₁ : G)⁻¹ * e * x₁ * e⁻¹} : Set G)).relIndex V *
            (V ⊓ Subgroup.centralizer ({(x₂ : G)⁻¹ * e * x₂ * e⁻¹} : Set G)).relIndex V :=
          Subgroup.relIndex_inf_le
      _ ≤ 16 * 16 := Nat.mul_le_mul (hVy x₁) (hVy x₂)
      _ = 2 ^ 8 := by norm_num
  obtain ⟨k, hk1, b, hkb⟩ := exists_pow_five_pow_eq_one κ (Nat.dvd_trans (by norm_num) h60)
  refine false_of_five_cube (V := V) (W := W) (k := (k : G)) hVab (hWH.trans hVn) (hKV k.2)
    (hKW k.2) (fun w hw => ?_) ⟨b, ?_⟩ hidx ?_ ?_
  · obtain ⟨a, ha⟩ := hW5 w hw
    exact ⟨a, hQV ha⟩
  · have : (k : G) ^ (5 ^ b) = 1 := by simpa using congrArg Subtype.val hkb
    rw [this]
    exact Subgroup.one_mem _
  ·
    have hker : (W ⊓ Subgroup.centralizer (V : Set G)).subgroupOf W ≤ π.ker := fun x hx =>
      MonoidHom.mem_ker.mpr (hCWπ x (Subgroup.mem_subgroupOf.mp hx).2)
    have h1 : π.ker.index = 25 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ, Subgroup.card_top, hE25]
    have h2 : π.ker.index ∣ (W ⊓ Subgroup.centralizer (V : Set G)).relIndex W :=
      Subgroup.index_dvd_of_le hker
    rw [h1] at h2
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) h2
  ·
    intro w hw hall
    apply hk1
    have hkw : (k : G) * w⁻¹ ∈ N := N.mul_mem (hKN k.2) (N.inv_mem (hWN' hw))
    have h1 : θ ⟨(k : G) * w⁻¹, hkw⟩ = 1 := by
      refine MulEquiv.ext fun v => ?_
      obtain ⟨x, rfl⟩ := hπ v
      have hxW : (k : G) * w⁻¹ * x * ((k : G) * w⁻¹)⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hWN hkw) _).mp x.2
      have hcW : (k : G) * w⁻¹ * x * ((k : G) * w⁻¹)⁻¹ * (x : G)⁻¹ ∈ W :=
        W.mul_mem hxW (W.inv_mem x.2)
      rw [hπθ ⟨_, hkw⟩ x hxW, MulAut.one_apply]
      have h2 : (⟨_, hxW⟩ : W) = ⟨_, hcW⟩ * x := Subtype.ext (by simp)
      rw [h2, map_mul, hCWπ _ (hall x x.2), one_mul]
    have h3 : (Subgroup.inclusion hKN k : N) = ⟨(k : G) * w⁻¹, hkw⟩ * ⟨w, hWN' hw⟩ :=
      Subtype.ext (by simp)
    change θ (Subgroup.inclusion hKN k) = 1
    rw [h3, map_mul, h1, hθW w hw, mul_one]

end CFSG.RankThree.PartTwo.Sec20.SimsYKO3
