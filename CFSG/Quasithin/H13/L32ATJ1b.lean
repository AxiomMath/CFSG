module

public import CFSG.Quasithin.H13.L32ATJ1a
public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace TJ1

theorem pCoreOf_inf_le {A X : Subgroup G} (hXA : X ≤ A) : pCoreOf 2 A ⊓ X ≤ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_pCoreOf 2 A (hXA hx), Subgroup.le_normalizer hx⟩)
    ((pCoreOf_isPGroup 2 A).to_le inf_le_left)

theorem normalizer_le_normalizer_D (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (omegaOneCenterOf (thompsonJi R 1) : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf (thompsonJi X 1))
    (fun φ X => by
      show (omegaOneCenterOf (thompsonJi X 1)).map φ.toMonoidHom =
        omegaOneCenterOf (thompsonJi (X.map φ.toMonoidHom) 1)
      rw [omegaOneCenterOf_map_mulEquiv, thompsonJi_map_mulEquiv151]) R

theorem thompsonJi_le' (R : Subgroup G) (i : ℕ) : thompsonJi R i ≤ R :=
  iSup₂_le fun _ hB => hB.1

theorem mem_pCoreOf_of_centralizes {X Y R : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X)
    {r : G} (hr : r ∈ R) (hry : ∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ pCoreOf 2 Y) :
    r ∈ pCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 Y with hOdef
  have hRX : R ≤ X := hR.1
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    hXY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hOW : O ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYX) hXO (pCoreOf_isPGroup 2 Y)
  have hOR : O ≤ R := hOW.trans (pCoreOf_two_le_of_sylowIn hRX hR.2.1 hR.2.2)
  have hcO : ∀ g ∈ X, ∀ c ∈ O, g * c * g⁻¹ ∈ O := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hXO hg) c).mp hc
  have hcY : ∀ g ∈ X, ∀ c ∈ Y, g * c * g⁻¹ ∈ Y := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hXY hg) c).mp hc
  let K : Subgroup G :=
    { carrier := {r | r ∈ R ∧ ∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ O}
      one_mem' := ⟨R.one_mem, fun y _ => by simp⟩
      mul_mem' := by
        rintro r₁ r₂ ⟨h₁R, h₁⟩ ⟨h₂R, h₂⟩
        refine ⟨R.mul_mem h₁R h₂R, fun y hy => ?_⟩
        have e : r₁ * r₂ * y * (r₁ * r₂)⁻¹ * y⁻¹ =
            (r₁ * (r₂ * y * r₂⁻¹ * y⁻¹) * r₁⁻¹) * (r₁ * y * r₁⁻¹ * y⁻¹) := by group
        rw [e]
        exact O.mul_mem (hcO r₁ (hRX h₁R) _ (h₂ y hy)) (h₁ y hy)
      inv_mem' := by
        rintro r ⟨hrR, hr⟩
        refine ⟨R.inv_mem hrR, fun y hy => ?_⟩
        have hy' : r⁻¹ * y * r ∈ Y := by
          have := hcY r⁻¹ (hRX (R.inv_mem hrR)) y hy
          simpa using this
        have h1 := O.inv_mem (hr _ hy')
        have e : r⁻¹ * y * r⁻¹⁻¹ * y⁻¹ = (r * (r⁻¹ * y * r) * r⁻¹ * (r⁻¹ * y * r)⁻¹)⁻¹ := by
          group
        rw [e]
        exact h1 }
  have hKR : K ≤ R := fun r hr => hr.1
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := by
    rw [hXYR]
    refine sup_le (fun y₀ hy₀ => ?_) (fun s hs => ?_)
    · refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      obtain ⟨hrR, hry⟩ := hr
      have h1 : r⁻¹ * y₀ * r⁻¹⁻¹ * y₀⁻¹ ∈ O := (K.inv_mem ⟨hrR, hry⟩).2 y₀ hy₀
      refine ⟨?_, fun y hy => ?_⟩
      · rw [show y₀ * r * y₀⁻¹ = r * (r⁻¹ * y₀ * r⁻¹⁻¹ * y₀⁻¹) by group]
        exact R.mul_mem hrR (hOR h1)
      · have hy' : y₀⁻¹ * y * y₀ ∈ Y := Y.mul_mem (Y.mul_mem (Y.inv_mem hy₀) hy) hy₀
        have h2 := hry _ hy'
        have e : y₀ * r * y₀⁻¹ * y * (y₀ * r * y₀⁻¹)⁻¹ * y⁻¹ =
            y₀ * (r * (y₀⁻¹ * y * y₀) * r⁻¹ * (y₀⁻¹ * y * y₀)⁻¹) * y₀⁻¹ := by group
        rw [e]
        exact hcO y₀ (hYX hy₀) _ h2
    · refine Subgroup.mem_normalizer_fintype fun r hr => ?_
      obtain ⟨hrR, hry⟩ := hr
      refine ⟨R.mul_mem (R.mul_mem hs hrR) (R.inv_mem hs), fun y hy => ?_⟩
      have hy' : s⁻¹ * y * s ∈ Y := by
        have := hcY s⁻¹ (hRX (R.inv_mem hs)) y hy
        simpa using this
      have h2 := hry _ hy'
      have e : s * r * s⁻¹ * y * (s * r * s⁻¹)⁻¹ * y⁻¹ =
          s * (r * (s⁻¹ * y * s) * r⁻¹ * (s⁻¹ * y * s)⁻¹) * s⁻¹ := by group
      rw [e]
      exact hcO s (hRX hs) _ h2
  have hKW : K ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 (hKR.trans hRX) hXK (hR.2.1.to_le hKR)
  exact hKW ⟨hr, hry⟩

theorem inverts_of_not_mem {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) {a : G} (haR : a ∈ R) (haW : a ∉ pCoreOf 2 X)
    (ha2 : a ^ 2 ∈ pCoreOf 2 X) {y : G} (hy : y ∈ Y) : y * (a * y * a⁻¹) ∈ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 Y with hOdef
  set W := pCoreOf 2 X with hWdef
  have hRX : R ≤ X := hR.1
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    hXY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hcO : ∀ g ∈ X, ∀ c ∈ O, g * c * g⁻¹ ∈ O := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hXO hg) c).mp hc
  have hcY : ∀ g ∈ X, ∀ c ∈ Y, g * c * g⁻¹ ∈ Y := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hXY hg) c).mp hc
  have hWY : ∀ w ∈ W, ∀ y ∈ Y, w * y * w⁻¹ * y⁻¹ ∈ O := fun w hw y hy => by
    refine pCoreOf_inf_le hYX ⟨?_, ?_⟩
    · rw [show w * y * w⁻¹ * y⁻¹ = w * (y * w⁻¹ * y⁻¹) by group]
      exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X (hYX hy))
        _).mp (W.inv_mem hw))
    · exact Y.mul_mem (hcY w (pCoreOf_le 2 X hw) y hy) (Y.inv_mem hy)
  let F : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ a * y * a⁻¹ * y⁻¹ ∈ O}
      one_mem' := ⟨Y.one_mem, by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁Y, h₁⟩ ⟨h₂Y, h₂⟩
        refine ⟨Y.mul_mem h₁Y h₂Y, ?_⟩
        have e : a * (y₁ * y₂) * a⁻¹ * (y₁ * y₂)⁻¹ =
            (a * y₁ * a⁻¹ * y₁⁻¹) * (y₁ * (a * y₂ * a⁻¹ * y₂⁻¹) * y₁⁻¹) := by group
        rw [e]
        exact O.mul_mem h₁ (hcO y₁ (hYX h₁Y) _ h₂)
      inv_mem' := by
        rintro y ⟨hyY, hy⟩
        refine ⟨Y.inv_mem hyY, ?_⟩
        have e : a * y⁻¹ * a⁻¹ * y⁻¹⁻¹ = y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e]
        exact hcO y⁻¹ (hYX (Y.inv_mem hyY)) _ (O.inv_mem hy) }
  have hOF : O ≤ F := fun o ho => by
    refine ⟨pCoreOf_le 2 Y ho, O.mul_mem (hcO a (hRX haR) o ho) (O.inv_mem ho)⟩
  have hFY : F ≤ Y := fun y hy => hy.1
  rcases TJ1.eq_or_eq_of_relIndex_prime hp hYp hOF hFY with hF | hF
  ·
    have hay : a * y * a⁻¹ ∈ Y := hcY a (hRX haR) y hy
    have hz : y * (a * y * a⁻¹) ∈ F := by
      refine ⟨Y.mul_mem hy hay, ?_⟩
      have e : a * (y * (a * y * a⁻¹)) * a⁻¹ * (y * (a * y * a⁻¹))⁻¹ =
          (a * y * a⁻¹) * ((a ^ 2) * y * (a ^ 2)⁻¹ * y⁻¹) * (a * y * a⁻¹)⁻¹ *
            ((a * y * a⁻¹) * y * (a * y * a⁻¹)⁻¹ * y⁻¹) := by group
      rw [e]
      have h1 := hcO (a * y * a⁻¹) (hYX hay) _ (hWY _ ha2 y hy)
      exact O.mul_mem h1 (TJ1.comm_mem_of_relIndex_prime hp hYp hay hy)
    rw [hF] at hz
    exact hz
  ·
    exfalso
    exact haW (mem_pCoreOf_of_centralizes hYX hXY hXYR hR haR fun y hy => by
      have : y ∈ F := hF ▸ hy
      exact this.2)

theorem comm_not_mem {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) {a : G} (haR : a ∈ R) (haW : a ∉ pCoreOf 2 X)
    (ha2 : a ^ 2 ∈ pCoreOf 2 X) {y : G} (hy : y ∈ Y) (hyO : y ∉ pCoreOf 2 Y) :
    a * y * a⁻¹ * y⁻¹ ∉ pCoreOf 2 Y := by
  intro hc
  have h1 := inverts_of_not_mem hp hYX hXY hYp hXYR hR haR haW ha2 hy
  have hXO : X ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hXY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hy2 : y ^ 2 ∈ pCoreOf 2 Y := by
    have e : y ^ 2 = (y * (a * y * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹ * y⁻¹)⁻¹ * y) := by
      rw [pow_two]; group
    rw [e]
    refine (pCoreOf 2 Y).mul_mem h1 ?_
    have := (Subgroup.mem_normalizer_iff.mp (hXO (hYX (Y.inv_mem hy))) _).mp
      ((pCoreOf 2 Y).inv_mem hc)
    simpa using this
  exact TJ1.pow_not_mem_of_coprime hYp hy hyO
    ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)) hy2

theorem mul_mem_of_not_mem {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) {a b : G} (haR : a ∈ R) (haW : a ∉ pCoreOf 2 X)
    (ha2 : a ^ 2 ∈ pCoreOf 2 X) (hbR : b ∈ R) (hbW : b ∉ pCoreOf 2 X)
    (hb2 : b ^ 2 ∈ pCoreOf 2 X) : a * b ∈ pCoreOf 2 X := by
  have hRX : R ≤ X := hR.1
  have hXO : X ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hXY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hcO : ∀ g ∈ X, ∀ c ∈ pCoreOf 2 Y, g * c * g⁻¹ ∈ pCoreOf 2 Y := fun g hg c hc =>
    (Subgroup.mem_normalizer_iff.mp (hXO hg) c).mp hc
  refine mem_pCoreOf_of_centralizes hYX hXY hXYR hR (R.mul_mem haR hbR) fun y hy => ?_
  have h1 := inverts_of_not_mem hp hYX hXY hYp hXYR hR hbR hbW hb2 hy
  have h2 := inverts_of_not_mem hp hYX hXY hYp hXYR hR haR haW ha2 (Y.inv_mem hy)
  have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
      y * ((y⁻¹ * (a * y⁻¹ * a⁻¹)) * (a * (y * (b * y * b⁻¹)) * a⁻¹)) * y⁻¹ := by group
  rw [e]
  exact hcO y (hYX hy) _ ((pCoreOf 2 Y).mul_mem h2 (hcO a (hRX haR) _ h1))

omit [Finite G] in
theorem zpow_eq_one_or_self {a : G} (ha2 : a ^ 2 = 1) (k : ℤ) : a ^ k = 1 ∨ a ^ k = a := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, k = 2 * q ∨ k = 2 * q + 1 := ⟨k / 2, by omega⟩
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_ofNat]; exact ha2
  rcases hq with rfl | rfl
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem card_eq_two_mul_inf {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) {A : Subgroup G} (hAR : A ≤ R)
    (hA : IsElemAbelian 2 A) {a : G} (haA : a ∈ A) (haW : a ∉ pCoreOf 2 X) :
    Nat.card A = 2 * Nat.card ↥(A ⊓ pCoreOf 2 X) := by
  set W := pCoreOf 2 X with hWdef
  have hW1 : (1 : G) ∈ W := W.one_mem
  have ha2 : a ^ 2 = 1 := hA.2 a haA
  have ha2W : a ^ 2 ∈ W := by rw [ha2]; exact hW1
  have hainv : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have hZ : ∀ x ∈ Subgroup.zpowers a, x = 1 ∨ x = a := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact zpow_eq_one_or_self ha2 k
  have hcomm : ∀ x ∈ A ⊓ W, ∀ y ∈ Subgroup.zpowers a, x * y = y * x := fun x hx y hy => by
    rcases hZ y hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact comm_of_isElemAbelian hA hx.1 haA
  have hn := le_normalizer_of_commute hcomm
  have hsup : (A ⊓ W) ⊔ Subgroup.zpowers a = A := by
    apply le_antisymm (sup_le inf_le_left (Subgroup.zpowers_le.mpr haA))
    intro b hbA
    by_cases hbW : b ∈ W
    · exact Subgroup.mem_sup_left ⟨hbA, hbW⟩
    · have hb2W : b ^ 2 ∈ W := by rw [hA.2 b hbA]; exact hW1
      have hab : a * b ∈ W :=
        mul_mem_of_not_mem hp hYX hXY hYp hXYR hR (hAR haA) haW ha2W (hAR hbA) hbW hb2W
      rw [show b = (a * b) * a⁻¹ by rw [comm_of_isElemAbelian hA haA hbA]; group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨A.mul_mem haA hbA, hab⟩)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ (Subgroup.mem_zpowers a)))
  have hinf : (A ⊓ W) ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hZ x hx.2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hx.1.2 haW
  have ha1 : a ≠ 1 := fun h => haW (h ▸ hW1)
  have hcz : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha2 ha1
  have h := card_sup_mul_card_inf hn
  rw [hsup, hinf, Subgroup.card_bot, mul_one, hcz] at h
  rw [h, mul_comm]

@[expose] def wOne (R W : Subgroup G) : Subgroup G :=
  ⨆ (B : Subgroup G) (_ : IsElemAbelianCorank R 1 B ∧ B ≤ W), B

theorem wOne_le (R W : Subgroup G) : wOne R W ≤ W := iSup₂_le fun _ hB => hB.2

theorem le_wOne {R W B : Subgroup G} (hB : IsElemAbelianCorank R 1 B) (hBW : B ≤ W) :
    B ≤ wOne R W :=
  le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsElemAbelianCorank R 1 B ∧ B ≤ W) => B) B
    ⟨hB, hBW⟩ le_rfl

theorem wOne_le_thompsonJi (R W : Subgroup G) : wOne R W ≤ thompsonJi R 1 :=
  iSup₂_le fun B hB => le_iSup₂_of_le
    (f := fun (A : Subgroup G) (_ : IsElemAbelianCorank R 1 A) => A) B hB.1 le_rfl

theorem le_normalizer_wOne {X R W : Subgroup G} (hWR : W ≤ R)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) :
    X ≤ Subgroup.normalizer (wOne R W : Set G) := by
  intro x hx
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hle : wOne R W ≤ (wOne R W).comap (MulAut.conj x).toMonoidHom := by
    refine iSup₂_le fun B hB => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hmapW : B.map (MulAut.conj x).toMonoidHom ≤ W := by
      rintro _ ⟨b, hb, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hXW hx) b).mp (hB.2 hb)
    refine le_wOne ⟨hmapW.trans hWR, ?_, ?_⟩ hmapW
    · refine isElemAbelian_of_forall' (fun u hu v hv => ?_) fun u hu => ?_
      · obtain ⟨b, hb, rfl⟩ := hu
        obtain ⟨c, hc, rfl⟩ := hv
        rw [← map_mul, ← map_mul, comm_of_isElemAbelian hB.1.2.1 hb hc]
      · obtain ⟨b, hb, rfl⟩ := hu
        rw [← map_pow, hB.1.2.1.2 b hb, map_one]
    · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
      exact hB.1.2.2
  have := hle hw
  simpa [MulAut.conj_apply] using this

theorem mem_wOne_of_comm {R W : Subgroup G} (hWR : W ≤ R) (hm : 2 ≤ CFSG.Open.pRank 2 R)
    {B₀ : Subgroup G} (hB₀ : IsElemAbelianCorank R 1 B₀) (hB₀W : B₀ ≤ W) {c : G} (hcW : c ∈ W)
    (hc2 : c ^ 2 = 1) (hcW' : ∀ w ∈ wOne R W, c * w = w * c) : c ∈ wOne R W := by
  by_cases hcB : c ∈ B₀
  · exact le_wOne hB₀ hB₀W hcB
  set m := CFSG.Open.pRank 2 R with hmdef
  have hcard : Nat.card B₀ = 2 ^ (m - 1) := by
    have h := hB₀.2.2
    rw [pow_one, ← hmdef] at h
    have : 2 ^ m = 2 ^ (m - 1) * 2 := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    omega
  obtain ⟨K, hKc, -, hKB⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := m - 2) (H := ⊥) (L := B₀) (by rw [Subgroup.card_bot]; exact one_dvd _)
    (by rw [hcard]; exact pow_dvd_pow 2 (by omega)) bot_le
  have hZ : ∀ x ∈ Subgroup.zpowers c, x = 1 ∨ x = c := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact zpow_eq_one_or_self hc2 k
  have hcomm : ∀ x ∈ K, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := fun x hx y hy => by
    rcases hZ y hy with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (hcW' x (le_wOne hB₀ hB₀W (hKB hx))).symm
  have hKe : IsElemAbelian 2 K := isElemAbelian_of_le hKB hB₀.2.1
  have hZe : IsElemAbelian 2 (Subgroup.zpowers c) :=
    isElemAbelian_of_forall' (fun x hx y hy => by
      rcases hZ x hx with rfl | rfl <;> rcases hZ y hy with rfl | rfl <;> simp)
      fun x hx => by rcases hZ x hx with rfl | rfl <;> simp [hc2]
  have hBe := isElemAbelian_sup hKe hZe hcomm
  have hinf : K ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hZ x hx.2 with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd (hKB hx.1) hcB
  have hc1 : c ≠ 1 := fun h => hcB (h ▸ B₀.one_mem)
  have hcz : Nat.card (Subgroup.zpowers c) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hc2 hc1
  have h := card_sup_mul_card_inf (le_normalizer_of_commute hcomm)
  rw [hinf, Subgroup.card_bot, mul_one, hcz, hKc] at h
  have hB' : IsElemAbelianCorank R 1 (K ⊔ Subgroup.zpowers c) := by
    refine ⟨sup_le (hKB.trans hB₀.1) (Subgroup.zpowers_le.mpr (hWR hcW)), hBe, ?_⟩
    rw [h, pow_one, ← hmdef, mul_assoc, show (2 : ℕ) * 2 = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  have hBW : K ⊔ Subgroup.zpowers c ≤ W :=
    sup_le (hKB.trans hB₀W) (Subgroup.zpowers_le.mpr hcW)
  exact le_wOne hB' hBW (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

theorem omegaOneCenterOf_J1_le {X R : Subgroup G} (hR : IsSylowTwoOf R X) (hchar : CharTwo X)
    (hm : 2 ≤ CFSG.Open.pRank 2 R) {B₀ : Subgroup G} (hB₀ : IsElemAbelianCorank R 1 B₀)
    (hB₀W : B₀ ≤ pCoreOf 2 X) :
    omegaOneCenterOf (thompsonJi R 1) ≤ omegaOneCenterOf (wOne R (pCoreOf 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := pCoreOf 2 X with hWdef
  set W' := wOne R W with hW'def
  set D := omegaOneCenterOf (thompsonJi R 1) with hDdef
  have hRX : R ≤ X := hR.1
  have hWR : W ≤ R := pCoreOf_two_le_of_sylowIn hRX hR.2.1 hR.2.2
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := le_normalizer_pCoreOf 2 X
  have hW2 : IsPGroup 2 W := pCoreOf_isPGroup 2 X
  have hW'W : W' ≤ W := wOne_le R W
  have hXW' : X ≤ Subgroup.normalizer (W' : Set G) := le_normalizer_wOne hWR hXW
  have hDc : D ≤ centerOf (thompsonJi R 1) := B2F.omegaOneCenterOf_le_centerOf _
  have hDR : D ≤ R := (hDc.trans inf_le_left).trans (thompsonJi_le' R 1)
  have hDe : IsElemAbelian 2 D := B2F.isElemAbelian_omegaOneCenterOf _
  have hDW' : ∀ δ ∈ D, ∀ w ∈ W', δ * w = w * δ := fun δ hδ w hw =>
    (Subgroup.mem_centralizer_iff.mp (hDc hδ).2 w (wOne_le_thompsonJi R W hw)).symm
  have hRD : R ≤ Subgroup.normalizer (D : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_D R)
  have hDWW' : ∀ δ ∈ D, ∀ w ∈ W, δ * w * δ⁻¹ * w⁻¹ ∈ W' := by
    intro δ hδ w hw
    have h1 : δ * w * δ⁻¹ * w⁻¹ ∈ D := by
      rw [show δ * w * δ⁻¹ * w⁻¹ = δ * (w * δ⁻¹ * w⁻¹) by group]
      exact D.mul_mem hδ ((Subgroup.mem_normalizer_iff.mp (hRD (hWR hw)) _).mp (D.inv_mem hδ))
    have h2 : δ * w * δ⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXW (hRX (hDR hδ))) w).mp hw) (W.inv_mem hw)
    exact mem_wOne_of_comm hWR hm hB₀ hB₀W h2 (hDe.2 _ h1) (hDW' _ h1)
  let S : Subgroup G :=
    { carrier := {x | x ∈ X ∧ (∀ v ∈ W', x * v * x⁻¹ = v) ∧ ∀ w ∈ W, x * w * x⁻¹ * w⁻¹ ∈ W'}
      one_mem' := ⟨X.one_mem, fun v _ => by simp, fun w _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hxX, hx1, hx2⟩ ⟨hyX, hy1, hy2⟩
        refine ⟨X.mul_mem hxX hyX, fun v hv => ?_, fun w hw => ?_⟩
        · rw [show x * y * v * (x * y)⁻¹ = x * (y * v * y⁻¹) * x⁻¹ by group, hy1 v hv,
            hx1 v hv]
        · have e : x * y * w * (x * y)⁻¹ * w⁻¹ =
              (x * (y * w * y⁻¹ * w⁻¹) * x⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
          rw [e, hx1 _ (hy2 w hw)]
          exact W'.mul_mem (hy2 w hw) (hx2 w hw)
      inv_mem' := by
        rintro x ⟨hxX, hx1, hx2⟩
        refine ⟨X.inv_mem hxX, fun v hv => ?_, fun w hw => ?_⟩
        · calc x⁻¹ * v * x⁻¹⁻¹ = x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ := by rw [hx1 v hv]
            _ = v := by group
        · have hw' : x⁻¹ * w * x ∈ W := by
            simpa using (Subgroup.mem_normalizer_iff.mp (hXW (X.inv_mem hxX)) w).mp hw
          have e : x⁻¹ * w * x⁻¹⁻¹ * w⁻¹ =
              (x * (x⁻¹ * w * x) * x⁻¹ * (x⁻¹ * w * x)⁻¹)⁻¹ := by group
          rw [e]
          exact W'.inv_mem (hx2 _ hw') }
  have hXS : X ≤ Subgroup.normalizer (S : Set G) := by
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxX, hx1, hx2⟩ := hx
    refine ⟨X.mul_mem (X.mul_mem hg hxX) (X.inv_mem hg), fun v hv => ?_, fun w hw => ?_⟩
    · have hv' : g⁻¹ * v * g ∈ W' := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hXW' (X.inv_mem hg)) v).mp hv
      calc g * x * g⁻¹ * v * (g * x * g⁻¹)⁻¹ = g * (x * (g⁻¹ * v * g) * x⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * v * g) * g⁻¹ := by rw [hx1 _ hv']
        _ = v := by group
    · have hw' : g⁻¹ * w * g ∈ W := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hXW (X.inv_mem hg)) w).mp hw
      have e : g * x * g⁻¹ * w * (g * x * g⁻¹)⁻¹ * w⁻¹ =
          g * (x * (g⁻¹ * w * g) * x⁻¹ * (g⁻¹ * w * g)⁻¹) * g⁻¹ := by group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hXW' hg) _).mp (hx2 _ hw')
  have hS2 : IsPGroup 2 S := by
    intro x
    obtain ⟨k, n, hn, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    refine ⟨k, ?_⟩
    have hyS : ((x ^ 2 ^ k : ↥S) : G) ∈ S := (x ^ 2 ^ k).2
    have hyn : ((x ^ 2 ^ k : ↥S) : G) ^ n = 1 := by
      have := pow_orderOf_eq_one x
      rw [hord, pow_mul] at this
      simpa using congrArg Subtype.val this
    obtain ⟨hyX, hy1, hy2⟩ := hyS
    set y : G := ((x ^ 2 ^ k : ↥S) : G) with hydef
    have hyc : ∀ w ∈ W, y * w * y⁻¹ = w := fun w hw =>
      commute_of_stab (hW2.to_le hW'W) hn hyn hy1 (hy2 w hw)
    have hyW : y ∈ W := hchar ⟨hyX, Subgroup.mem_centralizer_iff.mpr fun w hw => by
      calc w * y = (y * w * y⁻¹) * y := by rw [hyc w hw]
        _ = y * w := by group⟩
    obtain ⟨j, hj⟩ := hW2 ⟨y, hyW⟩
    have hyj : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime n (2 ^ j) := Nat.Coprime.pow_right j (Nat.coprime_two_right.mpr hn)
    have h1 : orderOf y = 1 :=
      Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyn) hcop)
        (orderOf_dvd_of_pow_eq_one hyj)
    exact Subtype.ext (orderOf_eq_one_iff.mp h1)
  have hSW : S ≤ W := le_pCoreOf_of_le_normalizer 2 (fun x hx => hx.1) hXS hS2
  intro δ hδ
  have hδS : δ ∈ S := ⟨hRX (hDR hδ), fun v hv => by rw [hDW' δ hδ v hv]; group,
    fun w hw => hDWW' δ hδ w hw⟩
  have hδW' : δ ∈ W' := mem_wOne_of_comm hWR hm hB₀ hB₀W (hSW hδS) (hDe.2 δ hδ) (hDW' δ hδ)
  exact Subgroup.subset_closure
    ⟨⟨hδW', Subgroup.mem_centralizer_iff.mpr fun w hw => (hDW' δ hδ w hw).symm⟩, hDe.2 δ hδ⟩

theorem inf_le_wOne {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) (hm : 2 ≤ CFSG.Open.pRank 2 R)
    {A : Subgroup G} (hA : IsMaxElemAbelian R A) :
    A ⊓ pCoreOf 2 X ≤ wOne R (pCoreOf 2 X) := by
  set W := pCoreOf 2 X with hWdef
  have hAc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hAc
  by_cases hAW : A ≤ W
  · intro b hb
    have hzb : Nat.card (Subgroup.zpowers b) ∣ 2 ^ (CFSG.Open.pRank 2 R - 1) := by
      rw [Nat.card_zpowers]
      exact (orderOf_dvd_of_pow_eq_one (hA.2.1.2 b hb.1)).trans (dvd_pow_self 2 (by omega))
    obtain ⟨K, hKc, hbK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two hzb
      (by rw [hAc]; exact pow_dvd_pow 2 (Nat.sub_le _ _)) (Subgroup.zpowers_le.mpr hb.1)
    have hK : IsElemAbelianCorank R 1 K := by
      refine ⟨hKA.trans hA.1, isElemAbelian_of_le hKA hA.2.1, ?_⟩
      rw [hKc, pow_one, ← pow_succ, Nat.sub_add_cancel (by omega)]
    exact le_wOne hK (hKA.trans hAW) (hbK (Subgroup.mem_zpowers b))
  · obtain ⟨a, haA, haW⟩ := Set.not_subset.mp hAW
    have h := card_eq_two_mul_inf hp hYX hXY hYp hXYR hR hA.1 hA.2.1 haA haW
    have hK : IsElemAbelianCorank R 1 (A ⊓ W) := by
      refine ⟨inf_le_left.trans hA.1, isElemAbelian_of_le inf_le_left hA.2.1, ?_⟩
      rw [pow_one, mul_comm, ← h, hAc]
    exact le_wOne hK inf_le_right

theorem exists_transvection {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) (hm : 2 ≤ CFSG.Open.pRank 2 R)
    {A : Subgroup G} (hA : IsMaxElemAbelian R A) {a : G} (haA : a ∈ A) :
    ∃ α ∈ omegaOneCenterOf (wOne R (pCoreOf 2 X)),
      ∀ ω ∈ omegaOneCenterOf (wOne R (pCoreOf 2 X)),
        a * ω * a⁻¹ * ω⁻¹ = 1 ∨ a * ω * a⁻¹ * ω⁻¹ = α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := pCoreOf 2 X with hWdef
  set W' := wOne R W with hW'def
  set Ω := omegaOneCenterOf W' with hΩdef
  have hRX : R ≤ X := hR.1
  have hWR : W ≤ R := pCoreOf_two_le_of_sylowIn hRX hR.2.1 hR.2.2
  have hΩc : Ω ≤ centerOf W' := B2F.omegaOneCenterOf_le_centerOf W'
  have hΩW' : Ω ≤ W' := hΩc.trans inf_le_left
  have hΩR : Ω ≤ R := (hΩW'.trans (wOne_le R W)).trans hWR
  have hΩe : IsElemAbelian 2 Ω := B2F.isElemAbelian_omegaOneCenterOf W'
  have hΩcomm : ∀ ω ∈ Ω, ∀ w ∈ W', ω * w = w * ω := fun ω hω w hw =>
    (Subgroup.mem_centralizer_iff.mp (hΩc hω).2 w hw).symm
  have hAW' := inf_le_wOne hp hYX hXY hYp hXYR hR hm hA
  have hAc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hAc
  have hA2 : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ W) := by
    by_cases hAW : A ≤ W
    · rw [inf_eq_left.mpr hAW]; omega
    · obtain ⟨b, hbA, hbW⟩ := Set.not_subset.mp hAW
      exact (card_eq_two_mul_inf hp hYX hXY hYp hXYR hR hA.1 hA.2.1 hbA hbW).le
  have hdiff : ∀ ω₁ ∈ Ω, ω₁ ∉ A → ∀ ω₂ ∈ Ω, ω₂ ∉ A → ω₁ * ω₂ ∈ A := by
    intro ω₁ hω₁ hω₁A ω₂ hω₂ hω₂A
    have h12 : ω₁ ^ 2 = 1 := hΩe.2 ω₁ hω₁
    have hZ : ∀ x ∈ Subgroup.zpowers ω₁, x = 1 ∨ x = ω₁ := fun x hx => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact zpow_eq_one_or_self h12 k
    have hcomm : ∀ x ∈ A ⊓ W, ∀ y ∈ Subgroup.zpowers ω₁, x * y = y * x := fun x hx y hy => by
      rcases hZ y hy with h | h <;> rw [h]
      · rw [one_mul, mul_one]
      · exact (hΩcomm ω₁ hω₁ x (hAW' hx)).symm
    have hZe : IsElemAbelian 2 (Subgroup.zpowers ω₁) :=
      isElemAbelian_of_forall' (fun x hx y hy => by
        rcases hZ x hx with h | h <;> rcases hZ y hy with h' | h' <;> simp [h, h'])
        fun x hx => by rcases hZ x hx with h | h <;> simp [h, h12]
    set B := (A ⊓ W) ⊔ Subgroup.zpowers ω₁ with hBdef
    have hBe : IsElemAbelian 2 B :=
      isElemAbelian_sup (isElemAbelian_of_le inf_le_left hA.2.1) hZe hcomm
    have hBR : B ≤ R := sup_le (inf_le_left.trans hA.1) (Subgroup.zpowers_le.mpr (hΩR hω₁))
    have hinf : (A ⊓ W) ⊓ Subgroup.zpowers ω₁ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases hZ x hx.2 with rfl | rfl
      · exact Subgroup.one_mem _
      · exact absurd hx.1.1 hω₁A
    have hω₁1 : ω₁ ≠ 1 := fun h => hω₁A (h ▸ A.one_mem)
    have hcz : Nat.card (Subgroup.zpowers ω₁) = 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime h12 hω₁1
    have hBc := card_sup_mul_card_inf (le_normalizer_of_commute hcomm)
    rw [← hBdef, hinf, Subgroup.card_bot, mul_one, hcz] at hBc
    have hBle := H.card_le_two_pow_pRank hBR hBe
    have hBeq : Nat.card B = 2 ^ CFSG.Open.pRank 2 R := by omega
    have hω₂B : ω₂ ∈ B := by
      refine mem_of_card_eq_two_pow_pRank hBR hBe hBeq (hΩR hω₂) (hΩe.2 ω₂ hω₂) fun b hb => ?_
      have hbsup := (F1.mem_sup_iff_exists_mul_of_normalizes
        (le_normalizer_of_commute fun y hy x hx => (hcomm x hx y hy).symm)).mp hb
      obtain ⟨u, hu, v, hv, rfl⟩ := hbsup
      have h1 : ω₂ * u = u * ω₂ := hΩcomm ω₂ hω₂ u (hAW' hu)
      have h2 : ω₂ * v = v * ω₂ := by
        rcases hZ v hv with rfl | rfl
        · rw [one_mul, mul_one]
        · exact comm_of_isElemAbelian hΩe hω₂ hω₁
      calc ω₂ * (u * v) = (ω₂ * u) * v := by group
        _ = u * (ω₂ * v) := by rw [h1]; group
        _ = u * v * ω₂ := by rw [h2]; group
    obtain ⟨u, hu, v, hv, huv⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (le_normalizer_of_commute fun y hy x hx => (hcomm x hx y hy).symm)).mp hω₂B
    rcases hZ v hv with h | h
    · rw [h, mul_one] at huv
      exact absurd (huv ▸ hu.1) hω₂A
    · rw [h] at huv
      rw [huv]
      have hc : ω₁ * u = u * ω₁ := (hcomm u hu ω₁ (Subgroup.mem_zpowers ω₁)).symm
      rw [← mul_assoc, hc, mul_assoc, ← pow_two, h12, mul_one]
      exact hu.1
  have hXΩ : X ≤ Subgroup.normalizer (Ω : Set G) :=
    (le_normalizer_wOne hWR (le_normalizer_pCoreOf 2 X)).trans
      (normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv W')
  have haX : a ∈ X := hRX (hA.1 haA)
  by_cases hΩA : Ω ≤ A
  · refine ⟨1, Ω.one_mem, fun ω hω => Or.inl ?_⟩
    rw [comm_of_isElemAbelian hA.2.1 haA (hΩA hω), mul_inv_cancel_right, mul_inv_cancel]
  · obtain ⟨ω₁, hω₁, hω₁A⟩ := Set.not_subset.mp hΩA
    refine ⟨a * ω₁ * a⁻¹ * ω₁⁻¹, Ω.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXΩ haX) ω₁).mp hω₁)
      (Ω.inv_mem hω₁), fun ω hω => ?_⟩
    by_cases hωA : ω ∈ A
    · left
      rw [comm_of_isElemAbelian hA.2.1 haA hωA, mul_inv_cancel_right, mul_inv_cancel]
    · right
      obtain ⟨c, hcA, rfl⟩ : ∃ c ∈ A, ω = ω₁ * c :=
        ⟨ω₁ * ω, hdiff ω₁ hω₁ hω₁A ω hω hωA, by
          rw [← mul_assoc, ← pow_two, hΩe.2 ω₁ hω₁, one_mul]⟩
      have hac : a * c * a⁻¹ = c := by
        rw [comm_of_isElemAbelian hA.2.1 haA hcA, mul_inv_cancel_right]
      calc a * (ω₁ * c) * a⁻¹ * (ω₁ * c)⁻¹ = (a * ω₁ * a⁻¹) * (a * c * a⁻¹) * c⁻¹ * ω₁⁻¹ := by
            group
        _ = a * ω₁ * a⁻¹ * ω₁⁻¹ := by rw [hac]; group

theorem exists_corank_one_le {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) (hYp : (pCoreOf 2 Y).relIndex Y = p)
    (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X) (hm : 2 ≤ CFSG.Open.pRank 2 R) :
    ∃ B₀ : Subgroup G, IsElemAbelianCorank R 1 B₀ ∧ B₀ ≤ pCoreOf 2 X := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian R
  have hAc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hAc
  by_cases hAW : A ≤ pCoreOf 2 X
  · obtain ⟨K, hKc, -, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
      (n := CFSG.Open.pRank 2 R - 1) (H := ⊥) (L := A)
      (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hAc]; exact pow_dvd_pow 2 (Nat.sub_le _ _)) bot_le
    refine ⟨K, ⟨hKA.trans hA.1, isElemAbelian_of_le hKA hA.2.1, ?_⟩, hKA.trans hAW⟩
    rw [hKc, pow_one, ← pow_succ, Nat.sub_add_cancel (by omega)]
  · obtain ⟨a, haA, haW⟩ := Set.not_subset.mp hAW
    have h := card_eq_two_mul_inf hp hYX hXY hYp hXYR hR hA.1 hA.2.1 haA haW
    refine ⟨A ⊓ pCoreOf 2 X, ⟨inf_le_left.trans hA.1, isElemAbelian_of_le inf_le_left hA.2.1,
      ?_⟩, inf_le_right⟩
    rw [pow_one, mul_comm, ← h, hAc]

end TJ1

theorem thompson_J1_prime {X Y R : Subgroup G} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    (hYp : (pCoreOf 2 Y).relIndex Y = p) (hXYR : X = Y ⊔ R) (hR : IsSylowTwoOf R X)
    (hchar : CharTwo X) :
    X ≤ Subgroup.normalizer (thompsonJ R : Set G) ∨
      X ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJi R 1) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pCoreOf 2 Y with hOdef
  set W := pCoreOf 2 X with hWdef
  have hRX : R ≤ X := hR.1
  have hR2 : IsPGroup 2 R := hR.2.1
  have hWR : W ≤ R := pCoreOf_two_le_of_sylowIn hRX hR2 hR.2.2
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := le_normalizer_pCoreOf 2 X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) :=
    hXY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hOW : O ≤ W :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 Y).trans hYX) hXO (pCoreOf_isPGroup 2 Y)
  have hRD : R ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJi R 1) : Set G) :=
    Subgroup.le_normalizer.trans (TJ1.normalizer_le_normalizer_D R)
  by_cases hm : CFSG.Open.pRank 2 R ≤ 1
  · right
    have hJ1 : thompsonJi R 1 = ⊥ := by
      refine le_bot_iff.mp (iSup₂_le fun B hB => ?_)
      have h := hB.2.2
      have h2 : 2 ^ CFSG.Open.pRank 2 R ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm
      have := Nat.card_pos (α := B)
      rw [pow_one] at h
      exact le_bot_iff.mpr (Subgroup.eq_bot_of_card_eq B (by omega))
    have hD : omegaOneCenterOf (thompsonJi R 1) = ⊥ := by
      rw [hJ1]
      exact le_bot_iff.mp ((B2F.omegaOneCenterOf_le_centerOf ⊥).trans inf_le_left)
    rw [hD]
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    simp [Subgroup.mem_bot]
  push Not at hm
  have hm2 : 2 ≤ CFSG.Open.pRank 2 R := hm
  obtain ⟨B₀, hB₀, hB₀W⟩ := TJ1.exists_corank_one_le hp hYX hXY hYp hXYR hR hm2
  set W' := TJ1.wOne R W with hW'def
  set Ω := omegaOneCenterOf W' with hΩdef
  have hDΩ : omegaOneCenterOf (thompsonJi R 1) ≤ Ω :=
    TJ1.omegaOneCenterOf_J1_le hR hchar hm2 hB₀ hB₀W
  have hXΩ : X ≤ Subgroup.normalizer (Ω : Set G) :=
    (TJ1.le_normalizer_wOne hWR hXW).trans
      (normalizer_le_normalizer_of_map_mulEquiv omegaOneCenterOf_map_mulEquiv W')
  have hΩe : IsElemAbelian 2 Ω := B2F.isElemAbelian_omegaOneCenterOf W'
  have hΩc : Ω ≤ centerOf W' := B2F.omegaOneCenterOf_le_centerOf W'
  set C := X ⊓ Subgroup.centralizer (Ω : Set G) with hCdef
  have hCn : X ≤ Subgroup.normalizer (C : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, B2F.le_normalizer_centralizer hXΩ hx⟩
  by_cases hYC : Y ⊓ C ≤ O
  · left
    have hJΩ : thompsonJ R ≤ Subgroup.centralizer (Ω : Set G) := by
      refine iSup₂_le fun A hA => ?_
      intro a haA
      by_contra hac
      have haR : a ∈ R := hA.1 haA
      have haW : a ∉ W := fun haW => hac (Subgroup.mem_centralizer_iff.mpr fun ω hω =>
        (Subgroup.mem_centralizer_iff.mp (hΩc hω).2 a
          (TJ1.inf_le_wOne hp hYX hXY hYp hXYR hR hm2 hA ⟨haA, haW⟩)).symm)
      obtain ⟨y, hy, hyO⟩ : ∃ y ∈ Y, y ∉ O := by
        by_contra h
        push Not at h
        have h1 : O.relIndex Y = 1 := Subgroup.relIndex_eq_one.mpr h
        rw [hYp] at h1
        exact hp.one_lt.ne' h1
      obtain ⟨α, hα, hαa⟩ := TJ1.exists_transvection hp hYX hXY hYp hXYR hR hm2 hA haA
      have hyX : y ∈ X := hYX hy
      have hyΩ : ∀ ω ∈ Ω, y⁻¹ * ω * y ∈ Ω := fun ω hω => by
        simpa using (Subgroup.mem_normalizer_iff.mp (hXΩ (X.inv_mem hyX)) ω).mp hω
      have hβ : ∀ ω ∈ Ω, (y * a * y⁻¹) * ω * (y * a * y⁻¹)⁻¹ * ω⁻¹ = 1 ∨
          (y * a * y⁻¹) * ω * (y * a * y⁻¹)⁻¹ * ω⁻¹ = y * α * y⁻¹ := by
        intro ω hω
        have e : (y * a * y⁻¹) * ω * (y * a * y⁻¹)⁻¹ * ω⁻¹ =
            y * (a * (y⁻¹ * ω * y) * a⁻¹ * (y⁻¹ * ω * y)⁻¹) * y⁻¹ := by group
        rw [e]
        rcases hαa _ (hyΩ ω hω) with h | h <;> rw [h]
        · left; group
        · exact Or.inr rfl
      have hyαΩ : y * α * y⁻¹ ∈ Ω := (Subgroup.mem_normalizer_iff.mp (hXΩ hyX) α).mp hα
      have hbN : y * a * y⁻¹ ∈ Subgroup.normalizer (Ω : Set G) :=
        hXΩ (X.mul_mem (X.mul_mem hyX (hRX haR)) (X.inv_mem hyX))
      have ha2 : a ^ 2 = 1 := hA.2.1.2 a haA
      have hainv : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
      have hab : a * (y * a * y⁻¹) = a * y * a⁻¹ * y⁻¹ := by rw [hainv]; group
      have habY : a * y * a⁻¹ * y⁻¹ ∈ Y :=
        Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hXY (hRX haR)) y).mp hy) (Y.inv_mem hy)
      have habO := TJ1.comm_not_mem hp hp5 hYX hXY hYp hXYR hR haR haW
        (by rw [ha2]; exact W.one_mem) hy hyO
      have hcop : Nat.Coprime 48 p := by
        refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_)
        have h48 : (48 : ℕ) = 2 ^ 4 * 3 := by norm_num
        rw [h48] at hd
        rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
        · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
        · have := Nat.le_of_dvd (by norm_num) h; omega
      apply TJ1.pow_not_mem_of_coprime hYp habY habO hcop
      refine hYC ⟨Y.pow_mem habY 48, X.pow_mem (hYX habY) 48, ?_⟩
      show _ ∈ Subgroup.centralizer (Ω : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro ω hω
      have h48 := TJ1.commute_pow_of_transvections hΩe hα hyαΩ hbN hαa hβ hω
      rw [hab] at h48
      calc ω * (a * y * a⁻¹ * y⁻¹) ^ 48 =
          ((a * y * a⁻¹ * y⁻¹) ^ 48 * ω * ((a * y * a⁻¹ * y⁻¹) ^ 48)⁻¹) *
            (a * y * a⁻¹ * y⁻¹) ^ 48 := by rw [h48]
        _ = (a * y * a⁻¹ * y⁻¹) ^ 48 * ω := by group
    have hfac := (B2_7_of_le_factor hXΩ hR hJΩ).2
    have hC2 : IsPGroup 2 C := by
      intro c
      have hcX : (c : G) ∈ Y ⊔ R := by rw [← hXYR]; exact c.2.1
      obtain ⟨y, hy, r, hr, hyr⟩ :=
        (F1.mem_sup_iff_exists_mul_of_normalizes (hRX.trans hXY)).mp hcX
      obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
      have hk' : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      obtain ⟨y', hy', he⟩ := A4.exists_pow_mul_eq hy (hRX.trans hXY hr) (2 ^ k)
      rw [hk', mul_one, ← hyr] at he
      have hcY : (c : G) ^ 2 ^ k ∈ Y ⊓ C := ⟨he ▸ hy', C.pow_mem c.2 _⟩
      obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 Y) ⟨_, hYC hcY⟩
      have hj' : ((c : G) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      refine ⟨k + j, Subtype.ext ?_⟩
      simp only [Subgroup.coe_pow, OneMemClass.coe_one]
      rw [pow_add, pow_mul, hj']
    have hCW : C ≤ W := le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hC2
    intro x hx
    obtain ⟨n, hn, c, hc, rfl⟩ := hfac x hx
    exact Subgroup.mul_mem _ hn.2
      ((Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ R)) (hWR (hCW hc)))
  · right
    have hF : (Y ⊓ C) ⊔ O = Y := by
      rcases TJ1.eq_or_eq_of_relIndex_prime hp hYp le_sup_right
          (sup_le inf_le_left (pCoreOf_le 2 Y)) with h | h
      · exact absurd (le_sup_left.trans h.le) hYC
      · exact h
    have hYD : Y ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJi R 1) : Set G) := by
      rw [← hF]
      refine sup_le (fun c hc => ?_) ((hOW.trans hWR).trans hRD)
      refine Subgroup.mem_normalizer_fintype fun δ hδ => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hc.2.2 δ (hDΩ hδ)
      have : c * δ * c⁻¹ = δ := by rw [← h1]; group
      rw [this]
      exact hδ
    rw [hXYR]
    exact sup_le hYD hRD

end CFSG.Quasithin.H13.L32A
