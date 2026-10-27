module

public import CFSG.RankThree.GF2n.Stroth80.Sec5SecMod
public import CFSG.RankThree.GF2n.Stroth80.Sec711PropA

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def LamOrth {G : Type} [Group G] (Z : Subgroup G) (lam : ↥Z →* Multiplicative (ZMod 2))
    (a b : G) : Prop :=
  ∃ h : ⁅a, b⁆ ∈ Z, lam ⟨⁅a, b⁆, h⟩ = 1

theorem comm_mul_left_of_central {a a' b c : G} (hc : c = ⁅a', b⁆) (h : a * c = c * a) :
    ⁅a * a', b⁆ = c * ⁅a, b⁆ := by
  subst hc
  simp only [commutatorElement_def] at h ⊢
  calc a * a' * b * (a * a')⁻¹ * b⁻¹ = a * (a' * b * a'⁻¹ * b⁻¹) * (b * a⁻¹ * b⁻¹) := by group
    _ = (a' * b * a'⁻¹ * b⁻¹) * a * (b * a⁻¹ * b⁻¹) := by rw [h]
    _ = (a' * b * a'⁻¹ * b⁻¹) * (a * b * a⁻¹ * b⁻¹) := by group

theorem comm_mul_right_of_central {a b b' c : G} (hc : c = ⁅a, b'⁆) (h : b * c = c * b) :
    ⁅a, b * b'⁆ = ⁅a, b⁆ * c := by
  subst hc
  simp only [commutatorElement_def] at h ⊢
  calc a * (b * b') * a⁻¹ * (b * b')⁻¹
      = (a * b * a⁻¹ * b⁻¹) * (b * (a * b' * a⁻¹ * b'⁻¹) * b⁻¹) := by group
    _ = (a * b * a⁻¹ * b⁻¹) * ((a * b' * a⁻¹ * b'⁻¹)) := by
      rw [h]; group

section Form

variable {Q Z : Subgroup G} (lam : ↥Z →* Multiplicative (ZMod 2))

@[expose] def comm2 (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) (a b : ↥Q) : ZMod 2 :=
  Multiplicative.toAdd (lam ⟨⁅(a : G), (b : G)⁆, hcomm a a.2 b b.2⟩)

variable (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) (hZc : ∀ z ∈ Z, ∀ a ∈ Q, Commute z a)

include hZc in
theorem comm2_mul_left (a a' b : ↥Q) :
    comm2 lam hcomm (a * a') b = comm2 lam hcomm a b + comm2 lam hcomm a' b := by
  have hz : (a : G) * ⁅(a' : G), (b : G)⁆ = ⁅(a' : G), (b : G)⁆ * (a : G) :=
    ((hZc _ (hcomm a' a'.2 b b.2) a a.2).eq).symm
  have e := comm_mul_left_of_central (a := (a : G)) rfl hz
  unfold comm2
  have : (⟨⁅((a * a' : ↥Q) : G), (b : G)⁆, hcomm _ (a * a').2 _ b.2⟩ : ↥Z) =
      ⟨⁅(a' : G), (b : G)⁆, hcomm _ a'.2 _ b.2⟩ * ⟨⁅(a : G), (b : G)⁆, hcomm _ a.2 _ b.2⟩ :=
    Subtype.ext e
  rw [this, map_mul, toAdd_mul, add_comm]

include hZc in
theorem comm2_mul_right (a b b' : ↥Q) :
    comm2 lam hcomm a (b * b') = comm2 lam hcomm a b + comm2 lam hcomm a b' := by
  have hz : (b : G) * ⁅(a : G), (b' : G)⁆ = ⁅(a : G), (b' : G)⁆ * (b : G) :=
    ((hZc _ (hcomm a a.2 b' b'.2) b b.2).eq).symm
  have e := comm_mul_right_of_central (b := (b : G)) rfl hz
  unfold comm2
  have : (⟨⁅(a : G), ((b * b' : ↥Q) : G)⁆, hcomm _ a.2 _ (b * b').2⟩ : ↥Z) =
      ⟨⁅(a : G), (b : G)⁆, hcomm _ a.2 _ b.2⟩ * ⟨⁅(a : G), (b' : G)⁆, hcomm _ a.2 _ b'.2⟩ :=
    Subtype.ext e
  rw [this, map_mul, toAdd_mul]

include hZc in
theorem comm2_symm (a b : ↥Q) : comm2 lam hcomm b a = comm2 lam hcomm a b := by
  unfold comm2
  have h1 : (⟨⁅(b : G), (a : G)⁆, hcomm _ b.2 _ a.2⟩ : ↥Z) =
      (⟨⁅(a : G), (b : G)⁆, hcomm _ a.2 _ b.2⟩ : ↥Z)⁻¹ :=
    Subtype.ext (by simp [commutatorElement_inv])
  rw [h1, map_inv, toAdd_inv]
  generalize Multiplicative.toAdd (lam ⟨⁅(a : G), (b : G)⁆, hcomm _ a.2 _ b.2⟩) = u
  revert u
  decide

include hZc in
theorem comm2_self (a : ↥Q) : comm2 lam hcomm a a = 0 := by
  unfold comm2
  have : (⟨⁅(a : G), (a : G)⁆, hcomm _ a.2 _ a.2⟩ : ↥Z) = 1 := Subtype.ext (by simp)
  rw [this, map_one, toAdd_one]

include hZc in
theorem comm2_congr_left (a a' b : ↥Q) (h : (a : G) * (a' : G)⁻¹ ∈ Z) :
    comm2 lam hcomm a b = comm2 lam hcomm a' b := by
  have haz : a = (⟨(a : G) * (a' : G)⁻¹, Q.mul_mem a.2 (Q.inv_mem a'.2)⟩ : ↥Q) * a' :=
    Subtype.ext (by simp)
  have h0 : comm2 lam hcomm ⟨(a : G) * (a' : G)⁻¹, Q.mul_mem a.2 (Q.inv_mem a'.2)⟩ b = 0 := by
    unfold comm2
    have : (⟨⁅(a : G) * (a' : G)⁻¹, (b : G)⁆, hcomm _ (Q.mul_mem a.2 (Q.inv_mem a'.2)) _ b.2⟩ :
        ↥Z) = 1 :=
      Subtype.ext (by
        simpa [commutatorElement_eq_one_iff_commute] using hZc _ h _ b.2)
    rw [this, map_one, toAdd_one]
  rw [haz, comm2_mul_left lam hcomm hZc, h0, zero_add]

include hZc in
theorem comm2_congr_right (a b b' : ↥Q) (h : (b : G) * (b' : G)⁻¹ ∈ Z) :
    comm2 lam hcomm a b = comm2 lam hcomm a b' := by
  rw [← comm2_symm lam hcomm hZc a b, ← comm2_symm lam hcomm hZc a b']
  exact comm2_congr_left lam hcomm hZc b b' a h

theorem comm2_eq_zero_iff (a b : ↥Q) : comm2 lam hcomm a b = 0 ↔ LamOrth Z lam (a : G) (b : G) := by
  unfold comm2 LamOrth
  constructor
  · intro h
    exact ⟨hcomm _ a.2 _ b.2, toAdd_eq_zero.1 h⟩
  · rintro ⟨h, h'⟩
    rw [toAdd_eq_zero]
    exact h'

end Form

section Descent

variable {Q Z : Subgroup G} (lam : ↥Z →* Multiplicative (ZMod 2)) {R : Subgroup G} {M : Type}
  [AddCommGroup M] [DistribMulAction ↥R M] {κ : ↥Q →* Multiplicative M}
variable (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) (hZc : ∀ z ∈ Z, ∀ a ∈ Q, Commute z a)

noncomputable def secLift (hκ : IsSecMod R Q Z M κ) (x : M) : ↥Q :=
  Classical.choose (hκ.surj (Multiplicative.ofAdd x))

theorem kappa_secLift (hκ : IsSecMod R Q Z M κ) (x : M) :
    κ (secLift hκ x) = Multiplicative.ofAdd x :=
  Classical.choose_spec (hκ.surj (Multiplicative.ofAdd x))

include hZc in
theorem comm2_secLift (hκ : IsSecMod R Q Z M κ) (a b : ↥Q) (x y : M)
    (ha : κ a = Multiplicative.ofAdd x) (hb : κ b = Multiplicative.ofAdd y) :
    comm2 lam hcomm (secLift hκ x) (secLift hκ y) = comm2 lam hcomm a b := by
  have h1 : (secLift hκ x : G) * (a : G)⁻¹ ∈ Z :=
    (hκ.eq_iff _ _).1 ((kappa_secLift hκ x).trans ha.symm)
  have h2 : (secLift hκ y : G) * (b : G)⁻¹ ∈ Z :=
    (hκ.eq_iff _ _).1 ((kappa_secLift hκ y).trans hb.symm)
  rw [comm2_congr_left lam hcomm hZc _ a _ h1, comm2_congr_right lam hcomm hZc _ _ b h2]

include hZc in
theorem exists_lamForm [Module (ZMod 2) M] (hκ : IsSecMod R Q Z M κ)
    (hnd : ∀ a ∈ Q, (∀ b ∈ Q, LamOrth Z lam a b) → a ∈ Z) :
    ∃ f : LinearMap.BilinForm (ZMod 2) M, f.Nondegenerate ∧ f.IsAlt ∧
      ∀ a b : ↥Q, f (Multiplicative.toAdd (κ a)) (Multiplicative.toAdd (κ b)) =
        comm2 lam hcomm a b := by
  classical
  set F : M → M → ZMod 2 := fun x y => comm2 lam hcomm (secLift hκ x) (secLift hκ y) with hF
  have hFκ : ∀ a b : ↥Q, F (Multiplicative.toAdd (κ a)) (Multiplicative.toAdd (κ b)) =
      comm2 lam hcomm a b := fun a b =>
    comm2_secLift lam hcomm hZc hκ a b _ _ (by rw [ofAdd_toAdd]) (by rw [ofAdd_toAdd])
  have hlift : ∀ x : M, Multiplicative.toAdd (κ (secLift hκ x)) = x := fun x => by
    rw [kappa_secLift, toAdd_ofAdd]
  have hadd1 : ∀ x x' y, F (x + x') y = F x y + F x' y := by
    intro x x' y
    have h := comm2_mul_left lam hcomm hZc (secLift hκ x) (secLift hκ x') (secLift hκ y)
    have e : Multiplicative.toAdd (κ (secLift hκ x * secLift hκ x')) = x + x' := by
      rw [map_mul, toAdd_mul, hlift, hlift]
    have := hFκ (secLift hκ x * secLift hκ x') (secLift hκ y)
    rw [e, hlift] at this
    rw [this, h]
  have hadd2 : ∀ x y y', F x (y + y') = F x y + F x y' := by
    intro x y y'
    have h := comm2_mul_right lam hcomm hZc (secLift hκ x) (secLift hκ y) (secLift hκ y')
    have e : Multiplicative.toAdd (κ (secLift hκ y * secLift hκ y')) = y + y' := by
      rw [map_mul, toAdd_mul, hlift, hlift]
    have := hFκ (secLift hκ x) (secLift hκ y * secLift hκ y')
    rw [e, hlift] at this
    rw [this, h]
  have hzero : ∀ y, F 0 y = 0 := by
    intro y
    have := hadd1 0 0 y
    simpa using this
  have hscal : ∀ (c : ZMod 2) x y, F (c • x) y = c • F x y := by
    intro c x y
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul, zero_smul]; exact hzero y
    · rw [one_smul, one_smul]
  have hsymm : ∀ x y, F x y = F y x := by
    intro x y
    have := hFκ (secLift hκ y) (secLift hκ x)
    simp only [hF]
    rw [comm2_symm lam hcomm hZc]
  have hscal2 : ∀ (c : ZMod 2) x y, F x (c • y) = c • F x y := by
    intro c x y
    rw [hsymm, hscal, hsymm]
  refine ⟨LinearMap.mk₂ (ZMod 2) F hadd1 hscal hadd2 hscal2, ?_, ?_, ?_⟩
  · have hleft : ∀ x : M, (∀ y : M, F x y = 0) → x = 0 := by
      intro x hx
      have hxQ : ((secLift hκ x : ↥Q) : G) ∈ Z := by
        apply hnd _ (secLift hκ x).2
        intro b hb
        have h0 : comm2 lam hcomm (secLift hκ x) ⟨b, hb⟩ = 0 := by
          have := hFκ (secLift hκ x) ⟨b, hb⟩
          rw [hlift] at this
          rw [← this]
          exact hx _
        refine ⟨hcomm _ (secLift hκ x).2 _ hb, ?_⟩
        have : Multiplicative.toAdd (lam ⟨⁅((secLift hκ x : ↥Q) : G), b⁆,
            hcomm _ (secLift hκ x).2 _ hb⟩) = 0 := h0
        simpa using this
      have h1 : κ (secLift hκ x) = 1 := (hκ.ker _).2 hxQ
      rw [kappa_secLift] at h1
      simpa using h1
    exact ⟨hleft, fun y hy => hleft y fun x => by rw [hsymm]; exact hy x⟩
  · intro x
    show F x x = 0
    have := hFκ (secLift hκ x) (secLift hκ x)
    rw [hlift] at this
    rw [this]
    exact comm2_self lam hcomm hZc _
  · exact fun a b => hFκ a b

end Descent

theorem propAGroup_holds :
    ∀ (G : Type) [Group G] [Finite G] (Q Z V W SB SC Bp P : Subgroup G)
      (lam : ↥Z →* Multiplicative (ZMod 2)) (X Y : Set G),
      Z ≤ Q → (∀ z ∈ Z, ∀ a ∈ Q, Commute z a) → (∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z) →
      (∀ a ∈ Q, a ^ 2 ∈ Z) →
      (∀ a ∈ Q, (∀ b ∈ Q, LamOrth Z lam a b) → a ∈ Z) →
      Z ≤ V → V ≤ Q → W ≤ Q → (∀ a ∈ V, ∀ b ∈ V, ⁅a, b⁆ = 1) →
      (∀ a ∈ Q, a ∈ W ↔ ∀ v ∈ V, LamOrth Z lam a v) →
      W = SB ⊔ SC ⊔ V →
      (∀ a ∈ SB, ∀ b ∈ SB, ⁅a, b⁆ = 1) → (∀ a ∈ SC, ∀ b ∈ SC, ⁅a, b⁆ = 1) →
      Z ≤ Bp → Z ≤ P → Bp ≤ Q → P ≤ Q → Bp ⊓ P = Z →
      (∀ g ∈ X ∪ Y, ∀ a ∈ Q, g * a * g⁻¹ ∈ Q) → (∀ g ∈ X ∪ Y, ∀ z ∈ Z, g * z * g⁻¹ = z) →
      (∀ g ∈ X ∪ Y, ∀ a ∈ Q, ⁅g, a⁆ ∈ W) → (∀ g ∈ X ∪ Y, ∀ a ∈ W, ⁅g, a⁆ ∈ V) →
      (∀ g ∈ X ∪ Y, ∀ a ∈ V, ⁅g, a⁆ ∈ Z) →
      (∀ x ∈ X, ∀ a ∈ SB, ⁅x, a⁆ ∈ Bp) → (∀ x ∈ X, ∀ a ∈ SC, ⁅x, a⁆ ∈ P) →
      (∀ y ∈ Y, ∀ a ∈ W, ⁅y, a⁆ ∈ P) →
      (∀ a ∈ SB, (∀ x ∈ X, ⁅x, a⁆ ∈ Z) → a ∈ V) →
      (∀ a ∈ SC, (∀ y ∈ Y, ⁅y, a⁆ ∈ Z) → a ∈ V) →
      W ≠ V →
      ∃ x ∈ X, ∃ y ∈ Y, ⁅x, y⁆ ∉ Q := by
  classical
  intro G _ _ Q Z V W SB SC Bp P lam X Y hZQ hZc hcomm hsq hnd hZV hVQ hWQ hVab hWdef hWsum
    hSBab hSCab hZBp hZP hBpQ hPQ hBpP hnorm hfix hQW hWV hVZ hXB hXC hYP hXf hYf hWneV
  let R₀ : Subgroup G := Subgroup.normalizer (Q : Set G) ⊓ Subgroup.centralizer (Z : Set G)
  have hmemR₀ : ∀ g : G, (∀ a ∈ Q, g * a * g⁻¹ ∈ Q) → (∀ z ∈ Z, g * z * g⁻¹ = z) → g ∈ R₀ := by
    intro g h1 h2
    refine ⟨Subgroup.mem_normalizer_fintype fun a ha => h1 a ha,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro z hz
    calc z * g = (g * z * g⁻¹) * g := by rw [h2 z hz]
      _ = g * z := by group
  have hnormR : ∀ r ∈ R₀, ∀ a ∈ Q, r * a * r⁻¹ ∈ Q := fun r hr a ha =>
    (Subgroup.mem_normalizer_iff.mp hr.1 a).mp ha
  have hfixR : ∀ r ∈ R₀, ∀ z ∈ Z, r * z * r⁻¹ = z := by
    intro r hr z hz
    have := Subgroup.mem_centralizer_iff.mp hr.2 z hz
    calc r * z * r⁻¹ = (z * r) * r⁻¹ := by rw [this]
      _ = z := by group
  have hQR : Q ≤ R₀ := fun c hc =>
    ⟨Subgroup.le_normalizer hc, Subgroup.mem_centralizer_iff.mpr fun z hz => (hZc z hz c hc).eq⟩
  have hsec : SecHyp R₀ Q Z :=
    ⟨hZQ, hcomm, hsq, fun r hr x hx => hnormR r hr x hx,
      fun r hr x hx => by rw [hfixR r hr x hx]; exact hx⟩
  obtain ⟨M, iM, iA, κ, hκ⟩ := exists_sectionModule hsec
  haveI : Finite M := hκ.finite
  letI : Module (ZMod 2) M := AddCommGroup.zmodModule (fun a => by
    rw [two_nsmul]; exact hκ.two a)
  haveI : FiniteDimensional (ZMod 2) M := Module.Finite.of_finite
  obtain ⟨f, hfnd, hfalt, hfκ⟩ := exists_lamForm lam hcomm hZc hκ hnd
  let Sub : Subgroup G → Submodule (ZMod 2) M := fun U =>
    AddSubgroup.toZModSubmodule 2 (secSub κ U)
  have hrep : ∀ x : M, ∃ a : ↥Q, Multiplicative.toAdd (κ a) = x := by
    intro x
    obtain ⟨a, ha⟩ := hκ.surj (Multiplicative.ofAdd x)
    exact ⟨a, by rw [ha]; rfl⟩
  have hmemU : ∀ U : Subgroup G, Z ≤ U → ∀ a : ↥Q,
      Multiplicative.toAdd (κ a) ∈ Sub U ↔ (a : G) ∈ U :=
    fun U hU a => toAdd_mem_secSub_iff hκ hU a
  have hmemS : ∀ (U : Subgroup G) (s : ↥Q), (s : G) ∈ U → Multiplicative.toAdd (κ s) ∈ Sub U :=
    fun U s hs => mem_secSub.2 ⟨s, hs, by rw [ofAdd_toAdd]⟩
  let lin : ↥R₀ → (M →ₗ[ZMod 2] M) := fun r =>
    AddMonoidHom.toZModLinearMap 2 (DistribSMul.toAddMonoidHom M r)
  have hlin : ∀ (r : ↥R₀) (x : M), lin r x = r • x := fun r x => rfl
  have hact : ∀ (r : ↥R₀) (a : ↥Q), lin r (Multiplicative.toAdd (κ a)) =
      Multiplicative.toAdd (κ ⟨(r : G) * a * (r : G)⁻¹, hnormR r r.2 a a.2⟩) := by
    intro r a
    have := hκ.act r a ⟨(r : G) * a * (r : G)⁻¹, hnormR r r.2 a a.2⟩ rfl
    rw [hlin, this, toAdd_ofAdd]
  have hcQ : ∀ r ∈ R₀, ∀ a ∈ Q, ⁅r, a⁆ ∈ Q := by
    intro r hr a ha
    rw [commutatorElement_def]
    exact Q.mul_mem (hnormR r hr a ha) (Q.inv_mem ha)
  have hsub : ∀ (r : ↥R₀) (a : ↥Q), lin r (Multiplicative.toAdd (κ a)) -
      Multiplicative.toAdd (κ a) = Multiplicative.toAdd (κ ⟨⁅(r : G), (a : G)⁆,
        hcQ r r.2 a a.2⟩) := by
    intro r a
    have e : (⟨⁅(r : G), (a : G)⁆, hcQ r r.2 a a.2⟩ : ↥Q) =
        ⟨(r : G) * a * (r : G)⁻¹, hnormR r r.2 a a.2⟩ * a⁻¹ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [hact, e, map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hZW : Z ≤ W := hZV.trans (by rw [hWsum]; exact le_sup_right)
  have hVW : V ≤ W := by rw [hWsum]; exact le_sup_right
  have hSBQ : SB ≤ Q := (show SB ≤ W by rw [hWsum]; exact le_sup_left.trans le_sup_left).trans hWQ
  have hSCQ : SC ≤ Q := (show SC ≤ W by rw [hWsum]; exact le_sup_right.trans le_sup_left).trans hWQ
  have horth : f.orthogonal (Sub V) = Sub W := by
    ext x
    obtain ⟨a, rfl⟩ := hrep x
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    have h1 : (∀ n ∈ Sub V, f n (Multiplicative.toAdd (κ a)) = 0) ↔
        ∀ v : ↥Q, (v : G) ∈ V → comm2 lam hcomm v a = 0 := by
      constructor
      · intro h v hv
        rw [← hfκ]
        exact h _ ((hmemU V hZV v).2 hv)
      · intro h n hn
        obtain ⟨v, rfl⟩ := hrep n
        rw [hfκ]
        exact h v ((hmemU V hZV v).1 hn)
    refine (h1.trans ?_).trans (hmemU W hZW a).symm
    rw [hWdef a a.2]
    constructor
    · intro h v hv
      have := h ⟨v, hVQ hv⟩ hv
      rw [comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm] at this
      exact this
    · intro h v hv
      rw [comm2_symm lam hcomm hZc, comm2_eq_zero_iff lam hcomm]
      exact h v hv
  have hsubW : Sub W = Sub SB ⊔ Sub SC ⊔ Sub V := by
    have : secSub κ W = secSub κ SB ⊔ secSub κ SC ⊔ secSub κ V := by
      rw [hWsum, secSub_sup (sup_le hSBQ hSCQ) hVQ, secSub_sup hSBQ hSCQ]
    show AddSubgroup.toZModSubmodule 2 (secSub κ W) = _
    rw [this, OrderIso.map_sup, OrderIso.map_sup]
  have hVW' : Sub V ≤ f.orthogonal (Sub V) := by
    rw [horth]
    exact (AddSubgroup.toZModSubmodule 2).monotone (secSub_mono hVW)
  have hBP : Sub Bp ⊓ Sub P = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, rfl⟩ := hrep x
    have h1 := (hmemU Bp hZBp a).1 hx.1
    have h2 := (hmemU P hZP a).1 hx.2
    have h3 : (a : G) ∈ Z := by rw [← hBpP]; exact ⟨h1, h2⟩
    have h4 : κ a = 1 := (hκ.ker a).2 h3
    rw [h4, toAdd_one]
    exact Submodule.zero_mem _
  have hmemR : ∀ g ∈ X ∪ Y, g ∈ R₀ := fun g hg => hmemR₀ g (hnorm g hg) (hfix g hg)
  let X' : Set (M →ₗ[ZMod 2] M) := {T | ∃ g ∈ X, ∃ hg : g ∈ R₀, T = lin ⟨g, hg⟩}
  let Y' : Set (M →ₗ[ZMod 2] M) := {T | ∃ g ∈ Y, ∃ hg : g ∈ R₀, T = lin ⟨g, hg⟩}
  have hXY : ∀ T ∈ X' ∪ Y', ∃ g ∈ X ∪ Y, ∃ hg : g ∈ R₀, T = lin ⟨g, hg⟩ := by
    rintro T (⟨g, hg, hR, rfl⟩ | ⟨g, hg, hR, rfl⟩)
    · exact ⟨g, Or.inl hg, hR, rfl⟩
    · exact ⟨g, Or.inr hg, hR, rfl⟩
  have hkz : ∀ (r : ↥R₀) (a : ↥Q), ⁅(r : G), (a : G)⁆ ∈ Z →
      lin r (Multiplicative.toAdd (κ a)) = Multiplicative.toAdd (κ a) := by
    intro r a hz
    have h0 := hsub r a
    have h1 : κ ⟨⁅(r : G), (a : G)⁆, hcQ r r.2 a a.2⟩ = 1 := (hκ.ker _).2 hz
    rw [h1, toAdd_one] at h0
    exact sub_eq_zero.1 h0
  have hpres : ∀ g ∈ X' ∪ Y', ∀ a b, f (g a) (g b) = f a b := by
    intro T hT x y
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    obtain ⟨b, rfl⟩ := hrep y
    rw [hact, hact, hfκ, hfκ]
    unfold comm2
    have e : ⁅g * (a : G) * g⁻¹, g * (b : G) * g⁻¹⁆ = g * ⁅(a : G), (b : G)⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    congr 2
    exact Subtype.ext (by
      show ⁅g * (a : G) * g⁻¹, g * (b : G) * g⁻¹⁆ = ⁅(a : G), (b : G)⁆
      rw [e]
      exact hfixR g hR _ (hcomm _ a.2 _ b.2))
  have hQW' : ∀ g ∈ X' ∪ Y', ∀ a, g a - a ∈ f.orthogonal (Sub V) := by
    intro T hT x
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    rw [horth, hsub ⟨g, hR⟩ a]
    exact (hmemU W hZW _).2 (hQW g hg a a.2)
  have hWV' : ∀ g ∈ X' ∪ Y', ∀ a ∈ f.orthogonal (Sub V), g a - a ∈ Sub V := by
    intro T hT x hx
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    rw [horth] at hx
    have haW : (a : G) ∈ W := (hmemU W hZW a).1 hx
    rw [hsub ⟨g, hR⟩ a]
    exact (hmemU V hZV _).2 (hWV g hg a haW)
  have hV' : ∀ g ∈ X' ∪ Y', ∀ a ∈ Sub V, g a = a := by
    intro T hT x hx
    obtain ⟨g, hg, hR, rfl⟩ := hXY T hT
    obtain ⟨a, rfl⟩ := hrep x
    exact hkz ⟨g, hR⟩ a (hVZ g hg a ((hmemU V hZV a).1 hx))
  have hXB' : ∀ x ∈ X', ∀ a ∈ Sub SB, x a - a ∈ Sub Bp := by
    rintro T ⟨g, hg, hR, rfl⟩ x hx
    obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 hx
    have hsa : Multiplicative.toAdd (κ s) = x := by rw [hs]; rfl
    rw [← hsa, hsub ⟨g, hR⟩ s]
    exact (hmemU Bp hZBp _).2 (hXB g hg s hsSB)
  have hXC' : ∀ x ∈ X', ∀ a ∈ Sub SC, x a - a ∈ Sub P := by
    rintro T ⟨g, hg, hR, rfl⟩ x hx
    obtain ⟨s, hsSC, hs⟩ := mem_secSub.1 hx
    have hsa : Multiplicative.toAdd (κ s) = x := by rw [hs]; rfl
    rw [← hsa, hsub ⟨g, hR⟩ s]
    exact (hmemU P hZP _).2 (hXC g hg s hsSC)
  have hYP' : ∀ y ∈ Y', ∀ a ∈ f.orthogonal (Sub V), y a - a ∈ Sub P := by
    rintro T ⟨g, hg, hR, rfl⟩ x hx
    obtain ⟨a, rfl⟩ := hrep x
    rw [horth] at hx
    rw [hsub ⟨g, hR⟩ a]
    exact (hmemU P hZP _).2 (hYP g hg a ((hmemU W hZW a).1 hx))
  have hXf' : ∀ a ∈ Sub SB, (∀ x ∈ X', x a = a) → a ∈ Sub V := by
    intro a ha hall
    obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 ha
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsV : (s : G) ∈ V := by
      apply hXf s hsSB
      intro g hg
      have h1 := hall (lin ⟨g, hmemR g (Or.inl hg)⟩) ⟨g, hg, hmemR g (Or.inl hg), rfl⟩
      rw [← hsa] at h1
      have h2 := hsub ⟨g, hmemR g (Or.inl hg)⟩ s
      rw [h1, sub_self] at h2
      have h3 : κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inl hg)) s s.2⟩ = 1 := by
        have : Multiplicative.toAdd (κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inl hg)) s s.2⟩) = 0 :=
          h2.symm
        simpa using this
      exact (hκ.ker _).1 h3
    exact mem_secSub.2 ⟨s, hsV, hs⟩
  have hYf' : ∀ a ∈ Sub SC, (∀ y ∈ Y', y a = a) → a ∈ Sub V := by
    intro a ha hall
    obtain ⟨s, hsSC, hs⟩ := mem_secSub.1 ha
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsV : (s : G) ∈ V := by
      apply hYf s hsSC
      intro g hg
      have h1 := hall (lin ⟨g, hmemR g (Or.inr hg)⟩) ⟨g, hg, hmemR g (Or.inr hg), rfl⟩
      rw [← hsa] at h1
      have h2 := hsub ⟨g, hmemR g (Or.inr hg)⟩ s
      rw [h1, sub_self] at h2
      have h3 : κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inr hg)) s s.2⟩ = 1 := by
        have : Multiplicative.toAdd (κ ⟨⁅g, (s : G)⁆, hcQ g (hmemR g (Or.inr hg)) s s.2⟩) = 0 :=
          h2.symm
        simpa using this
      exact (hκ.ker _).1 h3
    exact mem_secSub.2 ⟨s, hsV, hs⟩
  have hne : f.orthogonal (Sub V) ≠ Sub V := by
    intro h
    apply hWneV
    rw [horth] at h
    have h' : secSub κ W = secSub κ V := (AddSubgroup.toZModSubmodule 2).injective h
    exact (secSub_inj hκ hZW hWQ hZV hVQ).1 h'
  have hSBiso : ∀ a ∈ Sub SB, ∀ b ∈ Sub SB, f a b = 0 := by
    intro a ha b hb
    obtain ⟨s, hsSB, hs⟩ := mem_secSub.1 ha
    obtain ⟨s', hsSB', hs'⟩ := mem_secSub.1 hb
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsa' : Multiplicative.toAdd (κ s') = b := by rw [hs']; rfl
    rw [← hsa, ← hsa', hfκ, comm2_eq_zero_iff lam hcomm]
    refine ⟨hcomm _ s.2 _ s'.2, ?_⟩
    have : (⟨⁅(s : G), (s' : G)⁆, hcomm _ s.2 _ s'.2⟩ : ↥Z) = 1 :=
      Subtype.ext (hSBab _ hsSB _ hsSB')
    rw [this, map_one]
  have hSCiso : ∀ a ∈ Sub SC, ∀ b ∈ Sub SC, f a b = 0 := by
    intro a ha b hb
    obtain ⟨s, hsSC, hs⟩ := mem_secSub.1 ha
    obtain ⟨s', hsSC', hs'⟩ := mem_secSub.1 hb
    have hsa : Multiplicative.toAdd (κ s) = a := by rw [hs]; rfl
    have hsa' : Multiplicative.toAdd (κ s') = b := by rw [hs']; rfl
    rw [← hsa, ← hsa', hfκ, comm2_eq_zero_iff lam hcomm]
    refine ⟨hcomm _ s.2 _ s'.2, ?_⟩
    have : (⟨⁅(s : G), (s' : G)⁆, hcomm _ s.2 _ s'.2⟩ : ↥Z) = 1 :=
      Subtype.ext (hSCab _ hsSC _ hsSC')
    rw [this, map_one]
  obtain ⟨x, hx, y, hy, hxy⟩ := n12_exists_not_commute f hfnd hfalt (Sub V) (Sub SB) (Sub SC)
    (Sub Bp) (Sub P) hVW' (horth.trans hsubW) hSBiso hSCiso hBP X' Y' hpres hQW' hWV' hV' hXB'
    hXC' hYP' hXf' hYf' hne
  obtain ⟨g₁, hg₁, hR₁, rfl⟩ := hx
  obtain ⟨g₂, hg₂, hR₂, rfl⟩ := hy
  refine ⟨g₁, hg₁, g₂, hg₂, fun hc => hxy ?_⟩
  have hcR : ⁅g₁, g₂⁆ ∈ R₀ := hQR hc
  have hrel : (⟨g₁, hR₁⟩ : ↥R₀) * ⟨g₂, hR₂⟩ = ⟨⁅g₁, g₂⁆, hcR⟩ * (⟨g₂, hR₂⟩ * ⟨g₁, hR₁⟩) := by
    apply Subtype.ext
    show g₁ * g₂ = ⁅g₁, g₂⁆ * (g₂ * g₁)
    simp only [commutatorElement_def]; group
  have htriv : ∀ x : M, (⟨⁅g₁, g₂⁆, hcR⟩ : ↥R₀) • x = x := by
    intro x
    obtain ⟨a, rfl⟩ := hrep x
    have h1 := hact ⟨⁅g₁, g₂⁆, hcR⟩ a
    rw [hlin] at h1
    rw [h1]
    congr 1
    show _ = _
    have h2 : κ ⟨⁅g₁, g₂⁆ * (a : G) * ⁅g₁, g₂⁆⁻¹, hnormR _ hcR a a.2⟩ = κ a := by
      rw [hκ.eq_iff]
      have := hcomm _ hc _ a.2
      simpa [commutatorElement_def, mul_assoc] using this
    rw [h2]
  ext x
  show (⟨g₁, hR₁⟩ : ↥R₀) • ((⟨g₂, hR₂⟩ : ↥R₀) • x) = (⟨g₂, hR₂⟩ : ↥R₀) • ((⟨g₁, hR₁⟩ : ↥R₀) • x)
  calc (⟨g₁, hR₁⟩ : ↥R₀) • ((⟨g₂, hR₂⟩ : ↥R₀) • x)
      = ((⟨g₁, hR₁⟩ : ↥R₀) * ⟨g₂, hR₂⟩) • x := (mul_smul _ _ _).symm
    _ = ((⟨⁅g₁, g₂⁆, hcR⟩ : ↥R₀) * ((⟨g₂, hR₂⟩ : ↥R₀) * ⟨g₁, hR₁⟩)) • x := by rw [hrel]
    _ = (⟨⁅g₁, g₂⁆, hcR⟩ : ↥R₀) • (((⟨g₂, hR₂⟩ : ↥R₀) * ⟨g₁, hR₁⟩) • x) := mul_smul _ _ _
    _ = ((⟨g₂, hR₂⟩ : ↥R₀) * ⟨g₁, hR₁⟩) • x := htriv _
    _ = (⟨g₂, hR₂⟩ : ↥R₀) • ((⟨g₁, hR₁⟩ : ↥R₀) • x) := mul_smul _ _ _

end CFSG.RankThree.GF2n.Stroth80
