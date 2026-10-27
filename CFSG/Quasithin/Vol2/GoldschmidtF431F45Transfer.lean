module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Abstract
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Iso

public section

namespace CFSG.Quasithin.H13.F431.F45

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam.Completion CFSG.Quasithin.F7 CFSG.Open

universe u w x v

structure ModelBase {X : Type x} {V : Type v} [Group X] [MulAction X V] (Γ : SimpleGraph V)
    (m : ℕ) (a : V) (Q : Subgroup X) : Prop where
  Qfix : ∀ w, Γ.Adj a w → ∀ q ∈ Q, q • w = w
  Qtrans : ∀ b c, Γ.dist a b = m → Γ.dist a c = m → ∃ q ∈ Q, q • b = c
  Qfree : ∀ b, Γ.dist a b = m → ∀ q ∈ Q, q • b = b → q = 1
  two : ∀ b c b' c', Γ.Adj a b → Γ.Adj a c → b ≠ c → Γ.Adj a b' → Γ.Adj a c' → b' ≠ c' →
    ∃ g : X, g • a = a ∧ g • b = b' ∧ g • c = c'

section Orbit

variable {X : Type x} [Group X] {G : Type*} [Group G] {B W : Type*} {V : Type v}
  [MulAction G W] [MulAction X V]

theorem exists_equivariant_map (Φ : X →* G) (bw : B → W) (bv : B → V) (typ : W → B)
    (hsurj : ∀ w, ∃ y : X, Φ y • bw (typ w) = w)
    (htyp : ∀ b y, typ (Φ y • bw b) = b)
    (hstab : ∀ b y, Φ y • bw b = bw b ↔ y • bv b = bv b) :
    ∃ e : W → V, (∀ b y, e (Φ y • bw b) = y • bv b) ∧ ∀ y w, e (Φ y • w) = y • e w := by
  classical
  choose r hr using hsurj
  have P1 : ∀ b y, r (Φ y • bw b) • bv (typ (Φ y • bw b)) = y • bv b := by
    intro b y
    have h1 := hr (Φ y • bw b)
    rw [htyp] at h1 ⊢
    have h2 : Φ (y⁻¹ * r (Φ y • bw b)) • bw b = bw b := by
      rw [map_mul, mul_smul, h1, map_inv, inv_smul_smul]
    have h3 := (hstab b _).mp h2
    calc r (Φ y • bw b) • bv b = y • ((y⁻¹ * r (Φ y • bw b)) • bv b) := by
          rw [← mul_smul, mul_inv_cancel_left]
      _ = y • bv b := by rw [h3]
  refine ⟨fun w => r w • bv (typ w), P1, ?_⟩
  intro y w
  have hw := hr w
  have e1 : Φ y • w = Φ (y * r w) • bw (typ w) := by
    rw [map_mul, mul_smul, hw]
  show r (Φ y • w) • bv (typ (Φ y • w)) = y • (r w • bv (typ w))
  rw [e1, P1, mul_smul]

end Orbit

section Setting

variable {S : LieSetting.{u, w}} {X : Type x} [Group X] {V : Type v} [MulAction X V]
  (Φ : X →* S.ι.G0) (ΓM : SimpleGraph V) (v₁ v₂ : V)

structure XDatum (S : LieSetting.{u, w}) {X : Type x} [Group X] {V : Type v} [MulAction X V]
    (Φ : X →* S.ι.G0) (ΓM : SimpleGraph V) (v₁ v₂ : V) : Prop where
  inj : Function.Injective Φ
  N_eq : S.N = Φ.range
  dec : ∀ g : S.ι.G0, ∃ y : X, ∃ k : S.ι.G0, k • S.ι.xv = S.ι.xv ∧ k • S.ι.lv = S.ι.lv ∧
    g = Φ y * k
  stab1 : ∀ y : X, Φ y • S.ι.xv = S.ι.xv ↔ y • v₁ = v₁
  stab2 : ∀ y : X, Φ y • S.ι.lv = S.ι.lv ↔ y • v₂ = v₂
  disj : ∀ y z : X, y • v₁ ≠ z • v₂
  noadj1 : ∀ y z : X, ¬ ΓM.Adj (y • v₁) (z • v₁)
  noadj2 : ∀ y z : X, ¬ ΓM.Adj (y • v₂) (z • v₂)
  adj12 : ΓM.Adj v₁ v₂

variable {Φ ΓM v₁ v₂}

theorem baseVert_fix {k : S.ι.G0} (hk1 : k • S.ι.xv = S.ι.xv) (hk2 : k • S.ι.lv = S.ι.lv)
    (b : Bool) : k • S.ι.baseVert b = S.ι.baseVert b := by
  cases b
  · exact hk1
  · exact hk2

theorem XDatum.hsurj (D : XDatum S Φ ΓM v₁ v₂) (a : S.ι.Γ) :
    ∃ y : X, Φ y • S.ι.baseVert (CosetGeom.vtype a) = a := by
  obtain ⟨g, hg⟩ := exists_smul_eq_baseVert S.ι a
  obtain ⟨y, k, hk1, hk2, rfl⟩ := D.dec g
  refine ⟨y, ?_⟩
  have h : Φ y • S.ι.baseVert (CosetGeom.vtype a) =
      (Φ y * k) • S.ι.baseVert (CosetGeom.vtype a) := by
    rw [mul_smul, baseVert_fix hk1 hk2]
  exact h.trans hg

theorem XDatum.htyp (b : Bool) (y : X) : CosetGeom.vtype (Φ y • S.ι.baseVert b) = b := by
  rw [CosetGeom.vtype_smul, vtype_baseVert]

theorem XDatum.hstab (D : XDatum S Φ ΓM v₁ v₂) (b : Bool) (y : X) :
    Φ y • S.ι.baseVert b = S.ι.baseVert b ↔ y • cond b v₂ v₁ = cond b v₂ v₁ := by
  cases b
  · exact D.stab1 y
  · exact D.stab2 y

section Equiv

variable [GraphAction X ΓM]

theorem XDatum.adj_xv_lv (D : XDatum S Φ ΓM v₁ v₂)
    (hflag : ∀ a, ΓM.Adj v₁ a → ∃ y : X, y • v₁ = v₁ ∧ y • v₂ = a) (z : X) :
    S.ι.graph.Adj S.ι.xv (Φ z • S.ι.lv) ↔ ΓM.Adj v₁ (z • v₂) := by
  have hxl : S.ι.graph.Adj S.ι.xv S.ι.lv := CosetGeom.adj_γ₀_γ₁
  constructor
  · intro h
    obtain ⟨g, hg1, hg2⟩ := CosetGeom.exists_stab_smul_eq hxl h
    obtain ⟨y, k, hk1, hk2, rfl⟩ := D.dec g
    rw [mul_smul, hk1] at hg1
    rw [mul_smul, hk2] at hg2
    have h1 : y • v₁ = v₁ := (D.stab1 y).mp hg1
    have h2 : (y⁻¹ * z) • v₂ = v₂ := by
      refine (D.stab2 _).mp ?_
      rw [map_mul, mul_smul, ← hg2, map_inv, inv_smul_smul]
    have h3 : z • v₂ = y • v₂ := by
      have := congrArg (fun t => y • t) h2
      simpa [mul_smul] using this
    have := (GraphAction.adj_smul y v₁ v₂).mpr D.adj12
    rwa [h1, ← h3] at this
  · intro h
    obtain ⟨y, hy1, hy2⟩ := hflag _ h
    have h1 : Φ y • S.ι.xv = S.ι.xv := (D.stab1 y).mpr hy1
    have h2 : Φ y • S.ι.lv = Φ z • S.ι.lv := by
      have h3 : (y⁻¹ * z) • v₂ = v₂ := by
        rw [mul_smul, ← hy2, inv_smul_smul]
      have h4 := (D.stab2 _).mpr h3
      rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff] at h4
      exact h4.symm
    have := (GraphAction.adj_smul (Φ y) S.ι.xv S.ι.lv).mpr hxl
    rwa [h1, h2] at this

theorem XDatum.adj_mixed (D : XDatum S Φ ΓM v₁ v₂)
    (hflag : ∀ a, ΓM.Adj v₁ a → ∃ y : X, y • v₁ = v₁ ∧ y • v₂ = a) (y z : X) :
    S.ι.graph.Adj (Φ y • S.ι.xv) (Φ z • S.ι.lv) ↔ ΓM.Adj (y • v₁) (z • v₂) := by
  have h1 : S.ι.graph.Adj (Φ y • S.ι.xv) (Φ z • S.ι.lv) ↔
      S.ι.graph.Adj S.ι.xv (Φ (y⁻¹ * z) • S.ι.lv) := by
    rw [← GraphAction.adj_smul (Φ y)⁻¹ (Φ y • S.ι.xv) (Φ z • S.ι.lv), inv_smul_smul,
      ← mul_smul, ← map_inv, ← map_mul]
  have h2 : ΓM.Adj (y • v₁) (z • v₂) ↔ ΓM.Adj v₁ ((y⁻¹ * z) • v₂) := by
    rw [← GraphAction.adj_smul y⁻¹ (y • v₁) (z • v₂), inv_smul_smul, ← mul_smul]
  rw [h1, h2]
  exact D.adj_xv_lv hflag _

theorem XDatum.exists_equiv (D : XDatum S Φ ΓM v₁ v₂)
    (hcov : ∀ a : V, ∃ y : X, y • v₁ = a ∨ y • v₂ = a)
    (hflag : ∀ a, ΓM.Adj v₁ a → ∃ y : X, y • v₁ = v₁ ∧ y • v₂ = a) :
    ∃ e : S.ι.Γ ≃ V, e S.ι.xv = v₁ ∧ e S.ι.lv = v₂ ∧ (∀ y a, e (Φ y • a) = y • e a) ∧
      ∀ a b, S.ι.graph.Adj a b ↔ ΓM.Adj (e a) (e b) := by
  classical
  obtain ⟨e₀, he₁, he₂⟩ := exists_equivariant_map Φ S.ι.baseVert (fun b => cond b v₂ v₁)
    CosetGeom.vtype D.hsurj (fun b y => XDatum.htyp b y) D.hstab
  have hfix : ∀ (b : Bool) (y y' : X), y • cond b v₂ v₁ = y' • cond b v₂ v₁ →
      Φ y • S.ι.baseVert b = Φ y' • S.ι.baseVert b := by
    intro b y y' h
    have h1 : (y⁻¹ * y') • cond b v₂ v₁ = cond b v₂ v₁ := by
      rw [mul_smul, ← h, inv_smul_smul]
    have h2 := (D.hstab b _).mpr h1
    rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff] at h2
    exact h2.symm
  have he : ∀ a : S.ι.Γ, ∀ y : X, Φ y • S.ι.baseVert (CosetGeom.vtype a) = a →
      e₀ a = y • cond (CosetGeom.vtype a) v₂ v₁ := by
    intro a y hy
    have := he₁ (CosetGeom.vtype a) y
    rwa [hy] at this
  have hinj : Function.Injective e₀ := by
    intro a a' h
    obtain ⟨y, hy⟩ := D.hsurj a
    obtain ⟨y', hy'⟩ := D.hsurj a'
    have h1 := he a y hy
    have h2 := he a' y' hy'
    rw [h] at h1
    rw [h1] at h2
    revert hy hy' h2
    rcases hva : CosetGeom.vtype a with _ | _ <;> rcases hva' : CosetGeom.vtype a' with _ | _
    · intro hy hy' h2
      rw [← hy, ← hy']
      exact hfix false y y' h2
    · intro hy hy' h2
      exact absurd h2 (D.disj y y')
    · intro hy hy' h2
      exact absurd h2.symm (D.disj y' y)
    · intro hy hy' h2
      rw [← hy, ← hy']
      exact hfix true y y' h2
  have hsurj : Function.Surjective e₀ := by
    intro a
    obtain ⟨y, hy | hy⟩ := hcov a
    · exact ⟨Φ y • S.ι.baseVert false, by rw [he₁]; exact hy⟩
    · exact ⟨Φ y • S.ι.baseVert true, by rw [he₁]; exact hy⟩
  refine ⟨Equiv.ofBijective e₀ ⟨hinj, hsurj⟩, ?_, ?_, he₂, ?_⟩
  · show e₀ S.ι.xv = v₁
    have := he₁ false 1
    simp only [map_one, one_smul] at this
    exact this
  · show e₀ S.ι.lv = v₂
    have := he₁ true 1
    simp only [map_one, one_smul] at this
    exact this
  · intro a b
    show S.ι.graph.Adj a b ↔ ΓM.Adj (e₀ a) (e₀ b)
    obtain ⟨y, hy⟩ := D.hsurj a
    obtain ⟨z, hz⟩ := D.hsurj b
    have h1 := he a y hy
    have h2 := he b z hz
    rcases a with a' | a' <;> rcases b with b' | b'
    · rw [h1, h2]
      exact iff_of_false CosetGeom.not_adj_inl_inl (D.noadj1 y z)
    · change S.ι.graph.Adj (Sum.inl a') (Sum.inr b') ↔ _
      change Φ y • S.ι.baseVert false = _ at hy
      change Φ z • S.ι.baseVert true = _ at hz
      rw [h1, h2, ← hy, ← hz]
      exact D.adj_mixed hflag y z
    · change S.ι.graph.Adj (Sum.inr a') (Sum.inl b') ↔ _
      change Φ y • S.ι.baseVert true = _ at hy
      change Φ z • S.ι.baseVert false = _ at hz
      rw [h1, h2, ← hy, ← hz, SimpleGraph.adj_comm, SimpleGraph.adj_comm ΓM]
      exact D.adj_mixed hflag z y
    · rw [h1, h2]
      exact iff_of_false CosetGeom.not_adj_inr_inr (D.noadj2 y z)

end Equiv

section Facts

variable [GraphAction X ΓM]

theorem exists_nbr_ne_of_card {Γ : SimpleGraph V} {a : V} (h : 3 ≤ Nat.card (Γ.neighborSet a))
    (w : V) : ∃ c, Γ.Adj a c ∧ c ≠ w := by
  have hs : 3 ≤ (Γ.neighborSet a).ncard := by rwa [← Nat.card_coe_set_eq]
  obtain ⟨c, hc, hne⟩ := Set.exists_ne_of_one_lt_ncard (s := Γ.neighborSet a) (by omega) w
  exact ⟨c, hc, hne⟩

omit [GraphAction X ΓM] in
theorem ModelBase.flag {m : ℕ} {a : V} {Q : Subgroup X} (M : ModelBase ΓM m a Q)
    (hn : 3 ≤ Nat.card (ΓM.neighborSet a)) {w : V} (hw : ΓM.Adj a w) :
    ∀ b, ΓM.Adj a b → ∃ y : X, y • a = a ∧ y • w = b := by
  intro b hb
  obtain ⟨c, hc, hcw⟩ := exists_nbr_ne_of_card hn w
  obtain ⟨c', hc', hc'b⟩ := exists_nbr_ne_of_card hn b
  obtain ⟨g, hg1, hg2, -⟩ := M.two w c b c' hw hc (Ne.symm hcw) hb hc' (Ne.symm hc'b)
  exact ⟨g, hg1, hg2⟩

theorem cov_of_flags (hconn : ΓM.Connected)
    (f₁ : ∀ b, ΓM.Adj v₁ b → ∃ y : X, y • v₁ = v₁ ∧ y • v₂ = b)
    (f₂ : ∀ b, ΓM.Adj v₂ b → ∃ y : X, y • v₂ = v₂ ∧ y • v₁ = b) (a : V) :
    ∃ y : X, y • v₁ = a ∨ y • v₂ = a := by
  have step : ∀ a b : V, ΓM.Adj a b → (∃ y : X, y • v₁ = a ∨ y • v₂ = a) →
      ∃ y : X, y • v₁ = b ∨ y • v₂ = b := by
    intro a b hab ⟨y, hy⟩
    rcases hy with rfl | rfl
    · have h := (GraphAction.adj_smul y⁻¹ (y • v₁) b).mpr hab
      rw [inv_smul_smul] at h
      obtain ⟨y', hy1, hy2⟩ := f₁ _ h
      refine ⟨y * y', Or.inr ?_⟩
      rw [mul_smul, hy2, smul_inv_smul]
    · have h := (GraphAction.adj_smul y⁻¹ (y • v₂) b).mpr hab
      rw [inv_smul_smul] at h
      obtain ⟨y', hy1, hy2⟩ := f₂ _ h
      refine ⟨y * y', Or.inl ?_⟩
      rw [mul_smul, hy2, smul_inv_smul]
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp (hconn.preconnected v₁ a)
  induction hr with
  | refl => exact ⟨1, Or.inl (one_smul _ _)⟩
  | tail _ hbc ih => exact step _ _ hbc ih

theorem pCoreOf_map_inj {p : ℕ} {D H : Type*} [Group D] [Group H] (f : D →* H)
    (hf : Function.Injective f) (Y : Subgroup D) :
    pCoreOf p (Y.map f) = (pCoreOf p Y).map f := by
  let e : ↥Y ≃* ↥(Y.map f) := Subgroup.equivMapOfInjective Y f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [GraphAction X ΓM] in
theorem XDatum.qbar_eq (D : XDatum S Φ ΓM v₁ v₂) (u : S.ι.Γ) (P Q : Subgroup X)
    (hP : ∀ y, y ∈ P ↔ Φ y ∈ stv S.ι u) (hQ : pCoreOf S.p P = Q) : S.Qbar u = Q.map Φ := by
  have h1 : S.N ⊓ stv S.ι u = P.map Φ := by
    rw [D.N_eq]
    ext g
    constructor
    · rintro ⟨⟨y, rfl⟩, hg⟩
      exact ⟨y, (hP y).mpr hg, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, (hP y).mp hy⟩
  unfold LieSetting.Qbar
  rw [h1, pCoreOf_map_inj Φ D.inj, hQ]

omit [GraphAction X ΓM] in
theorem baseFacts_of_model {e : S.ι.Γ ≃ V} (he_eq : ∀ y a, e (Φ y • a) = y • e a)
    (he_adj : ∀ a b, S.ι.graph.Adj a b ↔ ΓM.Adj (e a) (e b)) {u : S.ι.Γ} {Q : Subgroup X}
    (hQ : S.Qbar u = Q.map Φ) (M : ModelBase ΓM S.m (e u) Q) : BaseFacts S u := by
  let iso : S.ι.graph ≃g ΓM := ⟨e, fun {a b} => (he_adj a b).symm⟩
  have hdist : ∀ a b, ΓM.dist (e a) (e b) = S.ι.graph.dist a b := fun a b => iso_dist iso a b
  have hmem : ∀ x ∈ S.Qbar u, ∃ q ∈ Q, Φ q = x := by
    intro x hx
    rw [hQ] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    exact ⟨q, hq, rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw x hx
    obtain ⟨q, hq, rfl⟩ := hmem x hx
    apply e.injective
    rw [he_eq]
    exact M.Qfix (e w) ((he_adj _ _).mp hw) q hq
  · intro v v' hv hv'
    rw [← hdist] at hv hv'
    obtain ⟨q, hq, hqv⟩ := M.Qtrans (e v) (e v') hv hv'
    refine ⟨Φ q, hQ ▸ ⟨q, hq, rfl⟩, ?_⟩
    apply e.injective
    rw [he_eq, hqv]
  · intro v hv x hx hxv
    obtain ⟨q, hq, rfl⟩ := hmem x hx
    have h1 : q • e v = e v := by rw [← he_eq, hxv]
    rw [M.Qfree (e v) (by rw [hdist]; exact hv) q hq h1, map_one]
  · intro a b a' b' ha hb hab ha' hb' hab'
    obtain ⟨g, hgu, hga, hgb⟩ := M.two (e a) (e b) (e a') (e b') ((he_adj _ _).mp ha)
      ((he_adj _ _).mp hb) (e.injective.ne hab) ((he_adj _ _).mp ha') ((he_adj _ _).mp hb')
      (e.injective.ne hab')
    refine ⟨Φ g, ?_, ?_, ?_⟩ <;> apply e.injective <;> rw [he_eq] <;> assumption

theorem facts45L_of_model (D : XDatum S Φ ΓM v₁ v₂) (hP : IsGenPolygon ΓM S.m)
    (hn1 : 3 ≤ Nat.card (ΓM.neighborSet v₁)) (hn2 : 3 ≤ Nat.card (ΓM.neighborSet v₂))
    (Q₁ Q₂ : Subgroup X) (hQ₁ : pCoreOf S.p (MulAction.stabilizer X v₁) = Q₁)
    (hQ₂ : pCoreOf S.p (MulAction.stabilizer X v₂) = Q₂) (M₁ : ModelBase ΓM S.m v₁ Q₁)
    (M₂ : ModelBase ΓM S.m v₂ Q₂) : S.Facts45L := by
  have f₁ := M₁.flag hn1 D.adj12
  have f₂ := M₂.flag hn2 D.adj12.symm
  obtain ⟨e, he1, he2, heq, hadj⟩ := D.exists_equiv (cov_of_flags hP.connected f₁ f₂) f₁
  let iso : S.ι.graph ≃g ΓM := ⟨e, fun {a b} => (hadj a b).symm⟩
  have hpoly : IsGenPolygon S.ι.graph S.m := IsGenPolygon.of_iso iso hP
  have hcard : ∀ u : S.ι.Γ, Nat.card (CosetGeom.nbrs u) = Nat.card (ΓM.neighborSet (e u)) := by
    intro u
    exact Nat.card_congr (e.subtypeEquiv (fun δ => hadj u δ))
  have c1 := nbrs_xv_card (c := S.ι) S.hι
  have c2 := nbrs_lv_card (c := S.ι) S.hι
  have thick1 : 2 ≤ S.α.qOne := by
    unfold RankTwoAmalgam.qOne
    rw [← c1, hcard, he1]
    omega
  have thick2 : 2 ≤ S.α.qTwo := by
    unfold RankTwoAmalgam.qTwo
    rw [← c2, hcard, he2]
    omega
  refine facts45L_of_baseFacts S thick1 thick2 hpoly ?_ ?_
  · refine baseFacts_of_model heq hadj
      (D.qbar_eq S.ι.xv (MulAction.stabilizer X v₁) Q₁ (fun y => ?_) hQ₁) (by rw [he1]; exact M₁)
    rw [MulAction.mem_stabilizer_iff, ← D.stab1 y]
    exact MulAction.mem_stabilizer_iff.symm
  · refine baseFacts_of_model heq hadj
      (D.qbar_eq S.ι.lv (MulAction.stabilizer X v₂) Q₂ (fun y => ?_) hQ₂) (by rw [he2]; exact M₂)
    rw [MulAction.mem_stabilizer_iff, ← D.stab2 y]
    exact MulAction.mem_stabilizer_iff.symm

end Facts

end Setting

end CFSG.Quasithin.H13.F431.F45
