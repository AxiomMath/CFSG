module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Ext2
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KStruct

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)
open scoped MatrixGroups commutatorElement

section KerAct

variable {G : Type} [Group G]

theorem conj_mem_pCoreOf_of_mem_normalizer {X : Subgroup G} {h x : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ pCoreOf 2 X) :
    h * x * h⁻¹ ∈ pCoreOf 2 X :=
  (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X hh) x).mp hx

theorem one_mem_kerAct_carrier (K : Subgroup G) :
    (1 : G) ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ k ∈ K, (1 : G) * k * (1 : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  refine ⟨Subgroup.one_mem _, fun k _ => ?_⟩
  simpa using (pCoreOf 2 K).one_mem

theorem mul_mem_kerAct_carrier {K : Subgroup G} {a b : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K)
    (hb : b ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, b * k * b⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    a * b ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ k ∈ K, a * b * k * (a * b)⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨ha, hak⟩ := ha
  obtain ⟨hb, hbk⟩ := hb
  refine ⟨Subgroup.mul_mem _ ha hb, fun k hk => ?_⟩
  have e : a * b * k * (a * b)⁻¹ * k⁻¹ = a * (b * k * b⁻¹ * k⁻¹) * a⁻¹ * (a * k * a⁻¹ * k⁻¹) := by
    group
  rw [e]
  exact (pCoreOf 2 K).mul_mem (conj_mem_pCoreOf_of_mem_normalizer ha (hbk k hk)) (hak k hk)

theorem inv_mem_kerAct_carrier {K : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, a * k * a⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    a⁻¹ ∈ Subgroup.normalizer (K : Set G) ∧
      ∀ k ∈ K, a⁻¹ * k * a⁻¹⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  obtain ⟨ha, hak⟩ := ha
  have ha' : a⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ ha
  refine ⟨ha', fun k hk => ?_⟩
  have hk₁ : a⁻¹ * k * a ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp ha' k).mp hk
    rwa [inv_inv] at this
  rw [inv_inv]
  have e : a⁻¹ * k * a * k⁻¹ = (a * (a⁻¹ * k * a) * a⁻¹ * (a⁻¹ * k * a)⁻¹)⁻¹ := by
    group
  rw [e]
  exact (pCoreOf 2 K).inv_mem (hak _ hk₁)

@[expose] def kerAct (K : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K}
  one_mem' := one_mem_kerAct_carrier K
  mul_mem' := fun ha hb => mul_mem_kerAct_carrier ha hb
  inv_mem' := fun ha => inv_mem_kerAct_carrier ha

variable {K : Subgroup G}

theorem mem_kerAct {g : G} :
    g ∈ kerAct K ↔ g ∈ Subgroup.normalizer (K : Set G) ∧ ∀ k ∈ K, g * k * g⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
  Iff.rfl

theorem mem_map_conj_iff' (X : Subgroup G) (s y : G) :
    y ∈ X.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * y * s ∈ X := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : s⁻¹ * (MulAut.conj s).toMonoidHom z * s = z := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact hz
  · intro h
    exact ⟨s⁻¹ * y * s, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem conj_mem_normalizer_map (s : G) {X : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) :
    s * x * s⁻¹ ∈ Subgroup.normalizer ((X.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_map_conj_iff', mem_map_conj_iff']
  have e : s⁻¹ * (s * x * s⁻¹ * y * (s * x * s⁻¹)⁻¹) * s = x * (s⁻¹ * y * s) * x⁻¹ := by
    group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hx _

theorem kerAct_conj_mem_map (s : G) {X : Subgroup G} {x : G} (hx : x ∈ kerAct X) :
    s * x * s⁻¹ ∈ kerAct (X.map (MulAut.conj s).toMonoidHom) := by
  obtain ⟨hxN, hxk⟩ := mem_kerAct.mp hx
  refine mem_kerAct.mpr ⟨conj_mem_normalizer_map s hxN, fun k' hk' => ?_⟩
  rw [mem_map_conj_iff'] at hk'
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj s) X, mem_map_conj_iff']
  have e : s⁻¹ * (s * x * s⁻¹ * k' * (s * x * s⁻¹)⁻¹ * k'⁻¹) * s =
      x * (s⁻¹ * k' * s) * x⁻¹ * (s⁻¹ * k' * s)⁻¹ := by
    group
  rw [e]
  exact hxk _ hk'

theorem map_conj_map_conj_inv (X : Subgroup G) (s : G) :
    (X.map (MulAut.conj s).toMonoidHom).map (MulAut.conj s⁻¹).toMonoidHom = X := by
  ext z
  rw [mem_map_conj_iff', mem_map_conj_iff']
  have e : s⁻¹ * (s⁻¹⁻¹ * z * s⁻¹) * s = z := by group
  rw [e]

theorem mem_kerAct_map_conj_iff (s y : G) (K : Subgroup G) :
    y ∈ kerAct (K.map (MulAut.conj s).toMonoidHom) ↔ s⁻¹ * y * s ∈ kerAct K := by
  constructor
  · intro hy
    have h1 := kerAct_conj_mem_map s⁻¹ hy
    rw [map_conj_map_conj_inv, inv_inv] at h1
    exact h1
  · intro hz
    have h1 := kerAct_conj_mem_map s hz
    have e : s * (s⁻¹ * y * s) * s⁻¹ = y := by group
    rwa [e] at h1

theorem kerAct_map_conj (K : Subgroup G) (s : G) :
    kerAct (K.map (MulAut.conj s).toMonoidHom) = (kerAct K).map (MulAut.conj s).toMonoidHom := by
  ext y
  rw [mem_map_conj_iff', mem_kerAct_map_conj_iff]

theorem conj_mem_kerAct_of_mem_normalizer {X : Subgroup G} {h x : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) (hx : x ∈ kerAct X) :
    h * x * h⁻¹ ∈ kerAct X := by
  have h1 := kerAct_conj_mem_map h hx
  have e : X.map (MulAut.conj h).toMonoidHom = X := A38.map_conj_eq_iff.mpr hh
  rwa [e] at h1

end KerAct

section Helpers

variable {G : Type} [Group G]

theorem map_conj_map_conj (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  have hf : (MulAut.conj b).toMonoidHom.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj (b * a)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hf]

theorem map_conj_eq_of_map_conj_eq (K : Subgroup G) {t₁ t : G}
    (h : K.map (MulAut.conj t₁).toMonoidHom = K.map (MulAut.conj (t₁ * t)).toMonoidHom) :
    K.map (MulAut.conj t).toMonoidHom = K := by
  have h2 := congrArg (fun Y : Subgroup G => Y.map (MulAut.conj t₁⁻¹).toMonoidHom) h
  rw [map_conj_map_conj_inv, map_conj_map_conj, inv_mul_cancel_left] at h2
  exact h2.symm

theorem le_normalizer_of_conj_mem' {S D : Subgroup G}
    (h : ∀ s ∈ S, ∀ x ∈ D, s * x * s⁻¹ ∈ D) : S ≤ Subgroup.normalizer (D : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h s hs x hx, fun hx => ?_⟩
  have h2 := h s⁻¹ (S.inv_mem hs) _ hx
  have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
  rwa [e] at h2

theorem mem_pCoreOf_of_central {K : Subgroup G}
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) {k : G} (hk : k ∈ K)
    (hc : ∀ x ∈ K, k * x * k⁻¹ * x⁻¹ ∈ pCoreOf 2 K) : k ∈ pCoreOf 2 K := by
  have h1 : CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj K k (Subgroup.le_normalizer hk) = 1 := by
    rw [CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj_eq_one_iff]
    exact hc
  have h3 : MulAut.conj ((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
    rw [← CFSG.Quasithin.EmptyFaithfulMultiple.L15420.quotConj_of_mem hk]
    exact h1
  have hcen : ((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun φ => φ x) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * ((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K)
        = (((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) * x *
            ((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K)⁻¹) *
            ((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by rw [hx]
      _ = ((⟨k, hk⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) * x := by group
  rw [hZ, Subgroup.mem_bot] at hcen
  exact CFSG.Quasithin.EmptyFaithfulMultiple.L15420.mk_eq_one_iff.mp hcen

end Helpers

section CentreQuot

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem center_quot_of_cfg (c : A2Cfg G T M L D H K q) :
    Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  have hq5 : 5 ≤ q := by
    have := c.q_mod
    have := c.q_prime.two_le
    omega
  haveI : Fact q.Prime := ⟨c.q_prime⟩
  haveI : NeZero q := ⟨c.q_prime.ne_zero⟩
  obtain ⟨e⟩ := nonempty_mulEquiv_psl_zmod c.q_prime c.model
  have hcen : Subgroup.center (PSL(2, ZMod q)) = ⊥ :=
    L2q.center_eq_bot (Nat.card_zmod q) c.q_prime hq5
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hc : e x ∈ Subgroup.center (PSL(2, ZMod q)) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [hcen, Subgroup.mem_bot] at hc
  exact e.injective (by rw [hc, map_one])

theorem center_quot_map_conj (K : Subgroup G) (t : G)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    Subgroup.center (↥(K.map (MulAut.conj t).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(K.map (MulAut.conj t).toMonoidHom)) = ⊥ := by
  let e : ↥K ≃* ↥(K.map (MulAut.conj t).toMonoidHom) :=
    Subgroup.equivMapOfInjective K (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  let φ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* (↥(K.map (MulAut.conj t).toMonoidHom) ⧸
      CFSG.pCore 2 ↥(K.map (MulAut.conj t).toMonoidHom)) :=
    QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥(K.map (MulAut.conj t).toMonoidHom)) e
      (CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hc : φ.symm x ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    apply φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hx (φ g)
  rw [hZ, Subgroup.mem_bot] at hc
  calc x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
    _ = 1 := by rw [hc, map_one]

end CentreQuot

section TCAct

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.TC_acts_trivially (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    a2TC K T ≤ kerAct K ⊓ kerAct (K.map (MulAut.conj t).toMonoidHom) := by
  have hTG : T ≤ conjClosure K T ⊔ T := le_sup_right
  have hKG : K ≤ conjClosure K T ⊔ T := (le_conjClosure K T).trans le_sup_left
  have hTC : ∀ s ∈ pCoreOf 2 (conjClosure K T ⊔ T), s ∈ kerAct K := by
    intro s hs
    have hsN : s ∈ Subgroup.normalizer (K : Set G) :=
      c.R_le_normalizer_K h37 h38 (c.TC_le_R hs)
    refine mem_kerAct.mpr ⟨hsN, fun k hk => ?_⟩
    have hkG := hKG hk
    have hsK : s * k * s⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp hsN k).mp hk) (K.inv_mem hk)
    have hsP : s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) := by
      have e : s * k * s⁻¹ * k⁻¹ = s * (k * s⁻¹ * k⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hs
        (conj_mem_pCoreOf_of_mem_normalizer (Subgroup.le_normalizer hkG) (Subgroup.inv_mem _ hs))
    have hKN2 : K ≤ Subgroup.normalizer (pCoreOf 2 (conjClosure K T ⊔ T) : Set G) :=
      fun k hk => CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hKG hk)
    have hXle : K ⊓ pCoreOf 2 (conjClosure K T ⊔ T) ≤ pCoreOf 2 K :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (F7.le_normalizer_inf Subgroup.le_normalizer hKN2)
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hXle (Subgroup.mem_inf.mpr ⟨hsK, hsP⟩)
  intro s hs
  refine Subgroup.mem_inf.mpr ⟨hTC s hs, ?_⟩
  rw [mem_kerAct_map_conj_iff]
  apply hTC
  have htG : t⁻¹ ∈ Subgroup.normalizer ((conjClosure K T ⊔ T : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.inv_mem _ (hTG ht))
  have h1 := conj_mem_pCoreOf_of_mem_normalizer htG hs
  rwa [inv_inv] at h1

end TCAct

section LeTC

variable {G : Type} [Group G] [Finite G]

theorem perm_conj {K : Subgroup G} {t t₁ : G} (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hs : K.map (MulAut.conj (t₁ * t)).toMonoidHom = K ∨
      K.map (MulAut.conj (t₁ * t)).toMonoidHom = K.map (MulAut.conj t).toMonoidHom) :
    (K.map (MulAut.conj t₁).toMonoidHom = K →
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t₁).toMonoidHom =
        K.map (MulAut.conj t).toMonoidHom) ∧
    (K.map (MulAut.conj t₁).toMonoidHom = K.map (MulAut.conj t).toMonoidHom →
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t₁).toMonoidHom = K) := by
  rw [map_conj_map_conj]
  constructor
  · intro hA
    rcases hs with h | h
    · exact absurd (map_conj_eq_of_map_conj_eq K (hA.trans h.symm))
        (fun h' => htK (A38.map_conj_eq_iff.mp h'))
    · exact h
  · intro hB
    rcases hs with h | h
    · exact h
    · exact absurd (map_conj_eq_of_map_conj_eq K (hB.trans h.symm))
        (fun h' => htK (A38.map_conj_eq_iff.mp h'))

theorem conj_mem_kerAct_pair {K K' : Subgroup G} {t₁ : G}
    (hperm : (K.map (MulAut.conj t₁).toMonoidHom = K ∧ K'.map (MulAut.conj t₁).toMonoidHom = K') ∨
      (K.map (MulAut.conj t₁).toMonoidHom = K' ∧ K'.map (MulAut.conj t₁).toMonoidHom = K))
    {x : G} (hx : x ∈ kerAct K ⊓ kerAct K') :
    t₁ * x * t₁⁻¹ ∈ kerAct K ⊓ kerAct K' := by
  obtain ⟨hK, hK'⟩ := Subgroup.mem_inf.mp hx
  have a1 := kerAct_conj_mem_map t₁ hK
  have a2 := kerAct_conj_mem_map t₁ hK'
  rcases hperm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at a1
    rw [h2] at a2
    exact Subgroup.mem_inf.mpr ⟨a1, a2⟩
  · rw [h1] at a1
    rw [h2] at a2
    exact Subgroup.mem_inf.mpr ⟨a2, a1⟩

@[expose] def a2D1 (K K' T : Subgroup G) : Subgroup G :=
  (conjClosure K T ⊔ T) ⊓ (kerAct K ⊓ kerAct K')

theorem mem_a2D1 {K K' T : Subgroup G} {x : G} :
    x ∈ a2D1 K K' T ↔ x ∈ conjClosure K T ⊔ T ∧ x ∈ kerAct K ∧ x ∈ kerAct K' := Iff.rfl

theorem le_TC_core {K K' T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hKK₀ : conjClosure K T = K ⊔ K')
    (hK'N : K' ≤ Subgroup.normalizer (K : Set G)) (hKN' : K ≤ Subgroup.normalizer (K' : Set G))
    (hK'kerK : K' ≤ kerAct K) (hKkerK' : K ≤ kerAct K')
    (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K) (hcomm' : ⁅K, K'⁆ ≤ pCoreOf 2 K')
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hZ' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥)
    (hperm : ∀ t₁ ∈ T,
      (K.map (MulAut.conj t₁).toMonoidHom = K ∧ K'.map (MulAut.conj t₁).toMonoidHom = K') ∨
      (K.map (MulAut.conj t₁).toMonoidHom = K' ∧ K'.map (MulAut.conj t₁).toMonoidHom = K)) :
    a2D1 K K' T ≤ pCoreOf 2 (conjClosure K T ⊔ T) := by
  have hKG : K ≤ conjClosure K T ⊔ T := (le_conjClosure K T).trans le_sup_left
  have hK'C : K' ≤ conjClosure K T := by
    rw [hKK₀]
    exact le_sup_right
  have hK'G : K' ≤ conjClosure K T ⊔ T := hK'C.trans le_sup_left
  have hTG : T ≤ conjClosure K T ⊔ T := le_sup_right
  have hTN : T ≤ Subgroup.normalizer ((a2D1 K K' T : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem'
    intro t₁ ht₁ x hx
    obtain ⟨hxG, hxK, hxK'⟩ := mem_a2D1.mp hx
    have hc := conj_mem_kerAct_pair (hperm t₁ ht₁) (Subgroup.mem_inf.mpr ⟨hxK, hxK'⟩)
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.mp hc
    exact mem_a2D1.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTG ht₁) hxG)
      (Subgroup.inv_mem _ (hTG ht₁)), hc1, hc2⟩
  have hKN : K ≤ Subgroup.normalizer ((a2D1 K K' T : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem'
    intro k hk x hx
    obtain ⟨hxG, hxK, hxK'⟩ := mem_a2D1.mp hx
    exact mem_a2D1.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hKG hk) hxG)
      (Subgroup.inv_mem _ (hKG hk)),
      conj_mem_kerAct_of_mem_normalizer (Subgroup.le_normalizer hk) hxK,
      conj_mem_kerAct_of_mem_normalizer (hKN' hk) hxK'⟩
  have hK'N' : K' ≤ Subgroup.normalizer ((a2D1 K K' T : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem'
    intro k hk x hx
    obtain ⟨hxG, hxK, hxK'⟩ := mem_a2D1.mp hx
    exact mem_a2D1.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (hK'G hk) hxG)
      (Subgroup.inv_mem _ (hK'G hk)),
      conj_mem_kerAct_of_mem_normalizer (hK'N hk) hxK,
      conj_mem_kerAct_of_mem_normalizer (Subgroup.le_normalizer hk) hxK'⟩
  have hG2N : conjClosure K T ⊔ T ≤ Subgroup.normalizer ((a2D1 K K' T : Subgroup G) : Set G) :=
    sup_le (hKK₀.le.trans (sup_le hKN hK'N')) hTN
  have hK'N2 : K' ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    fun k hk => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hK'N hk)
  have hP : a2D1 K K' T ⊓ conjClosure K T ≤ pCoreOf 2 K ⊔ pCoreOf 2 K' := by
    intro g hg
    obtain ⟨hgD, hgK₀⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨-, hgK, hgK'⟩ := mem_a2D1.mp hgD
    have hgset : g ∈ ((K ⊔ K' : Subgroup G) : Set G) := by
      rw [← hKK₀]
      exact hgK₀
    rw [Subgroup.coe_mul_of_right_le_normalizer_left K K' hK'N, Set.mem_mul] at hgset
    obtain ⟨k, hk, k', hk', rfl⟩ := hgset
    have hk₁ : k ∈ K := hk
    have hk₂ : k' ∈ K' := hk'
    have hkKer : k ∈ kerAct K := by
      have h1 := (kerAct K).mul_mem hgK ((kerAct K).inv_mem (hK'kerK hk₂))
      rwa [mul_inv_cancel_right] at h1
    have hkO : k ∈ pCoreOf 2 K :=
      mem_pCoreOf_of_central hZ hk₁ (fun x hx => (mem_kerAct.mp hkKer).2 x hx)
    have hk'Ker' : k' ∈ kerAct K' := by
      have h1 := (kerAct K').mul_mem ((kerAct K').inv_mem (hKkerK' hk₁)) hgK'
      rwa [inv_mul_cancel_left] at h1
    have hk'O : k' ∈ pCoreOf 2 K' :=
      mem_pCoreOf_of_central hZ' hk₂ (fun x hx => (mem_kerAct.mp hk'Ker').2 x hx)
    exact Subgroup.mul_mem_sup hkO hk'O
  have hPK : IsPGroup 2 ↥(pCoreOf 2 K ⊔ pCoreOf 2 K') :=
    isPGroup_two_of_le_sup (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K')
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans hK'N2) le_rfl
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_right)
  have hPD : IsPGroup 2 ↥(a2D1 K K' T ⊓ conjClosure K T) := hPK.to_le hP
  have hD2 : IsPGroup 2 ↥(a2D1 K K' T) :=
    isPGroup_two_of_le_sup hT2 (le_normalizer_conjClosure K T) inf_le_left hPD
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hG2N hD2

end LeTC

section LeTCMain

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.le_TC_of_acts_trivially (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    a2G2 K T ⊓ (kerAct K ⊓ kerAct (K.map (MulAut.conj t).toMonoidHom)) ≤ a2TC K T := by
  have hTH : T ≤ H := c.nf.inH.1
  have htH₀ : t ∈ H ⊔ D := Subgroup.mem_sup_left (hTH ht)
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
  have hK' : K' ∈ cComp (H ⊔ D) := CFSG.Quasithin.map_conj_mem_cComp hK htH₀
  have hKK' : K ≠ K' := fun h => htK (A38.map_conj_eq_iff.mp h.symm)
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := le_normalizer_of_mem_cComp hK' hK
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hK'
  obtain ⟨t₀, -, -, -, hKK₀, hs⟩ := c.kstruct h37 h38
  have hKt : K' = K.map (MulAut.conj t₀).toMonoidHom := by
    rcases hs t ht with h | h
    · exact absurd (A38.map_conj_eq_iff.mp h) htK
    · exact h
  have hKK₀' : conjClosure K T = K ⊔ K' := hKK₀.trans (by rw [← hKt])
  have hs' : ∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom = K ∨
      K.map (MulAut.conj s).toMonoidHom = K' := by
    intro s hs_
    rcases hs s hs_ with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hKt.symm)
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_quot_of_cfg c
  have hZ' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥ := center_quot_map_conj K t hZ
  have hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15420.commutator_le_pCoreOf_of_ne hK hK' hKK' c.nf.Kq hZ
  have hKK'comm : ⁅K, K'⁆ ≤ K' := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact K'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN' hg) h).mp hh) (K'.inv_mem hh)
  have hK'N2 : K' ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    fun k hk => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hK'N hk)
  have hcomm' : ⁅K, K'⁆ ≤ pCoreOf 2 K' := by
    have hXN : K' ≤ Subgroup.normalizer ((pCoreOf 2 K ⊓ K' : Subgroup G) : Set G) :=
      F7.le_normalizer_inf hK'N2 Subgroup.le_normalizer
    have hXle : pCoreOf 2 K ⊓ K' ≤ pCoreOf 2 K' :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hXN
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
    exact (le_inf hcomm hKK'comm).trans hXle
  have hK'kerK : K' ≤ kerAct K := by
    have h2 : ⁅K', K⁆ ≤ pCoreOf 2 K := by
      rw [Subgroup.commutator_comm]
      exact hcomm
    intro k' hk'
    refine mem_kerAct.mpr ⟨hK'N hk', fun x hx => ?_⟩
    have h3 := h2 (Subgroup.commutator_mem_commutator hk' hx)
    rwa [commutatorElement_def] at h3
  have hKkerK' : K ≤ kerAct K' := by
    intro k hk
    refine mem_kerAct.mpr ⟨hKN' hk, fun x hx => ?_⟩
    have h3 := hcomm' (Subgroup.commutator_mem_commutator hk hx)
    rwa [commutatorElement_def] at h3
  have hperm : ∀ t₁ ∈ T,
      (K.map (MulAut.conj t₁).toMonoidHom = K ∧ K'.map (MulAut.conj t₁).toMonoidHom = K') ∨
      (K.map (MulAut.conj t₁).toMonoidHom = K' ∧ K'.map (MulAut.conj t₁).toMonoidHom = K) := by
    intro t₁ ht₁
    have hp := perm_conj htK (hs' (t₁ * t) (T.mul_mem ht₁ ht))
    rcases hs' t₁ ht₁ with h | h
    · exact Or.inl ⟨h, hp.1 h⟩
    · exact Or.inr ⟨h, hp.2 h⟩
  exact le_TC_core c.nf.hyp.sylow.1 hKK₀' hK'N hKN' hK'kerK hKkerK' hcomm hcomm' hZ hZ' hperm

theorem A2Cfg.TC_eq (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    a2TC K T = a2G2 K T ⊓ (kerAct K ⊓ kerAct (K.map (MulAut.conj t).toMonoidHom)) :=
  le_antisymm (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (c.TC_acts_trivially h37 h38 ht htK))
    (c.le_TC_of_acts_trivially h37 h38 ht htK)

end LeTCMain

end CFSG.Quasithin.H13.NFa2
