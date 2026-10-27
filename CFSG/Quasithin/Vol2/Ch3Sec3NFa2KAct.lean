module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KStruct
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Inv
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2PslA

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.EmptyFaithfulMultiple

namespace KAct

variable {G : Type} [Group G]

theorem conj_injective_of_center_eq_bot {Q : Type} [Group Q] (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut Q => φ g) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem map_conj_map (X : Subgroup G) (a b : G) :
    (X.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      X.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (X : Subgroup G) : X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  ext x
  simp [Subgroup.mem_map]

theorem map_map_conj_inv (X : Subgroup G) (g : G) :
    (X.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = X := by
  rw [map_conj_map, inv_mul_cancel, map_conj_one]

theorem sq_mem_normalizer_of_action {T K K' : Subgroup G} {t₀ g : G}
    (hK' : K' = K.map (MulAut.conj t₀).toMonoidHom)
    (ht₀N : t₀ ∉ Subgroup.normalizer (K : Set G))
    (hT : ∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom = K ∨
      K.map (MulAut.conj s).toMonoidHom = K')
    (ht₀T : t₀ ∈ T) (hgT : g ∈ T) : g ^ 2 ∈ Subgroup.normalizer (K : Set G) := by
  have hKK' : K ≠ K' := fun h => ht₀N
    (CFSG.Quasithin.EmptyFaithfulMultiple.mem_normalizer_iff_map_conj.mpr (hK'.symm.trans h.symm))
  have hK'g : K'.map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj (g * t₀)).toMonoidHom := by
    rw [hK']
    exact map_conj_map K t₀ g
  rw [pow_two, CFSG.Quasithin.EmptyFaithfulMultiple.mem_normalizer_iff_map_conj]
  rcases hT g hgT with hg | hg
  · rw [← map_conj_map, hg, hg]
  · rcases hT (g * t₀) (T.mul_mem hgT ht₀T) with hgt | hgt
    · rw [← map_conj_map, hg, hK'g, hgt]
    · exfalso
      have h1 : K'.map (MulAut.conj g⁻¹).toMonoidHom = K := by
        rw [← hg]
        exact map_map_conj_inv K g
      have h2 : K'.map (MulAut.conj g⁻¹).toMonoidHom = K' := by
        have hK'g' : K'.map (MulAut.conj g).toMonoidHom = K' := hK'g.trans hgt
        calc K'.map (MulAut.conj g⁻¹).toMonoidHom
            = (K'.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
              rw [hK'g']
          _ = K' := map_map_conj_inv K' g
      exact hKK' (h1.symm.trans h2)

theorem quotConj_inv_eq {L : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    L15420.quotConj L g⁻¹ (Subgroup.inv_mem _ hg) = (L15420.quotConj L g hg)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  rw [← L15420.quotConj_mul hg (Subgroup.inv_mem _ hg)]
  exact (L15420.quotConj_congr (mul_inv_cancel g) _ (Subgroup.one_mem _)).trans L15420.quotConj_one

theorem quotConj_conj_eq {L : Subgroup G} {g r : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hr : r ∈ Subgroup.normalizer (L : Set G))
    (hgr : g * r * g⁻¹ ∈ Subgroup.normalizer (L : Set G)) :
    L15420.quotConj L (g * r * g⁻¹) hgr =
      L15420.quotConj L g hg * L15420.quotConj L r hr * (L15420.quotConj L g hg)⁻¹ := by
  rw [L15420.quotConj_mul (Subgroup.mul_mem _ hg hr) (Subgroup.inv_mem _ hg),
    L15420.quotConj_mul hg hr, quotConj_inv_eq hg]

theorem mk_eq_iff_coe {K : Subgroup G} {a b : ↥K} :
    (QuotientGroup.mk a : ↥K ⧸ CFSG.pCore 2 ↥K) = QuotientGroup.mk b ↔
      (a : G)⁻¹ * (b : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq]
  have h := L15420.mk_eq_one_iff (x := a⁻¹ * b)
  rw [QuotientGroup.eq_one_iff] at h
  exact h

theorem inv_mul_mem_of_mul_inv_mem {K : Subgroup G} {a b : G} (ha : a ∈ K)
    (h : a * b⁻¹ ∈ pCoreOf 2 K) : a⁻¹ * b ∈ pCoreOf 2 K := by
  have hn : (a * b⁻¹)⁻¹ ∈ pCoreOf 2 K := (pCoreOf 2 K).inv_mem h
  have hc := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (K.inv_mem ha)) _).mp hn
  have e : a⁻¹ * b = a⁻¹ * (a * b⁻¹)⁻¹ * a⁻¹⁻¹ := by group
  rw [e]
  exact hc

theorem mul_inv_mem_of_inv_mul_mem {K : Subgroup G} {u v : G} (hu : u ∈ K)
    (h : u⁻¹ * v ∈ pCoreOf 2 K) : u * v⁻¹ ∈ pCoreOf 2 K := by
  have hn : (u⁻¹ * v)⁻¹ ∈ pCoreOf 2 K := (pCoreOf 2 K).inv_mem h
  have hc := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hu) _).mp hn
  have e : u * v⁻¹ = u * (u⁻¹ * v)⁻¹ * u⁻¹ := by group
  rw [e]
  exact hc

theorem quotConj_eq_conj_of_forall {K : Subgroup G} {s y : G}
    (hs : s ∈ Subgroup.normalizer (K : Set G)) (hy : y ∈ K)
    (h : ∀ x ∈ K, (s * x * s⁻¹) * (y * x * y⁻¹)⁻¹ ∈ pCoreOf 2 K) :
    L15420.quotConj K s hs = MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [L15420.quotConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, mk_eq_iff_coe]
  simp only [L15420.conjRestr_apply_coe, Subgroup.coe_mul, Subgroup.coe_inv]
  have hA : s * (l : G) * s⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hs l).mp l.2
  exact inv_mul_mem_of_mul_inv_mem hA (h l l.2)

theorem quot_eq_conj_of_induces {K S : Subgroup G}
    (hI : CFSG.Quasithin.H13.InducesInnerOn S K)
    {s : G} (hs : s ∈ S) (hN : s ∈ Subgroup.normalizer (K : Set G)) :
    ∃ w : ↥K ⧸ CFSG.pCore 2 ↥K, L15420.quotConj K s hN = MulAut.conj w := by
  obtain ⟨y, hy, hyK⟩ := hI s hs
  exact ⟨QuotientGroup.mk ⟨y, hy⟩, quotConj_eq_conj_of_forall hN hy hyK⟩

@[expose] noncomputable def actHom (K S : Subgroup G) (hS : S ≤ Subgroup.normalizer (K : Set G)) :
    ↥S →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K) :=
  { toFun := fun s => L15420.quotConj K (s : G) (hS s.2)
    map_one' := L15420.quotConj_one
    map_mul' := fun s t => L15420.quotConj_mul (hS s.2) (hS t.2) }

theorem actHom_apply {K S : Subgroup G} {hS : S ≤ Subgroup.normalizer (K : Set G)} (s : ↥S) :
    actHom K S hS s = L15420.quotConj K (s : G) (hS s.2) := rfl

@[expose] noncomputable def actA (K S : Subgroup G) (hS : S ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup (↥K ⧸ CFSG.pCore 2 ↥K) :=
  ((actHom K S hS).range).comap
    (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K))

theorem mem_actA_iff {K S : Subgroup G} {hS : S ≤ Subgroup.normalizer (K : Set G)}
    {z : ↥K ⧸ CFSG.pCore 2 ↥K} :
    z ∈ actA K S hS ↔ ∃ s : ↥S, actHom K S hS s = MulAut.conj z := by
  rw [actA, Subgroup.mem_comap, MonoidHom.mem_range]

theorem isPGroup_actA {K S : Subgroup G} {hS : S ≤ Subgroup.normalizer (K : Set G)}
    (hSp : IsPGroup 2 ↥S)
    (hinj : Function.Injective
      (MulAut.conj : (↥K ⧸ CFSG.pCore 2 ↥K) →* MulAut (↥K ⧸ CFSG.pCore 2 ↥K))) :
    IsPGroup 2 ↥(actA K S hS) := by
  intro z
  obtain ⟨s, hs⟩ := mem_actA_iff.mp z.2
  obtain ⟨k, hk⟩ := hSp s
  refine ⟨k, Subtype.ext ?_⟩
  show (z : ↥K ⧸ CFSG.pCore 2 ↥K) ^ 2 ^ k = 1
  apply hinj
  rw [map_pow, ← hs, ← map_pow, hk, map_one, map_one]

theorem quotConj_eq_one_of_actA_eq_bot {K S : Subgroup G}
    {hS : S ≤ Subgroup.normalizer (K : Set G)} (hA : actA K S hS = ⊥)
    (hinner : ∀ s : ↥S, ∃ w : ↥K ⧸ CFSG.pCore 2 ↥K, actHom K S hS s = MulAut.conj w)
    {r : G} (hr : r ∈ S) : L15420.quotConj K r (hS hr) = 1 := by
  obtain ⟨w, hw⟩ := hinner ⟨r, hr⟩
  have hwA : w ∈ actA K S hS := mem_actA_iff.mpr ⟨⟨r, hr⟩, hw⟩
  rw [hA, Subgroup.mem_bot] at hwA
  rw [hwA, map_one] at hw
  exact hw

theorem le_normalizer_of_act_trivial {K R : Subgroup G} (hR : pCoreOf 2 K ≤ R)
    (hact : ∀ r ∈ R, ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 K) :
    K ≤ Subgroup.normalizer (R : Set G) := by
  have fwd : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R := by
    intro k hk r hr
    have h1 := hact r⁻¹ (R.inv_mem hr) k hk
    rw [inv_inv] at h1
    have h2 : r⁻¹ * k * r * k⁻¹ ∈ R := hR h1
    have e : k * r * k⁻¹ = r * (r⁻¹ * k * r * k⁻¹) := by group
    rw [e]
    exact R.mul_mem hr h2
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨fun hr => fwd k hk r hr, fun hr => ?_⟩
  have h := fwd k⁻¹ (K.inv_mem hk) (k * r * k⁻¹) hr
  have e : k⁻¹ * (k * r * k⁻¹) * k⁻¹⁻¹ = r := by group
  rwa [e] at h

theorem conj_mem_actA {K S : Subgroup G} {hS : S ≤ Subgroup.normalizer (K : Set G)} {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgS : g ∈ Subgroup.normalizer (S : Set G))
    {w : ↥K ⧸ CFSG.pCore 2 ↥K} (hw : L15420.quotConj K g hgK = MulAut.conj w)
    {a : ↥K ⧸ CFSG.pCore 2 ↥K} (ha : a ∈ actA K S hS) :
    w * a * w⁻¹ ∈ actA K S hS := by
  obtain ⟨s, hs⟩ := mem_actA_iff.mp ha
  have hgs : g * (s : G) * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hgS s).mp s.2
  refine mem_actA_iff.mpr ⟨⟨g * (s : G) * g⁻¹, hgs⟩, ?_⟩
  have hs' : L15420.quotConj K (s : G) (hS s.2) = MulAut.conj a := hs
  show L15420.quotConj K (g * (s : G) * g⁻¹) (hS hgs) = MulAut.conj (w * a * w⁻¹)
  rw [quotConj_conj_eq hgK (hS s.2) (hS hgs), hw, hs']
  simp only [map_mul, map_inv]

theorem mem_normalizer_actA {K S : Subgroup G} {hS : S ≤ Subgroup.normalizer (K : Set G)} {g : G}
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgS : g ∈ Subgroup.normalizer (S : Set G))
    {w : ↥K ⧸ CFSG.pCore 2 ↥K} (hw : L15420.quotConj K g hgK = MulAut.conj w) :
    w ∈ Subgroup.normalizer
      ((actA K S hS : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) : Set (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => conj_mem_actA hgK hgS hw ha, fun ha => ?_⟩
  have hinv : L15420.quotConj K g⁻¹ (Subgroup.inv_mem _ hgK) = MulAut.conj w⁻¹ := by
    rw [quotConj_inv_eq hgK, hw, map_inv]
  have h := conj_mem_actA (Subgroup.inv_mem _ hgK) (Subgroup.inv_mem _ hgS) hinv ha
  have e : w⁻¹ * (w * a * w⁻¹) * w⁻¹⁻¹ = a := by group
  rwa [e] at h

theorem center_quot_eq_bot [Finite G] {T M L D H K : Subgroup G} {q : ℕ}
    (c : A2Cfg G T M L D H K q) :
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

theorem mem_one_or_self_of_zpowers {Q : Type} [Group Q] {z w : Q} (hord : orderOf z = 2)
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hmod := zpow_mod_orderOf z k
  have h2 : ((orderOf z : ℕ) : ℤ) = 2 := by rw [hord]; norm_num
  rw [h2] at hmod
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with h | h
  · left
    rw [h, zpow_zero] at hmod
    exact hmod.symm
  · right
    rw [h, zpow_one] at hmod
    exact hmod.symm

theorem orderOf_mk_eq_three [Finite G] [Fact (Nat.Prime 2)] [Fact (Nat.Prime 3)] {K : Subgroup G} {x : G}
    (hxK : x ∈ K) (hx3 : orderOf x = 3) :
    orderOf (QuotientGroup.mk (⟨x, hxK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 3 := by
  apply orderOf_eq_prime
  · have hx3' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
    rw [← QuotientGroup.mk_pow, L15420.mk_eq_one_iff]
    show x ^ 3 ∈ pCoreOf 2 K
    rw [hx3']
    exact Subgroup.one_mem _
  · intro h
    rw [L15420.mk_eq_one_iff] at h
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨x, h⟩
    have hxk : x ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one hxk
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega

end KAct

section Main

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.exists_involution
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {x : G} (hxY : x ∈ oTwoUpper H) (hxK : x ∈ K)
    (hx3 : orderOf x = 3) :
    ∃ a ∈ K, a ∉ pCoreOf 2 K ∧ a ^ 2 ∈ pCoreOf 2 K ∧ ⁅x, a⁆ ∈ pCoreOf 2 K ∧
      ∀ r ∈ pCoreOf 2 H, (∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 K) ∨
        (∀ k ∈ K, r * k * r⁻¹ * (a * k * a⁻¹)⁻¹ ∈ pCoreOf 2 K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := c.R_le_normalizer_K h37 h38
  have hRT : pCoreOf 2 H ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf c.sylow_H
  have hTH : T ≤ H := c.sylow_H.1
  have hinj := KAct.conj_injective_of_center_eq_bot (KAct.center_quot_eq_bot c)
  have hRp : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hinnerR : ∀ s : ↥(pCoreOf 2 H), ∃ w : ↥K ⧸ CFSG.pCore 2 ↥K,
      KAct.actHom K (pCoreOf 2 H) hRN s = MulAut.conj w := by
    intro s
    obtain ⟨w, hw⟩ := KAct.quot_eq_conj_of_induces c.inner
      (Subgroup.mem_inf.mpr ⟨hRT s.2, hRN s.2⟩) (hRN s.2)
    exact ⟨w, hw⟩
  set A := KAct.actA K (pCoreOf 2 H) hRN with hAdef
  have hxR : x ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (oTwoUpper_le H hxY)
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hxK
  obtain ⟨xb, hxb⟩ : ∃ y : ↥K ⧸ CFSG.pCore 2 ↥K, y = QuotientGroup.mk (⟨x, hxK⟩ : ↥K) :=
    ⟨_, rfl⟩
  have hxb3 : orderOf xb = 3 := by
    rw [hxb]
    exact KAct.orderOf_mk_eq_three hxK hx3
  have hxq : L15420.quotConj K x hxN = MulAut.conj xb := by
    rw [hxb]
    exact L15420.quotConj_of_mem hxK
  have hxbA : xb ∈ Subgroup.normalizer (A : Set (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    KAct.mem_normalizer_actA hxN hxR hxq
  obtain ⟨g, hgT, hg⟩ := c.exists_inverting_square
  obtain ⟨t₀, ht₀T, ht₀N, -, hKK, hs⟩ := c.kstruct h37 h38
  have hτT : g ^ 2 ∈ T := T.pow_mem hgT 2
  have hτK : g ^ 2 ∈ Subgroup.normalizer (K : Set G) :=
    KAct.sq_mem_normalizer_of_action rfl ht₀N hs ht₀T hgT
  have hτR : g ^ 2 ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hTH hτT)
  obtain ⟨sb, hsb⟩ := KAct.quot_eq_conj_of_induces c.inner
    (Subgroup.mem_inf.mpr ⟨hτT, hτK⟩) hτK
  have hsbA : sb ∈ Subgroup.normalizer (A : Set (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    KAct.mem_normalizer_actA hτK hτR hsb
  have hr₀ : g ^ 2 * x * (g ^ 2)⁻¹ * x ∈ pCoreOf 2 H := hg x hxY
  have hτx : g ^ 2 * x * (g ^ 2)⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hτK hxN) (Subgroup.inv_mem _ hτK)
  have hθ : KAct.actHom K (pCoreOf 2 H) hRN ⟨g ^ 2 * x * (g ^ 2)⁻¹ * x, hr₀⟩ =
      MulAut.conj (sb * xb * sb⁻¹ * xb) := by
    show L15420.quotConj K (g ^ 2 * x * (g ^ 2)⁻¹ * x) (hRN hr₀) = _
    rw [L15420.quotConj_mul hτx hxN, KAct.quotConj_conj_eq hτK hxN hτx, hsb, hxq]
    simp only [map_mul, map_inv]
  have ha₀A : sb * xb * sb⁻¹ * xb ∈ A := KAct.mem_actA_iff.mpr ⟨_, hθ⟩
  have hs' : sb * xb * sb⁻¹ = (sb * xb * sb⁻¹ * xb) * xb⁻¹ := by group
  have hA2 : IsPGroup 2 ↥A := KAct.isPGroup_actA hRp hinj
  have hcard : Nat.card ↥A ≤ 2 :=
    psl_small_two_subgroup q c.q_prime c.q_mod c.model A hA2 xb sb hxb3 hxbA hsbA
      ⟨_, ha₀A, hs'⟩
  have hAne : A ≠ ⊥ := by
    intro hAb
    have hact : ∀ r ∈ pCoreOf 2 H, ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
      intro r hr k hk
      have h1 : L15420.quotConj K r (hRN hr) = 1 :=
        KAct.quotConj_eq_one_of_actA_eq_bot hAb hinnerR hr
      exact (L15420.quotConj_eq_one_iff (hRN hr)).mp h1 k hk
    have hKR : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      KAct.le_normalizer_of_act_trivial (c.pCoreOf_K_le_R h37 h38) hact
    have hKM : K ≤ M := fun k hk => c.normalizer_le_M h5 h7 h9 (hKR hk)
    have ht₀M : t₀ ∈ M := c.nf.hyp.TM ht₀T
    have hK'M : K.map (MulAut.conj t₀).toMonoidHom ≤ M := by
      rintro _ ⟨k, hk, rfl⟩
      exact M.mul_mem (M.mul_mem ht₀M (hKM hk)) (M.inv_mem ht₀M)
    apply c.not_K0_le_M h128 h37 h38 h39
    rw [hKK]
    exact sup_le hKM hK'M
  obtain ⟨zA, hzA⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hAne
  obtain ⟨z, hzmem, hz1⟩ : ∃ z ∈ A, z ≠ 1 := ⟨zA, zA.2, fun h => hzA (Subtype.ext h)⟩
  have hzord : orderOf z ∣ Nat.card ↥A := by
    have := orderOf_dvd_natCard (⟨z, hzmem⟩ : ↥A)
    rwa [Subgroup.orderOf_mk] at this
  have hcardpos : 0 < Nat.card ↥A := Nat.card_pos
  have hord_pos : 0 < orderOf z := (isOfFinOrder_of_finite z).orderOf_pos
  have hord_ne1 : orderOf z ≠ 1 := fun h => hz1 (orderOf_eq_one_iff.mp h)
  have hord2 : orderOf z = 2 := by
    have hle : orderOf z ≤ Nat.card ↥A := Nat.le_of_dvd hcardpos hzord
    omega
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hord2] at h
  have hAz : Subgroup.zpowers z = A := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzmem)
    rw [Nat.card_zpowers, hord2]
    exact hcard
  have hdich : ∀ w ∈ A, w = 1 ∨ w = z := by
    intro w hw
    rw [← hAz] at hw
    exact KAct.mem_one_or_self_of_zpowers hord2 hw
  obtain ⟨a', ha'⟩ := QuotientGroup.mk_surjective z
  have hnot : (a' : G) ∉ pCoreOf 2 K := by
    intro h
    apply hz1
    rw [← ha']
    exact L15420.mk_eq_one_iff.mpr h
  have hsq : (a' : G) ^ 2 ∈ pCoreOf 2 K := by
    have h1 : (QuotientGroup.mk (a' ^ 2) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      rw [QuotientGroup.mk_pow, ha', hz2]
    exact L15420.mk_eq_one_iff.mp h1
  have hxz : xb * z * xb⁻¹ = z := by
    have hmem : xb * z * xb⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxbA z).mp hzmem
    rcases hdich _ hmem with h | h
    · exact absurd (conj_eq_one_iff.mp h) hz1
    · exact h
  have hcomm : ⁅x, (a' : G)⁆ ∈ pCoreOf 2 K := by
    have hk : (QuotientGroup.mk (⟨x, hxK⟩ * a' * (⟨x, hxK⟩ : ↥K)⁻¹ * a'⁻¹ : ↥K) :
        ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← hxb, ha', hxz, mul_inv_cancel]
    have h := L15420.mk_eq_one_iff.mp hk
    rw [commutatorElement_def]
    simpa using h
  refine ⟨(a' : G), a'.2, hnot, hsq, hcomm, ?_⟩
  intro r hr
  obtain ⟨w, hw⟩ := hinnerR ⟨r, hr⟩
  have hwA : w ∈ A := KAct.mem_actA_iff.mpr ⟨⟨r, hr⟩, hw⟩
  have hrN : r ∈ Subgroup.normalizer (K : Set G) := hRN hr
  rcases hdich w hwA with h | h
  · left
    rw [h, map_one] at hw
    have h1 : L15420.quotConj K r hrN = 1 := hw
    exact (L15420.quotConj_eq_one_iff hrN).mp h1
  · right
    intro k hk
    have hzconj : MulAut.conj z = L15420.quotConj K (a' : G) (Subgroup.le_normalizer a'.2) := by
      rw [L15420.quotConj_of_mem a'.2, ← ha']
    rw [h] at hw
    have hq : L15420.quotConj K r hrN =
        L15420.quotConj K (a' : G) (Subgroup.le_normalizer a'.2) :=
      hw.trans hzconj
    have hk1 := congrArg
      (fun φ : MulAut (↥K ⧸ CFSG.pCore 2 ↥K) => φ (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) hq
    simp only [L15420.quotConj_mk] at hk1
    rw [KAct.mk_eq_iff_coe] at hk1
    simp only [L15420.conjRestr_apply_coe] at hk1
    exact KAct.mul_inv_mem_of_inv_mul_mem ((Subgroup.mem_normalizer_iff.mp hrN k).mp hk) hk1

end Main

end CFSG.Quasithin.H13.NFa2
