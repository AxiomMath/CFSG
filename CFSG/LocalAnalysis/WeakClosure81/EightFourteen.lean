module

public import CFSG.LocalAnalysis.WeakClosure81.EightFourteenAux
public import CFSG.LocalAnalysis.WeakClosure81.EightFourteenNat
public import CFSG.LocalAnalysis.WeakClosure81.W15SixC
public import CFSG.SignalizerFunctorTheorem.NonLocal.ModuleOfV
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenCommutator

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.SignalizerFunctorTheorem.Quadratic (LGL fixSub)

variable {G : Type} [Group G] [Finite G]

theorem Sit813.commute_oTwoMod_uGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) (hNV : oTwoMod (cGrp H T) K ≤ centralizer (V : Set G))
    {n u : G} (hn : n ∈ oTwoMod (cGrp H T) K) (hu : u ∈ uGrp V K) : n * u = u * n := by
  have hKN : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le_self).mp h.oTwoMod_normal
  have hle : uGrp V K ≤ centralizer ({n} : Set G) := by
    refine conjClosure_le fun k hk x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hn' : k⁻¹ * n * k ∈ oTwoMod (cGrp H T) K := by
      have := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk)) n).mp hn
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (hNV hn') x hx
    calc n * (k * x * k⁻¹) = k * ((k⁻¹ * n * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * n * k)) * k⁻¹ := by rw [hc]
      _ = (k * x * k⁻¹) * n := by group
  exact Subgroup.mem_centralizer_iff.mp (hle hu) n (Set.mem_singleton n)

theorem Sit813.commute_oTwoMod_u1Grp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G))
    {n u : G} (hn : n ∈ oTwoMod (cGrp H T) K) (hu : u ∈ u1Grp V H T A K) : n * u = u * n := by
  have hKN : K ≤ normalizer (oTwoMod (cGrp H T) K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer oTwoMod_le_self).mp h.oTwoMod_normal
  have hle : u1Grp V H T A K ≤ centralizer ({n} : Set G) := by
    refine conjClosure_le fun k hk x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have hn' : k⁻¹ * n * k ∈ oTwoMod (cGrp H T) K := by
      have := (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hk)) n).mp hn
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp (hNV1 hn') x hx
    calc n * (k * x * k⁻¹) = k * ((k⁻¹ * n * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * n * k)) * k⁻¹ := by rw [hc]
      _ = (k * x * k⁻¹) * n := by group
  exact Subgroup.mem_centralizer_iff.mp (hle hu) n (Set.mem_singleton n)

theorem Sit813.oTwoMod_le_centralizer_u1Grp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)) :
    oTwoMod (cGrp H T) K ≤ centralizer (u1Grp V H T A K : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (h.commute_oTwoMod_u1Grp hNV1 hn hu).symm

theorem Sit813.rGrp_le_centralizer_u1Grp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)) :
    rGrp H T K ≤ centralizer (u1Grp V H T A K : Set G) := by
  intro t ht
  obtain ⟨-, -, htN⟩ := Sit813.mem_rGrp_iff.mp ht
  have htS : t ∈ sGrp H T A K := (le_sup_left : rGrp H T K ≤ sGrp H T A K) ht
  have hle : u1Grp V H T A K ≤ centralizer ({t} : Set G) := by
    refine conjClosure_le fun k hk x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have htx : t * x = x * t :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 t htS
    have hxt : t * x * t⁻¹ = x := by rw [htx]; group
    have hc := h.commute_oTwoMod_u1Grp hNV1 (htN k hk) (mem_conjClosure hk hx)
    have h1 : t * (k * x * k⁻¹) * t⁻¹ = k * x * k⁻¹ := by
      calc t * (k * x * k⁻¹) * t⁻¹
          = (t * k * t⁻¹ * k⁻¹) * (k * (t * x * t⁻¹) * k⁻¹) * (t * k * t⁻¹ * k⁻¹)⁻¹ := by group
        _ = (t * k * t⁻¹ * k⁻¹) * (k * x * k⁻¹) * (t * k * t⁻¹ * k⁻¹)⁻¹ := by rw [hxt]
        _ = k * x * k⁻¹ := by rw [hc]; group
    calc t * (k * x * k⁻¹) = (t * (k * x * k⁻¹) * t⁻¹) * t := by group
      _ = (k * x * k⁻¹) * t := by rw [h1]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) t (Set.mem_singleton t)).symm

@[expose] def W3GapNV1 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {V H T A L K : Subgroup G} {i : ℕ}, Sit813 V H T i A L K →
    oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)

structure W3In814 (G : Type) [Group G] [Finite G] : Prop where
  one : W3Lem122One
  two : W3Lem122Two
  nv1 : W3GapNV1 G

@[instance_reducible]
private noncomputable def commGroupOfComm {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := hc }

@[instance_reducible]
private noncomputable def elemTwoModule {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ 2 = 1) :
    letI := commGroupOfComm hc
    Module (ZMod 2) (Additive A) :=
  letI := commGroupOfComm hc
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp (Additive.toMul x)

private theorem exists_rep_elemAbelian {E : Subgroup G} (hE : IsElemAbelian 2 E) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (ι : G → W) (rep : (Q : Subgroup G) → Q ≤ normalizer (E : Set G) → ↥Q →* LGL 2 W),
      (∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e') ∧
      (∀ w : W, ∃ e ∈ E, ι e = w) ∧
      (∀ e ∈ E, ι e = 0 → e = 1) ∧
      (∀ (Q : Subgroup G) (hQ : Q ≤ normalizer (E : Set G)) (q : ↥Q) (e : G), e ∈ E →
        rep Q hQ q (ι e) = ι ((q : G) * e * (q : G)⁻¹)) := by
  classical
  let hc : ∀ a b : ↥E, a * b = b * a := fun a b => Subtype.ext (hE.comm a.2 b.2)
  let hp : ∀ a : ↥E, a ^ 2 = 1 := fun a => Subtype.ext (by simpa using hE.2 a.1 a.2)
  letI : CommGroup ↥E := commGroupOfComm hc
  letI : Module (ZMod 2) (Additive ↥E) := elemTwoModule hc hp
  let ι : G → Additive ↥E := fun g => if hg : g ∈ E then Additive.ofMul ⟨g, hg⟩ else 0
  have hι_of : ∀ (g : G) (hg : g ∈ E), ι g = Additive.ofMul (⟨g, hg⟩ : ↥E) := fun g hg => dif_pos hg
  let hlin : MulAut ↥E →* LGL 2 (Additive ↥E) :=
    { toFun := fun g =>
        (MulEquiv.toAdditive g).toLinearEquiv (ZMod.map_smul (MulEquiv.toAdditive g))
      map_one' := by ext w; rfl
      map_mul' := fun g h => by ext w; rfl }
  let hrep : ∀ (Q : Subgroup G) (hQ : Q ≤ normalizer (E : Set G)),
      ↥Q →* LGL 2 (Additive ↥E) := fun Q hQ =>
    hlin.comp (CFSG.SignalizerFunctorTheorem.NonLocal.conjHom Q.subtype E
        (fun g v hv => (Subgroup.mem_normalizer_iff.mp (hQ g.2) v).1 hv))
  refine ⟨Additive ↥E, inferInstance, inferInstance, inferInstance, ι, hrep, ?_, ?_, ?_, ?_⟩
  · intro e he e' he'
    rw [hι_of (e * e') (E.mul_mem he he'), hι_of e he, hι_of e' he', ← ofMul_mul]
    rfl
  · intro w
    refine ⟨(Additive.toMul w : ↥E), (Additive.toMul w : ↥E).2, ?_⟩
    rw [hι_of _ (Additive.toMul w : ↥E).2, ofMul_toMul]
  · intro e he h
    have h' : Additive.ofMul (⟨e, he⟩ : ↥E) = 0 := by rw [← hι_of e he]; exact h
    exact congrArg Subtype.val (ofMul_eq_zero.mp h')
  · intro Q hQ q e he
    have hq : (q : G) ∈ normalizer (E : Set G) := hQ q.2
    show (hlin ((CFSG.SignalizerFunctorTheorem.NonLocal.conjHom Q.subtype E
        (fun g v hv => (Subgroup.mem_normalizer_iff.mp (hQ g.2) v).1 hv)) q)) (ι e)
      = ι ((q : G) * e * (q : G)⁻¹)
    rw [hι_of e he, hι_of ((q : G) * e * (q : G)⁻¹)
      ((Subgroup.mem_normalizer_iff.mp hq e).1 he)]
    rfl

private theorem Sit813.v1Grp_ne_bot {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) : v1Grp V H T A K ≠ ⊥ := by
  have hyp := h.minCex.hyp
  have hV : IsElemAbelian 2 V := hyp.hyp7.1
  have hTp : IsPGroup 2 T := hyp.sylow.isPGroup
  have hVT : V ≤ T := le_of_isCalH hV h.calH0.1 hyp.sylow
  have hVbot : V ≠ ⊥ := by
    intro hb
    have h8 := h.card_V_eq_eight
    rw [hb, Subgroup.card_bot] at h8
    omega
  haveI : Group.IsNilpotent ↥T := hTp.isNilpotent
  haveI hnormal : (V.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr h.le_normalizer_T
  have hne : V.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hVbot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVT, hb, Subgroup.map_bot]
  obtain ⟨⟨c, hc⟩, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hcV, hcZ⟩ := Subgroup.mem_inf.mp hc
  have hzV : (c : G) ∈ V := hcV
  have hzC : ∀ y ∈ T, y * (c : G) = (c : G) * y := fun y hy =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨y, hy⟩)
  have hz1 : (c : G) ≠ 1 := fun hc' => hc1 (Subtype.ext (Subtype.ext hc'))
  intro hbot
  have hzS : (c : G) ∈ centralizer (sGrp H T A K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun s hs => hzC s (h.sGrp_le_T hs)
  have hmem : (c : G) ∈ v1Grp V H T A K := Subgroup.mem_inf.mpr ⟨hzV, hzS⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hz1 hmem

private theorem Sit813.cenTMod_mem_rGrp {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) {t : G} (ht : t ∈ cenTMod (cGrp H T) L T) :
    t ∈ rGrp H T K := by
  refine Sit813.mem_rGrp_iff.mpr ⟨ht.1, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    have h1 : t * k * t⁻¹ * k⁻¹ ∈ cGrp H T := ht.2 k (h.concl813.sub_L hk)
    have h2 : (t * k * t⁻¹ * k⁻¹) * k ∈ K := K.mul_mem (h.concl813.ge_C h1) hk
    have h3 : t * k * t⁻¹ = (t * k * t⁻¹ * k⁻¹) * k := by group
    rw [h3]
    exact h2
  · intro k hk
    exact le_oTwoMod_self h.concl813.ge_C h.cGrp_normal (ht.2 k (h.concl813.sub_L hk))

private theorem Sit813.exists_decomp_not_mem_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    ∃ x₀ ∈ A, ∃ k₀ ∈ K, ∃ t ∈ cenTMod (cGrp H T) L T,
      (k₀ * t)⁻¹ * x₀ ∈ cGrp H T ∧ k₀ ∉ oTwoMod (cGrp H T) K := by
  have hb := h.concl813.b_not_le
  push Not at hb
  obtain ⟨x₀, hx₀, hx₀'⟩ := hb
  obtain ⟨k₀, hk₀, t, ht, hc⟩ := h.concl813.a_le x₀ hx₀
  exact ⟨x₀, hx₀, k₀, hk₀, t, ht, hc, fun hk₀N => hx₀' k₀ hk₀N t ht hc⟩

private theorem Sit813.inf_centralizer_u1Grp_eq_oTwoMod {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)) :
    K ⊓ centralizer (u1Grp V H T A K : Set G) = oTwoMod (cGrp H T) K := by
  set E : Subgroup G := u1Grp V H T A K with hEdef
  set D : Subgroup G := K ⊓ centralizer (E : Set G) with hDdef
  have hND : oTwoMod (cGrp H T) K ≤ D :=
    le_inf oTwoMod_le_self (h.oTwoMod_le_centralizer_u1Grp hNV1)
  have hDK : D ≤ K := inf_le_left
  have key : ∀ k ∈ K, ∀ x ∈ centralizer (E : Set G), k * x * k⁻¹ ∈ centralizer (E : Set G) := by
    intro k hk x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro e he
    have h1 : k⁻¹ * e * k ∈ E := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp (Sit813.k_le_normalizer_u1Grp (K.inv_mem hk)) e).1 he
    have h2 := hx (k⁻¹ * e * k) h1
    calc e * (k * x * k⁻¹) = k * ((k⁻¹ * e * k) * x) * k⁻¹ := by group
      _ = k * (x * (k⁻¹ * e * k)) * k⁻¹ := by rw [h2]
      _ = (k * x * k⁻¹) * e := by group
  have hDnorm : (D.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxK, hxC⟩
      exact ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), key k hk x hxC⟩
    · rintro ⟨hxK, hxC⟩
      have hx' : k⁻¹ * (k * x * k⁻¹) * k = x := by group
      refine ⟨?_, ?_⟩
      · rw [← hx']; exact K.mul_mem (K.mul_mem (K.inv_mem hk) hxK) hk
      · rw [← hx']; simpa using key k⁻¹ (K.inv_mem hk) _ hxC
  rcases h.kn1 D hND hDK hDnorm with hDN | hDK'
  · exact hDN
  · exfalso
    have hKcent : K ≤ centralizer (E : Set G) := by
      intro x hx
      have : x ∈ D := by rw [hDK']; exact hx
      exact (Subgroup.mem_inf.mp this).2
    obtain ⟨k₀, hk₀K, hk₀V⟩ := h.exists_mem_K_not_mem_normalizer
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.v1Grp_ne_bot)
    have hvV : (v : G) ∈ V := Sit813.v1Grp_le_V v.2
    have hvE : (v : G) ∈ E := Sit813.v1Grp_le_u1Grp v.2
    have hcomm : k₀ * (v : G) * k₀⁻¹ = (v : G) := by
      have h2 : (v : G) * k₀ = k₀ * (v : G) :=
        Subgroup.mem_centralizer_iff.mp (hKcent hk₀K) (v : G) hvE
      rw [← h2]; group
    have hv1' : (v : G) ≠ 1 := fun hh => hv1 (Subtype.ext hh)
    exact hv1' (h.isTI_form k₀ hk₀V (v : G) hvV (by rw [hcomm]; exact hvV))

private theorem Sit813.centralizer_A_u1Grp_eq_bot {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)) :
    ∀ a ∈ A, (∀ e ∈ u1Grp V H T A K, a * e * a⁻¹ = e) → a = 1 := by
  set E : Subgroup G := u1Grp V H T A K with hEdef
  have hCE : K ⊓ centralizer (E : Set G) = oTwoMod (cGrp H T) K := by
    rw [hEdef]
    exact h.inf_centralizer_u1Grp_eq_oTwoMod hNV1
  obtain ⟨x₀, hx₀A, k₀, hk₀K, t, ht, hcC, hk₀N⟩ := h.exists_decomp_not_mem_oTwoMod
  have htR : t ∈ rGrp H T K := h.cenTMod_mem_rGrp ht
  have hFix : ∀ e ∈ E, x₀ * e * x₀⁻¹ = k₀ * e * k₀⁻¹ := by
    intro e he
    have htE : t ∈ centralizer (E : Set G) := h.rGrp_le_centralizer_u1Grp hNV1 htR
    have hcE : (k₀ * t)⁻¹ * x₀ ∈ centralizer (E : Set G) :=
      (h.oTwoMod_le_centralizer_u1Grp hNV1) (le_oTwoMod_self h.concl813.ge_C h.cGrp_normal hcC)
    have ht' : t * e * t⁻¹ = e := by
      rw [show t * e = e * t from (Subgroup.mem_centralizer_iff.mp htE e he).symm]; group
    have hc' : ((k₀ * t)⁻¹ * x₀) * e * ((k₀ * t)⁻¹ * x₀)⁻¹ = e := by
      rw [show ((k₀ * t)⁻¹ * x₀) * e = e * ((k₀ * t)⁻¹ * x₀) from
        (Subgroup.mem_centralizer_iff.mp hcE e he).symm]
      group
    have hx₀ : x₀ = k₀ * t * ((k₀ * t)⁻¹ * x₀) := by group
    calc x₀ * e * x₀⁻¹
        = k₀ * (t * (((k₀ * t)⁻¹ * x₀) * e * ((k₀ * t)⁻¹ * x₀)⁻¹) * t⁻¹) * k₀⁻¹ := by
          rw [hx₀]; group
      _ = k₀ * (t * e * t⁻¹) * k₀⁻¹ := by rw [hc']
      _ = k₀ * e * k₀⁻¹ := by rw [ht']
  have ha₀ : ∃ a ∈ A, ∃ e ∈ E, a * e * a⁻¹ ≠ e := by
    refine ⟨x₀, hx₀A, ?_⟩
    by_contra hcon
    push Not at hcon
    have hcent : k₀ ∈ centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h1 : k₀ * e * k₀⁻¹ = e := (hFix e he).symm.trans (hcon e he)
      have h2 : k₀ * e = e * k₀ := by
        calc k₀ * e = (k₀ * e * k₀⁻¹) * k₀ := by group
          _ = e * k₀ := by rw [h1]
      exact h2.symm
    exact hk₀N (by rw [← hCE]; exact Subgroup.mem_inf.mpr ⟨hk₀K, hcent⟩)
  intro a ha haE
  by_contra ha1
  obtain ⟨a₀, ha₀A, e₀, he₀E, hne⟩ := ha₀
  have hE_le : E ≤ uGrp V K ⊓ centralizer ({a} : Set G) := by
    refine le_inf Sit813.u1Grp_le_uGrp ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    calc a * e = (a * e * a⁻¹) * a := by group
      _ = e * a := by rw [haE e he]
  have hEq : uGrp V K ⊓ centralizer (A : Set G) = uGrp V K ⊓ centralizer ({a} : Set G) :=
    h.faithful.2 a ha ha1
  have hE_A : E ≤ centralizer (A : Set G) := hE_le.trans (by rw [← hEq]; exact inf_le_right)
  have h1 : a₀ * e₀ = e₀ * a₀ := Subgroup.mem_centralizer_iff.mp (hE_A he₀E) a₀ ha₀A
  exact hne (by rw [h1]; group)

theorem Sit813.exists_klein_setting {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)) :
    ∃ (X : Type) (_ : Group X) (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W)
      (_ : Finite W) (φ : ↥K →* X) (ρ : X →* LGL 2 W) (ι : G → W) (B F : Subgroup X)
      (Z : Submodule (ZMod 2) W),
      CFSG.Quasithin.IsPSL 2 2 2 X ∧ Function.Surjective φ ∧
      (∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoMod (cGrp H T) K) ∧
      (∀ e ∈ u1Grp V H T A K, ∀ e' ∈ u1Grp V H T A K, ι (e * e') = ι e + ι e') ∧
      (∀ w : W, ∃ e ∈ u1Grp V H T A K, ι e = w) ∧
      (∀ e ∈ u1Grp V H T A K, ι e = 0 → e = 1) ∧
      (∀ (k : ↥K) (e : G), e ∈ u1Grp V H T A K → ρ (φ k) (ι e) = ι (k * e * k⁻¹)) ∧
      (∀ w : W, w ∈ Z ↔ ∃ e ∈ v1Grp V H T A K, ι e = w) ∧
      B.index = 5 ∧ (∀ g : X, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z) ∧
      IsElemAbelian 2 F ∧ Nat.card F = 4 ∧ F ≤ B ∧ RepQuad ρ F ∧
      (∀ f ∈ F, ∀ z ∈ Z, ρ f z = z) := by
  classical
  obtain ⟨X, hXg, φ, hφ, hker, hXl2⟩ := h.concl813.c_shape
  letI : Group X := hXg
  have hXpsl : IsPSL 2 2 2 X := isL2_iff_isPSL.mp hXl2
  set E : Subgroup G := u1Grp V H T A K with hEdef
  set V1 : Subgroup G := v1Grp V H T A K with hV1def
  set P : Subgroup G := K ⊓ normalizer (V : Set G) with hPdef
  have hV1E : V1 ≤ E := by rw [hV1def, hEdef]; exact Sit813.v1Grp_le_u1Grp
  have hV1V : V1 ≤ V := by rw [hV1def]; exact Sit813.v1Grp_le_V
  have hEel : IsElemAbelian 2 E := by
    rw [hEdef]; exact h.isElemAbelian_uGrp.mono Sit813.u1Grp_le_uGrp
  obtain ⟨W, hWadd, hWmod, hWfin, ι, rep, hadd, hsurj, hinj, hρι⟩ := exists_rep_elemAbelian hEel
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  have hι_one : ι 1 = 0 := by
    have h1 := hadd 1 E.one_mem 1 E.one_mem
    rw [mul_one] at h1
    exact add_left_cancel (show ι 1 + ι 1 = ι 1 + 0 by rw [← h1, add_zero])
  have hι_inv : ∀ e ∈ E, ι e⁻¹ = -ι e := by
    intro e he
    have h1 := hadd e he e⁻¹ (E.inv_mem he)
    rw [mul_inv_cancel, hι_one] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  have hι_eq : ∀ a ∈ E, ∀ b ∈ E, ι a = ι b → a = b := by
    intro a ha b hb hab
    refine mul_inv_eq_one.mp (hinj _ (E.mul_mem ha (E.inv_mem hb)) ?_)
    rw [hadd _ ha _ (E.inv_mem hb), hab, hι_inv b hb, add_neg_cancel]
  let ρK : ↥K →* LGL 2 W := rep K Sit813.k_le_normalizer_u1Grp
  have hρK_fix : ∀ k : ↥K, (k : G) ∈ oTwoMod (cGrp H T) K → ρK k = 1 := by
    intro k hkN
    ext w
    obtain ⟨e, he, rfl⟩ := hsurj w
    change rep K Sit813.k_le_normalizer_u1Grp k (ι e) = (1 : LGL 2 W) (ι e)
    rw [hρι K Sit813.k_le_normalizer_u1Grp k e he]
    have h2 : (k : G) * e * (k : G)⁻¹ = e := by
      have hc := Subgroup.mem_centralizer_iff.mp (h.oTwoMod_le_centralizer_u1Grp hNV1 hkN) e he
      rw [← hc]; group
    rw [h2]
    rfl
  have hρK_ker : ∀ k : ↥K, ρK k = 1 → (k : G) ∈ oTwoMod (cGrp H T) K := by
    intro k hk
    rw [← h.inf_centralizer_u1Grp_eq_oTwoMod hNV1]
    refine Subgroup.mem_inf.mpr ⟨k.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hconj : (k : G) * e * (k : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (Sit813.k_le_normalizer_u1Grp k.2) e).1 he
    have h2 : ρK k (ι e) = ι ((k : G) * e * (k : G)⁻¹) :=
      hρι K Sit813.k_le_normalizer_u1Grp k e he
    have h1 : ρK k (ι e) = ι e := by rw [hk]; rfl
    have h3 : (k : G) * e * (k : G)⁻¹ = e := hι_eq _ hconj _ he (by rw [← h2, h1])
    calc e * (k : G) = ((k : G) * e * (k : G)⁻¹) * (k : G) := by rw [h3]
      _ = (k : G) * e := by group
  have hker_le : φ.ker ≤ ρK.ker := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk ⊢
    exact hρK_fix k ((hker k).mp hk)
  let ρ : X →* LGL 2 W := (MonoidHom.liftOfSurjective φ hφ) ⟨ρK, hker_le⟩
  have hρ : ∀ k : ↥K, ρ (φ k) = ρK k := by
    intro k
    change (MonoidHom.liftOfRightInverse (f := φ) (Function.surjInv hφ)
      (Function.rightInverse_surjInv hφ)) ⟨ρK, hker_le⟩ (φ k) = ρK k
    exact MonoidHom.liftOfRightInverse_comp_apply φ (Function.surjInv hφ)
      (Function.rightInverse_surjInv hφ) ⟨ρK, hker_le⟩ k
  have hρι' : ∀ (k : ↥K) (e : G), e ∈ E → ρ (φ k) (ι e) = ι ((k : G) * e * (k : G)⁻¹) :=
    fun k e he => by rw [hρ k]; exact hρι K Sit813.k_le_normalizer_u1Grp k e he
  have hρ_inj : Function.Injective ρ := by
    intro x y hxy
    obtain ⟨kx, rfl⟩ := hφ x
    obtain ⟨ky, rfl⟩ := hφ y
    have hkxy : ρK kx = ρK ky := by rw [← hρ kx, ← hρ ky]; exact hxy
    have hk : ρK (kx⁻¹ * ky) = 1 := by rw [map_mul, map_inv, hkxy, inv_mul_cancel]
    have hN : ((kx⁻¹ * ky : ↥K) : G) ∈ oTwoMod (cGrp H T) K := hρK_ker (kx⁻¹ * ky) hk
    have hφ1 : φ (kx⁻¹ * ky) = 1 := (hker (kx⁻¹ * ky)).mpr hN
    have hxy' : φ kx = φ ky := by
      have h := hφ1
      rw [map_mul, map_inv] at h
      exact inv_mul_eq_one.mp h
    rw [hxy']
  let ρA : ↥A →* LGL 2 W :=
    rep A (fun a ha => h.sGrp_le_normalizer_u1Grp (Sit813.a_le_sGrp ha))
  have hρA_norm : A ≤ normalizer (E : Set G) :=
    fun a ha => h.sGrp_le_normalizer_u1Grp (Sit813.a_le_sGrp ha)
  have hρA_apply : ∀ (a : ↥A) (e : G), e ∈ E →
      ρA a (ι e) = ι ((a : G) * e * (a : G)⁻¹) := fun a e he => hρι A hρA_norm a e he
  have hρA_inj : Function.Injective ρA := by
    intro a b hab
    have h1 : ρA (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have hfix : ∀ e ∈ E, (((a⁻¹ * b : ↥A) : G)) * e * (((a⁻¹ * b : ↥A) : G))⁻¹ = e := by
      intro e he
      have hconj : (((a⁻¹ * b : ↥A) : G)) * e * (((a⁻¹ * b : ↥A) : G))⁻¹ ∈ E := by
        have hmem : ((a⁻¹ * b : ↥A) : G) ∈ A := (a⁻¹ * b).2
        exact (Subgroup.mem_normalizer_iff.mp
          (h.sGrp_le_normalizer_u1Grp (Sit813.a_le_sGrp hmem)) e).1 he
      have h2 : ρA (a⁻¹ * b) (ι e) =
          ι ((((a⁻¹ * b : ↥A) : G)) * e * (((a⁻¹ * b : ↥A) : G))⁻¹) :=
        hρA_apply (a⁻¹ * b) e he
      exact hι_eq _ hconj _ he (by rw [← h2, h1]; rfl)
    have h4 := h.centralizer_A_u1Grp_eq_bot hNV1 ((a⁻¹ * b : ↥A) : G) (a⁻¹ * b).2 hfix
    exact inv_mul_eq_one.mp (Subtype.ext h4)
  let Z : Submodule (ZMod 2) W :=
    { carrier := {w | ∃ e ∈ V1, ι e = w}
      zero_mem' := ⟨1, V1.one_mem, hι_one⟩
      add_mem' := by
        rintro x y ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
        exact ⟨e * e', V1.mul_mem he he', hadd e (hV1E he) e' (hV1E he')⟩
      smul_mem' := by
        rintro c x ⟨e, he, rfl⟩
        have hlt : c.val < 2 := ZMod.val_lt c
        have hc : c = 0 ∨ c = 1 := by
          have h2 : c.val = 0 ∨ c.val = 1 := by omega
          rcases h2 with h2 | h2
          · left; rw [← ZMod.natCast_zmod_val c, h2]; norm_num
          · right; rw [← ZMod.natCast_zmod_val c, h2]; norm_num
        rcases hc with rfl | rfl
        · exact ⟨1, V1.one_mem, by rw [zero_smul, hι_one]⟩
        · exact ⟨e, he, by rw [one_smul]⟩ }
  have hZmem : ∀ w : W, w ∈ Z ↔ ∃ e ∈ V1, ι e = w := fun _ => Iff.rfl
  let B : Subgroup X := (P.subgroupOf K).map φ
  have hker_le_P : φ.ker ≤ P.subgroupOf K := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    rw [Subgroup.mem_subgroupOf]
    exact h.oTwoMod_le_inf ((hker k).mp hk)
  have hBi : B.index = 5 := by
    rw [Subgroup.index_map_eq (P.subgroupOf K) hφ hker_le_P]
    exact h.concl813.d_index
  have hρA_le : ρA.range ≤ ρ.range := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨k, hkP, t, htR, haeq⟩ := h.exists_decomp a.2
    have ha' : a = ⟨k * t, by rw [← haeq]; exact a.2⟩ := Subtype.ext haeq
    refine ⟨φ ⟨k, hkP.1⟩, ?_⟩
    rw [ha', hρ ⟨k, hkP.1⟩]
    apply LinearEquiv.ext
    intro w
    obtain ⟨e, he, rfl⟩ := hsurj w
    rw [hρA_apply ⟨k * t, _⟩ e he, hρι K Sit813.k_le_normalizer_u1Grp ⟨k, hkP.1⟩ e he]
    congr 1
    have htE : t ∈ centralizer (E : Set G) := h.rGrp_le_centralizer_u1Grp hNV1 htR
    have hte : t * e * t⁻¹ = e := by
      rw [show t * e = e * t from (Subgroup.mem_centralizer_iff.mp htE e he).symm]; group
    rw [show ((k : G) * t) * e * ((k : G) * t)⁻¹ =
      (k : G) * (t * e * t⁻¹) * (k : G)⁻¹ from by group, hte]
  let F : Subgroup X := (ρA.range).comap ρ
  have hmap : F.map ρ = ρA.range := Subgroup.map_comap_eq_self hρA_le
  have hFB : F ≤ B := by
    intro x hx
    obtain ⟨⟨k, hkK⟩, hxφ⟩ := hφ x
    obtain ⟨a, ha⟩ := Subgroup.mem_comap.mp hx
    obtain ⟨k₁, hk₁P, t, htR, haeq⟩ := h.exists_decomp a.2
    have hρAa : ρA a = ρ (φ ⟨k₁, hk₁P.1⟩) := by
      have ha' : a = ⟨k₁ * t, by rw [← haeq]; exact a.2⟩ := Subtype.ext haeq
      rw [ha', hρ ⟨k₁, hk₁P.1⟩]
      apply LinearEquiv.ext
      intro w
      obtain ⟨e, he, rfl⟩ := hsurj w
      rw [hρA_apply ⟨k₁ * t, _⟩ e he, hρι K Sit813.k_le_normalizer_u1Grp ⟨k₁, hk₁P.1⟩ e he]
      congr 1
      have htE : t ∈ centralizer (E : Set G) := h.rGrp_le_centralizer_u1Grp hNV1 htR
      have hte : t * e * t⁻¹ = e := by
        rw [show t * e = e * t from (Subgroup.mem_centralizer_iff.mp htE e he).symm]; group
      rw [show ((k₁ : G) * t) * e * ((k₁ : G) * t)⁻¹ =
        (k₁ : G) * (t * e * t⁻¹) * (k₁ : G)⁻¹ from by group, hte]
    have hx_eq : x = φ ⟨k₁, hk₁P.1⟩ := hρ_inj (by rw [ha.symm, hρAa])
    rw [hx_eq]
    exact Subgroup.mem_map.mpr ⟨⟨k₁, hk₁P.1⟩, by rw [Subgroup.mem_subgroupOf]; exact hk₁P, rfl⟩
  have hcardF : Nat.card ↥F = 4 := by
    have h1 : Nat.card ↥F = Nat.card ↥(F.map ρ) :=
      Nat.card_congr (Subgroup.equivMapOfInjective F ρ hρ_inj).toEquiv
    rw [h1, hmap]
    have h2 : Nat.card ↥(ρA.range) = Nat.card ↥A := by
      have := Nat.card_congr (Subgroup.equivMapOfInjective (⊤ : Subgroup ↥A) ρA hρA_inj).toEquiv
      simpa using this.symm
    rw [h2]
    exact h.card_A_eq_four
  have hFel : IsElemAbelian 2 F := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro x y
      apply Subtype.ext
      apply hρ_inj
      have hx' : ρ (x : X) ∈ ρA.range := x.2
      have hy' : ρ (y : X) ∈ ρA.range := y.2
      obtain ⟨a, ha⟩ := hx'
      obtain ⟨a', ha'⟩ := hy'
      calc ρ ((x : X) * (y : X)) = ρ (x : X) * ρ (y : X) := map_mul ρ _ _
        _ = ρA a * ρA a' := by rw [← ha, ← ha']
        _ = ρA (a * a') := (map_mul ρA a a').symm
        _ = ρA (a' * a) := by
          rw [show a * a' = a' * a from Subtype.ext (h.isElemAbelian_A.comm a.2 a'.2)]
        _ = ρA a' * ρA a := map_mul ρA a' a
        _ = ρ (y : X) * ρ (x : X) := by rw [ha', ha]
        _ = ρ ((y : X) * (x : X)) := (map_mul ρ _ _).symm
    · intro x hx
      have hx' : ρ (x : X) ∈ ρA.range := hx
      obtain ⟨a, ha⟩ := hx'
      refine hρ_inj ?_
      have h1 : ρ ((x : X) ^ 2) = 1 := by
        rw [map_pow, ← ha, ← map_pow]
        rw [show (a : ↥A) ^ 2 = 1 from by
          rw [pow_two]; exact Subtype.ext (h.isElemAbelian_A.mul_self_eq_one a.2), map_one]
      rw [h1, map_one]
  have hFnorm : (F.subgroupOf B).Normal :=
    (isPSL_two_two_two_klein hXpsl hBi hFel hcardF hFB).2.1
  have hFZ : ∀ f ∈ F, ∀ z ∈ Z, ρ f z = z := by
    intro f hf z hz
    obtain ⟨a, ha⟩ := hf
    obtain ⟨v, hv1, rfl⟩ := (hZmem z).mp hz
    rw [← ha, hρA_apply a v (hV1E hv1)]
    have hvS : v ∈ centralizer (sGrp H T A K : Set G) := (Subgroup.mem_inf.mp hv1).2
    have haS : (a : G) ∈ sGrp H T A K := Sit813.a_le_sGrp a.2
    have hac := Subgroup.mem_centralizer_iff.mp hvS (a : G) haS
    rw [show (a : G) * v * (a : G)⁻¹ = v from by rw [hac]; group]
  have hquad : RepQuad ρ F := by
    have hquad_pt : ∀ (a a' : ↥A) (v : W), ρA a' (ρA a v - v) = ρA a v - v := by
      have hmain : ∀ (a a' : ↥A) (e : G), e ∈ E →
          ρA a' (ρA a (ι e) - ι e) = ρA a (ι e) - ι e := by
        intro a a' e he
        have ha2 : (a : G) * (a : G) = 1 := h.isElemAbelian_A.mul_self_eq_one a.2
        have hai : (a : G)⁻¹ = (a : G) := inv_eq_of_mul_eq_one_right ha2
        set c : G := ((a : G) * e * (a : G)) * e⁻¹ with hc
        have hconj : (a : G) * e * (a : G) ∈ E := by
          simpa [hai] using
            (Subgroup.mem_normalizer_iff.mp
              (h.sGrp_le_normalizer_u1Grp (Sit813.a_le_sGrp a.2)) e).1 he
        have hcE : c ∈ E := by rw [hc]; exact E.mul_mem hconj (E.inv_mem he)
        have hcU : c ∈ uGrp V K := Sit813.u1Grp_le_uGrp (hEdef ▸ hcE)
        have hcA : (a' : G) * c * (a' : G)⁻¹ = c := by
          by_cases ha1 : (a : G) = 1
          · simp [hc, ha1]
          · have hcCen : c ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
              rw [Subgroup.mem_centralizer_iff]
              intro x hx
              rw [Set.mem_singleton_iff] at hx
              subst hx
              have hc2 : c * c = 1 := h.isElemAbelian_uGrp.mul_self_eq_one hcU
              have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
              have haca : (a : G) * c = c * (a : G) := by
                have h1 : (a : G) * c * (a : G)⁻¹ = c := by
                  have h2 : (a : G) * c * (a : G)⁻¹ = c⁻¹ := by
                    rw [hc, hai]
                    rw [show (((a : G) * e * (a : G)) * e⁻¹)⁻¹ =
                      e * (a : G) * e⁻¹ * (a : G) from by
                        simp only [mul_inv_rev, inv_inv, hai]
                        group]
                    conv_lhs => rw [show (a : G) * ((a : G) * e * (a : G) * e⁻¹) * (a : G) =
                      ((a : G) * (a : G)) * e * ((a : G) * e⁻¹ * (a : G)) from by group]
                    rw [ha2, one_mul]
                    rw [show e * ((a : G) * e⁻¹ * (a : G)) =
                      e * (a : G) * e⁻¹ * (a : G) from by group]
                  rw [h2, hci]
                calc (a : G) * c = ((a : G) * c * (a : G)⁻¹) * (a : G) := by group
                  _ = c * (a : G) := by rw [h1]
              exact haca
            have hcc : c ∈ Subgroup.centralizer (A : Set G) := by
              have hEq := h.faithful.2 a a.2 ha1
              have hmem : c ∈ uGrp V K ⊓ Subgroup.centralizer ({(a : G)} : Set G) :=
                Subgroup.mem_inf.mpr ⟨hcU, hcCen⟩
              rw [← hEq] at hmem
              exact (Subgroup.mem_inf.mp hmem).2
            have h1 := Subgroup.mem_centralizer_iff.mp hcc (a' : G) a'.2
            rw [h1]; group
        have h1 : ρA a (ι e) - ι e = ι c := by
          rw [hρA_apply a e he, hc, hadd _ hconj _ (E.inv_mem he), hι_inv e he]
          rw [hai]
          exact sub_eq_add_neg _ _
        rw [h1, hρA_apply a' c hcE, hcA]
      intro a a' v
      obtain ⟨e, he, rfl⟩ := hsurj v
      exact hmain a a' e he
    change CFSG.Quasithin.G11.commSpace (F.map ρ)
      (CFSG.SignalizerFunctorTheorem.Quadratic.commSub (F.map ρ)) = ⊥
    rw [hmap, eq_bot_iff, CFSG.Quasithin.G11.commSpace_le_iff]
    intro b hb u hu
    rw [Submodule.mem_bot]
    have hfix : ∀ b' ∈ ρA.range, b' u = u := by
      intro b' hb'
      obtain ⟨a', rfl⟩ := hb'
      refine Submodule.span_induction (p := fun u _ => ρA a' u = u) ?_ ?_ ?_ ?_ hu
      · rintro w ⟨b'', hb'', v, rfl⟩
        obtain ⟨a'', ha''⟩ := hb''
        rw [← ha'']
        exact hquad_pt a'' a' v
      · rw [map_zero]
      · intro x y hxmem hymem hx hy; rw [map_add, hx, hy]
      · intro c x hxmem hx; rw [map_smul, hx]
    rw [hfix b hb, sub_self]
  have hstab : ∀ g : X, g ∈ B ↔ ∀ z ∈ Z, ρ g z ∈ Z := by
    have hstar : ∀ t ∈ rGrp H T K, ∀ k ∈ K, ∀ x ∈ V1,
        t * (k * x * k⁻¹) * t⁻¹ = k * (t * x * t⁻¹) * k⁻¹ := by
      intro t ht k hk x hx
      obtain ⟨-, -, htN⟩ := Sit813.mem_rGrp_iff.mp ht
      have htS : t ∈ sGrp H T A K := (le_sup_left : rGrp H T K ≤ sGrp H T A K) ht
      have hxt : t * x * t⁻¹ = x := by
        rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 t htS]; group
      have hu : k * (t * x * t⁻¹) * k⁻¹ ∈ u1Grp V H T A K := by
        rw [hxt]; exact mem_conjClosure hk hx
      have hc := h.commute_oTwoMod_u1Grp hNV1 (htN k hk) hu
      calc t * (k * x * k⁻¹) * t⁻¹
          = (t * k * t⁻¹ * k⁻¹) * (k * (t * x * t⁻¹) * k⁻¹) *
              (t * k * t⁻¹ * k⁻¹)⁻¹ := by group
        _ = k * (t * x * t⁻¹) * k⁻¹ := by rw [hc]; group
    intro g
    constructor
    · intro hg z hz
      obtain ⟨kk, hkkP, hgφ⟩ := Subgroup.mem_map.mp hg
      have hkkK : (kk : G) ∈ K := (Subgroup.mem_subgroupOf.mp hkkP).1
      have hkkM : (kk : G) ∈ normalizer (V : Set G) := (Subgroup.mem_subgroupOf.mp hkkP).2
      obtain ⟨v, hv1, rfl⟩ := (hZmem z).mp hz
      rw [← hgφ, hρι' kk v (hV1E hv1)]
      have hvV : v ∈ V := hV1V hv1
      have hwV : (kk : G) * v * (kk : G)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hkkM v).1 hvV
      refine (hZmem _).mpr ⟨(kk : G) * v * (kk : G)⁻¹, ?_, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hwV, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hR : rGrp H T K ≤ Subgroup.centralizer ({(kk : G) * v * (kk : G)⁻¹} : Set G) := by
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have h2 : t * v * t⁻¹ = v := by
          have htS : t ∈ sGrp H T A K := (le_sup_left : rGrp H T K ≤ sGrp H T A K) ht
          have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv1).2 t htS
          rw [hcomm]; group
        have h1 := hstar t ht (kk : G) hkkK v hv1
        rw [h2] at h1
        calc ((kk : G) * v * (kk : G)⁻¹) * t =
            (t * ((kk : G) * v * (kk : G)⁻¹) * t⁻¹) * t := by rw [h1]
          _ = t * ((kk : G) * v * (kk : G)⁻¹) := by group
      have hA : A ≤ Subgroup.centralizer ({(kk : G) * v * (kk : G)⁻¹} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        obtain ⟨k₁, hk₁P, t, htR, haeq⟩ := h.exists_decomp ha
        have htw : t * ((kk : G) * v * (kk : G)⁻¹) * t⁻¹ = (kk : G) * v * (kk : G)⁻¹ := by
          have h2 : t * v * t⁻¹ = v := by
            have htS : t ∈ sGrp H T A K := (le_sup_left : rGrp H T K ≤ sGrp H T A K) htR
            have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv1).2 t htS
            rw [hcomm]; group
          have h1 := hstar t htR (kk : G) hkkK v hv1
          rw [h2] at h1; exact h1
        have haw : a * ((kk : G) * v * (kk : G)⁻¹) * a⁻¹ =
            (k₁ : G) * ((kk : G) * v * (kk : G)⁻¹) * (k₁ : G)⁻¹ := by
          rw [haeq]
          calc (k₁ * t) * ((kk : G) * v * (kk : G)⁻¹) * (k₁ * t)⁻¹
              = k₁ * (t * ((kk : G) * v * (kk : G)⁻¹) * t⁻¹) * k₁⁻¹ := by group
            _ = k₁ * ((kk : G) * v * (kk : G)⁻¹) * k₁⁻¹ := by rw [htw]
        have hx₁F : φ ⟨(k₁ : G), hk₁P.1⟩ ∈ F := by
          rw [show F = (ρA.range).comap ρ from rfl, Subgroup.mem_comap, hρ ⟨(k₁ : G), hk₁P.1⟩]
          refine ⟨⟨a, ha⟩, ?_⟩
          have ha' : (⟨a, ha⟩ : ↥A) = ⟨(k₁ : G) * t, by rw [← haeq]; exact ha⟩ :=
            Subtype.ext haeq
          rw [ha']
          apply LinearEquiv.ext
          intro w
          obtain ⟨e, he, rfl⟩ := hsurj w
          rw [hρA_apply ⟨(k₁ : G) * t, _⟩ e he,
            hρι K Sit813.k_le_normalizer_u1Grp ⟨(k₁ : G), hk₁P.1⟩ e he]
          congr 1
          have htE : t ∈ centralizer (E : Set G) := h.rGrp_le_centralizer_u1Grp hNV1 htR
          have hte : t * e * t⁻¹ = e := by
            rw [show t * e = e * t from (Subgroup.mem_centralizer_iff.mp htE e he).symm]; group
          rw [show (((k₁ : G) * t) * e * ((k₁ : G) * t)⁻¹) =
            (k₁ : G) * (t * e * t⁻¹) * (k₁ : G)⁻¹ from by group, hte]
        have hkkB : φ kk ∈ B :=
          Subgroup.mem_map.mpr ⟨kk, by simpa [Subgroup.mem_subgroupOf] using hkkP, rfl⟩
        have hx₂F : (φ kk)⁻¹ * φ ⟨(k₁ : G), hk₁P.1⟩ * φ kk ∈ F := by
          have h1 := hFnorm.conj_mem (⟨φ ⟨(k₁ : G), hk₁P.1⟩, hFB hx₁F⟩ : ↥B)
            (Subgroup.mem_subgroupOf.mpr hx₁F) (⟨(φ kk)⁻¹, B.inv_mem hkkB⟩ : ↥B)
          simpa using Subgroup.mem_subgroupOf.mp h1
        have hx₂r : ρ ((φ kk)⁻¹ * φ ⟨(k₁ : G), hk₁P.1⟩ * φ kk) ∈ ρA.range :=
          Subgroup.mem_comap.mp hx₂F
        obtain ⟨a', ha'⟩ := hx₂r
        set k₂ : ↥K := kk⁻¹ * ⟨(k₁ : G), hk₁P.1⟩ * kk with hk₂
        have hx₂' : (φ kk)⁻¹ * φ ⟨(k₁ : G), hk₁P.1⟩ * φ kk = φ k₂ := by
          rw [hk₂, map_mul, map_mul, map_inv]
        have hfix : (k₂ : G) * v * (k₂ : G)⁻¹ = v := by
          have hconj₂ : (k₂ : G) * v * (k₂ : G)⁻¹ ∈ E :=
            (Subgroup.mem_normalizer_iff.mp (Sit813.k_le_normalizer_u1Grp k₂.2) v).1 (hV1E hv1)
          refine hι_eq _ hconj₂ _ (hV1E hv1) ?_
          have hρ₂ : ρ (φ k₂) (ι v) = ι ((k₂ : G) * v * (k₂ : G)⁻¹) := hρι' k₂ v (hV1E hv1)
          have hρv : ρ (φ k₂) (ι v) = ι v := by
            rw [← hx₂', ← ha']
            rw [hρA_apply a' v (hV1E hv1)]
            have hvS : v ∈ centralizer (sGrp H T A K : Set G) := (Subgroup.mem_inf.mp hv1).2
            have ha'S : (a' : G) ∈ sGrp H T A K := Sit813.a_le_sGrp a'.2
            have hcomm := Subgroup.mem_centralizer_iff.mp hvS (a' : G) ha'S
            rw [show (a' : G) * v * (a' : G)⁻¹ = v from by rw [hcomm]; group]
          rw [← hρ₂, hρv]
        have hk₁w : (k₁ : G) * ((kk : G) * v * (kk : G)⁻¹) * (k₁ : G)⁻¹ =
            (kk : G) * v * (kk : G)⁻¹ := by
          calc (k₁ : G) * ((kk : G) * v * (kk : G)⁻¹) * (k₁ : G)⁻¹
              = (kk : G) * ((k₂ : G) * v * (k₂ : G)⁻¹) * (kk : G)⁻¹ := by
                rw [hk₂]
                simp only [Subgroup.coe_mul, Subgroup.coe_inv]
                group
            _ = (kk : G) * v * (kk : G)⁻¹ := by rw [hfix]
        have h1 : a * ((kk : G) * v * (kk : G)⁻¹) * a⁻¹ = (kk : G) * v * (kk : G)⁻¹ :=
          haw.trans hk₁w
        calc ((kk : G) * v * (kk : G)⁻¹) * a =
            (a * ((kk : G) * v * (kk : G)⁻¹) * a⁻¹) * a := by rw [h1]
          _ = a * ((kk : G) * v * (kk : G)⁻¹) := by group
      have hle := sup_le hR hA
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (hle (show s ∈ rGrp H T K ⊔ A from hs)) ((kk : G) * v * (kk : G)⁻¹)
        (Set.mem_singleton _)
      exact hcomm.symm
    · intro hstab_g
      obtain ⟨k, rfl⟩ := hφ g
      refine Subgroup.mem_map.mpr ⟨k, ?_, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      refine ⟨k.2, ?_⟩
      by_contra hkV
      obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.v1Grp_ne_bot)
      have hvV : (v : G) ∈ V := Sit813.v1Grp_le_V v.2
      have hvE : (v : G) ∈ E := hV1E v.2
      have hzv : ι (v : G) ∈ Z := (hZmem _).mpr ⟨(v : G), v.2, rfl⟩
      have h1 : ρ (φ k) (ι (v : G)) ∈ Z := hstab_g _ hzv
      rw [hρι' k (v : G) hvE] at h1
      obtain ⟨e', he'V1, he'⟩ := (hZmem _).mp h1
      have hconj : (k : G) * (v : G) * (k : G)⁻¹ ∈ E :=
        (Subgroup.mem_normalizer_iff.mp (Sit813.k_le_normalizer_u1Grp k.2) (v : G)).1 hvE
      have heq : (k : G) * (v : G) * (k : G)⁻¹ = e' :=
        hι_eq _ hconj _ (hV1E he'V1) he'.symm
      have hmem : (k : G) * (v : G) * (k : G)⁻¹ ∈ V := by
        rw [heq]; exact Sit813.v1Grp_le_V he'V1
      exact (fun hv1' => hv1 (Subtype.ext hv1')) (h.isTI_form (k : G) hkV (v : G) hvV hmem)
  exact ⟨X, hXg, W, hWadd, hWmod, hWfin, φ, ρ, ι, B, F, Z, hXpsl, hφ, hker, hadd, hsurj,
    hinj, hρι', hZmem, hBi, hstab, hFel, hcardF, hFB, hquad, hFZ⟩

theorem Sit813.eight_fourteen_of_nv (h122one : W3Lem122One) (h122two : W3Lem122Two)
    {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K)
    (hNV1 : oTwoMod (cGrp H T) K ≤ centralizer (v1Grp V H T A K : Set G)) :
    IsNaturalSL2Module K (u1Grp V H T A K) (u1Grp V H T A K ⊓ centralizer (K : Set G)) ∧
      IsElemAbelian 2 (v1Grp V H T A K) ∧ Nat.card (v1Grp V H T A K) = 4 := by
  classical
  obtain ⟨X, hXg, W, hWadd, hWmod, hWfin, φ, ρ, ι, B, F, Z,
    hXpsl, hφ, hker, hadd, hsurj, hinj, hρι, hZmem, hBi, hstab, hFel, hFcard, hFB, hquad,
    hFZ⟩ := h.exists_klein_setting hNV1
  letI : Group X := hXg
  letI : AddCommGroup W := hWadd
  letI : Module (ZMod 2) W := hWmod
  letI : Finite W := hWfin
  set E : Subgroup G := u1Grp V H T A K with hEdef
  have hEhe : ∀ e ∈ E, e ∈ u1Grp V H T A K := fun _ he => hEdef ▸ he
  have hEuh : ∀ e ∈ u1Grp V H T A K, e ∈ E := fun _ he => hEdef ▸ he
  have hadd' : ∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e' := fun e he e' he' =>
    hadd e (hEuh e he) e' (hEuh e' he')
  have hsurj' : ∀ w : W, ∃ e ∈ E, ι e = w := fun w => by
    obtain ⟨e, he, hw⟩ := hsurj w; exact ⟨e, hEuh e he, hw⟩
  have hinj' : ∀ e ∈ E, ι e = 0 → e = 1 := fun e he h => hinj e (hEuh e he) h
  have hρι' : ∀ (k : ↥K) (e : G), e ∈ E → ρ (φ k) (ι e) = ι ((k : G) * e * (k : G)⁻¹) :=
    fun k e he => hρι k e (hEuh e he)
  have hι_one : ι 1 = 0 := by
    have h1 := hadd' 1 E.one_mem 1 E.one_mem
    rw [mul_one] at h1
    exact add_left_cancel (show ι 1 + ι 1 = ι 1 + 0 by rw [← h1, add_zero])
  have hι_inv : ∀ e ∈ E, ι e⁻¹ = -ι e := by
    intro e he
    have h1 := hadd' e he e⁻¹ (E.inv_mem he)
    rw [mul_inv_cancel, hι_one] at h1
    exact eq_neg_of_add_eq_zero_right h1.symm
  have hV1el : IsElemAbelian 2 (v1Grp V H T A K) :=
    h.minCex.hyp.hyp7.1.mono Sit813.v1Grp_le_V
  let f : ↥(v1Grp V H T A K) → ↥Z := fun e => ⟨ι e, (hZmem (ι e)).mpr ⟨e, e.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e e' h'
      have h2 : ι (e : G) = ι (e' : G) := congrArg Subtype.val h'
      have he : (e : G) ∈ E := hEuh (e : G) (Sit813.v1Grp_le_u1Grp e.2)
      have he' : (e' : G) ∈ E := hEuh (e' : G) (Sit813.v1Grp_le_u1Grp e'.2)
      have h3 : (e : G) * (e' : G)⁻¹ = 1 :=
        hinj' _ (E.mul_mem he (E.inv_mem he')) (by
          rw [hadd' _ he _ (E.inv_mem he'), h2, hι_inv (e' : G) he', add_neg_cancel])
      exact Subtype.ext (mul_inv_eq_one.mp h3)
    · rintro ⟨z, hz⟩
      obtain ⟨e, he, rfl⟩ := (hZmem z).mp hz
      exact ⟨⟨e, he⟩, rfl⟩
  have hcardZ : Nat.card (v1Grp V H T A K) = Nat.card Z :=
    Nat.card_congr (Equiv.ofBijective f hf)
  have hV1dvd : Nat.card (v1Grp V H T A K) ∣ 8 := by
    rw [← h.card_V_eq_eight]
    exact Subgroup.card_dvd_of_le Sit813.v1Grp_le_V
  have hV1ne8 : Nat.card (v1Grp V H T A K) ≠ 8 := by
    intro h8
    apply h.v1Grp_ne
    exact Subgroup.eq_of_le_of_card_ge Sit813.v1Grp_le_V (by rw [h.card_V_eq_eight, h8])
  have hV1le4 : Nat.card (v1Grp V H T A K) ≤ 4 := by
    have hdvd : Nat.card (v1Grp V H T A K) ∣ 2 ^ 3 := by simpa using hV1dvd
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hkne : k ≠ 3 := by
      intro hk3'
      apply hV1ne8
      rw [hk, hk3']
      norm_num
    have hk2 : k ≤ 2 := by omega
    rw [hk]
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hZle4 : Nat.card Z ≤ 4 := by rw [← hcardZ]; exact hV1le4
  haveI : Module.Finite (ZMod 2) Z := Module.Finite.of_finite
  have hZcard : Nat.card Z = 2 ^ Module.finrank (ZMod 2) Z := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Z)
    rwa [Nat.card_zmod] at h1
  have hZfin : Module.finrank (ZMod 2) Z ≤ 2 := by
    have h1 : 2 ^ Module.finrank (ZMod 2) Z ≤ 2 ^ 2 := by
      rw [← hZcard]; norm_num at hZle4 ⊢; exact hZle4
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
  have hgen : ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) = ⊤ := by
    set Mx : Submodule (ZMod 2) W := ⨆ g : X, Z.map (ρ g : W →ₗ[ZMod 2] W) with hMx
    let Q : Subgroup G :=
      { carrier := {u : G | u ∈ E ∧ ι u ∈ Mx}
        mul_mem' := by
          rintro u u' ⟨huE, hu⟩ ⟨hu'E, hu'⟩
          exact ⟨E.mul_mem huE hu'E, by rw [hadd' u huE u' hu'E]; exact Mx.add_mem hu hu'⟩
        one_mem' := ⟨E.one_mem, by rw [hι_one]; exact Mx.zero_mem⟩
        inv_mem' := by
          rintro u ⟨huE, hu⟩
          exact ⟨E.inv_mem huE, by rw [hι_inv u huE]; exact Mx.neg_mem hu⟩ }
    have hE_le_Q : E ≤ Q := by
      refine conjClosure_le fun k hk x hx => ?_
      have hxE : x ∈ E := hEuh x (Sit813.v1Grp_le_u1Grp hx)
      refine ⟨mem_conjClosure hk hx, ?_⟩
      rw [← hρι' ⟨k, hk⟩ x hxE]
      refine le_iSup (fun g : X => Z.map (ρ g : W →ₗ[ZMod 2] W)) (φ ⟨k, hk⟩) ?_
      exact Submodule.mem_map_of_mem ((hZmem (ι x)).mpr ⟨x, hx, rfl⟩)
    rw [eq_top_iff]
    intro w _
    obtain ⟨e, he, rfl⟩ := hsurj' w
    exact (hE_le_Q he).2
  obtain ⟨hZ2, -, hnat⟩ :=
    natural_of_klein_fixed h122one h122two hXpsl ρ hBi hstab hFel hFcard hFB hquad hFZ hZfin hgen
  have hcardZ4 : Nat.card Z = 4 := by rw [hZcard, hZ2]; norm_num
  have hcardV14 : Nat.card (v1Grp V H T A K) = 4 := by rw [hcardZ, hcardZ4]
  obtain ⟨-, -, -, K', hK'field, hK'fin, φ', ψ', hK'card, hφ', hφ'ker, hψ', hψ'ker, hψ'eq⟩ := hnat
  letI : Field K' := hK'field
  letI : Finite K' := hK'fin
  have hcardK' : Nat.card K' = 4 := by rw [hK'card]; norm_num
  let ψ'' : ↥E →* Multiplicative (Fin 2 → K') :=
    MonoidHom.mk' (fun u => Multiplicative.ofAdd (ψ' ⟨ι u, Submodule.mem_top⟩)) (by
      intro u u'
      rw [← ofAdd_add]
      congr 1
      have h1 : ι ((u : G) * (u' : G)) = ι (u : G) + ι (u' : G) := hadd' u u.2 u' u'.2
      rw [Subgroup.coe_mul]
      rw [show (⟨ι ((u : G) * (u' : G)), Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) W)) =
          ⟨ι (u : G), Submodule.mem_top⟩ + ⟨ι (u' : G), Submodule.mem_top⟩ from
        Subtype.ext h1, map_add])
  have hsurj'' : Function.Surjective ψ'' := by
    intro y
    obtain ⟨v, hv⟩ := hψ' (Multiplicative.toAdd y)
    obtain ⟨u, hu, huw⟩ := hsurj' (v : W)
    refine ⟨⟨u, hu⟩, ?_⟩
    have hw : (⟨ι u, Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) W)) = v := Subtype.ext huw
    show Multiplicative.ofAdd (ψ' ⟨ι u, Submodule.mem_top⟩) = y
    rw [hw, hv]
    exact ofAdd_toAdd y
  have hker'' : ∀ u : ↥E, ψ'' u = 1 ↔
      (u : G) ∈ u1Grp V H T A K ⊓ centralizer (K : Set G) := by
    intro u
    have hfix : (ι (u : G) : W) ∈ fixSub ((⊤ : Subgroup X).map ρ) ↔
        ∀ x : X, ρ x (ι (u : G)) = ι (u : G) := by
      constructor
      · intro hh x
        exact hh (ρ x) (Subgroup.mem_map_of_mem _ (Subgroup.mem_top x))
      · intro hh a ha
        obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp ha
        exact hh x
    have hstep : ψ'' u = 1 ↔ ∀ k : ↥K, (k : G) * (u : G) * (k : G)⁻¹ = (u : G) := by
      rw [show ψ'' u = 1 ↔ ψ' ⟨ι (u : G), Submodule.mem_top⟩ = 0 by
        simp only [ψ'', MonoidHom.mk'_apply, ofAdd_eq_one]]
      rw [hψ'ker]
      rw [hfix]
      constructor
      · intro hh k
        have hku : (k : G) * (u : G) * (k : G)⁻¹ ∈ E :=
          (Subgroup.mem_normalizer_iff.mp (Sit813.k_le_normalizer_u1Grp k.2) (u : G)).1 u.2
        have hmem : ((k : G) * (u : G) * (k : G)⁻¹) * (u : G)⁻¹ ∈ E :=
          E.mul_mem hku (E.inv_mem u.2)
        have h2 := hh (φ k)
        rw [hρι' k (u : G) u.2] at h2
        exact mul_inv_eq_one.mp (hinj' _ hmem (by
          rw [hadd' _ hku _ (E.inv_mem u.2), h2, hι_inv (u : G) u.2, add_neg_cancel]))
      · intro hh x
        obtain ⟨k, rfl⟩ := hφ x
        rw [hρι' k (u : G) u.2, hh k]
    rw [hstep, Subgroup.mem_inf]
    constructor
    · intro hh
      refine ⟨hEhe (u : G) u.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      calc k * (u : G) = (k * (u : G) * k⁻¹) * k := by group
        _ = (u : G) * k := by rw [hh ⟨k, hk⟩]
    · rintro ⟨-, hc⟩ k
      have h1 := Subgroup.mem_centralizer_iff.mp hc (k : G) k.2
      calc (k : G) * (u : G) * (k : G)⁻¹ = ((u : G) * (k : G)) * (k : G)⁻¹ := by rw [← h1]
        _ = (u : G) := by group
  have heq'' : ∀ (k : ↥K) (u u' : ↥E),
      (u' : G) = (k : G) * (u : G) * (k : G)⁻¹ →
      Multiplicative.toAdd (ψ'' u') =
        ((φ'.comp φ) k : Matrix (Fin 2) (Fin 2) K').mulVec (Multiplicative.toAdd (ψ'' u)) := by
    intro k u u' hu'
    have h1 : (ι (u' : G) : W) = ρ (φ k) (ι (u : G)) := by
      rw [hu', hρι' k (u : G) u.2]
    have h2 : (⟨ι (u' : G), Submodule.mem_top⟩ : ↥(⊤ : Submodule (ZMod 2) W)) =
        ⟨ρ (φ k) (ι (u : G)), Submodule.mem_top⟩ := Subtype.ext h1
    have h3 := hψ'eq (φ k) ⟨ι (u : G), Submodule.mem_top⟩ Submodule.mem_top
    simp only [ψ'', MonoidHom.mk'_apply]
    rw [toAdd_ofAdd, toAdd_ofAdd, h2]
    simpa using h3
  exact ⟨⟨K', hK'field, hK'fin, hcardK', φ'.comp φ, ψ'', hφ'.comp hφ, hsurj'',
    hker'', heq''⟩, hV1el, hcardV14⟩

theorem Sit813.eight_fourteen (hin : W3In814 G) {V H T A L K : Subgroup G} {i : ℕ}
    (h : Sit813 V H T i A L K) :
    IsNaturalSL2Module K (u1Grp V H T A K) (u1Grp V H T A K ⊓ centralizer (K : Set G)) ∧
      IsElemAbelian 2 (v1Grp V H T A K) ∧ Nat.card (v1Grp V H T A K) = 4 :=
  h.eight_fourteen_of_nv hin.one hin.two (hin.nv1 h)

end CFSG.LocalAnalysis.WeakClosure81

end
