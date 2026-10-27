module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2LnIdent
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps139

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {W : Type} [CommGroup W] [Finite W] {G X D : Subgroup (MulAut W)} {s : MulAut W}
  {Y : Subgroup W} {n : ℕ}

section Irred

variable [Module (ZMod 2) (Additive W)]

private theorem w1369_irred_M (hw2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    {M : Subgroup W}
    (hsurj : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W)) :
    ∀ A : Subgroup W, A ≤ M → StableUnder K A → A = ⊥ ∨ A = M := by
  intro A hAM hKA
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  have hcardM : Nat.card ↥M = 2 ^ rk ↥M := card_eq_two_pow hw2 M
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥M)
    (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by simpa using hw2 (a : W))) hcardM
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra h
    apply hbot
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hMA : M ≤ A := by
    intro b hbM
    by_cases hb1 : b = 1
    · rw [hb1]; exact A.one_mem
    have hea : (e ⟨a, hAM haA⟩).toAdd ≠ 0 := by
      intro h
      apply ha1
      have h1 : e ⟨a, hAM haA⟩ = 1 := by
        rw [← ofAdd_toAdd (e ⟨a, hAM haA⟩), h, ofAdd_zero]
      exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    have heb : (e ⟨b, hbM⟩).toAdd ≠ 0 := by
      intro h
      apply hb1
      have h1 : e ⟨b, hbM⟩ = 1 := by
        rw [← ofAdd_toAdd (e ⟨b, hbM⟩), h, ofAdd_zero]
      exact congrArg Subtype.val (e.injective (h1.trans (map_one e).symm))
    obtain ⟨τ, hτ⟩ := s16c1610_exists_linearEquiv_apply_eq hea heb
    let φ : MulAut ↥M :=
      (MulAut.congr e).symm (CFSG.Quasithin.H13.Mult.toMulAutPi (rk ↥M) τ)
    have hφa : (φ ⟨a, hAM haA⟩ : ↥M) = ⟨b, hbM⟩ := by
      apply e.injective
      calc e (φ ⟨a, hAM haA⟩)
          = CFSG.Quasithin.H13.Mult.toMulAutPi (rk ↥M) τ (e ⟨a, hAM haA⟩) := by
            simp [φ, MulAut.congr]
        _ = Multiplicative.ofAdd (τ (e ⟨a, hAM haA⟩).toAdd) := by
            rw [CFSG.Quasithin.H13.Mult.toMulAutPi_apply]
        _ = Multiplicative.ofAdd (e ⟨b, hbM⟩).toAdd := by rw [hτ]
        _ = e ⟨b, hbM⟩ := ofAdd_toAdd _
    obtain ⟨k, hk, hkφ⟩ := hsurj φ
    have hb : b = k a := by
      rw [← hkφ ⟨a, hAM haA⟩]
      exact (congrArg Subtype.val hφa).symm
    rw [hb]
    exact hKA k hk a haA
  exact le_antisymm hAM hMA

private noncomputable def w1369_proj (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤) :
    Additive W →ₗ[ZMod 2] Additive W :=
  Submodule.projection (CFSG.Quasithin.H13.Mult.toSub M)
    (CFSG.Quasithin.H13.Mult.toSub (M.map x.toMonoidHom))
    (s16c1610_isCompl_toSub hdis hsup)

private lemma w1369_proj_mem (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (z : Additive W) :
    w1369_proj M x hdis hsup z ∈ CFSG.Quasithin.H13.Mult.toSub M :=
  Submodule.projection_apply_mem
    (p := CFSG.Quasithin.H13.Mult.toSub M)
    (q := CFSG.Quasithin.H13.Mult.toSub (M.map x.toMonoidHom))
    (s16c1610_isCompl_toSub hdis hsup) z

private lemma w1369_proj_eq_zero (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    {z : Additive W} :
    w1369_proj M x hdis hsup z = 0 ↔ z ∈ CFSG.Quasithin.H13.Mult.toSub (M.map x.toMonoidHom) :=
  Submodule.projection_apply_eq_zero_iff
    (p := CFSG.Quasithin.H13.Mult.toSub M)
    (q := CFSG.Quasithin.H13.Mult.toSub (M.map x.toMonoidHom))
    (s16c1610_isCompl_toSub hdis hsup)

private lemma w1369_proj_comm (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    {k : MulAut W} (hkM : ∀ u ∈ M, k u ∈ M)
    (hkxM : ∀ u ∈ M.map x.toMonoidHom, k u ∈ M.map x.toMonoidHom) (z : Additive W) :
    w1369_proj M x hdis hsup (CFSG.Quasithin.H13.Mult.linEquiv k z) =
      CFSG.Quasithin.H13.Mult.linEquiv k (w1369_proj M x hdis hsup z) := by
  simp only [w1369_proj, Submodule.projection_apply]
  refine s16c1610_projectionOnto_comm (s16c1610_isCompl_toSub hdis hsup)
    (CFSG.Quasithin.H13.Mult.linEquiv k) ?_ ?_ z
  · intro y hy
    rw [CFSG.Quasithin.H13.Mult.mem_toSub] at hy ⊢
    simpa [CFSG.Quasithin.H13.Mult.linEquiv_apply] using hkM y.toMul hy
  · intro y hy
    rw [CFSG.Quasithin.H13.Mult.mem_toSub] at hy ⊢
    simpa [CFSG.Quasithin.H13.Mult.linEquiv_apply] using hkxM y.toMul hy

private lemma w1369_inv_mem {U : Subgroup W} (e : MulAut W) (he : ∀ u ∈ U, e u ∈ U) :
    ∀ u ∈ U, e⁻¹ u ∈ U := by
  intro u hu
  have hinj : Function.Injective (fun v : ↥U => (⟨e v, he v v.2⟩ : ↥U)) := by
    intro v w hvw
    exact Subtype.ext (e.injective (congrArg Subtype.val hvw))
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨u, hu⟩
  have : e v = u := congrArg Subtype.val hv
  rw [← this]
  simp

private noncomputable def w1369_restrictMulAut {U : Subgroup W} (e : MulAut W)
    (he : ∀ u ∈ U, e u ∈ U) : MulAut ↥U where
  toFun u := ⟨e u, he u u.2⟩
  invFun u := ⟨e⁻¹ u, w1369_inv_mem e he u u.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (map_mul e (u : W) (v : W))

private noncomputable def w1369_projHom (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤) :
    W →* W where
  toFun w := (w1369_proj M x hdis hsup (Additive.ofMul w)).toMul
  map_one' := by
    show (w1369_proj M x hdis hsup (Additive.ofMul (1 : W))).toMul = 1
    rw [show Additive.ofMul (1 : W) = 0 from rfl, map_zero]
    rfl
  map_mul' w v := by
    show (w1369_proj M x hdis hsup (Additive.ofMul (w * v))).toMul =
      (w1369_proj M x hdis hsup (Additive.ofMul w)).toMul *
        (w1369_proj M x hdis hsup (Additive.ofMul v)).toMul
    rw [ofMul_mul, map_add, toMul_add]

private lemma w1369_projHom_eq_one_iff (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤) (w : W) :
    w1369_projHom M x hdis hsup w = 1 ↔ w ∈ M.map x.toMonoidHom := by
  show (w1369_proj M x hdis hsup (Additive.ofMul w)).toMul = 1 ↔ w ∈ M.map x.toMonoidHom
  rw [toMul_eq_one, w1369_proj_eq_zero, CFSG.Quasithin.H13.Mult.mem_toSub,
    toMul_ofMul]

private lemma w1369_projHom_comm (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    {k : MulAut W} (hkM : ∀ u ∈ M, k u ∈ M)
    (hkxM : ∀ u ∈ M.map x.toMonoidHom, k u ∈ M.map x.toMonoidHom) (w : W) :
    w1369_projHom M x hdis hsup (k w) = k (w1369_projHom M x hdis hsup w) := by
  show (w1369_proj M x hdis hsup (Additive.ofMul (k w))).toMul =
    k ((w1369_proj M x hdis hsup (Additive.ofMul w)).toMul)
  have h1 : Additive.ofMul (k w) =
      CFSG.Quasithin.H13.Mult.linEquiv k (Additive.ofMul w) := rfl
  rw [h1, w1369_proj_comm M x hdis hsup hkM hkxM]
  simp [CFSG.Quasithin.H13.Mult.linEquiv_apply]

private noncomputable def w1369_piG (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (g : MulAut W) : ↥(M.map g.toMonoidHom) →* ↥M :=
  ((w1369_projHom M x hdis hsup).comp (M.map g.toMonoidHom).subtype).codRestrict M
    (fun u => by
      show (w1369_proj M x hdis hsup (Additive.ofMul (u : W))).toMul ∈ M
      rw [← CFSG.Quasithin.H13.Mult.mem_toSub]
      exact w1369_proj_mem M x hdis hsup _)

private lemma w1369_piG_eq_one_iff (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (g : MulAut W) (u : ↥(M.map g.toMonoidHom)) :
    w1369_piG M x hdis hsup g u = 1 ↔ (u : W) ∈ M.map x.toMonoidHom := by
  constructor
  · intro h
    exact (w1369_projHom_eq_one_iff M x hdis hsup (u : W)).mp (congrArg Subtype.val h)
  · intro h
    apply Subtype.ext
    exact (w1369_projHom_eq_one_iff M x hdis hsup (u : W)).mpr h

private noncomputable def w1369_Tg (M : Subgroup W) (g : MulAut W) :
    ↥M ≃* ↥(M.map g.toMonoidHom) :=
  Subgroup.equivMapOfInjective M g.toMonoidHom g.injective

private lemma w1369_Tg_apply (M : Subgroup W) (g : MulAut W) (m : ↥M) :
    ((w1369_Tg M g m : ↥(M.map g.toMonoidHom)) : W) = g (m : W) :=
  rfl

private noncomputable def w1369_T (M : Subgroup W) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (g : MulAut W) : ↥M →* ↥M :=
  (w1369_piG M x hdis hsup g).comp (w1369_Tg M g).toMonoidHom

private lemma w1369_stable_xM {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hKM : StableUnder K M) {x : MulAut W} (hxcomm : ∀ k ∈ K, k * x = x * k)
    (k : ↥K) : ∀ u ∈ M.map x.toMonoidHom, (k : MulAut W) u ∈ M.map x.toMonoidHom := by
  intro u hu
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hu
  have hk : (k : MulAut W) * x = x * (k : MulAut W) := hxcomm _ k.2
  have h1 : (k : MulAut W) ((MulEquiv.toMonoidHom x) m) =
      (MulEquiv.toMonoidHom x) ((k : MulAut W) m) := by
    change ((k : MulAut W) * x) m = (x * (k : MulAut W)) m
    rw [hk]
  rw [h1]
  exact Subgroup.mem_map_of_mem x.toMonoidHom (hKM _ k.2 m hm)

private lemma w1369_T_twist {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hKM : StableUnder K M) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (xcomm : ∀ k ∈ K, k * x = x * k)
    (hKnormal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) {g : MulAut W} (hg : g ∈ G)
    (k : ↥K) (m : ↥M) :
    ∃ m' : ↥M, (w1369_T M x hdis hsup g m' : W) =
      (k : MulAut W) (w1369_T M x hdis hsup g m : W) := by
  have hkM : ∀ u ∈ M, (k : MulAut W) u ∈ M := fun u hu => hKM _ k.2 u hu
  have hkxM := w1369_stable_xM hKM xcomm k
  have hk' : g⁻¹ * (k : MulAut W) * g ∈ K := by
    have hk_map : (k : MulAut W) ∈ K.map (MulAut.conj g).toMonoidHom := by
      rw [hKnormal g hg]; exact k.2
    obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.mp hk_map
    have hgy' : MulAut.conj g y = (k : MulAut W) := by simpa using hgy
    rw [MulAut.conj_apply] at hgy'
    have hyk : y = g⁻¹ * (k : MulAut W) * g := by
      rw [← hgy']
      group
    rwa [hyk] at hy
  refine ⟨⟨(g⁻¹ * (k : MulAut W) * g) m, hKM _ hk' m m.2⟩, ?_⟩
  show w1369_projHom M x hdis hsup (g ((g⁻¹ * (k : MulAut W) * g) m)) =
    (k : MulAut W) (w1369_projHom M x hdis hsup (g m))
  have hprod : g * (g⁻¹ * (k : MulAut W) * g) = (k : MulAut W) * g := by group
  have h1 : (k : MulAut W) (g (m : W)) = g ((g⁻¹ * (k : MulAut W) * g) (m : W)) := by
    change ((k : MulAut W) * g) (m : W) = (g * (g⁻¹ * (k : MulAut W) * g)) (m : W)
    rw [hprod]
  rw [← h1]
  exact w1369_projHom_comm M x hdis hsup hkM hkxM (g (m : W))

private lemma w1369_T_range_eq_bot_or_top (hw2 : ∀ w : W, w ^ 2 = 1)
    {K : Subgroup (MulAut W)} {M : Subgroup W} (hKM : StableUnder K M) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (hsurjM : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (xcomm : ∀ k ∈ K, k * x = x * k)
    (hKnormal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) {g : MulAut W} (hg : g ∈ G) :
    (w1369_T M x hdis hsup g).range = ⊥ ∨ (w1369_T M x hdis hsup g).range = ⊤ := by
  let A : Subgroup W := (w1369_T M x hdis hsup g).range.map M.subtype
  have hA : A ≤ M := by
    intro a ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
    exact y.2
  have hKA : StableUnder K A := by
    intro k hk a ha
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ha
    rw [MonoidHom.mem_range] at hm
    obtain ⟨m₀, hm₀⟩ := hm
    obtain ⟨m', hm'⟩ := w1369_T_twist hKM x hdis hsup xcomm hKnormal hg ⟨k, hk⟩ m₀
    refine Subgroup.mem_map.mpr ⟨w1369_T M x hdis hsup g m',
      (MonoidHom.mem_range.mpr ⟨m', rfl⟩), ?_⟩
    show ((w1369_T M x hdis hsup g m' : ↥M) : W) = k (m : W)
    rw [hm']
    rw [show ((w1369_T M x hdis hsup g m₀ : ↥M) : W) = (m : W) from congrArg Subtype.val hm₀]
  rcases w1369_irred_M hw2 hsurjM A hA hKA with hbot | htop
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    have hmem : (m : W) ∈ A := Subgroup.mem_map_of_mem M.subtype hm
    rw [hbot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  · right
    rw [eq_top_iff]
    intro m hm
    have hmW : (m : W) ∈ A := htop.symm ▸ m.2
    obtain ⟨m', hm', hm'm⟩ := Subgroup.mem_map.mp hmW
    have hmm : m' = m := Subtype.ext hm'm
    rwa [hmm] at hm'

private lemma w1369_conj_mem {K : Subgroup (MulAut W)}
    (hKnormal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) {g : MulAut W} (hg : g ∈ G)
    (k : ↥K) : g⁻¹ * (k : MulAut W) * g ∈ K := by
  have hk_map : (k : MulAut W) ∈ K.map (MulAut.conj g).toMonoidHom := by
    rw [hKnormal g hg]; exact k.2
  obtain ⟨y, hy, hgy⟩ := Subgroup.mem_map.mp hk_map
  have hgy' : MulAut.conj g y = (k : MulAut W) := by simpa using hgy
  rw [MulAut.conj_apply] at hgy'
  have hyk : y = g⁻¹ * (k : MulAut W) * g := by
    rw [← hgy']; group
  rwa [hyk] at hy

private lemma w1369_T_twist' {K : Subgroup (MulAut W)} {M : Subgroup W}
    (hKM : StableUnder K M) (x : MulAut W)
    (hdis : M ⊓ M.map x.toMonoidHom = ⊥) (hsup : M ⊔ M.map x.toMonoidHom = ⊤)
    (xcomm : ∀ k ∈ K, k * x = x * k)
    (hKnormal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) {g : MulAut W} (hg : g ∈ G)
    (k : ↥K) (m : ↥M) :
    (w1369_T M x hdis hsup g
        ⟨(g⁻¹ * (k : MulAut W) * g) m, hKM _ (w1369_conj_mem hKnormal hg k) m m.2⟩ : W) =
      (k : MulAut W) (w1369_T M x hdis hsup g m : W) := by
  have hkM : ∀ u ∈ M, (k : MulAut W) u ∈ M := fun u hu => hKM _ k.2 u hu
  have hkxM := w1369_stable_xM hKM xcomm k
  show w1369_projHom M x hdis hsup (g ((g⁻¹ * (k : MulAut W) * g) m)) =
    (k : MulAut W) (w1369_projHom M x hdis hsup (g (m : W)))
  have hprod : g * (g⁻¹ * (k : MulAut W) * g) = (k : MulAut W) * g := by group
  have h1 : (k : MulAut W) (g (m : W)) = g ((g⁻¹ * (k : MulAut W) * g) (m : W)) := by
    change ((k : MulAut W) * g) (m : W) = (g * (g⁻¹ * (k : MulAut W) * g)) (m : W)
    rw [hprod]
  rw [← h1]
  exact w1369_projHom_comm M x hdis hsup hkM hkxM (g (m : W))

private lemma w1369_exists_rho (hw2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    {M : Subgroup W} (hKM : StableUnder K M)
    (hsurjM : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (x : MulAut W) (hdis : M ⊓ M.map x.toMonoidHom = ⊥)
    (hsup : M ⊔ M.map x.toMonoidHom = ⊤) (xcomm : ∀ k ∈ K, k * x = x * k)
    (hKnormal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) {g : MulAut W} (hg : g ∈ G) :
    ∃ ρ : MulAut ↥M, ∀ (k : ↥K) (m : ↥M),
      ((ρ ⟨(g⁻¹ * (k : MulAut W) * g) m, hKM _ (w1369_conj_mem hKnormal hg k) m m.2⟩ : ↥M) : W) =
        (k : MulAut W) ((ρ m : ↥M) : W) := by
  rcases w1369_T_range_eq_bot_or_top hw2 hKM x hdis hsup hsurjM xcomm hKnormal hg with
    hbot | htop
  · have hT1 : ∀ m : ↥M, w1369_T M x hdis hsup g m = 1 := by
      intro m
      have hm : w1369_T M x hdis hsup g m ∈ (w1369_T M x hdis hsup g).range :=
        MonoidHom.mem_range.mpr ⟨m, rfl⟩
      rw [hbot] at hm
      exact Subgroup.mem_bot.mp hm
    have hgm : ∀ m : ↥M, g (m : W) ∈ M.map x.toMonoidHom := by
      intro m
      have h1 : w1369_piG M x hdis hsup g (w1369_Tg M g m) = 1 := by
        show w1369_T M x hdis hsup g m = 1
        exact hT1 m
      have h2 : ((w1369_Tg M g m : ↥(M.map g.toMonoidHom)) : W) ∈ M.map x.toMonoidHom :=
        (w1369_piG_eq_one_iff M x hdis hsup g (w1369_Tg M g m)).mp h1
      rwa [w1369_Tg_apply] at h2
    let ρ : MulAut ↥M := w1369_restrictMulAut (x⁻¹ * g)
      (fun u hu => by
        obtain ⟨m, hm, hxm⟩ := Subgroup.mem_map.mp (hgm ⟨u, hu⟩)
        have hxu : (x⁻¹ * g) u = m := by
          change x⁻¹ (g u) = m
          rw [← hxm]
          simp
        rw [hxu]
        exact hm)
    refine ⟨ρ, ?_⟩
    intro k m
    have hxinv : (k : MulAut W) * x⁻¹ = x⁻¹ * (k : MulAut W) :=
      (Commute.inv_right (show Commute (k : MulAut W) x from xcomm _ k.2)).eq
    show x⁻¹ (g ((g⁻¹ * (k : MulAut W) * g) m)) = (k : MulAut W) (x⁻¹ (g (m : W)))
    have h1 : g ((g⁻¹ * (k : MulAut W) * g) m) = (k : MulAut W) (g (m : W)) := by
      change (g * (g⁻¹ * (k : MulAut W) * g)) (m : W) = ((k : MulAut W) * g) (m : W)
      rw [show g * (g⁻¹ * (k : MulAut W) * g) = (k : MulAut W) * g from by group]
    rw [h1]
    change (x⁻¹ * (k : MulAut W)) (g (m : W)) = ((k : MulAut W) * x⁻¹) (g (m : W))
    rw [hxinv]
  · have hsurjT : Function.Surjective (w1369_T M x hdis hsup g) := by
      intro y
      have hy : y ∈ (w1369_T M x hdis hsup g).range := by
        rw [htop]; exact Subgroup.mem_top y
      exact MonoidHom.mem_range.mp hy
    let ρ : MulAut ↥M := MulEquiv.ofBijective (w1369_T M x hdis hsup g)
      ⟨(Finite.injective_iff_surjective).mpr hsurjT, hsurjT⟩
    refine ⟨ρ, ?_⟩
    intro k m
    show (w1369_T M x hdis hsup g
        ⟨(g⁻¹ * (k : MulAut W) * g) m, hKM _ (w1369_conj_mem hKnormal hg k) m m.2⟩ : W) =
      (k : MulAut W) (w1369_T M x hdis hsup g m : W)
    exact w1369_T_twist' hKM x hdis hsup xcomm hKnormal hg k m

lemma w1369_exists_centralizing (hw2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    {M : Subgroup W} (hKM : StableUnder K M)
    (hfaith : ∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1)
    (hsurjM : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (x : MulAut W) (hdis : M ⊓ M.map x.toMonoidHom = ⊥)
    (hsup : M ⊔ M.map x.toMonoidHom = ⊤) (xcomm : ∀ k ∈ K, k * x = x * k)
    (hKnormal : ∀ g ∈ G, K.map (MulAut.conj g).toMonoidHom = K) {g : MulAut W} (hg : g ∈ G) :
    ∃ k0 ∈ K, ∀ k ∈ K, (g * k0⁻¹) * (k : MulAut W) = (k : MulAut W) * (g * k0⁻¹) := by
  obtain ⟨ρ, hρ⟩ := w1369_exists_rho hw2 hKM hsurjM x hdis hsup xcomm hKnormal hg
  obtain ⟨k0, hk0K, hk0ρ⟩ := hsurjM ρ
  refine ⟨k0, hk0K, ?_⟩
  intro k hk
  have hAB : k0 * (g⁻¹ * (k : MulAut W) * g) = (k : MulAut W) * k0 := by
    have hmemA : k0 * (g⁻¹ * (k : MulAut W) * g) ∈ K :=
      K.mul_mem hk0K (w1369_conj_mem hKnormal hg ⟨k, hk⟩)
    have hmemB : (k : MulAut W) * k0 ∈ K := K.mul_mem hk hk0K
    have htriv : ∀ m ∈ M,
        (k0 * (g⁻¹ * (k : MulAut W) * g) * ((k : MulAut W) * k0)⁻¹) m = m := by
      intro m hm
      have hkm : (k : MulAut W)⁻¹ m ∈ M := hKM _ (K.inv_mem hk) m hm
      have hk0km : k0⁻¹ ((k : MulAut W)⁻¹ m) ∈ M := hKM _ (K.inv_mem hk0K) _ hkm
      have hσ : (g⁻¹ * (k : MulAut W) * g) (k0⁻¹ ((k : MulAut W)⁻¹ m)) ∈ M :=
        hKM _ (w1369_conj_mem hKnormal hg ⟨k, hk⟩) _ hk0km
      show k0 ((g⁻¹ * (k : MulAut W) * g) (((k : MulAut W) * k0)⁻¹ m)) = m
      have h1 : (((k : MulAut W) * k0)⁻¹ m) = k0⁻¹ ((k : MulAut W)⁻¹ m) := by
        change ((k0⁻¹ * (k : MulAut W)⁻¹) m) = k0⁻¹ ((k : MulAut W)⁻¹ m)
        rfl
      rw [h1]
      have h4 : ((ρ ⟨(g⁻¹ * (k : MulAut W) * g) (k0⁻¹ ((k : MulAut W)⁻¹ m)),
            hσ⟩ : ↥M) : W) =
          k0 ((g⁻¹ * (k : MulAut W) * g) (k0⁻¹ ((k : MulAut W)⁻¹ m))) :=
        hk0ρ _
      have h2 : ((ρ ⟨(g⁻¹ * (k : MulAut W) * g) (k0⁻¹ ((k : MulAut W)⁻¹ m)),
            hσ⟩ : ↥M) : W) =
          (k : MulAut W) ((ρ ⟨k0⁻¹ ((k : MulAut W)⁻¹ m), hk0km⟩ : ↥M) : W) :=
        hρ ⟨k, hk⟩ ⟨k0⁻¹ ((k : MulAut W)⁻¹ m), hk0km⟩
      have h3 : ((ρ ⟨k0⁻¹ ((k : MulAut W)⁻¹ m), hk0km⟩ : ↥M) : W) =
          k0 (k0⁻¹ ((k : MulAut W)⁻¹ m)) := hk0ρ _
      rw [← h4, h2, h3]
      simp
    have h1 : k0 * (g⁻¹ * (k : MulAut W) * g) * ((k : MulAut W) * k0)⁻¹ = 1 :=
      hfaith _ (K.mul_mem hmemA (K.inv_mem hmemB)) htriv
    exact mul_inv_eq_one.mp h1
  have hceq : (g * k0⁻¹)⁻¹ * (k : MulAut W) * (g * k0⁻¹) = (k : MulAut W) := by
    have h1 : (g * k0⁻¹)⁻¹ * (k : MulAut W) * (g * k0⁻¹) =
        k0 * (g⁻¹ * (k : MulAut W) * g) * k0⁻¹ := by group
    rw [h1, hAB]
    group
  have hc : (k : MulAut W) * (g * k0⁻¹) = (g * k0⁻¹) * (k : MulAut W) := by
    calc (k : MulAut W) * (g * k0⁻¹)
        = (g * k0⁻¹) * ((g * k0⁻¹)⁻¹ * (k : MulAut W) * (g * k0⁻¹)) := by group
      _ = (g * k0⁻¹) * (k : MulAut W) := by rw [hceq]
  exact hc.symm

private lemma w1369_end_K_zero_or_id (hw2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    {M : Subgroup W} (hKM : StableUnder K M)
    (hsurjM : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (hrk : rk ↥M = n) (hn : 2 ≤ n) {k : MulAut W} (hkK : k ∈ K)
    (hkc : ∀ l ∈ K, k * l = l * k) : ∀ m ∈ M, k m = m := by
  intro m hm
  have hcardM : Nat.card ↥M = 2 ^ n := by rw [card_eq_two_pow hw2 M, hrk]
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥M)
    (fun a b => mul_comm a b)
    (fun a => Subtype.ext (by simpa using hw2 (a : W))) hcardM
  let rk : MulAut ↥M := w1369_restrictMulAut k (fun u hu => hKM _ hkK u hu)
  let ψ : GL (Fin n) (ZMod 2) := (CFSG.SectionRank.Ccomm.elemAutEquivGL e) rk
  let φ : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2) := s16c1610_glAction n ψ
  have hφcomm : ∀ τ : (Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2), ∀ y,
      (φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) (τ y) =
        τ ((φ : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)) y) := by
    intro τ y
    obtain ⟨ψτ, rfl⟩ := (s16c1610_glAction n).surjective τ
    obtain ⟨l, hlK, hl⟩ := hsurjM ((CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm ψτ)
    have hrl : w1369_restrictMulAut l (fun u hu => hKM _ hlK u hu) =
        (CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm ψτ := by
      ext u
      exact (hl u).symm
    have hcomm : w1369_restrictMulAut k (fun u hu => hKM _ hkK u hu) *
        w1369_restrictMulAut l (fun u hu => hKM _ hlK u hu) =
        w1369_restrictMulAut l (fun u hu => hKM _ hlK u hu) *
          w1369_restrictMulAut k (fun u hu => hKM _ hkK u hu) := by
      ext u
      change k (l (u : W)) = l (k (u : W))
      rw [← MulAut.mul_apply, hkc l hlK]
      rfl
    have hψ : ψ * ψτ = ψτ * ψ := by
      have h1 := congrArg (CFSG.SectionRank.Ccomm.elemAutEquivGL e) hcomm
      rw [map_mul, map_mul, hrl] at h1
      simpa [ψ] using h1
    have h2 := congrArg (s16c1610_glAction n) hψ
    simp only [map_mul] at h2
    exact congrFun (congrArg DFunLike.coe h2) y
  have hd : 2 ≤ Module.finrank (ZMod 2) (Fin n → ZMod 2) := by
    rw [Module.finrank_fin_fun]; omega
  rcases s16c1610_end_eq_zero_or_id hd hφcomm with h0 | hid
  · exfalso
    have h1 : (1 : Fin n → ZMod 2) = 0 := by
      have h0y : φ (1 : Fin n → ZMod 2) = 0 := by
        simpa using congrFun (congrArg DFunLike.coe h0) (1 : Fin n → ZMod 2)
      calc (1 : Fin n → ZMod 2) = φ.symm (φ 1) := (φ.symm_apply_apply 1).symm
        _ = φ.symm 0 := by rw [h0y]
        _ = 0 := map_zero _
    have h2 := congrFun h1 ⟨0, by omega⟩
    simp at h2
  · have hφid : φ = LinearEquiv.refl (ZMod 2) (Fin n → ZMod 2) := by
      apply LinearEquiv.ext
      intro y
      apply funext
      intro i
      exact congrFun (congrFun (congrArg DFunLike.coe hid) y) i
    have hψ1 : ψ = 1 := by
      have h := congrArg (s16c1610_glAction n).symm hφid
      rw [show φ = (s16c1610_glAction n) ψ from rfl] at h
      rw [MulEquiv.symm_apply_apply] at h
      rw [show LinearEquiv.refl (ZMod 2) (Fin n → ZMod 2) = (s16c1610_glAction n) 1
        from (map_one _).symm] at h
      rw [MulEquiv.symm_apply_apply] at h
      exact h
    have hrk1 : rk = 1 := by
      have h := congrArg (CFSG.SectionRank.Ccomm.elemAutEquivGL e).symm hψ1
      rw [show ψ = (CFSG.SectionRank.Ccomm.elemAutEquivGL e) rk from rfl] at h
      rw [MulEquiv.symm_apply_apply] at h
      rw [show (1 : GL (Fin n) (ZMod 2)) =
        (CFSG.SectionRank.Ccomm.elemAutEquivGL e) 1 from (map_one _).symm] at h
      rw [MulEquiv.symm_apply_apply] at h
      exact h
    have h1 : ((rk ⟨m, hm⟩ : ↥M) : W) = k m := rfl
    have h2 : rk ⟨m, hm⟩ = ⟨m, hm⟩ := by rw [hrk1]; rfl
    rw [← h1, h2]

lemma w1369_K_inf_centralizer (hw2 : ∀ w : W, w ^ 2 = 1) {K : Subgroup (MulAut W)}
    {M : Subgroup W} (hKM : StableUnder K M)
    (hfaith : ∀ k ∈ K, (∀ m ∈ M, k m = m) → k = 1)
    (hsurjM : ∀ g : MulAut ↥M, ∃ k ∈ K, ∀ m : ↥M, ((g m : ↥M) : W) = k (m : W))
    (hrk : rk ↥M = n) (hn : 2 ≤ n) {k : MulAut W} (hkK : k ∈ K)
    (hkc : ∀ l ∈ K, k * l = l * k) : k = 1 :=
  hfaith k hkK (w1369_end_K_zero_or_id hw2 hKM hsurjM hrk hn hkK hkc)

end Irred

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps139
