module

public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.F4Count
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNPoly
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNYam
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNBase

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
  CFSG.ASVolI.ChF

section Setting

@[expose, reducible] noncomputable def burnsideF45_setting {κ : GLKind} {p f : ℕ} {E : Type}
    [Group E] {Gp M₁ M₂ : Subgroup E} (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) : LieSetting.{0, 0} :=
  { α := RankTwoAmalgam.ofSubgroups M₁ M₂
    Yb := ↥(M₁ ⊔ M₂)
    grp := inferInstance
    fin := haveI : Finite E := hyp.finite; inferInstance
    ι := incl M₁ M₂
    hι := incl_faithful M₁ M₂
    N := Gp.comap (toE (incl M₁ M₂))
    hN := haveI : Gp.Normal := hyp.normal; Subgroup.Normal.comap inferInstance _
    p := p
    hp := hp
    m := κ.m
    hm := hm }

theorem burnsideF45_three_le_m (κ : GLKind) : 3 ≤ κ.m := by
  cases κ <;> decide

variable {E : Type} [Group E] {M₁ M₂ : Subgroup E}

theorem burnsideF45_toE_bijective (hgen : M₁ ⊔ M₂ = ⊤) :
    Function.Bijective (toE (incl M₁ M₂)) := by
  refine ⟨fun a b h => Subtype.ext (Subtype.ext h), fun e => ?_⟩
  exact ⟨⟨⟨e, by rw [hgen]; exact Subgroup.mem_top e⟩, by
    rw [(incl M₁ M₂).gen]; exact Subgroup.mem_top _⟩, rfl⟩

theorem burnsideF45_mem_stv_lv_iff {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (g : c.G0) : g ∈ stv c c.lv ↔ g ∈ (f2 (c := c)).range := by
  constructor
  · intro hg
    exact stv_lv_le_range_f2 c hg
  · rintro ⟨a, rfl⟩
    exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a)

theorem burnsideF45_mem_stv_xv_iff (x : (incl M₁ M₂).G0) :
    x ∈ stv (incl M₁ M₂) (incl M₁ M₂).xv ↔ toE (incl M₁ M₂) x ∈ M₁ := by
  rw [stv_xv_eq_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩

theorem burnsideF45_mem_stv_lv_iff' (x : (incl M₁ M₂).G0) :
    x ∈ stv (incl M₁ M₂) (incl M₁ M₂).lv ↔ toE (incl M₁ M₂) x ∈ M₂ := by
  rw [burnsideF45_mem_stv_lv_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨_, h⟩, Subtype.ext (Subtype.ext rfl)⟩

end Setting

section Qbar

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_mem_Qbar_xv (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (x : (burnsideF45_setting hyp hp hm).ι.G0) :
    x ∈ (burnsideF45_setting hyp hp hm).Qbar (burnsideF45_setting hyp hp hm).ι.xv ↔
      toE (burnsideF45_setting hyp hp hm).ι x ∈ pCoreOf p (Gp ⊓ M₁) := by
  revert x
  set S := burnsideF45_setting hyp hp hm with hS
  let e : S.ι.G0 ≃* E := MulEquiv.ofBijective (toE S.ι) (burnsideF45_toE_bijective hyp.gen)
  have hN : ∀ y : S.ι.G0, y ∈ S.N ⊓ stv S.ι S.ι.xv ↔ e y ∈ Gp ⊓ M₁ := fun y =>
    Subgroup.mem_inf.trans ((and_congr (show y ∈ S.N ↔ e y ∈ Gp from Iff.rfl)
      (burnsideF45_mem_stv_xv_iff y)).trans Subgroup.mem_inf.symm)
  have h1 : S.N ⊓ stv S.ι S.ι.xv = (Gp ⊓ M₁).map e.symm.toMonoidHom := by
    ext y
    rw [hN, Subgroup.mem_map_equiv]
    simp
  have h2 : S.Qbar S.ι.xv = (pCoreOf p (Gp ⊓ M₁)).map e.symm.toMonoidHom := by
    unfold LieSetting.Qbar
    show pCoreOf p (S.N ⊓ stv S.ι S.ι.xv) = _
    rw [h1]
    exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p e.symm _
  intro x
  show x ∈ S.Qbar S.ι.xv ↔ e x ∈ pCoreOf p (Gp ⊓ M₁)
  rw [h2, Subgroup.mem_map_equiv]
  simp

theorem burnsideF45_mem_Qbar_lv (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (x : (burnsideF45_setting hyp hp hm).ι.G0) :
    x ∈ (burnsideF45_setting hyp hp hm).Qbar (burnsideF45_setting hyp hp hm).ι.lv ↔
      toE (burnsideF45_setting hyp hp hm).ι x ∈ pCoreOf p (Gp ⊓ M₂) := by
  revert x
  set S := burnsideF45_setting hyp hp hm with hS
  let e : S.ι.G0 ≃* E := MulEquiv.ofBijective (toE S.ι) (burnsideF45_toE_bijective hyp.gen)
  have hN : ∀ y : S.ι.G0, y ∈ S.N ⊓ stv S.ι S.ι.lv ↔ e y ∈ Gp ⊓ M₂ := fun y =>
    Subgroup.mem_inf.trans ((and_congr (show y ∈ S.N ↔ e y ∈ Gp from Iff.rfl)
      (burnsideF45_mem_stv_lv_iff' y)).trans Subgroup.mem_inf.symm)
  have h1 : S.N ⊓ stv S.ι S.ι.lv = (Gp ⊓ M₂).map e.symm.toMonoidHom := by
    ext y
    rw [hN, Subgroup.mem_map_equiv]
    simp
  have h2 : S.Qbar S.ι.lv = (pCoreOf p (Gp ⊓ M₂)).map e.symm.toMonoidHom := by
    unfold LieSetting.Qbar
    show pCoreOf p (S.N ⊓ stv S.ι S.ι.lv) = _
    rw [h1]
    exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv p e.symm _
  intro x
  show x ∈ S.Qbar S.ι.lv ↔ e x ∈ pCoreOf p (Gp ⊓ M₂)
  rw [h2, Subgroup.mem_map_equiv]
  simp

theorem burnsideF45_Qx_eq_Qbar (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m) :
    Qx (M₁ := M₁) (M₂ := M₂) p Gp (burnsideF45_setting hyp hp hm).ι =
      (burnsideF45_setting hyp hp hm).Qbar (burnsideF45_setting hyp hp hm).ι.xv := by
  ext x
  refine Iff.trans ?_ (burnsideF45_mem_Qbar_xv hyp hp hm x).symm
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp ha
  · intro hx
    have hxM : toE (burnsideF45_setting hyp hp hm).ι x ∈ M₁ :=
      ((CFSG.LieType.BorelTits.pCoreOf_le p _) hx).2
    have hx' := (burnsideF45_mem_stv_xv_iff (M₁ := M₁) (M₂ := M₂) x).2 hxM
    rw [stv_xv_eq_range] at hx'
    obtain ⟨a, rfl⟩ := hx'
    exact ⟨a, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem burnsideF45_Ql_eq_Qbar (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m) :
    Ql (M₁ := M₁) (M₂ := M₂) p Gp (burnsideF45_setting hyp hp hm).ι =
      (burnsideF45_setting hyp hp hm).Qbar (burnsideF45_setting hyp hp hm).ι.lv := by
  ext x
  refine Iff.trans ?_ (burnsideF45_mem_Qbar_lv hyp hp hm x).symm
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact Subgroup.mem_subgroupOf.mp ha
  · intro hx
    have hxM : toE (burnsideF45_setting hyp hp hm).ι x ∈ M₂ :=
      ((CFSG.LieType.BorelTits.pCoreOf_le p _) hx).2
    have hx' := (burnsideF45_mem_stv_lv_iff' (M₁ := M₁) (M₂ := M₂) x).2 hxM
    rw [burnsideF45_mem_stv_lv_iff] at hx'
    obtain ⟨a, rfl⟩ := hx'
    exact ⟨a, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem burnsideF45_Qvert_eq_of_equivariant {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y]
    (c : α.Completion Y) (Q : c.Γ → Subgroup c.G0)
    (hQ : ∀ (g : c.G0) (v : c.Γ), Q (g • v) = conjSub g (Q v)) (u : c.Γ) :
    c.Qvert (Q c.xv) (Q c.lv) u = Q u := by
  have hb : ∀ b : Bool, cond b (Q c.lv) (Q c.xv) = Q (c.baseVert b) := by
    intro b
    cases b <;> rfl
  have hterm : ∀ g : c.G0, g • c.baseVert (CosetGeom.vtype u) = u →
      conjSub g (cond (CosetGeom.vtype u) (Q c.lv) (Q c.xv)) = Q u := by
    intro g hg
    rw [hb, ← hQ, hg]
  obtain ⟨g0, hg0⟩ := exists_smul_eq_baseVert c u
  unfold Completion.Qvert
  exact le_antisymm (iSup₂_le fun g hg => (hterm g hg).le)
    ((hterm g0 hg0).ge.trans (le_iSup₂ (f := fun (g : c.G0)
      (_ : g • c.baseVert (CosetGeom.vtype u) = u) =>
        conjSub g (cond (CosetGeom.vtype u) (Q c.lv) (Q c.xv))) g0 hg0))

theorem burnsideF45_Qu_eq_Qbar (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime) (hm : 3 ≤ κ.m)
    (u : (burnsideF45_setting hyp hp hm).ι.Γ) :
    Qu (M₁ := M₁) (M₂ := M₂) p Gp (burnsideF45_setting hyp hp hm).ι u =
      (burnsideF45_setting hyp hp hm).Qbar u := by
  have h := burnsideF45_Qvert_eq_of_equivariant (burnsideF45_setting hyp hp hm).ι
    (burnsideF45_setting hyp hp hm).Qbar
    (fun g v => (burnsideF45_setting hyp hp hm).Qbar_smul g v) u
  rw [← burnsideF45_Qx_eq_Qbar hyp hp hm, ← burnsideF45_Ql_eq_Qbar hyp hp hm] at h
  exact h

end Qbar

section Model

open CFSG.Quasithin.H13.F431

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_facts45L_of_model (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) {X : Type} [Group X] {V : Type} [MulAction X V] {ΓM : SimpleGraph V}
    [GraphAction X ΓM] (θ : X ≃* ↥Gp) {v₁ v₂ : V}
    (hstab1 : ∀ y : X, ((θ y : ↥Gp) : E) ∈ M₁ ↔ y • v₁ = v₁)
    (hstab2 : ∀ y : X, ((θ y : ↥Gp) : E) ∈ M₂ ↔ y • v₂ = v₂)
    (hdisj : ∀ y z : X, y • v₁ ≠ z • v₂)
    (hnoadj1 : ∀ y z : X, ¬ ΓM.Adj (y • v₁) (z • v₁))
    (hnoadj2 : ∀ y z : X, ¬ ΓM.Adj (y • v₂) (z • v₂))
    (hadj : ΓM.Adj v₁ v₂) (hpoly : IsGenPolygon ΓM κ.m)
    (hn1 : 3 ≤ Nat.card (ΓM.neighborSet v₁)) (hn2 : 3 ≤ Nat.card (ΓM.neighborSet v₂))
    (MB₁ : F45.ModelBase ΓM κ.m v₁ (pCoreOf p (MulAction.stabilizer X v₁)))
    (MB₂ : F45.ModelBase ΓM κ.m v₂ (pCoreOf p (MulAction.stabilizer X v₂))) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  set S := burnsideF45_setting hyp hp hm with hS
  let e : S.ι.G0 ≃* E := MulEquiv.ofBijective (toE S.ι) (burnsideF45_toE_bijective hyp.gen)
  let Φ : X →* S.ι.G0 := e.symm.toMonoidHom.comp (Gp.subtype.comp θ.toMonoidHom)
  have hΦ : ∀ y : X, e (Φ y) = ((θ y : ↥Gp) : E) := fun y => by simp [Φ]
  have hstabx : ∀ g : (incl M₁ M₂).G0, g • (incl M₁ M₂).xv = (incl M₁ M₂).xv ↔ e g ∈ M₁ :=
    fun g => (MulAction.mem_stabilizer_iff.symm).trans (burnsideF45_mem_stv_xv_iff g)
  have hstabl : ∀ g : (incl M₁ M₂).G0, g • (incl M₁ M₂).lv = (incl M₁ M₂).lv ↔ e g ∈ M₂ :=
    fun g => (MulAction.mem_stabilizer_iff.symm).trans (burnsideF45_mem_stv_lv_iff' g)
  have D : F45.XDatum S Φ ΓM v₁ v₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hdisj, hnoadj1, hnoadj2, hadj⟩
    · intro a b hab
      apply θ.injective
      apply Subtype.ext
      have := congrArg e hab
      rwa [hΦ, hΦ] at this
    · ext x
      constructor
      · intro hx
        refine ⟨θ.symm ⟨e x, hx⟩, ?_⟩
        apply e.injective
        rw [hΦ]
        simp
      · rintro ⟨y, rfl⟩
        show e (Φ y) ∈ Gp
        rw [hΦ]
        exact (θ y).2
    · intro g
      obtain ⟨n, hn, h, hh, hgnh⟩ := hyp.split (e g)
      refine ⟨θ.symm ⟨n, hn⟩, e.symm h, ?_, ?_, ?_⟩
      · rw [hstabx]
        simpa using hh.1
      · rw [hstabl]
        simpa using hh.2
      · apply e.injective
        rw [map_mul, hΦ, hgnh]
        simp
    · intro y
      rw [hstabx, hΦ]
      exact hstab1 y
    · intro y
      rw [hstabl, hΦ]
      exact hstab2 y
  exact F45.facts45L_of_model D hpoly hn1 hn2 _ _ rfl rfl MB₁ MB₂

end Model

section System

open CFSG.GH74.BNPair CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.BN

variable {κ : GLKind} {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF45_isCoatom_comap {X : Type} [Group X] (φ : X →* E) (hφ : Function.Injective φ)
    {H P : Subgroup E} (hH : φ.range = H) (hPH : P ≤ H) (hne : P ≠ H)
    (hmax : ∀ R : Subgroup E, P < R → R ≤ H → R = H) : IsCoatom (P.comap φ) := by
  have hmapP : (P.comap φ).map φ = P := by
    rw [Subgroup.map_comap_eq, hH, inf_eq_right.mpr hPH]
  refine ⟨fun h => hne ?_, fun R hR => ?_⟩
  · rw [← hmapP, h, ← MonoidHom.range_eq_map, hH]
  · have hR' : P < R.map φ := by
      rw [← hmapP]
      exact (Subgroup.map_lt_map_iff_of_injective hφ).2 hR
    have hRH : R.map φ ≤ H := by
      rw [← hH]
      exact Subgroup.map_le_range φ R
    have h := hmax _ hR' hRH
    rw [eq_top_iff]
    intro x _
    have : φ x ∈ R.map φ := by rw [h, ← hH]; exact ⟨x, rfl⟩
    obtain ⟨y, hy, hyx⟩ := this
    rw [← hφ hyx]
    exact hy

theorem burnsideF45_comap_normalizer {X : Type} [Group X] (φ : X →* E) (hφ : Function.Injective φ)
    {H S : Subgroup E} (hH : φ.range = H) (hSH : S ≤ H) :
    Subgroup.normalizer ((S.comap φ : Subgroup X) : Set X) =
      (H ⊓ Subgroup.normalizer (S : Set E)).comap φ := by
  ext g
  rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have hgH : φ g ∈ H := by rw [← hH]; exact ⟨g, rfl⟩
  refine ⟨fun h => ⟨hgH, fun e => ?_⟩, fun h x => ?_⟩
  · by_cases he : e ∈ H
    · rw [← hH] at he
      obtain ⟨x, rfl⟩ := he
      have := h x
      simp only [Subgroup.mem_comap, map_mul, map_inv] at this
      exact this
    · constructor
      · intro hS
        exact absurd (hSH hS) he
      · intro hS
        exfalso
        apply he
        have h1 : φ g * e * (φ g)⁻¹ ∈ H := hSH hS
        have : e = (φ g)⁻¹ * (φ g * e * (φ g)⁻¹) * φ g := by group
        rw [this]
        exact H.mul_mem (H.mul_mem (H.inv_mem hgH) h1) hgH
  · simp only [Subgroup.mem_comap, map_mul, map_inv]
    exact h.2 (φ x)

theorem burnsideF45_isSylowOf_comap {X : Type} [Group X] (φ : X →* E) (hφ : Function.Injective φ)
    {H S : Subgroup E} (hH : φ.range = H) (hS : IsSylowOf p S H) :
    IsSylowOf p (S.comap φ) ⊤ := by
  obtain ⟨-, hSp, hSidx⟩ := hS
  refine ⟨le_top, hSp.comap_of_injective φ hφ, ?_⟩
  rw [Subgroup.relIndex_top_right, Subgroup.index_comap, hH]
  exact hSidx

theorem burnsideF45_conj_parabolics [Finite E] (hp : p.Prime)
    (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {X : Type} [Group X] (θ₀ : X ≃* ↥Gp) {n : ℕ} (D : RankTwoSystem X n)
    (hU : IsSylowOf p D.U ⊤) :
    ∃ (g : X) (b : Bool), ∀ y : X,
      (((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ M₁ ↔ y ∈ P D b) ∧
      (((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ M₂ ↔ y ∈ P D (!b)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite X := Finite.of_injective _ θ₀.injective
  let φ : X →* E := Gp.subtype.comp θ₀.toMonoidHom
  have hφ : Function.Injective φ := Gp.subtype_injective.comp θ₀.injective
  have hH : φ.range = Gp := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (θ₀ y).2
    · intro hx
      exact ⟨θ₀.symm ⟨x, hx⟩, by simp [φ]⟩
  obtain ⟨⟨S, hS, hB⟩, hne, -, hmax⟩ := hP
  have hS' := burnsideF45_isSylowOf_comap φ hφ hH hS
  have hB' : Subgroup.normalizer ((S.comap φ : Subgroup X) : Set X) =
      (Gp ⊓ (M₁ ⊓ M₂)).comap φ := by
    rw [burnsideF45_comap_normalizer φ hφ hH hS.1, ← hB]
  have hidx : ∀ {T : Subgroup X}, IsSylowOf p T ⊤ → ¬ p ∣ T.index := fun {T} hT => by
    have := hT.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let T₁ : Sylow p X := hS'.2.1.toSylow (hidx hS')
  let T₂ : Sylow p X := hU.2.1.toSylow (hidx hU)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X T₁ T₂
  have hgS : (S.comap φ).map (MulAut.conj g).toMonoidHom = D.U := by
    have h1 : ((g • T₁ : Sylow p X) : Subgroup X) = (T₂ : Subgroup X) := by rw [hg]
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] at h1
    have e0 : ∀ y : X, (MulDistribMulAction.toMonoidEnd (MulAut X) X (MulAut.conj g)) y =
        (MulAut.conj g).toMonoidHom y := fun _ => rfl
    ext x
    have h2 := SetLike.ext_iff.mp h1 x
    simp only [Subgroup.mem_map, e0] at h2 ⊢
    simpa [T₁, T₂] using h2
  have hgB : ((Gp ⊓ (M₁ ⊓ M₂)).comap φ).map (MulAut.conj g).toMonoidHom = D.B := by
    rw [← hB', Subgroup.map_equiv_normalizer_eq, hgS, normalizer_U_eq_B]
  have key : ∀ Q : Subgroup E, Q = Gp ⊓ M₁ ∨ Q = Gp ⊓ M₂ →
      ∃ i : Bool, (Q.comap φ).map (MulAut.conj g).toMonoidHom = P D i := by
    intro Q hPc
    obtain ⟨hBP, hPH, hPne, hPmax⟩ := (hmax Q).2 hPc
    have hco : IsCoatom ((Q.comap φ).map (MulAut.conj g).toMonoidHom) :=
      (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup (MulAut.conj g)) _).2
        (burnsideF45_isCoatom_comap φ hφ hH hPH hPne hPmax)
    have hBle : D.B ≤ (Q.comap φ).map (MulAut.conj g).toMonoidHom := by
      rw [← hgB]
      exact Subgroup.map_mono (Subgroup.comap_mono hBP)
    rcases eq_B_or_P_or_top D hBle with h | ⟨i, h⟩ | h
    · exfalso
      have hlt : D.B < P D true := lt_of_le_of_ne (B_le_P D true) (fun h' => by
        have := not_le_P D true
        apply this
        rw [← h']
        exact B_le_P D false)
      rw [← h] at hlt
      exact P_ne_top D true (hco.2 _ hlt)
    · exact ⟨i, h⟩
    · exact absurd h hco.1
  obtain ⟨b, hb⟩ := key _ (Or.inl rfl)
  obtain ⟨b', hb'⟩ := key _ (Or.inr rfl)
  have hbb : b' = !b := by
    by_contra hcontra
    have hbb' : b' = b := by cases b <;> cases b' <;> simp_all
    apply hne
    have h2 : ((Gp ⊓ M₁).comap φ).map (MulAut.conj g).toMonoidHom =
        ((Gp ⊓ M₂).comap φ).map (MulAut.conj g).toMonoidHom := by rw [hb, hb', hbb']
    have h3 := Subgroup.map_injective (MulAut.conj g).injective h2
    have h4 := congrArg (Subgroup.map φ) h3
    rwa [Subgroup.map_comap_eq, Subgroup.map_comap_eq, hH, inf_eq_right.mpr inf_le_left,
      inf_eq_right.mpr inf_le_left] at h4
  subst hbb
  refine ⟨g, b, fun y => ⟨?_, ?_⟩⟩
  · rw [← hb, Subgroup.mem_map_equiv, Subgroup.mem_comap]
    have e1 : (MulAut.conj g).symm y = g⁻¹ * y * g := by
      simp [MulAut.conj_symm_apply]
    rw [e1]
    show ((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ M₁ ↔ ((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ Gp ⊓ M₁
    exact ⟨fun h => ⟨(θ₀ _).2, h⟩, fun h => h.2⟩
  · rw [← hb', Subgroup.mem_map_equiv, Subgroup.mem_comap]
    have e1 : (MulAut.conj g).symm y = g⁻¹ * y * g := by
      simp [MulAut.conj_symm_apply]
    rw [e1]
    show ((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ M₂ ↔ ((θ₀ (g⁻¹ * y * g) : ↥Gp) : E) ∈ Gp ⊓ M₂
    exact ⟨fun h => ⟨(θ₀ _).2, h⟩, fun h => h.2⟩

theorem burnsideF45_facts45L_of_system (hyp : HypF_4_4 κ p f Gp M₁ M₂) (hp : p.Prime)
    (hm : 3 ≤ κ.m) (hP : IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂))
    {X : Type} [Group X] (θ₀ : X ≃* ↥Gp) {n : ℕ} (D : RankTwoSystem X n) (hn : n = κ.m)
    (hU : IsSylowOf p D.U ⊤)
    (MB : ∀ i : Bool, F45.ModelBase (Γ D) n (v D i)
      (pCoreOf p (MulAction.stabilizer X (v D i)))) :
    (burnsideF45_setting hyp hp hm).Facts45L := by
  haveI : Finite E := hyp.finite
  haveI : Finite X := Finite.of_injective _ θ₀.injective
  obtain ⟨g, b, hgb⟩ := burnsideF45_conj_parabolics hp hP θ₀ D hU
  subst hn
  let θ : X ≃* ↥Gp := (MulAut.conj g).symm.trans θ₀
  have hθ : ∀ y : X, θ y = θ₀ (g⁻¹ * y * g) := fun y => by
    show θ₀ ((MulAut.conj g).symm y) = _
    simp [MulAut.conj_symm_apply]
  have hst : ∀ (i : Bool) (y : X), y ∈ P D i ↔ y • v D i = v D i := fun i y => by
    rw [← stabilizer_v_eq D i, MulAction.mem_stabilizer_iff]
  have hdisj : ∀ (i : Bool) (y z : X), y • v D i ≠ z • v D (!i) := by
    intro i y z
    cases i
    · exact fun h => disj D z y h.symm
    · exact disj D y z
  have hnoadj : ∀ (i : Bool) (y z : X), ¬ (Γ D).Adj (y • v D i) (z • v D i) := by
    intro i
    cases i
    · exact noadj_false D
    · exact noadj_true D
  have hadj : ∀ i : Bool, (Γ D).Adj (v D i) (v D (!i)) := by
    intro i
    cases i
    · exact (adj_v D).symm
    · exact adj_v D
  refine burnsideF45_facts45L_of_model hyp hp hm θ (v₁ := v D b) (v₂ := v D (!b))
    (fun y => by rw [hθ]; exact ((hgb y).1).trans (hst b y))
    (fun y => by rw [hθ]; exact ((hgb y).2).trans (hst (!b) y))
    (hdisj b) (hnoadj b) (hnoadj (!b)) (hadj b) (isGenPolygon D)
    (three_le_card_neighborSet D (v D b)) (three_le_card_neighborSet D (v D (!b))) (MB b)
    (MB (!b))

end System

end CFSG.ASVolI
