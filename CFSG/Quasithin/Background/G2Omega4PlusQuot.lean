module

public import CFSG.Quasithin.Background.G2

public section

namespace CFSG.Quasithin

open scoped Pointwise MatrixGroups commutatorElement

variable {G : Type*} [Group G]

structure QuotSetting (I Sx S₂ : Subgroup G) : Prop where
  S₂_le : S₂ ≤ Sx
  Sx_le : Sx ≤ I
  nS : ∀ x ∈ I, ∀ y ∈ Sx, x * y * x⁻¹ ∈ Sx
  nS₂ : ∀ x ∈ I, ∀ y ∈ S₂, x * y * x⁻¹ ∈ S₂
  abel : ∀ a ∈ Sx, ∀ b ∈ Sx, a * b * a⁻¹ * b⁻¹ ∈ S₂
  sq : ∀ a ∈ Sx, a * a ∈ S₂

namespace QuotSetting

variable {I Sx S₂ : Subgroup G} (Q : QuotSetting I Sx S₂)

include Q

theorem normal : (S₂.subgroupOf Sx).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (fun _ hx => (le_normalizer_of_conj_mem Q.nS₂ : I ≤ Subgroup.normalizer (S₂ : Set G))
      (Q.Sx_le hx))

@[expose] def conjSx (γ : ↥I) : ↥Sx ≃* ↥Sx where
  toFun s := ⟨(γ : G) * s * (γ : G)⁻¹, Q.nS γ γ.2 s s.2⟩
  invFun s := ⟨(γ : G)⁻¹ * s * (γ : G), by
    have := Q.nS ((γ : G)⁻¹) (inv_mem γ.2) s s.2
    simpa using this⟩
  left_inv s := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv s := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjSx_map (γ : ↥I) :
    (S₂.subgroupOf Sx).map ((Q.conjSx γ : ↥Sx ≃* ↥Sx) : ↥Sx →* ↥Sx) = S₂.subgroupOf Sx := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (Q.nS₂ γ γ.2 n (Subgroup.mem_subgroupOf.1 hn))
  · intro hx
    refine ⟨(Q.conjSx γ).symm x, ?_, (Q.conjSx γ).apply_symm_apply x⟩
    have := Q.nS₂ ((γ : G)⁻¹) (inv_mem γ.2) x (Subgroup.mem_subgroupOf.1 hx)
    refine Subgroup.mem_subgroupOf.2 ?_
    show (γ : G)⁻¹ * (x : G) * (γ : G) ∈ S₂
    simpa using this

variable [(S₂.subgroupOf Sx).Normal]

theorem quot_comm (x y : SecQuot Sx S₂) : x * y = y * x := by
  refine QuotientGroup.induction_on x fun a => QuotientGroup.induction_on y fun b => ?_
  show secMk Sx S₂ a * secMk Sx S₂ b = secMk Sx S₂ b * secMk Sx S₂ a
  rw [← map_mul, ← map_mul, secMk_eq_secMk_iff]
  have := Q.abel (b⁻¹ : Sx) (b⁻¹).2 (a⁻¹ : Sx) (a⁻¹).2
  simpa [mul_assoc] using this

theorem quot_sq (x : SecQuot Sx S₂) : x * x = 1 := by
  refine QuotientGroup.induction_on x fun a => ?_
  show secMk Sx S₂ a * secMk Sx S₂ a = 1
  rw [← map_mul, secMk_eq_one_iff]
  exact Q.sq a a.2

abbrev quotCommGroup : CommGroup (SecQuot Sx S₂) :=
  { (inferInstance : Group (SecQuot Sx S₂)) with mul_comm := Q.quot_comm }

@[expose] noncomputable def convAct : ↥I →* MulAut (SecQuot Sx S₂) where
  toFun γ := QuotientGroup.congr (S₂.subgroupOf Sx) (S₂.subgroupOf Sx) (Q.conjSx γ)
    (Q.conjSx_map γ)
  map_one' := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x fun a => ?_
    rw [QuotientGroup.congr_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp [conjSx]
  map_mul' γ δ := by
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x fun a => ?_
    rw [QuotientGroup.congr_mk, MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
    apply congrArg QuotientGroup.mk
    apply Subtype.ext
    simp [conjSx, mul_assoc]

theorem convAct_mk (γ : ↥I) (s : ↥Sx) :
    Q.convAct γ (secMk Sx S₂ s) = secMk Sx S₂ ⟨(γ : G) * s * (γ : G)⁻¹, Q.nS γ γ.2 s s.2⟩ := by
  show QuotientGroup.congr (S₂.subgroupOf Sx) (S₂.subgroupOf Sx) (Q.conjSx γ) (Q.conjSx_map γ)
    (QuotientGroup.mk s) = _
  rw [QuotientGroup.congr_mk]
  rfl

theorem convAct_ker (γ : ↥I) (hγ : (γ : G) ∈ Sx) : Q.convAct γ = 1 := by
  apply MulEquiv.ext
  intro x
  refine QuotientGroup.induction_on x fun a => ?_
  show Q.convAct γ (secMk Sx S₂ a) = secMk Sx S₂ a
  rw [convAct_mk, secMk_eq_secMk_iff]
  have h2 := Q.abel (γ : G) hγ ((a : G)⁻¹) (inv_mem a.2)
  simpa [mul_assoc] using h2

end QuotSetting



@[expose] def IsSumOfNaturalSL2Modules (M Si S S₂ : Subgroup G) : Prop :=
  ∃ (s : ℕ) (β : ↥M →* SL(2, ZMod 2)) (φ : ↥Si →* Multiplicative (Fin s → Fin 2 → ZMod 2)),
    Function.Surjective β ∧ (∀ x : ↥M, β x = 1 ↔ (x : G) ∈ S) ∧
    Function.Surjective φ ∧ (∀ x : ↥Si, φ x = 1 ↔ (x : G) ∈ S₂) ∧
    ∀ (m : ↥M) (x y : ↥Si), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
      φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)

@[expose] def kerSub (I : Subgroup G) (q : ↥I →* SL(2, ZMod 2)) : Subgroup G :=
  q.ker.map I.subtype

theorem mem_kerSub {I : Subgroup G} {q : ↥I →* SL(2, ZMod 2)} {x : G} :
    x ∈ kerSub I q ↔ ∃ h : x ∈ I, q ⟨x, h⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hq⟩
    exact ⟨⟨x, h⟩, hq, rfl⟩

@[expose] def preSub (Sx S₂ : Subgroup G) [(S₂.subgroupOf Sx).Normal]
    (Y₁ : Subgroup (SecQuot Sx S₂)) : Subgroup G :=
  (Y₁.comap (secMk Sx S₂)).map Sx.subtype

theorem mem_preSub {Sx S₂ : Subgroup G} [(S₂.subgroupOf Sx).Normal]
    {Y₁ : Subgroup (SecQuot Sx S₂)} {x : G} :
    x ∈ preSub Sx S₂ Y₁ ↔ ∃ h : x ∈ Sx, secMk Sx S₂ ⟨x, h⟩ ∈ Y₁ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hy⟩
    exact ⟨⟨x, h⟩, hy, rfl⟩


theorem QuotSetting.S₂_le_preSub {I Sx S₂ : Subgroup G} [(S₂.subgroupOf Sx).Normal]
    (Q : QuotSetting I Sx S₂) (Y₁ : Subgroup (SecQuot Sx S₂)) : S₂ ≤ preSub Sx S₂ Y₁ := fun s hs =>
  mem_preSub.2 ⟨Q.S₂_le hs, by
    rw [secMk_eq_one_iff.2 (show ((⟨s, Q.S₂_le hs⟩ : ↥Sx) : G) ∈ S₂ from hs)]
    exact Y₁.one_mem⟩

theorem preSub_le {Sx S₂ : Subgroup G} [(S₂.subgroupOf Sx).Normal]
    (Y₁ : Subgroup (SecQuot Sx S₂)) : preSub Sx S₂ Y₁ ≤ Sx := fun _ hx => (mem_preSub.1 hx).1

structure HalfData {I Sx S₂ : Subgroup G} (Q : QuotSetting I Sx S₂)
    [(S₂.subgroupOf Sx).Normal] (p q : ↥I →* SL(2, ZMod 2))
    (ρA ρB : SL(2, ZMod 2) →* MulAut (SecQuot Sx S₂)) (Y₁ : Subgroup (SecQuot Sx S₂)) : Prop where
  surj : ∀ A : SL(2, ZMod 2), ∃ m : ↥I, p m = A ∧ q m = 1
  surj' : ∀ B : SL(2, ZMod 2), ∃ m : ↥I, p m = 1 ∧ q m = B
  ker : ∀ m : ↥I, (p m = 1 ∧ q m = 1) ↔ (m : G) ∈ Sx
  relA : ∀ m : ↥I, q m = 1 → Q.convAct m = ρA (p m)
  relB : ∀ m : ↥I, p m = 1 → Q.convAct m = ρB (q m)
  iff : ∀ y, y ∈ Y₁ ↔ ∀ B, ρB B y = y
  cl : Y₁ = Subgroup.closure
    {z | ∃ (A : SL(2, ZMod 2)) (y : SecQuot Sx S₂), z = ρA A y * y⁻¹}
  nat : ∃ (s : ℕ) (e : ↥Y₁ ≃* Multiplicative (Fin s → Fin 2 → ZMod 2)),
    ∀ (A : SL(2, ZMod 2)) (x y : ↥Y₁), (y : SecQuot Sx S₂) = ρA A (x : SecQuot Sx S₂) →
      e y = Multiplicative.ofAdd (fun j => A • Multiplicative.toAdd (e x) j)

namespace HalfData

variable {I Sx S₂ : Subgroup G} {Q : QuotSetting I Sx S₂} [(S₂.subgroupOf Sx).Normal]
  {p q : ↥I →* SL(2, ZMod 2)} {ρA ρB : SL(2, ZMod 2) →* MulAut (SecQuot Sx S₂)}
  {Y₁ : Subgroup (SecQuot Sx S₂)} (D : HalfData Q p q ρA ρB Y₁)

include D

theorem comm_le : ⁅Sx, kerSub I q⁆ ≤ preSub Sx S₂ Y₁ := by
  rw [Subgroup.commutator_le]
  intro s hs m hm
  obtain ⟨hmI, hqm⟩ := mem_kerSub.1 hm
  have hrel := D.relA ⟨m, hmI⟩ hqm
  have hcm : (m : G) * s⁻¹ * (m : G)⁻¹ ∈ Sx := Q.nS m hmI s⁻¹ (inv_mem hs)
  have hmem : (s : G) * (m * s⁻¹ * m⁻¹) ∈ Sx := Sx.mul_mem hs hcm
  refine mem_preSub.2 ⟨by simpa [commutatorElement_def, mul_assoc] using hmem, ?_⟩
  have e : (⟨⁅s, m⁆, by simpa [commutatorElement_def, mul_assoc] using hmem⟩ : ↥Sx) =
      ⟨s, hs⟩ * ⟨m * s⁻¹ * m⁻¹, hcm⟩ := by
    apply Subtype.ext
    simp [commutatorElement_def, mul_assoc]
  rw [e, map_mul]
  have h1 : secMk Sx S₂ ⟨m * s⁻¹ * m⁻¹, hcm⟩ = (ρA (p ⟨m, hmI⟩) (secMk Sx S₂ ⟨s, hs⟩))⁻¹ := by
    have h := Q.convAct_mk ⟨m, hmI⟩ ⟨s⁻¹, inv_mem hs⟩
    rw [hrel] at h
    have h2 : secMk Sx S₂ ⟨s⁻¹, inv_mem hs⟩ = (secMk Sx S₂ ⟨s, hs⟩)⁻¹ :=
      (map_inv (secMk Sx S₂) ⟨s, hs⟩).symm
    rw [h2, map_inv] at h
    exact h.symm
  have hgen : ρA (p ⟨m, hmI⟩) (secMk Sx S₂ ⟨s, hs⟩) * (secMk Sx S₂ ⟨s, hs⟩)⁻¹ ∈ Y₁ := by
    rw [D.cl]
    exact Subgroup.subset_closure ⟨p ⟨m, hmI⟩, secMk Sx S₂ ⟨s, hs⟩, rfl⟩
  rw [h1]
  have := Y₁.inv_mem hgen
  rwa [mul_inv_rev, inv_inv] at this

theorem le_comm : preSub Sx S₂ Y₁ ≤ ⁅Sx, kerSub I q⁆ ⊔ S₂ := by
  intro s hs
  obtain ⟨hsSx, hsY⟩ := mem_preSub.1 hs
  set T₀ : Subgroup (SecQuot Sx S₂) := ((⁅Sx, kerSub I q⁆ ⊔ S₂).subgroupOf Sx).map (secMk Sx S₂)
    with hT₀
  have hY₁T₀ : Y₁ ≤ T₀ := by
    rw [D.cl, Subgroup.closure_le]
    rintro z ⟨A, y, rfl⟩
    obtain ⟨t, rfl⟩ := secMk_surjective (A := Sx) (B := S₂) y
    obtain ⟨m, hmp, hmq⟩ := D.surj A
    have hmM : (m : G) ∈ kerSub I q := mem_kerSub.2 ⟨m.2, hmq⟩
    have hrel := D.relA m hmq
    rw [hmp] at hrel
    have hcm : (m : G) * t * (m : G)⁻¹ ∈ Sx := Q.nS m m.2 t t.2
    have hcomm : (m : G) * t * (m : G)⁻¹ * (t : G)⁻¹ ∈ Sx := Sx.mul_mem hcm (inv_mem t.2)
    have hcomm' : (m : G) * t * (m : G)⁻¹ * (t : G)⁻¹ ∈ ⁅Sx, kerSub I q⁆ := by
      have h := Subgroup.commutator_mem_commutator (H₁ := kerSub I q) (H₂ := Sx) hmM t.2
      rw [Subgroup.commutator_comm] at h
      simpa [commutatorElement_def] using h
    refine ⟨⟨_, hcomm⟩, Subgroup.mem_subgroupOf.2 ((le_sup_left : ⁅Sx, kerSub I q⁆ ≤ _) hcomm'), ?_⟩
    have h := Q.convAct_mk m t
    rw [hrel] at h
    show secMk Sx S₂ ⟨(m : G) * t * (m : G)⁻¹ * (t : G)⁻¹, hcomm⟩ = _
    have e : (⟨(m : G) * t * (m : G)⁻¹ * (t : G)⁻¹, hcomm⟩ : ↥Sx) =
        ⟨(m : G) * t * (m : G)⁻¹, hcm⟩ * t⁻¹ := rfl
    rw [e, map_mul, map_inv, ← h]
  obtain ⟨x, hx, hxs⟩ := hY₁T₀ hsY
  have hx' : (x : G) ∈ ⁅Sx, kerSub I q⁆ ⊔ S₂ := Subgroup.mem_subgroupOf.1 hx
  have h2 : ((x : G)⁻¹ * s) ∈ S₂ := by
    have := secMk_eq_secMk_iff.1 hxs
    exact this
  have : s = (x : G) * ((x : G)⁻¹ * s) := by group
  rw [this]
  exact Subgroup.mul_mem _ hx' ((le_sup_right : S₂ ≤ _) h2)

theorem eq_comm_sup : preSub Sx S₂ Y₁ = ⁅Sx, kerSub I q⁆ ⊔ S₂ :=
  le_antisymm D.le_comm (sup_le D.comm_le (Q.S₂_le_preSub Y₁))

theorem mem_iff_comm {s : G} (hs : s ∈ Sx) :
    s ∈ preSub Sx S₂ Y₁ ↔ ∀ m ∈ kerSub I p, ⁅m, s⁆ ∈ S₂ := by
  constructor
  · intro hsa m hm
    obtain ⟨hmI, hpm⟩ := mem_kerSub.1 hm
    obtain ⟨hs', hsY⟩ := mem_preSub.1 hsa
    have hfix := (D.iff _).1 hsY (q ⟨m, hmI⟩)
    have hrel := D.relB ⟨m, hmI⟩ hpm
    rw [← hrel, Q.convAct_mk] at hfix
    have hcm : (m : G) * s * (m : G)⁻¹ ∈ Sx := Q.nS m hmI s hs
    have hfix' : secMk Sx S₂ ⟨(m : G) * s * (m : G)⁻¹, hcm⟩ = secMk Sx S₂ ⟨s, hs⟩ := hfix
    have hc : (m : G) * s * (m : G)⁻¹ * s⁻¹ ∈ Sx := Sx.mul_mem hcm (inv_mem hs)
    have e : (⟨(m : G) * s * (m : G)⁻¹ * s⁻¹, hc⟩ : ↥Sx) =
        ⟨(m : G) * s * (m : G)⁻¹, hcm⟩ * (⟨s, hs⟩ : ↥Sx)⁻¹ := rfl
    have h1 : secMk Sx S₂ ⟨(m : G) * s * (m : G)⁻¹ * s⁻¹, hc⟩ = 1 := by
      rw [e, map_mul, map_inv, hfix', mul_inv_cancel]
    have := secMk_eq_one_iff.1 h1
    simpa [commutatorElement_def] using this
  · intro hcomm
    refine mem_preSub.2 ⟨hs, (D.iff _).2 fun B => ?_⟩
    obtain ⟨m, hmp, hmq⟩ := D.surj' B
    have hmM : (m : G) ∈ kerSub I p := mem_kerSub.2 ⟨m.2, hmp⟩
    have hc := hcomm m hmM
    have hrel := D.relB m hmp
    rw [← hmq, ← hrel, Q.convAct_mk, secMk_eq_secMk_iff]
    have hcs : ((m : G) * s * (m : G)⁻¹ * s⁻¹) ∈ S₂ := by
      simpa [commutatorElement_def] using hc
    have h2 := Q.nS₂ s⁻¹ (inv_mem (Q.Sx_le hs)) _ (S₂.inv_mem hcs)
    have e : ((m : G) * s * (m : G)⁻¹)⁻¹ * s =
        s⁻¹ * ((m : G) * s * (m : G)⁻¹ * s⁻¹)⁻¹ * s⁻¹⁻¹ := by group
    show ((m : G) * s * (m : G)⁻¹)⁻¹ * s ∈ S₂
    rw [e]
    exact h2

theorem natural : IsSumOfNaturalSL2Modules (kerSub I q) (preSub Sx S₂ Y₁) Sx S₂ := by
  obtain ⟨s, e, he⟩ := D.nat
  let toI : ↥(kerSub I q) →* ↥I :=
    { toFun := fun x => ⟨x, (mem_kerSub.1 x.2).1⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let toY : ↥(preSub Sx S₂ Y₁) →* ↥Y₁ :=
    { toFun := fun x => ⟨secMk Sx S₂ ⟨x, (mem_preSub.1 x.2).1⟩, (mem_preSub.1 x.2).2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul (secMk Sx S₂)
        ⟨(a : G), (mem_preSub.1 a.2).1⟩ ⟨(b : G), (mem_preSub.1 b.2).1⟩) }
  refine ⟨s, p.comp toI, e.toMonoidHom.comp toY, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    obtain ⟨m, hmp, hmq⟩ := D.surj A
    exact ⟨⟨m, mem_kerSub.2 ⟨m.2, hmq⟩⟩, hmp⟩
  · intro x
    obtain ⟨hI, hq⟩ := mem_kerSub.1 x.2
    constructor
    · intro hx
      exact (D.ker ⟨x, hI⟩).1 ⟨hx, hq⟩
    · intro hx
      exact ((D.ker ⟨x, hI⟩).2 hx).1
  · intro v
    set y := e.symm v with hy
    obtain ⟨t, ht⟩ := secMk_surjective (A := Sx) (B := S₂) (y : SecQuot Sx S₂)
    have ht' : (t : G) ∈ preSub Sx S₂ Y₁ := mem_preSub.2 ⟨t.2, by
      show secMk Sx S₂ t ∈ Y₁
      rw [ht]
      exact y.2⟩
    refine ⟨⟨t, ht'⟩, ?_⟩
    show e (toY ⟨t, ht'⟩) = v
    have : toY ⟨t, ht'⟩ = y := Subtype.ext ht
    rw [this, hy, e.apply_symm_apply]
  · intro x
    show e (toY x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, Subtype.ext_iff]
    exact secMk_eq_one_iff
  · intro m x y hy
    obtain ⟨hmI, hmq⟩ := mem_kerSub.1 m.2
    have hrel := D.relA ⟨m, hmI⟩ hmq
    have hxSx := (mem_preSub.1 x.2).1
    have hcm := Q.convAct_mk ⟨m, hmI⟩ ⟨x, hxSx⟩
    rw [hrel] at hcm
    have hy' : ((toY y : ↥Y₁) : SecQuot Sx S₂) =
        ρA ((p.comp toI) m) ((toY x : ↥Y₁) : SecQuot Sx S₂) := by
      show secMk Sx S₂ ⟨y, (mem_preSub.1 y.2).1⟩ = ρA (p ⟨m, hmI⟩) (secMk Sx S₂ ⟨x, hxSx⟩)
      rw [hcm]
      congr 1
      exact Subtype.ext hy
    exact he _ _ _ hy'

end HalfData


end CFSG.Quasithin
