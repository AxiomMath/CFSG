module

public import CFSG.Quasithin.Background.B2FactorizationBaumannAux
public import CFSG.Quasithin.Background.B2FactorizationOffender
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B2FactorizationSum

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

universe u

variable {G : Type u} [Group G]

namespace B2F

section Star

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

@[expose] noncomputable def starHom (hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G)) :
    G →* MulAut (IntMod V hV) :=
  (convI hV).comp ((MonoidHom.id G).codRestrict (Subgroup.normalizer (V : Set G)) hN)

variable (hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G))

theorem starHom_eq_one_iff (g : G) :
    starHom hV hN g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) :=
  convI_eq_one_iff hV ⟨g, hN g⟩

theorem mem_autI_iff {K : Subgroup G} {φ : MulAut (IntMod V hV)} :
    φ ∈ autI hV K ↔ ∃ g ∈ K, starHom hV hN g = φ := by
  rw [mem_autI]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.1, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hN g⟩, hg, rfl⟩

end Star

section PartI

variable [Finite G] {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem L_decomp (hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G)) {L I : Subgroup G} (hL : L = pResidualOf 2 (⊤ : Subgroup G))
    (hb : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi L)
    (hLI : autI hV L ≤ autI hV I) :
    ∀ l ∈ L, ∃ i ∈ I, ∃ o ∈ pCoreOf 2 L, l = i * o := by
  set K : Subgroup G := Subgroup.closure {x : G | x ∈ I ∧ Odd (orderOf x)} with hK
  have hKI : K ≤ I := (Subgroup.closure_le I).2 fun x hx => hx.1
  have hLclosure : L = Subgroup.closure {x : G | Odd (orderOf x)} := by
    rw [hL]
    exact pResidualOf_top_eq_closure_odd
  have hKL : K ≤ L := (Subgroup.closure_le L).2 fun x hx => by
    rw [hL]
    exact mem_pResidualOf_top_of_odd hx.2
  have hL' : L ≤ K ⊔ oTwoPhi L := by
    refine hLclosure.le.trans ((Subgroup.closure_le _).2 fun x hx => ?_)
    have hxL : x ∈ L := by
      rw [hL]
      exact mem_pResidualOf_top_of_odd hx
    have hxA : starHom hV hN x ∈ autI hV I := hLI ((mem_autI_iff hV hN).2 ⟨x, hxL, rfl⟩)
    obtain ⟨j, hjI, hjx⟩ := (mem_autI_iff hV hN).1 hxA
    obtain ⟨e, hxe, hje⟩ := exists_odd_pow_eq x j hx
    have hjeK : j ^ e ∈ K := Subgroup.subset_closure ⟨I.pow_mem hjI e, hje⟩
    have hc : (j ^ e)⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
      rw [← starHom_eq_one_iff hV hN, map_mul, map_inv, map_pow, hjx, ← map_pow, hxe,
        inv_mul_cancel]
    have hcL : (j ^ e)⁻¹ * x ∈ L := L.mul_mem (L.inv_mem (hKL hjeK)) hxL
    have hx' : x = j ^ e * ((j ^ e)⁻¹ * x) := by group
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjeK)
      (Subgroup.mem_sup_right (hb ⟨hcL, hc⟩))
  intro l hl
  obtain ⟨k, hk, o, ho, rfl⟩ := exists_mul_of_le_sup_oTwoPhi hKL hL' l hl
  exact ⟨k, hKI hk, o, ho, rfl⟩

end PartI

section PartII

variable [Finite G]

omit [Finite G] in
theorem R_le_normalizer_thompsonJ (R : Subgroup G) :
    R ≤ Subgroup.normalizer (thompsonJ R : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ R)

omit [Finite G] in
theorem exists_cjSub_eq {L R I : Subgroup G} [L.Normal] (hOR : pCoreOf 2 L ≤ R)
    (hdec : ∀ l ∈ L, ∃ i ∈ I, ∃ o ∈ pCoreOf 2 L, l = i * o) :
    ∀ g ∈ L ⊔ R, ∃ i ∈ I, cjSub g (thompsonJ R) = cjSub i (thompsonJ R) := by
  intro g hg
  obtain ⟨l, hl, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hg
  obtain ⟨i, hi, o, ho, rfl⟩ := hdec l hl
  refine ⟨i, hi, ?_⟩
  rw [mul_assoc, cjSub_mul,
    cjSub_eq_of_mem_normalizer (R_le_normalizer_thompsonJ R (R.mul_mem (hOR ho) hr))]

omit [Finite G] in
theorem I_eq_normalClosure {L R I J : Subgroup G} {ι : Type*} (X : ι → Subgroup G)
    (hI : I = ⨆ i, X i) (hJI : J ≤ I) (hXJ : ∀ i, ∃ l ∈ L, cjSub l (X i) ≤ J)
    (hGJ : ∀ g ∈ L ⊔ R, ∃ i ∈ I, cjSub g J = cjSub i J) :
    I = ⨆ g ∈ L ⊔ R, cjSub g J ∧ L ⊔ R ≤ Subgroup.normalizer (I : Set G) := by
  have h1 : I ≤ ⨆ g ∈ L ⊔ R, cjSub g J := by
    rw [hI]
    refine iSup_le fun i => ?_
    obtain ⟨l, hl, hli⟩ := hXJ i
    have h : X i ≤ cjSub l⁻¹ J := by
      have := cjSub_mono (g := l⁻¹) hli
      rwa [cjSub_inv_cjSub] at this
    exact h.trans (le_iSup₂_of_le (f := fun g (_ : g ∈ L ⊔ R) => cjSub g J) l⁻¹
      (Subgroup.mem_sup_left (L.inv_mem hl)) le_rfl)
  have h2 : (⨆ g ∈ L ⊔ R, cjSub g J) ≤ I := by
    refine iSup₂_le fun g hg => ?_
    obtain ⟨i, hi, hgi⟩ := hGJ g hg
    rw [hgi]
    calc cjSub i J ≤ cjSub i I := cjSub_mono hJI
      _ = I := cjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hi)
  have hEq : I = ⨆ g ∈ L ⊔ R, cjSub g J := le_antisymm h1 h2
  refine ⟨hEq, fun h hh => ?_⟩
  have key : ∀ h ∈ L ⊔ R, cjSub h I ≤ I := by
    intro h hh
    calc cjSub h I = cjSub h (⨆ g ∈ L ⊔ R, cjSub g J) := by rw [← hEq]
      _ = ⨆ g ∈ L ⊔ R, cjSub h (cjSub g J) := by
        unfold cjSub
        rw [Subgroup.map_iSup]
        exact iSup_congr fun g => by rw [Subgroup.map_iSup]
      _ ≤ I := iSup₂_le fun g hg => by
        rw [← cjSub_mul]
        have := le_iSup₂_of_le (f := fun g (_ : g ∈ L ⊔ R) => cjSub g J) (h * g)
          ((L ⊔ R).mul_mem hh hg) le_rfl
        rw [← hEq] at this
        exact this
  exact le_normalizer_of_cjSub_le (key h hh) (key h⁻¹ ((L ⊔ R).inv_mem hh))

theorem L_le_I {L R I : Subgroup G} (hL : L = pResidualOf 2 (⊤ : Subgroup G))
    (hOR : pCoreOf 2 L ≤ R) (hdec : ∀ l ∈ L, ∃ i ∈ I, ∃ o ∈ pCoreOf 2 L, l = i * o)
    (hIN : L ⊔ R ≤ Subgroup.normalizer (I : Set G)) : L ≤ I := by
  have hLc : L = Subgroup.closure {x : G | Odd (orderOf x)} := by
    rw [hL]
    exact pResidualOf_top_eq_closure_odd
  refine hLc.le.trans ((Subgroup.closure_le I).2 fun x hx => ?_)
  have hx' : Odd (orderOf x) := hx
  have hxL : x ∈ L := by
    rw [hL]
    exact mem_pResidualOf_top_of_odd hx'
  obtain ⟨i, hi, o, ho, hxio⟩ := hdec x hxL
  have hoN : o ∈ Subgroup.normalizer (I : Set G) := hIN (Subgroup.mem_sup_right (hOR ho))
  have ho2 : ∃ a : ℕ, o ^ 2 ^ a = 1 := by
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨o, ho⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  rw [hxio] at hx' ⊢
  exact mem_of_odd_orderOf_mul hi hoN ho2 hx'

end PartII

section PartIII

variable [Finite G] {V R : Subgroup G} (hV : IsElemAbelian 2 V)

theorem commutator_alpha_le (hVN : V.Normal) {M I : Subgroup G} (hVR : V ≤ R)
    (hRN : R ≤ Subgroup.normalizer (V : Set G))
    (hc : ∀ B, ¬ IsStrongFFStarOffender (autI hV R) B)
    (hM : M ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hI : I = ⨆ g ∈ M, cjSub g (thompsonJ R)) :
    ∀ x ∈ omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))), ∀ i ∈ I,
      x * i * x⁻¹ * i⁻¹ ∈ V := by
  have hfacts := alpha_facts hV hVR hRN hc
  have : V.Normal := hVN
  set Q := R ⊓ Subgroup.centralizer (V : Set G) with hQ
  set α' := omegaOneCenterOf (thompsonJ Q) with hα'
  let π : G →* G ⧸ V := QuotientGroup.mk' V
  have hπ1 : ∀ v : G, π v = 1 ↔ v ∈ V := fun v => QuotientGroup.eq_one_iff v
  have hαM : ∀ g ∈ M, g ∈ Subgroup.normalizer (α' : Set G) := fun g hg =>
    normalizer_le_normalizer_of_map_mulEquiv (F := fun X => omegaOneCenterOf (thompsonJ X))
      (fun φ X => by rw [omegaOneCenterOf_map_mulEquiv, thompsonJ_map_mulEquiv]) Q (hM hg)
  have hJ1 : ∀ x ∈ α', thompsonJ R ≤
      (Subgroup.centralizer ({π x} : Set (G ⧸ V))).comap π := by
    intro x hx
    refine iSup_le fun A => iSup_le fun hA a ha => ?_
    obtain ⟨c, hc', v, hv, hcv⟩ := Subgroup.mem_sup_of_normal_right.1 (hfacts.2.2.2 A hA hx)
    have hπx : π x = π c := by
      rw [← hcv, map_mul, (hπ1 v).2 hv, mul_one]
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh, hπx, ← map_mul, ← map_mul, isElemAbelian_comm hA.2.1 hc'.1 ha]
  let P : Subgroup G := ⨅ x ∈ α', (Subgroup.centralizer ({π x} : Set (G ⧸ V))).comap π
  have hJP : ∀ g ∈ M, cjSub g (thompsonJ R) ≤ P := by
    intro g hg y hy
    simp only [P, Subgroup.mem_iInf]
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hx' : g⁻¹ * x * g ∈ α' := by
      have : x ∈ cjSub g α' := by
        rw [cjSub_eq_of_mem_normalizer (hαM g hg)]
        exact hx
      exact mem_cjSub.1 this
    have hj : g⁻¹ * y * g ∈ thompsonJ R := mem_cjSub.1 hy
    have h1 := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 (hJ1 _ hx' hj)) _ rfl
    calc π x * π y = π g * (π (g⁻¹ * x * g) * π (g⁻¹ * y * g)) * (π g)⁻¹ := by
          simp only [map_mul, map_inv]
          group
      _ = π g * (π (g⁻¹ * y * g) * π (g⁻¹ * x * g)) * (π g)⁻¹ := by rw [h1]
      _ = π y * π x := by
          simp only [map_mul, map_inv]
          group
  have hIP : I ≤ P := by
    rw [hI]
    exact iSup₂_le hJP
  intro x hx i hi
  have h1 := Subgroup.mem_centralizer_iff.1
    (Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (hIP hi) x) hx)) (π x) rfl
  have h2 : π (x * i * x⁻¹ * i⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [h1]
    group
  exact (hπ1 _).1 h2

omit [Finite G] in
theorem mem_normalizer_sup {V α α' I : Subgroup G} (hVN : V.Normal) (hαα' : α ≤ α')
    (hcomm : ∀ x ∈ α', ∀ i ∈ I, x * i * x⁻¹ * i⁻¹ ∈ V) :
    I ≤ Subgroup.normalizer ((α ⊔ V : Subgroup G) : Set G) := by
  have key : ∀ i ∈ I, ∀ w ∈ α ⊔ V, i * w * i⁻¹ ∈ α ⊔ V := by
    intro i hi w hw
    obtain ⟨x, hx, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hw
    have hc : i * x * i⁻¹ * x⁻¹ ∈ V := by
      have := V.inv_mem (hcomm x (hαα' hx) i hi)
      simpa [mul_assoc] using this
    have hv' : i * v * i⁻¹ ∈ V := hVN.conj_mem v hv i
    have h : i * (x * v) * i⁻¹ = (i * x * i⁻¹ * x⁻¹) * x * (i * v * i⁻¹) := by group
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hc)
      (Subgroup.mem_sup_left hx)) (Subgroup.mem_sup_right hv')
  intro i hi
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨key i hi w, fun hw => ?_⟩
  have := key i⁻¹ (I.inv_mem hi) _ hw
  simpa [mul_assoc] using this

end PartIII

section PartIV

variable [Finite G] {V W : Subgroup G} (hV : IsElemAbelian 2 V)

theorem W_decomp (hW : IsElemAbelian 2 W) (hVN : V.Normal) (hVW : V ≤ W) {ι : Type*} [Fintype ι] (X : ι → Subgroup G)
    {I L J : Subgroup G} (hI : I = ⨆ i, X i) (hIW : I ≤ Subgroup.normalizer (W : Set G))
    (hLI : L ≤ I)
    (hd : ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV L)))
    (hX : ∀ i, ∃ g ∈ I, cjSub g (X i) ≤ J)
    (hWJ : W ≤ (W ⊓ Subgroup.centralizer (J : Set G)) ⊔ V) :
    W ⊓ Subgroup.centralizer (L : Set G) = W ⊓ Subgroup.centralizer (I : Set G) ∧
      W = V ⊔ (W ⊓ Subgroup.centralizer (L : Set G)) := by
  have hNV : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hVN]
    exact Subgroup.mem_top g
  have hXI : ∀ i, X i ≤ I := fun i => hI ▸ le_iSup X i
  have hXN : ∀ i, X i ≤ Subgroup.normalizer (W : Set G) := fun i => (hXI i).trans hIW
  have hcommW : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => isElemAbelian_comm hW ha hb
  have hXV : ∀ i, rkIdx (fixV (autI hW (X i))) = rkIdx (fixV (autI hV (X i))) := by
    intro i
    obtain ⟨g, hg, hgX⟩ := hX i
    have e1 := rkIdx_fixV_autI hW (hXN i)
    have e2 := rkIdx_fixV_autI hV (fun x _ => hNV x : X i ≤ Subgroup.normalizer (V : Set G))
    have e4 := rk_inf_centralizer_cjSub (hIW hg) (X i)
    have e5 := rk_inf_centralizer_cjSub (hNV g) (X i)
    have hWY : W = (W ⊓ Subgroup.centralizer (cjSub g (X i) : Set G)) ⊔ V :=
      le_antisymm (hWJ.trans (sup_le_sup_right
        (inf_le_inf_left W (Subgroup.centralizer_le hgX)) V)) (sup_le inf_le_left hVW)
    have e3 := rk_sup_add_rk_inf_of_commute (A := W ⊓ Subgroup.centralizer (cjSub g (X i) : Set G))
      (B := V) (fun a ha b hb => hcommW a ha.1 b (hVW hb))
    have hinf : (W ⊓ Subgroup.centralizer (cjSub g (X i) : Set G)) ⊓ V =
        V ⊓ Subgroup.centralizer (cjSub g (X i) : Set G) := by
      ext x
      simp only [Subgroup.mem_inf]
      exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hVW h.1, h.2⟩, h.1⟩⟩
    rw [← hWY, hinf] at e3
    omega
  have hLNW : L ≤ Subgroup.normalizer (W : Set G) := hLI.trans hIW
  have f1 := rkIdx_fixV_autI hW hLNW
  have f2 := rkIdx_fixV_autI hV (fun x _ => hNV x : L ≤ Subgroup.normalizer (V : Set G))
  have f3 := rk_sup_add_rk_inf_of_commute (A := V) (B := W ⊓ Subgroup.centralizer (L : Set G))
    (fun a ha b hb => hcommW a (hVW ha) b hb.1)
  have f4 : V ⊓ (W ⊓ Subgroup.centralizer (L : Set G)) = V ⊓ Subgroup.centralizer (L : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hVW h.1, h.2⟩⟩
  have f5 : rk ↥(V ⊔ (W ⊓ Subgroup.centralizer (L : Set G))) ≤ rk ↥W :=
    rk_mono (sup_le hVW inf_le_left)
  rw [f4] at f3
  have hsumeq : ∑ i, rkIdx (fixV (autI hW (X i))) = ∑ i, rkIdx (fixV (autI hV (X i))) :=
    Finset.sum_congr rfl fun i _ => hXV i
  have hle2 : rkIdx (fixV (autI hV L)) ≤ rkIdx (fixV (autI hW L)) := by omega
  have hsum : ∑ i, rkIdx (fixV (autI hW (X i))) ≤ rkIdx (fixV (autI hW L)) := by omega
  have hL' : autI hW L ≤ ⨆ i, autI hW (X i) := by
    rw [← autI_iSup hW X hXN]
    exact autI_mono hW (hI ▸ hLI)
  obtain ⟨h17a, h17b⟩ := B2_17_aut (fun v : IntMod W hW => IntMod.sq_eq_one v)
    (fun i => autI hW (X i)) hL' hsum
  rw [← autI_iSup hW X hXN, ← hI] at h17a
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxW, hxL⟩
      refine ⟨hxW, ?_⟩
      have h1 := (mem_fixV_autI hW hLNW (IntMod.mk hW ⟨x, hxW⟩)).2 hxL
      rw [h17a] at h1
      exact (mem_fixV_autI hW hIW (IntMod.mk hW ⟨x, hxW⟩)).1 h1
    · rintro ⟨hxW, hxI⟩
      refine ⟨hxW, ?_⟩
      have h1 := (mem_fixV_autI hW hIW (IntMod.mk hW ⟨x, hxW⟩)).2 hxI
      rw [← h17a] at h1
      exact (mem_fixV_autI hW hLNW (IntMod.mk hW ⟨x, hxW⟩)).1 h1
  · have hEq : rkIdx (fixV (autI hV L)) = rkIdx (fixV (autI hW L)) := by omega
    symm
    refine eq_of_le_of_rk_le_of_isPGroup (isPGroup_of_isElemAbelian hW)
      (sup_le hVW inf_le_left) ?_
    omega

end PartIV

theorem mem_centralizer_sup {x : G} {V₁ V₂ : Subgroup G}
    (h₁ : x ∈ Subgroup.centralizer (V₁ : Set G)) (h₂ : x ∈ Subgroup.centralizer (V₂ : Set G)) :
    x ∈ Subgroup.centralizer ((V₁ ⊔ V₂ : Subgroup G) : Set G) :=
  le_centralizer_sup (D := Subgroup.zpowers x) (Subgroup.zpowers_le.2 h₁)
    (Subgroup.zpowers_le.2 h₂) (Subgroup.mem_zpowers x)

section PartV

variable [Finite G]

theorem isSylowTwoOf_of_isSylowTwoOf_autI {V S A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hSA : S ≤ A) (hS2 : IsPGroup 2 S)
    (h1 : IsSylowTwoOf (S ⊓ Subgroup.centralizer (V : Set G))
      (A ⊓ Subgroup.centralizer (V : Set G)))
    (h2 : IsSylowTwoOf (autI hV S) (autI hV A)) : IsSylowTwoOf S A := by
  refine ⟨hSA, hS2, ?_⟩
  have e1 := card_autI_mul_card_inf hV hAN
  have e2 := card_autI_mul_card_inf hV (hSA.trans hAN)
  have e3 := Subgroup.relIndex_mul_card (autI hV S) (autI hV A)
  rw [inf_eq_left.2 (autI_mono hV hSA)] at e3
  have e4 := Subgroup.relIndex_mul_card (S ⊓ Subgroup.centralizer (V : Set G))
    (A ⊓ Subgroup.centralizer (V : Set G))
  rw [inf_eq_left.2 (inf_le_inf_right _ hSA)] at e4
  have e5 := Subgroup.relIndex_mul_card S A
  rw [inf_eq_left.2 hSA] at e5
  have o1 : ¬ 2 ∣ (autI hV S).relIndex (autI hV A) := h2.2.2
  have o2 : ¬ 2 ∣ (S ⊓ Subgroup.centralizer (V : Set G)).relIndex
      (A ⊓ Subgroup.centralizer (V : Set G)) := h1.2.2
  have hSpos : 0 < Nat.card S := Nat.card_pos
  have key : S.relIndex A = (autI hV S).relIndex (autI hV A) *
      (S ⊓ Subgroup.centralizer (V : Set G)).relIndex (A ⊓ Subgroup.centralizer (V : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hSpos ?_
    calc S.relIndex A * Nat.card S = Nat.card A := e5
      _ = Nat.card (autI hV A) * Nat.card ↥(A ⊓ Subgroup.centralizer (V : Set G)) := e1.symm
      _ = ((autI hV S).relIndex (autI hV A) * Nat.card (autI hV S)) *
          ((S ⊓ Subgroup.centralizer (V : Set G)).relIndex
            (A ⊓ Subgroup.centralizer (V : Set G)) *
            Nat.card ↥(S ⊓ Subgroup.centralizer (V : Set G))) := by rw [e3, e4]
      _ = ((autI hV S).relIndex (autI hV A) *
          (S ⊓ Subgroup.centralizer (V : Set G)).relIndex
            (A ⊓ Subgroup.centralizer (V : Set G))) *
          (Nat.card (autI hV S) * Nat.card ↥(S ⊓ Subgroup.centralizer (V : Set G))) := by ring
      _ = _ * Nat.card S := by rw [e2]
  show ¬ 2 ∣ S.relIndex A
  rw [key]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
  exacts [o1 h, o2 h]

end PartV

end B2F

open B2F in
theorem B2_18 [Finite G] {V L R : Subgroup G} (hV : IsElemAbelian 2 V) (hVN : V.Normal)
    (hL : L = pResidualOf 2 (⊤ : Subgroup G)) (hR : IsPGroup 2 R) (hVR : V ≤ R)
    (ha₁ : pCoreOf 2 L ≤ R ⊓ Subgroup.centralizer (V : Set G))
    (ha₂ : L ≤ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    (hb : L ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoPhi L)
    (hc : ∀ B, ¬ IsStrongFFStarOffender (autI hV R) B)
    (hde : ∃ (n : ℕ) (X : Fin n → Subgroup G),
      (∀ i, ∃ l ∈ L, cjSub l (X i) ≤ R) ∧ (∀ i, X i = thompsonJ (X i)) ∧
      (∀ i, Open.pRank 2 (X i) = Open.pRank 2 R) ∧ autI hV L ≤ ⨆ i, autI hV (X i) ∧
      ∑ i, rkIdx (fixV (autI hV (X i))) ≤ rkIdx (fixV (autI hV L)) ∧
      thompsonJ R ≤ ⨆ i, X i) :
    pCoreOf 2 L ≤ baum R ∧
      omegaOneCenterOf (thompsonJ R) =
        (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
          (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ∧
      (IsSylowTwoOf (R ⊓ Subgroup.centralizer (V : Set G))
          ((L ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) →
        IsSylowTwoOf (baum R ⊓ Subgroup.centralizer (V : Set G))
          ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) ∧
        (IsSylowTwoOf (autI hV (baum R)) (autI hV L ⊔ autI hV (baum R)) →
          IsSylowTwoOf (baum R) (L ⊔ baum R))) := by
  obtain ⟨n, X, hXconj, hXJ, hXrank, hLX, hsum, hJX⟩ := hde
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (V : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top_iff.2 hVN]
    exact Subgroup.mem_top g
  have hRN : R ≤ Subgroup.normalizer (V : Set G) := fun g _ => hN g
  have hLnormal : L.Normal := by
    rw [hL]
    exact normal_pResidualOf_top
  have hOR : pCoreOf 2 L ≤ R := ha₁.trans inf_le_left
  obtain ⟨I, hI⟩ : ∃ I : Subgroup G, I = ⨆ i, X i := ⟨_, rfl⟩
  have hJI : thompsonJ R ≤ I := by
    rw [hI]
    exact hJX
  have hXN : ∀ i, X i ≤ Subgroup.normalizer (V : Set G) := fun i g _ => hN g
  have hLI₀ : autI hV L ≤ autI hV I := by
    rw [hI, autI_iSup hV X hXN]
    exact hLX
  have hdec := L_decomp hV hN hL hb hLI₀
  have hGJ := exists_cjSub_eq (L := L) (R := R) (I := I) hOR hdec
  have hXJ' : ∀ i, ∃ l ∈ L, cjSub l (X i) ≤ thompsonJ R := fun i => by
    obtain ⟨l, hl, hlR⟩ := hXconj i
    exact ⟨l, hl, cjSub_le_thompsonJ (hXJ i) (hXrank i) hlR⟩
  obtain ⟨hIeq, hIN⟩ := I_eq_normalClosure X hI hJI hXJ' hGJ
  have hLI : L ≤ I := L_le_I hL hOR hdec hIN
  have hXg : ∀ i, ∃ g ∈ I, cjSub g (X i) ≤ thompsonJ R := by
    intro i
    obtain ⟨l, hl, hlX⟩ := hXJ' i
    obtain ⟨i', hi', he⟩ := hGJ l⁻¹ (Subgroup.mem_sup_left (L.inv_mem hl))
    refine ⟨i'⁻¹, I.inv_mem hi', ?_⟩
    have h1 : X i ≤ cjSub l⁻¹ (thompsonJ R) := by
      have := cjSub_mono (g := l⁻¹) hlX
      rwa [cjSub_inv_cjSub] at this
    rw [he] at h1
    have := cjSub_mono (g := i'⁻¹) h1
    rwa [cjSub_inv_cjSub] at this
  have hQM : L ⊔ R ≤ Subgroup.normalizer
      ((R ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    sup_le ha₂ (le_normalizer_inf Subgroup.le_normalizer (le_normalizer_centralizer hRN))
  have hcomm := commutator_alpha_le hV hVN hVR hRN hc hQM hIeq
  have hfacts := alpha_facts hV hVR hRN hc
  have hIW : I ≤ Subgroup.normalizer ((omegaOneCenterOf (thompsonJ R) ⊔ V : Subgroup G) : Set G) :=
    mem_normalizer_sup hVN hfacts.2.2.1 hcomm
  have hWQ : omegaOneCenterOf (thompsonJ R) ⊔ V ≤
      omegaOneCenterOf (thompsonJ (R ⊓ Subgroup.centralizer (V : Set G))) :=
    sup_le hfacts.2.2.1 hfacts.2.1
  have hWel : IsElemAbelian 2 (omegaOneCenterOf (thompsonJ R) ⊔ V) :=
    isElemAbelian_mono hWQ (isElemAbelian_omegaOneCenterOf _)
  have hαZ : omegaOneCenterOf (thompsonJ R) ≤ Subgroup.centralizer (thompsonJ R : Set G) :=
    fun x hx => (omegaOneCenterOf_le_centerOf _ hx).2
  have hαJ : omegaOneCenterOf (thompsonJ R) ≤ thompsonJ R :=
    fun x hx => (omegaOneCenterOf_le_centerOf _ hx).1
  have hWJ : omegaOneCenterOf (thompsonJ R) ⊔ V ≤
      ((omegaOneCenterOf (thompsonJ R) ⊔ V) ⊓ Subgroup.centralizer (thompsonJ R : Set G)) ⊔ V :=
    sup_le_sup_right (le_inf le_sup_left hαZ) V
  obtain ⟨hU, hWUV⟩ := W_decomp hV hWel hVN le_sup_right X hI hIW hLI hsum hXg hWJ
  have hWR : omegaOneCenterOf (thompsonJ R) ⊔ V ≤ R :=
    sup_le (hαJ.trans (thompsonJ_le_self R)) hVR
  have hUα : (omegaOneCenterOf (thompsonJ R) ⊔ V) ⊓ Subgroup.centralizer (L : Set G) ≤
      omegaOneCenterOf (thompsonJ R) := by
    intro u hu
    have hu' : u ∈ (omegaOneCenterOf (thompsonJ R) ⊔ V) ⊓ Subgroup.centralizer (I : Set G) :=
      hU ▸ hu
    rw [← (omegaOne_centralizer_thompsonJ R).1]
    exact Subgroup.subset_closure ⟨⟨hWR hu'.1, Subgroup.centralizer_le hJI hu'.2⟩,
      hWel.2 u hu'.1⟩
  have h2 : omegaOneCenterOf (thompsonJ R) =
      (omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G)) ⊔
        (V ⊓ Subgroup.centralizer (thompsonJ R : Set G)) := by
    refine le_antisymm ?_ (sup_le inf_le_left (inf_centralizer_thompsonJ_le hV hVR))
    intro x hx
    have hxW : x ∈ omegaOneCenterOf (thompsonJ R) ⊔ V := Subgroup.mem_sup_left hx
    rw [hWUV, sup_comm] at hxW
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hxW
    have huα : u ∈ omegaOneCenterOf (thompsonJ R) := hUα hu
    have hvα : v ∈ omegaOneCenterOf (thompsonJ R) := by
      have := (omegaOneCenterOf (thompsonJ R)).mul_mem ((omegaOneCenterOf (thompsonJ R)).inv_mem huα) hx
      simpa using this
    exact Subgroup.mul_mem_sup (G := G) ⟨huα, hu.2⟩ ⟨hv, hαZ hvα⟩
  have hLN : L ≤ Subgroup.normalizer (V : Set G) := fun g _ => hN g
  have h1 : pCoreOf 2 L ≤ baum R := by
    intro o ho
    refine ⟨hOR ho, ?_⟩
    have hC1 : pCoreOf 2 L ≤ Subgroup.centralizer
        ((omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
          Set G) := fun o ho =>
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 hy.2 o (pCoreOf_le 2 L ho)).symm
    have hC2 : pCoreOf 2 L ≤ Subgroup.centralizer
        ((V ⊓ Subgroup.centralizer (thompsonJ R : Set G) : Subgroup G) : Set G) := fun o ho =>
      Subgroup.mem_centralizer_iff.2 fun y hy =>
        Subgroup.mem_centralizer_iff.1 (ha₁ ho).2 y hy.1
    have := le_centralizer_sup hC1 hC2
    rw [← h2] at this
    exact this ho
  refine ⟨h1, h2, fun hSyl => ?_⟩
  have hS_le : baum R ≤ R := inf_le_left
  have hRS : R ≤ Subgroup.normalizer (baum R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum R)
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := fun g _ => by
    rw [Subgroup.normalizer_eq_top_iff.2 hLnormal]
    exact Subgroup.mem_top g
  have hclaimA : (R ⊓ Subgroup.centralizer (V : Set G)) ⊓
      ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) =
      baum R ⊓ Subgroup.centralizer (V : Set G) := by
    apply le_antisymm
    · rintro x ⟨⟨hxR, hxC⟩, ⟨hxLS, -⟩⟩
      refine ⟨⟨hxR, ?_⟩, hxC⟩
      obtain ⟨l, hl, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hxLS
      have hT1 : l * s ∈ Subgroup.centralizer
          ((omegaOneCenterOf (thompsonJ R) ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
            Set G) := by
        refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
        have e1 := Subgroup.mem_centralizer_iff.1 hy.2 l hl
        have e2 := Subgroup.mem_centralizer_iff.1 hs.2 y hy.1
        calc y * (l * s) = (y * l) * s := by rw [mul_assoc]
          _ = (l * y) * s := by rw [← e1]
          _ = l * (y * s) := by rw [mul_assoc]
          _ = l * (s * y) := by rw [e2]
          _ = (l * s) * y := by rw [mul_assoc]
      have hT2 : l * s ∈ Subgroup.centralizer
          ((V ⊓ Subgroup.centralizer (thompsonJ R : Set G) : Subgroup G) : Set G) :=
        Subgroup.mem_centralizer_iff.2 fun y hy => Subgroup.mem_centralizer_iff.1 hxC y hy.1
      have := mem_centralizer_sup hT1 hT2
      rwa [← h2] at this
    · exact fun x hx => ⟨⟨hS_le hx.1, hx.2⟩, ⟨Subgroup.mem_sup_right hx.1, hx.2⟩⟩
  have hSN : R ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer
      (((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    inf_le_left.trans (le_normalizer_inf (le_normalizer_sup hRL hRS)
      (le_normalizer_centralizer hRN))
  have hN_le : (L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G) ≤
      (L ⊔ R) ⊓ Subgroup.centralizer (V : Set G) :=
    inf_le_inf_right _ (sup_le_sup_left hS_le L)
  have hsyl : IsSylowTwoOf ((R ⊓ Subgroup.centralizer (V : Set G)) ⊓
      ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)))
      ((L ⊔ baum R) ⊓ Subgroup.centralizer (V : Set G)) :=
    ⟨inf_le_right, hR.to_le (inf_le_left.trans inf_le_left),
      not_two_dvd_relIndex_inf_of_normalizer hSyl.1 hN_le hSyl.2.2 hSN⟩
  rw [hclaimA] at hsyl
  refine ⟨hsyl, fun hSyl2 => ?_⟩
  refine isSylowTwoOf_of_isSylowTwoOf_autI hV (A := L ⊔ baum R) (fun g _ => hN g)
    le_sup_right (hR.to_le hS_le) hsyl ?_
  rwa [autI_sup hV hLN (fun g _ => hN g)]

end CFSG.Quasithin
