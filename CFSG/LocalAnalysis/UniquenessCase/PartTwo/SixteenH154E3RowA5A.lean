module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Table
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private structure s16h_Proj {Q : Type} [CommGroup Q] {k : ℕ} (I : Fin k → Subgroup Q)
    (Λ : Subgroup (MulAut Q)) where
  e : Fin k → Q →* Q
  e_mem : ∀ i x, e i x ∈ I i
  e_self : ∀ i x (hx : x ∈ I i), e i x = x
  e_other : ∀ i j, j ≠ i → ∀ x (hx : x ∈ I j), e i x = 1
  e_prod : ∀ x, ∏ i, e i x = x
  e_equiv : ∀ i, ∀ g ∈ Λ, ∀ x, e i (g x) = g (e i x)

private noncomputable def s16h_mkProj {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hspan : ⨆ i, I i = ⊤)
    (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) :
    s16h_Proj I Λ := by
  classical
  have hcomm : Pairwise fun i j : Fin k => ∀ x y : Q, x ∈ I i → y ∈ I j → Commute x y :=
    fun i j _ x y _ _ => mul_comm x y
  let φ : (∀ i : Fin k, I i) →* Q := Subgroup.noncommPiCoprod hcomm
  have hInd : iSupIndep I := iSupIndep_def.mpr (fun i => disjoint_iff.mpr (hind i))
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (hcomm := hcomm) hInd
  have hφrange : φ.range = ⊤ := by
    rw [Subgroup.noncommPiCoprod_range, hspan]
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hφrange
  let e : (∀ i : Fin k, I i) ≃* Q := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hφprod : ∀ f : (∀ i : Fin k, I i), φ f = ∏ i, (f i : Q) := by
    intro f
    rw [Subgroup.noncommPiCoprod_apply]
    exact Finset.noncommProd_eq_prod _ _
  let ei (i : Fin k) : Q →* I i :=
    (Pi.evalMonoidHom (fun j => I j) i).comp e.symm.toMonoidHom
  let eQ (i : Fin k) : Q →* Q := (I i).subtype.comp (ei i)
  have hmul : ∀ (i : Fin k) (x : Q) (hx : x ∈ I i), e.symm x = Pi.mulSingle i ⟨x, hx⟩ := by
    intro i x hx
    apply e.injective
    rw [e.apply_symm_apply]
    change x = φ (Pi.mulSingle i ⟨x, hx⟩)
    rw [Subgroup.noncommPiCoprod_mulSingle]
  have hself : ∀ (i : Fin k) (x : Q) (hx : x ∈ I i), eQ i x = x := by
    intro i x hx
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)) = x
    rw [hmul i x hx]
    simp
  have hother : ∀ (i j : Fin k), j ≠ i → ∀ (x : Q) (hx : x ∈ I j), eQ i x = 1 := by
    intro i j hij x hx
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)) = 1
    rw [hmul j x hx]
    simp [Pi.mulSingle_eq_of_ne (Ne.symm hij)]
  have hequiv : ∀ (i : Fin k) (g : MulAut Q), g ∈ Λ → ∀ x, eQ i (g x) = g (eQ i x) := by
    intro i g hg x
    have hgPi : ∀ f : (∀ j : Fin k, I j),
        φ (fun j => ⟨g (f j : Q), hstab j g hg (f j : Q) (f j).2⟩) = g (φ f) := by
      intro f
      rw [hφprod, hφprod]
      exact (map_prod (g : Q →* Q) (fun j => (f j : Q)) Finset.univ).symm
    have hsymm : e.symm (g x) =
        fun j => ⟨g ((e.symm x) j : Q), hstab j g hg ((e.symm x) j : Q) ((e.symm x j).2)⟩ := by
      apply e.injective
      rw [e.apply_symm_apply]
      change g x = φ (fun j => ⟨g ((e.symm x) j : Q),
        hstab j g hg ((e.symm x) j : Q) ((e.symm x j).2)⟩)
      rw [hgPi]
      have h2 : φ (e.symm x) = x := e.apply_symm_apply x
      rw [h2]
    change (I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm (g x))) =
      g ((I i).subtype ((Pi.evalMonoidHom (fun j => I j) i) (e.symm x)))
    rw [hsymm]
    rfl
  have hprod : ∀ x : Q, ∏ i : Fin k, eQ i x = x := by
    intro x
    have h : φ (e.symm x) = x := e.apply_symm_apply x
    rw [hφprod] at h
    simpa [eQ, ei] using h
  exact { e := eQ
          e_mem := fun i x => (ei i x).2
          e_self := hself
          e_other := hother
          e_prod := hprod
          e_equiv := hequiv }

private noncomputable def s16h_block {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ) (c : MulAut Q) (i j : Fin k) :
    I j →* I i :=
  MonoidHom.codRestrict ((P.e i).comp (c.toMonoidHom.comp (I j).subtype)) (I i)
    (fun x => P.e_mem i _)

private lemma s16h_block_coe {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ) (c : MulAut Q) (i j : Fin k)
    (x : I j) : ((s16h_block P c i j x : I i) : Q) = P.e i (c (x : Q)) := rfl

private lemma s16h_block_equivariant {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i) {c : MulAut Q}
    (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x)) (i j : Fin k) :
    ∀ g (hg : g ∈ Λ) (x : I j),
      ((s16h_block P c i j ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : I i) : Q) =
        g ((s16h_block P c i j x : I i) : Q) := by
  intro g hg x
  rw [s16h_block_coe, s16h_block_coe, hc g hg (x : Q), P.e_equiv i g hg]

private lemma s16h_hom_zero_or_bij {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {i j : Fin k} (φ : I j →* I i)
    (heq : ∀ g (hg : g ∈ Λ) (x : I j),
      (φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    φ = 1 ∨ Function.Bijective φ := by
  classical
  let K : Subgroup Q := φ.ker.map (I j).subtype
  have hK_le : K ≤ I j := by
    rintro y ⟨a, _, rfl⟩
    exact a.2
  have hK_stable : ∀ g ∈ Λ, ∀ y ∈ K, g y ∈ K := by
    rintro g hg y ⟨a, ha, rfl⟩
    refine Subgroup.mem_map.mpr ⟨⟨g (a : Q), hstab j g hg (a : Q) a.2⟩, ?_, rfl⟩
    have h := heq g hg a
    rw [MonoidHom.mem_ker.mp ha] at h
    exact Subtype.ext (by simpa using h)
  let L : Subgroup Q := φ.range.map (I i).subtype
  have hL_le : L ≤ I i := by
    rintro y ⟨z, _, rfl⟩
    exact z.2
  have hL_stable : ∀ g ∈ Λ, ∀ y ∈ L, g y ∈ L := by
    rintro g hg y ⟨z, hz, rfl⟩
    rcases MonoidHom.mem_range.mp hz with ⟨x, rfl⟩
    exact Subgroup.mem_map.mpr ⟨φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩, ⟨_, rfl⟩,
      heq g hg x⟩
  by_cases hLbot : L = ⊥
  · left
    have hφ1 : φ = 1 := by
      ext x
      have hxL : (I i).subtype (φ x) ∈ L :=
        Subgroup.mem_map.mpr ⟨φ x, ⟨x, rfl⟩, rfl⟩
      rw [hLbot] at hxL
      simpa using hxL
    exact hφ1
  · right
    have hL : L = I i := by
      rcases (hsimple i).2 L hL_stable hL_le with h | h
      · exact absurd h hLbot
      · exact h
    have hφ1_of_K : φ.ker.map (I j).subtype = I j → φ = 1 := by
      intro htop
      ext x
      have hxK : (I j).subtype x ∈ K := by
        change (I j).subtype x ∈ φ.ker.map (I j).subtype
        rw [htop]
        exact x.2
      rcases Subgroup.mem_map.mp hxK with ⟨a, ha, hax⟩
      have ha' : a = x := Subtype.ext hax
      have ha1 : φ a = 1 := by simpa using ha
      rw [← ha', ha1]
      rfl
    have hK : φ.ker = ⊥ := by
      rcases (hsimple j).2 K hK_stable hK_le with hbot | htop
      · rw [← le_bot_iff]
        intro x hx
        have hxK : (I j).subtype x ∈ K := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
        rw [hbot] at hxK
        exact Subtype.ext (by simpa using hxK)
      · exfalso
        apply hLbot
        have hφ1 : φ = 1 := hφ1_of_K htop
        change φ.range.map (I i).subtype = ⊥
        rw [hφ1]
        simp
    refine ⟨(MonoidHom.ker_eq_bot_iff φ).mp hK, ?_⟩
    intro y
    have hy : (y : Q) ∈ L := by
      rw [hL]
      exact y.2
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    rcases MonoidHom.mem_range.mp hz with ⟨x, hx⟩
    exact ⟨x, Subtype.ext (by rw [hx]; exact hzy)⟩

private lemma s16h_endomorphism_id {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {i : Fin k} (φ : I i →* I i) (hbij : Function.Bijective φ)
    (heq : ∀ g (hg : g ∈ Λ) (x : I i),
      (φ ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    φ = MonoidHom.id (I i) := by
  classical
  let ei' : Q →* I i := MonoidHom.codRestrict (P.e i) (I i) (fun x => P.e_mem i x)
  have hei_self : ∀ x (hx : x ∈ I i), ei' x = ⟨x, hx⟩ := by
    intro x hx
    apply Subtype.ext
    exact P.e_self i x hx
  have hei_other : ∀ j, j ≠ i → ∀ x (hx : x ∈ I j), ei' x = 1 := by
    intro j hj x hx
    apply Subtype.ext
    exact P.e_other i j hj x hx
  let f : Q →* Q := (I i).subtype.comp (φ.comp ei')
  have hfcomm : ∀ g ∈ Λ, ∀ x, f (g x) = g (f x) := by
    intro g hg x
    change (φ (ei' (g x)) : Q) = g (φ (ei' x) : Q)
    have h1 : (ei' (g x) : Q) = g (ei' x : Q) := P.e_equiv i g hg x
    have hgx : ei' (g x) = ⟨g (ei' x : Q), hstab i g hg (ei' x : Q) (ei' x).2⟩ :=
      Subtype.ext h1
    rw [hgx]
    exact heq g hg (ei' x)
  have hfmem : ∀ x ∈ I i, f x ∈ I i := fun x _ => (φ (ei' x)).2
  have hfkill : ∀ j, j ≠ i → ∀ x ∈ I j, f x = 1 := by
    intro j hj x hx
    change (φ (ei' x) : Q) = 1
    rw [hei_other j hj x hx, map_one]
    rfl
  rcases hend i f hfcomm hfmem hfkill with hid | hone
  · ext x
    have h := hid (x : Q) x.2
    have h2 : (φ x : Q) = (x : Q) := by
      calc (φ x : Q) = (φ (ei' (x : Q)) : Q) := by rw [hei_self (x : Q) x.2]
        _ = (f (x : Q) : Q) := rfl
        _ = (x : Q) := h
    exact h2
  · exfalso
    have hφ1 : φ = 1 := by
      ext x
      have h := hone (x : Q) x.2
      have h2 : (φ x : Q) = 1 := by
        calc (φ x : Q) = (φ (ei' (x : Q)) : Q) := by rw [hei_self (x : Q) x.2]
          _ = (f (x : Q) : Q) := rfl
          _ = 1 := h
      exact h2
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
    have hx1 : x = 1 := hbij.1 (by rw [hφ1]; rfl)
    exact hxne hx1

private lemma s16h_inv_equivariant {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    {i j : Fin k} (φ : I j →* I i) (hbij : Function.Bijective φ)
    (heq : ∀ g (hg : g ∈ Λ) (x : I j),
      (φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (φ x : Q)) :
    ∀ g (hg : g ∈ Λ) (y : I i),
      (((MulEquiv.ofBijective φ hbij).symm ⟨g (y : Q), hstab i g hg (y : Q) y.2⟩ : I j) : Q) =
        g (((MulEquiv.ofBijective φ hbij).symm y : I j) : Q) := by
  intro g hg y
  let Φ : I j ≃* I i := MulEquiv.ofBijective φ hbij
  change ((Φ.symm ⟨g (y : Q), hstab i g hg (y : Q) y.2⟩ : I j) : Q) =
    g ((Φ.symm y : I j) : Q)
  rw [show g ((Φ.symm y : I j) : Q) =
      ((⟨g ((Φ.symm y : I j) : Q), hstab j g hg ((Φ.symm y : I j) : Q) (Φ.symm y).2⟩ :
        I j) : Q) from rfl]
  apply congrArg (fun z : I j => (z : Q))
  apply hbij.1
  change Φ (Φ.symm ⟨g (y : Q), hstab i g hg (y : Q) y.2⟩) =
    Φ ⟨g ((Φ.symm y : I j) : Q), hstab j g hg ((Φ.symm y : I j) : Q) (Φ.symm y).2⟩
  rw [Φ.apply_symm_apply]
  apply Subtype.ext
  change (g (y : Q)) = ((φ ⟨g ((Φ.symm y : I j) : Q),
    hstab j g hg ((Φ.symm y : I j) : Q) (Φ.symm y).2⟩ : I i) : Q)
  have h2 : φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [heq g hg (Φ.symm y), h2]

private lemma s16h_bijective_unique {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {i j : Fin k} (φ ψ : I j →* I i)
    (hφ : Function.Bijective φ) (hψ : Function.Bijective ψ)
    (hφe : ∀ g (hg : g ∈ Λ) (x : I j),
      (φ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (φ x : Q))
    (hψe : ∀ g (hg : g ∈ Λ) (x : I j),
      (ψ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (ψ x : Q)) :
    φ = ψ := by
  classical
  by_cases hij : i = j
  · subst hij
    rw [s16h_endomorphism_id P hstab hsimple hend φ hφ hφe,
      s16h_endomorphism_id P hstab hsimple hend ψ hψ hψe]
  · let Φ : I j ≃* I i := MulEquiv.ofBijective φ hφ
    let Ψ : I j ≃* I i := MulEquiv.ofBijective ψ hψ
    let τ : I j ≃* I j := Ψ.trans Φ.symm
    have hτbij : Function.Bijective τ := τ.bijective
    have hτe : ∀ g (hg : g ∈ Λ) (x : I j),
        (τ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : Q) = g (τ x : Q) := by
      intro g hg x
      change ((Φ.symm (Ψ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩) : I j) : Q) =
        g ((Φ.symm (Ψ x) : I j) : Q)
      have h1 : Ψ ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ =
          ⟨g (Ψ x : Q), hstab i g hg (Ψ x : Q) (Ψ x).2⟩ :=
        Subtype.ext (hψe g hg x)
      rw [h1]
      exact s16h_inv_equivariant hstab φ hφ hφe g hg (Ψ x)
    have hτid : τ.toMonoidHom = MonoidHom.id (I j) :=
      s16h_endomorphism_id P hstab hsimple hend τ.toMonoidHom hτbij hτe
    ext x
    have hx : (Φ.symm (Ψ x) : I j) = x := by
      have := congrArg (fun f : I j →* I j => f x) hτid
      simpa [τ] using this
    have h2 : Ψ x = Φ x := by
      calc Ψ x = Φ (Φ.symm (Ψ x)) := (Φ.apply_symm_apply (Ψ x)).symm
        _ = Φ x := by rw [hx]
    exact congrArg (fun z : I i => (z : Q)) h2.symm

private lemma s16h_block_one_or_bij {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {c : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x)) (i j : Fin k) :
    s16h_block P c i j = 1 ∨ Function.Bijective (s16h_block P c i j) :=
  s16h_hom_zero_or_bij hstab hsimple _ (s16h_block_equivariant P hstab hc i j)

private noncomputable def s16h_comp_block {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ) (c c' : MulAut Q)
    (i l j : Fin k) : I j →* I i :=
  (s16h_block P c i l).comp (s16h_block P c' l j)

private lemma s16h_comp_block_bijective {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ) {c c' : MulAut Q}
    (i l j : Fin k) (h1 : Function.Bijective (s16h_block P c i l))
    (h2 : Function.Bijective (s16h_block P c' l j)) :
    Function.Bijective (s16h_comp_block P c c' i l j) := h1.comp h2

private lemma s16h_comp_block_equivariant {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    {c c' : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x))
    (hc' : ∀ g ∈ Λ, ∀ x, c' (g x) = g (c' x)) (i l j : Fin k) :
    ∀ g (hg : g ∈ Λ) (x : I j),
      ((s16h_comp_block P c c' i l j ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ : I i) : Q) =
        g ((s16h_comp_block P c c' i l j x : I i) : Q) := by
  intro g hg x
  have h2 := s16h_block_equivariant P hstab hc' l j g hg x
  have h2' : s16h_block P c' l j ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩ =
      ⟨g ((s16h_block P c' l j x : I l) : Q),
        hstab l g hg ((s16h_block P c' l j x : I l) : Q) (s16h_block P c' l j x).2⟩ :=
    Subtype.ext h2
  change ((s16h_block P c i l (s16h_block P c' l j
    ⟨g (x : Q), hstab j g hg (x : Q) x.2⟩) : I i) : Q) =
    g ((s16h_block P c i l (s16h_block P c' l j x) : I i) : Q)
  rw [h2']
  exact s16h_block_equivariant P hstab hc i l g hg (s16h_block P c' l j x)

private lemma s16h_block_prod_formula {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ) (c c' : MulAut Q)
    (i j : Fin k) (x : I j) :
    ((s16h_block P (c * c') i j x : I i) : Q) =
      ∏ l : Fin k, ((s16h_block P c i l (s16h_block P c' l j x) : I i) : Q) := by
  calc
    ((s16h_block P (c * c') i j x : I i) : Q) = P.e i ((c * c') (x : Q)) := rfl
    _ = P.e i (c (c' (x : Q))) := rfl
    _ = P.e i (c (∏ l : Fin k, P.e l (c' (x : Q)))) := by
      rw [P.e_prod (c' (x : Q))]
    _ = P.e i (∏ l : Fin k, c (P.e l (c' (x : Q)))) := by
      congr 1
      exact map_prod (c : Q →* Q) (fun l => P.e l (c' (x : Q))) Finset.univ
    _ = ∏ l : Fin k, P.e i (c (P.e l (c' (x : Q)))) := by
      exact map_prod (P.e i) (fun l => c (P.e l (c' (x : Q)))) Finset.univ
    _ = ∏ l : Fin k, ((s16h_block P c i l (s16h_block P c' l j x) : I i) : Q) := by
      apply Finset.prod_congr rfl
      intro l _
      rfl

private lemma s16h_pow_even {G : Type} [Group G] {y : G} (hy : y ^ 2 = 1) (m : ℕ) :
    y ^ (2 * m) = 1 := by
  rw [pow_mul, hy, one_pow]

private lemma s16h_pow_odd {G : Type} [Group G] {y : G} (hy : y ^ 2 = 1) (m : ℕ) :
    y ^ (2 * m + 1) = y := by
  rw [pow_succ, s16h_pow_even hy, one_mul]

private noncomputable def s16h_matrix {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ) (c : MulAut Q) :
    Matrix (Fin k) (Fin k) (ZMod 2) := by
  classical
  exact Matrix.of fun i j => if s16h_block P c i j = 1 then 0 else 1

private lemma s16h_matrix_one {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i) :
    s16h_matrix P 1 = 1 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    have hblock : s16h_block P (1 : MulAut Q) i i = MonoidHom.id (I i) := by
      ext x
      rw [s16h_block_coe P (1 : MulAut Q) i i x]
      simpa using P.e_self i (x : Q) x.2
    have hne : s16h_block P (1 : MulAut Q) i i ≠ 1 := by
      intro h1
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
      have h := congrArg (fun f : I i →* I i => f x) h1
      have hx' : (x : I i) = 1 := by simpa [hblock] using h
      exact hx hx'
    rw [s16h_matrix, Matrix.of_apply, if_neg hne, Matrix.one_apply_eq]
  · have h1 : s16h_block P (1 : MulAut Q) i j = 1 := by
      ext x
      rw [s16h_block_coe P (1 : MulAut Q) i j x, MulAut.one_apply]
      rw [P.e_other i j (Ne.symm hij) (x : Q) x.2, MonoidHom.one_apply]
      rfl
    rw [s16h_matrix, Matrix.of_apply, if_pos h1, Matrix.one_apply_ne hij]

private lemma s16h_block_mul_eq_one_iff {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {c c' : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x))
    (hc' : ∀ g ∈ Λ, ∀ x, c' (g x) = g (c' x)) (i j : Fin k) :
    s16h_block P (c * c') i j = 1 ↔
      Even (@Finset.filter (Fin k) (fun l =>
        s16h_block P c i l ≠ 1 ∧ s16h_block P c' l j ≠ 1)
        (fun l => Classical.dec _) Finset.univ).card := by
  classical
  let S : Finset (Fin k) :=
    @Finset.filter (Fin k) (fun l => s16h_block P c i l ≠ 1 ∧ s16h_block P c' l j ≠ 1)
      (fun l => Classical.dec _) Finset.univ
  have hmemS : ∀ l, l ∈ S ↔ s16h_block P c i l ≠ 1 ∧ s16h_block P c' l j ≠ 1 := by
    intro l
    simp [S]
  have hcomp_bij : ∀ l ∈ S, Function.Bijective (s16h_comp_block P c c' i l j) := by
    intro l hl
    rw [hmemS] at hl
    have hb1 := (s16h_block_one_or_bij P hstab hsimple hc i l).resolve_left hl.1
    have hb2 := (s16h_block_one_or_bij P hstab hsimple hc' l j).resolve_left hl.2
    exact s16h_comp_block_bijective P i l j hb1 hb2
  have hterm_out : ∀ (x : I j) (l : Fin k), l ∉ S →
      ((s16h_comp_block P c c' i l j x : I i) : Q) = 1 := by
    intro x l hl
    by_cases h1 : s16h_block P c i l = 1
    · simp [s16h_comp_block, h1]
    · have h2 : s16h_block P c' l j = 1 := by
        by_contra h2
        exact hl (by rw [hmemS]; exact ⟨h1, h2⟩)
      simp [s16h_comp_block, h2]
  have hprod_subset : ∀ x : I j,
      (∏ l : Fin k, ((s16h_comp_block P c c' i l j x : I i) : Q)) =
        ∏ l ∈ S, ((s16h_comp_block P c c' i l j x : I i) : Q) := by
    intro x
    symm
    exact Finset.prod_subset (Finset.subset_univ S) (fun l _ hl => hterm_out x l hl)
  constructor
  · intro hblock
    by_contra hne
    have hodd : Odd S.card := Nat.not_even_iff_odd.mp hne
    have hSpos : 0 < S.card := by
      rcases hodd with ⟨m, hm⟩
      omega
    obtain ⟨l0, hl0⟩ := Finset.card_pos.mp hSpos
    have hterm_eq : ∀ (x : I j) (l : Fin k), l ∈ S →
        ((s16h_comp_block P c c' i l j x : I i) : Q) =
          ((s16h_comp_block P c c' i l0 j x : I i) : Q) := by
      intro x l hl
      have hcomp_eq : s16h_comp_block P c c' i l j =
          s16h_comp_block P c c' i l0 j :=
        s16h_bijective_unique P hstab hsimple hend _ _ (hcomp_bij l hl) (hcomp_bij l0 hl0)
          (s16h_comp_block_equivariant P hstab hc hc' i l j)
          (s16h_comp_block_equivariant P hstab hc hc' i l0 j)
      rw [hcomp_eq]
    have hcomp1 : s16h_comp_block P c c' i l0 j = 1 := by
      ext x
      have hprod1 : (∏ l : Fin k, ((s16h_comp_block P c c' i l j x : I i) : Q)) = 1 := by
        change (∏ l : Fin k, ((s16h_block P c i l (s16h_block P c' l j x) : I i) : Q)) = 1
        rw [← s16h_block_prod_formula P c c' i j x]
        exact congrArg (fun z : I i => (z : Q))
          (by simpa using congrArg (fun f : I j →* I i => f x) hblock)
      have hpow : (∏ l ∈ S, ((s16h_comp_block P c c' i l j x : I i) : Q)) =
          ((s16h_comp_block P c c' i l0 j x : I i) : Q) ^ S.card := by
        apply Finset.prod_eq_pow_card
        intro l hl
        exact hterm_eq x l hl
      rw [hprod_subset x, hpow] at hprod1
      rcases hodd with ⟨m, hm⟩
      rw [hm, s16h_pow_odd (hQ _) m] at hprod1
      exact hprod1
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple j).1
    have hx1 : x = 1 := (hcomp_bij l0 hl0).1 (by rw [hcomp1]; rfl)
    exact hx hx1
  · intro heven
    by_cases hS : S.Nonempty
    · obtain ⟨l0, hl0⟩ := hS
      have hterm_eq : ∀ (x : I j) (l : Fin k), l ∈ S →
          ((s16h_comp_block P c c' i l j x : I i) : Q) =
            ((s16h_comp_block P c c' i l0 j x : I i) : Q) := by
        intro x l hl
        have hcomp_eq : s16h_comp_block P c c' i l j =
            s16h_comp_block P c c' i l0 j :=
          s16h_bijective_unique P hstab hsimple hend _ _ (hcomp_bij l hl) (hcomp_bij l0 hl0)
            (s16h_comp_block_equivariant P hstab hc hc' i l j)
            (s16h_comp_block_equivariant P hstab hc hc' i l0 j)
        rw [hcomp_eq]
      ext x
      have hpow : (∏ l ∈ S, ((s16h_comp_block P c c' i l j x : I i) : Q)) =
          ((s16h_comp_block P c c' i l0 j x : I i) : Q) ^ S.card := by
        apply Finset.prod_eq_pow_card
        intro l hl
        exact hterm_eq x l hl
      rw [s16h_block_prod_formula P c c' i j x]
      change (∏ l : Fin k, ((s16h_comp_block P c c' i l j x : I i) : Q)) = (1 : Q)
      rw [hprod_subset x, hpow]
      rcases heven with ⟨m, hm⟩
      rw [hm]
      simpa only [two_mul] using s16h_pow_even (hQ _) m
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      ext x
      rw [s16h_block_prod_formula P c c' i j x]
      change (∏ l : Fin k, ((s16h_comp_block P c c' i l j x : I i) : Q)) = (1 : Q)
      rw [hprod_subset x, hSempty]
      simp

private lemma s16h_matrix_mul {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {c c' : MulAut Q} (hc : ∀ g ∈ Λ, ∀ x, c (g x) = g (c x))
    (hc' : ∀ g ∈ Λ, ∀ x, c' (g x) = g (c' x)) :
    s16h_matrix P (c * c') = s16h_matrix P c * s16h_matrix P c' := by
  classical
  ext i j
  simp only [s16h_matrix, Matrix.of_apply, Matrix.mul_apply]
  let S : Finset (Fin k) :=
    @Finset.filter (Fin k) (fun l =>
      s16h_block P c i l ≠ 1 ∧ s16h_block P c' l j ≠ 1)
      (fun l => Classical.dec _) Finset.univ
  have hS : ∀ l, l ∈ S ↔ s16h_block P c i l ≠ 1 ∧ s16h_block P c' l j ≠ 1 := by
    simp [S]
  have hterm : ∀ l : Fin k,
      (if s16h_block P c i l = 1 then 0 else 1) *
        (if s16h_block P c' l j = 1 then 0 else 1) =
        (if l ∈ S then (1 : ZMod 2) else 0) := by
    intro l
    by_cases h : l ∈ S
    · rw [if_pos h]
      obtain ⟨h1, h2⟩ := (hS l).mp h
      simp [h1, h2]
    · rw [if_neg h]
      have h' : ¬ (s16h_block P c i l ≠ 1 ∧ s16h_block P c' l j ≠ 1) :=
        fun hc => h ((hS l).mpr hc)
      simp only [not_and_or, not_not] at h'
      rcases h' with h1 | h2
      · simp [h1]
      · simp [h2]
  have hsum : (∑ l : Fin k, (if s16h_block P c i l = 1 then 0 else 1) *
      (if s16h_block P c' l j = 1 then 0 else 1)) = ((S.card : ℕ) : ZMod 2) := by
    rw [Finset.sum_congr rfl (fun l _ => hterm l)]
    simp [Finset.sum_ite_mem]
  rw [hsum, s16h_block_mul_eq_one_iff hQ P hstab hsimple hend hc hc' i j]
  by_cases he : Even S.card
  · rw [if_pos he, ZMod.natCast_eq_zero_iff_even.mpr he]
  · rw [if_neg he, ZMod.natCast_eq_one_iff_odd.mpr (Nat.not_even_iff_odd.mp he)]

private lemma s16h_cent_comm {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {c : MulAut Q} (hc : c ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) :
    ∀ g ∈ Λ, ∀ x, c (g x) = g (c x) := by
  intro g hg x
  have h := Subgroup.mem_centralizer_iff.mp hc g hg
  exact (congrArg (fun f : MulAut Q => f x) h).symm

private noncomputable def s16h_matrixHom {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1)) :
    Subgroup.centralizer (Λ : Set (MulAut Q)) →* GL (Fin k) (ZMod 2) where
  toFun c :=
    { val := s16h_matrix P (c : MulAut Q)
      inv := s16h_matrix P ((c : MulAut Q)⁻¹)
      val_inv := by
        rw [← s16h_matrix_mul hQ P hstab hsimple hend (s16h_cent_comm c.2)
          (s16h_cent_comm (Subgroup.inv_mem _ c.2))]
        simp [s16h_matrix_one P hsimple]
      inv_val := by
        rw [← s16h_matrix_mul hQ P hstab hsimple hend
          (s16h_cent_comm (Subgroup.inv_mem _ c.2)) (s16h_cent_comm c.2)]
        simp [s16h_matrix_one P hsimple] }
  map_one' := by
    apply Units.ext
    exact s16h_matrix_one P hsimple
  map_mul' := fun c c' => by
    apply Units.ext
    rw [Units.val_mul]
    exact s16h_matrix_mul hQ P hstab hsimple hend (s16h_cent_comm c.2) (s16h_cent_comm c'.2)

private lemma s16h_matrixHom_eq_one {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    {c : MulAut Q} (hc : c ∈ Subgroup.centralizer (Λ : Set (MulAut Q)))
    (hM : s16h_matrix P c = 1) : c = 1 := by
  classical
  have hc' := s16h_cent_comm hc
  have hdiag : ∀ i, s16h_block P c i i = MonoidHom.id (I i) := by
    intro i
    have hne : s16h_block P c i i ≠ 1 := by
      intro h1
      have h2 : (s16h_matrix P c) i i = 0 := by
        simp [s16h_matrix, h1]
      have h3 : (s16h_matrix P c) i i = 1 := by
        rw [hM, Matrix.one_apply_eq]
      rw [h2] at h3
      exact zero_ne_one h3
    rcases s16h_block_one_or_bij P hstab hsimple hc' i i with h1 | hbij
    · exact absurd h1 hne
    · exact s16h_endomorphism_id P hstab hsimple hend _ hbij
        (s16h_block_equivariant P hstab hc' i i)
  have hoff : ∀ i j, i ≠ j → s16h_block P c i j = 1 := by
    intro i j hij
    by_contra h1
    have h2 : (s16h_matrix P c) i j = 1 := by
      simp [s16h_matrix, h1]
    have h3 : (s16h_matrix P c) i j = 0 := by
      rw [hM]
      exact Matrix.one_apply_ne hij
    rw [h2] at h3
    exact one_ne_zero h3
  ext x
  have h_on : ∀ i (y : I i), c (y : Q) = (y : Q) := by
    intro i y
    calc c (y : Q) = ∏ l : Fin k, P.e l (c (y : Q)) := (P.e_prod (c (y : Q))).symm
      _ = ∏ l : Fin k, P.e l (y : Q) := by
        apply Finset.prod_congr rfl
        intro l _
        by_cases hli : l = i
        · subst hli
          have h := congrArg (fun f : I l →* I l => f y) (hdiag l)
          rw [show P.e l (c (y : Q)) = (s16h_block P c l l y : Q) from
            (s16h_block_coe P c l l y).symm]
          rw [show P.e l (y : Q) = (y : Q) from P.e_self l (y : Q) y.2]
          exact congrArg (fun z : I l => (z : Q)) h
        · have h := congrArg (fun f : I i →* I l => f y) (hoff l i hli)
          have h1 : P.e l (c (y : Q)) = 1 := by
            rw [show P.e l (c (y : Q)) = (s16h_block P c l i y : Q) from
              (s16h_block_coe P c l i y).symm]
            exact congrArg (fun z : I l => (z : Q)) h
          have h2 : P.e l (y : Q) = 1 := P.e_other l i (Ne.symm hli) (y : Q) y.2
          rw [h1, h2]
      _ = (y : Q) := P.e_prod y
  calc c x = c (∏ i : Fin k, P.e i x) := by rw [P.e_prod x]
    _ = ∏ i : Fin k, c (P.e i x) := by rw [map_prod]
    _ = ∏ i : Fin k, P.e i x := by
      apply Finset.prod_congr rfl
      intro i _
      exact h_on i ⟨P.e i x, P.e_mem i x⟩
    _ = x := P.e_prod x

private lemma s16h_matrixHom_injective {Q : Type} [CommGroup Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q} (P : s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
      (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1)) :
    Function.Injective (s16h_matrixHom hQ P hstab hsimple hend) := by
  intro c c' hcc'
  have h : (s16h_matrixHom hQ P hstab hsimple hend) (c * c'⁻¹) = 1 := by
    rw [map_mul, map_inv, hcc', mul_inv_cancel]
  have h' : s16h_matrix P ((c * c'⁻¹ : Subgroup.centralizer (Λ : Set (MulAut Q))) : MulAut Q) = 1 :=
    congrArg Units.val h
  have h2 := s16h_matrixHom_eq_one hQ P hstab hsimple hend (c * c'⁻¹).2 h'
  have h3 : c * c'⁻¹ = 1 := Subtype.ext h2
  rw [mul_inv_eq_one] at h3
  exact h3

private lemma s16h_prime_dvd_168 {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (h : q ∣ 168) :
    q = 3 ∨ q = 7 := by
  have h168 : (168 : ℕ) = 2 ^ 3 * 3 * 7 := by norm_num
  rw [h168] at h
  rcases hq.dvd_mul.mp h with h1 | h7
  · rcases hq.dvd_mul.mp h1 with h2 | h3
    · have h2' : q ∣ 2 := hq.dvd_of_dvd_pow h2
      have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2'
      exact absurd this hq2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 3)).mp h3)
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq (by norm_num : Nat.Prime 7)).mp h7)


private theorem s16h_sum_cent_card_dvd {Q : Type} [CommGroup Q] [Finite Q] (hQ : ∀ x : Q, x ^ 2 = 1)
    {Λ : Subgroup (MulAut Q)} {k : ℕ} (hk : k ≤ 3) {I : Fin k → Subgroup Q}
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, (∀ g ∈ Λ, ∀ x ∈ J, g x ∈ J) → J ≤ I i →
      J = ⊥ ∨ J = I i)
    (hend : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hspan : ⨆ i, I i = ⊤) (hind : ∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {F : Subgroup (MulAut Q)}
    (hF : F ≤ Subgroup.centralizer (Λ : Set (MulAut Q))) (hFe : IsElemAbelian q F) :
    Nat.card F ∣ Nat.card (GL (Fin k) (ZMod 2)) := by
  classical
  let P := s16h_mkProj hstab hspan hind
  let M := s16h_matrixHom hQ P hstab hsimple hend
  let φ : F →* GL (Fin k) (ZMod 2) := M.comp (Subgroup.inclusion hF)
  have hφ_inj : Function.Injective φ :=
    (s16h_matrixHom_injective hQ P hstab hsimple hend).comp
      (Subgroup.inclusion_injective hF)
  exact card_dvd_of_injective φ hφ_inj

variable {W : Type} [CommGroup W]

private theorem s16h_sum_cent_sec_dvd [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hN : ∀ I : Subgroup W, N L I Z → s16h_SimpleScalar L I Z) {k : ℕ} (hk : k ≤ 3)
    (hS : SumOfNat N L U Z k) (hLU : L ≤ stabSub U) (hLZ : L ≤ stabSub Z)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {F : Subgroup (MulAut (Sec U Z))}
    (hF : F ≤ Subgroup.centralizer (autSec L U Z : Set (MulAut (Sec U Z))))
    (hFe : IsElemAbelian q F) :
    Nat.card F ∣ Nat.card (GL (Fin k) (ZMod 2)) := by
  classical
  obtain ⟨I, hZI, hind, hspan, hNi⟩ := hS
  have hIU : ∀ i, I i ≤ U := fun i => (le_iSup I i).trans (le_sup_right.trans_eq hspan)
  have hss : ∀ i, s16h_SimpleScalar L (I i) Z := fun i => hN (I i) (hNi i)
  have hLI : ∀ i, L ≤ stabSub (I i) := fun i => s16h_le_stabSub_of_stable (hss i).1.2.1
  let Ī : Fin k → Subgroup (Sec U Z) := fun i =>
    (I i).subgroupOf U |>.map (QuotientGroup.mk' (Z.subgroupOf U))
  have hmapZ : (Z.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hQ : ∀ x : Sec U Z, x ^ 2 = 1 := by
    intro x
    obtain ⟨u, rfl⟩ := (QuotientGroup.mk'_surjective (N := Z.subgroupOf U)) x
    have h2 : u ^ 2 = 1 := Subtype.ext (by simpa using hW (u : W))
    have h3 := congrArg (QuotientGroup.mk' (Z.subgroupOf U)) h2
    simpa [map_pow] using h3
  have hstab : ∀ i, ∀ g ∈ autSec L U Z, ∀ x ∈ Ī i, g x ∈ Ī i := fun i =>
    s16h_secIncl_image_stable Z (I i) U (hIU i) (hLI i) hLZ hLU
  have hsimple : ∀ i, Ī i ≠ ⊥ ∧ ∀ J : Subgroup (Sec U Z),
      (∀ g ∈ autSec L U Z, ∀ x ∈ J, g x ∈ J) → J ≤ Ī i → J = ⊥ ∨ J = Ī i := by
    intro i
    refine ⟨?_, fun J hJstab hJle =>
      s16h_secIncl_simple Z (I i) U (hZI i) (hIU i) (hLI i) hLZ hLU (hss i).1 J hJstab hJle⟩
    intro hbot
    obtain ⟨x, hxI, hxZ⟩ := IsConcreteLE.exists_of_lt (hss i).1.1
    have hxU : x ∈ U := hIU i hxI
    have hmem : QuotientGroup.mk' (Z.subgroupOf U) ⟨x, hxU⟩ ∈ Ī i :=
      Subgroup.mem_map.mpr ⟨⟨x, hxU⟩, Subgroup.mem_subgroupOf.mpr hxI, rfl⟩
    rw [hbot] at hmem
    rw [Subgroup.mem_bot] at hmem
    have hmemZ : (⟨x, hxU⟩ : ↥U) ∈ Z.subgroupOf U :=
      (QuotientGroup.eq_one_iff (⟨x, hxU⟩ : ↥U)).mp hmem
    exact hxZ (Subgroup.mem_subgroupOf.mp hmemZ)
  have hend : ∀ i, ∀ f : Sec U Z →* Sec U Z,
      (∀ g ∈ autSec L U Z, ∀ x, f (g x) = g (f x)) →
      (∀ x ∈ Ī i, f x ∈ Ī i) →
      (∀ j, j ≠ i → ∀ x ∈ Ī j, f x = 1) →
      (∀ x ∈ Ī i, f x = x) ∨ (∀ x ∈ Ī i, f x = 1) := by
    intro i f hfcomm hfmem _
    exact s16h_secIncl_hend Z (I i) U (hZI i) (hIU i) (hLI i) hLZ hLU (hss i).2 f hfcomm hfmem
  have hspan' : ⨆ i, Ī i = ⊤ := by
    have hZU : Z ≤ U := le_sup_left.trans_eq hspan
    calc ⨆ i, Ī i
        = (⨆ i, (I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [Subgroup.map_iSup]
      _ = ((⨆ i, I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [s16h_subgroupOf_iSup hIU]
      _ = (((⨆ i, I i) ⊔ Z).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [Subgroup.subgroupOf_sup (iSup_le hIU) hZU, Subgroup.map_sup, hmapZ, sup_bot_eq]
      _ = (U.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
            rw [show (⨆ i, I i) ⊔ Z = U by rw [sup_comm]; exact hspan]
      _ = ⊤ := by
            rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _
              (QuotientGroup.mk'_surjective (N := Z.subgroupOf U))]
  have hind' : ∀ i, Ī i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), Ī j) = ⊥ := by
    intro i
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hxi
    have hmapj : (⨆ (j : Fin k) (_ : j ≠ i), Ī j)
        = (⨆ (j : Fin k) (_ : j ≠ i), (I j).subgroupOf U).map
            (QuotientGroup.mk' (Z.subgroupOf U)) := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      simp only [Subgroup.map_iSup]
      rfl
    rw [hmapj] at hxj
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp hxj
    have hvI : (v : W) ∈ ⨆ (j : Fin k) (_ : j ≠ i), I j := by
      rw [← s16h_subgroupOf_iSup_ne hIU i] at hv
      exact Subgroup.mem_subgroupOf.mp hv
    have hzu : (u : W) ∈ Z := by
      have h1 : (v * u⁻¹ : ↥U) ∈ Z.subgroupOf U := by
        rw [← QuotientGroup.eq_one_iff]
        show QuotientGroup.mk' (Z.subgroupOf U) (v * u⁻¹) = 1
        rw [map_mul, map_inv, hvu, mul_inv_cancel]
      have hz : ((v * u⁻¹ : ↥U) : W) ∈ Z := Subgroup.mem_subgroupOf.mp h1
      have hmem : (u : W) ∈ I i ⊓ (Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j) := by
        refine ⟨Subgroup.mem_subgroupOf.mp hu, ?_⟩
        have h2 : (((v * u⁻¹ : ↥U) : W))⁻¹ ∈ Z := Z.inv_mem hz
        have h3 : (((v * u⁻¹ : ↥U) : W))⁻¹ * (v : W) ∈
            Z ⊔ ⨆ (j : Fin k) (_ : j ≠ i), I j :=
          mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right hvI)
        have hu_eq : (((v * u⁻¹ : ↥U) : W))⁻¹ * (v : W) = (u : W) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [hu_eq] at h3
        exact h3
      exact hind i hmem
    exact (QuotientGroup.eq_one_iff u).mpr (Subgroup.mem_subgroupOf.mpr hzu)
  exact s16h_sum_cent_card_dvd (Q := Sec U Z) (Λ := autSec L U Z) (I := Ī) hQ hk
    hstab hsimple hend hspan' hind' hq hq2 hF hFe

private theorem s16h_finite_mulAut_of_finite (X : Type) [Group X] [Finite X] :
    Finite (MulAut X) := by
  classical
  exact Finite.of_injective (fun f : MulAut X => (f : X → X))
    (fun f g h => MulEquiv.ext (congrFun h))

private theorem s16h_H5_normalizer_le_stabSub_commSub {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (commSub ⊤ L) := by
  rw [mem_stabSub]
  have hnorm : ∀ x ∈ L, g * x * g⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hgNinv : g⁻¹ ∈ normalizer (L : Set (MulAut W)) :=
    (normalizer (L : Set (MulAut W))).inv_mem hg
  have hnorminv : ∀ x ∈ L, g⁻¹ * x * (g⁻¹)⁻¹ ∈ L :=
    fun x hx => (Subgroup.mem_normalizer_iff.mp hgNinv x).mp hx
  intro u
  constructor
  · intro hu
    have hmem : g⁻¹ (g u) ∈ commSub (⊤ : Subgroup W) L :=
      commSub_top_stable151b hnorminv (g u) hu
    simpa using hmem
  · intro hu
    exact commSub_top_stable151b hnorm u hu

private theorem s16h_H5_le_stabSub_commSub (L : Subgroup (MulAut W)) :
    L ≤ stabSub (commSub ⊤ L) := fun l hl =>
  s16h_H5_normalizer_le_stabSub_commSub (Subgroup.le_normalizer hl)

private theorem s16h_le_stabSub_fixV (L : Subgroup (MulAut W)) : L ≤ stabSub (fixV L) := by
  intro l hl
  rw [mem_stabSub]
  intro z
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : l * x * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
    have h1 : (l * x * l⁻¹) (l z) = l z := hz _ hx'
    have h2 : (l * x * l⁻¹) (l z) = l (x z) := by simp [MulAut.mul_apply]
    have h3 : l (x z) = l z := by rw [← h2, h1]
    exact l.injective h3
  · intro hz
    rw [mem_fixV] at hz
    rwa [hz l hl]

private theorem s16h_normalizer_le_stabSub_fixV {L : Subgroup (MulAut W)} {g : MulAut W}
    (hg : g ∈ normalizer (L : Set (MulAut W))) : g ∈ stabSub (fixV L) := by
  rw [mem_stabSub]
  intro z
  constructor
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g * x * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have h1 : (g * x * g⁻¹) (g z) = g z := hz _ hx'
    have h2 : (g * x * g⁻¹) (g z) = g (x z) := by simp [MulAut.mul_apply]
    have h3 : g (x z) = g z := by rw [← h2, h1]
    exact g.injective h3
  · intro hz
    rw [mem_fixV] at hz ⊢
    intro x hx
    have hx' : g⁻¹ * x * g ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ((normalizer (L : Set (MulAut W))).inv_mem hg) x).mp hx
    have h1 : (g⁻¹ * x * g) z = z := hz _ hx'
    have h2 : g ((g⁻¹ * x * g) z) = g z := by rw [h1]
    have h3 : x (g z) = g ((g⁻¹ * x * g) z) := by simp [MulAut.mul_apply]
    rw [h3, h2]

private theorem s16h_stabSub_inf {U Z : Subgroup W} {g : MulAut W}
    (hU : g ∈ stabSub U) (hZ : g ∈ stabSub Z) : g ∈ stabSub (U ⊓ Z) := by
  rw [mem_stabSub] at hU hZ ⊢
  intro x
  exact ⟨fun hx => ⟨(hU x).mp hx.1, (hZ x).mp hx.2⟩,
    fun hx => ⟨(hU x).mpr hx.1, (hZ x).mpr hx.2⟩⟩

private theorem s16h_autSec_le_normalizer {L Y : Subgroup (MulAut W)} {V C : Subgroup W}
    (hLV : L ≤ stabSub V) (hLC : L ≤ stabSub C) (hYV : Y ≤ stabSub V) (hYC : Y ≤ stabSub C)
    (hYL : Y ≤ normalizer (L : Set (MulAut W))) :
    autSec Y V C ≤ normalizer ((autSec L V C : Subgroup (MulAut (Sec V C))) :
      Set (MulAut (Sec V C))) := by
  set X' : Subgroup (MulAut W) := stabSub V ⊓ stabSub C with hX'def
  have hX'V : X' ≤ stabSub V := inf_le_left
  have hX'C : X' ≤ stabSub C := inf_le_right
  rw [← CFSG.Quasithin.B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hYV hYC),
    ← CFSG.Quasithin.B5.map_secHom_eq_autSec X' hX'V hX'C (le_inf hLV hLC)]
  refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp (hYL (Subgroup.mem_subgroupOf.mp hy)) (g : MulAut W)

theorem s16h_H5_block_of_autSub_one [Finite W] {A L : Subgroup (MulAut W)} {q : ℕ}
    (h : ∀ E : Subgroup (MulAut W), E ≤ A ⊓ normalizer (L : Set (MulAut W)) →
      IsElemAbelian q E → Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q) :
    s16h_BlockBound A L q 1 := by
  intro E hE hEab
  have hU : E ≤ stabSub (commSub ⊤ L) := by
    intro g hg
    exact s16h_H5_normalizer_le_stabSub_commSub (L := L) (g := g)
      (Subgroup.mem_inf.mp (hE hg)).2
  have hcard := card_autSub_mul (A := E) (U := commSub ⊤ L) hU
  have hb := h E hE hEab
  rw [← hcard, pow_one]
  exact Nat.mul_le_mul_right _ hb

theorem s16h_H5_sum_glue_one [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {N : Subgroup (MulAut W) → Subgroup W → Subgroup W → Prop}
    (hN : ∀ I : Subgroup W, N L I (commSub ⊤ L ⊓ fixV L) →
      s16h_SimpleScalar L I (commSub ⊤ L ⊓ fixV L))
    {k : ℕ} (hk : k ≤ 3) (hS : SumOfNat N L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) k)
    (hcenter : Subgroup.center ↥L = ⊥) {M : ℕ} (hM : Nat.card (MulAut ↥L) ∣ M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hMq : ¬ q ^ 2 ∣ M)
    (hq168 : ¬ q ∣ 168 ∨ ¬ q ∣ M ∨ k ≤ 1) :
    ∀ E : Subgroup (MulAut W),
      E ≤ A ⊓ normalizer (L : Set (MulAut W)) → IsElemAbelian q E →
      Nat.card ↥(autSub E (commSub ⊤ L)) ≤ q := by
  intro E hE hEab
  classical
  haveI : Finite (MulAut W) := s16h_finite_mulAut_of_finite W
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hLU : L ≤ stabSub U := by
    rw [hU]
    exact s16h_H5_le_stabSub_commSub L
  have hLfix : L ≤ stabSub (fixV L) := s16h_le_stabSub_fixV L
  have hLZ : L ≤ stabSub Z := by
    rw [hZ]
    exact fun l hl => s16h_stabSub_inf (hLU hl) (hLfix hl)
  have hEN : E ≤ normalizer (L : Set (MulAut W)) := fun e he => (mem_inf.mp (hE he)).2
  have hEU : E ≤ stabSub U := by
    rw [hU]
    exact fun e he => s16h_H5_normalizer_le_stabSub_commSub (hEN he)
  have hEfix : E ≤ stabSub (fixV L) := fun e he =>
    s16h_normalizer_le_stabSub_fixV (hEN he)
  have hEZ : E ≤ stabSub Z := by
    rw [hZ]
    exact fun e he => s16h_stabSub_inf (hEU he) (hEfix he)
  have hfaith : L ⊓ centSec U Z = ⊥ := by
    rw [hU, hZ]
    exact s16h_H5_faithful_on_quotient hc hcenter
  set Λ : Subgroup (MulAut (Sec U Z)) := autSec L U Z with hΛ
  set E' : Subgroup (MulAut (Sec U Z)) := autSec E U Z with hE'
  have hE'ea : IsElemAbelian q E' := by
    set X₀ : Subgroup (MulAut W) := stabSub U ⊓ stabSub Z with hX₀
    have hX₀U : X₀ ≤ stabSub U := inf_le_left
    have hX₀Z : X₀ ≤ stabSub Z := inf_le_right
    have hEX₀ : E ≤ X₀ := le_inf hEU hEZ
    have hmap := IsElemAbelian.map (hEab.subgroupOf X₀)
      (CFSG.Quasithin.B5.secHom X₀ hX₀U hX₀Z)
    rw [CFSG.Quasithin.B5.map_secHom_eq_autSec X₀ hX₀U hX₀Z hEX₀] at hmap
    simpa [hE'] using hmap
  have hE'N : E' ≤ normalizer (Λ : Set (MulAut (Sec U Z))) := by
    rw [hE', hΛ]
    exact s16h_autSec_le_normalizer hLU hLZ hEU hEZ hEN
  let ρ : E' →* MulAut Λ :=
    (Subgroup.normalizerMonoidHom Λ).comp (Subgroup.inclusion hE'N)
  set F : Subgroup (MulAut (Sec U Z)) :=
    E' ⊓ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) with hF
  have hker : ρ.ker = F.subgroupOf E' := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, ?_⟩
      change (Subgroup.normalizerMonoidHom Λ) (Subgroup.inclusion hE'N x) = 1 at hx
      have hx' : (Subgroup.inclusion hE'N x) ∈
          (Subgroup.normalizerMonoidHom Λ).ker := hx
      rw [Subgroup.normalizerMonoidHom_ker] at hx'
      rw [Subgroup.mem_subgroupOf] at hx'
      simpa using hx'
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker]
      change (Subgroup.normalizerMonoidHom Λ) (Subgroup.inclusion hE'N x) = 1
      rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
      simpa using hx.2
  have hkerCard : Nat.card ρ.ker = Nat.card F := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hFle : F ≤ Subgroup.centralizer (Λ : Set (MulAut (Sec U Z))) := inf_le_right
  have hFea : IsElemAbelian q F := hE'ea.mono inf_le_left
  have hFcard : Nat.card F ≤ q :=
    s16h_sum_cent_sec hc.elem hN hk hS hLU hLZ hq hq2 hFle hFea
  have hFdvd : Nat.card F ∣ Nat.card (GL (Fin k) (ZMod 2)) :=
    s16h_sum_cent_sec_dvd hc.elem hN hk hS hLU hLZ hq hq2 hFle hFea
  have hGL168 : Nat.card (GL (Fin k) (ZMod 2)) ∣ 168 := by
    interval_cases k
    · rw [Matrix.card_GL_field]; norm_num
    · rw [Matrix.card_GL_field]; norm_num
    · rw [Matrix.card_GL_field]; norm_num
    · rw [Matrix.card_GL_field, Fin.prod_univ_three]; norm_num
  have hFdvd168 : Nat.card F ∣ 168 := hFdvd.trans hGL168
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (MulAut (Sec U Z)) := s16h_finite_mulAut_of_finite (Sec U Z)
  have hrangeEA : IsElemAbelian q ρ.range := by
    have hmap := IsElemAbelian.map (hE'ea.subgroupOf E') ρ
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map ρ] at hmap
    exact hmap
  obtain ⟨j, hj⟩ :=
    (IsPGroup.iff_card (p := q) (G := ↥ρ.range)).mp hrangeEA.isPGroup
  have hcardAut : Nat.card (MulAut ↥Λ) = Nat.card (MulAut ↥L) := by
    have e : ↥L ≃* ↥Λ := by
      rw [hΛ]
      exact CFSG.Quasithin.B5.secEquiv L hLU hLZ hfaith
    exact (Nat.card_congr (MulAut.congr e).toEquiv).symm
  have hdvdRange : Nat.card ρ.range ∣ Nat.card (MulAut ↥Λ) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  have hdvdM : Nat.card ρ.range ∣ M := by
    exact hdvdRange.trans (hcardAut ▸ hM)
  have hjM : q ^ j ∣ M := by
    rw [← hj]
    exact hdvdM
  have hjle : j ≤ 1 := by
    rcases Nat.lt_or_ge j 2 with h | h
    · omega
    · exfalso
      exact hMq (dvd_trans (pow_dvd_pow q h) hjM)
  have hRangeLe : Nat.card ρ.range ≤ q := by
    rw [hj]
    calc q ^ j ≤ q ^ 1 := Nat.pow_le_pow_right hq.pos hjle
      _ = q := pow_one q
  have hcardE' : Nat.card ↥(autSub E U) = Nat.card E' := by
    simpa [hU, hZ, hE'] using s16h_H5_card_autSub_eq_autSec hc hE
  have hmain : Nat.card F * Nat.card ρ.range ≤ q := by
    rcases hq168 with h168 | hMq' | hk1
    · have hF1 : Nat.card F = 1 := by
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hFea.isPGroup
        have hm0 : m = 0 := by
          by_contra hmne
          have hm168 : q ^ m ∣ 168 := by rw [← hm]; exact hFdvd168
          exact h168 (dvd_trans (dvd_pow_self q hmne) hm168)
        rw [hm, hm0, pow_zero]
      rw [hF1, one_mul]
      exact hRangeLe
    · have hR1 : Nat.card ρ.range = 1 := by
        rw [hj]
        have hj0 : j = 0 := by
          by_contra hjne
          exact hMq' (dvd_trans (dvd_pow_self q hjne) hjM)
        rw [hj0, pow_zero]
      rw [hR1, mul_one]
      exact hFcard
    · have hGL1 : Nat.card (GL (Fin k) (ZMod 2)) = 1 := by
        interval_cases k <;> rw [Matrix.card_GL_field] <;> norm_num
      have hF1 : Nat.card F = 1 := by
        have h1 : Nat.card (GL (Fin k) (ZMod 2)) ∣ 1 := by
          rw [hGL1]
        exact Nat.dvd_one.mp (hFdvd.trans h1)
      rw [hF1, one_mul]
      exact hRangeLe
  calc
    Nat.card ↥(autSub E U) = Nat.card E' := hcardE'
    _ = Nat.card ρ.ker * Nat.card ρ.range := (card_ker_mul_card_range ρ).symm
    _ = Nat.card F * Nat.card ρ.range := by rw [hkerCard]
    _ ≤ q := hmain

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
