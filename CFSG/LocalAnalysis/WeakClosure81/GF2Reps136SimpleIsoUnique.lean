module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleIsoGraph

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q]

@[expose] def w1369_ta_Equiv {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (hA : StableUnder Λ A) (hB : StableUnder Λ B) (e : ↥A ≃* ↥B) : Prop :=
  ∀ g (hg : g ∈ Λ) (x : ↥A),
    (e ⟨g (x : Q), hA g hg (x : Q) x.2⟩ : Q) = g (e x : Q)

lemma w1369_ta_Equiv.symm {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    {hA : StableUnder Λ A} {hB : StableUnder Λ B} {e : ↥A ≃* ↥B}
    (he : w1369_ta_Equiv hA hB e) : w1369_ta_Equiv hB hA e.symm := by
  intro g hg y
  let z : ↥A := e.symm y
  have hz : e z = y := e.apply_symm_apply y
  have h1 : e (e.symm ⟨g (y : Q), hB g hg (y : Q) y.2⟩) =
      e ⟨g (z : Q), hA g hg (z : Q) z.2⟩ := by
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [he g hg z]
    exact congrArg g (congrArg Subtype.val hz.symm)
  have h2 := e.injective h1
  change ((e.symm ⟨g (y : Q), hB g hg (y : Q) y.2⟩ : ↥A) : Q) = g ((z : ↥A) : Q)
  rw [h2]

lemma w1369_ta_Equiv.trans {Λ : Subgroup (MulAut Q)} {A B D : Subgroup Q}
    (hA : StableUnder Λ A) (hB : StableUnder Λ B) (hD : StableUnder Λ D)
    {e : ↥A ≃* ↥B} {f : ↥B ≃* ↥D}
    (he : w1369_ta_Equiv hA hB e) (hf : w1369_ta_Equiv hB hD f) :
    w1369_ta_Equiv hA hD (e.trans f) := by
  intro g hg x
  change (f (e ⟨g (x : Q), hA g hg (x : Q) x.2⟩) : Q) = g (f (e x) : Q)
  have h1 : e ⟨g (x : Q), hA g hg (x : Q) x.2⟩ =
      ⟨g (e x : Q), hB g hg (e x : Q) (e x).2⟩ := Subtype.ext (he g hg x)
  rw [h1]
  exact hf g hg (e x)

lemma w1369_ta_end_I_eq_id_or_zero {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {i : Fin k} (hpart : ∃ j, j ≠ i) (f : ↥(I i) →* ↥(I i))
    (hf : ∀ g (hg : g ∈ Λ) (x : ↥(I i)),
      (f ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) = g (f x : Q)) :
    f = MonoidHom.id (I i) ∨ f = 1 := by
  obtain ⟨j, hij⟩ := hpart
  let ej : Q →* ↥(I i) := MonoidHom.codRestrict (P.e i) (I i) (fun x => P.e_mem i x)
  have hej_self : ∀ x : ↥(I i), ej (x : Q) = x := fun x =>
    Subtype.ext (P.e_self i (x : Q) x.2)
  let F : Q →* Q := (I i).subtype.comp (f.comp ej)
  have hFcomm : ∀ g ∈ Λ, ∀ x, F (g x) = g (F x) := by
    intro g hg x
    change (f (ej (g x)) : Q) = g ((f (ej x)) : Q)
    have h1 : (ej (g x) : Q) = g (ej x : Q) := P.e_equiv i g hg x
    have hgx : ej (g x) = ⟨g (ej x : Q), hstab i g hg (ej x : Q) (ej x).2⟩ :=
      Subtype.ext h1
    rw [hgx]
    exact hf g hg (ej x)
  have hFmem : ∀ x ∈ I i, F x ∈ I i := fun x _ => (f (ej x)).2
  have hFkill : ∀ j', j' ≠ i → ∀ x ∈ I j', F x = 1 := by
    intro j' hj' x hx
    change (f (ej x) : Q) = 1
    have h0 : ej x = 1 := by
      apply Subtype.ext
      exact P.e_other i j' hj' x hx
    rw [h0, map_one]
    rfl
  rcases hend i j hij.symm (hisoAll i j hij.symm) F hFcomm hFmem hFkill with hid | hone
  · left
    ext x
    have h := hid (x : Q) x.2
    change (f (ej (x : Q)) : Q) = (x : Q) at h
    rw [hej_self x] at h
    simpa using h
  · right
    ext x
    have h := hone (x : Q) x.2
    change (f (ej (x : Q)) : Q) = 1 at h
    rw [hej_self x] at h
    simpa using h

lemma w1369_ta_aut_I_eq_one {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {i : Fin k} (hpart : ∃ j, j ≠ i) (φ : ↥(I i) ≃* ↥(I i))
    (hφ : w1369_ta_Equiv (hstab i) (hstab i) φ) : φ = 1 := by
  rcases w1369_ta_end_I_eq_id_or_zero P hstab hsimple hend hisoAll hpart φ.toMonoidHom
    (fun g hg x => hφ g hg x) with hid | hone
  · apply MulEquiv.ext
    intro x
    have h := congrArg (fun f : ↥(I i) →* ↥(I i) => f x) hid
    simpa using h
  · exfalso
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
    have hx1 : φ x = 1 := by
      have h := congrArg (fun f : ↥(I i) →* ↥(I i) => f x) hone
      simpa using h
    exact hx (φ.injective (by rw [hx1, map_one]))

lemma w1369_ta_iso_unique_equiv {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {i j : Fin k} (hij : i ≠ j) {α β : ↥(I i) ≃* ↥(I j)}
    (hα : w1369_ta_Equiv (hstab i) (hstab j) α)
    (hβ : w1369_ta_Equiv (hstab i) (hstab j) β) : α = β := by
  have hγ : w1369_ta_Equiv (hstab j) (hstab j) (α.symm.trans β) :=
    w1369_ta_Equiv.trans (hstab j) (hstab i) (hstab j)
      (w1369_ta_Equiv.symm hα) hβ
  have hγ1 := w1369_ta_aut_I_eq_one P hstab hsimple hend hisoAll ⟨i, hij⟩ _ hγ
  apply MulEquiv.ext
  intro x
  have h := congrArg (fun e : ↥(I j) ≃* ↥(I j) => e (α x)) hγ1
  simpa using h.symm

lemma w1369_ta_aut_eq_one_of_secIsoOn {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    {i : Fin k} (hpart : ∃ j', j' ≠ i) {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S)
    (hSec : SecIsoOn Λ (I i) ⊥ S ⊥) (ψ : ↥S ≃* ↥S) (hψ : w1369_ta_Equiv hS.2.1 hS.2.1 ψ) :
    ψ = 1 := by
  obtain ⟨e, he⟩ := w1369_ta_exists_mulEquiv_of_secIsoOn hSec
  have hA : StableUnder Λ (I i) := hstab i
  have hB : StableUnder Λ S := hS.2.1
  have hes : w1369_ta_Equiv hB hA e.symm := w1369_ta_Equiv.symm he
  have hφ : w1369_ta_Equiv hA hA (e.trans (ψ.trans e.symm)) :=
    w1369_ta_Equiv.trans hA hB hA he (w1369_ta_Equiv.trans hB hB hA hψ hes)
  have hφid : e.trans (ψ.trans e.symm) = 1 :=
    w1369_ta_aut_I_eq_one P hstab hsimple hend hisoAll hpart _ hφ
  apply MulEquiv.ext
  intro y
  have h1 : e.symm (ψ y) = e.symm y := by
    have h2 := congrArg (fun g : ↥(I i) ≃* ↥(I i) => g (e.symm y)) hφid
    simpa using h2
  simpa using e.symm.injective h1

@[expose] def w1369_ta_graphHom {A B : Subgroup Q} (e : ↥A ≃* ↥B) : ↥A →* Q :=
  MonoidHom.mk' (fun x => (x : Q) * (e x : Q)) (fun a b => by
    change ((a * b : ↥A) : Q) * (e (a * b) : Q) =
      ((a : Q) * (e a : Q)) * ((b : Q) * (e b : Q))
    simp only [map_mul, Subgroup.coe_mul]
    ac_rfl)

lemma w1369_ta_graph_isSimple {Λ : Subgroup (MulAut Q)} {A B : Subgroup Q}
    (hA : w1369_ta_IsSimple Λ A) (hB : w1369_ta_IsSimple Λ B) (hAB : A ⊓ B = ⊥)
    (e : ↥A ≃* ↥B) (he : w1369_ta_Equiv hA.2.1 hB.2.1 e) :
    w1369_ta_IsSimple Λ (w1369_ta_graphHom e).range := by
  refine w1369_ta_isSimple_range hA ?_ ?_
  · rw [injective_iff_map_eq_one]
    intro x hx
    change (x : Q) * (e x : Q) = 1 at hx
    have hxe : (e x : Q) = (x : Q)⁻¹ := by
      have := congrArg (fun z : Q => (x : Q)⁻¹ * z) hx
      simpa [mul_assoc] using this
    have hmem : (e x : Q) ∈ A ⊓ B := by
      refine ⟨?_, (e x).2⟩
      rw [hxe]
      exact A.inv_mem x.2
    rw [hAB, Subgroup.mem_bot] at hmem
    exact Subtype.ext (inv_eq_one.mp (hxe.symm.trans hmem))
  · intro g hg x
    change (g (x : Q)) * (e ⟨g (x : Q), hA.2.1 g hg (x : Q) x.2⟩ : Q) =
      g ((x : Q) * (e x : Q))
    rw [he g hg x]
    exact (map_mul (g : Q →* Q) (x : Q) (e x : Q)).symm

lemma w1369_ta_graph_le_sup {A B : Subgroup Q} (e : ↥A ≃* ↥B) :
    (w1369_ta_graphHom e).range ≤ A ⊔ B := by
  rintro y ⟨x, rfl⟩
  exact Subgroup.mul_mem_sup x.2 (e x).2

lemma w1369_ta_eq_of_supp_eq {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}
    (P : w1369_ta_Proj I Λ) (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    (hend : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
      (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
      (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) → (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1))
    (hisoAll : ∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥)
    (hpart : ∀ i : Fin k, ∃ j : Fin k, j ≠ i)
    {S T : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) (hT : w1369_ta_IsSimple Λ T)
    (hsupp : w1369_ta_supp P S = w1369_ta_supp P T) : S = T := by
  obtain ⟨i, hi⟩ := w1369_ta_supp_nonempty P hS.1
  have hiT : w1369_ta_projHom P T i ≠ 1 := by
    have hmem : i ∈ w1369_ta_supp P S := hi
    rw [hsupp] at hmem
    exact hmem
  obtain ⟨ηS, hηS⟩ := w1369_ta_exists_mulEquiv_of_secIsoOn
    (w1369_ta_SecIsoOn_I_of_mem_supp P hstab hsimple hS hi)
  obtain ⟨ηT, hηT⟩ := w1369_ta_exists_mulEquiv_of_secIsoOn
    (w1369_ta_SecIsoOn_I_of_mem_supp P hstab hsimple hT hiT)
  have hcomp : ∀ j, (w1369_ta_projHom P S j).comp ηS.toMonoidHom =
      (w1369_ta_projHom P T j).comp ηT.toMonoidHom := by
    intro j
    by_cases hji : j = i
    · rw [hji]
      have hfeS : ∀ g (hg : g ∈ Λ) (x : ↥(I i)),
          (((w1369_ta_projHom P S i).comp ηS.toMonoidHom)
            ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) =
            g (((w1369_ta_projHom P S i).comp ηS.toMonoidHom) x : Q) := by
        intro g hg x
        change (w1369_ta_projHom P S i (ηS ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩) : Q) =
          g ((w1369_ta_projHom P S i (ηS x)) : Q)
        have h1 : ηS ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ =
            ⟨g (ηS x : Q), hS.2.1 g hg (ηS x : Q) (ηS x).2⟩ := Subtype.ext (hηS g hg x)
        rw [h1]
        exact w1369_ta_projHom_equiv P hS.2.1 i g hg (ηS x)
      have hbijS : Function.Bijective ((w1369_ta_projHom P S i).comp ηS.toMonoidHom) :=
        (w1369_ta_projHom_bij P hsimple hS hi).comp ηS.bijective
      have hidS : (w1369_ta_projHom P S i).comp ηS.toMonoidHom = MonoidHom.id (I i) := by
        rcases w1369_ta_end_I_eq_id_or_zero P hstab hsimple hend hisoAll (hpart i) _
          hfeS with hid | hone
        · exact hid
        · exfalso
          obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
          have hx1 : ((w1369_ta_projHom P S i).comp ηS.toMonoidHom) x = 1 := by rw [hone]; rfl
          exact hx (hbijS.1 (by rw [hx1, map_one]))
      have hfeT : ∀ g (hg : g ∈ Λ) (x : ↥(I i)),
          (((w1369_ta_projHom P T i).comp ηT.toMonoidHom)
            ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) =
            g (((w1369_ta_projHom P T i).comp ηT.toMonoidHom) x : Q) := by
        intro g hg x
        change (w1369_ta_projHom P T i (ηT ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩) : Q) =
          g ((w1369_ta_projHom P T i (ηT x)) : Q)
        have h1 : ηT ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ =
            ⟨g (ηT x : Q), hT.2.1 g hg (ηT x : Q) (ηT x).2⟩ := Subtype.ext (hηT g hg x)
        rw [h1]
        exact w1369_ta_projHom_equiv P hT.2.1 i g hg (ηT x)
      have hbijT : Function.Bijective ((w1369_ta_projHom P T i).comp ηT.toMonoidHom) :=
        (w1369_ta_projHom_bij P hsimple hT hiT).comp ηT.bijective
      have hidT : (w1369_ta_projHom P T i).comp ηT.toMonoidHom = MonoidHom.id (I i) := by
        rcases w1369_ta_end_I_eq_id_or_zero P hstab hsimple hend hisoAll (hpart i) _
          hfeT with hid | hone
        · exact hid
        · exfalso
          obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hsimple i).1
          have hx1 : ((w1369_ta_projHom P T i).comp ηT.toMonoidHom) x = 1 := by rw [hone]; rfl
          exact hx (hbijT.1 (by rw [hx1, map_one]))
      rw [hidS, hidT]
    · by_cases hj : w1369_ta_projHom P S j = 1
      · have hjT' : w1369_ta_projHom P T j = 1 := by
          by_contra hne
          have hmem : j ∈ w1369_ta_supp P T := hne
          rw [← hsupp] at hmem
          exact hmem hj
        rw [hj, hjT']
        ext x
        simp
      · have hjT2 : w1369_ta_projHom P T j ≠ 1 := by
          have hmem : j ∈ w1369_ta_supp P S := hj
          rw [hsupp] at hmem
          exact hmem
        have hbijS : Function.Bijective ((w1369_ta_projHom P S j).comp ηS.toMonoidHom) :=
          (w1369_ta_projHom_bij P hsimple hS hj).comp ηS.bijective
        have hbijT : Function.Bijective ((w1369_ta_projHom P T j).comp ηT.toMonoidHom) :=
          (w1369_ta_projHom_bij P hsimple hT hjT2).comp ηT.bijective
        have heS : w1369_ta_Equiv (hstab i) (hstab j)
            (MulEquiv.ofBijective ((w1369_ta_projHom P S j).comp ηS.toMonoidHom) hbijS) := by
          intro g hg x
          change (((w1369_ta_projHom P S j).comp ηS.toMonoidHom)
              ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) =
            g (((w1369_ta_projHom P S j).comp ηS.toMonoidHom) x : Q)
          have h1 : ηS ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ =
              ⟨g (ηS x : Q), hS.2.1 g hg (ηS x : Q) (ηS x).2⟩ := Subtype.ext (hηS g hg x)
          change (w1369_ta_projHom P S j (ηS ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩) : Q) =
            g ((w1369_ta_projHom P S j (ηS x)) : Q)
          rw [h1]
          exact w1369_ta_projHom_equiv P hS.2.1 j g hg (ηS x)
        have heT : w1369_ta_Equiv (hstab i) (hstab j)
            (MulEquiv.ofBijective ((w1369_ta_projHom P T j).comp ηT.toMonoidHom) hbijT) := by
          intro g hg x
          change (((w1369_ta_projHom P T j).comp ηT.toMonoidHom)
              ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ : Q) =
            g (((w1369_ta_projHom P T j).comp ηT.toMonoidHom) x : Q)
          have h1 : ηT ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩ =
              ⟨g (ηT x : Q), hT.2.1 g hg (ηT x : Q) (ηT x).2⟩ := Subtype.ext (hηT g hg x)
          change (w1369_ta_projHom P T j (ηT ⟨g (x : Q), hstab i g hg (x : Q) x.2⟩) : Q) =
            g ((w1369_ta_projHom P T j (ηT x)) : Q)
          rw [h1]
          exact w1369_ta_projHom_equiv P hT.2.1 j g hg (ηT x)
        apply MonoidHom.ext
        intro x
        have hx := congrArg (fun e : ↥(I i) ≃* ↥(I j) => e x)
          (w1369_ta_iso_unique_equiv P hstab hsimple hend hisoAll (Ne.symm hji) heS heT)
        simpa using hx
  have hprod : ∀ x : ↥(I i), ((ηS x : ↥S) : Q) = ((ηT x : ↥T) : Q) := by
    intro x
    have h1 : ((ηS x : ↥S) : Q) = ∏ j, (w1369_ta_projHom P S j) (ηS x) := by
      rw [← P.e_prod ((ηS x : ↥S) : Q)]
      exact Finset.prod_congr rfl (fun j _ => by rw [w1369_ta_projHom_apply])
    have h2 : ((ηT x : ↥T) : Q) = ∏ j, (w1369_ta_projHom P T j) (ηT x) := by
      rw [← P.e_prod ((ηT x : ↥T) : Q)]
      exact Finset.prod_congr rfl (fun j _ => by rw [w1369_ta_projHom_apply])
    rw [h1, h2]
    exact Finset.prod_congr rfl (fun j _ =>
      congrArg Subtype.val (congrArg (fun f : ↥(I i) →* ↥(I j) => (f x : ↥(I j))) (hcomp j)))
  have hle : S ≤ T := by
    intro s hs
    have h1 : ((ηS (ηS.symm ⟨s, hs⟩) : ↥S) : Q) = s := by
      rw [show ηS (ηS.symm ⟨s, hs⟩) = ⟨s, hs⟩ from ηS.apply_symm_apply ⟨s, hs⟩]
    rw [← h1, hprod (ηS.symm ⟨s, hs⟩)]
    exact (ηT (ηS.symm ⟨s, hs⟩)).2
  exact (hT.2.2 S hS.2.1 hle).resolve_left hS.1

lemma w1369_ta_map_injective (n : MulAut Q) :
    Function.Injective (fun S : Subgroup Q => S.map n.toMonoidHom) := by
  intro S T h
  have h1 := congrArg (fun U : Subgroup Q => U.map (n⁻¹ : MulAut Q).toMonoidHom) h
  rw [Subgroup.map_map, Subgroup.map_map] at h1
  have hid : ((n⁻¹ : MulAut Q).toMonoidHom.comp n.toMonoidHom) = MonoidHom.id Q := by
    ext z
    exact MulEquiv.symm_apply_apply n z
  rwa [hid, Subgroup.map_id, Subgroup.map_id] at h1

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
