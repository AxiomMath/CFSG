module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136SimpleSupport
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise Matrix

lemma w1369_ta_exists_mulEquiv_of_secIsoOn {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) :
    ∃ e : ↥A ≃* ↥B, ∀ g (hg : g ∈ Λ) (x : ↥A),
      (e ⟨g (x : Q), h.2.2.1 g hg (x : Q) x.2⟩ : Q) = g (e x : Q) := by
  classical
  obtain ⟨-, -, hSA, -, hSB, -, β, hβB, hβiff, hβsurj, hβeq⟩ := h
  have hβone : ∀ a : ↥A, β a = 1 ↔ (a : Q) = 1 := fun a => by simpa using hβiff a
  let e : ↥A →* ↥B := β.codRestrict B hβB
  have he_val : ∀ a : ↥A, (e a : Q) = β a := fun a => rfl
  have he_bij : Function.Bijective e := by
    constructor
    · intro a a' haa'
      have hβaa' : β a = β a' := by
        rw [← he_val a, ← he_val a', congrArg Subtype.val haa']
      have h1 : β (a * a'⁻¹) = 1 := by rw [map_mul, map_inv, hβaa', mul_inv_cancel]
      have h2 : ((a * a'⁻¹ : ↥A) : Q) = 1 := (hβone (a * a'⁻¹)).mp h1
      have h3 : (a : Q) = (a' : Q) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv] at h2
        exact mul_inv_eq_one.mp h2
      exact Subtype.ext h3
    · intro b
      obtain ⟨a, ha⟩ := hβsurj (b : Q) b.2
      refine ⟨a, Subtype.ext ?_⟩
      have h1 : β a * (b : Q)⁻¹ = 1 := Subgroup.mem_bot.mp (by simpa using ha)
      rw [← he_val a, mul_inv_eq_one] at h1
      exact h1
  refine ⟨MulEquiv.ofBijective e he_bij, ?_⟩
  intro g hg x
  have h1 : β ⟨g (x : Q), hSA g hg (x : Q) x.2⟩ * (g (β x))⁻¹ ∈ (⊥ : Subgroup Q) :=
    hβeq g hg x ⟨g (x : Q), hSA g hg (x : Q) x.2⟩ rfl
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1
  simp only [MulEquiv.ofBijective_apply]
  rw [he_val, he_val]
  exact h1

lemma w1369_ta_SecIsoOn_symm {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {A B : Subgroup Q} (h : SecIsoOn Λ A ⊥ B ⊥) : SecIsoOn Λ B ⊥ A ⊥ := by
  obtain ⟨e, he⟩ := w1369_ta_exists_mulEquiv_of_secIsoOn h
  have hSA : StableUnder Λ A := h.2.2.1
  have hSB : StableUnder Λ B := h.2.2.2.2.1
  refine w1369_ta_SecIsoOn_of_mulEquiv hSB hSA e.symm ?_
  intro g hg y
  let z : ↥A := e.symm y
  have hz : e z = y := e.apply_symm_apply y
  have h1 : e (e.symm ⟨g (y : Q), hSB g hg (y : Q) y.2⟩) =
      e ⟨g (z : Q), hSA g hg (z : Q) z.2⟩ := by
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [he g hg z]
    exact congrArg g (congrArg Subtype.val hz.symm)
  have h2 := e.injective h1
  change ((e.symm ⟨g (y : Q), hSB g hg (y : Q) y.2⟩ : ↥A) : Q) = g ((z : ↥A) : Q)
  rw [h2]

lemma w1369_ta_SecIsoOn_I_of_mem_supp {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {j : Fin k}
    (hj : w1369_ta_projHom P S j ≠ 1) : SecIsoOn Λ (I j) ⊥ S ⊥ := by
  refine w1369_ta_SecIsoOn_of_mulEquiv (hstab j) hS.2.1
    (MulEquiv.ofBijective (w1369_ta_projHom P S j)
      (w1369_ta_projHom_bij P hsimple hS hj)).symm ?_
  intro g hg x
  exact w1369_ta_inv_equivariant' hS.2.1 (hstab j) (w1369_ta_projHom P S j) _
    (w1369_ta_projHom_equiv P hS.2.1 j) g hg x

lemma w1369_ta_eq_I_of_supp_subset {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {i : Fin k}
    (hsub : ∀ j, w1369_ta_projHom P S j ≠ 1 → j = i) : S = I i := by
  have hle : S ≤ I i := by
    intro s hs
    have hval : ∀ j, j ≠ i → (P.e j s : Q) = 1 := by
      intro j hji
      by_contra hne
      exact hji (hsub j (fun hzero => hne (by
        have h := congrArg (fun f : S →* I j => (f ⟨s, hs⟩ : Q)) hzero
        rw [w1369_ta_projHom_apply] at h
        simpa using h)))
    have hs' : s = P.e i s := by
      have hprod : (∏ j : Fin k, (P.e j s : Q)) = (P.e i s : Q) :=
        Finset.prod_eq_single i (fun j _ hji => hval j hji)
          (fun hi => absurd (Finset.mem_univ i) hi)
      exact (P.e_prod s).symm.trans hprod
    rw [hs']
    exact P.e_mem i s
  rcases (hsimple i).2.2 S hS.2.1 hle with h | h
  · exact absurd h hS.1
  · exact h

lemma w1369_ta_eq_I_of_SecIsoOn_I {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    (hstab : ∀ i, StableUnder Λ (I i))
    (hsimple : ∀ i, w1369_ta_IsSimple Λ (I i))
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {c : Fin k}
    (hSc : SecIsoOn Λ (I c) ⊥ S ⊥)
    (hnon : ∀ j, j ≠ c → ¬ SecIsoOn Λ (I j) ⊥ (I c) ⊥) : S = I c := by
  refine w1369_ta_eq_I_of_supp_subset P hsimple hS (fun j hj => ?_)
  by_contra hjc
  have h1 : SecIsoOn Λ (I j) ⊥ S ⊥ := w1369_ta_SecIsoOn_I_of_mem_supp P hstab hsimple hS hj
  have h2 : SecIsoOn Λ S ⊥ (I c) ⊥ := w1369_ta_SecIsoOn_symm hSc
  exact hnon j hjc (secIsoOn_trans h1 h2)

lemma w1369_ta_le_sup_pair {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {k : ℕ} {I : Fin k → Subgroup Q} (P : w1369_ta_Proj I Λ)
    {S : Subgroup Q} (hS : w1369_ta_IsSimple Λ S) {a b : Fin k} (hab : a ≠ b)
    (hsub : ∀ j, w1369_ta_projHom P S j ≠ 1 → j = a ∨ j = b) : S ≤ I a ⊔ I b := by
  intro s hs
  have hval : ∀ j, j ≠ a → j ≠ b → (P.e j s : Q) = 1 := by
    intro j hja hjb
    by_contra hne
    rcases hsub j (fun hzero => hne (by
      have h := congrArg (fun f : S →* I j => (f ⟨s, hs⟩ : Q)) hzero
      rw [w1369_ta_projHom_apply] at h
      simpa using h)) with h | h
    · exact hja h
    · exact hjb h
  have hsplit : (∏ j : Fin k, (P.e j s : Q)) = (P.e a s : Q) * (P.e b s : Q) := by
    have h1 : (∏ j ∈ ({a, b} : Finset (Fin k)), (P.e j s : Q)) = ∏ j : Fin k, (P.e j s : Q) :=
      Finset.prod_subset (by intro x _; exact Finset.mem_univ x) (fun x _ hx => by
        rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
        exact hval x hx.1 hx.2)
    rw [← h1, Finset.prod_insert (by simp [hab]), Finset.prod_singleton]
  have hs_eq : s = (P.e a s : Q) * (P.e b s : Q) := by
    rw [← hsplit]
    exact (P.e_prod s).symm
  rw [hs_eq]
  exact Subgroup.mul_mem_sup (P.e_mem a s) (P.e_mem b s)

lemma w1369_ta_isSimple_range {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)}
    {A : Subgroup Q} (hA : w1369_ta_IsSimple Λ A) {φ : ↥A →* Q}
    (hinj : Function.Injective φ)
    (heq : ∀ g (hg : g ∈ Λ) (x : ↥A),
      φ ⟨g (x : Q), hA.2.1 g hg (x : Q) x.2⟩ = g (φ x)) :
    w1369_ta_IsSimple Λ φ.range := by
  have hne : φ.range ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1
    have : φ a ∈ (⊥ : Subgroup Q) := by rw [← hbot]; exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
    have ha1 : φ a = φ 1 := by rw [Subgroup.mem_bot.mp this, map_one]
    exact ha (hinj ha1)
  refine ⟨hne, ?_, ?_⟩
  · intro g hg y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
    exact MonoidHom.mem_range.mpr ⟨⟨g (x : Q), hA.2.1 g hg (x : Q) x.2⟩, heq g hg x⟩
  · intro J hJ hJle
    let K : Subgroup Q := (Subgroup.comap φ J).map A.subtype
    have hKle : K ≤ A := Subgroup.map_subtype_le _
    have hKstab : StableUnder Λ K := by
      intro g hg y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      have hxJ : φ x ∈ J := hx
      refine Subgroup.mem_map.mpr ⟨⟨g (x : Q), hA.2.1 g hg (x : Q) x.2⟩, ?_, rfl⟩
      change φ ⟨g (x : Q), hA.2.1 g hg (x : Q) x.2⟩ ∈ J
      rw [heq g hg x]
      exact hJ g hg (φ x) hxJ
    rcases hA.2.2 K hKstab hKle with hK | hK
    · left
      rw [← le_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp (hJle hy)
      have hxK : (x : Q) ∈ K := Subgroup.mem_map.mpr ⟨x, hy, rfl⟩
      rw [hK, Subgroup.mem_bot] at hxK
      have hx1 : x = 1 := Subtype.ext hxK
      rw [hx1, map_one]
      exact Subgroup.one_mem ⊥
    · right
      refine le_antisymm hJle ?_
      intro y hy
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hy
      have hxK : (x : Q) ∈ K := by rw [hK]; exact x.2
      obtain ⟨x', hx'J, hx'eq⟩ := Subgroup.mem_map.mp hxK
      have hxx' : x' = x := Subtype.ext hx'eq
      rw [← hxx']
      exact hx'J

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
