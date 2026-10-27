module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136CentBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SevenSq

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

variable {Q : Type} [CommGroup Q] {Λ : Subgroup (MulAut Q)} {k : ℕ} {I : Fin k → Subgroup Q}

@[expose] def w1369_compl (s : Fin k) : Subgroup Q :=
  ⨆ (l : Fin k) (_ : l ≠ s), I l

theorem w1369_cent_preserves_compl (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {f : MulAut Q} (hf : f ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) {s : Fin k}
    (hs : w1369_Singleton Λ I s) {j : Fin k} (hj : j ≠ s) :
    ∀ v ∈ I j, f v ∈ w1369_compl (I := I) s := by
  classical
  intro v hv
  have hc := w1369_s16h_cent_comm hf
  have hkill : P.e s (f v) = 1 := by
    rcases w1369_s16h_block_one_or_bij P hstab hsimple hc s j with h1 | hbij
    · have h := congrArg (fun g : I j →* I s => (g ⟨v, hv⟩ : Q)) h1
      rw [w1369_s16h_block_coe P f s j ⟨v, hv⟩] at h
      simpa using h
    · exact absurd (w1369_iso_symm hstab (w1369_iso_of_bij_block hstab hc j s hbij))
        (hs j hj)
  have hprod : f v = ∏ l ∈ Finset.univ.erase s, P.e l (f v) := by
    conv_lhs => rw [← P.e_prod (f v)]
    rw [← Finset.prod_erase_mul Finset.univ (fun l => P.e l (f v)) (Finset.mem_univ s), hkill,
      mul_one]
  rw [hprod]
  refine Subgroup.prod_mem _ (fun l hl => ?_)
  exact Subgroup.mem_iSup_of_mem l
    (Subgroup.mem_iSup_of_mem (Finset.mem_erase.mp hl).1 (P.e_mem l (f v)))

theorem w1369_stable_of_stable_subgroupOf {K : Subgroup Q} (hΛK : Λ ≤ stabSub K)
    {A : Subgroup Q} (hAK : A ≤ K)
    (h : StableUnder (autSub Λ K) (A.subgroupOf K)) : StableUnder Λ A := by
  intro l hl x hx
  have hg : resHom K ⟨l, hΛK hl⟩ ∈ autSub Λ K :=
    mem_autSub.mpr ⟨⟨l, hΛK hl⟩, hl, rfl⟩
  have hx' : (⟨x, hAK hx⟩ : K) ∈ A.subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr hx
  have hmem := h (resHom K ⟨l, hΛK hl⟩) hg ⟨x, hAK hx⟩ hx'
  have h2 : ((resHom K ⟨l, hΛK hl⟩ ⟨x, hAK hx⟩ : K) : Q) = l x := rfl
  rwa [Subgroup.mem_subgroupOf, h2] at hmem

theorem w1369_secIsoOn_subgroupOf {K : Subgroup Q} (hΛK : Λ ≤ stabSub K) {A B : Subgroup Q}
    (hAK : A ≤ K) (hBK : B ≤ K)
    (h : SecIsoOn (autSub Λ K) (A.subgroupOf K) ⊥ (B.subgroupOf K) ⊥) :
    SecIsoOn Λ A ⊥ B ⊥ := by
  classical
  obtain ⟨-, -, hAstab, -, hBstab, -, β, hβB, hβbot, hβsurj, hβeq⟩ := h
  have hAstable : StableUnder Λ A := w1369_stable_of_stable_subgroupOf hΛK hAK hAstab
  have hBstable : StableUnder Λ B := w1369_stable_of_stable_subgroupOf hΛK hBK hBstab
  let e : A.subgroupOf K ≃* A := Subgroup.subgroupOfEquivOfLe hAK
  let β' : A →* Q := K.subtype.comp (β.comp e.symm.toMonoidHom)
  have hβ'apply : ∀ a : A, β' a = (β (e.symm a) : Q) := fun a => rfl
  refine ⟨bot_le, bot_le, hAstable, ?_, hBstable, ?_, β', ?_, ?_, ?_, ?_⟩
  · intro l hl x hx
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, map_one]
  · intro l hl x hx
    rw [Subgroup.mem_bot] at hx ⊢
    rw [hx, map_one]
  · intro a
    rw [hβ'apply]
    exact Subgroup.mem_subgroupOf.mp (hβB (e.symm a))
  · intro a
    rw [hβ'apply, Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h1
      have h2 : β (e.symm a) = 1 := Subtype.ext (by simpa using h1)
      have h3 : (e.symm a : A.subgroupOf K) = 1 := by
        apply Subtype.ext
        exact Subgroup.mem_bot.mp ((hβbot (e.symm a)).mp h2)
      have h4 : a = 1 := by
        have := congrArg (fun z : A.subgroupOf K => (e z : A)) h3
        simpa using this
      rw [h4]
      rfl
    · intro h1
      have h2 : e.symm a = 1 := Subtype.ext (Subtype.ext h1)
      rw [h2, map_one]
      rfl
  · intro b hb
    let bK : K := ⟨b, hBK hb⟩
    have hb' : bK ∈ B.subgroupOf K := Subgroup.mem_subgroupOf.mpr hb
    obtain ⟨a', ha'⟩ := hβsurj bK hb'
    refine ⟨e a', ?_⟩
    rw [Subgroup.mem_bot]
    have h1 : β a' = bK := by
      have h2 : β a' * bK⁻¹ = 1 := by simpa using (Subgroup.mem_bot.mp ha')
      exact mul_inv_eq_one.mp h2
    have h3 : β' (e a') = b := by
      rw [hβ'apply]
      change (β (e.symm (e a')) : Q) = b
      rw [e.symm_apply_apply]
      exact congrArg (fun z : K => (z : Q)) h1
    rw [h3, mul_inv_cancel]
  · intro l hl a a' ha
    have hg : resHom K ⟨l, hΛK hl⟩ ∈ autSub Λ K :=
      mem_autSub.mpr ⟨⟨l, hΛK hl⟩, hl, rfl⟩
    have ha'' : ((e.symm a' : A.subgroupOf K) : K) =
        resHom K ⟨l, hΛK hl⟩ (e.symm a) := by
      apply Subtype.ext
      change (a' : Q) = l (a : Q)
      exact ha
    have hkey := hβeq (resHom K ⟨l, hΛK hl⟩) hg (e.symm a) (e.symm a') ha''
    rw [Subgroup.mem_bot] at hkey
    rw [Subgroup.mem_bot]
    have h1 : β (e.symm a') = resHom K ⟨l, hΛK hl⟩ (β (e.symm a)) :=
      mul_inv_eq_one.mp hkey
    apply mul_inv_eq_one.mpr
    rw [hβ'apply, hβ'apply]
    change (β (e.symm a') : Q) = l (β (e.symm a) : Q)
    rw [h1]
    rfl

@[expose] noncomputable def w1369_complProj (P : w1369_s16h_Proj I Λ) (s : Fin k) : Q →* Q where
  toFun x := x * (P.e s x)⁻¹
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, mul_inv_rev]
    ac_rfl

@[simp] theorem w1369_complProj_apply (P : w1369_s16h_Proj I Λ) (s : Fin k) (x : Q) :
    w1369_complProj P s x = x * (P.e s x)⁻¹ := rfl

theorem w1369_complProj_mem (P : w1369_s16h_Proj I Λ) (s : Fin k) (x : Q) :
    w1369_complProj P s x ∈ w1369_compl (I := I) s := by
  have hx : x = (∏ l ∈ Finset.univ.erase s, P.e l x) * P.e s x := by
    nth_rewrite 1 [← P.e_prod x]
    rw [Finset.prod_erase_mul Finset.univ (fun l => P.e l x) (Finset.mem_univ s)]
  have h : w1369_complProj P s x = ∏ l ∈ Finset.univ.erase s, P.e l x := by
    rw [w1369_complProj_apply]
    nth_rewrite 1 [hx]
    rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [h]
  refine Subgroup.prod_mem _ (fun l hl => ?_)
  exact Subgroup.mem_iSup_of_mem l
    (Subgroup.mem_iSup_of_mem (Finset.mem_erase.mp hl).1 (P.e_mem l x))

theorem w1369_cent_maps_compl (P : w1369_s16h_Proj I Λ)
    (hstab : ∀ i, ∀ g ∈ Λ, ∀ x ∈ I i, g x ∈ I i)
    (hsimple : ∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i →
      J = ⊥ ∨ J = I i)
    {f : MulAut Q} (hf : f ∈ Subgroup.centralizer (Λ : Set (MulAut Q))) {s : Fin k}
    (hs : w1369_Singleton Λ I s) :
    ∀ v ∈ w1369_compl (I := I) s, f v ∈ w1369_compl (I := I) s := by
  intro v hv
  have hle : (w1369_compl (I := I) s).map (f : Q →* Q) ≤ w1369_compl (I := I) s := by
    rw [w1369_compl, iSup_subtype', Subgroup.map_iSup]
    refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    have h := w1369_cent_preserves_compl P hstab hsimple hf hs j.2 x hx
    rwa [w1369_compl, iSup_subtype'] at h
  exact hle (Subgroup.mem_map.mpr ⟨v, hv, rfl⟩)

theorem w1369_map_compl_le (hstab : ∀ i, StableUnder Λ (I i)) {l : MulAut Q} (hl : l ∈ Λ)
    (s : Fin k) :
    (w1369_compl (I := I) s).map (l : Q →* Q) ≤ w1369_compl (I := I) s := by
  rw [w1369_compl, iSup_subtype', Subgroup.map_iSup]
  refine iSup_le fun j => ?_
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_iSup_of_mem j (hstab j.1 l hl x hx)

theorem w1369_stable_compl (hstab : ∀ i, StableUnder Λ (I i)) (s : Fin k) :
    StableUnder Λ (w1369_compl (I := I) s) := by
  intro l hl v hv
  have hle := w1369_map_compl_le hstab hl s
  have hge : w1369_compl (I := I) s ≤ (w1369_compl (I := I) s).map (l : Q →* Q) := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨(l⁻¹ : MulAut Q) x,
        w1369_map_compl_le hstab (Λ.inv_mem hl) s (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), by simp⟩
  have hmap : (w1369_compl (I := I) s).map (l : Q →* Q) = w1369_compl (I := I) s :=
    le_antisymm hle hge
  exact hmap ▸ Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

theorem w1369_compl_eq_iSup (s : Fin k) :
    w1369_compl (I := I) s = ⨆ j : {j : Fin k // j ≠ s}, I j.1 := by
  rw [w1369_compl, iSup_subtype']

theorem w1369_sup_compl (s : Fin k) :
    I s ⊔ w1369_compl (I := I) s = ⨆ i, I i := by
  apply le_antisymm
  · refine sup_le (le_iSup (fun i : Fin k => I i) s) ?_
    rw [w1369_compl_eq_iSup]
    exact iSup_le fun j => le_iSup (fun i : Fin k => I i) j.1
  · refine iSup_le fun i => ?_
    by_cases his : i = s
    · subst his; exact le_sup_left
    · refine le_sup_of_le_right ?_
      rw [w1369_compl_eq_iSup]
      exact le_iSup (fun j : {j : Fin k // j ≠ s} => I j.1) ⟨i, his⟩

theorem w1369_cent_dichotomy_aux :
    ∀ k : ℕ, ∀ {Q : Type} [CommGroup Q] [Finite Q], (∀ x : Q, x ^ 2 = 1) →
      ∀ {Λ : Subgroup (MulAut Q)} {I : Fin k → Subgroup Q},
        (∀ i, StableUnder Λ (I i)) →
        (∀ i, I i ≠ ⊥ ∧ ∀ J : Subgroup Q, StableUnder Λ J → J ≤ I i →
          J = ⊥ ∨ J = I i) →
        (⨆ i, I i = ⊤) →
        (∀ i, I i ⊓ (⨆ (j : Fin k) (_ : j ≠ i), I j) = ⊥) →
        (∀ i j, i ≠ j → SecIsoOn Λ (I i) ⊥ (I j) ⊥ → ∀ f : Q →* Q,
          (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) → (∀ x ∈ I i, f x ∈ I i) →
          (∀ j', j' ≠ i → ∀ x ∈ I j', f x = 1) →
          (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1)) →
        k ≤ 3 →
        ∀ {X : Subgroup (MulAut Q)}, X ≤ Subgroup.centralizer (Λ : Set (MulAut Q)) →
        ⁅X, X⁆ = X →
        X = ⊥ ∨ (k = 3 ∧ (∀ i j, SecIsoOn Λ (I i) ⊥ (I j) ⊥) ∧ Nat.card X = 168 ∧
          (∀ i, Nat.card (I i) ^ 3 = Nat.card Q)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h n ih =>
    intro Q instCG instFin hQ Λ I hstab hsimple hspan hind hend hk X hXc hXp
    cases n with
    | zero =>
      left
      have htopbot : (⊤ : Subgroup Q) = ⊥ := by
        rw [← hspan]
        exact iSup_of_empty I
      haveI : Subsingleton Q := by
        refine ⟨fun a b => ?_⟩
        have ha : a = 1 := Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top a)
        have hb : b = 1 := Subgroup.mem_bot.mp (htopbot ▸ Subgroup.mem_top b)
        rw [ha, hb]
      haveI : Subsingleton (MulAut Q) :=
        ⟨fun f g => by ext q; exact Subsingleton.elim _ _⟩
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact Subsingleton.elim x 1
    | succ m =>
      by_cases hsing : ∃ s : Fin (m + 1), w1369_Singleton Λ I s
      · obtain ⟨s, hs⟩ := hsing
        let P : w1369_s16h_Proj I Λ := w1369_s16h_mkProj hstab hspan hind
        let Q' : Subgroup Q := w1369_compl (I := I) s
        have hQ'stable : StableUnder Λ Q' := w1369_stable_compl hstab s
        have hΛQ' : Λ ≤ stabSub Q' := by
          intro l hl
          rw [mem_stabSub]
          intro x
          exact ⟨fun hx => by
            have h := hQ'stable l⁻¹ (Λ.inv_mem hl) (l x) hx
            simpa using h, fun hx => hQ'stable l hl x hx⟩
        have hXQ' : X ≤ stabSub Q' := by
          intro x hx
          rw [mem_stabSub]
          intro v
          exact ⟨fun hv => by
              have h := w1369_cent_maps_compl P hstab hsimple (hXc (X.inv_mem hx)) hs (x v) hv
              simpa using h,
            fun hv => w1369_cent_maps_compl P hstab hsimple (hXc hx) hs v hv⟩
        let Λ' : Subgroup (MulAut Q') := autSub Λ Q'
        let X' : Subgroup (MulAut Q') := autSub X Q'
        let I' : Fin m → Subgroup Q' := fun a => (I (Fin.succAbove s a)).subgroupOf Q'
        have hIQ' : ∀ j, j ≠ s → I j ≤ Q' := by
          intro j hj
          change I j ≤ w1369_compl (I := I) s
          rw [w1369_compl_eq_iSup]
          exact le_iSup (fun j : {j : Fin (m + 1) // j ≠ s} => I j.1) ⟨j, hj⟩
        have hQ'exp : ∀ x : Q', x ^ 2 = 1 := fun x => Subtype.ext (by simpa using hQ (x : Q))
        have hstab' : ∀ a, StableUnder Λ' (I' a) := by
          intro a g hg x hx
          obtain ⟨g', hg'Λ, rfl⟩ := mem_autSub.mp hg
          exact Subgroup.mem_subgroupOf.mpr
            (hstab (Fin.succAbove s a) g' hg'Λ (x : Q) (Subgroup.mem_subgroupOf.mp hx))
        have hsimple' : ∀ a, I' a ≠ ⊥ ∧ ∀ J : Subgroup Q', StableUnder Λ' J → J ≤ I' a →
            J = ⊥ ∨ J = I' a := by
          intro a
          constructor
          · intro hbot
            have hle : I (Fin.succAbove s a) ≤ Q' := hIQ' _ (Fin.succAbove_ne s a)
            have hzero : I (Fin.succAbove s a) = ⊥ := by
              rw [Subgroup.eq_bot_iff_forall]
              intro x hx
              have hx' : (⟨x, hle hx⟩ : Q') ∈ I' a := Subgroup.mem_subgroupOf.mpr hx
              rw [hbot] at hx'
              exact Subtype.ext_iff.mp (Subgroup.mem_bot.mp hx')
            exact (hsimple (Fin.succAbove s a)).1 hzero
          · intro J hJstab hJle
            let Jq : Subgroup Q := J.map Q'.subtype
            have hJq_le : Jq ≤ I (Fin.succAbove s a) := by
              rintro y ⟨x, hx, rfl⟩
              exact Subgroup.mem_subgroupOf.mp (hJle hx)
            have hJq_stab : StableUnder Λ Jq := by
              intro l hl y hy
              obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
              have hg : resHom Q' ⟨l, hΛQ' hl⟩ ∈ Λ' :=
                mem_autSub.mpr ⟨⟨l, hΛQ' hl⟩, hl, rfl⟩
              have h := hJstab _ hg x hx
              exact Subgroup.mem_map.mpr ⟨resHom Q' ⟨l, hΛQ' hl⟩ x, h, rfl⟩
            rcases (hsimple (Fin.succAbove s a)).2 Jq hJq_stab hJq_le with hbot | htop
            · left
              rw [Subgroup.eq_bot_iff_forall]
              intro x hx
              have hxq : (x : Q) ∈ Jq := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
              rw [hbot] at hxq
              exact Subtype.ext (Subgroup.mem_bot.mp hxq)
            · right
              apply le_antisymm hJle
              intro x hx
              have hxq : (x : Q) ∈ Jq := by
                rw [htop]
                exact Subgroup.mem_subgroupOf.mp hx
              obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxq
              rwa [Subtype.ext hyx] at hy
        have hreindex : (⨆ a : Fin m, I (Fin.succAbove s a)) = Q' := by
          change (⨆ a : Fin m, I (Fin.succAbove s a)) = w1369_compl (I := I) s
          rw [w1369_compl_eq_iSup]
          apply le_antisymm
          · refine iSup_le fun a => le_iSup
              (fun j : {j : Fin (m + 1) // j ≠ s} => I j.1)
              ⟨Fin.succAbove s a, Fin.succAbove_ne s a⟩
          · refine iSup_le fun j => ?_
            obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq j.2
            rw [← ha]
            exact le_iSup (fun a : Fin m => I (Fin.succAbove s a)) a
        have hspan' : ⨆ a, I' a = ⊤ := by
          rw [eq_top_iff]
          intro x _
          have hx : (x : Q) ∈ (⨆ a : Fin m, I' a).map Q'.subtype := by
            rw [Subgroup.map_iSup]
            have hcongr : ∀ a : Fin m, (I' a).map Q'.subtype = I (Fin.succAbove s a) :=
              fun a => Subgroup.map_subgroupOf_eq_of_le (hIQ' _ (Fin.succAbove_ne s a))
            rw [iSup_congr hcongr, hreindex]
            exact x.2
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
          rwa [Subtype.ext hyx] at hy
        have hind' : ∀ a, I' a ⊓ (⨆ (b : Fin m) (_ : b ≠ a), I' b) = ⊥ := by
          intro a
          rw [eq_bot_iff]
          intro x hx
          have hx1 : (x : Q) ∈ I (Fin.succAbove s a) := Subgroup.mem_subgroupOf.mp hx.1
          have hx2 : (x : Q) ∈ ⨆ (j : Fin (m + 1)) (_ : j ≠ Fin.succAbove s a), I j := by
            have hle : (⨆ (b : Fin m) (_ : b ≠ a), I' b) ≤
                (⨆ (j : Fin (m + 1)) (_ : j ≠ Fin.succAbove s a), I j).subgroupOf Q' := by
              refine iSup_le fun b => iSup_le fun hba => ?_
              intro y hy
              rw [Subgroup.mem_subgroupOf]
              refine Subgroup.mem_iSup_of_mem (Fin.succAbove s b) (Subgroup.mem_iSup_of_mem ?_
                (Subgroup.mem_subgroupOf.mp hy))
              intro h
              exact hba (Fin.succAbove_right_injective h)
            exact Subgroup.mem_subgroupOf.mp (hle hx.2)
          have hmem : (x : Q) ∈ I (Fin.succAbove s a) ⊓
              (⨆ (j : Fin (m + 1)) (_ : j ≠ Fin.succAbove s a), I j) :=
            Subgroup.mem_inf.mpr ⟨hx1, hx2⟩
          rw [hind (Fin.succAbove s a), Subgroup.mem_bot] at hmem
          exact Subtype.ext hmem
        have hend' : ∀ a b, a ≠ b → SecIsoOn Λ' (I' a) ⊥ (I' b) ⊥ → ∀ f : Q' →* Q',
            (∀ g ∈ Λ', ∀ x, f (g x) = g (f x)) → (∀ x ∈ I' a, f x ∈ I' a) →
            (∀ b', b' ≠ a → ∀ x ∈ I' b', f x = 1) →
            (∀ x ∈ I' a, f x = x) ∨ (∀ x ∈ I' a, f x = 1) := by
          intro a b hab hiso f hfcomm hfmem hfkill
          have hAK : I (Fin.succAbove s a) ≤ Q' := hIQ' _ (Fin.succAbove_ne s a)
          have hBK : I (Fin.succAbove s b) ≤ Q' := hIQ' _ (Fin.succAbove_ne s b)
          have hisoQ : SecIsoOn Λ (I (Fin.succAbove s a)) ⊥ (I (Fin.succAbove s b)) ⊥ :=
            w1369_secIsoOn_subgroupOf hΛQ' hAK hBK (by simpa only [I', Λ'] using hiso)
          let P' : Q →* Q' := (w1369_complProj P s).codRestrict Q' (w1369_complProj_mem P s)
          let F : Q →* Q := Q'.subtype.comp (f.comp P')
          have hP'apply : ∀ x : Q, (P' x : Q) = w1369_complProj P s x := fun x => rfl
          have hFapply : ∀ x : Q, F x = (f (P' x) : Q) := fun x => rfl
          have hFcomm : ∀ g ∈ Λ, ∀ x, F (g x) = g (F x) := by
            intro g hg x
            rw [hFapply, hFapply]
            have hP' : P' (g x) = resHom Q' ⟨g, hΛQ' hg⟩ (P' x) := by
              apply Subtype.ext
              rw [hP'apply, resHom_apply, hP'apply, w1369_complProj_apply,
                w1369_complProj_apply, map_mul, map_inv, ← P.e_equiv s g hg x]
            have hg' : resHom Q' ⟨g, hΛQ' hg⟩ ∈ Λ' :=
              mem_autSub.mpr ⟨⟨g, hΛQ' hg⟩, hg, rfl⟩
            rw [hP', hfcomm (resHom Q' ⟨g, hΛQ' hg⟩) hg' (P' x)]
            rfl
          have hFmem : ∀ x ∈ I (Fin.succAbove s a), F x ∈ I (Fin.succAbove s a) := by
            intro x hx
            rw [hFapply]
            have hP' : P' x = ⟨x, hAK hx⟩ := by
              apply Subtype.ext
              rw [hP'apply, w1369_complProj_apply]
              have : P.e s x = 1 :=
                P.e_other s (Fin.succAbove s a) (Fin.succAbove_ne s a) x hx
              rw [this, inv_one, mul_one]
            rw [hP']
            exact Subgroup.mem_subgroupOf.mp (hfmem ⟨x, hAK hx⟩ (Subgroup.mem_subgroupOf.mpr hx))
          have hFkill : ∀ j, j ≠ Fin.succAbove s a → ∀ x ∈ I j, F x = 1 := by
            intro j hj x hx
            rw [hFapply]
            by_cases hjs : j = s
            · have hP' : P' x = 1 := by
                apply Subtype.ext
                rw [hP'apply, w1369_complProj_apply, P.e_self s x (hjs ▸ hx), mul_inv_cancel]
                rfl
              rw [hP', map_one]
              rfl
            · obtain ⟨b', hb'⟩ := Fin.exists_succAbove_eq hjs
              have hb'a : b' ≠ a := by
                intro h
                exact hj (by rw [← hb', h])
              have hP' : P' x = ⟨x, hIQ' j hjs hx⟩ := by
                apply Subtype.ext
                rw [hP'apply, w1369_complProj_apply]
                have : P.e s x = 1 := P.e_other s j hjs x hx
                rw [this, inv_one, mul_one]
              have hmem : P' x ∈ I' b' := by
                apply Subgroup.mem_subgroupOf.mpr
                rw [hb', show (P' x : Q) = x from congrArg Subtype.val hP']
                exact hx
              have h := hfkill b' hb'a (P' x) hmem
              rw [h]
              rfl
          have hfin := hend (Fin.succAbove s a) (Fin.succAbove s b)
            (fun h => hab (Fin.succAbove_right_injective h)) hisoQ F hFcomm hFmem hFkill
          have hfix : ∀ x ∈ I' a, F (x : Q) = (f x : Q) := by
            intro x hx
            rw [hFapply]
            have hP' : P' (x : Q) = x := by
              apply Subtype.ext
              rw [hP'apply, w1369_complProj_apply]
              have : P.e s (x : Q) = 1 :=
                P.e_other s (Fin.succAbove s a) (Fin.succAbove_ne s a) (x : Q)
                  (Subgroup.mem_subgroupOf.mp hx)
              rw [this, inv_one, mul_one]
            rw [hP']
          rcases hfin with hid | hone
          · left
            intro x hx
            have h := hid (x : Q) (Subgroup.mem_subgroupOf.mp hx)
            rw [hfix x hx] at h
            exact Subtype.ext h
          · right
            intro x hx
            have h := hone (x : Q) (Subgroup.mem_subgroupOf.mp hx)
            rw [hfix x hx] at h
            exact Subtype.ext h
        have hXc' : X' ≤ Subgroup.centralizer (Λ' : Set (MulAut Q')) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro l hl
          obtain ⟨x', hx'X, hx'eq⟩ := mem_autSub.mp hx
          obtain ⟨l', hl'Λ, hl'eq⟩ := mem_autSub.mp hl
          rw [← hx'eq, ← hl'eq]
          apply MulEquiv.ext
          intro v
          apply Subtype.ext
          change (l' : MulAut Q) ((x' : MulAut Q) (v : Q)) =
            (x' : MulAut Q) ((l' : MulAut Q) (v : Q))
          exact (w1369_s16h_cent_comm (hXc hx'X) l' hl'Λ (v : Q)).symm
        have hXp' : ⁅X', X'⁆ = X' :=
          CFSG.Quasithin.B1Red.commutator_autSub_eq hXQ' hXQ' hXp
        have hX'bot : X' = ⊥ := by
          rcases ih m (Nat.lt_succ_self m) (Q := Q') (Λ := Λ') (I := I') hQ'exp
            hstab' hsimple' hspan' hind' hend' (by omega) (X := X') hXc' hXp' with h | h
          · exact h
          · exact absurd h.1 (by omega)
        have hfixQ' : ∀ x ∈ X, ∀ v ∈ Q', x v = v := by
          intro x hx v hv
          have hmem : resHom Q' ⟨x, hXQ' hx⟩ ∈ X' :=
            mem_autSub.mpr ⟨⟨x, hXQ' hx⟩, hx, rfl⟩
          rw [hX'bot] at hmem
          have h1 : resHom Q' ⟨x, hXQ' hx⟩ = 1 := Subgroup.mem_bot.mp hmem
          have h := congrArg (fun g : MulAut Q' => g ⟨v, hv⟩) h1
          exact congrArg (fun z : Q' => (z : Q)) (by simpa using h)
        have hXIs : StableUnder X (I s) := fun x hx v hv =>
          w1369_cent_preserves_singleton (P := P) hstab hsimple (hXc hx) hs v hv
        left
        rw [Subgroup.eq_bot_iff_forall]
        intro x hx
        ext q
        have hq : q ∈ I s ⊔ Q' := by
          rw [w1369_sup_compl, hspan]
          exact Subgroup.mem_top q
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hq
        rw [map_mul, w1369_perfect_trivial_of_simple hQ (hstab s) (hsimple s) hXIs hXc hXp x hx
          a ha, hfixQ' x hx b hb]
        rfl
      ·
        have hns' : ∀ i, ¬ w1369_Singleton Λ I i := fun i hi => hsing ⟨i, hi⟩
        have hdiag : ∀ i, ∀ f : Q →* Q, (∀ g ∈ Λ, ∀ x, f (g x) = g (f x)) →
            (∀ x ∈ I i, f x ∈ I i) → (∀ j, j ≠ i → ∀ x ∈ I j, f x = 1) →
            (∀ x ∈ I i, f x = x) ∨ (∀ x ∈ I i, f x = 1) := by
          intro i f hfcomm hfmem hfkill
          have hnot : ¬ (∀ j, j ≠ i → ¬ w1369_Iso Λ I i j) := hns' i
          rw [not_forall] at hnot
          obtain ⟨j, hj⟩ := hnot
          rw [not_imp] at hj
          obtain ⟨hji, hiso⟩ := hj
          rw [not_not] at hiso
          exact hend i j hji.symm (w1369_secIsoOn_of_iso (hstab i) (hstab j) hiso) f
            hfcomm hfmem hfkill
        let P : w1369_s16h_Proj I Λ := w1369_s16h_mkProj hstab hspan hind
        let M := w1369_s16h_matrixHom hQ P hstab hsimple hdiag
        let φ : X →* GL (Fin (m + 1)) (ZMod 2) := M.comp (Subgroup.inclusion hXc)
        have hφinj : Function.Injective φ :=
          (w1369_s16h_matrixHom_injective hQ P hstab hsimple hdiag).comp
            (Subgroup.inclusion_injective hXc)
        haveI hXperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXp
        haveI hHperf : Group.IsPerfect ↥(φ.range) := Group.IsPerfect.range φ
        have hcardGL : Nat.card (GL (Fin (m + 1)) (ZMod 2)) ∣ 168 := by
          have hm : m ≤ 2 := by omega
          rw [Matrix.card_GL_field]
          interval_cases m
          · rw [Fin.prod_univ_one]; norm_num
          · rw [Fin.prod_univ_two]; norm_num
          · rw [Fin.prod_univ_three]; norm_num
        have hHdvd : Nat.card ↥(φ.range) ∣ 168 := by
          refine (Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)).trans ?_
          simpa only [Subgroup.card_top] using hcardGL
        by_cases hHbot : φ.range = ⊥
        · left
          rw [Subgroup.eq_bot_iff_forall] at hHbot
          rw [Subgroup.eq_bot_iff_forall]
          intro x hx
          have h1 : φ ⟨x, hx⟩ = 1 :=
            hHbot _ (MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩)
          have h2 : φ ⟨x, hx⟩ = φ 1 := by rw [h1, map_one]
          exact Subtype.ext_iff.mp (hφinj h2)
        · right
          have hHnt : Nontrivial ↥(φ.range) := by
            rw [Subgroup.nontrivial_iff_exists_ne_one]
            by_contra hcon
            apply hHbot
            rw [Subgroup.eq_bot_iff_forall]
            intro y hy
            by_contra hy1
            exact hcon ⟨y, hy, hy1⟩
          obtain ⟨-, hHcard⟩ :=
            CFSG.LocalAnalysis.GLTheoremA.KD264Gen.Seven.perfect_dvd_168
              hHperf.commutator_eq_top hHnt hHdvd
          have hGL168 : Nat.card (GL (Fin (m + 1)) (ZMod 2)) = 168 := by
            refine Nat.dvd_antisymm hcardGL ?_
            have h1 : Nat.card ↥(φ.range) ∣ Nat.card (GL (Fin (m + 1)) (ZMod 2)) := by
              simpa only [Subgroup.card_top] using
                (Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤))
            rwa [hHcard] at h1
          have hk3 : m + 1 = 3 := by
            have h := hGL168
            rw [Matrix.card_GL_field] at h
            have hm : m ≤ 2 := by omega
            interval_cases m
            · rw [Fin.prod_univ_one] at h; norm_num at h
            · rw [Fin.prod_univ_two] at h; norm_num at h
            · rfl
          have hcardX : Nat.card ↥X = Nat.card ↥(φ.range) := by
            refine Nat.card_congr (Equiv.ofBijective (fun x : ↥X =>
              (⟨φ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : φ.range)) ⟨?_, ?_⟩)
            · intro a b h
              exact hφinj (Subtype.ext_iff.mp h)
            · intro y
              obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
              exact ⟨x, Subtype.ext hx⟩
          refine ⟨hk3, ?_, hcardX.trans hHcard, ?_⟩
          · intro i j
            by_cases hij : i = j
            · subst hij
              exact w1369_secIsoOn_of_iso (hstab i) (hstab i) (w1369_iso_refl i)
            · exact w1369_secIsoOn_of_iso (hstab i) (hstab j)
                (w1369_nonsing_iso hstab hk (hns' i) (hns' j))
          · intro i
            have hcardQ : Nat.card Q = ∏ i : Fin (m + 1), Nat.card (I i) := by
              have hbij : Function.Bijective (fun x : Q => fun i : Fin (m + 1) =>
                  (⟨P.e i x, P.e_mem i x⟩ : I i)) := by
                constructor
                · intro x y hxy
                  have h : ∀ i, P.e i x = P.e i y := fun i =>
                    congrArg Subtype.val (congrFun hxy i)
                  calc x = ∏ i, P.e i x := (P.e_prod x).symm
                    _ = ∏ i, P.e i y := Finset.prod_congr rfl (fun i _ => h i)
                    _ = y := P.e_prod y
                · intro g
                  refine ⟨∏ i, (g i : Q), ?_⟩
                  ext i
                  show P.e i (∏ j, (g j : Q)) = (g i : Q)
                  rw [map_prod, Finset.prod_eq_single_of_mem (s := Finset.univ)
                    (f := fun j => P.e i (g j)) i (Finset.mem_univ i)]
                  · exact P.e_self i (g i) (g i).2
                  · intro j _ hji
                    exact P.e_other i j hji (g j) (g j).2
              have h1 : Nat.card Q = Nat.card (∀ i : Fin (m + 1), I i) :=
                Nat.card_congr (Equiv.ofBijective _ hbij)
              rw [h1, Nat.card_pi]
            have hQ : Nat.card Q = Nat.card (I i) ^
                (Finset.univ : Finset (Fin (m + 1))).card := by
              rw [hcardQ]
              refine Finset.prod_eq_pow_card (fun j _ => ?_)
              obtain ⟨φij, _⟩ := w1369_nonsing_iso hstab hk (hns' i) (hns' j)
              exact (Nat.card_congr φij.toEquiv).symm
            rw [hQ, Finset.card_univ, Fintype.card_fin, hk3]

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
