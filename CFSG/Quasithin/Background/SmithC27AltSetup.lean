module

public import CFSG.Quasithin.Background.SmithC27Frattini
public import CFSG.Quasithin.Background.C124AsmBuild
public import CFSG.Quasithin.Background.C124YZActOdd
public import CFSG.Quasithin.Background.SmithC27Perm
public import CFSG.Quasithin.Background.C124YZJR

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv Equiv.Perm
open scoped Pointwise

section SwapGroup

variable {Ω : Type*} [DecidableEq Ω]

@[expose] def swapGroupOf (z : Perm Ω) (hz : z * z = 1) : Subgroup (Perm Ω) where
  carrier := {g | ∀ x, g x = x ∨ g x = z x}
  one_mem' := fun _ => Or.inl rfl
  mul_mem' := by
    intro g h hg hh x
    have hzz : ∀ y, z (z y) = y := fun y => by
      have := congrArg (fun p : Perm Ω => p y) hz
      simpa using this
    rcases hh x with h1 | h1
    · simp only [Perm.mul_apply, h1]
      exact hg x
    · simp only [Perm.mul_apply, h1]
      rcases hg (z x) with h2 | h2
      · exact Or.inr h2
      · left
        rw [h2, hzz]
  inv_mem' := by
    intro g hg x
    have hzz : ∀ y, z (z y) = y := fun y => by
      have := congrArg (fun p : Perm Ω => p y) hz
      simpa using this
    have hgg : g (g⁻¹ x) = x := by simp
    rcases hg (g⁻¹ x) with h1 | h1
    · left
      rw [hgg] at h1
      exact h1.symm
    · right
      rw [hgg] at h1
      calc g⁻¹ x = z (z (g⁻¹ x)) := (hzz _).symm
        _ = z x := by rw [← h1]

omit [DecidableEq Ω] in
theorem mem_swapGroupOf {z : Perm Ω} {hz : z * z = 1} {g : Perm Ω} :
    g ∈ swapGroupOf z hz ↔ ∀ x, g x = x ∨ g x = z x := Iff.rfl

omit [DecidableEq Ω] in
theorem apply_apply_of_mul_self {z : Perm Ω} (hz : z * z = 1) (x : Ω) : z (z x) = x := by
  have := congrArg (fun p : Perm Ω => p x) hz
  simpa using this

omit [DecidableEq Ω] in
theorem map_conj_swapGroupOf {z : Perm Ω} (hz : z * z = 1) (σ : Perm Ω)
    (hz' : σ * z * σ⁻¹ * (σ * z * σ⁻¹) = 1) :
    (swapGroupOf z hz).map (MulAut.conj σ).toMonoidHom = swapGroupOf (σ * z * σ⁻¹) hz' := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩ x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Perm.mul_apply]
    rcases hh (σ⁻¹ x) with h1 | h1
    · left
      rw [h1]
      simp
    · right
      rw [h1]
  · intro hg
    refine ⟨σ⁻¹ * g * σ, fun x => ?_, by simp [mul_assoc]⟩
    simp only [Perm.mul_apply]
    rcases hg (σ x) with h1 | h1
    · left
      rw [h1]
      simp
    · right
      rw [h1]
      simp

variable [Fintype Ω]

theorem exists_eq_swapGroupOf {D : Subgroup (Perm Ω)} (hsw : C124.YZ.IsSwapGroup D)
    (hp : IsPGroup 2 D) : ∃ (z : Perm Ω) (hz : z * z = 1), z ∈ D ∧ D = swapGroupOf z hz := by
  classical
  obtain ⟨z, hzD, hmax⟩ : ∃ z ∈ D, ∀ g ∈ D, g.support.card ≤ z.support.card := by
    obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (· ∈ D))
      (fun g : Perm Ω => g.support.card) ⟨1, by simp⟩
    exact ⟨z, by simpa using hz, fun g hg => hmax g (by simpa using hg)⟩
  have hzz : ∀ x, z (z x) = x := by
    intro x
    by_cases hx : z x = x
    · rw [hx, hx]
    · have h1 : swap (z x) x ∈ D := by
        rw [swap_comm]
        exact (hsw z hzD x).resolve_left hx
      by_cases hy : z (z x) = z x
      · exact absurd (z.injective hy) hx
      · have h2 := (hsw z hzD (z x)).resolve_left hy
        exact (C124.YZ.eq_of_swap_mem_swap_mem hp hx (Ne.symm hy) h1 h2).symm
  have hz2 : z * z = 1 := Equiv.ext fun x => by simp [Perm.mul_apply, hzz]
  refine ⟨z, hz2, hzD, le_antisymm (fun g hg x => ?_) (fun g hg => ?_)⟩
  · by_cases hgx : g x = x
    · exact Or.inl hgx
    · right
      have hs : swap x (g x) ∈ D := (hsw g hg x).resolve_left hgx
      by_cases hzx : z x = x
      · exfalso
        have hzy : z (g x) = g x := by
          by_contra hzy
          have h2 := (hsw z hzD (g x)).resolve_left hzy
          have h1 : swap (g x) x ∈ D := by rwa [swap_comm] at hs
          have h3 := C124.YZ.eq_of_swap_mem_swap_mem hp hgx (Ne.symm hzy) h1 h2
          apply hgx
          calc g x = z (z (g x)) := (hzz _).symm
            _ = z x := by rw [← h3]
            _ = x := hzx
        have hD' : z * swap x (g x) ∈ D := D.mul_mem hzD hs
        have hsub : insert x (insert (g x) z.support) ⊆ (z * swap x (g x)).support := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rw [Perm.mem_support, Perm.mul_apply]
          rcases hw with rfl | rfl | hw
          · rw [swap_apply_left, hzy]
            exact hgx
          · rw [swap_apply_right, hzx]
            exact Ne.symm hgx
          · have hwz : z w ≠ w := Perm.mem_support.1 hw
            have hwx : w ≠ x := fun e => hwz (e ▸ hzx)
            have hwy : w ≠ g x := fun e => hwz (e ▸ hzy)
            rw [swap_apply_of_ne_of_ne hwx hwy]
            exact hwz
        have hxn : x ∉ insert (g x) z.support := by
          rw [Finset.mem_insert, Perm.mem_support]
          rintro (h | h)
          · exact hgx h.symm
          · exact h hzx
        have hyn : g x ∉ z.support := by
          rw [Perm.mem_support]
          exact fun h => h hzy
        have hc := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hxn, Finset.card_insert_of_notMem hyn] at hc
        have := hmax _ hD'
        omega
      · have hs' : swap x (z x) ∈ D := (hsw z hzD x).resolve_left hzx
        exact C124.YZ.eq_of_swap_mem_swap_mem hp (Ne.symm hgx) (Ne.symm hzx) hs hs'
  · refine C124.YZ.IsSwapGroup.mem_of hsw g fun x => ?_
    rcases hg x with h | h
    · exact Or.inl h
    · by_cases hzx : z x = x
      · left
        rw [h, hzx]
      · right
        rw [h]
        exact (hsw z hzD x).resolve_left hzx

theorem swapGroupOf_eq_closure {z : Perm Ω} (hz : z * z = 1) :
    swapGroupOf z hz = Subgroup.closure (swapsOf z) := by
  have hzz := apply_apply_of_mul_self hz
  have hge : Subgroup.closure (swapsOf z) ≤ swapGroupOf z hz := by
    rw [Subgroup.closure_le]
    rintro s ⟨x, -, rfl⟩ y
    by_cases hy : y = x
    · subst hy
      right
      rw [swap_apply_left]
    · by_cases hy' : y = z x
      · subst hy'
        right
        rw [swap_apply_right, hzz]
      · left
        exact swap_apply_of_ne_of_ne hy hy'
  refine le_antisymm (fun g hg => ?_) hge
  have hsw : C124.YZ.IsSwapGroup (Subgroup.closure (swapsOf z)) := by
    intro d hd x
    rcases hge hd x with h | h
    · exact Or.inl h
    · by_cases hzx : z x = x
      · exact Or.inl (h.trans hzx)
      · right
        rw [h]
        exact Subgroup.subset_closure ⟨x, hzx, rfl⟩
  refine C124.YZ.IsSwapGroup.mem_of hsw g fun x => ?_
  rcases hg x with h | h
  · exact Or.inl h
  · by_cases hzx : z x = x
    · exact Or.inl (h.trans hzx)
    · right
      rw [h]
      exact Subgroup.subset_closure ⟨x, hzx, rfl⟩

theorem normalizer_swapGroupOf {z : Perm Ω} (hz : z * z = 1) :
    Subgroup.normalizer (swapGroupOf z hz : Set (Perm Ω)) = Subgroup.centralizer {z} := by
  rw [swapGroupOf_eq_closure, normalizer_closure_swapsOf (apply_apply_of_mul_self hz)]

theorem cycleType_of_mul_self {z : Perm Ω} (hz : z * z = 1) :
    z.cycleType = Multiset.replicate (z.support.card / 2) 2 := by
  have h2 : ∀ a ∈ z.cycleType, a = 2 := by
    intro a ha
    have h1 : a ∣ orderOf z := Perm.dvd_of_mem_cycleType ha
    have h3 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hz])
    have h4 : 2 ≤ a := Perm.two_le_of_mem_cycleType ha
    have h5 : a ∣ 2 := h1.trans h3
    have h6 : a ≤ 2 := Nat.le_of_dvd (by norm_num) h5
    omega
  have hrep : z.cycleType = Multiset.replicate (Multiset.card z.cycleType) 2 :=
    Multiset.eq_replicate_card.2 h2
  have hsum := Perm.sum_cycleType z
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hrep]
  congr 1
  omega

theorem exists_conj_of_mul_self {z w : Perm Ω} (hz : z * z = 1) (hw : w * w = 1)
    (hc : z.support.card = w.support.card) : ∃ σ : Perm Ω, σ * z * σ⁻¹ = w := by
  have : IsConj z w := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_of_mul_self hz, cycleType_of_mul_self hw, hc]
  exact isConj_iff.1 this

end SwapGroup

section Std

variable (n : ℕ) [NeZero n]

@[expose] def stdInv : ℕ → Perm (Fin n)
  | 0 => 1
  | 1 => swap 0 1
  | 2 => swap 0 1 * swap 2 3
  | _ => swap 0 1 * swap 2 3 * swap 4 5

end Std

section Entry

variable {G : Type} [Group G] [Finite G]

theorem not_le_normalizer_of_char_baum {H R M K : Subgroup G} (h : Hyp27 H R M K)
    {C : Subgroup G} (hC1 : C ≠ ⊥) (hCB : C ≤ baum R)
    (hchar : (C.subgroupOf (baum R)).Characteristic) :
    ¬ K ⊔ R ≤ Subgroup.normalizer (C : Set G) := by
  intro hX
  apply h.not_le
  have hCR : C ≤ R := hCB.trans (C1GN.baum_le R)
  have hcharR : (C.subgroupOf R).Characteristic :=
    C1GN.characteristic_subgroupOf_trans (C1GN.baum_le R) hCB (C1GN.characteristic_baum R) hchar
  have hle : H ⊓ Subgroup.normalizer (C : Set G) ≤ cgsIn H R :=
    le_iSup_of_le C (le_iSup_of_le hCR (le_iSup_of_le hC1 (le_iSup_of_le hcharR le_rfl)))
  intro k hk
  exact h.hyp.cgs (hle ⟨h.K_le hk, hX (Subgroup.mem_sup_left hk)⟩)

theorem entryPlus_of_hyp27 (hI : B5.B51IrrInputs) (hA21 : AsA21SQTKSection)
    (hA36 : AsA36NoOddCover) {H R M K : Subgroup G} (h : Hyp27 H R M K) {m : ℕ}
    (hm : m = 5 ∨ m = 7) (halt : IsAltQuotient K (oTwoZIn K) m) {T : Subgroup G}
    (hT : IsSylowTwoOf T (K ⊔ R)) (hRT : R ≤ T) :
    C124.EntryPlus (K ⊔ R) T (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) K R m
      (isElemAbelian_omegaOneCenterOf _) := by
  have hm' : m = 5 ∨ m = 7 ∨ (m = 6 ∧ R ≤ K ⊔ ((K ⊔ R) ⊓ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G))) ∨
      (m = 6 ∧ Nat.card ↥(autOn R (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) = 2) :=
    hm.elim Or.inl (fun h7 => Or.inr (Or.inl h7))
  rcases C124.entryPlus_or_concl1 hI hA21 hA36 h.charTwo_sup h.hypC23_sup.sqtk h.isTwoReducedIn
      hT (h.starHyp.prod_of_le hRT) h.mem_cComp_sup h.charTwo h.starHyp.commutator_ne_bot halt
      h.pCoreOf_sup_le
      hRT hm' with ⟨C, hC1, hCB, hchar, hXC⟩ | E
  · exact absurd hXC (not_le_normalizer_of_char_baum h hC1 hCB hchar)
  · exact E

end Entry

section AltQuot

variable {G : Type} [Group G]

theorem center_alternatingGroup_eq_bot {m : ℕ} (hm : m = 5 ∨ m = 7) :
    Subgroup.center (alternatingGroup (Fin m)) = ⊥ := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := C124.alt_noncomm (m := m) (by omega)
    have ha : a ∈ Subgroup.center (alternatingGroup (Fin m)) := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

theorem center_quot_eq_bot_of_surj {K : Subgroup G} {m : ℕ} (hm : m = 5 ∨ m = 7)
    (α : ↥K →* alternatingGroup (Fin m)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
  let e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* alternatingGroup (Fin m) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα)
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center (alternatingGroup (Fin m)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y)]
  rw [center_alternatingGroup_eq_bot hm, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem isAltQuotient_of_surj {K : Subgroup G} {m : ℕ} (hm : m = 5 ∨ m = 7)
    (α : ↥K →* alternatingGroup (Fin m)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) : IsAltQuotient K (oTwoZIn K) m := by
  have hZ := center_quot_eq_bot_of_surj hm α hα hker
  refine ⟨α, hα, ?_⟩
  rw [hker, oTwoZIn_eq_of_center_eq_bot hZ]
  ext y
  rw [Subgroup.mem_subgroupOf, mem_pCore_iff_mem_pCoreOf]

end AltQuot

section Transport

open C124 C124.YZ

variable {G : Type} [Group G] [Finite G] {X T V L R : Subgroup G} {m : ℕ}
  {hV : IsElemAbelian 2 V}

theorem transport_odd_ker (E : Entry X T V L R m hV) (hodd : Odd m) (hm5 : 5 ≤ m)
    {π : ↥(alternatingGroup (Fin m)) →* ↥(autI hV L)}
    (hreal : (FFModel.altDn m).RealizesVia (autI hV L) (commV (autI hV L))
      (fixV (autI hV L) ⊓ commV (autI hV L)) π) (hπ : Function.Injective π) :
    ∃ (ι : ↥(autI hV X) →* Perm (Fin m)) (β : ↥(commV (autI hV L)) →* ↥(G6.coreMod m)),
      Function.Injective ι ∧
      (∀ γ : ↥(alternatingGroup (Fin m)),
        ι (Subgroup.inclusion (autI_mono hV (le_of_mem_cComp E.comp)) (π γ)) = γ) ∧
      Function.Surjective β ∧
      (∀ (g : ↥(autI hV X)) (u : ↥(commV (autI hV L)))
        (hu : (g : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
        β ⟨(g : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
          G6.coreAct m (ι g) (β u)) ∧
      ∀ u : ↥(commV (autI hV L)), β u = 1 → (u : IntMod V hV) ∈ fixV (autI hV L) := by
  classical
  obtain ⟨hπs, -, -, -, -, -, -, β₀, hβ₀s, hβ₀k, hβ₀e⟩ := hreal
  have hLX : L ≤ X := le_of_mem_cComp E.comp
  have hLsXs : autI hV L ≤ autI hV X := autI_mono hV hLX
  have hXsN := autI_normalizes hV E.normal
  let β₁ : ↥(commV (autI hV L)) →* DM m := β₀
  have hβ₁s : Function.Surjective β₁ := hβ₀s
  let β : ↥(commV (autI hV L)) →* ↥(G6.coreMod m) := (dmEquivCore hodd).toMonoidHom.comp β₁
  have hβs : Function.Surjective β := (dmEquivCore hodd).surjective.comp hβ₁s
  have hβπ : ∀ (γ : ↥(alternatingGroup (Fin m))) (u : ↥(commV (autI hV L)))
      (hu : (π γ : MulAut (IntMod V hV)) (u : IntMod V hV) ∈ commV (autI hV L)),
      β ⟨(π γ : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        G6.coreAct m (γ : Perm (Fin m)) (β u) := by
    intro γ u hu
    obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (β₀ u)
    have hact : (FFModel.altDn m).act γ (m₀ : (FFModel.altDn m).Amb) ∈
        (FFModel.altDn m).sec := G6.permAct_mem_coreMod _ m₀.2
    have h1 := hβ₀e γ u m₀ hu hact hm₀.symm
    have h1' : β₁ ⟨(π γ : MulAut (IntMod V hV)) (u : IntMod V hV), hu⟩ =
        (QuotientGroup.mk (⟨(FFModel.altDn m).act γ (m₀ : (FFModel.altDn m).Amb), hact⟩ :
          ↥(G6.coreMod m)) : DM m) := h1
    have hm₀' : β₁ u = (QuotientGroup.mk (m₀ : ↥(G6.coreMod m)) : DM m) := hm₀.symm
    show dmEquivCore hodd (β₁ ⟨_, hu⟩) = G6.coreAct m _ (dmEquivCore hodd (β₁ u))
    rw [h1', hm₀']
    rfl
  have hkerinv : ∀ g ∈ autI hV X, ∀ (u : ↥(commV (autI hV L)))
      (hu : g (u : IntMod V hV) ∈ commV (autI hV L)), β u = 1 →
      β ⟨g (u : IntMod V hV), hu⟩ = 1 := by
    intro g hg u hu h1
    have h2 : β₁ u = 1 := (dmEquivCore hodd).map_eq_one_iff.1 h1
    have h3 := (hβ₀k u).1 h2
    have h4 : g (u : IntMod V hV) ∈ fixV (autI hV L) ⊓ commV (autI hV L) :=
      ⟨apply_mem_fixV (hXsN hg) h3.1, hu⟩
    exact (dmEquivCore hodd).map_eq_one_iff.2 ((hβ₀k _).2 h4)
  obtain ⟨ι, hι, hιπ, hβe⟩ := exists_embedding_of_normalizer hLsXs (commV (autI hV L))
    (fun g hg u hu => apply_mem_commV (hXsN hg) hu)
    (act := G6.coreAct m)
    (fun ρ hρ => G64.symCore_faithful (by omega) ρ fun x hx => by
      have := hρ ⟨x, hx⟩
      have h2 : (G64.symCoreModel m).act ρ x = x := congrArg Subtype.val this
      rw [h2, mul_inv_cancel]
      exact Subgroup.one_mem _)
    (fun φ hφ => B69.exists_perm_of_normalizes hodd hm5 φ hφ)
    π hπs β hβs hβπ hkerinv
    (fun g hg l hl => (Subgroup.mem_normalizer_iff.1 (hXsN hg) l).1 hl)
    (fun g hg hc => eq_one_of_centralizes (by omega) E.fstarX hπs hπ hg hc)
  refine ⟨ι, β, hι, hιπ, hβs, hβe, fun u hu => ?_⟩
  have h2 : β₁ u = 1 := (dmEquivCore hodd).map_eq_one_iff.1 hu
  exact ((hβ₀k u).1 h2).1

end Transport

section Ctx

variable {G : Type} [Group G] [Finite G]

abbrev Vc (R K : Subgroup G) : Subgroup G := omegaOneCenterOf (pCoreOf 2 (K ⊔ R))

abbrev Wc (R K : Subgroup G) : Type := IntMod (Vc R K) (isElemAbelian_omegaOneCenterOf _)

noncomputable abbrev starOf (R K A : Subgroup G) : Subgroup (MulAut (Wc R K)) :=
  autI (isElemAbelian_omegaOneCenterOf _) A

theorem stdInv_facts_five {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k ≤ 5) :
    stdInv 5 k * stdInv 5 k = 1 ∧ (stdInv 5 k).support.card = 2 * k := by
  have hk3 : k ≤ 2 := by omega
  interval_cases k <;> decide

theorem stdInv_facts_seven {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k ≤ 7) :
    stdInv 7 k * stdInv 7 k = 1 ∧ (stdInv 7 k).support.card = 2 * k := by
  have hk3 : k ≤ 3 := by omega
  interval_cases k <;> decide

theorem stdInv_facts {n : ℕ} [NeZero n] (hn : n = 5 ∨ n = 7) {k : ℕ} (hk1 : 1 ≤ k)
    (hk : 2 * k ≤ n) : stdInv n k * stdInv n k = 1 ∧ (stdInv n k).support.card = 2 * k := by
  rcases hn with rfl | rfl
  · exact stdInv_facts_five hk1 hk
  · exact stdInv_facts_seven hk1 hk

structure AltCtx (H R M K : Subgroup G) (n k : ℕ) [NeZero n] where
  hyp : Hyp27 H R M K
  n57 : n = 5 ∨ n = 7
  T : Subgroup G
  sylT : IsSylowTwoOf T (K ⊔ R)
  RT : R ≤ T
  entry : C124.EntryPlus (K ⊔ R) T (Vc R K) K R n (isElemAbelian_omegaOneCenterOf _)
  ι : ↥(starOf R K (K ⊔ R)) →* Perm (Fin n)
  inj : Function.Injective ι
  K_map : C124.YZ.Bmap ι (starOf R K K) = alternatingGroup (Fin n)
  β : ↥(commV (starOf R K K)) →* ↥(G6.coreMod n)
  β_surj : Function.Surjective β
  β_equiv : ∀ (g : ↥(starOf R K (K ⊔ R))) (u : ↥(commV (starOf R K K)))
    (hu : (g : MulAut (Wc R K)) (u : Wc R K) ∈ commV (starOf R K K)),
    β ⟨(g : MulAut (Wc R K)) (u : Wc R K), hu⟩ = G6.coreAct n (ι g) (β u)
  β_ker : ∀ u : ↥(commV (starOf R K K)), β u = 1 → (u : Wc R K) ∈ fixV (starOf R K K)
  k_pos : 1 ≤ k
  k_le : 2 * k ≤ n
  inv_sq : stdInv n k * stdInv n k = 1
  J_map : C124.YZ.Bmap ι (starOf R K (thompsonJ R)) = swapGroupOf (stdInv n k) inv_sq

open C124 C124.YZ in
theorem exists_altCtx {H R M K : Subgroup G} (h : Hyp27 H R M K) {n : ℕ} [NeZero n]
    (hn : n = 5 ∨ n = 7) {T : Subgroup G} (hT : IsSylowTwoOf T (K ⊔ R)) (hRT : R ≤ T)
    (E : EntryPlus (K ⊔ R) T (Vc R K) K R n (isElemAbelian_omegaOneCenterOf _))
    {π : ↥(alternatingGroup (Fin n)) →* ↥(starOf R K K)} (hπ : Function.Injective π)
    (hreal : (FFModel.altDn n).RealizesVia (starOf R K K) (commV (starOf R K K))
      (fixV (starOf R K K) ⊓ commV (starOf R K K)) π) :
    ∃ k, Nonempty (AltCtx H R M K n k) := by
  classical
  set hV := isElemAbelian_omegaOneCenterOf (pCoreOf 2 (K ⊔ R))
  have hodd : Odd n := by rcases hn with rfl | rfl <;> decide
  have hm5 : 5 ≤ n := by omega
  obtain ⟨ι₀, β₀, hι₀, hι₀π, hβ₀s, hβ₀e, hβ₀k⟩ := transport_odd_ker E.toEntry hodd hm5 hreal hπ
  obtain ⟨hSG, hpD', -, -⟩ := jr_facts E.toEntry (modelFactsOdd hodd (Nat.card (autI hV R)))
    le_rfl ι₀ hι₀ β₀ hβ₀s hβ₀e
  obtain ⟨z, hz, hzD, hD⟩ := exists_eq_swapGroupOf hSG hpD'
  have hRX : R ≤ K ⊔ R := le_sup_right
  have hRN : R ≤ Subgroup.normalizer (Vc R K : Set G) := hRX.trans E.red.2.1
  have hJne : Bmap ι₀ (autI hV (thompsonJ R)) ≠ ⊥ := by
    have hDxne : autI hV (thompsonJ R) ≠ ⊥ := fun h0 =>
      E.hJ ((autI_eq_bot_iff hV ((thompsonJ_le R).trans hRN)).1 h0)
    intro h0
    apply hDxne
    refine eq_bot_iff.2 fun g hg => ?_
    have hgX : g ∈ autI hV (K ⊔ R) := (autI_mono hV ((thompsonJ_le R).trans hRX)) hg
    have h1 : ι₀ ⟨g, hgX⟩ ∈ Bmap ι₀ (autI hV (thompsonJ R)) := mem_Bmap.2 ⟨⟨g, hgX⟩, hg, rfl⟩
    rw [h0, Subgroup.mem_bot] at h1
    have := hι₀ (h1.trans (map_one ι₀).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  set k := z.support.card / 2 with hk
  have hzc := cycleType_of_mul_self hz
  have hsum := Perm.sum_cycleType z
  rw [hzc, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hJne
    rw [hD, eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    exact Equiv.ext fun x => (hg x).elim id id
  have hk1 : 1 ≤ k := by
    have h1 : 0 < z.support.card :=
      Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 fun h0 =>
        hz1 (Perm.support_eq_empty_iff.1 h0))
    omega
  have hkn : 2 * k ≤ n := by
    have h1 : z.support.card ≤ n := (Finset.card_le_univ _).trans (by simp)
    omega
  obtain ⟨hstd2, hstdc⟩ := stdInv_facts hn hk1 hkn
  obtain ⟨σ, hσ⟩ := exists_conj_of_mul_self hz hstd2 (by rw [hstdc]; omega)
  let c : Perm (Fin n) →* Perm (Fin n) := (MulAut.conj σ).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj σ).injective
  have hBmap : ∀ A : Subgroup (MulAut (Wc R K)), Bmap (c.comp ι₀) A = (Bmap ι₀ A).map c := by
    intro A
    unfold Bmap
    rw [Subgroup.map_map]
  let β : ↥(commV (starOf R K K)) →* ↥(G6.coreMod n) :=
    (G6.coreAct n σ).toMonoidHom.comp β₀
  refine ⟨k, ⟨⟨h, hn, T, hT, hRT, E, c.comp ι₀, hc.comp hι₀, ?_, β,
    (G6.coreAct n σ).surjective.comp hβ₀s, ?_, ?_, hk1, hkn, hstd2, ?_⟩⟩⟩
  ·
    have h0 : Bmap ι₀ (starOf R K K) = alternatingGroup (Fin n) := by
      apply le_antisymm
      · rintro _ ⟨g, hg, rfl⟩
        obtain ⟨γ, hγ⟩ := hreal.1 ⟨(g : MulAut (Wc R K)), hg⟩
        have : g = Subgroup.inclusion (autI_mono hV (le_of_mem_cComp E.comp)) (π γ) := by
          apply Subtype.ext
          show (g : MulAut (Wc R K)) = ((π γ : ↥(starOf R K K)) : MulAut (Wc R K))
          exact (congrArg Subtype.val hγ).symm
        rw [this]
        exact (hι₀π γ) ▸ γ.2
      · intro γ hγ
        exact mem_Bmap.2 ⟨Subgroup.inclusion (autI_mono hV (le_of_mem_cComp E.comp))
          (π ⟨γ, hγ⟩), (π ⟨γ, hγ⟩).2, hι₀π ⟨γ, hγ⟩⟩
    rw [hBmap, h0]
    ext γ
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact (alternatingGroup.normal (α := Fin n)).conj_mem δ hδ σ
    · intro hγ
      have hδ : σ⁻¹ * γ * σ ∈ alternatingGroup (Fin n) := by
        have := (alternatingGroup.normal (α := Fin n)).conj_mem γ hγ σ⁻¹
        simpa using this
      exact ⟨_, hδ, by simp [c, MulAut.conj_apply, mul_assoc]⟩
  · intro g u hu
    show G6.coreAct n σ (β₀ ⟨_, hu⟩) = G6.coreAct n (σ * ι₀ g * σ⁻¹) (G6.coreAct n σ (β₀ u))
    rw [hβ₀e g u hu, ← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
      inv_mul_cancel_right]
  · intro u hu
    exact hβ₀k u ((G6.coreAct n σ).map_eq_one_iff.1 hu)
  · rw [hBmap, hD, map_conj_swapGroupOf hz σ (by rw [hσ]; exact hstd2)]
    congr 1

end Ctx

section BmapInj

open C124.YZ

variable {W : Type*} [CommGroup W] {m : ℕ} {Xs : Subgroup (MulAut W)}
  {ι : ↥Xs →* Perm (Fin m)}

theorem mem_Bmap_iff_of_injective (hι : Function.Injective ι) {A : Subgroup (MulAut W)}
    (g : ↥Xs) : ι g ∈ Bmap ι A ↔ (g : MulAut W) ∈ A := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    rw [← hι hgg']
    exact hg'
  · intro hg
    exact mem_Bmap.2 ⟨g, hg, rfl⟩

theorem Bmap_inf_of_injective (hι : Function.Injective ι) (A B : Subgroup (MulAut W)) :
    Bmap ι (A ⊓ B) = Bmap ι A ⊓ Bmap ι B := by
  unfold Bmap
  have h : (A ⊓ B).subgroupOf Xs = A.subgroupOf Xs ⊓ B.subgroupOf Xs := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  rw [h]
  exact Subgroup.map_inf_eq _ _ ι hι

theorem Bmap_normalizer_of_bijective (hι : Function.Bijective ι) {J : Subgroup (MulAut W)}
    (hJ : J ≤ Xs) :
    Bmap ι (Subgroup.normalizer (J : Set (MulAut W))) =
      Subgroup.normalizer (Bmap ι J : Set (Perm (Fin m))) := by
  ext σ
  obtain ⟨g, rfl⟩ := hι.2 σ
  rw [mem_Bmap_iff_of_injective hι.1, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg τ
    obtain ⟨t, rfl⟩ := hι.2 τ
    rw [← map_mul, ← map_inv, ← map_mul, mem_Bmap_iff_of_injective hι.1,
      mem_Bmap_iff_of_injective hι.1]
    exact hg (t : MulAut W)
  · intro hg x
    constructor
    · intro hx
      have hxX : x ∈ Xs := hJ hx
      have := (hg (ι ⟨x, hxX⟩)).1 ((mem_Bmap_iff_of_injective hι.1 _).2 hx)
      rw [← map_mul, ← map_inv, ← map_mul, mem_Bmap_iff_of_injective hι.1] at this
      exact this
    · intro hx
      have hxX : x ∈ Xs := by
        have h1 := Xs.mul_mem (Xs.mul_mem (Xs.inv_mem g.2) (hJ hx)) g.2
        simpa [mul_assoc] using h1
      have hgx : (g : MulAut W) * x * (g : MulAut W)⁻¹ ∈ J := hx
      have := (hg (ι ⟨x, hxX⟩)).2 (by
        rw [← map_mul, ← map_inv, ← map_mul, mem_Bmap_iff_of_injective hι.1]
        exact hgx)
      exact (mem_Bmap_iff_of_injective hι.1 _).1 this

end BmapInj

section CtxFacts

open C124 C124.YZ

theorem fin_zero_ne_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) : (0 : Fin n) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem swap_mem_std_five {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k ≤ 5) :
    ∀ x : Fin 5, swap 0 1 x = x ∨ swap 0 1 x = stdInv 5 k x := by
  have hk3 : k ≤ 2 := by omega
  interval_cases k <;> decide

theorem swap_mem_std_seven {k : ℕ} (hk1 : 1 ≤ k) (hk : 2 * k ≤ 7) :
    ∀ x : Fin 7, swap 0 1 x = x ∨ swap 0 1 x = stdInv 7 k x := by
  have hk3 : k ≤ 3 := by omega
  interval_cases k <;> decide

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G} {n k : ℕ} [NeZero n]

omit [Finite G] in
theorem star_le {A : Subgroup G} (hA : A ≤ K ⊔ R) : starOf R K A ≤ starOf R K (K ⊔ R) :=
  autI_mono _ hA

namespace AltCtx

variable (C : AltCtx H R M K n k)
include C

noncomputable abbrev bar (A : Subgroup G) : Subgroup (Perm (Fin n)) := Bmap C.ι (starOf R K A)

theorem starHyp : StarHyp R K (Vc R K) := C.hyp.starHyp

theorem swap_mem_std : swap 0 1 ∈ swapGroupOf (stdInv n k) C.inv_sq := by
  have h1 := C.k_pos
  have h2 := C.k_le
  rcases C.n57 with rfl | rfl
  · exact mem_swapGroupOf.2 (swap_mem_std_five h1 h2)
  · exact mem_swapGroupOf.2 (swap_mem_std_seven h1 h2)

theorem surj : Function.Surjective C.ι := by
  intro σ
  have hJ : swap 0 1 ∈ Bmap C.ι (starOf R K (thompsonJ R)) := by
    rw [C.J_map]
    exact C.swap_mem_std
  obtain ⟨g₀, -, hg₀⟩ := mem_Bmap.1 hJ
  have hne : (0 : Fin n) ≠ 1 := fin_zero_ne_one (by rcases C.n57 with rfl | rfl <;> omega)
  by_cases hsg : σ ∈ alternatingGroup (Fin n)
  · rw [← C.K_map] at hsg
    obtain ⟨g, -, hg⟩ := mem_Bmap.1 hsg
    exact ⟨g, hg⟩
  · have hsgn : σ * swap 0 1 ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup] at hsg ⊢
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · exact absurd h hsg
      · rw [h]
        decide
    rw [← C.K_map] at hsgn
    obtain ⟨g, -, hg⟩ := mem_Bmap.1 hsgn
    refine ⟨g * g₀, ?_⟩
    rw [map_mul, hg, hg₀]
    simp

theorem bij : Function.Bijective C.ι := ⟨C.inj, C.surj⟩

theorem R_pgroup : IsPGroup 2 (C.bar R) :=
  Bmap_isPGroup (le_refl _) (isPGroup_autI _ C.hyp.isPGroup)

theorem J_le_R : swapGroupOf (stdInv n k) C.inv_sq ≤ C.bar R := by
  rw [← C.J_map]
  exact Bmap_mono _ (autI_mono _ (thompsonJ_le R))

theorem R_le_normalizer :
    C.bar R ≤ Subgroup.normalizer (swapGroupOf (stdInv n k) C.inv_sq : Set (Perm (Fin n))) := by
  rw [← C.J_map, ← Bmap_normalizer_of_bijective C.bij (star_le
    ((thompsonJ_le R).trans le_sup_right))]
  refine Bmap_mono _ fun g hg => ?_
  obtain ⟨r, hr, rfl⟩ := (mem_autI _).1 hg
  have hrJ : (r : G) ∈ Subgroup.normalizer (thompsonJ R : Set G) :=
    normalizer_le_normalizer_thompsonJ R (Subgroup.le_normalizer hr)
  rw [Subgroup.mem_normalizer_iff]
  intro φ
  constructor
  · intro hφ
    obtain ⟨j, hj, rfl⟩ := (mem_autI _).1 hφ
    refine (mem_autI _).2 ⟨r * j * r⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.1 hrJ j).1 hj
    simpa using this
  · intro hφ
    obtain ⟨j, hj, hjφ⟩ := (mem_autI _).1 hφ
    refine (mem_autI _).2 ⟨r⁻¹ * j * r, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hrJ) j).1 hj
      simpa using this
    · rw [map_mul, map_mul, map_inv, hjφ]
      group

end AltCtx

end CtxFacts

section SylowMap

variable {A : Type*} [Group A] {B : Type*} [Group B]

theorem isSylowTwoOf_of_le_of_le'' {P Z Y : Subgroup A} (hP : IsSylowTwoOf P Y) (hPZ : P ≤ Z)
    (hZY : Z ≤ Y) : IsSylowTwoOf P Z := by
  refine ⟨hPZ, hP.2.1, fun hdvd => hP.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex P Z Y hPZ hZY
  have h2 : 2 ∣ P.relIndex Y := by rw [← h1]; exact Dvd.dvd.mul_right hdvd _
  exact h2

theorem isSylowTwoOf_map' (φ : A →* B) {S Y : Subgroup A} (h : IsSylowTwoOf S Y) :
    IsSylowTwoOf (S.map φ) (Y.map φ) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map φ, fun hd => h.2.2 ?_⟩
  let ψ : ↥Y →* ↥(Y.map φ) := (φ.comp Y.subtype).codRestrict _ fun y => ⟨y, y.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨_, y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩
  have hmap : (S.subgroupOf Y).map ψ = (S.map φ).subgroupOf (Y.map φ) := by
    ext ⟨x, hx⟩
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨y, hy⟩, hyS, hyx⟩
      have : φ y = x := congrArg Subtype.val hyx
      exact ⟨y, hyS, this⟩
    · rintro ⟨y, hyS, rfl⟩
      exact ⟨⟨y, h.1 hyS⟩, hyS, rfl⟩
  rw [← hmap] at hd
  exact hd.trans (Subgroup.index_map_dvd _ hψ)

theorem map_conjClosure' (φ : A →* B) (Z Y : Subgroup A) :
    (conjClosure Z Y).map φ = conjClosure (Z.map φ) (Y.map φ) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine conjClosure_le fun h hh z hz => ?_
    show φ (h * z * h⁻¹) ∈ conjClosure (Z.map φ) (Y.map φ)
    rw [map_mul, map_mul, map_inv]
    exact mem_conjClosure (Subgroup.mem_map_of_mem φ hh) (Subgroup.mem_map_of_mem φ hz)
  · refine conjClosure_le fun h' hh' z' hz' => ?_
    obtain ⟨h, hh, rfl⟩ := hh'
    obtain ⟨z, hz, rfl⟩ := hz'
    exact ⟨h * z * h⁻¹, mem_conjClosure hh hz, by simp⟩

end SylowMap

section CtxFacts2

open C124 C124.YZ

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G} {n k : ℕ} [NeZero n]

namespace AltCtx

variable (C : AltCtx H R M K n k)
include C

theorem X_le_N : K ⊔ R ≤ Subgroup.normalizer (Vc R K : Set G) := C.hyp.isTwoReducedIn.2.1

omit C in
@[expose] noncomputable def starHom (hX : K ⊔ R ≤ Subgroup.normalizer (Vc R K : Set G)) :
    ↥(K ⊔ R) →* ↥(starOf R K (K ⊔ R)) :=
  ((convI (isElemAbelian_omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))).comp
    (Subgroup.inclusion hX)).codRestrict _ fun x =>
      Subgroup.mem_map_of_mem _ (show Subgroup.inclusion hX x ∈ (K ⊔ R).subgroupOf _ from x.2)

@[expose] noncomputable def φ : ↥(K ⊔ R) →* Perm (Fin n) := C.ι.comp (starHom C.X_le_N)

theorem bar_eq {A : Subgroup G} (hA : A ≤ K ⊔ R) : C.bar A = (A.subgroupOf (K ⊔ R)).map C.φ := by
  ext σ
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨y, hyA, hyg⟩ := (mem_autI _).1 (show (g : MulAut (Wc R K)) ∈ starOf R K A from hg)
    refine ⟨⟨y, hA hyA⟩, hyA, ?_⟩
    show C.ι (starHom C.X_le_N ⟨y, hA hyA⟩) = C.ι g
    congr 1
    apply Subtype.ext
    rw [← hyg]
    rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨starHom C.X_le_N x, ?_, rfl⟩
    exact (mem_autI _).2 ⟨Subgroup.inclusion C.X_le_N x, hx, rfl⟩

end AltCtx

omit [Finite G] [NeZero n] in
theorem isSylowTwoOf_subgroupOf {S Y X : Subgroup G} (h : IsSylowTwoOf S Y) (hYX : Y ≤ X) :
    IsSylowTwoOf (S.subgroupOf X) (Y.subgroupOf X) := by
  refine ⟨fun x hx => h.1 hx, ?_, ?_⟩
  · exact h.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe (h.1.trans hYX)).symm
  · have h1 : ((S.subgroupOf X).subgroupOf (Y.subgroupOf X)).index = (S.subgroupOf Y).index :=
      Subgroup.relIndex_subgroupOf hYX
    rw [h1]
    exact h.2.2

omit [Finite G] [NeZero n] in
theorem conjClosure_subgroupOf {Z Y X : Subgroup G} (hZ : Z ≤ X) (hY : Y ≤ X) :
    (conjClosure Z Y).subgroupOf X = conjClosure (Z.subgroupOf X) (Y.subgroupOf X) := by
  apply Subgroup.map_injective X.subtype_injective
  rw [map_conjClosure', Subgroup.map_subgroupOf_eq_of_le hZ, Subgroup.map_subgroupOf_eq_of_le hY,
    Subgroup.map_subgroupOf_eq_of_le]
  exact conjClosure_le fun h hh z hz => X.mul_mem (X.mul_mem (hY hh) (hZ hz)) (X.inv_mem (hY hh))

namespace AltCtx

variable (C : AltCtx H R M K n k)
include C

omit C [NeZero n] [Finite G] in
theorem MK_le : M ⊓ K ≤ K ⊔ R := inf_le_right.trans le_sup_left

theorem sylow_closure :
    IsSylowTwoOf (C.bar R) (conjClosure (C.bar R) (C.bar (M ⊓ K))) := by
  have hRX : R ≤ K ⊔ R := le_sup_right
  have hCX : conjClosure R (M ⊓ K) ≤ K ⊔ R :=
    conjClosure_le fun h hh z hz => (K ⊔ R).mul_mem ((K ⊔ R).mul_mem (MK_le hh) (hRX hz))
      ((K ⊔ R).inv_mem (MK_le hh))
  have h1 : IsSylowTwoOf R (conjClosure R (M ⊓ K)) :=
    isSylowTwoOf_of_le_of_le'' C.hyp.hyp.sylow (le_conjClosure R _)
      (conjClosure_mono le_rfl inf_le_left)
  have h2 := isSylowTwoOf_map' C.φ (isSylowTwoOf_subgroupOf h1 hCX)
  rw [conjClosure_subgroupOf hRX MK_le, map_conjClosure'] at h2
  rw [C.bar_eq hRX, C.bar_eq MK_le]
  exact h2

end AltCtx

end CtxFacts2

section CtxFacts3

open C124 C124.YZ

variable {G : Type} [Group G] [Finite G] {H R M K : Subgroup G} {n k : ℕ} [NeZero n]

omit [Finite G] [NeZero n] in
theorem eq_of_Bmap_eq {W : Type*} [CommGroup W] {m : ℕ} {Xs : Subgroup (MulAut W)}
    {ι : ↥Xs →* Perm (Fin m)} (hι : Function.Injective ι) {A B : Subgroup (MulAut W)}
    (hA : A ≤ Xs) (hB : B ≤ Xs) (h : Bmap ι A = Bmap ι B) : A = B := by
  have h1 : A.subgroupOf Xs = B.subgroupOf Xs := Subgroup.map_injective hι h
  have h2 := congrArg (Subgroup.map Xs.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hA, Subgroup.map_subgroupOf_eq_of_le hB] at h2

namespace AltCtx

variable (C : AltCtx H R M K n k)
include C

theorem MK_le_alt : C.bar (M ⊓ K) ≤ alternatingGroup (Fin n) := by
  rw [← C.K_map]
  exact Bmap_mono _ (autI_mono _ inf_le_right)

theorem star_alt :
    alternatingGroup (Fin n) ⊓
      Subgroup.normalizer (swapGroupOf (stdInv n k) C.inv_sq : Set (Perm (Fin n))) ≤
      C.bar (M ⊓ K) := by
  have h := normalizer_J_star_le C.hyp C.starHyp
  have hJ : starOf R K (thompsonJ R) ≤ starOf R K (K ⊔ R) :=
    star_le ((thompsonJ_le R).trans le_sup_right)
  have h2 : Bmap C.ι (starOf R K K ⊓
      Subgroup.normalizer (starOf R K (thompsonJ R) : Set (MulAut (Wc R K)))) ≤
      C.bar (M ⊓ K) := Bmap_mono _ h
  rwa [Bmap_inf_of_injective C.inj, C.K_map, Bmap_normalizer_of_bijective C.bij hJ,
    C.J_map] at h2

theorem star_alt_centralizer :
    alternatingGroup (Fin n) ⊓ Subgroup.centralizer {stdInv n k} ≤ C.bar (M ⊓ K) := by
  have h := C.star_alt
  rwa [normalizer_swapGroupOf] at h

theorem MK_ne_alt : C.bar (M ⊓ K) ≠ alternatingGroup (Fin n) := by
  intro h
  apply autOn_MK_ne C.hyp C.starHyp
  rw [← C.K_map] at h
  exact eq_of_Bmap_eq C.inj (star_le MK_le) (star_le le_sup_left) h

theorem le_R_of_normal {P : Subgroup (Perm (Fin n))} (hPM : P ≤ C.bar (M ⊓ K))
    (hMP : C.bar (M ⊓ K) ≤ Subgroup.normalizer (P : Set (Perm (Fin n)))) (hP : IsPGroup 2 P) :
    P ≤ C.bar R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xs := starOf R K (K ⊔ R)
  set P' : Subgroup (MulAut (Wc R K)) := (P.comap C.ι).map Xs.subtype with hP'
  have hmemP' : ∀ g : ↥Xs, (g : MulAut (Wc R K)) ∈ P' ↔ C.ι g ∈ P := by
    intro g
    constructor
    · rintro ⟨g', hg', hgg'⟩
      have : g' = g := Subtype.ext hgg'
      rw [← this]
      exact hg'
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hP'X : P' ≤ Xs := Subgroup.map_subtype_le _
  have hP'M : P' ≤ starOf R K (M ⊓ K) := by
    intro x hx
    have hxX := hP'X hx
    have h1 := (hmemP' ⟨x, hxX⟩).1 hx
    exact (mem_Bmap_iff_of_injective C.inj _).1 (hPM h1)
  have hMN : starOf R K (M ⊓ K) ≤ Subgroup.normalizer (P' : Set (MulAut (Wc R K))) := by
    intro m hm
    have hmX : m ∈ Xs := star_le MK_le hm
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hιm : C.ι ⟨m, hmX⟩ ∈ Subgroup.normalizer (P : Set (Perm (Fin n))) :=
      hMP ((mem_Bmap_iff_of_injective C.inj _).2 hm)
    constructor
    · intro hx
      have hxX := hP'X hx
      have hmx : m * x * m⁻¹ ∈ Xs := Xs.mul_mem (Xs.mul_mem hmX hxX) (Xs.inv_mem hmX)
      have h1 := (hmemP' ⟨x, hxX⟩).1 hx
      refine (hmemP' ⟨_, hmx⟩).2 ?_
      have h2 := (Subgroup.mem_normalizer_iff.1 hιm (C.ι ⟨x, hxX⟩)).1 h1
      rw [← map_inv, ← map_mul, ← map_mul] at h2
      exact h2
    · intro hx
      have hmx := hP'X hx
      have hxX : x ∈ Xs := by
        have := Xs.mul_mem (Xs.mul_mem (Xs.inv_mem hmX) hmx) hmX
        simpa [mul_assoc] using this
      have h1 := (hmemP' ⟨_, hmx⟩).1 hx
      refine (hmemP' ⟨x, hxX⟩).2 ?_
      have h2 : C.ι ⟨m, hmX⟩ * C.ι ⟨x, hxX⟩ * (C.ι ⟨m, hmX⟩)⁻¹ ∈ P := by
        rw [← map_inv, ← map_mul, ← map_mul]
        exact h1
      exact (Subgroup.mem_normalizer_iff.1 hιm _).2 h2
  have hP'2 : IsPGroup 2 P' := by
    have h1 : IsPGroup 2 (P.comap C.ι) := hP.comap_of_injective C.ι C.inj
    exact h1.map _
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hP'M hMN hP'2
  have hR := pCore_MK_star_le_R_star C.hyp C.starHyp
  intro σ hσ
  obtain ⟨g, rfl⟩ := C.surj σ
  have hg : (g : MulAut (Wc R K)) ∈ P' := (hmemP' g).2 hσ
  exact (mem_Bmap_iff_of_injective C.inj _).2 (hR (hle hg))

theorem sylow_iff : IsSylowTwoOf R (K ⊔ R) ↔ IsSylowTwoOf (C.bar R) ⊤ := by
  have hiff : IsSylowTwoOf R (K ⊔ R) ↔
      IsSylowTwoOf (starOf R K R) (starOf R K (K ⊔ R)) := C.starHyp.isSylowTwoOf_iff
  rw [hiff]
  have hRX : starOf R K R ≤ starOf R K (K ⊔ R) := star_le le_sup_right
  have htop : (⊤ : Subgroup ↥(starOf R K (K ⊔ R))).map C.ι = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact C.surj
  constructor
  · intro h
    have h1 := isSylowTwoOf_map' C.ι (isSylowTwoOf_subgroupOf h le_rfl)
    rw [Subgroup.subgroupOf_self, htop] at h1
    exact h1
  · intro h
    let e : ↥(starOf R K (K ⊔ R)) ≃* Perm (Fin n) := MulEquiv.ofBijective C.ι C.bij
    have h1 := isSylowTwoOf_map' e.symm.toMonoidHom h
    have hcomp : e.symm.toMonoidHom.comp C.ι = MonoidHom.id _ :=
      MonoidHom.ext fun g => e.symm_apply_apply g
    have hmap : (C.bar R).map e.symm.toMonoidHom =
        (starOf R K R).subgroupOf (starOf R K (K ⊔ R)) := by
      unfold AltCtx.bar Bmap
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [hmap, Subgroup.map_top_of_surjective _ e.symm.surjective] at h1
    have h2 := isSylowTwoOf_map' (starOf R K (K ⊔ R)).subtype h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hRX, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2

theorem exists_lift {σ : Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    ∃ (y : G) (hy : y ∈ K), C.φ ⟨y, Subgroup.mem_sup_left hy⟩ = σ := by
  have hσ' : σ ∈ C.bar K := by
    show σ ∈ Bmap C.ι (starOf R K K)
    rw [C.K_map]
    exact hσ
  rw [C.bar_eq le_sup_left] at hσ'
  obtain ⟨⟨y, hyX⟩, hyK, rfl⟩ := hσ'
  exact ⟨y, hyK, rfl⟩

theorem φ_mem_bar {A : Subgroup G} (hA : A ≤ K ⊔ R) {y : G} (hy : y ∈ A) :
    C.φ ⟨y, hA hy⟩ ∈ C.bar A := by
  rw [C.bar_eq hA]
  exact ⟨⟨y, hA hy⟩, hy, rfl⟩

end AltCtx

omit [Finite G] [NeZero n] in
theorem isSylowTwoOf_Bmap_iff {W : Type} [CommGroup W] {m : ℕ} {Xs : Subgroup (MulAut W)}
    {ι : ↥Xs →* Perm (Fin m)} (hι : Function.Bijective ι) {S Y : Subgroup (MulAut W)}
    (hSY : S ≤ Y) (hY : Y ≤ Xs) :
    IsSylowTwoOf S Y ↔ IsSylowTwoOf (Bmap ι S) (Bmap ι Y) := by
  constructor
  · intro h
    exact isSylowTwoOf_map' ι (isSylowTwoOf_subgroupOf h hY)
  · intro h
    let e : ↥Xs ≃* Perm (Fin m) := MulEquiv.ofBijective ι hι
    have h1 := isSylowTwoOf_map' e.symm.toMonoidHom h
    have hcomp : e.symm.toMonoidHom.comp ι = MonoidHom.id _ :=
      MonoidHom.ext fun g => e.symm_apply_apply g
    have hmap : ∀ A : Subgroup (MulAut W),
        (Bmap ι A).map e.symm.toMonoidHom = A.subgroupOf Xs := by
      intro A
      unfold Bmap
      rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [hmap, hmap] at h1
    have h2 := isSylowTwoOf_map' Xs.subtype h1
    rwa [Subgroup.map_subgroupOf_eq_of_le (hSY.trans hY),
      Subgroup.map_subgroupOf_eq_of_le hY] at h2

namespace AltCtx

variable (C : AltCtx H R M K n k)
include C

theorem isBorelIn_of_bar {A B : Subgroup G} (hA : A ≤ K ⊔ R) (hB : B ≤ K ⊔ R)
    (h : IsBorelIn (C.bar A) (C.bar B)) : IsBorelIn (starOf R K A) (starOf R K B) := by
  obtain ⟨S, hS, hBS⟩ := h
  set Xs := starOf R K (K ⊔ R)
  set S' : Subgroup (MulAut (Wc R K)) := (S.comap C.ι).map Xs.subtype with hS'
  have hS'X : S' ≤ Xs := Subgroup.map_subtype_le _
  have hbarS : Bmap C.ι S' = S := by
    ext σ
    constructor
    · rintro ⟨g, ⟨g', hg', hgg'⟩, rfl⟩
      have : g' = g := Subtype.ext hgg'
      rw [← this]
      exact hg'
    · intro hσ
      obtain ⟨g, rfl⟩ := C.surj σ
      exact ⟨g, ⟨g, hσ, rfl⟩, rfl⟩
  have hAX : starOf R K A ≤ Xs := star_le hA
  have hS'A : S' ≤ starOf R K A := by
    intro x hx
    have hxX := hS'X hx
    have h1 : C.ι ⟨x, hxX⟩ ∈ S := by
      obtain ⟨g, hg, hgx⟩ := hx
      have : g = ⟨x, hxX⟩ := Subtype.ext hgx
      rw [← this]
      exact hg
    exact (mem_Bmap_iff_of_injective C.inj _).1 (hS.1 h1)
  refine ⟨S', ?_, ?_⟩
  · rw [isSylowTwoOf_Bmap_iff C.bij hS'A hAX, hbarS]
    exact hS
  · refine eq_of_Bmap_eq C.inj (star_le hB) (inf_le_left.trans hAX) ?_
    rw [Bmap_inf_of_injective C.inj, Bmap_normalizer_of_bijective C.bij hS'X, hbarS]
    exact hBS

theorem nonempty_equiv_bar {A : Subgroup G} (hA : A ≤ K ⊔ R) :
    Nonempty (↥(starOf R K A) ≃* ↥(C.bar A)) := by
  have hAX : starOf R K A ≤ starOf R K (K ⊔ R) := star_le hA
  exact ⟨(Subgroup.subgroupOfEquivOfLe hAX).symm.trans
    (Subgroup.equivMapOfInjective _ C.ι C.inj)⟩

end AltCtx

theorem two_pow_dvd_of_isSylowTwoOf {Γ : Type*} [Group Γ] [Finite Γ] {P Y N₀ : Subgroup Γ}
    (hP : IsSylowTwoOf P Y) (hN : N₀ ≤ Y) {a : ℕ} (ha : 2 ^ a ∣ Nat.card N₀) :
    2 ^ a ∣ Nat.card P := by
  have h1 : 2 ^ a ∣ Nat.card Y := ha.trans (Subgroup.card_dvd_of_le hN)
  have h2 : Nat.card Y = Nat.card P * (P.subgroupOf Y).index := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP.1).toEquiv]
    exact (Subgroup.card_mul_index _).symm
  rw [h2] at h1
  have hcop : Nat.Coprime (2 ^ a) (P.subgroupOf Y).index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hP.2.2)
  exact hcop.dvd_of_dvd_mul_right h1

theorem sylow_five_of_eight_dvd {P : Subgroup (Perm (Fin 5))} (hP : IsPGroup 2 P)
    (h8 : 8 ∣ Nat.card P) : IsSylowTwoOf P ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  have hcard : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd : 2 ^ a ∣ 120 := by
    rw [← hcard, ← ha]
    exact Subgroup.card_subgroup_dvd_card P
  have ha3 : a ≤ 3 := by
    by_contra h
    have : 2 ^ 4 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have := this.trans hdvd
    norm_num at this
  have ha3' : 3 ≤ a := by
    by_contra h
    rw [ha] at h8
    have : 8 ∣ 2 ^ 2 := h8.trans (pow_dvd_pow 2 (by omega))
    norm_num at this
  have ha8 : Nat.card P = 8 := by rw [ha, show a = 3 by omega]; norm_num
  refine ⟨le_top, hP, ?_⟩
  have h1 : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right P
  rw [h1]
  have h2 := P.index_mul_card
  rw [hcard, ha8] at h2
  have : P.index = 15 := by omega
  rw [this]
  decide

theorem sylow_seven_of_sixteen_dvd {P : Subgroup (Perm (Fin 7))} (hP : IsPGroup 2 P)
    (h16 : 16 ∣ Nat.card P) : IsSylowTwoOf P ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  have hcard : Nat.card (Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd : 2 ^ a ∣ 5040 := by
    rw [← hcard, ← ha]
    exact Subgroup.card_subgroup_dvd_card P
  have ha4 : a ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 2 ^ a := pow_dvd_pow 2 (by omega)
    have := this.trans hdvd
    norm_num at this
  have ha4' : 4 ≤ a := by
    by_contra h
    rw [ha] at h16
    have : 16 ∣ 2 ^ 3 := h16.trans (pow_dvd_pow 2 (by omega))
    norm_num at this
  have ha16 : Nat.card P = 16 := by rw [ha, show a = 4 by omega]; norm_num
  refine ⟨le_top, hP, ?_⟩
  have h1 : (P.subgroupOf ⊤).index = P.index := Subgroup.relIndex_top_right P
  rw [h1]
  have h2 := P.index_mul_card
  rw [hcard, ha16] at h2
  have : P.index = 315 := by omega
  rw [this]
  decide

end CtxFacts3

end CFSG.Quasithin.SmithC27
