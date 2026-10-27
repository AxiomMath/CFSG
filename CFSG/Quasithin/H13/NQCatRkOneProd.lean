module

public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.GH74.Uniqueness.Bender.Models

public section

namespace CFSG.Quasithin.H13.NQCat.RkOne

open Subgroup CFSG.GH74.Uniqueness.Bender

section Bender

variable {X : Type*} [Group X] [Finite X] {n i e : ℕ}

theorem bender_sylow_eq (h : BenderType X n i e) (P Q : Sylow 2 X)
    {Y : Subgroup X} (hP : (P : Subgroup X) ≤ Y) (hQ : (Q : Subgroup X) ≤ Y) (hY : Y ≠ ⊤) :
    P = Q := by
  obtain ⟨t, ht⟩ := h.exists_benderCore P
  have := h.isSimple
  have hQN : (Q : Subgroup X) ≤ normalizer ((P : Subgroup X) : Set X) :=
    hQ.trans (ht.le_borel_of_le hP hY)
  have hsup : ((Q : Subgroup X) ⊔ P : Subgroup X) = P :=
    P.is_maximal' (Q.isPGroup'.to_sup_of_normal_right' P.isPGroup' hQN) le_sup_right
  have hQP : (Q : Subgroup X) ≤ P := hsup ▸ le_sup_left
  exact Sylow.ext (Q.is_maximal' P.isPGroup' hQP)

theorem bender_isSolvable_normalizer (h : BenderType X n i e)
    (P : Sylow 2 X) : Group.IsSolvable (normalizer ((P : Subgroup X) : Set X)) := by
  obtain ⟨t, ht⟩ := h.exists_benderCore P
  exact ht.isSolvable_borel

end Bender

section Proj

variable {A : Type*} [Group A] {ι : Type*}

theorem iSupIndep_of_commute (X : ι → Subgroup A)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ X i → y ∈ X j → Commute x y)
    (hZ : ∀ j, ∀ x ∈ X j, (∀ y ∈ X j, Commute x y) → x = 1) : iSupIndep X := by
  intro j
  rw [disjoint_iff, eq_bot_iff]
  intro x hx
  rw [mem_inf] at hx
  have hC : (⨆ (i) (_ : i ≠ j), X i) ≤ centralizer (X j : Set A) := by
    refine iSup₂_le fun i hij y hy => ?_
    rw [mem_centralizer_iff]
    intro z hz
    exact (hcomm hij y z hy hz).eq.symm
  rw [mem_bot]
  exact hZ j x hx.1 fun y hy => (mem_centralizer_iff.1 (hC hx.2) y hy).symm

theorem exists_proj [Finite ι] (X : ι → Subgroup A)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ X i → y ∈ X j → Commute x y)
    (hind : iSupIndep X) (htop : ⨆ j, X j = ⊤) :
    ∃ π : ∀ j, A →* X j, (∀ j (k : X j), π j k = k) ∧
      (∀ i j (k : X j), i ≠ j → π i k = 1) ∧ (∀ a : A, (∀ j, π j a = 1) → a = 1) ∧
      ∀ (Y : ∀ j, Subgroup (X j)) (a : A), (∀ j, π j a ∈ Y j) →
        a ∈ ⨆ j, (Y j).map (X j).subtype := by
  classical
  obtain ⟨e, he⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup X hcomm hind
  let e' : (∀ j, X j) ≃* A := (e.trans (MulEquiv.subgroupCongr htop)).trans Subgroup.topEquiv
  have he' : ∀ j (k : X j), e' (Pi.mulSingle j k) = k := fun j k => by
    have h := he j (Pi.mulSingle j k) fun i hi => Pi.mulSingle_eq_of_ne (M := fun j => ↥(X j)) hi k
    rw [Pi.mulSingle_eq_same] at h
    exact h
  have hsymm : ∀ j (k : X j), e'.symm k = Pi.mulSingle j k := fun j k => by
    rw [MulEquiv.symm_apply_eq, he']
  refine ⟨fun j => (Pi.evalMonoidHom (fun j => ↥(X j)) j).comp e'.symm.toMonoidHom, ?_, ?_, ?_,
    ?_⟩
  · intro j k
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Pi.evalMonoidHom_apply, hsymm, Pi.mulSingle_eq_same]
  · intro i j k hij
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Pi.evalMonoidHom_apply, hsymm, Pi.mulSingle_eq_of_ne hij]
  · intro a ha
    have h1 : e'.symm a = 1 := funext fun j => ha j
    simpa using congrArg e' h1
  · intro Y a ha
    have hx : e'.symm a ∈ (⨆ j, (Y j).map (X j).subtype).comap e'.toMonoidHom := by
      refine Subgroup.pi_mem_of_mulSingle_mem _ fun j => ?_
      rw [mem_comap, MulEquiv.coe_toMonoidHom, he']
      exact mem_iSup_of_mem j ⟨_, ha j, rfl⟩
    simpa using hx

end Proj

section Product

variable {A : Type*} [Group A] {ι : Type*} [Finite ι]

theorem product_sylow (X : ι → Subgroup A)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ X i → y ∈ X j → Commute x y)
    (hind : iSupIndep X) (htop : ⨆ j, X j = ⊤)
    (hB : ∀ j (P Q : Sylow 2 (X j)) (Y : Subgroup (X j)), (P : Subgroup (X j)) ≤ Y →
      (Q : Subgroup (X j)) ≤ Y → Y ≠ ⊤ → P = Q)
    (hBs : ∀ j (P : Sylow 2 (X j)),
      Group.IsSolvable (normalizer ((P : Subgroup (X j)) : Set (X j))))
    (P : Sylow 2 A) :
    Group.IsSolvable (normalizer ((P : Subgroup A) : Set A)) ∧
      ∀ Z : Subgroup A, (P : Subgroup A) ≤ Z → ¬ Z ≤ normalizer ((P : Subgroup A) : Set A) →
        ∃ j, X j ≤ Z := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨π, hπX, hπne, hπinj, hπsup⟩ := exists_proj X hcomm hind htop
  have hconj : ∀ (a : A) j (k : X j),
      a * (k : A) * a⁻¹ = (π j a : A) * k * (π j a : A)⁻¹ := by
    intro a j k
    set c := a * (π j a : A)⁻¹ with hc
    set W : ∀ i, Subgroup (X i) := Function.update (fun _ => ⊤) j ⊥ with hW
    have hcmem : c ∈ ⨆ i, (W i).map (X i).subtype := by
      refine hπsup W c fun i => ?_
      by_cases hij : i = j
      · subst hij
        rw [hW, Function.update_self, mem_bot, hc, map_mul, map_inv, hπX, mul_inv_cancel]
      · rw [hW, Function.update_of_ne hij]
        exact mem_top _
    have hle : (⨆ i, (W i).map (X i).subtype) ≤ centralizer (X j : Set A) := by
      refine iSup_le fun i => ?_
      by_cases hij : i = j
      · subst hij
        rw [hW, Function.update_self, Subgroup.map_bot]
        exact bot_le
      · rw [hW, Function.update_of_ne hij, ← MonoidHom.range_eq_map, range_subtype]
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact (hcomm hij x y hx hy).eq.symm
    have hcC : c ∈ centralizer (X j : Set A) := hle hcmem
    have hk : (π j a : A) * k * (π j a : A)⁻¹ ∈ X j :=
      (X j).mul_mem ((X j).mul_mem (π j a).2 k.2) ((X j).inv_mem (π j a).2)
    have h1 := mem_centralizer_iff.1 hcC _ hk
    calc a * (k : A) * a⁻¹ = c * ((π j a : A) * k * (π j a : A)⁻¹) * c⁻¹ := by
          rw [hc]
          group
      _ = _ := by
          rw [← h1]
          group
  set Q : ∀ j, Subgroup (X j) := fun j => (P : Subgroup A).map (π j) with hQdef
  have hQp : ∀ j, IsPGroup 2 (Q j) := fun j => P.isPGroup'.map (π j)
  have hmax : ∀ Y : ∀ j, Subgroup (X j), (∀ j, IsPGroup 2 (Y j)) → (∀ j, Q j ≤ Y j) →
      ∀ j (k : X j), k ∈ Y j → (k : A) ∈ P := by
    intro Y hY hQY j k hk
    let R : Subgroup A := ⨅ i, (Y i).comap (π i)
    have hPR : (P : Subgroup A) ≤ R := fun p hp => mem_iInf.2 fun i => hQY i ⟨p, hp, rfl⟩
    have hR : IsPGroup 2 R := by
      intro r
      have hr : ∀ i, π i r ∈ Y i := fun i => mem_iInf.1 r.2 i
      choose m hm using fun i => hY i ⟨π i r, hr i⟩
      refine ⟨Finset.univ.sup m, Subtype.ext (hπinj _ fun i => ?_)⟩
      have h1 : π i r ^ 2 ^ m i = 1 := by
        have := congrArg Subtype.val (hm i)
        simpa using this
      obtain ⟨c, hc⟩ : 2 ^ m i ∣ 2 ^ Finset.univ.sup m :=
        pow_dvd_pow 2 (Finset.le_sup (Finset.mem_univ i))
      rw [SubgroupClass.coe_pow, map_pow, hc, pow_mul, h1, one_pow]
    have hRP : R = P := P.is_maximal' hR hPR
    have hkR : (k : A) ∈ R := mem_iInf.2 fun i => by
      by_cases hij : i = j
      · subst hij
        rw [mem_comap, hπX]
        exact hk
      · rw [mem_comap, hπne i j k hij]
        exact (Y i).one_mem
    rw [hRP] at hkR
    exact hkR
  have hQP : ∀ j (k : X j), k ∈ Q j → (k : A) ∈ P := hmax Q hQp fun j => le_rfl
  have hPQ : ∀ j (k : X j), (k : A) ∈ P → k ∈ Q j := fun j k hk => ⟨k, hk, hπX j k⟩
  let QS : ∀ j, Sylow 2 (X j) := fun j =>
    { toSubgroup := Q j
      isPGroup' := hQp j
      is_maximal' := fun {Q'} hQ' hle => by
        refine le_antisymm (fun k hk => hPQ j k ?_) hle
        refine hmax (Function.update Q j Q') (fun i => ?_) (fun i => ?_) j k ?_
        · by_cases hij : i = j
          · subst hij
            rw [Function.update_self]
            exact hQ'
          · rw [Function.update_of_ne hij]
            exact hQp i
        · by_cases hij : i = j
          · subst hij
            rw [Function.update_self]
            exact hle
          · rw [Function.update_of_ne hij]
        · rw [Function.update_self]
          exact hk }
  have hPeq : (P : Subgroup A) = ⨆ j, (Q j).map (X j).subtype := by
    refine le_antisymm (fun p hp => hπsup Q p fun j => ⟨p, hp, rfl⟩) (iSup_le fun j => ?_)
    rintro _ ⟨k, hk, rfl⟩
    exact hQP j k hk
  have hstep : ∀ (b : A) j, π j b ∈ normalizer (Q j : Set (X j)) →
      ∀ h ∈ (Q j).map (X j).subtype, b * h * b⁻¹ ∈ (Q j).map (X j).subtype := by
    rintro b j hb _ ⟨k, hk, rfl⟩
    refine ⟨π j b * k * (π j b)⁻¹, (mem_normalizer_iff.1 hb k).1 hk, ?_⟩
    rw [Subgroup.coe_subtype, hconj b j k]
    simp
  have hnormP : ∀ a : A,
      a ∈ normalizer ((P : Subgroup A) : Set A) ↔ ∀ j, π j a ∈ normalizer (Q j : Set (X j)) := by
    intro a
    constructor
    · intro ha j
      rw [mem_normalizer_iff]
      intro k
      have e1 : ((π j a * k * (π j a)⁻¹ : X j) : A) = a * k * a⁻¹ := by
        rw [hconj a j k]
        simp
      constructor
      · intro hk
        apply hPQ
        rw [e1]
        exact (mem_normalizer_iff.1 ha _).1 (hQP j k hk)
      · intro hk
        apply hPQ
        have := hQP j _ hk
        rw [e1] at this
        exact (mem_normalizer_iff.1 ha _).2 this
    · intro ha
      rw [hPeq, mem_normalizer_iff_map_conj_eq, Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      rw [← mem_normalizer_iff_map_conj_eq, mem_normalizer_iff]
      intro h
      refine ⟨hstep a j (ha j) h, fun hh => ?_⟩
      have := hstep a⁻¹ j (by rw [map_inv]; exact inv_mem (ha j)) _ hh
      simpa [mul_assoc] using this
  have hsol : Group.IsSolvable (normalizer ((P : Subgroup A) : Set A)) := by
    have : ∀ j, Group.IsSolvable (normalizer (Q j : Set (X j))) := fun j => hBs j (QS j)
    let ψ : normalizer ((P : Subgroup A) : Set A) →* ∀ j, normalizer (Q j : Set (X j)) :=
      { toFun := fun x j => ⟨π j x, (hnormP x).1 x.2 j⟩
        map_one' := by
          funext j
          ext
          simp
        map_mul' := fun x y => by
          funext j
          ext
          simp }
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro x hx
      apply Subtype.ext
      apply hπinj
      intro j
      have := congrArg (fun f => ((f j : normalizer (Q j : Set (X j))) : X j)) hx
      simpa [ψ] using this
    have hpi : Group.IsSolvable (∀ j, normalizer (Q j : Set (X j))) := by
      choose m hm using fun j => (inferInstance :
        Group.IsSolvable (normalizer (Q j : Set (X j)))).solvable
      refine ⟨⟨Finset.univ.sup m, ?_⟩⟩
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      funext j
      have h1 : x j ∈ derivedSeries _ (Finset.univ.sup m) :=
        map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom _ j) _ ⟨x, hx, rfl⟩
      have h2 := derivedSeries_antitone _ (Finset.le_sup (f := m) (Finset.mem_univ j)) h1
      rw [hm j] at h2
      exact Subgroup.mem_bot.1 h2
    exact Group.isSolvable_of_isSolvable_injective hψ
  refine ⟨hsol, fun Z hPZ hZ => ?_⟩
  obtain ⟨z, hzZ, hzN⟩ := Set.not_subset.1 hZ
  obtain ⟨j, hj⟩ : ∃ j, π j z ∉ normalizer (Q j : Set (X j)) := by
    by_contra h
    push Not at h
    exact hzN ((hnormP z).2 h)
  refine ⟨j, fun x hx => ?_⟩
  set Y : Subgroup (X j) := Z.comap (X j).subtype with hYdef
  have hQY : (QS j : Subgroup (X j)) ≤ Y := fun k hk => hPZ (hQP j k hk)
  have hgY : ((π j z • QS j : Sylow 2 (X j)) : Subgroup (X j)) ≤ Y := by
    intro k hk
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    show (((MulAut.conj (π j z)) • k' : X j) : A) ∈ Z
    rw [MulAut.smul_def, MulAut.conj_apply]
    have e1 : ((π j z * k' * (π j z)⁻¹ : X j) : A) = z * k' * z⁻¹ := by
      rw [hconj z j k']
      simp
    rw [e1]
    exact Z.mul_mem (Z.mul_mem hzZ (hPZ (hQP j k' hk'))) (Z.inv_mem hzZ)
  by_cases hYtop : Y = ⊤
  · have : (⟨x, hx⟩ : X j) ∈ Y := hYtop ▸ mem_top _
    exact this
  · exfalso
    have h1 := hB j (QS j) (π j z • QS j) Y hQY hgY hYtop
    exact hj (Sylow.smul_eq_iff_mem_normalizer.1 h1.symm)

end Product

end CFSG.Quasithin.H13.NQCat.RkOne
