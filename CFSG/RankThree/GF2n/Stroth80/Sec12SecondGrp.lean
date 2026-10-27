module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ComponentClassification.OuterAutomorphisms (Outer perfect_action_inner)
open CFSG.ComponentClassification.SolvableKernelContainment (hom_eq_one)

variable {H : Type*} [Group H]

@[expose] def conjAut (K A : Subgroup H) (h : ∀ k ∈ K, ∀ x ∈ A, k * x * k⁻¹ ∈ A) :
    K →* MulAut A where
  toFun k :=
    { toFun := fun x => ⟨k * x * k⁻¹, h k k.2 x x.2⟩
      invFun := fun x => ⟨k⁻¹ * x * k, by
        simpa using h k⁻¹ (K.inv_mem k.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' := fun k l => MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem conjAut_apply (K A : Subgroup H) (h : ∀ k ∈ K, ∀ x ∈ A, k * x * k⁻¹ ∈ A) (k : K)
    (x : A) : ((conjAut K A h k x : A) : H) = k * x * k⁻¹ := rfl


section Perm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] noncomputable def famIdx (A : ι → Subgroup H)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (h : H) (i : ι) : ι :=
  Classical.choose (hstab h i)

theorem famIdx_spec (A : ι → Subgroup H)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (h : H) (i : ι) : A (famIdx A hstab h i) = Subgroup.map (MulAut.conj h).toMonoidHom (A i) :=
  (Classical.choose_spec (hstab h i)).symm

theorem famIdx_injective (A : ι → Subgroup H) (hinj : Function.Injective A)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (h : H) : Function.Injective (famIdx A hstab h) := by
  intro i i' hii
  have e1 := famIdx_spec A hstab h i
  have e2 := famIdx_spec A hstab h i'
  have : Subgroup.map (MulAut.conj h).toMonoidHom (A i) =
      Subgroup.map (MulAut.conj h).toMonoidHom (A i') := by
    rw [← e1, ← e2, hii]
  exact hinj (Subgroup.map_injective (MulAut.conj h).injective this)

theorem famIdx_one (A : ι → Subgroup H) (hinj : Function.Injective A)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (i : ι) : famIdx A hstab 1 i = i := by
  refine hinj ?_
  rw [famIdx_spec A hstab 1 i]
  ext x
  simp

theorem famIdx_mul (A : ι → Subgroup H) (hinj : Function.Injective A)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (h k : H) (i : ι) :
    famIdx A hstab (h * k) i = famIdx A hstab h (famIdx A hstab k i) := by
  refine hinj ?_
  rw [famIdx_spec A hstab (h * k) i, famIdx_spec A hstab h (famIdx A hstab k i),
    famIdx_spec A hstab k i]
  ext x
  simp [Subgroup.mem_map]

@[expose] noncomputable def famPerm (A : ι → Subgroup H) (hinj : Function.Injective A)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j) :
    H →* Equiv.Perm ι where
  toFun h := Equiv.ofBijective (famIdx A hstab h)
    ⟨famIdx_injective A hinj hstab h, Finite.injective_iff_surjective.mp
      (famIdx_injective A hinj hstab h)⟩
  map_one' := Equiv.ext fun i => famIdx_one A hinj hstab i
  map_mul' := fun h k => Equiv.ext fun i => famIdx_mul A hinj hstab h k i

theorem famPerm_apply (A : ι → Subgroup H) (hinj : Function.Injective A)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (h : H) (i : ι) : famPerm A hinj hstab h i = famIdx A hstab h i := rfl

end Perm


section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem perfect_le_iSup_of_factors [Finite H] (A : ι → Subgroup H) (hinj : Function.Injective A)
    (hstab : ∀ (h : H) (i : ι), ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, x * y = y * x)
    (hout : ∀ i, Group.IsSolvable (Outer ↥(A i)))
    (hperm : Group.IsSolvable (Equiv.Perm ι))
    (hC : Group.IsSolvable ↥(Subgroup.centralizer ((⨆ i, A i : Subgroup H) : Set H)))
    (hSn : (⨆ i, A i : Subgroup H).Normal)
    {P : Subgroup H} (hP : ⁅P, P⁆ = P) : P ≤ ⨆ i, A i := by
  classical
  haveI : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hP
  set S : Subgroup H := ⨆ i, A i with hS
  have hPstab : ∀ p ∈ P, ∀ i, ∀ x ∈ A i, p * x * p⁻¹ ∈ A i := by
    have h1 : (famPerm A hinj hstab).comp P.subtype = 1 := hom_eq_one _
    intro p hp i x hx
    have h2 : famPerm A hinj hstab p = 1 := by
      have := congrArg (fun f => f ⟨p, hp⟩) h1
      simpa using this
    have h3 : famIdx A hstab p i = i := by
      have := congrArg (fun σ => σ i) h2
      simpa [famPerm_apply] using this
    have h4 := famIdx_spec A hstab p i
    rw [h3] at h4
    have : p * x * p⁻¹ ∈ Subgroup.map (MulAut.conj p).toMonoidHom (A i) :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rw [← h4] at this
    exact this
  have hinner : ∀ p ∈ P, ∀ i, ∃ a ∈ A i, ∀ x ∈ A i, p * x * p⁻¹ = a * x * a⁻¹ := by
    intro p hp i
    haveI := hout i
    obtain ⟨a, ha⟩ := perfect_action_inner
      (conjAut P (A i) (fun k hk x hx => hPstab k hk i x hx)) ⟨p, hp⟩
    refine ⟨a, a.2, fun x hx => ?_⟩
    have := congrArg (fun φ : MulAut (A i) => ((φ ⟨x, hx⟩ : A i) : H)) ha
    simpa [conjAut_apply, MulAut.conj_apply] using this
  have hglobal : ∀ p ∈ P, ∃ s ∈ S, ∀ i, ∀ x ∈ A i, p * x * p⁻¹ = s * x * s⁻¹ := by
    intro p hp
    choose a haA hax using hinner p hp
    have key : ∀ F : Finset ι, ∃ s ∈ ⨆ i ∈ F, A i,
        ∀ i ∈ F, ∀ x ∈ A i, p * x * p⁻¹ = s * x * s⁻¹ := by
      intro F
      induction F using Finset.induction_on with
      | empty => exact ⟨1, by simp, by simp⟩
      | insert j F hj ih =>
        obtain ⟨s, hsF, hs⟩ := ih
        have hsj : ∀ y ∈ A j, y * s = s * y := by
          have : (⨆ i ∈ F, A i) ≤ Subgroup.centralizer (A j : Set H) :=
            iSup₂_le fun i hi x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
              hcomm j i (fun h => hj (h ▸ hi)) y hy x hx
          intro y hy
          exact Subgroup.mem_centralizer_iff.mp (this hsF) y hy
        have hle1 : (⨆ i ∈ F, A i) ≤ ⨆ i ∈ insert j F, A i :=
          iSup₂_le fun i hi => le_iSup₂_of_le i (Finset.mem_insert_of_mem hi) le_rfl
        have hle2 : A j ≤ ⨆ i ∈ insert j F, A i :=
          le_iSup₂_of_le j (Finset.mem_insert_self j F) le_rfl
        refine ⟨s * a j, Subgroup.mul_mem _ (hle1 hsF) (hle2 (haA j)), ?_⟩
        intro i hi x hx
        rcases Finset.mem_insert.mp hi with rfl | hiF
        · have hmem : a i * x * (a i)⁻¹ ∈ A i :=
            A i |>.mul_mem (A i |>.mul_mem (haA i) hx) ((A i).inv_mem (haA i))
          have h1 := hsj _ hmem
          calc p * x * p⁻¹ = a i * x * (a i)⁻¹ := hax i x hx
            _ = s * (a i * x * (a i)⁻¹) * s⁻¹ := by rw [← h1]; group
            _ = s * a i * x * (s * a i)⁻¹ := by group
        · have hne : i ≠ j := fun h => hj (h ▸ hiF)
          have h1 := hcomm j i hne.symm (a j) (haA j) x hx
          calc p * x * p⁻¹ = s * x * s⁻¹ := hs i hiF x hx
            _ = s * (a j * x * (a j)⁻¹) * s⁻¹ := by rw [h1]; group
            _ = s * a j * x * (s * a j)⁻¹ := by group
    obtain ⟨s, hsF, hs⟩ := key Finset.univ
    refine ⟨s, ?_, fun i x hx => hs i (Finset.mem_univ i) x hx⟩
    have : (⨆ i ∈ (Finset.univ : Finset ι), A i) ≤ S :=
      iSup₂_le fun i _ => le_iSup A i
    exact this hsF
  have hPC : ∀ p ∈ P, ∃ s ∈ S, s⁻¹ * p ∈ Subgroup.centralizer (S : Set H) := by
    intro p hp
    obtain ⟨s, hsS, hs⟩ := hglobal p hp
    refine ⟨s, hsS, ?_⟩
    have hA : ∀ i, A i ≤ Subgroup.centralizer ({s⁻¹ * p} : Set H) := by
      intro i x hx
      refine Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
      rw [Set.mem_singleton_iff] at hc
      subst hc
      have h1 := hs i x hx
      have h2 : s⁻¹ * p * x = x * (s⁻¹ * p) := by
        calc s⁻¹ * p * x = s⁻¹ * (p * x * p⁻¹) * p := by group
          _ = s⁻¹ * (s * x * s⁻¹) * p := by rw [h1]
          _ = x * (s⁻¹ * p) := by group
      exact h2
    have hSle : S ≤ Subgroup.centralizer ({s⁻¹ * p} : Set H) := iSup_le hA
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have := Subgroup.mem_centralizer_iff.mp (hSle hy) (s⁻¹ * p) (Set.mem_singleton _)
    exact this.symm
  let φ : H →* H ⧸ S := QuotientGroup.mk' S
  haveI : Group.IsSolvable ↥((Subgroup.centralizer (S : Set H)).map φ) :=
    Group.isSolvable_of_surjective (f := φ.subgroupMap (Subgroup.centralizer (S : Set H)))
      (φ.subgroupMap_surjective _)
  let ψ : ↥P →* ↥((Subgroup.centralizer (S : Set H)).map φ) :=
    (φ.comp P.subtype).codRestrict _ (fun p => by
      obtain ⟨s, hsS, hc⟩ := hPC p p.2
      refine ⟨s⁻¹ * p, hc, ?_⟩
      show φ (s⁻¹ * p) = φ p
      have hs1 : φ s⁻¹ = 1 := (QuotientGroup.eq_one_iff (N := S) s⁻¹).mpr (S.inv_mem hsS)
      rw [map_mul, hs1, one_mul])
  have hψ : ψ = 1 := hom_eq_one ψ
  intro p hp
  have h1 : φ p = 1 := by
    have := congrArg (fun f => ((f ⟨p, hp⟩ : ↥((Subgroup.centralizer (S : Set H)).map φ)) :
      H ⧸ S)) hψ
    simpa [ψ] using this
  exact (QuotientGroup.eq_one_iff p).mp h1


theorem iSup_le_normalizer_factor [Finite H] (A : ι → Subgroup H)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, x * y = y * x) (i : ι) :
    (⨆ j, A j : Subgroup H) ≤ Subgroup.normalizer (A i : Set H) := by
  refine iSup_le fun j x hx => ?_
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  by_cases hji : j = i
  · subst hji
    exact (A j).mul_mem ((A j).mul_mem hx hy) ((A j).inv_mem hx)
  · have := hcomm j i hji x hx y hy
    rw [this, mul_inv_cancel_right]
    exact hy

theorem exists_eq_of_conj_factor [Finite H] (A : ι → Subgroup H)
    (hsimple : ∀ i, IsSimpleGroup ↥(A i))
    (hnonab : ∀ i, ∃ x y : ↥(A i), x * y ≠ y * x)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, x * y = y * x)
    (hSn : ∀ h : H, ∀ s ∈ (⨆ i, A i : Subgroup H), h * s * h⁻¹ ∈ (⨆ i, A i : Subgroup H))
    (h : H) (i : ι) :
    ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom (A i) = A j := by
  classical
  set S : Subgroup H := ⨆ i, A i with hS
  set K : Subgroup H := Subgroup.map (MulAut.conj h).toMonoidHom (A i) with hK
  have hKmem : ∀ k, k ∈ K ↔ h⁻¹ * k * h ∈ A i := by
    intro k
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hx
    · intro hk
      exact ⟨h⁻¹ * k * h, hk, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hKS : K ≤ S := by
    rintro k hk
    have hx : h⁻¹ * k * h ∈ A i := (hKmem k).mp hk
    have h1 := hSn h _ (le_iSup A i hx)
    simpa [mul_assoc] using h1
  have hAS : ∀ j, A j ≤ S := fun j => le_iSup A j
  have hKn : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
    intro s hs k hk
    rw [hKmem] at hk ⊢
    have hs' : h⁻¹ * s * h ∈ S := by simpa using hSn h⁻¹ s hs
    have hnorm := iSup_le_normalizer_factor A hcomm i hs'
    have h1 := (Subgroup.mem_normalizer_iff.mp hnorm (h⁻¹ * k * h)).mp hk
    simpa [mul_assoc] using h1
  have hAn : ∀ j, ∀ s ∈ S, ∀ y ∈ A j, s * y * s⁻¹ ∈ A j := by
    intro j s hs y hy
    exact (Subgroup.mem_normalizer_iff.mp (iSup_le_normalizer_factor A hcomm j hs) y).mp hy
  let e : ↥(A i) ≃* ↥K := (A i).equivMapOfInjective (MulAut.conj h).toMonoidHom
    (MulAut.conj h).injective
  haveI : IsSimpleGroup ↥K := by
    haveI := hsimple i
    exact e.symm.isSimpleGroup
  by_contra hne
  push Not at hne
  have hdisj : ∀ j, K ⊓ A j = ⊥ := by
    intro j
    by_contra hnb
    haveI := hsimple j
    have hn1 : ((K ⊓ A j).subgroupOf (A j)).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : H) ∈ K ⊓ A j := hx
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · exact hKn _ (hAS j g.2) _ hx'.1
      · exact (A j).mul_mem ((A j).mul_mem g.2 hx'.2) ((A j).inv_mem g.2)
    have hn2 : ((K ⊓ A j).subgroupOf K).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : H) ∈ K ⊓ A j := hx
      refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
      · exact K.mul_mem (K.mul_mem g.2 hx'.1) (K.inv_mem g.2)
      · exact hAn j _ (hKS g.2) _ hx'.2
    obtain ⟨x, hxmem, hx1⟩ : ∃ x ∈ K ⊓ A j, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact hnb (le_bot_iff.mp fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
    have hAK : A j ≤ K := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ A j).subgroupOf (A j)) with hb | ht
      · exfalso
        have : (⟨x, hxmem.2⟩ : ↥(A j)) ∈ (K ⊓ A j).subgroupOf (A j) :=
          Subgroup.mem_subgroupOf.mpr hxmem
        rw [hb, Subgroup.mem_bot] at this
        exact hx1 (congrArg Subtype.val this)
      · intro y hy
        have : (⟨y, hy⟩ : ↥(A j)) ∈ (K ⊓ A j).subgroupOf (A j) := by
          rw [ht]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).1
    have hKA : K ≤ A j := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ A j).subgroupOf K) with hb | ht
      · exfalso
        have : (⟨x, hxmem.1⟩ : ↥K) ∈ (K ⊓ A j).subgroupOf K := Subgroup.mem_subgroupOf.mpr hxmem
        rw [hb, Subgroup.mem_bot] at this
        exact hx1 (congrArg Subtype.val this)
      · intro y hy
        have : (⟨y, hy⟩ : ↥K) ∈ (K ⊓ A j).subgroupOf K := by
          rw [ht]
          exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.mp this).2
    exact hne j (le_antisymm hKA hAK)
  have hcommK : ∀ k ∈ K, ∀ j, ∀ y ∈ A j, k * y = y * k := by
    intro k hk j y hy
    have h1 : k * y * k⁻¹ * y⁻¹ ∈ K ⊓ A j := by
      refine ⟨?_, ?_⟩
      · have := hKn y (hAS j hy) k⁻¹ (K.inv_mem hk)
        have h2 := K.mul_mem hk this
        simpa [mul_assoc] using h2
      · have := hAn j k (hKS hk) y hy
        exact (A j).mul_mem this ((A j).inv_mem hy)
    rw [hdisj j, Subgroup.mem_bot] at h1
    calc k * y = (k * y * k⁻¹ * y⁻¹) * (y * k) := by group
      _ = y * k := by rw [h1, one_mul]
  have hcommS : ∀ k ∈ K, ∀ s ∈ S, k * s = s * k := by
    intro k hk s hs
    have hle : S ≤ Subgroup.centralizer ({k} : Set H) := by
      refine iSup_le fun j y hy => Subgroup.mem_centralizer_iff.mpr fun c hc => ?_
      rw [Set.mem_singleton_iff] at hc
      subst hc
      exact hcommK c hk j y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hs) k (Set.mem_singleton _)
  obtain ⟨x, y, hxy⟩ := hnonab i
  apply hxy
  apply e.injective
  apply Subtype.ext
  show h * ((x : H) * y) * h⁻¹ = h * ((y : H) * x) * h⁻¹
  have h1 : (h * (x : H) * h⁻¹) * (h * (y : H) * h⁻¹) = (h * (y : H) * h⁻¹) * (h * (x : H) * h⁻¹) :=
    hcommS _ ⟨x, x.2, rfl⟩ _ (hKS ⟨y, y.2, rfl⟩)
  calc h * ((x : H) * y) * h⁻¹ = (h * (x : H) * h⁻¹) * (h * (y : H) * h⁻¹) := by group
    _ = (h * (y : H) * h⁻¹) * (h * (x : H) * h⁻¹) := h1
    _ = h * ((y : H) * x) * h⁻¹ := by group

end Main


section Binary

variable [Finite H]

@[expose] def facFst (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    A →* H :=
  S.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A B))

@[expose] def facSnd (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    B →* H :=
  S.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr A B))

theorem facFst_injective (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    Function.Injective (facFst S e) := by
  intro a a' h
  have h1 : e.symm (a, 1) = e.symm (a', 1) := Subtype.ext h
  have := e.symm.injective h1
  exact (Prod.mk.inj this).1

theorem facSnd_injective (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    Function.Injective (facSnd S e) := by
  intro b b' h
  have h1 : e.symm (1, b) = e.symm (1, b') := Subtype.ext h
  have := e.symm.injective h1
  exact (Prod.mk.inj this).2

theorem facFst_comm (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B)
    (a : A) (b : B) : facFst S e a * facSnd S e b = facSnd S e b * facFst S e a := by
  have : e.symm (a, 1) * e.symm (1, b) = e.symm (1, b) * e.symm (a, 1) := by
    rw [← map_mul, ← map_mul]
    simp
  exact congrArg Subtype.val this

theorem facFst_le (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    (facFst S e).range ≤ S := by
  rintro _ ⟨a, rfl⟩
  exact (e.symm (a, 1)).2

theorem facSnd_le (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    (facSnd S e).range ≤ S := by
  rintro _ ⟨b, rfl⟩
  exact (e.symm (1, b)).2

theorem facs_sup (S : Subgroup H) {A B : Type*} [Group A] [Group B] (e : ↥S ≃* A × B) :
    (facFst S e).range ⊔ (facSnd S e).range = S := by
  refine le_antisymm (sup_le (facFst_le S e) (facSnd_le S e)) fun x hx => ?_
  have h1 : e ⟨x, hx⟩ = ((e ⟨x, hx⟩).1, 1) * (1, (e ⟨x, hx⟩).2) := by simp
  have h2 : (⟨x, hx⟩ : S) =
      e.symm ((e ⟨x, hx⟩).1, 1) * e.symm (1, (e ⟨x, hx⟩).2) := by
    rw [← map_mul, ← h1, e.symm_apply_apply]
  have h3 : x = facFst S e (e ⟨x, hx⟩).1 * facSnd S e (e ⟨x, hx⟩).2 := congrArg Subtype.val h2
  rw [h3]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)


theorem perfect_le_of_prod (S R : Subgroup H) [S.Normal]
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (S : Set H)))
    {A B : Type} [Group A] [Group B] [IsSimpleGroup A] [IsSimpleGroup B]
    (hAn : ∃ x y : A, x * y ≠ y * x) (hBn : ∃ x y : B, x * y ≠ y * x)
    (hAo : Group.IsSolvable (Outer A)) (hBo : Group.IsSolvable (Outer B))
    (e : ↥S ≃* A × B) (hR : ⁅R, R⁆ = R) : R ≤ S := by
  classical
  let F : Bool → Subgroup H := fun b => bif b then (facFst S e).range else (facSnd S e).range
  have hFsup : (⨆ i, F i) = S := by
    rw [iSup_bool_eq]
    exact facs_sup S e
  let eA : A ≃* ↥(facFst S e).range := MonoidHom.ofInjective (facFst_injective S e)
  let eB : B ≃* ↥(facSnd S e).range := MonoidHom.ofInjective (facSnd_injective S e)
  have hsimple : ∀ i, IsSimpleGroup ↥(F i) := by
    intro i
    cases i
    · exact eB.symm.isSimpleGroup
    · exact eA.symm.isSimpleGroup
  have hnonab : ∀ i, ∃ x y : ↥(F i), x * y ≠ y * x := by
    intro i
    cases i
    · obtain ⟨x, y, hxy⟩ := hBn
      exact ⟨eB x, eB y, fun h => hxy (eB.injective (by rw [map_mul, map_mul]; exact h))⟩
    · obtain ⟨x, y, hxy⟩ := hAn
      exact ⟨eA x, eA y, fun h => hxy (eA.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hcomm : ∀ i j, i ≠ j → ∀ x ∈ F i, ∀ y ∈ F j, x * y = y * x := by
    intro i j hij x hx y hy
    cases i <;> cases j
    · exact absurd rfl hij
    · obtain ⟨b, rfl⟩ := hx
      obtain ⟨a, rfl⟩ := hy
      exact (facFst_comm S e a b).symm
    · obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact facFst_comm S e a b
    · exact absurd rfl hij
  have hinj : Function.Injective F := by
    intro i j hij
    by_contra hne
    obtain ⟨x, y, hxy⟩ := hnonab i
    apply hxy
    apply Subtype.ext
    have hy' : (y : H) ∈ F j := hij ▸ y.2
    exact hcomm i j hne x x.2 y hy'
  have hout : ∀ i, Group.IsSolvable (Outer ↥(F i)) := by
    intro i
    cases i
    · exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eB
    · exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eA
  have hperm : Group.IsSolvable (Equiv.Perm Bool) := Equiv.Perm.isSolvable (by simp)
  have hSn : ∀ (h : H) (s : H), s ∈ (⨆ i, F i : Subgroup H) →
      h * s * h⁻¹ ∈ (⨆ i, F i : Subgroup H) := by
    intro h s hs
    rw [hFsup] at hs ⊢
    exact Subgroup.Normal.conj_mem inferInstance s hs h
  have hstab := exists_eq_of_conj_factor F hsimple hnonab hcomm hSn
  rw [← hFsup] at hC ⊢
  have hSnormal : (⨆ i, F i : Subgroup H).Normal := by rw [hFsup]; infer_instance
  exact perfect_le_iSup_of_factors F hinj hstab hcomm hout hperm hC hSnormal hR

end Binary


section OneAndThree

variable [Finite H]

theorem perfect_le_of_outer (S R : Subgroup H) [S.Normal]
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (S : Set H)))
    (hO : Group.IsSolvable (Outer ↥S)) (hR : ⁅R, R⁆ = R) : R ≤ S := by
  classical
  have hsup : (⨆ _ : Unit, S) = S := iSup_const
  have hstab : ∀ (h : H) (i : Unit),
      ∃ j, Subgroup.map (MulAut.conj h).toMonoidHom ((fun _ : Unit => S) i) =
        (fun _ : Unit => S) j := by
    intro h i
    refine ⟨i, ?_⟩
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using Subgroup.Normal.conj_mem inferInstance y hy h
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance x hx h⁻¹
  have h := perfect_le_iSup_of_factors (ι := Unit) (fun _ => S) (fun _ _ _ => rfl) hstab
    (fun i j hij => absurd (Subsingleton.elim i j) hij) (fun _ => hO)
    (Equiv.Perm.isSolvable (by simp)) (by rw [hsup]; exact hC) (by rw [hsup]; infer_instance) hR
  rwa [hsup] at h


section Ternary

@[expose] def facTri (S : Subgroup H) {A B C : Type*} [Group A] [Group B] [Group C]
    (e : ↥S ≃* A × (B × C)) : Option Bool → Subgroup H
  | none => (S.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A (B × C)))).range
  | some true => (S.subtype.comp (e.symm.toMonoidHom.comp
      ((MonoidHom.inr A (B × C)).comp (MonoidHom.inl B C)))).range
  | some false => (S.subtype.comp (e.symm.toMonoidHom.comp
      ((MonoidHom.inr A (B × C)).comp (MonoidHom.inr B C)))).range

theorem facTri_le (S : Subgroup H) {A B C : Type*} [Group A] [Group B] [Group C]
    (e : ↥S ≃* A × (B × C)) (o : Option Bool) : facTri S e o ≤ S := by
  cases o with
  | none =>
    rintro _ ⟨a, rfl⟩
    exact (e.symm (a, 1)).2
  | some b =>
    cases b
    · rintro _ ⟨a, rfl⟩
      exact (e.symm (1, (1, a))).2
    · rintro _ ⟨a, rfl⟩
      exact (e.symm (1, (a, 1))).2

theorem facTri_sup (S : Subgroup H) {A B C : Type*} [Group A] [Group B] [Group C]
    (e : ↥S ≃* A × (B × C)) : (⨆ o, facTri S e o) = S := by
  refine le_antisymm (iSup_le (facTri_le S e)) fun x hx => ?_
  set p := e ⟨x, hx⟩ with hp
  have h1 : p = (p.1, (1, 1)) * ((1, (p.2.1, 1)) * (1, (1, p.2.2))) := by
    rcases p with ⟨a, b, c⟩
    simp
  have h2 : (⟨x, hx⟩ : S) = e.symm (p.1, (1, 1)) *
      (e.symm (1, (p.2.1, 1)) * e.symm (1, (1, p.2.2))) := by
    rw [← map_mul, ← map_mul, ← h1, hp, e.symm_apply_apply]
  have h3 : x = ((e.symm (p.1, (1, 1)) : S) : H) *
      (((e.symm (1, (p.2.1, 1)) : S) : H) * ((e.symm (1, (1, p.2.2)) : S) : H)) :=
    congrArg Subtype.val h2
  rw [h3]
  refine mul_mem (le_iSup (facTri S e) none ⟨p.1, rfl⟩) (mul_mem ?_ ?_)
  · exact le_iSup (facTri S e) (some true) ⟨p.2.1, rfl⟩
  · exact le_iSup (facTri S e) (some false) ⟨p.2.2, rfl⟩


theorem facTri_comm (S : Subgroup H) {A B C : Type*} [Group A] [Group B] [Group C]
    (e : ↥S ≃* A × (B × C)) {o o' : Option Bool} (hoo : o ≠ o') :
    ∀ x ∈ facTri S e o, ∀ y ∈ facTri S e o', x * y = y * x := by
  have key : ∀ u v : A × (B × C), u * v = v * u →
      ((e.symm u : S) : H) * ((e.symm v : S) : H) =
        ((e.symm v : S) : H) * ((e.symm u : S) : H) := by
    intro u v huv
    have : e.symm u * e.symm v = e.symm v * e.symm u := by rw [← map_mul, ← map_mul, huv]
    exact congrArg Subtype.val this
  cases o with
  | none =>
    cases o' with
    | none => exact absurd rfl hoo
    | some b =>
      rintro _ ⟨a, rfl⟩
      cases b
      · rintro _ ⟨c, rfl⟩
        exact key _ _ (by simp)
      · rintro _ ⟨c, rfl⟩
        exact key _ _ (by simp)
  | some b =>
    cases b
    · cases o' with
      | none =>
        rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
        exact key _ _ (by simp)
      | some b' =>
        cases b'
        · exact absurd rfl hoo
        · rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
          exact key _ _ (by simp)
    · cases o' with
      | none =>
        rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
        exact key _ _ (by simp)
      | some b' =>
        cases b'
        · rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
          exact key _ _ (by simp)
        · exact absurd rfl hoo


theorem perfect_le_of_prod3 (S R : Subgroup H) [S.Normal]
    (hC : Group.IsSolvable ↥(Subgroup.centralizer (S : Set H)))
    {A B C : Type} [Group A] [Group B] [Group C] [IsSimpleGroup A] [IsSimpleGroup B]
    [IsSimpleGroup C]
    (hAn : ∃ x y : A, x * y ≠ y * x) (hBn : ∃ x y : B, x * y ≠ y * x)
    (hCn : ∃ x y : C, x * y ≠ y * x)
    (hAo : Group.IsSolvable (Outer A)) (hBo : Group.IsSolvable (Outer B))
    (hCo : Group.IsSolvable (Outer C))
    (e : ↥S ≃* A × (B × C)) (hR : ⁅R, R⁆ = R) : R ≤ S := by
  classical
  let φA : A →* H := S.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A (B × C)))
  let φB : B →* H := S.subtype.comp (e.symm.toMonoidHom.comp
    ((MonoidHom.inr A (B × C)).comp (MonoidHom.inl B C)))
  let φC : C →* H := S.subtype.comp (e.symm.toMonoidHom.comp
    ((MonoidHom.inr A (B × C)).comp (MonoidHom.inr B C)))
  have iA : Function.Injective φA := by
    intro a a' h
    have h1 : e.symm (a, (1, 1)) = e.symm (a', (1, 1)) := Subtype.ext h
    exact (Prod.mk.inj (e.symm.injective h1)).1
  have iB : Function.Injective φB := by
    intro a a' h
    have h1 : e.symm (1, (a, 1)) = e.symm (1, (a', 1)) := Subtype.ext h
    have := (Prod.mk.inj (e.symm.injective h1)).2
    exact (Prod.mk.inj this).1
  have iC : Function.Injective φC := by
    intro a a' h
    have h1 : e.symm (1, (1, a)) = e.symm (1, (1, a')) := Subtype.ext h
    have := (Prod.mk.inj (e.symm.injective h1)).2
    exact (Prod.mk.inj this).2
  let eA : A ≃* ↥(facTri S e none) := MonoidHom.ofInjective iA
  let eB : B ≃* ↥(facTri S e (some true)) := MonoidHom.ofInjective iB
  let eC : C ≃* ↥(facTri S e (some false)) := MonoidHom.ofInjective iC
  have hsimple : ∀ o, IsSimpleGroup ↥(facTri S e o) := by
    intro o
    cases o with
    | none => exact eA.symm.isSimpleGroup
    | some b =>
      cases b
      · exact eC.symm.isSimpleGroup
      · exact eB.symm.isSimpleGroup
  have nonab : ∀ {T : Type} [Group T] (U : Subgroup H) (f : T ≃* ↥U),
      (∃ x y : T, x * y ≠ y * x) → ∃ x y : ↥U, x * y ≠ y * x := by
    intro T _ U f ⟨x, y, hxy⟩
    exact ⟨f x, f y, fun h => hxy (f.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hnonab : ∀ o, ∃ x y : ↥(facTri S e o), x * y ≠ y * x := by
    intro o
    cases o with
    | none => exact nonab _ eA hAn
    | some b =>
      cases b
      · exact nonab _ eC hCn
      · exact nonab _ eB hBn
  have hcomm : ∀ o o', o ≠ o' → ∀ x ∈ facTri S e o, ∀ y ∈ facTri S e o', x * y = y * x :=
    fun o o' hoo => facTri_comm S e hoo
  have hinj : Function.Injective (facTri S e) := by
    intro o o' hoo
    by_contra hne
    obtain ⟨x, y, hxy⟩ := hnonab o
    apply hxy
    apply Subtype.ext
    have hy' : (y : H) ∈ facTri S e o' := hoo ▸ y.2
    exact hcomm o o' hne x x.2 y hy'
  have hout : ∀ o, Group.IsSolvable (Outer ↥(facTri S e o)) := by
    intro o
    cases o with
    | none =>
      haveI := hAo
      exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eA
    | some b =>
      cases b
      · haveI := hCo
        exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eC
      · haveI := hBo
        exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv eB
  have hperm : Group.IsSolvable (Equiv.Perm (Option Bool)) :=
    Equiv.Perm.isSolvable (by simp)
  have hsup := facTri_sup S e
  have hSn : ∀ (h : H) (s : H), s ∈ (⨆ i, facTri S e i : Subgroup H) →
      h * s * h⁻¹ ∈ (⨆ i, facTri S e i : Subgroup H) := by
    intro h s hs
    rw [hsup] at hs ⊢
    exact Subgroup.Normal.conj_mem inferInstance s hs h
  have hstab := exists_eq_of_conj_factor (facTri S e) hsimple hnonab hcomm hSn
  rw [← hsup] at hC ⊢
  have hSnormal : (⨆ i, facTri S e i : Subgroup H).Normal := by rw [hsup]; infer_instance
  exact perfect_le_iSup_of_factors (facTri S e) hinj hstab hcomm hout hperm hC hSnormal hR

end Ternary

end OneAndThree


section Embed

variable {A B : Type*} [Group A] [Group B]

theorem card_le_or_le_prod [Finite A] [Finite B] (R : Subgroup (A × B)) [IsSimpleGroup ↥R] :
    Nat.card R ≤ Nat.card A ∨ (R ≤ (⊥ : Subgroup A).prod ⊤ ∧ Nat.card R ≤ Nat.card B) := by
  let f : ↥R →* A := (MonoidHom.fst A B).comp R.subtype
  have hK : f.ker.Normal := f.normal_ker
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · left
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp h
    exact Nat.card_le_card_of_injective f hinj
  · right
    have hle : R ≤ (⊥ : Subgroup A).prod ⊤ := by
      intro x hx
      have : (⟨x, hx⟩ : ↥R) ∈ f.ker := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_prod.mpr ⟨(MonoidHom.mem_ker.mp this), Subgroup.mem_top _⟩
    refine ⟨hle, ?_⟩
    let g : ↥R →* B := (MonoidHom.snd A B).comp R.subtype
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have h1 : (x : A × B).1 = 1 := (Subgroup.mem_prod.mp (hle x.2)).1
      have h2 : (y : A × B).1 = 1 := (Subgroup.mem_prod.mp (hle y.2)).1
      exact Prod.ext (h1.trans h2.symm) hxy
    exact Nat.card_le_card_of_injective g hinj


theorem card_le_or_le_prod3 {C : Type*} [Group C] [Finite A] [Finite B] [Finite C]
    (R : Subgroup (A × (B × C))) [IsSimpleGroup ↥R] :
    Nat.card R ≤ Nat.card A ∨ Nat.card R ≤ Nat.card B ∨ Nat.card R ≤ Nat.card C := by
  rcases card_le_or_le_prod R with h | ⟨hle, -⟩
  · exact Or.inl h
  · right
    let g : ↥R →* B × C := (MonoidHom.snd A (B × C)).comp R.subtype
    have hinj : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      have h1 : (x : A × (B × C)).1 = 1 := (Subgroup.mem_prod.mp (hle x.2)).1
      have h2 : (y : A × (B × C)).1 = 1 := (Subgroup.mem_prod.mp (hle y.2)).1
      exact Prod.ext (h1.trans h2.symm) hxy
    let e : ↥R ≃* ↥g.range := MonoidHom.ofInjective hinj
    haveI : IsSimpleGroup ↥g.range := e.symm.isSimpleGroup
    have hcard : Nat.card ↥g.range = Nat.card R := (Nat.card_congr e.toEquiv).symm
    rcases card_le_or_le_prod g.range with h | ⟨-, h⟩
    · exact Or.inl (hcard ▸ h)
    · exact Or.inr (hcard ▸ h)


theorem card_le_or_le_of_embeds {R : Type*} [Group R] [IsSimpleGroup R] [Finite A] [Finite B]
    (f : R →* A × B) (hf : Function.Injective f) :
    Nat.card R ≤ Nat.card A ∨ (Nat.card R ≤ Nat.card B ∧ ∀ r : R, (f r).1 = 1) := by
  let e : R ≃* ↥f.range := MonoidHom.ofInjective hf
  haveI : IsSimpleGroup ↥f.range := e.symm.isSimpleGroup
  have hcard : Nat.card ↥f.range = Nat.card R := (Nat.card_congr e.toEquiv).symm
  rcases card_le_or_le_prod f.range with h | ⟨hle, h⟩
  · exact Or.inl (hcard ▸ h)
  · refine Or.inr ⟨hcard ▸ h, fun r => ?_⟩
    exact (Subgroup.mem_prod.mp (hle ⟨r, rfl⟩)).1

theorem card_le_or_le_of_embeds3 {C : Type*} [Group C] {R : Type*} [Group R] [IsSimpleGroup R]
    [Finite A] [Finite B] [Finite C] (f : R →* A × (B × C)) (hf : Function.Injective f) :
    Nat.card R ≤ Nat.card A ∨ Nat.card R ≤ Nat.card B ∨ Nat.card R ≤ Nat.card C := by
  let e : R ≃* ↥f.range := MonoidHom.ofInjective hf
  haveI : IsSimpleGroup ↥f.range := e.symm.isSimpleGroup
  have hcard : Nat.card ↥f.range = Nat.card R := (Nat.card_congr e.toEquiv).symm
  rcases card_le_or_le_prod3 f.range with h | h | h
  · exact Or.inl (hcard ▸ h)
  · exact Or.inr (Or.inl (hcard ▸ h))
  · exact Or.inr (Or.inr (hcard ▸ h))

theorem exists_injective_quotient {G : Type*} [Group G] {N R S : Subgroup G} (hNR : N ≤ R)
    (hRS : R ≤ S) [(N.subgroupOf R).Normal] [(N.subgroupOf S).Normal] :
    ∃ ι : ↥R ⧸ N.subgroupOf R →* ↥S ⧸ N.subgroupOf S, Function.Injective ι ∧
      ∀ r : ↥R, ι (QuotientGroup.mk r) = QuotientGroup.mk (Subgroup.inclusion hRS r) := by
  refine ⟨QuotientGroup.map (N.subgroupOf R) (N.subgroupOf S) (Subgroup.inclusion hRS)
    (fun x hx => hx), ?_, fun r => rfl⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have h1 : (QuotientGroup.mk (Subgroup.inclusion hRS y) : ↥S ⧸ N.subgroupOf S) = 1 := hx
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
  exact h2

end Embed

end CFSG.RankThree.GF2n.Stroth80
