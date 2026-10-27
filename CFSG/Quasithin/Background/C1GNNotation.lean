module

public import CFSG.Quasithin.Background.C1GNDefs
public import CFSG.Quasithin.EmptyFaithful.Setting
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.Equivariance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C1GN

variable {G : Type*} [Group G]

theorem baum_le (S : Subgroup G) : baum S ≤ S := inf_le_left

theorem thompsonJ_le (S : Subgroup G) : thompsonJ S ≤ S :=
  iSup_le fun _ => iSup_le fun hA => hA.1

theorem omegaOneCenterOf_le_self (S : Subgroup G) : omegaOneCenterOf S ≤ S :=
  (Subgroup.closure_le S).mpr fun _ hx => hx.1.1

theorem omegaOneCenterOf_le_centerOf (X : Subgroup G) : omegaOneCenterOf X ≤ centerOf X :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem omegaOneCenterOf_le_baum (S : Subgroup G) : omegaOneCenterOf S ≤ baum S := by
  refine le_inf ((omegaOneCenterOf_le_centerOf S).trans inf_le_left) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have heJ : e ∈ thompsonJ S := (omegaOneCenterOf_le_self _) he
  have heS : e ∈ S := (thompsonJ_le S) heJ
  exact (Subgroup.mem_centralizer_iff.1 (omegaOneCenterOf_le_centerOf S hx).2 e heS)

theorem baum_baum [Finite G] (S : Subgroup G) : baum (baum S) = baum S :=
  (baum_eq_of_le (le_refl _) (baum_le S)).symm

theorem isElemAbelian_map_subtype {p : ℕ} {S : Subgroup G} {E : Subgroup S} :
    IsElemAbelian p (E.map S.subtype) ↔ IsElemAbelian p E := by
  unfold IsElemAbelian
  rw [isMulCommutative_subgroup_iff, isMulCommutative_subgroup_iff]
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨fun x hx y hy => Subtype.ext ?_, fun x hx => Subtype.ext ?_⟩
    · simpa using hc x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
    · simpa using hp x ⟨x, hx, rfl⟩
  · rintro ⟨hc, hp⟩
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simpa using congrArg Subtype.val (hc x hx y hy)
    · rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hp x hx)

theorem card_map_subtype' {S : Subgroup G} (E : Subgroup S) :
    Nat.card (E.map S.subtype) = Nat.card E :=
  Nat.card_congr (E.equivMapOfInjective S.subtype S.subtype_injective).toEquiv.symm

theorem isMaxElemAbelian_top_iff {S : Subgroup G} {A : Subgroup S} :
    IsMaxElemAbelian (⊤ : Subgroup S) A ↔ IsMaxElemAbelian S (A.map S.subtype) := by
  unfold IsMaxElemAbelian
  constructor
  · rintro ⟨-, hA, hmax⟩
    refine ⟨Subgroup.map_subtype_le A, isElemAbelian_map_subtype.mpr hA, fun B hBS hB => ?_⟩
    have hB' : IsElemAbelian 2 (B.subgroupOf S) := by
      rw [← isElemAbelian_map_subtype, Subgroup.map_subgroupOf_eq_of_le hBS]
      exact hB
    have h := hmax (B.subgroupOf S) le_top hB'
    have hBcard : Nat.card B = Nat.card (B.subgroupOf S) := by
      rw [← card_map_subtype' (B.subgroupOf S), Subgroup.map_subgroupOf_eq_of_le hBS]
    rw [hBcard, card_map_subtype']
    exact h
  · rintro ⟨-, hA, hmax⟩
    refine ⟨le_top, isElemAbelian_map_subtype.mp hA, fun B _ hB => ?_⟩
    have h := hmax (B.map S.subtype) (Subgroup.map_subtype_le B)
      (isElemAbelian_map_subtype.mpr hB)
    rwa [card_map_subtype', card_map_subtype'] at h

theorem thompsonJ_eq_map_top (S : Subgroup G) :
    thompsonJ S = (thompsonJ (⊤ : Subgroup S)).map S.subtype := by
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    have hA' : IsMaxElemAbelian (⊤ : Subgroup S) (A.subgroupOf S) := by
      rw [isMaxElemAbelian_top_iff, Subgroup.map_subgroupOf_eq_of_le hA.1]
      exact hA
    have h1 : A.subgroupOf S ≤ thompsonJ (⊤ : Subgroup S) :=
      le_iSup₂_of_le (f := fun (B : Subgroup S) (_ : IsMaxElemAbelian (⊤ : Subgroup S) B) => B)
        (A.subgroupOf S) hA' le_rfl
    have h2 := Subgroup.map_mono (f := S.subtype) h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hA.1] at h2
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A' hA' => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le (f := fun (B : Subgroup G) (_ : IsMaxElemAbelian S B) => B)
      (A'.map S.subtype) (isMaxElemAbelian_top_iff.mp hA') le_rfl

theorem map_top_mulEquiv {H : Type*} [Group H] (φ : H ≃* H) :
    (⊤ : Subgroup H).map φ.toMonoidHom = ⊤ := by
  rw [← MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr φ.surjective

theorem omegaOneCenterOf_map_subtype (A : Subgroup G) (X : Subgroup A) :
    omegaOneCenterOf (X.map A.subtype) = (omegaOneCenterOf X).map A.subtype := by
  unfold omegaOneCenterOf omegaOneOf centerOf
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨⟨y, hyX, rfl⟩, hyC⟩, hx2⟩
    refine ⟨y, ⟨⟨hyX, ?_⟩, ?_⟩, rfl⟩
    · refine Subgroup.mem_centralizer_iff.2 fun w hw => Subtype.ext ?_
      exact Subgroup.mem_centralizer_iff.1 hyC (w : G) ⟨w, hw, rfl⟩
    · exact Subtype.ext (by simpa using hx2)
  · rintro ⟨y, ⟨⟨hyX, hyC⟩, hy2⟩, rfl⟩
    refine ⟨⟨⟨y, hyX, rfl⟩, ?_⟩, by simpa using congrArg Subtype.val hy2⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hyC w hw)

theorem baum_eq_map_top (S : Subgroup G) :
    baum S = (baum (⊤ : Subgroup S)).map S.subtype := by
  have hJ : thompsonJ S = (thompsonJ (⊤ : Subgroup S)).map S.subtype :=
    thompsonJ_eq_map_top S
  have hE : omegaOneCenterOf (thompsonJ S) =
      (omegaOneCenterOf (thompsonJ (⊤ : Subgroup S))).map S.subtype := by
    rw [hJ]
    exact omegaOneCenterOf_map_subtype S _
  unfold baum
  rw [hE, top_inf_eq]
  ext x
  constructor
  · rintro ⟨hxS, hxC⟩
    refine ⟨⟨x, hxS⟩, ?_, rfl⟩
    refine Subgroup.mem_centralizer_iff.2 fun w hw => Subtype.ext ?_
    exact Subgroup.mem_centralizer_iff.1 hxC (w : G) ⟨w, hw, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨w, hw, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy w hw)

theorem characteristic_baum (S : Subgroup G) : ((baum S).subgroupOf S).Characteristic := by
  have h : (baum S).subgroupOf S = baum (⊤ : Subgroup S) := by
    rw [baum_eq_map_top S, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
  rw [h]
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  rw [baum_map_mulEquiv φ, map_top_mulEquiv]

theorem characteristic_subgroupOf_trans {T B C : Subgroup G} (hBT : B ≤ T) (hCB : C ≤ B)
    (hB : (B.subgroupOf T).Characteristic) (hC : (C.subgroupOf B).Characteristic) :
    (C.subgroupOf T).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  have hmem : ∀ (ψ : ↥T ≃* ↥T) (t : ↥T), (ψ t : G) ∈ B ↔ (t : G) ∈ B := by
    intro ψ t
    have h := Subgroup.characteristic_iff_map_eq.1 hB ψ.symm
    have := Subgroup.mem_map_equiv (f := ψ.symm) (K := B.subgroupOf T) (x := t)
    rw [h] at this
    simp only [Subgroup.mem_subgroupOf] at this
    simpa using this.symm
  let ψ : ↥B ≃* ↥B :=
    { toFun := fun b => ⟨(φ ⟨b, hBT b.2⟩ : G), (hmem φ ⟨b, hBT b.2⟩).2 b.2⟩
      invFun := fun b => ⟨(φ.symm ⟨b, hBT b.2⟩ : G), (hmem φ.symm ⟨b, hBT b.2⟩).2 b.2⟩
      left_inv := fun b => by simp
      right_inv := fun b => by simp
      map_mul' := fun a b => Subtype.ext
        (congrArg (fun x : ↥T => (x : G))
          (map_mul φ (⟨(a : G), hBT a.2⟩ : ↥T) ⟨(b : G), hBT b.2⟩)) }
  rintro _ ⟨t, ht, rfl⟩
  have ht' : (t : G) ∈ C := ht
  have htB : (t : G) ∈ B := hCB ht'
  have hψ := Subgroup.characteristic_iff_map_eq.1 hC ψ
  have h1 : ψ ⟨t, htB⟩ ∈ (C.subgroupOf B).map ψ.toMonoidHom :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht')
  rw [hψ] at h1
  exact h1

theorem centerOf_subgroupOf (T : Subgroup G) :
    (centerOf T).subgroupOf T = Subgroup.center ↥T := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hx⟩ y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hx (y : G) y.2)
  · intro hx
    refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    exact congrArg Subtype.val (hx ⟨y, hy⟩)

end C1GN

section Remark

variable {G : Type*} [Group G] [Finite G]

theorem isC118Pair_of_baum {T C₁ C₂ : Subgroup G} (hT : IsPGroup 2 T)
    (h : IsC118Pair (baum T) C₁ C₂) : IsC118Pair T (centerOf T ⊓ C₁) C₂ := by
  obtain ⟨h1ne, h1Z, h1ch, h2ne, h2B, h2ch, hH⟩ := h
  have hbb : baum (baum T) = baum T := C1GN.baum_baum T
  have hBT : baum T ≤ T := C1GN.baum_le T
  have hC₁B : C₁ ≤ baum T :=
    h1Z.trans ((C1GN.omegaOneCenterOf_le_centerOf _).trans inf_le_left)
  have hC₁T : C₁ ≤ T := hC₁B.trans hBT
  have hCharT : (C₁.subgroupOf T).Characteristic :=
    C1GN.characteristic_subgroupOf_trans hBT hC₁B (C1GN.characteristic_baum T) h1ch
  rw [hbb] at h2B h2ch hH
  refine ⟨?_, ?_, ?_, h2ne, h2B, h2ch, ?_⟩
  ·
    have hT' : IsPGroup 2 ↥T := hT
    have : Group.IsNilpotent ↥T := hT'.isNilpotent
    have hne : C₁.subgroupOf T ≠ ⊥ := by
      obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := C₁)).1 h1ne
      intro hbot
      have : (⟨(x : G), hC₁T x.2⟩ : ↥T) ∈ C₁.subgroupOf T := x.2
      rw [hbot, Subgroup.mem_bot] at this
      have h' : (x : G) = 1 := congrArg (fun z : ↥T => (z : G)) this
      exact hx1 (Subtype.ext h')
    have := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := C₁.subgroupOf T) hne
    obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 this
    intro hbot
    have hy := y.2
    have hyG : (((y : ↥(C₁.subgroupOf T ⊓ Subgroup.center ↥T)) : ↥T) : G) ∈ centerOf T ⊓ C₁ :=
      ⟨⟨((y : ↥(C₁.subgroupOf T ⊓ Subgroup.center ↥T)) : ↥T).2,
        Subgroup.mem_centralizer_iff.2 fun z hz =>
          congrArg Subtype.val ((Subgroup.mem_center_iff.1 hy.2 ⟨z, hz⟩))⟩, hy.1⟩
    rw [hbot, Subgroup.mem_bot] at hyG
    exact hy1 (Subtype.ext (Subtype.ext hyG))
  ·
    intro x hx
    exact Subgroup.subset_closure ⟨hx.1, sq_eq_one_of_mem_omegaOneCenter _ (h1Z hx.2)⟩
  ·
    have hinf : (centerOf T ⊓ C₁).subgroupOf T = Subgroup.center ↥T ⊓ C₁.subgroupOf T := by
      rw [← C1GN.centerOf_subgroupOf T]
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hinf]
    have := hCharT
    infer_instance
  · intro Ω _ _ H ι hι hcl
    rcases hH Ω H ι hι hcl with h | h | h
    · left
      refine le_trans (Subgroup.map_mono ?_) h
      exact fun x hx => hx.2
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

structure IsGNChoice (C₁ C₂ : Subgroup G → Subgroup G) : Prop where
  pair : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → IsC118Pair T (C₁ T) (C₂ T)
  c2_eq : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → C₂ T = C₂ (baum T)
  c1_eq : ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → C₁ T = centerOf T ⊓ C₁ (baum T)

end Remark

section Choice

variable {G : Type} [Group G] [Finite G]

theorem C1GN.baum_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T) (hT0 : T ≠ ⊥) : baum T ≠ ⊥ := by
  intro h
  apply quasithinOmegaOneCenter_ne_bot hT hT0
  exact le_bot_iff.1 (h ▸ C1GN.omegaOneCenterOf_le_baum T)

theorem exists_isGNChoice (hGN : TheoremC118) :
    ∃ C₁ C₂ : Subgroup G → Subgroup G, IsGNChoice C₁ C₂ := by
  classical
  have h : ∀ B : Subgroup G, ∃ p : Subgroup G × Subgroup G,
      IsPGroup 2 B → B ≠ ⊥ → IsC118Pair B p.1 p.2 := by
    intro B
    by_cases hB : IsPGroup 2 B ∧ B ≠ ⊥
    · obtain ⟨C₁, C₂, h⟩ := hGN G B hB.1 hB.2
      exact ⟨(C₁, C₂), fun _ _ => h⟩
    · exact ⟨(⊥, ⊥), fun h1 h2 => absurd ⟨h1, h2⟩ hB⟩
  choose r hr using h
  refine ⟨fun T => centerOf T ⊓ (r (baum T)).1, fun T => (r (baum T)).2, ⟨?_, ?_, ?_⟩⟩
  · intro T hT hT0
    exact isC118Pair_of_baum hT
      (hr (baum T) (hT.to_le (C1GN.baum_le T)) (C1GN.baum_ne_bot hT hT0))
  · intro T _ _
    simp only [C1GN.baum_baum]
  · intro T hT hT0
    simp only [C1GN.baum_baum]
    have h1 := (hr (baum T) (hT.to_le (C1GN.baum_le T)) (C1GN.baum_ne_bot hT hT0)).2.1
    have h2 : (r (baum T)).1 ≤ centerOf (baum T) :=
      h1.trans (C1GN.omegaOneCenterOf_le_centerOf _)
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun hx => ⟨hx.1, h2 hx.2, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩

variable {C₁ C₂ : Subgroup G → Subgroup G}

theorem IsGNChoice.dichotomy (hC : IsGNChoice C₁ C₂) {T H : Subgroup G} (hT : IsPGroup 2 T)
    (hT0 : T ≠ ⊥) (hH : InClassG H (baum T)) :
    C₁ T ≤ centerOf H ∨ H ≤ Subgroup.normalizer (C₂ T : Set G) ∨
      IsL2OrA3Block H (twoResidual H) := by
  obtain ⟨-, h1Z, -, -, h2B, -, hall⟩ := hC.pair T hT hT0
  have h1B : C₁ T ≤ baum T := h1Z.trans (C1GN.omegaOneCenterOf_le_baum T)
  have := hall G H (baum T).subtype (baum T).subtype_injective (by rwa [Subgroup.range_subtype])
  rwa [Subgroup.map_subgroupOf_eq_of_le h1B, Subgroup.map_subgroupOf_eq_of_le h2B] at this

end Choice

end CFSG.Quasithin
