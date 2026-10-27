module

public import CFSG.Quasithin.AppendixH.H12.Trans
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

namespace Trans

variable {Γ : Type*} [Group Γ] {L' : Subgroup Γ} {G : Type*} [Group G] {L : Subgroup G}
  {V' V : Type*} [CommGroup V'] [CommGroup V] {ρ' : Γ →* MulAut V'} {ρ : G →* MulAut V}
  (τ : Trans L' L ρ' ρ)

private theorem injective_toG_hom :
    Function.Injective (L.subtype.comp τ.φ.toMonoidHom) :=
  fun _ _ h => τ.φ.injective (L.subtype_injective h)

private theorem toG_eq_map (X : Subgroup Γ) :
    τ.toG X = (X.subgroupOf L').map (L.subtype.comp τ.φ.toMonoidHom) := by
  unfold toG
  rw [Subgroup.map_map]

private theorem fromG_eq_map (Y : Subgroup G) :
    τ.fromG Y = (Y.subgroupOf L).map (L'.subtype.comp τ.φ.symm.toMonoidHom) := by
  unfold fromG
  rw [Subgroup.map_map]

private theorem pCoreOf_map_injective {A B : Type*} [Group A] [Group B] (p : ℕ)
    (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    pCoreOf p (H.map f) = (pCoreOf p H).map f := by
  let e : H ≃* ↥(H.map f) := H.equivMapOfInjective f hf
  have hcore : (CFSG.pCore p H).map e.toMonoidHom = CFSG.pCore p ↥(H.map f) :=
    CFSG.pCore_map_iso p e
  have hh : (H.map f).subtype.comp e.toMonoidHom = f.comp H.subtype :=
    MonoidHom.ext fun x => rfl
  unfold pCoreOf
  rw [← hcore, Subgroup.map_map, Subgroup.map_map, hh]

private theorem map_center_mulEquiv {A : Type*} [Group A] {B : Type*} [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Subgroup.mem_center_iff] at ha ⊢
    intro c
    obtain ⟨a', rfl⟩ := e.surjective c
    change e a' * e a = e a * e a'
    rw [← map_mul, ← map_mul, ha a']
  · intro hb
    refine ⟨e.symm b, ?_, by simp⟩
    rw [Subgroup.mem_center_iff]
    intro a
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (Subgroup.mem_center_iff.mp hb) (e a)

private theorem center_subgroupOf :
    ((Subgroup.center ↥L').map L'.subtype).subgroupOf L' = Subgroup.center ↥L' := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    have : z = x := Subtype.ext hzx
    rwa [this] at hz
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_toG {X : Subgroup Γ} {g : G} :
    g ∈ τ.toG X ↔ ∃ (h : Γ) (hL : h ∈ L'), h ∈ X ∧ ((τ.φ ⟨h, hL⟩ : ↥L) : G) = g := by
  constructor
  · intro hg
    rw [toG_eq_map] at hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨b, hb, hψ⟩ := hg
    exact ⟨b.1, b.2, Subgroup.mem_subgroupOf.mp hb, hψ⟩
  · rintro ⟨h, hL, hh, hψ⟩
    rw [toG_eq_map, Subgroup.mem_map]
    exact ⟨⟨h, hL⟩, Subgroup.mem_subgroupOf.mpr hh, hψ⟩

theorem mem_fromG {Y : Subgroup G} {h : Γ} :
    h ∈ τ.fromG Y ↔ ∃ (g : G) (hL : g ∈ L), g ∈ Y ∧ ((τ.φ.symm ⟨g, hL⟩ : ↥L') : Γ) = h := by
  constructor
  · intro hh
    rw [fromG_eq_map] at hh
    rw [Subgroup.mem_map] at hh
    obtain ⟨b, hb, hψ⟩ := hh
    exact ⟨b.1, b.2, Subgroup.mem_subgroupOf.mp hb, hψ⟩
  · rintro ⟨g, hL, hg, hψ⟩
    rw [fromG_eq_map, Subgroup.mem_map]
    exact ⟨⟨g, hL⟩, Subgroup.mem_subgroupOf.mpr hg, hψ⟩

theorem toG_le (X : Subgroup Γ) : τ.toG X ≤ L := by
  intro g hg
  obtain ⟨h, hL, _, hφ⟩ := (mem_toG τ).mp hg
  rw [← hφ]
  exact (τ.φ ⟨h, hL⟩).2

theorem fromG_le (Y : Subgroup G) : τ.fromG Y ≤ L' := by
  intro h hh
  obtain ⟨g, hL, _, hφ⟩ := (mem_fromG τ).mp hh
  rw [← hφ]
  exact (τ.φ.symm ⟨g, hL⟩).2

theorem toG_top : τ.toG L' = L := by
  apply le_antisymm (τ.toG_le L')
  intro g hg
  rw [mem_toG]
  exact ⟨(τ.φ.symm ⟨g, hg⟩ : ↥L').1, (τ.φ.symm ⟨g, hg⟩).2,
    (τ.φ.symm ⟨g, hg⟩).2, by simp⟩

theorem fromG_top : τ.fromG L = L' := by
  apply le_antisymm (τ.fromG_le L)
  intro h hh
  rw [mem_fromG]
  exact ⟨(τ.φ ⟨h, hh⟩ : ↥L).1, (τ.φ ⟨h, hh⟩).2,
    (τ.φ ⟨h, hh⟩).2, by simp⟩

theorem toG_fromG {Y : Subgroup G} (hY : Y ≤ L) : τ.toG (τ.fromG Y) = Y := by
  apply le_antisymm
  · intro g hg
    rw [mem_toG] at hg
    obtain ⟨h, hL, hh, hφ⟩ := hg
    rw [mem_fromG] at hh
    obtain ⟨g', hL', hg', hs⟩ := hh
    have hsub : (⟨h, hL⟩ : ↥L') = τ.φ.symm ⟨g', hL'⟩ := (Subtype.ext hs).symm
    have hφ' : ((τ.φ ⟨h, hL⟩ : ↥L) : G) = g' := by
      have := congrArg (fun z : ↥L' => ((τ.φ z : ↥L) : G)) hsub
      simpa using this
    rw [← hφ, hφ']
    exact hg'
  · intro g hg
    rw [mem_toG]
    refine ⟨(τ.φ.symm ⟨g, hY hg⟩ : ↥L').1, (τ.φ.symm ⟨g, hY hg⟩).2, ?_, ?_⟩
    · rw [mem_fromG]
      exact ⟨g, hY hg, hg, rfl⟩
    · simp

theorem fromG_toG {X : Subgroup Γ} (hX : X ≤ L') : τ.fromG (τ.toG X) = X := by
  apply le_antisymm
  · intro h hh
    rw [mem_fromG] at hh
    obtain ⟨g, hL, hg, hs⟩ := hh
    rw [mem_toG] at hg
    obtain ⟨h', hL', hh', hφ⟩ := hg
    rw [← hs]
    have hsub : (⟨g, hL⟩ : ↥L) = τ.φ ⟨h', hL'⟩ := Subtype.ext hφ.symm
    have hsym : τ.φ.symm ⟨g, hL⟩ = ⟨h', hL'⟩ := by rw [hsub]; simp
    rw [hsym]
    exact hh'
  · intro h hh
    rw [mem_fromG]
    refine ⟨(τ.φ ⟨h, hX hh⟩ : ↥L).1, (τ.φ ⟨h, hX hh⟩).2, ?_, ?_⟩
    · rw [mem_toG]
      exact ⟨h, hX hh, hh, rfl⟩
    · simp

theorem toG_mono_iff {X Y : Subgroup Γ} (hX : X ≤ L') (hY : Y ≤ L') :
    τ.toG X ≤ τ.toG Y ↔ X ≤ Y := by
  constructor
  · intro h x hx
    have hx' : ((τ.φ ⟨x, hX hx⟩ : ↥L) : G) ∈ τ.toG Y :=
      h (show ((τ.φ ⟨x, hX hx⟩ : ↥L) : G) ∈ τ.toG X from
        (mem_toG τ).mpr ⟨x, hX hx, hx, rfl⟩)
    obtain ⟨h', hL', hh', hφ⟩ := (mem_toG τ).mp hx'
    have heq : (⟨h', hL'⟩ : ↥L') = ⟨x, hX hx⟩ := τ.φ.injective (Subtype.ext hφ)
    have hx1 : h' = x := congrArg Subtype.val heq
    rwa [hx1] at hh'
  · intro h
    rw [toG_eq_map, toG_eq_map]
    exact Subgroup.map_mono (f := L.subtype.comp τ.φ.toMonoidHom) (Subgroup.comap_mono h)

theorem toG_inj {X Y : Subgroup Γ} (hX : X ≤ L') (hY : Y ≤ L') (h : τ.toG X = τ.toG Y) :
    X = Y := by
  apply le_antisymm
  · exact (τ.toG_mono_iff hX hY).mp (le_of_eq h)
  · exact (τ.toG_mono_iff hY hX).mp (le_of_eq h.symm)

theorem toG_sup {X Y : Subgroup Γ} (hX : X ≤ L') (hY : Y ≤ L') :
    τ.toG (X ⊔ Y) = τ.toG X ⊔ τ.toG Y := by
  rw [toG_eq_map, toG_eq_map, toG_eq_map]
  rw [Subgroup.subgroupOf_sup hX hY, Subgroup.map_sup]

theorem toG_inf {X Y : Subgroup Γ} : τ.toG (X ⊓ Y) = τ.toG X ⊓ τ.toG Y := by
  rw [toG_eq_map, toG_eq_map, toG_eq_map]
  rw [show (X ⊓ Y).subgroupOf L' = X.subgroupOf L' ⊓ Y.subgroupOf L' from
    Subgroup.comap_inf X Y L'.subtype]
  rw [Subgroup.map_inf _ _ _ (injective_toG_hom τ)]

theorem toG_bot : τ.toG ⊥ = ⊥ := by
  have hbot : (⊥ : Subgroup Γ).subgroupOf L' = ⊥ := by
    ext x
    simp [Subgroup.subgroupOf]
  rw [toG_eq_map, hbot, Subgroup.map_bot]

theorem card_toG {X : Subgroup Γ} (hX : X ≤ L') : Nat.card (τ.toG X) = Nat.card X := by
  rw [toG_eq_map, Subgroup.card_map_of_injective (injective_toG_hom τ)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

@[expose] noncomputable def toGEquiv {X : Subgroup Γ} (hX : X ≤ L') : ↥X ≃* ↥(τ.toG X) :=
  (Subgroup.subgroupOfEquivOfLe hX).symm.trans
    ((τ.φ.subgroupMap (X.subgroupOf L')).trans
      (((X.subgroupOf L').map τ.φ.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective))

theorem coe_toGEquiv {X : Subgroup Γ} (hX : X ≤ L') (x : ↥X) :
    ((τ.toGEquiv hX x : ↥(τ.toG X)) : G) = ((τ.φ ⟨x.1, hX x.2⟩ : ↥L) : G) := rfl

private theorem toGEquiv_mem_toG {X E : Subgroup Γ} (hX : X ≤ L') (hE : E ≤ L') (x : ↥X) :
    (τ.toGEquiv hX x).1 ∈ τ.toG E ↔ x.1 ∈ E := by
  rw [coe_toGEquiv]
  rw [mem_toG]
  constructor
  · rintro ⟨h, hL, hh, hφ⟩
    have hinj : (⟨h, hL⟩ : ↥L') = ⟨x.1, hX x.2⟩ :=
      τ.φ.injective (Subtype.ext hφ)
    have hx1 : h = x.1 := congrArg Subtype.val hinj
    exact hx1 ▸ hh
  · intro hx
    exact ⟨x.1, hX x.2, hx, rfl⟩

theorem isMaximalIn_toG {M : Subgroup Γ} (hM : M ≤ L') (h : IsMaximalIn M L') :
    IsMaximalIn (τ.toG M) L := by
  refine ⟨lt_of_le_of_ne (τ.toG_le M) ?_, ?_⟩
  · intro hEq
    have hML' : τ.toG M = τ.toG L' := by rw [hEq, τ.toG_top]
    exact (ne_of_lt h.1) (τ.toG_inj hM le_rfl hML')
  · intro X hMX hXL
    have hMle : M ≤ τ.fromG X :=
      (τ.toG_mono_iff hM (τ.fromG_le X)).mp (by rw [τ.toG_fromG hXL]; exact hMX)
    rcases h.2 (τ.fromG X) hMle (τ.fromG_le X) with hcase | hcase
    · left; rw [← τ.toG_fromG hXL, hcase]
    · right; rw [← τ.toG_fromG hXL, hcase, τ.toG_top]

theorem isMaximalIn_fromG {X : Subgroup G} (h : IsMaximalIn X L) :
    IsMaximalIn (τ.fromG X) L' := by
  have hXL : X ≤ L := le_of_lt h.1
  refine ⟨lt_of_le_of_ne (τ.fromG_le X) ?_, ?_⟩
  · intro hEq
    have hXL' : τ.toG (τ.fromG X) = τ.toG L' := by rw [hEq, τ.toG_top]
    rw [τ.toG_fromG hXL, τ.toG_top] at hXL'
    exact (ne_of_lt h.1) hXL'
  · intro Y hXY hYL'
    have hle : X ≤ τ.toG Y := by
      rw [← τ.toG_fromG hXL]
      exact (τ.toG_mono_iff (τ.fromG_le X) hYL').mpr hXY
    rcases h.2 (τ.toG Y) hle (τ.toG_le Y) with hcase | hcase
    · left; rw [← τ.fromG_toG hYL', hcase]
    · right; rw [← τ.fromG_toG hYL', hcase, τ.fromG_top]

theorem isIntDirect_toG {N X Z : Subgroup Γ} (hN : N ≤ L') (hX : X ≤ L') (hZ : Z ≤ L')
    (h : IsIntDirect N X Z) : IsIntDirect (τ.toG N) (τ.toG X) (τ.toG Z) := by
  refine ⟨(τ.toG_mono_iff hX hN).mpr h.1, (τ.toG_mono_iff hZ hN).mpr h.2.1, ?_, ?_, ?_⟩
  · rintro x hx z hz
    rw [mem_toG] at hx hz
    obtain ⟨a, aL, ha, rfl⟩ := hx
    obtain ⟨b, bL, hb, rfl⟩ := hz
    have hcomm : (τ.φ ⟨a, aL⟩ : ↥L) * τ.φ ⟨b, bL⟩ = τ.φ ⟨b, bL⟩ * τ.φ ⟨a, aL⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (h.2.2.1 a ha b hb)
    exact congrArg Subtype.val hcomm
  · rw [← τ.toG_inf, h.2.2.2.1, τ.toG_bot]
  · rw [← τ.toG_sup hX hZ, h.2.2.2.2]

theorem center_toG :
    (Subgroup.center ↥L).map L.subtype = τ.toG ((Subgroup.center ↥L').map L'.subtype) := by
  rw [toG_eq_map, center_subgroupOf, ← Subgroup.map_map, map_center_mulEquiv τ.φ]

theorem pCoreOf_toG (p : ℕ) {M : Subgroup Γ} (hM : M ≤ L') :
    pCoreOf p (τ.toG M) = τ.toG (pCoreOf p M) := by
  have hψ : Function.Injective (L.subtype.comp τ.φ.toMonoidHom) :=
    injective_toG_hom τ
  have hMsub : M = (M.subgroupOf L').map L'.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM]
  have h1 : pCoreOf p M = (pCoreOf p (M.subgroupOf L')).map L'.subtype := by
    conv_lhs => rw [hMsub]
    exact pCoreOf_map_injective p L'.subtype L'.subtype_injective (M.subgroupOf L')
  have h2 : (pCoreOf p M).subgroupOf L' = pCoreOf p (M.subgroupOf L') := by
    rw [h1]
    exact Subgroup.comap_map_eq_self (f := L'.subtype)
      (by rw [Subgroup.ker_subtype]; exact bot_le)
  rw [toG_eq_map, toG_eq_map, pCoreOf_map_injective p _ hψ, h2]

theorem isElemAbelian_toG {p : ℕ} {E : Subgroup Γ} (hE : E ≤ L') (h : IsElemAbelian p E) :
    IsElemAbelian p (τ.toG E) := by
  rw [toG_eq_map]
  exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf h L') _

theorem isExtOf_toG {X E : Subgroup Γ} (hX : X ≤ L') {Q : Type*} [Group Q]
    (h : IsExtOf X E Q) : IsExtOf (τ.toG X) (τ.toG E) Q := by
  obtain ⟨hEX, f, hf, hker⟩ := h
  have hE : E ≤ L' := le_trans hEX hX
  refine ⟨(τ.toG_mono_iff hE hX).mpr hEX, f.comp (τ.toGEquiv hX).symm.toMonoidHom,
    hf.comp (τ.toGEquiv hX).symm.surjective, ?_⟩
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hmem := τ.toGEquiv_mem_toG hX hE ((τ.toGEquiv hX).symm y)
  simpa using hmem.symm

theorem isExtHatOf_toG {X E : Subgroup Γ} (hX : X ≤ L') {S : Type} [Group S]
    (h : IsExtHatOf X E S) : IsExtHatOf (τ.toG X) (τ.toG E) S := by
  obtain ⟨hEX, Q, hQ, f, hf, hker, hHat⟩ := h
  letI : Group Q := hQ
  have hE : E ≤ L' := le_trans hEX hX
  refine ⟨(τ.toG_mono_iff hE hX).mpr hEX, Q, hQ, f.comp (τ.toGEquiv hX).symm.toMonoidHom,
    hf.comp (τ.toGEquiv hX).symm.surjective, ?_, hHat⟩
  ext y
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  have hmem := τ.toGEquiv_mem_toG hX hE ((τ.toGEquiv hX).symm y)
  simpa using hmem.symm

theorem isSylowIn_toG {p : ℕ} {P H : Subgroup Γ} (hP : P ≤ L') (hH : H ≤ L') :
    IsSylowIn p P H ↔ IsSylowIn p (τ.toG P) (τ.toG H) := by
  have hrel : (τ.toG P).relIndex (τ.toG H) = P.relIndex H := by
    have hψ : Function.Injective (L.subtype.comp τ.φ.toMonoidHom) :=
      injective_toG_hom τ
    have hPsub : (P.subgroupOf L').map L'.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hP]
    have hHsub : (H.subgroupOf L').map L'.subtype = H := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH]
    rw [toG_eq_map, toG_eq_map]
    rw [Subgroup.relIndex_map_map_of_injective
        (f := L.subtype.comp τ.φ.toMonoidHom) (P.subgroupOf L') (H.subgroupOf L') hψ,
      ← Subgroup.relIndex_map_map_of_injective
        (f := L'.subtype) (P.subgroupOf L') (H.subgroupOf L') L'.subtype_injective,
      hPsub, hHsub]
  constructor
  · intro h
    exact ⟨(τ.toG_mono_iff hP hH).mpr h.1,
      IsPGroup.of_equiv h.2.1 (τ.toGEquiv hP), by rw [hrel]; exact h.2.2⟩
  · intro h
    exact ⟨(τ.toG_mono_iff hP hH).mp h.1,
      IsPGroup.of_equiv h.2.1 (τ.toGEquiv hP).symm, by rw [← hrel]; exact h.2.2⟩

end Trans

end CFSG.Quasithin.AppendixH.H12
