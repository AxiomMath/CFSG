module

public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace A312

noncomputable def modO2Equiv {G H : Type} [Group G] [Group H] {B : Subgroup G} {C : Subgroup H}
    (e : ↥B ≃* ↥C) : ModO2 B ≃* ModO2 C :=
  QuotientGroup.congr _ _ e (CFSG.pCore_map_iso 2 e)

theorem card_pCore_eq {G H : Type} [Group G] [Group H] {B : Subgroup G} {C : Subgroup H}
    (e : ↥B ≃* ↥C) : Nat.card (CFSG.pCore 2 ↥C) = Nat.card (CFSG.pCore 2 ↥B) := by
  rw [← CFSG.pCore_map_iso 2 e, Subgroup.card_map_of_injective e.injective]

variable {X Y : Type} [Group X] [Group Y]

theorem isExt_of_mulEquiv {PV PY : ∀ (V : Type) [Group V], Prop}
    (hV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (e : X ≃* Y) (h : IsExt X PV PY) : IsExt Y PV PY := by
  obtain ⟨V, hVn, hpv, hpy⟩ := h
  have hVn' : (V.map (e : X →* Y)).Normal := Subgroup.Normal.map hVn _ e.surjective
  exact ⟨V.map (e : X →* Y), hVn', hV _ _ (V.equivMapOfInjective _ e.injective) hpv,
    hY _ _ (QuotientGroup.congr V (V.map (e : X →* Y)) e rfl) hpy⟩

variable {G : Type} [Group G]

theorem mem_normalizer_map_subtype_iff (L : Subgroup G) (S : Subgroup ↥L) (g : ↥L) :
    g ∈ Subgroup.normalizer (S : Set ↥L) ↔
      (g : G) ∈ Subgroup.normalizer ((S.map L.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact ⟨g * h * g⁻¹, (hg h).mp hh, rfl⟩
    · rintro ⟨k, hk, hkx⟩
      have hkx' : (k : G) = (g : G) * x * (g : G)⁻¹ := hkx
      have hxL : x ∈ L := by
        have : x = (g : G)⁻¹ * (k : G) * g := by rw [hkx']; group
        rw [this]
        exact L.mul_mem (L.mul_mem (L.inv_mem g.2) k.2) g.2
      refine ⟨⟨x, hxL⟩, ?_, rfl⟩
      refine (hg ⟨x, hxL⟩).mpr ?_
      have : g * ⟨x, hxL⟩ * g⁻¹ = k := Subtype.ext (by simp [hkx'])
      rw [this]
      exact hk
  · intro hg h
    have h1 := hg (h : G)
    constructor
    · intro hh
      obtain ⟨k, hk, hkx⟩ := h1.mp ⟨h, hh, rfl⟩
      have : k = g * h * g⁻¹ := Subtype.ext (by simpa using hkx)
      rw [← this]
      exact hk
    · intro hh
      obtain ⟨k, hk, hkx⟩ := h1.mpr ⟨g * h * g⁻¹, hh, rfl⟩
      have : k = h := Subtype.ext hkx
      rw [← this]
      exact hk

theorem isSylowTwoOf_top_iff_map (L : Subgroup G) (S : Subgroup ↥L) :
    IsSylowTwoOf S (⊤ : Subgroup ↥L) ↔ IsSylowTwoOf (S.map L.subtype) L := by
  have h1 : (S.map L.subtype).subgroupOf L = S := A4.subgroupOf_map_subtype' L S
  have h2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  let eS : ↥S ≃* ↥(S.map L.subtype) := S.equivMapOfInjective L.subtype L.subtype_injective
  constructor
  · rintro ⟨-, hp, hi⟩
    exact ⟨Subgroup.map_subtype_le _, hp.of_equiv eS, by rw [h1]; rwa [h2] at hi⟩
  · rintro ⟨-, hp, hi⟩
    exact ⟨le_top, hp.of_equiv eS.symm, by rw [h2]; rwa [h1] at hi⟩

theorem isParabolic2_top_iff (L : Subgroup G) (P : Subgroup ↥L) :
    IsParabolic2 (⊤ : Subgroup ↥L) P ↔ IsParabolic2 L (P.map L.subtype) := by
  constructor
  · rintro ⟨-, S, hS, hN⟩
    refine ⟨Subgroup.map_subtype_le _, S.map L.subtype, (isSylowTwoOf_top_iff_map L S).mp hS, ?_⟩
    intro g hg
    obtain ⟨hgL, hgN⟩ := hg
    have h1 : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.normalizer (S : Set ↥L) :=
      (mem_normalizer_map_subtype_iff L S ⟨g, hgL⟩).mpr hgN
    exact ⟨⟨g, hgL⟩, hN ⟨trivial, h1⟩, rfl⟩
  · rintro ⟨-, S, hS, hN⟩
    have hmap : (S.subgroupOf L).map L.subtype = S := Subgroup.map_subgroupOf_eq_of_le hS.1
    refine ⟨le_top, S.subgroupOf L, ?_, ?_⟩
    · rw [isSylowTwoOf_top_iff_map, hmap]
      exact hS
    · intro g hg
      have hgN : (g : G) ∈ Subgroup.normalizer ((S.subgroupOf L).map L.subtype : Set G) :=
        (mem_normalizer_map_subtype_iff L (S.subgroupOf L) g).mp hg.2
      rw [hmap] at hgN
      obtain ⟨p, hp, hpg⟩ := hN ⟨g.2, hgN⟩
      have : p = g := Subtype.ext hpg
      rw [← this]
      exact hp

theorem isMaxParabolic2_top_map (L : Subgroup G) (P : Subgroup ↥L)
    (h : IsMaxParabolic2 (⊤ : Subgroup ↥L) P) : IsMaxParabolic2 L (P.map L.subtype) := by
  obtain ⟨hpar, hne, hmax⟩ := h
  refine ⟨(isParabolic2_top_iff L P).mp hpar, ?_, ?_⟩
  · intro hPL
    apply hne
    have := congrArg (fun K : Subgroup G => K.subgroupOf L) hPL
    simpa [A4.subgroupOf_map_subtype', Subgroup.subgroupOf_self] using this
  · intro Q hQ hQL hPQ
    have hQL' : Q ≤ L := hQ.1
    have hQ' : IsParabolic2 (⊤ : Subgroup ↥L) (Q.subgroupOf L) := by
      rw [isParabolic2_top_iff, Subgroup.map_subgroupOf_eq_of_le hQL']
      exact hQ
    have hne' : Q.subgroupOf L ≠ ⊤ := by
      intro htop
      apply hQL
      have := congrArg (Subgroup.map L.subtype) htop
      rw [Subgroup.map_subgroupOf_eq_of_le hQL', Subgroup.map_top, Subgroup.range_subtype] at this
      exact this
    have hPQ' : P ≤ Q.subgroupOf L := Subgroup.map_le_iff_le_comap.mp hPQ
    have := hmax _ hQ' hne' hPQ'
    rw [← Subgroup.map_subgroupOf_eq_of_le hQL', this]

end A312

section Generic

variable {G H : Type} [Group G] [Group H] {B L : Subgroup G} {B₂ L₂ : Subgroup H}

theorem A312C6.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C6 B L) : A312C6 B₂ L₂ := by
  obtain ⟨hB, hL⟩ := h
  refine ⟨?_, ?_⟩
  · rcases hB with h | h
    · exact Or.inl (IsAlt.of_mulEquiv eB h)
    · exact Or.inr (IsPSL.of_mulEquiv eB h)
  · rcases hL with h | h
    · exact Or.inl (IsAlt.of_mulEquiv eL h)
    · exact Or.inr (IsHat.of_mulEquiv eL h)

theorem A312C7.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C7 B L) : A312C7 B₂ L₂ := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨IsAlt.of_mulEquiv eB h1, IsAlt.of_mulEquiv eL h2⟩
  · exact Or.inr ⟨IsHat.of_mulEquiv eB h1, IsHat.of_mulEquiv eL h2⟩

theorem A312C8.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C8 B L) : A312C8 B₂ L₂ := by
  rcases h with ⟨p, hp, hp3, h1, h2⟩ | ⟨h1, p, hp, h2, h3, h4⟩
  · exact Or.inl ⟨p, hp, hp3, IsPSL.of_mulEquiv eB h1, IsPSL.of_mulEquiv eL h2⟩
  · exact Or.inr ⟨IsAlt.of_mulEquiv eB h1, p, hp, IsPSL.of_mulEquiv eL h2, h3, h4⟩

theorem A312C9.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C9 B L) : A312C9 B₂ L₂ := by
  rcases h with ⟨s, p, hp, hp3, h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨s, p, hp, hp3, IsSL2.of_mulEquiv eB h1, ?_⟩
    rcases h2 with h2 | h2
    · exact Or.inl (IsPSLEps3.of_mulEquiv eL h2)
    · exact Or.inr (IsSLEps3.of_mulEquiv eL h2)
  · exact Or.inr (Or.inl ⟨IsAlt.of_mulEquiv eB h1, IsPSU.of_mulEquiv eL h2⟩)
  · exact Or.inr (Or.inr ⟨IsHat.of_mulEquiv eB h1, IsSU3.of_mulEquiv eL h2⟩)

theorem A312C10.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C10 B L) :
    A312C10 B₂ L₂ := by
  obtain ⟨p, hp, hp3, h1, h2⟩ := h
  refine ⟨p, hp, hp3, A312.isExt_of_mulEquiv
    (fun _ _ _ _ e h => IsElemAbelianOfRank.of_mulEquiv e h)
    (fun _ _ _ _ e h => IsSL2.of_mulEquiv e h) eB h1, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inl (IsPSL.of_mulEquiv eL h2)
  · exact Or.inr (IsSL3.of_mulEquiv eL h2)

theorem A312C11.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C11 B L) :
    A312C11 B₂ L₂ :=
  ⟨IsAlt.of_mulEquiv eB h.1, IsSporadic.of_mulEquiv eL h.2⟩

theorem A312C12.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C12 B L) :
    A312C12 B₂ L₂ := by
  have hE4 : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsE2 4 V → IsE2 4 W :=
    fun V W _ _ e h => IsE2.of_mulEquiv e h
  have hA5 : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsAlt 5 V → IsAlt 5 W :=
    fun V W _ _ e h => IsAlt.of_mulEquiv e h
  have hA6 : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsAlt 6 V → IsAlt 6 W :=
    fun V W _ _ e h => IsAlt.of_mulEquiv e h
  have hH6 : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) →
      IsHat V (alternatingGroup (Fin 6)) → IsHat W (alternatingGroup (Fin 6)) :=
    fun V W _ _ e h => IsHat.of_mulEquiv e h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨?_, IsSporadic.of_mulEquiv eL h2⟩
    rcases h1 with h1 | h1
    · exact Or.inl (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsE2.of_mulEquiv e h) hA5 eB h1)
    · exact Or.inr (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsE2.of_mulEquiv e h) hA6 eB h1)
  · refine Or.inr ⟨?_, IsHat.of_mulEquiv eL h2⟩
    rcases h1 with h1 | h1
    · exact Or.inl (A312.isExt_of_mulEquiv hE4 hA5 eB h1)
    · exact Or.inr (A312.isExt_of_mulEquiv hE4 hH6 eB h1)

theorem A312C13.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C13 B L) :
    A312C13 B₂ L₂ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, IsSporadic.of_mulEquiv eL h2⟩
  have hE : ∀ n, ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsE2 n V → IsE2 n W :=
    fun n V W _ _ e h => IsE2.of_mulEquiv e h
  have hA : ∀ n, ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsAlt n V → IsAlt n W :=
    fun n V W _ _ e h => IsAlt.of_mulEquiv e h
  have hP : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsPSL 3 2 1 V → IsPSL 3 2 1 W :=
    fun V W _ _ e h => IsPSL.of_mulEquiv e h
  rcases h1 with h | h | h | h | h | h | h
  · exact Or.inl (IsSporadic.of_mulEquiv eB h)
  · exact Or.inr (Or.inl (IsPSL.of_mulEquiv eB h))
  · exact Or.inr (Or.inr (Or.inl (A312.isExt_of_mulEquiv (hE 4) (hA 7) eB h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (A312.isExt_of_mulEquiv (hE 4) hP eB h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (A312.isExt_of_mulEquiv (hE 3) hP eB h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (A312.isExt_of_mulEquiv (hE 4) (hA 6) eB h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (A312.isExt_of_mulEquiv (hE 4) (hA 5) eB h))))))

theorem A312C14.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C14 B L) :
    A312C14 B₂ L₂ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, IsSporadic.of_mulEquiv eL h2⟩
  have hE : ∀ n, ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsE2 n V → IsE2 n W :=
    fun n V W _ _ e h => IsE2.of_mulEquiv e h
  have hP : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsPSL 3 2 1 V → IsPSL 3 2 1 W :=
    fun V W _ _ e h => IsPSL.of_mulEquiv e h
  have hP4 : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsPSL 4 2 1 V → IsPSL 4 2 1 W :=
    fun V W _ _ e h => IsPSL.of_mulEquiv e h
  have hX : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → IsExtraspecial2 3 V →
      IsExtraspecial2 3 W := fun V W _ _ e h => IsExtraspecial2.of_mulEquiv e h
  have hH : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) →
      IsHat V (alternatingGroup (Fin 6)) → IsHat W (alternatingGroup (Fin 6)) :=
    fun V W _ _ e h => IsHat.of_mulEquiv e h
  rcases h1 with h | h | h | h
  · exact Or.inl (A312.isExt_of_mulEquiv (hE 4) hP4 eB h)
  · exact Or.inr (Or.inl (A312.isExt_of_mulEquiv (hE 6) hP eB h))
  · exact Or.inr (Or.inr (Or.inl (A312.isExt_of_mulEquiv hX hP eB h)))
  · exact Or.inr (Or.inr (Or.inr (A312.isExt_of_mulEquiv (hE 6) hH eB h)))

theorem A312C15.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C15 B L) :
    A312C15 B₂ L₂ :=
  ⟨IsAlt.of_mulEquiv eB h.1, IsSporadic.of_mulEquiv eL h.2⟩

theorem A312C16.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C16 B L) :
    A312C16 B₂ L₂ :=
  ⟨A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsExtraspecial2.of_mulEquiv e h)
    (fun _ _ _ _ e h => IsAlt.of_mulEquiv e h) eB h.1, IsSporadic.of_mulEquiv eL h.2⟩

theorem A312C17.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C17 B L) :
    A312C17 B₂ L₂ := by
  obtain ⟨h2, h1⟩ := h
  refine ⟨IsSporadic.of_mulEquiv eL h2, ?_⟩
  let eM := A312.modO2Equiv eB
  rcases h1 with h | h | h | h | h | h
  · exact Or.inl (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsExtraspecial2.of_mulEquiv e h)
      (fun _ _ _ _ e h => IsHat.of_mulEquiv e h) eB h)
  · exact Or.inr (Or.inl (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsE2.of_mulEquiv e h)
      (fun _ _ _ _ e h => IsSporadic.of_mulEquiv e h) eB h))
  · exact Or.inr (Or.inr (Or.inl (IsAlt.of_mulEquiv eM h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsHat.of_mulEquiv eM h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsPSL.of_mulEquiv eM h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsPSL.of_mulEquiv eM h)))))

theorem A312C18.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C18 B L) :
    A312C18 B₂ L₂ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, IsSporadic.of_mulEquiv eL h2⟩
  rcases h1 with h | h
  · exact Or.inl (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsZ4StarExtra2.of_mulEquiv e h)
      (fun _ _ _ _ e h => IsAlt.of_mulEquiv e h) eB h)
  · exact Or.inr (A312.isExt_of_mulEquiv
      (fun _ _ _ _ e h => h.elim fun f => ⟨e.symm.trans f⟩)
      (fun _ _ _ _ e h => IsPSL.of_mulEquiv e h) eB h)

theorem A312C19.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C19 B L) :
    A312C19 B₂ L₂ := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, IsSporadic.of_mulEquiv eL h2⟩
  rcases h1 with h | h
  · exact Or.inl (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsExtraspecial2.of_mulEquiv e h)
      (fun _ _ _ _ e h => IsPSL.of_mulEquiv e h) eB h)
  · exact Or.inr (A312.isExt_of_mulEquiv (fun _ _ _ _ e h => IsE2.of_mulEquiv e h)
      (fun _ _ _ _ e h => IsHat.of_mulEquiv e h) eB h)

theorem A312C20.of_equiv (eB : ↥B ≃* ↥B₂) (eL : ↥L ≃* ↥L₂) (h : A312C20 B L) :
    A312C20 B₂ L₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  let eM := A312.modO2Equiv eB
  refine ⟨?_, by rw [A312.card_pCore_eq eB, h2], IsSporadic.of_mulEquiv eL h3⟩
  rcases h1 with h | h
  · exact Or.inl (IsAlt.of_mulEquiv eM h)
  · exact Or.inr (IsPSL.of_mulEquiv eM h)

theorem IsRank2LieChar2.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsRank2LieChar2 X) : IsRank2LieChar2 Y := by
  rcases h with ⟨f, h⟩ | h
  · refine Or.inl ⟨f, ?_⟩
    rcases h with ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h2, h⟩
    · exact Or.inl ⟨h1, IsPSL.of_mulEquiv e h⟩
    · exact Or.inr (Or.inl ⟨h1, IsSL3.of_mulEquiv e h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, IsPSp4.of_mulEquiv e h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, IsG2.of_mulEquiv e h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, Is3D4.of_mulEquiv e h⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, Is2F4.of_mulEquiv e h⟩))))
  · exact Or.inr (IsTits.of_mulEquiv e h)

end Generic

section Parabolic

variable {G : Type} [Group G] [Finite G] {B L : Subgroup G}

noncomputable def subgroupOfEquiv (hBL : B ≤ L) : ↥(B.subgroupOf L) ≃* ↥B :=
  Subgroup.subgroupOfEquivOfLe hBL

theorem eq_perfectCore_map {P : Subgroup ↥L} (hBL : B ≤ L)
    (h : B.subgroupOf L = perfectCore P) : B = perfectCore (P.map L.subtype) := by
  rw [← map_perfectCore, ← h, Subgroup.map_subgroupOf_eq_of_le hBL]

theorem A312C2.of_subgroupOf (hBL : B ≤ L) (h : A312C2 (B.subgroupOf L) (⊤ : Subgroup ↥L)) :
    A312C2 B L := by
  obtain ⟨⟨n, hn⟩, hX, P, hP, hBP⟩ := h
  exact ⟨⟨n, IsPSL.of_mulEquiv (A312.modO2Equiv (subgroupOfEquiv hBL)) hn⟩,
    IsRank2LieChar2.of_mulEquiv Subgroup.topEquiv hX, P.map L.subtype,
    A312.isMaxParabolic2_top_map L P hP, eq_perfectCore_map hBL hBP⟩

theorem A312C3.of_subgroupOf (hBL : B ≤ L) (h : A312C3 (B.subgroupOf L) (⊤ : Subgroup ↥L)) :
    A312C3 B L := by
  obtain ⟨f, h1, h2, P, hP, hBP⟩ := h
  exact ⟨f, IsSz.of_mulEquiv (A312.modO2Equiv (subgroupOfEquiv hBL)) h1,
    Is2F4.of_mulEquiv Subgroup.topEquiv h2, P.map L.subtype,
    (A312.isParabolic2_top_iff L P).mp hP, eq_perfectCore_map hBL hBP⟩

theorem A312C4.of_subgroupOf (hBL : B ≤ L) (h : A312C4 (B.subgroupOf L) (⊤ : Subgroup ↥L)) :
    A312C4 B L := by
  obtain ⟨h1, h2, P, hP, hBP⟩ := h
  refine ⟨IsPSL.of_mulEquiv (A312.modO2Equiv (subgroupOfEquiv hBL)) h1, ?_, P.map L.subtype,
    (A312.isParabolic2_top_iff L P).mp hP, eq_perfectCore_map hBL hBP⟩
  rcases h2 with h2 | h2
  · exact Or.inl (IsPSL.of_mulEquiv Subgroup.topEquiv h2)
  · exact Or.inr (IsPSL.of_mulEquiv Subgroup.topEquiv h2)

theorem A312C5.of_subgroupOf (hBL : B ≤ L) (h : A312C5 (B.subgroupOf L) (⊤ : Subgroup ↥L)) :
    A312C5 B L := by
  obtain ⟨h1, h2, P, hP, hBP⟩ := h
  exact ⟨IsPSL.of_mulEquiv (A312.modO2Equiv (subgroupOfEquiv hBL)) h1,
    IsPSL.of_mulEquiv Subgroup.topEquiv h2, P.map L.subtype,
    (A312.isParabolic2_top_iff L P).mp hP, eq_perfectCore_map hBL hBP⟩

theorem A312Case.of_subgroupOf (hBL : B ≤ L) (h : A312Case (B.subgroupOf L) (⊤ : Subgroup ↥L)) :
    A312Case B L := by
  have eB := subgroupOfEquiv hBL
  have eL : ↥(⊤ : Subgroup ↥L) ≃* ↥L := Subgroup.topEquiv
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · left
    exact A312C2.of_subgroupOf hBL h
  · right
    left
    exact A312C3.of_subgroupOf hBL h
  · iterate 2 right
    left
    exact A312C4.of_subgroupOf hBL h
  · iterate 3 right
    left
    exact A312C5.of_subgroupOf hBL h
  · iterate 4 right
    left
    exact A312C6.of_equiv eB eL h
  · iterate 5 right
    left
    exact A312C7.of_equiv eB eL h
  · iterate 6 right
    left
    exact A312C8.of_equiv eB eL h
  · iterate 7 right
    left
    exact A312C9.of_equiv eB eL h
  · iterate 8 right
    left
    exact A312C10.of_equiv eB eL h
  · iterate 9 right
    left
    exact A312C11.of_equiv eB eL h
  · iterate 10 right
    left
    exact A312C12.of_equiv eB eL h
  · iterate 11 right
    left
    exact A312C13.of_equiv eB eL h
  · iterate 12 right
    left
    exact A312C14.of_equiv eB eL h
  · iterate 13 right
    left
    exact A312C15.of_equiv eB eL h
  · iterate 14 right
    left
    exact A312C16.of_equiv eB eL h
  · iterate 15 right
    left
    exact A312C17.of_equiv eB eL h
  · iterate 16 right
    left
    exact A312C18.of_equiv eB eL h
  · iterate 17 right
    left
    exact A312C19.of_equiv eB eL h
  · iterate 18 right
    exact A312C20.of_equiv eB eL h

end Parabolic

end CFSG.Quasithin
