module

public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4Defs

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace NoJ4

variable {A B : Type*} [Group A] [Group B]

theorem blockQ_map (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    (blockQ X).map f = blockQ (X.map f) := by
  have h := CFSG.pCore_map_iso 2 (X.equivMapOfInjective f hf)
  simp only [blockQ, CFSG.Open.pCoreOf]
  rw [← h, Subgroup.map_map, Subgroup.map_map]
  rfl

theorem blockU_map (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    (blockU X).map f = blockU (X.map f) := by
  rw [blockU, blockU, Subgroup.map_commutator, blockQ_map f hf]

theorem blockZ_map (f : A →* B) (hf : Function.Injective f) (X : Subgroup A) :
    (blockZ X).map f = blockZ (X.map f) := by
  apply le_antisymm
  · rw [blockZ, blockZ, ← blockU_map f hf]
    refine (Subgroup.map_inf_le _ _ f).trans (inf_le_inf_left _ ?_)
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, ← map_mul, hx k hk]
  · intro y hy
    obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
    rw [← blockU_map f hf] at hyU
    obtain ⟨u, hu, rfl⟩ := hyU
    refine ⟨u, Subgroup.mem_inf.mpr ⟨hu, ?_⟩, rfl⟩
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro l hl
    apply hf
    rw [map_mul, map_mul]
    exact hyC (f l) ⟨l, hl, rfl⟩

theorem mem_centralizer_map_iff (f : A →* B) (hf : Function.Injective f) {P : Subgroup A}
    {a : A} : f a ∈ Subgroup.centralizer ((P.map f : Subgroup B) : Set B) ↔
      a ∈ Subgroup.centralizer (P : Set A) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro h p hp
    exact hf (by rw [map_mul, map_mul]; exact h (f p) ⟨p, hp, rfl⟩)
  · rintro h _ ⟨p, hp, rfl⟩
    rw [← map_mul, ← map_mul, h p hp]

theorem isShort2_of_map [Finite A] (f : A →* B) (hf : Function.Injective f) {X : Subgroup A}
    (h : IsShort2 (X.map f)) : IsShort2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf with he
  obtain ⟨h1, h2, ⟨h3, h3'⟩, h4, ⟨h5, h5'⟩⟩ := h
  have hQ := blockQ_map f hf X
  have hU := blockU_map f hf X
  have hZ := blockZ_map f hf X
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  ·
    intro N hN hp
    have hN' : (N.map e.toMonoidHom).Normal := hN.map _ e.surjective
    have hq : (↥X ⧸ N) ≃* (↥(X.map f) ⧸ N.map e.toMonoidHom) :=
      QuotientGroup.congr N (N.map e.toMonoidHom) e rfl
    have := h1 (N.map e.toMonoidHom) (hp.of_equiv hq)
    have hc := congrArg (Subgroup.comap e.toMonoidHom) this
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at hc
  ·
    rintro a ⟨haX, haC⟩
    have hfa : f a ∈ X.map f ⊓ Subgroup.centralizer (pCoreOf 2 (X.map f) : Set B) := by
      refine ⟨⟨a, haX, rfl⟩, ?_⟩
      have hQ' : pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := hQ.symm
      rw [hQ']
      exact (mem_centralizer_map_iff f hf).mpr haC
    have h' := h2 hfa
    have hQ' : pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := hQ.symm
    rw [hQ'] at h'
    exact (Subgroup.mem_map_iff_mem hf).mp h'
  ·
    intro u hu
    have hfu : f u ∈ blockU (X.map f) := hU ▸ ⟨u, hu, rfl⟩
    obtain ⟨hq, hc⟩ := Subgroup.mem_inf.mp (h3 hfu)
    rw [← hQ] at hq hc
    exact ⟨(Subgroup.mem_map_iff_mem hf).mp hq, (mem_centralizer_map_iff f hf).mp hc⟩
  ·
    intro u hu
    have hfu : f u ∈ blockU (X.map f) := hU ▸ ⟨u, hu, rfl⟩
    apply hf
    rw [map_pow, h3' _ hfu, map_one]
  ·
    have hp : (CFSG.pCore 2 ↥X).map e.toMonoidHom = CFSG.pCore 2 ↥(X.map f) :=
      CFSG.pCore_map_iso 2 e
    have hq : (↥X ⧸ CFSG.pCore 2 ↥X) ≃* (↥(X.map f) ⧸ CFSG.pCore 2 ↥(X.map f)) :=
      QuotientGroup.congr _ _ e hp
    rcases h4 with hqs | h3c
    · exact Or.inl (CFSG.LocalCores.isQuasisimple_of_mulEquiv hq.symm hqs)
    · exact Or.inr ((Nat.card_congr hq.toEquiv).trans h3c)
  ·
    rw [← hZ, ← hU] at h5
    exact (Subgroup.map_lt_map_iff_of_injective hf).mp h5
  ·
    intro W hZW hWU hXW
    have hZW' : blockZ (X.map f) ≤ W.map f := hZ ▸ Subgroup.map_mono hZW
    have hWU' : W.map f ≤ blockU (X.map f) := hU ▸ Subgroup.map_mono hWU
    have hXW' : X.map f ≤ Subgroup.normalizer ((W.map f : Subgroup B) : Set B) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro b
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨x * w * x⁻¹, (Subgroup.mem_normalizer_iff.mp (hXW hx) w).mp hw, ?_⟩
        simp only [map_mul, map_inv]
      · intro hb
        obtain ⟨w, hw, hwe⟩ := hb
        refine ⟨x⁻¹ * w * x, ?_, ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hXW (X.inv_mem hx)) w).mp hw
          simpa using this
        · rw [map_mul, map_mul, map_inv, hwe]
          group
    rcases h5' (W.map f) hZW' hWU' hXW' with hW | hW
    · left
      rw [← hZ] at hW
      exact Subgroup.map_injective hf hW
    · right
      rw [← hU] at hW
      exact Subgroup.map_injective hf hW

theorem isExt_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {PV PY : ∀ (V : Type) [Group V], Prop}
    (hPV : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PV V → PV W)
    (hPY : ∀ (V W : Type) [Group V] [Group W], (V ≃* W) → PY V → PY W)
    (h : IsExt Y PV PY) : IsExt X PV PY := by
  obtain ⟨V, hV, hPVV, hPYV⟩ := h
  have hmap : (V.comap e.toMonoidHom).map e.toMonoidHom = V :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective V
  refine ⟨V.comap e.toMonoidHom, hV.comap _, ?_, ?_⟩
  · exact hPV _ _ (((V.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom
      e.injective).trans (MulEquiv.subgroupCongr hmap)).symm hPVV
  · exact hPY _ _ (QuotientGroup.congr (V.comap e.toMonoidHom) V e hmap).symm hPYV

theorem isE2_of_mulEquiv (n : ℕ) (V W : Type) [Group V] [Group W] (e : V ≃* W)
    (h : IsE2 n V) : IsE2 n W := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

theorem isSporadic_of_mulEquiv (s : TauCeti.SporadicName) (V W : Type) [Group V] [Group W]
    (e : V ≃* W) (h : IsSporadic s V) : IsSporadic s W := by
  obtain ⟨e'⟩ := h
  exact ⟨e.symm.trans e'⟩

theorem isPSL_of_mulEquiv (n p f : ℕ) (V W : Type) [Group V] [Group W] (e : V ≃* W)
    (h : IsPSL n p f V) : IsPSL n p f W := by
  obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hadm, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem center_map_mulEquiv {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) :
    (Subgroup.center P).map e.toMonoidHom = Subgroup.center Q := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Subgroup.mem_center_iff] at hp ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hp x]
  · intro hq
    refine ⟨e.symm q, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hq ⊢
    intro x
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hq (e x)]

theorem perfectCore_map (f : A →* B) (hf : Function.Injective f) (H : Subgroup A) :
    (perfectCore H).map f = perfectCore (H.map f) := by
  rw [perfectCore, perfectCore, Subgroup.map_iInf f hf]
  exact iInf_congr fun n => map_derivedSeriesOf f H n

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem blockFacts (hBlk : J4BlockFacts) {K B : Subgroup G} (hK : IsSporadic .J4 ↥K)
    (hBK : B ≤ K) (hS : IsShort2 B)
    (hE : IsExt ↥B (fun N _ => IsE2 11 N) (fun Y _ => IsSporadic .M24 Y) ∨
      IsExt ↥B (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y)) :
    K ⊓ Subgroup.normalizer (B : Set G) = B ∧
      K ⊓ Subgroup.centralizer (pCoreOf 2 B : Set G) = pCoreOf 2 B ∧
      (∀ W : Subgroup G, W ≤ pCoreOf 2 B → B ≤ Subgroup.normalizer (W : Set G) →
        W = ⊥ ∨ W = pCoreOf 2 B) ∧
      ∃ x ∈ B, orderOf x = 3 ∧ pCoreOf 2 B ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
        CFSG.IsQuasisimple ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G))) ∧
        Nat.card ↥(Subgroup.center ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)))) = 6 ∧
        IsSporadic .M22 (↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G))) ⧸
          Subgroup.center ↥(perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)))) ∧
        ¬ pCoreOf 2 B ⊓ Subgroup.centralizer ({x} : Set G) ≤
          Subgroup.centralizer (perfectCore (K ⊓ Subgroup.centralizer ({x} : Set G)) : Set G) := by
  classical
  set f : ↥K →* G := K.subtype with hfdef
  have hf : Function.Injective f := K.subtype_injective
  set X : Subgroup ↥K := B.subgroupOf K with hXdef
  have hXB : X.map f = B := by rw [hXdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK]
  have hS' : IsShort2 X := isShort2_of_map f hf (hXB ▸ hS)
  set eX : ↥X ≃* ↥B :=
    (X.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hXB) with heX
  have hE' : IsExt ↥X (fun N _ => IsE2 11 N) (fun Y _ => IsSporadic .M24 Y) ∨
      IsExt ↥X (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y) := by
    rcases hE with h | h
    · exact Or.inl (isExt_of_mulEquiv eX (isE2_of_mulEquiv 11) (isSporadic_of_mulEquiv .M24) h)
    · exact Or.inr (isExt_of_mulEquiv eX (isE2_of_mulEquiv 10) (isPSL_of_mulEquiv 5 2 1) h)
  obtain ⟨hN, hC, hirr, x, hxX, hx3, hxE, hq, hz, hM, hnot⟩ := hBlk ↥K hK X hS' hE'
  have hQ : (pCoreOf 2 X).map f = pCoreOf 2 B := by
    have := blockQ_map f hf X
    rwa [hXB] at this
  have hQB : pCoreOf 2 B ≤ K := (pCoreOf_le 2 B).trans hBK
  have hmemX : ∀ y : ↥K, y ∈ X ↔ (y : G) ∈ B := fun y => Subgroup.mem_subgroupOf
  set Cx : Subgroup ↥K := Subgroup.centralizer ({x} : Set ↥K) with hCxdef
  have hCx : Cx.map f = K ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
    ext g
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨c.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)
      simp only [Subgroup.coe_mul] at this
      exact this
    · rintro ⟨hgK, hgC⟩
      refine ⟨⟨g, hgK⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_), rfl⟩
      simpa using Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hPC : (perfectCore Cx).map f = perfectCore (K ⊓ Subgroup.centralizer ({(x : G)} : Set G)) :=
    (perfectCore_map f hf Cx).trans (by rw [hCx])
  set eP : ↥(perfectCore Cx) ≃*
      ↥(perfectCore (K ⊓ Subgroup.centralizer ({(x : G)} : Set G))) :=
    ((perfectCore Cx).equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hPC) with heP
  refine ⟨?_, ?_, ?_, (x : G), (hmemX x).mp hxX, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    · rintro g ⟨hgK, hgN⟩
      have hg' : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.normalizer (X : Set ↥K) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        rw [hmemX, hmemX]
        exact (Subgroup.mem_normalizer_iff.mp hgN) y
      rw [hN] at hg'
      exact (hmemX _).mp hg'
    · exact le_inf hBK Subgroup.le_normalizer
  ·
    apply le_antisymm
    · rintro g ⟨hgK, hgC⟩
      have hg' : (⟨g, hgK⟩ : ↥K) ∈ Subgroup.centralizer (pCoreOf 2 X : Set ↥K) := by
        refine (mem_centralizer_map_iff f hf).mp ?_
        rw [hQ]
        exact hgC
      rw [hC] at hg'
      rw [← hQ]
      exact ⟨_, hg', rfl⟩
    · intro p hp
      refine ⟨hQB hp, ?_⟩
      rw [← hQ] at hp ⊢
      obtain ⟨p', hp', rfl⟩ := hp
      rw [← hC] at hp'
      exact (mem_centralizer_map_iff f hf).mpr hp'
  ·
    intro W hWQ hBW
    have hWK : W ≤ K := hWQ.trans hQB
    set W' : Subgroup ↥K := W.subgroupOf K with hW'
    have hW'map : W'.map f = W := by
      rw [hW', Subgroup.subgroupOf_map_subtype, inf_of_le_left hWK]
    have hW'Q : W' ≤ pCoreOf 2 X := by
      intro w hw
      have h1 : (w : G) ∈ pCoreOf 2 B := hWQ (Subgroup.mem_subgroupOf.mp hw)
      rw [← hQ] at h1
      exact (Subgroup.mem_map_iff_mem hf).mp h1
    have hXW' : X ≤ Subgroup.normalizer (W' : Set ↥K) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro w
      rw [hW', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hBW ((hmemX y).mp hy))) w
    rcases hirr W' hW'Q hXW' with h | h
    · left
      rw [← hW'map, h, Subgroup.map_bot]
    · right
      rw [← hW'map, h, hQ]
  ·
    rw [Subgroup.orderOf_coe]
    exact hx3
  ·
    intro hb
    apply hxE
    rw [eq_bot_iff]
    rintro y ⟨hyQ, hyC⟩
    have h1 : (y : G) ∈ pCoreOf 2 B ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
      refine ⟨hQ ▸ ⟨y, hyQ, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC)
      simpa using this
    rw [hb, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  ·
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eP hq
  ·
    rw [← center_map_mulEquiv eP, Subgroup.card_map_of_injective eP.injective]
    exact hz
  ·
    exact isSporadic_of_mulEquiv .M22 _ _
      (QuotientGroup.congr _ _ eP (center_map_mulEquiv eP)) hM
  ·
    intro hle
    apply hnot
    rintro y ⟨hyQ, hyC⟩
    have h1 : (y : G) ∈ pCoreOf 2 B ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
      refine ⟨hQ ▸ ⟨y, hyQ, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyC)
      simpa using this
    have h2 := hle h1
    rw [← hPC] at h2
    exact (mem_centralizer_map_iff f hf).mp h2

end Ambient

end NoJ4

end CFSG.Quasithin.H13.Ch4
