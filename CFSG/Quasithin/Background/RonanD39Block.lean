module

public import CFSG.Quasithin.Background.RonanD39Sec
public import CFSG.Quasithin.EmptyFaithful.S153ZN

public section

namespace CFSG.Quasithin.RonanD39

open scoped Pointwise
open CFSG.Quasithin.Z391 CFSG.QuasithinUnique

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem le_stabilizer_of_isInv {S : Subgroup Γ} {P : Subgroup Q} (hS : XMod.IsInv ↥S P) :
    S ≤ MulAction.stabilizer Γ P := by
  intro s hs
  rw [MulAction.mem_stabilizer_iff]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hS ⟨s, hs⟩ x hx
  · intro x hx
    exact ⟨s⁻¹ • x, hS ⟨s⁻¹, S.inv_mem hs⟩ x hx, by simp [smul_inv_smul]⟩

theorem elem_subgroupOf {A H : Subgroup Γ} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hA2 : ∀ x ∈ A, x ^ 2 = 1) :
    (∀ x ∈ A.subgroupOf H, ∀ y ∈ A.subgroupOf H, x * y = y * x) ∧
      ∀ x ∈ A.subgroupOf H, x ^ 2 = 1 :=
  ⟨fun x hx y hy => Subtype.ext (hAc _ hx _ hy),
    fun x hx => Subtype.ext (by simpa using hA2 _ hx)⟩

theorem rk_subgroupOf_of_le {A H : Subgroup Γ} (hAH : A ≤ H) :
    rk ↥(A.subgroupOf H) = rk ↥A := by
  unfold rk
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv]

theorem rk_map_subtype {H : Subgroup Γ} (A : Subgroup ↥H) : rk ↥(A.map H.subtype) = rk ↥A := by
  unfold rk
  rw [Subgroup.card_map_of_injective H.subtype_injective]

theorem block_step [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ T A : Subgroup Γ}
    (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ) (hT : IsSylowTwoOf T ⊤) (hAT : A ≤ T)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : ∀ x ∈ A, x ^ 2 = 1)
    {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) (hVT : ∀ t ∈ T, t • V = V)
    {P : Subgroup Q} (hPΛ : XMod.IsInv ↥Λ P) (hPA : XMod.IsInv ↥A P) {g₀ : Γ}
    (hg₀ : ¬ g₀ • V ≤ P) :
    ∃ (P' : Subgroup Q) (g : Γ) (A₁ : Subgroup Γ), P < P' ∧ XMod.IsInv ↥Λ P' ∧
      XMod.IsInv ↥A P' ∧ LChain Λ (rk ↥V) P P' (2 ^ (rk ↥A - rk ↥A₁)) ∧ A₁ ≤ A ∧
      A₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ T ∧
      nB (A₁.map (MulAut.conj g⁻¹).toMonoidHom) V + (2 ^ (rk ↥A - rk ↥A₁) - 1) * rk ↥V ≤
        nS A P P' := by
  classical
  set H : Subgroup Γ := MulAction.stabilizer Γ P with hH
  have hΛH : Λ ≤ H := le_stabilizer_of_isInv hPΛ
  have hAH : A ≤ H := le_stabilizer_of_isInv hPA
  have hPH : ∀ h : ↥H, ∀ x ∈ P, h • x ∈ P := by
    intro h x hx
    have h1 := Subgroup.smul_mem_pointwise_smul x (h : Γ) P hx
    have h2 : (h : Γ) • P = P := h.2
    rw [h2] at h1
    exact h1
  set mk : Q →* QuotMod P hPH := QuotMod.mk P hPH with hmk
  have hmkeq : ∀ (h : ↥H) (x : Q), mk (h • x) = h • mk x := fun _ _ => rfl
  have hker : mk.ker = P := QuotMod.ker_mk P hPH
  have hq2 : ∀ p : QuotMod P hPH, p ^ 2 = 1 := by
    intro p
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective P hPH p
    rw [← map_pow, hQ x, map_one]
  set Λ' : Subgroup ↥H := Λ.subgroupOf H with hΛ'def
  set A' : Subgroup ↥H := A.subgroupOf H with hA'def
  have hΛ' : ∀ g : ↥H, ∀ l ∈ Λ', g * l * g⁻¹ ∈ Λ' := fun g l hl => hΛ (g : Γ) (l : Γ) hl
  have hNH : XMod.Normalizes ↥Λ' ↥H (QuotMod P hPH) := normalizes_whole Λ' hΛ'
  have hNA' : XMod.Normalizes ↥Λ' ↥A' (QuotMod P hPH) :=
    normalizes_of_conj Λ' A' (fun g _ l hl => hΛ' g l hl)
  have hNΓ : XMod.Normalizes ↥Λ Γ Q := normalizes_whole Λ hΛ
  set S₀ : Subgroup Q := g₀ • V with hS₀def
  have hS₀ : XMod.IsIrr ↥Λ S₀ := isIrr_smul hNΓ g₀ hV
  have hS₀' : XMod.IsIrr ↥Λ' S₀ := (isIrr_subgroupOf_iff hΛH).2 hS₀
  have hS₀P : S₀ ⊓ P = ⊥ := by
    rcases hS₀.2.2 (S₀ ⊓ P) (hS₀.1.inf hPΛ) bot_le inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hg₀
  have hinjS₀ : ∀ x ∈ S₀, mk x = 1 → x = 1 := by
    intro x hx h1
    have : x ∈ S₀ ⊓ P := ⟨hx, hker ▸ MonoidHom.mem_ker.2 h1⟩
    rwa [hS₀P, Subgroup.mem_bot] at this
  obtain ⟨g, hgiso, hgT⟩ := exists_fixing_translate hΛ hT hAT hV.1 hVT g₀
  set Y : Subgroup Q := g • V with hYdef
  have hY : XMod.IsIrr ↥Λ Y := isIrr_smul hNΓ g hV
  have hY' : XMod.IsIrr ↥Λ' Y := (isIrr_subgroupOf_iff hΛH).2 hY
  obtain ⟨ψ, hψ⟩ := hgiso
  set φ₀ : ↥Y →* QuotMod P hPH := mk.comp (S₀.subtype.comp ψ.toMonoidHom) with hφ₀def
  have hφ₀Λ : EqvOn Λ' Y φ₀ := by
    intro l hl y hy
    have h1 := hψ ⟨(l : Γ), hl⟩ y ⟨(l : Γ) • (y : Q), hy⟩ rfl
    show mk ((ψ ⟨(l : Γ) • (y : Q), hy⟩ : ↥S₀) : Q) = l • mk ((ψ y : ↥S₀) : Q)
    rw [← h1]
    rfl
  have hY1 : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hY.2.1.ne' ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hφ₀ne : φ₀ ≠ 1 := by
    obtain ⟨y, hy, hy1⟩ := hY1
    intro h
    have h1 : φ₀ ⟨y, hy⟩ = 1 := by rw [h]; rfl
    have h2 := hinjS₀ _ (ψ ⟨y, hy⟩).2 h1
    have h3 : ψ ⟨y, hy⟩ = 1 := Subtype.ext h2
    have h4 : (⟨y, hy⟩ : ↥Y) = 1 := by
      have := congrArg ψ.symm h3
      rwa [MulEquiv.symm_apply_apply, map_one] at this
    exact hy1 (congrArg Subtype.val h4)
  have hφ₀inj : Function.Injective φ₀ := injective_of_eqvOn hY' hφ₀Λ hφ₀ne
  have hφ₀range : φ₀.range = S₀.map mk := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(ψ y : Q), (ψ y).2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨ψ.symm ⟨x, hx⟩, ?_⟩
      show mk ((ψ (ψ.symm ⟨x, hx⟩) : ↥S₀) : Q) = mk x
      rw [MulEquiv.apply_symm_apply]
  set S₁ : Subgroup (QuotMod P hPH) := φ₀.range with hS₁def
  have hS₁ : XMod.IsIrr ↥Λ' S₁ := isIrr_range_of_eqvOn hY' hφ₀Λ hφ₀inj
  set A₁' : Subgroup ↥H := A' ⊓ typeStab Λ' hNH hS₁.1 with hA₁'def
  set A₁ : Subgroup Γ := A₁'.map H.subtype with hA₁def
  have hA₁A : A₁ ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha.1
  have hA₁H : A₁ ≤ H := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hA₁'eq : A₁.subgroupOf H = A₁' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hA₁iso : ∀ a ∈ A₁, XMod.Iso ↥Λ (a • S₀) S₀ := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : XMod.Iso ↥Λ' (a • S₁) S₁ := ha.2
    have h2 : a • S₁ = (a • S₀).map mk := by
      rw [hφ₀range]
      exact (map_smul_of_equivariant mk hmkeq a S₀).symm
    rw [h2, hφ₀range] at h1
    have hinv : XMod.IsInv ↥Λ' S₀ := hS₀'.1
    have hinja : ∀ x ∈ a • S₀, mk x = 1 → x = 1 := by
      intro x hx h1
      obtain ⟨y, hy, hyx⟩ := hx
      have hyx' : a • y = x := hyx
      subst hyx'
      have hxP : a • y ∈ P := hker ▸ MonoidHom.mem_ker.2 h1
      have h3 : y ∈ P := by
        have := hPH a⁻¹ _ hxP
        rwa [inv_smul_smul] at this
      have h4 : y = 1 := by
        have : y ∈ S₀ ⊓ P := ⟨hy, h3⟩
        rwa [hS₀P, Subgroup.mem_bot] at this
      rw [h4, smul_one]
    have h3 := iso_of_iso_map mk hmkeq hinv hinja hinjS₀ h1
    exact (iso_subgroupOf_iff hΛH).1 h3
  have hA₁T : ∀ a ∈ A₁, g⁻¹ * a * g ∈ T := fun a ha => hgT a (hA₁A ha) (hA₁iso a ha)
  have hA₁Y : ∀ a ∈ A₁, a • Y = Y := fun a ha => smul_translate_eq hVT (hA₁T a ha)
  set K : Subgroup Γ := H ⊓ MulAction.stabilizer Γ Y with hKdef
  have hKH : K ≤ H := inf_le_left
  have hYK : ∀ k : ↥K, ∀ y ∈ Y, k • y ∈ Y := by
    intro k y hy
    have h1 := Subgroup.smul_mem_pointwise_smul y (k : Γ) Y hy
    have h2 : (k : Γ) • Y = Y := k.2.2
    rw [h2] at h1
    exact h1
  have hΛK : Λ ≤ K := le_inf hΛH (le_stabilizer_of_isInv hY.1)
  have hA₁K : A₁ ≤ K := le_inf hA₁H (fun a ha => hA₁Y a ha)
  letI iY : MulDistribMulAction ↥K ↥Y := subAct Y hYK
  letI iQ : MulDistribMulAction ↥K (QuotMod P hPH) :=
    MulDistribMulAction.compHom _ (Subgroup.inclusion hKH)
  have hA₁p : IsPGroup 2 ↥(A₁.subgroupOf K) := by
    refine isPGroup_two_of_sq_eq_one fun x => Subtype.ext (Subtype.ext ?_)
    have := hA2 _ (hA₁A x.2)
    simpa using this
  have hA₁Λ : ∀ b ∈ A₁.subgroupOf K, ∀ l ∈ Λ.subgroupOf K, b * l * b⁻¹ ∈ Λ.subgroupOf K :=
    fun b _ l hl => hΛ _ _ hl
  have hφ₀K : ∀ l ∈ Λ.subgroupOf K, ∀ p : ↥Y, φ₀ (l • p) = l • φ₀ p := by
    intro l hl p
    exact hφ₀Λ ⟨((l : ↥K) : Γ), hKH l.2⟩ hl p _
  obtain ⟨φ, hφne, hφΛK, hφAK⟩ := exists_fixed_hom (Γ := ↥K) hq2 (Λ.subgroupOf K)
    (A₁.subgroupOf K) hA₁p hA₁Λ φ₀ hφ₀K hφ₀ne
  have hφΛ : EqvOn Λ' Y φ := by
    intro l hl y hy
    exact hφΛK ⟨(l : Γ), hΛK hl⟩ hl y
  have hφA : EqvOn A₁' Y φ := by
    intro a ha y hy
    have ha' : (a : Γ) ∈ A₁ := ⟨a, ha, rfl⟩
    exact hφAK ⟨(a : Γ), hA₁K ha'⟩ ha' y
  have hφinj : Function.Injective φ := injective_of_eqvOn hY' hφΛ hφne
  set Yb : Subgroup (QuotMod P hPH) := φ.range with hYbdef
  have hYb : XMod.IsIrr ↥Λ' Yb := isIrr_range_of_eqvOn hY' hφΛ hφinj
  have hYbS₁ : XMod.Iso ↥Λ' Yb S₁ := iso_range_of_eqvOn hY'.1 hφΛ hφ₀Λ hφinj hφ₀inj
  have hS₁Yb : XMod.Iso ↥Λ' S₁ Yb := XMod.Iso.symm hYb.1 hYbS₁
  have hYbA : ∀ a ∈ A₁', a • Yb ≤ Yb := by
    intro a ha
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    have hay : (a : Γ) • (y : Q) ∈ Y := by
      have := hYK ⟨(a : Γ), hA₁K ⟨a, ha, rfl⟩⟩ y y.2
      exact this
    exact ⟨⟨(a : Γ) • (y : Q), hay⟩, hφA a ha y hay⟩
  have hfix : ∀ a ∈ A₁', a • Yb = Yb := by
    intro a ha
    refine le_antisymm (hYbA a ha) ?_
    have h1 := hYbA a⁻¹ (A₁'.inv_mem ha)
    have h2 := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := a)).2 h1
    rwa [smul_inv_smul] at h2
  have hstab' : ∀ a : ↥H, a ∈ A' → XMod.Iso ↥Λ' (a • Yb) Yb → a ∈ A₁' := by
    intro a ha hiso
    refine ⟨ha, ?_⟩
    show XMod.Iso ↥Λ' (a • S₁) S₁
    exact ((XMod.iso_smul hNH a hS₁Yb).trans hiso).trans hYbS₁
  have hstab : ∀ a ∈ A', a • Yb = Yb → a ∈ A₁' := by
    intro a ha h
    refine hstab' a ha ?_
    rw [h]
    exact XMod.Iso.refl _
  have hfixiso : ∀ t : ↥A', XMod.Iso ↥Λ' (t • Yb) Yb → t • Yb = Yb := fun t ht =>
    hfix t (hstab' t t.2 ht)
  have hind : sSupIndep (Set.range fun t : ↥A' => t • Yb) :=
    XMod.sSupIndep_smul_of_isHomComp hNA' hYb
      ((XMod.forall_iso_smul_eq_iff_isHomComp hNA' hYb).1 hfixiso)
  obtain ⟨hAc', hA2'⟩ := elem_subgroupOf (H := H) hAc hA2
  have hrkA' : rk ↥A' = rk ↥A := rk_subgroupOf_of_le hAH
  have hrkA₁ : rk ↥A₁ = rk ↥A₁' := rk_map_subtype A₁'
  have hrkle : rk ↥A₁ ≤ rk ↥A := rk_mono hA₁A
  set j := rk ↥A - rk ↥A₁ with hj
  have hrk : rk ↥A' = rk ↥A₁' + j := by omega
  obtain ⟨hblk, hblkrk⟩ := nB_block (Γ := ↥H) Yb j A' A₁' hAc' hA2' inf_le_left hrk hfix hstab hind
  set Blk : Subgroup (QuotMod P hPH) := ⨆ t : ↥A', (t : ↥H) • Yb with hBlkdef
  have hrkY : rk ↥Y = rk ↥V := rk_smul g V
  have hrkYb : rk ↥Yb = rk ↥V := by
    rw [← hrkY]
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm)
  have hrkV : 0 < rk ↥V := by
    by_contra h0
    have : rk ↥V = 0 := by omega
    exact hV.2.1.ne' ((rk_eq_zero_iff hQ).1 this)
  have hfin : (Set.range fun t : ↥A' => (t : ↥H) • Yb).Finite := Set.finite_range _
  set s : Finset (Subgroup (QuotMod P hPH)) := hfin.toFinset with hsdef
  have hsup : s.sup id = Blk := by
    rw [Finset.sup_id_eq_sSup, hsdef, Set.Finite.coe_toFinset, sSup_range]
  have hirr : ∀ X ∈ s, XMod.IsIrr ↥Λ' X ∧ rk ↥X = rk ↥V := by
    intro X hX
    rw [hsdef, Set.Finite.mem_toFinset] at hX
    obtain ⟨t, rfl⟩ := hX
    exact ⟨isIrr_smul hNH (t : ↥H) hYb, by rw [rk_smul, hrkYb]⟩
  have hind' : sSupIndep (s : Set (Subgroup (QuotMod P hPH))) := by
    rw [hsdef, Set.Finite.coe_toFinset]
    exact hind
  have hch := LChain.of_sSupIndep (Λ := Λ') s hirr hind'
  rw [hsup] at hch
  have hcard : s.card = 2 ^ j := by
    have h1 := hch.rk_eq
    rw [rk_bot, zero_add] at h1
    rw [hblkrk, hrkYb] at h1
    exact (Nat.eq_of_mul_eq_mul_right hrkV h1).symm
  rw [hcard] at hch
  have hch' := LChain.comap_quotMod hΛH hPH hch
  rw [MonoidHom.comap_bot, hker] at hch'
  set P' : Subgroup Q := Blk.comap mk with hP'def
  have hPP' : P ≤ P' := hch'.le
  have hrkP' := hch'.rk_eq
  have hblkΛ : XMod.IsInv ↥Λ' Blk :=
    XMod.isInv_iSup fun t => XMod.isInv_smul_of_normalizes hNH (t : ↥H) hYb.1
  have hblkA : XMod.IsInv ↥A' Blk := by
    intro a x hx
    have h1 : (a : ↥H) • Blk ≤ Blk := by
      rw [hBlkdef, smul_iSup_translate]
      exact iSup_le fun t =>
        le_iSup (fun s : ↥A' => (s : ↥H) • Yb) ⟨(a : ↥H) * (t : ↥H), A'.mul_mem a.2 t.2⟩
    exact h1 (Subgroup.smul_mem_pointwise_smul _ _ _ hx)
  refine ⟨P', g, A₁, lt_of_le_of_ne hPP' fun h => ?_, isInv_comap_quotMod hΛH hPH hblkΛ,
    isInv_comap_quotMod hAH hPH hblkA, hch', hA₁A, ?_, ?_⟩
  · rw [← h] at hrkP'
    have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    nlinarith
  · rintro _ ⟨a, ha, rfl⟩
    have := hA₁T a ha
    simpa [MulAut.conj_apply] using this
  · have h1 : nS A P P' = nB A' Blk := by
      rw [← nB_map_quotMod hAH hPH hPP', hP'def,
        Subgroup.map_comap_eq_self_of_surjective (QuotMod.mk_surjective P hPH)]
    have h2 : nB A₁' Yb = nB (A₁.map (MulAut.conj g⁻¹).toMonoidHom) V := by
      have hYA₁ : XMod.IsInv ↥A₁' Y := fun a y hy =>
        hYK ⟨(a : Γ), hA₁K ⟨a, a.2, rfl⟩⟩ y hy
      rw [nB_range_of_eqvOn hYA₁ hφA hφinj, ← hA₁'eq, nB_subgroupOf hA₁H]
      have := nB_smul (A₁.map (MulAut.conj g⁻¹).toMonoidHom) g V
      rw [map_conj_inv_conj] at this
      exact this
    rw [h1, ← h2, ← hrkYb]
    exact hblk

end CFSG.Quasithin.RonanD39
