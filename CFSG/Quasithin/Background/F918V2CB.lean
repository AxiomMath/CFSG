module

public import CFSG.Quasithin.Background.F918V2CA
public import CFSG.Quasithin.EmptyFaithful.S153ZM
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.Z391

open scoped Pointwise

theorem v2c_inv_of_sup {G : Type*} [Group G] {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    {Λ B : Subgroup G} (h : Λ ⊔ B = ⊤) {Y : Subgroup M} (hΛ : XMod.IsInv ↥Λ Y)
    (hB : XMod.IsInv ↥B Y) : ∀ g : G, ∀ y ∈ Y, g • y ∈ Y := by
  have hstab : ∀ C : Subgroup G, XMod.IsInv ↥C Y → C ≤ MulAction.stabilizer G Y := by
    intro C hC c hc
    rw [MulAction.mem_stabilizer_iff]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hC ⟨c, hc⟩ y hy
    · intro y hy
      refine ⟨c⁻¹ • y, hC ⟨c⁻¹, C.inv_mem hc⟩ y hy, by simp [smul_inv_smul]⟩
  have htop : (⊤ : Subgroup G) ≤ MulAction.stabilizer G Y := by
    rw [← h]
    exact sup_le (hstab _ hΛ) (hstab _ hB)
  intro g y hy
  have hg : g • Y = Y := MulAction.mem_stabilizer_iff.1 (htop (Subgroup.mem_top g))
  rw [← hg]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ hy

theorem v2c_step_embed {G : Type*} [Group G] {M₀ : Type*} [CommGroup M₀] [Finite M₀]
    [MulDistribMulAction G M₀] {M' : Type*} [CommGroup M'] [Finite M'] [MulDistribMulAction G M']
    (hM' : ∀ p : M', p ^ 2 = 1) {Λ B : Subgroup G} (hB : IsPGroup 2 B)
    (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ) {V : Subgroup M₀}
    (hVinv : ∀ g : G, ∀ v ∈ V, g • v ∈ V) (hV : XMod.IsIrr ↥Λ V) (ψ₀ : ↥V →* M')
    (hψ₀ : ∀ l ∈ Λ, ∀ v : ↥V, ψ₀ ⟨l • (v : M₀), hVinv l v v.2⟩ = l • ψ₀ v) (hne : ψ₀ ≠ 1) :
    ∃ φ : ↥V →* M', Function.Injective φ ∧
      (∀ l ∈ Λ, ∀ v : ↥V, φ ⟨l • (v : M₀), hVinv l v v.2⟩ = l • φ v) ∧
      (∀ b ∈ B, ∀ v : ↥V, φ ⟨b • (v : M₀), hVinv b v v.2⟩ = b • φ v) ∧
      nB B φ.range = nB B V := by
  classical
  let _ : MulDistribMulAction G ↥V := subAct V hVinv
  obtain ⟨φ, hφne, hφΛ, hφA⟩ := exists_fixed_hom hM' Λ B hB hBΛ ψ₀ (fun l hl p => hψ₀ l hl p) hne
  have hker : φ.ker = ⊥ := by
    set K : Subgroup M₀ := (φ.ker).map V.subtype with hK
    have hKΛ : XMod.IsInv ↥Λ K := by
      rintro ⟨l, hl⟩ k hk
      obtain ⟨k', hk', rfl⟩ := hk
      refine ⟨l • k', ?_, rfl⟩
      have hk'' : φ k' = 1 := hk'
      show φ (l • k') = 1
      rw [hφΛ l hl k', hk'', smul_one]
    rcases hV.2.2 K hKΛ bot_le (Subgroup.map_subtype_le _) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).2 fun k hk => ?_
      have hk' : (k : M₀) ∈ K := ⟨k, hk, rfl⟩
      rw [h, Subgroup.mem_bot] at hk'
      exact Subtype.ext hk'
    · exfalso
      apply hφne
      refine MonoidHom.ext fun v => ?_
      have hv : (v : M₀) ∈ K := by rw [h]; exact v.2
      obtain ⟨v', hv', hvv'⟩ := hv
      have : v' = v := Subtype.ext hvv'
      rw [← this]
      exact hv'
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  refine ⟨φ, hinj, fun l hl v => hφΛ l hl v, fun b hb v => hφA b hb v, ?_⟩
  set S : Subgroup M' := φ.range with hS
  unfold nB
  set F := XMod.fixed ↥B (⊤ : Subgroup M₀) with hF
  set F' := XMod.fixed ↥B (⊤ : Subgroup M') with hF'
  have hrk1 : rk ↥S = rk ↥V := by
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
  have key : ∀ (a : G) (v : ↥V), a • v = v ↔ a • (v : M₀) = (v : M₀) :=
    fun a v => ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hmap : S ⊓ F' = ((V ⊓ F).subgroupOf V).map φ := by
    ext y
    constructor
    · rintro ⟨⟨v, rfl⟩, hy⟩
      refine ⟨v, ?_, rfl⟩
      refine ⟨v.2, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
      have h1 := (XMod.mem_fixed.1 hy).2 a
      change (a : G) • φ v = φ v at h1
      rw [← hφA (a : G) a.2 v] at h1
      exact (key a v).1 (hinj h1)
    · rintro ⟨v, hv, rfl⟩
      refine ⟨⟨v, rfl⟩, XMod.mem_fixed.2 ⟨trivial, fun a => ?_⟩⟩
      have h1 := (XMod.mem_fixed.1 hv.2).2 a
      change (a : G) • (v : M₀) = v at h1
      change (a : G) • φ v = φ v
      rw [← hφA (a : G) a.2 v, (key a v).2 h1]
  have hrk2 : rk ↥(S ⊓ F') = rk ↥(V ⊓ F) := by
    rw [hmap]
    unfold rk
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ φ hinj).toEquiv.symm]
    exact congrArg _ (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv)
  rw [hrk1, hrk2]

theorem v2c_step_nB {G : Type*} [Group G] {M₀ : Type*} [CommGroup M₀] [Finite M₀]
    [MulDistribMulAction G M₀] {M : Type*} [CommGroup M] [Finite M] [MulDistribMulAction G M]
    (hM : ∀ q : M, q ^ 2 = 1) {Λ B : Subgroup G} (hB : IsPGroup 2 B)
    (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ) {V : Subgroup M₀}
    (hVinv : ∀ g : G, ∀ v ∈ V, g • v ∈ V) (hV : XMod.IsIrr ↥Λ V) (N : Subgroup M)
    (hN : ∀ g : G, ∀ n ∈ N, g • n ∈ N) (ψ₀ : ↥V →* QuotMod N hN)
    (hψ₀ : ∀ l ∈ Λ, ∀ v : ↥V, ψ₀ ⟨l • (v : M₀), hVinv l v v.2⟩ = l • ψ₀ v) (hne : ψ₀ ≠ 1) :
    nB B N + nB B V ≤ nB B (⊤ : Subgroup M) := by
  have hq2 : ∀ p : QuotMod N hN, p ^ 2 = 1 := by
    intro p
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective N hN p
    rw [← map_pow, hM x, map_one]
  obtain ⟨φ, -, -, -, hn⟩ := v2c_step_embed hq2 hB hBΛ hVinv hV ψ₀ hψ₀ hne
  have h1 := nB_chain B N hN
  have h2 := nB_mono B (le_top : φ.range ≤ (⊤ : Subgroup (QuotMod N hN)))
  omega

theorem v2c_exists_embed {G : Type*} [Group G] {M : Type*} [CommGroup M] [MulDistribMulAction G M]
    {Λ : Subgroup G} {V S : Subgroup M} (hVinv : ∀ g : G, ∀ v ∈ V, g • v ∈ V)
    (hS : XMod.IsInv ↥Λ S) (hiso : XMod.Iso ↥Λ S V) :
    ∃ ι : ↥V →* M, Function.Injective ι ∧ (∀ v, ι v ∈ S) ∧ (∀ s ∈ S, ∃ v, ι v = s) ∧
      ∀ l ∈ Λ, ∀ v : ↥V, ι ⟨l • (v : M), hVinv l v v.2⟩ = l • ι v := by
  obtain ⟨φ, hφ⟩ := hiso
  refine ⟨S.subtype.comp φ.symm.toMonoidHom, ?_, fun v => (φ.symm v).2, ?_, ?_⟩
  · intro v w h
    have : φ.symm v = φ.symm w := Subtype.ext h
    exact φ.symm.injective this
  · intro s hs
    exact ⟨φ ⟨s, hs⟩, by simp⟩
  · intro l hl v
    set x : ↥S := φ.symm v with hx
    set a : ↥Λ := ⟨l, hl⟩ with ha
    have hlx : l • (x : M) ∈ S := hS a x x.2
    have h1 := hφ a x ⟨l • (x : M), hlx⟩ rfl
    have hφx : φ x = v := φ.apply_symm_apply v
    rw [hφx] at h1
    have h2 : φ ⟨l • (x : M), hlx⟩ = ⟨l • (v : M), hVinv l v v.2⟩ := Subtype.ext h1.symm
    have h3 : φ.symm ⟨l • (v : M), hVinv l v v.2⟩ = ⟨l • (x : M), hlx⟩ := by
      rw [← h2, φ.symm_apply_apply]
    show ((φ.symm ⟨l • (v : M), hVinv l v v.2⟩ : ↥S) : M) = l • ((x : ↥S) : M)
    rw [h3]

theorem v2c_rk_eq_of_iso {A : Type*} [Group A] {M : Type*} [CommGroup M] [MulDistribMulAction A M]
    {S V : Subgroup M} (h : XMod.Iso A S V) : rk ↥S = rk ↥V := by
  obtain ⟨φ, -⟩ := h
  unfold rk
  rw [Nat.card_congr φ.toEquiv]

theorem v2c_comp_mk_ne_one {G : Type*} [Group G] {M : Type*} [CommGroup M]
    [MulDistribMulAction G M] {V S N : Subgroup M} (hN : ∀ g : G, ∀ n ∈ N, g • n ∈ N)
    (ι : ↥V →* M) (hιinj : Function.Injective ι) (hιS : ∀ v, ι v ∈ S) (hSN : S ⊓ N = ⊥)
    (hV0 : V ≠ ⊥) : (QuotMod.mk N hN).comp ι ≠ 1 := by
  obtain ⟨v₀, hv₀⟩ : ∃ v : ↥V, v ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hV0
    refine (Subgroup.eq_bot_iff_forall _).2 fun v hv => ?_
    exact congrArg Subtype.val (hcon ⟨v, hv⟩)
  intro h
  have h1 : QuotMod.mk N hN (ι v₀) = 1 := by
    have := DFunLike.congr_fun h v₀
    simpa using this
  have h2 : ι v₀ ∈ (QuotMod.mk N hN).ker := h1
  rw [QuotMod.ker_mk] at h2
  have h3 : ι v₀ ∈ S ⊓ N := ⟨hιS v₀, h2⟩
  rw [hSN, Subgroup.mem_bot] at h3
  exact hv₀ (hιinj (h3.trans (map_one ι).symm))

theorem v2c_inf_sup_eq_bot {G : Type*} [Group G] {M : Type*} [CommGroup M]
    [MulDistribMulAction G M] {Λ : Subgroup G} {V S P₀ P₁ : Subgroup M}
    (hS : XMod.IsIrr ↥Λ S) (hN : XMod.IsInv ↥Λ (V ⊔ P₁)) (hdisj : P₀ ⊓ P₁ = ⊥) (hVP : V ≤ P₀)
    (hSP : S ≤ P₀) (hVS : V ⊓ S = ⊥) : S ⊓ (V ⊔ P₁) = ⊥ := by
  rcases v2c_inf_eq_bot_or_le hS hN with h | h
  · exact h
  · exfalso
    have h2 : (V ⊔ P₁) ⊓ P₀ = V := by
      rw [sup_inf_assoc_of_le P₁ hVP, inf_comm P₁ P₀, hdisj, sup_bot_eq]
    have h3 : S ≤ V := by
      have : S ≤ (V ⊔ P₁) ⊓ P₀ := le_inf h hSP
      rwa [h2] at this
    exact hS.2.1.ne' ((inf_eq_right.2 h3).symm.trans hVS)

theorem v2c_coreG2 {G : Type*} [Group G] {M : Type*} [CommGroup M] [Finite M]
    [MulDistribMulAction G M] (hM : ∀ q : M, q ^ 2 = 1) {Λ B : Subgroup G} (hLB : Λ ⊔ B = ⊤)
    (hB2 : IsPGroup 2 B) (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ) {V S P₀ P₁ : Subgroup M}
    (hV : XMod.IsIrr ↥Λ V) (hVB : XMod.IsInv ↥B V) (hP₁Λ : XMod.IsInv ↥Λ P₁)
    (hP₁B : XMod.IsInv ↥B P₁) (hP₀B : XMod.IsInv ↥B P₀) (hdisj : P₀ ⊓ P₁ = ⊥)
    (htop : P₀ ⊔ P₁ = ⊤) (hVP : V ≤ P₀) (hSP : S ≤ P₀) (hS : XMod.IsIrr ↥Λ S)
    (hiso : XMod.Iso ↥Λ S V) (hVS : V ⊓ S = ⊥) : 2 * nB B V ≤ nB B P₀ := by
  classical
  have hVG := v2c_inv_of_sup hLB hV.1 hVB
  have hNΛ : XMod.IsInv ↥Λ (V ⊔ P₁) := hV.1.sup hP₁Λ
  have hNB : XMod.IsInv ↥B (V ⊔ P₁) := hVB.sup hP₁B
  have hNG := v2c_inv_of_sup hLB hNΛ hNB
  have hVP₁ : V ⊓ P₁ = ⊥ := le_bot_iff.1 (hdisj ▸ inf_le_inf_right P₁ hVP)
  have hnN : nB B (V ⊔ P₁) = nB B V + nB B P₁ := nB_sup_of_disjoint B hVB hP₁B hVP₁
  have hSN : S ⊓ (V ⊔ P₁) = ⊥ := v2c_inf_sup_eq_bot hS hNΛ hdisj hVP hSP hVS
  obtain ⟨ι, hιinj, hιS, -, hιΛ⟩ := v2c_exists_embed hVG hS.1 hiso
  have hψ₀ : ∀ l ∈ Λ, ∀ v : ↥V, ((QuotMod.mk (V ⊔ P₁) hNG).comp ι) ⟨l • (v : M), hVG l v v.2⟩ =
      l • ((QuotMod.mk (V ⊔ P₁) hNG).comp ι) v := by
    intro l hl v
    show QuotMod.mk (V ⊔ P₁) hNG (ι ⟨l • (v : M), hVG l v v.2⟩) =
      l • QuotMod.mk (V ⊔ P₁) hNG (ι v)
    rw [hιΛ l hl v, quotMod_smul_mk]
  have hne := v2c_comp_mk_ne_one hNG ι hιinj hιS hSN hV.2.1.ne'
  have hstep := v2c_step_nB hM hB2 hBΛ hVG hV (V ⊔ P₁) hNG _ hψ₀ hne
  have hsum := nB_sup_of_disjoint B hP₀B hP₁B hdisj
  rw [htop] at hsum
  omega

theorem v2c_coreG3 {G : Type*} [Group G] {M : Type*} [CommGroup M] [Finite M]
    [MulDistribMulAction G M] (hM : ∀ q : M, q ^ 2 = 1) {Λ B : Subgroup G} (hLB : Λ ⊔ B = ⊤)
    (hB2 : IsPGroup 2 B) (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ)
    {V S S' P₀ P₁ : Subgroup M} (hV : XMod.IsIrr ↥Λ V) (hVB : XMod.IsInv ↥B V)
    (hP₁Λ : XMod.IsInv ↥Λ P₁) (hP₁B : XMod.IsInv ↥B P₁) (hP₀B : XMod.IsInv ↥B P₀)
    (hdisj : P₀ ⊓ P₁ = ⊥) (htop : P₀ ⊔ P₁ = ⊤) (hVP : V ≤ P₀) (hSP : S ≤ P₀) (hS'P : S' ≤ P₀)
    (hS : XMod.IsIrr ↥Λ S) (hS' : XMod.IsIrr ↥Λ S') (hiso : XMod.Iso ↥Λ S V)
    (hiso' : XMod.Iso ↥Λ S' V) (hVS : V ⊓ S = ⊥) (hVSS' : (V ⊔ S) ⊓ S' = ⊥) :
    3 * nB B V ≤ nB B P₀ := by
  classical
  have hVG := v2c_inv_of_sup hLB hV.1 hVB
  have hNΛ : XMod.IsInv ↥Λ (V ⊔ P₁) := hV.1.sup hP₁Λ
  have hNB : XMod.IsInv ↥B (V ⊔ P₁) := hVB.sup hP₁B
  have hNG := v2c_inv_of_sup hLB hNΛ hNB
  have hVP₁ : V ⊓ P₁ = ⊥ := le_bot_iff.1 (hdisj ▸ inf_le_inf_right P₁ hVP)
  have hnN : nB B (V ⊔ P₁) = nB B V + nB B P₁ := nB_sup_of_disjoint B hVB hP₁B hVP₁
  have hVS' : V ⊓ S' = ⊥ :=
    le_bot_iff.1 (hVSS' ▸ inf_le_inf_right S' (le_sup_left : V ≤ V ⊔ S))
  have hSN : S ⊓ (V ⊔ P₁) = ⊥ := v2c_inf_sup_eq_bot hS hNΛ hdisj hVP hSP hVS
  have hS'N : S' ⊓ (V ⊔ P₁) = ⊥ := v2c_inf_sup_eq_bot hS' hNΛ hdisj hVP hS'P hVS'
  obtain ⟨ι, hιinj, hιS, hιsurj, hιΛ⟩ := v2c_exists_embed hVG hS.1 hiso
  obtain ⟨ι', hι'inj, hι'S, hι'surj, hι'Λ⟩ := v2c_exists_embed hVG hS'.1 hiso'
  have hψ₀ : ∀ l ∈ Λ, ∀ v : ↥V, ((QuotMod.mk (V ⊔ P₁) hNG).comp ι) ⟨l • (v : M), hVG l v v.2⟩ =
      l • ((QuotMod.mk (V ⊔ P₁) hNG).comp ι) v := by
    intro l hl v
    show QuotMod.mk (V ⊔ P₁) hNG (ι ⟨l • (v : M), hVG l v v.2⟩) =
      l • QuotMod.mk (V ⊔ P₁) hNG (ι v)
    rw [hιΛ l hl v, quotMod_smul_mk]
  have hne₁ := v2c_comp_mk_ne_one hNG ι hιinj hιS hSN hV.2.1.ne'
  have hq₂ : ∀ p : QuotMod (V ⊔ P₁) hNG, p ^ 2 = 1 := by
    intro p
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective (V ⊔ P₁) hNG p
    rw [← map_pow, hM x, map_one]
  obtain ⟨φ₁, hφ₁inj, hφ₁Λ, hφ₁B, hφ₁n⟩ :=
    v2c_step_embed hq₂ hB2 hBΛ hVG hV _ hψ₀ hne₁
  set Y₁ : Subgroup (QuotMod (V ⊔ P₁) hNG) := φ₁.range with hY₁
  have hY₁Λ : XMod.IsInv ↥Λ Y₁ := by
    rintro ⟨l, hl⟩ _ ⟨v, rfl⟩
    exact ⟨⟨l • (v : M), hVG l v v.2⟩, hφ₁Λ l hl v⟩
  have hY₁B : XMod.IsInv ↥B Y₁ := by
    rintro ⟨b, hb⟩ _ ⟨v, rfl⟩
    exact ⟨⟨b • (v : M), hVG b v v.2⟩, hφ₁B b hb v⟩
  have hY₁G := v2c_inv_of_sup hLB hY₁Λ hY₁B
  have hq₃ : ∀ p : QuotMod Y₁ hY₁G, p ^ 2 = 1 := by
    intro p
    obtain ⟨x, rfl⟩ := QuotMod.mk_surjective Y₁ hY₁G p
    rw [← map_pow, hq₂ x, map_one]
  have hrkY : rk ↥Y₁ = rk ↥V := by
    unfold rk
    exact congrArg (padicValNat 2) (Nat.card_congr (MonoidHom.ofInjective hφ₁inj).toEquiv.symm)
  set π₁ := QuotMod.mk (V ⊔ P₁) hNG with hπ₁
  set Z : Subgroup M := Y₁.comap π₁ with hZ
  have hNZ : V ⊔ P₁ ≤ Z := by
    intro n hn
    show π₁ n ∈ Y₁
    have h0 : n ∈ π₁.ker := by rw [hπ₁, QuotMod.ker_mk]; exact hn
    have h1 : π₁ n = 1 := h0
    rw [h1]
    exact Y₁.one_mem
  have hmapZ : Z.map π₁ = Y₁ :=
    Subgroup.map_comap_eq_self_of_surjective (QuotMod.mk_surjective (V ⊔ P₁) hNG) Y₁
  have hinfZ : Z ⊓ π₁.ker = V ⊔ P₁ := by
    rw [hπ₁, QuotMod.ker_mk]
    exact inf_eq_right.2 hNZ
  have hrkZ : rk ↥Z = rk ↥Y₁ + rk ↥(V ⊔ P₁) := by
    have h := B1More.card_map_mul_card_inf_ker Z π₁
    rw [hmapZ, hinfZ] at h
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]
  have hrkN : rk ↥(V ⊔ P₁) = rk ↥V + rk ↥P₁ := by
    have h := rk_sup_add_rk_inf V P₁
    rw [hVP₁, rk_bot] at h
    omega
  have hrkS : rk ↥S = rk ↥V := v2c_rk_eq_of_iso hiso
  have hrkS' : rk ↥S' = rk ↥V := v2c_rk_eq_of_iso hiso'
  have hrkVS : rk ↥(V ⊔ S) = rk ↥V + rk ↥S := by
    have h := rk_sup_add_rk_inf V S
    rw [hVS, rk_bot] at h
    omega
  have hrkW : rk ↥(V ⊔ S ⊔ S') = rk ↥(V ⊔ S) + rk ↥S' := by
    have h := rk_sup_add_rk_inf (V ⊔ S) S'
    rw [hVSS', rk_bot] at h
    omega
  have hWP : V ⊔ S ⊔ S' ≤ P₀ := sup_le (sup_le hVP hSP) hS'P
  have hWP₁ : (V ⊔ S ⊔ S') ⊓ P₁ = ⊥ :=
    le_bot_iff.1 (hdisj ▸ inf_le_inf_right P₁ hWP)
  have hrkWP : rk ↥(V ⊔ S ⊔ S' ⊔ P₁) = rk ↥(V ⊔ S ⊔ S') + rk ↥P₁ := by
    have h := rk_sup_add_rk_inf (V ⊔ S ⊔ S') P₁
    rw [hWP₁, rk_bot] at h
    omega
  have hor : (QuotMod.mk Y₁ hY₁G).comp (π₁.comp ι) ≠ 1 ∨
      (QuotMod.mk Y₁ hY₁G).comp (π₁.comp ι') ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hle : ∀ (j : ↥V →* M), (QuotMod.mk Y₁ hY₁G).comp (π₁.comp j) = 1 → ∀ v, j v ∈ Z := by
      intro j hj v
      have h3 : QuotMod.mk Y₁ hY₁G (π₁ (j v)) = 1 := by
        have := DFunLike.congr_fun hj v
        simpa using this
      have h4 : π₁ (j v) ∈ (QuotMod.mk Y₁ hY₁G).ker := h3
      rw [QuotMod.ker_mk] at h4
      exact h4
    have hSZ : S ≤ Z := by
      intro s hs
      obtain ⟨v, rfl⟩ := hιsurj s hs
      exact hle ι h1 v
    have hS'Z : S' ≤ Z := by
      intro s hs
      obtain ⟨v, rfl⟩ := hι'surj s hs
      exact hle ι' h2 v
    have hWZ : V ⊔ S ⊔ S' ⊔ P₁ ≤ Z :=
      sup_le (sup_le (sup_le (le_sup_left.trans hNZ) hSZ) hS'Z) (le_sup_right.trans hNZ)
    have hrk := rk_mono hWZ
    have h0 : rk ↥V = 0 := by omega
    exact hV.2.1.ne' ((rk_eq_zero_iff hM).1 h0)
  have hstep₂ : ∀ j : ↥V →* M, (∀ l ∈ Λ, ∀ v : ↥V, j ⟨l • (v : M), hVG l v v.2⟩ = l • j v) →
      (QuotMod.mk Y₁ hY₁G).comp (π₁.comp j) ≠ 1 →
      nB B Y₁ + nB B V ≤ nB B (⊤ : Subgroup (QuotMod (V ⊔ P₁) hNG)) := by
    intro j hj hjne
    refine v2c_step_nB hq₂ hB2 hBΛ hVG hV Y₁ hY₁G _ ?_ hjne
    intro l hl v
    show QuotMod.mk Y₁ hY₁G (π₁ (j ⟨l • (v : M), hVG l v v.2⟩)) =
      l • QuotMod.mk Y₁ hY₁G (π₁ (j v))
    rw [hj l hl v, hπ₁, quotMod_smul_mk, quotMod_smul_mk]
  have hsecond : nB B Y₁ + nB B V ≤ nB B (⊤ : Subgroup (QuotMod (V ⊔ P₁) hNG)) := by
    rcases hor with h | h
    · exact hstep₂ ι hιΛ h
    · exact hstep₂ ι' hι'Λ h
  have hchain := nB_chain B (V ⊔ P₁) hNG
  have hsum := nB_sup_of_disjoint B hP₀B hP₁B hdisj
  rw [htop] at hsum
  omega

section Restrict

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem v2c_isInv_subgroupOf {C H : Subgroup Γ} (hCH : C ≤ H) (J : Subgroup Q) :
    XMod.IsInv ↥(C.subgroupOf H) J ↔ XMod.IsInv ↥C J := by
  constructor
  · intro hJ a x hx
    exact hJ ⟨⟨(a : Γ), hCH a.2⟩, a.2⟩ x hx
  · intro hJ b x hx
    exact hJ ⟨((b : ↥H) : Γ), b.2⟩ x hx

theorem v2c_iso_subgroupOf (H : Subgroup Γ) {C : Subgroup Γ} {L L' : Subgroup Q}
    (h : XMod.Iso ↥C L L') : XMod.Iso ↥(C.subgroupOf H) L L' := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ, fun b l l' hl => hφ ⟨((b : ↥H) : Γ), b.2⟩ l l' hl⟩

theorem v2c_core2 [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ B : Subgroup Γ} (hB2 : IsPGroup 2 B)
    (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ) {V S P₀ P₁ : Subgroup Q} (hV : XMod.IsIrr ↥Λ V)
    (hVB : XMod.IsInv ↥B V) (hP₁Λ : XMod.IsInv ↥Λ P₁) (hP₁B : XMod.IsInv ↥B P₁)
    (hP₀B : XMod.IsInv ↥B P₀) (hdisj : P₀ ⊓ P₁ = ⊥) (htop : P₀ ⊔ P₁ = ⊤) (hVP : V ≤ P₀)
    (hSP : S ≤ P₀) (hS : XMod.IsIrr ↥Λ S) (hiso : XMod.Iso ↥Λ S V) (hVS : V ⊓ S = ⊥) :
    2 * nB B V ≤ nB B P₀ := by
  have hΛH : Λ ≤ Λ ⊔ B := le_sup_left
  have hBH : B ≤ Λ ⊔ B := le_sup_right
  have hsup : Λ.subgroupOf (Λ ⊔ B) ⊔ B.subgroupOf (Λ ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hΛH hBH, Subgroup.subgroupOf_self]
  have h := v2c_coreG2 (G := ↥(Λ ⊔ B)) (M := Q) hQ hsup (A4.isPGroup_subgroupOf_of_le hBH hB2)
    (fun b hb l hl => hBΛ _ hb _ hl) (isIrr_subgroupOf hΛH hV)
    ((v2c_isInv_subgroupOf hBH V).2 hVB) ((v2c_isInv_subgroupOf hΛH P₁).2 hP₁Λ)
    ((v2c_isInv_subgroupOf hBH P₁).2 hP₁B) ((v2c_isInv_subgroupOf hBH P₀).2 hP₀B) hdisj htop
    hVP hSP (isIrr_subgroupOf hΛH hS) (v2c_iso_subgroupOf _ hiso) hVS
  rwa [nB_subgroupOf hBH, nB_subgroupOf hBH] at h

theorem v2c_core3 [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ B : Subgroup Γ} (hB2 : IsPGroup 2 B)
    (hBΛ : ∀ b ∈ B, ∀ l ∈ Λ, b * l * b⁻¹ ∈ Λ) {V S S' P₀ P₁ : Subgroup Q}
    (hV : XMod.IsIrr ↥Λ V) (hVB : XMod.IsInv ↥B V) (hP₁Λ : XMod.IsInv ↥Λ P₁)
    (hP₁B : XMod.IsInv ↥B P₁) (hP₀B : XMod.IsInv ↥B P₀) (hdisj : P₀ ⊓ P₁ = ⊥)
    (htop : P₀ ⊔ P₁ = ⊤) (hVP : V ≤ P₀) (hSP : S ≤ P₀) (hS'P : S' ≤ P₀)
    (hS : XMod.IsIrr ↥Λ S) (hS' : XMod.IsIrr ↥Λ S') (hiso : XMod.Iso ↥Λ S V)
    (hiso' : XMod.Iso ↥Λ S' V) (hVS : V ⊓ S = ⊥) (hVSS' : (V ⊔ S) ⊓ S' = ⊥) :
    3 * nB B V ≤ nB B P₀ := by
  have hΛH : Λ ≤ Λ ⊔ B := le_sup_left
  have hBH : B ≤ Λ ⊔ B := le_sup_right
  have hsup : Λ.subgroupOf (Λ ⊔ B) ⊔ B.subgroupOf (Λ ⊔ B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hΛH hBH, Subgroup.subgroupOf_self]
  have h := v2c_coreG3 (G := ↥(Λ ⊔ B)) (M := Q) hQ hsup (A4.isPGroup_subgroupOf_of_le hBH hB2)
    (fun b hb l hl => hBΛ _ hb _ hl) (isIrr_subgroupOf hΛH hV)
    ((v2c_isInv_subgroupOf hBH V).2 hVB) ((v2c_isInv_subgroupOf hΛH P₁).2 hP₁Λ)
    ((v2c_isInv_subgroupOf hBH P₁).2 hP₁B) ((v2c_isInv_subgroupOf hBH P₀).2 hP₀B) hdisj htop
    hVP hSP hS'P (isIrr_subgroupOf hΛH hS) (isIrr_subgroupOf hΛH hS')
    (v2c_iso_subgroupOf _ hiso) (v2c_iso_subgroupOf _ hiso') hVS hVSS'
  rwa [nB_subgroupOf hBH, nB_subgroupOf hBH] at h

end Restrict

end CFSG.Quasithin.Z391
