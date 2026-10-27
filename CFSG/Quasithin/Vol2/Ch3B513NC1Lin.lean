module

public import CFSG.Quasithin.Vol2.Ch3B513NTc
public import CFSG.Quasithin.Background.G64Case1Pre
public import CFSG.Quasithin.Vol2.Ch3B513NC1

public section

namespace CFSG.Quasithin.B513N

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open (quasithinGenFitting)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem not_irrPlus_of_split {L : Subgroup (MulAut W)} {I J : Subgroup W}
    (hsup : I ⊔ J = commV L) (hinf : I ⊓ J = ⊥) (hI : ∀ l ∈ L, ∀ x ∈ I, l x ∈ I)
    (hJ : ∀ l ∈ L, ∀ y ∈ J, l y ∈ J) (hmI : ∃ l ∈ L, ∃ x ∈ I, l x ≠ x)
    (hmJ : ∃ l ∈ L, ∃ y ∈ J, l y ≠ y) : commV L ∉ IrrPlus L ⊤ := by
  rintro ⟨-, -, -, hsec⟩
  set F := XMod.fixed ↥L (commV L) with hF
  have hFU : F ≤ commV L := fun x hx => hx.1
  have hinvJ' : XMod.IsInv ↥L (I ⊔ F) := by
    intro a z hz
    obtain ⟨x, hx, f, hf, rfl⟩ := Subgroup.mem_sup.1 hz
    rw [smul_mul']
    refine Subgroup.mul_mem_sup (hI a a.2 x hx) ?_
    rw [hf.2 a]
    exact hf
  rcases hsec.2 (I ⊔ F) hinvJ' le_sup_right (sup_le (hsup ▸ le_sup_left) hFU) with h | h
  · obtain ⟨l, hl, x, hx, hlx⟩ := hmI
    have hxF : x ∈ F := h ▸ Subgroup.mem_sup_left hx
    exact hlx (hxF.2 ⟨l, hl⟩)
  · obtain ⟨l, hl, y, hy, hly⟩ := hmJ
    have hyU : y ∈ I ⊔ F := by rw [h, ← hsup]; exact Subgroup.mem_sup_right hy
    obtain ⟨a, ha, f, hf, rfl⟩ := Subgroup.mem_sup.1 hyU
    apply hly
    have hfl : l f = f := hf.2 ⟨l, hl⟩
    have h1 : l (a * f) * (a * f)⁻¹ = l a * a⁻¹ := by
      rw [map_mul, hfl]
      group
    have h2 : l a * a⁻¹ ∈ I ⊓ J := by
      refine ⟨I.mul_mem (hI l hl a ha) (I.inv_mem ha), ?_⟩
      rw [← h1]
      exact J.mul_mem (hJ l hl _ hy) (J.inv_mem hy)
    rw [hinf, Subgroup.mem_bot, ← h1, mul_inv_eq_one] at h2
    exact h2

omit [Finite W] in
theorem sup_fixV_eq_top_of_not_irrPlus {L : Subgroup (MulAut W)} (hP2 : B51Part2 L)
    (h : commV L ∉ IrrPlus L ⊤) : commV L ⊔ fixV L = ⊤ := by
  by_contra hne
  exact h (hP2.2 fun hd => hne hd.1).1

omit [Finite W] in
theorem cmHom_mem_map_of_sup {L : Subgroup (MulAut W)} (hsup : commV L ⊔ fixV L = ⊤)
    {a : MulAut W} (ha : a ∈ L) (w : W) : cmHom a w ∈ (commV L).map (cmHom a) := by
  have hw : w ∈ commV L ⊔ fixV L := by rw [hsup]; trivial
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hw
  refine ⟨u, hu, ?_⟩
  rw [map_mul, cmHom_apply a c, hc a ha, mul_inv_cancel, mul_one]

omit [Finite W] in
theorem card_iSup_le_prod [Finite W] : ∀ (k : ℕ) (T : Fin k → Subgroup W),
    Nat.card ↥(⨆ i, T i) ≤ ∏ i, Nat.card (T i)
  | 0, T => by simp
  | k + 1, T => by
    have hsplit : (⨆ i, T i) = T 0 ⊔ ⨆ i : Fin k, T i.succ := by
      apply le_antisymm
      · refine iSup_le fun i => ?_
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact le_sup_of_le_right (le_iSup (fun j : Fin k => T j.succ) j)
      · exact sup_le (le_iSup T 0) (iSup_le fun j => le_iSup T j.succ)
    rw [hsplit, Fin.prod_univ_succ]
    exact (card_sup_le _ _).trans (Nat.mul_le_mul_left _ (card_iSup_le_prod k _))

omit [Finite W] in
theorem exists_moved {L : Subgroup (MulAut W)} {M : FFModel} (hM : M.Faithful) {I : Subgroup W}
    {π : M.Gam →* ↥L} (hr : M.RealizesVia L I ⊥ π) {l : MulAut W} (hl : l ∈ L) (hl1 : l ≠ 1) :
    ∃ x ∈ I, l x ≠ x := by
  by_contra h
  push Not at h
  exact hl1 (FFC.faithful_on_of_realizes hM hr l hl h)

omit [Finite W] in
theorem tc_image_facts {m : ℕ} {L : Subgroup (MulAut W)}
    {π : ↥(StatedSL (m + 1) (ZMod 2)) →* ↥L} (hπ : Function.Injective π) :
    IsElemAbelian2 ((tcSub (m + 1)).map (L.subtype.comp π)) ∧
      2 ^ m ≤ Nat.card ((tcSub (m + 1)).map (L.subtype.comp π)) := by
  have hinj : Function.Injective (L.subtype.comp π) := L.subtype_injective.comp hπ
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨γ, hγ, rfl⟩ _ ⟨δ, hδ, rfl⟩
    rw [← map_mul, ← map_mul, tcSub_comm hγ hδ]
  · rintro _ ⟨γ, hγ, rfl⟩
    rw [← map_pow, pow_two, tcSub_mul_self hγ, map_one]
  · rw [Subgroup.card_map_of_injective hinj]
    exact card_tcSub_ge m

theorem c1iv_holds : C1iv := by
  intro W _ _ hW G hne hB53 h1 hiv
  have hP2 : B51Part2 (quasithinGenFitting G) := h1.2.1.2.1
  generalize quasithinGenFitting G = L at hiv hP2
  obtain ⟨hGL, n, hn, k, hk1, hkn, I, π, -, hind, hsup, hreal⟩ := hiv
  subst hGL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hJ : G = ffJ G := hB53.2.1
  have hπ : Function.Injective π :=
    FFC.injective_of_faithful_sec (FFModel.nat_faithful _) (hreal ⟨0, by omega⟩)
  have hsupU : (⨆ i, I i) = commV G := by rw [← hsup, bot_sup_eq]
  have hinvI : ∀ i, ∀ l ∈ G, ∀ x ∈ I i, l x ∈ I i := fun i l hl x hx =>
    (hreal i).2.2.2.1 ⟨l, hl⟩ x hx
  obtain ⟨l₀, hl₀, hl₀1⟩ : ∃ l ∈ G, l ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  rcases Nat.lt_or_ge k 2 with hk | hk
  ·
    have hk' : k = 1 := by omega
    subst hk'
    have hI0 : I 0 = commV G := by
      rw [← hsupU]
      exact le_antisymm (le_iSup I 0) (iSup_le fun i => by rw [Subsingleton.elim i 0])
    have hr0 := hreal 0
    rw [hI0] at hr0
    refine hasGood_of_realizes_small hW hne hJ le_rfl (FFModel.nat_faithful _) hr0 ?_
    rw [card_commV_of_nat hr0, Subgroup.card_bot, one_mul, Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    have h0 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    set i₀ : Fin k := ⟨0, by omega⟩ with hi₀
    obtain ⟨J, hJdef⟩ : ∃ J, J = ⨆ (j : Fin k) (_ : j ≠ i₀), I j := ⟨_, rfl⟩
    have hIJ : I i₀ ⊔ J = commV G := by
      rw [← hsupU, hJdef]
      apply le_antisymm (sup_le (le_iSup I i₀) (iSup₂_le fun j _ => le_iSup I j))
      refine iSup_le fun j => ?_
      by_cases hj : j = i₀
      · rw [hj]; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le j hj le_rfl)
    have hdisj : I i₀ ⊓ J = ⊥ := by
      have := hind i₀
      rwa [bot_sup_eq, ← hJdef] at this
    have hinvJ : ∀ l ∈ G, ∀ y ∈ J, l y ∈ J := by
      intro l hl y hy
      have hle : J ≤ J.comap l.toMonoidHom := by
        rw [hJdef]
        exact iSup₂_le fun j hj z hz =>
          (le_iSup₂ (f := fun (j : Fin k) (_ : j ≠ i₀) => I j) j hj) (hinvI j l hl z hz)
      exact hle hy
    have hnirr : commV G ∉ IrrPlus G ⊤ := by
      refine not_irrPlus_of_split hIJ hdisj (hinvI i₀) hinvJ ?_ ?_
      · obtain ⟨x, hx, hlx⟩ := exists_moved (FFModel.nat_faithful _) (hreal i₀) hl₀ hl₀1
        exact ⟨l₀, hl₀, x, hx, hlx⟩
      · obtain ⟨y, hy, hly⟩ := exists_moved (FFModel.nat_faithful _) (hreal ⟨1, by omega⟩) hl₀ hl₀1
        refine ⟨l₀, hl₀, y, ?_, hly⟩
        rw [hJdef]
        exact (le_iSup₂ (f := fun (j : Fin k) (_ : j ≠ i₀) => I j) ⟨1, by omega⟩ (Ne.symm h0)) hy
    have hsupW := sup_fixV_eq_top_of_not_irrPlus hP2 hnirr
    let π' : ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) →* ↥G := π
    obtain ⟨hAel, hAcard⟩ := tc_image_facts (π := π') hπ
    obtain ⟨A, hA⟩ : ∃ A, A = (tcSub (m + 1)).map (G.subtype.comp π') := ⟨_, rfl⟩
    rw [← hA] at hAel hAcard
    have hAG : A ≤ G := by rw [hA]; rintro _ ⟨γ, -, rfl⟩; exact (π' γ).2
    have hAne : A ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hAcard
      have : 2 ≤ 2 ^ m := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hcoord := fun i => FFModel.RealizesVia.coord rfl rfl (hreal i)
    choose β hβs hβk hβe using hcoord
    let S : Fin k → Subgroup W := fun i =>
      ((Subgroup.zpowers (Multiplicative.ofAdd (e0 (m + 1)))).comap (β i)).map (I i).subtype
    have hS : commV A ≤ ⨆ i, S i := by
      rw [hA]
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨a, ⟨γ, hγ, rfl⟩, w, rfl⟩
      set a' : MulAut W := G.subtype.comp π' γ with ha'
      have haG : a' ∈ G := (π' γ).2
      obtain ⟨u, hu, hwu⟩ := cmHom_mem_map_of_sup hsupW haG w
      show cmHom a' w ∈ ⨆ i, S i
      rw [← hwu]
      have hmap : (commV G).map (cmHom a') ≤ ⨆ i, S i := by
        rw [← hsupU, Subgroup.map_iSup]
        refine iSup_mono fun i => ?_
        rintro _ ⟨x, hx, rfl⟩
        have hxa : a' x ∈ I i := hinvI i a' haG x hx
        refine ⟨⟨cmHom a' x, (I i).mul_mem hxa ((I i).inv_mem hx)⟩, ?_, rfl⟩
        show β i ⟨cmHom a' x, _⟩ ∈ Subgroup.zpowers _
        have h1 : (⟨cmHom a' x, (I i).mul_mem hxa ((I i).inv_mem hx)⟩ : ↥(I i)) =
            ⟨a' x, hxa⟩ * (⟨x, hx⟩ : ↥(I i))⁻¹ := rfl
        have h3 : β i ⟨a' x, hxa⟩ =
            natAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (β i ⟨x, hx⟩) :=
          hβe i γ ⟨x, hx⟩ hxa
        rw [h1, map_mul, map_inv, h3]
        exact natAct_tc hγ _
      exact hmap ⟨u, hu, rfl⟩
    have hScard : ∀ i, Nat.card (S i) ≤ 2 := by
      intro i
      rw [Subgroup.card_map_of_injective (I i).subtype_injective]
      have hinj : Function.Injective (β i) := by
        rw [injective_iff_map_eq_one]
        intro x hx
        have := (hβk i x).1 hx
        rw [Subgroup.mem_bot] at this
        exact Subtype.ext this
      have h2 : (Multiplicative.ofAdd (e0 (m + 1))) ^ 2 = 1 := by
        rw [pow_two]
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_ofAdd, toAdd_one]
        funext j
        simp only [Pi.add_apply, Pi.zero_apply]
        exact CharTwo.add_self_eq_zero _
      calc Nat.card ↥((Subgroup.zpowers (Multiplicative.ofAdd (e0 (m + 1)))).comap (β i))
          ≤ Nat.card ↥(Subgroup.zpowers (Multiplicative.ofAdd (e0 (m + 1)))) := by
            refine Nat.card_le_card_of_injective (fun x => ⟨β i x, x.2⟩) ?_
            intro x y hxy
            exact Subtype.ext (hinj (congrArg Subtype.val hxy))
        _ ≤ 2 := by
            rw [Nat.card_zpowers]
            exact orderOf_le_of_pow_eq_one (by norm_num) h2
    refine ⟨A, hAG, hAne, hAel, Or.inl ?_⟩
    calc Nat.card (commV A) ≤ Nat.card ↥(⨆ i, S i) := Subgroup.card_le_of_le hS
      _ ≤ ∏ i, Nat.card (S i) := card_iSup_le_prod k S
      _ ≤ ∏ _i : Fin k, 2 := Finset.prod_le_prod fun i _ => hScard i
      _ = 2 ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Nat.card A := hAcard

theorem card_e0Perp (m : ℕ) : Nat.card (e0Perp (m + 1)) ≤ 2 ^ m := by
  classical
  let f : ↥(e0Perp (m + 1)) → (Fin m → ZMod 2) := fun y i =>
    Multiplicative.toAdd (y : Multiplicative (Fin (m + 1) → ZMod 2)) i.succ
  have hf : Function.Injective f := by
    intro y y' h
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    swap
    · exact congrFun h j
    have h0 : Multiplicative.toAdd (y : Multiplicative (Fin (m + 1) → ZMod 2)) 0 = 0 := y.2
    have h0' : Multiplicative.toAdd (y' : Multiplicative (Fin (m + 1) → ZMod 2)) 0 = 0 := y'.2
    rw [h0, h0']
  calc Nat.card (e0Perp (m + 1)) ≤ Nat.card (Fin m → ZMod 2) := Nat.card_le_card_of_injective f hf
    _ = 2 ^ m := by rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

theorem c1iii_holds : C1iii := by
  intro W _ _ hW G hne hB53 h1 k hiii
  have hP2 : B51Part2 (quasithinGenFitting G) := h1.2.1.2.1
  generalize quasithinGenFitting G = L at hiii hP2
  obtain ⟨hGL, hk, π, U₁, U₂, ⟨hsup12, hinf12⟩, hr1, hr2⟩ := hiii
  subst hGL
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hπ : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hr1
  have hinv1 : ∀ l ∈ G, ∀ x ∈ U₁, l x ∈ U₁ := fun l hl x hx => hr1.2.2.2.1 ⟨l, hl⟩ x hx
  have hinv2 : ∀ l ∈ G, ∀ x ∈ U₂, l x ∈ U₂ := fun l hl x hx => hr2.2.2.2.1 ⟨l, hl⟩ x hx
  obtain ⟨l₀, hl₀, hl₀1⟩ : ∃ l ∈ G, l ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  have hnirr : commV G ∉ IrrPlus G ⊤ := by
    refine not_irrPlus_of_split hsup12 hinf12 hinv1 hinv2 ?_ ?_
    · obtain ⟨x, hx, hlx⟩ := exists_moved (FFModel.nat_faithful _) hr1 hl₀ hl₀1
      exact ⟨l₀, hl₀, x, hx, hlx⟩
    · obtain ⟨y, hy, hly⟩ := exists_moved (G64.dualNat_faithful _) hr2 hl₀ hl₀1
      exact ⟨l₀, hl₀, y, hy, hly⟩
  have hsupW := sup_fixV_eq_top_of_not_irrPlus hP2 hnirr
  let π' : ↥(CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) →* ↥G := π
  obtain ⟨hAel, hAcard⟩ := tc_image_facts (π := π') hπ
  obtain ⟨A, hA⟩ : ∃ A, A = (tcSub (m + 1)).map (G.subtype.comp π') := ⟨_, rfl⟩
  rw [← hA] at hAel hAcard
  have hm : 1 ≤ m := by omega
  have hAG : A ≤ G := by rw [hA]; rintro _ ⟨γ, -, rfl⟩; exact (π' γ).2
  have hAne : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    have : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨β₁, -, hβ₁k, hβ₁e⟩ := FFModel.RealizesVia.coord rfl rfl hr1
  obtain ⟨β₂, -, hβ₂k, hβ₂e⟩ := FFModel.RealizesVia.coord rfl rfl hr2
  have hinj1 : Function.Injective β₁ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := (hβ₁k x).1 hx
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hinj2 : Function.Injective β₂ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have := (hβ₂k x).1 hx
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  set S₁ : Subgroup W :=
    ((Subgroup.zpowers (Multiplicative.ofAdd (e0 (m + 1)))).comap β₁).map U₁.subtype with hS₁
  set S₂ : Subgroup W := ((e0Perp (m + 1)).comap β₂).map U₂.subtype with hS₂
  have hS : commV A ≤ S₁ ⊔ S₂ := by
    rw [hA]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨a, ⟨γ, hγ, rfl⟩, w, rfl⟩
    set a' : MulAut W := G.subtype.comp π' γ with ha'
    have haG : a' ∈ G := (π' γ).2
    obtain ⟨u, hu, hwu⟩ := cmHom_mem_map_of_sup hsupW haG w
    show cmHom a' w ∈ S₁ ⊔ S₂
    rw [← hwu]
    rw [← hsup12] at hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [map_mul]
    refine Subgroup.mul_mem_sup ?_ ?_
    · have hxa : a' u₁ ∈ U₁ := hinv1 a' haG u₁ hu₁
      refine ⟨⟨cmHom a' u₁, U₁.mul_mem hxa (U₁.inv_mem hu₁)⟩, ?_, rfl⟩
      show β₁ ⟨cmHom a' u₁, _⟩ ∈ Subgroup.zpowers _
      have h1 : (⟨cmHom a' u₁, U₁.mul_mem hxa (U₁.inv_mem hu₁)⟩ : ↥U₁) =
          ⟨a' u₁, hxa⟩ * (⟨u₁, hu₁⟩ : ↥U₁)⁻¹ := rfl
      have h3 : β₁ ⟨a' u₁, hxa⟩ =
          natAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (β₁ ⟨u₁, hu₁⟩) :=
        hβ₁e γ ⟨u₁, hu₁⟩ hxa
      rw [h1, map_mul, map_inv, h3]
      exact natAct_tc hγ _
    · have hxa : a' u₂ ∈ U₂ := hinv2 a' haG u₂ hu₂
      refine ⟨⟨cmHom a' u₂, U₂.mul_mem hxa (U₂.inv_mem hu₂)⟩, ?_, rfl⟩
      show β₂ ⟨cmHom a' u₂, _⟩ ∈ e0Perp (m + 1)
      have h1 : (⟨cmHom a' u₂, U₂.mul_mem hxa (U₂.inv_mem hu₂)⟩ : ↥U₂) =
          ⟨a' u₂, hxa⟩ * (⟨u₂, hu₂⟩ : ↥U₂)⁻¹ := rfl
      have h3 : β₂ ⟨a' u₂, hxa⟩ =
          dualNatAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (β₂ ⟨u₂, hu₂⟩) :=
        hβ₂e γ ⟨u₂, hu₂⟩ hxa
      rw [h1, map_mul, map_inv, h3]
      exact dualNatAct_tc hγ _
  have hSfix : S₁ ⊔ S₂ ≤ fixV A := by
    refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ a ha
      rw [hA] at ha
      obtain ⟨γ, hγ, rfl⟩ := ha
      have hxa : (G.subtype.comp π' γ) (x : W) ∈ U₁ := hinv1 _ (π' γ).2 x x.2
      have h3 : β₁ ⟨(G.subtype.comp π' γ) (x : W), hxa⟩ =
          natAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (β₁ x) :=
        hβ₁e γ x hxa
      have hfix : natAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (β₁ x) = β₁ x := by
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (show β₁ x ∈ _ from hx)
        rw [← hj]
        have hmap : ∀ y z : Multiplicative (Fin (m + 1) → ZMod 2),
            natAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (y * z) =
              natAct _ γ y * natAct _ γ z := fun y z => by
          apply Multiplicative.toAdd.injective
          simp [natAct, Matrix.mulVec_add]
        have hpow : ∀ (j : ℤ), natAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ
            (Multiplicative.ofAdd (e0 (m + 1)) ^ j) = Multiplicative.ofAdd (e0 (m + 1)) ^ j := by
          intro j
          apply Multiplicative.toAdd.injective
          have := congrArg Multiplicative.toAdd (natAct_tc_e0 hγ)
          simp only [natAct, toAdd_ofAdd, toAdd_zpow] at this ⊢
          rw [Matrix.mulVec_smul, this]
        exact hpow j
      have h4 : β₁ ⟨(G.subtype.comp π' γ) (x : W), hxa⟩ = β₁ x := h3.trans hfix
      exact congrArg Subtype.val (hinj1 h4)
    · rintro _ ⟨x, hx, rfl⟩ a ha
      rw [hA] at ha
      obtain ⟨γ, hγ, rfl⟩ := ha
      have hxa : (G.subtype.comp π' γ) (x : W) ∈ U₂ := hinv2 _ (π' γ).2 x x.2
      have h3 : β₂ ⟨(G.subtype.comp π' γ) (x : W), hxa⟩ =
          dualNatAct (CFSG.Assembly.LowTwoRank.StatedSL (m + 1) (ZMod 2)) γ (β₂ x) :=
        hβ₂e γ x hxa
      have h4 : β₂ ⟨(G.subtype.comp π' γ) (x : W), hxa⟩ = β₂ x :=
        h3.trans (dualNatAct_tc_perp hγ hx)
      exact congrArg Subtype.val (hinj2 h4)
  refine ⟨A, hAG, hAne, hAel, Or.inr ⟨(hS.trans hSfix), ?_⟩⟩
  have hS₁card : Nat.card S₁ ≤ 2 := by
    rw [hS₁, Subgroup.card_map_of_injective U₁.subtype_injective]
    have h2 : (Multiplicative.ofAdd (e0 (m + 1))) ^ 2 = 1 := by
      rw [pow_two]
      apply Multiplicative.toAdd.injective
      simp only [toAdd_mul, toAdd_ofAdd, toAdd_one]
      funext j
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    calc Nat.card ↥((Subgroup.zpowers (Multiplicative.ofAdd (e0 (m + 1)))).comap β₁)
        ≤ Nat.card ↥(Subgroup.zpowers (Multiplicative.ofAdd (e0 (m + 1)))) := by
          refine Nat.card_le_card_of_injective (fun x => ⟨β₁ x, x.2⟩) ?_
          intro x y hxy
          exact Subtype.ext (hinj1 (congrArg Subtype.val hxy))
      _ ≤ 2 := by
          rw [Nat.card_zpowers]
          exact orderOf_le_of_pow_eq_one (by norm_num) h2
  have hS₂card : Nat.card S₂ ≤ 2 ^ m := by
    rw [hS₂, Subgroup.card_map_of_injective U₂.subtype_injective]
    refine le_trans ?_ (card_e0Perp m)
    refine Nat.card_le_card_of_injective (fun x => ⟨β₂ x, x.2⟩) ?_
    intro x y hxy
    exact Subtype.ext (hinj2 (congrArg Subtype.val hxy))
  calc Nat.card (commV A) ≤ Nat.card ↥(S₁ ⊔ S₂) := Subgroup.card_le_of_le hS
    _ ≤ Nat.card S₁ * Nat.card S₂ := card_sup_le _ _
    _ ≤ 2 * 2 ^ m := Nat.mul_le_mul hS₁card hS₂card
    _ = 2 ^ (m + 1) := by ring
    _ ≤ (2 ^ m) ^ 2 := by
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ ≤ Nat.card A ^ 2 := Nat.pow_le_pow_left hAcard 2

end CFSG.Quasithin.B513N
