module

public import CFSG.Quasithin.H13.AS91Sec3TwelveOneDefs
public import CFSG.Quasithin.H13.AS91Sec3Twelve
public import Certificates.Certificate89020

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

theorem repT_r121IdTab : RepT Native.r121IdTab 1 := by
  unfold RepT
  decide +kernel

theorem repT_mul {a b : Array ℕ} {σ τ : Equiv.Perm (Fin 24)} (ha : RepT a σ) (hb : RepT b τ) :
    RepT (Native.compose a b) (σ * τ) := by
  intro i
  have h1 : (Native.compose a b)[i.val]! = a[b[i.val]!]! := by
    simp [Native.compose]
  rw [h1, hb i]
  exact ha (τ i)

theorem eq_of_repT {t : Array ℕ} {σ τ : Equiv.Perm (Fin 24)} (hσ : RepT t σ) (hτ : RepT t τ) :
    σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).symm.trans (hτ i))

theorem one_shiftLeft_lt {j : ℕ} (hj : j < 6) : 1 <<< j < 64 := by
  have h : ∀ j < 6, 1 <<< j < 64 := by decide +kernel
  exact h j hj

theorem exists_clear_bit : ∀ s < 64, 0 < s → ∃ j < 6, s ^^^ (1 <<< j) < s := by
  decide +kernel

@[expose] def baseR0 : Subgroup S24 := Subgroup.closure (Set.range tPerm)

theorem tPerm_mem_baseR0 (j : Fin 6) : tPerm j ∈ baseR0 := Subgroup.subset_closure ⟨j, rfl⟩

section Rows


theorem sextsOfTrio_eq {p : ℕ} (hp : p < 3795) :
    Native.sextsOfTrio (Native.trioList ()) (Native.sextList ()) p =
      (Native.trioSexts ())[p]! := by
  rw [trioSexts_getElem hp]
  rfl

theorem mem_sextsOfTrio {p q : ℕ} (hp : p < 3795) :
    q ∈ Native.sextsOfTrio (Native.trioList ()) (Native.sextList ()) p ↔
      q < 1771 ∧ TrioIn (trioFin p) (sextFin q) := by
  rw [sextsOfTrio_eq hp]
  exact mem_trioSexts hp

end Rows

section Read


theorem r121Check_true : Native.r121Check () = true := Certificates.certificate89020

theorem groupCheck_spec :
    (∀ j < 6, Native.prodTab (1 <<< j) = Native.tTabs.getD j #[]) ∧
      Native.prodTab 0 = Native.r121IdTab ∧
      (∀ s < 64, ∀ s' < 64, Native.compose (Native.prodTab s) (Native.prodTab s') =
        Native.prodTab (s ^^^ s')) ∧
      (∀ s < 64, ∀ s' < s, ∃ i < 24, (Native.prodTab s)[i]! ≠ (Native.prodTab s')[i]!) := by
  have h := r121Check_true
  simp only [Native.r121Check, Native.groupCheck, Native.genTabCheck, Native.mulTabCheck,
    Native.distinctTabCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4⟩

theorem prodTab_gen (j : Fin 6) : Native.prodTab (1 <<< (j : ℕ)) = Native.tTabs.getD j #[] :=
  groupCheck_spec.1 j j.2

theorem prodTab_zero : Native.prodTab 0 = Native.r121IdTab := groupCheck_spec.2.1

theorem prodTab_mul {s s' : ℕ} (hs : s < 64) (hs' : s' < 64) :
    Native.compose (Native.prodTab s) (Native.prodTab s') = Native.prodTab (s ^^^ s') :=
  groupCheck_spec.2.2.1 s hs s' hs'

theorem prodTab_ne {s s' : ℕ} (hs : s < 64) (hss : s' < s) :
    ∃ i < 24, (Native.prodTab s)[i]! ≠ (Native.prodTab s')[i]! :=
  groupCheck_spec.2.2.2 s hs s' hss

theorem exists_prodTab_of_mem_baseR0 {σ : S24} (hσ : σ ∈ baseR0) :
    ∃ s < 64, RepT (Native.prodTab s) σ := by
  unfold baseR0 at hσ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1 <<< (j : ℕ), one_shiftLeft_lt j.2, ?_⟩
    rw [prodTab_gen]
    exact repT_tPerm j
  | one => exact ⟨0, by norm_num, by rw [prodTab_zero]; exact repT_r121IdTab⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨s, hs, hxs⟩ := ihx
    obtain ⟨s', hs', hys⟩ := ihy
    refine ⟨s ^^^ s', Nat.xor_lt_two_pow (n := 6) hs hs', ?_⟩
    rw [← prodTab_mul hs hs']
    exact repT_mul hxs hys
  | inv x _ ih =>
    obtain ⟨s, hs, hxs⟩ := ih
    refine ⟨s, hs, ?_⟩
    have h1 := repT_mul hxs hxs
    rw [prodTab_mul hs hs, Nat.xor_self, prodTab_zero] at h1
    have h2 : x * x = 1 := eq_of_repT h1 repT_r121IdTab
    rw [inv_eq_of_mul_eq_one_right h2]
    exact hxs

theorem exists_mem_baseR0_of_prodTab : ∀ s < 64, ∃ σ ∈ baseR0, RepT (Native.prodTab s) σ := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs
    rcases Nat.eq_zero_or_pos s with rfl | hpos
    · exact ⟨1, one_mem _, by rw [prodTab_zero]; exact repT_r121IdTab⟩
    · obtain ⟨j, hj, hlt⟩ := exists_clear_bit s hs hpos
      obtain ⟨σ, hσ, hσs⟩ := ih (s ^^^ (1 <<< j)) hlt (hlt.trans hs)
      refine ⟨σ * tPerm ⟨j, hj⟩, mul_mem hσ (tPerm_mem_baseR0 _), ?_⟩
      have h1 := repT_mul hσs (repT_tPerm ⟨j, hj⟩)
      have h2 : RepT (Native.compose (Native.prodTab (s ^^^ (1 <<< j)))
          (Native.prodTab (1 <<< j))) (σ * tPerm ⟨j, hj⟩) := by
        rw [prodTab_gen ⟨j, hj⟩]
        exact h1
      rw [prodTab_mul (hlt.trans hs) (one_shiftLeft_lt hj), Nat.xor_xor_cancel_right] at h2
      exact h2

theorem le_card_baseR0 : 64 ≤ Nat.card baseR0 := by
  have hex : ∀ s : Fin 64, ∃ σ : baseR0, RepT (Native.prodTab s) σ := fun s => by
    obtain ⟨σ, hσ, h⟩ := exists_mem_baseR0_of_prodTab s s.2
    exact ⟨⟨σ, hσ⟩, h⟩
  choose f hf using hex
  have key : ∀ s s' : Fin 64, s' < s → f s ≠ f s' := by
    intro s s' hlt h
    obtain ⟨i, hi, hne⟩ := prodTab_ne s.2 hlt
    apply hne
    have e1 := hf s ⟨i, hi⟩
    have e2 := hf s' ⟨i, hi⟩
    dsimp only at e1 e2
    rw [e1, e2, h]
  have hinj : Function.Injective f := by
    intro s s' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · exact key s' s h1 h.symm
    · exact key s s' h1 h
  simpa using Nat.card_le_card_of_injective f hinj

theorem fixCop_spec {p s : ℕ} (hp : p < 3795) (hs : s < 64)
    (hs0 : s ≠ 0) {y : S24} (hy : RepT (Native.prodTab s) y) (hO : ∀ O ∈ trioFin p, y • O = O)
    (hU : ∀ U, IsSextet U → TrioIn (trioFin p) U → y • U = U) :
    Coplanar (trioFin 0) (trioFin p) := by
  have h := r121Check_true
  simp only [Native.r121Check, Bool.and_eq_true] at h
  have h2 := h.2
  simp only [Native.fixCopCheck, List.all_eq_true, List.mem_range] at h2
  have hoct : ∀ o ∈ Native.octsT (Native.trioList ())[p]!, Native.img (Native.prodTab s) o = o := by
    intro o ho
    have ho' : o < 2 ^ 24 := octsT_lt hp o ho
    have h1 : maskFin o ∈ trioFin p := (maskFin_mem_trioFin hp ho').2 ho
    have h3 := (maskFin_img hy o).trans (hO _ h1)
    exact maskFin_inj (img_lt hy o) ho' h3
  have hsext : ∀ q ∈ Native.sextsOfTrio (Native.trioList ()) (Native.sextList ()) p,
      ∀ x ∈ (Native.sextList ())[q]!,
        Native.img (Native.prodTab s) x ∈ (Native.sextList ())[q]! := by
    intro q hq x hx
    obtain ⟨hq1, hq2⟩ := (mem_sextsOfTrio hp).1 hq
    have h3 : y • sextFin q = sextFin q := hU _ (isSextet_sextFin hq1) hq2
    have h4 : maskFin x ∈ sextFin q := mem_sextOfL.2 ⟨x, hx, rfl⟩
    have h5 : y • maskFin x ∈ y • sextFin q := Finset.smul_mem_smul_finset h4
    rw [h3, ← maskFin_img hy x] at h5
    obtain ⟨x', hx', hxx'⟩ := mem_sextOfL.1 h5
    have h6 := maskFin_inj (sextList_lt hq1 x' hx') (img_lt hy x) hxx'
    rwa [h6] at hx'
  have hmem : Native.prodTab s ∈ List.filter
      (fun t => (Native.octsT (Native.trioList ())[p]!).all fun o => Native.img t o == o)
      (List.map (fun s => Native.prodTab (s + 1)) (List.range 63)) := by
    rw [List.mem_filter]
    refine ⟨List.mem_map.2 ⟨s - 1, List.mem_range.2 (by omega), ?_⟩, ?_⟩
    · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hs0)]
    · simpa only [List.all_eq_true, beq_iff_eq] using hoct
  rcases Eq.mp (Bool.or_eq_true _ _) (h2 p hp) with h4 | h4
  · exfalso
    rw [List.isEmpty_iff] at h4
    rw [h4] at hmem
    exact List.not_mem_nil hmem
  · rw [List.all_eq_true] at h4
    rcases Eq.mp (Bool.or_eq_true _ _) (h4 _ hmem) with h6 | h6
    · exfalso
      have h7 : ((Native.sextsOfTrio (Native.trioList ()) (Native.sextList ()) p).all fun q =>
          (Native.sextList ())[q]!.all fun x =>
            (Native.sextList ())[q]!.contains (Native.img (Native.prodTab s) x)) = true := by
        simp only [List.all_eq_true, List.contains_eq_mem, decide_eq_true_eq]
        exact hsext
      rw [h7] at h6
      exact absurd h6 (by decide)
    · obtain ⟨q, hq0, hqp⟩ := List.any_eq_true.1 h6
      obtain ⟨hq1, hq2⟩ := (mem_sextsOfTrio (by norm_num : 0 < 3795)).1 hq0
      obtain ⟨-, hq3⟩ := (mem_sextsOfTrio hp).1 (List.contains_iff_mem.1 hqp)
      exact ⟨sextFin q, isSextet_sextFin hq1, hq2, hq3⟩

end Read

structure IsTrioNormal (l : Finset (Finset (Fin 24))) (N : Subgroup S24) : Prop where
  le : N ≤ M24g
  fix : ∀ σ ∈ N, σ • l = l
  norm : ∀ σ ∈ M24g, σ • l = l → ∀ n ∈ N, σ * n * σ⁻¹ ∈ N
  isPGroup : IsPGroup 2 N

@[expose] def StabTrio (l : Finset (Finset (Fin 24))) : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 l

theorem mem_StabTrio {l : Finset (Finset (Fin 24))} {σ : S24} :
    σ ∈ StabTrio l ↔ σ ∈ M24g ∧ σ • l = l := by
  rw [StabTrio, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]

theorem IsTrioNormal.le_stab {l : Finset (Finset (Fin 24))} {N : Subgroup S24}
    (hN : IsTrioNormal l N) : N ≤ StabTrio l :=
  fun n hn => mem_StabTrio.2 ⟨hN.le hn, hN.fix n hn⟩

theorem IsTrioNormal.norm_stab {l : Finset (Finset (Fin 24))} {N : Subgroup S24}
    (hN : IsTrioNormal l N) : ∀ s ∈ StabTrio l, ∀ n ∈ N, s * n * s⁻¹ ∈ N :=
  fun s hs n hn => hN.norm s (mem_StabTrio.1 hs).1 (mem_StabTrio.1 hs).2 n hn

theorem smul_mem_trio_of_mem_stab {l : Finset (Finset (Fin 24))} {s : S24} (hs : s ∈ StabTrio l)
    {x : Finset (Fin 24)} (hx : x ∈ l) : s • x ∈ l := by
  have h := Finset.smul_mem_smul_finset (a := s) hx
  rwa [(mem_StabTrio.1 hs).2] at h

section Octads


theorem exists_stab_smul_brick {y : Finset (Fin 24)} (hy : y ∈ trioFin 0) :
    ∃ s ∈ StabTrio0, s • maskFin 255 = y := by
  rw [trioFin_zero_eq] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl
  · exact ⟨1, StabTrio0.one_mem, one_smul _ _⟩
  · exact ⟨lPerm 0, lPerm_mem_stab 0, lPerm_zero_brick1⟩
  · exact ⟨lPerm 0 * lPerm 0, StabTrio0.mul_mem (lPerm_mem_stab 0) (lPerm_mem_stab 0), by
      rw [mul_smul, lPerm_zero_brick1, lPerm_zero_brick2]⟩

theorem IsTrioNormal.fix_octad {l : Finset (Finset (Fin 24))} {N : Subgroup S24}
    (hN : IsTrioNormal l N) (hl : IsTrio l) : ∀ n ∈ N, ∀ O ∈ l, n • O = O := by
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have hlg : g⁻¹ • trioFin 0 = l := by rw [← hgl, inv_smul_smul]
  have hX : ∀ s ∈ StabTrio l, ∀ x ∈ (l : Set (Finset (Fin 24))),
      s • x ∈ (l : Set (Finset (Fin 24))) := fun s hs x hx => smul_mem_trio_of_mem_stab hs hx
  have hb : g⁻¹ • maskFin 255 ∈ (l : Set (Finset (Fin 24))) := by
    rw [Finset.mem_coe, ← hlg]
    exact Finset.smul_mem_smul_finset (a := g⁻¹) (by rw [trioFin_zero_eq]; simp)
  have htrans : ∀ y ∈ (l : Set (Finset (Fin 24))), ∃ s ∈ StabTrio l,
      s • (g⁻¹ • maskFin 255) = y := by
    intro y hy
    have hgy : g • y ∈ trioFin 0 := by
      rw [← hgl]
      exact Finset.smul_mem_smul_finset (a := g) hy
    obtain ⟨s₀, hs₀, hs₀y⟩ := exists_stab_smul_brick hgy
    obtain ⟨hs₀M, hs₀l⟩ := mem_StabTrio0.1 hs₀
    refine ⟨g⁻¹ * s₀ * g, mem_StabTrio.2 ⟨?_, ?_⟩, ?_⟩
    · exact M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hg) hs₀M) hg
    · calc (g⁻¹ * s₀ * g) • l = g⁻¹ • s₀ • g • l := by simp only [mul_smul]
        _ = l := by rw [hgl, hs₀l, hlg]
    · calc (g⁻¹ * s₀ * g) • (g⁻¹ • maskFin 255) = g⁻¹ • s₀ • (g • g⁻¹ • maskFin 255) := by
            simp only [mul_smul]
        _ = g⁻¹ • s₀ • maskFin 255 := by rw [smul_inv_smul]
        _ = g⁻¹ • g • y := by rw [hs₀y]
        _ = y := inv_smul_smul g y
  have hodd : ¬ 2 ∣ (l : Set (Finset (Fin 24))).ncard := by
    rw [Set.ncard_coe_finset, hl.1]
    decide
  exact fix_of_odd_transitive hN.le_stab hN.isPGroup hN.norm_stab hX hb htrans hodd

end Octads

section Sextets


theorem ncard_sextets_of_trio {l : Finset (Finset (Fin 24))} (hl : IsTrio l) :
    {U | IsSextet U ∧ TrioIn l U}.ncard = 7 := by
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have hlg : g⁻¹ • trioFin 0 = l := by rw [← hgl, inv_smul_smul]
  have hset : {U | IsSextet U ∧ TrioIn l U} =
      (fun V => g⁻¹ • V) '' {U | IsSextet U ∧ TrioIn (trioFin 0) U} := by
    ext U
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hU, hUl⟩
      refine ⟨g • U, ⟨(isSextet_smul_iff hg).2 hU, ?_⟩, inv_smul_smul g U⟩
      have h := (trioIn_smul_iff g).2 hUl
      rwa [hgl] at h
    · rintro ⟨V, ⟨hV, hVl⟩, rfl⟩
      refine ⟨(isSextet_smul_iff (M24g.inv_mem hg)).2 hV, ?_⟩
      have h := (trioIn_smul_iff g⁻¹).2 hVl
      rwa [hlg] at h
  rw [hset, Set.ncard_image_of_injective _ (MulAction.injective g⁻¹)]
  exact ncard_sextets_base

theorem IsTrioNormal.fix_sextet {l : Finset (Finset (Fin 24))} {N : Subgroup S24}
    (hN : IsTrioNormal l N) (hl : IsTrio l) :
    ∀ n ∈ N, ∀ U, IsSextet U → TrioIn l U → n • U = U := by
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  have hlg : g⁻¹ • trioFin 0 = l := by rw [← hgl, inv_smul_smul]
  have hX : ∀ s ∈ StabTrio l, ∀ U ∈ {U | IsSextet U ∧ TrioIn l U},
      s • U ∈ {U | IsSextet U ∧ TrioIn l U} := by
    intro s hs U hU
    obtain ⟨hsM, hsl⟩ := mem_StabTrio.1 hs
    refine ⟨(isSextet_smul_iff hsM).2 hU.1, ?_⟩
    have h := (trioIn_smul_iff s).2 hU.2
    rwa [hsl] at h
  have hb : g⁻¹ • sextFin 0 ∈ {U | IsSextet U ∧ TrioIn l U} := by
    refine ⟨(isSextet_smul_iff (M24g.inv_mem hg)).2 (isSextet_sextFin zero_lt_1771), ?_⟩
    have h := (trioIn_smul_iff g⁻¹).2 trioIn_base
    rwa [hlg] at h
  have htrans : ∀ U ∈ {U | IsSextet U ∧ TrioIn l U},
      ∃ s ∈ StabTrio l, s • (g⁻¹ • sextFin 0) = U := by
    rintro U ⟨hU, hUl⟩
    obtain ⟨s, hs, hsl, hsU⟩ := exists_smul_fix_trio_sextet' hl hb.1 hU hb.2 hUl
    exact ⟨s, mem_StabTrio.2 ⟨hs, hsl⟩, hsU⟩
  have hodd : ¬ 2 ∣ {U | IsSextet U ∧ TrioIn l U}.ncard := by
    rw [ncard_sextets_of_trio hl]
    decide
  intro n hn U hU hUl
  exact fix_of_odd_transitive hN.le_stab hN.isPGroup hN.norm_stab hX hb htrans hodd n hn U
    ⟨hU, hUl⟩

end Sextets

theorem conj_smul_eq {α : Type*} [MulAction S24 α] {g x : S24} {z : α}
    (h : x • g⁻¹ • z = g⁻¹ • z) : (g * x * g⁻¹) • z = z := by
  rw [mul_smul, mul_smul, h, smul_inv_smul]

section Main


theorem mem_baseR0_of_fix {r : S24} (hr : r ∈ StabTrio0)
    (hfix : r • tupFin (Native.x0Code ()) = tupFin (Native.x0Code ())) : r ∈ baseR0 := by
  have hle : baseR0 ≤ StabTrio0 :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact tPerm_mem_stab j)
  have hfixR : ∀ n ∈ baseR0, n • tupFin (Native.x0Code ()) = tupFin (Native.x0Code ()) := by
    have h : baseR0 ≤ MulAction.stabilizer S24 (tupFin (Native.x0Code ())) :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact tPerm_fix_tup j)
    exact fun n hn => MulAction.mem_stabilizer_iff.1 (h hn)
  refine mem_of_fix_of_card_le hle hfixR ?_ r hr hfix
  rw [card_StabTrio0]
  calc 64512 = 1008 * 64 := by norm_num
    _ ≤ _ := Nat.mul_le_mul ncard_orbit_tup le_card_baseR0

theorem stmt3_12_1M24 : Stmt3_12_1M24 := by
  intro l k N₁ N₂ hl hk hN₁M hN₁fix hN₁norm hN₁p hN₂M hN₂fix hN₂norm hN₂p hne
  obtain ⟨r, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hr₁ : (r : S24) ∈ N₁ := (Subgroup.mem_inf.1 r.2).1
  have hr₂ : (r : S24) ∈ N₂ := (Subgroup.mem_inf.1 r.2).2
  have hx1 : (r : S24) ≠ 1 := fun h => hr1 (Subtype.ext h)
  have hOl := IsTrioNormal.fix_octad ⟨hN₁M, hN₁fix, hN₁norm, hN₁p⟩ hl (r : S24) hr₁
  have hUl := IsTrioNormal.fix_sextet ⟨hN₁M, hN₁fix, hN₁norm, hN₁p⟩ hl (r : S24) hr₁
  have hOk := IsTrioNormal.fix_octad ⟨hN₂M, hN₂fix, hN₂norm, hN₂p⟩ hk (r : S24) hr₂
  have hUk := IsTrioNormal.fix_sextet ⟨hN₂M, hN₂fix, hN₂norm, hN₂p⟩ hk (r : S24) hr₂
  have hxM : (r : S24) ∈ M24g := hN₁M hr₁
  have hxl : (r : S24) • l = l := hN₁fix _ hr₁
  generalize (r : S24) = x at hx1 hOl hUl hOk hUk hxM hxl
  obtain ⟨g, hg, hgl⟩ := trio_transitive hl
  obtain ⟨p, hp, hpk⟩ := (isTrio_iff (g • k)).1 ((isTrio_smul_iff hg).2 hk)
  have hlg : g⁻¹ • trioFin 0 = l := by rw [← hgl, inv_smul_smul]
  have hkg : g⁻¹ • trioFin p = k := by rw [hpk, inv_smul_smul]
  have hmem0 : ∀ {O : Finset (Fin 24)}, O ∈ trioFin 0 → g⁻¹ • O ∈ l := by
    intro O hO
    have h := Finset.smul_mem_smul_finset (a := g⁻¹) hO
    rwa [hlg] at h
  have hmemp : ∀ {O : Finset (Fin 24)}, O ∈ trioFin p → g⁻¹ • O ∈ k := by
    intro O hO
    have h := Finset.smul_mem_smul_finset (a := g⁻¹) hO
    rwa [hkg] at h
  have hyM : g * x * g⁻¹ ∈ M24g := M24g.mul_mem (M24g.mul_mem hg hxM) (M24g.inv_mem hg)
  have hyl : (g * x * g⁻¹) • trioFin 0 = trioFin 0 :=
    conj_smul_eq (by rw [hlg]; exact hxl)
  have hy1 : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hx1
    have e : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [e, h]
    group
  have fixO0 : ∀ O ∈ trioFin 0, (g * x * g⁻¹) • O = O := fun O hO => conj_smul_eq (hOl _ (hmem0 hO))
  have fixU0 : ∀ U, IsSextet U → TrioIn (trioFin 0) U → (g * x * g⁻¹) • U = U := by
    intro U hU hUt
    refine conj_smul_eq (hUl _ ((isSextet_smul_iff (M24g.inv_mem hg)).2 hU) ?_)
    have h := (trioIn_smul_iff g⁻¹).2 hUt
    rwa [hlg] at h
  have fixOP : ∀ O ∈ trioFin p, (g * x * g⁻¹) • O = O := fun O hO => conj_smul_eq (hOk _ (hmemp hO))
  have fixUP : ∀ U, IsSextet U → TrioIn (trioFin p) U → (g * x * g⁻¹) • U = U := by
    intro U hU hUt
    refine conj_smul_eq (hUk _ ((isSextet_smul_iff (M24g.inv_mem hg)).2 hU) ?_)
    have h := (trioIn_smul_iff g⁻¹).2 hUt
    rwa [hkg] at h
  have hyx0 : (g * x * g⁻¹) • tupFin (Native.x0Code ()) = tupFin (Native.x0Code ()) := by
    rw [tupFin_x0]
    simp only [Prod.smul_mk, Prod.mk.injEq]
    refine ⟨fixO0 _ (octIdx_brick 255 (Or.inl rfl)).2, fixO0 _ (octIdx_brick 65280 (Or.inr rfl)).2,
      ?_, ?_, ?_⟩
    · exact fixU0 _ (sextIdx_x0 (by simp)).2.1 (sextIdx_x0 (by simp)).2.2
    · exact fixU0 _ (sextIdx_x0 (by simp)).2.1 (sextIdx_x0 (by simp)).2.2
    · exact fixU0 _ (sextIdx_x0 (by simp)).2.1 (sextIdx_x0 (by simp)).2.2
  have hyR : g * x * g⁻¹ ∈ baseR0 := mem_baseR0_of_fix (mem_StabTrio0.2 ⟨hyM, hyl⟩) hyx0
  obtain ⟨s, hs, hys⟩ := exists_prodTab_of_mem_baseR0 hyR
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [prodTab_zero] at hys
    exact hy1 (eq_of_repT hys repT_r121IdTab)
  have hcop := fixCop_spec hp hs hs0 hys fixOP fixUP
  have hcop' : Coplanar (g • l) (g • k) := by
    rw [hgl, ← hpk]
    exact hcop
  exact (coplanar_smul_iff hg).1 hcop'

end Main

end CFSG.Quasithin.H13.AS91.M24G
