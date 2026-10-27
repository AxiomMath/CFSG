module

public import CFSG.Quasithin.Background.E2SolvBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

variable {G : Type*} [Group G] [Finite G] {V : Subgroup G} {hV : IsElemAbelian 2 V}
  {H T M : Subgroup G} {𝓗 I : Finset (Subgroup (MulAut (IntMod V hV)))}

theorem Blocks.nonempty (B : Blocks hV H 𝓗 I) (hT : IsSylowTwoOf T H)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    I.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hI
  have h1 : autI hV (thompsonJ H) = ⊥ := by
    rw [B.eq, hI]
    simp
  rw [autI_eq_bot_iff hV ((thompsonJ_le_self H).trans hred.2.1)] at h1
  exact hJ ((thompsonJ_le_thompsonJ_of_isSylowTwoOf hT).trans h1)

theorem Blocks.card_eq_one_or_two (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) : I.card = 1 ∨ I.card = 2 := by
  have h1 := (B.nonempty h.isSylow hred hJ).card_pos
  have h2 := B.card_le_two h hsolv hSQT hred hJ
  omega

theorem Blocks.eq_singleton_or_pair (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    (∃ L₁ ∈ I, ∀ L ∈ I, L = L₁) ∨
      ∃ L₁ ∈ I, ∃ L₂ ∈ I, L₁ ≠ L₂ ∧ ∀ L ∈ I, L = L₁ ∨ L = L₂ := by
  classical
  rcases B.card_eq_one_or_two h hsolv hSQT hred hJ with h1 | h2
  · obtain ⟨L₁, hL₁⟩ := Finset.card_eq_one.mp h1
    refine Or.inl ⟨L₁, by rw [hL₁]; exact Finset.mem_singleton_self _, fun L hL => ?_⟩
    rw [hL₁] at hL
    exact Finset.mem_singleton.mp hL
  · obtain ⟨L₁, L₂, hne, hI⟩ := Finset.card_eq_two.mp h2
    refine Or.inr ⟨L₁, by rw [hI]; simp, L₂, by rw [hI]; simp, hne, fun L hL => ?_⟩
    rw [hI] at hL
    simpa using hL

omit [Finite G] in
theorem iSup_eq_of_singleton {α : Type*} [CompleteLattice α]
    {f : Subgroup (MulAut (IntMod V hV)) → α} {L₁ : Subgroup (MulAut (IntMod V hV))}
    (hL₁ : L₁ ∈ I) (hI : ∀ L ∈ I, L = L₁) :
    ⨆ L ∈ I, f L = f L₁ :=
  le_antisymm (iSup₂_le fun L hL => (hI L hL).symm ▸ le_rfl) (le_iSup₂_of_le L₁ hL₁ le_rfl)

omit [Finite G] in
theorem iSup_eq_of_pair {α : Type*} [CompleteLattice α] {f : Subgroup (MulAut (IntMod V hV)) → α}
    {L₁ L₂ : Subgroup (MulAut (IntMod V hV))} (hL₁ : L₁ ∈ I) (hL₂ : L₂ ∈ I)
    (hI : ∀ L ∈ I, L = L₁ ∨ L = L₂) : ⨆ L ∈ I, f L = f L₁ ⊔ f L₂ := by
  refine le_antisymm (iSup₂_le fun L hL => ?_)
    (sup_le (le_iSup₂_of_le L₁ hL₁ le_rfl) (le_iSup₂_of_le L₂ hL₂ le_rfl))
  rcases hI L hL with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem Blocks.fixV_twoResidual_inf (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commSub ⊤ L = ⊥ := by
  rw [eq_bot_iff]
  rintro w ⟨hwK, hwL⟩
  rw [Subgroup.mem_bot]
  rcases B.eq_singleton_or_pair h hsolv hSQT hred hJ with ⟨L₁, hL₁, hI⟩ |
    ⟨L₁, hL₁, L₂, hL₂, hne, hI⟩
  · rw [iSup_eq_of_singleton hL₁ hI] at hwL
    obtain ⟨f, hfL, hfK, hf3⟩ := B.exists_orderOf_eq_three hL₁
    exact B.eq_one_of_orderOf_eq_three hL₁ hfL hf3 hwL (hwK f hfK)
  · rw [iSup_eq_of_pair hL₁ hL₂ hI] at hwL
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Subgroup.mem_sup.mp hwL
    obtain ⟨f₁, hf₁L, hf₁K, hf₁3⟩ := B.exists_orderOf_eq_three hL₁
    obtain ⟨f₂, hf₂L, hf₂K, hf₂3⟩ := B.exists_orderOf_eq_three hL₂
    have h12 : f₁ w₂ = w₂ := B.hb.triv L₁ (B.sub hL₁) L₂ (B.sub hL₂) hne f₁ hf₁L w₂ hw₂
    have h21 : f₂ w₁ = w₁ := B.hb.triv L₂ (B.sub hL₂) L₁ (B.sub hL₁) (Ne.symm hne) f₂ hf₂L w₁ hw₁
    have e1 := hwK f₁ hf₁K
    rw [map_mul, h12, mul_left_inj] at e1
    have e2 := hwK f₂ hf₂K
    rw [map_mul, h21, mul_right_inj] at e2
    rw [B.eq_one_of_orderOf_eq_three hL₁ hf₁L hf₁3 hw₁ e1,
      B.eq_one_of_orderOf_eq_three hL₂ hf₂L hf₂3 hw₂ e2, one_mul]

theorem Blocks.fixV_twoResidual (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    fixV (autI hV (twoResidual H)) = fixV (autI hV (thompsonJ H)) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hKJ : autI hV (twoResidual H) ≤ autI hV (thompsonJ H) :=
    autI_mono hV (twoResidual_le_thompsonJ h hred hJ)
  refine le_antisymm (fun v hv => ?_) (B1.fixV_le_fixV hKJ)
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq] at hdec
  have hv' : v ∈ fixV (autI hV (thompsonJ H)) ⊔ ⨆ L ∈ I, commSub ⊤ L := by
    rw [hdec.1]
    exact Subgroup.mem_top v
  obtain ⟨c, hc, w, hw, rfl⟩ := Subgroup.mem_sup.mp hv'
  have hcK : c ∈ fixV (autI hV (twoResidual H)) := B1.fixV_le_fixV hKJ hc
  have hwK : w ∈ fixV (autI hV (twoResidual H)) := by
    have := (fixV (autI hV (twoResidual H))).mul_mem
      ((fixV (autI hV (twoResidual H))).inv_mem hcK) hv
    simpa using this
  have hw1 : w = 1 := by
    have hmem : w ∈ fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commSub ⊤ L := ⟨hwK, hw⟩
    rw [B.fixV_twoResidual_inf h hsolv hSQT hred hJ, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hw1, mul_one]
  exact hc

theorem Blocks.autI_thompsonJ_eq (B : Blocks hV H 𝓗 I) (hT : IsSylowTwoOf T H)
    (hsolv : Group.IsSolvable H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G))
    (t : Subgroup (MulAut (IntMod V hV)) → MulAut (IntMod V hV))
    (ht : ∀ L ∈ I, t L ∈ L ∧ t L ∈ autI hV (thompsonJ T) ∧ orderOf (t L) = 2) :
    autI hV (thompsonJ T) = ⨆ L ∈ I, Subgroup.zpowers (t L) := by
  classical
  obtain ⟨-, hsyl, -⟩ := structure_of_not_le hV hred hsolv hT hJ
  have hS : ∀ L ∈ I, Subgroup.zpowers (t L) ⊓ L = Subgroup.zpowers (t L) := fun L hL =>
    inf_eq_left.2 (Subgroup.zpowers_le.2 (ht L hL).1)
  have hsup : (⨆ L ∈ I, Subgroup.zpowers (t L)) = ⨆ L ∈ I, (Subgroup.zpowers (t L) ⊓ L) :=
    le_antisymm (iSup₂_le fun L hL => le_iSup₂_of_le L hL (hS L hL).ge)
      (iSup₂_le fun L hL => le_iSup₂_of_le L hL (hS L hL).le)
  have hle : (⨆ L ∈ I, Subgroup.zpowers (t L)) ≤ autI hV (thompsonJ T) :=
    iSup₂_le fun L hL => Subgroup.zpowers_le.2 (ht L hL).2.1
  have hcard1 : Nat.card ↥(⨆ L ∈ I, Subgroup.zpowers (t L)) = 2 ^ I.card := by
    rw [hsup, B.hb.card_biSup_eq_prod (fun L => Subgroup.zpowers (t L) ⊓ L)
      (fun L _ => inf_le_right) I B.sub]
    rw [Finset.prod_congr rfl (fun L hL => by
      rw [hS L hL, Nat.card_zpowers, (ht L hL).2.2])]
    simp
  have hcard6 : Nat.card ↥(autI hV (thompsonJ H)) = 6 ^ I.card := by
    rw [B.eq, B.hb.card_biSup_eq_prod (fun L => L) (fun L _ => le_rfl) I B.sub,
      Finset.prod_congr rfl (fun L hL => B.hb.card_eq L (B.sub hL))]
    simp
  have hcard2 : Nat.card ↥(autI hV (thompsonJ T)) = 2 ^ I.card := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hsyl.2.1
    have h := Subgroup.relIndex_mul_card (autI hV (thompsonJ T)) (autI hV (thompsonJ H))
    rw [inf_eq_left.2 hsyl.1, hcard6, hk] at h
    have hodd : ¬ 2 ∣ (autI hV (thompsonJ T)).relIndex (autI hV (thompsonJ H)) := hsyl.2.2
    have h6 : (6 : ℕ) ^ I.card = 2 ^ I.card * 3 ^ I.card := by rw [← mul_pow]; norm_num
    rw [h6] at h
    have h1 : 2 ^ k ∣ 2 ^ I.card := by
      have hd : 2 ^ k ∣ 2 ^ I.card * 3 ^ I.card := ⟨_, by rw [← h, mul_comm]⟩
      exact (Nat.Coprime.pow k I.card (by norm_num)).dvd_of_dvd_mul_right hd
    have h2 : 2 ^ I.card ∣ 2 ^ k := by
      have hd : 2 ^ I.card ∣ (autI hV (thompsonJ T)).relIndex (autI hV (thompsonJ H)) * 2 ^ k :=
        ⟨3 ^ I.card, h⟩
      exact (Nat.Coprime.pow_left I.card ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
        hodd)).dvd_of_dvd_mul_left hd
    rw [hk]
    exact Nat.dvd_antisymm h1 h2
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])).symm

theorem baum_fix (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H)
    {x : MulAut (IntMod V hV)} (hx : x ∈ autI hV (baum T)) {u : IntMod V hV}
    (hu : u ∈ fixV (autI hV (thompsonJ T))) : x u = u := by
  have hVT : V ≤ T := (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans
    (B6.pCoreOf_two_le_of_isSylowTwoOf hT)
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set G) :=
    (thompsonJ_le_self T).trans (hT.1.trans hred.2.1)
  obtain ⟨y, hy, rfl⟩ := (mem_autI hV).1 hx
  have hu2 := (mem_fixV_autI hV hJN u).1 hu
  have hE : u.val ∈ omegaOneCenterOf (thompsonJ T) :=
    inf_centralizer_thompsonJ_le hV hVT ⟨u.val_mem, hu2⟩
  have hcomm : (y : G) * u.val = u.val * y :=
    (Subgroup.mem_centralizer_iff.1 hy.2 u.val hE).symm
  refine IntMod.val_injective ?_
  rw [convI_apply_val, hcomm, mul_inv_cancel_right]

omit [Finite G] in
theorem eq_one_of_fix_sup {W : Type*} [CommGroup W] {y : MulAut W} {A B : Subgroup W}
    (hAB : A ⊔ B = ⊤) (hA : ∀ a ∈ A, y a = a) (hB : ∀ b ∈ B, y b = b) : y = 1 := by
  ext v
  have hv : v ∈ A ⊔ B := by rw [hAB]; exact Subgroup.mem_top v
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
  rw [map_mul, hA a ha, hB b hb, MulAut.one_apply]

theorem Blocks.exists_local (B : Blocks hV H 𝓗 I) {L : Subgroup (MulAut (IntMod V hV))}
    (hL : L ∈ I) {x : MulAut (IntMod V hV)} (hxH : x ∈ autI hV H) {t : MulAut (IntMod V hV)}
    (htL : t ∈ L) (ht2 : orderOf t = 2) {c : IntMod V hV} (hc : c ∈ commSub ⊤ L) (hc1 : c ≠ 1)
    (htc : t c = c) (hxc : x c = c) :
    ∃ l ∈ Subgroup.zpowers t, ∀ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L, x u = l u := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hxL : B1.conjAut x L = L := by
    by_contra hne
    have hmem := B.conjAut_mem hxH hL
    have hcx : c ∈ commSub ⊤ (B1.conjAut x L) := by
      rw [← IsTransvectionBlocks.map_commSub_conjAut L x]
      exact ⟨c, hc, hxc⟩
    have hbot := B.hb.commSub_inf_biSup_ne_eq_bot hW (B.sub hL)
    have : c ∈ commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
        ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) H' :=
      ⟨hc, le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV))) (_ : K ∈ 𝓗) =>
        ⨆ (_ : K ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) K) (B1.conjAut x L) (B.sub hmem)
        (le_iSup (fun _ : B1.conjAut x L ≠ L => commSub (⊤ : Subgroup (IntMod V hV))
          (B1.conjAut x L)) hne) hcx⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hc1 this
  have hstab : x ∈ stabSub (commSub (⊤ : Subgroup (IntMod V hV)) L) := by
    have hmap := IsTransvectionBlocks.map_commSub_conjAut L x
    rw [hxL] at hmap
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have : x u ∈ (commSub (⊤ : Subgroup (IntMod V hV)) L).map x.toMonoidHom := by
        rw [hmap]; exact hu
      obtain ⟨w, hw, hwu⟩ := this
      have : w = u := x.injective hwu
      rwa [← this]
    · intro hu
      rw [← hmap]
      exact ⟨u, hu, rfl⟩
  have htop := B.hb.autSub_eq_top L (B.sub hL)
  have hφ : resHom (commSub (⊤ : Subgroup (IntMod V hV)) L) ⟨x, hstab⟩ ∈
      autSub L (commSub (⊤ : Subgroup (IntMod V hV)) L) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨l, hlL, hlx⟩ := mem_autSub.mp hφ
  have hlu : ∀ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L, (l : MulAut (IntMod V hV)) u = x u := by
    intro u hu
    have := congrArg (fun ψ : MulAut (commSub (⊤ : Subgroup (IntMod V hV)) L) =>
      ((ψ ⟨u, hu⟩ : commSub (⊤ : Subgroup (IntMod V hV)) L) : IntMod V hV)) hlx
    simpa [resHom_apply] using this
  refine ⟨l, B.mem_zpowers_of_fix hL htL ht2 hc hc1 htc hlL ?_, fun u hu => (hlu u hu).symm⟩
  rw [hlu c hc, hxc]

theorem Blocks.autI_baum (B : Blocks hV H 𝓗 I) (h : MinParabolic H T M)
    (hsolv : Group.IsSolvable H) (hSQT : CFSG.Open.pRank 3 H ≤ 2) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    autI hV (baum T) = autI hV (thompsonJ T) := by
  classical
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hT := h.isSylow
  refine le_antisymm (fun x hx => ?_) (autI_mono hV (thompsonJ_le_baum T))
  have hxH : x ∈ autI hV H := autI_mono hV (inf_le_left.trans hT.1) hx
  have hex : ∀ L, ∃ t : MulAut (IntMod V hV), L ∈ I →
      t ∈ L ∧ t ∈ autI hV (thompsonJ T) ∧ orderOf t = 2 := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨t, htL, -, htJ, ht2⟩ := B.exists_orderOf_eq_two hred hT hL
      exact ⟨t, fun _ => ⟨htL, htJ, ht2⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose t ht using hex
  have hexc : ∀ L, ∃ c : IntMod V hV, L ∈ I → c ∈ commSub ⊤ L ∧ c ≠ 1 ∧ t L c = c := by
    intro L
    by_cases hL : L ∈ I
    · obtain ⟨c, hc, hc1, htc⟩ := B.exists_fix hL (ht L hL).1 (ht L hL).2.2
      exact ⟨c, fun _ => ⟨hc, hc1, htc⟩⟩
    · exact ⟨1, fun h' => absurd h' hL⟩
  choose c hc using hexc
  have hJTeq := B.autI_thompsonJ_eq hT hsolv hred hJ t (fun L hL => ht L hL)
  have hcfix : ∀ L ∈ I, c L ∈ fixV (autI hV (thompsonJ T)) := by
    intro L hL y hy
    rw [hJTeq] at hy
    have hle : (⨆ L' ∈ I, Subgroup.zpowers (t L')) ≤
        MulAction.stabilizer (MulAut (IntMod V hV)) (c L) := by
      refine iSup₂_le fun L' hL' => Subgroup.zpowers_le.2 ?_
      rw [MulAction.mem_stabilizer_iff]
      by_cases hLL : L' = L
      · subst hLL
        exact (hc L' hL).2.2
      · exact B.hb.triv L' (B.sub hL') L (B.sub hL) hLL (t L') (ht L' hL').1 (c L) (hc L hL).1
    exact hle hy
  have hxc : ∀ L ∈ I, x (c L) = c L := fun L hL => baum_fix hred hT hx (hcfix L hL)
  have hloc : ∀ L ∈ I, ∃ l ∈ Subgroup.zpowers (t L),
      ∀ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L, x u = l u := fun L hL =>
    B.exists_local hL hxH (ht L hL).1 (ht L hL).2.2 (hc L hL).1 (hc L hL).2.1 (hc L hL).2.2
      (hxc L hL)
  have hJTJH : autI hV (thompsonJ T) ≤ autI hV (thompsonJ H) :=
    autI_mono hV (thompsonJ_le_thompsonJ_of_isSylowTwoOf hT)
  have hxC : ∀ u ∈ fixV (autI hV (thompsonJ H)), x u = u := fun u hu =>
    baum_fix hred hT hx (B1.fixV_le_fixV hJTJH hu)
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq] at hdec
  have hJTle : ∀ L ∈ I, Subgroup.zpowers (t L) ≤ autI hV (thompsonJ T) := fun L hL =>
    Subgroup.zpowers_le.2 (ht L hL).2.1
  rcases B.eq_singleton_or_pair h hsolv hSQT hred hJ with ⟨L₁, hL₁, hI⟩ |
    ⟨L₁, hL₁, L₂, hL₂, hne, hI⟩
  · obtain ⟨l₁, hl₁, hxl₁⟩ := hloc L₁ hL₁
    have hl₁L : l₁ ∈ L₁ := Subgroup.zpowers_le.2 (ht L₁ hL₁).1 hl₁
    have hl₁J : l₁ ∈ autI hV (thompsonJ H) := B.le_thompsonJ hL₁ hl₁L
    rw [iSup_eq_of_singleton hL₁ hI] at hdec
    have hy : x * l₁⁻¹ = 1 := by
      refine eq_one_of_fix_sup hdec.1 (fun u hu => ?_) (fun u hu => ?_)
      · rw [MulAut.mul_apply, hu l₁⁻¹ ((autI hV (thompsonJ H)).inv_mem hl₁J), hxC u hu]
      · have hu' : l₁⁻¹ u ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₁ :=
          B.hb.stab L₁ (B.sub hL₁) _ (L₁.inv_mem hl₁L) u hu
        rw [MulAut.mul_apply, hxl₁ _ hu', ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    rw [mul_inv_eq_one] at hy
    rw [hy]
    exact hJTle L₁ hL₁ hl₁
  · obtain ⟨l₁, hl₁, hxl₁⟩ := hloc L₁ hL₁
    obtain ⟨l₂, hl₂, hxl₂⟩ := hloc L₂ hL₂
    have hl₁L : l₁ ∈ L₁ := Subgroup.zpowers_le.2 (ht L₁ hL₁).1 hl₁
    have hl₂L : l₂ ∈ L₂ := Subgroup.zpowers_le.2 (ht L₂ hL₂).1 hl₂
    have hl₁J : l₁ ∈ autI hV (thompsonJ H) := B.le_thompsonJ hL₁ hl₁L
    have hl₂J : l₂ ∈ autI hV (thompsonJ H) := B.le_thompsonJ hL₂ hl₂L
    rw [iSup_eq_of_pair hL₁ hL₂ hI] at hdec
    have htop : fixV (autI hV (thompsonJ H)) ⊔ (commSub ⊤ L₁ ⊔ commSub ⊤ L₂) = ⊤ := hdec.1
    have hy : x * (l₁ * l₂)⁻¹ = 1 := by
      refine eq_one_of_fix_sup htop (fun u hu => ?_) (fun u hu => ?_)
      · rw [MulAut.mul_apply, hu _ ((autI hV (thompsonJ H)).inv_mem
          ((autI hV (thompsonJ H)).mul_mem hl₁J hl₂J)), hxC u hu]
      · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
        have hu₁' : l₁⁻¹ u₁ ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₁ :=
          B.hb.stab L₁ (B.sub hL₁) _ (L₁.inv_mem hl₁L) u₁ hu₁
        have hu₂' : l₂⁻¹ u₂ ∈ commSub (⊤ : Subgroup (IntMod V hV)) L₂ :=
          B.hb.stab L₂ (B.sub hL₂) _ (L₂.inv_mem hl₂L) u₂ hu₂
        have h1 : (l₁ * l₂)⁻¹ u₁ = l₁⁻¹ u₁ := by
          rw [mul_inv_rev, MulAut.mul_apply, B.hb.triv L₂ (B.sub hL₂) L₁ (B.sub hL₁)
            (Ne.symm hne) _ (L₂.inv_mem hl₂L) _ hu₁']
        have h2 : (l₁ * l₂)⁻¹ u₂ = l₂⁻¹ u₂ := by
          rw [mul_inv_rev, MulAut.mul_apply, B.hb.triv L₁ (B.sub hL₁) L₂ (B.sub hL₂) hne _
            (L₁.inv_mem hl₁L) _ hu₂]
        rw [MulAut.mul_apply, map_mul, h1, h2, map_mul, hxl₁ _ hu₁', hxl₂ _ hu₂',
          ← MulAut.mul_apply, ← MulAut.mul_apply, mul_inv_cancel, mul_inv_cancel,
          MulAut.one_apply, MulAut.one_apply]
    rw [mul_inv_eq_one] at hy
    rw [hy]
    exact (autI hV (thompsonJ T)).mul_mem (hJTle L₁ hL₁ hl₁) (hJTle L₂ hL₂ hl₂)

end E2

open E2 in
theorem E2_3_one_of_isSolvable {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    twoResidual H ≤ thompsonJ H ∧
    ∃ I : Finset (Subgroup (MulAut (IntMod V hV))),
      (I.card = 1 ∨ I.card = 2) ∧
      autI hV (thompsonJ H) = ⨆ L ∈ I, L ∧
      (∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
      (∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥) ∧
      (∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L') ∧
      (∀ L ∈ I, ActsAsNaturalL2 L (commV L)) ∧
      fixV (autI hV (twoResidual H)) ⊔ ⨆ L ∈ I, commV L = ⊤ ∧
      fixV (autI hV (twoResidual H)) ⊓ ⨆ L ∈ I, commV L = ⊥ ∧
      (∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥) := by
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have h3 : CFSG.Open.pRank 3 H ≤ 2 := hSQT 3 Nat.prime_three (by norm_num)
  obtain ⟨𝓗, I, B⟩ := exists_blocks hV hred hsolv h.isSylow hJ
  have hdec := B.hb.decomp hW I B.sub
  rw [← B.eq, ← B.fixV_twoResidual h hsolv h3 hred hJ] at hdec
  refine ⟨twoResidual_le_thompsonJ h hred hJ, I, B.card_eq_one_or_two h hsolv h3 hred hJ, B.eq,
    fun L hL L' hL' hne a ha b hb => B.comm hL hL' hne ha hb, fun L hL => B.inf_biSup_ne hL,
    fun L hL L' hL' => B.transitive h hred hJ hL hL', fun L hL => ?_, ?_, ?_, fun L hL => ?_⟩
  · rw [commV_eq_commSub]
    exact actsAsNaturalL2_of_full hW (B.hb.card_comm L (B.sub hL)) (B.hb.le_stabSub (B.sub hL))
      (B.hb.inf_centSub (B.sub hL)) (B.hb.autSub_eq_top L (B.sub hL))
  · simp only [commV_eq_commSub]
    exact hdec.1
  · simp only [commV_eq_commSub]
    exact hdec.2
  · simp only [commV_eq_commSub]
    refine le_bot_iff.1 ?_
    calc commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' ≤
        commSub (⊤ : Subgroup (IntMod V hV)) L ⊓
          ⨆ L' ∈ 𝓗, ⨆ (_ : L' ≠ L), commSub (⊤ : Subgroup (IntMod V hV)) L' :=
          inf_le_inf_left _ (iSup₂_mono' fun L' hL' => ⟨L', B.sub hL', le_rfl⟩)
      _ = ⊥ := B.hb.commSub_inf_biSup_ne_eq_bot hW (B.sub hL)

open E2 in
theorem E2_3_two_sylow_of_isSolvable {G : Type*} [Group G] [Finite G] {H T M V : Subgroup G}
    (hV : IsElemAbelian 2 V) (h : MinParabolic H T M) (hsolv : Group.IsSolvable H)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2)
    (hred : IsTwoReducedIn H V) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    autI hV (baum T) = autI hV (thompsonJ T) ∧
      IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H)) := by
  have h3 : CFSG.Open.pRank 3 H ≤ 2 := hSQT 3 Nat.prime_three (by norm_num)
  obtain ⟨𝓗, I, B⟩ := exists_blocks hV hred hsolv h.isSylow hJ
  obtain ⟨-, hsyl, -⟩ := B2F.structure_of_not_le hV hred hsolv h.isSylow hJ
  exact ⟨B.autI_baum h hsolv h3 hred hJ, hsyl⟩

end CFSG.Quasithin
