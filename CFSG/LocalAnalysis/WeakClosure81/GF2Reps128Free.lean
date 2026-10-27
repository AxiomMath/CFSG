module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Lift

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mem_iSup₂_of_forall {g : MulAut V} {𝒥 : Set (Subgroup V)}
    (h : ∀ J ∈ 𝒥, ∀ w ∈ J, g w ∈ ⨆ J ∈ 𝒥, J) : ∀ w ∈ ⨆ J ∈ 𝒥, J, g w ∈ ⨆ J ∈ 𝒥, J := by
  intro w hw
  have hw' := hw
  rw [iSup_subtype'] at hw'
  refine Subgroup.iSup_induction (fun J : 𝒥 => (J : Subgroup V))
    (C := fun w => g w ∈ ⨆ J ∈ 𝒥, J) hw' ?_ ?_ ?_
  · intro J w hw
    exact h J J.2 w hw
  · rw [map_one]
    exact Subgroup.one_mem _
  · intro a b ha hb
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb

theorem iSup_inf_fixV_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V))
    (𝒮 : Set (Subgroup V))
    (h𝒮 : ∀ S ∈ 𝒮, StableUnder X S ∧ (∀ J : Subgroup V, StableUnder X J → J ≤ S → J = ⊥ ∨ J = S) ∧
      S ⊓ fixV X = ⊥) :
    (⨆ S ∈ 𝒮, S) ⊓ fixV X = ⊥ := by
  set T₀ := ⨆ S ∈ 𝒮, S with hT₀
  let P : Subgroup V → Prop := fun T => T ≤ T₀ ∧ StableUnder X T ∧ T ⊓ fixV X = ⊥
  have hP0 : P ⊥ := ⟨bot_le, fun _ _ _ hu => by rw [(Subgroup.mem_bot).mp hu, map_one]; exact one_mem _,
    bot_inf_eq _⟩
  have hstep : ∀ n : ℕ, ∀ T : Subgroup V, P T → rk ↥T₀ - rk ↥T = n → P T₀ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hT hn
      by_cases hTS : T = T₀
      · rw [← hTS]
        exact hT
      · obtain ⟨hTle, hTs, hT0⟩ := hT
        have hex : ∃ S ∈ 𝒮, ¬ S ≤ T := by
          by_contra hall
          push Not at hall
          exact hTS (le_antisymm hTle (iSup₂_le hall))
        obtain ⟨S, hS, hST⟩ := hex
        obtain ⟨hSs, hSirr, hS0⟩ := h𝒮 S hS
        have hTS' : T ⊓ S = ⊥ := by
          rcases hSirr (T ⊓ S) (stableUnder_inf hTs hSs) inf_le_right with h | h
          · exact h
          · exact absurd (h.ge.trans inf_le_left) hST
        have hSle : S ≤ T₀ := le_iSup₂_of_le S hS le_rfl
        have hfix : (T ⊔ S) ⊓ fixV X = ⊥ := by
          rw [eq_bot_iff]
          rintro f ⟨hf, hfX⟩
          obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hf
          have hab : ∀ x ∈ X, x a = a ∧ x b = b := by
            intro x hx
            have h1 : x a * x b = a * b := by rw [← map_mul]; exact hfX x hx
            have h2 : x a * a⁻¹ = b * (x b)⁻¹ := by
              calc x a * a⁻¹ = x a * a⁻¹ * (x b * (x b)⁻¹) := by rw [mul_inv_cancel, mul_one]
                _ = x a * x b * (a⁻¹ * (x b)⁻¹) := mul_mul_mul_comm _ _ _ _
                _ = a * b * (a⁻¹ * (x b)⁻¹) := by rw [h1]
                _ = a * a⁻¹ * (b * (x b)⁻¹) := mul_mul_mul_comm _ _ _ _
                _ = b * (x b)⁻¹ := by rw [mul_inv_cancel, one_mul]
            have h3 : x a * a⁻¹ ∈ T ⊓ S := by
              refine ⟨T.mul_mem (hTs x hx a ha) (T.inv_mem ha), ?_⟩
              rw [h2]
              exact S.mul_mem hb (S.inv_mem (hSs x hx b hb))
            rw [hTS', Subgroup.mem_bot, mul_inv_eq_one] at h3
            refine ⟨h3, ?_⟩
            rw [h3] at h1
            exact mul_left_cancel h1
          have ha0 : a ∈ T ⊓ fixV X := ⟨ha, fun x hx => (hab x hx).1⟩
          have hb0 : b ∈ S ⊓ fixV X := ⟨hb, fun x hx => (hab x hx).2⟩
          rw [hT0, Subgroup.mem_bot] at ha0
          rw [hS0, Subgroup.mem_bot] at hb0
          rw [ha0, hb0, mul_one]
          exact Subgroup.one_mem _
        have hrk := rk_sup_add_rk_inf T S
        rw [hTS', rk_bot] at hrk
        have hS0' : 0 < rk ↥S := by
          by_contra h0
          push Not at h0
          have hbot : S = ⊥ := (rk_eq_zero_iff hV).mp (Nat.le_zero.mp h0)
          exact hST (hbot ▸ bot_le)
        have hlt : rk ↥T < rk ↥(T ⊔ S) := by omega
        have hsS : rk ↥(T ⊔ S) ≤ rk ↥T₀ := rk_mono (sup_le hTle hSle)
        exact ih (rk ↥T₀ - rk ↥(T ⊔ S)) (by omega) (T ⊔ S)
          ⟨sup_le hTle hSle, stableUnder_sup hTs hSs, hfix⟩ rfl
  exact (hstep _ ⊥ hP0 rfl).2.2

theorem exists_isIrrOn_le {X : Subgroup (MulAut V)} {N A : Subgroup V} (hNA : N < A)
    (hA : StableUnder X A) (hN : StableUnder X N) : ∃ J : Subgroup V, J ≤ A ∧ IsIrrOn X J N := by
  classical
  have hex : ∃ n, ∃ J : Subgroup V, J ≤ A ∧ N < J ∧ StableUnder X J ∧ Nat.card J = n :=
    ⟨_, A, le_rfl, hNA, hA, rfl⟩
  obtain ⟨J, hJA, hNJ, hJs, hJn⟩ := Nat.find_spec hex
  refine ⟨J, hJA, hNJ, hJs, hN, fun J' hJ's hNJ' hJ'J => ?_⟩
  by_cases h : J' = N
  · exact Or.inl h
  · right
    have hlt : N < J' := lt_of_le_of_ne hNJ' (Ne.symm h)
    have hmin := Nat.find_min' hex ⟨J', hJ'J.trans hJA, hlt, hJ's, rfl⟩
    rw [← hJn] at hmin
    exact Subgroup.eq_of_le_of_card_ge hJ'J hmin

omit [Finite V] in
theorem map_isIrrOn {X : Subgroup (MulAut V)} {C A J : Subgroup V} {g : MulAut V}
    (hg : ∀ s ∈ X, g * s = s * g) (hgC : ∀ c ∈ C, g c = c) (hgA : ∀ a ∈ A, g a ∈ A)
    (hJ : J ≤ A ∧ IsIrrOn X J C) : J.map g.toMonoidHom ≤ A ∧ IsIrrOn X (J.map g.toMonoidHom) C := by
  obtain ⟨hJA, hCJ, hJs, hCs, hJirr⟩ := hJ
  have hg' : ∀ s ∈ X, g⁻¹ * s = s * g⁻¹ := by
    intro s hs
    have h := hg s hs
    calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * s) * g⁻¹ := by rw [← h]
      _ = s * g⁻¹ := by group
  have hstab : ∀ {f : MulAut V}, (∀ s ∈ X, f * s = s * f) → ∀ {B : Subgroup V},
      StableUnder X B → StableUnder X (B.map f.toMonoidHom) := by
    rintro f hf B hB s hs _ ⟨u, hu, rfl⟩
    refine ⟨s u, hB s hs u hu, ?_⟩
    have := congrArg (fun φ : MulAut V => φ u) (hf s hs)
    simpa only [MulAut.mul_apply, MulEquiv.coe_toMonoidHom] using this
  have hCg : C ≤ J.map g.toMonoidHom := fun c hc => ⟨c, hCJ.le hc, hgC c hc⟩
  have hback : ∀ B : Subgroup V, (B.map g⁻¹.toMonoidHom).map g.toMonoidHom = B := by
    intro B
    rw [Subgroup.map_map]
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, MulAut.apply_inv_self, exists_eq_right]
  refine ⟨?_, lt_of_le_of_ne hCg ?_, hstab hg hJs, hCs, fun J' hJ's hCJ' hJ'J => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact hgA u (hJA hu)
  · intro h
    apply hCJ.ne
    apply le_antisymm hCJ.le
    intro j hj
    have hgj : g j ∈ C := by rw [h]; exact ⟨j, hj, rfl⟩
    have := hgC _ hgj
    rwa [g.injective this] at hgj
  · have h1 : J'.map g⁻¹.toMonoidHom ≤ J := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hJ'J hu
      have hv' : v ∈ J := hv
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.inv_apply_self] using hv'
    have h2 : C ≤ J'.map g⁻¹.toMonoidHom := by
      intro c hc
      refine ⟨c, hCJ' hc, ?_⟩
      show g⁻¹ c = c
      nth_rewrite 1 [← hgC c hc]
      exact MulAut.inv_apply_self V g c
    rcases hJirr _ (hstab hg' hJ's) h2 h1 with h | h
    · left
      rw [← hback J', h]
      ext x
      constructor
      · rintro ⟨c, hc, rfl⟩
        have hc' : c ∈ C := hc
        simpa only [MulEquiv.coe_toMonoidHom, hgC c hc'] using hc'
      · intro hx
        exact ⟨x, hx, hgC x hx⟩
    · right
      rw [← hback J', h]

variable {W : Type} [CommGroup W] [Finite W]

theorem commSub_eq_self_of_not_le {Y L H : Subgroup (MulAut W)} (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) {U : Subgroup W} (hU : U ∈ irrSet H)
    {X : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hXU : ¬ commSub U X ≤ fixV H) :
    commSub U X = U := by
  obtain ⟨-, -, hHY, hn, -, -⟩ := h_facts hL hH
  obtain ⟨-, hXH, hXn⟩ := conjSet_facts hL hH hX
  have hirr := isIrrOn_sup_fixV hU
  have hCH : StableUnder H (fixV H) := stableUnder_fixV fun y hy h hh => hn y (hHY hy) h hh
  have hs : StableUnder H (commSub U X ⊔ fixV H) :=
    stableUnder_sup (stableUnder_commSub hXn hU.2.2.1) hCH
  have hle : commSub U X ⊔ fixV H ≤ U ⊔ fixV H :=
    sup_le_sup_right (commSub_le_of_invariant fun x hx u hu => hU.2.2.1 x (hXH hx) u hu) _
  rcases hirr.2.2.2 _ hs le_sup_right hle with h | h
  · exact absurd (le_sup_left.trans h.le) hXU
  · apply le_antisymm (commSub_le_of_invariant fun x hx u hu => hU.2.2.1 x (hXH hx) u hu)
    calc U = commSub U H := hU.1.symm
      _ = commSub (U ⊔ fixV H) H := (CFSG.Quasithin.commSub_sup_fixV le_rfl).symm
      _ = commSub (commSub U X ⊔ fixV H) H := by rw [h]
      _ = commSub (commSub U X) H := CFSG.Quasithin.commSub_sup_fixV le_rfl
      _ ≤ commSub U X := commSub_le_of_invariant (stableUnder_commSub hXn hU.2.2.1)

theorem inf_fixV_eq_bot_of_pair (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hH : H = ⨆ X ∈ conjSet L Y, X) {U : Subgroup W} (hU : U ∈ irrSet H)
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hX' : X' ∈ conjSet L Y) (hXX' : X ≠ X')
    (hXU : ¬ commSub U X ≤ fixV H) (hX'U : ¬ commSub U X' ≤ fixV H)
    (huniq : ∀ K ∈ conjSet L Y, K ≠ X → K ≠ X' → commSub U K ≤ fixV H) : U ⊓ fixV H = ⊥ := by
  obtain ⟨-, -, hHY, hn, -, -⟩ := h_facts hL hH
  obtain ⟨hXc, hXH, hXn⟩ := conjSet_facts hL hH hX
  obtain ⟨hX'c, hX'H, -⟩ := conjSet_facts hL hH hX'
  have hcomm : ∀ x ∈ X, ∀ s ∈ X', x * s = s * x :=
    B69.components_mul_comm_of_ne hX'c hXc (Ne.symm hXX')
  have hirr := isIrrOn_sup_fixV hU
  have hA' := sup_inf_trivMod_eq hL hH hU hX' hX'U
  have hCH : StableUnder H (fixV H) := stableUnder_fixV fun y hy h hh => hn y (hHY hy) h hh
  set C := fixV H with hC
  have hXC : ∀ x ∈ X, ∀ c ∈ C, x c = c := fun x hx c hc => hc x (hXH hx)
  have hUC : StableUnder H (U ⊔ C) := hirr.2.1
  have hUX : commSub U X = U := commSub_eq_self_of_not_le hL hH hU hX hXU
  set 𝒥 := {J : Subgroup W | J ≤ U ⊔ C ∧ IsIrrOn X' J C} with h𝒥
  have hX'UC : StableUnder X' (U ⊔ C) := fun s hs u hu => hUC s (hX'H hs) u hu
  have hX'C : StableUnder X' C := fun s hs c hc => by rw [hc s (hX'H hs)]; exact hc
  obtain ⟨J₀, hJ₀A, hJ₀⟩ := exists_isIrrOn_le hirr.1 hX'UC hX'C
  have hSig : (⨆ J ∈ 𝒥, J) = U ⊔ C := by
    have hmemSig : ∀ J ∈ 𝒥, J ≤ ⨆ J ∈ 𝒥, J := fun J hJ => le_iSup₂_of_le J hJ le_rfl
    have hle : (⨆ J ∈ 𝒥, J) ≤ U ⊔ C := iSup₂_le fun J hJ => hJ.1
    have hCSig : C ≤ ⨆ J ∈ 𝒥, J := hJ₀.1.le.trans (le_iSup₂_of_le J₀ ⟨hJ₀A, hJ₀⟩ le_rfl)
    have hKs : ∀ K ∈ conjSet L Y, ∀ k ∈ K, ∀ w ∈ ⨆ J ∈ 𝒥, J, k w ∈ ⨆ J ∈ 𝒥, J := by
      intro K hK k hk
      obtain ⟨-, hKH, -⟩ := conjSet_facts hL hH hK
      by_cases hKX' : K = X'
      · subst hKX'
        exact mem_iSup₂_of_forall fun J hJ w hw => hmemSig J hJ (hJ.2.2.1 k hk w hw)
      · by_cases hKX : K = X
        · subst hKX
          refine mem_iSup₂_of_forall fun J hJ w hw => ?_
          have hJk := map_isIrrOn (fun s hs => hcomm k hk s hs) (hXC k hk)
            (fun a ha => hUC k (hKH hk) a ha) hJ
          exact hmemSig _ hJk ⟨w, hw, rfl⟩
        · have hKU := huniq K hK hKX hKX'
          have hKC : C ≤ fixV K := fun c hc x hx => hc x (hKH hx)
          intro w hw
          have hwUC := hle hw
          have hkw : k w * w⁻¹ ∈ C := by
            have h1 : commSub (U ⊔ C) K ≤ C := by
              rw [CFSG.Quasithin.commSub_sup_fixV hKC]
              exact hKU
            exact h1 (Subgroup.subset_closure ⟨k, hk, w, hwUC, rfl⟩)
          have e : k w = (k w * w⁻¹) * w := (inv_mul_cancel_right (k w) w).symm
          rw [e]
          exact Subgroup.mul_mem _ (hCSig hkw) hw
    have hHSig : H ≤ stabSub (⨆ J ∈ 𝒥, J) := by
      rw [hH]
      refine iSup₂_le fun K hK => fun k hk => mem_stabSub_of_forall_mem (hKs K hK k hk)
    have hSigs : StableUnder H (⨆ J ∈ 𝒥, J) := fun h hh w hw => ((hHSig hh) w).mpr hw
    rcases hirr.2.2.2 _ hSigs hCSig hle with h | h
    · exfalso
      have h1 : J₀ ≤ C := (le_iSup₂_of_le J₀ ⟨hJ₀A, hJ₀⟩ le_rfl).trans h.le
      exact absurd h1 hJ₀.1.not_ge
    · exact h
  let δ : MulAut W → W →* W := fun x => x.toMonoidHom * (MonoidHom.id W)⁻¹
  have hδ : ∀ x w, δ x w = x w * w⁻¹ := fun x w => rfl
  have hδC : ∀ x ∈ X, ∀ c ∈ C, δ x c = 1 := fun x hx c hc => by
    rw [hδ, hXC x hx c hc, mul_inv_cancel]
  have hδs : ∀ x ∈ X, ∀ s ∈ X', ∀ w, δ x (s w) = s (δ x w) := by
    intro x hx s hs w
    have h1 : x (s w) = s (x w) := by
      rw [← MulAut.mul_apply, hcomm x hx s hs, MulAut.mul_apply]
    rw [hδ, hδ, map_mul, map_inv, h1]
  set 𝒮 := {S : Subgroup W | ∃ x ∈ X, ∃ J ∈ 𝒥, S = J.map (δ x)} with h𝒮
  have h𝒮 : ∀ S ∈ 𝒮, StableUnder X' S ∧
      (∀ J' : Subgroup W, StableUnder X' J' → J' ≤ S → J' = ⊥ ∨ J' = S) ∧ S ⊓ fixV X' = ⊥ := by
    rintro _ ⟨x, hx, J, ⟨hJA, hCJ, hJs, -, hJirr⟩, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro s hs _ ⟨w, hw, rfl⟩
      exact ⟨s w, hJs s hs w hw, hδs x hx s hs w⟩
    · intro J' hJ's hJ'S
      set P := J ⊓ J'.comap (δ x) with hP
      have hPs : StableUnder X' P := by
        intro s hs w hw
        refine ⟨hJs s hs w hw.1, ?_⟩
        show δ x (s w) ∈ J'
        rw [hδs x hx s hs]
        exact hJ's s hs _ hw.2
      have hCP : C ≤ P := fun c hc =>
        ⟨hCJ.le hc, show δ x c ∈ J' by rw [hδC x hx c hc]; exact J'.one_mem⟩
      rcases hJirr P hPs hCP inf_le_left with h | h
      · left
        rw [eq_bot_iff]
        intro v hv
        obtain ⟨w, hw, rfl⟩ := hJ'S hv
        have hwP : w ∈ P := ⟨hw, hv⟩
        rw [h] at hwP
        rw [Subgroup.mem_bot, hδC x hx w hwP]
      · right
        refine le_antisymm hJ'S ?_
        rintro _ ⟨w, hw, rfl⟩
        have hwP : w ∈ P := by rw [h]; exact hw
        exact hwP.2
    · rw [eq_bot_iff]
      rintro v ⟨⟨w, hw, rfl⟩, hv⟩
      set Q := J ⊓ (δ x).ker with hQ
      have hQs : StableUnder X' Q := by
        intro s hs u hu
        refine ⟨hJs s hs u hu.1, ?_⟩
        have hu2 : δ x u = 1 := hu.2
        show δ x (s u) = 1
        rw [hδs x hx s hs, hu2, map_one]
      have hCQ : C ≤ Q := fun c hc => ⟨hCJ.le hc, MonoidHom.mem_ker.mpr (hδC x hx c hc)⟩
      rcases hJirr Q hQs hCQ inf_le_left with h | h
      · have hwT : w ∈ (U ⊔ C) ⊓ trivMod X' C := by
          refine ⟨hJA hw, fun s hs => ?_⟩
          have hsw : s w * w⁻¹ ∈ Q := by
            refine ⟨J.mul_mem (hJs s hs w hw) (J.inv_mem hw), ?_⟩
            show δ x (s w * w⁻¹) = 1
            rw [map_mul, map_inv, hδs x hx s hs, hv s hs, mul_inv_cancel]
          rw [h] at hsw
          exact hsw
        rw [hA'] at hwT
        rw [Subgroup.mem_bot, hδC x hx w hwT]
      · have hwQ : w ∈ Q := by rw [h]; exact hw
        rw [Subgroup.mem_bot]
        exact MonoidHom.mem_ker.mp hwQ.2
  have hUS : U ≤ ⨆ S ∈ 𝒮, S := by
    rw [← hUX, commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, u, hu, rfl⟩
    have hu' : u ∈ ⨆ J ∈ 𝒥, J := by rw [hSig]; exact le_sup_left (α := Subgroup W) hu
    rw [iSup_subtype'] at hu'
    show δ x u ∈ ⨆ S ∈ 𝒮, S
    refine Subgroup.iSup_induction (fun J : 𝒥 => (J : Subgroup W))
      (C := fun u => δ x u ∈ ⨆ S ∈ 𝒮, S) hu' ?_ ?_ ?_
    · intro J w hw
      have hS : (J : Subgroup W).map (δ x) ≤ ⨆ S ∈ 𝒮, S :=
        le_iSup₂_of_le ((J : Subgroup W).map (δ x)) ⟨x, hx, J, J.2, rfl⟩ le_rfl
      exact hS ⟨w, hw, rfl⟩
    · rw [map_one]
      exact Subgroup.one_mem _
    · intro a b ha hb
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
  have hfree := iSup_inf_fixV_eq_bot hW X' 𝒮 h𝒮
  rw [eq_bot_iff, ← hfree]
  exact inf_le_inf hUS fun c hc s hs => hc s (hX'H hs)

end CFSG.LocalAnalysis.WeakClosure81
