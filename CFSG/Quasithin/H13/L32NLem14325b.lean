module

public import CFSG.Quasithin.H13.L32NLem14332h
public import CFSG.Quasithin.H13.L32NLem1434
public import CFSG.Quasithin.H13.L32NThm14326

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14325

abbrev zL {G : Type} [Group G] (T L V : Subgroup G) : Subgroup G :=
  centerOf (L ⊔ T) ⊓ fsuU T V ⊓ quasithinOmegaOneCenter T

abbrev vH {G : Type} [Group G] (T L V : Subgroup G) : Subgroup G :=
  conjClosure (zL T L V) (l32nH T V)

structure Ctx14325 (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) : Prop where
  hyp : Hyp14310One G T L V
  lt : fsuV1 T V < centerOf (fsuU T V)
  plane : IsL32NPlane T V V₂
  setting : Setting1282One G T L V 3 (fsuV1 T V) V₂
  gP : g ∈ p128 T L V
  gN : g ∉ l32nH T V
  U2 : IsPGroup 2 ↥(fsuU T V)
  card_V1 : Nat.card ↥(fsuV1 T V) = 2
  T_le : T ≤ l32nH T V
  U_le : fsuU T V ≤ l32nH T V
  V_U : V ≤ fsuU T V
  zUg_le : CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nH T V
  zUg_ne : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥
  q_tilde : centralizerMod (fsuV1 T V) (l32nH T V) (fsuU T V) = pCoreOf 2 (l32nH T V)
  card_hatV : Nat.card ↥(D.hat V) = 4
  Z_ne : zL T L V ≠ ⊥
  red : IsTwoReducedIn (l32nH T V) (vH T L V)
  vH_le : vH T L V ≤ centerOf (fsuU T V)
  cent_le : Subgroup.centralizer (vH T L V : Set G) ≤ Subgroup.normalizer (L : Set G)
  HM : l32nH T V ⊓ Subgroup.normalizer (L : Set G) =
    l32nH T V ⊓ Subgroup.normalizer (V : Set G)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem zL_le_zU {T L V : Subgroup G} (hUT : fsuU T V ≤ T) : zL T L V ≤ centerOf (fsuU T V) := by
  rintro z ⟨⟨hzc, hzU⟩, -⟩
  refine ⟨hzU, ?_⟩
  exact Subgroup.centralizer_le (hUT.trans le_sup_right) hzc.2

theorem zL_ne_bot {T L V : Subgroup G} (hUT : fsuU T V ≤ T) (hT2 : IsPGroup 2 ↥T)
    (hne : centerOf (L ⊔ T) ⊓ fsuU T V ≠ ⊥) : zL T L V ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centerOf (L ⊔ T) ⊓ fsuU T V with hY
  have hY2 : IsPGroup 2 ↥Y := hT2.to_le (inf_le_right.trans hUT)
  obtain ⟨k, hk⟩ := hY2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.eq_bot_of_card_eq Y (by rw [hk, pow_zero]))
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have hy1 : (y : G) ≠ 1 := fun h => by
    have : y = 1 := Subtype.ext h
    rw [this, orderOf_one] at hy
    omega
  intro hb
  apply hy1
  have hmem : (y : G) ∈ zL T L V := by
    refine ⟨y.2, Subgroup.subset_closure ⟨⟨hUT y.2.2, ?_⟩, ?_⟩⟩
    · exact Subgroup.centralizer_le (le_sup_right : T ≤ L ⊔ T) y.2.1.2
    · have := pow_orderOf_eq_one y
      rw [hy] at this
      exact congrArg Subtype.val this
  rw [hb] at hmem
  exact hmem

theorem exists_ctx14325 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h12813 : Lemma12_8_13) {T L V : Subgroup G} (h : Hyp14310One G T L V)
    (hne : centerOf (L ⊔ T) ⊓ fsuU T V ≠ ⊥) :
    ∃ (V₂ : Subgroup G) (g : G) (D : HatModelU (fsuU T V)), Ctx14325 G T L V V₂ g D := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  have h1283 := lemma12_8_3 h12213
  have h1284 := lemma12_8_4 h1222 h37 h38 h39
  obtain ⟨V₂, g, hV₂, hgP, hgN⟩ := h.exists_plane_and_g h13322 hV (exist1282g h1222)
  have hs := h.setting1282One h13322 hV hV₂
  obtain ⟨D⟩ := hs.exists_hatModelU h1222 h12213
  obtain ⟨-, hV8, -, hV1, -⟩ := hV G T L V h.hyp h.fsu
  have hUT := h.fsuU_le h13322 hV h1283 h1284
  have hT2 : IsPGroup 2 ↥T := h.fsu.sylow.1
  have hU2 : IsPGroup 2 ↥(fsuU T V) := hT2.to_le hUT
  have hZne := zL_ne_bot hUT hT2 hne
  have hZzU := zL_le_zU (L := L) hUT
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hVZ := lemma12_8_8_three h1222 h12213 hs
  have hV1Z : fsuV1 T V ≤ centerOf (fsuU T V) := hVZ ▸ inf_le_right
  have hlt : fsuV1 T V < centerOf (fsuU T V) := by
    refine lt_of_le_of_ne hV1Z fun heq => hZne ?_
    obtain ⟨_, S⟩ := L14332.exists_setting h1332 h1334 h1222 h hV₂
    rw [eq_bot_iff, ← S.hZV]
    intro z hz
    have hzV1 : z ∈ fsuV1 T V := by rw [heq]; exact hZzU hz
    refine ⟨(inf_le_left : fsuV1 T V ≤ V) hzV1, ?_⟩
    exact Subgroup.centralizer_le (le_sup_left : L ≤ L ⊔ T) hz.1.1.2
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hTH : T ≤ l32nH T V := h.le_l32nH hV
  have hred : IsTwoReducedIn (l32nH T V) (vH T L V) :=
    isTwoReducedIn_conjClosure (l32nH T V) S (hS ▸ hTH) (h.charTwo_l32nH hV)
      (hS ▸ inf_le_right)
  have hvH : vH T L V ≤ centerOf (fsuU T V) :=
    conjClosure_le fun x hx z hz =>
      (Subgroup.mem_normalizer_iff.mp (L14332.l32nH_le_normalizer_zU hx) z).mp (hZzU hz)
  have hcent : Subgroup.centralizer (vH T L V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have hZ2 : IsPGroup 2 ↥(zL T L V) := hU2.to_le (inf_le_left.trans inf_le_right)
    obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge
      (L := Subgroup.normalizer (zL T L V : Set G)) ⟨zL T L V, hZne, hZ2, rfl⟩
    have hLTN : L ⊔ T ≤ Subgroup.normalizer (zL T L V : Set G) := by
      intro x hx
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro z hz
      exact (Subgroup.mem_centralizer_iff.mp hz.1.1.2 x hx).symm
    have hM'eq := (h13322 G T L h.hyp.h13 L h.hyp.h13.faithful).2.2.2 M' hM' (hLTN.trans hNM')
    refine le_trans ?_ (hM'eq ▸ hNM')
    exact (Subgroup.centralizer_le (le_conjClosure _ _)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hV1ne : fsuV1 T V ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV1
    omega
  have hHM := lemma1433Six_of_inputs h1332 h1334 h1222 G T L V h.hyp h.fsu (fsuV1 T V)
    (l32nH T V) inf_le_left hV1ne le_rfl
  have hzUg : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ := by
    intro hb
    apply (h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN).2.2.1 hlt
    intro x hx
    have hxH := L14332.conj_zU_le h12813 hs hgP hgN hx
    have hρ : D.ρ ⟨x, L14332.l32nH_le_normalizer_fsuU T V hxH⟩ = 1 := by
      have := L128A.HatU.rho_mem_img D hx (L14332.l32nH_le_normalizer_fsuU T V hxH)
      rw [hb, Subgroup.mem_bot] at this
      exact this
    exact (L14332.rho_eq_one_iff_mem hxH _).mp hρ
  have hhatV : Nat.card ↥(D.hat V) = 4 := by
    rw [L128A.HatU.card_hat D hVU]
    change (V ⊓ zU128 V (fsuV1 T V)).relIndex V = 4
    rw [hVZ]
    have := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := V)
    rw [inf_eq_left.mpr inf_le_left, hV1, hV8] at this
    omega
  exact ⟨V₂, g, D, ⟨h, hlt, hV₂, hs, hgP, hgN, hU2, hV1, hTH, h.fsuU_le_l32nH hV, hVU,
    L14332.conj_zU_le h12813 hs hgP hgN, hzUg,
    (h1284 G T L V 3 (h.hyp1281One h13322 hV) (fsuV1 T V) (l32nH T V) (h.isTSub_fsuV1 hV)
      (h.isHzOne_l32nH h13322 hV h1283)).2.2.2, hhatV, hZne, hred, hvH, hcent, hHM⟩⟩

end L14325

end CFSG.Quasithin.H13
