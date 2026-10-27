module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma1547Module
public import CFSG.Quasithin.Background.A1cA131
public import CFSG.LocalAnalysis.RankThreeEvenClassification.RankTransport
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.Quasithin.Background.I4Basic

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

namespace L1547

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def valHom {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := IntMod.val_one
  map_mul' := IntMod.val_mul

theorem valHom_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (valHom hV) := IntMod.val_injective

theorem valHom_mem {V : Subgroup G} (hV : IsElemAbelian 2 V) (w : IntMod V hV) :
    valHom hV w ∈ V := IntMod.val_mem w

theorem cjSub_map_valHom {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (g : Subgroup.normalizer (V : Set G)) (U : Subgroup (IntMod V hV)) :
    cjSub (g : G) (U.map (valHom hV)) = (U.map (convI hV g).toMonoidHom).map (valHom hV) := by
  ext x
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨convI hV g u, ⟨u, hu, rfl⟩, ?_⟩
    show (convI hV g u).val = g * u.val * (g : G)⁻¹
    rw [convI_apply_val]
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u.val, ⟨u, hu, rfl⟩, ?_⟩
    show g * u.val * (g : G)⁻¹ = (convI hV g u).val
    rw [convI_apply_val]

section Main

variable [Finite G]

theorem exists_eq_of_card_eq_two {Z : Subgroup G} (hZ2 : Nat.card Z = 2) :
    ∃ z ∈ Z, z ≠ 1 ∧ orderOf z = 2 ∧ ∀ x ∈ Z, x = 1 ∨ x = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hzZ⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 (by rw [hZ2])
  have hz2 : orderOf z = 2 := by rw [← hz, Subgroup.orderOf_mk]
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz2
    norm_num at hz2
  have hzp : Subgroup.zpowers z = Z := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzZ) ?_
    rw [hZ2, Nat.card_zpowers, hz2]
  refine ⟨z, hzZ, hz1, hz2, fun x hx => ?_⟩
  rw [← hzp] at hx
  exact I4.eq_one_or_eq_of_mem_zpowers hz2 hx

theorem mbar_structure (T : Sylow 2 G) {M : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hF : CharTwo M) (hsolv : Group.IsSolvable M) (hM2 : IsTwoLocal M) (hrank : evenRank G ≤ 2)
    (hZ2 : Nat.card (quasithinOmegaOneCenter (T : Subgroup G)) = 2)
    (hJ : ¬ thompsonJ (T : Subgroup G) ≤ Subgroup.centralizer (VZ (T : Subgroup G) M : Set G)) :
    (∀ m ∈ M, m ∈ Subgroup.centralizer (quasithinOmegaOneCenter (T : Subgroup G) : Set G) →
      ∃ c ∈ M ⊓ Subgroup.centralizer (VZ (T : Subgroup G) M : Set G),
        ∃ t ∈ (T : Subgroup G), m = c * t) ∧
    (Nat.card (VZ (T : Subgroup G) M) = 4 ∨
      ∃ V₁ V₂ : Subgroup G, V₁ ≤ VZ (T : Subgroup G) M ∧ V₂ ≤ VZ (T : Subgroup G) M ∧
        Nat.card V₁ = 4 ∧ Nat.card V₂ = 4 ∧ V₁ ⊓ V₂ = ⊥ ∧ V₁ ⊔ V₂ = VZ (T : Subgroup G) M ∧
        (∃ t ∈ (T : Subgroup G), cjSub t V₁ = V₂ ∧ cjSub t V₂ = V₁) ∧
        (∀ m ∈ M, (cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂) ∨ (cjSub m V₁ = V₂ ∧ cjSub m V₂ = V₁)) ∧
        (∀ m ∈ M, ∀ k : ℕ, Odd k →
          m ^ k ∈ Subgroup.centralizer (VZ (T : Subgroup G) M : Set G) →
          cjSub m V₁ = V₁ ∧ cjSub m V₂ = V₂) ∧
        8 ≤ ((T : Subgroup G) ⊓
          Subgroup.centralizer (VZ (T : Subgroup G) M : Set G)).relIndex (T : Subgroup G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Tg : Subgroup G := (T : Subgroup G) with hTg
  set V : Subgroup G := VZ Tg M with hVdef
  set Z : Subgroup G := quasithinOmegaOneCenter Tg with hZdef
  have hTsyl : IsSylowTwoOf Tg M := isSylowTwoOf_of_sylow T hTM
  obtain ⟨hU, hred, hcase, -⟩ := B2_16 hsolv hF hTsyl (V := V) rfl
  rcases hcase with ⟨hJ', -⟩ | ⟨-, I, hPsyl, hJeq, hcomm, hind, hnat, hspan, -, hcind, hperm⟩
  · exact absurd hJ' hJ
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVT : V ≤ Tg := (le_pCoreOf_of_isTwoReducedIn hred).trans (pCoreOf_le_of_isSylowTwoOf hTsyl)
  have hTN : Tg ≤ Subgroup.normalizer (V : Set G) := hTM.trans hMN
  obtain ⟨z, hzZ, hz1, -, hZ⟩ := exists_eq_of_card_eq_two hZ2
  have hzV : z ∈ V := le_conjClosure Z M hzZ
  set z₀ : IntMod V hU := IntMod.mk hU ⟨z, hzV⟩ with hz₀
  have hZC : Z ≤ Subgroup.centralizer (Tg : Set G) :=
    ((Subgroup.closure_le _).mpr fun x hx => hx.1 :
      Z ≤ Tg ⊓ Subgroup.centralizer (Tg : Set G)).trans inf_le_right
  have hfix : ∀ w : IntMod V hU, w ∈ fixV (autI hU Tg) ↔ w = 1 ∨ w = z₀ := by
    intro w
    rw [mem_fixV_autI hU hTN]
    constructor
    · intro hw
      have hwZ : w.val ∈ Z := Subgroup.subset_closure
        ⟨⟨hVT w.val_mem, hw⟩, hU.2 w.val w.val_mem⟩
      rcases hZ _ hwZ with h1 | h1
      · left
        exact IntMod.val_injective h1
      · right
        exact IntMod.val_injective h1
    · rintro (rfl | rfl)
      · exact (Subgroup.centralizer (Tg : Set G)).one_mem
      · exact hZC hzZ
  have hgen : ∀ U : Subgroup (IntMod V hU), (∀ g ∈ autI hU M, ∀ u ∈ U, g u ∈ U) → z₀ ∈ U →
      U = ⊤ := by
    intro U hUinv hz₀U
    refine eq_top_iff.mpr fun w _ => ?_
    have key : ∀ v (hv : v ∈ V), IntMod.mk hU ⟨v, hv⟩ ∈ U := by
      intro v hv
      induction hv using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨m, hm, y, hy, rfl⟩ := hx
        rcases hZ y hy with hy1 | hyz
        · subst hy1
          have : IntMod.mk hU ⟨m * 1 * m⁻¹, Subgroup.subset_closure ⟨m, hm, 1, Z.one_mem, rfl⟩⟩ =
              (1 : IntMod V hU) := IntMod.val_injective (by
                show m * 1 * m⁻¹ = (1 : IntMod V hU).val
                rw [IntMod.val_one]
                group)
          rw [this]
          exact U.one_mem
        · have hmN := hMN hm
          have : IntMod.mk hU ⟨m * y * m⁻¹, Subgroup.subset_closure ⟨m, hm, y, hy, rfl⟩⟩ =
              convI hU ⟨m, hmN⟩ z₀ := IntMod.val_injective (by
                rw [convI_apply_val]
                show m * y * m⁻¹ = m * z * m⁻¹
                rw [hyz])
          rw [this]
          exact hUinv _ (convI_mem_autI hU hm hmN) _ hz₀U
      | one => exact U.one_mem
      | mul x y hx hy ihx ihy =>
        have : IntMod.mk hU ⟨x * y, V.mul_mem hx hy⟩ =
            IntMod.mk hU ⟨x, hx⟩ * IntMod.mk hU ⟨y, hy⟩ := rfl
        rw [this]
        exact U.mul_mem ihx ihy
      | inv x hx ihx =>
        have : IntMod.mk hU ⟨x⁻¹, V.inv_mem hx⟩ = (IntMod.mk hU ⟨x, hx⟩)⁻¹ := rfl
        rw [this]
        exact U.inv_mem ihx
    exact key w.val w.val_mem
  have hJM : autI hU (thompsonJ Tg) ≤ autI hU (thompsonJ M) :=
    autI_mono hU (thompsonJ_le_thompsonJ_of_isSylowTwoOf hTsyl)
  have hne : I.Nonempty := by
    by_contra hI
    rw [Finset.not_nonempty_iff_eq_empty] at hI
    have hbot : autI hU (thompsonJ M) = ⊥ := by
      rw [hJeq, hI]
      simp
    apply hJ
    have := (autI_eq_bot_iff hU ((thompsonJ_le_self Tg).trans hTN)).mp
      (le_bot_iff.mp (hJM.trans hbot.le))
    exact this
  have d : ModData (autI hU M) (autI hU Tg) (autI hU (thompsonJ Tg)) I z₀ :=
    { exp2 := fun w => IntMod.sq_eq_one w
      SA := autI_mono hU hTM
      S2 := B2F.isPGroup_autI hU T.isPGroup' hTN
      PS := autI_mono hU (thompsonJ_le_self Tg)
      Psyl := hJeq ▸ hPsyl
      comm := hcomm
      ind := hind
      nat := hnat
      span := hJeq ▸ hspan
      cind := hcind
      perm := hperm
      z_ne := fun h1 => hz1 (congrArg IntMod.val h1)
      fix := hfix
      gen := hgen
      ne := hne }
  have hI2 : I.card ≤ 2 := by
    by_contra h3
    obtain ⟨Q, hQJ, hFQ, T', hT'2, hT'ne, hnc⟩ := d.exists_noncyclic (by omega)
    have hQM : Q ≤ autI hU M := hQJ.trans (hJeq ▸ autI_mono hU (thompsonJ_le_self M))
    set K : Subgroup G := preI hU M hMN Q with hKdef
    have hKM : K ≤ M := preI_le hU
    let φ₀ : K →* MulAut (IntMod V hU) := convHom hU K (hKM.trans hMN)
    have hφ₀ : ∀ k, φ₀ k ∈ Q := fun k => by
      obtain ⟨hkM, hk⟩ := (mem_preI hU).mp k.2
      simpa [φ₀, convHom_apply] using hk
    let φ : K →* Q := φ₀.codRestrict Q hφ₀
    have hφs : Function.Surjective φ := by
      rintro ⟨q, hq⟩
      obtain ⟨g, hgM, hgq⟩ := (mem_autI hU).mp (hQM hq)
      have hgK : (g : G) ∈ K := (mem_preI hU).mpr ⟨hgM, by
        rw [convHom_apply]
        convert hq⟩
      exact ⟨⟨g, hgK⟩, Subtype.ext (by simpa [φ, φ₀, convHom_apply] using hgq)⟩
    have hrankK : CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 2 := by
      rw [CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 3 Nat.prime_three K]
      exact (CFSG.RankThreeEvenClassification.Helpers.pRank_mono 3 Nat.prime_three hKM).trans
        ((CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
          (by norm_num) M hM2).trans hrank)
    exact hnc ((A1c.A131Concl_of_surjective (p := 3) (by norm_num) hFQ _ K φ hφs rfl
      hrankK).1 T' hT'2 hT'ne)
  have hSsyl : IsSylowTwoOf (autI hU Tg) (autI hU M) := B2F.isSylowTwoOf_autI hU hMN hTsyl
  refine ⟨?_, ?_⟩
  ·
    intro m hm hmZ
    have hmN := hMN hm
    have hgA : convI hU ⟨m, hmN⟩ ∈ autI hU M := convI_mem_autI hU hm hmN
    have hgz : convI hU ⟨m, hmN⟩ z₀ = z₀ := IntMod.val_injective (by
      rw [convI_apply_val]
      show m * z * m⁻¹ = z
      rw [(Subgroup.mem_centralizer_iff.mp hmZ z hzZ).symm, mul_inv_cancel_right])
    obtain ⟨t, htT, hgt⟩ := (mem_autI hU).mp (d.stabilizer_le hI2 hSsyl hgA hgz)
    refine ⟨m * (t : G)⁻¹, ⟨M.mul_mem hm (M.inv_mem (hTM htT)), ?_⟩, t, htT, by group⟩
    have : convI hU (⟨m, hmN⟩ * t⁻¹) = 1 := by rw [map_mul, map_inv, hgt, mul_inv_cancel]
    exact (convI_eq_one_iff hU _).mp this
  have hpos : 0 < I.card := Finset.card_pos.mpr hne
  rcases (show I.card = 1 ∨ I.card = 2 by omega) with hc | hc
  · left
    exact d.card_eq_four_of_card_one hc
  right
  obtain ⟨L₁, L₂, hne12, hI'⟩ := Finset.card_eq_two.mp hc
  have hI : ∀ L, L ∈ I ↔ L = L₁ ∨ L = L₂ := fun L => by
    rw [hI']
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hL₁I : L₁ ∈ I := (hI L₁).mpr (Or.inl rfl)
  have hL₂I : L₂ ∈ I := (hI L₂).mpr (Or.inr rfl)
  set V₁ : Subgroup G := (commV L₁).map (valHom hU) with hV₁
  set V₂ : Subgroup G := (commV L₂).map (valHom hU) with hV₂
  have hVi : ∀ U : Subgroup (IntMod V hU), U.map (valHom hU) ≤ V := by
    rintro U _ ⟨w, -, rfl⟩
    exact valHom_mem hU w
  have hconj : ∀ m (hm : m ∈ M) L (hL : L ∈ I),
      cjSub m ((commV L).map (valHom hU)) =
        (commV (B1.conjAut (convI hU ⟨m, hMN hm⟩) L)).map (valHom hU) := by
    intro m hm L hL
    have := cjSub_map_valHom hU ⟨m, hMN hm⟩ (commV L)
    rw [(hperm _ (convI_mem_autI hU hm (hMN hm)) L hL).2] at this
    exact this
  have hpair : ∀ g ∈ autI hU M,
      (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
        (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁) := by
    intro g hg
    rcases (hI _).mp (hperm g hg L₁ hL₁I).1 with h1 | h1
    · left
      refine ⟨h1, ?_⟩
      rcases (hI _).mp (hperm g hg L₂ hL₂I).1 with h2 | h2
      · exact absurd (ModData.conjAut_injective g (h1.trans h2.symm)) hne12
      · exact h2
    · right
      refine ⟨h1, ?_⟩
      rcases (hI _).mp (hperm g hg L₂ hL₂I).1 with h2 | h2
      · exact h2
      · exact absurd (ModData.conjAut_injective g (h1.trans h2.symm)) hne12
  obtain ⟨s, hs, hsL⟩ := d.exists_swap hne12 hI
  obtain ⟨t, htT, hts⟩ := (mem_autI hU).mp hs
  refine ⟨V₁, V₂, hVi _, hVi _, ?_, ?_, ?_, ?_, ⟨t, htT, ?_⟩, ?_, ?_, ?_⟩
  · rw [hV₁, Subgroup.card_map_of_injective (valHom_injective hU), d.card_commV hL₁I]
  · rw [hV₂, Subgroup.card_map_of_injective (valHom_injective hU), d.card_commV hL₂I]
  · rw [hV₁, hV₂, ← Subgroup.map_inf _ _ _ (valHom_injective hU), d.inf_eq_bot_of_pair hne12 hI,
      Subgroup.map_bot]
  · rw [hV₁, hV₂, ← Subgroup.map_sup, d.sup_eq_top_of_pair hI]
    refine le_antisymm (hVi ⊤) fun v hv => ?_
    exact ⟨IntMod.mk hU ⟨v, hv⟩, trivial, rfl⟩
  · have := hconj t (hTM htT) L₁ hL₁I
    rw [show (⟨(t : G), hMN (hTM htT)⟩ : Subgroup.normalizer (V : Set G)) = t from rfl, hts,
      hsL] at this
    rcases hpair s (d.SA hs) with h | h
    · exact absurd (hsL.symm.trans h.1) hne12.symm
    · refine ⟨this, ?_⟩
      have h2 := hconj t (hTM htT) L₂ hL₂I
      rw [show (⟨(t : G), hMN (hTM htT)⟩ : Subgroup.normalizer (V : Set G)) = t from rfl, hts,
        h.2] at h2
      exact h2
  · intro m hm
    have hc1 := hconj m hm L₁ hL₁I
    have hc2 := hconj m hm L₂ hL₂I
    rcases hpair _ (convI_mem_autI hU hm (hMN hm)) with h | h
    · left
      rw [h.1] at hc1
      rw [h.2] at hc2
      exact ⟨hc1, hc2⟩
    · right
      rw [h.1] at hc1
      rw [h.2] at hc2
      exact ⟨hc1, hc2⟩
  · intro m hm k hk hmk
    have hgk : (convI hU ⟨m, hMN hm⟩) ^ k = 1 := by
      rw [← map_pow]
      exact (convI_eq_one_iff hU _).mpr hmk
    have hg := convI_mem_autI hU hm (hMN hm)
    have hc1 := hconj m hm L₁ hL₁I
    have hc2 := hconj m hm L₂ hL₂I
    rw [d.conjAut_eq_of_odd hI2 hg hk hgk hL₁I] at hc1
    rw [d.conjAut_eq_of_odd hI2 hg hk hgk hL₂I] at hc2
    exact ⟨hc1, hc2⟩
  · rw [← card_autI_eq hU hTN]
    exact d.eight_le_card hne12 hI

end Main

end L1547

end CFSG.Quasithin.EmptyFaithfulMultiple
