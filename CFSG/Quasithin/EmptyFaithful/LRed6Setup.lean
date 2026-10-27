module

public import CFSG.Quasithin.EmptyFaithful.LRed6ModLemma
public import CFSG.Quasithin.EmptyFaithful.LRed6Gen
public import CFSG.Quasithin.EmptyFaithful.LRed6Grp
import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace LRed6


theorem isPerfect_statedSL_three_two : Group.IsPerfect ↥(CFSG.Open.StatedSL 3 (ZMod 2)) :=
  CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) (ZMod 2)

section Index

variable {D X : Type*} [Group D] [Finite D] [Group X] (ρ : D →* X)

omit [Finite D] in
theorem card_map_top_eq {N : Subgroup D} {k : ℕ} (hρ : Function.Injective ρ) (hN : N.index = 2 ^ k) :
    Nat.card ↥((⊤ : Subgroup D).map ρ) = 2 ^ k * Nat.card ↥(N.map ρ) := by
  rw [Subgroup.card_map_of_injective hρ, Subgroup.card_map_of_injective hρ, Subgroup.card_top,
    ← hN, Subgroup.index_mul_card N]

theorem card_map_sylow {S : Subgroup D} (hρ : Function.Injective ρ) (hS : IsPGroup 2 ↥S)
    (hodd : ¬ 2 ∣ S.index) :
    Nat.card ↥(S.map ρ) = 2 ^ padicValNat 2 (Nat.card ↥((⊤ : Subgroup D).map ρ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hS.exists_card_eq
  rw [Subgroup.card_map_of_injective hρ, Subgroup.card_map_of_injective hρ, Subgroup.card_top,
    ← Subgroup.index_mul_card S, hj, padicValNat.mul Subgroup.index_ne_zero_of_finite (by positivity),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hodd, zero_add]

end Index

theorem inspectB51Rem153_of_b56
    (h113 : StageLemma14113) (h56 : AsB56) (hG2 : G2FixBound) :
    InspectB51Rem153 := by
  intro G _ _ T Mc M V₁ V₂ E t s conf hconc hlist hS3 hO2 hnp hYFX hQV hcomm hG1N hQ1
  obtain ⟨c, r45, r46, r49, L, r66, r67, gl, r68⟩ := conf
  classical
  set G₀ := G0_153 T Mc M E s with hG₀
  have hV0 : IsElemAbelian 2 (V0_153 T Mc M E s) := isElemAbelian_V0 c r68
  have hIN : G₀ ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := V0_normal
  have hVI : V0_153 T Mc M E s ≤ G₀ := V0_le_G0 r68
  set Qb : Subgroup ↥G₀ := CFSG.pPrimeCore 3 ↥G₀ with hQb
  have hQ : Qb = (G₀ ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)).subgroupOf G₀ :=
    pPrimeCore_G0_eq c r67 r68
  have hA : IsGoldschmidtAmalgam (barQ G₀ Qb (G1_153 T Mc M E s)) (barQ G₀ Qb (G2_153 T E)) := by
    rcases r68.triple.goldschmidt_mod_pPrimeCore with ⟨-, hA, -⟩ | ⟨-, -, -, -, hcyc⟩
    · exact hA
    · exfalso
      apply hcyc
      have hpc : Open.pCore 2 ↥G₀ = CFSG.pPrimeCore 3 ↥G₀ :=
        Subgroup.map_injective G₀.subtype_injective r68.pCore_eq
      have hbot : (CFSG.pPrimeCore 3 ↥G₀).map (QuotientGroup.mk' (Open.pCore 2 ↥G₀)) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', hpc]
      rw [hbot]
      infer_instance
  have hD : Open.pCore 2 (↥G₀ ⧸ Qb) = ⊥ := hA.pCore_eq_bot
  have hSQ : SQTKGroup ↥G₀ := sqtkGroup_G0 c r68
  set ρ := rhoOf hV0 hIN Qb hQ with hρdef
  have hρ : Function.Injective ρ := rhoOf_injective hV0 hIN Qb hQ
  have hJle : thompsonJ G₀ ≤ G₀ := B6.thompsonJ_le G₀
  have hJN : thompsonJ G₀ ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hJle.trans hIN
  have hB53 : B53Hyp (autI hV0 (thompsonJ G₀)) :=
    b53Hyp_autI_thompsonJ hV0 hIN hVI Qb hQ hD (sqtkGroup_of_le hSQ hJle)
  have hmapN : (barQ G₀ Qb (thompsonJ G₀)).map ρ = autI hV0 (thompsonJ G₀) :=
    map_rhoOf_barQ hV0 hIN Qb hQ hJle
  have hXI : XE153 E ≤ G₀ := (le_sup_left : XE153 E ≤ G2_153 T E).trans le_sup_right
  have hXEJ := XE_le_thompsonJ c L r66 r67 gl r68
  have hne : autI hV0 (thompsonJ G₀) ≠ ⊥ := by
    rw [← hmapN]
    intro h
    have h' := (Subgroup.map_eq_bot_iff_of_injective _ hρ).mp h
    exact barQ_XE_ne_bot r67 r68 hXI (le_bot_iff.mp ((barQ_mono hXEJ).trans h'.le))
  have hcommV : commV (autI hV0 (thompsonJ G₀)) = ⊤ := by
    have h1 := S1417.commutator_eq_map_commV hV0 hJN
    have h2 := Insp11.commutator_V0_thompsonJ h113 c L r66 r67 gl r68.toNoTwo hO2
    apply Subgroup.map_injective (S1417.inclMod_injective hV0)
    rw [← h1, S1417.map_inclMod_top hV0]
    exact h2
  have eH : ↥(Xdot153 T Mc M E s) ≃* ↥(autI hV0 (thompsonJ G₀)) :=
    (Subgroup.equivMapOfInjective _ ρ hρ).trans (MulEquiv.subgroupCongr hmapN)
  have hlistH : IsInspList ↥(autI hV0 (thompsonJ G₀)) := Insp11.isInspList_of_mulEquiv eH hlist
  have hS3H : ¬ Nonempty (↥(autI hV0 (thompsonJ G₀)) ≃* Equiv.Perm (Fin 3)) :=
    fun ⟨e⟩ => hS3 ⟨eH.trans e⟩
  have hnormal : (Xdot153 T Mc M E s).Normal := barQ_thompsonJ_normal G₀ Qb
  have hL3H : ¬ Nonempty (↥(autI hV0 (thompsonJ G₀)) ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2))) := by
    rintro ⟨e⟩
    have htop := Insp11.inspectL3Normal153 _ _ _ (Xdot153 T Mc M E s) hA hconc hnormal hO2
      ⟨eH.trans e⟩
    apply hnp
    have : Group.IsPerfect ↥(CFSG.Open.StatedSL 3 (ZMod 2)) := isPerfect_statedSL_three_two
    have hperfX : Group.IsPerfect ↥(Xdot153 T Mc M E s) := isPerfect_of_equiv (eH.trans e)
    rw [htop] at hperfX
    exact B1Red.oTwoUpper_eq_of_perfect hperfX
  have hYFne : YF153 Mc M E s ≠ ⊥ := by
    intro h
    have h' := hcomm
    rw [h, Subgroup.commutator_bot_right] at h'
    have hc := c.hyp.card_VZ
    rw [← h', Subgroup.card_bot] at hc
    omega
  have hVZab : IsElemAbelian 2 (VZ T M) := c.hyp.elemAbelian
  have hYFG : YF153 Mc M E s ≤ G₀ := le_sup_left.trans le_sup_left
  have hYFN : YF153 Mc M E s ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (le_sup_left : YF153 Mc M E s ≤ G1_153 T Mc M E s).trans hG1N
  have hYFP : pCoreOf 2 (YF153 Mc M E s) ≤ Subgroup.centralizer (VZ T M : Set G) :=
    le_sup_left.trans hQV
  obtain ⟨y₀, hy₀, hy₀3, hy₀f⟩ :=
    exists_fpf_element hVZab hYFN (YF_quot c r66 gl r68 hYFne) hYFP hcomm
  have hVZV0 : VZ T M ≤ V0_153 T Mc M E s := V_le_V0
  let W : Subgroup (IntMod (V0_153 T Mc M E s) hV0) := (VZ T M).comap (S1417.inclMod hV0)
  have hWmem : ∀ w : IntMod (V0_153 T Mc M E s) hV0, w ∈ W ↔ w.val ∈ VZ T M := by
    intro w
    rw [Subgroup.mem_comap, S1417.inclMod_apply]
  have hWmap : W.map (S1417.inclMod hV0) = VZ T M := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, S1417.map_inclMod_top hV0]
    exact inf_eq_right.mpr hVZV0
  have hWcard : Nat.card ↥W = 16 := by
    rw [← Subgroup.card_map_of_injective (S1417.inclMod_injective hV0), hWmap]
    exact c.hyp.card_VZ
  have hy0N : y₀ ∈ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hIN (hYFG hy₀)
  set a : MulAut (IntMod (V0_153 T Mc M E s) hV0) := convI hV0 ⟨y₀, hy0N⟩ with ha_def
  have haW : ∀ w ∈ W, a w ∈ W := by
    intro w hw
    rw [hWmem] at hw ⊢
    rw [ha_def, convI_apply_val]
    exact (Subgroup.mem_normalizer_iff.mp (hYFN hy₀) w.val).mp hw
  have haC : ∀ w ∈ W, a w = w → w = 1 := by
    intro w hw haw
    rw [hWmem] at hw
    have h1 : y₀ * w.val * y₀⁻¹ = w.val := by
      have := congrArg IntMod.val haw
      rwa [ha_def, convI_apply_val] at this
    exact IntMod.val_injective ((hy₀f _ hw h1).trans IntMod.val_one.symm)
  have ha3 : a ^ 3 = 1 := by
    rw [ha_def, ← map_pow]
    have : (⟨y₀, hy0N⟩ : Subgroup.normalizer (V0_153 T Mc M E s : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy₀3)
    rw [this, map_one]
  obtain ⟨x, hxJ, hx⟩ := Insp11.YF_act h113 c L r66 r67 gl r68.toNoTwo hO2 y₀ hy₀
  have haH : a ∈ autI hV0 (thompsonJ G₀) := by
    have hxN : x ∈ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hJN hxJ
    have : a = convI hV0 ⟨x, hxN⟩ := by
      ext u
      apply IntMod.val_injective
      rw [ha_def, convI_apply_val, convI_apply_val]
      exact hx u.val u.val_mem
    rw [this]
    exact convI_mem_autI hV0 hxJ hxN
  set Γ := autI hV0 G₀ with hΓ
  have hHΓ : autI hV0 (thompsonJ G₀) ≤ Γ := autI_mono hV0 hJle
  obtain ⟨k, hk⟩ := Insp11.index_eq_two_pow hO2
  have hbarTop : barQ G₀ Qb G₀ = ⊤ := by
    show (G₀.subgroupOf G₀).map (QuotientGroup.mk' Qb) = ⊤
    rw [Subgroup.subgroupOf_self, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Qb)]
  have hmapTop : (⊤ : Subgroup (↥G₀ ⧸ Qb)).map ρ = Γ := by
    rw [← hbarTop]
    exact map_rhoOf_barQ hV0 hIN Qb hQ le_rfl
  have hΓH : Nat.card ↥Γ = 2 ^ k * Nat.card ↥(autI hV0 (thompsonJ G₀)) := by
    rw [← hmapTop, ← hmapN]
    exact card_map_top_eq ρ hρ hk
  have hTsyl := isSylowTwoOf_TE_G0 c L r66 r67 gl r68
  have hTEG : TE153 T E ≤ G₀ := hTsyl.1
  have hTEN : TE153 T E ≤ Subgroup.normalizer (V0_153 T Mc M E s : Set G) := hTEG.trans hIN
  have hP : Nat.card ↥(autI hV0 (TE153 T E)) = 2 ^ padicValNat 2 (Nat.card ↥Γ) := by
    have h1 : autI hV0 (TE153 T E) = (barQ G₀ Qb (TE153 T E)).map ρ :=
      (map_rhoOf_barQ hV0 hIN Qb hQ hTEG).symm
    have hS2 : IsPGroup 2 ↥(barQ G₀ Qb (TE153 T E)) := isPGroup_barQ hTEG hTsyl.2.1
    have hSodd : ¬ 2 ∣ (barQ G₀ Qb (TE153 T E)).index := by
      intro h2
      apply hTsyl.2.2
      exact h2.trans (Subgroup.index_map_dvd ((TE153 T E).subgroupOf G₀) (QuotientGroup.mk'_surjective Qb))
    rw [h1, ← hmapTop]
    exact card_map_sylow ρ hρ hS2 hSodd
  set Rg : Subgroup G := T ⊓ Subgroup.centralizer (VZ T M : Set G) with hRg
  have hRgTE : Rg ≤ TE153 T E := R_le_TE L
  have hRΓ : autI hV0 Rg ≤ Γ := autI_mono hV0 (hRgTE.trans hTEG)
  have hRW : ∀ r ∈ autI hV0 Rg, ∀ w ∈ W, r w = w := by
    intro r hr w hw
    rw [hWmem] at hw
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV0).mp hr
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h1 := Subgroup.mem_centralizer_iff.mp hg.2 w.val hw
    calc (g : G) * w.val * (g : G)⁻¹ = (w.val * g) * (g : G)⁻¹ := by rw [h1]
      _ = w.val := mul_inv_cancel_right _ _
  have hTEV : TE153 T E ≤ Subgroup.normalizer (VZ T M : Set G) :=
    inf_le_left.trans (c.hyp.T_le.trans c.hyp.le_normalizer)
  have hint : Rg ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) =
      TE153 T E ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_right _ hRgTE
    · refine le_inf (le_inf ((inf_le_left : TE153 T E ⊓ _ ≤ TE153 T E).trans inf_le_left)
        (inf_le_right.trans (Subgroup.centralizer_le hVZV0))) inf_le_right
  have hTEC : TE153 T E ⊓ Subgroup.centralizer (VZ T M : Set G) = Rg := by
    apply le_antisymm
    · exact le_inf ((inf_le_left : TE153 T E ⊓ _ ≤ TE153 T E).trans inf_le_left) inf_le_right
    · exact le_inf hRgTE inf_le_right
  have e1 := card_autI_mul_card_inf hV0 hTEN
  have e2 := card_autI_mul_card_inf hV0 (hRgTE.trans hTEN)
  rw [hint] at e2
  have e3 := card_autI_mul_card_inf hVZab hTEV
  have hk4 : Nat.card ↥(autI hVZab (TE153 T E)) = 4 := r66.barTE_klein.1.1
  rw [hk4, hTEC] at e3
  have hc0pos : 0 < Nat.card ↥(TE153 T E ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) :=
    Nat.card_pos
  have hcardR : Nat.card ↥(autI hV0 (TE153 T E)) = 4 * Nat.card ↥(autI hV0 Rg) := by
    apply Nat.eq_of_mul_eq_mul_right hc0pos
    calc Nat.card ↥(autI hV0 (TE153 T E)) *
          Nat.card ↥(TE153 T E ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G))
        = Nat.card ↥(TE153 T E) := e1
      _ = 4 * Nat.card ↥Rg := e3.symm
      _ = 4 * (Nat.card ↥(autI hV0 Rg) *
          Nat.card ↥(TE153 T E ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G))) := by rw [e2]
      _ = (4 * Nat.card ↥(autI hV0 Rg)) *
          Nat.card ↥(TE153 T E ⊓ Subgroup.centralizer (V0_153 T Mc M E s : Set G)) := by ring
  have hRle : 2 ^ padicValNat 2 (Nat.card ↥Γ) ≤ 4 * Nat.card ↥(autI hV0 Rg) := by
    rw [← hP, hcardR]
  obtain ⟨hHat, hcardV⟩ := b51RemMod h56 hG2 (fun v => IntMod.sq_eq_one v) Γ
    (autI hV0 (thompsonJ G₀)) hHΓ k hΓH hne hB53 hcommV hlistH hS3H hL3H W hWcard a haH ha3 haW haC
    (autI hV0 Rg) hRΓ hRW hRle
  have hHatX : F6.IsHatAlt 6 ↥(Xdot153 T Mc M E s) := Insp9.isHatAlt_of_mulEquiv eH.symm hHat
  refine ⟨partB _ _ _ _ hA hconc hO2 hnp hHatX, ?_⟩
  exact hcardV

end LRed6

end CFSG.Quasithin
