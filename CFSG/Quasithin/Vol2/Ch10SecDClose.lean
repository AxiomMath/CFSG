module

public import CFSG.Quasithin.Vol2.Ch10SecDClD
public import CFSG.Quasithin.Background.BlueprintB2Bridge
public import CFSG.Quasithin.Vol2.Ch10SecDClA

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem commutator_Vz_ne_bot {Gz V K₁ M : Subgroup G} (hGzV : Gz ≤ Subgroup.normalizer (V : Set G))
    (hK₁ : K₁ ≤ Gz) {s : G} (hs : s ∈ Gz)
    (h1 : Gz ⊓ Subgroup.centralizer (V : Set G) ≤ M) (hKM : ¬ K₁ ⊔ CFSG.conjugate K₁ s ≤ M) :
    ⁅V, K₁⁆ ≠ ⊥ := by
  intro hbot
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  have hN : ∀ g ∈ Gz, ∀ x ∈ Gz ⊓ Subgroup.centralizer (V : Set G),
      g * x * g⁻¹ ∈ Gz ⊓ Subgroup.centralizer (V : Set G) := by
    intro g hg x hx
    refine ⟨Gz.mul_mem (Gz.mul_mem hg hx.1) (Gz.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hGzV (Gz.inv_mem hg)) v).mp hv
    have hxw := Subgroup.mem_centralizer_iff.mp hx.2 _ hw
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [hxw]
      _ = g * x * g⁻¹ * v := by group
  have hK₁N : K₁ ≤ Gz ⊓ Subgroup.centralizer (V : Set G) := le_inf hK₁ hbot
  have hK₂N : CFSG.conjugate K₁ s ≤ Gz ⊓ Subgroup.centralizer (V : Set G) := fun x hx => by
    have hx' : s * x * s⁻¹ ∈ K₁ := SecA.mem_conjugate_iff.mp hx
    have e1 : x = s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ := by group
    rw [e1]
    exact hN _ (Gz.inv_mem hs) _ (hK₁N hx')
  exact hKM ((sup_le hK₁N hK₂N).trans h1)

theorem stmtClose10_of
    (hW : FactSymFiveWrTwo) (hA : FactPSL2NormA5) (hAut : FactAutSL)
    (hMax : FactMaxP) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1023 : Stmt10_2_3) (h1024 : Stmt10_2_4) (h10211 : Stmt10_2_11) (h10213 : Stmt10_2_13)
    (h1031 : Stmt10_3_1) (h1032 : Stmt10_3_2) : StmtClose10 := by
  intro G _ _ T L I h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 := (h10213 G T L I h).1
  have hc := (h1031 G T L I h).1
  obtain ⟨t, v₁, v₂, hd⟩ := exists_isData10_2_11 h37 h38 h h3 hc
  have := h.fsu.simple
  have hK : LocalSQTK G := (qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  obtain ⟨H, hH, hHz, hO, hHK, ⟨e⟩⟩ :=
    exists_isHStar_le_KzT hW h37 h38 h1023 h10213 h1032 h h3 hc hd
  have hTz := T_le_centralizer_z h37 h38 h h3 hc hd
  have hTGz : IsSylowTwoOf T (Subgroup.centralizer ({v₁ * v₂} : Set G)) :=
    isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz
  have hX := pCoreOf_Gz_ne_bot h37 h38 h hc hd
  have hGzK : Subgroup.centralizer ({v₁ * v₂} : Set G) ≤
      Subgroup.normalizer (Kz T L (v₁ * v₂) : Set G) := le_normalizer_conjClosure _ _
  have hKM := not_Kz_le_fsuM hW h37 h38 h1023 h10213 h1032 h h3 hc hd
  have hXM : Xz T L (v₁ * v₂) ≤ fsuM T L :=
    (oTwoUpper_le _).trans (inf_le_left.trans (SecA.fsuL0_le_fsuM T L))
  obtain ⟨y, -, hyX, hyo, hyC⟩ := exists_odd_mem_Xz h37 h38 h h3 hc hd
  have hy1 : y ≠ 1 := fun h1 => hyC (h1 ▸ Subgroup.one_mem _)
  rcases concl10_2_4_Kz hW h37 h38 h1023 h1024 h10213 h1032 hMax h h3 hc hd with
    ⟨K₁, s, hs, hK₁, hsn, hKz, htype⟩ | ⟨-, k, hk, ⟨eA⟩⟩
  · have hTK : T ≤ Subgroup.normalizer ((K₁ ⊔ CFSG.conjugate K₁ s : Subgroup G) : Set G) := by
      rw [← hKz]
      exact hTz.trans hGzK
    have hK1H : K₁ ≤ H := le_of_case_two hW hA hK h37 hX hK₁ hs hsn hTK hTGz hH.1.1 hHz
      (hKz ▸ hO) e htype
    have hKzH : Kz T L (v₁ * v₂) ≤ H := by
      rw [hKz]
      exact sup_le hK1H (conjugate_le_of_mem hK1H (hH.1.1 hs))
    have hKT : K₁ ⊔ CFSG.conjugate K₁ s ⊔ T = H := by
      rw [← hKz]
      exact le_antisymm (sup_le hKzH hH.1.1) hHK
    have hK₁T : K₁ ⊔ T = H := by
      refine le_antisymm (sup_le hK1H hH.1.1) ?_
      rw [← hKT]
      exact sup_le (sup_le le_sup_left (conjugate_le_of_mem le_sup_left
        ((le_sup_right : T ≤ K₁ ⊔ T) hs))) le_sup_right
    have hTH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hH.1.1
    have hloc : quasithinIsLocal T K₁ := quasithinIsLocal_of_mem_cComp hK₁ hK₁T hHz hTH hH.1.2
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥H))
    have hcardH : Nat.card ↥H = 2 ^ (b + 7) * 225 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
      rw [Nat.card_congr e.toEquiv, card_symFiveWrTwo, hb] at h1
      rw [h1, pow_add]
      ring
    obtain ⟨eA5⟩ := nonempty_alt5_of_type (not_isSolvable_of_mem_cComp hK₁)
      (by rw [← hcardH]; exact card_quot_dvd_of_le hK1H) htype
    have hchar : CharTwo (Subgroup.centralizer ({v₁ * v₂} : Set G)) :=
      charTwo_of_le h.fsu.qtke h.fsu.sylow hTz hX
    have hlt : Xz T L (v₁ * v₂) < Kz T L (v₁ * v₂) :=
      lt_of_le_of_ne (le_conjClosure _ _) fun heq => hKM (by rw [← heq]; exact hXM)
    have h211 := h10211 G T L I h h3 hc t v₁ v₂ hd
    obtain ⟨hVle, hred⟩ := h211.2.1 hlt
    have hV : IsTwoReducedIn (Subgroup.centralizer ({v₁ * v₂} : Set G)) (Vz v₁ v₂) :=
      isTwoReducedIn_iff_isPrimeReduced_subgroupOf.mpr ⟨hVle, hred⟩
    have hVK : ⁅Vz v₁ v₂, K₁⁆ ≠ ⊥ :=
      commutator_Vz_ne_bot (le_normalizer_conjClosure _ _) (le_of_mem_cComp hK₁) (hTz hs)
        (h211.1.2.trans inf_le_left) (by rw [← hKz]; exact hKM)
    have hfl := quasithinIsFaithfulLocal_of_isTwoReducedIn hloc hK₁ hchar hV hVK
    have hPX := oTwoUpper_P_eq (T := T) (L := L) h.fsu.sylow.1 (z := v₁ * v₂)
    have hXK : oTwoUpper ((fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G)) ≤
        K₁ ⊔ CFSG.conjugate K₁ s := by
      rw [hPX, ← hKz]
      exact le_conjClosure _ _
    refine ⟨K₁, ⟨hloc, fun K' hK' hle => ?_⟩, hfl, isQuasisimple_of_mulEquiv_alt5 eA5,
      fun hTN => hsn (hTN hs), ⟨eA5⟩⟩
    exact eq_of_isLocal_of_le hW hA hAut hK h37 h1024 h h3 hc (hMax G T L I h h3 hc t v₁ v₂ hd)
      (le_inf le_sup_right hTz) hH.2.1 hHz hTGz e hK₁ hs (hKz ▸ hO) hKT hXK
      (by rw [hPX]; exact hXM) (by rw [hPX]; exact hyX) hyo hy1 hK' hle
  · exact (not_case_three_Kz hW hAut h37 h38 h1023 h10213 h1032 h h3 hc hd k hk eA).elim

end CFSG.Quasithin.Vol2.Ch10.SecD
