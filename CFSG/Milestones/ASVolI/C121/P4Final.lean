module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Milestones.ASVolI.C121.P4Psl
public import CFSG.Milestones.ASVolI.C121.P4S3
public import CFSG.Milestones.ASVolI.C121.P4GrpC
public import CFSG.Milestones.ASVolI.C121.P4Nat
public import CFSG.Milestones.ASVolI.C121.P4Gbar

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped MatrixGroups Matrix

theorem burnsideC121_part4
    {Ω : Type} [Group Ω] [Finite Ω] {X L T R : Subgroup Ω}
    (hX : CharTwo X) (hLX : L = oTwoUpper X) (hLc : L ∈ cComp X)
    (hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hT : IsPGroup 2 T) (hSR : baum T ≤ R) (hRT : R ≤ T) (hQR : pCoreOf 2 X ≤ R) (hRX : R ≤ X) :
    ∀ V : Subgroup Ω, IsTwoReducedIn X V →
      autOn (thompsonJ R) V =
        autOn (R ⊓ Subgroup.centralizer ((V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω) :
          Subgroup Ω) : Set Ω)) V →
      ∀ Y : Subgroup Ω, Y = oTwoUpper Y → Y ≤ X →
        thompsonJ R ⊔ (X ⊓ Subgroup.centralizer (V : Set Ω)) ≤
          Subgroup.normalizer (Y : Set Ω) →
        Y ⊓ Subgroup.centralizer (V : Set Ω) = pCoreOf 2 Y →
        ((∃ n : ℕ, IsPSL 2 2 n
            (↥(autOn (Y ⊔ thompsonJ R) V) ⧸ CFSG.pCore 2 ↥(autOn (Y ⊔ thompsonJ R) V))) ∨
          Nonempty ((↥(autOn (Y ⊔ thompsonJ R) V) ⧸ CFSG.pCore 2 ↥(autOn (Y ⊔ thompsonJ R) V)) ≃*
            Equiv.Perm (Fin 3))) →
        IsSylowTwoOf (autOn (thompsonJ R) V) (autOn (Y ⊔ thompsonJ R) V) →
        ⁅V ⊓ Subgroup.centralizer (thompsonJ R : Set Ω), Y⁆ ≠ ⊥ →
        autOn (baum T) V = autOn (thompsonJ R) V ∧ InYSet X R (baum T) Y := by
  intro V hred hJZ Y hYperf hYX hYN hYC hcase hsyl hZY
  have h : burnsideC121_p4_Hyp X L T R V Y :=
    ⟨hLX, hLq, hT, hSR, hRT, hQR, hRX, hred, hJZ, hYperf, hYX, hYN, hYC, hsyl, hZY⟩
  refine ⟨h.autOn_baum, hYX, hYperf, h.SQ_le_NY, h.sylow_RY, ?_⟩
  obtain ⟨W, hWred, hWmax⟩ := exists_isTwoReducedIn_max ((baum T ⊔ pCoreOf 2 X) ⊔ Y)
  have hWm : IsTwoReducedIn ((baum T ⊔ pCoreOf 2 X) ⊔ Y) W ∧
      ∀ W' : Subgroup Ω, IsTwoReducedIn ((baum T ⊔ pCoreOf 2 X) ⊔ Y) W' → W' ≤ W :=
    ⟨hWred, hWmax⟩
  refine ⟨W, hWm, ?_⟩
  have hW : IsElemAbelian 2 W := burnsideC121_p4_Hyp.elemW hWm
  have hHW : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ Subgroup.normalizer (W : Set Ω) := hWred.2.1
  have hYW : Y ≤ Subgroup.normalizer (W : Set Ω) := h.Y_le_H.trans hHW
  have h2W : ∀ w : IntMod W hW, w ^ 2 = 1 := IntMod.sq_eq_one
  have hYne : autI hW Y ≠ ⊥ := fun hb =>
    h.Y_not_le_CW hWm ((autI_eq_bot_iff hW hYW).1 hb)
  have hYnorm : ∀ g ∈ autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y), ∀ x ∈ autI hW Y,
      g * x * g⁻¹ ∈ autI hW Y := C124.autI_conj_mem hW h.H_le_NY
  have hcase' : (∃ n : ℕ, IsPSL 2 2 n (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)))) ∨
      Nonempty ((↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸ CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))) ≃*
        Equiv.Perm (Fin 3)) := hcase
  rcases hcase' with ⟨n, hPSL⟩ | he3
  ·
    obtain ⟨hn2, K, hK, hKf, hKc, ⟨eK⟩⟩ := burnsideC121_p4_psl_equiv hPSL
    have hKc' : Nat.card K = 2 ^ n := by rw [Nat.card_eq_fintype_card, hKc]
    have : IsSimpleGroup SL(2, K) := burnsideC121_p4_isSimpleGroup_sl2 hn2 hKc
    have : IsSimpleGroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))) := MulEquiv.isSimpleGroup eK
    have hG : ∀ N : Subgroup (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))),
        N.Normal → N = ⊥ ∨ ∀ τ, Odd (orderOf τ) → τ ∈ N := by
      intro N hN
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h1 | h1
      · exact Or.inl h1
      · exact Or.inr fun τ _ => h1 ▸ Subgroup.mem_top τ
    have heven : Even (Nat.card (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)))) := by
      rw [Nat.card_congr eK.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hKc']
      exact (Nat.even_pow.2 ⟨even_two, by omega⟩).mul_right _
    obtain ⟨ι⟩ := h.iota hWm hG
    let θ : ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) ≃* SL(2, K) := ι.trans eK
    obtain ⟨A, hAG, hA1, hAe, hAFF⟩ := h.isFF hWm hG heven
    obtain ⟨β, hβs, hβk, hβe⟩ := burnsideC121_p4_psl_natural h2W hn2 hKc θ hAG hA1 hAe hAFF
    have : IsSimpleGroup ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) := MulEquiv.isSimpleGroup θ
    have hYH : autI hW Y = autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y) := by
      rcases burnsideC121_p4_normal_cases (autI hW Y) (autI_mono hW h.Y_le_H) hYnorm with h1 | h1
      · exact absurd h1 hYne
      · exact h1
    have h4 : 4 ≤ Nat.card K := by
      rw [hKc']
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    refine ⟨n, by omega, burnsideC121_p4_isNatL2Section hW h.Y_le_H hHW hKc θ β hβs
      (by rw [hYH]; exact hβk) hβe (h.YCW hWm hG) ?_⟩
    rw [hYH, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.2 θ.surjective, C126.Nat.commutator_sl2_eq_top h4]
  ·
    obtain ⟨e3⟩ := he3
    have hG := burnsideC121_p4_s3_normal e3
    have hG6 : Nat.card (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R))) = 6 := by
      rw [Nat.card_congr e3.toEquiv, burnsideC121_p4_card_perm3]
    have heven : Even (Nat.card (↥(autI h.hV (Y ⊔ thompsonJ R)) ⧸
        CFSG.pCore 2 ↥(autI h.hV (Y ⊔ thompsonJ R)))) := by
      rw [hG6]; decide
    obtain ⟨ι⟩ := h.iota hWm hG
    have hH6 : Nat.card ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) = 6 := by
      rw [Nat.card_congr ι.toEquiv, hG6]
    obtain ⟨θ, β, hβs, hβk, hβe⟩ :=
      burnsideC121_p4_s3_natural h2W hH6 (h.O2_bot hWm) (h.isFF hWm hG heven)
    have hYsl : ∀ g : ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)),
        (g : MulAut (IntMod W hW)) ∈ autI hW Y → θ g ∈ C1Pack.sl2A3 := by
      let φY : ↥Y →* ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) :=
        (convHom hW Y hYW).codRestrict (autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) (fun y => by
          rw [convHom_apply]; exact convI_mem_autI hW (h.Y_le_H y.2) (hYW y.2))
      let ψ : ↥Y →* C1Pack.SL2F2 := θ.toMonoidHom.comp φY
      have hY : Y ≤ (C1Pack.sl2A3.comap ψ).map Y.subtype := by
        conv_lhs => rw [hYperf]
        refine (Subgroup.closure_le _).2 ?_
        rintro y ⟨hyY, hyo⟩
        refine ⟨⟨y, hyY⟩, ?_, rfl⟩
        have h1 : Odd (orderOf (ψ ⟨y, hyY⟩)) := by
          have h2 : orderOf (⟨y, hyY⟩ : ↥Y) = orderOf y := Subgroup.orderOf_mk y hyY
          exact (h2 ▸ hyo).of_dvd_nat (orderOf_map_dvd ψ _)
        exact C1Pack.mem_sl2A3.2 (burnsideC121_p4_sl2F2_cube h1)
      intro g hg
      obtain ⟨x, hxY, hx⟩ := (mem_autI hW).1 hg
      obtain ⟨y', hy', hy'x⟩ := Subgroup.mem_map.1 (hY hxY)
      have hgy : g = φY y' := by
        apply Subtype.ext
        show (g : MulAut (IntMod W hW)) = convI hW ⟨y', hYW y'.2⟩
        rw [← hx]
        congr 1
        exact Subtype.ext hy'x.symm
      rw [hgy]
      exact hy'
    obtain ⟨⟨n₀, hn₀Y⟩, hn₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
    have hn₀1 : n₀ ≠ 1 := fun h1 => hn₀1' (Subtype.ext h1)
    have hn₀H : n₀ ∈ autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y) := autI_mono hW h.Y_le_H hn₀Y
    have hθn₀3 : (θ ⟨n₀, hn₀H⟩) ^ 3 = 1 := C1Pack.mem_sl2A3.1 (hYsl ⟨n₀, hn₀H⟩ hn₀Y)
    have hθn₀1 : θ ⟨n₀, hn₀H⟩ ≠ 1 := by
      intro h1
      apply hn₀1
      have : (⟨n₀, hn₀H⟩ : ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y))) = 1 :=
        θ.injective (h1.trans (map_one θ).symm)
      exact congrArg Subtype.val this
    have hfix : fixV (autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y)) = fixV (autI hW Y) := by
      apply le_antisymm
      · exact fun w hw x hx => hw x (autI_mono hW h.Y_le_H hx)
      · intro w hw
        rw [← hβk, MonoidHom.mem_ker]
        have h1 := hβe ⟨n₀, hn₀H⟩ w
        rw [show ((⟨n₀, hn₀H⟩ : ↥(autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y))) : MulAut (IntMod W hW)) w
          = w from hw n₀ hn₀Y] at h1
        have h2 := C1Pack.sl2_eq_zero_of_fixed _ hθn₀3 hθn₀1 _
          (congrArg Multiplicative.toAdd h1).symm
        exact Multiplicative.toAdd.injective (by simpa using h2)
    have hrange : ((autI hW Y).subgroupOf (autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y))).map
        θ.toMonoidHom = commutator SL(2, ZMod 2) := by
      rw [C1Pack.commutator_sl2_eq]
      set M := ((autI hW Y).subgroupOf (autI hW ((baum T ⊔ pCoreOf 2 X) ⊔ Y))).map
        θ.toMonoidHom with hM
      have hMle : M ≤ C1Pack.sl2A3 := by
        rintro _ ⟨g, hg, rfl⟩
        exact hYsl g (Subgroup.mem_subgroupOf.1 hg)
      have hMne : M ≠ ⊥ := by
        intro hb
        apply hθn₀1
        have : θ ⟨n₀, hn₀H⟩ ∈ M := ⟨⟨n₀, hn₀H⟩, Subgroup.mem_subgroupOf.2 hn₀Y, rfl⟩
        rw [hb, Subgroup.mem_bot] at this
        exact this
      have hdvd : Nat.card M ∣ 3 := C1Pack.card_sl2A3 ▸ Subgroup.card_dvd_of_le hMle
      have hM3 : Nat.card M = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
        · exact absurd (Subgroup.card_eq_one.1 h1) hMne
        · exact h1
      exact Subgroup.eq_of_le_of_card_ge hMle (by rw [hM3, C1Pack.card_sl2A3])
    exact ⟨1, le_rfl, burnsideC121_p4_isNatL2Section hW h.Y_le_H hHW (n := 1) (by simp) θ β hβs
      (by rw [← hfix]; exact hβk) hβe (h.YCW hWm hG) hrange⟩

end CFSG.ASVolI
