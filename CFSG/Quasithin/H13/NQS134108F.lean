module

public import CFSG.Quasithin.H13.NQS134108E

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

theorem a6P2_orders : ∀ σ ∈ a6P2list, σ ^ 3 = 1 ∨ σ ^ 4 = 1 := by decide +kernel

theorem a6P2_e45_orbit : ∀ σ ∈ a6P2list, σ ^ 3 = 1 → σ ≠ 1 →
    e45 * G6.permAct 6 σ e45 * G6.permAct 6 σ (G6.permAct 6 σ e45) ≠ 1 := by
  decide +kernel

theorem permAct_allOnes : ∀ σ : Perm (Fin 6),
    G6.permAct 6 σ (Multiplicative.ofAdd ![1, 1, 1, 1, 1, 1]) =
      Multiplicative.ofAdd ![1, 1, 1, 1, 1, 1] := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem hasWtIn_zV (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347 : U3.Stmt13_4_7L2)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) {H₂ : Subgroup G} (hstar : IsHStar T (normalizer (L : Set G)) H₂)
    (hH₂H : H₂ ≤ H) (hi : U3.Concl1347i T H₂ (U3.l2Of S ⊔ T)) (hcore : IsCore5 K W) :
    ∀ v ∈ V ⊓ centralizer (L : Set G), v ≠ 1 → HasWtIn K W v 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, -, hZW, hL1, -, htype⟩ := D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, hHKT, -, -⟩ := D.seven hC137 h1332 h1228 hC58 h317 h56 he hnhat
  obtain ⟨-, hZVW, k, hkK, hkH₂, ⟨m, hm, hkm⟩, hkz, hmul⟩ :=
    D.eight_i hC137 h1332 h1228 hC58 h317 h56 h1222 h1347 he hnhat hstar hH₂H hi
  obtain ⟨_, -, hc⟩ := hcore
  have hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) := by
    rcases htype with ⟨hK3, hnat⟩ | ⟨hK6, -⟩
    · exfalso
      obtain ⟨-, -, mc, m3⟩ := card_autOn_of_module (K := K) (W := W)
      have h1 := mc hc
      have h2 := m3 hnat
      omega
    · exact hK6
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc
  obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW D.isSylowTwoOf_inf
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  obtain ⟨DP, hB⟩ := frame5_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
  have hTB : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K → F.ρ g ∈ a6D := fun g hg =>
    (mem_a6D_iff _).2 ⟨F.T_D g (mem_inf.1 hg).1,
      Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, (mem_inf.1 hg).2, rfl⟩)⟩
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ a6P2,
      F.ρ t * γ * (F.ρ t)⁻¹ ∈ a6P2 := fun t ht γ hγ =>
    a6P2_conj_D _ (F.T_D t ht) γ hγ
  obtain ⟨γ, hγ, β, hβ, hγβ⟩ := exists_a6P2_conj
  obtain ⟨-, -, huniq, -⟩ := D.h2_of_parData hM hZV1 DP stab45_le_alt hTB hB
    (fun Y hY hYA => a6_overgroups hY hYA) (fun x hx => a6D_le_P2 x hx) a6P2_le_alt a6P2_not_le
    stab45_not_le_P2 hTY a6D_relIndex_P2 hγ hβ hγβ
  have hH₂eq : H₂ = DP.parOf a6P2 := huniq H₂ hstar (hH₂H.trans hHKT.le)
  have hkN : k ∈ normalizer (W : Set G) := D.Wirr.2.2.1 hkK
  have hσP : F.ρ ⟨k, hkN⟩ ∈ a6P2 := by
    refine DP.img'_parOf_le D.TW hTB (fun x hx => a6D_le_P2 x hx) hTY ?_
    rw [← hH₂eq]
    exact DP.mem_img' (g := ⟨k, hkN⟩) (mem_inf.2 ⟨hkH₂, hkK⟩)
  have hσm : F.ρ ⟨k, hkN⟩ ^ m = 1 := by
    rw [← map_pow]
    have : (⟨k, hkN⟩ : ↥(normalizer (W : Set G))) ^ m = 1 := Subtype.ext (by simpa using hkm)
    rw [this, map_one]
  have hσ3 : F.ρ ⟨k, hkN⟩ ^ 3 = 1 := by
    rcases a6P2_orders _ hσP with h | h
    · exact h
    · have h1 := pow_gcd_eq_one.2 ⟨h, hσm⟩
      rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)),
        pow_one] at h1
      rw [h1, one_pow]
  have hzVW : S.zV ∈ W := hZVW (S.mem_ZV_iff.2 (Or.inr rfl))
  have hσ1 : F.ρ ⟨k, hkN⟩ ≠ 1 := fun h => hkz (by
    have h1 := mem_centralizer_iff.mp (frame5_ker F ⟨k, hkN⟩ h) S.zV hzVW
    calc k * S.zV * k⁻¹ = S.zV * k * k⁻¹ := by rw [h1]
      _ = S.zV := by group)
  have hfixiff : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
      ((F.ψ (conjAct W g w) : ↥(G6.coreMod 6)) : G6.PermMod 6) =
        G6.permAct 6 (F.ρ g) (F.ψ w) := fun g w => by
    rw [F.equiv g w, G6.coreAct_coe]
  set w₀ : ↥W := ⟨S.zV, hzVW⟩ with hw₀
  have hzVT : S.zV ∈ centralizer (T : Set G) := (mem_quasithinOmegaOneCenter_iff.1
    (U3.s134_zV_mem_Z S)).2.1
  have hfix : ∀ σ : Perm (Fin 6), InD6 σ → σ ∈ alternatingGroup (Fin 6) →
      G6.permAct 6 σ (F.ψ w₀ : G6.PermMod 6) = F.ψ w₀ := by
    intro σ hσD hσA
    obtain ⟨t, htT, rfl⟩ := F.DA_T σ hσD hσA
    rw [← hfixiff]
    congr 2
    apply Subtype.ext
    rw [A5.conjAct_val]
    show (t : G) * S.zV * (t : G)⁻¹ = S.zV
    rw [mem_centralizer_iff.mp hzVT (t : G) htT, mul_inv_cancel_right]
  have hconjw : ∀ g : ↥(normalizer (W : Set G)), (g : G) * S.zV * (g : G)⁻¹ ∈ W := fun g =>
    (mem_normalizer_iff.mp g.2 S.zV).mp hzVW
  have hpsiconj : ∀ g : ↥(normalizer (W : Set G)),
      ((F.ψ ⟨(g : G) * S.zV * (g : G)⁻¹, hconjw g⟩ : ↥(G6.coreMod 6)) : G6.PermMod 6) =
        G6.permAct 6 (F.ρ g) (F.ψ w₀) := fun g => by
    rw [← hfixiff]
    congr 2
  obtain ⟨⟨h1D, h1A⟩, ⟨h2D, h2A⟩, ⟨h3D, h3A⟩⟩ := da_props
  have hcases := fixDA_cases _ (hfix _ h1D h1A) (hfix _ h2D h2A) (hfix _ h3D h3A)
  have hpsi : (F.ψ w₀ : G6.PermMod 6) = e0123 := by
    rcases hcases with h | h | h | h
    · exfalso
      have h1 : F.ψ w₀ = 1 := Subtype.ext h
      rw [MulEquiv.map_eq_one_iff] at h1
      exact S.zV_ne_one (congrArg Subtype.val h1)
    · exact h
    · exfalso
      have hka : k * S.zV * k⁻¹ ∈ W := hconjw ⟨k, hkN⟩
      have hkb : k * (k * S.zV * k⁻¹) * k⁻¹ ∈ W := (mem_normalizer_iff.mp hkN _).mp hka
      have h1 : (⟨S.zV, hzVW⟩ : ↥W) * ⟨k * S.zV * k⁻¹, hka⟩ *
          ⟨k * (k * S.zV * k⁻¹) * k⁻¹, hkb⟩ = 1 := Subtype.ext hmul
      have h2 := congrArg (fun x => (F.ψ x : G6.PermMod 6)) h1
      simp only [map_mul, map_one, Subgroup.coe_mul, Subgroup.coe_one] at h2
      have ha := hpsiconj ⟨k, hkN⟩
      have hb : ((F.ψ ⟨k * (k * S.zV * k⁻¹) * k⁻¹, hkb⟩ : ↥(G6.coreMod 6)) : G6.PermMod 6) =
          G6.permAct 6 (F.ρ ⟨k, hkN⟩) (G6.permAct 6 (F.ρ ⟨k, hkN⟩) (F.ψ w₀)) := by
        rw [← ha, ← hfixiff]
        congr 2
      rw [show (⟨S.zV, hzVW⟩ : ↥W) = w₀ from rfl] at h2
      rw [show ((F.ψ ⟨k * S.zV * k⁻¹, hka⟩ : ↥(G6.coreMod 6)) : G6.PermMod 6) =
        G6.permAct 6 (F.ρ ⟨k, hkN⟩) (F.ψ w₀) from ha, hb, h] at h2
      exact a6P2_e45_orbit _ hσP hσ3 hσ1 h2
    · exfalso
      apply D.KZV
      intro g hgK
      rw [mem_centralizer_iff]
      intro x hx
      rcases S.mem_ZV_iff.1 hx with rfl | rfl
      · simp
      · have hgN : g ∈ normalizer (W : Set G) := D.Wirr.2.2.1 hgK
        have h1 : F.ψ ⟨g * S.zV * g⁻¹, hconjw ⟨g, hgN⟩⟩ = F.ψ w₀ := by
          apply Subtype.ext
          rw [hpsiconj ⟨g, hgN⟩, h]
          exact permAct_allOnes _
        have h2 := congrArg Subtype.val (F.ψ.injective h1)
        calc S.zV * g = g * S.zV * g⁻¹ * g := by rw [show g * S.zV * g⁻¹ = S.zV from h2]
          _ = g * S.zV := by group
  intro v hv hv1
  rcases S.mem_ZV_iff.1 hv with rfl | rfl
  · exact absurd rfl hv1
  refine ⟨{ hnorm := F.L_le
            θ := (F.ρ.comp (Subgroup.inclusion F.L_le)).codRestrict (alternatingGroup (Fin 6))
              fun l => (F.image_L _).1 ⟨_, l.2, rfl⟩
            ψ := F.ψ
            surj := fun σ => by
              obtain ⟨g, hgK, hg⟩ := (F.image_L σ).2 σ.2
              exact ⟨⟨g, hgK⟩, Subtype.ext hg⟩
            equiv := fun l w => F.equiv _ w }, hzVW, ?_⟩
  show (Finset.univ.filter fun i : Fin 6 =>
    Multiplicative.toAdd (F.ψ w₀ : G6.PermMod 6) i = 1).card = 4
  rw [hpsi]
  exact wt6_e0123

end Data13410

end CFSG.Quasithin.H13.NQS134
