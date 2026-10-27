module

public import CFSG.Quasithin.H13.A6S138Ic
public import CFSG.Quasithin.EmptyFaithful.S146G1
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.H13.A6S138Ia

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace A6Id

theorem card_GL42 : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field, ZMod.card, Fin.prod_univ_four]
  norm_num

theorem card_of_isPSL42 {X : Type} [Group X] (h : IsPSL 4 2 1 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem eq_one_of_comm_GL42 {g : Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)}
    (hg : ∀ x, g * x = x * g) : g = 1 := by
  have hc : g ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
    Subgroup.mem_center_iff.mpr fun x => (hg x).symm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨a, rfl⟩ := hc
  have ha : a = 1 := Subsingleton.elim _ _
  rw [ha, map_one]

theorem eq_one_of_comm_ab : ∀ σ : Perm (Fin 6), σ * A6Coc.aP = A6Coc.aP * σ →
    σ * A6Coc.bP = A6Coc.bP * σ → σ = 1 := by
  decide +kernel

theorem eq_one_of_pow_three {G : Type} [Group G] [Finite G] {X : Subgroup G} {c : G}
    (hc : c ∈ pCoreOf 2 X) (hc3 : c ^ 3 = 1) : c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 X ⟨c, hc⟩
  have h2 : c ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have h3 : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h1 h3)

end A6Id

theorem ident13827_of
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13 : Lem13813) (h16 : Lem13816)
    (h21 : Lem13821) (h24 : Lem13824) (h25 : Lem13825) (h26 : Lem13826) (hG2 : Lem13827G2) :
    Ident13827 := by
  intro G _ _ T L V S hNS hNU hG1 hab hF
  have hS : S.Hyp138 := Setting4.hyp138_of h13315 h1356two hNS hNU hG1 hab
  have hnsol : ¬ Group.IsSolvable ↥S.G1 := fun hsol =>
    hG1.2.2 (h13 G T L V S hS S.G1 hG1.1.1 le_rfl hsol)
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable (le_refl S.G1)
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_rfl |>.mpr (Subgroup.le_normalizer)) hnsol
  have hKG : K ≤ S.G1 := le_of_mem_cComp hK
  obtain ⟨⟨hKN, -⟩, -⟩ := h16 G T L V S hS S.G1 hG1 K hK
  obtain ⟨hL1K, hlist, ⟨hKT, -⟩, hUK⟩ := h21 G T L V S hS S.G1 hG1 K hK
  have hF1 := hF.toHypF91
  refine ⟨K, hKN, hKT, hL1K, ?_⟩
  rcases hlist with h3 | h4 | h5 | h6 | h7 | hU
  · obtain ⟨h, -⟩ := h25 G T L V S hS S.G1 hG1 K hK 3 le_rfl (by norm_num) h3
    exact absurd h (by norm_num)
  ·
    obtain ⟨-, ⟨hhat, ρ, hρs, hρk, β, hβs, hβk, hβe⟩, -⟩ :=
      h25 G T L V S hS S.G1 hG1 K hK 4 (by norm_num) (by norm_num) h4
    refine ⟨fun h hh hcomm => ?_, Or.inr ⟨hhat, ρ, hρs, hρk, β, hβs, hβk, hβe⟩⟩
    let f : ↥K →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
      ρ.comp (Subgroup.inclusion hKG)
    have hfker : f.ker = (pCoreOf 2 S.G1).subgroupOf K := by
      ext k
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact hρk _
    have hfr : f.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [A6Id.card_GL42, ← Subgroup.index_ker, hfker, ← Subgroup.relIndex,
        ← Subgroup.inf_relIndex_left, ← hF1.card_autOn_tilde hKG]
      exact A6Id.card_of_isPSL42 h4
    have hc : ∀ x, ρ ⟨h, hh⟩ * x = x * ρ ⟨h, hh⟩ := by
      intro x
      obtain ⟨k, hk⟩ : x ∈ f.range := by rw [hfr]; exact Subgroup.mem_top x
      rw [← hk]
      have h1 : ρ (⟨h, hh⟩ * Subgroup.inclusion hKG k * (⟨h, hh⟩ : ↥S.G1)⁻¹ *
          (Subgroup.inclusion hKG k)⁻¹) = 1 := (hρk _).2 (hcomm k k.2)
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have h1 := A6Id.eq_one_of_comm_GL42 hc
    exact (hρk ⟨h, hh⟩).1 h1
  · obtain ⟨h, -⟩ := h25 G T L V S hS S.G1 hG1 K hK 5 (by norm_num) le_rfl h5
    exact absurd h (by norm_num)
  ·
    obtain ⟨α, hαs, hαk, hchief, hβ⟩ := h26 G T L V S hS S.G1 hG1 K hK h6
    have hnhat : ¬ IsHatA6 L := by
      intro hhat
      obtain ⟨c, hcL0, hc3, hcO, -⟩ := l0_decomp hhat
      have hc1 : c ≠ 1 := fun h => hcO (h ▸ Subgroup.one_mem _)
      have hcL1 : c ∈ S.L1 := S.l0_le_L1 hcL0
      have hcO1 : c ∉ pCoreOf 2 S.L1 := fun h => hc1 (A6Id.eq_one_of_pow_three h hc3)
      have hcV : c ∈ Subgroup.centralizer (V : Set G) :=
        S.o2Z_le_centralizer (oTwoRes_le _ hcL0)
      have hV3 : ∀ t ∈ S.V3, ∀ k ∈ K, k * t * k⁻¹ * t⁻¹ ∈ fsuV1 T V := by
        intro t ht
        refine hchief c hcL1 hc3 hcO1 t (le_conjClosure _ _ ht) fun k _ => ?_
        have e : c * t * c⁻¹ * t⁻¹ = 1 := by
          rw [← Subgroup.mem_centralizer_iff.mp hcV t (S.V3_le_V ht)]
          group
        rw [e]
        simp only [mul_one, mul_inv_cancel, inv_one]
        exact (fsuV1 T V).one_mem
      have hUC : conjClosure S.V3 S.G1 ≤ centralizerMod (fsuV1 T V) (conjClosure S.V3 S.G1) K := by
        refine conjClosure_le fun g hg t ht => ⟨mem_conjClosure hg ht,
          hF1.H_normalizes_V₁
            (pCoreOf_le 2 _ (hF1.conjClosure_Vp_le_pCoreOf (mem_conjClosure hg ht))),
          fun k hk => ?_⟩
        have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hKN (S.G1.inv_mem hg)) k).mp hk
        have h1 := hV3 t ht _ hk'
        have h2 : g * (g⁻¹ * k * g⁻¹⁻¹ * t * (g⁻¹ * k * g⁻¹⁻¹)⁻¹ * t⁻¹)⁻¹ * g⁻¹ ∈ fsuV1 T V :=
          (Subgroup.mem_normalizer_iff.mp (hF1.H_normalizes_V₁ hg) _).mp
            ((fsuV1 T V).inv_mem h1)
        have e : g * t * g⁻¹ * k * (g * t * g⁻¹)⁻¹ * k⁻¹ =
            g * (g⁻¹ * k * g⁻¹⁻¹ * t * (g⁻¹ * k * g⁻¹⁻¹)⁻¹ * t⁻¹)⁻¹ * g⁻¹ := by group
        rw [e]
        exact h2
      have hle : ⁅conjClosure S.V3 S.G1, K⁆ ≤ fsuV1 T V := by
        rw [Subgroup.commutator_le]
        intro u hu k hk
        exact (hUC hu).2.2 k hk
      rw [hUK] at hle
      have h8 := Subgroup.card_le_of_le ((le_conjClosure S.V3 S.G1).trans hle)
      rw [S.card_V3, S.card_V1] at h8
      exact absurd h8 (by norm_num)
    rcases hβ with ⟨β, hβs, hβk, hβe⟩ | ⟨β, hβs, hβk, hβe⟩
    ·
      have hβe' : ∀ (k : ↥K) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = k * u * k⁻¹ →
          Multiplicative.toAdd (β v) =
            (A6Nrm.heartModel).act (α k : Perm (Fin 6)) (Multiplicative.toAdd (β u)) := by
        intro k u v huv
        obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β u))
        rw [← hβe k u v huv x hx, ← hx]
        rfl
      obtain ⟨ρ, hρk, hρK, hρe⟩ :=
        S.exists_rho A6Nrm.heartModel hF1 hKG hKN hαs hαk hβs hβk hβe'
      refine ⟨fun h hh hcomm => ?_, Or.inl ⟨hnhat, ρ, hρk, fun k hk => ?_, fun σ hσ => ?_,
        Or.inl ⟨β, hβs, hβk, fun h u v huv x hx => ?_⟩⟩⟩
      · have hcσ : ∀ σ (hσ : σ ∈ alternatingGroup (Fin 6)), ρ ⟨h, hh⟩ * σ = σ * ρ ⟨h, hh⟩ := by
          intro σ hσ
          obtain ⟨k, hk⟩ := hαs ⟨σ, hσ⟩
          have h1 : ρ (⟨h, hh⟩ * Subgroup.inclusion hKG k * (⟨h, hh⟩ : ↥S.G1)⁻¹ *
              (Subgroup.inclusion hKG k)⁻¹) = 1 := (hρk _).2 (hcomm k k.2)
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
            mul_inv_eq_iff_eq_mul] at h1
          rw [hρK (Subgroup.inclusion hKG k) k.2] at h1
          have e : (⟨((Subgroup.inclusion hKG k : ↥S.G1) : G), k.2⟩ : ↥K) = k := rfl
          rw [e, hk] at h1
          exact h1
        exact (hρk ⟨h, hh⟩).1 (A6Id.eq_one_of_comm_ab _ (hcσ _ A6Coc.aP_mem)
          (hcσ _ A6Coc.bP_mem))
      · rw [hρK k hk]
        exact (α _).2
      · obtain ⟨k, hk⟩ := hαs ⟨σ, hσ⟩
        refine ⟨Subgroup.inclusion hKG k, k.2, ?_⟩
        rw [hρK _ k.2]
        exact congrArg Subtype.val hk
      · rw [hρe h u v huv, ← hx]
        rfl
    ·
      obtain ⟨ρ, hρk, hρK, hρe⟩ :=
        S.exists_rho A6Nrm.evenModel hF1 hKG hKN hαs hαk hβs hβk hβe
      refine ⟨fun h hh hcomm => ?_, Or.inl ⟨hnhat, ρ, hρk, fun k hk => ?_, fun σ hσ => ?_,
        Or.inr ⟨β, hβs, hβk, fun h u v huv => hρe h u v huv⟩⟩⟩
      · have hcσ : ∀ σ (hσ : σ ∈ alternatingGroup (Fin 6)), ρ ⟨h, hh⟩ * σ = σ * ρ ⟨h, hh⟩ := by
          intro σ hσ
          obtain ⟨k, hk⟩ := hαs ⟨σ, hσ⟩
          have h1 : ρ (⟨h, hh⟩ * Subgroup.inclusion hKG k * (⟨h, hh⟩ : ↥S.G1)⁻¹ *
              (Subgroup.inclusion hKG k)⁻¹) = 1 := (hρk _).2 (hcomm k k.2)
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
            mul_inv_eq_iff_eq_mul] at h1
          rw [hρK (Subgroup.inclusion hKG k) k.2] at h1
          have e : (⟨((Subgroup.inclusion hKG k : ↥S.G1) : G), k.2⟩ : ↥K) = k := rfl
          rw [e, hk] at h1
          exact h1
        exact (hρk ⟨h, hh⟩).1 (A6Id.eq_one_of_comm_ab _ (hcσ _ A6Coc.aP_mem)
          (hcσ _ A6Coc.bP_mem))
      · rw [hρK k hk]
        exact (α _).2
      · obtain ⟨k, hk⟩ := hαs ⟨σ, hσ⟩
        refine ⟨Subgroup.inclusion hKG k, k.2, ?_⟩
        rw [hρK _ k.2]
        exact congrArg Subtype.val hk
  · exact absurd h7 (h24 G T L V S hS S.G1 hG1 K hK)
  · exact absurd hU (hG2 G T L V S hS K hK)

theorem input13827Six_of_leaves
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) (h13 : Lem13813) (h16 : Lem13816)
    (h21 : Lem13821) (h24 : Lem13824) (h25 : Lem13825) (h26 : Lem13826) (hG2 : Lem13827G2) :
    Input13827Six :=
  input13827Six_of_ident h13315 h1356two
    (ident13827_of h13315 h1356two h13 h16 h21 h24 h25 h26 hG2)

end CFSG.Quasithin.H13.A6
