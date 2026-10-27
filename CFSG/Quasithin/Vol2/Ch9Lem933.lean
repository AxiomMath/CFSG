module

public import CFSG.Quasithin.Vol2.Ch9Sec3DSB
public import CFSG.Quasithin.Vol2.Ch9Setup

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem inf_normalizer_le' {H K : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hKe : 2 ∣ Nat.card (oTwoQuot ↥K)) :
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ H ⊓ fsuM T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  set M := fsuM T L with hM
  have hTH : T ≤ H := hH.1.1
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
    rw [hHK]
    exact sup_le Subgroup.le_normalizer hTK
  have hTHs : IsSylowTwoOf T H := CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hfsu.sylow hTH
  obtain ⟨P, hP⟩ := exists_sylow_coe_eq hfsu.sylow
  set Y₀ := H ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) with hY₀
  have hTY₀ : T ≤ Y₀ := le_inf hTH fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hs, hTK hs⟩
  have hY₀M : Y₀ ≤ M := by
    by_contra hY₀M
    have hInH : InH T Y₀ := by
      rw [← hP] at hTY₀ ⊢
      exact inH_of_le P hTY₀ inf_le_left (hP ▸ hH.1)
    have hY₀H : Y₀ = H := hH.2.2 Y₀ hInH inf_le_left hY₀M
    have hKN : K ≤ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      intro k hk
      have : k ∈ Y₀ := by rw [hY₀H]; exact hKH hk
      exact this.2
    have hTKs : IsSylowTwoOf (T ⊓ K) K := A4.isSylowTwoOf_inf_normal hTHs hKH hHKn
    have hTKO : T ⊓ K ≤ pCoreOf 2 K :=
      CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer inf_le_right hKN hTKs.2.1
    have hodd : ¬ 2 ∣ (pCoreOf 2 K).relIndex K := by
      intro h2d
      apply hTKs.2.2
      show 2 ∣ (T ⊓ K).relIndex K
      rw [← Subgroup.relIndex_mul_relIndex (T ⊓ K) (pCoreOf 2 K) K hTKO
        (CFSG.LieType.BorelTits.pCoreOf_le 2 K)]
      exact h2d.mul_left _
    apply hodd
    have hidxK : (pCoreOf 2 K).relIndex K = Nat.card (oTwoQuot ↥K) := by
      rw [Subgroup.relIndex, ← Subgroup.index_eq_card]
      congr 1
      exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
    rw [hidxK]
    exact hKe
  exact le_inf (inf_le_left.trans hKH) ((inf_le_inf_right _ hKH).trans
    (le_inf inf_le_left hY₀M) |>.trans inf_le_right)

theorem inf_normalizer_le {H K : Subgroup G}
    (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T) (hKc : K ∈ cComp H)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ H ⊓ fsuM T L :=
  S.inf_normalizer_le' hH hHK hKc hTK (by rw [(oTwoQuot_facts_of_alt_five hKA).1]; norm_num)

end Setup

end CFSG.Quasithin.H13.Ch9
