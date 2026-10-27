module

public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.Quasithin.Background.SimsE22Fix
public import CFSG.Quasithin.Background.SimsE22Model
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.SimsE22

open CFSG.Open CFSG.QuasithinUnique

theorem exists_involution_of_inf_eq {Y : Type} [Group Y] [Finite Y] {Ks Ts Ms TKs : Subgroup Y}
    (hmin : MinParabolic (⊤ : Subgroup Y) Ts Ms) (hKT : Ks ⊔ Ts = ⊤) (hTKs : TKs ≤ Ts)
    (hTKK : TKs ≤ Ks)
    (hMK : Ms ⊓ Ks = Ks ⊓ Subgroup.centralizer
      ((TKs ⊓ Subgroup.centralizer (TKs : Set Y) : Subgroup Y) : Set Y)) :
    ∃ z ∈ Ks, z ≠ 1 ∧ z * z = 1 ∧ ∀ m ∈ Ms ⊓ Ks, m * z = z * m := by
  have hZ2 : IsPGroup 2 ↥(TKs ⊓ Subgroup.centralizer (TKs : Set Y)) :=
    hmin.isSylow.2.1.to_le (inf_le_left.trans hTKs)
  have hZne : TKs ⊓ Subgroup.centralizer (TKs : Set Y) ≠ ⊥ := by
    intro hbot
    have hKM : Ks ≤ Ms := fun k hk => by
      have hk' : k ∈ Ms ⊓ Ks := by
        rw [hMK]
        refine ⟨hk, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
        have h1 : h = 1 := by
          have hh' : h ∈ TKs ⊓ Subgroup.centralizer (TKs : Set Y) := hh
          rw [hbot] at hh'
          exact Subgroup.mem_bot.mp hh'
        rw [h1, one_mul, mul_one]
      exact hk'.1
    have htop : (⊤ : Subgroup Y) ≤ Ms := hKT ▸ sup_le hKM hmin.le
    exact hmin.maximal.1.ne (top_le_iff.mp htop)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ : ∃ z : ↥(TKs ⊓ Subgroup.centralizer (TKs : Set Y)), orderOf z = 2 := by
    rcases hZ2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.card_eq_one.mp h1) hZne
    · exact exists_prime_orderOf_dvd_card' 2 h2
  have hz' : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe, hz]
  refine ⟨z, hTKK z.2.1, fun h1 => ?_, ?_, fun m hm => ?_⟩
  · rw [h1, orderOf_one] at hz'
    exact absurd hz' (by norm_num)
  · have := pow_orderOf_eq_one (z : Y)
    rwa [hz', pow_two] at this
  · rw [hMK] at hm
    exact ((Subgroup.mem_centralizer_iff.mp hm.2) z z.2).symm

theorem exists_not_innerFieldAt {Γ : Type} [Group Γ] [Finite Γ] {H T M K : Subgroup Γ}
    (hmin : MinParabolic H T M) (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hK : IsPSL 2 p 2 ↥(E2.star M H K))
    (hMK : E2.star M H (M ⊓ K) = E2.star M H K ⊓ Subgroup.centralizer
      ((E2.star M H (T ⊓ K) ⊓ Subgroup.centralizer (E2.star M H (T ⊓ K) : Set (E2.StarQuot M H)) :
        Subgroup (E2.StarQuot M H)) : Set (E2.StarQuot M H))) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ 2 ∧
      ∃ φ : ↥(E2.star M H K) ≃* StatedProj (StatedSL 2 F),
        ∃ t ∈ E2.star M H T, ¬ InnerFieldAt (E2.star M H K) φ t := by
  have hKH : K ≤ H := hHK ▸ le_sup_left
  have hTH : T ≤ H := hmin.isSylow.1
  haveI : Finite (E2.StarQuot M H) := E2P.finite_starQuot M H
  have hKn : (E2.star M H K).Normal := by
    have hHN : H ≤ Subgroup.normalizer (K : Set Γ) := by
      rw [hHK]
      exact sup_le Subgroup.le_normalizer hTK
    have hn : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
    rw [E2P.star_def]
    exact hn.map _ (E2P.starMap_surjective M H)
  have hKT : E2.star M H K ⊔ E2.star M H T = ⊤ := by
    have hsup : E2.star M H (K ⊔ T) = E2.star M H K ⊔ E2.star M H T := by
      unfold E2.star
      rw [Subgroup.subgroupOf_sup hKH hTH, Subgroup.map_sup]
    rw [← hsup, ← hHK, E2P.star_top]
  have hminS := E2P.minParabolic_star hmin
  have hmono : ∀ {X X' : Subgroup Γ}, X ≤ X' → E2.star M H X ≤ E2.star M H X' :=
    fun h => Subgroup.map_mono (Subgroup.subgroupOf_mono H h)
  have hz := exists_involution_of_inf_eq hminS hKT (hmono inf_le_left) (hmono inf_le_right)
    (by rw [← E2P.star_inf_M, hMK])
  have hKs : IsSimpleGroup ↥(E2.star M H K) :=
    StatedAPI.isSimpleGroup_of_statedClassicalModel_psl_two hK
  obtain ⟨-, F, _, _, hF, ⟨φ⟩⟩ := hK
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F p := charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hF])
  have hp2 : p ≠ 2 := by omega
  refine ⟨F, inferInstance, inferInstance, hF, φ, ?_⟩
  by_contra hcon
  push Not at hcon
  exact false_of_innerField hminS hKn hKs φ (X0 F) (odd_index_X0 p hp2 hF) (X0_ne_top p hp2 hF)
    (fun g σ hg => exists_conj_of_innerField g hg σ) (unip F) (unip_mem_X0 F) (unip_ne_one F)
    (fun z hc hz => eq_one_of_commute_unip p hp2 z hc hz) hz hcon

end CFSG.Quasithin.SimsE22
