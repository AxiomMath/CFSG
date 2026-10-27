module

public import CFSG.Quasithin.Background.SimsG46
public import CFSG.Quasithin.Background.SimsG47
public import CFSG.Quasithin.Background.SimsG4Weak
public import CFSG.Quasithin.Background.SimsG4Orth
public import CFSG.Quasithin.Background.SimsG45Odd
public import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem transv_orderOf_two_or_odd [Finite F] [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4) (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) :
    ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀, orderOf (a * b) = 2 ∨ Odd (orderOf (a * b)) := by
  intro a ha b hb
  obtain ⟨u, hu, c, hc, hau, -⟩ :=
    CFSG.Quasithin.SimsG45.exists_transv_form B halt hnd a (hSp ha.1) ha.2.1
  obtain ⟨w, -, d, hd, hbw, -⟩ :=
    CFSG.Quasithin.SimsG45.exists_transv_form B halt hnd b (hSp hb.1) hb.2.1
  by_cases huw : B u w = 0
  · have hcomm : a * b = b * a :=
      (CFSG.Quasithin.SimsG45.transv_commute_iff B halt hnd hu hc hd hau hbw).mpr huw
    have hsq : (a * b) ^ 2 = 1 := by
      rw [pow_two, mul_assoc, ← mul_assoc b a b, ← hcomm, mul_assoc a b b,
        CFSG.Quasithin.SimsG45.transv_mul_self B halt hbw, mul_one,
        CFSG.Quasithin.SimsG45.transv_mul_self B halt hau]
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hsq) with h | h
    · exact Or.inr (by rw [h]; exact odd_one)
    · exact Or.inl h
  · exact Or.inr (CFSG.Quasithin.SimsG45.odd_orderOf_transv_mul B hdim halt hc hd hau hbw huw)

theorem transvGen_irred_prim_of_connected [Finite F] [CharP F 2] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty)
    (hodd : ∀ a ∈ transvSet G₀, ∀ b ∈ transvSet G₀,
      orderOf (a * b) = 2 ∨ Odd (orderOf (a * b)))
    (hconn : (advGraph G₀).Connected) :
    IsIrredOnV (transvGen G₀) ∧ ¬ IsImprimitiveOnV (transvGen G₀) := by
  have htrans := (connected_iff_transitive (transvSet G₀) hD
    (fun d hd => transv_mul_self d hd.2)
    (fun g hg d hd => conj_mem_transvSet (transvGen_le G₀ hg) hd) hodd).mp hconn
  have hirrG := transvGen_irred_of_transitive G₀ hirr hD htrans
  refine ⟨hirrG, fun himp => ?_⟩
  have hD' : (transvSet (transvGen G₀)).Nonempty := by
    rw [transvSet_transvGen]
    exact hD
  exact not_connected_of_imprimitive B halt hnd hdim (transvGen G₀)
    ((transvGen_le G₀).trans hSp) hirrG hD' himp
    ((advGraph_transvGen_connected_iff G₀).mpr hconn)

theorem g47
    [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty) (hconn : (advGraph G₀).Connected) :
    G₀ = transvGen G₀ := by
  have hodd := transv_orderOf_two_or_odd B halt hnd hdim G₀ hSp
  obtain ⟨hirrG, hprimG⟩ :=
    transvGen_irred_prim_of_connected B halt hnd hdim G₀ hSp hirr hD hodd hconn
  rcases weak_form n hn B halt hnd hdim G₀ hSp hirr hD with
    ⟨b, F₀, hb, hmem⟩ | ⟨Q, hQB, hQ⟩ | ⟨V₁, V₂, h1, h2, h3, hperm⟩
  · exact (case1_of_subfield n hn B halt hnd hdim G₀ b F₀ hb hmem).1.symm
  · obtain ⟨k, hk⟩ := case2_of_orth orthIdent_holds n hn B halt hnd hdim G₀ hSp hD hirrG hprimG Q hQB hQ
    exact hk.1.symm
  · exact absurd hconn (not_connected_of_imprimitive B halt hnd hdim G₀ hSp hirr hD
      (imprimitive_of_decW B hdim G₀ V₁ V₂ h1 h2 h3 hperm))

theorem g41
    [Finite F] [CharP F 2] (n : ℕ) (hn : Nat.card F = 2 ^ n)
    (B : LinearMap.BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) (hdim : Module.finrank F V = 4)
    (G₀ : Subgroup (V ≃ₗ[F] V)) (hSp : G₀ ≤ spGroup B) (hirr : IsIrredOnV G₀)
    (hD : (transvSet G₀).Nonempty) :
    G41Case1 n B G₀ ∨ G41Case2 n B G₀ ∨ G41Case3 n B G₀ := by
  have hodd := transv_orderOf_two_or_odd B halt hnd hdim G₀ hSp
  by_cases hconn : (advGraph G₀).Connected
  · obtain ⟨hirrG, hprimG⟩ :=
      transvGen_irred_prim_of_connected B halt hnd hdim G₀ hSp hirr hD hodd hconn
    rcases weak_form n hn B halt hnd hdim G₀ hSp hirr hD with
      ⟨b, F₀, hb, hmem⟩ | ⟨Q, hQB, hQ⟩ | ⟨V₁, V₂, h1, h2, h3, hperm⟩
    · exact Or.inl (case1_of_subfield n hn B halt hnd hdim G₀ b F₀ hb hmem)
    · obtain ⟨k, hgen, Q', b, F₀, hdata⟩ :=
        case2_of_orth orthIdent_holds n hn B halt hnd hdim G₀ hSp hD hirrG hprimG Q hQB hQ
      exact Or.inr (Or.inl ⟨hgen, Q', b, F₀, k, hdata⟩)
    · exact absurd hconn (not_connected_of_imprimitive B halt hnd hdim G₀ hSp hirr hD
        (imprimitive_of_decW B hdim G₀ V₁ V₂ h1 h2 h3 hperm))
  · exact Or.inr (Or.inr ((g46 n hn B halt hnd hdim G₀ hSp hirr hD hodd).2.2.mp hconn))

end CFSG.Quasithin.SimsG4
