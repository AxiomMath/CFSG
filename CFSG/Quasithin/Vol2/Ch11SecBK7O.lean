module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.Ch11SecANat
public import CFSG.Quasithin.Vol2.Ch11SecBFacts21
public import CFSG.Quasithin.Vol2.Ch11SecBK7F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin Matrix
open CFSG.Quasithin.Vol2.KGNat
open CFSG.Assembly.LowTwoRank (StatedSp specialLinearGroupEquivStatedSL)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.ClassicalInvolution.ModelFacts.OddCover (Usp)
open scoped IsMulCommutative

namespace K7

theorem exists_fixed_ne {Q Y : Type*} [Group Q] (hQ : IsPGroup 2 Q) (act : Q → Y → Y)
    (h1 : ∀ y, act 1 y = y) (hmul : ∀ a b y, act (a * b) y = act a (act b y)) {S : Set Y}
    [Finite S] (hS : ∀ a, ∀ y ∈ S, act a y ∈ S) (heven : 2 ∣ Nat.card S) {y₀ : Y}
    (hy₀ : y₀ ∈ S) (hfix₀ : ∀ a, act a y₀ = y₀) : ∃ y ∈ S, y ≠ y₀ ∧ ∀ a, act a y = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulAction Q S :=
    { smul := fun a y => ⟨act a y, hS a y y.2⟩
      one_smul := fun y => Subtype.ext (h1 y)
      mul_smul := fun a b y => Subtype.ext (hmul a b y) }
  obtain ⟨b, hb, hne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point S heven
    (a := ⟨y₀, hy₀⟩) fun a => Subtype.ext (hfix₀ a)
  exact ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun a => congrArg Subtype.val (hb a)⟩

variable {K : Type} [Field K]

theorem eq_trv_of_range [CharP K 2] {γ : ↥(StatedSp 2 K)} {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0)
    (hγ : ∀ x, ∃ d : K, mat 2 K γ *ᵥ x - x = d • y) : ∃ c : K, γ = trv y c := by
  obtain ⟨x₁, hx₁⟩ := exists_bil_eq_one hy
  refine eq_trv_of_fix hy fun x hx => ?_
  obtain ⟨d, hd⟩ := hγ x
  obtain ⟨d₁, hd₁⟩ := hγ x₁
  have e := spB_mat γ x x₁
  rw [show mat 2 K γ *ᵥ x = x + d • y by rw [← hd]; abel,
    show mat 2 K γ *ᵥ x₁ = x₁ + d₁ • y by rw [← hd₁]; abel] at e
  simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, bil_self, hx,
    mul_zero, add_zero] at e
  rw [bil_comm y x₁, hx₁, mul_one, add_eq_left] at e
  rw [← sub_eq_zero, hd, e, zero_smul]

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem trv_injective (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) {c c' : K}
    (h : ((π (trv y c) : ↥H) : MulAut W) = ((π (trv y c') : ↥H) : MulAut W)) : c = c' := by
  have h1 : trv y c = trv y c' := hf.injective_nat (Subtype.ext h)
  obtain ⟨x₁, hx₁⟩ := exists_bil_eq_one hy
  have h2 := congrArg (fun γ => mat 2 K γ *ᵥ x₁) h1
  simp only [trv_mulVec, hx₁, mul_one, add_right_inj] at h2
  exact smul_left_injective K hy h2

variable {G : Type} [Group G]

theorem exists_coord_sp4 [Finite G] {L V T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hnat : NatModuleOf L V n)
    (hk : KindSp4 L V n) (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (_ : IsMulCommutative ↥V) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ n ∧
      ∃ (π : ↥(StatedSp 2 K) →* ↥(autOn L V)) (f : ↥V → (Fin 2 ⊕ Fin 2 → K))
        (_ : IsCoord (linModelNat (StatedSp 2 K)) (autOn L V)
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f) (g : StatedSp 2 K),
        ∀ x : MulAut ↥V, x ∈ autOn (T ⊓ L) V ↔
          ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L V)) : MulAut ↥V) := by
  obtain ⟨hcomm, hnat⟩ := hnat
  refine ⟨hcomm, ?_⟩
  obtain ⟨K, _, _, hK, π, hπ⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L V),
        (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥V) (autOn L V) ⊤
          ((Subgroup.centralizer (L : Set G)).subgroupOf V) π := by
    rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | h | ⟨K, _, _, hK, π, hπ⟩
    · obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
      have hbij : Function.Bijective π := ⟨hf.injective_nat, hf.onto⟩
      exact (SecA.kind_not_SL3_Sp4 (by omega) ⟨K, inferInstance, inferInstance, hK,
        ⟨(MulEquiv.ofBijective π hbij).symm.trans
          (specialLinearGroupEquivStatedSL 3 K).symm⟩⟩ hk).elim
    · exact h
    · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
      obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
      obtain ⟨f, hf⟩ := exists_isCoord (G2Q8.lmG K) hπ
      have hbij : Function.Bijective π := by
        refine ⟨fun a b hab => ?_, hf.onto⟩
        set e := MulEquiv.subgroupCongr (G2Q8.g2Derived_eq hc0 hc1).symm with he
        obtain ⟨a', rfl⟩ := e.surjective a
        obtain ⟨b', rfl⟩ := e.surjective b
        exact congrArg e ((G2Q8.rhoG_bijective hf hc0 hc1).1
          (show G2Q8.rhoG hc0 hc1 π a' = G2Q8.rhoG hc0 hc1 π b' from hab))
      exact (SecA.kind_not_Sp4_G2 KGNat.factG2DerivedOrder_holds hn hk
        ⟨K, inferInstance, inferInstance, hK, ⟨(MulEquiv.ofBijective π hbij).symm⟩⟩).elim
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usp hK (by omega) hf
    (SecA.isSylowTwoOf_autOn hLV hTL')
  exact ⟨K, inferInstance, inferInstance, inferInstance, hK, π, f, hf, g, hg⟩

end K7

end CFSG.Quasithin.Vol2.Ch11.SecB
