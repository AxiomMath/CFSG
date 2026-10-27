module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4Red
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsEleven
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace L128A

namespace HatU

variable {G : Type} [Group G] {U : Subgroup G} (D : HatModelU U)

instance finite_linearEquiv : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
  Finite.of_injective (fun e : D.V ≃ₗ[ZMod 2] D.V => (e : D.V → D.V))
    (fun _ _ he => LinearEquiv.ext (congrFun he))

theorem card_hat {A : Subgroup G} (hAU : A ≤ U) :
    Nat.card (D.hat A) = (A ⊓ centerOf U).relIndex A := by
  classical
  let φ : ↥A →* Multiplicative D.V :=
    { toFun := fun e => Multiplicative.ofAdd (D.π (e : G))
      map_one' := by
        show Multiplicative.ofAdd (D.π (1 : G)) = 1
        rw [π_one D, ofAdd_zero]
      map_mul' := fun e e' => by
        show Multiplicative.ofAdd (D.π ((e : G) * (e' : G))) =
          Multiplicative.ofAdd (D.π (e : G)) * Multiplicative.ofAdd (D.π (e' : G))
        rw [D.π_mul _ (hAU e.2) _ (hAU e'.2), ofAdd_add] }
  have hker : φ.ker = (A ⊓ centerOf U).subgroupOf A := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro he
      have h0 : D.π (e : G) = 0 := by
        have := congrArg Multiplicative.toAdd he
        simpa [φ] using this
      exact ⟨e.2, (π_eq_zero_iff D (hAU e.2)).mp h0⟩
    · rintro ⟨-, hZ⟩
      have := (π_eq_zero_iff D (hAU e.2)).mpr hZ
      show Multiplicative.ofAdd (D.π (e : G)) = 1
      rw [this]
      rfl
  have e : φ.range ≃ D.hat A :=
    { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative D.V), by
        obtain ⟨y, hy⟩ := x.2
        rw [← hy]
        exact π_mem_hat D y.2 (hAU y.2)⟩
      invFun := fun v => ⟨Multiplicative.ofAdd (v : D.V), by
        obtain ⟨a, haA, haU, hπ⟩ := (mem_hat D).mp v.2
        exact ⟨⟨a, haA⟩, by
          show Multiplicative.ofAdd (D.π a) = Multiplicative.ofAdd (v : D.V)
          rw [hπ]⟩⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  have h1 : (A ⊓ centerOf U).relIndex A = φ.ker.index := by
    rw [hker]
    rfl
  rw [h1, Subgroup.index_ker]
  exact (Nat.card_congr e).symm

theorem card_V : Nat.card D.V = (centerOf U).relIndex U := by
  have hZU : centerOf U ≤ U := inf_le_left
  have h1 := card_hat D (A := U) le_rfl
  rw [inf_eq_right.mpr hZU] at h1
  rw [← h1]
  have htop : D.hat U = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    exact π_mem_hat D hu hu
  rw [htop]
  exact (Nat.card_congr Submodule.topEquiv.toEquiv).symm

end HatU

namespace Setting

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

variable {G : Type} [Group G] [Finite G] {V V₁ L T : Subgroup G}

theorem rconj_wA_le_centralizer_V (S : Setting V V₁ L T)
    {g : G} (hg : Good V₁ L g) :
    rconj (wA V V₁) g ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have h1 : x ∈ pCoreOf 2 (L ⊔ uA V V₁) := S.rconj_wA_le_pCoreOf hg hx
  rw [S.pCoreOf_sup_eq hg] at h1
  exact h1.2

theorem rconj_wA_le_normalizer_uA (S : Setting V V₁ L T)
    {g : G} (hg : Good V₁ L g) :
    rconj (wA V V₁) g ≤ Subgroup.normalizer (uA V V₁ : Set G) :=
  (S.rconj_wA_le_T hg).trans S.T_le_normalizer_uA

theorem rho_eq_one_iff_mem_inf (S : Setting V V₁ L T)
    {g : G} (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) {x : G}
    (hxX : x ∈ rconj (wA V V₁) g) :
    D.ρ ⟨x, S.rconj_wA_le_normalizer_uA hg hxX⟩ = 1 ↔
      x ∈ wA V V₁ ⊓ rconj (wA V V₁) g := by
  have hxN := S.rconj_wA_le_normalizer_uA hg hxX
  constructor
  · intro h1
    rw [← (S.nine_five hg).1]
    exact ⟨hxX, normalizer_le_normalizer_centerOf _ hxN,
      (HatU.rho_eq_one_iff D ⟨x, hxN⟩).mp h1⟩
  · intro hxE
    rw [← (S.nine_five hg).1] at hxE
    exact (HatU.rho_eq_one_iff D ⟨x, hxN⟩).mpr hxE.2.2

theorem rank_eq (S : Setting V V₁ L T)
    {g : G} (hg : Good V₁ L g) (D : HatModelU (uA V V₁)) :
    Module.finrank (ZMod 2) (D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) +
      Nat.log 2 ((D.img (rconj (centerOf (uA V V₁)) g)).relIndex
        (D.img (rconj (wA V V₁) g))) = Module.finrank (ZMod 2) D.V - 1 := by
  classical
  have hXN := S.rconj_wA_le_normalizer_uA hg
  have hEU : wA V V₁ ⊓ rconj (wA V V₁) g ≤ uA V V₁ :=
    inf_le_left.trans (wA_le_uA V V₁)
  have hEX : wA V V₁ ⊓ rconj (wA V V₁) g ≤ rconj (wA V V₁) g := inf_le_right
  have hZgX : rconj (centerOf (uA V V₁)) g ≤ rconj (wA V V₁) g :=
    rconj_centerOf_le_rconj_wA V V₁ g
  have hker : ∀ x ∈ rconj (wA V V₁) g, (∃ hxN : x ∈ Subgroup.normalizer (uA V V₁ : Set G),
      D.ρ ⟨x, hxN⟩ = 1) ↔ x ∈ wA V V₁ ⊓ rconj (wA V V₁) g := by
    intro x hxX
    constructor
    · rintro ⟨hxN, h1⟩
      exact (S.rho_eq_one_iff_mem_inf hg D hxX).mp h1
    · intro hxE
      exact ⟨hXN hxX, (S.rho_eq_one_iff_mem_inf hg D hxX).mpr hxE⟩
  have ha : Nat.card (D.img (rconj (wA V V₁) g)) =
      (wA V V₁ ⊓ rconj (wA V V₁) g).relIndex (rconj (wA V V₁) g) :=
    HatU.card_img_eq_relIndex D hXN hker
  have hK : rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g) ≤
      rconj (wA V V₁) g := sup_le hZgX hEX
  have hb : Nat.card (D.img (rconj (centerOf (uA V V₁)) g)) =
      (wA V V₁ ⊓ rconj (wA V V₁) g).relIndex
        (rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)) := by
    rw [← HatU.img_sup_eq_of_le D S.commutator_mem_centerOf
      (hZgX.trans hXN) hEU]
    exact HatU.card_img_eq_relIndex D (hK.trans hXN) (fun x hx => hker x (hK hx))
  have hmul : (wA V V₁ ⊓ rconj (wA V V₁) g).relIndex
      (rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)) *
      (rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)).relIndex
        (rconj (wA V V₁) g) = (wA V V₁ ⊓ rconj (wA V V₁) g).relIndex (rconj (wA V V₁) g) :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hK
  have hle : D.img (rconj (centerOf (uA V V₁)) g) ≤ D.img (rconj (wA V V₁) g) :=
    L1294.img_mono D hZgX
  have hcard : (D.img (rconj (centerOf (uA V V₁)) g)).relIndex
      (D.img (rconj (wA V V₁) g)) *
      Nat.card (D.img (rconj (centerOf (uA V V₁)) g)) =
        Nat.card (D.img (rconj (wA V V₁) g)) := by
    have := Subgroup.relIndex_mul_card (D.img (rconj (centerOf (uA V V₁)) g))
      (D.img (rconj (wA V V₁) g))
    rwa [inf_eq_left.mpr hle] at this
  have hbpos : 0 < Nat.card (D.img (rconj (centerOf (uA V V₁)) g)) := Nat.card_pos
  have hr : (D.img (rconj (centerOf (uA V V₁)) g)).relIndex (D.img (rconj (wA V V₁) g)) =
      (rconj (centerOf (uA V V₁)) g ⊔ (wA V V₁ ⊓ rconj (wA V V₁) g)).relIndex
        (rconj (wA V V₁) g) := by
    apply Nat.eq_of_mul_eq_mul_right hbpos
    rw [hcard, ha, ← hmul, hb, mul_comm]
  have h5 := S.eleven_five hg
  rw [← hr, ← HatU.card_hat D hEU, ← HatU.card_V D] at h5
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V)] at h5
  simp only [Nat.card_zmod] at h5
  set e := Module.finrank (ZMod 2) (D.hat (wA V V₁ ⊓ rconj (wA V V₁) g)) with he
  set d := Module.finrank (ZMod 2) D.V with hd
  set r := (D.img (rconj (centerOf (uA V V₁)) g)).relIndex (D.img (rconj (wA V V₁) g)) with hrdef
  have hrd : r ∣ 2 ^ d := ⟨2 * 2 ^ e, by rw [← h5]; ring⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrd
  rw [hk] at h5
  have h6 : 2 ^ (1 + e + k) = 2 ^ d := by rw [← h5]; ring
  have h7 : 1 + e + k = d := Nat.pow_right_injective (le_refl 2) h6
  rw [hk, Nat.log_pow (by norm_num : 1 < 2)]
  omega

end Setting

end L128A

end CFSG.Quasithin.H13
