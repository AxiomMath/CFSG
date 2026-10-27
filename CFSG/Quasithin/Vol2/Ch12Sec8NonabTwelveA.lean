module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabElevenFive
public import CFSG.Quasithin.Vol2.Ch12Sec8NonabHatImg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

namespace HatModel

variable {G : Type} [Group G] {T M : Subgroup G} (D : HatModel T M)

instance finite_linearEquiv : Finite (D.V ≃ₗ[ZMod 2] D.V) :=
  Finite.of_injective (fun e : D.V ≃ₗ[ZMod 2] D.V => (e : D.V → D.V))
    (fun _ _ he => LinearEquiv.ext (congrFun he))

theorem card_hat {A : Subgroup G} (hAU : A ≤ uOfL22 T M) :
    Nat.card (D.hat A) = (A ⊓ centerOf (uOfL22 T M)).relIndex A := by
  classical
  let φ : ↥A →* Multiplicative D.V :=
    { toFun := fun e => Multiplicative.ofAdd (D.π (e : G))
      map_one' := by
        show Multiplicative.ofAdd (D.π (1 : G)) = 1
        rw [D.π_one, ofAdd_zero]
      map_mul' := fun e e' => by
        show Multiplicative.ofAdd (D.π ((e : G) * (e' : G))) =
          Multiplicative.ofAdd (D.π (e : G)) * Multiplicative.ofAdd (D.π (e' : G))
        rw [D.π_mul _ (hAU e.2) _ (hAU e'.2), ofAdd_add] }
  have hker : φ.ker = (A ⊓ centerOf (uOfL22 T M)).subgroupOf A := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro he
      have h0 : D.π (e : G) = 0 := by
        have := congrArg Multiplicative.toAdd he
        simpa [φ] using this
      exact ⟨e.2, (D.π_eq_zero_iff (hAU e.2)).mp h0⟩
    · rintro ⟨-, hZ⟩
      have := (D.π_eq_zero_iff (hAU e.2)).mpr hZ
      show Multiplicative.ofAdd (D.π (e : G)) = 1
      rw [this]
      rfl
  have e : φ.range ≃ D.hat A :=
    { toFun := fun x => ⟨Multiplicative.toAdd (x : Multiplicative D.V), by
        obtain ⟨y, hy⟩ := x.2
        rw [← hy]
        exact D.π_mem_hat y.2 (hAU y.2)⟩
      invFun := fun v => ⟨Multiplicative.ofAdd (v : D.V), by
        obtain ⟨a, haA, haU, hπ⟩ := D.mem_hat.mp v.2
        exact ⟨⟨a, haA⟩, by
          show Multiplicative.ofAdd (D.π a) = Multiplicative.ofAdd (v : D.V)
          rw [hπ]⟩⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }
  have h1 : (A ⊓ centerOf (uOfL22 T M)).relIndex A = φ.ker.index := by
    rw [hker]
    rfl
  rw [h1, Subgroup.index_ker]
  exact (Nat.card_congr e).symm

theorem card_V : Nat.card D.V = (centerOf (uOfL22 T M)).relIndex (uOfL22 T M) := by
  have hZU : centerOf (uOfL22 T M) ≤ uOfL22 T M := inf_le_left
  have h1 := D.card_hat (A := uOfL22 T M) le_rfl
  rw [inf_eq_right.mpr hZU] at h1
  rw [← h1]
  have htop : D.hat (uOfL22 T M) = ⊤ := by
    ext v
    simp only [Submodule.mem_top, iff_true]
    obtain ⟨u, hu, rfl⟩ := D.π_surj v
    exact D.π_mem_hat hu hu
  rw [htop]
  exact (Nat.card_congr Submodule.topEquiv.toEquiv).symm

end HatModel

namespace Hyp1281Two

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

theorem rconj_wOfU_le_centralizer_VZ (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    rconj (wOfU T M) g ≤ Subgroup.centralizer (VZ T M : Set G) := by
  intro x hx
  have h1 : x ∈ pCoreOf 2 (L ⊔ uOfL22 T M) := h.rconj_wOfU_le_pCoreOf hU hg hx
  rw [h.pCoreOf_sup_uOfL22_eq hU hg] at h1
  exact h1.2

theorem rconj_wOfU_le_normalizer_uOfL22 (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    rconj (wOfU T M) g ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
  (h.rconj_wOfU_le_T hU hg).trans h.T_le_normalizer_uOfL22

theorem rho_eq_one_iff_mem_inf (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M) {x : G}
    (hxX : x ∈ rconj (wOfU T M) g) :
    D.rho ⟨x, h.rconj_wOfU_le_normalizer_uOfL22 hU hg hxX⟩ = 1 ↔
      x ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
  have hxN := h.rconj_wOfU_le_normalizer_uOfL22 hU hg hxX
  constructor
  · intro h1
    rw [← (h.lemma_12_8_9_five hU hg).1]
    exact ⟨hxX, normalizer_le_normalizer_centerOf _ hxN,
      (D.rho_eq_one_iff ⟨x, hxN⟩).mp h1⟩
  · intro hxE
    rw [← (h.lemma_12_8_9_five hU hg).1] at hxE
    exact (D.rho_eq_one_iff ⟨x, hxN⟩).mpr hxE.2.2

theorem rank_eq (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) (D : HatModel T M) :
    Module.finrank (ZMod 2) (D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) +
      Nat.log 2 ((D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex
        (D.img (rconj (wOfU T M) g))) = Module.finrank (ZMod 2) D.V - 1 := by
  classical
  have hXN := h.rconj_wOfU_le_normalizer_uOfL22 hU hg
  have hEU : wOfU T M ⊓ rconj (wOfU T M) g ≤ uOfL22 T M :=
    inf_le_left.trans (wOfU_le_uOfL22 T M)
  have hEX : wOfU T M ⊓ rconj (wOfU T M) g ≤ rconj (wOfU T M) g := inf_le_right
  have hZgX : rconj (centerOf (uOfL22 T M)) g ≤ rconj (wOfU T M) g :=
    rconj_centerOf_le_rconj_wOfU T M g
  have hker : ∀ x ∈ rconj (wOfU T M) g, (∃ hxN : x ∈ Subgroup.normalizer (uOfL22 T M : Set G),
      D.rho ⟨x, hxN⟩ = 1) ↔ x ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
    intro x hxX
    constructor
    · rintro ⟨hxN, h1⟩
      exact (h.rho_eq_one_iff_mem_inf hU hg D hxX).mp h1
    · intro hxE
      exact ⟨hXN hxX, (h.rho_eq_one_iff_mem_inf hU hg D hxX).mpr hxE⟩
  have ha : Nat.card (D.img (rconj (wOfU T M) g)) =
      (wOfU T M ⊓ rconj (wOfU T M) g).relIndex (rconj (wOfU T M) g) :=
    HatModel.card_img_eq_relIndex hXN hker
  have hK : rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g) ≤
      rconj (wOfU T M) g := sup_le hZgX hEX
  have hb : Nat.card (D.img (rconj (centerOf (uOfL22 T M)) g)) =
      (wOfU T M ⊓ rconj (wOfU T M) g).relIndex
        (rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)) := by
    rw [← h.img_sup_eq_of_le D (hZgX.trans hXN) hEU]
    exact HatModel.card_img_eq_relIndex (hK.trans hXN) (fun x hx => hker x (hK hx))
  have hmul : (wOfU T M ⊓ rconj (wOfU T M) g).relIndex
      (rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)) *
      (rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)).relIndex
        (rconj (wOfU T M) g) = (wOfU T M ⊓ rconj (wOfU T M) g).relIndex (rconj (wOfU T M) g) :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hK
  have hle : D.img (rconj (centerOf (uOfL22 T M)) g) ≤ D.img (rconj (wOfU T M) g) :=
    HatModel.img_mono hZgX
  have hcard : (D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex
      (D.img (rconj (wOfU T M) g)) *
      Nat.card (D.img (rconj (centerOf (uOfL22 T M)) g)) =
        Nat.card (D.img (rconj (wOfU T M) g)) := by
    have := Subgroup.relIndex_mul_card (D.img (rconj (centerOf (uOfL22 T M)) g))
      (D.img (rconj (wOfU T M) g))
    rwa [inf_eq_left.mpr hle] at this
  have hbpos : 0 < Nat.card (D.img (rconj (centerOf (uOfL22 T M)) g)) := Nat.card_pos
  have hr : (D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex (D.img (rconj (wOfU T M) g)) =
      (rconj (centerOf (uOfL22 T M)) g ⊔ (wOfU T M ⊓ rconj (wOfU T M) g)).relIndex
        (rconj (wOfU T M) g) := by
    apply Nat.eq_of_mul_eq_mul_right hbpos
    rw [hcard, ha, ← hmul, hb, mul_comm]
  have h5 := h.lemma_12_8_11_five hU hg
  rw [← hr, ← D.card_hat hEU, ← D.card_V] at h5
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.hat (wOfU T M ⊓ rconj (wOfU T M) g)),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.V)] at h5
  simp only [Nat.card_zmod] at h5
  set e := Module.finrank (ZMod 2) (D.hat (wOfU T M ⊓ rconj (wOfU T M) g)) with he
  set d := Module.finrank (ZMod 2) D.V with hd
  set r := (D.img (rconj (centerOf (uOfL22 T M)) g)).relIndex (D.img (rconj (wOfU T M) g)) with hrdef
  have hrd : r ∣ 2 ^ d := ⟨2 * 2 ^ e, by rw [← h5]; ring⟩
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrd
  rw [hk] at h5
  have h6 : 2 ^ (1 + e + k) = 2 ^ d := by rw [← h5]; ring
  have h7 : 1 + e + k = d := Nat.pow_right_injective (le_refl 2) h6
  rw [hk, Nat.log_pow (by norm_num : 1 < 2)]
  omega

end Hyp1281Two

end CFSG.Quasithin
