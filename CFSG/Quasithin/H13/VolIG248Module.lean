module

public import CFSG.Quasithin.H13.VolIG248Basic
public import CFSG.Quasithin.Background.G2A5CoreWrap
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.Quasithin.A5Model Subgroup
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

namespace G248

theorem sl2_sub_injective {F : Type*} [Field F] [CharP F 2] {m : SL(2, F)} (h3 : m ^ 3 = 1)
    (h1 : m ≠ 1) {s : ℕ} :
    Function.Injective (fun w : Fin s → Fin 2 → F => fun j => m • w j - w j) := by
  intro w w' h
  funext j
  have hj : (m : Matrix (Fin 2) (Fin 2) F).mulVec (w j) - w j =
      (m : Matrix (Fin 2) (Fin 2) F).mulVec (w' j) - w' j := congrFun h j
  by_contra hne
  apply h1
  refine sl2_eq_one_of_fixed h3 (v := w j - w' j) (sub_ne_zero.2 hne) ?_
  show (m : Matrix (Fin 2) (Fin 2) F).mulVec (w j - w' j) = w j - w' j
  rw [Matrix.mulVec_sub]
  rwa [sub_eq_sub_iff_sub_eq_sub] at hj

namespace Setting

variable [Finite G] {V V₁ L T H : Subgroup G} {g : G} (X : Setting V V₁ L T H g)
include X

theorem S_le_N : pCoreOf 2 L ≤ normalizer (V₁ : Set G) := fun _ hx =>
  X.St.hyp.base.T_le_normV₁ (X.St.O_le_T ((X.mem_pCoreOf_L_iff (pCoreOf_le 2 L hx)).1 hx))

theorem comm_mem_Q {t y : G} (ht : t ∈ lOne L V₁) (hy : y ∈ pCoreOf 2 L) :
    t * y * t⁻¹ * y⁻¹ ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply X.O2
  have hyL := pCoreOf_le 2 L hy
  have hyN : y ∈ normalizer (lOne L V₁ : Set G) :=
    le_normalizer_oTwoUpper _ ⟨hyL, X.S_le_N hy⟩
  have h1 : y * t⁻¹ * y⁻¹ ∈ lOne L V₁ := (mem_normalizer_iff.mp hyN _).mp (inv_mem ht)
  have hc1 : t * y * t⁻¹ * y⁻¹ ∈ lOne L V₁ := by
    have e : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
    rw [e]
    exact mul_mem ht h1
  have hc2 : t * y * t⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
    have h2 : t * y * t⁻¹ ∈ pCoreOf 2 L :=
      (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (lOne_le_L ht)) y).mp hy
    exact mul_mem h2 (inv_mem hy)
  have hle : pCoreOf 2 L ⊓ lOne L V₁ ≤ pCoreOf 2 (lOne L V₁) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((pCoreOf_isPGroup 2 L).to_le inf_le_left)
    intro l hl
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer_pCoreOf 2 L (lOne_le_L hl),
      le_normalizer_oTwoUpper _ ((oTwoUpper_le _) hl)⟩
  exact hle ⟨hc2, hc1⟩

theorem pCoreOf_L_eq : pCoreOf 2 L = conjClosure V₁ L := by
  obtain ⟨t, ht, htθ⟩ := X.exists_t
  have hb := X.St.hyp.base
  have hg := X.St.hyp.g22
  obtain ⟨⟨s, hsum⟩, hc2, hc3, hc4⟩ := X.St.hyp.G24_six' (U := conjClosure V H) (I := L)
    (S := pCoreOf 2 L) (W := conjClosure V H ⊓ pCoreOf 2 L) rfl X.hg X.hgN X.I_eq.symm rfl rfl
  obtain ⟨-, -, -, hLVL, -, -⟩ := X.St.hyp.G24_four (U := conjClosure V H) (I := L)
    (S := pCoreOf 2 L) rfl X.hg X.hgN X.I_eq.symm rfl
  rw [X.S₂_eq] at hsum hc2 hc3 hc4
  obtain ⟨β, φ, -, hβk, hφs, hφk, hequiv⟩ := hsum
  have hβ3 : β t ^ 3 = 1 := by
    rw [← map_pow]
    refine (hβk _).2 ((X.theta_eq_one_iff _).1 ?_)
    rw [map_pow, htθ, c3A_pow]
  have hβ1 : β t ≠ 1 := by
    intro h
    have h1 := (X.theta_eq_one_iff t).2 ((hβk t).1 h)
    rw [htθ] at h1
    exact absurd h1 (by decide)
  have hsurj : Function.Surjective
      (fun w : Fin s → Fin 2 → GaloisField 2 2 => fun j => β t • w j - w j) :=
    Finite.injective_iff_surjective.1 (sl2_sub_injective hβ3 hβ1)
  have hS_t : ∀ y ∈ pCoreOf 2 L, ∃ y' ∈ pCoreOf 2 L,
      y⁻¹ * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹) ∈ conjClosure V₁ L := by
    intro y hy
    obtain ⟨w, hw⟩ := hsurj (Multiplicative.toAdd (φ ⟨y, hy⟩))
    obtain ⟨y', hy'⟩ := hφs (Multiplicative.ofAdd w)
    have hty' : (t : G) * y' * (t : G)⁻¹ ∈ pCoreOf 2 L :=
      (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L t.2) _).mp y'.2
    have he := hequiv t y' ⟨_, hty'⟩ rfl
    refine ⟨y', y'.2, ?_⟩
    have h1 : φ (⟨y, hy⟩⁻¹ * (⟨_, hty'⟩ * y'⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, he, hy']
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_mul, toAdd_inv, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_one,
        ← hw]
      funext j
      simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]
      abel
    have h2 := (hφk _).1 h1
    simpa [mul_assoc] using h2
  have hUcent : ∀ x ∈ pCoreOf 2 L, ∀ u ∈ conjClosure V H, ⁅u, x⁆ ∈ conjClosure V₁ L := by
    intro x hx u hu
    obtain ⟨y', hy', hxy⟩ := hS_t x hx
    have hcQ := X.comm_mem_Q ht hy'
    have hcN : (t : G) * y' * (t : G)⁻¹ * y'⁻¹ ∈ normalizer (V₁ : Set G) :=
      mul_mem (mul_mem (mul_mem (lOne_le_N ht) (X.S_le_N hy')) (inv_mem (lOne_le_N ht)))
        (inv_mem (X.S_le_N hy'))
    have hcS : (t : G) * y' * (t : G)⁻¹ * y'⁻¹ ∈ pCoreOf 2 L := by
      have h2 : (t : G) * y' * (t : G)⁻¹ ∈ pCoreOf 2 L :=
        (mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L t.2) y').mp hy'
      exact mul_mem h2 (inv_mem hy')
    have hs : (x⁻¹ * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹))⁻¹ ∈ conjClosure V₁ L := inv_mem hxy
    have h1 : u * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹) * u⁻¹ *
        ((t : G) * y' * (t : G)⁻¹ * y'⁻¹)⁻¹ ∈ conjClosure V₁ L :=
      le_conjClosure V₁ L (comm_Q_mem_core hb hg hu hcQ hcN)
    have h2 : u * (x⁻¹ * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹))⁻¹ * u⁻¹ *
        (x⁻¹ * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹))⁻¹⁻¹ ∈ conjClosure V₁ L :=
      mul_mem ((mem_normalizer_iff.mp (hLVL (X.U_le_L hu)) _).mp hs) (inv_mem hs)
    have h3 := (mem_normalizer_iff.mp (hLVL (pCoreOf_le 2 L hcS)) _).mp h2
    have e : ⁅u, x⁆ = (u * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹) * u⁻¹ *
        ((t : G) * y' * (t : G)⁻¹ * y'⁻¹)⁻¹) *
        (((t : G) * y' * (t : G)⁻¹ * y'⁻¹) * (u * (x⁻¹ * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹))⁻¹ *
          u⁻¹ * (x⁻¹ * ((t : G) * y' * (t : G)⁻¹ * y'⁻¹))⁻¹⁻¹) *
          ((t : G) * y' * (t : G)⁻¹ * y'⁻¹)⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem h1 h3
  have hSW : pCoreOf 2 L ≤ (conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L := fun x hx =>
    (hc4 x hx).2 (fun u hu => hUcent x hx u hu)
  have hWS : (conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L = pCoreOf 2 L := by
    refine le_antisymm ?_ hSW
    calc (conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L
        ≤ ((conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L) ⊔
          (rconj (conjClosure V H ⊓ pCoreOf 2 L) g ⊔ conjClosure V₁ L) := le_sup_left
      _ = pCoreOf 2 L := hc3.symm
  have hWg : rconj (conjClosure V H ⊓ pCoreOf 2 L) g ⊔ conjClosure V₁ L ≤
      (conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L := by
    rw [hWS]
    calc rconj (conjClosure V H ⊓ pCoreOf 2 L) g ⊔ conjClosure V₁ L
        ≤ ((conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L) ⊔
          (rconj (conjClosure V H ⊓ pCoreOf 2 L) g ⊔ conjClosure V₁ L) := le_sup_right
      _ = pCoreOf 2 L := hc3.symm
  have hWgV : rconj (conjClosure V H ⊓ pCoreOf 2 L) g ≤ conjClosure V₁ L :=
    calc rconj (conjClosure V H ⊓ pCoreOf 2 L) g
        ≤ rconj (conjClosure V H ⊓ pCoreOf 2 L) g ⊔ conjClosure V₁ L := le_sup_left
      _ = ((conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L) ⊓
          (rconj (conjClosure V H ⊓ pCoreOf 2 L) g ⊔ conjClosure V₁ L) :=
        (inf_eq_right.2 hWg).symm
      _ = conjClosure V₁ L := hc2
  have hWV : conjClosure V H ⊓ pCoreOf 2 L ≤ conjClosure V₁ L := by
    intro w hw
    have h1 : g⁻¹ * w * g ∈ rconj (conjClosure V H ⊓ pCoreOf 2 L) g := by
      rw [mem_rconj]
      simpa [mul_assoc] using hw
    have h3 := (mem_normalizer_iff.mp (hLVL X.hg) _).mp (hWgV h1)
    simpa [mul_assoc] using h3
  calc pCoreOf 2 L = (conjClosure V H ⊓ pCoreOf 2 L) ⊔ conjClosure V₁ L := hWS.symm
    _ = conjClosure V₁ L := sup_eq_right.2 hWV

theorem card_U : Nat.card (conjClosure V H) = 32 := by
  obtain ⟨s, hsum, hcard⟩ := X.St.hyp.G24_seven' (U := conjClosure V H) (I := L)
    (S := pCoreOf 2 L) (W := conjClosure V H ⊓ pCoreOf 2 L) rfl X.hg X.hgN X.I_eq.symm rfl rfl
  rw [X.S₂_eq, relIndex_self, mul_one] at hcard
  rw [X.S₂_eq] at hsum
  obtain ⟨-, φ, -, -, hφs, hφk, -⟩ := hsum
  have hs0 : s = 0 := by
    by_contra hs
    obtain ⟨x, hx⟩ := hφs (Multiplicative.ofAdd (fun _ _ => (1 : GaloisField 2 2)))
    have hxV : (x : G) ∈ conjClosure V₁ L := by
      rw [← X.pCoreOf_L_eq]
      exact x.2
    rw [(hφk x).2 hxV] at hx
    have h1 := congrArg (fun m => (Multiplicative.toAdd m) ⟨0, Nat.pos_of_ne_zero hs⟩ 0) hx
    simp at h1
  rw [hcard, hs0]
  norm_num

theorem mem_V_of_comm {x : G} (hxVL : x ∈ conjClosure V₁ L)
    (hxU : ∀ u ∈ conjClosure V H, u * x * u⁻¹ * x⁻¹ ∈ V₁) : x ∈ V := by
  refine (X.St.D.hV ⟨x, hxVL⟩).2 ?_
  refine coord_four_eq_zero_of_comm_K4 (Multiplicative.toAdd (X.St.D.ψ ⟨x, hxVL⟩)) ?_
  intro k hk
  rw [← X.St.Ubar_eq_K4] at hk
  obtain ⟨u, rfl⟩ := hk
  have huLU : (u : G) ∈ L ⊔ conjClosure V H :=
    (le_sup_right : conjClosure V H ≤ L ⊔ conjClosure V H) u.2
  have hα : X.St.D.alpha ⟨u, X.St.LU_le_normVL huLU⟩ =
      pact ((X.St.betaU u : A5) : Equiv.Perm (Fin 5)) := (X.St.pactA_Phi ⟨u, huLU⟩).symm
  have hc : ((conjAct (conjClosure V₁ L) ⟨u, X.St.LU_le_normVL huLU⟩ ⟨x, hxVL⟩ *
      ⟨x, hxVL⟩⁻¹ : conjClosure V₁ L) : G) ∈ V₁ := by
    rw [Subgroup.coe_mul, conjAct_coe_apply, Subgroup.coe_inv]
    exact hxU u u.2
  have h := (X.St.D.line _).1 hc
  rw [map_mul, map_inv, ← X.St.D.alpha_psi, hα] at h
  rcases h with h | h
  · left
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_mul, toAdd_inv, toAdd_pact] at h'
    simpa [sub_eq_add_neg] using h'
  · right
    have h' := congrArg Multiplicative.toAdd h
    rw [toAdd_mul, toAdd_inv, toAdd_pact] at h'
    simpa [W4, sub_eq_add_neg] using h'

theorem U_le_pCoreOf_lOne : conjClosure V H ≤ pCoreOf 2 (lOne L V₁) := by
  have hb := X.St.hyp.base
  have hUL₁ : conjClosure V H ≤ lOne L V₁ := by
    rw [← X.comm]
    refine sup_le ?_ ?_
    · rw [commutator_le]
      intro u hu l hl
      have huN : u ∈ normalizer (lOne L V₁ : Set G) :=
        le_normalizer_oTwoUpper _ ⟨X.U_le_L hu, X.St.U_le_normV₁ hu⟩
      rw [commutatorElement_def]
      have h1 : u * l * u⁻¹ ∈ lOne L V₁ := (mem_normalizer_iff.mp huN l).mp hl
      exact mul_mem h1 (inv_mem hl)
    · refine hb.le_V.trans ?_
      rw [X.St.hyp.V_eq, commutator_le]
      intro v hv l hl
      have hvN : v ∈ normalizer (lOne L V₁ : Set G) := le_normalizer_oTwoUpper _
        ⟨X.VL_le_L hv, hb.T_le_normV₁ (X.St.O_le_T (X.St.VL_le_O hv))⟩
      rw [commutatorElement_def]
      have h1 : v * l * v⁻¹ ∈ lOne L V₁ := (mem_normalizer_iff.mp hvN l).mp hl
      exact mul_mem h1 (inv_mem hl)
  exact le_pCoreOf_of_le_normalizer 2 hUL₁ X.lOne_le_normU X.St.isPGroup_U

theorem U_eq : conjClosure V H = pCoreOf 2 (lOne L V₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := X.St.hyp.base
  have hg := X.St.hyp.g22
  refine le_antisymm X.U_le_pCoreOf_lOne fun x hx => ?_
  have hxL₁ : x ∈ lOne L V₁ := pCoreOf_le 2 _ hx
  have hxL : x ∈ L := lOne_le_L hxL₁
  have hθK : X.St.D.θ ⟨x, hxL⟩ ∈ K4 := by
    have hA := X.theta_lOne hxL₁
    apply mem_K4_of_pow_four _ hA
    obtain ⟨k, hk⟩ := exists_pow_two_pow_eq_one_of_mem (pCoreOf_isPGroup 2 (lOne L V₁)) hx
    have h2k : X.St.D.θ ⟨x, hxL⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxL⟩ : ↥L) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h12 := A4s_pow_twelve _ hA
    refine eq_one_of_pow_three_of_pow_two_pow (x := X.St.D.θ ⟨x, hxL⟩ ^ 4) (k := k) ?_ ?_
    · rw [← pow_mul]
      exact h12
    · rw [← pow_mul, mul_comm, pow_mul, h2k, one_pow]
  rw [← X.St.Ubar_eq_K4] at hθK
  obtain ⟨u, hu⟩ := hθK
  have huL : (u : G) ∈ L := X.U_le_L u.2
  have hθu : X.St.D.θ ⟨u, huL⟩ = X.St.betaU u := by
    rw [A5SettingCore.betaU_apply, ← X.St.Phi_of_L ⟨u, huL⟩]
  have hs : (u : G)⁻¹ * x ∈ conjClosure V₁ L := by
    rw [← X.pCoreOf_L_eq]
    have h1 : X.St.D.θ ((⟨u, huL⟩ : ↥L)⁻¹ * ⟨x, hxL⟩) = 1 := by
      rw [map_mul, map_inv, hθu, hu, inv_mul_cancel]
    exact (X.theta_eq_one_iff _).1 h1
  have hsQ : (u : G)⁻¹ * x ∈ pCoreOf 2 H :=
    X.O2 (mul_mem (inv_mem (X.U_le_pCoreOf_lOne u.2)) hx)
  have hsN : (u : G)⁻¹ * x ∈ normalizer (V₁ : Set G) :=
    mul_mem (inv_mem (X.St.U_le_normV₁ u.2)) (lOne_le_N hxL₁)
  have hsV : (u : G)⁻¹ * x ∈ V :=
    X.mem_V_of_comm hs fun u' hu' => comm_Q_mem_core hb hg hu' hsQ hsN
  have e : x = u * ((u : G)⁻¹ * x) := by group
  rw [e]
  exact mul_mem u.2 (le_conjClosure V H hsV)

end Setting

end G248

end CFSG.Quasithin.H13.VolI
