module

public import CFSG.Quasithin.H13.A6S1372L76A
public import CFSG.Quasithin.H13.A6S13812
public import CFSG.Quasithin.H13.A6Set14
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped IsMulCommutative Pointwise

namespace A6L76Y

theorem t0_c012 : (swap (0 : Fin 6) 1 * swap 4 5) * (swap 0 1 * swap 1 2) *
      (swap 0 1 * swap 4 5)⁻¹ * (swap 0 1 * swap 1 2) = 1 ∧
    (∀ κ ∈ K4L, (swap (0 : Fin 6) 1 * swap 4 5) * κ * (swap 0 1 * swap 4 5)⁻¹ ∈ K4L) ∧
    (swap (0 : Fin 6) 1 * swap 1 2) ∈ S14.C3 ∧ (swap (0 : Fin 6) 1 * swap 1 2) ^ 3 = 1 := by
  decide +kernel

theorem mul_pow_mem {G : Type*} [Group G] {D : Subgroup G} {g d : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) (hd : d ∈ D) (n : ℕ) :
    (g ^ n)⁻¹ * (g * d) ^ n ∈ D := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (g ^ (n + 1))⁻¹ * (g * d) ^ (n + 1) =
        g⁻¹ * ((g ^ n)⁻¹ * (g * d) ^ n) * g⁻¹⁻¹ * d := by
      rw [pow_succ g n, pow_succ (g * d) n]
      group
    rw [e]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp ih) hd

theorem mem_of_mul_pow_odd {G : Type*} [Group G] {C : Subgroup G} {y c : G}
    (hy : y ∈ Subgroup.normalizer (C : Set G)) (hc : c ∈ C) {j m : ℕ} (hyj : y ^ 2 ^ j = 1)
    (hm : Odd m) (hyc : (y * c) ^ m = 1) : y ∈ C := by
  have h1 := mul_pow_mem hy hc m
  rw [hyc, mul_one, inv_mem_iff] at h1
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, pow_one] at hyj
    rw [hyj]
    exact C.one_mem
  have hcop : Nat.Coprime m (2 ^ j) := ((Odd.coprime_two_left hm).pow_left j).symm
  obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_two_pow (Nat.pos_iff_ne_zero.1 hj))
  have e : y ^ (m * k) = y := by
    conv_lhs => rw [← Nat.mod_add_div (m * k) (2 ^ j)]
    rw [pow_add, pow_mul, hyj, one_pow, mul_one, hk, pow_one]
  rw [← e, pow_mul]
  exact C.pow_mem h1 k

theorem conj_mem_centralizerMod {G : Type*} [Group G] {K X₁ : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X₁ : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G))
    {c : G} (hc : c ∈ centralizerMod (pCoreOf 2 K) X₁ K) :
    g * c * g⁻¹ ∈ centralizerMod (pCoreOf 2 K) X₁ K := by
  have hc' : c ∈ X₁ ∧ c ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) ∧
      ∀ u ∈ K, c * u * c⁻¹ * u⁻¹ ∈ pCoreOf 2 K := hc
  obtain ⟨hcX, hcN, hcK⟩ := hc'
  have hgP : g ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 K hgK
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgX c).mp hcX,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgP hcN) (Subgroup.inv_mem _ hgP), fun k hk => ?_⟩
  have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) k).mp hk
  have h2 := (Subgroup.mem_normalizer_iff.mp hgP _).mp (hcK _ hk')
  have e : g * (c * (g⁻¹ * k * g⁻¹⁻¹) * c⁻¹ * (g⁻¹ * k * g⁻¹⁻¹)⁻¹) * g⁻¹ =
      g * c * g⁻¹ * k * (g * c * g⁻¹)⁻¹ * k⁻¹ := by group
  rwa [e] at h2

end A6L76Y

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)

@[expose] noncomputable def X1375 : Subgroup G := by
  classical
  exact if IsHatA6 L then l1plus T L V else S.L1

include S

theorem X1375_of_hat (h : IsHatA6 L) : S.X1375 = l1plus T L V := by
  simp [X1375, h]

theorem X1375_of_not_hat (h : ¬ IsHatA6 L) : S.X1375 = S.L1 := by
  simp [X1375, h]

theorem not_comm_V3_of_plus {X : Subgroup G} (P : S14.PlusData S X) {Y : Subgroup G}
    (hXY : X ≤ Y) (h : ∀ y ∈ Y, ∀ v ∈ S.V3, y * v * y⁻¹ * v⁻¹ ∈ fsuV1 T V) : False := by
  have hle : S.V3 ≤ S.V2 := by
    rw [← P.gen]
    refine conjClosure_le fun x hx v hv => ?_
    have h1 := h x (hXY hx) v (S.V2_le_V3 hv)
    have e : x * v * x⁻¹ = (x * v * x⁻¹ * v⁻¹) * v := by group
    rw [e]
    exact S.V2.mul_mem (S.V1_le_V2 h1) hv
  have h2 := Subgroup.card_le_of_le hle
  rw [S.card_V3, S.card_V2] at h2
  omega

variable {S}

section Tilde

variable {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
include hH

theorem T_le_normalizer_of_plus {X : Subgroup G} (P : S14.PlusData S X) {K : Subgroup G}
    (hK : K ∈ cComp H) (hXK : X ≤ K)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    T ≤ Subgroup.normalizer (K : Set G) := by
  intro t ht
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  by_contra hn
  have hne : K.map (MulAut.conj t).toMonoidHom ≠ K := fun he =>
    hn (LocDbl.map_conj_eq_iff.mp he)
  have hK' : K.map (MulAut.conj t).toMonoidHom ∈ cComp H :=
    LocDbl.map_conj_mem_cComp hK (Subgroup.le_normalizer (hTH ht))
  have hsub : IsSubnormal (K.map (MulAut.conj t).toMonoidHom ⊓ K) K :=
    A3.subnormal_inf_right (subnormal_of_mem_cComp hK') (le_of_mem_cComp hK)
  have hlt : K.map (MulAut.conj t).toMonoidHom ⊓ K < K := by
    refine lt_of_le_of_ne inf_le_right fun he => hne ?_
    have hle : K ≤ K.map (MulAut.conj t).toMonoidHom := he.ge.trans inf_le_left
    exact (LocDbl.eq_of_mem_cComp_of_le hK hK' hle).symm
  have hR := le_solvRad_of_subnormal_lt hK hsub hlt
  have hXK' : X ≤ K.map (MulAut.conj t).toMonoidHom := by
    intro l hl
    have h1 : t⁻¹ * l * t⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (P.T_le (T.inv_mem ht)) l).mp hl
    refine ⟨t⁻¹ * l * t, by simpa using hXK h1, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  refine S.not_comm_V3_of_plus P ((le_inf hXK' hXK).trans hR) fun x hx v hv => ?_
  exact secAct_solvRad_eq_one hH (le_of_mem_cComp hK) hrad hx v (le_conjClosure _ _ hv)

theorem le_normalizer_of_plus (h37 : A37ForSQTK) (h38 : A38ForSQTK) {X : Subgroup G}
    (P : S14.PlusData S X) {K : Subgroup G} (hK : K ∈ cComp H) (hXK : X ≤ K)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    H ≤ Subgroup.normalizer (K : Set G) := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hN := normal_conjClosure_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian h37 h38
    hH.1.2 hTs hK
  have hT := T_le_normalizer_of_plus hH P hK hXK hrad
  have he : conjClosure K T = K :=
    le_antisymm (conjClosure_le fun t ht k hk => (Subgroup.mem_normalizer_iff.mp (hT ht) k).mp hk)
      (le_conjClosure K T)
  rwa [he] at hN


end Tilde

variable (S) in
theorem l0_le_centralizerMod (hhat : IsHatA6 L) {K : Subgroup G}
    (hL1K : S.L1 ≤ Subgroup.normalizer (K : Set G)) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hyp : S.L1 ≤ l1plus T L V ⊔ centralizerMod (pCoreOf 2 K) S.L1 K) :
    l0 L ≤ centralizerMod (pCoreOf 2 K) S.L1 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := l1plus T L V with hXdef
  set C := centralizerMod (pCoreOf 2 K) S.L1 K with hCdef
  have P : S14.PlusData S X := S14.plusData_l1plus S (S.hatL1Plus hhat)
  set X₂ := S14.K4pre S X with hX₂
  have hXL1 : X ≤ S.L1 := P.le_L1
  have hCL1 : C ≤ S.L1 := fun c hc => hc.1
  have hL1C : ∀ l ∈ S.L1, ∀ c ∈ C, l * c * l⁻¹ ∈ C := fun l hl c hc =>
    A6L76Y.conj_mem_centralizerMod (Subgroup.le_normalizer hl) (hL1K hl) hc
  have hTC : ∀ t ∈ T, ∀ c ∈ C, t * c * t⁻¹ ∈ C := fun t ht c hc =>
    A6L76Y.conj_mem_centralizerMod (S.T_le_normalizer_L1 ht) (hTK ht) hc
  have hL1NC : S.L1 ≤ Subgroup.normalizer (C : Set G) := A5.le_normalizer_of_forall_conj_mem hL1C
  have hX₂X : X₂ ≤ X := fun y hy => ((S14.mem_K4pre (S := S)).1 hy).1
  have hX₂2 : IsPGroup 2 X₂ := P.isPGroup_K4pre
  have hXX₂ : ∀ x ∈ X, ∀ y ∈ X₂, x * y * x⁻¹ ∈ X₂ := by
    intro l hl y hy
    obtain ⟨hyL, hyN, hyK⟩ := (S14.mem_K4pre (S := S)).1 hy
    have hlN := P.le_NV hl
    have hN : l * y * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN hyN) (Subgroup.inv_mem _ hlN)
    refine (S14.mem_K4pre (S := S)).2 ⟨X.mul_mem (X.mul_mem hl hyL) (X.inv_mem hl), hN, ?_⟩
    have e : (⟨l * y * l⁻¹, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        ⟨l, hlN⟩ * ⟨y, hyN⟩ * ⟨l, hlN⟩⁻¹ := rfl
    obtain ⟨h4, h5, -⟩ := P.rho (x := ⟨l, hlN⟩) hl
    rw [e, map_mul, map_mul, map_inv]
    exact S14.K4_norm _ ⟨h4, h5⟩ _ hyK
  obtain ⟨hinv, hK4t, hc3, hcube⟩ := A6L76Y.t0_c012
  obtain ⟨x₀, hx₀X, hρx₀⟩ := P.three _ hc3
  obtain ⟨hD6, hs6, -⟩ := S14.t0_facts
  obtain ⟨t, htTL, hρt⟩ := S14.exists_TL_rho S hD6 hs6
  have htT : (t : G) ∈ T := htTL.1
  have htL : (t : G) ∈ L := htTL.2
  have htX : ∀ x ∈ X, (t : G) * x * (t : G)⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (P.T_le htT) x).mp hx
  have htL1 : ∀ y ∈ S.L1, (t : G) * y * (t : G)⁻¹ ∈ S.L1 := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 htT) y).mp hy
  have htX₂ : ∀ y ∈ X₂, (t : G) * y * (t : G)⁻¹ ∈ X₂ := by
    intro y hy
    obtain ⟨hyL, hyN, hyK⟩ := (S14.mem_K4pre (S := S)).1 hy
    have hN : (t : G) * y * (t : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ t.2 hyN) (Subgroup.inv_mem _ t.2)
    refine (S14.mem_K4pre (S := S)).2 ⟨htX y hyL, hN, ?_⟩
    have e : (⟨(t : G) * y * (t : G)⁻¹, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        t * ⟨y, hyN⟩ * t⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hρt]
    exact hK4t _ hyK
  have htx₀ : (t : G) * x₀ * (t : G)⁻¹ * x₀ ∈ X₂ := by
    have hN : (t : G) * x₀ * (t : G)⁻¹ * x₀ ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ t.2 x₀.2)
        (Subgroup.inv_mem _ t.2)) x₀.2
    refine (S14.mem_K4pre (S := S)).2 ⟨X.mul_mem (htX _ hx₀X) hx₀X, hN, ?_⟩
    have e : (⟨(t : G) * x₀ * (t : G)⁻¹ * x₀, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        t * x₀ * t⁻¹ * x₀ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hρt, hρx₀, hinv]
    exact one_mem_K4L
  have hx₀3 : (x₀ : G) ^ 3 ∈ X₂ := by
    refine (S14.mem_K4pre (S := S)).2 ⟨X.pow_mem hx₀X 3, Subgroup.pow_mem _ x₀.2 3, ?_⟩
    have e : (⟨(x₀ : G) ^ 3, Subgroup.pow_mem _ x₀.2 3⟩ :
        ↥(Subgroup.normalizer (V : Set G))) = x₀ ^ 3 := rfl
    rw [e, map_pow, hρx₀, hcube]
    exact one_mem_K4L
  have hXgen : ∀ x ∈ X, x ∈ X₂ ∨ x * (x₀ : G)⁻¹ ∈ X₂ ∨ x * (x₀ : G) ∈ X₂ := by
    intro x hx
    have hxN := P.le_NV hx
    obtain ⟨h4, h5, hs⟩ := P.rho (x := ⟨x, hxN⟩) hx
    rcases A4_gen_K4L _ ⟨h4, h5, hs⟩ with h | h | h
    · exact Or.inl ((S14.mem_K4pre (S := S)).2 ⟨hx, hxN, h⟩)
    · have hN : x * (x₀ : G)⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
        Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ x₀.2)
      refine Or.inr (Or.inl ((S14.mem_K4pre (S := S)).2
        ⟨X.mul_mem hx (X.inv_mem hx₀X), hN, ?_⟩))
      have e : (⟨x * (x₀ : G)⁻¹, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨x, hxN⟩ * x₀⁻¹ :=
        rfl
      rw [e, map_mul, map_inv, hρx₀]
      exact h
    · have hN : x * (x₀ : G) ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hxN x₀.2
      refine Or.inr (Or.inr ((S14.mem_K4pre (S := S)).2 ⟨X.mul_mem hx hx₀X, hN, ?_⟩))
      have e : (⟨x * (x₀ : G), hN⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨x, hxN⟩ * x₀ := rfl
      rw [e, map_mul, hρx₀]
      exact h
  set D := X₂ ⊔ C with hD
  have hX₂NC : X₂ ≤ Subgroup.normalizer (C : Set G) := (hX₂X.trans hXL1).trans hL1NC
  have hDmul : ((D : Subgroup G) : Set G) = (X₂ : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X₂ C hX₂NC
  have hXC : ((X ⊔ C : Subgroup G) : Set G) = (X : Set G) * (C : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right X C (hXL1.trans hL1NC)
  have hsplit : ∀ y ∈ S.L1, ∃ x ∈ X, ∃ c ∈ C, y = x * c := by
    intro y hy
    have hy' : y ∈ (X : Set G) * (C : Set G) := by rw [← hXC]; exact hyp hy
    obtain ⟨x, hx, c, hc, rfl⟩ := Set.mem_mul.mp hy'
    exact ⟨x, hx, c, hc, rfl⟩
  have hL1D : ∀ l ∈ S.L1, ∀ d ∈ D, l * d * l⁻¹ ∈ D := by
    intro l hl d hd
    obtain ⟨x, hx, c, hc, rfl⟩ := hsplit l hl
    have hd' : d ∈ (X₂ : Set G) * (C : Set G) := by rw [← hDmul]; exact hd
    obtain ⟨y, hy, c', hc', rfl⟩ := Set.mem_mul.mp hd'
    have hyc : y⁻¹ * c * y⁻¹⁻¹ ∈ C := hL1C _ (S.L1.inv_mem (hXL1 (hX₂X hy))) c hc
    have e : x * c * (y * c') * (x * c)⁻¹ = (x * y * x⁻¹) *
        (x * ((y⁻¹ * c * y⁻¹⁻¹) * c⁻¹ * (c * c' * c⁻¹)) * x⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left (hXX₂ x hx y hy)) (Subgroup.mem_sup_right ?_)
    exact hL1C x (hXL1 hx) _ (C.mul_mem (C.mul_mem hyc (C.inv_mem hc))
      (hL1C c (hCL1 hc) c' hc'))
  have hDn : (D.subgroupOf S.L1).Normal := ⟨fun d hd l => by
    rw [Subgroup.mem_subgroupOf] at hd ⊢
    simpa using hL1D l l.2 d hd⟩
  set π₁ := QuotientGroup.mk' (D.subgroupOf S.L1) with hπ₁
  have hπ : ∀ (a b : G) (ha : a ∈ S.L1) (hb : b ∈ S.L1), a⁻¹ * b ∈ D →
      π₁ ⟨a, ha⟩ = π₁ ⟨b, hb⟩ := fun a b ha hb h =>
    QuotientGroup.eq.2 (by rw [Subgroup.mem_subgroupOf]; simpa using h)
  have hπ1 : ∀ (a : G) (ha : a ∈ S.L1), a ∈ D → π₁ ⟨a, ha⟩ = 1 := fun a ha h =>
    (QuotientGroup.eq_one_iff _).2 (by rw [Subgroup.mem_subgroupOf]; exact h)
  set x₀' : ↥S.L1 := ⟨x₀, hXL1 hx₀X⟩ with hx₀'
  set q₀ := π₁ x₀' with hq₀
  have hq₀3 : q₀ ^ 3 = 1 := by
    rw [hq₀, ← map_pow]
    exact hπ1 _ _ (Subgroup.mem_sup_left hx₀3)
  have hX₂D : ∀ y ∈ X₂, y ∈ D := fun y hy => Subgroup.mem_sup_left hy
  have hCD : ∀ c ∈ C, c ∈ D := fun c hc => Subgroup.mem_sup_right hc
  have hclass : ∀ x (hx : x ∈ X), (π₁ ⟨x, hXL1 hx⟩ = 1 ∧
      π₁ ⟨(t : G) * x * (t : G)⁻¹, htL1 _ (hXL1 hx)⟩ = 1) ∨
      (π₁ ⟨x, hXL1 hx⟩ = q₀ ∧ π₁ ⟨(t : G) * x * (t : G)⁻¹, htL1 _ (hXL1 hx)⟩ = q₀⁻¹) ∨
      (π₁ ⟨x, hXL1 hx⟩ = q₀⁻¹ ∧ π₁ ⟨(t : G) * x * (t : G)⁻¹, htL1 _ (hXL1 hx)⟩ = q₀) := by
    intro x hx
    have hx₀inv : (x₀ : G)⁻¹ ∈ X := X.inv_mem hx₀X
    rcases hXgen x hx with h | h | h
    · exact Or.inl ⟨hπ1 _ _ (hX₂D _ h), hπ1 _ _ (hX₂D _ (htX₂ _ h))⟩
    · refine Or.inr (Or.inl ⟨(hπ _ _ _ _ ?_).symm, ?_⟩)
      · have e : (x₀ : G)⁻¹ * x = (x₀ : G)⁻¹ * (x * (x₀ : G)⁻¹) * (x₀ : G)⁻¹⁻¹ := by group
        rw [e]
        exact hX₂D _ (hXX₂ _ hx₀inv _ h)
      · have e1 : (q₀⁻¹ : ↥S.L1 ⧸ D.subgroupOf S.L1) = π₁ ⟨(x₀ : G)⁻¹, S.L1.inv_mem x₀'.2⟩ := by
          rw [hq₀, ← map_inv]
          rfl
        rw [e1]
        refine (hπ _ _ _ _ ?_).symm
        have e : (x₀ : G)⁻¹⁻¹ * ((t : G) * x * (t : G)⁻¹) =
            ((x₀ : G) * ((t : G) * (x * (x₀ : G)⁻¹) * (t : G)⁻¹) * (x₀ : G)⁻¹) *
              ((x₀ : G) * ((t : G) * x₀ * (t : G)⁻¹ * x₀) * (x₀ : G)⁻¹) := by group
        rw [e]
        exact hX₂D _ (X₂.mul_mem (hXX₂ _ hx₀X _ (htX₂ _ h)) (hXX₂ _ hx₀X _ htx₀))
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · have e1 : (q₀⁻¹ : ↥S.L1 ⧸ D.subgroupOf S.L1) =
            π₁ ⟨(x₀ : G)⁻¹, S.L1.inv_mem x₀'.2⟩ := by
          rw [hq₀, ← map_inv]
          rfl
        rw [e1]
        refine (hπ _ _ _ _ ?_).symm
        have e : (x₀ : G)⁻¹⁻¹ * x = (x₀ : G) * (x * (x₀ : G)) * (x₀ : G)⁻¹ := by group
        rw [e]
        exact hX₂D _ (hXX₂ _ hx₀X _ h)
      · refine (hπ _ _ _ _ ?_).symm
        have e : (x₀ : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) =
            ((x₀ : G)⁻¹ * ((t : G) * (x * (x₀ : G)) * (t : G)⁻¹) * (x₀ : G)⁻¹⁻¹) *
              ((t : G) * x₀ * (t : G)⁻¹ * x₀)⁻¹ := by group
        rw [e]
        exact hX₂D _ (X₂.mul_mem (hXX₂ _ hx₀inv _ (htX₂ _ h)) (X₂.inv_mem htx₀))
  have hall : ∀ y (hy : y ∈ S.L1), π₁ ⟨y, hy⟩ ^ 3 = 1 ∧
      π₁ ⟨(t : G) * y * (t : G)⁻¹, htL1 _ hy⟩ = (π₁ ⟨y, hy⟩)⁻¹ := by
    intro y hy
    obtain ⟨x, hx, c, hc, rfl⟩ := hsplit y hy
    have e1 : π₁ ⟨x * c, hy⟩ = π₁ ⟨x, hXL1 hx⟩ := (hπ _ _ _ _ (by
      rw [show x⁻¹ * (x * c) = c by group]
      exact hCD _ hc)).symm
    have e2 : π₁ ⟨(t : G) * (x * c) * (t : G)⁻¹, htL1 _ hy⟩ =
        π₁ ⟨(t : G) * x * (t : G)⁻¹, htL1 _ (hXL1 hx)⟩ := (hπ _ _ _ _ (by
      rw [show ((t : G) * x * (t : G)⁻¹)⁻¹ * ((t : G) * (x * c) * (t : G)⁻¹) =
          (t : G) * c * (t : G)⁻¹ by group]
      exact hCD _ (hTC _ htT _ hc))).symm
    rw [e1, e2]
    rcases hclass x hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact ⟨one_pow 3, inv_one.symm⟩
    · rw [h1, h2]
      exact ⟨hq₀3, rfl⟩
    · rw [h1, h2]
      exact ⟨by rw [inv_pow, hq₀3, inv_one], (inv_inv q₀).symm⟩
  show oTwoRes (o2Z L) ≤ C
  refine (Subgroup.closure_le _).2 ?_
  rintro w ⟨hwZ, m, hm, hwm⟩
  have hwL1 : w ∈ S.L1 := S.l0_le_L1 (Subgroup.subset_closure ⟨hwZ, m, hm, hwm⟩)
  obtain ⟨hwL, hwc⟩ := mem_o2Z_iff.1 hwZ
  set o := (t : G) * w * (t : G)⁻¹ * w⁻¹ with ho
  have hoP : o ∈ pCoreOf 2 L := by
    have h1 := hwc _ (L.inv_mem htL)
    have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L htL) _).mp h1
    have e : (t : G) * (w * (t : G)⁻¹ * w⁻¹ * (t : G)⁻¹⁻¹) * (t : G)⁻¹ = o := by
      rw [ho]
      group
    rwa [e] at h2
  have hoL1 : o ∈ S.L1 := S.L1.mul_mem (htL1 _ hwL1) (S.L1.inv_mem hwL1)
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨o, hoP⟩
  have hoj : o ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hπo : π₁ ⟨o, hoL1⟩ = 1 := by
    have h3 := (hall o hoL1).1
    have h2 : π₁ ⟨o, hoL1⟩ ^ 2 ^ j = 1 := by
      rw [← map_pow]
      have e : (⟨o, hoL1⟩ : ↥S.L1) ^ 2 ^ j = 1 := Subtype.ext (by simpa using hoj)
      rw [e, map_one]
    have h4 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
    have hcop : Nat.Coprime (2 ^ j) 3 := Nat.Coprime.pow_left _ (by norm_num)
    rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  have hwD : w ∈ D := by
    obtain ⟨hw3, hwt⟩ := hall w hwL1
    have e : (⟨(t : G) * w * (t : G)⁻¹, htL1 _ hwL1⟩ : ↥S.L1) = ⟨o, hoL1⟩ * ⟨w, hwL1⟩ :=
      Subtype.ext (by
        show (t : G) * w * (t : G)⁻¹ = o * w
        rw [ho]
        group)
    rw [e, map_mul, hπo, one_mul] at hwt
    have h2 : π₁ ⟨w, hwL1⟩ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [hwt]
      exact inv_mul_cancel _
    have h1 : π₁ ⟨w, hwL1⟩ = 1 := by
      have e' : π₁ ⟨w, hwL1⟩ = π₁ ⟨w, hwL1⟩ ^ 3 * (π₁ ⟨w, hwL1⟩ ^ 2)⁻¹ := by group
      rw [e', hw3, h2, inv_one, one_mul]
    have := (QuotientGroup.eq_one_iff _).1 h1
    rwa [Subgroup.mem_subgroupOf] at this
  have hwD' : w ∈ (X₂ : Set G) * (C : Set G) := by rw [← hDmul]; exact hwD
  obtain ⟨y, hy, c, hc, hyc⟩ := Set.mem_mul.mp hwD'
  obtain ⟨k, hk⟩ := hX₂2 ⟨y, hy⟩
  have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hyC : y ∈ C := A6L76Y.mem_of_mul_pow_odd (hX₂NC hy) hc hyk hm (by rw [hyc]; exact hwm)
  rw [← hyc]
  exact C.mul_mem hyC hc


variable (S)

theorem le_normalizer_l0_of {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (h0 : l0 L ≤ centralizerMod (pCoreOf 2 K) S.L1 K) :
    K ≤ Subgroup.normalizer (l0 L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans hH.1.1
  have hPT : pCoreOf 2 K ≤ T :=
    ((GoldS146R.inf_pCoreOf_eq_of_mem_cComp hK).symm.le.trans inf_le_right).trans
      (pCoreOf_le_of_sylow S.h13.sylow hTH)
  refine A5.le_normalizer_of_forall_conj_mem fun k hk y hy => ?_
  have hkP : k ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K hk
  induction hy using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨hwZ, m, hm, hwm⟩ := hw
    have hwL0 : w ∈ l0 L := Subgroup.subset_closure ⟨hwZ, m, hm, hwm⟩
    have hwC : w ∈ S.L1 ∧ w ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) ∧
        ∀ u ∈ K, w * u * w⁻¹ * u⁻¹ ∈ pCoreOf 2 K := h0 hwL0
    set p := k * w * k⁻¹ * w⁻¹ with hp
    have hpP : p ∈ pCoreOf 2 K := by
      have h1 := (Subgroup.mem_normalizer_iff.mp hkP _).mp (hwC.2.2 _ (K.inv_mem hk))
      have e : k * (w * k⁻¹ * w⁻¹ * k⁻¹⁻¹) * k⁻¹ = p := by
        rw [hp]
        group
      rwa [e] at h1
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 K) ⟨p, hpP⟩
    have hpj : p ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hpN : p ∈ Subgroup.normalizer (l0 L : Set G) :=
      S.normalizer_le_l0 (S.frame.T_le (hPT hpP))
    have hpw : p * w = k * w * k⁻¹ := by
      rw [hp]
      group
    have hm' : (p * w) ^ m = 1 := by
      rw [hpw, conj_pow, hwm, mul_one, mul_inv_cancel]
    have hpL0 := A6L76Y.mem_of_mul_pow_odd hpN hwL0 hpj hm hm'
    rw [← hpw]
    exact (l0 L).mul_mem hpL0 hwL0
  | one => simp
  | mul a b _ _ ha hb =>
    have e : k * (a * b) * k⁻¹ = (k * a * k⁻¹) * (k * b * k⁻¹) := by group
    rw [e]
    exact (l0 L).mul_mem ha hb
  | inv a _ ha =>
    have e : k * a⁻¹ * k⁻¹ = (k * a * k⁻¹)⁻¹ := by group
    rw [e]
    exact (l0 L).inv_mem ha

theorem lem1375_seven (h139 : Stmt13_3_9) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
    {K : Subgroup G} (hK : K ∈ cComp H) (hXK : S.X1375 ≤ K) (hL1K : ¬ S.L1 ≤ K)
    (hrad : ∀ N : Subgroup ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))), N.Normal → Group.IsSolvable ↥N → N = ⊥) :
    ¬ S.L1 ≤ S.X1375 ⊔ centralizerMod (pCoreOf 2 K) S.L1 K := by
  intro hyp
  by_cases hhat : IsHatA6 L
  · rw [S.X1375_of_hat hhat] at hXK hyp
    have P : S14.PlusData S (l1plus T L V) := S14.plusData_l1plus S (S.hatL1Plus hhat)
    have hHK := le_normalizer_of_plus hH h37 h38 P hK hXK hrad
    have hTH : T ≤ H := le_sup_right.trans hH.1.1
    have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
    have h0 := S.l0_le_centralizerMod hhat (hL1H.trans hHK) (hTH.trans hHK) hyp
    have hKM : K ≤ Subgroup.normalizer (L : Set G) :=
      (S.le_normalizer_l0_of hH hK h0).trans (S.normalizer_l0_le_M hhat)
    exact (S.lem13812_one h139 h37 h38 hH hK).1 hKM
  · rw [S.X1375_of_not_hat hhat] at hXK
    exact hL1K hXK

end Setting4

end CFSG.Quasithin.H13.A6
