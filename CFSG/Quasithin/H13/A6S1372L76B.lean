module

public import CFSG.RankThree.PartOne.S11d.PSLRank
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.HMathieuStatements
public import CFSG.Quasithin.H13.A6S1372SixteenTilde

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace A6L76B

@[expose] def E9Pair {X : Type*} [Group X] (a b : X) : Prop :=
  a * b = b * a ∧ a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ a * a

instance {X : Type*} [Group X] [DecidableEq X] (a b : X) : Decidable (E9Pair a b) := by
  unfold E9Pair; infer_instance

theorem E9Pair.map {X Y : Type*} [Group X] [Group Y] {a b : X} (h : E9Pair a b) (f : X →* Y)
    (hf : Function.Injective f) : E9Pair (f a) (f b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by rw [← map_mul, h1, map_mul], by rw [← map_pow, h2, map_one],
    by rw [← map_pow, h3, map_one], fun e => h4 (hf (by rw [e, map_one])),
    fun e => h5 (hf (by rw [e, map_one])), fun e => h6 (hf e),
    fun e => h7 (hf (by rw [e, map_mul]))⟩

theorem E9Pair.indep {X : Type*} [Group X] {a b : X} (h : E9Pair a b) :
    ∀ i j : ℤ, a ^ i * b ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
  obtain ⟨-, ha3, hb3, ha1, hb1, hba, hbaa⟩ := h
  have hoa : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hpow : ∀ k : ℤ, a ^ k = 1 ∨ a ^ k = a ∨ a ^ k = a * a := by
    intro k
    rw [← zpow_mod_orderOf, hoa]
    have hk : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by omega
    rcases hk with hk | hk | hk <;> rw [hk]
    · left; exact zpow_zero a
    · right; left; exact zpow_one a
    · right; right; rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, sq]
  intro i j hij
  have hbj : b ^ j = a ^ (-i) := by
    rw [zpow_neg]
    exact eq_inv_of_mul_eq_one_right hij
  have hj : (3 : ℤ) ∣ j := by
    by_contra hj
    have hjj : j * j % ((3 : ℕ) : ℤ) = 1 := by
      have : j % 3 = 1 ∨ j % 3 = 2 := by omega
      push_cast
      rcases this with h | h <;> simp [Int.mul_emod, h]
    have hb : b = a ^ (-i * j) := by
      rw [zpow_mul, ← hbj, ← zpow_mul, ← zpow_mod_orderOf, hob, hjj, zpow_one]
    rcases hpow (-i * j) with h | h | h
    · exact hb1 (hb.trans h)
    · exact hba (hb.trans h)
    · exact hbaa (hb.trans h)
  refine ⟨?_, hj⟩
  obtain ⟨k, rfl⟩ := hj
  have h1 : b ^ (3 * k) = 1 := by
    rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hb3, one_zpow]
  rw [h1, mul_one] at hij
  have h2 := orderOf_dvd_iff_zpow_eq_one.mpr hij
  rw [hoa] at h2
  exact_mod_cast h2

theorem two_le_pRank_of_e9 {X : Type*} [Group X] [Finite X] {Y : Subgroup X} {a b : X}
    (ha : a ∈ Y) (hb : b ∈ Y) (h : E9Pair a b) : 2 ≤ CFSG.Open.pRank 3 Y := by
  have h' : E9Pair (⟨a, ha⟩ : ↥Y) ⟨b, hb⟩ :=
    ⟨Subtype.ext h.1, Subtype.ext (by simpa using h.2.1), Subtype.ext (by simpa using h.2.2.1),
      fun e => h.2.2.2.1 (congrArg Subtype.val e), fun e => h.2.2.2.2.1 (congrArg Subtype.val e),
      fun e => h.2.2.2.2.2.1 (congrArg Subtype.val e),
      fun e => h.2.2.2.2.2.2 (congrArg Subtype.val e)⟩
  have h2 := CFSG.RankThree.PartOne.two_le_pRank_of_two_elements Nat.prime_three
    (Commute.eq h'.1 |> fun e => (e : Commute _ _)) h'.2.1 h'.2.2.1 h'.indep
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y]
  exact h2

theorem pRank_map_le {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    [hp : Fact p.Prime] (φ : A →* B) (hker : ¬ p ∣ Nat.card φ.ker) (X : Subgroup A) :
    CFSG.Open.pRank p (X.map φ) ≤ CFSG.Open.pRank p X := by
  set ψ := φ.domRestrict X with hψ
  have hkerψ : ¬ p ∣ Nat.card ψ.ker := by
    rw [hψ, MonoidHom.ker_domRestrict]
    have h1 : Nat.card (φ.ker.subgroupOf X) = Nat.card (φ.ker ⊓ X : Subgroup A) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective X.subtype_injective]
    rw [h1]
    exact fun h => hker (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have e : ↥X ⧸ ψ.ker ≃* ↥(X.map φ) :=
    (QuotientGroup.quotientKerEquivRange ψ).trans
      (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range X φ))
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (X.map φ),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup X,
    ← CFSG.SectionRank.pRank_quotient_eq ψ.ker hkerψ]
  exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.out.one_lt e).ge

theorem apply_eq_of_cube {V : Type*} [CommGroup V] (hV : ∀ v : V, v * v = 1) {ψ : MulAut V}
    (hψ : ψ ^ 3 = 1) {x c : V} (hx : ψ x = c * x) (hc : ψ c = c) : ψ x = x := by
  have h3 : (ψ ^ 3) x = c * (c * (c * x)) := by
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hx, map_mul, hc, hx,
      map_mul, hc, map_mul, hc, hx]
  rw [hψ, MulAut.one_apply] at h3
  have hc1 : c = 1 := by
    have h4 : c * (c * (c * x)) = c * x := by rw [← mul_assoc, hV c, one_mul]
    rw [h4] at h3
    exact (mul_eq_right.mp h3.symm)
  rw [hx, hc1, one_mul]

theorem fix_of_realizesBy {V : Type*} [CommGroup V] (hV : ∀ v : V, v * v = 1) {D : FFModel}
    {Y : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥Y}
    {β : ↥U →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy D Y U Z π β) (hZ : Z ≤ fixV Y) {γ : D.Gam}
    (hγ : γ ^ 3 = 1) {x : ↥U} {m : D.Amb} (hm : m ∈ D.sec)
    (hxm : β x = QuotientGroup.mk ⟨m, hm⟩) (hfix : D.act γ m * m⁻¹ ∈ D.ker) :
    ((π γ : ↥Y) : MulAut V) (x : V) = x := by
  obtain ⟨-, hZU, hks, hYU, -, hsec, -, -, hβk, hβe⟩ := hR
  have hxU : ((π γ : ↥Y) : MulAut V) (x : V) ∈ U := hYU _ _ x.2
  have hm' : D.act γ m ∈ D.sec := hsec γ m hm
  have h1 := hβe γ x ⟨m, hm⟩ hxU hm' hxm
  have h2 : β ⟨_, hxU⟩ = β x := by
    rw [h1, hxm]
    refine (QuotientGroup.eq).2 ?_
    rw [Subgroup.mem_subgroupOf]
    have e : ((⟨D.act γ m, hm'⟩ : ↥D.sec)⁻¹ * ⟨m, hm⟩ : ↥D.sec) = ⟨(D.act γ m * m⁻¹)⁻¹,
        D.sec.inv_mem (D.sec.mul_mem hm' (D.sec.inv_mem hm))⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      exact mul_comm _ _
    rw [e]
    exact D.ker.inv_mem hfix
  set c : V := ((π γ : ↥Y) : MulAut V) (x : V) * (x : V)⁻¹ with hcdef
  have hcU : c ∈ U := U.mul_mem hxU (U.inv_mem x.2)
  have hcZ : c ∈ Z := by
    have h3 : β ⟨c, hcU⟩ = 1 := by
      have e : (⟨c, hcU⟩ : ↥U) = ⟨_, hxU⟩ * x⁻¹ := rfl
      rw [e, map_mul, map_inv, h2, mul_inv_cancel]
    exact (hβk _).1 h3
  have hψ3 : ((π γ : ↥Y) : MulAut V) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hγ, map_one, Subgroup.coe_one]
  refine apply_eq_of_cube hV hψ3 (c := c) ?_ (hZ hcZ _ (π γ).2)
  rw [hcdef, inv_mul_cancel_right]

end A6L76B

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem pRank_three_centralizer_V2 (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) :
    CFSG.Open.pRank 3 (Subgroup.centralizer (S.V2 : Set G)) ≤ 1 := by
  have h : CFSG.pRank 3 ↥(Subgroup.centralizer (S.V2 : Set G)) ≤ 1 := by
    by_cases hhat : IsHatA6 L
    · exact (S.lemma13_5_4 h13314 h13315 (oTwoRes ⁅L₁Of L S.V2, T ⊓ L⁆) (fun _ => rfl)
        (fun h => absurd hhat h)).2.2.2.2.2.1
    · exact (S.lemma13_5_4 h13314 h13315 (L₁Of L S.V2) (fun h => absurd h hhat)
        (fun _ => rfl)).2.2.2.2.2.1
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at h
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact h

theorem mem_V1_or_of_mem_V2 {v₂ u : G} (hv₂ : v₂ ∈ S.V2) (hv₂1 : v₂ ∉ fsuV1 T V)
    (hu : u ∈ S.V2) : u ∈ fsuV1 T V ∨ u * v₂⁻¹ ∈ fsuV1 T V := by
  have hidx : ((fsuV1 T V).subgroupOf S.V2).index = 2 := by
    have h := Subgroup.card_mul_index ((fsuV1 T V).subgroupOf S.V2)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.V1_le_V2).toEquiv, S.card_V1,
      S.card_V2] at h
    omega
  by_cases hu1 : u ∈ fsuV1 T V
  · exact Or.inl hu1
  · right
    have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u, hu⟩)
      (b := (⟨v₂, hv₂⟩ : ↥S.V2)⁻¹)).2 (by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact ⟨fun h => absurd h hu1, fun h => absurd (by simpa using (fsuV1 T V).inv_mem h) hv₂1⟩)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h

theorem conj_eq_of_cube {H : Subgroup G} (hH : H ∈ S.Hz) {e u : G} (he : e ∈ H) (he3 : e ^ 3 = 1)
    (hc : e * u * e⁻¹ * u⁻¹ ∈ fsuV1 T V) : e * u * e⁻¹ = u := by
  set c := e * u * e⁻¹ * u⁻¹ with hcdef
  have h1 : e * u * e⁻¹ = c * u := by rw [hcdef]; group
  have h2 : e * c * e⁻¹ = c := S.conj_V1_of_mem hH he hc
  have he3' : e * e * e = 1 := by rw [← he3, pow_succ, pow_succ, pow_one]
  have hm : ∀ y : G, e * (c * y) * e⁻¹ = c * (e * y * e⁻¹) := fun y => by
    calc e * (c * y) * e⁻¹ = (e * c * e⁻¹) * (e * y * e⁻¹) := by group
      _ = c * (e * y * e⁻¹) := by rw [h2]
  have h3 : u = c * (c * (c * u)) := by
    calc u = (e * e * e) * u * (e * e * e)⁻¹ := by rw [he3', one_mul, inv_one, mul_one]
      _ = e * (e * (e * u * e⁻¹) * e⁻¹) * e⁻¹ := by group
      _ = c * (c * (c * u)) := by rw [h1, hm, h1, hm, hm, h1]
  have hcc : c * c = 1 := by
    rcases S.mem_V1_iff.1 hc with h | h
    · rw [h, one_mul]
    · rw [h, ← sq, S.z_sq]
  have h4 : c * (c * (c * u)) = c * u := by rw [← mul_assoc, hcc, one_mul]
  rw [h4] at h3
  have hc1 : c = 1 := (mul_eq_right.mp h3.symm)
  rw [h1, hc1, one_mul]

variable {S}

section Tilde

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) [IsMulCommutative ↥(conjClosure S.V3 H)]
include hNS h13315 h1356two hH

theorem not_e9_tilde_fix_V2 (h13314 : Stmt13_3_14)
    {K : Subgroup G} (hKH : K ≤ H) {v₂ : G} (hv₂ : v₂ ∈ S.V2) (hv₂1 : v₂ ∉ fsuV1 T V)
    {α β' : MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    (hα : α ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    (hβ : β' ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
    (hE : A6L76B.E9Pair α β')
    (hαv : α (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩)
    (hβv : β' (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩) =
      InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHU := le_normalizer_conjClosure S.V3 H
  have hHV := S.le_normalizer_UV1 hH
  set x₂ := InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
    ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩ with hx₂
  set φ := A6Mod.secAct hHU hHV with hφ
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hφ, ker_secAct_tilde hNS h13315 h1356two hH]
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 (G := ↥H)).exists_card_eq
    rw [hk]
    intro h
    have := (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  set X : Subgroup ↥H := K.subgroupOf H ⊓
    (MulAction.stabilizer (MulAut (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) x₂).comap φ with hX
  have hmem : ∀ ψ ∈ autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)), ψ x₂ = x₂ → ψ ∈ X.map φ := by
    intro ψ hψ hψx
    obtain ⟨f, hfK, rfl⟩ := (A6Mod.mem_autSec_iff hHU hHV hKH).1 hψ
    exact ⟨f, ⟨hfK, hψx⟩, rfl⟩
  have h2 : 2 ≤ CFSG.Open.pRank 3 (X.map φ) :=
    A6L76B.two_le_pRank_of_e9 (hmem α hα hαv) (hmem β' hβ hβv) hE
  have h3 := A6L76B.pRank_map_le φ hker X
  have h4 := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) H.subtype H.subtype_injective X
  have h5 : CFSG.Open.pRank 3 (X.map H.subtype) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEX hE => ?_
    have hEC : E ≤ Subgroup.centralizer (S.V2 : Set G) := by
      intro e he
      obtain ⟨h, ⟨hhK, hhx⟩, rfl⟩ := hEX he
      have he3 : (h : G) ^ 3 = 1 := hE.2 _ he
      have hc : (h : G) * v₂ * (h : G)⁻¹ * v₂⁻¹ ∈ fsuV1 T V := by
        have h1 : φ h x₂ = x₂ := hhx
        rw [hφ, hx₂, A6Mod.secAct_secMk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
          A6Mod.secMk_eq_one_iff] at h1
        simpa [Setup.rho_apply_coe] using h1
      have hv := S.conj_eq_of_cube hH h.2 he3 hc
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rcases S.mem_V1_or_of_mem_V2 hv₂ hv₂1 hw with hw1 | hw1
      · have := S.conj_V1_of_mem hH h.2 hw1
        calc w * (h : G) = (h : G) * w * (h : G)⁻¹ * h := by rw [this]
          _ = h * w := by group
      · have h6 := S.conj_V1_of_mem hH h.2 hw1
        have e : (h : G) * w * (h : G)⁻¹ =
            ((h : G) * (w * v₂⁻¹) * (h : G)⁻¹) * ((h : G) * v₂ * (h : G)⁻¹) := by group
        have h7 : (h : G) * w * (h : G)⁻¹ = w := by
          rw [e, h6, hv]
          group
        calc w * (h : G) = (h : G) * w * (h : G)⁻¹ * h := by rw [h7]
          _ = h * w := by group
    have hEp : IsPGroup 3 ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 _ g.2)⟩
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num) hEC hE hk).trans
        (S.pRank_three_centralizer_V2 h13314 h13315)
    rw [hk]
    exact Nat.pow_le_pow_right (by norm_num) hk1
  omega

omit [IsMulCommutative ↥(conjClosure S.V3 H)] hNS h13315 h1356two hH in
theorem sec_mul_self (hab : IsElemAbelian 2 (conjClosure S.V3 H))
    [IsMulCommutative ↥(conjClosure S.V3 H)]
    (s : Sec (⊤ : Subgroup ↥(conjClosure S.V3 H)) ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) :
    s * s = 1 := by
  obtain ⟨⟨u, hu⟩, rfl⟩ := QuotientGroup.mk_surjective s
  rw [← QuotientGroup.mk_mul]
  have h : (⟨u, hu⟩ : ↥(⊤ : Subgroup ↥(conjClosure S.V3 H))) * ⟨u, hu⟩ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [sq] using hab.2 (u : G) u.2
  rw [h, QuotientGroup.mk_one]

theorem not_e9_model_fix_V2 (h13314 : Stmt13_3_14)
    (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G} (hKH : K ≤ H) {D : FFModel}
    {π : D.Gam →* ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))}
    {β : ↥(commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
      ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec}
    (hR : CFSG.Quasithin.H.Mathieu.RealizesBy D
      (autSec (autOn K (conjClosure S.V3 H)) ⊤ ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))
      (commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
      (fixV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))) ⊓
        commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
          ((fsuV1 T V).subgroupOf (conjClosure S.V3 H)))) π β)
    (hπ : Function.Injective π) {v₂ : G} (hv₂ : v₂ ∈ S.V2) (hv₂1 : v₂ ∉ fsuV1 T V)
    (hx : InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))
        ⟨v₂, le_conjClosure _ _ (S.V2_le_V3 hv₂)⟩ ∈
      commV (autSec (autOn K (conjClosure S.V3 H)) ⊤
        ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))))
    {m : D.Amb} (hm : m ∈ D.sec) (hxm : β ⟨_, hx⟩ = QuotientGroup.mk ⟨m, hm⟩) {a b : D.Gam}
    (hE : A6L76B.E9Pair a b) (ha : D.act a m * m⁻¹ ∈ D.ker) (hb : D.act b m * m⁻¹ ∈ D.ker) :
    False := by
  have hV := sec_mul_self (S := S) (H := H) hab
  have hfa := A6L76B.fix_of_realizesBy hV hR inf_le_left hE.2.1 hm hxm ha
  have hfb := A6L76B.fix_of_realizesBy hV hR inf_le_left hE.2.2.1 hm hxm hb
  have hE' := hE.map ((autSec (autOn K (conjClosure S.V3 H)) ⊤
    ((fsuV1 T V).subgroupOf (conjClosure S.V3 H))).subtype.comp π)
    (Subtype.val_injective.comp hπ)
  exact not_e9_tilde_fix_V2 hNS h13315 h1356two hH h13314 hKH hv₂ hv₂1 (π a).2 (π b).2 hE'
    hfa hfb

end Tilde

end Setting4

end CFSG.Quasithin.H13.A6
