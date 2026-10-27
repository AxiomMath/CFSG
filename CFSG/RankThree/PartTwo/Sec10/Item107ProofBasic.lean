module

public import CFSG.RankThree.PartTwo.Sec10.Item105
public import CFSG.RankThree.PartTwo.Sec10.Item109
public import CFSG.RankThree.PartTwo.KFacts.KS10BorelFacts

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

namespace Item107Proof

section General

variable {G : Type*} [Group G]

theorem exists_pow_eq_of_pow_thirteen {x : G} (hx : x ^ 13 = 1) {k : ℕ} (hk0 : 0 < k)
    (hk : k < 13) : ∃ m : ℕ, (x ^ k) ^ m = x := by
  have key : ∀ k < 13, 0 < k → ∃ m < 13, k * m % 13 = 1 := by decide
  obtain ⟨m, -, hm⟩ := key k hk hk0
  refine ⟨m, ?_⟩
  rw [← pow_mul, ← Nat.div_add_mod (k * m) 13, pow_add, pow_mul, hx, one_pow, one_mul, hm,
    pow_one]

theorem conj_eq_of_pow_thirteen_of_card_lt {x : G} (hx : x ^ 13 = 1) {W : Subgroup G}
    [Finite W] (hW : Nat.card W < 13) (hxW : x ∈ Subgroup.normalizer (W : Set G)) {w : G}
    (hw : w ∈ W) : x * w * x⁻¹ = w := by
  by_contra hne
  have hmem : ∀ i : ℕ, x ^ i * w * (x ^ i)⁻¹ ∈ W := by
    intro i
    induction i with
    | zero => simpa using hw
    | succ i ih =>
      have h1 := (Subgroup.mem_normalizer_iff.mp hxW _).mp ih
      rw [pow_succ']
      simpa [mul_assoc] using h1
  have hinj : ∀ i j : ℕ, i ≤ j → j < 13 →
      x ^ i * w * (x ^ i)⁻¹ = x ^ j * w * (x ^ j)⁻¹ → i = j := by
    intro i j hij hj heq
    by_contra hne'
    obtain ⟨m, hm⟩ := exists_pow_eq_of_pow_thirteen hx (k := j - i) (by omega) (by omega)
    have h1 : x ^ (j - i) * w * (x ^ (j - i))⁻¹ = w := by
      have hji : x ^ j = x ^ i * x ^ (j - i) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hji] at heq
      calc x ^ (j - i) * w * (x ^ (j - i))⁻¹ =
            (x ^ i)⁻¹ * (x ^ i * x ^ (j - i) * w * (x ^ i * x ^ (j - i))⁻¹) * x ^ i := by
              group
        _ = (x ^ i)⁻¹ * (x ^ i * w * (x ^ i)⁻¹) * x ^ i := by rw [← heq]
        _ = w := by group
    have hc : Commute (x ^ (j - i)) w := mul_inv_eq_iff_eq_mul.mp h1
    apply hne
    rw [← hm, (hc.pow_left m).eq, mul_inv_cancel_right]
  let f : Fin 13 → W := fun i => ⟨x ^ (i : ℕ) * w * (x ^ (i : ℕ))⁻¹, hmem i⟩
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : x ^ (i : ℕ) * w * (x ^ (i : ℕ))⁻¹ = x ^ (j : ℕ) * w * (x ^ (j : ℕ))⁻¹ :=
      congrArg Subtype.val hij
    rcases le_total (i : ℕ) j with h | h
    · exact Fin.ext (hinj _ _ h j.2 h1)
    · exact Fin.ext (hinj _ _ h i.2 h1.symm).symm
  have h2 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 13), Fintype.card_fin] at h2
  omega

theorem eq_bot_or_eq_of_le_normalizer [Finite G] {E W : Subgroup G} (hE : Nat.card E = 27)
    {x : G} (hx13 : x ^ 13 = 1) (hxfix : ∀ e ∈ E, x * e * x⁻¹ = e → e = 1) (hWE : W ≤ E)
    (hxW : x ∈ Subgroup.normalizer (W : Set G)) : W = ⊥ ∨ W = E := by
  have hdvd : Nat.card W ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE]
    exact Subgroup.card_dvd_of_le hWE
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_cases hk' : k = 3
  · right
    exact Subgroup.eq_of_le_of_card_ge hWE (by rw [hE, hk, hk']; norm_num)
  · left
    have hW13 : Nat.card W < 13 := by
      have hk2 : k ≤ 2 := by omega
      rw [hk]
      interval_cases k <;> norm_num
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    exact hxfix w (hWE hw) (conj_eq_of_pow_thirteen_of_card_lt hx13 hW13 hxW hw)

end General

section Std

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem D_inf_L (h : Sec10Std G A c L a R) : sec10D c R L ⊓ L = R ⊓ L := by
  apply le_antisymm
  · intro y hy
    obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
      (fun x hx => h.commute_c_of_mem_inf hx) hy.1
    have hck : c ^ k ∈ L := by
      have h1 := L.mul_mem hy.2 (L.inv_mem he.2)
      simpa using h1
    have hck1 : c ^ k = 1 := (Subgroup.disjoint_def.mp
      (disjoint_zpowers_of_pow_three (h.pow_three h.mem_A) h.c_not_mem_L)) hck
        (Subgroup.zpow_mem_zpowers c k)
    rw [hck1, one_mul]
    exact he
  · exact le_inf h.inf_le_D inf_le_right

theorem normalizer_D_le (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) :
    Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) := by
  have h105 := rank3II_10_5 h45 h97 G A c L a R h
  have key : ∀ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G), ∀ y ∈ R ⊓ L,
      m * y * m⁻¹ ∈ R ⊓ L := by
    intro m hm y hy
    have hyD : y ∈ sec10D c R L ⊓ L := ⟨h.inf_le_D hy, hy.2⟩
    have h1 := h105 y hyD m ((Subgroup.mem_normalizer_iff.mp hm y).mp hyD.1)
    rwa [D_inf_L h] at h1
  intro m hm
  apply Sec11.mem_normalizer_of_forall_conj_mem
  intro u hu
  have h1 := key m⁻¹ (Subgroup.inv_mem _ hm) u hu
  rwa [inv_inv] at h1

theorem conj_c_mem_D (h : Sec10Std G A c L a R) {m : G}
    (hm : m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G)) :
    m * c * m⁻¹ ∈ sec10D c R L :=
  (Subgroup.mem_normalizer_iff.mp hm c).mp h.c_mem_D

theorem exists_orderOf_thirteen (h : Sec10Std G A c L a R) :
    ∃ x ∈ L, x ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) ∧ orderOf x = 13 ∧
      ∀ e ∈ R ⊓ L, x * e * x⁻¹ = e → e = 1 := by
  obtain ⟨e₀⟩ := h.nonempty_mulEquiv
  set S := (R ⊓ L).subgroupOf L with hS
  have hScard : Nat.card S = 27 := by
    rw [hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h.card_inf]
  obtain ⟨x, hxN, hxo, hxfix⟩ :=
    KFacts.KS10Borel.exists_normalizer_orderOf_thirteen (e₀.trans (Sec4.projSLEquivPSL _))
      hScard
  refine ⟨x, x.2, ?_, ?_, ?_⟩
  · apply Sec11.mem_normalizer_of_forall_conj_mem
    intro u hu
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (S : Set L) := Subgroup.inv_mem _ hxN
    have h1 := (Subgroup.mem_normalizer_iff.mp hxinv ⟨u, hu.2⟩).mp
      (Subgroup.mem_subgroupOf.mpr hu)
    rw [Subgroup.mem_subgroupOf] at h1
    simpa using h1
  · rw [Subgroup.orderOf_coe, hxo]
  · intro e he hfix
    have h1 := hxfix ⟨e, he.2⟩ (Subgroup.mem_subgroupOf.mpr he)
      (Subtype.ext (by simpa using hfix))
    exact congrArg Subtype.val h1

theorem eq_D_of_le_R (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    {F : Subgroup G} (hFR : F ≤ R) (hF : CFSG.Assembly.IsElemAbelian 3 F)
    (hF81 : Nat.card F = 81) : F = sec10D c R L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hΩ, ⟨e, heRL, hW, hcl⟩, hcnot, -⟩ := rank3II_10_2 h45 h97 G A c L a R h
  have hΩeq : Subgroup.closure {x | x ∈ R ∧ x ^ 3 = 1} =
      Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G) := by
    rw [hΩ, sec10D, hcl, ← sup_assoc, sup_comm (Subgroup.zpowers a), sup_assoc]
  have hFΩ : F ≤ Subgroup.zpowers c ⊔ Subgroup.closure ({e, a} : Set G) := by
    rw [← hΩeq]
    intro y hy
    exact Subgroup.subset_closure ⟨hFR hy, hF.2 y hy⟩
  have hce : Commute c e := (h.commute_c_of_mem_inf heRL).symm
  have hca : Commute c a := h.comm h.mem_A h.a_mem
  have hcT : c ∉ Subgroup.closure ({e, a} : Set G) := by
    rw [hcl]
    exact hcnot
  have hab : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h1 := hW.eq_of_abelian (h.pow_three h.mem_A) hce hca hcT hFΩ hab hF81.ge
  have hEL : KFacts.eBase e a ≤ R ⊓ L := by
    rw [KFacts.eBase, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    have hai : ∀ i : ℕ, a ^ i ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
      fun i => Subgroup.pow_mem _ h.a_mem_normalizer_inf i
    rcases hy with rfl | rfl | rfl <;>
      exact (Subgroup.mem_normalizer_iff.mp (hai _) e).mp heRL
  have hE : KFacts.eBase e a = R ⊓ L :=
    Subgroup.eq_of_le_of_card_ge hEL (by rw [h.card_inf, hW.card_eBase])
  rw [h1, hE, sec10D]

theorem exists_conj_le_R (h : Sec10Std G A c L a R) {g₀ : G} {F : Subgroup G}
    (hF3 : IsPGroup 3 F)
    (hFN : F ≤ Subgroup.normalizer (Subgroup.zpowers (g₀ * c * g₀⁻¹) : Set G)) :
    ∃ k : G, (∀ u ∈ F, k⁻¹ * u * k ∈ R) ∧
      Subgroup.zpowers (k * c * k⁻¹) = Subgroup.zpowers (g₀ * c * g₀⁻¹) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set b := g₀ * c * g₀⁻¹ with hb
  have hR0 : IsSylowOf 3 (R.map (MulAut.conj g₀).toMonoidHom)
      (Subgroup.normalizer (Subgroup.zpowers b : Set G)) := by
    have h1 := IsSylowOf.map_conj h.isSylowOf g₀
    rwa [map_conj_normalizer_zpowers] at h1
  obtain ⟨Q, hQ⟩ := (hF3.comap_subtype
    (K := Subgroup.normalizer (Subgroup.zpowers b : Set G))).exists_le_sylow
  set S := (Q : Subgroup (Subgroup.normalizer (Subgroup.zpowers b : Set G))).map
    (Subgroup.normalizer (Subgroup.zpowers b : Set G)).subtype with hS
  have hSsyl : IsSylowOf 3 S (Subgroup.normalizer (Subgroup.zpowers b : Set G)) := ⟨Q, rfl⟩
  have hFS : F ≤ S := fun u hu => ⟨⟨u, hFN hu⟩, hQ (Subgroup.mem_subgroupOf.mpr hu), rfl⟩
  obtain ⟨h', hh'N, hh'⟩ := IsSylowOf.exists_mem_conj hR0 hSsyl
  refine ⟨h' * g₀, ?_, ?_⟩
  · intro u hu
    have h1 := (hh' u).mp (hFS hu)
    rw [mem_map_conj_iff] at h1
    simpa [mul_assoc] using h1
  · have e1 : h' * g₀ * c * (h' * g₀)⁻¹ = h' * b * h'⁻¹ := by rw [hb]; group
    rw [e1, ← map_conj_zpowers]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hh'N

theorem exists_mem_normalizer_D (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h98 : Sec9.Item98) (h : Sec10Std G A c L a R) :
    ∃ g ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      Subgroup.zpowers (g * c * g⁻¹) ≠ Subgroup.zpowers c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g₀, hg₀D, hg₀ne⟩ := rank3II_10_4 h45 h97 h98 G A c L a R h
  rw [map_conj_zpowers] at hg₀D hg₀ne
  set D := sec10D c R L with hD
  have hDe := h.isElemAbelian_D
  have hD3 : IsPGroup 3 D := fun u => ⟨1, Subtype.ext (by simpa using hDe.2 u u.2)⟩
  have hbD : g₀ * c * g₀⁻¹ ∈ D := Subgroup.zpowers_le.mp hg₀D
  have hDN : D ≤ Subgroup.normalizer (Subgroup.zpowers (g₀ * c * g₀⁻¹) : Set G) := fun u hu =>
    mem_normalizer_zpowers_of_conj_mem (by
      rw [show u * (g₀ * c * g₀⁻¹) = (g₀ * c * g₀⁻¹) * u from
        congrArg Subtype.val (hDe.1.is_comm.comm ⟨u, hu⟩ ⟨_, hbD⟩), mul_inv_cancel_right]
      exact Subgroup.mem_zpowers _)
  obtain ⟨k, hkR, hkc⟩ := exists_conj_le_R h hD3 hDN
  set F := D.map (MulAut.conj k⁻¹).toMonoidHom with hF
  have hFR : F ≤ R := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 := hkR u hu
    simpa using h1
  have hFe : CFSG.Assembly.IsElemAbelian 3 F := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨u, hu, rfl⟩⟩ := x
      obtain ⟨_, ⟨v, hv, rfl⟩⟩ := y
      apply Subtype.ext
      change (MulAut.conj k⁻¹) u * (MulAut.conj k⁻¹) v =
        (MulAut.conj k⁻¹) v * (MulAut.conj k⁻¹) u
      rw [← map_mul, ← map_mul,
        show u * v = v * u from congrArg Subtype.val (hDe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)]
    · rintro _ ⟨u, hu, rfl⟩
      change ((MulAut.conj k⁻¹) u) ^ 3 = 1
      rw [← map_pow, hDe.2 u hu, map_one]
  have hF81 : Nat.card F = 81 := by
    rw [hF, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, h.card_D]
  have hFD := eq_D_of_le_R h45 h97 h hFR hFe hF81
  refine ⟨k, ?_, by rw [hkc]; exact hg₀ne⟩
  have h1 : k⁻¹ ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hFD
  simpa using Subgroup.inv_mem _ h1

theorem good_or_bad (h : Sec10Std G A c L a R) {x : G} (hxL : x ∈ L)
    (hxN : x ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) (hx13 : x ^ 13 = 1)
    (hxfix : ∀ e ∈ R ⊓ L, x * e * x⁻¹ = e → e = 1) :
    (∀ e ∈ R ⊓ L, ∃ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') ∧ m * c * m⁻¹ = c * e) ∨
    (∀ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') → m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L → m * c * m⁻¹ = c) := by
  set D := sec10D c R L with hD
  set E := R ⊓ L with hE
  set M := Subgroup.normalizer ((D : Subgroup G) : Set G) with hM
  by_cases hbad : ∀ m ∈ M, (∀ e' ∈ E, m * e' * m⁻¹ = e') → m * c * m⁻¹ * c⁻¹ ∈ E →
      m * c * m⁻¹ = c
  · exact Or.inr hbad
  left
  push Not at hbad
  obtain ⟨m₀, hm₀M, hm₀E, hm₀c, hm₀ne⟩ := hbad
  set e₀ := m₀ * c * m₀⁻¹ * c⁻¹ with he₀
  have he₀1 : e₀ ≠ 1 := fun h1 => hm₀ne (mul_inv_eq_one.mp h1)
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hxL)
  have hxM : x ∈ M := by
    apply Sec11.mem_normalizer_of_forall_conj_mem
    intro u hu
    obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
      (fun y hy => h.commute_c_of_mem_inf hy) hu
    have h1 : x⁻¹ * (c ^ k * e) * x = c ^ k * (x⁻¹ * e * x) := by
      have hxck : x⁻¹ * c ^ k * x = c ^ k := by
        have := (Commute.zpow_right (show Commute x c from hxc) k)
        rw [mul_assoc, ← this.eq, inv_mul_cancel_left]
      calc x⁻¹ * (c ^ k * e) * x = (x⁻¹ * c ^ k * x) * (x⁻¹ * e * x) := by group
        _ = c ^ k * (x⁻¹ * e * x) := by rw [hxck]
    rw [h1]
    have h2 : x⁻¹ * e * x ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) e).mp he
      simpa using this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k))
      (Subgroup.mem_sup_right h2)
  have he₀E : e₀ ∈ E := hm₀c
  have he₀c : m₀ * c * m₀⁻¹ = e₀ * c := by rw [he₀]; group
  have hcE : ∀ e ∈ E, e * c = c * e := fun e he => h.commute_c_of_mem_inf he
  let P : G → Prop := fun e => e ∈ E ∧
    ∃ m ∈ M, (∀ e' ∈ E, m * e' * m⁻¹ = e') ∧ m * c * m⁻¹ = c * e
  have hPone : P 1 := ⟨E.one_mem, 1, M.one_mem, fun e' _ => by group, by group⟩
  have hPmul : ∀ e e', P e → P e' → P (e * e') := by
    rintro e e' ⟨heE, m, hmM, hmE, hmc⟩ ⟨he'E, m', hm'M, hm'E, hm'c⟩
    refine ⟨E.mul_mem heE he'E, m * m', M.mul_mem hmM hm'M, fun e'' he'' => ?_, ?_⟩
    · calc m * m' * e'' * (m * m')⁻¹ = m * (m' * e'' * m'⁻¹) * m⁻¹ := by group
        _ = e'' := by rw [hm'E e'' he'', hmE e'' he'']
    · calc m * m' * c * (m * m')⁻¹ = m * (m' * c * m'⁻¹) * m⁻¹ := by group
        _ = (m * c * m⁻¹) * (m * e' * m⁻¹) := by rw [hm'c]; group
        _ = c * (e * e') := by rw [hmc, hmE e' he'E, mul_assoc]
  have hPinv : ∀ e, P e → P e⁻¹ := by
    rintro e ⟨heE, m, hmM, hmE, hmc⟩
    have h1 : m⁻¹ * e * m = e := by
      calc m⁻¹ * e * m = m⁻¹ * (m * e * m⁻¹) * m := by rw [hmE e heE]
        _ = e := by group
    refine ⟨E.inv_mem heE, m⁻¹, M.inv_mem hmM, fun e' he' => ?_, ?_⟩
    · calc m⁻¹ * e' * m⁻¹⁻¹ = m⁻¹ * (m * e' * m⁻¹) * m := by rw [hmE e' he']; group
        _ = e' := by group
    · calc m⁻¹ * c * m⁻¹⁻¹ = m⁻¹ * (c * e) * m * (m⁻¹ * e * m)⁻¹ := by group
        _ = m⁻¹ * (m * c * m⁻¹) * m * e⁻¹ := by rw [← hmc, h1]
        _ = c * e⁻¹ := by group
  set g : ℕ → G := fun i => x ^ i * e₀ * (x ^ i)⁻¹ with hg
  have hxi : ∀ i : ℕ, x ^ i ∈ Subgroup.normalizer ((E : Subgroup G) : Set G) :=
    fun i => Subgroup.pow_mem _ hxN i
  have hgE : ∀ i, g i ∈ E := fun i => (Subgroup.mem_normalizer_iff.mp (hxi i) e₀).mp he₀E
  have hPg : ∀ i, P (g i) := by
    intro i
    have hxic : Commute (x ^ i) c := (show Commute x c from hxc).pow_left i
    refine ⟨hgE i, x ^ i * m₀ * (x ^ i)⁻¹,
      M.mul_mem (M.mul_mem (M.pow_mem hxM i) hm₀M) (M.inv_mem (M.pow_mem hxM i)),
      fun e' he' => ?_, ?_⟩
    · have he'' : (x ^ i)⁻¹ * e' * x ^ i ∈ E := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hxi i)) e').mp he'
        simpa using this
      calc x ^ i * m₀ * (x ^ i)⁻¹ * e' * (x ^ i * m₀ * (x ^ i)⁻¹)⁻¹ =
            x ^ i * (m₀ * ((x ^ i)⁻¹ * e' * x ^ i) * m₀⁻¹) * (x ^ i)⁻¹ := by group
        _ = e' := by rw [hm₀E _ he'']; group
    · have h1 : (x ^ i)⁻¹ * c * x ^ i = c := by
        rw [mul_assoc, ← hxic.eq, inv_mul_cancel_left]
      have h2 : x ^ i * c * (x ^ i)⁻¹ = c := by rw [hxic.eq, mul_inv_cancel_right]
      calc x ^ i * m₀ * (x ^ i)⁻¹ * c * (x ^ i * m₀ * (x ^ i)⁻¹)⁻¹ =
            x ^ i * (m₀ * ((x ^ i)⁻¹ * c * x ^ i) * m₀⁻¹) * (x ^ i)⁻¹ := by group
        _ = x ^ i * (e₀ * c) * (x ^ i)⁻¹ := by rw [h1, he₀c]
        _ = g i * (x ^ i * c * (x ^ i)⁻¹) := by rw [hg]; group
        _ = c * g i := by rw [h2, hcE _ (hgE i)]
  set W := Subgroup.closure (Set.range g) with hW
  have hWE : W ≤ E := by
    rw [hW, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgE i
  have hx12 : x⁻¹ = x ^ 12 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', hx13]
  have hxW : x ∈ Subgroup.normalizer (W : Set G) := by
    apply Sec11.mem_normalizer_of_forall_conj_mem
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      apply Subgroup.subset_closure
      refine ⟨i + 12, ?_⟩
      change x ^ (i + 12) * e₀ * (x ^ (i + 12))⁻¹ = x⁻¹ * (x ^ i * e₀ * (x ^ i)⁻¹) * x
      rw [pow_add, ← hx12]
      group
    | one => simp
    | mul y z _ _ hy hz =>
      have := W.mul_mem hy hz
      simpa [mul_assoc] using this
    | inv y _ hy =>
      have := W.inv_mem hy
      simpa [mul_assoc] using this
  have hW1 : W ≠ ⊥ := by
    intro hbot
    apply he₀1
    have h1 : g 0 ∈ W := Subgroup.subset_closure ⟨0, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    simpa [hg] using h1
  have hWeq : W = E := by
    rcases eq_bot_or_eq_of_le_normalizer h.card_inf hx13 hxfix hWE hxW with h1 | h1
    · exact absurd h1 hW1
    · exact h1
  intro e he
  have heW : e ∈ W := hWeq ▸ he
  clear he
  have hPe : P e := by
    induction heW using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hPg i
    | one => exact hPone
    | mul y z _ _ hy hz => exact hPmul y z hy hz
    | inv y _ hy => exact hPinv y hy
  exact hPe.2

end Std

end Item107Proof

end CFSG.RankThree.PartTwo.Sec10
