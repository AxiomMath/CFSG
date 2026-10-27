module

public import CFSG.Quasithin.H13.L32NItems143b
public import CFSG.Quasithin.Vol2.Ch12Sec8OneAbsHat

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

namespace L14332

variable {G : Type} [Group G]

theorem conj_le_centralizer_of_le {X V₁ V₂ : Subgroup G} {g : G} (hX : X ≤ Subgroup.centralizer
    (V₂ : Set G)) (hV₁₂ : V₁ ≤ V₂) (hgN : g ∈ Subgroup.normalizer (V₂ : Set G)) :
    CFSG.conjugate X g ≤ Subgroup.centralizer (V₁ : Set G) := by
  rintro _ ⟨w, hw, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hgv : g * v * g⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hgN v).mp (hV₁₂ hv)
  have hc := (Subgroup.mem_centralizer_iff.mp (hX hw)) _ hgv
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  calc v * (g⁻¹ * w * g) = g⁻¹ * ((g * v * g⁻¹) * w) * g := by group
    _ = g⁻¹ * (w * (g * v * g⁻¹)) * g := by rw [hc]
    _ = g⁻¹ * w * g * v := by group

theorem centerOf_le_l32nW {T V V₂ : Subgroup G} (hV₂U : V₂ ≤ fsuU T V) :
    centerOf (fsuU T V) ≤ l32nW T V V₂ := by
  intro x hx
  obtain ⟨hxU, hxc⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp hxc v (hV₂U hv))

theorem conj_mem_fsuU {T V : Subgroup G} {h u : G} (hh : h ∈ l32nH T V) (hu : u ∈ fsuU T V) :
    h * u * h⁻¹ ∈ fsuU T V := by
  have hle : fsuU T V ≤ (fsuU T V).comap (MulAut.conj h).toMonoidHom := by
    refine conjClosure_le fun x hx v hv => ?_
    show h * (x * v * x⁻¹) * h⁻¹ ∈ fsuU T V
    have := mem_conjClosure ((l32nH T V).mul_mem hh hx) hv
    rwa [show h * x * v * (h * x)⁻¹ = h * (x * v * x⁻¹) * h⁻¹ by group] at this
  exact hle hu

theorem l32nH_le_normalizer_fsuU (T V : Subgroup G) :
    l32nH T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact conj_mem_fsuU hh hu
  · intro hu
    have := conj_mem_fsuU ((l32nH T V).inv_mem hh) hu
    rwa [show h⁻¹ * (h * u * h⁻¹) * h⁻¹⁻¹ = u by group] at this

theorem normalizer_le_normalizer_centerOf (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (centerOf U : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  have hU := Subgroup.mem_normalizer_iff.mp hx
  have hUi := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx)
  constructor
  · intro hc
    obtain ⟨hcU, hcc⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨(hU c).mp hcU, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ U := (hUi u).mp hu
    have h1 := Subgroup.mem_centralizer_iff.mp hcc _ hu'
    simp only [inv_inv] at h1
    calc u * (x * c * x⁻¹) = x * ((x⁻¹ * u * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * u * x)) * x⁻¹ := by rw [h1]
      _ = x * c * x⁻¹ * u := by group
  · intro hc
    obtain ⟨hcU, hcc⟩ := Subgroup.mem_inf.mp hc
    have hcU' : c ∈ U := by
      have := (hUi _).mp hcU
      rwa [show x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c by group] at this
    refine Subgroup.mem_inf.mpr ⟨hcU', Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hu' : x * u * x⁻¹ ∈ U := (hU u).mp hu
    have h1 := Subgroup.mem_centralizer_iff.mp hcc _ hu'
    calc u * c = x⁻¹ * ((x * u * x⁻¹) * (x * c * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * c * x⁻¹) * (x * u * x⁻¹)) * x := by rw [h1]
      _ = c * u := by group

theorem conj_zU_le [Finite G] (h12813 : Lemma12_8_13) {T L V V₂ : Subgroup G} {g : G}
    (hs : Setting1282One G T L V 3 (fsuV1 T V) V₂) (hgP : g ∈ p128 T L V)
    (hgN : g ∉ l32nH T V) :
    CFSG.conjugate (centerOf (fsuU T V)) g ≤ l32nH T V := by
  obtain ⟨-, h2, -⟩ := h12813 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  exact (h2.trans (Subgroup.centralizer_le (inf_le_left : fsuV1 T V ≤ V))).trans
    (Subgroup.centralizer_le_normalizer _)

theorem card_img_conj_zU [Finite G] (h12810 : Lemma12_8_10) (h12813 : Lemma12_8_13)
    {T L V V₂ : Subgroup G} {g : G} (hs : Setting1282One G T L V 3 (fsuV1 T V) V₂)
    (hgP : g ∈ p128 T L V) (hgN : g ∉ l32nH T V)
    (hZ : centerOf (i128 T L V (fsuV1 T V)) = ⊥) (hV1Z : fsuV1 T V ≤ centerOf (fsuU T V))
    (hV1 : Nat.card ↥(fsuV1 T V) = 2) (D : HatModelU (fsuU T V)) :
    Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) * 2 =
      Nat.card ↥(centerOf (fsuU T V)) := by
  obtain ⟨-, -, -, -, -, h6⟩ := h12810 G T L V 3 (fsuV1 T V) V₂ hs g hgP hgN
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := h6
  have heq : CFSG.conjugate (centerOf (fsuU T V)) g ⊓
      centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V) =
        CFSG.conjugate (fsuV1 T V) g := by
    rw [e1, e2, e3, e4, e5, hZ, bot_sup_eq]
  have hle := conj_zU_le h12813 hs hgP hgN
  have hN : CFSG.conjugate (centerOf (fsuU T V)) g ≤
      Subgroup.normalizer (fsuU T V : Set G) := hle.trans (l32nH_le_normalizer_fsuU T V)
  have hker : ∀ x ∈ CFSG.conjugate (centerOf (fsuU T V)) g,
      (∃ hxN : x ∈ Subgroup.normalizer (fsuU T V : Set G), D.ρ ⟨x, hxN⟩ = 1) ↔
        x ∈ CFSG.conjugate (fsuV1 T V) g := by
    intro x hx
    rw [← heq]
    constructor
    · rintro ⟨hxN, h1⟩
      refine Subgroup.mem_inf.mpr ⟨hx, hle hx,
        normalizer_le_normalizer_centerOf _ hxN, fun u hu => ?_⟩
      exact (L128A.HatU.rho_eq_one_iff D ⟨x, hxN⟩).mp h1 u hu
    · intro h1
      obtain ⟨-, ⟨-, -, h2⟩⟩ := Subgroup.mem_inf.mp h1
      exact ⟨hN hx, (L128A.HatU.rho_eq_one_iff D ⟨x, hN hx⟩).mpr h2⟩
  rw [L128A.HatU.card_img_eq_relIndex D hN hker]
  have hle1 : CFSG.conjugate (fsuV1 T V) g ≤ CFSG.conjugate (centerOf (fsuU T V)) g :=
    Subgroup.map_mono hV1Z
  have h1 := Subgroup.relIndex_mul_card (H := CFSG.conjugate (fsuV1 T V) g)
    (K := CFSG.conjugate (centerOf (fsuU T V)) g)
  rw [inf_eq_left.mpr hle1] at h1
  rw [CFSG.conjugate, CFSG.conjugate, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hV1] at h1
  exact h1

theorem finite_linearEquiv {U : Subgroup G} (D : HatModelU U) :
    Finite (D.V ≃ₗ[ZMod 2] D.V) :=
  Finite.of_injective (fun e => (e : D.V → D.V)) fun _ _ h => LinearEquiv.ext (congrFun h)

theorem pow_conj_eq {h y c : G} (hc : h * c * h⁻¹ = c) (hy : h * y * h⁻¹ = c * y) (k : ℕ) :
    h ^ k * y * (h ^ k)⁻¹ = c ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hck : h * c ^ k * h⁻¹ = c ^ k := by
      have := map_pow (MulAut.conj h) c k
      simp only [MulAut.conj_apply] at this
      rw [this, hc]
    calc h ^ (k + 1) * y * (h ^ (k + 1))⁻¹ = h * (h ^ k * y * (h ^ k)⁻¹) * h⁻¹ := by
          rw [pow_succ']; group
      _ = h * (c ^ k * y) * h⁻¹ := by rw [ih]
      _ = (h * c ^ k * h⁻¹) * (h * y * h⁻¹) := by group
      _ = c ^ k * (c * y) := by rw [hck, hy]
      _ = c ^ (k + 1) * y := by rw [pow_succ]; group

theorem conj_eq_of_odd_of_relIndex_two {h : G} {Y Z : Subgroup G} (h2 : Y.relIndex Z = 2)
    {e : ℕ}
    (hYe : ∀ c ∈ Y, c ^ (2 ^ e) = 1) (hhZ : h ∈ Subgroup.normalizer (Z : Set G))
    (hhY : ∀ c ∈ Y, h * c * h⁻¹ = c) (hodd : Odd (orderOf h)) : ∀ y ∈ Z, h * y * h⁻¹ = y := by
  intro y hy
  by_cases hyY : y ∈ Y
  · exact hhY y hyY
  have hhy : h * y * h⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hhZ y).mp hy
  have hhyY : h * y * h⁻¹ ∉ Y := fun hm => by
    have := hhY _ hm
    apply hyY
    have e1 : y = h⁻¹ * (h * y * h⁻¹) * h := by group
    rw [e1, show h⁻¹ * (h * y * h⁻¹) * h = h * y * h⁻¹ by
      calc h⁻¹ * (h * y * h⁻¹) * h = h⁻¹ * (h * (h * y * h⁻¹) * h⁻¹) * h := by rw [this]
        _ = h * y * h⁻¹ := by group]
    exact hm
  have hidx : (Y.subgroupOf Z).index = 2 := h2
  have hcY : h * y * h⁻¹ * y⁻¹ ∈ Y := by
    have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨h * y * h⁻¹, hhy⟩)
      (b := ⟨y⁻¹, Z.inv_mem hy⟩)).mpr (iff_of_false
        (fun hm => hhyY (Subgroup.mem_subgroupOf.mp hm))
        (fun hm => hyY (by
          have := Y.inv_mem (Subgroup.mem_subgroupOf.mp hm)
          rwa [inv_inv] at this)))
    exact Subgroup.mem_subgroupOf.mp this
  set c := h * y * h⁻¹ * y⁻¹ with hcdef
  have hyc : h * y * h⁻¹ = c * y := by rw [hcdef]; group
  have hk := pow_conj_eq (hhY c hcY) hyc (orderOf h)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hk
  have hcn : c ^ orderOf h = 1 := by
    have := congrArg (· * y⁻¹) hk
    simp only [mul_inv_cancel, mul_inv_cancel_right] at this
    exact this.symm
  have hc1 : c = 1 := by
    have hd1 : orderOf c ∣ orderOf h := orderOf_dvd_of_pow_eq_one hcn
    have hd2 : orderOf c ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (hYe c hcY)
    have hcop : Nat.Coprime (2 ^ e) (orderOf h) :=
      Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
    have hg := Nat.dvd_gcd hd2 hd1
    rw [hcop.gcd_eq_one] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  rw [hyc, hc1, one_mul]

theorem exists_odd_lift {K K' : Type*} [Group K] [Group K'] (f : K →* K') {x : K}
    (hx : IsOfFinOrder x) (hodd : Odd (orderOf (f x))) :
    ∃ k : ℕ, f (x ^ k) = f x ∧ Odd (orderOf (x ^ k)) := by
  obtain ⟨e, m', hm', hn⟩ := Nat.exists_eq_two_pow_mul_odd hx.orderOf_pos.ne'
  have hcop : Nat.Coprime (2 ^ e) (orderOf (f x)) :=
    Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  obtain ⟨t, -, ht⟩ := Nat.exists_mul_mod_eq_of_coprime 1 hcop (by
    have := hodd.pos; omega)
  refine ⟨2 ^ e * t, ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf, ht, pow_mod_orderOf, pow_one]
  · have h1 : (x ^ (2 ^ e * t)) ^ m' = 1 := by
      rw [← pow_mul, show 2 ^ e * t * m' = 2 ^ e * m' * t by ring, pow_mul, ← hn,
        pow_orderOf_eq_one, one_pow]
    exact Odd.of_dvd_nat hm' (orderOf_dvd_of_pow_eq_one h1)

theorem eq_one_of_odd_of_pow_two {y : G} {e n : ℕ} (hy : y ^ (2 ^ e) = 1) (hn : y ^ n = 1)
    (hodd : Odd n) : y = 1 := by
  have hd1 : orderOf y ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hy
  have hd2 : orderOf y ∣ n := orderOf_dvd_of_pow_eq_one hn
  have hcop : Nat.Coprime (2 ^ e) n := Nat.Coprime.pow_left e (Nat.coprime_two_left.mpr hodd)
  have hg := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

section Stab

variable [Finite G] {T V V₂ : Subgroup G} (D : HatModelU (fsuU T V)) {a : G}

theorem mem_img_normalizer_of_odd (haU : a ∈ fsuU T V)
    (hV₂ : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c)
    (hHV1 : ∀ h ∈ l32nH T V, ∀ c ∈ fsuV1 T V, h * c * h⁻¹ = c)
    (hU2 : IsPGroup 2 ↥(fsuU T V))
    (hodd : ∀ h ∈ l32nH T V, Odd (orderOf h) → ∀ y ∈ centerOf (fsuU T V), h * y * h⁻¹ = y)
    {γ : D.V ≃ₗ[ZMod 2] D.V} (hγ : γ ∈ D.img (l32nH T V)) (hγa : γ (D.π a) = D.π a)
    (hγodd : Odd (orderOf γ)) :
    γ ∈ D.img (l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)) := by
  obtain ⟨h₀, hh₀H, hh₀N, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  obtain ⟨k, hk, hkodd⟩ := exists_odd_lift D.ρ (isOfFinOrder_of_finite ⟨h₀, hh₀N⟩) hγodd
  set h : G := h₀ ^ k with hhdef
  have hhH : h ∈ l32nH T V := (l32nH T V).pow_mem hh₀H k
  have hhN : h ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    Subgroup.pow_mem _ hh₀N k
  have hxk : (⟨h₀, hh₀N⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) ^ k = ⟨h, hhN⟩ := rfl
  rw [hxk] at hk hkodd
  have hhodd : Odd (orderOf h) := by
    rwa [Subgroup.orderOf_mk] at hkodd
  have hZ := hodd h hhH hhodd
  have hπ : D.π (h * a * h⁻¹) = D.π a := by
    rw [← D.ρ_π ⟨h, hhN⟩ a haU, hk, hγa]
  have hhaU : h * a * h⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem hhN haU
  have hyZ := (D.π_eq_iff _ hhaU _ haU).mp hπ
  set y := (h * a * h⁻¹)⁻¹ * a with hydef
  have hyU : y ∈ fsuU T V := (Subgroup.mem_inf.mp hyZ).1
  have hyc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyZ).2
  have e1 : h * a * h⁻¹ = a * y⁻¹ := by rw [hydef]; group
  have hay : Commute a y := hyc a haU
  have hy' : h * a * h⁻¹ = y⁻¹ * a := by rw [e1]; exact hay.inv_right.eq
  have hzy : h * y⁻¹ * h⁻¹ = y⁻¹ := by
    have := hZ y⁻¹ ((centerOf (fsuU T V)).inv_mem hyZ)
    exact this
  have hpow := pow_conj_eq hzy hy' (orderOf h)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
  have hyn : y⁻¹ ^ orderOf h = 1 := by
    have := congrArg (· * a⁻¹) hpow
    simp only [mul_inv_cancel, mul_inv_cancel_right] at this
    exact this.symm
  obtain ⟨e, he⟩ := hU2 ⟨y⁻¹, (fsuU T V).inv_mem hyU⟩
  have he' : y⁻¹ ^ (2 ^ e) = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  have hy1 : y⁻¹ = 1 := eq_one_of_odd_of_pow_two he' hyn hhodd
  have ha : h * a * h⁻¹ = a := by rw [hy', hy1, one_mul]
  have hhC : h ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hV₂ x hx with hx1 | ⟨c, hc, rfl⟩
    · have := hHV1 h hhH x hx1
      calc x * h = (h * x * h⁻¹) * h := by rw [this]
        _ = h * x := by group
    · have hc' := hHV1 h hhH c hc
      calc a * c * h = (h * a * h⁻¹) * (h * c * h⁻¹) * h := by rw [ha, hc']
        _ = h * (a * c) := by group
  rw [← hk]
  exact L128A.HatU.rho_mem_img D (Subgroup.mem_inf.mpr ⟨hhH,
    Subgroup.centralizer_le_normalizer _ hhC⟩) hhN

theorem stab_le_img_normalizer (haU : a ∈ fsuU T V)
    (hV₂ : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c)
    (hHV1 : ∀ h ∈ l32nH T V, ∀ c ∈ fsuV1 T V, h * c * h⁻¹ = c)
    (hU2 : IsPGroup 2 ↥(fsuU T V))
    (hodd : ∀ h ∈ l32nH T V, Odd (orderOf h) → ∀ y ∈ centerOf (fsuU T V), h * y * h⁻¹ = y)
    {Tdot : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hTH : Tdot ≤ D.img (l32nH T V) ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a))
    (hTN : Tdot ≤ D.img (l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)))
    (hTodd : Odd (Tdot.relIndex (D.img (l32nH T V)))) :
    D.img (l32nH T V) ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) ≤
      D.img (l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)) := by
  have := finite_linearEquiv D
  set S := D.img (l32nH T V) ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) with hS
  set K := D.img (l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)) with hK
  have hSodd : Odd (Tdot.relIndex S) := by
    have := Subgroup.relIndex_mul_relIndex Tdot S (D.img (l32nH T V)) hTH inf_le_left
    rw [← this] at hTodd
    exact (Nat.odd_mul.mp hTodd).1
  have hidx : (K.subgroupOf S).index = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro p hp hdvd
    by_cases hp2 : p = 2
    · subst hp2
      have hle : Tdot.subgroupOf S ≤ K.subgroupOf S := fun x hx =>
        Subgroup.mem_subgroupOf.mpr (hTN (Subgroup.mem_subgroupOf.mp hx))
      have h1 := Subgroup.index_dvd_of_le hle
      have h2 : 2 ∣ Tdot.relIndex S := dvd_trans hdvd h1
      exact (Nat.not_even_iff_odd.mpr hSodd) (even_iff_two_dvd.mpr h2)
    · have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p ↥S))
      have hle : (P : Subgroup ↥S) ≤ K.subgroupOf S := by
        intro x hx
        rw [Subgroup.mem_subgroupOf]
        obtain ⟨j, hj⟩ := (P.isPGroup' ⟨x, hx⟩)
        have hxp : (x : D.V ≃ₗ[ZMod 2] D.V) ^ (p ^ j) = 1 := by
          have := congrArg (fun w : ↥(P : Subgroup ↥S) => ((w : ↥S) : D.V ≃ₗ[ZMod 2] D.V)) hj
          simpa using this
        have hord : orderOf (x : D.V ≃ₗ[ZMod 2] D.V) ∣ p ^ j := orderOf_dvd_of_pow_eq_one hxp
        have hodd' : Odd (orderOf (x : D.V ≃ₗ[ZMod 2] D.V)) := by
          obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hord
          rw [hi]
          exact Odd.pow (hp.eq_two_or_odd'.resolve_left hp2)
        obtain ⟨hxH, hxa⟩ := Subgroup.mem_inf.mp x.2
        exact mem_img_normalizer_of_odd D haU hV₂ hHV1 hU2 hodd hxH hxa hodd'
      have h1 := Subgroup.index_dvd_of_le hle
      exact P.not_dvd_index (dvd_trans hdvd h1)
  rw [Subgroup.index_eq_one] at hidx
  intro γ hγ
  have : (⟨γ, hγ⟩ : ↥S) ∈ K.subgroupOf S := by rw [hidx]; trivial
  exact Subgroup.mem_subgroupOf.mp this

end Stab

theorem relIndex_img_dvd {U X Y : Subgroup G} (D : HatModelU U) (hXY : X ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (U : Set G)) :
    (D.img X).relIndex (D.img Y) ∣ X.relIndex Y := by
  set N := Subgroup.normalizer (U : Set G) with hN
  set f := D.ρ.comp (Y.subgroupOf N).subtype with hf
  have hY : D.img Y = (⊤ : Subgroup ↥(Y.subgroupOf N)).map f := by
    rw [hf, ← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have hX : D.img X = ((X.subgroupOf N).subgroupOf (Y.subgroupOf N)).map f := by
    rw [hf, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr fun x hx => Subgroup.mem_subgroupOf.mpr (hXY (Subgroup.mem_subgroupOf.mp hx))]
    rfl
  rw [hX, hY, Subgroup.relIndex_map_map, top_sup_eq, Subgroup.relIndex_top_right]
  refine dvd_trans (Subgroup.index_dvd_of_le le_sup_left) ?_
  rw [show ((X.subgroupOf N).subgroupOf (Y.subgroupOf N)).index =
    (X.subgroupOf N).relIndex (Y.subgroupOf N) from rfl, Subgroup.relIndex_subgroupOf hYN]

theorem le_normalizer_centralizerMod {Z X U : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) :
    X ≤ Subgroup.normalizer (centralizerMod Z X U : Set G) := by
  have key : ∀ h ∈ X, ∀ c ∈ centralizerMod Z X U, h * c * h⁻¹ ∈ centralizerMod Z X U := by
    intro h hh c hc
    obtain ⟨hcX, hcN, hcc⟩ := hc
    refine ⟨X.mul_mem (X.mul_mem hh hcX) (X.inv_mem hh),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXZ hh) hcN) (Subgroup.inv_mem _ (hXZ hh)),
      fun u hu => ?_⟩
    have hu' : h⁻¹ * u * h⁻¹⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp
      (Subgroup.inv_mem _ (hXU hh)) u).mp hu
    have h1 := hcc _ hu'
    have h2 : h * (c * (h⁻¹ * u * h⁻¹⁻¹) * c⁻¹ * (h⁻¹ * u * h⁻¹⁻¹)⁻¹) * h⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hXZ hh) _).mp h1
    rwa [show h * (c * (h⁻¹ * u * h⁻¹⁻¹) * c⁻¹ * (h⁻¹ * u * h⁻¹⁻¹)⁻¹) * h⁻¹ =
      h * c * h⁻¹ * u * (h * c * h⁻¹)⁻¹ * u⁻¹ by group] at h2
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key h hh c, fun hc => ?_⟩
  have := key h⁻¹ (X.inv_mem hh) _ hc
  rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this

variable {T V V₂ : Subgroup G} (D : HatModelU (fsuU T V))

theorem rho_fix_pi {a : G} (haV₂ : a ∈ V₂) (haU : a ∈ fsuU T V) (ha1 : a ∉ fsuV1 T V)
    (hV₂ : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c)
    (hV1Z : fsuV1 T V ≤ centerOf (fsuU T V)) {h : G}
    (hh : h ∈ l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G))
    (hN : h ∈ Subgroup.normalizer (fsuU T V : Set G)) : D.ρ ⟨h, hN⟩ (D.π a) = D.π a := by
  obtain ⟨hhH, hhV₂⟩ := Subgroup.mem_inf.mp hh
  have hha : h * a * h⁻¹ ∈ V₂ := (Subgroup.mem_normalizer_iff.mp hhV₂ a).mp haV₂
  rw [D.ρ_π ⟨h, hN⟩ a haU]
  rcases hV₂ _ hha with h1 | ⟨c, hc, hca⟩
  · exfalso
    apply ha1
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhH) _).mp h1
    rwa [show h⁻¹ * (h * a * h⁻¹) * h⁻¹⁻¹ = a by group] at this
  · show D.π (h * a * h⁻¹) = D.π a
    rw [hca, D.π_mul a haU c (hV1Z hc).1, (L128A.HatU.π_eq_zero_iff D (hV1Z hc).1).mpr (hV1Z hc),
      add_zero]

theorem img_normalizer_le_stab {a : G} (haV₂ : a ∈ V₂) (haU : a ∈ fsuU T V)
    (ha1 : a ∉ fsuV1 T V) (hV₂ : ∀ x ∈ V₂, x ∈ fsuV1 T V ∨ ∃ c ∈ fsuV1 T V, x = a * c)
    (hV1Z : fsuV1 T V ≤ centerOf (fsuU T V)) :
    D.img (l32nH T V ⊓ Subgroup.normalizer (V₂ : Set G)) ≤
      D.img (l32nH T V) ⊓ MulAction.stabilizer (D.V ≃ₗ[ZMod 2] D.V) (D.π a) := by
  intro γ hγ
  obtain ⟨h, hh, hN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  exact Subgroup.mem_inf.mpr ⟨L128A.HatU.rho_mem_img D (Subgroup.mem_inf.mp hh).1 hN,
    rho_fix_pi D haV₂ haU ha1 hV₂ hV1Z hh hN⟩

theorem rho_mem_normalizer_img {X : Subgroup G} (hXH : X ≤ l32nH T V) {h : G}
    (hN : h ∈ Subgroup.normalizer (fsuU T V : Set G))
    (hh : h ∈ Subgroup.normalizer ((X ⊔ l32nCHat T V : Subgroup G) : Set G)) :
    D.ρ ⟨h, hN⟩ ∈ Subgroup.normalizer (D.img X : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
  have := finite_linearEquiv D
  have hCN : X ≤ Subgroup.normalizer (l32nCHat T V : Set G) :=
    hXH.trans (le_normalizer_centralizerMod (l32nH_le_normalizer_fsuU T V)
      ((l32nH_le_normalizer_fsuU T V).trans (normalizer_le_normalizer_centerOf _)))
  refine Subgroup.mem_normalizer_fintype fun γ hγ => ?_
  obtain ⟨x, hx, hxN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  have hhx : h * x * h⁻¹ ∈ X ⊔ l32nCHat T V :=
    (Subgroup.mem_normalizer_iff.mp hh x).mp (Subgroup.mem_sup_left hx)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCN] at hhx
  obtain ⟨y, hy, c, hc, hyc⟩ := hhx
  have hyN : y ∈ Subgroup.normalizer (fsuU T V : Set G) := l32nH_le_normalizer_fsuU T V (hXH hy)
  have hcN : c ∈ Subgroup.normalizer (fsuU T V : Set G) :=
    l32nH_le_normalizer_fsuU T V hc.1
  have hρc : D.ρ ⟨c, hcN⟩ = 1 := (L128A.HatU.rho_eq_one_iff D ⟨c, hcN⟩).mpr hc.2.2
  have he : (⟨h, hN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) * ⟨x, hxN⟩ * ⟨h, hN⟩⁻¹ =
      ⟨y, hyN⟩ * ⟨c, hcN⟩ := Subtype.ext (by simp [hyc])
  have := congrArg D.ρ he
  rw [map_mul, map_mul, map_mul, hρc, mul_one, map_inv] at this
  rw [this]
  exact L128A.HatU.rho_mem_img D hy hyN

end L14332

end CFSG.Quasithin.H13
