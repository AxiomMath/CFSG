module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zi

public section

namespace CFSG.Quasithin.NoTransv

section Restr

variable {X : Type*} [Group X]

@[expose] def stab (S : Subgroup X) : Subgroup (MulAut X) where
  carrier := {g | ∀ v, v ∈ S ↔ g v ∈ S}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {a b} ha hb v => (hb v).trans (ha (b v))
  inv_mem' := fun {a} ha v => by
    have h := ha (a⁻¹ v)
    rw [MulAut.apply_inv_self] at h
    exact h.symm

@[expose] def restr (S : Subgroup X) : ↥(stab S) →* MulAut ↥S where
  toFun g :=
    { toFun := fun v => ⟨(g : MulAut X) v, (g.2 v).1 v.2⟩
      invFun := fun v => ⟨(g : MulAut X)⁻¹ v, ((stab S).inv_mem g.2 v).1 v.2⟩
      left_inv := fun v => Subtype.ext (MulAut.inv_apply_self X (g : MulAut X) (v : X))
      right_inv := fun v => Subtype.ext (MulAut.apply_inv_self X (g : MulAut X) (v : X))
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  map_one' := by ext v; rfl
  map_mul' := fun a b => by ext v; rfl

theorem restr_apply (S : Subgroup X) (g : ↥(stab S)) (v : ↥S) :
    ((restr S g v : ↥S) : X) = (g : MulAut X) v := rfl

end Restr

section QuotConj

variable {G : Type*} [Group G]

theorem normalizerMonoidHom_coe (P : Subgroup G) (n : ↥(Subgroup.normalizer (P : Set G))) (p : ↥P) :
    ((P.normalizerMonoidHom n p : ↥P) : G) = (n : G) * p * (n : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ p

theorem map_conj_subgroupOf [Finite G] {P C : Subgroup G} {k : G}
    (hkP : k ∈ Subgroup.normalizer (P : Set G)) (hkC : k ∈ Subgroup.normalizer (C : Set G)) :
    (C.subgroupOf P).map (P.normalizerMonoidHom ⟨k, hkP⟩).toMonoidHom = C.subgroupOf P := by
  refine Subgroup.eq_of_le_of_card_ge ?_
    (by rw [Subgroup.card_map_of_injective (MulEquiv.injective _)])
  rintro _ ⟨c, hc, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hc
  rw [Subgroup.mem_subgroupOf]
  show ((P.normalizerMonoidHom ⟨k, hkP⟩ c : ↥P) : G) ∈ C
  rw [normalizerMonoidHom_coe]
  exact (Subgroup.mem_normalizer_iff.mp hkC c).mp hc

@[expose] noncomputable def quotConj [Finite G] (P C K : Subgroup G) [(C.subgroupOf P).Normal]
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hKC : K ≤ Subgroup.normalizer (C : Set G)) :
    ↥K →* MulAut (↥P ⧸ C.subgroupOf P) where
  toFun k := QuotientGroup.congr _ _ (P.normalizerMonoidHom ⟨k, hKP k.2⟩)
    (map_conj_subgroupOf _ (hKC k.2))
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf P) q
    show QuotientGroup.mk' _ (P.normalizerMonoidHom 1 w) = QuotientGroup.mk' _ w
    rw [map_one]
    rfl
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf P) q
    show QuotientGroup.mk' _ (P.normalizerMonoidHom (⟨a, hKP a.2⟩ * ⟨b, hKP b.2⟩) w) =
      QuotientGroup.mk' _
        (P.normalizerMonoidHom ⟨a, hKP a.2⟩ (P.normalizerMonoidHom ⟨b, hKP b.2⟩ w))
    rw [map_mul]
    rfl

theorem quotConj_mk [Finite G] (P C K : Subgroup G) [(C.subgroupOf P).Normal]
    (hKP : K ≤ Subgroup.normalizer (P : Set G)) (hKC : K ≤ Subgroup.normalizer (C : Set G))
    (k : ↥K) (p : ↥P) :
    quotConj P C K hKP hKC k (QuotientGroup.mk' _ p) =
      QuotientGroup.mk' _ (P.normalizerMonoidHom ⟨k, hKP k.2⟩ p) := rfl

end QuotConj

section Stab

theorem eq_one_of_conj_eq_mul' {X : Type*} [Group X] {z x c : X} (hzc : z * c = c * z)
    (hzx : z * x * z⁻¹ = c * x) (hodd : Odd (orderOf z)) (hc : ∃ k : ℕ, c ^ 2 ^ k = 1) :
    c = 1 := by
  have hpow : ∀ n : ℕ, z ^ n * x * (z ^ n)⁻¹ = c ^ n * x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hzcn : z * c ^ n = c ^ n * z := (Commute.pow_right hzc n).eq
      calc z ^ (n + 1) * x * (z ^ (n + 1))⁻¹ = z * (z ^ n * x * (z ^ n)⁻¹) * z⁻¹ := by
            rw [pow_succ']; group
        _ = z * (c ^ n * x) * z⁻¹ := by rw [ih]
        _ = c ^ n * (z * x * z⁻¹) := by
            rw [← mul_assoc, hzcn]; group
        _ = c ^ (n + 1) * x := by rw [hzx, pow_succ]; group
  have h1 : c ^ orderOf z = 1 := by
    have := hpow (orderOf z)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at this
    exact (mul_eq_right.mp this.symm)
  obtain ⟨k, hk⟩ := hc
  have hd1 : orderOf c ∣ orderOf z := orderOf_dvd_of_pow_eq_one h1
  have hd2 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (2 ^ k) (orderOf z) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd2 hd1))

variable {G : Type*} [Group G] [Finite G]

theorem comm_mem_of_stab {L P V : Subgroup G} {C : Set G}
    (hno2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    (hLP : L ≤ Subgroup.normalizer (P : Set G)) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hPV : P ≤ Subgroup.normalizer (V : Set G))
    (hCV : ∀ c ∈ C, c ∈ Subgroup.normalizer (V : Set G))
    (hC2 : ∀ c ∈ C, ∃ k : ℕ, c ^ 2 ^ k = 1)
    (hCL : ∀ c ∈ C, ∀ l ∈ L, l * c * l⁻¹ * c⁻¹ ∈ V)
    (h : ∀ x ∈ P, ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ C) :
    ∀ x ∈ P, ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ V := by
  classical
  set N := Subgroup.normalizer (V : Set G) with hN
  have hodd : ∀ l ∈ L, Odd (orderOf l) → ∀ x ∈ P, l * x * l⁻¹ * x⁻¹ ∈ V := by
    intro l hl hlo x hx
    set c := l * x * l⁻¹ * x⁻¹ with hc
    have hcC := h x hx l hl
    have hlN : l ∈ N := hLV hl
    have hxN : x ∈ N := hPV hx
    have hcN : c ∈ N := hCV c hcC
    set π := QuotientGroup.mk' (V.subgroupOf N) with hπ
    have hzc : π ⟨l, hlN⟩ * π ⟨c, hcN⟩ = π ⟨c, hcN⟩ * π ⟨l, hlN⟩ := by
      have h1 : π (⟨l, hlN⟩ * ⟨c, hcN⟩ * ⟨l, hlN⟩⁻¹ * ⟨c, hcN⟩⁻¹) = 1 := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hCL c hcC l hl
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hzx : π ⟨l, hlN⟩ * π ⟨x, hxN⟩ * (π ⟨l, hlN⟩)⁻¹ = π ⟨c, hcN⟩ * π ⟨x, hxN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [hc])
    have hzo : Odd (orderOf (π ⟨l, hlN⟩)) :=
      Odd.of_dvd_nat (by rwa [Subgroup.orderOf_mk]) (orderOf_map_dvd π _)
    obtain ⟨k, hk⟩ := hC2 c hcC
    have hck : (π ⟨c, hcN⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : ↥N) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, map_one]
    have h1 := eq_one_of_conj_eq_mul' hzc hzx hzo ⟨k, hck⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    exact h1
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, ∀ l, l ∈ S ↔ l ∈ L ∧ ∀ x ∈ P, l * x * l⁻¹ * x⁻¹ ∈ V :=
    ⟨{ carrier := {l | l ∈ L ∧ ∀ x ∈ P, l * x * l⁻¹ * x⁻¹ ∈ V}
       one_mem' := ⟨L.one_mem, fun x _ => by simp⟩
       mul_mem' := fun {a b} ha hb => ⟨L.mul_mem ha.1 hb.1, fun x hx => by
         have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
             a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
         rw [e]
         exact V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV ha.1) _).mp (hb.2 x hx))
           (ha.2 x hx)⟩
       inv_mem' := fun {a} ha => ⟨L.inv_mem ha.1, fun x hx => by
         have hx' : a⁻¹ * x * a ∈ P := by
           have := (Subgroup.mem_normalizer_iff.mp (hLP (L.inv_mem ha.1)) x).mp hx
           simpa using this
         have h1 := ha.2 _ hx'
         have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = (a * (a⁻¹ * x * a) * a⁻¹ * (a⁻¹ * x * a)⁻¹)⁻¹ := by
           group
         rw [e]
         exact V.inv_mem h1⟩ }, fun _ => Iff.rfl⟩
  have hSL : S ≤ L := fun l hl => ((hS l).mp hl).1
  have hSn : (S.subgroupOf L).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    obtain ⟨-, haP⟩ := (hS _).mp ha
    refine (hS _).mpr ⟨L.mul_mem (L.mul_mem g.2 (hSL ha)) (L.inv_mem g.2), fun x hx => ?_⟩
    have hx' : (g : G)⁻¹ * x * g ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (hLP (L.inv_mem g.2)) x).mp hx
      simpa using this
    have h1 := haP _ hx'
    have e : ((g * a * g⁻¹ : ↥L) : G) * x * ((g * a * g⁻¹ : ↥L) : G)⁻¹ * x⁻¹ =
        (g : G) * ((a : G) * ((g : G)⁻¹ * x * g) * (a : G)⁻¹ * ((g : G)⁻¹ * x * g)⁻¹) *
          (g : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLV g.2) _).mp h1
  have htop := hno2 (S.subgroupOf L) (fun y => by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (S.subgroupOf L) y
    obtain ⟨a, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
    refine ⟨a, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hya : Odd (orderOf ((y : G) ^ 2 ^ a)) := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, by rw [Subgroup.orderOf_coe, he]⟩,
        Subgroup.orderOf_coe, he, Nat.mul_div_cancel_left _ (pow_pos two_pos a)]
      exact hm
    rw [SubmonoidClass.coe_pow]
    exact (hS _).mpr ⟨L.pow_mem y.2 _, hodd _ (L.pow_mem y.2 _) hya⟩)
  intro x hx l hl
  have hlS : (⟨l, hl⟩ : ↥L) ∈ S.subgroupOf L := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf] at hlS
  exact ((hS l).mp hlS).2 x hx

end Stab

section Main

variable {G : Type*} [Group G] [Finite G]

theorem comm_le_of_transv {L Q V A : Subgroup G} {O : Subgroup ↥L} [O.Normal]
    (hO : ∀ x : ↥L, x ∈ O ↔ (x : G) ∈ Subgroup.centralizer (V : Set G))
    (hO2 : IsPGroup 2 O) (hq : CFSG.IsQuasisimple (↥L ⧸ O))
    (hcen : Nat.card (Subgroup.center (↥L ⧸ O)) = 3)
    (e : (↥L ⧸ O) ⧸ Subgroup.center (↥L ⧸ O) ≃* alternatingGroup (Fin 6))
    (hno2 : ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤)
    (hQ2 : IsPGroup 2 Q) (hVQ : V ≤ Q) (hQC : Q ≤ Subgroup.centralizer (V : Set G))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set G)) (hQL : Q ≤ Subgroup.normalizer (L : Set G))
    (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {l q₀ : G} (hl : l ∈ L) (hq₀ : q₀ ∈ Q) (hl2 : l * l ∈ Subgroup.centralizer (V : Set G))
    (hlV : l ∉ Subgroup.centralizer (V : Set G))
    (hcomm : ∀ p ∈ Q, p⁻¹ * (l * q₀ * p * (l * q₀)⁻¹) ∈ A)
    (hA2 : ∀ a₁ ∈ A, ∀ a ∈ A, a₁ ∉ V → a ∉ V → a₁⁻¹ * a ∈ V) :
    ∀ q ∈ Q, ∀ l' ∈ L, l' * q * l'⁻¹ * q⁻¹ ∈ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) :=
    hQC.trans (Subgroup.centralizer_le_normalizer _)
  have h2elt : ∀ x ∈ Q, ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hQ2 ⟨x, hx⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : Subgroup G,
      ∀ x, x ∈ C₀ ↔ x ∈ Q ∧ ∀ l' ∈ L, l' * x * l'⁻¹ * x⁻¹ ∈ V :=
    ⟨{ carrier := {x | x ∈ Q ∧ ∀ l' ∈ L, l' * x * l'⁻¹ * x⁻¹ ∈ V}
       one_mem' := ⟨Q.one_mem, fun _ _ => by simp⟩
       mul_mem' := fun {a b} ha hb => ⟨Q.mul_mem ha.1 hb.1, fun l' hl' => by
         have e : l' * (a * b) * l'⁻¹ * (a * b)⁻¹ =
             (l' * a * l'⁻¹ * a⁻¹) * (a * (l' * b * l'⁻¹ * b⁻¹) * a⁻¹) := by group
         rw [e]
         exact V.mul_mem (ha.2 l' hl')
           ((Subgroup.mem_normalizer_iff.mp (hQV ha.1) _).mp (hb.2 l' hl'))⟩
       inv_mem' := fun {a} ha => ⟨Q.inv_mem ha.1, fun l' hl' => by
         have e : l' * a⁻¹ * l'⁻¹ * a⁻¹⁻¹ = a⁻¹ * (l' * a * l'⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ := by group
         rw [e]
         exact (Subgroup.mem_normalizer_iff.mp (hQV (Q.inv_mem ha.1)) _).mp
           (V.inv_mem (ha.2 l' hl'))⟩ }, fun _ => Iff.rfl⟩
  have hC₀Q : C₀ ≤ Q := fun x hx => ((hC₀ x).mp hx).1
  have hVC₀ : V ≤ C₀ := fun v hv => (hC₀ v).mpr ⟨hVQ hv, fun l' hl' =>
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLV hl') v).mp hv) (V.inv_mem hv)⟩
  have hconj : ∀ g ∈ Subgroup.normalizer (Q : Set G), g ∈ Subgroup.normalizer (L : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) → ∀ c ∈ C₀, g * c * g⁻¹ ∈ C₀ := by
    intro g hgQ hgL hgV c hc
    obtain ⟨hcQ, hcL⟩ := (hC₀ c).mp hc
    refine (hC₀ _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hgQ c).mp hcQ, fun l' hl' => ?_⟩
    have hm : g⁻¹ * l' * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgL) l').mp hl'
      simpa using this
    have e : l' * (g * c * g⁻¹) * l'⁻¹ * (g * c * g⁻¹)⁻¹ =
        g * ((g⁻¹ * l' * g) * c * (g⁻¹ * l' * g)⁻¹ * c⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hgV _).mp (hcL _ hm)
  have hQN : Q ≤ Subgroup.normalizer (C₀ : Set G) := fun q hq =>
    Subgroup.mem_normalizer_fintype fun c hc =>
      hconj q (Subgroup.le_normalizer hq) (hQL hq) (hQV hq) c hc
  have hLN : L ≤ Subgroup.normalizer (C₀ : Set G) := fun x hx =>
    Subgroup.mem_normalizer_fintype fun c hc =>
      hconj x (hLQ hx) (Subgroup.le_normalizer hx) (hLV hx) c hc
  by_contra hne
  push Not at hne
  obtain ⟨q₁, hq₁, l₁, hl₁, hq₁V⟩ := hne
  have hq₁C : q₁ ∉ C₀ := fun h => hq₁V (((hC₀ q₁).mp h).2 l₁ hl₁)
  have hC₀n : (C₀.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₀Q).mpr hQN
  set ψb := quotConj Q C₀ L hLQ hLN with hψb
  have hψbmk : ∀ (l' : ↥L) (p : ↥Q),
      ψb l' (QuotientGroup.mk' _ p) = QuotientGroup.mk' _
        ⟨(l' : G) * p * (l' : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hLQ l'.2) p).mp p.2⟩ := by
    intro l' p
    rw [hψb, quotConj_mk]
    exact congrArg _ (Subtype.ext (normalizerMonoidHom_coe Q _ p))
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : Subgroup (↥Q ⧸ C₀.subgroupOf Q), ∀ w, w ∈ Ω ↔
      w ∈ Subgroup.center (↥Q ⧸ C₀.subgroupOf Q) ∧ w ^ 2 = 1 :=
    ⟨{ carrier := {w | w ∈ Subgroup.center (↥Q ⧸ C₀.subgroupOf Q) ∧ w ^ 2 = 1}
       one_mem' := ⟨Subgroup.one_mem _, one_pow 2⟩
       mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
         have hab : Commute a b := (Subgroup.mem_center_iff.mp ha.1 b).symm
         rw [hab.mul_pow, ha.2, hb.2, one_mul]⟩
       inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by rw [inv_pow, ha.2, inv_one]⟩ },
      fun _ => Iff.rfl⟩
  have hΩinv : ∀ φ : MulAut (↥Q ⧸ C₀.subgroupOf Q), ∀ w ∈ Ω, φ w ∈ Ω := by
    intro φ w hw
    obtain ⟨hwc, hw2⟩ := (hΩ w).mp hw
    refine (hΩ _).mpr ⟨Subgroup.mem_center_iff.mpr fun g => ?_, by rw [← map_pow, hw2, map_one]⟩
    obtain ⟨g', rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hwc g']
  have hstab : ∀ l' : ↥L, ψb l' ∈ stab Ω := fun l' v =>
    ⟨fun hv => hΩinv _ v hv, fun hv => by
      have := hΩinv (ψb l')⁻¹ _ hv
      rwa [MulAut.inv_apply_self] at this⟩
  set ψ : ↥L →* MulAut ↥Ω := (restr Ω).comp (ψb.codRestrict (stab Ω) hstab) with hψ
  have hψapp : ∀ (l' : ↥L) (w : ↥Ω), ((ψ l' w : ↥Ω) : ↥Q ⧸ C₀.subgroupOf Q) = ψb l' w :=
    fun _ _ => rfl
  let _ : CommGroup ↥Ω :=
    { (inferInstance : Group ↥Ω) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp ((hΩ _).mp a.2).1 b).symm }
  have hW2 : ∀ w : ↥Ω, w ^ 2 = 1 := fun w => Subtype.ext ((hΩ _).mp w.2).2
  have hrange : ∀ y ∈ (commHom (ψ ⟨l, hl⟩)).range, ∃ a ∈ A, ∃ ha : a ∈ Q,
      (y : ↥Q ⧸ C₀.subgroupOf Q) = QuotientGroup.mk' _ ⟨a, ha⟩ := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective (C₀.subgroupOf Q) (w : ↥Q ⧸ C₀.subgroupOf Q)
    have hq₀p : (q₀ * p * q₀⁻¹ : G) ∈ Q := Q.mul_mem (Q.mul_mem hq₀ p.2) (Q.inv_mem hq₀)
    have hcen : QuotientGroup.mk' (C₀.subgroupOf Q) ⟨q₀ * p * q₀⁻¹, hq₀p⟩ =
        QuotientGroup.mk' (C₀.subgroupOf Q) p := by
      have e : (⟨q₀ * p * q₀⁻¹, hq₀p⟩ : ↥Q) = ⟨q₀, hq₀⟩ * p * ⟨q₀, hq₀⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv, hp,
        Subgroup.mem_center_iff.mp ((hΩ _).mp w.2).1 _, mul_inv_cancel_right]
    have hu : (l * q₀ * p * (l * q₀)⁻¹ : G) ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hLQ hl) _).mp hq₀p |> fun h => by
        have e : l * q₀ * p * (l * q₀)⁻¹ = l * (q₀ * p * q₀⁻¹) * l⁻¹ := by group
        rw [e]
        exact h
    have ha : (p⁻¹ * (l * q₀ * p * (l * q₀)⁻¹) : G) ∈ Q := Q.mul_mem (Q.inv_mem p.2) hu
    refine ⟨_, hcomm p p.2, ha, ?_⟩
    have h1 : ψb ⟨l, hl⟩ (QuotientGroup.mk' _ ⟨q₀ * p * q₀⁻¹, hq₀p⟩) =
        QuotientGroup.mk' _ ⟨l * q₀ * p * (l * q₀)⁻¹, hu⟩ := by
      rw [hψbmk]
      congr 1
      exact Subtype.ext (by simp only; group)
    rw [hcen, hp] at h1
    show (w : ↥Q ⧸ C₀.subgroupOf Q)⁻¹ * ((ψ ⟨l, hl⟩ w : ↥Ω) : ↥Q ⧸ C₀.subgroupOf Q) = _
    rw [hψapp, h1, ← hp]
    have e : (⟨(p : G)⁻¹ * (l * q₀ * p * (l * q₀)⁻¹), ha⟩ : ↥Q) = p⁻¹ * ⟨_, hu⟩ := rfl
    rw [e, map_mul, map_inv]
  have hbound : Nat.card (commHom (ψ ⟨l, hl⟩)).range ≤ 2 := by
    by_cases hR : ∀ y ∈ (commHom (ψ ⟨l, hl⟩)).range, y = 1
    · have hbot : (commHom (ψ ⟨l, hl⟩)).range = ⊥ :=
        eq_bot_iff.mpr fun y hy => (Subgroup.mem_bot).mpr (hR y hy)
      rw [hbot, Subgroup.card_bot]
      norm_num
    · push Not at hR
      obtain ⟨y₀, hy₀, hy₀1⟩ := hR
      obtain ⟨a₀, ha₀A, ha₀Q, hy₀a⟩ := hrange y₀ hy₀
      have hV1 : ∀ (a : G) (haQ : a ∈ Q), a ∈ V →
          QuotientGroup.mk' (C₀.subgroupOf Q) ⟨a, haQ⟩ = 1 := fun a haQ haV =>
        (QuotientGroup.eq_one_iff _).mpr (hVC₀ haV)
      have ha₀V : a₀ ∉ V := fun h => hy₀1 (Subtype.ext (hy₀a.trans (hV1 a₀ ha₀Q h)))
      have hle : (commHom (ψ ⟨l, hl⟩)).range ≤ Subgroup.zpowers y₀ := by
        intro y hy
        by_cases hy1 : y = 1
        · rw [hy1]
          exact Subgroup.one_mem _
        · obtain ⟨a, haA, haQ, hya⟩ := hrange y hy
          have haV : a ∉ V := fun h => hy1 (Subtype.ext (hya.trans (hV1 a haQ h)))
          have h1 := hA2 a₀ ha₀A a haA ha₀V haV
          have hyy : y = y₀ := Subtype.ext (by
            rw [hya, hy₀a]
            exact ((QuotientGroup.eq (s := C₀.subgroupOf Q) (a := ⟨a₀, ha₀Q⟩)
              (b := ⟨a, haQ⟩)).mpr (hVC₀ h1)).symm)
          rw [hyy]
          exact Subgroup.mem_zpowers _
      have h2 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at h2
      have : orderOf y₀ ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (hW2 y₀)
      omega
  have hψ1 : ψ = 1 := eq_one_of_transv hW2 ψ hO2 hq hcen e hno2 (r := ⟨l, hl⟩)
    ((hO _).mpr hl2) (fun h => hlV ((hO _).mp h)) hbound
  set P₂ : Subgroup G := (Ω.comap (QuotientGroup.mk' (C₀.subgroupOf Q))).map Q.subtype with hP₂
  have hmemP₂ : ∀ x (hx : x ∈ Q), x ∈ P₂ ↔ QuotientGroup.mk' (C₀.subgroupOf Q) ⟨x, hx⟩ ∈ Ω := by
    intro x hx
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = ⟨x, hx⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h
      exact ⟨⟨x, hx⟩, h, rfl⟩
  have hP₂Q : P₂ ≤ Q := Subgroup.map_subtype_le _
  have hfix : ∀ x ∈ P₂, ∀ l' ∈ L, l' * x * l'⁻¹ * x⁻¹ ∈ C₀ := by
    intro x hx l' hl'
    have hxQ := hP₂Q hx
    have hxΩ := (hmemP₂ x hxQ).mp hx
    have h1 : ((ψ ⟨l', hl'⟩ ⟨_, hxΩ⟩ : ↥Ω) : ↥Q ⧸ C₀.subgroupOf Q) =
        QuotientGroup.mk' (C₀.subgroupOf Q) ⟨x, hxQ⟩ := by
      rw [hψ1]
      rfl
    rw [hψapp, hψbmk] at h1
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : x * ((l' * x * l'⁻¹)⁻¹ * x)⁻¹ * x⁻¹ ∈ C₀ :=
      (Subgroup.mem_normalizer_iff.mp (hQN hxQ) _).mp (C₀.inv_mem h2)
    have e : l' * x * l'⁻¹ * x⁻¹ = x * ((l' * x * l'⁻¹)⁻¹ * x)⁻¹ * x⁻¹ := by group
    rw [e]
    exact h3
  have hLP₂ : L ≤ Subgroup.normalizer (P₂ : Set G) := by
    intro l' hl'
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxQ := hP₂Q hx
    have hlx : l' * x * l'⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hLQ hl') x).mp hxQ
    refine (hmemP₂ _ hlx).mpr ?_
    have := hΩinv (ψb ⟨l', hl'⟩) _ ((hmemP₂ x hxQ).mp hx)
    rwa [hψbmk] at this
  have hstabV := comm_mem_of_stab hno2 hLP₂ hLV (hP₂Q.trans hQV)
    (fun c hc => hQV (hC₀Q hc)) (fun c hc => h2elt c (hC₀Q hc))
    (fun c hc l' hl' => ((hC₀ c).mp hc).2 l' hl') hfix
  have hΩbot : ∀ w ∈ Ω, w = 1 := by
    intro w hw
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (C₀.subgroupOf Q) w
    have hpP : (p : G) ∈ P₂ := (hmemP₂ p p.2).mpr hw
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    exact (hC₀ _).mpr ⟨p.2, fun l' hl' => hstabV _ hpP l' hl'⟩
  have hnt : Nontrivial (↥Q ⧸ C₀.subgroupOf Q) := by
    refine ⟨⟨QuotientGroup.mk' _ ⟨q₁, hq₁⟩, 1, fun h => hq₁C ?_⟩⟩
    have := (QuotientGroup.eq_one_iff _).mp h
    rwa [Subgroup.mem_subgroupOf] at this
  have hQb2 : IsPGroup 2 (↥Q ⧸ C₀.subgroupOf Q) := hQ2.to_quotient _
  have hcnt := hQb2.center_nontrivial
  have h2c : 2 ∣ Nat.card ↥(Subgroup.center (↥Q ⧸ C₀.subgroupOf Q)) := by
    obtain ⟨k, hk⟩ := (hQb2.to_subgroup (Subgroup.center _)).exists_card_eq
    have h1 : 1 < Nat.card ↥(Subgroup.center (↥Q ⧸ C₀.subgroupOf Q)) := Finite.one_lt_card
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2c
  have hzΩ : (z : ↥Q ⧸ C₀.subgroupOf Q) ∈ Ω := (hΩ _).mpr ⟨z.2, by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg Subtype.val this⟩
  have hz1 := hΩbot _ hzΩ
  have : z = 1 := Subtype.ext hz1
  rw [this, orderOf_one] at hz
  exact absurd hz (by norm_num)

end Main

end CFSG.Quasithin.NoTransv
