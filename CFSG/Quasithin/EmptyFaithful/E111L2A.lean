module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.Quasithin.EmptyFaithful.E22PL2Psl
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.R37Dihedral
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.E2.E22N.E111L

open CFSG.GorensteinWalter DihedralGroup

theorem dihedral_central_of_comm {n : ℕ} {w a b : DihedralGroup n} (hab : a * b ≠ b * a)
    (ha : w * a = a * w) (hb : w * b = b * w) (x : DihedralGroup n) : w * x = x * w := by
  rcases w with k | k <;> rcases a with i | i <;> rcases b with j | j <;> rcases x with l | l <;>
    simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr, r.injEq, sr.injEq, ne_eq] at ha hb hab ⊢
  all_goals first
    | ring1
    | exact absurd (add_comm _ _) hab
    | linear_combination ha
    | linear_combination hb
    | exact absurd (by linear_combination -ha) hab
    | exact absurd (by linear_combination hb) hab
    | exact absurd (by linear_combination hb - ha) hab

theorem dihedral_noncomm {m : ℕ} (hm : 2 ≤ m) :
    (r 1 : DihedralGroup (2 ^ m)) * sr 0 ≠ sr 0 * r 1 := by
  simp only [r_mul_sr, sr_mul_r, ne_eq, sr.injEq, zero_sub, zero_add]
  intro h
  have h2 : ((2 : ℕ) : ZMod (2 ^ m)) = 0 := by
    push_cast
    linear_combination -h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h4 : 2 ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm
  have := Nat.le_of_dvd (by norm_num) (h4.trans h2)
  norm_num at this

theorem og_psl2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {P H : Subgroup (PSL2 (ZMod p))} {m : ℕ}
    (hm : 2 ≤ m) (eP : ↥P ≃* DihedralGroup (2 ^ m)) (hPH : P ≤ H) {z : PSL2 (ZMod p)}
    (hzP : z ∈ P) (hz2 : orderOf z = 2) (hzc : ∀ x ∈ P, z * x = x * z) :
    H = ⊤ ∨ H ≤ Subgroup.centralizer ({z} : Set (PSL2 (ZMod p))) ∨
      Nonempty (↥H ≃* Equiv.Perm (Fin 4)) := by
  have hp : p.Prime := Fact.out
  have hF : Nat.card (ZMod p) = p ^ 1 := by rw [Nat.card_zmod, pow_one]
  set a : PSL2 (ZMod p) := (eP.symm (r 1)).1 with ha
  set b : PSL2 (ZMod p) := (eP.symm (sr 0)).1 with hb
  have haP : a ∈ P := (eP.symm (r 1)).2
  have hbP : b ∈ P := (eP.symm (sr 0)).2
  have hab : a * b ≠ b * a := by
    intro h
    apply dihedral_noncomm hm
    have h' : eP.symm (r 1) * eP.symm (sr 0) = eP.symm (sr 0) * eP.symm (r 1) := Subtype.ext h
    rw [← map_mul, ← map_mul] at h'
    exact eP.symm.injective h'
  have hcardP : Nat.card P = 2 * 2 ^ m := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have h8 : 8 ∣ Nat.card H := by
    have h1 : Nat.card P ∣ Nat.card H := Subgroup.card_dvd_of_le hPH
    have h2 : 2 * 2 ^ 2 ∣ 2 * 2 ^ m := Nat.mul_dvd_mul_left 2 (pow_dvd_pow 2 hm)
    rw [hcardP] at h1
    exact h2.trans h1
  rcases CFSG.Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hF H with
    h | ⟨z₀, -, -, hcyc⟩ | ⟨z₀, -, -, ⟨eH⟩⟩ | ⟨-, ⟨eH⟩⟩ | ⟨-, ⟨eH⟩⟩ | ⟨-, ⟨eH⟩⟩ |
      ⟨m', t, -, -, N, C, hN, hNe, -, hC, -, -, hNC⟩ | ⟨m', hm', hm1, ⟨eH⟩⟩ | ⟨m', hm', hm1, -⟩
  · exfalso
    have hpz : (⟨z, hPH hzP⟩ : ↥H) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.exponent_dvd_p _
    have hzd : orderOf z ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hpz
    rw [hz2] at hzd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hzd).symm
  · exfalso
    apply hab
    have := hcyc.commGroup.mul_comm ⟨a, hPH haP⟩ ⟨b, hPH hbP⟩
    exact congrArg Subtype.val this
  · right; left
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hab' : eH ⟨a, hPH haP⟩ * eH ⟨b, hPH hbP⟩ ≠ eH ⟨b, hPH hbP⟩ * eH ⟨a, hPH haP⟩ := by
      rw [← map_mul, ← map_mul]
      intro h'
      exact hab (congrArg Subtype.val (eH.injective h'))
    have hcomm : ∀ x (hx : x ∈ P), eH ⟨z, hPH hzP⟩ * eH ⟨x, hPH hx⟩ =
        eH ⟨x, hPH hx⟩ * eH ⟨z, hPH hzP⟩ := by
      intro x hx
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hzc x hx)
    have hc := dihedral_central_of_comm hab' (hcomm a haP) (hcomm b hbP) (eH ⟨h, hh⟩)
    rw [← map_mul, ← map_mul] at hc
    exact (congrArg Subtype.val (eH.injective hc)).symm
  · exfalso
    rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card] at h8
    exact absurd h8 (by decide)
  · right; right; exact ⟨eH⟩
  · exfalso
    rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card] at h8
    exact absurd h8 (by decide)
  · exfalso
    have := hN
    have hc := CFSG.Glauberman.Dickson.MaxUp.overgroup_comm_mem N C hC hNC ⟨a, hPH haP⟩
      ⟨b, hPH hbP⟩
    set c : ↥H := ⟨a, hPH haP⟩ * ⟨b, hPH hbP⟩ * (⟨a, hPH haP⟩)⁻¹ * (⟨b, hPH hbP⟩)⁻¹ with hcdef
    have hcp : c ^ p = 1 := by
      have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hNe.exponent_dvd_p ⟨c, hc⟩
      exact congrArg Subtype.val this
    have hcP : (c : PSL2 (ZMod p)) ∈ P := by
      simp only [hcdef, Subgroup.coe_mul, Subgroup.coe_inv]
      exact P.mul_mem (P.mul_mem (P.mul_mem haP hbP) (P.inv_mem haP)) (P.inv_mem hbP)
    have hc2 : (c : PSL2 (ZMod p)) ^ (2 * 2 ^ m) = 1 := by
      have := pow_card_eq_one' (G := ↥P) (x := ⟨c, hcP⟩)
      rw [hcardP] at this
      exact congrArg Subtype.val this
    have hco : Nat.Coprime p (2 * 2 ^ m) := by
      rw [← pow_succ']
      exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have hd1 : orderOf (c : PSL2 (ZMod p)) ∣ p := by
      apply orderOf_dvd_of_pow_eq_one
      simpa using congrArg Subtype.val hcp
    have hd2 : orderOf (c : PSL2 (ZMod p)) ∣ 2 * 2 ^ m := orderOf_dvd_of_pow_eq_one hc2
    have hg := Nat.dvd_gcd hd1 hd2
    rw [hco.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hg
    apply hab
    have hg' : a * b * a⁻¹ * b⁻¹ = 1 := by simpa [hcdef] using hg
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hg', one_mul]
  · left
    obtain rfl : m' = 1 := Nat.dvd_one.mp hm1
    apply (Subgroup.card_eq_iff_eq_top H).mp
    rw [Nat.card_congr eH.toEquiv, CFSG.Glauberman.Dickson.MaxUp.card_psl2_galoisField hp2
      one_ne_zero, CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF hp2]
    ring_nf
  · exfalso
    have := Nat.le_of_dvd one_pos hm1
    omega

theorem isKleinFour_of_sq {H : Type*} [Group H] (h4 : Nat.card H = 4) (hsq : ∀ x : H, x * x = 1) :
    IsKleinFour H := by
  refine ⟨h4, ?_⟩
  have hdvd : Monoid.exponent H ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by rw [pow_two]; exact hsq x
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h

theorem isKleinFour_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : IsKleinFour Y) :
    IsKleinFour X :=
  ⟨by rw [Nat.card_congr e.toEquiv]; exact h.card_four,
    by rw [Monoid.exponent_eq_of_mulEquiv e]; exact h.exponent_two⟩

private def k4Set : Finset (Equiv.Perm (Fin 4)) :=
  {1, Equiv.swap 0 1 * Equiv.swap 2 3, Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2}

private theorem k4Set_mul : ∀ a ∈ k4Set, ∀ b ∈ k4Set, a * b ∈ k4Set := by decide

private theorem k4Set_conj : ∀ g : Equiv.Perm (Fin 4), ∀ a ∈ k4Set, g * a * g⁻¹ ∈ k4Set := by
  decide

private theorem k4Set_sq : ∀ a ∈ k4Set, a * a = 1 := by decide

private def k4 : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := k4Set
  mul_mem' {a b} ha hb := k4Set_mul a ha b hb
  one_mem' := by decide
  inv_mem' {a} ha := by
    have h : a⁻¹ = a := inv_eq_of_mul_eq_one_right (k4Set_sq a ha)
    simpa [h] using ha

private theorem k4_normal : k4.Normal :=
  ⟨fun a ha g => k4Set_conj g a ha⟩

private theorem k4_isKleinFour : IsKleinFour ↥k4 := by
  refine isKleinFour_of_sq ?_ fun x => Subtype.ext (k4Set_sq x.1 x.2)
  have e : ↥k4 ≃ {x // x ∈ k4Set} := Equiv.refl _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  decide

theorem exists_normal_kleinFour_of_perm4 {L : Type*} [Group L] {H : Subgroup L}
    (eH : ↥H ≃* Equiv.Perm (Fin 4)) :
    ∃ W : Subgroup L, W ≤ H ∧ IsKleinFour ↥W ∧ H ≤ Subgroup.normalizer (W : Set L) := by
  set W' : Subgroup ↥H := k4.map eH.symm.toMonoidHom with hW'
  set W : Subgroup L := W'.map H.subtype with hW
  have hWH : W ≤ H := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  refine ⟨W, hWH, ?_, ?_⟩
  · have e1 : ↥k4 ≃* ↥W := (k4.equivMapOfInjective _ eH.symm.injective).trans
      (W'.equivMapOfInjective _ H.subtype_injective)
    exact isKleinFour_of_equiv e1.symm k4_isKleinFour
  · have hsub : W.subgroupOf H = W' :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective W'
    have hn : W'.Normal := k4_normal.map eH.symm.toMonoidHom eH.symm.surjective
    rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hWH, hsub]
    exact hn

theorem klein_three {G : Type*} [Group G] {R U V W : Subgroup G} (f : ↥R ≃* DihedralGroup 4)
    (hUR : U ≤ R) (hVR : V ≤ R) (hWR : W ≤ R) (hU : IsKleinFour ↥U) (hV : IsKleinFour ↥V)
    (hW : IsKleinFour ↥W) : U = V ∨ U = W ∨ V = W := by
  classical
  let D : Subgroup G → Finset (DihedralGroup 4) := fun X =>
    Finset.univ.filter (fun d => ((f.symm d : ↥R) : G) ∈ X)
  have hD : ∀ X d, d ∈ D X ↔ ((f.symm d : ↥R) : G) ∈ X := by
    intro X d
    simp [D]
  have hcard : ∀ X : Subgroup G, X ≤ R → Nat.card X = (D X).card := by
    intro X hXR
    have e : ↥X ≃ {d // d ∈ D X} :=
      { toFun := fun a => ⟨f ⟨a, hXR a.2⟩, by rw [hD]; simp⟩
        invFun := fun d => ⟨((f.symm d : ↥R) : G), (hD X d).mp d.2⟩
        left_inv := fun a => by ext; simp
        right_inv := fun d => by ext; simp }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have hmul : ∀ X : Subgroup G, ∀ d ∈ D X, ∀ d' ∈ D X, d * d' ∈ D X := by
    intro X d hd d' hd'
    rw [hD] at hd hd' ⊢
    have : ((f.symm (d * d') : ↥R) : G) = ((f.symm d : ↥R) : G) * ((f.symm d' : ↥R) : G) := by
      rw [map_mul]
      rfl
    rw [this]
    exact X.mul_mem hd hd'
  have hsq : ∀ X : Subgroup G, IsKleinFour ↥X → ∀ d ∈ D X, d * d = 1 := by
    intro X hX d hd
    rw [hD] at hd
    have h1 : ((f.symm d : ↥R) : G) * ((f.symm d : ↥R) : G) = 1 :=
      congrArg Subtype.val (hX.mul_self ⟨_, hd⟩)
    have h2 : f.symm (d * d) = f.symm 1 := by
      rw [map_mul, map_one]
      exact Subtype.ext h1
    exact f.symm.injective h2
  have hinj : ∀ X Y : Subgroup G, X ≤ R → Y ≤ R → D X = D Y → X = Y := by
    intro X Y hXR hYR h
    ext g
    constructor
    · intro hg
      have : f ⟨g, hXR hg⟩ ∈ D X := by rw [hD]; simpa using hg
      rw [h, hD] at this
      simpa using this
    · intro hg
      have : f ⟨g, hYR hg⟩ ∈ D Y := by rw [hD]; simpa using hg
      rw [← h, hD] at this
      simpa using this
  have hk : ∀ X : Subgroup G, X ≤ R → IsKleinFour ↥X →
      D X = {1, r 2, sr 0, sr 2} ∨ D X = {1, r 2, sr 1, sr 3} := fun X hXR hX =>
    CFSG.QuasithinUnique.DoubleA3.dihedral4_klein (D X) (by rw [← hcard X hXR, hX.card_four])
      (hsq X hX) (hmul X)
  rcases hk U hUR hU with h1 | h1 <;> rcases hk V hVR hV with h2 | h2 <;>
    rcases hk W hWR hW with h3 | h3
  · exact Or.inl (hinj U V hUR hVR (h1.trans h2.symm))
  · exact Or.inl (hinj U V hUR hVR (h1.trans h2.symm))
  · exact Or.inr (Or.inl (hinj U W hUR hWR (h1.trans h3.symm)))
  · exact Or.inr (Or.inr (hinj V W hVR hWR (h2.trans h3.symm)))
  · exact Or.inr (Or.inr (hinj V W hVR hWR (h2.trans h3.symm)))
  · exact Or.inr (Or.inl (hinj U W hUR hWR (h1.trans h3.symm)))
  · exact Or.inl (hinj U V hUR hVR (h1.trans h2.symm))
  · exact Or.inl (hinj U V hUR hVR (h1.trans h2.symm))

theorem kleinFour_comm {G : Type*} [Group G] {V : Subgroup G} (hV : IsKleinFour ↥V) {x y : G}
    (hx : x ∈ V) (hy : y ∈ V) : x * y = y * x := by
  have h1 : x * y * (x * y) = 1 := congrArg Subtype.val (hV.mul_self ⟨x * y, V.mul_mem hx hy⟩)
  have h2 : x * x = 1 := congrArg Subtype.val (hV.mul_self ⟨x, hx⟩)
  have h3 : y * y = 1 := congrArg Subtype.val (hV.mul_self ⟨y, hy⟩)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3]

section Model

variable {p : ℕ} [Fact p.Prime] {L : Type} [Group L]

theorem isOddPrimePower_zmod (hp2 : p ≠ 2) : IsOddPrimePower (Nat.card (ZMod p)) :=
  ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, le_rfl, by simp⟩

theorem isPerfect_of_equiv (e : L ≃* PSL2 (ZMod p)) (hp7 : 7 ≤ p) : Group.IsPerfect L := by
  have := psl2_isPerfect_of_card_gt_three (ZMod p) (by rw [Nat.card_zmod]; omega)
  refine ⟨?_⟩
  have h := Subgroup.map_commutator (⊤ : Subgroup (PSL2 (ZMod p))) ⊤ e.symm.toMonoidHom
  have hc : ⁅(⊤ : Subgroup (PSL2 (ZMod p))), ⊤⁆ = ⊤ :=
    Group.IsPerfect.commutator_eq_top (G := PSL2 (ZMod p))
  rw [hc, Subgroup.map_top_of_surjective _ e.symm.surjective] at h
  exact h.symm

theorem sylow_dihedral_of_equiv (e : L ≃* PSL2 (ZMod p)) (hp2 : p ≠ 2)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) {P : Subgroup L} (hP : IsSylowIn 2 P ⊤) :
    ∃ m, 2 ≤ m ∧ Nonempty (↥P ≃* DihedralGroup (2 ^ m)) := by
  have hT : IsSylowIn 2 (P.map e.toMonoidHom) ⊤ := by
    have := (E1.isSylowIn_map_mulEquiv e (P := P) (H := ⊤)).mpr hP
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  obtain ⟨S, m, hS, hm, ⟨eS⟩⟩ := CFSG.Quasithin.E22L2.e22pl2psl_sylow_dihedral_q
    (isOddPrimePower_zmod hp2) (by rwa [Nat.card_zmod]) hT
  exact ⟨m, hm, ⟨((P.equivMapOfInjective _ e.injective).trans
    (MulEquiv.subgroupCongr hS.symm)).trans eS⟩⟩

theorem centralizer_kleinFour_of_equiv
    (e : L ≃* PSL2 (ZMod p)) (hp2 : p ≠ 2) {V : Subgroup L} (hV : IsKleinFour ↥V) :
    Subgroup.centralizer (V : Set L) = V := by
  have hV' : IsKleinFour ↥(V.map e.toMonoidHom) :=
    isKleinFour_of_equiv (V.equivMapOfInjective _ e.injective).symm hV
  have hc := psl2_kleinFour_centralizer_eq_self (ZMod p) (isOddPrimePower_zmod hp2) _ hV'
  apply le_antisymm
  · intro x hx
    have hex : e x ∈ Subgroup.centralizer ((V.map e.toMonoidHom : Subgroup _) : Set _) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨v, hv, rfl⟩
      have := Subgroup.mem_centralizer_iff.mp hx v hv
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, this]
    rw [hc] at hex
    obtain ⟨v, hv, hve⟩ := hex
    have : v = x := e.injective hve
    exact this ▸ hv
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact kleinFour_comm hV hw hv

theorem normalizer_surjective_of_equiv [Finite L] (e : L ≃* PSL2 (ZMod p)) (hp7 : 7 ≤ p)
    (hp8 : p % 8 = 1 ∨ p % 8 = 7) {V : Subgroup L} (hV : IsKleinFour ↥V) :
    Function.Surjective V.normalizerMonoidHom := by
  have := isPerfect_of_equiv e hp7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 ↥V := IsPGroup.of_card (n := 2) (by rw [hV.card_four]; norm_num)
  obtain ⟨S, hVS⟩ := h2.exists_le_sylow
  have hS : IsSylowIn 2 (S : Subgroup L) ⊤ := ⟨le_top, S.isPGroup', by
    rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index⟩
  obtain ⟨m, hm, ⟨eS⟩⟩ := sylow_dihedral_of_equiv e (by omega) hp8 hS
  exact perfect_dihedral_fourgroup_normalizer_surjective S hm eS V hVS hV

theorem card_normalizer_of_equiv
    [Finite L] (e : L ≃* PSL2 (ZMod p)) (hp7 : 7 ≤ p) (hp8 : p % 8 = 1 ∨ p % 8 = 7)
    {V : Subgroup L} (hV : IsKleinFour ↥V) : Nat.card (Subgroup.normalizer (V : Set L)) = 24 :=
  CFSG.Quasithin.E22L2.e22ps4_card_normalizer hV (centralizer_kleinFour_of_equiv e (by omega) hV)
    (normalizer_surjective_of_equiv e hp7 hp8 hV)

theorem og_of_equiv (e : L ≃* PSL2 (ZMod p)) (hp2 : p ≠ 2) {P H : Subgroup L} {m : ℕ}
    (hm : 2 ≤ m) (eP : ↥P ≃* DihedralGroup (2 ^ m)) (hPH : P ≤ H) {z : L} (hzP : z ∈ P)
    (hz2 : orderOf z = 2) (hzc : ∀ x ∈ P, z * x = x * z) :
    H = ⊤ ∨ H ≤ Subgroup.centralizer ({z} : Set L) ∨ Nonempty (↥H ≃* Equiv.Perm (Fin 4)) := by
  have eP' : ↥(P.map e.toMonoidHom) ≃* DihedralGroup (2 ^ m) :=
    (P.equivMapOfInjective _ e.injective).symm.trans eP
  have hzc' : ∀ x ∈ P.map e.toMonoidHom, e z * x = x * e z := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hzc y hy]
  rcases og_psl2 hp2 hm eP' (Subgroup.map_mono hPH) (Subgroup.mem_map_of_mem _ hzP)
      (by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]; exact hz2) hzc' with h | h | h
  · left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [h, Subgroup.map_top_of_surjective _ e.surjective]
  · right; left
    intro x hx
    have := h (Subgroup.mem_map_of_mem e.toMonoidHom hx)
    rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
    simp only [MulEquiv.coe_toMonoidHom] at this
    rw [← map_mul, ← map_mul] at this
    exact e.injective this
  · right; right
    obtain ⟨eH⟩ := h
    exact ⟨(H.equivMapOfInjective e.toMonoidHom e.injective).trans eH⟩

end Model

end CFSG.Quasithin.E2.E22N.E111L
