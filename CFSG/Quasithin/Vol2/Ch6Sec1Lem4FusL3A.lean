module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Lev
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3PGL

public section

namespace CFSG.Quasithin.H13

open CFSG.GorensteinWalter CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem exists_eq_zpowers_of_L3FusFacts {G : Type} [Group G] [Finite G] {N T X : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (h : L3FusFacts N p) (hT2 : IsPGroup 2 T) (hXN : X ≤ N)
    (hXO : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) :
    ∃ y : G, orderOf y = 5 ∧ X = Subgroup.zpowers y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrank : ∀ V : Subgroup G, V ≤ N → IsElemAbelian 2 V → Nat.card V ≤ 4 := h.rank
  set P := X ⊓ T with hP
  have hP2 : IsPGroup 2 P := hT2.to_le inf_le_right
  have hPX : P ≤ X := inf_le_left
  have hcardX : Nat.card X = 5 * Nat.card P := by
    have := Subgroup.relIndex_mul_card P X
    rw [hX5, inf_of_le_left hPX] at this
    exact this.symm
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5
    (by rw [hcardX]; exact dvd_mul_right _ _)
  set y : G := (y' : G) with hydef
  have hyX : y ∈ X := y'.2
  have hy5 : orderOf y = 5 := by rw [hydef, Subgroup.orderOf_coe]; exact hy'
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hPy : ∀ c, c ∈ P → c ∈ Subgroup.zpowers y → c = 1 := by
    intro c hcP hcy
    obtain ⟨k, hk⟩ := hP2 ⟨c, hcP⟩
    exact eq_one_of_mem_zpowers_of_pow_two614 hy5' hcy (by simpa using congrArg Subtype.val hk)
  have hXP : ∀ g ∈ X, ∀ q ∈ P, g * q * g⁻¹ ∈ P := by
    intro g hg q hq
    exact hXn.conj_mem ⟨q, hq.1⟩ (show (⟨q, hq.1⟩ : ↥X) ∈ P.subgroupOf X from hq) ⟨g, hg⟩
  have hdecomp : ∀ x ∈ X, ∃ i : ℤ, (y ^ i)⁻¹ * x ∈ P := by
    intro x hxX
    set Q := ↥X ⧸ P.subgroupOf X with hQdef
    have hQ : Nat.card Q = 5 := hX5
    have hyQ : ((y' : ↥X) : Q) ≠ 1 := by
      intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      have := hPy y h1 (Subgroup.mem_zpowers y)
      rw [this, orderOf_one] at hy5
      exact absurd hy5 (by norm_num)
    have htop : Subgroup.zpowers ((y' : ↥X) : Q) = ⊤ :=
      zpowers_eq_top_of_prime_card (p := 5) hQ hyQ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      (htop.symm ▸ Subgroup.mem_top (((⟨x, hxX⟩ : ↥X)) : Q))
    refine ⟨i, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hi
    have h2 : (((y' ^ i)⁻¹ * ⟨x, hxX⟩ : ↥X) : G) ∈ P := hi
    simpa [hydef] using h2
  have hycomm : ∀ q ∈ P, Commute y q := by
    by_cases hPb : P = ⊥
    · intro q hq
      rw [hPb, Subgroup.mem_bot] at hq
      rw [hq]
      exact Commute.one_right y
    let W : Subgroup G :=
      { carrier := {u | u ∈ P ∧ (∀ q ∈ P, Commute u q) ∧ u ^ 2 = 1}
        mul_mem' := by
          rintro a b ⟨haP, hac, ha2⟩ ⟨hbP, hbc, hb2⟩
          refine ⟨P.mul_mem haP hbP, fun q hq => (hac q hq).mul_left (hbc q hq), ?_⟩
          rw [pow_two, mul_assoc, ← mul_assoc b, ← (hac b hbP).eq, mul_assoc, ← pow_two b, hb2,
            mul_one, ← pow_two, ha2]
        one_mem' := ⟨P.one_mem, fun q _ => Commute.one_left q, one_pow 2⟩
        inv_mem' := by
          rintro a ⟨haP, hac, ha2⟩
          refine ⟨P.inv_mem haP, fun q hq => (hac q hq).inv_left, ?_⟩
          rw [inv_pow, ha2, inv_one] }
    have hWP : W ≤ P := fun u hu => hu.1
    have hWab : IsElemAbelian 2 W := by
      refine ⟨⟨⟨fun a b => Subtype.ext ((a.2.2.1 b (hWP b.2)).eq)⟩⟩, fun u hu => hu.2.2⟩
    have hW4 : Nat.card W ≤ 4 := hrank W ((hWP.trans hPX).trans hXN) hWab
    have hWne : ∃ u ∈ W, u ≠ 1 := by
      have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPb
      have hZ := hP2.center_nontrivial
      have hZ2 : IsPGroup 2 (Subgroup.center ↥P) := hP2.to_subgroup _
      have h2Z : 2 ∣ Nat.card (Subgroup.center ↥P) := by
        rcases hZ2.card_eq_or_dvd with h | h
        · exact absurd h (Finite.one_lt_card).ne'
        · exact h
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) 2 h2Z
      refine ⟨((u : ↥P) : G), ⟨(u : ↥P).2, fun q hq => ?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_center_iff.mp u.2 ⟨q, hq⟩)
        exact (congrArg Subtype.val this).symm
      · have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
        have := congrArg (fun v : ↥(Subgroup.center ↥P) => ((v : ↥P) : G)) this
        simpa using this
      · intro h1
        have : u = 1 := Subtype.ext (Subtype.ext h1)
        rw [this, orderOf_one] at hu
        exact absurd hu (by norm_num)
    obtain ⟨u, huW, hu1⟩ := hWne
    have hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
      rintro w ⟨hwP, hwc, hw2⟩
      refine ⟨hXP y hyX w hwP, fun q hq => ?_, ?_⟩
      · have hq' : y⁻¹ * q * y⁻¹⁻¹ ∈ P := hXP y⁻¹ (X.inv_mem hyX) q hq
        have h1 := hwc _ hq'
        rw [inv_inv] at hq' h1
        have e : q = y * (y⁻¹ * q * y) * y⁻¹ := by group
        show y * w * y⁻¹ * q = q * (y * w * y⁻¹)
        rw [e]
        calc y * w * y⁻¹ * (y * (y⁻¹ * q * y) * y⁻¹) = y * (w * (y⁻¹ * q * y)) * y⁻¹ := by
              group
          _ = y * ((y⁻¹ * q * y) * w) * y⁻¹ := by rw [h1.eq]
          _ = y * (y⁻¹ * q * y) * y⁻¹ * (y * w * y⁻¹) := by group
      · have e : (y * w * y⁻¹) ^ 2 = y * w ^ 2 * y⁻¹ := by rw [pow_two, pow_two]; group
        rw [e, hw2]
        group
    have hyWinv : ∀ w ∈ W, y⁻¹ * w * y ∈ W := by
      intro w hw
      have h4 : ∀ n : ℕ, y ^ n * w * (y ^ n)⁻¹ ∈ W := by
        intro n
        induction n with
        | zero => simpa using hw
        | succ n ih =>
          have := hyW _ ih
          rw [pow_succ']
          convert this using 1
          group
      have := h4 4
      have e : y ^ 4 = y⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hy5']
      rw [e, inv_inv] at this
      exact this
    let σ : Equiv.Perm ↥W :=
      { toFun := fun w => ⟨y * w * y⁻¹, hyW w w.2⟩
        invFun := fun w => ⟨y⁻¹ * w * y, hyWinv w w.2⟩
        left_inv := fun w => Subtype.ext (by simp [mul_assoc])
        right_inv := fun w => Subtype.ext (by simp [mul_assoc]) }
    have hσpow : ∀ (n : ℕ) (w : ↥W), ((σ ^ n) w : G) = y ^ n * w * (y ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ', Equiv.Perm.mul_apply]
        show y * (((σ ^ n) w : ↥W) : G) * y⁻¹ = _
        rw [ih]
        group
    have hσ5 : σ ^ 5 = 1 := by
      ext w
      rw [hσpow, hy5']
      simp
    have hσ1 : σ = 1 := by
      have hd1 : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
      have hd2 : orderOf σ ∣ (Nat.card W).factorial := by
        have := orderOf_dvd_natCard σ
        rwa [Nat.card_perm] at this
      have hd3 : (Nat.card W).factorial ∣ 24 := by
        have := Nat.factorial_dvd_factorial hW4
        rwa [show Nat.factorial 4 = 24 from rfl] at this
      have : orderOf σ = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd1 with h | h
        · exact h
        · rw [h] at hd2
          have := hd2.trans hd3
          norm_num at this
      exact orderOf_eq_one_iff.mp this
    have hyu : Commute y u := by
      have := congrArg (fun τ : Equiv.Perm ↥W => ((τ ⟨u, huW⟩ : ↥W) : G)) hσ1
      simp only [Equiv.Perm.coe_one, id_eq] at this
      have e : y * u * y⁻¹ = u := this
      show y * u = u * y
      calc y * u = y * u * y⁻¹ * y := by group
        _ = u * y := by rw [e]
    have hu2 : orderOf u = 2 := orderOf_eq_prime huW.2.2 hu1
    have huN : u ∈ N := hXN (hPX (hWP huW))
    have hpu : ∀ q ∈ P, Commute q u := fun q hq => (huW.2.1 q hq).symm
    set C : Subgroup G := N ⊓ Subgroup.centralizer ({u} : Set G) with hCdef
    have hCmem : ∀ c : G, c ∈ C ↔ c ∈ N ∧ Commute c u := by
      intro c
      rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      rfl
    have hKdef : leviOfL3 N u = ⁅C, C⁆ := rfl
    have hyC : y ∈ C := (hCmem y).mpr ⟨hXN hyX, hyu⟩
    have hPC : P ≤ C := fun q hq => (hCmem q).mpr ⟨hXN (hPX hq), hpu q hq⟩
    have hCc : ∀ d ∈ C, ∀ x ∈ C, d * x * d⁻¹ ∈ C := by
      intro d hd x hx
      obtain ⟨hdN, hdu⟩ := (hCmem d).mp hd
      obtain ⟨hxN, hxu⟩ := (hCmem x).mp hx
      exact (hCmem _).mpr ⟨N.mul_mem (N.mul_mem hdN hxN) (N.inv_mem hdN),
        (hdu.mul_left hxu).mul_left hdu.inv_left⟩
    have hK_conj : ∀ d ∈ C, ∀ x ∈ leviOfL3 N u, d * x * d⁻¹ ∈ leviOfL3 N u := by
      intro d hd x hx
      rw [hKdef] at hx ⊢
      have hmapC : C.map (MulAut.conj d).toMonoidHom ≤ C := by
        rintro _ ⟨c, hc, rfl⟩
        exact hCc d hd c hc
      have hmap : (⁅C, C⁆ : Subgroup G).map (MulAut.conj d).toMonoidHom ≤ ⁅C, C⁆ := by
        rw [Subgroup.map_commutator]
        exact Subgroup.commutator_mono hmapC hmapC
      exact hmap ⟨x, hx, rfl⟩
    have hCN : C ≤ Subgroup.normalizer ((leviOfL3 N u : Subgroup G) : Set G) := by
      intro c hc
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact hK_conj c hc n hn
      · intro hn
        have h1 := hK_conj c⁻¹ (C.inv_mem hc) (c * n * c⁻¹) hn
        have e : c⁻¹ * (c * n * c⁻¹) * c⁻¹⁻¹ = n := by group
        rw [e] at h1
        exact h1
    have hXC : X ≤ C := by
      intro x hx
      obtain ⟨i, hi⟩ := hdecomp x hx
      have h1 := C.mul_mem (C.zpow_mem hyC i) (hPC hi)
      rw [mul_inv_cancel_left] at h1
      exact h1
    have hXNK : X ≤ Subgroup.normalizer ((leviOfL3 N u : Subgroup G) : Set G) := hXC.trans hCN
    obtain ⟨hKL, hc⟩ := h.levi u huN hu2
    obtain ⟨F, hFf, hFfin, ψ, hcard, -, -, hψker⟩ := hKL.exists_action hp hp5
    have hKp' : IsOddPrimePower (Nat.card F) :=
      ⟨p, 1, hp, hp.odd_of_ne_two (by omega), le_rfl, by rw [hcard, pow_one]⟩
    have hcard3 : 3 < Nat.card F := by rw [hcard]; omega
    have htopPGL : pGammaL2PGLRange F = ⊤ := pGammaL2PGLRange_eq_top614 hp hcard
    haveI : Finite (F ≃+* F) :=
      Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
        intro e f hef
        ext x
        exact congrFun hef x)
    haveI : Finite (PGL2 F) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    haveI : Finite (PGammaL2 F) :=
      Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) (by
        intro x y hxy
        exact SemidirectProduct.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
    set sX : ↥X →* PGammaL2 F := ψ.comp (Subgroup.inclusion hXNK) with hsX
    by_cases hy1 : sX ⟨y, hyX⟩ = 1
    ·
      intro q hq
      have hyK : y ∈ Subgroup.centralizer ((leviOfL3 N u : Subgroup G) : Set G) :=
        hψker y (hCN hyC) hy1
      exact hc y (hXN hyX) hyu hyK q (hXN (hPX hq)) (hpu q hq)
    ·
      have hyX5 : sX ⟨y, hyX⟩ ^ 5 = 1 := by
        rw [← map_pow]
        have h5 : (⟨y, hyX⟩ : ↥X) ^ 5 = 1 := Subtype.ext (by simpa using hy5')
        rw [h5, map_one]
      set T' : Subgroup (PGammaL2 F) := (P.subgroupOf X).map sX with hT'def
      set X' : Subgroup (PGammaL2 F) := sX.range with hX'def
      have hT'2 : IsPGroup 2 T' := (hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm).map sX
      have hT'X' : T' ≤ X' := by
        rw [hX'def, MonoidHom.range_eq_map]
        exact Subgroup.map_mono le_top
      have hX'N : X' ≤ pGammaL2PGLRange F := by
        rw [htopPGL]
        exact le_top
      have hX'O : X' = oTwoUpper X' := by
        have h1 : oTwoUpper (⊤ : Subgroup ↥X) = ⊤ := by
          apply Subgroup.map_injective X.subtype_injective
          rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
          exact hXO.symm
        rw [hX'def, MonoidHom.range_eq_map, oTwoUpper_map, h1]
      have hsub : T'.subgroupOf X' = (P.subgroupOf X).map sX.rangeRestrict := by
        ext z
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · intro hz
          obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
          exact ⟨x, hx, Subtype.ext hxz⟩
        · rintro ⟨x, hx, rfl⟩
          exact Subgroup.mem_map_of_mem sX hx
      have hT'n : (T'.subgroupOf X').Normal := by
        rw [hsub]
        exact hXn.map _ (MonoidHom.rangeRestrict_surjective sX)
      have hdvd : (T'.subgroupOf X').index ∣ 5 := by
        rw [hsub]
        have h5 : (P.subgroupOf X).index = 5 := hX5
        have := Subgroup.index_map_dvd (P.subgroupOf X) (MonoidHom.rangeRestrict_surjective sX)
        rwa [h5] at this
      have hX'n : ((X' ⊓ T').subgroupOf X').Normal := by
        rw [inf_eq_right.mpr hT'X']
        exact hT'n
      have hX5' : (X' ⊓ T').relIndex X' = 5 := by
        rw [inf_eq_right.mpr hT'X']
        show (T'.subgroupOf X').index = 5
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h1
        · exfalso
          have h1r : T'.relIndex X' = 1 := h1
          have hle : X' ≤ T' := Subgroup.relIndex_eq_one.mp h1r
          have hmemX : sX ⟨y, hyX⟩ ∈ X' := MonoidHom.mem_range.mpr ⟨⟨y, hyX⟩, rfl⟩
          obtain ⟨k, hk⟩ := hT'2 ⟨_, hle hmemX⟩
          have hk' : sX ⟨y, hyX⟩ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
          exact hy1 (eq_one_of_mem_zpowers_of_pow_two614 hyX5 (Subgroup.mem_zpowers _) hk')
        · exact h1
      obtain ⟨y₂, hy₂5, hX'y₂⟩ := exists_eq_zpowers_of_relIndex_five614 (N := pGammaL2PGLRange F)
        (T := T') (X := X')
        (fun V hV hVe => card_le_four_of_isElemAbelian_pglRange614 hKp' hcard3 V hV hVe)
        (fun a b c ha hb hc' ha5 hb2 hab hcb =>
          mem_normalizer_of_commute_pglRange614 hKp' hcard3 ha hb hc' ha5 hb2 hab hcb)
        hT'2 hX'N hX'O hX5' hX'n
      have hy₂5' : y₂ ^ 5 = 1 := by rw [← hy₂5]; exact pow_orderOf_eq_one y₂
      intro q hq
      have hqX : q ∈ X := hPX hq
      have hmem : sX ⟨q, hqX⟩ ∈ T' := Subgroup.mem_map_of_mem sX (Subgroup.mem_subgroupOf.mpr hq)
      have hmemZ : sX ⟨q, hqX⟩ ∈ Subgroup.zpowers y₂ := by
        rw [← hX'y₂]
        exact hT'X' hmem
      obtain ⟨k, hk⟩ := hT'2 ⟨_, hmem⟩
      have hk' : sX ⟨q, hqX⟩ ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hq1 : sX ⟨q, hqX⟩ = 1 := eq_one_of_mem_zpowers_of_pow_two614 hy₂5' hmemZ hk'
      have hqK : q ∈ Subgroup.centralizer ((leviOfL3 N u : Subgroup G) : Set G) :=
        hψker q (hXNK hqX) hq1
      exact (hc q (hXN hqX) (hpu q hq) hqK y (hXN hyX) hyu).symm
  refine ⟨y, hy5, le_antisymm ?_ ?_⟩
  · rw [hXO, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hxX, hxo⟩
    obtain ⟨i, hi⟩ := hdecomp x hxX
    set q := (y ^ i)⁻¹ * x with hqdef
    have hx : x = y ^ i * q := by rw [hqdef]; group
    have hqy : Commute (y ^ i) q := (hycomm q hi).zpow_left i
    obtain ⟨k, hk⟩ := hP2 ⟨q, hi⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    set m := orderOf x with hmdef
    have hm : q ^ m = 1 := by
      have h1 : x ^ m = 1 := pow_orderOf_eq_one x
      rw [hx, hqy.mul_pow] at h1
      have h2 : (y ^ i) ^ m ∈ Subgroup.zpowers y := by
        rw [← zpow_natCast, ← zpow_mul]
        exact Subgroup.zpow_mem_zpowers _ _
      have h3 : q ^ m = ((y ^ i) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h4 : q ^ m ∈ Subgroup.zpowers y := h3 ▸ Subgroup.inv_mem _ h2
      exact hPy _ (P.pow_mem hi _) h4
    have hq1 := eq_one_of_pow_two_of_odd614 hk' hm hxo
    rw [hx, hq1, mul_one]
    exact Subgroup.zpow_mem_zpowers y i
  · rw [Subgroup.zpowers_le]
    exact hyX

end CFSG.Quasithin.H13
