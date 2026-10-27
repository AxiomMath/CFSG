module

public import CFSG.OddTranspositions.G2Chain
public import CFSG.OddTranspositions.TheoremTwo.ImageConnected
public import CFSG.OddTranspositions.WidthOne
import CFSG.OddTranspositions.SixSixK

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

open scoped Pointwise

section Bender

variable {K : Type*} [Group K] [Finite K]

theorem commute_of_even_orderOf_mul_of_isBenderGroup
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) {s t : K}
    (hs : s * s = 1) (ht : t * t = 1) (heven : Even (orderOf (s * t))) : Commute s t := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := heven
  have hpos : 0 < orderOf (s * t) := orderOf_pos _
  have hk0 : k ≠ 0 := by omega
  set c := (s * t) ^ k with hc
  have hc2 : orderOf c = 2 := by
    rw [hc, orderOf_pow_of_dvd hk0 ⟨2, by omega⟩, hk]
    exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hk0) (by ring)
  have hcc : c * c = 1 := by rw [← sq, ← hc2, pow_orderOf_eq_one]
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hst : (s * t)⁻¹ = t * s := by rw [mul_inv_rev, hsinv, htinv]
  have hsc : s * c * s⁻¹ = c := by
    have h1 : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
      rw [hst, hsinv, ← mul_assoc, hs, one_mul]
    rw [hc, ← conj_pow, h1, inv_pow, ← hc, hcinv]
  have htc : t * c * t⁻¹ = c := by
    have h1 : t * (s * t) * t⁻¹ = (s * t)⁻¹ := by
      rw [hst, htinv, mul_assoc, mul_assoc, ht, mul_one]
    rw [hc, ← conj_pow, h1, inv_pow, ← hc, hcinv]
  have hsc' : Commute s c := mul_inv_eq_iff_eq_mul.mp hsc
  have htc' : Commute t c := mul_inv_eq_iff_eq_mul.mp htc
  have hcP : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc2, pow_one])
  obtain ⟨Q, hQ⟩ := hcP.exists_le_sylow
  have hcQ : c ∈ Q := hQ (Subgroup.mem_zpowers c)
  have hM := Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer hK Q
  have hcN : c ∈ Subgroup.normalizer (Q : Set K) := Subgroup.le_normalizer hcQ
  have hcent : ∀ g : K, Commute g c → g ∈ Subgroup.normalizer (Q : Set K) := by
    intro g hg
    by_contra hgN
    have hodd := hM.2.2 g hgN
    have hmem : c ∈ Subgroup.normalizer (Q : Set K) ⊓
        (Subgroup.normalizer (Q : Set K)).map (MulAut.conj g).toMonoidHom :=
      ⟨hcN, c, hcN, by simp [MulAut.conj_apply, hg.eq]⟩
    have hdvd : 2 ∣ Nat.card (Subgroup.normalizer (Q : Set K) ⊓
        (Subgroup.normalizer (Q : Set K)).map (MulAut.conj g).toMonoidHom : Subgroup K) := by
      have := orderOf_dvd_natCard (⟨c, hmem⟩ : (Subgroup.normalizer (Q : Set K) ⊓
        (Subgroup.normalizer (Q : Set K)).map (MulAut.conj g).toMonoidHom : Subgroup K))
      rwa [Subgroup.orderOf_mk, hc2] at this
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hmemQ : ∀ x : K, x * x = 1 → x ∈ Subgroup.normalizer (Q : Set K) → x ∈ Q := by
    intro x hx hxN
    have hxo : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx)
    have hxP : IsPGroup 2 (Subgroup.zpowers x) := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hxo with h | h
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
    have hx' : x ∈ Subgroup.zpowers x ⊓ Subgroup.normalizer (Q : Set K) :=
      ⟨Subgroup.mem_zpowers x, hxN⟩
    rw [hxP.inf_normalizer_sylow Q] at hx'
    exact hx'.2
  exact Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q (hmemQ s hs (hcent s hsc')) hs t
    (hmemQ t ht (hcent t htc'))

theorem false_of_isThirdKind_of_isBenderGroup (hK : CFSG.BenderSuzuki.IsBenderGroup K)
    {x y t : K} (hx : x * x = 1) (hy : y * y = 1) (ht : t * t = 1) (hxt : Commute x t)
    (h3 : IsThirdKind x y t) : False := by
  obtain ⟨n, -, hn1, hord⟩ := h3
  have hs : x * t * (x * t) = 1 := by
    calc x * t * (x * t) = x * (t * x) * t := by simp only [mul_assoc]
      _ = x * (x * t) * t := by rw [← hxt.eq]
      _ = x * x * (t * t) := by simp only [mul_assoc]
      _ = 1 := by rw [hx, ht, one_mul]
  have hc := commute_of_even_orderOf_mul_of_isBenderGroup hK hs hy
    (by rw [hord]; exact even_two_mul n)
  have h2 : (x * t * y) ^ 2 = 1 := by
    calc (x * t * y) ^ 2 = x * t * (y * (x * t)) * y := by rw [sq]; simp only [mul_assoc]
      _ = x * t * (x * t * y) * y := by rw [← hc.eq]
      _ = x * t * (x * t) * (y * y) := by simp only [mul_assoc]
      _ = 1 := by rw [hs, hy, one_mul]
  have hdvd : orderOf (x * t * y) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hord] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

end Bender

theorem eq_one_of_isSimpleGroup_of_odd_index_two {A Q : Type*} [Group A] [Finite A] [Group Q]
    [Finite Q] [IsSimpleGroup A] (hA2 : 2 < Nat.card A) (hAe : Even (Nat.card A))
    {P : Subgroup Q} [P.Normal] (hPo : Odd (Nat.card P)) (hP2 : P.index = 2) (ψ : A →* Q) :
    ∀ a, ψ a = 1 := by
  classical
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exfalso
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp h
    let ψ' : A →* Q ⧸ P := (QuotientGroup.mk' P).comp ψ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ'.ker with h' | h'
    · have hle := Nat.card_le_card_of_injective ψ' ((MonoidHom.ker_eq_bot_iff ψ').mp h')
      rw [← Subgroup.index_eq_card, hP2] at hle
      omega
    · have hmem : ∀ a, ψ a ∈ P := fun a => by
        have ha : a ∈ ψ'.ker := h' ▸ Subgroup.mem_top a
        rw [MonoidHom.mem_ker] at ha
        exact (QuotientGroup.eq_one_iff _).mp ha
      let f : A →* P := ψ.codRestrict P hmem
      have hf : Function.Injective f := fun a b hab => hinj (congrArg Subtype.val hab)
      have hdvd := Subgroup.card_dvd_of_injective f hf
      exact (Nat.not_even_iff_odd.mpr hPo)
        (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hAe).trans hdvd))
  · intro a
    have ha : a ∈ ψ.ker := h ▸ Subgroup.mem_top a
    exact ha

section MinimalNormal

variable {G : Type} [Group G] {M K : Subgroup G} [hMn : M.Normal]

theorem eq_bot_of_normal_of_inf_eq_bot (hMK : M ≤ K)
    (hC : Subgroup.centralizer (M : Set G) = ⊥) {N : Subgroup K} (hN : N.Normal)
    (hNM : N ⊓ M.subgroupOf K = ⊥) : N = ⊥ := by
  rw [eq_bot_iff]
  intro n hn
  have hcent : (n : G) ∈ Subgroup.centralizer (M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    let mK : K := ⟨m, hMK hm⟩
    have h1 : n * mK * n⁻¹ * mK⁻¹ ∈ N := by
      have := N.mul_mem hn (hN.conj_mem n⁻¹ (N.inv_mem hn) mK)
      simpa [mul_assoc] using this
    have h2 : n * mK * n⁻¹ * mK⁻¹ ∈ M.subgroupOf K := by
      rw [Subgroup.mem_subgroupOf]
      exact M.mul_mem (hMn.conj_mem m hm n) (M.inv_mem hm)
    have h3 : n * mK * n⁻¹ * mK⁻¹ ∈ N ⊓ M.subgroupOf K := ⟨h1, h2⟩
    rw [hNM, Subgroup.mem_bot] at h3
    have h4 : (n : G) * m * (n : G)⁻¹ * m⁻¹ = 1 := by
      simpa [mK] using congrArg (fun y : K => (y : G)) h3
    have h5 : (n : G) * m * (n : G)⁻¹ = m := mul_inv_eq_one.mp h4
    calc m * (n : G) = (n : G) * m * (n : G)⁻¹ * n := by rw [h5]
      _ = (n : G) * m := by group
  rw [hC, Subgroup.mem_bot] at hcent
  exact Subgroup.mem_bot.mpr (Subtype.ext hcent)

theorem eq_subgroupOf_of_isMinimalNormal (hMK : M ≤ K) (hMs : IsSimpleGroup M)
    (hC : Subgroup.centralizer (M : Set G) = ⊥) {N : Subgroup K}
    (hN : Asc72.IsMinimalNormal N) : N = M.subgroupOf K := by
  obtain ⟨hNn, hN1, hNmin⟩ := hN
  have hM0 := isMinimalNormal_subgroupOf hMK hMs
  have hM0n : (M.subgroupOf K).Normal := hMn.subgroupOf K
  have hinter : (N ⊓ M.subgroupOf K).Normal := by
    have := hNn
    have := hM0n
    infer_instance
  rcases hNmin _ hinter inf_le_left with h | h
  · exact absurd (eq_bot_of_normal_of_inf_eq_bot hMK hC hNn h) hN1
  · rcases hM0.2.2 N hNn (inf_eq_left.mp h) with h' | h'
    · exact absurd h' hN1
    · exact h'

theorem exists_conj_of_mem_sup_centralizer {X : Type*} [Group X] {M : Subgroup X} [M.Normal]
    {x y : X} (hy : y ∈ M ⊔ Subgroup.centralizer ({x} : Set X)) :
    ∃ m ∈ M, y * x * y⁻¹ = m * x * m⁻¹ := by
  have hy' : y ∈ (M : Set X) * (Subgroup.centralizer ({x} : Set X) : Set X) := by
    rw [← Subgroup.normal_mul]
    exact hy
  obtain ⟨m, hm, c, hc, rfl⟩ := hy'
  refine ⟨m, hm, ?_⟩
  have hcx : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  calc m * c * x * (m * c)⁻¹ = m * (c * x) * c⁻¹ * m⁻¹ := by group
    _ = m * (x * c) * c⁻¹ * m⁻¹ := by rw [hcx]
    _ = m * x * m⁻¹ := by group

end MinimalNormal

end CFSG.OddTranspositions

namespace CFSG.OddTranspositions.QZ

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions

open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {D : Set G} {u w v z a : G} {K₁ S' : Subgroup G}

namespace Config

theorem barOmega_triangle (hQ : Config D u w v z a K₁ S') {e : G}
    (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G))
    (huY : u ∈ thirdK D e) (hwY : w ∈ thirdK D e) (hvY : v ∈ thirdK D e) :
    IsTriangle (barOmega D e)
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) ⟨u, huY⟩)
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) ⟨w, hwY⟩)
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) ⟨v, hvY⟩) ∧
      IsThirdKind
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) ⟨u, huY⟩)
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) ⟨w, hwY⟩)
        (QuotientGroup.mk' (CFSG.solvableRadical (thirdK D e)) ⟨v, hvY⟩) := by
  classical
  set O := CFSG.solvableRadical (thirdK D e)
  have hKY : thirdK D z ≤ thirdK D e := thirdK_le_thirdK_of_le_centralizer hzK
  let φ : thirdK D z →* (thirdK D e ⧸ O) := (QuotientGroup.mk' O).comp (Subgroup.inclusion hKY)
  have hφ : Function.Injective φ := thirdK_z_to_Yb_injective hQ he hzK haK
  obtain ⟨-, -, huΔz, hvΔz, hwΔz, -⟩ := hQ.z_facts
  let u' : thirdK D z := ⟨u, Delta_subset_thirdK huΔz⟩
  let v' : thirdK D z := ⟨v, Delta_subset_thirdK hvΔz⟩
  let w' : thirdK D z := ⟨w, Delta_subset_thirdK hwΔz⟩
  have hu : φ u' = QuotientGroup.mk' O ⟨u, huY⟩ := rfl
  have hv : φ v' = QuotientGroup.mk' O ⟨v, hvY⟩ := rfl
  have hw : φ w' = QuotientGroup.mk' O ⟨w, hwY⟩ := rfl
  rw [← hu, ← hv, ← hw]
  obtain ⟨huD, hvD, hwD, huv, hcuv, hcuw, hcvw⟩ := hQ.tri
  have hcomm : ∀ x y : thirdK D z, Commute (φ x) (φ y) ↔ Commute (x : G) (y : G) := by
    intro x y
    rw [commute_coe_iff_of_subgroup]
    refine ⟨fun h => ?_, fun h => h.map φ⟩
    exact hφ (by rw [map_mul, map_mul]; exact h.eq)
  have hmem : ∀ x : thirdK D z, (x : G) ∈ D → φ x ∈ barOmega D e := fun x hx => by
    rw [barOmega_eq_image]
    exact ⟨Subgroup.inclusion hKY x, hx, rfl⟩
  refine ⟨⟨hmem u' huD, hmem v' hvD, hmem w' hwD,
    fun h => huv (congrArg Subtype.val (hφ h)), (hcomm u' v').mpr hcuv,
    fun h => hcuw ((hcomm u' w').mp h), fun h => hcvw ((hcomm v' w').mp h)⟩, ?_⟩
  obtain ⟨n, hn, hn1, hord, -⟩ := hQ.third
  refine ⟨n, hn, hn1, ?_⟩
  rw [← map_mul φ, ← map_mul φ, orderOf_injective φ hφ, ← Subgroup.orderOf_coe]
  exact hord

theorem exists_conj_of_image_le (hQ : Config D u w v z a K₁ S') {Y : Subgroup G}
    {O : Subgroup Y} [O.Normal] (hKY : thirdK D z ≤ Y) (huY : u ∈ Y)
    {M₀ : Subgroup (Y ⧸ O)} [M₀.Normal]
    (hK₁ : ∀ (k : G) (hk : k ∈ Y), k ∈ K₁ → QuotientGroup.mk' O ⟨k, hk⟩ ∈ M₀)
    {d : G} (hd : d ∈ Delta D z) (hdY : d ∈ Y) :
    ∃ m ∈ M₀, QuotientGroup.mk' O ⟨d, hdY⟩ = m * QuotientGroup.mk' O ⟨u, huY⟩ * m⁻¹ := by
  classical
  obtain ⟨-, -, huΔz, -⟩ := hQ.z_facts
  let C : Subgroup (Y ⧸ O) :=
    Subgroup.centralizer ({QuotientGroup.mk' O ⟨u, huY⟩} : Set (Y ⧸ O))
  let L : Subgroup G := ((M₀ ⊔ C).comap (QuotientGroup.mk' O)).map Y.subtype
  have hmemL : ∀ (k : G) (hk : k ∈ Y), QuotientGroup.mk' O ⟨k, hk⟩ ∈ M₀ ⊔ C → k ∈ L :=
    fun k hk h => ⟨⟨k, hk⟩, h, rfl⟩
  have hK₁z : K₁ ≤ thirdK D z := by rw [hQ.K_eq]; exact le_sup_left
  have hK₁L : K₁ ≤ L := fun k hk =>
    hmemL k (hKY (hK₁z hk)) (Subgroup.mem_sup_left (hK₁ k (hKY (hK₁z hk)) hk))
  have hzz : z ∈ thirdK D z := by
    rw [hQ.K_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  have hzL : Subgroup.zpowers z ≤ L := by
    rw [Subgroup.zpowers_le]
    refine hmemL z (hKY hzz) (Subgroup.mem_sup_right ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzu : u * z = z * u := (mem_Delta_iff.mp huΔz).2
    have hYc : (⟨z, hKY hzz⟩ : Y) * ⟨u, huY⟩ = ⟨u, huY⟩ * ⟨z, hKY hzz⟩ :=
      Subtype.ext hzu.symm
    rw [← map_mul, ← map_mul, hYc]
  have hKL : thirdK D z ≤ L := by rw [hQ.K_eq]; exact sup_le hK₁L hzL
  obtain ⟨n, hn, -, hord, hz⟩ := hQ.third
  have T := thirdK_transitive hQ.setup hQ.local2 hQ.tri hn hord
  rw [← hz] at T
  obtain ⟨k, hk, rfl⟩ := T d hd
  obtain ⟨y, hymem, rfl⟩ := hKL hk
  have hconj : (⟨Y.subtype y * u * (Y.subtype y)⁻¹, hdY⟩ : Y) = y * ⟨u, huY⟩ * y⁻¹ :=
    Subtype.ext rfl
  rw [hconj, map_mul, map_mul, map_inv]
  exact exists_conj_of_mem_sup_centralizer (Subgroup.mem_comap.mp hymem)

theorem false_of_disconnected
    (hQ : Config D u w v z a K₁ S') (hmin : SmallerTwoStar (Nat.card G))
    {e : G} (he2 : orderOf e = 2) (he : e ∉ Subgroup.zpowers z)
    (hzK : thirdK D z ≤ Subgroup.centralizer ({e} : Set G))
    (haK : thirdK D a ≤ Subgroup.centralizer ({e} : Set G))
    (hdisc : Disconnected (barOmega D e)) : False := by
  classical
  set Y : Subgroup G := thirdK D e with hYdef
  set O : Subgroup Y := CFSG.solvableRadical Y with hOdef
  have hYne : Y ≠ ⊤ := thirdK_e_ne_top hQ he2
  have hcard : Nat.card (Y ⧸ O) < Nat.card G := by
    have h1 : Nat.card Y < Nat.card G := by
      simpa using Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hYne)
    have h2 : Nat.card (Y ⧸ O) ≤ Nat.card Y :=
      Nat.card_le_card_of_surjective (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective O)
    omega
  have hradY : ∀ N : Subgroup (Y ⧸ O), N.Normal → Group.IsSolvable N → N = ⊥ :=
    fun N hN hNs => OddTransp.eq_bot_of_quotient_solvableRadical N hN hNs
  have hS : Setup (Y ⧸ O) (barOmega D e) := setup_barOmega hQ he hzK haK
  have hL : LocalSecond (barOmega D e) := localSecond_barOmega hQ he hzK haK
  obtain ⟨-, -, huΔz, hvΔz, hwΔz, -⟩ := hQ.z_facts
  have hKY : thirdK D z ≤ Y := thirdK_le_thirdK_of_le_centralizer hzK
  have huY : u ∈ Y := hKY (Delta_subset_thirdK huΔz)
  have hvY : v ∈ Y := hKY (Delta_subset_thirdK hvΔz)
  have hwY : w ∈ Y := hKY (Delta_subset_thirdK hwΔz)
  obtain ⟨htri, h3⟩ := barOmega_triangle hQ he hzK haK huY hwY hvY
  set ū := QuotientGroup.mk' O ⟨u, huY⟩ with hū
  set wb := QuotientGroup.mk' O ⟨w, hwY⟩ with hwb
  set vb := QuotientGroup.mk' O ⟨v, hvY⟩ with hvb
  have hu2 : ū * ū = 1 := hS.oddT.mul_self_eq_one htri.1
  obtain ⟨H, hHtop, ⟨x₀, hx₀, hx₀H⟩, hHC⟩ := exists_subgroup_of_disconnected hS hdisc
  rcases theoremOne (Y ⧸ O) (barOmega D e) hS.isClass hS.oddT.1 hS.oddT.2 hS.gen hradY
      ⟨H, hHtop, ⟨x₀, hx₀, hx₀H⟩, hHC⟩ with hB | ⟨f, n, hf, hn, ⟨φ⟩⟩ | hAS
  · exact false_of_isThirdKind_of_isBenderGroup hB hu2 (hS.oddT.mul_self_eq_one htri.2.2.1)
      (hS.oddT.mul_self_eq_one htri.2.1) htri.2.2.2.2.1 h3
  · exact false_of_l2Wreath_of_localSecond hS hradY hL hf (by omega) φ
  obtain ⟨M₀, hM₀n, hM₀min, -, hM₀s, hC, hindex, hW1, hcls⟩ := hAS
  have hΩM : ∀ x ∈ barOmega D e, x ∉ M₀ := by
    intro x hx hxM
    have hall : barOmega D e ⊆ M₀ := fun y hy => by
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hx hy)
      exact hM₀n.conj_mem x hxM g
    have htop : M₀ = ⊤ := by
      rw [eq_top_iff, ← hS.gen, Subgroup.closure_le]
      exact hall
    rw [htop, Subgroup.index_top] at hindex
    omega
  have hSQ : Setup ((Y ⧸ O) ⧸ M₀) (QuotientGroup.mk' M₀ '' barOmega D e) := by
    obtain ⟨d₀, hd₀⟩ := hS.isClass
    exact ⟨image_isClass_quotient hd₀ M₀,
      image_isOddTransp_quotient M₀ hS.oddT
        (fun x hx h1 => hΩM x hx ((QuotientGroup.eq_one_iff x).mp h1)),
      image_closure_eq_top_quotient M₀ hS.gen⟩
  have hP2 := index_oddCore_eq_two_of_widthOne hSQ hW1
  obtain ⟨eK⟩ := hQ.K₁_A5
  have hK₁z : K₁ ≤ thirdK D z := by rw [hQ.K_eq]; exact le_sup_left
  have hK₁Y : K₁ ≤ Y := hK₁z.trans hKY
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  have : IsSimpleGroup K₁ := eK.isSimpleGroup
  have hcardK₁ : Nat.card K₁ = 60 := by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  let ψ : K₁ →* ((Y ⧸ O) ⧸ M₀) :=
    (QuotientGroup.mk' M₀).comp ((QuotientGroup.mk' O).comp (Subgroup.inclusion hK₁Y))
  have hψ := eq_one_of_isSimpleGroup_of_odd_index_two (by omega) (by rw [hcardK₁]; decide)
    (oddCore_odd_cfsg (G := (Y ⧸ O) ⧸ M₀)) hP2 ψ
  have hK₁M : ∀ (k : G) (hk : k ∈ Y), k ∈ K₁ → QuotientGroup.mk' O ⟨k, hk⟩ ∈ M₀ := by
    intro k hk hkK
    exact (QuotientGroup.eq_one_iff _).mp (hψ ⟨k, hkK⟩)
  obtain ⟨mw, hmw, hw⟩ := exists_conj_of_image_le hQ hKY huY hK₁M hwΔz hwY
  obtain ⟨mv, hmv, hv⟩ := exists_conj_of_image_le hQ hKY huY hK₁M hvΔz hvY
  have hMK : M₀ ≤ M₀ ⊔ Subgroup.zpowers ū := le_sup_left
  have hmemK : ∀ m ∈ M₀, m * ū * m⁻¹ ∈ M₀ ⊔ Subgroup.zpowers ū := fun m hm =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hm)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers ū))) (Subgroup.mem_sup_left (M₀.inv_mem hm))
  let uΛ : ↥(M₀ ⊔ Subgroup.zpowers ū) := ⟨ū, Subgroup.mem_sup_right (Subgroup.mem_zpowers ū)⟩
  let wΛ : ↥(M₀ ⊔ Subgroup.zpowers ū) := ⟨wb, by rw [hwb, hw]; exact hmemK mw hmw⟩
  let vΛ : ↥(M₀ ⊔ Subgroup.zpowers ū) := ⟨vb, by rw [hvb, hv]; exact hmemK mv hmv⟩
  have huΛ : uΛ ∈ conjSet M₀ ū := ⟨1, M₀.one_mem, by simp [uΛ]⟩
  have hwΛ : wΛ ∈ conjSet M₀ ū := ⟨mw, hmw, hw⟩
  have hvΛ : vΛ ∈ conjSet M₀ ū := ⟨mv, hmv, hv⟩
  have htriΛ : IsTriangle (conjSet M₀ ū) uΛ wΛ vΛ :=
    ⟨huΛ, hvΛ, hwΛ, fun h => htri.2.2.2.1 (congrArg Subtype.val h),
      commute_coe_iff_of_subgroup.mp htri.2.2.2.2.1,
      fun h => htri.2.2.2.2.2.1 (commute_coe_iff_of_subgroup.mpr h),
      fun h => htri.2.2.2.2.2.2 (commute_coe_iff_of_subgroup.mpr h)⟩
  have h3Λ : IsThirdKind uΛ wΛ vΛ := by
    obtain ⟨n, hn, hn1, hord⟩ := h3
    exact ⟨n, hn, hn1, by rw [← Subgroup.orderOf_coe]; exact hord⟩
  have hΛD : ∀ x ∈ conjSet M₀ ū, (x : Y ⧸ O) ∈ barOmega D e := by
    rintro x ⟨m, -, hx⟩
    rw [hx]
    exact hS.normal m ū htri.1
  obtain ⟨hΛcls, hΛodd, hΛgen⟩ := hcls ū htri.1
  have hSΛ : Setup ↥(M₀ ⊔ Subgroup.zpowers ū) (conjSet M₀ ū) := ⟨hΛcls, hΛodd, hΛgen⟩
  have hM1 : M₀ ≠ ⊥ := hM₀min.2.1
  have hradK := solvable_normal_eq_bot_of_le hMK hM₀s hC hM1
  have hLΛ : LocalSecond (conjSet M₀ ū) := localSecond_of_coe_mem hΛD hL
  have hM0 : Asc72.IsMinimalNormal (M₀.subgroupOf (M₀ ⊔ Subgroup.zpowers ū)) :=
    isMinimalNormal_subgroupOf hMK hM₀s
  have hidx : (M₀.subgroupOf (M₀ ⊔ Subgroup.zpowers ū)).index ≤ 2 :=
    relIndex_sup_zpowers_le_two hu2
  have hconn : ¬ Disconnected (conjSet M₀ ū) := by
    intro hdisc'
    obtain ⟨H', hH'top, ⟨x₁, hx₁, hx₁H⟩, hH'C⟩ := exists_subgroup_of_disconnected hSΛ hdisc'
    rcases theoremOne _ _ hSΛ.isClass hSΛ.oddT.1 hSΛ.oddT.2 hSΛ.gen hradK
        ⟨H', hH'top, ⟨x₁, hx₁, hx₁H⟩, hH'C⟩ with hB | ⟨f, n, hf, hn, ⟨φ⟩⟩ | hAS'
    · exact false_of_isThirdKind_of_isBenderGroup hB (hΛodd.mul_self_eq_one huΛ)
        (hΛodd.mul_self_eq_one hwΛ) (hΛodd.mul_self_eq_one hvΛ) htriΛ.2.2.2.2.1 h3Λ
    · exact false_of_l2Wreath_of_localSecond hSΛ hradK hLΛ hf (by omega) φ
    · obtain ⟨M', -, -, huniq, -, -, hidx', -⟩ := hAS'
      rw [← huniq _ hM0] at hidx'
      omega
  have hcardK : Nat.card ↥(M₀ ⊔ Subgroup.zpowers ū) < Nat.card G :=
    (Subgroup.card_le_card_group _).trans_lt hcard
  have hO4 : O4PairData ↥(M₀ ⊔ Subgroup.zpowers ū) (conjSet M₀ ū) := by
    rcases hmin _ _ hcardK hSΛ hconn hradK hLΛ with h3t | h
    · exfalso
      have hdvd := orderOf_mul_dvd_four_of_threeTransposition hΛodd h3t htriΛ
      obtain ⟨n, hn, hn1, hord⟩ := h3Λ
      rw [hord] at hdvd
      have hn2 : n ∣ 2 := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) hdvd
      have := Nat.le_of_dvd (by norm_num) hn2
      obtain ⟨k, hk⟩ := hn
      omega
    · exact h
  obtain ⟨M, -, hMmin, hMlie⟩ := IsO4Minus5Pair.exists_L225 hO4
  have hMeq : M = M₀.subgroupOf (M₀ ⊔ Subgroup.zpowers ū) :=
    eq_subgroupOf_of_isMinimalNormal hMK hM₀s hC hMmin
  subst hMeq
  have hLie : CFSG.Blueprint.LieModel M₀ .PSL 2 5 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMK) hMlie
  have hcomm := quotient_comm_of_L225 M₀ hC hLie
  have hle2 : Nat.card ((Y ⧸ O) ⧸ M₀) ≤ 2 :=
    card_le_two_of_comm_of_class_gen hcomm hSQ.isClass
      (fun c hc => hSQ.oddT.mul_self_eq_one hc) hSQ.gen
  rw [← Subgroup.index_eq_card] at hle2
  omega

end Config

end CFSG.OddTranspositions.QZ

end
