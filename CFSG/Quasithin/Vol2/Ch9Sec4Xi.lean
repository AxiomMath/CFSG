module

public import CFSG.Quasithin.Vol2.Ch11SecOE2A
public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.H13.NQCoreCanonicalResidual

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Xi

theorem mem_normalizer_sup {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have e : ∀ {y : G}, y ∈ Subgroup.normalizer (A : Set G) → y ∈ Subgroup.normalizer (B : Set G) →
      (A ⊔ B).map (MulAut.conj y).toMonoidHom = A ⊔ B := fun hA hB => by
    rw [Subgroup.map_sup, Ch1Sec3.map_conj_eq_of_mem_normalizer hA,
      Ch1Sec3.map_conj_eq_of_mem_normalizer hB]
  exact Ch1Sec3.mem_normalizer_of_map_conj_le (e hA hB).le
    (e (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB)).le

theorem mul_pow_mul_inv_mem {W : Subgroup G} {w o : G} (hw : w ∈ W)
    (ho : o ∈ Subgroup.normalizer (W : Set G)) (n : ℕ) : (w * o) ^ n * (o ^ n)⁻¹ ∈ W := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hon : o ^ n ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ ho n
    have h1 : o ^ n * w * (o ^ n)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hon w).mp hw
    have e : (w * o) ^ (n + 1) * (o ^ (n + 1))⁻¹ =
        ((w * o) ^ n * (o ^ n)⁻¹) * (o ^ n * w * (o ^ n)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact W.mul_mem ih h1

theorem card_le_card_mul_card_centralizer [Finite G] {P Z : Subgroup G} {a : G}
    (h : ∀ b ∈ P, b * a * b⁻¹ * a⁻¹ ∈ Z) :
    Nat.card P ≤ Nat.card Z * Nat.card ↥(P ⊓ Subgroup.centralizer ({a} : Set G)) := by
  classical
  set C : Subgroup ↥P := (P ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf P with hC
  have hCc : Nat.card C = Nat.card ↥(P ⊓ Subgroup.centralizer ({a} : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hmem : ∀ b b' : ↥P, b⁻¹ * b' ∈ C ↔
      (b : G) * a * (b : G)⁻¹ * a⁻¹ = (b' : G) * a * (b' : G)⁻¹ * a⁻¹ := by
    intro b b'
    rw [hC, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨-, hc⟩
      have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
      have hc'' : (b : G)⁻¹ * (b' : G) * a = a * ((b : G)⁻¹ * (b' : G)) := by
        simpa using hc'
      have e1 : (b' : G) = (b : G) * ((b : G)⁻¹ * (b' : G)) := by group
      rw [e1]
      calc (b : G) * a * (b : G)⁻¹ * a⁻¹
          = (b : G) * a * ((b : G)⁻¹ * (b' : G)) * ((b : G)⁻¹ * (b' : G))⁻¹ * (b : G)⁻¹ * a⁻¹ := by
            group
        _ = (b : G) * ((b : G)⁻¹ * (b' : G) * a) * ((b : G)⁻¹ * (b' : G))⁻¹ * (b : G)⁻¹ * a⁻¹ := by
            rw [hc'']; group
        _ = (b : G) * ((b : G)⁻¹ * (b' : G)) * a * ((b : G) * ((b : G)⁻¹ * (b' : G)))⁻¹ * a⁻¹ := by
            group
    · intro he
      refine ⟨(b⁻¹ * b').2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have he' : (b : G) * a * (b : G)⁻¹ = (b' : G) * a * (b' : G)⁻¹ := by
        have := congrArg (· * a) he
        simpa using this
      show (((b⁻¹ * b' : ↥P)) : G) * a = a * (((b⁻¹ * b' : ↥P)) : G)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      symm
      calc a * ((b : G)⁻¹ * (b' : G))
          = (b : G)⁻¹ * ((b : G) * a * (b : G)⁻¹) * (b' : G) := by group
        _ = (b : G)⁻¹ * ((b' : G) * a * (b' : G)⁻¹) * (b' : G) := by rw [he']
        _ = (b : G)⁻¹ * (b' : G) * a := by group
  let f : ↥P ⧸ C → ↥Z := fun x => Quotient.liftOn' x
    (fun b => (⟨(b : G) * a * (b : G)⁻¹ * a⁻¹, h b b.2⟩ : ↥Z)) (by
      intro b b' hbb'
      rw [QuotientGroup.leftRel_apply] at hbb'
      exact Subtype.ext ((hmem b b').mp hbb'))
  have hf : Function.Injective f := by
    intro x y hxy
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective y
    rw [QuotientGroup.eq]
    exact (hmem b b').mpr (congrArg Subtype.val hxy)
  have h1 := Nat.card_le_card_of_injective f hf
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C, hCc]
  exact Nat.mul_le_mul_right _ h1

theorem IsSylowIn.eq_of_le [Finite G] {p : ℕ} [hp : Fact p.Prime] {P H Q : Subgroup G}
    (hP : IsSylowIn p P H) (hQH : Q ≤ H) (hQ : IsPGroup p Q) (hPQ : P ≤ Q) : Q = P := by
  have h := Subgroup.relIndex_mul_relIndex P Q H hPQ hQH
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hQ
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 (hk ▸ Subgroup.relIndex_dvd_card P Q)
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
    exact le_antisymm hj hPQ
  · exfalso
    apply hP.not_dvd_relIndex
    rw [← h, hj]
    exact Dvd.dvd.mul_right (dvd_pow_self p hj0.ne') _

end Xi

open Ch1Sec3

section XiConj

variable [Finite G] {T X : Subgroup G} {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}

theorem IsXi.sq_le_relIndex_frattiniIn (hX : IsXi T X) (hp2 : p ≠ 2) (hpX : p ∣ Nat.card X)
    (hP : IsSylowIn p P X) : p ^ 2 ≤ (frattiniIn P).relIndex P := by
  have hΦP : frattiniIn P ≤ P := Subgroup.map_subtype_le _
  have hPne : P ≠ ⊥ := hX.sylow_ne_bot hp2 hpX hP
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP.isPGroup
  obtain ⟨j, -, hj⟩ :=
    (Nat.dvd_prime_pow hp.out).1 (hk ▸ Subgroup.relIndex_dvd_card (frattiniIn P) P)
  rw [hj]
  rcases Nat.lt_or_ge j 2 with hj2 | hj2
  · exfalso
    interval_cases j
    · rw [pow_zero, Subgroup.relIndex_eq_one] at hj
      exact frattiniIn_ne_of_ne_bot hPne (le_antisymm hΦP hj)
    ·
      obtain ⟨a, haP, haΦ⟩ : ∃ a ∈ P, a ∉ frattiniIn P := by
        by_contra hall
        push Not at hall
        exact frattiniIn_ne_of_ne_bot hPne (le_antisymm hΦP hall)
      set U := Subgroup.zpowers a ⊔ frattiniIn P with hU
      have hUP : U ≤ P := sup_le ((Subgroup.zpowers_le).mpr haP) hΦP
      have hΦU : frattiniIn P ≤ U := le_sup_right
      have hmul := Subgroup.relIndex_mul_relIndex (frattiniIn P) U P hΦU hUP
      rw [hj, pow_one] at hmul
      have hne1 : (frattiniIn P).relIndex U ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle
        exact haΦ (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers a)))
      have hdvd : (frattiniIn P).relIndex U ∣ p := ⟨_, hmul.symm⟩
      have hpU : (frattiniIn P).relIndex U = p :=
        ((Nat.dvd_prime hp.out).1 hdvd).resolve_left hne1
      rw [hpU] at hmul
      have h1 : U.relIndex P = 1 := by
        have := hp.out.pos
        nlinarith
      rw [Subgroup.relIndex_eq_one] at h1
      have hUeq : U = P := le_antisymm hUP h1
      have hz : Subgroup.zpowers a = P :=
        eq_of_sup_frattiniIn_eq ((Subgroup.zpowers_le).mpr haP) hUeq
      have hcard : Nat.card P = orderOf a := by rw [← hz, Nat.card_zpowers]
      have hord : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hX.pow_eq_one hp2 hpX hP haP)
      have h2 := hX.sq_le_card_sylow hp2 hpX hP
      rw [hcard] at h2
      have h3 := Nat.le_of_dvd hp.out.pos hord
      have h4 : p < p ^ 2 := by
        have := hp.out.two_le
        nlinarith
      omega
  · exact Nat.pow_le_pow_right hp.out.pos hj2

theorem IsXi.map_conj_eq {T X D : Subgroup G} (hX : IsXi T X) (g : G)
    (hXg : X ≤ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (hgX : X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (X : Set G))
    (hT : T ≤ Subgroup.normalizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G))
    (hD : X ⊔ X.map (MulAut.conj g).toMonoidHom ≤ D)
    (hDq : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥D) :
    X.map (MulAut.conj g).toMonoidHom = X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X' := X.map (MulAut.conj g).toMonoidHom with hX'def
  obtain ⟨hX1, hTX, -, q, hq, hq2, hpow, hidx, hirr⟩ := id hX
  have : Fact q.Prime := ⟨hq⟩
  have hqX : q ∣ Nat.card X := by
    rw [card_eq_card_pCoreOf_mul_relIndex]
    rcases hidx with h | ⟨h, -⟩ <;> rw [h] <;>
      exact Dvd.dvd.mul_left (dvd_pow_self q (by norm_num)) _
  have hcard : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨P, hP, -⟩ := exists_isSylowIn_ge q (bot_le : (⊥ : Subgroup G) ≤ X) IsPGroup.of_bot
  set Φ := ⁅X, X⁆ ⊔ pCoreOf 2 X with hΦ
  have hXX : ⁅X, X⁆ ≤ X := commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  have hTY : T ≤ Subgroup.normalizer (((X ⊓ X') ⊔ Φ : Subgroup G) : Set G) := fun t ht =>
    Xi.mem_normalizer_sup (Subgroup.inf_normalizer_le_normalizer_inf ⟨hTX ht, hT ht⟩)
      (Xi.mem_normalizer_sup (commutator_le_normalizer (hTX ht) (hTX ht))
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hTX ht)))
  have hPP : ⁅P, P⁆ ≤ P := commutator_le_left_of_le_normalizer Subgroup.le_normalizer
  rcases hirr ((X ⊓ X') ⊔ Φ) le_sup_right
    (sup_le inf_le_left (sup_le hXX (CFSG.LieType.BorelTits.pCoreOf_le 2 X))) hTY with hY | hY
  ·
    exfalso
    have hB : X ⊓ X' ≤ Φ := le_sup_left.trans hY.le
    have hPX' : P ≤ Subgroup.normalizer (X' : Set G) := hP.le.trans hXg
    obtain ⟨S, hS, hPS⟩ := exists_isSylowIn_ge q (le_sup_left : P ≤ P ⊔ X') hP.isPGroup
    set P' := S ⊓ X' with hP'def
    have hP'syl : IsSylowIn q P' X' := hS.inf_normal le_sup_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
        (sup_le hPX' Subgroup.le_normalizer))
    have hPP' : P ≤ Subgroup.normalizer (P' : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hPS hx), hPX' hx⟩
    have hSX : S ⊓ X = P :=
      Xi.IsSylowIn.eq_of_le hP inf_le_right (hS.isPGroup.to_le inf_le_left) (le_inf hPS hP.le)
    have hP'X : P' ⊓ X ≤ P := hSX ▸ inf_le_inf_right X inf_le_left
    have hΦP : frattiniIn P = P ⊓ Φ := (hX.frattiniIn_eq hq2 hqX hP).2
    have hZΦ : P ⊓ P' ≤ frattiniIn P := by
      rw [hΦP]
      exact le_inf inf_le_left ((inf_le_inf hP.le inf_le_right).trans hB)
    have hcomm : ∀ a ∈ P, ∀ b ∈ P', b * a * b⁻¹ * a⁻¹ ∈ P ⊓ P' := by
      intro a ha b hb
      have h1 : b * a * b⁻¹ * a⁻¹ ∈ P' := by
        have : a * b⁻¹ * a⁻¹ ∈ P' :=
          (Subgroup.mem_normalizer_iff.mp (hPP' ha) b⁻¹).mp (P'.inv_mem hb)
        have e : b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) := by group
        rw [e]
        exact P'.mul_mem hb this
      have h2 : b * a * b⁻¹ * a⁻¹ ∈ X := by
        have hbX : b ∈ Subgroup.normalizer (X : Set G) := hgX (Subgroup.mem_inf.mp hb).2
        have : b * a * b⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hbX a).mp (hP.le ha)
        exact X.mul_mem this (X.inv_mem (hP.le ha))
      exact ⟨hP'X ⟨h1, h2⟩, h1⟩
    have hP'q : ∀ y ∈ P', y ^ q = 1 := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hy).2
      have h1 : ((MulAut.conj g).toMonoidHom x) ^ q ∈
          (pCoreOf 2 X).map (MulAut.conj g).toMonoidHom := by
        rw [← map_pow]
        exact Subgroup.mem_map_of_mem _ (hpow x hx)
      have h2 : ((MulAut.conj g).toMonoidHom x) ^ q ∈ P' := P'.pow_mem hy q
      have hdis := IsPGroup.disjoint_of_ne q 2 hq2 P'
        ((pCoreOf 2 X).map (MulAut.conj g).toMonoidHom) hP'syl.isPGroup
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).map _)
      exact (Subgroup.disjoint_def.mp hdis) h2 h1
    have hcardP' : Nat.card P' = Nat.card P := by
      rw [hP'syl.card_eq, hP.card_eq, hcard]
    have hΦle : frattiniIn P ≤ P := Subgroup.map_subtype_le _
    obtain ⟨a, haP, haΦ⟩ : ∃ a ∈ P, a ∉ frattiniIn P := by
      by_contra hall
      push Not at hall
      exact frattiniIn_ne_of_ne_bot (hX.sylow_ne_bot hq2 hqX hP) (le_antisymm hΦle hall)
    have haq : a ^ q = 1 := hX.pow_eq_one hq2 hqX hP haP
    have ha1 : a ≠ 1 := fun h => haΦ (h ▸ Subgroup.one_mem _)
    have hpowΦ : ∀ n : ℕ, a ^ n ∈ frattiniIn P → a ^ n = 1 := by
      intro n hn
      by_contra hne
      have hord : orderOf a = q := orderOf_eq_prime haq ha1
      have hndvd : ¬ q ∣ n := fun ⟨m, hm⟩ => hne (by rw [hm, pow_mul, haq, one_pow])
      have hcop : n.Coprime (orderOf a) := by
        rw [hord]
        exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hndvd)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      exact haΦ (hm ▸ Subgroup.pow_mem _ hn m)
    have hpowP' : ∀ n : ℕ, a ^ n ∈ P' → a ^ n = 1 := fun n hn =>
      hpowΦ n (hZΦ ⟨P.pow_mem haP n, hn⟩)
    set C := P' ⊓ Subgroup.centralizer ({a} : Set G) with hCdef
    have hC1 := Xi.card_le_card_mul_card_centralizer (P := P') (Z := P ⊓ P') (a := a)
      (fun b hb => hcomm a haP b hb)
    have hC2 : Nat.card (frattiniIn P) * q ^ 2 ≤ Nat.card P := by
      have h1 := Subgroup.relIndex_mul_card (frattiniIn P) P
      rw [inf_eq_left.mpr hΦle] at h1
      rw [← h1]
      calc Nat.card (frattiniIn P) * q ^ 2
          ≤ Nat.card (frattiniIn P) * (frattiniIn P).relIndex P :=
            Nat.mul_le_mul_left _ (hX.sq_le_relIndex_frattiniIn hq2 hqX hP)
        _ = _ := mul_comm _ _
    have hC3 : Nat.card ↥(P ⊓ P') ≤ Nat.card (frattiniIn P) := Subgroup.card_le_of_le hZΦ
    have hCq : q ^ 2 ≤ Nat.card C := by
      have hpos : 0 < Nat.card (frattiniIn P) := Nat.card_pos
      have : Nat.card (frattiniIn P) * q ^ 2 ≤ Nat.card (frattiniIn P) * Nat.card C :=
        calc Nat.card (frattiniIn P) * q ^ 2 ≤ Nat.card P := hC2
          _ = Nat.card P' := hcardP'.symm
          _ ≤ Nat.card ↥(P ⊓ P') * Nat.card C := hC1
          _ ≤ Nat.card (frattiniIn P) * Nat.card C := Nat.mul_le_mul_right _ hC3
      exact Nat.le_of_mul_le_mul_left this hpos
    have hCp : IsPGroup q C := hP'syl.isPGroup.to_le inf_le_left
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hCp
    have hdvd : q ^ 2 ∣ Nat.card C := by
      rw [hm]
      apply pow_dvd_pow
      by_contra h
      push Not at h
      have : Nat.card C < q ^ 2 := by rw [hm]; exact Nat.pow_lt_pow_right hq.one_lt h
      omega
    obtain ⟨B, hBcard, -, hBC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hq
      (by rw [Subgroup.card_bot]; exact one_dvd _) hdvd (bot_le : (⊥ : Subgroup G) ≤ C)
    have hBcomm : IsMulCommutative B := IsPGroup.isMulCommutative_of_card_eq_prime_sq hBcard
    have hBne : B ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hBcard
      have : 1 < q ^ 2 := Nat.one_lt_pow two_ne_zero hq.one_lt
      omega
    obtain ⟨⟨y, hyB⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hyP' : y ∈ P' := (Subgroup.mem_inf.mp (hBC hyB)).1
    obtain ⟨z, hzB, hzy⟩ : ∃ z ∈ B, z ∉ Subgroup.zpowers y := by
      by_contra hall
      push Not at hall
      have h1 : Nat.card B ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hall
      rw [Nat.card_zpowers, hBcard] at h1
      have h2 : orderOf y ∣ q := orderOf_dvd_of_pow_eq_one (hP'q y hyP')
      have h3 := Nat.le_of_dvd hq.pos h2
      have h4 : q < q ^ 2 := by have := hq.two_le; nlinarith
      omega
    have hzP' : z ∈ P' := (Subgroup.mem_inf.mp (hBC hzB)).1
    have hay : a * y = y * a :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hBC hyB)).2).symm
    have haz : a * z = z * a :=
      (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hBC hzB)).2).symm
    have hyz : y * z = z * y := by
      have := hBcomm.is_comm.comm ⟨y, hyB⟩ ⟨z, hzB⟩
      exact congrArg Subtype.val this
    have haD : a ∈ D := hD (Subgroup.mem_sup_left (hP.le haP))
    have hyD : y ∈ D := hD (Subgroup.mem_sup_right (Subgroup.mem_inf.mp hyP').2)
    have hzD : z ∈ D := hD (Subgroup.mem_sup_right (Subgroup.mem_inf.mp hzP').2)
    have h3 := CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (G := ↥D) (p := q)
      (x := ⟨a, haD⟩) (y := ⟨y, hyD⟩) (z := ⟨z, hzD⟩)
      (Subtype.ext (by simpa using haq)) (Subtype.ext (by simpa using hP'q y hyP'))
      (Subtype.ext (by simpa using hP'q z hzP')) (Subtype.ext hay) (Subtype.ext haz)
      (Subtype.ext hyz) (fun h => ha1 (congrArg Subtype.val h))
      (fun n h => by
        have h' : a ^ n = y := by simpa using congrArg Subtype.val h
        exact hy1' (h' ▸ hpowP' n (h' ▸ hyP')))
      (fun n k h => by
        have h' : a ^ n * y ^ k = z := by simpa using congrArg Subtype.val h
        have h1 : a ^ n = z * (y ^ k)⁻¹ := by rw [← h']; group
        have h2 : a ^ n = 1 := hpowP' n (h1 ▸ P'.mul_mem hzP' (P'.inv_mem (P'.pow_mem hyP' k)))
        rw [h2, one_mul] at h'
        exact hzy (h' ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers y) k))
    have h2 : CFSG.Open.pRank q (⊤ : Subgroup ↥D) ≤ 2 := hDq q hq hq2
    omega
  ·
    set N := (X ⊓ X') ⊔ pCoreOf 2 X with hN
    have hXN : X ≤ Subgroup.normalizer (N : Set G) := fun x hx =>
      Xi.mem_normalizer_sup (Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hXg hx⟩)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hx)
    have hPPN : ⁅P, P⁆ ≤ Subgroup.normalizer (N : Set G) := (hPP.trans hP.le).trans hXN
    have hXle : X ≤ N ⊔ ⁅P, P⁆ := by
      calc X = (X ⊓ X') ⊔ Φ := hY.symm
        _ ≤ N ⊔ ⁅P, P⁆ := sup_le (le_sup_left.trans le_sup_left)
            (sup_le ((hX.commutator_le hq2 hqX hP).trans
              (sup_le (le_sup_right.trans le_sup_left) le_sup_right))
              (le_sup_right.trans le_sup_left))
    have hP1 : P ≤ (P ⊓ N) ⊔ ⁅P, P⁆ := by
      intro x hx
      obtain ⟨n, hn, c, hc, rfl⟩ := (mem_sup_iff_of_le_normalizer hPPN).mp (hXle (hP.le hx))
      have hnP : n ∈ P := by
        have := P.mul_mem hx (P.inv_mem (hPP hc))
        simpa using this
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hnP, hn⟩) (Subgroup.mem_sup_right hc)
    have hP2 : (P ⊓ N) ⊔ frattiniIn P = P := by
      rw [(hX.frattiniIn_eq hq2 hqX hP).1]
      exact le_antisymm (sup_le inf_le_left hPP) hP1
    have hPN : P ≤ N := by
      have h := eq_of_sup_frattiniIn_eq inf_le_left hP2
      rw [← h]
      exact inf_le_right
    have hXN' : X ≤ N := by
      rw [← hX.pCoreOf_sup_eq hq2 hqX hP]
      exact sup_le le_sup_right hPN
    have hO : pCoreOf 2 X ≤ Subgroup.normalizer ((X ⊓ X' : Subgroup G) : Set G) := fun o ho =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 X ho),
          hXg (CFSG.LieType.BorelTits.pCoreOf_le 2 X ho)⟩
    have hXX' : X ≤ X ⊓ X' := by
      calc X = oTwoUpper X := hX1
        _ ≤ X ⊓ X' := oTwoUpper_le_of_pow_mem fun x hx => by
            obtain ⟨w, hw, o, ho, rfl⟩ := (mem_sup_iff_of_le_normalizer hO).mp (hXN' hx)
            obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨o, ho⟩
            have hk' : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
            refine ⟨k, ?_⟩
            have := Xi.mul_pow_mul_inv_mem hw (hO ho) (2 ^ k)
            rwa [hk', inv_one, mul_one] at this
    exact (Subgroup.eq_of_le_of_card_ge (hXX'.trans inf_le_right) hcard.le).symm

end XiConj

section Local

variable [Finite G]

theorem Xi.isSolvable_comap {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hker : Group.IsSolvable f.ker) {Y : Subgroup B} (hY : Group.IsSolvable Y) :
    Group.IsSolvable (Y.comap f) := by
  let g : ↥(Y.comap f) →* ↥Y := (f.comp (Y.comap f).subtype).codRestrict Y fun x => x.2
  have hgk : Group.IsSolvable g.ker := by
    let i : ↥g.ker →* ↥f.ker :=
      { toFun := fun x => ⟨((x : ↥(Y.comap f)) : A), by
          have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
          exact MonoidHom.mem_ker.mpr this⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hi : Function.Injective i := fun x y h => by
      have := congrArg (fun z : ↥f.ker => (z : A)) h
      exact Subtype.ext (Subtype.ext this)
    exact Group.isSolvable_of_isSolvable_injective hi
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [Subgroup.range_subtype])

theorem exists_isXi_of_cComp {Y T L : Subgroup G}
    (hY : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥Y) (hTY : QuasithinUnique.IsSylowTwoOf T Y)
    (hL : L ∈ cComp Y) (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hO : pCoreOf 2 Y ≠ ⊥)
    (hLq : ¬ CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    ∃ X : Subgroup G, IsXi T X ∧ X ≤ L ∧
      Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (X : Set G) ∧ Group.IsSolvable ↥X ∧
      ∀ K : Subgroup G, K ≤ L → ⁅K, X⁆ ≤ pCoreOf 2 X → Group.IsSolvable ↥K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLY : L ≤ Y := le_of_mem_cComp hL
  have hTY' : T ≤ Y := hTY.1
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hTY'.trans hYL
  have hSQT : CFSG.IsStronglyQuasithin ↥L := by
    rw [CFSG.SectionRank.isStronglyQuasithin_iff]
    intro q hq hq2
    exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt (Subgroup.inclusion hLY)
      (Subgroup.inclusion_injective hLY)).trans (hY q hq hq2)
  have hLself : L ∈ cComp L := cComp_mem_of_le hL le_rfl hLY
  have hLtop : CFSG.IsCComponent (⊤ : Subgroup ↥L) := by
    have h3 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp hLself)
    rwa [Subgroup.subgroupOf_self] at h3
  obtain ⟨p, hp, hp5, D₀, -, hD₀, hshape₀, -⟩ :=
    H13.NQBlock.nq_characteristic_radical_odd_residual_witness hSQT hLtop hLq
  have : Fact p.Prime := ⟨hp⟩
  have hCp : CFSG.pCore p (↥L ⧸ CFSG.pCore 2 ↥L) ≠ ⊥ := by
    intro hbot
    have hD₀b : D₀ = ⊥ := le_bot_iff.mp (hbot ▸ hD₀)
    have hcard : Nat.card D₀ = 1 := by rw [hD₀b, Subgroup.card_bot]
    rcases hshape₀ with ⟨-, h2⟩ | ⟨-, h3, -⟩
    · rw [hcard] at h2
      have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    · rw [hcard] at h3
      have : 1 < p ^ 3 := Nat.one_lt_pow three_ne_zero hp.one_lt
      omega
  have hpF' := H13.NQCore.mem_primeFactors_fitting hCp
  set Q : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := CFSG.pCore p (↥L ⧸ CFSG.pCore 2 ↥L)
  set B : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.closure {a | a ∈ Q ∧ a ^ p = 1}
  set E : Subgroup ↥L := B.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  set Xq : Subgroup ↥L := Subgroup.closure {e | e ∈ E ∧ Odd (orderOf e)}
  obtain ⟨-, hXc, hW', hsolv', -, -, ⟨-, φ, -, -, -, -, -⟩, hshape, hker⟩ :=
    H13.NQBlock.canonical_prime_witness hSQT hLtop hLq hpF' Q B E Xq rfl rfl rfl rfl
  have hXeq : Vol2.Ch11.xiP L p = Xq.map L.subtype := Vol2.Ch11.OE2.xiP_eq_map L p
  set X : Subgroup G := Xq.map L.subtype with hXdef
  have hXL : X ≤ L := Subgroup.map_subtype_le _
  have hX1 : X = oTwoUpper X := by
    rw [← hXeq, Vol2.Ch11.xiP]
    exact (le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun x hx =>
      mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)).symm
  have hXsub : X.subgroupOf L = Xq :=
    Subgroup.comap_map_eq_self_of_injective L.subtype_injective Xq
  have hXchar : (X.subgroupOf L).Characteristic := hXsub ▸ hXc
  have hNX : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (X : Set G) :=
    H13.NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := hTL.trans hNX
  have hO2 : pCoreOf 2 (X ⊔ T) ≠ ⊥ := by
    have h1 : pCoreOf 2 Y ≤ T := pCoreOf_le_of_isSylowIn hTY
    have h2 : pCoreOf 2 Y ≤ pCoreOf 2 (X ⊔ T) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h1.trans le_sup_right)
        ((sup_le (hXL.trans hLY) hTY').trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
    exact fun h => hO (le_bot_iff.mp (h ▸ h2))
  have hirr : ∀ M : Subgroup ((↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq)),
      (∀ s : ↥L, (s : G) ∈ T → ∀ w ∈ M, H13.NQBlock.residualAction Xq s w ∈ M) →
        M = ⊥ ∨ M = ⊤ := by
    intro M hM
    have hTLs : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L := A4.isSylowTwoOf_inf_normal hTY hLY hYL
    have hTLp : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
      hTLs.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLs.1).symm
    have hTLi : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := hTLs.2.2
    set S' : Sylow 2 ↥L := hTLp.toSylow hTLi
    have hS'c : (S' : Subgroup ↥L) = (T ⊓ L).subgroupOf L := IsPGroup.toSylow_coe hTLp hTLi
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hLself)
    have hW := hW'.card_W
    have : IsMulCommutative ((↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq)) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq hW
    have hWp : ∀ w : (↥Xq ⧸ CFSG.pCore 2 ↥Xq) ⧸ frattini (↥Xq ⧸ CFSG.pCore 2 ↥Xq),
        w ^ p = 1 := by
      intro w
      obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
      rw [← QuotientGroup.mk_pow, ← hW'.exponent, Monoid.pow_exponent_eq_one,
        QuotientGroup.mk_one]
    refine SteinbergCD.perfect_sylow_two_irreducible_of_card_eq_sq hp5 hWp hW
      (H13.NQBlock.residualAction Xq) hW'.nontrivial S' M ?_
    intro s hs w hw
    rw [hS'c] at hs
    exact hM s (Subgroup.mem_subgroupOf.mp hs).1 w hw
  have hXi : IsXi T X := by
    refine ⟨hX1, hTX, hO2, p, hp, by omega,
      fun x hx => Vol2.Ch11.OE2.pow_mem_pCoreOf hW'.exponent hx, ?_,
      fun Y' hY1 hY2 hYT =>
        Vol2.Ch11.OE2.eq_or_eq_of_residual Xq hW'.isPGroup hW'.exponent hirr hY1 hY2 hYT⟩
    rw [Vol2.Ch11.OE2.relIndex_map]
    have hcard : Nat.card (↥Xq ⧸ CFSG.pCore 2 ↥Xq) = Nat.card B := Nat.card_congr φ.toEquiv
    rcases hshape with ⟨-, -, -, hB2⟩ | ⟨hQB, hQnc, hQ3, -⟩
    · exact Or.inl (hcard.trans hB2)
    · refine Or.inr ⟨by rw [hcard, ← hQB]; exact hQ3,
        Vol2.Ch11.OE2.not_commutator_le fun hc => hQnc ?_⟩
      have hB : IsMulCommutative ↥B := ⟨⟨fun a b => by
        have h := hc.is_comm.comm (φ.symm a) (φ.symm b)
        apply φ.symm.injective
        rw [map_mul, map_mul, h]⟩⟩
      rw [hQB]
      exact hB
  have := hsolv'
  have hsolX : Group.IsSolvable ↥X :=
    Group.isSolvable_of_surjective
      (f := (Xq.equivMapOfInjective L.subtype L.subtype_injective).toMonoidHom)
      (Xq.equivMapOfInjective L.subtype L.subtype_injective).surjective
  refine ⟨X, hXi, hXL, hNX, hsolX, fun K hKL hKX => ?_⟩
  set R := (CFSG.fittingSubgroup (↥L ⧸ CFSG.pCore 2 ↥L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
    with hR
  have hRs : Group.IsSolvable ↥R := by
    refine Xi.isSolvable_comap _ ?_ inferInstance
    rw [QuotientGroup.ker_mk']
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).isNilpotent
    infer_instance
  have hKR : K.subgroupOf L ≤ R := by
    intro k hk
    rw [← hker, MonoidHom.mem_ker]
    refine MulEquiv.ext fun w => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    rw [H13.NQBlock.residualAction_mk]
    show (((MulAut.conjNormal k x : Xq) : Xq ⧸ CFSG.pCore 2 Xq) :
        (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq)) =
      (((x : Xq ⧸ CFSG.pCore 2 Xq)) : (Xq ⧸ CFSG.pCore 2 Xq) ⧸ frattini (Xq ⧸ CFSG.pCore 2 Xq))
    congr 1
    rw [QuotientGroup.eq]
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hxX : (((x⁻¹ : Xq) : ↥L) : G) ∈ X := Subgroup.mem_map_of_mem L.subtype x⁻¹.2
    have hc := hKX (Subgroup.commutator_mem_commutator hkK hxX)
    rw [Vol2.Ch11.OE2.pCoreOf_map] at hc
    obtain ⟨y, ⟨y', hy', rfl⟩, hyc⟩ := Subgroup.mem_map.mp hc
    have hy'eq : y' = (MulAut.conjNormal k x)⁻¹ * x := by
      apply Subtype.ext
      apply Subtype.ext
      have h1 : (((y' : Xq) : ↥L) : G) = ⁅(k : G), (((x⁻¹ : Xq) : ↥L) : G)⁆ := hyc
      rw [h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply,
        commutatorElement_def]
      group
    rw [hy'eq] at hy'
    exact hy'
  have hKs : Group.IsSolvable ↥(K.subgroupOf L) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKR)
      (Subgroup.inclusion_injective hKR)
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.subgroupOfEquivOfLe hKL).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKL).symm.injective

end Local

end CFSG.Quasithin
