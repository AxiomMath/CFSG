module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFStmt
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313B
public import CFSG.Quasithin.Background.C124L2MP
public import CFSG.Quasithin.Background.E2TwoProofY

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat)

variable {G : Type} [Group G] [Finite G]

theorem inf_pCoreOf_le {H₀ K : Subgroup G} (hK : K ≤ H₀) :
    K ⊓ pCoreOf 2 H₀ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun l hl => ?_)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_inf_right
  exact ChiefCount.mem_normalizer_inf (Subgroup.le_normalizer hl)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hK hl))

theorem exists_outer_modO2 {H₀ K T : Subgroup G} (hTH₀ : T ≤ H₀) (hKH₀ : K ≤ H₀)
    (hout : ¬ InducesInnerOn (T ⊓ Subgroup.normalizer (K : Set G)) K) :
    ∃ s ∈ modO2Image H₀ T ⊓ Subgroup.normalizer ((modO2Image H₀ K : Subgroup _) : Set _),
      ∀ a ∈ modO2Image H₀ K, ∃ x ∈ modO2Image H₀ K, s * x * s⁻¹ ≠ a * x * a⁻¹ := by
  unfold InducesInnerOn at hout
  push Not at hout
  obtain ⟨t, ⟨htT, htN⟩, ht⟩ := hout
  have htH : t ∈ H₀ := hTH₀ htT
  refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨t, htH⟩, ⟨Lem3313B.mk_mem_img _ htT, ?_⟩, ?_⟩
  · have h1 : Subgroup.zpowers t ≤ Subgroup.normalizer (K : Set G) :=
      (Subgroup.zpowers_le).mpr htN
    exact Lem3313B.img_le_normalizer h1
      (Lem3313B.mk_mem_img ⟨t, htH⟩ (Subgroup.mem_zpowers t))
  · rintro a ⟨x₀, hx₀, rfl⟩
    obtain ⟨x, hxK, hx⟩ := ht (x₀ : G) hx₀
    refine ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨x, hKH₀ hxK⟩, Lem3313B.mk_mem_img _ hxK,
      fun heq => hx ?_⟩
    set w : G := t * x * t⁻¹ * (↑x₀ * x * (↑x₀)⁻¹)⁻¹ with hw
    have hwK : w ∈ K := by
      have htx : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htN x).mp hxK
      exact K.mul_mem htx (K.inv_mem (K.mul_mem (K.mul_mem hx₀ hxK) (K.inv_mem hx₀)))
    have hwH : w ∈ H₀ := hKH₀ hwK
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨w, hwH⟩ = 1 := by
      have e : (⟨w, hwH⟩ : ↥H₀) = (⟨t, htH⟩ * ⟨x, hKH₀ hxK⟩ * ⟨t, htH⟩⁻¹) *
          (x₀ * ⟨x, hKH₀ hxK⟩ * x₀⁻¹)⁻¹ := rfl
      rw [e]
      simp only [map_mul, map_inv]
      rw [heq, mul_inv_cancel]
    have h2 : (⟨w, hwH⟩ : ↥H₀) ∈ CFSG.pCore 2 ↥H₀ := (QuotientGroup.eq_one_iff _).mp h1
    have h3 : w ∈ pCoreOf 2 H₀ := (Lem3328.mem_pCore_iff (⟨w, hwH⟩ : ↥H₀)).mp h2
    exact inf_pCoreOf_le hKH₀ ⟨hwK, h3⟩

theorem conj_mem_normalizer_map {Q : Type} [Group Q] {A : Subgroup Q} {s : Q} (g : Q)
    (hs : s ∈ Subgroup.normalizer (A : Set Q)) :
    g * s * g⁻¹ ∈
      Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨s * x * s⁻¹, (Subgroup.mem_normalizer_iff.mp hs x).mp hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨x, hx, hxe⟩
    refine ⟨s⁻¹ * x * s, (Subgroup.mem_normalizer_iff''.mp hs x).mp hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe ⊢
    have : z = (g * s * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * s * g⁻¹) := by
      rw [hxe]
      group
    rw [this]
    group

theorem outer_conj {Q : Type} [Group Q] {A : Subgroup Q} {s : Q} (g : Q)
    (hs : ∀ a ∈ A, ∃ x ∈ A, s * x * s⁻¹ ≠ a * x * a⁻¹) :
    ∀ a ∈ A.map (MulAut.conj g).toMonoidHom, ∃ x ∈ A.map (MulAut.conj g).toMonoidHom,
      (g * s * g⁻¹) * x * (g * s * g⁻¹)⁻¹ ≠ a * x * a⁻¹ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨x, hx, hne⟩ := hs a ha
  refine ⟨g * x * g⁻¹, ⟨x, hx, rfl⟩, fun heq => hne ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at heq ⊢
  have h1 : g * (s * x * s⁻¹) * g⁻¹ = g * (a * x * a⁻¹) * g⁻¹ := by
    calc g * (s * x * s⁻¹) * g⁻¹ = g * s * g⁻¹ * (g * x * g⁻¹) * (g * s * g⁻¹)⁻¹ := by group
      _ = g * a * g⁻¹ * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ := heq
      _ = g * (a * x * a⁻¹) * g⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h1)

theorem normalizer_sup_of_le_normalizer {Q : Type} [Group Q] {A S B : Subgroup Q}
    (hBA : B ≤ Subgroup.normalizer (A : Set Q)) (hBS : B ≤ Subgroup.normalizer (S : Set Q)) :
    B ≤ Subgroup.normalizer ((A ⊔ S : Subgroup Q) : Set Q) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBA hb),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hBS hb)]

theorem not_two_dvd_card_of_odd {Q : Type} [Group Q] [Finite Q] (B : Subgroup Q)
    (hBodd : ∀ x ∈ B, Odd (orderOf x)) : ¬ 2 ∣ Nat.card B := by
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 2 h2
  have hodd := hBodd (x : Q) x.2
  rw [Subgroup.orderOf_coe, hx] at hodd
  obtain ⟨m, hm⟩ := hodd
  omega

theorem isSylowTwoOf_sup_sup_of_odd {Q : Type} [Group Q] [Finite Q] {A S B : Subgroup Q}
    (hSN : S ≤ Subgroup.normalizer (A : Set Q)) (hS2 : IsPGroup 2 S)
    (hSA : IsSylowTwoOf (S ⊓ A) A)
    (hBAS : B ≤ Subgroup.normalizer ((A ⊔ S : Subgroup Q) : Set Q))
    (hB2 : ¬ 2 ∣ Nat.card B) : IsSylowTwoOf S (A ⊔ S ⊔ B) := by
  have hSAS : S ≤ A ⊔ S := le_sup_right
  have hAS_X : A ⊔ S ≤ A ⊔ S ⊔ B := le_sup_left
  have hS_X : S ≤ A ⊔ S ⊔ B := le_trans hSAS hAS_X
  have hSylAS : IsSylowTwoOf S (A ⊔ S) :=
    CFSG.Quasithin.C124.L2.isSylowTwoOf_sup_of_normalizing hSN hS2 hSA
  have hAS_rel : ¬ 2 ∣ (A ⊔ S).relIndex (A ⊔ S ⊔ B) := by
    have hcard := CFSG.Quasithin.C126.A5.card_sup_mul_card_inf_of_le_normalizer hBAS
    have h1 := Subgroup.relIndex_mul_card (A ⊔ S) (A ⊔ S ⊔ B)
    rw [inf_eq_left.2 hAS_X] at h1
    have hpos : 0 < Nat.card ↥(A ⊔ S) := Nat.card_pos
    have key : (A ⊔ S).relIndex (A ⊔ S ⊔ B) * Nat.card ↥((A ⊔ S) ⊓ B) = Nat.card B := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      calc Nat.card ↥(A ⊔ S) * ((A ⊔ S).relIndex (A ⊔ S ⊔ B) * Nat.card ↥((A ⊔ S) ⊓ B))
          = ((A ⊔ S).relIndex (A ⊔ S ⊔ B) * Nat.card ↥(A ⊔ S)) * Nat.card ↥((A ⊔ S) ⊓ B) := by
            ring
        _ = Nat.card ↥(A ⊔ S ⊔ B) * Nat.card ↥((A ⊔ S) ⊓ B) := by rw [h1]
        _ = Nat.card ↥(A ⊔ S) * Nat.card B := hcard
    intro h2
    apply hB2
    rw [← key]
    exact Dvd.dvd.mul_right h2 _
  have hdiv : S.relIndex (A ⊔ S) * (A ⊔ S).relIndex (A ⊔ S ⊔ B) = S.relIndex (A ⊔ S ⊔ B) :=
    Subgroup.relIndex_mul_relIndex S (A ⊔ S) (A ⊔ S ⊔ B) hSAS hAS_X
  refine ⟨hS_X, hS2, ?_⟩
  show ¬ 2 ∣ S.relIndex (A ⊔ S ⊔ B)
  rw [← hdiv]
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hSylAS.2.2 h
  · exact hAS_rel h

theorem centralizes_of_outer {Q : Type} [Group Q] [Finite Q] (hFact : FactAutL2pOuter) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (h8 : p % 8 = 3 ∨ p % 8 = 5) {A S B : Subgroup Q}
    (hA : F6.IsL2 p 1 ↥A) (hSN : S ≤ Subgroup.normalizer (A : Set Q)) (hS2 : IsPGroup 2 S)
    (hSA : IsSylowTwoOf (S ⊓ A) A)
    (hout : ∃ s ∈ S, ∀ a ∈ A, ∃ x ∈ A, s * x * s⁻¹ ≠ a * x * a⁻¹)
    (hBA : B ≤ Subgroup.normalizer (A : Set Q)) (hBS : B ≤ Subgroup.normalizer (S : Set Q))
    (hBodd : ∀ x ∈ B, Odd (orderOf x)) :
    ∀ d ∈ B, ∀ a ∈ A, d * a * d⁻¹ = a := by
  have hAN : A ≤ Subgroup.normalizer (A : Set Q) := Subgroup.le_normalizer
  have hXN : A ⊔ S ⊔ B ≤ Subgroup.normalizer (A : Set Q) := sup_le (sup_le hAN hSN) hBA
  have hSylX : IsSylowTwoOf S (A ⊔ S ⊔ B) :=
    isSylowTwoOf_sup_sup_of_odd hSN hS2 hSA (normalizer_sup_of_le_normalizer hBA hBS)
      (not_two_dvd_card_of_odd B hBodd)
  have hA_X : A ≤ A ⊔ S ⊔ B := le_trans le_sup_left le_sup_left
  have hS_X : S ≤ A ⊔ S ⊔ B := le_trans le_sup_right le_sup_left
  have hB_X : B ≤ A ⊔ S ⊔ B := le_sup_right
  set ψ : ↥(A ⊔ S ⊔ B) →* MulAut ↥A :=
    (Subgroup.normalizerMonoidHom A).comp (Subgroup.inclusion hXN)
  have hψ : ∀ (x : ↥(A ⊔ S ⊔ B)) (a : ↥A),
      ((ψ x a : ↥A) : Q) = (x : Q) * (a : Q) * (x : Q)⁻¹ :=
    fun x a => rfl
  set Saut : Subgroup (MulAut ↥A) := (S.subgroupOf (A ⊔ S ⊔ B)).map ψ
  have hSyl : IsSylowTwoOf Saut ψ.range :=
    CFSG.Quasithin.E2P.isSylowTwoOf_map_hom hSylX ψ
  have hInn : (MulAut.conj : ↥A →* MulAut ↥A).range ≤ ψ.range := by
    rintro g ⟨a, rfl⟩
    refine MonoidHom.mem_range.mpr ⟨⟨a.1, hA_X a.2⟩, ?_⟩
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [hψ]
    simp [MulAut.conj_apply]
  have hne : ψ.range ≠ (MulAut.conj : ↥A →* MulAut ↥A).range := by
    intro hrange
    obtain ⟨s, hsS, hsout⟩ := hout
    have hsX : s ∈ A ⊔ S ⊔ B := hS_X hsS
    have hmem : ψ ⟨s, hsX⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [hrange, MonoidHom.mem_range] at hmem
    obtain ⟨a', ha'⟩ := hmem
    obtain ⟨x, hxA, hx⟩ := hsout (a' : Q) a'.2
    apply hx
    have h1 := congrArg (fun g : MulAut ↥A => ((g ⟨x, hxA⟩ : ↥A) : Q)) ha'
    simp only [MulAut.conj_apply, hψ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk] at h1
    exact h1.symm
  have hFactApp := hFact p hp hp3 h8 ↥A hA ψ.range Saut hInn hne hSyl
  intro d hd a ha
  have hdX : d ∈ A ⊔ S ⊔ B := hB_X hd
  have hdN : d ∈ Subgroup.normalizer (S : Set Q) := hBS hd
  have hd'N : (⟨d, hdX⟩ : ↥(A ⊔ S ⊔ B)) ∈
      Subgroup.normalizer ((S.subgroupOf (A ⊔ S ⊔ B) : Subgroup ↥(A ⊔ S ⊔ B)) :
        Set ↥(A ⊔ S ⊔ B)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    exact Subgroup.mem_normalizer_iff.mp hdN (y : Q)
  have hδA : ψ ⟨d, hdX⟩ ∈ ψ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hδN : ψ ⟨d, hdX⟩ ∈
      Subgroup.normalizer ((Saut : Subgroup (MulAut ↥A)) : Set (MulAut ↥A)) :=
    Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ hd'N)
  have hδS : ψ ⟨d, hdX⟩ ∈ Saut := hFactApp (Subgroup.mem_inf.mpr ⟨hδN, hδA⟩)
  obtain ⟨k, hk⟩ := hSyl.2.1 ⟨ψ ⟨d, hdX⟩, hδS⟩
  have hk' : ψ ⟨d, hdX⟩ ^ 2 ^ k = 1 := by
    have h := congrArg Subtype.val hk
    simpa using h
  have hdvd1 : orderOf (ψ ⟨d, hdX⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd2 : orderOf (ψ ⟨d, hdX⟩) ∣ orderOf d := by
    have h := orderOf_map_dvd ψ ⟨d, hdX⟩
    rwa [Subgroup.orderOf_mk] at h
  have hcop : Nat.Coprime (2 ^ k) (orderOf d) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (hBodd d hd))
  have hone : orderOf (ψ ⟨d, hdX⟩) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hdvd2
  have hψ1 : ψ ⟨d, hdX⟩ = 1 := orderOf_eq_one_iff.mp hone
  have h3 : ((ψ ⟨d, hdX⟩ ⟨a, ha⟩ : ↥A) : Q) = a :=
    congrArg (fun g : MulAut ↥A => ((g ⟨a, ha⟩ : ↥A) : Q)) hψ1
  rw [hψ] at h3
  exact h3

namespace Lem3313Q

open CFSG.Quasithin.H13.BenC CFSG.Quasithin.H13.Lem3313B

theorem obl3_3_13D12NF_outer_of (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (hFact : FactAutL2pOuter) : Obl3_3_13D12NF_outer := by
  intro G _ _ T M L D H K h hH hHLT ⟨e⟩ hO hK hKq hYK hTK ⟨q, hq, h24, hmod⟩ hout
  have hq2 : q ≠ 2 := by omega
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.simple
  have hTH : T ≤ H := hH.1
  have hTsyl : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow hTH⟩
  have hT₀ : IsSylowTwoOf T (H ⊔ D) := ⟨hTH.trans le_sup_left, h.sylow.1,
    Vol2.Ch10.SecA.not_two_dvd_index_of_le h.sylow (hTH.trans le_sup_left)⟩
  have hT2 : IsPGroup 2 T := h.sylow.1
  set φ := oTwoQuotEquiv e with hφ
  have hYH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hXi := Der6D.xi_of_iso hTsyl hH.2 φ
  have hrel := C1Pack12.relIndex_pCoreOf_oTwoUpper φ
  have hOHT : pCoreOf 2 H ≤ T := pCoreOf_le_of_isSylowTwoOf hTsyl
  have hpow3 : ∀ x ∈ oTwoUpper H, x ^ 3 ∈ T := fun x hx =>
    hOHT (C1Pack12.pow_three_mem_pCoreOf φ hx)
  have h3 : 3 ∣ Nat.card (oTwoUpper H) := by
    rw [card_eq_card_pCoreOf_mul_relIndex, hrel]
    exact Dvd.dvd.mul_left (by norm_num) _
  obtain ⟨P3, hP3⟩ := Vol2.Ch10.SecB.exists_isSylowIn_three (oTwoUpper H)
  have hP3card : Nat.card P3 = 9 := by rw [hXi.card_sylow (by norm_num) h3 hP3, hrel]
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hHN : H ⊔ D ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hKc h37 h38 hO hT₀ hK
  set H₀ := H ⊔ D with hH₀
  have hHH₀ : H ≤ H₀ := le_sup_left
  have hDH₀ : D ≤ H₀ := le_sup_right
  have hTH₀ : T ≤ H₀ := hTH.trans hHH₀
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hKc hO
  have h37Q := h37 _ hQ
  have h38Q := h38 _ hQ
  set π : ↥H₀ →* ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) with hπ
  have hker : ∀ x : ↥H₀, π x = 1 → (x : G) ∈ T := by
    intro x hx
    have h1 : x ∈ CFSG.Open.pCore 2 ↥H₀ := by
      exact (QuotientGroup.eq_one_iff x).mp hx
    exact pCoreOf_le_of_isSylowTwoOf hT₀ ⟨x, h1, rfl⟩
  set Ab := modO2Image H₀ K with hAb
  set Tb := modO2Image H₀ T with hTbdef
  have hAbc : Ab ∈ cComp (⊤ : Subgroup _) := modO2Image_mem_cComp hK
  have hTb : IsSylowTwoOf Tb ⊤ :=
    A312.isSylowTwoOf_top_map π (QuotientGroup.mk'_surjective _)
      (isSylowTwoOf_top_subgroupOf hT₀)
  obtain ⟨-, hT38⟩ := h38Q Ab hAbc
  rcases hT38 Tb hTb with ⟨hnorm, -, -⟩ |
      ⟨tb, htb, htbn, hconjT, -, hcomm, hinf, hTbN, hsupT⟩
  ·
    exfalso
    apply hTK
    intro t ht
    have htH : t ∈ H₀ := hTH₀ ht
    have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
    have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) = modO2Image H₀ K := by
      refine (modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩).trans ?_
      refine A38.map_conj_eq_iff.mpr ?_
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm]
      exact Subgroup.mem_top _
    exact A38.map_conj_eq_iff.mp (modO2Image_injOn H₀ h1 hK h2)
  set Ab' := Ab.map (MulAut.conj tb).toMonoidHom with hAb'
  have hAb'c : Ab' ∈ cComp (⊤ : Subgroup _) := C2A3Orbits.conj_mem_cComp_top hAbc tb
  have hne : Ab ≠ Ab' := fun h1 => htbn (A38.map_conj_eq_iff.mp h1.symm)
  have hcomm' : ∀ a ∈ Ab, ∀ b ∈ Ab', a * b = b * a := by
    intro a ha b hb
    have h1 : Ab ≤ Subgroup.centralizer (Ab' : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact (Subgroup.mem_centralizer_iff.mp (h1 ha) b hb).symm
  have : Fact q.Prime := ⟨hq⟩
  have hq3 : q ≠ 3 := by
    intro h3q
    apply hmod.1.2.2.2.2
    rw [h3q, pow_one]
  have hq5 : 5 ≤ q := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    have := hq.two_le
    omega
  have hF : Nat.card (GaloisField q 1) = q := by
    rw [GaloisField.card q 1 (by norm_num), pow_one]
  obtain ⟨e₁⟩ := modO2_mulEquiv hK
  obtain ⟨e₂⟩ := CFSG.Adapters.RankTwoModelTransports.nonempty_mulEquiv_psl_galoisField _ 2 q 1
    hmod
  let eA : ↥Ab ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q 1) := e₁.symm.trans e₂
  let eA' : ↥Ab' ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q 1) :=
    (Subgroup.equivMapOfInjective Ab (MulAut.conj tb).toMonoidHom
      (MulAut.conj tb).injective).symm.trans eA
  have hAN : Ab ≤ Subgroup.normalizer ((Ab ⊔ Ab' : Subgroup _) : Set _) := fun a ha =>
    Lem3313B.mem_normalizer_sup (Subgroup.le_normalizer ha) (Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcomm' a ha b hb).symm))
  have hTbAT : IsSylowTwoOf Tb (Ab ⊔ Tb) := ⟨le_sup_right, hTb.2.1, fun h2 => hTb.2.2
    (h2.trans (by
      show Tb.relIndex (Ab ⊔ Tb) ∣ Tb.relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      exact Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hS0 : IsSylowTwoOf (Tb ⊓ (Ab ⊔ Ab')) (Ab ⊔ Ab') :=
    A4.isSylowTwoOf_inf_normal hTbAT (by rw [hsupT]; exact le_sup_left) (sup_le hAN hTbN)
  have hAAN : Ab ⊔ Ab' ≤ Subgroup.normalizer (Ab : Set _) :=
    sup_le Subgroup.le_normalizer (le_normalizer_of_comm hcomm')
  have hAAN' : Ab ⊔ Ab' ≤ Subgroup.normalizer (Ab' : Set _) :=
    sup_le (le_normalizer_of_comm (fun a ha b hb => (hcomm' b hb a ha).symm))
      Subgroup.le_normalizer
  have hS : IsSylowTwoOf (Tb ⊓ Ab) Ab := by
    have h1 := A4.isSylowTwoOf_inf_normal hS0 le_sup_left hAAN
    rwa [inf_assoc, inf_of_le_right (le_sup_left : Ab ≤ Ab ⊔ Ab')] at h1
  have hS' : IsSylowTwoOf (Tb ⊓ Ab') Ab' := by
    have h1 := A4.isSylowTwoOf_inf_normal hS0 le_sup_right hAAN'
    rwa [inf_assoc, inf_of_le_right (le_sup_right : Ab' ≤ Ab ⊔ Ab')] at h1
  obtain ⟨⟨t₀, ht₀H⟩, ht₀T, rfl⟩ := htb
  set K' := K.map (MulAut.conj t₀).toMonoidHom with hK'
  have hK'c : K' ∈ cComp H₀ := map_conj_mem_cComp hK ht₀H
  have hK'b : modO2Image H₀ K' = Ab' := modO2Image_conj ⟨t₀, ht₀H⟩
  have hKK : conjClosure K T = K ⊔ K' := by
    refine le_antisymm (conjClosure_le fun t ht k hk => ?_) (sup_le (le_conjClosure K T) ?_)
    · have htH : t ∈ H₀ := hTH₀ ht
      have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp H₀ := map_conj_mem_cComp hK htH
      have h2 : modO2Image H₀ (K.map (MulAut.conj t).toMonoidHom) ∈ conjSubgroupsBy Tb Ab := by
        rw [modO2Image_conj (H := H₀) (L := K) ⟨t, htH⟩]
        exact ⟨π ⟨t, htH⟩, mk_mem_img _ ht, rfl⟩
      rw [hconjT] at h2
      have hmem : t * k * t⁻¹ ∈ K.map (MulAut.conj t).toMonoidHom := ⟨k, hk, rfl⟩
      rcases h2 with h2 | h2
      · rw [modO2Image_injOn H₀ h1 hK h2] at hmem
        exact Subgroup.mem_sup_left hmem
      · rw [Set.mem_singleton_iff, ← hK'b] at h2
        rw [modO2Image_injOn H₀ h1 hK'c h2] at hmem
        exact Subgroup.mem_sup_right hmem
    · rintro _ ⟨k, hk, rfl⟩
      exact mem_conjClosure (show t₀ ∈ T from ht₀T) hk
  have hKKb : modO2Image H₀ (K ⊔ K') = Ab ⊔ Ab' := by
    rw [img_sup (le_of_mem_cComp hK) (le_of_mem_cComp hK'c), hK'b]
  set Yb := modO2Image H₀ (oTwoUpper H) with hYb
  set Pb := modO2Image H₀ P3 with hPb
  set Db := modO2Image H₀ D with hDb
  have hTY : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    hTH.trans (le_normalizer_oTwoUpper H)
  have hYbA : Yb ≤ Ab ⊔ Ab' := by
    rw [← hKKb]
    exact img_mono (hYK.trans hKK.le)
  have hPbY : Pb ≤ Yb := img_mono hP3.1
  have hPb9 : Nat.card Pb = 9 := by
    rw [← hP3card]
    have hinj : Function.Injective (π.comp (P3.subgroupOf H₀).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : ((x : ↥H₀) : G) ∈ T := hker _ hx
      have h2 : ((x : ↥H₀) : G) ∈ P3 := x.2
      have h3 : ((x : ↥H₀) : G) ∈ P3 ⊓ T := ⟨h2, h1⟩
      rw [(IsPGroup.disjoint_of_ne 3 2 (by norm_num) P3 T hP3.2.1 hT2).eq_bot,
        Subgroup.mem_bot] at h3
      exact Subtype.ext (Subtype.ext h3)
    have h1 : Pb = (π.comp (P3.subgroupOf H₀).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      try rfl
    rw [h1, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hP3.1.trans (hYH.trans hHH₀))).toEquiv
  have hYb3 : ∀ y ∈ Yb, y ^ 3 ∈ Tb := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    exact mk_mem_img _ (by simpa using hpow3 _ hy)
  have hDodd : ∀ x ∈ Db, Odd (orderOf x) := by
    rintro _ ⟨d, hd, rfl⟩
    refine Odd.of_dvd_nat h.Dodd ?_
    refine (orderOf_map_dvd π d).trans ?_
    have h1 : orderOf d = orderOf ((d : G)) := Subgroup.orderOf_coe d |>.symm
    have h2 : orderOf ((⟨d, hd⟩ : ↥D)) = orderOf (d : G) := Subgroup.orderOf_mk _ _
    rw [h1, ← h2]
    exact orderOf_dvd_natCard _
  have hDN : Db ≤ Subgroup.normalizer ((Ab ⊔ Ab' : Subgroup _) : Set _) := by
    rw [← hKKb]
    refine img_le_normalizer ?_
    rw [← hKK]
    exact hDH₀.trans hHN
  have hDA : Db ≤ Subgroup.normalizer (Ab : Set _) := fun x hx =>
    (mem_normalizer_of_odd h37Q hAbc hAb'c hne (hDN hx) (hDodd x hx)).1
  have hDA' : Db ≤ Subgroup.normalizer (Ab' : Set _) := fun x hx =>
    (mem_normalizer_of_odd h37Q hAbc hAb'c hne (hDN hx) (hDodd x hx)).2
  have hDT : Db ≤ Subgroup.normalizer (Tb : Set _) := img_le_normalizer h.DN
  have hcore : Db ≤ Subgroup.normalizer (Yb : Set _) := by
    set tb : ↥H₀ ⧸ CFSG.pCore 2 ↥H₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥H₀) ⟨t₀, ht₀H⟩ with htbdef
    have hTbmem : tb ∈ Tb := mk_mem_img _ ht₀T
    have hq8 : q % 8 = 3 ∨ q % 8 = 5 := by omega
    have hq3 : 3 < q := by omega
    obtain ⟨s, ⟨hsT, hsN⟩, hs⟩ := exists_outer_modO2 hTH₀ (le_of_mem_cComp hK) hout
    have hAL2 : F6.IsL2 q 1 ↥Ab :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₁ hmod
    have hAL2' : F6.IsL2 q 1 ↥Ab' :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (Subgroup.equivMapOfInjective Ab
        (MulAut.conj tb).toMonoidHom (MulAut.conj tb).injective) hAL2
    have hNN : ∀ (X : Subgroup (↥H₀ ⧸ CFSG.pCore 2 ↥H₀)), Db ≤ Subgroup.normalizer (X : Set _) →
        Db ≤ Subgroup.normalizer ((Tb ⊓ Subgroup.normalizer (X : Set _) : Subgroup _) : Set _) := by
      intro X hX d hd
      have hdN : d ∈ Subgroup.normalizer
          ((Subgroup.normalizer (X : Set (↥H₀ ⧸ CFSG.pCore 2 ↥H₀)) :
            Subgroup (↥H₀ ⧸ CFSG.pCore 2 ↥H₀)) : Set (↥H₀ ⧸ CFSG.pCore 2 ↥H₀)) :=
        Subgroup.le_normalizer (hX hd)
      exact ChiefCount.mem_normalizer_inf (hDT hd) hdN
    have hSA : ∀ (X : Subgroup (↥H₀ ⧸ CFSG.pCore 2 ↥H₀)),
        IsSylowTwoOf (Tb ⊓ X) X →
        IsSylowTwoOf ((Tb ⊓ Subgroup.normalizer (X : Set _)) ⊓ X) X := by
      intro X hX
      have : (Tb ⊓ Subgroup.normalizer (X : Set _)) ⊓ X = Tb ⊓ X := by
        rw [inf_assoc, inf_of_le_right Subgroup.le_normalizer]
      rwa [this]
    have hcentA : ∀ d ∈ Db, ∀ a ∈ Ab, d * a * d⁻¹ = a :=
      centralizes_of_outer hFact hq hq3 hq8 hAL2 inf_le_right hTb.2.1.to_inf_left (hSA Ab hS)
        ⟨s, ⟨hsT, hsN⟩, hs⟩ hDA (hNN Ab hDA) hDodd
    have hs' : ∃ s' ∈ Tb ⊓ Subgroup.normalizer (Ab' : Set _),
        ∀ a ∈ Ab', ∃ x ∈ Ab', s' * x * s'⁻¹ ≠ a * x * a⁻¹ :=
      ⟨tb * s * tb⁻¹, ⟨Tb.mul_mem (Tb.mul_mem hTbmem hsT) (Tb.inv_mem hTbmem),
        conj_mem_normalizer_map tb hsN⟩, outer_conj tb hs⟩
    have hcentA' : ∀ d ∈ Db, ∀ a ∈ Ab', d * a * d⁻¹ = a :=
      centralizes_of_outer hFact hq hq3 hq8 hAL2' inf_le_right hTb.2.1.to_inf_left (hSA Ab' hS')
        hs' hDA' (hNN Ab' hDA') hDodd
    have hy : ∀ d ∈ Db, ∀ y ∈ Yb, d * y * d⁻¹ = y := by
      intro d hd y hy
      obtain ⟨a, ha, a', ha', rfl⟩ := (BenC.mem_sup_iff hcomm').mp (hYbA hy)
      rw [show d * (a * a') * d⁻¹ = (d * a * d⁻¹) * (d * a' * d⁻¹) by group,
        hcentA d hd a ha, hcentA' d hd a' ha']
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyY
      rw [hy d hd y hyY]
      exact hyY
    · intro hyY
      have h2 := hy d⁻¹ (Db.inv_mem hd) _ hyY
      have e : y = d * y * d⁻¹ := by
        calc y = d⁻¹ * (d * y * d⁻¹) * d⁻¹⁻¹ := by group
          _ = d * y * d⁻¹ := h2
      rw [e]
      exact hyY
  set R := (Yb.comap π).map H₀.subtype with hR
  have hRmem : ∀ g : G, g ∈ R ↔ ∃ hg : g ∈ H₀, π ⟨g, hg⟩ ∈ Yb := by
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hg, hgR⟩
      exact ⟨⟨g, hg⟩, hgR, rfl⟩
  have hYR : oTwoUpper H ≤ R := fun y hy =>
    (hRmem y).mpr ⟨hHH₀ (hYH hy), mk_mem_img _ hy⟩
  have hRYT : R ≤ oTwoUpper H ⊔ T := by
    intro g hg
    obtain ⟨hgH, hgR⟩ := (hRmem g).mp hg
    obtain ⟨y, hy, hyg⟩ := hgR
    have h2 : π (y⁻¹ * ⟨g, hgH⟩) = 1 := by
      rw [map_mul, map_inv, hyg, inv_mul_cancel]
    have h3 := hker _ h2
    have e : g = (y : G) * (((y⁻¹ * ⟨g, hgH⟩ : ↥H₀)) : G) := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h3)
  have hO2R : oTwoUpper R = oTwoUpper H := by
    refine le_antisymm ?_ ?_
    · rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hx, ho⟩
      exact CZCore.mem_of_odd hTY hT2 (hRYT hx) ho
    · have h1 : oTwoUpper H = oTwoUpper (oTwoUpper H) := hXi.1
      rw [h1]
      exact oTwoUpper_mono hYR
  have hDR : D ≤ Subgroup.normalizer (R : Set G) := by
    have key : ∀ d ∈ D, ∀ g ∈ R, d * g * d⁻¹ ∈ R := by
      intro d hd g hg
      obtain ⟨hgH, hgR⟩ := (hRmem g).mp hg
      have hdH : d ∈ H₀ := hDH₀ hd
      refine (hRmem _).mpr ⟨H₀.mul_mem (H₀.mul_mem hdH hgH) (H₀.inv_mem hdH), ?_⟩
      have e : (⟨d * g * d⁻¹, H₀.mul_mem (H₀.mul_mem hdH hgH) (H₀.inv_mem hdH)⟩ : ↥H₀) =
          ⟨d, hdH⟩ * ⟨g, hgH⟩ * (⟨d, hdH⟩ : ↥H₀)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hcore (mk_mem_img _ hd)) _).mp hgR
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨key d hd g, fun hg => ?_⟩
    have := key d⁻¹ (D.inv_mem hd) _ hg
    simpa [mul_assoc] using this
  rw [← hO2R]
  exact hDR.trans (normalizer_le_normalizer_oTwoUpper R)

end Lem3313Q

end CFSG.Quasithin.H13
