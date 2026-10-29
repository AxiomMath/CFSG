module

public import CFSG.RankThree.GF2n.Smith81.OrthE1Steps
public import CFSG.RankThree.GF2n.Smith81.OrthSL2Cube
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Gaschutz

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem e1SplitCompl {H : Type} [Group H] [Finite H] (P N : Subgroup H)
    (hcomm : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hsq : ∀ a ∈ P, a ^ 2 = 1) (hNP : N ≤ P) :
    ∃ K : Subgroup H, N ⊓ K = ⊥ ∧ N ⊔ K = P := by
  letI : CommGroup P :=
    { (inferInstance : Group P) with mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  have hsqP : ∀ a : P, a ^ 2 = 1 := fun a => Subtype.ext (hsq a a.2)
  obtain ⟨KA, hKA, hmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {K : Subgroup P | N.subgroupOf P ⊓ K = ⊥}) ⟨⊥, by simp⟩
  have hKA' : N.subgroupOf P ⊓ KA = ⊥ := hKA
  have htop : N.subgroupOf P ⊔ KA = ⊤ := by
    by_contra hne
    obtain ⟨x, hx⟩ : ∃ x : P, x ∉ N.subgroupOf P ⊔ KA := by
      by_contra hcon
      push Not at hcon
      exact hne (eq_top_iff.mpr fun x _ => hcon x)
    have hK'S : N.subgroupOf P ⊓ (KA ⊔ Subgroup.zpowers x) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro y hy
      obtain ⟨hyN, hyK⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨k, hk, z, hz, hkz⟩ := Subgroup.mem_sup.mp hyK
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hsqz : ∀ j : ℤ, x ^ (2 * j) = 1 := fun j => by
        rw [zpow_mul]
        have h2 : x ^ (2 : ℤ) = 1 := by simpa using hsqP x
        rw [h2, one_zpow]
      rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have h1 : x ^ (j + j) = 1 := by
          rw [← two_mul]
          exact hsqz j
        rw [h1, mul_one] at hkz
        have hyKA : y ∈ N.subgroupOf P ⊓ KA := ⟨hyN, hkz ▸ hk⟩
        rw [hKA'] at hyKA
        exact hyKA
      · exfalso
        have h1 : x ^ (2 * j + 1) = x := by
          rw [zpow_add, hsqz j, one_mul, zpow_one]
        rw [h1] at hkz
        apply hx
        have hk' : k⁻¹ ∈ KA := KA.inv_mem hk
        have := (N.subgroupOf P ⊔ KA).mul_mem (Subgroup.mem_sup_right hk')
          (Subgroup.mem_sup_left hyN)
        rw [← hkz] at this
        simpa [mul_assoc] using this
    have hle : KA ≤ KA ⊔ Subgroup.zpowers x := le_sup_left
    have hK'eq : KA ⊔ Subgroup.zpowers x ≤ KA := hmax hK'S hle
    exact hx (Subgroup.mem_sup_right (hK'eq (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))))
  refine ⟨KA.map P.subtype, ?_, ?_⟩
  · have hN : (N.subgroupOf P).map P.subtype = N := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNP]
    rw [← hN, ← Subgroup.map_inf_eq _ _ _ P.subtype_injective, hKA', Subgroup.map_bot]
  · have hN : (N.subgroupOf P).map P.subtype = N := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNP]
    have hmapTop : (⊤ : Subgroup P).map P.subtype = P := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have htop' := congrArg (Subgroup.map P.subtype) htop
    rw [Subgroup.map_sup, hN, hmapTop] at htop'
    exact htop'


section Core

variable {G : Type} [Group G] [Finite G]

theorem e1SplitMemBar {R Q S : Subgroup G} [(Q.subgroupOf R).Normal] (hQS : Q ≤ S) (hSR : S ≤ R)
    {r : G} (hr : r ∈ R) :
    (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ : ↥R ⧸ Q.subgroupOf R) ∈ bar R Q S ↔ r ∈ S := by
  unfold bar
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hsr⟩
    rw [Subgroup.mem_subgroupOf] at hs
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hsr
    have h1 : (s : G)⁻¹ * r ∈ Q := by
      have h2 : ((s⁻¹ * ⟨r, hr⟩ : ↥R) : G) ∈ Q := hsr
      simpa using h2
    have h3 : r = (s : G) * ((s : G)⁻¹ * r) := by group
    rw [h3]
    exact S.mul_mem hs (hQS h1)
  · intro hrS
    exact ⟨⟨r, hr⟩, Subgroup.mem_subgroupOf.mpr hrS, rfl⟩

theorem e1SplitCommCentral {H : Type} [Group H] {a b : H} (ha : ∀ y : H, a * y = y * a)
    (hb : ∀ y : H, b * y = y * b) (x y : H) : ⁅a * x, b * y⁆ = ⁅x, y⁆ := by
  have ha' : ∀ z : H, a * z * a⁻¹ = z := fun z => by
    rw [ha z, mul_assoc, mul_inv_cancel, mul_one]
  have hb' : ∀ z : H, b * z * b⁻¹ = z := fun z => by
    rw [hb z, mul_assoc, mul_inv_cancel, mul_one]
  have hxb : x * b = b * x := (hb x).symm
  calc ⁅a * x, b * y⁆ = a * (x * (b * y) * x⁻¹) * a⁻¹ * (y⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = (x * (b * y) * x⁻¹) * (y⁻¹ * b⁻¹) := by rw [ha']
    _ = b * (x * y * x⁻¹) * (y⁻¹ * b⁻¹) := by
        rw [← mul_assoc x b y, hxb]; simp only [mul_assoc]
    _ = (x * y * x⁻¹) * y⁻¹ := by
        have : b * (x * y * x⁻¹) * (y⁻¹ * b⁻¹) = b * ((x * y * x⁻¹) * y⁻¹) * b⁻¹ := by
          simp only [mul_assoc]
        rw [this, hb']
    _ = ⁅x, y⁆ := by simp only [commutatorElement_def, mul_assoc]

end Core


section Split

variable {G : Type} [Group G] [Finite G]

theorem e1SplitCore {R N Q L : Subgroup G} {q : ℕ} [(Q.subgroupOf R).Normal]
    [hNn : (N.subgroupOf R).Normal] (hQR : Q ≤ R) (hQN : Q ≤ N) (hNR : N ≤ R) (hLR : L ≤ R)
    (hQL : Q ≤ L) (hN2 : IsPGroup 2 ↥(N.subgroupOf R))
    (hcen : ∀ r ∈ R, ∀ n ∈ N, ⁅r, n⁆ ∈ Q)
    (hLcomm : ∀ x ∈ L, ∀ y ∈ L, ⁅x, y⁆ ∈ Q) (hLsq : ∀ x ∈ L, x ^ 2 ∈ Q)
    (hNcard : Nat.card N = Nat.card Q * q) (hLcard : Nat.card L = Nat.card Q * q ^ 3)
    {Ω : Type} [Group Ω] [Finite Ω] (hΩperf : ⁅(⊤ : Subgroup Ω), (⊤ : Subgroup Ω)⁆ = ⊤)
    (hΩsyl : ∀ P : Sylow 2 Ω, Nat.card P = q ^ 2)
    (e : ↥R ⧸ N.subgroupOf R ≃* Ω) :
    ∃ X : Subgroup G, Q ≤ X ∧ X ≤ R ∧ N ⊓ X = Q ∧ N ⊔ X = R ∧
      (∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X) ∧ ⁅X, X⁆ ⊔ Q = X ∧ ⁅R, R⁆ ⊔ Q = X ∧
      L = N ⊔ (L ⊓ X) ∧ N ≤ L ∧ Nat.card ↥(L ⊓ X) = Nat.card Q * q ^ 2 ∧
      QuotIso X Q Ω := by
  classical
  have hQRn : (Q.subgroupOf R).Normal := inferInstance
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso
      have h1 := Nat.card_pos (α := ↥L)
      rw [hLcard, h] at h1
      simp at h1
    · exact h
  have hmksurj : Function.Surjective (QuotientGroup.mk' (Q.subgroupOf R)) :=
    QuotientGroup.mk'_surjective _
  have hQRc : Nat.card (Q.subgroupOf R) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
  have hNRc : Nat.card (N.subgroupOf R) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hHcard : Nat.card (↥R ⧸ Q.subgroupOf R) * Nat.card Q = Nat.card R := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf R), hQRc]
  have hRcard : Nat.card R = Nat.card Ω * Nat.card N := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf R),
      Nat.card_congr e.toEquiv, hNRc]
  have hHcard' : Nat.card (↥R ⧸ Q.subgroupOf R) = Nat.card Ω * q := by
    apply Nat.eq_of_mul_eq_mul_right hQpos
    rw [hHcard, hRcard, hNcard]
    ring
  set Nb : Subgroup (↥R ⧸ Q.subgroupOf R) := bar R Q N with hNb
  set Lb : Subgroup (↥R ⧸ Q.subgroupOf R) := bar R Q L with hLb
  have hNbcard : Nat.card Nb = q := by
    have h := bar_card_mul_card_of_le (M := R) (Q := Q) (S := N) hQN hNR
    have h' : Nat.card Nb * Nat.card Q = q * Nat.card Q := by
      rw [h, hNcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hQpos h'
  have hLbcard : Nat.card Lb = q ^ 3 := by
    have h := bar_card_mul_card_of_le (M := R) (Q := Q) (S := L) hQL hLR
    have h' : Nat.card Lb * Nat.card Q = q ^ 3 * Nat.card Q := by
      rw [h, hLcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hQpos h'
  have memNb : ∀ {r : G} (hr : r ∈ R),
      (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ : ↥R ⧸ Q.subgroupOf R) ∈ Nb ↔ r ∈ N :=
    fun hr => e1SplitMemBar hQN hNR hr
  have memLb : ∀ {r : G} (hr : r ∈ R),
      (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ : ↥R ⧸ Q.subgroupOf R) ∈ Lb ↔ r ∈ L :=
    fun hr => e1SplitMemBar hQL hLR hr
  have hcenmk : ∀ (r : G) (hr : r ∈ R) (s : G) (hs : s ∈ N),
      (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ : ↥R ⧸ Q.subgroupOf R) *
        QuotientGroup.mk' (Q.subgroupOf R) ⟨s, hNR hs⟩ =
      QuotientGroup.mk' (Q.subgroupOf R) ⟨s, hNR hs⟩ *
        QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ := by
    intro r hr s hs
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hcRm : (⁅r⁻¹, s⁆ : G) ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem (R.inv_mem hr) (hNR hs)) (R.inv_mem (R.inv_mem hr)))
        (R.inv_mem (hNR hs))
    have hc : (⁅r⁻¹, s⁆ : G) ∈ Q := hcen r⁻¹ (R.inv_mem hr) s hs
    have hcR : (⟨⁅r⁻¹, s⁆, hcRm⟩ : ↥R) ∈ Q.subgroupOf R := Subgroup.mem_subgroupOf.mpr hc
    have hconj := hQRn.conj_mem _ hcR ⟨(s : G)⁻¹, R.inv_mem (hNR hs)⟩
    rw [Subgroup.mem_subgroupOf] at hconj ⊢
    convert hconj using 1
    simp only [commutatorElement_def, mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hNbcen : ∀ h : ↥R ⧸ Q.subgroupOf R, ∀ n ∈ Nb, h * n = n * h := by
    intro h n hn
    obtain ⟨r, rfl⟩ := hmksurj h
    have hn' : n ∈ (N.subgroupOf R).map (QuotientGroup.mk' (Q.subgroupOf R)) := hn
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hn'
    exact hcenmk r.1 r.2 s.1 (Subgroup.mem_subgroupOf.mp hs)
  haveI hNbn : Nb.Normal := ⟨fun n hn h => by
    rw [hNbcen h n hn, mul_inv_cancel_right]
    exact hn⟩
  haveI hNbmc : IsMulCommutative ↥Nb :=
    ⟨⟨fun a b => Subtype.ext (hNbcen (a : ↥R ⧸ Q.subgroupOf R) (b : ↥R ⧸ Q.subgroupOf R) b.2)⟩⟩
  have hNbpg : IsPGroup 2 ↥Nb := IsPGroup.map hN2 _
  have hLbcomm : ∀ a ∈ Lb, ∀ b ∈ Lb, a * b = b * a := by
    intro a ha b hb
    obtain ⟨r, rfl⟩ := hmksurj a
    obtain ⟨s, rfl⟩ := hmksurj b
    have hr : r.1 ∈ L := (memLb r.2).mp ha
    have hs : s.1 ∈ L := (memLb s.2).mp hb
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have hc := hLcomm s.1⁻¹ (L.inv_mem hs) r.1⁻¹ (L.inv_mem hr)
    simp only [commutatorElement_def, inv_inv] at hc
    convert hc using 1
    simp only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
  have hLbsq : ∀ a ∈ Lb, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨r, rfl⟩ := hmksurj a
    have hr : r.1 ∈ L := (memLb r.2).mp ha
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (hLsq _ hr)
  have hLbpg : IsPGroup 2 ↥Lb := fun g => ⟨1, Subtype.ext (by simpa [pow_one] using hLbsq g.1 g.2)⟩
  obtain ⟨P0⟩ : Nonempty (Sylow 2 Ω) := inferInstance
  have hP0 := hΩsyl P0
  have hΩidx : Nat.card Ω = q ^ 2 * (P0 : Subgroup Ω).index := by
    rw [← hP0, Subgroup.card_mul_index]
  have hodd : ¬ 2 ∣ (P0 : Subgroup Ω).index := Sylow.not_dvd_index P0
  have hLbidx : Lb.index = (P0 : Subgroup Ω).index := by
    have h1 := Subgroup.card_mul_index Lb
    rw [hLbcard, hHcard', hΩidx] at h1
    apply Nat.eq_of_mul_eq_mul_left (pow_pos hq 3)
    rw [h1]
    ring
  have hLbsyl : ¬ 2 ∣ Lb.index := by rw [hLbidx]; exact hodd
  let PL : Sylow 2 (↥R ⧸ Q.subgroupOf R) := hLbpg.toSylow hLbsyl
  have hNbLb : Nb ≤ Lb := IsPGroup.le_sylow_of_normal hNbpg PL
  obtain ⟨K, hK1, hK2⟩ := e1SplitCompl Lb Nb hLbcomm hLbsq hNbLb
  obtain ⟨D, hD1, hD2⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.exists_complement_of_sylow_complement
      Nat.prime_two (N := Nb) hNbpg PL hNbLb hK1 hK2
  have hdecH : ∀ h : ↥R ⧸ Q.subgroupOf R, ∃ a ∈ Nb, ∃ d ∈ D, h = a * d := by
    intro h
    have hmem : h ∈ Nb ⊔ D := by rw [hD2]; exact Subgroup.mem_top h
    obtain ⟨a, ha, d, hd, had⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    exact ⟨a, ha, d, hd, had.symm⟩
  set X : Subgroup G := (D.comap (QuotientGroup.mk' (Q.subgroupOf R))).map R.subtype with hXdef
  have memX : ∀ {r : G} (hr : r ∈ R),
      r ∈ X ↔ (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ : ↥R ⧸ Q.subgroupOf R) ∈ D := by
    intro r hr
    constructor
    · intro h
      obtain ⟨y, hy, hyr⟩ := Subgroup.mem_map.mp h
      have hyeq : y = ⟨r, hr⟩ := Subtype.ext hyr
      subst hyeq
      exact hy
    · intro h
      exact Subgroup.mem_map.mpr ⟨⟨r, hr⟩, h, rfl⟩
  have hQX : Q ≤ X := by
    intro x hx
    have hxR : x ∈ R := hQR hx
    rw [memX hxR]
    have h1 : (QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ : ↥R ⧸ Q.subgroupOf R) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hx
    rw [h1]
    exact D.one_mem
  have hXR : X ≤ R := Subgroup.map_subtype_le _
  have hdec : ∀ r ∈ R, ∃ n ∈ N, ∃ x ∈ X, r = n * x := by
    intro r hr
    obtain ⟨a, ha, d, hd, had⟩ := hdecH (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩)
    have ha' : a ∈ (N.subgroupOf R).map (QuotientGroup.mk' (Q.subgroupOf R)) := ha
    obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.mp ha'
    have hsN : (s : G) ∈ N := Subgroup.mem_subgroupOf.mp hs
    have hxR : (s : G)⁻¹ * r ∈ R := R.mul_mem (R.inv_mem s.2) hr
    refine ⟨(s : G), hsN, (s : G)⁻¹ * r, ?_, by group⟩
    rw [memX hxR]
    have e1 : (QuotientGroup.mk' (Q.subgroupOf R) ⟨(s : G)⁻¹ * r, hxR⟩ :
        ↥R ⧸ Q.subgroupOf R) =
        (QuotientGroup.mk' (Q.subgroupOf R) s)⁻¹ *
          QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e1, hsa, had, inv_mul_cancel_left]
    exact hd
  have hNX : N ⊓ X = Q := by
    apply le_antisymm
    · intro g hg
      obtain ⟨hgN, hgX⟩ := Subgroup.mem_inf.mp hg
      have hgR : g ∈ R := hNR hgN
      rw [memX hgR] at hgX
      have hmem : (QuotientGroup.mk' (Q.subgroupOf R) ⟨g, hgR⟩ : ↥R ⧸ Q.subgroupOf R) ∈ Nb ⊓ D :=
        ⟨(memNb hgR).mpr hgN, hgX⟩
      rw [hD1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    · exact le_inf hQN hQX
  have hNXR : N ⊔ X = R := by
    apply le_antisymm (sup_le hNR hXR)
    intro r hr
    obtain ⟨n, hn, x, hx, hrx⟩ := hdec r hr
    rw [hrx]
    exact Subgroup.mul_mem_sup hn hx
  have hXnorm : ∀ r ∈ R, ∀ x ∈ X, r * x * r⁻¹ ∈ X := by
    intro r hr x hx
    have hxR : x ∈ R := hXR hx
    have hrxr : r * x * r⁻¹ ∈ R := R.mul_mem (R.mul_mem hr hxR) (R.inv_mem hr)
    rw [memX hrxr]
    obtain ⟨a, ha, d', hd', har⟩ := hdecH (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩)
    have hx' : QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ ∈ D := (memX hxR).mp hx
    have e1 : (QuotientGroup.mk' (Q.subgroupOf R) ⟨r * x * r⁻¹, hrxr⟩ :
        ↥R ⧸ Q.subgroupOf R) =
        QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩ *
          QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ *
          (QuotientGroup.mk' (Q.subgroupOf R) ⟨r, hr⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1, har]
    have hA : ∀ y : ↥R ⧸ Q.subgroupOf R, a * y = y * a := fun y => (hNbcen y a ha).symm
    have e2 : a * d' * QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ * (a * d')⁻¹ =
        d' * QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ * d'⁻¹ := by
      calc _ = a * (d' * QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ * d'⁻¹) * a⁻¹ := by group
        _ = d' * QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hxR⟩ * d'⁻¹ := by
          rw [hA, mul_inv_cancel_right]
    rw [e2]
    exact D.mul_mem (D.mul_mem hd' hx') (D.inv_mem hd')
  have hRRX : ⁅R, R⁆ ≤ X := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hcR : ⁅x, y⁆ ∈ R := by
      rw [commutatorElement_def]
      exact R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy)
    rw [memX hcR]
    obtain ⟨a, ha, d1, hd1, h1⟩ := hdecH (QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hx⟩)
    obtain ⟨b, hb, d2, hd2, h2⟩ := hdecH (QuotientGroup.mk' (Q.subgroupOf R) ⟨y, hy⟩)
    have e0 : (QuotientGroup.mk' (Q.subgroupOf R) ⟨⁅x, y⁆, hcR⟩ : ↥R ⧸ Q.subgroupOf R) =
        ⁅QuotientGroup.mk' (Q.subgroupOf R) ⟨x, hx⟩,
          QuotientGroup.mk' (Q.subgroupOf R) ⟨y, hy⟩⁆ := by
      rw [← map_commutatorElement]
      rfl
    rw [e0, h1, h2]
    have hA : ∀ z : ↥R ⧸ Q.subgroupOf R, a * z = z * a := fun z => (hNbcen z a ha).symm
    have hB : ∀ z : ↥R ⧸ Q.subgroupOf R, b * z = z * b := fun z => (hNbcen z b hb).symm
    rw [e1SplitCommCentral hA hB]
    rw [commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd1 hd2) (D.inv_mem hd1)) (D.inv_mem hd2)
  have hNL : N ≤ L := by
    intro n hn
    have hnR : n ∈ R := hNR hn
    exact (memLb hnR).mp (hNbLb ((memNb hnR).mpr hn))
  have hLdec : L = N ⊔ (L ⊓ X) := by
    apply le_antisymm
    · intro l hl
      obtain ⟨n, hn, x, hx, hlnx⟩ := hdec l (hLR hl)
      have hxL : x ∈ L := by
        have hx' : x = n⁻¹ * l := by rw [hlnx]; group
        rw [hx']
        exact L.mul_mem (L.inv_mem (hNL hn)) hl
      rw [hlnx]
      exact Subgroup.mul_mem_sup hn (Subgroup.mem_inf.mpr ⟨hxL, hx⟩)
    · exact sup_le hNL inf_le_left
  let θ : ↥X →* Ω :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (N.subgroupOf R)).comp (Subgroup.inclusion hXR))
  have hθapp : ∀ x : ↥X, θ x = e (QuotientGroup.mk' (N.subgroupOf R) ⟨x.1, hXR x.2⟩) :=
    fun x => rfl
  have hθsurj : Function.Surjective θ := by
    intro ω
    obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective (N.subgroupOf R) (e.symm ω)
    obtain ⟨n, hn, x, hx, hrx⟩ := hdec r.1 r.2
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hθapp]
    have hmemN : (x : G)⁻¹ * r.1 ∈ N := by
      have h1 : (⟨n, hNR hn⟩ : ↥R) ∈ N.subgroupOf R := Subgroup.mem_subgroupOf.mpr hn
      have h2 := hNn.conj_mem _ h1 ⟨(x : G)⁻¹, R.inv_mem (hXR hx)⟩
      rw [Subgroup.mem_subgroupOf] at h2
      convert h2 using 1
      rw [hrx]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_assoc]
    have hxr : QuotientGroup.mk' (N.subgroupOf R) ⟨x, hXR hx⟩ =
        QuotientGroup.mk' (N.subgroupOf R) r := by
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simpa using hmemN
    rw [hxr, hr, MulEquiv.apply_symm_apply]
  have hθker : θ.ker = Q.subgroupOf X := by
    ext x
    have hxN : (x : G) ∈ N ↔ (x : G) ∈ Q := by
      constructor
      · intro h
        have hmem : (x : G) ∈ N ⊓ X := Subgroup.mem_inf.mpr ⟨h, x.2⟩
        rw [hNX] at hmem
        exact hmem
      · intro h
        exact hQN h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hθapp, map_eq_one_iff e e.injective,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hxN
  have hQnX : (Q.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (⟨(n : G), hXR n.2⟩ : ↥R) ∈ Q.subgroupOf R := Subgroup.mem_subgroupOf.mpr hn
    have h2 := hQRn.conj_mem _ h1 ⟨(g : G), hXR g.2⟩
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hcomX : (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆).map X.subtype = ⁅X, X⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hPerfX : ⁅X, X⁆ ⊔ Q = X := by
    apply le_antisymm
    · apply sup_le _ hQX
      apply Subgroup.commutator_le.mpr
      intro a ha b hb
      rw [commutatorElement_def]
      exact X.mul_mem (X.mul_mem (X.mul_mem ha hb) (X.inv_mem ha)) (X.inv_mem hb)
    · intro x hx
      have hmap : (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆).map θ = ⊤ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hθsurj,
          hΩperf]
      have hxmem : θ ⟨x, hx⟩ ∈ (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆).map θ := by
        rw [hmap]
        exact Subgroup.mem_top _
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxmem
      have hyker : y⁻¹ * ⟨x, hx⟩ ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
      rw [hθker, Subgroup.mem_subgroupOf] at hyker
      have hyC : (y : G) ∈ ⁅X, X⁆ := by
        have h1 : (y : G) ∈ (⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆).map X.subtype :=
          Subgroup.mem_map_of_mem _ hy
        rwa [hcomX] at h1
      have hxe : x = (y : G) * ((y⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hxe]
      exact Subgroup.mul_mem_sup hyC hyker
  have hRQ : ⁅R, R⁆ ⊔ Q = X := by
    apply le_antisymm (sup_le hRRX hQX)
    calc X = ⁅X, X⁆ ⊔ Q := hPerfX.symm
      _ ≤ ⁅R, R⁆ ⊔ Q := sup_le_sup_right (Subgroup.commutator_mono hXR hXR) Q
  have hLX_card : Nat.card ↥(L ⊓ X) = Nat.card Q * q ^ 2 := by
    have hQS : Q ≤ L ⊓ X := le_inf hQL hQX
    have hSR : L ⊓ X ≤ R := inf_le_left.trans hLR
    have hbar := bar_card_mul_card_of_le (M := R) (Q := Q) (S := L ⊓ X) hQS hSR
    have hbareq : bar R Q (L ⊓ X) = Lb ⊓ D := by
      ext z
      constructor
      · intro hz
        have hz' : z ∈ ((L ⊓ X).subgroupOf R).map (QuotientGroup.mk' (Q.subgroupOf R)) := hz
        obtain ⟨s, hs, hsz⟩ := Subgroup.mem_map.mp hz'
        rw [← hsz]
        have hsLX : (s : G) ∈ L ⊓ X := Subgroup.mem_subgroupOf.mp hs
        exact Subgroup.mem_inf.mpr ⟨(memLb s.2).mpr (Subgroup.mem_inf.mp hsLX).1,
          (memX s.2).mp (Subgroup.mem_inf.mp hsLX).2⟩
      · intro hz
        obtain ⟨hzL, hzD⟩ := Subgroup.mem_inf.mp hz
        obtain ⟨r, rfl⟩ := hmksurj z
        have hrL : r.1 ∈ L := (memLb r.2).mp hzL
        have hrX : r.1 ∈ X := (memX r.2).mpr hzD
        show _ ∈ ((L ⊓ X).subgroupOf R).map (QuotientGroup.mk' (Q.subgroupOf R))
        exact Subgroup.mem_map.mpr
          ⟨r, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hrL, hrX⟩), rfl⟩
    have hLbD : Nat.card ↥(Lb ⊓ D) = q ^ 2 := by
      have hNX' : Nb ⊓ (Lb ⊓ D) = ⊥ := by
        rw [← inf_assoc, inf_eq_left.mpr hNbLb, hD1]
      have hdec' : ∀ r ∈ Lb, ∃ n ∈ Nb, ∃ x ∈ Lb ⊓ D, r = n * x := by
        intro r hr
        obtain ⟨a, ha, d, hd, had⟩ := hdecH r
        refine ⟨a, ha, d, Subgroup.mem_inf.mpr ⟨?_, hd⟩, had⟩
        have hd' : d = a⁻¹ * r := by rw [had]; group
        rw [hd']
        exact Lb.mul_mem (Lb.inv_mem (hNbLb ha)) hr
      have hLbeq := orth_card_mul_of_inf_eq_bot (hNR := hNbLb) (hXR := inf_le_left) hNX' hdec'
      rw [hNbcard, hLbcard] at hLbeq
      have h3 : q * q ^ 2 = q * Nat.card ↥(Lb ⊓ D) := by
        rw [← hLbeq]
        ring
      exact (Nat.eq_of_mul_eq_mul_left hq h3).symm
    rw [hbareq, hLbD] at hbar
    rw [← hbar, mul_comm]
  have hQuot : QuotIso X Q Ω := by
    haveI := hQnX
    exact ⟨hQnX, ⟨(QuotientGroup.quotientMulEquivOfEq hθker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)⟩⟩
  exact ⟨X, hQX, hXR, hNX, hNXR, hXnorm, hPerfX, hRQ, hLdec, hNL, hLX_card, hQuot⟩


theorem e1SplitTopPerfect {Γ : Type} [Group Γ] (W : Subgroup Γ)
    (h : ⁅W, W⁆ = W) : ⁅(⊤ : Subgroup W), (⊤ : Subgroup W)⁆ = ⊤ := by
  apply Subgroup.map_injective (f := W.subtype) W.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]

theorem e1_split_base (h34 : Stroth34Statement) (hC : NtCentralStatement)
    {M Q Z B : Subgroup G} {t : G} (hH : E1Hyp M Q Z B t)
    (hNcard : Nat.card ↥(Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z)
    {Ω : Type} [Group Ω] [Finite Ω]
    [hNn : ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (hperf : ⁅(⊤ : Subgroup Ω), (⊤ : Subgroup Ω)⁆ = ⊤)
    (hsyl : ∀ P : Sylow 2 Ω, Nat.card P = Nat.card Z ^ 2)
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* Ω) :
    QuotIso (E1Xpre M Q B t) Q Ω ∧
      Nt M (LB M Q B) t ≤ LB M Q B ∧
      Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q ∧
      Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t ∧
      (∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t) ∧
      ⁅E1Xpre M Q B t, E1Xpre M Q B t⁆ ⊔ Q = E1Xpre M Q B t ∧
      LB M Q B = Nt M (LB M Q B) t ⊔ (LB M Q B ⊓ E1Xpre M Q B t) ∧
      Nat.card ↥(LB M Q B ⊓ E1Xpre M Q B t) = Nat.card Q * Nat.card Z ^ 2 := by
  have hc := hH.ctx
  have hQt : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt hH.mem
  haveI : (Q.subgroupOf (Rt M (LB M Q B) t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => hc.hyp.Q_normal.2 (hc.Rt_le_M t hx)
  haveI : (Q.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2
  have hQN : Q ≤ Nt M (LB M Q B) t := orth_Q_le_Nt hc hH.mem
  have hNR : Nt M (LB M Q B) t ≤ Rt M (LB M Q B) t := orth_Nt_le_Rt _ _ _
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt _ hH.mem
  have hQL : Q ≤ LB M Q B := sec39_Q_le_LB
  have hN2 : IsPGroup 2 ↥((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) :=
    (orth_Nt_isPGroup M (LB M Q B) t).of_equiv (Subgroup.subgroupOfEquivOfLe hNR).symm
  have hcen : ∀ r ∈ Rt M (LB M Q B) t, ∀ n ∈ Nt M (LB M Q B) t, ⁅r, n⁆ ∈ Q :=
    hC G M Q Z B t hH
  have hLc : Nat.card ↥(LB M Q B) = Nat.card Q * Nat.card Z ^ 3 :=
    (stroth_3_5 h34 hc hH.case.width (by norm_num) hH.noA2 hH.gen).2.2.1
  obtain ⟨X, hQX, hXR, hNX, hNXR, hXnorm, hPerfX, hRQ, hLdec, hNL, hLX, hQuot⟩ :=
    e1SplitCore hQt hQN hNR hLR hQL hN2 hcen (fun x hx y hy => Subgroup.commutator_le.mp
      hc.commutator_LB_le_Q x hx y hy) (fun x hx => hc.sq_mem_Q_of_mem_LB hx) hNcard hLc hperf
      hsyl e
  have hEX : E1Xpre M Q B t = X := hRQ
  rw [hEX]
  exact ⟨hQuot, hNL, hNX, hNXR, hXnorm, hPerfX, hLdec, hLX⟩

def E1SplitSeven {G : Type} [Group G] (M Q Z B : Subgroup G) (t : G) : Prop :=
  Nt M (LB M Q B) t ≤ LB M Q B ∧
    Nt M (LB M Q B) t ⊓ E1Xpre M Q B t = Q ∧
    Nt M (LB M Q B) t ⊔ E1Xpre M Q B t = Rt M (LB M Q B) t ∧
    (∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ E1Xpre M Q B t, r * x * r⁻¹ ∈ E1Xpre M Q B t) ∧
    ⁅E1Xpre M Q B t, E1Xpre M Q B t⁆ ⊔ Q = E1Xpre M Q B t ∧
    LB M Q B = Nt M (LB M Q B) t ⊔ (LB M Q B ⊓ E1Xpre M Q B t) ∧
    Nat.card ↥(LB M Q B ⊓ E1Xpre M Q B t) = Nat.card Q * Nat.card Z ^ 2

theorem e1_plus_all (h34 : Stroth34Statement) (hC : NtCentralStatement)
    (hKF3 : Omega4BasicStatement) {M Q Z B : Subgroup G} {t : G} (hH : E1Hyp M Q Z B t)
    (hP : CaseE1Plus M Q Z B t) :
    E1SplitSeven M Q Z B t ∧ QuotSat (E1Xpre M Q B t) Q (IsOmegaPlus 2 (Nat.card Z)) := by
  obtain ⟨hQc, hNc, hY⟩ := hP
  obtain ⟨hNn, KE, hFE, hFinE, hKE, ⟨e⟩⟩ := hY
  haveI := hNn
  have hc := hH.ctx
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have h4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨hperfKF, -, hsylKF⟩ := (hKF3 KE h4).1
  have hsyl : ∀ P : Sylow 2 ↥(StatedOmega (StatedQuadPlus 2 KE)),
      Nat.card P = Nat.card Z ^ 2 :=
    fun P => (hsylKF P).trans (by rw [hKE])
  obtain ⟨hQuot, b1, b2, b3, b4, b5, b6, b7⟩ :=
    e1_split_base h34 hC hH hNc (e1SplitTopPerfect _ hperfKF) hsyl e
  obtain ⟨hQn, ⟨isoX⟩⟩ := hQuot
  exact ⟨⟨b1, b2, b3, b4, b5, b6, b7⟩, hQn, KE, hFE, hFinE, hKE, ⟨isoX⟩⟩

theorem e1_minus_all (h34 : Stroth34Statement) (hC : NtCentralStatement)
    (hKF3 : Omega4BasicStatement) {M Q Z B : Subgroup G} {t : G} (hH : E1Hyp M Q Z B t)
    (hM : CaseE1Minus M Q Z B t) :
    E1SplitSeven M Q Z B t ∧ QuotSat (E1Xpre M Q B t) Q (IsOmegaMinus 2 (Nat.card Z)) := by
  obtain ⟨hQc, hNc, hY⟩ := hM
  obtain ⟨hNn, KE, hFE, hFinE, hKE, b, c, hirr, ⟨e⟩⟩ := hY
  haveI := hNn
  have hc := hH.ctx
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have h4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨hperfKF, -, hsylKF⟩ := (hKF3 KE h4).2 b c hirr
  have hsyl : ∀ P : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 KE b c)),
      Nat.card P = Nat.card Z ^ 2 :=
    fun P => (hsylKF P).trans (by rw [hKE])
  obtain ⟨hQuot, b1, b2, b3, b4, b5, b6, b7⟩ :=
    e1_split_base h34 hC hH hNc (e1SplitTopPerfect _ hperfKF) hsyl e
  obtain ⟨hQn, ⟨isoX⟩⟩ := hQuot
  exact ⟨⟨b1, b2, b3, b4, b5, b6, b7⟩, hQn, KE, hFE, hFinE, hKE, b, c, hirr, ⟨isoX⟩⟩

theorem rtSplit_of (h34 : Stroth34Statement) (hNt : StrothNtStatement) (hN : E1NaturalStatement)
    (hC : NtCentralStatement) (hT : TMemNtStatement) (hKF3 : Omega4BasicStatement) :
    RtSplitStatement := by
  clear hNt hN hT
  intro G _ _ M Q Z B t hH
  rcases (caseE1_iff M Q Z B t).mp hH.case with hP | hM
  · obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7⟩, hq⟩ := e1_plus_all h34 hC hKF3 hH hP
    exact ⟨b1, b2, b3, b4, b5, b6, b7, fun _ => hq,
      fun hM' => (e1_minus_all h34 hC hKF3 hH hM').2⟩
  · obtain ⟨⟨b1, b2, b3, b4, b5, b6, b7⟩, hq⟩ := e1_minus_all h34 hC hKF3 hH hM
    exact ⟨b1, b2, b3, b4, b5, b6, b7, fun hP' => (e1_plus_all h34 hC hKF3 hH hP').2,
      fun _ => hq⟩

end Split

end CFSG.RankThree.GF2n.Smith81.Smith23E1
