module

public import CFSG.RankThree.PartTwo.Sec8.Item812ProofFinal
import CFSG.RankThree.PartTwo.Sec10.Item105
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

namespace Item812Res3

variable {G : Type} [Group G] [Finite G]

@[expose] def IsMaxPSub (p : ℕ) (P K : Subgroup G) : Prop :=
  P ≤ K ∧ IsPGroup p P ∧ ∀ S : Subgroup G, IsPGroup p S → P ≤ S → S ≤ K → S = P

theorem isMaxPSub_top_of_normalizer_le {P Q : Subgroup G}
    (hP : IsMaxPSub 3 P (Subgroup.normalizer (Q : Set G)))
    (hN : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Q : Set G)) :
    IsMaxPSub 3 P ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨le_top, hP.2.1, fun S hS hPS _ => ?_⟩
  by_contra hne
  have hlt : P < S := lt_of_le_of_ne hPS (Ne.symm hne)
  obtain ⟨x, hxS, hxP, hxN⟩ := Sec10.exists_mem_normalizer_not_mem_of_lt_of_isPGroup hS hlt
  set T := P ⊔ Subgroup.zpowers x with hT
  have hTS : T ≤ S := sup_le hPS ((Subgroup.zpowers_le).mpr hxS)
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := sup_le hP.1 ((Subgroup.zpowers_le).mpr (hN hxN))
  have hTP := hP.2.2 T (hS.to_le hTS) le_sup_left hTQ
  exact hxP (hTP ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

omit [Finite G] in
@[expose] noncomputable def IsMaxPSub.toSylow {P : Subgroup G} (hP : IsMaxPSub 3 P ⊤) :
    Sylow 3 G :=
  ⟨P, hP.2.1, fun hQ hPQ => hP.2.2 _ hQ hPQ le_top⟩

omit [Finite G] in
theorem IsMaxPSub.coe_toSylow {P : Subgroup G} (hP : IsMaxPSub 3 P ⊤) :
    ((hP.toSylow : Sylow 3 G) : Subgroup G) = P :=
  rfl

theorem commutator_mem_and_mem_cosets {P V : Subgroup G} (hP : IsPGroup 3 P) (hVP : V ≤ P)
    (hcard : Nat.card P = 3 * Nat.card V) {a : G} (haP : a ∈ P) (haV : a ∉ V) (ha3 : a ^ 3 = 1) :
    (∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ V) ∧ (∀ x ∈ P, x ∈ V ∨ a⁻¹ * x ∈ V ∨ a * x ∈ V) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVpos : 0 < Nat.card V := Nat.card_pos
  have hVlt : V < P := by
    refine lt_of_le_of_ne hVP fun h => ?_
    rw [h] at hcard
    have hPpos : 0 < Nat.card P := Nat.card_pos
    omega
  obtain ⟨x, hxP, hxV, hxN⟩ := Sec10.exists_mem_normalizer_not_mem_of_lt_of_isPGroup hP hVlt
  set N := Subgroup.normalizer (V : Set G) ⊓ P with hNdef
  have hVN : V ≤ N := le_inf Subgroup.le_normalizer hVP
  have hNP : N ≤ P := inf_le_right
  have hdvd1 : Nat.card V ∣ Nat.card N := Subgroup.card_dvd_of_le hVN
  have hdvd2 : Nat.card N ∣ 3 * Nat.card V := hcard ▸ Subgroup.card_dvd_of_le hNP
  obtain ⟨k, hk⟩ := hdvd1
  have hk3 : k ∣ 3 := by
    rw [hk, mul_comm] at hdvd2
    exact Nat.dvd_of_mul_dvd_mul_right hVpos hdvd2
  have hNeq : N = P := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h1 | h3
    · exfalso
      rw [h1, mul_one] at hk
      have hNV : N = V := (Subgroup.eq_of_le_of_card_ge hVN (by rw [hk])).symm
      exact hxV (hNV ▸ (⟨hxN, hxP⟩ : x ∈ N))
    · exact Subgroup.eq_of_le_of_card_ge hNP (by rw [hcard, hk, h3, mul_comm])
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := fun y hy => (hNeq ▸ hy : y ∈ N).1
  set V' := V.subgroupOf P with hV'
  have hV'n : V'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hPN g.2) n).mp hn
    simpa using this⟩
  have hV'card : Nat.card V' = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv
  have hQcard : Nat.card (P ⧸ V') = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V'
    rw [hV'card, hcard] at h1
    have h2 : Nat.card (P ⧸ V') * Nat.card V = 3 * Nat.card V := h1.symm
    exact Nat.eq_of_mul_eq_mul_right hVpos h2
  have hcyc : IsCyclic (P ⧸ V') := isCyclic_of_prime_card hQcard
  have hcomm : ∀ u v : P ⧸ V', u * v = v * u := fun u v => by
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg v)
    exact (Commute.zpow_zpow_self g i j).eq
  have hmkV : ∀ y : P, ((y : P ⧸ V') = 1 ↔ (y : G) ∈ V) := fun y => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
  · have h1 : (((⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹ : P) : P ⧸ V')) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv, hcomm (↑(⟨x, hx⟩ : P)) (↑(⟨y, hy⟩ : P))]
      group
    simpa using (hmkV _).mp h1
  ·
    set abar : P ⧸ V' := ((⟨a, haP⟩ : P) : P ⧸ V') with habar
    have habar1 : abar ≠ 1 := fun h => haV ((hmkV _).mp h)
    have habar3 : abar ^ 3 = 1 := by
      rw [habar, ← QuotientGroup.mk_pow, show (⟨a, haP⟩ : P) ^ 3 = 1 from Subtype.ext (by
        simpa using ha3), QuotientGroup.mk_one]
    have hord : orderOf abar = 3 := orderOf_eq_prime habar3 habar1
    have htop : Subgroup.zpowers abar = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord, hQcard])
    have hxmem : ((⟨x, hx⟩ : P) : P ⧸ V') ∈ Subgroup.zpowers abar := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
    have hkmod : abar ^ k = abar ^ (k % 3) := by
      have := zpow_mod_orderOf abar k
      rw [hord] at this
      push_cast at this
      exact this.symm
    have hcases : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · left
      rw [hkmod, h0, zpow_zero] at hk
      exact (hmkV _).mp hk.symm
    · right; left
      rw [hkmod, h1, zpow_one] at hk
      have h3 : (((⟨a, haP⟩ : P)⁻¹ * ⟨x, hx⟩ : P) : P ⧸ V') = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hk, ← habar, inv_mul_cancel]
      simpa using (hmkV _).mp h3
    · right; right
      rw [hkmod, h2] at hk
      have h3 : (((⟨a, haP⟩ : P) * ⟨x, hx⟩ : P) : P ⧸ V') = 1 := by
        rw [QuotientGroup.mk_mul, ← hk, ← habar]
        rw [← zpow_one_add, show (1 : ℤ) + 2 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, habar3]
      simpa using (hmkV _).mp h3

theorem exists_mem_normalizer_conj_eq_of_weaklyClosed (P : Sylow 3 G) {A : Subgroup G}
    (hAP : A ≤ P) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ P →
      A.map (MulAut.conj g).toMonoidHom = A)
    {x g : G} (hxA : x ∈ A) (hgx : g * x * g⁻¹ ∈ A) :
    ∃ w ∈ Subgroup.normalizer (A : Set G), w * x * w⁻¹ = g * x * g⁻¹ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set y := g * x * g⁻¹ with hy
  set C := Subgroup.centralizer ({y} : Set G) with hC
  have hAC : A ≤ C := fun z hz => Subgroup.mem_centralizer_singleton_iff.mpr (hAc z hz y hgx)
  have hAgC : A.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change g * z * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * z * g⁻¹)
    have hzx : z * x = x * z := hAc z hz x hxA
    calc g * z * g⁻¹ * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hzx]
      _ = g * x * g⁻¹ * (g * z * g⁻¹) := by group
  have hAp : IsPGroup 3 A := P.isPGroup'.to_le hAP
  have hAgp : IsPGroup 3 (A.map (MulAut.conj g).toMonoidHom) := hAp.map _
  obtain ⟨S, hAS⟩ := (hAp.comap_of_injective C.subtype C.subtype_injective).exists_le_sylow
  obtain ⟨c, hc⟩ := KFacts.exists_conj_mem_sylow S
    (hAgp.comap_of_injective C.subtype C.subtype_injective)
  have hSp : IsPGroup 3 ((S : Subgroup C).map C.subtype) := S.isPGroup'.map _
  obtain ⟨h, hh⟩ := KFacts.exists_conj_mem_sylow P hSp
  have hAhP : A.map (MulAut.conj h).toMonoidHom ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    exact hh _ ⟨⟨z, hAC hz⟩, hAS (Subgroup.mem_subgroupOf.mpr hz), rfl⟩
  have hAcgP : A.map (MulAut.conj (h * (c : G) * g)).toMonoidHom ≤ P := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : (⟨g * z * g⁻¹, hAgC ⟨z, hz, rfl⟩⟩ : C) ∈
        (A.map (MulAut.conj g).toMonoidHom).comap C.subtype := ⟨z, hz, rfl⟩
    have h1 := hh _ ⟨c * ⟨g * z * g⁻¹, hAgC ⟨z, hz, rfl⟩⟩ * c⁻¹, hc _ hz', rfl⟩
    change h * (c * ⟨g * z * g⁻¹, _⟩ * c⁻¹ : C).1 * h⁻¹ ∈ (P : Subgroup G) at h1
    change (h * (c : G) * g) * z * (h * (c : G) * g)⁻¹ ∈ (P : Subgroup G)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    convert h1 using 1
    group
  have hhN : h ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hweak h hAhP)
  have hhcgN : h * (c : G) * g ∈ Subgroup.normalizer (A : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hweak _ hAcgP)
  refine ⟨(c : G) * g, ?_, ?_⟩
  · have : (c : G) * g = h⁻¹ * (h * (c : G) * g) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hhN) hhcgN
  · have hcy : (c : G) * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp c.2
    calc (c : G) * g * x * ((c : G) * g)⁻¹ = (c : G) * y * (c : G)⁻¹ := by rw [hy]; group
      _ = y := by rw [hcy, mul_inv_cancel_right]

end Item812Res3

section Config

open Item812Res3

structure Fin812Config {G : Type} [Group G] [Finite G] (A : Subgroup G) (a : G)
    (X Y P Q R V Pa : Subgroup G) : Prop where
  pa_max : IsMaxPSub 3 Pa (Subgroup.centralizer ({a} : Set G))
  le_pa : A ≤ Pa
  pa_eq : Subgroup.zpowers a ⊔ (Pa ⊓ Y) = Pa
  sec8B_eq : sec8B A X = A ⊓ Y
  q_max : IsMaxPSub 3 Q (Subgroup.centralizer (sec8B A X : Set G))
  pa_le_normalizer : Pa ≤ Subgroup.normalizer (Q : Set G)
  q_eq : R ⊔ Subgroup.zpowers a = Q
  r_comm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x
  card_r : Nat.card R = 3 ^ 6
  r_pow : ∀ x ∈ R, x ^ 9 = 1
  b_le_r : sec8B A X ≤ R
  omega_r : ∀ x ∈ R, x ^ 3 = 1 → x ∈ sec8B A X
  le_q : A ≤ Q
  omega_q : ∀ x ∈ Q, x ^ 3 = 1 → x ∈ A
  a_not_mem_r : a ∉ R
  r_weak : ∀ g : G, R.map (MulAut.conj g).toMonoidHom ≤ Q →
    R.map (MulAut.conj g).toMonoidHom = R
  normalizer_q : ∀ g ∈ Subgroup.normalizer (Q : Set G), ∃ r ∈ R,
    ∃ k ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G), g = r * k
  p_eq : R ⊔ Pa = P
  p_max : IsMaxPSub 3 P (Subgroup.normalizer (Q : Set G))
  j_eq : ∀ E : Subgroup G, E ≤ P → CFSG.Assembly.IsElemAbelian 3 E → Nat.card A ≤ Nat.card E →
    E = A
  b_weak : ∀ g : G, (sec8B A X).map (MulAut.conj g).toMonoidHom ≤ A →
    (sec8B A X).map (MulAut.conj g).toMonoidHom = sec8B A X
  v_eq : R ⊔ (P ⊓ Y) = V
  card_p : Nat.card P = 3 * Nat.card V

theorem Fin812Config.isMaxPSub_top {G : Type} [Group G] [Finite G] {A : Subgroup G} {a : G}
    {X Y P Q R V Pa : Subgroup G} (hc : Fin812Config A a X Y P Q R V Pa)
    (hAab : CFSG.Assembly.IsElemAbelian 3 A) : IsMaxPSub 3 P ⊤ := by
  have haPa : a ∈ Pa := hc.pa_eq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hPaP : Pa ≤ P := hc.p_eq ▸ le_sup_right
  have hRP : R ≤ P := hc.p_eq ▸ le_sup_left
  have hQP : Q ≤ P := hc.q_eq ▸ sup_le hRP ((Subgroup.zpowers_le).mpr (hPaP haPa))
  have hAP : A ≤ P := hc.le_pa.trans hPaP
  set B := sec8B A X with hB
  have hQeq : P ⊓ Subgroup.centralizer (B : Set G) = Q := by
    have hp : IsPGroup 3 (P ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :=
      hc.p_max.2.1.to_le inf_le_left
    exact hc.q_max.2.2 _ hp (le_inf hQP hc.q_max.1) inf_le_right
  refine isMaxPSub_top_of_normalizer_le hc.p_max fun g hg => ?_
  have hgA : A.map (MulAut.conj g).toMonoidHom = A := by
    refine hc.j_eq _ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg z).mp (hAP hz)
    · exact ⟨⟨⟨fun u v => Subtype.ext (by
        obtain ⟨z, hz, hzu⟩ := u.2
        obtain ⟨z', hz', hzv⟩ := v.2
        simp only [Subgroup.coe_mul]
        rw [← hzu, ← hzv, ← map_mul, ← map_mul,
          show z * z' = z' * z from congrArg Subtype.val
            (hAab.1.is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩)])⟩⟩, fun u hu => by
        obtain ⟨z, hz, rfl⟩ := hu
        rw [← map_pow, hAab.2 z hz, map_one]⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hgB : B.map (MulAut.conj g).toMonoidHom = B := by
    refine hc.b_weak g ?_
    have h1 := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) (inf_le_left : sec8B A X ≤ A)
    rw [hgA] at h1
    exact h1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← hQeq]
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨hzP, hzB⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzP, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hzB ⊢
    intro u hu
    have hu' : u ∈ B.map (MulAut.conj g).toMonoidHom := by rwa [hgB]
    obtain ⟨u₀, hu₀, rfl⟩ := hu'
    change g * u₀ * g⁻¹ * (g * z * g⁻¹) = g * z * g⁻¹ * (g * u₀ * g⁻¹)
    have h1 := hzB u₀ hu₀
    calc g * u₀ * g⁻¹ * (g * z * g⁻¹) = g * (u₀ * z) * g⁻¹ := by group
      _ = g * (z * u₀) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * (g * u₀ * g⁻¹) := by group
  · intro z hz
    rw [Subgroup.mem_inf] at hz
    refine ⟨g⁻¹ * z * g, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by
      change g * (g⁻¹ * z * g) * g⁻¹ = z
      group⟩
    · have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hg) z).mp hz.1
      simpa using this
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : g * u * g⁻¹ ∈ B := by
        rw [← hgB]
        exact ⟨u, hu, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hz.2 _ hu'
      have h2 : u * (g⁻¹ * z * g) = g⁻¹ * ((g * u * g⁻¹) * z) * g := by group
      have h3 : g⁻¹ * z * g * u = g⁻¹ * (z * (g * u * g⁻¹)) * g := by group
      rw [h2, h3, h1]

end Config

section Final


open Item812Res3

@[expose] def Fin812Local : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∃ P Q R V Pa : Subgroup G, Fin812Config A a X Y P Q R V Pa

@[expose] def Fin812FusionW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ P Q R V Pa : Subgroup G, Fin812Config A a X Y P Q R V Pa →
      ∀ w ∈ Subgroup.normalizer (A : Set G), ∃ r ∈ R, ∃ k : ℤ, w * a * w⁻¹ = r * a ^ k * r⁻¹

@[expose] def Fin812FusionV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ P Q R V Pa : Subgroup G, Fin812Config A a X Y P Q R V Pa →
      ∀ z ∈ V, z ^ 3 = 1 → ∃ g : G, g * z * g⁻¹ ∈ sec8B A X

@[expose] def Fin812Extremal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X Y : Subgroup G) (n : ℕ), Sec8Final G A c L a b X Y n →
    ∀ P Q R V Pa : Subgroup G, Fin812Config A a X Y P Q R V Pa →
      ∀ z ∈ P, z ^ 3 = 1 → z ∉ V → ∃ r ∈ R, r * z * r⁻¹ ∈ Subgroup.zpowers a ∨
        ∃ x ∈ P ⊓ Y, x ∉ sec8B A X ∧ x ^ 3 = 1 ∧
          Subgroup.zpowers (r * z * r⁻¹) = Subgroup.zpowers (a * x) ∧
          Nat.card (P ⊓ Subgroup.centralizer {a * x} : Subgroup G) <
            Nat.card (P ⊓ Subgroup.centralizer {a} : Subgroup G)

theorem fin812Sylow_of (hL : Fin812Local) (hW : Fin812FusionW) (hV : Fin812FusionV)
    (hE : Fin812Extremal) : Fin812Sylow := by
  intro G _ _ A c L a b X Y n h
  classical
  obtain ⟨P, Q, R, V, Pa, hc⟩ := hL G A c L a b X Y n h
  have hAab := h.mem_partTwoF.1
  have ha3 : a ^ 3 = 1 := hAab.2 a h.a_mem
  have haPa : a ∈ Pa := hc.pa_eq ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  have hPaP : Pa ≤ P := hc.p_eq ▸ le_sup_right
  have haP : a ∈ P := hPaP haPa
  have hRP : R ≤ P := hc.p_eq ▸ le_sup_left
  have hAP : A ≤ P := hc.le_pa.trans hPaP
  have hRV : R ≤ V := hc.v_eq ▸ le_sup_left
  have hVP : V ≤ P := hc.v_eq ▸ sup_le hRP inf_le_left
  have hmax := hc.isMaxPSub_top hAab
  set S := hmax.toSylow with hS
  have hSP : (S : Subgroup G) = P := hmax.coe_toSylow
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hweak : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      A.map (MulAut.conj g).toMonoidHom = A := by
    intro g hg
    refine hc.j_eq _ (hSP ▸ hg) ?_ ?_
    · exact ⟨⟨⟨fun u v => Subtype.ext (by
        obtain ⟨z, hz, hzu⟩ := u.2
        obtain ⟨z', hz', hzv⟩ := v.2
        simp only [Subgroup.coe_mul]
        rw [← hzu, ← hzv, ← map_mul, ← map_mul,
          show z * z' = z' * z from congrArg Subtype.val
            (hAab.1.is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩)])⟩⟩, fun u hu => by
        obtain ⟨z, hz, rfl⟩ := hu
        rw [← map_pow, hAab.2 z hz, map_one]⟩
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hnoV : ∀ g : G, g⁻¹ * a * g ∉ V := by
    intro g hgV
    have h3 : (g⁻¹ * a * g) ^ 3 = 1 := by
      have := conj_pow (a := g⁻¹) (b := a) (i := 3)
      rw [inv_inv] at this
      rw [this, ha3]
      group
    obtain ⟨k, hk⟩ := hV G A c L a b X Y n h P Q R V Pa hc _ hgV h3
    set k' := k * g⁻¹ with hk'
    have hk'a : k' * a * k'⁻¹ ∈ A := by
      have : k' * a * k'⁻¹ = k * (g⁻¹ * a * g) * k⁻¹ := by rw [hk']; group
      rw [this]
      exact (Subgroup.mem_inf.mp hk).1
    obtain ⟨w, hwN, hw⟩ := Item812Res3.exists_mem_normalizer_conj_eq_of_weaklyClosed S
      (hSP ▸ hAP) hAc hweak h.a_mem hk'a
    obtain ⟨r, hrR, m, hrm⟩ := hW G A c L a b X Y n h P Q R V Pa hc w hwN
    have hmem : r * a ^ m * r⁻¹ ∈ R := by
      rw [← hrm, hw]
      have : k' * a * k'⁻¹ = k * (g⁻¹ * a * g) * k⁻¹ := by rw [hk']; group
      rw [this]
      exact hc.b_le_r hk
    have ham : a ^ m ∈ R := by
      have : a ^ m = r⁻¹ * (r * a ^ m * r⁻¹) * r := by group
      rw [this]
      exact R.mul_mem (R.mul_mem (R.inv_mem hrR) hmem) hrR
    have ham1 : a ^ m ≠ 1 := by
      intro h1
      rw [h1, mul_one, mul_inv_cancel] at hrm
      have : a = k'⁻¹ * (k' * a * k'⁻¹) * k' := by group
      rw [← hw, hrm] at this
      exact h.a_ne_one (by rw [this]; group)
    have hao : orderOf a = 3 := orderOf_eq_prime ha3 h.a_ne_one
    have hmmod : a ^ m = a ^ (m % 3) := by
      have := zpow_mod_orderOf a m
      rw [hao] at this
      push_cast at this
      exact this.symm
    have hcases : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
    apply hc.a_not_mem_r
    rcases hcases with h0 | h1 | h2
    · rw [hmmod, h0, zpow_zero] at ham1
      exact absurd rfl ham1
    · rwa [hmmod, h1, zpow_one] at ham
    · rw [hmmod, h2] at ham
      have : a = (a ^ (2 : ℤ)) ^ (2 : ℤ) * (a ^ 3)⁻¹ := by group
      rw [this, ha3, inv_one, mul_one]
      exact R.zpow_mem ham 2
  have haV : a ∉ V := by simpa using hnoV 1
  obtain ⟨hcomm, hcos⟩ := Item812Res3.commutator_mem_and_mem_cosets hmax.2.1 hVP hc.card_p haP
    haV ha3
  refine ⟨S, R, V, hSP ▸ haP, hRV, hSP ▸ hVP, hSP ▸ hcomm, hSP ▸ hcos, hnoV, ?_⟩
  intro z hzP hz3 hzV
  obtain ⟨r, hrR, hr | ⟨x, hxPY, -, -, hzx, hlt⟩⟩ :=
    hE G A c L a b X Y n h P Q R V Pa hc z (hSP ▸ hzP) hz3 hzV
  · exact ⟨r, hrR, Or.inl hr⟩
  · refine ⟨r, hrR, Or.inr ⟨a * x, hSP ▸ P.mul_mem haP hxPY.1, hzx, ?_⟩⟩
    rw [hSP]
    exact hlt

end Final

end CFSG.RankThree.PartTwo.Sec8
