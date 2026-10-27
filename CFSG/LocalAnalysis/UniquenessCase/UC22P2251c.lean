module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F8Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.UC6Mod
import CFSG.Milestones.ASVolI.C31.J4NP.Orbit
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

namespace P2251c

variable {G : Type} [Group G]

theorem not_dvd_card_of_isPGroup_two [Finite G] {H : Subgroup G} (hH : IsPGroup 2 H) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) : ¬ q ∣ Nat.card H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  rw [hn]
  exact fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))

theorem not_mem_of_orderOf_eq_three {O : Subgroup G} (hO : IsPGroup 2 O) {b : G}
    (hb : orderOf b = 3) : b ∉ O := by
  intro hbO
  obtain ⟨k, hk⟩ := hO ⟨b, hbO⟩
  have h : orderOf b ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  rw [hb] at h
  have h3 := Nat.prime_three.dvd_of_dvd_pow h
  norm_num at h3

theorem exists_mem_centralizer_of_coset [Finite G] {O P₁ P₂ : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hO : IsPGroup 2 O)
    (hP₁ : IsPGroup p P₁) (hP₂ : IsPGroup q P₂) (h₁₂ : P₂ ≤ centralizer (P₁ : Set G))
    (hO₁ : P₁ ≤ normalizer (O : Set G)) (hO₂ : P₂ ≤ normalizer (O : Set G)) {b : G}
    (hb₁ : ∀ u ∈ P₁, b⁻¹ * (u * b * u⁻¹) ∈ O) (hb₂ : ∀ v ∈ P₂, b⁻¹ * (v * b * v⁻¹) ∈ O) :
    ∃ c, b⁻¹ * c ∈ O ∧ c ∈ centralizer (P₁ : Set G) ⊓ centralizer (P₂ : Set G) := by
  have hconj : ∀ {P : Subgroup G}, P ≤ normalizer (O : Set G) → ∀ x ∈ P, ∀ f ∈ O,
      x * f * x⁻¹ ∈ O := fun hP x hx f hf => (mem_normalizer_iff.1 (hP hx) f).1 hf
  obtain ⟨c₁, hc₁O, hc₁⟩ := UC6.exists_fixed_in_coset_uc6 P₁ O hP₁
    (not_dvd_card_of_isPGroup_two hO Fact.out hp2) (hconj hO₁) b hb₁
  have hc₁C : c₁ ∈ centralizer (P₁ : Set G) :=
    mem_centralizer_iff.2 fun u hu => mul_inv_eq_iff_eq_mul.1 (hc₁ u hu)
  obtain ⟨c, hcF, hc⟩ := UC6.exists_fixed_in_coset_uc6 P₂ (O ⊓ centralizer (P₁ : Set G)) hP₂
    (not_dvd_card_of_isPGroup_two (hO.to_le inf_le_left) Fact.out hq2)
    (fun v hv f hf => mem_inf.2 ⟨hconj hO₂ v hv f (mem_inf.1 hf).1,
      mul_mem (mul_mem (h₁₂ hv) (mem_inf.1 hf).2) (inv_mem (h₁₂ hv))⟩)
    c₁ fun v hv => by
      refine mem_inf.2 ⟨?_,
        mul_mem (inv_mem hc₁C) (mul_mem (mul_mem (h₁₂ hv) hc₁C) (inv_mem (h₁₂ hv)))⟩
      rw [show c₁⁻¹ * (v * c₁ * v⁻¹) =
        (b⁻¹ * c₁)⁻¹ * (b⁻¹ * (v * b * v⁻¹)) * (v * (b⁻¹ * c₁) * v⁻¹) by group]
      exact mul_mem (mul_mem (inv_mem hc₁O) (hb₂ v hv)) (hconj hO₂ v hv _ hc₁O)
  obtain ⟨hcO, hcC⟩ := mem_inf.1 hcF
  refine ⟨c, ?_, mem_inf.2 ⟨?_, mem_centralizer_iff.2 fun v hv =>
    mul_inv_eq_iff_eq_mul.1 (hc v hv)⟩⟩
  · simpa [mul_assoc] using mul_mem hc₁O hcO
  · simpa using mul_mem hc₁C hcC

theorem exists_orderOf_three [Finite G] {L P₁ P₂ : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hP₁ : IsPGroup p P₁) (hP₂ : IsPGroup 3 P₂)
    (h₁₂ : P₂ ≤ centralizer (P₁ : Set G)) (hN₁ : P₁ ≤ normalizer (L : Set G))
    (hN₂ : P₂ ≤ normalizer (L : Set G)) {b : G} (hbL : b ∈ L) (hb : orderOf b = 3)
    (hb₁ : ∀ u ∈ P₁, b⁻¹ * (u * b * u⁻¹) ∈ pCoreOf 2 L)
    (hb₂ : ∀ v ∈ P₂, b⁻¹ * (v * b * v⁻¹) ∈ pCoreOf 2 L) :
    ∃ a ∈ L, orderOf a = 3 ∧ a ∈ centralizer (P₁ : Set G) ⊓ centralizer (P₂ : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hNO := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
  obtain ⟨c, hbc, hcC⟩ := exists_mem_centralizer_of_coset hp2 (by norm_num) hO hP₁ hP₂ h₁₂
    (hN₁.trans hNO) (hN₂.trans hNO) hb₁ hb₂
  have hcL : c ∈ L := by
    simpa using mul_mem hbL (CFSG.LieType.BorelTits.pCoreOf_le 2 L hbc)
  have hmem : (⟨b, hbL⟩ : ↥L)⁻¹ * ⟨c, hcL⟩ ∈ CFSG.pCore 2 ↥L := by
    have h : L.subtype ((⟨b, hbL⟩ : ↥L)⁻¹ * ⟨c, hcL⟩) ∈ pCoreOf 2 L := hbc
    exact (mem_map_iff_mem L.subtype_injective).1 h
  have hbc' : ((⟨b, hbL⟩ : ↥L) : Bar2 L) = ((⟨c, hcL⟩ : ↥L) : Bar2 L) := QuotientGroup.eq.2 hmem
  have hb1 : ((⟨b, hbL⟩ : ↥L) : Bar2 L) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact fun h => not_mem_of_orderOf_eq_three hO hb (mem_map.2 ⟨⟨b, hbL⟩, h, rfl⟩)
  have hord : orderOf ((⟨b, hbL⟩ : ↥L) : Bar2 L) = 3 := by
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨b, hbL⟩
    rw [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, hb] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hb1
    · exact h
  have h3 : 3 ∣ orderOf c := by
    have hdvd := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ⟨c, hcL⟩
    rwa [QuotientGroup.mk'_apply, Subgroup.orderOf_mk, ← hbc', hord] at hdvd
  exact ⟨c ^ (orderOf c / 3), pow_mem hcL _, orderOf_pow_orderOf_div (orderOf_pos c).ne' h3,
    pow_mem hcC _⟩

theorem exists_orderOf_three_mem [Finite G] {L : Subgroup G} (h3 : 3 ∣ Nat.card (Bar2 L)) :
    ∃ b ∈ L, orderOf b = 3 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3
    (h3.trans (Subgroup.card_quotient_dvd_card _))
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩

theorem le_centralizerMod_of_ne [Finite G] {M L K : Subgroup G} (hL : L ∈ calC M)
    (hK : K ∈ calC M) (hne : L ≠ K) :
    K ≤ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L := fun k hk =>
  ⟨PartTwo.calC_le_normalizer_of_ne hL hK hne hk,
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L
      (PartTwo.calC_le_normalizer_of_ne hL hK hne hk),
    fun l hl => (PartTwo.calC_commutator_le_of_ne hK hL hne.symm
      (commutator_mem_commutator hk hl)).2⟩

theorem inv_mul_conj_mem_of_mem_centralizerMod {L : Subgroup G} {v b : G}
    (hv : v ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L)
    (hb : b ∈ L) : b⁻¹ * (v * b * v⁻¹) ∈ pCoreOf 2 L := by
  have h := inv_mem (hv.2.2 b⁻¹ (inv_mem hb))
  rwa [show (v * b⁻¹ * v⁻¹ * b⁻¹⁻¹)⁻¹ = b⁻¹ * (v * b * v⁻¹) by group] at h

theorem mem_pCoreOf_of_mem_centralizerMod [Finite G] {L : Subgroup G}
    (hZ : center (Bar2 L) = ⊥) {a : G} (haL : a ∈ L)
    (ha : a ∈ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L) :
    a ∈ pCoreOf 2 L := by
  have hc : ((⟨a, haL⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h : L.subtype ((l * ⟨a, haL⟩)⁻¹ * (⟨a, haL⟩ * l)) ∈ pCoreOf 2 L := by
      have h' := (inv_mem ha).2.2 _ (inv_mem l.2)
      rw [show a⁻¹ * (l : G)⁻¹ * a⁻¹⁻¹ * (l : G)⁻¹⁻¹ = ((l : G) * a)⁻¹ * (a * (l : G)) by
        group] at h'
      exact h'
    exact (mem_map_iff_mem L.subtype_injective).1 h
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hc
  exact mem_map.2 ⟨⟨a, haL⟩, hc, rfl⟩

theorem exists_elemAbelian_of_list [Finite G] {M : Subgroup G} :
    ∀ Ls : List (Subgroup G), Ls.Nodup →
      (∀ L ∈ Ls, L ∈ calC M ∧ 3 ∣ Nat.card (Bar2 L) ∧ center (Bar2 L) = ⊥) →
      ∃ E : Subgroup G, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ Ls.length ∧ E ≤ ⨆ L ∈ Ls, L
  | [], _, _ => ⟨⊥, CFSG.SectionRank.isElemAbelian_bot 3, by simp, bot_le⟩
  | L :: Ls, hnd, hLs => by
    obtain ⟨hLnot, hnd'⟩ := List.nodup_cons.1 hnd
    obtain ⟨hL, hL3, hLZ⟩ := hLs L List.mem_cons_self
    obtain ⟨E, hE, hEc, hEle⟩ := exists_elemAbelian_of_list Ls hnd'
      fun L' hL' => hLs L' (List.mem_cons_of_mem _ hL')
    have hEL : E ≤ CFSG.Quasithin.centralizerMod (pCoreOf 2 L) (normalizer (L : Set G)) L :=
      hEle.trans (iSup₂_le fun L' hL' =>
        le_centralizerMod_of_ne hL (hLs L' (List.mem_cons_of_mem _ hL')).1
          fun h => hLnot (h ▸ hL'))
    obtain ⟨b, hbL, hb⟩ := exists_orderOf_three_mem hL3
    obtain ⟨a, haL, ha, -, haE⟩ := exists_orderOf_three (p := 3) (P₁ := ⊥) (P₂ := E)
      (by norm_num) IsPGroup.of_bot hE.isPGroup
      (fun _ _ => mem_centralizer_iff.2 fun h hh => by rw [mem_bot.1 hh, one_mul, mul_one])
      bot_le (fun v hv => (hEL hv).1) hbL hb (fun u hu => by rw [mem_bot.1 hu]; simp)
      fun v hv => inv_mul_conj_mem_of_mem_centralizerMod (hEL hv) hbL
    have haE' : a ∉ E := fun h => not_mem_of_orderOf_eq_three
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ha
      (mem_pCoreOf_of_mem_centralizerMod hLZ haL (hEL h))
    obtain ⟨hE', hE'c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE ha
      (fun e he => mem_centralizer_iff.1 haE e he) haE'
    refine ⟨E ⊔ zpowers a, hE', by rw [hE'c, hEc, List.length_cons, pow_succ], sup_le ?_ ?_⟩
    · exact hEle.trans (iSup₂_le fun L' hL' =>
        le_iSup₂_of_le (f := fun (K : Subgroup G) (_ : K ∈ L :: Ls) => K) L'
          (List.mem_cons_of_mem _ hL') le_rfl)
    · exact (zpowers_le.2 haL).trans
        (le_iSup₂_of_le (f := fun (K : Subgroup G) (_ : K ∈ L :: Ls) => K) L
          List.mem_cons_self le_rfl)

theorem length_le_pRank [Finite G] {M : Subgroup G} {Ls : List (Subgroup G)} (hnd : Ls.Nodup)
    (hLs : ∀ L ∈ Ls, L ∈ calC M ∧ 3 ∣ Nat.card (Bar2 L) ∧ center (Bar2 L) = ⊥) :
    Ls.length ≤ CFSG.Open.pRank 3 M := by
  obtain ⟨E, hE, hEc, hEle⟩ := exists_elemAbelian_of_list Ls hnd hLs
  exact CFSG.SectionRank.le_pRank (by norm_num)
    (hEle.trans (iSup₂_le fun L hL => (hLs L hL).1.1.le)) hE hEc

theorem mem_normalizer_of_pRank_le [Finite G] {M K L : Subgroup G} (hK : K ∈ calC M)
    (hKn : (K.subgroupOf M).Normal) (hL : L ∈ calC M) (hKL : K ≠ L)
    (hK3 : 3 ∣ Nat.card (Bar2 K)) (hKZ : center (Bar2 K) = ⊥) (hL3 : 3 ∣ Nat.card (Bar2 L))
    (hLZ : center (Bar2 L) = ⊥) (hM3 : CFSG.Open.pRank 3 M ≤ 3) {x : G} (hxM : x ∈ M)
    (hx : Odd (orderOf x)) : x ∈ normalizer (L : Set G) := by
  by_contra hxN
  have hMK : M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hK.1.le).1 hKn
  have hconj : ∀ g ∈ M, L.map (MulAut.conj g).toMonoidHom ∈ calC M ∧
      3 ∣ Nat.card (Bar2 (L.map (MulAut.conj g).toMonoidHom)) ∧
      center (Bar2 (L.map (MulAut.conj g).toMonoidHom)) = ⊥ := by
    intro g hg
    refine ⟨UC6S846.calC_map M _ (UC6S846.mem_normalizer_iff_map_conj.1 (le_normalizer hg)) hL,
      hL3.trans (dvd_of_eq (Nat.card_congr (UC6S846.bar2Equiv
        (Subgroup.equivMapOfInjective L (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective)).toEquiv)),
      eq_bot_of_card_eq _ ?_⟩
    rw [UC6S846.card_center_bar2_map, hLZ, card_bot]
  have hKc : ∀ g ∈ M, K ≠ L.map (MulAut.conj g).toMonoidHom := fun g hg h => hKL <|
    map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
      ((UC6S846.mem_normalizer_iff_map_conj.1 (hMK hg)).trans h)
  have hx2 : x ^ 2 ∉ normalizer (L : Set G) := by
    intro h
    obtain ⟨m, hm⟩ := hx
    have e : (x ^ 2) ^ (m + 1) = x := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf x + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    exact hxN (e ▸ pow_mem h (m + 1))
  have hne1 : L ≠ L.map (MulAut.conj x).toMonoidHom :=
    fun h => hxN (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
  have hne2 : L ≠ L.map (MulAut.conj (x ^ 2)).toMonoidHom :=
    fun h => hx2 (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
  have hne12 : L.map (MulAut.conj x).toMonoidHom ≠ L.map (MulAut.conj (x ^ 2)).toMonoidHom := by
    intro h
    have h' := CFSG.ASVolI.burnsideJ4NP_map_conj_eq_map_conj_iff.1 h
    rw [show x⁻¹ * x ^ 2 = x by group] at h'
    exact hxN h'
  have hnd : [K, L, L.map (MulAut.conj x).toMonoidHom,
      L.map (MulAut.conj (x ^ 2)).toMonoidHom].Nodup := by
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_,
      List.nodup_singleton _⟩⟩⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨hKL, hKc x hxM, hKc _ (pow_mem hxM 2)⟩
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
      exact ⟨hne1, hne2⟩
    · simpa only [List.mem_singleton] using hne12
  have h4 := length_le_pRank hnd fun L' hL' => by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hL'
    rcases hL' with rfl | rfl | rfl | rfl
    · exact ⟨hK, hK3, hKZ⟩
    · exact ⟨hL, hL3, hLZ⟩
    · exact hconj x hxM
    · exact hconj _ (pow_mem hxM 2)
  simp only [List.length_cons, List.length_nil] at h4
  omega

theorem le_normalizer_of_pRank_le [Finite G] {M K L H : Subgroup G} (hK : K ∈ calC M)
    (hKn : (K.subgroupOf M).Normal) (hL : L ∈ calC M) (hKL : K ≠ L)
    (hK3 : 3 ∣ Nat.card (Bar2 K)) (hKZ : center (Bar2 K) = ⊥) (hL3 : 3 ∣ Nat.card (Bar2 L))
    (hLZ : center (Bar2 L) = ⊥) (hM3 : CFSG.Open.pRank 3 M ≤ 3) (hHM : H ≤ M)
    (hH : Odd (Nat.card H)) :
    H ≤ normalizer (L : Set G) := fun h hh =>
  mem_normalizer_of_pRank_le hK hKn hL hKL hK3 hKZ hL3 hLZ hM3 (hHM hh)
    (Odd.of_dvd_nat hH (Subgroup.orderOf_dvd_natCard H hh))

theorem mem_centralizer_of_isCyclic [Finite G] {R L : Subgroup G} (hR : IsPGroup 3 R)
    (hRL : R ≤ normalizer (L : Set G)) (hcyc : IsCyclic ↥(R ⊓ L)) {a : G} (haR : a ∈ R)
    (haL : a ∈ L) (ha : orderOf a = 3) : a ∈ centralizer (R : Set G) := by
  haveI := hcyc
  rw [mem_centralizer_iff]
  intro r hr
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hraR : r * a * r⁻¹ ∈ R := mul_mem (mul_mem hr haR) (inv_mem hr)
  have hraL : r * a * r⁻¹ ∈ L := (mem_normalizer_iff.1 (hRL hr) a).1 haL
  have hord : orderOf (r * a * r⁻¹) = 3 := by
    rw [← ha]
    exact orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective a
  have hz : zpowers (⟨r * a * r⁻¹, mem_inf.2 ⟨hraR, hraL⟩⟩ : ↥(R ⊓ L)) =
      zpowers ⟨a, mem_inf.2 ⟨haR, haL⟩⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord, ha]
  have hmem : r * a * r⁻¹ ∈ zpowers a := by
    have h : (⟨r * a * r⁻¹, mem_inf.2 ⟨hraR, hraL⟩⟩ : ↥(R ⊓ L)) ∈
        zpowers ⟨a, mem_inf.2 ⟨haR, haL⟩⟩ := by
      rw [← hz]
      exact mem_zpowers _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
    exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
  rcases CFSG.Semidihedral.GL2Recognition.SharpFourM11.eq_of_mem_zpowers_of_pow_three ha3 hmem
    with h | h | h
  · rw [h, orderOf_one] at hord
    norm_num at hord
  · exact mul_inv_eq_iff_eq_mul.1 h
  · exfalso
    have hc2 : Commute (r ^ 2) a := by
      refine mul_inv_eq_iff_eq_mul.1 ?_
      calc r ^ 2 * a * (r ^ 2)⁻¹ = r * (r * a * r⁻¹) * r⁻¹ := by
            simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = r * a ^ 2 * r⁻¹ := by rw [h]
        _ = (r * a * r⁻¹) ^ 2 := conj_pow.symm
        _ = (a ^ 2) ^ 2 := by rw [h]
        _ = a := by rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, ha3, one_mul]
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    have hr3 : r ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨m, hm⟩ : Odd (orderOf r) :=
      Odd.of_dvd_nat (Odd.pow ⟨1, rfl⟩) (orderOf_dvd_of_pow_eq_one hr3)
    have hrm : (r ^ 2) ^ (m + 1) = r := by
      rw [← pow_mul, show 2 * (m + 1) = orderOf r + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    have hc : Commute r a := hrm ▸ hc2.pow_left (m + 1)
    rw [hc.eq, mul_inv_cancel_right] at h
    have h1 : a * a = a * 1 := by rw [mul_one, ← pow_two, ← h]
    rw [mul_left_cancel h1, orderOf_one] at ha
    norm_num at ha

end P2251c

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
